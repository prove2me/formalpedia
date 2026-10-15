-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4989
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:22:44.906833+00:00
-- url     : https://prove2.me/submissions/002f5744-6372-4341-b4f9-7d18f4b8f1b4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 897122302 ≤ n < 897302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 897123552 1250 897122302 897122309
    0x3160f0306060515071b0306020712020d03060602030d200a0201021207080402100e060d050106020705010207080105010e040b22030201020a1209020d0b0c0d1107030f080103150510051903020a 84
    0x1000e40030201103920300c40c0e034185d9049942003a000e200f903141d403001340c8010880ca9003015000740d00005820b814421004901c10421469a0895200c0003e403401241128154024600180c01c1001455810101a0410743d05642c0d0351024501034a600c4040049607844160788101507500818003140300e40b0f90741c42c002d50103900f50420003c503103040ea0001c2d4803407000d2030f1843e00340a00c0303502a805a03201c03034096444900e401d40003009107503100d1201079556001e91041e10300500c00e40c44082503050041c05000c1c1240c0c00d0700b10007a80c54030b95070f5914007800d1000b0705510050081d0b400322903440d44048152986d0b9030090700016980c916110b8010110f9040101317207111241800640342c0180c481c0000000c00c550024041440c546900343c1d0345100e4800c0400203d40c4030b0034522140c101104d41d40c01001e0b018401d807034101024103e64000e95258800b48030240401210b0554654001e9050b04125031001003503010040680d00d40000501c0f800691281c3c59581d4100360003030045080c2240c2400c00b5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 897124802 1250 897123552 897123559
    0x50705101404060f030b1c14070338150405060d0510091b1e450609050f0a062d03140d12050c090d0203160f03060605 52
    0x30075024030903042240320340d11039401000300724110349030514804d0703005ca481c00f04011b05035806409800c1d85015990079480f4207507071006443d548050601c00c0001c40c1c1045a078460041d41040000044524ad4894405454180d01039010040d01d10100c0800032280304401000911803000302ca802030004131b135402010180100c0c0c00b080040c01040000903903144203141280c0c04500c0319041c1c94000e260040540d818802e01c1007060020500c403446050a50015130203641040d01c16680710010300241c1207001c896224030f0035814114402e051080b04000700c001d025207591101046031594007040b01d00e5076114148c415590010b00034034030340940f1540e81001d82840b0074845a8207002e10800455104280c6601c00980381d804401c800c510003808030300850b04800d4800320281030740e0903552120140b40000d40010a0700c0181003000490f8812107002c0ea802c1041c05041c015814240300d840c04a20005a0740746c032405006901d01c1000e40d900383c004d07000c0d50b801000058a10316040059070000d8211500c17 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 897126052 1250 897124802 897124817
    0x415082506020a08030a09030e190303030e010515010c051204091b0e09340507030908010c0c020409032003041a040b0f160b0405031e0c060a050604021605070510 71
    0x2060b00c00d0140d80d000306e00c00f1000104000c5924050780c54020b41194503400011207208803248004058241040381d01036201401380c2420640e240c2e0807100c0c200c601c0e941104285120110a5200e034440c03130007441c072031022910b115001700404022500302d5801400c1a58071119401c43c0c183d0080c8213003018034105d0902450401c051800100d940f4001402e0469011529408100c1241001381911100507680c00103c600c201007140240a540100008d4002c911045c000103441c11051042e07480c104000e581e4103c10240580c2000068181000c054042007c880706008a4032503a0800e40191404d407802942ea40c0d00c1d0001000c0d040741100c03500c074111003080c401084190346160484181d0510070b40a00d0b1740d0610381c5840b4510588441e80580060460740030082040780000003402d40400082e441c901e098031180c5d04038050700c2038030918401ca400138004601da624440c3c1209801100050015040c01200312004d41541c0d51490261019440742d80b040045040031303c0b013419107180a29241c2c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 897127302 1250 897126052 897126073
    0xc060501150f02010c020c1912060c08010510050a080618090a052103010b0c01200309060f130f0507150306090501090b0d030807021509030a03050115020c041508250602 74
    0x29200c1400203541e5000b5813045c1c1c0704009a408c040c48883c0540340303540c1600c200443c0c5040c0030b001010340c40c55070f0021943c0d500000c40e0501d400c0001d0340c98225295035081ca050101c4404449003640a402c0395001002c00f02003061138040141001e2240401c0c000071710358001d40742002e80c0313003442c480c2208980e441b00c6200c4086070050b42040328152800214860303500c20143d0401c90040c40d900036000158190b80c0f800d062075902003002140261030030701c00c40e0f40944928520f000082c50a542000598081223031090000300108803202496000c0c40c1a40d9030075030354440400780502d5170a0303414002555103505103c0549a881424050043c2080810503050454041074806809800290500c03588800141219100700720000010800240010643c20481c0407242d8a80114000201207403d100001c12007500010076416142d88035401402e54086800500c0006c001081ca00c401405090402044480e0104410b0f070300c032565920640803400c200940d008204000742c01c42003c54000c2040c04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 897128552 1250 897127302 897127307
    0xc1401080a060503073b0103050d02060f04110d060f020a1704050c01050c010e01090c05041a0a05061b060f1e060108010308250302030307030c080f07050306010c060501150f02010c 79
    0x40081d43ca01b1100b01c180c03455403060000e510049449410000d003000340d910458002a5890306040720300c18800c58001c3c45244100380e071522801c440056100f803940c0006004140198006602d80d580074245454180307040d2031380d030299075140741c00030200c5400082e248c4541e54004082c5001190f008001101810f00791303120394480799060425410080d01043c0010040401c2d131001c2d5860415030b0007003000074920325084c480032a40340b080c548143d1a2030640d01246442c51882244590010802c55116040204010698118801101940007522286000030788200040c6000e130340100f00c1c600051400e030003050f40041001d00800810b0500d0420b011841c0d80119955042d20352011a05446080b1618180701c4070b00d1580007184d074010703081000c0081c540c01000070350003150b0703d44d000d0245915841054520741300992344c4120300c410340701c001042544640c003c1c40d003140e41450849140c801548440d400d840081c1c10200454210309042e060f016040010080d1804250000b44070217010070002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 897129802 1250 897128552 897128563
    0x50612010e06011a0d1e0e0f0709151d04020a050117040b07110327010e0a03080903160915120506040201030509031611130b0a030f0f0c1401080a060503 67
    0xb074079503056000f183c0c9440f0160000c2540c8006460417410802d03998041d00101c80e00c131000240e0520b803840e116071541c075660081070045c40c600d2004014076019103005d040600400300750060b40c1750441e0440000c90501840c4400c04110200150169500d0030f05004000800c91603610203814000c2000309003680022a09585505c1303904103d0005855496440940b00c4a12401c1040024040058101c0c080c801154203c50444074403041c0540702c1200100548103900525140c9a11100000c020400200c5800040c41240405010303a544c2d960488400440e1100c2e0360800980c0d07940310b160340b4404000f0843d20a005003582607852000305200e4071100d88500c0302500190406889500003000391300e080049030380000120000100d00035a07800d00204440000e50014841c0300210802d80300072015000307552a070071008250042c0d65203181e440360007440d1106c0007110305014105c2900c002c558051002d10050080704081d08180090600040441100070502c8455030315021040c00242c900181 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 897131052 1250 897129802 897129809
    0xb030f0a02090d060c081801050c040302090c0d0207050d0e040603171e270d0b01151107030305041805090d030b0102011407022b1403151201050612010e0601 69
    0x100603610340e8528003141030400c1148000e4182810311000b11743c0c8691200702d05201d0500d091070360104198505585003a290180d0b0000103e1304140020710161910a20310303a0803280e008000781c0340003a43ea070003070140d8200c084103844c1508030084142c031041e007082c549035621100f02c1d802c110940c11652040035a08400d54003102c000408111a60340b4071145010020024018011036112034068040c2f0410035140041c903080b48842c07031004880d90030400d62407101ca60b0710030401c08030750b0700341340e80f071880d09160801a9003007102e52001c1803024502071090801650180d510340741e60b581064425010341e9505003001e90180d152100b048104480840c2c2c64080c04035518000c00d422410b0030040f4090032002d25040310319a41602403168190b00050b80303045217200002502810755002501005955608038002d0215155900c058020710b403034801940d00a4003452079030031603104000400c2d4000c20351103240401e40e640e40240003a42c98090848600700d81448028071038510700c20340c00d60f21400d040c407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 897132302 1250 897131052 897131071
    0xc030a090213050c040f0501031b0e0d0b070315081c03020c010207080d0b01080c0c0d030c17040302060109050c07020d0b06013b092e17010e070b030f 66
    0x61550441d540c03403088054100c542d0b842400103040031054004980d010744a0001060156440001c155009014400403e07560b4102d0460a02c000e01c1c05079001d152040059500941c1800b03050001440680e2080c0182c01c1c42e070b00010000180380040141050702e40042180781d02900015034441100c8598001c448076900c0c025031114003c0111a000e401000b20080c15480b001c0b402e40120226a4810301c881c2c5001d90707540c0c00d1504c440c43c01404c0d0380704003074006a0070340100f6080301c004c5004c0d0b04405101072544c5081e10745401062032091500c1b809403000c5006030000001008110014041c15401491003102585001300711750001e03260300010000108114038907000202640c0c001c1002201394140480b51959007008590f21a41c0d400607000e011104e286030518880c13403070a2064403e441038803407029411341103203134400c08840d5524591140070160000a40440c1c4e59070304020f0100141d40c0a00040340c0708a0444000e410300c0c2258100010484040c81040b440304400b020301c940140300d40c5d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 897133552 1250 897132302 897132311
    0x150a09111306090608010f0522060c050f0a030c09050108060109091505040905070905010909080d0e0c0a082112060127060504140909031b010e0d0207080f060c030a 72
    0x100c0c100001e000700da0b100c203d510b407034600009030030b03841900b0142c19900c20100030001556401e842c0381c80c014504a208200311920030180307001501c0740d8480d03075134124035080c4075080400940c01c244181e8030002c0c0440c00a901c070250b2001160b00000a4000b50009007044452850b1020000700820791a101d203210722a100e60004003031084140c502005454050801e024900300d6041095803482c0503c6180c0041c1d14182c000110681e048c882c0410f200d41c400440707450181c0541440c40500078046800055001d060148801540c444102100410510020b80b0400181003542007005049803001c06107840c04000c0c001d81c15081078052603001509080c203a4100c40c04090301ca1581500008011505200003400320702c9642010280c02250800e4046109401e0002d041c490600000d88115513582e1041c02010441080c0c49801e16030040020000201624258581403401108200e14009600083c805024881c014015030004a08100040c005405e00002c95501480002c20a00c5015901d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 897134802 1250 897133552 897133579
    0xc24050906070f020d050f0607020304031208040203030919090b092710090831030201120e0a0809090f100b0d0e032b06350609150a0911 60
    0x9107040704900f150050460701c4040e40a1a01035982d001080d98194a0b11513880040d010318800004c4800362544000702407044240d014040c0c950013409403003203038107000a11001c4155151029121010740130800b200f00b10503d0040440200c440c01204d03540104002d90400c980301c44048001400c0c208240905c1311072001c13a112060411481d115165505414420b00c00284503e040280c002c0d80d0500d542a10042c0001c5014140e1030b0075210a0000c60541e2070080000d5030042c40d4400408004120203e505000c0e01c0d412418101d104008650000002c10542c480303007030500500b5844000e00f04401e050f4208800260b81c40300e00d80c840c0307010407440020314080c44480342c1c10901c6091a2a42100d48030711081c546c41b2444840d840341e0b041108140d54081d10903075000c2c0107032000c4401c215400d030410b600c00030036060010880c04074401c04200d5850004071541c030401c20144500704c01009050111500030285200d03400140c80780d000f003401c000f005000300c1c00c4100040892a0111072424004c1e80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 897136052 1250 897134802 897134813
    0x17010605161101050f160c1223070f03030c0b07080606070b04030201150303020a0b07051c021602030a03050a030e060105010e0409050c1005070c0f060c0f1406040c2405090607 77
    0x35000303646582602c0462891506c65940002c020312074421921008001e495100003038503219103e0001d4521007105010203058061101d2145990700135009890070035440d01307a07010501e12544e00403000540c80031100c1d824400400b80880e00107002c0e251280c858104040003030100d01a0320f0020b00030313152140100d4105030003588500c01220440e03001a0f0010381c3c07824069140c410b480005c0d5120780c04000013a001c907100d10100c0300c0f8231f00c1401d61010300103070b00744104d4001d4011101d20181066080089000340e6130410040b8a01d901c80d80d90300d90b03039819070107000f000e858501c00300204a501000040c480da81c0c0010055210030820342d0001450341150402518000d0a41e000070f03080141141d66162055011004144590003480340c0601e1580d500e62106190032280309690010350181e17071080c0004c10070101850014011903c1c490f500d80000340c01c5007030030020341c0c04446216120008200c0da020082c0c1d1440303440030f2250080c60314418114003070040e100f039408151082d180003640300c04015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 897137302 1250 897136052 897136057
    0xc1a0f0c010f060b1209061014120f250303020628050403120c180b030c04030803070504031104020c06040b0a06081b0109050d03050702101e1701060516110105 70
    0x1d6001405020f8680c1d81c0c008079006a03c071600f00301a951400e00000c40700c8400041582c010742040f0860400e152a2511184020b14001c47c10785d400340d010340980ca01214100200e495160000001d00f000181310511a20385030520028403942d00d101c8030003000842d4020812940c46a5400700700c4641d641080030298190001c060710550340c502d4003080c08241030744030094500005140f08108100b0090b5042500c56607100000c00a414034980380500001d50b080020756000041d880c049800c15440c1d40e41c1c1070103030300121a54000581c000c6410810702091051034500c1003001e89085103405c0c075070300030310351111001000585007086220105003400000c0d0700140003400084165415083c1900c1d800c0b01450126401500140c40306901144614042000c151025455191640b51070080c0e8244444a8010501d1701c0174014000c03102c0f40c101107007540ca03142c0004a50f44030030324055107004880c00140107030402400c00100340b01e01030300c0e4607420b013401c00b200d0f402441c0c0242e005001001290030b803 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 897138552 1250 897137302 897137321
    0xb0d09020d12020c0a030b04060c140705250e0a0b130e0a1a060303070605040204020d0c0c03141306110a0c0308030907060c030e010309030314130c1a0f0c01 69
    0x1808814815040c041142c0b03280c0e0103240a81d00751030028120300d040200e0540180800750100b50b20401060004200d0350169025915608211048030401e9800b4445904004425074113a0040e03a44500c4003003905a002004429085680c403146080c04040100d04d08002c00114001d075440c5480d03401541e03a0a02595540301c42c00c0b003885030b0b01c100d8401c1500c40c1c40d0081c1c00c503035103600080d458500440c90740d0071620451000e4015428548162a42c5010f04000b45c400d0740c002e642003004e456070301d641d4001c00c60305c41c41d00c3e141c2980d020120b2400030408600f20b14050f0350190280910180050f02d60813400440c0d449162000300c000142d0b411500b0a041c62500401c1204140000010800701801070351144400c076094880e030950354001030703c13000c90801c4014006008103c00e1250340d0b00a0b40000111400b80c50300040c41c003180110495013810a4408090342d0600018200c02c00c620760076207502800180070011031b0144005819080d5010728a0303424205240803803040703613985096000c001c2c41d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 897139802 1250 897138552 897138559
    0x1093206070f02010b0319150b04050a0903020c0306061e1201022b06050112020c0a0506090105390307110a03051c18140c06180301060807030b010b0d0902 68
    0x303400e0004001d0048000701003148095402c100350300551b454045000381429030130342d00032200e03680c240c1da07200450070400c1c60103101c0f281d45807001c4090761500e00c00d030743c801d914003a400030f5440f6480c01c000e071604041c9141c10b8407075072000007040780c26243c0c10700310562030464091021003c9d8200300041e00c5a0005480d04100d98404907054604d5510b00c4c440b00440c5810300280440d0035110309808040e507241d401140d01207489400082d600b44c0e902c0e40240300d1102c4020668490000f00c0d80c509040040a48940100e0381d1904184841c1c0d0030001071419101d440c017800401c0240c1c1c0c1d60301562403085070060a01c040c0c6004000036501c01e008211400c540c010000640300c508541c2e18000c2c1c00c540191071980b01102550791980404a2a44517403540403a42d100440409101039842944441510340c041c46e05005200c1078032526260f03032014121210454000c0c4010302285c00c281800c480343e5901034400d03544600f000304042284002e0305410b40d08050600d87c0d075404000594000742450f400029003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 897141052 1250 897139802 897139813
    0xa051b0d0e03071b050603040507050d061d061008070815070c120f0f0e1f03020918011e15030e07030804031202060604050c12090a06060b030f010503010932 69
    0x40000b040a0250401c803042c130140131168840b03040c8803d40c082101c00824507170265005001304e140060814100038440c060200746a0b80300d00e800782c00c9011000c0a2111a88444140b10f26156051809000390201074010b102d158902140c5c103a860b10f024116540d05a15039004c00c00b40da108819600306143c225214035047c500308400240944907441a10300050500d0307a000e00c81e28401c000e0f0042120006041c550300c40340684802c0d10001040342e0110900d07500f000020080c2d252004900c1c0d04e031881c120804400c0d890000d842c40c2c035100c8421440d21a445082c1e081c011400d9550410700d140001e886d0000d1414481581c25107071280b5a0409407084c0c0c03010a000003006105913807004a42c81950070344034240c950005000580300103a499024107034060040480c0400703007807141036000c0d03443c004403032102000703843d41c90440e0707507a400100041c1400401c1102e01c00c00005842d00424098008000e007034082c1d01c50381e401c07817194a1302c0103044c0b10a50401ea40c51000000021850b0a40000c0e01d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 897142302 1250 897141052 897141067
    0x30708040302010e070303090323063d1e08011107210e04020a1b06380d020d0614181906020f0d1103040b0a051b0d0e03 53
    0x20000282103034214019800d20f140114903d002296041c1101e0303054451010382801e580d00c010230000500d654000320f0f001111041c03030b0700d5410418070303000b113131810001d8142d5040900614401e89901051705900c14006042c840b80c24544101d2008030313080650107200c00c036103088041d12002e40c2607100780017035070a0000d00305110759a5401005840d202354a900d103080c01c1c0001c0c81c07850300100c07260080401d0301e4012451142c1010340042112400c10300d080b00c94101c82541c00c210384d81c00d00c001618141d52b00d10701d40c071020400c00100c60707403106009561440c580501e18103044078601c1b266050b0050b0000c0c0c8035007003103450382e0380241465640304809025007201400a10340040f002c480fa403e40240010021101c2500898086513290100841c0e205042c001e0302e8020295120160409071401d003000300144084481c46040c100d5a5090b012903507d00b4181408400c03c03501410f003440091030b010901180850341d03c4821006140f82c601c003515100c24581c4c01008100748956010305000024554 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 897143552 1250 897142302 897142307
    0x1203030115081509010b0901030605030601080321010e01060f0903020904030309020f01051804270c03170307020312060105040b04031506090b180c1e090102011d030406081009020307 80
    0xa80d00541956002030655680000002c903104180c030310343d004204e20005110701e800b060b00510712440113040101d410f942c0c5002103841e00400340d1201040d608089042c5910303000c0c0f094982038036034040c03403074089d40c0d41054002010304206115101c1448440148000315a00411596008680003005c0c80401e142c6400c000e0301406c1c003400100d20030440419a035076203601501c00c1d104d80031500081c3c00601c000d00323020f00004207000a00c610030007038006d48032442c81c045104140c1c8007922910901300203a180d0300e42990320608003501d02902c1841802008045603000041e00d407407441802801883da2107110068070389105070b410030a00c0120008000c400c2c13120103181e40003081c94010341000040c0e6102c051004403080103150590001c890300c02c250301c511030704c0d15040e04400101c4006180401074581c4e51020b180c480b10016040c0c0c1c000c5a17060f02c640c0c080c0f0a0983d1102d00031541c0c0c2c1c0b8100c007014595242c0c0714502424060282c120003142d0240c50580c820400307000071800c115500d080c4802c01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 897144802 1250 897143552 897143579
    0x4060e071b0c080d0f0315030818030604031101050618070f1707030e1908030c0d0f140604050f0424090f05010204080d0507080a0503090c0306010e060f060c15040212030301 76
    0x100b04c082004c2d04070174207429219110780000102481500d950003401d541e150304440d8009038103801045607100401e400c990b000e000c50740c05544a521510a00b403076100045007541d000803c03451103001ca1014020501c04e0504d40750341e10210b01d06d081912a40740c02c4c410303100d10101611420030280350b4000c0065646d0540e00025070342c90007070104e40d181010500806000d0341c2509008000329020300200e43c1462107040a8481c00c15856000700e0507252381000c01c0201c50b00071402ca0402c038141d03c01d10a46091610480c6d800005036040d400191501d034a90031659840700802408801005034400c8200c482907018a4000d94008040140c0b50580d041c010f010390030500404080d406111964886280110704494500b540700c05200c2c1000b005640c155815000144200c800c0d0180c10040ca610381c0d02445414043d10407400c4548281c2410014060810741c8100e0f2035024440802c521190300c040090076203200070f03912811545594440c80400c0c0d5000f490300e840740b11480003000201e10503030030584 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 897146052 1250 897144802 897144823
    0x30427060f080709110a0302091203120f010608061827030a111c1805040906090b13080d05180f03091e060901080619030305040305010b04060e071b0c08 67
    0x40390203290300c44c41520111003a003074514140040c1000b003c0700483c041d80203030802a0000308040c80031200d00000d1070450380706100c05040000801c04002d0280e14100d2034034098441407404580310301d031440104684290f1494a40305c4440c803040003691084c1c410390b60705074050b00300c00b0050801c403540c0d039002c1c0d0320f8019070380385004644100034001c0c0b44e1400181c0a04c82c1c44440c9040d101d00000b85506882514410700c41c500400381c86000440e581d1100c0c00f0391200d6520030714000480442170b0400700040300000d070071070119065a0107030390702003010101540c130740c440a03240c00580c603118460710f0441c0700032034007a54015004585180b2040800070002d00700304c544c180c81e80070944640100c1a460b0703000554009a00000901444a865104120031030744000302520542011515665080348c81696a02c11000a0f10015090040007000c4c02000d2030994146c07024064181040154141e0756001800c0c00c0c1000003000c8400c0d0019403100c400b02c0030541140d06485195201c124054a800001ca07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 897147302 1250 897146052 897146069
    0x2040b0904061505030a02070507050607080d050c0306010c080d1b0f0e01090501120b0102010b1e04180507061101110301121202070806011a070b011401090e0702030427060f 76
    0x1c0c8006109400c3e818003600c0c070700c06552110710f076a03200500080250000300c400d651900c5450008190f540f115002443d2990040341610b840f00320524010050710b000030009000090280b080c050166009140310803003d9002d450031307071540036034000760009054040070708101c00c04000c40c0300e1040d40c0002c0106030204e202d541d8004040e4001c5c1c015144140c0c00c0c0706007400940001c644014980880d070280c500b800d414400881c1000303081000911081110140c82000703003d58440103564903151041801071a0010003200201c00940c4825849000d180700304014021071000703164104034290712500100c8944459941c49503143c812482c0c0710b0801c000c040f181c0c03015212002c0202400021068119001040141166820101561808c1d556102103456000701800b0074070004590400007406002155604e442d00c0d10b0840004040040da80d11119000024106115107079601004a40c291145030b03810312007004600c00030003c1c01400752840760b4424a05900490543c4000703003440112007011 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 897148552 1250 897147302 897147311
    0x9120111040914100b09061605070b0307091205031b031e0304151407200709050a0501120c33020c0405060414060904034506051b07080102040b0904 65
    0x130200d102c140707030890299400182060000e51054030701000207007040c0d15884021850011299903180c41c210071500820002030010003000350181c2d000c46088014445e1010080207401c454440c95120700c616000303008148031400c01d00070307001030070030031103a503071041034400001c000d0b00700d640a04942042e28122040c45a41d4021f842009090042a1607800e00201480302601d604a0a8a1000d17107000b0300100207171003990410b0007403001d020303080040c005540701041910b0031400e04421694160440f105001700050020301190030b6005020075512400c0c4d80d58007415611043d034103c00c4046170b80d02c4035405401200f01d403140c2d001c1261000350400341c4042c0099240c0d10708100c1910030b0186000c001c501c00f24005140c0e4540800800d820174003a0904546000041810b00d0340300380c0c1002c00300030082101400c02c15010694440307409250745604280d0307a482c1041c000524620542020520103140d14445015442e028405c1d01e0050181030300866540c0c0e5202003014498204d0342c0058031442c0380 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 897149802 1250 897148552 897148561
    0x5010b010801150815120a06020d061512020c011e0b01080609130f230a0507091b0309020a08010213060905060f0a0f12140105040f06080309120111040914 68
    0x181180fa4564006840c2c3c10800c2e40c03031048048001c9a03115001d684240c6914520501d024144031000c00c640c01800c01507600d55000001c0003d80f0075581c814214000d02c0310420400c16803200260601c0c141c864409641c1c0d02d012701c0ca02d1701401c01101540c4210403c404c42c4190041580d0011507641001c1c0c0320503820341e444030200481c020049a48400e8030158042c0c103400140205541d580b450310501aa41e20060005502e0310444105002c425660303104410400620908200d040c0040240800c217008400c0460440f9a801e482c0a4510041c5500c5284100131903541021340d07009006290006c40d2503103110f10b128407515516110b16008140c94060109039418a40b08a421070400c0c2025203260810204045078440b10b0141604200501d8901c03c03400c02c01240602e8002c03030b41c894500a80c0d54104001c110444090000c148540d600e40072041100701c0000c002d07a0f0b180c0d681111030451140002030604d01400f0640d2000803111400200403a1220b015400a403011241e00101c00c001d80c0c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 897151052 1250 897149802 897149819
    0xa051809010506040501030c050f04032607111c022206170705060f0d050f04111009030b0705041a071b030f02040b040e2a042007031b05010b010801 65
    0xc203020b800c1e00300c00104420f0003654041e40020114044602d03089103007843c110070202d01a0880c0c1c00444802d80141e0352015125422071440c1c81e00a905a2001c4ca8030300e45a507141c200300500e0440a01a09180c0b40c10000e080741400d031601204d17009008000b2980851000030f40d086d800094010403d45480004184843c000003190b01500c804401483d115041004122640d042040703107070f04002040140300113880050142038084d0390080c0501000b41843e01e014450b404141d143d8600a40203107542c50342d51340d886514242103e40051a0344603644035120115a24400d43e00b007940000e11004000140d404110f0080580c5401400b004501d2022032080b0b03040c01c1d1040c800680200f542b28607050240c034040d07003d09500d48000b040000c041c0d407400030044c10902d070301d40e140000001c20140307040c0354003000001c03200c0406d0031a4104211788640740125201e1250340d40040580c1d4000c03580b2820107008110390424050403a0580c64055580d00d04a03018003410201540020f8001000260000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 897152302 1250 897151052 897151069
    0x306140f1e040b0603120c0703060f022a030d0c17010602010504120e0d0c0602012324030309030a0c06390507091817041a0a090503030a0518 62
    0x148010101015515152100f071000f010107001540d040c09155800c1e840c42d8030b003000a02100d001200545007051450418100b22614a0440c1500b280108139001000c05030b2400401740c0a030b052000014004d00385400b80c83e600841c0c01c801c0c50076103805a225007003900010b41c01640701261010b04e00580e00c440d0100c0c00e032007081d600100315012004042102c58011500c0801a0700003801c481c1440490f40c40f450b0804080703501450245c2d55036100c102c910a0001000c510344282004100142d05241d0080d00d25400c45800c25800c01d40b0146110305555004d000721841007000034201c0d1414407003410600b032030390000d02c50000030481c5070030b03a801d44a801d1001c1817110300d034074a440c3c001c1c0c82c2c403030740072070040b42c0c011740c0c01c03119805900408100f011051003080304a55559141164000140c0b9280c3d40f03085094000c1c1c1900d80041c4403c009a65001210000c084601413545850307035203200056800114941201364580004581c01205607481406400781ca10020440000c120300b901c2880a1035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 897153552 1250 897152302 897152341
    0x8030c0903010f271a15030c1801060309020402070506010f1e05180603030d05090f1e07141c03050d0b0f011e050405120a03090b12040605100306140f 66
    0x1000504801c002420392031308100860300683c03003107406100c0308810b00c1000c00d0841303062181e0020100b10b0417590404101040e1080c1083c0e848895600b500d078030752501c8140520031801015203d00006085403101d805503010075910400b00e585c2540c50304001ca41010709800f40081d0b14245058140c0c203100070f02d848804962300075000d1007210030850300d0902116030003030445805120820071046840954420700740328900d0a406002e64011030714030a410014030300c1d04500d11035440c1c4d440007411840403036404111412110b501301d5050360900421659885590007082c60946030407107000f8542c000008103452012200c040010380d0040e0304100c0000300001850f4000703061210f20030308036440f24071039041c0300e60b19003070150809546500091010001000e180e4142e0020b4120104041d0404040805407032140d02d83c41c00e01001034111710fa200c0006001406143d00e5501048400303416178000780c0034580005003400040c0e4000d070b0800b140c0c0001c2d1940d00340150b09100150801c00b602d920040709 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 897154802 1250 897153552 897153581
    0x30f0611040e0a09031b11010e0402070302120a090803041203090906061b020604091503061d0a030f05120a02031602030309250b0c0a030909020f09120a08030c0903010f 74
    0x1203031180000000181320600c1c0c2141441070719030700c49240e03844244103583c400d4070484e01141e00115904c00141151f4008080c540114018040140001c0c4c011808040b4820301070b0659031a0201c13404200d52800b49540245201d0100040c00315641c00d0308100c01c3d140a02944844203010741d5204020101c80040c41003000042c0c050000140520540c1e4203034800c24001409075080c15202e000700d10407a00080401304101090f481d04108020a5000b80030807200072814000c0302c0181003550f20380381c000c942c800508102d860900c203d40f0354025025a1000e20080c000c10b480740c03074801000c400a52050741c1c80d0070418105215000c11038800070031203110740b5132123025141c1c02003650200c655001d000511180f8188061101240c1c1000c0c88000e413014040d9031001303081d039949030b0070094180d00050300700d00da1041c01048060124446041240d4011a05513040360a40f0200e10199003003400540c0002c0060382c0002c28405e00782d400b1000b0340660035048008102149400140c034045454000b0306140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 897156052 1250 897154802 897154829
    0x601051c0b061f02071a07020a05090a02040f0609180b010f1b080316090e04050705090a0b03061503010c0302041202040c020f03070c0609060f080c090a030804030f061104 75
    0x40c400224032900282c0181a1400310801944242003d41c0c030500300d0b030010380c880207040000602c0c0600ca0b26940000b00c03001c61412110303030081164001c850086500030004100401c0112a02e035040b60010301c85480840d049503210380c001070216071548101d00546000302c21101940940d8803c45600170b0050310b80c20b601040081013601c021105a0150f07001110801000010038090380c0154401c0032944141a0b513034081c15800b070312030788554003c030400d00504030420000690014210058500c11500c6159558580c0c05a501412040760120b816010308010305c40c000ca5200c62841150a00b103009226a4086ea01c2c124202e010b10300c107183e40105089030300000340c02c15511000c81841e051040e2821004002c110038550361142d10103c66450f0075150400000c2d45c428400009021146001d41c401220001c0c01816840041c224001e001c0001542440329601d1740d03072031030003190700149903601c86940c1d00708414000b10306407003a260700c1e0815411646000e00502118182d44101c1809203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 897157302 1250 897156052 897156109
    0x120213060f0e030616090e0906270d020f01050c09090610020115030c05040605010c08070605220501050108060606040f060e0312030a0531021509040c11060105 70
    0x1240744540300c10080a000c01d540154109071018448035204a003440d602c143c0c032840408000341880d50b150321540d02100203809000300e030800031a0041d004008100c10741c2540c02d413405101002c20700d0409010f9180f1640b20179644050700804e000e41c0c0500254001c10543d622294030155a01c20000f0407540300f01d076400001c07110720700004141c0a000e81c0d440001914409a07181641b60103c1e030b0400d99410b003c4590070041442c041c060100600428030703019001c214250b030f81480794011041c000b0000c5442d8070006142c01c6003a8201064600c00e103006074140300c1d19061a50003804207010740105401141300083d01410944200c804403040d600c8144030452030302e8412070f01803030548041a4503015042c0340910b40c640c03200c0610301035002d0080018150a000d0008008040407042d08036605040140c1e006900101c0010b241c00c9a4043d0fa210042c0148212824440d1040c10400307030380a440c101e841d01010380c3c0040c03c151465154821254141d0301d030410004620200c82c400c4420020184101 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 897158552 1250 897157302 897157307
    0x90a1d07201203100f060503040c062a1b090e0705100504060f0201110f0901111f15030f08030105100207150e0f040f05070225052b050c0112021306 65
    0x3990b1140d13503030200004003500d5110718802104070b5800100010008420b0000f48115080f0400041c000e50428a40c0e29001d4580d4400115003142051102040702e41180148903000100d510b009860030001d8a04540f220900380040140d1103050040c1e01c9843d0011074181800d024000090866840e454201407410500300d5021080d18040320455407244820551002d20002800180560440700c0344c450344558001081c0680604c0700d09441d501484198071208000c104200c144d070340410011034018203462039041103204503400141060b040c8a41c0340180705010018505885080364401c02d00c2003248402caa41b16460301400080c0b41c0404480c5003000d01507001084c00c41d0000d41000600703030301c00c0001021140300c1076551400135114801c01c1002c65060051302049509072000403000615007008080c0d4003221700806000f0042080e0005d12400304001800b413200501c020300e60305205914125441d400941d41ea0342c003292210f40e50000255070350080d924009055000720048a260001c00c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 897159802 1250 897158552 897158557
    0x3060203060d06060f0e0a021e09010504031506080610150323040309061e05070204020903280b0105010e090a050415060b0c06010b070302060408090a1d072012 70
    0x56036030001510240000246040c00f0307010080c100b459018517030614209180c0ca032100d0051921401d680304020a030344104010628403828130524110b1500d40411900503901c83c03080307800281920700e151032740d901050003507044441520411400d44803641c0704c40020480a0415000e0040f41502480c2901d0215129520109122000f403a00780700f018a40540da01038203005a50940005503602414072426412000241007003110801c1c06030b408080c088018618024248020721440d000a401d40382540c0410003a00c4105006119201914903111906d180c2110400b0480308800d4000000a041d0b00891422105042c050081641941c0d064590307401031100070411110402c008080a007091302c58401d020152500990443d5200b9141c0ca00030710f840070503030100305400410040f210021303034041034068101d80d0040e0103946600216000584d600b0258000b40b4015860308100795144030300c044013034080d451580ba0000c818090b0b002d00420310388203150070901d691013103120780e4400c01c17034000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 897161052 1250 897159802 897159811
    0x51e01030b0426030702010b040c140912030c0d050d0c08060105030a05070c05031b121615022515060b0a0e06130603150b040806060d020d060c1808011503060203 71
    0x38072403000303850414140f00c5038005480140060395101b50040050a0a108035900341c003040c20941c8601000a0204100e403140300c0c0524002c4402030402c4403242010029200050b0018090300c455446841e0010b21035008401c803031803141d042c5421005d64a001780f60250043c0c07010707912a4510382d41c181c4040c0190001400540800c0315900050000c50710503c094106a030020b16450401c0f0303140c0e11254589480400083c035540d82c20403412140d131103c4507052400b503a004403844060580040c4000c000c0c01184680d100b460701510959100c0705e0304514100780c85100c0c00d2541c400b40301062913101150f21328001c40151480802168500c80e01585041000301c06c01400349207080d9401464400c03a459560080c00401e0315032041a00c002c440910b000042c01203400081d06003071800900580d47e840150019001e8516810a84295150348094540703280d01312a00b440f82e031400700e60081c004801010407400c111413011012458210602804250500d0132010540d01425500c84d02d00070f5001a0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 897162302 1250 897161052 897161093
    0x203060102100c02030c1e0111161101090f0321080403091e09140621150c0d1b020c01140d0c031d0c1503060127090f051e01030b04 58
    0x845c1c0006e100007042100703006141080010000320602c10510300352020380101c01c4900070140030408450b070200303166020540d0000719580c1241c03d0324005945030f525031b2b04040c0c5240381d440008401e00031010740e400041c040400c172005080c40c1d0700a0480382d4410031b45000f40094480e1784100204400000c03d244034920a40104120301d40d00d40b541021111042c50303561345031102e001005080e00d070a46130240141000b465030540d01c000550950b841d4416901d2a281b104403440c0401c80600d000010350380c0341543c803201041280c1c0d00c4110742d0400002501c0c1c1c2070052040043c0710070131b54400d0300e079a118030181c042c1c200d007031144001d052005803203408020300426944203800c1c20303d01c05c00c00c000c860307846045000d0011011000288510202c4202c1001c810031002c00510009992082110740d070042c2c14003500100414042c08031290040c0c940c000c0071902d0514020100340c0c002544054000c00d1300d1490031102901e00b0000324003000013440098900c498a1001030041494507065644000c1c805 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 897163552 1250 897162302 897162307
    0xb0a120302011a090f0a0f1e09051c1b06110c03030402031c09031e050d0807030b091005060304231612080306090c070f0c2c06040e03070c14130203060102100c0203 72
    0x554460700e0070943c8c04c54141c520351504101c4082c003400340494009064803030040240d503646c60a01034115185046c4040300c1d80c0d03010b03000d403090040b10380c022002030460b9880c0690780c1a012052558940040e1401c0c0c0c401e025060b4031009039a4844400802c1c00e1594071a03595403441c50312040c2048120780b0402d0a8024800b1880c000140280b01c8031243d1886500c0e405194240114000c04944e0001e8030680607040c41d9040c0303c1c003103d410801c1c40840c0c40c00c4404c199280d0300c07868900d010500030400c0766214244800030100d601008a007601e04015281d48140c1007954690210412041c482c1d000f405a690800c00314055050005081e07038880c010511507854071003030b0382d901c0c45602d06c48041514410105441801880c0c102c0507003100c1c3c090f14a0040f0345c10138030b10f5600c1c1d20030540540554420380e0740b0414080c1102003071041e80e86458002c0c1c010003007641d0b10f00c1a0708030783c6000c03e0070038441c2d43d0090120100346020300c240ca004410690060002e1650015110010540c200c800e00652205 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 897164802 1250 897163552 897163571
    0xc1f020c0306072c1309060207140c04180b040308090f0d02010623011d0d0b0901050f1e0408130b220f0b0702040b0a120302011a090f0a0f 61
    0x70010701c3d0040306a82c2c1d4010f64061440c00d800d280f5040305101c0d0b0340448814500f81ca59507a2442c5662209400c500c0c005407807481460000003c0c401c014004280040e0300b4000c51001c200821145c0d9a80000c0e03d051190b04206803032003086841096004000c16400c5d0082008203210703444813640f080102c412501d10141c0500e00e03520b0034643e0121240180e440754001d00910310401d91031101046145100341003981c016001802c03c880c103464059084403c0b80c0f042da45076030343d0800030750810b030001c51a580508007061002d02804040b203c1e00581130420010850500d2420348060b40c5039916090403405403a10345d26941503521134800002e20014482d00410f4a4044c0401406030501800006280d00814015895104c003a0b03440350f50600742926042080c042d120381182d00c400d50444001030100c3c2d1450016440c2041900201c481100a0042d0002c054055110025807a4912501c00f001840e4070200502081c08403503402ca600001008a00030802941240c43d80c00c030034080100d0819039 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 897166052 1250 897164802 897164809
    0xa0f061b1a0f100b030c0d0c050f07030905030d05090d140109061a09010501031a0904080c0a032105041a04111c03090f08060c1605030d020d0e0c1f020c 67
    0x50548070390200c10070680034820041c0444041000030122484003905520380f1070400d1085006241403400d0030380c1c44108c0701602c1403042c001c41d94100072401c1040c1d2201600d050003000d03807105004042c061312036a64030425113800391054400d011300c01003071034003501d51580d1003c1484202c480300c1c95556403546c0e0200c00203a2140610030300000140700f41110300300380e5810040c2000e0103a02c454185803424803c103020002c1e15500030409070b401c1d2081156522145065540b40c843c08100c1440341c051020b0404c01c1580c851a07140040c480941d009074505042c0a0740344c1200c0043d18020145400324400300307008418071044550190040d80308803110300001d0086018410504144420031403815440d0042641120502c00038200420818640c241003a400c03a681d00d4020309802c0300c0f42c8010549800701c3d03041d50181141c0603845801d03070340c03251040d014440194008030111040c0070300313103d005e407042000010740d241301c3c1e04020843c0a000600d1140031804210140d910011409201d5901c030703680c0c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 897167302 1250 897166052 897166103
    0x1608192105090d0605090114310818090c1207081317091002030414090603030c07090c030c110601090e011808070618080f0307050d09110a0f061b 64
    0x11302035107000c00d442c50403030025400c54000344800400b2040c50018003851301d814141c81d02e001d20f0703d241402d498081002c0310b282080303004900203140200c001010000501c20b80c000000510040c0d41c42c2101c0d8944c0c0007000d481e0702400c0c81882000e641c07030000070510f070310a5218640141080b98825020005500c6443e24140142c11805c841a000a00341c081e13421b1a90310070140c110144041d50034181016400d0541c3c50044a41c2480703122208041103c60f80d0500480e040700034900d0031210301a55405841000e8555144100c0101e4600003c2d50f24460087d10681a102d90b802c002d42036681c2421805001400543e06403145590b0b00c0018610803081480300e25041409204690344855103450007500395040844001015101c6105900000e4003402c19500c0ea80c000b0b40c4010b4481ea28500203c89d103010f5401d03a4400c0a050482070001c1c0070700d201034542910000d540314004070340c07100e804130072424592180c1000921200791901e01c1012603110051450321483e45e808002e408000130b40182c0c07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 897168552 1250 897167302 897167329
    0xa080f0c0c0f0a020a051801090b03010b09070908060a05011809030e18040b0604110703082a1309050105060715020412030815010c0b0711010608160819210509 70
    0x991200340250254508126004010b003400c6420009a00c103803c01fa40ca80007044c841c000c41740d0f40b500203d64030f5550a4002e0060100080c1c200071041c50090002850325a840c800c41c00c5078011140410340004a0740a80d0741030700d03221b4406400050f424564240141342d02032044d401c1007441c813400c02da240e0310b001c01d60391030a8a4901c030b0085410301b400d00a80640e409000d1901c914a060411f035550034800c0c0035a00815018107000407503075500700c19055919040303920307407900320061203084810f0100c000103030160406102c510101c4030740351000c0328200c0388280205a48014180050720000f810080c40000e6031585031805402c040c0d98140b030fa13140342c0c0d003014101d0108019108010822040841e0800441424030303203500049000d0f01d417101880d8000c1c00d1003040040d042d03421556801309402c000c008000a2080325503011488070030203c0c40d81d007800b07061000c0c01742c0400306441c0d405800500310b1a40d0080480c80303000c204040000300003a101c008090a100d002d00c0401d8865590050700f2046 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 897169802 1250 897168552 897168583
    0x11030406030b01081e0c030a060816261b120709020318161202040b10030b03071a040b130b040603060302040e0a0b010e0a020d0e150106050a080f0c0c 66
    0x5000b0141c0c009030004a0051030020070800d4440070090780c8000c40803050b0418001c02c1069544d444100b054801741641e90040720213803103090040001f0850910b01882214a40c401e0b015a040d4034001450401d88808200d5291b80d01c44401c400b04004018558010340c98000c0855080050305c60403141820255840f09208650202c1006502802c5100c048021100440544004400b20a051616003014040c4100544440c4596021521180e02241010f40700400084040e0340c1204010050104e200c1518000e006041c2c001805040c03405040b0985a030488442c2e052130301b06001401c80e5041038940903410160705000091407007840c0010005881a640c010824901318014441030300d10700080903290b507120401d250045852401d083d4192850408011030b152141e40142d00a4021040c0c9000c8861510f80c03d012440c0e0001070890b41800c002654400aa0b03070b0700d4081e42c05024904075031004c540210000f8048001139026258410b12004c031850410300202c15040c41c00e00b4005080d02c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 897171052 1250 897169802 897169811
    0x5090a06090c0f06110d050f120907030615060903020405040201020a0f080904050c03070c11010210020d061701060b03040602030702150702010f1a01021b1305090a12030b100806011103040603 84
    0x1036080003000051300240c14002205189021580d030f442c0e0002c1c40003810084080b40c0c0081000428040702c801c0140d04240d0500e40c10042c54a83d1540760620013245c1c1d05140c400310b003149101040b580c0b400c1394582d44900101c58a540c081c07002030700d4000c00882c1140640c1040000084004c02c007050b050380118007040e02d03a04001e00340011154054124800340c03105008204507160b110071040c0960707620281c02000522401c005030311301040c0001e81c0042d1400802c14100c2110746a101804503a410300c9516084080b4201c514204d0b21640540001003108000040200d44c45400654000c0850303c1240c104440140038075012034401d031031840042c1d4507288501e401e009280280c034078041042d9110b00f102c030713040e400113580c0301c1e00d0904101601d01d203103011010a0341d40440b1a546102c4107078007070000349070036629a621486010800c0b2031030f018001c40504414400d224481c6005005811007240b443c10203000d450b0748000805c03041c1085580c0034002d2440e401400a4001400c0c951400325 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 897172302 1250 897171052 897171059
    0x7080723061303111c1212061503110f040303050c07050301020a03020c060901050709062001020c150f1e0406021902030a0f020303061003050c1b0a0309171005090a06090c 75
    0x70207007203848064400c13220000243c4c0d01c0c445c8018420074850f0311580c030200e4003a00050540c1c03941c81c1084504083c51601c2000640901c40b5a04400f4030a202e94080203156881e02c42c0031524058001141c102007010300c418000a4000c400500500300c41d1011a0102a0390f0710009081e40d20400c00180029000310b4108041702e01001543e42108030407009002500c2c080300001e261500c50711945003000f000300c40031000da0990351800325940719040029980d41c01c518120a60391004410705401c6422a107001a50388040c00070708600410001401000030101030340e140c0205c420192081d1440d83d420010344012208910b11094a03480381e030095910b440c0c40390000303403d40d401c8621032000d5420400c20026607580d691503d01d040c844d14103000030f4a0b1141040068280141500c0741c40c1c404106016210504e000206416041c4c1300c3d5880c48549a110205104402000c10b02d810342540040d20322050486641c0000d5405800da000300d4030000710780c2c5c8461065440d030100c240d40811003200c060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 897173552 1250 897172302 897172313
    0x9050a0204091b2304121a07020d2c1c020306060d0213050a060b07030201021201060c08340b060a0605120a05281d07080723061303 58
    0x14006207505020682c1c41da00c441c40291401d400b007988030700c138540d2005034400c60080c100240e4000d450745004030485850b1528180803000c03035000d00c1c2c3c14006a0000091015840050203402c0721001c4c0d925942c010804c100c0c4900300c44d000c8006c030036100250035681042c5485807101c8890a0561310000401044039005040c20801d020300b2032401041c64600ba0809a00c500d07401800c6401c01c00e1001565503180d56888005004c20380203001e8100001a00e81c00745503054024151610800c0d4080040c1d9986240c00e031090402c0b120000c200a20500001d4000189030001d6800244249018017400c0c2c60702c250709820b000c0c0414100c0e101e80a010504c0311a08100710544083d180d14201240740594240e040002c54070010044203480e91200d00190032551031550301e003000c4100e0210034001c0d00301c0007d21005442e064a610003000b07480d541080f4001c100090050440300a1800340c02502e042c40f100500d50089848507040b51b0051603d042c80300c1d1191401058240c1800400d140c006080d40342a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 897174802 1250 897173552 897173561
    0x204151809110f03090a0c06120e061003082b060e090a3309030306050108090d08070f03150f030201091703161b0e071403100b070c09050a020409 64
    0x4040d0507180800c00240714890340b08a600506180b01080d803030b80d56803074425140c0368108100610f01100343c0d200194443e00140c01450018000109221160070681d18a660300c07000c588801128204035800c0005c24264001018105040f000064030020075a0707102c1e05011600c1800442c2d242d59440412401815850580c5c00c1500740025103002e0b86e140d200d9a075014900e013032410192480c22071049940e28082c40c050340407402d40c0701c00e10078480305080140080030796101c3d40313000c188054001506003802203001c2e0907050321903c030070001c1c0d207038100d0465003a1709490860090581c5e8644800340300c03900d2441c00008090310b030040c024990079407000500720400355000c1681c0d09c60715074500000242c040250341135440b25a1501b400d0300b034607042014591080c1503080300340850060010900e1804030006c14800d200f607440c2c2c4840c0204c02d142c10203551004440d21342c07448250940500c62020b0319001052038038000e00075802c5460321a4400c1e4201c6809841c500082030303001404100d0746800703005 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 897176052 1250 897174802 897174809
    0xa3e040f060b0426280b012619080901020a05070306091e0804050f04020d020c060702061f120f1202160918021009151215050d0308070302041518 64
    0x180b00303100f032006101c03684d035164101d101c1c030170b000b90540c81c45803680d6090202e07030340c1d03950040c52111803560340b40012204100130465404101020f03207181000504009a0340e00c09440000e241503003401581c4401c0d40a410440d0010704500440d03042c9404200100f040e04061801494009440c48551410542c130041201404104401c000d2080b004541e6000599044070010f4230469811000040014000e20580b0710b40c2144034030200e10f2003006003002590345e100340e5698003129065111000200701c3d001950301c007107100103000c1005006c68413841100e080800d2107840e4103800d14030b0b650780b256024810320b04510010703031240f420620703480f10b8002e0b07500045c034041c40100243c1e44a02c502010f2204400e03000390080d800e0300e100c0e0000c0c510400c580d80041003004e01d000b421010191000f040f035540c20303007c808058104078911284460f044c51030401c4a4005200e05181d80007664103441c400c10040520083c0741d400c2c440052985a11005150141816511010282604144000b81802c3c640 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 897177302 1250 897176052 897176099
    0x7051e090a0c080a0e03090a1d01080309060f0d0906180b010509010f15110102130e0f0108031c02070f0b09210a0e0a05030304080a3e040f060b04 64
    0x408030081240c00040060f00000c6510005c40c00842c08090316107188210481c0030b4100203c114001100864100c804070303081c001d920000b405980c0d0b031f01c0380b0b942ca010303244119520020400240c00b1881d0703d03000400358043c4c0620301041d01c038904e03140c0c1d0301200e00302c02c0511880c04260b409842002920342510380545412984462b0a50610790021101032076805a440030741c0742011680d410310700590b06030465487c820025552001c00d40f80280f9642c04e40d1280306820400e100c04903000c507802c00701860594010707130000d6040110b1b10700c0c02522079000310304c1049040d90070000500414000c94a80944501681614650b4207120003098600307608480202040340c00d0f103c1e580301e016540c40464101100e00e151050b0a00c02090010701c889090381d20440c0d052000041c006442c610115401501c2c0303000f0490851a00c1c600540c000d072110340c04042d001201264070040081803d030f0015250790405c040c10004011000841420403905a0303084a0b1201101007000c00c09141c05800c1c0c0130b00c0700d00a4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 897178552 1250 897177302 897177311
    0xe0a06060e070504150e010e0307091e0e03070809131503141f0b0109080f1c02031305100507021801180605010c0b130512071101090803180307051e090a 67
    0x22001c0441c5c40d41d80751210204905504100c0d441d03031043d583c0200350b80d0014103490405079a0342c140001400c02c3c4800c13146e20701d83c0b00c014a00404907072007020403082c1010017540c030b45644d80e560808070b40d0064080950224101c4400c081070b007000d20481181d0050a00c0e8440300d1800c5040201149440540e80440d680c4507445e01909144541000181c980b000000441e00384428001a58055400e801407c100c0c42000c3c10f4404403040014059441000c141c844520360b40300003412a228410394101d0000904064002c10036400c150000034071503071031880c001e13060804a03030000328040480e00f2010100d408403c01030100070070455405101d404885c004119a0b49440000b0384040d0303054102403c807146040c0010221130581d6446450f859000d026502005074140d4400c070160001941598031243d001c1c0b0442c019402410403a0540d4222001542000c030007002c0607464030101d141d820b8140c014540000344945501000c100440e0f00c900401c4c0302c3e40380440600c4128103005001803600c0e4280f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 897179802 1250 897178552 897178559
    0x80f0106050a2d1509090e0a0201081f17060906062b0503070f0c0303110303010b090d030e060d060608060402070b06010c030504030506041a1f1403010e0a06060e070504 74
    0x1d014240c5040c003a0f0340c5154100300c11240d895070380700460b80e210b1a0101006a013003d90550312040c1001500d06c00d4908004844000350b2903079071080c912900a001c82c61040100e9000e070051300c1c041510b04079402486c2690394aa150240c5181d0360144070740c44580c04481400382c2841c0500480fa441182501c01c0442da111440c250301440e840858907010041900d140d940c2030102c00c0c42102c07080307030b0000e28002c00c0e6005450503210750241d40c0300580000700315641000040c000802140c2c12102c5692169041c05d9441c000c0017020003440300e04800303102c50745032943e00c1d985034500548602c0d5000600054042c1c50200040c0c01d13002c0003015144154410070948002594071610541c0000080c42d141c1e080d03071290b01d8207450501c01c03500058034a1107a18200010002d40050221140c1c0680c0411051515004401403130429107202100c11403001ea0424049560000101006620020004035001c2008402c641c01c0c11a101015908070b500c1c0c06080c0f16841c074075642d56401150030318005241902c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 897181052 1250 897179802 897179819
    0x903050d140406050f04091107210c02090603150f0601090506040e0103060507110f011a030f0d05030703061a040920071b0302091807080a030203120718080f0106050a 73
    0x12801140305100005c070b003003511014084180e5002c0d2044141c100042e442c020003202c03450300901011a620102d0303100059078910b0030a411100300c140358032495601c26041d4204251000d000341680d401d03104080821200080b80c40002c0d002d004001c044011505094000400b4911950001e5000300c40801c4100540b80d5899206070450f0f802c10700016854403010002c8a80109030b01c9940382500c260043c07011498419840180c0c215009107041928642e00342c10b050b00d608424031420040d401a0056540c8140190010b41d403002d1070340740000d103998980140f640600c240000344129207d010400344400404c9101d0070f80a604001d41d440000d2401c902c5d03080991141c004000e0550b8019069a540302c1401c68580c0051070b402000000e07140342606040d00701c000e002600601501c0f6030100051070000218041c3d92080d0140c1c0a14601002d028181e42c102c5401f40c050704c10081c1860708103617031400121420014110090103064140841c41c2424251003880e0030140c400c0e10030350f10404c610117 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 897182302 1250 897181052 897181057
    0xa0c090503030705030f03060d02100f030b120604031202090a06020a020f090c030703180602031519060c0209040c0f030507060807170601030c021f0f061a2502030d0903050d14 77
    0x6c502c03642c2c0603a00c1d46d031032010481c03170104035100a4000050412903103006400400c1014103116a542c20040c10812000300700203440707101240681ca4000c44003103004240700d40424130b0450460400585480a0200450642d4119501c50320046c2c101c081c1c80c00452600802e42e44602c803081b1100d00460611104802003840043c110700141036803045401d1008086118070f4080316048141192207141040c1101c0c0628888000300f4419801c0f035282000d80005442c0210076900e103a6262030f09031140e5800e004450070040d101b9515034060400014a1a40c7c0780c4503000554882c030042c9c000e480c41d0240c042e140e0741e00a040e01050080103894001b40000c401c103001e41c0714000f46008180801c885a00341d003889005141d000b40320164120944441020f90060442045000800c0281035a11500b040d0b1080328074039030071641801082181802c03804042480c106205144a94146c90042d0340028500100d0031003500c003040c481c01d420400d00c2010302c030200501d96682401c0356451050b5024484c1d91 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 897183552 1250 897182302 897182317
    0x9060403080f1306050f16090b09100c0501020a022d0c010f0c05060c0310050402030f0708040510090b0a0c0c15020d020f04090f06120b160c08030a0c09050303070503 73
    0xd001070001d89051903103404098010303004000509207003141e005881403c642d00c6100f1f071180410a011284601e03c1d80b07046840d0040c0640c00c00400004220120320304d018100100806618050003241d000c0c4020841102d65800809500d070741550840e140300158011180741d5203030141010103411000c0f03006101d2000034a41a81d80c500c031644103444076a03000030b01800921441041020901341c0310021402046038910b00d104c0075540e581000180c1c80204c50510342e6200c0e000103c1c0407140140a03039034000e0322441c1a5200d94420040d201e04544440384290b4846941c0c0080c4000811944220f0501d81d000c1d16040503c1002030b2503001545860342030081c0d0503a030004070020004801d80c180c1c0d04901813440b20b20340d20b039030300c00f000300241110018604aa515081c030000e801d90009141e407030442e03804108441107503166002c824190307180300140030a22601007055800288510b00451240300c0102002411850359407000344200d0031a00010b0013130b48104401004210000265880f4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 897184802 1250 897183552 897183571
    0xf1b16030f0609060e0d0905010908030408120c0c10090302040f111806040f080715090e1801020f0a050c15091f0617061504150608070c14010b090906040308 69
    0x460703c289090320007040756400188044c010a840307081e07079a03400794a41044400990741e80b400d0980b0741d2000390701c0344500e2190303010541c80008140c1004a140c00940807c6140c0400e031520300147c04086900d0b20203d411080004121440500071841c00d841a24064210203400300021000e1080300354092242d9502c04a585c8a0f401000c40240e582e0000c440c09030659016804c44e8980c2c2c2c402c129500c0720103005104016000e0380c1f250607000c1c8103603100e03800c039100310600c0101038540144c262810703488100d003940155001c000c0b045000c1001c1d40180040007440d0354490351031900492050500c83e40c0c02d910f0340d06403000340503c003a07190001042e0740000344101080c8280d1149503100c00090803d03902c071039000710341d403505100440d00c08281288642002d01d502d144224000080104554180d032001040644849060014500c41c50115900486a040c84100c0700c000e034580e40c00045401e0b00049090703444500c40d120301e0611001858005a40d2001484103042c15500a80311080040c100002d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 897186052 1250 897184802 897184811
    0x5160801030f06060b0c01140c0909060d03030207080a050417060f150a0e011d0117070b0705150a021908040f06021c0c020a030f0c0b0411060f1b16030f06 68
    0x70f00c90749600c101c0052201c0c0c0e50540c5d4070190761994901a003440606140d2000c50f04000400d000c1808044828818004041903495034600c010407000d005a000c0c250100b40c0e00380101e400154022006042911040c0c4805458600e400003510901c2d00d00c040100e50782c4c0001041c408c4a0028400d4150492601e65041c40c2d20340d00800421070444007980428403404d501000007400f6a92201c0000503032100340f00100c030580c3c0b140e0003c0c4c000d4500e80b00007001c0d584000b8040040c1e404d0000a08041480303003007610140e00c110080605110400d03100b00703080640c00540c2c00c440c4040b5044039514503020382001502c1d4034241c3c60302c484410b07501401078902c9400181e60b001010403804c60a12004e24a6010012141300071402565105980411000f00d550299000c2d6501c0c0503810440700300703512400c1c2c4101c542d01c1d83d072030265000c2c551a1031908100244038988200030f030790f4040e010943c7c5001500c1010b0b05d601d07281500c4d000c9440c2d0907604030084882d007400415050f456224415401078800708 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 897187302 1250 897186052 897186083
    0x6050c1018080304110a150915030902041e0c0f05040504020702042d1d060624041e0e01080d0f020304120f020103050114100c08070506010e0106030516080103 70
    0x400350752440005180c514004204810400703169440d884004080d103c4000c140c1c3c0314455050300c25120303281074000c00c114000c1002890b22000c5082a8450300349004130f0011020342c08a0150358034589c1c0e90722030030303000360b1240c403401c1080c480c0140c0500d1130310706000124200d800c01380152155014207070040f5000076014041d03444076000100c405643d044081c0748500704400c000b8000501000c0b01808a09008403c0c0405804802d50101c1c40e03000b0014040f103854800400500e0f070f1940b5000d280303400b480109200301c3d001030301c01752009142d0340c1606400c420902a00d00010b04168008041d4911204010301580000160f02c03200501182402c0c2c0c0b04c0302d1b010034140d140d809185c1c440040f07003040c48000c20400c00c91103800c20101d4800c2e00c1c1800f250340c0b50f24100b4041c1030701c45c00c01a00415018082004648030302c6410507050300814260386416000d849450500320309070059441114000300401059030305109040d8400c1688081e590800501d1400504400042c8405031090a0004000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 897188552 1250 897187302 897187331
    0x7061a030316030503180f0709060806010b0f030a060f060c060b03010603111509040513030f09030809130207020402030c07021c0804170f0a030e01020c01030603020f060307020f01020a090f06050c10 87
    0x41808024802c00c541f01850100c95080e0b4490b841d004442820341030101c0051806000580d0b14183c0303c011206605007080244210b540f50001003003070600c0f6841d0040001d103140007403000b00161060340c1d944034004100342805010382c1c40910010380031740e14003c02080800e220759070b060400001128141c110482c0340310281101c0c0905400300327601500c0c00c018445d1051110344a050200d12948801c0510480702c00b003500c500c2030601c009820198108401265844c003614004014036940ca801801c25015401117001ca0304110340e1400c6c0008002050425450f09148940041040c1d0901ca20000050f42d242005400355101d03090341d10403100c019040c2e004041c004d100d041d04a103400c4a518040702d080091182d166031050318054000e0b441c0c24035840d4400d004000907250090880c0d0500e4481005004550340008c00c21011030151600e260558a001e0000f06185c0c0d4441d59105a02c0e41420414026100c84c3e07803202c1c0900c503080203030580286c008114186030807180c1e00001070224660504 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 897189802 1250 897188552 897188581
    0xc03010504090f0c0e0a0e06060121020409141f03050d1214090a030e010513030f0807020a030b0417090319080d02041806150504090504080d0207061a030316030503 72
    0x403c4c203141c49102082000744110b03442d100360140042880850b41c80c0c039559441c2c1c8000d444650001e9810078232086644039105a000d24003003a000300524040e03840107150100c601b006002440000e050061048010780100d0911380110710b04a2111140d02d15518160382c3c07074061420100b0710011310750111a00341281c1c420407511448041c42e080d24070344400c51540b101d185060440124040090101841d44600e081e2183c450307103420201406070550f1203100d104000140112260b44080100c078005841d892041001548200900700503803e15203000c2003c1103101c0110a61031000344454506690001504500c1d0620300580f16001c021505080711544613070384203095442d000007800511200302801e40444041c1d591401c10120b600c44034803030181c491507402580042c00a0000b0310205c9810b5000c560414890380c52603103030802c9121160140d03009110146d03941c581d188140d10881d0b0001e03c2036031000d24101d001c1c42c40d10515040c070811400c0c09400c050200b004c00f0001a180030120802d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 897191052 1250 897189802 897189833
    0x40315090807030201020d290910090c0207170d05040506070c032a0509070c240c030515010809030307050f0706330b09060f1e0417060c0301050409 65
    0x101e10b41d5070380712410301901035440007030782c0442c6c64a0305a0340c80038160418807000e60000d10034684410340041000b04008e0b0313400903225540c074110154000400070407520898141005076006003070846d1030100c2106200c00b20581c050441c2c1c111056102c0d0240d4000125000d48000700c8880d81c8481c0c0e0b6051400c40180e05400c0105154507200f16060290455100c00980242d90032004030550f848605202c896401510041d010440c10b0302894002802041d04495002c22004801c0f032110090000b070055640d4041c2ca00003080d81c0c3c005020844800c5488250841d200703080204c85400c1400000790b403884001c00c60401c001001c101a0018a08141160046500300c60280904804d010f401407500c40703d80c086100c5441409052955546060b0007601282e000203140e0781440c84c0349041c01a190b100091840b21020301300f202030055008420004002c4070311141003a12a81004441c10007207045481c5101154805804c0084065040301204c0c10348034103a0300814920305c81e1424a8041d0010b41 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 897192302 1250 897191052 897191063
    0x18010e10020d0f1409010614090c07050a0f0c06090b160b09010204091103090c0d030f08270c09070201020f04120f0c03060c1b0b0f100b040b040302030c010f020304031509 75
    0x4000b4071121a0800030f074059002c5d070008000c017964501a039030007030546902c01030304002071a000a41d460071000c003600c800350140e4282c84810b2410354840b07800c0442c802c0120303982c00e03002406100d441e62103103440d0040c042e103041c106c0c80d040303401c1c800308127400540710010309806a900015601c08020740540d0010080a40140f207011050548000c140d04204c0360b10b4170318800d480d91054285040c040070392000c0e1b015107500c81507490141048406410092122407041801c5a0450181107141d20001d5046c1c000e0003d4521034241c202005801e100180000085a0051250415a90940c000c40e401c494035180703128000500391800040c030084440000c0c090304030b004800410f00003160081c0e1072040d200d40c3c504c3d81e44110228ae010640d8012179016025400210000340030451076150b0795000b40000f8003681080769980c041c0d110941c01600059001080070808208506040040d5104d47c042400c0c10300c2010713110900259240214072001c0d004005a6400b00c00307043d42c1e80e110140c000e8010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 897193552 1250 897192302 897192311
    0x507050f0715150f0918021003091b230f18161403010302120c061b06010815132d0b150a050409050313030b18010e10020d0f 55
    0x2410b04012150059801d1664a814895003000c0214180d26950650f102014a484410f0402c02450024514941c510402d000348000c5400541d0b54150f9200034440c2c0340d6408106500a03145c6a80c81c880d00010b40b8616400001040c00320388010001541a2700e10790b22542540c8058000180390201c880c0446504140308490000409400d61401403090982081c61529490402421100c030031b1a0f5030aa11102c2007400103000501d41002800c0d1440c5c808070031605240300140000310700d54895124800c00074101507000550507001d001035801004840050f010030900081141d40152000340310340c1e8612074402240013003084000c024110428911760100c08505101c011560000c8031303480540d0460403400c0090052038018000090240025060650191800091102402e07100000b110b16010034070500124040304200070f0f0003180504a02034441c1800380040344c1392000d01f4600316050b410860051680e2100080c0c00901003e48000140d4980341c0040c0d800c000c002d9907d14004440c01c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 897194802 1250 897193552 897193567
    0x7052d18071b08043003050d11070204150503100b24120109020a080c0c07210506090a0201080c0310031113051609080a0b1f050312030f070809030d0507050f 69
    0x182c4080c2107a00c10b4811007045100e1441030120320440300f905c020001101004211803100c8c0e02e030041c2c419100a4441282040d01a5000070280c4885001e806444250b40c1c40410061808008070441418210020040b46801901041744c504900301c00b100c90080364503c1c040c1105500d0f04a400c00c0e00c1e008005406540c403401b21310041d40c00944040d00054100300469a04c3e00c140342180c5224109100424406140125403400707000342060144806c034210782d40201280003404041d1007505207502508080f6001c0c4009800c40101520101ca50340050040144610074a03500e00162500881e072501120a20800515103503696061502c0703442c1464140400b0401c0c49030100d28104442d00d644c0441901c401c0e40540e261066040a4054a83c0c500491b1718905000b81d082644041e0484d081040d58480000c02e10340700c140341e80107886460000c100400704000d124440c0d0488a00d2030144514101b86d40541d035603000d0f134112461103a81c1d4401240e405c3d40a07030701f2120f41d040c245015548038401d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 897196052 1250 897194802 897194819
    0x308030c030106081b1c0612050c100503091e0a080d05060310022b020f0403080714030a09030201030c02070f15021b0a030f0507052d18071b0804 64
    0x3e10a01c1d01003a010130100d0f250304070080401a010710101c0d030b0981000601242c0550b142041620003100b0ba9032004081800c0810f45010744440d0f00074401003070f5209200044c08406000d4405c203104102050081c0b016403280460001c00d100010a03241000c154511407640c02d000b0210303c0200503000000d2202c040002075000144580381c114152022166424424802e0788500311081c13512200807400c0c1e810813003a03d07480740e01401400074010308001e0494040901c0740e00c2a0426a0b00c2900840c100c010080355580d02800100300300050b6040080c0b00001410b00080f6000c0281070603180c13610312402c02d1003003007004000c141da02086000715665400e514405000350f84070300c0042c021140d285208030003042500320040406046800d070280795440302c0b1441300d00b096003262203006003a0001061342e11500261002c01e401e0803a5084080700713490f03829202c104d0007940f40c01000740003554100f648501c0041640400d13281070100f402c07002d2000c071003450020448018080b440100e0301003641807 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 897197302 1250 897196052 897196057
    0x503070e0a0e090c10050915040503101e0b0105070314092223072105190b030115090e0a0b090d0e0a0f1e05090a091e030c08070c0308030c 61
    0x4101030242c4004d60400014441c0e5000c114542c0e0020441c200a8030f140c1d414150b2000300c0001001e440070303042580b0f4900103410300002c5141e030010503131111060400011001058110b250310f04004010700c183c0030001804a0103240000b406001400c005c00101c40c89807022136262460040c208000014007101c1c903203211b051004a000f00350318050529000d4034100144280380c007041c030108013595a401d1030442c2e001d594005a990304026510139120045580d0150700c0c0034279507020035540149902d580c21004c5070030040c00c40d4440e030304180404040d071140c2403035001542c04800b0040341d020090340351186484e10050004084004403c1084000180490110b0078000702d9600c13481d03000051800c0001c0c8607140d0252b0202da51280c0020403647c0c25500201d0100910f4604d03000c1d000b41e0f207200050003a401100d04507821901c5404aa0400160924801c0b510301034420900d410310942e28010006151480010200c20340061207100780f100f180030403002560310440d10f50396440c24801c03000c8181c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 897198552 1250 897197302 897197311
    0xd0206220f1b060509090a020318060a060509161b020102190c0f05060306130b0103060e040809030d050c070b16020402041d07030b01170703090206191b02060a0503070e0a0e 76
    0x44072003031070100e6003030320134400c81c0ca5400d801840b0285d56203a1100c10343c02035002a203c2c0d000500494111001c26006101d0140319007800f40700054150703d07150501803403040041070144c1c002d1961001c0c40c12150000c200300ea20f002c0c8054901125400c5100507850061500716030000c0b0340020240604110500349048203440004c011206401d907500d0500506000503106561b02500d0504c1c7e5041046480d40300d902641414900810401e42c5c40c41c01c09020311069400744c84c5420002106052030508100d0403a030b210741494007501c2d1035040048280c4659450003200d044210001e00f0180e40c101c1b010315280071781d030001c00840d9101d0742c94507043d90454550000d052826600000158200d0207407251299038403068444030b910342401200301c00d40c00c42c01003010701816030b110501d50150301e444000d801e070b400000d80320f54880864118086d0410280d0003080c2100092200c9000068030760307005a40305907115042a60700d82c1c40d5400283e50091042030703403030f4201d0542c000c0000c034000200d43c202d008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 897199802 1250 897198552 897198593
    0x207051306170a0f02011d0a0e0115090302030c0d030908011b0212160b04060e06070e03010b040612020d0507080f030909130b1b070501050405070302030d020d0206220f 74
    0x3000c410301e543ca6401c080d001030b28400301ea4031041c000d94051a040c00c08060415095003d44002200081c0030005680044247c0c43c1b4040046c401920b4900f00c00c05d1211a41c142045076600e90303400a0f580749800d840d0700303000e041401114030070580641c603254041c00400009001903c0c0c202011180d100405280c0c0d001485003040114402449004458501020802103001d242e01030311003200c0100041c0007160074640c1e52060700d000308000c0c0f0520b40594800d45c0c900b81c0c40700c90141094256040d82e00301c1807081d40f1707002003040208140d0640c201f219905643d40c017a00d0311720707042060070146980d1084d07200b03005d620201201090003100904140ca800c4031300c0d560603101c49011054020714100010301307811029010490417851008602d0500300d44240c610700e0030200380d485c1400d4a80c15113007254503a104510600c05c510302400301c4c10007050240b0050102080e2400700079036640d405021241030f40d0544680c0050014040341c00841c01e904068030400e0303407107a80b822461400c10711640c0d050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 897201052 1250 897199802 897199829
    0x604050607090e1509180f0a11040e03092803051005010f0503250506040609030b0c161104090206190801052706030a0615060f080f040b070207051306 66
    0x200025240c045a01030701391040b040d505040300e54184000003030003410481c4403000d41c03029007607640c004024500311701b0f1051024004441e1545444031858075403a00c0e06124a0a200318204a400000700741c86407090122489078603000c45903440f601000ea203c90324110307400b0501010062282c00030311660b00341852102001a0382c0d841001c1d40080c41c0d103015840d40f6402c8240c00100200c010140ca002707203040e04a0326091a0341c0c0c3c02c00981d041d440b640c4008040351640b0030400c1400074503c0320b503030322180c09241545040c0362005043e060211081000300008500070441c0300584442d03010750b440a42c084e1516650b049101d00780403641010203060000120528004611814415100c940e68400452044000e0f00c84071010203402100400c150340520031181070401054050254207082580920158075842c00c01100034000240c0090ba0824444543d052001c02035440760029403044d04072801080355218100d0032400c02c241ca43c0070a0b8404800039000d00601e03a5544000e00f200c03840c00c1d007540f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 897202302 1250 897201052 897201059
    0x82107020c100c0b100e090109061a010c080c1501061d040b01020c010309110406060c0c1a0d090201020c04050903040f060c02150c1906091e150c0c0203060405060709 73
    0x280d21400000300000e03030301a8401c000104018400e9412403848280170180e50b417150242010719008607014010341e915221200c080c007802c1e110b40c10002240c1100c92100210460011b41031031408000240401e100082e0030303170101c1c0140f10b8180000705100a40086594810009165101c0c12031213a02c281401c2802c40268078151040103015181038015000c0d28800d20700640080c02980c000341d44a200c4102d04080075a1184102d10103004692a80800714815052149061546070808400d00101c20005c090300c1010340291076001c001000085404242440101d0500c088015030035041420801402079562012002c0c105840046100804442da82c403c1100d015001e0314010f908803590500f00600441c1c2c100c0203000c0c034103000301280c210f013020043c001e2169000580c25a030700c603600c4507400d0800c10a00303020350485501041c086142c050701e840319a08100c02c0c2c4c210208a680d40c40245003801e00615040d00c0080c6c005050700e040c0d103840d040082d1a0041150031000081c070105010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 897203552 1250 897202302 897202309
    0x12120a090311031504121b0c260304031511030a0e010f0221100e0c040f0506090f09071412010513150314030412060e0c030d0e0d082107020c 62
    0x100c1c00c0c04200b80014040752a681c40d85208082110781420812048040041030702d5034145e09031f00c800380305502c103a441502c2c1c1204400b180e007610441c130102080300c1c1261281c0440000588050300e0f00031401c0244040201d0030800280703604000c081e8002c00105c100008100c045e440010421041c43c000d04c8142c00c000d0b483c0080748a111142c103d810030351500760b00030515150000b5807120380440e1100d401034a4002c0661204001c990000c41c241c800242807001c4101922014000c050a0720580d040107281d80000780c411882c005068010f200782c00000d96064480c4c90104807002c0c08048217130392000c001c483c03409664004d00550307010707110328620548240782d2480703052126840a4150b0f40302504544d03410440c2c4070240c001c0042e0784024440862419914600b80111a2184100007242d881c8990f403103042051329131030b1504c241c0080c10f00b0201d1a8000c100c0c1203000d40308613000b02e0600021b01d41401c2d236018181c0440c55030074001c10714490705413400d0740c1103019858540032034044002d45002c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 897204802 1250 897203552 897203563
    0xc0515010b04030b0604090b011511010903092309090c030f060f0c1e0f09041404030f030f0222030c0b0301030c03170c0a03021e010501031112120a09031103 69
    0x1030041d401c1e0708210410100c4c1d102e02d440e5410000062000c2600301c00c685440c200003d080e0000001d840071080b003c614650040410b4079071417002d800070b0000c0003042e01c003d4184510b910840c0804d6498060558403218408000258220014070550072810701c4d4a0179945ca2119840e8540288201d20001d0326460300040c1c0f40d8400c480da617051607031603654544040c0040c0c0144002c100c0280414240718181d0010340054030039006d50744040ea485007100c00400084d2902c1c241540303466504c131400d11012a5000c00100c1c29030150341808200b42c8540c0004e170000740b003100b01a80c2150041144d120141e81c82c0720341007084a02580010030845c0e00e48026020603c002c0c40020045000759404100140a548010350300c4040c1094040c101031150b10b44a041c034001c0745040380140c100d202814a045400d040720b0b0f40c0380c041070000b040386d581541d5410b040010031081840c0300745030300e070203503d1701c40d004111042400000000311030315440c00a00283c01600c087c0004c132070810154803244207174200000d8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 897206052 1250 897204802 897204809
    0x201090b22181401290c060406050604050c18092701021e0c07030b0712050a0e061f0e15030a050309150f03070806010e0604080f0d05070506010e090109120c051501 72
    0x48403034100a245c007619494250141540441c801d00100c51000e8003403040c0e910443c02001c0104441c030788a4108021102c0c002e18104490405102140310940b00c44061407200006030307010401078441400080507192445032000110b090381d500d40d54407242c19006420480d0301a6070100415a280d0f652800501030010b141c0c27807650080c002000810a48504240c015405003006990700710038654400540d50200c55042c2c140352184044031007c0e030304000490740f00701f50310a81801341c03002540038030340c08400d8452405030341c42510105d1012401c94105006019005080316511815460030585071340000b0212880b440c000004d00c96040c3c0110202c1d056003004514a44c07650780e555800743c40380c0ca40a003a141c10084030130101141515400c00401c040c0c84028001c080040c111000385180401403200482005020700082000400004403d130541e1000041aa502e580f1484498018484054003928100d00511b1900307203503404c914501122801403080c0d40b40210030078001ca241c0c6d10280b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 897207302 1250 897206052 897206069
    0x50106020a0f030c08090607030c03140a090b0315091f0b0f0f0a09080d050d1811210114070e0a06080a09060e070308030f130201090b22181401 63
    0x295002c0c00a4458404500241e1098502500709030030311021854503008188118040765480580e4024150002c144903209010080303014502040120001d2501c5014840c0310b1040b84080003180c2d03a0305002d60900c0020380003a200e551103140a403200401c8012000c0380884081003404085515503101080f11441c051001d11940351441c02404806117a01c94030f004001c02c00103d00c042001c03181807007205032000300707540d6103602c400f086800c03030046454101c8148002000400c0381b10015500440d00090300f00304944480405136513802d501560000400c43c02c50700d500e8003840780c0c0010035104802e070081c845a55050844d50f0f1000500000c0340317460140c0c1000c5200507000030046050b9401a091061246202042c4401e20340d01071850032200350400c03607d00e0000701c10000d85680c000036180e4000d07a001072402c3d010701242c0000c1c08004060081d9400000c00090400904200705c031844a604000b41550a80550f5440101800010180054416418242c0b0340703600c41c90341c444a906940c0b422 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 897208552 1250 897207302 897207323
    0x90b0102030a08070201180803090c0306090715050706050a02040303030c020a020108061005070c0b0414031207020609150c060402100329041116030f0c030e041a1201020d050106020a 80
    0x710010f40e501640241008210364030b892039030a50031107845070258810b1090a8194a900781241c025041c1b444103c000c42c0a940020100420b141001035820700302d86584101010000ca140710456540c4a58030000d00014104030600510b010b450b170061046034025030301084801006201240c440d0100d02020780000d04401c0410755074130f48a010349580c0345031401e10b589050071507a41c00d046240035a0101314003680200302002900c2116001100103e03040300030340800045400e011842e0700900c200640100c5011400d405180c6416080380414007228041a4461002c0d440c41907076008203d400701e000348000490310320414024090f01261202001400c50240407103440c00d00d40c03021460704c43e58010b4039000e4000342061030100a0001c60b8058010505280b014100a4240614000c0c9130040122505203100401d511180c0b8417414034040300d0108040343d0881080046500300c0d4042980042c2e0b02e000101f20755015030003841e52030403480302407109a07600c41c0103a0b00e50700d1045010b085045003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 897209802 1250 897208552 897208567
    0xa030306090203060d1506090e0109060608060c0f160f0809010e0103061a2a15060105040b18040603051902120106060917030c010c0c020306100807140d17040f090b010203 75
    0x50001d03129000c006c0640001301c0359903d04405082c0c0c1c0e042d40c0c03002c2031b0b41d41d501d40c880f062103980d01990001d492003000a25850801c02c0142c0d04a2044071746109082801040c10400090482803018149420480716044048182440d5200358030900f00da501081001020441d0303035000303004840c1201e4000f1622883e001c0d10a07035100d03c0d40d00c01c2d0610141c40c444410080b230900d8030400031106031509100203009007810714061010020000d807d860500006010400009c4000421199038103444040b603024408500045005010f1a400042540c0070b980d42c50f4528610086048181900882d2000c0681e00d0035040796080f11101c0c0221400030350b07400703000c0c011090841c0b83c02d400c0040510850b0301d0500042e48181c21a1220780700540002c80c100301060030352400f00308681c1c0051081150341d25592502d26030a5407000c05125584108020b80727202803955441000080c0601d4014146c0a0640c03212414203109071300c6405540001001c400001c1540205840303019070350141a0010740c5810b04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 897211052 1250 897209802 897209813
    0x80106020d0f0c0b0406150b070f030c050f010c020309040b04061a0a11031305010e040b2112040b0306010201141905040821180c01022109060a020a030306090203060d 73
    0x70b80d101c1c0e0b000c2c0081d850030310300011103c81d48588128042d070400190700780ba4020141c081d6942d40d00244080c042400080045068100607035001c56260170400503000b0f003032a2032820069072150b101d069501c0d141c284100140c002c0014540e60000b11410070251040d201004115080d900a120b6000040c02812810401d40002042d0042d69414008002c000d8429924556402202e41c1d95600d41d00840030003103540c00c500044d28012080b50306100720349980300031820b100c00c00c0b442e00e8011182400c00d82c0c01d80009100d01c0d46009522005182d80c1c0341c803821000e10940c025644140158640504a00d030340d14108805800744061031202c144880070b00c61000090103000c1c000b900d03901000c012095031140d40301d60505d0221084c00300030000d444c010041d10001403c0c09910507250f08200e03d1102540ea0100b100610740c1812401030f503014040498143d1107000b280351840c2c104400141400c000c6400154003800c06101c2d541c03c1c028591149102e10a84c0425103e040d0800c083c8811140001c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 897212302 1250 897211052 897211067
    0x22060c0812060d05100c080a060e040201080601180305011d01090b130c0b0a080402041514010503153021090d0602030c04090501120b060111210d0b01080106020d 71
    0x2041c840d400030709078441c0b80c01c0501c40d0030316581042d46d0310a0307407080c1908511003e034420503520080007403034900a5500d0a0860003000207040000d400d0000d0742c1c9070701400c00c40d061609182d028007a0943c50307181c035a009210441046049010030b00e03110044120500071400b440d075010300003401c1c80d01c0c2c0c10020801841100800c03900040702075004680d103121032000c2c3c02500d04a0b5502051400e21740140021502d015404e0400e002d4220300500c003800084503005245c44083c07915580d2513440801681c01c1d00d01d9036003d070b0340c8080001d0120000b090b4408481c5200e502d012001c68140303000001e001d5039040e120540c2c0001500c00600d182510b0700b0400a000310340406420700c1c0210700117a813890100e078421070340281160f1010609011003c0b0034440c1d079000d480181c0d4500700401e402e89980d86902002400141081101e01107200c07414420b20000705107462441c04034510039807038a0016000e0b04451141901c207494015946d5556100c0d84c0710504a402a4000d0190a041224100c5002c0d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 897213552 1250 897212302 897212311
    0xf06110307050a12051c0204062715050c010c05031e070914030a0605090d180806010902090a121a06040c0c03080a0e060a060501180f05040c0c0822060c0812 69
    0x9000d12201c101042ca00c160898030000711b400040e902d505029028042482450214091003090b920450417201d03100ba80109403038505010107440440e00008072010f00c41c4a071215115420720f0300f04079642e0b4000d8041c5010700c0500c00000620341c150300350080c440c002111654005000e0034020001c4070181d1010070140200601964101c201c5515030358240da1040d950040142c2c08828160701c2140c2c01410140d81d01e11040f0040f0025240c400b5403507031208107028540e20306900103141029075540c51041c1300100483c00005084400c50b0a2852403203184950003d202030902000450520b41441108882209500c0c4c1d0030410b80303035450449039428010044150181e484001e000f4400c41048502d118461064000c2899400c000004060500400e142c0b06903c0c4c0c03100701404040780750080c1d0410b60380d06440000b040f048007d01294060f4282074003411a1a00090501600d11414881d4800e9241c40c3c91554130155981c800301c441d407440c0c40300508000414030481e5201d599034400306802 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 897214802 1250 897213552 897213557
    0x12050a06200a022b0905150403020d03020105061504051c060612080c010606020c0a09110910120b0f010e130b150d0605030a0c12060f05010f06110307050a12 69
    0x444000004210702d9006200c1600542c0c881030070006410580c1c4004c0101011614810036004030307040015281c2e006a021b00380c80355524440360142c0d015240c05540003560000c212aa8800d80740c00d001e03000740300648925000d00440c3d042c803415000b80c601202d04540d405009502e0081f1082d10410880b1410300013144e0043d2103280c0010620101c40d941a89680140249a0707136141000901e821150b4550103401550881120440c0f50390310058032008952035a000803070502c041681107481ca100e0340988507401003400350444070b078030340c0301008444c144180140ac1201030000001c0000f907514948041e0f0008464020461480c00c1c41040302c0203000154034049001c0d144900040d00c43c4a9402c2004041c0c41c01041868a140960181500a1109802a11030480e090711400b004504501680c0d4000c00741d03207241003c03c5010740c009010800049004c0029503101d40c0103002c9840b451240c2000110100e0b880a0724140c080111441d00b2392120040503007801c66074500c15040104d0a54106 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 897216052 1250 897214802 897214841
    0x11010302072f091003030c0209040501091721090717070506160312090201080c030415060b0a020d050f030f040f05060f040c0b090904111512010f12050a06 68
    0x242080b00c10024031038000c01e2000501a22150b805002c070329080100581c4660384400400c201094222074003080306034054a08a46aa0f40c5007850b03409000309000042c68a1200c40d2129004284000039003400501031030b6440b400c5c1400100403541c0300c410b580c800107e80110320308011071100d03c0c180100e007001d10010350300c40980d9400010074942002e0001a104540708010404166005070114203255541808000b8940e803a00020410765005100312140d120000200e0709001016010100c500141203003480510344404884007141c228007403132409403080c3c070400031140380035405464503640401d40060861351000104140c019000d441500c41189500040003c030300280580c0d882626207400c0392100d4241031038825280c1009a0101009140c1400b00d20010f684075403444e600305800c01b050311261501c0000064020840002d003440c464000655211554802c03014141203803113144580e40c4080c0d40c1d421088081c0c84868004100d07811401010000603003e6106070100e8400c07504100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 897217302 1250 897216052 897216083
    0x50108090708070e04171c02160b070e130b01050d02090d020307121101030606020303060d03201e03040b07031101060e010305150105011d04050603461101030207 71
    0xe00b441c2080e0004c00710a041c200c104014442200c04801c040608030a0b6a403801120f4684904000c2001600515903500015a1039000a920000c080e6480e0080c0e40f901d883d0a0401c405040c104040805a000312001d180c040001d854502c114602c40c00181c4030680740540c00041780009601c05001d33a540070088060170000750b102000140082d04290300540c42190082c1400084a060750400c00e04140c10202c090201e20740c0481525000300041d10480d04841d0785d4582036807030094800c030401d0031240b0482204950000041c03000510106034a24004228801c0161502c1e48901d0103a102e20000400c49540001d104403001d0340c280666400000f01e030381d160035201010200a03402a0b48a41c0651880d01400340301c0d41d1300500500090030085040d1805000403083d094505400c0351189545e9400102940c40902404a82d96690440c04030009040301c0f444000740e101c1075001c01100058120000c981413401c00b014611601b012581400c0050140114082c2d8042d0404032002400f492410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 897218552 1250 897217302 897217319
    0xf0507320c07172e0f0f15090903171005060703031409060103020a050609060c030a260601170601030b030d0f1706090624040e061203130501080907 65
    0x4001200700040a0100c951402041604000d140510528603400106802c50301002484204607250f142c0b4480f20119140c08622800400c0810181d071000d1341001c2c1e03d405640c1503540415000c0c0000c2d450240c80c680c480f06143c00f00d072000382c0014046426008064003500899081e582e104211388681e9a44503200c60114410350012081140443d840712858a011b1804a00c3c2c541d0200d0f014004112039031640d000142e841e0064400e40b801f450b0700046500d95600c0f200100c0d0f815040420032290380d080f000c400103141103482c0442805160000d043d00001a0900d40f100380140d505948031980c195030004100c2c03510780080d015506160b503640c400c691545080c0b180f02e45914145d2106440d42c40d01c00d801400308850b4000000b80045102c0801c005943e6031084e03181c02041c280e03007202507120342c080e8410140036015420800c000c40442c00103901100301a00510030141910308000c06100c540d1102c0d9039004001d640700c072640d2500d209106552080c4640c5600a00c410704841e0099a02c8907007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 897219802 1250 897218552 897218557
    0x60c0318070605070c0e090a030f020312040b01090506060a021c09271d0a0b13080309061504050606031f320612161709030c010f050732 60
    0x440b01041c408250a400e20100b0451740000346603002580c0752910342046000d49078540030385c0c02424040f82c0340d6140d404038800c0065502c42d83e2418802000d0f410907050850f002002489051481820400002e1280c24800240d1702c541e25141c00030120f00d0a5181c0c07a80212158012074000c1140c032900010f80c1164031074a40d04101010040240084201c0c10303124140c486403030300545103100d034540741c181903040010725804590304201205095114082c07000713548480702070017500c200c00100912134641000b18096000d04214040e400004a14000b400305407502100e005034005000d000180c910451507002d09070000207003043c003010503241c400051000a026200110341848180310696420f4440c0000010031340c1242e20311300304680b8580c028411340c8010200324a0142c9205002c180d00e001e00140c902040303140c5240c10907850128000d81e9240c03c0081100d00c15802c00c203201220300614071549020b4440c1d65500044030a482c00c80b120700201051070152584501101c550041004102 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 897221052 1250 897219802 897219809
    0xf01201c02031e0423010b010507020904150203100801060e10090507030b03030a052101051f020316030302070b06010306150c03020f0607020c09070f050306090901020d1b11010e060c031807 83
    0x20707030001902c0205c50349140d102140c98030003400c1e13261001d0480c5d16078110007522030041c0c0c11110000181d5561801004d03206410f09423881c20f50000c1b003481510203c4940d0a8140c4409074001c0000c41d41c0c40b203241c2c4072440c042d207120424442451060203524180c1d000039500810508000c1092140103010a1855210008440000d01c0c04141a0701031000d10640402402c0310f5401c00d480355040c840050b004060040300800c04180c0301340c1640002e4024401d41c3d40c0c01d0700c95042c8403071f02c0c095420040c001e0351203080100e801d41d03030040001d035503507000703204010039245250842140c1180c50401940c0d03c0e404994154203502c181c010144846604000451080d50b482e4041c1036240e1300032040c0815004060802414044201c440750045940481526841442190700d26869140c3c500c03064020702c13a109a5040c540e040040c12420080803070001c030006003240d500c500c4200c003415121400c0b15000c0b010091a0b80095001c5404480c021000e0350f004022506000e44581d082001c040c41c00406a2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 897222302 1250 897221052 897221063
    0xa09030c12090807060305040503030a0903020a080c070e010803031003032f0d08090f0c010804140303070905091819030504080a110301050a0b031504140f01201c02031e04 75
    0x21080c062074000303004e804010300d014241400281815514103459000c020704291001c0d5660079240c0905100300000e1141942142c0c09a59034464000440c0c1c40d003500d40100d0708410007410000529100000c2124421400401c00310304050669804a40c4010070b5409262a180f040321402d40b400f120440003848046c404009040381001c1e40d0300581065001458901581c00041c11a43e480740f02143c107054a140910384003600d903440785440c40d034007844200424190b110200402c52402c0c0c02c02c041500750b80b411146650160b4400c140340c140b0340d819140c150f410340c01003802d2112440a280c40a40543e05c60700b13045051a4460307040d185005c002c00030039110703603070008a141404c2c202032248075004000c02c8402d000f01030a910101e9503503001080155106400440001c0900920b0482c003000001c00c2c40070b50b500d5a2003103604902800442804401d07134006441550302d00703000002213608100f2118078889808201e40082c0b0001c1d0002000c508010702c0e50500c00b1303c220003005043d032042d403080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 897223552 1250 897222302 897222317
    0x2d1b04090e101104091104030605070503040b060a12061e090c0306060e060609010804030c0b090c03060a2a03090501021c0e150c07060f060308210f0a09030c12 70
    0x7141e06441c1224415440d0121440d11690036800700004084a044d503280910100d014000c1400b544550b10030396101405861410b0240003940381c8c0000254002c502030016482d10307403101d10400c41c61400034420300180303003040d45070ba00001d45144c100006c500c0e0103c02c6001c0e241c507041e100a0503101e4852084401400f0340c01e0034010000300d40300e81400f409032004060030501d0102e000c54420b215a09500341440b01050024080500c5041054140c0d680180d009009091403040150340b480c466004034030138058a00000c1c000358685c45904001c24038010103141e544640285180d1850a084000302015100c8221202040782400249030601075121402c000c540c00c010200104d03404a0b5079001580c025015070300016110411964004551105643d07a0f400c1d6460120020985169001109420303d9000814825064040c0050b460802d41011142c4240b107944040e80390206c4449040c0a15600440c0038952180c0c01758604510034100000c2040b200c0d26426010140d400303904000402c403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 897224802 1250 897223552 897223571
    0x6030f050a12020606030c010309060b150a0e0303071a0c04120b06041112060105032e0302010305090601290d1a010908030c0c31090b2d1b0409 63
    0x11401e520350b03416910103041c043c1001c0c00025141e40c00c01418504040e140c0d02040c090106a41c08440055401041c21a42c19540069405241c1119408402007003400c202c8034001c0c100442183d41060f880490340001c21b080c1071580789129406000000c1c580018400400d4100744201d604a00e43d000700641ea90900d044000c11003a16020101550b85070380600c02d41030070b107105025184d0001c3c0c007420a50746079610b50f51004d0310890f11f284000b0b44070b003244561040702c652038107554042d02e0007a0f0f424440ca58517415550390f540f10a200e4840002007582151400e44580c918400030001c83c030140c1c03444d03d071250448605440c1c034400d201124150b016034041030b0b984c01440940080020318061424501411310880e100c4001d2200e45010b424540140782802e8000c00500000b01205641c03001070509240d2000000c0003982c500b01c1d8640c2e0410042420744440030446801030903940010360441100101c40384036980060300d4004000e9140204030240980700c406400641000c0500041541c075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 897226052 1250 897224802 897224813
    0x6050307060801260303040507031b0510030c03020f0a0e030d08060904080919151206060207060309050f150a11042103021c0c03020105010f0528050d0309031203110a030b0406030f050a 81
    0xd5109248150120520100701c42d8507500400d44441000780ec00103515207007123900b64064401d8a2034002c41c000006a1030101d01e41081c451100e446080d4225413414000c064140e50508007074a14961003541400064000b078084401052001e6010703020540c1802a00701d100c0407201181c001c0b91201e131008105609041d44000a0700303059600c0081400007a25120010b921865a40284420561076010740801d101003041084881c1c0c47d603004030358903201040070303181500c1400e454040c120346c24482c41e9881010364500f90740c10780740d114103004604441d8000d000741c01c1e251200101c0640c01880f0544022407000d070442001101603444520810340303103240007821180140c200c20755010300701c1c400744850307191040c0700c04c10140d1201c54681d04981002d0041040380701580401c0d802018024050101a07000c80640116031090610340001010101c06805803002440c541ca0403000502030381e4020380c42034009d020710030300180000036410b440e6143d01c0007118100805070b0780d6500c04900c0350100072 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 897227302 1250 897226052 897226073
    0x6030b090606090c031f030206070b070f0e01120c111002041805090a020f1305240d03121d0111090306180703080a140a120605030706080126030304050703 68
    0x10840d0392200d030b85008016801d45010180542c444605141b0f084028041451041809035800410050703e44109e4644002442c80854070500012031a00303c1500b49400381440341c82070740050311118000741120003041d008080d4440840c00700180c0030641c00c1e2026040c0025100751500f8080581e80d50704141c444400007140170b00204040e4a008104140c1e00c5000c00c6c4a044194110381c1701c04040322420010b0300d249881c2e2030744800c951400c802d04c80000114130300c0052050000a0f0300d81129460001c0113440c0e40c44840103000b141401da404c1004a100303900c80d01e182880c0312400700320f00402000950031280b410f503010580d400700007001281d51a040001d203501404c41031954505100741113000f603c500e402d10004124540200b405003d0310b00450443d1240c180070401c50303031149158080146400c0c50084c0c01d13072a0313601d841000b18141c04c2c0070542c031068900039140e04019900e85290381c110856139000f0107800d81c4481180c1100300324248011802903004100801c4007a084d41403404018 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 897228552 1250 897227302 897227311
    0x3271201061e0503070b1b0d081e0c1204080d06060306031e030c0b0c090d030203131e050d14011121071e020c0a090f0534021006030b0906 61
    0x100542a01000207540c005045415210b00522186e258040c001500c100345040a800c6500703809023002d20400d150303003c2203180c804c2c0044440c9040c201344041c02100f4005043e21070b07000040c0308006040446503e060840d030801c0c42555003e180c1120040c0d5101100c98a4101c1c00000b0b494140c02c006000f801c0c03180039842c1c000e582040024410b1542c0180440900120050096110200042c00d14405a06452540e58050b0085222503001e1800940702d0340400b8445035100ca100b000815240f411041e5105401c15103011900e04a04010800000350a082412940407480e14102d00d00300e5801c2c042c1180d511102043e503034541d243c1441c1c3c10300310701140001200140c5000b0401c1025036101180d00079000e048010b42c0b0b28942170410803414031911510407500400b0b241000602c000300c80e031020404d00d943d01c02c100150f858080e000e10300e92000d003011a00b2821609028405140c8440000700e80700c041d40110360541c0d01c2c600100068414030791060b151103941504104a4290901600e58803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 897229802 1250 897228552 897228599
    0x106050c011d150406090b151804110105070501111201030210050a080c0304020f03120a170c0d23010f1505090a181d010e0c030a050327120106 63
    0x1644820242c00e50741d480c42c030007801143d42610301040a00000b17500c284c80003138000c072040b4100d00c0d0035407a00d80100c0884402c1d0b0300850016140d1503210410401c40c030302684d40141016511034064004613090f400402050340d46560b03c6803102241d822020003004510080c903030881c8551702d140100034014214a11200908c002080000403242d4030a04035a40000340307000481d26901e80340041000c00c080381207402c0c1c00d446a00124009001a1405400d5011540e560040400c003040780103024060295003c018414050002c8200001039030459440540400c0c1c81c407000b402000b0700d0340041102a44a1070004030a80d00a205251506544001d0f131601c80c00c5c503924014450020480804480c40754805825040d0000e401d82800e507000358445a000c400791585440a4158040c02402d400002c18228403030340c4030040c503504001c59003a840d030b0327040005141001114440c40302c2e200030b2407a416510031165260400c15640354942070008440010000a01604001b402e060608100404051 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 897231052 1250 897229802 897229841
    0x10614030c030f15030a032f15041a15010f030b131d0a0812010905160528031b0e0604060e0a0308041d1b04050d15050106050c01 57
    0x44051039070100d81e04184030039014102640d4a4140c018880c03c69608181d040c0101a000028168800051950021031520b48102c2c4800c90b50240f50580800d00900d805800806112169038141c90300150f210b8040c400320411424090304281e410310040300c0701541d0710010707051502a5640301d119003100d03207024242000b2481181000a5400c0101112050080d4540c0c1d0240c441100200312000002c00c80c45c00c4408407009440e126080ea0840c0d4051b0039041b4051000140620301402071500810103a60b460598400c0034000b101d49034000d6801000d064289420134201a070012a10200499680e1300001d548001c080426401d1221140036410080302060f0801c5661703956007110101d80a909140080001c150042000000e01e80d0003d042503402040000798104032811008294a80c4513000d4420b0350341c02495034101c00348030004504c1120510081c0524200400000d9425004415048444c42c807084400306a0300d098000200044001c1044d942c0903100b40600350100c0107100001c0d8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 897232302 1250 897231052 897231061
    0x1020105010e010e1308040906081506060a18050a090504060b03010c0504230306310f0204020a020c0306150102160e04081b070306140c030411010509030c060c010501061403 76
    0x40b0034103018200580d00080c011440440001d40c0d82d0582a501c8209035031925500c1010400800a9115150b0341e030042003101e03174503044696a42c5100c0c440003040c00b030070113008441c12100c0480f10a160300020754403c03c041016600e000c842401072100d00d10104080c94149000f1f025100e81281d01070090307040c04548184d05402c8002d84007982c454440c200d000020072940c2403103542c8000c640310303050b000701001c0c4005004410821818000b41c0d42c104192130320038001d0b46440743d21070078010f807040710880001c0340140f40c00c1d0014007000c006481182c61221020300046e00748942680d6071010130019540c841c40b1540c041c0241c080c140307903100d07100c1040d0b45080712007032800c0c0300180300410702c9000042602c100d880c40e4000403210801c1c08100c0b08055143c0c9010701c0103000c4c1c000a800114545000a10305114030811640300307030342c04032019424440e060015241034021000242c0d250182841401c440c0d03c0c4c14000e400f168042030008159545008405480511300d07a0021485d60010000c01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 897233552 1250 897232302 897232319
    0x40e2707030b13020d050c01031508120708070b13020a0b0703050f130b030106020f1501080307021306050613140306160c021306061806030e1005180f0a060b0102010501 74
    0xc60489800c000395040aa072409807116040c21092402036216414240c1c0300c081c040001200c212407042a00c04000f41d242c036520741800b00e02284201c03040380d404900303001100c015000c06807511520482c2440c0c10310b20a1394548024a5045900e039254210300e0003004298600110352070000e01d60340003a50715202d00b0fa01c0080051080841204120600050f8052035002118140001700450f4000f2926561980402911b0342034a1542c0e0445200324145901000408209207049600290041d03281250a0342408a1301c440c04000c640940c1e03079400001050788940d80104034070111280140340b00c0d401d10040f0120400300750417040c066070085080004128899035114a09201c50400030f0a8450603c00181c04441e6540c4c601081c03030916800081e120f410010403480f61040c1a070b940802d41d01da020031002c640b164061000c0307c0d840101201c2c405044c6a104540001a030141d0489019282c0c2400745030026883e64020680c0c4114940d1781806020310818030781d22002d100a00444d49000c1e1396 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 897234802 1250 897233552 897233563
    0x60403020c0a1508090f0a03080a1407050412140f0c03190b061507120f0f0f090b1e0a080118090503030601111f0626190309030602040e27 61
    0x349030900c105034000ca800145c00700314540c110f075560811511000400c0c5401025890151600030202c0d0402d03182921110302107034024070440055030707440c0c1400d06e404451000b0f09030402c41600c5110501c0d01c1c1d412801c0303041c8101d03854140c103030001b060025805002c1c5171806003040f981600d0302003140d05c1c80e400140900c4100e6084031040702e4503120413040c0c0007a03000d20320551500828140e00107250340d8040390000041780819249071614582c402c6485801d032400b012100c82c02001072105070042c0300c1c3c5180321002d40510100c40d51140d160441150021426034041c000c41d0004c1440030004202c4800302c84280b240840a102c400e021591050b5109070703070b81c00080e2086040c8140d4200451046c2d00801c02c608610780700040340d000c10101146008018060750080e00300110003102c0c00f007100c19440c0c8003c61074074150b1001b002c4800001420a120060300308044042000150340000402c81324000b410240c8104003080039907003420b020b41c0d41883c4440e481d0035030800031101302d40c400c0c51001c0350 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 897236052 1250 897234802 897234839
    0xd0f020f0613020a0909060b040507050c06040b09070b0301080102040f0510120f090206210601050c03040504091a0c040801060f03020f0409060f09080405040b0a12080703140309060403020c0a 84
    0x50002868480d403002500303402d15500111713102440d0921041c1800f4050704030440410303080c0d03020080d0740c5030b80340704541c14802c100102c0c11580c00503011500107456480070b41d070300402c0c0720b054a019075101c2501201c207510aa00c184c443d0703900410705004010381c01d66020014141281c021143c0c140113038025200c40c01c06a16080304903607074181e2802c11035050300010625680204a603176030301100071000ea000354020b10f5540000d9044c0303001034140e5000d81e040f07a201c00320b180e00540c00c003031810301044041c1c40f2407142150300c8400e02c0741c0040d841f500d001c801406914114042900c1d1410409402d0031038589510a903040d0780300300c07410005619440e1183d0119901503078081481c03146420000050a90548405a0f03986042c15403400d200070b6801400036903c0444040c000c5928807000c11a07640407900503445e801c50403408680029030904014074400d4821306000c003200c0f004200e044460f403c1102d41103e250018000c0008241d4140b0001d01112001c54004c07140a04041c0f607d8441c824655 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 897237302 1250 897236052 897236071
    0xe071e0902030702030d050c0c0601060807051602030f03070b070806010c0206070b102d0902090604060807030f090f1b140103020a05090904050102040f0f080c0103020d09060606020d0f020f06 84
    0x404128918130034400c40d24440c050401c02d004070b04001d80d40c4d04066120400c02580c5018110000c502035215808080c021742095079007a082c100000c4000c0c0541100c445c0880e45446445110707201420103002030300380c06010f6000d401c42481e04074405498030074018509410043c504900c080140c0c1ca060944207800e0b00085462001e44e10300e0500c4460307a04940012001ea41007016142c01c3c0504460b00c0c41b8a03101071524081e04950f6407004400f40c0c000d2003e8154014028002440f4031440369941540c08241490b000c9203220b9004a050110380d2541025981400ea8058010a1004074817413846079014103406144058034000c0340f5141c0710300440005041603000503402114501c28002e40b078070008010207841250410703190250007544140301c0c09852042d112030002d0450415980341080314640c070040c20007545602c0046009501c402d0185203580d507643e0303550700400c40ba84926401f6110940062464240310540549003108113543c80302150301c81c1040c1240310901040c2d450b04180c014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 897238552 1250 897237302 897237307
    0x3060f0e01170a0b04140109050708010204090e06010f0302010302030405031608030a05090f060109051503010614090618040201230c010b03060901090201021c0c050d0c03231602031f0e071e0902 85
    0x1111041c0c0234103060b4001520741c0c071412030b02140105040d0700510454a48020070841c51903440ba031700b030315240c00f441440000707040b01d241040594001c0d0015584948500c2c240c0349070002d20781c000c072501a0307018070030784004070080b080010495a5210361074000e091100100001288081e1050f5508030502034028060b8840f40421515042d0395402c4010301e01c01002401201d8541d001c109120400c419079520809484000c5041d500300300700c01101000105501412941c1c0c1c1d078006545542c404200001402c5082c42c211094181482c06080c0300f801c00ca002040b1604070004140c50080003419807541649002040300050f03070002001040c040300e410040b29a0008084d00782c0b0070001c6208084c100e40030301c0c0f0021754229800702041c40718510907141d0718100b0001201c034090019082060340c411050401c2a400000d4000a105071814070003400c40d5684100c0c420307030811952034100c0c1b9040c01d036141ca81c842607040c8180800c8024201c001128100900c203d40481f90f040498441c24580c1d1740d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 897239802 1250 897238552 897238583
    0x71701090c2310030b060a030212060a05060417031b0a02031002031e04020d020402030106171006090902160c0f0501030e1c050a1b0b07020607080606041503060f0e01170a0b04 77
    0x2500701710850b007001070180b034403403441c0840903000c0e45c400d500d0040340e40d0b508130000e0b02510f0004c403000107591000e4082410141800000c0345007075142421903482d448280300701c49640c2c621147da6040a803041001c1e0441c04400d20600d032a0001580500c46124010b00422403611003503030801c003000d08001480c0d00191078034000f18880102105c0040d40090001001150040e0011172031110403000e040114020354803041954512906d6000d0100040c030b15050030401014103402030191050b08004080c00724001d0740c1c45508000b85030380100d6071044800400c003c81c1da0103100b80b4500d8074982000c1c00b40c401040840206a800890941040c4400840e000e43e000d0311401251070700c940e8240c0d4004074400d1a00f803110611804590850061044000044450780301e01c003154014030000e41036509140c101004000842c80e54017004003096503419001036074541c0ca2203032b10000c000807038a0710490350500310140d401d10150f04408032940d100075890000070f07250320007899029030810803c0043d0440e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 897241052 1250 897239802 897239807
    0x50f04170105010305100b0d0b06060d0609060501090902211b0705010522052d070f1d16080c1b160f03050c0909071701090c2310 57
    0x245400400c0003600a0344030403980c400c154030060680340100304a5640700d4140081e40d0a0351000f19800d0307001007480d040003000419441c03c264000030010403990910007011403500840d9180c1d4004005a030301da010421240d41c022503640b014109002c01940780c0f00c0411245102d410312100d5180c0082800400611003150b400040404c007036140c070344241d50300340310305003140640800c6c3d0792400c4841007104401003444030612007001683d44900170b88101008010721050107035031412158850080d803101d082c41000140201750107480c0e546890100da03400c011103004480d2500802c400741c44c1500d018017113550b007503082c03901e42c0300c0f000e1900c550a90b460340c4545082d40240e818241500200311401c0894060203e1428080c0c101c41083c07440c250350f80e40042c18100120b100c0503201c1e410240c280d00c413a0034035480d0258040c0c10141299021903446c61584040901c100140d8000e07503607054020204460303074113070300e004014100001c00000107182400d5002003480e402144504c940b944503042107030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 897242302 1250 897241052 897241057
    0xb0a03060f0e09011a3f07030c0803040e0a0e07090204260d090501032a080f0901020415050d0b090112050609010e1203090f0703030507052b050f 64
    0x111050360390307695540d1072041c02d000a603000c1040e5401c0c00071310303c0880740d000e90101d141040188031140c0b501400b01c00480d0800742c907408001c21981012050035019044204030550040321b0020641c003891030604242c8200b80d50000b405d95002000100030440d10840c089070007008490300064003281c0382c984140740000c594401003183d4004140020683e94200d540401010281c0d400007410394150b20361516001001100700124041d44030501c003c0d403199100d04001682c6900350188650a040c2211054070715158000002d54640304200003c0320710313a04030b0342102c0c0003002581404d04001d02c01d44104030b41c052039003c103d0042008601112a07401ca03d00350a00600204040e584445900a0019001400351198032074407011035940407051055980c4900c0e018060440c000d000e03041c80c07286a02c0500544203d10800742c4c250044181800000011032082d03d072195105020b00d0454103210070084080c40e416121310141c510f070740d202410b0927005c80b40c2e40f41c010780d150748040740c038401e50 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 897243552 1250 897242302 897242309
    0x10e09070c020919050610051c09080d0c140c1c21051605130e28090201080708070c14011d0708190f020609060405031005070809070602070b0a0306 65
    0x8041c40051001404007150044c91041e241d0300b06000b0343d40c58505001d980c0c0e2641e0480c40005204100e82c242c1c00b010114107a0882c402d05001198200054032183d005401007140000321030361b42c2211541c1e164110002c81480f0070071543ca9400c005c40c41c1420394840011401601000c9611000403000d14494000b000340115184483e142c0176042d6580c070f4005180843d09500e140380d045c0c00d0b07001c0d114010000e8a42e80200c0000039100541400e10a4070918005405880014100e00004203640241101440190b01d584d00004890000d80001483d03040c02514010601030a88280207800f41d0102c080503a1581020b00401031038410f09103280144100400f20800044000342c0c1030a080340828100d0454502804035100344044441100d00c1521041000705410513250107240103050080240a545030000c0c4100d0505507504086070401100591001d0b00581c0c4a0800064a4010802c0b58000c0c40070402050b899003403641c081e5a83c2d8250244054a90000c0380790600c00b80700e030300700f04042d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 897244802 1250 897243552 897243559
    0x11806030b1f03060303090503151306020c06011d01050a05061b07050307380a0c1109070c06200904090c1d010303030e37060e150114010e09070c02 65
    0x640e0b007440000d005100e18001200000c480a00000345807a0000d1581e1002495440c0051540c4032000c80c00308440101070100c4041c1e4084c0144009140f06104650003400300a04175041411b910000f51b90001058010a01c2088801d00c00d00c0075403502ca007a00c035903030165465403001e1500400041e19200f096800580d01d40314620006ca45080c2c400f508800d45505240c4001058500070840854a040078000c0d4103040c00c28000c2d0b00b107041c8190300e00c1a1030785c02102c1d0000304910b56030104008843c100e0307800001c0392000c80381c041085458403c101203c0e2100f81e80c29801e19901c90141071781c3c402c0c8510248a140c840c0712040512101c1d0941000030709040b240c1d05c0c3c40c0c1c103c002c2c2c0c001050740d09110a402080c03401d400114520b201080030240d41405009511004c4d1011030818222080c4291800b1301408404d60807000807010310800700c0c0c02010000520b440c0110703403604010312005030081d00a007002012080c505036005131039203007804811181400307140e5691504032000202031202a60 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 897246052 1250 897244802 897244849
    0x30a0c090308042c01050f060706060b0a0e010f020d0807200a05010914010507050d020a211e090b010b09120a03030b01080603160306182f011806030b 66
    0x808000045000c1c0da506400741c006400f01c00342502c20a1301c141e09200e9250010704c600070310100d80c50008000c00b02144103020000f003164840890100c1500103140d4031000c50000c202810301503800100c54080d1010910041413031300c0314a00b0080880d00094581d006102c0038905421349054094410407071035860404480030401c0314100a4080e042204042c0c0b40c1148128044107200d00601580d4070800c1d841d25041d203004104002c0000035409400404104000d41c400c0e891001a20303044c030515405900c00104c1c000aa03d241c1021502e80d0119030401c19103490300d41c500048003c2e00c0b26044800914800d0f48440101c804201c0701c0c40176170a04000e034010740102c0400c05415601514001030700303aa038640c06035a4842455a03850049150310390044042c0420000a0f1146d00a601c6a0340c4a00e07484100c4c800ca0f6035415050440b45c00c030255800100d20b41c100c2e010103809100c4601e06000d191150720303061000b1040001d001240200760401d0384541d0051615207031502080ea01000e00c00c00302d0b1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 897247302 1250 897246052 897246059
    0x150c110a0c061b080306060f2812140115110d11060a0504030507121e020703120315030f0c0f0305010b0306070521060f0a060f0807020111030a0c09030804 68
    0x140c21240d03a0048601140800810503c421840749100359000ea2140c500383ca141c40c3e1100304400c03504503560700e0f00002c41c2003010b402c90200c20b804100b00700b00703030f01d5402d184000c203008040c2c031031120310b5001d00c610340c984175454050044202c02681180c02c0c0104801070340302c1c1c045007111004881c40035540544600d003291051950b0005a0b054103003080810340d51152594000312040d9001510b01500040062101102240703401d01c40c0c00708040242000c0b00040c00400070019a1b507038101c40d050242c0c21054042040c48202d41402000800754a400c002d4403079903a4116030f00000c40d00014010102c11081841000307000d48084000d09022003503650030903600d00d40b0754041d14802c00707568000d008280204205070302440685d03548410035054080500c110749040c3c088000000c0c19281d21134002001c40303080d501c0c0d02c10a64042c00c3c45a4800e07010500e8248081d0001601614070400c680c07400072076401118481081c0c070b8112124001c00308401ca40d001080300c40d0f8801d80c001800c00f100c0001c002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 897248552 1250 897247302 897247313
    0xb091204150f0504120311070807170709110f0c12180f10050904020c0705040c230f030c0d1b02010b031203060a0312120c0903021c150c110a 62
    0x1d01040d00035039825100002460007103483c0c0c01240b02d1038403071034030146154000900451060200c1d00786a01242e019941d04d5400500c0d003035169100391449007068004001140050120901618860005200040996400d80200e00c110072060803010303804146503a00301814000c2d0f07058410101c0c407203070b00c841e0b440308150241010225018890780e41d549141d43c240c2030a460720700380110300e0b485190404012400b444061360020868ac0070038090300c0c0300482e607562075100b4000c00c81c03190f0742e540782d94181c54076106442d11000096454210b801b40f05062100c50b02008403640210b80c816051381303030100040c441d00644a1400f1141c10006901e110448081c1d0560290708403070300443c1101c1800400c00e003640c50314402a2034051b0072106008082c4081600720a565200644a25100c840720130310a41040840b2400c000803c001020102c04005501d04824507081c030000b403100342e142c0e40b00c82d0b5070f070300d0b90342c1e04810701607182180c98082d0790385007600030aa0300c8004080e010640e0364441070303460709 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 897249802 1250 897248552 897248579
    0xf0819020610170d051c050103080d0606140d1a030a0b040c0609051309030512010b0306130c0806012f03041701020f0a05031504063c030b091204 64
    0x107044449030300c503000040c03c40010100c26aa4000e070409414030b00c0c3c4015049407690700421444240010250060002c3d0701c46104542c0250300424010b515540c40140b44419207840303030311450810506600410111080030104c1f44088910a40060002c0d04485012040744400c0700050380340c0646051107080c0075000050521561003810607545070317500c440b0151800d9065000303c94114818400c40e45130694241d0060584134003904266080189060000304044c03000d0b0468a08030342c010061194a040c62a580d41c9039001010007030041001a0000a10b200c1004000c40d04201e4040808840d41c0352103451060181c4030500c417801d069802c501c4440e502d900a11454010404a01030046011070601c00d1301c02e201c9510b20307101e240100740d1070308403041e03040030f8140041449901e0044440b03030f40c2e0307105071401807090460140c0040701c0301c0e25200360482000682c050001d87c0e0010451000c100c40201d46c1034035800401c1500780c0e114204100d14100c18031801c034689220001c0c003c90340c0e8542001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 897251052 1250 897249802 897249811
    0x6040b030a0c030c17180a030903050106060903020f040f060b03091b09131b05030706270f050d080913052e2105011b030b040213030f08190206 63
    0x60000034480407044044809408400c4c2c001098500d030030a007000320420298106004d8000146d800010b220030f0780c1408000c4408070049403070b824081041210038050a001000b0504241c038607c0d1464010603070030100c0c0a00188500d0351102400159031090313207d80c0140c01c1e611171468982c40d0142e0510b645114841d407038442005003808010b02403505a101a100d0320310291a0750044c00c40c1d964010320f04c0d010310a40c1240c1d450809020070152800c00c43c2e44010503140d0b544032611609000340700403030400f96000c0b0340b400b190300030284a070360900011070007240e1003a903000c01525001e04140001e4045c005089501254940e48050414a00e4120a0040718413040495455040010b030030994400d031001c071002a03400b100104900e00400300c0100002044400b0004980d0643d070781c881c211580310701d0142e413070108620303158483c0c0c2e4903202d00040c0a409035000c40c58452810000100d0f11201d11000306201e0303041c4c0c19442049400ca081d40c0c02c90740c0c1c913541400d20591040000e51142c00031103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 897252302 1250 897251052 897251071
    0x3070b0a06180204030203190f0b0a0501060305091902130f020c06060f030d080f190e0105090c010302040f0b0a0504050a0e19051311190602060414030a080c070c030206040b03 77
    0x400c442c081d500c1c00c0c400c407401c0700d03401401445d055403101018030010840300703000d482503010302c1001c101203099120348920400f500100094a981041c4000d0121a0054013280c0700d0751100b0701c56001190701c20181f02055404840342c800c05421601c1c1d1303401a110380d10001c15160700100da1b610111000061460161204403860020480a54141039552509949080002c1c20311004541e41c1181000c40310380140c44010900c044000c031070542c8003591001c3c900c40019070340d10f1003000030b550814001000072410929081d071806141000e10380d140340950240b040c1c66040027070581c00391801201103c00501001d481d2903800346d6106905544030904640740f400046a0a40c0e034200c3d800d0b0f5108280c03041040315620b040c1c0410300e40761002c50b80c10f85007600c1e41081c240310300329581041c41084d00700106400d07801414030f803030a45070042c1c4480b00349a0030342035036005010f036a0100340c0000b0b00c80e902c4400f150400f0f44404d800c2c20710840e032824a0344065000365001a020480d10042c0008601c1a006407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 897253552 1250 897252302 897252329
    0x614030708010b090c090418051011090a18021e0c010b0906100c030e0307080c15030411150702090a090201110c100f02010f0c0807090608090604020d030203070b0a06 73
    0x2000c4071401c0c0da028514580c0d01c100640001070400c21110013800ca841c50241c00080c1e4118824001c09a04044040c00e0703a280c0c1c0083d4000d440790b20203000b20305ea40e20b481c1110504100740d68002c104e618004c0c0c000d500c00c0c4000c00301c1015a00d04968152203520403100c0c400d480a0745000800c10145c0d000742c0b2221085c2d400e007918003180d818a444014080c0e54064101c0d661170720314610803582d003645808204c2c00c115a007011103150303a508000410283c20000b02801c8020003070401c00018940c500008004000140208008669524068015540e01b9644c135080820401c004003501c0c850719000030351191960f0240124082c82d0703030281c40c0591003030704d401c0f100c100030081065485e440f2121140e8488004512903200030711502360445103c6250001061440f200501041901d010100340710008880600b00002c0c2030f8003c1c2110010710180c20100c02604189148680391a80100b000c2c0c000d00a0300d600c801018420030072244000e800c072200032903900b00500304401510b0349114146d01258030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 897254802 1250 897253552 897253559
    0xf07090b0a091202041808190c15050408130e10061125030503040b07030806060c07060f091509180e0304032003030a0215131a04060f06140307 63
    0x20081101d20701d100e142c50b001d91041c60446080410044042c040303805c0b80d143d500102d440300e02070140341c6500d0312441180703490b240280c0b0060b0580c4502246c0b1010003000200c1a004101841d00342800300c03600e00004513071981c46003800b020b83e1103007400c0304a228220780400516403c1526000f40030f49020201d504150344c1e0303003030100c030144409002c0980710303000460302c10341005003000090030000c460320b04103620701c0c0c0d00c1c0c40300c50840e0001c1d482103030001c1000038028201039000e000240d200c88102c61440c1408814010990b41d021a401110103102105401007980707030181c1c0e2880c00402e41c40d0b00d034504d0410402c40c0200b00300340600c0380700b03500f0004a410103c0303034545000c2c04030340c40e040e6001582840d2554580e00b2070142d40b884240005d030380303c25a400b03585e00c007400140b0590285800400071505c0d250b240d0750409000070100a402d00740c40320700200243ca1103071640708040409810800c44e4403942015802010f4110000110302d1a002c3c000600305e0041d02c8205d03200c41c1c12030644103110768 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 897256052 1250 897254802 897254819
    0x2030f070f0e0106390b0f0f0c0f03061302030103030c1401021c0b1206010f060809010c140307020c04150815161b060203041103160506090d020111060f0709 69
    0x801c4c010b90000c500802c0c0140d00c00b078102003080d805410500d0458008815101540112030003030072060366104040d8041011589030752580c4c603000303017416010308842e01d8113803002d408a000300c0d103503406290710001c0800d2043d130319040f500d000c10890780c108643d01e50f034a180180100c88059012070b551180402c4242c1e5802e010305c2591901d41100d500341c03d19440400c075a50040c04881500b543c02400f1101040d9000e0341003000c24040d01d04400382024403810404082c081c000c00801c441100da04045a001e0703061392108164100c0d1340f0400315103850303481c0c0392026070524404040707040e005450160070101100000300c0010454001d00242c4031070040503040300390b2100b0100c5244e480c62582c107014085d003034030401d5072064000c031440300040c800410340c0d140010f9038000c0c0c3d42070300c0b80c950300c2e0081e0429140a021008400c40c16901105002d480d102c0820028050f2204c018490408030740c00d2002c7d640a07011070290016000152416071034220f5800030000f00a5910b04000703146080041080714 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 897257302 1250 897256052 897256079
    0x509010e0c0114160501140a1107080a05070f060b01110c10201906060522230405060403030b09010305070e0414060a06180b0d060207050a02030f070f 66
    0x200d48502914a40d00800c0055504050b802111082803e0400c07a50706245165200180c102d44500d0000c503983d8920500c413a20004050b00c031504483c82e00351400000022041203401c220341c00000c081d102c0080d441e00f5542c0703000c1c15001500c580c045a0343c200070000c50b0380c13000405030b40903222010460700c4a80466502c8601c0408981c0100c0320401c001c50440c0503c59120043c80072010306aa608804070960b420070728188030740c001015440d41100d0801260340500d00280c80f05444c001c40b203240c0c058900f44081420038210301710ba603941c0300c210601e070450750719501244c2c0710040c2c580300e605003440c0c1140c1d6850b044409600103441c0c450322035a545000c410340c604890f0000010010942024108548040301038812260107070308003056003401c40c00340091841000304520005216140451035401c81c40e00c1d018101c102c516240041180c0c2d5592101c0c01c0c000c50f0419001620b840300b51900901d008a007410213035041c407510032346110000c000200502540c0e80360200c96000da1fa0796102c4c10021 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 897258552 1250 897257302 897257321
    0x10050306010b0c42040506060907270504060905160518330c0d0302071a040803010906140d080a0c0b01060309030306140607350d050901 60
    0x40d040000100601150040039100002920090b1205114480e03450b005038030808560006580015a0006503440ba406031340c01d1030f10a9800882c060324056a070f003900c45400030101441503a4a034049a43c6510541c001801c400d151903018414554281790316105000c24030500384201d0801c0004104a581c9008031400b50a0b0050706000e0f00c1c1074280140c2d0a81c02c503c2c2a031078a0601881004610341c0c4442c10721943d80c0c200048020095981030034025080f13078104044d000f2010402a100300884c0001d000c2c1c40c1c10100303280058a0300541d182440d507810514445420214030700c4c0520040c006200000c504a4541c8103080280c156240e541e201c144d060741607516401820318440034007146480d070041080d0744552030f164205140d41d64540c81010740a8120000080d03a50b8407034003c058240c4110000303004004032102504014000098091181074801080d5488081040a030141c10340e00600745185451506030880c1130205801d1f55540003210a81e140340c1c24100816030300103041c030401006 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 897259802 1250 897258552 897258559
    0x5240907140c100605041a06070f06110d05060d2109030b0a0b120a020102070303050702040f0507030213050d020310110f0706020a0f0e0a0e06030a080f090f01080702030d0b0a0b130602061005 84
    0x400487c1302000102d400c000019a01026445403030030021305540701d051440040c10144d05e0320380c19070020100461760b005004500494071139001401007000c10142e1030034108003105448244082c0b24003114507681a600c02401240036a00340096145103070040030700c034401170f640040300c079442c13905840d6190401000030380586c101100900110307114030000e0512600180c0045080344210b0502012540100e4415001944c04554906081c0c04400d402c0c0041c90b04aa811241d1082e680000b03841d0035240413040a151b958a031401701c01c15440094a00b01a260401c1e00c0c0c83d490389080075400303580840c1c25140015804000b065070540116861124654080c1004c001903050030f859034128140038000307603418861408100c001030000401060010328041d00241c80341d079100207110385c0400384c00586050007420001c004244c0c4d8000150f80107802204404940c50f1096008959070894503000f2880201001a0000c6040c0d9034000c600c0440e021070742190219179951031038042c004414028141d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 897261052 1250 897259802 897259841
    0xb1206280513141609091a0405070f171f14040507080106090507020307111207061718030307080703181209080c0a030f06060b0310030605240907140c10060504 70
    0x2085c16072040840710b101c2d000588160b10208034801400e83d084500b20b81d6940040d40038403505141740024001010400c1702c8001c1a042c24032032689441c003d10302e15041e4000070b0841480a8010780001e401d0945440401002d828542085600c41c501e41c005c3c0f0b500c5601380b4000180c403809a2080ba84a0400c0e60b01035818081265200040e4104140100380d0000000003820b51400d414460000140295101d4400e1144112078104030540001c0800780280d4100f007500c040c88c40302200300d9511201c1803401042c580c5e606001a80140030b121036041310200d025140e06e04120403401501d00b0811035848607000d1650380c030002a80d50303170640310340c640200303241c2002c00c001050340318101c0500d4401d201c045421744d01c4111420464008880c90310740c15850440c10010300015200341034026000104800030701d55458521505941d645602e00d009880140020303020621440350b0301441001c03541c1c0ea5a84083d003403d0180e80c2c460303012201c605c861070700c00f00242a15003441200c0e04100d0084681d403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 897262302 1250 897261052 897261059
    0x10c020d030309050105070f030608070501140c0a05010501171006051c080d020d0c1103030f280510080d02030903060718030c0b0703030b12062805131416 68
    0x210030400c00c0411824540c64410843c0010000c2c02040d1040345290348004449658000050a451856210080581041c0024071640c5d91140b60410a00102641310b5600c12030600340501d017420b60480a8134551800d0000325012104403510300e07040008a0460f03c041403541807600c1100c4161203460b078014030401d900c581c03443d5000030b00e481090003501d4090034031200105140980e802003010421190b5110000c03904950004101c41c0d283c00000b00031800c40c41c2252120080080242030111000b220070122003500e40605a030502040c0b44100c107200c02e041c40c001008981d520744c06900c02d02e0240c40001580c161000086c1c42c581c4c08010000d050a8440e03400c00c0d210741654126490140d44001c00200114078002d41140c020410724203d540e5810203428010101d4500054080c0720f8134800c000600045000034445800408906488441d40d020329001140c001c114001ba0720024106020011100859111190014041c02c0c5095101c0d046100d0540c403410f0403684075003880d5a000050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 897263552 1250 897262302 897262309
    0x1020735030313060c02150f01030501140106080a0908041508090d050a0203090d0515070f030b091e090c1c0c0501030c020604111305010e07180630020705030c010c0e010c02 76
    0x941c4002d4016503416003480c00c00095104012500070088c400b0300401001084401d12401045c000c03003060300102c5505209005010243c0034111803c0f0303e07122116401400804012200100186104d035409e01030345080c0500714810803591034030240165800346070014001c604507003580050f42d01862920754010b080141c0010070400a81d03c9100300f0700001402030204114601500c03042c3c84807440e4082400008042d180041c00803030003583c0040a200c003c50102210502110040d0714030b0150ba52103000d040e240c0000c14040035030081001000310004152480300c00d50345030160794001801e82d1541d0040d02542c4003540c49400681c046400100403a1842d200020a942c0c010400160608072100c0d82040d244280c00c80c00c00007031018244450a0f802101e00f0005c0002c1012596440707160110207050540803024804003a03a92a000d900700d0405601c0c08146020415411510b030001400d0103070ba00d4005c0b81484842d5860143c0045007140a8044440c5d240c00c160350f148091b80710355090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 897264802 1250 897263552 897263561
    0x120031c0c121a1c0209240a0e0f0702010f020d0207030909150308160803070906030c090e1605091e030d11061819060c0e01030501150507020102073503031306 70
    0x70b84070461030002c1540e005031b483c1d103100742c00b400c0d0140d0207961000803800140040c41c40680000d1150907000010052130504a040c00d80c0300c0f1407000e21400b2aa01c95100764094081c104200025070304c005000c0101320417682c040d007245030195517240f110b40c2e00c41d00810100c0c0d8101c858400c01890b400010000141300100501101c205005403070f1b40c01e01c60303540300c0025801c29280e2001084000c842404802c0c0e05218407200303108145401e043c0d180c50812070305031780340b009010300d041d5001ca03031150500c481c025021030b001c40d54090030104024000301107012021111002a51090280030703401e580700b900c04ca04000c0381d0284080501842d4541800d84401a403081d550083d00b4000c03c05080d0242450f104c0020348e05004407004100003501020042c41504800c43ca10305051400e07005102d9a03010403146d498410441c20b103681c4e11299400141d1400b1042d0f801010808246090103140c0003022051b020000301100501801404a11280c0d850340803c58000100148026000000c26442d811 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 897266052 1250 897264802 897264829
    0x150c0304060b0a08061e0c1e1b03070804240e06090a0306050f060a0b0705071a0c030f04050f0a03120309060605030a030e0f0a03020120031c0c121a 65
    0x10608146035076004031030501d41e044070392480040081c50350184124142ca905c542c0410401400c5107420311001c60801e14225890101c9000d03a230204074060500055402442c01d40d45080441342c403001c0600e404281540140920042405d65541072100811f204031035006420007030f112500110040001d002442e00003501050340000c080c1c1000010070414454a4014500308150700d2003898017000707010b5003038402e40c000c1c100100c0070844c850201c1d501007004415243c4031a480d84980c404c11040b00328502907941c44a40302e00001655103400000c84000340100d88080e150a4100c00610b41008050700d0b141c84058102c0e80016895140d0620a07406105843d10504001841e1070700c03003000c6450700381107402c100d011454800001000b450b0806165000344822525a040c00303065a000a0170030741150008030340680e81da6002840c114040c400d0b102c80e640801824000c1c0340107109480003401c820030460011900c4440b048903000414016016a00c0d107488806013584103420502c0419803a038803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 897267302 1250 897266052 897266059
    0x4050312040602090a080a0b0105100c02060f0c06130c0e0f190608030c03070203060121020d0f06090b0601080a05040519050106030c06050915040302010e2b14150c0304060b 76
    0x808000c132070382e4610054016140307090050045038040e02e0300380408641070704400e10640034401c0e150138042d0701c400d68002c0300390305580c4a501c900320200c5c2d06032180607a0002d02d42c180114000c0001d61911181e1881d80c1a001c0c1034040d5003150b4600c82c480320340d8010b0707a04448002041000881d82c0c2c04400c0d020100140e01400042c0300c5565100c01c506542107010070100f0340d00000740440961804100d403030b02406441e0303000035254048185c540d25625151070003c0c02165002c200c5410302c4842c032010100180c011406121141c101e1501c05210721040300d144d800f044444002c100f025145115480c030071540600200039004d900036601162181c400002c6415649a9001100148441d03141100822042d200c840d100c1d121a800c10540300c42d495202107031030105100c01c01c0581e91065035030300001c00540301543c40358848204000c5007080801e18541100c3c06050050400c4884034034028000d00704000e032060780c940311110407000c6a0603181103403810814000f00c0c0100c0c0d6290300030801c680c07008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 897268552 1250 897267302 897267307
    0x2070503160f0c0308041d102d0b1b0316030806032d190807030f140a11160f0312030e0d08090709090323130e0a0b0904050312040602 59
    0xa50f107880b03030382e00b82c1c0e001103403a03401c0803408201034560101c2203450301c4600608100c031460701c1924003144504501c10078070090031000c201c1d07401842d0070089618507030241e1502c0f07091030703160548100c1560210004482e402c00388010800401c1020081d10102240710640024413070f86510111001540a02041c0d41401904e180c8445481c15100c0000603262083c000da09503800c0c0820740f42000c48104882d1440c2c8100d02c01c0d600040c08450803138900e41e42c9420802446503604104540d40181e8248401035403100041c050161500714511002d5540ca550440e80c140d551019881c00d03a40c510310402c1011000c1d40303401d2000074481c05914110f000945000203444040202c80d82c41d1940f5015200049102c0e80280040103e0900805001d0518100180400c4406070303802044014078854040c102e940325040c2500042c05001290403038600640b903a0507558541c403994542d00802d40741e400c0b00324034281c2001800d041880c25944510f4010f000365080c0040d00403104443c5400500840c0e035281d08 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 897269802 1250 897268552 897268583
    0x120031024080c040605180109210b070e130507140c060a0f1503020103090204020708030f0702060a0603080a0c061b0e0108130209010e0c13030b06103e011d100207050316 75
    0x108203a44088460241ca1094101761030409204919002e84000f00304090b12110100714ec4a92a01241140e84034500040302d41c5d031907808175180300038405d05140d0000e0010b041e405402000a103a0b004d20f07526202080030b0301648001004417141a011154400380f004400c10166000c0e5110107002c90015001616103280c42d5a50100c07640100c0d0303210b0a058100c010304c824140d04002e01c80d030000701040304100303040c2542c441030341034014109240100a000c0d2505003c221aa402a0072401011101203184104080010b0414062090600e00045020002030102c4103542c1e02c2d5910b89030080d00d1030040340d09008225000c1103004210941c840b4040003081803840c2280c244000450144103540d1f614145070081200449800800400704070400003c8004080c41e40403a01d0410103806030f018000301450701502040c1485148441a17528141d181c1e51002000e1107010807403207044c0c00755071f003128440b483e0f00103c0c0954840500564070522401c1d0088241c5018103068a0040340142e20341c050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 897271052 1250 897269802 897269819
    0x151a040914070b031003061d0a0b07031a09040305160b0903090906421c0b0102060f010b0306060c0604060911030120031024080c040605180109 63
    0x1405004039400c410110600d4110441809444090041180f07101d01d1410005008510800039010103400b89a072848440d940c1c24040c58240028185002622180811400c040644001c00c0350b000010030b06020b0348110000c0f0000805a0b11040100b82d02c00da501c8a0b1001c03111a04504841d010641c1741e00c003a4004070b025055500c0c03054401100841d44e03245010140030f40c0d0180038241c01e0050290464104648914119041c1e110a4650340d540070483e81c0300000300c15490509640c540c1c41000110010003004982c01c00c20601b428540c14402c1d071000a00485e56110100d40c3c5c502188524001070010b40d8030800155081200140403d091000800780d050800a003981c0c00c0340c0d43c1d580c2d80d418804201c4c40208a254a40341100208030812075801c0740452200d4840c0c5100c8040e20010002c1c843c3d94039206500050701c90108040c28240703002c423585213a06403100501c00800c142c48c0c00a40001602d600b108c090310340300d907a980e041001041d100000003e1b0b4004650501c0032011000c02d0051 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 897272302 1250 897271052 897271061
    0x30905100c1505090a020a0305031c06140f270412081918020a08010914030f040e060a030605040f0c080138060a0903060b0307240c0c030b22151a04 65
    0x50140b130265580790354bd070445004501030311075031000c000d003860f00030031040e060f104081d01d5810098481d01204156800003880c008100030b09200b08107081090b124484500300c0c5002c1c4030780d01c120040c11011080c00d01c10344810310101c0d200268142410200802c404550300b01702c0cc040c011882506c101d203407590004440100540180c4c009a5442a052003401000403400c400701500c1c2d0055803405039030cd001e01c0f111f44038a00403903942c440440702242107600c441355001c0045404c0070f030802c01d60615140c0b03100007180008003500c0c190000003011550f0f080601c101d40140101e031014000350b00a0317100311038142c03c50065003500c5180b030021900c1035842d040018088240c135550313800322803411841c118044480d6891a03d000303610080d4180107107400c45a14540229109044010804215108550034016000c1c02028950700640000400001c400d00b0ba00035003218082038a98201444449a003807044100500303600d001071007040b408282035200c0e0a44400b81c5032403200c0c9c1c60085c0f01107801d86 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 897273552 1250 897272302 897272309
    0x3032a0a030507020118020105030622020f04052e0f0309141f05010b0d090c150203090a12020306010e18030c0a0201022118041404030905100c1505090a020a 69
    0x29480344100f00e191582841030010703010304500703030004c940a25000242580001001c40340038084a01e41540c032200c0c003d580d10184c0725808000c1d1b5031024100d455100ca03800921a2500484c0d40c2c2e1107059030b031010058880361118210000010444203403004456141811081c04140b41c4e41e400c060021440720700c440e500d854114002081c40035400da00111644965401d07401c015480d210050041000e14011582030030f074241c8000c51081080c1c1400a200c611a62246008007402850038606680210152214a1048130501980c90740e91880e55015001440d009506801680060149041c0030040c41d40049028201201000400703001074603580c840d10f4507864592180c01d24404641e8100a42c030300c071403140c100304a410880c14040c041e050040d4101500d545210504544480e2200d5000b01c040441003112035030581003508000d85100c4e8a8001d0900403421014044e000c54010710700c95210720750020450300c00f03d01620a000042101510011440c000c1800040c09a41c0b1030401c40d001e07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 897274802 1250 897273552 897273557
    0x5030307091404020a050d0f02160b0130021e1011060c0415050a020c0405150a05220207050c0a080f0705040c201e070303030f020c03032a0a 62
    0x102820900429080c5402d40b00716481207004201c0684241d90000c140c404600c060007011402c44100300450001e030049852004104035405515001e00202503000d604a0303450481100c00c4000e031021050b251000814101e0f24825041c02040050a00f0b521954000344ca81c003185404141100c00100041d407028102c0f80010911440304071166814002c154118554404480c40d080c0303030a0b60380c11307086040c0d140c11050000215417030360302c14020b2244504c0d0b020000c0041000380f4050502440080305024014003500740d20794040b5603824081d580300320001c0500c04809480061b5a401c4001c1e52007450115818000c0b403840c2e080340d4603030201990190070342801401d0142c880b4030950b80341c030009a00c01c0e8415810103001d0101603400135104803000245000c0c428661a80d171201a280205200e05079106202026202001101c04100349068a10075a0309210406051140c40700f64042c02e04000459001000803c011441c00410760114007800072039601104045c0f540481150010f5002501 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 897276052 1250 897274802 897274817
    0x2091f0602031810080606070f0c120302010c030e21041211330c0313180c0306051323090d0f1e0e0105160f12081b090d05030307 57
    0x30443c0e6260000e00d18030001da40880c09040e1908000b0100c0c000074205a0242e01e000820809102c00240c3c01b1283c5a00407085101c40e941c2c17207101e000b54800e5244268015403802625410441c4240140707483d2640140007855607003c200d5000c48440700503082c107902c1407403c010016080c2e60104401d10f882d8050102011822051420710070b68040851035522544559182d1111090301c1c00c50148841604664103034544490314606131451041103440d1446101c0380c2c0e0001040d09460481103511070201606001a0390003420a0742650100d008050340150440805100301210303170301109540b41080209108030001c80e1941451910a60790500b198100d0051001c00035006000e003120084207181080c800d281d11440c040241c800481c618007044504030741c00d002d5a1003441500d03000d0b4160100c0c0d403034804040c03074854180081c4071802c640030040c0c40d0030800000d00892039644241219060422002120044040554806c404466110399816580c85c0421000c00145102d44402d458415 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 897277302 1250 897276052 897276067
    0x15050106031112070c0f02040e0a03020d050a050f0a140a08090d0f1709011104080a11060306100311070807110117070f18030b09060703060504021602091f060203 71
    0xc003920b030030714061140c00b00100b203503c03070310f000c0c1d490382075441301003490401300800440c54002100800b01c0c4000c1d50003400c01c000f046024101182c2000719501c41d030222041002007841c00d40d0240141e650610114500340040c00003101e01100a01c007d140c140b40403458410f6400c007200113900243c0d40600014142d10401001350410001e81e0081003007070034145007102503404005d0040290742d02e0742e41c039140c3c144c3c0494003180094010108841c5042100d81d102c0c2d0b1035100207507613011400e105030740200b071002c04001c480c2002d404807401504090305004000c18105410b0700036160509042c41e05e4002001941c0102d4016800380c6411480b51071081d201e00322880c001000700d40b48081340e20105040da02070201c40350300403287c15070804103418004225020381410b150540200c0d8400383c9501c072503a04000300000003048041c8070b500035450410800c0e4880046c0003c03401600404001c407104426490058030305031400d50f91000c488607032019a800c0380c0809680d24401c3d544854096803002c103602 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 897278552 1250 897277302 897277307
    0x5060c1c02030417061003060209030705061c0b0907021203090c04020406090e0f01180e19050325020102070b0d0b0a09020901090905190203041716021807120c0c15050106 75
    0x40c4c0036449448001c00f110304100d5000d52043c8a03900c00104966030002d0010880d481c14801d01009100c010b101c90f896244100754001c1003115069043c21292800d80229402e21f4070050081c02422503900030700d21404803004800c80e55001600e146902d00c03d00804420070f599500050010b020a942c0c0c050074940741c00b1440b210f014028080810454000d0010710811004501210f94104016000314141415000907410700c0c0c901046560b50326072285107401407000000091040c26441c2c80d80b84c907400c804000b602005000e500d002401608076240811405441c0c0001d890700c000f101800003050486800001c4000c05c050b4415a84243c0200d0b00403580e680041c2d00c90010208210180168a05840400c04590315100720080d219404000b08090202d5003180c7c072850491400c0d42561600300c58107613600d05944d5402207204400700c0962407826020551028000c003405d03295a1010f0740045199000390406100342420808005c2c0e030b02c400709806041c802001d1a90040c0020740d5414001c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 897279802 1250 897278552 897278579
    0x121113091209331101050a05061206090c01031d0f0601031101050711040222030b0a05010611060433020301080106050109051815040f050603010c081005060c1c020304 73
    0x2108981221031a40111619a407181040d200510807102c0d85205030300b005507106041415549003c0d0b10301b00400c440b4010503070002d80031780c1c421a030751545048200c4420b030740c80d4022665031034035800680440e82d5650081d0018a800e030030f0340030f40a080e01c00082c203540c0741100c002004c0103550302080042081c4101e100c060300d500c8000b860120b1501c0c195031141c82c55006082c500c0c60180b0740c001030440b188107440103c907618841c0c0300700142e41269607081c9040c0b545000da0b0903641c02031604000040c0350b40603036680161741c640580a400240c1e929200c0000c0b10b00e590140303941818580c00040c01035040c000e14007110070040c4600603182d5040c50000b0342102c201d90040ca040c0442c8190174015541c3c3c0c101107617142e03107003001c64611603501c4000300700184007d080b40329046400c00c03800a0010f00d00c0d40040380303d85401d50081001880348201107400440980d200700c00700040090034801814004010b0080080e40e034100e0f520041c1c44441c5442030b946120321100140c1001c00e041c05240f400040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 897281052 1250 897279802 897279809
    0x615050307141e0a030807030e01030621150f0e01110f2b15050f04050103170f072907030207110f030c0a0b030a0f06121113091209 58
    0x501480c0d04020344259007180b02c8488911800306900a144214159181000d00c15000740c6641d1006a1302d10700341c01c0d144c120302d8044005c5100c2110715400343d4420f1042204680c100c01201940103040241d40140324007081b02912041c0c8031401e09440e6078423500482e060901320b901d0000e60307000d40c2000759084502d80c0c134204140840401c0444940c018100507604194425503c045501c503070300a0156040ca400d20a448885017000c0c6000b112402c03103074201d4116003023a56030b94072408082c2d0030801118003d010050801074201c1c3e0340955025640080e0000720314158510340307011640d0321003510032034100746c00d525901412448c0d210300301d202e031303032515002142818154249006540c50b80c0108224640c050b00401c0f1300c500c428a90743c0d0800000c101d4a1028000700703161034032055a03c1940d80101c5450b065503042c1520102d805500c0e10407141200e0303e20081d910300010595070060078110802200c1d0b40150004c403c940e80342d0251150f80f131407034405e40c68410140c1241da4040d203003150550 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 897282302 1250 897281052 897281059
    0x30f030403020907030b0d050601150905100f0806010207030807060902010e030d092702070c060908190b0a060e0106030203090d09050f090603120c010b1e060a03020f16061505 77
    0x20401c01600c60070040d6400c04030700e04001c03a110038041d0200d11502d120795006846031041600004843d80620241090708a455a810000544480c14001007814010110300050680811012810321940f103203030b0414014410b40b030060341d60752201aa41d401090382511250b039103815600444d03810044a51441800380d028251005100201902e2001d440c4100004074207201e19100003425004a03412400c0320700300b000c41d225280f50a111814540601403100401c03804074000c0343c0141e0010b44139000700304101212007101c1480e90740031420314001c0d100292850710f9003000b0402c196000c82c082d018041940d001601c1c0e01e0203185142c6400000c1d0a00d1083c45807060003488192900c5011941180041d11495807607228040403c2c54511075190524401001003801c0b01d40300703410f4000d04611203003110180203030443c104082c14100c490350681903001c00c041003441d5695020b50089d005901d82d03465030506012815050354040000120126151a40c510380815505120050381c4007810080c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 897283552 1250 897282302 897282307
    0x1403070909210912060f1a0310110903010c08090106050a030206040b031504180203160e13050a02090a0f140f1305030c120a140a0903060c030209100806030f03 70
    0x41c0c9071500d0400c118581000300341c02d82e600c60451940114416401028224801202a10303242448401418011b21020046e802c00700c5108030101e4803500011358020041c0031706440100d201c5150020311030810721a8000c03000740315a120700d990a02c5246152595501c81910502e08007248608440403074110783d12a80c9407520500140e2200800c0c0c5055440f017503041c0717030307a40c50300341400315a1088145035950260900c80c2400c1c40e0744480d80044c1ca8070344280d003200c0340c100280f044628414244c1c018400c03d01c20402c0000d0060608240c00b40d143c80c0148140c5102405507004280060411140c1e041e0003a110a41688944d48a00c9030b01c00101000852840c982411816200001e9000e8076180403800c0b04c070300e6101840014403c84403070303095004c11580b400540380b9203c04542c00a03a4114042071030b500e1081d10711115841280d003100701640d0ba4440c0e007419030f99640b0007004404101c004240d400d11494042d0344880561200000b4181c85c2c8164914001082501c0d00e07160f85080107503038105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 897284802 1250 897283552 897283571
    0x81308040302010518130b0a0803160b040813060305150301090f0b0a02040b030109050601020c0d050705011b1b0503100b060d05040807021003090b070906020a15020405060414030709 80
    0x1800165000e0740c0d824a4820f0f41c440b03014240060030300d00100c50742d5100c4000d10b41d50812494030392042c0e0510009480d9099400d82e03855031940ca9001c0c0b240742444140401c1c0c0c42c00c0010b030394601c6440d030140c810001075003041003109101c051030803183c010801007540c03074050048e00c135a07207681c901054408038000d0201c40740ea551005401c0c0748001c402000124100d01244080c030068065030058100703502295200c0d03075201640740107800240c1c2d0f01805030040000250003414040e411412041e0400001c00340c0078606001101c01d00d100342d01c0d580b003201c0740092460014501d1510320381080440e900e00030006080904140c1440c68250324104c4040c0b130200e06802c3c3da1501c80603501d44c0e01c3c50043c00505a903450408064074032450070003c0d032000d200c01c06041c44a405070301050480b0f010343c0070402c19a94505081c0d54143c0f41d17010701d102580c40640030310005260341c00043c039000030105015080c503550b140030a829800c1030300156807041032660410001d04041040400400c1103500c01c4c000c4928 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 897286052 1250 897284802 897284813
    0xe070e180c0d052e090b1906030b0c07020112050106020f0601080d0f030b061210030b0115090e04021815090c0a090611011b0c050d02060402090a02070501180804060813 74
    0x8103002c0801c0302e954021040c0300e50f030040700c030303100500b84c400b5a00b48420fa0003454103480c0468119129983c020b404903140c200c0e01024880c58050b40d502021203001c82e01e8581d50942e9079002440228100406004010712003842405043e000700099001041541000c2c84074504084058010025540c410200240071030740c40f9000b14100380184c00c1c0001c0ca031074a42c002c0703201c500c1500020b40e02c01d8881002c0c4401e0102554540081ba0f0080f00c1c800000c4c1d072035070390030323100041c0c000005c000042c3c0c100340c04e20030303038100c4091030703801c28402030881e50301c006081d0b40080042c02c12201e41c41c2074814020031030200d041a13092683d00c901140d401900e00003040d1005402c00b40c01d800f400d010440403040000c0c41003000d50003c9642450303d8104508254110300c01003100f1030302c10003107074a03010f60b070310255803030303000040710b5014550052492407665929040f1000941050000703482c0341d074031000d40da000e40700c2075400800050b000d24840c0b6551824114094882d238009401701401e400c190300351101095 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 897287302 1250 897286052 897286063
    0x40c050405040c1407120f230d0b030d030b0111071d100810020301091d0718020d05011d0919262107031406040e070e180c0d05 56
    0x24001c890014008403c0e100441d11280080580c4440b214006038000500040c5285da9401000e941c2d90251520a110800c07034201240b00c0008148400d0810414210035280010300400d600708000000c5c9203400100080ca0900e0644801010a580794078044195900881510b031680b4448010440b80b45000340500c0c4061798224000500c0104101141c1b88408007880c6000402c1010b01f102c001c03400e03090744900258428860348464910b400d851105840c5913100426007201d400e00034100d030780e00e40140020302005c2c01c40380c0e403a41c0da42000a500204814415603000e03140495030030210705a1150440c3d44014041c044040700d50000d50680c00f0103106030600d00c441d0b07a000c1d00310600c070011429101580c16200701580307411500801c0c2d060003103501d13a094a40c03500c04c2150206964881c400e0540c202d440d445842607442c541c0c400080e1075810036410040000c2d942c1c030700319561030340d8961a07480143c1c4240c1d080c591344080035402d03a180050030030003c207040c001110481c6042e4441e6403040ea513070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 897288552 1250 897287302 897287309
    0x10605061204021017040b07090f03030516110a03032001060e041b050a060806040c0e060d180c031406011d060108060d14010e06100602120d06180504060506040c0504 73
    0x1805110803070b0f01181d02c1409503490350003190086100071b0501d4500240108801c907610301c00030b89030301d200288450500105904aa40540302d0b18034210310100080507403c00004180d41482d0355a00400440d241c2c0010100110f009a40e40e40d0b03941510805041030a28105a9180720380c1042428000201d40143c2c0c03903003040e0700a18440b0f40000c070001081d19030880c2d9120700d0740030303030000d10011f203444c0c004e00c10300d1140204460801179005c0090003030f5032040c80c924040360000004e0009608100880c1d10901b0091010030705060888115a50001c10048a030412900c0c440031207060503034040204241409080001c2da26402c10708403c11a0f00d0350040202524100001200881c0c010740744e01207441e81d0150011040b003840104007070b125010700013260301100c5c20302c140400514000c0104c1505420307100641c1c050702a0081040c030b400e1a6402018900619a83d608800121005820500440404500c501041030326003030400800316100141040d0249041c4185a0301080e13001c82100c098 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 897289802 1250 897288552 897288559
    0x16081605040b130b0a0c112e03020f1911030403050a02040504020d02030a05010b030c1f030e19051605010f0905060a050706140925031725030201060506120402 70
    0x29115001441c1c120803400d80c4c0300001d4030100256014200341d2094942000704c1c020582114518904001d010f550706030341402081072140ca90031170100c0c0c1002e0b143c1045015007440c0241c20100c02192400550303200c1d42905103401001d144800c0529000001040c083e0070b45009103050a01e140c0302d0540710701d004540217200e560303070380c0c0090119547c00d02e406410b190045e0840c1ea510880d8500b50b4028500103400f240301e8800c00725000190b150a44c1c0140002c450503482c0365030881c5071034041d4040c0c02090451603041c003030381c80344c2500b21825403410b000d5540944001e01411286234031485445280e078000c0b504002030140301c500713a140c00c00b0640080328002c3e90001d075100071002048076540286d410007032400f418114400c041b042900202405036180c1ca060f104c6424501d10340c0c804080040300300b2500200030305010008101042e02165030075600b05042851302e00a908581d040e0102d2100100c035040d40e810f140d60a2680c24801d0b00041c102c00e40d80d00d03160060100c2c84508500004000038031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 897291052 1250 897289802 897289807
    0xf030306060901050c0a0302010f0f0b0102030f282f0606101404031109060402070b0c03041b1e0902040f05090406091b1a090d03030b0d020916081605040b 68
    0x82c0364455000c90b0040c0d00010152000e0300d940c2e26000340604411204d0080c000c2c200020b5080e4403e0500c0b80e0584440140c005515005081c4581803d640108451000b03a035201c52034115141e00e10101d0250b40c103459941e807c1000700c684003140082416042c0003804415942400d45100c40001e55150000012600b51411003050141101c0340c00d8100e80c054446070010038000104034044400d9030785c0031300031540c1600e1560340070300740012400b420f400504445011004034402000c2c42004540042c010fa004000c51070f905402d8040d00d0f0100ea010f4244540749500300720b90150b081321400050085100705515041c40d0200082103100d039402110700ca550b030140400e04212180e8409003690f584502c02d05004000d1003001c2c0c03080d004a00c50803066080b00c401c1c540c91310205d1b604803001c00000401d9002c0c5140d56450840081c201c0120554001c0101d0003500b016944044c1d136030307105100d00c001e001014400070b07200609008000d0203541c160056030051048464000041d00c00303565120100b41d8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 897292302 1250 897291052 897291067
    0x7050a14070c0f081614030604260f090909010902130c030f060f050a0b03040b04140307021e10020a0c0e0c160c090c0e030606040b120115080f0f03030606 68
    0x30b0165845074080303a0325a004000c001690b400210783c046043c8110600c168019a4881005600d002c0c1d120407560700d0781000d00042c001911440c1d6000e81031030105007818a00e40301e1030030707000726034003080d41d8602000c404108414240303000707148140e12440044c000d011080c1d0300d5002c0b0351f05020401800300010307161104101e515109610020010401c1202800b115540d059401c0400c8c00f0b030700486004408040002c240b0590080c120f07400345600201100311540c41d80c9501c282d642240c94101002d02041103543c015030740d802485100e8101801b12405035482c10340400152076100c1c2106401d41d0031445e5180c0104680910003001c5a48070514003095990b850542115880365141c072060028461030f015007445a41c4508400356800200100400d49001d00306460b1044d04d50517040c0d1603448180002e40505140e004011030150181c4103040402d03c0e0b240650130355002c2e4604424103600b501d406c018482081084d50180d502101c042d0009141641003203480c0d01c8011b1000b800b80c0750029208 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 897293552 1250 897292302 897292313
    0x3010e150d0308071818060608150402210a05160e06122203081b0702061602040f020408160506090a17031317011a03070e0a0e12030f07050a1407 64
    0x1403a450401c11103440c00d20740c6598803443d0b406c60f20038490124510b8400046401401080200e0040c035100142e40001d0103180108406035200f00d107400510060001d5221003100108456401241016404500c51400d1a404400c00050244d40410003402c400d64a50030340f038030822225541680c0003408220360301c01c152010368070034441e00200781c1404d143c0180181648584002d0080c0806860042046600e90961a103030184140280d4000010804015200090080c6140083c4040d00c0481e00b00d80c41c244e0201241c01541c400d07041a08002c2030380302c4150413441900c002d8201100d44904110709032001c00e12103403a034081e40c2010b04501d0340c08001000c04009407a00b4500c03070640c0c4086140c40d042000c09000c1950001c140ca90300384200c1104602c1d03444400c15006034043c0c0240580d91514003c0007420101510300360001e0340e22844484030b1402400380e1406421602d960503502d0502d03244488038028001c2200080004c00c1c04281452030744200d41400c1c0164020070b41ea100d03001c4c1d0601d07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 897294802 1250 897293552 897293567
    0x19020319090f09021315022b120e1005070507110612040b0415110c01050f010501020d210f05040201020d030e060f1f0602010501050a090e06071107150503010e150d030807 75
    0x40a2012200c070640c1c0002503000400300700c1000c90300500010450a408241000c1598488c0f1102080c2c201c40400a107611b1f0b5030103018112030300c0080319807031605600900c6c100c4074140c80420004d2000541d402c14840420415911454240c0d00e00b4600b407e94011200010030182c002404c200069001c1410702c45680c401007d0380780c005200b04226847d00c040101154080313144000381d942842d000450a2191852260496606030094075003041d81c00402c80700b440e900d00c6091460302c0002050400c2100d81e00c104c001840d050840082d19091500000e494904010380090805085c1611041c3ea0300e80481e8541d0095105950404940c407410b0710071003e000100034031071102d106201c00084450303054001e0f50484009079010000c0c0f03500c68107000d0981d100c4001c0c5d80029445407003c03070520307486041c040703180c07070340f8a41035800ba0341e11100245c010200f20985580000c1c000300c01445a200421052900b19200b01404801c603200303500072503022050320318042c061000d41c00005100c0c5024031312 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 897296052 1250 897294802 897294809
    0x81e03091026100503060402011706012102120f04050a030e0f0d06271119150207241b08090a08070305011b0c0f020619020319090f090213 61
    0x1003002010070740c110082c1d140400c44082d020680c203002c3c0042c8134240458154000c98060f982c603003400d890541345900c4120080c000c54108002c00c020f200d41811007071840700c9048500c0202594403542c030106148040000f51000402844407014000000d800141c140380c41c640c94201241004c240c1d2001038003050b40102c40e19013011002c0c4040c0300b001301640c006d80d10090718000381310b02514040790b4181c2d4130303a981d0802401582c0031a04181c00d458a6041c02c80200742c501141c945058903041d00a00fa00c140c035400741d002d6880366800740304002485920708801141e03c0703284c402d940d4010388002c0941920304118001c080030355a001080c400c0b500308079000250084c2c9a12449a51044ed5907a209014801910300e540380c911100403e080030359031203802821035507900f000040c080d11744081c804c003602d400b240d011400300b1403805045592452401043e1054001d5038890f00d80400c200c06001024500034100b00526005000c0628059191015624489401600e4800c40d010701c603661030300c503007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 897297302 1250 897296052 897296087
    0x304091e0b0a170c060304051c0203040b0d0203090c030a08030a0b0d030915030605060f0c15060a032009180f010905030d0e1e010b0a080c03060a0905190c081e030910 73
    0x104100a02800240e00c0d140700e50a5410008902701f1020304a032280680d00410741c01900030044604a004c0b1a00510b40014003142916000ca00c61400039140140005003107034858404800c104a070b00c424480c03800303502c006031010748804605590040000089001340304003494401082280e151284c0d1100c000b9000180c04241d40b0788242680c1c0041c0e800260780e0b2034661017045000881d803203141294500030900a82002c000e02e0441e5500e002c80107400382000b0071035111034548a4240d0355a00420b0007107002801781c0d6520151851818181001002c080347c41e41c1c10714030420001000002100c8007003902c2c400c006110b04000c0c0704d480c10304184441801240e28410507102d01140c046d8032516900b201141c2170044a40d03241e49940e21942d051205d1075064112800040c0c10503030f50740114005501ca80d0544240c0d00760290718480500759281d05564000410300140a2180200f0080240348244104030088003404078100d0340e00d02c80d804a003402303641b0708540501c00c1c80c00303030801c0d50503030a000703 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 897298552 1250 897297302 897297307
    0x1513141c090f090207050709020a021009060614030c01090302090c040801060905090115030503070b130807030f03050a060f140a1706100617040b180304091e0b0a170c06 74
    0x310000742816442c0c028000100180640001c03200c16074401c648900750700c000076140191801c0c04010094000e240780b1429401500300421080100b881001440e621402c00082c059051041d5070b107180c9400c6400c580a43d01003140740d10b20b030380c21040c84030499904640c400502e56400040c100180034a0713100e400158200b0101141000311504141d00c02c8509400800c88003031007000c1580e85015520001e0155001009000c0c08a40c1c1d600d0380b5a032020302d182c00940d0012256072040741940c015030301a00080c48030608101182d905016494101c080d40100b44142418241c1c4924054410322483c070341105c03c1c20a0000a880d4545050010980c145010301e45540707400241d52a107030304540c220118030204001003003582c0540107c1280c040480e055000341d0380d580e9600356200b840603044048420070881c1201c0c890108100503c0a04000b0310b002c1900302c5840000c0c40c851408140c0424110b0518000170401d03100c80900e082260601e03100004c0d00d2001d0740410342001c1030420201d4000000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 897299802 1250 897298552 897298603
    0x1b030527011b11010b0904200402090d08030405010c0e03151b04030302070e0f07090506071110050d0e030306010e0d2f13050c221e0305151314 63
    0x415030203c60011000c0082c0702402e441c0302006007071300301201c0c01000ca007a4910349500740c0c840c03044c1c0c500103074402500041c60090b017a4001050070140c2c1d0000c8529503400810002001400c0c0241003580b8000d085c16151101d10700e0002c0d80721000c68450a103403000c040009040040c0952440d10300381600c6c40807603504d9899060003500c0e41102c2c00f41c00e610b900b400300403079003a00a050f4164401c0a450b9501d4804609100822006510064041d0351500c6032000c402134565911030001d0314600c5a85407644d40341103c0100746c09a488a9085910a800c2481006002c0e60412510b01c02d6600c01c4404158000062606006082105020038010b015054540b481009001c024001000e011201c03900139850740d001601c282d91085400c00304400e401d000d0041c08984203c14614107182004110b0f144c0c54a17015106401285038180c841c3c8165500c80c2002445024800100c0050f401d543c3d039002481c0203445219005203218004080e9402020420b1048a05000702c050340c0c0306260048031900394 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 897301052 1250 897299802 897299807
    0x714010213060806060301061b0b070807120204300b09032701020c13091a0a060b0a0c02211c0e040b03060a0207081201091b030527011b 60
    0x220300c070301201c0c1d18844000700d040e42c021911944500c0c0c0c0240f0040c9140c0c02e002049525003448020b2085074445803a108000419071080c0c04e01c02d0000d42d8507055207240080c402800c150030082c0c0d54109a2040100b400103e02d0169808400c4840c0301d5080140010700005803a210072001016207516451003d01100403004802840450b03030005e21840802d0006000d004601002440180564403802d20181241002285d0071072611001074000388506c203076100d040031a501d04881d5039581049104005030206148500005041d41c00c4015003403080c07069018158001740d200181c0301e149400d60a0a200c0340b0b401d0080a5002c03c0e03c141c2d00c0340851880b038600023013a42602c5001082100041a8590900d0721808608182c010028000740c1c442e10010802980045425254004204202d68507030340b160300142e000b4003100400094908441e1145814505031051100c04c050824050000030b001555501104000340e42c0e845d03001441c2d0405c014018948561541d2075128070f044941c004a8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 897302158 1106 897301052 897301057
    0xb15031606030b12102d0e0708070308032e08060f010e07050703050903030c060106020609060703021c02090f150405040e06010605030705030a0e060f1503070317070201030207140102 80
    0xc070b80598401d50621810720001d20a607c030000c0d04405041042024000d100c0c00003d07110031411555400818800a4504d000400c849001d0132548101c00c103402543c116a00305510803559034a0300307540c4403142120180707088400c800c00090f0340000b03010440d1181c0110340e07415180c60b00580d02030700c4507004540510341501c414000da205003041000018040c080e103400510030351800444007480e2400050035601014014841e24154424402e50603107035400c40c2e0750160303c601814011070712030340030016036aa10014a04040f00b4a018842c002e009440c8261024082480c0100d0810b65a041c2231066a000520400000d0b802e40e1040b0082d54200d2000b44020030140d000040e001d103020025522240140450000e0102c0d00c1c4800d54a203141800076000760051526540300c0050340a448122603004141c000781c200d045a21a40c12620b03c40d6003c075a13014030b0f0902c040713124000e4 = true := by decide +kernel

theorem cover : BRFrame.Cov 897122302 897302158 := by
  have h0 := BRFrame.cov_init 897122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 897122302 ≤ n) (h2 : n < 897302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
