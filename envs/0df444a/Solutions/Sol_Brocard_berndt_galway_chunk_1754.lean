-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1754
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:33:24.509017+00:00
-- url     : https://prove2.me/submissions/1b369a49-d5d4-4744-a78e-a61487564734

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 315287769 ≤ n < 315467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 315289019 1250 315287769 315287773
    0x80f040c0b0310091b0f0504082805010c030c110c01090306150b0703020a050601051005030402131118090106020a030c0321020d090203070b03011208030c0d060e16090e130c08 77
    0x3e103448903a641714100c0d402a12503d800f01d601049a00075540c9000e288200505508860403010b100303072140310a41b00030741c01c480130780151448580340c0c0c13821109148400da02081d95022a9007580d90048000b41070b803444500145080e10340e940008080c0355041c03000400d442d44a11074005140655503081c03024104c04401e242d110403450070000d50722a4000c0c0d00790b0325805020300128840c1031081c0c4045a0303c40c50388909145031110345c01d2091418400e580010020f070b6922007555500521402404e600c41d054043e5581d8000e410304110654a040c7d00080031341d44424450710010303401109003160700d501811700c00106040e00307000858408081180499491001030103003003001c550307400018a5030081e0122000140c44803c1110540700038090101c507040d010b80c041d030002d9001c1c0300566026014291560600310b4040700031065401c01c0c1c008a401d101400e080203203d84c08078101c413842403550300e40104504d1414160b030520074805820060440810500320302400149101341000300710b1281 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 315290269 1250 315289019 315289031
    0x102040509091006060e060f1c050a091104050601140c19210c031b020a0e011202032503141c0206100506040f0e1f030f03080f040c0b031009 62
    0x400d460301803510180310704500d04040410903e1081c80e490340b6640c1c02908941c6845207610320300b14249c0210344144031484010b0556a514a464041ca9008822426007c1050000c40ca00a0038821900c3d200c2402107150130100000c5a82c80070609040400361843d46075902e071a00601402c03e0750180a59203981841101c40003005240c54103080c40003d246070b15180002212401c0380e4600305440c0c040d000074130f0212424510300c034140402c000e00d1310041041c0c0d041039454003000130111090344a0602454000488401e40c2414040c00030725010090280710445105d401a1900c110179020107006d00c0030301401d0f4000041c041010950001d58946000056684060001e660b1501100c0390030728000361a10000e024104042580c1c10349a62803030350140281407007105944400300502c1d01c03003003642c1c011a00c0c403503c0100c5480f1000e140225021000d10f9094180506030080242000e00b4010b1044204004104a40181e03810b032101d1f0011140d42c0e41394140c000c1189011a002003c070700707141c40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 315291519 1250 315290269 315290281
    0x30c03030e0a091a0111151611030403080403120c0b0f071103040e010b03070203070c0e010e010b03190905010b0a081506010801032001051c0507030e061e04050102040509 75
    0x10464088201100d4041d001c07030b164a410401d480d15070115200c0a021844c1c000040d43c041d07014810120600720807100d9080c1c410000c294100400d031004454040d17488440344130140d0080031200745030b64001c000c629203443c41c7c3c1d0f151910b2040b880702810010351020f0007007e0511416030f071140303150400f190803641c3c1440d00010030b04e80015100000851010000382d241a04080b0130f54089822803a196400741e840c2c140240b9495000804401c11804100300c10030025446001800c05811102c503982c140b981092824882da01060f04240e141e1a42030040040d80340711004000c00c84100d450700400c0c0b407d042d00c1c242d405400324505003644120500b5000c9000d000010b00b02c1c01081003441d000d5080c3d1255001940d003030038280406051000000d0a4100c58120814411030509061501c1c0785004685d40e14200080d001e0040b00401c5a00ca000b8886030315414014105007102c0040680010300b030441000303410f0313040000071950044104000a0a100080d030545000b03100c054200041841c2003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 315292769 1250 315291519 315291527
    0xd0c110d08030a1a040501060f0509030f0313060206010b040b0d09050c040f09020315090a0f1b030b01054204090e06190911010c06020d110306030d080c07020409020a030c0303 77
    0x1100c661213424140d030540629440c0c01d00a00781220090740f1680d260601202080b03a6980c0880780f0b99405204408080c0e029460400041500640c0444a943c400e400c0100003401c00906a1101c0b06040043c4028001c0c070100c00112a08010414030000b2011140c0c900a801c006074501c055512a03d030a1441c82c9000507600400d2006100303c05448680700c4019140c014600140c80c013004962081c882000041c0050801e190740b40c0c000e00703001d01c6d44a802402104280c0058004403003200312400100100d003002164006910810715602004001940c14414941c452100f403c0b8500c10003049a0807079000001140d0180801c5082400885040043e9075964001075501e041e40350300740500707808002040d2290000380381e8040c071100214841381c001190783c0b00800c802602c1c2182c1c20000b00356014018480c2d4080e40d0222189aa22881e00074201800e10584080c070009002001c0200038168904204940075030354101d0300000c40000074004100802c01d21f03040100084051000031080c1900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 315294019 1250 315292769 315292781
    0x10c020f0d080c12060a08011e0e0a05120d060504020c0a05251401030e061e0c07030e06070602160309090b0a05061606020c12040503010507020d0c110d08030a 70
    0x180d4412188402061442100d0314901200c5402c620f031070912042c0c0c0f84214146650781c11a500610707a8040c4c507119210300b030071260608030b0000b00c412607181d12034407404103020303424240400802030600d080c0d00c4d8071031a0321380707107070090000c0142d80004040d1403050b85030f80081c0c042c0034064011074a0304580240c1503520825441c00b81c0300d9100d01d080803084807c060f0304405005c00c4101d0001700d80d078074005251014501c0c000d215418140c40c3c589840d404941000b04510a08090307850000d81022001803148075407024185080708403081007040701181c0c1045c5e0340840c510094561035980c003a2400d103c0b0003801060804640100d420200350141a845a0421b003070b03610840341001110310758000c1141003881031240d103801c250148500e008002e80001c69803492805454058500402c50602c1343c1014150041030000100119040c401070409216040d80207120f80010a428840c0403000751400b111514002c00b0012007074a030100c15110010f4070030b0720990003000a9181d007010030691001d410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 315295269 1250 315294019 315294043
    0x807050105010e07020a060c121109100e10180503031c0b03070e040b040201030b09010b1b010b0f0907050d02192c0f03011d010506120714060d0e010c02 67
    0xc24200081450f00118100900940d9590001c10030a0798a50b00d000140c5070203000030040c840007668000d4645032034001d00300700000e14071440c0c0c0c0d00c41140c0e04200110898900038020418202c04010440d02da100298814070070a0400c41d40d152280c4204401400c41e6801854240c04045004162040d50001980320703454207950500c0319842c4007003030540d00c542d90301c58844460035100100d000f0407140c2002540050041c034010030058420404105d02180a034085001000d00180c003804581c1408840c0303002c030341c040c0028080d01a030f140c005001d0b2284001d08520941301c10001c120300c0b9004101b220340b010b01c43c2c0e07015525040040040102c1d0180c00314400d000c0392800002100c84890b02d0040c0700c0c190045465014449a00000d000d80d6210300620300b901596200c2e8182e501ca1500f400c00000c02d14160001300d014a407240a01c55260040d00b02c401c281e0744840300c248003e00324429011820402511926110503400d44824060f080040c40c0300c01551800c100c00d800c41ea400724540780ca01e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 315296519 1250 315295269 315295271
    0x105090105060a1e08120309060f040c090b061603210510050105031f03030c02090702030c060a0203070c060603050102040911071104020f0d14040611040e0105040b030f0601170d0e01050706090507080a08070501 92
    0x180d141d2b211410181000c50b001003400a404000388403a5000740e101c190050b0001c3d000e00d04143c2031074101840072030742603000e80200d08942540e401c04200400b80c155141c6e401c00b028041801e0940262080540714000c07107041c45008000103456411b4103910100007000c050601080070307604c0c00c01820400115505a0242e0761304c0000810640c00041180c070604440001482780e43d40b401c85410003500068504e90801021400c014082942c134040c4201460245000607030306d91400e0141130072030b03051802c0700b10740303c0050080341c02281c00506121801070040e500540e80d4500840102c0440c4902420680801d00e040b0b824440c8001000350f6600c0342e40b0952007080f4004540f107c002090003180724204294142000500c60f034103064000341d480303803000703002c440c600481d04200a09040f4242c024000210b8400a5000c01038010005024110f6890401204116528000800b00d104001015040c103444d80141e00400ca820000c80c0001c04080701030303801159542c542011903030300c0031078241e4441d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 315297769 1250 315296519 315296521
    0x3010308040905070e01050a032a18060e011d0d061802091f0b0c1612060605060f0711030a240e0c100c0c08030301090b030105090105060a1e0812030906 67
    0x1380d004243c15020000141c60f014101194094210b014100e4030804c4418004504091241c002c0300003101080d41c0c0386504d654850f03001c0c00c14990390f010328a6000e0420812110190380742e80c2d811600702d440702e0140084144005d000c004c0441e80300030b5207000042c0320f18a0100d500040b140c1d40450340b150b1a00c00c40303c600040c0c0f01c0700310880b980341052482c00c144c480c03051010080c0c101c4441c01001e6809059040d035842c401101c0b00e0910b0a40b03a6407104424100d2001d803041081100d203d41d101824088648a041103100019030045000b00b8400605144003e6101240b5985c200701c2c0c03204203a0700110049000d520281c1d101c00804440401020345400e141c400e204241d070100d00078180440c0900204421440c40d0300489080e6030f40d490035070300340481c28408036852000740025030181810f031901191140000d0300b490708481e0018048203050340342030103002c100d540c0c407004241151a9502e0008111010809031411314410390710000d0103100c3e01d1425402c022036a40039601c41c020a1082d00e10b2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 315299019 1250 315297769 315297781
    0x10311010c02030303060625030c0213050928020a060207181a0910030b070e0a0b0a1d010905030115080c060a1e03140f090105070507050316061103010308040905 71
    0x205501e407402503040d0400e00015003e07080076406412516203441e001c0003503404050080c03120410385803041e000155041001800d60038000c1c1c54540c03203060080c017045949402d0203555199040120780395924103000d5101460038006808501140d174004284c40303083d5a803020007030b44e12071840c0308078550301c0000c9405501c5880240b00f031100364000a040004080b170a5030412801030001810121001d280b003001101154170305650714401c2543c0d84440b076003a0354000400c00b4002d61548034103461902041101c0b80240e02207000c90400c00c08a14031251032840500503a04070b0f040340c114a805610301001c02c3e080740740d500090b5085803c5841650070025075081800080c2c42402a0361001c100c0801040d40c0ca0081d034035072580e1704a56407400043d2402d40700240d40c10040141c030980081001031043c001401390a00c2600c1d006292820300707500d0041d8071b90740d007500c2e4061000802030300461740c4021030034403a00307801030391582070011801581d968483c90140b0070342c0c0003400364504940c40c000000784 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 315300269 1250 315299019 315299027
    0x151206040506030a08090409230601050315041109060325090e030403170c0a060e06090c0418060203101a12060108072a0210030906050c040b04031e050a060501031101 73
    0x44260081e401c24500b05001c000d07c000351840000442e02c802454520b403285103070300001c0000040b41305010f4251035240c01c00305440c200c0304503801c04800c1025402c1c031000a01d5640811003c00040d41c0c0c00341e41e6954100082d08041210030940c01d204a80040034408182c0500c0540c203235040403030304000202ca9010b03015500d00882c00300810300380310603510034840030184015100400c0680106c4144602c0c030b03950310007503c00c01e92160707405500c494180f01d8900340920a04035014000d540c00c128041d60145551181050404050310866001000c00c20501010f96500064010750f51032066902195a4902c2d45910400341202c2c1100d00ae404104150310a40c0218001c0c0701c507507500e03000c02c401110b00c048110294503100104030216030001d40161030b500d0791070b00700c41d001d5100000c0704581401c100c030a4410003400748140800c10002032045192446c2034509680c0c02c48000800d4020122541f4044050702002605501c03078802d0001c10401b180d0485c1d8140c0b4810140c401c881c012440c0191 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 315301519 1250 315300269 315300283
    0x907030f270c09020c1203090c04021309050a050f07050a05040305071508090d1d0102031c020306040b040504050607030b031203040c03030905060a0c030f050405060315210606010c0215120604050603 87
    0x10317060b50021144692010786000155400038040750a8800c6c04010400081c12603002c1c0000b00d05402c002e00042103110040d219099200015032400e00640c609007008005c0a50010080c6060103400325008001d02d1181c010f80300a194800c048502180e00c0c2c3c1140c8012804070115030000402140004040c1000440c02d03c2c1c8094903038607010501d2940f0940036503003102160481d4114401404100c0003000a071400b02101d00901400507a41d003441da0910080d9000407482500442c141014040050000140903502c184a454005030004407600000c2c1005604c2c82d00ba10440000700600c070038880d400041108a902c66120003003515511801d114050103540320450100d03070180845400320380138a0f00c041c01503026203410361a05d6200d10000b0b180b504144c844108102505202c91910308250810890030364440480210510400381c4031a074560b07000300014100007401a5140841d110f0750034260892501a08264881c1e12080281c625840121659841682010003103042130801051070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 315302769 1250 315301519 315301537
    0x903130311040e011503120e0f090a061710060501030501140904050705030d0201150801060b04170c0402030717060f010c17040312050a021204050907030f270c0902 72
    0x808a100d140d038940204418840c003880b500310752102d10036103c40740c00388201c41d0091a004840700380281141490b240b001c0148504009200c1060b800700401d03510809440305525049500c5001c5603151090350003d441c680c2d001c41ca1281200e00e0000d8044000f00300000c0420306c00c001000324594400c0118107a82d0284504030b020400c0650011241c18000f1200340e11900620455942c150f580380441d107445643c074103900050b595601134882200d0103d2504c2d0080000c030000344025400e0074126000703803107184111112030f40d0580318010b0600051242c3e507000c110003002103440e45090720b405046c2c00000241c020000f440d00000a2003071818403c5540e070140103070348100200700c3c151303214000509909484030800d54140400000540076a4680e080c0c10711954403980c544c040b400c4003a181ca520381c0403039038040c001804140082c0d02c402111507803040107460081900d6005036511402403250190760554603180b000011410301d9944414113045104cc100104070302d5441d03a414049005080301 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 315304019 1250 315302769 315302797
    0x1030c06080a050f0a3801030608010606020c011101060509040308090105090d1409011803080703120513110607201206040f020d0813090b040c3b130203010306050903 73
    0x454058100d41e030207012644140b14111171070744c844442c46e001d80040303c148400758401945155201d0b50780b600806000b459424005d02000c1d040100194842d0140d100c441d0401800b00300340d44001400f50044c1004000240c1414010300745410000d000904c21a80303681c1c03544c2170101040510a0003d0750034043c20250307071044040482407088600d6035000440d95410070440314404809a180e00f01d200b402148078402c06036031007180d4600542402c1d40b000c6c03012141840c03e400c12903450214125002d8042d13000702003a10040000c000515203002e085405819420244440006101401c1803c0c40e0300c0c00c22100c2100001c2900c01041d5205012500100f40300701c80c0900d07800504281d0349020f2110710035071003142002109038411140068681c04016540d131120b0444d00d8a04040c0304210b8001490700e055900351810b41101d40311018880640128040907074100702002c40c0b0489200e0b46440020507002d484000e0f000d071071019400a02081d101180340101041403507000104980f8030190000b9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 315305269 1250 315304019 315304021
    0xe0d0f051806031806012303060f0a0518030c01151e0918020603160905120a0b061203070b040c0b03010807090e1005011203110f2a060301030c06080a050f 68
    0x140300b1142c001070440024030000401d4564a207100780841070280c5182070081c1c4078503d00d074103002480e40440700b145020750021030a000000c1003070b890700c4d03621001004001c145911099241120300c0c5440040810901010901c442c8015042d0804c100c541c2e1001e007103603501921001d13140c40c60340704480200d1300218500420003030718080340c1006081c0d404c0c0d43c1c800101c0c174181344c011a02c9031380308841c01000300c001440381a40c20354000a05401800302500d4016080b18070f07070325250f0781e0300c1c0031400540f608031603c001481c5030b074807104802035050700c03032081d00d403a20034500d0011803035001554102d9070742e1040080469000701c03070010791341202c040c18001c100301443c2001882c001c02d50792000741180d005100c44c065040c21540201ca0013072800d180d424210300740509000740b050390500500c03840c0b030700459040d10b400040041c40079400e54014500c965607100b210844165404ca5091080d00990040000010b2045c8940307203408036a0a600e90090380e0f505c2021050449800315000d80003000488 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 315306519 1250 315305269 315305317
    0xa0501080c1915080f130305030402130e1207201f020c0d0b0121080414060405040c18060c0b01060503040609050709020d0f0509060c09130e0d0f05 65
    0xc1d9540c9a090440c0d03182402c654580d034640200002c08503050000c14201400e0040d1000165200e60348905c03903c8502840144ca03640c02401031001a1020303105046461815481010543c00103900f62020000c5481e1703003081740d01c004096040f40e072041d99000b03861840480202e80f00710700b103410007600520f840e860060860030021980040e0b504c4004600c910101210130380c42c0c8980c5615040d0090000707104542c5404014010b8880c041c01103000100e880780c2e59170025400c0403c0c0c1d82074668941c0413061000004012503064000cae6441207034400d0805402c50380ca20b42100e0100710010300e109500200903140c590950700327481c2d85100103100802010040240780d04c1280a160020701c00e6070046904042c0340c441928044164100c100217550004d00260b1720f000ca84901c003074a400b40b00084c0721602d070034481c09448540051541b011803500113a2100305940d00000c41ca101d4a0380d840401c01120541c140545da480c181e0800400300300c480303081020450141c0140c58001038405d5805003100824 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 315307769 1250 315306519 315306529
    0x20f06131a0103050c090112020f0f13050f04050f07120b1504020c10150e160e0303040305010501030b0a060b0307140c1504020f060301030b070509010507060509060f0a0501080c 78
    0x40d203810740c0d55001c500c208010125142111a0003980204010000801c0140400500c900180e0002141e24a00380402c0c006844e80304003811011821280e00c20302c50450702c04100018003003003544d180039181c40e00308080d840d5040e203030500682c011030031500100b1803000e2450b9952030501480914a046a11000000b40c0140d03440798006041d9001c6030b40d0003a03440208090343c10000c1d42c0ea00a030407542d50f850141d44140b1403108011250a00c0115243c5821000f00c440c00000c0c04040b12001050390900c2607034000c1e103a0051803807001d0102c90390740e550780c180701d8001c003820f0100325150b80c0039901007143c1c01002e000d030707509907607000402d1407130764a603030748203031500e94220036401c1c002d00301880580194241405242541c1c8005a0b00606902d098070401850014001149126040502c0113101003030701080d503290b00c6001d0341002940d81da140b00050359070b802580c0303000780800c0c1000c0030000b0341300e40450700c60b00800c0402c0f1598100d4485c010800c007501d809000f41c00c02c56201716042c032042d00d40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 315309019 1250 315307769 315307801
    0x61106060604060c0f030311040602010c020c0105180405100e040c06080105030a0b0f04020109051504050a0503030c03030105190503120403060e0105061e0105120a150801020309070306021c1d010b01020f06 90
    0x1b09040000360851984014111074000d42d10030700250359500c22050505806000e50240017400340b8040b403500b03c0d07070b2842c00d440c00070841c801c90280740d480000801c00c0000440103805841c00200c140264a003524120200900d14000c00740040c146c40000213160034000348401441d0f81c45402d800303041c0d0310500e0071021a00b00500c260f0411440300302c006107680700c044000c2d00b03403030240c08011b83c1c95040009112040441d68007190103503004200104410002000b52419513400b142d40080100081440408254003034012950500a40820343c5000170140b00400840c1c1c4075035400e11207040c0c2c0807000d900b21141100c0b03050304610607040c42c840c0c0b05000d010180803a40141040e03401d03c0c0342051600380303a840444035080240e40d01d500d02d03125130064420b242d0041c03106000070340c5103180142c2d0f9030f61204614480108100d8005c100e109420013460041201e545030014100095480403504003028004040150300075440c0c5603841c1c3c1c140d403000c24034200c881c080300c00031314181d2119226010110340c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 315310269 1250 315309019 315309023
    0xc12040812070305160509060f03190204060207060e01030902150a020a08030109050708130c050904082b0b0402090303030c0c0c030a0b10060906020a0f060f0204061106060604060c0f 80
    0x10104076106a20506082a0340034005035a0005001e1402d040041c400c1d4080403191424407038203010300780c0c5030340c0d601e4111903080c5044141c2c2030320398540c170469081607040c082030929202e0012038003107031441d800105201281c20306d0390303988604841c00005500726000c1c00c001a40040380e500700400d000103842d00404a05c0da0700c0c81100d002c451a92501d0380150420380003c00d0003a1183d09200100d9882070300150001715560186100d130500750707914003803400c80744a400d014181c1e50780003030117000c0b2000a4410200940c00d10f482074403440004d00c0c068883c1140c0c6a440e051801807001c003103040502c260303402004080c1c0192301c0c584490750400403030381240c1415100c5218030b962504150300e00b8841455600c0c8585a000040e042003c00d0a120600642080c0d041054103c010840e160f0300241e0015100d41040c1070818000c0b1a042201c00341401820205455000090019260791700220031100c8030402c3c001e403036464031120300300107240c03103940b080000103182e00f0390007004a8900c11580f0903043c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 315311519 1250 315310269 315310283
    0x10b09090705160503070b0601050a050409090206280207090c020d030f0b04110d0b031c230307050c0f0f060c0c0307020405070c0302010f0507080a09030201020f0408011508060c1204 80
    0x300701c0101d08900f2030710403004a0700c642021401d81c1c20804902e0603550021001d0034039505100500c81c0c0100203019501ca510903c81d00c41d034082c015500e80800b01c0b4440b08189143e40f242d010001401c03691074002c015590010312500c0c2c0c000451b00e525114401c0701d10807d902500111a00c4841180507142848581c07208959844d4103002980d01c0c4e03c00c0d03d02b040304c0c550200307840761105132035401150b0500f00464000c1c0c0240000c100800c07084010304110100900b44980c0e0f1015107420540ba4520700005007003030305000001e0215071900300010705004600c410071501e4a080301401345885844e004d142188952001012075030101c080c0000e042d40d40da1100840382844d81c2a00000e0564100f03445250104600b060303404145942070040c0b0175000c1a490b001d000782c0c104500c00400b0428028005e04030141d5840ea41805c15200f074044506802d0041101902d86860300d40c400e0080940490b1200c4061b0b5041001400c03e1000c51070301e1044911885003800c246042001900c60040200211030308 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 315312769 1250 315311519 315311527
    0x10302090114040e191b05032109030d020105060a0f15030915090c232d090c0904050108060c0d020a030207020415030b070507110f0a03050d02150a05010b09090705 72
    0x10101c10016000c20050f15420486050342e06c0c00c2040c2010403480144090036048207043c025034500281001c502081012040d402c441070700000c82e01e42c02180384003589400307081515080700764150030090140c0c404680000c40203a89040d00752020025210750328107840103000d00c2103828000d5000800720750144080144c115100c00b099030840d1552030045441030b041101c107110000d00d0b1108001042007880707025810510100016125203443c00c1000d01081c5000251460032501c40b002e40c2c01c04070048c20a440700d0030800d86840702504000c922074003440c07030600001001a800100c8034020034940003020300d40740c42c0c0303103444020f9406104980d06064007040714400680f1644140d04640c41400c0c144807400782146000c000c00807029128004100307090020782c000c9020340c01c41c2580d0364000c4803210161410318000c1442101168030140c594002e000e08804e07440d07000306201c83c000a2084110403180c1d555607141040351000e01441007003080030b002042c142d0626040c0980c20144030f00b001424 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 315314019 1250 315312769 315312791
    0xf0c050312180f01271422050403090801060e220b040f02030a170c0708010c120b0a09020304050607080a06030b0c0d0f15031a061c11060a17070801030209011404 71
    0x41d0075088803179110b00c9544010040044414010301e8010742c222440c075441c03200d0320710003040d00343c40d1014406500e545a0115003090b004807084401000b0300c000a020355079030b58070070320483c20381240c441146204c40385048a00301031000140034103d034881d001000d113444075250800a420002d004a8141c4590504c05000c81d1514803203010709502452460394580e4554041e5081141e41d6000035070766030414442100082d0444024240d6032035004000030024049030014202c40302075031050507420310000922040c0704000c43d00b03500c40ca05a480e00500c42d2a904140c2007121501d200107031048089801281c400c24900d0024081000c1558000c1000c0074000c070900115140c0c0c140c80070910441003410002c21100c449101a0082d0350179003141d00b0301d44200450030002500c200609112041d00c061000c00842940525003244003405454448100803405003401c0c40d81040444202c1d0f801001170140d0348158845816031303602500324000d03070746004840c0d00000b03415500f0907402508c03480e0140c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 315315269 1250 315314019 315314057
    0x1090905191a04231209010c080d0603060209011713030807030e070f09060905101217040b0304021219020910051804060509070f06080606070f0c050312180f01 70
    0x802580188213000300c000358441405000e00729032a081c08590449a0704825003010b80c0c0640386400820709141100c0c03105071501e4405880303510040700c145403510401200341702d00390f40603003c80e203001e88506d41107001c00a00022700120485441350045001c141c0c40001074070070091950840c000341004260b5941c0c0c1140c082c14034080e81c00043c0d99030341054003009145000e01968008040c0e01c0c8041000c0c1c2400348140b002c80016010300707500ca60f040b0003120108516000e0000400c0203212800e500c941d00c6106208250b0b2040c2c40681c8241c61800a103800c030000480c0c440b02d10241100f030040400262703070a00102c030f03038010b1903d4821610208001103d03100d03151b10300a19543d5405c1c1c04110301c0c0c03919003107080741d4016010b0b508a070702600c024085d4400c1e0b00290000c3d5030719400d0001183e526640024043d01c40c2480c01011a0002d40403c0c1c03c100d501072440090750f00423015582111702221814000f8080c01e080c8046520880b01900c1003800d003480b403540c1641c0306240c03d07400e51201548183c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 315316519 1250 315315269 315315271
    0x50705100c05160303240305060c130b04091a010e030a02191205100c1e03020c0120090405160e040f060e04050a0b010501050a050301061d04060b0a0801090905191a 72
    0x740110343c03280c012541c80400300300c031080301b040382c240c0c00703402c860860b260980c0c0c0c0d00c0d0007031803079507010b00010780188004003082c024002045040c04803a580e43e00e42c507040019041c03a04940803022a50321010301c4542c01000302214240001d0300501c0f44c096642c0812807540310610640c0c41c81803854070049140c044100030704201e80d010720010451102440441c0c8200d0f42041105820041d06040c50340f40c00442215404690741b0525025880311588294240140385000100c0c0031107003030040048013a03a04401504100300104c5013000540d960075101d654040d40a20402c00089006154075420700c1c040d880003540450590002132070546820f003805003000160340540d103e40c40041da140c1006443c1072a0307405410700b0b1030074a08042d00040c015026000c180141c20a00c00c0c00b8510b1140020040300c0d9004e1124010414441c15503169041b4141f5840030000100059030180082042811130141d04583c65210008110100300a5060791540c42c125004660b1070018007544248074100c14601 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 315317769 1250 315316519 315316523
    0xc03040317010815010f24020c0a060e03010e1209010c05101812050703020307060f140103080418061208030c0d060824100302040509030c0a11030d050705100c0516 72
    0x8140700c61101c00c4e55885940164801001101c0300581070260750300103041e02c2c007060b86003c0041e420250071201070781040138440d40142c000a1098002806a520400c3c5000301d43c016802008200c048149443d2116640c6481442d4014200140103065108000d8103648a0003001594401003001301c0e4082980c20b8540c0300803007580c140343d290b010f01c881904054000e8a040c100031b850503503659406500c81c001d1500103840145c0d2044402c140c2ea0040d0040781c881c8103109200b18580da100d02c2c1075210743d00070f8000c8a40e403c02c1000145584034080c441c500503908854040d4103003141c55600c2c1d004591004044481038041803140030074900c12401804003810907000035041240300302c01e80103203490502621103110880d410a01c4444820040c0180c1541c0d01a40c020816551b40c00b2a107280d44520340942001d4881c46d844482800340ba01200500801300700c1c140c0307104005000c42100d80d80554a4042c0c0540c1000c10070b1504000740c0d5000c04a58101400c02a00307000c0d01d8203e0001e4261540c1c81 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 315319019 1250 315317769 315317773
    0x1140f040c06020a0b04020d0f1e15140609091507050901020c01171306020f0d0b040b06070c060e0a09110705070f1217131205060906010303080c030403170108 70
    0x140010015590003507009001e051000384011140ca80300d001598401074030203070048074800da8080074000d03607000c07014203590043d600050b100c051900e03046242c4500d10f01503602d901c0505000001c90200e02a01a18440780001e000e525200c40042229202014103e1800b0f03204607080d210b005005110f0b6039114010a44410b601c4038820400a03040180039850681040900c0e0399407500200d1440320250842000808001e0540451030308000910940150451010b00420000400a00c0c2e0704442d50a94017601d05214262000051102034002c0640007007a138150100203000440c4036aa50000b051001004441d40907038480150742195031100e1481c0b40c2100018403481400400c02042c0d00030147d5040b01c1c4491031916500c4406503282400090803c0d010600c0321681d0707a02703002030700c0030b15003501e0483c014960f40381076003941112501421119405240700181e00d91201140190480f500350701c43c1c41041d0340307140005540307520013003088080c40510310034101144c08140c69a40079240c0040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 315320269 1250 315319019 315319021
    0x5120703051b13150833060108070c06090b0c070308060d0201020705060f09090c0c070923071106040813090b060d150b070804030b06030606010801150201140f 70
    0xc0250402415411030103110042e0480403034035880380d03070a484501c014000f00144010624880c40108080c55100e0019482005400c03500c0101c000d5010520080e0200e0a4801c0c0c11440441449110110380c441d010803000c03000610002e02500112070602c0c8a03d0700015004840e9030748414460301660211407102c80413030701c03400305034200d0485c40c0c00401c110362802101c80c05a000030341d100003a020b9503001c1c100c040341801040c40b505081d0750003804014082c8941d4903006003d400c1640002e80f500603c1c0c03040080005604809100381e2003141d40401040160603012510400d0b11403024041ca03041001c907500c1c602c00b02d103041c00b906004034801c11035240c0c1c5600c00a54440d00080503045005005e2a259140034039594034030865200c40501755001c00e40341069500043c140405910044031504c4c000307007420801c986880103205407481407540300c3c0c0c01e840b6502810740d6260100c41c014080780540c001803090311302d40910101500700a10000c219038109542142c9030760029101c010400701510 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 315321519 1250 315320269 315320273
    0x110f1504140615041d0f010e06100b03010e0402010504030602120402030c10020714010e0a08030405010f17150f101806050708033c10050406060f0509060405120703 72
    0xc00c500003440c007224001c2046081a000c1441481a80c01e0303804e01c502e5503200801c0e50640405425426440c1a800340c0c0e8a1003210480b1030b0290040c20401403e43c052400050211203100f844042541d40035000142180e00380f9641d148a200c010b0001e9062200600001000038040d00042070940200503003201d490030940305140c1b0f403408001a042c4070301d80c4030f01d400403c41e50004804084454004c0d251100c404400d0058070481100030655401440c1d01c10003081e004c41c000010300880d482a6524080c2c00380802d4125041d82500407108450138110010608648240c902c420306070000801109140d50604002603128038001000000b00340340e05c9031025a90b0910301050b0050031982002442d2038155940c905031444010300084285038450300c6013100ea020080c080e15410710f07011610310781a11204c100c0b00c0c03c0c001180e000842010402000c501d0b420a8000c0d00100d0300c1c50307110152440c48030001513035190445120990440f00c24840000d80340e99698010820800440203003501900718 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 315322769 1250 315321519 315321533
    0xc070519080d0c050408100f1104120c08060103031710170705040e0a1e170414040509010b0a14060f0301060305040308090309010e0d0311010f0221010b0703110f1504 73
    0xf0102e1001800802c0c0010015840080b47c00038449820718400148001240117403401004c035045998030090011801143c50000116040103c50280c8100510181c1c1d0b10041079580c0401d00005001400e04400d01c0e1800c0070401820b50891610501d140c809600c0784070008001c06c44024904503544840c5082205082c9842460706500c066006800044520b846500100310345940780e542c806160451007040c01655100c414210000a40c26940d0307550712007000d14543c03291a0300038881c919001c04036030485814400c00200b03080142c07628035241d1400310003851020081032000d402c88030410204044e40794040066010303107081e446c006100d040504000b40101c10040034051030354010042d081e456030300210200c801d190126411500482245401c07959034401c0500e100c07241d82000140c201c0c890345038015000e1a400414034009105e040340c583c800010302841a15801c40c03041001e2000310384141901680400341c201190034002e4410015442c00310000b10310958802043c0c28031040150f4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 315324019 1250 315322769 315322781
    0x6070e100216050906030a0b1003170901080106030e01090213020d0606080f01180f090614060a031505040606050307030c050406051203030708090f160e070305010605030c070519080d 80
    0x11a00c0180101c21107202e851201d441d490250703611030041c0790b0002d402c40c0d034104901c9000c154018504000e03810048140c50508086000403180c0000c000d0080d40c00b00700318003c2e80d15041059550f03000f82c0e441d01d8401d4008107400b1030b8241e030300e5480c0c03042c903400358480b000ca290340b407000020010780e140741c0351a81c1c1080302c0003a0014400c100340201440003902d00c04149906444c50030503e44480c9800040104c020071100d14400421402c1c0102e950a00c9a10760040006c0702800c10a43c403181d4421041011942540c04010203880e418400b840911080e0781c00a60303c1071052000140c1180c0b40c0f80000e15103030701c5900886800d510081c0034440c40c00e0074001d01c0010107058407081c0c10440003072001600c07408001c009400b0041128000b5002030010440d181c000428032080d5541110108541885008a800344596517080711740440ca20174480d2064a048504540c0c440d42952141c0d00501c142e588500c5042c0d80070f1045804c0460900e0340c0b4000306907424030940405681c0c5400c1100b900958103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 315325269 1250 315324019 315324049
    0x203120f040e100f03120201021204080a02060606090d0f14030c16140d0308060a150905030f060f013809030c090403020d053007021b0a0e0a0e06070e 66
    0x82c1c2c3c09070821024018006080980b5480b000800c80913100440480c0207014000d41000c081a0072010b01c8240b01c007190083c02d65120550944005903504018048103102d455545c64110050f01041400300349084141021503100d591000b10700340800300850f18541001ca00140c4d541c009090b6041e03511006a60903000f000c8001c580704092100a00103455048215030240c02e03c21900002280ba03030711002c030000500481c0d040c6590071202a103004059000d01d020701c40c002c3c49820780c800b440620018006110351300800116030140e0812801014424400c84940310030f2008d03000d04010301c82c03121540f40318092045420782d103610707241d001c140c070304440750240a000b41005020300c80840d9000c5101c1480400d0350a0030360352031014000700d8001888004800d803c00c3c0c0c9840b646801c0820817800c06004440300d03402c0f00c1600f08810000d040d0180e0742c404c40c0f80c1c40382c10b034a81048601c81d0b41240b258031540c4007a0005000303901a01c1d007414031900b282c0801c0015085aa800014a800c0e0b1211500c0d0b8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 315326519 1250 315325269 315325291
    0x3180109210f140a050a0302070c080601091103041709031204060314060d11090919050a0605180601050d0303020c0609070303020f1f1104180f06150e010305040203120f040e 76
    0x640005043c428481c1d007401d0401c100e400914030b071100d402a01142c04e070316800000b0b01c411540d1120302c51340b030380b400303001300d40701d0314100b020002e21600000c1c1039a010302d42120091240b40c0324071181c415103610400c0d10755054020095111480307641d100141c801807410340c9000c1082c3e101000340301e0012074024160791250150070740040100b00207050f6960b00400648031146aa1180d003171032031a0a030503914070b00e01064580403150810001140003c0001d00c264014403840e04d405111061101409900d41856401000100a1481d100c0d0002d0001c5000c0c0c207005151880d141582403c00c001101d01341000c1d40b1012081080543c1007010030744001400c406021224104800c14070b5100f19100308180349034a8803440240d80344168115001003034ad0b8401a070050440120f05001341c0003120343c1c000501d107410800208003c68043d4041002e0300c542d00e003100703000c2c404010b40003428050000d90b010b04c40c0452078010503181500628400c600c00740007070784843c40c0c09940803030408000c2000100b1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 315327769 1250 315326519 315326537
    0x50103020a120b031c03021b072301030f0507080609060616030503044215060c050a08040602010b0a0807050a0510031103040c05040b04050c03180109210f 68
    0x10703941c05501c20300c505950241c0442c5003910100000e01d804e10510403900c03550715045d500d10b01140c05900408104919201140800481da44419200e10440c4101100800c00b40107201600308940002030169405040028040318030854a40490b401180e040f00402c071020709211007031030040c41c010f500c200d0841d00146042e4001600c17401130100070380e00509000000c00840c040007102444285494003105642c58680b540f1201d11100036214918142201500840400000000c0c050b403141c0400074003090f0310365071a0032400c94181c0c00201042e10a405603081d403c0004103404002c200a1110364004180700a41008200802a1302d901a403069400040f0030030042d100d505268040703400c12504419402c0c5140025400340c07404800030301121800204100800400c43d00c60416108242d40030400152104140030407148140c440141018003400002d1010450a140d8070a080d0f1040c0081400714941d5200034840005024000d03401000d444c850f52901c1c0e11082541000610340740c44049 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 315329019 1250 315327769 315327787
    0x1403041d06011215120f1220060411010503090114070e040b0d0b070503060d0605070215151311090406090509011413110a0e0a0906110a050d0e010b150702090105010302 74
    0x280c1e6400d41708802003100c0480c0c84c103080c402c007400400441c0e80c110001c50364007001c14400600014241081c011903802c80311020a07920800198a44180c0c0c0c4512240c4100d411400103452a4200625400c050764940b6141a113100045503140e026402d26191111240d80880420054030b80c03020703c2c0da0243c90399103048008104003840464200380241405680d0392036030380c003040b001c1305000fa015010030b040c1420301019903400a5811000350700c1096482c0942ca407964002600107480021a521401820035100e62000603441000b81005110750540f8001807480454107841c041e5102104065403038041143d00c072402e0144100500644189000a00c1e06d071010000040d03034241d024156804940190000742c5407025008040c04000d450010726191440d20314002d08804902101e4583c104481c20700034024a9042e2094a41e0720b0302c410b420b00c115041030600804900b1480303e00c0750740342c13641c41885c0d454248602c0e240648081100c1c0d076900d128014000c905070181d00c0030741018070400030716070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 315330269 1250 315329019 315329051
    0x207080f06011511030708030a050a0501240504080f060402040f02030709060c0203030d050a0903030c021612080405041b0f14090d06110309030a1d09041403041d060112 74
    0x419a903484010f00c0c43c40820354011500b48945032102c101c0d82c0700010310407007401046400303140301c0c1c50000f2061042daa544020f41003580c0342845690000c0c8070040440c4034610106950b20079009003454001e0900d82d4522055141c084400c0400030990002028002075003864051140c07060710f603520940c03a5050007100100501010b1040504210342e002003402156028404c8604880c025032042c0418104803201a004000c42c003800c82c08680341c00c445015443c00483c0c0812850884100c03003003040e2030156a0081e800d4270740c004071a00c501c1007001003400c1c0d841c0d1054440d80c0b550b0b01b40000004a405002030039501c4030000103028811510100000c44012000b01e6581d8501900d04030019002480d00a02510082661082914000c010051810000005010340600e9035803600024021440364002c481100d050780b0f41c2002d44100014042450580208464881102141d180a60b9400046103842c03036140000315540042003480015a8001214251a800003070100309807070400d900d0217 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 315331519 1250 315330269 315330271
    0x815030d1d0901260a17040e090a02030309120307060c020304060f02010b0a270906050610030209030a0b040c0b0a020d0f0e0d02130b120c0102010c02120d0b130c020c010207080f06 79
    0x2000104103141e00508144040c4001d01c034555001b00a00c284940507058098640c100d40603a981400c0a5400074100500010700d40c2c040030b80280c040c62a2404a005029000340310304020700352840100302c0c0704000796203885208080c5040750301940c0c42c1c50606100820b00103c40440300110380c104a01000142e0b41d240003001200d21000c88440449c4462202565503880842e17480d003820f1614025a0500c01d45800c080c0c40380c036088810001c10070071420150704a000c0c2400c129003682c040000000010030360442181c109000344048200b0035904c2d0341488107584004e103403c005030080d086543c0d54541003c43d60380f12100d2801e003c0c13084105440481d0b03518420a070301901c03545203201c0450941680d507224406100d8040c00802c0a400d050307843c1550342c503202018078019072130f00c1101031219101098110144c1642d0750420702d0080321110b52009000000a800c0c4d2102210011501ca0303402c034490b00024124507005080303403000c46000a4105181540001d0445e00118040344500f44089091 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 315332769 1250 315331519 315331559
    0x30f010b0f0a1a032d04050d0507030504090b120a1103060a0504081c061802041508061c110d0312110406051b0c0307030f0c0f03080a0815030d1d0901 66
    0x241c40b42d860240e25640348070300300c1c00c0c030103041e0f007000c0c03000840c0c5440700030544118010400c0320403003c92032000b00c9e0684130741d0501074002541804240031040d03258102822148005081080c0303402810212401d00030114400c590501300300a00c0791583c1024420141c3c4440008030800062400da190400380b0301c01c5c003802c207551031444101d19450300b05552114001d0040040f08100b03916502c1c414030000d500038001e410404000c1d50001066621030110148141d101506407680b10800d419180c0034085482021a8400101c2c13207401003e490308412a10300500035500c034090468041900412078a011907941d41c1414200000d01071203401c14200e491900f13401d42040240b1101c154001d04240e0a050742540c107006c0e10b4000000d00c81c100c0c5200c601180101459526541d60f1040a880c605a0b48002850408140044940140107100081d80507160414181e0b13a01403690010f803c02d0590011003010403594511500780451041685003028802d0700d94009550404c2c1c034074180c083c40703000c00c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 315334019 1250 315332769 315332819
    0x12160e0f040603050d0c0201110328050f07080414091b16050307060501030c06020706020c010f0309020411030108102f12090c010e0301141b09030f010b0f0a 69
    0x90580952100d920400c000d43e001030507540d06480e000784c020040000e0040503400a81c0144270020700c0d84020080301d5103034000e036070103c2507640f50b058504444100001c1420a020f81401641c94041c11040100005441805d40030b41d150f0400d80b0304065900d00c8003846008010080c10000c0c0100d0301078001081c511070880f0991650300455064050700780c0608024098080441c05100b04a0f280e040f240c1641d20403903442181c0c0c0e072203040899036207407207101d100d005901c5046020069401000b640102c51501d26020070f01401c45d07004501601c90225070041d804d0800070040103403803030512480700d1074009034100380240e00c0c100b10a52041c203802014100c0306142d058002104070081002c0343c1a0300200411b81216280007203401c0d40381c071401c03c5610702180c5030f0131441c0302615061040041e800c05010552006032a50100814501d0b45000060310b03451040044140c1940c0030031141c44c0384500340002182002c4040144100a03900410150084420304024000303007103001f142e40950502155 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 315335269 1250 315334019 315334039
    0x4020a0e04050a110604030507080c0f120a03030504150e0a020a0501020c0109051522080d0e031c09090f0b040c0905180c0d0507020d090807150507020a0503030f12160e 74
    0x4c002080c034442e0b5031000302148915200082d4410000c01c1030407400d0001c851480542c0240400d2184140b00d84609a5264102c400f007140081d0090380302c5504035000309c40c00b150a1100c00c070f603081290700000c0246442d51015480604600d805004400503140a2004e0200d004140c00081c041040d240511440f65441c0581c46800403050010794a09403001c02042e501c0c0031500c40848542c05150168030b500e80a04d030300002182e4081c1e01081c200403070180c018034014200c000e10300c1d40410650103a00070050030708800600c007800d50040c1c2038003509400d0005043c0c240d510400c0116881d503300703d0306100d58400c00300840d9484000e848629180b140365800507542c4c00020079183e05c80c1000d0541e803103181c07100340010307035900081310f4421581503102c0803c800d40324840c043d07840007203115040085441c1140c01e214944a02e02800d019440a000d030303144d281c3c954000a055030807138001d02410800101e180d00c3c01d10781c10040c0b82d4001c4208000042c460300d42540050403149100911402614070321 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 315336519 1250 315335269 315335303
    0x100b0a0b090d0203011e061a071202120318010b030610030b070309020a09061503090c051014030c0c06010b090109061b0c08030a1214040f02060f040b0304020a0e04050a 74
    0x180354200541c021300800ca81d54100b40700c142d00b05001c440800c216454940003180311255502d1610358088030842c0b440c20811107640b00c055024505000c1811801592010703a40b04c1d1010f00690301402700b4220120075030146801e4542118000e404452282d40010107102c2003441080c00030341a0390f000070340b10095940e0490186c0143c5101c02009400c00040342d0002038001459000700240e826041c2c0c1c00c4c80380c5590310f40c210b0a032280d0505c060030110440004011318940b420800405150604040c0101c504030311107207a090b0012038228030007450006910551076800e00c011405491501c1c145810101c20380d0000708809114000c400900c202003203c80514400340d40c9103010030303900030300400da4a0307201c4030707159101d8024084150103c0d508403103495040140d4000c800c218030a40728070034103c0c1ea80303468042000090b0b034401d0380c0103101003028028041d40341d00100064140f01c07107a1640ca00b014414081c80e008240e002200d43c80c880018040024004030f001d02c1d106402903d14421072a5030707 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 315337769 1250 315336519 315336529
    0x606070201050a14030115030b030d1d0a08030310030606051203040905070909090c030b0c0403150903141201060f090b09040e032b0f020a0906030e07051e03100b0a0b09 74
    0x1040c000c81400003000001c2d0000c01f41c005c0e1100311001c0d036414440768150a041c90740d40d0341d17000b400c0800b240721294190314901d4400c02400c150140140a420004e03910380003a4215842501e201d020400300d0780c0c0501c00c1c06030718092140205416280d42031300315000f00c00551603000f64064401d07802d40b90000f1030f0603644170703080c900058a41d14004001c040b4203850914820039031f61000f2900010070000040d10b00500e00241c43c1141e41006850304140a80714480c0020003e0203421814021000f00780d11200e449000942200c070140b001d92005541000d8001d00710b00c03010ba1f0040100202c02506004e060144005c0e030307a101c0d4098402080c0e0011103d07185066009245000300000d007807510901c420000300c25404030301074200108110114074690380340140d100f040f0301c0402080c1c12040820000b031082e44456045400708080e503141f607442e0300020300051407a050100c40030b000d010301206585024031a00c419a0381501c42046203043c414041003500f19240700310326010320301107102800ba44030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 315339019 1250 315337769 315337787
    0x160503041e0c08030307090608130206072303121b041707051228050309061e0d0209010f11070b0703050403060c090f1203020a020402160609050d1101050606070201050a 74
    0x48002d00914490f00c1d1141140c0e250003c5400e4000501e000c2e2001581c03d0007094080d000300303507030120768000f9025038090010307551126030121210038407090100c16161240c490b03403001d054120043c45e501c0d081d000004502c154054015481c2d40000407080102c00700c01b10464044600e40881c90601200c00d1101a0030081154040c40c0c01030098007841090007008141c3c00b80c14201004464415401d80040c03520390306c060f4000605681c410071880819190580290105002c00940c54409100d48c40c010306081e042070044000c11031700402c80d52000c0d038105030b080308910110f00c1d05c1016038840390110307039a0310360602c01c0c1055454001151028107210b882198040c40c1c000005200e40041050000c2c184c11940c4a520280e40c0100e6001c16424051114032040c290903600a281962642d02084004d50100c543c0c25403013400b101d405c5000610502840710568003076070141125600b00350019001041d203141c088240d1b403400c820440c031561248159642c03140c0a20b0710700d031903003007090f411346003025 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 315340269 1250 315339019 315339023
    0x121b0c0a0503090312070b0c0f0f0703020c1806090a0203090c0307030b0610020d1403060d0b19050a0b0a170102120f0717090d210204030c050306160503041e 69
    0xa140d19600070300030004002c0907110825000c542c00d884500724420002e018014004014044201c081400746040d48090000d280b581c00000345032407111541c00342c8551001008801580000c03840305200d1074082d1102c01050f42078418280d030b81c41d22a002420300301c1d000b05a9807000e540480480d040500400c1541c1d02c0c40c2c40a001c6500007504c905200345030450448403148105c0d000030804d2040f501c045046480c10403c0d460f01d040302c49541c0004000c5410007805d840d0840d0624000038041408483c81c2405200d200c4505001140501348081c150b07000103098500660400d07072612081e845944940302250810b030600503d00c0041c11500380a88204500f080204200005104d0740001542545015801e40e441e50300d03407a201c40c501d821442e00111941c200507002a601d0940c0c80e401042c107600c02c84608490140308002400460007240c00c00d030070540d0940d160510500c40c03405c0c100681c0350812150640140780c1c4011a074000c0c01032100510050442070400d0410b60204002950107000517 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 315341519 1250 315340269 315340273
    0x1020a150209061813291305071e050c0a0209100308030711010c020a0309050d0f1b050102070506090904030507051002160201031a0603011203090906080102070b0903121b0c 76
    0x100d081c40d0349440d0800d0032007824030072101c400380c45182c8001361098100d42c06c6840a03151115064103200340310307080d2405103250042915071081c000c120481c03149038443c0300c02e5100c0700070030320040640c8680e800c0020030705418002c00308003908101200244100115904880d825003036078401c00792a00078000355000406090300030040c80301302d03a00031000d00410013080300208480400210100d0380d03460400c10240228103600742c00c0c040c4d810003541d2281c116008400084001010303603211900f84181c51028108051140e50502456a0600081c8010001220b5103820400100009001940082c1c001418403000141000811400340441182d1495001c0219119850301c8800c1c4c040401da070408a001910b44500910075501c0c1c1504980c8414001c4c084070f0460303003860b0040145402d140c03816414090140d5001a13901540d00510f009019040000360325401c0728a4884205c080140010005810078405000d901070715403d080e51200c2d480a02c100b91910400030704101d0301c10031003014118 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 315342769 1250 315341519 315341527
    0x10911160b1b090904020904021215011e0305030f09030a060c020705150a02060105152502041506023a03090203061005010e040b04150915060c0201020a15020906 71
    0x48550028460701c80c90100c00688250b141e02001202e040c407803421142e0780881d200020802604181c1181c59005101408909640600d1360f0341c4c42c40c048503800140440d00c60400140a18504070400c030300340c2c200c14504480c280e0708690300c1c9510b0f40201117200c00c120b000032942c1046030b60104161240c89400100800c584141650029180c1c0480c0c06524050745840c00c0b450b15061201d41190280004c0340c0c0542210f9003003000f0884c01c4c140200390b022450105005500010a0b00c800d0342d41190983c0c42107080b40e60051040c00240c55a07810510a205600c1008000b426000b28045200c100a0000c44400004191810f034148a0403c0f4038202030207101c4404030300c0ba400da07102200c554021012600300c0e5840071100c06085e08140500c40c005014814500c40300d081135089082c4110b8001c0c004aa0380c41a081c0d001044260b030b40c09020169103031903140c65141d00700136400f406007032a07180400700c110030343c1c0000c1c1d610295004000c040d4080e460000705e00c510a03505640510380000c02d0f081d0381d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 315344019 1250 315342769 315342773
    0xd0309092307171003080904050712020c0a1101020703120c051e0d030e010b01051b1c020d0908060408041e09020d0c090b070f140f01140103060e0d0801091116 70
    0x1644040c001d0340f4001c64050004140b405080210740c0084035440307003141d882c0001c040140030141c00c019006500b40980d41d201c2c6800b0380030a0019020b10b25004000b490b88103800d0500c42080b0741d0503100607040d90400941800032030b0009112080160f480d0800448075212490030034a080e030b504040c0d000303074840955000f068800104140182c0300d0140d401f48580184542421b0072144201e00c0c29010420402032040950b00c00d044142c07000200c43c0030355040324a080010b100568680c650380340160004044080482c0e000f0748010054034224009041d0752400d0b45d0381c200a4032490040f00c0c1e680d040c000a0740706000ca0490b9802c06002d20040a540340d6003810300315009403450400c440c0100d081070b5400b00c0c1078400ba5090307403002030b0445980c1120240c2910386a111480715043c00c0564001c544403000004401d0048210700c2518848003009503140d800c00c401103804000b4510510340001c0140e000c0641d002401d030b81528050f050000340a54a030540248078880c116507094541400f0320f01c441 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 315345269 1250 315344019 315344027
    0x3030a110c04021204330b04020c06010303021e030301061b14070b03060411031506090613060c06060b0325020a0b090a030e4002031003020f0d0309092307 68
    0x40161b1107021520180303101c507400b0008070690310710013507980d0b8600d0705402e80c20340007500f001240e43c8028000620301451800214107210f0243c105901580c845000150070408212070485007011201c040c5003103504103400100790b520300c12456094054001d40d0b150611030a10b010b035440f46c031014102c505d0f035580c464090f030b005c0e08225240da128910709031100b020351401404491107441c250204548021041041080603040801e0300764000e2402e00070035105c4403c05160b43d014203155102c0195403103d81c504038082e10090303000110841d00038014000781e8200240301c0300000100c55481030303440c440010100e240c030b20031220140080200409000305450080780f0840c4040c045e985048401c0f04007010310400000d074130001500724460391100c99000400c41c001200004491207250950004125801c0c26030308165064860003002507402c00031460314186034101d202003034a51041090054401402175621482100c40300c82e211040c41028546141d8a00980d1190a04c440d0890400b828020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 315346519 1250 315345269 315345271
    0x140d0506030c01092907122d0f08040821060306060102010e0d031a10260709030605060d0f08070318121211030a1d040b03030a110c040212 61
    0x18001e02072040c5112241d4850043c010695110416000070f1000ba55000317031103100d40200c060b070b02e05800c1c071203840002c0c4840807200d03005e48030b596000c203808503901841c80421301510340480084800822110b60701d810142903181c902182c1000380c2c1d0341e929420949424400c204100c0703411041e00440c03481503685010158000c0f1010f6086070000d9540c54010380c00c807504251f401c0c8995116103001c400803407003074001000c04440351908100b1215004041140390612554400101c0d01558500016507100b40c149841801c111010301141d003032200001d0302e01034131400081e05682d11000040c2098448800c0703500070710b0744a1742e5180b81d41d0341810582002c0c0c000c0e0380124001403034481c0500c86c402150b050141910000342c81580c00d580d1030384d40ca0200c010944490005e11900346c01c00082c1c00070501c050041c09019480701c00c600020785200580b40401c1c90400d51145140c8021100c00d0345002041c1c0701d4200c0d10b41003542081501101451808040c7c1a000f50701600001d24ac10305d04e16124051 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 315347769 1250 315346519 315346531
    0xe06090d14031c090c05060a09050405010b0a02160b04090c05120c1306020303280b13020c0c01050412060902150d090204110909041e020d060e0c030316020d03140d05 73
    0xd00c01403c0c52205050303600303044010b420550422410b1080c3d1030020300815254060b420100d50890b81c0c5e03404642074030070980c088130030954081802051103070140b040d04000c40c4136158110300b00b8100900071249000d14003903040e13050741c0d9000d03107013560340a1021595011404c147c0d9074034501d0b10007640752680d8007806100060100150f0300281880c0000244c0e070040c1d0f4480d06140c0d0442c0c1c1d1200d203084110210325000300142d01c40041028076141e01c2c017220184c000d00c00002d60340308421021249032061441016042080802041207030b800040918072640364010408110b0040500001d0203501079034043c0c1c410070000166100b1841244e6114003810762090301d09001803204500d0818031f82c080c8201181e01314507400e00140009000c4002c410388a100e403107203c0446e0170076401042080c20408000c403032142d61001c5950800d13104005100e0408030440056141840e140454441006040c1c2c00030f02412b11042c50000f014060008165414600803041d42c44081958040001e810140c4003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 315349019 1250 315347769 315347797
    0xc040f0807030516080a08090f0d0303050604060609030309050907020c09160f050a17040c15080402090112031409040225060b010e220e0105040309080601080105070e06090d1403 78
    0xa000079004c1c4c80342c0200c2d4461400f40c00a02c1850311020415407210410981c80300e0341c1c51250709142d5580002c2c41055011b950002160f07d0124107000032680103800007001d00c08054000c0000a511101000030754000742c607030755204e40b074100090b480d0100003414240c0c084401d10030405220705c0c808a44291961a984421a50248500030717100344c4180d4106800240e01d000304101e0402d003445080350000e10039a503c0901030380e01c481d4541c55081480c0484001500b0340c00b07110547c641030038079501404540900c41d04000c0b00c0d5a014018020b804122500030902040d00030315540c55506a0340c201c1c542c20841c084c0088240c90a54488088003422035405e0f03c1c0400c4000c16501c00c60095614803c007030034611086450741c1401031420f100c03503a140d444d00c1e00e41100903c1004c0038000d89010314440c2d01d40701e8210b400c0101a5007044416080035465038542401c00c034402d80c4c420341c1402e03007502c1a40c18940d100c0242020400045801030064035000060b82522441d040000c0205461209081 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 315350269 1250 315349019 315349033
    0x1c03110409052e0f05102f0105060603090d081807060c0605132a1212021203040b0402040c1205010e160e06040e10090906091203090512030c040f08070305 68
    0x310440d42406140a0004c12080d80e10003482942007224222a9940311410140ba20718415400221090f00c00c4003440311000c0f00c8440b8070b020480c04d00a03039811581c2142d03054203602c3d0490040b5500c102500b440010006280c000c01d580e10b00125100c00c1064948040d11000c2d900d85001408a00c082c52045034a2031601d000070f040d528034102e600c203440d58400c0a03a108940c02d0403040c040285002c102e0340c40562101c0c40000c21000110a04100c680319100180344d4018000c006818108104804442c42c44108100300010352842a081d602c183e04950024140401e550b00716440701c406041ca440d40f525081c00030500025001c10640310700c1e18105111035001503014100c03030034010360b1038607034101d2801d000c240011a0b5410f9001d511102003582110700c15550742d845016207040300b1064400b2662840c8a40c180000c08ca449004504141418001c2c0e54a42c1e40703869448641c00d04c482c4a912012003c15801c50010341118010803910250400f0a510f074452103460748440d200031907507841015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 315351519 1250 315350269 315350341
    0x106020a14060411010305090c030304030609020a061b0f06020408060901240602030706051819060501090203040b0610051324030e03030a0c051902060a0506031c0311040905 76
    0xe01c840c0318984c410a00c0110f42d08100040d80906400f0b012003a5a024249466400d5141040588011405940d000c00e03038000c1c90040c00f802a00607000001004844580080c030219540340001c4d48640c40040d1030054181414050000e000d19080720000b80602d1060268007141500b05001b41282200d9105c0c0001403e0b80301e01490007117124401c05030f0020b100140109070241e200300d500017044003d02400c41c00a644850401d400103118014280c1c60b100614188641c07840b034079000d00140801140356040586802004410003441e061040d81400c0c0004240c511400589140d00c4010300e8028030f003901c0d0809440450740b18940050b0b40c005c00104815894072a00858480b0b1981d800a5072440d2a10780782c40010b0007025032400107206041140f102c00300e2100c9101150302956502421450070810200313402e5a0020306120700c681d001c01b8116516441051813107040741b090f42400079243e25130b091110568051580269022843c20b420081c3d0700c1c0c1c1d601541c003503040b035500d81c0500f880408 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 315352769 1250 315351519 315351523
    0x503010209280807030c140418080a140c0a02090c0708090d0503130902032703030c1804020301092313120c06150501020c010905090c210106020a14 65
    0x65000781c0e0010107260858040004403812560041c04040440718140e182c0c44280d14088045c1d00131500c00300e0143d41041003a0503074409404061040b18280000b6485a0320381340c1c4603884c480003038082d00000809030b03520703030280519010482c90340e400c15817140004180c240d1544460101a030003007804100040b020040300e0101c1d080d4560140d102810100150103010f24a483c071001203031148020808807295685040711036008084c90040941c1d40e10701044400d980490b134904441c2d024000229411003800040252507002c502d014001b030701e82c040d40d201c5180d041189081180c02c10310000c0013140700481030b040240c0384204110210010001e003c040b0b040d15600f241d103200c00d0a075900e20f00000030060a881e441c003c0139807031b00544030201c1c2d8880c4070031540220800c07160402e00800410803560148084000f205003420700034005440e150104000c288010101c1940100008400903000d9482c2581709140152018120301c56840e8000030750348110b40e840c280d806504082c803070b401940700 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 315354019 1250 315352769 315352777
    0x80f070f0e10230304080708031003152a0c080904060b04080109050606180c0904090b0702010b0f03070f0e040606230a0b04060c03030504020303160308060916020303041502070204020a051305030102 87
    0x80001c46a2401f445600d44003601d400107440c4000702e48030701300c0000c00301e0015045410382016442000a8800c0c2c0754480040485441d940c0d0034000d250041e541104a80002d115481150000d02459030b504048000600070000c43c0c010403039144002c2004036550030150720000946216204449441e150041008101d035801c9003090180c011400c00900060761070350280c01401c01c003a201203440215030303031500c2c20300504440210040c1e40d41c03c00b2941c83d10f40709040c0d2a5101c2d0a9024040007030a1207484201d10480c0e00441403e501c6030b1001c18100030380e6510580c005c154008000d41d45a460160310358158150240c0c80d0310078240024045032032040c4000300d400712000e940b2402c40840443e03400f038014050042082e6490300060005401c6903d000d41040b503500d12070340d50360180f4913002003040320495010f4001e20125412004001c51150000100c3c2d07001038000e2905038458840050a40c080d100b2040003d420034004030f03c00c3c10705504403000d001d84061001d009920700351201c0900d0300700c3c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 315355269 1250 315354019 315354023
    0x140c01021905030c040909110a080a02010e09060d030e0f151305030316021c0503030109060608130c05091305010f020912120a0302160819080106080f070f0e10230304 73
    0x184c2004200310041080e0302c1516414410903850700c8442129001401c2409030303602c15005c0e500200c13480c0c4c04569100f0807100084c00f04464010813424004081024821100350040030300c02c014190803081e545011200c080380d90020308211082080100304d0b2011b401c400007a800300c07209490301007421314001c03081e10380b02c031031380e41c041d140c4900784da000c0101e02d55510380440126074850203c0408580f060009502071301100c180442d030b42d0714001005060020051000030b1030bc0c044205031001410382051541110340803114126245ca035620010070550040c1c000038100c9d840c000700504148500c1d0007900580c0380841c5d480003c1c52100454680711441e1b50300c3c0c0c00c0150707400c002c0c0f42d6055020b5400f500503000ca031100f5108840d40b9588100c880d600c002040b030415800d4440074403039594400b4059001d4440e034640b04420341800038007004650b0700a440d05040c01242ca800c040c1081c40745826241044e402040d507410300c500f20801400208400c04218480c8000c1848080040e00d0780088a000326 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 315356519 1250 315355269 315355291
    0x1d0a121a0f07021b0f18011a04030b0103020f01050d090c030b07031e02161b031b1802090d0203011e060b12160c0203070b03060f180a0507140c0102190503 68
    0x9078540041d0301c00c2000c00c03c2181c0c040c41c8108034401580b11034030220b5494816810031b10301d075414502d0b030b124401144040c2142c0000c08000600015038811030b1281100e6041d62000c900700100801601d403030003080300040d1030510344819042881106040750b0122401507400c00f0140d241d0703032401c43c00e4443e15000881c1000d500d4940c0c2141c45d040d94002c2406a001c42050407840c0a80e6a4011344002a400d209544050f40a03047c010b020f010b0062411408d103421003d02d203945000b05429080280e21184541c895003c6103000d6151144561303180820340c0103000f08280a14001c54449410070100c802803401e140c81030205128110030100c8001c01568074200649590b19001c145a4010802080b002c00207403c0c503000050318100048070162a40d82070031626442d0003414000003200b0400c86901c02c0c042c0c10760807080303d400e4600507500241130210100b5039a8403000309880403a40350301c10010548002030341001b00d000642c05403c205c0d4980c81c0c0d0420030081184105c6907400b040c0c869400342 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 315357769 1250 315356519 315356533
    0xa02120f0c04050d05010501080105090f120708040b03070c0302010c08071b02040e031303170304030c0f020301090b011d011d06061815190305071d0a121a0f0702 71
    0x20003640c0c90260740c002a0080707150b1500782c850001c1140c00d50381500807240b984d122001801055400e01900d948030b09110b000300b290241160610b566140505500b41c0c6000b0001419800d2225a004031000382c038074003202e1652814040d070002e01217518428194019403a0809081a00d03104e011044d0143c800c60380ca01404c940a400b0b001952050031000302da01a0765005400c94031001803001d4026040415030850b8000d20b10700744894026208070045852050401c104800070342c0050b54824410741040804c440390200303201083c01011440e070081c15000400d0000284400c415002c00d105030750f007640810040c2da0720003a560b86c0e01f03c0008191456003241c40004c0081c281100a42004e410307105240d0900c90344070010555400e5482e003824010790000480c000d0503407880f4441c8196403030f0740c03408120701c1c80c00040c020110401c010366096440d48040d0980f41d103503501c100d2400a000d001003407840442c020b03c3c0c1083e5100c400d800b03003540c003028100044c2031407000714100f074454442500074082d1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 315359019 1250 315357769 315357781
    0x317130c0320010e0303180d020a0303090317210a02121609050405160503090a06050108030304020a080f0a081804020d140601020601060c02010804020a0b07060e06060301090c05121510030204050a0212 88
    0xc10091f84120302d40103000c20b40743e000943e8800781e00c80000c50003512240388150440c100801c001e88060501c11040d0f000b046481e1100d240d03044d001650f10100c16054009403184105000607120703903c040d0404000d14405e002c2603c003642039030302040216883d151400741e6604240300903118120b5100124080c00182044100c4c043d400035a40f10342c04205403502004540d498104642e006e82040302e5030381c0044100021410308510314000b034403100c0b00401081d0b503040341c13217a138a0044400041040c1c001240e185602071104020381e5803035100400654950300f0810f040390042c0b1400d10f10305030801c0254045403495001141160590310385a0b6002d004034481d400541e5003440142089800c0b050400d40090400c5641c0c02410856220f0400401e1401d03525000c9490010701500c075510070b0b407400c0c80c4200041c400c541a081218000e0307034680200b1310050002401c2041000d40300c40a01000320400c86007402015107a030650384211420010364484902032412030050b0307640318103422170701004100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 315360269 1250 315359019 315359047
    0x7050f0609010f0e03191701090b011202180d0c17010e0712020a0605090a0f080105040201020f01110a0809030d0c1106070c080306060d091704050a120317130c0320010e0303 76
    0x48951b400e81800d0b48021266090101d040c00241c0c842c444007691021010b03013660f0b1000e0340030781d8030751401420b5080c0340c0310180345407003540c03914002d07441260f0007410201002004011103004007027030403440d000c6a01640195003e0042081514001c1c05081000300e8103500f94054804500c1c0c01070290b02e07040e410070304140c6441c3d1180e03403d1070f803114510390b002a003500100821400362800c107002103101d00b4284006450007509c00d803041140d0341805503030f078024070014003500c00010140ca441d0390780c7e8079001030007070851060f030401c0c824043c1071007844031045400c018000240003503d02203a485644460044400344122000141102010404600c45203014400341c016115210000251114030b0703a202d0f43c80c81b1040c0a07941b2003c0f80490200901d20345542584010102e40400300c00741500c1d6500100b898110550281c803000883c408110442040300090103d96880314000004944901702003101200120002038021402c003002c80c074551085040d82c00c03003403000d40114100b49500708106 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 315361519 1250 315360269 315360307
    0xc03160614040803131e05010807050d18030905091e0a0f150e01090c110c12070b070c0e090307050d05030613020d05040c0e07050a0e0607050f0609010f0e03 69
    0x101004003400085001c200510080445c0d1884012501800d40303007003001d542921985511410031004440d0802560340c201c50641d900544506d0090b0756440d241003040b00804110301111850541c00b0801c5041640204400703094410807980200c0c03980d00c0003007400704890440380311003403640080c001c25401d61842d08001209941ca000c081440054ad15240c14103407007030b500084260030000010400001240300e24880d04003113240c6a03542c030b800148040d9850340791122080c080c0d00c4007a2600182d034801d100a102500301a516076075a0300a07410041104581d0b40150090b07090144040351030114000100c5039615400809415001c4900001766500e40009020070342100e82e450480c10200c44500c02841029400b580008245c201400c00501c01845500210741d40d000c01010300801035000400c0c0c404c90780051074031ba102e00105201003031080c01501c40080451040b40c500428503500800c90900c11104200200549000d01c0d4943e410b44980c103011840c290410044e01410055506d981 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 315362769 1250 315361519 315361547
    0x40c06050a0309050f013305060714060114010e0907120e0c0d0302100501050405041a07020a1a060906030d0c031b020a0e010626010e04171306020c031606 68
    0x8a6100b41d807215070400124805140c0035955894a05002e1450b40042200307010b02e00c41340c046580f03401144480c0c47e0540f030203401d124400205080003007015070340c061402d00c01c40750107944255941f884d00f0a00d00a030700400c0360101d0b230140c0b514030490400ea840ca603c150b8165440c07942658204d010000206150024800c1c82d0084442e015100d440b10341c50681a1072081d0b0052403d002183d43ca10308448041c0c020b40e00c11707400c03d41400003050003084189403880c0c20191960080d11812001d9240400d0100020880310090043e40c141c6085000e00a02c914000d0302d00d84465a9000205a1100e58918551012440508031400824400c0070f42c0380c901c0e000c00d0300800c2c10b00c0c4d10750000340719060640c1c4a070220f0000800144142c2d41e0011622150407004250b06510408100c0042000b507814000c05005940c4a00003030b0038490007284000361003401f05949550b1b100351840001400106008820240c4280b8040c0e00c51818005000100240e00d11840c45041d410001c013110b01c0f81c464852 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 315364019 1250 315362769 315362771
    0x912030801030206090a150f03110c0a12050403050a0f1407150507020307030c08030c30032a130509040b01030303090c08030f1804090c0603050c0705060405150f040c06050a03 77
    0xc003141f01a070102d06d0003a0311040391505100310b9603081005098074003600c802d43d03c07003500f8800d80300e14000c0020124041940b1034081010b01d0b10414003260301c1d00035a440900203200e400820020300c920018103202e45406203000111941c00c800c1100e9480e84a8401e0301c159081040c80401003074442c00140c03c6a601c024191000c443d540d499410310845560850703105500000760000c2e040008004103071000c2903074035035602401710003c2c0054004540400d080c000c18030000000f0340718980d1142c08288446140e5841c90304035a031807100a0983c01039032040290116000340458075240009803588504e5016070b50007980d07070a643d0103c2c09082d80035400c0320620028040825440424030243c020038800a0f40581c1720001c400c0000e0f00b03c81c1c0942000d0080e881c2058406c040b0322141101c0b01a200310342004550b640302c2850801300c0d4880c00c400079065008038024001004000304455070005054004100b03185c80710809121801c07019100107050801010b41000b01c203010300c0c050120f1030080c0c10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 315365269 1250 315364019 315364039
    0xb030106170f2802060d06150f030605030111030a0e010b0d05010b040501051804030e01020c0a06080405060604060810050613091101081f060e060f1207091203080103020609 76
    0x88030100700c240c02410158075040040144510901000151900610420703030252182076492146594010008042d024141c0060000030072407903600b104004050100f03100c1c0445c0b18441d0000c14000c40c3d4031100c8002810000001072625050064840a107028800d460de15100c9c1010b0000400c003804103440103540701c140b8081c0c2036594040000b242801040007207040a400e204100480e40141c02451156500307250420700d661540000540c040e9150030006c13080010320f40180c0c070301010382c810240e011203142001300303029501c4240c01d4000c1c0d100314100e0748e05840340c43c04c20081c0c805c80c0c0280161a440014a461141031641046030441005000796125032800c107030f00d205540d180d103020349060000281200565034480c2d42e0301e5006100d40514585040c001c0300e41034070300341c05118000410610000078045540d42c00111241640d1503081155100807042141c401c11100b01d940d080032600044000400e04c1d01c0801460203070703525680358416070303085908018158201c1159541c0010200c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 315366519 1250 315365269 315365279
    0xe030c0603010b041508011a07020d0227060603010b090d0807060501030b160f0f0f09051e1207030201020a08032d1803042102060c0d050307110f100b030106 69
    0x118040c0c104266000d41d034900300170028200007020802d000c01c2003209401086440507002803095900c078125030040e070ba922507000140c801c54603102c001e0350054007000b404552041c180c80d1407904401c00d605008045d542d400400005001c05d103e00e500c22501004180c60f24031707048034100a40742c4075804440c1031840b2a1104c4040724400d0f00112220004903081c000c0c00340e030581544070180410303e403071001c41d0305101000b0308400c071103140c040a00803140400d0b02e04500581300240030f044007510101c0c11001e02c0b20b07003411103c00c40400c1c1d4000c003d40a1181000003022956000390798042e0001c04100f09290f49640c106c0d031004003c4030540080e4000d8580d981003043c00c0c404180c10714641daa5817802d0000d03c3c04102c0401e214080c02d00d610401007001a0b041e0803144d24070f8004565584c58005043e40085004c2e8403070b03040d248006015801480300c3c203607089009580a1946540d031010148030303150300c032562400f104007250742d150302c045200b05440b00990050381d201c55001d4004610716170f4034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 315367769 1250 315366519 315366529
    0x302030d0f140a0c0e0f04090f060c0f020303011a090604050409050714010302130b0903012403111e04050a0e010c0929040314011407110706050c07060e030c 69
    0x3502424196a1035145044401118011254000c105600f0800140000c0440600511820010300d4020115803010308210f699547c07040c2d10058120300303000300300500d5282c88001401070000180c003103424600300307481c0e040c8000705480c182c51a12400ca2004034000719800055040800e071107038003d50070400481e85446038090002118403c0c0003d050440c1030501c1c0c1d00b21442c1c0c4088040c10140306100420301002e07608000b004075014107450b15a1810401d0119000d8400701c0c01d403808041d01000d0802ca900e80e0701100030210b0703016960030741c25580d400e800c106081360503182c00050904d8039203811842d440c01e540921f402c81d0b1521400a04041d41c4450705d82510504d0100e100440c203040e40402c006a4240b1000c3c0e22140400c1c0c01044070b0031012000700c2180511f000282c5503a0b21555858940e5000754001c507000c1e82d52800342201880c0c507100003000402c0140307080ca050700940c00001103860240c41510180100e01c0060320b5001c3c1042c030200e070300700355401d0304541c18030039001c82984585071 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 315369019 1250 315367769 315367781
    0x70320070f060f080604022505010b12060702010b0315040204151a0a1d01080c180a0e390c030d0510060f020c030309060714060901050601020f07080a0b040302030d 72
    0x25a1103d039240c0c110100f000d40241c0c0000c03c1903014500402c8110030500a6294001d030350007800c209401805c4242c200709006081ca142000e400c00c1c1001c0c072420201000041d0188030b20301540c003d04c041604101859264103c105c3c030b10101ca031880010800628007500700403545940d2480704101c040c0e840303202c1c02c50440100303c01c0760003000004100031003d030300000c074594503e0180408501c1203c1f46000038801e2200600e25010402d005c02c14a81e1000c40c0f841c1d00021200041c14035041c2c03520b49a41410151013540d040e41d060b51001c1807090080780060829401c80011240318001403801da012140c01d620500c0401058002049000342804061040c14020102600742e070490a04111020380b03030040e0750100d401594095900051280e500001301d40c0201c4040d11400d07200e0091386084404000f2049aa032621301804080181d02c2c58150320003071254001368219001e41c00d24501158851b140e42c0203501c0796800107190381c0045030310030b4011500301d40b091040b0b0b0316013854181d4140c11948 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 315370269 1250 315369019 315369029
    0x31908031608101703040305120d05071e0806010309020423060105130510030605060c0115050a2603130303050405040f02030708180127020a0b070320070f 68
    0x1004014490010100090103500e1001401c203401d0a00f04010301c1c841080381413188001088500102d10700b10724040c400d80300116807041c111414423181e808a403a40d41c01141d03050034050310341000540c44a116207500c0a4201c1c0316041c00840e5500c880c2c040b628840002e1005041c075454a007648016102c034400e51941711440020382c0040c01c20f9004140c501c00d8094096070420806000014184080a04800071903104444002c2d100c003c040e4182c0c05000c2940c00660f0244001c04c03107085418040d000048614800c0d00c0094103640c66808000d031000c01400782e0149200315030508115815a058140001e403e4101140e0401c0d510848a0108409540046002540201d07042040b820f16001d01500d090140c4015800d628002c6801052060010032500d11724002c0449880d040740290300c02500c0c52407c24001081c183e04000401c14204008000c0f4011100c0c0540051022240000ea030b864075415650901030120f01921080a40e415042c0d0041c0c502840b540001c03115014406400102 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 315371519 1250 315370269 315370283
    0x405040201020c0d0f0623130519140f01110412021915020c06190819060803091e0102150406020f0711030607020106050a1a0408030307030209090a09030507110319 72
    0x75040781b41c440d0a94008009070322138544200d00c2041d40c50074007198160700500101c0c0817541860f16040103032034128802d203481e4071030140c0c900706014410202c9400c0701c840d0101040b1a4000030300c100142c22940c405068040d904010b010600c29950f0035030808c004c0c280000d15110414680134152560480b00e035100c40d03a120325400100340f00a0301880140101c5d0b80c22282203090001114608003004001c085c0071081001c00000503240001903900b002203065004c07010440140c45200c0e03541d0700c0d8001076001d449018501c03490201664030f088556442c2e041030b40a48101291802a401380c044003900440c0c0c0d40d0b80910940c1c4a01c0704140141045a00908050142c0d425003818517003410000fa04d100216414120300303110b543c580c181120304507480790440068070750184000c1c000a0003250032005d40c0d40000018040c006074150060180580100c81010458550340c0081007241c01c02440100407030000e00c4054040341e1110641d0a1248001e42595540801d08c50410180c40c0c152004031142 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 315372769 1250 315371519 315371543
    0x20301020f130e0f04030f050d0c0306080709110a0c020105120705130b0711060c0f060412201f020708030a0e0106140114030603070513020307120b0f0405040201020c0d 74
    0xb42241040410007002c03000000c1490f803c1c250072030b105504006101400f40010400c052a85900c1181100d0840c424880e0400461503000c000401801440c800e01006116081c00481c5d00c0002e0f100d42c040e400b545000f41d81c41c00307082c05030030366245100b90030603410302009101c805041a4860280351144501ea0780f119640c9032019254011300303d968000001c075401c1400310400244185a1030503100034203d81071600c8070060700c1140e01d025444107014030140610814030042040000c03101c440c400864541c980900c205101d00f0000c0146042c0b0341d113495101401c407100a60703c40200c2045000c4002c005807800d4030540321200a54030688420103900e54607060040307108800e02c81c2101401003162803064507000c0c08002041030034580c900408020001004c241144c0d0f041003079a00801c40640529200b0000c4040c000003034004540c1200860b41c4413505601284091081c680c500c4c0009020a00b000f040000340001000c00030000c0f4154071811610113460349e00c19038240c03a6180301c5d414208032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 315374019 1250 315372769 315372787
    0x20f1b120309060f160f030b12010906050f060402031e13081b010c02060907052106010611010e0115090c0e2112030114090a090b0c03061903032a020301020f 69
    0x64075100908500c045060100c0c15501d556100c01d22825522251802284040007800027510703c2c240058580c25541ca09a40c0c4803c018980c0c100300d22030480d805000446130f40b000203100507072008039414079032a84811115580386c4005030b1714035040140030f0004d1448082590750305140f07900070382c4040c801d00c2022030107000c250024010700a00c45070a10150400d410300d2030140c1d60f2843c0500501e4491054400c0c000030200c0700a9145400f0841101102c0455942d1100500401016940c001195080200000040d0814080c0740111402d040310942143e14091008006010800001c03080080c80005100ca0750346240030146d00300703010651850446401400c035403603c01140c0c1700304004174017071004006518845115111901c401d60f2102c07050390301e19031110300134290020020903401c0306105202c48000100040d43c89901c060b1056a0300d01c48200d003144400c0c0140c03200400003542c0e8101f850a9140420400e102c0b04940241d10402d00041d90029080ea00680b0f40f0b028402c0e004156202 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 315375269 1250 315374019 315374041
    0x30b010509180d0302090f040c030903110c0a05041107050f030406110105060d020111120f0304020405010e091e1609020a030c0c050a1704030b090a0302010e01020f1b12030906 77
    0x141050b240703010b49640a40d04002c264940401860100505a0200e8548215200c00040126000b0300810412900910078805070041240b590144d000611410b103610090500088000c8107400080074075410524003810000a021a010002001001807083e40005202040a80c101708640e0018680300c5060500c010000c06448038101c0c400d1b8100800d003c901e0710750312060150b0980a2805c50740035540900c0715407410310b549080b4207040700d0008010151003402005940105d00c00c82d030034007040e40e903401001c0c1c00403000e0b01c00a02d03a03080301c40e40710f2101c13054501e00e1006161410664001c0d11664188000c11a042e0b40650101500051407405950b454401c82d1405102410aa804e00f44071f81ca0303144c2d841800400050008141d0710f0b0000140c07452a0a540c025680f1403c0207042e850704564040e00d440c840b403002c80266081c00208009130b1018000d0b41c1c06002524100b90411b021010750081c2143e030080c441240780115400a003054007031000035840f452503540200350900709900442 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 315376519 1250 315375269 315375271
    0x310090203040b1f1d0612060f06010314010b030a0e010608030c010f0b04110a080703110c010207060c08060f060f0403060213062304090b0109080f0109060501122409050106030b010509 81
    0xc5100200c4d6420302004d90307183c07024003a58600303072084000d030f603114804038100d1141015214224858a0100135500c2c581c0703003003d4804c040030f0760140504150401c0c0425a42c0083c080c41c3c90100d01480010b4407114580e0002c0021542c410000c108039a503441450b0031940a65140d6603140d455071194a00f241003405078000401082d50100308905500503500524040c00d40c00e80c040042240115040920941041030740b80b200d030702c04507515800098250300039800800101c1c0e5060404044034649230060240f24800c10015041c144500000c204200040e40114064401400144004008100c00f4400350042101d1610803814240c200030021f03106c40b11524000c40c0d4a40040f6241259600c0c0b01c040d80c04490300210040342000c41100141e56003c425000300c101881400c00004401030150004480540140d1040107940d80380c40507001c030f0740703038903140035001c4000784c80b04465242e2043c01e50900c81100c801c3c00101500159640c0f0b003910483e90050328440e50410040c402880c00ba2045 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 315377769 1250 315376519 315376561
    0xc0a0b070e190e010b0307032318070602060a110d06062304080a0308092e0c0c050c010516080c030a0909181e050106080d2606060310090203040b 64
    0x103041e05600c1e03c002c0c045520014000c40790748590103c08209058081d4110f1f400701603202c2c0e104189020407100301442c44a08885064000b00322264a000c0781d00041942d8041d5102d503400b400d82c60703440c401000302a0101c050030748902c4604021460100c183ea205160250040341c0e1400070688502c0324494055035801682e03902d40000300010400d210700050780d03520059050a109900d40d450302880c5040004140d80d4400e041c1044200980c4503c40e603030038101001840300104415102104201c1c2c90b171100c03240c020843d9201085a9000d503004401078001c0101ca24481c0603d003103a135450519640090b89090780315800400c032224465004041d02c1d029182000f01042091400310a0200c03280b00c401c0d001e0086103040d41240e00302200c4804031180342c1d8100000f408010b07a100d1001e40c0e601560000200080d0180c24005420f8056550581020800502d121581c1d02d9260810075160700140030707107003000074042000885c0c01c03190000c0c510590280c82000790700d207040c94070744641034407600d90 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 315379019 1250 315377769 315377809
    0x5010206070215040609330603050a020d05011b030209090c1c09111c0506060a06081b070f05010903020c01081027050405070305100203040c09020c0a0b070e 69
    0x100440c0741d5000070110245041009001041e0b00c503402e211004011200740030300164210081c101e10740500164840091044410700c0c1402d125104c070420482d10b060200400542000a43c1c0001d45048040204040d0082000003a0310131007044658000001082d6040400d401003124482d51900b5100700d5840a1a0486a840d0078144920258025812840303141d5250383c0e9400441885121803018005030806080010540150315a00c100070f05080000c8034548100da000441c10304281c1c40c0041154407a44407401540c03600929000f03840030304042d240d150003082c0700701004100e0074403803042d40034000c10000616101c0780c00e0007404e20418a81e450f06002490080c0581060001d007614200c4001922200410031300c1c00c854020014450040700c800ca0820060102384030001c00d5820850b8403883c01c807070090304a01d904005a01003220054403007850802d00b008849160b400502a41d44d40200b80d500300401546c03101d11805060b14603034006203088050001078102070400001000260340c2c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 315380269 1250 315379019 315379021
    0x7140f0d050706120b100c1a0711071401020a0201120b1504150309020f0409020d1a0702072c090c030607020f0d030603020d080f0d021815090904030e030a05070f080705010206 77
    0x10100301204404480b10b0708020707c81d1008424050f50044084620440d418888014100600c009090302c0c041c0d41c149045028028000540d00e003c80c2002c020208103030090294116a074006550001d60a44081480741d15212003030515941c8414552882240038415900c2e5400d0100d02450268400e013048107140c60212048003680e07403d549164414011200441c0300d00b081d20208400455044004003005004400e039001100d00380d500600c150807580c2150145030385c2d0035400360103030036002182941003090600317584500003000c2a9944400c51008442c450340404010a1600e141180c140006030401d90084104180074021220040202d1500340141800c6030000b41c00031803102c1d00100f20780130003d05800081d83c1038013036511000d9000011901c4850040000b4414241c000c0306611404a0322188020500248140c542c2100041c0c1100f01ca9910b0780d0341a42d500f00e90260059151040841080002c0c00801c03800c005041145003100c45180341046503454060a03411060654000c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 315381519 1250 315380269 315380291
    0x70e0d031403090106090207150c02160b0307090e04060b0a1d01092c031e0c0a0b06010e0a080c090705070506070e0a03020a0608101707140f0d05070612 67
    0x1d40780c140c918898a025079903c1d1581c3d900c0500604180d44580e140c2d0380007041038014419080d0800c0d5642d11f200000703205401d19100e04070707211190b400c00301c0350300381010005004113074584014540c008840d080001c203c948510842410f4501110201d0f1410745031b85892440e800d00d52184d030010714a0280c2100b48007001d80803c00780700340502550012a55501129249a00904650555030031850712001451192426031ba1030340d11582100704000701c0400c2c4110a04414400c0715041c100c0c07400079241c1c4488030354400b144420064078a90411945010445681d9036403550f81008104203801030011103800803d10211540c010500700510500303000c910040341000c02c4540d40000c4a01d4140ca0f04510b900000705d0103505600045c0d0011b96000e40800e100d5000040140201c009914100d015030b50b49420484603d207030005071805030880b45082102c460408101ca40841e002000c3d81d40e1001c00b1004107810f44c10f00f00081d96158080c08040046c00e411458a00103860f44110602616500d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 315382769 1250 315381519 315381527
    0x5241621031b08040501150602070e0603120d050403020a0804090e01060509070225090606030204061806020c0d02060d0c020c130c1e020a06060e0a0e01060e0a0213031a070e0d03 78
    0x408411000d00c10300800213070800a0070b500c0741600c2c0c1d00c0880c541c6012915454020b51310b825602420307111000f0750012800d01d20700090340c5c002440e03100102614000380302001901404000d44101d00b50311425260000007041e082c0500b01a24a0b07041c0007034040c1110100c1030039034080c3d034440c5001e03200d40d0b8180a003140c0d011681062044d0281031580c0081d40c82c00d8160b007441410760000c41443d1130018045600d0b0380c5500240121622130b90b6198800075100001030300d0030311501c07440c80980d1101018031182d0400d0420600e00d9800248554280380032a40d00c1d20503a00c4051881005800540311320300c03541341414010207410640030381084982e401c0d0b90040d11842c0c0200301c211003601904011540b50f03208010f503507035841c1e02c82400e1211950f61000c0b641d88003001c0d20345015140c1090008860441c0c144900000c40b800c3d2103000c840b607241e11085200030750242110800c0d000c45c1c08804804a1218001c1d591075184041c08503440e07140c0312000414074492070b8103c034400c805818070600446d80c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 315384019 1250 315382769 315382811
    0x1060905100306020913091101142a0a0f0b0709061119151a0a06180b070602070212150f040503030a051012030207080105010e010524162103 62
    0xf001c0401692090042c0014030a40050900d4941c03181c103112101041042c401c511501914003070f2910890300034404440c18050054280f034086408813846000c1241001100400700002e441c0d040d00e00c6550142c86040c00300032070300c174213a40c51000321091000055000c50b85100410f0300346000f1021000c2100099141c01480070f940e040d0201c0100d040b0188200c5507540c0a001518032020009510411207019681b11401d500780d2050150b06400141140203681504c0b402c4100c2042180c46805c1071400703401c40d00804000e5980750703401d11416005803078405400302070280305002032400c024040a503480350200200661002c8454006001c00140008240e0350001020030000c80c1594540c059002c61200c0c9610480e50f001c41d07010880281900411500c0a44410300c0003484280cae2103440c002c01030682032184a400180c0c0b404a0701c0b0010580500c0200e448000301c030203103840c245402d41d1104500010096502203401840b450900c1d155081c3c2d907000ca041030505003d404503180c500340c20104 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 315385269 1250 315384019 315384023
    0x201020c1e1504020f09150306151c0804090e0f0105160c020603060d0c060521011202010516080a030b0f0103140a1505040c080f0a050907230d030201020a02010609051003 75
    0x1080d90110b411551600045203107017401400e240220b18100c0c03402c0240700301280d821400b03801264049030006201c1140e655080380041c08540201002e2408034004c3c40b4030120607912051f06003c0400e0b100c0360b500445c2c0c80c45812000500040f0f41c107031890760131034002608041880b20746041b401c02d003a0300010896203d036012580151280d4072880803920310000c0c5000141040c0b2116408903030079400c50043d250118980044510841d6028408104254207003d01c1c101201e802146200545c824002043c0b01903200f0074420906106940d501025009080e00c1004203488549164086c02c100c0320b00d0852810910b01408150002c0f2005000b020300035054100c0142ca5a01201d034100d03030004a200140390142040001d064044e500919151054400540340a01c60300801e44661b00760051a00504080019100d400d180c2600300b2058003c41c01180e0042880c94142e851036905c28a400003c01d00030b030005a550030000c14001d003100c1040e08007481d010301e00000d01070b000450141c1e60054070303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 315386519 1250 315385269 315385303
    0x3091202033c0106060e01090e0a02030403020a15090b06040507090509070302040503060a06031103030a050a03150504090b090d0f0e12030f07060e061b030f0a0b0604060201020c1e 79
    0x100c1d880004000c0b00c8400d0522903840951002c801da101c541544110201c07001a514111950f1003400112110348642c400c45408004007400318002d410140c1c01140c01c94840d00442c0c07040c410030b40d200e4101d6055200d034900031640c0d0301e4102c414407141d60121b03070f48040c1c01c0781d0400440c1b60401c00a0b040711540e0148a004454201c0026907075400fa6040783c0c060000281200c540c0d14220703c0743e1014003502d0004a6900c1410410102642400030a540512400d0307111541020743c010700480041400c40c141080c0510038070701c0001c0b140c807584205203d0310700480c2c2d1aa43c0d49000c40481d494410001c2d40d9404000c882e610f00c07084180e000308400d00c0610202c1d0441194154045a2880e60181e041a0800c11170300040c000100000c1d64801c250010300e15096400da6aa24140d04900010f400346148202004000298158801d14000c607800041e46400080e141c2d64580411140c1d040341d0400000b5030b600203003810402c1000c004104060703d20351042d40404480c0b6000d141c442171140740d209948 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 315387769 1250 315386519 315386563
    0x5160506160c1a10050303070605060a0501050f0d23090303041b21060e0706210b060706090f0803090102071e0210140d1104030303180c05100207030b0403030203040309120203 77
    0xb00c03135100540c0020003000b001c49403121541d08200380201025206644242802d16001075654041d03800d441071a50000c40080c1040c2d4103100c54005004642d007a50280c44448040611360103c902907d80644844401182c80e8503051400c1ca00990030040c0d081000075a0315020042c62244800042180a003807961051001030340c5041400303400d05003000c0416004032a030120b002c5d41c4c001c040b1001e4400070261111a0b83d9403540c0c00e0100d48103003050503006001000b00300040303a01a00043e82c010310500c0661104001070702c3d49a0303250400c2d106c0040994000981c1e400748800c40d01c400d03e2130002c0b0148001561102d500103507040d20520900e10034800c01d08480740340c1e2403c40080c0c80201d69840c006104200c103003400241d031030f0301c90301040300401c0c41c0c84848140c00c2402c80c078030f2444a03445026111054240010080800c014415000031445040740c0400042e14401826028038480e03100541c4900b40351234060140811904070300f0791541e8501c2d8000160b900016102d0040c1d420003107030f05103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 315389019 1250 315387769 315387781
    0x50f0906061b01091208070807030603030210020306010c05100b040e01140f060d0f12140a14090d0c1d0105100507020d1716110114070803060105160506160c1a 70
    0xb50100e0413001e41010304802d60b0740c1403d80c01c901d4840c42650760783d5540401e0b03035a50360305400b15100e034000540180d00020b540315801800c1e03401150000b105040036a0f00326a26601ea502e04000703005152804c503104c000c08444ca00f898040c4602e418803040c000d0000300d00040c1d800e02819001040c5240084110010400e240c5442e00c55030903664000b85200314580080c01e20500040006910100003804444c00c01c07410650039040e1000038041e0361307810750400c91009107808a5041307401b520383e20240c49400e410000300e5204001c0018105801c0c041c000468142c1034264254050744a40c1c020b98006082613401c1e0b0780801120100b0f40d045811721611807460409001d03061031212007003a650800200b40e68a420500e44104101d4861002e2481042c645001103071000660302414411140900040c0005080e03080550351001d010f241042c100800300c0404002c03500c07148030585003900400184181d20822504c854808071a0f800c2414a15540d40d0300e04180c0c40c01c80d001c02912228900210390 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 315390269 1250 315389019 315389021
    0xf0305060d020102190303090b040c06140c0a030807050408030d1a03191e201002010c0207050d05010f05040c0f080a02060711181504060e0610111213050f0906061b01 73
    0x2234100d4000c981c2002c68074261600300c1c810040c502404020513009080440c0411200e812a9020300b08413014014001c541c0d03906480262000d8112414040103002c04615200c04001510f11030601910110350460941b07200c1c100760020b81901402908016400361100c000d0004c010301041d800900702c0790710081d41942521007800100c004284035001c00c0703020248000f0040142c2400d50866204070115644107007a800ca80d05c8180b0305001d41c0001504110301e2074043c00d15401d1500500000c0345281e4402902800c440041b1400c03030704264080340900c6200481185030011b0050350b002001c500b811500014201d00a41030000c0048410902410b880d840f4011140c100d4000007820020a0402d8494903043d0480702c50300c1ca00861400600003036044c00c0101460180102070820000118100021100c41e4071100314105d4900c40d40344181100318800000300460758040074000c0c0401d043c80d04206404145601c0503104080c12002d00556030340303410480d880100502090400c1e009140401c078 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 315391519 1250 315390269 315390281
    0x42919060219080c0a1212060f1401020a1a07021c021b190620120912120f04060905030f10050720030d062103031d06070f0305060d020102190303 64
    0x69198011805c0c03090030805036106040045881ea01d414881c84107447c0440b007203039414401d843d1141d0103018104445040082c808503505010300c1a0743c075141090302c581c1854079144074440125000e140070404e5080c1d040c82240d0f0b4200c803000500d050361080a200940d03c498164841c0c179840b1203244040e00f02d80d02c13034000280190f4800032154080e940d84401500035201300d841c00c680403c8842c0c2c127484c0740e80c0100300170700058240c3d218030b801c10308007106012603191104420021482400d80701e0451118110141c9201e0f078548600c0340e65507050103402410710170719910841c0a9400240c01c0c00141502041540140c80641c5000410740da07030300c070221015018001642285004210302d100320000c08001403944a007000400d00c00c0590380d41030004c441805505e00c80d0310790f40c0c031f10307010b80003d100b504942c410f1490002030814400d45d0940141c204907094807004017169141c007500c0d401c3c9416020b40c0e984148212100d4080c604180c0000c1d403078190b040344e00d11281051350720350b8080600a500030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 315392769 1250 315391519 315391537
    0x60a0e090c1b0120040303092904090f0b181f09090c21081b0304170606030f0d0c06020d09060e060403170402060702010e04291906021908 61
    0x100c0b1914440d645000b450010304c0000c2650304400903031000040c05044404130f035899903800340307240d01e00160b070101c4c003549003010041c180040c280c8040d160b503540b000d000646121303600021180400d2850404448862005130300404018002669608410030942e611070600f09170000c1c10001601070f041c143d10301d41c000d0400c8a00c1c100e4180140181002c0400a0340c01500701e05440c0320141c602026a21a00603008042c60010850a1142d03030701110907401182e001011282040e4841d4080c400c1900c44485000141d40700104015084c40c0410090414041400240076510001c01006006400c0d640c006461140c0000e00005001b266a00c403c00c00741d001402003000c0550441c486072211010b440c240c00040e82e03401c80000100080610030b000f640d0040449103410552740c01599141c01089080f0f5020396118102c5040d141d21020603401c0080104047d100500c0703801c104003e281502c020000d19885100081c085030b5000950000c001d407840740e4107002c0320b001e072a040c2c00d584206115 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 315394019 1250 315392769 315392797
    0x27030e030601260708070303201504020906040614040b0a08241b0d0c3f1413020a080111030105040506060702150d020d0504050307030e060a0e090c 65
    0x191065a48180b600b814241100b210442660004003035907613078090044603d40c0d00403240c100b0010b030055100000c8107200d6040e1106580840c4151400c15113404403405044051030f00b0030046107404e0000d0740d40008122001c202c6607040c101c0124088400001d118001e69440820071381c3d90307031500d542e800101040ba084680b1000218013200324821b1044002003140a90000300d0001d04141d401276990030b0714142400d003011092480390340904010050301d000e10105041e10701c40310f58208680c15013a4001480c41c803600c0d84420004918560000110306c441d0300d002400310724603c0c81d08146801041c1031410340024020750000814030320382640815203035031030300300740901c0405c4000c0958101c40d012a000c0003150349200a0021512406074000d40c8104028401903001c079861019051a045014006040c202c00729800000c582046d01d00b03550a50011426000309507000655028900b0107480c2e043c00c2041540018269100c1045000d1040b24a480000c88042d450002e0741d1711400b1000d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 315395269 1250 315394019 315394021
    0xa0f09060212010f030b0615280801090603020913050f06070201050601080c21180703110f12031b030d140f180c15090d0b0f0a27030e0306 61
    0x945800258091140e04000c02d0040c0000100400c4846140c0126508000c5032610360759241d040200c10001c0400a1a14190a202c034a1701d4009145802018005100203450340c0f8980340e001824090050f800a18075509041c0180016103510034100c2e04100004032a010f0328040389490f505100620304094158410041001280c66054014500404003a201ca12250325180d650701d905102e250b054040c0e040e00a040b58155a03045041290301c0f11107000c5041003d0484403035982800c86603401a903021451200d24002c070710b8040355218402100311208010b03400050700007900e0b4052940d5050702c04206048543c0d07441c030240f0441d2600032404c07104102c2d0210320600507481d40c07010303298040e500018000041c035104c03089100880d56166040240949412401004880991262828079084042c0140d0b40d07070f5244c0c00c11012242c0c2c82150803110924001299a8002d00e004210424440c1030103003100d18a0b01d81e28a9658011035403402081c0c0101fa42030a0780c1d00400f0794400c940611402d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 315396519 1250 315395269 315395273
    0x8070501031e0c18060206061507020d080f0403051605011b1b18051609090902010509211204050f0108270f120403110f1f08060a1d010b030a0f09 64
    0x2000b084140a0b0345113110741c0a460315400ca95446084400750340040b008194400940d0a1001400c14288000c01c80380c21091035a40d149901d4100c2c01c4100b5403520086000e10401005020706076403150040b07107040c0c9580c0341000091488896a0b80c40c03510704014030303d4030107100d4010585a10345512194400500b80d031003650b88900c41740f60141c0003446107000045414202103001d02c2100c004140d0300e000c0440d0504851fa001812100c00032418840208aa20a40d496603240d40000c480d052035040050b01148400500b450251035041c1214038003044284420303501e07040c0381d2913051800c0c0703080b060540c2c90721088949508035554a040040d00884d240c42d9003500090051142d560171401c3d50301e04848100c80c0d845070700580c0402031041e100151240281e04000001e0510003030300030000860342c2846401001c1c07034000001382200052800d000c0007094100080a8001020f81a04000c5c000c52201415900d070350060090b5003c080780003001c00d20640598001c82c020840c0c00808000c0d401ea14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 315397769 1250 315396519 315396527
    0x203120a0228030e030d0804060c0309061104030b01050102030301030b0a0b0a080f101a030a110f0603150907050309030a030b04020c0f0c040b040b0105071509170a14030108070501031e0c 82
    0x100b40c040f40020001002c07076800782008519115042c1203615540515290381c0d55240c0905101e0740d0b04820140e0316620b4201081c181d00449c1c0c48118240c00650744c59085042080c5c40c40416003046e4150b51081004000042c1c40c4180140d1049410b5400180c110820000448a403903d5228a0841c450000c440301d40400201c2c40f9007030556581c1d0200030700c80000740b031401c00280c0000c415506070001c01462012500b81c82c0b1140c14810300074444da200040c1c1c500002d09a4000b611080581540500030155a041010308541c120070181481030552906080c01540c0b0303c01d40541804258031000300e00310390740722a0140c4143c80b00c0ba8098540c890000e1101a50390384012a0080c421401d1010440c5282094410908141c106a40360342c5002121340f150034400d240701d40360f14651aa03508415011440740d9211800d0b407a04021401d41d65910880018007103403400034803001450003000108002400080c030407040f01c0003800c1c0441c038500035406200035180e480c0c03103884081c2c1c01d101c1c10020350307640 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 315399019 1250 315397769 315397843
    0xc180f0916080f100b0604060c0203011104030b0a060608060625050607030c031a0306041e0206030a09050d09051c03031b05030405073008210618040203120a02 70
    0x1810b04980007291144c69110036128280c00e40f64115008100c20f01550f8403d41000000a0000e030011070505021481d0600c164000d50054901410741d10500c64019a14052100204014600300b0101e00380400081e00ca4070030201920340b00261442c03036402d00703007114601d0307040385400c841510308514000c480900903000c404041c5001a20700888007460703d03815481d540d611070000c4c00400040d581e41d0346105100a21104404c014036103000c6000042e501c0380025031041103120000b091031903451418030b00d44504024a60180142c02c9028000d80c0c5030030001e26100d100343c8203442c190342c0081c20258002d00d2800f0511900080d1712401c1c01a0313940240065000c1c51050044842c04e95484d1122492412a550281012404100c1164088110001003c0b20a000380851441c00a0000c00303c10f00269401080c08018003860030070195107024914840c012420040350b00b00c500e480d600194480304100e40d034040c0f8183c0030481c10f4415108000340300790502c440030400d00c120031180c20318503030b407103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 315400269 1250 315399019 315399043
    0x8072d020a1a0711030c070603020901110709020a08070c15050612030310030b0f150409140102180109080304080601090c02070e040f0b070e09040f02030c060f0702030c180f091608 79
    0x2581c00c0441e8104c44000304640040e215030018101d000c0c10600102e002e5405004168104804480000d10368202030148200401c03000c480141c4d211242c0c54003030310440009105a0521030081d01c040e001c82d41044100040c510022000122130751210002a2004c48040120070940b2001c800c000d000103100f001c080559001d14481c0e4165501d504000c0d9070311400b141d41c0c0352080ca0344549842c250400d5000050060b2040d0b82c0c3c00d0000c0801010329089030011040d0845000071a007011445580084034000030b000d901001e0351a2a0400c6c41d030b59036a0b4018401c08640c0340e61565800c3c803441c407d00c095005424106c800c0700c050309042c01c0c400480541140c1c1554034500500100d040c2500541480151040103426072080d51780e01d440d06100698000401d036014051441441c0781555064000c01c20114410a0b9907114440f034018185445840d214542c0588404e2290382c040d0500e10743e0b0190b0009600650700050360b10300390041e060106a440d00c2c08109004a07000c10100e6000c10045a104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 315401519 1250 315400269 315400277
    0x9090e070e0f04120c05030403020d05010c090501050a09050118031a0702010b100804030e2806090e0105091f08070b09090609010f0911040f120308072d020a1a07 71
    0x6101c01d4080540b014007501c0040000b444240100305941c0100003114aa60054099030b0400b41d41c1e40101c2c008038802881200c043e5556006240159040848100544020302c0c1490900e680001c025011249900a8506100040ca62000b002d1541080c01020310b0340030440700c8240c4104850131542007411f82720000554200200c403401ca08140760f00c104807211550301c91881e03403a5510f0507103004415144540d00080c3c4036800f80d03201200c0070b6480000d59a0010104000c030300c0c0100041071514250444180b0504000040255507250218036401809003030025050340e1305c3c180c1c190305819080c3d1020380d49006000000500030340b41e40180c10002d00640e5206995642c807404c000c81003609000d89043d030035800c20180210542070b4080820005c4004005141c2501d807555606000010703404141000b03544065441090740c00140c00740c0142c0c4a0074080f181c00c500d0010b0300381a5111740c044003d500500c12030000e006200300904040d894111005410340c42c0410782c0c9410107141121540701207 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 315402769 1250 315401519 315401521
    0xc01060f060c0c06050307030e060f10060201060b03060f310b09070c0b070201060906030803010f06020f070303050a0329030706110a0803060d080c010f0c0503010605120709090e070e 80
    0x314010064600303210f03440b15070f100d201d908021042d5034540000e8001c400b05a0b80380440302082404105060040c080c0c1c2512201e140b90190b030700040c4102581040d070840e41044020441c010411040e03d410003c2103900c1182080303401d011a401c4006410102c01580c803c8404484083d4410150402080103180902c8000c442c0303024001040400d071a40c0c2c000890800702400422400306003150442114400030030f1081e030302c1c2400070a0f5a207580007550703801c600000406c045003c00140000501950003d00aa00401440d640e2182d490f4800a0280070000944d444228804d074440c03000c8501c00c0c3c80a24010764200034000744800000c9105010340314042d004164030f4050b2405418050b20003000b00240245651954003d41000e0320a80c0c110520400719030005034124040c04401c0c14102c000136a0104019000e41960460002001809000c00042c040542c2c001c0c00c840800d045d110307004040d500c890f0021a04007803203074842094246007039000040e01802046400485404951228007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 315404019 1250 315402769 315402779
    0x11403150421050a0c020103090c05060706020c060906061011010f0f090309060203040f0605090d1a07081003020d02061e0a020a1103030301060e1e03100204060f02060405060114030a02060c01060f 86
    0x50322480454001182c20017000c1c40056100f5000000070601c110592011a662500410b281d030300500710484040380c000c0380740ea400080c10400c681d44071084000400b00d0307003000340114180000d00d08000301000001e92401d2024070094001c18400411035004102d081c09130810500181020300048001030a4644001340d080c0c8000305031004d0707414081030321101a00d049000c1e1220390206404076080311402d03401d10003082ca0300b85072080400d50725294200914150000030702c0358400815070140400e0558091006d62200903611502c030390306039201c50b81c4014030480e0f5902c1c3c1c841a280741134400d0700040e140000c0d56012500c001c445204545a1030020141e06c101500c81c0024021070001528045107a42c0358a811212320ba10807400003000080b0820b80404641071510006183c176500340c0025080000d5507001200a54954591020f0401410260359a5455030f406200d4221440300d0039200b8203481d078080c001d1503455540106210740e41d20f10400014003a140303902c42c200600c070b030150300060 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 315405269 1250 315404019 315404027
    0x17180d0216062f07060909060b0703080c130b0d06090e0a06180c0b13050402180f030708250f12060504080405040e01060e150603011403150421 63
    0x808000d0041004116402d00404642c0e03040e200f01c25a241c40600f1a84561041c81c9908150030202c220000e4008142480c00140484019902c0b11040b2890900d04001010ba950103466420307905192552050b110884010118082d40141d2144401d00c0340000030f040313400c1e4008203103240c0840014800a03543d4054401180c03e24031802c5401c1c4c00100d86a0f00013841d6130301a0030b501000180200c40903855032600102d114040c0c01c030301d20b0301d02c0c00100e80342d04240e550100001041d04440a42c901082c6961001c845481c07981600d0052000c14800f035903660742409400c0240c00c400044464002882040c510507540190b0750602d0507042c5031000c15110304040094003070303c002c0301e42201c5000345c07076603590000c1c0001030003030f54055400c0c40042041d50720f41c01040304902000f00003040d19410460b01000c25030780608003144075801031111482c5602c543c4c055a0444440c100f94464001d5040082400c0c0200c1000c46100761845000300410005940810301c650708405440b50890043ca5200781c0f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 315406519 1250 315405269 315405283
    0x20d0c0203130e250e03012405090a02040e0106090620151b0706090c08060403140f0909040609150501050a03020f030f0102120708070905150d060810022d031617180d02 74
    0x148c61042000c0042c0309034201078166603007003628042c0040c40c0c19680c07045c00100c01c0003a041800050507007030b4204041c80e03110b86070749940c018403202c8d000700010761048243d07502e00440841c4890a142d00004d5480143e0101e00580e01c4040400282e980500d445d00c50024a40e00e0340c00c03103644c050b50070041801e1400141441c421945901c500101c0360b000710007601d0581203000304031428101045600115259501000e0040c0d22401000c102003a640c1344c030b00060301c4290f2103020181d10709001000240d42c0c1410041c00c480d010b5400061b0800044082410a050081100c060b5800000d6483c01c00b501c1e8891a407080840f55901c05041d01c5200341103c0c208024441c00303138030050340078003c0c0406000d48014460200e00c00320005603150740d111040d080c014801ca0070360381e85501244210400c120060a20b80c07010889000e0102c0b2840010680c40c1c2d030001401d0203c00c5a02c92001c4055240141c000c4040803000000d540d107a45000700f03400c42c040746004403c8900d40112500811218000203421b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 315407769 1250 315406519 315406571
    0x6031103010b12090703020d0c09200301090906090203010504082106152d1b0a15111201031113020703091a1606020d0c0203130e250e0301 61
    0x1c81d01c0c0915030308180310f01d52805010f0600d14090300b080000180d561140c20b42815219a00c401c00407864203d101c41152401841c00b943c18204924151484044a0489056070036240d80002d40400724203100780101004a0b0007500740d864030083c00305000f01e0300c020301941e20f00d8520104a1844150281e00307030301c501755041508150f482c026000d0002c1914003078a41c4a1019441500140e148044552090301c06510650a50380004400514508120041d030885900c0401003031900344540e2030315040b00402c91150010b55540701d40b400440800c004a6400c00f511640c4403610b940c4030f0400b106400d1031140c0482c850303024408240f0a0400c2402501d00503034047c1c44010319613103400906800d21100741e00d12842001c1c05c120058445021903040d04a8602400c0c006882395103605000c0c080350700100e044400c0d54001d01400020032140c850b4501694000c00c0102c9440d1502035a0409408141040e021420001c070108042181d01c1383c400150100228024480c14005000b02c1e50384050000907 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 315409019 1250 315407769 315407789
    0x1703030a0b010c0f080f0c0307030f1206030209010e150a0b090a0f060e0904060209040908030f0609090714060702180a15080304030f11190f05060f1213050709060603110301 76
    0x41c4000b045002d4041c243d12000001305070328040000381f05034203560029500f2400314680f011040000c59210440c29020304c50000300b04041e40c15500010910103051041144040a0b00c0010310790000041c4640d84e01c0501511001d80240c45070903071b0000e41c0014580a000d2540820006606800142e0403021900c29880729203400603100d0600808140080c13080d203045400300003180b0142c0301c0388100c454803402100c00c3d50f2603040c4103100c7c002800026008500c580030107800c0c4811200041041806c03103040c5103041c2529035209001c13900341c0c002c580010303521003400080317200b85143e02d4410610a00121340704110781c218144124203d0308260041501c0d40e4000c1c0424000a80ca410f501c040f1349008542c030f21041002c910001d03810048031280c55440004010007001040504c40c032000c0034080468206040144c3c46111107a83c0c001c2407118615010050041400d1100b400d030110a901c0d0400180d80780113884038440000703040301b8130880000034600740c070b042c2c440b045650a880c182d0b490070b03007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 315410269 1250 315409019 315409043
    0x1509032907050918130203060a06140909150c0d0c0306141005040b130302030d030903020307030309110a03030306080c1801060c02120d080a0e0d0806060c071703030a0b010c 76
    0x403102a001110102c1c0c200c0c0d000e00403c01030b01c0744c2c80c0507107118000000c403c030301103269841418109400580352a4195090150a00001c074003445c0b0400050401d446224030741c1e8030020036a16080701e88681c400010700c04403d00c0801040f100007846a002801070500c401481d09400703c00312021442580c0c603170103028280000c1c500d4400c029070906500c6280c0b00742071648a024605440d4041119000b45240d0124100210700b000d102c0b9500c03c0b50303281420040840c442d200a9143d104048004040603030309e102c010704201784600342c02003240e0060f024282c0c0c25213919000d4014405401000c000b0f100300c044c41c5d5843d00c0c0c035240111119580365401c00c600e920b000000c1e98009403260080703910041082e55459000c40c1003107007413118141e940d6520500d0600c20402403c44118a071405010f8102e00c0400180d5900712403c5600130000b40e68055507980c42c2d540107400c0c4100c3d50030911120401005030400312070b00201442c0210100c51081000d0b518000054440790b9000900929603000d00f4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 315411519 1250 315410269 315410281
    0xa080a020a06050d021c1a091b03060d0807050a11060c07030b06040608030f040e0109020726160303060312020607020618010b09010603020703090b03060604050f0a15090329 76
    0xd01038021025040d00143c24041c1d4040c120403100310340308009004a0799821b038007a0501c032803000c9134800030313041c0d52003102c0d2706140b1044100503003490120301180d000000800c1403a1181c100c009034580c1c1154401c6d4840c40140703801c0c0e845a10754002581c88603441208482c03e403a0030800c581e00b50580030010704031103195641d10b1454410040c03106610541d01c16001800c8941400101145001d20b551150ba4909001703940a00c5031b03068104d032030300c20f106104050006200c202c0752200351149401545a00c0c440e450740e41c46a2103400c5500a4220f031005a4008168060704908207070381c42201400800f040144040b0794840040752840010b0307022070040340c0c1b041242400385070b4074006200041802c424000114080d4807080c0c0c0004000380c0d00050b10404d043c0c4c03010003900640040310800e0f1a60a16000059050045010340c030b101c0d40801c140004035540c1c0c03104050003080740781405000742c440c06801504074182c0344801d13074000c3c140030141e030074200300301101403810000c000c03074801d0581742c40c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 315412769 1250 315411519 315411527
    0x1060b0408250f03080c0601060801050d02040504111917030c0304150507060c120510051e0111100c08070e0102073b01060201060602060105102307060207020a080a020a06 75
    0x42d50b804020001540d000328044411401000140d40103400d02e9035111010301c0721916004059000d4000c00800303034010b001a03601e920070710f120180c0460380450103803a542000f100151243d07407174980c80f010100402a0710b000d42080b0200720707848845450500008a8030b01c54582c42800c0c20080325800811040c00400007030307800c07258242554549a410622140c1d5202e04540001c402880440c114404044521031140142580031403a010718082c11850900070403c2c2c0781c082a2030100304580e00f1000c4d44664840c2c20300d05400c0b000c01c0111540340891241140091040e0003c01001a03c240006560750340201244d094002041c3e00824a8501e0010300344062460034011a0181004040321400800502c000003000c82903080c816013207514000c4083d003150700d142c0c002402d41d04182d00400060760380300c44030701201c911030409503940c071841d9044284580d0301401c030340410080803070100103000320343e4007501ea81b52003950001c030b00070b45400d465603072444e01250007944200d40070418030083c0d00c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 315414019 1250 315412769 315412813
    0x30d0c031e02041d10030813050a060203160b0702190f02040c08011409040614070801060801060f02070b0a020f0601030303021c2c0c1002030c070b2802070306110c01060b0408 77
    0x200c14848142d16032240e942206039030000c4e003238038a103884558041c4100e1801c0d00b0301c0c01c0184031b80c1c00258a40b100d900c900e1803581d45031902c083c02c14030322000007030b150031300a11003190b090001c40441b200c0c0c4c886a1401001d4941e694500740c2c000d500c1c0402011a45015a0105060350840044c1d51152040442004113002e00140115403442e120403c604083c0720440c00c09000d0004d0752a1000700790b040c02c0000700306c2e00050b1321040402803101c0301603c5070390700450360900b518403240c4070079520390701441c0580c5041e000211040e41032246c0c500001c2410f9159003c0c00300d0032138000800d0007200e6140035500c10745108022030070101d00c1036406450f08848603141c03045a0804001074801d226010800a0804c000b0072143e072025800000c1c6441c18150248044005080ba01d050740342080d02810b0f031203112a10307041c0c00c804d030405031300580603105008120b10002142d100b44240120030f0100c808141c103810091099246600b403440c041003400ca0601036909881c1e0300c4004013810a0048007416807401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 315415269 1250 315414019 315414031
    0x70609020a03060e0f0c04020f0901110309030a03090e0a02040506030a0513020a0609031406090c06070c08100618290411030a0b100906020c010809030d0c031e02041d 73
    0xe66894000005443c50141400c49002003010341980460101c01506145021182c0c03446079104000041400c0f61440036650100070a2074051900303044082000e10354407450b00c1c816458804c14115030101075020b110102500c155440c4828251114040700d0281d00803070003a40e9120707800344001021a5242da110b164400c0803400c41160848468020800c1505160400000075034428400d10503c843c40c50491518801e510041c1524603080c0480e6448000c21102c40788607100000300036081c8042c02d400c250203000380d00141c8115214850094000b001c09200d11042d040e001c4d040700041041922942e10400d40110542400090304072661141031a1640d1180e40940c0d03a1240e44030f00c1c0c2d02c00740603600c90a401500080c00501c4041008404c0b00c60207962007c0107500307101844403d90104400580d403000782003520451f01c03050205429400740e15202946c00c2e20b031000c03040800da810780104034241c0d0701c000425031103403126102506070311031405000014118640e040441c84c91144480354408 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 315416519 1250 315415269 315415279
    0x303091809120e100801120b19020d0507200c040b01091e0303140309070603020d0e011404030909060501020c100908160e07090e060f040e0d02060412031107060902 72
    0x1400540c0c4039103186564104000c00524000c0d1075001d04e041c41c1c2458000c5080604100071150325004011481e0811140e00403c003403400c50200b01c2c19000091201d01c072812804081d511345105552a40082904031101c1c170014828400e5405e20917842c0d400c41131800c450030040d0a04ca0021006c1c400074082c03101034a410032168143c009410290644090390b400c541862840c2000e20390700700181441054206212102c10800500ca00b201c3d002540008031419801d015803180d40e0703c07100c18010004202000481e50030040e036003e10224010419200d1442500c60021058031401540c2c200d54481c09440c1c050780c4140040d60b9540380505000503600c80b0ba15007040c02c5900c0d040018209a110342e4103007000740d000c880a20031100ba001680e6889880b03072030000c00d043d140280d1038861110151100d40135140300070689601c1c3d02c03181c011005c1c48020404640c10b0800740d1a000b5661a0211002d60304404600c4108041713510074002e0000313502d10860700909050140d1034540c020801034030201e80c00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 315417769 1250 315416519 315416531
    0xd210519020c100e010b09150604050a090903020f03040f171c08190203060904030323070f26070f12091103100c1407031407210903030918 61
    0xa212203000030a511020000641040c403803e0118000341d0300c00c401c41e10001d90400305214855121241143d50040ea5844894800c09609020079500d20468002c50340108480c08041803442013030b0440034015100c3c0e401c43d800c5100f101e40403900c1e0b01a50140e102a003200302020000018200c0620802c00014402d90b88280400c00c0000340311052615610003240ac601c0801010304411415030594001111f015882c5140400004008140080c8002c2c18159645010f008201e01e0b44804591010010025401c50400e80340c0540583c2c00d030450580025240d04080701851a5030303901d441c4507010381991954540b1200700540c1c3c0000c0d04004075081214038881034000781c0d07180c0a540d0036240241f021110000e8040181811710066110300800e90b41803001c4039a40395440075800c848991480d24081d200c110514040781c2d4401c03d440d030b8009180002c60079800f17024062150001544c0300000040d8801481441620012410310005d40481d01d0752400f04081041c020441c00f89005401e070005003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 315419019 1250 315417769 315417811
    0x15220f05010323010f030b090607020c0d050f01050c030a0b0301060e070c03020a0c0b07150e07141513050405010e04031205060109030b070810060201090503090d05120d0504050d2105 80
    0x8100070992105170281d104500400502040200150b000751180000e0070031490104006942e84080c118130a0081c54801059030030f0080502c170307498008800e80028829800c00c1d40d050b0707455400c16074950030f00919028850045103014810a4100c40410b00c00710340944c1c817910241c51090195070140c05602610301d0050020f8000000300024003040c000c15600d842281c2081c0c00160b000a00700b1075118904181070501e0240040e03e80202c07040210403c000c2070f004004104d2802640c00d41150604000c40c1100000c82404103110a8990903901003050785c0e81c404007118002000c0d100500400d800424209010740c180c1c000950042060400a54003540d03031741c8850f0315070301c121079020019910700184103031421400240d200800140c07009002e1081d09460307003901d134416019070741e200748541e0995208024060201e0410404405480384d2178000c22030501c0d0103040211002c403043e000b002440b105507405098010003007818000300d25840d80300150310400821700601801c0600c0c10700710b0100a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 315420269 1250 315419019 315419081
    0x2105090d080d14090a0f0201021c0806120102070b070503060a0e011202010f0918150b070c06030c0903031e020a02090c0703020105090c10080c0915220f050103 70
    0x30129104200d40c0d42d4440d9041d110104581180c944400e000a50750103202c0445030009030105000e8000c15110342c1984240700603458110042015100020021901000190070065180c8955030580e0104009507190f41d03c9400c078803501100519121150020442c2107124030b02541d8060300241800100035210014035204075000d038003031100d0700c0540c3d003040d0465038400312105042100381480b4070000d0410714800512071603021204140c0d80c0d1000210300c4a100c20054900a00c4090041980c0360f45609003102160704d0341c0a01030100b4140760b0b103404102d00c2261802c0890b501651408511248080d058140c11154a454170851181e1182c40015a40e2203201a0148110950103a83d40120340350103030039202e00606420283d0071108900720291643c4100c40300003010341c0303000411a660400960054011010000c0d0410f440d1244410110300314002030081302e40c1603003500800b00503072000e64541c81280c0616400900c1c43d80c4200103650003500b000424880c3c0e141c503c0107a00000214034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 315421519 1250 315420269 315420289
    0x181b01181d09010e01050a050a0b0a03031d0102010914060108120a050d021602100509190305030a08071e09030308060d030207091109040212181c0e010908010504060e07050409210509 80
    0x41c4440b9528000d200d049c1c001071064002590b4280c502904203451500c0141c110301d6803d0264681d030441c00b8080744168400e40c4520710303040c2d002c4910004000c03044034565a82500b4018100705220b4180007000e42e00d241420b41da030095040c0d0b075442c90405000ca2110280d0000100300840e000044003400050740c8003902c3d035903000c0c0c1d00c0d80c40a80b10440702082220800c03040d6202403c2461001080c8003044000c0215a486804c1d418500c8003900ca01d03e00b118148203d2810300e1400300661448520103034070415400c1228061380e104142c54032641c0c02c02c44076405403c00200982d00103942006400040c0e0000c241204035240a1800c111070030010506a82c41030010b1384026001b90100043e402172100c8102c01d260350f4100a02c00251143d80c0c00a020080034440d0041c0480500ea12485078451040040507001c03c80c024041404e291405d00b014140311150300c1c406008089000c50142020f00c10201115003114000341140b00e03207c0b4018401400d07c40103400c01008110050316a00c40003000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 315422769 1250 315421519 315421531
    0x1c0c050f1006090603080313050307020a060c12080c09220e0106030c1d0f06131e0b1002071421070306050609040218181b01181d09010e0105 62
    0x5444450000da00c54411030303005800c41e203800b80c6404c01c2807001c0748034041602c0c0d04c9103030480c3c1d0221079102e40c01c00c41d06d140510240258084400d07007020401c00d40c02132405451910038400202040c0c201c00e0305503103080c0e0407592a402540c05010010282c45d04103004504016649141c0900c141030030f200300c0a0b581890300140780c981d11004200208002c0e00389400091400c0b0600a017103848200804c0c91400001e0440318a01604202040c4107541d20b0f6800300c810201c1711800c2000908420f4000791207200080c4e1075500c107140a4424016092842c0c0e11307181d0710400d0380501b003094102011000c02d444185d02e0203400a0094124036031191112203c0b4014110b22002401382f24614078169055440081201d030090442c01d09110050b00e03580964003401d4103842601041e5542c3da1303003c110000ca8402209050301c1074820321006404462003400c1501c10a0b0303520701d262141301d2144800440d051080401c01940306400c50214150507540d140c010602500108444280141e030324250b80c416540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 315424019 1250 315422769 315422773
    0x20a0e0105361212040605070c0504060e06094008070602120a0b15370306050f0d02040525030606090510080705031012050c0306060904051c0c050f 65
    0x4094200d15203142420009000000100400365900140b01c013a4000c0e403082200f48400031400350200452681c0381e074054240a48100503056450b0310b001007103401620094003695201002c10042010010160b40071200b0700102c5000c80b10303540391a2a040200440071441d6800c01c134104002800800044c0b40d50b03400345901507196680021880e0f00c0c40809012042054981729034020740e0b0f11031610442c90002080303140358842d001c25a4498a0341e26168105c2a19052000e51140c000c400c4012104087d4075a0f404210481d126001d00c00c1406103c2c0b0005d500c44822603465005140640003079502640203055100d200282d0058031004400b891a81804241c4407401802610b9205072882c005040495400c0030110003c64040c00c504805800c03082000000800901b00011402c107120041c50241c503400007001030303800c0c410744540150942074400c2c000c50f00458070618181c26091b02440e000000362010b80002c6840c1c42c100001c1c5800c01e010302881034541e00104100303209507220300b038a07540 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 315425269 1250 315424019 315424117
    0x20f040b06041203020d0206151009270501060906081602030c0f030c010b06040509160912080405040f06030c06030507020a0c030f0201170702100513120512060301020a0e0105 77
    0x20b4081e01b00040f62080004641c0000c0801c110007421100b140050103040c4d400c0d400b150054002107591b060b10703070400e0708009a0340107410002180190b400c61283c2503c003041090740d89500d41101c85801a102c3d41c00006e01c100040344ca41e4100030a107110b044c0c810f00440c0d2070036000d00c494508000031001e445103203030030104003045144020f000d6003440c803108596062506041c100007030401c0c00c02504c00d1175a4400b5110b1084183d0045141d44094100d070100c81c80c512032a498083c440341d129008141c022420240e0040b0300b010640070307110650f9848001510781c039041040460007010010324540440c420351214402040040e101007001c0c5000301c682c050000020b000243c032180c0c4440e0b032008105003150400000340e9011800c04201072000102241c3e503103c01d0600c48076440c0381030014044e6002c0030041c4210680000c0100b4408a40c01d924445503540e40e4201402c03402440b0460b004107000040e520301c0c661080000344000d402400c218044100c445084001030b11012040345601d48040c1c2c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 315426519 1250 315425269 315425273
    0x1060503070611010b06090915040b1f0e040c051b0102041d0a0c1812020307090f1b0e150d090506041112190b130506190606020d0c020f040b060412 65
    0x300171070b40c0e014400c3e1825458400c010300452500f210040545070040ea83c00580c0d041540d4503041611050001000c140c1021850340750b02c0d2540c50800202004150300d2000c0d450303142410f000708980412144c5681382014070009540224000b1001400c6482d5420400410070304450750900c40c1c2200c2d020b08408541c41c040151300300711040304507600140031070362440b0401da48114201d0002c0e17646e1008400a10395240c40400e14101c09900600391260408140d80c4001c8103a50003000f1814a03202e51015451800c107040d65403e540c0801590030600b03540c41003000503a00c0000b03005c00d800313112002408e01205d440300ca09100050f41c084412205000b441005840e000400c40100c07445140907216280300710500004100d03081d20000c090070361150025196601c2c41c00c02901c61600700d420750380e0341e1401c5400304410303030003403030700b216550346428404035600b0700c00145462184215228000c0c4140d80b0717001c0003a040d20f200f09040e40661174000c214407a46419010380024001c401d55054140c1d014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 315427769 1250 315426519 315426521
    0x203100f0b040608070c0c030204020a0c0501050c180a0806010b0318010c1701050a0b04030b040203031603110d0305040b06010c061803051c0209090103060c231c0c050d0e0106050307061101 83
    0x54005d9040041d00642d0f2000b245241d04c600c01160360403140147e407001c0d200350580e490004a0000380c070075403810302004210101e0200400d5040c414200c03504840f001d04040140d03050030f40c0500300c056030010005008000402d001140c002c4000000c080846402e01036107070a4a4844941c07130b002a202d410f4903941410b88061560141108603481c04850b0308011113103515000d40d02c005007002c10b40e10041000d544007802125041c072a4148a140382c91044c1c10003403c2000414001d40e1030784140260b0b81c49281c4a4400c0c18010b0f0740c007841c5407440744c60310340c0111400c650b20402560003175900e0300d921f00b0200300c0b182c901c0012403182d15030316114400403550500342c20607010b00c2d4100500420000e0500d540d1500650b06482c3d200a0004490f000c0c440111084c541c60b01440c0303840c0c208100040c555820841c007914a004e140e51000450b255689541001c2d101c503640d00d00b0100d0380a221500701102c60360450082d02446000000b900755847c00020718200c90343e80450007180c0b4500f61344071500c4c02 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 315429019 1250 315427769 315427771
    0x40c1d0a0b0307031a120d1b0c0e07080f040c05121c02070503300f07020d1103011506080114220209031e0a08071506080102090f220203100f0b040608 66
    0x5c11100551400c030012500b030348941308000390000300074100441c50202100b1451481046402c001c00ca15002d4079985502030405054640f4408039a4040c00100400c1c0036507000d40c451580580e20840c003624000a12008160800701600c032405040c0903544120100d013410400d0214550090001c0c1d0300d400149030501b21030045409120302d40c2c80c0d00d5422845426100030185802c80394907943d44415000c0f401d854024501c009612807000e400c200c2c1400707040d505164a00da0120002c1050031a0361820801344086403003001c010420ba1001000000084c0d1214006413202515014405401c00b250b02d071101c14601858000c2030307000c1980b200c1402c042001141501c043d10340e0280540208094035641c04040b00300512503003001a5480c108451100702000400c1d80003028812542c42c0c0c1c181a002c5d4000c484014055500d54000300101d250075800f120080442c0c05100c0604414440d413040a940300800610000b00001000030700b0402410900006294030442c550316035062070070080003020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 315430269 1250 315429019 315429071
    0x4030324050f0307030206030f091c0207030209011d06060d09020405040615080a0302030418020405060a020d18030c050d020d1406010806010b03010e06100e06070c090b040c1d0a0b030703 82
    0x3c4404000c5c801a110311080b43d400058442d0070789180c1d039442601a107000050180e1507101d81940700c0d0b520302c00d500010000b007038034821501081c890380c0311003030420100842d140f0080c14855180105582e0304040b402895000c42804011880c0040e40e00820203071036090310210ba2003a44d4002030040701480c000104040c00507100541542d21250714000d50b40c0c000c602480d0540980140340c10a01360050781160000c2c0005001c10351a80c3c0703c1e8030040c3d22070103d90468008105942c3c02c0c405140c0d0711841e50f1013583d174480c0b41001c502d424802809001c000c2140200c0c0c00000a103000404580e5800801d0385c94a01000144125810b2200321820140706038400302e00c22030300740010310500000d001000d038014816100c004c0e41800c0300004944010000d41d5440d0400380014400042c8002c0e0030b14981940c08100e018800040b036071040c0f00468000c065200002415001c5209111101005030740d40000020060b1203d42e4482d5040080c552081e00e061020942c1d49182041c0302107062000c40c8140c1c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 315431519 1250 315430269 315430273
    0x7090e030d0c020a0c090e10090303150b27060f031015030b010e1201091209140604050105070f240b120c010519021204060e1903020f04020304030324050f03 69
    0x1542ea2108405100da002d021b00d0140c69008000860303408100c100300444100400344641e01072400d02800400d20043c0300c801041c807580c004075140000d40e00315000c0b950140c41c0c41c003c0c11403054035000103280003030455901540401c0010701016103480610701940b000003030580d50078500500c003400c10051032170701c42c141400c00b0041100d5030307003015004080309820b85040400705054a19a0b00411001344c00400701e190403605c2c02a4951300c48488001e8134648603008040a10040c10410076000c0d5208603400508100040400294451010b020192242c40c06d8a80ca070ba03104418944004668200840719945a00304925441c00380a1322100780c481c03c01420806240740c000a2540c07041c07510824900380c040b40c2140445100304a400c003070030f42859540f41c80d80e40300c441c01480c1c3c140030380446106041340750140d8211244400a83c1c00c8036070007062406100202000e1002035000100140d043c195100c800c11801d0b84444040051030305112400307c503490030b041c10003000107410602c4070701039 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 315432769 1250 315431519 315431533
    0x408030c100e070308070305090d060e070501052505100504060203040309050603040c0b030c04050306010329280b0907080a05010b07080d15080d050304150c020a02011107090e030d0c02 81
    0x2c2c1ca000c40c2600c25650481582503442c0310b1800c0c15034042c4a810405900452402c0c032a0050040c0c1d0340c0f1980c0c03801c0c0503405980509580d080111441d0080c0c900e0204500d42012010300d84401c1c5403031140020740b240e415200341c070004407600030485004903016a00640c0000801c0f040560280104020740021a100c900390f050689882200c4585030142c1c800ba00400004200c028800000340c40c0144002012280d266840f0b15001ea40c1049203000300360358040c10084038480e05000300a5600c984170500b009080740310700542180961014002d00000c26603140c13503414140c3c0715a116248220145d0301d0700c01c0315040504500e0100c0d001640680c060907014003803100001c111004540c00e20600000109200f58000803100034014694800800752060032400d000c0c594210001c0c510807809040044c4100b10480b08041c29180d5192003d001138104914520066008840d91030003010100110f901864450700240101c81186610900d03d600200d2841c2001d0980c0c0102888202544043c0040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 315434019 1250 315432769 315432791
    0x4060f08060a0806040b060415060e040b01081e0a09080a0e030f010204060e0d0203031318230a0f0f05010801020409230f04050f100905010506010e10050d0905030408030c10 76
    0x700d01010300014200d401746c4020a54564954001130011000ba003401690140d650b000078044c0055410040d021728202034080003e0340c0101d4101e8412594407045038001c0026008140c1800e0000b009030407400e550303203030400110b810480942744c00000c50700ca80e007070412001c1c00c0601d4031000b240c0d0000d840e80108010322485902000700711000c803094462000c0744100344002819800743c880e608039560800600004c80b04a90003601000701d9104000f0080342005084440f181c04c90180c00e41c8002c4c641d100410000d03807007503010030780980c06640700082400e15400c1940036140c0c00e03881924076a401240a00000c4221303c82c4030300c420700300b082920700317981c1504850310756200041080e46100c0740200040d0030701034184254a0b050150500b41d8202061003e6002c00404100c042030320f0359840c000016090754013601030700a0f8114000c08250b17801c00d020208540d242e0010218280d5192540071200c0003d1003000544068880e04001c0c58403007031829285403500c9034030301d041680e080c10700900e041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 315435269 1250 315434019 315434023
    0x507271505060f07060f0b090903040501051c09020a0b0901030c030b03061618120c12023003030c030109111804020f1c0e1033030804060f08060a08 65
    0x4a070429a041a1600009038850920380662400a040f0034182003c80207001d080e94030144100e10301701d41e42d2200b51200c159071076480c0218010140441c20070440c15540000c551100b255030702d031059010a4420303459010641440041d40407d0821034045400c012940c0c141c05031802c0c050380340c5020081e00e02c8190001c0d659940c00741c02100240b62000320f8012040c8138070000c1074052100c1e20820349181c2e46142e080da600b07280900c06d071000d0704c08090100740d20a4054803446401c0d002001f09c4030142441102c1190002c1a54244a446100803403070403000c40140090341c4952203407030070b40d9102d41c54000500181d0f2400c4c5612800d4500401240c503050704c00e00b507084000d0311305480041e110300015041e11914854440b03125030904d4120710489289019800600702c0300103520a90700200200b803405019a103603150303584461040105c082d0400d901440d203108007001c5c0f13481070780070280e540c1d00c4400d0a0b80c05074002c3c000003140c4450003042035800164554110809598400741d55140001141d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 315436519 1250 315435269 315435311
    0x80f062d0d170a090b030603100e1c11010608120301060c110607120f05030c181807080a0e0304030b0c0901030e011802010305060d170a0309050727 65
    0x100805048014400030394450940100889a12005101c60702000400440d000e400101c82040000d4100c400400c1080c150340c142c3c3c1c0510409802001d490480512240203450380c0d10b8803000714442c1c0031581200d8610071442810044c0c554544400d49a03e000b202829505160400440381e80300b00f880404007083c07001101d045507500e2030010401b1285160500c0f03001c038000d00040d800600401c405091210b80c0000c080000c0c4141c1340d8604403c110042a6002d002c1110b0f003410517801481800320034090f145015114680081c0b548400030000c0c940c003210340505a030f501c030001d1841e60402c55001418403d0500b4000303018001c42c1414a5940d40010401c4001c00410944502058030301861b401794020504460400001b0f004008054000c10383e00c8503200f00590000f41000007141007810710146512041d81c20198200d4900305e143e610000c2980903c8041007095a10203805021520900c82c0d48090160300f001040d105100000740104100002200310000c0e140044070380c441b40d4040c0d042 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 315437769 1250 315436519 315436579
    0x50a0207031e11010516120c05030a0c0e0a03080301150206010e070507052407021b13020715050a05060f09060d020114040f15020616020a1b050d03080f06 68
    0x5282d20b4039000c1c03c5400701201c000030a4550309007020300030310003219041e8203206034440d80c3e6503000c80c02e1000c44c0300a5603480340586000c201c0801c0442c5032281c5a40100d842c0d0516070800c4e90b0691510000b0030a111b045901c1911484400f000502c00040c0018462038001c03400d00c01050203505141102c0500308002c0c02041c144980041c14000b004000c0c0120541d2581500c1810707650010b11070404564103044401000502030300d80620709a1807011003e04020768042c1400c804082103817659030095005242c1a14080494040316118064901480340314154668011569013008001e2050500805400500c118102c6042192988820b620002e141c0c1e024680701d24441105050441e29200350b4028188007560071402240401290f8107810041b043c1e6821240d9944d1510341e208c107280b4a04043d1001600200d222001060701d8030001d80f01f1700c0c40308183ca80d0710766030b0350300007000c0280105040380803880c0070040108422030607460720750104081d900c1c0310011408201c00038441ca000c07030407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 315439019 1250 315437769 315437807
    0x6170411190b0a120518030d110c06010303090905060907050304022b060506030c030f0a030302030702010f020c0d080f0903090909030f12100603060b0f0313020a0612050a020703 78
    0x601e0608181d0003006a009240200305590343d610410801000010303084d40808615041c40c010800d42104800c44a50300d060760070196051002c2c0390b1028001c2c00500a410070403c10a014001e0644400c1c801e9600a52294036412081032078640303038070152900285164801c0d003d083c02c002c9200d4118003207a60050b41103c10003d8500751041810181c40c1e40c4803108075500762140301d2003c2209980c0324501a1301c044040765002d00c000310030942e80f01409030345048070b41c02542021001a000350051500008079000204d154800540d218040760841c60001c0c0780c1d907211101c5503141030b0308100f200da000350700350000555600d040c20f80c041e47c0e44940002a4000c81d04200000d50030281423060720303400d42503540030a44d9007104244025950005560120501c285188000b503518028803504040755007030800141404d05681d8004901c0e00020807540a2900103240c90300181d50704036666010301120703103c168001c2016a410300c12a5401400e00900d141704006030001700340c000d01d00c0806480d80400b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 315440269 1250 315439019 315439039
    0x10c02060708160c05011104051c1e0507051012050609090d0c06090803010905090d0507030206040b0c130905010812091507150504030c021e01140d230106170411 71
    0xd41103810031101c1502404039403078100c1410074007282c41c0c010011200d04850400e400180ac1980106001c030310400248a40200200140c0146001c40c0d20b4440900400c02d07202007595840c08180f0b031013100e45080c000240c50755403400c14281ca030300c5134503080913003601c40c150a85441000103640701c06080c085000d111501c010402049015004907408660002c0c08076220b5070f59103041005040c050300e0041442c09603031540f080251090b0152040d40f901136004104a03103854070341031507032071001c1c0c6582000c0d1400c1281d04407030010b2441190082074001000241580350940d06420521401c0790085966004c00c4003407442d07920b9164030840050842d1202d9561f940ca03141081d00c09080e0f4405440070f41c141001c100905801c0a01c0114060003911510403c40308014107c0420f40200680b0340890140380540248116036006031143c60314041d80001c1242c01401c10052a8107901080307010384c40ea020040c85116803129070000000c4c90603070740c00c0c000d00f03140d5200c46006c01290041801612222 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 315441519 1250 315440269 315440311
    0x708040813050a30030504230303071202070602370f03081005090603060720071214010c0503150103090c0b03070305010b0415030209180711010c02060708 68
    0x24441d4005003001840b982c80d5680d100300341c1d402c41072401500c00100a0112440001e20303240c2d190b0f9034100707078181e880c946440e040140141903401102031049040c0c40c451140981d03034804000503c20903000d64121180c0751500003001b45801c0c4103800c0071003190040714011079805500780000c640d17003403460b10b01101d801e200c03841c042004061420203060703405030212001c10700d03400c0340c5102c1c00340401c030040382155602c8500b807150320401580e849070194045000218040d1042d822407100307210348c0000450140c001403003645807041681010044801905e0001c2c204a0001131a0041c540303203400034002c000d0b00c128098a14000200702d445500484c3d20b8440b51a88603a0251910503402080520b01684070032442405420440d105400b192404002040b0081c1240035130342140c038410078505481e0303600c0500b14040d4000c6030a1070f4002255141046a12004203841c0c0c1c07080103541d44a61040101c102c10a00b504c3e86481030340c0664001c0000e000c2000da01501d420707406468a0b40c00d16480c05070b6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 315442769 1250 315441519 315441547
    0x1b040509010b06160b1f03020103090c0302060d0c0917060105150403060c030c1101090b06060906040504020f0a02120c0d110a0b090303100905091b060c010c02060a1407080408 77
    0x4118030941c09031002440101040f100410850014050178480705d4a0740e0b05244900101401800300e6983c41044104000640c4240c205070000742c4030702814034000b0354a5000c01d02d01d8005540250301709071a0040e00c10b029500c15490001048030407a507145c0348000114641d00d442c418004d0034020040341c8a10110b0900b400111402958451020403280c0c00620008000f40a0f03d80e14a0000d03800007800c0480c2c2105004804d09541c00048220190300c2e11020011140c1c41004026003001d810302c4002810f13034680c80500310100b8802e44581e80e46e10451402400c2ca0450020b03600b1440d8240440c4100d410006402040c450700c1c0e04250040c454100d00c00c2e07180400f0080e000304190802e0003081a810b0010002d107002e02841c10b494420303646c89030940810307100100d404e5592640900c4100844440044e01034804110242c00070f0f181c42d0300b03030001500f9036080714411805a4000300620003580201c0c81040c1719915240e00408140c1003c0c0401003d02c031028101414003507010900142d10050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 315444019 1250 315442769 315442781
    0x2070302071d04060e030909071206030204021603260103080306040e1603020a15051602061603030507121406040c02010e071205151029030403050712021b04050901 72
    0x242d0080c0000e01c00140002d10110710845040b10b0321030800c1c40c90303828000c0002c00c0d141c006100400ca12069610803000310744200c4005001c0e0030a0342c03524000809030b101c1e03100402e2600040310100624454605020f40900d450f0000c03903030b00e640d20700404c1260b03841c1220424107480d406840c03a9641c1d160b04002802400e000001c80e8810301880180502c0801c001520000320380c42643d1941040740d891808140308403112215a011071401c219103640c0508548031540d00520080009041012001c0e0300c50380c0c1c020000c0120080790f551424010030a800c0481c00b8050a0b4210080c011068103c3c02d4451108002c1e021314089d50322400b030914010300030b4005003c0303444074804440315580d40c2d104480c44003c100e41d05941034003030b814a0342103041030080d50520031401d003100b1202061038024440000014140c4080821a407015200e04c098102070045015034000d654458480000b41446034070b03400c4100c06d20081d54003815107140400107030f940b00b0642460031100080c0c42e9039408400d40c09410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 315445269 1250 315444019 315444029
    0x6020a020304051804020a05010e0a03020f0a0306050c121506040b0a0c0b0702100b03010203011d0a09081201090b09041203110403020a03030c031107030b040f0813090f0f1401090207030207 83
    0x1007100741d0313150500512200c1c3d00c00c070f0084440100b1565100015218095441c0350982c1000300c0000510150520030206200d44138003500d030000e9644d4a032100b504075030b019160002c0940700000c000041441340308086411104e10680c0180b6928030000294491043c0c3c80703030f415071070b0020410700ca0160241481c1002c0070f0304480010070600e4a03420007501c410080401038038251401c0c1846429060520999060b5548610302c07460802d00f400c0340d0203192030020041800d683d141e255800c0060009401381030b444810008070003c650410b03042d481983c00140d0b80600034940502040301203072848500c18031b1078085060000d80e1030700d51404412180315681006c0d4202c60034980c000304241d803007480d0604060103076545800c95041c5070201c0c0e80b00c410038070014000c8056440400d0100d41000f2401103100d204200251600103182070411043c0100d0307000079501650b82c100000c00b003d040c0580c1800740c42420302004410040d00d040300c0c00240c180101c520030380c0d000c24a842018001c1150a0142c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 315446519 1250 315445269 315445279
    0x703030f021902071d0105030606061c0608070617070e0906010216080601030c0806010608070509010e040e06042105070809030c1c1704060206070305072f0609060103080706020a02030405 82
    0xc00ca00c02d019548043ea40303d200300030040a245203462403000030380c20303050b02c2c0300a020f480f89840e0041000619002619801c401c903400c20042c201e586914410000109034407405481c80368030704903010b400364030300024402d0403110050800c0480340e0312070819200d000e41210301c40c1d001e46071000100d00e004010014850a00d00300c1e07034040b4024000140190480c1d11590345410182d403070b48542c1e921000c080c0b01c1c0740041a00400440d0016002ea0040c200c034010616101c5c003000d0305c1400081c252002c00001500c00d0300194280820310441c502c40c108100040a040c40300f00070508002005845424000307400004049610300035aa02401701800c440c01c01800025500300c41c241d244080401003d0440c1c1c1102e070355410801522203d01507900b2104940c025180e1f43d0f403012030036006004001d007400c041001d8042c184048480152812890545111141c4c000c900c109560320b2404001621250031940701e040100006442001151801ea5111401507110f422a030020703441c1d070245401c119400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 315447769 1250 315446519 315446557
    0x71206080c040513080a1b08120a05070504141203042610110313060b040c270f170309030a0f03080609070504050d03020309060f04030201230703030f02 67
    0xc20018050941074002c4070708200a03210940c00200800c24580000c009210511a00801a01500d4000800c540300a808101080c00b6a240d600e207a1040420000c0d202221003030010202c501d124003a032144940c00c00c280380c541029029149035143c0941c5a100c0c0002c4101e00b0410131040c000e50f4020181041c420340c3c0110a04660100c0b003107400c6034541140308400100b5a83c07080c5001e100040b084c4440007901d55100c00d90510700e007030200442903800c2500c80f036002d8640d44a904c110b1040d0080c0d90350f450040ba44195140c9501070303211850140c0c50044250500140385c0280540c0c084400c14845030b0360036190b20100c1425402140b455540c03600651a805050001490400c0c036400e2080d0b880c114941e03144010000c41034000e841c0e160008900340301c10b00032810809c0c03800b90b0b07090083c01124102003031240012110f034003812208841c0f9401080800440d41c000d8030641c102e0f0200145025010a83c2c4660b1082c0e02582c4800b03410591a5111100e0380c0c18194121600401d1103c1d4000300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 315449019 1250 315447769 315447779
    0x6090301140906061009060e0105030703090506010807050a29250c060305090615060904090b2a03040503030c070c0b0d090507090b010504300f021302031608071206 72
    0x450f401150a64050310341c2507081c48810f4800d1141c0000e40705540c6444103130852450044079660802004102450381d80d00305200860802c00c2482d000703100d558002c4c08444e00f00401d103d02c090040d8482c1c80c8140c520240c80b00080d44070f001600c0d4400500c0030144d20303240010a03070ba41c55000851885003030306001003135100b4004201040826580245c5050041e034039030581c2c0b580e84520854804c914a40104001001c0345031040040010040007000460021141d44529144240986465415210000843c5400480c5010311a002d0380c00064407421445e02d40c8400d6128400100120000580064403204000c000304411002c0c0c111106011386030540015800c0007443c03100d100f521103105d03c1400292038455070048042290040c0c5d61507080c1890801e05141a030805198030060303004501005851030786620300d44c00824020780e0610200806401417204911707641148500f010f0040041000c0203c9440d0300308a40c610340d00c2d02121070340d80c01004403070f55000303140445415414003400141c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 315450269 1250 315449019 315449023
    0x90d020f1504120302060f2707090e010608120301060912020d0803010308070c050a14011d03010c020a0b100f030f020a090c11150603070b030c0d020706020307030f110405060903011409 81
    0xf80d158465000c80384183c0318190016416041200d404441744600c41e140b40c0040074418120075005a0300c0101e46420303448803100f60907150308078209000740e90b48420820880e002002404103254800000340d10b03650401d1801402c810f0503000300e00002d40c580d030340d010454a03a401e1016485030022141612561139150105181d0300610301910541c00c10440840c031031030320220a408031075235072080c55040b681c3e010040d595081070008002d204841c2c03002d091b420ba20300b0f0048120b2620320f0343c0035208080303403407030709964440015114085040d80c0d040c041c48102c21102c115000c0d40e40084d502d8010100a100140107205260005c4182e01d04180036581e43c0da81000c1c8c90802403038480142d4444100d05c403449542d2107401c07900c60f030341617000e000200010f8080d8001150408811800686480c4030906100160307031008400b01c2c0d1040c0e0010030001d005a15104c2e0700f503c0e4410020600810440a02d00d110a010381c0c000c07144074000000e060700303103030307500b5031001c3c03040908240c20071083d281c440c1c4826 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 315451519 1250 315450269 315450299
    0x3090b03070509031c0806040c050315040204030b010e100608010501051c0e250e0910091e08041a07120e01020a1b03031e0512070c02130e0c010302090d020f1504 71
    0x980070805036004a07c040c41e00c0c1c020501c5504003551280e0a599a84160032490780030410b100390429801c01c0040042654141480d01801d04040412034a06000d01042001507070381e1311030f80402010b00d005010607a8490102d0f840c80c2d0341c04034400740c00c600c0c0704c400c580201402400035116224104e019140d140920a9482600e510420b0117070074640d90310550380c000300c0c00b122030b081c140d04940a00108c0302000c2d40410052800703113143c2110703203403840c9000400c401d0304d060039111100041010001c0d104022181d010199a50034514140303901a5558050034511300d803040c00740401071010065a0344208045043c2c05d0700a500c4001f5640810100c01090b10140803e40014030051840c4405c03409015482505c0c16040d1f641c80d03e00848203007006031340c1c103000d403d000c2086000c3c41e856000d0b9130742ca1040500d00c0402c050000b2030441c03040c1450324045240c3c0800341031500610620721a03a40742c0303c40708030031601a1010040301c071560b00000d80845420f02c0d803100d000030216000c688482c0f203801030703 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 315452769 1250 315451519 315451573
    0x10906080726270c060403060203090f0307030e0306070c02010f0804110a030303020403060606030207080d05040203120711030106080601080d270b0319050f04061d063103090b0307050903 82
    0x54800c10030380250756526208044c40701a007040d0100410800030b1219401503a0140101d4252848049404070060a59100d0b00b81940040c0546150078240e01e82404000d802030b20320308082828602c1c2e540040c1c075080d0415070480900c081100081d003403141d041040c2d5500c0304001e00e4500d0040d12460041e00941260005031091407402001180c0b8078001c4c400c0b40c519541109803541855032402c0c12002030040100100d8042c064000d403107a402c00c0850180045500c5103202c2401401c5a4050600311a01648001419405107004001003c00450701d003584c4411032a0070040501c200600004690501c039200e036100600c4500040c1c1c10780004091801143c3c070f59070400300a440790000405886c0700b80c2e10515002d000340041000a00c2e15801080b1840d02a98180b41e00302104403054204181100d40110014205828a849100040c244219184a10b413020042000b0340c4004002524030302800c05120030000c00303c2d01c41070007801030b11501d080042c22200980790010580721744030908039407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 315454019 1250 315452769 315452821
    0xe0a06170a14160318030c061a060d020c0f0f07060f0504080c090915041b081c080403090906031211011e051009090803060f010906080726 61
    0x105012500030b00502c0400400000c4a4002da190951990050709145401000f030595900550484205041110403054043e480e4035198074854140301c029074400d100f0315015554401d662040b16030b9000b054900364100e01500507100d500320742c101c901c0c0c0305c0390310091101d80c4150031100c42d044000281e040305580c62a9030315844d0050042c4141c82500a42c0100402030300303e981c2c2d00c2c049080008569520804020840d0b1519491013070090541c41e01343c0e4203440b000300d40c0518020301da064a10100c0244140802021820210100c00f64002c800448050400c503541005c142454420741c140d00c0900000b80007045000e940780b5020201545411103c0007107544c012128182940601c140141a50980e078140d0341201845481d400419005110300707003d5422000100340d56420348207010305103100e00d075219900d0502c2000c122000800c103030384504202101700103010b8554815400d50300110f82c0c0c103101c4424100310060101d40b20552404c0d8000c1404141001141404000300310200d54040302 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 315455269 1250 315454019 315454021
    0x61403150a0f09050c1f080c0703030605041a030f0a1709031f0207060b0111030703270b070c0504020405030709200307081005032406030705041b1101051306020a0e0a0617 75
    0xf0f5001c5e407407028540c4c0c000f07d40036400080311540c0c45401008854803d10b4001805502c2e00000781c00c90740c45010070a02d03882405030210883c00d04000d00b811100761030700104400302440d48c1c5c404690002d945c000303003036403800310340604e40d074400b00003800c802589100c0c0002003003200e1170120000e4004100275a40d1a06150070400c0d954015010481d84a40b44d802540c45d1082d683c03010340c0e260030904092210500110541400d9420751000c0c103020704201240c0d541d40d1280d90401c0c855407105900000c0c895481007204100560b400070301001150794160011481c4030b11100d4040c403001800e5210060140000304201d0102e5102050b603100f409143c90140c5540e07101d0050603683c0d56501500300d0280401d88026888042c1d01c01038507440213000f001c44110a8444001c541642c0703424200d540804074078010751480c647c218000388600007540001f00030078a001840c2004468403018040e1420b5800503980c02090f106035000084014042c00c504a602c2d13560b18020703c0071645400003980b480d6500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 315456519 1250 315455269 315455299
    0xf020a030210110c0a060c0803060f0a0b040305251e030c0906170a03081807050301020a021c0f020c01120b0a03050c10020a1713030b0a050a061403150a0f09050c 71
    0x110305d06040d2009a929100409140e0f91014590303400504410f40c0410385e00c0d82c054107039075031261582c040c005050380152518503500c0c0c22031a15401100c151110300c41003142500742d1080455803800c40d0b1132041d45070340c60803100e512a078226600707400141a1918401000c18111001c0d000303030040790110001140c442d2105003207241c54802101c40140090240d0010404a02c201d00940740c500076031400f034401d01e42c1c0c0c44002a003240d10110f004809a00140a8000000000260084003602a06000310f0001070900001d4803042c2e0040101d042c00301321200300941600584c0250b4900304041c0580b00e5254480c1400e6665041481c0c8080c0f01c0c0a60141070b040c0c0920224001103c50340c010705011107040c0c400d41550039608809015807410004080000100f9000c4070003d000d00c140700c10015041c10480c00040507903101d82c011482001d5028841d0300681c0b0000750740c500c58440303c1c14443c1a516a500040060a2000c4080c0d09503404d00040e00c040c004d010a0064019000304c98501c2044580 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 315457769 1250 315456519 315456529
    0x50f0324010201052401031d0106030b071707030c1214010e070c021c080f0307030929190f0e01052202060a050c0307140c010908010204120f020a030210110c 69
    0x11254400c0066440c51260460003412a001701c9401d014100829222460b801c1d09110312550420f80c44603a4503100d00b04140f10341840125040159840e116a5884204401d600365000c090f00380b0080603036901c0d0b445400e034400d08a4102e4030f090001d06014241c582402d0501242c020b0141c50204400d1502052006004501c0c095140c1d5003e02072241e808548002d0268074000c10300f0544074030382c0401c141c0881c448840000e500c18040e03910005241c0343d00341007100c41c510740103117854240c1c5999612407040307100c1020015408940821f031080314202c0c001d555009481d08040c110625403e2074484500c040c41904218407403014000284642944417021603407143d603411020b500003808000e2111010f20610040c40c0c0c2e25422001c9a26001043c0d07036040040d08401c140d07c4907600920503803201d40da40858040000c011040081d400c0074140f01881e001803818082c000c02c4c000d1074a181c08110345980c00c0c040000c1d90028441280203084d000098480d002d0400703202803600071092664054540b17 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 315459019 1250 315457769 315457771
    0x13021903020412020f04020f03010312030f230712110405040506060702100c0804050d0b07030b0306041122050a020a0f140318010b04050702100605030703050a080703050f032401020105 81
    0x250541e0071240f5000f90f001e0001c0003141a0714240c00039001c1140025800781240118000c1d80f01c0d01c82039203112107514004044403014030896550710308003091000b24080c00510071840828178071407442103031100c42c016506d007110a45001429804d10050600708601003010384102d4100390b0303043c04156110810000356104078140254015240c042200600e84200c070b220a03001d1140c0a21841c180d00c80c1c00281140411502c1100e0b08000c0208212010b6410300464901500940007020a42480d40d501c000100494690034041c9050300407001201808820001e0100140384d000c108034100400b00e100a5480020b140300899180c2c045c540c0d8480c03044c4580070501180030700706030540d160f800009142c0281003680b00a19900d80e2412003044d5914802d080c0106800d1b00181140a050140e09003952500d0344914481d4029103020000700d180800d850660b06d41c45100b85540703d459181c283d5050081741540010341d980030041008910502c560504130300f034448541417840710024012400e03503078 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 315460269 1250 315459019 315459029
    0x5010906020313090c02030d0e0102040315020702130e12041203020c150306190b190815030a021302040305300a12320a050106050406050a0c050705130219030204 71
    0x2510b020200404c4a11340d00049250800384145c82c90003c006142c50305444181c04140081d9600040c10410006260710580e00403202d0300065007000030a40001c0d002c60310381d500b0342443e10340303942504039034800c00d10100a00c1c40084244a80b916100c440c40e41408519607021405440383e40a48412131810900d00b40d03001003a02d1109c0c1c503640d9000d0a0080741001c14001807200d464084009c1044101f21000c0c0a60506282c120080e038110480c00419018010f800941c1940c2c808d16109059100415130401d0660180c03140242c05d440200c84000a109540c0007400ea805043c5c00c5e81260020741d038405002c00c2080591010754404a0040801d80c17046090070310214204140802041100d600604000341e02e05003500344280c41500c00c036401c003a000c580e10044552000c00c2100007000c0388115409000340b46442400c05040c070f4405045841104004014000740c1302140701005001c20070000a441c01a000c09c50589480c04081e011303400109031111158100e00005061921a10035a01111 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 315461519 1250 315460269 315460297
    0x2070c0e0711101107080406050a0f0f1713050604030206041205032202010320040303020115030309050127120b060d02010909091119050a09060501120506031015050109060203 77
    0x294400c55580c002c080e8151450f070310110170f22195004c21680c101400041207a5110681e48007002c43c801480da007503054070b401c18090845480c49800380d004180c091102c010f0146502030b40c9030040180c41c40340c1c3e41c51000302b951040100f00410944e002c905580694460701d81c80b0413a50320450b090300d80d80412142c240c410341040d4002480440d6104402c62158010304000400003070807a4500803c0c40100d0700c000281d10001820020564240b0910842079200d440242540303003036030340003000c000b828030600341007110058000300c0c448a148014a0384c40401c0d0121000d01d0741d6100441e86017264400c059aa4541010010701c2e142081c00800744180c2c0e0507512200d6003402c00c0c22110061041440039030b00c3c2e83e03d14814100c0ba4692013109400c0c0054444550070503850a4100704548950360044500c05003400701c10411a41c209504554410100e0008541c50703880f81d01103403030a10003800700d00c1042e050a180c14500500900c40c001914400e03a15904800c3d101c04045e6035070301c9140e104043c0a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 315462769 1250 315461519 315461533
    0x20c070f12030c02010e0406090b15070b1308191d03030306150a090e09070512070e040609060209060d0b0a0b0a050711040912021605120c0405070e0402070c0e0711 72
    0x80d03c00c0c10541e040360302c1410070412221910012078200e03011504005070407030382c03049010960f20b01901c100055000d21419540303040b1007581c410152400c0981303860728848182d28401c9c10404540180c03008043c075050f82d084c00d00803001e0018494600318212009041606890054508021003103c0c81054040d002c0c0e000284418450341107540300c00306da181002210100462080c10700740d801c5005600c2c040080c00d40508090812205103000b0a1110701a0b004540c01c002942440b2080c60b40944c00c502d00051922090808001074800c1e40b4403940e2010780061210f044080c6503201c0210ba40064071b807044101c1d1248280c51051050004150103c1d209100010014502c0070441c80c4441001d0301c04070f21140c4a035239507405a203050304003c000d40c01a200700d2240e03403195480c2e0320041800300c5015144400b610701f0951203d51200391207014640b21000540054081da00c01d881c246c46c0a8411541c0d5941c07400c2c2902041c110707008154942c0e18100201e05043d12407000301214948a00280402c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 315464019 1250 315462769 315462773
    0x40608070e0406051201060302030609011803080c07120224010513090501020d05010b07060b1014031008120703170606040b03150d0c081618020f0708070501020c070f12 74
    0xc4060040744195006803a00c4021660b0f46a02d601000e2070071a2400110381142148101420708000402c0041c542e890401c2e1903226482c002d000b04002909420f101c6890348544098505510690b040904460940700c07000c01d07941d50000311461003040c0c401090711440081150031030a141d080c442c160340444207000070085025140d00000f1594800c0d80010309d409103190200068500903440b10090368070114a81c4144990340c040c040d01a031007121083c100c242c8404019002003050421120f03d0640400000c02d9070001c1c04a103070181007500200e131031407048180407030040c0d401700004030000340100c0000000300d00c030303d18900e000303060007081c0c18100381c00d0165603d486c0e00014105d40e1402030200200f989078548000c05d6600310301624a07040c4060410910610b40303c042609400c400c141c104040001c445240b0075650101003244002d47e9072600748952003040d0007942001307080c0d080002000c00410a0560003041d29044803400e5851007582c540014800003d203204e96240a0900180100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 315465269 1250 315464019 315464027
    0x509010e01020109020d03030c090b030105060f0c010902030a0c090f060e01030f05030f0412020406060f080c0912160e22030f090909140616020a0b180610050406050604060807 77
    0x2000e850188000108030405030005054041810005d0700865503410300044041d50001108018100d4815814034551400020a07103074810024284d80ca80700110b48007050000030f4200701c60300c540040480300b08500608107207020000c24442c9140e560f280c50381000b180d4031507000b0f8200726075120304c0400f4147e01e036031101320600710340e0481100e49010030001e10301307948804030150000c0c00a0f030316200d42d01d07501881030004444042d00141c0c144801e05004184007a80705070b4060344404014102505d40031218041602c07070f503100080d20020301907450100c104400c1041d071a42100d00c2103c00405031f80700c601c155030980444141510306010001081e001181c003407400294200c9881c07921105031039403040400100c850804c2d04803400010242c000070381c01c100b001882d40080da003000034071344015200c00196a402c2034900042c00c030204000010030400040020b00c000c55641025a11a49401005800c800202d8095544541d140c45004555420100103035030035590151141c1d81c090710b41c90410781e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 315466519 1250 315465269 315465287
    0x2071206060f060f090e06030a02130b03030c060a0c080108060c1c0203150a06080c1204051e03040314031603080604150801060e1302030a022101021204050616050901 73
    0x80e0354140c5400d8002958545009800018030380c039034800b800288824802440d0075040d51205800340d0000051101640e000700c0c00003400e950407294100d40c001ea03202e048001d484c4c000a150b40c940030100304291000d001040e0030384036249884041060b040364060a4908103028090403000381e1240d4005408102114000e10595241000f4400d0391014a0740c4d0209980c8219032541190318032450a120508041003501c0c06041d140c00c10045925001c9410050f6005507403a2517003400842c0b010400b40b107014007541d91204855076240c1d00b0400c032180d01c0c0c0d03a030750b0091100f00c07480f01d80107000501e20308010080d0383e03a000001c0f0011003440243c1e01c040710f00310340180c2400d0784940d4400300c0c4880011510001c030014880c0d10004038040d0310b06820080d140d607008000c05401d45035601e8040041c5e1300881c541410a504661070105994800502c050b40340040c03444031500d61000502d40c0600b080c0d150407502c01c5108104a0303c0d03694a880a03480741701c2e002d1120380b01080307050001c00d0041d8001d81c07100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 315467625 1106 315466519 315466523
    0x204050f07051903110f071415060103090201110f0f0f031903020717040905060a050f0a06140f040311101107030b0a0e0f0c0405070f020712 62
    0x1a100c2d1140200c110a09aa0f00a0105000740030740d00001941144100c02ca86901024010a00513840800142e501143c24102000b88400c000760030801004400742040c402e84818005401500ca0392408a062141458110b01c40d03c0c020840b04010b0300d4044014240303c2c0f104a2000c0c14040c0303441c2089401d070801c00c000010719150441d001210b036034501c0c0059440d070a41c00c000d0760109120700b030410300c2c0d44000380018803240290040d41c040d01c070132502c0d8032201c0c0c1e8500400c03590460080809410003001c1200300080c1c1c1c0103201c81c0ba44101c2c204101403401c0d00d1160902d0740c1d5031254004990341e406014059000d0306201c140261101a81e09001c12444d0480c00c1003640e81c0341511005000d140c00200040c05220ba82c1c003c1ea0001c810715003140c07110b111004034240c898000c118014051442c002c0098900c61107085100144400c1c1c2d0045c007036607070038400f580000903501842 = true := by decide +kernel

theorem cover : BRFrame.Cov 315287769 315467625 := by
  have h0 := BRFrame.cov_init 315287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 315287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 315287769 ≤ n) (h2 : n < 315467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
