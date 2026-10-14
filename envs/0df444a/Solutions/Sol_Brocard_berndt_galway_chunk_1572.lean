-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1572
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:44:06.466826+00:00
-- url     : https://prove2.me/submissions/c2b1de2b-fdc0-4ffa-9125-7cb12a558390

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 282553956 ≤ n < 282733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 282555206 1250 282553956 282553961
    0x19030b0709060f080a0b0406080d050901080f0103020109060f0e091e0a0501180209030a06091a0a020f180319050d0e041509091506090605040f020a12050907120c09 72
    0x10482024000f04000caa4205030308400060ba01204284003c1118210000803078058030f1554455000351007009483d402207504003028210100003a40c0303416240d03692800042c9403480a00c070281c04110451000d011040c403502844483c10b0f100d0404800000080010815800c0121203c900582d6904901244814070724021a00460301810602c00303541030003102404111a0311200010f141e00003040981505c0c207208001d41c49804c9202003200c14510309106c440c80700c40000402150607113400060350201d00b44291144040b03060113075400c051486103c2c184203420690115803520840000700503031514a41c010050a200700040d1180005914000d0103c0c4803441996200c0c5007001086800745c80d80503c0801221840f51022a1100c0c0500748800648083d243c030307143c40b505107074011075982210340100b4211030302524100180c2032080d000800700e028000102c00011f0807080c0d20300c0c944a403a001650000e4a54050740c801c1991100e80000c03498a0441c2203800b50b140e01810000b420706d0b803 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 282556456 1250 282555206 282555209
    0x315050a02120f0901110313060624050912030a020c010e01020d0c0f080c0a080a020c09010302090609090709181a1905070c150e0c0f03120919030b0709 67
    0x140030550900c42c2c2401140c0d03414400400801a80d94a0320015001c80e409401050a410301103001a69a0814102600071303862520030a44110f170410900241d80303481c8007840ba1f4800710720481c921024812030001c440315400002c0e0705911034040f0f1080b81d15000b0601c0103101012240d0000e1086a0743d18002419880d000728295055411104800c85026001000d00c459940c1c000d44180045240c1e10f040c43c4140102110020310b0301c0b41c426034000300518170009004000d01a000ca4580c0d5520400704a0400000d000017508503c100300800c5590524404030b42d0410004000d6400c5985c640e400d07a000c441d94031841c56041c0b0f100c044514188849145a00c528610202800707810f481d020000700d50308400c28000c40400c5ea40d580000d003025115495120215034429105d95030001000e0081028188110310300c1e800703000d83e01000c1c16620b0445000785c036524002e80901145c00b01d01130108442d8001c02d50306a00b18000c0700d042e11920344040842c07005140b10340d00301c80d0f0a045c0180000d040c11328a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 282557706 1250 282556456 282556471
    0x403030e010b1011030705070803070c0b1801030905071e0509090a020306060d0f051617010501050f0114040506030c041508060d061a131a03070b0a0804020613031505 73
    0x10030380c000340c2c01e49440c0d495000006182c00c0040c00083c00f1000d0600d10b200e080c01c050058083c1841c08664400080018128540030744030504d4050384805d20740b45d89200d5200d0782c6000000e00350200c02154001d400c01d81a25001e6416603810030713a1442c00c101e01c0c0311000440a14524800d40500030f0f82740820341c0d40d400180ea0700013403202040d150f010a50714000500302510400c7e112000ca000c0140a40340b0801c4150303c20150340d03a4440c1c007481440402d03030b540580480100601102c0c4010201486902d04a4200030000900c15240c01c0c015a00347e81010428005e036401000003042540b0380e840298040c400f03000026a4035890700079410281c00d0a20305801c1000801414444035941d90084035100035001070000660121078507140400d424005801c41d0420b080d0600c0412282a5512610624111400c09001d21015600b059243e480a019915101e0024070008100700d00c038100140e031061000d00740c0d51401d01102881107407000c80d07600440342c400782407440d08803100090050b241c01001c13 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 282558956 1250 282557706 282557711
    0x90203011a03010f030318090c08060103180b0a020c07090905030a11060408091504050d050709050c070c030803060a0f09051b0403050a0212120d05090606030706080a02030a0b180403030e01 83
    0x108005000d041c4205d20010b010420310300c0d4040400c1080b0301c00000209880c1e80b04200180e10940080c3c4511002c903151404640351009102d40c10145608101525900805142c200c0c1d444004000094000d02104034640c4985800482c0f1080d840c4180c14044d8020301c021034441e0300c0f070031004045960303120780070483c0d0b0011003e10001802800c2a2a1219021968044055140c41c000403607400303168009944140b004004509201e008900070090300d400c0c600500c46540d07520002c240324840c815000300102040802000402d00c014091500050014015001980c1d02e09003400f20205540202e126150b43e0340a008042510303205610007a86200c410600b001e1a41d190745898048040d0080d01401610031480480e075824403040d84c6240d00800c0060702e0b081480411002000200d0300e4504900c1401c000c07034440d1400168030710480c2c01070b6071844481d83d00d01082e04041e400c050b220b440035540f541400b000b699901e0410100024420286110915007420002c0981b0280d00b0314640e141d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 282560206 1250 282558956 282558959
    0x503071e0609080307030f1e0c050105090d0212070c08060106050c010b0316030f021908030d060b1303031d06030c0901080a1122080f0307030f08010f0e1f090203011a0301 75
    0x81c0402a038083c0e50700350800b15201d038403081d020b440e001080c0243d55034402342c603013103a50010b41017100900c020307018400030000341c0e482e01790740b60f516120400c403940540c0c0560070724520f0105402c0200a403500c14150400042c0c3d5482d103040c0380c20000e0300107201284010500501821003445180c0e40c0682c2100200301c00b28820021404481d140e000c00b503c0702d10100988415500c4603c101d4500d041c5003024608107542d05c00d0751584076000f01900c1d03880c85003060800a10f50007840705840c68280c9600c1c3c0911014510b80e0b068820520003059040c112102142d006c40726a1680050742c85061555405a600d505410005260010042074155510301d098845d001d8502c144040c0d942070010b82008641c981c000e82c00c0c030880782410781c1c0121041d209400031803050000200250108620940b1a407403d0b800310070042d07440507403d014403107440c18000002c01109040e000d0aa0b00002c000c0700c1044603800d010003036201c41d03150303400004855400000400c103800351201090350f8001079218060855 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 282561456 1250 282560206 282560219
    0x21c05010311090c2a100603020603060d1419020f010f0804060e010e0f011b17041101030e010f091e03020c150912060f0109091208040602040503071e0609 68
    0x1c4682c00314034012201d03140014940d800c031004490242c501405a0903c0c00e03020940180c0d080e0784041126954010303600c04058158841c010901960350061220f82165184014400181401c40050700e96084201c20041010018403004100100902c40b49001181600601c03d030980340340e01090401810041c03980102d544901070a4120754016400300f50018041c800602500101c070019509024070510390454030015441505006c002e40881e02c04a03000c0300042e40c5074006080c41510014180c4001400640480640300702c100e014100016801c000e2019107084600b95050100b0a95840c140c003814070540d85400715941c0308412040440d001c00b55002074031840440802402594500c000d071070090381c100251040c00c40050a00841029001060f03507459005403890400c0e25404000840d20340114041c0c1001359802c08031a036540c00034064110b4164200400c16204031380e0030f0202007185e07602404a01d00070314403080d664124182c02003003030501e95115400181802007400081091 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 282562706 1250 282561456 282561473
    0x303110c1002100b010e12010504061103040507091e0608010906050105031b04110c0102070506010f09090206160f051609231605040f061e1403060d050703060f021c050103 75
    0x82c0c0340c4240000c101044d020b001a0750301d800322164554007000750b40084501d200c0551020b0300c101e00403c014081040102d444d1856444140d40180140d00905020f04c00c0300d903542c1010700c3c003810a4081d01440c8400f49405401c5420076001510700340d441d12030540502070300e03000310350151200b02c020b0503502a031038106001ca84406810740b40119251396208168640c2d403002e8507a000b2840000f07541c0d035403680ca001d03926000c013401a00c5d40304ca000000894819050700c10000000d40c0584840c0c5840308024100400d0254000200c9400304140104400030b4000d02c40c805d400350000c2000d0340d00600b409580c20507100300400250548401000844c1031040c49000035403ca04070014484103003040355400c480c5446690030840707034660b1036017000403010344c010741104601080a50502200361251012180039241d40e0308201030400c10700200e60103252488281182c10300c60001c940718036649981e8101940c0420250600059000c1400c4400703141103005040241000c400c00c0050b5030555491008 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 282563956 1250 282562706 282562723
    0xc0604031d0a051e0d0203010903020a03140f0a0509190806010612020306090a05090f031303030801090221070203040e0c1809010e0a0b040f090b09100204060c0f02010507020a0303110c1002 83
    0x150400200b0042c113a2103401722481c5140d0068000d0080800b981000f035500d8061500031000110b040b0b000d42c0c110303144603098a03404504a00320074a4620120303000c461580088006680c8819640e00e00500c500c210b102d850010060600a000300758904100a4243c51169420303000003401003040000da5038a844025920029a1070700040c1c40d180c0a501900c3e025021501d40c3c2203201c009540301d401d44c2c04907444070460344a81e0300c01e0301aa80350400d98003a400380c00180c101040c12610381c218040c0c1d0962600740e005e90603104590802e9556040644049020746041c1c480090024084500c0701c2c1e18090f90000800665101e80a5450101e005656090081c4040c0410ba0f94203c20300b02d0b0f070354176000642030050404c5c0030300c201055420b001c40341103000d4031881b105100e01440300032440340714001d9401716841900c0d44000400d15403110a21100002c400b00d04010041001d00016950130700110087c5002e60750342e065241d200382d40c3d5031801c49204106440380b0112948800c000340c0c0013904a8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 282565206 1250 282563956 282563989
    0x20109120303090b09060a060902090102030d200703110c06040e0c0a050d0c050306030c090720070f080706120204270b1c2a0314030c0604031d0a05 65
    0x11006150700301100280040380c0d0080c42c0c0d0510906108580070300141e00c601440054100300240351380c13140c241080344180c0e20b4182c0581c1081c00808046800b03540400b4407071001039418192000104400f552a03440520300724042100416120000d010800c85103a40c0c18051f24018a4241880308002d01e0104c0148142d00e503420004105458500c6a01503c104800e2400c062110945480000d400c60b00100c0382b00307000344201c046840f841c0c82c6c0904034900405064036880c170b09250b904842417500041016070001440741002c0000d5a104001c2a2002004000301601603c0d06200c8018910800c003946105064018001800030b4001c010305090000c66411428407105513501c03501e8050321003032a8a03030f40440300311508401c4500d028514401241305440c10070084140e1545091111100052640d082c901802c0520006185a080200030b80034002100e0900c0c1711600c06514151301200c08600040501200541c00c04900c41c010341281c80440d5410011410316000c141e500c082c11030f074036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 282566456 1250 282565206 282565229
    0x7170a0c080c010e1e060a054f05060c070c050103022a03180303070c0e0718060519022a0103111602090105010801030803040206180904051006060c020109 68
    0x908811000358400d15690f06071100b070341c010a80d210460142d03000320720361744002c6000340d000160401741305119aa00c140d4070034907881900c070001e41c1c9030100e402d4010b0320030700e0054071003030248211807282d1940c035124030a5042c0d640d421105840d100d4141500170b48004c4180c80b0500401b000100d882c0d628000b40c1c0c10a00c1d0050711140754888044c800851100344001a10044c00000c032560350110050040401404012680140904c1815928490385001038102400c0003014070000f1020080d040d04041ca51604201c02c922071000e9a180e403002e42d002c80003041c000940381c5981c084c604a01c00c640070b0320303001a10040019003280341e960740c48401781c094401c8001160210303a82c0030758031820821400c0005251540d484138850700031102ea82d03000f40d108003440d200002e907640c81401458103895200031824155210717642884280d400c8101e034103a401001c1040c4044540b40c0c5284107202d18050401001c2481082036014200c03810754000340200900c03030a0324000f60b6000341d075103012240a245203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 282567706 1250 282566456 282566467
    0x30901030b01090b0d0606030c0e060706181e03020d030c08150102160e06030c030102030903250204020703030515040b0109050603100806013c0306020721030207170a0c08 75
    0x40f00c80714441c0e00500c442680200780030f055a000c0da03010b80c0a40f901030f10100b21440d5000c00a54242c4440110258840400c00c442000524140c11401c0440c140403403850040d00303113030f441e920480446001540400c1c0411449402d05604100074500c625080c201081102ca0401c0001c01640c00100003681200c00c1c0507d00c4000c1c0d00c20444510154902e0701707030800b01515000014050351098840790300c81c0c864018520310a25040c8216801115440c009610b055440502200c010040792408000003100c0007100c1d0162710381e800100030a9200f0b590003d0385103030094186410f0040031101c02e000394542844500036076041800b113001e407082104c15170707100d40e5124075040000c1c0054001180c180580800081e14400840c000c8a0344d03901c0301c2c0400c000d80000a10b40005d40c4494043c506403080c1d01c001000402c0302940144403144c0603001000403514141081e8980000c61140f200010360300043c80030611080b094000013402c40518064608009000c0013812811200300280540d80001341 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 282568956 1250 282567706 282567709
    0x6130b070311060939010c05070308040b09040f1a04090804090608030915180607050a02030106031104060602010203060d06150f03050709050f060a030809060d05010f061709030901030b 81
    0x20340100030410b2004a800500e020960142c0b0341a541942550001400d117a5280d80c00340910070b20b00b1030054a00d0115210411001114482500c28045d600c6008111000c40800c0c6800003c101401c1100852595285940306000444900b40780c01c580040ca80040403403c1140000ea0400d00c8030210740125100e80c081c01c5c504454442c41d0310442600c2d00c0e150000450105c040702400040d4000c45440a0840140959002ca44555455026244507900c05d12441d0319021001c4d18546000d0401c96220044d16400704e801c4030343c140c000f0f445c0381c059002c515006180a020344405011544001e601f5401d081e0701042d40750300c504034024080c6844514504884034143d84100c014079004034032003159036403801c1464846000d402003640d007900700800520b2542044c3c0c1c105024500c040c0100c48910324584940b03030140c2118040e25400f4000300601c1c4210b0f00320f80075180c007a008d10301d19910454a01000580000c000f1001410400c01400805c10841008000d5a028030428200420405940d80 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 282570206 1250 282568956 282568967
    0x17010b0f0d0e0105060111070e160c05010e01050901150b0d0b06070c0b0307030b09010b0d0515040603060204080d0e0604030b060406170a0b0f0105030d0e0d171806130b0703 76
    0xc1401c84614904403641c442d9032015000280514000e80301e000a1030b51543c01c15441d1025030042c00010340301d83e801700e800d4a69620a00d00b94000a10784001060320980d00e0a0039030303010440c040c6040e911901888a14034080c440c28030009400c08003d0901450100300c07000714001e200c541000c2c651f44d0889003145450340c0c412240c8150380a0210302e21181c0380c90302e0700b0742c40d001036031103400003807811401c401181000c0324047d05940d06911520705005400c00100301500b801018160005c030300c288a10780030b456034000c030005980309078800f5071603a08126800c0d1410583c00031510400503c9504900c1c2c5849090445054980211500b80c1699400c408070340a46541d80c000100c5e884a120300d0580b40501146e401e01700c0303109599083e090746850030749059000003030050a915402c05030800d41c005018200c012170750346001d805e0404405040c0c40c0d0000e200b94100c45d600c08090300050940300c1641c44030f24031000440480d070080c00c0c02000450710103040034900420a01c840000340590505003c0e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 282571456 1250 282570206 282570217
    0x609030a0605160305130f0209070c12050714060c031f03080a0e030c03010b01120e070810060305210a03050603150a150806090a1b0e010807060f17010b0f 68
    0x8050000f410000e140c044028101440d120000f0301c0d10010440359401e44002d140280d42042d245140d07200303680c00300003001101403c01030a02c0007a43d14000040e10350940652a0300542c0c44072a21030280e0700703080950f10f024088416503074001c0020480405071a10a0705c1e0820324400c00314021581200c003000940740e0326040980364103c04686c07106200c0d8406241e20324180241c0944192003011814503003a2412110031901149064842c0100d0442c1640206a206103680450784816a102d41c02400c00c285407010154541d100c0d4011b2051040070490000004800f0001c2c5e450b4501d5401000d001d400340da8900c2003050342754000f0452a50781003103e80c0c5030405500c818160340c185611450020009000f80c4103022035607150001d104003020031040c2c85400060b0240441e00526541c500080c920107510134a00b0785960404100f9245080d1264041c080744001442000d0074800050241c01d06443d601c401c003c000f580081c1d98920013240d031070440700c0032012540c03140c040400300b1000340680e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 282572706 1250 282571456 282571463
    0x60305060705130f09060f0909020d11041d0c0a0e1510120507020a061a0d02150c0d0201060503010b060406050d0c031d07090c080906040b0a0b0a1202100801080c0609030a 75
    0x1107400100301c5401c00c0d88400200c41c411f00740f0195045d41c0da0242c00503a04204c038080d40c0030407200404404294584c607000203c410042000410300414803a00405c8030048040b40c0040c0e02c07011024810b4144042004040c191b4030f00c20b00010714201401003e00310042d80c46600415908014103055400b030250362042443c2e45074103200500e4034180c02903407041030364010799543c0e089c44880241d082c0015140300d04c0c0c250282c44440b03018029020b1180d00070701041c44910441c3c04221030900c14134280f001681e803180a60010940f246050101400d4402e8400f0262003044208030820409412600b11603c0c0080c01d0342c041036001d140c0100750010711400703514040e881541d4030500310032140031811000355544240c0400c180c6e03804140850f40e00000b2100604140c1c808000f02d401702d02c0d00d698059020309641408100c003580351020030060714150b800121821048041101186400d40c41401a48e08a14080406614003984035644282c818a03041c05208002001e0f030b01384c0c5042c0b081a615036003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 282573956 1250 282572706 282572729
    0x20705090f0a151406070206120c0d0605031b011805030d020708060a061203080c042403140c09040b030a02060f0909010603091130010204080f0106030506070513 71
    0x180341c0500005000125100422035142c83c071180c00c603c50104010b002e0720601c0c000ca41a180311841800000e503c9008180c0e484041030000000c05000056181d10aa14585130542c507550202114030a03291242c004502c00d4104032810802488040c1c2e4280e0420340034603003400c0c403503100c903041050301d800d603040a9054055240e0219901350000f62140c1201c00c5902186c10f250354a030b86000888055024041e4209000740e1001c0100c2e104400f1240c10017908103200745010b5540e01564101c24004803441002644015040310141d003511481d0220606203001400c0f6150918240085c1d00c00c98291170303c02d0307569144c0400d25440030410751090300d50144c80da40e96a00b4200300320016400c200440792103015100000700c1c50384c0c031a0180d085650380c0890351440b10740c004010000c000d0341c0b00b6284040302c0b2045450b54101d04120f11a0805103500d00b00043c0d94600f816122403d00204101e01020b90381418020400101d0004006600040c58a006519038180b004078810210080d881640c0005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 282575206 1250 282573956 282573961
    0x509041712012414070f03022e0e010515120a050312010e010605190e0f03030d06050906040209090a020d0b0a0305070f121e06110a0302030402040e03040f060f02070509 74
    0x1540f10700900711040c83c1d800c000c20010200c2e504031442090031003084000c0304140403000000d0004110801c4852081c01914040d5022906580d222403040b201c0116400c0c0d0407003860241ca0081c0b00c1d28811803807200091004d40f0b451400404411500b04840340a0390400f8980c0e40100020302c400003807a41d201050703a40e540004507150400c01420b005003440c12102100008001e4010000c661844269410050224450084c20384582c41000710701504000741c414410441e64003840280040689450000740140c140014050744402c01411940501d10401c00f1050641e1802c1000b84d01416940c0056030794828600c01ca4003400001c04120f07001911800b01000700032002c01e5420944014403e41c098455541084408032600198081e181c14181c000842000030450b0320104071500800010880261a11041926500c0340d400000025400320138042149044e014100c519440c45d001142001d0604815200641f0075210758001d0040c100c106654183c0213001050050400604038445403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 282576456 1250 282575206 282575219
    0x609011809060e150301051e0403090f0605031501050a02070504230f07020f120a08041b090e1603020609061c060e0603010e15010b07060e06090703020a0b04050904171201 75
    0x70b02c0d0507100d01c944002082c0006136035060500c038091140d881c6044c07428040560b41501d0120031805071041d001c00c90b00180100e4600c410b5100325004001560b0341d66a280b40c0b5804050740d00741f1001e411030400c45d00b001002140c9034000740d0300b402d80d10704580002c0c81040b04204d40da5004401c0d4800008507000101700700b41070401e031907054800c00c1c85409503183c0410700e14a25403114404808541c80003030a0021400d92032003840300c560300901c00c1f0030000c0b40c10103024107454443c459038003541c5159100c0500f078421180512a89c0e00c01d440d4a4080f10b501130555001070894080c528030180200e8010484444104188200511030010040104812515448ad8010740c05003100c001d404be60901100c0c010690000641840805454820000341c0c0d00705801c0342d140c0d5000d90825180c590300c8480350301b10710405003c02c50050140d1801040414914030501c00341083c9580000580801408104056240e02c640954410342c0840c0c51540f04c0c030941407001481c0210204400d19000400020907030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 282577706 1250 282576456 282576479
    0xc020105031b1c091412040905070224070905060306240d0908090a052205090109021f110307110103180f03080403030b0303040503030702130b1008071805060901180906 74
    0x141e0242482818015031070340441c1d070300d2002d41d1b00c808403c013003003104102d1410640e03c540c0e0040320303a20645006c1044002040c2c00b000328003107805d5400f03409000348100c007a00104814014201550040d003146810000a010800d080800040500d40d15248003420516081151021042044104240d0f500c9082c1040385822000c0d0300d90107005070810116203031070b000656452030b40306820746800348188504036001800010309040350319901c0d02940d00060340d03400c2004104403004628826412001c2c3e4005060a51110004d80c0070740080083c3c038041141c03442190003100c0203080100f082c4404480130014407404660207030a900c040c002400030107a200100c540514002d07039040c003100c200181056100d21803031083d6541940300f001144018207002c500c0c0154104050400240d40011101181c07600c60040520f90010b1182e208011506030408892903425400c0160040321904240100d402031184c075901c5810b00910007110040407102040d0031016000d10783c1c00b8048a642d41d010101c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 282578956 1250 282577706 282577721
    0xb12030a03050c0412031d0402070f1205160f1712071805010e1306052205071706091803040801020409061508010b0304050c1e030606010c020105031b1c 67
    0x2d040001107a15114007000391401d039202000c0440c41310190b80d03416910f0b04284550080010307504c0303601c0b140980d5144050204140607100d100c2001800380707046c01d100c0d540503888100b489000d210341c41d14441d15405150380d05a00000038000700c1300c141400032282000c505c1541c4074513000a501d03504103510301c3c80103000d5030650b2a8181074070001e640001101e50030f030040074009440041c0400d06841d0180700541c0ba401c20710f20001c3c4543e142c1012130b5083c4c124010f00640941031203da03a080340e11510038a0b03400011450500e10103800e0107590181c1a10150680d482241e45802080203001b00901c40910220b86508580d0f0b40c503a01e18641d8041d4200c1c0c410010b0f030307074900400051071840d145070241c0003010613aa200c0b00d0382e0078054150075a070006001a240d030710a450b0685010788501030f20940041240000e13800c4552184205031901c0401400c003410411341109010060360414162608500e40c258100020800d441050425000d009500c00d2240300d000001494011142d01462 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 282580206 1250 282578956 282578977
    0x4050408190906270f03050a0b15030604030804020301180311150c1b070f0b09040f0b18060d1a0403020d050406050403020f0406030f1b1409060607060b1203 69
    0xd0007281c41c48007a0340348556840f4120110b51a9050901292210b01e0744100078640c3d0741d40c1403140394852a400b62900020303081122160b00100c00d41b018072624510055011a80000d51f0010452010120340c603088041c00060a10801c0c0000c641103681c00e4001041d01c40c2c0e805141e4a040000e41002403d03150300c03e4400845014402012700045404041184540554102c0380e02c2d0207003a16031112031965032051401d003401038510118001c10071880160040c24035040342178030b5041c0318007007000b129001c426024401c1e19101100c0f1881e01c400d03905140010816658803007550711040829034407548924000c02c00d24900304000003800c10540c1e041d000f24040e17400c8902c1c000303002c00e05070b1380c511a0780112008500241702c1007005141100c1c541070204e4001d04081100d507504d42d19600802181c020884030301200d0300303c81103400103801c030100040078840c070b2030b00305c03a8210740c080354880c54080c00950107490001a40310030700403a60086014802d0140001003110400b10306162290042401034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 282581456 1250 282580206 282580237
    0x12040606050f27100312120b040b031009080c0109060603061a010c08070812150f031b041d0708030c060109060b0a0302070309091b0201050c070308131104050408 71
    0x942c040c0c2081101085412203c0602420b841c625a007000b40f0141c0043c0781c0d440114684201000060103001c00c0350501545803580c29010f041208036500f41d5038203c030064003c1c1e25100c03981c2d0700ea40d4002070902e5511076040c400902103003241480c604521461004645540c01c0062442c10007005510080440b4002c0008010034003a41c000c5840910134100010300080c0a0303458400416100d500410a481c41000014130705205800b440460480807923040500a241032140304c95802c10758100e041640e821806410030070038048200540d003038811066070043d82c0e2812a911201041030790756000b201c01000711000181c1d141e0f4400c0e41d03948042c0b5510076501441c0000540012140240b1040d140b20035441e9040c5504141d045009421501080d8104040820000b0740340405106000340040030b08078601100700c0d055070190070344101070b1002d183c07118100440700200c0e5008909a402c02501104001595042c0c1402000c1090740b20a5517445894542030104004862008094214140c1c190 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 282582706 1250 282581456 282581479
    0x100801021b010b0a0806070521131109040b0c130e040609020a09020a050901051c060608160513030f0503040819060f0915020c19120206010e0106170601051204060605 73
    0x910a81305100c1c0f240c11000e5100f0300120701211b01442c00ba0840c41a40c035290038042400f1400707580a0f0809440c0e03181c0003551402448140140c1d803105458506054a00381628107240d07441d00100480280740118022010542404000d50405240000d200c2075a144182d800c160920300c00a10072241c1c120322a001023000014403181500a55200c2d5959441c1c540c01c0c0207400340103540a50010220034680c0740b010642203600340c1c00d8031650000d0b001da80c1d135200c4685001b414085113003405241c2c503001c0c080140041c11009104801d01004c0d25442002030318012800c0c505645107002d00d03000a0742da401120081140e0000080d00440d07000d000b0b04080c4086041019150201c0d110301801408010000300b0325825012035400a184018010b4101e580d00760420b040c0e003a440703404220032640820042d281011444d0f0400056000d4100315201c0d17041949041c1e00a00b50250414240409a9020000500581c05003081e1040180098000303505490030780f80c0200180a603006840c0300d903c09100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 282583956 1250 282582706 282582709
    0x5010f0506120d0207060c2d050f0316080901020a120507030f080708040f1103190606090e152a0904151d0405010b030d050c07060e18100801021b010b 66
    0x1940f81980215030054030b101400c01e81c0455007200415010344506207100001c05ea149001021800ca5898400c030b407503c09039139803810604029220381c040800e80c5c000d102d030703a0b501c2104201500301240d2000580c0d40d902c3c40600143e043c40c01c40c45014140440400f95090036039080001084040e1080d070314a840310700d0300030081d0780c039400960b620000030760070384001000151140075000b400d0f030040b50710808010747c003070000745410306c4264440551124003048408000c11800f510003e0302001c2d00030312100c4030740d00380b1130340d200f170910304084449007040040f40905007400044207807044401c0b5007151500c40300d08415043d505c100601c078085d5141400e5201c0e0350038210303290415200120000480d16400a01c1d030130102c60064815541c0355a0380b070302e510f1280c0e401c205a40c0340c1c8009032943d41c0c5540c580c2d0703ca42d060103078940c4914180300309005009490340d102c50190035880030440001d10030f81c0f1440001b41d15040540c0002c44191b00c00200b5451a10a881e140501c40c8200402440350340c42d54030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 282585206 1250 282583956 282583963
    0x1006020708030f160201210b01120902060a080703060e10031401110f1308010c0e0913050a03030203070e0a0806151905010c030216030b0103060f180b07050705010f050612 75
    0x40505203444044c09810300d540d065a000d04203d82c0149040c0395100d0003944680440d402800740011456620308416409503007110034030041100310781003005600f000340c011a800d4800d4046d40c80030820000009000c1d00d0003680074130050b04060900c503a944c64801106034409030a40000c2d0380704151981503200412050086138807074010a8121070030074414103060151900004a44001030134401008140e600d070900c00d04001001c507544040382c41c204101445030307403100642400740c001154000f40001c2040024061000ca03410714006980b50784000040b11421004200c1d00d91000030741030001000d400000e0214020f03040410480f411034403180400280d40f10343e100b1126000ca204504014640c0202030240071180280140c4240d010740d0801c008201c65241c000311151480b0720014030070300146114050040e4548003040025003c440c0c40c2c000c2610000000900514401c0b00080c5800c0c8280300751070340340c0e0f840030080c000000401c07800c502030302007190b1480c00707006d08a184a03110700000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 282586456 1250 282585206 282585217
    0x305011a0603040f1704080609060414030304051207110933090c0c12030a020d0f061412030d0e0303090d02070e070f0c120507020918101a09100602070803 68
    0x1007001c2280f0039290740340c805c0c016614441170000c8206020004106100340005c034032801c074400251076541b03418a415030030b118141c030003000e89510600c2040000307400040d0f1200710110000c0710a44455803450507070030052000301da6940011807a0107200c02984450002d8030f10801005c00441b6200d000007500e4100da80c5011140e47c80a0740b14082000c1070400b000500c140f4013000c00f034078035402c50b8403104444c65000380d406111456000581c0081c04c0e081381b1480c0c00c0141c00020074400a490254010a0340100e802c10510564100d8109885980100101c44441c1004242405080822503441ea2641c0046514118030301a043c0131091451000c9520011340b4128079500110703885014040f162900c003d000d04c014032000c45503c8000c00e2a0080c81c0754605059074440b51783d81c2141c8140103003440007900c035400756404506011340c85240803428a480050000001481000d28180b03000f1001c0040c00c482d0b04204c0716828885401100ea0b6040280e9245408545800e071740e640415a691050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 282587706 1250 282586456 282586463
    0x103080a350421090909051e03030a15050a06031503150e060c091503101e140102010506010e040f06030f0605060a060f020703020d021f0504090e01111204021201060305011a060304 79
    0x504c0c000d010445144d841013845601400445054240104c04001e1003102c6204a49860380048100584080c0e1802021040c0d11084041d4610718076050100d8516669402111309154440c0c0000100c0d165a4050300300450300036605280c0c41e60f130a1448001401a030b01e5a0360580580f10000e458040301e00103c17207010303e01401c0d9800300854005513414640000e8140c2c1e40d81000c000300010f01144010b03e0705203c0d0600d100c00049185000070106c00d41c2482006a0b066905080400071342d81c0c1c01028084080001351004510302c07807600850002007030b26400c01860246058600802d005190384000c0c032410080d240c015aa90304c0722019141c07500304e000c1c51320050340710b4003080c4018208130000980407880500441c034010088800301d010354005c221301030009000440c040000702d00c10b00581a019038200d0081020082d0744d0540c643e00d1040011402042c514500480c2c11520b50404e51f00720203035180001c100b0310f0345a00c0c2660280c03020017082c002c0381c9258002c1c0c602e06c2ca000c00c200ca006961 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 282588956 1250 282587706 282587717
    0x5010201021305010c08270907031404171309060302030706080408030a0f090204180203010c05160b0702120403050c0306060f030c01030c020c042c01050103080a350421 74
    0x34060045400c441017540440b08101c09010f0f0700304840b640c08407000703960034007810601c0c1f1905107000d115140c013008090004060921403403040000d510b4110179002134010300595242c02c0342041c000b406100d0303002d81681003114490300280500c01c0741c0c041d5040d07910032001d940d80f240d9140001c4030160f50584000d040003004102082c2400401ea010000c0542c1d45000812000400d0700060115079410941c070000340b200003e03020071481d082c4103210084902d420494200400d400c80e60303000c5100c0340c3c001400040080702103003242d03000708059254001d8007450039a44586924016841d510700c540214024803840e00402c00ca45001c0f1040100302002400901c1e00114080045001c4e00240110009500a0081d80c083c16204d40c01003005007511690b00c5218288011015002c41d01e0380300d0a40c429900d0031006100150080c1c0071035002e00e10925200688a000c0c0351152044046142001050039528602000510740341400d6840780d80a89401a8594401022000c0b80c5d5503440c801000102d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 282590206 1250 282588956 282588959
    0x6010f031d0f011d0616090f0e1006050a2a140d030b03120d020310030b0c07021f0509010f090905040b01140316090f0608030a05120c04030b010e07052b06050102010213 74
    0x160b0141c801c06d54028213240480c6180d80c0c408215000d8a000d82020302000000d808100010b07440c0b502c003070000d100e240342482c5403605500c0c0c0108101d900900042000c4030110420107800e00c80441d101d5107540003001c2d41c04585400400769621910031408030082818100802450320340491209802c1c003032201e02034a400c480320355050003540000c04002d0300901c22000400419000d6501500c220000c8007401c2d600e20040c0100002404001c455140c8140c85080400c1c3c05e030741c0181030755042d040a003001100d851004400751140682e5420241c091450071003008144030f81415094100e8000030040c510b8440e405c0d083c581c441c1c031000141d4003404086441008545115031003560741c5800141c0001790552101d05250569004044260016a0110701c41d8038050441c2040da0304400d581545a00e0b15281da035658041682c14030404140c2c0200074001244540280d040325040100c0c80c0d004140380e500102c01900702003540c28052a0385142100c04030b0194014030032160021050101c0d42d980303a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 282591456 1250 282590206 282590221
    0x1215010302120f0d02010c170103080d02030c041a030402100e010c08090406180b010216120204020a0c050118030e0315010b0702120d05090f0a060806010f031d0f011d06 74
    0x10724040401440512407000d243c0319440040c4509603440340d00b5800481c14800c400da0040c2195141070b0381611074605040100300040940c2e0803509000d06e105000360720380c0e81e05001c0c4001801503621200914681c2610541003e0186000303500c618401c0f20440501001c100003118018000404280070404e9030519502080407100902213004c001840461030907258030341e01e44106c90030950302140079215085104250380620200c03000003d02158018400d2030b01c00406000c10010001a00850f03002640425071445903a4819089030448001c0c42042c40400035600144203180f0107400192400419602516011490f03940007014801d4071085d81e400c100c0c401142d03070701101003240d10124105141c54481811711151851443d103407203086d00c44003110148215a8174400c1540d12a0f032448000340082500000c0b1250454001e19145102001052003a0300500c02c8a40c0c948001c1e10f0a07202c141c54130300015143c600c46204c00d00a000030b01c0514581c0580070314603000002250010f0b0f0009801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 282592706 1250 282591456 282591469
    0x906120705060d020d060603050402030a0f0201020703060204030f030306170a0b1e071205010614040306050a0e160801110703020a14030f0a030203150a03021c0204090c0b091215010302 81
    0x10052484203554140741d4450002d2210752040c83e60400154003c00c0d0009220010703c1820010820b0781014000c42c601a030002e0707150130900d1002000030300e28120683c2503900c00c0140d100038507031000c030840d5116128140906038505010040700001c1c20010041101281036551410345203024004284c3d96126586131440c201004110201c2c83d401c28245800131f220300b9426602442b07207912104240d0945401607429560143c20050900c001840030b00e517154990402c950840b900000c00248584031450440d01424000c0c030321505c04d206040c00503419862070110328040b0758604000b000007003080c101d000c4190041050180240c0c200380e903581d01060000103511300b00440c61003136038580700b64110402080e0704401d8812000030b81c04004c010080c0045500c8003800001200c4000300c0d20324543c00604c021079400507102c40310120b460454119180c907040b02c00c16980c441c00c002c0110b1349a002411940c0c100b085580d1081040d00416070b5481408189510f4240d01060080c4040c0e00350b4090282 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 282593956 1250 282592706 282592729
    0x120c0702031b211f06080706020c0901140d0501090516050108010b070f030c060513030f02160b0d020f160b010510020307020405042906040507030b0607150b060d020408070f050906 79
    0x28018551100006144031340381d10a00d00d401c2400007031450a01e007030245404082e4000c00c0955110780d4125a071070350360301261811030300041259820f120040010640d2106a00c0e00148150308010301c54040020119043c2086d505030b6501e000ba660f034810045031464000c0c4561400f01d2020080107002c5038082602c003070194028200311f45400c0190350b0b54000c5580450341130414000080b020007c1550007001445404618030080a01981211080a0b61503403842541684500010b41c010300d61110780541b00d901129480f02602d074149603a62400c2c940c02d05504403100c001841c0045082d19020340b100ea00489503034011814145280d0a00000344805070058405501c0c0f403914004038100c00100441c1c06225030030480d181d0030502c052005603240945043c081c141022003416041d01c44c1001c0d03811140d04558906100907111f02054002c2910300c0e00360780c00c00c50000c2c04580854650700200202d511160407140c20a5491120040c2205103000e440c0d4400c0403c004a809450041c05069 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 282595206 1250 282593956 282594019
    0x2180406021b07050a09050618041b030302100506042702060403120c05011d0d0c0f080c061005060405131e02030112030905031603080d02120c0702031b 67
    0x41c94855107103501d29007895424454020b40d070002d042402941000091000108241e0780280041e062038000070309902286040c40300400541c000080034070440707810344030b1111588a0301d01c0443d9202d080007921900110002c0c0301c1581408003090040c2032a1040c40440351302020f030340c42e0781d4000083c075950386824100107030f910160520010010858040130b01c03030f142ca0a6110000103010700e1400d142550442c441d4020007d10703280c0c0502d020031b00803903600525107103450070f4010500c1034a0f1119110108041c0079000c0440858441c2040d44001040750045454255185142d036070b034820400d95108500440d5000220b400c035109040255401108a040c01030302c1810740c0002c0d039110070040342c0003648400c1c084a4400c20a0080c96005000c1c0c0300503041c00d601401c40e000c0780c03000709580c10400d480024210040000c441694602c9541500c5021070b07130000132541070038a0322170a1034a400c0035405a200c1e01511425240503030100311200e08148001c0c10394440b07005604041c1c180001c0b2b04141c41c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 282596456 1250 282595206 282595211
    0x609060d0312060b1c0c0c0b06010f03022101170111040501050d0f0504030f0e06121302060c0a030c0b16020c2b06020c0c030303010605070609020a050d0311160302180406 75
    0x3198000081019164105000720f90317100c9074641c2c0400200352405038160100303201d01ca80210020170f80381c9011661050b800e003410001c445951030210700030711901d03180c0740544c05192480040c0320020080b580c122841040c1c08d01144942d551814201c0705000180a00f40d1800c010402565000700060082c482c044403001074802c4095407044250b440843c0d0072030000d020019551101e0350041400110020103680103414404210754890140c60040d00030481d02801c030030301c07a045549041c01c076040e0444080a03540a205c1c1883c0c0a03140001c5548210380318071140c1d00240068001c1c0e00f20182c0c0b00b0b500d03402000842e03040c13800d00201d006c600c0c1c4a2240307500e2904c00c0040c1900501594056588160001a661291819007504000c11600d00c0340c4079170020001040865400400d90300f6241d0071000000c2c09054134400185076007110742c0040c2d040300c00191754070241a080002c030600040c43c070b0b00ba600e12404800b038540070006c003408000e601c00d16072441c01580d8910300c0984c0b54801e110b030400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 282597706 1250 282596456 282596459
    0x409030516060516090506031f05030a0506060112050403080402010e040e012d0c02060f0c1201030809310203090f031605070b071a04050a170406080609060d031206 72
    0x400302940c40750700d01611200d48400c240500905200c03a90030b5203a159250401c5150708100c005161072002824115002042007051071014808a002c0c1006010050441707044800c00d20341107445820031241140451801201014105402c0c040c1030b00c503641c591340d4511030766500c0c0d00641c1d80c0d0315a0b05000e60055911080030000b01024490780b4842884031503190980a0351141c441c42c0c0c02035000c081074035181822100611a81c0000f6010b4018541440c1008150741e07803040c0b44144e0060300912010a03403648000000c0c801401e004240102003926a00b075000340100b400504c40d0741d10b8060b01c501040005220225021580c050f64000000c602540c030000b0720410b503030385560007012841810881c404000d03420080d0802c880b10080c1580c074a005d05100c603644a18040b011000c44c054642142040080d0070010705000712840385500141f0650004109446006240c03c54080c2d40c01040030b000c0820001c0c0b6100d0b414038406e00000300705030b0007100550303403c54103007400124180845864890 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 282598956 1250 282597706 282597727
    0x60b13060e06090a0e0a0b13060e01120309051201020f0f0909060405041218031a010e1f060309020f03010903080a0b060315040b0d0f03020610060e030714030307060f09290604090305 80
    0x9096801c2360b00040104102c2d08005c80d582c03001006070b00c4142c03c2ca605102d5030000075040200802118022101103064004400c1071902a2103424205d03e2002d20020b5884211048031002c1c1001d01019141230601d60703583e000b404216801620040d11440340d4403a1001c0181c41545240700f640b0711400300150551b900d0395008010007840400c00100d2200300b00500c0174846138a1003d03070060304020440300b0300ca035100501d0000c1c0d041e8001d071410107490301040c5041d0b4540c400786100107030001e0020421101d8a0900500f0ba040030f49244825904100c0302c443c02c0c0c03030b00100b0349029007480700c841d8440c100040100030080840000f41500581c07404c400b080030680022850a019010703801074043c4c2d2400388803e42c0a0189500200140075a1006c130603020348000895809540c07918048078080c61041001a04d58010701000510315804d048a45401507195000680001c7c801e03005441103181180404401d203554075146101d5944000c000340c168a0035070000c45040d030083c10310342d242c500712a2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 282600206 1250 282598956 282598969
    0x60d08030411151305100c05060a0911060c03041e0824060a080c1201020d0903020109120503011a0304020d15050603070e06150904060b13060e06090a0e0a0b 69
    0x210282c81c1641114840107030b0742056841c03481e80802c0710f030102d803804183c0001c0141d044054080c05000314401c0558150050041102c007450070307003240071a195031929403807103c00f40850345421299201281c221361418100501900c02786c071207800280d81040e0038010407d00b070401044410360075011103980015405070500c44000740070040d616081c0d0307003a00d4884a140110001d400b00f401032418200c1040310400204034403042c418120b030b01c81c1c0a690425a4035019002d0b2902c89801540b03021107030001c15405610101d000307841440c0b000c0607115000010b49a41c042407080c0c40c07a290381d40b0780c07030003007101c3c50002960300c5807004191030700801c2c15403503001c001502d111550030400c2d07030780003401031518003002040002d000c0c10b1001c0e030030b5107008004651002c100c24103e001500340401c02c0312580e0394070342045002d081d114250070349682c1d8500312401c046440d0320982c3c002c06c08039045ca84550610004031115644007074030089032a86000000319900b1030040403d401a5694001100d6a55600 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 282601456 1250 282600206 282600211
    0x80703090608060f09060108090a02090c07020a14010c020d0f1a0a1503020609100207120303020a09060503010f150c0b0c0408010b030f060a090510050106050310050621060d0803 78
    0xc0d40c40a55040c10030340040c0c000c10001d001c080c8a0783d080c901a000590342e0050960380143d007864141010780311011803d1070540c001070001c0d804410041007002c210740c0710300a00542d9008544081c00325540300150071420341e1511f90140028007820b0b4070401b600b0300c011803002c0b140c45440600b01a0856845010101c900e5041030300700603007280300380104a00280034201c5503610021100180d149140e0002c0d01c18410b1040150003861108590b15045009200b404010009500911114822803400400a5020300c0035480404e07030700d410200e0110f00c04d005907030607a42d900d05464003241c1407041c0c165009020b20303440b40400c60802c000f6000942c05140d810b002e50246e50301d1940b210300b003c1c401402d64862802c09400303541304080c001a0150001621030b005240048005010344503410b015042c4410100b42050003800c0c1800060300e0b5911600031482200003640c0d00407510b441d0020081248202c0000004145040d041d40403500c8281150541004000700900b6441d9681c0d9074004c5aa00704 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 282602706 1250 282601456 282601463
    0x3070b1c1a01110c03101109030105090312010e0412120209060a030c14090d0602030c09031204050114071a09030c1207121107060507110a08060612070b040e0606070807 74
    0x76084040711540c000c3c110020310142c420140002c8500c00340070035680c407051440c9003015611241d00109400c0000112540c0d110301500034016031500c03456240c1c1d2a4411440110b000303c04100018000b00d00c001c21300d0040b0b920400c00c1607010342d682811030340c02d210a40350710300450382040b807861513995080c01400100d45136240030410780302000015203071001c45260034208040400550107582c1d6149c0307481020365406080103803281c441440b284e20600032100790641501c6034203007803924008500050011200242d070b0710380c1c07042800c1540b01c03202d010b0b41400a05008801c45802001c0143e2003486a1000e610001c6906000310426000e1500042401d110400e540004a410610090b64083c000c0c015403400c2400850300c070b11301d0242c0e444101c0d01c510030800a000c1185002c101c80311111580f2108010400300010380c40b1260740752500402c2c3c1d8001e220791310642c050400c552022644404450030002141d0419140c4030000025020050015034009820003006000a648d030005e03180c80ca00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 282603956 1250 282602706 282602741
    0x3060504050103151a030a0609060908040e0a0e1c0c03170a060f0504020a050406111f0203010825050d020102030c070803090310140103060b0609030d0e010f0c0203070b1c 75
    0x28140b14030044506040c801c1ca4170088550002907551000600c3c0240d250f40444002084251130a000c8001c0584880003041c0c80c100280010303004c000d5054180c09841001e90801809124102c515529405401131f102020701000d8071080d003030701441031060000d019080c507203841841142c0644494104035254a1310643c0c0e01c2051015003092400034014000030b031821490000411303005402c03401584940300802c0042c80036411400c0e03040c84401440c01d200f000c00a890205400711601a4100340600d2040c0d00c1403d0103514804422445d8007500c1050001d00b403821800c05051013502602542d080e070540c402001885580c02c4100082401050921b01860305d9903244800c0500b080c242c0c0000c442d1250402c107000034140c0051000da41100c0d4005000101e82d040c0c40c1c0440e84900400e018030760306000311809020511341112000f840c03404266141c0601c100301c0c100a4510801000f40a500359105040c140212140d6800800198203110001c04441c1420075403034003030702c6040046980300071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 282605206 1250 282603956 282603983
    0x3190302030d0b030a0510050c1306021e010504020a0509071704050304030b01060809030406030c2708010c0c0b1602010902060304050c011e05031308091503150306190c03060504050103 81
    0x5500f4400c094060f9400c4000c1c0c2102e41e9161981c5961b184032404402d0800d986001060144100754125040c100741c103440300403415030f00c1c98080d44414040001c942d06503000315007040d8401040c443d0a200c1c0750700a00002c48581008188202c1e600d0040c5442c00380200c40501c810700104150300107204a11030b0005580d100e013149014882c122040e03001605111002060092100c03010041c0c1c0c0c159007540c07800180d880b50322041103030f80381000c0809400d07034a80250480700c00c0c110702c040d160503100d018009006803c0c42d0001116411550003025100144035804170f0069400d0103c0030050303005038400414021385a400051072070340250303012642503000b0131864000356000508404402100215102c2030301ca190406003861100800b0741c40c51401004264082284080580d1080b01000e800081c9048107052180210791080e9014030003154512040f290718a00003901d00d116414104544c903131201031031403440160009100c0303141890703126003020074a51200d110f010f000354003c1040e581ca40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 282606456 1250 282605206 282605227
    0x30307150b0d02060315270412020d020a030507080d061805010b030709051014040b13080102090f0904140a030c0209060405070f0f18080606100c0b070507020319030203 74
    0x228000c004071402881c1021030400541d58a10940c0e601640c0b202100c0760000d8010700068810161079030903414903134121220106c3d46a42e0054521641c49068001080c81400b5426070395000443e1a040041c4c0c0060700c032034000780c0f040001d00615440340d22581c1c2045d502c2104c90b400c0c0c840c241c01c08480d2042c2d80344402c801d210301d4002d850052100d210351034030b90700382044001c001034011300039076010303001c0707030400c20b503440d104141100b8100a030400041d1901c2e2a800201031030b40c04200b02074000640f440011414003c18800c507035001e90010840c40c005540c130414440941c0e0010415100d0402550100c0200328080c802d00380a03500c00e50f5003482d1450288108110380102801413805580b4100c200030701c080e004201c061618080e41420780010000f40822602031080d240540c0c0c0b220340f04e0700d0010708000d0000e04070740200800c46105441160002007140d00000400c4042e045041c22004604410700a50003020f255002405440c41240d05000c0800d4041ea00b40040300142c1c000520510700 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 282607706 1250 282606456 282606461
    0x60609150d060915120c09022a060108010c080906160c052b032d0f18050601050303070305041202270601110c131d0604080703030f0e030714070503030715 68
    0x280440010100615000d511b5000d4031110078010f42511990010b020803290b0901c040d03100010034054181184c0801400850b9159442803060001541c01d14450400742801020800c0c8601545d0000301000c2d40e0b1034007441350245001d202e80007440400351084c40451001c0c04150000c40c0941c540110010740c3c0b92406941d2000204642d08040c0f030000220420f65110f0003282c94504074004110b42c000520b01d40c0f1004012450407058000d151200b03a00241c01c400f401c050101d4041e030f042e00d610383e90398000d0645034809c035007000380050b50400c0188004501e080c507401345503001802e141490340740d00c4c0c4010402565070b004102213080c2c41d010040b082d0b90000000800d0100031019000c0221400d01080312442e1000182c0900c079241d28002d005001e50100c00c4190341c1111003180d6440c20581000d05059100c0002500040c1c04c1190b070440c01d2556001d00c206440c0c1100c02945031003544d48035400c0f01400ba081301e88041c0102d02c00042c0030b54081026001d00e9004070b0642c16100c0601e01c0c00401c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 282608956 1250 282607706 282607709
    0x140102040e0703090807020d061823030702060403031407060c0305180f0316080d0606120c05040608011517010803040518070c0305030a14010e06040b010305060609150d060915 77
    0x800d41019044c10000d90310006a403407599040d030701800d000d80e4901d03009014114440102c5d074101102441c84007400381e2011844001c56482a01c03c03a0740f5189001d80f03032203100342c3c2c1001c0e400c000c041000b04000382c401c013200c20181c1000c011a50a00c6882d58800050702c1d10040c20100207629a014014009100c0b40f00001301e15a0718000d0000030300c0501560745030b0054040000c10524030f60104400c2c03002c003400301c82040c120a02e01700000c03074072214003400c24080780242031203041c03505500c9104180110107c0341035507125240c0c80324680c038040400150340d1101700150204403c02003002600c440f00e807030b018042e02c400d40c0607688950a20b01803180c2110300c446a28070a551031814030070010703003009490080541514000d5030360341d81e035080d100c0900f010008280300c14501c3c100000d803180e00811801d02030b503401c44043c40141007000c011419a803080d164645e20a0040000d031080e441e1038020154400c1d0008059410f00260301c030103070201c0d8032541c080b4860980b65003480c20240708000c1d0560 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 282610206 1250 282608956 282608971
    0x7031715100e0a1212120902030312070c0605010905061507110d08041203020c090f0609010509090a0516291c0b04020a1d0d03020c0d02010c140102040e 67
    0x80030360840000d00400000c001c0482880401c0b2030100968035409540310182512082000c1d08038210301e0140c01203500042d90000144d014404203039000018098104065002001075050000c4003461100101c80907100350103001d2101040c10000341d19000f1a4000d2440721000034161034094280020140240603880507040f0030401c4900150001c842001d88042c156440d110550035441e2040183c40360ba00004a0881301e5051041015800a02c2000101060b5928030f501c0c0c80c0c82d81d00b40036041060b10425880241c800c0103020505228142c150302001603001c842d0081101e0b01c9081c01c0c14001c200b55640070703e00c14010f2251542c1341c442311119070350f901100180b000b5480c6040d038050265a46886045102c007100390312200030394020400b0040d000703004540d10180914058030090180c41c403600c900102d1080e00800f490040c100501868146d0064412080c0003010000faa000402d0200d0500502d40004c00100340e000b50f80080c01000d407400140e07980e060507460840000c0003071010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 282611456 1250 282610206 282610231
    0x30509040b1e0f031f0b0109030b04061a060415121107140105100806150d060f0b011403070e0d020307030507060c0605090a03091217031306150e0112080c03070317 72
    0x1426004c0c0b403140d00691032008005c0055841c509400403125984540c0c00030b481640307494140310074807500b6408800d94a440c400365048504818090191602aa11603070540c0f00d44041c0d1000c1542c05080a16141c0b2240b410008251081c030601502e0b58100300003e482000300d005000782e41c1d00b024031546070402542d0018280181c90880e44d140c0d03c0f40014610b10009003018444110358031040c1000744075941c071800034001006c2c40394040000741201e501550005441092012504104400301c81c092242031b030b900b05100001c107042c0006582d0489089030540b08506001000ca45c062040b00060003440c1c0e50000d07801f9660a194050760b030091701040032908a036540e80002a00044a50211082c00c3c0b0000300c4610f0501b00b81107450020040305103111000800c220400d4a0b4030542d80b00c1d81e120f4001000500d40841300480e000314140180c541c4862000010300c01084a1998442e0b4035201d20702d800d01d840b42002c0d41c1c40c2550400c010440208160205000d06400424401071f8000f9162403234 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 282612706 1250 282611456 282611473
    0x10110601170a080c0f060f07080601030e300d02030712020a020318030f010c091503110d020c120418050601030209130c02010e07031406071b030509040b1e0f03 70
    0x56031502e6a10400419101001440600d105000d00545580039062415920b65140443e41d2032509182200c2240c0000e04000000d101980207100d50190866080c00401a003680d00c29084c4031100c1d50644da040c044210038440c0d2103100c1c040001c0403204051000940c170307828403580286c6a070101c9090074029600520140c10003a03800010b9070a00c40341e10440b0041c2c1800d490210742080c0c080c904c54609035080444083c2056006200c0a040300c410340b000070148410184100d007100c2242c0040798610b101086105209201070300a072082080c800c1c1034400029020300901c406900c44e9200c4285404c41400094004405124141c3d00090a080c198644602c07680018800407003c21000710083e46c984441c507005100358003481d0345091070300849034415101e0804500e03024580584031114403e43c3c000404c541c0c41150310307401101003030341085a50b0480382d03401d0750150000000642c000303030340380000e016542d20500d240140400010000c5c00c1000da0710188440241000d0001e4000e42c48104d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 282613956 1250 282612706 282612749
    0x100e0304080303060f010516060b150a1b0203032701022802010c0c05060f09100309050a030305090c040f09030e2b0f02060a080f0919061a10110601 65
    0xf200c0e4080001c0b43c103411039035004130041c0c42070f000340c0d80c10083c42c0581c0c200c4441000720f0b5034001c500044040325100e02d0f642c1c0790440341c0d6841c801d016203800040c1600c05540e05c130504041d85048030600c0141540e0400c41d194034081c0c00b503203940d1a10f51044040444002e09560184858a002c10041c422685084481c18440c40d151100c280002e040040d5200c8090501c21250404d0000c2c2c800101002e07a24070000078008095000b0400140c8510216040c1c01101400f03482508902a4004041c00003062907071030540003008014802100c5000302c104800d0165186d2192a103a0340c080b490005060039141002003079008039440260290f041c01000d038101845a0303441c2124030351070040c00c07054043c040c5459105512000d00003908460003041510300d194000b000544685c2030300883c4c01070340d80d410401696900380269001d680c04502110700001c25010380080c2d1808081080ea502101140004220200c8413106000c0c001019458407401001c0240039140c0180341e0f81d01461499041c07020b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 282615206 1250 282613956 282613963
    0xf0744030412050a02010603060608100509010207020d1211150916052107030605010f0302030f060705030a0c110601180e0102090a090905160803180117040b0709080a05100e030408 79
    0x2050b418000e0101d061a03d10380300f50040c4024580c000c5044c441299684000e5503200e0200c00d40406407410980014150075051080c0c8806076001054136000440a0316810700101c0f0f8140302008229603042c1c80e01240703000300418806c80d04004000000e038039041c90014108450340c91104c80c2941103960800c4290307280d25a042200001c1443c803150345120350701c104e01c1d00d041a0b000801e02805c201c00001c1c081448900101220700907400d03600c0fa068080319403529000c00301e030040e01289090010603000030559205030059006410040060a400c1e42e10310700d07205099100c640040c400700c5000b20300c111940140141c0c2a402c000075424107849100040e9014418081c0c2142d09075581c002500b440070420944c0d00b40044c8403422050070341c9400946440f0340c008128564110700310144007241c0e51258410003540001840e000541d6121307503440340700ca003001a00740710030000084408204a6014400c0d032203401c1c8100011b0003a022415614410b0310500c450200a0303810501c0100032003500030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 282616456 1250 282615206 282615233
    0x3051b24060d0210200303010303020706020a080a0e0a051c020f123a1706010e0607060b010908120c060105090601050a051608040305030304061109060f07440304 71
    0x440b000000d04c3d140303e8049580000761512030304841d4880f0b04000203c10040000c6060f607019900ba200300603102c400680e80ea00c2c00c24402418444104500d400305031084040b489540381c000d10302c4101c00c0c9c2c1e400c0000c1a40e61031022807641a4000d00034181140b03041c0c50400c0032080705035050002b502108070240c0d203d0429040140009940c4d01250b8a5900188141811000b540c564030740f02e8618a040100071020440e411094449020080341d415070003888403070341c85d4200411592804026654136001b074144d0031405418040c49010101c0d41c4403080c40003d181086c00710302c96481d5000d10780c00d80e2411a041c4d00650007002c0385000d10400e640d004003112203641207401c00a80e039052840c14070b05007440c100030240c034211000c64003004002c004401903000700d000751070074440d55000036003604c01440340c500819881031040000400705001d00d0050040030740552445561302e5400b41452603102742c0043d203800a440000079074000408056100800078840001203400d618003551580c0742880034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 282617706 1250 282616456 282616459
    0x402190e0406081b18281103041103070807290306091f03020a1211030610150302070803010f030b0106021207172703010c0c020a1203051b24060d02 65
    0xe992240083d030301c0340c0ea000c8400b01580502203240d4075100340a02c46000200406900d812034030f00c50102c03241b406005102e003d0300c02464951468655640300c40550980541064060254000000d034110044c8002c000405003002e0038000c1403440030080d1030350111082c480000341000c0c0140041038403142a03040c1d0203260304c40010b00d210084040fa0b0040c1d841940025413205c0c200c840460440d86002e5040c0e034a900c1085c00780155107003102010f403100404c8420041c408003040003009442440800320700340c42107906006142030310030b80b01c0780d2031a80241c0014440383c92800081040002c0d03e5141401031400d44041e10421000c00030b80b4016114040000e020072a0414110f0440e9000400f11101d040590f4441c4030b05a101041c014035000c80b25070302c0c1d4400c1d403800c100040304070f002d6044940c1c8182d006191407001424901050526299a1000c3e820090288502203401c0c0c0400700c091102020107004041d25030401c50006e8a51820500c0d0780b13402220359003444400c1c0c0301c500011100550 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 282618956 1250 282617706 282617743
    0x10e0c070804030606090f1404050c010513051c21080c0a120c030603111002070915150801050306011a03060f121504020a0b0309030a030b030c0402190e040608 70
    0x5107042880036401280c0000e0300c010315180f800600800d440c0c0c4041501000340300b0900018000e01c54400ea0110200e030041e105400680312420b144d03200b070f00100000c03c80700e04502c0354580c961002c103005a00805034485013140301140341087c016840e03003800410400d9801044002040c0768010903004028000d0701080700085400d0170168000c0d080c203004c0c3d41c0054000c00c440c104c006d40050251401e4131094920401407442001035003405e4454041e140310320b4008001c000c0c1b80a015100802070a0380c240c403483c1000c03101003560008070140232001000c3eaa200810f43d41410308160624606034490030408950329403040d981242c12094a074400070031101400d00b002d5000100d82c401400b800907042c20f000f00d680811a20a5550031346024a0080e41c1c150801d03510b40b080ca202c14032040d540041107030b105100c0395014078400d40001c2c1c05114080d041e517490042e0369000c1810707a003103140003001c0620f810f0035000400d0350000907800b22801c02ca80c1800400d00d401000c1d6250344400c02101041c00d07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 282620206 1250 282618956 282618967
    0x90712060b090403031e18150605060a2001021603030e0a14031e070201020303011208070609030809010c140d2013051008070e0f21030408070e010e0c 66
    0x40e155001c0419800040c0c010845882c26140007001004044003030904d4200e14803422480460900c106064200c00c0341c00080501c040b40c8441c08050440e051001c2c0c125103c12002c5890b8030750740082c1c00101029110a444180e003255140002e8580244081050b032060201c0c08060300c1c42e80c1c03000001909070900040260000b584039041c003c604001401d45542803800e010707003210020040c4100c3c0b554088070f9615080e03901d9100154442c140300680142d01c14801484022106c000750014688034140c0d207864800c50b075a0702410b94030b034004103502090144041100c8120207000b00b079440541c6140ca950f0300b011001c0409858042c00d80710740542580c0d0203111442590100300200100302602c00c59031105004999411050554040c0501840310880c01c0c0150900485640e03010300b065466112015007600700380040610004c1c8143d038050009040380f03410383c40b00112a2524820003014603500da003014060361034032600303910150000b90300d180100300e02c103184440a42c110000c41e902d9542c6a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 282621456 1250 282620206 282620213
    0x7030c0203131502100b06030f06030a0618171204110f0613090b0a1503090809090a050411030a0803130602040e0c0307090906060c0b04020103021e0702090c03090712 73
    0x50144030b5881141d00c401d4500803602c8090000e10522180403a400c4a120001d03441d410415600700d50a1b4903040b40741072010402c070150000703821b544054080c0858550307410f2625140c090762124601d00304031960052070385080c0185520303c1130105504801b103e24003103000ea03509850f46c100410240400ca5010449503081d0341e81d00051008000043c002c68851142c01c16043d03090b181441074035007135442c18154503690700341184100111242600e4051491360140820303000340074014021601c201003004104060341e154400d8600451070008001010b207400e01e0100000c0c107800c111644a58002e41c0c408001503280c80481c1da00000ca0001c0800381e511514011010380215003006040d0129070701042400190080034501ca960b41d5500ea0403455581e0301088200da489000d80d20005d5600254000461b507481b406a4000744189001031800d5285030703218404003101d0341b5018055900060313180c25860075010440d000030100c070f08c20f4a9410310350010b43c2e0300c016501c1044640c842d040b0002090 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 282622706 1250 282621456 282621463
    0x5070f030506011803030503011511070b0a020705060c060702071e060e0f06030c0307090b070b0a0b0d08040b0a031d0c090901060806010b220302010806010c020a08121c050c0307030c02 81
    0x2080310b440910070150f1a4900906982c000340280ca018099242c00c0ac002984982c150000d070011000141140d1400c00405898550180c4d884100303610840c3c40005d500d45803040140100d05030f486c05050305080c40c50300223041c060701e540030800c2e56002801052124084000c90011145c0a05060306071020080c00f040141d64030b202c950740d2005005c000c201001c03840f03200661003000144e0310041210b88030030f0740545a02841501030101e50840000411540c6168000c42032010010806005000240d0b6030350700d941c0c002c3d0450400404c010500d20108ad0f00341c0110521503000100c110500c50290b00c0865440c0c00400c01c0c284944030000c08038140c51002c0d40000003a2040c2002c2d101c1c503684030900d9001c540d02c8050030b95a88142c100c07071900d0885072340f0f4110096a5050391520b14640b1240011901090205000d1ba1b0111700c01e00700080600c4100980c2001103142004203440303071a41303004410300d6003000c0888110103080c241004035003542d21040729808509811300040091055004928 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 282623956 1250 282622706 282622727
    0x110d08190f060509040b1605031003110301150816050d0803060d03111504020a080102181e0301092d05030d05040602160c0e07031104260a0b0108070905070f03050601 73
    0x100304c0304a005100a01c00d10110b0a0321400503601b182440c00c01c0d074042100c3c50b20048640d400004591030003400000e0894030305d8080f412000700003103013038040141400c5001000350b0040d041c1d503000022a440001c522032581e00144400c4500e0220020344e51034840c1c0d5403000815851044c9503110030142014003c0441c00488902101200c00580b058000340705a030700c0a070f400341e00c140e880c0340000420703840500071903546c01d40c21141c81c0c1852005005000c44800614158411003640320400801502c00348201604070740180b4100c641c0c1c541802c45200e000c02c04c00c1d140c07140c01c0b1b000340c010f802207600003080342c18000c4a1b580024640d9210705103100207019080c07080c4200c900c4214002e003849040c00b0300d001500c0301051900030303a46401e00103604448048130b04509801e01880104194400035108003541d811150a11035884282d0400e05c2c1071840a0100f1500c00750350030018042c02c0010440b1402400946e0001c02081c20a10005003010100400f00c1003090380341c05c00a07165034850780d0120b1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 282625206 1250 282623956 282623959
    0x1060323030f0d0f0513150c050c030a02100c020705010906081b031302040506030c100e06040e090307050d03060e0f130c060c02030f0d0905090a1b110d08190f0605 72
    0x10f8072581030030805030141003000c1150f00c149003014003045100c0c0b4007a40d10316070254850360b0200b00074072030303000e000c0039012001810003800320501c504000717400140010f105111495010700708112200780b50300700301c81095210008551140784240441c1e60444118000d44a05050126681e40e60105092900d60b40000401c400c0350040144141050040489103069100f2501406160b45034000d00d40e98589240b032180e8400540d1401001250080b4800e141807075002d810646403c8d15036070340780701144090358a02007583c0700180b40310034003c043c81038400050503460103102c802d140120b090980c5001404084015041c640443c0707000c20390320700340704203581d00001d160310159413040050308500740f068042c1e0081c015240c032800605404522040503041030f8903641c10484c04d0806100a139400140490001540c9109284900500b01d07052400290706941f190001790040e80004e06110210445009102440052003141c640c0c41c2030484070306252403000295010f0400707c0c0070103410a58440f6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 282626456 1250 282625206 282625237
    0x905043621231606060501260703020a021006081c0c08090f061b0106050a09050105030a0b060a0806010e06400605090c1801090e07120615020604030905030106032303 73
    0x1003042600d0b0020310440f8001d0b20745a0242114265808c201c01a540c0e00f60203204002000030f5181d03000340d0190208034010320480e50481d800f860303e0000c840503500045101c1e88000308008280c48010000d403113410b0390385400382804210380d803103003011b018440c24035210300282c4800f07050680300e110a54103180c40410a01d00c82c10701041603280244868022a4042c0c186c4000108241c00e560143c64101c54000d0014411466107898250304108041c200650043c0701c001d000414102c1007020710b0103820703075109030703442c03030601b00c003000034442140c01c40d40c0720814410b034a0800708200b596410103c040081031901c00ea1307903c50440c0014000c90300501d41c045100018804c984203c280039081174040e40d981c1c00b02c90030701a401074414081a21038011999914000200030a100c0e44902c07003001002c80780072844644940d060501c00c0c182c030306e00100603032254007000189a0b00c41e07162401000c0c190000c206540c1140c0f14002d912820205603880f03940e4128441030417110030403c07942002c070564110b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 282627706 1250 282626456 282626497
    0x1f050313110301051801060f0501120b06040e01030804091b0c0308090f0f010207020f0a0308030103080706060902300c0f0c07091104080c0301020a090504362123 71
    0x301e40101362821445c0031691b1074003401084904404400d1000c0e1201610b034640f0a4154588030f101070300289100390f0b00440e040c0720020f10980d950507011f001e540714003080b90315181051300460803a81100c0011030300301002031422081d290003543c240f100c15014504041030b503452081d01807900d81904020305052140302c00320300c0b5556040d4090400c051080b40c0c104608903440c4200076001d80d041c00003074401c500800042000442890040000d24400c0c4000b080c01e9942da16084e0898000d214066652402c800380c100b50302147c840c11b0200c00c801e00c800c002003403d1404030210140180318000d01e0f2000000750805001604000c031000074680742d0414040341c18840700145c0d168019108080852041601c000b01707034034040c002d8400b4145142d80f222109071a21003040701a21551602e5802580f001e00b4080c0d8100d03c10940c0d0580c10f426003040c011410712441c00e020070b41440c0c20303500e06183c01c0260f490716442d4881d00000b40c0c070030010504400c107aa28146d5125030311a020480c003044403940720 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 282628956 1250 282627706 282627721
    0x180b0307060c150c02280203070b0a080604140a090828080106090b0a0e0d1208090c030a050a0219080706170f06010207090f180b061f05031311030105 66
    0x280310070420b104002d088280e40c003020f1100c0548602190300005078004580305d107010382d9202c005603000f00020f800504128007980209040c040242c000c486224030000707650b15540e0700652042d80080066908000d01650300807102540c14000e41140d4056462f49210018086d004050310641032501054408a114403600001c0040c80b007030400011031030000000407010b015180020886e8600b42d1400e05d410078840c81103074080e070301c46200f03031340b12050703907442008aa000c10083c240043c042d202c3c1d081d0750604902541c5041c8021140a02c41c1c0e20900800c0009000490344040c25941a14a02c2c07840a0070501110f6040e02e5402c9142188a6101c00091450307111803182c607000d0b940c0c0c0741031459441c0c140705501c04081c110f030800c1c050f9004550400c0348448503480301e00d16422065001800104206103009102075005042d04d04e07043c0740c0240581441c0802d0b070122000442ea065a86241ca1000c001d040307804000c000714400c3c0c1180e03840c0e0048c01f601e149001900380c4010000c1116103031406 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 282630206 1250 282628956 282628967
    0x20409020306040b101e05040b13171b0402070204060b0f1c1103131b03080d0c0203030403090b070c24020c090615030c07081b0c040203060a180b030706 67
    0x282c20034400c80c00c0c1300c00c0200d541006101003400520701d80d0b42c0120307003284901c2c2d07102e014044442601049400c2000046000c584400f400203240c0b030085aa41032844e180c0c100d43e04201c0c4040d602c6003500058107a1a02440d840c42651404400703079409601e83ca020700006008150315844558805c000281107924034032540000c012140002001e1003551034039224101c100c6020b0900f001000d0010004034514980940200c0d12032031040c403004003490300d203181110f00d4005c184d00c100d4021a01041d0007450703c215028410031100a03100550031803802e0345006003190214415410000c81c00542402845851641403000d010840400a14130012506003049011141082401805070008029903840c20081040c090107000b0010810a080c040410f0516440544000b03035108080007140300040c16500030700582240b6005110442013804601421301340c241d01c190348503030310410030000e15544045490701501c2080c0790000c0c80c0784200c04200700034900d859506600d0701c590040001c00c980d001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 282631456 1250 282630206 282630211
    0x101403030f03100f080d050406050d1b12050a02090a0b0a030e01020f180a051e040b0310020c0601151202070503131502010c05070503040608091f06050108090312010504020d0f0204090203 82
    0x5803c0340c900130703a80701081c41d20b650022801c0400200b040000b0802d0301e1090300a002c0d2580481c0002441e0071000e4504080c80264801c0f80c0003140305200140e03c5586c1d40d00c525503010450700c20541c5414504400142000558001c410007100c0124101c14654030a83c405c0307a04081c4200215558141c041070100c0d00d410841100c01350340c040b24984d809506016603544200c5001a1240461880380a80b41d02107a84401c2d5440e0400d564200d45c2e1060f9a0070002d0407040c1800f0200181e494007000961410080305030001041c0511720300007200120303401184404c40c0c069510b401030f251b440c3c52030524214850603401d0f602034201c0c040080766403c07140c0342c041c2c85910310313800070002c803d1051420354141c001d155003c0c02d140c0042c08204555070003207030090b5118450005960301c851404001d4240072500310b400600300e03a07649800340281c1d60030802080d04650345000035405c000b601626210009014020305016a40119000c3d050f0b4400360441181800c3e0b1a0082d902c07a034448462038001e4004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 282632706 1250 282631456 282631469
    0x17010213090902090a0f0b04110d0507020613030807050d09060c080106021501120f020306070306080105100321140c06060306100b07030311090904030c05070b03101403030f0310 78
    0x384a8001824070030792103020308003070380135241c01d0440c1e8458000900510007a045039030515203d01d038541c0c0950350b5100b000c51080c55808860b864442c103040f1071049503401002d03442954401d405120784400344001c0c1c60f04076941482c3c00c3d0720395511040211140d01940115a03c041d0901308003c0c2044080e0700114907000040e03440e18003e80e43e454080740e8606c1c0c095402440d40c1050001480150240098a00020701505550301d440e00d090b03000c00d03d480c0c412a44840040d6460b01e050080d92000e0041340e4010b000342c43d4140c461400d640316540c240d50102d0700d50104c10040040400224081c0900192102d560030308140c039070310a1302c011521460102c402d1403081c000e4800149990648080ea1401c3d20750b09202941004160394080d001021080d4040e02d403034009101d46080c6580701e20402d44218420380d42e00e02090442d142c000d1030b203005a0000700c0c0f5100c041c0108410103194080e00c1d011220844c80030100e00350050b011030704501c140a0a07181460b0f000080000000040c040842220030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 282633956 1250 282632706 282632737
    0x2909030a0f080709061b0804030f05011a060f09011701080a11030109080922020d0618050c16020d020904030e19030302070e06130c020c19031a10170102 67
    0x142510120b6111408844401c081165100280038141c468011180003030a52200032041c04020344400056030450350084420300410181c42040000a010713594101c40804520b40711200400d0028080b0b000f220010710404102080b40601a032140c1c90742950051180340806955846400250320b0700512036041c1d0321440318035403060705400c0500c03611180381e07000344c401424004904d08101c25600c1003100070608145940003034400c2d04043c030041040d80814503001502c607240176880d0461460507100d03108540d10b002c00b0003411101031000c0b43c3c44640c0105410200301e84610000d0f0003411f42901c06504805640100020181c000c2001800b40d503003107801403107662010000d258980d1484c000100142c1044d8820001150450801c82d040340c030080201851411400b15102202c2c9409008401a8840c045140c803a003415804010b075101e0201c0c3e080d1003d030440d201c42c02d881e000769543d2900e4a0141d0000b03007200c1e40c410540805440700240200350703217910f88040e1f0f0103034110140c81c00c1c5041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 282635206 1250 282633956 282633977
    0x60d0501092001031a0901170f070602070609050316030809120102120604050105190b0d06050d060501030b10030512030601020307080304030c030206100620120d1a060f0301032909030a 81
    0x80d42117031030031040d00042c07580c1c00c1a804c21400621324940c445c9524400d2140c4801030321160424045880078001c103030b0050020600e009401888005554000da0090f01b0213030b4501100520841c0240c15641c0060300240e40750402e0340442c452079803442e02030490b07520101d00c2081c05810720034202c1c011a81182c0c180190303600d5000b00b107402d101160b00c6a5622074002400c02c045070300f14019000852104200081c420703610341c0458604032185da012210310356110010b1040040d010102030f00030182280f05c146250540d1340700c03907603142c8103401e03144032940c08030000d04560303c2002200d134642c4d403284607a52a4200791170090320408a83c1e80840141c01100009922070503c05090000c50303a003943c2e0002019003c400380c460286203588114400d00030010710034203c1040100410f20b0712000000040c3e18040d440b0500044c0084110080c40f9142c1044000c02d0b03601402e0070380341503036040907240f280c81c01940b03180170118032801030028440c84407800300100241c0c04005040900394903103603100d200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 282636456 1250 282635206 282635231
    0x13050709020a08041b08060a090c1205030304060f1505061c0e070e06010309111e060c0c131b0f03060515030f060306071b0203030c060c03010302030d0314060d050109200103 76
    0xd00e1790040c0180741d40301000250002a480d040030340302d24000c001500a0b181c0b0380183c640302c9009040c054420b507000205220030811540b14102d020603140108000c0305601ca40e18a101d0409489082d10030a000f18411000300d42020b4216980b2081c44010000c1e4105c1c0100380d5100e084522400158020f03100010b81294000e00500c00000d030b0250703150071480080350800409000007661024240f040010404580e20b44030024604007180500801d030014120782005010801c000562422a00306440418404203200d004a0306440360f00300041520b010380c1d0110003c142d65400f2a91050f12a04505c00d10411140218000c0da004081081140d9610080c56900c0c541940c2403c005108107072900e41c205a5442d15500da207100406680c5410600800350340340136019180d036034240c013001004108501e0f007000407081200c4641020f100300b5000390003165041400a0001d4028445100d0400c1000b00a62000411941c0540310403050030303070a881e5480c031044241d40700b404240707441d800000780e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 282637706 1250 282636456 282636503
    0x3070c050a12030503060d0311011d0111090d1106070606030c0f12112701030c140111060106030b010302070f05010510211506080f0d08100b0313050709020a0804 71
    0x48a0b05501d84c1c52030342e12448240240a1311400040c1c0c10024540c80104504034280284074034440784681055012002100c42c5084825a90410340031200c100301080654507520781c426502e80d081009101010300304070225000780300d1244010012850500041308025410030303064241c800c02e0035a014415119034125000c502002c0c00684102c00d42c141c02916880d101d1030407141c1c1c0d0403e00c2160721014141e24a845043c00a1300200d4980300c0c0d402d001d11910b42030a0480015440034a080146041007c0505447c0c10307040c000d523410182c440484c810941d00a80490760ba541c2d12940c0e410b0421180d04140e03000b04401e07a507400c8545c0a031100011281d070003020100302c08960540c41c01515100390f4800b0b030440425001c04185a48030400025002810700c815000800c912000d4400000280d0008200c0742c801480800c0b4103400400600c14028a401929484000c0748103c4c0c11000c0300f03040c11843c000343c1e075000b1001d0500004403072100c9039001c0e03409400b5070310460910380801151000f441c81c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 282638956 1250 282637706 282637739
    0xb0a0906180821041a0c0906040803120c030712051302060714060106030213062016080606030105010317070311070906050102070b0703230c0109140f0a080301120501060803070c050a 80
    0x803003404003150b041117940800c5c4840e04000b80800d02c80c80c0544660105140d5000740d442010140c001162081c183e10b041d240fa20345c0403000c0c0102c1072039881c0c8820040d181071265107104400656643c0050b800e80c1181c0703180c0d01841d400074180d603219803c0f071800d41d0602c460011084154024100000341541c028002c1c1e4421a11915a1082ca2420800200d4040c0d00740c04904858140e2068884090b84003130000c54400459690544e82b0709003440091440c0280103807038540660b00d07040042004c500c048880c000418000c54104d90f80b464103041c111065240009040503600501800182c903000701d520120403036100382c003541d102554500040d0414010301c400a004038000c51450646245070321200c4445c0d0b4250344600342032a0301c011710542110282d44040743d080181c1f0700074043c085003c21180340d0303401076140180002407141d91400013500040c1b10700c10f4207010302c02825040103400c1d081000a03110304002c4948600701e81c100400c07401024403c59020720000c4002083c02e0342c00120350035 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 282640206 1250 282638956 282638963
    0x3090405040605010603180c2102040f090218150432011e150302130b040305071a0910030e031b0705011403090303010513090b0f0108190b0a090618082104 68
    0xb032030039227000000c2d500c03002010454504011100841e2005035118030405200740c02d00800002c00c00c070b0383c2c8140700b1790600c219821a80c85d601a400c0042c0800358003202040300c442a24045804440204440e8080190090700c007402c641c0080503090105018a1507812035003403076071941600c60700d145111240e01450003002d142100c1100880e0840f8040d0f0020310000318034982e11060300741c0c1c4509041c1181c000e030b0400ca0303850300090010006200031402c4040c80c0408036610078031b0240309a0004200342940300b0301c4c0c000d25449820040300a001401516128a4102025107020010300c1d0340a131100c2c0c407805007034007182080340e0210340300c140759040e80c1c400d0445000845c91642404200044040a0042481e07840d4031080840d002aaa52a100d0302500300101f030440e4039410803034000d00745092000c2c4860001000c2c2440e601080d03803604c225400c940007507000034040b0407a01b408006080486c1c0074083c1e080c03062450b041041102401000701240c0031400003240f564107502040b41941c16034000d07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 282641456 1250 282640206 282640223
    0x109020f030a09030905130614060a0509010c08160507050405100815091e0c040f020f040b030912030c0c0d09030807060f0615020724200309040504060501060318 71
    0x4600e18020303440f41c40d405010703003001c000b07041d0303a48005904e00003c1042e0250305070301c400c000c105050803948101c84020b001c8504c1810000030810040c80b5004080010b810000c5821191080c001d076041115010303502000c80308102621420943d81d221103600c0303aa0300491400000032a4918210b003c0700a5680c002c0143c00081030810742c4142c65000506041d407240a141e800c03040407205da43c084d0a100c0c102601500d4016103042c100000c451024403200250740c0104a0440b41c10341c2c00d011201540c803030502158803034807024041460000081400c500c0d100000080c895190301c00c0d4090210612120f049a41d91a0300420485a4504d42d12006141c21814403003400058541d0b00300340794180201900207216641d950440514020810020340980c005010a01c180b65040e40704541c88000c0f903004001c1003841c44801008078000e0510400d030401c1038084252000400d01c101d030903910004000b0f1000b401d1a00b4284001c10003841600046880c16252040c240c00d040c0900d540580c208500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 282642706 1250 282641456 282641461
    0x80d02061008192109080d020718150803040f05090c0a08041118161716030c090f0b03060909011803030f14010905041403191b150e060109020f03 64
    0x104030080f000d0f00030844150310040b0052038a4803280d408090304500315510842035a14104805082071f591a8440c001c54001000c24490701c1c1401104102d44c050000e0300103404841000000340114181c2c1140c100c0780800500011039062140708202580e5003194180e00a40781c00d010b00f402c030302c200c1669102080400d40050042244c0000c0007007020009400c20f0344200c0c07801549100303482d040f11008800c281403040110841c5e40305034148003100d8000d24000e414200003065001d0460b1034903c007402c00da100d0500e01030f03180c800c2c003801c40144606841c0302001ca441e040b100c80a40c20489026004424600000b02c0c508070501404003111600000031248400c03580341140500f20201c80c6012a070340b0741034421441501491034030300910f0304a00c00034150030181342178031181d20b20b1000c18085d82e02c107101400b94401100e1801d0300b00c0349241042280307602e41c0407520020301540e60000d45849001c11100b100258243c100c444400d64880c2580c04a80c0c1392081c9004030b014030003001c40014000d000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 282643956 1250 282642706 282642733
    0x190c030209060a030f03110f070812090111060a050702010c08070509090a021c15080106080613030e04020703020c040c050a0c020d05010e0a0516050612041209050604080d02061008 79
    0x720650091800f07006890900c0e01d03500d464181507000c003011000540f090945d114182d400b4000300c000f054800c005407541038900100c03aa51540354503034007485c0c120001100d112030380c02404040d0310760401c501640e200c1c1c9040c000400007410700301c44100141d400d00885501c7c00e441000110b1040c50540c44090420501300140a000d007001040e41c403590303900704840352459854401c0e0700e055105003000464600724860044822440c0382c1e105103296810088284507500000c50455030141d06100004103a0b0b06606045403100c14081e846038002c0e100041c1c8105065003c5203001100304140c4080c4203020240d4002c4980b0f116520708440010108480940186404c1e81c0c3e11038043e000700000f0440c465404c2c1c11904150403040129010b40c415102c20303143c4c00404142070020101203c40e2401d141070301d0b400703a00c00f1000620060030f44600c200751010003800f4405503400f0b8040a0003440d111910740304403540e26401e000c1c0e0b5101500c1103400054412100080f003000b520b030f004000d401405e2a40c00c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 282645206 1250 282643956 282643969
    0x70e1006050912010e070f0914010302011d04140601080702120406030e0f061e090f0a08160c080d02011a030d0f2318030d0c111c050708190c0302 64
    0x100c0260b001d400d000100399003c00034018060f8808014018200d59442e0581d01c242820315507104901d0719081c0320108004200100342e060460342c081c24601c0c02041801e07510840840c1c0c0c070028a901c030f8030b41803200d0b001040c0c80c0011441000c00307886110701030b102d401082c0da070b83c0e076681003190314003070104014009148650071803115007800108403201c8554010003581030200868000c1d000b414140071001003403040c3d4100c1358100405030050580c5000f80b134100e584a41050344050201400020550244c0400c990130f018015003210f00c8081c0d55072100c0e48207031100720042c0f00000641c00d2560710055114903022410316880c00400030110030440000c00e0755000801d140410911154142c03070079031108480890308840300048200c0e940c0d50002000c150f40c180216401c46d001c0e600035510201d40d6034224201000c241e800c41c40c2ca440c540c00d810000340360400300780c50014007060080313242007c0000000d80b140a40310381800f504d407110310102c108c5803280a038000251107000711b1a0304201506141c0e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 282646456 1250 282645206 282645217
    0x302090328050303010e0417031618150c020108011d01030b04030525050d03020901200717011508120d020c0a021f030609180803060f09040f05070e100605 68
    0x3020780d412915644034207040d078209034003089051107001c0c200400c0007071440c92a2482c00c03071404101c1c2103040000c0c0318a860340080442c1400e020101200500d14030004007000f00822004004a2148220b0b81000b0128580418100d0201d001c5000104100f204508440800000046d21003032603861900c036100342d414007620a42c18007004001c001046124141400c1806d000c0883d10840020715152251801000d00f01d403800301407050000b80e107641c0c0c1c00f03020381e0f251160880c00500b1860710240e04a0a058043d0300a0700d125200000407610b00a042d04000c642142078011014a1a03450300055154034180c0194a042402088624000c0c0700550140c8046140310084580c4c0404a85c0401e5581e07088810b01c0e032555583ea5000d07034105901d8040c0350060a4401428044400e1034036001031150b0f05400028503060307021002540c4c07a11480000074507200020101500c0c3d04050038041c5030003c500701c1c282c409024408000c40c0580d03415483e24040c0558425900c0e074603180503400c44054000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 282647706 1250 282646456 282646513
    0x314150f01050d0e010e0303041208070e0105070201030b060a031d0114070f0309150f360201030f020f070c0603050f16050c01060621060e0a020a0c0b01090507030c03020903 76
    0x11284c05800900b0700340704200300061490000c6580f07003414108007284024490481341081041810001055403004240403072600038208540c40745014801070300500000300781d0907003000c000305405c45001c2d81500410310791410707103000c000f00c481d81903015401d03150f4508082005081c181302041e882031207007007842c85101c00b03481c0004803400710381e84032210407100c2d80078407100e01e0b101d0081000001c1d15220300036484103010513500c60400480303152080c1d00703030203001581c201d80140c0b065420f40e4000e0b00110b400d200740c02c2d804c55882ea07403040070092680100c0ba040d1580601e1082c0803854500920a55015040d202508840f5550360660511003026240540c1c0420100303122000c0f417001c0074003402c0050f261a80720714410140c0001d01c0f0a20000105001d0045414110104154803c0800b5190400e46040001da0f40343c0c10b20100350707070040140100800c0303513400e10000141c4140960119000f0483c03507505004035400801d045042e03000301c00312141c0c9604415807002c1a9004c41c0030382400e1981c1c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 282648956 1250 282647706 282647711
    0x12030804051509060402010905030c1f050c07090c09120c03060c09170f060709061202090a03120909052508060f042408070803041502070e01060314150f01050d 70
    0x51900c04200c0b004026542d4042c0d80d409007007404215a0442c0808026110030f600911203549000001544440d039036000402c0c1400c8055881c140b144544115801c04904074100c840c400d41d105d424400038031174109101c0000c2c1c00711102081c3c0107940c0c205140306580242201138402e065480d814010710140c03184405000d0104400640c2040c1004c1111104200d080540804010f00840c07500f8144024504010800c0403001444001c0d048920081352041940f00162940c050b03e02080b00181c80b5000505a03000c0e8649103200c1661000450003a2100c0000078001e6846101b070785019580001c0e26114400c41c112948031003140b05070303a4164440301c02070164852500d00400700d0304513021032404940100002c0c000d1812a207040703003c24001d010140007070503403900e40f04400d51a8091405600c6a45c003402d8034040c0c0c13180c420003141028000da0314032803402e540d44080160090650705488232121008100141c01020a403103a11400b55015007000740c01c108003001100e05d940031581c964a240e5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 282650206 1250 282648956 282648973
    0x9060d0504081206010302030622090b0c1905070f060c270303090b0c4b010b0a150f030207140606150a020a030c0f05010c2001061203080405 62
    0x121401014012805603030040e0740d400300100301d00c0b041c4400601060505004100381700d002c4e00ca03210f1489400c60304a00030260f80000000b05d2004e4605c1d00d0000e002c2500301401d1211482150300244451860403c420110300c00c000c000b0b036128080c100c0c2c0508130206012001000c1081e40d00700842441941c0b42c0448044006500224500c1c44003460f4100244034410500805401c80100c1004d400f116072154244002400d0171a44c1d12500c010b403848041600507a00100032400c12030008100007040398081c0004035103c08600c0541301c0030011025801d01200c4040c03402c00c003444a00352450a10244a65001108151b40c005403a05050042660030000400441c4586091141084100014000508144007080f0b964669201003485c4000100010020b8a0300003802d900140d034903045c41078180d500c6040030070b81c6241d500340c050480e508165100e88120b50184407180132610b210b40d4881d002c01c8941d429800c80f80503015241d400d05911134840046070086080340e034014400e8040304c40c400c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 282651456 1250 282650206 282650227
    0xc050d05220f05031b09011e180212070804050d18031406060103060e09300711120a0b011a070c030807020f0907080708040c080111030603100e0a0303020906 69
    0x80440b40c0c84890040c1158005005924041c448204030400d00e0360f0550b1503606100014076000b1040c4074042e0443c0b801c2d0020403040908041040c01049002e008541610381080c5e9407000e03601c410f40480c0da0078800c00004d51114001c4000b9402a0741100c0201074060088005840c021700214051455620b034000010010b4500682e1032034043c0050040c085500f0814000760680d0203a410043d48980004100441c8817000240d8520f29503501280f2030440d24180000c003510b04c0c000038001c1c5c441000044050031321820a924011207207054800002d54108010403c6d00c0e03080207440200180d99110040141c4051022142e642466401c440d526042e140e81d99001d501260380d001b124840b401240003800e501d0440d005181d00402910704010a107072440c4001d000c3c82e40200000184000080130400340489811340c00041d01c001c00080000040c040b643c40072a0f081110803e00c60b1042141c200900c0d03a540c0180d03071105142d2001400664490390702038002e03420141010b6000082801000100c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 282652706 1250 282651456 282651517
    0x40204051f09151212030b0402040b04121109090d1d0a0e010f0f0e01050105070c0801020d020403140703030f20060a0516020a03080a020d020712020102190c050d05 72
    0x3031846410005200c0c9904098458420961340040c29041801000707001040b0316030016020b4105610700000d5990980380010300901940d00960089040030a02140051030080000b1071035000b075451401742c13030080c003c1040b580c608645032000c90f044814402c4000d4044c0300c100c3c5181e418a1940754900100c0804140c01e00007030b500c94405010382c0c80041101c802c2040c1c00c00090040040c210384540e00740f0000c1d251a55042c0304880c10080009114000d04c510400c0d0f00000e0840c9000a560b0f6105208000d80a5082400241c074a08000c54101002480c0003e0440807aa0305844181d1440207940d01580c03003a003a544007a10384560303144840c1d6440380a00140d4030442c400240000c040c200800c0d141c032a2100a0126020340d4800e42000380400e4000c00c409601c800380b03200140c0d40d54100d00031103020707001c0d01c04024440c409400c1080440b80d019000b420000c0c00a28000c03c00d903120f408125903c540407d400307000d03a0403d440705803525200b14003d00c000c1c4141c01c0503072980000140c01851 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 282653956 1250 282652706 282652709
    0x1a0f061e0304030503040c0b090d0b090a050708010510051207090c1101050901090c06080411152101061713030503040204020c06070207030302210d09060e030703030504110103020f03040204051f 85
    0x500d00001b0002000110136098010b0000c07100d002e401c116800c03000c14101c030300203400900120200b400203113030b240007001000c00c40c5902070280d940031b0340d5460b00c3d14043e04042e100c620135800c1d0000c002c07406040103100400304118450003002070500d07002d0110000c0520184203c00c00440b0440700031080d000b40135060161040500000d907101060a205101209541185007003000102c00d20001c548841e00c014551031040380c3c1c034501d42800342d00880070f9224a6200c2940c8010802400d030000703517058034840c101e41e40c689035100c035809003020f04901c1d14400c0350350710004920855006c01013480341c0041c0d0fa0240c80030304014605214000f20510b04082290000e006903c01300c0c0070301c01c159052000c00d1902003041046410800c810b600c50115000c2d9804c0003161660741d05841c41400744541240e05017140f00d070240ca650b4540c50600401425049809445004641d102e9042c194800d00c01c80c0d2140241d01c604a0454075540d013008043c000240548030418185458407a4415100080c1070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 282655206 1250 282653956 282653963
    0xc0b03090a060515030d0806030f010c08090615011d010509060f0d0b01080907050f03010f02040b0310141e12060a02091c0804120c0e07030902041a0f061e0304 70
    0xc41e1108900e859030a84800400c0f040701d800021201d2410b0b5180060007149442e4141002622543d600000c0b07850241e840290b41c0041d824128490780003038101400c0c50013101d0b0142560000e56640c0c1010f04200d169502240c0060075940301c21030295800122904441c80500d8040c2c03408045000280090304a10340100001500048840d001c1002c0d04c00d021840b1000c1c00e1200d00d519041c20314907124445841050f0144815007180040b565007075100f140c602e05540c0d02103407215100d144c40c03007568004580e10ba00c03c03191000082074039200d803000d0031a01c15000300115510150000e518805469000c2c00681000045070904039014090050701d100303c2c2c561100517102e28849041003a03400c8000d1910850b00c6040c64081e01080a180172502a600c14854809200b221813400c4030006c42190710818412480b0000c0c0301200782e150b040100b41c24000c4409200f410702d14440c44213141100c900856020b1210500d02449045c01005810784800044001c038603684d102d40481032660080740c00f01c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 282656456 1250 282655206 282655213
    0x150d0902060a030524032a0607030e010f1d0f030309040c121802180601180620340302040603060615091802180d0507081209010203070209040c0b0309 66
    0x10000c540131038100016064045c0300c42800607248070109454420a204500e0020180c07071480070b207485810304000d40c00710083c1c03646035203034200e003001402e1401070700e4068002503101d681c4203c91441004110140000d100c41d0070005882c020402030342056a4045581500013408030801d25035451040080b040340310303114406590214600e03c801c0702c0c0c030540014103069070182c0210260300c41ca01603402e0003840b20301d10101e0b40c66400040e1406142e4903000071441d03101c1c100c0400d416034001c243c0038480c0352100c20810905140308184d40c4500d030f00c81300040d11800b03002c0512103410300a031140b00502c886100e90301490391260089805d640383c0d0740040c1e170401d450f80000c000c240c02c0d4000103440341685240a0000500b0007280302d2100d82c0a000d000d01e4641c01207040e03504035040c02000c26070004010711206e0106514641561281924800c40c03505005001d42000c0600314402141c407020301c168040e51502c01c5030340c00c010f1689400781040d0384000c031406005c28501192001135000c0d52000005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 282657706 1250 282656456 282656461
    0x50d030917210c060a0903030902033009011d0604081005040c060f020601030f0c092307080c09130b04290607020f06070609050d120b0f150d0902060a0305 68
    0x40000210341d2040c10040004000381c4003083e501261030703500444100400305e0714640c00c0c1805c40180210f40000396250080203001200c121071070102c1210090a07450b03214200c89250850360382c5016010a644c00b08402c400c1103a260191055294220f010003001a810191140c0446141c001100c22714540c0da0340e500c05000074004d2914540008180f0b61030104d6094070745000003511740d00706110040007444100c1e850b0007000003944403039001c9c0c080c19104002044100d030113003c640200180c40788600100401103194030348252480d510401111040b02e2415061381e0902075200035070f46441486995540103851941d940d0300480c3c02e0303900c0b00011180007046007046402c610361040019031103440100882e40060315404e01c4408910011546240c03160081d0624001900c02000000d11902850f028040701c241c21445107001a24410001c02c103005d244001d1000340480d90500030b038007401c20406460300019080040001003c13038040401c2c1c19040c2d0380424059040314a0902c003080c2c40700c0c00c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 282658956 1250 282657706 282657733
    0x32805060f100e0907051302090415140f04020409150303020601142d0409030305010f05040603080702210307120305150f060a18080a0203150f01050d030917 69
    0x194114603406001c40142c01c00c0103540e00703200224407580700c01d0f038424000644000410301045008010180a0b440c1800300c01800900039400113090341e200e03900d421203201c0c0440c1540d4103841500e45201d800c426100d610410044400d950040c905d50080e000c00011070010580c0c051406400c0c10449844c0c1c4141c190318010b0b04062050b00b00f440d074164148030b4a42e09a84040c00c0b07440d010381d40c0280e00c00c400740c84242c02a000300034000c40c0e50464208808a005c0562540c07280341298004142281070644680801081c6c42d010720024001550920400c4090f14110848102d0360000c42d0701902c0041c1e82d40300d8a41150086442902d1040058615460498040c0129580629090408c02140103d240001d45804044004a003e080c0c0403600314551406103016035001c2c500003000e1130350255074581c0da642c1c800424008900074041d160154402d002c038010f0a03802800c40081e605810fa080000b0701030301000d420016800c021860b07000082a181c4020a0280d40084201504104c14610b6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 282660206 1250 282658956 282658963
    0x3081801031b021c03090803090a02040c030b0609040b1f030b090a090201022a060c01090c060f080c07020102011b030f0e03090a090e07091103090105060a0b041202032805 75
    0x8003001030354900c040708842c00c00d50102d80740d921a030309410584106024030f00308030028000b42c1d000030300401c000018400c4880000406004d054801c0f075041c0907400f0040070403400e071500e4500c456000b03a420703c40c003030851400380c0148040c00806042310022522a0f0551022800510004c50101e07907103a01e10038450500810b119070008600344180103410a0380e0000b5030302c21160b60090022100801d4007403038885810500c0591000c0208502d44854240d54410f008000c1d100c0d0445203241c65507000220036000c0c00703450044c050789480d200d00540d034820000b040707640290b40c102e04655030703441354150810050100641c40102d40d5070008680000c00b03281c0b0112149011045810f83c0148002503075542c4920020701035034401c20003c20034045200b0b001d8038207040fa41103c0c41c240d003400705c1c0c03101c0030400c1030140d40b1404002e8003e20268071210306202c02d820f050300aa0034000001c100511030080c494688000e00352010701103d5181c00000c1c2c4c1c901350110200000101005101c084a05124041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 282661456 1250 282660206 282660221
    0x507080a0e070308030f1305070825060504062001020a0909050f06060d270807030801060c050c0402071a01090c021b03060105010309030c0b0a0f05070e0f09100308180103 75
    0x304001d01042c1c0c2151100c0346580801000c1c0302d2444080c40000c4d455400b001c000c091980d030302204840312240c80b01420390711001216102180e0f42030600c0035111710080803904000f1900c1e0358031458a4542058000c840c06620302040700700b545241d0a660301d01700e60900c002e280942c0d40c3c0d0385010029040160280c1600e00c06003544200400300c105004099890740d040740d8200d9103510000420446440340070704450070681c9501c9200101800160612808000a0080520035540e0740c016a881e00f0043c0c4081c200c1c00380c083c2c1158021003511a56007029402491200c0c0a000c0504154080a9003a46500000d030003498846072500b469020054040106a42042c6041960345490f45c0712008241c0da1181481813904040d100d4040c107003418000d011042010760021700c601000d103042610013014044440704c14074414640000150010300c1100451a5142d00a1011140104a00800410100203045e44030b000d00310100000025183c0d200804041c0b0014401d01c009102107800501100c841 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 282662706 1250 282661456 282661481
    0x20102041403031908060a030b0109050403030b0a0305030403030302070c05060c07090509010207030806040b04060b0711010f0f0507030f0509130e070911120a18140f030421060b040507080a 83
    0x4c1c1305801d81000400c0c40107140050500d000d0109550f20000074440c4142503001410000c3c2e00c10000c41e884c000754108a01c220b00946040c0714210600040c0200003029110140054009010030701c0082c0c401e40003064803038060384000c1406a102e0303002810652041d2090b50342030744040c1041106007a13a000e5603070b010207060000c60a003c9141c602800300d00d4010a900d104581d01c01071980c1540e00c0703a11003400b500003202182d85a6100349049801c41034405c403864042600070b036198105034419020710225494a903112400c0045c599001c2c1c4200c68105509410701c4414040381d00280c42d404201880300c0308214002c81e005c145500d405041070059042280c1150908004095900041084400d191001c240a0701c076070352070064400c02030580c544807007850300d96082d0700303c103100e0b000007100075155108043d1501c15003004120743d924801c0703104102d01905540090310130440861110380b03100d40104070209403414104000350480300110350030004500500188050503c0c188140800040d6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 282663956 1250 282662706 282662713
    0xf0a0f05010807170703230c1f030f091b140907050a080907050904080d0f1b0e13050a0501080d09030302071401110a030908120403020d0b060619020102041403 70
    0x409420584900f01c5015070704180001d0420451180c2003008000011508003044034594070030f00360360803a010b1508420120a00c1505003020355840c090307441c1c6003040c1c0350210346c0c001e641072014260302804c8041c4c4041202c039511004500441c0940e5600d90031001091410130354141040c245041d41c0c64011015800fa1800108114040e5081800caa00b000030a082540044e5075205416140c01c0640c1c2106800840c144244810820340c04090b0a50100d4000d0500a50030024010300071242e00702e00000850030400d80740405240100340342d810306500079046200480b402d00c00f0000382c540650320800b80c2a5520010070100c081800a891980014a41180900d01c2d58400a50700c80d1180101070714072001000c0d85019030b002c1c2d504081a4191281640e030fa105650401510442c0715104004140c0165000f140d81743c5a11001c440540750b0051031507806611a171070304488000c0003000150881c1e420070503840c03030f07031740700f01c203440d4044525400943d9071418075588a106004601c13029000c1d61 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 282665206 1250 282663956 282663959
    0x90501090b0709170c122b0305010801020a08060405061305150f031f1a1e030c0f031c02010b030601080a0312050f070c03020309040e071d0405071403030d050f0a0f0501 74
    0xc004117220b01200d0080303407051100d98a5014403070400048103405111100030018000000385500000800d680e00703a10104041d0382e03078500c2203090344503810740c0300b00249406000920b185450b52015400000280500e24103880d40b001100864030191200c2c401c61148000725100b034a4174010f441c1c82d80b40141c000d05120a040345840c0700c090341c03195100c008551104031906000644d41d80f000c0d024500201884201410000615030b9680c0c04046a4041e028601181c003160404020101d201c00e40074000348100b90b1074900f0600c80f0030304c01500d03500b155261500c0b0b510607a0104803180c0600003c10150a4100061030b019110011440c4003d01140c2054100080341d41242c5069501c0035080c24080d2030210a450201e04520480c044194043e140001d0450b000b00b000407828240c420201d40340e5a034429408489030842e008940061407070744840e005000f01c81000c503286600400c0981120308144071952030006840c03045502d4060140b2907410031402803200d000700e0809641040040081d035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 282666456 1250 282665206 282665249
    0x1302010c0602091903080a030506030106140402130509010e070323150f0907020d02010e01140705130f0902070201120b03060105150418020913022b090501090b0709 72
    0x20440010700701c0c81c0e0104095426454010b07103d01001a4084043d4030340380c484c640a0119040741e1503007000641361100088890405200d4502901c6d2403242c1c90011145035410800a50f02c403840341e60704d0f2071020360001126207521900a0190641e100024100d11f40050010300311240352210704641804000a07802d1008082e0f141504514a05000c403c02002c5101142c2c0c2c0c4a0041510340d040000030302006465a0b0105d2400d120001035402480038411044c0c504c0e00307842000003500e0720483d03150f020411142c018001000f607101c403c40c1c0500210307624070b0701586034003040e0301c107001d407a8000030756808660b030001e40646001c10003d000c001416009000c40d9a9040c140241802410200384600002c0b01900985008207408642e44404501c2244050007941041034020b001d50f5115101003020000d0340282c030303101c165111141c0a0070f18040c00d800c548900c10000f02010701d94070521100401e20038000e0010050040c0c4581807103080000004010540a80c030080100c40d110140e024034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 282667706 1250 282666456 282666467
    0x1d0a030e10020312010906060824040908310506040803041415180a0b1204080306010e090a0b0906090702060601052116080a060f05040e0715020c100504122303120a05130201 76
    0x2d0362b40c1520b000400101520308954684689515004e4550000c40c0540c0100d081000c0800122000c441c88207103581c1e00d0082c010300307005901a41120390800d100034042c1c1d00c00d0340205080500010540e200340a0081e544980d580d10007400780034201003d0941c6001e5027800c0135000010040c2c1c48d40c0624002c9250408031340303200082c000400da880000301140d43d1781e100b04c4104000010007844548503084c016a220024000c4102c6130340a91411800542d46103082c80303040d4032403084c58000e400a030717039007070b00441c0e03140c0c05200540c500fa4154604090580e41d102d540b00e00c19464003407480201d498580c070103070201c10000d19804519007880e009114160105201104459043c2c40110713482c0c9074105860b0801c2da00381c2152025202c0703101c14807601580041c0c0200b0400064400090b8480c000d0421200341c441c81c021480e00c0300301014088000740100781c18110301d4480741c841221960701c0a501070300390b80c4400486140b005c0100140005000c040c070950307400042c500c1c40345000000550010b0314 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 282668956 1250 282667706 282667771
    0x303020d0e010e1806180405060103032f010e060a060807030b0c0f19110607080c03040c151d03031207120204050604091d0a030e100203120109060608 66
    0x100500031008a2550f4064032030102ca0202c02000001c0d102c055521540348080d040700d9081c89509501c01061281000300c40c1c0070b00441e00003025252507070940e00c05842000c1160129010303042a4075100645404d0040a00b10040a04001140c508008002185801005007200100604d4900c040190110005a020072254021090b01007a6186000418a4001c1d88842c0c050424002061041503c00b551401402c0c5610f841e214070040070205110740c1c4e0642164440c0100361a01d012a0400c204400555402480b500c9074641103901d500d1108070007401e000400c800700305440d5009201d8884000c0600c6240c005a0081d428200e001d18803000e1640064014418088102520040c0f10001e80441c0e0103010007500d526502c40da00c1c1240c0005000180500c4090501061500781c00c110100b250100283c16030b84080c41c0062010820038400c81000004055110030002040e06c2c0d0944e0f0081c600034420b000000031f0b450f240c540090944200100108107600c200403074101c07100455110303c41c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 282670206 1250 282668956 282668983
    0x50f1e1b03071511010c08010815060f04050a0207060f05070f0507050c120a0b2a09090c090d0c030506040203061b030415020c160f0609031106180603190b0604030302 73
    0x100000c0c0020f0155410302040d0500c2c4540c0d400c2003504011160450703c00c50485888a00b2624500807031a048003007a0801d441550b400485101108900c1c60b0540141da008090020010301d4080181e5491045030a007060000001c1d840d8010032000a401c60a00e03403e020143c1040c0f441d0451983e150350b151029100da0318071a82d44d00742c05109001040143d920340690048c1074480b1400c091440c3c00703032026031300700700212000300301d04170b403c045d61190950303030700c0034014103c0480c0d0748076546169103e401c0400c8581c1c02540700a540070200300d42c25081c42c025400f49016051508240c01410b0804a0041ca42c00c040f0b0006455540910394010859502035004407000207815011101d0b44060311440d2000466803280050410100e0202134030b1100300c90921281103071a995404080d11200721505c070281c003555401e001c01c1c00c1410540010000219000004207001082c07000050300c80d042aa8001d02d19003014410b0103000c805480380440703044040b1813082c00c07d4515980255a01035401062 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 282671456 1250 282670206 282670229
    0x10303110a0228170f01060506040e07210231120b07050d0c050901030c0806031009050106030f050d030c0e091602010b03060a15090506010516050f1e1b0307 69
    0x11048486082d94800b5201d602c0144e0f0480130b1104c0f10740e641d542c240c903000f181355180400c0001d251528008840c02c80c1c10182e032003070613956102c60a50383c0c507000822202c141000c481100d400c0030030620003441c80c000540c80403182c4441034003001d5000c4941c0d0080c03441ca0781c0702004c184415440300f02800d000030303402806000c4994608004030340c1c034001e00c00e420060b6801c1003941c3c20700980010143ca003410003a45c0803c4070001899048545000554040d0b4064100001e0240e4250541e0071103090907000780004035815030b40381d48805078001090b00607a07540d000070019020b00e13179160207440c2e246009894a101e581c0803607000241d41039000340c0f00844400d0002a80381c1618000e400c4805030100082c00d448041c64400101009807201d21400021120800e001288070121445018003690040c0d4034942815403250030341e2082d41007140d050f516841250522055014104a500a048800d043c017a40f81d010081000c1d1612100702e012150000b9081d07071521190b2800180e0310102c0d4481e5828 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 282672706 1250 282671456 282671509
    0x50603040f060b1804020f150f0711060408060708011d0c030601020118030e0a0b160807020a0902040605070c06050a0e06180604030c031208090a0303090326010303110a02 75
    0x860080c941c00b0546904220314040c040103198003401c8035403107640203075045082c7d41d0030314080021400c12480741d10030841c018840314240c241c070305014041c2188500380103050300259100050071904654041d08090f48600c0410111580c82080a4014501d00e58803c0700104c8220b9200d40c4170500603c44442100c0110009003144c2c03003500227848030340920801e1088501e60707040090000120703445403402212a1207001446540c0e0b441102c00e8403442064001880c0410380d80ca261a621611003640c0c01070352550003281607022440104010252501e54954460702e5103403ca01e20001f03a4041000c1c020240400380d071080e040170204d5520941203894035610703400c00040c4401180c11041d1141c21610204000c030400055007100c0042e2401404072120f1054602c0084540c1042181d600c0d0480c1c02c5031321900006806a000012803a1007800c1c070454480c0e8941000301488401ca5861b100d01801c00010000e164210413408800040500644121a130540105000030010072005100d45a549d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 282673956 1250 282672706 282672713
    0xb0616030503041e0b010303080c07050c28090c121406090a020c01090501020309060604090c0306051e090307030807091d100306090c24080f06030a06110406090e01050603040f 77
    0xa40941d510800d000c166a80c0394600f0030b0305c2480b01c02d00048000c1a0f8400c0410100320803501a03402c1d0640c40300003014124107020603c503692003c98100c42c20b0070103184034a249000741805038805001030050005000c52070f082c004190018004040c41c0365441d03c80407040841945110591201003a1014112925490754103402403041a105152a52a1400a2003008019002140200030030030441e1140c0d1512010042240d03584d00000308a803408050400029400744c201a41c807540340c641400302d1200e860781c14501104110752800d503075000014070408060300311181541044e146c2c071748046c0ca83d0402e040030000911881c0c0d10000442da4400180c03072003141024540c00b40da07000708c051080e1030417898036414207100e0340210407021616400c640c500340824260f00c02d482113a9680c0c5038045c0c03103904582010210141c40c1c80c0e01030142e2040100818403500600d60010310400b542036440e40790001c0204008000d401c81c01103455440b00402c100c0e61090152074001e0707003101d603a542d405094038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 282675206 1250 282673956 282673973
    0x6040b0f0717030a060f050909070612020c19140106060206061504080d030203180a0506070507050f0a120f0302190305130b0f070e0303070302060106030e0c06040f08010b061603050304 81
    0x2051140b50000000411083c44805c1d0440400c4444004114001d203440c0c60400c203401c442200d80c00305a40c800d1004011151003006049041844410018900943c0300c0c3d105041214240520b040c0348401036000d401c0150108588101c3d072581c100810030036042aa00940b9440e005d0005e510401045451940041001d0300322001004014101c441042c45030724090061341084907000a0444c0a017848a0002d60108688803580d03405009020645c0c4c03482c40543d20340e00014020760382c81c4500403410181c42e100f0401000b0003400b8000300d005120540030010074400080c12660704240c01444044500000907200303440c9884507042c04269a55040e1180080e1601d0010103449a0841c00c28032104001c0301160a0069005544a038081e1a111003815500d209078600203006a02c510700401ca03491080c0d103d68140d04d414000c1d1400c548100c000900382c2d800a4000303551401c0d0300d840801c5000c03001d10032100c400e403003690485d007012100c00c99001c03101c0a0b01070103018008000002410000c509 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 282676456 1250 282675206 282675233
    0x3010311120109350408010603031106040809040f020909040303050907050d03080f0a0b03033004023307051b0f0105070b191404060c3207022d06040b0f07 68
    0x8402c0c5070b171110b030349524031030213045644404c1d000320703110304e042064140340862218810f81d0044801c900d885c0100d020300c002441415400040140d09010841580da144000207000b24000e6030082650308050103060b0401c3d50540c030483c03050301840800000030382c12035407541c1c1c48443c51940b0003640d41c1c0e03070728204050000308040710f074540000100111000e51103147c916904000605454103416140107900c035110040c0c070040c1d03000c07110302200d580c00c0040318030065010301d8001c07500d90751a052480002880d000f00030704664540106100003100d00d40c524520746854401c80c1e241e80710000d40b00000c1c09504c01c0b90f0014010b40344840004006141c0b25812100d0400e000208001000702c01c440307000c07404416101224140c1c103011162515078802da5250200070f800484124682c403c0c1c1f558086140741c0c0b8040c2c01e00e191b41c28458180582d4940c00a5140d54040c04c0e190720700c030b0302c104009040b08402444e40d1b502ca210244030900c6100187d4003030b21400b1041c60192a690003650904410403000c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 282677706 1250 282676456 282676553
    0xc14160612020403061d0706030624030605040513060b100f0f0314070f1106041101210603060b01020d020a030e10021608100c02030403020603040f080f03010311120109 74
    0x1880c50300940d41541591880000c030030801501ca01503181c1104505460092085400003e1103800da551030bc203901940c038545c1c580f43d041c0090780c2030b610008202a18002c0f2400594180301401030800c2c424140070300c3e000b0640444004c40c0140c4600405000d1185240c580800c0002070740e00c5a01440c060350010510307110802000358035242c000002802511080c0c0c20074005920314907213810f01d60001030014042c81d80824102900c46a0f40c0c0119200b295158017803038120084140002a2035145c0320f40805507010710000701d103110458001a1610540455110465106008074804250b001c0c0402c007810350200ca80c42c1d922550003004918000310f002c40b2075040c05890800194144001400c1140c007070306400c091180c44207a9034260313103e0041c1d21029412100800000d00040c04407010300103843e00c074803116070428030305403c90390217a0070036003041300d680150510803042844c0c204520001c80c21950000c0c04079018941d51540c1c1f20314210884003500b40c1c600d10351181c6800f424080880d425a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 282678956 1250 282677706 282677711
    0xf0c0a0503040803030a060503010c0804080309120d060603050c16060207030306031b03140a03021005091c050306180c091531050306100605030406020405060a0c1416061202040306 79
    0x201c4110f03c1c0d4a07540b0a440c07840c5100d192260000342414180101d000503070031a1151a001c2c0d4941d260501294002000da80d85401950402050642d8501c050646040300240c009002d07030070030340b001d022541c015007924050b620501c02100345206101c400c0c205141e0040340035803541c0c05860250040c10341604014400c00f01506541c075901031500b400c000300e0740517000d00814000b40800c203a4540080400280061300b21000582c5032140c00d4202e070b81c210a07203e049510003c40300410a00490741a0303050300002e000003045c05003614048940203003210000041390300034103002554404a00c103c0d080c01c0d00402c6030f000040c2c0011818403c0d82e2845007040400c6514481c00b00c140205416101d0f03050160a0855001080034103001503040d00c01d07101d01c00914001c2c0d08000c4103079419003000704121151902000080360503186c3e00c01404072800203454040c0080e01d2407400040b0342c0c00c05840c0102c954080d0302c500000c0101514918110385490074205400c054403070b8030380040c0c403031a0806001c0a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 282680206 1250 282678956 282678959
    0x1090b071206061b0201081e071d0a150f18090b1503091515030a03030212090c062a0303070c051608060121150204090f050402060f0c0a050304 63
    0x2504410304141111100740c08000b01516080c1c2500e0214035007915000d15550000c88200550044801a0b0890a0035a48100208441c0030300d1203080c5003220700800154842842600701c1303c1407a0024203038134013101c0c103002d031034104911402940072400c92002084050200c0c1010140182c80f004040703182e00c290080416243ca40d018040d01006610501900b030040100c40c0c11124070301968001e0381104041c011030340c3d0110003000303c61800362206c03103004004100700384c02d03039020000c0d403010b50b00c00e88000d03854038102004a0b02141c40100408a25040840e50112540d500700803a45211082e0b030140e03030034101415400c440391000104c070078150b1100005100205412091030134545100b0400c8038a49619030103003c00b040f4161140307000c9540324800512407040041003901c00318220340c45000b1022240d84a81c9a50780041c440c0300e01895001605100700c030541d001c1d9169598621205001c581040d03030214400c0d11030410035050000c400300380c0c094030b19010b04c00d841a4079000021070f0f4a85 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 282681456 1250 282680206 282680221
    0x20d1d0a140102120909041719030b1503040302070b2a0106030b130506060d02010c06020d090201141e0c030403080a030c031811041505100c0218010e07030e01090b 72
    0x11190512094054824281c034186013008a100310750400c070024041c04000c0d103641d83c61a03c2006602d45035800304400f80400181c00c04d48546000341c00219990200e440102c46052080c0030780703098110351b03690108104010219400240071021a0507215070301c1e0b036a20403041c10425480e4843d01c0d103e02c1440310711880700010b02c150010410303070740207900c11100394840342c030010310800d601e1030018100d03005030002881501c3c04106412003a40107040054040d07003d641d50104030b82c4072811580d07145581e508410309559001440b1b020107806106400d24300319103c1140c1042c400103d0b030f1a075825000107810505000184192001140d00c15900c5450701d65489000d17001e08051611080080d240030292075258040c0d0150f00401500844080c00d0005800d0501000d4500d00d0400040052402c40000707290715000e082ca042c01c03450f5941d00c540a003080c0304101c022242e045d4120381003000f8000520110006099160b0044964140040d0805900001e94050300c140304000d0306824001d420444d02 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 282682706 1250 282681456 282681479
    0x1504031e050c0705010c26130e0a0507030b01050d0917040e010924030201030f061806030b09010902010905010c2d0302010e0609030301180209151201060906020d1d0a 73
    0x102d28814041d1109603440d9401168502c40480c0090040c0221400d034a0b01001a03c400710500b841d00c0b16420310700301881e00e10594040480c3d20616001e400d1108202000c01d16100d0190072502605c0d042c04164402d0000800304e0065000c107204440c0d4035440303003040240b6504007178403000300c5c8a010b544681d91400312203080d03282486a4401181880b0080002043d000c00c2140d080d0900c454594205040d9001107001b00681c9810109007a511000407800d540d0902401d14001c3c0342d0400407070350b14114640014815000340c0900030b00e80c103000d00c0700010703a04442000d065070345c02c3c030f40712021240c6814140941400075a41070344851468001020382c0c2c4820b018100701d5402038000b8800c12151700503a6546283c1101c50705d8650300180014400c45500c1c400070714043c8100b120141c18004890001903103016035480c565080c8200080c0c001c0c2280a0003840f030b00400c12805c00d02c1089290110194443e081e540c11a800c00009285010036425a40d45844541001134110a8600d4030781017031440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 282683956 1250 282682706 282682717
    0x203040806040305040e0f09030f0c1e1b010509090a23010e150d03021230150a060c03050d061d091b0d020d050f0a08030a05070906021504031e05 64
    0x1104000e55000807c02068100e440f40198003da00031440c24480c0015124150000310340c0220380c0c00381d9844000b160700c0905010382c1c51001c0b000a09200034a928103d0003040170405100c1c140315050004100c240c0d03414000c540e1241c0001070210340101e03c40700544842c00c0d110030488025003210008903000d2080d240b050700c0340c010302030301c1c00000c8c00f0381003007100d19901240000d0040e88254900022500803201400c0c40785a000944510f403400900070380c5000000300135040c201803400c001c0082040000482034601042030724000c07040c07410484000c05240d2022030140c148400040d240d0b20030419030340144c0c0100070780381c41944210300010540002107001d0720081c0152043d40b41d02208248031100b28286120010030800019505500748251401003020941d0b00d0700070524603440400c1c0034000d00c2c08161091240e56940d1074009603002c1100d1029208404000000005000e00fa40011f0005c0442c545000d10108945d80c03842c0c200d40c0120340c2e0903408200d1500d00c10152807150000003510 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 282685206 1250 282683956 282683969
    0x9060706061406090913080f07051506040b1c021f050306100503010f031502120903040914010e0c360108010e150603090c0a12030f0306030b16020304080604030504 72
    0x10b041c41e400c0740420003140240d4071600e40c040b1105000c82c01410480b0000c2c003190707106e900035504001d1201001e4550350442202074031950001d00d14440040c140034072460f800130041714108a98400305003c1000651211602c1480e000c103000144155520720401440c404140a83c0590507406080c005100740c000b9a016400794982100022001c2d0048080d00c1c140c616000881481b145151030384111503030b8070b00c2002d905076403c001004040c0401c4003103920802140004640e107501e4091034000729203c030710301c0c0366085c40b5200052181e801402c01150b0449035015040d51548081c00312220080c103040c01594402500101101c1c03d4048040c012852103401d1f00c50780e1550703984039014491030008a030803400264100001e03100343c1c03400602464002c03120340c048450010300d280120700400110741101000404940c2d140041680c0109404100340c400d181c14056149550b40c4c0c41402d00014080c400409050713038003010140d01c200309980081842c903048454504007420060a84d03402405001d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 282686456 1250 282685206 282685229
    0x618030c010c05100c0e030106091d0105040503190e090708070e150909040c080105011202130e0d030f020706020412120c0b060f040b120607030b0406051305040203030906070606 78
    0x2284107601549441500c60707001009040103c0265140100900503901c940003400b0b40003208a1541c0c400f4441d110142405800000c0d500803404800600b210b001106420160304107030400c4002103010060701c03d00f00e08105101130103c040407041c2d80b00c25061415540104020b400c0144243c2e110710081d026071095114043c0421410f000c0c0201100c40b51480300c1201410021003801c0c2c14860754040c1d200307000fa8185800907460b18005400d484007a4001803515400110402c150300d441d00c038401103212249020898004207820541d240c0b0301004884050603510f624601042145030125050b907540402c0031540d850325822644444201c15009551408400ea0324810143c01034440003070003500480892856500c24041280044002854030b0b0442c1d01d5080021168907122140000350050b48050f020920780740500404440e880300140d84590306002003049103465550400d15602c1109901003441d60b0b1f03a0000c02c2c03440c071425000c59004000083c14130705104140d88981e043d15070b058000f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 282687706 1250 282686456 282686473
    0xa030e040f020a0c0b06011809200414130f0c03020403050706091d0907032306070305010b0405060f0c07030312050c030105011209151517070f180b061803 68
    0x800300d008000c43c00c00428105003451000c10708811440c1d07400901450310782c2260449500c160500c20703960388051451900d90044442c1100d0000c41500304601c1c00b00782c14101440c11184000708030403120413900900042582c0e00c1c03d6030858001481c4181000b0301809190810071005000b50310a00c4141c0d054018601e0105207580719050a40850b940442c0041c10302540c810342c031012140283c1082200e105504001000074002c0c1d203815082c4504d0820b001000e09021265414004020014010140350034014070050300840160b409a0300103035049500e4407600c0051400e0b6210340000e91000b03100c0c02000000709607102011107500d444208040c412512100081e201030301003802210b000c0360304548130980780319031544010074a80c02004003038401c0c00c012011000b01c800c0c068010162201000342071081c800c90f0003442c00401c00550052120601d4400440004c013440e000f1f044c403030f11454000d0742e020030140e0044160008000c090399a1428230300301120350513684555050081c06000318 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 282688956 1250 282687706 282687731
    0x203070c0320032b0609230606030c0a02010204120f03021209033a0519020f0a0201050304020102071502010609110a0207060f0c060f05040525030209060609030a030e04 74
    0x40d0480030b40071100844c1401c3c1c0160030281c00c25500396120b080c036806140200d0729110f41e401070314001c003d4842e0000303569807443d451003528418030320a0301c1d0714010a02404174584407402101c3d4000d6600072850340302c1014400482c0603101d81d45c0090b46040200d0b00350001e1010f00345090101c0e5229800b02c80c500380c04c03017100002d68000ca02920f40d041d000220303208811200b9144194180445140c0c0c2203221201d9082601c45c1c4100c2600040001c40105089190704000744c4101d002c00382d140020070700f0040f040c0d84950380b00000349000b0b0410034007001003811640204200406480c107948410103c0c41c04882c000d000740401c1c85aa108a4203010400846004060403246185003c2d07020703100d924140282a2a1400700c4c00042d42004200503030400881c580b4881c400021080000c08a06401d10303050180c03030300345050301d5100581040c00810821000041c924000c8960580c0d80c0002c540d51a000030703d041c000c50010640500618002e081015800104117400e608121003c1110710030448 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 282690206 1250 282688956 282688997
    0x30c0d020f0607271701050402120f06060d020a1206050604140105011e05130f090b010905090a11040905040822060f030e0a0804081506010c0b04030e0f040203070c03 73
    0x41d1001c001c1507021840620082003044207603500000e1440d04d11078180d0352440780744174004101e2a512543d54800501c4114a0301705442e07400da40c01c071801055000c2c500642a43c80b602c000d820b1b10f00c02d00081c8818011901c0391650b43c0010411903c1d0038241422134100ba03806400220384442c41545407041428010603000c9a0034140c50307040c1d407540b0780c60360002c1003007910b517450341641428441c05014681488000d00d41000181802ca0300e440da8951a0901200c16900b8644c4900e040c0104104180b0040d16400d11250f400b650021f00450041494840003c4030704c540c0d0402450170341000b0400041c4080e5500074400000602443e0103c50011403d4a5841c0c0700c5004440001d5040d5603a8028188240c1003488000303c500306462401007560384e103175000d500a0703014050903000154496102ca0341c266029512850030300305492a103109640714141500001c00c01000c0c80442d55260f031450310b44000010700d008000c0c00031552030414250181440c0c4906008400042c88440803116035040344 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 282691456 1250 282690206 282690211
    0x9030903110a060806100e0a06050a03060803180625030306080c01030509030d020706110307020718020414040509010906060305010b0328030c050f03040608010e06040207030210110408030c0d020f06 87
    0x242c0c0c070305143d600d03800c00700308041803106d80e003400700249161088656a00e05100358010b00031600d4147e5185490b0714050260b8170356070f00012040e00140107042c480c41d41d0078002048064115041c40d0307165101240d442c42c0421000d043c001e8200154005000c050b01948407030150b8411500f19181007100d04011006c1d03c604a40c800c8141c0c20a0080b05040101074001d410441d1180c080842e20a00c1f00114080581084918400581c080c000030071040707150702030142d90311107504030039444c083c188040d8440604091885a028a503134500103500c00360700b940301e240001c2c2d10081c24002c0343d550341040c030b028010400c0894864003c070b00003884007104010301003441c018804251291401c041c2ca094a050001040a4820740113188c00f80c01e4440060000788007078801a12812400d5051a00c607880c609002030040d4000c0c0d2040002c1f0f80401e80001c0c1c50300c0c0500c6846e00101341040034003588011405103601011451001090000c0154070100c0d40311107000c0194220346a0482501c549a030f5150107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 282692706 1250 282691456 282691469
    0x1202011a0d03021e1912180e01050d0c0504050a0f05010501020724090b0712030b090f0415060801060308090907080c0f0f09180702120c070e040501090609030903110a 73
    0x82e101e0b2a000800072644981c3c0113501c0004d840780d40f030040404411070305030204100c4020121604118280d80c10004000501040d410701486083c20060b580030450b2060003102d100300c118807140030070449600070310300c003034080907005000d20300f0b100d08068007404110791140c039210304120012a1135440007031014215241c0c0207610b910740c0b20080103200c6801d041030000d41082601c00300030481840500080880a1094030310303684c150b48681000302161070003802940309204680034018050760b030442c0b446d041508280c1d4861419210f00e03080e0011f1110340d01c40c0100b5406c10300000140110b0101511040c81300765072004840c0d886400c2245d904004461501e042d0b0780c240b004010241603580500b00c541c5641d51303000e1a002d200d200090081c80117080320317034900c00283d0070400c0840e03051251555020340961460305000315100203a07205c0d0080c5c0111440c4d030540c000042c00380002500302e0504241c2041003003101c8141420002e101160900050b100428442d007800303410300305250000100c449 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 282693956 1250 282692706 282692713
    0x30210200d09021c0b09010c05040e070f0306030b0a09030e0d02060f070812041101020d0e010906030c0513030809120f0a0816021518030606030604030e06071202011a0d0302 76
    0x801140550050094120513a00a03504154510360000310746040c6041a0044003540724520302100340e1400e40e00521151000c00030248010403107014404c092503040100342c1440030040407100da04600400b20b5501c003400c03070484241031107207811a40d4003016182e8000c0d03a440070300c502d002041c400140c1d0304010003500070b042007080840003010358010b4003003a0301c500388080c50b043c0c0184841e000081e05540603a40000304144848140d030301003040ea15000307083e00307240309010344940019003908080e00c5031320180b40c2c8450200e40351500c01c2d001c0724802d80004d0365000082d610703428200d40c0c6801143c1402c0c0184030803d028031040390009034003010000c044009019182c0c0994408044d50418445c0361b114a020704000d10040e0303600c04c0081c10b1030b28001603c9498010207005210700040700c1340482c0c040d0b0000b1080c802144c034086909a44644c1600309540d01e041c0c0007010a00c0340c402c0340000b900200145908041c40c41d4107401004450460000507007214604200b00300d000340c0101402070141c4d2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 282695206 1250 282693956 282693967
    0x120a030c08130b190f1509140105040b01030f0e07080c0108011802090105090409141614121f0b03070b0f0d0507050f0a05030f0a06050102100b040f0903021020 70
    0xd288101c920380c064113804690303c0040300c07001200e080d20290200c9152550310f640b9242504912156004024070000905200d440c4e8001c071401003485041c003507240902d80b28220f400141e40240c0000c1107405406800700140b06207421881d46035800707802032040500030302100300c042c0c0d803062070098103070780845098a100c0511440500020760080c0c18040c14880144000702071030743c9500c24040058011411100301450181c021401d1600402d502080303c030000c1014480c05d440c3c5030720311942e81c0c01640d0307400000f00d410440d1842d002106402c85021401e004601081107801d8014181f69403040d0100d904030742d1501c0e2880803034080c0c1c0d900d44003200e40c14860003958a110703410240c0c11800c1070800f5443d151794190b1011555100c40044800700303400109010039080c401c0c03540781c0e22004900042003c90b007400d00013912070580000c820109603d0b0f0304414250b594641c4a540c1001c4110400c0003050600c0c41c0103500c60702001d500000311441e003507070f0281012407000902d4613004c0d448021440c20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 282696456 1250 282695206 282695213
    0xd02100e0a1502060906090d0509040b04060e041b05030111072006031008060c040f0e0c0f070f020f010804032a05010609050412020c15030603010e120a030c0813 71
    0x52a200c4026075101c0e582032030014070062100702428250409a010300719031700e0a185854684800034100d440c0c00c0e88a5074101070070a80c0320b07041d160300810407103001c9541607102c800103000c1e0505802000140078480148400c02820b0315400c542c64045400401225549604041c00c95801c160a3740c4d9500c01041143d001a40c0a0f40c0000c1c4410741a225049000c074200c08504180c108803903203200304050741424402c0300002c201c0c055000410425152a060901d0000d22002c8418840c098100d0b1080021684070308614050302c5032201010300d8580c490740b050802c0820f112068801b030340245644441c00c1195441928040d01c5250940c40301042080c2c050490390581e1040036041800407528964040013542c20f004074001403c40c0032001c14a4101410a4050801d0325030701a400d642c000050b507180f94450b095600d460b242959040380c0c480d900c05020030302404d0071510071900c07400b401005183c0912000094003094401d0b80d0100040d24189405480719002507410200300c004614200002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 282697706 1250 282696456 282696467
    0x109020702040e0604050124050a090b060408122511060d0e060103050a020f010f0914040f0504050706120c0210050403020a0b1501080a0506010e120304120c090b0d0210 74
    0x20358806000091100c000105944c01c250081e1012500390351035079a0000100d188244510000c02480e1210010601d0840010200307621446224141d0340c48150500351a07a13004c1c16140101a5101682c070603e4603164a115a41d20240e0901400040b0580120034080e26042004085078001c040c44084442c600030002943c01c001100c40030182c50321643c04800100b441031600944c03161004200381d10140c810804001d056041150402941d024650055a40103400c042200c1d0820f01650a149440d4081006094410300300850b80d820311080c08104076002402030300b02c4600c0c0e03a400c0103020508226005640c000340b030110040e4031281071700c0c0f854419036210540241c440d00488917240c41c159103038146090102c8501e2005070ba04aa1040c1071758005600e82d03800541c04e54200080e140030340028142c4850321010320700400315441694100c000c03c008450240c201072210304004001c9103400c0c0c40d81882800790362503803401c0c1200e541c1d5900b000c43d1030040e0b090380240311469030461803108440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 282698956 1250 282697706 282697717
    0x1051803030d24050906010909050c07060207030e030c030705010c15060302040603030c12030203010e0103080702010c0b090a050c0603010e0103080d0204090f0b1f050910030e060106020102121608010902 89
    0xe05010801c4a900150101e2050248081d4100c00c1e07a14a40309890300110481103039030000d409807009004100d40f0f0b0381c1c0115110140c603140700d0000380c980c40308102d21702c117401061801000303188005200c4050580094110f190080220700b01d03011204a801459110315180c0726940c0070903a4080ca2200280e07421030102001903e2040004000d40d40e900098213940696100390701140c120301d1400c061000d0349094042e020700d41e0030b0940c03a40d40742070300c884031071401423001802c584030124000c000c41e03108984c6200c031650010210030482c02c007280781c1c0341c03640610381c3d080720b07107104600c4515041d06102c01a00d049942c8080000f00d66031968482e50010750109003c0c07650540c1c20440404c0d568514424481540300204001602001580a000014201c002050f144588aa01d816805540002203841124007a18a2118400a590158081c006200c007840c95402043c0020881c1039055015044001403c0c80c09501d5031502072462400802081829000600100050240c5001d0f13400409 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 282700206 1250 282698956 282698959
    0xf0206070e0d081201150503090d0507112805010c150506030a05010f09021c0f02060c150c0a0f17040807030903021804050d02010c080f070e15070302060c0702010518 73
    0xd40c2103580e509095404591410700442e0b200b401800200500800113551b000d041c1801403a50800d40001075507980031550341d00420000207035400c1082036059403c0d41a01c000740c00c4914018074110300d8a910401d03280c040c01344100400002805610071105140e426400c501100c40720312426440c6000384c180200840d4161141101c44400603400f4440c1204003204c62800082c240d0407031041100405441000c60a0311440c1081500456620b041440c1196411162150350700005140242040c000c8658120705100c0101040322401a1200a00c41800c0d1660380000800b1410b000781c070b41e41403110710b510101c00f11500180005150740d00501d103007806800c00d00710b0b459480d400101120030486108410032140d106100800c40d040100c00030a44a070b000074800107000b00300043c230139003004052030308902c1501e01240029000e030105082c0210f010f040e1550004440341601c8103130340070300c1c1d0450051054600280d200559a0b0603079212a038160b65203842c00440000e01030400030042c213050b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 282701456 1250 282700206 282700219
    0xa050702010b06031605040f080105250e010e0f0a141003050103030804170d02040b1b0c06070b0619121505010f3303150503030f041502010605031b030d0f0206070e 72
    0x401c0c0c0c00c542001e080010404040003181924251030012220314001106106a5407007034040c041003a00237040d501304403400c1c603240188514100010b10071002c07120109400c040c880b000407448049076907018240001c29501801000c1e420328003207040300c80910000d4000307640701c0049800602d41001c0c0d5040c00e1040b45645080900c44000318003240d0055009114940001561030102d1240d50354803080c3c5c404082c0540b9030000404040b0b441031082490080c05d1080504c00117000d50740307502c2d81040421200505903551900c60100943e404000d00c010b075461480200c070000814a01c1c01024142c45018410525480c908001030f000030f4611114010100680e901c0c07049134501000300940e400040d42d402284091130205e4281e030701340e1981c1005000350010001100c00c1007822080b40c0c2140c038a1a15030000e181c4014003280182110740001e41d050051070031807810040007940c0e40b20040f1084095600c0f9064001c015210080740c00c04500147e01b011000801c140d01549140d0b41211010703040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 282702706 1250 282701456 282701459
    0x803130515010e0609100504110c0d0504061d03150705070f261206010f05130905011a03130b060a0f0f030b0705070c0909020a0513050a050702010b0603160504 70
    0x311070600064141104220340c0399001041001e012480284e003000c0291201c04039070400103600c1d8544161030149034003407070b21903907000d280b90341400455068155038001d880300c443e9091030081c1548d02c41d02c03980b800901340310303106000072209078000c017450800140140741e840c84101c032001c004500284103070240441803043d0004141001c03001c60106115080d0781180d4600c8030000c00d04400d103019074000d104c80070b02c6001501e0381100500c5401c0031090078a410000381901f0203c805110b05000f00c1c280030b03140b45002a9410b1181c1269050364251900841e20f0100c040c10707040c9501044500144d255004c441380070108144680c0c29401c10006440846a241c07540092120224250700005482a14101c10000c1c000c0d0040c1c1031350005c5041c0b41561030a00140c03200380c3c5030740680c000c000d8415951101d600031542d55800e01c9009000181000081c030202241140041c032045072300352a40d9003030500203800d0901c18460fa8401a03001412103080d0b0f202d02c00405008114140d9010501038108130 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 282703956 1250 282702706 282702713
    0xb030708041103030a0c05010e01020408120d060314011e02090d020d11041409160302030601090c03060909030c03030e210d060b070c060e011404090c09030c060903020405010e040b04080313 83
    0x1d2905c060262544212aa03840c54407500311844030148502d07591041c4424051038101040c5c5440b81d1140040042d03c84241050b0321004140546c0001c00030801480c00c44001c0106400c00d054007080034540e960700ba8485000c036070507480ba4666060b404030062810030014609900020400e0740101110030a02400d00042000c94821200000700304202c9020484251410030128203111a444282300030030f461680070031f43c3ca20044c00344bc20381c541c44040e0700480303070310a5014500801e00c40800f484128140d08002d07000b8030030750700140d0001c0d04bc9081d507503241000042d1040b80780341002c0c50804c240740c00c07240300e051034110480d43d92405485000c0001c41c070482c40c1c09040e202e03000301d074039240991a00001810034240802c04c036051020030609000d2112612040c1e03030455850660100b01d82450207001c0350b500115400042c04d0740d002c2a00400c03060350007562141a40d100343e038208503e0740c84c0c14000240940441d00148001280d0300044d00240f810000303150070441541146d51043c202d40d8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 282705206 1250 282703956 282703963
    0x613091217160540050301090203030f032208041d06030304060e1203031f09060303050909040501090f0b1006110a260d02070b06180610050412110a050303040b030708041103 76
    0x40e50326004c0d5081071200404a8401c0010b040105002c030020000300c0c01c5139001c640c0b20300500010312a0040c0100020341c4c140340340000300001301890340b4240b4641f185071828805070703005030207034500480b600850025000380384a032590284000a0055040ca880e000c02110103058100702d1581040042280c420012020005107000e00310300741000c00144c51202000c00c5546459104802840c10000700b000425001380c00c442d04000d09503055117244d603403814083d001d04540c48005000c0b100c41c602030303402e020000442a0082d201c20180100c525907501e000c071045446410200c92680050420740e000401c12603000c400c0c0c881000e020300f054180011021180d07000a0a8480c07920380010b403c604024207104c040340d1104085400b0f201c01264042c600d668200014209405500814008003402d402402510001c01ea00c010166100c202d514165258140640b05c4038049e14119402080301c2c0340210603601521806030165003903030748520040303c1c6000c0281054900909092800420f40c8060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 282706456 1250 282705206 282705277
    0x307030603051b011e080708131505040204050105100e04090507080703050a02181e0711030a0203071a0103120f0507020607050f16140103020306130912171605 70
    0x107600b030300000c41440d002401d4140c9a00390700104541d48170301c0d091800c2d0481c86240d0404a18540340f031560b9554a43c80080841402018001088054003408921241d4010b103206a20a840500445e41e8480c14030040010510b03100020441e140798003481810b0603440445082d0207941111612a80c8640040c144a410380060303c407a04440240c20039820301c100028011603007100010b02d41d02e003141d84a500c04c00c60400360303825500307036001080989116052030401c8010310400d5079507030610084081e5595001400842e025001c5803004410008000300d023070304032030300000840203a031000c042c01c8078104050700c104002c0c80f0307003405008096110a00a4509144220f00412100021001d22840d102402c0b40440043d000301c0b001307000a841c082c47c00341c0c1422007070a0258480c1c070b034200010042e401c0300c040004040e141c8904d8505112102d281c0d410300c00d44540344c060712030714a12001890128111000a0000c1c07140114090891041009041111903c00d022589446602e09044036a008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 282707706 1250 282706456 282706483
    0x4020d1812030c080c04091d0106170c03030405060a050d0908030c04170610140102100e0604031e1b050a2406080318060901120213060f081b030703060305 68
    0x11401080103182c162040744520920703410a42c07010300c0c090000026500c110f004088540d629131201c108012803016141851481000081c05026181c4091101c1c9243d002c48200680c41f51958805040c10f0100880b800c0d514050503603490440d40e018150740e5584940b401d004401c2e41d402c81c0c0c03800f0900c04005140030343d08015040e81d45070705d02650b03103195003850007413042e80b60022404e1210040469100700212040824200c030007000d03440050741002c0348920703110b03412810080c41030101840429101d1007a4440d40b03595030b0a200f80b0402103408403a43c0f0f11600440d0050082c8401c01342c2840e44240c204e845030003101c8000d502c503070314480c900401c040008000410740400c07414055440c01120098680d00b00250f06100d41c40c070350445151010503401c2d004250014010810780d01ca04403038032000121140a640d149250748000340031680500c40c2c140000c0c05440c9070921644030741040c5004403d00241c7d09103000407071706400700c660300c09020031050594443c0000002401406800e070391450 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 282708956 1250 282707706 282707723
    0x903040305011b0f02010b0d02040f180f03140a0e2e0207030b091203010b030604020403081201050405011703031819050f06090106030b0c07050a080403052a0a0504020d18 75
    0x10007540138200c510352542d00c10959040c41c400281c1a101c010700e5081150301114003080000c445858540100302403a00350070001141100803003030001020009240c1c5110741c0d9414143c80c0d02c4003c0d440d150081040c010700184a04042e43c00a00d8030070030000c070405820310045c601603242c107110048441c64202d0440035030801c460420600100901199005410038040d007418013500030481e040f440b0502510030986004004181251102ea060b01c0155601200465079146409040502e035a000d21605101d1401d080000c102516800e0400c594600d10707800550541e158240d1040b03440ea0710100c0011248503840d1447c00c4012088a0b640005000782c3c0a010004d0031207034800d003003450081104c0a036a04141c0f003000007441800c2003903409407410841740e032500d1551520a0030302c0c03d0f46201900710394000c20040180400400c2500c1040100841c00390001c0070040180c0a542c02941803990040d24068100318034107003034000700040601d00400042422185184a00703000b032018050340c0b00700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 282710206 1250 282708956 282709001
    0x1b210903031a06030115051305090106080a0501050103020a090e0601030b1e01031803020c010f02100203040606080616021906020c0f03070209090102160f06020d0c05031603020301030507050108090304030501 91
    0x30b14100071900d030081500c40718a150304015003154202d814048540400500280b0404144e5052640c0005000010096140395944e040010a8041c0964031004075910344000010f0540c040e10858a0044294030342d40d00c21031030b08a084205440080102d414180c0790328a0080903601d07003000820003da05110740c8440c5401c440010122540d00400030a00241146e0079000310b60001303240b038005082480d0440060407040012820049215800034410740003006200411240b03030000415940d03418101c0706641e4480c080b02c0403c0c012440311030096000340e040407004000d80007000380c004c0e00641000d85042c8854081074170740801151059525000483e010382107181c02c100c03007500003100c0030003907042100c19401c41c07080114409000b400f260510300341108000741c07034040c0e0703040011124042042c50195000074101d948100d42c121100742503000c4010090f030280c0f090747d058a4003c0020140241400c0c01510103900190840a051000b440004001071b024014100c002c0390716080801d205 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 282711456 1250 282710206 282710231
    0x1060e2701151d060d0902060f03070917060f07080a060b07050d090b0f1206120a050d09050301020408060105060a0c021002011410030f0b0c04051503010e0106031b21090303 76
    0x10b90100c21110070341c0b920b80e022244590740c80c001c5d50410035011000107100c2029100281c1b2314465030903039131034294001c41080107080d004802c4c20203c079400310740f110001c0780c0001403030344036042201d000c1880315045020030000f502c41c80000350f02004070400020242d864144c02d20342e641041400315140d60100100b41c5c06143d0004d401401045651106c900304101c10f2408100342c010f5a0070750900030551800103546030740b110840b4080748900426196070300f000c1d0900b40e031a0401b4910040c0030070006200051719043c14821501242c0c841005030499908000420a099101c05114420400070078048000b41e622020001c420304055000061040c401d1b20000c61706800061500111000e010010004a03c00c1d00f80d1440403540000030003659a10102e180700e05000f990081904944e0310706003c0c40d040ba2503002035051350b0141115101a80c1e039038104409580710706640f03c074407020901d028a12540180143c0014000c0782c410030b90242c2e00801401c01304d511401040e40000d80f182e04c940380c503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 282712706 1250 282711456 282711467
    0x30e0a1b08030301060519021e060603061503071205100c0807020d091a0a090306020d02120f040f0f03090317180901050a210501020a02010c020d0801060e270115 71
    0x1040798070007440c1150324048000d0228052013194054a00820300d1400b03501d4030a010800000740d48190032150f0300b202c64641660b07000111481030003031188902140800081417108160364100a0090400714240220715118100c0f80d481125107209003120b08002c45486e0003848006a41c595070031180b85400c00009250074000c1a0210a00a2440301802141c0c1d01c0551024411000103000d030351005851800c980380700181e8405001c1c688003040010500c0302d80d400038942c94408200c852081d480c0c510b83d100c080c0d0030a40e4001c0035030011150354000031300149914262a4043e007801c0f0002d9640e0703100d00c5450741190300c1c002d0382107400003402800715003410700004100605551070300c05981000080fa2030680240511000b00144104e81c0d400440c200030112a90b982c820003d48d2504c4580a01901a1002c1075403100980641c0d0712039904140324692840c1212038958416148a078264207111a0840e140c0e003800c5000440810320304c1003140400028003c24141c20646c0e40070301c2c9003c00130030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 282713956 1250 282712706 282712709
    0x409020f0909070519030b06070213020c0709050f16020313080d090801020c0d08060607021f0809031305090403050405040e0616170105043c06151e030e0a1b 69
    0x1030104c140502d141690806494411941550134005800c55140380016098001d06200a501010014015038000a560003404111090320b0854400c15200d20b605803d540c0104c0d2102c03540001040080e1090b1403404000ca0b00380114015245000791141e41c80851018541150030585c1c0b180000b040d41a600c650200024a0010021803c1400d41d0a085854144070300428003001407084c00328100d5034401c0d0884094981c01803869100d02c0201882c6101078501d0003134200410007050000d054448044101c509850b41c1201066405003410101310303041c000608160100a0140300116171502d03540700c0c00c02d080740038800401d42890009c03020520310480304ea04604020071800b1040c20340d42e100700300340c3c103682c402c6070003280243d0310001c52a46800042e4481000d4500344c1440e00200703002403541c40c240740d6044000e1200580712858851640b22485c8010005500404884c80070118040c1150520b21149408100c020a16803410320304200e600b001d40c1c2c0300600c6003000c00600c00442040c0b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 282715206 1250 282713956 282713971
    0x60f0305060303090108060f03030705060a0c0c0c1a070803010b03190b030c12160608010602010605030109022824031b020303010303050c03040e0a0f0b040603260409020f0909 77
    0x10081ca8608003103a00ca0082807103441c1444240000f15615640c1d018940742260b002504503600c649603805c090340d5410f000c0d9000040c480c68002c1e0300d40d8492080c0140810590130141101c1d1080c0782c0481001002440c500420f0100810300c02c1078002600800110300800801241a40740c2c1000c200016040c242441240310079480e000e040196620702060200610004941a40700007001d00c00c09410500d01b80250705031002a07280218080b40c100d02410b059645990080107140c0e254003d0500325120000080c1d481003450309140c1684d101e0328407a4650520b020300d140c3d2a1a0385042140407112416881c0c050140e4860004c1112640f42c40795200d000c0e01c0d4907401008081c0e00c10007940300e101c1804041c0030440d002544055802080003243d0003000b1000b2070400500d841042c02c0000c1451010b42c401241c101a07101065217081d006010659400004030010800f841002c44004181d003009076604400a2000203540005803010300808142c44d0515503a6650030001c00290b01c000801c0748 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 282716456 1250 282715206 282715211
    0x50304030219110103090302011104080a050609060c0313020303070c030302010506190b0405090603070f030b04170a140a2a0b0907080303060d0f12120501060e13020304021903060204060f03 83
    0x20b01090f4140049945208203080c002440f42807420100e01503c104c00c00501c8940d80064001601c00c000a05242110f0040d829a0120b495018600d511401d050f200307a01445424008154020750503850058140c0c0b005007140d01d0710a00e65102003c501490b072040d40980d5641e400c0100078149285c4101c00081100d5034001300e10b0400070000424040e500038580104070007000603440e40c404100c1c05000d428002849019582d40e032070245291117048900300d880ca0703880c003d8805041e14032020344480c070815841c0c010054410f104915840d4104a11007020080c3c1800c40d80c0d00c0e4404401e081c0070b07010081c12005140a01400e0401510001a10302402903114000c104034422011040e60303040343c001c80701c810140f040e5042c280c0380030b402400f0142140c2c4052500341c1342c05811008402034000e0b840b400b0300c22603985540c282c5a02d00f200f906680c00c21001c4182e42040801c40d1700840d4070501c001c0883d05002c0e40b1310020a00003099401c21a0301640c0020305010381c0707030020030703640c0b2074000c1e803805 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 282717706 1250 282716456 282716503
    0x20106090603020108040f1a09030c19021c032a050c0906061611060d0507080702060c0403020409170a23030c070609050c1e041a0d150b100503040302 66
    0x5c05404c00100003903d4105006501c00030021114415078008842c0e44e448074540c00c04042c0359480e948840071500252140d2008206804406090700c1800b680007401101d02003417000c40801c20145500084003005100e41c1402000f900c102d010081c1c40c44c40005a090180440c80c4c201d241c02c4a0039280782c8210031030010411503590303113800c8942200c00c11f21280c1c8407002d01c2ca000000c4c0103540e22001e45c8180041106107400b8180e0b17100601c07480c0030790b4851541380c4503180b09a03100d1000342d51910001e201040280094201600700462941c41485984c2c9008030680a000d03407a04aa400f010008001502151180d0141d402a42c001600c404290f072450400e030044051510603010002c00103900c0300c501c2c00900405002c041440308010300313101c2c1d031300c03541c409021407a400c1c17442c4461089241c80c242203121603084020607014a0040c1401141c81c1ca291182901003032142c040307030201034451402c1900c58031201411482a626500e0300c6803282000d00d806400c217103610030104e0004680205 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 282718956 1250 282717706 282717709
    0x1051e18070522021c0f06081e0a060614100f0c021c02030604031e02060402090c07050a05070303120b03011a010f0311030c04030c060f080402040c0c120f02010609060302 75
    0x1c958003203403000c9500c10b1114882c03100038252142e07080e10a1507258408250640c90001c0400c00360b04800600300b041201e2103404406804a03072140c094004903512803185050707001c0300302202d0b44006d440c50045506e00c0c400ca69074241514035031b40041080700c03108041030045040407a0716000e0102c0d2800c0049016094003001048814040b001034401e201c9101d0303016900c100070700750311403494016041c6c2c1c1c050b00d41800c0203841450141030702c82600c80b444011071480f03880031480a00559005045050b00d858041312081c00d604546019650342c000c0c0f2540c1000107070200305540085200707072180c0403038080100000701241d607410449030083e418680b449000680c22511031030302d4002400c009241d0064a80c1c00c4004091994020000310800428406003000460203001100d10518103525a95203074981103404400c0c9148020104164401140051a054101c1c1900d00500e00e015501c801c01ca445000c803001120100d400810111074a46104035820b01810000d000c00c10f02c14400c3d00d285a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 282720206 1250 282718956 282718963
    0x2070e0714120f01050a0504020a05040e0606160f1a0411120316051f110f0d140f090c030c01020307060b06040807060807022104030605130501051e18 66
    0x806180800490300403a400300d1544505841600b05140041a818500540d108106420a0040900c18000d0840004461419000700c800040041d942c1031300f010b1900804010b42140030309141d82c004402d000003100002070413004001c0d40d00801005001140b0390074014406415540a10a00c142c104200030125004045801c4c03c0f120540700f0b25000b9401b012102d0544c02000890300328030941c880c01400348080020f20404480c0007007e4941000040038584003101d08070200c1039820102409450844610000035000402d40e800d008187c100c06000302080030720084450050070917024042c0401050700308090320303050350181d009014a162450010b944c034000c01000800341da48804280005454880a0790000d020290032507041c9500d602c4082d245100441d910030040c03242220154500340f05608105000c0143c01d0954034013030460b2125000f078880100501c1c5070a054151031030000f8000d202d500c5c41440c4000851094014600c60202e05840c0500321003050780c1282c00d00c801c59500030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 282721456 1250 282720206 282720211
    0x6030f14060d020a0f12140601060e010c0303020c1006140d02030303180703050d030623100c1b091b0206040b01050409031704060f0506010c11061308120903010c02070e 74
    0x841c0c60950002031440010708420b8207070448104205c4902c1c001070381581560501d0700e0b00344103c000000750b2140743c4040b90f5801c000d01c180c0000801d403c103440c00075402000c0180e120380c000d00e0050b20f0054014401454001104094044241d940380b0400034003000d88454034a0740c0d03080340c0316044410307913400182d52400040c1001e01403507480003103061214001c00c40c00004562203003d4580b00d20b06460094000e010a202d1074440070240030111802210000e4103c50003000107100d800d5071500c030b08088030000e226140403108135044141d10bd08500310201228010580320b9001b2030403142d84204000c16030550b05d001029940920207100009a800c0d08450542d00161400124403c003820b084a06d40e941c10080410f2900c1c5406010621409c0e810401c6004001c6005115a494540046641c00423098019000881280c0c11015624000c00101a03c05c4401540c81d80a40c982290a007408107808445031000d500141c001250704080c0240c55001809002601860b03162245250140c1c400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 282722706 1250 282721456 282721459
    0xf050301290604051201050f07080f010603050c0423040f060303050f0918070e01020118051f0b0402040801060f120203070b0f0f04031211031c0b0310140106030f1406 73
    0x1032100c07489054445000b51802054002d10304005900c1007418a4000d20003950303c141e11140c1c44e00081d5219000e039200c4d034081d40300d801e03c0181982c84c2c0030301140108805080c0010605007040f0005041e00344201c0b4440c034649408402494003070680800084074040c0c04280740250601e40300f000130903000400d0310f00d14003190b0021540c0d00380380c4000410844440c840d00240d03041038800e001c0141d078072114854900070281c0080003540c0348440050100f20307806000402c2d0303a2280b094410b01c1c409101d0351480c0e20080c49008507128088600140590300540c0100c074203691745110030131048044541220080c40f00f0040e05400c015a1340202e51101000c0c020750741c024400003003007c1052000c508031030401c200412030380c3c0c03996124904080405000b07546100083c13905820411380c414040210348100907203100c0e82060b40c1d14182480040c00d070a400fa90f03414016401844c0c01e46003e8090b410003842d5008504a00b076040c568060301700e540e102c45200d4120329001c50107143c500c2ca4144160007450 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 282723956 1250 282722706 282722771
    0x1090606020a0f021302040303090905060a050f040c0e120f06101212051c0e150c1b0304050901090605031209150d18030504051509030703080a11070602070f050301 72
    0x103c50002c19007032041d96020380c004c80d10004001003070651048050064854070401031000752110010031065031401d00807580e22990141c14289640360940c001d200710361107424003540440b0380303d00140c40e04901c40b030205c1c0d80e6000421449e02e180c20510000303a00c03010210080e0801400c01210541c00b00310404010f20f2204462401d051460190341580e004082c01c4110707444621420310281e014001c441114130280c4904403264620110200c2541e115205280d421b03130424002640c5007204000f603424440d681d0004001c0860302d501c80006042c041c0035910710124003145008280341c1380c907a140d04200200742c2d060141541c4c44da24092801460280b20110350745034540980c2a500905804151a421010f01000d0384101500300014000715001190500881c000441002d501e47c402d20b1902a80b41d04050401d200199002c40905490486031600416081095210514001c010b40242d070140e1f00040d003c010b5101c4070040b0350041c0005030f000788040501080f500d9890f010440c007140c0c8244 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 282725206 1250 282723956 282723983
    0x30d0c15090c08190b0919060b0a0515071a04080301030b0a020c0114040c06170a09051c020703050705010908031606020f0d0f0605030d14030c04032901090606020a 72
    0x18035080102a10200040d607110500070113a800c07800d002c41c0740855000c83e0280020311251404a4401000084a400541d4000440e66084000e2020003040342e40301c0307031700035001c2201c0d124104a0340c0c12081402410b6510388460030401c4506032001c0caa0f030050541a01044001407ca00907641101e81c41070002c110340d101c10b803501000c0e001e20b01d51603806602e08102c1c0141480d110b955a4000c0e0b000e0806242e040e92074000450308500d061000e40045015a030115102101c2a4400b15545000c0c1c1d083d100c84641e29042c17001003400c803801c03940059000c00b00a209012003405000f005120900742403421510300200143c0343c1c0211410502040124040c000c280103642e01140c40b011000341010350f41c2ca20440c0c28100400b2002d0400c01000d1030108042240d0a00251002540980c5d8589455202143e0701c0240154002031003442d01c1030341480000001040510741c609145500c4e0b480040f144407010b811040d0600503408a800682060410055540c0104c2d040a03036682050800340c010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 282726456 1250 282725206 282725213
    0x32809031505100501020d1d0a0b0f0301030b0c030f0402010e030c04060609080f0d090e1510080702010c030b0108061c08040905040507080a0305040527090c030d0c1509 74
    0x2415036001404940c0c01e5441100740d001d055010394882e02d403400d88007044a459400484c0c0d03603844081c0c03100200340f600310800c03000101b00700c0e51400c0d8400106000d00e11915104425942c2d080400050b100300c1012005004028502c003049030b0080c240e00702c00d403c41c50b040c1a0b2401e4400c010304007074140310441081401c26182403204991103a000342007402100d540300c40040004000c0e01ca00b1429005580d80711000c40d001203498021034060b6580c00104505081c090309002c41c1c00307410070421a03032160a4034015121080708880035030090b15041c1851600e200081c0c03d542da0148880d00709031410014a200d0b0780c21070710b41d98011100303a4100e00032025443c10361392150b4441002418034100804c0020b8194855000148581c1c458016501d8083e80c4021150b550301c043c0342d000300407480c2400140964105603180a102e154090f41c44008001121665055401e0a442e605240d07003003441080e146050030017100074018414074003042c0f10301c02030301c4180c00c10701c108840000321620b6940c0078061 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 282727706 1250 282726456 282726467
    0x14040b0c030d05150102120c10050601051e04091a1311070b0a0c09050a06050409020a032a08060a0812030606041502030403050d09080613050106090c09090506030328 73
    0x40020030100800c0c101304803c5071a000c59611068014401c043c40044405130310415111342000e17400c010224698000c0b1070001800e40103000b181001014082c00c00d24503026070385040000c10900d6210b54450a08100009a442d10704251041c401514a1450151074cc2240d144a0010034200066021015992040c20b0301c1307810009098205408107128440307480b030340070950150003516141d10300c0d0382d01c4c000e02541c045e0b07910a9601169052104008280c0c081d002010454010b02c0c3c002811441105840c030030a0701700c69a0840140c0800e03481e0300c0075030400b60a5401100413120321400b1441d00c0c07100c5603034494a1107a5000d01c00084049405502c841c415180908050780f10700c8529105a00002e41c0c0b1f4119110a9030603209a206044078203010f001d50b9000d80300d404000d45019030382d03030001e90002e405036001194103641c2d5013400941c1051900c1416940710255a804c1022842c05941c038060310320240085229401c10800300070203203109402c03104620300c03100c40d0a044661000c0113844 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 282728956 1250 282727706 282727717
    0x405030924182106070804030c0f1110052d0909091b0a030f0b1b0a031e18141504121e140c0c0618090714040b0c03 51
    0x2407003010410394441c4950000302580010182c4214246a018000030740742d03424050a500341580041c2d0104075068454011a60700074040c3c00c042c00110b1140c0e8407045050640c020545251a218035040210720380b12b1680d01085405250041c01c11104004500c01107444081d089080707801940440f003a9039210058401d0803000038094555403506080d01a1581038400c00c0c4002400b24501244652070031800401c04d60350882104400104142da0354038042d0b002030031000058840d07189940200c05200010001d6110b60394011940d030211218449030044501c03038035582241080c0c0504c04415022003003c03001c94005201071060704940040d01e0a040c024130f01505000340080411041c00301c5101e0144100720703241d403409803110781c494900c1d411880e09404840003a80600c910403040c10704402070418044180b081d04d5691a010000172034540c0208500f0706a1410600c00c503185290140126034031140785d0419041d075002c00c4e44038080c0d5204d9400381c4109140041140042c11030f0400a540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 282730206 1250 282728956 282729019
    0x20310060509070c150e0a06020a090e1003050a230106030606081005040b2701050702030721020a0305090406170c04060821070c05040920030a020904081e0706020408070e04050309 79
    0x19611400d2b072078000c12125250213040d007005608400300301c1004480c003410f070449400c000580714101540ea0341941c921000c0d0424092030080e0010711100540a118060045218210000d200741c6005249070400600c40703c403004203494035007000302140e04002c40990243d000c040500b1254180094201480003c0010f482c02d0340c80d000400441e19000001010454051441680b0b48000ea540c5041c0c00070b09910341c240140c20480176140080e008801a1014140040003c00d64584031310b0240e6640c01c9241302e0460b1a4040c800303588060920b031149101900000020f0715030144c0454103e80c1d0350b50581200d08540300005912403e00c021105e400020702030080090007841c01d0350410065120040d158283c40c170342011643c94951038001250501d05501400a01841c0d40b80d0310b44030a1504003184c000781c1103800310421051154000c00400c102d41c805c0e000180c446060070000d506d052015008201011041c1c0709000201e40000203507101e6040480b04040649810911030400303044541449 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 282731456 1250 282730206 282730211
    0xc040c050a0903120c120f09140d020112111602040c1b080307140d0e0c0f030c0d060e010905030c0f1902040e0705060a020f1606080c03070c020310060509070c150e0a06 74
    0x7840c02d03540c40401e020301f82c101503688040d06a20392485a0b44045013103003103503019020401c1b09005500803444061200c240e50000600347c0b6490b030f541407080d070224134503411004114130f004045103407620a5220031070403840c00706603042c2481c00400103420302e0200944008030120002e11603c0c40340101c080da41c4c455519594450414907049409050080700d80301590080703150520107410304000b140141e2000400810bc0902c84070144100e018a40d00b0a032165502d80030320301c82100c024010b9403150351250001b156203401000e0140e041884000002c180b070b03008401002d05030800030b003200d442d003a0100c50010b0a48a80920b041c517001860740250341011001c22480300700341d00450a4940341c0c0b0100c0c10f84420541080303a035044403d49000703020104d1503c00100d013260503488090746d80f000c21401c09805541040e00040d16001c482501401c0c0c03e61501014059410319101042d0441040d081440e9103400564854a001c400111020440d42d03448200c1400c6c2d100412941c82c5954206004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 282732706 1250 282731456 282731483
    0x809060a03051909052505100c0b010e1b0306010302070501050f0613061526010b0304120503071e030b09090601030606050a180216080c0c040c050a0903120c 69
    0xc1c01501c0c044842510540700c81660090b851024014070410356803040c00b400f08018101401c2000d160f20034544041e007408030700c02007071a0301c0b2001d0000d21401035481d03002030250946040281c200c0140c02040d40c2401c600280800c001d41410fa0280313400031044501e80b25034902004038004d00603150080c1c000d41c20320051000300003021600724001c48007075480150392900d01c9942000d880a0303114a603800602e030260508020710500c08003460404e00c40760450255040200702c503244030282c02984001d1000130a0000704034940d04c90031101009410042e00f149803100000d41119806a440c8804880640780711060324070981c032102032813900416251003420181c80720755807403609000460b03401d4030b00b000204403407401048400845009489002c80c000e42030314001c01070f42105080062809a0050340c000040c072100140003c808000c004003440c00c9804c081106440000c0515424808100960b0394070b50ba00074102e0342903940003460071343c458a47c00021206d0a5510781d001c0c0040410104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 282733812 1106 282732706 282732727
    0x1050906060f0c070f140906011101060b0409020304020310060b0d0c02030417030705010b0a0f03060b0315090d09080705060418090c06020c031905031204080906 71
    0x12403800c042600c02410341c140c20450f05001c05400502003400701080c5030b1030440092148104d40103c200302000480c03071512002d006241000380100e00302e1541c08094100800501211015503500c43c2e540d08810020340080c0d808a110b4007038110284040480360161030f090b108a480418074082c40d020f4000000c0c05504d5500b4158041072000052403005100c11724075440040014558800700c501e015401c490a17030614030700c5544a02000e00c2025070300c4c120301c020780e94022400201d1403030b888006403404c0c20038103d115190410030200300034180003085201184169031291030341c2640f82e01c030310b0341c88912a001f12500b084050100f0402d1070f1100041e481c150404d0603002400b50381c50b0711907007e583c603590005030250b8081b004510712410200900860b0350f440b0140804ca8811f646d50705903d81c4180032031410301100c40c6011a080c00410f00464400304001407070103a4400c03607000c = true := by decide +kernel

theorem cover : BRFrame.Cov 282553956 282733812 := by
  have h0 := BRFrame.cov_init 282553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 282553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 282553956 ≤ n) (h2 : n < 282733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
