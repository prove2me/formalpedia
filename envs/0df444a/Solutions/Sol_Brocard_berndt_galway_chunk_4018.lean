-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4018
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:20:02.472241+00:00
-- url     : https://prove2.me/submissions/06a43a23-064b-4630-a976-be25d52f1a1a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 722482014 ≤ n < 722661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 722483264 1250 722482014 722482021
    0x30e0313060516052407030203040f1101180902070314030c040b1602040906020706050703090b061c0c06051b0a03080105010318050d02060916120f03180b0d1a09060603 74
    0x11034440182c15401003290040c1c410440010404081c400e9010302c0d145c0701c40743c1959958008500701c0c0030841300a0051503d410303c18000c244c3c08030300302494803c180341c61802c00900c0c0503c659038030015805001141d038006104014181c0c0001c100000d1440d44282e01c0c60340c100880021001c0c010b0340260800f00500103440031140c1899110012069800b0b00203114114a50410600a402c5100c0603502942081d002441441c03203446409211030788070700759100548400c0280480c9030000051603441007001c00e041000b08280d10b002c0001400c03075958541e603880d0726000380001d442d10501d40602c1c5034845074040c000a60402c0240381511021300c0e000440646140702c01c10794010705840901540500922507a8081d4041882c0d40304031800c00444001c181c02510036405650b042c4103007000a89051008400569401500180d15000b4034221414035098145210041160381c0f001040020010381040c0e003c9142c0500807121000102c0710b440100640c01040740c4c140000c003224840d11000000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 722484514 1250 722483264 722483287
    0x3061f090905031b060f0103060b060d090c14010504060909051b0c07090612081801030b060409060302100807120b01030e0a0c05120c031b01020a0b0c0a030e03130605 73
    0x4211552003070220205605100c0d407a81e00501e80703d00282203950300ea01c10302c0c0c0001001402200402d103c14540e03803131340c0c83c1d2100800403500d0f51031340035400700501108952507010f40e6032254080d0b0400d1f8020fa1601c001c28170f4130664130504078180a0140070401000ba00142c5480c200c070302100020801d641e42004036400d013040e1465440c100074012070030814800001441609440021200704181521001c40710034000080c40d00410440003040345510080d201c12092410001c1811f02086c500b10142c00103c40e0340103908050903031980d8520810540c501000f07101d14811003800c01d1442030621050090200984406d107001e41511822207900d1030f442030344105401c5140d0800e440101c1c1c034900c0c110f0b003240c40b0303885010300ca0100344480380900a80441c80880341807006004011203d800e42d80150384071f10b40e0300058150700401c010344010030142c606580c03141c49021160769454440f010050100c031070340c42c3c1c050f00030303402404029115120b06010718140d406904245890384604500c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 722485764 1250 722484514 722484571
    0x2003040b0a140f16020601050f131404050a1e02010504120f060e0d0905062b06080102030c0c0114060120100216030f0c03050d020c030c06090d090501080103020306 72
    0x30ba00942600381c1040300c00180c9a00781400b034200202c1c2c0307240320182d050049a450400f801042e03070110306504c0c41d14061400c01c048072442c00f60041c008c2070025403100302000f41481150151030315000707010000c08000d00d81c0039004030800a00400103060407107400080c11405280968203c2c100b154000c502403180d88564454115031203241405100001502c0035281c003400c91140c4049603c145e80171400c1d16004082e200a000c0701c40119243d80c00300c100e580350a8482d40c0041698075030342e60011135051000e000840c400c90462980503910440607841030300311140b0071411981244a00c040c03184503a0b20000e0042161002c000309031907400001c000508020700a049448001c0c0300161850199004150040369103001707813206000101c2521041d10b201c0c010540050024504011030707950f07824582d016060540b4004110307428007070b0400f416881c00000b55480442c030fa106c1444508d03001d512000d03d03005040f00b0f21b0883c0d2207514503408a50781e0311010340400044180c0382c540b003e2150000d175 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 722487014 1250 722485764 722485781
    0x20304030e0d060c090f2d151d040513121b11011103040f0504021315210e0a02040f02190c05060f0f061002032205042003040b0a 57
    0x108802d020b80620714003035000304481c8450501040d141440040c0401a0138201800c46040c0a40b400c1c3c0c6285c40780340c0000c1012601400c1d18220a2500046941503000180d000d20b603441d034546c06140207005030000060380b000c00500d88164104800c2113141e00100e07040014260340300030140611880e0711001d94591000081d5203071080c250860007400d01c96014034003500d00e042a02d0341003074041c803011025180c0c840d602403610b901710a00d004000600f465401080003200c07901081c6241909c0d000311710b0075020b0094610001034900c2101180d1a4603d4140f6060a48111004c10401d00035009003074480000450203840396075920802c40c07800a060b0100c0c3d070802003003561304c00c2406800002a1441c02c0c00d038401d5803c1e00c1000c2c0050042410010420b01503000040d020a0076504d210410442854904d52241103000a0200c8481d860818020900c2d0950800c1894001c0341802d00740000c9807540503d410f0f2036110408142448140c81c02105e4206822400e004101d68510030084041c02307150 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 722488264 1250 722487014 722487019
    0x100b21060a4a010f0e090d11100e0c030705040b0d0303020904020c061003050c0603220f080d0e0f03030402060715060b1b0c01020c0307050d051e01020c060c04030b0604020304030e 79
    0x2808551502c0c410842050580c0d50040c1000000c41d15510545a200800c45a02e1070315445003100c040d00c14005d921304a450150704c8100c07034000040d07542c06020f5549a0164805541c8590003000d40c0c1d185c140252030142c0f40030b43e130801c541c0e2035483c0091502241c0302c5000d804d0540c0021401001d1300c0d550112140002c007030342241c00608080302240300104091000359020700442c802d00c40185080421a400303100c0e00440c00c1c52600011200c2c03008440c1148040f280800c85018035070000d848000a8650b420204000040e00c01c50000c10b1414030500f20110200c80d0010410840184d6074070040e01c481076000309500d801840c40c0b18014005142c9074002600821001c0f801d4442d0300440c0d21089130100d40d02d0143e820b184503200059984010791101c0c1a4144c01030320741401181010010f90300460b000d082100d42c001418010741103007100700d01c4052241d03500083c80300941c907810800c0c2500400003c404a29045c5036441d5140c45040252410340f003103400001142c24103108100044410400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 722489514 1250 722488264 722488379
    0x180d111c09151404050418050a210206040804060e0a0906090b0406080c0307271104050102160b030118230a0b04060308090405100b21060a 61
    0x1104019205440c240318042c030442e440c0707801414062151072406810301d00700c4141d5052605000c200030182c150031043d030144c0342505110704081201040407074151802000340d40040c80c135211820780100c800000f00415941700c00d00b440300040c545400c460445103185814085000000d0010300b101c1c0f030b50b80c07160074210306125021442c01400e41c0082014007007154100b0038642e0f103000d01501d418640310301c03c0c1d05402941040045110090007001954920103402e8113114038165a0021242c3c1e0544e41060b0700004a4103206c6540c040046100040350390341d070a030581d032070940c90340c419100502030108501200c029202424840e500080019500c4610000318080c52004170000f01c0000c03203007904503d0030b1030350224150a05201d0a0300340e03900000012324000401017408007611000d0907008104c00c04c0c0d50300066450340e40010346071a003a2901c0c14210f40040710010480e003600036024622480c101139041124a514000140400013078a450340c005c9441d240c114071a003803203400c2000c01c0c0d550 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 722490764 1250 722489514 722489563
    0x110a0509011401021b01080412031d010b04050f13030f020a08040e0601090b13050409022103070b0702190f15060602010b090903040303081801090807030305010806180d11 75
    0x400301c00c802d228030710a80c00c03610311401300d01d411a0b640c49808040ca0108541801040106120403004029500340e41400b003403200302c220f00e14203141803100b40c80c9400d0359103051482c0ca92800d40201078111060703808207a1a0700340607015490501408400400b03000f900c1401c2c20a0500a03c0303030034040d503005030390700b612030740d0700e8502440380e1204031484c42c009440054041a4986080259001403c007801003a407071505101c1840000d09504200741e81c400c1030100c014039500d503042000d50080407190b01441d1299028900b26500707640c00b030400020341d00b0040d070b10032038410390100d9110000d40206100448a450f41002c407001c030003401c05840c00d02c0c18050302140c06c540540000c0a0f0250680b0b01888541c1c6050710309440780030310300004002903010400b1a1040100c0881d90082d031400100000b4004000e0b41d4514042e4842c080171400b20780c0b0381d00100030482083c004c40d0340c0032411031002c1104940d5003101030b448084025512041c0400015a1403607014104941241301189075500d4000c101d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 722492014 1250 722490764 722490779
    0x306010e070e0406060e01030207060f3e0915072003100b0d080901170a0b120c030d03180c0e040506011e030b0402060f0712120c0c110a050901 63
    0x140c1101d246000c6481e501041c1034500702403042d41c00301c983d07035034441d8007010780c0800440c060b50081d4410344a80751030342d90310b121448462161400f5100e52499a103520108844100d07007060019410340001000302c03006600012155007110f035894000c558440d00121000320340c400c1400b920501408820102e0052031f120186c0317240b00203082c03204038216407082c5044041e981c151075029075810b0b04801e80c2d9007a03a00090000d070140128a005042c10304183d6014089041680c03803c84009514a44940d0b0f0781105060940c4514100c19000d005052407111902c00b00760303604890004007081541c2c80382c02404088a240c8111701150b4000c1e0102d050550b01d8948202c29034042c0c0d0282c0d0a4040c08000241240111030044171504824000c030030090701d151624a10144014410386e0040d50402440e0404000c0c03000400071244129101c0e82040761186000b005020101800c0404c14070b000901f00e502034000544140c00ca61241c100c80250040300d0115405070309070f9105030340254400c0000310380345 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 722493264 1250 722492014 722492039
    0xc02130e030a030e190302071701090b09030304060b060306031b0a0b0d0f0f1401151404180e19020418050f031908040c0605030a0603170c0601050d1a15030601 70
    0x30090b80c0c0c00c0b200c408044412901d00142c0c80174000700075a1000c4803c0114540901e480c0d000b20608000011b00840c2c207071142e810380c02044507206c0031608000100401c0000c241b00303103c0e40b041300362496800d528009001c41d84d5401b80d500c4030785d110f07100d8031040203075603941100d13680280c081008902d4403100441607074005400c1039007202c0d5409041115890344034009102d24510030f8080005c80c0310a92820f41101400d18207000c942082040014181a080d02d40790001d200500e039003d0300c1c08400d0708014100040b12051564404035802c480c502103d42d072035a218004000390116400281c2c0e100c00314030101c58142140005025006001c845904000040b010f07046510380d01010580900700200c044030b020070100e40061110385180400d0000d28480c601560340581c0304100000c3c01600ca4807611400b42100940640503803000510078800c00040c0b0640d8011301c82994861013501710341c0e0f50403249009005641d010801d1050002d80f07000300e03041d44207441000c01390507030b459940c40e205a00402c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 722494514 1250 722493264 722493281
    0xd020303070e210d090e09241f060f180e0106030f0902180402180c0a11011515140708070807020d06090609020405061c020405090321010608160c02130e030a03 70
    0x404600400040e5007540200b0004203030751214000800d05111082d00010208c070242c019070303101c030401c1000b6504050682c0c2e150080d040540350340d045107182000050406007160956840c3c000d11050400c8510a00030813035054074407904001c00e80c106c00c1c01c0d101d001441c6000020b584243c0d0511101c05940207010076500a074026030302140681e010b881e01d02d0307040c1e80595864102010400c0703a000303424401c84c40804421003400000c145500d14151143c820300d082d801028100c0588490310b1001074000c80d01e1060740c411105c895080c03282d40d0325503410034010b04002524503800040c0ea1000c6540c0c102c038513107607107a1103c02081001c545007030100043c81403d104a00035450400443c915243c80070650021040c003011804000307460b903003400081c000141c2042a507100a0200b580e10320082201c40c40c1d010164800d51420307614001005000e640080c003a00760a400503081c0784040c1d64010303d80d042c12034055607201451703003031552a24020a103001e4410307503500021400503211303541500b00d91030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 722495764 1250 722494514 722494529
    0x71a0d14010303030605010f020606061e030f1006090b040b0c010b1233340e0a0b0304200102100e010c1d03071206020c07080706020d020303070e210d09 67
    0x1400b81c4890054600380300230032191000da48800000780710741c0746c4403008040006201458103030018400d0440b0000b50029035403100e007884000d0402ca508142502c8030340090a192504600003443c1c104990001d00c87c0c0c4c01100301c9601c000490355006c060035040000740a5020700703139052980422440c5500e646000c05034240142022025808400205407524103401034280051000c2e198881480c940c584401e82c12846880345000008002c0c05242003d00309000c0791f102c000d6403940d55000c204d1a462640c00c02d00c4450130034810711000c544001c1c40b1403130001400512500384209100142d1400500480b600e43c3c0f43c0c00c001c0c800d00f9501041d0001e0440e445591a548500825100e000719880c001140042e003591100310708121510840340e10b802407500075a00185003c400e05070603414111250010307000d96010b400100b000070b904011050100d59503102035030071420006001064902070051343c2e80701c0c0e0110b007800036000800300e0803042484030a00072505441210b2001409002c0184039041e03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 722497014 1250 722495764 722495771
    0x14190f0b0417120a030b01030e12120115080f0a090803041a16020c0d020a0302150a080c07031b021201060312120204030c0b0f040e0a06050f12071a0d1401030303 71
    0x61090b040060444550141451881c1c01c0001c252001c60003414080032042c101500d80d40c510308106010700a5002c41d1110504495550349403101d003421460040c0c0c0300402c80b06082d80d001c40b070941e00c00302c4071703030440008070464203039855680305200501440d29000d8203484000082c0410010b4035002c03640b0140c4100d00c02c45243c0d03a03aa584004820b28030b10800096000381d8030103504c070f10340b81210003c140e1000306603900b4907031660041480c101020174401301c1e08000058100610b6000700c401517021290750300c200d03d010540d175402045070b0710340140d240941a5a506402c115921110038651308448a4020021140d4908100b403403003054100d40300210348801c98040c2c01c6d4401d4022102034079000a035150100d480e005024040e980b0101a407403401c0800c0c440070801013641b0f448140141c0c40c3d514045002c0d0b00384410810040b410342186ea2095005444620744410046649801c462014100d00c0001d01c403040030f81c105203c0d414900c0c100340d10344610940790000140b038550580740680d5081 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 722498264 1250 722497014 722497049
    0xc03101d0f0a0213050f010506030705120a0603020405100b0906031012030309031b051c0509120a020429120f1504110603090709090c03172214190f0b04 67
    0x18000ca40040d94030494a8007806c0051141c1d00b418002541c0100441c80c00602e444514128042e800c0d40c1900c61102c9036071510030070400e42c506402190342116400038240c000c18a04030004005203e1500164002c2c03e01100040014150103500001411a0103120300414200d1800800500174081c084002c61b1020032145200714909801e0700d81f240e80031000381018070409600d440700300900b007144c8080000810801c94203031241c0e030fa0910170700f00030001404044110f20403c016100840819600032050604000d003000b60810b2803900140c7c00d44141000d6400b4a15083c2006c03510403c4820511420100400c943c400100c524480c80c003d03403c40304036425182c02c0103814803040d10202000d80c018681802a88041e5211500252051f002e902c2e02c0c40ea20382e50030100c0c6400300a602cad0425008100ca0b40c016071058102c60046620300701d2034068604207501070001281d20403481d40141e04401540306143d200c8500040038143c004003a8580b50342d82c852201c065070040c001c901c03a110040042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 722499514 1250 722498264 722498299
    0x20a0c0c090608030a0318020307380d020a02011508150a0203060a05010f111e0d11190807230f0610030b25050a110c03101d0f0a02 58
    0x3400c2c1a205140007841c0303041c00d298000c03006000007680940710181d800803c030700140c0e800c11400c00240012a0480900300f040080c1c14010990182403000004c03450760000c1d09403840008a840c1c05a0b02100182c4503200000100e0041c030318034400c05018002c2d04004114940c3c0014a1000d901e00c9c48032540340c954a28040d90107a0006031155504501c8902003400070750300030700d18608008441c0c40c040c200003591007030700e0b03103040513001d15510009480c403040c2807640001d01800700ca9240ba410214404400854401e070750700040c01d00300c2c1c040c0180170924001c00c04072800300d48105400443d5400c0408408007003c0c1981981e000441e0390388101408940145400f2641d6845503440c012040009450741d103a1140003070004154615003070010b04224851040304c60140d070440e038207a43e01c40c0c41d545042c101808400a8240a1880d58400c110a01d20790b503000a121800c002071500101d402d8400941200410080d004004618012401040c414850009001c20030500840742d4032941c2404102 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 722500764 1250 722499514 722499521
    0x302010518420d0b06070b10051e0a0b0d060b0c062d0403050a11010c08040c050109030b0c0c070503070303020c0a0b0403030c0f052a0a06080c04031e06020a0c0c09 72
    0xc101c0c495a0081c0030380c01e6040c501e540138140089000e40b18502e094441e0f03883c01c2c11180100e80740c030030005180c0350501c82d17818801000150800da00184040503060880003626420a522071a90280e10025101d050f9070b605811200003071030750004084e11450307400e00440d240e4804030b503240690344843d000b40c8141c8070100c20f1244141140100c001c0561200c1c0c50444403a880342031b420040c0a26412100e0f040c060921651601c4c0c1442c1c0c0d110552400c003464200c241c042d1640c029410004141c4061011906405105421680030150341b6a00c0c80541881e41c2041c113141e111950601401c007000080c1038021684226554045441d1840c00340c468a0854030b5010340c4c000500052101d000307182c00204060801080540038108482000300c00c6c0e82c520007021305406003141100408103200c08a42081221500a0811410101301d24030340241c1c0e28540303004520000d459a403444185540008402240c0280c8981054056541c1c0f00c103400040e1040c00c030741104031458200304c000018140c00341e21 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 722502014 1250 722500764 722500879
    0xa03090b16050a0302030403050f0409140702010c1704170403080c121303060c11030a11010b100e01080414070905090f070b030c0c0c060408010c09060201060f0302010518 75
    0x1203a00d410400d16030004c500070b4000800032428007808001c52017a001c0501701038002443c140d04041403540641c4014903108402404002c10b6a05110303080b52000e0b081025240780c0c240d14114030b241c0d40e4580c02d190007107481d484140c01c8082400034010060040010003017108010780c6045800308050710b010340d111032040d00703d40726440390005000e00014103190464000e0655071318003240301d201d440d228a41154080c220000205041e45c4105c600f0075801e001d5652210343c1242d120320040031540000d402c07080c00a0009040001300000202000031081c60b5078805c0d03400f2002c8401c01d64071010904010f280a039214001c2e44200358001c4c2d02400c00240355001c3c0d8465184250854aa50200710b14540180c040007859005185080c04280c8820020340002c05151001040c2c5070b599050182c00410260020300859041203414040d801e2894403501c1101c2c0d080c6011035550034440d0100c8a052031001c5015845024540894648814100c02c5d40081111003c1042c10640d440040c809211802 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 722503264 1250 722502014 722502017
    0x3090d0e03071404021c020c0d170601030c0c0b070c02010809031c180209041b080a0506071202070209131709010e120c03060a0609050a05130f060b03030a03090b16 72
    0x1941c2c24426880211a0040c2112016001504105100c811902c080b5491500750903495400705652041c50006c1141c50301030040b50510703040e04c04102c0342c9201c0084000f000103040c0b584a50079240c07264459600c0e100e440ea08020205a50b04001c00010505414081c042c1d000902e1140455001c00700441155005c025940241d895000445049400340850828203400c0c07400089400703016840d981c2c07165224074800c510307100c01000c04042c00003a078140c03500500340b079903c0800082c00140b000151541c01083c0d505003000301803101003c050103841360340c2c0001d40054114060101201c603110340c0d40c00e641e1081c1d8000f49110856465501180100c4140ba030000d85401c001081f103092000d40a09a0400b00041d00d502e40c01401c0031a00d008000d941c040126030783c444080045403014880d0681040b007800c014041401c1021007100424a0041d015127000c03101c0302c0f08020003045a11045079140050140da40700c54803050054020071701000c090324084001d02c005011705225882c04028405107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 722504514 1250 722503264 722503273
    0x7140c0f0f06090a0320420c010c030203010e15010c030804020a0b0415030b060901171009110301081b090a0f0b0909152a0706140a06051c0b010b090301180803090d0e03 74
    0x140d244000d001f5400140f000f21000c0422403000e83c1102805408041010341e240075a59516142800402c254001c0c010007010505401602c000da0b03110040d021102c0d010b142840b421740300ca0000a286104a41c030403a20080000344c0080d03d038525004000784400c154804000c1e90248406011080c402d01c0d100d240041c4048035402c3c1c5820949000d540c010008000d0801d0440d2640421030441c0e06881401601260100c0100f110001c01c0041c1201824580405252565190080780c00c000f8054881110b01d925180b200f4803440c10350307000f100300c00d070014000c550340d003013240c0065283e101c0100c10015940c5d24a0010b912030114a001745049a00007005d5034160118444000b06d07904040012641c07240c50f01c0f00b4071032001c0032040d003a010303040c4110006005131510042000080e64900c0446440d03503c0303201034000c104840a000d04690400307401e10b0380c6429201c00a4010301d1186030b00c0e40782a62b10703005101400300850145210703030b00d040d040b601180c400000590340140a02c080c1b6506601 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 722505764 1250 722504514 722504599
    0x219030b210705012607030603050d02070f0e0604020c1b04181a060a09060b37030c05040902030406150501050301080c0f010c050307140c0f0f06090a0320 68
    0x1240c10741c644c440c01800211100350320307000580e0034108400d0706d43c000042d0300c0307030400d10602c0340c00e21401c2401c80d0380c3c1c002001014136000241414210622550003801d030000005034090301c0307540448014640318000d03551490b058124511940907004140350246182c0700340c080310300c401007030949038050700466408140d8000030558003220320000c0201d50070004c0c40d04002a10009809100083d0922480b1340781c0741e4114035075000c6c200b816049001450058480c0c084119665600c00c0c1c40002c0080c5004180c03030200307440c15219440340f54000214a40b00004010501c0325950060381ca00c20340d041c2e2650100d0356800110780c240420300809017941c00685003c43d140c600303404040f40390001070400c44a1880c454a035a82560003881d01580c0c03180f16503402d1000c0c003100b0700c954407401200b00c84a4450b4402800852900e40401904030f01450340000c0c104000e640d001d0812009562100301d018030480c801c40e213010031110000340d550182d0715a5800460510100b05076044001b84201c284100e81e2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 722507014 1250 722505764 722505767
    0x1030803060d0b040f0209072a210c020f0306041e05100504030f030b01021222080307080a0e01030b09040f06090b071808070e16030219030b21070501 66
    0x24000703003209034440c1c0b46aa811002800c448800e5110b02e00808145c4a0508240140144910003e00b80c4042209100300380840302d410350340c1013800c20301d8480b81d042c03147c065103403081c200d003920f84a40f03102420210003d20416800792410030300d0ba100f42d541e4210822031000b4107a82c0e0710141c2e401070188083c400c1c41034009851084092403180a03a04450400e1849494081183d500b03a0303017900000d0b4445109030555400d4054454118820320082500403200065034010f40144002c2416400041c04424000c20103545c082d07020f009800b0540355213100501e8008882c1d070001400402040203039000e000703d50b020f840340c44940320020300308100a076150f82d0740c403807425283d00c41118156507840340303071000c2001c040d01c0314860801500c4140380e100ca5013a1400c810022580034091640c01002c0a0080580d0585079940040c94401103282c1e9103c0860140c3c081d000f0400b0b40000c41c01c0091110401640c1504010504001070301c4162410910034a030503c540042404608607a001601c03c1280b035 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 722508264 1250 722507014 722507017
    0x30d150b0322030225030204050906040314090a0503010c210c08060f19030311010b0f132d1508161503091713051017060f09090115060201060302010503010308 70
    0x20f01c00e02c1500c4420000c0c142003120740f55104510550320034820302c14811801e0138440c0c20307002035805d8018401468aa40c00821024914866059024010400c8a0161641a503100c05404020000d000c1e842c21024000c2500c5400f200300502c0c04400d50b41d40e508100e462080407954069aa0703100e0850740c40c10280322216240c510320541100161008480f084100c0445c140554481c0d40c1d80341104e020a542182920b80799515603108821030b4603035400f66921825820040c0c1c0f24101d001c6640c00e120521411084428020004050911031201c103a10345903500c00e900070300c081c64020355203640361072030355544409180c1802055196400300b40141c003000b00c0d400c0c1000f50203240100d4041031513610420112804504125000800f00d030303220a178240c90f001400603020a654084205090b0600100100c0e0008100240307424900007007005030702d55102000040c03001501407115810402244d034001c0ca440e1503040c18510005001103042441800b501d82113a8050f543e10b4150790a61310b449246 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 722509514 1250 722508264 722508331
    0x118050a023a1506081b061c020c070f05030d03050c04080d09030203071505030406020304020102010605210d0509010504030303050603070f0803180603041a04030e03030d150b03 78
    0x100a410035561071401c000200c141c000030310101c558904401d40e01e0b10400d10401455004032282c1802c805110340b080001d520301c4001e042448103200381b48800c002c15030300c2c41400b0040d41129008507a030354600700c56030010003000c0310034002c07035400079030780c0400d541b0071483c038025558590091390383c1c085101e1098212907000302072500c20b60b1a0540d6041e0152a01011a58080104100c0300c17041044d450306220100041082c00448d10001e00c2000005000b40300040006040a50220214096903c02d60103000648405406940c0c0041d500065440c000319078400204280300d0f06580f515454402c809031150341034103841d143d06190650354281c000c0d107070050060b5018400c001c0c2c0047c0c01c041c0504d0032001001440b016641e1504c11042c05202c400d2080c0c0038500581042041c0b000180704200ac5c002404c262810900c21a01d5038a01201c03800080f00610f64544000300b54444c0d041031562001e02191801510805069540d80b0000c2e103a0004584810794080c004440c40d01549011011819 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 722510764 1250 722509514 722509549
    0x803030f1e0c0c0c10020d020f1204050d0302100f1a030724030b0a0608100f0305120705011425020109051908040f030606050109120c23040e06090118050a02 69
    0x804400030130204003004000d0001e0401a4080011035420680510000c006003408102504156100724900e4446201e140f01c1c6600415000c0214820b040c428802842c02c41c10b404000e00021b07641c118400090701410035070030b02181450040307400d40e00e00001c50004860046d803c03503a240740e412504100962a450105007459103584980d0301a0703032040c2c01c00000c0e02c104d8176040030904000d020001d004501c1d410196900d810500b00f400856400a12a42150704050a055036403209250060150601b484820b404508000c00e02c20741d804510700b02c0d4410240004460002506003034100c1c2600c5404001800d650001c2408609003007220440260141c080c8902c0362600d5518080060840300310f034800e03600e956403131006000c250390203d0840b0060201501c800c40008071520bc21080040da84100c60041122012030b66030240b0009621030701400042040004120940707030030303407640f400320f9000c201c039407030a8100000721400c070484180e03c50304403005100c00b88003a0b0078001d003485001c51059 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 722512014 1250 722510764 722510773
    0x604030207140d0b01090203220c03060f06090216030806010f0504030209130b0403050307031b0f0806032503050d0908122818080d140708130803030f1e0c0c 69
    0x8040341344001c885008055903e4016902d140444081800760f41514115000700d80601c2d001011a80101c2c0300019a500600c002400e402c41c017090a00074199a0301901e40e180c004070340400381c01100d17000b0307a8041e4040d40b503c250320740d40c070401180c46040001c640700c0401c01c1800140050704102c1a400d034000c00e42145006485020346440002660407a001c41c00030314000100b003109a403500a050210015200380e1303031010460f840140c0101044d0002c00d080050131000100159001c1088001c030f40e40d101d040c0400c4298424030041001d4007400b040d1540e214126990400303078400c2c6003200491b40d5100260200c1900c4110742c1c05c00e60700c1001da0107664111420b00c1c2503583c518440360614100c8036220602c20364075542504801d00007650200c5110380003514101c4880780c0101d0010210140c500e0f985646e010340e80307007124043c01007425455070918500c4000c284e48070000000c40c0a600c0c018500c1c075103690b80700c00c01c0f005507404020b0780030401d07030744008107619192030030250210101410654 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 722513264 1250 722512014 722512039
    0x307080c010e061317070b072d090812030c0906030a0f021303063914490f020d0c0e010e04020304050c0d02121b0a0503060403020714 59
    0xd40b0f0801d050300c85401c4503c0c80c051030410030400b80c030030401184e41c40c441182000210785503045d604000502c100c0074000405000c901102d0f002d02080d100e80b6040031000290310040000420003003950003604440d10a01500d5482c0e103500304c003a2171180c1c0403000e203245080500014000c098102410346a03005032500c02801c0041c2d00c900103002d9122440c071155000502c3c60520f03409840f45100c0c3d40b0820b041c100420705050001c40301c0d0344403009910051030b03441115203401f202d04c030100d100803424031040441d20600aa40881061985454600b244004044e04040c82c41d0950810710400c0040d0204000742ca000c0a142c1c1c206011503902c01c000103042140382c2c0c04c1c24040d105070020010025107035a80100580d078211420211844054808505515040e65081da8400468201324881c0895101c400110740d81d00789001caa1284040684407001031009462002c6440942002d11440201c003002c00d6904000507102d1003144c03d0b40c003e12003145480c48501c64180c801c46142d4015042c039158 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 722514514 1250 722513264 722513291
    0x504020a05040e030d021602042720180717011203080601120212040c06110c0d020f06181c110108040c0f0b0405090f010308190306031406070f0504080307080c01 71
    0x47c091041500c1190240c1c1d20952040001303c0c3c4045080350700850180c085401e01401944000006035884a001c04c0a800d518410524154003044c105502881c2144503000404200702086d0068a04d038444002d04155520303c81317041802401508a040d500d50101c1c00030034800e607001608160107040050b07600240116000c260380c0f092003603078503000715401404100440780c5c020710000c251900d4080800c1100325002d0341c44070f000c14070407442120f0004140065540b0002c4942c21940e005243ca07a4441e2204036500460180c0700c007281c03141c02c408442005a500782d0480d0890194840800614200e405005440340c0c10060410f44100c00065408540d40301100c0000780605a100443c0f07481d00e00d002c0402881c8440208410144120b410041001600f094107a41c0f0b103030043d04140c14074142d0410102d00030401544060036040b50400c0c03218504601007205070060015564043c0d4408a42d00c050b196407040c3c0c03003110240e5104004290201e001c7d0307406082100324600010074400500c488 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 722515764 1250 722514514 722514517
    0x402010f05180603091e16061d09040f05060112020d0b1810141006090620060c070302060f150114070803010b0a02070f0501090603050903070f0302010b130504020a05040e030d02 78
    0x140481c3c258001540c11030102c0e40b000c0c0c0c88400c1d05000c1b00522140c01c26000924509146108100034800405218005901140c2c4216030070320001e0700d003414030326142c2000300f500055200c0035641400703510b00215040000b0300403da08641c01030307c0704540c5401592500c036004001070401d485401c80d034800c284554824003030510658140000420421100302803458070400c040c18400403294810010802c07540c1280056040710503600700310796211441c5c864900840800f044500742c1e8000c00c0100041100c1d484043d011440c003960031034441c1d50f41c03080042c8002070180e07010004104d1103c040e40540d8441d52284101c070000e92400c604240440c0d869104980080c1c100a45c40500071640d02000381c1d0411024006000150341c0740e008030b242500180491070980142020161a100042c501740801c00407959031a600480e031011049041c10024002c1000c10242446240c1c00344d21945042d1142c0078041c0503980040002401c240350030200b0004003110103601000b80002e104044c5400114030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 722517014 1250 722515764 722515771
    0x412110a0c09150e04080a09240806060c1f02070609290c040b030403030e16090609021c05040204060e0f01030c0911031308090a09020408060c030402010f05180603 72
    0x1081c0c185241e00708111070080d24078410019800c0401c0c404100030340781411018a41054210700919a1814002c40c111840d00c20b58000360401165544d0356808000b00181c0000e128070b10703548403503254444c401041154402d0209420042c0e018140440d00700360042c10039504007400f01001131502060383d8894040d10031180307041d15800c0051101c1c042c8400124031110402800501ca19580d140002ea6860180118003d1861b8440c000c000201014001d40c4011009481e4208961804030a41d6441400c20300c98001c0b6070b801e90800200181040140c002c2c0c2d0007146002d2100c9600c045050140b60050000038401c0e83d109071211000101c00f05c1c2d4242c030754003c2c02d2400c191b0400c2e6046007000c2941340c9403a402902e10724607002e08842c60f4440d440c00c6d20742200195000f000c807440c01e400d0042d4940100244250b1294992a0019601c29280c0c0180110740951069490a60f180c0640d40c0b1580411200039020a000e4070f118025a07109000400c0d880700c00d5881c0302020815200410110380084 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 722518264 1250 722517014 722517023
    0x7060c200601030b0109140f07020a06020409020309070501030605100c1703010b04081203070c110d080c030715020a0e13060e2d040507091a0402070c030b15090412110a 74
    0x3030340140240009501805d002d803504060500494060415144002da0020900e606900364100482c039030602c00e10603200c8242e080310303041d51503070b0311688441c009610075900c0341a00d100740140040c20b5402805654100c42d030041890800b644000000d440401c102071b03080311110100b8010f1020354013004051800b907d0340058443d04c0c0c0d41000803041ca01407c203c0e0b403102e40b03a018020820744607800307841502c0495020007201c05461655011800e4500307031320b40c0100300c6e20010901c0910b0000001c040c041880c002e0398011203041c0d81502480491241c0e0040c0e00000303031030000b43c20303050a1110b1104180354291078000f90955513160704000460301600d89250141031003500041390307410404800c5000400002c41c1451b82032943e00d140c1e844080b40b2074650460346130003000840303075550341c14070501400c050400d5541c0c4848e407409000d1803202d80412180168210041050101080d4090309070000140c03d0446940b20f03030b12589180041d1495031020004082582c0f540c96500b03000e4600d44074400c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 722519514 1250 722518264 722518273
    0x50906040b0310060504030c03030c02040f1d070506040e01060c050f01050a0c0e090f010311010e0a080f06010b0f0301091518060e0c070510051e0c03160f0507060c20 73
    0x803400000070b42c400fa038000d20400c0303003d100c24004503141c10a030342c0407a07078541056110f205070703440410301402007555149201403801080324000c1e034190a035040c41d044150280c80352541c5542c02c000d0640a00d0048803180407440c4018002d082c0100301603d50746000d10226604101d5003d24a400d4070350460720000196200c40584a2480c1c001820a1015a007210f1449903841c0840551598020510000d0f0400c00148204512640070761090b80d05100081d00290300c50f83c956000559130044030424a00c2442040c0c000980407007004141e031110000c3e01d40303280c95640381900603805042c00144070010805401d40000b95069162049444544042000b04000345071510f0b01403682002030040740041002c21130000010004100089407007148240010103440300e0085d21304088604401582889026041c8a42c440a00e0065440f80d40d0405c000b6810584642c0c08665038000e9140c00f00c04600309104480020342c5e03030b4100070244031643c6000401485203180018030300c1d40c00954a20035400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 722520764 1250 722519514 722519521
    0xf0905040e0f0616120b0f010f030609061d07020102091e06211005060901020703020114040306021b0601120c091e0f090b0606090109031b3f03050301090c050906040b03 74
    0x801c807440c21045c08200c08100140581d45010802c0c003904604000e04025041844da0307030300ea0099000c20058034092104100c0d164880c3e003500800210490840c0d001c0f0006030020b1001d520500132261401400351084920b1907050b2045074031900c42d2300c50164400024031109248860980b07248045003402062105181825a10b40300c1c010f070b02c0d82189018910408c081e41040e60006030b8541184d90a1034000064840040084175a010341e0b000109800e000013001e804801d0645d030301942855200d400c2e5031340d507660f41b12a040318a071780c20002408500e045004010341d042c40c1d80110000388034442c0c01043c11a60104080448182c2d0328071803141c4c1d40d50387d0301505020b082101c090b400b49082e0782181c903280f01240007070302ca031125100050121045e4205000640e516010801c020821074404484007046c0b000440f20a850482400395038440c10100c6c1003100410038051024030340c06881d1180f8590034111500041c0c0195448038042c404100902002500d42c0304c010002091303d44001c0c0c0e120309 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 722522014 1250 722520764 722520767
    0x20d14040b06010c0506061c0c0e0708010e04030f0c0602130305100606030204080703021207080102030a140a0504120e030c031009030206060108071205070c0f051c0f0905040e0f0616 80
    0x1e0700544164108858469140001000010010340044003110b10846110303c4983d003501c81c01000b06d000700702e0105d540c0000352681c018414280202040c1c2c8420340d0b036030303200d131900154000103d13130140016070070302408461f0f0f5010300030750381c043ea0042101502e41001006c54002c20841c2d1340c01152a58030034003c4e0b01c079900081c07051300080e2446203015807034103103441c02403582c0d12814003000e07105041900c00d1402041041001000a01c440310080d9141c0c1f90490b8010010203002e080f5200002c80080000c003c454284035061103954070000000f54402c80c80c800326040c1c01230038207480d01445201c3e011600b9680401c03000341d2841d01c02d00046800504d51800138144140544920305000328101400441c032303000b007249a002d0001c40c0b4001000d90f00c012080754001c2a041001d400a4410001401404008507002d00f1046192a030170a030340b04082c0045420034481c441000c0041c0e4001c00900191800b83c001c1a600d0028000f160800040b6540d1917082003000c1e02c108101101d280000c10743e45 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 722523264 1250 722522014 722522033
    0x815061801020c0f09010b0c03041a18062a0f030c0604120801030309060c260a0206060f180405030c25122a081207050c0d080a12020d1404 61
    0x10581a6a13014600c90f540010420004041c0204403170341c0000b10740400c41010800c250790003860180f1840002e16200e99107001d50b5840107070b00c42d0402e521900c50401605280302140e1100e0001000200c0d4200c05504968040c100c6881d16680c07401b481100f460f0074901000a485151942d0010301000e060030f1030308080d0040c4650031142444220300042001c00d400468420884985083c01c0c60003080354030300328100000c2d0705d42c0e00782801145465005110307400070107000711422035007c0ba2807035160030741007122042550070456441300c3d200980a0340c1803000603040350031504c078004903030425030480b10b01800e080283c2c00720054030320060941204069800040310040c00718030a1801b004d4001d0300c641c5401e218500c1c00c0749161040b080c400400c52003250f4100020804102610303402200c928042c1410f9201050070fa031140b1424142c010344d40351030000c1130b48040c0d00c0300c0102e182203086003023614061252181d00b0707109513090080001c00946802607a85000140b090151907103858079100610703 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 722524514 1250 722523264 722523283
    0x50a080105070219050102190807120e0624060301120c0b0705030d1a0a08030409150b04050f031212070809010209131508010207050d110d0906081506180102 69
    0x8580c142000d000c0d080e50045a52903009012141c100303135030091414401d02901c0b071018000b94180e030030b0390890f420641c80034140340a400b0507600d000c0003540c4042c001042d80c0c80550a809030b40c021001095a00c41c01e2801010400380103240405400c0e881f40014105801c240c0c8068a0f5181703050079682044500380b05ca0003d80720b1100c2a904096064a03001d56070701031551100016640c4d907503003240c10b614000b80407600744030040022150315210007072940c40c0c2c0c000c0e1041c500c1e2503050004507c480c80074102c2d4481595604180281407900d003804200342000500d00075900f60141081d82660030070004010300392200d0109201604d0b040030384008205242c002e0100c2001c0e44144107040407960f4104020700e0358480608045040c240c9054184038004903580088100c0d84006088010008003050320302c00800503444000148207060f41c01074964441c00708400010300400000d10034940103440c4c40344c109a1852540e058140e113a0701180701ca07480141c10160002c0804041851341d80c0c10403c00c4034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 722525764 1250 722524514 722524529
    0x10b040302190e0403120b040218040605040c0c020907140403201507060e0106050d0b1b12310b0a2412020d05060f0f012c0a0e030a0207050a 62
    0xc0d858080520780c40c02004d4030040402c8000520000031003501d800408001000501c11942c2d0700481007040804541c207410240500e0802c14006510b19051060903074000075074842c100450403950812121001c0202540b051183e20651202c9901c04900500051486004901102d1850068221a441c10402018440c14180620203000703119103003a00d001030380c000008038001c554203020318094a240c0d00003075013000b098680d28040c05001c064160096209120340c400500c8003881c48290b0340b15100c0c1f220b2140805002040c503c0c80708a9135003409142c0da5224400e040803c0036106000080c00e4026907145c4d40000c01d2001d00c01d414411a014100160303030a009121006000111001d65446844c003846403100038130095482c1c481000000d02d9000056940a1612011220006601f07603031612600d9800000072403800301b0040d95001e0105c8441443c07942c11692226810605401000e200c0b440b034031550306d456142420070140600300a2500600b014500f00000c0c008034281c540e0242a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 722527014 1250 722525764 722525809
    0x9080a170106120b0102070315090c1d0403050c01061e080d11071401030b0d0602070308010e101a070210050c1911010c02011107080309010e0d1a100e010b040302 71
    0x960460710020f412906010302141c2c00c00400d0050381440c50691000d014145c400154510b0308800d50300c02c0c00e40070b1281208401c940d0b1200b1100310175107051200b440c14200c20320003060109000d90040c01c0b04154150000c10480d84a480200540803004091000701740d070f90505110b40c4805004036002c1c440545800c00300306c1d0103501c01c0c942d18030a40c4107082004bc1c90003480081a44250000400064090f100000701507030752501000950061405400090314003001094255200000300c0c002d13410b049081903030078140784081000400d402d0064480610070441c100058848216000144505884840d2200780142d03c0e5410a541074204065a5003240341c0034002902d440c1c094041e0301005c6c64040c2e80c050307441c80141c50600b40c010703a40b15544034074107000524241c000003c2130208800e80c2c0d03d9035103a40600500c17a00c1d105210f0010030a0503044d801010603085e844440354404a22901c1c482c0a984c1c5100b018110b802c2030704030401081d400102401982040e856000c0400304120450 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 722528264 1250 722527014 722527019
    0x30703060e0d0e040e070509070e0d0f05010e0d05030c0a050c011803090b0c1e01180804030312141506130602070e0f240d0204050901050403030e07050f09180109080a1701 75
    0x1b0749034503407800f400d80700d01001804102450f120b03003050007407010060308081c1d461800341019460030340880300c04c031800c0d820281c0e0b12141d8a070100303490041d640c0da07403110340c2541c030382c014440c0140d081502000d04001e424031030002030081c24003a8050740360381c009880d04e09804c2820000c1440c9290340002d041058100303c100c0d0303100000110318140710b0300310081c56004a060148640541b1012850700c0740d2042d8201100c05104848c2c00a01c12a40320751104086001e080d00c0306400d890003c1c081003450b48400f400114109410f51301b202c946d4200610322860201a0f40e41080c64104540118005a1144c81c0922403000d00311112030304511003079180b82680c5070441100f11000c1540e88050303005501c4041d0b200f440e0711070144407400300364004e105118501e0000b407240d000300000c407003d6002034101b000411405402151004c280c03070b0003604041600e6880414000c500700058801502c080459405170b14415003803080801c198816000981d5900d01d003440103040d241c2c00c1080703401101129004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 722529514 1250 722528264 722528291
    0x4060e18030c12210f010801050906061e0a09050c04030c0b0f0a2703060e1b010f200109060501150e03060613230714070203030304080702030703060e0d0e04 69
    0x803205481c402c082d541d500d20003540c4001c4611218138114910200300c2041c0000c3d206550034440c10307201488020071140c1e071101c080b550380c2d6030305665150f081083c42c804c070880c1184e0382c5211880000081e000d2101c0c40d99a401e43c0b000c441080390700c00598200405c0a20800190744c1b4503400405801a105040031000b4070804054820f140740a828016003401d02c3d40030100c040aa0024811011280707444a82e0700d05019000d04034896001651380078018a0700840036061045408684041c1e4480c04514070701101660703000380e01f1a81000d180c810110780004004240070b13060209100e44004038041d454210119030070001d0075030103c14403a00051080954400043d080da10090444900042101c1318111400500499060840404641d00c152003803524031791a01e0b0007602035a40d00d5005100312025140f03e401905d0740294590410800304000c110301601510714180010700392811280c0d681d442608581c1c50600c01d114542241c00d000380c071180c0104100b0b441c0303003090300d052003040318409a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 722530764 1250 722529514 722529523
    0x20f15060603060418050a0503130b16120309020a080114010e04170304030c021c030906022805010b1201050a1503020117040312091a011a0f0f0904060e18030c 70
    0x1206004d1540c8071400701d00319010010200180342c00c41c040e00c181c00c03a2400d0642e203030707400020703041ca02c1d00d9501030001c0c05035040001c43c0d0030b49010084004c184003095480741e802018030404001010f8a036900d107005652245c0716080201404000090825500310140c0c0c0da130b1405074000c2d640c14003403d0821005c160111642903d40c080000140e942c4c1c0e507a850305031181e042c00b26000e50000c8040401c02c1c130341341031004100701a40c0a84c4405a40ba9030360001265203e100c041d2454001e00e07200d8070008420b83d9243c110f240c080c416000401d04001c5400481c0f256140180401d1442e91a8004e200b8286030354811419000c1c0b1904c1c5800c6134a003944c0028042e0583c2c4900008403c00c03c03c00141454824808481c25074809042401010094280001c40041e00d04100400070340040000400c025141852104400c0c03002019060410b21541404c07650011001168000e10800c600301941d035440c4a19006031085030402030250034070040364540c622038514680341175442000011414240000d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 722532014 1250 722530764 722530771
    0x81203070c0b060307030804030503090406150203091e10080106030f0c090b16050f0f010f020306030d050f070b250f0203031f051002010525120921020f15060603 71
    0xc2402c0c036440e00070204e407410040742d20180500d0380108000c0208100440100140035045505005450711900c483c40380842c0000e0800161f4001c00542d6010b040c025151444c0c065036482001d209100c050100e152140d004100c8000111b24070300511155401d4840c400f1071328900181000380070f6040030086c0c11000d540c041d03c002d20401148450407458856a40b4800d16409000c2e52001040403800a41c0c901d05458068055404d042c803103d0601214405d80340300710f8009000b131845100d0a1402d130703000d601c44100c0901b4014200f214601040da078419160040034a104e440386070754900d051844a600c15403218004210810b141c210b46680e00000f80d98001c107001410310714502400300c49803030b5104941e2141d07411804a0b901c0e132a1440c2c042d840340d442503140c3e12840d9402a07400f2282003010038411100c2c40891a070310403101c0802c130aa8045450035115401030141b00c3c2207401925001c1d9040c95140d40141c0c0007005503040000c05001441d039401580d90f00310300c3d6041260000d4154003004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 722533264 1250 722532014 722532023
    0x240f10061409041509061406030c0403020108060d060c09031203020a120b1c0b1b0c0d05030c120f061003060f120606050613080c0f09070f0e100801081203070c 70
    0x820707100850707543c5501c41d043c0010285030780000241d64440b80e40150031144601100c2c1060f001c9102d03a10b00b080000c07031f403080ca455903860749400d0660b80196269080a0200f507009100e0a40000004550b40303d59a0003072a141c82c0c010300f541c031b10701e003a03d103000e1010131100400d030040c0100c1c1821600500e44203540c031001f0340c011642283c02d10200d140d1100c244202403100300081c14120038003d400740194062071a64503100082c1c0d407407000c0210240f0420324400201d6000c540c050818a102c2d602541c2c10a00b05d4501c4c81c03a0425000c1070b2803c0807016140105a10800000d00078240b8080c00c2001525016040600c44540b030904203408407049485000750300c2080f031100d101004015444500500300080070962106942c0030801c80360007507070056040904c11a1501e031242d1901110b120301c0c0c1800100200c406a0b1405011075603123081d9480f0000b481503900780d042460380c1c1c1d002c084200e2903240d558204590314100d02c161902803901300081c1441c2042051084042c2e00114030144117810 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 722534514 1250 722533264 722533267
    0x12011706062413050907020c03030d0c03021b0c182e030506090d030b24090d0b0c0703020106091112040302150c07060c021b040b0102240f100614 64
    0xc41c0c2c4800d9100d00c100d42c03070511400001c0c841c2c03032010000303404000c1c1c540540c0e08410381d0f6219102079075074842803140c43e54554020300440c00800415004003100c10340740d2802504052040d07210320f031802d006128202254002202d1411a800e1103004040a0240c201c444100b6040407021003070710b810040c8000c0015101807200c503c0c0b00c55214200002181d0000446803c0d11784000f80c240c84440351900d800009080c590801114607040c0411001119126400082c8106054502c80c0c01d60125042c142c2202d0200007120100e4120b082031031280800c80341036580c0f0724a900d002401c42301a0b80100c4041c0f441c050316400c82d6041841640c001400e00881510161580d04041c1e180946c91401a901c1d03a0405041041c030003100700213800340d148111000c0c02007189d0a0000c4c1d80340c1c50312481c400c141070085510071050340b0340382d0402f03012044107005070b50841d0f01340000a2000b0340240c2810109800c0d48040c080c1c55840100c40d0b60340085081d144000d02424008020100072440c0341c0c1c140007640 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 722535764 1250 722534514 722534539
    0x1a040b0a08190b09270609011b02010903080126060a0c09080307051506060c01090507060f0509130c0905030109080c06070207060f03090c083c0c040207080702151201170606 76
    0x400c5170342c10b00c941012070481d82d2614103403140c10301070b000c02d200d00c0088410103103209031068014014803aa079036150f101d0b808580e00f0b25008410000004080b040d0000110302142c641c0c480c20710045d030184031241d2020034204a1250007900c0d500c8142d200340425442085190082400840c2c5aa0600214070310800d00f130312034030700203480ca004620395941254a481541000c12a000840344111117454840072103051105c0340540b258010003a0302c3e5040201c1841460103405298003641a030303d007905181540680300c402003030844410318411141080c0005205221480402525a01100e00d2005056450a1480040820000c240ca203400d01d034035520f0410821a08619010242c1070340005c031409070300301c0f4030403c3c00704401c081412a006110255207200d0344900e039012840184181c000c017400143d40701840005c1d8802c039800e481e2010244038031401070b47c0741c1c07064002807075401402c5d9031114a902680b0280c880107901c8455542616a0380900240012030030507400b4204aa42480410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 722537014 1250 722535764 722535811
    0x1a07020919090c0b040515040608040212011d0105090709060303120216120c02040e060903070206030a02091906020708010b0901090507020a061d07050306010b041a040b0a08190b09 79
    0x800070001071843c000140080b0344403e45074040c00444200302e070b4400032000030000507803030380c0310318040d410005400380005000343c2010a203c0c140b1510082c0001440960300c41d100341280801141d5080311394590060200950003084054040c0803802c20801c90145181c0c0c020745500441740580720174540103e001380192041d80c0000c4174894100022681503280b0b9400106900c2d00c1480481c803652034181e2407211501c0003e041c5115080200086103881e2003a000c00416400040c00d00007819002c02210039541c44907880c00301d5480c2c03105100d0301150708003c00a406c1c50303090b402003109a890303c141c107105030f0b85803c0701c903046807440b50f800281034442043c12800c0800703601c80980094240500c200151010311030745650015000280c2d0625501c61b800c140e00d0307540c2071142c136003138180501050003200940101d40402c4501c0c044100c0c07800da682d14423480b1641203540507034045540c45007007080c602519000000d1454400c5030404c50f030000c0b040081c0500c0c20107061500c030b01c0d1000714203442d0710 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 722538264 1250 722537014 722537021
    0x5120c0307091409072304020c011a131a222405300f0601060207030605010504021e0913060e09010b03060411040c050f070c1a07020919 60
    0x10140070784540d1a1103129010180049091034181c240070080020039030040411200142c8580154032034004140d01ca0810010300f031429003503849942041070a031099002d100e40406280d65500c02d04101d4075120030015046000b116030014542428610603030341c0007860020504510454203040c1c544007191400025450b580c5510b44000c1ca0000301071384d2032809040c1c00604241d44107031500d5868841043c042102e42114486043c0d180300d854801e0a05884450100072240d04011034681d1744007415120b10f082800c0e801000941c00200301031050201c0b0340500d40c003400c001d403070540c80c1134240036581e0140440c0182d071083c0e20381d0104070900f543c0d403058010700512046d58000e004140d195408241c4101c801c0e1640c1e5519860840410643d04000c904036115940280c00f4020341f0f4103100c00d001c0503000066581c000c00c0310030003c8000c01c0e1840b00c098000c5601610b0316000c9182404804c0d6100c1580002c0070810003014002c00c801607445804c80395000c04d0941b450041c002984601c400503 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 722539514 1250 722538264 722538283
    0x51c29030a0314032701090203100204050f0f1c080307090603060b0909040516030614060307230a03060504060b030d080105030d050c120a020312010906030f060c111606120509070512 80
    0x2152450b400c0f26258105c15000070f55014000c40070384000300c59041c501e4080348100d103d0603400220b42e101104039498115041000d1039130207881c44440c680d0010745901c031148410000c40f42c034000401807080d00c82c0d0003541140640031601b82000302a04201d0344803450700601c5045403051490500040800c00c1c00e01400742e48800c03c14000700c0294981c505603000d00500c0c001c0e90071190310500090b50301c0c94001183c2d4100ca00c04042420702d024a081e2100100608440340c0383c0160300301200000143d903d2081c24400c034013644000030115032140c205410301c0480b210b00002c114040005020310354000c01d101d03880e94030782e0510f143d85000894025091150020034104c0b058408505150426004402815889005400a442681c0301c801907421038000b804094840d20704550300c00c000841660107098401154101940c490521420042c90400800084042c07414000c100b08035054101c00084d511884003141031109c0c0c42d00e020070b13076607418907403240d0380c03080901002e680791240c0140b100144 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 722540764 1250 722539514 722539561
    0x4023717100e070c0b0c03481b06010b031302011e020102030709060804030c03050a02030d0f0f0e0609060703180c0605030f06060c0706051c29030a031403 68
    0xb002e03d40030001504105808906551503001200001c0842011134100c034410341d4540710070b070f049115a44000e4560880040c4038007d6080d40b00c204554030030740070384400385a0340b41d1003810307600d99100d2031801e10090190a6006650300200c010300600d54802e040c3c80d07002040300c600d40300e00125400103d404411546900c01c50844140c02c042c0745e1079064000354031a07d000c0d20b47d8038180b80d07100d408a40500c802c95028000030b041c0c10a07040024800d0001304100d451500c1240e00b00301031070700110b04a5075500c07010791050b559003d0414581026018440900311030b035024040c28500002d54548480000f040e0104050b134074030250b60014003003101241d07180d40084840c04c0c06a04d503a800340c0568000d40d855030190342218009515460650100c07081d20010740d001d0704805241450030755850b00048030035024004ca074801d612a0b00194880d82c003441000c840300d01c8140348582da0841a4001600740c1c80e00a41100782c041d004680c02103110901605454112a9242e075601403400c0010a4003ca902 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 722542014 1250 722540764 722540789
    0xe010b070c05100807030f021b210f04051903080d09020406050f0d0605311703010b0412021818060610090501030b0d020402371710 58
    0x8818406902420655120794107519819450304100311403080c58504210014402c040081e002900c03981002c02214080d25000d03040040030700e003010380c200e03943c00e1284140d403080700381491707000201c101c803442c00591030262840c0c04100c0010200510682c01114000d00802a50070f081c00e00c014004001940c00c0b10045440b0358103070640001038451542c06070700c12420301c81c000c141468000802d43c05800018001c2c0848100703990340f070000e040000e14503200314408032b1088613220752400a103041444421000c4d4545a806e1502200c0b01c0320400e40c00401410510060012450307001c2190306841d071995031000444900e1000030f8548800c201f0300240c204141040c0003003136074100c070300d2250850300e1820388103190f031a0020b00008000405c20b181c0002c030800b001b04002d5001364840503004401500c20012a201500842d082e84d03c4140c442100c0081d040581070280d4161003c141d000034540c4c11560401c288a00c01080e8000944142000b403c5040c04601501c0a0b180604000c2c030402c2c40701c8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 722543264 1250 722542014 722542019
    0x20f04120b101d19060503100e0118030504050d0807060f1b030b06030105210f0d1404060203120c1b060a0b090906010e0403090e0108030405010f05090f0405100e01 72
    0x105070307005540d408a071108050b004500b51154a40500e030403225403103840056940d02d0819031a41c441e030444803400a5030b4070384c081455181400400d00754500682d01141844031000c5003800c481c400100501240700390201203001a41c81801c84088a40441d0b4520750007486041599051060240043c030303261501008030b4101c1620380003101d80140d214042045081c000c44281e090300c24550308243d1148003040140042c1c548007241c080c180d4804100351742c07003100c20f550b814607003d0328156400340d90303004515a9400d19400b60a1a01510b08104420f05261600344042d590340140500e0352002c0311840300003150f400c4d1b1881940c0ea4440c1c106403210310220003400300c1d9200c1d01d0540b040b20003d8140350b5041110b04041c0038850151411070000d0100368602081c0a140e000050700c102e00704000300f10b0005a81119600503406031046070060340e651450000050015880411210103012050041092030307900e0313414001103803005480100e07450751210390010480d1035940043e9555176016002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 722544514 1250 722543264 722543273
    0xd060609050a0504020711101427030703051b01050918063309060c0d0e0a0f08061602100606200a0203190204020405120604120905010210020f0412 65
    0x4100c110340d015210806038a4680f014407080e481613290141a40e8000750107a03155040008000700d003841c5500d800c40403000400f201c04103a0307100001a001c00300f18020b0381d0f00c2c0b50740e540e0f1003021b407801c04034010501c1d145155074490b00c4000044036020a5544d444520182c0e0f4052421182000001440700e030b2000001c40380e4840c00041914614010805219031601c445441c81c00a81218800100040c0c0400d081c2d004200c01c1c1d00600009801003070a004419400c90200a084c000c410320f03403a44030720413103402e00784400040c0d1a44550b40078001c542c010040b030240030030a50303041354000302d14107000348216000740e2400c8003902e00d400c4c520745071000015089600c20810502400998480d030b0604000001c03150b9902c1c003000000e503041c0c0082c54a00d8416101c00c54011740d0a20241c405828250b40e08006414902902c401440d2600040700300000c01c8811440c4040340c0301c15040038041c1608000000790764005507900b10140942c002000380803807148105940003054500041d05582045152 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 722545764 1250 722544514 722544527
    0x28020d0806121e070b031018023f01080f010513120c0f0204020a0807080624070302070305010e0a0c0e160804021f08060a09050402030a02010309080d0606 68
    0x2485000a08403001080107460036828044280761000300500c45842d0040000000c00c2c4420f0300c80415201342600050f01500e0b0701c014511400d0031074600001e41e850b00006000001c190312814408600c10071203501c24000c0c00d034000070306040748111802d51310095100b08606646d02401103520030200c000000d007600c400203001d07074000f84000082c420fa455405290800292184000b80781c0c0304010085c802640c40f07445141e21640c000c5030401031100103900828102d03800740e400035001031452020000c14503048140e081d002201980d074007054a50f034407284038804103580c081c2c440010b0b0000b400002d06208204241c00f442d0001e00030031034951a200c0196641c81c406c0030483c0c000641200015001d90f80f45d480070722510740d40100743e860039910780c01201c924500a1013240d204103103510703400078041041d0b0a00d1002c0c00640b9490110700300b120801c1000d85556010761f543c18100010000143c401049210030b8035420300300494820400d03c2c104500c0c0c0030f00606028410314143c000116503034800e8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 722547014 1250 722545764 722545783
    0x16080d150510050c030708040305010c0f1e050d0e100605030c0909150601120e070920040302121c020a02011d0d11011e08160809122802 60
    0x40420222a00c14801001000356100307050b8400c0d0340740c0214501c02c0c040c400820540b12000b081da03145c8680c039a03075141d09401540081e1f070242e545250012441ea0003d05139882c0c0c0c212400d01c81d410390340b400e0404015021000062040040c041205181e9074500d42040c1d17642000d1105507201d105004100ca0000c04c0300d4461241300b44030f220a000d686040c580a4a80100b14040c090314080c10243d1407040d070307140301610590410441d511000c4c0300200c00c0c03180c68000810035001d001850720307110894040e6080b01c20751201c3c12007420300801002d10140112001c40354140c410400207000600c0300313401c0c140d80b103102102c290745c090203880903d80e0206010b0700300c9100340c0b900700b241c140c0030070880744003500c50030642c0d0411040f003504004502441104c448c1e8440c1490203a01544d40d407a81940302038084501c81011407811014400d4042441111b0b0a14030018900900c20b4a0404681c80da650780c40720b50440c0c80c01d00000c400981e51040c3e601100d43d24444c407484410940c410b080255200140d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 722548264 1250 722547014 722547037
    0x6060f031a01090203060907030c120606030509060c0405030318060d1401031403090d080715020a0c0309090203070c02210d05030412230c03040509040c150c020a09111608 75
    0x34000490f1403109442031340d008460181800c2d0f03c40d9200780f82078004000d501c42210034855464481c0004807818010700c4050030003a0350101e41400d2000301c0b01d00c0e1041c00b40c0340009901c0244018041a10008107440741c5403107230034242074140080070100e0014030800654030042c80c20312040350440030a0030b0105040364454540d00000341d84078a905a1030b80908940164001c16042038280410282d0014001060043c44c10340c00c488007203c0d104080380d002c0954400868041c1041d1001d05030004503041c0144082d078400d51551811010042416800703000c0244215040310828060007084040d04041d014242c0484a031a481c0c0d000c003500e82d0300212412181c8511540c40c050800c0d101d40c02c0500c428080880a41c9049801e4840e0625504078400b6a00d282c801448002400c0d0b407201c03c1075000303d00412035060260b040004043d1507001032054802402074010880300103840b0b1007804c030b04403582d003d030003c0c02c41c5500641c600103206400c05c0340a107907a11100c4106002c0030000805860901 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 722549514 1250 722548264 722548313
    0x220516050315040503091516050c0102100509060c0307020307050604080409180c150e1503181b0d020a120b10050a030803040803040516060c05013606060f03 69
    0x44030200c88903044800134401d80042c000503c031401d28a1241c01c00115030b6807403508105152142299800c1c0c400419551a48090b044100d1941c0602c0303490007000c1594024880c924100610595074040a030841ea40040c0c00800240018424000da80d060356010050300c18a05082c20205a1a00f0030301403040307802d19005100c42d001450000182c40320b035000d4000c42c0140d140c110100103400044130304005002c0307081100c071215500c031510054807400740042d1546030f0130101804440344c0100d0b54500456440541c4010a840910545152142080b10365203d4409103101003640c240041d0300c2202283c40007481b20080182c103203001440750100e40e4600325070590b5942000342e86a520b205c044c3c0309140400c08203000c00c00d840300441e8084e00410842c0c40c08550807880b428100c03450f50000b800107207080071183c200f020078068180789003022082e040034083c078051046d0707050012040d6020000322007241c4800300406508207100038006607c4101c1265600d003003100480034095161801a2203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 722550764 1250 722549514 722549533
    0x6010e01080d0c02010e0f040f020c01090b070e400209100801121e0f0b09151b0d1416110a08030412030b0d1103010b01080c032205160503 61
    0x3c00c030800003da9805944104110014105001805014190345500661144c1405108102600092031f9648111000080750206403d001c1c1c43c2c0c0310301420f02c0c01000150300300b641d03030f130355482c5004a101d0020038146c09103000300ba01c820724000c200c8980068402c02c03a9801d0941844190301a184c000c0342902d0003a000520b4002c111203000c0300b4021048d100400140c11004103114010f40c08a0f00000103803145640403545403c1c02e01d00d40ca407001c5540b0b41e202001c0040140003400b420340603040d201084a0719060188240100a00100c0d02000ba10408a02090088900e400c551110406058165164186888114010b02d0780c46030003008660280e040c003846c4d5500083e40080c10b60803040d02821521140d030752a135400d8040305400109501c80300c02d48407030394510102100c0a4403580608040542c940181400c0d185c0704d840f058140850202000008003013281140c1e844020210040c09070365405a000405092204000d003291088003014411081c95049031030640d079044040f19804107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 722552014 1250 722550764 722550767
    0x60d1503030f170912090d0213060f090902010c020111010b040c182103031d160f08061302010f02160b1305030727230412050f0403020904110306010e01080d 69
    0x40700740c5050074541e21180001c03030b17600e044001628080310014500e00100303000c1d03000521240ba49045c00b0941ea9650141003124021022056008015495061100c00c10320303000a481241200000ba05218007002c24855241080d480034070300b010010010401080750b058001d0241e1004101c1c05400b90500038046002440404500c000f41ca000e04c46a4100e039142d41c049015151200c0c0e5000340003d54212000c0310700c01030180d4405205002c0c11003052078034041401050780d04030350000318150041000d2001d581d042100d01c1c030b036042d02800c20a500707000c80c8008078a4044012131000c81e500c070f2080042007006009001f0407404007180c5400005584600402d5251041d43c4941d501c41016013095004004022100e0350b062000000e002a140c03075580c001d0540b882c000f05020344035901400401041103040036618521040e1413801c542010108107405103d841207010107846504100002010801d071401c0b40001c00d500502540c0455035510040300038680203000700e0205010300e004501490303 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 722553264 1250 722552014 722552057
    0x4020f010318081e040e10050f010f0c0813140406140102190510020d1e0b0127080114090705010c0308180a050d0203040e0a0509060402060d1503030f 66
    0x281c426049940c1d200b4101c3c1e43d80040b41d8030288506201140368040059110b0204020700010080000c60a80e1803400c075140c0c400ba40c1700d85c1c00140c801c0350841703044480380e40d101184103500780450500c500c02c2c00e110b090103002c5019174402e00c00500f12540010812501e101c000504036031040d1810f0201640300d40128010600e0b03802d08030b0040e072001000c134500f5152081a01140c500a0301542d9401205c060444260303885040c0360809213440d03001e0060034040858811000d81d521302400c0209502d000c000900402c60742c510b60901218444400700e9004555000328010400c40f002003080f2401854021403070041201d90507058003e1040c000380c0c0c1d5028850001030345a041d0341c2c40740c00340d541f68450403c4500c07000003602c440c1f00c1c4481c50000110100144608035820342c00454582c1c0c54140d544907007444c02040c0b1251641800144030201034000740b02030300183d0440d41e140d11031200e50282402400701a200342400110b80c90000b0a26400c02c0c1c00c140050400d03540c080315184c10a040c448070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 722554514 1250 722553264 722553281
    0xf01030f03080c09090103030801051801060906230412020a080c0916030914011e0e030a0503041502040b040302181017070803030a020309060912270402030a0504020f0103 75
    0x1090000a600081e1040c03010303c0c0d0000742002c140d8101607801011904141e0260030840200d444200180818a0841d840380e0302d000e2682151243c1c0e40c100314000344840c00c50f1003010240445044851040080d00060b9800403c48010042e00c40c2d0791108510045685031005034080c426018005c1911240420b0007054520003901c17040491b203507030000341d11a070143e05401c420180e490034080000380300a030700c55001140070000401ca0401c1803d21010380100219032030103a80c03404841e2a121200803003036606502142c1800c1c0e40f40e90360b0741045613030400441c00510035184005004156420031901a0003581d009442c0414103a5100c00a0400f1581c2a07404034007101104408001c40c2a031044404402e05904083d01c511582d07501400b49160025245c44181580220802c214868104015684682c280c80205100d000c100d1007002e5a200e600e50300304441c610208107960484800c4100d50401a003d001113580b846c0c00d440c500d004080030743c1c040b8030510a217041c1d00c40310340c441e0151264 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 722555764 1250 722554514 722554523
    0x1305030609120f0d090501090201030506010314010308070813060207090f021606090c08011505120c1528030b030705060310210f0c17070f0b0304171606050f0103 71
    0x40d01200d02070079009a00308030480c03140d181041000c0031318500d4034041e46101d0f40c444c4e000810000c40910005d002d6a0004000c0350400d443e01c0c60100001e1b060650540c1102c5c0c005840e00c0c0da800140c1001070750303031083d5015401010000d12000448540c00200e000484040b1b40040020741d01400741c0340164440c00c07a0b01c420a200c52420b540c00325a03180d110b410b0580c0700d42c54510b112a0b80310b242a0958010703c51403504d114650100b0480781c00d04141401500d42004042c01c45103e0800010704c0d0345c11180a41c1c0c0d000c510104110310341900000704220b0440c0200460b610000b241035008010700b40c0350700c0c4a4001e008904000909080a209690180001205075460f182c101041c405840c08000203e00142c020b0040c00c0c404114211602c040e85c6000e904402a42410210004200c204284104445500c0704c041000007040c50081d400c2520b800c0e032007030b582e00d80b65400e0409588403810004034400d200040c061030842042112003940505c070340381c240280e507284480ca5031300040c244400b91 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 722557014 1250 722555764 722555773
    0x61f050a030311011424030105010e160e030a08040617190f1503051c0c150507050d0f0b0f06070b04032001020a03060e0a05070207031113050a021305030609 69
    0x280240f200440caa0384802c0001800c6440070409480b061042d905010050000284400b040006043c14000c686003034000380702c00d515100680b440c50384006c0240b603890318400c00e5840310520900843c041090000c0480d00e42d040241403070303400c2c2d0344180f160304017148010149005603c140c0d44c1440c42990500c0f03091007081c0e44014148040c02d5aa40c07440d03141d86d922903a04000b5064041c0384000385006400078406000601800c0c503a60a40665000c2070060b0021080006840000510990a01c03001c1c0407030b2907151820b050700c0a009080d6030201c1141050322944c0034060541c0321440d500b0b0100d03180721080c2e060100f4082e55224090700542440000b200203001710380150658040c6400a42c0d502c010340804036072182c22a000032510000080d240c5404000e030030700070f0801617000181444204000d00740050082d41e21241ca01c4001c00d0155180e000010325912800a1000c030f2007000c805101c0c1d07240800c0340700020751100b14408500c2858601c081124107001074501d100340e00940061 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 722558264 1250 722557014 722557019
    0xf060409170d020405030f0a020319150902010e27060111060f060a050d03090501030f0e060412020f0a0b01030203100c0921331116050c0d05061f050a 66
    0x1607a41e0b803008110682d000e400300800603007510200401065030f035440014120340411071040600b07182c003004180308c00e1900241c11401044451440010070b4645040010b41c04440d840140d03042102c0c1e0b080d0561116180c0003103000040d2010040d580014a40034240b010b80e0303541e005660406150410b00d000d5800000043c3d0b81c0843c91107a10303007280d00140b00740340c06981c4a001619002c1a128114002003500004100550301030040c1c2c000212010801d120080200c0d413520350311003008001a00b1809004908041c103070090000d4071100001c281582c03029102424a065100b50070301c010cc1c040d00c00c505d400faa06400034481d510b0910b005a42c0e01e90100c1c6041030000401090080c0010f040c1d0076010388000048180081e40c0100c005a002104000000588001c28a244586402403103040001c2c4102d1410400c08503103480011110303541e0782c4150b0781040c07494402060348440d04401034005030820300100040e0540710381e83c800c120b41c20119178210b00d0070a1080c144a03103034114a490805 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 722559514 1250 722558264 722558303
    0x6011e0309060b030a03022413080304060906050c0c07080c030303161803060b01030c2a0f050303070507021e0120012c0d05030907060e060f120f060409 67
    0x201c580c14003820003c2204a0740400090030f26201820031000340c1d204408450b000048688400c4003540d03141c507601c0d00c40c680783d005101008003407100148182c80001c0003d003000b001c6d501002001b0740005081085151201003050035900813542101244921440052103510018442c8000c0102a01440c119200d900b003012014440b000007800707004500400e0410055240809001140140008544400010005000c9414072060001044130349001140149a9101203a80f20744841315000d04154503802e0040022010240c001d040d404004180b210039035001d0b01510400b8022204500240c0d0204c105080303440c6142089400b240c00d42c400c0022403103418849614441c4280c0001c2a920101134003c0c20003d071030805503d00d503d82c00d800e803540400c1082810301c00f406504260b0301d582000340c0d850340c0e1007099209580810158140002032503d48600765541400c410106a131114250340c00710705900b00444071110302e003044074000b8140f4070305030003000d414070b4001c1000c0c80740340c841c2041c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 722560764 1250 722559514 722559521
    0xf070f1a2812020c0d030c050c0607110f0118051213030809010516050115080313050d050a021801060305061c17040503121308061b0a0210050a050f06011e03 69
    0x70810510000d0000641e015206000074030b60a02503201038800503c4610001c2c04440340502403004000b014040c808820500003170060b0082e1850134008410404442128901403984031461025400c0c80901c4100707101811710840c84d6031045080c0c1c1c603c42203100d01c03d2a18002e0400c8500440c280000070000308441c0001000700d890103240c0319151540242a800d4880c504039801c903140da5541d200315410402c1001600090481c0401071860070010308040c140c001640d02965108000c1c03001306604001e000c100400060760301914860303103070310900e00350350061400f40310f01008a8248030005e0150300e0305e4080a0202c0c80205000380c0458210b441d80c3c12007881c80491056400820000030805c0d5900300102c141d80c0a5501890750741d4507001c03440b0780d41c20045a100303108940c018820312030481c840710a416810341008002d9074454a0420049152161400000c040545030200340010650329800051060880070243c00040c2c80f0500111141c1201c40c10968500460154400c40c4510940 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 722562014 1250 722560764 722560837
    0x3050403020c2101050105040b010f0311090d03020d110102041505090a05220e06071403090709060f0627090b031c030c091d040b07020f070f1a 63
    0x204490300100d9400c0460450f2110642c0c01a2031400c81d0500394152200340160350240c0b0741960148400103c1a0001e02401c0c1c20300c0300c2d0700a05446403041d640e20004e0790142c600307030900286040020b288a00700a903c6070720044410002400c014030200605c90140202e41c11101f6a0742d12582c090750300101251190441e001d02540444200300005039681c1c0c84603060704142556a0189241c0140170680046640004100c4100d0b084041008045504217040b9011081c00d02c10b220390381d0780c5211501d420280c1a4101c240603501e042004035921104003084415154507844501e500f4541c151800e0380b59100307545141050348009000d005202c2c454000c80102e40c801f900321000c60243ca11000c80781c3d1000011a00040d40d5440c1b40241c16a01112001c014114400d01048845c5076034041488100010f2000d480d0f0400306010604280c820041c541c4000050015512010703141c0c0090b10b4144002d214040c8550000242d507000f440c4918201e9941d035900c812000b850322800b403003032094a4001d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 722563264 1250 722562014 722562017
    0x90902161502030901060f0e010e06031e0a030e04090b0a1508071401090f080304030605040f02100909200717070506011e12030e01030e01060b040b04080d0c1203050403 74
    0x15440d00018455005000c00d6280c809000b585924201610700d003128a41d9020007010140020101f00414540000c2410340d60002c0000c1e04603908c0102092510b046100002110022010700c9085c42c0030100324817000c1441303652424800002c41702008243d0f801c41d00c01421040d492008034028030f0351a484040c400045402a1000c0c5030b5541c049030810391a940180e0302644003003100307692903030700c001c008010382241d003042c200260801c0d4400b9607034021800000c104654800101c0c040c041c1d151a20006554014203110000c1c0380d00d00c0081034640513210b070100c00c50400d0448a4040040c030303800c5620a071a0303006030f41071105541b10102c4003a00c20040e000b198008104920115406001d114060050403000c040070050503403007407903400c600d580300444604035044e5890009074480301c45030420300e0034600401d8941d000c0303000d140185560b1388180c6603c1310014000842140380400b03401100d0340d480c00d40d45440c040351010703070740800c00c080010510100227101e00c02c0c0f6400395001c40e4006009 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 722564514 1250 722563264 722563297
    0x228080102070323070b0103080702040f0903020d08220809040f0c1e261b22090c020303130c0b031e160e0409030309050102030a0506010f080106090902 67
    0x6846165007281e00c50304040d40080c492684150900e419003003e450940340001c042444c2c62201d8880306046101800014004840003c0f40c000355a1a900400c000c495440010014600c8516000e551b6009281d03051000c609414001035115214820302c45241100555401819070ad030780d102c51280c0c0c05034114943c015038a031340e28000c4d0700c618418100951b40d29142d9100c140c000c40380050303603640611036907400c0107004d0301c05640d040100f0314180c0440c05c110b4134480f03503a1182c0c400c40c803141009540e144005d5402092002c02c0480013440d00f00303d8031003204064242c58072004c080d81524510554900903900030008560000b900c002c0c2d00140f40e01070022040b0b51350303c482040f80580d0069540408103468003030945a42040e4003041500802f508805910701010388001038040814087c0c468400c079500e000490601d8000d800c86610a503002008556914000c200c11000b01003d5403103074000f86441010031112409512258103899407525280480b40c640102d00029500251229816046 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 722565764 1250 722564514 722564519
    0x307050d08331302121e011502071818032a0c0b13150903060c0807020a0201050f090312031e09030f090d0b0a0515040b06090603130b1f050d0228 64
    0x17013107200c3d180566007007005e590882803400340075080c1c0e40040c0c11442444c010700c00081d01d403540001d0000c0803a402c07200e00401e5110902e0300303117000b4114442a66452800c0c1d0850030304041d448000304444200c1140c903100844162110160060071020000b0070003400c0c02d5050100701c802102a241c0130404400920200f034a50880d04801007109065602090304410700707204001c25030080400320ba10f01d14014801d45002d48000b55252412007000e0b05101000482040d80a403003811aaa030760030280c211101080c460110000c182d0007100c280b185a440410706100801e99100c1444c05108a54011810083c140f00c010100340d0001c03980c10303032090a41558200152121003650b110300e0344140001b61524107100e110100800001450744124070f0403c003c0c00c99039a00c400d81e440740c80141c07006500ca99542c05580e440821040d000760200e480c0e0303800c01c44105202055441c001d1455803000b81003d940d1070038480c116408820003980f010503000706001107000e07440340c0704521942000071519148d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 722567014 1250 722565764 722565787
    0x2b0905061c090c08010f05070c0b1b040f080601030524012c040807060506010201110a0c1a010b1801030c05030a0207050a0b07090302152a0307050d08331302 69
    0x41992014084e80d44541c2001c008a501d84035aa5201c511410600031080f101d0340c802480e0b110040002e02c691043c140d0607001c80003940141d401401e440c019011109480d280726680c0e2382801d12088030540f1034000c101400d904407808101102c065103c05070f42590910289540096100246007080c001c140000c5000c0000044880e005034080d00280e591840c05050180039103000611a505581c10711406104072041041141c41416042c60039110380921498120a00309a200e4a2119079048100101c0c0d9820310750010140e0307030400c801d42c050700110440150290741c0d5600b0074101040b420303c0040c02c17408180c6c00901109228030f00303580200d02c084d518061200b03404e8030941d00142024000340118200384036444689090080403606250412404001c209800201100210301c0140304294040c8204180d4a61540c00390a0310414810108010041001280c401841401d400017000300105481d001d446c0094030b580d400b01d8908000380601840c00c9020b01800790b00c6d03500300131207021070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 722568264 1250 722567014 722567033
    0x307050709140a1505041e05040c051003050606030106051803010906020309070e0c092112031527060f0d060e010606020f0c090411032b0905061c09 65
    0x408005500080725601c0103280742042d20003d00101c0454075160f003111900e01406032200407101d00312400300301c000000c0c0304500c1c8500c1840d08481071310300340424041008480d10b9001c00340d070300a6070b4155000000c10412230503114251101a00040200010b001c85071282005102665040304660b1418602c0004a42181c6c0050802d03111141e000c0b040c0500d40b4000d00c55540144015030b0344060070b05011541300324038400e01d03040030301c0750744080c0012a0340c00610702800ca1300311002080d50100c540c620a0568290304c00c40380014904071400382c1e0090b0380791000c0d9030551500103500303045010160313141900040740098030840c0d010011104902d09a90380d6199040d07510321900000c04c2c1880101002400d40d0000e4000c0740a64103d20071300071800320300180c0e10041c1d00c01194004007980b100d040c10101030000c050300079010f00a115a64030b880c000c078660001100000039516041c103000c00004c868603880d42c018554051302c104088810703a086003600b020a00b0b03034203a00190003e650303074420480 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 722569514 1250 722568264 722568269
    0x1e0a0207050312010f0b040518100f080c1026090309030a061a0603040201171504020a031d03040f0303050c2805060609040803010308071a1e10030302061803070507 72
    0x2980442401417180f510161800c0c001091034012203401c2c42c0c20900004c8001c061000103c101000104c002030b50300d4802030000c0020905a2a821030294845184589412503401610f009030500c41a481c0024402c42c1c101403102e1040008050808400400b003030000405480d0760a184014810304469940c14480351000910940700090b4600001101e0520481c6501080c0c3c410f1005200300310140c2d810075500c8c41c01e03e040940040841e0345081d018030009001c101c1c0c10340c0203403010a04620040d0076030310100c01e01105a4111900c4015002c0b129600c0c03007180075400d400c01203040200000b030b001d20050440040b403182500c420040b82950141c0c40200c4050710000c1e00c250503901c0301030003028010690000b20a4888103243e14007070702c500d610b0f0320043c4001031404070005000421f11110b80c1403080504038030a429201418100d0f40203604982110b1800304503400b41002ca00481030745801d480440b5410703005408113030b466428484040300400c0d14800140410080d400010303105102c510301 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 722570764 1250 722569514 722569537
    0x91f20070509150f0d08040f030f020f030601081c110d020a0c0909020105040e040623010825170a06020309100501141815060711030d02061e0a02070503 67
    0x40c403403a040420611080c05000c00d800d00c0a10650035409481c1c0c07441d820880e050070344102c030303102040e403a0000042c810703680039104400130b0302d00100421031040a8081c0d03260080707030f02100200083c010143c0343c403820300c150341c00da13444950b2102104840c402003803004092410310225181c000484107092070a20390440c00141c0005064004007c5070a124102030030300d9442c20800c191490780080c1c0710388100d00400141c2d6232200c2c0002c04020542d0480e01100210482c1622001009411604102000c0c0500c0b03540b40541040a00d0a840011600032081d81940020709036511f400c8004080c0a80020902498082c0da00844040713103060008500641400d00106800d00e12459040222501038100004081340302c0c1041407659946800800385045216640c1182c0d16464134004846000140b5540c022502107621000e004010300c40c50090072054098551044480d0802c91302c3d00002c0303c680320b545012148c90204500048441b03940b0203500a001494004291141859504031324103144 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 722572014 1250 722570764 722570773
    0x180f090103241d07060f020a1b1e080f16050f040221010504050c0f12180f010f050106030902150d090206070b04170408100b061b100e03091f20 63
    0x3850903c100040d9004007101d181c803200300f00303500360000d44a01701918094206909100407215103007a010221300140b07020030315807240806c03c031000c41100a0900c200101130080321420084400e0110b5170b13080c00c424403140d0105103400e001c00c0280c8205082d4146800a50030302102c0103241c50032880035805030013090107084961400c4100025103000401840810b0004d00c10748440030300940c10f407102010bc890182080d0743d504d40c001202100380c0c568082c9540300304500100c03049410b43c840e141011400c5c2041c0016a02d6040a50544441c1c03800290442e4403582c4802542780790001030595441c50781c5c400705100320190000b03800358100440c20380b11411b1000501c002c204c2e140ca881d001208a098a641c01c0c1440c1920954940c0c4003404074142064482d0b000c601750703580301c004036001901031490b4000495075598a00d540c034079110140ca4003103440c0000340051000000103403440344030021305100300519182039105495201d480904c041c028074010081c059020407c0094802c6030410051 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 722573264 1250 722572014 722572061
    0xc0c0315150607030815010c0503130f05090405071208090904060b010323071b080f031009020f09010f0c2003160f0509060d06060b180f09010324 64
    0xd14441ca0450000e225801c200104400660480c0030254010303619103811000d41e240d070005881620a0082c014000e010004242035080c41c100221002d44044003640384105031604140a51900b0545010b0030f2644030003000c101d814001d001d101c02c0c45118407642424a08a0004210042000c0d10100c0360591100c00d03641c029641886496004c8081c80d42000c0c0500c1c03240325040c0e1260010300304804100c00c00c4a11405010b2030112511040d50200fa41680c64664403440006a0810741d1940c0694410b001c000602c2c40c042c0c02a221203030441644649050854001590710307005280d81d4005000144165501040000304141d0f17070a4060245558113000c88000c140c00c042072070303580408800c0b015105110083c1421001404c0d151f09541d11201600c62400164501101000040445d401c000021038a20000000b42482c41c0e48141e040c0d40c0d000c854400c008070282145c0c2641d8015011600400101e1022088000001c01e11481540401c19280500d82610f0b000b454010701c220540109 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 722574514 1250 722573264 722573281
    0x2030702100b010c111302120921190516080715060501050c0a060c020102120907080601050d03021b0a181a0301060b0a12021201060e18100303050c0c0315 68
    0x10709805503400d1030205070340c444903601c0f0700c1d45d07000b03d02215004910160b0349030248245941106c28030899042414514a003c3c1070f22503450807410022460310301019a10031003088004e09403000c1e41d030304045070f03103140c0c103414011501500300083c540041e103c2580042c2c007044e80e5400070242d083c000d03403c03032503000078100082091310150ba004504101c0c003040350000410000c035010a860381d0001010a0608131940101d01900070080c001103074a01c800107001d2014400120f05040300c1c1084250303803080e03170303683c007005568550482e0250240c0c0000400340b200085224405590300743c000e0500031030b035031503045e940711100100d0590500300359141194a0150258800700103060800c030300030300c40c8a0410306104594004c2d09046d07403c2c0410035030408400365081d01543c1c60503c02c6401d008480d80c0d601d40081241e41d8010301107009085613001a014801070851451040d80425440c1508900d035540c215401d5019800d0b840c0c85004083d070703812240d42d081c0940107500c01201003400c40e508042c4503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 722575764 1250 722574514 722574521
    0x20a0b07020d020f03040b09040e3a0c0c03060506150301092f070b0a0b090c0d051f0605070302030c0706030e0708010501030c0302090a090605090f16050303030406020f0d0203070210 80
    0x80b92400d17540240300c20800d11000c44200c6010713840a49010440c042c00d821841c0c5002c0700001c00300c580d054402d448003040d842010802118000250000400d4514440103480f40c0d800542c000e008200c400405002052041d0405134111a02a22466259222002c01121500283c118440c4503031a8030b82940c0b0b21302503403160740c0b400300b00c001a6a0005002400e00c4624468080b009200103203040c0000c0d541e840642c4451302515000c4c10600b141d20f4220900d560341d600010358800740030f01e02804078950102503001d2818800001c9042c015040c01c040041d1034640100000300c1c11480f0401000c11104814030150f0014412501d010900c0c506120a190278802c140c0c208401581c5413100400108030101311040450350150781c465015111280440e01903d0801009040c2c1c504000030301007043c00005450800c000d030702c800c4da54010f41c0451044000c8585200e038640c55442880440c0c0401c5265004014890100c82c4051406288c5081340083e030300111644400b6810420005080480c02d01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 722577014 1250 722575764 722575783
    0x60509031e041406040e0a050c0c03070b060112051918060216050d0f170402040e0a200f09010e070302070c06050307022817040b07150c0305041205070201020a0b07020d02 75
    0x607510345c10603080c0341c0d03a01404500181021402516071010603d00d102460464561172003070003e407595031030b0070308010789291001e0b62203500064a01c520740d60400014410103010b4920000348900109103626600003504601610702c0c602c90710480d050001030803030b100074030241c1d01c4490380d08100310842c2815803e0201051801080c030255a101d040720070762015a914118009565092454403203001107001844001c800c000f0030305c100d291507000d002888410201802e104003a12a803140843c09126242c8050b4503043e401c149920010320030ba40c080c0c004254000c6491a006051100c10b440780c0c07034428407039813010010440002c1803101032607040c04880a224900034101c0d1598030328500700c00200c5284d0502406000c0740000d01c50441064104450080c80e001144640301d20440c1404204031111ba0724081c007140c50300f0b0511a5083c02405950320598000561641540a4210941d0550f000303203012811405001480e00c0051180714485000311415401000f2034030076020041c1c40d2030f9015 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 722578264 1250 722577014 722577019
    0x1216170702010207150e15130603151a0c150a14061005090109170714030105040503090111120f2104121101021204060b1005040f03060509031e0414 65
    0x40000c400980d800182c0042100c8a0142115154040002c00c030b4030703444075031561503014614420a054180703070342e03002d0002401d003001e1459006583d55000d03030864a6504e07415100058404c010401034a2459002a404030101c1420380b428001400c503908000704000440505800301090098400b200d11900d4082a0884410595410174100081750b11050184103005c01c080000d107000e00d648258031140041c0703822070394207000010080740c1603195a1140a401c041000324081d04050340307070500400d8003503600036020b1803401c40d01e8801154119a4100f10a4040c03103070400d90b20349806444001e20034429120345da1138032408046858000c0c207102c0c601d11034001140b00306001c085140c017403981c400006a402e204480002c000c0b035080c064000c15910081c8103152031704000903c0155041800080c0701101e02c02c0d410003120340300b03032500d0040303004900c80d0388460399084c4001102030380080d40001030041102e0825502281c0c180b00c441c0440f400c48015a0085002c1082c075801040290007582d04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 722579514 1250 722578264 722578267
    0xf0d0c030e0d1d060a0c020310050711010203010e0a0203090304030f060527060f06010c0605130317150d030e0904030e0f0103060501020a0615030804031a0a0605010c030e0102121617 80
    0x10503010510102d24282d00030f02c42c000c002640c1017400c0c010003034042460740c00340c15501d0081480011000411044509401003034900080740309185041c400c41f810785101010202c0e554851580b114000d400040c41d01c002d506c800c00c00400400e10221524511a2181a010071141f030030051001901c88014640c07204142e00c02c0c0b4141c0300401c0071901c5548174514064039072407599004012202c1c46520000503007114940001d109080403007403480c1c2c440034042d443e500e410703c00014070307c111907104441d0f5000ca0301481100d81d2031407800354503141d6040d02038604034280b4410320300080c50f5110b056600314041181c000080c1040d082030044030481d400e003401c042251618000020f500e400e0440c400a214903915290440c00e01003058100e005560407210454540d612031030626603140300c03445450000c0c450719000565000f55800340c0c005580741a940c0c25019041564141c8032030500080c07a0341940903101030150700342142e20240494980c05d0a00030130080e240c0c00e001c04640702a0484c601d03045030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 722580764 1250 722579514 722579537
    0x2120318070515030604051b0f04031b080d0513031e201302030a0906091a01050301050412080a0b090a020d0510050a12170703030608061005090a020f0d0c030e0d 71
    0x20140c041d00c5e88030806640100302ca0fa10700c009000d407511101407003000480041036000101c60100c0182c02503038458240700f1880003052084080c071a55a01c0380101d40d9010108200c0c02c184108003502a5650303c8000401c03403a01c0350b40d01c851240445880c030742c80030303a06064002405151001c0c20800a000030600c080b00c81448040780795044100401d5200640010200c3d100d100c540c0d00500c00345804c64410000c8860601d054846c0105807030900b0071030080d04002107090301c0c040c403030030740203a03480036443e0b000854800c1d0075503000c4401804824525640e81c00c0c020203071921140c261044407140e20060340c03407543e140c803102150009020140c00f10106402844a40c0785c2c85240e030141e4201090080b64260306142c002c20072a06000c50007910100411500101609900080292525801564190380c0c034241d0a400c01340310340c491164810851404104044400c1e4028000c05921050b8036150052410005054807084445138000a80da9603081410500c107000d0500011440d03c1d20707041841 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 722582014 1250 722580764 722580799
    0x30a110d03051b070f0204020309030901080f01060c020d0305120108060627060105070f1e0c06020607121a03030301032001020d0f050a090915030605010510120c021203180705 77
    0x1c094015014608074005132400900126a00800000d40e000700255603171700d054007903562260001407186011586150100c1d80000c150581181a038800d40c2d40c1c030700d140b5002c0d020400344070704400044d010b000003004240d100100681c803850190510000401c1c103804c040040c000700c150041201014050900e89105100d1b402403089500078009190640d1202c0e51404c0003134441d000020300401c2c002148410840c000070385144060700c14080c50280032156615002a44ca551040b240c280c00101c2040c1081c0e030b0a14554000380500c0c0240005c0160340300c1e1580401e2841d03100ba0000d40303181640b5480d00c0c016510710301402101c41801e01c043d007000b203c0514003a1800401003000b03818810041407014495115410040040c00da45105200d10010380d0020b4074a42881c1c001a1803943c200b500220340c0c1e0900c05403560391070810b030756081d19218040c9030a83c02800301840403000c600403080038424071405100914042c03002c0c0040b80000117200c8000f240751044030751000340600301004080c00d10b01e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 722583264 1250 722582014 722582041
    0xa0302150c120f060a0807090f0c050a0f030e0c0d0305030a1a061b2a010206010f050a030b0901020c0303070203040e010e25020c030d03090c090b0a05010f030e030a110d0305 76
    0x1c0710719404880075440d0400013511708195904000503038810f0300d0340081d8452a9421041100004000400401c0100002101d5510036000304102040341c003e110b0320600c1c440c0d404900002d0104d02500e0001113603400044000c0120503055000501c04001c2c0244e1204522070a038072200800c500c206140c00a0b40414943d009902c812128201d4403941c50100100510030041c030b0070070303900380301442a007001c04440c0c1b469607907080c42d4018440c4000205c0d68100360944075080d100e00600c01d00c0c1942c9180c4c0d800300340c41c800606a14041d5000d11203213100c1c0508001450203124160090354403142001d80d18040d941050740001800220101031040400c442e1041200011540340b072813100d803208440a034640000314032866050300c12204000a4240e055105420280c8a80f8000246c141e5645164055811261040c0d0340000811300401c90b541c05815505004d0302e45050100f040d8110710b02050854100c20b1045002c181803a011174420002440010f4807210f490600304041e090040e20050607 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 722584514 1250 722583264 722583271
    0x4080703031103041a040602060a06050603060d03020c060f210601120b04140132060a03090c1a0904140702070311010215090f060105030f0c0405060607050a0302150c12 74
    0xc2c00044001403000d000300b4011078000c0c00400608241c0c00900201a44490b4800c1c42108014041d14000c5016100f10703005032001c894000308940d06544503c0c01b00210b1002e00e800071000c0d44111200c0344042c0d2201c42c0030344086411400760948414000d114240c241c5191046014000c1c00007040000316a00f0410b490960f41e00340700c002602e48180c0c0040380080c0f407400300100e5408604000082ea06c245111300180f0202c050035a4429034021407003035443c20f2600310b00340364842c1e400d101070f01940303119501641a00e80510031070004030b980c03000c43c08542440030f4004e991241cac0000300c00015061500844a0701c1200d040a1885845c0c280c00080d211500c038000240203043d0100300045076031007040030501d51064a00f2003c0d081c18804040b40c1c1d6038580000409170b6000d180000501c0345008690045902c45840251019500300d80c200001044028440380d400b02d414400400450001c0010b1002c0034400c1c1c00402071903041007003444503420010030740c140746082002106644c000c3d00c03810582 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 722585764 1250 722584514 722584517
    0x180618160e0703111204121220130506030a0f1413060506010905040c030501150203090a0605031f060804050105011a0901050d180c03031116120614091b060408070303 73
    0x41d0640e601c0788004c1c1c94415032100044011514041c442404040a100102c580858441031070302d40460b014001501d017004e98010402005100416002d001e80c00140261542c81040910a035210710005907a500700740d800802d0320b90b40d01840650641248a203200f0346094080c10901c03460117132039001c0c1d200e60003d4020103160319400400c0807640140086405828002d20a11203000c0442001740104000d1242c055040c4091100c00c5d4000e00200031194041d9010704001403440c2009001d07162a40080d1060001c05e90700480200b01910701e21118000e0b05055a400c07100d41401d051043c00d40e04180c01c1140300f034406506480c8040d203c0e004a074200d09081c01c1841e22090300740100001400101c0017540c000d040040080c0c10400d14600c680244c0b4400c1e15040d00d500c82202045a807001e5001080180029520301881000300a0102d40c801c04d1140d40045020751404c0882c000614065443c0140c9a0080b08010f030700b0380c0752005840300c0d04d8058030b00c582000e203801c070070030348d101d419200140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 722587014 1250 722585764 722585771
    0x9060b031b043228051f0810080a060515040c02030d18060609020901020d0507080a030b03030706060902040510050910030c09030c081b040b030c0603180618160e0703 73
    0x2045000f007005a6101044010f25003100403c2026540c24a800700b080030720405072071001d003c6420f1509409200c00a904268100e00f8603642c010180c5e10403070058819060030440490002d0648000c11061201d103108004c04900c0381041c1c065401252a18515140300d641480c110340e161560000640d0611248580046a07140f00344031404144843c50001919981c203120000c240e03e446500104142c8070f080c0e08403100034034510401c443d103001ea4500101651010000c510302948030307030408806a00700809891405051381e07240012107800364800705059401081c10040307450800d11503484a440383c1081450243c60400207410058140350800c140340e90307181111035684c443c8240728041e651020700c015940f0340ba120580e907079820f078040207544072010040c03680007401c181c0152550000050020034513160150200f04103500010300c21100b200003050b00024120f801c100c0c0070701415071400340815060100d01c3e4039040c48000000d9201c42903c0400c00c020140903810487e520051614000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 722588264 1250 722587014 722587079
    0x16090b010e15130906060908030412060f020c0a03030902040606020708101a061803061b0703200304030f051005040b0a1e09080d1406060a05030c0409060b031b04 71
    0x11410740c000c08204007000c1d00c100390045103000ca40d07032205046da101a1140d0801c580d0303403615159a4465030040003140700b81100a4800144140c00509c04150900009410000e10101036483c0004031142a00025110f09240d0254200f034031801c405003046101600083c0e00b85140d19503034909035180041419a01c550a416894000f0050141e50300002c00c81561021045618001200102500c0c3d10034010000490701c0307034191480340c21b000c54040680c641031000d95141a500a90007210f080c40c07090200e0008000542d0902c0100055071003401c10300e130303e60713120b00f4001d103030901c1041444511482c00c010300002c5180a900d042e849800e181020905500c41400d04252500140811015500f080101c2041245400144c058144000c2c0200150030959819042004080d00d140c1e420902c100070035070640384580c005580c040481c0822a140c1390f070f10f405440807500c1d05c1d84254030a6a02106202001018280c0c00d101c4003210303001103040505040c4a0306440e5010750003e1800d5003004000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 722589514 1250 722588264 722588299
    0x102115090f0503070c06090f050603090a060509150a0e060126030d0f18020f04021b0607020c010f0201200c011d1f060b03071112070516090b010e 64
    0x92403500d5010301180c000303903020314289549800941d81245d14425410001c60524401c025800032140006a800c00c000d1404050000079032021701184190b009200c80342020619500501c0d01540ba408000c202c0e020946080442080c0b0180c19108268200150b940f965040042c0143c15914040601005071070b102a140a80403040071800616000c0420382840c0d16015a00c1900c6216240f1f82c14044080d030400c0303000450780c010000a511401442c003000803412f10b9400303808070078140c680c1405209190020b461600104641c6c46006030b202c00174031641c65078081d140c0403520900c2d00007400280a0a840e8400d0315203442c40c5001e840d070010541140060782500020a920840109041c050744144140707511180920381c04480000445106070081e8240c0c0315180440e0700c102d10302821501c941d441191307130401c01d6540d00b10502c41c80c8074038011048441c0003000341d54803900050149403078010001650b01d4090b0302581c0700307034038060540d41c441c1d810042270340e42d91504803500360b00150040030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 722590764 1250 722589514 722589521
    0x2060903030c010f020a09140907122a03060e0f061c0f030c03083103110607030f0f1a19090c020601090f060b0a0e010203040e0f102115 60
    0x3040411982003061300340c0c06000e00e0340200041c4000c3c0d070780c0d480b486490f2500c0e92025a0300c01c002d0340d00a000348000520251180045605901c2c050502091400720320ba4000d219081c0000030401800074151b1545c4015094407540004004000c600107040c501004000c414140c000c02c1940210440c000701141e0800501c0c641c45410f9000e070a80349440c2d40e07401d000302400140402100410030030004903100c090f20380103100e050b642c9510300d00865492404d1a002c4041c26900880c20b12158140500112078103100e5144145029900014034018603900d04094a80c461510148030345002020802000d0100110000f100107854081c1d260581c00e00440607480e05902c2181594039080e840d50905031301040c501c0c100c8031441000e11540c0181640c80045070020b124841c2e5000040000090310390052a07140d010520500543e8100303a03680420843c004001c4030002030329420b01d07041180c8031020300c596402410350100d030180b401800b419003801c0080f043c8801707490140030884000c20300c2200c1e007 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 722592014 1250 722590764 722590777
    0x604020d060b031e060a090b06090907050c06010b09010915110f010e1225080409051501030f05160e030102131d13050d0c0501020d0614030c0d0206070206090303 71
    0x580c104503030759560000c80d1040c0c105071443c0000711140c000050b071180403e25058011140103144840040c54a00d541004040f840e40041e0058403d2182844903034a1500180c461441c50f00c981d5554100f1401c3d041c20300300140c109a03032182082c45446d10b2070b64040c90103415249a100020041001c1110a543d01680c1d02401e4030107100e0000c510034023040c103400c018143e45401c0102c40d0000e000c05140701450266040352040b600030b003105540010b0000910019484c042c9104515043d1900c0d424020b80318103c074131000014410944496a50b0b040c03040c1c02d41e030700104108014030b007003500282c000c880c414203d40007088585c0b8a032103020368007907040f41c0d00004107400340004a0303500c002440c1c1c1c0030103808013240700c4802480041d00040c0102036448000b80d200002d001510101c3c403050302c40c614542401d81c1d40790b6007800b90700d10020342841484080c1c004c48007145101c403100c404061520000030b0001d8050824803079810300589605c002c0c2c42109a04942e80c58035000b000e80403918500030507 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 722593264 1250 722592014 722592037
    0xf0e190603051c090503060403030507110d03050f0705120f070e03030d0501240e19080f0a0b0a15090f02070b130c0e0105010e091f0b0315091b03060402 67
    0xc1400020814000380c00301581c5021000c107010000d08000c143c40c482c00900c41c443d0580c001d140003030300003442036024580c03041080c18409540444840304070314102003000b50030086a540c105002c48a40c90706a110340c000b41d141313443da15100e030340e90200e45201c41c0039050a200011510200d106217000f103010310401100038040320b89464000100f40c026203000e00c9001d0850110040604044d404d982b03107103a031540e4640724450b140c5288410300c0152411005942c00c882d60b102c0c4e000c1414101404480520748055004000d216000c0c24820080340000d004040c5c10303450050b00651580240500e84111102408001603440001c086035019200f54000109201d0300d50f0100095840c002c45107501c1d15001d888619a07071a194900058024020300401d404030303489070400040b42c5000400540e003d50b400c4000301c0d030304400400c0c100c1c007886d050700441c40700c10000c402c000c8040601880d40240b01c0c4121503c14047c1000c1850111280d5024507001c0081e10010004000ea205d9404903490500754 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 722594514 1250 722593264 722593271
    0x2205030c0a0320010e071517190b120a08031806070206010611010203041e0213020c030a0e1c0f051f0c020105070903080f071112030903060702070f0e19 67
    0x11440c00501102c07511181203509020181100401141480392020041d5a0001030411a0407d03405100034a21440151300b00300c407860b9001014030110340300c1c2c0d0048070810364001128190220b82c0b000e403a051407585011344a140740f69205904001004c4034103a8001690603540d4481251100c1c4225051500001d07900c915004d001c140c4c3c2d070000c1c4840c1241d00c3c9503508040824009a200d0030303480280d5020388040c40000c1800030010700b0004184840784005c0880529400c0e14924105a0304240320400e136075000445e03015442c03070700044140342800c03003200c13201c40480000384043d088440302000178107900207400340ea8007041010040c524141030030b994551114081600b0180c050500d1425080055080c074000c90380c268003550341c1005581e4030400e16400e01e0355006101040d5003100d50241c4640c83c9182c114080c645802d50002c2c00110380c1d801455079555040149454120301504110455200704020814242034030440c005507840c06443e4019a200d020241042001629072103e44070314 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 722595764 1250 722594514 722594533
    0xd0c02030d05090c030f0106080c04020904140c09010e0301020f0301091d070e16020312070e010311070b0a0b0d05031c2c010b1915020a080301080705010210052205030c 74
    0x300050600014000300c04844d001e03001c51b01c00c913090300e105104221059000d0b507162074052405402805000801600001d2082d82803c80504450020340c1c10340d808050001d0b002030956801918143c1aa405030000c4d40b803c508a01c04e08154030051080c5005aa503038492001ca0b108156424002c46030020201c070806038544005840031402030300c01024511160038480c8010740007100361807664110440d8404150b680010981c0c5402e0401c81c544d0400d07030b442c550304005440090142ca02d003401604103074958542940646d084900041002d44540c21205045001403400002c84401909001380c05515010500703402c8003030320074a00b001c115034080a40d070900c40c460000041e1f2046103000c0081c00321403000d00500c442c40c10034060b078845100b031b008000e2080c0c0c2140100791a101074207104a80c0414400c0d102c2e1904c51704203030405102c540000b0402c006640e410051514004e00300da904000a0031b00038040300280c456601c074404014046041002480303c140146e50340d000044081d1000510b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 722597014 1250 722595764 722595781
    0x311040513170d0506011b0311010f0c0c05070617010603091509151b050a2a0c06030e060f01050d050f0f0f1608072303030f03010303020d0305040203030d0c02030d05 73
    0x1c12818290003072600d80303c006203146d885142030015808551120346d040c540240c0f42210150038000e0003161035900c41d0343c01004c1c06100e00c80c60481019664421640c155245402c3d0b0400311550f10003000c100303022003840000b030310100c0840d044861604000500940c0352524101d400074001c3c3c11180e1b40c0c9401103000c280000c040804000010601d4200304458925260b4844180c0045c0391400142e409e0084c05003c074083c2040c9001c0b130100826014221104010400103440c1c684000c40b2081c000c0b800421907035404d40980031109032080054203903444c08404160501c541403083c644200c0d1400074001c1442002d0142454110361070080d40d0058203415140d640d03950100350b5144180c41241050941c1742c00c4c820301c5406a91251002c0c02081e031400c2c0702600039403982000a41d0700900141518800e5a00b00000c1c00c100c82c241007010346a40c034500b0080d0074012a81b62a03004e250822041000580d0003004030303204180101c80010700c60110039012895402078031040c0032036902d014240303c03280 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 722598264 1250 722597014 722597017
    0x15130b0a090b090105040b01091a0a06050703020733030f0c0305010f061d0402032206050712091101050d391b17070b070906020f07031104051317 64
    0x181d00400c2c40d4825512082e041030b00b2203d003260090640c0c02e40c00b0062081c20b02a40181c42403125000d1040c0c00f04018500007403600180d50b00540120b07800140803401c040c6c061005000805c100c0601d00340e240f5218411341a00e175030b00100300301c030071b44d03111032206441f4002c1c6d120241140d0a5941000180c0d9000c0c0081c00828080c02141d890030380340d82c00010303118807400d10f0b0340c013092004aa46040380368400510010b500064008005070300c80701c0c0254940000c2000080070540503010200d29401d0080018112074540102151701d142005c1a60001c2404a4800c200d004001e1030300b96a40d032408aaa20b00410003002258224a82d07200b40740d40914045090403006068040654903410f441e220a80b081420092160103050f042c00d041d0001c07820000000341182c0844400520345402d660701c0900c2c140c81150407070003003641a070341400030f0755040101c00100c8543c10010040340c0d0464542c0400074180b50b00003403089840b039000414105189518a4070154440f070700743d0ad0351410b1980309605 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 722599514 1250 722598264 722598281
    0x312020307020115080c151b0307030507060f14040b09071701020409050601020a0215070510050a1b0807050d0518120408210a051803100b010806090915130b0a 70
    0x20040103200208044e500813406c402040f00040a0307104054103a24018216004003503009003000c1054001c50320850300344024810503110365990750b035820343c91900740112410725035022429450003200c4841c6c0151614880e4119801081e0102a80c2c0c40394402403a0104940081c0c0c0c41d1f203080596880b00c41ca0540280050b0f07030b0700e09024007003a070390705004a0b5900b10328080a036008400c004a8202200d000000740102c44c001c0d815150104401c514035015200705032607003460103079524482004041030f10380691740b0886625010146003000c210040c403030f000320017800d503d443d0b489000c620192800031502c8800300945d41135446000e0004500d42041d013251080072144d0080442422300380106110704d86800301d4180c1c0b82824101044822106074221160640049468210b43c44165030308000202c009042c032070012414280c1500010400ca2020f4405805070540c4c00600030303920800706140d45c1d50082440d00c8492a5205101c8080e804a031140107800e03142c800041c042503c403a500300144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 722600764 1250 722599514 722599541
    0x60c06110a090b0d0b04020f041401140a0f180e010f091107060c02030706090b1605030f010509092103060108090d0c03050306010e060f03041a01080a020d03120203070201 75
    0x400880c602012010384a00401d480000d05003071030500048103200040d0694031408603000860010300004a0100c1c0c1c1f00e00091407103208003281c1002540040e075034003100144207181804140d14021074041c0e003030013655030207001d001c0d18561120440d481120324140720000c1d4045642812340d1800c260310380309801e020320b809210b0345250110b004c2545005da4030001449068041c47c001c055101c52000f001c400344c0c0c803000c600040101c103000c02c07070901a04c4461405040780d10aa07080c81d50a814a8a1500b002101400307414810001c0091700482074a0441d40192104901d0340d5903144120b04007036041980601041c4250550603007100008046c40c0300b608207072912481e40c0c0b02c1c0a6103540d00d10550170581c1c00964040300c8900007a02c10f90280d600650181442c84e50001c81d000021900c0d04001e011240c00440441080188640041020616030115513400d00c03e50510620310384601441102900544405000740105840382803001d22100c0304860454503130425140007406445505404c62 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 722602014 1250 722600764 722600771
    0x20a03060b0103141b031005060a0906091d06040f02040b0708030601200a140102040504110306090c07120503070e090f060310110a110a0507060203040f08030a080105010309050a020307060c06 84
    0x207030304c0c9410340c090a00036014000803001d0800508076a9007103501c001d11030071600703d84010004130340e20784401400c08510f16840e4912040d003030500042802d001c9902c5401009958424010001540c40210780c000d6020380d008103002040c4c90011001e48110750040c150307010700140305001c6c01060710185009480036654042d5440741103081010f03880c403040110b07a1513080700c17180c0f1000070b859070b5481808910220000d401e0568420005080303c511010442807006c0c004200589031030040802503220844030840c5081200035258065903900d007402600900800101185001e80503071241030b84071200030203110031458000d40c2c82c820600142d805a00920440f070301d4000140e601d0090740d154455a404c02410301441c40c0e41208c141d000300c05107000b103000741800000441c2c0140011409030071150000c55856243c034000700708028290717204c4c0b503840c1c10500c810020303550700c02c40450448409107004512020a4201581400c407603c200039810320506d900003400302d170050842c03407145000d28000c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 722603264 1250 722602014 722602031
    0x1d1012060e0415020307030e10060f050604030305040509190617010c02010903121a0a03051e0703030e0d11041d150f180a06021206100509031203090a020a03060b0103 73
    0x54031410042d580240003003038042c0c0c00e440c440800c1c1d002c2c42c1d00c10818035000c50031192514071141841c401101c4c4021440d15030303405100540d8203103202001030a040e141d66103060700d1920014001d005038060036100b1345850002ca12074000c40e031640c10002c44045d0302080703080d54480307984550000d030040c0c60744203501702151041428010300c0380340e4a40f6055210000c500c0100340508004040c024800e0710020140c3ea4009002e4031019801d00146100f20018046143d42c01030044c5500e010015140f101d80c004241440040d500080130040034100740c441130490000c1d4504511003055030995a81c01c1890401510001040380004812240d21030301902e100040894107450020350840c1d11040c50b064000c04503940c48400448010ba0111040642d9400e001c44d80c2d45100341e901989810080a03d82c1082c0041454020300c40c0b004031b501d5003003140c500001440401c0c0c44620706800b20085000c08800146081401d100070241294010b103a044000d49034586000144440c6003654002490000350 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 722604514 1250 722603264 722603279
    0x313150314011e0914060306220809040219030b0118271107060b01090e0f1b040504020d021804090f0807030e0904120305070e101d101206 61
    0xd00c0c03031141014405905580c240054204003882c03003c40780c0240070040d400003c14a000e44995141108522a00d00513401d0090426181490260484c904541480000c000304104000c042e002281c0c05030b503040d11140c4030300004009014034030740154107000c801da080c0e03103181e810b60040040c20003d803a05c0402000c0c1131121020400c01c0d019004003020403da221803c51003030100e507001200400c00c0403444920fa0104001640c03c8041c040b20344a44400c8580302e03d603000001140a4100c0da060f20900380380c00d60118080f40b0740580088170480d20306804600b1302a507081218040c01024009654450040d10304000030741c4036201038282c5072202141101d29250030f00403001601c0c0c00c44000360780003050340c889405a40c02410201c080c801440f411400b152114000d1500c2207024541583d0001c044040103026580c3c0141108108111202440079907580c10000c80d484920a103407031400b1301c02448050243c7c0c250841d4440e4003004500c0d804140c1540700104c402841120038042c0202c9645210 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 722605764 1250 722604514 722604521
    0x5060c1524011107090e07090f11041e050307060e0a050d051203070314040606060305100515070501020d0e071703070b0c0306061902010b030705031b01050a020f03131503 75
    0x35100e2148080c002103600e10b40c4102ea10020b0703407114400761084141d844c07030b031442121811041031a480d00108000c216564180c49040319074000440144564074040e0700042841c4541d0040300c04031180c0181c02d134134a030384041d040409402d002d13045480940d22801d0150514404c1361805101705401c50300032403e8100348441e4000654480c0062403540040d22035010a50801050141016070b079075035100e10496030403617142c00b450042d4030000b840d5061034070040c25103000030032801d40780c039800300e0420035900c0d4200c06030301070b01d081c14515423640614500680640704c0e0030f10340525682413480d100f41905010610404680c5000c3e01141086012090b55803a4004d0b04000383c41d030442c000020f0450311890000350b51002004003060300d4030003140303a080285003540c0702d8100143e6440c1100c4446040c200b0449018003c102c000b81550952080c1c00303800c0e048040860390402c0350124200c9141070081049219148280c400e907900c0e41c0c1c42645442005080f8492108003800d9940e42200050184c0f2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 722607014 1250 722605764 722605801
    0x5060919021503090a06061508060906150306120703200109080304050103020d0603062c030f091302121303030c0302030c0d1d070f031104020f030403030f0605060c15 73
    0x2040111000002e55048005800080c107901050140c0b400020000e01c45204140240c0b80300414540d1414002900600c403035070003400ca41c081e10b030140070f02c2400d5640c0b8640c1c0c10b0620031061802d50380e5540c24045150900700101000071481042004010003098054030401c00c040164160048650340b0011188900c46102c0c0303502d00d410420050049501c60340050540304170051010514035a03c0d038424044600c035406528000c6244030b00c1c820300e049405d45500c0000c50103002542840b82000c0054828400c5000d010f11036054800b1201155405405640c0c8003240400010081e10307090050300d22a8010440440000746803304150700240640b00b524011100d803501d040c01c1c100c1001c0c417a401082884002c0c03030280010050a814000c0420421001d0145d00a550307848134a58505085c1c08198400074920447c0180200020b0780040000d59074055014135007c961614070307411600040c0496003040d0f810580009807244d08100c00600300c2503034039903d03902d520543d503602e182401d16803040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 722608264 1250 722607014 722607019
    0x1401090e010b010c171309020c060601031e1d01110a02010b0405040c060804170d0605120c0f01050d0608030403031e0201090507050d06020405030307061e1413030e030a0506091902 79
    0x784044005c2010071091926a101d8101c00703500c0c009407851010424100c0e544103000c0d66400080b00d0004940611207240c0000080c2000d0208956400c290b25810307042d03414072000b156980c8a40b46410b150059208480401a00200034010078902c000e1590b510008144000d9030a00c0128880c0b81414400c0c42d106030341000034050b140341030190840c0c09040c06001903854400903100080e031003c00304003d02e40d030080d40c07000180c03481ca00000d1000c10200f03030480054680055845a10944506007010113901d024a88282e6802000306068001c01c1941c020070460311022074003108058000c00340d00700c0f0726403040c444002c65454843c200c0c2a289400001081c5400011017009641400e58002803614032865025062640350404a40b80d5003144405a804580f40d00c10304500c41000105a02401c110b5203080c025043c50a0405954140141c07482c0303d410344610105082c1341c401e80500441c1c4400600340c0c0ea1400d042c1c2043c0750b80b60000d8544610b58040c1040c0207841c00945021a004c0c40d502 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 722609514 1250 722608264 722608277
    0x303150301420b09010e04020d0c0801080709090c1a040308030709030218100b09030a0212060f091915110307090504060f06020a0f02010e0d08070c12020d12121401090e010b01 77
    0x20011240c1b074582c68402074115400b4404000008408d000d01c410340d0380c1a50315070a0942c0b5207442c2c83c0c545505940300701407003840d040450002c03e007103e852000b81c2c0d000c0c030315043c0840048200302caa1403080e6880900141c038040300b031200855109090340212802100d0342e03900c526001007052180641594045020801502c003041452010b01c05054541c10090a44840150a40100b01d0a010900300c015007034001c1400c200c501181112044c1d0020540b8005218042c03456103041769a9418440142c45041003041c44140081250800b48111a0305031800c0e44900340f541025003444c00502600344202d0402c000403c4101d001c125041c215041c5a0081460f64120b40300e1202444a0041c00e174101f001200d9200e03940c0e202c581480709039134403d004803603070744036079060008003521990410130814280d1309910026a030380c29001d0319001d4104c0032140b040300c080134091314019548100e0440c82414410114034490004d203410b070485040b0b000030f0010001c140502c500301c505100005000c80d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 722610764 1250 722609514 722609527
    0x501050306101b060204080609030304030c110a15050901030b040203060d15091e060f06030b01090c020f0f07050301050114180c0409020d1b020703050303150301420b 73
    0x2000c11822074240b0240c186a10125503080806094945001060b00d5464000500f00a001020003c0325840071040018500718206942d00a100900881d0701601005000c2d176840748503520205000000c010489140024040350070018015410009a0f580801c0c074224005016050500032207229402c02044c40384c100050b540c0c2c1e1034400e00800501c007074281d582e580000c000f0301e20300400701041c40a050494010250307480c1c620265400b426059110701e0500e8810000240c602c4031450540d0350700e00c80401c20407180c041c00c038541181e144400c141445a114080550764010424400b62401540240034980c2c0b90b41c03108200f038000301035040d0842950f410081d0340455400c0c5a680015101503120310f86a0344000840581e08040049469161748100e4180c17042c2c0c0107422100120342500250070864516202e00380c503408002c006107c800284c040545117507500394088140380030f903054580121001d94141078000c800c402480400c4016150161349014500d00400e01260100314609103800c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 722612014 1250 722610764 722610769
    0x90a11040e0c03161802070f11010516080a030608120307030b06300603060403020d260a060e091621140c0f01170612070e07020303060907090501050306 67
    0x15406000300c1c01c501480a405000b03660500400907250040e210301c82c102c600304100f50315030032103d01c0003078486841001201c0c000b85801071b00301e95903a0000400c401060510006070780e684141c8030680402500080784d44d04012008018201181e0156001c11110b030b142c1604550303900c150240da882c3d40a0920000c2c1d202361203034104001c403802c06002c141c10b000308101410001000d0300e038840840c0c2041c072803104d56004a0b0149950040c0200d000b40000d08180c3c5003c0c0d150540701581e1403c02c072260081d00341c000301036174040d14910200240c0e00b0140c50040e92500040046005003409100e01d500803400000c4001171000d0310940300b002d074044603407600406801c0342611284900d9108402c40f0f145010031900308100e0b1102c004000581490000c000c200a10201c9221039541071100407081030f1030400b44404110303413000c01950b50410700181c08410500d403500e10b03444030b00d8004031103041000b810390210207103000d02c100b44d40c00f0169072200c507403c1d64100e603a40110b82c000740c0140001203491 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 722613264 1250 722612014 722612021
    0x9120509031f020f040e1e04031b0c051507050610031203090c050a06110d030c0c230d0f08010515180103290306060f0d02090910090614090a1104 64
    0x2c1c41488010320b081c80b1032101d00d0745074029070b10503161400003400708080d04d04600c107040741c40c018074403500f400c81c900381d0b6001e001c0d809009284141ca6200f0001c0e1f83c10060205052406420018640140071041c01001c01e51075000140844041c0204004038614203500e001100590398000d6051000c3c14804900310018001024140e1303c100007242c0010302900c03800d1140740031b00340039628124070a003500e056524201d0642e03d01c4003010724100c0064411a406000d0904a0b40d006403040c008828010703400203110031042501445000c0d4201c1010706941204817018000c0c03003a21a402c2030b1f80d0300e0081280005102071101c0418401308008005c250301e040c2a04100403050600003241c410600e0b0181d000426240d11701c2c840c2d083c4025120b1140f03010044954849011641001c1c400200c1000c03445e52610f00030024003c0d20042d0100300b510b041803290440450946004000300300c1942498806400e83c0010343c0850445180412a03070813011070b414031541c0e04000004246081e1100703003c0207 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 722614514 1250 722613264 722613313
    0x3070803090313060e030105070f0f0c030c02061206100c11010804050f0d1206050f030c04110f03150a080a2a03080304050d090f060807080403090302030609010912050903 75
    0x30300040000741403000340d80411002912240e0341c0c190081017494185421900041d0018080c40401e031803000e513907a0711034070448103081c980c80c0840b036000c154941551060740c041002540400c0c0450740108000418042c1d0784a90f40484102d99034105c011070a450f481c4064601400390101c4046001845d4090304007103410920130411a0910104540035a04000080d8141000100150080c16004509000740c0d4058101241c15a408820801c00280e075034484180c01c5006584900600080080380c0741910340c4100c0c0c050312280d4a1604c005135042640700c1050701c44c410700c0640710214800000080d04c0300540d6201001101c0c0e03d4a00d80420711141d07000010169610a6500110000301720340080c60103203110368014400158030740800340110300b06802030090a61005000c02c4040c1c0d01400e0039401c52814101000540c0399806c00301c6030001541c00180d0144512414081c40884c15030048980368010100b030100131f08003d038219904e108203c2c54075450390081c1091140d29071a050758005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 722615764 1250 722614514 722614531
    0x15040b0d120806120a150501050a06021e011e02040504050a05060906190506120109050c070302102f19030e030d0b0315010303081005030a080307030b0112110714070803070803 77
    0x84c0805901c400601c1c008400000711605412131050004200c0315010719400341004036210720b07060b401c00740c0c003d5a54142205804109072007540801c60748000b0b50110030345080c50003e45000c184007080c4032000c1d6121b4410180682d14000009943c03e0442c403034503004e900003d0a61007261241d00400c1080c00e8069001c036400c84c0090800645540c4030001008000c0c44002084101d40c034000e0440c0484000528141c10603000300201c10000ba40411000c1c001c5200490005120b100c1c45e007445840302c40e0b02001403404401465030440c1558a0000c1c201044611480140b81d06513198220252100850710803440e50003400a600715240a4102e41d4240501804480c10881101c1c000810b034042030b8001d0300424040e1080c8041c2d080700d608e140b0043d0200b41c00401000f140c59540c11854400113041c1804c00d580c03402c4420442e031041240f48072120307400b001413108075060b4008000d260700040d0101c0741e8500d6003074201014000424420304131082a00514200601d80c0c40301700031a40010403c01 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 722617014 1250 722615764 722615779
    0xe16170a150504061206060e090d120b09010b0d0e0f0318030a30030908030103020d0f0f031805041416260f07020102130b0a0306090515040b0d120806 66
    0x190719100ca10444c402000c4246141c034421500c1e00780ba80c21111035400090140001d0001c20080b00d10004408442103a503180c03801104400e059400c0040003507081503a03220500300c000080c4043e10340007420011401003070810408402c000d8881d500d80d441c081c07000c003540044c00401400d400c89423041142c1c0314003400756907c03010107a54545070304500c591000c143c52020601124803007440c101c03a500b0600c590800700108281c075129008980414400207108900c00b050795020000d03021135074140164026121402ca02252601500484e20740903809401d02411100042034a054011182c135298100c0c01103105496004204075011010180d01003407142c03010170b1a1105200486010101000341500a090b0900c110883d84140c00508400116801440094690ba008540c3c0c04101c0301c2c424920307560703507411013404e0b00a8400c580c407100d0143c5ca01410441030800e01800c091101c1403c032002c00401c00700008108000240d56009082d1001e22480d8015803409004060b811100091034803 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 722618264 1250 722617014 722617019
    0x604110f070f1a010b0405090c070b0405070503011503150b0a170105010807060938040603050906060306040503031f09020d02071a0106020d031a0306010e16170a15 72
    0x80415500041c400c032a410100c0740c1d00070a00c22281d000501c0f080100311031038901e51412058100a0245002c1e40707200301118004079100c00c040c03008030780d4441d50081aaa250b845c1504065444c0c512601c03a0f54080e5080001c0750321610a0301c0b042a00340c0398000c446203400e111021840380100f00491819400415240e0b011a02c0c42d100104030544500d200008211581800c080e5801c2400583c4844140000100140640c5c001d903010700001260701003007180040d0b010b4900c40442e01d420301c01d150150400140114001307a0641003e0f10070035055040b1752050321807805160307450340101c0f8080e01540050010a07181945c08160800b9500c910008100058842042d10100d9001c0d03100c194469071700140d4001002940d00c480007008104441d4208150700d00480a900d56549a03030b00e80c00c04d55602130f00608101041c0a01f20303040d002908403401c960315400c50000115007560820b072298500c2e412001080d1058118a03000329107041d0a05190300c501036014080e0245629400e106803040313802 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 722619514 1250 722618264 722618287
    0x61902090f1906021002030c04060507020a090608010b0a0803070507030f050307050105160e0414070c020a080a120809030313080307050c011401050f030601030f11130c0507060c0c0209060411 84
    0xb1100542600300992821915001000e8034003078070340b02010b40a500501c100035030010182c0c00c0e502190342d01e08110344e5901c000d100103441c2c03950325000014110726003000481d11560551000825048c2aa01107080075218003005590340210a001040707944030f5401800040c4122025044840c40303031088a0a05005075680c03401d43d0004c803921030480111602100300340b6807080d62092240d0090354104001482d141881c1440000104481c00b486000210601152241c0404e84020b007095000d480c0241614a03200c0301009017560900c002424100c00304808100100440b4001c00e0110119007104480b0b035104411030300000c000f2000d12105014907441004207024141003902c410507480219030410040203902924130222034003a42c001030040c40001c402d101c80300c0e1540e810144204614808800113406400203404400f44241440521032855070000d000c4c1c580c03140703d14800c1c0141044010100c1c0e0b00710283c00065400507c1002244c51400d0030760000039249450118a86400002d010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 722620764 1250 722619514 722619529
    0x1b12040b1501080f0c030709030f050706080c04120201030b060706180b0c0a02070e040606120507050a050d0b060d1e032106180e0c090a050402030f061902090f 70
    0x18280c034444032030001c105100403076a24400c8800707000d00781100c0c582008804841c00c0383e002003520070300d66800004212000d0050102100840e40b041d42041d21450034540f840d1980c280d40f160360085400340000c9602c4002103401d0b20162030000c181c1100ca01001c0d00110003501d1600c02c41c940010041144c000420303403030701820f0002c04a200340d013049140303189001c181001f001000904601c2d0240091034080381c1c08640e003000c42e601001e003c1c04940317403820510000d0580d54428860700d080c0340e480c102086404200003084030340c111078032560103a403281401041001c0c07440003091103104000003140f0346001d0742d2080445000315030098001141c074031200110520a0015008540818a618005d00c054400303a01c1140a452060150a00c0c2c0848002d10800754072036581d1300b60301d07280c601c990408100309044d82040d000304152501c2c100032001000800003600c050b40a0300a0100010340804001841401001c0701c1e82d20400030941d9140d458020341040700ca0590240d010721f03065001d50758008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 722622014 1250 722620764 722620771
    0x80702090a09020a05030c0d030809030f12070912030e130b1309060f0e0d050a02030d0c08091902101b02100f120e030409111e0406140708031b12 64
    0x710005030001441c010000c0455050780b205202e540410680e0b00c07280c907a00c0150030200d5150820417101c0d2150302030305096001e41381c800f0350014808580d4410000d01c40303030042d000e2074058848000d481c1d120002450f134603915040250114001d405e01c90500d0030800d00c000c1c8807441e6400c0008414054a002a000c5c100603215140100e441e440e01505100c3d4078800c40841c4c4604501c10802d5801e581c3c0e115448914061650040c4940442c003031132554024004c0740c1c240030f40000c042148402156014003022030944d00780200e849103c0d0405090b05c80b000c5058056030b0000c09509800705160000c4514225060380002c0c401c44c11204040103894070544540c0998081c0c440c5040e2a0b02e0980041c4940300040e402c000c51410854a035032216000b0017260103503401c2c2c00020808420542080507248a0780c40310515a03240c074420306070b0100b1024040e10a5039050760360b00c222320003041e0400c14035009903031014010340c80400c00b241d43c0d03c7c0507104600c40c0c180c0b1000c0407810702181134000b41c448201103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 722623264 1250 722622014 722622031
    0x14130c060e1f0c0c18060905040507051c0804121119050907050909091b0315010b0703110f06040b011e0b160f030903150509030a0c020325091a13020708070209 70
    0x3c034540d11703140d09103000c0c103406000c00142c2003207285801c1e00d4041c0c1d00c824501c41c060003000302180b0f010408482d030a2103100c0c3d5411400d40b5649036503840b06950b0300100c100c8181d541240d5109050814a0014006036142802e281c00310005d904040411501c210081c0000092050030440200706440e851001c1d4800d2290801401107040c450500c11200000740300000e1282d00700c041c85035031b1400ca240c800c50668a082e0002d42e1526100c1c50162156000400341031000c1c800c4c0c0e0350025900400262743d51041d4401c0e105200c40707907a20456001e000c1c514200850400d40c070345c0c070306021030810b10010304544c40156400b0010041e16803104a40b0851a200c00d60015021000500c01d00400341c50640f01201d04410400591034440e440039180d005184081c001c2040c8000e40c40c0943d03504001051a802d01c0307240c1c0030f6030701031603507610501c021031442081c82c03860402141d1400403221448401d250100540200c01a58450710000300a5212200898280c0014410140540c031600622803080c5900c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 722624514 1250 722623264 722623289
    0xc1e02030d0f060b030a1e02030421020102160b1b0c0706030e030306100c05010f180c0e06010c0b040312090305040302011205010b160614130c060e1f0c0c 68
    0x240041034490040a24220b00e051000420056041c41e080380d41c40000c03042c1c00209030200c02c0349601140240100340381428000b2051005001c883c20782c200c02041c00c1103c2680501441500343e090303001d15181c82003001348184500d00803c96805c1d05a9200420070300700c0c0c0c0e6146144642050640000001002c00c1d8864902070240c1601403240c0000010340c1c8000314114030307200700014024440d00050400700f0584009040400c10250001440800d10200920113589520380d8010a03480c10101a01ca200c4140e0f000a803240c40c40f42ca0034060344040c1d54a84d41c00c441910b0f100c1d14190094404c6082121940b603e5043c00e40324801d410009110b41d07520780e580c80c6580001004000c1070a00010081d11f00001008004800c0089074018500b9030720380a400750b220704010000b0302000e41c01d5204958031504024007600502202032642d4454160003244e66282e00c030449200d04110030094211350b0741000e252070307840920000440b061030752820159040803940d402c3c11041d040d5200074540d00e034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 722625764 1250 722624514 722624527
    0xe0609100909141b120105310b010806070320031b070b0403050301180b0d0201030c020f241006021f0b06072102030705250506041e06050a050d0c1e0203 67
    0x70171034002e03600005080001d100301d041100c0040b00108140c1a140121020800d400b90440560004014400e4020142c0310503580e4400880351210700440325200064036003518000d00c480b8401c54100304024000303100d8103596543c054004016204405280c41e200207014180000c0c0342000103600c40c500c0f84c0d03501526549800c400040190ba00107440c040c0303500301170b051311158641404415180d0340910700492421314400e000da060410650040c5103a01440000f0f1511007483d5103142c43c01da248000c001c1d860795410b6407520082489018100060308244607075500c2180d03218000c052000c070040700281442c20000018142d9020003812982c030400100151414840441e03243e442c1d080c24000341d4070701030090b65555160702d20b540700181081c15907010785003a52404c03040000070707080c00303003c1942d0340e5118640c502d07160031450b290241200010901182c0140700d0001e0b600c022405445c0c09050001d548040009002d4000d402d104001c024517000c0500701d107082083d10401d2098014599401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 722627014 1250 722625764 722625769
    0x10605011409091f08070608060307051c1103100903080f0907050609060304080c010203010f080c0109230d021f1d01091a091503010e0609100909141b 66
    0x780281c0d407030145810034440402561903c83c0c0300d43d8080954251605920400501c2035000c08494115002c144034120000c83c010350841d514900030b40d4110102c440e00d564840c1008004c0c46102801000c0d4000340300c4000c0080c41290101c4801240101950900d04028420ba000c40e000040f05500082c8400c0500030827000902d41e05400c06c1000700035001c42c60030040425501c1c41511030700c5026050010000701800314103405d4407408103080000b9980c03942d444050544c0b244003030003054080d026901400740b03a98040d035090400c035040c24112403100300c2945d085040340f0040d414a290080280502c0c2d40059603601c50303400203c0601911000d5204a910009200ca904141c121901141941e84000c42e81c0c3c200c410700080750000b80d140c034200c1004030701013400342c02240942d1b500580d80c0030300b1180345c072a4040614141d0b003906607906003690f200f0781088034101007070310362060a10130020700384a90b0865800003680f05001705c00358640d83c12135201f050b04e48031010100c07004840403140c5003542e51 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 722628264 1250 722627014 722627027
    0x120810120b0f1501050f0702121c120c020706050a0c06060326030f0408130b0f0403060e011802010513050a08032a0d0f11010207110102010c032915070501060501 71
    0xd80f0780c04103040310303042e0701c0020f00244078840c0003d1202d0710207c0c40c0c07001c650b15211740e0300080e12000180c41c8003801d1151303810391203e80700b48104003003004000d080c1c24201041c8074140400720103138001d0140900d841000e84940d80025030302001c1044000054000c1141c5000d000002c0d80300d030030f0f0261554961206100006685840d0001c11b090404c203000070184040301103500b05411200050340d84a0041d07001580c0440c6900c004c044c0b0101050b4500d03002442000741c0f0880f4016a028010114180f00c424202c4070001103100106094000581c0994030950250003050340f2030303ca0308480d03034985000401400156000f2109540000f6114003850742030600c00d1f00861003400420f00c4ca00c0c0100070f90b515032840031326040400540b01c0b01886d4a0b84151061024000174034000c44d42e034045030410310800c0c080000c4c4240998241122011041c0c801c0c8500c10f10b881c18401002d10601d40b10448046801d0b9000810354866044110b0303c07810704403000101680d07071150000042040ca04800507008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 722629514 1250 722628264 722628271
    0x7141b0f0d08150f0904060e060a0e0d080a060b16060c020114010e22030c03020f0f150606040911041802031303050702150a0e01080c0403120810120b0f 67
    0x403900816502103406401000c455002504149a194003e100d480424108558a42d8050f40700e80710b00e05100a00407a5800000030340800c00c1a283d441e62152804810307198041d10500d4554015180c1104040c460030b8510b81000ba05080425907540d1200c0c1d00882d500200950080359904842520030810039105038100490940000d0200030b015142060004c0780500c0f520860b0916640028883d422217111410241c0c10380343d00e21440d91107401c00800e010b04c100811805481040d01058009034006504d40307400c034090000f01450a42c01404591408000d012550082003e0102152400c0140110483e056400340c0c8203898030719042d071464480c441200e000540714410028804560b18256091100e281c240c00c21540c0c803030461012a40c00d01c0040164425900040b40e03640b195903121a10301e9040c8026a0781d0391280c0c03110713020184184640d200c0101001244c92a1081003406a00b1031a070000b030107910600800e9585038004810b009100c021555a4410720400c0104920310101a41 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 722630764 1250 722629514 722629543
    0x80a3809090114131b12140105010b0a030e0c120f072103030b0105130b0a090618050d08131d01060c0b0103030e0f03010204090209040e0607080f07141b 67
    0x1003600f400300c01c48102c5405060000340042492810b0144081c810381c01011800da00103411031030355548400030b141e183c1c06000b203030700c14407001548400c4001401964140c81c00d46181619201000070240c005003480714201030940100140404c0550305d06a103844410f036058050140d031420380c1100e42c1061616000301040c855100424141c0a5219078442d1840e42e01d401c3c002071a0fa481001680c142c0182e08001440c400111008641060440050082c0c9a110b46403454803d4560350b00391101060550300c031142c141050300400883c07500c1c4142c41a018000d40c01d4516007654000000c3c6c021104c0d80104402043c228049012240b2184144d4014640b9145c608820315155440111002061101404201200c20000010703900d00081440d0144005c1c000c6594540d81c070703001000303500701c80041440740d454a90802e03544d00c00882e180380300c0c0c45243d8404400ea543c100e49800c014101500700020088529070324003c10211800500913104002c0304000c5800c0c06800c140d1920890a88020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 722632014 1250 722630764 722630771
    0x60f0902130f030c0303080411030105130201080c0f1204020f0306070801030c1a220504060806090106092d090606081c0f090611010908041d01050d03080a38090901 72
    0xc903042203056019691b052030300300c00c1a1124180003c031400864800d917819440c14051003c8540c8005424000ca0310030389074030304c140d0340301c12100c04140101d41c9071400c0c10408200c007494140d40c01094035413061008028058274402400841c1c600f102c01c99200c00424000401441881110703d5103c001b01020011100568449030120901d03001b146020210b89500381d014903014282c1018860240002800c2001410b50710100f82c0d54455042d100b02286504e02100841c0f0b03d03c05000e03003148648030038080c00c81485100c20160b50b0040072198165910b6460640500090107405070000030024040140107144004196a0008441e18481000d203c1d1407101d8030560b41e0808000320803104d241c204610007140185e03c2038050f01d800c1d0070003011080d00180c046909841080c459002c21060442c030302e882e80c2c0319401d00c0212551002c1c081c3c081071580c8001a601c2e1503e07009a80c620b200b00003090707514000103031484078980034640c0f070007804003441c4d40c01e50103410301c80b0885601201c02002070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 722633264 1250 722632014 722632019
    0x1050619050a0c020316060e0d0c060f0e092706090c0f0d0602070c081e0c04020a0309060f06051309020a0501050a090b0c16060804020901090f060f0902130f 69
    0xe03101420000da48109001011400340c01607800340e21800c001d80d4024081da01e9078072076040501004181d034003e80008c251040000c00711810101041038903541e10401c4d007001c8500f0044142c41820280c54034000300040f22101d0a00d83e260030a846003e006038911000c04c445a00c1d104540860b2000426000ba51008042000d00c8000151228815605550140d1004c1108003c40c604402da03100c0036084c07d000041403810410511002c0c01280c0b8070310305449071140000d020100c0b042e031207107d0841950203031003060290b180a034020100c0e42d25908000a140d905965628241c440110864019550b40c41003004035080680d82c02c620290314480030040060250300003922658035014040c1002400308003044014000c3c40d14001422007071107041d48a000d1400c5990f0307a40b550a840c900002d10007080010402e02961145000780e81c0103081c60000e07030034009004010301a810110100684403240003a56007040304001014000491025aa40880724100c19010b1384560010315500034410f800c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 722634514 1250 722633264 722633287
    0x2180609010c060b0d0602210105010c0f1e0f0507060f03020405030316050111031006200c0114041a070605012103180f0b031e1b16050a0f0b010506 65
    0xb1440700e1a8094400901c80d0a1140460020054400011710702880001c50f5070503510031507003420000039080b00301030840c6e0b203031001150b60703018402008104031100c01c0c00074009240e4441d10510100650580c130030250309910703003054000e03001c1c1c0c090342d10750004207040c4515540841d4040d8ac0340354508003075141610301000719540c0c4c85a040f86807068601101c02c01d040010030340100c81030305c414021894a038140b0503001d0100501920130000841c3c00100648403030706c01141520809207142016000115809005440d201d050320032403601144108030120b0803420390986510f03200c0c000c1840c580c49440c18a018803c649042e081444c10500103141100b8203005c400741f080495506180c91220b885135203d540070162800d400600f44420044000309a4490b1030002c0c52003070100704121550614180b0b890801d07844162a12103004040303a01c5040700b404213800500702c80c401c00d050255240d000c1d440d02810114000f808030748141e80801040e05010500d005075024003000c40700780b868070821130003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 722635764 1250 722634514 722634527
    0x6121b03070f0e03160f0905090a031b030e03030406110124031b05090106050a02010f0905071a1209030c0706020102040503061513060b0d0c02010b2808030c010218060901 75
    0x141002c10140f0080c0c410036482c180100090026001e00c1c900920351185403503100190540107402c0f031305140100040c03809034005441a0841c1d01034a6603003804200b47d02406882200c1201a030034009882a4810141c5003000240000c000701d03a5585400c001058046094036818403003804840c4844600d0001c0c080f00c480000101c03940414541040115420000380c10a080c2e449103074000896000007400a070030100601c00d10419900030010348034031404070300032142e01c0d0b103029186074841d4030180719408504251105400b015045941008000d003000040300700c1c1101d0503141c41d000490034031074078507040191134050b18050000b507050500384008241d46910051070170f06001da030b02e0069001a124803161070030801090380d00344080b540b00c1c10b90b03d0091348215540944240385c0046c0d0040148103101e0301c060868018240c0f036002c5a8140d00c0b0300c48620409060103052907042c80003405071402c10050400301c1c41a4000340e150307500703500c0c020404e82000c0d0009004030020842d40c2101da90044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 722637014 1250 722635764 722635787
    0x1c1112031009020a120e03030f011239030c0f0503070608150a080d080417070206070f020621040605070f02060a2a0e0a1202010206070302090f06121b0307 68
    0x10b005841d8a8130050448a250307a0082408074940f13000401c0c41c0090010001b507100303194440395012181d0741c13024100554251414082c0041403017031318214400304251482c600403c00b01c2c6648c1c0e00c29009005a4662034070035032046a02c141c06150400c49041217040220040c14201c01904980d4035103600605110002415040c0c1191144100f550959501c0c0d50303a409070054408640d07010301344101c0074061600a650540c0c0d5504012060b5844071808800c483c6003681c054169810459140e580600148001c20300302d9102c0300602c201004460b20b0194440020740050000c0310034103290401c80111034010b0b0a482c20420150144250326800003a0300c5d80000c082000003400d0542400640800f5030100c01032210180080720003056568804520611754900315200d4044c1a601c85405101100c40040203015801000004070414001c1c2d000d40070961024003203882044254000814540c00075000081c0c0c0342c04002405441c0002403404046100e61000700c0d031540c00c0000707024014042a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 722638264 1250 722637014 722637029
    0x1050301030609030c14010f060503070510200a3e06090102100608010e070801051612090812040b0f07020712030e0406031110080415020a021c11120310 67
    0x20714800d0f007014441c541d1040c002c0e81080d050311134072040c42142d42c060019407580208035820305030302145519011600c0c1080f01c030010544101d5440c1000300f40e0350810385042841715410030441c00300103e60240013901002d8890307500e284180a107022100c0b040048204a0300021071000110b6008200551080c10300c01001c40d90306484816050040386082d090503400b08246040a4001445040540020740c80e00074000c262003096844040303440c203c3e9401c13108422010184024514020302802e9018004152000040354504841d01c0e100c001c0e030700212410b20781000c4c2608100501002d0480207401000b0030218445909140000959070301e0a805403810190f40d00304044105401801c441420b0325001d4410701c0040d5603400c1900100a580380181c0c01048006500360a10f4442c1c0d040c02d2186174416070200501021061120003500014000c4e002e41c400d84850390184000c0444410102480f5600c801d450388451003a14240750484012a0801c0c20074000d0003105c1d00c2d4410303e4401d88220 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 722639514 1250 722638264 722638271
    0xb0f070602130303030e0c01110304090203040f060606080109140f0c0307020c1c030f050a021906020c010f0509070b120a050406060f0b22030807031409060f0702040e0606010503010306 81
    0x450904000a00c41c00401e01145121210000100340c0c142e0058150307260500247c0310319100c944015100c2c040302e802030607010b810411090000000c181d015640090240c1e955558566a070741d5000d04866032604440301041029004000e10782241c0203200c6940c10b00c00361556503043c0b031010010190005410064901000720004d840d2a101700700002254078002c00d0124031030104084c0d00e407904508041a40042e9520440710785180c081e1084580008855000f050b03100e003100382d551030300b010711401140e503240c08204809009100b401041d03454000e4403000942c85c20048100303842c0c20800e43c018600808280846100140800d00300d50748000d40102c007207402d07517071490700c01c006050940002203000c1c9040300120320341030b01002030a2400d0360303080c0700c50b40032100c0504c503840745246210040003480108550400a88201b12070358a01410488050030441c00344000b40d800c1c0c0050841c410b040401044443c250310305801002c190780c00c0071002d403015043c0000002c0c00c51205001c0900140e45 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 722640764 1250 722639514 722639527
    0x8010f1203020c22020a0305041a06090414010f0c0f09050405010f0306090606081504060c1d100e120c0405061801050910031b0302030c030f0607110307060e06100905010b0f 76
    0xc0390200a00130900c90411503807100707410000740080100340e506464404841e13406055040b1010000c60040304002d011000b15502c3d6615841800b001d008480e800b5500d07140f00c034040d4030310750140c2d804101d40e5031200030400d0160741d00101460444e600041c407550a180040003007440d00042c00d010703245c000d640400c030800e4a04001000d08400d9201090a205810040903005521620603000d184030f128240005522600111100c0600389421030300c940342c8407060200c1c0d1420b0072a014030103107207081c080e5000080380d001a040200c800b058000a81040556810928091042980c0400c08840003980c480d400700f0860b4041505019440c00340c0c801c200032840290030b03000e10b1802554400404403841680c0300300c0f02c0685004e40b0049000744607565004041d4500464181818040ca0000704000d9580003000c6070101040ca403040c080380010000d0708045002e50161042c2d640d91704004111a0034a40141040b0041c03640c030030417a49207021700602194402900315400300d901600f10645484 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 722642014 1250 722640764 722640799
    0x605031603020405120c090c040506042715081e0a060b0d0f0602041a27010c050303130c0f060903060b0402090916031b12050c160308010f1203020c 65
    0x40f640d089154480c40010750310181200008140c140d001c1c041d5101c401c1034035a410500024012801280c4d4000024002404420086009001c80a502c400410780c80c1c0300c02c1c61f00301e088400c0640c280c0c100740c42c0100140080d1004004104005821a0400d1400400d080410740c4400841000a044c6510381c01062019510003100c0c80c9020741007040b450301c1480c20b240c1940294010700c150001a515032412107039030007a010507100c0d2047c0401081002900c4918018026080d004c882410b2000d0313040050089202000603612810f913410144c40700b44001d0a00010300e210035440b0074002c08402400b80401b540c000c0d0b4800440b5800800030880717207681c0b400100a40558509150400c00d080c0800c4815007903460900c043c2011a1010000d080b42901c018030100304095a02d004104258100d1450451507808180e1141190400d1800c05030385840c00e42c03140080010030740008031780d00011b20110548141140082804452081d01d19121741c1c1e0194581140001c442d100c0c179020303000c5a0484 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 722643264 1250 722642014 722642017
    0x6150901030b06060f03090307050706031406040f110c0309030c0a03031707030f0f0c080a1811030c090405032709040b0a060503010e030a03060b030606030f0a0e150f0907060503160302 81
    0x200b80c140005e61a85044420179980e81c00c00c80d4140d650b4400c8078400200e0368000c0c42140d490004004442d9007039070301d940c02d000280595480400d0310507622044025034950003400307045850315040140d603450b01c551041501c1d04048442961251052180810019420000f00c4100b0806000b80245030b44d0b07495401c0d4000c15003001102207442c1002d018000e104032690103e55452030507100e090380c648403206144200c48421811f201400007000018021840b40140a840030000504075440d521040c00462540c210070342e412650743c3e10100300710600059080306030413048040c00c0340120301980c5d84001160402d01400180c000c0c484440840c200d0348483d00400c000c0c00001e030003404461200756030156aa80100407910009240c100c0100310103001100710703801032600900c0d071411902e5040860211303043c082d1020030825615080d8883c0c4600c20711a9000c4d40070800e120a205203080d50010580101c01405c9002640100b202800407680000c2980d800200344400c004046044002c250002d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 722644514 1250 722643264 722643277
    0x141003031b02090c04060f140a14130e1605030702060414010b030a0302030c070b0405181f0e040b06010201020c2505031501050411070b0a020f040915060206150901030b0606 76
    0x441c400f0820080c81008001002160a659101608040c0441003240c80d250342d540c0c0780407808400c01071031844a10601000c544c2c4154186c8051900e08440c2c3c0b68050211b103944048200d0307128404000d50030038000e078501b40f016103d040480c503600d84844000c2d21003000420003015100e1118038510700510950142e1200071001d81141cbc030003151803c001e07540360881501d0a07250f1144000c080764000510301a1002c0714000f8003031880700c0308c160820b010b9003031004082000c2000c200315020060344039403c151005122401c3c1c10416402d160500c1490300c03200506881c1968010080d4242c40c06002408034034203003c9401807400c000420101410405884d40181d40c103204028101c41034400300f641c20b5040f110126010400702c0039507a10030485000c1c8120207030200a1020005041030700a800a00f26030712112003491801e13450701c00c400c00700d400d011540101d890103102d06110741c0d13404021054201000850508804030030780002141072030140402480340a11001103052503d03642c0584a9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 722645764 1250 722644514 722644519
    0x303060607080408010212090607090602060c030406021204080d05071403241012060501020f0d0e030705060a03090303050f1b070f0804080f060717130302121c141003031b02 76
    0x555042c072140c0b00510780000d40b9185523601558020131601801406000b0458142d40c010f0003d0395603540752510030ba00f00420a640c01c41c0c003046480181294060143e118034805c5003031036216a200e07000f8a040300c45c01480c0106001d1400c10454a484009c0c0549500c80e462003002d102c604022002000e180d928400b00940210310074022000d00c90b00420041a002107030601003050940e200e0049a0307a00900358440c61503008a0904000395220f0410095074100c050308840c4e20030743e00c4020422542c0030744148c10009640b042d113403080503414011a034224203103d0000129080510690200c44407000710340280c0310700000c25000300a02c6680c100607807074105030490380f00d6590700ea2443d21008070f10303180d004a002c0c2500184a99010320b510b9090030240300300f40c1403296140c03401123a46618984098041d84540102190804080402400041c0d10b06994542c086105c2526600742d07003421074000c05010605007080103601c0081507600c00c603038051411100002d40d103000c0080044000602a4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 722647014 1250 722645764 722645767
    0xb0f090f0a170f0a020603270616120b100309030215010902030105030d030c0c02040506060c010c180f0302030615010c0b090a0210110636060405010605030a0503030606070804080102 80
    0x1d44001c90b416001c55082025069075189020400b409031901c070900740081d405003080c0041000000307429440ca003600d80f4400c4921070240707a030303408a203000c008541100711000000d0044001c6580145d001c0d5907200c1b664818800098240b000405103070840340c40c401095a14207034001818805c000390b80b40480310140c041c00c03d585550114019500c00d001d014040d1003014260804184244508440e12100340d840000f0900d1940c01c10015103c05403005078001c60621010074644400e00c114601d03401c050729004c07586a048a2328002800c0c20754402a0b418481240400150302d012411580c0002d13055821600b40b00d00c8401030314400b0081c500600140308407400c000700c907000020140700381402101c00100041c0a203200f01e50804a110b0000d03c9030300090049500c041060504c041c201c3c2c0203450110241003410320030005416044844103150b48140140014801c082c41804007400081d03000d400e0345450758171160b50b00e21014040502505000404d4024400d5030380a42c1c002d090301c42c0095 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 722648264 1250 722647014 722647019
    0x110a03121401080d09051005160f02040f0c090b09011d031207141b1f050f070c0311030105010e011208132c160c231c020303010b0f090f0a 61
    0x80e9180d041d8a84c8001084604034081a10700e031142c80800402d20b180c2d90b41e0314226400c11080018a0800c8003201d20301402044080180d4443c01142c1c40c29145203000030b1003a0040340f0040c44c0c00002da11000b025801081003c5450f60700c10b1250640c010741c02c0200b984101e040700481d1504401241040c3c0790030000c1110820010301901d207643c008601c400f110015082252082c00e00c0c94202201030344525100c205405140c135841f600d030400420b50802c2814410301d02c0043e001072307208050456125802d10424400c004143d07500000da001c055000300070035810400075007070150040c003640300001c0010549008000c3e078501280c111402e101c4030134107140e0741d86444a81c056410382d5041c3c413208564041d4182001c140c030926100f075071062240c04e2840a00d8038161a0740c60114000d540420803c1509100185450701c01411003ea6400034101008105509001894100c90341d10454204200401c806e0000409541482c2c92203c0500e5440360340d400002c8501e848100007035045200940300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 722649514 1250 722648264 722648279
    0x109140d0c0b040b21070f0c0c03061d070909260904091a060d02060901051c0c0f200c0f1807050c10050f0403200109150606110a03121401 61
    0xa02542d80c501c0c17200499000b4803401e00c0e06070007011144800002c24052081c13400601c60300c41125a54015001c1508681d129100c100c15945404030400181e010380c101c08000d203d040048200405000000300a074407456552a44003404590510040360403c842000b02850080d04031100150b00801c01c0154011900c1c2c50030f01400704920300404884040001105030500208003651103a0040c66180340128000c010341d0990000052744c110314405124404060340c541c82000c00c0701d03049131a05400107440d100001c00d00d4102d0341c0200f80017111010440c0c0d80d500c000a504005a400f1103160b9600324407200881c03000088564000403000e856814000000c1c3c00c580140300078100345c8240c8040300d82098800c010703958107480102d081c2a1520010f4082449402d0103862544100044202844a0b1700601c0c00d60700c0c030020607607510840d102002a1764010303108003001040c4501306121002d60390b4085980b41d802005014047c0124035100d1250300240e40c0c0400e501221f01400f01e0708a5854081 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 722650764 1250 722649514 722649517
    0x60a0e04050c09060306160305090a02060d060509060a080a02040f090b0a090309090e0304090f0b03060106030f060f0501120905071205060603060901050930040b070b01050109140d0c0b040b 83
    0x2d605000e101070fa03012465078140492042d00c00c0e20340881c0a49400c40000c5e040f0014180104140e0880c0160010200145c5d01c2d480104a00461f003031000c255581042d04100c203400c0c0c0604490300c10b400c00141045000f90210b0751064213601104c0000d4440701c3e688200c8058502c080006242d02e0041d0f04204030a28140d002e002040e0003595410740365601c60014408403081018480204d41c42030100b00701d00103941e005881d581210513008183c010407440828600722080c0c104030b002c60703100ca1020701881c0302e610401e801400340f400102c0ca014504400601142c00c02c1d01000704694039010303014107106040000300b0042028180700c28207100ea40c00c00c261102815a5264841d01510b4040340e00d298050003070781c0c02024000b020308029041440030820005410000300d140c001d207500f44a110441040107000140030b0024550755420052034045003002050304020705101800b40c050060300513140c04802102001e13a80c50042210504002c1420301459000080b01800064089808400e5a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 722652014 1250 722650764 722650783
    0x90302121b12150c040815090d0c080d02070f05060c07110d0c0b0d110406080402010e0d030807050f0c01060605071506030b04020409080c071526060603060a0e0405 72
    0x10388454603003901000300b03441142d40002d0075544049900001c2c003c4103400b49420042e000e802070314282e81ca912403418030010142c050204070040e4108040d05009102da00f0b00f1407101e1a000d002c2800c1c0760781d11701c13141c0640302080900c59030114000c01040042d123400d42496412000715081c83c5054811940541e0110070210340502c4400700d0825681041d0b02d10a0307103194816034a01ca42410826011455006001807103691034403403184084000140d002440600b600e03550f203e0407450640005441c200c04105010700a6030401140404079504c40100341d00f08601d864038560f100901680c0c04680d004001d01500554600140010280d410130014074502d44100e159080c884594086a400c50305079100240011800c90b00082c0185443c0d0300141c0c18500c9905454100f10741200390528190760f0f904916800d029040d01100e080e9080040000b03810102e459045c90200240c44810100314080d04490140b6004404903166a5900040d8409011180c50100303032440c150502c3c913960301d50303107 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 722653264 1250 722652014 722652043
    0x708010f111314190305010929010501030c0306051504140319030305060d05010e0c011101020c030d020a02120a120c080402092a28080405070b070309030212 69
    0x1554055550a0300642d0403840740c1c010550740346032510303c4601104003aa481e0a0b4030210f924040c2100c1181004d1080107107001e03200000c0c218844d4644600307038480d215180c044c02e4101ca250480c503403206410310741c1074850a00c0c001c00da135008120160701070400703600416071180100f00d0060300c5002240181c0b0845040700d0f110548802e0280c10301d5120900e090070120340070703040240c0c440802d009811a0390400c0d005803082000d600242c0741ca03803c650621b103115510fa003103404424895079020421220002e2404002c515203400c916869561344070300c1c04610003082d0080351031440035000780b0a41091855050446a50f0400c03c28000d101803050700c030704500d05180845514a451080002c28400c42d805080c100841d19091401d6062044601d80c10000e10142d80d008000d501c2c440000d03009104414420900713246110022021002d600c4070b02904100c040c0080001040c000508401241c401c1050540d95001d942000c4440369215040a5042041c6046048034a0000074022407480c658 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 722654514 1250 722653264 722653271
    0x4151a0307140a120b04030e0a09060b07031d0307120203120a05071e0b0f0a1104080a03080603060f13030504090c0c11010306061409210606010f050313140a050708010f 74
    0x841d000041c00c654404c20142c00c1c004040700041c000780c0500320742042c90500030041c2140d81d68a0307101c1015203003160425194000085005400c0540098002d00100340d078070050681070f00643c1c080390f544c9602d0b1045901043ca5132106009648052188414006109030030030f560f080c440c44098459480348900b2121080d0070030000302c24505c50b82c0c0300c00d002503102d00d030140e242c1c5400070b03484103203400984140c8400b0341e940b541c0031519a0600c0140010540070020340a0030440d420f001e44034030b200421550080d0015800c00c030407001942c1ea081d5000c4040031400e02e1340202d9040898443c0034540050350681c0c60005100c07145608032000c070b40e06900c51552140d196203102d00440c15900c941c81602c0210b200c18004181d24200ea801500c5681400703070a4130f601c15801254140080600c0d0449020b07500a481800758135688000c4084840c48641801840d5040146490003d207090010182100001400d1000041814840070f10010b030030074101d511003622217624034001d01032840541c07529440c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 722655764 1250 722654514 722654519
    0x6020706030e100c020f0a03020d0905040e120a090e040308040c23040c1b06060f061b02010818240702071409070e0a03050115090504151a0307140a 65
    0x820b00032401804056030140c0312403010000340201030704041250500394002d21355400c2140804000704810280070b5402040f101820284c0541101aa50000f0b4000c43c2040030709601045e00041500021803541855945d807038443d2000c891081a80c7c010721410b030841000d120074964041485806a801843d99000c420707551365070a22160030800e1501440c10030004c0116003490142d01c107004060460800c515061107100500c14a0b250700e4a00720350030356403200180700000f0b808091002921030350038a000750800c0400c603000d0610403030000070304024126002444e110301002c02812842d070844101c944c80165040078400c84070311a0030703e00b1401c0b03441000a94541c40025504d0803030340100c1108a42c40008000c0c406903040040a02c01404046942440c9d00d807240b00103000198010310002405500b4002031400040e440d0b44020012400d20b024440820161036041c080745886240001e41c0c0e022328400e0040454050401d117615002d1524006505e56041500010039601210303020070321034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 722657014 1250 722655764 722655767
    0xf0302210405030d0819060902071709011403040f0c090b0f041104060c05120c1014010311061c020c0706030605060c030f0d0207080f04090c030504200607020306040c06020706 77
    0x100d201d001e40c0750b4822080c102d80c05005411030b90300881b131880b0007032100c400b0811100a07140641c0c059020250b00040c840140300340080c641b20a103a00d10301d03071443c210741d0200081c01c01001c029401c0304108000041010040244070701c1d035280358030460322000c050381c0d4402030b4010710840d00c0550140ca03041c5128885460603100e07048005522000301c6007800d041140450321680c4803242100d00744600b4000d0b4007078100c0e41c5d020300524000c540080140001482070079040d11000c2c540b024240074000300500c000344260840c0e00c40350138141c40c0551101c004010748442002c00381d0061102c14800124280d035124085004410340310140c5050204d40d58031000d00c07a0a00c2004482d030b2082d042448107621440003d4001c040171814510090704001858903925480c0d071114052014000700046c08105850b138601940d107502d406070804109500d459140d01116548032807061400c2080715410f1900c0e59186c0b003e4881c0140c01504071000f9141a03d004e0a00c00c02c240522005403007406000030307a95 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 722658264 1250 722657014 722657017
    0x714090d030e040b101b060933050f01030807050c090415200a081b0d1a03010c020a0b100906090b0a0510020c010f0903020612150609011e0302070f030221 68
    0x1907039155a10005900300d88031b1459089414542254165103400c842d0380070403420b6030080107030b9943d402e40900d08007000000380c4010100301d031542c81ca68100802c001da060079140350141101d40184400e543e030709142ca4100d0420451010349607000c100368040c0814800c6504000d0040340070081c040003c02d800e142d0a260455000c02654500c850420500200a104404247d08035480000492240c4004220120385410907041000310581e030b203802481400910314009550700c0264000c000c080c3c0ca10000a455208844015100005000c08610083c9252085e40300400d1200c0040000d141c440302d8000203040720b10f0752948a07911a0350041410300d0080080c02d03c00006030014000040c85000648008171180b480c0420310990050007c05621458002c0c800c14001a50888140ca8200201c1c40c011090b07040160065000340695045a42c202c4540f4001c25081646903105c05c20a150403000791140500040c03100c60813001c50020141c0019800078400c5905500c290032007040c81d11100103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 722659514 1250 722658264 722658289
    0x50604030b15030c030a03020c030106140303070303051503010f020702040e0102040f0e0705070807050604050132090715050c1513032f0d0e09010e0714090d030e040b 73
    0x1c1184880824200c00d5440c40800c002c44028041c1d0312004100b000007410f0095294055015812200041078149800c1c89500060929800d0401c00804548042944d84c09024002000c1c035035110b022803880100d180c1d03840c01c03d020050091001d0307207985050368080d401405049004500702545250307104410300030f4a081c0d40800e00a5807460b443c0c28001d10101c04080c10820911104100f1000440e0145004051150082c0014002801c2520f0081d084800b10b01020551040403850585001803142d400c258040403980180450707100c1c0ca507514106074250780000040f1140004005c400c5030044003a0500800e0724054519107040c3c07407030514800004a40d1914542c5178070040c8000a4050105010032404000340083c07084e054003060401e4482c641d14451080d408008a841c56135400110959000c0040d10b0a680320b500d803d21000800b41c002e0301e40b000b0311003c3d55034006010f4501c01a180075420040940e5000f4034ac5040180ca204c0101429030702031410800100b005040440007020b2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 722660764 1250 722659514 722659523
    0x30506010b1602150706020f03011d06030c060c15070c0c06050403020f090c070c08030d0e0c0f040504030212040b040509010501020d0210020d02040b030a1b09081c05070503030711010605060403 85
    0x222074030b0b6401c10004a0480d02c000c070000a06001c000c000c03442c1d500c0030702075034220143ca8503500e5041182c50350419171400e84c10703069006d602040008035180400d0b860700a0340f082d86e0361616510a00c80302400c1c14124413030b00c9d02184d030f02010410b84a0b13111140003440c40c001d41c444184203454030340c21212433285000184d040b030b02804040713005081481000f540b00382c03800c0b262400d0540941c0e81003812841d590080d48a507101188022006840d44500d0340307a100c0c4c0c0001440882c56800c0800c07880d182ca5039000c0d202c1c07585c41e0700103410b2500a1051800104034540711680c0c86807508000c400d142c1250080c140110f03400d400120701c550002072415007400c01030b00280070076250dc481250287d4098050070f01c84039000c0c0800150050706401070342c002ea60241c408a18140c0001e076100040382480c03a200104120740c0d604020480c0049281910b40410b07141c06840901d45000c03d0385d15100309200144244000010400100e034007000b1060200641402030058640da101042041c0c015400042c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 722661870 1106 722660764 722660797
    0x50102060a02040f0909020438011b17160c092331110306070207061403090123071205010308030f0712060b04030506010b 54
    0x1540441c20000460070185030400701050381c0b4540c0305a0f03c0203035840c000082951100e07003020302d100f0355500720400313020034401c141205800035501d07040c440d0040710f01d400710a62280c0c543c1911040402c9800f0416041134581c0c4070252060a49a11190350400002200d01c40600341c000c1e100340141c03140c0421030304d00307c0c18005440109411640b494503140c0c1d040e2007501691001a00000c034a0600c0d10348401104402c2000da0b4200c03103030220140f5440b4080100a5001d2074880d0560090302a294240c0b50610243d07943d85050280c0d1001c2130241f206d407103c00c0c00c440d018590003c80300b030001c00e00c643ca0714000c44044641d404401c07450500300c42004162600300b9008400c02040e020108469850b42e06d5205060001605100c8240200b601203a000743c89140d410b161503201290401c600c551305e074031545240d4001d110440300c034043c00000084c80400c20081d50044100e00c4140c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 722482014 722661870 := by
  have h0 := BRFrame.cov_init 722482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 722482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 722482014 ≤ n) (h2 : n < 722661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
