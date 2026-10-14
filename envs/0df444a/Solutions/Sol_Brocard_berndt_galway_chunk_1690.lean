-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1690
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:14:20.033291+00:00
-- url     : https://prove2.me/submissions/ba6a230e-d5b9-4faa-88b8-f50e633de197

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 303776978 ≤ n < 303956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 303778228 1250 303776978 303776981
    0x105042109030b01050d02152205100c060c18030506060a0905090c13200d0b10021002130506070515060307080c0103320106030c030c0c030c1103030c0709 68
    0x1100d00e040c24524030050a503158203640400520409200d50803058a200854468409030036440c009035100b03907158482c001c0300500942d99480ca020320700c00b4078078002070385140540e520001e00c0c0d03076a1a0341d420800c51740c4592003e0f0004419000500c2074442500100c02c1c0d256200b1402140504003500107410280c04010380828039600c80d100c014280403c0c4150740b1800700c0e07600f00080003207582c901e00055036120200501441c0400e8035201000d1001c25901d2286c0348010100c00000784401c00604a50004000c0f1103900300d5810001071780700b80c00d0031541440903801407002000c641a04041030b556030000807c1a402958201d803c1d800203412030240522200740a500a042240501891070803c000305550310129401541056280d403555035502a101c00d182480d0030b0868100c203e0000302003504010500f00388500f0000a140c201400c410364400d1082010002075070340c5d03204440506407000c03560440000c8080d40c00754005080303036500e660200010190001c809014152151a1042e05030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 303779478 1250 303778228 303778283
    0xc1d0d1b080607260f070201091709030c060a050313080403020a06050c010b01020606010e2404080c1005070314090103020c060f1f1d100f140f010513090209010e03010504 75
    0x40f000489042904103501050506500c03e1240d5640e071443d54458504901600b42c814018240403512b610a4500c00c0703030407004040c10f04c001e0b000c6661200000082c0b00032845151480741c009a402d01c00b2640b0181c0070a604040140a9a541c0f0300702500d940010f43c1e1064141d11000100c1c50010ba242030b1214203004400300038501b4006400d0526003900007030060500000810320a801446d00320690502c0c403841c40c4d40c240100e00d06603841e6511013140944d1940880752482c0f24a480450364040d4510403021145110f0f4941c0d41c0642c4900084c4402d816070700886511414990203002c6500c02c10003c100291281140d0300451007981000c4003014172221641115110110000c40c083c060a035950503141200302c3e55014102c05640c841d404c2c0607035241a40c10180c82c505809400040d0700c1c6020404030a800c000b00c6030b5411600100d00107503520321800554010042c03400800b0010000c0356406490f8624042c108800c030710007604006030071160111000c50700400380745000c00c004208405c904 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 303780728 1250 303779478 303779507
    0x11151f180504060b060c0706080a0f0e0f01050f1303051b010f1d07050303030c0d0b100f080c031302090604020d0603150b030127030203040b0316030c1d0d1b080607 72
    0x740303846e41c5040d007a030b05c5421a005400c180b00c150404141d50790400c0d070080600d201111030810050403640041d0392201050400c1d0001e543c20200401e009000d03800311240200614680300364100c0d40395030b050340c00350018441c1c0146800d60940640c1001d40a0152444155001d40c0c0041e43c3c0c09207100310b00c20f000d5001d542150551080e10140060340f0000100c0f6046032650200b1515040240e180320050881c0541d100c4e0440a5203135800c02554010440f035420191130348070719400303660f920080861404200c45c2e0343d044059042007400981840165950081000340003d45170120811240069a100f0792080703c000360441740e542d0b00302140c1c0c4181c507400d600c110001d002815060384c0c00200da0300b007100c1d00c2640c0d1401500d035a00301402002218001c210a8202c00d0300c81c50700b00304111400441c000034a01090030440152205c40c03252849642c25010012102c1001d1842414040c40714a02802201d011008018940070404803001401c020095440181454642044010441e403500c0342c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 303781978 1250 303780728 303780739
    0xc140c0301110c03120405010219020f010e06060a15030f02031302030705040501050105190c02040507110f0a02060d0e030904060e190513020d030e041b11151f180504060b 75
    0x240c480c00308000c800c96554034041c5c8030640c8035440e44c1c18014028401d065603410000701e0003203606031503a00440d018411007050002080500039411385a521941c044808907030084054500b440803903844481c0e0380998241e854001140c00103006120100c4e8002d580d6000c07201d0300c806e5007404501d8100010f4024200645040c801d951400c40082d00070b010301200c04206012112001c502c480c883c06282582940040040c4a903003042d610180c2822050f11220304140100d0800030380d5490b0005628200e258040c1005217480100344c1c060303006002c01d41145aa50100300034424003692940210000f40498283c2075016003000307a6103280215901490803a09070401e010012842400f00d020b0b24416015140c02c1d134104a589011101040c40c2c080f0780358402d2502003481c059481944090209408607181d28100b65902ea00ba965940111201e0f8074420340d0480c005080c2c071801c002c043c1148880140030300c0038a80c66200341d040500540100900b00b076500c404200a0141030b0054000d404801e840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 303783228 1250 303781978 303781987
    0x503061504150e03030705010207030c0c050603060d12020a020d050601170604030509040c17191d030d1109090403180f140103051b0a030605100905010f0e010c140c030111 75
    0xb101014011041d0318109001c0030540341c11098400384221210b0941c420000c650710569880c0180121030042416201c000500001041c0b508210040324000c00d402001d4a495516683d602c541800c800c441c004118011a0b03080c2005884100000b0074862203071018000d1903060809503055417501d000d0f2441d544d0b0041040c030010030381010450b5034040003541c02141e840d080004c1a515002c3c8282c0d803180da079070250104602400c0c1e4458a0688940449050003c03615281f1821040740c1c41c2240956140c004103c000d0106d201e6512904800b440d44803507508000d14a40016040744080760281c01140080071070699284003610020090170f0a000707951089410a04c407500060280c0c010141811380c3c1d000414843c02841c440703052022600001d00b541e0306080c1c9030043c080e0226100e410301035030708042d100c031005004002c650250741c81a1345000e02c142c0004011a842d45c2900032039414880302c50282c40105440e401d4014010402c00005c1c940c2500c0c0c0030605003125000c40648000100c10302 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 303784478 1250 303783228 303783239
    0x120f050f07050106240f0905010905121c17010509040b1603150603091502030c0a080a090b0a0902180906190209030303130c230402071a070503061504 66
    0x1000e4441669649000e1a100e0740e0a10346903006203901c2c0c00600030718455003612429241c80d060450007130a4180d85507410032189031310507075200c1d140d80201400320b151940240164101035000b6100d4542d01c50444010041c21454059203d60080081000036200d40415405c0440025110b00400050310f050050345000d4070b40c400c040708060148490510019515004940700c0d4201d0b1034907101d40001c2c014456907030f00f0090010155907030b04480810a003030354180c4048081c8207403440b039082d41100f14900007001c601100c140e44001d06c8041c0041d540c00a01c004143d1503003000340708002810b0005040c41d880d004200586a42e60040d03050f100c0102c0800000c0c48000c0746590f0088400200310a02d1401e5072140300190003030200f5280c2501c404803c2107074134903809003642c1f00c0c07500590301d014010f5210081c00c20a80501010040400301d044501e9000d81003a5004203071150050001751045400d07200203c0c264403040d64040c00041000c0144403482c40d100f032070114610b02503008545003a2520 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 303785728 1250 303784478 303784487
    0x60f090d0c05010902100305221e08120903030a051303020d0e01090b191b08030c2104030207050319111011030f0301080714090f0a060f030609120f 65
    0x400a00c410414810680020403209402142603264020070500c1600d50104c0001c004003012500a41034080c075100041800d2006400c00c0703090b030b40090700807090800e107002064078041c0c1c2c40822175801c40700304905c800412200c2d000501900e20200074580c0c03401c040c0a510142c40d009041403c00e00b001c42190400290005010382901555080c43d20001100a00580c2e130700015a007e51303a24900012107900f611401c0409400c001c010392511480350011a242c14520600740c0002030071400d04001160a480c51080542000800040407194012044820040811040c1c50440144e0301c07485060000d03160505c04400d03003408000c100003042225454180c2120040100360b40120004491620203500c2412002e41d80d001080072a5692001c038000c407401c5a000f4401c2d40b8040c0140d000c08100c041d80c0100704c0040b0b1000400303030201602c400c80c503000d1546000d4041d480b020780d41c0c03100050507030606c0600c81c002d44c002c0d000001e51100307a09003d001d0942c503152031001c0101c1e400c40800d00c0d0b60017 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 303786978 1250 303785728 303785743
    0x15050306060d0c021f0506031c02070605030603030f0c0d270504090807021206150a0609050f0d12020109020906090705030f040627150e06060f0402040b04030b0603060f09 75
    0xb00b001040c0c4020400e0141e0600316001c111006400d125040c40d4820701c26500203d00816080e0121004000707180c4050000c02100d001c40d00068200300c000300401c51080000d5a04070300c00905480c038000e0401c1350a01c41c0c0d44540d1003583c1642001d04009045600802e03541e40030b04c044246000c48408170400c5071103030456806640d11895a407028241405210401d403440c865003e4485120045428902030b038800e412222000d100c40e010368020100e0501c41308400864807542c85005081b41030004025801c16260310091b00580f2030203120001c542c07504444d0480300c42c681c00001e00420180140100448000c0080e40070b0380c90441400b1310b19074804101c9521504002d0707400c515032141e15284002d05002c40741c0584203454251151712015401e00e0800b003592081250a115113500c20440342500e9194115400d2a04561300040c11428882140c60401b07000420051409490f2444039295400940061355681c0122041003020305080000540200c00d1f001e51400360b140030401d580c1d80d10321 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 303788228 1250 303786978 303786997
    0x1115040f1203060501120f0f0509070f090b030703020f031005010f0f0b070b04060c0c05060f0f060306040507050f0414090f0c03070819020d021816110604080f090a030305041505030606 81
    0x5644460078003080e4150700403141070740c234210709003d1400c05c0c0710030f45d59646e031500415100c0c1c840b143c800030b16940140b03c1c03078000220160291145502d107400b00842c0000c1c000546406000314280e80551083c0752040502030130150220300000313424109114641c000e6504004240c060030048000440c4030400038561240d403004001c01c1a000c02c1008880003030303403000010094030400003441606004000c109106010350081d00c8900c0d922030f001c140da201020369018220b6040400d061201e410020a00003200070060404207200440c0d103441c1b400b41500304d402c1c4546400908500b04200f00c20b00405076440030460050090740c1c100405191036060100b10329400d040720200f0f0804540b0f4030100c00c5c00960b001800c156101110a8a911489004441c14041c20700b141080342c1055016a801402d105540001042143d54603650a502c0e54807421443d45001028400d04032213540305103104001c0c612a54070a900d403072400d91880f940701752149111051280510070031515482d520151410120b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 303789478 1250 303788228 303788231
    0xf150504060605240919090204031a0f04030e030f0d020a0b07081b030a0609090b0612071203051606050112050f0309061c0b043204030509011115040f120306050112 72
    0x117008400250301c000240d904214108100b030400145040241e0180c01200d002e0703021508012075028a54a0b503140c1107a01c0391088095502040209110b00c19441e8220800360072181d601e074000740d910380741041c500352200060340130b010000e080150034885282c0100450074500c100e410b10040700c1c4d8480706502c1603030b10700140101c001440200c03075420480040c0000d01c01000342400d2801c01422240f402c49400b405026081148038000320300060810456070085288000c030042503404491561005c46041208060b484d49040494000d01c01c00b030081c00e00d040c40d02031700e00440c6000d50820444000b04035003a00144131050007a02c900c021103095441c0e03034032103800c031009407040308006268144015400c41d1500d030b0310344252230b0340140200b48170060850150219122004000c0200b0b000c0300c0007000104c040c4640c10265002d1582280c803200e0a2054840508010719220b20b4010100c3c3c2c02c5d075211b102a01040240618509500c1001110346018008607043c01d001804c1291070b40340c107000b00c5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 303790728 1250 303789478 303789487
    0xb0f0405220312020304030306210210050f0d0f0b010f09120b07031d030c120715150312050306010f030504031e110a0507090c02030304030c0206070f15050406060524 73
    0xb5104189550f1499106002152079003003606005004210384d0044030500079418002049545203104e807440c25640c01011690410141c06045900382c1040d00d5182e0f41000a1054024019013400340c0f107901810018002450b0744007900040078404e210a104003032004029080c408e103040c000b101241550408000c54203612441000c80080c49814650f840b504010044092010408401041e40c07403254400c450100c107100704000c1c1d840c421060700801e5400703840420f011542c510b8003e4500c0e400703104044100165a0703120b6044040103440c4410000d0b0000081000729070300a00040d01a02c90303403a0800030761400d40d80c041d004d21101140c40b00c80c0f0070110210800180f007800910312042d44a0191a400c10252174070b980e0307444241c010a0310003424490f90041c0c1c0307440042541e209035059504c45c205c1500c0c0740c0038000b0036845888140c402c5040d04000902140390300d80045190020f291001500f4500303810301000304d03100c5420443c821132000c21002055826490754100c4149400c0d07200d5a00d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 303791978 1250 303790728 303790733
    0x3090d030c1a070809030c10090303060e0108010c080c0301082104050a06081009141614070b0f0108120f0d06030b040c031401110a0809150a0b0f040522 67
    0x400881d01001070010a020540010404100c00e01070300075900d40d1691103182e160891a26280c1c012409640701c00c0c0e001844004845416412803083c25002e0309000034040e45541d85040144026000807000307030345445148418542c807042d1141c0c48034804102c0b900b503505014030b40341c0b20000306d000c0c08902c4000c0c00c0140c1c03245450314225030040100401c11000da0b41d0303884000c1c00c000c03402c6410410304001203400044550307e901588020002c01d000c000d4555070b481c0700304d800072502410314100300078590b110004241510001000ea0a0044501e00c280f86440f00301d98800d40c02c16005202181c0100b402034400d40c8124054403000c4201c0c001c0941c546000740301a1000308252f60020b03114041c000300b40401c0c0034008480c141980c2c0241102d2400302d8400c0c0120f820b80310640d82c00f034003034482000b0303003501c0038031454036550401103a001382c40c008212030074a00105181951900c140550350540030b030017481c00d100114101f101c1614148000c2c03420301500c2d41031000722207002c5030414029201d1400c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 303793228 1250 303791978 303791987
    0xe06010e1f0903020f04020702010c260f07050d0f090b1e03010b07051b060a050d180302010c020d0305040209060f030712110108060319060b0613080307111203090d03 73
    0x101851019160300190050710300600103041c0c0e20007640140001d02603c802400c00e402210f12440c3c041e1155003102c00c0c2035a5401c420048280150781d100340710440522440f180400034404c040403003081c0e07902c40020381041410040031214200034841986007581d146a0459030410894030600c06075034a91911902030002c030b161541200010100000000c1040395400f0084c1c084980a0070442e07960300b80f0304c0051a0504000c2d88050ba00032010b00603848040c0c840c8000340505200b016010488482d905401010300b851201e007200982d46070a010a02564104803080c50040e06107005d00c100d003001d40100b040004040c1c862400b491070b8507003441181c4c90801080e070081481d45030300500511039081130038410302d022904900080015010507a20720700003900f0106074400318002d0030700342d000c1d0769000010214180e985400caa000e000210100180700000c4004048071009160389032801c1c030b4507040041da10102c051196400d40307903d01c0c040d100081030b0740c003c45040d904090204814201640c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 303794478 1250 303793228 303793249
    0xf15030c060c06010f1712090a0909120f05090604051203040b16051203040b06210d03140a020304030c03030b060405151216020a03080c0c060915100e06010e 69
    0x9801c4040010581d0000c9000660b05049401e03d12006031131544664a46130300301540c02e80d0b50742d80da128100002030804008010070f22484000d052004003652003c0090581d09600340a942c05048143d11005141e00080d5500c0c100030300d0328000349803c841c0800036410b40158029a8040d0854482422210004008440252008000711516038044403a508840000c082c0b040303820780208081380d21a80b0b18402030740d0046510581c0446545e480809000e0b524a079400c0c0c181e10000758081e1101241030502c07000d4101c540c141d4000ca80c00f504030388422411035000d0200e4000030301c1002008082940450000401c5606103008203041c40d0041c00505a0300503070304502e50142900c01e0000c440780100004110b01847c5052261913540d840340c86043c5003224290f414050f8015074482c00000f03124a8045901c4804000150704000c0781028451a00004842c1c1c940607038001000e0341c0c0f00522010a855110141740d007880c202c01d040040e102c0d000d89010748058180030344442c00c05400d40da03480070380 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 303795728 1250 303794478 303794503
    0x3080d090b0c0c01060602030310290301060f030615020a12020102130b041404151a0c0f060f010b0a09140d060c0306060e041116051005010602070e010602060f1503 72
    0xc14207040003084092250f00018500300507604c0c08200181c86030012094074400d180b00c68610100a1401c080c00e02c0f6400c1480b41c006100074110040320710f54031140042c50180405030303900886a6000e060140489446170020310707464207045040143c4035400203006007071503841424418403101c07401041e40a07005242c6500c4040807160004100301d080c2c4400b4104490b1041c41c4501502078003403d2204a07a42d10361000c10500760a0410b202c0c140601300c3c1040c00005c40340740285008203895045003051220408507500c0c0d0062400e100012261103002400360814040a51400c0d09502c005006071040384140b403801541c9a031560000c0e901e64020216464110401f802003d12040006009128a001d44800305032501300c0c401090400e0721172002021540e480d0345140585988030301c2c801c5092000e04541d9441404029005c2c0c0d0703994003c0c5402090940c00500032181480e600e0000f0310016000741045522100070042d1f00c59503010165000707080c41c0003101401c0c2520011074100b03a80220342 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 303796978 1250 303795728 303795743
    0x10e0105041a093c03120f040e01050a0b030601030c0314180601090903090902030603070b04030f020f010c05030313080c010c2f060411130507030c0305060a05030703080d09 76
    0x802e54030300124005241c142001c440f40c10540e4031088407001c00e0713442c1641d1241201005401405004428802d240f80d003200101103951081c00003e804c90707a5070100307800907a03444010030108020031800207601c1c05400115002c0c0350b00c9007801300603040b0f804020285810141c031016000c103607902a9000fa40c1108000f000380d02c01e1302d85041d562402c0d5100c0e6926010303038490341000041c2001c00d03209a01000c3d5065484401c510700d0068500040c1d01301403c03a40e80b5024071440022030050980c01000154460300701c0c1c1017000198010000c5283c000c44c2da05040c04000c0504000080c0040b080342e41c083c083d052002403500311400d0040c41ca009000d0721303800c00d40c600704011000a800c0001c0200c2d10324021a080c080c00003a01840d030100181c054044580c0d070000340450005084540c02c03250303502000d001504040c62030031616054620680c1c40f507003c03070b070b5450500c3e8034242d140c06400d030302c21001d0f207801061743d01c0c180100e03942d0b1000b80f2024006580c0443d550041c04016000b00300d4240e0022003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 303798228 1250 303796978 303797009
    0x82107030b01020601050a08070e090f060405070306050a02031b0a0e040c09210c0e0a0f060b0d0b09190903050d0203010305070f080d050d110c0109121205090c010e010504 75
    0x10003400804901000a0151091600000703481c60581044801da86092000e001c4842c03503e2250080e84034041d1005180f4000e050b1480401031003003000c1885039010380002d0040d2423442c200001128005004044028010070421500280d516001c4000018800003281c1c2c4141c203940c12120349c540380c181d031640700f410700710f03400c011742c3e842040801070f11012024940c5000441c0c500103240c60007440b0041c151340041404104110a8500b081e600140501c80880d0700e1102c21100000c5900d01e03040144107403400f00320300705881603c0c89a174092074015501c1c0d009504100d440e2001440c0b24202e0b0a102c40d0301c91160034101403041082d039103514031000055440356124a083c030384820041c010300c0f041c1c2815840000d030300c0c032000642c00e500141c5911480c0c54612540080c0010380341c2101c6043c5092410040b082c0032100921800d000d4602500c65180c0503002c40740000d0600101c0108980443d060005018a861020881110001d400d00300103030201001001a2640e0085500c020702100f510b40c1c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 303799478 1250 303798228 303798241
    0x30f0709050a06080106030510022101030609170a021510030c0e041716021c0b0a0b04051006050d09020109030b0a050411100c0b0c0f0d150b0909040821 67
    0x82129008410b0385200f44541a01d50b440f0900300c0d43c1d90321000d4802c0d0b0140156420721002507009100792410031000b00620149030314407020180003070f03000704c03010fa030342c1c607208c0d42401294940101ca901108602d10310340200d10030001e41e50020800311444d42001c1c030004c00c001e15a40304440006680c01201002015910000c44410410449041d00c01c1c22503089984c0c040b0059104461400703920b2041c10291011503001d025248481641c040401c012101d58500403030100702049101b11400080424840c200c030b410700003a2440a03044a1440c00d200109006264103c0305441090081c60000941c41000e400102c80004c00c41e8406403c83c26041d05100c0ca02500f508490300c201c0c0110f0f82c600e2070020b103c090050b04e8000c2100130000451002c48440000c10f61a101c82d000000080c0362800c00502416003026688000c0440c0b031107541e1410500c90207060460100010044000040d00b8851f4400105901420003030004284d080006440004210032241041104e00c5028051000340361a8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 303800728 1250 303799478 303799481
    0xf01290c0f0714010f0503011203020a061b0e03070f0e060a0302040c020d180f051c0b0a0e10050408030112061e0203060405060d150c020a02100e01090f050a0311030f0709 75
    0x18000c54002072600303e046078007940210a0b0004000c550b07903c040c03443c0c0c644200f000c10149000f0084046010702c01e1840c0c0400c0d100e00414400c0859038503021282e08101c0d0010702a000803401e82d03400f03504000d00422045400c0c03110f01e8100d40300c4000d001c400d56249800502d0307213001908025840344c60281d20504190740018800240703d466140c030348801ca150091703f0325441d40f070310500c0c1003120745080500c40d500344440c1084203034000c3d4020118454082c4c0d10402003800454900001c0c03540e5003400054164204040c0b4a0000d030785400b0481c5081c1030b100c03d08275110500a24100100182e4000300f0445c0e0790340403811440708a001140340244142d10600a9401a54154400c50a01c0080342c65423a06001d41c01c6850750284811100204088804028080c0101d010b0158090302c0340000140e00c400e01c914140ba00d2989d1070020140c02c00f0005000c0750456008003480c8407501100f0f01154071000d00300ea05480e00135084c1610300d0f4260000038a41146250f5040c07203030040440001d40d0b050103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 303801978 1250 303800728 303800743
    0xe030715021501060914060922021c0203090a0b0601090e071706031609050c13090f1103010609050f041d0c030c060a020a082505150f01290c0f 63
    0x1842d00b000c1c20760342c0c0c0395421900d0f045180564204d4000c0240c0f1071400d4940b52004101c1864003034880400701081100103800404003040180d082600090810000c081c64520368001c03040f0840c0131401e508169100300d5885209070340007001e1a03610340200c0c880303178050b1600d180105510312031719032a0319200c080141165245101551151500c00108000d17160115a40a14100d40000c01c48840c2c40c01e640391025200c00341100c0340202c1d00304100c068101100c0c042101a010361840416a010702c245030070212082c0041a12084c1014030042c05150340c030504d40d604698003120f000c1d40300c1c01088006402086003c070f1301a070680703040448581c0300101042c0707001d07116821010f45807402034002c00d0001c00d11a032a40036006170080c0501400190041000d001030001560b580c4811024814500d841c0c24648a0141c0d000c1c2d202d200094071020360140200e6020a401a40c0c05a5502d0320810200c0301c4044440341007144161038410942c6030001042d02ea44545000403a074081e0030440c1400c0d00c5008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 303803228 1250 303801978 303802003
    0x1091a09040507050705060720030a110c0a05180a0b06030703230115140c070b2502010503180f011107021216050d0302010906110421030e010e03071502 67
    0x100b00005040038002d50682d00c07410f41000245c1996a6020421500030450701e1045c000441c0444034420707904000c20140034101c40d162266070201e0703451240c641c90030112030769840c030134210074000307202e03a4844031074000c80900341c0310480003039840e813010f2003016103500452036401010100804c007132658990001ca0326400290200b00e0030002406000d0900340f024081c03402c000c10207a402c00e2206102d443d543c01040750307220101c1c0c10685083c4200b402c2054983c01540c10342e0000c42c00c9680030f1088050305d10444100440c1c0041c080140d0300180603408000c01c0003c01d40e40c2480103180c4500c2c18001e000040c0300c1c0318020844203031101103014058100040c01d030700500304003a090a000100041c1e000254000b41400c1600520700300030130002c4000f9001c110115500c44000030005006400342410309141c80d0b01841e01c1c1c3c0c0c1000c81c3c2c40d640380000e1814a9000c41c0a07821000030a800c5110040806d00a01e0544c4071141c502010902d81242940f00d01d004090220703024012550200300075801c2003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 303804478 1250 303803228 303803231
    0xa0e090c0a080f06100e120a030509090702010e06010905130c032306040b060d17040803041401031802090a18050303040516032f0405071e0f0e0f01091a0904 69
    0x302d03004854000510100c803410b80208100b170a40702e901c1e00034000503a6102000b0b100c904042030f1516041e0612101a9084010501c04102415913151600c01e80360301801c644000c00200489011b2584e5550042c401c503050a0381da18080389024014080300b03825503400c540e03494151592403802240d0030f442444000da000080f81561000c40ca00800c0c0e09000ea600a503505c42103856401c00c01c13082103000340301201c007110445120406454440003510080c164100955100c0b45800c29011840d074143d000a81010b01d000c891100c00811104a20070880c0c05030386030341c0c441e9681c004031401021608a01c20200b101c06070348804020b4000011031245120b0740503030742c4008014400300083e18680c040101101d40c00a0f0749240c030400c210102020458070288003078a055000c000ca021958242c80420009100005003c040c4080140d0612000c0051504004008001d1300082c040f45c038075508a485164100c9021086a215140040240034144007510501641c00b4401900b50b00801149010390b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 303805728 1250 303804478 303804481
    0x12150109031104050c120a05040c06080c03070f050904090606030215040b0706230717010b0306060a030b0f03070b0712030506010c0f03170c0c16030203120a0e090c0a08 74
    0x1944580d8121003280d038844420150441c01c00104000b07460014880c0b0b00400c0103010400000700003c0480d1300910b180d450004260a060030422200c4003d5008074061181070418021a83e0b09101240c1c3d12100f2481c0c015080c0b040210110780611a00300603a40c00382c00d204c02c2c1d105100981c0c0c050022248205c1701c89030441d241c4212040a80614800d0301d0007004280141008940c441d0054095040c909569040e5102160314010040400342ea4100c000703855880c9020f10301c4007201ca03642c05003211954460440c588000000c1c451311507400180e0030580c41b43c03064015625620480d40054800605450805071104443e10951704401760503208649032000d00c4204502a1142600864040c5d44056107181e003914ac0c41e00b0400d80da00c08a0421010042101004c4c1318000002d000b00704a840d86590b80c0801d2040302d2070300d000d5580140540080450070070069500281085610030351002482d15107201200580d130803481c0116440e0403c40c52001c0142c1b90101100520505050b9207461205 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 303806978 1250 303805728 303805771
    0x10b0a14010c15020c01060e0117010b1c020d080a0302031e01050306040618210905010e1f14070c030c090b0d2d080702041b0c06020a03060b12 63
    0x10600124a0a030204880040707000200b908103d01e9096000c4180340549880b06060046084a01c1e540c00301002d002040010703c004c03102d554803160380250b000c0c02807003030744c1e0740c0d100181141660744501c6d129026603113401c8045440799104600e40d03641006c841901c4542d02c0710094069841118020429800e05001c44a544d22408445041ea070000d0004c240550f070300d98070710380181841c15030b00200d20341180b5060006403008860401c41c0005804440c4407812658028019140640046e418811200f030038a09544510403844101c181014a080c441d03003000d00255020403800f0039416030200000307101d20600442040000440e803144440c90f00704c2c4c0d81c070501241240c500d0380f001e03540014000f50304404078450310281402c805418950407803030b20034149010641850b400088810030008188031003540307810b00c561b0390303c0e400f15203031070001c481c4280c2d0041c106408200f00400d616804581c42d2541c5d4801d40c8844058a11080c4450740ca070b0f014106161300c44000c40d00382d00c030182c484620712074 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 303808228 1250 303806978 303806999
    0x307060c0c0506070609050a0320030a2309030a1b090507050d11130e0402030607020f0a0303050901110a0507050601090e0a0b19061d070201140609060f030708010b0a 73
    0xc41508111290400707400c100810545501c042400d580700c030307118007400d000b0071814008900168443d80b036140c0d014401c0441e9460380045000c40b030ba0260401d0120105458210b180104652000b112207180150180c44401da00d02a1025154151280100403410000940503000c029140c1d5081c8403c0d45e5540c07400f60b800d8034000c031040000a0070500500301012002d03007084104000c500011ba00348541e02c3e1581c0c40c2403610350301030000a10380d1414041581004e00c00c241d0000214405007104c05200320505940d191600802000c050f0b0b42c00024418440a5001031030342032a5035005c0d0fa0324040084000e02907042000c00380d90702d000ba0000054981c40500c40c41c03100c1e007a0440540611040c0381c8590000d800b00520000c010030800176000a60a42403182e14081d00c242020303010304200401d0041d401d41300c020075000c1903a1510b094848810490300050382e2000c000c031980300790740d43c83c60080303002a11061809601072140d280c010450f42c1c0b042d040400e00d284141c03211540180c0d100c84590 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 303809478 1250 303808228 303808247
    0xb03010606090b0c120a020703060f05070807180801091109071e0f0e090403030c14040506070807081c0e0f030909150105211909021807020f0a06050402030706 70
    0x2012881050040041a072043e02074045000c1e03074002d88071041c404804040f41c0b035000c2c0007000e0040e0001001402007111380d12500801d010021400c00040c07a2040c00038244003030262152052003004412161280c10f2044190007401140000340810390701803500b00c0700c428900750018401c644000c0002d4070b0503c20040003981451840c08100002d1190070186c1c1c3c1802d02105007400c00600883d41c048548500080d240598482c0e500000e40d03c200ba240245215600d030711852400310100300030451590b64000b514402c0e600b10b032041d550380d55503290801451042c3c4842140c21a1a07031140d8000e01c116900a914180e501010380c0c010a0494824584030320850b40c00590010170540820700c42001c041400d003c1d2001810980c0c40d05081e01c08114000c071210301035140706030a5200b0071507001c0c00510074400181199100344a000d03060350010b030080000c02d89040c0340703505039000145414403c0005178000400c24042c2c0c1c41144050500c080500b000710742c2a8000c0c803070300000045140c491103041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 303810728 1250 303809478 303809489
    0x93e240a09051e03060601030510080a0b041704060804081c1d330901090b090102030a0f0207030203090f011b0503180f031018020a08060a050a0b031011040905190b030106 75
    0xc5c405c40d40e521006400400000e01154841c00c05000c01240c80741040010104150142400c038109207030500e402400d0021244c42d0200e5180706020420680d40c1154045410940c8049086d8486200150004028421402c4110b031141040240c3d042060f44407849540100f007201a240080305408610030b40e003000d0b8820705410030405c5110b090401c60800c003150081400c40000c940d0020035102c407260914141c5d0310680d141d50010601c60719240c684182c4a5401015805608002030358501070345034000c2c10406ea0080c04080d0981219138440e0301440c056070700c40580b01c1c8052000741410383d0380e9000500260750f40c03944040300032242c4c6402001e9650fa02002070042c03102e504808900400703442245c408100096404c0300703130710041e0b65814203100640243e20007000113140c60540c000a41d5006802107503081d1074040c40b040a91000701d8520900c0441d10300205888600c2e405c10b0056100710307440001c80a141000380040440441c05490142682200910414406a04160032244940b040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 303811978 1250 303810728 303810733
    0x2401020c0d03030e120301061d18071215140301050c070b040f051f0c0f0807020303160c12030b0321031302060706093e240a09051e03 59
    0xc0c0703400a0320a404c001c9600000703100b42c170002d403c501c03a10b681540003a0400c00101d280c1c098402d0768801c48045404841d1400c80320034108910b11300a9202c2c144021f4105820043e02103240126255540c200100c0c44080310000d0394103550743c004418681d803001a11074407035400c15002c121000040c03419561180e030405040e412544581c3d440303040d4040c0e004411200c6001d00244802c0d422045020b649814004c89030110b140c80c005000100060b060304070040034015460140101c1550000c2a25070080d00c8407844200ca00340d100c000c0e0382d0100c4400000700b009840580e0000c40551640000d652a201641203941c003501707004d0700d200d80300f0904a600d8082401480040c41c0000070354a42c280b0fa500103040c0746d14041158444c0010b0b122440c8054078026500e40390080c3c107100301e013000b244001034107a090300405160b41d82c41c12814001c280b21840b4010100c44403201504040401c03001c5266412903a90f030341251400036001182c584100380c8201e601e40900c2d616101b030204201c2c041e4500602 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 303813228 1250 303811978 303811999
    0x612050609070e01110709150905190c09080304080304090c02060106021504030516050c15092103131805011a03070f031503030903150b0a0614122401020c 68
    0x2c50b00f084075a50a039042040641c0e1416000a00784040005031604020104a40e5041e83d0031224030800c80d80203501540c544010086907020340c00b0368050214508801003007054110a04a0b00340d001500000c0c3c0c00d00001500050302c810000c0100308803220b0b01824000107140000603600c4003024468180580c2190100745124a001c840c3da560151203414418180304000801d54800b144900044a2552111490355080e01c1c011072420a450168500b2078608080c4001142c601340320081080d095003000707404040b6000c03003802903880540d0740c182401c100d596108690820500c550741300d00b480320b10f800e001007030107203010038800300c1c62100d0400c075451501e1b002ca0895415024940070420540c2c0c80541c40110038401d545200214029a40c1d05a5182541040120000d41c042c01214240c907001c2402c84035110b40700ca80c02280c6807410b10703650501407540314001900c1200c08102c4001121070400900b0103104000304903000344000da24209040c01c2005a80c4c035903101c2e925075444a6400c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 303814478 1250 303813228 303813241
    0x30c01020715031107030e0f0301050c1605010f1e11070305040e070207091a0918070e090c0307090c0e01030509071505090306042402120c0a0507050f070612050609 72
    0x2c14041040307038540b030000768a28110f5840b0100d0b400143c000c50001e0742140000d0414648005e08000a0008038001c0003641014056801c0038815481c44012a08410000106001c020b40c459132540043c800240528680c031008200c03a0f4281e46080c45801d8a8040d454040c1150001941d00b91a45170f243ca40c58a418240d0740082c650000340540114400d15402181c04641c5001380002070504c11010410046160204010f5400003007904489d058061210080600c00207a503c0c122154440016556190a1070050501c030200d20150b0b00751054a000240212039688803506080c22565404160920440114161031085d1000e803982e5202c003000340070040d68005800400442800c1079460800040082800c0140846056a03003684c6000803011502c52080d241d040d80d40352a13011072611185401040302090044c00c81c040b03060000ca40c0300780450190084a0075190480122990390f4880d014a9a803040e060086030001055883c404076080b200c1e0051a0090030024400c03070707907581c889 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 303815728 1250 303814478 303814499
    0x90b040b09160b0a090509102706080715020a020102060402010e1309060b04060510090e070c020303120912040f0b0c070f0906030614010b070f0813180506030c010207 73
    0x28007940e0441c0542c100355030780510a11450710051848180d12615400c86041c090304504850784070b0b0b4042c5045904002080741c003440942d00b5190081d11a0a20b891002d4100c030b0300700c07410309401c4006440c0250219180c40d0002c0d8030720840e80c10711840400f04444090417038454800b80c100902690082011500660043c41d0721040442c0140801d0380400d03400021030103680b802101921aa17503105850700e03071070500d0300459000d04001e9880b611040c0070040c0007414009584542e5070000e00c520302050f00203104100c0100d040750018100c2c0e40314140b000001e0403040b000d0340c0c0880707503100701c0e030005050507258030594003203411036100140e61030f142060f00c07005540400b034540500d014500022500c1c0b001c1c090054040c10040c20001406421407408204841d4490b41460483c0c42c0c04004102400c3e01c0d10440340072603400131408610000c0388c9000030b10380c0298061400c0c1c40c0310080b40801d2901741b46103908442c0303d02030000c0c0f11607154041415141c00000b084240142c00c0440148980801e9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 303816978 1250 303815728 303815731
    0xa02150a0e090a0b0d031709071d13080c010506240904020706091e0308010504060b0a0e0103060b0f07022409010c0510150602010509060702060a09140703030819090b040b 75
    0x1c0040c0031035003d038800c0004174040500c40c0110080303207200311044c00758000d07400b085910a103414001e2071f0990514580034410030840405506019081001074060b01c92400140c039903550202e21551503010100315940a80022036105000e1844260001f02040c456290dd95941055001c001c1c944100718051001035844103906807460b030340314500c40d4005030119400300c00c01141102200080401c92400804400040e4061841141010414005d22031040210f40280c9160300303040b0311150306940168080c4c0241d610001c41454049503200308901500003e040d00751003201d1000c071507201c3c01e040070b040d464506032520745068207200200c0c19501585045010300c3c010340c02c40f03141003802e41031181614480d0340c600311111034402d810050950240540ca800c441d685028110034a00080b001350707110002000e80ca1040e0300c1e408900e0038044506901140924100e00b0b41c1c9800b41c590501034900e80c400c0d20380c002d12000348448101c45034500d105011030203500140c442c00359125034075581051f100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 303818228 1250 303816978 303816991
    0x7031d0f13180f0b0c0901020d0e0111070b1b1b061606020a1707030b030a080a1403010f08160f142d03010506120a020409230a02150a0e09 61
    0x16030718900c6901d0503034000702c5448940308408a0030340019034a040000320b0005010201079000521021031540e80200360321180f89001e20301610325a4110004070f480940c0c54030019414041c292000c500503c405000b4200051141c20100c885000154a145c1d1000a003810b0702046581400b00295441c02d0002814080700c628261081c054054403008105d0b40003c0c54140803405c109002d0161441e034802040c0d0148007401c040100140e488086600c3d00803250740100014170008581e10280c1c0034156200551102c61010790300c0c4e6071102d400801d80318082c040c981032841421000c80000d02d1588044040d2414000c1c0001f07528540f080c07211001460640c0c0c82d03030004440c84e140740b042d14450440080382905000c10b9842c0842a028107003151800f070311903402109190300018030b640300010000d22056040d1800120744a4a0401c42e480b5040c00398004c208a1142040c0c0708000741c0040c480035110f008881c240c0c8117040050140415100300c409020110789000380c03058603841c108da0740076803010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 303819478 1250 303818228 303818231
    0x70b0f030a2a08070c0519020118090e060c0301060207060f020309040e1e03090a27181401051603090201020c0604060908010608070b091c0c0b07031d0f13 68
    0x204180d003403021245205004800020281d4446486140d000407411380003070417401c0490712406a0344030251140c090180162580e914083c0035000c592090310544007030090590300c4038a440d12582e105000c0c068800e0001c5141c031030f10020500045c1749030110b81c101d424640013080b080d80360207004d0ba4500c0030b0221450543c00180043c02403038640d4003030f11080040c0e000140c5041c51804d80c240000308611241c40b200340d0700c02d01c091402a102c4104250686000d007413500e040e514007000a880c0300c404030f04240240303410001c03001018404800103c1d03030b4522840107112001050f0480500301c4400b00c0306102031841e080c59031062a40268000c2d081c0740c1c01807040d034008254240204909510aa100e5400505144000c01008000788614800b8144c1c7d4070280001c50b20704100120746004520700e02e8031800011490070704107001208080407840d8003060700c080740c5598903925419a00006000d4000c556103244006581c12071544403000d48500030445619070701d1340c00501501c1c620307c2e2083c44505 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 303820728 1250 303819478 303819491
    0xa02070b0c211504060e06120a051f0b03120304170a1b0201030905010e16080a0b040201030b0a0819060c030c080103030807140c0309011b0c0504090305070f030e03060108070b0f030a 80
    0x392240e028505c09052440c000c1102c90828200b41720400341350090a02c020b400c04120000040c00100341c0e16180b203800e0800c1e15400300c1400d0038100074201d21800345c0c2d2601c100ca44904a650240000d075116900440448a580c00b101411800510400c44400005126958520ba8441c20112510304441c018500050098069600c40d800c4a00480450880c0d43c810750060144d2a09001010003410202002d07000300e00791541d5400b0280c1d0080c10080c181900c0c2c4504502c40c0e02d5582e0b510004210355411038110104454404030404a1814240d99442c1400310314210b0302e00901501080185664078420b683c2c0c03a50700c08561032400500014104103034075003c2480c0c4248040500700d950f10b2000030315502d04402000ad416041c902004200002e00c0354102c2002c56038141492045400690b00404e200c1001e1508403814491038000608610b401090030050690140385407140343c1c0f0070303400c84041c2c0c0d8032540d5040d902c0060344507000d0510003c0054240b4055001c2c042c54000c9072210001c01d41 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 303821978 1250 303820728 303820771
    0x12030c1207020a121110020d0207020d080406080a0b01020607110f0a08040e0f070203030a020c24090106050a050607020d1703010605120a020708070308040201170a02070b0c21 77
    0xe204080d6850001a44495004400e00c400c0c09401e8601680b07609141407100c240d15456070b02d80072150304070001e141e40860b125116a00a40450302c409600400003ca11212407070701880540043c0a03c2c40080e49800000341d45420a10412003003600580080029a0b12450304403107003074060500c08004c0c0207c1e94485401101004036421242c8180715142c1c5650030450707002d141407002032440d1044150601400b807415004030840350098000c2c800541c1ea00003500e43e40e403902c290810ba04941c4a01c1401301c581c8000030b8215103001e039403a40c0090000071b603900d04008580085000e6281e100e4000c20451005281060008000c00d22950b00003103400d092006a90140e0805d92103040454000203041c00f0802c0402e0780e0a600c101120300450400d043d41d1984003480c002d40354000d0a02c50303440d010a082d68011020008400c2c83c0e001040e40d540790405042020303401200c0704076608a80103020030000e00300e1505942c188d02d410500f0b05002d640d02400302c10111000b9109140c0141c0b030003c0c0d41c25 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 303823228 1250 303821978 303822007
    0x405100b0d02040317190804060908120612010504030e060d0605090103060506010f021b1e04050a1a0a180b2101020318150106030e010609090507140105030912030c 72
    0x301c0314040c0c00d0060f101d900c0d60074031440601d82800c0e03508840c0f90030070140000078840c840c5440501c000340341000b41580c8500d03004000700b0141340c0c00f41a411010036a50400140904424440d42c07080d10b03245070342201c0c801c1e0a801d80d9030543e0010f01068551519058034200007024021406521b200410540e6840c004500040000c0c0c100b0f81c0c21645a03c00c0005035600041a007040c2c0010340700900d4003030550120100750100c402c04451243c2c1c3c051b450f1a810b000c03602035584918100130404c00c000c2c200815a10000c10f1703101501c5000030070100182c02c3c10f251600c1c90000711031000050424240320741c00100f008000050103030b40d00544029642d15410305a512031581c900c02d02000503568184900c007103040004409803940c2542c07020b84491201c00c81e04002504641c0e4030f0502240ca440001025809082581c004148040c41c040c50501413050000b510300840303000d041c4a0342d01c00d030303040300454103440300702c4201d50744e5032003010812022032000008581c040c0610303036500c0c18411401030000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 303824478 1250 303823228 303823237
    0xc120d0b09041101170c07060c200f16050303030109020c030f03130c0b04030206070b18030c07030c050102010605060403031b150509070605030618101d2d04020405100b 74
    0x1950403508200d2201e9950300007804021500d10100f00c603961b403a0000380b882d114485d001000380740548584001080340d00400641c1f5103810212018103080024800d4203658032480f1300400854441c0031400d50484c0e10784800c0500743e401c042d029500e940e08001c03203d0007a6100b601d4002061100b001a00024004a00030718026442e50360036030310024550070a03448610b0341e50008008100308000c03c200580e03502c004c81317501561120b826146641e41c090700c0c18035080404901c1c00c0a010001c0c403032400d03a002040c0c140589109006610f003154403100124200c584a001d0660050010001880424003800803d6034a494011202d5088981c1e036a441c40389100b89500490440c2d180d030300b44885107006211040c080c0410389000e41c210300d45074000800c036070f060381074080c0e400c0d02030b0000c11302e0b480070000d51030047c0c2201030751000c400001251301039902004580d40c00da02e140d42d0301181c00410444201c100d01c0a40e14210408130744880d001c200c000e22010f0b00f612581d6940000001d40c0c20301d80700190 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 303825728 1250 303824478 303824483
    0x6091b070206070804180b04050709030308040c09110a02010f06030b07140d021308010e01110f090604090c0926060a0b040905010f0203010510050405090f0613090c18020c120d0b0904 80
    0x5a01545005125411f44e41251200c0f882a8140300800a40d80d03408260502141e03018542020203484500b4860b00e192a20340003003a4490610150002c11426203006201440003170f4002c12070201c40d00052401c41d00305000050042e104007001c101c03580e00c0341415192041c000210030349800c2d55001c03000b089920243d1500ca03d84000b007420891a0002c1c4283c180e1203000030000e01c010001d90134810700500c11035450840d400c07030104212515407155000d85000d405480d80802401d101d803600904a80d0785489440c841c00400c50b842d400c1c2a02c4a00c0d0700c4250128140100015100c2180c0d85026102150703450383c001d69a06414000324109020b01d180c10441c0300c00060303a1794142014880305140b059440c8061250402c400c10058440522403588010203410b40146a268840080c0440c80020715205c22941410002c4082c85100e044400c211398289804420591035441e80c03c0590080d4031910285411048019104c03448020040c99038030302180c000140c0504810020301884002e4405 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 303826978 1250 303825728 303825749
    0x50f0406050708100b0d020f210702030c0a150902130903090b07080f0a090b0403080414150a031e11040f0512121c05090604020906091b070206070804 66
    0x18041405014070405070031407603903d8a11494903090712120002001d92099a000080005090142000c140e0560700c200308070b048082daa50408841c29405250342e500084005034503000820232082c000411294649008009070107c0b000c25103c0c03103034051028204c0c200306900d80d41e18000603a030b4818543da102c104034500141c244541c1c240140040d40c1d54100b0b001404017000284040359544080c1c1c1c040a0365001e400d541c079008007008076007036411035002410b1050041804402c0043d00d0000d84240e80a107441daa40720212681000120700184001d01c0100700c040040c1e1541070300c01d400984d42400341c0d100070718081c9460750180040b00c3c1405081c030752180b00030505100351660a003400008010854500780350003540021030744c40e08100003124110000000c6c0340783c03641104401e5071a404011007010042864051049074076010129000c1380325003003090000f20390f403604980490191200042141c88409045022021503024000982c0e000c14213004000c00201003d00420140450414 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 303828228 1250 303826978 303826981
    0xd0204170312010603050709030221071205160e01050409021810090e060603060c0a03180b0a0b0a03110f01030b06030915010f03030e010e0d0c090507090902070b0103030e01050409050f 81
    0x2c120715401c6041c1c20110030107041505111802e40e000c9a900143c9804440c98656103d0314401240700380c000c5c0850341064020b0303c81c000751444003400c400340c0c04e034000d0058440a0783d44c000506142021070003020508000d600040c48103080540c07040011070b00c09812502c9031a00822442101c83d011122103400b1849031109006e0004a401005d54101c0504d0042485080c000002911483c0082220710020400b290381c142c014441c0c1c0203224040d07080754480c0c200484901305002c02c42c40845802800c2400c0031000040384c1040030542c2c0880360498003030210b041c454010000485241d56000d4101034440d81d81c0010355a800c80210b0044503c44001c0008207030180000c13a11460590010101c681b00c00020804203400c100c1803840d901c001d00c0c000c201e1580000000f02041101d20b0041c200d00366540d400704055003244d00c0341b8010132540d1920000e5981d00c5491700282e01c104203005080150f000300400c00680100d46501080005040c501e081507241c4400c40101c03101107a2544540c5000300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 303829478 1250 303828228 303828247
    0x708071a0907080102030c12040201020a0c060201062d03020111150f070f020d020606010e21010624090e130b0f04030e100e120721021005130306020d02041703 70
    0x440c0d000f00400b4000354114074040740f02c9500d900a94030f100d4408400c820014007168401d001d5680346640c8084191103c64030307544001c0c001c10f01409681150000f140001d6404480c002903c40b40c2000d2090b0500d501e401c5600440350f43c059141050700901c02c0001a00030031700400410b0b4401d4504141c062100d1411740c000502c0811001910001c1d50080001d02030b4040d404501103500c0f070400e08001007024580ca002c5003030000c130549282252468005001c0803004107411140454025150403880501c100f034440d181d008030710443e980402c00342c0c40304202074095a01c445612031070024040f4851900d0b5150608008800c6940b44850307078480c41003008060700304600c9424003c05440782121a4500c0385d02030858043e880501d4405c42d04449641d480040401038080500401d4060f0040d140c0d04200c141083c001c610012813042821a140c950541c0c881e0003a10941c40841342d940e12490300c4c5441d071000940c0180007030b1402507000c00012032030142e07404c515031500c0c0018000795614041c25 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 303830728 1250 303829478 303829483
    0x19020f010b040c0507110619050a03051513050907030f03090312090b0426030a18050d050c060d0e06070806010e040501180e0c280806100b0708071a09 66
    0x40041c58400e034500382854040d2a03100003654080c0350f03c45e0360280100c10940c0040d00e64004c611030000704414102c86510165482070182c0108442503d00303200d0764131040810101085002c1d030058200f0a4452041c190107a66042035030080d1210041d40c450300d4803511028003e01c02004160041840b01c03504200308100d038007402080300011b24040e5410b5086c500114454801e501c124608000000030410000092151080b895104481100d0340d501801d80f0150210b588403802604023400b0460009242c00c0419981c40304641c004050300c0380611010810142c0d4014004411540c0d0781c402d004603201508000303490140e07609881d2001245840c80c0010a003409440600d8003542c2810010440c01e02003500c640c801c00c21020000c1071800810030b0b25483d01100c5a00d00d40d0044040d4011070030400d044144113090b259942034000119110300317480750344990590b001c00039151422010019074070b175000540581485003c019107010070303903207814140c9070b44984282c4840380044140000d80604 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 303831978 1250 303830728 303830741
    0x30b0106050403020109050d0203031209010c090b0309150405070e01031a01080f101a0301060f21031704060f0e0c01110708060c07050106180920030d110319020f01 72
    0x140751540c41c040c00d66000900703400c4103100d0603020b819440100400c5603814001d4684001c0042c0008001d46400f100650182803005040400b007501035001090300c4441c081100d108005800c0140035000a5440c200e0304030a0043c01502c0b1402071440c0400d003c5503180303855000718010f12000e074051050f001502a000c0c410fa01c030800a40c044805591050300c0840d50408034030b40071000203038403a030a11101031390038207408440d41e065180000100d95900c035241407109403003080d040081c20310501d200264084c00201c2020340803030940039490344401c1c080c409103a0b00510038607000c510080507826a02c10358a441070750500b140c100e04402001d5503403088060340b0721001c2500800700e1070300d0007803130130b850718400343c10010500d40001d441c00a204094010764000d003810803c1940003411101c81e04010002c80c4c03000c65040e06080b540f548030208a0300301e1240b10400a01420020218400c203461040040071034003c1c0d4041480301440550120207848040f2180b50064400e0050141c0344900f140e10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 303833228 1250 303831978 303831989
    0x908030c0c180106200c0a0e1009020f04140f0402040621110f030903070c0806010614041401081906121b12140109120e09060a08060a02070f0503030709030b01 70
    0x2c401c40104005a4010b60090141c030130018826041c10400840724207024003514801e030017101078003000030b9a80c903d01d0958402c00b07104001101e05620740e8125416445000e0140740e04c188148014025465050f0540c04400c030004e103c0207030091a080421706036003044d4071100c0803c1d440c0c03c030f4403010030b11052040c03004036104d081048514180e40712040740c3e00038030b0300c41701fa10ba00100001700d40c000d04004817599203800400c500310a41c1d460280f80d81d1100d003401045c0c009000c035400d8ad0050040c078402d0301c09440110b4002c00e035954904004590040b4002d00c0381d2140030306d000058041c03800e44c1c41198058200d110f10b200b0000528208181c04018840a030f05040a2000081001a0f249044094007030350045850308840c0c44022920b0141000000c05092071340216000d61102d40c01c000d400c946000305440d1a200d9546940c10400040e046110b104020703000040000c607164480e82c003d00e1141d01c0b07440b070110769103030503112949150421544100485c4070b0850a10902209030700b050700421 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 303834478 1250 303833228 303833269
    0xa120b04050c0d0509150114060c070b0319020a0f0c150c0203091009050307030f0c080102041e170a0605090a0818011106041101050f0408100b01080903070206070f030908030c0c 78
    0xa40e1000c0411b0052051103104080382c08034840800e20342d40c1001f1210440a0300003110081a00c03103030210026402602d0740031402c02807802c40032480c0e00b18002c2d41c100501584501d002c0b004084011348a400029508840c9910110956140e40109108000c90340d8041e0f80155224010702090082028128000c070003031000c034039810030050341c00150b1042540d07440406500d04a9079071400000c900c1003900004a15400800c0124518070001501280740030001291503903150780e51078003003002c90f0020702c0d0042d0750402039031000840c0d4a90001c40d00402803c0485003444180d49070041039800108008400800320b481700c40841d03a03c5050442581510009030455090584d60b042d1149800014503041c010089020640b0640e9102958000c0c1210b005a80a800d400d03518140100400090343d07001ca00c0700e10200f00381c460000700b81d61a1a41c0a07203054a00400e0307032580c1c6015441d04c1d40803030400c01c1d000004501701c1c4050018056a800400061583c0c2e4420401c102808181c2d02d0081c01c0c0c079 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 303835728 1250 303834478 303834493
    0x63006032603040204110c030c1f06140405060604090c02010b2b0326040503030603060703050108190204060b0a120f0209060d050a060302030d020d0e0409080a120b04050c0d0509 78
    0x1400703180440350415811174002a005401340200001360041a404013800d00000c2294180c0d00c20201e04d100021a4032814810a402400454400c6528031300074003c0d032590524108070a410280c1c400c540101d4014a601e050950707480d43d810950b10070440100050751035182660450425000148200741c5c0541e01075107a40100b01000c580300b603010405801c004a800540c0b110385004071030740880c420038a0020300305107810b0034816682d40c401d481080c0644982c81c00940001e02c0f03407045905843d8000058070100d2066940300e06080c011200c1a6803040e0307565000a084c082c80402000090000c0c0c031030b0040144881e1901c4116003103038000c807001500401010301c903035682404031084d1032086000065a515034074001c200038002900000d405215440344042155000140c00c103400c2e000c0e80d40d43c000001d101c000d0200390b400080c0002e000c0f400034404000201e0080c004640040b0b4000300000f003c18003040080c0568805407014401300d0f01c001050710800d1000e00440f907008402d02e0081800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 303836978 1250 303835728 303835793
    0x606020f0a02150310090203040308010e090703020f0d080d14010515120a0e0f01060605030a0b0307350109060b011d0a03170708071a07090f06300603 66
    0x440c60283d40000d114100100040d5406901840000981240b182c21501c902d002c0c90042c08095080c0540c010b40741810001035050640025140b003943d5024102441d03841c140000c0c080021603004d4122043c0e84244160030354160309205100381c4500c00008054554034144c280409041c4002c140c085a440c10001110b0300410000780c60b4019404900024000d002c0390959402c0c00c04203002c03020203508044000031000d80c841d019601070b5a0340c950402000020004166460100e0701c0303482c0d030103000c0032880020800c0003c40c1d2031075440c1c000f0b0b50f0b40c54140001c3e80982140c80b507900464003142d40d0560382c242942d1203062828910080d140441c485040040001c49400302403100a004d122011484060810980142c40069520448440c0c0320038903841c002992000c2c0c90f44d00020890444005500c0702c0c81034940908a45444825001c0c0b60f040640c200c0d48001581c940680082c00c03000d12810601010008003422101081d0000b40a0b04528000b480d1560880ea402451622080100c10703 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 303838228 1250 303836978 303836989
    0x51203030708041410090308060402040e04020f0315010605070c14030a020f0f030d0305010e06010c2a03020d060207050c0901050307090e2d01050f040c17070e0a0606020f0a02 77
    0x41200c03075401c202c14a540d40389070803042d801d444a250302c214000e018a00c45078440c41d8206c054514802d4a401e0801c1c0c0e58203043c00100d000c1c1d40304081800440d0001701e03001d41032460000c418002c0c040c0565090140a20a500000350b081e408540020b00004603041441070302c039500e00141051740300c0c110608000d10f002a070340d00c06010300a441000254492a075980c0e030b9041c901c20186001e020344d00d045001c840050001c00302440380f0f641d21f41c40c00780003900d19803094100403802a8000e41c250140900541c88490880c21039404000e203100684000c000b6945205501e001c00748034000240e039940507803801904028150040740d0207990706030018009998045000d0003901d1310308a00251580b1040025807508981c601d500d003081c0e407008104980d1810080340c000e54404402c0080c082070f185d050b40341080700070031507000d071220301c00c18003d01018003407000f182a180c50510448010030345842c01803406042c15152030131440e64680703041280c41d8040c85100302e505105009001900c1454011030b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 303839478 1250 303838228 303838231
    0xc030102040e0415091202030a0e030601060f05070c0e041118090309010521090c10090b07151d010f0e07050d08090a03120302030106032a0305070c0b090a0c05120303 73
    0x40c0142000016882c43e0f13180e545c85891041e030005007000e60700105820203526584800c0120f000500307201c00d180b105040001d4440c2c1204d4060b9903080a0366201d5108950f1500200400c440518200d20b00041d89001c00c1e0843e80110300603448410003800c04010045845182c2d50342a56a6040d0010444a4040841981e403004c4082c00e09a540d021401880400c60311380c1c1000302c2040300c44074144200107100181000b4444020780704d0901401c0e00c14016141440140b00c0c6070f03080003041050030000383e48401c0e800303001c409401d80801c00c7d9410a2410a0421000881d007200f40c2d0340d1000701030700c180140141d03407180e843e2001400b21035040a011401c030301560388020381001400588880ca5484011502c0021500412070391000b071081f500050195100b0b05c0703000006414a4146042404440f581c052058490449890105000701e4242e02900e0001c20318400d005d9600500c0e000324645040c458403c00059018003070303040403403915040050007034000a003d184078106510f007420000007240d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 303840728 1250 303839478 303839483
    0x8030106170112030819090c0b0406020d050c0c0d021f1722080714160f1a071121010603060606050a09030605060609130b01030c1b030c0c05120601080c030102040e04 73
    0x5420802c06c580034607002c0e084840c80141940e0380706000140c02101c200c0980140ea00d0351342a22a000c001c4c180844850141109001c05d075004010b400e115441c00000d1480c2c00d81c80a1300700c62030520320744c00f010840b035040c08000700411a00605694048810340c1034503406000720707041c080c1040100054150544c250913000b407600c4400255442404a460500100c1440f65000c031105124410200401846144030385001c0103a02003010642001c5100f503849040e05601402d07051505a403101821039a40d1000d0300d8001c984c4814081034811015041c1d00c1c40e190380c10000ca8618a5858031004440381c59000008100c3c040c42000c1d10158000c4030402126000000840c0c907403600700010354203201d0490040d0f40f00d08440640c00258946030040d800f00b043c00d80b0200101550110244c1c0c9102c02e40c01c035071103044460300440001030700440800051a00440d20540710a484402284070107207121001c05070f580c009001000089000c01148000f10400c0d80203608062414512000c200f0016000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 303841978 1250 303840728 303840751
    0x30f02032205070e01120309060815094602040501140a050c030a03051e0c040603180813030203060a09120507020303220f3f080301061701120308 64
    0x410042c01020840503000e0a851903c81c1e1155035202e1314200c010100ca030046000ca0f400140000d0b03414001c52030148034071070800c000d2612501d8081082042d51004024444480210f401941c000b50f00483c82a140180058883e42e0710710070b940c3e20607402825001d800c0c45613004002c2401540d030303c50309410400340c02c850807540b2441040000c0e95580a51030700000d03e0b22000c6031996a480e41a00070a018a210342c2e1926050b003820401d48034500c2040743c1040400c1d408000811805100f980105a1100c11042d100d403030408640d100e900c1170740240030790084600041014810751409000550b040b41c07100104200002441d070307810a0f040741c0d00038030038148a030210b40082551000d2003160020001404829070400003460040140c0006001d00d444002020340007160901c1d00351022001c01c2e0798400440050081400141803030b008506c2074040103c4200c500c0c2000070107070000b841c082c050907140c951481c12041d4042d410344805902c0405610210148040400d4000c0c0d80300b034200015452 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 303843228 1250 303841978 303842041
    0x50318011a1516060902042712090803070506040b01051e01080c071a191e230103080423010f08040606170604061b08151f050901030f0203 61
    0xe4400b05070003020004080802a1005442004065840341d00800e01c2201c04201d03424202c1c800755807542e182c103498540a003e010f5002e0104260844100e0f00d1f031050301c1d0040800780c440181d542035030040002121183c0c00071062104005c03603849568003405042d0380c3c80c01d00303101c81c00300740326900003401d112030601235018003040d00d500d50700040b00c0c0c103150400c449290b02d16201404000e004411100188a40442d41c0e1030002e50066000341401221b540c2002c0c260036600c407054070700030b00708417003400e803203084903030303070344100c0469912614029400769550743d0716245005044e40c80710030703003c54901c64419520811001a03030069500115403001e0300c1d080440d03564500e080303801000d0075004034288405968500080c1407001480318407640c4945010302508101289064107002070031010b0380401c004000040c1000d442150741d28104034000d00c450f1031009900d41e200050502c0090380030010b4000119084e1030350300340c040e000410b1010f40d130071451460460041c03c0010394100040250081416 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 303844478 1250 303843228 303843259
    0x3190212040e1f061106010e070c060b0f190608100303050d051515180f030d0f0507060606170f070f03150815070908030712050901050712050318011a 66
    0x50344503441c500c06403c907452207485407000350001302c24140e42c0074244210300020503100e000d00700c07150149520380c40c2c022906003a5590b640180c5541c0301450b40040c1516910001940c0b04c0166031401741c14800008020390a116008021000085c150744c171100c46910100000303a03010702281e68607007020000080540354041002000702540c1a56580015041d03038280030b180d1003400600310580d040034100642100c03c0e080c0005a52843e090561642102c14440807a900074030086841110500e01a0300e08122903851008032000c94024600041c2c0c540403004824081880c03603600607081f040c0c0d030807284c6080c4c44d0080c603005800c0758120406465003034804084da84c1410b508042c1c081d84041d0780304600c9165000d43d800100b100d81c800040c11040c00010015804001c4032400c039009040d5580b40000c903801610b07198480b600250400c903041000b0300c01700380e010745244122591a62000d80d2418811610340e0725140398031440d806645050401c038448143d12000d000c841c0001da4903503da24001c0c0c0d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 303845728 1250 303844478 303844501
    0x3090f120d02010606030608010e07050d0f06092402090d030311070203030409021e07050a0f0c1503090311030c0601050d0c0315050a140f190f0e03190212040e 70
    0x1400980018418a10003201d55501034010b901662500c0d41d00b0004943d0380d604441c00d036114191085e4503a0003000d41407210b4202601d4040c019405a81604842c900c00e50b1540d045802f9610103a481d2042440c0400511050380300c40e850000c1c40d01c40c00d50600d841100000c014031850f100003428035941d901040da03451440000d5560b00341d002400d5944581c0ea400025000c0c0d40b1200001c8203000210118200e1100c0c0070b01a10070064000c0010411441c2984e42c1408001e079010b0141c0d00d40051020004110a1503007008a654900390350110f207000c1c4a14024144010440700512a40c00c144001e80b1107803c00070704181100c000b01e44240001c40b43d81008130043c40250805040000d010707800858181c42a00032600804640340200603010300441250441441580c190700d00b00d5440001c83d0000e2a2840704032246c1004540c00141840c1c1d9140f6581240c48140112055402c04034180b5038000c039910050f40900e42d0340c0081c201c1c014500c84848060302c60381c0074a030084403122000c1501000c04 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 303846978 1250 303845728 303845749
    0x506090f0f0612161508040804090b040b0d030e03121801050d021b0a120206040b0c0307020708011e0b040c02070b0c01061203080901150f060e040e01022b02030903090f 74
    0x9190544da25100c98030030309000702da520302a0070291200c0803860188944915201c600c51f542166060f0301303060810b180c1c0005000420001c0368400c0e11381c45002d03aa03591710940c40c00524420b49420a2104241c028542000101c86240003801014084c01c42803d0b104102d07402c022609280030307541d9142e41d4411070000d010301c09031125446600d0003e028548000128044824014540c50081050100e022a900c5400312002010010f4850100f5001c4210401464001104d40113aa516035202d130013413401c40300075404448035060101c002d42d038480014810032004482c01d0710140300b44082c440012f90b58030b000d441030420043c0005400b071000c0000b03502410141005030b02c03203128103400e03090051040300705070350307500d529480c0c4065201e90700c0d03400c0071100483e881c88500c0003505243c44826500e50200b12085504503841c2c00c820030300141300780b00800780f003a00c0d00030074007112030104030301003111095808400400d0b01c10010b202d0000c4000040c0d41ba40340d0704544203514030b5a69008240c1c0031a5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 303848228 1250 303846978 303847009
    0x121407060204080304030302070e070c030c11090a0c03060501031103010302271303140a0e0603090708060a050106020c01090311040216080309010914010b01080a0207170711040506090f0f06 83
    0x1c08180800e00741004402801240d00a40c00c4608854070b40d0302c01d80c83c0103000c1c0c0f03070000400c46154016001901880e48041414000c040c040b200c445201d010900b049805c84039a00202e54030900c920320f03240c1601c1503901801d42860304100c10311000d181c030f00315484103000c0030f889500c0d0905800c040c0d800c8854a152404410080c500080c00c0c00144c00d030b09200c1760300d4103c3c04240d0012000d807a0161200c2503440210284c1e458180701011002401807551010b032496020340183c1c1d03400718202c1d00411503140240c01d00c100010700c542c54440000d00740039144100741d04009001d50200003042200503103090101d002c840050303031070241001240c1c624520110091001c0e00100c1000303040d01040d807050b080345024480184000d84003140c154201e0f107500c203000340490220347c046203007207040358080c0c8031943c811000c821903064050709035000c1e5000600b084448240500410005051a00640707030041d0050b0355a28090404800c02c08140304020300650024601d0400205c140c1e0310750151264103070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 303849478 1250 303848228 303848231
    0x15150f10030f0605150316050c01020705060114030102042702090406060c030905242a100f020f1b210403060b0f100809010632040912140706 62
    0x128046030140203858070031482d10380706140000000d01400c3c81d450b039101664222035082d1655445180c04103000303074841c6290b020440140540c0c0c00c4140244010a04540250000d060541c0b4040c0c078201640464030301170340283d00502c010042518510040e060f460b51420034503101090300140100207004004816921074100080014296045504800401d000303039155021a034940060220841e4001d0b42d080121449640140e10031280d030001c3c10600d0f03901001807031525124146407000c140354442860b42030304080104d00200c100351141c2d035906c1e4040d0105508211200810603150f00903e9900c1c0c0d54800070428082d0020410311111103500d0450503010100d500f8030440742019042400212480c1c0e103407504180786880c02ea5a150403121000b0000b04014a09420403160503002410303071031056480d0940032941e0010300304a08241d504040c44a1903451100c5000e900600f2030705403541c012860036201034040307801c000d0f42c1c10700204241031041c0340074034149280c01c0d28810704101a10740c0b07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 303850728 1250 303849478 303849499
    0xd1a15030d09080d02120405060f0c010606050c0d0c0b040209040807061a0102010e030c100e0f0105070e0a140a06080727030203071a040e070302091011070815150f 72
    0x40d40c00010700c4056030f402c0c000f10f404c214480c40e400e80c3d8074045120303084000131040c007080009142c48001400700e140e004041c07509100c0301e01405401d5542e242c0081e408541c0200384d0744407038074041000b500000880c0c60980804081ca03159030358003881c068800b9006000e128001400c0c4800b200454a4890b84000104840100b681c0042e4036540c0368000c0300e00650a1070b07040c1c0300303900001007074485422240020381a203c170341880070402820400c01c041090f0103880244a10104288611807284007242c032241d04000c034500070040208459002074014404c0846811401e4607807a2482040d100982003002c040d45400c0802d41e56010000760250420414040000c9045501c4000c50101c910a40c111410183c03500340300e03d01c0403001500c0d000c400109000c10000c0340003440526401050600380145003611030310111705c1d42c0c0614460500800c5400c900c0c07030740c03040007041080000c01201c4003a04602d203440d4049401303660040d10b800864441030307400d50403076900c150104060300d6009040f203900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 303851978 1250 303850728 303850753
    0x22061107050a0c050306010501020a050c0d021c050d03060f08100510051215011a03071404030816150509151e01060f030b010207030f080a0c0816050c0d1a1503 70
    0x89112901030b031380c00ba01401c00001a03550001a038500780b10390080c0070301940900e81040c84648a2074540070b1740d200f6801c9900d074030700414200c003809020340610040c0150b0100190003405031407165001021281440c00100301268001c9407500e006c07040c0c0308012a0540341c40340007030451006908495030010300e4404002d8403d000140b5002d001000200a001c00c0c1e984103091100d4600207003607a641d4140030000100800c0c455a030034807058100c01040742c10140c49440b0680950030007540140950f500500d868144100d5201c0c1d40c040c0700d170a039014002072501c1442d0361781701c40318900b1000c4141c0010300403e00440b44c41c0306c6c2d07094003040c5801d08143d0390ba407040c0003400c000482c1000c40109140540d000c1c01d951000c9003000903250070019641418516a8540c45c00b5407103854004204000b1001c0c000000310040024020b4124518405840d01c0450805134284148952041d119881c007054040004100c6500111a1107248a10883d2980c609401d00102d031100405142d0500807400750205 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 303853228 1250 303851978 303851993
    0x1a03030c03091906020c220203010e221511091003090c0603050c0301051002010e0105090f01062909030a0611030708060603040c09020a05090301020d0c0822061107050a 74
    0x5800d42d08481007080740306007421018074076520b07000e40c0005811040700721440f0700302030800e110100306a9944001e4800e03024003107000c036002a0130035a1141c0f02401403003900300000076240c034200c1141004005a110310740e500c03820504064940b50006407510001c001411590b070582e5082040034056a00c551703450b0200070002c0450000c00c88013040303b144085004d42c4030784102c9200e00740107074026241da420202041410001900706504564030765054680e050401c2c002c1d14040c0300318034000c1c4440c0c0452062642558600c0e0480407405000d0349108415041e1044051103807080d50469070750b54110f80300800e0525003041e101500090804c411424905500001103102e000380e5603910405441341000c01420f40700554000e00003a408900c00d10842074140d000300500d640078100280b400840c40080fa00b0780c1c1006050b085000e944000e81c006180d0420b14040d40b140c00000c821200507003000f1501d102100803040544000e40c1c0308a041081c0320340004491035250080d00301d0343c00f50200d150912 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 303854478 1250 303853228 303853237
    0x4060b0307110307120305101e0503010e0d0203071e050d0c05240f09160810050709050307090b0103091424090a03030b060403020603040827131a03030c03 68
    0xe002a40e0b01c0d03a02040d20a0100c1900d0300d29601208500100c008100c00314050036025068403001c494a60b400207144150b405001c3c21203000340400448039142a04250858a039560054120303003004103213400c82d035070110171984090743c00551a01408040f078440c140310070302148002c0035803149011000c0b2458104030801009881502214400c2101c0100740311314450601c0d00c105d00c81d56000204072402080310394241c0c459a440c007158488a1034001c20380220400740c1c0b0040ca150410924840c940c02c0d40d000f0b0540c047d20904280c0b2a40303151001103a070701c02480c0b050303a002d941e884108904a0b8866041040c1d02904030501d4a00228103460742174540c500e1081010010b141d00c00a10100040c26070060300c00d00c445401713002c42c2601c68400b9009403400d6094994407000803c07005c001651600040c5010b54050319441d903e031541c440300c00036201900c1400c4040340050320100c00c0f07156946003000e005211159000304034602c00f640d6410790700654400300c03a4540404214106d08650020180 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 303855728 1250 303854478 303854491
    0xa02120106060912060f181115160f02060a050a09080105010f05130608100c170601081302030a020d0b070224040822030b1006030203040c05091906030302010501060e060c072304060b03 81
    0x4c100c1000080140c50280041c0c4101414828460f0148803040c002904070400cbc014000707481d0440d496400507996903c4041744a002c2480801d003000a1a8401061400b03059140c0003008594142010380484d094148102c522490902c00d0101100240d034201d14010a40e090460b140088038a03001c1016145a44030200060740510a0620f0f484207021054050750060f11400b880c0d03211103807003011103100c0043c181d0b05485100050341c0140c4500442166542c02440c42201a04001000074100a1240b51407040c1112203d41f0f400b00b1080c0095850704160b12081d010340e203150741d01000702d111650446422001c0c601c43c00000178042004130f020711520800580003112515030106908038081914050402071320b0341030a204504020700d9840e00b00b01c0040540c410b143d2038881110584100d03410481c01030351070f000104000c54001e4440e20303124004880f03060034811103c00d848d1f900c002520404d115100c44c0a00140b540240b507409840e00d41c1d0103402402160b440d04031303080d01640151101c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 303856978 1250 303855728 303855743
    0x703050309040525201b100212220302090a0e01050a11180a050a12020a150503060d0819020c030f01060602030d050a0212090a02120106060912060f18 66
    0x20b112480070040700da00001034603850500c0c0074000c81c0c01300c0c0e40a201e00350740c1200000c405d2404005000c1007004180d2a602d801400034030f980c500d014095a206009519011755004007034003001c0e0a4901c0642c1c9081201c1d40e101c084034084000c0d20303018007140c1e510294004507601c00b44003100c01305d80c002000030600a002408651108800c01d001c44400620407017500c030060010140c03001d5404000e9880c5440100011550390f1a940040c6008000343e00400030803800999480c110f09191110b40c0040484c140c3c00c14142380e0228002e0601e00c030040989200d01110003144040012920545066254280b0b0b00d07200e144c08002d02035540c80b400c40c1c1d8144248507540c3e10b01405417050241505480190f400785051182800c4940050080074140c2182c03d0303004e22001c2d42c0b004c2c245003c588110341c49402442025100c0c01841141520745c110424540d04010007030291a8108000000f11800c0c16556444144075003009802024010365501405091405558080500142c3c114815008606 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 303858228 1250 303856978 303856981
    0x70215030c310b0c150702031e04030305070605040609061107050106050a0308040e13211b020a0b1c02071406010b0c060f0601180303050417060408030a0905070807030503090405 78
    0x480034802440c00300c0c45141002c0a8406000068038080941460740e005400c0b280000003e00150003805030846406005900200e071b8068040c0c2946c50000c001d241c40c0404628140c19928001d01902c1091400303045507031203c02040800040354084581c59802020810600d0200c40c0040c3c016405484180c40760740c20140e0120b1145402d60007081140c0d40002402c0c5010320b02003008598980c001c00100c80c2e241c2090b03400010808202e5516204402080c840c11115541c141c013410551340303031822020071103108400740010780350540124141e4401e2442d0030344610402c610030420350816400405020700200701c1e5410000c0c01d00700f686510307041c0003c1e207856030381f00d5409031802d0140545149030340c2c0c4040081740129038801401d0b60000b1041c98044480304c80802e00001031807403170740100d001602c005402c02c01c3c18400d40350050041700c500080c0140b0700b0251500012400050452a1060341d10300e90a0204401004904020035446043c2d841d465603a00b040e41d20303074000105031400b8504000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 303859478 1250 303858228 303858277
    0x10020306041401080319090b03070203030f01080d020d03110418060603141509070509100e03010b0103020f2505101406010c03170406020c01060e0a060515040b070215030c 75
    0x701c0382e41680c034158015400e00c140d10035901e02d00f645407034004050251014001c0303400da035a0002103205540c56001103030f690406a0101c4100382d0140e0010529401410032480c03000c0d40407850b043d0f000c01d039181c0800e1901c1000004030721440781da0302c140301c0d03070f592030040c04840220b42d045201180c00a840812080700324807a5540b5003d000c07505001000120440e00026140101c80035800040c140361050810005c0c102045a400c0c42c00c0b14000480c18103e8094044c0c030b0240201400c501c030a1905506003d03000f28140c1c058016200100d01089481d030540254600340354001c2401d07500001107482d0007000410700c00007860901d82400d50b40540400241840d40214848991190b040d40e17400b0500d0881c3c0f100c094480409081150059002c00007803040e10000d0040c40003905404814036554182085c01030110707046070780820b000f40707022413400e10b44141d020103540407602446d100c3c9a54141520010740c00480c82e250898018201109100c03551103288003800c01d00d440d4149003a0f0705070250b03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 303860728 1250 303859478 303859511
    0x7030306170604020603130c051302220b120606070611130f030c0302010503180d180504050f010e0c040806070509010e0405061c0609060509240105060702120f1002030604 75
    0x11280079405c0302041000c1021003442611036810140101c0090402030344403400501500c200d00d00d1748081a402044402216213103521040c0c50040660aa041e41c0f40b400c440c001f03050056050b0442480e81000000b801c0740c40341000c07100d8041d4080c40c01c0003000f6035140a0f102c240c0084840e50b416131440f80002c0781c41d03018840040d068cc1d07040000c1d00751140c6550700440303103940018a2045220100310010880d03030410071a000c1208800d4a0b0040c0c49080304c00c004100b00c20780d40c00a1b10803400d0905000d403011309145060305403a105101c03100c01d80d8941351954502c1c460350340f04224500c550740400c010103034400d0140208403400d07640c0041c214650b0f030410050b903d00341e410b640d00040891021308200d414103548500c403032040030049a074214035264181152001c486400e810381240d400000c04031940300422810602c110350700381e401c1d41460089081380c01035806c002e01501c00302039000ca07040002c203c03a08440961600311151490381104910181d0400d88440d4066810007550b4000051403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 303861978 1250 303860728 303860731
    0x503040213022203050f0c06030f0112031b05150901141501030e01021308240114120609010c020c0f09130204110406050306010806010c02030607030c050f070303061706 74
    0x14140c1441070341080c00400250702c00c5a03030000204010303200080d6204001c1c80500118042e40152109034a10402c00d130078101016646403103640c0400400200b1603a10034054150ba40400b0780380a8084d65280643d44807840d801070010f19030b44010309074100131b00080c80f011880c0d407a103441a81c545882d405107090f180e0511505030041503400c00500e40340e1044e000d00206030414980820142c442600710317400c980c414084003003411801407080c00b41000412003643c0a035505545401c003640d0441c41100901e03018002c0c00c85001c40758000c5032665031071030210f205c490414010380d80c19082250303c82e8000c0c9480064031000d40100d03180f00e0814502141c460846070710260141d000b50b41c0e01411050802c95041e81242d005035180d132403002e982000d02c00360001d4136040d210140d40c1d041240015280c0342006142c103041001540c0220016140070540c190080e80905000c65912010f12003924a402114100d03840c0000102d03006c028035504d90010000c039410074111001c0c0388560148161550720 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 303863228 1250 303861978 303861983
    0x912050303040b0c040504020c0604020f011404060f2a2102250801020307021e01110702090601091710110f07030c050a0b070306051f02060610030b0904030c12050304 73
    0x10600c000b9000c51800f640260340620310f10810f0b840c02d511080010300f03c2e08805000700305075001e03504210071404d040d2010260103600342411400490070380c0c0305901c584200d0040348100310000f0040b4000304c0c09081d4100c112070b49110030040e80010315120401c0c140c60103500baa41c4281c482201205008842100098082c20f54050b1804142c0429003107019001213540134407103c244c0c000010491030a10145000c2c441d10307400b400c0200c041c0f01c070a845804a0300010146a4074003940d8541840b400d034120b4060360b605580d01c203601e40d20900162140849036119007503011009120701d4107008082105d070768224a40340208804000d180c800500d60044941c42982100d0400c4440c007c00d01809038400c3c5544a0400c036007140c1d00c1c40d81e07054900d407829112500860f444101c244800e2421510520340c40b103402c0b0403044444440c1000075556134014240a01079410703129800d5005110350404514404043d24030308036400c092030000d2800c924000c4c1940e14000c803659103102d0a100e981124060368 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 303864478 1250 303863228 303863233
    0xf0309080318070306060602010e060a060609090f02070f050f0d050c06040b0619090606090e040317090f0601120308060d0b040615050d0f0606060c080d021305030f030a091205 77
    0x25107681c420400b89500c424620200e100303007000040010304c03034010a0054446c40c4d0002c40c0b2002c450286514041c80540004000c80c100303401840320a074032204a0b800c0ba2600c10b0080342c800611f200060003841814800f82006900c51502d2092000000f00426804203900071a030b80c01500c200300711000c1c02803681131a0150080004030300800d01500459410102c02170440014003c2c4402500c1c03d41096407000622540ba04010414036401c01d01201c010044074003580641c3c0b819a030001e10600101c50541464103030030f40418020f141c20065160b5055015049500f5540c582a0358141d03081002030440c0040d040600103211400c14801080d8844d07401617450015450729a5002c1c041e0104400d00b1381c81c429410b0740005e0554440310f07280300d144e01694900044501c54102482520f409070441424055405030110000b10000100d9040d8840e01c000140c13150b1001e0405400124036a002d80e60502c600850b0f000392400200042032104d400d80c0720464050341d84c1c0b82c2c4071005003145001038000d8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 303865728 1250 303864478 303864481
    0xb0105010f050f180102030c03070b06010215070e091b0403030c0b1305060c0306032a0103051b0a140409021c0605010201110703030c0c1403070605360304050a150f03090803 76
    0x2d604c296107260f02d01342c140180c0e42083d1918140c03501e190800007054502003a001d003403003d95601030107206102680e610694410307144c0114081c02d8443e001c20034074081d19000740040c00e60b0880b061042840808901895034541d0340c0d0074000e0030000d0000065403003c003071101103942c0c50300312586200ba4503403007405884642d0340d000071035030380740c100629994050152101c1003c01e01e40d04500e10000306a0b0001c001c49040300d03d00010100c0f80e00803c50000e401580e201e15a040000030180c840c50801c6181c09801d00e0640985040c144c0160b90100b201180081440c01003804804d07801030300c8020100040200c84d550744012030a0b1a00440302c540d0400080128401207032094102d190301c10102d091074080c00e1003ea440340c1030b20082c0c0c54441d0a6400202c0d02104015071401440e07009052408012040055902c0c4110780e54000042c150101c29651002c0c4070002c028825900240310040445c841c907a5101a68003502c04800c9040f00024050405100301078081d2040080f01b5030840c0026046 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 303866978 1250 303865728 303865747
    0x4080607120f020a0503010806090c1f090b03010e04140309010f030f150801020c0c010816030917030a021306081e0702100f0603020108010b041d060a120b0105010f050f 74
    0x1103100c40c1074103000054464040e00103044090004160314507640d91415525813500310300c181080c1001d000c407042d680002074060200c0c0d4902441306d0400c031300c000803c88409400f00c0160344940c2d590740520540036020000250500141048520880c09441449102107061681d151603201d101403850100d02455148400759102e90700c03800c0d10b268030401c00502c0c080100070b040400074080d4003444490b900010f0310804800c1c10310035401c20030000c0c01c203403c2d5401e0078415020345a05440850b0304065035901d44500344001c3d4240c040b5010303068558250b40e402c20003200d101a40c0404100d800d62000c0b4000080c001d1711801c40c0e580700d4000c01e140c0c05468a4482e0040010a030003614241c1144610004540180032a11402d03803000b81e00c1c60005000f034950f02c0058003008050740700c03120101080c0300070000200494945002e210942054642c60398507240000c4000910b81c01055890240c2c5854100f041401495141615801d881d5215246200381040b10240b251500d0401c0c0e20106210f40c804 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 303868228 1250 303866978 303866987
    0x40c0b07020f0909070f090b130b0a0f0b040501090f0806180f1f110a0503040305030702012d060902180f0d0b190608010c1e0c020603010b04090b040204080607 70
    0x5100344010826550b0006200005000450581e0341030314070b8000c8a8100001d20200e124a0010b101b1030001707229107a450000201c80d240103000c029a00c40d140d00303d812481d6650b0f0503940c081c10703c0007070300101191940082511500103015141c00b02d500c43c0804035100c000d10481504440e030010003804144d440030200c00c4440402441c0110038030405240281c025400c4c0000003548490541001c0304041445002c1d0070380c0c03011201060b14400400100280b194084121b075030007078240c03c0065a80d180c1c800224014128880c0e45003001c00d1034903016804610990011a8001d0682010700034a0380301e80100e004c9115805003041102e203042c51400d030608252032075030001e01c0001c000d0460800c20361200c500b0440111202d00d80c00c1d50300d6945036000e6046200d80409810080020403012600440c0904020548500755403001d01c020704c501842e034400c50202000690141c441c54403569952940003054001d400742404403410485030140a08043c402e55040340c1c00d00700103007459100c49000741e070f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 303869478 1250 303868228 303868237
    0xf011406100e0307080d0f02010609090b01060c0507090903080403031406012708060a0b09010e100b030a0b1e04110f0a0f050d110a091706010b03060f03071d0708040c0b 74
    0x80d0140500d58000a03540070a00c800c0c401080c1c1601c1f411521514042e000b401c444143d0003940c0354602d42129400402c0d8041442750542d001400c00581c0055141070040ca030001c641e00020f01a0b08003002c00c020103601078032080c01a40701e0b403000d104818665507114100802290600e0001d00e45041503040c0d0003150101300344202007103480b0440d15484890140c01c5c41011941c0942e07140e207406001c1c440d4103109007954010110f61031080b0103801d01c00c038142c0074481302d4421072100040c04400719800b40f150b94444030104c00d00811031441e0488a02c0508810301c044451036225a1905945269102d444000c5031501e0140e00c9107d80341194006050b9a14052540c506c0c0030040b0501445003501545c0c4620a5071031410b8503241d89a100c000300060036118180c02c00c190351040c41c40b4000215400142190568a040e20215200d984480100300c43c0028540c01e994144030b08400013440c0301c90b005080510b003601c0301041c9490b5607140c030240c600320019503000b48900e800c403500f0804070000d240a030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 303870728 1250 303869478 303869507
    0x209010e040f09061515050310120c05031603050c010f050702060309070509011e05060a020c010e040b0414040c0b0901020d030e24060f040b1e040209040603050f01140610 75
    0xd0307a40081e00e0b450200c1e45d00f141c1d40000e2013881e18092202240c1c41c11042041c070a20300e0a140346250014a8600030580c61003504503081c2c901c440d4a0030071100c0f164140c007422020b0122261054100c20300200104240f00a0b41d003801845005405c95100d558251004005c40e00c68904d4035120741d0a204507544010030504c0f00340108100810bc1c2e9844440d80b5000b0310341076100d4111411900a200c07480700c030640c08188a07500c00c02494005a40103d0000d20a82d02401c040b90120314000118000e006403034a41603000c0d2a15503840c14103401030003d01c0c0100d01421072070001c5500d88140040900c45c0703400311070160748400300c41c82d040d52082c1c100720201480d0f18151482c15030303210354155481002405440040300c00788108006814080031030b41d804601203405100d507001000102e2894a541c81c100941414040c0c02172081e522190100c40400401500c2080203d07924142580ca928030281a44525401c012170740311138104210171240076400c000c003d194540400002514800901c1048 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 303871978 1250 303870728 303870731
    0x112b080403020d0f05010f060609090515090106021005090706080c0c03160b010509090606130b0f1503010503060a0b090c070f020d05011b02010e031b1c030b12010209010e040f 77
    0xc001030f03c0c0d42c4036015115108a0400001101c10314009082d140c411130300081080c03401908211040d800410b000460304031800c002920b441c0d005034201c00d06424111150020344840000995680c0014038a0740011558402c005603116440f04c562150001e10a040019401d0f202103461075400c980202034000384a011a4a00b081c41069207482c0025141c00761040494a0010001070400009055000c00aa8040d001501c1c00d140010b0f510440c05500c1100745940e00041d0307400d83c4a030f500c055030000d0b0091032103c0c0b66582000c048001e42c800d004142c001d02940380403d4400455005510241c100104044110343d19110b0a00c0141c200715401d40f04040b45070441c1c0e01507200c03010f020707410900480001c1103800f00f047c43c5520f45101082070404681c5003d51120b003100002c0240c40d41c1020303000740d00080c00202140e491810240e04400b0a100c2202c0019841840d010b070722200d241c60b070640c2c1d003103403820580326241d00300d005200b0704070701040020031841c107185403030b900038023100c03882400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 303873228 1250 303871978 303871987
    0x30604031416031701050916030c030b0607051b01020f03040608040305091c0b070c050a060e330c070b0a0903120908030402092a03090a080a020a112b08 67
    0x14000b0068845400d802003013840c6186412055134020b5180504401d80700741d00c4c0c0e03041000000392401010540344c410036a075003c4112a052082d081b000400d6070062810762110300724101507489484510030360001808002060070654008a107200103001d600f4013540c1050319201042d00d500b18001c00403800c00c80c080107030806503658502d0b410104047d0500304418100603280c00b0ba00d0f13410103000b039801d001243d20b01c500041d00005200f01d21075030007040811031941046c1c2c5940b800001800701c00903410701e80c0550303100100035043d4070260702540c1c40c0c4001030f071950060f1950074441c0ca90040e000305000c80001b4002042600943c090751f11928100c02c0160803541c20a00b01c032140e0340300302ca0122000080c0700540c941188110f4000c0401040510640c004408103071280d4030036138030007508242c040001611b0319002d21005100a800406007980c5900380c2200940b602c0000500300d03095101155107081f1418a0700321a20180311103001e8600c44d410118074007036004002c11044440510030031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 303874478 1250 303873228 303873247
    0x60602061305120c0f0d090f03020409020d0b0c190503010605030106050a1e020c030c0a050306040f03020f01061d0a11040b070602070210020610080d08072d12060e060306040314 78
    0x1c00e03c9101040c003510510305d02c007070100d00b4003004070018001c1010300e8a081c406035000190f514100c80d41142d0000c4c1108840c0f0208034090f0240001138010300703581081000300200320004001d400e19150050380e86202401d8291004e000a0181c20300040b01400103000c990301880c0241740802060610701d203a0001503064401105501e0072040050b00011071844850504000301010700600300d4001100d0390410000c031b07986090090003d003400d12007451200c18503009110340208009010001d00406840d00c220f25150b2070001c0b1156031a01003803000458040c0c130b5220b080f12402c01504038601c0d00d841c0491b084507076003100f80103807441c0c0e03030030842100160b0380d0794401c4400c0080c0f078014100a2410013003003111410141e0200a141c0c2104254004860344a0000c503400709a508018070131020b40307481e00030260900c460200f004e800503d004290560400c0d000004400d50440c1800303000d07212981641400380c1966003a40684c007130804507000a01448580e02c500c4401c1c92614184500103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 303875728 1250 303874478 303874513
    0x10e010e030715030c11030915041208090f0916030b032d06180a080313080d090506070c0308040b040512030a020301050a05090108030717040b0c150703060602061305 73
    0xf980640d50802c0f5a01826503c00d03098061490003818500305a51814490708043c0e40340d10800c1c000c01c0c81000a07182c00d12020b6150400d45010308905040380c08145142d29103110a64829a0158030907140602540d10614214404901c1180308070401e0820082111099018005540781e0f00c0e8107002e245031000e8140b120400b1003126000e603400d940940c01c030b29014075040100280030b11003210292811401314070400190b0701090341c0e00c91001980ca980d00300c0d000b8040083c0a80050450000095008400c6041c0c0c004150a5020700141c40c1591180c1f1019224000c00c04030080100b200900050041f401100c5040e9211307024000f660400000081510401d6004072408840a94048010700143c00c0041c00c40d005090183d132500003550400e00c2c1242e4074040d442000300010910340003404030442000542d0024a00c0004254698815060194540d414402500b00c9081c0a800248186102c1e001c1e00046801c140c002d0420350312542c24100d80c500152005031074600c5800d001042e0318801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 303876978 1250 303875728 303875743
    0xf23030a080a0c021c0f0306090903050c01050c04080d030b0d0c0806040b0106050a05030f060a090c051c0203010501050f030408040f0b030f07020c130e0a02060a0c020a0905070c02010e010e03 84
    0xe950351603010701d04841d4810840f041d010700b0008550150341d40050761440d481c01e10441d13510a0804110302d030002c5d4011406006d26411005560f42404c42c107000b0035800c040900340d03a1403920000e000a0b91040408000c41c06203224004180c0e2041d91600c2c52213000b50f005402910001d801c0345583d2a20341c88074820008250311104ea03917440441000248180440d5040c003502280c940203260200808000b841030001810f000348011110004c07400030f0b41d1b603106c00402001201d00a1050b41c40c1e03040302400ea81c0150004450990002c202041c900040b03100f00c9043c0c90050b103030b072814060013400c003111a400017041190048800c010121300e140520314050010841540050755a240c0444807280740e00000d032405042d50301010300200c0542d1106447c1e22603128586000a804004680d40c92030980440c00194000c0000201d2103401540300c0d0703039050620700070758a16150b941c2d520650412a80f04031081c100141c8200c00c0703c00150b00c1104c4148003900305261802140c5031007c00170b410401c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 303878228 1250 303876978 303876997
    0x3020a0807050309011e0c120e04050c0915070503120601051e03041a0601020c100c0c0b031605160201080406020432030a0201020304120c170102040807050d0f2303 72
    0xc04145852150380c003810f417281c2a006072641b00d80c1c84c0d00d10b0304050291184100001c0141044094900c111849030307010400003c8010018040e0741804502d200c3d465000f00c120a00400e1042580111520f401d0103d0f900740354040300562510280070403810042401801d0700d4100f1000300041d40300c00c0034069000560a001040582d075a080c01d26000880d4003016100030958840c52041142580c2c000c1024440041c00b03640003000d0910880b0201d0318030000000003041c20310485804607110b14444091441040b1214011011141c003040c19149801095505034084d41141140401540305124594015100300350150a2945603240d14803500092912228600c018100c030506040c02d54440c042d40c68010340261004015070740000303441e071242d03020740c4c61700307404450005040080c002e80d404001d100000c102d140c2c0c0c440350320809020754001e11408400344034126001c960351805501c1e0700d0230780d980040b500c089089180c0e02c011088003114a40802800f000c840305260403400c0c0b00030700d081c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 303879478 1250 303878228 303878233
    0x50901031e1a010501030501090501230301020d021b07060201140a0c0203040f080309090a0e0309061617070b240f030f031308060f04050c120a15020705060601080411040903020a080705 81
    0x44c1010001400c0b100c0503800001040e0070300303004000b0000c0c05020900c0c01d2108040c2c0c42040010200030902902c034450320740e91200d10014880140c40d9041c0032410811080c40162031000f80e407500200e0076180060304c0c0c10414854840803038a2824281d0005e4010350036401940d06040e518112051820420740c4041e2135504001002c0327240d4500300b2001d41d44050489420403201000b111625640d00603030210f41d00400d80000c0f81007245808130b03e942c9a840d0310000d070716403001c078144200d805500918400c03180b00050502080348803680c40295143c11203046008110303040810304010411050301112074242c098401898080341c0180020101181e91041190700ca41c985103600b480c02400030031030044500c1c840240000200b000c600414810f504032000300f05047c9181d0312a0500154403401441c11844820030054100c480e000b804025010b4800c1e1405556648015641c3c850304440060080c10b0302d01e60301d200b83c5401d40c02000c3d03441c0207104030f600e5907015988041c15a48000300a07902036 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 303880728 1250 303879478 303879481
    0x30406030f0f0e07180f150e09030403023601091a0306100905040212030a03090b090a020919020d09060b0301110a12050a0e0312150604050901031e1a 66
    0x401003402801508900550b040112000c040c46550700c40364a405165860000444c2906084005400000562030504010410044042d4030002c1c1003055200380720038141c09000050080c180407043c0c404403a0041c5c4685260103003100503458012040b041d40340f407510048071031004102044600d40c089c0c00d82d218002071005180c241041510b8918400a1003503020a080080040a81581200300d40c2c60403c0800c4981b1240b000880040745072850405070302c00440c0c02c540b103e0b4550000c00c0e901d8018806006035480301c001098a030501004041d40160038600030484480c4d1607103485e829403480d01001420564400c4118041c1e4a41140c1640c01d20740313416294600d031800b840356400e0703219811841803a1800152024001858181c02f00310195a50720010303074000b12030b41003c1991001401501d5858150741808085441d003611400d18081c5e40c0c41001d501801c000c01101d0aa800042480d107981e880c559808204401c58130044500b0700689881c5e030000340030003a80005213000006075100d135 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 303881978 1250 303880728 303880751
    0x4030c0c0510090506090406030f0804051306030206190318080c0d0201021e13050406030f05010c050a02030f130b0705030a021615050703030b0910030c05030d0503062103040603 78
    0x5004030364210500c68120079000c5001c0a03008248078040b1181900c00039101c400c1340f00003d0041000c0d60000e00b030508a841e508040100200c01002901e800f1244098135600c1c0c0788605040f00c91030b00000b504100100682084428030101803400000b192502144070400c0d40c4407007252140e854002c541203000810901030242040c01000c038500301c50b2008600303144111185042e030721505c007091200344100096800c1402d034503031510009000003500902401d42c5e203192640040103208000d0f10294600903051040e103200300d0448200390010390085082400604003000294402c0c0f03540c6560803031800000030004000c50160070010f0180010b1500c91141c00d40203801d04100b000040d1041d03003055402d0104590102d41885038007510714180f0380f01c8415250513001060402070041c0d12491a80800c14000840980c004c252481800000d1b49960303131354145a640c480c40030b094000b007842400011218100644050080d2140c41e42d4968ac42807082072942c210352103034100e040080d8442c81030064 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 303883228 1250 303881978 303881993
    0x706090905061f052d0c010b04050412110a170c07060807351006020f0109020a1403150906040c0501020c01080a050a0207050115081513020409031704030c 68
    0x1407001040c0c511031a0442c1d98100d00c0303041c40c0b20180c80c0091100218401001c10201202c480200c04004000100c1420314074103117165401a02840106600b8802403400c2814a4002e1340d0050798051482c45003055815000c0d43c0908903040180440e12070b41801d000490b0b2942d5019101030b0141e504c00d035544988407819403c00306030350020014000d170070080c00310460384040040c01020035580c04c0d03880e400a1054000461803490340341101c04007140700b440303000d02d6404241021900b60341c003182e408036604281e0700d00360381c5004c074040d41c84030300030108001d28103080f45480c900480040650348840d10452085019207005d444003905640810208020030a80c8032041d400780c4024001000801d4440d40000c2c0203d0300100419909520f800119000541c69019250241d90181c000d000040e11440007401e12080d5200d0340380184501071110401d014404401405000305401070080c1c0400313a000d10002e000c11046c102c0801c5a01000c0100c440312400206002c3d51090350b42e82520465410b0544 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 303884478 1250 303883228 303883231
    0x4050108010b070308010b0f07051c111911010c0b071d040605130b040b0d03030e010c0f1707020a141e160501110c06040e07090605040f090515030706090905 69
    0x140ba490108042c0c00402d821004050440d03e10007107090703451034909011000d0380140040107005109041043c0f60710610800c07018459041a80e4081204180c400143c3e075610702419000044030741001c12401180c0e10b13504481c1e4204040c14031101c1c08545a80b2407101a404641000001d050014a0000007480d101c1c4801d0104080304c7c241700c040e05110014001211145d400d803603040d0f0382c00040003d0307110354100012160740100000c50321031480c10040c02a0108180f100000d500e000c92400a80d0300032004010120026038402d05010920380d0440c01000d0050042000d41c0309280c100000103c40e8440c21204107450b4010b04140c651986441d08000c0306103e40c1500c42c1c12001c2820034844880742164101c41003481c02d042000d005100c083d061190700350328181c0005000a0100d0400d03058101c3c0c0d4041c001c0380c0d5445441959605040350940214099620214480c2030200150320f059085185c2202111611290040450001a2801101c2d6110f0804104955410840c3c9162885030a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 303885728 1250 303884478 303884489
    0x207060201050601090e090c060c0c0901090606170703110a171005061909080307030c1a040302030415050c0708010c140705070e04140a0c0f0611060703050903070807080405010801 79
    0x2e00c51410460f001829404c9280501c1221702e030200005044010300b0800c910468030042e003810ba03079044044500f922101c07000150342c02282082c0000071011124418002100c2040d61002651583d0b410314015051001d030048040644410604100301c110300003d0084100e10707100d94482c1e071800b1020501e082c0004009a214099000c0b04001c151200000c444a10a00341503100940104820a0703031484a250450a6203200200f41001050340103200245030b6400345140780402c4061b2401c08640345000c230b40050068200740420001019400d00b0503211003002e091a604007940c40302110b20f01221035100718000c2c0e44440c2880b0996070805c0cac001d0304a4101c0d0032260f16181b62a11250784d61561131007003500e0b4914102c002014000400040d010108400007540c008a1417030030001201d450070701903840880301030b5500140341806002d000b41c451285802610300c0e41d69910041d00101402459218980000c105403000500902d005004192140b51107580b11820f24000402e0b0581c1604039 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 303886978 1250 303885728 303885731
    0x60e040b0a15060e04110310081911040b010e100903060e0106050a030b09010612050304150503162106081f020a0206042904030201020d150f06050d14090601060207060201 75
    0x3040c404102c480c2c00e610644145040000c58400802c0100d40144005828a601d041c0c020090100200040607294103c450510440f0240384200710400011040e108004041e0185c0c81d006032418202908100d844c010141403114803581c03640007241602c61380e10fa1400018600d60418801c10007039206896442c50407038001c204441c2080c0100d52415068000036007008500f00001e10810b9007508110040e240e1200030318203901d500e1400781d69a03005402290440785511001c0d44038140b140003038030711810900c2c40d084402d040b07048094400c0d0030518404803420001010000c1c80e00d83d28001c0c48028100034004002140310900700040c10688802030640e82d0b40100300440c1001c0d0300144658001c1d130080d041003400d061b8680a000000034558500e48482814000c01041c9601036019203110340c181d040a1240c8d0301c945a010b0784c42012401201c45081c0c0811003804558414405400454907003840010720085010481005100403100e5204680c040c400520090303505104010041466000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 303888228 1250 303886978 303886991
    0x80901180201030f11040807031101020c09010504090c0b0c030a02010e030a02030423030a060207150912050c121603022506080618150109051f0c15060e040b0a 70
    0xc20040206248400380c10503841d10348584405a55902800013a1001e03410141da0302c0da42c1c060b05807a89164801550701d0140d003008800b0950002c10304400100008000d41450303801c3c281040010481060141c4049084500c0030600f400c50070300916000f100d41c0000c1d511021401e5000382581da03400c000c03204a40040c07105d402500d40020545003a282d90703024032240d24419942480c1540750001c40d1305e9151064580c0031090140503070080c03400300e010b00c4481c9905020240494181c030034550006100c00c070354240c01451035103d1310107017201000000c19215a40f2041c040c010702c0f43c1000d8402c00001c0e000300356a40403d07404000011420b0410b60f0302d2030150303481d0440341c0441d644901c9500144060b80000a0887e5610720b0407803072031141c0050107140340c2040158103610044864071140441d05004012030b01d850180450003548488007507102c94210070650071141c01403170740822248041070000211001f48180544405803681171140642c07441d040c1040035107604007a041044a5282a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 303889478 1250 303888228 303888251
    0x6140a0e01200c1c03050106080114010207060e06040518010806011238070801060320030c09010c020d080705010c0c0f0b0c0c030408100b010212120a0f06080d080901 73
    0x4404103050b0000542907103e90240628a041912240709400340b040c413800d14424607500340e0b2005058829135520080642c0c0c8452903501034481112805015a1040030204032080c441d2081e50601c981c082c00481c1080c1d039a201203902c052405800c0e441c0304a0036001031007895030400180b4010a403c0c100280e1000c000c0d100c050900c040140300c6001c40302c0c40f64001e100c1c441210080c580d8100915420740892900500040c00300c103003030080e00c001030b0800c807010444041c1c885e19a040400c4005080c1d1031138440c010084042d9203d080b4050520103003460000150f0f0f502e08040407681c0c042c00b03003071f9560161864000d00711010540c5050601004207154030204462050842d142d984c841c0b80e90f41c05480d0080c04980034000c144c880ca405101c0054003142800700400e640100407404202488910303d5540103a80f01c0e00c04980b2600e94040c14040b50320504a81e1100d19040324000400003404240c421f00c1406031643c40e003080c42150701036194a214107034400606a800078414008001901750038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 303890728 1250 303889478 303889511
    0x409060e150d080903030403200907020c01141c09080d0c050310090c0e0a0609030318140d030327110d0b060f0a1508040b0c0a020303061201020706140a0e01 69
    0x140b806052110007203241c500984003081100c01442d04210f1256410100076070b0940c1200303c0b5080c6900a1030003901048603d40006038420314000161030b25038418980343c0c2240c0c00d5030030a07440c043e00c8481040c40da852062051140c20712850140c0603080d581d01d030001076201503c01000d04041089810010050074541d0045c07107109071042450041881603005100701c075400c00303420440798030209422000424a412445040c1168400d0726140f0740c44803041d10280d181801303031140c0c10a44441c20b8450610b481c2102c20b990015100341400a810040101b440360411185503600907060031340c3c500d0106010000704103190b00711007240c105504600550300c0c91441280501101e000d070030320380682c0d601079030b03040d20541c040c05410480429804420000400d2400305480640b10040c9003c013054024070040c0447e00080700c85d800071461621a20140b007072003950300c9070b0003046560034044540014654000c079614020130800e90700480c00c00e006400104c3d20110819000da0380740002c02c01d984c0014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 303891978 1250 303890728 303890749
    0xb010f0b0405061204231006050904020609042706060603180302120f1e030f070c21090305060a0c0207050a0e0c1e040b071104061d15060409060e15 65
    0x6042c03c52030341791407501c07079250100101c903484540c520000d040c400050001d6405074070854100c05004c0a80c0d100b080c0f0039400410356010350010410032502c0c2441c00c0540203c182485081c1c4400800407030604031480000c4480384c1107900707a03194801003091660500070000306400b02a102d034845590350b178000e5607641c0300400e40703000000c0108140c40480340000030740303002400c4a0321035103101154a0390703580198400c0b0f40c10f54000785410301042c45188600454000940d03c0801000d00d102200344169903004110450420400d2128001c40000d400b0322049005010b02c1700041420300050700c01030b042c42c3d89a00b085025545080c003c101d01c555000180350008180c0c0941d07030350380034505030b6000ba124003040d20361065040000c0004407428000d0050440310302803c0034414640d80b10040000b9107016100d2004484a4801d96245c00381c100c244841e0414001c030000140c0b02c29003c085050f0b82c105500010752190303191410418400c0c1c5141043c0c0c802c01d07440e024400000403d001907542c451 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 303893228 1250 303891978 303891997
    0x509010503040b060f0d03050306091008120f0f160b06041104121110020a0c1208090103050910051e101a0d200c150601051903060509040b010f0b040506 67
    0x1c2d83d00880c0d407548030007100c645aa100a4200032a01c2210300f0040c125600c1a554540641c0b841d800140124800404010668605001600d46654080024841c1c0e4121407090203003014100f0504041d201039000500006074100e10512031000f00d801c001b8549100105041d00407403c0051035007200c80300c130b01254150341560800c01525030107030070058440c2c0d14900b100b90308103080548080229800240c80300c4c5d040d100d013840300744045c2c40d0781400c044540d001400a1100c5014441441258001d41001740d102d880807040303503550740309107054409503402031380c5840b0489104c2d441d09003101005400141c0c0600c4540444228508e0038625994585102849007086100031070f40c40300c66403982c1c114480810f003402040050009403000100300754408045002c29208441d00510364121140b5800c0c8980d005840c0d050800c4407119406032520750b08a5035600701966994007161036a03c4002482c01071b0b000f90310094182d8185403c9480b00061500540200c0301c0503c0100315a94030a0126a0101d2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 303894478 1250 303893228 303893243
    0x15020d02190e1824190e070c020306011202010c020d121403160c0302121306091203080a050910060e091501031e0606090c020f0c01030c0c0209040f0b13030807050901050304 76
    0x3804105280e95601c07001800d0b9001d0310003000c520305103411042c41070503520103814001c0720380c44054098402199230300009405d03420420040201c4105030f080755a58030b0040c10040d455140a0b800154080391100080381c445022902d141181070f480501610006028400103244d410003a4482c1044041201c4240801c4001818181014402d10115008542c058039050f142c0b074659040d408454a85d005078000544031000001e1240c0c01c03000c83c15046501a203440125803030380d681003409018000c00148042c45140340081848240780300f844000c1001c3c1f4244600c504090b410070307090000c4684820160900702005102084800405503980c034000d0f8441811902c03a0328100d00035290350307444645c1080c90615006102c81d00030908000c2c034159441510f0702541e03108010b40c12078100321903940014803800402001802c082000e59003090058030b1202000d003050b50781c488402c001311071240226100920704010107402200c40380d000900e6042c03040c140071034600002d186010060000d00b0780c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 303895728 1250 303894478 303894511
    0x507020303120a1104030303091509120c05030f0f090f040506130221090604061d0c010c0c0e130501050109060e06010c060b060a02031305060c0a15020d02190e18 71
    0xf5941c80702c07441256145089480325500d04014000307081c0418250b60798900e00e00c214808131954840c1302002c69202e4282e120781031030081c040b200b0948000089501d071104110359888090304101030020441049407980e0b50f070422000f80b0000c014107003041350096060a0a000b40d555a56802d000c1c2c41d02c0702034005032501c2c03180042c98081c4000c44c01c1c4040341c3c0310000a02920750400300d040752140e0301a2400303001a10805034010b1580030000c0243c002078119411006e215172051000003003e42c05240d00500c40341d106d1404070650841510a1681c044e40c4018460420400b801080c1c01081d200c1010081307180380c44150035544100802d0103041040a9100b581001101e9008480300380c0050400c9440d2482a00e01a580c0d50050300c00c2d106240403e4030016861600e03104485101409402402505510756102a21200e00089001c6060780900801100c55950301c0070f881686e044042c00c007030305007507072402600c44040410341074001c40050162100f0315541651681c1c100300d0580000084 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 303896978 1250 303895728 303895741
    0xb12060d1a0a060518060102062e0611160803030606030c0c010501030b060a081609150801050702010b040b040902150a020f010f020a20060103031209290106050702030312 75
    0x42407080c0c14015180d400d110511140c0342080e8000700070348074240c5500107503003d4807540c0c070010340040341e046005074810030000e4407156005d9030f0b108801c080e14040f0140d0101d4400b0b07802c81781e503050700008009011590b64640c0c1c2d41c020030058081c00400c400c541004c5081016464580c400103142c5e60050400102048210300b04004440030042100020070481d612882c1140307001c60f003136070028450758440700003084c0d000000c18075207000d503903001e840d2109a240c60300a4001d0400104088601e10b80250000f80d008020701465215102e19800020301c800f154040000300c1e00d0441c849030007989040c4001005896a65000643e4a86411280c1c0c035040714090880ca840d810260b2b0340802c0d401d142c103488082001d90041d1050034071a4540e10906d0422010b411481c00d21000c800b140f6074040382c0104040390040005043d26080e10001051840c5141c070340e06011400441401000394180001034403400078150014050b009504d0820b01d80380d466000a40c0d64011644690242c07204078011a00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 303898228 1250 303896978 303896993
    0x6030203100306022d0a1d01030b030d02070302010f050309060601030905190b0f090321041106070b0f0609011d0c12011d010909030c0f0201090306060801020a090b12060d 75
    0x2140d11003002d65980c0501358485c40c1658498400103c14242229410343d001001130136603180008540e0385039040890f1090314111100308044040c113050381d880740c81d10310f52008d014a0360286001c1d00200001d41c0380d0320006004d402001c481c00108035061041c000f070414041391040e0000e82c24079001c41c03042c200341041820b03e45403640458030324448403c1441000a0a60618840c00110380001c2c000d40e6945e40003034503442030015002a0080c586040880c0c40501e907002c0d50000e01400d04010801e82c8000443c2d0b82e640483d2081d00d0408140040040880040764495440340c42a0380c0142103500d000e0341c500f244030094003403403c000f03a160000703414900c1d1501a15215040c1c0106c403440707035039030381003003814180b1903001c200c00059042c0000c5a4501d45000d21800301b581907131841e0507800141c0700c514151903159800c90400682c0304000000c50414000d600c040d0803204001656285000d001a20607241940002e0b2001c00c14003540c10500003c00310190f0240c0140d41440103910946030421 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 303899478 1250 303898228 303898261
    0x50f0303011a490e01060e010302061e0d0501060c1101021b040e011b09050108070305010320010c050109230703020a0323011503030311161104090b040f0b1e0106030203 74
    0x4107062009103424201c100c0d01c0e0004d800424005000300200b0b40c41e070010003a0300c2002d00020b5005182040b41c0058614034901280b00c0340710308181c83c0d0401d29026880c0d01503810030390200000801000d1070b0428840d242c40080c2400c04240001c1402880c05440c08001d00e01142e10306204594582122100d84801c0d040380140000d002d40c642c016044909000c1e180400b0360040701d0015141400040b1194081e10405041e280c2001c8006102151980100c04007418a0b031114100010000404001002409440c150038842c0a0f20740040d03001004d0980c1081c1b440f010f454250340009400c0015131070740c40ea8082500d401c40d400b9489048c0d9565040b07410301a00215901e00e600e0141825540100100c103034040d02e2080c1e80c20700180c0321021500d0b045000b00b0801141a0000998440000d84800c41d22429075030090404a2946140c0d00d900d06e402d0310032074060b54080d2120a04c4000c011280c040c179a0b0120024000b42c9a23020680c0c09071114030414002e0000b0700d07600002081d000d40316001000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 303900728 1250 303899478 303899587
    0x12020901091703070c1d04200301051302090c070305030a0b031e0d02073c0f090203010f0e09151902030702011e110d090807050f0303011a 61
    0x100502c11080b1909640c95005260a549a038200040828000c5100d8026990310701020030820325521a901c6504060010704081d501954610f0044400e649003030240c0352045400014100780c41e8118018171004000082008c10b2044003040b0990000e500802079a411090040c000607105020030042440e003c071000002c40602000e10020034005030004004403204c400b54281d40c9451ba65500c50100780800c3c558040700c05d581804d81c006103000f1074120074440d810b000e1042012913603c00c00300a180101e60010051184c00000601c46942c502d0655402010031001810052425005998a803286450006401e860060201c0c00c05040c203903a1180c00e01c1c02c406c04650301d0a01c0c1340040c0c001c08902810040110502d150284040024400d0702000795407888030a03d8041594440c0000304102c0d1030440f4811014031110b00071980c104a131504c00320b05003000316500c0d4180b0040a1840d5800500041416420419810b508010301d0444e04d0000000c03506281c4428100113182c41920305882d01d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 303901978 1250 303900728 303900749
    0x90c04150e040c05180a0c03060b0f0c120309030a140306180411060a030c0e011701090e01060803040308030105031501051e0f09090615060403050706050a120204030b0411040c1202090109 82
    0x5c2c1e0701e4995a0300411402140c40f008104907890300d03000240e0a0340c000340725042c000304d070a01040241031800310091500614820690300c500380d04194110030313a0000c0c0d0b82a6015400828071058403a0050b041c02d084d038600400c4141149002000600040c030700c0082520000d10703400c040b9003080300c0c085540007a484c0041190b13407102801034000b401030610381705010000d0031240080300254002c84400900f81a000070030011a800e058025002c0d00c03075044289400e40d42d49100050074103040c4050030266202e059529500e5140501301480c0c00500001c0d05003103100100100266960b11501e031890826040c200d075003250b11100041c0407507107031700360054200c1a15000c0184009010a4a43c8100c1d041c0c070143e281506483e0034411140a540401080342e48105070502c42c1d14062009015101182d140c50868080f1410b2540183d800551048541d5403550051108011071407015109d4803e090760104403800c103070740c0c005106000f007aa410800c0750340042c0300c1c00c02da48100310768805130181111 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 303903228 1250 303901978 303901999
    0x20d0c090510060c02030606010f1b150b0316030b191a040e01111e0c1c02010f02090d02040903180f090507020307030212160b01080105090c04150e040c05 68
    0x3020000303001c003210480300c01140d4100104485000c0e80341340341d5041c3c0260003424140d60f841c1c015600c500014404505100040c440c15500e091214551440c19200340b82c003941040b407403d440002c2da80c500c1100c1e4840d0304032400c6502c400680100c0c1c02c080b260010700031203c07038460710850340042c4040e4171041351080c00c210011100b00f00800101c4804a0140c1c0e00f0403584d403101018a00326041c024181200d81000c0240c07d10343d440d26605941d40f81e90901e4054500600003400070f14102d450750020b1030501d0b401d0f607501c84032a028070400d1884080000203600d030902c0c040004d1900a60004001e100b107550365403880c01c0c10b12803130170b020740940a00614004140c4610a103010b06545125440d150b600300380002d42801d1010050340d000641c0b680003050311100ea060030b40641c1d0044013107140344a50054903c004140d07d8480c19000f8a10800000b0700c50501c800700505090640800f10f00032401c018940c06421046280c4000f04e4154440e070089940720b0f0703c0e03c602e2a5046034032641e030101c0e0814 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 303904478 1250 303903228 303903239
    0xf0f04080102090915060f1309091209050d0b070305090f10020702031902030a030c11060a170604090506160c06020f1c060302030303012112180b03060603060d020d0c 73
    0x14002c1900c1d000032126044c496030b482d910508503032001225590841002d20076105201c42e10000360464401d000c054441640c3c96084240440c2e035815000d840ca154541a01c000c0f0036040b00c02440a85000c0e00c070220755054640300d11400301c502500e40c104040e514000200901814042000d000524006803519020041001030103500216001d900c603004030b0844801000520040d04c1c407099025000e040940103507141698800503c420035229560030500c482015030b18000280065001da45800080d00d50306c00c1010741104004020301e000d5854688848007040000852a0b4410101d00054482150018007252101144100100168004110400d12202e40005001040030030440c0e450003d5101890f101943c2c01e5101c080d405410801c01030080603c825405940020b40074100d05511180799140400c1f8201400c0000005003c0c0c0f501710982540c804003000144a040c040700d05500b8640c00150403071002801003840341c000a89401c2c01c6444100d8507285184d00075034084100750b600c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 303905728 1250 303904478 303904481
    0xe0d0c080303180c1c150905031803060402030a0204110c060a0b03060601090e0708071106070c02120a050606060a021f02040311010507080901141318150503120f0f040801 75
    0x35101d25800d06007a103e070a080000008a50003420f4000304141d4400f1002c00402c02c5a401e1841c061745c0c41190120190740c4841c060040603115440b540c0255a034004410454584032186600540320b40c00c042d090002690b40011a0303070345650100d40000b02800d1642d547d075603030721034070103170055600940b4108611038074103038440f024056050717007a0746959590701c00468519030345001c2c40e4041c21001002c205400e226580c0964009183e050014222848610641c0381100407a068000210000840800c40c00e0410300318042c400c8034002010780403203654403161030f040000c00080c012000880c10b52141d600c208004119a60050529800d800429100710040d44c441d0100f994000300c00c0c0490140c5511940489078040d801c01860b90401c01803000465550507076a218144e040d0060001183c108401c800d0700b4010194040840d20f061814802d64040c1d6004640c45400351070880020030454034081501640b009060120a0741c440410021001c05c1c0070700c107900d2050701c2c004140801d100205 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 303906978 1250 303905728 303905731
    0x50d03080405010518061b0904091506210803060f0d050604050d050304080301151e0504060e061305011202070606030803010602010e0c130924150f08030a0e0d0c080303 74
    0x30300020710081c0d4420030560a07a0724034000040030b6074401000908440109600000d203d001f50a44031325020101d8001410b0f0307403400d5016103840003032501170029112284603440051294000d03120f4003a10020b41c003600007880c2c1c4800380c440580000010126980e00060624100c0c008200081041450030090360b95201110115018407503041d0190803d0b0282007a40d1041c2c1c1d119911500d140c1c02d080f08890000c040136011014044460801881d441e0075480300740c640c0c0c8480d40c1e010b0b00d03a03103031040c01020400f1149006008480400402e46004050b03100101030704c4080c04c00080c01c40b00b0180503002031003a4031020303042d00d2074050040104038074800214121003007030b802403042d5055844c8058443c42070040095102c1c4130045c81f030810252580280c042140a01d00006034841030b010700c09400c0c405105480720a03a50380c0b01030050307484000011005400c0e007814444000c1c2c1000c88141d6280b00b6070081c90203211089034201095a1101c04040107554043d400c100c0103a0780303a4609960743c10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 303908228 1250 303906978 303906983
    0xd050a02010f0e0f010e0f12011509112a0f0102041d0906060907170c0702121915180506060319050a060c03021e19090627050d030804 59
    0xb10440c900140c288250407003148000002c208061102000303005440b800e519401c49500148080030300455036070f80210380ca048580900020820901200600b00c81c545903410032801907207455083d03030b10030500d80195200035000c01002885104881d492006007044205105203600c00c0d1039102c44800019000783c03084800820304480f402400c1d0004440d03507032040342d038101a0391001000541900c1e1540c2c07084e4001c1024100b0030902084941890300340c210485141d0014480004c8250840c00c102c000d20f104042c080d00a0215400c021308004c007138000780c42000d00011101d03200d011044030f15034424102da08081030040114500c82c54150303102c88080302c0d0148a801091031900f94140304d20300040050368040090440840c460740d40c2c0e002010400c030500d0400d6420b0040c000390f503081d5800e110300c058500c80c00f0723078440c0301600104407081c280048100030801c0ca59010896150090b540360f12440405032011618010b16041514010982e070091323501c401d440307043c20107058100306582d02550 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 303909478 1250 303908228 303908237
    0x1603021e0d05061e010c0312060905090d050a09060e01120507080f0a050108030405010311040504050c07050f0c0a18090b0117010e2107112106180d120204050d050a0201 74
    0x5032500100705818600404c520050110020707802010b41c03040840300d00c02e074401d042400c81103c1d0700920b4012122560801e40a003942c800900c00420030800c0120b5600c0100d103086490000801c20040c0308032030303900c105030a01900141102d0160302804958602040681e0200040d1401c51402400c1d402c0170b488102c14588100c000c180c442e00c407402918140c594081c020752401e0310b4580110001c04100c3c030515030904040c04041801ea17100e009450103036482d03c02c0780e03403901c4003410541d0408242c00f051b039101d94070824804950b0f8642085490071209410661400d92005202036800380a4000004155103012030001c035001c08184080943c41c03202e04000c005582c201c030900c55480c03081203d2440c16903103440300248200504002480580d2185194400b401a0800882c0040000003900e541c0050600442072511004000d4607030710051210316442c550940e0034045854a40c0403020301d041018000b40300500301c0b000e4044400421002d85290030401c2d207070030070a490b01801c940c2280040d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 303910728 1250 303909478 303909481
    0x110405091f18090206070f0b0f04030206041119060206090114010e04080310080102030901020306120118060c030e1006142b031412040606060203121603021e0d05 71
    0x1054003521800c0e610303005980c05201d0360502c0909084504149806150103448038442030050303c84902504003180708846080c00f48a50f0700e8007600b03410004100b100c0d0b180e40041000042540002c0e502d030081e030009001444075000c03201180d009800000c2d001401041c2140001305a5400901c03980300b841700b84003c0018801c41584d0b020850400e20400281c490140046000b041412004680140c016940d00841c20307038840c00282640c01c1100c800006075070200c2000324506202070340036400c4400d04001c01007500e00c00410340c41110300240c080c00565640524503101800307980070044003406a8100c03100d4900a4a00c0006441035000f009900b8458584040160510020703012000b05446091000c80c2e1000540381c00b860500354050b81006104c6154035454003a400091881c1d9011102030031092405041c00b000b0b81c0c203282d01160456000f04105d1403070300619403060780c0104119000d0361201d043e410084020303008410805041004d00001c040024074840024000e02c0c5031100c00348021f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 303911978 1250 303910728 303910741
    0x70e0907030227030c0d0503070303140f04030305071b080d0e06060d060c030b0d0303380105180901080706020c04090210230c0a0b0a020703020c12030d11040509 71
    0x41e80201c0310f9040350314044034060724104000c501c2115580340c019085646111215000179040321a03000c0651701604002109030915601d4040e41a070183c201079141440c1c03c250708104100d140c024006401c01d550f44020031801e611900d010030703602c2c0410800c60302c00d1005090601c0c440c2d11050600c48910301d803401c0800d0031900803c2c020b2040702c000b0130320410304d40301c0e4071264003411840400804042c1e135080221507a58a000c100701020b806541c0006501c0d0000020060601d1180724624040000300b050150400145400c6280c0400c2071804688885902c82862660010700701002e9004140c9400403403a902c0008000c421110594200e601010380481403008441031f071a03000c0d4010381c0d10410320310064001e000c0061403501c40c00c1d80245109130000325100300e801c04c0c0b1880c403160308942c070381c41c040c415801c11864102c0c10b0700000f14542031035564003139500d607502c501d002c3c0100f50b500961348490a09005540c100c01c0380c0002400280741c9001c8002c2d041d4400cac0182d074420003e01d80450003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 303913228 1250 303911978 303911981
    0x1e050f0105150f13090207200a0501050d060e07050c0d0e09040b220c06090602030f090f0a120c050a2c0a0e0a120201060e100e0a0f05070e090703 64
    0x100c40c00500b8441d585002c901c0a201140d1011082000c02e100400101c814040351548040003032088540041e107408451070954000140710f409504000e40c035801c2c3d60003681e206c83d00c110445d6002d0802d030743d55041c1208040701800c9280c0c81b51101890150030040d81c10380041c0180041003100040d200c0c102c80c0c120044d40c111f01140709007030b00302c2c0d107071030000b0005030102008a410021745119404003480170024800c100b001004101c4840301800010410729800062880117800c0c14000b560800403c1048440e590090708801c0b4441d00b1142040255626641c8184000d0200e41180d110801e10a04000480c070b2028031415000394040d0b08005194006413080261008443c85602d400401d00390131501c0e010005001480031b03640c3c0c0c030440c21340c2c0c903020010301c15228490700340d12413540401a4041c2c00c4038141c1c1c1c0700c610308901078800c000030043c20300c4407c4190b420305e01290500c2e03160050440000e01c0f09140c000000c0303140009100c0e100ba00a45c05505088040381d80c20f502ea0f5802c0e40440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 303914478 1250 303913228 303913231
    0xc060711121606050f040e07090e151c0303020f0301060804020f090114040906060512010e070609060522090504080909010512030d110f0a050c010b04060608011e08011e050f 76
    0x4401c005241414443d0901c10002809407180a0300614101900c030140383e4600d072000c3e240d80021a80c4042c082000801c545150380d4402000300180b000d80e19000c3c0400c100c00c0c1d18260207001d552074610034508050090f4141c441000c05802c003552250384500c07015155080c1520160700c24440f101c00c4551500d04035044506036002c0c2180084904071400500000d0315404c9011203d25032180307000300b001c0d01e5120005040b82210030000c04d02a00c42180c0b9414a0256040070003004800c42d0f007800f04540190880c1d208041080352451803462608455500074915042486020304000a200030b01c14603502800d6480f030101d800ca40d40d66078510400110311150f071707000d9030113400a222543c3c100c1c00c01c0d0300c8004100041100e2501c0c11b1010340c44c6800c20b0f4490704940c408200d01240340005e0100c24407030031103406000d5404010380c070b082550107852200144a120500c80071890401445500184104010200000284070554080c007134a80310755031303c1080c41402c5150100082c502804a114103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 303915728 1250 303914478 303914503
    0x30201060816060804050c04020a0c0201030b030d020307080a0201110f09040e0c130c02010905061602150106120b01020307060f380d050a05071230110c06071112 71
    0x1c20b1024035141c0c050710711601c0180281da0368000d602ca80b5400340c8550006000501440c1d65070b0240c40103a20015044800c2c0100301c90280c0d005540d0050034a40000481c1c1d60030360000a2552141e080000890242210320f024030300c03070b00010425040044850000d800680d000b01d0307052091010b0060260f6a40304000300d01ea07030001d074a04070301c2d440c0007243d80700c0d0039548030503c00030502d042c0c41d03203883d0f10b0940d00307840600070902c0f54442020a0340c0d05100420030b0340c00d116403030395980d450008010009107894403100042551000c1656903a8001c100700c90f0b40035404001400403408000c50200101180b400e030406a10348840c10341d41200d15020030420422140740c084240024007024272220120582c0116050710942d1440c001181080290100801c204011012040e019140141181300d209100b20304800d881c00c10042001070780a22410002c0e2149042e441c0e001610400030300e099101c215168020310002810400e1101d016002d4289000c00c0e0396008002e5055464a41e4504491160 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 303916978 1250 303915728 303915763
    0x1101020a080c0a0e0d1505070503040b0606030703090219061818020901090e0a06090f020f03060103051012080d060506040509130c0302090109090308060909070605030901150609030302010608 84
    0x340b55020b5440640400c001c00c0c9402c0400c0305425021401d084900c80c0700792a8100c80d24540803800885000b420340c0f02c0700c14540181541025501c1c038005000c044c242911800340440000e0380360b0f100342c0c440300c45940c00811944030764a0708440ca1621103501c0c09610001582914450f0040220200540031280c000461461110160440e50020740045402c24100031401500040400d2440a07090203211032900000d1058135200e1640f00311550782000d01c3c136103401442041c80c1c140389e03082500d60002082c200401c050381d5a56903140f07058610f40060308101c6078a24008144500d91019102c0c0c082c000c08100305040c2c0302c000f0058680a07a106195201a1074000120070445110507000721500c5880210686c90712a03002400c035050036040402c3c002d0740d503d002030905a00661301a00400c090760121001d090034a4000d40310500d1740203007030600c0030000100b4290582540328801050506200c86411910b800000780a0202e611040c0c0056081400114440b540400c4240138221220701 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 303918228 1250 303916978 303916981
    0xe190204020f0d02070c0602010c02010c0e040c09090c0507020925051b0307140c0d0c1202010e030a06240e01060c050a060f020901110a0209040602070f0519031101020a08 75
    0x2000080d5000044070180c4410a11080c3d00c0d052090000c1c101452040310019006405e05800074211807603c000c1c0000c5a04102c080001c15400124648004c00184e50110740c114400c0710688500000e036000c81340f200e2510240c2c801c819480805482c2d82071085625071b116446201c03c08900d00d40d04040041c000d5034503922030a41d1801034000307160180b1040e40020703080141d110300c00d08680040344181d4844460131014141c650301071140381c2c040c0c041200d07101101300140c0c40e09600d100d00b5005000d00d5058010010040d6809584007107034001d801400c0700e05921140c90b055002c0e29a00b404014074107c145075019104200c5120003041c0c0d400a010203010b0b070320b00501260340c0e0008500940c0c00d4020044401d011440a00a055050507004030150b81c401c4d50000044c18a02d84039000e40c10b54100000d10001651504102e5400c960002000f58640e045030400a440444805005156114100058107000e83c40c001400c940c1d030080c0c540c7d0300e952000d1002d0900380c0c030407801c001c40090641c50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 303919478 1250 303918228 303918233
    0x910030213030503040807030b0c13030314250302010e06091b060f0a020f16030b040f08090306090a02150702010f270e06031912050f16080a02010e19 66
    0x34040c01004440c44a900d031a103540b07031150303820340e070082e00581003035002403800780148060a0601a00044400380803803418902601000001906000017820440e60084401c11304c0b80c010140d804200741c202e000070001e00990301d0303840300d1007801c070781103015508100201c1b91081001c14014880c2c4030b0403000d0f01c1050103507010001520145c18049921080a00044995120802c050100005181c000700f107820340080d48145051058424143e420009038030134400a01500002170b00160b0160705541a02106d1a00f1449070141040d5583c0503c90542000050f0b0000540e00411a0007501d050b810b0620219040010b4410076801a000c151100d00b42c01e02c0c0c0c0d2040e1500c03600102400d48041c2004041c84492807040c0c06644181c800c4c801210070306c1071925003408102e4000401c065a1440100d09540b00c00105074801c402005010300031511115a076082c0382251590154004031401c041d61600d008010703a080b98120500662034030f46440d444c00c60020300c00c418010b2000d1808075240d040d9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 303920728 1250 303919478 303919481
    0x801021e030604110f03041704060207180e12041e2615161704031b05030906030f0708130818040902030a0c05180606040302130b0d0606140402091003 66
    0x50030316a0403503900c264002030004850017030240c6000c00d00f8400e9403420b00c1d0409030308503c3c2100c0c1d14840c45508200030403426800083d2003048170001440000c03000f031360064034801052424040f40c11409040309a864142d500c80040c400d40da4100c504c1140d940203884d80142401d03040c0a80d01a043c0000c00d561620a5504101f0303a807845400129042014032040405014100751414083c1412001604141e160085450b10302e02d416442c211210b031801e038600800c40134000890300582910101030206200b0180100d40d1900405850150759003000c801c406c10003e0101c5201000560f4a008150b0342248184010384c00b03070308111050f003170107440c8181d401c2c036100381c1c03459a03842503484240b00d0040e01c041c808583c055004500446026181c082403080003440085030310800004c5804000081d83d0341400d5400340e94050340e19603145803002a07400001d0045104656004151500c02401c01c41c084c1c000c203094600d11003606601c0c00700002484181d01411041507840000c180c0802a0140309 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 303921978 1250 303920728 303920731
    0x20105072d081302040e010c0e0108060307170a060207080306040b040209091b0d0906050627010e070c150605030c01090303051806070f03050306031501080a1b08010e0f070801021e03 80
    0x10003c6400b0814030310350008007101e084200303122081e511741c0300034040c0c42e4110500070f810b400c081c00c0c54642c920f402400661211064000c12201c00020209002504800c00001c05d10980c030041c00c659515040c2014503054001b00c800a10480c245560410241000d009603020140040e1145255407200d015060000d180020b420402e0481808091007440c1180110010076010b901c0000741ca0601800340710304d8004090401c08890000c801c0a00e6146140d00424111a1403400da001e8545901314211440034884a01400d01c124a184401503150950302c008112a002c07007c844980e5000c8e0019a00c01d4070340e20015011030810301020050780c1e5600580150a84010400e0b86445601c0ea42c042c1d0083c0818401d4000807800701c204252414200100b8a80f080c4003580c0307000d00e600d0030003000e1303445c0240d0200508c7d03036040c03414500c00780004000d118081c0001c20004d000416000c403210340e441c480821125498420200006040c0c00181700b1205c014101010403070490b0800314941e9483d070700 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 303923228 1250 303921978 303921991
    0x907170a060c110d09030204050a0b0915030109020a0303020609100c05180d020603010609180902061902070905070f180806061011010f050114101d011b03020105072d08 74
    0x4106160f0142c80024402188003004949482c9038641c2540140f004585c00249002d585500c3c0002402060342d40049107640481911642c0c030100000202090140c40400002500040d446401004268001c520751340301d0031005084031841344000c80c000b403c0d45c100350215800314804000b4181c1d03103010404061840e800181060554000d240c2c041192940241c3c0301d4000900d5004041c0040d850840340740318911045401400348007105c0e00060100d1164044070507603114041041c5090170700a00035040100034413079003003201e03241030039002d01881e000d0040b400006503060b02200c07004060000b000709544010004005a50b42e000c01e01401aa211504000f80115900d01010b070341307801d004402c90314101e00004100c552400040c000f90710003107420349204011410b964241254080400c45580348850952846d0300040e500507500384e0100300080d919584001215818540c0540005020300103070f94400000c050b6008410144100321081808005070800003407410303601c2030015030341020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 303924478 1250 303923228 303923237
    0x12231b0708120a120204030507050f1f021f021201050105070510022709040506040b180a0525080303070309080f2b110301030f0f120203030907170a060c 67
    0x603141c1c0c1c655490400d50000c0044182d2000600b01402c0340d000080c06102c001c0c40d070095052a003140c0e113242d181c258a0080501614401c1c2c0e00003450743c0d0710030b4520704e02030030101c3c401268111103a0007500c84000c5007030603102500581180d014002c4c0d610803102080c5082d154040c0603400c1400440c0d207540030360340603140703486508807030513154215100400d0078405601c0c051040c00d1707011510b03100c0c061041680b40c4c0b150011030108004944041541d0b5401980155140455500c002000782025100c0304006407c1c0318401c04c90041100c001509500c0c14528400c01826500784028128011100e000750000340d0000d10200d2005070083c0c1100c820b46124681d45c500706040c951640603140c01686401d018210303410f0390001c07580d59090030910340c1d81c1c2c0b491003808882481c800007025440188401421807072070a500710117210440c0460015a40e200700480038030702070700c88000d68075041a1517000c3c5501490070000b5803055000c84a080c055240402740003400141c1e1168070013010002113200500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 303925728 1250 303924478 303924493
    0x103080c010213120b01050103051909080c0d17060603010810020904090605270129030f1203042001140d110d1a040c0203070b10050d12231b 62
    0x80010b280f2001800600d089640d003100c460420603045201a44818145072501c410712000c12a0007203c060b80c440e6450700400c90301094130384040c25108050801110307000700c06814031030941c03100103a540007500030032450058542901300040c5200a07c0386031029800015003003013501283c3c01a141d003aa0003000060000340a032210400d54008a4a10702d0f0441c4917045010050003c4084698103a00c040017040034a815004111000c2c0450407818048608800d00341c250b6503007005690340910382c0406580b20002d0303030744081c0ca540e0001e0702c0c1154041a01c445403003041f01c01551000d46040705960782c0d09503040400b090100360340080c04010940f62100d58094401d00403000604546141040c00260401803000c0700360328012140015107d0b60a10301000026603002040e00c0031182c01c841c0300711540e112481c842c402142d040e40065040541d41c4088000c5c070400c00400c01c0c0c054100c1d00c032040d1404c02480c45190038001d0251000000304203000e40c41d0303881c14003030b91103003915a18400c450701c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 303926978 1250 303925728 303925747
    0xe090d05090d2a03060c3002071b05030d0203030603120306030114090f1908030406020c070e161b020d080c070519031101050301181806020d06080615090103080c0102 73
    0x3c1c0380c2c4400c04a070000c0412000c10401000e031241062903640c0789480c0022121a0a0580380d102440301d00700000407011547d0541c0440c240d0448076000d920654143c800d5200c84004a103404261003614842c1c06010001da86040c008401c9a2094400030003810407001401490342244d08058240c41e0590f50380c1d0140764018102002e0580650070100c010100e000d40031024a10704041880f00000200b034001391007000402030b100780c0340c001d0342c0b0810151310b5200e550803e07480d105c1103a100c4c400f4580c0c0300e0240f00ba46180d01d40c503d40c00304ca03942d95400380040100080d201d4000c220794001d4000b4464617a03135002c5001d6a01800e020030400c426981c4250b0b580c00046d10305c103800c01a607401040511400c20820000a5203900515000c0c02c02030b095626202c017450f03c1d20280a426180540c4480903020011556180400002d90007401152110800403042c4000c00c0d250007604107520805c00402d1210301c41000e1480301000080c072401207030303003103580d030b401542c015044242d07496400380000c004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 303928228 1250 303926978 303927023
    0x9060608010905010b040f1503020d021912030206070311070f3f090608070305071707120501051e040905010b09240f0f100c0204050a060e090d05090d 66
    0x1c1c0b1405600017140c141034103001c201c00c45034601800c0182a245c540781000c00a0307650300b540116a0100c1d441001c049450021424100400341c50100704902c0307603030209079a018202e022403114029803c9400c561b4400381c0680440703211a0001105079018001a400110301c0341c821070496204035824449146c00701303507c820341e808904500581c15041404949001d048810401800b50285000c40c20207184c528060420310010340024101601c2c1c40000c3c040790f008203c40301d0b1082120110301c901e440d101900030300d6543d8240c403a41c1000d08281c00082d0a1801100400c600010301e28403500c8483c2c0c4070100002082e0b00c8108030382c20b5403102d05082403580c40c0c1802c3c03441130340c484040d510644540e4011500d8942140c200c42d1252000d12184801c0391110342610083d28801e030740c140500242c580c0e003541d600809602c0203501a06200030060f00211a4000c6411100c19051032296500c4142e0056215500c5100300c00000310107201c522081d181a030200c0d072030380c2e00400c041c0e50301d0061150700e0785 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 303929478 1250 303928228 303928241
    0x60409062906040e0c07060902030a06270804061d040507050a080c0703050708211014030c0303190903060c0215180a020609031518070f060504090906060801 69
    0x240c045900e004000d8142000019407207114007100c25914040c140071120450400c050040c0c00f1604001c01d03080c040000e950712182e60a40c008048031551011440c10314017910340030701e2078441400001166144520314200c55210280c0c0035606c01c0c20941843e8044076045e0000769441100c0d081200c101060b0380721803045074001c941654845e50740344101c0303401812000024006800d890010000000884e500109503200035034401c80d00c69940b59010301800d035007000b82d012810303480600f4060141c40102c00c04480704641215075841c0d403070300505040680ba51070980003907800d40c008120406c01310402c82c03010003851442c0d0502c0071940b45c0325101c110032101c074402030301c000d684031800c1c1080c044503101c01c140d48811a0174600200c080c1c004085604c840c032000009004040101380d5881035a02400078507414440a89210303441c1c0782034000b10340b1101c40003a09a906009424021802c109545c42c43d60540d81d0380d849140c03801c0d00d02080e13100200074904042d5462680c495010401e00e000380102d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 303930728 1250 303929478 303929501
    0xa0c080601030c06080c1e04212d0219081c1805033c01050402040e0c0108041209030b04030509010801050a1a0f0c010203011805090313050906040906 66
    0xc0c030369981140350003400081580c10850502010300c00b04900c8021a06c01c03661f240d41a0303090342e02064000450541075003d103801503051007070b101202d000703a80d24080c0310380032450083d080f440b50340d01d00c1014034400007240f102051111041c5650b15026003840801c164207845190404a801c03660707a001141840e090301045000d41c01301c016400603196000c0131020090030f080354220856032404000965030000707501001c442d215000080060714800d0040038842044044466000615071000300b8000c00c2c00b101d040784100c6ca0b18408401d44840001e04c4103a106068580c03140340e8484ea11140c3d00a1030003000c00b000c00400d03103070110004205240349801180300f0b0b160b80d6181c3c1200c41c0050882403050300706500800c1400c004000b42110b980244445105030710000750754a48614a50303000d03125000320300e000fa600001c000201a880084c046803200144401045035842c1d5000082e12407281c010b40280b41c0c0e11000d4207012901c1d1103042c450700301c1d00c020300020341114141e0341d00c4180c604907402c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 303931978 1250 303930728 303930733
    0xd0e12030c0316030c0804200a0f06080a05060d0209040f061b0e010804020619110304060f18050306010608180d0806190b0d05040f0602040e010518040f140a0c08 71
    0x60124065000702e4040315103c10b820305000310100300d480180310380e4008001a008800d281c03403400074180302c4002070410985c00741030020a6522826169484c510511a0800054503030b40050041d285610030180500c00007000b04030700103031030303020040c241d10094400e40e40b0340702806410001070018822910b04041324100c2e03814040d207200c0058207074001565154180102c1c0c1041000607a11030040f2030381d181d604180780e21200703d4480300b2640395052140f00340c100d20001801089680c2c2000292089a18941c3c0d089800d6040316802240c1c590544a090b416a1000d00140302c41805400c07920381c4616a41e40c0c9124002440b942545055808040b00d401b14261400780121800e00300c0024030904501c2c0d101142003860069200d50500c80d00010075031003a901c01c00301e0200402d080450301491b0304401c09540381c035201c1882051104003882910300c5111180d01c0710b4024414000000c0c41550461045220b00310280c031090321201c1c482000301c200c1d000c0c410a51000410740443c10010f0400c0200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 303933228 1250 303931978 303931981
    0x7030804060c05030405330907030b09030a050403080f1c1e020a0c0b0c120c2508161b080309040c020c150d060906090b030706140d0e12030c03 63
    0x1403200480b4015507040041120070020031011031400101c001d12616a5801000d6582c01044031070340103880d500300b00040c2c80c5050300340301c030400340020a401030b84d00070824185507840700f0602c143d0705d00c42c02e445980441c00500080012070f848001404ea00f8401400480c640079003614401c035100200e449000c071300c075600c0b0038581e4880c501500d800000d064412045181a10402005e84400740c0114010441c50020000643c0c071504081030701c400500290b445015402c1004140c0c1d0a03070840310060540d040d0814a0001c004000d84003602199000354a50b03141103c0000740c4115082001421f40719104044040c103d90850080d0381c0c0010504000555201c07913000040109a032403000403942198030007480c4000382d5642d680818417a0b4104400d8580c1c4606082c1d400b805082035500040700c041c0390000024446c1a143c202c0b40c402a000c82c1543e0b1101d840b81c809503613040c0f4140001070065030500020f15100341755400760f2110703000704046580300081140a514507074001c50321030042d04130200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 303934478 1250 303933228 303933233
    0x5030709050d060c0e041a0d0c0503010203070c173103080a030204080106050609030706080a09021e09060907050f0706090b07020a1518120e190602120415050c03040b07030804 77
    0x4500171024035040300c09022011966020424581e544900980f10348072260301e0302d04102529400304010308001d4001d640703d180440016008400070304050720214091695041448242000c54036a130034451605031000f9403240c500030507484a5240c480701c0b41210318011020400c0f250243c490b1030060380c0d01682d10750034030054a0a46000f903106501420041c810f82e601c1e990301142c550261009440c1200c216500c020100010b4840500013a421031009000e400075005004140c6440420645006625480380742c28080305038421144000010802d02a210007407002c04020a10341e2300540000c2142c0d0450740350401c03c41703010f0300c105c40503031f024902e1881000300d030445651502c224824204016503803405140320b44030010500910158100644180e81405140001c600d07400190550b200580000050840d41100340200300c094441c80380c400d94003803040007c0758150345002c9160942c41c626614140c0d110713040f5040e00c00042c0400d0001282e0880c85002401c82940296102c2c8454107250 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 303935728 1250 303934478 303934487
    0x50102040f09050c120c0d020f090a12050c1c02090109020409051e04030503060a03061a0405101d0703091202071a210c0d0c05030a0c0c1205030709050d060c 69
    0x780d10200b44141000d0400c9810200041070398140180c50a00c3e4217107a84006e1511810b2140c40d541c80142d901c04204858000821130117080082002d403841120640c481c40b00303012540c0c90141c01809540440d012111a0a1030b440e090f80d510410540f07410402c003164009007954a007600450406075002c24100134552081c0901500141c008540d0700c1c101005030341186181c0c800810140501c10700001141c007079103910405074000c5820a10030025080d032a01c5ca01c0b5a00c0d03240407031911039030816011032000c3c14186005400ca902203903080504081603070364004200c10007003032407080c1607440c00101c01058031200920040803160307001d032105606000c0101900e0408180701039140d401031201ca19110044102c100c036100759140600f05554810440485a1082d1031700100164281090481c00580100c0954003401d1070741018445c3d44840842101d51440d082130217480d1601c41c40300503200364000d41c015604024680351201c0807940703d40104a6131910b0f4a0216042c0e660f03084c105e81d100303510 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 303936978 1250 303935728 303935759
    0x306031204050d060b0f04020c0d0e06160f081308161d0601050702191202010801050607050601061d100804140d08011701090b010f05030601080a0302060a02090d05070305010204 78
    0x159841d04150400c4082061034519810003000f003662a040d07820113996400400f40600e4000340103540d503a203e2801c447d203c1e0786030b0780c82c0c5021031901100140589403042c03ea50b0f40340045007039210300701400d0300d0f002c0681114100c181c0748540b0401140c0e01d1807400c0c00800d03000e00b20f8800206200141e06802c00c070054225809140410440f54000844140b41190030750010300c2442c18a448588600010b10350101c81c14580403004a44e00c030006a02c01c1c00203c0c040b586000340c888078002d07a80d80040c002684078014000303003107400150052080c2030003000e503240029078006200f41d0095042000c69407144600d1035250104260f41c0c104000c200c10b0748103030000c500f030080141090500610b40681708680600450000e9040f01c4002001c5c480c0c01d40c44039410030b402c0440c501455a540c054100d84130014040c080c001e00683d0000f0131300e2080040d510300c200d03a06a0007030000d69100d1141070000c0d0051702c10241e1003016a00c490022900c00c0204030040c501404c0016640ca1900c101203200b03404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 303938228 1250 303936978 303937003
    0x90f170c060f09060601031a0a0801050105010e1207062102030703140a09121b06051006090605030f0a0209040b0d2f0a090e0c1e01020733090b0a05030603 68
    0x150900704a9031140100d10145c01800a09002c2902d50a201c20610b8141c803010007550803807104000003074040415003080707040f5a003c4c2c9404040910800174815000324140b403a114607400041d08204a41c468507421441c1082100baa00c0046243da10440c240e80c000d88400c40001c1c0c940c2d0f0944050704074440710642015110700f04100e41005907445458401154a070b00b018440a1905890340f000b030860ba10702c125034403140c100140d03e09a0302c40c210819207405103800180f07107441c001c14030fa4090300c104d9008003007007900c640031a5034265002c0c029603c141c0c981900541c9032124402c05848100b4001c00b018070030850303001420320900c580d04000040c0c111208294214018120840d00c90b4001001510207030400032a007440300c1541d452600740001e0344281c100b68500608a24000f03103018140e07200d04241c2c01d640070b8950b286a811b11000c4101d0758241242101c03e1143e181c411110294001400103050207250146d903000d00740fa15070481e00b008000701d0400000c1110515040c410030070401b2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 303939478 1250 303938228 303938251
    0x504020114120a051f060315060c08040b0c0a080d09060b0a050f010c0501021303080a0201052401050a030603150f0b030604030c08031e04031d0306010503030904090f170c06 76
    0x240c0002411140c400076045400c4140d0714001300b0040904510f4503030f02171a0107048840b0895032600000d008000b1480000c4a506080501080c2948910715180b0702039000b40e030780740c1002e0604407611280e40c4400015410391040743c0c0c0314000101e03143c010385205560084005111112400e04034251540c81c0491440341da2010001e00c219915401034179110142881c080c54014451f1400b140244910b0f000c0f05e19075010404004100500c442c01004018040d500a110700e4540d040055450700150f0394880e40100008800302c81035205030080c101004440c81e021480c15500d8030b0ba4a40e242c0707a281400440c0ea100c0710859029050707406550719020041c0c0080c002032425450082000110300c0008058120020102da146640c07001540c80401d401c80d9100300d07504091401412040600b08400901c1e0035040b041c0d9070520300810340394101d07607000c6c0c0918900711807401000b000700712902c401c60b0740751081c0040a01040c1000c0300c2d85501d510362113406079a020052101407808200908174031044 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 303940728 1250 303939478 303939487
    0x11101110f0f0d02030a0603050d110705010804061d07061d09010b0702031f05060a1d0c0307021f020405090906040305041a040909030f0311042303011e0504020114 72
    0xc94554121001081d6051080c0c2d1150498115410540302e0025540e43e502e0000c42803112080b02e81d8041c0048920400031520752006010b002e4400b012000710030861608842d008101c036500030907045601c9441400e00003030205051450240014095080380b01c0c035840454207100c0f1a4111282e041e140704505070543c1e45c1e036000000a503901a050146038010032001c6000c2085480030441d440c4440d43e0313260031020801e5104007041c01808100ca10501c540d296860004000e15542c0c900c0030011046003003a00e0540c0d40c131100b101c0590010384120210f20602041ca201e5000d059880529403d0b60000540e0b00c620348801c02072055030190910203290881e0080c000005d4010b811034044031603000354510180d02011302c4000c1030240d85d000d80003c5086c600403400301070707000d40444a1103030591420405c8100800686903140243e0007201d16001040c6c40740040201707512030988991400030300108901120742020580341054040f5290301d29190401e001c2190303003240d0740640c0c10380820b45c481d080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 303941978 1250 303940728 303940751
    0xa0309060f0c140f1c0b1e0418030c06050402030313080a0c06020708060112030c0c060302120702010c0f030b03011b05030a06050f060414010c0209010f05090a05270f0a11011101 78
    0x1d071188000281c5c04500d200c907950208441900300c2200310b14000d19002c1c0d5103034a540001c45a0488841c224071640c64020483c1802240708540d0140b5905a40e6180c00c075161551480000e0402600a9074944001cac003503200401401ca8980b4081c114200c060704946005103440c203c80d1840d60451003c0d07421015060000c0040000c400341103462080c9008400c00b40ca0405550000c40c3e02009048540f000c603010401607056001042c12a1412400541c6940c404e01d04900720b5a05001400010300c000050866a44c8280c000100744000200001520309a400801031007040900c0c01e44007158021040141c000f9141c40782100800302030340c070150f104020000007a101d200c1d5001d0040c45800c039040c1c9000740d9110304050526580d01509044240d43c4030764003118855058840c1e28860400800000d81c441c2d601e000d098003401039000800001d4510a03003616140f03004040c0c101e000e200301c510100d07041004100c48050b030f90044000b03820b845074140005014010010203c0b8040e81031a281c203c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 303943228 1250 303941978 303942007
    0x209040e0c030d05071502040b040303020c040b1011190609020310050412050711040e03220f05060a1e0822050d050903010902130e0613050309060a0309060f0c14 71
    0x1c3c0c0d15000e103404d6540303032201c0c07804420152010340820f100e03610200d404a203024204005000f170300d009400300d540d810314003400c002c1550100414a50003501204895007914084e451074131074642c204080c1c0300d00c22500d01e01004151981482910301d25156208035040d0b0800b84120188000c800c10300780450318141d241c030140002d540301000100080002d00000703008141070000b0001d14010014002d404007910003a40c0c94008410003520b022034084000c441505218183c003c032680e9054a1900514000c02c0000c1904681c03520320500103500049000401c00c51459600130303400c1e480e0380056003006c004031141031010014210f002c60400c4d03954004910700242100401d251803811b1381e540c42800c00402d024010402c2e000350054050800c1c0e980c00000b0360841c645071880c03281247c04075552465045910b0303407224006429500100701710241c070b00f840002001504250f050201d1a45116034604088a07003409201840c140e90b544d403101c0780c0c0d17030005125211074411003501d402c01c083c5041045 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 303944478 1250 303943228 303943243
    0xe1b01031104120b27060108010e010b010e040b010309020306070c0c0b0f09040c09050a090204210c0608060303070b040f11100906030504110409030801060e010302130506130e01090209040e0c03 85
    0xe00309031301880010b1041010200194149003515a0050a50880c84682c3c0c3c0d9000c0038094401c09500b8000d1502a9110500c81d290851005a481102401400c001d00000303218083c0d082c0d04050722564100c000d41c41c2000580d020b040e0039030f102038a0900ca814640c13510716854100d200360183c10414113030a20100000e84080807000c81d0009041d1038024010380f80c005003541b0013034108002000005000244e0f5011f0310450f440c0d500a00d048070300001c03059a440351100d40082c03903074060354000e000c40e070b2090032540d50000002c1d044a1404c50700d5140c00b20000c40c01c403000c030703104902404080c080207502d50342e80c242600c0a944188070700802040161046507117000d580101a5144009018040000440418134001500401c0080c0c0c0d6418002c01e81039003401901c0c0847c3c01c0076826490b80d4441c0c070072601003650003520380944034207080070001c4950045e00c441c103c5107420300c4040f0302c0070110801103001b040507a0340169514524402d000980740e0009207e5415000500b000c0754070b450110740103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 303945728 1250 303944478 303944483
    0x10050109140f18010b0c0c03060702061611072c060906060708070602030a02030f0c0301080709020c1006060302040911040302030a11060c0f060105010e030105160806040e1b0103110412 81
    0x10280440080c0c041541c01d500507075610b0f034481c60200005060500c2c18020007a61009806840f4110034050a16a031007a06075104001070f03000340c002554014083e041c04048107018a441381803118403800503881c2500903042501801c0510010708840a5030140701180803160700045402460b0260000312102c000505090103050006284410407440c402210f5501d0340c400021522030600142c0040250402c6075180b820031103941c0414443c06100051700d0490701001c005000950900d9245006900408000c00300b03031140e800f9880c50b200722400b620000e03081c01d0340e00603110307407901d00002c003942e1742d0000880300c08000300803d001527200820b44001d016000b07042d90490140d010301281241c4100d1058400c24000c07408040c400e00804241c1d141207030002da0740c0320720b41c581205c205801c950040e038041c403520140c40c03e00741265005d0b581e4564002002080000c1081040c401c95050425049820084003000c102d0400d00d503030544502103001e10581090390425040818083d05c161840034007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 303946978 1250 303945728 303945739
    0x70e09010c02061f050910081e03030402010509040b1809100204032a0e0112030e040506030309010c020102030405060a05190903050601030b0a0609020c03030a0c03052e1d1005010914 80
    0x1916041d0130444084001d15010b8103615161415014a194020160050304291b01135400c0c0000e45441e604101010b0f114618041c500c0c5450759030041d21580c2c010102190040d490340c24400b05561000c0c1e08224009120011000620345280550304001b8200b8401000070300c14441440820b8003000d07207620603101c51584010619a041c20030b02c09c0c422a51101c03508192140c0007180c40055120100ca95074400d89558903035441c0e1204002c25981f007291946d8040d44140400140c40d0710a03002c0c4560700d8010300541b0b2a058480020503941d0384040d20003c0410790000e14005900c1076007003007100455661520320700960440c2d071074903160170041c8005040c0c520741c44017045d0f00203582e52200f401402c809a0440d51801e0781f00c42c01d07841c6d4000b01c130120780040c54001400700d40d0340a07000700c42c1b040c0c10290102580740711012000211031071004041030444402c54000c901515408140f200120a4905001051400700c2c0c2001c01d40d60707140c212604225040c0400c22082e0382840081c441840100d95 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 303948228 1250 303946978 303947011
    0x6200a030b1e01110114070c0b06150304120c0b180616051b030c010f060602250603090312150510090e01050d051f05061504030215130314070e09010c0206 68
    0x500d9000d0091200c034281d01c08106d000b40148160009200f8a115200c3d80501d2440d54440d000c01c0034042c40240e503c1028081000000c0c0019550004204000d200307050008641c0b609488595080e0380c1161f1060210403000c00c2c608000700b0800c0003980c0061516682c0f1031888a412004100340145070b042c8481120b0001d142102c8101401601c1c806102c0200030002c0c190181508006008207208010160050048505400c11825090710000c41d50150a88255140010880c02801c1142d03090b000c009d19103050806401e600d02034440400e12845846002d18245010440000300d41144c4606010201508104c6541e01410407811581c0c100e5581c24a164030341000c0b410034065210300d0781005410031400c9043d86031903100320701643e400d0346d90080a001440503810507202d103001c00381d0310045071040380c92401c0700c83c0c00420a0740c91160145204c2a0b51740d650400c2d0f003000c800001200d801450050200c8a01380543c550710501e420003d001d02005044003a40f0740201401d1a40c00040204 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 303949478 1250 303948228 303948257
    0x319020702031e070b210a0203090a1e0b130c06050a091208041d1f03080f070309050307090c0f031a0d03030e1f0e06070203041206200a030b1e01 64
    0x11307800051180e040080e0382ca02807115900d20240c0064581c0050b0178900011500000d824800c0d00c1c420044000207108001181c1c540e29421a01044000800a074040080000824112901740200b14000b8040070b100c03420700c0d00e40800c400c640c00c42c408000c03051103040301059003c6140001c88685000a0a48210700e003004040fa1041e60030420426a0280c0d003c1c1c103400e50080090321410074003055043e004074010b050394071034425200117007251a050100400c03104200b401800c1340c62181c01d140410300d5441002c2800c19a01f035100243c200d9031441403151550304160010700303c03000741c40d041044940040ca07556104c080703004228080d000e2070640d0410107020340e00202110310391804070789501000e1124501800388480b06544180d04000c03900f040040d001440c00c1c00764100390044c504140c10250320741c1d00720f12003100564905403035403274004040c1c0140341c80380107010490082a580e140300820190548406052460003050080e000140b44688d40c1d0400420b20f50928158060080301d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 303950728 1250 303949478 303949483
    0x904020412030c0605010602070807141c050601030b130b0109020c0a21110a11060d18080405120c01020c010f110d090503060a0b0d03110a0c0b0319020702031e 70
    0x58002118181c203208400007816003242d00d8104041c4100740c144910780c0c0b41e401c100e0312642c1603ca03015103584080c0c1c084c8149040c91300d0010072584041d000b4a80d5410000411141100c2c6c00400d442c0d41d00041d0041c424441ca4200940c2d00c65000d00e0402c014691980d140a80c4941c14441c420115501003070342014560284401409150401000c907451500503000c0e00c554108002e036100810700c441c1e000c07216540c010076405c1c40950000e40c55250101900b080c000d07658401e040110600d503030b66000c00c164104d001e821403800c03406615100d80f210709190901802101c104900c10040d0f025a030790441c282c0c1d00140c1d070aa00034080ca00030002e00340103882641c1041d4800c1c00f0035490b02071000c490300c0355030f0302c0b40c6401e040360b404a00300c50302a100d000c0124102c61711083c43c0c9400803402c80c00d0002080c003c00c101615007005508070380601c40c007521040c802d644290000040c0303003800000d2010560400007586141c44100d8411843c2c0741d1141e00107541c90404000007100d1104440e051800107a00303 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 303951978 1250 303950728 303950737
    0x20f01030f090501020a020c0409020609010c17030405160632160b041707031b0f1e05010f020c0307020405250305061e010e01081f09090c05090c0708090402 69
    0x10702605001c11112440c21501030b41011040d9001031041d205400180c1c5030034010602040d401400652820b01848011181c0f80c50380c1c2c2081d544240007401244c008145c1100840c0309501400c0641481101d10015a2007241a40d12610804c500c161400110b500c0e0341502064a01170a41941525036040c02c841e0824090b1101c0d0b881ca0300d5009a0030024000ca00607a540304621402840710f1104800034914594000e0800150010f450100c02d907c0c0511002c030060302e214045c0c80c1c0e49680810b61744d5080c480d40c2c030810005030308086003600102000000d0040e4074000108030425400e200b010061240e99010b02c8002920032500c4002040d000002d10f1030003a030040341410074054503c0d222502801070001610411300503c0c0407150382007600d11509010709410816543c010100b54174400464400b40041c00e400c1482049003042000a8103001d0100014249048081000092030500f60140402030344400d0081420724101716001c4000b000b103c0c2c0c640d038445011600c074480d40002c10028060f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 303953228 1250 303951978 303952001
    0x10801111234090e1317070f080408012307210f090813051f050304110a12020315010605220e0f040b06010306030b0613090b0f091c0c020f0103 63
    0x50b841100300040d42c0c004501000d940340c0200c0c1000301e880d089040046810300100262111007202000c030350f510003000c0282607490003503941004080c400c0e1a5805154091741c00031859030740d580c29000d910107060221501c0740c103c1d4141c13000c942c50449406042054604031690198204d03800c281c40020041d40320030410744140c14100302c265072914240c0060340c000e002034400c803042564001a20715102608483e85405100400d41010452a06035030642000d0403c84011112040090154035000d43c150000d080c40d000c04c0d0103003851070040c5414444020381000002c00d10500501c040c0d600300c41201c03002c4582c03c590f80900d51781042906013000e0f003908140482c1046c003003030081a503581c60320680550301448138054192a44401581158698480101801c0d00c0c00c000508510b0300c0d040e2100c091094220200d441c50181d40d031400000790445540404555010502c041700354104521416074141003004c001d094070540f0050031415000d20002d204101c2401407100b00d0b4400d40104e680580c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 303954478 1250 303953228 303953311
    0xf020705011b050f0c0102060c04060f0c11130518070311010c02010207030b09060a0b03010e100e0a0803090604030f0c1a071205042102070e010306020d1e050108011112 74
    0x3041c0302e4490711002d0342c405c1c0b2401441101c2c0800d10354008841160300710b50036511054110700a04406403451000a281039604685803025100552a4060100d441c54516000015180350a40350305880140d40f0110105903807008505100080800710180040c000900709281003040c40d10040303203400c103541c2000f4000346004040c0302c2c121000007042070181c00035420500c010414101031508a40044025204e0b9034054640140e02180030360003140b480c20204282d4110400310307103606d803e5601c207803400071150340700a01b084140750303015030805135214503440c103420064115124100c010590901040748420501c000c02e0b505130140d801c032410340009440034402842c26040045482d609000c58401c041d6000075813200342c91000c078800055507040860003580d6404c50711014000c0d0040e40c6d51030703820b580e01c00e440d6507480001409002d858400d401c0124056040c1300560303003034580b041910000f440c0c061041c50581c044c802e038010785c00540c4181e409070242d0b0340011100061683d401e00180034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 303955728 1250 303954478 303954493
    0x10021b03190f05070506180c030102070507030b01050301050f07050d09020904031110020405061b070819111e060c0120040603060b040303050406050a120227010f020705011b05 77
    0x2001e005061210340c41941c4403100da0700c580395000c0c0c44900c075140c001000e507002500002c0711120030950380c40203419500101c65400342500007080c221317030051034142c5882e4042c04d0100100035071034450b980500420340003403046060400380e4200e0b50f440540054140300e000b2038100d00c8552554056400560024a504031a040505002e407000c00d0740f00c90b000060040003144a2440d105001f11421140c003d08180e01c0c240103401b900d401c4a00b4051a01c0313990040d0340002813845804c1100c038841c007a40040800d0340164038130b0b080318102021650240900c02c0340c0400140c6444a0a42402160080d1480d0782d4440380380d1442c0d4014250811110154400800031a100c800c0c000e029200b520b040b81c904211081d214601c81400340158407000b0000b6000704028068a88118064440b134001400c02c0d0400310085411601640c000d1622820146684080da00010302000c4504003079840030308254002d0285048025280c039014040c2c00d050084c2d540c075454100c2e2045402c1d100b8286c0007010b0744d028 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 303956834 1106 303955728 303955747
    0x304060b0901050901051021060617101202040b122802090a020a110f03130617180c0414160f0f18080f150109090510021b03 55
    0x2003001408e0041302045980302840a0200401c202091950500c00300601036034a182c80d44000d403122105025202c504c20011400362180c41201c0c0962524034004500984800311050350400840306844c455041c0110b4070344030030084002040307030507048146007032010039240c0d8000c1d40c4032120a010490701021980105102c20b040d041001480315500c06050030030308100c40b040c1d00760300006903002c0001c00c0c1072641c10103000e00c1e0038050401e41c41e4412440444200070308802d1482105103c080d4140020030400c180b20500030004c0c03140041e403815014500c2801c0c4d6840c403110780b68419180b86a0b00501c164441c20025a0b00e480064404981c00c84298a0010502a4500f142d11000c1001d0b80c05100d030032492040000105524207005c140400c0d100b03016030026048038034200c80d801c0027503000326554030b01c2c0c84c2140000d03803161211034900c0410309115020144030300c40011040075 = true := by decide +kernel

theorem cover : BRFrame.Cov 303776978 303956834 := by
  have h0 := BRFrame.cov_init 303776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 303776978 ≤ n) (h2 : n < 303956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
