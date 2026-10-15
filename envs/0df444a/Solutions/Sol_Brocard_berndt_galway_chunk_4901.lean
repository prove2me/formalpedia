-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4901
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:06:16.219718+00:00
-- url     : https://prove2.me/submissions/26c7f218-2f30-4994-b15b-74f2213f04ad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 881294964 ≤ n < 881474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 881296214 1250 881294964 881294969
    0x1150804080d0f020d0c020a0c080106030803180102070f060903270b0711031e070603050621070b030a091401021e03040c050310060303020c010c020a090e01020904110405120c0109 79
    0x103401150f88505a202c01000e88030b03d0107104412031900150035849580441da40030300a120b40c801d49125542c0d04480da0a8413141e00000e044058100045482c0c0024000b140301441c003000000350900e04039440308164411aa402039442c0303030303c3d00328400070543c1c404590840503030242c42c40c031031068641c4200703801243ea601880101d07580004800d401e004107011408400007004048032110071480c0c0c06001244a034035590b171400c1c400c041d40810f5280c007034000c00303104007805007c88050000d1780d03440d40c9000c03140301040d088901030810081050248034005501c900c5d41c03440003240c42c1fa02c5240c01044100140c110108507441489004d0031401e01a00e04440c80f4940c0e804030f80c482c3c0b140d003880001c48d074003540010341c188a284203652101c0400d0304100110390094082d10a0909020010340e03030554a641e0081d8010071250041c488007146a102101d10038a4000050034900c0d203070082411181e84200096400402040800040c9001034080d030740641590080d20b01e8004250010349030103041e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 881297464 1250 881296214 881296237
    0x20609280201030204090207060b032415040935210912030702011b030911061804020301180b01090b030f13020d0f2303030c030c0c0f0102030115080408 67
    0x460300007903a02c0380e0162000341c002034000b199038003c58980b000c003c11a0114281c0170f0b000c0c40c1154810160300c007809005020308220215590341d11112a1800b594011325296070140d41d071800c880c00b00c3c140720409003400310341c0c0807080c03d80b007030740345612511140401080886a104100d1640c0082c540c80d60a512101e4a0014600588880320054140038021001c2c94a00c4004010001c081c0e605402c902c0d83c4012008158490807041c1e2412001e443d540d907009019541da24401c0c014908080000300a58184141007600712540c00001a041c3c2e4401e0740513240c1c42c403540000800c2c02d09107108229603030200b401c0ac4801d02d460b00e5548002c9000050045e00f14480700000100302a01c988022403103a0380c002d146006c0b025261a00c003000200c0304000355890315119480503c200c6031040144900c0e40300100950171580c0d0450030240e5075200920516002c101841b003801010340800a4809a00d032407800540c507503041c186c0c410499001c20b51403000300a004000d000205045008442001641 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 881298714 1250 881297464 881297533
    0x70f0303091431050105060301030b040b0712090302060a0501150f03020c030706021b01051008030f28020f0f010b0a120501110f040501020f0c101808070303050a020609 74
    0x207420020b05000a100326a0150211900e903001c071a0940021040c46a100fa1030304104030398032002805001d000901000b050f020f00c01d40400c021a24210005a110360b4518081990100a07031034042603500b80441100035a001c2000e105009119004050162171082e0410300c15030408c5200a16501c1a00540400d05500090401c0804024000c40c0c1c0c100350000c60540d138507001d001d1340310b02c2c2e60001d80044145510740000f28540904850141003200d0407080114100ac078441081002d1340c1c0181c0080300306039102c1c4480066500c91038422200c1209035005085980a090a8582801148034141c80181d140c40346041481d13950407800d4059558450b0480d05806039480c1407801800d401008010105010504540382460b400042003070f240203030b0a0715401c100e059000382c4d503060903102403a0701495040000081720f1040c00b2840140c490031301c030702c0e03c460341c0d608680c3e0400806800950025100003a81c68216804000315504501e220009110790112508451241107510b40101e01800c0c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 881299964 1250 881298714 881298749
    0x405031b011e0903170301090b0d0302030301060e03010603021c1203090f240905010e0d0e0a0905090a06020307090311030610060e37061d0103020702011101090c08070f030309 77
    0x3c00c201c16005154041c405c513011004190f5480f180790000d1003409103a5080110b070a81c1d6040804c1a002c2c3d04d03515130021800c40c1d08000c002e03140d000c0795406083d0503660720640000503135a10700b000c10f240421b0100c2840c02c00114101803040011268541c0c00781410031518000143d16120b8002c0c00b1500709103501d103c036400c2c0708110306c0c100102001c100b20b036080426810034400190f000350b03411284602220038440b849031003611580c0c5003a0000d035020100c10340c01c228409054102c942c1c0840c0c2c0c1c80a48180c8040c83c3d0f2000200e13041511000001080c14200740108000b40d440603103e030380124010092441d0002c0070500d2185540034020400080380e00e0002961074980f00d05000500103120383d03100c00c00403c0c00c0d0350111a044460440780c0f0581000044150050304804400000c42c1e03401703000710003410019070103544080422070400c06450044200c442c020300c12409858400d20950003030a03e411000d5140c551340b6040503c140110b45001c10010f500409071208035085c011050f61045c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 881301214 1250 881299964 881299967
    0x412031404060f050a05280809121602061204080712050315010e030f0d030f0c03020306030d0e0f040509030901080603063102030d020d030e01150902130f0b0405031b011e 75
    0xe0700e01000c40a44d6111114114800108091f101e64405a5142641591803d014941d070300c60524a48021391010019118902040282c0307241e018009400103142c88000c3d501d0481a007011102a0345421000c220041003120907401c801e15071403103142c01c60660030020f007250364488051703200341e0501030030032814180d6032028031410740041e030414181d86400d00e403c034002d00504121007603001010300d04410403100601920a41c0e005d40340140040000b040310147c00d89511007520140b95010115070703032200d8260307124003c40c0e105125050103940c80b000c00c00005840c121002d403199200b90030420401000740c03415075a1400081c55824600807401b17840d003000b001030070354090194050103154000c1003116000600707503035a41c00c140d4041111301e85884e41c2e1401ca42007070041c0035592150340c07010401203060360054000b03100d00302c54180e08a9518840c295600d48103a2042e010f240703001c00d00700700c0e900e01406810b01000800f014210703440b4841c00001c010b034210710041030b41c00019602c02d0004a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 881302464 1250 881301214 881301217
    0x21609090b13050a120522030f030f02100f0b09090d1e110f03040e09060408030a020a0e10030510050d1a0c1303060603231b0607080412031404060f050a05 68
    0xa40d00a17118160b84844484002e00580c005160300880302070b40c2ca41100200780704082407040b04c0c0c0100c0c0360f0204018540d8111381400b401c0c000c403000c5225100e450301201001d44030b500314600c0c0d0440005440c40c1000c00748011100010005040c9400001c054501d45030801031b44051100c0e101034511180c0c0100d402654400d114003003200143c800c07443c44459a01c0d00000500544e040c80310880180d41c0d81040b0513949480440d4010604c1c282400030a4507491240c02914031003c4504099200c441c2c000c0214030100030600f18000002d40317810a203d218500440110003500c020341d103d4000e840c00b40c8034018180418034076800c14195007400188642801400d0390106030804902051850360781c24450301a00c010f020540b41803980d0303482aa5503480c04400b034000c4040300b00141050320003c1064882006c034070054240c00c50400c02120000030b080900500c05400e58070b501e9400080e05040050583e20541081502c0b803000b0003092114580002c05100411503c1c90031503501d0282d1041229203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 881303714 1250 881302464 881302483
    0xc100c0b0c030f090d0c032a1a090c030a15240806070c030e011d032d12040b280e010305060105031303052206021609090b1305 56
    0x40d060005200311041c94000640c000d228440000100340c840c0c030301c03841c0c4901c500841c24011540104000c00001d000b0f0801c0001840800c2640300c40020000300600c41407150b12045504130380406142456408414407581c001054400a22603210703280c01203036594010b0500540f42d261780a880c1c01058030343e03400101d950040032805110660b070f480802c68584060740191360b040d0258500080020344034201001409825650b9014107207110300040d5480d022560846942075800094070b1202d4070b01b00205060303890543c184e080c0d2581c1d54400000e1940072040244895041080380d4983d0b420210f040c2c13000c1e0390184040d41d6981d11030040081c00c3c44441400d503010000420f1500e242c0580150040203911802e80341404103030f4813403004442c5440221220380e080d107245044000441d22940147c01740d120805041c00a114581a5205501034641d100720016842218000101c26a50001c0e0001b802441402e2100082c5961501c1d00e0b03100081814031030f460010f0703440e814807004001c660781 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 881304964 1250 881303714 881303723
    0xb16061503080a110a0b0a021605160302030c0f18071e031b14030106030c0201020f0d0e1504080a0e03150f061e09060f240d0e0105090c100c 62
    0x45503249014441904907514110100303191a03042c600c040400306040b400070343c0c003100801b000e5803444840c600a400003c908103401070800e0b0742d6400990100000c00154000c0d41c003840c181440c41c41050710700501000e04030302a42903601032080580350944035200c40d24951035010081c2d9109842150030350044002200110300400f4178044168155000761811000c480420400d240008015501030103500b01130800081d08100421100d03200340c1c801014112035200152030714440ba0f07149032458120360790380440c044d40c0c0c0308510400e2104004001d42a0700034020f00c4120b14003522510202c0c0940b0b000340c018010812030059059030280003000c039402112500c00041d0400d0341e0941421002103031b0b140d0264040c4800c5d812040541d40954105050023002c420039513417030005005007403200c000d20703603041945050000c403484c068103040b4030080c0c0c2e00d18038103880d0009081040d0940f031400605400d0780e403401c03050041c86000880c8001b582002503450003521030902000302c903040c1c030540c0c0180 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 881306214 1250 881304964 881305001
    0x50d060902032503030e0916030209030703060906050a060e070e010f0528021216060c0e10020c0316030210081b04080a17040b030a090c050d0515100b1606 68
    0x2000f000100001060703034041c1d503c12114814520500150100507a00e9512400b006510010301034840e4004004550014080e624407a680c0d1741ca04c03080d18012001200d110352036004000390a03540388070380401000381d0f00342e4a8150170102d0004d000516081d001904103e944444003c0e0346002e40c1c200d41150366111440c145600001d110750003240601e00d01080140618a0040503188500c4d0594807046600303a00002641c50b0782c0c1e030307080003450084040c2003805084560030080e40d896182c41ea074030715100e8010307040b0314210004241c103100800c1045000e50841c2c02c000e002585030b0146032030101100b8200403103980c4904513503140e01b190324504000340540028011841d8100402c80c0d400350b6100b03901c814822804004803601502485c02080762241041c80000c4498007190441a03846001d40600f4456075200d01c0401d900e6400c019081d40c80c2d0340840440e40c03100c000081c80b1680051034000c408505424901c5401d154031802100100f0911075200c0903082c400d881d440120400300c03044105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 881307464 1250 881306214 881306263
    0x5030c040b0d110a030f0b060301050a0b0c160608010e010f0e040206090d0b0a09020112050702061f03060c2106051c0501060e0403020d0807020606150c0a020a09060906050406050d06090203 83
    0x8021b400c040301d103511940e040c0652081c04d41014020790707050300d0000740605020340c144071551040c0e4004519807125032055500c440e40c03051071205a080641420755a043c100c0d8107155040340441c01c1a40720400f1300329900420420351015034801a0025411540c4541d109116000070f03030700381524800904446607420900c050f180440c0d111030102c920030788480c3e03050507031301c002d081c1280c00448100b40580c200a00241801070a107106a06010507590801851503c1c1d455003412070702480743c1a07000c281c07071280c1400c0b03011078048500c40c09400c01400f40320a5041178042005a0320b4010b05002407001109a0810801d082d0045001f4105100ea55103161510b8140250f8400303100c120b21002c1815900031031a02c034408541d992052001515801d00a8422403088519a02245c5688184d0258031180c0340140e55030111a002010b1040d00418036a04181ca1081254020f502c05803040d450a0410410b41c1c89918844902507045500007504c00c0150020a08000c4400c1d900c0040304804000c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 881308714 1250 881307464 881307467
    0x2a08010209011b0b01090509031623010e0a02010305130f0f1209030507120201140a020604062d0209150301180c0804050303060d141906050705030c040b0d110a 70
    0xc1c0c40c981000740e035200326081e036261640c60300e9003001401900484100c4014020390702c40da04115008082d2404492816049094207495441d410408a070030300d10460403850540315900c54020307020440b000800054080101c80e90f614041c100c0d00030705041c4c58500040301c11226844c0050750513005001807881250600d407414200d036890800b140c00103450b1080d0302c180c503c0365540c43e080d69032000c010216542003001e441101d54220a040b8100101c0c02c11910b058100c0c1c0d00500f0310b003025600180300a00703162404405484203083c1d0000540310707000a100246e550848810410144c00c40016a200c400102082049011104064072000000b0000a210100308800358044011585c100180b601d00f41c0200e030b00007030075140035049600601c0460001e141000c14540864800c1600c3c4904403031910440341072552401c00310206505c44d516030400d21810380512075203c6040c2c0b6240e469031500280c03a0340e1600450044a80c032200100b48000000c9550f0300c14000142240f07062a20741001420 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 881309964 1250 881308714 881308717
    0x304140f070924050a03140c0a120201080117070603021c020f030a0f06052206081b120f06070f02031204111e06030a090201020109020a0e090d0206070203072a080102 73
    0x5400068040c0d0048207800c1012207410301c2d0513214024510f099140c0b441d00e503214030082c8521802d856001d68100c20804c0d0f40d9040300307540100604d007007082100310036000140500605900c410072281044410014502c0081001015610f1034140141c4516064040d800e01440580c44802076520000d500d1440c6045031000c0d500c1500c040c0400d00c80c540d102c0b140ca8041c2c620324405c0c3e907007220790103280b4880b1f10407098060150940c0c101c00058020ba840c0c0b074003031902041108040032040c00b040f81c000c4600b480c52140500c284010001e021008900c90695038811005040c0780401143e14600c2601510078021a00d0103071f6030030784403001c0b405c05051621000780801e0300d40d485800d0b04c410f07420700c80c500640c0110114030010502819590f40910f40c030050001ea4000b00d0455696a02c03807001079441407c128081e05a1000200030391420500c2c03180351221505960013958003400411446686c000200c400041c2e100d0036850154060b002c08000c03800d1512000418418084004181c0301300560 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 881311214 1250 881309964 881309981
    0x8031807120515010f030b01031203020c0703080307020c0301020c3f1305010e090708090a05010504150605010804170a090902220f030c150c051b010f080603030304140f0709 76
    0x103d0480c0d0b80d0300c2c0d429481d81c0c0103102c002c1541e100040100007180f00c03580007016100950174003600e0301b06801070907070406800c0d80088070f054030f0210622204550410a190815000360000c605d41044032160503503030702d0342003410352200c100c041c118011018070b40300a4071901002c1c500304425181703482e209105038000c2013100d420340d00c104800041c0d42d071107260740284005c800b0300320681d142c86003882203403005030080441880f4400d01100c080050005d1068a12640c0140010f040800a8802060945615610180c10445943c1c18800032452000f0f40d69808e440d0501c200d41c0d190f90211095814050b264003000c0300910114074811400d0301360100d658409150290160600d8941d0380c00c0d00007141e180005020b165018409015003200380e02c0c0c0010f0100b6078101410403003500d03507420340303048a0b03c0300d200600040c3d03008807401942c0200b0003600c1600981454402381c41d200b00420396a0100800280c005003401240314140306041c17000d61400020103065034156601c0340883c0020b0b01403031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 881312464 1250 881311214 881311243
    0x5030c0a12080f06040c09050d24021e070606030b01081e4207090e01090603081801030e12040f0f032414042102010504080318071205 59
    0x1039008481c0d446100002e109000b6480691181c0d202ea43c10701c0002d0520301050802d2045249000c91181d40c3c5104e138907401c0c1e1140daa4141c028540c200302c50002c940000800c45070f01d006010303441603201c1241c281c1c92040e680034012901c0d4000b5041500281c0a1903201612740810000082481140410141102c50049180f01011080c9000d601d948003060b460641c0d00c1c0b074006545a600640201c2c4022461071809150048407500c200c4c5d0f1090030200f0744058011480b0b806e410400c40c02d04030001d90051804200401140345903455001480c030801c40c400c03160941c4650450907607030080d80074040e084e1016086403203101c80b030340300307124554000e0044038a11001c0b650001008484a0006c00a803542320140314401041c6c1d04010b1243c0c1454011310142076110b49450301004040d4084500c5203004400380541d1000e000c118281b1420000303100c10443e41448104000b01d11035804481e00200e10020716000d202e00509400e0520b842c9800c000c4d42d05081898080503c4000600c084562580 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 881313714 1250 881312464 881312483
    0x120c1401021f061e0b09151c02030109230106050d02070b010821040501050d180c0e0601021e0d030507020712030c0c0b0a0c0b190e0106050f0d052d0109053d0f0905030c0a 75
    0x440d10518030b08070f0400302024035860600e00600fc9903100d0b1001d1f06803424000f0300542082c01558038160346041c240c00000c081d62040485025a2807420418440f40302c14908044c0707824140710008016114501c1003043c0c040d00e50340c01d20000d40f0071079000081550001480612a901c5050111400340d01b9a0300d9030041c41034101a88030400d110100c507374000700c3e2200810542072903d03010740c0034110092558056000c1d0701d40004103112056110040540302e0b64400c074032072004d4640b080420085800c0351310445e1b02804402c40540e00113002c09961604a10340344881d81c0d40b40000364031250100e040400c802e080c800b4511500d441500814152481210b030400c03036012000030301109403401140584940d0015980e4103551a82082040115020385c6408a03480402d50722603080d5031611004541590041d42a00c140c800c0940408030102161104800c810b200c0111030000d000102403000601d60391800c6ea85000a6242c1c4030030007441c0e1220a03030391916003c40341d154271440e2a000903940c001c45d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 881314964 1250 881313714 881313731
    0x6061404050609090901061a0c01050a06080a0f060216080408010606020f1203070905220516020c090a0b0a0b030f01120c1401021f061e0b09151c02030109 68
    0x18240698080c1c0303101901480c10000c0b0728040010340400688850059507076032a01084038080e51a00301072840888034420f070f0f1045590704280c00c54400404e0941d41d54500003007402822000f01d155100e15810019006034920ba40c0cd00d03070300038031400c8615101c0d0160110807004001869003e07004a990000c001c01180b60b807080141d0329140007405c2c0d41c0c400d800080780441c0506400c0302454110781145460540f00d40c0700c0c00030442c1d04a0b106001d40c450003005d000a048148180030385588103001214008003101e004001941c1c418000c0f1015104a102c0c000003460480990302400000c40020300301d0300c900da600d00034214254001c0c2c503020b4044068030000715020f6031816415081507400301d100340d0014508008100105042c4580ca811400b03040b8800c11f1803002da07a00e20040051428001030b20a10f044104c1d4440c41d040b800c50141980316140030451807804400f9074444420582d00c0c2c40828412189650041c031400350010700c942c1c5191080060349580e58040c5040c1c4400043c00c000001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 881316214 1250 881314964 881314997
    0x50705040b060901050318030d0b03100632100906171506070206070b09011d0f07150207080f010b1809070302060c030c0f1c0503010312080408070b04060606 69
    0x1919603681c1e6411040410212082d54804d4005561007046400710041c951455101725055030303c0424000855601e035002c2400034a400d0081c1e9290150001040240c2403402d2030321140e01d0129800c1c0b41130420410031070041e4040d039290760801084000c052640044045001800107405401900c00080c2240e4400c140c80962923400d0f80280003031040c00c0340c1e60320710408100144d800298201c2c2c000f84107011002c0001d441d1424a402004600c00218401800b4600310404203a22540030314154001c8001c9640380d500401c070141550004001203000c40175a213002d03490440240d02c44e00c240e1060100c3c401d180c0c1810351203405004e1040715118654020983c8211040030b00744e40e848042e80000c54100014507060000304010122301003901c0c01c04127481e04a500b4240101d441a44a03040032403603000d4090b1034284d039410f02003e8100f032811541591503542401200700744607000e0210b84000305042c0801c00c0103032015290300206010b80c0340341c01e240680203401d280c0701e81004103400c14146180230 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 881317464 1250 881316214 881316221
    0xc0b0a08010816090914100b10020a1a0907050a030503130b0415030c1b1109010b0f0706051e07233609041a0c0315130e07060c05070504 60
    0xa51070003210110701814030f907004000f4443e41c40e040360080b20341841d40d91b00085c1030000b46116800b81400103220b0801c5001d03c2503100805025204540140c42000b00103a80c0481d4580c00d0103a04040c0251641e0724111640f404d00c03140c002961002000400000300035000000340201201405645406581c4003d036491030b00482c06411307a900e409803404035080b44658003689084c40c3e545070000c03006990720703040803041c02c6c60f644c140c0703000c4816030302d0120034281502e226004101d4103c040b4900030284860000c40d01500e03500402c003544039004070b900320740d01e0300083c2100101801ca48090342010100581a5000031481d840194503003010462050140b801b5a440d0100046040504040100104515a01c0c010b01340d50341c002e4003940c241c080e0310b458074820702c01c0d8440c4241a09520041260094003d0010301c0500202c108104119815020560100c10bc000c265411ba01880302c501500d405840c0307405c100c0c510341c03041d40c0c00092002d40c0021203440300d90080041e102c445407038400307200a4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 881318714 1250 881317464 881317483
    0xe060901141005060c071e05010215070c0818030d050307021b0112020f04150f090f180c120c0e010e0306010e130813080303061503060a140d0c0b0a080108 68
    0x20320102c5200300650b05040340100801003100080e80c06035505c440c120004012100f4007504203400c8902e0a0001c0d5804005242c0c81c80c4400180c0000b07403901c060010700040720380d2401040c100001c0342c40e01c0e0a00c001103641203101d07070003416503003d07404c00307003008040307800c111240001445501e03803c4d07956440c0c4074588c1c0030000c0181d49000a1400100d1400080e50001181103844041080001410501d500382d0201d00d40c826520b4041c3c40d0707030200300145403a0a6400241018400103010406081c950140740804070b0241004204052240d4007560b07201903201000080e41d0601d04240c1e134003507200c003001d40e40e4032090701c1d01c001703045000080c035a5903a024021302c040c2c0300700031003c0751031130900415120059100c0c0c0c007800c1c03615902121038281003030141d1084060b580040140540b500e000c1c1c1e9546500c01030241524103500c1d2070000a04d51241c0c40c42130034080159901c041c0c51740c2d1145d03c00701f416203400c00518041c0035a14641d482c0242d000c2da07101000145e581d0000304400c1c1f00811002c51 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 881319964 1250 881318714 881318731
    0x40b0c100606183314030c0c0105100f0608040201050f1309110a1d06040512101b080402090406061721121906030611030403120501080d050c070305010e06090114 71
    0x400d031000c0c800131441c0b80c000c0200d02d4280884645501030b882000c0005510a162924240740c0303c0d144807040c0d40c00e40720701a00b6810380076546001400300092146804080314541d20304800d0710b80319400140c030644514102d00c412120000790700041088641c8480c030444158031030800c102541d10300d030541c2500071340520100040c2c2d00d00301e51841c18210141209140d000800d074524050b80c4800141c40c0d1b03040c01910b100c03250081e11122206003a18440c588050482c010920300c46c1c0b0042c82e005012041c0108028401c181c45404581800143c4d804840901301030f842d205030105141c41602ea803519180240304500081d00f44c41081c041e0035106a8502048600c40290240c0308e150f07444124040100d01071940650710080040800c3e0f01f0300500104d10510001e06a81c0c1c01d1905004003c501100e410030107140c05c0c000100408600020032048030b84031031400e2a10344950130764450070038a80b079001524944c00c0c6911041040c4020500500948058000b0030220104808201c18407008444842 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 881321214 1250 881319964 881320019
    0xc1b010f090b090a17060f060109050108010e070309120e090109020f0f1e190e01140a0c020613030b0f090d08071d1807140f040b0c10060618 62
    0x411542040540070201d40145528135403520341c41c242c88017044200c0121059070002d01809480842401c45540088003071030010300440c1440f001809041e0184a00c440d42c0c8600400541c1d000c0c42a8484074466510130bc1031511001c200e2001030140e8100f03c003d9125040520001884184620807204107000000b5007504082c0180100d16241d00511889101c00c403680f1804c1d21a144030000510348500500401e2000d07030302d81113000304820500d4440c01d0510018a203401c54802d101000d65045c000c4929150f003d0030014804a000c82c01003e070480492950031402104000000c180c4d44d110360144a4200d15540d140700640d039440303905100c00740100d0f03d0000407580407881100c54a00400b0034407000c60310b805115002c188103442d81e03000566484091018884825413052500680c00d01111324141003420120741c1e000d0501c20f9100e80810040005007540d5407403405e120743c012050001000304001580d5401c003602d014207085450301105940800131400b51400001d082104141c0c0d4901e1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 881322464 1250 881321214 881321219
    0x504081608120c100608150106030b01080105120f010203011415040b040303200a060c0e06040f0b0703140c06010504140c031902040906031401151a0a030209060c1b010f09 75
    0x16000e83c0d0140c4400e039803900444924051000c0d0034040d5100400751038004110507245009468100d200603002a0304140c2031800c0f200c540d070f0380f041c0b20b01e05480c1c048a1210a0110384c0180302d207851291090f4060700d500110000440e90300d1003001d50039520702613072003034210f404c13032080010548518020500285402e110a2020910074042d03130407410b001301208140f40d20001103a500c0c0c4026040c08482c1d25880d401c0c40309006078004100040002d090b0707a0207052505000782c405464034103000b52a602030700400c0a209040c440c0c0700301c00b840e10440590b03e58603001c113a481e42c2c48079004d006c5c143c015800e20156100c03002c02c48001074460b200f181001070454031102602d02030508500010343d0700070340900c00407400c00424854100114407848a026100300824080341c06e655034440ba0ba00e042004400030890b003d4588611040d0b0621801c09940c4d84002c0c4100764001d000e00d0300d8043d040750300070440c0e1010708400140c0040d2220191061511320807210011038956112201d0000080c3c05501c1c00c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 881323714 1250 881322464 881322493
    0x90f0f060b0c15090712050a330209030a0b040f1a01060905100909020f122d04050a0507062c030d030207020f1903021c0f032007060504081608 63
    0x10b203411210880c10703280490760b64102840d4800c028582070322182c010340d00034000c00500e10b08188401c0c0c156102c4040c160610401e0794070001300807140c042c20580004502c2f503c1d44c0c0510102220b076500c40f20300081403c1904007016032782d04080045840103202004648a00f05646a03603048a105650b03003950f40c0e041905001802104442410920241e103001117002c04036070000d4803085c1e04201e25030b0780300d034600c000d074030000750700600051082c1c55841a0030721414010022040c1c502180703a018901d039103807450024030780b46152101401e18026400c0110302558007000304000a401205261048004908641d19042c2d1055545d81d15030b010320032000d0287d0194001d800b2030b50004260f01c00110f410030108100055482030903007207098800e02402180740c800707180300340140404d4090810b4800ba54400320815800c00028050104038121220f96050356066129120700040607204140c0e654000989070b50018000d200680c09002e14003840001004c14203002ca5070007038001c00150205084 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 881324964 1250 881323714 881323753
    0x1b0309101e0c050a0204060806160e06070611040308032d060d1401021e0a030c0903052a03030705011a0f0a1e05061305030705010c08091002010204090f0f060b0c 71
    0x101216180202c9142c103000d40c6c0c3d1440b07100003c01142c40904024035020f6002c00940c3e40e420045001d00048030840025a1111800e07289074940c040c0000510608052030390607540a1944010404400042004201400140c07903680403c401d01c014402040400c1d940442000f04480168005d2800010354000c100c61076104e40c1d090740b000c8001031034202144280b800000721078414002d086000550407200c0b40d41446103000d40052481e11001441c02c5542e056221030004000c0c01c0a080c440158080310345510348030599040004040300e03074038603103490494080d004003040006140214514100503003007501080049030001444c00d0340c003504000c01c1c10103001103001802c12400080c00c0100e05511039400070640480b88052148a00349408100f5103002c03000c2e04800d04008016680600140010b000d40740700316422543e103900c3c07500070700d800c84c0240120790002e0440d500300350840c0c0040e035075944003a9109407800404c0c0111070b00d89100002d14402c00611290aa00255544010100e6143e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 881326214 1250 881324964 881324987
    0x8010204050301112706130303081501030501030305040b070519110f0a35060108030408010c050a0f0e0d0203030a110709050105060f130506040e0a0e0109050718021b0309101e 77
    0x401581c24142911095100c4250b2078208401044c0040b0038000050780c5c1d0618501e8bc0d070030900e001c2c402c0350f0441d079000300760f4041c80c46a61080e11021481204002041c403002802c2c285a03503600fa61041c244c10329440d803905a10507035010b020100360030180360a004903000284c401c400140c82200e0980b1001c03003240e401e40c11040070141c0f4200c04c2000046c40622206c1c0c000c00107803000b9500c9905008020307085440041c06c60041c0803040048450f00c07034000b14001c00c1c501c2e003402e0482e440d03002d0a0200e40500c0343c040009516000003e00e006003240c0040c504492540c40300110760240d078481c84140202c41c420700541c1e600c00030520a10f580203d003a0001c10042c104035a6511a6503602c40104009400941100c850b40104400300142030070f15100f0494416200d07002808102016103031151110454003601000b112007003101004200941c0484007484800c0d84e29503520441c013104035849401144480380324106070940510118465081b0074603440d5050b00c802141a01c4500c1602c4800410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 881327464 1250 881326214 881326219
    0xf031b0f010c0f0c051320030a0e07080d0e010206010e01030b0615040b21272b090519140d140d02060702190b060d020a080102040503011127 62
    0x4100003000a412080d5030480c18411002c000c0e03028145070801410707148601c0310050705454100c2440e0100201c00183ea101189030000030341d00d448078170040b006004ad15503c81c01d03504c99400002440a00014002c03403138085582e424480c040d60304012601c441c000e00c120781c030303011400d001480424071544902c0e4201d0310081025030f40b204124281e03403054105a0020021850120380b0b100c01d003c0511084017800010080311005260103c01c0740c02021a04c02440c2d4001c81c1c0c0c4000040b91070b001c11489811110211100f40013106144030121100e024409210000c0e400402c006400e090840d1540b0000784040a102181410612200d14070001016003a40c003000c899141b0020a400315089a443c06070800600039044120341d0203803a00601803c140210f60200346c203603d01c8291002078034140750f0302070a00b000d02e84032440050800791540c800030750300c40c0483e68002100c0c00158000c1c411202d080d0021b008045c0da21020b03110500440f0301c01d68680c8000c4000c09442d000c00401c882a0740c500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 881328714 1250 881327464 881327477
    0xc18050316230a08071d0f13050c041406040e1609020a0c0c0b1206030f0307140c1804050105060a030f030309060914150901050915090f0604110f031b0f01 68
    0x265000400090b0181e100c4e410f42e810070901070004980b40c50044100d540c5200d2001c00a04201049543c0c4c600c0c004d120912050f0600c520341c2c00c002082c01015400c020041090050005a240320040c400054541d0742c072961400c5891950044c000c02d400016002904070001401d28044a801c0650f11100d041301c20000410b007540700081844002002400c017400a9989604c00ca030014001a030000c1c000520a9100440500020000104545440f540f02c04242555804800c3c070619041101510650104038040c1c84c80d60340d45480607440c41940604001c0c001500d0300024488008035901015100b545d510380c00e4801301e406904040300300d92050600150300107a60304c80501240c07410704010895080b04444120703074a0341768103e942020144000704803c0c1003100075950740700017030070848400180ba0380004070340c0da1092003200d03945428501134030f405107018902040c005810008140c45031889450030020f50a0000346502600d10808417108141c07409020422524036044559041100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 881329964 1250 881328714 881328779
    0x171303050f0d020d020304060f14062b080306030d03050c0301030f2303220b19170405150c070302250305100203070206010b07110f040f0c18050316 65
    0x2520050803510110704d00180c0783c1c101440d216042e01c000081c0b405803182000c47c06015042d40ca841280c010104980c5030441e000c525039a840000383c0e801942c3c412944441020b130a02541000962046400701c0694281500401c0240c0880e0380a480500d4809014001400040d0181c000a00114061114ce00d4041030002a42c0448046994000402e410200b10b0640b0440c5290203260010f402d24400045582080c600c2002e60103050702800d022820b00709481c00780c901542d10307400c1c01c1405151040f454509800c1c06565140010b510022150401c40041d28819020081e50003e650543c0600700160803890384005842c200f04500c4d86907149050004000f507010004405440782441001d6183c0ca03041038082e041c82c605a0003c248000c0802c021000034a00241c07104500e10110303101108400b05d403002c10000d1a2180b9042911444c18141860090308110f441c041206d0610000320240d84803824103131250400108003071540c4096409001c8620401c1120f601804500010340782c03802c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 881331214 1250 881329964 881329987
    0x1180b09070f031118041a031605031524040608160f0501050309070e041a040b0406110a05160f02150a030c020a030816170115171303050f 61
    0x340a9446101141541c0e10303990185030180035021034021815185401c0034068010603c1c00c2d002c442160b40700c2e03a03a402041c0342030300c281d1006155082020b0100c50400806010344804009280030752480392040c03400c0702d40d5031110600841e10a103074041c00034104c4507131101c210400c1107040251550042d03da26001c1242c04e001c02c045240d004419031140201440d20400000c611000c1e000181082002c00820419a8000075014221a01030070000110340e1b035030400100315030102900040f03492100e0305010911035040542400341c0c2c0100c0041020503050001d800140c803a44011401142080c015107070b115040c1501030480600502d61406622200e0340046c1c5030081d140c0b5660980700d03011a0300d50304503a240c85001c0d01c1d1416400100040c0c0e0b500e40b40601401c03002090f0b480301c41c5040b0001d0515034425103403980514804071441c03000d035844106d03680300251502c041800050460078550b071155541503006c0d004001d503d0221420002c90b880c01c94640c0d0209a990b90b140c40200030081d002d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 881332464 1250 881331214 881331229
    0xa0c050d170f0a1706150a09082a030a110d060e03030a0203070f08061509010210060f14090c1206011b03030911030a1a061810060305090607020601180b 67
    0x5600742d00b40e0350759903002c2c41800780581d0a452503182c642e042250420141c1c5d1076000b50700303074503041008000d51100100001225840003039040940c49008041c0c401400e018107803110701c1202c00210103940560351070818190f45503034866002c1c1200c1030003500c509150801805501c46503004841c041400258a00c00c42e03c0c5900c15a100840b26030b0020810600c10f038030201e646801601803911602d0703428050005802c4040d001c0c01891202c80015203403210380c3c000c201e0003154040c2007a09100740e41c0d44a49030101070056100700114050002e01e0081e040c546601c1d10361040072120702c01400c0204043ea4510a010010046410310881c01082c10135801003e4000402c140302e540c01040b050020f180070100e00ba86c021219000e58840740c05000000c03400000f0b40880d06010146034030030380d14100007c0d13680342400124640c1d480031009104825454660f4081511000d44051000707440b031550890f40c44a08035040350041c0c00410041c085003040c840c1004140b03c80c0e0b1800f040c0e00340c5a03000158507 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 881333714 1250 881332464 881332477
    0x513061b570b0f07110a0305280305101403030d0507020312010909052416090f06020303090c0105070816060b04020a02030909181b1206090a050c030a0c050d17 70
    0x6107099500f00149807280a00309980290207207440104d0303100340410385544001c2050020280800441e60301c108241071414000310100640308107544911044020300200b8082c1c540801850b90000c020034441c00d04d1140c002d805402500662420040902402c018440600070a085010400c0b0480c081d04012034698040c2500b541d00155a24440c039000d80307041e810012080310203000c51034403e906003040380410340c8111311001100e01040e8803042255090195007003180c11099284020400710303800000341d03100d1900388045030418060907005650502403e10014900101001100140329840d810324184510071113011481c90502e000003401d80c0c00041ca50401607001264a120503d440464107400c509960b07881d4030603810560b40a030710742312048600100705848409442c0c0c03c0c1c0390407029841000c10302c8180ca440c2e003004060681c4502011100307980612824400b0407140c03a0101c1c0b41c280e0fa95008045500c194500b5080c0b01ca0350b0115201507603280b280220401c40040e507640104107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 881334964 1250 881333714 881333723
    0x1020a050c15011d0a0603150e1203101a2704180c0506090f030304082d070603050408070209070e0114070c090513061b57 54
    0x701d41c80c004800902d4580440700c0d400340309a0240040004031071030f00c40c8a4503110501004240c81c1d8401100300d02030038017503100401c980800700d0b04824403190741d88001d0320b201451064610240c84990702c00c1c11400280c4901c1c0d01c0700c9481904012064050350714805103407103a034003981807410444019880382100403107410702280c0e10944c64514175103481918803c941e541c120441e0800d0a4850451015040c001c244c0680b1001417000e4007079540401c4403039109001030403a503459440340002e58840e0b0b100000000b180401a8508c4d080c0080c00c0c0440701101100e00040002030728100044003c0d00d4003410a54a610080004001685515055034400c0807030717490b220705150100c00014080486081d08040c00841400030000046541d41e610302140c12101010460307803660710310230141c2c000d0301d071006003001d140243d40132428001d4145400741020544906c61542d4061210801c070103040d40e410304110409160f150616581c18042482000d1011a044071003401442c01d0209048a440c0c240e8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 881336214 1250 881334964 881334967
    0x803190f14070506191a090c070213020a09150e0409080d050405060106090801060303081605090604080106180204050f101206090f0b0609100e0301180b1f14010809010e01020a05 78
    0x10000710b1905d6410100300006004000b008031001301401c0c04401c050202d44601c0700d110115080c00b407004152540d143e0000d00c18071200d2101a0004000d43c485401d013008150440340010700402c141040382001c0c1c0031070700c9200941001604000c000c0c900600e00b143c0700001401000c115200600c0707a684624480c6e001400c440d410314001501600b00c40d4400300d02a07040400c103100196008510030703001007030b06c0703112404030b68400c405942d0b501038100503d800c03400128000605d0704054100400b1580ca0300c602d074041542918078442a44030300c5c06031b81c1e00544002403181590800d101d4442ca4617485103402540c0381d0b03248180f80242c0e105903000c10300141e11000c50f204040400c0c0701e1901180300c1107550a291030400c00120321a14520000482440790340074039941c1d107882c213400c103510700054404642c2d540c090030320b1705060803102510760200d013550001010800020038044001590200d03c050042d20a40e00300440e941b8000070701740231141d5242c04c51102c13901401d001502d02d24a00d40c07900b9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 881337464 1250 881336214 881336221
    0x201210b12030301060504030803060a1703071e1101111f0c02250512030f030408070311060702060a02130f061707030203060d03030b030102120c130803190f14070506 73
    0x700440c4040385201c1d45a400401c010411550070030101d9048070f501c080b40c961203a58000002c1c410304415804050032454811040c0300904002c401810010b2184002c201e01c100445154840c080e0804130092280c0003040941c030140d070051984007d081c42000850310302002e10090714401603414040000075a868100d4040311540602c04a03082c2144c20078820000c1000d8003070000c41c0c6842d8418907009014000a88201440c10703c112009611080121a46c0e0304051803c4480342e44880d90075000185185802c109501020038610700600440c0e0082080780c40d9040210003d520110303003512144041e9000090030083d03a000c0307100609240d2150700e20150a101c902440c41c40041400c41014410420031509036070704000c0502941e0036103800600c0130b440781c01080c0203201e01101e050118105408010a10759503c0040a00d1003200004481240da9510b802d0360b00d000d00c403025000c9800f2100380450041c450710317070560510720398988408043d104c2000c851055001c0c0d401600c5c0354000c0e8007003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 881338714 1250 881337464 881337469
    0x6060102010b120616020312070f0905010e030601090c05090d0b07140a0c0f060207200307050301062615040302010902030622030309080c1906050108010b010c06090201210b 76
    0x10506410420f07280003051070860100310b070703d4002c01403503000204956003c4548191080042c2c034000303004100a8402c60400034000342a81000c030f074040b000201d52000106065200b140f20052948001d0020700c441e90034900400003a20605e0581020044223024030340c140d42e82c1a580c0f03514580030794521100d604180100800c803560704564200f0f042c00401ca1030300312a52000c0b41880031030300490006209400752410901920502001910211540c804d40b034400048034982c805060b0101c0444160039076490070b0500f40e440601c60300d1440286a07000d004030540160f1314010500080042d9080c220040441c0011030300c05413415001070b0b40d10340140c0f0441c14100318460700800608010028040c903144c0d024420f0000e00c0c40102003580340d26a00b002c00007454152001000404166091501c81d10030304500c8075040b03681519102c0c102800010b0f080410f108a00300d088041c0d42d400e0310020f140d292a80a418190401c030304201d11040e0b00540040951780314840307122021400f1400d00e240404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 881339964 1250 881338714 881338721
    0xb0a09020903150610080601120606031416022509022205060f040611100c02210906030420040908071109151c080c0604030f03060f141309050606010201 67
    0x2c40e20350f00108482848034942e5201d000c0080c0c2c208501d080c144031394500700100e03117840240c565130075850b007040008a943e681540026601c0d032061f1148854607600d00800844c5580200440c2d0301580008941ca92404d09659240f07041d01c07a00038204945a584000050403a13110201204061036041021207948409000a200808080702c1483c148048070b11443d0891207144030709000c1c0080ca04076000100c02c06d102c490103840074100108001c000c4920040d4845003518440b03040030b4a280c0c40c1654400684081d580d80d210302a0415085a591755283d110404440031200c4401403607141000882e62075004800d4407030300c2915403a440302d1082c500540300100050407107100d1049502007000750001c6000e02400c2c50802c45090401094081d5180c444500401c0040c2540c800010003d61021000480314043e605c02d948207902d000070007000328200c030014000c840740b1030f95020040100105001c645103900d0002070010014007d520300b4401112164401101c00313410050800c8425030b020300c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 881341214 1250 881339964 881339983
    0x1080f010605060901120902030f1e0601140f2d0f090f04030e04020f030a0b10020d0503010312050f03090a11040c050f0d1b030212010f0e040b0a0b0a09020903 70
    0xa00901c840340c10310001403220300960000b64100701c12102040b05105070b9800015106801a044c1c45203001500d0740d441d15221149901101c2c03240e06208072603103580010b40c1034103c82c0e0158001c0e81a6404008104180c40014421a845081c90204000428541c00c0052489000300b064401b0a201102030010800761100054403540d21030040203072030764460700115400340d490b261003100a080400010020701880145001041b804000c000b0f080613039600c44000040e0468100c90f10449402e422a40c88828001c1000045c500381f00400001e1000061048142c00d1410254108038107180880380a40048a000d68907520203074a00040c001e682e00c890036030320740944080c41241c22500d0050441d10030b01c0b44140d00144002503d06d000d041c1070b84103040045120300b4543e0a4000c2000060103900004502000d00d4596400001c021031440c80400490b41484034103240340d9140e4a40544030140100801001031b140c6410300780310350303a44001c0c0d005082e102000503151540c3c042030528109004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 881342464 1250 881341214 881341243
    0x206090d030c0e040f0f0c05090a0e162a030c030909060b1b0c310203070f0e040b03060a0e190f0b040c0b0412060c0f090611120c03030108 61
    0x41100c80340207078811403c12802c3c00070384020030712074100d600260007030420084c40c4032440e00d0009180c610b2903100004003101c0c0c404882c04a01991918008519250250b41011402c149981c83c20020780c001c3d1051010194120301a0070f0400301e140c84135410105e501001c4001444160b50502010381242c9883e010b004440300400c00031b42424491f41a40c03184004502d0100d60140c602058500104401c1e4196400074100740b506a000c1020407480210b120860014407074600241e040c00b00045c4203582c403d440954620710a61540c401c2070325192500c119060300203403602011340240d101003110300c4c0558103503c0000340d0b400e054a0300c0c0303040c22207468044030002403509110300881c05454003280307566000001944251928901840d0a1401d90b215a5404c4008140020b0911110144600383c1c0d001d20028801c00e00c184408480054001d40c50724003184d49034405000c11031140220034001c1c61072600311603800c41400220303d0b4580012a03000c02541c00000140501102482034561450a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 881343714 1250 881342464 881342471
    0xf0c0c020316140d050313060201061a031506030a0e0105090f010b01020c060409020a110109030518030309150a0c0b0907030c050a0e16031d070906060e03030304140102070b070206090d03 82
    0x5040140045190030903c040c0b00e0a2000fa41c90140501441103c010103404010b24050740d9540034040c0c0a000144103a03071280c0d00c0901012400280001102d10680222070180040340c1250704000c01500081c121170913250303a56040a10501d0244599400f0b150b4002c02040c3c0200451100e5083d03400001c0301504642010301b03c2d62480d2544030560b001d42e840c07004007503201d180d150400c940c4030324409400e6038030350b0803c0c99150606130024000c20740b09064802844d0300800c500181556441041d00103070300b0144a036203180c2c02c485048040c10401c2c9040c41c14002d0b4245075200c1c2055190b040da140d43c0183c004500400400001c011901e0050200783d41c0702d0320f51880c104a964070402d000300350303e02d04607070100298030061081e4092010100007121141c800d403076451078195602441c0c0210309031149048804503090340101c619000881d00140110b145a0792039582c102011540e040600b1150740038401c12001a001d80039040c400d000c40d0303004100c14a050045d0a2403e1104807401060514 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 881344964 1250 881343714 881343719
    0x7060e0d020a02280308070201020118110915060d0906151403060106030501030f060504020f0a090507110c0604120618080307080705090d020f0112060b0a021c050a120f0c0c020316 79
    0x40200b00d413001c990300000480c1d1200c100d0700044c0d006d030103071a0403000101c0c01551070b4001c0007130102e85013071000000d980c604029628421205001e01c40c40c06151750020060000ca00c907411203130441c0b00c242d4412000814041c498a030f2001403005541c00411001d860207600e160541000c121140c010815850705101c1949103449041c1c001035024005400191120001000d548402554a40000713000d0301e1001050340e6880004010141560000c1c0010001c4c10406100d01002980c001c80480c02000f0503d0186000680d0b07641b4440303590f04690054941001841d80c461070494861a00d004a40c0d040d40ca180c44a4000c220000c024071440a0100603c62900c050700d8a1010b5034100380d054070050868110400160f5a042c05444c4110200381041d0300803c00b5103003040640301d081116000c84182c1d03000c2268042500f40034196a40010302c044c00080c00d03591042c0d44d00324011050440c002890041d2048240940300c02e04c010501180c0c004d0407542c1107081c02c0226400d11140e544a100d009030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 881346214 1250 881344964 881345029
    0x30b09060108070c060207020306010605070b0612060a1e05090106050a090203010f090c02030d0c02030415020316060b06040f0602060105010818060106050f0f0d0e0c0307140607060e0d020a02 84
    0x41d0103011003080084c130080c2107003003001c9581281d115540007002c13a00250b9650300002c1007540500d0003101c10840c4040850700909204600d800c210321804084e01c0c95a031400307602c10003060414441c0300c48560b95a03441142c00e810380325540c000c100d0100042902d60a04c824030003c15038a5001c20381c002e02c100010004c664160109a090f64010000030800c82c9000500703e00d580a1154804c0400d4035125403030700b115800000500c1205c0b4201c800340301c9041540026600c03402a000f03100220055800040d0000f01c40d070303000400020000f0941400d268960100c00e902d9a540d40195015034494030040c445503030851141944222182d800048900c1426000ca4030b5060620640080c4038011641151a441030803c3d01e110002e0032a099483c1c9510101d4a001340080340b120304031a015811480c002c03414040351b180241c400000100003402c12440034007800c2d62050f0b00c2035030710640d5251001071131081406103040810fa42e030b0007051120046c0c0108180e0041e9180c040030b004141c010380e4030b80034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 881347464 1250 881346214 881346227
    0x103020918030f0a05090613050306060402070b0406050603160f060311040803120714070b040c081612110402030901290a21080a09080c010801050f090a0905100606030b090601 77
    0x746500b0f00403a22216845801e643d0350041c140f145600881c0890490201040c0c150780e4812503030110112000c0e40c443d0b809000481c0304e200d8000e403140c0400c20004001c140640c0000d03030807013030150840e408100c141c09011064446500a011300c400050010440315500d40190840b184105040ba07290515010209680348280038081d80c0500d9220b00140341540121100c1c100ca0020b03105c0203950380481d2400302a0214121400c480711000b155020581c1003000500000300c0c0714070864854000e00305402a4880038007654121010001654900c40ca512940090350241d00b182d40041020820701210404450300700128241c4000c000802455503a103076a08a411601900049541d100ca01481d0304480f0a420101030580200000e40707150403a80120148102c400c03c0c000d640a00c80038500442d040a02842041d503c84000c0010440910301421825040030301c41d0030000ea12002550340b0350a29841041490382a40e0743c0104011081d054002c1d040b500c4001c80704038481d0311b00300d000038141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 881348714 1250 881347464 881347477
    0xa230a060c0b010905061815040c021005090c0a051c06140402011d06030c0a0e030a1b090203010e040b180d020d0e0d1e05030d0603050d0306090e07030206250803010302091803 77
    0x1b003207e00100720034961107228070517003000150052041c5102c40c18083d540d408080039000c046880c180004400c6400031502c09210140100244070350b03403a2204015a14210340d440190310801e4071080c000181c0f4500c180d101a01c045007003000b140c0b400d4000500220305182d02d494003000d042902041d55a1a04222540318404200c0386403500062042150703040c07031408500e60144a409020418886401001840c40d103080015140e035948441604042c0e02013813080c80b070380703400c28000b10340010901c02101e54007900031458101e1018481c0600b034070f0254141c02190158100341c40300034440b070748040341024104040da00c2e004001031503640c05100c6640115210503400500080008004043c0200d80388180031139020702c904c54603800d003d6200d000e050030b80d0b00428a041070006030b1a4107809130004401410010303020441c42e507024007505600502000084c1d80c10005031400c0300b48914240b52019015a4469441e0340c10741c814440814400b0744014494401e207100003040002c00003c40c0c01c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 881349964 1250 881348714 881348749
    0x120d020a03081005030a0f0b01151e05210a05060f0604030204052d091b03210f1612020313140102032b0b0f0a230a060c0b01090506 58
    0x51960703404143c88024205800c0306130b15004202d0845c0c2800042c0c00f002102901900c14000280da03038034400b071640781f03444156201103501c945203c0d0980c015050700c1003c100d42402c16500d080c0318415409110b480000000070201108424800c4122070742c45410343c041001d83c0e00d00c41c0d4a4149001400b00c3c0100d2000910654491002070381e5040041c0500e0002e040d0030b20510394000c8001c0f4030317412054040394100c00c0c0344550f40d505000c00c40708460402200101401a18014182800b5050240c40c10300c900b41020307004010b941207828a40008090088040c040c41050940b140f074040351101802d109801158818000c488038101191041011101e1511b02c02110000260050b4110302070171150102c01c444440d91344600000d551019a10105684000c002c861024410840c0503900444030b103410179034404040c00180c041904480c2190b80f200c103032901c0000504005003040b140307504200e0004013500702d550204407006100c1c0380507284044c028005850500c010610141307400c0421003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 881351214 1250 881349964 881349977
    0xb0c040f03080c010207080a0c03021b0d11030c0604121104060b0301061d04140618220c0b0415090b070812040213150612020408121b0304030c05120d020a03 69
    0x3c4840c0301c254116041e0ba90b026072210b4507201440b00240035060b14202c25000360103524032004440461305c0130340014000042540b84410030b19180c0b005661b1308010480c0c1c040c0704001001440341e42d541c01910090a0702ca20b00c9541005620781085d0040305038080501590602a040c071078000c003c1c041c5c0b41502d05900e0010003040c00b02108210810031810840d030482c1ca0f0a082e52450050903008500c5844152a500744a40408510f9103114100f00c502030004540d100d6503400c002144003140d44003d00800751005403c0d180c00340078242c0e500c507a01110349941480c408071304864000e40c002000702810807180d0304280c62601c0e042124030071400c0c2540140382c4000040d0031076550050001402c480c0603800c03c05003504601d400700040050040340c01148042e0450a40c262640c000c49003176400c6000900480e80a0380d00b41e0b41030303801120f04445269003400d020000c800701040a4001103000e60300402c00c46280c82c0a102d40e4075202210072616400c554601c0c292960009414400c89505103000c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 881352464 1250 881351214 881351227
    0xf0b0d080405040e251a13030605280c020111160305031305010e0f06060d022404180203011e120b090c040f09060b040c091e0b04120b0c040f0308 64
    0x107080120340d020800310705106170382e4484840201e001070000d5501d8a0302e0407040b11b004140c3c2403036502450080340640c5442000a01c009561038200e00c0e00102c010001441c4c2d81035880b10721201e14003440c1d5a000f0955a0035006051903424002c21070311a80007500c0c2c600d81588400c181c0038441b01c109001d000e102000010900e4900005804003080d03400038002c0000b90301403a601503c60070381c48200d50f403d10070a4082803851400c079010056440c1d0041580800103080941000a0701c0500003403400098240301c001155102e5941c1c00748030b180750200060381c0358100201100b040044103020030442411203803d020540a2000c0307040c505410000440d60765941a1001c0e140036400d80e20107400c5810811406000c1130607400c5144118031071038041c0300e0f00c07044005200c1102e55901076003000030f1300f00c6020001c214442e20340c220340380004000c4150f06911041801e0240d072081c0d1045805007102c80201082c80855014240c0200015803030601e014070300100c1c6e42f680001400003074020280000d05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 881353714 1250 881352464 881352491
    0xa120e0c0d0503030402010201050c0f16020d06140403080a05070e12010e030f040303030b030c030705131404030e2701060e010504030b1005030f0309010203161a0103060f0b0d08040504 81
    0x803a01000c40050040c0616240c0e481e01c1e94036500155402c038007560030071010503020010141a16442c00314081701a00344402119003500c00c0d1080c0e0350580e004480f0035000d001184080c06030360540107c1e000024a10f040600c0d0040c0b140c00014041d0180078908800c0c805865130003500340350050400c49685d401800004065030040c8892185500c0c64803002507032501c03100643d030140c0b0449001e07490401550740203005158648070181040d0350305820081085c016072400042e03000b040070390040700003004817104802c0c104c4104240e400b40e000c0343d902104450f191038a500143c1021004008640d4003450360502c401c1110411f00980e41400a4405501075591080c4251401940c103c44182e2280c01e2820041e44a4402c81c086c040c040d0103502c556130914000081124045c80040e4029441c1c41c04e0540c0d040380e8030b41503c03403c40e948000b00180501d9000750b11100d074061401004000f58400c50354003402c0480e800c0c1c464460144510722140d80110344000152411101c013940c021030f5201c0c41e680b8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 881354964 1250 881353714 881353723
    0x3507021305040221070501030c11060a022a01050f1f0302060c01110f220e060d06020c03070b0604051608011205124909020a05120105040c0b0a120e 65
    0x180c0c0002103d02d0b103804c0b0450080010061704072403003070301c0c10015480c240c4400c841c0321a0b010404071983d0b110130701041c11203c059004200c00c1c00b0000203c2014404c103882250504c000701c29499032603454031f0074810130b1410410780c1e40e003100c481c44420417070b070003000702280e0304120a10019116450200b0f54001848080d0080714010280400071540d81c002220341e2021074000511103000ca8082d411001c038500f030000425020b030360a00e501c0b404195100d804001d82080e1042040b10a00c0e001d008241200d101000a004801e02c14241c42c2000d2503c0010700084500052800c1d030150705014108858541100105041d124100e8449908007041e0074110700e8081d2010300d42d410141c001592146501c8140b02c40780006200404201c4070703100d072200d40c0c0c0a0240c115010408a601107500100c1182207500c035140b280c0c400340076083c41550b202d0005908405004410546945541c100030030002d501c0c0315400505007021070f0905116910390b004005001845010401664500404114078130801 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 881356214 1250 881354964 881354989
    0x18130303110d050f13050319170703050402040b0405011505210c04061710140301150b07051002070305090111010e0d090303020607020a050d05090d35070213050402 72
    0x40c4116610b162551600c2c008203021544008111344401c003280401101c04204824590401d000303506003408800030441c2080d500900c0ca0034401100c1040c034000d400901b03281d00c190070b1a200040c05140c82d00601095038200340115100f10301d000d0044c00f2903024091491070b404041d1804c1e170384494140038001c1c001d00000c060041010f40324002c211500520800510544100340d4030a4000d035130707201d8020201d201c241e6000e980d0340d804134014462801142121948040001d0000c1402c0202e0b030184911282a81c124004944000883e2010301204110303801c8a0300d44858211700c0c120190b10028080d00900000714108203514070007503035000e003d4200d145254942c1d400c0d20000035207610090060b0109210032800750040c03000041c0400e0021906422268100b0007030001c0a40d482e10884a80e889244440e50001d001402000032560b404280b41510b021680c804224009000390783c0000142c5090b203c06400c820050040103855502c6e06480c1410460808031b40f82c0c455100007a264940308 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 881357464 1250 881356214 881356241
    0xa0b01120f02090a0219030b10140706110c0c0604080d0507050708100506040b100c06150803041d130305090d0809090709060906020c06072d05030406080618130303 72
    0x10720900803000c9451780140510308000300354252104482a0035000e40b084120295445002d450324030340254010360200504010000849280200541d5402c007183c003c140d00c5550442c010a50038400c1c0300401078a03039009001c46d40113007400c1ca0195225540c400421000042160201302d04003004010450748014020034010744a003101c0f400315103001840f046819511803804c0540040082c1880e4510300c0c00c0c00e40f40e55520f580030a0584440d4050004108244003401080c50009004501130001c2c00280079070b10001184070000000c01a0402c1c0060920300741c010400d604480001d821400f00e13000c51405407046241c10940c0e0402030064043d40c0c0844d0303003180100b8100054070b5030050340c080560f1020344642c03a61640ba0b20701240c1d150650040c80740c0000041000401040d4031600211903c0e401c0c1503c0046101c03504644089015112001c80d40c0b40d00100e0207011440d0071000741c940c442001c0d91119224556803040c001c041d030303000d049180042070785110740c410f141c440d420204110440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 881358714 1250 881357464 881357479
    0xc140d11033f240402040b0d0b03100e1e010b0d060b01090902040e06121f020310120821070c0305090f09091609050403020d18090c0806030f0a0b01120f02 68
    0x15041d42c00948120f840002c00c2d007042c03000004940c03619100b517030f05558400c141d05040c1101010f140c0d000744002c00003280d040c4109014121008690b018140c3d01e00132200140071404a01d418807034900c0303012107100709a0790518030580c40b140c5494006a00c1150408400316843c416000180c52583c0503401540d03501c3c0c00001c003c80ca01802465943c0200e205445401032a000f403080562101c200d25081000110315098114032520389070046c5800200e4078604015069848022030510381140c14204c8010501041d51419905907204601d0381c43c040c1d9060209618048900801e4821206c00c0181030003000300b10115070342c8480e85082a4060064007820540c1031550b0700e96640c440c41c0c0e41c0b50280320f00a81c40490724103140d000d10b84c000d43e0b040c1c00900c2c40710582001502c00d40740c0c00d1085034031400d1082c000100b42d05c4a004580c00b628141d00d50303a6860806200b41410035896100111155000c1992500002c0001d41c0040c111000a60b072550214001c1c940b0011f110708154020307602c00c40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 881359964 1250 881358714 881358721
    0x1806041a03041403032d0f0c07050106121209060224091006090f0e2d191109060607051005060102030904020c030d180b01030b0402010c140d11033f 65
    0x100c095034142e002100e02d0b1070804c4114480d40c0206d490864454440d5141c01c000b01b141c0c0600080500b030042d10540004c41c1603612103c0d44c040c0c01300c404900f03942c014000c0383c91400b00c070341120510010342164070141c40c03101045600840300d8600701b4440295142014000380d40280244062102c4c2c0768880002c1c0600c0c0d0751905201d01400d41c24204040783e0f03143c2155685d0840c40021030b400c0050000420f0340e1410318039041580e03001e40050701c003917050098842182010341c1d141202185180300c0c3c0f03000d6508808403c18880309590060409008030b0040000002241d0b0010b864068007034006004646650764500407403c6025001000e034000d40042000c3c1080d20012020702028004007a04011440410030140a070349071107800900440400d50050000c1080086050390042c0103042082c91038041d43c1c0c40000000348007003640c6040d0880e00601c01059844030180e1012203103d0000c60030028116440f0200c050104640104142c0c004c08c00020320300c1040760488a0204a54a0b107a02d02c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 881361214 1250 881359964 881359981
    0x40b0d0b0d0b0610020309090109020904180807050c010c0b0a1a063001050d03050c070308030c0703030615120b0d05060f070306080a03080f040f0206030c1806041a0304140303 77
    0x2602c0440c4115130340030703080c1210703480002a9455803100034001c00c603a9180c001c1c910300a5003e076a5a5402c6a142c100c80700f960000ca0039100f000a10805031140c2d14601820068105620b420351a4108801c0059000200d0841c550281d04070541b6600001c1d10060403150710510717841710040940041021402c4d4082d5403503a00c1c000c00030109140b829a849144007148558407809000700b640c020480341924020034401c2c0b004c1c08140390943d04a40c612034894499140c150000c94016050000000d00801059410b0142034001d05901c4201d55103150341c0c5002030b101600c504980b0b0303c4180d941d290168241d0760f10f4122103160307070013805450050074168011180c200b8100c0700703140403c1c20b10400252134400008c0e20b071099905507840000c2c945503522808011440640182d5004844102c01009641d83c10021800b03801d82201e25070b0398019a5400050a0040000306849014113110070444d0b079281042045a10b10726941090b5030ba034561400d0680602040c200f60002e110100802c802e00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 881362464 1250 881361214 881361233
    0x6050705060609010e1f23040b01030c0e0f28080f210307020a14012301080a020103020f0f0c070509010b1c050a11070614011208040b0d0b0d 62
    0x502803415180c09558840502c07000c48400e20482600720800390004044850400b503268400d910340c0c0340b01040d00c0d568441c07810301d640c260150341d4800a411401501d645010310540c3c0440318207083c01c0c0894030360f401018058440c502201d40c010819074004880c1651101d020b0044c201c2d41061801441b1600c0090b0050420140200d4001d8847c020400f00d185400050313205910801d0003624038074a20842c1d940e59503400c0a0903010540c0f040e0500341c40018807114601e0020169440002440c5a8107104031805440b40040c400548034087d0050101d9800898104000d0b0380a09001d40d40b4030710344003010414481c00103091441400810800305d4444003040d0013040f140b04462291840e602ea500c44a10752041030702c0311a00d002c5011001e984000107070042580046c0d06540020000110f0360018150350116408444560340c2e2815030313041405505056014005104001030104032030f0740e401c0b03c144500c0c0150031150b440802c0c40440c0386840e41007441c0854024044882210452400d12101c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 881363714 1250 881362464 881362477
    0x18110a051801052704020d0611070f0b0105060c150c13090f0507080f0f1005041d010516090311040b06040b0703110316081b060c1e03011202040203060301090c0605 72
    0x1061031592000c11301e1401c0d44080b0f0021801c003000006900e0f03c3e420009141100303403046401c80c1e1502c000c12080000356010304041400b03404040090340e0743c0c0ca070445000c48160085440b8000c1445100702c8200c00044020a004000d40d07011031649403041d42a2490184040d1003807141084500440c0c81e80c9550000011202441c505000030b480f1034609662580e8115000c2d03001d1100c040000b030114004c0c001150b000078500c40c1d01d191458592022600b038881c03858004001246607040c501c40034009100b001e90219451040003103a07680c0c2440241910310522000d450888035480c40c0d001507541d40e0000c030040000a10107540d03140d8070103440c0042c0e003203154290042540d542800c8a80b84000c4100d40e980740078213076000d0010643d503071165003039001070410000c14580c0c0c8451840b0b256081003d24020600d0624454403005800d00d10001c90030b55220700380c445a403e00040000d422420304100e0305590485015899503190380103c4c1c01442140d83c040d080e086600d000286180c1c218008225 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 881364964 1250 881363714 881363719
    0x108030c0f010b010c0809150a030902010e092e050406090603030e04060b09210303150a15140a02151614040803040506130306110a090918110a05180105 67
    0x1c022140070180d00700d038056410300d070100d0205003619001500d00002800052030040100840f0b07020300610081e10341100003410042076403440c640d0290f40c0c01c4008ca0308514800c5a14089500e00900031143c0c8041540204040030f0300c5000c41d0101e1202451981c000c1e10014104002c165555190030002d44581c0c403040c0d01045102c00240e400d402d081c01500207580240000c240b4243c5104107000503101c410080f45443c407032a01924083c15030030300055002d22134010300c0f4082c40b42c40008202134149294440b0864051022444035010340100d40d044901d1805400d094840e448000c0036824105040148000c100c4c14108206002c10b003440380d2030801c0c690350b9802c001d42044800245480c0f0590054959543c41440100b0462418600a0580913211138440b40c01503546e80d583ca0a0341c03464414820741c40800b081d404481c0780e00010120052070034240a00070040c4415a130796024000b4040074008034000d41501e40c040d100e40302c00400400c80034110500f4070101c0c10061400d400c00f80551403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 881366214 1250 881364964 881364973
    0x231905060708060915100912060905070e13061a10030c1e020c0d060209060d050f070c12121e091415070e0d0b0c070c060f051204050c090108030c 64
    0x5000b424008002441741104010500c0c1a9521604011a64408503a006c041040c4070710f001c10820000c3c041d0001c0684a180085620240c40c90820b0500c0955002811800c82c6001001400b0200c5078102c0d40b86a004880054048913100d09000c11180740302c1c0d91030b008021041c1c5561100c0c0e25034003603070680f0175070f0b5146a491440c2401c0c05810000035888900103902000c03c0c42150310300010386c50308451003035900500e011342c4d080100d06150841101c6041c69a602d07002c000f000a410325034107600c1071741131a041589040a0b03540e0400129140c45147c1040300005018081c581e0310b0f84003118591400e003180c4003002540b081003004d403003807003000c5a501002003917200c04000c0004d0070b20501640008206184d1303860500031920a20b401c440c140d8440813120411002c00c5c003800c4114020381e24040740c1030f0307560541c1c00c08203102e181e00c0c0c0c040c0c81004840550314854540c13180c02d540207c0d40b400c2e142851500d03581409480c250315907960a9222041000000c1c4c0c14800000512010303000380c0503a03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 881367464 1250 881366214 881366221
    0x120c020f060c09030703240e07090c030203100303030c0e04021b150c0a08090304120b0106030e160b09010903050d090e010b0c030703050702030f0a0308180604231905060708 76
    0x141250051158240e01503006401c00d200082107808208641d0848803480841100341847c0c10701660001c0400094030303005000180800341850090030b5840320380b8201540b031410f10a034080c8a1036281d100c041c007099034558070603440d580300381d19a0303c404800074819900d40d1046c6502c1181d21811180d92403051007000b801c85525000000124419050a90041c0c00e0a00e03242040d529001e0007002031445000821022400ba000a8501d604103030140c411506c0b15030500c4009802c540905204041c0d9502581c5480880c903e05903801302950503407650182c0340d21240f001a40c4181541d00000c00c41d0142511003030a2070ba009203504200d1310081246103890341d0307031011035206215450f51308400350401c00401010a01401c01400b40d540f024080300d03e0400542c64680c20035043c1c44089001030741071710521400d200603001021204540c40043d10703803400c00d5600c184101048501e0014407007508150513000d540309106040d030342031403814004c000c02414a0b0094550100701e40700c001184064012 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 881368714 1250 881367464 881367481
    0xe15030915040b1b040b0c101a220b060c01020306040c0912380106020106142808120306010f0c02220f1509050702060c1603120c020f06 60
    0x441c1d010340c1d0010549506a1912034050703004105001401c3c040074002c00c00015042a108000c0000080e02406400881d199040d030400390f0f28000030300700900b542c4080e00c880315501d400740c1c0b00619010080c28050f084443c000c0780081c00b44c2c41d4216601040204a50417050410b400451140d50200d03010002100b5906054801000d140201c0340c203091500c00d240d000400d106016a0510040e070031800100507410441074480c138a504855008031340c51001007260340d80900800d4054100483d6403810300315400007290784803583c1040c000b0700c000080380c00040c401003804e680000d009200b09442c2528a9031030543e030194001c0c0e8279503000a45052003840d011b4400c40701200070550041a001c41c001c564602e400011940c0d00d45a402e0390360f0b4040305900b95506201d801e824810041d0070054039890580d508080380c500509000940d00a2010082500c080300c0c01c403030600c0075a0904501e140d12500702110f1f000b50b0f000c00c1c00340719454502144070094000810b15049181c110071110341c0c0daa0b00c1c04c07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 881369964 1250 881368714 881368753
    0xf03040512031e090a0609050145020a15081e040f0f1103160e160804080705120f0c060a06060203190c0506010303200a020d02040c0e150309 62
    0x2d00038407980c02c2ca070022403c00d904079441070700400680201c510368289500c8a904982c086801110560365034a5844845089038003801602406000714000d581e8540604040c245200c5944008001e03401155074215520007110201a00740c283c00c105160b00c080b24040d10f24941035a00072450350f070410042d0030601c01101145e103c2c1d503015005400910031980d8407010302c10031001c1114003103a001480b0606841c2088a803101c62048441c5400325868520300300418000549148440d05e0701014966040e40c00c80b040941256029110ba507850240341025030030550b0807810f581100000103484000c0315001005403880360204816240262141c0503a6801c4819a00c207440142c5c106001c020046502d0005041c3c1c007240604019026607191b699860070440c00360000c0b00403e008c2c082c40601c000d4203074030614549600e0001040f0f424015000a404495131349030007889943c4485004019512885508000300d0001e48010761a0008944040340c0d504111501c400900c01c6011852000150704c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 881371214 1250 881369964 881369971
    0x31e0c010e2512060c1724010206010e062103181206090601050f0f04110a020706080f0a021b030703020c010e0415120c080d03020309070b090102100b01030b060f0304051203 76
    0x10545840103071503680e078002904440100c05c0034840700c82064050201c100902620a09904142c0d54107510a130f00b6808440440000150440d44244014405805c0494825030420f03070031580261595640030740711110310700c51100340070907000109400e891408e500d4004002c8100450f80015403100ca08002070382c3c3c110407a02d840240c1d01601c0100034900307000b240700d504120054580c0201c5034540000c0740c192000744902c48544c01c00001d20901031036046c41070354082c004515211010b4104a102c402500d100941110443c0381c0c002528091466510b510200148004087e40d8035410345060203034441203254081804182100a15292490a407050350b803210a18500546940d040100040011a03520821103140e00300130000305072020100803a154844032540d0241e503901d0030144d81c80c02e02c521541f043c1000e80080c0000c0d03246a03004203a10029400d03651000072107600d107400407005800e03030003017154101d0720001e00400380705094001944154000d5044409848004809a00350b20045 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 881372464 1250 881371214 881371229
    0x40302060f0702010e0a030e09010f1206050c130e0601090b190c110a1e05030604020105030a15050a06020d09050607080a0c03020c150909090c03031e0c010e25 70
    0x3040014042000c464200c0e420030001e00c000518011103904151030300d10402403c2d00811617000608503145040c0020030f014101e070950383d03154685406d01240b03242a0b103200043c0303d141c407000003442d01815a0181c400381c20700e01074800758069032256076641082c1f080e202d031070014201c407801161040c1108200d90b200c1c4100ba407050394040391948202c2d840c00d8210707000c0320f242c1402003450503195240391810001d00040b42003804105058550f00700524401c0d802103000e90011030811000d40c1e005410360340c1c080c207100c40201d11072400c8600842442c0082e00220742c01a5040d80103d501a4009400402c103000c60700c400c80101d4541d8100300c2c050140b01402800100b0030807103420254800c00e001641144207004868160241c0000600c1e1510140c50b40c1c1407220008c1030303030002d42c030f0100300d52500003c440c40540311341c0b2135220101c0d843c0e104025050b200d06c41314008564000302980300300c0d00c0c8000c95400802050765529140d1f5268503000105074030010910308450031a020740b0000700e003100d000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 881373714 1250 881372464 881372473
    0x22e06032d02151b0303010e06030708160504020d0b0a0305031b011406060f13031a011d01090b13050901020315010503070f030b0409020d0f150204080c041d070f030218040302 77
    0x10094041d005501503840c440d840300d08144c490090316005c1015502816240d00410400c0c40c00400713051070300c081070380b06490b00c1d4400d4902214110001d1181010303108155000350740c0d0807100410402030319801610b19080000c441c1c1c00000c1c46000b10103010030042d44615807410012a0301d201d130070b885401110842245045001c900b0a1500b20001e00802e4a0310a12506240c0701c11642400040e20380d1003500d0720800c0c02240181e4011900b00c6c60301401d880c0c9a404840415030003407043d4002c05018802d180340d5030701d110448960380c6400003118110004030501040c507228400c00c1c042d4000b5101c00000c41640f103030782c245540c010400d413803003481c5c1550f80310795211501604038054080d00c0c00c03d60300665038000e00400b586034040c01c0c5214034050201c00c0080020751500d21001400049418550b500c107000c18051480d01080410311180c1c2190007040101c490010180c0c0141489003290280c801d06800092014500400e282280e0007221040d203088990340042818040488000700181c12 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 881374964 1250 881373714 881373739
    0xa0602030f1b15040c0b1c0e120a0c0501060905061f0c140618060603100b0307170d03063003020c30010c022e06032d02 53
    0xe09401400810708040060000901034400050a1400280080c40e01c9a00f040c03c001c28420380d86001c0c2c0082c105540504d103002c13000322410482d20b510803141c24210b901c800b442c0071103200400044020140301c24000c0d54aa401500c080c0c1490301001c1e00707c40f2942414800580708405104091040d800908030b040300d6107200804503907101620010405000c0000d0001d40411410301f80843d081c0005001014207041c0908209600c04500702c01d044d00d40e1100003003040a403004140c96100c80c440141c04503c00c47c1c544006402c000e5590840540710003c0c65900c40e1022000a4030313400105152002c11050380c5842c12a808482e510a1803540300e4610950802c14041822124030030900a01c1134030800842c140000301000c8141d411059a1032944840908101094140e40d4019036418003c01c8182d041c0d860180d00e40340f80e13940000116149907000c501d0105a1801010309100e400010000c0710f44924102907103441400c2265504038021510075103041020207165201a0010401c110038503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 881376214 1250 881374964 881374987
    0x6030b042912150411121c030911120705090a0b011403041e0303050901151d091903021605010305091011090405090a03020c0a150f03020403020907090e060a060203 72
    0x10b045405100d0070322034841d0001c0400050700d030650241d03100e0020400300360411020805c2c2900d1050701e8810350340000010700a003d103c0b880d890750114190802051058050038013803080d004d0362180301e81100320b10b8004600f8540c0450326005403003040f68429020b803280b0b40b20401301e52128001382d0200b178403081c01c1da805926140c0515031044c80345d8000c0d5070f038040c402a483c410443e1500202c0101c0e45841c18825189028002c0c841461000101000994a020500c014540b01c1081190b480b5002c44d0225101c00340c00e000101c040c5001c2d4141705c1d007503505860025628200e2151800343c030035651801142c6903209006090182c0c140c0e6004081354040005100001d041e00413030481e80c1102000340d180c0e00d0f103d90181d0780c0f181710804080e0440c00210b04003e400c0c401c5103100e89214010305e900c01c0c050101d000000d080c14811601d0002d00d000d41605080e07000744199000a5030001442c400c1201e066031050201e400e8070041c1410032300030348074031007402164040c034081c0b4005604240a070503603a6 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 881377464 1250 881376214 881376229
    0x10323060c030c1b15040501110c0c060d15151407033023010b03071d0604240e01020712020105070804050a0810050609040c17120406030b0429 63
    0x18503811002514202d01c442d04c680c5840e40c4543d042c210712041d4010402031000c203200c2d121030742547e45da102c1d07e00b1100402490b240c0d52500e1940c3e11695000c581b0b80540b288030ba01003c00b014413071900315980c5855034240105500010700c031000048480c04070300845c481c4481540c051651548410715481d040d41c0c0344000707031b44481c03055144594402200c00100400c600a100c8040c8600c1c03682c521503040c000c0300b10580c0c08160030a02810350204248a042a441044c1c0c400c203801d800581c455802010001406601c15a441540000e04100c11150840b114040c1c80c40000540d88130304500381c48030401a605c8600a1260407110840700c1c504401650003040289030440c81294290b24207601c95000031001c090035000040103a100e4100d00401200c01c0c46820b030009001c8485040364a1702d41d0310100300d95410700841c02d0f4401c00c41e100903200b8104006214506041c3c030404e94a0303e46820f4014010701c42211700714450380c1000e12012071072211b0034160700ca00508015518815020208ac03041c2e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 881378714 1250 881377464 881377477
    0xa06050f070311060c09010207350304030602210603061902090102010b06041512050f060409080c0607030c0906080915070507170a030e1519060806010323060c030c 72
    0x52041e440c44180000501340142071140184682240e243d281e20320009180c81d0203500500f02801030300d14040e001010403407040b040395076a5012640034842414400b03003140110b45c4018231090000ca101c5042c580a84940c500d001100d0702280c603d0f6691104240d5100000e80b0241c41e0078030540c84501e01e02ca09900144031210041c0004220703a442540880c02d254020380c4041d01c00c1c03e41340001c010540d48204841c5000800b84070520450414251680280d04c014048070705c40d035660301682d000c218012041c1c6403100c00c850140c40c01c91424400c0600a8620841d01c0030029044072404288a4000e000081c0680700c0c907401001454120030206403802c502030700580500c5400d01001000a0145030032486840b0f010194035114102242d028090395a00750701550705400c886550b90301002c1912025900240100d40c86401d00110345111000700155000042580101c2d00044140500d01d410200d0111112a88003101210403071004c1d141d100a403801c0224410030000b081d45048541c025042 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 881379964 1250 881378714 881378717
    0xb0a0212070806030724020d0f0e06030a0f05040b01030308073e0604060f0609020702030d08100839151e040e090d090501090317090306090a0507050a06050f0703 71
    0x204152250241110440c8211240910801d01c0c6c1e038103a0310541c140074146400205040c400300404002c80007a1074400303504071080c0160004400180040241d03000b003005800800400c00250526050075a4802c109000c141d0114a403040411a40c2d031040110b101000340b0504620003803144410a1250001d113a00302c54041034a006283c0c1c40e580703003030007843d01541c4a1100010f291038408005000da03100d5500c0310110324411300010025072004903800491100510740844160b982841c40d03402d00c46281c0190701140302c3c1340c1c030b0030700008129001040b5003220303201d10b010050a213620b540c081c403e200d40e0701d0380c2052005504920b03134261f050241c42c0c100c445034410f550b0503040e85501c10761a0003135030004445030710000a0184080301440900fa03075030114540ba03400b907420400080c3c560005888014486408000040840700c0c0443c151030203104001e054620b01e05100108560b50540d0307500c00d03249030050010000f81407405007074035402c03600302e520303000e045c0b20b180c0000c0c600da030700107090650 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 881381214 1250 881379964 881379973
    0xf09120b060a081c11150a0e160b071e0c051521180d0e12100606020304030b0a05041a07020c0301060303021f140103060c050c06040f0b0a021207080603 67
    0x9841d81003030107116131083d443c002864800110b500000d091003049294500c1941089a5440d407043c2c42c1910300d40d01806030080400c121020254881c07500d80ba035030300c00da0400001000030602c500100c005080703650080c40c001400200e6801b0000068030441c234002c01a00620000300480e09051035251182503824416600300396040000040d81c0300390041c500c80c4100840c08104030269110300450420280b200101408051814090164030000e11198811f20101080c0415140c00700a090902c0345000410320640e03950700c4010303599401c54001150103030840000505001c8081c8545c07445036801c20485020310345080c0d410340821a024040d042180074a8039035404948003402840000c5110303600a1010040c414071078800e5641401103000549e0414103044411202c500300c05042d26001000050021308500050b1090302c125480080340d400303020100801d01104456403041a40220001142903440b8a100f034228418110400740d058510030100310241d00c01d020706940071b9005003c0701d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 881382464 1250 881381214 881381219
    0xf030316020612040c05010908030a08011a0d1a03010e031204060203040f0b10050f0301090b011a040f080a06060f030210030e0f0f0f0c010c0c030f030e06190f09120b060a 75
    0x1c6444003c116410307192107100d19020011568041d04910080200720095800d00c0c0070128001c2100c9010300c02d02030b108045184292008506404850300c0e140e16a00401030010701452031400051140c004502c00d500c3d1910105148402004450604028145180b900d03900c1e551180001d40003d401900e56014910840d0001084500d12038020a002c58480a01c41e10b00000c011465949068050103079060804803000a240d500f4100d054070401940303200064001c4003421064002e6a110700c1074510444000140c2c0071000c41e190586602800040c46100d8071003107580e400d08a103100003504150b184058102003442907010000314482c50003a500042105440545804641c91124010707030880c602003070030310204010b4400c00fa042030070080c9050a00d41c07601031354001359100c058441a00250400700b0107100300d403074007403814004203250745403c402c1858008050100300d6807070108000000d41003c1c04d000d07008020480da10301c0207008090031150303154001e24101501160300804100342c007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 881383714 1250 881382464 881382487
    0x63519060219050c120d18260403080406030c03110d0b010e030c010f0507061b09030516080309190509181c0804110d1502030907050f0303160206 64
    0x944a0040c01118050b8540c541048050042c0001d04545000e00104010880c1c0d641c201040c00641094500f1682da00d4100f200c0901d0302810041c40d030380e01424140401ca000b040f441c000d601307014204e509024007464810340c803402d0007446a4080a080d0039020720040044900c070b904601c0b0112450314000c0f8810b20b0380c0f81c50800d9138100c541b9224480d61620b05132000e950740030b1400080721030210014a041c2c060100082c0920217584c0142d0208a00041c00005000c040e4200c9054443e60100d101e04804820100520381011170004903014051000e4101030101a0840181590740c5503000c1c5103442c036030f40c040201002d8800c03141c03103500d41d40040029880c0e80e9418030381c0c031a00032500060f00b0f015403400100d0800303034a140030010150400300c00e000c0c044e6010600caa4055801100001030000302c200096440c1d001d13500041c0780000b1006624250700702c90f00a076018840001c221034003036480c2d0b4100078181c5456442d281d011b500c00d0007414031404071482400702e803500103030601d4079100b4803265 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 881384964 1250 881383714 881383753
    0x51b010203091f0f05040509070e06070b0106090e0c120105012006011202011106070c0f241b0905010e0607060e1b011218062a030f0635 60
    0x31103c00b00709280d4030340001150054004c11a00303166203015840d060401d00015100030010341a542005061511080c154481508590011f81c0020070300c4603540c1c0d6502e0042c4042050700503604429940e40c00b142079000f0100581d03a41204080001807903a0810004540075030765810007062040c2c0380103900d00d46600c00d0010b0740c040c008024080c0101038080c00054401ca1100c81203075000d901040810260a621111038144a50f00190b031190310911420400c0300000001f80c004842d4095103000120b842450380410617809090300f03c0380144419440a94140031180316450205056480d020003610b0f00c60300500070703175104010015844d01c400325642d10381200c0c80d04103c2c2c0d010b0100d036400381740c1d82c000380f00c0f0040e1860b501040c002c15100d801d1304035070b0b9070141c00000d0220b900d90703451290030b10280b05201d24841c0103003010740300004070070780c02409800c000f80f51010191a2510106541c0742c2401592900190008218030003007440740d01e0740c0382c9560200200200d0148101511502c900c07500d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 881386214 1250 881384964 881384989
    0x1c0222050609010602030a080a0b0612010b130b0408030a1103070501050903030f150f011805063702120a170705030a050f160e0406030822090207051b01020309 70
    0x21000449140080074800041d00607004142550f0003400028542c0d0303888000b25920020750000450841310f0000403c5044c05514549180034641e00000b00364010500040c00300c401e09601a0460f841d84d540e14100548114055120745400030003001d10708a0003500940052401c40d8112454140d9507180c0500b16501690101482c1d00000180710b0303040c02000c205a0000784501c00304114a000b00001101c4124a0f08203605200c2c15035842c04104005080c0714004003006071404d0f6440042c1d00540f00100300c0031807060503258a030f08689410121101c00703020f540c90640c0080401e100c15010300481500080303102c80400124000c80c0008040ca01003036405100e0a4a81944030304061800e8416103000500750814540c0d08000c003e00c3d2054074200940c42451818580c100070141c0d008039000d080c050300054100400001d86c2c05044541c216070948900741c80001c100603070b883c0c6107a03800341c0c86400c038090116030200740c41100e011110030140c42009414011a49404100404600380c01c8515 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 881387464 1250 881386214 881386279
    0x6190e13080c151602190209061f08071b0b040305070f06090303090b1303080105042c0309030c0102060727030b0a060305011a03070e180a050706031a1c02 68
    0x40500c4104100035441c0d182e50031280c005030806c185540042c07190500310301ca010b4400c0d4084401714910b51100e4040c140c4182c04130a134035180103038102c13000e054040c0c1910f001c000900c071004c3d0702e02e1403809201c002985c1a8060024542a204c0d900d0484140d0802601a101403450058400004001e48140440e142c82031300e002c00c4181c043d003845243d6900052420005c14140c441035000268417820040c107640c801c0b14001030780440841681e5142c00d854014a08400c8011071400c0c0000f00000948480c0c0300c120304130784281a00800480c2c43d10400d0359000d0201d1070b12800e80b001c1d000c400c0c00e01100852984c4242803056500d0320780f90000e603c01d48191590640e100e40c02d1062040a014405603140c0c20011400724118a0380400c0c8c0d2844140310300c4640150100115602c00d08a00440c030392103190001301c1d601e6803030701d0400945449a0b845401c02185c0f0701600350001d1240f0410040315024002c04881c510000b4816000c0480c9802c8006c982c4012a007500f0b9014600e01c05c0c0392580e980b8070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 881388714 1250 881387464 881387503
    0xd030e0c030a0327050613030b011d0a050405032a0d0f08040609022b110f060909040501090b010f0f0519060e030c1203040602010e0c0f12160e06190e13080c 69
    0x450070120314509c010782014040b101d01e10f80c60024016294102500104600c40000c0c0c965a28180b490843c002d0303c14001d0000100204003100c0c000d074010f8004d07500052811344021f2070300343c402a52007604c1c0c50500382c003052280000401240165001c101c0050002d0600c4502256a910030040c0d080081440c1120400b00148407088c8071542c00c40f8054040305aa003032010300c980900003404e602428070300c5032103103588400045c00c000c070030f42004041c19031040d40d94125503111030146021001d140613054690303030701c5040092545803502c807100024001100d810282400c14000b222640d89408050b41c00d4440c4000f0304101d504c401e0008503018000c20051600c490a002e002825541c41c4182c0140a40c004e80f100f0f011075403840b81700d66114208803011402c002d140340030242480d190503030080c24810311302d1000800113280c2c0b125078400d0320104d03900c1d8503241d90001c2005e018400390140b41590720003940011000310700d00810040c0d060048125a0825418600f81c5150018400050901044 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 881389964 1250 881388714 881388719
    0x20c1018092309070b16050d0509030609061306020d0b03060702010f0e01090812130501020f04090c081b0c0102070f0503070210111209120d030e0c030a0327050613 72
    0x1901d1011180e500340001c110503032410001034103507491005025180d4a064009045a1b64103500c20f6002e800c03592200503036204660464015050f07030000c1c00c65500a000300b00005072480008030704a44110503620961800340340b10785414009400000c03c1c4d01d851940c500298031680e500f040182e00c180d110340d0012441070004404c0b00150380040340d0703c1840b41e050841c0301c400035a01c50103486171408030506070113403036640c400703406c0d100c014819000d407140d440081c4014207005c1ca0310080066809240d014002089087d0013107501410455480c80306590b000289a200d0707900c44000c0041111180c005402d105017038032400c000799025001180c0e50303440003400a00f1410301c00d8042c4581c100c203091005009440003501616a6032980030350f461000300240440203540e50980400c004d01c1440d04480a204011201a0050007104111b92442c4980001443c480c900060624103150303040c0e6425040c04a1541007286045903d00082d08065002d400030520ba21004042c201028203060740110092 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 881391214 1250 881389964 881389991
    0x120e030610182009190e15010f0c0320070b03090d02010605010c03030906180f021f0507020108132111070b041401090b1b100507020c101809 62
    0x8030b002c00d4600b4208042001050005420000c101e1001e1503401d80e00c010800008820803c00b50001c1d440c00c0c44d1420114240a22041c428800c040c8052901c11404e440001921004000180364001500c01c0b001d210010b441504d0a2002088504100002d424140c03812410a6001d8028200031040407003000f44400003007115540200c80790008200c02401c00000078a01c80a4040180c18180c54503400820481301d940305200508501100403000c6841d80b40940c1c8007040164164400d0500010503008002241e400c110008490b03180c407441d052270380c0e006481c0d60400400d1103010014034408040824440311003001d860020180c002c0f1011540c000c00b500810840014101a5100840c00e11640150b40c0c1180c082e10203043c0c007190181070180040340e15013501e0304071040f0090040b40188a070f414445c03100201e40f8190094600c04401502100b040315002c40d803e05c01648100f007881601e0811a20390020440c1d0b902d001410401242c0413420104d40c03a40c0141519a550486440b010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 881392464 1250 881391214 881391239
    0x50d0501090e0601061d031006031a0f1902041e0509010e09060c09060910030510062a02030a080a0e0108070206071409191202150a0c120e030610 64
    0x182980d0900b00090045801c0659a8110501980c004c4c0b0402d8600300c42e100940400e1440450001000ca904a10754042000045c102da0710088540b07603034920036a1400b07034100c51600d100d1008032406080b25526480803074210044028000d0b00035908200c0441d041008854201800300000340c0104c8030b62405051042e140300c146d200885607046101030084200c40406c2080d00303d100102c409455640c1d10b8002581d5208010440d070307120b0401004a900310b50142c004c60b01c92046a40030900c80359541d0004d89420303040355810001d10070760306c8a0503081c445252a0300402e60025045418100310369903400416402a4680f502141c0d01310180e22580d03074406c101d541d00540a20280c0700900f81070001400503000300c0e00301d460140011034110a1a2141700119914905c541c02514859540301860b12900d201c003281a8000c01c11950998000d0000c2412260352803019a90110548503a840e91801c0720b070030b08560020400c052980314416601041224003521046200d05130903880c000052992 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 881393714 1250 881392464 881392469
    0xc0118110d0b040807031407150f020f12041a0411040c0e01050306150903100203250503010b0304061b020d0807030506101103040306050906070f03090f02011b0b07050d0501 76
    0x32100d40641c8000900742008141e005944200a141c0700c1c0014901030704c2901020268a150000209007c400d218404044440191100b00100242c5154118038030030b0344a1000c64503036200e030400101c0307003100718000344070b60141c0a000f00700c0c3e0402c001c010042d1070000c241c8040d1916008240042010b00e440d100d84900714540f41040384035603083e40000fa0190100403e42e5105a071406541d260446400084601c2c00e94000c0503980c6e1080401c005074004e41080e641c4c80610070400b0a4000341c0d41d102c41211144d01c14685a45045a2030030382d134801960b100401c101e91158803411401103071a400a80c002e003082140e00500fd205400790b00041611500402e41c0040608000034031006071140048001c4504040c07402200074000c00da0140e11394412688010540ea14050030401500008200c2900906603036030b035030845c5850881d044065484900c0080c280ad00d0b0300f001000198022020600849008158220300941c5921038400a001c207d44a00110b200054407240036401da2085174007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 881394964 1250 881393714 881393719
    0xe01030e0a23010524090106120902040e03030705070614071e11030a1106061909020702060c0d020c0310150b09040f060603200403210504030f030e0a090b1f050c011811 74
    0x280c7d890203500500030519940e40d401c0d50f555803400d0205645441d0403412402840c3c0084903500e0520540c018410350000405580b82071815080280402d0b113004e0041c050041d540d00c103202d03000502c02344140038140011000038082030710000c1c4941d040034000340007120442c1c0c072100c08003103240014a08224004052600c1002d104100514001030f07100d410081d03503500c1750300503182c010500c0402c0300c521a00d5402d44040c4161802c80030300d15400103040e015000e0a40a0303a140c1000403c100041c0c030804400c41080b03c414200902604143c540940070250004101080b41c00c0410407100443c6d580da00720a002a450b007003090030340c4902c00c4040b40ca108900003501d103081e245448100412140d01e80c552b811922b201f80c096030b118801c2080d10003031500044190b9105055203000713080c0800100302c1d280074014000001600141911a2041981c0058403a42081d8680f8180c28851200c541c0003505228083c04519402d100c00d1151950350340c01c00054046090203410009201e8444403000707031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 881396214 1250 881394964 881394979
    0xf2706030f0b010c1401150e0403020f060408040905100e090d090609081903051308031c0516140c0d020f1b2101020f03160e01030e0a23010524 63
    0xb852030340d0220a02c482650403800b0f100d80016036840e01c43c007414241d480300c1040c440e820000318901450140030750141d80320ba002c6441900001c80e400307481d8042110013520041d0144030070040743d24682c203c01d5004010b8881c1d42403481d1110240004440700b40d074010170079441282000361450304034003510702a01c0c0c0c2341040c40900c2d02d0500c0040c1e4805500320030010205000600c001014015000e0b59403c0030f07003c82100081791206a195030380c2d0001106210490703044007888110f14598441c880c0a003211503490418002100029512010350048880c50180e0812000a80802c01e001c3c21a140a0710790240041d00300d48040185020307041200c11202c1100320b850010b190f510075803035800c8a404000c0c01c68406000e081c03014024090302a0410b1601800410040394042c01c001201c0c50380025240d40000b1000500110203e440c81080124a17900172203001012070402201003007003054500c420105151090302050960b4000d4030266408000a245c80810440c0c10f0381c00146d8000595040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 881397464 1250 881396214 881396231
    0x31204051b010806031b060403020d030c060606030605060306043306140c03030f090114040f021201060f050d02130608160905060a180f05150418080a0f2706030f 71
    0x25121240d118090200d1241780312680c84031f440792010f990095800408103a801c1100d4200030340320510058044805600c0c0c4207001c1078143c024400c6800340e9a02130070707140c19645c414040c40000c021002d03198410040240c0070031040c2544c1150780c25018501d40c9044841c45c030345040074152000311244000c004000307003c85801c0c01030010541c1d41c0a0000001c010160702c0300a943c900401301c00300d9001030204210108020f1048030f04062408034404d54054450038401d484e000d088030318501460700a00441401040b0a1070800103403001c65000511034011202864010821035a1950143c00260442c8501c1c98140b0346030b26070407000f89180d080a005070314080c1c1c0091303842a0180210000da000000314518072590366801790010a02e043e030100054149040300c50f08448114601034415414035400904480b000011152810b40c01003640c0d0a14900000581f0003900c203010030000c1090b4945904146050084149540040e4101d14081030342007400040694800d451641c0c0c1c03480c10411032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 881398714 1250 881397464 881397469
    0x30a0f0f1d3c01050c03160f02070603111b061f2d03082b0e0c0904110a180b090606370315090b0a17031204051b010806 53
    0x70940601080d81160444101c04003441d502003180b0b04820a0f58646001c00c400c6851100046000d910400e0491a060710003010840d24542501c90f21f100517000701104000d250300070341000e0307840c1c3c4400065a050408412540b4443c4034410400043d65010806100304015002600c00d02050901036040e0744c507007400c070405554a080d00e2201d01480d00344001d9490f07008000f0707008028581c080d51070780e03881d0b11010810f8083e4a80341101c0290320000d0480f044003864600c108540d214000010b801140d40800c01c11919000040060340c0c0c924603104000039590b200e07940203014203c0b000c480030694002d4980501102c15107149140600d040009000389a5105002d644442250740c05881412580003400340c26070081d03401004a2042c0e1141500c156034141d0400921090b0a01d9008481c90b80c0305004401d4500c143c400740d8010384400750602041d6905030300300c82413030400400c8a01d031000911443d100d2000440e01900e00c6d070012507106840200725803001541e200240f82213000350614100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 881399964 1250 881398714 881398753
    0x20702100c0602091305060a0905151513080a1115070f050a021203040915050d021903240e070602100c0201060f0e070801170c0402030a0f0f1d 63
    0x350206115002088008000060b011a02200b0003d450910000740305192a0003034101a02c0242c8200c50080d8081110842d51041501c61f9540305580c1c2d20302003e16050041c8181001028002c901080081c00100845545644024046a0010800e10b80305080194146166907070803441007280d0a0541c80b805525025224110342041c004040b0155070325200e403520300b4102c4000e401ca08504c1c103511103031001202500440b031003071006124040c11207507120740390340642c051a58070840310004840035041811079070010b100304942490005440703484502800c840c0c13900e005450b5220300c60100c00140340f8029802c140c80074100401000e401d00402940314040d0390309101010b556140d0031001580300350811401484c1d0b0b502e03250ba0543c1c8401121560074000c030b41210208011200000c0c0800b0303040001c10201c0707414009060316000c4102004003951014011400b055101c403824140001c01e44a51a2094080301e0000b8070b13901c6044078000c0001c000c803010030303442d086500d50b541c0040c244030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 881401214 1250 881399964 881399989
    0x60a0603030c020405060d0609050c010e03011526070b030429010303050309010603080c0f06010f0e0606070c350703080315060f0304030807090b0723120c070e0a020702 74
    0x1c1e1301084035a140c0700800d049004206015014906080c1900305100010a0300006111301307a81340c42c4502010001d0500b40e40407240200c90103d036040c410003403043e090f40524041c450122407805941d01b100e003030038a480803c0d000201c03032180020134001008515640b29802c200801034600390518004c641981c1c0341014440a8180300b0f0010000b019500e083d409180610b600004981c1c45414100c01559140d80d4a100006c081c49924004940398240211107001c48840410301d412325600e00013442060342007410304403201300c0580d801040001c00c9020700d44104020700340310fa6200da0140c40c0303072085041c040190310003500048018400729500340c04480d40141c54586560844002002084551040348504d848055003c03042c03104040d805600d884c050306407035a0f0300d2080d644540c081d404520072034000503d01080b01d50940110072028448990440030700b000e0780e0907012070000291650744681401003464125074800e000354800c0504071030b0412807078032045062000c2d55010401222198 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 881402464 1250 881401214 881401219
    0x13090506070320040605040906090b03071a0d0e030d060b03070f051c05180c0906010f03090f02030d0315090216023106090e15010504200318060a0603030c02 69
    0x407103100d441182403a401c01c4400c81c40c40c14884d601e80d540c180c0202240c01c54040d5080c15400d00d58000340850b454005c21041c81802000340603403914000102d2280b000800c40008a00c000b4481402490f40500c1030351b06c048048009541e4800080100e01c1c1110000e401000d0100001e0043c011070b0350b808250f00c082c42d1421300703100d65288075512a084061040e0942e00c20100d040c082013000002100156614000c000c07012603204862403010018101d20440364140040c0410b81074031701a0b071080e08a00545070040c1c160b140c01001c5034012a040104010506021940791110b4030001d41603003012000800400404608004100c03005214950003040080d00c20351f00c200424003005c0303803a6116014901000780c40481c9064141c03581018100d036128080c0014039000b00203148100100d889000000d55030352140071030307081c80e041200400340007103d0700c8104204074090581071039a00045028042050540d074994401821251601344001c02e01c1c0326190909004000098011524100c2103070304 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 881403714 1250 881402464 881402471
    0x306012103020a0602040f1e0605120606070b0a0510080109050a1b09020a03091101020a210903020301020f0403110d0f170712031a010504050901030602031e15130905060703 76
    0x40c1e0508924000c44003d000d40b01c01e20003d00000c10109442c601011260318100c0640c2c003080c10260204080700c1c40c852040410381c100448060070383e02d5409558058001000c0c60306041480d19650220300c01124200e062035603c40a2000300d500101c0e00350020300d65000248007200c005ea40700c9849103000c3c1001081c681441d1802ea02d04412419003d01400d00b5100031915401211001405001c40001c15100c1c01d01e035201c600c0c895480401c11117034080e00443e2142109000503845400c1d1490401000b040044244010005a9081c00100040e811820b04c0d240c6840c110700385010b5117146d2002c1e16100d209030708036503000600c0f0b10b4007181105401c01850b5a8800c0d1031115481c1911a4840c010b11100c0028410701900780c01d640100803640340781d42030082054001c0c006540743e100364050307150301960f800e0040000480f250015035105500d8081c40fa000b0a034040a9929200b00743c50b45400003441c40305030061810200c04070500040c0c0130702c007845121144d0301c0c2c075070300c0c1c1c4000350001c0c041540303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 881404964 1250 881403714 881403779
    0x1303050109060b19180e0a1a040620071419080c1603030807030f0902060c1515060d05060402070c0807060305070216060c0c050a0b09041a06040513110f0301050f030601 74
    0x781400030340c1000d600403044108040c0b02320030750355400a046904544051801c8429407090740241c0310701003412451a585440c1135900d8486e80a54000c500011a01748540040409000320b66189042064450b0b544180ca80080044050800c00000c4c110302d01c03200590010030200380d11045a6400c10428100090074030441240980613090650029401c6200043c0001c2000000103500c001d046904a20501ca0307110310080a03d1050f091080c3c550004048c00b845484014541c41160007400040005140011660394404800c04540c002c1400b0380005030204440c40d05805603a510450300d20140c610b080100b22008141401c0c0d000b9902004044180f4004021114141c100a0400145010a200d60310301d03a2151903808244031600860030450400e1564030000d83c1940c0c0d5020041006040c24140414030420212508401c20869151171001c950000e00a0080c209140c000409a43e61b40c10002400300d6142210b4503140654482720040141e2015241604001c2849440c000041003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 881406214 1250 881404964 881404991
    0x212a24120a06050a141e0918010e0a110108010b030112060504080c060c0309070b1603030e030f160b061e060a05070c090608070614040b1303050109060b1918 69
    0xb06410040c0c101c00a0030b008a19841c0c060303040c8261100c1222241c10070b206111140c240b1419486801ea040400e0300045142c100c00d692845401000001c0002000000d41043c2031920b40042ca056924004941507542e032960300c814241d0142103190310551075545400d5040b80544110b460191140d6541d101007400c0200c500202c498484c081421244182050010500154020740307000c2028410f0140001d07000b0405410355111003000700c48074105058548055001c0d18603800000354a00041100c00c0440f14284060b1040d03005815085034292628507002c0711400010346407a11462100c3c0c8520000461100e500c0c100c81803d65040752141c80456083d42d181c00388140041240a44100129400d092940204116007842045641ba140e854501307131803440070f5540040d680e0390200070901204607190024070b01c651032624011070780c40d5251113103802c4400c1307030b10b0403a40305854519164440c6070991200b903c0d217070070120720411145040e01c1441c0b008480c42030742c03071510784508034101c449 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 881407464 1250 881406214 881406221
    0x2f071a1e190905030708070303141605160e072c0105041703071728050f0c1605040c05070209040f0204090305030a1505212a24120a 58
    0x40700c0691105000c07046100c00074040607200c0c0110382c0688255880011800400a440c108594068032507007100010706072014070301d5004c4d03242180a1602d242e0311000003072081001010241e80107000b04103e50038000401050b100203811081004040c081e01e083c05200b40210601049142114865600c408001602e40340192740c803c40040640f4035030020810000310041c241203100b1401c03800161003003080c100c03041c080d0f003185400241c0880501d008002c8101504d9903590700c80d081c164107000745c4c46d06a1000380d001d8842c08031150403082d61140c0c601440364642000d090202c800b440742c652603c400070100e008014011384109202000324052240b500174103110b107900980288010b406904000e4883e600a0320852025403a000749007602904407844402950f00081100c502d0415032030f4008800c41c880117069642c2d008420802d402402d0111400910f0f0401c01540c0b181088407104020806066030b041e415105080c03070f07850500b82d01d02c60480e12042e2102810090070386034020180000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 881408714 1250 881407464 881407477
    0x10608070806330703141305060c0309041a03010c0f08070e060f0c0a0308100e04020d060e06010306150512070e07050403080c0303010905090a1a06012f071a1e 70
    0x24482e0f40c1c44100412a60f0701c01031007818007a842d0303208080600103d10380c070b40c45400007030110b40b0342d030340d80900483c58210010050040d50700c0c11a1b0030920100d00103000c6074403048203410202c46607004104103040c00c0c041d01044190600301544904406500900b40a00c010046010040c6c038030300308001503503900c080d039545902000c05542c0b0380100018003555000140c0342034000c103407450000349090a140c8101e8084e1190406490019140c59003804418403194100315005512049011a403013010420300740218041c1c0030204080e07480c100d20f4241c100458100e0f0f40140e0b1005034210302c45d107002030128101c51442c3c010544640d11500225083d004a0704003d1401c1000900c0800e44140000514141c5034004410002c54075114110360340d0310b010000c01022817209400c400308801804480710740c40101810900c400e20341c0c0382c25022040b200c4510602c04150002c14990070410100001030143c00c100c800312921605d04262600540611701c4c2520a000c0c1e100761040e000034000041c0d840 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 881409964 1250 881408714 881408779
    0x306090e06060d1e171b0f0d0e060f0310051c03051614070b030702010501050609130f0204150306090507020312040b0403031e0c020f0106060f0c020301150b070b010608070806 77
    0x880f0300312204039170320b10741c000301220390380b080e4040e0f501e01e103a0b001140c0c030810b90303808000501d03145007140000d44212081e00d5595510207010b0140c40710641c0007000940c440e900b01804000518108800c000003030804514031a07031810113840d42030000c3d404c03d049a0f00100c4441640d11040e81900e04a003484000009c84180c0c0d01071094005500030860b0095401f0390044e400a010982c1c8a50520006000d140c0715a03500000e210f00e100000c43c02d80d44a086035101110026181c20b4590355045d507d501f41c544034100180c1d503000100b003a0001441002e400807a0b901c0594501029003062402c0346001a0025007400c00e08404142010301036440030f542c1c0c1c0c00c11400d03090141c90000040c4028410318101502600a09406007030125040c8240000d540c4c9544075088070224042e002c603048019900200d030150350703e03024000c3d16040035120000400e4014446955210f2a28000920b808183d0005082c80400701c1488440c0c0e8002001e158404003c3e80c0c021300c4072085404c0e00c0c00409240e0400384 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 881411214 1250 881409964 881409983
    0x151e100902070f05211c06080d021b0901030c0b160209100303020d032007030903080f0702011d030604080f0d0e06160806060d1104150306090e06060d1e 67
    0x40c1004144002c0300c0f681400b0b8000d4880b07000c1220102e01d1400c608540121200d1020005503108141180a07241610102040006d00d01d03210060103190490002105015074008400c3d503001d00b00390300300500704034070a850741042949103545235242070305640a00102c520020503600c810404a10b845d410b00d50300284604031a0410303000302c482140c005d000550040c05000c1078405002d00071301540c4c03001064080d40c04142d1601210310805c50b00280e0080b000c20804480010124125001400c0c01100078042182d45403800e01c0090404000341c60150780d180d082020b94403180c1e4001c01da19a12036048400655215a105101c00540c800d0384c828a0700c6914254a11804080003d81a13218550a00d104080b103071030306a0540700c501d001c80d0141c0c2e10600410072054003441a42020580b0540020703040e003000d80380d18040c0070f010000c1d424400000c7c2d031804204000b05a601035000c49501440c040c200740d0801c1703008901500d0103168064881c0f00d0001c0d80324029a40883c035540e1154001042e40d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 881412464 1250 881411214 881411227
    0x1060f0905040f0813030b0c0a1d1315051c2f06120106020c01020312011a07120203182d1f03020706050f0903040e07050d0504080c151e100902 63
    0x48242c17103000d0100380c40c05100c4900042c0000703041c40880305a081c840e01c8001c460340d011000e40004203440030ba91504102d10650204101c40c1600881c0760f25642010070400c10b40c140414400c510210240c1c00c503450b8a16604400458816105d81010304000d10301c0074115a445000b900d40040d4540c1501c0c1c0020000604640c1728602032842ca040e02c0550303007a5406000741c600120f03582c0c000c10b5003429240401000401800840e0040f00310318420a00105040002e5a2141c0b00b001d09a46440b6025800003e090310305031a00c0d14240c2c1182d00222040c01008605501030344015050011400d00c03040140890715040d0369103504444a01402c030600d1003800c0500000602940103007034226141414074010894195110b0a06841076102c1c20044d810585440c100f141440005030426003400410010030301e5044081c040d8a104502800c0303216600ca0540c9429450000414a18003c3e000964188081000e0320300c440d00c44c240c1c0300c0e04032410545807100304110b220030700c0d031180c5000b52002941 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 881413714 1250 881412464 881412487
    0x100921120806010c021c0b0a05010f1403120a0f1e05030118090c0617091c050d091a0603160602030d020a0201020909070314090606010f0c0525080f01060f0905040f08 73
    0x8540a54410f42200602c1d0310340b4500230055810070301071200c6503004090180812008415000200c810040455048011603100340c00540c7c0102c03003210005205c2404d43c4041a003041c0640c050344145a0144600410301c1c074000c01c5400180102c01e061420308210003240e4115070000d4065542006d12a00e406544520103402d00f410703580b1001c0300c0260540000c010003404941480c030481d4240036031101c01200c00c801c581c80d900c0b800c0c0704002684e40c4c980342c0004c940b911880603d568036114600d459030410004040c9459985034014110b030041110500c400c81d808410748508c29245000581c5030f0301a004280d019003e0086032540000c3c041042080140d4142c103c080c40b00c8040410480c1ba4843c003010580740d000031241503002c606405c14403410039120b080030382d0382c07923000b407041c0d07400803a4040c065140040c1c0c4041c0402c2060b03c0f0882404080f10501c181944101c0d2103000300000351811800f00201a06071190143e010f81d1071001070180444403403008112036000031026955000d60302c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 881414964 1250 881413714 881413759
    0x30307060c0f021b060702010f0c06020304050a140c030705130e1207061112060135090606181603060f0b0a09050d021e01020c100921120806010c02 65
    0xe1440103101d1301d0060303c00c400385000541c1c180310024141c0c916000c04e41e001076440341000f003130302000c01400c06549404101c0c02d1002c2d40c0200c1c850006400c480c0b0a500b044088074070f2155a540c3c00d034000248486403030b680000c4ca941110401e0320318610100500394490020102d00c940c9140794040c0006034128002840b0040035003031710444003048409450000c2595a0190106047e0381c102e04070040380d8558064454844400c40b4000070748012588005000c1080c418124264a400403213803d100c148102400b00755800001510f80388061200c40c4418515181c0240403042c042c4202030080880c1d0b80303c1c0d08860080c0001c3c44480801c0e07959010030440541c81000e0000000e040004042003626042007007958064008010346c00c0c05518039020f00c3c2d2507070b003012250706500c108a03901807141c441641c1074444110b9a03c8000e40d82e0303d0246405802a422007070b0310f0705c0000c00521000044c800c0000310f01081403910340420550380303040060383e40003489207001c1d42c480c4900140f29035140340c2d1384 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 881416214 1250 881414964 881414987
    0x11030d090308011a031b0d110c1e0118020d02120f1c0f08040602090301060513020705060c2a01200c150402150904060e04060e1506010e040506030307060c 68
    0x81c0c04c0c0441d0103e0403a41450b40000d540d40c1000c00106014552856840c0c00a041103814a060000d02e1841101c0c0e81d42403580042d004001b00d810000d5845007034030707221001c035184018040081c400d900c68410101001604203000a104003074042d100015900d429008400000061044440040742170340200c0ea100d40305c00c0f074991515401003030307010a244106081001c00704c00c0d40b1110500c2d100c0342d03120340282d080241403540666803030f03000041c10340d6281c40114051014100041e5500410300f4920705020000341020f2001d0000c111041c080c540c010456200c50008524000c8603804514230240505045401070242d0201e035030880c0c1b4041c003c0720050101d00b0f4040115a1500010500f014082404950280d8802c09007a80da20700b2084400c01020035400060001070041e4603207140c0e0005440940e800e80d40f841d07488034100b0b0050010808a4840402d2160140e100e01c1d2110000b000400082240f070700031a00e500124080e03480400540d00800d600c60b20a10034000166002040004080d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 881417464 1250 881416214 881416229
    0x405010b1e070203152a030105040c020111070609052e0b01030e070e1005030712050f2e020c03030f06010e0f0109140307170703061104080d11030d09030801 69
    0x405140c0381c007030741c00c5044440043e400340c058420784208002c08503609074020f0540003d0780d889001d0b582c00007201803107140c0002140c0d0350b507912941844240401c851662100505680c5420200103070204504251907900b80d10200109512105103449420020310890403502e05c0f501c41281409800030a24020644646d5641007184c0d8141030011010b0750510f40049040c2c2d081a0000c2c0a582a4030410641c03100745418400d5038035a9030b4012038070342100c9030701c0160b891818201000401c070003400f04808015204000704482c0311030041c0e03036840c881d05400040c03090482000382b00f040c80850301a529009205021390b43c42c0c0c9402041e44844c0c0300220742c407130700068658405c1c80b401e03e8074003100d004045040e0750319642141084128043c40007401e03001c03640740c86003810005404503018204000b140705180605111491450316005072074402d01c0c1e00407030b5a41031005010807500080c7e110221107092409400202280c610308e03045100391b03003840c80d41c1803c10f13031010141904500c0c10b038101c0c1c500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 881418714 1250 881417464 881417497
    0x702041a0f010c0231050a02040b0406180308040e0a0509011802131b11010b0105040501140310030b0c07050615030604030c0305040f030b060103050a06030305030a0908090405010b 79
    0x104000e48030114a54444603078040ca00d42150901c0e54800c042d007a095600c0075103401c440c1d400401061020002c008001e590b407404194001c68900703101d014550300501d00000641c04c09003807111b050002d0246005901c00c00150103c10707400c04180d00214401140c00550f400d6545484144002d04900300700d40e02d1941900b043c012034a081e00510660103656400441c0980000c02a8200305a141982210143c1251201c0b11840f42010031819200340486a4480e0310035008000c012500b954841c1100605111042c4810051a40c01c40c0c11000c2028500f0801c035502c1d500d42102e49524107468101601c18000341d0f00708000200004010f2a0f520f010300122103580e030715208209800c100d070520454142d04200080fa000a0140f5070346a078062003802d005017825150103455103c5000b940c03003920988440703014843d003940c1603c180c6030084001041841440e06544019205101c00f0b070030500c41aa690ba041c50502280c0c109450040300020003c1c000395a44001c000308070382105041e101010355 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 881419964 1250 881418714 881418731
    0xf03150108090606040f0b03010203090c0108160e06071b06090602010e01050c040e04020111120405040c0503161d060408060105012007060320070b0f011205070909030306030b0903070204 82
    0x28107500e03881402640e005150a541e00070030701c405084110b01406840340c68200c400116942800510700c62483c0800030f00050080b50700040040c00090030321501c0b80341161103564601c1d8050148041d807581075400d08d0742c4200178907100b41a601c0450f00780c942c030900d030180444c400394096804411241180d0086c40107031103003082d4a0032035400b40c0e1b201212a500b04810402d0300c850001913a403141c014141050003190007070b022400c1100700c6102503e05100060305001503e42445003140240192800070700350328000070300c104090209800d010a11144405032281c540c544940c12440c42c1c0080d11198a80d07907038403410340da9580f0a0203158081040b84030038621614615602a40440c1d0030002000007916050040d0300400c01c0001e0300d071401c0f01052042146414a42c010305100740300303509100741460840e888080f0759406030014011003241101840124000141e98415034000500000c2c0c120411700d070a030000c16035a800145400601020003450340c0000c00030302010b40c0291004d0041d5070b03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 881421214 1250 881419964 881419967
    0x6090d11120405101404091e0623041d100c030b28090207053012060f2805010c02010c120c0803100504110301060905090702120f031501 60
    0x203481e2030500030300010500c010000d51600501c0d0400f1380d01103003480011a403418214040690040d0420103005480d140078084400714280441c51400501100700300b8582441c00d1600c405650303889003a50008061620f10b420b41c0c8980c41129058820301107002140910500c0c240c0311340340506c07196015490a5411103419005c0d00076500340350402002141ca502100509048030080d20240c0134048424000104845800340300800d04c540c0514002d280e0004a002c0f0300c0c580c0440000d1140c0301011045d03120380850405401d562305501168080b030201e075036110200d031034014103100d0542c2c03283c031000050102c04031120324000e180315610040800c0641340c4005580c0c1c0700303020600a002401041d1007001048101c280245841d006141001108106480d030442582056400d6001c040e801d04003081949058070680d0b0a92004101d0306096614001024100170414458a40a150f505000a800510a00c4482c030351349103004060351030b141041180d0f8065001161601103800d030308103094040f503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 881422464 1250 881421214 881421223
    0xa080613200a05130626100b010912021507060507020622150b030109080306010e0a030803040b0402011403010807031e0507050103020d060803041805010b160303050c090306090d11 79
    0x41c0000340c07149607181c0c50031040c0030b408800c40000c0740b18180d070782c3c0000c104114000c2c0074420034568108107400c82c5091130150390500740f1540c0d40010705e6250082810660340c20148181c102c80c4401190f08105034140003081101043c5800c022120320002801c600304441c50340b00d035024103016403c507902656002c04102041c850746027409003200701170304494000360361220030b00700c4000c0942001c100f0010a0307010a0030340e2910721048a111b580232042005a5910100c4c1400d4007400301c0e8580c01c91840c0d5200c007005844058005841000902d0018080d64000c006400e504c88480310500c0d92580d440b68034036120201400100d629640c4000210415203208035400d41c0c5a420002402c101c1c0e160200640c02903000c80c013420151526814000b4504e002800a400280350745203e0b8036038105601010300c11603030305030040c0c00c480c0010300054660031031b01005c4440c0c065240c280083d0a8440000110340da0040c0300e6a00e40c90b00c140c00c100030000c1400b04410028900c60345480c4c0080d01c0504216407074 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 881423714 1250 881422464 881422523
    0x615020d140304110913031b0c0b0a1404090e0c041a010807020c0409030e0f120d03090809100507060506120c01050313120206010f0503010209010f0e0a080613 70
    0xa407010310000d000440040055030440c0c0b2506001800081510100e881c6000890f0034031003005910045c40300b8160401e00101e000040d400c1011702c7d1003110350b50801d21900a0080000c00c45001c0b89d030b01d03a05401582004485000c5009403500c2e0303641c49000e00d001c0c5c41a81101e424078081c011481000f4100b500a05d40c61070850f490090821004200440d038a02004080078114072800c4035405035900d07140b10304850240a96640c80f03200c3d00c03600500010780f0264100c1030090200b61540c40000c40041030003520982c0501c8c0c0070a0020550070802c0c41b03400b42c1c2441942c015216411124441d1704040181000c0b0f1190800340100c1c2e4440042220380401e202000783d05e5001a001c0c094150701c42d80046500080c0000340c00ba4420f10303a20742e07a000350016207600000da80070000510030908503400d0000280780850080d8036000c0c0b45030000b481485550500c40911200c40082d141d50383d10b16031910054110481220000c0c070b070480d104800c17120444401d031401007800d0f00c2e03001c0075401007949985 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 881424964 1250 881423714 881423717
    0x15090e03090609040b01020106090509011a09040803011a09100f0f08090c130207140f0f03030108030d0c030b0d05031305060f030c070804030c06020a030906110d1206180615020d 78
    0x400001e00f050001400c00750140a046544e0b8440109000c80d4500c9128050080795000261141500f40111042c40d0500a45440f59060700d00b0000040d0300700f01200e064030794409003041c00a544a580036000e014428586500951103951014902d0344a092585904410f1351603519070b1300a03040c161061f400c155072500050300071940d29145070402c17125480c41da480c081c0d001403412580740c07101080c070449a4288141a0031400d110702812504025000c80540018061441c5525040710550b492080000c0c01111980b20b0a640b44081d000c0c1e48040074824000d080c0354001e210916000743c0381d500c50b00d43c402804840e680e012a003814800190307010270840c042224910b4a50314101003141d007050741d04445201c420440400001c0324070b22024014512500280340344a25440c01820341e0b020303500440308102c8210080d40340c4190004034441c901d800c81c103084402441d510301660285c01c5030303041004015051074a02e2041c1010b9881f2001b112900840000c42d254103080c00c81c2c4034003d400f41c000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 881426214 1250 881424964 881424967
    0x609031002091302040b1801080925030204020d051b070506010323070f18051612061d060a050102060603060118090c0806180c130e0c0415090e030906 66
    0x603000400c0d030340140070341c48004022000d807801108070a030a07644507810245000101103688042c0c140000c940b0201030609081803039551414295560b030300d000c0c181351160000380c2d501d03c035801c081408608001868018100b9555003040804d1400980b105031420f00c0303100450030351034540c1800101603030011a4800c0141110b80d107191140800034101964084202054011140d000102048624020b20b524101400350b44e107031210004102147c1c1404100c40703810310341000b020342170f5500350107040f91160600c01019407000844400a180940081010118480d561840751455104880c4a08021504000d509850700c00481c0c9951003511899050303840500180141c05404101d08400c410a54001420002c00c4d166112080090340c0000c01941110301408901c03c281c1100800004582d4010b240d40350840010450342c6a144002180c1e003640ca1210540080302482105030f004001030051040d4580c0051072208046544101c1c150249072a019000100002c81a10030081d03004000d0b9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 881427464 1250 881426214 881426233
    0x120a05310b18010216110d0210030515040c020c090c0a140c01090803161e1d01021e1e150103020d03020a200f010804020f0f151c0b060903 61
    0x1001d04a01c06803003410540707066840a107031400700b4030140c0308010058030071a001c0d04140c203128060b030f05101407107401911040080701c0541ca652076031084c0358032a4600001c2680d0345205280058102c048100d504c5801c18525420745a400941e40708842d0003102d100009440744081a105803240500100200c0c5808001070b03880f000c1d500140c02c0702040d800000c9010281555145c455501c125000c00b000c030b01c481000c0207101e034007070505064007032100e60031065200040c401a085001d15600c0000f08000301041918a910a2047d4048142d5519a01c02c00c132009591040c1c44400f022080c0c08208042107078100d1810000801ca0540c03084215045cac0c803039086409001c20001c0c80c5409074154440c03407c0c0d5500198044a108504101d849000e854401040080114600c4506a0303681000b090703500b80400750303580c100c0c0700700748520444130110b024902070702080c22561030034080045940003240c10203040c0c40303400b42d5010000c1900300130040c0380b0224003002168022010020f800d41d10880d00d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 881428714 1250 881427464 881427473
    0xc05090a05010c1a011d0610210204090501091406091510050f160c0503070f1217031303080a091a04080405030106090f0501091e020f120a0531 63
    0xc83e4207034000c0c0b885401100b4802030a28880c1000c0e440f030103510ba1800c903d8a05d0011000740260040c50480b0868000070702043e00410716075000401903091101102080301550380350741124000d01c20200c00742b0903580d441402000404030f400c1e086554025a5001588600e1310240e820310500145100c10350400030b0201b44410201c040d18070a00b03203c000c03c201140402884060700100c5c070700d21401e24001d4440d2906030444841a840b140c040d0b80701c82c005104258040ca0544107035003031402c060f183c0100700c0c181203000e5410480d40d410841000814070a030310300107000303030302100f0f00036101c0c00d00741e4441e080320f08121040054080c204122031551700004c400c0c1c0030031168105005a40ca00c1c1000d441e403001900711001c1d60700c04410726036a414400510f5186d40101801021074110800c66000040da0341a02804001c407a0b01d0100c2d0700013410402c40c107001c0140c0300c0107207001c801c110461500070401e41c01410295640780080110b100785101480344104040708505180d102e03c580105255034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 881429964 1250 881428714 881428727
    0x2011d03611104051e07050d1e1a01020d050a0305060307030602070b150f0904060903180609051311090d032304081006211a04210c030203091e12010507030c05090a0501 74
    0xe156803589601a007040c1100c20301501c50050382000134ac1c0c1811781e200c82000d0850454000d0554004000e441d5095400c007054580c043d8960602050355a1100002030600d4020340005000302e101090b10070501030000340c8148a42e50600c2e00a40510b495010894208045c03011940e00124010000380000e400340c02107001e05111b0309001d01111b1440000d11020380381c640081c0e00083d0b03040030800192070410040000580829410042c141c07008000e01d0461045120241c05058144811800c151141c1d071805001c0e41208111420b4031400ba22a00c400d40c0103101d20680c0d48100c203030381c4000398818865407085401084031125110800c4030818007000460b0802e031024a91205081c0344034440034492032003607100343d1130100c440400443e1041c81000b035232005ca0801c141c0d090a2300001c1e8001040f03580c20b00c0100d405d400c0c03900c80c040300218000010001c3c5c9400c0107180010496000e4150406801000140c40c05c0c000d40d01015000c82d801e005103c00301e43c0c0301a1100040286501441 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 881431214 1250 881429964 881429977
    0x70807081c03110c0615100804020907051308060c0a030b03060907140307050d1103150702070e04061e0f2d0c02011d03611104051e0705 60
    0xc0e402820024048401428004100c502c0b482482042845a60615215404664402940c180b503c2343c0d04103500820105e2900412000c01d0190005102c880401e142c59000f0041c24640d00712050b514083c00b44d50b14580040c140302010908081000800d880c0103c2c41a00c03401409008090461401d800074034103501c0302c44010341500420307101248644410489942c0315010303080080c1c440b100d120600d0700c0c140c003440c0e1408035068510207200007164085121011556007656580b015151400d00b413008048201c000e0300c041c1c0614001d4051011190031420005400000400806400d100c00b0400c6200d50191441082c407850001000069194811500c5030420720000901044c40c01e01080b00c0181c4c7c007600242640301140380136441c0401100503800d80710350b5289110380e009046140000302c02c0c031915241514013200713141d02c91000b9811401700ae090190910303042040c040c00c02d110403810780301c400e034025410a00041c14000344203c06d0701c035508030103c1c141d0660f6182d0100b19141c1e08900c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 881432464 1250 881431214 881431241
    0x3080c04030b150a0b042310050d050406020d180b09012c010e06130b090c1e040b101d0a240201020409050c09030f0f030306010c1a0108070807081c03 66
    0x80d100070035107104c81401ba101a21118000002003080002a40f02c01101c00e041c0b03611850301c042c8100040d9a000c010303251390542c2c0d4500415a61100c1c074081b00640123400c00c5000c198034200d21181d880c510902d1105006009901008181d111a4080740c00e0324000807180301d88a100e103460040c05050714510020580e468000001c80d400031250700703400d22106540380310414106130340c0c94007402f22000d036054011492000802a5918400104425106062006d0740711081c0b0900648a5215074000c100f940d0402000304207072040300c1c1005001a10051500010502071a0510215040401e880d80644040c410000801401c84040c40d442c80160080c4c1402c6540a02c80050008080d0090300d004295210803d61502c0000c81130600c0e01401b10303402c0319107500c020f5034414001d20100c22250020f070700b0718010754a01110300b800c0e00820b010411441d4915100c90000a0082010410906851b80c0c05c007510f0040c5d50740c0e05015034800c8110500050021901440d01455000748e00240500e00d61 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 881433714 1250 881432464 881432479
    0x50709140a090513021203030103050d030b0612040605090c030c060306042301090605011d010903062d0501030b0106050a0f0e040b030a0605101d010b0a0c02030706030903080c04030b15 81
    0x250481481074903400d4580c015031004c6606100708500c5d2103c2917032164040800110b0a540c51354482e1a0303190ba404200f402070542d101d450186a4031241c00315030301c100745180c030b03904a41894900507000740422101014903000b060002c0c03520f0700d004901d48807035000051129055031140c0081000400c1c1c0340c0012140d92843e00e041030003200540c0441d44c007e084860300010400d280600141000c80a081e681c903011000c04c0348102140c5e00442c2c000c058a400a10020f502c4101c3d680190b10101e49007032048000d00c0780b0008818114a0342c10080c182c0e48183e01202441e40e80c0d0038251094061a102d0320041422003550300e940b2480340881c21090742e801040400c0d41c01042010a06256000005492680d150b20401013000a0f141300c60000301104440050355155015414540f01c0d01030068001d1084000748608085124015007520300d50000d09581c5441d075240b034068014007003014200c2c08030b0800c1001800d0300403800c05441c11250401a01c2980d9900c861700b840390a0841c010140e0311845 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 881434964 1250 881433714 881433719
    0xa180605130b0106090f0f210203191410050603100b010c02090c0703080601051303111503010e01030507120213240602030904151215060305031c0f050709140a 70
    0x140b00b94810300814241d26440125400c00f4103189100000c7d421125006440c0030042114000381c6090805d07003540c9110381100d40302c0e50310000b41000403005449805421003c0104188a190304604900c18003d500321080742d1008900b240540d04100e62566254000441c00700280303a041e001130856200515007544060380d2075002420f10182610040d03842100800c289041503001204903801000900b40b0505107051180b4034501c22840340001442d02a102c0124016a01c03070300c0982c1c1390798118440c025180d61315141420164103003488152950300c60350100207080900440415140d0760040e0070446650609820940640f09401d080080b5843c071941e81d400004c080c08a01c2c0c042c0943d42c1c061541c420307411041000307603008281c454294010000c0c00300030f4a03644500040d107442d80314015072140902c00da82c2a00414241e8800b80580c0000102c6c0c861022189115100b4841d03080f404202c0303d514000300c102203400c100d85800203d81242c81c1400742015140007003414010040030040030360b4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 881436214 1250 881434964 881434973
    0x3040b04210c020f0121020f120903090325090905210405010207060206090a060e070906091e0e0703170d1503051207080405010f05190806090a18060513 67
    0x41c585250140081c107040250401c51410380c00001c40705000346811b08141807481c0035000c25486016540c080d082d07000400304184181c080950381c0343d100d140303507000e854640059a10707207a50100d003425100e80113020000100b42444101d00b8086140e4a461404aa08080d5500020b04505130152018401c41200d02e183c00340da0320014011000d084020381d103071441d11001901d015414bc0003030081d504080100400c000000818030a03482e008003000c2a601c0081c1d44040c10b022154102240c814200040441c502c005a00881d1403148010380c401c1030300819601d0b100480b8100030310604e0a07007051400304042801c84500208580d00359255910301030385000000700301d0301100701d070101a0600200410034442c0910008034030000013004c082c5030620b103076034840080c851030081e103060020341ca00c02600544144281c420784200b00c030744011030703160511000d4030340c4104a9885102d010a0030003d43c3c5101180540104001040403010001c0f01c03995803030018000041c030072203c1010b1141103a0106 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 881437464 1250 881436214 881436263
    0x510030f09030309021302281707031b03050405100b060f0c160909050706030c1205090f1006051005070f0209010e193b01020301060e19030803040b04 66
    0x6900c03e0320b000a900c10103106000b11441c90304103070b0000900c18005001100c1c0b040d82c02841e5210040c2e120321038007452500c00e80d400c000844246600384080d204100b51142c143d84240001c03000048000d20340588604110142c0340300329001051a0000842035141d1249034000e000d100c0d60050900f0f04000c80305003c03400c0c0f83c000022840440e4410700280d000d03090320241c000c0141602d1001409800d5103900c406079280054800c500405940d6000c0020702c40c0300340310581c2c80d039148407403c2c07000707050400c586607a6070030501c5041c02d54003403000404500e00403407103032008032440501500c172007441c0d245099503143c012000554001c10f0005000300180d580390705079406404040c0511002d800d00da0402861b036a2541040c24065142c05484044141500d65908403038440d04142e244c45503120071441c4104006442c800c0c0b15600202c004640590072901c6481c8030ba90940387e290440510f807d407100d00c24031074070000e0701c6410208080741c0442c5181c0c5d00c0c2c951040c01090070707009030040c4408400c4413 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 881438714 1250 881437464 881437481
    0x303160204200f0a02010b09070c03020c01080f070e01090b07140706030e0307232a010305152403010303031d0a0209010b0307020a1b060207080303010f0510030f 71
    0x1161012025045140c02c2c8240b80102031000148031001d00001c81c000c940b440344001900b11250701040303038052a4400d402c40100004054030100311030030189005000130794409001c502600440c4c1c1741014952141c101d8911800710311a81c4007040e11000816100680521110790401c42d094502140171600b460051242c2881418003c00e80a00d5018042c20541348e90030000415080c26401c810202000040d1603030945c000c0081405007174410b040e03881e41004a00007120701d008a586d0391440d0402040c0700b40200910032041c440c2c0c0c1c40b1002c011011a0401c844180b01d62184400101d171500b00310141c0c210040007910b40540c0540b02803054000740d042617004400081d203c2c6c803045015005415982c030261156401402d18a115500203081c1d01d8050058600f058000f02c00100306078070800150a94079040304220f502080e1082c10403110041c01d02488001d0f100345040004c0d94480001107070f0480c0d00018001d91454100b02c00c01c1000441401d0041c10541c031251810380d8410b031441901507 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 881439964 1250 881438714 881438737
    0x3060108030307020d09080304050105030a0b041b0306080a031b0c03021203040504110408060f190603030903140309150f131202041d07140a08060118060e0103020f01110c0303 77
    0xc0b24646500024580b2071014003030810095904020001c03a8000010f07101510700034200326461ba034404201340700910308100b00580c041d04021030700d0310b1300f04d4400f0011078030342d01641c0c1070102d182c850806030385d245281c03a4010002030026800241d003000b45910103032260310030031401e40440e640350001444181f002c08494032070741002070100144d1400b4400c1e010303c4401611903d007001c1c503018234240c550b940241a000d83d528440005030707508851903c181c84651410004020058490900420304c254a0004549200508411402e484400400d48882050040450440c0c480d40c07d502a1650010090494154070901001c500c1d030103480c5800005e030030011050240445a40100f00036a00011005020801c5032000b000c2e00741404603443d8280c0d40703c00c446800100c0800081041418541c0c840712003409044004181c024601384c04203d0111010005d02c005621422400176503c002e10000398850132652407e00c9650041902828042d400c03400c0d500c2a11118012070304650200c060241c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 881441214 1250 881439964 881439967
    0x1e040f0219080f04030801030b2a040905010506120c22030b1f030b072303041b15050304020f2103090a090510061b06060e0109180f120e0306010803 65
    0x1e0040360311458041c1c0c000303880c0d40000308905203500d014044076418000034040400d100f000408003040082c25940d54940c203206094000301c51407000d001c60b003107402110720041c01c1c130000048602d402c1058840c401c0688141d803003203031194004030000703a020311180414869038940540c0020355180c4104000e50180d40049054544240c00180d007400108800c40080c1080500340040740002803003c2e8851094200f9000e00c01001c10681c0c0d601c4850200c1240c818000001c100403c40400403940d455041d626028403c0f41e110745804504a610340d040d40000b47c0301b44002409450400e03005040004080c02441c00a850901a400c50314080c030520038076a48000348030340031802c2c022040d80003400c1c04401001141002036061501107240e114620410551742c2106d884040300a41401707009a00c07000411803559100c050000c03000c400d10401200ca842d20700c4511103070702d21203e651042540306481ca400300c101c5659298140060104403c2001141071804805072410004a80079264100046 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 881442464 1250 881441214 881441257
    0x7150212070318030207060f09121101090b0f460e0406060914012a030e040507022d03070f0203060105040c0903031d060304210503061e040f02 63
    0xa01510b5070032901202d0100303c04081c00200381c3c0030420b9800d4689030702e0820155401706904440c03000c05070b000b20702000c0b501c0e01c0d441e0401001d50b004503121042a02c504040b40e68800c249aa5405402c80d440b0503204100504506850240c80414800c00c4a27207a03201505000c0210121200c075501400b0340c80300301aa0f07048281a0011010380514008407024012281088001003007070940748169107408015040c8001c0e03581c001d8400440c0705099485030302c60044076034014032815080c0d2406401040580b40400c4881c180303400341c1c501ca03000176001007141040c100b403030f45d007840d0744498191f40002098034070041d4902d080c001070901e980a043c83c1c50000b03403107004250420ba810b034881c900c83c03071400701307500c00d41d41e0440525003c07a505030030640400f15040e40548114030301c00c0f440a602480c0041004200b140d00351071003680101c03640403800c08889104c81070b101480203072521940451484139250b03441601101481da8401c02610214800482058600a0742c2200240b0500158628280c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 881443714 1250 881442464 881442467
    0x807021c030b191809150c0819110327070602100612030e2e0903031806020304050d0c08010642050c2b030e03031603020715021207 58
    0x500200e02c81d07909155140504e000030881d40204501c12006840380c6405d980024080390013083c5140d4101e008007800b608903110340062040d07204440c0040c403807001009000d0008224425001e014003001000d501c0e5884e00250308550410350010000515040c500c240840e9405101010007017815030002c0010030000d06e0042c0035904070f0303041500b1900c1040c00040c003082d03100141c007046d4001650b1342c3c0124040030528001482180d800a084ac900e410301d1805025400311042c0200c034000e40c5e41074942c42800310b1303104401c00c140c071445006a10900080c811440d0141c3c0c421601c81c89603003a495060b544608840c02d4401302d03072003211100f000041c0302d1041c1c1542c1079540807100f1030443c0751300c4040d08040c01d40301031145081740c0f008010011070f1384040c0910820183d5030468508002c10218450410225003684071612036000103070034203c040c00f0400c80041502c0c080c04100804640d0003c8651048009400c107941c103079a00014413800c1d050070043c0e880240072039101c0840e8211140b0f44a00c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 881444964 1250 881443714 881443729
    0x30901030c02030913020304230c010305091605010f0201061805071b05060f13020d060e010e07080a021509090c0909060a050609040f02190c12110d0807021c030b 71
    0x4041c007990401c210f249820355601d89018407000344124010b803a61101e0414500300e032401c0c0c01031441c2c041d9144801e0400507000400d00c0903001c0c01d90f8240515561001c503d5290000d50840c0500c80745502c070b017802158003920342c031041c40300144000548155202d00c0080c98128100004050782e85e03840500c560140c0c01581014005189284504009541d03500d19a49110007070150424000d0040482d0080b84c8001700c481c1c140d17800801c06203009841d410450020566140c0c102d02540c038041c10300151005c040b41940c1210585000b50208101a8090211002d52003241da80c5031141001004c1c580d907218000bc5004440c1d04803070035212081a02804000302014290301c0c0300ea20f40407420456552264110f8034000419100440c80305c410f2125a4060302401d00040d502c20151444220641d42c02020010154090007004060f803030743c52000e4611001c07801c620b1109401113643c10402c1406840c205811210b0380c81143e01000325483c607101c0109911010f0030000f900ca4541e26030501c4c0c0701c0c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 881446214 1250 881444964 881444981
    0x60c0c15071b1b0e07090b090609120318040c0c030e060c1905060705041206090c080d051210051f09080304090c02060901050c04050103091a0c0a1d0109032a030503090103 75
    0x1241d090082c03d002e00701500000c00387c801c07801c68141c0064072403d1070305d43d0010340f121004007610384442119155601034030380c0c12064042c401c00b2070203202d0851303030301d0300b405118098001740d116100c8010098404680d00390450408031b400c40b10403c440d40c0404c0003040003014400a140000c400d8480c0b6142050804d98040c0c61082042018002440358400a44940b140b541d40400000344030590780c90109805c1900d580701260a0023007040303030206544c01078010136070050070030f42d40035940da202e07441e220508402d8080c40e40c000000c1d0001c1d814158003000080d000b0b95250408151040d41c0e041610b00d150300c140c000c4905607488501488500303404204c01500071140300c0c001c0c041d903d8404207201c024081c2e84100c03810113884070950b1003030045802d040814a4050300e201c130000d1410070241004c9500c0004100d0016801c00c0056100742c5000305451040300381651185100c2e0b02d96100c0d100c44010307210742c403031001140e10a02c50380c1c2681c1158030401584030b1006141c540c0c040000240403a615103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 881447464 1250 881446214 881446229
    0x31d010b1201050417030702010f0c05030a0f050c12090312270d0e011d040204031406010506040b030f0703020d0f060306111e0a2c03060c0c15071b1b 66
    0x418071001170b51054891200908140322a0344030364484000320302504000c0070303440419160000880c0d02903403010045101c1c5001c80030502846000c5130100c41114021030302c0280e40300081c8440e01c80c4a90300041180c2049401084a0426482496102811505465a0302c2201c1003483d9801c2c0c0120009030049051035034009011110141c280c054000749019002904001c2ca5442000b0300340251140040c042d10301a1086448980324605080b2803008034041070405c1c8a0000006245c2c40c24404a41c180d4914203015030035608c41d40c0300c01c40700410141442040c10b409001c850520445071140d9101a0204000821300a10790b0900e802100c00342d68112032145420071000c101c2425035284000c850341c41c041c1c15a43c2e8070b03060004540d8035681c1484008051900c0101d11658000c024183c01d800c0d6045055a1841d101c0e0000320b00ba51042d2035024015401142452a40c5d03001d48000355882640c0c0c1c140710340102e4100b842d00d410007100c02c8048543d05000980700300815068080c14010b006103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 881448714 1250 881447464 881447471
    0x150a0506031303080405100903080f15030a11030336030d05070b0405010e0f07060f051321020a0b04031502070209010e090a150b040b030c091501031d010b1201 70
    0x42d480c4044500c542081c060144042c18010604200301000180d512842c0d40c101009001d4403440c0007003a204080d280a007801042d080820100200825000080c1170020018054020b0701d544125509402480d010b90601042c444007803126600807100344a0003102030151008960040f44045628000c02a20301a600c80d1205013225900801200e22658112201011669136850810301400d004d11240300203000740c5681c58840c00f03000402c0c03c2030b02d041d038a41002d000b220500840705e600510320502602c01d030314801000600d01e900c7c4098207031360381c0c40500c0b20004920380220301c0c040c1e1190300041142200085c1041402003810001c000d001581c0425880d0102540003d10741d2007040c001c042e070300d01100020400342e103001c0149085035070780321100303440810046200c84010a40c65030071500440c140403030348078589001300d0070303c0c01140000d109000380e444403107030110003e0b1190001c505040c0c1e1480340451034112140c0100b18075040c0000071034910044014031121100360540a641c2e13a04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 881449964 1250 881448714 881448721
    0x1006151716030e0304090f090b01060201050412050a1101050106021f2a11121e070f060209010302040b0d06030501060e09070303050304240902011407080f03060612150a050603 77
    0x31502066101015103240203d401c0d121010001e00798491940030840e01c61a000d0911700c4501c03544c0088079a2400390b0b08504180e0381c2c800c0164203850003280c00805c00801c15400349441800750001e000e00004a19001c0e506000340341205084032004e820000240e40181c081a8414200c02209105084101c4c3c1c1030000861100c42c000281401000c8a004c1802c00e41c81c2c494600c0c031500702c954050401e00c04840c1e6840440c810700d030203030384441240c0c08e07032140900c07103948041c1d402d10881d044940c0c480030242e491409512071a00035007210b15402d042640800002600500441c041e011903002e1000001d0100c0c030b18900203084410b55409140519402010042021008500842240c0e09030603d80c0d660303983c52800350400001400500c030301003c0c440310401002e050381e200c203102070705c00c2e22103900034503e50100c48000d0045103801003274080c1c20022001da184c600740c0034640000000d0480e078281200840c004004000c00c03220b00c1c002c1114200743c1c6110b850002e50301002003405840e11460b40c00d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 881451214 1250 881449964 881449981
    0x1a0405071707050f13020c0d0314071d0f0109050d06020c070e130f0f080318010e0616200a140c04020a0c06052a07050c0402040f1710061517 62
    0x7546222144210005070702c040e170900c40e0350101e62040c5013070303400e458030241142c102800600d40300c10342007016541140010b00690150b41c0c00c004d40005400c204200b09d2200301006140000c4481060410244220010f000d884039680b0300d200d20304c250005600c1e158012046882d0810a0744000f52554500c0140a061503820711214076480d080a0741100004a0341450b0704010301c007480c000c01840001042044500c131240a084002600500074424403418010345560b904003603a140b10001c00b00d881c40d080090060b1508030810710400c00501d10010718011085c00d2407940c40c41a03e01d03081c020a44032000c002884282ca244000f2a130450402683d41001002c0008602c0018405903455021440411812110b580d1500e280304400c04500e03800006400941c010784000c40f6130344a41c0100c03c1c00352403c0d0094500390360030a46189111131030803401c134208816001c16100e070b07405201d80003207410106008000c0034100031846031020380d1300600e0091514990450b4444000a56401e00040c00c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 881452464 1250 881451214 881451229
    0xc010e0d0f03080a0e0d090303020c04090309180b03010903090e1018050a0b03100f0605040501030f0b1801060e0f06040905100b0f1309110316030209041a040507170705 74
    0x96014585500c060362842c4c8620300400700344a4a00080c8501e074900d5455a0f401a8010162841707642900d0b14801d18009020590724140c0c0300801152003540d00b403003807450640c035a02042881010101e01010312102180c21107010341000d4000541c03902050120107135202c1020b8102800414800d1070070700d0185410541e400407030b110121242c443e00424003004454100c0e4650900080075130310f4901548604000502075650000c9440b800c000c2c00080e646454880d0302d04a94001404080c42151030b603402d0006440100708140c0810b86034010080000b00f4490030b000b400010364080384d14101a5500d00180d40001c124520441c145425030700000c8000ca422440c049840c88081000c290f1400003402c1c045a10042c15080382c000741c070b000c6820320640c00010742c05020309403160644001c4030600d070712185215445c500c2d00d07050500070401824030340344840d4018003c1c2c203102904035108151251000c010b40c0c083e1410750050f4810303c00a102110610301d800b003804001c0c80b1300e03460000400c0c3c08 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 881453714 1250 881452464 881452493
    0x8030c0325140f1b061606110403050a02090a0c0c02040b0f060d020d0507030b010918020d1a0306060307050307061101020d0612140d080a0e0c120c010e0d 68
    0x1640500007444800300001c403070704401d06500c0510101c03500c2e0803440c019501d920500c5226440c1c414031400f241d04005128925032041405080b851410807108025880c61450354012140940e4039820300104402c4480a00050741c0711303102508203000d280c010400010b41c0500b211a44500d02214581400e401c610348004603507050f074000c10014600f40014840c14030200c032880e0003da0001c0c00d003802c0c454903070003003070350750040c0c1c10810003516400c104600310382844e5210380c0802d54100e0103110205910204141050400b2009898170210030000020358640380810300b410541003c80249a2805000e201c3e80910260700038084146460f0000365680e015100b0002880070300480c54000b0300e800e40442d0081c1110038020721000313a84003202151408441000e076180d001d160121450f20202040800b103402072a582c0c444280c40716241d0030004d000c00d200c200d503140b181c16101c4100361924070180c074948110300301a00855a1920015002500742c1181c01d214035018081c001c00100c40c1c1e000c9812 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 881454964 1250 881453714 881453737
    0xe010507110312130306060f0b03040b0a150905010302030c090906180a020d03110717071404200318010603050717191b2702090607170304060608030c03 67
    0x740000700c002090918000075001040050005509103204d099140b00b032048a2003440c00b04180da070340b14059800712134035000d4098090b20400c0403602143c00b60705d4158002c419840300140c02c0102d01c0c3c50304a0080aa4400c0d078901d9105d20041040d807805000c840080041a64a90341d640b80112000b91510002041c403a080c0d0042280201003010401030450010b40c00f50640018103924100a0715020320340c0c800c6942441040d401142e1110050300000b00000140000c101080c18200c00c0000c2d02d50359202e1030b4010f6580c00c5090150444000b0682d203d0b01c10b880450b81d00c0c10241c001c400b0a00c085000c1c02200c3e0b041940c02c000050002608000310707070501c84c8850280501e0b03039210b03040c4440351a2042c81d81d180304040006000c0c59108640741d40b0104544400c583c1c0d6200d034100c00c51801c21540c81214515a040b0b040b030241103070000c206030040100301c240785c54055500c00380703a410081c80468602c1400b00c100000c1102a01c0b60402401000c4000c500740162004003070303940c1c4105a00801d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 881456214 1250 881454964 881454983
    0xf1d1003060c0219060b0405091b040c0e0306040c080f01020906071101050909010617220b0a1d060a0e0105010e0c0706110c0303062409271003030806010e010507 71
    0x204500c24030441c1480003620740c20300f0480c865820294098100700003000d20580c07510340407134452240018082800340d10301c2003402c91507581c2b10801009100d20f0040305c5c140084002ca040560313409200e4984154072540a0b016841d007048401454280c060300843e41c50380c030400205c0d80560b91801036170322803030340840301c11780b41d0790004012036507400b9803201d041d0003155440001c00e0180d00407629409c0e0b84084180c8030140e0740d03540c25441c00030001144100354103902c0341030307080842d894400c1240d22840c0301601041041c0d1196220481515400350704029801070b80c20f002010b002c5004070450480144024019941480e00c1180d04040c040e0001407075110000b14801003040c40d400c0070384541d410702d41154440d0041592152203901c04c4841501c2980c0e00c0c0091503c54000c002d10b1540796072100a4141054420340071f11850f04000b900d1540022020003d03540100070028036a4403070030032a00d1101c891491850090090b600c090056411b10020740c2140d0020b9a000c819502c02c0c070340101440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 881457464 1250 881456214 881456231
    0x507090f270204080715030c031a010503041704060c05150405030306090709090603111309080301050d0606030c17070803120a0b01121505030f15070c02190f1d100306 73
    0x20710080c0f043c0e41c403140340d9018007000090207040c050420103000c2d007961401d0100ea60030003000c600f142c424081481c0b004d003c009869407030b075100d10003944d440340c85040d208103044251044820550000d9002c02c000460150001c1e0401006000c181c09202084040880030b04240d41c41c2e80d242d000c000e00d614051500500003c40040c40b448000300100b500401c00c00c00103441e42401892000b40800860140b60340e40c0745413a0741c410512030450715580001c603050450f401e00f42040a074844000080c2c8401da20385002101107041905444024021003d01c1075450189003076081c10940240d11094164206024100445840d90615a4003c1100c87c0004031050b0740c0c00169095a08602c1c80790100e0f19003034038034024410004401081d160708408803000d0031007070702400d03075a0148042308100180c50000800c8215000d06560413806100414603c600a80e48200f04c000d80d4407030340420440500344504220129180300c16840c184074030042003000c4c2ca00032041100681c640d100040ca203d5071101c3d074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 881458714 1250 881457464 881457539
    0x140f0a0b06130801020a0e180103030318210e0607030927020c070609090606020a020603060619120b120d110309191a0a0c0f020d02060307030507090f 66
    0x201e812020328402d148102c03e03241d600041c001d400c24090310303010030041e03032000d1510300d0682e403c0c0c441800070050340e0282d6829641d04801500c84103d0426490344105a02e20004100d05030003013189546030184014a0400b00b40180002c8910084034052441001443c0109521a50711015107014266000303001038500b10030b0901408004078002d5079480450100b880e060042421400c0b10041e6450b1003006880300c0003003007120380500c10704015070701480c58140141055406950b021500810a60505c001071a580f14201d1000240b100080e030700340c1007d030580700188104800c00300152640103c1c1f040c0d4410b4595201801d407880000d0003613100130b00044407420000c0301c3d40288064264a1848011450b15680000c140211513000c0d0340b0051200b800c1c800c1d030040e0340d0044129926074035020300c141c4400d540401a40800d076000248001214090707100d400040d030040d0340030b81c1c0c00252807071700c05001031010b121500842008410404c040012904031400c050060800643e14800d10054040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 881459964 1250 881458714 881458717
    0xb10030213151418011709070e0a02070c0612050901050408091e040626010c02030919080303070e1e03100e0c030604050706111f0207020d0c0315140f0a0b06 69
    0x80420142c640002c4000341300b811100d00002c200ca080c0c07922400b401d14001c18000c0858112240c1c80c1a900c002c1c1c040041110b8801115040000c00400500d800310a0f15117a201c04e542e42c10150100e410b01c0c00e0b03192406103900c246507010356403600800042c1065034441485201c1c40e078036540700350b44034034190002c4000714502880c501001441044244d84d103041e000a000d40114270360141d0b800c0442c3c034118021060154242c14800350340907514002c00c210821810041c0b1682106001403c04000b1600140030401140924100e494404000401800b00320300d00d1000035a010801030111070070040380d10000b44c0340c1c01040445401107405c01803090103c0ca40b000c860050b980c140318541c184003d001c40400e0740d4099a40780c0d6155500203080c1100c03180e0320402034441e501840344010621043c00350b40d034040c3c040300d407000f4101790a0314401c0d110b0148850440d0801e0300c28610f50149161012483e2107060035954204003260660f107400e02e10314400da100204500e012949030040001d06684110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 881461214 1250 881459964 881459987
    0x120a0906050307120e01200309281a160c0b0606030901020705060117070609032f0d1a150105030606090406080d03021e0415030b030f010f0b1003021315 67
    0x1c01c2000c0705c140c003080780c081c1070300014119480514041103940e002240e401c0305c3c400c000c6940104000c1c147c2103081c0c151000c40010f002410701900c4005030004020501030301d0690010b803200074050a01c5480d0072080509400d041e001d1128216180e03000444141100c1e500600840311a41c59940c0e01990320301900c282030009105006000c004036102d070390001c42681614015017211801c548541042d034040310b4602001c0c1400341c1c0c50710500d83c15020706140201d10410820704501360149000455010a1a444121030303040500302080c007a0320801e11020b030f104100745041d150719540c00c0c001074907034070010705058001d0300002903001c5036803155005007005018030f070100c4505d112040c000900940180500521030b11403030045810440b464415181030382c2d840240f0a6080241090170360050a80752611509400380004100e12030200307225034503c0190843c40800e03052070440401040a20507803403e8245841070080c040700c400380031a0750059860350740c8809003d01c090501980c0310025a0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 881462464 1250 881461214 881461247
    0x10b0301020d1a0409030507080309031902030a030e032a03130f0e010902091302030703090b0c1309090503070f0c41010f0309020a09110903120a0906050307 69
    0x602d0840c8840283d00a10a8003400c081c1d0740001000e410820007502c0c01e9140140001da0180320441c0841c0ca002c3c01103800007010411240344c07581200c00d600c0c605201440c43c0c0c02503000405d03001f40c244c1e003500400e4603107840301c0081d602d480d840e0600b4000812084c244100303250105a02c842601404000b1144110000449000c1007950762207000c860456a02400c20301148a02c000103d010460094810040700100b4408020303400301070035030080d000140039004068413285c024002c1100e031140c0a00038103c1e041180c0da5520901c011307e171001040c2c1d101c1003101d80b41c50030701400f1036004400e841d28103038800c60b16019418541080d20b021102c5411801e11078070b2a40c04001100c150ba035840b4084c06a1001103815040481081c5549a680c9004940840e83e0841c0c0805111b12951203032240d44e1000380480740307890704d42e00380ea021144405c1c0005182800080c03200c0051900304050b00d90f425081c4540340c54140d8810b0010890328481c4a017200b40200400400c0449020300c40901d240d0481e0f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 881463714 1250 881462464 881462467
    0x100302070302010c0356030708070b09040203040f0f060e07061407030804140f1b04020310140d21140a02120a1b0c06080106180320091f09141503010b030102 69
    0x1a518406c0e80349a0b55143d00c284241440000d04a00102e09a01140e20852140f420140218244000781d4402041180c0c042900404400014440c88a41540e103015940024455510118861070080e25811103400d0010100f2840d1003240c16108980701c8235890301d040030840d21140303008030800c0348c030030320b200041d000d601c000440116001481d42d02c16202098030104181c2040c090004074803007928040c10000740b030311090080340c545480c0d1050010010f0900810b0550a44a801c007030041000224030103540b140201810076030008520425103031610540d490301d0354009019503140c1850304003400411012400410060043e50021400c0c0284800c840c0d913807510b1701c0d00d402e070740b80705c8e0091401040340c280000c1410703807240c217901c869503c40c50761460f250307410343d02c0b01c1d0720700781031a20f4461003a25502901d5840751a211942800340c690b14406403464000d41c900301454400e25003101c0c0400c0c1c50061201d0f40346140400f450340040700c071003015801884940c0464050f140034402150950300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 881464964 1250 881463714 881463851
    0x9020d0c03080a08011a03180c0a0e0a051005011205040303060f030b09070605090f0d050c0a0b0c010515010804031b05060c040e0105030f1f0605100302070302010c03 73
    0x40c2c800051401c4212591104501ea1320b8050403000c034683c162182c868100180002444089500010748804405204588848031400b000038440b06803900f00b410b02000c681c0c140583c66180d805402e401c008984046410f00e424500000c114800c6115100c07000341e20f07030700441c040c54001e0b4464000b0300180312128800c1d94507803c042500c0102900c4500040c4584030000840512980649007080c400614402400c0b00c110f0410454101125080e120f6018651003010a0ba507000b045c1c100602510502c292594100005e040c21550000c1103da500702018510b940301d6a800450075510581c1410681101d000247e0411a1f0549a240c014064400c40080c403212501b414080c00c1201c1040c2204a0301e40c0c1c854040c1915007400c0c500c11030035540300103804440310301c00e0444191110f4042c400010f50590307070b40000c3d120805440004011075800500c01c4c06050742070007100c40240040c281030080e07000a00c88800c20110009080d2400c075002d64940108100c0c8809a018a00c0000b0209101c80f8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 881466214 1250 881464964 881464973
    0x8040f1208041e02060d020d0f020c070f06030204060c060c0e10030209041a1e1906030209010801091406130e030c0c0a080d020c0f0609030d0c0204050a0e1009020d0c03 74
    0x400c0e1002d0303842da0300642c00b01c1002983c03002103d4400b0743c040c00060038211100d13038039006508841c0611010710384540e00c580040a0a102400110308140000c000503480c02e11100406056608044209401000300b48000c030b070040100c001c410740c0040002058928040c00f20b03000418240e0300c41d032040707129401002290345038000e89907501c811502000b00301d046064146207281101d036026045034800c4d8800c004bc0f0540c41c040f07185108058910b00043d80840c030380c50006200c03070b0048404a98041403040c15543d01070794840c0540500303c0c04100e011040d881c5213041030001854144038502d405c0350040d440c1074a030000d83c04e4000c402c0c11642c80d1985441070ba83c4030110001c0c0c150281c0c1440c80c002070b010800181c00540000160044d0509a20003030622041c041d07480b14558101d101004031080d86c2d201008242c040300119566a8100041881004140c1c0c001410404070103080a810500d03112011405c07181c2c00265050002c0c1080e0b062001c10010320501e04040e08180040c3c0b400070601 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 881467464 1250 881466214 881466227
    0x3030c090a0302220c0507200301060308031f0501050408250b040311101403040b2d07110321060d06050711330621030a090e011508040f12 61
    0x413951510500885140450032a4a40103c19001e8185000d862240b8801800040c205070101405170020a020b80c0b60303182c140103a4816117002403001b0f4581031502c030401400e103154002c0c02003440c1c074600e03007850011107998803180031241c030070030048146c3c4446080800c8483d01d401001c02440700ea0311282c1c0c034103001c2c60341540c1041650040c00c29a07001d160301841141c40160f41540000050305540303a41e16940c08810004204403614026421980d40004414503d40758849103518400d8283c0b0f46010b005207003400005c0750389240d5100340068102e101c40e100003203803c0014003070050125600c040001d140c03a030340c9003000390400d032070305052000c0300fa0300443d15288084064101d808408a100020354024040041030310310407410008903d00c00031154505800c40c000422003402c0c2e01070900c100250302d84c4640c0c0482581e100148083c0309a802c190120700400035081c8500f82d0b98500b070600d01c84030454449136010802d0a00000741000900101240722940020240c6246010700c3e8024024 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 881468714 1250 881467464 881467519
    0x8010209040f02040e0c07050703061103071d0307180b04020406020c0102120708070f030309060f061a03011406070c1d180a050d050f1209070f150203030c090a0302 72
    0x240d07040c85584550660b15000301c80484240000342c0b80d20f0f03036500d00c04408a40003140d0444142c0582140003000c1681c5006800c4656507a10341940e03a07041c409805480d00712000e25285080c840c130703405054180d50200304001201c00b01040400c4203e41d00c000c1400410507509010b90051000c100031491039400107406568030000e03002c4501121150058440394081c1e1a401000640100f04010010380305034283d500303d0f8400d040226501c8620f50300d410503039580c01003aa5503540e60b54010001c030403000804010b1036034100442e07450b55040540707007040d0340c080510890140c10005000e03c1002030614946004042d030710407440c07003000c4094403808603400a03a480c5040042e018000c2c00303ca500412402c06940c2e0040c02002c0020348424140c0e9242c100d10340040424500317100710400340414000d0184a07903000c030040c0140e20b00745120312620101c990803800e01520309002d8008102e0b0004112908005100305064440b1842000107601c18041c1d00029001030701003000b01d541c0880c80d14400075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 881469964 1250 881468714 881468719
    0xa0b120312060d0f030c060f090b060312070f120507140309040501170d030c0905040903210b010f050f0714060402031c09050603090f01110703020c010e0907031509050108010209 78
    0xc0c0c0e1100001c004210303880f040050641c020342c009a0700024040c0300c0031002d03980b243d034022030700701c08840341003088503555402540d0304505981080910304d000d207c0c10f81018032804840341080a6900e8802c0b800c260fa0600428031240c444c08542d0483c0601d0588159540c010318003003500c0307401c60402e6113941052031210700507820301c4004989444280b85e8100069020b0000340040440442c0c02c03000341100541ea6030130f100d070740321012800c0e444038040c128155007e929140300260b031901e16210001c2c54000003e83c03e07490324610f01001c0ea8442e20a055140c4c042ca00345841d00580e05000d45c0610840030010004c0d401c4401c0e0001105004c20340b00d115900890a4410b890900ba400ba110741031811030301c000003129414140010710b80b070406560040000012944441c0d42000301d20b0840704121000880e4990202d0241c0c10140e0401100352182020f10f000e16070605076a01047c030205014002805064580c40441440700b03400154400034001444244099652407040318001e511100d0700d1030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 881471214 1250 881469964 881469997
    0xd1a070207032406030507060f02060f10051002030910090303200c100507060509072d06030506030109051501060f0e060301050f0d1b0f0e04050a08030a0b1203 70
    0x520403400480e000c01200e81000710000d41e4181588074202010f40d510b86801c91035540c000100126900b0402d00d0701820040d01c945c6200c408030362001e8644407005161620102444003081020250010075900b165003d840d007440300a44030728282e00798026010b951343c220100441100c0e50036070004450007128001e03203850814001c0707610000b42ca50b8001c42040a01d5004280680f5507007003041d484000c04020345030843c00c1070aa961017105032903090300da9880940c010340f824402c12909125000201071200d00d4031186085044030004429041d11500c0c09050b0f5480c001096602e003908082066a40842600c5a48070034400003d1082000e00035a00010f01070242c5031071041c010680d02d584a24010b0000c0d003503a290804124103854640070a07a0090100d404001c006600d00d50403500b000c105407503940e100390034007105e40c0d200b4825a00083ca801e03200c070148000310383c1c0030a000d100c090700300c0c140300e03600d580f004600380c098a103810b983d07508020300d991a01300900e0f003c00900000c60f00c0004c480d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 881472464 1250 881471214 881471221
    0x402030c0f0f03040210020c0a0311031002072111100504080c060415230402090702070308030a090519080d051015050903150601170a06051005090103141b07060b0d1a 73
    0x481c2e40303070550751148c3c0d0001d82c220301c1800422031886040c51503e8004044502d40300082070541c0076a0030141d81121200d0700000c0800f03070f901a0750102c01c2c282c0c101d85000601c54403540c0400c0c1d40c3d01d60150702c0b000c0316603841b8041002c1c4078052007240e030400800c4044415034101450300003100344c0100e24a444091800304200302d05200c2401042c9a407000e40c076502c005868507020082c115401401c101c00f58428558008001618140910310401a01034001440038841c01c20030b0422060401442c01e030640c00e2006000034078041d082c0d900104c0c0c4810002502e0740c1d0290416044411508070001010307896901000c1554020020412014281c3c182c0d0525444444400c019031015a1044d001c28004075540415403009640154410441c80e0045111565540841e02441440b0451030000d1030000b81100300c0d50b0580221a080501c0020190f0303946001540d200d40300c81a400e0078032846c0c400040e40000e00c18942c00407075a282006002c450700da110b40c6020982035003400380b904034100005000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 881473714 1250 881472464 881472467
    0x30c28140a060e0f04090507210b0a090201020c0a090b1206040c030f0c09140a150b0f071406010b0720010503151804080319020f0403020402030c0f0f03040210 70
    0x20481034900192010701414244503055440c0d284a80c0803d4018951101d1491141d459014103820180a003000d0b2280906100101c6e40420014600e10310680105580d04005803030510304a0340300e447d40744002900304c102e100407414040b4a42000c2c0e4000f400c02008500c49400d45c0c05252008001c68500d8600c0e0a1035041948860302160080c0009600c5801040401c09014200d071809115482c0b102105445054030012615105200003125080a01700010b041e00c0d4403c120101d1130407402c614056107401c200e2a403034426960170001c0140d000c150b038410060604e10210780e002c8428142c645c5d0b5a1180301a039403507008040b090720700742c50340c14480d11400c4c0c20203d01030b07481c101030b910140f455170341d111f02030189104001c110741c212030001c814000a481224055004030301c280c14883d07032820194074019002ca452114007100340d01c100140d804254402c0100d6044950507100541c6a50703c0440f401d54500031070981500b0380f400040c0100350300d0b05440c02140b00f644201d82040b941c280e030020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 881474820 1106 881473714 881473739
    0x27170f03030a0b19030b27070311010201151217031311150307020114390412050f0607031e0902220e121215030c28 51
    0x47c801000311103800c444400b145d0320f525800010520b00000c1c0c40d261148001004038810701c1c007110b5103900039004088285003a030b1049010350303510240c41c81c500000040c00c603109501c00120780015000002568003a819007002510000f0107590b45d8003e41c025001c40c240c1c410303042c8000d420030320311040007903105c0c0006a002003000214502c0f0b031045081d01610210b042604011044e0054061100c1d19000859071411074403444812100140140b0507178001c2a1420b0041790f4000510000003041212507900c08211185683d6400c400c82c1160961032403505040040c80c5217820311001d540100c0541e82c00106994003d039000c01d014500800e00162108055483e0320076409507603000c0c000c003801c190000703005511303000e908100d41e49001001401e4401c41e0f0a1480701d40c010340c50401441840020140c1681010160b076001a80410392101c410b0b141442599408203803c20b1501 = true := by decide +kernel

theorem cover : BRFrame.Cov 881294964 881474820 := by
  have h0 := BRFrame.cov_init 881294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 881294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 881294964 ≤ n) (h2 : n < 881474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
