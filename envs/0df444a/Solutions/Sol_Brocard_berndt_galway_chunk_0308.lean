-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0308
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:06:48.944748+00:00
-- url     : https://prove2.me/submissions/2bba7030-ed65-4bb0-b0c2-a483f59b7df5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 55215830 ≤ n < 55395687 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 55217080 1250 55215830 55215851
    0x60b1204050f01090506010504180c12030309120e120102032e08120310090b090c0c0f0303090a0308090307050a02060705070e0118050601030c0f0c02010c080a21061404 74
    0x74885002c00c60350140003400000d4560a10580d18042800b61520807031918403000040b045884951900303d5000c4041c2454601c4d14228065444101d0429024540c07111802c10000345440c03469072104405403030340618004180148030200e0190f42040d01c0c02d80c810000e0041980b01002c1c02907800180c550007203080306c3c40141c54001d004841d484500e051084d103542c040e06100102c061071141038981d501186050341d5002d503906564a072041700e84c010300481c011602007101e540080ca1070600c1d40781182c0208401640700c1e46154002c8803440919007007ca0b011040607400907405e41c010311404001c5003031080580b24180c407030405d01c800a02c036002c00940d203000c000041c007040005100000310340b601980e42e0011824020192034840441910b0500021041d6000e03200b4004a0031040d40e898008902c040340076281c9000109059050002c081098000950107100412a0552554400d200e00a41d6111060014020720140c0d2045003440c0040c0500d46824459005000b0203d80200e0900c2c000e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 55218330 1250 55217080 55217083
    0x150c0706020f030702060714030c091c0212010510051e04020a110604030f08070206070903080f0d020d1a01020d05030415090609051b0111100203041a10030b0703060b120405 76
    0x1c0d95202c200519001c0100070406801261207440740c4030549800144540d00700d00102d051000700d54103007003410207004041c01410940e560f4030300108a01c119100845c10783e00003ea1a2441d5601502c4580d1204100108485081c3c680001001e041c2c03008640400b48810301c95503804a040014066540071804072821803040b6200200060500140c0d420350400781001404130192001d0000410359860100d06024400103e840c820542643c540345450b05641e81c0208591121514403910f903000c1c80401c40307803e038902c010885442030001c0081c03c0fa0f070f0382600c240408929402541035401c05000310340b0440d0000200c80d480303a481012070171507180000e0b550004000850001e0083d9182448400130400005442408909021943c0100301d150100445541182c145d0305245900000300040c4030003001d40185801c02d100d0604815030800c0c00c90100020001105c0500e601c0340f00c00c400b0030034400010740a98001c9060f203410300030a41040d0b644201d900c03407407180c0e50150301000006001d0200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 55219580 1250 55218330 55218337
    0x506090102120d1401060507030f0e0616060204150305090f06010b0706091a01081b04060b04030308090114090d030605010309020603070f1e030b040b0a08070302090411060a030e060603150c070602 86
    0x4d801300d20140d15610b03454010941e41000100303e002c00c001c4443d440e607550050b031000c110410000c0050b4509880c034044040c1e00c1030803030000c5540c4c1c1d409100220352030501c980510f031030101c0707a80c00103000c1c940041301e1858299240c41c5185145c2060f0018050380c0c0945c030840b6207442d00404086480081803900803d0461101c50740d0180b04058000464074140225070b0641c1a2181540f00700e0b05100b910801c400c5581030310840d180004200710820020380038040c01c0354402c5000c0000100764104e50361403080500221100c45903500884002201c46401d4880e89002c0c2800f0f1038200242890365000c0764541c800540989c061001d14856090901c0c404c842c81134408801d0540f040c14004449000383c0500307034610b203061160382412440c076290300b45540401d0483d40282c009052040c41c54081c48850400508140ca150f60030704040c02d05900d40c0d00041600148a035000103000c041d0481c45810000e016100611942001031130034004001e0400f40c0350800840090b0765a40c0000d8540ba10007440b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 55220830 1250 55219580 55219601
    0x2010c02060c0f1509010b09091c11030a0e090a020304020924030f030a021e06041209080a05030d110310051c0615050111151b0d09060609060506090102120d 69
    0xc184501c541c4d14501203d0054040c491080c000d2180c016110101300006804461b040300da54043c6101c0e044c08000860114107200140c2400000340c521001c24500315441880503e0104141e41ca0354009400d00c01c0d940c640c0b000d0308680840c21400c107a0300141d004000030f4000751141c03010b05412621295410b00040b83e106004003150044100f17203030303050f0305d94200c400000c0242c000c0910014501c4441c0c7e155100281c2010b01400c4242e0703582c0d4a40a00c0460aa0b0b180104414000082981c010030080c0c005c019005400a5071500c1c200c1803c4426945407a4044496000500030320030400070880c03815007943c0c03040314006202204144001c0d990381449002606050030508504980d084e644c0804040c3d500c02c1c2d868092042e0b0b0b07a460344c0d54401000f141c004a900e1040d00040042c11620380f202107a858494585140801d07401943c0199502c00b07000703844151b40d0b003604207c3c04034188692001000c094842c00d007000e1940340047d444041d040c0032004c4001002404d4018a41c59501c07400000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 55222080 1250 55220830 55220833
    0x706050a0921110609030c12010908070b0a1a0d06050604020d0f0207060c02030a080406050606040302040e0d020c010207080705190308030c04030308060103090c03080a0909020f070c0f0302010c02060c0f 89
    0x8502c07107210200421a080310075503a48161002c001c0b40780c00e0550407166180c60107001400c0f00000c4c074007032040b4459034522294255680f04502000610340344000c0000601a91900ba07050a141c12501e00701d5040704841e000c4001e00c3d001c0940075440d52811030440e0398009000048555400001c240644030b140e080d0030b030041c6400c1d458072190038240c0c05010b0340d0713001302400c21401c24600d5069981c0e203c1d0b50802804200340400040010780c00360081a440200989004d082c42c1c2e896000c039013980c0e841d500c519500c2d003060401044981c1c0c1000102654142403004080c03440c40c00760556110011801940c1c001d0507800100c00e0210030015440c0010b5a120031202e590b4a02103001071450741150000b14005116803000c40d800758807900030807100c1a00020403440481c5107940c1c0181c02d034880ba444e0400c1c89000a00007a6030f04451015001c5003d40d0000c135680c0701c030189440007500b50300d40c10001c40d41c0420700003071001d40d912a40c0304000650603142c4607580c40d40c03030013190310f4406803c1c902080d9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 55223330 1250 55222080 55222109
    0xa0b030601080123010f0b0c070305120403050105090a030914061c0501031703060a050418050a060b0a06020319050702120d030b12010902090c0906070b1602070b030106020706050a09 80
    0xc5001540b00d112901c4421000303089400c0f4084c15201c1d4250300f88038511704802080c50600c0030080b22801031103041030400403240225520340d82c440c1421840c000c4120440004601082404070030700a1940c4402c100c000f0f8040030419035400340c40c4c0c03000d9001d035041001c4243d108002c80c0e141d200413100c0c1c0da020f0010480c005c2403020700d4140908000d0008844550111481c0e000c1c15040006480c0100d8008054208050406090000400240f00e01e1742e00e407910841c098011890a00081006c140a0800440d1001c0002c0901208484951081007154400c015580340b4044503400013181c400d4514020b50b80e05070500000d0180e54030b0703011004083c000c00d0031116209800d0b520041d9039240039036000100c0c40381c0d119114201c0f5140900a5000000b04001030040a00807000f000c0b110001090f00c0d00701041c9484e00c108815040703505141488800120340c1e081601003100034001c0192003042d80c619810b0400003900d03450300744079181c107008010800f50344590050040c01c01412034203100703901 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 55224580 1250 55223330 55223339
    0x50a0207031a1509090304030b1905040c050a05060a0504030210050405030303010603140109020f09010804060608010207080904110309150705040b0f09010f0e310608030703090f060e0402030a0b030601 88
    0xd01d1071050b211008183c180802c2042d541c207201c40540c0c0310385401c101841c1010b00c3e54440500d644c0c401860303485d860300c0b0041d44240e2440903203e0140514007070421803440600300b034203104d031590007504001d00c0b95009201100e41607500c58115070039a81d041e103043c0d01c20b0388505016110382c082e9800655060102100100c0c4069143e80407140d000860803801c0e146903602c809103009c070b1040750850210100c04001400d04c0b540182201c580007481108006041d503592400107007260400c00080320401000609070445142c07a000314250081a41c00c028950306110311046d94605000c4010406006080c0008626602610036140100076050300d69a9504007004401c0711036111030403403408148021125500540304201d0007848280141118200c210402d8045c0504080310b0520360801c0103103d03c01a02c0d00030740c0107480042c84004025500c0c2c501d6845d010b041400d0343e800500244540740d0080000303645c428040c00b2010310a4400680e00d48031042214007074005001c0d0b154241c41080000507 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 55225830 1250 55224580 55224623
    0x40212070f02120703050403120e0a06020708060f01082806020310030203100c050a0c02030c030a030905090a02070c03030807050d110a030f060f0b0c0307060915060b09010f050a020703 81
    0x8001e0250303030035500034150940009803035019100004d00050b40c20f000a2000514680890039040e12504044034200c517110001503811540c0e41003880140c000070000c11902d40d04104281e04a00c180052150325814801d10a0340c406115039000041902144001c40c1544100d01c7e5141c0e46400dd00300b0355480c42d00c00b04810307481c54540310032030003407065400440c400c42003841180c016001e0703a581c1900d40f05040508413005041300c2402d03079143c0121810344401c2c0ea002c00484032003920039243c01400d58a494100841c50000a05400c002c0340104408000254000c50210a480d45810010055102c900044655004040509040c5450b0003482c4019000c0e4202030400c1c120550340174824441e80c44011400e941316031140d000e401001c00d00a00482005102a290708141e41041701d04000040d100c05090b58101c040c1a15001c0c0c00340000c82d410085030050401805801d04040c0c03030400e2200000f0000e1180f200d00808002022540d104942c1c0309000c5200115003116040402050007000071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 55227080 1250 55225830 55225847
    0x80a081009061d0108030703080406110f120609130503190302040308130801050a180f141506030106120515060604050a0b130801060e1602070f090b0406050114040302060904021207 79
    0x32410800c0c02000054809000801c955003141e260b5103120494441e039603000c0242403040200140e10f481400580040130170180a440400ca07040905201401c0c8102405403185011e001c0351036041030000020b0200e1400811950416542c1c60040a03111000c00220028062504014405400040d640b0399241040b540c68040c0d07803c00000b000540c0b02c2c0001441105d0a1248a091740d408603101f02010481600d2010409401031961003141120f0801c02070034041e41c103c0c040d001400c91028004c183c00c1c01d100310030142c4800403104000460030b40300c0903030303c3e00c0340f0013030041354586540000c0942e1101c0c0c00340c50003040081d04c55018583c550034025040d0f000003500d40c280142800000500320740500070203046a00810190b0010b4661603085030354070480101f15001c1d0f02c030318070000401c54414080d01c0700402a0000000d10017425204020950711141d00c568100401c09180e82c901a08240441d000c80b9411a816076075060100b000c10040d006403540450516080c00801007403540107400d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 55228330 1250 55227080 55227119
    0xf07080309010501210201050c030c010204030506070807031401150e060a0504031703060f01080c120f01060f140a050703030b040501090914030708070b07030b0306090102041e03080a08100906 84
    0x20701c0984c1e200c01c20451109905d0481000401c0110980070240d4002c900505889141d901a40d1501c00c8504480c1e007642c0c416401200c10b64003000c10000c99550201c956500a58240b50900034030001d00502d101d200e01c180252000c4010807041c440c1094001d1040c04845071000d025251141040c10002e00590494801030301c1c510102422042141c1030007040b00c1c45441c0003040c81c0c082c10584001110070764002045040607542c1041000440541c001980c2e04c1007410b40606100c0398100781d170080a0540d200038680611203c9008040d0152a038810364440440384c2ca4135680b52074031401c048010749055800150094a40700001c03070340000e00e070451464180140d80e23400102505010b01c5660344250700c3d020b8080c08090040030b0015000305032043d080741c45072034080b6201c868400060709051043c0c4825080740c0d80010108520011002c0511040843e60268030005107143c031104260b01c2043c0c080e03020490317244000760001520320b5807135020340070680c404c2002c0c41e00c0306c00340e001c0e006130b0240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 55229580 1250 55228330 55228333
    0x519050c071211071e03080901110307080301090c0203190806030106090e070603060e01060c03030207020607050d080601030b0301090c1707170c010801093803012f07030203071103030f07080309 85
    0x1107601d060191005c072144540f00e418414051071500d070030395550424500c2c94100003040410141c1c80300308101500c2c2c8540201c9885603294036142c0d0756001c4400852010041d50002d205c0700c810a01070060703580c0309404038106981d0395a80c200003e8010002d6400c00d03d8450f140c001064040400000e125040c0e5129840030000d00d5107030400305800c07040901c1001d00144c0591103500000344a83c015140c9248044c080310305146542e41c80740c3c20801c18038020000180440108459580e140c029841da0701c1e801c0e00200080825921442c40c6031009008541095544500c0d0080300301c0d042000324010080100c07403002c55a4008038890715540c40d944058001404000041111416449180c55004120040c060030381e0f0140f043c06811820341c0c103455400c088801030054903407801e000d04902c59024008404807005504c13485200107026411424941405019a000103900002103800c1c0e2030300440075043c2d0b143d100c00001d2452268a5a4900c0540042200030070404017001440c0518895030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 55230830 1250 55229580 55229593
    0x110109031806033806030405060403080f0108030d05090703050105010b03040b010f05060a030b0a05040c05131203021f0b0d0303020c0c04050c0f0a14030112020102060a0519050c071211 81
    0x14220150b820010461032040000b0822200d220110540403040407040010044c0e030540303d2002584641045800391400c3d0071030010071040540c4410255030010301c01281303110550604240590f04d00030414001d18155840010403160401000340e00000c59204000b0b024541c0c54004644198005540c00c444548004001040c03100b003d080074020f03107502610307142c240340c1107940483c080c201d1000e0302500102d210030040386940300c2d4003030605800340d40c0e2691581ca03039161023030304100781d01988a07082081c10354103404000380d4041a00340310101d4a018104420a810300154020300390249100c1e8440308010300d000402d609138024000c3d0b15980002d1711041032504083c40240c035411031382420740b45810400388024017500300207001c0000301460a0403240800509107242c0b030744281c03c02c50070700714480c040f00115031381000440d03070080000754184840c2c10503040035031441d0420b510b43c414441c2c69030005040c001a1501f80c811a0303802c0541e008000c083e049000d0f00c07200e160b01100071640505d5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 55232080 1250 55230830 55230839
    0x3020703021506090c031314031306030b030706030e10050f060a081501090c0504051e03060c071e060b0301020d0e060114060301031518050309040b0d021c031101090318 74
    0x100b10388204400340c803500f890b03613030081c1061160344010420105545540102408070300b0364414149400c151000941e07690102069412845e4620ba008504050400c41c0020391510003241b00c0d0100d40ca103040c00324a20382d40742c01150508407120484410185071508001700c0007032004210340104019502c0c20046522818920703203540905a40300300e11420707100100502180e9038000740c00c0210030310b401c80c2402e407620700150404541c899010400c2c12444080022443c05218880e0000b04284020b45481c5556480281d0542e40c0703200d80e4692001b28041c0b4040c03210b01d0f0043d00726084c00900855890312900c072514010919644004602e00c591000402d451240c00c28015a038100205614216031940d40c4101d51f181d20804d102c812207440320f000c862445403040740402c440d07104402441c3c0b1442031101b0301044070241c0400c81e101e04d02c2c3c84201c50150310b500f14807004803e4800102d4400e00e440341020f940c200003031800141d01e036103414403205c241031744070142d90508100740d08001089541c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 55233330 1250 55232080 55232113
    0x150a0e01090f06080f09010605180a05010b0a08040f051203040311010606021207020d02040b1807020c0603060d290a0605040509030f121801020406080603100905030a0507080405100302070302 84
    0x5000d40c402140c10140400c69042c5c1c000012a440259000041600c50311500416812400031b08032110f02d10b540010700c0700d000c80e80e01900b0701601400c203802d42084044c9500070003040c3c0190000c2e01800042006905002043c0b21000c6180c0c904c01043c1d603241400d207801448806142e100803515483c0550105000e032005c614240c0361018860040d05118994003084110912640c003268020307640c201ca1441600c446250800c03455040305019020301e089c030000f07130400300c0c00300000317109103c20800c0143c3c40d82d548c9000071003103410001c022880d86605e00c4074002403600d00703040d50040d4100c0040081c0b0b401140c0003a000c1e181c0c00d071000c0c080c0e62903800c8450395901802255010441c0c00707218030074a0620f00c1e103040740d000012000044000c41c00a40290890b4401d07081800003404040800041381402c2100c0001d01041c0303a01008803c00c0e60300e07015103a010301030b0711100300301c070000740d0700c003480403e00c1603501402e00100111000c032010000a802544141070031030160244a00c5400149030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 55234580 1250 55233330 55233359
    0x3030f0411030a2d0c080c120a031b080d05041209060903080f030c120408040914060114090a030c08070e0f09030a0f0314040f030905060403080414150a0e0109 70
    0x18060058034140f981507200c0852509003c449840844e0304001e0703000890000c8040f0002008008098000d54244000303104030356014201315000340c1c1c440410400001da02902051900c0010540c1d0b460000b03440c501040d91f07114801d014810b031410300e41031205001c080361140070341503c5511105141079507800b058442c400c8074400a4101807041c4541d400b003144920055078007404400b451031512025407012a41341405550645001034003180621034492031740f08000d94401008005200c41c0f401c00002485882e000405400c3e440010074054400d4541c1d002d050007540d44400005c2ca45034803000e25a44e80c54107441034255820140300418040f4080c241c08902801d503900c059460300040f50005e4130790700b58030740c1603004256441c1e2000b0300c40e000e402c01480c0a40c0c03007a08030074603890300d50400a001e540b030b42e040355104c0c01041104000058800085504a4903201a54810310650b480002c2e28941e40c0701084401d108005048505154458000c28107444245c9035100b200f61183d0400d00f1020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 55235830 1250 55234580 55234583
    0x3080103060504020111250f06050306150c0604060b190b1605070f060203070b060a0f0e07020a0c030602030f1503100513080310180204030c091a03030a02010605130c020c09070201090503030f0411030a 88
    0x42b000c1011034503a090624004921915030300156180c206d605150605c3d040003250140c40b4a0b9540ca110103031480c040003401c4030000c0c0030000d11405400d0503003100e5107218480702141c11540e1402000100072007800200000d0009500c4331078860f03a00d141c06074423644510011601043c0101c0007a40034504207211100b692003d24001e40c0c09030a100400100700c001600d654194459008940c7c00206220000000f461040358096104d05100c00100e03510300002e8256400501034900d004515140083c002d41c00030785900001c0b8ac0c1d62100c2d07800072454541c46d040588045000000c110b69048011014021100811078480e21a8000c2400341c080307014500008200007201c4400f048040301e42e4100c1e6a600c60200f00c0c18405c011103a0001c1c2c55a8864000c1001503511360004000e03928001c0c414585e1585401700c00c2c00328400d902002900c4d0007101108038840c500050108003003510075440080219405070899689003843e1829840d008000c5404440740f0490302c40c01300d12810f0206001d15080d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 55237080 1250 55235830 55235837
    0x20d060e041a0405010e06070c1101020105061e0a1706060a120203060f19060e070e0105030103020607030507080d090f02120a03080c09010e0301060b03061c03080103060504020111250f06 82
    0x2c240d4551005001c00040e0060741c59640792222100318050031300c83c2c0380c021800ca486189400c4c0300c0303203401541d48031514038507030659142508000301902e450301c650540c1344c5000c0000d400420030313070000381e400c80d05900450700d854404020101c4003040001c586000325401c803290901142e1301c009031009222403020003034142e0015000300740a103c0701c50441d5000b4030b00f445600e40e0300c5401000340c011904154442e55140c40081c05028040303402441643c415082817a0030b40c42e560540c0c022541a20590100804011000071018280070340e490955040b0100b12805001c100c002c0d061407a602841035a0903845442c010381b020607031400000c0c0d500c5230141e2540702c1501547d03422001406940004000b103044c440e4a841ca8100350313a003031040c40060f1210003507182c1c503030501c0300501c401c4680c0d4008040c0582c0e104495880469086507a080c11203900400108503503845100495a50708190001c0c407a91041d21441c0038980f0407103079040300306005003041d80c18081d50341c42040c0380c0c10594454000030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 55238330 1250 55237080 55237103
    0xa0503090112060e07031401060201021e0a0e120c030706030c0e010809100606020714040603021c03030b0d120314060d080705030408030f041404110d05060a0305010f020d060e04 78
    0x407940500d103080c9451200d00000200c40b607941040030340142d0300316040d0780029903070559040124110451640986a03d00c002c505103808009040381c610042c0b4a140d02000340810022031491003800082481e140182c207031080d00100018003030703440c051031068a109010f014008511540b0038400c40b071680350644c4d50460840390240c01981c0e0102c0c0680030030f0003809840c0b01103290442901400000301a249d009250721840c0100d403102d0791107904c60003032145003010300070405681d4902d0034020b0140444c0500c1e82c0b00400c0e28081d00141089002d0350f401085489082c02440310300071001031400d4560700d080c8141c80e019400c040d01710720704640f0ba591062106d180c400124518401404603148504200d91405072564026455600141c1c45007800e0080000c041c4802103401882d0208001300b95014001c01040f0445d15131a40191520090b203255101c0c0000c3d125659180980700550300b100080007540c016054003800380d40142c0d820302845052400014000ca0700e040160b102d241c0125191a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 55239580 1250 55238330 55238347
    0xa08010b0f2710020a03080f04080406140d06030b04030215041509021302070c05031c0221070f0b07110c0906010f170903030615090f131112060a080a0503 68
    0x80507100c4242e092440c90301d03000031601522140c049140d2221641c0050900c2041458001c0c556240148014440b1003154140000103030400140c405071000c0b41020b040141207224484054010141500d040078107280700001442012540d580c0580c0c00303035081d05c003000c56425013500c0110701650000e10000603c00e4034420404507030310000c00d01380f0003040a100c840f00e089091003a0380000c50b0685545220b00350070819440c0400002d8501c00d0304505101c407100103820082e40b41c1c000c00041c03600e80e0341490503184000098a0440c1c0c08280d12400c5030341c031178065003003031002c17043c0842c2d2140c08100c0303805402a00c0310000410124808004001d8440e030365a0800440702c07000e00f0000041400702898090307613030858840b039513441810395000441c1c03285803d4081007014084d01440f9800301e02c1c02c0041c80056141c012020203e150300ba0b800381d4140c00080d4900e4020143c2940000c005907004c96090070100754000c200740684000c032641212191510040394640e1482500109075910070400c0d000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 55240830 1250 55239580 55239607
    0x10905090603070306020f0a08060319020415150906030509030903070b300405060609160c03050c0304090f0f020a09030b0c130e0405070e011503020706200a08010b0f 73
    0x19030101c4050103590740c0994969444050740c0000000c801084000b14040f14021b0344180c040d0b0f8411011001010550b042c490185614080d01c84041e000b0303500c605440b9603908003414804000c0281300380f030500d00b074103070000184600704a00400c1e0000c2c1c10718001c0b41d1100000410f03600c0310b020003409412014a03141514140b94040701d05010b181c1c0220085400304198070b0901c580c8004894507568940c41c0c00c0c5411424840000c210b07a12844400c0c0034811a001d071084c0305213592590341002001c045050034140c0304c5004800081c00103110010300031881400380d0700312800c411000c100600103050074400c14810381c001c1c1c0790040005421707440708102050300c01800c5608907010000286ca000001304c0310031408a50381d000030001c071a107501070004005080002100410400d49580e42035410520561107100c0068151402c054001c5854030500455500210404900c4207540d22001c018006800941e08819072034400724188000014240360540f00711070610b41c289680e9072401e03081807507a2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 55242080 1250 55240830 55240849
    0x3010b12030a200102070305031609030c0e1e012c071704140304030804170a1203020c0309030703120f080f07050a0c05060406020d0606050403020303090609190b04090b01030902010905 81
    0x310300c1822440d00d00031009403e05c020040d15000303a40d06946c2e460b01820703520200d070a00329000c0030006e0052003000424450384201c01a964568000120b40e2601e0000c00c480000b000c00c040000c0c100c2c10000940301c2c0c8441d445040401c051900104404c03c8101c10701a07401c1c0c1211034101142c80c03088210582240601c041e540540314511114228504101c018038540080e081200c1d9040d001805000d02001451030044020480b002400080304a0b0340344003995103000304075001e00d50017217110949250213100344d560f5081e0103422101515503a0170700e080e07101044005100400d00d4416004195881803c1c00d45c0b0502022104c05400d4403582c200301c91980c8605030301010480c02c1c01c02600010000d1020303501039405102c2c00350301c0d800030801090440b01a5070000b8144142004108016100801030741d41c0034604413010f5031a114100013190303051032400d0728032010402c6058041410050f00020704203031040300c3d20421440c0030b0300c8015411206010406808159200700801caa8034109410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 55243330 1250 55242080 55242107
    0xa0b0106030b010c0611040f0801150306111b0a02010806010801030309030b061807020109030e01030b03070902030a020702060c01090501050a110306040c092c10060507060507090506031503010b12030a 88
    0x4001381c11510341c402251100000102030845c001000c001c2c0c800e5030019900a400060000c2101c200901c4100310101c0031840f0080c211600c4000c0740b03209043c180700f6500d440a2042c00c400300340c5828450581c0f200541a000c03030100c1c4040c0d01041c429445612000d050381c2e40342d11100e0390704d42180c0316101151002020784e070b84600c0f100710090701c952000b064140500016000811219514500504502c0d46200980e04140c60500b009040c0d0f0fa0002d2014102e60f11414011303a02d8032060000f10207407081e240702941010340010104501d502c1503101c4400c00d030180e4020045501c901c20031505039010342d200c0307144040d014404910070746403590280c0d415070150308205c4000c50759002c020706007620070b0704240c07100301500140f440c03140148156283d0102040840b9a640c3d4100301c0050140d003e000c02c060150b41d51400061070382070040708524043c0c0401449280c50b4a00030b80112078803000c85071514041d500b00301e14026107080100840b10b01c1c031020700c0550f04055030900d045440c01d600740003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 55244580 1250 55243330 55243337
    0xe090403110c060a110601090c050a080606120915100506030402060d0b100504030501060b0a021f021204060608010e0114060103090f0804030b0f1006051c0f0e010209030f0a0b0106030b01 82
    0x2500382c030350381c03010001c000460351a1a000c9000c183e01110504007103059221070320090a0119130321450754090102c400302642410a002c1c20b403500c50101d141d900451100600d003814a44c1030010030140012240d51540511400b1500c030341c3c90b42d000e01d1a8012908c00d240d04900103201003401490540040d00340340203800030009904584400003082049015114800718100150500034044280905000303050240c1c01689402d0b141040256038000d807a0b80c01d500045005012001218503804441c43e250311118005c2c403a08280c24400003c040c13034441c0300c5180d841c0440e13104441d40103014410030280c018000114980e922801500a48280242140d0310070525042038001030981c0054400380d40140f071b052038240790003140c542141d1405000c94030101d004c10300c2044a07a902008913000881105410803c0085002c000000b40080440303540080e030900340c00e491a80c1055001c2c0c054604128200c13540290005003e90b16000c00c4140034007080c0d5500010b000c41c138026088101100350615 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 55245830 1250 55244580 55244593
    0x9010c02031005240906150408030301090221060f0112060b070602070203012301031212020a03090c0b0702090a02071412030103020306181e010e100605100e09040311 73
    0x80c0080d05294080c055000b00c00d0340d0380b052100c0910903c2d00031026041c000200101404480c0000d512903200034803451207000444840c4002d05ca00100341e400400004084076100c0d41c44654a201035040740a10f011800e07100314008180900c485171240c010340d005019800c1692041c4011201b4510100754003259545480002480480b500e00505c0c9441c0100300040c0c0340d074041d204050070340e4090103080d080480340f1900207804240801d80c580c1103940c00741000329030544500c400d4036000011044036201078400b248485240d42c00d6002080c005214034000c84c1c3c110b84403200000c940c002d00360041d400c1041040050f04c50107855004080490045a1210244680315000d51600042851041d00b41c05c01000400c00c6080410075950040c58840c000c030845440a82640d40d584010845d4004401d5007400c0b4900e451000c0d4019032030b528051040d030300c00410514241001d001c8921620f402001c0c04030341404054400e043c40f2900c050003c00401254440752803c84a001e10141030364071601400c0d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 55247080 1250 55245830 55245833
    0xa050d0c0905010f05031005040213050103080a11010203150d0807020604031407060c0b0c0306010c1209031b060c170d0912020d170721020d02090a0906080a0809010c 73
    0x9451002400c0c45822000d0045007005218001d695041c1d0144584e22812101404241e50111709281a000c00050000e2690340b40c0c0001054442e90f1401d200e4807074036150002c818081e8010040400c000c10f91114080300c1802a091400c070722044030f402052a64500c011191840c00340704132280e490140c8203041c100b1a1940016150b540140c0c0215060300d801540800100d0301840310328000c01c0f035414411946811611203a4182d000105059003081d4000001440c680c02003c1225100b0780000d039200c4102140b49000d8480c1d0b017107000a96000848a590f881d45042100e43c01040e614260b59070380e01d000090355010b0242c80d5640001d0540c000900c00e10f5155041e42c0300381c0c4011406024035012280301018081c1c1043d503030fa658001000300d101e111442039411102100d41110145c50002403103800c0010940c1402124450003041c2800059849090a015005030100c068221740041000da40c0384009011203072144903540c426041281100042241403014011000c818105511202c509 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 55248330 1250 55247080 55247089
    0x705100f1202040b0a1706030c0d1b23030109150504080c0a06020403030f0203030f010b0904020c10090302010b01050c120d0605030a0501090308011d0c030a0e03030109060e0c07150b0a05 82
    0x1d13001040c04d0200800da482000d50b0081d02c1c0c060b00c00e1300042e040010306000020903150f060184426020340d178220402c40c10801203c52420001850506014041d03071584800c03e041d000704004072101d4007810306a02c01500d0103204e00310450394803c01c854000c0c1e400e003c1001c041d0038014015a00250280201d400e8001c09000b034407540f0f48034a400585d035074254540602070920703041e005021540280704100d0050004921941940d00303266070291a0394a220006006e882050200003181c025400000c00e0b0140c1c0d50080034402d40301c0c3d0003d01c04040082c0044559015100c2a96015480303030b4032005840c0d90000c018516916481c81c041a1280c075080424034000c0c020000f00d0702130b0f550300120000e00d58800c02c41409000c500441c0842280c1040002e44001c0c2e0180090078502e80000124400b49402c0c0d1012816010100540340c4a40e0340d2034400c00103202c68891500e52500110008034100d40c1ca034111031005501000502e405603040082c0e600400c140d00005811a541e624041106e503503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 55249580 1250 55248330 55248337
    0x8060f06010203041509080d090b07060e012c0705090603150603010b0918100204050102070509091005090d08060303030f0406051003081803100207021008070c060615110705100f1202 80
    0x61b07281c500c3c555280c8207665244c40da0401c6a40108000d9100900c00401e40e0411034405603085107003c075000078040300c05401042400564070380326a01e61101458070414002c0040111034100680e5945651a01071000428089840036419041248416804109400c0007608040081c0001540036001800b04001c0e61050350840710051900940b8100468100b1229120780c0c2c011000b035040500c1c00c0001707503139034002c2e000d114425484a40000c4411800308041010781a0201c1c1c00d2200d810001c40450712680c540c1038080c005807003a00050180d003800001c5074015899110005155580c0c3e40b83c000c020403003d800710207443c003210000004605500f01401030050102c0307100204548100415151481507a183c1d41c1c050300601824026076210304c3e803c00e20702c1035030500344010303030300c802045540c0c00201c0001080b19240c0b020124080c40d1103268507110000940382c410094011109166860380759218460784403d8400c6c82290740c5115960b0614084030398113180c010500e4080c181d106980 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 55250830 1250 55249580 55249619
    0xc04022b0b0a0b0909060a030309180b03070306020909090304030c03080c010902041d0c031f0519060b0703091d0106050c0312040b0f0705070804060503130b07120f0608060f0601020304 81
    0x41d80424084c15514200d1040d0750440000c8034070009081c51560701a00e04441031041d04401c00d50b225891911000b650008115140000e086e035480603102c0ca070aa0086d000400700d50b000311010710015070303421000021642642e80010403400c08600c1d646e42c403030040d803000d201e40c4099521108041d0058030b582c00b40718042c03868041a03880041e8011201d0f441c20038401100362007580030001d00003001d4840420300103a020300c1e04001c01c45644250724441492180c1501a40307aa10b80840060a40d1302c0d00701421050f4401e5880008180e40c424650062040c3c0b003c1600c0c0c041e54001c010800140240001d00034141100300303582c202a8501042415400e0844003075030000e103e5000c00c0400f81010701160342c402680d0900034184407a54440c40da0307500480c01307603000344400000410b601d6200e01c070714011825170051b0811024645420000d150111010310002014148015081c0710b200e203001c0d550540c8c0b40d04008181d103560301c40a10313001c0d610107010349056001c01c02012546040c800310140319070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 55252080 1250 55250830 55250849
    0x9060a09080a030e0f010e060702060d15080601060315061e2a0506130803070810030f080c1605101416050d1103030601080f040c15030c020c04022b0b0a 67
    0x56040c2c6041c4081d048600f80300c5c0e8100040400810ba495540005540100740c0642d4019156072501c0e164000818403115106054a800440041d150b940012010b040c5c4060359000e0020f6004841103411059a038002c7e54081614450184000b220020318440d0070100e92400820540c0d43d11811a625001280e00080d00d511258175241408001c0104a030409180203600c0c14040c03d58540c008240030203003284c01000030020100380707a104c01c001034030080c0d40c004003030180320740712860010341961084098003150301900804440c00c0301c46118030400c0f00e00c007230180d501c1109100011184080e46e202c441c00401410f00102110144030145420b4440c4540011702c0742c41280200035007444d441801c03001440d4820801c004450740c1c4851a01d4010f04054180300460b101d920300900145802c2d007004001140b80620000019850b40182d16500d0301d40c2c09440e0075134a4507007400168480c4100000c0160003030560b9001900100c0644c0300301400d00940054001d00d40d0000405c0c00c051a44140c490 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 55253330 1250 55252080 55252097
    0x10602070f08070b070803250302030f0609040c06030b01050c010606230309100914150610030204030b060603040510061d010e090601030605100305073809060a09080a03 74
    0x206040c0203a000107010b141008140b400d280c4541e6085174842c1e0540103220a0340880811040c11f0031201003d40c11402800e201e1000c101a90002c00a4000301c0c0d02d10075a0b01c41d6000f107589414804040c5009070b4102d40190701032410f10b01c068025100014080c1e04003c0300300410880d044d028414107015152a40d0313084000480d44c119180000643e03180168003000400520a01d50b000054108510140160200c0d0789a41e50a229254918001402c0014060404124040750010080c0c03882003108595840204100b0203084049000c2c42c00f00420002400c408100b26107002005150302a2281089a1020034040c5140d0213890f229401580c28280420217245806180c0c2c030341da4094901e0180f00c0ea01c610340a10a541d075207006103c0501059038400220f480c0e9043e450b80740c406560098211907146a841c0c45010f000c1d0050000d02401401c00000d03c4400c00200342104056080c0090040c24000c0c150704210440d4000607088044c811480d0001580310000c0c00310406541c0170b515041c15 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 55254580 1250 55253330 55253339
    0x51b120906010602120d090c031a0a05090a03020c0d0512180906060703023012040b06030105010f06140d1e0e01050907061d031507030e070302090105060d1401060207 73
    0xd001e006800203c15500054208040001c01c003095804404100d5004200804d8031304006001140315003002d40341104803844641c05c0c180c00c0b0002c602078240c10f0010070266441d00b44172500e692941100400581003564450007e10b4903003100c1d80e500d8000c1080e00c08400405036941016407208010324840005e0980126552030310004c8954400029180940382c1410b03982c0094950312280001038200d11001e5056401c1c0003004e0340c0240d00805070507610b0f60740031301c0005c0a1401504480444140c0d940c2e200081e1103042c103000e075504850071401c6010001c2d040800c290744950f8600540c0e10051024002c0d507000a00328000c4200c03585003824040110300c0390b42d01d00300540d1503910011603103a040c1400d2001c1e140000a01c10f0403542e080c50980340408515180035881e0389a0841594503208582010256000781c180700e5000300f003d40c50030400c800e001d42080c0e4440c01d0340e00c0f0180d40211480300410441c108070004200121076080002800f0070105c0c400001d0307890030707005040160300a490601c07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 55255830 1250 55254580 55254583
    0x90809040518012d020d06030203030c03040e0a0605031c0e18060f090c0415020a05010204080106060801080705010c150902041506030f0e0601060309080f0d020d0f140703051b1209 79
    0x3c41d030013010011a4405010642402000c0c0c0040c28140f00c016070004400e200651154006009140c3c01000c1d00c0d07440c000c21b0b90041d52134010313003c0c0d68803410081000c1581c0650b148540c004440b0041c1c042c1c12016070010015044040c0c1c81c4072030341130100b43d072040e40301c50340d540030045044036074020b54000d141080000e114100c1c030801e0300540180130503c18090060052401d43d421110f41c505240c8104004010490070400c4507400202030350b00101c0c4c0413411040c1900700c1c1054612070340d40c01145070b036240e002a40c0c4495910500780410488811113002c20400840e0000c0009028004030300140d190740402c04680700001101280d180301c20b41800020352500a1400c13a881c001030500001140e01d407203903142c81c0107110f20750034160f80300c40031010440c0703100c03c0e55201d04240c900a525020580c4444002c1e610a200c3c02424503d0811100860f001920a4184044032003441399038503a0f90050580040c080600a01200400c01c1e081c0000102280c0c002c01314080030780c00c5622030381046800309 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 55257080 1250 55255830 55255841
    0x1812051b01030b0a0302040b0307030606031a06060f07060b01030204080307060b100207030b130c03050303070504080c060a02030a030515060c0309180103080a0c060605150c060603010b0f0409080904051801 90
    0xc504050600340602400d0359000b0150061303980481e00040e102c4803242c00a46080e1113640020b019504181000091114001e030320381b6101a03030b44a591555582c07004100107845070300000c407001c040030302140000c00d2695000d9601c42d60107040052806441d40301282c0f41d0f07000340c0306c1142c0d5107898800d43e9103582050440b8400b01c4c5240d0000701000d0b0300b96510740d58070b034030014000050621030210035014441c1d00c401d403200440e0040d06890380c034281400000c040e81d1282c040d00100d481080104085401e100301264184502035001d07508058084601b10b0107032401078031140e0b654084051a4130a90f451000803c12211000020759a034009030041c0301320b12076154420144564250010000b181000040351901e100500d48040581150725008000f040b15412403031300510440141030804407400000c00307900c0150310071600117a89400426090301c241d0030207143c01aa0100c0040840d06081d002a00d074280300d0396816060040c4c0c2d5021904a600450303501d941c510038070441500d064070a10a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 55258330 1250 55257080 55257133
    0x5061c15091d010b22051302060a1e0f0e0f0d050706030b090a02090a050111030c0a03080601020f0607210b03101d0307080a050904150303020601150801080a0201181205 74
    0x1540e405469242d030350045001e0b92a00d00785c103075445000007107540c00000c1d00c0480042d4028007041d16501d600b00020503c0c20150741a00c072600030030b0f0202030401d000300d800215103d1103a9582420801403018010f030000403000f129000400707520001d001038403d1051030b01404559a00050541c0400300304004c0000c0070301040142c03807041090b03c42d6602c9900160741541d6082c00e08013540246864501c0c51846070303054601b031754000c500d40d04041650003006140181406d03402c540c1c3da1050030700b0742a01c80c0c80030b40740e03140415510094134020b4400c414210507181c10024002610b400c0020100381001c0c400121302e11012b64030110045d01c06034100b4250210b400002c001c40c00d004040e500d202e294030405c0164001d000022480e4262940c40d5000080324202c80d5024901d080c0e40c91a01070b540c1d00013802107000e404e020034092846540700b5081e19040307980c407034002c0c180d8858a80054582c00c10740390307a03211048180d00021404040c1d034624201102c1c880c030000e0040d00f403000a40d0f03c02e0038800d0700 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 55259580 1250 55258330 55258339
    0x5160306050906040b061c020901122f0403060608030405010207080604150b0d05011b030b1002071703090a0f1a040303120e031902030706050105061c15091d010b 71
    0x6081c0300e1030b00d41c2070309140e004000761000510803041d4400a0420b001c2c000e004c0000c50004803100c02d0405058002c0d000c0c02100ba00c0b02402c0201820710701080c0c0f0002d8000312100086012502a980c41c85420f080d42c490002d29218078098582c5c0b9901c007520342c03079084000c0c3c0350300001d010441941c0c10007500300280403190240206060503541c1c9140f911414090980c015201d60008405035129500000b038a5409002007160610014207031504210080c00400401d00e40b1140d2440d900b490203643c824030310070b50301034184141041422030030f003440c0c0040c1442d14030041c0300404007502d1b080c00380000303408409286d154051811041c100d41025100b0003800551091004100194010011910904541d0300200c0e4481450140710b180d80282c1c2c0101e20452005000c0e2003200d9000f2005000681c0200e03014840390381c0f51424010544070708003500480100851020010351880c3c3c2c8001040740c0300407940c0350401c0c0e451071504107440c06d0314040620b5543c21030120021400c2441040b448010998 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 55260830 1250 55259580 55259591
    0x703390213050708180c0d03080a0e03090f1306031a0f070306061e11060106030e070e0c0f0714060109050a0b01140a03090305160803010e0703090f030c140105010306051603 76
    0x81008000f013202a0640b01c200f0504542c0c1c0003200c030280300b030001c03024000c0d00d021940030700c6050080941d041a5040000f9500d0280e24801840c0040111804054054910b00c0b42c61000070602c000b401c41c00780d0b0051107a41e0307400048001142c00809400320103070304410718181d083c0101e0410018002034202803e00d86000401c02646801c0380c0301207103101e0242c00504401182040c25103174a2213224968006006034000810190781540c0b0061425080070111000c041e2122203002003080191000541c02c502480401007265540f001443d01501c01d1951b0300c1110305c0c01c4d8049241100a8124402c5030b51a9020059607003441c1c03254107136002c000d1038131400115013100c3d001e255218143c2200c007050b03203030680c400c18980100b0844500841d884000104481e190604444c06e170401e008841030b50f40103038042880c1b28480c1c016400c0d01070b006280880003141c81d0350140d40c0c0d2031400500301d410b0014411070b45850f140c01c1c4985130085006200204092926828904000541d44a07060515145c03c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 55262080 1250 55260830 55260841
    0x90c070b07020712020f01030f0e011508030405131107051f050703140a020a270303020c010804080405040c0306080319180602060c03090c1201020702031908070339021305 75
    0x130b5644003045d4041e034200640b06800b0740101c1c044c0c15500702c1c030f44001c2e0030020084800c640550003041449892400c060b601611810345903100d110b14801c00c0e40c03000da8400d400c040710300e4580c020008442001d642a19001c80c59607800d003410303002008840b08101c188200c458081c41070103a950b00401520b1b04008000c8420700032120880b0240075400b04035070101c2d0200c3d101e070003000002207540340e003088446c21101c1000c19074421030150101710018060700c441842154080d00d2240d020399442800303103041071309040c14080100700720802d0b1340816032240b00c00904004144020401d01341c851004080b06429110301a00d00c0440701504c025074002c4c80d0007040000e13808149150441c810080c490340e03a40b164501d031841c1c080d51b0488190b01032201c05545c2001c1d04154000d04000d8801c0e400d44015010101c061403495151100c0034000314000c00c441c8000a03c0b0344140c0e400e240c07040e1180701040030f2148000708003035512602140eaa900700c1c0040d800390301c2c02d94418840600300482c140030070b1415 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 55263330 1250 55262080 55262099
    0x60e040303230c0a0f03151403070e01060903080904151707050a0b1c09080301060207090b01080411090703110c0c011b0c031202120d0c0f0201060b18040b090c070b070207 75
    0x5454030082041013205000b040d0354400c3d08200d846100d505909000c40352140c0e80b400704000c0180c81e0703610a22600800003100d4bda0950090704990300c40c1c80758883c1030710315210321017550700c10310605034003664401014900080ea00c440b1070280400c0451035450000014489191001a4010b10b114801c4400c041109113410011201480104804584c416164003050400f81c80040342c01009400c000c0000b103000ca134002076010407115000707414801240e6140054070f6524094802408190700c2c3c3c91041c016081901006400043d2880c000174081e012856407643c0d43c00002003401c0e55004490450300a603485110114092419001112811241d9980c241840b410f4480201a68a06407044000c1402486145400200304207100ea807141942070200042040c000c1300004a11030301c1c00300007064414850f0000742c41c681e2903403c1c64440008068020010300301d120035030090f1140c584240649a400100d800707010322149094641c80186030881080800500345011503102802c100b000c10072 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 55264580 1250 55263330 55263337
    0xf02090403121d100923010b0d080a090f03030801030303020a0203220602010f02030f040f0203031210050405070203070c060e04060b07050106030c06081e0c0909131e0b0109050703060e040303230c 86
    0x10321440d06c9800665910310240500740e8035401591184030781c001c06003480311000080c0f41c82e80c4150380d89070886440c0c86004501561901000c0c0c000380030a4014400a4001c0e802410141403a0041f2030034030200c00c0c031003000c5454000017502c14070b00003402005070b15024000c41d1003020581c002541145012038921008900081c005040c0f1f1003841d20880541d2401d0048405003441501030084a103082c013400800311099200780d90003180341200184103148044103607045568013401c00810b07146009002c81d80c0110b0f07079010f13a9100d5650540019108101c100500380b084c410000441c1181c5142861041e03851642c0c403035820310246408104d01804150000d450007141380e2400f40041d186c4083d121003078043c0c0796805030048105018040d01c24040032840d0307e1144280c21161b1090b46d0a01d078a40c203000e4900c001421546810018005110903800440c0e00611f03920740012465911070001d5100901914280d020a580b07060341c911020340700c21102c0121027944042c41c00c9013171042d0322500700c1c403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 55265830 1250 55264580 55264613
    0xe03031e09130501050f09011d041403070c030b06030f030d020d1404050105040510110904090f0b0c0d0c05090109050d060f0203070509090f040f02090403121d1009 72
    0x36035080c031000c421002501d030303240c034042d0141c1c1c000100045a10b00600d03003030082c54855011200350303c9962501e20714441c140c0d40380e40c8046000554660040144140c058000c49071081c842141c000c0101040019100b03140c001c00113007018516500380304001c41c501501c15070083e0043e0001095181001040703400600c812100160b81c0d140107060709000b0001e0780f080c000a610f281080c4820b002054104034052400340040d54400e0b8000e070000c408654646022542024040c003640700f061402d5404421035a000c1c490004d6030f40b00310780d5101d0400354100c40c0071082a0b800700e10b540c2455280c2c4102410300c802420030b04c3c500155100040c08150f51846034a120340341012201e810808207130407000a1030801c80048d5100d00700070304042c0050f0024207445006442640001c1c00b121811a2094001c81c0c00c104e107040984c0142d024000c1200700200305405010780040f10800c0100e59102d8001c0781010004140d1407542a18081418130b0700b28982a4038840c00e03c050079002c12400180d042511 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 55267080 1250 55265830 55265857
    0x6010b0c07090504120f09140f03010902030a0308041202030c030304081810030509010b010c02060d02031f060f080f04110402160606121a1003030c0206040306051e070e0303 76
    0x51241191140c50801107400a09140d403c15040c07104108508441070b800e82c005407160403402078050b00c100c2c2c2801852080302c1c465054014420590308140804000f00c0b20068008a2103c00307039000310f072074404222011800039920308100400d110116001000c0d07ca030603c095440c0005546800340c2d42d010141010348001c0c0c0000d036001c040040840d14104002000c2d2504401d0a028480540144411a62070f510743d4284a8040003561250052610312940282641d04113804201da040007074000510b41c0121581d04c600c1c2002c01200c180c1558010b2a181d95802000c41d0624001444c4500c0a401450f21a05450034440050080d1100c10721048044d00d0060320303408201c0c80c00351080f01d81d074405041d07203182941c0420208500260300030118080c3c1d002068241c9006c8032007601442c122480e150f801d0320258107000007445403e0071180a400104103c0c14280c0700e44450003101e00c2a103d03103081106e480030240051040e94240c3c2e85c0b01c07806040400d444000d001c0032079201e105d0300b800394804 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 55268330 1250 55267080 55267087
    0x9070c03030b010c05060405010914030403030504140f060c010e100c1d0f130605090c07030f05071716110307080c060306060c15180a02010c14010b06030c12130506010b 74
    0x96441542c4021300d8641040443d034650602e810a14001c0c002e406060b6103240590520250441001044034112a032542c1e41c41d11b8180b80c141120b26030440c052071141c1c09003540a070010b0560b02c09010b0f00b010722001c400000d480042c3c4c00320f0392038842e1101c00c071503401c0c2c102080c100b0f1050300480c070301d100107140d01045041c44419034001060139001d0344800c1e60000d01103a40c85210b081d25480401910400d50b40400a030b160254202d0550264400c014001409040c14000c000e00c900c0250203810303c18040c001c03800a005004224681144010003415195013035204140010a100c501aa403405c0d00505815400c00d82000c1c0c4402124001e41d010301c1c80000440d9007074079030004446240a030700c801d8480c0d80c1c440c44480c221900c0e0540d80785201c0b101400e0070881c80c0001059020300c60394140c6804100001c20b50343e0a45004000c0102841950f8032012a60741e80c4442c0d000714400c282024030b8503034400d02141100c00c441d5023700040c000144c0c070400d0800103000020f03001d0550f800042c01c3c030345 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 55269580 1250 55268330 55268351
    0x80a0b0102072606090304030f200607080903010b040501050a050d03021518070f08030d0504080c070608011a0f03010b030c0409061503050c030714090105090303041404050609070c0303 81
    0x40c00010764840103181c46081040ca404219528440410101030010707603405444205c2d10725580c0c001e9000140400025900400001e000d880c00c07013040c07000f13080d204e0074240e04e0500028443e40006409a50318840007425190900d000e00c100301c00a4003c80b030801c025410400440da112442c1d0094601490098025105050003000441c007409001e5007000316520341202c0d11104980c44400c0c00d41c0500c504a000b050304100000300d4401c0d102858001d505003040082110301070107024009444403d000c0087e9000140280300781005801661501051949808803034401c030071190301040c1410782c040c8130314004c8581100c216411a04003118180c2c03a9201e054500e611031180c0d910100c580b61518000241008400031810010b000c00d84042086507036a2110001500c011960180003803c840b010021107160031024089070201854510f040c05c1440010a107503600035045100300c0d0100c24045000e07441c10b402080c0c0c1c0480140d5000b0141d0500d06000707480300441c85401024075445010068 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 55270830 1250 55269580 55269583
    0x60c0c0602030c120c0c10050408040b03070f081003080301030b0612031602030d0306030224040902120103060b010f020613050102070c03030c05070515090103050c040b130905070c03080a0b0102 85
    0x10000390064011560ba003042c0550043d954460340001c1e100d03429610004140c10300e5003040e10142801100038100704070020340d0120040c04014803c807000c180510010541d0703401d80018521a026945070000b001040007005416040300510010301314608407801c2c0002001e400a0740c0c1100c2c5d1200c0c600d245615400005503482155020204440c80041100b0040a05d0500c0020045000750191583d0303140703501049080e614203002c003940040808440d0715070ba40c090112002c0840606482c00c0c10141c0303900b0484240e030321051604113040c02d04801402407252a2080451070442400c113104883e4190f00041d48519004103980014040c0e04c0440c2b040c40b03000e40440c3d0450307500c07040b11040309031689409000780c030000400351000e115400000ca0383d8201800e02c0c80390400c0e48402142441074030001100a0107000308045142e035014880010b01c0c040420242042501169200f00601e0401d03403180c0880f80024011000c01805251a6000c6500300c104250480c00c00c00300030500060080040c0d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 55272080 1250 55270830 55270847
    0xb0303040503030708030f0708060d020d060912030b01110a11090c0f0d09060b180604020f1204051e070506041206090f0c050a120b06062b0603030905040e0a060c 71
    0x54050100013114010040300400440c8a958500a903e207180c49094046400160403500d15800c80c180c508104050700e400b41c0c44c4c5100c00c2c4a4103000c40d6074902603845842c024840440e0002081c1c4400b1200110b41c1c2004010003044400c100038a1820902c3e1925140114246c50060040240802180104090314120303100c440309241c0c400d40c1c8841d07074522003005002040090300e41a2030300507050300300c2c6088248000030001c14402130845403280c40c20800250301045880c986e011081010314840d0306000d010343d01c0fa90150380a80350000c50665141c0d0700c40e10300724500849400c140c000344401da0f5040186d4040e2068000c1150310305100d8a01200149002100609807100c10030744501000505030448054400507142c901141e56146100d20b1044c141460040c14055900001115400d200000c0d000054508a00401e0303600e9604005403545218000c118400380c5403942032060603000311716640181015901040302c0500d07000403030f4844603460781c01450716803240101045141b080a0300f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 55273330 1250 55272080 55272089
    0x30a0c031808031803010e0a0303020a09030204050c0705060708010e0106201e07050a030f06020304020613060f0201050105010801080613050c0a06170601020a0c090504030909090303020a030b030601180b030304 92
    0x92204564940e12420380d00c0d04400f030104c10714814822503c0b407a0a060140c2c2809501c86401840146469035065000c1e40011104c0810040c0d0705000001507079881c01070901038020032614942d9400a414107908052005040c9000e01503820010081c0b1170601c2007550464502d841d00980031600780170084800c1d2040c900c064168070586084598105007010000b0f558242c040407140f2041d034400c00e0006203000742c41701a04a068076001c40010035103d0f00115807192000f080145030981d8071551110301c440a0b003012001560f490f4150740125024400c040c050402420424465803610060560b5080c005051341210200c061409081007810440b04064120003049610b540da140e50005011685131000100e203140f0b600701240803035001080d0103034000d81000f102c5045504003282c51014000240c000c804018038000c00180682c10b0740300301e2078000d2280c1da000d0713956010114014180c41c0c15104041c42500402c0041005030300721000600c600001c0200401d4400c06080043d013503001c1d42e8007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 55274580 1250 55273330 55273367
    0x10050a02031c1e060f050f0303130b0d05010504110712030902150901030f02040605040b0c070b030106030e0c041e0c0c0b040501050117070506161b0f0f1205030a0c03 73
    0x12010492402600014070f41c8102c08103c400d0352110f411080280c51082c802c5050340d0b400c4900900c0b030f40c189800f004000d10340107401c45c4c1c030700300313546106a00301c0000380c0c03044c040c006020907113920040c1c26006480c01031908450a001c800324a14070a402d130301c2000002040403078002c17660702c0b0241c0660001d4002c0c07a002484049180d1204420f018141c2c02960f03d03a0000b85440d54020016990b413080d50155a500d40da014141070410031220407551085521014030710545100007180c4245d800118040d2890703940105005264a000d5890b00f0b0004a115200701d040408000c3c06411840c505030074075410072008240202c3c1c0c200c00b5a244105040702815002440c0200030600c201504124100c441d40c5a55954000c4401403140d00c4810328002c42e030340980300b000110194610340c40c00c007001e2801040d00b0b00d00c080d40e4030a800860709613030b8002d21282c400010200040c8040c0c195100c010202520142d00d400700c41e5590b540c903031182d1000441407040031941e070300c00d051141b180ea0981003010030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 55275830 1250 55274580 55274617
    0x11a09060d091505040b01050312130e07090b0c1606020a02031011090d0602030f0609040f23012f0f07020405180604111c05030711040f140402090601090510050a0203 73
    0x6d20746807410303090054600912455a0001444d2003120480d100c10b030b2441d1310149568105035200280040190205041040200b8003088030700f001001881510700340c030001c201d800d41031058080e0035441a0301441c01d6401c00c0b0051030144c2c80100d203211080003120800200c03002c20070300c0504a0700500c1d44880d0460302404842d03041010700c1c1d0044d80900c000d442411920b544032130800002c644d044400412100429030750300d002076001559221500788000301c0300c841c1040b400c00d40f42101c20017040746410040284074105c40c0b06468a035205001d80d003c0d0301d24900314103c3c2c040401071140d03100003030280e42d40c0c03400543c8041c461684166101c00410a4034a0390410703041c40c0500c1500701c0111171242d000c441000300364001019450004581c00f030045d41c18100a40c846038240c1c02c00e208811f401c103450360710640d034002c258414000c3d00240880e4942d028200f90041c85207848000305540d052086c1c0c1c010500c00c5c3c1e90b03452080b10415205190943d80e9031001d00041707040d401426102c80034001c044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 55277080 1250 55275830 55275833
    0xc091306120b01090f0603120509130e060609070509030a1b03020307060504080705010201020307080f130b0c0d0b120a08070f020604030c030302060f071b0206040b03040b011a09060d09150504 84
    0x4000318104c60400d603090000500c0352030078130100c541d248030003480d081070180210705890046000c1d0502140003864400d8085800c03100398182d030b6401d5801d14260304010308000d01840c06e104841c3d001011494207d0a158082d000300307603641e8200c02c0203007180440080c8214010694840c210165038054241e500c0c10703035240000361a42d04a030142107001c0c0520400400c155105109032842442e0f01c0d44c0705482a2035202e00c8100351200076052861100e070700343c90b079404034800c0c5003158060728160100554481c1e4184480f0215070184100522803404030720040c0c441980098038100040d000359086a5541c42d07031410540e20b00290100035080b542c007040005c14003940250500440303029800760b036055591040d6102d240541140c030740010032100003006102e0f07070402c1d01101c0120b1024140624154484010038010b80084408903003920a032001801541c80500340d140010075601a4107003880310101c00181c042c080d2045891046659010440500c0f43c61290100218031303515081044d41000d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 55278330 1250 55277080 55277093
    0xc23100e01020405031011030f060d12020606100809070312051209010902040b04050618070903141e060f0718050414040c0b070c12080715090c0e0c09130612 69
    0x920555219005400b1007111b0082240112179001c075280401c6461582c1e0140180c540c4400544460f0b0810f0f00135501200081c14000d9140d420756030707a0014501440c04000f0000003803508454281080035032005c0c4410240000340b0f0200f603130f50102c241d5040d045202c2045865000c1d00007a0030191141006005c400d500662080c00214000d41c0c040c08809414400d0006a4505854040d00a0342c400308008210300310b8111103030440d0b2985040d500440d503d8a5120040c0c0d00030074008215004a000000c11442c10040e1841c1a03d13884080c041c6c624004001c202607810007481b000078030616001080090142a00032005043c00810401c80804071203402007416808850480f400f03400c40d140030802c4900702041d50743d001d078050181a081420300c0141c03410000140e9080703079000d1040c0b00c22000203000031143da0700710640c43c00002e0088010309001110604581c0310260582c03513141407001d07100302003003146c906c52030680d810b441d00448058004001c01c0c903a4015021541801c80d1070b02000030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 55279580 1250 55278330 55278337
    0x20d05071d01170303130302010b0a031a010503060412032307021501050f0f040915061701050a0b011b03020a02031f060b040f030b15150909070c23100e0102 69
    0x21001400101e80c1e0301e402d41c03c40c58510b65107002e44268810700c000f9a041c2c0c000040b540c15035100c1c0c8004501c490030030001c24004034950300200d40403d003500c5082107130400021000d0041c0300444c002d049509113034a6007015015069140802c06458045010b0b58040c2b908049c1070f84a80c90740303007107041c0c9805440203445130300c0c01141c40c040c2c01d40d0a00019061504041440c40104010100c0c0c002036882030422008004031002140e1181903051340c04c3d600c0142e80701d05401031030310a0440d01c0700c0381820001421560020051302d040e501d070144240c5e03140da104052100a00783d10010b440043c0c020f04090b490280340c40c000035890721607000d104503418048424152800181201406016114440c016460260740079180381c05900702030800102ea00070411030707009140d04a140841811f000301084c94407165403441c00316190005501044c82c05c298405552041691400010304101d554a48a8108030040810340d401c43d00c1030001201e100520010a4400c12024104040d2583c1c040e02c9020f900b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 55280830 1250 55279580 55279619
    0x50106090b070f122d02100905010b030a1a071704020402030402030307050a0602090109050303041208090a030501142e0303140f0c0c030607020303091c03020c03031009110903030301090207020d0507 87
    0x400200d50005c2d80c445040c0314804400d804c0d0041c1c2190344048407110000c005030403050f00e0395901c0c2c400404003900e0030300505038840c0c007800e541891020701410440248101415a03c2040740c405002c5c0308401d25101503540042d41110056a00d0302d0760b0000900d1802000320181c4203024039148901080311560003041c2034030302a25540c408030f94070300825889004178803441e000c803007100f079001d0002803100c03000b00030b140300c024030f62061681c070790b207400b401c40384071071f1410581d120a5410310942c40c0c0001b130300307000a07061281d0407001c48030380090182503840e03180300080902003580301507200301c3c2c1090142c4140b440701e00c16558540c80190410b60741e40c0d8040c21024002c0c0122800704500901c04811280b00d500d0340d03c010b01c545440c4040c0c010b1480700d4204c0031410190300380104c4203d004140021409849652203031601903042181c14000c6580310b098200c00b020f0204141151034401009490459941420040c2c542c5050300208540e0400c1c810010914019040d02262003113034600c5241000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 55282080 1250 55280830 55280867
    0x218010503061b07020d02041508030c011503030c0b0c04090906050105090a0b240f0a080f071806080a1103010e01080d021b060306011e020c040f050106090b070f12 72
    0x1621990014030041e094020b00340c0c5200000c200c0e134005400d1003010201c0140c809000050f9000401d50b60502c0c003407054000510a400004280d4500d0038240541c6030741402c025104411546540d0300540051000308005000600074400902545164010b4a0040950705014000c0c00198640400101024000c03544620390034000b15001444178400d0000444028220b03103440e10491040c115824074050a010b000c4804000200400394400d000d4814a4165150320b84113060100400c03445480c000c1c100001c000c25016444017a900803140751044449078100490740b034458501c0500500303200d02c0e030405620400400098140c0041c45a00c1c100c440756016590740c48040603049854a80c1d4117008043da4600c1103a001c240e182c44801560084014102440c0071a0198024000610f0f02e002d60405078010020500e600e0900303020b1034569202d0780d00c2c20001981452400b6001100e50b0050004103c0c1c003098803410042d0039000e00c1e00b12900302c0019180c0f04c0e101800104440c500c085c0c01b0b11407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 55283330 1250 55282080 55282093
    0x6171f0509070314010b0f0708180303070c0303080f040203100b04020f0a0908100e030403060b01020f010c020105010f060207031505180303010b07110306040f0210091d01030303060f0605030411010c0218010503 92
    0x3003034400341a14505920000000d1900e101d80c3c92707010035608200610010041d41090501c0c603a941080200191442020000406450b50030082d0118500901d0f5000c101c0300002000b0040c0e50108034012a0750340000000340503540c04010800a02a0722038031021014000b17003500703484e60003211220840700c451084580301070601103200e054600c01112980158000e02052001480c0f50b0040e88d02058188100d90000214100a500f0354821808540160f5520401407203001e21441030340c8041c00c000c0c0011b000c0d003450350799020f03421903d83c1c4460002c00d6130f030008500d0380c0b4075512102e82980b14600842e6100c2d41c4406c040461940004c008132440f1100e0320012206080105045118a400520310030100c1c01c2502407010144540d003078a400c10090703510100d0410711100c56a00842a003104408580d81186009811503d06400064822032040010020580c1c0001220381c0305a0066500681142c01c4005941100712481c00946c00000340014164403130000500360304131601141280d05 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 55284580 1250 55283330 55283339
    0x302151206060c070902030613090b0402010e030c0102030d1802090c0c100606020309100315080601090b0d05070303050906070b0a0f060e060f01200a120906171f050907031401 77
    0x42c5403250b181c0700c2d0555004400e042091a010760701640e40f02d80040c3c22181610180c07010082114104401100c011114100b400b044d942c1c04200a80400310aa00030b200d401c90010010390b59004004a01c00c03800d488201040505544200070650258040e210f2501170034226106000c982116a44021910450b0b10400111280b4014842100d03c5900594a4080d26200b07012440e01c0c031020800c141034039821640c2ca44e40041b0300c0704004048100c050004d0f0b505050841090316820102548107510014141001c510007140700000c8036418203000f41d913902a840454203900950b50080c2c00d44400504100402c04150801a96402c0d14a000c020942d03e480420000d080300b03480796604183d801c14121500d501568441302030070280722000d81c401480c005441c0c03a2240e00da10440d0700b40800e070610240705800a028001406481c1800607400c2c420281d02c1b006504000c18410900072001340314074441280643c90030240a011f820f8044c0d5182c880d002174007801502c0e041081c241c00503000010b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 55285830 1250 55284580 55284589
    0x6090920032a0a050a09090605060402040305030901260f040326070327030201020912010b100309020d021e131406060f1306090f0e071e090302151206 66
    0x540d44a0103000c0d803660410703009445000711102c6840c4580181140c2c0000c00c43d90389131202d6000030300c110140030500c02a1480c20800340c0380040d02c281e0150f0b0042c17105100140007c000c4d282c20020038a0b200310780c3d910b4170701826240100120f0190800e181d1034280444401c440d2400c0d449180251a801111004007200111035580c810050300010443d401040481d0302c01c1d0803142d092411031200c0da0324000c07a1112260100303518402100035070343c002120301c05400d0081038011174065000003045081040008a000008400c0e21142007554038403451045581d681c1c1c007015000d801920b20066858000000040296030f04015849883d0701c2c800c410398480c16014080c00c0d248400e250140300d854040901c103e6400c1f81c000003105603c28041000013072414010f41c001449107a59161000307140120010032000503412100b8a0040042004807041d0011590405440040560482681c0a040c2140c0b2012250402036020400c10400a0b4040320a4090880810341c100d0811241d04c9210801 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 55287080 1250 55285830 55285843
    0x30c060219060e070e0114010305010807060807030b12030703020109110d0309050d1a0f04020f04060302030c010c06020c070902070506010f030506070c06140703021206061e09040609092003 83
    0x5011000c6000181e0024606400507284000401c080302c1d1001d4075088420500381098100e4411703c440040c1003441580d060186034010560300000d0044207007000d4000b401c00070010031407402d150311091524415220110208180c594060a03a6140d010074030300240a061468025200c1d105071004528203454450340840f40c4540c562102c85034641b900c8144610307100f0041c0c064400a074070700240718021101600061080e051149900200d252600c100841e046900407107600407441d101081c0010707240000c11910160342400c04015002c400e01d01000070344100150200d40f800741000c0003405000540281007201e11031000d0702d08903a260740b112031071003c0f184805095940410081600180a5074064140b90701a400c08182c4003000083c81e08112070680310000020b5001451184202e241a40580c010404a0703c0034601000b103c0e81c010f0880c0381c170007507441190b0001105003d50fa01c561150300109503400050080100d1400c140082105003042c5002c041107144081c3c0c40344c41d000c00d80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 55288330 1250 55287080 55287103
    0x30106060302040b250501140403120606080c09040b030f03040501111203071409091305010c0905090a0e160e0609070f0f050a0e090c0c010606021b040c050d0906020301030c0602 78
    0x91400c0c105449160311400134041e4880d001c1300605516180400c1081c0141c23110000c051448054034141031074002c01080890101001c1c0750b1808400f0700509510082c0c40e42c00c00401d20702d5548852409000800030411504180d074944540b0301c100e428840c01102500032998240c0320010903401d0304074001c1d101e40300589004140030080000030201d6003d0340d200310000c8094080a4204051200464200007055900013851140d15400c101080400d002e03411110000746091041c05182401040280c54041c00c0207100c0c1d5100c000303a802041080180000942c03c68a06000d00c3e6541c148805040c441990701c5030007040440009038250b401074200325043c0349255500e42d1141310501d000c9801c0d810804540080041d00c1e420910301d5500c81c40d0380c1c2d000309079185400d41d0b03a45855002a085810b107038429429504071145d45424490a80305240c0e5504080d2000308544000da6000c030340d544902c50100c1561450181c01005100b5198040d60690740f00f00a07423001c298486005a03603400d1241c07207 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 55289580 1250 55288330 55288349
    0x5150301060b090103021308070906241d01050705011d0c0109080a0b19050910050a090c2913030309050405010506030402040c12020703080615070201021b03030706060303050903010606030204 84
    0x11002c00313512aa0080c007556800401c0100e40301d44840c5814188202c030b80c40620140d440d048244100f8000301e002c540214071440381c1c1d01b50000c6c060b038042d00c04100c000d40d44134801c00d465400c650a13400340c802c84071400d40c03050003001011964190304154691880c40320310a84105c040e110015401251900240c850780c40c0184404080c6503200005050000e112003801825414404c000000e14002d25009008540141c030000c00420100d800716a0700514032100e5070700300100d40010800050781401aa0100b03120480c1604000c107585800a0314103403020403c0600280041e40c0b190000c8848041c0c0c0d1081e0360300003e03150740c0c10821003912000c0c014154024401c0006c0b800610702a070000c81d03010450700706a080c444015904804a0b000740c4000d0300812119820420b942c9060b0f01c10240810183c80f038682407007102e800003940c8008014451900c2d0171040760350035181d601082503c88903a40224140140c40e26850018a0394118080541c0258201200424814000e0091350243e503d20701 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 55290830 1250 55289580 55289587
    0xe06040e061501020c090a23060d02130921080708060907030b0d02101d0909120d060e01090e0d030905030f1809090610060516141903020105150301060b 67
    0x2501110008211243d05520800f01420381640314186010f205860948000801ca4411080600381c0c084001032454590a5201042203c0d0384244560030140d80560b0380200c3c40400e00a80f0005000c10b1368080c1c500402d405400300790b40c100e0840c86024129075510840f0b29183d1080a885801e010340706558003402c02c10010342e1a5110307a12041e1480002861050200195004250910442c808050002c2e1402e814920000d480e2500150003d4082e07072000154030f050001c0d542c40e060030119542d010701001420450380d403026041107000e003a50794840007003035945003003001c010001c52100e4040c074010310f80c03201d032070391b00a00ca444103590704803000e1071808043c42c510841d15800390f0200300128a00c841e40400f00c1d101c2221071841904020018982c1e410070302170300c240c4d07071245502c040200281000b1040e00c600c4501283c03405503502c806194194529049140d05058024040150740e0804803090014198150000760080c000100780f044050281c0042c54241e44941c06403088040c2d040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 55292080 1250 55290830 55290841
    0x3010503061303021c260c030c130b0c010506181509070909020403051e120d020a0504031a04060b062a010b03030408060708060a08060420040c090e06040e06 69
    0x181441083c468810744000006080c290546592514804000500b5940f4101c00b090342c01d2842005c4803c0c4071208000c207240801c2d03004c82c00d06c00101080c001200103d6900c481c00001e8040b000588003104010f9100d11800550600a040032541f2503c911103400044000350340030451a8096a60703180440940f201603010701507000005810401007007039a070390000d20071200d80301500c081e61050000d001140000d205124446100d9142038000c1e0b006804040c42c401500c0084603040c4010050150b200c01501300192641d0003254806042007140e80000c82d145141c421010b48620f22804c4c041055010407010b20845010f103050b174100304920364a40c4a0b0700d5982200313980071446494004150301042401090960300300e580511219448902030080f800d412800321644044195013003d8001c0c5801c2c44103907114005807002d494408149035031203042036a0208001c160f00042c3c01400710444d1a10b009100c0c1450b403141c40c81840311000452914070302030280c12201c4031004020502c0d511403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 55293330 1250 55292080 55292101
    0x1707050a031b020613020f030a0803040203010f0219030903030f020f0306030d03020a020c0105070203190c06020609160b0c0c0a23120604030810080616021b010813030c0503030a1e020301050306 85
    0x1780c00a0f64040d401c00045000c5a5003040303d0380c00d09102d401d9031030b00c80c1040d106050070745010601d40c00d41c00f4010f001d45000d01c0d10b40a4a0748400000745030101c0c440e02c1d42e00b41a0010100155952605400003400d504050318000045001d000d041d0126400302044d842c0803022030141905040c0183c0150180095543c0b242c03020b00003890004007580c16000b00b00312078844264550000302d43e20482403400b00011a0180820390340900301030042d00c801501da818910030108907024191007418003245d9482510820030640511840103090181d44586819a400d5481c0c408800544141d80a500781c0000b401c1c4111016450205c083c014145a1540d550035108100001c0030060b05d542000f20000f9404e008222040c0603445064520208000c0640001d04240c1001c0056082c1c03455030601c0505640d00400440c1c4c0314070900002d00c00d0301c0036450100c0c2c241c0500f4002412034440030041c001d003480319610800085480d41e04100c0290283c1612009901091143d144d040d0045c60004204124 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 55294580 1250 55293330 55293361
    0x1060323030f21010602010510050d0311012a030902060904090503071b030308070f0206010b0c0f0f0709050f0907050112020c01020706050601020c010908070b0a1707050a031b0206 79
    0x100006580c108507050b840a2055006401d01c2c451240d07400380d40714105103030100ba06001d000b691000303100910b070540500055114071301c641c901498030b259040342814840e00c40c030304e0310200c010000e200340f1560000a000070210400420b11014440140c01000d900a200b200440c076405004142044c00140401004200c2844e003960701e8001001520005880d140c980c10350300c90b401010145250441c01c2c003e003a00c07070081802e07050007070207107000a8407500058002c0c11640312410701641c80318840c1d011400d10b441c0402e5186180320780c3c00780c003040300800704011782602c0e1112010440d80d500c0d020807003144c04050310309060b140c100b1082401954070406108400840f02d2901614200c800301c10306007207074803028054039425591424040c4540c1c3c1030160005000f82441c2907d08030781402031051300c0e520f2600ca010800c00340090118001c9014a0445420b40d12680c2401000d15141c080540b03640d000c411403000007450604d0005003215102001001010300b58010029030350f800700007220b0f000c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 55295830 1250 55294580 55294643
    0x402070804150507050105070e060306040f110408100507020c01050412030c020d0f0c05060a1d0f0a060f02070515090d06090b010b0403050f0f0c150d020f040512010603 74
    0xc000c201c007049440081c0e1a04200100c5541c03816910b130524100b01d4211840605180300b046072000300d030540c550720102505d8004008460002d000309060040000411484008022841d80420700242c0814080745441d42249004d205000c1035a5205007280c80315800c54413180422420301090208c605070203402e0a00d548a8104440320b19280e4000513210710308603601300d40108148640c00c2c10071042030441c4004000075100c00d4141101c42001424002c00c10400540c40d450030248a81195900e000c0e040e0807100281050704ea01e611008018042c10401910b4805482040400651070030408040740650307100b038041071b04200302da1003080300c840b10345238050300c416840340c150341d0201d181c0032542e5008042100c1860380d03403451803520794140002c65944030302c96040340e040700348040804500c0d4070035100111220401460315040c00c440c240034004c0c0403c2520710101d01c880c0f1080c004c81c0188150381c00bc0320940300c000031000c0180c1c04d0350820301004010b42a001c480544409040c80c2001480 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 55297080 1250 55295830 55295843
    0xa050a030f1412041409010501082a0a05090108010803040e0109050702010e0d020706092408060607060501140f040e1e030904020705010f0b1008010302100302160c0e01150c02040207 80
    0x100b118424074544030103403000c0c1007821400036040002d49103000e0140031107401a43e00c540b5661404001806a4078014004403468440b1104a0410249201000010809020800d4480c494490010076a07040702c24403501080c0e5500000c181c840340081a201211100810b10040e0ba0802c0860405000040c004200b03664a0f032000c2c403507602c01400b820004840d9a801042d8051601600a05642c110350003a4508000003075100c0c00e0a40c2c0b4429001c80e1036481c01c100580f5281d040110310340d44204035020748811b14241c008540c891101c841034564038012500e175450001000708200072a0050400012550300007408441c00c070548180450111412000ba2410062200049810b990115008591903552801d41c40045e450070300ca450b020000607101c140e686056188060950841800301911400620f04040b824038071170b030100e80846d400240100145034151501d420001c455010f0445104d1450001041032951500786685041040e03a83c0100218550244802940591002e0301c40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 55298330 1250 55297080 55297103
    0x19030605060c100c141b0c13050403091a07020f0f040e101d03120c0f04090b0301050601260901110309070305120306010c0b0916060315050a050a030f 66
    0x2a60307220040c0180c006040b010704001c0004001c0074044840842c03121060010b1110700040700080c5400f5551780510a04a44034804421a661440c24107841689680102480036610f17502d002a0002401207200b078892a001d1500c030600784441d5030b941c038082c44e42080148a00360161414041d4070b0b040d144068022524070a0b01703400328080c1c80301d5044807040340e4004500c006800100348920040700818640c0703001d05c0c48070031030a9074032881030309025402130545d24003040e40d2040c1941141d000075200d58172260342e03543e03c2201d0000b0f4060b92101e01e202e546040e001407145e501942c80c0c0d5450715096034a180001003050102d52140c01c010303098100f02d40da0b0b00d88840301f07402d106000314007030301c500304c02404103500d1850214500700740c02c1d804a50804092082c45100d903003003040c603800184d110521076541ea48800c40c0301c0c94807500c0300300b142c030f000c009260003c0c1058050384100c43c03920268214141c6242c50380107002420286d40302d1241c02c408580ca0810109040c00032104803584104403c005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 55299580 1250 55298330 55298339
    0x3061903050f0703050c0d030206070f0e0307032405010e190e03180a06050a08180a02030604120e09040b0105040923030a110606030d030c090515041a0f190306 70
    0x90030310038000441c41a482503c040c41441000c120313081400d0030071103002103404810764009450750b4000c2d01090034001034001c0101404d0017a40120107929010b01129141c540d03c1c11300200c1e15400c90b00307000341d003030250000810040d52401140d040c0d5001c20150012500c0d00d42500418524500008440c82c0d92800c5048007900140010582c26a0040342d0783d8080c04140100300300100a42c1c495010711104110583c1c1c110340025025a01c40b05807203100c0403031b4038101c420508010fa0104020341c9405100200b004000444070300c0522107015550305804490148140200c203042521b000d0a450010401000300c0c1ca0203402200315944180c0d1548440340717241e00d003c0080f064500900d0015080403c0701b4107901ea211200400040d0b05100401941c1840c1012079280c0742c4010030642056140c0070fa12110300e028114901c018140071b0000da4540d8503855500f20309410034000c01c00d4544000b056800c03441e456400b501c500003060f40c10149451003410480810074484100d000c14561102000207 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 55300830 1250 55299580 55299583
    0x3050309070308120402040c0807020c0409020109080a060501060806030d3504030f02060604060e040b09070b120613020c030f0c1e0303060306070f210605040c050403120201060b0306190305 83
    0x41a0340131406013500ca410b0030300c1004155003003030701740400700480c6100f04056503034001070340021480d054030001106040d500048072410810b4018040c80d00c210005001000103540c042c41c100c0356103944084031600c458040649030030100c81e21000040002c00d101188210360030b000c117190741000c48445004114250200b80d82c0c0422a4140d011401074282d400c02c140c3c05001c81c980c032040c00ca40802c403450a08a0480044a02078400340c0352400d500002088440208205800f9200f4040019210542e840740707171303040c03100445080d800b850210000303100500f050700a8486422040020f5800c003901407050061a8110f480b07900c1c0c40b0f1050781207141d0000c1c0b5140d4000954007400000d180d8914180e0141803030034901401503010061f010790302081e080d901400e100309a00c040c0f6042c5540c181181800f070068030382c03070708400ea105241200c10b1003660341003001001113911a02801401d0581010140d00300c84503881034403100c010400024506142c8800340c2106400e0b420740100d0b030540c490b19000e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 55302080 1250 55300830 55300837
    0xc0a18120503030415020f1204110303030907050a1505090112020d02030109060905091b010f0e1008010305070b03060907030e030c12040810020313260d15050f0d03050309070308 78
    0x35140781d040007060106001c60103030712441240d1004410f5213450300804c2c00c00d000d44614009401d0340031003407000c6420052440c5d8664250240102100d8613800c04004943e1034044a1040c0c1d441a06000400201000310b0f4480e90310b030012585900d03041903a00d01c019584124011141c54400d903003044020780350110782c030155000e0042e0b0700c0c00168840c2026121800c43d007002d0f160703034226800001851503030340d00300e1140070341000203107414056404c041000ba2406d07207000404c07a44c85440f80e420789040d5984480154100d03400b40c012900a03a030b55201074a05c1384000e60304a80c01c0700f040d00001c1c0a10740241c01c42c04004c0c00d1401281d00d80070000d100c4a081150120b00c0741c0400b01c00103420070641800f04800c81d03800c11803d20851a5040981c1568400059042c0040c07012103014410040040180126044620300b01c46841d075800300380e641d4500420115441704d004402064011a050500c1e80b00a00781410103420000080240c2d103094a0b150001040c000300c80c4034191300800000d6448002c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 55303330 1250 55302080 55302083
    0x140d1218030605090606120a0b0a0b01030609020301030b0402011b0c060509060f030a061505040e0f09031b161401020c0918030c01090203010c020313090c0903080c0604060606080c0a1812 82
    0x80c02c210b0801d2010044801c1031f00c4880b01856201d521000049510703007012540001c035a5a00160100b13008006074040d11a0394858480248048000010300810a0700503205038400d80e5034075020340054041140b0b01c40340c00d50180410516400c140050342c060350007032100200040086042c03142400700e079500ca90040b40d03440d02150300e0303000400501c0610602c82410080c90b0406905080c01e0400c800741c000c200131300070b5442c40b83c0000842e00481c8107004540c03002000c2003612901c0352108840139a183c109140e006c1c50306800040c00500086c0380200e4028482e0164041c040c495498010001c0417403000d02115000300c115851041d420004000070300407040e40704000f1907e110240101802c68001c00705180564008002d21800c0e09602c2014005903240d950f40011b60020780402120064400c2e04000c1520400181140c1c402400041c82c42c807540c8914000d0200a44441d03007200c1d90310b0700380c603a690f40d0f10092040b107544600030b00c5804c401580c40280384069580e1511940d5407101c7c00c1c0030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 55304580 1250 55303330 55303333
    0xc06030b01090503061e0a02090d0b07110a0807060203060a090c1206080f120a0e04020307080405010515060306010525080406020f01050108070302060a020c1801140d121803060509 79
    0x661021541c10240b250010b000c110b02400366031030100581c518900c0c1071b01040ea01c00e07041200054840b40d0907410341d00e41c4c0700040c0402d41001082c0c500111140025070300c9501003000c03920b050050081c00640c840605030f11550301800e0892036030f5600040d41000d0071a59121507190404102000390344202040c8042d1a602c0c0c540c0400c5100501c0202c803119080181c00d030304440c5844080300c800040c034100c3e002075500c2040d035031658584212031a40e00b400603150300a0001082c01340290b03001a90341d0140b40900000c2005d9102c40c500e800880c1e000392103a0380c22a00a000003000c0e50f0080d03020701040c08491044e415410034445048030788401540044681c400042020b0252650421a04001a28502c000c2105505104d1404da4031100d6100c000e00c65000001e00700350042c400d12000c500c0d07100c003030a48000c00c900d02030a8240e1074401d0181c3c0780003500c0c000a02c41646800401603c0681d0802d05401607017458440032a151a02000510003244041c8000000100b903441800d10901d605030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 55305830 1250 55304580 55304591
    0x9040303021902030d140103051221071e0c020d080c030c01090602070b100f0510030b030607030905010b010e061812030309010906050112020907031e0e030403050c0418120c0c0603 79
    0x6a420106c41e000c2e407204415010031401480002e00c000340d100702c00c200715040d5944840c6100b654003000381c2c4012403440e03000030f0841841040c0c0c4c0c100145003200050350300711800c0117a0244046956078451240607500c411440c0240000c501800010091052a0810740f842e00040708002429900c05407400c440d065800034400b01804566800c458000000e040304222552030f0000c0d0240312209802514400d15400700c407251101c0c040ea100d002100703000340039540036151040014008084028098072a94240740c1d201c041c0358446c1c1100002d410008261900f88035081a12441403884601d8180d08090700114070004648100040e6104519150010038440711a141507001d4034810b921035901c0c6d004e50300d120401030307a85950351360703002d0040d1600061303558401060154035110a110340c044c140c60401d1031804010048010810390740240221804c4c180e2081c1400100c40c03c46249050702500048080001400703000482022a8203280c5541040d21070b850380707400080746510640200340d03180c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 55307080 1250 55305830 55305847
    0x31e03010e0a0606020303071b0c061806020102040501020a140f0105040b100602060609040209130b07021506090103111302040504020d0b01020d0309081605070906030303020307020f0304030804050904030302190203 94
    0x200700e2681c402c0c1004014801a450448041d560b07020180009051207003658610091a100c0e070801e86146070410b21180c1c2060341c8000290003094900c2000034030450020300450210f00500850b03080340d0040c1d0050200300455192046540e181c0c6901035500d00078901e8410000409000e00c6000341d018803a203142a0521112040da6490230317910a40075074002c942007100644d14503000507400b580503581e6164a540d000700030380217000d042000602d010028024880729a50004540700c001051002d070b5035481e2900b104002128a0900c8000c2013001909494005404c148a910800c1c0b6443d0401606058032003000070143d80200102c00c0d1426900c04803649150b03810000038031440814101000030014a0302d502c0c0a9205003281d08190520240507403003004020402c0320020450582e041005a807603180c000c0c00381d0300070b5800700d0042c40f502002e00d65009000c011101225800303d071842c50149480c00740807869000420076400d0682c01c0c400b001c01da44070340001c50038218880d4051650386000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 55308330 1250 55307080 55307099
    0x10510050102150601080a0504050312010303021b090603070b07150204090f050a020703120b0a09090f0c0b03090715030b0d050601030b0a2903010e0a03020a050c0607150905031e0301 80
    0x206034809410f09200000d00c20a81d820480b038540240d2854008031300c50381d403410158594800c42c0c0c03440340c00c0d280d82400003091541c00301d01e1000b01d1600c149820180c2c801d240401c00c504e002516a0b50385a00b010b6803c01003120140020025184108103010160006075048070890b0850381c480f500007a00e48d4030800c1c00c040c4920803103030300000d1503500310f01b8840e16880042200045c411040c10082d550891421030755100d42c2d00d0801000210028484001a403070050100489803004440840322480c01080c500c0003402078034460710b800c000812440d480c110714209106805040407091603a10309140103251540140c0440c120301601c000d0040e945545440c0c103031088020988030f106841d00021010650010503a4424801000e580070706101c8014002401045002140341d031070b01c00c00401302c080580101e000410140120305444140c030100061101510a110000f8054102c41408080d0060150702c6100d6240c000c40c2107030b003030800f1800407000c88a10901f0141e800c04d000b10040241e00003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 55309580 1250 55308330 55308343
    0x1008040b07030c05032a040b07060c05040305030f0a1e080405070b19030b0f060304150f0b0616030c05070f0806061203160f1205030f060f03070b090d05010510050102 73
    0x1e492a04009900c48000000d100d40406030503069041c90075603020700700711203a80c91956000c20200380c1c00e55450340c071803001c2031640c8002c408032411818500c0040d440d0380200140d40459400901951a10700c502e035050920350b02100d1560140711540340d0848420308103008001400045854003c0103040c58100310745848900d42c000b012060301007000c9104c1400403100d25110401074103010a40541c444001041014881c0040750030581c0401000113201110018142d41d5124010401c842050040d41c0070070b40d0250880c80303801c10f8040041c00e40d007082c0c500c1600f070018007030701e01140e040c46580d0b070f00d500b00708090f4842c2241481d03009043c072402070300f406001c0d042002194054440800000500d84a010300c02114440c0180c0e800380c20184159a504407440e5580007018000e0f5400c5044060541d0b0402d0780c03a400f41d02e12140010b403240c02c1504080c0c4d80150014010180d0b0b078a419a0a00540c1c071080d0800c1c4c00002c02c1c054040051401d000d10327402905600d130210f91490030440024500b40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 55310830 1250 55309580 55309591
    0x40909060c02100e0c010c110d080715021201030b0a02090d05010f110702090403030b0d060c020105010f05040911090915010f0e0606070803070507020406030f03080609131109090c1008040b 83
    0x140b034500a802001c0340090f0711781d50003c0a0905402a00103400c201d40d80350502e03100b0903000b0b12084556404c0200650050909a103c0c1580d07107164442004050228015117546c0750008030148014804101440c007840e52210340d5083c0945030140d8140428070040d506001110103030745454204030011054020709c07450000305844c00d801e080c810f40005000d00c1d4080c0010301490355400c44118540c07a06850a646c450b00218107114008000c54000c0c000c01007445403508a65219001240740e1600f401200529a04009000b5204050404006c0d0710900039028020900ca00c180b880058111003410a00070114000c1c0440301520b01550201902c40c0102a10301c81c0404016050000e1a0344e81525045029403511503114843d505c0414018020b640028201c241c1d8807407040c3c201640445110b10420342500d0b00c0000b625401c01c507030313030040601c807004100703070b80081d0052260b0818880c0160f00c4480e50701100c0006c1c1d84000820600b28165078180001008403081205100003c1002034210 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 55312080 1250 55310830 55310863
    0x1080327041a0405060d020607020d0309050a0b130b03070f030b04061214060903070c0306091502030c0d0605010201020f0a05030c0909070203030a05060307030201080103020909150a0606110d05030402090c040909060c02 96
    0x32021031f030000d54640700c0c2c040000d200d24030b150060014180b18166810241801401d140703405601c8a03081d5070790b0341021003450f00054a4580100d184080a416640034202944440000d000200b03415000b0f042007800c1c3e1500a6a07038000002c1a100d4005091314042c016070191807566050000c4504181000f4041c0100d68020848980041c216408050441e9003010000501d1507051401d092407645110189615a00110920401e0307103c2074000c0c24120035041040100d2079980d4016401d074000d82c1c610244204081c031924800318041e03401035a1020917240c0051a01a010b070004d81281c1050703414000680c00841005078401c49445013907000b4000720001c00c600d502e140d0000b000d154050100074006c640c0440450030540d8204012851b07806032224120013803030040202001418948603980000c2c803030408455400702c020525141020560f03842a1850b5566000d0120310300d009864000484002c04c400a640540b40c414440028031070074000c00c18501d0a680203280c04440c81411428 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 55313330 1250 55312080 55312099
    0x1060909270b1902070b0a0c08010b04090f0902030f01050106021204140409080d0e1605060705060f070507050f0d09050402030609010501030b0f031501090c050301080327041a040506 80
    0x1a161440702100e8202d81c030800035191552aa0140c2c1c480d42240340000b58214000305481d01006441c0d0740702407060f0700501080010f4502543c003211910380a1061507441203003007105101100f185d8100c620b4112400b50045030f40b0080d6800b080c03400396804501c3d0b0780d50355200018007900e5810303c4101e20300c11001221605003820060f140fa0300039002440c4d28419943d8620410070060400203880c2140b004040400c00d64a00214041d20761040b001c0e0003080b103030000000f10f004c3c80d100f81503070000c035000300052207240e031505094001e40d44080c00c100c00303000d01440701c2c02c0015010881e101031580490090003020b9050341c0003501c084000c4d00b155101c3d50042c01002070644030f80c04a181141c40900c2c020846140302030104010b50300e6000c1068042c00349441480841d102c0e03800441c1200c400c50b100304002403800c1812119401700b03000e0005148c200b00015089015000303020781105622400380c140302c0d481400001e00b101e040e04001107003203400309050001460240b044542c0500c0c16201c0c00d45 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 55314580 1250 55313330 55313381
    0x8071d15040f11070606030b0121020f0105070c0b0d150602060a110f04060504050f04020406211401090e07060e01050702040e01060f0617070f0c030807030b0901060909 74
    0x11009040114001c66884020000708400c035003000c0c1c01034091000c926a03544040c1440d40142983d4002501c012280c0c00000441c1808006020784440c0340d102c0d00c0d01241002e50800c44032112442040d070400806000311004203685402c01c1004014019040341c3e01d51954000c035050f607404210280b28005541000c114654010814aa114410040c009404403071258884014002c9141d684181d200101c0e002c6400c0d9006001002035074000c4442c80001c03c000010881a1720070307400740e20000703000d41c000301c45400070b0b0045203180c041c3d604c0404501402c00d20f4410104000903800829415254503c94103d42030178041580031f40f410313152120a8050b900c0c0081c106100384d29000303001d9940e581150140f0300d000e40c0030802511100d004146055510240200003401c50103400c07034003025003c0450800d500808800e004820700341c4a02d2920b500c41e440659203000001d04200038941c40d030b4404005039694492642c068100c94407144510790401400300c0407280a00c0640342c00d4800c0188001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 55315830 1250 55314580 55314601
    0x170303010303080f10060f12020c03040513020301030c030206070f050a0f11040c020304060f0c120804021519080603030d0908130801060803040b28090e15010f030c020a0503030108071d 81
    0x2010b551447c240a100c2c140d840324206d800c44e04511400051920100341382010041c00310091003141e50496654034007400c04c0203402c2c201d100a110003080f1841c00390f8104018140b600286c0500c40c0078010b052401c10840d00c48504101404a080340c034940510092800c00140f05580f000103001507808020515502c1d40c080c0d642d209a000f08420311803681c0b042e4201c03031f03c66040414120760121007500040360095020742100d5040d01d04034070072002030b9000700003031006d01c040d600c01c0e18a010380e00c01034200503070307040d9401440603024513010300081000300f0700280103010b01d20030180700303c4015590303295905400246406541180c0080d0b410b000040060180000580e4190b4801c038446655507801c2c482c0c1c070f40035414100003080480000b44440d210482d0031800c00d074210707081240540311076696031702c0d00d641d003003206102d0074086001146015a8540f00744d115101400c001d00440780085290f4890610719042648041207550126000788501c500e00345564a44103e820900c2c60382c0d007023212403039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 55317080 1250 55315830 55315861
    0x20309070306052701060602010612050703030c0201120914060606070308041b150203250b0a0f0e01090f050f010c0f0f0e060c0a020f06160f0804170303010303080f 72
    0xc2c040729100c101090050303804006000721600e1010ba14070040c0240811180600083c3c8186c83c00765280020020f15442c903001814955035000c2c01521303109055950a8800c2da0411905a0400c248054903101d850f6240c802c45800301c0c050840c0319540e0751000c0c0007074902100181100e00400c1d0a01140c000242c120640790703006035009061200c0c00c0e10556100e048450300e03500061038100703446645464140c0102c002c0c82c50001241d201a810034003160360707601000b01002c1c000c243d003180c1130010309644455030010349940000e070710110700b8500e01e802841c00c0d42e107260819a00102140106400c20100f04042c0340703003c85d001c00900099524000160040d50000180c5092150381040b0340f45a0f8824982c8a1004d04010041e40c4c1300c9070140c00d11a501c841c000c2e0301300e00a43d4854440d51642c58101c0940b0740244100e45588946101942d50001c1d100340480200c0d00220f0a210100b51040800350341020758a0a400941d101e40c91410024844400070b1301c0c07812004085c500f0710591804a00c481d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 55318330 1250 55317080 55317083
    0x120506010b1603030506060f030123040614040203070905060d020912010608060112050a0b04080301030b100f05060c0a020405010e2d0403260106090609050109080c0108091203280203090703 83
    0x2620b91b07a4800804c48900c5021800e004040c0000000b1804860340c0301e42c903201c0200032a0360f5041c0c8909000f884101c07605401245c40f244a60030b03040d14140b4058000307503440315451030b0002200e075540c0c011030f045800103400030440d00d4012420b510f49040400d103c000c9002c5960003440100e2401d800552581c006015000e00c0490080d11541444070800c090380e0342c00e500c041d54045914042c01c107051a82c100b030008039543e0490b030000c40c02c603854150541c401c1e10800c4440c6030085240008122107a880031014082c1400390401800160792031740b080070300815000c4110350492510380c40990000c507071072505a50102e406907d059055043d814490380c402d41c10706040151060080508500398459000000c14080840000c141c0c036500400c0b41f0120344181d2508100145c44400560741d00e40f039401000c680350312000700300000f58070441e81c99070440764000c00d80d00c024510718100600b69100b00c6040403d84044000c00e000d00504d01c3c0c84284000000c0003c50031420301090403074480d4141c3c0310 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 55319580 1250 55318330 55318337
    0x8010c1b11100513080604060506041401051003060e090a0309050118030308060a03020913020111010c170c0c06040323090d0f02150703030b0a06021606080903090a120506010b1603 79
    0x14480070038021021215400185002640d130786a40743c038100d1396204101c40c100c60303003030610b0040382440c2018003480e07807292b1010030902d14503030914040c4010501c10540300001c0581b00c040c00030310b8041150250307028001c004040d010504035400d020340b0701d0400d50320141c1008503500b1405540005100c2020580e645841c22507140d85402e8006200d80c00e1540010754000c8081003230102e91a05255007041c3c040c1f003030302c1c1d0000c6002954907603400c840c0080d45d41e5002c90289080703980d012031641c504990003c20544058205100109950703d40b103001c580441c041003c1c0c14512480350940d00210000c0920320310b1061402032041c000c0b4080c1460700074000c094040303000c5804115a2500c2c0c0c01d2421846507140241c0300c01a500380140900901c960060003041d0821000c5032251012a201d8a40309811040100ca00d1030124101d40c8243c0c02400350401e800180480e101541c0c850241100411800b45182070114560038841d06040c0d06900000b00c0c44005c0040300810100f220250746200d81604 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 55320830 1250 55319580 55319599
    0x6030c1d0a022218051005030a0f06150803031e06010f0e0f1309020a090203040b040b13080d0f0e0604030e01030e0115080312010e040201050702100c0b0108010c1b11 73
    0x111070fa14000c1c0b600c2407014540c1001d900424030782c0340b185100a20012011042c030a43c0c07141c02c02d00020078000e0044c5601a040181c13008042401011800300780303841460001020b003140d82c0c052a1458031600803c445400c000140302090050b030794000a40e25078403130343d0710306410003034000382048490f80c100c203060004000355403503e503540b41c40502c8203103406400c00a0300858544408010b0100060403445600d200101141d4034105109503031045511a0040b0080d44940d00c401140381002003c41d8202240d12144000103a40c0340c1c058540d1605c204008a00307400b42107054015503480144082599116500300001b182c0e1189034800d8050080c240003c2800c00d11940901601e107101c036440700d98280c00710018aa120010080c00c480c044c100d50074455989901c00c20340609001c0e030300680020400c0c40410094540b840c8050f40d824200d0500c0d0080084540d9003c0300f11b40f0992081c640d59664104000c402904144c0603900f403420044aa46560499550140164014220140a088501c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 55322080 1250 55320830 55320847
    0x100c021c02010f0c090929060c0a080403030c060605031f020307030608010218030d02070e010b1303021f030506030706090918080403060b01030b04020405060909061507050106030c1d0a02 82
    0xe501c80c901c400c3d8280d809105a01040c98040d041501030310865441c0c620307118020a46064100303003d070300052404070540b8030005181c2000925040807020204a0240c040e4a50006088c60014001035101c0d40341c1d05881416403d01c00112441c0764041402038010f031000c0d410079104c030b200418405110480040e282c1c2c84111044005043d5904040c0d450740c0300003140001d10120b440003040b240c2044046034041c042c041800c82c1c69840c00e01c240c3d2403200700d110062100b13a8180700507040040035045021007060796600000c2c440150400503144d01ca2140840d04c1286605001c0e180d4404001c1d0b0003040000c2c0741960080c20b070042441218405940d442d405407108446980d14038840b42c01114481c1c85a4890a04400810600364802e010915190019030607040900a50741102e00003000103040910305c40034800850f500070040b81c0c1c80030f2013800110100d1131440c05044003034003c5000040c82419850002c501581e65045041c007940e00809002c0340d1500704100992200d142d42c0c01681310f1707640 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 55323330 1250 55322080 55322083
    0x70c0b04140a050438040603050a0c09020405010518010c06050a02120601020102031303030906060803070311070f030206040e060411030c0d05011e061407050a060f0b011805011409040c03090302100c021c02 90
    0x1c94445c0350b0250500c00004184400003072800074490003a0180381880e5a40c0150354224801c80c8600c44c0829800e21800c80004c170014041100000306040555100c000c6a80748800c40390102d601e0341c0034aa000ca08017800c59060582c1c0c9a00410a000071851420018228400c145491000904140d02e401d60f8104200721604001c00070180303a81242d413500310601c0c010708501c03c03a40c1c0019840c031908800080b10010510341e40101c0b60003509103403600307060424007105000d00030300321031700030361510708403001d0103060b034001d500c07407150407500b00d03180e0801003c40c1301560010383c440d860024003003220000324001c80c00c01504032051801c000c0380b2402c1c1c1a26035142c500400b00060403901500c004202840003c6e00041003140c0c0e82c030f1082081c6001d10006503000d200e810007040000740e5003a814412035004d000200200d0070424103441c140b016180c000390a9540e000c2007900060b444101544c2010b80401c41c0807140c2d10000c605100c0c108851000a6903184074002d1910183d107031030b91001d03e1500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 55324580 1250 55323330 55323431
    0x200a20030102040f08010c080901090209070c060b090103060209030106060320070507080115050a120c06120b03010f021305120a0209040f06020309010509100c050f070c0b04140a0504 80
    0x7141c00d0281c60490b80d031303483c0130300a20303003447c03c41c010691071000210561018820640c1c0c09a00600d076250644400d9011950780751944022204550385035a10030090b84d0b0100d44500070b40c031880000d82d171900c03050249800d40b038490b4000000c2c1814107c1e8041e400701040d452a41308400302c004039440305018281180342c0842036000034419480c082c0d0b07005080a401e500042614030a0358003d01d0f06a850f42050394030042c040300684030300411030003480260304c2160b2000461401076000300e5011a000002070031a40c07070401c1e850788150300207041e1607142210070f4040e0041500319182000c1030381d8450010380b12030001600030700c518030302e4001600b04240c0503c882c0c211908448219101e03c3c24200c540e00820701501c0289113803260080c0c019400486000d00d0700320400e03590304c00d82081016090001030790004079040b5000240d5406c007080c0280081301800051400c1e42c0c3e42162656680c0a06c451240305030001d502682c10300f0070ba524513010b01ca60100803084200090720070005440403030a003030381 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 55325830 1250 55324580 55324589
    0x1090e01200c1606030204030204050105060720030705120709050708010501090b07050a06020d05040308060f0607061802030d0f0e060a1b0c0503010c02030a030b0402030f01051203040e0106200a2003010204 90
    0x8501d0004500d1301c0c0d140d4060000c0e85d100b500c08106a1b42c89800304079181c02164402030200c112030344001941070500c941c502e0a440080c2c200d8a40342c0d100c0e400290102402ca00c415600d5004110400801c000f41c0139040c0c2091060500d0915035041c0703c002081980140600d86603200f00003584400c0210801440e483c3e19000203045413941904040200503080a07541a0001054680880e1041c81c01c1105d071202910020482842c1600c590303540005000403000c0c0350380c0c1c078803040b0003200562001c2c41096080029035603031404440244001400415020010303a00610091004d82e5090760002501d07070041c00401e0750600001c0300e900c1c0455a400c000c1d0441a05542020303203110440e50004060000810701ea1820300c85c8840c1d010a2200700c1c0011a0300c08443c031400801000f060520440810815100034107a9240c2911035040402d000020303802540001c0f02079440256480a00e1601500e0302c501101510100d8810b84440f640d07049032668010802000302484810b9a6003541240c0090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 55327080 1250 55325830 55325863
    0x60309100c09031505070509040905070302030604210e060a0e12100221060f010c050f03070308010e07020307230c0a0909031106091510030f0b01090e01200c 69
    0x90314801c004240e039585100403103800c040c000041c02108502c0c01501d1140c0d00a0740c4440c204aa10410800582500d440c156101d0150110210158a007405158402c50081510950111041000386016464404c80704c04200b04030740a224642e40702000c031b8a14207600d18108109070039040000d0b6034422284004041846027000781501c0303c1054029052020070644e140000c80400e04c00c1e03014030003040b10041e03440070710743da00302033b00e9070140b043d4240507801007040314144101400890328580c00900f06034003180030540108110050125480d03030000691014606004499566003e80703c1041181c0c000710aa400b000a030080b01000000d140b10300090403070704d10540d100d0112002382042d402c180c000070050a501c0702c00450004965010b0ba031000d00819001801300c3c07030350400e101c0241c540e01e41418280c0000020a2a41006008070f9015059850195241c01e48035422102c001c80046902c0e41000c054204000c0060f07111440c590380c1c1c0106aa4808075500c0b9103081240c50302c25012071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 55328330 1250 55327080 55327091
    0xc0c040b0a050d1b0602070506040b0f1303050303060f0d02030c041a031509010b040903050316031401060509040e0d0207060503040f0605010b031005060f0301090b131a041a010e06030910 82
    0x24440c0960703203510115441441c04d0070f42500e170341e82283c807101c1c030f0702031550800030400040201705809401048003010300e0305140e08060500761340741c02c1200b066205a400350700c04410b00c412454804840594030404884005800f9401d0b030100e5120881c0090440c4034964a28a410401c0341d1280340310503442005056844030601d10351104903100301038840c12851340c64204022032a050612484228503003603100d450841d43e60984020422440c119010200f603154490042c4a100d4210348502810250b1034054903a0610018001221901001454654000c0c1130391070b02580c002c20008292029440c0c1541d82ea500c6d824007200c0f90807140c80080c155450003000103032442c0d580000d140a5030200100c40070f2140d03240d08202c02ca00031824090060394080004104100300303580b00c015611405000058402c1e06004100201c90484544200f590070007200505140780601c500e1459603945543d455610600d003000074103204240803c0d602603000000403400c810300c10000070150088400c404d03c44c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 55329580 1250 55328330 55328333
    0x307020106061119080f090d0c09050f0114040903030e0d03060302011116091a03061501030605090c030106080705040305010c020d03050a14040210050d09200102030c0c040b0a050d 79
    0x307000611410300000c0ea60001c1d1000440042500840c410b00140e100c05000c540341c6410000741d0200602920041040045039225128200319070061401400000503c510f45500c0c40141c40008085480407000000148600e001200258007030070800d0f240054416034030314040d402801c01e00441c240512580c0c2458254643c1500b181041e24400c0c2d9443c4d815011410800b56100001260b591047e00840303030500c03035000260300566284201c00786240080c0f82100220b0b040a4081d0b490b10300c00030207900c401a540d60140030720002050291059415031800001d96105404103002d1a020400d41c0d0021542041c4104141c030051600311000f004010400b44000c1e50b209440c0032a0320100e800d0000040c12294244140c1180440c10340d0301c240300c0c0d40c813036080101d058600641103040c880d090241e6400001d20b4824020010320800c10602a41401d80c511a42c82c4000280641150700c20003040c1c00e010300200722030031054000d40303001c1031900d41c4034005030740046607410031900228401d6040c1e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 55330830 1250 55329580 55329583
    0x51b04021309060303020f2407120e072309040206030a0b03071401030c080103050c13110d06080106090c0c0b040203071208030402010305090609030403151b021c0201020a0c0809010311030702 84
    0xb007100e01c2502202e01804100d0220b0b9200d502e0380c4408030200e510350002140d4074100810460b4481c000780f40100340340c0140300c00070b8115400144034bc48198803088091106080d081614100601c00305104010700c521440000e031403050041000f4046c160220208074600703401c0e048800340c044010b09690b469625a59411401501c40440d0383c00641020071a64042d40511590f6060b2900034020f4400c8402d030106000b42d90580f103401a8080c1d65a440011001c1140806000c905002c1078021600c246000091407e4031026040030038a41e04d0001c0107101150003450307401d0f4a903072022043c01c079950350f400001d00340380b595801a149000c0e0b0300e004100f00030048000350700c00d9100340c0741000301e91501000b20342e40b110300311403010b8076520810051002c1815203024554820a00d480407030304041c40c3c4207980748525044603030800b503400510031180190a0b80c504aa00e80c1c00c40c03000310305002c91031400920804206da0007400207003000070380034400d034402c0e0070103085048818115980d07420982c1009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 55332080 1250 55330830 55330841
    0x912060f06060322020f04020a0201090b1807061808010212040317061c050307050f060108210901030c0c05070e1b0405060f090d0b07080f070507051b04021309 70
    0x14124001440001e0002d20b403000c240c80c0500d10203142010340756102c1c4041d412603003d1032005d0342d1055140c04030b906245d98500041c034400496500100d80c485162900003e44940945a482a9081c1d5151413144500004514084400910b0011000000c81c86520341d684d4441d0040212540006100b103001c04001355040d001d02e10030f0313031080d001c160541e900700000d000683d00950f2004404040304400b20a0000540d0000e00882c2a04e107804000c3c1d4850b4900001101401c4198218400410030240240681c20501d13a1000024065428180d07035045c41d4800d9501c42810f02d90ba840c42e84450038400c01a54400c4c650280449080c07075101c02c05910b441034100c5d0b04005961100007483d81860580e01603804071840a4443d178148200d1101c2c0d0291038111000031034100080e28001408125050700103805002c498880d62480e0405c04401034600b41d0041140041c880100444400540001903c0007003501c0742e0030080341080c041000801030320070114418076610700900041541481d5a122 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 55333330 1250 55332080 55332091
    0x5041b060f0f050a271d01030201020d08090d052b050603010c0f02030f03221a06100c0b040602090a0803090901080106120b06031009030f02010b01020729091206 71
    0x140b4402e9010550200c685100d104c3c258400502400100e00c1e11500b0a5800070220031081407005aa030340f106041010400944152150070743c065004109550b01031101c1075840c4e000d0314150f1020300c1e000f41c2c941d40d17403419070300c5100800c24009031084034140ea101ca80200381d00d40310560004c02c0100300200703000d010240d4415200b946032901c2e00800034004d001924401000380c005e5814204480440c003d944c000800617a03912131002803c620f41c20004c0f04000301c1d60310454644d03400b0b8890b00c407030302203401c0020322860003004643e8540d0ba1482d000032100307002da07920111903100c5695a2030701c400070380515940560400c00c0040c021489001c04006001042410b8034003449681c0d03680350150076511640301d040700f000307910a01940031520220007181c0c8080081c048900f841114011081201c50b588802c1c4d000600c1410034803c0740f43d0a004894200100348000c0c4805810101602481d207201e905001c407420f00e80804000ca44400001c1e21720841c4010089051241d90b0074440b0703260b640c02c482 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 55334580 1250 55333330 55333337
    0x30206070b04051c022d19140d0903030e032e09061104090e0c1f05070c0f14030a051b030708030c0f070b042303010209090405010b01030c0302070b06010305041b060f 73
    0x250501100c8003031b50a60920f261003801041d030700500c0002c14461544c0c0031410340c0d00c0307804002d03003d01807102007001541a22681e9124141c0300d1550600900010401000742e00c039030000200d441e0141075006c04091080600e0b06000e5047d44080c501400a04809a0041c05d030340c282000841b40b101c800c0003400494504a00a0000341d0043c12180d4944a03a4000203610044c0c07184c0030023034488203144900c00c14070390703060075483c0c844140c40b8450f0b03403480d40d80f1205d8100d203881014450b9410840580303203800d1094004200030314055855649881111050380394000904512894654040001c44003c02480055950b185034010080e81c464000009070b10302032044030700010322340018801b200c00301c9031800195014131000c000c40c62800c4010051403641590207010311141c0d41d840c2400c0c5401503100e00000190303c001e2000241c141e840b0010703145c0c245841401090040748010510652003007013480d0006e043d54591824042c2001d00e80340e9140d0143e07061101041c601c0d081408a041401c0a88 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 55335830 1250 55334580 55334623
    0x509030d0503040b1b040906080102070201030e1c0503060d02040912080601090608010501050f27010807030b0901031b120303020c0c1518030106080f031e0301030206070b04051c02 79
    0x1a0a9400d4841682e0050482c1c42c000c0000c0c071711044840151910303805a4100c0b500d03240e0368980140544020360005105650f00151080840d0780510400448844a0010740310803183e0401c90240040340900301740a2100010006081d90b44452110191550040003003004050038201042010306404203040884c2503a404105c80c2d6014100c80402c231a81c0d69100b00541c0e00b048011122900000c15500c0d910900344071142902c11407081030340e20300643c8046403566800c00b50004102c1d040280a07402132614102c1581840d840e0030140e00e0549800108240303a031501c0d59511a841180c2d0361101c0c1c10005d0185001d02050380c103070020034080d40120300300c84489a00404104c078504c1d41807507956101004018410514641c203141c2c4000c1b1740010f000090096581d10030500b00081510003051642002801e480e14901c1c070011507609469000440381158113650101b0070501c60f101010b0059660200090b0401908203d904006441d07a400040c1341e460080c0d010350349030402c0c070311103c1e8900c154 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 55337080 1250 55335830 55335853
    0x2031909030204152301091703070210080c0a0318231507080406090c0b040f090e0102070f14010b06120103140d1b031206080313080309060730050903 66
    0x90034135030240da88001104902c1d068012410300c103200782c4c14019060012410300094030034411046160210380c200080e540d20286841040190003241203000c0034010584140f00d02d50b1014000c0d50308048032800c0020312601c1c59444000003184200700240b982d42c00040720b10040120712a8680c80c54100c0301211305120b05201a203c4114003159103d00040f01000040c2c0400c180c3d40102d501c1a0140d22741011040e11100b0301ea200c0e42c007503002004520050b183c03c109038030313251181c1c41e295030b10308008500b40b4802e42e8801c041a4056070026009408410740c51b40d0a00c000e601000d1983d00081c1140d40d2654502c1c8000391940d4244000d90705c00c03440d00b10b0003a4441c80864045c0e208041913581c4403060307407180d2142980d41c0d0341c01400e404100d052805a0440001c500c03903100078000140c0116124183c00d0b00041340c880454008802d181c01c1400001d00355103503031090341d0120381c0c40201e0300c0703052a07080100b20214100e242c00c504280788010b40c0310015a042001031903030750415019182ea484c2c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 55338330 1250 55337080 55337111
    0x6011b0c0f0f08150f1e070302180102062a1605070302040c030203101a040302030105040515070912060b060c030d05040605060103060302060f0f12010e15090408030a0c02031909030204 81
    0x1c4030500250496003800080009801c603201a501c06c00b8003d02e20030400c0781d00c45c40946050100d902801090340015442c800469210000319041400d2008001500c0c00120019070a0030100c4204d5402c0418104c07459600401000e640b4204200a01804880343e01d00f45250340da8607520050f8011441c00e15244882e41c402c2c001c81e446581d54001218620346400710302a0500115200c6041c1401e046c00b002c40161707001e000d03690055000fa0020300d0342414808074400020030161030b10051009101c001c000c00310320f85013440b01041d00704400094010003000821020b00c10694070845c6408002a42e000450803680010700139400f03075078100020760303480d80150b048621a01010b913002c9014410305070401624030041681420880d861801c05031404a850342000c020781062529043d040c04106c00e01c000c000d4620248401228a0b09040c01c09496420342e03444087c15100071070340ca44201d02082e500810407205807801c2d03c01805940b0030160401450302000d80402c030b2080d8180507450202098 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 55339580 1250 55338330 55338343
    0xb040207050a05030a180e060d02060904020d050609090f150702070f0801050a20070b09070e2505071101030e0a080309030901080105030109020102070e0403030b0a09090b180606011b0c0f0f08 84
    0x102181205d0894588d6010002e00b292101012039200d50204010581d503152070025201182c3d007841d0116103818180104694004020700d807450310f41c00300e43d10741c24040c0005004000303030080e4130219606868640080741410b005801c09a18111541400a00d901c01540414884c0e604448108440f203132110700e2106040003211820b6a1399018041c0304046480d0045047e0031034040400c40c1c2c1015520650303c0e816000468020929142c030010890744980340568100b58101c0c2d62500ca1b203410140d5a0700f02e1004007118806040507551000c4410200d410012013015a030444440ba45901e00101c01540e00c0d4048500c16000800840c000100fa0070140190400706c1e5050b00030b8000b803400d044040000b90f40c020402c0c0c0800d511000b40c0081fa84680030b030f000252404030b00124a100d598206000301440290402c0c000071000e80c250782c0450804103400342c00038001d1800303a003182004007016607001c0000c840901602e03014000080e80c201000e2841c42213a550341d001842c07842c2c1d95182d0b50744505 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 55340830 1250 55339580 55339589
    0x10050102060a0c0306080f030a02071202060f1614010606020111190f0203040f030c060801122102030c06100e0108030a05040b0f190c0201031d0703060b040207050a05030a18 76
    0x1e005001041c0107498030342106080360780f80d01e400103005984800c4145400c4128041d40c0c016000000c105144580c1402404050611101c581140c412030f50301180540c03003041145040300c4030101324000821a0010b0350288141c0050310071204000780510103000b0007403441004059031a22003d81500b40c07022080d03803402c10401102c2d05a6a5981d0350945801e1981c400038011800100804501003411396428400b65025072240301a00c0c0c107000c0081c18503a0306030850b00100051010707000c0054107071620000d0b465001c060903054003000d658260707c0d50007485100d0440e0b0042d80100090130344482d803c002100c4000d114101166a80d0103402d450780b00310314043c00015002c001c00c2c42428803074401800605a210043c0e440c0032030301c00c0515954080c0741c03501400102407462280656a041c01081c0060f14001914501009507225141d074640c11403100600381030700c0c8c2e401c0c1001e070b0b40c640c1c0c1602c0c080fa8000040c0c60707940d5850f00c2c2450f1a580002841e602050181c14023520310300600b43e017041a00c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 55342080 1250 55340830 55340833
    0x1e1c080408090a0506030a050906010b180112060f0803120606030907090b1807030e010c030c0e0d0f0209070507061104060e0f040906020d09020a0b130605070609050102030c03070810050102 83
    0xa031640d0311038806a6004030261600001c80707480028858403a00300840c4126a48613000032941441110700d8108081a440508003c4090260180c500303d0700f107003480c8c80c040900f05070840c85503511012000d400766900c412890521f1010020300e450000c8018000c003c0d4141c4100b14603a00c0008101940c0401d403154505680000001c4c40040c009910034094030800400c400c11244144c2c0c50814041c804603800780000c1e8440d1689100c8031800d0207007110030f5540e82414000914601802800010380460340342c4120381c0c0001c0001404490400d404040d40c001c0c1040031a86450f05001d0000c0e844440112409803415680400c0c2e288203006440542c1d106544041c402c0074185c1c10407441602203440141d00540d210700d100000341d2240f005001d085581c040c0410118550f00400040d060141e00c05042e14004000d81c00075292842c540e08103441c400e0900a485e410103052030b00040c0300580c030041c0298400814001100380c1500914400c1c415a618040340b991404448050120144201e5015 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 55343330 1250 55342080 55342097
    0x20403110a1d04030e040911010206090c0108150109030507080d080a050c070b0618090f0d0201020c0c010305041e03051305030a020d060c051e030618090c04021b1e1c 73
    0xa03211a509094000d4007071700c1d0030200c1614043c0050b044404040007241e0140040c10846040c0d601400955809807050001c1c0055580c2d0700b0021341400c000420762418140e0107072401f00140c1c010822040910b0304502202d2105460b86191039543c800600540702145800300061903281d1180a00ca106030b1191504600707059140d625050352220150166134424070400350b800540c0002100e00348541d070480008c002c41056282585e060450f00855102103900400240c12944130000380140e03080c03005c3c1780002d09940c45013400c1c006403c1890401d920714000d145030340d09042e13020018100340c02c110704500345900d968804155859004941c0207400003010720303188002c0741c090b51000041c00c03501c0c10720902d80100c410401100e00c5031440c500c1200d00700030040c4051410030070054174401c0d0080b494500d41e4200280c69568512410440c2403055400190036000c01e900606a280300c00f0708102121910803458454103089000c04100d9009442442c0d020f00c0c000b80e06050b101b114034881c1e142c600e003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 55344580 1250 55343330 55343369
    0x3080f10031b031415070e01090e0405030c030f090301110909070c080c1608010e010209031c02070b0a0e01140a050a080c09060f0d0c090303090e0714030109020403110a 74
    0x440035040140480c4030410380002020034803280781c0c44c110f44a0100a092034400c552040c41c1210b002400c0c403020458021604142660000c1142d020f540882c080618036540343d01e8400d255200b802d208000500000c50f440100088940c003074035401038110001d00001c0400d900d4402140203a25081e548108000041a18135014a0140c2d01c60750090046a240c4160100f00b1032824403480b0030480e0600e4000401c0101045c207116020410030f90070001e6140c445040d000a546030958541c52003651541180c03081814005c1184d0360040584041194136a0348280e400341c281c0303514015450100303070310305c2e240441418800308072020b0400c00d86495060100c40e0300c08581000c3c0003009d088134450204141071640d6240000381819070004694940d90b6001442c42005441244000d8410b0219010042c80083c0d0060081015582c5212030300059584d14601110480348054041e445600000004038081040350024000d60303019610702c0d00340c1d640d072006111400003184606000c0340a03d100040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 55345830 1250 55344580 55344593
    0xa0b040b0709051903051b061e090a03111011060112020411030a15170307060c0309020409210503010f150c061103010e1302030606040507020a0803010b03010303080f1003 75
    0x41e00050180340c071001c0c441d15140441d9200103100180d030500c14840c8010810020200400c944110090b0700040140c180e03030010920380d016807a076000301c019a640c3c0c1a04102c030424150303051040b0040540803080e0740d0b4140f9041103201f405d034403406000700c2840d20000070b000744400301803020007100800440c0e00e07000100a004c140310b502280c4c0942c03140b01c0000004030740c10145000709512800041c200d101c1247d06590031007241d000507918074440300049001ca00c08000e0343c1701c03190041e1020403401740c8808210700a01c0000002580f10f480c004100003030208030300074626990b90744000000301380c4002009542a0009100d8024028054001803040403814800860000c0945c18200b00140042e03662105451412030070310b00c0321601000402c00092441c1147d030f000b4540c0b041036500220303e43c01090326504000d0100707002d0f90f00c4e0310200300024800c1000841072034100d031b40d981d103c1d612412a160268020302c001d90028011102040752820b130b00070950f00400c81a08608281c924555424 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 55347080 1250 55345830 55345853
    0x408070c05040507090312020c0607060b010207050111070b1b011d0f070f12020301110d09020109060c050c0d1b060305090d08060901030b0a0209060c010b190b071502160305030f010501020a0b04 85
    0x78110b00400c0327484e002c2910b441c005405214880c590208048691000091510440f07030310050401c00010300d00c4104c64008121202074800320640c1d01c0d6142c0600d8415516a6980e880306451986800744540c25141c010500154080ca4101520b10301078240203a2540d4030024000e0758260301c08640100a00004602c0c0041c1051024002241003162502c40181a03007220304c101042a8803048800110340c0d10510080c01703041e542c10035240500e803a4032440c4c4d6420000640324011495181003070244014017074a048044809611585d0315510350341c00501928054032103e0711803041045942989025020461003040d000e0450301c2181c0c615100e0360064031010302a290810380c2006220740c1d60310340000030a030740c0c100e6200204000201c802848944951030014604c82a450318041c4412602042210041900201218894012440c00e82c000380309a0702c5050094100c4841a03041580000c003540c85442404001f200c1a82c1e12001680c481c42d190400070119800040013600140c90354220 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 55348330 1250 55347080 55347113
    0x6040b100c021c120906050f0a05070302100c030204090501080a2117070903140c0307090b01030e070f0f1410050a030e060f09010b01020a150b06120408070c050405070903 75
    0x60f503a481c40142c07000003907030400b580c080c1c4c0c484142c00d04e002072643d0001041070003080c8a1919074900b002c41c5804011034040d040b424420082d00040f040f0506208100b2515190490a800c10500c43e00034001740c002c1d03005225501d00281000c00008003d080419038040041e008580c060000484d031141030400381690203420140084011410b08442c511b048440c454400d41d1102c920050942c03c00402c800d125841540840d44080c400c0d4040c1c0c0c03404621a01181d02d00d4001040341c0b07010382e005030301420360340003007102502c2962000603a1000c040032010480d0100780540c070900d51500b88038008100c0c00c0d02c403540c01040d100703404080c41d442840145a01c0d2914500010410019500786060140c16505600101e1742d0000b40000c11070284101000c075507007400104890348a559030810a4840b500c040c841d91650b415289142e900c0d130743d00315000441e070b40e8940f030190315092604441c00c2e0008042903401d141c0030341002c80c070b41c1041d02c241400313503581d900c1d5002c040c1c0c0396940b68100c044080c2507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 55349580 1250 55348330 55348339
    0xa060b06070b0703060e06030c031b040207060e161203050a18030204020a020f0708010b010905060a0201060b030c0a030501061407021504091a0312041d0c09060703080601020606040b100c02 83
    0x2202010a0b000720340c0038003070800c40d580030503c01d14011513009052400b50402e0303c00d410042c1200749540d00003414422440300e040c108103580d642c5e5400a8000c2c0510308011342000c2c00c01038442c00c4618042100315000038403c064504541e00e0700b080b20030078005200020041803003004000892800390f03900d030111024000314000b6094580d07001c5070681e0024000803016904c20001d040c110790080c009180a0824007000301300c1d140108000030448070142c440c40c0e00800001401e407000503c02e40008001d04905000e9039624104518401d0251b0b01515407a800285442c00202e0b07100c0c031446d082004144143c104a0a03e9016000c20465814040ca0220340d04405c000002d0006954000c010103451146100d00d0b038403450b5420f1504041d1680c648494501d030400c000c1c0314902c0d0242120104035140003811204e0f41d10b080707082c5150f1140009107070340024041180010142e00c407600d284940000c1c0d0a0307500d1901c0d0139041c04190364803c00003950140030101c80e8070741144206001d0004900040c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 55350830 1250 55349580 55349587
    0xb0a0302060708090108090105070210050402040b04060f030605090313090e0a1b0911030609040f030207270e07060e0d0201020a0b010305030702101403070806030307020901090218040e0a060b06 85
    0x280041c889038044101140d80c284040f425000642e0010813540c0c0c4110001c00900803490990380094460700c0380014809020381e00e030082020f42d203c2c3e900c0810840ea01400400c0b20383d84845881c02007071034034801210501d003481c00080070040003200307a8000c005e003034503102a9642803c815a015103044a038000c52032007100080b6022540405c0c00c28a8516112080400e4505000c0d0b001c0680c0c50301b0070900b05260b020420721000392191400c41d903200e0f40046844041084500c3c040382001d1403a840074025070310051501680d520890010002404000d50030803042002c0c0d0002504c0d803c1c140321711004981400c940c5032250030441c0c801200682b0504c15076241840381e5503042d015040a0300305a88075440421000f04600380a0000305413804181008850307000325042040f041d2000030414410041001b012900c191010429502e4140c0d000342640030b25a100c105240094105448400c0c206040c000d80b12000d080c40d10420350b0506814010781120f007240c2d04c5403c0902042c0d18000d40204081 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 55352080 1250 55350830 55350833
    0x6031e0807120f1404050d060b060c030c03030a050108010e0a02011d060d020408060702030f03130303090b0405060403020d05040b03010e0606040f1d060a0b0a030504020f19031203110301090b0a03 86
    0x941141100e00540c0310f8600362100100c00030700341c0d20003500c0004000401c21091103240c0d0382241a940042e44100d01052610200d004039405004a007654191b503c0042680e540003040800954852070001c0400c020f940ea0799408a4240c030900e4002180c0c40e0010010400994401e04141c030802c45403410301040d1082e40c00c04111315522031040580c00d6a4003007814800c40c03a040c410540c1200e8548005d41c1046800703001440580b2001d000d5008400027041c510041500940100301c074a504546044c0c80e92919042c450345815080310f048005014030310390810078502410a4606031000d2580041c00c5a00f0f0045010b00c81801030102684035800303220000f001c0d0b40d803115803400f6042c5081101061014210803480804010b03146034800c0c4068003003400152580c00c1540c0d260040c51030003268644403400400c3c0100b07040c000c84c9400c055507003d64140034104112040489100c0d0102d161007c1e502c1c0c81c22011103070985811400c0c00c0d8204010040010326403c01d02c5500340c01802d81400c195207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 55353330 1250 55352080 55352093
    0x10e010305060f150423010207181503110a050901080d05030402040603020d030903060b040902150723070617060a0e092406120c0f040c110105010b071506031e0807 72
    0x31400813500581001909124400c0ba4590411202864001402c1c5113148140082c0d2506000e0040c4001d41c040c4000507800c25825400c034881031030381c3d1010310704541e03120305002c0c0b4501c03228a40a8002c176840180000e00381040c114050407140b071f41c3c0207440000c07801e150444180d440508107a9005840c0e50010002d80e031141801003020b0320940340c0c80c0041c0c1c6189400b5080d544c400518a2055260984a50142c0c449000c5050010260040d26a450f1514940342d14071400050b110390180c180d504d202d1544120010709001a82d0107030303e40d0810a2008007000524400c100d071400e4020410784001c000d00c0885044064001c00ca2505507540c583c0414140448100c452000c2e03a0b45c1c174200818007203181810202700e02402d4458000d4101c8401a001142940600c4015180159503401d001c641091150b40550001180800244078951351104038202d280c00912050313a01f5000341c40c09a031440c40910500040300e0380031f40802c1040b805a0001c1b030072514008000c3c1e444550801007a2700142c1c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 55354580 1250 55353330 55353349
    0x91805030a0f1704080a050705010e060a06050316050d08030601170c09040b1807080604020906190201060e011409040f050a140609030c070504020c0a0b0a0504110f010e010305060f 79
    0x20599400b255440700b8a0014a0b4002c001d2000c1070a0483d801400702044456048810012103414060b9a401c1c0500d081401850341c2002c105c0c840c0111018814a1390340794122008030740c0100c0807030740301400c50806076000040c42c3c801c017944074040b114071000056090029503400001418110000b21000c0d800780d81030070040f140160021000125071156180504c642c28120805607111030f00c454040d000c4854070680944100706000092000803525900c6804070741807084050240e43d06c980c080c0382681c00602054400c4009035090850201d04074051a07000b504a80c1103000c1c010100043c00280480014058425900c8101a069040105400300041e0012600c03038040a03e00315030852807907082c03020152103449503400404c8035500801c00001c40005484044600682da03480c11030b6068030300241d100f0000c10080000c4100152010a580700300c0c4201c7c01800280c0405414001708001101d0318066540850100512440c0780d51113076001542c0047c001d44409012640c1e04000399000c031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 55355830 1250 55354580 55354597
    0x12060f031205040e0708011a03090c1e0d050f01050108010509031b010b090c030a0605041104060e030304090e0d09090603150f0e0102030907210f08070c090203010f0305010b0109080709180503 84
    0x6000c100100200541108d0350716000c0c0994220320f0070f5080090321103131076505803d1000d102c1e414a0a02d0b00c1260800c0c21000000c074002841c001900c641440e1154841160074255180c0b54038060000405440c18002c041c45074400801540c0b80141c503510301001c003413041500550341d41d40d8000e030201c243c403261010b90180c2d124104580d01ca1504144500940d100d64021070702036800c0610481c00a0091000e441c01d864075800c05543c0c803440507010914500541d4040c00300705040101c241020748012846c031003443c0659035000d1072542c56115000aa03a080d1000030b16411441c404080300d110154003400c5003401712240031449501c188421820f98106580c0c00f43d141d04401020403211404044112018280d00072200e2400229100c0c50204411401301801d40400028014200442d5500308005480b1025046450756100c400d1819801d00c0e50200715155803811100c48441e600404500303003100d541c60010038a5500b4610444081d02180318403004080c048682e002c0001c0c0140080c00041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 55357080 1250 55355830 55355837
    0x90a060306090c02070501081524030f072309030313060503150109050a0e040326061005180f0109050d08090108010b0a08010b070c05040c0c0312060f031205040e07 72
    0x110b06042c01081118407840503d8250b60002070100416600212004d03031110202c010811200081808541c0221041d083c281e005071540000350343c4026000051405001d000900c0c200c41d0b0b940c8a003c0da0410000034110f0380d105856104035a0380c043c2c43c0c005000c12200502641e04050400000c4003441c1344507049170340401c401004001580d0512a10400c0030346091a040241524150101d0844c604070302a28141d4540c610002d03090600560360b0300010001003008540c40e05006501c0c5e034a201099407200c0c45a110b40e81ca006400c4e105509407080201c102510b002010f040400b00039482107400c4070141808040c000c00100c90307440880380c15400780902c51040d941d440b540001001820140c000081502003845001d464aa0100c103480c11340d40e100340e2040d0390700c156041c101d14110080e4800c1d0b51182c00c044000a40743e80c01143d4802441c82916642d4074030210340c4504090f10b00c107000311400b45e44804010804504c08d50f001581803052810440d140039250b20458114000071031303c21020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 55358330 1250 55357080 55357091
    0x302060304050a060c03021e030403050f1902070611030d0e10060306050a05100f0312090b040b0702040e060603280b010e190b01050a08040507090f0e06090f0a120203090a0603 77
    0x1404014060a0002c034928075085280c80d8140030741da80d14030135011140c281d0341230100c0001d003090301074000c5854000102d171072640c0751405d90300520300c2a030b100b000520050280c584005901400340510301050603002c800365003440d46005450006090580c2030741e00d00d1050300c800300d8100c0d02610600000d103000b042c0c04a002e01d4101031b80c00a654014200c207601554014041240c095642c0c240e00c01d40e07a0010961003508801001202c00c065030340c10452a2036030014000a041709050001d00009200703803020302211044080031034a9810848403150150410725110b1902d600b0705a404620070010b10909904905a0721070030042c0400340c2120b40d8105800d07081c40818072040030748181030380000c2d10602142030001d000030a10b0003810b41d90000c0c05509400701781004410300810020304030380c480401102c200003070312502400060090300007900640c000316408090200368100d00d02c2d6004000c0c143e1507a5980c079070381c00014030340500c021800148031214032503030b4002d03983c0c0050680d581e02048 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 55359580 1250 55358330 55358333
    0x18100c0314040b1e040305011a130b0312070f05010e06091501060e010309020102030702090916050301020405060403080c070e1306050c0a1e0c020d0b040b0903160204150302060304050a 81
    0x340500301e220794403580410b0104100f58040201114103200400004107982801d0703035900c850354002d94000400d11b508145162417191024004010f040d401181c0d82c03031085405921410031118003035890358064000946c8440c0d0040e0540091500911901c4440c12210b429214682160b1032419426810b400030800e004045c4400c004190414440c0d8031000500c0d49044005000c410001c1d802906050300d9800d0102035a0080c01520240e94028024805501c0d048610070b40f14009803076000b410444040c40421107042c144255425100003918541c500b5095480744c80781a041191280340c948107001d80481c00d543c100300c9072801214540300c000b040310722a2074040180c0354000c1100f03000c1d0000f072081c54800d940c03106404024200345640d07000c0c01d1369042030845040c40284e1004e500300301842c000ca001c1104a55680344038901a515540d21519420512500c922800002548040d103220303400c2c01501e07141c0d0004070f11001c040c411403039445d41c07a4085106504103d60645807a04070390542c50 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 55360830 1250 55359580 55359587
    0x60203010f060516030e0604090e07051002010209030c040f110a0206010501030515030c13060b04060c050f010e0703060506030c090c030f060a0510030e120318100b0603060618100c03 80
    0x902401c0c450070f02900700314002c10003070f18007980441c000d0200616030800c840ca40e1901400c5501038440c1602c117000b8a10300803011a0345010a2240394000c0910b1034900c1c2c0c3d110b2047c420b0700c502e100010050f010a820010800001e00207100384944650365a4440c0e103c900c01100080c0400e28541d000381c00c02e036241400240444000500100740c170700403c407400205548c0412104440c1c50110ba23400b15a111a10b034100c0181055001050062000100414050b8014144403501c0b4804d00c1140d00d80000880d140d03007a00c03042d0001d480301d90300035241400007c03050340105070700c00e002600715a80c24905100107030208034241c81c41e4034602000400e001c2880803071081e0a500030010f0790140707180b80c50040410350030091644030300f04041c0e0700d0003500d41107001402008460810860641e0b00c80c1041c144041c20710b242030b151a0264407504501882001807401240200c4400802450441e62a0814058290321544922000c1b112400c261109030360794151188100681d03641d002c420f01420326010703 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 55362080 1250 55360830 55360859
    0x703030818010c1806080f061002250e180706111f05190504050c040f06080a0308071e0203040302010e040f09140c03070e07030b010c0f08070c0b0306010e0105130b0706020301 77
    0x41704001046007045982411900d01d1070308403c080c1c564012402e143c10003241046c0d01c4001022417039040e40003e160200146203032605440e68a0881e504a80b02d540c001b80340858100030300d0044ee08041e40400a86000d0b28044101c3c3c02d9a1080c0c580012184210704030f22602c107559115041c0d525400d000d50901c2a0310042e8040f11221410800c0e0304041e1581650b40240c0104a441192100701c40d0100018640050004200c4a0210365201e182458042d221110440b80400003e1421404000c1c00a041100044500c5a03402940c501410341c1c004484032400601728a4116850304800340742c140c2c1038400e41c8012030050840d0b44541804a04040c14040d180c040540302c0e40c0107041c00d102591502e1803003500030f82c0754100050801e91170401618482d50f400c001034000d1000b51000024007580e080100203051040c040c041c1e08a071117612260980c00251820790000d091100d0b4440e0703d501074402030400c0d482624580d10015540c20800c1d20542c000e25086540d95000301c010080745100d00e680 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 55363330 1250 55362080 55362089
    0x19081e0c0406030c0507031403070e090c0703020105090703030813080408060f01050f0301020c06061e0901140901090e03030a05040501020c100f0b090f0c0d110a021e06090703030818010c18 83
    0x17103860941140c6000f00301001559003034500882c0000890203050044038941c001c140c0107844200c4501e050000c90000ea000500706078050350070100000c504200c08100c2c0b07015254581c0391302c01c40e41c503030300014000b80790300307040c100c64000c000c100210320403000f040040d210744017864030000b2540c102024400e18224000b4914040e82c0180010300c2c40389404102c440d8004402d4660303070400b001542d10301802500c028003841d0000c58080c00800c0d06c0c4140060000c5800b402e40d00e8445a90360b40101d5411500310360449110741e002400810b040c00f90036040f01d034020f402000058181440b0120060a2840103141d000904e603807440070900a4810f4013580d032030020129801d90491901c683e15503c1e120340144091303c41d0000050750384402040b07910000c44200a402000c2d02c4020004001e580d0b11038220045488190030305256026400001d0710070b00c50b45100001e448590f2950303605484126020344039152080c10503600d011040ca00344180d00704183d069540078401d00c503403840403a071054180c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 55364580 1250 55363330 55363337
    0x603070e0c0f070f08040305100b0a030c03030e01020a0c1419080618030d1d100606050a03020c070e0c03190e03072411091519081e0c0406030c 63
    0x80250040780c01007a9184210340c1c02060341e031a003551412007600c021070707034000303008a60104d40070040c064000b4501520050048041216030603000800a21660902c4005c20100c4584009c3c000a4810240c0501400040c0125400b880040d5226034032500c1c0ca070051400030203507201040325880d0441021640303503540e6000e44852130510300f61a0300c90400030004034030f0300d4040c3c00740440c603503041040307440d698042d24040000080002c504584248000851421441035040d40b100d044880d110311000c031002a20740342d150000480d400e401a401c4510440064050031800083c42d55114407854410248150343c10b0392490240c84800d908204260840c40451829941c0c072203211001003103a55481d00802402d81c00f80f07400c1240100c5940c81005d9859050030469441a1a14203901070f1566803000c1342c54051260a1060044050180c10501020080004100c08c1d10f180180c070680c2c2c1044c94070b48650b0b24100c512000030f040c0101a00c0c07100060700001420005d90398948a140f24040c0700e0b00d03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 55365830 1250 55364580 55364609
    0xd0c020f100204080705090907151e032d0b040911040509060c030a09171903061d01030f030306030803040f050111090d030e010306080f0106090605060403120507060f0e06060307 78
    0x80d06130796600780e64040c80d802480b4550228011000030000680284944c0a10003107103283d500c801015501c3c8111440354a200405440d01d809001e4043d00c0000a40c0341c0d0b001160103030481c820f00e0340517092401d129145a9480d10742450341c9a5019070704205000741003884c080c80344e4006120031200d0041603205290407401c1030000b219944c50449400040e0310601080110a0382048170b110780f007100240b03045040018544001507501100011880d910b030f1000c03c00195504001040c4408514145610000c12801031000510f140b005003441c0b4001d15001480760b8807070742c445006501c02d1700e05444408030f06440c2c00420a00b4011030102681c043e002904080000010420200c0a2140141403080720840e010b1664031a5000300c2c010075076481100c4501d9280c0c07a005000f00744501981c8051402c7c00008506810000f00702d07021a0341c0014591010b050307002c2c0442e6070350400c8404855058403201040e0b00c581180c040d100e59244011301170700040c14900100340c507181940d4043c2800581c0d14 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 55367080 1250 55365830 55365839
    0x90f090c09020a0c03030b0402091002060712050903070201110c0301180c06020a030c0f060b030706050d11090102030913060e04110414040506180f01020d05010e0a0e0309060a050d0c020f100204 85
    0x203802615117645814045504034034000050007900034802c0f0280c00c80540c035503038000345500056090107401a500d50041032401500e6400540301c040701ca0319080d601c00c0002000651180050303200e44016102580d01000c1103600082c250b4601e03c150300380103044c840c2c441c002d100c803011400c401095a400200414100356401034440c1d051707208040e00000d4000e007460180100c581140c403001b00000c0c00c0d2a10591038000c09003440d0840540312801a10b0300c0d80c820f038001c48003000c035010410160021810814003030300f0040c40f10041000c002c80310b501c4040002d00d04190131100c80c06a8070802208608040c2c4001303100031240c4e81e0501540c05800e550500002c210003140c501d4120400c0b1901c6409140d80c040000c0c50010712030100d00c8558400102e100402c102a03125506840714000e00c0d110700d88410751a80141c1d80820310060710340d0810070044a061030800020844086141456800c0c0200046410120b407541d401003005130700404d00da0340035880e003131081901401c0b05450841c102803d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 55368330 1250 55367080 55367087
    0x9060903150902060903060118060e010e0112050709020406030906050a05040b01031202031c050603011d032209090c051c0804050f010c0503040906080705010c03050a0804030504090f090c09020a 85
    0x41075400c066a95119004195180c00c012200880800303021a4050b51391000401d004518089090b03080516100700403406900c0b052059040740c071101c80341303510380c1d0034410b0255001e0200d0104580701c0c825104002800860f42c0082c00c01085039441c0002d80d6511420300100382c640c0149800003d81c40c04041100241152905030b06494000c0d030010002c0c010a81305920b903100351010149240c902c0d800b0360480080d281c0003288680400d030001e0125822044880f62a844a01c0c6049116082070000401c403248a40700091a200d104021010280d5100c0300e100803100410010b075800020070006208a0400202030044002407059107000d0201c1a140c074241c90017580510b9100d00b51400c040074041c0c1c82990606e400076004800c0d40e5549940d4003980c0d0007050340d0700c01c807200e0307004078540021598055081070b101203400da22114500201035504603421000140218140602808041440b00f07251081e0f8082c00b45010000170310705080d003010104a07406500041d0351a00412a00c0c1109a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 55369580 1250 55368330 55368353
    0xb0a05090a061a04290a21060605090f0f0603120a0e060f0c070603060b03060a0314070e1501080a02250311010903050301060e01020c011d060c01020d050709060903 72
    0x104501c0005400b40101003040800780440e081d290301500304040b081c00001005444010701c0403002181c102505548103000c40080e0710700c00d1500d0a00c81f050450340d100c58504aa034141c510407240050025100d600064840f0815030742013050480c50307410002450804e054850b00308400328001c0095281184412030107110702c4c0042c2040109000b4001601e89950066602d1071909001e6079444920201c481c5581c4e240601c1000d0019040182c005060303589101124054400600100031103415510384410030240360254901c10303c51341034002840180e5514150160303641d0784200425108003000189003400141440240340e204200411407a00c41c030302c0406240400c03800003400700e00d250078180c60080c0002109040b65081c07040315070406500000440c113a540b15190213104000d031200481e52038400700100d0b03011500581c43d040030006140010014080300505842c94400c3c800403d6003607800c0303080d0540c0c0d80ba8a507014098100d82260040b000307041d0503e803a90780781c2d24507100e03460100c6 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 55370830 1250 55369580 55369583
    0xc04151106070c110114090603040f0b0f0408030604110c060412090608130b09120c0604020406060507020f04050a0b190807080a0302190f0b10060912030c0803060613120b0a05090a 79
    0x14407240320301206d0721100180d60307080100071302d4035881e45001e0529400084003910100c80303400300140010416070084010703070300a941085895040d95900c0003400300400b01d902c1000c2d5103a0080c420f0030b000400c100b14082c425841018050a00f02c8940c0d405410750495030081401e01c03603007008002070302e0904000c81369400d070010107600c0c0d203841d030803c080c1c00c02d00d01d80480a2402c2d00000c000718a1140002e8050081d442640c04201e0540d9482c41101c042c052240c000354081500001500c8500d01a0000ca802006024000408114100004c0c15102c0c1480354680c207042d000408101d800f40900040f402080800054698040c081c5d8000351100412000260307c0490485040184103904440d50601c56100240d40198103014164407910029445200c0001300d05482c04030328007100c1106603c6150341031f280d000c010340441c0d640104a030030003014250000409d005062030411180d92040040000e040d44c03c809182500381144400790003011000783c10700304810300c40d6032500000e0584503603 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 55372080 1250 55370830 55370837
    0x618030f03040201170403090e0f0103111005090406080106051203090d0611040f06030510242601170d020706170405010f0509010b0406090b10080c04151106070c1101 73
    0xd555503c0103885001c890000320521220b0702c0200020960031003440400d64006080e000c00503a5429000a42020240001807160340178900000c0785042c8400030844005031414031600b0201e080020030308441603603110144ca80e44131b2100700903504200c03400c05070240c005009185007802c50404600380c03800005000301f42555850b440e903002c40941041c0c6015104c00c41500c140ca5661381c2006000d403400ba00e162801001180d00001c0c6081c124101c0c141c8404c2c04d030208441004e0301f490641e441100440d884c0903d0002100184020500c080254041d0095050108a4220507140039190078015940403056512142c42406030a800c011444443c01c0700d1034104169980c1e514049016290a5800303040e04c0b414102408080c0c44190400342c0a014140c3c0c080020302e54030000f003c260341c1080b00d19070300300c09004040b0910794810031026a0000d60080390f946400e80e00c03a248940d2010003080c56000841d00001e440c1043d00900c0b842c0e400504510f4914600469030310744821141d201110a03041c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 55373330 1250 55372080 55372087
    0x9090303010e130f0f06050f1005030d03020a0e0411070302070b1c050a0e0d030e160b090603060307080d020a0c05030c130b040605031501090c1806030c030905160302030618030f 78
    0x10400000c1c106000c141e400a0f400a00c841a8684207002d0b07c0140c4a00d5200112080080e50282c20103240f01c00f12180200200003c5c4130202080e402948214410020070400414000d4103848a01030144e8000c01c1c0b403803880c1d585100c0d040090034030100c6d0f00300180c110030410000450740c070752528085651403145c10000d111b80b10b084154006003a643c1980107503000314071000d008141c16500074115207640c1816a605944d050f8050040c01285000d2020000401d00c080007135414070740f002e1940290054200c0e032890380c03142c00c0e00e0310f0007041d0741c1101c005034403501e003006c100b041c819503010080c00260010240c000d0a240000d03007842d200c5140e518410355803081c02580340d0300d940101d4000d11018095803000e5001660030950880f01b4094030501c1414000b07011000d45c840c0320a03011048100c00246d51950038000120054014059010200340d1210503040c0030030801d02001e40b4079800c0592510511f859441890f0512a0041225000086207c0c03116240c01000c01110624580c0c201150764 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 55374580 1250 55373330 55373333
    0x30605010c080d0b041e09020a05010c02030717030702030604080d0b0103020f0702040902040213080319020d080c1c020f0315030327040e1e0c0d02011e090905130209090303010e13 79
    0x400d2200701400f4032803184050703021340c0c10003031f80503003078090003565104c4865458500544008041660094255002c4c0108010b912a41007812207170030341c041e003600d1401841d0340000340f80c50000d8609403902c0d0790024000c420204503201e150154002030801358100688400056054015030303070042e000d2a114080c04c41190364540c1100e86c0850700700700105e8040d0300c502040b6501e03002081c4107880b20400261901400d800010000b45100d100d507280710207980d842c400c05c040384c1c010100c81032007514400c45e405000700321400540105100b101c40140c80303151600c4601007500c0f6482c0c0042c0280c0007007101c081d9203940001851000004401c1003002e0402041c0030800078940030305005e00b940614000b400d11840e0701c4402c4103102120008031800c03400b025003000400480100d000740806d0212101a0341d0803020b0300134a840b04c04c941452000199103c40d0b00c000e035030045900d00f00490018000350218030300070354920f03040303100f001c01541190b0401441d040503400c0a01403d2030005040c00490 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 55375830 1250 55374580 55374589
    0x60c07080a0201150f0501080a0b030703080d0b0414040219030c090c020c090a090309081b01080603010b030a03020d0f0302030c040501111f020315040e0d1206050a03080a030605010c080d0b 83
    0x803400100d0551008111703500d100e5100740004034052103001405800220b28010010b026408481d09c00030301a00300149555180d1070b440e8002828407840781e494403000c2c045580c071480b5003142c2c3c00d9416455007807454180b042204082003c482b0b180005881001031010801010000301611a010350014402102403010b0346440080f084403680304180204015800001d40c0110352180d1103925140302d4151120242916582c45512021028824941e06095588034900442d0080303c060300001c3c040b69003c2c086800c140e0849403d4015a1042303c0c1c50782c4260780020341c2c01d002c800c00e142c2141942441e2608079140d200c1c0d48107030381c10403028400315003d1030800d22031406010701030300010174005400e1003250b01a40044411826611719111045001d04080c055001542c46000140c014001803041c207643d8012000480e2811076654880031076103484504205001d90300520840c0d8440c0745040d002410703104240c21a90410006802140c0019803030015510084141480801c0f01010000810b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 55377080 1250 55375830 55375841
    0x80705090301060305070801060803180105071509060903080a020408060415020c06090a0c06050403030c0609050f030a081009090b0a022107030f0c0201060b16020312120106020708060c07080a0201 86
    0x39a81035103070a100204001002498104440b61346000303001246d030300c011254803400703400c240280040001d130b07200c0c40961003203008041040c8034900100c8001140c41800c1e0498035282000c0ba80b40d603070381c148202807640105840e50300500c5201e0542c506070030010b40d681c0b210005040240040703030400600030207070707070b66010340b2240f800c0700003190038928290019550340c9596a000740c03103003540304002046291242049400f5203406840e060007045d5250307500001000055001d96003802015001c0b841d0300e20a10051600340746a90b41c00019040010750001d1614407030303200d0b066040c03a01c0e01c40000160400c4031698400b008490040e21881051030f605026040d21040781318580c820070411811a40603840b1076115a544041085514010a0164200c4040e0301a0309500502400300c40440c880a290030001d46102405440025191945486664000101d0001030010400045c04140c0d8100304c004010b00800c4024101c904108404c068584034180d80a004004002103000e5034bd4000d4200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 55378330 1250 55377080 55377097
    0xc0c060c060417041a0a0c05060901021206030a030f08040c090501030b01080d11060105100e0a06090503060c041d130b010806090f07050a050d02010909020d0203070e030a030906080705 81
    0x211561091090300d4980c4031601100d08448004141254001014200050390169920b160142c2440d44040010f843c9a03008410000c0070051030b0300c0c04c40d0010758144640c5006203600000903880300b07035004401070111001030125010381c0c080c103039084c0420b82c44401d902d074072400350074806000d49030790405d13900d05a6079802c80c45107542010000410070841c158003134100d0f079001040d20303003803c60f450003191001d000c46c02110855001d040103100c030b031501140ca52200105424204622401c00e8003080c0c2e40d1401e0341c800008994288020002e60270144030310b43d4440c0c60b4090061601741030140c00a1695014201c0b08000001e00c000145042c00d42000c250340070350006483da17880e43c0d5600302250b171340700104d45444190107945640303814164002100b10a9501c01415a02c0d82e0b4240403e001c000100c00d1003d030f0420007480d9002401c02014402400303070a41038000075030740c0c2ca0b0020000d4070a940316140c613400303a44903016000100f2340c4082154256008d034540070096444156044540f4090080f0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 55379580 1250 55378330 55378339
    0x90b06211e010e04021003020a17060d0501060f060207080a0305040905040c050301053301090504200d060f0f0311090a0608030c0304141807081306090809090609010f06050c0c 77
    0x108800d468082501d00c01c51003101c450380c906d925143d007101a40039039a800c001168003502c0301a525072070801700710340c00300c800b0b8602502050750361503050a40f140766028486080c4601d03810701007650b050108001902440c00240920305d95550002c100d80b2492060441c01c50340c820225042124140c0100001c0200030020b11660900075041c044a09420301840c100810195002441300440c8e8070b810f502ca01c0503141c0d8281c551504003440040c0ca410180c204041d000c8041d107400004603c009801d0289500e00002681400c0c1040341080507183c1c2c019004c0050040000c100042140c69a07040f5000c013a100180c06803540da00c080090580703078020003c10701001c940300c8500f020000c080c008a82400a0703c20405210b0410302004030052102d0300d6660b00c0503000a1300060080c41d09a81000e851802c0038070007403c9444a5088414801d003c072a140d80004220740750749440f002854024108494008080d454100c44d08207140e118454141400404525071a010314280002c4005110182 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 55380830 1250 55379580 55379641
    0xf12060f040c0b0a0e0a091e02160c0803120106030b090a0903090503070b0d050f010e071b0b0f0f0f0709060f0e0409080c07080604020913020f04060807090b0621 71
    0x4c4010301006031107244a4000c0002140018010761a070003011440d240034030080a1a03080000d041c0040d40c06094040680d100c088084000140c000041ca0001d0042d03030b01960702d0b541c105410400c48081130340000d0801d401c101e440c0205903505851250442992200095842d0541c9002c0d903050038a80e01141d41402501000103152a0b02e4006000d1890901003c104980d0b8848803103003a01e00c00c0c0242d0b0800c050070382c0003440b03d5010340c00043d100c00750082000302540083d600d05401c200102d600000d4848100d09000b0529044a66030740c204000450074009460107520080407202c06200390410003000060601d021402190003100c4000c014105111500a505003048150b1001c80d60704e44c0362003801c40000d0318400104801d401154020191071b015103d1031800354019981d140705990100e46000205410303038442c800d0900524107900900345035850130b0f14200449141d2941240207800c01c0020400803030799000500142c100d81e5103800560b4988160044046c040352000f00507080d00310 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 55382080 1250 55380830 55380847
    0x1006060503011409090309060319050103030e0a05180f1b03090304030b0603060c071101140a09080105100b0d020a0516060f1107080306010e03010b1804020f12060f040c0b 75
    0x940154160f48902c01c4005034842d10009010078120100c030f40000c03a0b04240b01008035460280021500081e5468803240c20201038003e01044030400c5e84100e001c10340814041c40b242c24000808402442c2c02c445a020708501e181d152200008020b100440c0000060001403400d107036000400c2945cbc0c0076500894403450128030155881c3d02c280026039403403050f540013510301e01c3d0006440d440341840c04800c0d401e0602030783c0c807003a0808060701c0241c1841511040ca8000080100240c4074250131540c034880111324240c21a03003119005440710001c841d5070841480750603600ea0840f178a40307010380c10060b41c171020054119644d001e412000e00726a4110680c81c014882142c006115400400b46c080002c01941d500c65081c03031161705801000440c0c1400041d01a40c01034256010f0410040c001003409001d20000500034280016184000d0796003409000c2581002c100012409070161a10316484003805031103075868000802407007855201034001403c02182d0380f400c0d0024031080642c4c54851b88076 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 55383330 1250 55382080 55382087
    0xd02040c120911150a02031b071d040b06012307020411040f06020607030203100b07050c1504060e090402030a1403090901090506040e0c0112150314070810060807060503040203100606 80
    0x50301c03800c0c8100841000c052080324044c08480b000000c80c1c000b1450409255550390b00c403620744100d0f1029004500c8000390b42901c80090b0050381c091700080d403105242c50f2811030400310010301514100115280f0032030404842c90416201c6403002c03c02d0f1360b100d001030320028004d02482c141c1012401c1001c100010701c07041c001d0320501079a84030380035207001c1c1da41d90000720b04038001103590f1207a103c01c8003c10003d541c00280200019405801034550482c0e043e00860049402610548103024001400700b058640c4546449041e1200326480c0115003010340010b60350b00502d8101428007081c08841c2200000c081080710707103806014020348420b40e9601010801040f003100d46d107010748d003041028507914034049560303460120140c4800b0818036031050782d4030003040e901981d404401b440c1c0303030b0110220718001240094004840014002182002082400c1180000107468218103242040c01180b0000c10341e401518010301e03120707459588500000c0e00c2c00c10390b00108480d0034581000801d6081d030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 55384580 1250 55383330 55383353
    0x5070c03080406021e06070c12050c0d0905030106050d0b0c030702030c1204150203030702060a05060a03050a05010203070306050d05030412020105190305090f120d05040201090302031501050a140d02040c1209 91
    0x1280088800c60172045a01c0e548695007154600001041121044001a948904182d1200843c41d000d1b0500c058100b5403072402c00d07010079a80204502c05010801441c6c01d000314400750000b6121140c56000c1599843c1000101601d07001510301c0110005030094420401d86d040503070200304450303104115001d900941e0b070040c01182c1d1700e1034140c0e401ca080140000216802520aa80202501d03030710091264010321014008562240465000001003602000f0421066000b100016031b641007480c000350840e1035540c42180503442c2c19011102050011040c2c0301260300345651003040c1d841c20320041301d0a1040c4410740311400100c01b01600c2842d0b060340102d1182c004001240c200488054900703580710703180400c140e4015001c11041020710702d603801083e001407060504124441d242c0c1c3c00603061050410342c01d41c8420030240104090320340b48041d00d00519603025502603c00c1480042107070000c1c03040b40680516140c498901d5654400c0d820031440381c0b61640d0810250b0306926151600c07a4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 55385830 1250 55384580 55384603
    0x412050f0d0f180503030621070e0115020703020d03030203060f0901030f03020d1e030e070b0403121d010804020103020304020109030204060807091b0801030f05070e0a020c1506030601050105070c0308040602 91
    0xb03140c08456408140c01401655806030004c00450071070381d0740d20400403038070040700141c416051003198420700d008040007600c001d082401c614220399070402c48040d4510529000900841d4442141000982c541c4550540c03002d4043ca00075076203559660104045d403494404c1c0c1c58214540400010a00c0000600001018420740c00d4401100e6a03030360440c2c6080302c2c00c403070000c0c120140038007551090084d4804000a103903030b015202d0a5541d050b8076021340c1c02c158000e640c00802400a020f070320b070307103d5240d041001c040c460b14069010880c00084c2000c0000304000d05044d0700001242c1036a010b5a020700c000d5a000f00140010380e02c2d00d41103501e03140e29204040075503091014000c4451556510040140c030580d840624680c0707991140b41c202d60044d40300744c50b140640f100c0800d403940e80032420f605c104614038015a0714510500b061f490003140d003112007038209000d400e0001e00e40d00400c403541110000d00e40551600c030303141081ea06030030003680020445240001d000920a4010441c001c1d41d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 55387080 1250 55385830 55385861
    0x31106060405040803011203030b060a170106050a090311030102160302010b030709050f06090402061201030c03030e01111e1f0614060313080a11011d01060911030412050f0d 76
    0x15190304050000303589007900d000f0128034040c401840010018503d0181c10b078041c3c03801045101504000c55083ea00004a950016860f000c1501440d540003528900410107813030030724903040030f00d200249a2106030000800c8103a541c1d403c080b003654250162511a01d5a000528030507806140c06402040c44400b194040e0144100000b40c8400783c6c46250312450880007907444941d11a8208030355010300034412a4402e5060243d803642155031080c0d079000e940f0401c05644d1480c1541000b0300a8032030204010704121f405100d140f03015202041c96103858241d4000258004a980099810031508480c20703130300c0720f03840b038000f1580c4002900b041007260005081c2090710400902400344c1840112600e00001c0303801101c030720000e049000104510000740c03078425504041100a0750958a803101a141c910949000c400080502072040354001e0856400030040048541c081105601009001805125000100022031801201156800300b90b1054081e074234001d11080d40c0c01020214000d0100c07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 55388330 1250 55387080 55387093
    0x170d06060f03020c0705190f0e041104020307020319090b070503030a0f02090108010b0706060b0304030f020c0108150d0f1a0a06060f0503130203011e0c18060905090907080a0311 78
    0x440e800b034803c41d22421106009043c1d0079092001348055401501c2c49240506e0800c1c1e0001101041c100701c0a002d4641615640200d0400d410b101621004100e2310b144258410010b000d000c91b000412110104034001c80315003480400c02056034040000d46c01102241e0340095003a0400c04048025840340c5409a010422504000185400c81c02040c004070f011900080047c0001c207030729005000c0c00703403280c540480c410752a00307485074407500192021070105a40c01241150b0b260113200d80441181c082c603104020b8034020100440710724070348603580c0c00342c50000151414000302c5d50346c4103103068208091035034062075101d00c03408444040b981e18505d2440c020b004a07480c0c0c4140d0744c036074490742180d0b03915040d901c509218a040000c070401c220790540d40c41f00581c507a4600034030074504140d8510000203c0c1406004060706400e95420403030b0700401d09020610549411400a60a03114183ea5046c010f90314030b412141b4080198010b00401d105e8054803008050340300000b4424647c40314103480c00d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 55389580 1250 55388330 55388357
    0x303032d0402010c03050c010e101a04110406050a0203120f16020a050303010e0c0d060902030105011101060e18071d0402011d0d1401021201030809032107020409170d0606 75
    0x20301000565009000900c074003034001c0483d2280014000803070012000203042d0000d0b4907000d00d00101c9081001200c1e40f182d8545400301c040000c0c800210708203680a1100c41e0380d180c4420310174030030350080d1020b000300070540c0703045c1c00d100700190ba08a4500c241140e4090810b040208c0344001c089030014007400702003969802544c0b022a4440c80e16510000442c1581d0922903c41030034080140403540101c2c0c10b100303102c1e119a00d4020000180006000103a8a50501340010b10942003060032940903814460b041140500c3d080180d031b400340444002c980b9880702d650605081441690142050f17442c070759442c1000b18440302c40c070360149100740c0368011502094891303c0500b0003400800e0303902440044032078000ca02d1100300103125402c004001450301c295190303100e4443c0c4007a0402d441c503a5000c5020030850408000c092201d2199a071b04035411042c41f280c0e40c006100f0707204001d0103117499051260400030100e400347e17242886402c0e0152925840e01449000388200c0c41501300081140a0800 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 55390830 1250 55389580 55389661
    0x109050114100801060309021f1205010602030c15040807080408030a030c08010e04030c08190c060b01020c03030a0318060f050a0510080a0803271b0a120b06040b030303 74
    0x40900d480c3c0350300344103070f1030301d441507000b001004d20503078021400780301c2c0c842c040150901da070441d18011744070700d14042250f01e131200803544160015001e540c0100700c42c2a00300301c0040c1058002d40d036160ba88519644900d80006580030728800205000070201c0c010031201c002001800e40302e00c10356010411400b540380b08030382182d800e204d0104014510800720740407a11611581070300b540501810307894050184001c5440a866480324400900000052010040180100044114248003c00307490700468000b945071302c1380c2c9030f100c01416500c074a90303070070210280e041c0842240c10a0f002c025142030a120301010704411110242c446e890400003074510500700d4a080282c900c178500400c0018517554070240b0a40c0042c2c40740c14031890082605240d0303070200410021021500024120000280703c080b101ca52025180e01c1c4240c080120500c600e80036500c2040325580c2285c40c9409980341d400108000b848440c0105416000001c01c100140200040e0881c2d10700d010508404000080f20070300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 55392080 1250 55390830 55390849
    0x20a1205060a03080708090f0a08010b120102122701020a03091a0403120207060b0a031b09060b0904020f0904050c0301050f0d081b0f15040b010605071106130e0109050114 75
    0x2d012a0b414000c030408250260003400c030f8803031f014140d03c1b245040700c4002151503485034031a055581d100c1070b2824980c00d1410180c160101c0c0303a0001c1d030070400b40c0034568500c00001020740c0520042036038000c41d003585003000702c0c4a802040008640c0d60031106401006448103e20075121005202084c90210784a89002403041c1c1e059550031030308c6010756503c1400703903004070b405507551520f03060385400d2030f81c901c002100218426042c5041c00f02d04858110741c991411b0784800791541c03034030104004110303101049902c038900444005030384e50743c2a102001140100030300c00d03810514040801c4600c814060080d4140c0742c2c01c9840c049400c00700001c0102444101c480104404c03000e10010720450f031121261082410900207564003103d80e2141503103005090340c020041c40b404a4244000e0020052044d030140c0305502e001807901005840d03212184c44040750300ca01683d0300007003070701000d100b2001803c0940b41c419146402940d45e01c00e490f010300401e018400d00c071824403102031164602560403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 55393330 1250 55392080 55392083
    0xf030c14190302040b0d0803010b030103050613110907030f1a040b1c0204090c03050f030306041b020a0f211107120b190207060f05071707170604020d020a1205060a03 73
    0x1694110f5003884041c2c18004000382c4c0000003006144000b96004005d1800b0b0b10b000e5003480d490b5891420b0a614110001d4010b40f1400c03000320a03540441e981200705000100705440e80001c0351100c810881c0104910300032511890b19003880503844816a0500d00a031603400c4074148003440c2608100821513810095103040c0c03844a4030040010f0400b90004402180541640c484050b038988a00c2e042000758608482da80c0c2000081041a1038540305416400b05224400312006480c0e90f0040d65910254502406907180c07518110b080114894020007100b401d8010812110741c00100a400820304010961050060007000700300815132105020466821661811040c1c41c0c0d510a6144040c100e16480c7c1515001c00a50300400c00c64025115004c0e41103500140701e20308440001e0100d003a03005e441c0090b442c0c110500c051250f001c11030f40c07102407400c0032400b4940c81d0180014028400c41c0000c0d18628008034034250311a8006900c0c01d203d4540040c00e01c40340d540d1404009c0030914a000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 55394580 1250 55393330 55393369
    0x20409050c0901320f09090703030305011a0a030e07081204030606090e0c120102040b0a0c0203010b040b030d110106031a040510051e070509090a02190c020a060e01090f030c14 77
    0x250f030042411040c585841380001d041022248030200200c1c80d460400c550f40c01d50b82d44200e07000c10416078180300f028010700d403480402c0c40c50100701020f01120b11a5035015403c1584917074110b90242400c0c8449801800030200f01e030060940305503400041e030400c0c84241d910519204000924086c01e0003841d6484038814003805418104408102c5600c4ca1501c00c6034aa650900000c03c40120903402010000201e40b202d10018190b44105800d41c1c211000003806241000f5240c004c0742c07030004201b54102c01d11b04000740b5041c4001321407401082c80fa030021303000444201302c140048000000050081d806401a5040134400d4001d01c0165801528542035074012400f03000000070007031804e660400c409103000d901d4141d00000040c0c07400f4058560b0009150300040440301c1e600000c10108005a5070304280b02100c11903000a5841d203000c2c40b41e141880071000d011400c0317070b110300494009045400d04181489449040c054080a681d024440b002010740d0301d100141d20b00407024682d0350952a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 55395687 1107 55394580 55394639
    0x1c0f02030a0c0e0f010509040b03060a15060206040308040b040c0e0405010b0108070306061b020a0e09030306190308031807121a0106090b160f020409050c0901 70
    0x400900c40d1940c00030f9010745038802032160900003400e03c3c43d140c1810001140240c5400c25000380e00d405504204040d01101d03600c0014811509007514034610b4448105a036541c0c001c2e200600032a40d038100007400101e00c104241e50040c80307032030034048079940c610342041220300c00d55044645944030701101d480340d41e10141581c2d104456160130701c007480c941000900b0581e0310104140c17032041a514810190340710804000010520b250015180d480c000f40c03031075103e070000d8616070b100b03228041440b04e60040380060042600c0c1c0042d40b040c0f45031180c0c0c0c2c17844101010701d1001d02003030044400000d6030a004409000d445402041c3c150b81512148a02c0051010305800010174420481004d00181803000c0640d40000200460100c4a40c9981002d03507103603030030342c1e402940503040044040410401040e210201d0106076066411640c07115048003d441c881100c0c100c0001c1d804c07 = true := by decide +kernel

theorem cover : BRFrame.Cov 55215830 55395687 := by
  have h0 := BRFrame.cov_init 55215830
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55215830 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 55215830 ≤ n) (h2 : n < 55395687) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
