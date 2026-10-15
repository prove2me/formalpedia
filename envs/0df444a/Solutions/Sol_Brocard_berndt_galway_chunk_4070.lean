-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4070
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:29:23.545339+00:00
-- url     : https://prove2.me/submissions/9a902d71-7b45-4fe5-a0a5-7d0324f25f0a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 731834532 ≤ n < 732014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 731835782 1250 731834532 731834561
    0xc090b0921031201120b06010309050c042d02040803030f190603080a031d150c0d020301080d0306050d0506010506071121010e070b0d110f18040f0c1d0103 68
    0x14140d00701540110103090103002407210b201c05aa41d8480320300e660020b00030020010009400015100e6004e580072444807801703201200c19040f40c0601260446207030210861a03460040c05007a80e400d6200002c9280e4524250203505240c070301a40e2907a00d00001d4020300c400040000000d83d2495410140280070100040c2440410350302d0400750b8a43c0d0004107000002424101c020b02c1440214806071007241c8403038005c05050b00042001d0000142c054070805400c2020041c880032100a4005103000e82403c1025003100041c031103000d0200e69240e40018010641c5010240c049400450140e045880603103040e5a180380500d00415011115081c0350741c0421a10741c00710410320013415003109042920000c2260364401c6440a6071141c0b10700c21030148030000c0002203049440d98200f0b1150414042d0b02c1414203505909070701a607002807495160202c4040f290000d103203024090354800c455903c508000c6116404c0000b00100b0400401e80050f2441c2c10189185074426440f402100610f00d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 731837032 1250 731835782 731835829
    0x3020307110303090d060209010e0619031a03010609060f0e010e01092c06040606080f190812160323060d170a0c0203010e0c06070201082d010602100c090b09 69
    0x6c1c90244001d400c03207850580003845580790305101c0e0614404481c80380c0c1c50000340c032680b5100e080c0d045000e080505040b43c183c44000100703480c60f440900846001e40b0715404081551800d00c035444034008002c0e07001d940580114401001010100010103040d26038105010401e12030582c24603811406012040d0991840c2ca448411914004900907010b41c1c41500e040c03140030b6031000419036070090307e1f03060900b41d00000c400714411b071102624640564031610015051450452a0406140c0304443d0200700342241c00142c0086585072140c21140402c072100b02005802582c540078050388028015070103451501d00c0388041c403583d003041c80480e03610300070f000c3e5403100c034880010210841c608089005e50300f801d807001c01c46140851510f41c0c2180c0075106a0915146800440b000040580b00902d14803155401c4a10002c1050000c841c00040b4000c0c00125494070318024a00001082250382003860040c100fa2610b9000801d48125072805800c55107800d212000a1101e000c0b0012001010b4004d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 731838282 1250 731837032 731837059
    0x408070f0b061c08040504020912010501090e060906090d0c21050415050702030c0108040f06060803071a131415150411030c0712121d01060807030302030711030309 72
    0x42421030348144030548428507031502c11550f000c8280460007004001030b9050209004174102076014051100c401491155180000040c3c0b03801c440d420380144c1c064544441e80e602e0220410410b05d41c00c000180f005000600e49560043e4803520130303218080400c03100300c2d84e910511142c800c03045031070f1032221b6072a076103010880c2015200307a0040c413600905909500020402c1800b070300c161080c0075000342c040c1440c840c090004660010000b4012035107403861318800004602c5c1e510a88020748615802160345040f6410310020b143c0d01514000258045a0108800d0715100d407031202005500c030090701c241032100f04800b42004d000ca4551540c00c80c9503405c11410056041c01031920120960342048680081c24000180d440210b4286c100d8103820800e42c800607560b041c031810381800c1e600c0e249041011a05406007a280c0850103000c2034455900240280642889400000c0c0081001040c0a41c41d5517070185d00e03801041000740042c01d000700c0d000040d450070f004030703821010010300889200c00f4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 731839532 1250 731838282 731838293
    0x1050706020c0a050706020f0c04150b0a0903060b06090d021302091207170606100f0c150f0b09011d060a0305060702031c050403120e0705060417060610170408070f 72
    0x34007070301030300c1500c170b50382002410600100c3c411440d03e8044c00a012418055020301024210000c01c1d0038400c4110000000ca01480b41e024041402850b90307040d1007a0310303508107481036a2100c160b2602c01c00702007120180e19a00d50707841484484e41500e03c4007640166507085002400b4854041d03400c00c884064950f81031001092290a071651028180d2007417035010120303603403640c1c111086c1341c20603040d018806840d400344030440c05801440c036080c26a115150b4424540c001c400035150f00e00e580b2890076610202060060300c5218200750303120300040d89046a0500070203031024052640342c042d0004036203d9158800781002440d00703c4116540b509201200a50b281d210b10000141d10518036048503284060380600c070700664059039160a02028210300c40001e250300c104199803407140000000700ca03143e0b940948002d0040d000c00200440c03500c0085810030100074041403194020000d62640305030424000f8000920819043c10941d40303505d80001103105110f8054620449400f10381e04022 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 731840782 1250 731839532 731839543
    0x7110105011706090d17041412030403031b0e010c050c0405010303020d090806070509010f1b2108010b0706020c1015060f0c151a040612060507181401050706020c 71
    0x11001070495a00d60390b150030036900c1d002800b0103400020210440d41001b828030101c05078006001c1c417003034040e200c1c80300c90840c43e00d40d00179003020324030202200300402d01d80c0501c20b02d442c28003004220744440480c044000c0c042c10740c04441c54140710010140c201032010802c01a2541c0d00040c00400c2156140d040195913000700e01100400102ca07a20081a030400104200e0702501c6282c43e440d040100407030064030f100c03c448100c0010404111501001c0e4200b891080920b01e01500359042500c002d15840d11030341d81c1e0001504188210300c80100300c111200400c40342c0050700180e0050700d80301c0f01c010b8a800d00361070001c000c8c40705062051184404043c824a601200e2858803152040005c0007000e654030026000007078401030207140001d003242016001000a2505407100c080d0004071080028211240c03500708110310f080d03580d40001081058412240c04c0412800c1014020b4005110358603140000e005101508102c071901300d00c142d00640c07c0d500129403150096481d651000c01682e55031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 731842032 1250 731840782 731840819
    0x16060e0a06050c0c0604122709060611100e070b0a0503090c040c17040201020139050c0307030315210201020705042c0a1b0905060102160e0711010501 66
    0x4510b80300120301e0000e041ea045460307522042000c0c000b25a116200e0710401da5a2419000600003005000d00516203c0ca40e11105000c00800c2112028105800041281c042c0d8000800340a07a00d142a102250001101c1041d0850300401084c0014403120103400e00c0e000e0307401800090008250b00d411641c0040203540320764580d03401c03124803046c040204410743c0c2075a145040410310f101c0d901c0102c1c0c90071074003950744507006000200310317020303021480700400751030310040680143c50f241e2032044402d02c074888040c3e442d4a07141041c140390036030b50f08586030700c5001e500a05041e9600c11502c401d6840c02000c000034450107020b803044610b0584600518080c81d01c0403401400f6030384000c2600e261900c41e101140100d49095032541c1d40c500a845030815001c042c81580d4424036100270b000500210000360030349203200541d06d25614117070345d9109680010b0904e40c15500140c10820148400c45c980c40100d0310039910305820b07625505e905440154120200707100da5403c05c1e00210307003640c00181e90002e4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 731843282 1250 731842032 731842043
    0x3070906020c0102070617061f0f0e0a05150a0207050a170d08010f14040902060a030b030613020108071b0212030319020309070b0a26010314010e0d030216060e0a 71
    0x602e00032030012a12411240218000b140007003280360f454154004010b80e0020020f0400062803400f00760b0f011010719071344603810000311490f250007001580701400c4001c608040d20712190660812000540a12022400d00c0f00402c0c003180c0444c6480c420881d070340082102910f1130104640b42d5005410030a240e1443e03000c280b28207031546100e14412010103040700c003890304d0515a50f08100200e500304207070602d4283d0160300e9000250140e80c5640041c42d07104041e40340054a116040305243c01c2ca00c00070182c00c00550b05aa681000d41d810650890f07104a040c0b41242c8a64072035800e407600321043c102d010790071000e001140381d240c0c1000002140110341c0045002404540d180d8154281c0c44200d0345a4120780100c50100803001c125005025105440e05040d554446084003003402e08403020580e2168050240040041c0700d0a08084c110600d1108028803600d4031002c443c80e070340c0510030160300c101940000c400f248100d0240708081c2043e4041700501584060080c003541d941d0030510705480 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 731844532 1250 731843282 731843293
    0xc0c060906080124051c020d020310121212060e090a06050907050f04020c0a02150a0305150f300c040605180a1109040c0512070318020d02150307090602 67
    0x6403440040701d00550040313803030429600010001c1c4101c805401940c4202c03001c401c80d420440d0509980d00103000040800040140c9030319255042885110080d88404550050140f80e07401140030403a40c0f02c002c2e491030a05445400d1501c00301d030700074511540680282140c007800c0c01a680b40115040d00f04c2c501461050105460b107100641e00c4020728840e00d40e01c0380c0303c40ca002040d410660050030000c010281546c80800560300030a144d0303505120421050440040d2003561690144104c3e50401134011010300c4144480c8040399110110300b990512994410125810840d4010380107259001c194001c010b10015080350103988148a0a1052040d42004c03404521414052150780441180d0508a55182c03a0310052000a100c0500c4003018088208009099510b940c061a801038070302d0b0752003556500c55980103411554019003108205420319400c03068002c03a9a03440300715181c04032b0709600b4164141c07000942c0143c684000d0360000a02008000d80581c204420108682040c0c00340c69 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 731845782 1250 731844532 731844539
    0x1d190f1b112509020c07170304050d0212010e030f070303061403060c0a1806091401030603020a1403030705010e0607200d0c0614011e080c0603070c030c0c0609060801 73
    0x80362451119103140866100440c0c2e418214070071a42c1e50311141500c61849601c42d01c90300800f042ea07004050f49284c96103c10800c1203174031881c8070f02a2244c18004065410036040200007901c22180150281c40780c0029600e01500c02002c1d88030070b41c15003c00703048980e0307142c41c0d208586890f0082242a070220b4a404000140d03030602d091030044580005001d484581d07240814640c0b41d40000301e0000412440030030341c044515015444002500e8684c41d5141c01c1894003e460007081d181e21483d1b4101802c000b03003080182c4079078101c80c0a0340c0c0f4008002002ca01c0d0003010030701c5c0d40111000913005600b015281e841d00000801e10340c1c01040d566444420305c0c4010324039070040e0303c0044040010356024a141102e402e1007000c2200400c0c1c4144800300d00305101c1801002d08442c00e0b008007003241440710201d030028a818603010010400b20001d0405800008001074082c00010306031400d0107001418401014810600e01070001d80c0145459030340f135140d40004081c00803600545011807000170020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 731847032 1250 731845782 731845787
    0x50c06190f090b0a0e1f0204140102010b100509031005010b040302010219050d0e060f03040303050f130b0411010905100806040513050a110a170c0f04061d190f1b 71
    0x940e036070f0888100030060311640c0340f140080005050348840350041a020304515000d0055000c00c04149403c0961030b142000c48a003400610040180d040d60700d806603400d01a22242c00307004000440b410f0103600c418000c400700f800c0c03c0d01004804c006518280010482c0c101030b80c0030b4400e981c002e038211802000341c00000e08403404202d0300038054ac2d10901241064501c21000f10f144d2810103010310341080342811003054603400945048002c00e40300d408000f03200d142ca13403000e41d0100308a90070211003489030721941d01440340948083c2048203903080182c02640076200c541e00406000e03041050020002d80300620b04481540d03410301c05d07401c00000c55400401000307025946508280039101f003a4a070750314545030000140340c151700040c0c1c00600103200d1080c1c030f11041d14072060394098003c1000400403c44a542c00c0070003503201d14036103203007030000c9290500c01d0f4840f1000b4448403081621200803050526182e011802c400358205200d184d078042042e0400880e40400300d050600e02c14108805 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 731848282 1250 731847032 731847041
    0x204031208070c060504060902060705010b091b07080d020403170706060504060f0b2803090c120b0105120a05061314012906070c0b0408150702030d0903050c06190f 72
    0x600c80064981403c881c0482c620381d000359009403107107a000031030741040c1d8003140441e0003907001600d140c0d40d5010380052030b0801c0a421036000c903000c82c00000c48007030100b0b6607169014400c00580740c0030000c600c40c01c050b903665044402454000c8001942024480710654142d8040716040707a23468200388001071642800e0140c40d00307a664521a034224a400c00d01052484e40048465541407054070000e081c42035081ca9080740030b035690b651f01203602403440c249106110b04c81e50040c44010317070102006001c290860007490644a0481d151881d02103c43d90592038558a5a00038055008403003d01034032007051268400000c1c4961101902a0441c0514508071018041151110401540c0203142c80521880c5050900002407107507007021126201c5c0030240c00b55400407220103400060903c114001040314003180d5500c8000c0c0030691603c020003c0d00c9001745042441c4c4d003a16866200304040c050b07400d840356020020b0440c6c2c8030386428202809001d600020b120415854a50424280800d6028 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 731849532 1250 731848282 731848291
    0xa0b010b130603020a02031611040509070510110d140d1a010e04020c0c090a090f060501140604120206130b130f08010204050303071103070803030403080702011a13110c010f0204031208 81
    0x1039400c044071128081419004044100d40c3c903120011102d54580c2da5100c3c89004040c04070060000500304010321080e90141c1102d0f000780043010115200c000c6001841965101081ca040d01e00f090f8040c0da030031000e0040007a110280c500341440110001e80c100c4e0b03545450803090303030345030350403d220ac040c00101d100d541d10208481d00041c0c0408001e04107800c0b013680251a5080000b01d01c12035072034004151410a42c1154040d80721001003000c080e0012214188140c126540c52509281844100e4003d9084800074065400802c0751114013800381c4859004095510b050b5603525140c1d501899400c070030b40202805403050300c00205543c0e4051082e1015143c014004510700007d1b901d64401d20b030010409180c1c948140340d000303e03169400b030000d50700445c800d03240e00800b82480c00002e4203403030070814940e50781010307401650b00a0350303030210b414810000200001042c90012600011a100d6094031400035820643e00500007041c540c020000c49008a903082a15a00030303034100d4407014243c9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 731850782 1250 731849532 731849537
    0x20d0612050604030305060105040812030f07210b04090c140312040f330203030f130305040b0a02250801150608160e09010b0309010e0f0d0e01020a0b010b130603020a 73
    0x400040011703010364801a0040b00504186060640d00d6891520b0f0880b00641308440e000003005000510a0103000180c11010500340603900034803180c0714010300d00d0491800007003151100844000e5860320b81c04010103a03041a4212062a142c038003c140000c41249014043d200b0341d00d200324041455003c0c3e41c152108259161051441c0185030101000d0010a410300880c00c514201c00320440c9441c40c1c034552174250050344e140d04d842003102c00c00701c000400c400307030004071a8000d60029034000121400c0d901180045d81d200e0000c180124584400407244042524000c0301410a81c910b114641e011640c84c1d100910505141c0300c00280503400c0c912440000c20b00d03030404105001894403080407003030510f1410040d03007000100040d000c0c0c1400c0c0e20101c0580c1d000414000342d14820f004800f46642d440f00203208140c0044841742d0f4540d5011814000c001c18810405841da1091044642d010380225068000396110051485594231554010600c803080000025000307000340203650142200c0d8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 731852032 1250 731850782 731850793
    0xf130209151f1b02030d0c11211b01020709020d1506030e010c0302070b060d0201021203160e120703060509070902030108280507060825020109030e03123a020d061205 73
    0x1106480e400054401100c2c0c0c1103070030a0510903a00c030000d41e441c5c0c24180c00d00c4c1030145180c981009d400c141c000c130308401811800910342000c40c1d800103071007021110441e0005076500c0404423100300030b00b07a0b0316015a850090000005480703515800c46a40351038048003c21074101c1000d802d5040340700d0400d000b040c640d040700005030071b440c1c01d40080c2016401070046d101460100c0c0c251b881c081d0301c111008502c01d992aa0301c20b003456132068031003402010036541c4810138104190076681c1c40440d840f0041900d42c035070f400215a040244202401400b5440c02592a940c68485164480c041e06509010070700028848a0307070f140e8002c2d03504541c1074011010300410f50411604030340101c00102402e554040c0c02c1450f498441003903085ea4001d103c55800003440f41224035008000900e24942603110754891b280d050842c40000084a03103444400e14150142150001c02d071852001a01c203410281400b404961581c08030390b00148815004e01808101860f190481c99851039207042c0080d14030b5208 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 731853282 1250 731852032 731852053
    0xc09030c0311012d08011508060f12010e03031f0501090b030717190c05270315130c080639130e0f130209151f1b0203 52
    0x4000d4903100c0744044c50031000c0f00c0d4020600c110b011040001c074541d0010000d48400c50a584044c0c100c1c09480c0f03c5000c1c2540c00c1041c0340003407030b02c0310140c1124451040c056158640340d496804004203010448000d00400b43da44080e15200c0d0070403034290711040100c0c0300540d442c000313490560303069440586621400d607003010155401500010240001d201d03600000c8c03402400810102032080e0403d0000340584011201e20a050703c001e4000d8800307000f8103002008041114150044e0a022440e03106030a090b5094000703854442602003005642d42c0960601081c9981032500e00c0a6a010380d5a50174aa0b6641c086980c2e0362000b11540c8100701d4800b03102143c620300b007404803074064040380000c2000b5070b50300805852a90102c65903140f105d07400c003010001c160140107481d501403241512451141f40c54280200c0d01c500550000b88501d0010002039404402001c098104450182941c004507900702c90003104d0104010a007004070315401c602640130000000566001a400b0f00075006d41c000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 731854532 1250 731853282 731853293
    0x8010b0a0f050d03120b0d060203061c0506180a0c061e08060307171e0606120106050f01050a140708040e060306071205100e04050318060a08010e0a1b030b040c09030c03 74
    0x50344140000c90b103842d00e411514940c0c4580d4107287d2540541001641c9003009420032840c000d600c40c03860402e5481480d0080810400714003141d100383c1c0034010188030040303400c0090505055000040c84002c00180204079254020324141500c3d0156010300503421b0701a106544040c3c1c02c81e142581580950402c0c00f0544202850009000c3c2240480d00c00b80240e16013000c901d03c04000509441d03120b80100501460901481191140e202c8000c1100a0511020810721102c1c4504141800000110006080e206d1340b034a41c20064080305081c1c441c2d041f450a010664070510071070302c1f0f40c560003001c18061316000ca0302601403e01d5486125030075486a1503c0d010b010010541400c10703021030400164440d0101e0b205100da40300e44061642c03440031030b0f241580720700304a00c1a40598024002414096001010b503410340b00d880306888810707a030719a2441d016162410302210740380c004281118006070150015541c82d01c0448043c41402110030044034941c2c11803002030400d00d051407040000ca20f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 731855782 1250 731854532 731854547
    0x62a090d02040209040e0c190f052716140306100309170414100e210a1203020d050703020a090e0c0405060c030408240103060b1201050108010b0a0f050d03 68
    0x41c8042c00160408000c0d10024040703030042680c4407195080210041c865142a00c1c4d26000b0543c0c008048005a040c5068801840000d004440c0501400040c1c3c0214140005220540202c0e0224070b035134030310b03210703c006030040c0e40d0b90904d00104c0d603160700000c0e000d00d90381d0030b9a01c40d2901070081d016018400004401410503024259050b00d02000c4004105000d000107101130500d14002d00d40001c860024040c00150aa00410802410030500c3c642c5980d030280840b441c500c00101c950b0001c405958003800c005484000511180d4080780c0c0048154041d0054100c0d19911074040044d0741e905041a42070784150248040084c051f201306000d8a0700c1204001e030840030600f140c40c00c05840340e021540c95485800c03c0c25140e840440c0c100102d00d410820a80c1402d0004d00544642d07084429002d4444e10600006000c103403983d26071041902c3d00900c1e090b44007444402440309507500e03c49a40203083c24803025010307030021f11000c40c51001e0703828500c0445501130300d42d100030001602d0803100072 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 731857032 1250 731855782 731855809
    0x20301060816120633020a03081008010614090928080c01050406061802091c03050d0515030c03060c070305090a0b0f030709090b0d0201200f062a09 65
    0xf1115401010807442d680c8500700203002010900b90040204405001c1150115078446002c50b5907504000d24440e404548610581e5040c10411629224000c04c54005c000a810140440d0719001001400080e2980d031141c204030207403018249600c85038a5140c842c06410543d502e0314003400c90100200c4c0000484c94105070040342c059041c0366240d20308074291074056400366038003903c4082c24000e045440e0091010051546000c521740400000844c010344c02e04082420219038001c2410180340c000c1003240e16480203100d04008524010543d418160698840580030344a010082a01410002141400703640d42d4030300301e401c040c0c0d1994101c1e80c03980329103207076034103d04902800680b4074400300242943c1c8000504190703c034545000003c00346052a4001c0c0801410015000406e4455100c030f070f1581d60702032910042c10041400c080541c000001c05181c0070744520035a02c208408046012801891000101484c1e010401c5240e8100c0c1c50300855003e100c031003080fa28800d49000039000f11030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 731858282 1250 731857032 731857037
    0x609110a0f052101080f060c03160e010e10030504060509030c0309040207020a0305070306060602010c0519080406150314010c0e030304060e011b0b07091e0b030a0912170a020301060816 81
    0x1c0741d1030400c6416400d4405c1c1d1212036250701c00a2501b54401c0c05101030340e0f10280540c42c0d54154905038400500310719103441030009000c444980c14409074458640b0701101040074080d0f68400d540008020700509040703505561080c9817030049041d0041c040201c4070202c020400440c1031110350410400290b0201c0012a8041c0d480800040040d1043c0f00c408021070040c1c100064951a040000e400e40320b08078003d07420400200900868510703419500800100946441d80546e900c0f0304d06140105202ca032000d010231000200002008070401c4030106080c2060b0090003003400c1c80b44d095034040d00080d106a8160818001803051f1441104455802441490301480740c0b41400d28811407043c1c08202a625a08600c2c00c001c001a0132010000042c06110301a203058a4400c4040d0030340d40031402a0108014000045880200d1641008544682082920100007001071004e461035456074445101d452044001549100c82d44c801d481c12184c6589950226a079031206180244058001350030a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 731859532 1250 731858282 731858317
    0x203041503110705063103080f040c080105160e0906090615070615030b0603070608012303030a0c150e0d080403020a050610360207080f0d0609110a0f05 67
    0x4a80c1c10030881b070060842c014610303000c3c24483c00c0303a5100c9001c0240c41d620484007409003000280e00010f0039502c1b28501d2003042403512685444107150445a1009103030358282000d0150700c0c0381072074070003010603140d450341240101c0d10300602c81800e1045400543c848999400a412814201c1104100c65049022180b50000c1941c64404445501c07001e0503d80c1c2d002c000178070400010150094002d8001c41c000d140307241c070b0424001e02c1000c0c14081d20b8010582d00b000b0390003100c080c03048600103210040c1981e0301c500300d0410040042c0b0340110180c4030103071441c05402c4203442902c204846104030030041c11f01403c00d140180d84005000d0030031011482102c001c00c0c0868400c0c80014010092014022500f1340750000e003002c0c0c1f0521080c03541c0c1080411803003204880100c0429940d40896400c05030300d174621400d1070710305402081e42c41100c0300c10014105819400542c00107094441000d0204115241000b1005c214001e90b100130010400b1100c2800445026a029040c0f071100503c0b07126 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 731860782 1250 731859532 731859547
    0x6020c031309060e18120a090b0c0f0114011a0901090e0a090c05040e03032a03040c090606031407030f06050d0b041509050d08040f1e030e01020304150311 68
    0x246041c20707551140d118142e40c2c0c0018401c08041c5554a0781141c0300300c6042004c1e440c800107064071020b0310040350b0350a1500046c41015280561880001850b8030781c4c4590700c640c41e81c6a00c0342c85840000341e5030ba5652a080c10028100320f510391903030507500c0d18400c1e07140042c1401c80c2603400d688010025418015100300016480c408800301e507209a0440e440859041d19900d00092404038079000a84100d041c5505103c03502000810f496101c481d02186400c10b0b242d810951440e401d0301201d00e40c1a140020030403080c40044070411003141c003880410031540365140c0c0110216554200c0c801c2d17102e286840030524031482600b1000d840c0c01d01000c0085c01542d55400645200081241121210042c2c2e0801c0140104c40c0011722521380d09000c2849814481c0d034840381c4502c0741d9858a41809100d0001c1001d00c005c541d00b0f41d0503e03a122140860080c0280f100100c030200c0448220002040154480300c4c1e0352002c000c0d13400700c070140054a0115400000d0a030040c00a04c260244c240c0028032011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 731862032 1250 731860782 731860807
    0x151207140324060306010c0b1e0c03090f15160e062b021603050a110618060a0908090609040f0c090f15022e060e011d0105090406020c03 60
    0x11400b03141000300040c4407009451450300b100d411500018442e1109004011741c41c1d811030400104994003009580c0e00c0c0e80c4034900581c031280210401c51603901c2a504000c081010000214095074210049490103044400ca499840ca00b504142c9540004a0042404450b10f0100c5c201e940340c4c80e080041e09111020003044e070603000f00240740600c01d0340d03819071882031800214500f1070310341016055181803400d010102c01000418401010001d000a040341854401c90703135812502d07801000d075440741c240f2422140c41e403100529012000d004a80c0440d10b0fa550b0303881070749034990b40024a01d08011080c01002a0740e00140d1415400985804424408600318460080c00c030380c440d103901c4000c0b820840c000070075902035002182004105c1d5010031400760002024140714060300380d6003020404686045a00b074070348006400c1c07503500b4800042001c0302d02000042c10396401c103030020789030680116850110794080c0305007600001039901142c04250b4640003052110290700480313150592041c0007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 731863282 1250 731862032 731862037
    0xc04020d0b150a11012a0c14030a0e0102010b01120c0507050a05031b12120403050f0c0705030f071d0720010b0102010605040e0d1101060b070303150515120714 70
    0x1407031010341c40003c0c551003481d000004078044a512000810902c90380d1788162004618950003d030803103900a0240c071415210302c0211200607400071480f500003403418802c5a0702d4000b06148004501d450f59000195441403107001d070070140507036881d00d0000b0160b112000603e014010340e81000010064000401c00401074583e88900c90801199144d0100158982c0342f000d000000301c2c00d0300700304140b5140750010800d444c141c070703908806203215407118038098a0074400d4a0050302610302c0400d00b00c1d00107401103040c004481060302070702d0400d0f030303410100b42c0ca6001a01070314001412034103d04d03002c25186568503600003074905100c1a6081451100310544049802540641e03445401180507542d0a018440c000c00c02990103000b42048884419101d24400003018100000c054500d04030003030941108000b824040d4100c2d0f42d07800c06c1e04006010f481070f6980c004903602c4030500050182409403005907000701c0100380904003c2241309410040f0301c0a4048401c0140700283e86c0e00e2403144400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 731864532 1250 731863282 731863309
    0x218100c11011e050909060a06020307060209130e0303160806100507081308060108070b0f0f1806030a0b0a0f2709020301110d1a011e0c0605012c0105030c04020d0b 72
    0x100c4d9074848480b0b10400070026001070425014041c050001c0209a4000080c0d81c0380c29072042001d42c43d0704040d80425246128540070340d240604288041c0000c080c04001507015001e00c1e034205c0b201d004a8141510700003030580780940c0103030075124400a141e2140b00580f4501e44600342c0d045c80c02900070440c50072030f200e5400c0042d06400000c0104031461007040003034010403800240d107061078040e4054440301d014081c50b80410320301c001240503140c40c00150b40484260020005078076030410744002c2c0020101504424020ba884110103c0c55141c000160001c03612400e600c01c000c0c40c188060808540010306192041c00d40311000200143e42c00c1c000c0501c078141d07180c9625142c0c1d142130280c9066071400c1036282007505d4580b2400c58241d0340b00c0520411070b14900800601503540c020300300d030800050103025090714135020011403800d00407083c0003d013200e4034001c81c019550f00c030308000d40c07118203110b0b184c0c0c158030480c5030240034100b5801811802a51680020307200b4020400b007090b9884115 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 731865782 1250 731864532 731864537
    0x102071712090c0a09090201050903010905060106031112070c03110a030804030e19034d031f0914010f0b030607020a0c0302041109060403060218100c11011e 69
    0x26019070704500c444075a5501c401c201c0c008080080180f4003244079844540644140540c0300e010143c00d59014001325000540f01a0081100444504043e40c0700c8a0038011400004e041001442d08051307007005465200307104002031f072540d88501c44160380946a050041b01030000300c058002e170034201880b200100d00c2c001e03112020f42d85810b1a000303028100700740780070b403096140e91024230000040c800983d041d20740c4080c04544003d8004542d006050300850605500d1000c145c6800500e0071042042e0040c51143c4100c0074008040d00401d40c54000210441e0700d6070503461001a02c03502e1b00d4008130841e501820111b0ba280600721903040c06d59034400e00c00d80b0b240380c0b0b505005003a820b040001940c8031550744080d140f55034150fa140b04014440e4440a442191500b5400e00500340900450300e50700c1d002400c1945d255600d140040194019103001c0d0541d003c42642e02403031b42010016181408403541d180c0c10304000655800c00782c024140d400a0401117600585504081032210174034030f0081c03c3c2c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 731867032 1250 731865782 731865787
    0x30e0d050a08061c030309060216110a051f05070c031403070c0905070e0906040f2c031306120b19050310061a1e03070306090e0d090902090301020717 66
    0xb40c503000020306400c1c080e020030031129050010420000544070382c185004540220241440c001900a2070b00f100340943d04044144200402d100100508a60560380e00855951314020081e0300e882e031001c103d42111f07105520a000a200d080142100c92042584086054490722402100009030507030001e00d5000145503424050000c00100092100300e50500c0540f40c4580002d007907841540c0c10a0050a14030041802a92aa0007042a0500b00c140801c082e0040c840d1510450945044049004203030030140071020001200b140c07103401c0c481d104000035a02d4900d00701c0d00022800c2040c040341d030b41e410f00c0d2052991007800074140d0410a501140d1102d0030a0109410f00000d40301c0d92010b070b4a03041c8104014580d0174494034000c402ea21341e5684030400e525038060241c0c070311191411055400410040d103a42c050b8090003d0350789800b0100020700c0d11160066440c03800001c40c0e0040b620901d0304002c1ca80d1030b50010031030154068009410b00220342c1d950003003440440300040056401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 731868282 1250 731867032 731867047
    0x314100c050c0f0a0210030b01110a0b160e010f080402060d110d060b0c070512070305060106030f05011d010314010b04092009041518050a0c05011b05060115030e0d05 73
    0x40148601c260203107405040307880d0851707000960300c2450603000400c0c9605c03008403005a0f03010720000f0300c02c0b000000980d80e1008a034a408540440121616500da44103807240c0c84c3d80301d101d001c0d8465200340c1a102e0050304080d0030f0b011340342d4000040003203900400421000444500c54007444810070005036a072034860b00104040d106583e4290800d04480d0014000c0c403608120000305681152800d0300c0311140070302082c15040c10070744150006442c82c4200000040c900d641030380305055020600100b000207980700c1403400d100b80c0d0724031607140c8113501d0040140302260540c14031144c00e102000001800981c02404201640c0304000d06603003484032042d031410581007174544542414401c0f1103070713807132480e140d40c032000141c0e0069600d0f0f904a5550070070a07401d41020805201d1203030003200715555104640313001d000740c0d00b041c09101d0004181106501d400504030100d4a50780340c2c17100240400d40e0030b01041c000c10000b044400c03420580c641c4200d80a40c5e0080c45150b0001c3c0c090b07590503648001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 731869532 1250 731868282 731868307
    0x7050f0409181a10050303130b03070207121b0905040206070209060a090905100608061909050111040311130516030203060411070f05010509120703050c15011214060903040314100c05 80
    0xc5548254082c0d08100b00a650111409130223006440d10724901c40e4032502c3e4103034103d150080030742103003240303600c000c4001c42440341e4809913030000041403058811283c1c541501106803441540c1c003d40040041c4201030062500041140c0d10070740151100064a17969403042003a20744480d004c2d0742e16005081c090005200300c0c0258000781c490b0754000d1600d410501c0300c200087c014598004542e640e61216074080103000e411441841c0000004240c50348e440e0700380141c07011590743c207840c030981c520a00000102d405006051082019003069202e10060070301c241c001c0d50008007155806541d840f540d080600031280a0302030b00303014004c06070f45214249803846c01c65001401c041c4165103c4a11654002d06c00403c0f030f00c2e450744c1071600300c2d294041a245107103443c0007404615903254503c400400c0c0207155100d038102203800b440c40f401c40714100104e5140c583e0825900e081680d00204418804900481c0a20795540d041408541c0700c540300040103030484060210002c0010380001d8909000031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 731870782 1250 731869532 731869561
    0x120c0203011d0c091e101d0f130f0605150a06090f061409090c1801140d0e0304090903081e091509010603020418060507050f0409181a 59
    0x5420790046100305141c0142c150740d50248500320303200c0d088840008081d00b40088a130b07501444a6080d0f001c07542032000030400b001043c0e00610a200e01035000c01c0003040c0d80707540c04a004858501c900201031f11100c1c642008400c00305816103c09100e003203408009803203031044074820150510301552a403242c400300303c400f00a5500a004014181d0420300c000801440c0e00b104079544c0e0b0a05050000340d000030f01301c15000d0354804036031224080b020818580c0d90000180000c0300c0803c0c2c40d100c0f10310080f0064412030303101e98242076408401e1010380302852059204501c0550703900112030506680e1460801543c0b000e070002c0340054000002d02c041c4c0740c06070038800083c404001c0d0f8009185440f8030000d564401e0070629134600010000031502911007940920003950b00070b4010711108036010003a50003906400c0f412a01d0a141000140145d4802c50540713a54006401486103000c0c07805c00420040c1c8810b400040f01c0114581c0d00781c000511644801e04540b01c4d060440020b031909a84109005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 731872032 1250 731870782 731870801
    0x201030e030705120d090f15150b03061003060305060c0c0706030504020f0d2a0e0c03010303020a0b06060f0301092313020d110303030c1b03161509120c020301 70
    0x1a803040c841c070b600142d0086030001d0700c0c850319007015480703105555007038001e03180882c40a01182c0380100c1d040d091110700603405074402070107601442070a607000140802010b0740c0c4218044150b040c404a68030b8504107845038a8658a4980440c1958803511880d0400c80c00380c1c3c407644458130008a0f4100e00350140302d50b40003818a0b003810880d92600d600811144800150040c1c419100592940100300e0852000201c1d002c4202011001c0b52168450f6229042e29001d50300001c400000018590900b00d421241a240d040d4050100d000311070b07940c000005c2004c2c0145a02400a12442084040c00030103580240100e01010440880800a02240b02c499400c0e03501803e11130b50420680d42c03d0110662201d540c16100c0d500e030000b40781000c06100c0f50202130f440d41400b0010510070500030080c060300905940040980120615496085c1c0c0c030b21031403012049044e06104008045013020b00c1c401c04c09032184070003083e098203680c1c844c1c2a45103485d0151000c01d902c002110150304003441a22480e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 731873282 1250 731872032 731872061
    0x50c0a061d100606050304061d1b01021504050304030f241e0b0a050f010e03010908030115110706110307060c0908010f020421020613080d080c070b160c02030604050109020103 77
    0x203ca041c80d0b0002c03c2c6100051000d08800d0b00d90010345071000c42c48810b400019102000e94880d410100c00c0343e100c4400284e0640c0c0188180c0301c841907401340701e10700c2d0350146510800951800c0c1c80c40d5070700c2e11200303119001992040c040c081c0390020346409032201c0840c00101e00300082c900980458040a090700301c4076022481d40303400219040c83d140c030211101510022291481141d01060040b1101c680b10402e10b030b0554240071480b410800120040d6050750348802480034a80300890044400c440780100031082030380704500800805024038000288083d102003680e140c001251121019210042d520400080800e202000403076000e03c80c0c80034508401d101586040e00d018605032881e020700c2134001c1542c0d000c4d181001155560012120b007500c45001c010300741c40d6225102911000c1f2011036030041008440040e00c4400000125040254400c520f01c0c1c45486440d036400300d11124100104c140700f540004100580d070100301c080e20440c0700c1c00011910041c541300042c02d45102c1000800c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 731874532 1250 731873282 731873291
    0x70201030f0b0f0f0a1d06040b01080c160c0806091c050403111017010e06040c0314180c210106080a0203060f15061b0c0a1203050c0a061d10 62
    0x250b992280c00c0b075a4420f40882e02c42c0c003070300c01c0c203c0001c4154119a2080e880512003805071103540e070b0318072800340c03040c1801c65007000100703018401580c2080b0104d420f0036483d40d040122400d4509250114030750280260100403034103440c3c1d80008e180040a541203002d9900183e031410884200274290050a485464000e09151641e500c1d13048045c0304009651007503028484409c00644182c203202c0382100c815404800035655001d08424418080d5079260190b4100520744280c64040c0c0a0780c103400040c100d68040382c3c2e50300340006154102010100c1c5c40c41c0509a0507071080d90301e40c80d502408801d101403008034801d000c1201821210503070300409041d0002c0c1340c54000f698010500c0c1d80d229035152455081540c03001c104114640e00c030442070b5840f0102003400d074021901842d400e05030070384201c116100401da00080107040d2185106100c8110040104000068800c5000e010041c0b40c2c00100c51a203030310780d50786805940c02400c2a0881c00030405004014540070020b2111100f6102c40800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 731875782 1250 731874532 731874551
    0xb040314010b041b03050408090a031217040206030604050a0b040c110f0f1e12040609030b0a060b04151b11100906080606031f08070f0e160c030221070201030f 70
    0x208030070388403c0340c4217050ba20b4000070140185501180c0c0440401011805066109d02d01188542e43c3c0c1c0c2481c2000850b0580401000380c1c0001005004d190000c4c8454159640c800811010f040001c1c2900d02c455220380940c041921a4003816465031031980f1080c00090145400602c0d04e404801100d1096004c0c8081c1da0865101040844e01d501c1c90511807805c1030002e094140c074004130050442c0320b8a9000800003040c90b808544981640d210b24000b00ba03544402072000141d9a080c00759646802d410070003008416150382c0310b014460030300d043c58112400441004002c5503421041619a15807561a5090714501008840c600300d103542406010181810801060201c0080401d8080c101c0000815a180144065040000311200e4034482842e00e03682c0d0242c84801e940304081031403420400c003103901002801010311070003030031580078803152925000315090301e031078901602540100040c1c072005210300800032510350192038a1b00d41e240f200344001000c41c1d1140b0040350703002d85000000c0b03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 731877032 1250 731875782 731875811
    0xc110f03030112060b0a121a160f0521040c0302040606050a231612030f09170d021c060501080601050702010c0f0201140d0504050111070f1b0b040314010b04 69
    0x76440355400c8800098850075070780210301e0980c036a8002c3c12001550107000c5040144a04d9235a024030a4642001e0198540c140c0b1034a1403000001c00c1404643c801c64aa1542d51185000d05107100102200c1c51032188013204400003080103440a0700c2c00d6040700001e005509041c01410002d080302c0c0340c000d08d003407a4404014000c000d241000b0092404150300c201c3d43d1483c8006035020461003c81c400a119800d00e80800c0e00340e010030256000c00e090000200d101117040c418a2686a000b8100700d0500582c0a0448400da00114410400300e0f400d0120000c0620095501c401e104c020800000e01142008005070035603000078130242c10444204940b900503640006a140081d03071005821788400c0031407005a50145558a2580601c280400d04070080c500c55006180603a020703200070072140c9540100700c4100d04c600a0090b015425130400c40000826a446080906071500c88000c166600d40d41c0481d126801a4070903682003a040603c40301c482c5083c4034030b00690108440c01c010080e2680e842 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 731878282 1250 731877032 731877059
    0x1060e0705031e070c0803150f01090b041a0f070f060f02040302060a030504030c020303210906160810050a03060218030c03100903171810050105010207050d030201020d0c110f030301 80
    0x10801044460740124030320030f00445c41d5000c0b0030751146240b9203d02d48076032030b1400620780b81c20080c82a410204180700c50b5011300b1801d0f040c2d52240d03640070303d80b50410074601203117040e2096541d260f5000300b101003441e0030728038060b1071401d2064070042412030031703030521405a80b40c0340c1d40d00d00c540384108400c000613510507048503004003090801080303554490070181c501c21078040c0041d415002c00100950244020400940c02c84103011032682603440713011a890b0fa0307040c1220381807008068400d021144078002c10584c0e80c402d6031150a09101511080412005407039984100e5640d600440c0054284424807c0700c092040182c00805201984400085d518103207428003031125540c0d040301d10140740c0310300800c0c11b00c00c02c521841003440c100070400307580340b003140c42c11524903028400c10402e000c041802521b04813141680140203240c100703010003c24940e000c3e400c03000d642d42004085514181400389209901d940c0e21070108414034903903000d0410940c440f050060350400c01c01070000700041140c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 731879532 1250 731878282 731878321
    0x618080c01051804150b090a0603020712030525120b040902180604020906040b0405041b080609132a17060103080c0106080f0a050106090c0c020112060f0801060e070503 74
    0x100c00f82140c0881c07001c036009190b400e07082158041a0b04000c154034601c01c0042c0203604099440002441e40d40c8400c800328065060b0040a18052070045460b8034400d400464000300000310010b55200364509484000512100d1480840c06411031041c820000c1d101c2d070310f1891010303142800804050f9000501c0c1c501310b500c2c0b14a48900e040c0200c0e4044d00d888e8140e6203203000140500d07540f15107c48600d0b24640044c40f031103201d50b040401c10308000e41c183da00138526040d25101c103c001d40b01c1030100b0101a00003003914402c4410441e140010420300c0b407024512420f80441d001c042e1030101c081f1001c025040c0c004558489a8821990801000007000341c1160740181c100e03900d4202076041580540000c0e0b20820940c428056501f120040100f810308085100b84000c008255548010005491050503910045603681c106440554014900e422242c0c001080001d0040d495008c1801a00c110350820100340c0c0d5144c409028141200b43c00a801c003245044c40c41c1146031684881d095a000101c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 731880782 1250 731879532 731879557
    0x10e120301033c08030105040506040b030303130f06091209050405010b0a0c020f270f0408090607030306030c0605040503060f0c0702120102120a0e011503030e041805070618080c0105 80
    0x80f8a41000311020440a11911081c1e0700c2d141071165a0412805a400a0043d18843c0b40307030001040c00c03407400d071098486080001d000b440c19a5600c00800710320811401042e80d90106680c0450300040f1a44100c1c1c60b0341348190500c000610721441c008206041700d030415070007241b40c40700500100f804902640c5003e9640e1401640300501440880e03056400c0300747c940e400c4422545241142804c1c541c46200400300380441c03102940c1d4101c00c900d030000081d1409820110100700501403410300170014160107000c0d041c08540c2903625901c20010f07400f00d0b403280300000d001203802c0c421031406112041e08981001c1c900366103800d10720a000082d218030349000b44280411341c40c0006120003034044d90701c1014a40056410791500c5c5040c07501070840b15620000703075403804245080800950580d081920341507981da440f00d1500300c05101c000e02411404a068004c590103400001d1803c1091002030301607039840000a0414109075041c0e030010740c01c40c6c501c4d908000002040c0d0303680300c802e03030b0304030203c03013 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 731882032 1250 731880782 731880833
    0x7060524040e1e0a020909071e0e160e090702010c0215010806012922060215071b0605041a010e09030a18090e0703020f010203040e0a0c02011d010e12030103 69
    0xf4038060746001480301c2c000350889660000c01c02030103404101c800484032000d04e17450142001c9400c000c0d05a255001f0200b1391100f110214001d9107611480b1a4480da09092410f6004061400034005480c00c8031000c0041c1e44030b0100c0042281c2c180601906148840d1009503503504006240c0d407a0382d414045d0030030281400f10310401c1984110345620f81449000740c1e150b520030400c12010714040b8541d20300c0d09032041a00e80061000d00c00150410780002d20806032806885a4004450b20000440c10342c0142801c1d04030403000c10f880c0c1c8256030191340300b100700d0514146050501507070501c050b4000d608021490040010365a8080100d030301100c42890640d40c2d4074502d00601e44100340c10b8011090715803a100c1c004900e5040000c100041d03900032100b0402c941c0c074240c01280d40340301e43d00448610500030340104003480341c180c00c07512405009000229101145601c031840c520400c206c1215560744035905840d850b1810f01000c0390040c1c4990300ca03407070366045840e1b420b92949281440190301518 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 731883282 1250 731882032 731882083
    0x604050901140703061a0301060e0f03010b030d080f01050301090309060305040f1a060405150a0311131806060f140111070e1e060d0c030807050307060524040e 70
    0x20b6011503410303492000a0801800c000c84028000c10940c05400001d80c0c15002c52005611081e003503130304962059a900307100581f50f40602044071101400302d81c040d903c41c480b00c003813507500344607034200707051035a951416034039012891080910069220754081c0e45400c0e034840100b548410f1031419078907181404035080c0c50300e2a1801550042c940c2c00307460304000f0780c2a000b40180540c1040d0080d5800c507020300461303c0301c3c20f10754001c10072010083d6200380308440401c0018980c41ba40324040500030010641e0b50622a543c0e02640d01202c101e070669090440d000040120034410000684100e00319a244503003000d031245a00308143c0140750511a50080c8500003410811110780a000030700c04101d07280c240310364044001c4d00ba50b0640714210380444000740301c07428840081201c4c1500900a810a245107032030713540c2c850703000c9032068400d0b0100300038401c04102180200c80c01070010000c203114003000402400d03036600120340442c0c8182d00f00706068042050001b0340d98948060034100510b501358 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 731884532 1250 731883282 731883301
    0x30106051c060b070b060a240201110c0307120507110402070609020a03050f0706030e060f090708061006090602031315051e07110118180f15050324060405 68
    0x55000c2040c03019400c00e040880c2100e943e00143c05058494540c6149a8441104220b41c0c0e106a0191003000d0703442510300741044004204419800125000002c0e05005404e00d5006a84c418051013034240d00003d010003c104000d1000b0111400030311703100d400c1032225034031450081c281b00d2a80740729030b4010500b241400840d40c407c44289500400144185d0340e40d00c1c02d540c80e1118850901c1e05400740d010005000e900a01400c22080c110030050f000603030f54503031101c5103a8400350208a89200d84100807400c940104441d5010f20010420140498030b080c6004000100c640c1103141150024072800728601800040e1a0549440b441070384245c0c2c0c1145411189804aca42c880e50066410705080343c90003a404000340781c1c89001e2084641d00f4256600192008079508000d403528641c42c1c20104607402c0c49204400c41d9050860011a04401002002042c0c07600e0b208071451a0f65203000c200004d180c02c01c000d144004158802203e90a0740b00301d00218210b0041509005603103900020b03040382d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 731885782 1250 731884532 731884567
    0x30f03091401150e01330302091503061e0105070f0212031804050c09130504061b1d0a0605090415030f0c06170609060418020303180103050c04050603010605 69
    0x304141c001c1051002d401031212200c1058420301114003000c100108150039400d00034000f40c00103202100380f10154001c4044030080042d079080826900b400110600e642e80340d68040b200099854843d101c0c1020010410040081007603480c4094204801511a0740c1080c20364102941000720482c0c01421800418102c5461266818890200260401c10f5000807000c1c461812400d84082241741d4561030000f5807031044192440d0301200c9190a45500e11054200c1a4403600c00d02c00440c1040a2100c0480070000d0f034440d850100f80c0b944c030b0520103900603a40d68030848200b00d17040004107103481c0d80075140d4482c206001e8043e50302e50320840b581202409520780111b9001250000304211410080c0250526000f000f0004024070500346100f180d10700d5250083c04010401c20880d06e4000421004243d5200b0107422840003000080150389c0c144050301c143c042011403108421808800141103601c010310003580c150041c4800e10942d114442501d054034401e05029603598100003c81441d030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 731887032 1250 731885782 731885813
    0x601020f0105090106031707020d080d0b090106111b06030a0903140408030c0609070303080c091c03020c0301180507030b0c1b0a0c121505060d05070906031a0103030f0309 75
    0x250b0a000500c41c24480562001080300d00414040c040c490090300810f1803071081a60103507104c602c1d229010041070b0030400424070449a0040001c0e10324011001c5504900d003640a100424a0f02c071507143e44010502c9114603c5613071214048107240c4520001c1d842d0300010b00b10b041110360751040e090030103018481c002c0e00e5445030301107641c45070350b11070707181d5a00d52180d100483c1c2d030b000e20780204201c51400a000030640342e03d91a035946a83d140f42c10644683c1201541c564051580c1d001d4000d1000614110106a4041c0d0b002c1c00000308070800b410300751110700d01c1076a08a541400c002020650100305541640d60000380c0510315161487d8520140c0a200c034602010340e9030813003012400900181e441c90040c4550010105503540d030554203420304803088050151400c4000443c203100c42540090740c0018000c3c00008500000e44505240c030b0515000300c5400d560340c04040c014089100300f900501920444000803540c159940184001c07802002d8000307260b02d8080c09000c11060b241500860f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 731888282 1250 731887032 731887063
    0x1903050c0309091314061909020a15080f0c07020f0405060d02060d0e120c0c102102370c05120c1b1c030c080702060a05040e0606030618060102 63
    0x10341c280400c0c102c0103000044d4040b9042c1240d158010183c140210300c140c41203108103c04c1d41032142800401c0c001e081c807603100300e0340300d4280030b000300341c00c05041d200f46500c0010b0b0350f034104d69203441d801d241d4000d1b40c0582941c649440600c0400016559100300708400042a180494030307482e85030105802d500c001c1c1c8000d51000b0042445014045244d0040000540f0380c811150b002403050385000766846282a6444540c00a110030701080c14804071205081c2002d10f84414902c40c1c9011540e988001c0d180d07001020390700020015940c1b80000c5d0803c249500032a00c0d0b001088000700c0c425070031120100050b062043c3c0b040307003505005050040e4504821340a40455545e0507800d04140c441c103207a48400c4000010284d50b0b401418040800c040440b52040e03054000d14642c1c0301500c1ba07000c6140c045a103842c041140c5030041e110000074081580a030788800e912103082810603144450700a00c868000d40c0240208890341e9140d10000c003290740281108ca01980b52280101d0804c81444c004808 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 731889532 1250 731888282 731888299
    0xe0f0f060f130b0a02070e01050a03021915120f05130b0a060905040b01050108070f0525080711010f08151e0405150f0405010b0a03020a0216030302030306040e1903050c0309 76
    0x2c0030710302d0a004040ca403d8607405d45c4c00e41921006c04401101089c020365410034182c034000c0c0018100110a03050070070400f4001c428041d0345600100040340d2123508500050450071440c0c141d580c0720300070a84a680955414000c516101d07258682c0c0710840c3d040078054030034920205285081c3c6170710800c090114070900744854505410712047c1c041c420322502d03000405502c00107408603c40c80308898004020b039581d0b85040d242074101d610381b45200f130034003d603c05998600c00021b0000d600030704003e8400c1c000302420000040000d00b40b128a10180014031915504100c0200340611817145856011504080391010030a20340c0a004003100c1550b811510b45000d01240840440340010300c00c60441d1082c0080600c036040c03100f40e82d070038030a9407003a0b00e00344004454940244c000d00661300c418411a401c4005902500b082007540d41d0040d005030308008140000d905250141d40c89412081c0000c00c1500070f02e030030305140240f840001a007088800b0911401c009020710444400c3c41000304402d2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 731890782 1250 731889532 731889539
    0xa022206061d1c0b100e091b0f0a0519030506070c0f120e06030f0a050a0207031d01020a081210121a10050d0b06040506010804050601030305070507090f0203070e0f0f060f13 76
    0x8509a814004d0110702106c81c00020088800040c01215000341180d1130100e0f401c0040511540b180c442c1011035120710480070200d031a40381d91007a502c812a003040000300052940c2061030030300030080c0c100810400c0c02d031080e03004200d103020513030440c41d8020944405191004070454030500060045507004600200f0702c90000c0e51991a1405255130000811903070b01c407144048102d108102004000c180070b501010358030112031038100741154060040e100d40b92050744d034414159010158030080c014000003400424030004104d5000b6210900640603c08400d03200c9900261402d01d03180442102d00000075010800d40d44a64010080603001003007100481c6490340d048081100c8040c000c40c070b0302000411941c4075820301c601540c0c20002a040d1a4219101100d0369444032006960904c28450b0000d00740c081c0344549200c04200d10401070303e80c01c0c8000010520540c03030b25094030030b0380340d669100c840d59264480e14116010465050769100c10408141d00c660042c10018001c4402c68007000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 731892032 1250 731890782 731890801
    0x50d060b03010602100f02090d0f08160f03110c060315031e3304170c0a0c0608132a03080a02010b0112020309100504050a022206061d1c0b 61
    0x10142442c5c050340030303c0046074401c0544100e026951090758010b444900d0301c0c1c0402c1e0300e0094500d0150003510420701d881c1400e000e40c01d040f1585076003222800c20080c0a00180365210700c0c1c524002000d00050100414503c000030001c3c08050051070f0000c0078020119410b03501041011030414442c000c0041029404407241e0b00c0d40c24800348103801d200355047d815040d04e5055494180c0c41c00781e0402071076a032100d4885c6040148280c00011440d0020010390005680c02c001010000340300d5024590300702d04028000308100700c09080282100c04900c0c1c0900025854042c0034241e2811007103030058883c1106c0c02200010072940b024280da04001494103582d641904042490402a202c51042e05e00403003454089100448440340e058000c4154180030110301c3c3c10054020340610100d901c007480c00d40001c0d09a1001c410101c01d101c1e00315440e18082e2025010703010041490342800c29101e54060002d030544540000e5140c880c0f400780c440d5041d030000902c5554009900100c0030404c1d49090780d000b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 731893282 1250 731892032 731892043
    0x151201020c0d050f0406180b180a15080f060303040b120f06100c060906020c1507020105070c03020a0b040c0305030d0b04110c031c0e030d0213081507050d060b03010602 74
    0x101401c074060071140220290090007169880c2c0010742c2c5031403070980b810504031403602c1600c1801c03004513480200000d044100f01c020708031080100a034010300303981d0141001984050307540550302c0c90310941013880c1082d4200880aa100403038001c03248581d502c01c40064207610440d00b0040c03100300c0118403503d04640f1010158415038083c84803076110746420040010003012048000c00140521001c0f00004410342c21400180e48524005810301101983c820b003040804100d146d07114041d00100240f10343c0c240541d039000045418808101c86003928000d488014442d405880102e5190204080108212003003009540040c2501e03140c4c060140200041c1c545214840d02c240d081583c02e40e51462003008403030140034614002c4d40381c01c59500030380342000402c506284004d84d6034801c2c45c1000b007040c80103040c941e500303140050b50340e09010b85080c441840c60b008101d07258480d0343c02d00021200141c0c4e4580043c00ca080c541c1d250582c07801d400707003c5c10003030700000c6014002100009066800199 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 731894532 1250 731893282 731893297
    0x403030b1e0a06020606060720040914060121081c02030709080d091413110408010f0f050c0901140405030712060c17220209040f12090b07030815120102 67
    0x602582070b903980c11040740c2d640b6007034130101da01080400c01a000960a65908068941c41d08040f502d4004103000190850700e0421058130224400750051503100f07001e200050160807540600300d22aa8a0b0041c0f5100c8050b43d00c000f0b2880e040040d08085504008219102440329a20b041d0b50b04d16180c0300050a9580034440c080b0b99101d40c000d4218668081d1040d001960500018025644098003c011540e84d07012001c4103455a5110a1f00d04200c480f802000036004800000c01c3e5460120745260450300341088400c811490300060049080e16003080b115960702c01d01e410324600501103500c13031003449140d025980c1445100c81c00184400008141e9011500031581001041c2d81a00c09031880500180000f04051141d00000d00182e14034054004042254121081000e5190b0202d034032001e05a80c01d80c5e6400c9100000c0042000e01610401110168680070322030600e0021641114002c404000381030003c4080080d42c0c0805410380e20740301010040c5010310032842440343c2070003540500c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 731895782 1250 731894532 731894539
    0x13091b0f05060f0f030129390f0303091216060915020c0d0e0102010c0c02060d02120a0f0e0d020a110409050a030f0e03010e06010509040606050303030a0605130618050403030b1e 78
    0x8265410310000c100656001a030951269840844400800046003403a0649104904041f07804400e0303058007044880ca50782c140500440e2f4909064102c00d14141c52804c9800310a42c0c2000505200300342d407164200310369404600030500b21014034142c107003d0740120809000500c0490303500312020000a04170f400a82640302c1204e4100d075440124203840c40462070f04003040c01c8001040050600d04010240c0384601c980040c2000580d8001d016409001d903409044161a04e080218942d00d51062401d8480f800e8002c1200c0400c04c0c0010392182800300024094405038120700a154031160001e4900d181e000d416641d0b460000e02d00a8580d80d10440740100043c2d02c21841035603810140328061490312000018403c030380c41c100411010b01c034010001c48409454800004a94134104081c0d03005194000c3c010921038240418448000303581c81e1108046401d1060030030210380800040302d162030302e04401040980c0c4030b00301035001d4211b02c61000d400c25034294901d502c481c06c52503030810703007030089 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 731897032 1250 731895782 731895839
    0x933060e040605031e0c0d05062212050d02040e1f050901050a09020c070f030804081612020d020f090711060a022503030b13091b0f05060f0f0301 64
    0x60288012212140111a0150f008020003400c0d03100c01210390945c20550800ca13040468110045004003943c3c5104603200c5c0c2c0703c4414042c181d01050112a44031000d000c0c0d22140a14544448040340442c2c28498140040000e04483c0001c0d01d4044801a01142a41800c01e080c480d00030031050401c110120142c400c0c40e2008642446e00041981c101e4000900300d000c410305004105009500c000e83e030f442c1d14400c055000401400d4050b1040c0110300a8000c1d90712145040343d1142080026011031442a645034000d20030042080300d03020400c0d40559000350515007520100c1c0203004500200d5074022402020844502c5e440300d2142561180401070b0741603500d030701980c5030a90107160221485004982c1d00040ca040010011480300d5000b89000709401d981c0f400402c80c0d40303404945102c2100e45808a500c280940703401d42010503082d0000c1c00c060503141c01ca0346120321446e0301800d4450030340086d242d01c4808092041e500540b02c11451039035203583d40c1400c4080840c2e081c4240500c400c070b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 731898282 1250 731897032 731897057
    0x905060a1d0a290c07060c05060a0e0a08031305011b0f020a0503090d330506030f070620191a0f13020109180b0103150f093306 56
    0x100d40010454618450740c02d0310740700000800545015256950f01c48031803c0c004044035010400a2900502c802c0e182c60f030315aa03007424102d0034818002d064041e950309109212254040005008040a80251f01540ca0b074890201e880c00030140060058019801c1501c00da200703244c1c904044400c03071007580390303544003003171059080c0d8130b490050002810b00e400a114180780c50401c20301020742d1511030004d003514030408a00c60b0f500703408483c48002048601c011421080260b034840d03d030300684203d0050200f00782400c1510341d101c1041c06602c0030060b070341002d000d120b0b020301d901c84410741d0000241c8a401d12001c1307440d0805040300307005981f4907001c6440c070030003035289009040c020311480003080b450b0b585101e095000007564420403410441d500b000080c1ca86a803950040c210110007001007184041240010241d48a003940028141e0704902e08124a240410101003150011400070403140d2101007580045150402809409045001e5000844d0b49008901c02070f6481501c07a511480103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 731899532 1250 731898282 731898289
    0xd1202070603091a0604090c1217030c030a1e06031a0703020307120c1427041803270611060f011503050603010b061305010306080a080313030905060a1d 67
    0x3c056101400c0003201c070941c84203001c10810b94a51003c0040e0021414000a50310a032101e42c40e54409004049120020390812994460441101074025205411414a900c40a040d4800584450505a5101000e1021308042220350070158451f11003005030a5803410008003003202604840c80b203020050002d0321440c000c0c07090300d0140b54295920b0300c06c84802c605800c000c1a120040300c003802038038500d500840040308010070304040c7c40b4652a912180c0800062210601c003842d483c800c0e41030400c1c40d003441d003008508103c01500340c5865480322030001c460710071b880252074a01402c4040803d011540d01c0d001400c02184820031001c89115031b40da030340ba06e10f1a880c03e010381101e00060b886000c0300548a50400d43c0c010000a0001801030400310001c1c2140d40302480c0600401d40c2c6100822480d038043c415070000b00200c2c0d010348002e51959032403600038480100b5001011007641c1464062600c20400340010380700107401903540e00000040a488036420f5102c112100d1405400d101d55401d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 731900782 1250 731899532 731899541
    0x20a02190506220b0c0d0c231e03010e06030715020705300d0905010c0c0e0417210c0703080106030519021306031d030a0804110d1202070603 62
    0x140c0080142c14180c80750100340030780c0840c0c0c00010003095160341140c2d01107158411aa07005042c4a41807030340e1010301c540c070902a60903503900b0398144001040d48518420790145c980081c40007021445546818a0400500d90300440381c0c0081181404030003c5105e5103c89003080c09804100c040b0307901107554011078884c5030304400040b00140c2180740c4c1085503050112001c590340d51181641e0707184105001120030701c149011200300103640702e50024601c45801441060103440d0a1a08694958694a500755884540e209103043c41c071180300048c0038048541440703116103826950b095a502d030f66000360060842114800d464040075000410101c0c20f100003110807a60707150b1a54160b603031900308160004c10000301012010450b401005004030400d2000781009564030b09c40c500702e1401e0000080c100c4403182a44859401801c1009407100000801c0d600b00a5051806505654985c41c0c00040c0300380d000d41d200d070050803d0f041c070300400c0400a1586d83e0001d140d8216045642d070f0702c50480558 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 731902032 1250 731900782 731900833
    0x81609080613020a080a200105040549080a050705030a080405010606050c0a021e03070b030a11040f030b060117090a05011b0903020103091e0c0f0503010b150d0b13020a02 75
    0x80903141c04035403221f51b42e6004100300c1d00c050401070b0406965401003101411005610b0494820b0360b1444036210000515980b154681300c0315071044092100c40e42c4007070a0404101400150001c145000750398803900071203240755403003c1a6a00c40d401c40c0710240041d04256411a01ca50074000c1c041060b80c4075400740c816480151004019000d0306409000c0c02c015000c00e13024040d4500c00d1030b01402d440c20400c2400400d81a001550703240b81c1200c049003160a0852244035a81080104100c055200411041540d4100814840c075031194001030700e148101c100030851070341161080081051004c10342c058204c0c000c00090018089820714a68200060511440801e601032801d002551103a031103421000d203d00014082d0001a5824060300c10340404102c517440c00e1841b0500801384c100000300003c0c01c00303030020310607803030382070002444001000d11400314050042903960703155a00b5000310604500190281d00d040c008183d051000c0d500c261001000b61007401580045d091080c0d82c4601c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 731903282 1250 731902032 731902043
    0x2151308070e060a0e090f19060b03060103080909250c03110d14070507050918070b0403080d1e0615030c1b0807021906080414010c081609080613020a080a 68
    0x1240d040449000701c5c074034050301c10300542c8114400040c15020800c504081d10b00340344001e03c085d039041c0c540b00c01591030740c039125070080d0400301c010800900c41c181038540e200c1c0d044401c84065035407000c0700c061100082c0349060070740d200e04180004241e01f0210606603a8040d035203800000081d80c1540da40d9007140119280026220310100051a80b45005050340ca031054080d940120b40d5840041c002c140e040d502003115880094014080500c1004008010070640100c00c0c2800c0c519280d003003260140c21901d501c0c0c2c41e165420446010b40d0b0402030441e081e45c01804000c000d4441031055aa05102c402d081c020924010700e0884140c0034481c03a183d843c0040040c120f48003816520b40c22aa0000742049811070700e50500d86010181092081019050583d500c04091038076003040384c54003144098401d0681d04d04aa072180865000c22800e500c0001c0c400501c0300c41500d403100704d030b102e440c90780700305014040d200500c00301e820b1405045500324002c852894902d41c880c00030a4480300158002041d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 731904532 1250 731903282 731903299
    0xf0103061109131107020301020d0509060603070602101d1e12070c031514160909110306190f030c0816151209120201090203060a062102151308070e06 66
    0x10f01c9986400843d10340032450a0142004030070340c08079013640c1011030195001b503190020001c117040d04001255020808800030401c061904030083c1d25902500c507601e0301c194403a504105400b03105480d41d105443c01904860400b034420b401c40d0403c100402c0b00d402c86000300700401001d0884102035450803500700e600902e2051071655099642e040d00580804059255400c400800764900649403103031400d000c001c00392000c0c15800414000e540e80000780d0080c608a0310000750455103051302c4e4090415246204105091446d03406000965449000c0c0f07440d10001c0403042041c03004551044640031011501c2c1d1041c01c1d0310442840106015440b030208940072480c1ca014814640408403550300d000001c2c0210071620355113107044a41d110600980e45418414086040070824580e02541900041103070506004d02c01500c55000102110044049440402950b460300800e542c0806044901c99440d400303111240c0761007501d8440c40d032050292601c0080c108148080907482201c000b04100e2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 731905782 1250 731904532 731904559
    0x10f05071205040c0504020309100b1806040b15030703020703110616050307111005010608180601060e03010e03070b040c060504080316061503230318270f0103061109 73
    0x74000d01c00240300782d40e00203000c00009041c0c4c07142c0c80158051081c95000c1c140e075100c1c10b40710070283c655903e401400f5104003400340003000449807200f90003200448020405200140004104655485002c0d088100c000240116248c166006140040c4261182550941240052611200201c50100c1c1c44000b045103413031054032882c0110360040042c201440d000f1028252540340042041c66150740d90b41d079200500c040c9402000482d03101d90348010108003c0c1000040310344820040c801c7c5030501c100c545441c0d40710742e0b080d006070030f03440680b2048a071190440c1c100481e1182d8103603810384000000e8a004503540784203504540036a10003100031450044050b582030b5020586047c181d0740540ea400b805800e02c200500000000c0d4014540ca04108096421080c5820100c141ca5801c56008102c2c4005081211040307c1e903610f011511250b130012010702180f9042c0a400b24130b141c1155181c108140303204a4000c0506072801a10100720080200700074504601c030f00385c49260f000d0b68880028 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 731907032 1250 731905782 731905817
    0xd02030606040e1903050406080903031e0901060509310f0f0c03081308010b121f020909130623160201060801110304060f050709031416080f010f0507 66
    0x180310341460f101c2110041441e10003104046868400b0440000d10001010408030358001d40c0c1c075810240c0607020b1403550030303c1c098103490522003103003c0075005405030010703208200a5200340c0080c08040c1008003985040c030400c0c0d210131a680c140b507040f036210481103040040703004800c0103e40e9100508400750480c90712120440c44207400111660310700c0450200010350380e03034043c1480d240808800c51686060030455829a040c074944e0b10301078004500840304038240001c8070101e444540d1004203442d20390b0f10745139002e1f01c03807220f469401030340250a01040740c0340c06110031112400b440d000c0048400c08503191074141c10005004c0300780410701c00810292681d46081a234104e66a00000420319960403010b4207560964400c0f44001201004000c02d20a1601814001b160190340802141c42c05220140c800c2a03680405440e15a03074401c0c40854030010040f40c528400c54000000001d5510400f2aa450304083c020607040d50810003803a41c10340140c01014010001e5440b04510900f00f00b000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 731908282 1250 731907032 731907041
    0x20010c06020711041a010207080c150310030f0b040b0c040b0d021b0105014a0c041d0601120903091401020a120203070c06020706090504090807020907030605040b0d0203060604 77
    0x143c07809a086540b0141035940c5100703842c2d2065503c2120540c4814100019080100c2948030130003d0308548041d4000d41d0701c52005100103144684080e449844417801420b00651b540c2005001003418600801401078000380e02d8481c0b0310440d00d0241c184d40d105801c103202d01132840340d1011660240400080da100f00d0300038000e50200d1982007481c0e0808518881d007580c0080c3d01c10003100b02004100e001d108140008020072420040f100480c00b120041c00b2512001c02c00e111440c0c0c1054840403c00c00541e400c102c500070100344105005070640d03070580440d9108291409808920714800315000c22001c0e00803205119099225000035516249101117070190390000c0318114000c409003100040c0a000c213070359014a031030780119114000c071720340002c00b003841760898402e543c4080e004112055210645c902940c0068901058164483c074210103240103100e40298403441310b0003040203265042e40314400301c40c0122070501a954140040c000d03288082c003001703501908070b08001555824144c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 731909532 1250 731908282 731908297
    0xf030d020d1e02040602010c0212030105011803060507050a0e0123030a02072118120f020103090818010306050613120c0302060304030c110a0521120c0a20010c0602 72
    0x1e02050209241c070034890b030902e09030ba00d1140c0e5a404501445805d81c2403252180d401d020b030000f0326a80da80899018494001403140038101b040c2c0f00b40d1340d980407400b041014011a48150144840c0c10148005011900181207010000740c00960381c02041d0321600d803951030a5211406003540c200050102c1c8441d60009101203252038082007040001059500810590070b6503502105440c40c650034001c14070200c0c1400c50080c00c160907c24030020400203101c10400f64051401002d1810030302c0182d000d0601190040d0020801044048900903424000c20906100340e0301004403130303218010020540600984252555100d030018405803240e4101b07a82c03003c1c01743c510751803400d5032540011440c0e8000c444c2100080c0890900300100040030941c41e83c900300489062050b24180000b00701d4140d600700801d10041c100c40c40041c01900b081c0080e020030860540310595880000c4410f6554601c0c0e100102d850304100e103c50803490094020810000304142e4400150185503281c06000e50007040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 731910782 1250 731909532 731909557
    0xf06020a2a201009080706090e070c050c060c011b020d020c010507050106050a15120203131203090501050114150c1f02041e030212011406041a0d0b0103140f030d02 72
    0x41034400b02d969892400000d102e10307648840c9024140f041c0c190500c1d80e01d502c100c0902c603490340180a41c03c8280d4100750311030282d01d0014624455418001d00d00a0305038032498001e14000744c0c2150840045d0013040c4110166045480300d262100400c81e03803034145061001c010381220183c0989988198018224103008800100782980c561000912010080e4007a07007548200884803000150403070310000c0311241c0d00d0421070451600c2060030000a0001000601a10580590015080c060f42c0a135a40b1508800200070135170b1036100c81d04480300000c0d1100e01c1160344200b006400c564800031210341e404007070042e10440007070a842840c403460760650465501c1d024407020a807640002d0342d90b442054420340700c00c00e440c5140144140c031161030b2008415a41080000480048070718852a00720f0016900000c0b04901070017006a100e152812459001d80343c004041d0a0242c91002241681c1c058400c440c99510820f1443c0c0e41d40e0321410442d00503030424010f9070380e0040e803540034003000d00901d07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 731912032 1250 731910782 731910833
    0x4020102101d07090c020d0c03020a02010e040f050f01330f050c01110a0f08100e22080901081e0403030207060b100201060306051311040c020a0f06020a2a 68
    0x4140b01d4200816500100390683c0e0300c04540745265410000d10500854504001602c0c11094030001c1d11030a00e607401078107001740142249604d84036030307202d1445101151010011410161018501300c0380a02c03882c0050b51200d00102a060100521000c107510303080c504014450381600192a214032448540b41402410300a480380102c00780038a10151002c0800107aa5040f400c07000f50420001a0f040e07020060114104250111502e502200303891480040c464103a4686038001101e041100a24820030006000542000365101c00380400503001d0f00d82107501d40c0c5885405c19424140c41e03041404001210104001c62700aa00601c0008c0c007604001c02d0100d489e0700070904942c0f1048030300f40140e550300010005d0082d9441a550012500c2c4240c01d0028025190100b0b86a440000903200b10340e50041015014020010110101d9000f046155040e085d03080c04402034001c240114045030348070003005805020003805a09907500e00f124010f0700c9001d9103403441800780d00100034241d40301c80c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 731913282 1250 731912032 731912081
    0x120b09010b13091b0602061801060803040b04030b0a29010207090c181e05060c190c090b01030b0d03030207033b060702060429130305010509060402010210 68
    0x2000d20010b020180100c0c04600da0000340381c0945805919059401141030603081440310642c0490b48940244030100b407204c1210f0340c5400300c4d00600b60b590120f541444005070000e1403440c2800a40200c030b00400c0b4224203a41d6803610761058952842c50680c1550010005540e42e1014a01e00080d560040c412151003607280c41d6403008460b017513035940d0040380080036440c02d2aa120341045014014030b8071102464080c1c0802d41074a04168050301d440f4030004070300031000314010420440c13400015820100b28144a080a141c40c040c0c03802650541401c094401c0d803254001c1c080c0c00c1c034240c8080c080204014698904030000d410540c0102c1c200044d0081c08806002a20004c446035444602c242a401a50254240441c0085a1924080c0b0307c1130112a0150391000306031412a01e00d500c0600030361050403900b1407456009907070440e0324000802c0c14031180d40342d2080703041034a108000820403501ca5107541c03a51601c1c1150020300580c0061000c94500080b904652482c181240400741c413084e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 731914532 1250 731913282 731913289
    0x80c0609190806070e0f3307060f0905100c021207110d0819090311060a020f0105040302010b011d0a0b0d020904050c18090c0a05250506061009120b09010b 68
    0x2c09039010000269400c445c1c00952806149614080c14202c509030b01940404003280302c1d020018015513020080c0a00040c1300d000e0307960450325071a81c44038040203242520144800100040c50007070f0740380e200d10303500d25480c02aa0320400340b10802c190028030202502c030310f0705c101c030b82e200201c1200c540307009081d40b050b580c86488090b03580760705c90355290361610611040076080e46c0d07400800d40c0c100a0f0122040020405501203680300300307010703240c00d0390382ca890100c140d00d0402d1340c4d034220f003056180c40e08001c00d0650640c04950036a01c2681c03101250720281822003982c0044640c100e5111500d41410803c24025a00405104000000c05400c18020000060407548211048405c20000159590b0a004401a0800e200e0b00c104c84035040e40c2404c0c40e030340005000d900d407031005000700000c80014921035480100e51070f0a402240d1030b5001c4403494910344584064072620b010324581d5942001d1135010b445010180d504088100c0c5c1002c04544802055010141618203655a034803209183e076103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 731915782 1250 731914532 731914543
    0xc0e0306130b011e09181a07030f09030909020a0302040f0815010e2205010e01020f130e130b10050a03050a0303050105010f05070b0c0d05040803160804020d02041505060a0e0a080c06091908 83
    0x1032140b50554081c40c1c03502e000789c203840c1c0e0380781003204080c42d20920000084c0c1081d1038400740c5498190040e245c405100b800e8000384600d400035102c61071070000004003000c00150360400028107080c081803a0360307104a80c092581c1c0a6646a8800c01c000851202644d07c0700025482e05001c0c03000401d840301c90340340c050300b26484464030844004000a02000b0f0000d0140800000d010842850000707140000780c00e072101d001c15100a10300e641e464045240c2c07640f6000c0d184043c1000030600c1c3c0c681940ca00d4038540c1e071340420000710086810140009815801441c0044441d00c441c0c4480341340510369a548003103e0340041515100340001d2040c007160300c08a02c5014401c0b84195801550303800e01c078111034207140d80000b00c0c1003080540c10811005031255911400e041e50b0641d07001c0b9030b0702c00c4a607650f455004c00d60419038000c00003041400c0040d91200e880c11007900705485001259884007121034071080d0002010307070450b008218051060a0003c045000b000701074502000c0c80d9100c400090400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 731917032 1250 731915782 731915813
    0x11502160b0d0e03040b030415110f0d0c30020d0c030e070803040605070f030c12021b151b120a05070c090b03100c0e0306130b011e0918 60
    0x7444045100740392110b02d4440e046034441c4000013907040518002050b0128403008100404102d051240d6545c203c030190002c03180001003040c410780380e0030702c0d010700c4406030803c2c1c1994007441d00304038440e1185409507501000c11644c9106445627004001004200c03018208580d0400550800410250081d244079515913440c0f41c0d5004500f444080328683c1ca0030005d0b0b0800d010640080008100264210040b120103613030101c450110285d0b642405c0c2e40c040704c0300700c010f064218401001440c0c1c0d0b5020540b42c0c0703031403d2040212a10941d0b0b0060100d01c2400180c1c0203100c00c0d0400c41c41c45040c0805650700c0c0030641400c211040741a1406000219400c0180c0d800081a00808c2000403c0500c2140001803d456241000300308ac0800000fa514080d90710500b400319a038000500d81c861254184000c00e180180490306603003841100d0328800c840e0300c0c1c0709940c00404500045209400040202414482a28140380490410008100034a46007500c145202201c60700715000030224900c1d282d10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 731918282 1250 731917032 731917049
    0x6090613051e093301060f110d1701080a0312021318091a060d06050402010531080c1810091a130c050409020d060b121509010e01150216 60
    0x12100244070080504484800c203043c0d209218441d1649410f11095044035958648246501c0d6405401d423501c22500300908214040c846c14180340070340040e0344200c00040d032104860300313a99440c4081d803281c1070540c00030002080031803071000d220201e401400c82072541044049900e50b942c4c4c0c0021101c0320170304402ca0324640f00d156442c203102c0407580c0fa19030000f01d00e54003440c0d86000d10000f070b1201d91517100280686d55600114081da40b044003070b2030404440201c4c2005070200c001e140000e1110700c10200741c404000150200344007001180a003801100a0021460b12840b040d160154000007000f1042032200c6802c001413003040c6000d40081214500109c0c030106450000f80080d100c44144540400c605100c004860a0f5010301124110f820b03002005803240c1c450010940a09190b6100321140640071950600034021124503a0203800c0c211460110885032105100141c64244030740ca01d004030010042041d1040c0d1280d130f1000307001e5441aa900400c0c170003000d20021010b038208405 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 731919532 1250 731918282 731918293
    0x70f020106090c08041221021201090b060702060f0f03070c03030506031c0e1c0c0509010e100605160f030206060319150c020708010507020d030506090613051e09 71
    0x41160288038560240c2180307607040c000c0c0309400902401100c0c015100501040304030b803c50b400305218080b5400f000345203002c3e2105040300d286052019402c0801280b0b100c500c00030001451010350700c55801441c1000d404141040c002e82c0030002e07e60006a029484100c041044181c0d4a6945000354844e54454440510b52041410010200c0b00d000740007500a600801c5401c507010000e103d900c0d0a030b80b15103090030510008402064089070a9981000049a201e00c450100b0031840c00b01410346009035806c02d40d981e660241c01244500a4680140808803d03009000c280d00c00c00c01811a921626001c4910500360b07034481e24216401001940140c1109041c402c0510781400b0542c01682c410052505a19003912141808110710500d0b903005940d50a41c101d03c0c900900c0500000c01c000303002041107151050000c2e40f1441c00f0f80417400041d00c0d10780001c55030320b00a01028080d50b40035100854400807421070034024440900100c00302096802c031501c00c8034805140d9407140300742001030031 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 731920782 1250 731919532 731919557
    0x507060306180c1403070311030c0c12160b040201140c01050a05130305041e05131406041e0b040e01020d02190221030a02071719090b0f0c070e07 64
    0x140940e050b00c80c1c21000c0343c100016041e000f0381c004500100d03145003072002585d91b11001c909400400011002900f414004020803544510800180a0220450059500011150444c1c0360b142c401c401d844c210a85810a800c4082035002c1e5400d540b0a1041c1000300941d000030404003d00d42080803d080981e4642080040308a4035018054001408005142c0002d51690b03000e8803600450140da04194003040281810840c0740004600504010344020070b80d600a04829001c1c04a00b040356015101803c041000c9003072910441104500d0485c0446502c60b6000b820300c040d01202d2800b0741c1c40741c3c849440c3c00d003000303081c40280716400705003000580d83c04100c1c078a4074203c0344007400c1c902550400340d800020111046c80e03210349131a454400c60360f242e603122011002406410005060074a032511444500c3c003038000144020001c82041d03100d00c402c030840171203071000e16018005403206e042c4100a440304554002c1d0608202280581cad41c1700c0d85845984101050031035110b4001100a003148 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 731922032 1250 731920782 731920799
    0x5090f010e060c040e0a060b03070c0512040501081501020f01020406170f0c0f031306140402190f05060d090b040308011818080702041506020c040c0203040e04080a0c0507060306 78
    0x10800141c4a202401c200e01d01112a514140aa4070440000c2202500015451402035000d60003800c060b500fa9512414017803c02000700040c06070444940c40349100005204c14100180c0b003c80c4c1c1c0507582e106465807034640d89008240348510311410f40c0b10709450f400a000d028005800a82101d0fa03450302e030719244004110300b000005d030868109031180004d108825440000325110300c119540e1003a035980b44c070301c000c00d941e0320440c102525903854010b0540410141c2440c0e42c0c0550f0084540e5504e030003059403c280d048041d4170400c481000b40030810415820f1000140025000680002806480548400c00811422902100090b200742c0044c0103034680598003040000d00e00700d041044d08040c0203400242d404401000d003d800c004100d140440d521600300640601440c0c4001035140d41d03c40d4042d503203004030103c080c4994200821442458800015a01119070400500c0d505803500e4581c61900d901c00b03940307402004440c0307e4180102e03100b086424000c00c4950750014a1900e0b15142 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 731923282 1250 731922032 731922041
    0x60703030e12130f081002072a0510031802010305070c020306010f0504050c0f090405100b21130f080703051e0706061a0d050903090a0b070b07110303010b0304080d05090f01 76
    0x2080c840138070a0a020403400012001490742c841304005070f5515103070502650a034a032715150700c60608400a01c00b40081404090411910181c0303440011020001017075080c2c0300111614100554003681441c0903602c84c1e00800d2700308410303040020781c80131070b90040303420600f09070001d00300000e0924013008142401e200d96a8825281114107041c83c04400106480b0711a9049491240d42c81c2e030701050720304403031300e0b541c00003890060380c01e1b90b0b541900500c0c0c0c0418a10303409000f90201d03403580090741a413070703006140341240d5100d201451940180d42d11455aa04005000d408101d418000b06589205010b15490104140050345803200321605d0000c003070f110203421142400c60300140b45c1e804c0245030000c0c0c40758042d0340328011070242e03103010f042c528501503008a00e5006401d07820004d1055070f11402030071201e00404143ca069a61010700303440c200724502704801c3c180c0c000c00040000003a2040610b23001441017181c14030707142c0c070360100405480d0203560914031078102c00408860704030240704 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 731924532 1250 731923282 731923289
    0x1b030e03060c0702010c120504050402040306090c09051b0f0d0e15060414060103050a0e12040303030f0e0703140c03060c04080d0f050415030608010f0518120306060703030e1213 78
    0x200340d0f03c0c1040035800288048008000206140c1a80f0740c02c5a0003406041520040c00000d442103403941d40c0c03803e0a4018207a031703280036600c0c0c00c50450086569281c1d40038480c0303e19140f140401c1c9030480b04c03801e15041c8e4041180d003408442d043c0201d80d42904280150440c903c000d80080607440785031140c00c0425000581010f100e40d10340b070603a019242031420a513078421024200002c55590b038901c201c020702160032140c4000c2c055500c1d680c411001038009003095074080e40d01004100322000502c2c0c04c40b581042102c5840e80580020800109407140407603c400c1480151094108100042460101c00ba251800492030101d401d006001080000040f014114600500b42e03a1021101034175510540c003420107160468085d482015009421000c01498080c000b00725182152608000801064600012249038244480d001440028014110320b0300c0000d1949180c42e05410000755501205084042c181c503504580c503000d5090000c44100310192a0b425682c0303000c0442c0000e80703201d942 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 731925782 1250 731924532 731924551
    0x90c080c1201021c050402030a060c0906020c0a0b07111f02070923040b06040e030c030901020c01080708012702070b0907060f050924071401060905060d121b030e0306 73
    0x441e01300300355084036110307204141c000c000207100c3c1c0b00ca001082c1410a180e070302400352030402c03d01403d050b600008010490300b0320340c280c031030511480d000c01c2441704441c812104110801d1104401082d4010700c6440c2c0c0b40e000418510014001d025050341c0240840351000261300702c0d00080169400c207004904404031900c0140900d01c0c910704140c16840c6024001408403592900007d4894030ad55010380d899413030103021030f501c441e0b040c45c11139501d90002d66014014003501c810038a480d4014911180505051b03282d64200307a00b09500c020b05032075007500c620780c4004500d1048128150b944020031015018080d440013502d0720703001d124a041e8466100500304900c0440202c0240e510006546280500711684000c0f15911101e02e000000c2501844500325030025003601040009500c040807001c0030f0009000d01e80d51503404da422110210ba0359034104d203600302c06c440003c81180761680d0705005030606000c01543c400c624820302010a500b280455101d80200c0300504d001c0211907030200600 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 731927032 1250 731925782 731925787
    0x1090c050409081b0c0607051c03020c070b07030c150506151606090c0503071212031b030b03070b04060e03070e13080705150a02030109050604060506090112090c080c120102 76
    0x40d56600ca240c42080484113804441498140d0756101c14800e01c000460700520454548456081081e203a60044550486081c500703111074802d18028020717034030300310707041e4000d040032038500042e010039588043c074200c0c104211401c0310310016140b01400c2c90300d5420004001340900e40b1070140403164803088000b0031518010b00487c40004881c5102600c07840c0d2000c4041158100c6140c00d11160040360085075140c020070f400030804028607803002611502071214006001c60408003581100c1070100036149600e204c0340b4000031540640c0140c4003042d4041d08403400c2c00d84e1140e030130310307180c10581090340003480c0804000200e00d010441c51010b001c420007111540d0802018810030020400402030110300082541030912500f0701880340c50550b0207a031112285800088000250710901408003070070715000c085076943c2828030411050350000742c112032911103644019a104440c8042c100c034070f6030711032900c8400920703103840356070007410450002c008444040c0c0411200c1000061030f8041c60307206 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 731928282 1250 731927032 731927051
    0xf040611150c090a0503060405010221040b010b09010c0b0a06060216050a090905070e0906060111010c08063313060212030406020702010e0315010824180a021201090c0504 75
    0x2240c540c0e5030010004a40346542d900081c01155002138150301043c0d1500403402003009202e0190000d004100220b01d000d40a8030745110001d001c02c40a54001d080e20031204d0041c8031020207540145003442050403d08500c451942d140c1c505058201c6254aa2a4403010100701c0345030100900081c030540040c46607444c07410240880c429010510401c022903440360180b9043c03010a20a0001610711034a01285034038001264940d1051309880090000d4248090416491010721800030100c0d41a9180000d90316282c04101541c09400403003101c5c515440040d14607058621031100c00c01444c440901d448050034061414031031101e91202d000e5401c030400c00791181000350216648180c0c030010068642d10b41d400100d80300035010141c4d80d09072003408650181d4044d0100d083d8102c500390000c0f100498681c403484c8101507072550110144c5040c8038080f8200d88000d9a0b00d044110100086540c11400c43d000901c8402030b440590000b03075900c507002e40a0004102d03d0802a210603a0240006900d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 731929532 1250 731928282 731928313
    0x91806160e0906061903090213050114010f09091401092d0e070b070f0c05060c12030a0e0d1d0907170601090f091e0507090303140d020f040611 63
    0x42520740c0600c00d6402100150060b624038059411601c0004200c28141080c5507014000744001101644952094501e0541c5050b15005090585000001c01c510a0f003155005580c807001ca071400200748200e070280455550300c5407150181c0d560031882a45a82d51600401004440c40c40f4903003804001411010000070f20101e01c0801001a0010000b03681142e6121080c242005a006011a84400140700c0103201c074003144d22004078011240d000b6155502c200b04915403165002540c03460f0881a6100b081511020280d80d00c041e264401080c01c41d80088892300b800c65200000c0045004e03c940c560044090132030003820958144c602100a051403100600030003c180c103034101030041c1c04c0000b103603a40700341c1c0358100505a03121240445501c58180324040e25250042481620303003440d01c4030b40000ea6028850243c0d94a4035020b40f4070b4110f40342161040e032013081030f0414585c1005410700c0c0303185510040034840b0f0180155a00c1c0c81c105403005082c01800031114800c0e504c01c0428940940 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 731930782 1250 731929532 731929547
    0x608040b04031e0f02010c0905031b030a020a173a020c0a030c05040b0105031b03100b1c06050102160e070e030a0b07081f030b0a020909180616 63
    0x940005020846949a280480b00d14102d00f0714440d40499241803a08490b412003510f040c0c05442c0c0d0000e004020712244100c424680c0ba201d002d905610000001c4503000315610601d803050009800d494854403550085060f442480e030045040b420301881072010282c013031011034622241500c00307996507100d112041d04110800080b03611509800066030020500800c55882400400342200c2038080c0d80e41000c500389043c0344034031805603041080c0356400350b204204072440b0b1254005040d002000d410b01c007400640000300603070b0141d005250003251482c0d10754090030b000321821520f0000100c50503171410076551a0b9100c0350540d4007082d100c5280640d0f0301100c07000d84501803900d0320980c0d50700e4011902030b5084c1c00b200380c250041000001c1440203d90181d44104c0320350b200c1d2000d5486d02c1c05c0d5080300c13007020300007103000002003407050000441601d882d94010040d10405410012813100043c0756080682d082802500304800b07883c00d040040c007005511944001401c40e1044ca1031002501c001c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 731932032 1250 731930782 731930791
    0x30f06042a0305060607140f1605010519090518060a06030c1b020109170a06060f05010504180b1e1005090f09060a080610090612020a050d02010309120903030305060301060608 77
    0x580f500000751070f030303252501900c0410381c00c9034400c0c111042c0c60741169107510316109048031038040c5421031400701042800500484006a40f8149040401d158040020384030039010010403500b1100051950380d01600b0101c0806600218803e41c00c1c61401c0022082d040d60048091605003100110b145401c40044d107018400c1c50040595001e140c40129100091038100720701c086070410980c02202000100740c4991480b4803820481181c070b40070883e02c814418840d050002318200801c1c400c0e410110201c1c003040c2032002c0f01081088190000584d0020168150181e004080700708003840c0c940440b504c03c2c007032658104940707440f5050000c0780038110704214507406800150040340180d141d84141350020b14060003074401c10b0a10800c1c1c489400b01c144207503400c0d107061490125002101c141c6100056600900703207202c40c0d2600f414051141c00b500c206034107045e41c842200000c2501c5010540a50109540340d0301c03464203511b005011140080e00701d074000da03d844000d0000d20b42101c00d16401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 731933282 1250 731932032 731932037
    0xf060306050117150d0602030c0d06120209010b130f120b130305030612030d09061b180303080603100c080603100605060403080c030d02070303060311030610090f02040902030f06042a 80
    0x400f00038010070301724040108014201071000040000120043e00644004c80741a203003400029074811445001c1a00ca003006580702c4040f4004105440307010009240c01c1000d0b13402009490b550b90464107070400795a002ca405008510083c208000001071415800740502e0003031407280400f80c80040040c000144900e000b8400740d4a031041140040050b52201a6054024400c080d084c0c80c2500252011081900031000c0e03e0401c810103e01030b49649000709442c0408405452454400301c0d0034640162140ea0940505022051510004c0c0218402e503c0181c0f1204000d0a140050621b800794201030744904914141081c0280d0b66a0011101265088020300303480301e000c003e016007503218a00e0241c1440f880003544c501003641541010b003c990041c01e0044419160f41c05241d201d0340c0c00ca814055000c1908001e010552442d400340c912030300524001414192a801300d401260700568000040d14003050070084c1f00e01e4507000d01030f04200c0b41e000d4440e0070b103000c20a841e2601c550700100e030203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 731934532 1250 731933282 731933311
    0x5030f01050f06090301181b030503180414040507080f071a030c0909101a0a051e0c16051c02010503010308030c12040b15030d0c020d0213060f060306050117 69
    0x5552042c0c244d403000e00c070003030003000002000d080c0000000310700d1900b2188424400c031440c43d0503001031812000c50b600403000c0e500e094107020704031104804840e80a68400c0e685d54150300d540040c040054411803040008182990800c042545017102000d2005e030594409503092002d450717509440078001c00c0c00e03500580ca07601e907014412403500503140025080004030342008840b2075490740100407105245d0131160444000303c2515a40d10840f200c80010803002c010480700205280c681d1030f100448000c246040c400346002207030a2904e4440b040716a14680041070189203400c45800d140c071428810000c6600b2001d5002078442d0205200284c0320440100004070f08008801c00c48103062503419802c122440c20741307020680c018056a00e01c0b00c0c0b00c0c509200740b00500300054600c1a802043d180c54100d501240d0821650300d11030035080b80c02002c100d68000a10f001030042c400900030442d9031920107810000700904940d100d41c0118108120b09070106141f81000110581148141d0080d11 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 731935782 1250 731934532 731934559
    0x3080304050309131e0f330902070c0510230a110307020907050313060c030509060f0417090409050a050f120406080708070c0c06091a04182f0904050705030f0105 71
    0x800500100341d447c0244440b101c010004150418a0300005040561171080d03c2d03034480c51808100d00603500020400300890340d00740842c1c681002e40d500008040e2410703a01c0559110005400680c014012407070101021070744038816a0001e40303a08007200024021400d05a00c1e0f000240300280182c0030005000d000404168042806030144003d40d80204c4103002000352000c0003002030500702c80d12a1180034038408680340e16040c0b41e416000d02d820100401e28030803030f619107100507030100e200594410760350b0211400003607044c002e44d0036041c040c502806103824110189810310b20000c03c2d0b01c10502d001c10003030100700d4001d2000e03030300000c4614000300542d503016000d0f5004a81010701500751030481e580042c0381a0f018540c14180e5190326107489407080340c9100e4a0703c600690040351107006000075418404039982c1e01070601500a403000080c1948801c04082149107920b61080e5803010000d00143c80b42418000c15400000d241f4105e443c528003501010910030040c002d0f107200b1403171022000e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 731937032 1250 731935782 731935811
    0xf0f0b04020c032d0f030403031b020a02060f1b0601090605180a05191d0c1203071106120901090204110301080604030e060d0c0e040c020d1d0a03080304050309131e 72
    0x1d4001114540c13035955a20000342c420741a001100c0880000c2d05007180c020000c43d903550103070a40305050700185401a4a41d00f000000c1e00014820300401c402400741040301d8074520100c43e00d034200900130704559414104050107403109a041140a05068460f042c0702c50041c3c04540d034440410000001c2075110200384008589010003103402c818101070540440982c1c061402409501120440e5040c2d1203080611a07500c04007032003c079464009010180c049880070340c0080c0381080052030036281a20780030b11880002400c0d941c00303101e80c0d5118002411030505104035020000446180d5040d50314010305a5a038180003000202000341e0041e02c50004d4441384243c43c41c07408146001d008010b01c1d13220041c216408071300420300c03ca0a08502600700303800403a01c0d000542c0681e56072994030341c5802030000b454050b038100c20b0708545070b90800000f050010002e1401a40700fa40955901c003001404c000c2c000751550b40601c0a94030381104081c07000032880c184107000d01c00142c04a0050f00c00e1004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 731938282 1250 731937032 731937097
    0x8060403050f0a03061a030f01060f02030417070b0406090e0f040c05010e041d010903120504210e09010f030303140c030a2a08040215030f1302130f0f0b04020c03 71
    0x39051b80000000c46140414010040c0d4842c5c032401c0140e80051781c1c0c0ea2002c654a101c1c00ca40c000168100304410300090342007162280d410003402089601665686075101c4840c6d1203584400001204a001400013000c03c007011a00010036010500450401d03456030030001c549071288034103200c03503030081054685881d08020048002880301d01c0600c003071626614081d20607581c00320300090245895218a10741486074a00454000091400002404148500d03481101076510248245440356000b940c0d100d000507030190141000f01c0440602d5850302130b0603144044003106100003000200032181d10030400340c0e50710240852000ca01c007503100c15040c043c01e10031103104e000d02034901d0000e270300e00d0340000005015501c01d8072843c107035001050040c1c080c4c0c0000c0d2950700252040d03401154610005120003101180002d204d41040d078828403505080310034140c0c4290b200380d228500e04e00c0d041c030740b4400c3c0d00d001e107c10341d0b06615120703d00d4505502c0380b04800742c0c0100c1c000c1d00760910780000c100000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 731939532 1250 731938282 731938289
    0x2060417011e0b0109051f0e0d17041503200f1b0d02060c0a09060819020a020a14120403080d1503080309011515030e100c0507060608060403050f0a0306 67
    0x1c0802d070410400741c0c04025114200d40c260210b0b2072000300240c142880c10703220b0745045211071420384856640300d04642c1131150b2504590b1040c9074510040c0130401e492000d0f500d604031909a15591850000c1c0c3c041c0412040b00400e043c10320300a0900c0c0b849000040201e000f15004541380e94a440f0086c2c0f9001c0c90003100f10740c25080114401b214041c040025682c4c03510807407502112400e80d100c58811000c1c0c4560b00b4072400058100a00300b04030303800391203107540000042d14003101d001500d00002c8220f82040200c0c40050303004040c56000c2c0412400c0400b042c803000809840280e0150b0070101140c8224840200125000203600c01e40010b40e80c000030228202c5c0c5000c81102c1d60720b003801c0d50642c00581d0403032500c1d4a007600c2003040300c1c1500485821101e0542007040c4919003070906400418403101d03100d00c0380c0200300c40c50103100094400c41c0c2c4401d44513100e294550a040c20040c00325403058120300c40fa41e115105000c08030b90442d059900540c1403641082c0c2d02c9906210031006040543d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 731940782 1250 731939532 731939561
    0x804150f021c0b04050105130b150d091a010815060f03070e070311042102011206060203210702191e06021902011b030b1c05031306020a0206041701 65
    0xe022440d6000c038851403440b04035061014014002d0311001c2100711113083c81081c0d400381000140da40707000140d800500c1c4008005005a0302e4821701008500345501022018441780d6481c1400c1e001c2000d05030004c05810f41009111001d5818044cd09690b483c141805100160f150f400280b003659a0f5881000c0008000e425904090303075590b407152800384140c40b0390300842c1c04c2403100d040c01c2c15044181c4088410004111404003000f400c1d603101507481420503810000ea4448400e041c20441c001e034001000240d00461791040b0a60003420310150a03003458150510310014058069800941d050000e0b00103c100710841c0c0180c81c0800300200180c070301d5880740c10900041e0050251039030141219400d45201d1014010700c0081c201c0c2240c2e40800421000d80088004c2d221843c800d034014944010041e056078505051186004201070402404445a91001900d04415811884c2100c010a0307640003c0100c0000c0764002555030240e402004a040c4181c0540441e01000750883d00c05000d081 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 731942032 1250 731940782 731940787
    0x307020d03050c060106050f1812010e0624030a12020f0609010504031706010c151119090602060f070503041515030201020705062d27031504030804150f02 68
    0x24035020b4900e0304290803644042c0950070002400501501c22211500e03804254645445180f0b003004820302c40410b61550031000c2d000328083c51600900c501d50f81082110010300d002d2a003543e224a10060300e2a0744400b070310400744103190940740000e00340c0f00664455003a00401403883c0f0200d00c4e0002007007014000b8850700b0140290350406500c00c5005602070303603c034000005203000d501d44034071064a0090000303442d50180d0f00807428820b4480890035140d00302144400381142e6285141c0c20180d21201104440c16003081d0f0184c000b40048000c1070280041c0074117143c02941c036010036a000305024140700000000400f08008000e00c40b0000e0035180f0108190308030500007a800140c02e0000702d0240c441c41101003107508c1d02cac100341c42450341d813040f10030341c8400451040c1c15064140b5894881b141424420040f140341081e21902100744030303050f20f030018598882014a0894003112120401415109210100f81d2252030581e0042d00140c4240c501c0ea90300305078500502400d081c075510140b01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 731943282 1250 731942032 731942059
    0x8040b0c0102210f01050105120604110c070b181008010909030c0b15100e10030906060b030117060705070b2a04080a0308090c010e10050409021c0f14070c05030702 72
    0x560f203141c00340101c40d05044503a81c0300c0005440900c2558207042281440d071000641c81c3c03506400001680507201071081c208903030b52141501c4e003100342e040010b8503100031550a1640e403110350034040112044810007041e00f4100c0000d0842e00d018060303230103442d807108003640505010f400200d0303440358003401c81601c51506034400040c1440b41d1307039614410941100c2c1162054070841c03507441d048600800066000c1c000300403e5004150007a401c40e13007580c0350300f400a15510500f01540c000c1600d002c071551641c00e0341210340d08154000b441002440014030400010820300d400c208e9100140e030324918114803040345003000c0c0800c01a10800010f07000180403900307441c040380403080706100352a003100a03107580c120946c880c2e86541d800c82c006414044c038a8014901000c454480100701d09065140544130201c060681c0d000d81c80c0b40c09143e003415000070032415148161100200400c00410140101302891001a032020b44a5020004440766900900900b403085032181c590041550562042 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 731944532 1250 731943282 731943337
    0x181303090503031b1b1e1305070801030203071e05011d03060108010f1a300708031c15090e0106080a0c061b0302070918122102040308040b0c0102 64
    0x15513180344007907030117880e00c05010003e180c20501c5214500405440c1c0090101803110305081449420a50000f0600922410b10401d4070606024600701d980707980d401d6045005051404000e940000a124540c1c20f110f40c40491b000b40b0341c0250b4109181200425a005401d01c05120041c00150740c14003500b400050412015070040203102100c850502a030600e4507444691118500c031003d800c105030400c606100034a400116040c0002c654081c68980c03031441d800c030f10308801c5410011640e8800205041e02d6588101d02c01c15040070407805010610313042260b000410703070301e03c02e0801890b1a0a1145003a500c00e41190000c1e0803032008490040c421400d00081003d20303481058085170014508443e07180343c0300190701c407158168004085051924503444010813483c508a00c00171117030200d450010b0800d540c14035044005684881e54212408030f01003e17411444605800c10344104810000030f0002000d803030845000319071154aa000c80316045000e8410704401c141684129444583c134000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 731945782 1250 731944532 731944567
    0xd05150a03151d1b150703021f0207140d0305010e0c09011103090409061a090f040311280b0c03150114040e0906090d051201031124040501030b18130309050303 70
    0x800325800300d04d85c480d0f5000c0910521a69601a005030001001d507050741c00c0142003082c60111415005150080e10307150040c0e00380f5883c80b08103070754110240c0d14070b0882d4140907550161100070700c100d496003043d084c0b41c04948a42c5000034184a080c0a031030707603081c900b80301ba00d0f401c5402800034010318140e031800070b008000c42d208603a4010407a0b000d080c0350341411504284141201803d620300c0c1d45942d202940d0110032422114528498854642c00d007840c440707505040402c2c1c0d8801e14507849240d2401000d0280010310020109000780104040c4007000100d000382144c0c2820a203030303603610081ca40304151240e034001d80480c6410030144060003e001449034801d51905082d50300014180b00120b07810700c2a02203c0c690124441d0050020400103116000c900c0d20081100d0169041c070001000d076044145c842140084001ca0104484d507014018140400c900301e0b136042d035181c403290000108000162944014030448001d000415001d041e40402620000f01100d488198060003c001702c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 731947032 1250 731945782 731945833
    0x3081306060602211201120f1a07260c0a02190c0302120a11090910050c040504180b04060c051b01020901090b030421030b060d05150a03151d 62
    0x1441180344969940c0503007003a030360403010350050441d05d646811500d401c140b1080e0000d607800c0110102080c0045e80809895003100005080c0d0081e81c9014600908080e1040e01500041041440b038015903410300d24441d6400a11109919142d400c411022450714003414004191117041c82006800d000f510044582181d108480c442c00041c60311400e40c0e2143c155840044c960310100c5424913880c604000c070301c0d0340710181004a9207840c20404810302036407010b4803012940c06002a0501103400c060240501481c0ca1134004903000c4410783d11420004c40041c00540116590601500601d20a10856040c0140280400c42012810200718000d40c00700c1d00e134501141c4016400a40c41e55003070b0689218541050902d580e00e00c0039040c0b54410403407031030080c040540c0e0b03400c40c149a680c1e101c00740c8081c009805000480f4a40b0001c07011156001d910502d20503503400c542040016486d90310b0300018139055402080e581001450b4810094102004014a0141624561050013201501d0119 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 731948282 1250 731947032 731947063
    0x31e070203010e0d020a0303091712090c041806200d0f0f0e0a060b21060a0b01020a120c0f061406090105150a0c020a090c0903050c0303120403081306060602 69
    0xf150024100f880d500c5603200080000340c0c005402c6c0c08003084c040d03401140201d00820165221070221020400d00c1d41c411402c8141e100400002d00206004c1003051404c58482a9010454224248800c14140d103060100802041d21307901c0741309580c81a0304d00141d0f1000c540c400d6549801c1804503070b030302a0030030000810000349403000f2406900038a00400e003090008002801781d880f4507407070340c501900c401e1014035004070f005003a03981440440d65101214940090281c00d6500740302e03691034107840a000010781154050541c2c240800c0c40800c5003070391601d8605107012040c0c9280340a04603010b0404000c0d00c50f5190a0900c40c046096151442c0724010466102c1207581c0c0300d4040100804c0045041c0b804001c040c8010b10981e405030700076040c070798002848482442d0769444900c0c2900c40070000280001c0449004008124041180c1403805200b100910305014040e810010380c410001c0c030150030009c94a0100d00042d011500543d034550b00f25005002882c0c40c2c00b006540c1c1c01c2c2d01002d1f00d01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 731949532 1250 731948282 731948291
    0x18300c030f1a06090a1a030709020405120303070806060c0c03120301240f0e24040510031109040218042c1b040c1719140f04060c02031e07020301 64
    0x3002d040035800358401d03c00209010185d840f0411850001c01641d4409071198414581c049400e070703020003a980c010000040c01580d51400c00301400282420100038a000342e01c140b042c8200c1c20b4000300310550112040e90225200c4003d02145890801c0003004241c0500540e020710000100e20001107060f83d0541100218000c440803101c4101102c40502e18000f4820404492030107118403a080c0031060020407040060980118081e03407036407403800000003a00001800c0215003016150b2540c0d8070501d040c10000c010104421404921806e07402c20f00c07941c0c0c0024442c0c5401d4a84561242461021f44200803d9481000050300c807540030791003200400819045400b81100000e940c0e503000d00141d40d00c0b019400c01820702029154104800060000c01c2660b519641101c203041441004c0c4580c4420822680007403580886d81c1007180381c0c1e0a01c0c0840c04001d0b195403122081508650300000014803444250801c90070341c003c900750410303d060601c1d501a000000b40003d0100c03680210002c11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 731950782 1250 731949532 731949563
    0x2070812090f1513021908060c3103060f0b12011802040b0303040b0d0501050f010912030c031b08090405360a081918300c030f 56
    0x2e0390b40c1e220540c004860303801104000c198018195510360044071404c074510401c1d03d2580006c8003400784035180c80b007229111404200d00402008415080710700c0036040d03032810300c0101101042e10012265281d8046a103107222088041c4040400c0c0155040401040340401c500042c0000c1d00f0028500ca204011f081e464541110040c880d40c020000d60b110f038a005901107600b03210142c940c104006605000a010001702121104010b1400309401e03000019158106030421000144c0e800c015410001c1070300b42484040c0c000700d14110403c0d01420b00c0c1d0000d07040e41c1742c1214814a00c540b2440d600209100c90000c0100c103101501c10358108403408c0c0000e6a0b030002c06062a41401c80d0522103030a002400c0748502c00059160f219585260140d8000c0421511403401ca43e01401c810303c6a803401050000400754450504094040c402e1882220380d841c0a105002c4114a99120303110800d985540f000e01030b0002d406001c0c00750707120494602c180d1f60390400c0001e041802a083e61054540c00c1d600 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 731952032 1250 731950782 731950801
    0x1050901050c0409050a06030503030709090e160e102402061803040e0c12070c0203060a06150f0306051e011701030308012312031e04050604090905030d02070812 71
    0x45100c2c03044100007034101880c104140000e42400b80404041c03c1d41c0384804001300350280f0080d07100e02c80315103501070640d00e4840d03520300319001c10381c89100c90380020440b40b949984802400381110030401c41a13144c0d444602d0341003814038030759104014560000d19000301da0012200d4001070072240f60240d41161f0754803d00c08040c614200c0c54280c27550401c100501141e0207140c0308941000d50301410905005026070007140c01d24040e244200030610b49002101185003c1080c594000b80c046402d01181e4601a2018400000c00503a423040c0001920000b40e0301c0c0c801da02500c002d02001b03000301c030340a2210039003640c903103110151240012040c846140442402140d00c904a90b85583c400441e68602030000f0800740030300079410501c400d420100b440d0f6644c0c401001c0c02603541c140c0503542c2c40c3d20440c91501c01ea444080700050702ca9003800200500d9403104203580c1107800b01140031503985203501c0e10703e003180308d01a840f8428910200309a810301603a04090140448114005d00503500c500000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 731953282 1250 731952032 731952041
    0x10f0602120310060507232b020715260a0b010c030912060b0d231b120102130905060f0409052d0d11071203091211060a050c01050901 59
    0x500080c800e11150410401e4400c40081424074014031111465406a161a0806202070840b44090b50300c00d00d15142c3d03258030f40c0c00e00b64542d0440610610210088c10000c2d4849140780700342d8207420084a100354000c1c0c090280c0d006045250482d08010700b8105450000d4150309030b0b513192049140034030082071940100c10001c541d6401d900c80c494610f01c1c10030b440142841c109011903d0648480001d45076803280401d400240340300b80c40541d21010701100300c1d2041d056110a80516501c00c404004072644103001244c00c0032415528810030602e544400c5001e8861490080c43c81031502e08002a40c02c4594440c0d405000704440080d056207581c40ac00c002c0d1001d10102501a400a80a5000c8500359403070307071010028148903103022080c03214030060504c900a900f44000caa01c40c41d94160500c070901c903020207130a014004030104a100e4070010181c20842c01030580450381d021000341401070002120001100003400715a5400c900400108150014101490190300304004128000018001c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 731954532 1250 731953282 731953291
    0x3030a20060c030f072a050105070311180d120c050c09010605030f09100509030d0e0109030507032001050103030903052109040c030b0a030c080d050306010206040f02011106010f06021203 82
    0x312a41161540d00c44d51403416009880d02007440700c4100c1126562000000691942e407030302c0c50030241b1414500703069081d150020003110815242411803442151940c060b99071151164000200c0080444041925a501028064514140e00304100c400950001c450220300c1c1c8200155440030b40344600340060352000380079850100b0740038000184c001903002c103240c3c1d0145005040312a84041c00300b940c070482d2070a49000340e40b41c000084e0b02c02d0000c1c0501640501c620514020012188183c40c024420f003d54103005040000b1f00b204101c20300d2040710881003e5011070020821541d4038034000c1c0c0312201e20303c000c41c3d56006a01d2180300c99002041120460aa01d10f40580340c030012104010081690034041c0c0e0503d60f65404900603030320350865030b10185100348017a104030380c24100c1c2185480140c7c11500200001003003001030310399010940540280d4428881d0b5541211440166490301c600700f00403440e8840d52000159000480f001181201c40e00d40984a072542a861203a80e284011103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 731955782 1250 731954532 731954551
    0x12060124090611030706050405010c030c021b04020a1e0203091513060f1701150207170703020f060d1802210a0b0711060c040f14130f0b03030a2006 65
    0x801255000700fa08100024503901a24038052007951070300c00315030080c0c07808c1c1c420b6951004e0141c841e980610514445011030700007440b82124031612402038241c0d000340c0c6401541c022034003800c514013034030f012592080b08001101c1180d0919a00a69035004a40200d03c98207100131f502905d00814001c40307042880045624034074905214041d5505448500c660b02004100c0759000901500100d125007e000c46600c0401c0c0c128030024003d01c4c1c05090340011001c2029500300750b0781600001084001c403036041c4d840c0080791405400107015070040380f1020724050b040c03013065190030b6a500e024080c0c442c030803500f05c2c0026180c501001984814812154422340c0700711020f00124500402041d8400c2d00ea1a080d40d810407820701d0a0300f864015601c000c4c101c003011800b40100100b00840c9400360100c124841840c5241400180d2140c066600300760000da40c400c0b90030051038854000040320b11010b8116941c0340c00e0a1802000466081e4511403030100460011300c82241c08207125001c0d83d07071607 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 731957032 1250 731955782 731955797
    0x21003180b040512070b010f06141b07030804062001063c060c140c360c04080f0a080714070807030c1d040203190c0512060124 56
    0x199100001c10001030019192403041c440700c0307101012014000c050b00d41c811035030010154035121840f400e02c14a03030096000e00c031502c0301c2d070322031810680142c400e40b8011100d28051025050091418055941c201401d0410300240100d041345e00a00c0da002d020708002c141211741d0350040103c07030894075180154500c1000c1c1d0b0310f80281c070b9032021400020080380e4201880004003a03002e8101c2c181e0140c0d12100100b01024101c03414080d02c2007102c100000c022020b400c1004c031000028030103409a002c90790102009980c0500c40740c08110703154070409003480315180035003043c1001c00780c1074216104003401c034480c0565120451101003043c61156502c00d44441c14030405030341e181c0000b4982000380341903121740d800001d0690410081840290b00410000503003508143e80b054414414001c0c2004c000d1240d010301c001a01c3c00145941c45003c1d06010001c107810510780310300280140c0d40030b40d070710802e0640034140035074002c81c1c881e04a8112003080d000501c0c90b011120008800b0010388400314007070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 731958282 1250 731957032 731957081
    0x90a02091506090d1a0901090b1602011b03020405040b0102010608030901200a030806040e0a0f141501030c060206091207080d020c010e0a03021b0603161103070b04021003 75
    0x400040d07901c01e20340100038904051020000c644881c41c9a00d09071032683ea502c121681c441059100030750040c03c014024841c104068855581c1e03400c000d0841c0c01d440c0c040d0138420420703502c00c1d030029000591882e0001102070020600901a41140c05814452807074107503154001c0d80140320701c400315010040518105a080030055400d00316540c0003070210a40003100c480c0c004824003640311039602c26215500c6d00d090600512080303828465407500380346e1080580c0300100c0c1400c141444110b900140c4924815003421100c0d0801d034003c516080c6503904c11002004100801d4803545c180da190b039003124901c0e136a0000003070b034400403841c1245a4240400410000c15035090040945042001001d4901180316070b0403421150f00d01104070580c0c00c40c081d0002010350612010001040d613100e02c06407481c00c0b01c0001e046d884050f0000154842d8078889818032409004881e01c8881400b050300d480b107000b8100000c074680d040b02d04a10030314020456031a080c2c003c0c4200090b405c0314610071004089c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 731959532 1250 731958282 731958301
    0xc06060909340e0a02070c0f0b09040f020c150415050f1504110a030902120303011809020d0f0f06050a02180105131802070c0803160b07090e0c0a08090a0209 69
    0xe046903180880d410ba41000c15401d802c1440d840c0581c22007000160b5076403443c100310b41c0b000c4407a0040a01003540b010101310004c03041055440803401220001100c40f0540ca100000303110340310300803001303018444404100e0108034020303d1241d0701940340301f02c2d02c07030180d503032031040700c00c201c4520f01f241e41b050021401032485c22041d07800c0c1082c050070000b02500c4d0310001280760f8002071001d0000940b5000c0313400460a01c038001c000c40480440042d81194101809540c0110005000440c1181d40300c250106640e11901c401c0039180d04803100407984034082c102840e2902c04020151406418030012a06a01c000d100301d40d960640b07003640202d540d0204004441c80c0c2e00400700e101c030100b401c1030003041132800044010180300d040100160f9450044c41c0011150310300e0351141c003181e0001d208002070700c038040b040c203041ca941c03101c1400d0844c1d80310300003903c5800c42074120b100000c000303c0030000800d020000600c6501200c1d00e0fa10207581e40c4640c583d9a075a450b40c2c0094000e420400170409004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 731960782 1250 731959532 731959603
    0x50421020918030c1f0f0501030b060103090213020a030b0307060c020a03030c050c090c0a1d0d060b0a08010e01050103210918061e03021c050312060f060c06060909 72
    0x125401c0982c0e24201c2c00c1d0708824030307111081c4400141044005405c01644c00c0600c00c4481102c0403035424040c56245880e04e201d00c0704018441814141c90360200e10841d9101c10210b2600021042c0031900c07961f210400400602c18448464021b02c1080000305525010b034021048166004043e4079803d0300f940c1d001c66103003090039001c4030720348119070341e04d880c039a40d03d094184100209130003107440e44201d0700700403c50703500152600c0e034600c3d085141300c80070b454070311020300a107030480c0010500802d10004078079080500e6006604552071320380d1680403800b0640105040701d0040c2003102408446800c201138003000b00782100301107040d46d90200030120101100c00c1141614a034002a807540d90903140c2c0042d02c07100c500500d02c049011082c0300f1850514412131031100200c500516544d1203554140e6244203414038ac2c220029079400080715541e580c0d91480c1d03501005080071b901c0741245840903644040a076616440352004070700050100c1d000045d400011002200056074080f4046600031151 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 731962032 1250 731960782 731960821
    0x503072405040e0f060907111e03090d030908010f06050916091a030f16091e03020406030b0a11090307060e0f10020d082203031503120504210209 64
    0x1828000058548803e010f0544140c010007014041860300008002072210010070031028040c100d180398103540030005600d5903104060302e0402030440c0f4401c100349103014060505900c80d4003250854101030744103d100c1c4c120b5403110024800003a0002e00c603c10794507180100d60704001000000340030520740600c41040140349060803074055885500e91980181200e030b20003890000002440128852000080da00a4072801d520b14032400d185030080c14107942d40b05d008158020000300c000c2c41a4548100c4c0e00840e4010810450690740e45404400c0398411108001040e28150044004c7d282c050111544081c00401a203041818000b00342c822144113000305400c1500c50940c20044d480700501503000ca506074000f4008070040c00401407001038000c0042c00c1da0341d21140301c0e41107500d00a00b00c42e1050780c10308010918140203011064101440e500182800f81c0f1600c042c81401d401000500c142c036880342a0f265001c0035141900705424035180001e402441c0302c40010514841c80c0f0b410100e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 731963282 1250 731962032 731962037
    0x180b0d0816020406170a031d010c03050c030c01061205060604060e01150c0b0708100614120705130b040810050603030a262403010c0e0402030912040b07060605030724 73
    0xc2e281c0328580b4018103601c5e000c1c1007240354004101c000030b054000076142584000041a400b0441c00b6100003400f0840030000201032110200d0f00f19203107a400c2c8140c4200004040c000c01140303030785d8040101100080c8405448501070240460000d00b8a4010307101555414036050000d0703480e01300c3c9906400c016030380f15010004141512000145c8603000c080c090030b12641c90f821107007007010181034041c019a00c004c003030003c44407030030740c0c003c2544c000e4415050f079200d0040e6407695445001d80c0c003403061081c90540d40c00e04100124540e906d09014000390380700e840803200a9142c80011800f125425550580c0c503620521402c100c01e8030402141014400d0800c8514000d074101c2e1a81d8030b0f0038801d8890000d00c1e42030f54080c09080c40c3c008000b002c1240300324000e11642c1045200507200039118259036005a400100042405404201034a8507c203010b444560b038555991110381c89400045080b03401605141c0001442e2070001054010341c0c849818103071401030244c03000c041d08a4003880c030906 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 731964532 1250 731963282 731963291
    0x2011407120e1204050a0503060403140721090f0b09010509040c14070803011d0c18011809050901110403031706010905040e0f010c02071a030c13180b0d08160204 71
    0x4000d00f44400121018180c0e12035444034184410820300c52466040782d4001d5002074200404207600c91404100c8100343d56070300daa81c5201d8201031910804040c0e4101c1640f07003038140002c10310350040d0140c00711801d110705020401e482c0e114240ea035108c0c1286560000b4424861600d0310701e01039014004000240c1000964025540c0d8100703043e4200f100300ba1001d4402000400808030420034560460190707080d1143e8034a04400d1009090103031094030383d52030510040010071640182310341050094282008101c5a41e10908000905011200640254200300a02c001828a00309490580360f05403038401c01005080340c0c0d21185000107101504000c05a800040d0380c3d211886190010103a05001d00824003880e880c1030709459410032007034215403040300100820002070622600320305041c20b1701e955948501c2c00d40e100718000c15981303001d16a00031070700242d8a819006148180d030310641d010301a500013003040100c1f85900c0c901c081d003007020410182c4490100c4028002030310f480200000b4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 731965782 1250 731964532 731964551
    0x120606240d09030909050703091709041d101d07061209060908030901150b040b0d0902031509060a0510090504020111060709050f030c03070e060319031e0201140712 72
    0x1019a00b00d4401640400c1181e8418080e1500900070190b00c4041420700344004646959400301d81c04c004207020701240d901045107030655455800012200d030980c0480c002d103607118104151501802110140d00c103141c04011100190003c04c2142a00240400390403080d2509109032859a4090074560b0360300d5a8000c2500049c22034811142e80c01d008003601b5480b4500218050300b1031b100b0400c2081cac1000c01e40c10401c0b4080000045409858414a03031a03125910508404080c0200c420029410b0007022a0031000d413884881c40c0f44143d4038502250041e889070000c200484000b45c4c0c03080c608000401003071140c00c445c0c0c0c00142d00180b06240c0b20512750b07503584030700e82040da040d11080000780f0312400c00c001301d241c20000300445a20881c0607041328403407180040d9441415102d8010792003034a40c001001a1707414000c44241515885c034207001001d05160043c5854142c5161f100404084040d071648184148190384410302c01a400003103d4548240070350341007904030f030300440503516001c410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 731967032 1250 731965782 731965807
    0x40c03050304080d0305060409021f020a06021602040c05030705030601030903050f21060411040302092701050f130b06090406150807152604060b0d1112060624 70
    0xb400144464030141107000b40c00b01005041e0fa4024180c58866802e00c0c00340d50240e91100c81c81c840d501e071018004060010b400c141030b400c1484c41c80c4054074080c804118608050f11080180700c01d00d1084408011000c0d01c031009440078041940d10b41d002800038400200c695000c5d5002003d560701030f0030000c0c200020101c0c00062076110728800d04404800794040e14010400c954802d40000040f01d0900c07045404c40b4070408a07025502c00607114106400c0480c94200030031303000d01d002120341150341590304d041c181c5460181070282ea807280c0d07600c120710006004448080e01d01407103e900c1110004661580e000b0041c4502c00503009071040c030398801c001c546080d884000b0000801e8510040c1c60f4080c606441c5a85141680000c48140081400031106503100b04144800241a40520a040713484a040c0724000703000b0420541d03003102c8028036039403e11001304504210400d0858143c41002404c4020544030203040e940d1a0b01304400d015461105041c401440c8460f070481601c00e410b0069803940c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 731968282 1250 731967032 731967037
    0x40206091c03090f1a1b07060503010e0f06090a020d0e0d27080d05030901060f030614090f0601060e0103090c0b12010f120f1401050f011e051305040c030503 69
    0x4800c0e2044220030300070541c104280030010900301c041300074098030700110b40c001c2076900034500c0c0070030500107104001e050180c0c0c02c0c1e59111101c80d0844180d541c4420f40680720ba4801c0c02500e040c2c040382c0001420450040440c54030411010303001050b0b9071202000d101c00703504960300a2200340e8841c50307403046d8004100844803035103215941e00c0c202d014409070b00780040900860100c0084030107820501c0042c00005466004144e01e25000f6580d030b84101003280109201d401840e00040000740c0042401615000481459151921079105849900c031481e80e034450030340c3d041c6450f0404001000364034060303030038000106018100030942c1110399551007080400c0790001d00e10605c020900070a0110030300007490140c44104032880145040c8050110b0008040000412941c019110641000201001288080241c80c020320060814408020110f08240103100c411441084400250b106040301e41003120702c00382c00c040c183e0a00f0104203018100081c010350314207502503000000540e08000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 731969532 1250 731968282 731968309
    0x21080f010b0f3106030c080c0304020d03020a0f03081b0c2a04090b0f0c0310030803041a100503010e0c0a050d0533010f180c020718020408100c1704020609 68
    0xc00f41c031401c0c07060141c121210084a10100410075040002e5078030070204598115030100c0e120500070700c440c0350403803918050102c020050881c0e05050310070903801c514064010720800102a0401c1a60000801e5074060010500c12590020022150030030302d141a80c1252a6848100c59943c0011404a070940300d00c40c00840e25140d144003044581e07a0040050b54001c801d5090203441e50030aa100319030280302070b000c041d00c52400007011804001300c020961946101000e03c0030540e24240005c1140038110340700b0369019500345000b6028012011445204108004290342c41050400040c4803809252040840d068800c0985102a03080c1210b03825403040d466904004e22402000184014040c1c103900aa9070030192140c21f01038407104880e01102c84115410000d40398551001c201d1400382c2a80c0080043c03000508c00741011143d0781c0092040c0d031511000c82c0c1d00303141542e40000484803c8078069002507015003104079540906441c0c10381150004040500303240e0800b0000751110621034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 731970782 1250 731969532 731969617
    0xa2702040b04060305060109050735060307081f0f050f0703060509010e2212020d1403091903020106030506071e080115180321080f010b0f 61
    0x154540214549805411400e0200340d50030300c042841c558403140e40e041e040c0956925185c4910000d51214400c0000780d9a41003124160581403545564500110314a90b0440e40c18000600002d00c40f41030005d8008100d0b4001401001d41200c0350064641d16150302119110b01e83d220943e5110016050207814000d48080780b80b680e090900c0d4401404139400d076441540520f08400042041d4000307400e00992001420303848000b03012080c125071402160030400148407064070200c0545c1a030380060b920103a42e045449550002940700c0502141d170000b202d1612669010705240000c260102401d401181c2c070030300003c5510794903a90798604044040b90302000182401d0400c064007a01036100c41c00c2020141070201d11795043c14408903002d440e45203139000b070056101203280c54107160b846d82402150824014207a00f0803131440c10300a1844c003101c40001541c100085004220710b04c0301e0b00c0c121840e40300e60500e81084900080c6080e009000000105440b40311414140e03038100301002c98070355008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 731972032 1250 731970782 731970851
    0x12061911040503160806180a060b04020712030605100309120f02070f0b0304020f100e010e0a0806130b010e07080a1d0f010b03100c05040513290906090609040b0a 71
    0x44021740c0b4007880148000c1542c9000441754000702400321704500300c150440b4000c1001c040d0040170802a00c100d1000400703115110301d0500c0c803160705901c8032051303980c100c0c1c000307183c000c2d41c0c24120250350180134080c24154000000044407130180d4404004101c95005461404d542c90200115042c0240d014a07030540c400800c010440c641402c00784243c4008841d00401034000060080581032580012030500c42c106030710310b41542e900d1456100420b2020200e41440c0391905c441010140300301411549181c80c0400403039180310f48081e0f944030303070143c0d91000c08030390740d038031a05001d803c014880c141c00c41040382d0388803007082040c001e807412200c1c054004244e0b46a101d05051030184222a41101680303003008200d1b50b1a1f10804690407100e0449000c0041551082c0c407900402c1c1c00c451480400c400315102c0207201260903543c440503032003260400f11907601c4038184400000200c0e5240d41c810300e8400010006410074070240e0300035001680005405d82018602507141500384036008500d41038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 731973282 1250 731972032 731972039
    0x908040303180e07051204060b1003200306010503042a1205060a02040501020316050102041e210210200303071706030a02060712120f0501051206191104050316 70
    0x406910b80b0040503200000001d034588043d00a0a500600b2050b40d80c08400b280410240080354100c8182c20307400030a0444c181404001c050001c1424034151082005260414031000110209480c403a84068448a20f956a540e13a0058103898800900415414070b04441d02c1005003100c91401410010207040302951290801e60724000000309215080390040009206590b4044241d900701c112070290480910350924000c0d0180c040e9801c881561803843c1c03412042508840008004c8607003030404601d038524104202d4030700140e41c800c060b40151140121102c001c1c4103c0e0a4a02604482e03403000541c0000d2400301d041da44141c510a0005408100e00001e182c903100c0c0c02a0465400c5004ac0481c004c0c59000c90100e002d02100508481c04550708001018000c3d00e040480e0780740788070100008031b008466a40140001c0c002d0a02490300c010380348004c024005038540c0592403912001751084c1324480c603207019001c070b4843c840101000340000140354a0412041c2070000e1100c10420700d4070304 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 731974532 1250 731973282 731973317
    0x50d060320040b0f1c0c090e03071e1101080901200d06060c0b060603102c0a0504031e0e040203091b060f0d200c010501080d09031509060908040303 65
    0x386803455503c41c3c20070f801c40003d240e8170401c5840c8640c610140101c08640795040180642c9039035440161610704000c01a000740d10044001c0195620907001c018581551304115038150100d04c0004050700054103200845600031000c2543c41140e80c2c00110f0071244091508030101400703800864106004100034070b0740300c141d0040c04c0c090308180c0b82841a50702a92100000300101415450084030004041414042103c1d480300240400156008841d808002d0031003107004082d0502c04040c004e180810006951805418095609660345a008004210103802c4440000c0c005005208a0400d2001c0c0b40d1124006180724000b41d401506480350807144c940c45255195420a21070380d410450a03903901c5000082c1c46079203401c0e032030001c1c00c01001450381412101c0e80403c0e1200d448040f50b20074030070405400c4581a640c955040c1c64078401a00000c3d110503049000041c103130240e02201c080c0300c2a19601c0301c00c80f94010745020500700c805e500d403183e0300c0d07000390030550000349400e04800000c0c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 731975782 1250 731974532 731974541
    0x70c0306150f12050a0b150a080f01050a021224131a0117070509210a0309050102010606091a0904051806010e0c18030a050f01020d050a0e0d050d06032004 68
    0x100002c0910a20f442d955041d101c2d41d110100170241003071000841d0748450b888254903600c10b80500b042c4481a100c5440f2030341d40c1c0c03940c0c904070815820100007448a010358020f03a001640e00c0c0355010703007079151010010086807500c040e0750b03103050020801000d81d95507003d4000c024082502c1c0080c00c680e1007000d210740b400046040e01d040c00020302203040c2c480f41d55105150306c040d503464100d480300c03004000540302405109041c0341102d00181c880c2c00c24040420502c0005200f034440e810415039407001a402d89109208480c089165800200000360600d44d03028680700c2824041441c00715020001000c40d802660004d28040c0509481e1340c50013020041a40508541d040905d842d2078203e1071a001445807151602e00c02d01b00001e054000c1e01c04100007403401c1d030311005a40384140c002203914000d4000c0a10a00590700344030105140d02c126110315aa40f04003480604000805100d05956035404041c0303500c0d0860741d5103030000c04a03200341d811440e841c11030a039020420603003600700815035 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 731977032 1250 731975782 731975789
    0xb01170702011b09082817070b0411030c0103050f0c0a05040803040303030e1506130e010902030d0f140403050a030503220b10050603160f0e0d050105010819030503010b070c0306150f 80
    0x8046d00100904a0103c07013444e80d081036000455200ea0a0f41ca9448031890140007801442c01c42044180f00403c01c0b100340c41d2440da00150f04981018500ca0300450503900c0569120801c0183d00010402644142000b050507550070304003640703001e6940100501d0769016a00c1030b00043d9640f80001040030301400190701140d90002c2004143c200840010b0f0305031920441d100c4626502c000b200700050702904000c032a650028144c50240101100c003800103100155034000244d44081c01c544480c0c0c28000b40c078140c1c1c0e04138008081580a640d0203554651015013815102805016448032299000700e008400e80e00c103030014081c3d414a05410a06414203810162082d2410b004016841c03820070920500c40300203151460031a090300e034050300d10380d08403104550403c1c600e91028083c0841504000d040381d18a204940100b4241c4008401320462250b000b0000307442000100b09020303541c0c014081550003907001e520400d50340c0c1d49032401c85903804800c0c00a50311f91003080040031900c59080004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 731978282 1250 731977032 731977063
    0x31e0a080f010e072a0311010e0a03020c060706180602130909020f0915040e070806070e100c0203070e01031a06060a121802090106050301090e010b01170702011b0908 73
    0x50b5410708001d0f030b003e914028504010030900c409060042c2c60344180a030700c188a0114900001c0e4580d0070000c02c00300294a00b80c1c1250301f881e820661203140010040300007a09a80500b01070050f070003c001c0035a00c009030a44140761944010500d4403a0002054903461055000581c1d544082a143d1300309500c40d40020303070240c90145a240540c9030520100c44c001300c01c40303550205da920003104900740c440050490380c10603e05803030344085010008120f015104260704a07182659516411224000e00c3e803d0a5003012001c1030110031140141e02d01100644020241d03800591076000e002d850807400d91003030301c1c4014207004000e00c003019254906e40029040c4c0d00c3da490b048c2e00e884094000b0140904400f00507944680f055151401c0e20740408103ea0300030024121540c1d03034840104640c00c00c2c0540d842491800201c0c5800b01014031070b0400d0301d28180c40d5003c0c4003d034040f030701481c2840145803d0540d503c1d80f00c1c0400c0da2102094062001c4407948174041c006082222862414180e4000d01d5003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 731979532 1250 731978282 731978311
    0x301020706180c0510140d0f1a010305060a0303140c0c090c0a11070b031503210403021509130c05120718050108040b131b0f0302090604091101030b03031e0a08 70
    0x4107174042c4940e803415006d40f118980c2c600c403071310382c40008145030908450340f54a80002d0140e0040c0b0060340200100d000d0ba0280440d488034020014800c480c2d1000130042030060107104900b4150340c01501061040d20156201000700c1004902d11850854052049003000030300d007044150800034111041f428540100715250400b00c0018041c40050814565009120714800107a42c04201c420b00d6507100e000300d049040c0018500001035041404220310440e20388200b51a602a114180c6030701e814014100901d584401c001d01000384442145002009400c006c40041001c0103880c0ca801001140e0b11700e4043c5040c02c1115104480a0300300300e04000b844400d1101003010140c9a64004440d003003801500805441d200c0b4020750903036508120750403c0c80e40060907480ca481014101ca00954900c0c07400d40c0c9041c00c000c2220100c000080030000f1845101031207504c06e03031042d0781d0070744050304507898a903901502e14169200382451360480080042e8040341c0075449000e143d00209890454813 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 731980782 1250 731979532 731979559
    0x2003060f0a270e03090d060b03191208090f070e04171803100e0a0605060a03020d03020c0f1516080d022a06041e06061805180d020d0e0301020706180c05 67
    0x519441c106c20000c3c054a854140a480070740d0b090199010003034400101040801d554a001a1010325508560001c582201c0c0050010600490010b0000c02c40070058641541014915601654064170a0760f954014010045052010703000800c004102d0543c20785068034240101840c00078440c0c10b40d24401d0900310145220440041d00c5002d0507031000010034140d80e41004150407817195803019502c41400b18404051503004110303140700c0c5105807038184112842d42c0a0003a003c48046109203100b10800c11241400440010030070405d00c180c2c50549007506071141403080ea08084009150a280600591080803070080300700c0e0688200b1001d0000e51500303480392030b131000c82802074454040203402618104009540201c01522584100720324071442840c1c44001804125185548100120140358070300b90006291203001046a005220191198000f1140c0c141001da149800d0f64080c440e0f02c0014401e80942d422103004259443d00c05401c4d0305202c0c40990306940300da0301503010141c002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 731982032 1250 731980782 731980789
    0x108100f02040b12150607080c010513170a02010902220b0f09010506030403140301030b041101020f19050114070824060702040515031501092003060f0a270e0309 71
    0x398910150f07440c13800708568540942094424044498540c8103400048000800c22200050481d032000c120081003566940711608a1405010788094132541c3e20f00d00c1d03e003030701503290010118140c4602c000f0030b1001c410750105203a1500080c103032842c0d03058504805c503507442c41d1098081082089502c0e030f0200d00c0081c045051350106002c2c142c001ca80010000e01030600a48560700826442620076a4135a56414405006101a0340845010802c00d5050240b507100188083d6120b660070082c080e091070305041d41c8401d580c92641210255221070300f00301e40001041c1d00300e00c0f4008907107511030b0300e261100c00c0003120400c0110300c81001c03041141c050400c6d2206015611700981c144d40c0051070792260059400403071001e1134100e03410b07c910041c140708150176810060407981c40081c240880d40002a0340c1d070001e900c005104040845c1400042c0340f51420000303284071880050400072419440b00303a220041d0354012001ca0909140d612010305400044c440c3d00507001550002d075043c4031195000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 731983282 1250 731982032 731982037
    0x303090a0605090d080309012a09140d0203010618110a020d0c02060d0e0a0b060409030215040c0f061d040b060702121f0e0705090603210d050108100f02040b 69
    0x1c000070000041104045503c9a0f00c0107600e00b50410405134503450416030b4240038001540e100c0448001c111819584280500998041d40107543ca418400e1402c0403080502c209001c00c00c40d50124a42c2c0744080540c82c20b00c9000d001e803081000031440022162003400c10344041c44107814450078208442c0e000740d5408248906400f005182c140010300b0b580c00042c526002c1c8805265800b440c4c5950901c8608001a11501c0c0034412404224999641000c01013191402c04010700540c00c1031802000c5031003802e1100381c0c0a481071003420803268a4400482403810707250403540c04221351000520341c1190310020b180182004503001d002d00d0129101041d10b6029154009000320081c503103003da803240034041c020310ac0329090490040220100014009020140051041c0c2e0090f500e01044500b400c0b00c455209810280c0102840084004420302c0219a185510750000003841b4203110300b0818024030740207200440003021250f4131110b100003100ea01c000c4550840c0d00c104400c00042c11414207 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 731984532 1250 731983282 731983289
    0x303090904080d02070804090905100510090e10020a0f02060108010504080a0e011202361822111815010c0201050c060a1e0608030d05070e10050d0b0303090a 69
    0x1e40d030303c80c0e200d0449a07010780901c480040c4a64404100480c09421503413200c00c07687c0c056021a47c0358032041101b0802c03100d00b60380d521516203c0b00001e00641a2940201c0d0548410b05c0c2141c000780c1c48040c10300f0490300a030100200041c80c1c04081044168100302881c0508840402041a800c282d03403041c020307104078102d103400c0c00104022520f20343c0c0200c200b0f07500868508403d40d610821000b2503c105003400c1a140c01d5129000035000d03826804119030084082e01606041075140601144040003200410046d4140d0500f8001c03209070a0000e040040f20b4481c0b44550005800901003203900e40034090507100300c80a501c108038070050885441c40d400c050a00b85030b81c0c00300e02400122603034032444001e84064402c2c00240501000b19900c08007840c60f901d660b190321007070132594034420ba500d28031550019901c24080400d001345a5031040d90000d050f03090110002240d000820584044035080d0340100d04d0105403110035104902401408a4049014514280f0180000398074182e2500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 731985782 1250 731984532 731984543
    0x1c0506060915090d030e130603050703060b12010e030423150901021002030c180102070605090402030a0f0e161a120c2809050108040b13260909060303090904 69
    0x600c11900e0380b00542100c1c48440050310b01d5041951a08016190f0348071204141d01900155a01989654a131312502c002d9960040203001101d10755100c0354090300404441681c40344034000c02c070850031024402c030100890700c80090b6032201c3c50941c1c040740501d480b600d15a510781d4441e0080c0395943c2c6404080c5071004484500d99264190000100d141c00400780c0300107803c610001c00d00140c1c10f0040060081006c4601d07118250800a9004a8a82d007052042d240450420300400c81d45140c40c0e0055a4840100306002504c14802d058403000d480c04442d915246400440481c18600b405401d900060998030290003031140554501c8101c9100e90540d0645111a42e008508005002d40c2100c420f561100d07500790a000d1300ca9010b818003100c1c03d98050100710f04074030028040d40100074080c0f0440d0422190350080e80c50021a07108803c40440031076000940600c41d07198280a41d00c11100400c00342c6c0059107628619041c4244000080e0070355100c1d91040c415081e5550742d21142650099114 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 731987032 1250 731985782 731985799
    0x1d0409080904050c19030917041d1b03010905042f0409260a081f092301060302070618021c05072412060f060f0210020705031c05060609 60
    0x503143c1c48545d020300c011400170807000d000d0803007001c2d902d60041110540226120800440031104c2c0c00070078462071160269055000c00c090203007031f0f002020503501084891100c1520003048050204e258800d0308006070a81d951f0703080c8028001e03218040d034130340c1994008a61035490300490203d406001455002e100356160440712040245180d0500c0026203580d5a81c10940c04181c8800415001100a480040c91100c000b4a4081000740b40b6507461580f2221049218100441d410140c00882210041a03103e050b1704007082802000e0703140207158540d401621747d4020f1030108191024024004c280542131000ca81c003603945c00c44140a200c9040b0f100a04001e01d618015041c1107a9600c4000c2c4085072030866481241009104c140c0b6040355a55032480302130000712001110244c0c01661581c00c002c0f4070038050180a01c1841140542e00c0c01250034144400c000441a6170003a2021a6660004591030310808592220720540c84403510051000b031030081c1c08101d082c060264440d1107507503036 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 731988282 1250 731987032 731987041
    0xb010f2a06090525050108041104150b0406090501020f101d0105040b0a1d0601170708010908090103050c040b120c0702030d0309020109120b0408281d040908090405 72
    0x300c900c4a00c101d03400402407100d451503007001600ca10081c000b11040780c640402441d5000b90001d21401601c8058443d134046071a143c9604030036988800e40c003600255130342040d021000031040c840000f451420b18803551242002ca00400c484002d41c0300505640c48440385444c07180d004201004181e2a000300083c03041d03954030341d0010700c0d405030709014801d502c0d04040c007041c4018078940c14481e000b8103400344032411150a83d90134512450103841c4298000800511070090422000071002502070308079410035441d205410700b19480030341c003110358000002c0e0310501b6507007500406520080d40c2039100d080500e0140c900f00d40d482020509035041a0003070000b20200320550548022a401404480d9040c002080250040c03944001c26404140c182d1400210a140f4010882e1441d510281d20341d100d0b12541ea50303c07d00d81001151040428486015041d48200440d201344541d50070756500c49881001c40404e4401000d4150b218000c505000b512000300b2507000031100c04580030b0b2400140782d501c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 731989532 1250 731988282 731988347
    0x2030904050717010e100f03050a020909010e070f08100b0d080a0306120305030f15100503131403120f04020d08031b0408100e0a022d030a03120b010f 66
    0x41c0340e0b0f03180001c001e29100100f41d52580e0550769100e41c40f480801003c007529810070340103051079840001d245074402c420b132100609180041513084000034002060140b03800d4002e0b400c114650308214545004885e0420421100300801200f03260001410840781c6c440101154549403d440041e00f00710f8009201c0c0142d91180e8001801806200200c6000c002d00c0c3c60010714a501c10f55103245a1218540030511003804421179024541c0000c011080303a1034400010b4400f03820041880300140c0c5402103107408502d1500300001a21040d078003459540e1754829124403640c1010340740420342c00000003000010b0302c0740c2c1c40780050240c03c25040e030380701d54801602c41152285003024140c3c010b004a00005c2d00c04002075900309030100200306102c3c441d9009035059640020901c080e601032102210808169102405900441c641c003032403440000c0b132203000c80d15040310850124005031440065940900151044c100ca0190910f0402084090604000d2441c070344082c0b200001ca40e1180203901140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 731990782 1250 731989532 731989547
    0x60c010e19110d03140a080610020d0e04090515090f15060306010605030406020919050102010b0d1e03090b0703020a0303060b1303200d080c06060109030c03031d0612011502030a020309040507 84
    0x45c50a18055610301c0c8030180102900717420381b0340500a1023500d00300801a80081a82590814259180c40f54101040c04002c09403944e16400c1e100780c01040107910082003100480c9208404a100410310f5040858100c2c0c50101080c400e40340707188104045c0b040c5a60040b564904507142450405d460f0344450510900a22030141c40310390040c901d8404144000c90801d001c0c040314401d030020003130302800000b88007101e012407000920b56107050451072010740300303424410301850292400d03907112501c2e00c0809056620166081e00503900c41c0d200380081551501440b40901246541c0a00709001c004564060344110b020081c011100803402c29103441401030800f0000b40003e20f800720050b02820300c0b043d2540950402240c80c0981c0300000c1565008030b071240c08030384e80510807140d903a1951b20201d504480d060b822045200341e044024980d551180050101c03080c180c2c5c030b4140b46524101d01c0d8a02110035224000c01d542080c00f0045000d50040301703a445141c010b4601050b1071b641c5140031030b40d00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 731992032 1250 731990782 731990807
    0x10c1115011e090504120f02010b0303090d0c03021302070b0c0a021b2b0c0609150c061e0e010606030b0f12030d02030106180f15030911060c010e19110d03 68
    0x30f030728180801081c0710044c12080c0e00c14405403100b20761440d003002c00b02e081c3c508419001da0503500800c51100242001d0315142082d84c007880e0200702c0c4545a40c00214003150b488010505950041080c03000d0280c080007098000034803d050a140c8440054003a4881a5a4402c1610300c0b9840003541c0e005e488200310103074078542c1c0340105800742c0001460043c038038038050ba050304c16005420703011035036034001c81c0380e603050752100c01c50130050350b0800130101c031005032800088401e04d8a605c0440b0b0880e4a11000d260281d0b1a00c4c000318105250030304a03802c440541d485002054141101000942c0343c2c40361540400d20107480c100304114060740c6480c513520501a80c516a41d02c0007000203440f41e07018140214a0341014000541d8550f100907065984d03c50380103c04070f17503599109203100e40c2c0c00395201c2040c091003600512121310b1b201000420582004420141c0da944501109004413010b00c444074a02c3c888a4040418046540701c80c01c001d034078058202e009200c0701420b0403e0501462001400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 731993282 1250 731992032 731992049
    0x94113050a02060307031a030d0905220f0b010807030b2101090b0906010812041a0a030902030d02030903011d0601060818030301091d030715021812010c1115011e 71
    0x8a092062004008102c0110340d0304001c031f01e01e10620118503010600014507240c0342d0314098460300b410301b046aa04500100c04c0ca03001ca4003440029404294003481808005510000400610100015051184c01001c0d03900f05031038544800b00030380c0c4070080181008260010ba03000340080c400c05900400036590301070003d4200c4401c04c1452000011003505139012402071303a02081d4200402d12060065000300040108040030081d0100c090304007500348012180f4004c00c0c0800706401207030a10688945400042e04001020950740c1424014100807807540696100703502100901a500ca100600030081008440c1c40030a00301041c0d40c000c8407407660180c0039a60390b0350399203104000500080a500c0c154460010701c000000750080262403515420100120312880d08060040095000451a0000c181d1100c1d607622240c0300c1d5076141410071140000000d80303c500620107841030580d400200c0c0c503944800003100171404600e8201d41103941410148080c0a426040c08580031038030340201c0d44 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 731994532 1250 731993282 731993287
    0xa15020f060f01031202031c02030a0b131a151c0b060f09030c06071211030d141f0b0403060209010c1a070f050a020c09040c094113050a0206 62
    0x90070b1000469540c12244526410700180040d0f0b5001d0361207015507180c20345200c030f128000b2443c4460b6034009640c03140e420316001a4480071040051020f4040c88107840d40103544803183c5010011507110004402e07030403180564000f1010407100b40350312030481c018251541c1c00040499540554001107140c0c08014511901c0340c010a0040d0616080080c8552092080d030900c88040d06104085400080d0040c41000d20700f40c8400054440301c1c103100d20042c441c4002c0203022040c5100e44240102c4c103800b000c0200050909010142c0740018201a00004008810003081201e011004880444e6803000e00940c88001860040e182d1015084c4040c100000346006040da0350f618840300c9109414030389903003030070b1039508000319818042d0f00b40880150b881000c0d1980c175840e100085540c400d01c03d49014454580781c100300b00036916403c10b07520003c00410003940c0981107601032030303180c520781c0780c6131009444000f803025944010140c80b400c49041c1ca03003034240501c2000d2003910b141035009044541d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 731995782 1250 731994532 731994541
    0xb0603090a02090f1b220621110f0333030c030705031f020702030a08091801051c060902031006030b010914241e040f09020a090b03030c060103030e1e0a15020f06 71
    0x280231040801c540741803000130824507170544c040341c0721b204040a43c680e01d95061400038401541d0680c0044d020300c410700c0101090001004c00c180c10006400607107051000e10704201c0d402d1502d00800c2c3e48109203e6003000b0014011900c3c005040c4000d15000a6076003c02c107081c01e60b0400901c2124000707505801586101024041904002c000b140310a03641c0c11010184800c589041d08821b02507144d1240d01401200a405405260b902c0308070700070000011201a40c2d40040e2511402504503500c85844000c00c009000c1c0c111032160051103544000d0010449640a00500c200005c1c02c101400e007200f4030001c401884607952030a40b1401a04685911641e241202a84480303140c619100314242852050001c44030300a07809100c3d4060202c5071020b06080180c1e0151020409640d014031007840750400c640003c000490085020f03417140c20000080c2000c1c42440c0140414920503e03400b2240c0000c19142c2c0c203a443c084905044003280c002e44654000ca0a00e90180300340a40c41c4551020721 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 731997032 1250 731995782 731995787
    0xb12061c0b1e04020d0201030b19030f030e010f0905150c0a1b0807030c030b18030703120b0103050723210604060e06030307080c010b0603090a02090f1b2206 69
    0x3140585101100e61040c019000c2e003000031020700b140c000350003500c400114030055000c0e400c181804d200050070482100180380c005e845015199000351008031418003c2c505041d0450b80044801c8801c6c41d140036064010180a8404195842168010018440c0c0c1d01c0d03000041e41d041c0e611a14224090b01c1c4034070f586080034060031001d007000502090007020005462980010311038101d0f0f40c800c840e007a401d40b55845a0b80c03122402009001e00410342e20801078809402d1000300100b51103600d450040500c0c0f9041301044541d0301150340c1c14149880144142140c0042848190748030381511292007085286d20b2070581d000320002c4541c451081e000e030184003080e600c420303403180905607410801c0980c1c41440c440e6070202601c00c160550810418000410310b000700600c070421040001013900110840854405c1e8070807a00d071075039904041035807002c52801c00354940d00421180d440c1d1800c0d0820b0500c510714108003ca0a903000310380000c030b02031950903107120b003a4910b0346408046181503550201 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 731998282 1250 731997032 731997053
    0xf020f060a020d111c050309071d010920090f0f030115031502044a0103021e0102070b0a020109050a23030f0a03180c090f0e03040b12061c 61
    0x46401055007504c43d1440c280c800107007a0f41c1c2c11030b070302c02c01c030320030a1407190943d0168030150030b09007a40174101c80880e02480380240402c0114851800007000d6151040c8081102d0711880c0802011000d41c0010704c1100805c0140c0703040e240103d90319070802c03052000251981c401c0c00c02e004d800d03500706955030451032200140403046030b01402d5090744c0c440d8030050ba04101d204500511904600d48100d669100d0011040b00e005800b070702440e8508003d8035629160402031801100d03804003600310040c01141013038440030f81124102d02001480385c000d840080e48070200740c01b41005170400415414150b900c01d40110070302d1070704403080c0c800d005800d080c03c54000b0f00020200c8614204900307140c8500c2c900100f01c2d0300900c42d0340b1090f41449581a803c0300a41480c00d1100180300c4850540c8000c0380c00110904003c0c10350301c80019046891201c0f40c4195218421440c43e2500148410084103170740800710760750070242442803161962104000365100c1c40f902408020301d19030a40c940104849400c6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 731999532 1250 731998282 731998303
    0xc06050f0702010f14012105100218010c111c140601050f01051204150212161103090d0f230102070b010504091e030e120102070b0105090103020d0f020f060a02 70
    0xb44144002c0e201d80c10150b414084202401c09594001007011050500007d03400e40c030b0f4080740d900c0b44c0e8a145c0704c01e03103052110a10501342d59800507004c4102039001d0507200c0760741802c0c20103402802d86501c0703544101080c030200074052144a820166100e0303840c0080310025030701c0003034445124540f20340700e6a02d910900070503010b0250b28400113201d40c000c401f595441003e906041c00d10356503981c2c032010941ca402140d42a5075400388000480c141c0e03012a12403003030000c0440c0181c40800041d00820300b0800b4500c01410340c0003004488000e45400440029280c0c000d42280342c3c1d2600342c68010301c5a07006040020001c5a0b628480c0b01104c41900184a66070044400c110380b070f40ca55082200b114101c1400501251807801c94144040c41102003a0708240607041c86000e01c41c0309408200400c0c0c2035031a0300c003603940c001400d50030000e0102c8e04d00e01414064454400e03030341c15a80411000d4044900140c103841d10750f45841c046640f034031490204507001400541d142d8402800c0a07585218400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 732000782 1250 731999532 731999537
    0x1003260409140a050f1b0702030319031a060c0d0c050703120c03030b0613030327320d0312020d060b0405040f0e060703230106180602010623010c06050f07 68
    0x20104605c3e000d201c010a000388440529020b14120300312000c12240d1003a80100c0e003500083c4a029803980789101c2c1d9205940d082d407008103880c00c0d14041449110700c0a0202752007500180142c200154000802c8603450703840d402d220942a205003007141c03a0444aa1008046494010030742100c0d591201c000740840340711781c40c10320000e04c191040000f6802981c4a1101145280d4020000709100c2c02011f80445104801024250b01c00b4061810340004d030b400014008580ca550b562900b505810708807403c15145e030144040844440004a03522240780f0007404200ea0003203107924490f0321b50704031100004c40d9141008520b641d40c1114640c3c0d002441441d104d42d00e4090101c01503103c43c064a018641403034050200c1c0da83d0440150001c104080e1141082c550750a1210007140d103c0250700c1c0a000d850311100e50b003c04c1c910004045030b84d00d030030040440e410500d04104122a0038141d0b040503040080e002c4202d50303a000101d8419000d00c4019026034240030500c17140c000c8100d40c150040795640e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 732002032 1250 732000782 732000791
    0x120c0d02161a0f0d06030303061805270312090705010e0d0b220b010b0711010207080d0819050411040b030d0c020f2409091003260409140a 61
    0x8551481481d0035101e81142c1403040d10310800790380c003180d0003003450070407080b00c80342400c01d0346014604a480540003107020030342d0b822050180b61501030203661108503c0c10248214941a11029605240c01d8203851075946071250346a0220014000d8074820a84101a101245411783d215a610101072040c81d0102c0c0c4d0b041c4000b191070a001480d04411a040002840c0c280c8a4001080107025092406c07150098510805000129500d4081d4000c1100111003520f440c142d051840d080c034046040b180c159404050208078a001c0031031040e035049024104410070f80d660420500700601c008540b020070a140c001000100400032084201c46641900d00700419003000c4c042c190794080cbc00180d04003103005100181c005103040000303000b00d5200944040d9640c2c0620340180120810007400c80101080820300c08a2402c02e040706545c4031401c0c3c0041c0c10f1852071919114171913008170030003085142c008032800c5070b14243d040c02c80e03000348807201c401c108604041d076091200d1801030340c00c0660365060 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 732003282 1250 732002032 732002053
    0xf1b210501031109040c08070306051b04050d0b0c12070f022a0418020306040b0a0c020a03080402040c0e030f07061211090d110a15020607030c0e0d0302120c0d02 71
    0x3845464140c9611120144581c003480d010040c1e04e44004104840302a40000d01040d0340f4024842200210b125110205182c14403400035a6220368091030303415512411f000401c41569041002c1800300c0d0805000c000c0e07500d80302c981050910a544507454420a401c0030302a031a070b0700c807100b0703001e0074010303825903045011100d5a0210414a21000c19a10540c00b80c0402c15190503031000703d030f403002e001c950002420194042420040100c0d8103881000e0f01d42c1c2080344c42c0c101401401c1c100c01c00c40c0b014040211450341d004c0c00200c00648064015941c4049011209000381111145a040181100e4054840a1780740750340c0ea8080c05150300060f06854440e4405000780540a004118060490304180340c1800b400000210a1420f5951038828400c0500c6600c1c0c02240350b0181940c01c0d417403180d4040806020b850301c034001e0b100a08052420008a100c0f5a00000c44e1042c85004c569811284103942400c0340f4004c042a10705800070701c0001e5a400003040088c540c5040145070302a03450404c42e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 732004532 1250 732003282 732003347
    0x22205010809010c0f0e1f08100e010b030708090307050a110301270602071b030f0b07180504020a050c06091c0801030302030a030f0e01090b040c0b0405130f1b 70
    0x40004e650380c086030500f8400d25005014206a101c1c0140140050101d02100d10010019110602802000c40d429500b0700c240780100c0d600410140c400d444100d00b10754546409083c6511004215904000390000461821031060040718070541e00710048542c0104241030403945244149040c1c2e200350301e040c0d07507443c0007403041440241c40c480801030302000c00c00c1925150040e621204e8125003000034011400b83e811405110f000156007d564800c40614a13403902540340400030744010300340218990562460140c1521407010340e2810f0701d016894201c110010340f014020030040405034002d00003040381440c030000e401a03220000b0042c05200c00d00c148010b0303640a07030a00014005800400422410724000c0e0030008c3d14000f20344d8001008044420301e2821200039210880e015041e07102404180450140e841010301031003504a840d041c82c120000d071100030044c0d420300e40d007500e40c0b003003010400c407a07400300e020780b56509101d0140d0b00050600529031046400025461481050403800c00c1c417 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 732005782 1250 732004532 732004541
    0x910080d050d0e340b1b03091c0302060c0408030702040e03040b040b2107020a1b0b0301170c030303100612060504021234030938090c09130602220501080901 69
    0x20200c107251752400e6581c82e4840c0800108000240c03844c40208811605a00c5034001e0300300d2500030600d100386110081c0340090900c0c0010705145c003203080510042c03241c0e00020045804c2581d0480c1c0c002401030041c83c030b0f10b003140107561010901036404500000d00040003030041ca040d000c2c2c18280b0f40c840611940f801d142e40c10907600000180d005a0f540800203850040000c40d8100480004600c2652001c8c60040c0d0b6100343c21034640500c0302141c601415108100c00e91508408074061030440c0342101100340c42604a120341c00c100b04642d0170910070f40c040ea0740010007070800600103550701c00d8503040010480000380e69400c2d07168940c0050050300440742210702c1c90048a250300c16003040001d1012400740c54111401c1d2100002030300c9103009040f0130500c05000c040720800e801d28440b00c0310003400c800b00c00144502d0704c68012841880740360751034802d0b90307074070185560354090303a82400c0c1011002802900c030a0100c00044168220384c00c00c400b02d03c00201d4100f642c030b108840e561480703500e00341c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 732007032 1250 732005782 732005789
    0x605150c0303010e130c061106070c020616030e0409030315090b01050306270a0e070501020604050303010e1911180126070516110910080d050d0e34 65
    0x1900140b006000c02c0010305400c81d00506103071001c050380001911000800540f9500200c0486e10107032a03995071000034011140d101040e41082c20042c0420340104119208040a55449100c03d151b00e000f01801440040c60407d0017410401481c1a40d24001d00104034000380d1001e4154060303c00224032482e40500b004880046e95078a00f1038981c40140003079111001c80c10005400d00c105080141ca283c0d242061080c0b40b0010041294110017a00c42d0903c001034021790b0440d08080d0400010030f10010449044502c9101240c03280e6a03041300e0000c40941d40c0d80101d5034a03080500c0000c60031240000381c000154040041c94000c902c0400554001070301781200b020030480d03140c00744110314444c2e221980c003c000741071079840c014280e13902c0004802c03501021180107800480030b140038141104000c0d1700200301c4188613005410205407503a20001052580b0800200160480c034110050300038807002d0805508030f895041e220704202499501140017003140241c28100c504c0d10810a940540c100d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 732008282 1250 732007032 732007057
    0x22a01050c16031d0402030a050f010506040501050304080a09050303040f080c041a010807120e0f0607020c210307020603091c0e010909020310121208060405040c0501080406060902030a060515 84
    0x201201d6034090311141c0d5440e10135082040000c0d0695441c0d2070340c4c002140314500c61040040c0d5403038488418500c2d880c06030070217405400107120601c2181d80040840b0b8000d034100c0080d540758121004122917003002d5800c019054040454000307003107104081c64500303944031001a2002c039144242448101da410f4106091003d11103440860254090581c40d0341283e91494035070302854645c2101ca0544001d00202405a0701074280c15040d95010700c0401d030845400c0c400f5100b002e8242c0c0c00604203d020042e0070b070b0344d0280300d141c80c20b08280403c1101d107440da014040c142c807890840d407056110345540610380d114400038681ea0340603512400201c0000700050311019a61400c141e54400250030003817071aa5812403c40c400b00d1840070460105070300503c81c0c5103103c1c5c02009000000c06045010702094060f50420717007400300003008100110b0507141e013803030004079135692800c3c140043c2142e580940c12017071001082c010b584c5203e810030003e80341d0903112540c4101c01c502c0c05001501ca008101c180 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 732009532 1250 732008282 732008317
    0x100c0804030c14010b04020a09030302071a122a0405120606060d0f0f182d0b0a2c0d180e19020d1409031903020c01022a01050c 56
    0x81500c1640003c0848000000940c1586440810126030105880002281c0e07028030800c00c050341000288090b040b846640c861480c00401d8804542c040d0240c84001c0000d1440083d404042c0020b08019842038921614446c8240c9242441150700500070103000f00c05120800b020328400244c240d0243c03c0c0a4500c0b440e10010600c01802803600300c2c082e210310ac4d142c000103203140ea414069801900100c81c9006100d05182c900b0b21003a40c1581001d0000a070100b00c41e005405256035404100c0e40c21403c521041c3d036a8201c0e50008056052003c405080800c00202a000920303165030780c1038070b58070708403041c0252411054138502039855008455242c1000c0c10303c41c0c960100707000e642040541c005804100f24486440050381c1240c240030103102e5485c0c0320052580300c0321750441d4002428030301a6160050f0541002902c00305001c0340c005141d0001007400340060250704031803951a0703800b2544200780b0003441b10305000195802d0030f04c40f03600b0000414a240d030507034102c0f90304c0c0714074050700c14 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 732010782 1250 732009532 732009557
    0xe030c0907020a08040b0d060e010609030b0a092406170319020a0b070e010305071403040f031806030203183f0406020a052b030b12010905100c080403 66
    0x4042600107240304214001c019110000480320006000904a05044a43c581c04400320100c1100c02c1b95008020a030049001044041d400c03031601c01c1900c3e00003100301c429030b0741c51066070040d18040a00800b4040018058030007180361b40310800c01500543e03414030a840d0340c0c1e800f045121481003e101036070781080161001e070300c04408004c880d280d01401078546c120310940b200700d9581c0003141c2810104d104032801070029a4140708042d8400d0681c05c00e1942080c0e07005003c0f00c680401000103140007003000c254002d040c0a100c9501d4020000c40403007011980ba41e01c000e000c2d41013901e40c0740c20070080381005075101601040b13618441c003200d805040254005400b850702c1c1987c101001820949a280310002c400102c4010320103450181c000f0314003440301d480e0043c5081030220340070260075120400c451001c802255400c402d86800d103004204200948001403110395880c03107000c03080d07103412040c0c81003100105a840e401d640c242c030100a0041c140105642d02d0030216401800078000b0705d001c9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 732012032 1250 732010782 732010789
    0x618080111180a08030703112407030b15160b0a0b0906211006030201200319050c06070804020915012c191509080c040b150f0403120e030c 61
    0x18940320000511940c50f45644214041c1943d02000064000403401c1d0302c000d04143d4200310765a60030405584040104d0b020240121420002814400415490344209a030070307034440c036007481400c104180b42907a03482c0040052250011000044078042d4005000400300d8a442c41140000c60000d440741c8000d95540c4104a0328a484428449103140340c044507000440c800c0004215040b010040010210306600014010701c008005112030f04900508a101c06034001c0140c6403508280700e00300710504951502503440d03029a21980c1000c1c0b2580c001c1040b070560003481a40664007e42d4045082e03290020b4028201d84880c10319408965400d01550001142c0d10b1000c20100d04911100d0001c802034001070b01040c91004c190b42203010764bc200380403e000380c64050f1602841c500345409441d01d0602c00a4441d5120340646125aa8400814590380c6a03608081800768800400703680d40c480061140d00307150080d0005a9420300740c50310384010729000b0341c4440008400200241540104041003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 732013282 1250 732012032 732012067
    0x5100309020d0c0e04020109092c070803030f10060f0503011809141b01090e06060304081c0c02070608070c11040209060a08041202150a02180a0618080111 68
    0x72600904114a2000410059041040030340f2400d55001d546040c20f000050407140381c2c3c1c01602815150001c08414506032103e1001c0e2a9440c140108801e03890484c078500304000790780301c41b180f03010000c01c008050625484440c82901e800343d10743c40407070300d03000d00b22034200319104113801044040005000040c8910109211300c054000081030b050076a640e1101482486403070390b9990340c0889140c00401c1c45116008921030307001e1030301c402020314280c4901c1140340068401402800000042014001c0c0032040702c0e8403d12122140e030000c5a90412100100800004c19006000f00c0001203030307941c4034a1809008a02d1540c801d0500c10607074541c0408140c138068403a600543c200000001502c0c4c0b0307406441d003171130191100c001529190804001810404543d40300310341024024440c401d000c4460f00c3e400c05220310006031070f03c840c0806c5813241c00750480e129600c43c149070000654a640849002445030000083e088102d517500406800c0e103403101901c02d02001e00b482207203000380d0071804 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 732014388 1106 732013282 732013301
    0x7080a0815030a02060304060b030136080316120f0b0909060403210e120304120305060618040b1c02181603050403110607091707051003 60
    0x1075203d511111000f44a0b10300440031034180800ca9018030140f1201a00030041001e05045150204e01491640c1403002c1e40b96150013820348002800c8900b99a00c001041e0464075284c001c50300422680f01c9c1c0208021110326041c89101d00382c0903401c00401d0030840000c0008007101404162000104500c0c3c281d4040c0f0b00707110011b0b0f40a8428400c41c1d0200060034100700b060400c0c44d001c2e0000d600035542c9440764034100c401d080185801540158895100340700c03c0114203a081e0141d0388101c42c0503901040602c0b03a410307144641140091140c80042002a9900d80c5500180340158446030305031202c940c0413401c4045052421000c544c0d540d848130164000d1402c1055003986c0c0528034156420143c956011400b0180106001090700e2100c105a41d030a2915400003028000c592081030190115050302092540000c40ca00707095400260103040604c0c0e0320b40081d40a03054200 = true := by decide +kernel

theorem cover : BRFrame.Cov 731834532 732014388 := by
  have h0 := BRFrame.cov_init 731834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 731834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 731834532 ≤ n) (h2 : n < 732014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
