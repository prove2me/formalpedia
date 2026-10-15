-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5328
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:30:22.770251+00:00
-- url     : https://prove2.me/submissions/66b4f7d8-6fe9-4af6-9ace-1e363e3a430d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 958093525 ≤ n < 958273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 958094775 1250 958093525 958093567
    0x7140a03150f03031409040603050303090609010c08070806090702010609021c0b01080721061205150906070c170c031b0d05070c060815190f080f190305090402 70
    0x2000c10504155038102c50100120700b8000107001c0b41d00780050710081c0202001a02018500038404190b01d80e070f83e1522410743d4025a8491300e0754000304200a9180030134001d8408803181072800c82071600d801e00c030081400f8005403646104d8060500400c8100b403003504044007900e1a205c0840d80c500c1004c0c40c82540e014000003401481b41050134580496002d42880d901c12103240e16030300c4417141e03060f8000c1000095518100316a80d6107003400700311700307210740000d09207213114030300409100c4e040202c22a510600200800c5142c1d00940c2000701d21035021801c40503565028920034400d0150780e140b95954024000104c0081c4004101d01c5055051480008150b40090b000c0d01d11810190f00c04841a02c50303818040d040b810214000c2042c07620801c0700d194001c4400d00c00f242140604000922100000c6405031005610380e1401c1c46045e0858280000034001c1000405000003900c003030780e0300d4510b107015030703c0c44444014120040c90300900444e000700200410071540e40b44090300c080c010100807 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 958096025 1250 958094775 958094801
    0xc0a0f03020103050f090601031b08150414060408090112060302090c042102030d0e01030f0501080f0c030f0a02120f060406061503020a0c060510030b0f070f0f0c0b07140a03 76
    0x10000c0f13200101741600540c0241d508801405030703a030850722455071141000640080c81040c03c04005400e103024010a820400c2c0700a05196506050901340b40b100c01d107407080001900440c0c284000143c0003c11181b5a040a0800091407003e981040c0002d000c01d40c8003035041000c80b0108045144c03401c1c001c02c15101d58401442401c285009100b43c1c0c82001d11000350182e0140f044a85258001e810282000005240102d15082150010380a442080c1e20003480c51b032001c3c150584100e070900c101c1910711019801410385001c1c540a1550307960f81030700301a01499142d901c25242d56806c1c419000b04559880485e2050304140c5008c030010040da2049031030758a00142d01284040c404e00850f141c03100d0311780c0c80b1070540364a83c5a0f0303002468043c3c0300420b60781610200100213000c0c800d401d0303c220301d84070312041980f80826000d0801040c1240803020082c403128100c03c110342141010601030381082c5c2210169680d85002d07601200141e40c1c140b00b940004c40c0d280d12040d410b8000c00611050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 958097275 1250 958096025 958096031
    0x60916080613080f04170a05010516080c070303021b0d08060d151d07030b061c020a0b0a0224090c011d061602090103030c0b09030f19020c0a0f03020103 67
    0x51010001d0321120241e030728401c00007000b807958000c1040b100240c0207110184a03550f18040c1d8491120341040c201d0700c450f4201c0e0b082601d202c01413210030301c20340341d105072800c8a000d109008000018400c04004116480340c19001c03800358103240c800e070706803860350b000841c40245445864985e1990b8003503c00c0a4000100c01a000544508041d00c0b01551141e00110b120341f0b6110b4041040058110714581c0c0c00e2060b140020003c0308281000701c0c3c80114040c0a221002e800c1510034003030400d1182c400c43d8100003d02442000607111107039070808031208410499100d87c1d00040407418250105d84065140c410408030717403011002c00d400140140c12580032a02e43c2240c100043d039004c140e0003000001c0721152100d400c2c2c0c0f800c1080060002e81300c000403200904000c2d43c00a8040c160a030425000034104561000420200c45203140d04861a0b00c003c506059044050031003170f11494841e505d00c0c140300c0d100902124000c00080c28910b8004040c030710000e0b01d5044403485001179100a90000741 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 958098525 1250 958097275 958097279
    0x8010c0504060e01052b0c020c09040203031204260912010e0c0415080d08100b040e0604022101230612070c0203030d0f02070c080303060307050111010608060916 71
    0x8010340886040311400e486046a02c40700c0401942c194020b1400c07441d04501c0780d07008070340003110500c1c880300b40e840c06c400004103401680b0b002407410101403001400380b450001404050303a000802ea82612030075041c0c840b07203541c0d946044218840d2a0502c58031020102d4002c044519000000d40a0000d05882c0440301c031369074245070350a9911b40000312616030002616a0f009042c50b801c986c01e03404a02914661042d40d604074507181507404140d8100082200013880781114800d18604028807107080c1040c00c4c20304004c2c036a40b6142e00a411b2a2184c0c0d4001050314a000b00d450084101c40d400301610350710380d0f03034a640d20109400c0f001c60101b0161041488d08400380703080030503500d40e48040c3da00550140d40d04036040d07482d00c083c1c280980e41444240641c2c16460700600a811442950100160719807030b8034a40882c41c0b108540002801e60420700c10030050351000520042103420902c1c4c0045d088012540385d6004260704c2d042605203009280c00c01c401ca440c00260900007407941560520703061307 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 958099775 1250 958098525 958098527
    0x608090114060907050c031207030c0809032b0f0506030c0d1a04020f0a0303020705190320060c030423030a03021e0102132c060604091d070e0108010c 66
    0x22040c00c01e048411920700080791540c1002610298800c0a03401c00d546010b956102942c9150013180b00e20010312290030400100d60713814040d0383c1815403c1c5c204647c1d24108800c1c929100d00403104900303a20401c0d6081c4030981101c4013036060356111000810000000300a050001420080340e81900a1040703441d0321000341046800f1250407900000b456078407000100c0c004c07166034006003042c0c2e88892a4900e0012581d81c125030311005522a40081c1100da24008c14003441c0d03e6401030950800315102d00400120b0f66103000d8418612a48000310441c00301d000024041c1d004a600310641e52102190114402c40068042090202481d800500040100040580e0b030071803d00010f0058008100d10320b0810840560303002d020540c4c0c0d0001d42040114503070004100702d00d41c42100440403482c0c2404544103015250b8555000018840d0010310f08140420715a00c1684281d0032250f580e500c500c04204a1080c103500b40c030341c004058032a038039601c850100701c01000303000f400c840f540303468610080c2c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 958101025 1250 958099775 958099781
    0x2011409300625140405041103040b150f04050613050c0a0201060906060f12270b0601020604110111030408030a051b070f0303030b030f070810060f030203061602030c061006080901 79
    0x100110a49010140803036520898120f0384c0320030000c001c80401e12000c9001e1f9120f00408a81072241050a03449140900b032500380708202400800004011002c9c080064484030b943d0604104147e40100e5a5241c003404640714081c0f1200380c00e0014900f6050000c0000070800420b0b81d500c0c00e900a110305d944800340541111804c1c4074040128a100c0c00c9118851b00138403080040c21403801000502c00b80c045a41d510382d2402c6420f2840e0942100510070811103411011900060203200420080c58107982e100c1c5400500c1d04e003d814405140314411a80070204200c0d40641b51020a5036191884a0800b80c240d8125600c0b1428806180c5000f042e04440041c0001c201e0b064680c20395190b520f5910141c008000a03542c1c00d801d07000d01403c03401104e6080144a0040c01040d00a0030550881501d0004942c0160045100c580400c80b0030009640c0000d500c5030040c010480e040558586001d05078594410017070401510300900c82041044064901440112690380d2104c5040d5914074030744a0803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 958102275 1250 958101025 958101061
    0x7050a241d030d0507120603030f080112020f0906040e07030605071b26090618040f060b0415020c0316050901270b0112060308130b0304020114093006 66
    0x1056000b4002080f141a00740c00a5402c2055824540d0140c1410003c03003080c0c5c0e100b03400a40c00305280ba01001a00c42d40643c1b0140101410f90040080c40076642c00100e280c140d401100b031040e00504045062070340c99601c4501c0e9041c4240440c0d10721a0b40303260060183ca4101e90000100380703082c00129090000d0300e1006071082c0d011810109540c41d803070190f480318040b500140541e00040c00b590241d070300c85c8001002d0009560400780c02c9031114104100c1529510002990141c0c1008000c0104441e12015603056070380500b080105000042002ca1500054441e019454818403648125001105807940f0590fa800d4070514021381c0c80f060b050b0000321107000e600115080800b101000d1400079880480416414074002084040706d4a1072820303503090740c206641d1600f00284001231450b5000718800201601e4200605528040d0006842d42d20008803e5001c640f0000d035002d42961401c00d1a070303400d030702400304264010408903414541030716031600201d50310581e004240c0c0710f145c2ca07003501c036 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 958103525 1250 958102275 958102331
    0xa020d060209040e0a0203010509241506030f0a0501150e01050702060903150a0c050a0e061b01051518010303020d110c0406180c0e032508030a0c020307060305010609090207050a24 79
    0xc404070444a0350045001c0050903300101561011072450f9501c182c000c3d4007c8040c051050341c142014412070302180e00c180d000111009143c891814060381280040c068400300742006500c411450010540c00d20601200e02c0d8076003c0c240c4a1851340b80e510780280e0140f14010360421a00b6501034096800748120321010012601e00c0c1c9540343e0a14180d4001d1074081454040740b01c4d40c40450991a003552015188450030b0350803040c4541e07950410165845c200102d0b0b451941c0039516548000c0d4032010451001410810b5861000d841c10804105c0700c4602c40000e4020068030307a035140442c2c4100000240a2550b03420440310761207052046e6942584007100501410002140c016680d684800c1c0240410240d149820000340b0000d050003e0121400503031228140142da0384101401d03c5096044002454034040041c032505501000d0071040c0e82910740c0040c1d86d0103017400d02c0741c603200000d6001805003a80c0c1c0180c1420500c07030100c41c000e0080c499810b200e0101068880c030845607000361092 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 958104775 1250 958103525 958103563
    0x50702040906141e0a0e01020705010e1b04090803131416050108060f1008060d05060114011e02061614070309050f0103090f06051005090f041a04050a020d060209040e0a0203010509 79
    0x20b0317001c0300355441120401c240381c000500c0d1808aa031b900703094504480300da1040350084005601c00311100e50401e212484200c03810030101d00c01ea66240040e002c050304003501500840300d4001001040e0594540c00502c0c070040b2260346098260314140c641c000d0207410300140100001c90703100e00703040b4070050403410001c01c2c66699942101040703e0030500202091b030b0040e80c04000c000420000d0080c0d0340030340300903804080300a0038900098000141900781a6106111a8800303440301c1d80421000d800ca05100b26021300110510700444010082e0030610004400020342402003580160542c021101c1c1a41c11307000c40741140f4015000c50b00984001b410702d641a01141e800a0482e81c0860b6022500da800f0500f9140c41e000418000901110440c00d1041d583c0c0600090003180c05040413889407410100c0840d20b42a40d4103074548042003c002c3c0500ca0206c030480030000d941e01034840e50381d8050170400c2106000b0004075521202181d041e40203500e4a00801d07140400032594080b13403a1194200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 958106025 1250 958104775 958104781
    0xd0c02030309150d1409122502031606050901020d05160b041502120f0f060a09090c0812070c0503032b0b1807020d0c150c050702040906141e 62
    0x4400080c0c0d4041e0041c0e9840301c1000703031208418485c40341e01400c0392a01c0107118540341001c04140740c00317034000d289110f41c201440305200001d4500385030400841241e10803071001d021880840d14019010710780a8900b0781000001c130740b4a46c80005810000c80c00da00325510380510702d0040c2e030f581c81410405412580040703034041c0819416904140c10500c00d49454590305107061031002282c1000d00901203a0304250b0078401d070704128104280d00008505000031a500b007510001da20b212103846850342003515443c8400510824805040c01440c40c8410f03540c1804100c404515281d10105044824804042011840307040c00025600401a45812030b607400301300341012007041c0c11884840242d15225515a4065154401c0d80c420b2240080450300c03642c02c0028002e4244072240d034020702009a50110400406c01c54a0790421076440980002840d000e68a000ca13040c2c42501c1000c1c1d0098103040c401d600300601640007043d04801003a80c040e02c0e807611a8484042c0d281c0c840c0c0c00d1440d19a00d004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 958107275 1250 958106025 958106029
    0xf030604080c2b17011a0f16031716021c030b041d10050f0a020c0a15091a150603130b0f090d05040617060406030209090615040207020a17030f07140d0c02030309 71
    0x801c0411f81213200319080102c1010003500c1c101107443c04070005800e000080c0c9440b41907074111904a03540003a2607048404909000394ac1c0c90511380030300b5509050401820689001c0c5c4c0c0140b9075003101510078008028108101c054850000ca00c042e4144160580d150030034a840c420a03009000180015805880e00400c500180d00020070b18081401152a0240058100d00c4c0705240310f0a601004a50106903040840c3c03603d0010758050754040100c2c04101164882a0328100c1c00e03507044440c251a40c035210304080510b4154000240791700782d50010701107a0402284054428500c4400300d40b5a0320852004940901843c403070800814408107640b0400c8640e4000d480c1e001034050000901240e0b82d400259900c00141c80300001500500d0600c814800c01070501c8608400903a01507142581a40c040b410001041c4a50102200464803030192441c007481100c04800000b05001e85030421800c210388510491a9804078034810340407402126405020301d01002a0010059801c00c124441 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 958108525 1250 958107275 958107277
    0x206090c0103180b0618091b04020406020a062a0c0b010f080a0b2809060630080f0309030a0e011e080a09020a080109060b0f030604080c2b17011a 64
    0x2110380d006c5400c40c00216841d448001041c480d1500c80020729502d0034442c0d00c143e5101501c80718501440c0100814410542c00080c10300c01680d0002c40011400e01a110b50003100c801c0c0fa4003060344820307100c04e81480300d50240d5220780f040d0052105610f01d0740e0703e10755003520031404c0c03143d00304940010405601203a180072040760710210707104000440c0d1700c14400c00c03400558001c03c5196040d5035241c0150078004144280d4016050b84485014860a42000c181516560340c0c0b0329820100284904810810380d0806d44589201030311015440c2c4c106000c4da903450f40c120050040024500b0f49183c42e030742d0705c07030701402084002400115031484034943d4210b801d030500805800c0d010b03407990349034030043c1c1340e0050030f000030503086d800011141280e00d0054107451351002c406104525243c01f1030f0080d517010408035041079000301c0c00f0380e8541d40306205074140a59200c03030000c002d1043d54040d00d83c0151708003d014401069440b02c240c41c1d40c040002403224030078021042000c6138042e01c2c018100040c3c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 958109775 1250 958108525 958108531
    0x9090c03080c0322060f0908071a090a09050105031c050324090a0f0f0905070e1306060e040b010603020c100c0c06050a0605120a1127070206090c0103180b 68
    0x1e4241e9280c000318140031500e0313030f6205140c1c1c0280c8810180c100310703050340900c1080510000c0d103011014a86028600c1e541c4025074010b05c0d90100c0b4101c8007507800003074201251040c0001a0408411940e1200f0400c02054244120360081c0a643c0041c0d0100203001c40814140540303468103421030700c841801103d400540141d001c454030501100c000140c1c0c0706140e452281004100118205c00540c418106a40519400180442c2004030304800594046141c3e42034420203540c104003a40d034810142d01500b040903000c3e214038036011000c0b4460a0510903107200714050440c560159a0343d180c11022403140000101c1d0703076048083e4030034092100740c0210a4803210380c60640d0307440c1c40036155081294800d99440760055590481041349041c10406540b610101c3c42c00751510203202d80301d1200d040c054100c00d600c900d0010400c1800040b0381000809140c5501c0c0c1117004624040340003940e0b400b02602d481610f171040c0004d000e150340c86806801c02040c140100389021240d25916515014405 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 958111025 1250 958109775 958109797
    0xf060203033102030a0f02030d020c060f07030e0a0b0d140f13060209150301030215161101030f0e030901031409031803101b1101020301141905060c0d0909090c0308 72
    0xc680d0b4400035940420a41e1005400b40091405203407151042601d01070707404c0d00c440155004100ca0600ea60f58100550b511058400c811030f42e1104c030707407600710b4081d03101116051b40720151080101d070061819024103540c0406640800001d1000a40000301d00000c0390881610f1030700c04009440c000d01c0f090104151307032150b080981441d0680d00054041c15000c2d1303000e43d0b0140003000400943c0b03000c0b25400c0256514081892514480480c92000c41402c02000382c440f60407183c5c010700c1030b4881d606c4104c1144100c041005004558190705899030b0040810b20b001a0030050302da0710342c00d288445c0f98020b4001d080114540021a15100c1501d142550303900d0749030203010046040e00a050107050701d0240e11815805058011b01800703410040944000e0411303078070500044c42800c001c0d0803c0035114204071145005030a141003003040c40001c0d9046203420210101d2441c0b107440c03001807441d40c400b1264503004482030b01d4041c070408480000b2406040107107042130400100c0c500744014403410440f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 958112275 1250 958111025 958111111
    0x16050103180b18011404030806010f140423041109010c03050f0c0304081002090a03030e03100e0304082109010503100f061d040e060c0f071b0f06020303 67
    0xd8860b501ea031801190140007480d810310310150900028811000c0d101c03d000c8400c0082c1c1031a071002001260014110342c180403410818140301c90140c10080901802d4040c0c041e61680c5901d004111600030040c080c0d55041c005d038800c0341600d0716004039214085080d2420f401c1a0014004507846500f404042c1c040c080200500308101354107030b00920b684030004c001142d542c2d1074445140c0c41c105010b4600100280305000a584982c0c1d02c4c5d500c00126501490250102c0d50317030800203130805481d0506152030510340016041e203904044082c0c81100c214800b9210040c000703500441080030802e10b45a10200108640c2e0401c1d13000e40040c43e000f0041070400c41107640c883c42a124480c1080c0c202e04040f540014800f4404041c100c504e106403c000c1d13800340701d080b0002003120303605d06028115040c02c0d000490080758501512081d681c2407504080990a070540c0030b44000313007219041c050550144802c00c0c004c1001c900000450340030380d40c01401030311800091090712070340103d00d00482000d000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 958113525 1250 958112275 958112321
    0x10e030a1524140f060423060f0304030e01020d110718060b040f030501060b070f03121517070801060303050f0310030210021609151202060d052716050103 68
    0x8400500b10014106590000c5404080d4404104090f02c4070483d0a204500822090100305000300d0580442d060440040741920036440009400380203182c3c0d81a01104080108800d060b8403140340c2d948083d00b80c007503511184c000c0b882100c0002201700004000c1e407100904000b10b1111407814030008000c00d40004a203030f180c207523001d070b10303800380c1e0041c02c0c000f180c0002482404000e1140034001d00054292901c4e04445c2d58514003902010200607050108509585210610341d0304451603d840369001e9005568a407251040d400207890f900d04558411000003140460f414031078042034940603283d050402140d94070b5980d00d81c2c8010445072403040c60400c00030042c0c45811103814040c949802a1100c0400386040310100c00d41c80e0720101200e400d068885046c0414500494181c64503448000e0503c51240042031403840780c010015207461910080000914a0785603051401181000d0100c0448030b41c065141d43d541084038000c15038404075020001503002e81d200700e466003002c0441d1400c040d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 958114775 1250 958113525 958113581
    0x1e050c1e071407031202010c1b0b090c0a0b0406110f03090d030e04150603150f060302091801060f1205010303170627010501030c03050103050c04090804030c14010e030a15 75
    0xf0354164000c882118240741e00050030354080c0507030282d900007890b0003905204207030505e801407200d450b405003000b500d40e0b000c14070711102030206641c510b00290a0b0702e86030342e480f42070031410742c001d1140000154034000341162001e4003103490324801801000560800c01030388100652000103050840c00c0c0035404240039103548503405008a9080c070a403c6040301450140040d083c1c0b5103000d040d80c4504001075003400a0405c01c0c003408141c8000d0302d4010703218070155011134610410011000710b02c000c403400001e0215400201420903a9450b0384034001039101468501c2918401c3c0001004100d181c00070103400c10000100c07da00c138200900c2030704000180e00c0d60f6189102642c1c56069800504401403000d560140103c1c40082503a03c1c0c104041c0d072441d11400e48540d01c0b941003504c21b90f00e81100109001c0d1070b8082c0c50145030801c480a150b103544207174402011000d004c4103070110f907041d890516646000705007100742a410001001003107001502c25402820b5000ca900c0a8040048801e8541 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 958116025 1250 958114775 958114783
    0x130b030c070b22061506020f060705030c0708180a0501050f0313060f0f0b1207060e10031d030711040204060503040f21021509070b07030f09091e050c1e0714 69
    0x81d40642000240000d03617080362240494250855419980803d200e030043c0100040c8159100585103050b0b038607515036007680821031155020281a100c0d01042d0b0401e450030f020303442c107907030207086505001c0c0c00c3d51b803001540c02c4d005080b80040a8001800083d040241c0da20000c07010500c2210001031800c845265102101d0240029158486c0c0e18800c9410f94102442a5817500c2c00210060510f00c0c50110010210f4004500d0580280382240080141078003d8021031920320780a25650f00b02c0701540750260341c9411050083e105541c0e40c2401c41c086042c06d1003128191500c994459240d5600c4d074aa01075414440c2c403045442589089850f0113811001c045040707170b603a40358080e0500340c00351404e02552130f0000d0024811a080f44004000640c0701504a44400da4142000e1740341546906d002e4a0140d065804911071600700101c900ca09a81c5911350122078041c800200005e8640c4140c004c503e0043c80210080030348440c10411030032819501512441d88614618049080342c940703142c0c18 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 958117275 1250 958116025 958116091
    0x31103040f0e1e0c070314070c0314070902070c030308070903050715080603161203031b0806031c08012303070e0609010801090503040b03090c0d0503130b030c070b 72
    0x2260907440103120070751054110342800f08410b43e403a89500c1c24400e9807407140748904040207080c48141d5407040c94021000c07040d02c4480350080d01480d0f0056076030820702544105084182c2c0340703014068003c10910158400d403480b494000707003004d09150441e40c0560b200c41000c2c1c802c80070300510010000000340700f0405030024203c20825048008007205001e07000c0c110184c0900d201c0d40000040a00e8440c41c9811071088440c0400b444400344a60304041d801031491b41d10b0710861a22241403003540f00d8001101501983c01901140c00015a02c0311510188051105140001d0035030001000280b110310009410048103140c02c40c02d03121030304002450400356501515032940c041041091a1400c2d4904500401481e8003d110401e090f030760302512881280144125071902201085442c0e1081040c00c0c1e0308580034011004c0e451080c00c201d50349410002c107030451001c94850208044413210300b40c81c051940150380300c0c181000e076907400e0407030f04008000c01c03908000c04403d044e0b06011340f891014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 958118525 1250 958117275 958117289
    0x307140309010f140a1b2a090c0f030c090f15090e13020607150c021501080c0109090b010309050303010306050a0632150f030f0109110403031103040f 66
    0x9a501c8040001411203000054040144603212200c490000f12840c00c0350b50341c00c280c3c50204040010b214182c0716060030200c0240011000c0c2d030200149039071000c040340c10040141d0104140940e070758076650549401302ca40d180090384084006120390b0294001107000c0ca0242403000340c20361038007020140c0c8a040e074040820403100c48100960190401c5184000d04101d020001a529000c01c00070003501c58030070006d0007840002100c0c414415044480100342e1071200702840181c0313120200075510007441c101d174200c1e0801c80f80001009800050a51074401040e103800c41420f150460100c000c006c62191581415210243c1038001001800190701071846040c0005441c100740200c0c004480081c0c010306a8006d001902c03c46030081c040f1010306428440041442402c14540422401e0981d951040404440802c000e42c082d149000614401ca0403d08031b4001a83d80d420034400b071383d0f03a10141e0040108100410320202c0d1103410f000b0003242000b4100c926140c0d031826941100000340e03020003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 958119775 1250 958118525 958118527
    0x90c030a060f060506090a03080901090e090309032a060c07030b01060203032211120c13090b063309030712060b030601231c291003060c0203071403 65
    0x1948042d581c030070500503020a030f51007410000c8101c046603210b4487e0002a003d24004244008030360311610084025150361004074099050107500c0f2640d1381c011b0f40c2ca00344079010360009003141c1100741c0d0100002c00791784d040d4080c0350452641030008540c0606201e5540c0c0c09403400c040041451403c20600a110780d60085a40380350807000341c1d090090320801800f00da0716107072040d00402d0b441c0420001e90b0004179180c1e14915030300380501d4600b9140540c00350700102e00380c00304000b281480d80600c50350350044050780c00554542d170810003c0c48080c50f1504a03101c50010038035001000c0030381c00e060320100b03071943ca00e00444840028541b580c180d201503400b4184086d83d800300100c42c092104100710540086c0b8180d410b0070302d402d0321044100180c000d00d8040c002d48041c959681459480c000300030031a01da20301080b609008004580103800d1500200d83c1404031410024400421441a4400d18a426001e030031662804003a02039100c40c07030214441800840301082441070001c0f00c90880ca0300079 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 958121025 1250 958119775 958119791
    0x152209030f1403010e180f06010e06130e03041406040f080c040c032a050d020d0209031c080c16050321070c050c09040f08040b210408090108090c030a06 67
    0x41c240b00441540c003054510910040084880c0c3d0f1018507004143e07030808a48841c00306a255240201c40f2403104da1a00c207140c000aa1909044810b81c0246005c3d242a006820070070110019030303120b8584090f8580c41004208080c81480340804020741d00188403071300d0701d541d4010b99510500c40d90800354494010b84814451864144280000c1064604082c030507482050303450b2048124248000c94407100d842180726049100c0c004889440d40000740854440e41e11420700340080d0400d4510900a02c00e0330082c0040000c0c05140c400602d000c3d80d01c01000d60380e008000c1520340c0150340000b82c0d44601c06615030020b401880a00040600007010001000180e022242c42400141c0b4080504c48403078031001c045400400c102c45080c100f0345032500b40e0b0711185030464800304825005401907002242c041113070645d4100400c006801ea60f80740840713215001842c1c04154060354020480d203010003504040354014145203611a1061098a840300c00500201e07061081c0d810045829030783d51814 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 958122275 1250 958121025 958121027
    0x10e0402040941060714040b0a021f1514061603030b090609090706050315030601270c050d1d01050a14182a040c03021c05152209030f 59
    0x90945061401c103401070b203c0551030212911854060309200030400900c44810074010548102c5001f808003c018696030364040000035113070300032208580b5600d14440544c02000001d40141181241d00700e071500102c0d8540350100b400151a50001c682103c0b0622605500101d0140103440040c0292000303c1c240024400b0480c00c010014280b501c60f400c698140444208005030030780070f942d51400d10326920b4031384601030100a0f400410a0303a05205440010400d0180f964580c00304443c0c10410b00040740c2c1850b01c400558500410703500002d4001d1000b11180c40990b002040c0c12600080303002001c0011f4010740b400c0d114115807002d507050700d822403403480010380d028007a400350081c100d05d503100030001c1c41e06840348211305030301c82c0c1d01081c07201c1031181d074102d0034481500f040d00a1007008420040c00015000c1e41140a242002d040c10b46441c10103580c69000f501e214040141050403e40482410840c80342080071340c0800d010503001207260b807102d144c89043c92060007601c82e82c01504120340 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 958123525 1250 958122275 958122353
    0x50a0210050a38100909050106020a02120f031c0e0a080903070e0606090402250507090507050c0c0103050c070807060614060f03012705070306061d09010e04020409 72
    0x828030f0200040c0c2e800c00c0080044107501003d26001114140200040c00e0400c461200c0340b074200c035409030702e80300001480303680014a040c8501c0c0301365003840101c01000031a0ba12000348456082c160b070410016511b82e50341d0f040940c500311944a500048610b0319007806031a01c0c284100465040e0320004000c41d0707514041240d0002040b05818040d030514001011440034040d220303c0301d0182d600405c03079111280c0310ba45403243d0fa90700050201e00036111030421582c2d81041d4401c2020301d85c500804101c4051190302100c80150341100140550721010b13004400400c0300034800049900240b0904002602e41c0c3c2c007c000081c02240d010030094188a1b4290204020072180c600c102d00c10000041c0741d60303408042d60304403415805130b60b04e012841c4440c800b04202211011a04601e030104100c138090301648440c090b154181d9542c0802111100002e400300340105010307074060305400042102c2e5520740303e8075910900c0030340081400f28581c0d480303100c0c00d407903000c03000f50219884155082c6416801 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 958124775 1250 958123525 958123571
    0x9050f0a0204060911040e0a02070f080304020a06090303170403110f0a050f01050403090306091110030e0c0a051e0d06090f1214030a022206020f06130c0501050a0210050a 75
    0x2580810500303081500040b068846c1d44034045905039640005510300501d503050f03400b09904100b100211072484e2811401c180d1048504a05c00d504408000c50443e00c02c4140100750307640358440b0803104214607940210180000d1045041180303003c9103401100b8107000785481104000c00401241c00149403050420740b49501c142a03c0e8501030070840400d03407011150003103a403c50000900791155052001c10810340c1c4081c2608a0300074602c0c030f05516496030141c0e44681031081030b900700795030784010462100307024882d4540c0301400301080710722003d8090100c3d80c0d54170003e00c1070150318520354648050703c451402c1a100b8842c8500b040c8140034011030103105203c085d1030f04460024803050300042500006d000400215170100780c07108400341134880b050328960448480320020340d071240002d41d01c02c1172107001e0102c1d01620300803d40190032260a82d0441da44014103840c2c05d403e14004407100d40080c2081d50441c46685124003d4038118810720317000302000980418420008003a14091000301 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 958126025 1250 958124775 958124789
    0xc0801060f0f30030519051b060f1801090f030f090f080a080f12010e07031410051504090f0c0f0e10180902120f0903180f0409050f0a020406 62
    0x180401111000380c240c2c041143c042010300114120b9003504007264203014207111040040c6201030100d00c05600702005d40800142160380180301c2c051140300d261034078010344004400040f1180451200e13510150300010810342c030400080c807003030181c9847c0310000c503801040d008603d4a8500031403159201c00c01c80003521242013900d83c150300c7c1c402100c1d5100c2c03540c803001d4600e0b1404200e000d81d8880550440e10313149664020250b55507150b000d950300d07103102690110003103480c0850094154964051903403240c10214021100301c4e2400050120016a650101c0501d40080201040100e410711482d280301869400c0059621003000703028004250b91508402800040c1054400c150f03907011740900d400c44e4514180141c1c84540c0c1c90f464130f114064004070080e40c000b04180c01748242500c3d03a140f15003030f658002030b036685540201507221703c2841740e10708105000005051003410141c04009a100c00940001080f1180c0d4030381c181400f29804414986421600c040420751801703000d200040d02c6c00c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 958127275 1250 958126025 958126049
    0x9040906140f0f010509220c150c08040e0601020a050307051515060304060b0112020a02011b0c08040603110706051302030f07080c0103090212060c041a03010303080606070c0801060f0f 81
    0x7040d0b45040b22030f10305110301807040c8000800200c012645c42046c0344005500c2044010700f40e20745c603108000f0410340c011000914030708030b040c50b04184241d107800081d582000d4154074081c01c004001101e20030081c0014150b10580c22290f00003141000100030950047e400341c07a09481980340c00402c0d04e00134249079110380f0541c0d180030720b40d9501c00840ba0081e0f0701060005e444111000107071080c2c02030701c003010801d07480850700c00e4103150103420211140400b00300e401060303142000107030b500714150100540000400e11003441064040c0c1c3c090520301c407041d41414204056640d0358030a0383d0b400c540c5c90503107a03000f41402045080c10030901c84c1d0a0803200241c141d0320704003802e1a5840c840b0400d2241096202c90a10341551070f001c2c041c2806070b0355070741954264605400001c0440d0300038401c0890b21926403858820034410141030324107a95256549203840d488040401c543d5030412001919519035411000880a009220b81030044c0100d0010000003864440c982060400036840340c11030501e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 958128525 1250 958127275 958127281
    0x106050a0311040207050f10090512030c0a140403081908130506150f0a0803120c04031a0a02271e030706110f0d081006020f060a05090309040906140f 66
    0x841c0121820302030b8826900180c84a1050800d01c4ca4407211006060302d80c0a103800c10030141d0044d0300041c0540e0300035821520302c1c02201d01148240c2c40211422040b4210500c040740016104d142c4000812150041c4c207410b080e101d40350346078190300105200f0b951800c09a86482c05e05c1e000004143d01c41c20303140c451001e0100540702e25840740001094010405444001600c207583c0780715180d0361022004d48541c1036a5101e2034055036a03806070344d90981c1460f01c080069020034201c4221001da0380d00c482c09074224901c0e50000070440700e010b807036580c80540a211100014030711841d8500702003099014002040c0d030507000d000755028002c044010b0581481d0b02d0b400b003524005042002c446640c030302100348055120030503040051510807143e00e80100c0074003480070760344101c1e45802501450403d02c0f20b03580d51300d8141da59243c0c0c200100107540203400011546100c0707600090344981d8003000d40340b03003140300c0c000101110a8244c046812590320800004004851418640d00c11f00b8440b1410083c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 958129775 1250 958128525 958128533
    0x50f06010806060c01110d06030c0b030403050720100903021314010521070f03020307051813080408070815090105090a1e20150a090b1810110106050a03 67
    0x2400200b02c10701924002070709903840300c42580a02c0e003a000c4082c0542e2100c0390403401c0d101810040c4401d56044c0000c0b84089503040404044034020340c0c1c580c480b503182801c2c580c3c2d22400c5101031060020050032000da001101c0e00e400c44407158004480d940d0700d0003203017148100030880b2401034000064501d4801c1484256074840041410766008072406254102280c040402050601d100700f0702d83e002d40360001610560003020a41078074800c0301554011030b01e500c1400351070f0900c68010324402d48008080f903201c0d0005610201382c24041c1c1c52722403a254032200440e151500543c408400c0b030707002000030042000114802034100f0b41100003071203a800c003103211503500c01c1070081c00307015271454900c01310b41c46400c03100c2c1c0d01a240d44002000200c0c071100c01440d01031051201018081c41154060341e40180c2504110340c540c0a1a03101c1c075040500b01304000e08aa08041000e10583c41d02810b100803aa0b2070303c69994954032159250305a0505044441d402d41d011584090b01525032958140001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 958131025 1250 958129775 958129787
    0x50412020d0c02041a0406030c08010b01080c0304030f0e15041e0510080a061d1e070212072307031704050f0d06150b030709050108010b0f2208010c03050f0601 70
    0x40c90f01250007244102c440b11002c01103102c0301c40d5442d0b0003403912100004118a8000c00c42c210380240d4001c200145081c8015120410201c0d80c0f81f00d101d100b00000380029015003551040c3c0c045501c1c203480216460340c0032661440b40041c4164040750b002c20304004200d2802801d591610100843c0c0051618000c0441d200c0050170b0a1f80c8280b050120005000c580036a014400910a1402c455941c17140e00d1155450703128141c1c0d241e605082000d0320201c40101052040f40101500d50041400c002d0100e00c040140d00a03d4040354001c54801046003c210380d00f0341d00780e2802e00704000c0c1161628500d071482401004c541c61403075104080c8410002669501c58281659a007a03c0748002c0030481c0c9011001020388454096800024020201d42400000061481408651241074100c0e464200540b4182000d200d039007080d00d8108084d51074a40c0034030243c45032041c0c02d441100d40c030100c07000400c204245900700f0030041c1c8d0340e45000e422065040c00b455400c586c5406001c5032a04014000074030f0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 958132275 1250 958131025 958131047
    0x5100605071208090f0a060f05010b031612140a0b0108090a08030a0207080403050f0a1e0506040809180114010201141306091b1806061106040308091e01050412020d 72
    0xe100100b00000c0240009003c0004845c00f14070944000e8040792801d00d004029401e0344840030340c0790500200750126454101d034001c90500090501c00b40c003180c0c0440d01c40070f6001130300314029114880403a0060540424500170148040d0104601c440c00b400108010340c02440128298000314100c0d0201d0402c000b01da4202c0e0461201582e10b40090503c004548200d43c001401d5104072000c4180c1c40ca400704001c0900b911407007004110115030650b0115100c51240007900c2900110b0204000545042c02420204809040c0004030850800c0c42034030010700741d103c448401c07090150b4032869a4288a2544501c009a14403034880c00c05416a88401c2c180394401000b55680d6103410301482815540c1c01d010a0a80700450300c2e02e0f40700e0f00303210810000701c0c0494000605016000c03031110f001d0104600096102001000c0c81d80c1c40703071012551030502614644440c05030220344018204811920b511440311940046000d08003482c0c00b00201200c2e036411411504405441c41e8210760225035190 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 958133525 1250 958132275 958132277
    0xe061c270b0702030403080c030306041a060f071103011506080603011401030210091809031106060906012a11030f070f0603020a0e0d051c0f051b0f0d03051006050712 73
    0x1e070603941d90405a10714840c0b038101516006004c1810141e0510000c01948501000d89080c04400c036000a04100190058041984554180f0280e18250341c000068814240501d20b000036040380900400d0850303215a0620070140d880410a001054000548c1504000b041c1c00030000b0074000c015880e000708060200034442c0310b210344a03c10982c400e00c100d4015240b2810750315816281045400d00400c00424124003198041201c080f0030310700419031034494007014011003c1035032990011500c020722a80c8448000d02022150900100000c1051134298895500c0741c155004820030140341c181c0514a050599004060501510301c08281c0d085c2203031814180543c417104103550907994a40c5074011aa04903072802201000d000000404c01c21a02150b105404d031340c202c113030044030681c0000c031b055400300d8020061200c0c06a40c1400c081c0024040ca0309031260044800b00541c1044034012604000984650a00050b0700144210000400b0a0300b4003910340309850f5241683c2c2041224094 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 958134775 1250 958133525 958133543
    0x5060a020904020d0c18120b06010e06071a0a0b0609011d030109060e07060f0906080601230304031808010e0c040504035d0c0e061c27 59
    0xd0700342c8564058820852062509000455100c0001001c080d0002261059009610381c0051700440f080020744c0243e41003802918181e592000640300a460b003800960050020442540403d0128824070000e2110f446d14005030700706502d000c1d054400000c4518401d00c4204031250b0944e0304000105442503d09948240061300d01000074010880040088c1c411424401d4188070600042095000d071103094407640fa0800d8a040111601945d070301403031020480210100744d5940c02190241104074400b854800d000e160249408003d41003500e00b28080341031000102c10759111800180d0203002001c00030001c0350b0781500b81c41e80e245840c51216004569070004501403502c6041001c400b10b40c240d101c49a000c0c01c803030b203a03052103200701d21881e4051007003a480b07020311005610015210704080145406408414884002480b81d20f4840091012400e918403603130301c502c000b8040152285080c2c08451110f0782207142503c03484188020082400700802e000c41c1c9000c0d01d42d0340003d4002d2101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 958136025 1250 958134775 958134787
    0x1050a0c0f20120301090e030301030f2a0e04120503270a020a0608070e040513022e05040e1308071b030b040609020316081b040609021602091305060a02 67
    0x880c0c400d0400210b0540030b81034414801c2001100154125401c1038020000d2149501d51341d43c91f40070a0100034079040c40a43c2c1074020410490710112400f8020480189400e94403481c1042c0409a80c0041c030020810400c000c148016020311021aa0303903414914a103203040e04107143c0c1854023010009003801d04480c2e41041030cc042042c1109a58098403580320710f511140c0c042e02c1c0348405c0340c50b4800910300c7c960b44d0107941440c0c000e46c3e002d048800b010741c40300b0400341e0030410508181400b922182c590030192070001c2900e5110a519420291600ca0380d89060441142c5a244010b04007803054000806178400162400d00721800c041d0801080007100781c20045884800903103078405021012030310b040c0400e101e0030343c0c400b400c01c43c800c800700c400001c0036050411070108c0b648100d1a140e008140711410b802c000075012032540300700034000121a40c0702c414181c100d812190b000318003801e0346034190085043c440320b21078026008490b400c018900d5656801c0c1e40310b10003001c203400130f0f8022401c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 958137275 1250 958136025 958136057
    0x50a090f060804170909070c0602160b061302040e13080408101e1e181a1806190213170d0e01030c0c060902030a0f06060801050a0c0f 59
    0x61900503020044000c1030032030365420000c200580c26602910500070360504c420f081d441c0c0c482101c480c418007a1112006070784000060307511024211042d00c400342c0030444004014840c02e00c48a0719845810b4540060030aa004d00c070040714403c031000e01041c4100814040e1580d031414569118043d14540503030401a40b90003840d0b8016a449500e49100310041d00b66111040d421100e0900074000d0440f143d07004051003031081d6091071001083c104014554a9209031694002503100085100030402849c003580d40c90340d0300040c001c030a01000e0740b0f1405000d007013a109580030840340e0210004000b5810008200c0f40b02d003003040c045403055507001030409824010914040014100350710500c6031303c411041010380758888910a03900103404070b40c000e0b02a6010307104005000c0c0f01903546000108481e920040104004013040e641441204905800900340340c00c0040f140f48696804200c01c0e00d04020f590a58a000d000c0d1000507091074201d502c40c0e0b6000180d50a1344c000d9142034440f100d50b50b00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 958138525 1250 958137275 958137287
    0x31509011104090f110f070615080a0f021806060f0a0318050a0209011e03021203040801020c0304091104050108150a030507060e0f041103010e041401180311010e0d050a 74
    0x109030550640301040010b080c101650005040000700c0c581400035801042030308045c0d205502040c000c1344030a0154002007000c9501004a694440140755032054079100520302c0c0a00c901411540c18580441000460030200d00c1c80120310124000f42105040410010780e1502070310000131031024004c600852190310a401580304c0490800017041e8802c618200a52258000c0b00c00345e0203000e203071000103900207500d42500c000c00c54698000c0c10240c1542d007000306546001180c08401d101c1032102103240c1c0401e03c02000102000d100440e5942e20f00706648050b64105914003072800014042080141d0b00030385041c0d440300700c192b4040c0d803000ba2203000800282d01600003800c40d1141c0e04010404640028400841250803604124081d86210800055504110840c090f940040c001000110180400950803d11442c80313413100c1078284c0c0b641800c440310302c2814001c04015101d148145500103070602100740080000740021174003014400c0e945d107147d003074000c100000050161300c1644111 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 958139775 1250 958138525 958138541
    0xb0a080a150204150e041a03070b13030506011d07020109030c02090403170115090b131202060708120f220b07050409090510050c0a020c0f0a0302040e07091a03150901 73
    0x16484c104070407035995008200b10b0240c000c05024a1409104102c0c144039110811214000200204840e5051100ca010950080c1d1010000030000c0040880091414491540641062041c0680c40d1041005491100c14044c10403415a4948a2280301203a0f00600003240a5010b5805c00090345072490b048840074140b409442c050100000040794000d41d000840c19800c003a0782d40d00f250141c680c0e690740c80324402d803804a010007400501c03c01c45d422400b146000c0c1035000800881c240045511206207641c4220000c0e50b0107803800c82080544080e030119203030001c0030384286a01a10001188035284154840d001d0400c1c1c0344400061070161094040ba00500400d0300140002a41441c00e40e50b40d6000708882d400c010b081c000041c00e44501e9005407020032820f540148000074885081c406080c80d402c01503500118490b5010015031a0ba001c0c0c04001d0710038038010020b01b858009014221212920400d062803010400048540d800003003c9140132401510841941c45400c82140101200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 958141025 1250 958139775 958139789
    0x11503061a0301051c0501020d0c122a0e122a09060f0f1305040212062a0f0a1809051e0919050a0b060102070f1203020f1f0b0a080a150204 61
    0x2744540c1d1110b801e411002d0110426141d41e4216641c18410b40c0a40e00344004006101d0b140300e030808440269130799100418034880c1801010300c403030345c0081200000c44040b500c145512a4034036881c03c1c040c001550071410821180380c0e19031015a000640410f4029101c54403c1c011301104051035522642107200039440100306035050201c2d8500038018080440b0160300c40d1901510300440e02202082903482800302032417107041c1c2d42001d4600641e0036140e4000700314000d024064550b0035401d4038002e10a181c000e403904011540040042101c03015603411052600781001e0511100e02070940100051541c84441c201c201e82d6a030b0340d00f030300d4401030442074080102020807100038000c0c04200900f405000d00c90106050343d984005998618542c410000240304690301085400e550940107464603200b40305807125031441c9076030302e07140c01200072194150080c8594a4449100e452150074000c40068511212682c90b181240d502c609817444098600c0d80c001f116113111020a41c100c9000c0d102d1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 958142275 1250 958141025 958141027
    0x801030f2f030c040b010e01050d1104180506033715060807120c0e06010507060606030f1a130c050f040b091201090b160314011503061a0301051c050102 67
    0x1024011141e00307441d0090301806070082c4598414a400c0c98022070300d1501c4180c440c80c20b0302003201e0046846a0003c01c90040007540c604140c00c1124482d0300410040c14626440c0f00d040a07190182001c60b200034045c1403103944030301d903066101c00c00940140d040b1003a484180c10308800500103122880440d401c0140481d03c140034090399035074141d00081c01c0d00d0001c021101c05076201c00c0c040c5884140ea400c09071070142105000c0080ca500030704000c1c3e2000e8189045820314100340e40710340a644003600401d010a03220305603c40105a188206d085000541100004800100020656603c40140c4404019885950f0941b00360300400481da200d03c400c9814a0341c0c0c0c1c0d546c01000c100740d0401c100d1f26205130380d00428058040d070140159441070f81c010140940507119041003101003060210840180b41d1205450003924001050060083c0040040d0041900c50888010126841074129090a41d401c0042c020141403040075281503e200b61076296401c039004a852601c40c424117002050b940c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 958143525 1250 958142275 958142333
    0x405060c0f06010609060c080d06030803090a0605060d1a070c17030105130902031b0f06040e0618010609140f1c0611040515090a0503011d1c0801030f 66
    0x40341e00c0c4100c01041924516600c90700e080703802c11514440e0800141c0105c48490209070040010701c00701c98241070014810399280d561041d030f03400c1101e0076016604480d05400501140d401000d5210800315804904d1405540d500d451203420b00d4802c543e21101180090701c00783c01400e880013100d42080e400f91042c2c08002a000d8554803d00070340f40214406001d60030301484a00030101c3c4a43c1c000c014090001402030b40305143c2c0440d01d01c0580c030000340c007441c1071182c42d243c0050019040012040c5520b190010a0041310981c070380d046002c0b00d40c0040100081503100140000b07031400120103105480e80b0f14005110b003500e105610f5801210321850351645041400700c003900b544102000d00966001300f01040c03131809a0701c80c040d000107403000001d0344552140001c150085000b000a01800d4444000c24210356401c80503881d400e21012101059000411592003d252100b442d015103450f840c600901c0e404041c88014496111038901100b041280e001c59600d9035441003c440d2120 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 958144775 1250 958143525 958143547
    0x1706030c09011710111204020f130b0f030a030522030501060b09011b1e08130306020a11060709210506090d0e040501030b0708041e0302030307030c111e03040506 71
    0x1d410941c000a84c2c410910406101c896030b0250710b816030a540f5007182000140c0c5d95001c0f8140d00244102c5c1e0040911041c0d201c2540c030030f0015144d0105807400050f00d40e01c24011300c100a00c1d50003881384a41d012452080009501c4000c40d81100c10780c10001c0d0310589031625440002a00c3d40004000754249280861125145000b810b4480d000340d91f0004408002515a0210942180b028003407000041a403003611100700c0085202601c1522a546004484800144040c800d900304841c1c16030005a880310003070303201c55035100074181f03003010b040c03a0306200e0703c0900010414070801150119070a5580f240c90358031400f40803001d07008015191a40780410205403206040e4452201061340d010205125040c00c2c844e0506030b0307610080001c4942c403910025548244024011180b5003e4401c010b8096044901d0756501148640c0042d5164140800050161800007e102c0104a904035890324601e42c0055000c100c000f01c0440001d5141914072010b00354031560700020b4100c803000580107125 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 958146025 1250 958144775 958144799
    0xc03151e0b0c280b0106051e03180a080c0c010915080406022802060a0c0504171f1e090201120b01020106080f070801060603050c04031502070204050103081e04061706030c0901 77
    0x43c03481035080507880d07a202c600a9034140a03d8068401e07111128090b00003c3c8160b4000b9a0000391080f0307a00070701400d04003854900240c02d042210110408a84c21149010421445459403424200142c54a041c800558080c000456034001004400e00200e4203016941c0d0444000d01c05106541300c100445905c032407024002e1848140040c400c1c440002e1b402d070541d2042d111540410b69809142c103240500c4c50141c1c8090286a880c24024030310690076000300171051075414952020003060802103180701c51601507464118041c110306001c00540142c0c0e02c00101c5255a00030400061141d4038400101d00401c800d4001115510443d040002d030b4880c001510021a00d030603009115481c3c8820301101594015916a512244240410f000141c0b50745a20030303821104030401403c080568002500b0781d04280d2003a01c2d0801c002820004200100b001c82441422101d032503803400385005001002d02405140d44a030b045030000110340556414024244620001411015156100c404a40304 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 958147275 1250 958146025 958146103
    0x2091507050c03030f0a081009052e050a09180804081e0102070b160302283f0e15090d0206060a06080702100c03151e0b0c 54
    0x642e114a1203401003e1800204680b08106510085418844000d8080c1c5032240042c140400700c4050b5040401c04640f00d100c1c151044052a40d0300801e08040c0c114031341311155000c0344d4030254403902028815a1103d1380c4030b80840360b0302100041c05021098282c0c2c1c20794040807009001035800600005d1003240040c11406010040c410303c5400c04920300c000307080340300308000100403860010005c0c0001d16994a181d50084140c100585851000f0700c5030b909a00c03c460303118581c40c402c049038424007a4080c200206000d044100c0100c40d5150030614846051500b402c2c0c00c01c1001010141d54040480d00302400140085040321150a4110a031602484044800d5503992007003125140e6420700c0005d0f128000c81c1c000e444004802d041040c11181400300501c040e0075803141c0180c090604c01e1a10421080030380c1c5660007d0301c0e00610f008081c488101d5440041884103030303803e0034070f04004800c0b12400c0f140c580d50300e1079588003030000b041d0a080210b14124405002446da03009002c0c0c00703c0003104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 958148525 1250 958147275 958147283
    0x509060c01092105031302010f1206091d013602090405100b100f0309140a0309050a060f050f16020303040b12130519030e060c0f010f0b010c0b04030302091507 70
    0x1007221043c00f070448050108944400c26010015642400340d4002c45010080e46038600c0c00340800740e2080e00400c2911800e40c02a4a25961075010a620800d550101040311410302c0080c00130000301c003c03680030060f40020301c40102a25090141c41050441c4103141c460741d02070034801c001d01d050b08001d52216540c0b040c3c0d002503403c060101d10f042c43c0c248030409494406484250400400c1c1d8170440003040650811202e00c04008001d402d444801c002c0b06075039600c42c0e9900c0354240d041100348800301107141e00c41c070140300c040c4211540254008040c1d668003200c0d100500d071504003507400d03654814040d00d0b01a4040c00001404581e00a070070b0004c1c444580e800000ca82a51502c0c080d207180707a9210314000e880b540080001c04903008510380507000c0c4034041c1c540003142c0b0744c40c074002400591004903c2800c5a1002c14840c65003c400c2c0100801e048210a082180f40c140e880003a041e903000d2007004080e5880c1c0c40002c1d0030103020340d05072103c00c580600241e44c80a100307606841b29910807040bd40f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 958149775 1250 958148525 958148573
    0x22401090b0a06080106081531062303100c020303011703090f04020c010f0c2a0f2904120210050c040902250c03020a0f06050a0509060c0109 62
    0x362080c01c00c0000c00045030000c0c0d136000000c0e13103050000c070b43e02c41c8050800300802d840300c1c90700c4560340c0e5140252600161502a1507000b04030311054600c2e1416504c2201c00040d040c46030412a861049181140e0310401c1a0f900e00300401401c006420000b103104008103070351509000d5106203500002443c1a0b5144a00341c030b00e00030300d10440f1030340d0b80119440d09a100e0005440d804803801c1503005411040a100004180765400c00381920076100300c09140000103400340e40c0c1c03200a00880740140e0a190664000950b0500c45444290529204074000750807800d058240c8002c540c03004c0302e03110f400061040400c21604013468504410003e400c6000014416030351450040004c0303214080c09100c088a030a03161602d418002e00294101823486086442c50025404494a00c0016004171511801c00c040c1c40c01c1c110b10411008000e0360700150f0390030000100c180b11040c2c0020896915107410b06010f40c03208804000101c551140c81c0b950b1242e0b5081c400950b0421034020201041d00842184030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 958151025 1250 958149775 958149791
    0x506070c050705040b01020a0b07030f0b0d050a140f060106231201061805182d0606031b1606060b090d080a14070804050f0f091602240109 61
    0x11241140e0440014246800c060300030010f500c3d2640c00340c2031803501070050715907011040d12540301008045411f14003180e02c80008004c90314103407081da481c5907001c480101d0f203051142c5542d607407080c40941c0141030b41c0304a01c0c1c16805850401131130503a89403032411502c003580c54410041c10a0451007801c1840c0300009021000000001c0607210307607007000d070413031021030b840c0a0003103501c0d62400c54070584a0140da1000324245d11510b600d8103d80144070010b0116081c05030340045030740c1101c2c1c03084e0b841803111051222058101c08806401440484d0880d80721b848a04038400510700c5038003a0005081d0004800c2010401242c4200900d030040c081002000c0da00c0c0f290400922600e000164070450090400b0005040039000d001516070920b010508958414032107820340e407080c0e0080e50801004601041645404059a00055020f94040929160407400308211000181004140c1c103070201c2ca020109100300941d40c01c854001c0d0300555140022484500196000e029007000a400c20340700d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 958152275 1250 958151025 958151027
    0x11d13110d0515074506020319050a021905010f090f0303060602160b2a160504020f03010e041103030f0c070806010605030c0d1e02030601180b030610020f0118050607 73
    0x261040f0400400c02204004507000100d10500200040076400714040e148400305e11442c02c1107032400b0b40180e40040d65501c0044040b00d04074410525040c04001c010030075030501941c0031a13460f02030300d0041081100412545002400b410001c004c600f40146804126001e00110603040144580a900c04224190304c4440482e20707101190084051040c0748882006215540ca00030400041e80f510044410384010002145e07050711100200c20960140840d002450490706102c0700418080b20304510b0714240b00c0d146582c0c0e010520034481d00b080714070002414429640495211840000d040c1d0307549244806101c07120f608000c48400261185c4100030940400009000b4103903006a03d6036070131503440090013142c650242d4440c2071096120300c403000c05007180440c06c1e4040504041d001d81c4a250400005121544007040c403a508030380c410040080251b0f08003220f4102c5030035560712a401c000100160701d09003403a174114a0030b40c40e010088140c012101c4140f080103200f442500c4040c4c6461030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 958153525 1250 958152275 958152287
    0x80904050f01080601140d02030f03040e010f14060d0e0703031d06030c0f07020a0f08030d050f06180603070506030c0d0c0c0b420306011d13110d051507 67
    0x3d15202980908014030801000c0d0000f0506450014800d04074800c00d980070905010840c0d032240c09650021400b4070520020500349405070400403410400b1034a80102600503111801009010b0703000041d2890a003039440e00700d40c0512072110210358400340e0b41c2c039005103544101181003101440c151101c004514014040301d0041400c6020503040c100d48501811082c1c1c0b024100301d1380040410720000d281480c844109004000300c1c0c01031038a4240031417180094074030003440740484440d80e000700050740e039644645c22000c80700c80c1c0c039422850b40d81ca0b01013407a2424a8011aa003c00b000c010080e80d0b1043c100100f0b02400745100500001000c1c4009444c08444a800200300b03010711030006805c4042c0711a03480f000c10f081c810380407100c00071341c1d04010140c1c05034480340090302940110750140d050410485006002070181d48070130004180c9103050722100030340900704040c103180d02413051000120340f0010340003004002810780b0840c4d2611070b903510802c8252800c07010b0010300196445000e68 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 958154775 1250 958153525 958153529
    0xa021201020c0604200936030a030c0912080408010f1103040b040c05101805010e01020703261201030c060503101403010e071502151513110304080904050f01 69
    0x11004218684580d960301140340c1c00c61040d444180c01a0502001c555103846c17000740034090400b010a202108480390010070102c0403c20400383c00400403070244828008211202074002d843c0c00201c40c03c9002c0200c1ea40c0c6020740c02010203010315984039041c00006c2c0c0082c4112205107008000101c14404d1380c1c1e083e200c0006585103400003c0c030000c0c0c0883d900994048d0300a200310001607007a0707221800a0300450624249800040c5100342d80ca101d0508481c012001d0402405c0220304841c034280002c0d517031070031400002d110743c0362400c40003146c0040b9004040d0384148481d00c00d440f0800c8105860f8100703001d20094404039100040040e0040c0940e044034080c0030003d20464078030341814076000c2010711000d115600343d941c8034104a003d00b005c2c0f1481015003d2410440c0c5c1e00d69083c040280f030302d40460035052100400b64140500d4a1841640d201007017002e07950720081089800c052401880d021a00c0020300700000b081208201e10314005052051084408110b940c503420700f0b80011113024 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 958156025 1250 958154775 958154797
    0xe090a0c30050c120604060b1b0c15120c03010b041403100e0c010201061d04021903061109010f0c0b01051e060c0601170a1a07030603060e0a02120102 66
    0x1022500c4821000505140030080400800080c01101903480300454804075000d1140c3c0c40f02007400c0d080d01d0b607401d43c070b6600503008a0741401010306210381c8125134440d00801640f101159440030803100c00c18004504c3d201130041100000114960b10340c80141d00c1203140e503049008a0002504480812083d82c0c1613407045051181400d0034520a0f40c0900c802d00315490f45845040b9405a941e0901c0c0264501c800861019201d1040c0e920006803c0d560740313070010b89040c40c5101224000a91f1315404542c031a804580d001d4484240064600c0c4130300b400d420190603d805c000180f03802d5841b290041611000a80c1c8079607014100900458201e41d1004004103c40d420300c00401c46c2e071402d25881103d0041204d0151f1500b103038040051020b9110311942c0403107403c200c00401130b5040d4500164141c00c1500301402820f590341ea660011500e503070b6402546695800041040c441c481e6208001440d07000c00304006410742d062050b565101200070403440b0326401d8880084240781070080c0c921070307244 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 958157275 1250 958156025 958156037
    0x903010b0a081213050d0f0210020a110f1c1103070f05090a0c030b030703050c0a0f1d0408090901030317060a15031107080f0a26041b0905070e090a0c 66
    0x20110b40f4503901c1c0e00c0400d079540d26541d481400b1920b5500c2d2280082e119100344642c0d40c0c1e1f81003500c140001c111000701d00d0403d54010031070700400300b151066003819680044800e851890301a50025080d0300d911201c6820001d540c940b040c04010f60550391000740c00c000c40071182e9196803540240311805030307401603503042503c040100320105002e401c0408100c0c154240400c1c9841858042490295190702c2580c059109100c18205410085400000f41030014580400b8606094000629030001c0d941c401c0071030b031003c00003014002805d007581c2001c50002c10001455a4a040c000c0c130900c40d05601c05042203805020901c0c501c1c0020a0b0700480b410700b4040d00c035141c000c10095006003000030003410104800c10001001840c00001003024489140d802d94136071031000c90003414011518541140d15650607a503500c10051490b680340d000b54064900158404150100c04410a03d03500c40240a17041005000805402407600400c1500c00d0300e110280365a6501143e00703540340d500080c40410a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 958158525 1250 958157275 958157293
    0x1090e070b09120c131e1505011209021507050d18060c1502071421040e070c0501060f08010b01020726070b1612020c090a0519050c0903010b0a08 64
    0x6084000b50780c000410011340c0c980c09824030114000041e00d071002e001640d40ea50490000840319a4201c20344940c044080020700c0607140d03100c0ea12842401514144509481d4021145545070410b01d0381da40c0c0517050b13109500a88035801c003103412110301100d4a000e12b00d070001090f4811240c1c1d141800e00e10710005e810a2070403006640a82005d5026900c01e020740c50440074002141c002040070030312450310040c081c0240b06c40581043c810040d0070034146824901b02c3c0c6080b882d20150b800781ca4450045140c2a1030f8140c042c0c80000313100000501c65400d005c0300003500e0b514050700504841c0600700070f101180c5200b004a80301d60302030150a0045400300e040305001c40540300b42101ca861781d003085a4542da00c2e25008015500041000d81491284504030400c110703545403a4550007040340018034810480c0800180e00c00b10040403441c816984400045002178003400a4810b03c2d4818070401650a00580100c9150301405031f20b4082d600307080c0c0c4261b103414030380116803c66000324040c040781c134 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 958159775 1250 958158525 958158529
    0x80c1606050901110c0a14060c0a0302030c19030b040f090512090d02090906010810050103030516052a04151a13170607020d0f1407170a0801090e070b09 67
    0x106002d031401445641e0780340f107000190180c01c010407450003400002c1c8445c4c505841d0151010b0801d2034820445c3d04410300b4044c1d06d101042c240c4040d21551300700941c50317555114803142d083c002c4c3c1d10594804142d04c2c4600401d160194480040c0c56800c1c1c80c18800c2402d9a40a041607c5070020024450f5004000c802d17411007468000d030117140c0340208072820b100200d400103102c5400507031b8019240c0c2c114a004102c0e5100401411101e80a651420b00c0b60b507165850281c03081c01000703003442100002049400030090240300c1d060140300700502041c9000390243e18100d0078040580c4090089103401e42420b4030300c031990b4a02c02100c0302d000c2d40701d2603c01c41503602e0b030503178001501e8441c41125070000071619100d0514036000d001d0080d4020450703031505410003850319200c40c04040912820b40c84041c2074a0b0701c810350340c0031902c41182c1650740e01d01b1890f180d480c00d900038a5000c11180c000c0707654034407290300888070350480c2c412200502400000620741b9454034418410030300e0b0aa82040500154 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 958161025 1250 958159775 958159781
    0x4060c0e0603041b0911090d15050103080c06070f0e0904020a0e150111030414010c06020c150f0f01050a150c0501020c060412050a0e010815041a27040f080d0e010c080c1606 76
    0x42032041c41042181d03000b558906054803420303001214070050100c4d2880c1d191104200c1994403014524060014470104400a01207100c00c0918500507540440001c007035483d807484020040950f034140c1d0702d951400c00803018a1406110200b030020b44519050502910000700b6501035400003052010b03070030401c10040d202c0303003040007003118107a07020b1110085d5140c040c03243d142e241d6030000030341d40d071442c2c10354203903500b1140201004030441e00c5000600080d11004040d034103403005400d004012031640c2000f510500000000144190300026440042410101e001c0303004611500108500200e5000700b40d8440c0140101c18001441c1c060b07004025611031544c82d50408204035101030411000000720741a41c03007a603a41c00040c1070020105016040075035601c0c03010b02d070031040d16510301d8004219204c5240d001d4800f405203c000d55a0009001450040754844c11110004110b981a1041098040c19550308000c3c0480c040800040c0b410348190100c4031610480b03201e458066010f0380d222801 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 958162275 1250 958161025 958161049
    0xd0e06030c1e0c0703150905100c11010603050c150c061b0c010c030c090b070f0b09030909130c060e030d0309110d0c091d0604060c0e0603041b091109 66
    0xb540c0032080e0740c0d000c0030034218000c00c207240c0c0d00000380c00d50300d042d03003004800038a03520403114200d843c1c5010300001c1880031541c2d080145405c200882c00100c4528219040040304021207142c0d4a0312034000b040000000f0051320440c402e0b20714110550421003451042c2c0100012155141c0100000850380c030f41c007a15118070b80c07640020007820410b07404981030031101c04003501c20100b175075020317428001a0406801801428412415840c142d4595191160040b2a84004014640f0100818003080e001c0c4182c0e400040e015001511a10b03110301c41c028081c180b804207071015aa0142c01140c094810318292020b000040c0081c6051500c405044000344400e61b002d03680031387d00300c61017030750b6544504400700070f0741c050641e19441da03040100300340031244007401c240c51b004070740800a450140b02084440c1d1154202600088d01004d02c801030750140c0c075480d4010351180d000070820040085007000c2c5605800c414002c0c0700c215403120203035002c07150036009c95480460103000505c40c61400c8082400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 958163525 1250 958162275 958162297
    0x6100911070b0115110f0d03021e0a02030a1b030e0907030f06140414060f0909010603020604030308071704020105090d1a1303080906010e2403120c0d0e06030c 70
    0x45460307096107949502003800c1c0c208558050301d0344103920702039a1000310041503092007001b61030200304401405942e002c1c01d5050318145500814184034050101c40d1080b802c0c1e4001328082da5480211400130b44a501036100003011600c103590150181c040503c481d54410781c0f54482c80440300c1181c0800a8501008080c0700801d03881e83c0785080c0b8600c2d02e005c2e403002000410618024000c0d40c00400066402c4a1481d5045408140c00c1089669440b50f00380c0540c0b0003902d00790080d848940300035014004035003019400c0302c00014000105940848200d1107400c440d541e44a0503074050030141c00c0041d054174083d0000da408e10100802d481e00c107258814582c8a4280b0000040d001070042c04420812100b094059104446150a158000103850780c0500e5082c090300d41036040007000703141c40c0c00c040d20080b401a0b036643c2c00454034000780b2119003100401030489030820301881d17054605070b00001c480c00c8940070743c07442c110780d450150441c00a9400010110b07400c6584403908040e0399040501810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 958164775 1250 958163525 958163527
    0xb0d0506060c0708010527060f09030409050106170c03060d0201051b011d1e0a0602090409021e1f0804111512010f0b031603240b030402090906100911 66
    0x200c4200c104025100041130050004100381c03a00107903120003d03901007188003088804044031070f080d141c00316413558844071841045401c2c2d20340b100c0e1140781d0b0044c0d41203201d001d484d24001140d0307141c20400018000308211000b0f0100d0740c55024076070300c82c00709440c007941000c2604d25500c0158080c1020b4400e240000f80f002340070140b4880800c0c00d48008401110200301000340958042100f031000152050721201c00074124500ea0051035a52a40c40502401c9194041440d22117030340d650704003083c010b80040100111117000e08440100034880088a4460b25843c0c03502068503107145140b413020103041c2c5510146540d180c8a0018111418295550002540d541c41700260410b401074255009026241d84441d0705104544880f141c454100c1858a0024410000655491030640ca180c204520300441c02c83c03507103d00c1c0c89489407440d100089401d400e4801245201800300598852402103400b0025510b440d10019281c00054030061001c19403440240076441d2260840e801c01020f2207826 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 958166025 1250 958164775 958164787
    0x30c06061003020703360b07060f02040303142a0f0114151509040501270506090403050a0905030601090c0306090b01080414070909030509030c0f0901060f05090310060510090b0d050606 81
    0x70f002540306c0c0c0d0880204408041049000e00c803052003490342400300c0d07410461a003401e41d240a041d5204442c0754040b10180080c40c0d0204a006007070050844100d41c8842c60000000d0400d02d86451044d030002a956217406603980c1d0940c0c004004a0040002c640d48040c01501c04050080110840350380a116600410903130f0030945551107030a00a00c40c2c000c40d641c803404400403075400110320402e0004c0c01d604000c1440990b6031100a0749400a6040c1070056981d8100300050310b200145a2001d030b40b40c0a07100c000a00887c4030780081c0740a0016540c1040700a440f03c03416001c03200b43c06243c85c009441013002400242212016024429a02c001c492195a8031804030042e00e4040208800003032010690180508003084009001c0c43c0450b40340080038950341c049010f2740c005104d2841004290788100305902d00500440b2900c2c1000b5053790041c00100c0c285002400c20b612960f0300804644101c0b0f2022407049801c0815103100740031079490401001001c0780642400b510450b4003400c10455 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 958167275 1250 958166025 958166117
    0x3050c03061504031a040b0901020703051606140c0301151103180118091a040902030d120b030f01051611071203121a011d0901030b1305030c06061003020703 69
    0x1285d011650340984c10100361809180c10f20140c40045c282c07281d541e00511512000a800105481d10000d526074480d03a80007041c1000b4000c0c0c01c0f07544440085c9400c1100307105040882c0e50045050711070000f500301801c0e030360040480b00c00c2d481254250b0345406c00e114807280c0402161035641060814508062110280b55211090700d8481d03014441c1c403955140a0405403007808a20084142c0807070f404c002903402c580101c5d80340c045c8a2402c00400c1400c001401c1001181d030b105800a9002038121102900e42e0303601c0e18020700040d6055103200c444031002000c064410a1304a192080c48d101500040e03150003d10940700031300c0c0000b1418401a83c03d1503452041c5171080c0300e5154420211807180d036240784005031114501c4500800010b180c0c0c0b032102c0303145c0c03503440c08a4112540701c0b03000340495441500503540e2152a11009100b4080050b6808031074100240c12805001d085030a03207810401200258224480c52500901248402c0e800001d407003051084d4010340820807414005040316095 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 958168525 1250 958167275 958167293
    0x3060f060a0f09090c05010f08130206160501140105040b0307030807080d090809040f0c0e0906040209060307091a03103c06030b240a02031317060703050c0306150403 73
    0x83c4488960b11400c140034024101441c500502080c01c3c8140003050514004040b204002c1c0b0707200d0b6210401c00c8050864503002c007191b1020840000c007024042092034654060941c2e59002c43c0d0007031a41c00040b842e403800d44030b41c0300e661000800910315940345030b1390b07030b03e56400c03001c0240d92032002406a4040b020305070040c07803000c3d84550701007659070010801300030071910321041094600340b42004810b030041d040700c85011811002c41d5400304980d03134200000c000e0301c20755020b99007150340070090000c4c103a008041d0405036800c20407101d00301019401c4070a40b1703010446000b00c51002107001000303031150908a800031600e404448601c840052000d030070207014071259807103a80c01510410440030350f15110320000d100e01155961100490b6075516503035480707402d24075111428001004100503008004503681ca080b180015039600366520380829070300380114010441e502484000924181c07107841002d04c40c1d00c400c0403181c21038031070380c0510807180510909202003480821010001c500580 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 958169775 1250 958168525 958168529
    0x7050406270b0112026405030403020a020d120e0f0d030e060409240e09061501092d0b04030c05011b0f0f11060903060f060a0f 56
    0x10210500101404010306050080d0120000080c0d2030003200c2e01c4581c1e80851100400b0108090160300c1d0698000b00111030710000e003040d00c0341105982000d900342c605c001c414072000000c0000341000200041c1185030400c40100506510b0450500407401c1c1d8014005190031500030310440d60f10700b28030344c003040c0c4014801c0c00959401007412100300c54140e101010788688002500c0c0b154122803101c000ca022440c0f0180c00a061050301d4443d01800d07204c5030203980090415070380a01c40d280c2c0c0e044440000095105404009000403d400300d82140f00d980c10900414841000b0030701a541d42e2101403043c00e14508040c1000b0a84500044004615400042c5112180c2060010503140040c034230b00c14031242d01c11180e65100380410800319100d03520ba18200c0740c1c01c0c01e040109408060300c658480d1403041d03000308846544008001070040d01504c1a150612a120448203095032404000b054082c0704402035159021000265a5a44461100780c1005c006440ad070b00e01e0b920394030054100c028070707 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 958171025 1250 958169775 958169789
    0x6051312060b04060819020405180d0306030b0a02030c22050622080f06040303020a09090f05040317010b07060e10050424110d0e07080304080d08010e090a1407050406 73
    0x502d250881c540b0b0240708240042c45900001e20030103c551210b06584051040d020740700d669900002103545941182c03001000307150009541704101f81141c0a00142014001075404003400b40020b00c0381e080d40e1003168001c24141e115103003000c89594080001010185000040c0c3d000c001001411303884c0c50b4050860401c201550443d0300c03084100d610040e0320264400000341c2c1c00000b101a080c1004600b0581080d09450056502c0c00075400070741d0b000e00e10ba0301030180315107484244d0a01d02641c2e885280101d02c240d8405541040071056030b090190280a5080c1c0d10404000000c00921164005100168840260381c801c02c1c180b0a640b04031001114255010846181c151800c0650020389a052440c407100030494202512001016402080020000030342d4460080c0d85d26241009017000800229048a83c0c030740d120000c0644071003820a1450128040034000b241c2c08610a10140c4502c66400c001c00300c0848a0715440c00340c68a00e1140400d40c0070310308000c0b03116240d40c06484054440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 958172275 1250 958171025 958171031
    0xc0903060c03020c1204120201051303051006031a07050435010c0801090e07150507020d060b01020c0301090f02152122120806031509070920040605131206 68
    0x4e030030207080c10905400f07500030f4160700412090000701c5408052807007007034080c80c00039103902e2103030421004c603c0c0503040500548030704c040c1200c2c40609604900300f0380f84201400f10307200c1c41000c1e008421043c107842542c0422000c5c802806403041620b201021410f54144095260f8682040c0c07d846909072118003025944500d10701202580211115005004c100d03410040c4600541549441d65501d020f0803003511490354881c0e03000744c8114140c075139a0390000d1845d80313401964a0038000a2001442c43c5001d0b001d80301d0511900e29062203891410741c2c1007103d402010006078200142d680000c19910b400c81e5003402030100d00081444101000f001d0024422413a0900100c902c41c0c44520b0415000c031031b07100640980c005500d21401f50420741d00e5040c5000c280c0c45141c00a410840c9084400380c9810301c120410105410006800d41204c100e80c3c000c000454000341e450030703c5114603a04a03008601003000b0001d0a22400041402c0003456113a2907803180c6541882410345030042c01a905691 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 958173525 1250 958172275 958172287
    0x19060f0f090e0a031d12030a030b090c04180c03150f0f090b06121b18102c030a0f05010f0b06090f0409050703050d110f07060806040c0903060c0302 65
    0x90034414040110185401004a110b1564000b0304071001c2c561140307110f0b45e4450540361507403a40e0740b11402503802c08058949900304040010000d10104c00d0740c510422808021651401c030301001c403016284000764909400c005100440e0203407100151140805607074402d000200140e9140041c0a404c440165208582c90b03c00d01c1110000b1030b4002661262510660412540c0c500007151003400400041030515501c80d170550801700101c270407104c0c02540014161441160340d03405e9203181e460440c1c040d2800650800102c400c1c1e9180a2010740e00000320310200c900030203010308002e60718401012600726011554400f00d40b901c1e040c4085a03213a4542844480d02e40c07442c000d902036500180c50040c10400c02c1c40c00500000c40414110340120b5071403007440140310050003401c0195801000700c960750740301010000c040d400c1f8031f1842051800340c03240b001e4803048081008000c0710381036a100005601e0f0307401080003c210070180c010a2201800d800030000720303d030290807a60a415180103072282 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 958174775 1250 958173525 958173539
    0x20d03050a0605100e0d150204030c0b0708030126100605011d0f0409171801180302030a02121005100f06090302180c0d06080c1e010819060f0f 63
    0x960301818480d111402c1040a0000c0d4542c42c2d5a40c80e0041d051504401010205000c00c0c070106200d64041d0088051a1181480040c1c0381c000b001101d10030f00014100b959a19241521401000f50040660000b00010000c017040001c0e4030342d0141c2240c181d564060084001949041c038803880d4a002103072684801c10880d0f0f04100c4181b9041c0c0c0c2034504498200741c000010b8500303c4c41e03540507441241d40d020b044e82803106028000744034020040000f5a1345c80d0100c3c400c0c400058540641d400101c861a1400c1545040b075864030032240d000c0c0003055007100da41d003001401456015180301790302c112113a079054800c1e0790080ca400b9603143e108e660100b6091454954030204680c00500501a0983c02040140c603802c0c054421101900442185500c0d2115881d5a40c41410071121104d401d1003404143d91501082507140b014088500a03c92400d8100a440e076040000352540420002e40002c2d002c81b00c1c1c507594142c950902c2200003003043e120004450b5058403074001c40201190728030144110 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 958176025 1250 958174775 958174781
    0xc100203100e0f1603050c070611090a1208040b0f0f070309080d0201150e073b0d050a020f0f1005030402030105072f070506040b0910050c0c060c1903020d03 69
    0x4600703814503106902e821441d03201003c0844d1390b014100f40c1c0c0d405c0020b0014240b1020345090382c0e0301071000d005400c4040c010200a8003c90b20003481074003c48000940c5000d5901286070f200d502c44003035070400f8603003801c0751800d400c20044240b450800300540d01803c3e2445d0014513480c1d109494404960b070410845030720348a44115003105681c5000240740d020490716400e0001c440045103520361581e10164111900041107134258006919201604401e0401140031030076200507401c2c41901c20300342000c00c04042000540076006402846005015003080c0d8403e10940c070b0b010308000d900b00b0079000401d9030104000700c91b80000d400031080c170046113402e00805800082e00d1030410000c0081880c4400c101503050507049551218030542e40c40084103200740c200400d4003c041989603035980480300d001d07070f110300303140c070311480d020344084030313014041c0d016250002206401000b10305900810b0020a61245071103100314810ba2000000c0b00d5042030f8891500b511a9004e000e400d120a0006825 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 958177275 1250 958176025 958176031
    0x80309061602030d0e030904021c0c02011802060a030b1002010902041a03151323010c02010615050c0f0703080901120501030201050307031113031b08030702060f0c100203100e 77
    0x4545000c620300307080690001c20b40d0b24040c3c11100020702213001d502000c3c5184181d074030458106001080b0400da041e4044100d800311b40d00c0c0d0109100360386c88410300b28200d401c02043c502180d00a0003101e005410800050403400005007000251000c00728001443c01848010940040c0c1d1a050854114102030103801c03001c248240c081e1403110b105500003030f02e40390000006000c810748180011214035401e40c81c5d042894004070744c03198002c80b0101d804075828408401000c0356007800ca2650701c0b01d1051040d00d04641c030030410340c490303403c004108581d1980f01c6080810303244240b40b440b4113812401d114a0300210304c42e0f144160b541c40c0e80c0002410517801c019900c041580780000400240c1d030448103c1ea803000d250710380011400112040071025004d00d008044068244050200c1000412410564407401e040c0c4c4500960366580e0300166244180c54000350025410312148608041d0a4040e10780411140144c4101c001c40c613500104a80089070307070105060703000d40100704528061083c030390 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 958178525 1250 958177275 958177291
    0x6020d180302040c02120c063c06150c060f060d05070909080c0d090302031b15090a12031706180f1807030602031005030a0c0608070c0f08030906 64
    0x4030840000d5058112030340512020b80150744540649030780c68402e111007005103100000312030703d03500c00e80c5085545030b1044444c18400c1c51500c204062850444044200030030a461510b514018104645a2602c2c406050150080401d1140c0e0b039281c2c204901520320902e03824003c10203440c1100e200c0350001409007009000c3c0c01000340c94030104101180302c038260751220b600856030074558900502e0612079030091903068021040c40307992160380014a40d00701c80c000c4003103841e5104e002c10354032035100c51400380ba9030007500400405400424038025140c000b40041003240c3e042da0f5113510b914042201c800c04ca0005220701510b6500c00842c040c02e6400c21415145840300060904030b40c921000007820706140c5508510000b8000b0b010100a0301051910500780d61850343c0d02d151503c080d400644141e03110508540c0046040d00700010014100780c1c2240a540b0914504407003503d0901c409170008040020000d0714901081e054140812580d01c0f80300b11a54074505604218184171015044032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 958179775 1250 958178525 958178537
    0x30c1b0813120201020d03200d02070501050708010530011119080c030a18021c0212011503081b07031401050a0b01141303023708100c180f06020d 64
    0x210140c2d0b0b000540140150050070300194007405925021100c615031141d0203231103a0300243d070106800007600540b07202c1c1d118000902443d204c0b42001d03900c00d0760034092a504040044400e0541d1410340780c0001c0c400c10070080b001c1d08003484030401400e48a40d500040202c240014550465209040402d4078a1f44585020802820b02400c00340141c800a0312000615031200c01c9180442010705010700241c0d4024403442407240301c20091a078082541340241d12880700403d03900219107060250300f4607240e45540501980742150303202d84a0341c11150014040701c840380d0000d244440108010b0b000355014000d551000c42020180d142581c04c01003039100c20504001150300700ea40c00000701410400c0c0c0f107006a44520b00c1c03001c007554030011640040e5002e0108100f046041c078480308064600b0404412100c42c82e4200c04800001c18006d10806038650f100c240c00408810641d840f101c15080c16261406a11991542c1500140c2294016080205c00c10704104212031701001407907060700c00c50400c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 958181025 1250 958179775 958179809
    0x180612040b0613090804270c022409030a03050403020a06110d0e010b1e031005010b030604060e040b0c0a03090f1209060c02010e040f06030c030f03020618030a030c1b0813 75
    0x840d05e0340120710075070441c046580c1d5080410b220140c183c80c00798406110800101c1100c46000759601d90f281001240c14200e095110000001014804d10072840d8000551070402122000c0b00100701c002e0003501140100c0324104001000c5000d01190f11011000c0305480707150310025041201c5c5110101c03034946e0b140210310212a03c0e2600c61400030f4103c111205c100405a0300483e00b03044410a42020403440c110000c1265040720380558040d007030690b000c00c491078031140c840041c0841034502510301d06c0343c1d40004010b141d45000500b188203445c50045502e01d65503540104184040340b040701c03002e00d185d41c0150306a0303101c10307414000d090324075088044039402e0b00003800013504410100c5c080d64035a10038940666141d08101c0c01154084c00c0138041c80da40f81804440005145400c0b40140541c202060b88111284582c0a15600100c040c6180825898080d402841d40b2070083c4180a40d84209203d1417000080d580d607024018650b1991f03861081c20298100c1d11070390890200d441401142c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 958182275 1250 958181025 958181033
    0x1903120204260123040c050f0901120f120e13180f06200c060601050a08010509090c0916140403030212030c0708070303240803180612040b061309 64
    0x95445500c2d008030360b0401c1810070a00003405402c0303090a00883c0f280322450070a640d00c0090760588940c1c000c0b04a411800e80300d500708540c290040c54030301e901c0b1401d030b00188100e4030400021600b40c1d10803810007003440915030b030b84a000311514441c0c40c045086030507207c0140c1446c481c0c0201941e03004108001c900e02c07001000700b51400907000a010300c1c0b070074024102040f9241e4001c192034000140c1c03000c41c1c00400c0c0402010341d8440a40754801d800381c0d1010442d10350250341503507829a09522000120b80c28001030002d0b0703030710050100501c0d1007200300c0068143c4a04143c640900040890040707012180c1c0c401a20041c1902100c2d00300403801c0004202090b0301003041c0782d44201c4c507507105982ea00c441d01c290995001e00708000d410110000b441e001055099400244070a801c0302134012020382c42030b81c5503218000ca02c80c0140a030400c100203000d90b0704410a02d40a0a0010305490500242000d1000140c10849040750250f4201c3c09000103446c00703036000c0411b50f02d20381c010700240d600360340c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 958183525 1250 958182275 958182299
    0x3060e0f0f2a0c030904060b130905010812090102010b150c0c090411010c031e1e02160308030703061809020102010e120d09030912050706140a020c130605031903120204 74
    0x6207500410000714050f840b0120620440d070320003d0080044c041c03a82c03110b4401e61076a2241411707036401354660b04002407a1907517000760f070304941c0c044020b00f12102d0030a8490165611200c1042d045550b1840401242e81e24540b403c0d07040c40a4600960700c40003018619441e00c8142440c2501c68040b00381000006540002500005442803038900030341d4903603180c01e841800d4440ea00c41aa00400848060320f42d40c00a4485140b01c10513030b1101041041c540c043c3d840d40080000c00468010320001840417802001c0155001482e40c5000240a82c0e645000c190206503040119a001e860f2001001507690900030b003c01500c0540180c90611549801d02c901c2d885130703a9540d18020b0305e961079081414060119131004044480380c01c00b6610382c5161203074072024030740540303c0413a52446017108030560900c143c8580040d075400030072500d140d140c1003140c0004140c800800741c507224840880d860720301780401c0f000800036801c070340c505106c1c500d8040c0c1500c00329125a0742440c41444201300b4521030030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 958184775 1250 958183525 958183591
    0x604060b04060b0304050109030f1d040c23190f080114030109020907050a020d091a090411040b0703030605062b0f2d0e0303010e0703060e0f0f 63
    0x6a00046119620000c500904042e5200c1424480003108100611006400003a041c6110b0b5980110b92081e01038140c8071146101d100e181c0c08249440780b07282c6420240d1041040c00761a00307020310300c6844d414038003400d2168003004619880c00441e1420035461080b45e941c5014115040c0302818501640000b010710740148903200e001d040e0381500080a460130352020242070740141041001e0f14004002a060740d000b01000b500500c030704030340b01400d14820a4400181d8600e2100038403030041480828100c4d4215008056200c1c0c0c0e41d0401001a9a8650051005241c482980390302c442550501030304803400f56108500401041040244920004001036000c0020a40480208140754055002451500e202c03444130f516080701a81d4001000c0c01207805140095035800414441e041600290360b00e11450b0300c00ca5100344018000090120380361070f8010301616000400c640d403a0441840008103803280c5089070351031028400c406c01e0a80f6038a40c04485101061210034881080383d030f941100d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 958186025 1250 958184775 958184783
    0x6030a15021e09210309040f06380c0a030f03020d140108101506270f0e0c0c0a1b0909050d02011d3a080402040606110604 54
    0x40220303055405800d9058550303019540341c1e0780410944050701c002d100d501180c41d46100c1d0150320f41424900d500051500c41c3e90311010061410040c50b2000e100142c2166400c07104999212400412030784101e4140300340b4020b04900440d1241e84002e200580d20300d0000c426800c28030100140024807800146c03407105250305150040b914002400110000d0148004120242d42010b641c00d55403c20038200e0b60680d10543e00341c3d245000042000b1045641c224640360030800000000c020300780c015a0300340741000f15040000f212000c0e2858003c035104007070300507107000714000100f0700c421800b24844551080905400343d00d0122100f0780d807695810413420041c041d4401c41d03d100344000ca507031004002821024000d002045540c60015140c0344000302c03400041d881c1860486400c0c00036030b03d128145070008054076032404465040582c0d12a00e0306482000302d111060b2800300100714040c0b034003031203850340c038404c00d800c007481000706461785640000200403a507104000c0c91940805d500f0342107580 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 958187275 1250 958186025 958186043
    0x1020a030206062403130b0a23270312010501050c101e060611060f0609130515090109030e01110706031808130f05090c07060b010e190603050c0306030a 67
    0x40ca80003030000c0d000b150078200d160700005c414414080440071a000b4024402e54100700141d840c4500c8808844011800038900440864440d40880300700d07034150740000a4040d074000c0042d8194138151030f4070040040200c698400100713007a6003070241000b05c0c0074150901c5c1480c50901800380d49036a901000207880c1c200c5556442a140c9601015000c1c102ca00c0171940500400b0360f1200c1c080d000c0d010300d080001c1603000302c10000f2035038a445000b9610540c401844d504203620b51003641c0c0c187c0d4071080822203181c820005562400c6205108180c4511042070002c5a040628034005098a6202050505008485070700e140300c0070000c545c00041e5030003444d0001d40c041204200004107280c0308001b80400500240982c0e817100704100c00c4069980c0750040c0c894440c0d541c414841c51020840b802d1100c80424042c03000001d00c40e070000c0c1041c0790145400040c00201c0e90014003404201c614880415150b81d40401855805000383ca611a2110340c8490440c40c002c03001c691102c100103001070050350 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 958188525 1250 958187275 958187299
    0x601021b010513150c0b0a0c140d0f2a020109021e0a051306150906050306090613060806010614041d04050a05030408010f141b030a060806090102130501020a03020606 73
    0x2012010f00000d16044101080540c07202e10064000248840103030350b259000c00000303d024006004040008080790b82c2d0f24480d40381c0801680c89a0020b0031514400c0e6260080c40032808041c0c050840c10300e21511258404801c1000c034504c1120700101a4030959041444046c096075540110120581101c4a065410303911000014001e100035006560702244d00304201603805040e03444001600c9812000d9a1210841c040a4403600694810741c400118104001102410150103c54000001800300c9100c0703196862000103079403030307500014180c0e800440104881039201c0800040100c00e0000d040c600b50030501242a030500c101101010f440405000c941000300800009039560341201c15261541d4540441da400787c4203032441d04103510b041803030840c107109019520a0040385156140703e8072034110307800d60340e8a80004180d21f43c1035030346840c0001c00c410305008841c0309816040006075103444400c859190070070150407950465010041c1c401c002f94000030503a4024404507582c443d010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 958189775 1250 958188525 958188547
    0x6090103060b0f2101050619260102070b090d03060f0e04032109051c02102403050c0a090b0108190615050307091e1a070f0b01030b0601021b0105 64
    0x10800d8400c441c1c00200740304c410058100311442084d00c01210030b00a20054403038000700002c0c4d000c00c901c0c88001009060041002510145515006203035074012803070100c240c44002404c9030000381041c1c9d074144200082100d15176040c480003901c0c02450a0400c1602e003085028851003441e80205201740c0c0c4000c0c045018140240d5000c4010202d4400444101004031000400b030714490394111101d224074810446141410080c458091145a000b4a100c9084425001c06002401101108420402c504a600201414401029500480090400700d80ba0010b216001101d42c0c0000c161518003614202143e03400703450f1581200c5000c0301c843d41c42c2d9500908400406055200d40c24541c83c07030741500101600403001c0c40c0301e0025600c0710428503940f842d1a2141c10080f200150080d04a00b0b402e20044000c10440c1d590300c08510364050a2a0311603503034000c49003601c9015a039020341c001c010000c00003c0044c055000e40300f88060550580c1e0070103141c1c0708510000c1c074241071080206999605c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 958191025 1250 958189775 958189789
    0xd0e0303041d0a0603080c0f150402012705030601150e03030c030708030408040e04061a010f140d0204181b1706010318021509041a0306010e1807230906090103060b 72
    0x181d40c00442e0b0940e6080904192540c50710002e00000481c01081005480540500c0d09c0364803881c3c0603125009000544405213001103428842d101d942d40c1282c0001c11661410448103028100b0740c40b055044068203000030f4003040014101d24070a91007001541c840010102c203170b0342510b61040301e59842761601d141c52110b038002d5411031000b003034103081004103004198112103010130701e1081e1001d0340c1045800455948150180080106402114000d00740d0700030302c0140100803a096005003020740f078004c0780c240080b41c0150070030300c04c0d00d4440c04050490580303d1580800c01c0d60400c0403404050103102e00b2003440c010041d606050380c074003038402800c0002413911512540140b1302c21580802c40040c0440303800c00511140154036182d509602004d95401c500c100420040c000c04507a0301e001e404482c0800001c08100d251100f8203800f80d0841401c02201000e090a2540d010583c401404101841010066218824010342041c01800c0e220240410b0640760801d40c04154109241c1c00300e03000e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 958192275 1250 958191025 958191029
    0x50603241c0605070f08100308180a1401020d020703151107060507090e060f0d120302070506040b0f0705030c09010c0204022a1912081005120d0e0303041d0a06 70
    0x521250500718108002e81940f0a5115145030380340e01e102c50300325560403038a0700c1c002c030307a40001e01c800c034641400443e0b0914098214074141d040d070010000c4584022030408203c55105400f05450312409210540c1c0500c072007020700000344010304c1d480b40746881c4e00c1042d82101078042e007141d07526481000854001022605c0b00b80e0056011b200358103103144010502c69651003040342e454021804540c0914007808018541c8400500e228500031441d191000038007201140a014075500f0410000056000c0c0080740c440d9014040ca14418640141d8030500c184008004100700101003041180f140440c40aa611501c0d007840d010301729003c1480410000c1c82a440c61502040c00e5085100000074aa4601c0c28694507139025602c04103901c01c0b0014065004000041c808100c022154182a1045407912b80c0412903020401c4803c0d541c50101d9244950084500d2950b0006174584400580140e4102114241940198070b840e141c2005900380c0f910110110b0b00c903911180200b40d00d00515082240 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 958193525 1250 958192275 958192309
    0xa090e120a050d06081908210702071701022703010e120405040608120a0c08091011011b0801170c060316081f09050402040207050a031805060324 64
    0xa900da4800c1c0000d032407030304600e4a04030f100e4140400403075150300118020400341288201c07131940e50f005594030f07019078015225503480c403c07514080b0000f43c180050f420340900e01d150007a104090130a03d200b03032500e003000c042901580c010040b81d8201d5031040c40000031261000c00d004030320f140410000c0c0c050300b41c0b14140690782c402d2251100000c144040240121101110100300895031109903540720444411018148103090240301d0b0341c1da0285c0c1050519920910b0028503014541e00000e9021010b45494000904900030741c50042109104072280300c0c00c0e40d21072044251240b40c0080c0b00c10380502500c5003041a401c0c41e801c0b040c034204040030364200020092501d9213070000f005408000c02c241180001140b0401203000e8000d620741c22a800d00d4504294806241060341071f2020f01006801240c100380e0820001d07011603c1440704d052518466655240c04100f05000101000503a800c0644100403c00c1800388804408022a00d460f41c01d038840080c0b02c82c2040054001e00b1041d0600d5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 958194775 1250 958193525 958193527
    0x30f071407121e0e18100e04020109080604030804061d060c1303061103270a02100905031603120912020d0212030418060e0c1c111b0c040504020a090e12 67
    0xc680c0d2030300320101c403012910541c0d07142c1103000000c420742404175080e603100004991008051000e0181100c2907a07000d0300604201102903503d60040c0e240a034200e42c150000744040c4180010040c0c5402100c070341d120600040d090b002e103601d8415885070005450020300c031100040346c01c18688281d04a900850b045181081402122031586000d94011940101041d40b6000c0b05941d1211142d000e0105801050041003c81c00350350034881100c0344a01441305108c1d80200c00241607a04010319113010400500000310301d40307186400c02d0b001581007640b00500c4071800090101c4040300b05a01c100c250100d9403280441002d00218814040070003508215000c0050040303419417801d8034245c25010b01c03075010007090f0b50721315959240d0710091701e20000d5a6810007421501c3e03180b425201c1d0713400300da00e40005026070401d5000300c607980c0000451030059088403010000340005005051140c441514240001c5c40c09038001141e40f502801482c071455a905220483c106040000e1540880034140b01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 958196025 1250 958194775 958194827
    0x51005040903050415090e150d0b0a0f15053a05150a14070f0215090a050f0703030c15020909040b0f070c080414010e0d0305030f07140712 61
    0x10070703540c007030300034200e11740d415450f44110584105110421190b200c1d0003480c00391110040c070203402c1c500340d41c141e40c0000c001891001260008903900e000e8030300688000f441d0318800c00e10205031200049180c074843c52300c0408005079221030721035049405003800380081548441c41d41440f8803c1c084006003004a1300003506081040000e40f200400400442c1c00b1169a2003103d21025a8885505000c04984a42c0811102d40c0900d511144481300c1d4015609058840d585032000050308443c00001680445200400e001051102889110103c4040d00080d4250389002e0411507000301c2c0240032542003503c070b071402c035081e40c10380e00006001440c4a4150401e0300703102650131410b07a6065004240b460115420b40d004d29556440c107a8000d19013414a450300c01c0c2014411841c01c012810b01040141843c5590313141d010650b4102c0c82900c55548134106003010720114800200440e05100c1f11904404003c6d122a05658410364811208086081d100e0011030300811005115045401c4035010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 958197275 1250 958196025 958196027
    0xb04060c14060a0213080c0604170c100509011119030c02120d031514010c030807020a051f0b06070c050409240b010f0e1c021507030f090f0605030604051005040903 72
    0x43c0f2101900008a881701c0f0307103549805407140c2c1c158449a90000302000b04002008800c540c440c5442c840341d00313070781c9040b0a030004580c1d501c0c00d0703d15490020310005103401c0305680003568516401000ca000b0040d42d01d108000c50540d0105000240a00030f042c164081155a00010250f9840000c1d042c3d90b008594072030041c3c0500300310402a800d8102c4c01c040411810a101041102130405035122500c0c11f00b44e460030343e0382810180c5810211300070040c140021990800c9041c00c103aa20b07910403812200644d076104100d1b8031801c4118491001002040c0104034411168800c0e507404490000c0c1d000203601e00b0103400310440e251050b400b0009104200c60100c0f40d40b051441c02020780714201c6040d1510f80450700b003034000c0c02441d441080301d1000080e04081c2950301c060103101428210307201004982070780c4690092481140012603800c42e003248035a2240801380100201802162481c0c240f010140407130100a02d1706000325a03890009002030004c01000d0700078840600101f0400f9060b041c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 958198525 1250 958197275 958197277
    0x40e030406051e1801081b0403082a0a0b1009110705010605040203061311250c061b1b0b21060a030c05010c050f100c08070305010b04060c14060a02 65
    0x1941d8881d240d43d450384083c0c080014002c0381c40300c500b01858405980d113440015120008040c1c01100540c1240d40701e620203001d80001030001e18000c0c036060341c40328508001c104005184803100103040c036030140a842845070015810720301d41c3d03008424108a6503560304120340101c40754080c100b85801c0038040c407108444c40005007080380c0580024040c0b1500d400c2408142c1c1700580300b0704e4010707500d2850b440903203104d68864064580d4404000380b0705049040c54000b0f1401480c00b4200c1440601403403170401c03000401d8074000b00460701303101c2c1f40885400361a040f981800308024144003000103c502c1c0c80c9410000c448060510300403403a403204100c40e0001001882110420704010b640b1000c00c06504d85403241c04212540414000b9100d804d00d03004443d0040301c0b5200329900d2044243e498501c8206001440324040c4100d0009002c0f104a20003e01e81e20010308074000303061510b030060043c1404a0308580580700341e0300300949240c24030f1803da040708401044250103030203410f090150003442c40d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 958199775 1250 958198525 958198537
    0x3090c150810050a05040c05040b0d1e05010305122a010c0e0a0b0f1606020f0a08160206310515060118060311070506070314070e09060d02040e03040605 67
    0x303500c0110558a1200c80b240c40040b5000e0a0b44c0603280300c1d0b04004500d05508a140444658600307030b8201a500c0c020010701d5001400c2d41040c8a44030000c45c080c0102540d40d00110303458184c0e007030056502d9500d0712502ca056001040903000d500107462101485d403204802d88486403041000d0b05514021100b07402010390420520000340c00d401503070841d240c0108810300341e03981c5807040c0349440c54942402505500640101c00e504550820220224a0ba80f010700300142003c50744965880305101d0003808000700400c2c1d500542e1089080340c400702e90003e61580e10200102c1490482c3c5520500040c0301030000c10b0014000359400010000c100000c070700ca110403c0000752446440c0c4511005562005051004102000301c04804000d528443c0d0050500c0c01c103008102850480152141d90801004450803000300e40c42d92a00c81082d200e800341141e100d0007d01d003a080348004480041e09541c005012a403007643d00b4900c010941d1745030352104031000340c11400c603581d031669403402602681041d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 958201025 1250 958199775 958199777
    0x109060506030a0b010e10080d0909150b160305040909050307050c060f0a14090d03030e0c040218040b13150810020f09061c0e031b070e011503090c15 66
    0x200c0040340075400c0018000780c1080d07100001105981c01c0840301054083c00411113080401c4104d0001584c200034058031a85003841d640d18150541010180c00c01d40f10240d054107640908440c08220160180084c0c80e00c028100465007903103401402d040781d150065030480f6401da4a00300d013400401c10004005c2200e9407207101074035150303805041040010300840c07408c3d038041101044030040c4148550070f000a0401d40d02d0711030b400c048210000c500c02030021241200807030b5a4020705180188200031101161000300c90030361410f2a84450b283c115050b810f410b5020717a44540328500c556450300c0480c0c100d5a2100c400300010140250010f44590311441344081c940103203010540400c10fa0b000300c85091030f071001e0880c40d140302c107002d00a05911809140051200820032103205094501a070040b07490001e0045858044010320041c0e0404201c01e1003100f076116490410601c03100c01685811508000d1035001c0c103400c090000d402601e03401a0042401d1004d20021506003405420803d4000d81 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 958202275 1250 958201025 958201031
    0xf0c0204051801230c031008060703020309010f0b010207061b080f0306090a020a1b020616030f0207080a020a0504090f320f0a14120310170a0b04080f1902010906 71
    0x10690441c2c01c040a1203400b104d5040b940400120203009800045401c501c404e4503100182c0d685a4a0302d0400200f940d00380e0020342c0000030302c445240e00740503c1e4011620003800f0009032481d000043c1d51b44145102d800284000711a400c80e210b0141e0441d440e04940288a1940d2040111005071481d40f0480d2824840c40c2a18085078041c0d00314400d50f050940c26403202c11007010845980c8014072500c5070100ea004000300028180c9900d40c1d0034102c000361007501d900ea035524200b075020b810080b5942000445501c003400d0403015a5800301c80e807084403025900040e540440b420b04501c409140340015040203101d40303c01c400f9440e070003a51107a83d1040d441c18003002c0d030101441c0e5103a49104611150b80d0b449421f400b00443c0e645141f2a007400000421505c403200d82c802c07020050340040b40d08000034458604200203500c41c5907403060081c42d1660207481c400000e651142e001d04070162001d851a0400f082c2800c6442190301150809090309203146150362203031100034080c2c00c1481088481500f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 958203525 1250 958202275 958202291
    0xf0302011104030c090b0609041505030f2a030a020607030f17090d081503070e160507030f0503090a0f050c0f0319020405091015170c0f010f0c0204051801 68
    0x14191050302c00303a9601c10360f94108540f50085c010080d2000c40c0c01c59901007800c00c03441c85566600e11480001c03c8a2020400342e00745408201810113400c81440717030540d0401440203d1400101d06803284070303105035007002c03910744030400428505420444002c4d0400400a2444203060700605000e8151406d642c40c0740152210b00840c401e02c12041d6904e034819408141c2c030b1000240070710641680b000340000d91703882e2075000000191911003580c1c004501e80080c40280940d039081da200e20401d0301e00305d040640c40c109082d035000b032503080391410410801c0f902201140f808081070190400c2107800c0001950740b1082030810075201c88082e61600d04c03854043c50540c1075401c010414890890282815911b01a003503024031000c0d14006100742402c0c0100d1640c0e28141c8a0741c400d01c00808486500c4e00182c40c01c0002c000411003084900c40710650100310012001da41e14490a50305000030302c1c00d049c1100d17540030269000841100c0c000d40c00b50912080013000000601c404199078500030003030290320 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 958204775 1250 958203525 958203551
    0xc1c020a0c1701200c060105060f04060c240e0105281104030b0103060b010f0e210f0601060e040c1e030e0a060203070804420e07030f030201 62
    0x4000c0c22401809202181d00400c1a40d407200120540b540088001050818004507003040c508269240455044800b1030144a200c20400a00c0c3c0500004d50300d0314a130542100200103036001b1403094500b04500c1a4000c020031944594a07283c00390748070280311410400c0000c00001d8852903040c0c030314661810000800301548030003540d840a02944d4600741e0300c540f10540d90098a0141c6a4158640003000000005161007080c0350013180649800641d81c050000010561080f2217400c00400c030341501d030b82c001585c8410070040d00014560080c181500c2c0080202d00740406d0a81c0e10724107008042c000520740e078010320ba08401d00c0048a0401060503c2c0c602615009080342c4103e0241e4098103091101a0181d40300d00855a000c81c00c5440c00c00541c2e0b40c04099034800c4400c0800240f00800780b20400842640f0410f6001001d03211254803050942d180415030b242440d0001210a140328000404010390f2200c0402c501c544192035003141c032400e00c101c025281c540102c005610302452504c1407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 958206025 1250 958204775 958204783
    0x7050f130b0a1203030207030e1012020c0a050f0f010b0a0f0918050a0b0f01080d0801051c12030b01080a020403150506120d0809100e030a110c180402100809030a03020711060c1c02 79
    0x401c0064540707002c42f41c07084c180ca60083d044404030215a1040c641c21002251082001c550200e81e11002400340000c18900036081d10050340015010712185075052000002c000100070544c2c0300b4140001c0c0c071b800000415081c1d92007008000c4d00071b010b041401004d02040090301d5110301503082d1031101c56681c442c04940e950300d0120341000000c900c0401400680b070301402d40c01654070400c09181c80a0b4507515880380211544107143c0109540748030042036940c00c4031809a203c668851f0460516242d034a8000200100810101d4040c2c0c1d02c0700080d030995501c04a28800c2404034080312003240f10341d50007402405090b01d031a4078a120b20910089424610b000e50440b070320200000c3e5052500e01101901c0d41c1d003605003026518060030b0603815030790320b4880040901c04190780c01c07200b5604040c01440500b48500040d43c1c100401c1908000c0b40d40b4000080300c900544038a0010395500c941d0809403042c4861001c91503000a0000310a100604d0010b103106110380d130801c0d406040c10f80110140d07a5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 958207275 1250 958206025 958206049
    0x30106060806180405070b03010b43210903060b04020a0906050c0a050d0e040b04090c1703160f0b1f030204091a1807050f130b0a1203030207030e 64
    0x1014822070b070007020f00d10700943d9080c0c0013807090b4102c0345a10b440d849007007000c0c0c009030824100d244c000b007103034860644010280a809041c0302d010440c1400d04c003110480600f06525150141c0403501d84160400002807191020215581100005851400001001441745120648250303003410000ca10070726051080310364400c00d64481401992038203009070341c5030708468004000741c01150f401c80c3c0810000e00c10a150101c031507a55a190380e00b65410001190410846580107a2131315403090006001c00c3c2c00c1000380d130310000010034090180d03081180b461007100b80140e800380302425003d0801c011050342e1310300c45201c0c0c403107500160307910040c008040d0625403088081c440551410409810254041c203110342c0a0800c6988100171031090350403020301605d00280b10780b000708035907140c40c2d1b003407010b900030f03104c00c503080b8121680e030700009034020162141d00d11314103544144213940c558844100900401e00040d03480c90840c00784c01c001d0004d4011103002d9001c2602803411480030303e440240526 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 958208525 1250 958207275 958207279
    0x70905150313020d2108010e041101031104051c03090e070203030a1505090907050909030c030403150b03060406021e0306010804150e1e070602060c040605090d060515030106060806 79
    0x419a5100031940c4050298070320141c0c1c102e021504280082000110030040c15489108500480d1a04170700041a0680c16403000002c00c0720542400f0024030038040002c03040b8400d01c1c000c2079204588003181c02a100c0c0d80c0c0019071160b080c003844901e401040c1030050b40140251124280d2658411803440423040858034040141c00c02c000042041c54142d0045040380c10a855000360382c2d8407000407410810096642c5900e035800300a080045103000040342da0b1003078442c80a9818110001d07071660343c174010340c00000c00d44481100780d82c40c00b040325400500d202d20020f00300c03041d138142402e0440003540010240c09044040040800117200040101c070f0041106a681c202c070307a51241c68041c07250015980742c0c000741d130700e407a030b489140d0b21300304100506100c42d070191070420144003007c0c030310708010381d03110409542100c0204030708100500242c9044404500345076542d070302c070000082c02403142403000819240c40c0100b40140740d10080000310300c1c00020b6001304911a00c0f0070040e500d465007222001c1d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 958209775 1250 958208525 958208527
    0xd09030201082206020f090316050d11130203010b0309010b09010b0a03051306061404050a091101210203010308120601020a110f0d081b070e090d03050916080607090515 74
    0x2c0003c1d10681d0390307850b5400c100211900b0320456540e20416030b404040182d05e1500041019003491a051200e02d08442c5070030004403e10b454a00820010519490007030b100d20000c2c00b030b402c801d8490858400001c0150082150f03250b840304854074a03508250f0b6804220b610300607100741c15040030514075050303c00700c00036242402c00c1281c04070050000149454007880d40c14442000042c000d0050038090b040c0c1100c0e000401c11003000380011901d00506803121142040402c0010508031103815100d21400e00e8840b190300030b00b461800d048103040c21001c80c018400030002007403040d05000307041e040100003008a00d0362901001241d0b100ca6003a0060803840f41c0c01a200400d24106410302c64000c0d002c3e0085081c51202d80b941c0000340c00060003da1059201d26401c46400e01c01e03c8008040c1015404403001401c140c89421754900322031003480f00703065a07000480c1c02c00804102252071240c500800649254550640b10344035607068624070040313100d56501080703d2500b00e40c1e84080c00140303401070b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 958211025 1250 958209775 958209781
    0x50118050903271302091207031a0c040e0702070302011409030601091e02030112060b0904080306010f1b0c060908120f070201230403055a0c030d0903020108 69
    0x40c00107489508960220a0180c1050b503250f00c55507031040c1c00c05001131005803243d032403000303000450040c2408100140c2017201c0520016180301e005890300442c0d8450b6821640c1c41c1b030809032551080350044045e1292000170401c000c2c0e0300046010541c1e2007a40c40c1c210180c00340b0340501c4207020300d4403110785c1500002c006105400d00d40d4800c0d141c00c101c160320505102249100101260b00a8005c01e6901031015400800d00209008156200754240d83d20111440c003619a258030b4000905207030304000058005101e618800d0140c4881c0f11413006d2a4110720601349008442d91080e885620081006080f0000704007001041d1010003a62280300c51746001c401c000131800c0d80d80a00c4089041c050420001c02c41d040542d00001401c820314a6415641d03800c60410724a0014007130080c50300651000340056140920103004070600d0741a5600c6800440310811909101103800e4941200e000c040b040003682c00000075200c0070000c81941907910a01501a044a0903030711404003902141c610804 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 958212275 1250 958211025 958211047
    0x70516120e0607330614150301121104110301090f0f050603030702210610060305132a031506060806060304050a170c0318030d08010e160203120901050118050903 71
    0x25261095032824070801c0200110030604440054010104282c18408036100d2030501d0200021f00b034156605c02819907142410154844803103800060008000f5203410503151030b41d4004810450180d0402500c940c0c503080c114005041810440b201d1b14100701c05506541e0343ca2064a02810300680554541259038007804200c040b40e59425a001c15403461110b8441003c1c00441d000f100181c0c4a02c151500d450b0b0000d007961005824841c982060b28030b0840041c6209291003628550a101d203079103020402120640c107503882d84082c090a055038041c3c84034140581c0703c8000d41c0c607151914111a01c50313400f488610f0100300c40c0213145034803000c10140450104180e440018400d46075107440c0c2082020303100d0664210820203076110017102042c1007540b6080c08540780405c05072a1003801e5600d4180810340b00e00d4050f0000704e60b142890340f46814070340309100301e4402070600c2550b0312690508122040c001e01c0c003480303490401000d0007010544c0c0c030998061140100c440c1c01c011810007041c629 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 958213525 1250 958212275 958212323
    0x605090c070206070605041b0603020a1e0c0c091e0608030a0309050708070303080f07050c070b090105091e010206011d060108060109030f05061906031703070516120e0607 75
    0x41c0c02c0e60b0220082c440741000405501400c2c2c4110303c90180c1010100d400c1d85179a1104800d03401607002e242c010f00951002c075030701004a054211440000100b240080300b019268901c00581c060442050100d0209100801303802504508c514092100700600d0300d40c00388000c85d00540200c05540d00200520b101081c0300c4d4019910030340c02002030b41c409643c0e8803000c52a0044551040b030101e60060700b0807800e020049011a400081410310500d009050b002c030503120500ca001d14800c0060210f05001180d03c5a002d80d070303c0540c09000c0d505018080703e82103000d0008100000d00511600f000451454002082012050031444041c0080c2c0c07910001506c2144004081a04200352090f000010408801c04030180502402c0580201d04140000c0c0000541403941a0f00700d50071700d1410000210008480901207402c1a013060f181c1d110000129154840d080718017400300740001c842824841c580c603c045580302c040d180e0102c1048600b0602859002d44074002e0600000e0603881580307110b41c01c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 958214775 1250 958213525 958213537
    0x10b0312040609171204140f0f09190b0d1505100b0708070204021207050307030c26061f080108070f0e010311040e1c12091110050d1407120605090c 65
    0x20144e81d400126000001c24940196000341c0403010030280e245820304000d081a2128238046e03842d58101115240403812260010300107511094400034035202c24802c0d5800794040c01d50041007820580c25505000790003440b40b00c52903005600d0440030070090003074201c0c850100da052010090400001e038850011503080303548103130b8005401f000350503080f0b800c1c019014402d0000303484403078507410300c0c00005003110350b010b0301c1d40240a880e0f400040c162806000e0441000c90b0700380c034200360350741300408180440481100c0d003105060403101c00d107003150030044070f5040c0c03100941110030b00c540e030344090340302c026991081c4818014810014000b10700b51000900e804800904040350602c0101d01d101e14102c000040c05080600002c1c03950601548a903101c040c040010001b400b4801481d11400120201c41c1d5805104205081b01c6044240c080e0084c1c50b805000c1c1d82d82004080d103034a002c0d00e940703141183c10744001109850500c44003d103921520051b1500601070310203682c0e0760060f0410300d40c091 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 958216025 1250 958214775 958214819
    0x803181c08040b0403120c03200a050f03040608070302030105060d090812090304090b01030908031501121407092c062101060501030e3c010c02010b0312040609 70
    0x45503651012414003030092000340010505960303100d155040021000b0181040c0313104120891441c440400d51104144001825030710448e20f80209940c000c610340f102500c4000c2c03280c0903240c40d0b400d44030030100c041e00441d41d050300c0d0340101d84ea81d000124101e1001f400b030258003c03c11302204180044941c4150b1200e8480c910003490a19143ca186403090001c332102c044aa100160522002c040350003003150320b074402e0905021081c0c5580d1a80160300000341004020181960086100e0703210701400c2e8441d5155007820404404061064006408215450000f0a06c2315600280390b0302551703013200c00d0401c11114811006455030340401c40c1070000e415a1352000b4018000d1461003903040e941d000d0a0103640000034454034080000d01a55081f0006410f0768100b5580f5034040c3c0340740c480400344510030480d03500e840480d01520360602e42000740305070f10961070a10b065050980561298240c10f904400700c0c0c00201c0080480107a92040b4042c0c080040c66071001004030080f01500c02c4151004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 958217275 1250 958216025 958216069
    0xa050904030207060f094a010306020d061706040b06010c02011d190b0301031203050c04030b0916030b0405071a0405040b06040e0c030a11040e040201050310150216080318 75
    0x61290749a04024450744100418007d82c001220306c01d0504044420300c1404104084813240d85403199194041c0501c00034000c2a00000c21071200c1460b544400e0241841d0801d031603d60705a5954965108412102126000d10b5070b0080340e03156000c0c42c1c0030b6550982c141c3d243c26481a054540701c280b0b6040228103600003411801100448031052806070142c010b0b40c020301d449600d941494940c4100d420100d03806d15180000380012140c001088605480d0881d0228580307440d4100030500c2c03d00b80302d05142400000e0000841000100510719000d18051070844444a03103c00c2000700a000b5111448050741081004000c00d0a09820a0540220080419003020740d40c0401c3c902500c0101c40203020950000f082004922083c1300e0b01d442011294505405c081c07d046401281c260080e2003c2d040c8400440002c025100d407006001c040c05030408102c0280b442c0c0c0704041e6840920b2030100200080035900402d00036000003c0d6504056078201c8003495418a10a12100c40341c0d040c507100810365 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 958218525 1250 958217275 958217279
    0xf06150b0406050a08010b04050d0b0714040e010503010c0f080109090201020f010f05090d0c050712230309010e01020c0a0b030405120f03071209110f0303070203070e04020a050904030207060f09 85
    0x1103000d014200809058440980c0c03201003c01c000e000c4001600700400300786040c082404070361100e46c001d450342c0e5806090001152901c81c4141d80c0c64946050540c10b100300003d011500a012400c02c81c101e480c140c000b400441000c031415200710703400c0301c0310f0706c0003860000042040441c6500300c04c2005006005440441c03202c101c2e0300d400c2d2400603e284441e540c482c01840180e1070100003891100304207252002c003a041c0e40d501d840e120603080c0304200f06181001400c10600001c2d00e44141e8048000031441510847d18482d0340c0c2326084001c1850214004240d80c1000b540049440705a4030002040c3c0d90215060288035815500041e0007a103c621849154100b1b000306c3e40010960442912040364807403420503001011420b0802c400903000d810311500000040d06032804501800d07040340d08902080034100403901e98060700a003c0d40c180710f05600041d4060151510301d004038000d4507014601c5807a4024005280000c1d50001e005030b2101c80100b0981e07108a40c000c85c5800b182c5044030300e00d9 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 958219775 1250 958218525 958218539
    0x50a182009161e0c1b08190c090905060606030a090209010f0e100e0a05070210140a0605030307030c0809010203070b010b030a051005010c02120f240709030f0615 71
    0x18212002030460b21414203101c0540d400c02100121422900351070207098443e207000820344811200024100203401101c01d01007442446890003030840748040b240c406d00ea000c0d029000c41c0d40c03400d0603120042c0223000401c0c00310203402144c2405400900404035a1540000e01000354001444040055900d0b013203100183e40c0c3c1d04d0414024882440c04404143c05e15010b40408003015204d402080900300382000701001441540d40d12080701800000c040e03451581c189e04011026134152580c0e480e0000c101c2c3c0419080c0d0849000d101c4441c1c04100040c3c81d14103040d980e00c1800800340104501c0441030703002618030801010000e1741841541d080800555810810400c02c2c1c000c854148400300403c11407005030b110b4282d20603001c0d0380351584186403030000b800d00d0301418406401910070903507600310030004120000c3c118000c40200c03040300c01d5020352005102c0440981c105400110004219603e2040c81400140c9400001007084c01b205030b5181d50091900540d044102d50110740c00003609 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 958221025 1250 958219775 958219789
    0xa0c020105180d14101407030b0d17040611010902061204060b06070f02032a150415020604120305040305031323031309060305030d200c0d03050a1820 66
    0x90791042a94001e014010b001c2c4e030f810300d035030160b407449a54a0301089848401003031181a41001e19800c000480c0140c000c04540540c9240601602c0c05860080400c1c0c200c070380750010421140580c0e1111800b0700c07000b041c1c90a0326503071034010354045024458010026003071103840390080e12030200010b1030050040424016040440282e0300900b08104c0e400644c2001e0280c00c0890445180c01380b0300d00340c0c074000100b9054491700042c1c0035110001441c8542004001141c02501108403011602066428000d5075540121030403503007005015041034016000f4022a405217616842d61401c6035100c070110700d11070b0f0495506075684062110944003440d0480700c1000b10a02c2d2101440da00c6e206480d114005040940c00308115034500b0108201127080442610000701441303001180c9449410007a54141c20000c0e06248480400075948145003000510802d60340c08544040c04642e44002c1d20b001114803524100c02680040c100040c00601d40002130040c0f010010440002101440702240c40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 958222275 1250 958221025 958221049
    0x1141507032f01090314120a0e100e0705190e0f07030204120b10171203042a060915020c22020706020702040605120d0507291b0a0c02010518 62
    0x700365900d200754814164810681112814004c4102d1f1134412061344182401800a10044d01180c3c0d80e05680c0c2480c20a007d20503030940c103030a042c003540c0a0076600e15155610707803007203620074502040d019003070104145004c82100e004421035241640c03482d42c13007009000002c043c1420541d0810022446401c1c805101050341d0099174000024074001980342c0c55950183c00caa0303560920104442c03818080080c10411484102503426281c0d05c9a1510300c200040b0350001d0b10581c14041c29140c5410b4002d03c0344011130f4040ea07907404032540e070b4482c1d040d143c20a1401280058001c441e40100a06040141d05d05000c5210b5804090b280703065104001c0f600951001c031a1280c0011f40202503142601580014100c212078460541030000d00c881e80c0c1c1c4215210144c01e00c00c001c00c0510501901a5115403120280d00d00c0e01810100c010100c4030351201250034030301c404200c500b0070b50144180c0084d50440203031912844201e8900c3c0d0015100c3c2c0d00035151000d01002d000814240a4032401d9001e10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 958223525 1250 958222275 958222367
    0x60a020102120c040b04053a050d03090b13151509140f131a040b04051b01200c13090b070507020a031101050c060702060114150703 58
    0x620b6403007008942e55540409403400b000610180014403e00800c038084504070b0b542251251000000f41c4800381200390702680030903500a0009002d09010b904685001e04184036000391041d4021440d0305404940300b44501404600c003120008218000d0002090741c440e020b007020940000781c58071407030309403224004100b81942500108000c0c401d07550203080640440001104c0051404030b9140c0e4040384014203c0080c44001c50401050014a5451400d040d002030f0120b0307281c8c03516043c80020700c1c1098400711818482ca184070807403034084129604250b1016503c0c410f00f04240c1e50354607054001500c0c50709085c000d88920700d03403e940714131000340000707400f03e404500c0d0380c035504011404c828000c00303000038410b040205000698507410080c090340d42c483c0040080502810048401e8018800e48541034416070080c80106600010801d0403650170300b42400300c4040e4542405011810400c440d1640340c810b2045c840024001c411643c0b1405003420007000c40300b8030b070f81c141c501c1a6020714845 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 958224775 1250 958223525 958223527
    0x702030d1809020403260c0a260703090e071214340507111c02151e030901090506010f0303020c0a030201020a03030902061606020306090a0c052205060a020102 70
    0x40e121554005640c00502c0142d0085081a207941c9640d13580700c22180c0350f8402c1003141c054074900fa00d85203055410702415001181e081c8005860000c0841204000d0120040313622000d101d00380c81100d04907580b942d41b6540d0106081d152201a0b0700c0d0100240242c0240a071450f90340141b02980c0c401c002c07180307404c100002c000c1e04103841805002100210781f070854058400c20712020754030460055024460342d103000769541d8110f007405040441001010307030f40442501100165030a0f24021300c500760b4000c5170550700308072031700031891814803400c94091480302c0c10900041900e601031024562010440c0d00104412082c1e9039243d080800980050728440503108050040c59810415841059000d07500c03102c5490079900040d60314900800020300300360700c0d80c5ca10021512454151613141415061344600310030a840e20101035001101c101d4010f02032900001c011030030a0080402d100350513241c0c0c40c0342c00280c0c50225800c1c2134070340c070301c84c0700c1c0060303030030006254803a03c00920f5030181c594001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 958226025 1250 958224775 958224797
    0x120c0305011406070309060e06190509041401080712080405030f0d020105070305010617041a0709140411190c0b10030302010e0604080d0b1c030f0f0c050d050f0702030d 74
    0x501140a100c0b1401406080705009820000342c000c008001070f118542001c000181c11540001c40da1302c140b0080e454020903400d2800301058104001d4920590116000e00c006440c2c2a401c203080002441107120350340c0302500400010045106c202c035241e00034828107240c540c68002203480d03d80401c036120615800300791003d10380d550a215280c1c002e000d45ca410702865251580060869a4000115000c5007101011804200400a80c07200c14080f15002c000f45141c440b502802e610103903c0f44580d03650141002d15118500b5202c0d030709250014202c03480c00e0a00aa03010030025040d1003550092002071803150b0085440308400d58400d0503511015403109095140003801e403044908070006035400300007407100141d18081916526100105c1c0002e40060000000d00c0080d500c00880700c0040b04c48008409040c0d000350000030441063b102c1801300d803030031b4404442580b5901c5c000782c8150440403550494501c1840248001034101d03010f1402c1c40d80680002e0f0600c0500706508010030301c0300607a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 958227275 1250 958226025 958226039
    0x20d1703040b150f0103020a05090a1806060912080c0f10051506031b030718080706020d092405040512100b010c030e0405061809010b041a03100903120c030501 70
    0xd03403607104903195030540141d02c03a080031402d204c120344130f80c0b8140768010542c4a6001d02c80c0c2d0549015410042031281080e54404081040c020780c000701110441c04c0400220702940070b000d03900c003160840c4000c1052440c060320f802d080c0340c022850600031030050402d243c07450141001004414a4510000603803801d02085141040794078020300d601491040c81080556010300f10030020070704000449031b0362070b03585030000c42c2e01035040100b281e45039a80c8500030800349000140c1d2410769116808598189a05001c01d48004d03550348502104003540600b0aa12522102ca00340f50040751800d0440c00d244e101c0303000a0b62040301c006ca002c0c113540049908aa80ad119002d140c201d50b10030f0800000d038001c07545004001c0079001c001c25000d26180d80c00300fa02e50711007507201907111030461010300780e90810114a6001e4641c501145118a052166a0600140c201030a40000324020012b01400c0c241c01e88203000340c000804103a05008040c00303000d9184996002e1502c0c01c5140d50340001d442c0d818104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 958228525 1250 958227275 958227293
    0x201090b0a0215340f2f160f120303111303080a0e100c170c010e07030501050903030c0d24060f120603020603040201080912040e06090618070507020d170304 69
    0xb10140b0340801303820040007a0300301c021241001c48904d040c2c0c034040e03040c06104041d01100003941c000030700c0500c4940a500400702e0620a1060b0390814a48000d40c0c514801e01080c00f203005d283c901020740d184440c0024020790021015031428a40795042c000f80c902c01d130144540c1c603403080d0b800044c000765400049510040444126004075000d5400e00c0031a68001c00c0b04515140c0103124030006104c4900981400d025160180c604038001c0c0308940110098988a03041e51000312095800c0102151004501001340c907c9500503505490030700004c0c1007294081c000c2000590110040087c03c031100301c0c08102c0310340c00303071a60303450f02140a8100c02004009070003802c030000d01b8515040c000e000580e03a4804503508a90246002e55094494050043c281207461542003d52280000d0002d0811101050140f10b845c2c11903140e074290b5648001d00c1501010600c42104002880000444607030180d0050111580050012050401d80d5503032100c0c000074a51100102d000084208000c01048503 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 958229775 1250 958228525 958228591
    0x1a010b0712170a0e070906060323010302010219030e090a1b1b080a05040e041209050f030d2601170120030a05070509060307081902070201090b0a0215 66
    0x101e0320480b190194681c01c001440054040d03041542c81e1030f15030024507002c0003030310040c15944030100300b55552010050003c045160240001e0700d590916050304005d0311889a040365010707005403881120900070313041001d40c011012410700c4488002e000036500d1711103c06106018100001500046c0708680141a0780c0d0428204100301c160b9100317034079040c080542c40ca202d1368030011060315155544410b490502864024070100c0e610902000284006100701640700503003615000d80850701d0307100f40000408031402164242d032080d400e0242c2244070b054101c0440000c1048040416607000180d01e00350001c0c0d1200c482184001c101e030340e0220782840b070004510240030240d400d040c494400b03084075000c000d00d42c806590340c0320000382e061401042200d031400c0000b0400e0ba81c9203440c00c0c000d08107210540e40c8103a0300ba2454cc2602007891341e407003280d40140d0161a00b5203c60700d8032414131003580c413a042600450142c0d5124076088500784004a006820101e055005140340d02070400007440d4103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 958231025 1250 958229775 958229777
    0x12020f10090305070b07090519150e3a1103010c02070f0e0604110c030705010605090112020f0d050f0619060605121308030903090f0a031a041a010b0712 67
    0x3003a94000003c0d041000c40d05501d620101c0034106580d10003040d5000c4285a10880c0c000b681c1011004685c0c4040b406807080da80340d4100c64003044010101110b0101c0608450ba800c0790141c00014820702c10190080c8001d08a080c071a1a40ca80b211003122081c8100341c0c2c1210803803110340e24181640740a00036041c0c0c0f100c00d8401401c55918201074002030960a100703c0c0c1000c0c071400045641a1540e402003c04c902e080c00300c0540d01e842072507940d5520746c03040300140c98552807c5070226407032914a18160480314034460606415525808014808070b0004030b45178040e80e40e030304140015009102c6483c00e480504040c105624040707902c070780d1009800074010700052a002040c040107401000340ca89400c0790302e05102d07a43e510300200301c2e10340403164005000c0c44408002c011107040004010300e803c002c10744032010b6921011090010a90890000400004c0c0d20107030a40000a003103011a4400e000702100f040394400712120301d00c0d0740360a0300400c40700180015150244074030b00312409040100c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 958232275 1250 958231025 958231031
    0x280c0209150d0f03030e060c04080f060402030c12011805011d1501091113030b1b040b03041b0315060603180507050108130b0108010e071a0f030a060312020f10 70
    0x440010b078010000b00c40003000f48902e0001032050511030380c419005800f034281180c01038148038042c502c1c240c1080c4600d60542c8120150381c3c80d04403002ca1a0303405558043c006080000f646020000c00c4001154600607540d40e810407c2240a440c60340c0d0003501380110000160501c0031003c4588105070314001b5072491340007404000b240d03043c26503020f046440e0070b50001040d886180101899124081042a00c503086c03000100c28425800079032380c000d03d4076042c001016020701c581004e003401184a492105181440064007042881c03001910120f8480800010143c43c1c1c0c1e2180b450312013214008622a07681d41090bc0415011300c039040308207031010b4a401d0350341d41c6036403125901d9100e800b5040c10400041c021034503018504d880b964400307900c02c419034030b907685803098a1300078400740c0c40420703581c42030303a80c0002d512421941d91000000f201e89164074111002c091000168009400c3c600010b035521000400b003000200c2010340481d0540c00703815050503841800786400e8004100d040b8240c0707 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 958233525 1250 958232275 958232311
    0x10803070f02040f0905010f0605010e010f0801031b03021504030c050a12060b0103020d1d070b0708190e0409050c090c0f220e010815070f08060402280c0209 69
    0x203481014080703400e41c11070700850044c014100e13884c00303040600c400a2603503003020681041d00540b50448001e032034081e83c9a0718101c40c1e42d07004454040c00320f5080d0000c1842d075801407000c0f400c01e000320b504255001303490009442c4d0341c1d4041500c020450002e14200c0030003140178010403561828203001403108031f61482c200f41c1018026141504414030003000307180c1c1d600004046074040d8054170307081009401c0800c18010b80580641500c11406100d1585000303818000c82c08505a00c05d13a1803082c1c0100042e4100012441042e8034202e43e0340c070721414001401000c0d03000d69140e0141c20360140c81217004d0050036081d1803d0003044a00608180180e040038044501145115400c0e00c080480300f08001103098074405002984607040c0d00440c9540b040d20001007001c400000e2400e02c0e07810760a800d1030307484e40c0d040c8040304ca28072201018170004070036102282451606070098000e17200040d00307031071038000c03032015007124100c40003074000204000914510035403404000d4154050640803540080007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 958234775 1250 958233525 958233533
    0x120901090f150c052719330818103306050306010e0a0302060414100807200f1e100203010509010909080d02030408191716031113080601080307 63
    0x10320601c0c040c071951031618903005030783c1c4441e040e266001111000c002c03403545500d40e8010801981480171030420647c1e203440362414050b007502107000c000743e80e58151a10381d4846007419400c0116046160b1145030a103411403000b0b03204072030242241c522808402402c2900015203449105003052014100b5034007041000c1d007000c1101d038882000d10b00685288110000030718108101c1c0c02c041d41041c40441c000c541704454200504646004440c030147c914402003080700d50030400c90f984c0f40083c20000e811684c00c0c1000c0c100303076071442c2d4203401d8418104071401101d142044030885011141c5982221095030b0300d090048210101040c541545598100004980880310600c05c1108813a0344d003000e60180300301c1209484680c1c507458402d40d9203091900309941d081d040303011130f00140300e802d0f5088003d60b802100304500c000324480010a50340c0d103500b10580325001807008482856203038a803480700784907014010400e803034640c000501d02034101080e507490140140c02141507035108003d980007203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 958236025 1250 958234775 958234807
    0xa0906170405061b130b04090b12030d0f1119090503032a0124180203190b0a050a260d1227080c0105061005120901090f150c05 56
    0x1c13114800b080142400805400c0445219003050411980c0c0b00c0200441e002c030081c0001e108035124030a00b030058611000401190740f40c0300d81503207080e82c000c1109250502c03461700205444c070740501c00000e16036070f8000c030f01186500c0000a14166060b0b00c0b4135140d2582c01002100c0030341025402903040c41054000081400306941550f103007007411905141451100350002021982141051000d40e14104840c581100c00742c01000c1c80503030410300c405601c078054800ea9100c1c803a8203900700441c4a2160f00f490090600307000154002038580c001085540340c03000080020540c480010f0105845075000c3c10740f0040d03100041295400801c0322a84641d880116800d01d14528607000500d14128107084009050b000100c464070743c1205403c1040c070400c1c5014004261070038009008030b039a02010070a01c0144201c0c00000302d9014001c12007021078100007154000b05120001841154507100da110708c42011070f0031142200344120031502d41c800307402800c2e001580d509040c3c1c00d20040d0410780c404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 958237275 1250 958236025 958236031
    0x1c062306040e010c1709030c030c0f0c041b03090606052706090601020a02060f0d0f02030106021b031908040306090f151103060103020a021006060f021b21120a090617040506 76
    0x120a0348100424206c880910468850410600031241e4400045150544844101d40e00804602071030b5241e20390b0b03040c94020a80e152640c03642c820314000c5114415001400011403c0d542c0d15a140808110358845507100301d01d1040030069041c14120070b4800c4081001d0060003180144012014018039036000600703004003d0341141d485440e44088011507074140a422682c0340e00608050014010001c41d6000b50b06848090307080d030791240c1c11840d01e01d0890a550380840d4041c1d0101d140d11510842440c41060140d20803941c0501e0280d42c1d0704c0301c1c0250b031407904056136420b4118402d40204080d015406810b0400b03c207003400305004c0340050068901006110a042c9500007a800902901c00d001c1070483d010060001c0081d00d440b00001044030a14140c22030140c0708200406020008001d00d280804100034028442c0b404012034000040c02609100e9910780300366019400c03038041800c0500000302d0559103400d011440c14030700a10b266254602c06c610361f12444180720214401041081e8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 958238525 1250 958237275 958237307
    0x3080405010c150203040605040c05031c050a050d060936110a080a030c020a0605120a0b030132011517091603051b01020106051c062306040e010c 64
    0x20780b40c40c1d081103040d2000c10365a070500d05100004102c104080344e03001d90f0245024200d00007010742c44a0516699190100590713002403d0340e40d550b500144280014152040585803040c1400c020280c04000d440f9035400000c441c13a10741117070562001c40e2840d00b02c8005e046419440314190000004075100711407440142480019102120260f00d91b1203c1c10b00606402048445031042d40c01c00908140e18614228410031003004000348003032207031050300e03100e047c0400786d00c14a860721330150004004410ba456055502c3d01c101200380544224a8000200800d4400041c41c416032101d07414118160801d610780c09596410111855200015002008001c0c100b564503488510b80c1d41c0c500540b00f102d1045a0035023110100808c60042031100c10729140307a03100c00b00004540c00580c00d07140b00c0e00a0581150783e11000c0340d550f9000c1030040308114051000059a1003d400d00c0055900e11103071041c0000c002a0140402c2e030030705100d144000c4281100802851a0348500100b000d02c0c0011141 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 958239775 1250 958238525 958238537
    0x2120f0606130602010506210c09090703080a0f030b031204090506030c03030a0c02030c030604031b03050d020a0c050c03070f230d0f140a03230702031006051003060308040501 77
    0x10416181c41c1c1c1114180c2c941c0341102e04a05a490000038080d080844200d801100f440241c8080294984541c400d02260b540207829010601424490901001440e2010300c1c49080c50001c04140810010301c6214074554030b1000d40d040050010b8242c0c4c101045441c0207074410402c040c4807290b40c5041e103066500c0018042070a454000009e4540b0009151844c2e050100140e1509131640101034802003070710035000d1710324000ca4102010b44030142180d01901198025404070304885000300c6840707205102e810502d04090150109034102d800c0305c140c0a0100301c0c170f0000341d418844100017180b4410b1080b001000003034100b01640211f242c0500c01d41d81001980c1d00e104103140b01c401041d58140c0b0000e029412039401d9401d0400c544403400ca41901e80c0095010100d010b90000310301000415010740b240ba05009400a01081d02d01c040320f08801d07080402d00081c3c0042c2e03000d10504a2070704082c0b001003003241c1808100f05445107818031000c2854541f80040001031034000070755046a400b42050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 958241025 1250 958239775 958239781
    0x140a0207180b04060f0914090303160c1a04021f0e12010b0301020f03010e0709061b0f02090a090c141e180408040305060c0708070b10090204060e100302120f 69
    0x1514030044407641c814103080c40401d182d40240a410b044450010051001550480c7c0c0b01c2d541000940380102c090304100001a210700d51000113070303541c01042c6403c0850b502d95848011f00c1e0b03c0a090401c0c044000b64040c881540342561141070340c00d128112004034607004030800341242c0e0038040b4060281c1d01d0000c40440040742988402c0f540503000c0d000b90b554103150360422900da442401440c0c0c2030f095120101d800d03540715003020340c15185a521081014035070311380c4401c203150440070116072300f282603500c0384c006899408985010700c01c09540803912684900e0503118002903a000000074803031a24103091269a0030200c0b80c920080102c000c1c8000c00d5202c0410010500c4103002c85180082006110803ca1204011301c00c6a000754241d510540790380414032503900c0f03250005400e03600c0c00e104540205100030791107900141e0300d0560782d4038282c1d114010b80907a00107a204402041e2007100d9440c490902c03c0302142e0103803440c03508610f8400c4040406503460301c00352504d130340301801c0703000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 958242275 1250 958241025 958241069
    0x20c0d0219080a14070b0f070501091202010507030b1903030320040807030b07180e090a1502040f050904030f050d0b0303040b0a1206260a14060601140a0207 69
    0x190900c0c140414100c20100b5103070741c11182e0b5800039410031101074662414440d8a4030002c01d1010980c3d44e50b2101c00e10300608148820980c2e003082c4020b50301c0795130300e0041c180000c2903545080044000c0ba0004902450a12009400c84418411250050720305918185d4540340160071a019030360f25090001d00510380c408100c044a44410014003410000103010404500015000003105c0c4103820306a140d030382c0c90104a403401d11525800c080710403990014840e00408520884e48801d43d0780486445a0150712490b5040c113101d09004101e55000a05011481d000c0312081c003d040107030340103020f504050f50014081365220095000708000414200091036940d0861040c020004080b00c0d12580c855140c540340ba44040d0440c80401d4508152b01d6444116005410844480403816404880407001c09103041c1020801581c45000701001d41d40000c0c0c11410003d000b464800050089180c40000906182000038818056500074026030344110b600003143d0090b51000080300b6450909011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 958243525 1250 958242275 958242289
    0x120109080301051519090e0c09090c2b0e0106080c030303040305130b030415060501030e07050111070909150b0306090c2202030f07300207030917061501050a020c0d02 73
    0x20b034205a20a400c040385c2d02407075004000c1c0c016264042d0b881255500c588010320030b203205800349aa0844039510000741b0030308100c006462000140511052401001c0c10606001da03400c2c40103090090343d178800008200400d11400d40a0b00c8030000400e0302e8035580c4006562070000034001800c02c20f0000d480c6010340444288d11004080c1482c10f107071603007800d2802051603416503003041c0103a450310600050941c4280074901c1460140c2024004990a010044402c0b10744064681c0040c410810b002a20000c0e0348034420381d4034095040d02aa5080c10740c24078003640c0400c4403281c840e40c001ca0078003680980100d04400c240b5400c403200402850f030180184c4680012041c444103441c07002c4104090300500140d4640320381c9007613841c0d000b81d11a26a440c2282000d200411113030500c1c000107500009104c0d0300030100180281000d48802c0d80c2d480c00d007545401d242c40c030010940c0040050240c818810205401440001d082442c186401080000c2d55007808030681845003004ca200303d802e40d26221 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 958244775 1250 958243525 958243537
    0x8010b060f032d0f070c030e100e0604030f0c0b0a080a0c03060321030e3405120721080324060307230a020c10050f070b01051201090803010515 63
    0x1e400964203e0708140004054001181e05440a2182200003404648250200d8034080e074561240409421a44180000851220054070038400c1880100c0a03030b45d03601024100540c4650f02202049910f0301d84018046090360158586080030304c820508160081c200584c89010302d180000d000802480881c05410746a001a1040b40b02040480c003c9110145a506072007980d2024844003005c40d0310543c1c0c0b640307681c0512071400000c4820205003440d0b107003509144814103451000d03e5484400084500d03e02c0352210006521080040150752050800c0c2513240b12404c080071940e800da07407211402c920006003d0340d0054801b0903079013444409242c000010503400b0740b01c15120320308100007038400300b05001c10104500704445103c060703443c190301700c8015100c0c0c1d602510642c03481c5418080040d081510300d00c02d01c130341400790300303400e60f03030007002e0142140681c209020f00c0d4900010304c4000490320003c400c69074140300410011a521604590440d0b2083e00c8005500d100c060a81005020f24 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 958246025 1250 958244775 958244821
    0x80c06030415110f07110111030d090302072112030e0312131502040503010b1215060607051203060a050d05061b0d14010503060f01030f0f03111e0708010b060f03 71
    0x800c2c105040341904e40501a054414600050b184024500642d824400c0e8410404280d104000200c0f4031032281d00400c107054800c0c0100c2e541c4640300c00c082e40e200d0f4208604d83d011280c41c3e030342d90b00501c0700e250700b130000d544424241040016039100b900c82d160704c1805454040b8161600104441c41032201c4007801550b004104008a4490050746001070360041c4110b602c0384d8240342c40740c1040c0c50034100074103010034803000400e2101485280503041d0000241110751101e410711003000401c0043c841400c11002078010207950b403401d00300b041005000d54101e14000e1a01c0c0d100765000402c0003c083c3c2e04106510450a120030030300305204040d2040c1c01304000ba80b801c001003c0444403072281d10034141d420480c162160f5581d0045800f400c01c40900c0081c1003c06247c650001103a1b42007032440f2214000e03d000826425650000c81c50b02d0040008080d960051007003a100701c110034442403000c0d0004000030f0000c07680500004035107029400e20003001400010228940280740307030f1612903004403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 958247275 1250 958246025 958246027
    0x140f0f04030323070903020f0f0d0212010618090507060828021c060503070e1b0c10021b060603010626030d11030138090316080d0306080c0603041511 66
    0x44490010981805d03803008900850000403442c4040c40d11021501c1081c6014000651080340c40d0204014410414003d00e4595031300c60b030100d4070f124031007007160082a01c128042591a014540186004540c1c0c0c000c80800c442071007444001f4a0301d88584003a51405100352040c919030140400003031050880c0004549085e4103540079141003504000d0460300110280d5103529982c1c0010414000121aa10203803480340d00300d01081c28446000d0038969080b1000c840a01d13a068400c6412a4040c060a002d000c04c400050b02c80c0c030707404201d241e5010000fa0001d0000d01c1ca081e5040003512000011000348080ba40c1100002400c01c00035512341d0804000d091050000c07944841c44650300a0082c1601c86102409401c039110383d5038640c80a1140540300780d54501c044400d0313442184c101d020040d07894003e0703034003c3c0245819041c200c406001c4520140101907150b16015048402550200e01c0700d42102e00c0201d0300e90f80e01c4c0183c0b40c0c4680c0042074040d800c0440c140800c02807100d0000d05a071408 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 958248525 1250 958247275 958247281
    0x105030610020717100e010c0917071d0402030c040c050d0b0d050a03051308070501020c01050f0702220e06040543030201141206151309140f0f04030323 67
    0x7100248084100010174000c00411940c0d0310390130300b603c2e00480ca00002c01c1e8080760401060004200c9001a226200150380b1040e845140201d001c10031156084143c40700342052109502c2e0038080c101082c0c004407010450220041c4000d0002d0085180055126544808012031920b480201c6800790394444140d070f24600d560700c0c01810603001007414082103407650074081003642d4000f4001040e60b41c1600140384640351803004503050f5000185d4543c0f0008240324020060711050703401c6010106128140141045005400e0211401a180802e69a01038014080881c0700420710780300004803850700440005416020f6000e091801c000b48592044884030301100144584400707042d04e200360f90304551034602614011883c021100703c00344444a2802140c1c8520306803a0000c40307881c03000703145418080066841780d001d400c03582c000140661540c444032098491810106d034051680982042c0b103040c100740081e444007000308020b0606a55081c0d00d0b4214044946100c1c1000c82000303094924a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 958249775 1250 958248525 958248569
    0x30903040905090a0b011503090222180c12050c030a141204030b24060f0403060b0d0804140a0905152103071707050a080309070e010501050306100207 66
    0xe4081e22a10061600d031401140f19404007007001d400550f00b02c03803440c00a90a24007000840b8100c510301c2d10601d42d07100d4410005071141c125960003059901180300300d15444070202000d8520391002580b0000303074602c40c0400662403802940940d400740070204a6105603140007854001412090f40e80340c8540c21050003001502000b05541140c100250b4519145010300c1d1546030003140001005080d150002800c21000394401c999080490703071000c01c0154013031011030f0559000b0004000d000c94001014001d10002d8003809464900944440310f402945403600f0b80e25010718040c4245034811035000c22400c0d0b5842c0e000c1c0001c1c120b6070108020b1070030320300801260361300d105a0560243c0e60000e0181c0581210917048140501c18002039480c02c01c1c180c2d10301c006d0208041e020441e0385c03828005040456801c200030398105101710b140544d40d04000304443c0c0342c000141c2c8646556a28070740144481d90348001034940000061700c03030030120f03201c00d0382c16030800519810041c8109107680c902c05000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 958251025 1250 958249775 958249777
    0x222180b0612090706090603110a0f090320090108031608030c13090603050c0405060a06050f07081909080f0c04110702090a05072c0d0c0e070c0b16090e0615030903 72
    0x480b006d454040c00103607619426016100819080d85514206002445800340200c522201b040d904e45002140c40c0d031a951000a850070009549940b03224400c0702010354104110414003400d0b1240043d81007070100b021480200f406d0700b000802d0400044041107414901805564001d0802c448619103240c81d03520320790081109100a84203445040c0c0c2071510343c142889268060040502480d040c40d040c801d06484d01d42c40f1402501344200e040141070040b50070740c0060140021a641550403801208a0042c980940b41c2c21040d00c0c0c5d004070b60711748039501000448c048035403401d64021070344040c0440108051301074ac04010390054100001c01101e0440c5602c414410750071602c2d1000600c072408a5100b18031605405a803095040c54181e404928280214031130903442841c84e6a883d030f0300d65003541000001526110041040345c03402608019003182c0441d0311894032100750b208081c01890060000486100d06e0060311501d90110b07581da103c50300003e00d841548040d00da580c0c201030100070b80e2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 958252275 1250 958251025 958251029
    0x140c07180f0b0a0308030903210f18061306111908150102070330050403120e06090d0501180f02030d0203070803070f030617010222180b06120907 64
    0x68500d84203107410890600e01c150680c80c2005826144150f0543d5600b0805070b00203405020320344800d01c040704070001281c89104601345800800801030500c418650081e030301c0907000315044020340d4186190240001401c035405448110703030070074002407400c10350000d20840b40c26505890001901400c0d008804c414030413443d04a5464207156680c4000d41d810b15450071304114010b801c481001c00c041000c82c0714900000f45850038052f0400d440010000f0116a50380020003c00c4001c502041407140c880b40c41800001c0702e0900c081e404064400144082c402c0d1542944501e00321b140f01024030009603c9500140c0701403401005005141c00d060300038400d100c004911034810500007a44551011055a240542c002041800d5448030041034034024203414503402016030781c040c001090490600162511511440016515803489000c1c20381301e001501642d950454041c410046560b94541148804030071000c009006202040020300501c147d02c10b942680b4090420f200000d01c010640e082 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 958253525 1250 958252275 958252319
    0x15120b060109080c1309060b030303130611070b04260c03040311030109030806061b07090b01020d17060d110604030302031b01062402031c06230907140c07 68
    0x380059444440071340d80c103402c881d00307504606a03070f08140d21214140c010706a01481000c0c04a495100030001c21b146030001c59400b002102c0e42c0d40781d8018040b60b44100106a0082d4030160300d00515074540350311001001e00024075103000c41107181c94900000020048402159211039912800624510354a40060005a41c800d08004004000d49414800c00c8071030340c1e07d510b030b41d90155904410850140c02528040000c1c0011194200c4880014005000035248100c0300050041889000a01d40011542403a0278400746d01c200e202e4400f0f40300f4005070b00200c100d032070005038486464034060304034030380d10303801d420000c04600032003010340100180160a41d155000400396006603a494260351040c40344425204241c24444804403242950303480030010307401200d28080c010100070400094440842c003529554000601551101d4070040e00c90420003280d5110005d03009000601241001d00000d0502c20244601d02c0c1400622040d180c005500000b5122035641c0c4050501080c024a11140313 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 958254775 1250 958253525 958253537
    0xc160f050102011505010f0c210305060f030c040c0314091c1e03020904060e04030e19061d03010902030a060c120207030203120a02160c180209011215120b0601 70
    0x4201544140b02d02ca001042c0316441d06113241c5008015101d22900b400c5410400c010f00740301c1c0d000b140100444850543c040c02030008240400303440182120000b605080c4905114415905240d40000d103a61000340b04460002e685040b012099009042001884003a100c207202041a412004144800aa2404030700c012803003a80c0b030011150f04e41200300004a00300b140031a4100c984c4aa4054050b8802c00350001a150b511000c001080b010100c03400c50016240781000c0e1094245540004155929495a010500d05000018044100802d5030119404400e640004269025040a2000c54000c1c09070383d2031585a05100d0003a080b00b080400104451103850300c0404c6140c82220302013a0943d010354245519030009149014010f0003d0402a4003130000833010300100b0584684d140c0710b0b10042c0704680c54000c100c0304c8100f0540c148602c2c1841404400b00e40d903040f0b05010f00c1c098429a0011f442e400c0000081d0700303044c280d00404030b181d000c0d100040810108240c0c0c14002e60342601c0704 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 958256025 1250 958254775 958254779
    0xf03030c12091a1c0203180114010503070302042007150e06010e0402060a030e06070e0a05040605060f1c14070e030a051c020a080f0909010f2304020c160f 68
    0x307a420840b140709041c2901101003480c0c5000c111040603001000740d400407010b0314003100300f0501c00c0c0d800c15289070042c46903420000000c2802441085030b00d02d50000d12003030035890400040d0726500c46100c00785c000d6403207543d0300c01900c000d40100180300000c404c0d001d0301c9000354100303103008903600b0714102e03100c514000041e0b10419002820324101c80c6984d00c00c00360b6580350343c00c0c80701d42d070045480c55040c5074a03100c2c03031150701c4414440d40b88141440e40d104088603a100c0200b141c400ea0a40c46640181d1822a007031006456810460b205210720a080c0740c0c1d540090f00c0b4051007656012042241c103032070030050321528214200c0c061300844070b941c0c138585651000c10816880d403001e0340c001030450b0b01c0117400010700c030b0070000c02900d010b1050050f20344402007a00c03403d007a60b00680400509440025803819546000f140080c091300c50088000255818440b00b8214000305100701c22014003000503081055456030111040c0c0b6500e0b0050300d0f02c5051061803214100750703500030000a90803c03000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 958257275 1250 958256025 958256027
    0x908160609080a0c060e0f0a06270e06210a0602040e0c34080f120c0307050f092e0305060d03020c120715050309010b010e09150a0f03030c12 62
    0x31010b04135007040c40e14054918044040c3e4060007a10180780d003005034a200b00c6865130301d06100800801c0d1903201c03900d0405280c51038038007141c51030b4100c2d482807000c50020b10601580c1040b032540800f0581340480d4500a200d540595050701c240b00c04000e00c41e52001d003040040310303005001160428801595281c40f1941141d840f40100c42000031f50014424100040d07084a44290440100440251101500c5074480312504d134011000c55032071101c001006800c2d03600e400c8102c1d50107031040c41007038150704000d80001d207184100d10a0505501c004108407030a50b0700d1071000823038000400400702d03000038216403a1804203001407011002c689804005100742c00c107400342008c1d641d8150301800702e5041034404c01010649110f2584410702c036203030010541c1c000c0500756000d4403000da11303165200d02d84516120300b501c40c8220340c10304120074415074500d681c13944407449811070603881c4194040401c020108a02e0712031980002d48020110f03100105141d0441d02040341035001d409620a80d00758110 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 958258525 1250 958257275 958257283
    0x31e0215030c0315120307050a2303040611010b060c1e0d121a0402131a1e09030a050106060c02030105100e0f15030706090e06040504031e090816060908 67
    0xa805009000c03c20006840542d03000410004a40050900d903800d000b00c170000d480c40c0c000341e4084506034440000341d8240603035100c10700236006046845650048011696030384a001c0c910480d01400001e210840b00c50310290850802c0440c00f5000a80f01c1043d01d07071042e6610600148040000700b00c07a40982d4002002c224440c0e11455038860f0380c411420980c40d000142a9411f61042d0f07511000300c50903950352180020110340f0305c3c0484000100c1d040040b00c04030f45a42540300c0040360020024038400394180221400e20043c40644151500304200c0820300388103080c4001060341d4130b4180080b844a8100c00501c000500950007000f5580d500300c60450800c0403070164030703000050640000d0020385d1200f041076001945590601030340d0485400701c0c0ca042d8290f04205c01098480c5006c2c4400c1d001e04e100650301040480302400141000e440c0907146a030004543c100902583c2004200365001d424071030001c1441a0031a07108551022124500703038400c1c0624000240251000221008000303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 958259775 1250 958258525 958258531
    0x91206180c2c070f030e01050c13090c0c150b0909030c162d09050a0f051e07320a0923061608070b01090b010306032a031e021503 57
    0x200380b4030201d498002060341d6400d4079880c2d620406458901c0000092001e0150038040d051115640fa03c0ea09072007820030030f40031f1035000745103160301c1c243c0210030071940400f860040d29042440006182c03003900c201d0000d41400c4a280303400041e60340a000138640d00000a10011b40e0368415036108070a440c108451b0709142c0d00c04c41020150380180d8008100381e101400744420318400c6e00440b43d40d91100c244069a00454510208695464191032609228003035180d01800d50100c64030340040c00700f80c64048007070140140e400c004800d4402a00719441c4e80d500003000c40400307816046004a4000014a80d00031110b03d800100508000203202c0d0f21200b04020300602c00c103103201603406a505100c2c680d003040440184004081c075a040c04503994400825803a0700419043c2d406604003a000816039003503981d018101440c0c1841040440d410039041ca0300c3d11000a5001d40301c004828461010040c1d980000c0c2103095800c105640c9910b2112100d814140300342c0d0004d1816940b5220000306001c11 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 958261025 1250 958259775 958259849
    0xb04150b1023041e0602100c120507090b13081b1525050a02031b0a05010302030a1b08100b120a020c0a1401020403020111010c091206180c 61
    0x8403080305a600290104515001c0c0b404000b42480d40d20900030354601c50200c80b510b11403840303010502c0f107590b06002d2016a044152000c0c409407095140041001c182d0501040c1401e9030350000c100e00c3c5100302105801092002191925101140c030641c002c0300e0b5910440020b48121603540517080d44502e1000c007040001080c03518440c202d103090b05404d40c0b01164203520040c0c500c01d841403861000c545101c1301e6002c0c40083c404a801403042c03518040c44410041c40d8100e880d03e180503a50398855110341a20420f180140c4c0760703251000c030704000d4114600c0c032210800a80c000c40b03d0199011514a03c0f03880d111071140c864a5913a01150600d00c241307ca034520f40c80c0e520001801101c0706030010300440384a4011a050070025489046c08105480d840c10290394000504000355a070180c0c800300d102100c680200300d00c141c00000507210740c00038841c040c0039003000c109100070702c200c030f5100c100d1012400c112846220600d02e00301042c0740d41030060a682c2108100305104c203580e0701140e4015503c038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 958262275 1250 958261025 958261037
    0x6090b1009140603060613180b150a150507050a020d06050f0f0c030711030712020f0d09050a152001141509150d0507091508160308070804030b04150b10 67
    0x7851050004600c4083e100c103209070723240d070b08003c0c0000d01048051122030064184442d2403c1c654929902c0c0300d10814298802d44503008248064a61341d12610101d85107802c0165840180d40b4000742081c400c00d40c003030b41c8081c40040f82001e0110681003648140c1d2040d190040b01d0740c41110b180110390003a1003010040c00d00b800002c101902421000186500d1a81103d041c0741c150340d1600348209415900b94011b0b0409600c94100c030004108403202d051090900403400760810b408a07001c19218401c02c8802040c0c19014211580600191980d48a05d20a42c0c0400d01040c1d9001d4042d22507441c11846201d490b07000544628a10032560b01c00c214001c050400d03e0712010700400e00000b4110000d0fa0102a82280800281c02041100010090144081810800d1502e10300c0800c0d8a58446d0754aa0080d00e5050002258844184203480d07100910340d45031112800d01c0040381c09a90001811300c0c0c0075406002c11f00101c41048061000c407101d05014060000707040c00b400364074010511000c109 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 958263525 1250 958262275 958262281
    0x44a060f01050904061b1107140d060507050f0c0703020901050a12171b0601080d030e070b070804090203040303020306190b0a05090409050d1205150a050d06090b100914060306 77
    0x58050b10f12900540075001c08646e9410905111886c080381a1102021407110072070f60311083c1060000c42c00920808030340e50541e134069030100d2040940c003d002043c080e61071000136540f60050b01174030340c81c0707000c140c4107074868030388040300e6565240300e0000380c0c483d03812480001928600400c50340c00307a40b410f00300300c448001c1075510f4100c3c2620700d40715442110790901807005860010070b12421400307400740c020542c07549044015030070300780c55130b0800e800c25080c54107002d00c51600082c24011075180403102980c402003402c0c00d059501036908001c80140c000000e100c10b05034107801441c05804110341c201e10f403064550030004520424402c10220017020300ac2200807a014001503c42c81c003001c0c1000c10880b034161384c0e90303082c014032400c074170042488540c680503006100c0c41420b9101d210074409415141d035110024043c3c001e940b01c1c0a1084440441c540c040002907002401040c0d0301c4002c0c16030b00d061001186240c00f450380640b0902902d05410191000c0504a03028010700000d4094001c0351 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 958264775 1250 958263525 958263529
    0x90507050a031814070e09060402100815041e1505030d030b01170423030406090311060c010609051b04031203090f050a0f230c044a060f0105 62
    0x7280301d603d2520402d0380010140400d480340c180340b030b951080038090042c650901a14003001e0743c02400d10900b0341d20610400005896001c0020b040381106c0c180081c60760b46007040d400c038805840351110380140c1018028800340440310b4524408000d555005d0049203c020200e070b03c070401c2e512419600da445105040c940718043e03401044604010701d07000e00f88546d06044945008001c0d1400c40c0c3c0030090400381c4504c441d8204040406141d910080d51500e40b0b052001800600d080c0805068820040320314044d95885104603a0040560002031000d9a43d82c401c8900904040740c1c03002008020540240d03d004a4804807401d407588046100704428404600314010440078408891210102c0c84800c00f244041000c4000341d4030426450240000c903203402d0024042504d6147e11034003078826450300d50b01c0c02043c0380f40025025540054010101c654803500304030070048076084180c0d02c5004000401a14000e041d20194007426a0307003615041d005503030b980e030049400c0011800300100600c624 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 958266025 1250 958264775 958264781
    0x41211060f1b0c060402042306011209050d0c0201021002120f0c09191a0a0818010209041103011d070503010603150312031406220b0a1203020d09090507050a03 70
    0x88502c0e400c848609a0004030400d07803241144000c03030f5011004000452402d400781903032142003040c40c0f00806c0460b22102d000800f0280c102d13810301c01500d6800103a0141544090401600f000444480000180340030340500c2c0b040c00180c0c018010301c8003450080341c144c000c44004040c403000f11801950307000c250085011001e07205503010041040211566500c0d0380645001c80380e18001240843d241800d00c034000c1c800703070b410584280350030b01c901c10005801c01d80c100e9000301105a9506085548031000d0700a12600750b075558030030b142555400d8200003400240d03060f5044443c1c1764054024688404801d0312080316900e00042c2c04100500c1f825100343c005000d4641380c4503e49446e240c0b2999604c0140c0704100401c0006651501c82a14000c0c580c0c284540000d03040e6840d44005041c40803880c18019400d01880025450301e07032008064407000a401d0060544103201080d00d0140c1c9402900c0d0410a00c079600050001000490444620310446006004507100c6501d00881214103a020f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 958267275 1250 958266025 958266031
    0x3060602060c0d110408151501020106120f06110309010b040b041a01050a050717071e02101d0603011202100305060a05121e07150e090c091201090308041211060f 71
    0x43d501c0c045c440000c078590304200c000e659111584402c0900c1c07401d08003945002a8040c2014110fa0411a08104030340b6a0815603003403d80196009901c0f803901d06084000d00140b0783e00c0c0b18101000410001504410f51092080301d10031503040c407a000b2400d040105840360780d48551044a414164200c196000d0b1008004184007406e00904224058aa40e01c0704405060542140c040014203441080004002e00300716078103459180b1030002140d0007007140d8040b8281100c060040b40d250f141603603070411030a4020350b100108141d60300e41e19401d9070b81c0d1003000c20308203d001c0c2c0035070306118806901038040d480c0b0a8001030041d11040d0300c1c200800c0f4035191002c80c420101c1c020100100d001c0002c0020600a88103060001c2c03402500c0c06101e069001d900d0307001c3d80100446070741441c00136918040840d0708180a26456904c8a00b841d00003803000d200301003550320541c60f212004041640019506224038016a0480c24035001140d01380d540c4404e0340c4aa05950700b103840040c07220501048590f0f0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 958268525 1250 958267275 958267301
    0x504091a04050a110102030a0906050c0304030519060506030d0e130204090c080108120f1b030405030a060603060c1704120e10120b030a0f030309030c080d0203060103060602060c0d 79
    0x84035a2185005400002080e107069a0300d4000e40d4048003844584198884207400030303c000c6280003c0c000004100f51010f004600400800003030f0f11858083c01c2040c0c802941d0082c003a250540301e036810760210600900c80c100c91071410003001801c903190100303446c008045540c41d0007548560500800c1a030605100c0c15541c0c0517070911012810150710303c00c6c030001003116120580755506141d20307a46004071101000711340e0b51042106101400b040000c1e650320003280c4000d41d0031150401400740c02c1d030055420881d05407081411030800d01c0159000481140e020b10010400700d03e1896045580079000c030500310003052080c000c1000120b8040c40c2800c4580103240520a07058504002600320301000780000002c0c00321440f81e00044041e1042c00c5a080c0201e000300182422581e902c00c1000d030b501c10140506a40d45202d1b424107020b010140c210b1a84030b240a80e50f03444415100000790010f0710f41c01d0000307113000c0b00843d00310700001d44a4003410064070300354140100311031154050414803803481c2d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 958269775 1250 958268525 958268543
    0x61517070311030c0c011b02070b0304060e0d091a040608060603040512040b070605060a0e0f0408041809060e0d090902131703030702210301140103181104180c050409 73
    0x19031040c0b030741d82c0039601420300403840c969103004a01242d8255803402078038003d03481e4011304103446a60006110710071600c642040f81e4481d541c50800c0b000514001ca404001030040028546950384c0c04203408041e120b0000074504541000a40003e880c0100d00500c1c0208a00801041140c0341900146034824810401c81d0301d5400c1c0012480e0480e0020b0340420520600418203108006860280c0c0d0790008040d680096586d11f0301028844044018001d06052070f09030700483c041c8807907001280d000d0501c1ca2001d2000700c146501d007100500c8009400c0e98282d1a040b003481d45a50081107094030608955504001039081c0a15040258815003040a43c208614400a071201000b03089204900000001c0e45e120320340110040d042100c142c86804de0169000401300300c4801e01015241901c0d03001c2400a031100c0e8260040c0c0c000e01c1c1c140d4196240755504541c003c01c0092000d959a1400030540b410300c20511040344081c2c840302900001046510394040030302c26801c0c07640c00040002c0c0200f002d9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 958271025 1250 958269775 958269791
    0x901030203130f0303020307110a0804060f0c05010c1e0203090a0315020d09060f05092109040e10060807080d090302040903090b0d0204050f0609060901080426030a0615170703 77
    0xf070040e12000e80460100350044100700403213401015000c40c1101d80d00c05045051408e9036008400e1107540544418451488000d0906500c2000a140b25aa101000300712015000e80042d14089152200c10504c40013600c81243d203030b01c0803056800501c4090904889142035645000455a1080040003020781c07c1c000841c100c0d645000d040d40440c00703490000b5580c00179401540a540008120101030341c400700c90301c07201020b00003d6109100209642c3c5459960381c40004000c0e121210b9481c00360300c2018104406a0800e038400c10032070710f4120407114450794808001351a100440c0d0f035100031461030b01040000d0304080c0c00c07042903030380700b031400003031850715040500216003240b03010035512940400d09002070309296820154080048418a00b4841c4280004145200f0075009a0400801c4c2c0085000c2040034404104501e00d10001980d0206d19101a249039400c1101d0a8002a013003c1000402241c42c00e4810480d1800f9542d18100320b00307048100c440c102019100360200f650300d82407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 958272275 1250 958271025 958271033
    0xb1e03030d0f09050c060301050a120503130b0a0206070f09090e010b03030a090603060905100504091557091a0d0c0806130c0c02040203070305040213060308090103020313 75
    0x754900c5060030500c00186101d01c2d09219241000451703c0c603025540c1080148042d81d0740c440d00c1c0e8110348074402131090780c1d90740385402d501314001c40300d02949000592401040c8130341e412029111490103a4212070303442c0d0750010211150365107000c174040814004c7c201400301a01503088005090b03030841c000f06480540c84082865a0321850440c0c0c00502c3c012414441a80d250142d00002d00c1c2c1040b0500203814610304c03600300e00c401841a94865951005041e04206010a4854009840180410100113000d10b4403814801c0c041c00c4c0f80b20401d411810b8540d05e01110440410104245414a203030b0041280303902d00c201400d816074042c000d1140c00000c0070440040d1100c00d01c1e070400c01c46034496441a00300c505444c10500400180304140c0c0c00c00c6400e0700c4110658810f25a520000b10f4081c03000d01c020f6803140c8076444080d405c42c5c000030402c54059010303040783e07004901c241e41c0b07038501c1c03155010302d501110407070700008048400030480007013158800d401450308200c200d81600c0e548031180c1d0f1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 958273381 1106 958272275 958272281
    0x20f01050f0c0702030a0c170f07080a0f020a2409090507020c10050d020f0901020d1b02010309020f09150109060c0b27060109020712030b1e03030d 65
    0x10f0004150b5030200440c070705a5405c031840c442c1d46512004032032030180040c8104009407154030580c030949a80000c10744c6c02c8625010151900c0c07410365403030000e0b6045104080e1380c0500b01081c0821084905403918504000501c90341403a282d00e0f0f50080c0c08502e00744d03c1042210b143c00200040c40e90080f60420b10b100045811030300151610074251240c0c01108403003440184007080134034415080000904104000340c007140d0075401c1038101207030260b5518812941784049191104c0040d402500496041d910003002e64641012041c0468201e000440e221075400c0ca90b504c1c0000c0558120101a0240c030082c07503c3c40c2c00c8501c589072880142c6000e0062450f4443d00101c288504442401c844d80b010aa142a00c44a507524801000a50001700d01643c025444000c0c810320369009104902d1720150192001a803980200440186519150320403505400100050214034a8600c = true := by decide +kernel

theorem cover : BRFrame.Cov 958093525 958273381 := by
  have h0 := BRFrame.cov_init 958093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 958093525 ≤ n) (h2 : n < 958273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
