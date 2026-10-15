-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4084
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:31:16.78998+00:00
-- url     : https://prove2.me/submissions/7d5dcd1e-c090-4797-9c24-00bbdd121a68

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 734352517 ≤ n < 734532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 734353767 1250 734352517 734352523
    0x110d090f180f05010b04230f01050d0b0301060b0910090f03060e0f010603061a1e041a06070807170f07060b2704020108070e03100c02190506060f010908 67
    0x1c8aa40741103034000d824402100503651200e150a4690b140612080d43c3d0785401e0821030304180154040b900a02000c07040411243e88803500034000503052061184003000155250307041040c01c400b1194070303a01c0c5801d66940a00c151005404540340d1140c80c1c030006011f1104500100b400c00381808039200c03045c030401e032030315100f582125400800440d4040c1540106400e140c42544201125803c051010081001c2500b281c035054070103604807402800e000b010801201400c0880102002c0c1d02a200000e45c00c05400920f9510091003040003204940c80200b01a40d0004d141580c0031000420380408000303501c80c98038002086000010300788601102150a03900c1001c0b0010300d441c1d034801c403030f04040c0c8410f400240b541c0000d018118010595034001c081c1010121404c0f4000b40c10200024403140c0181400c030880d081c040c006200280c45100c034000240201e80380c01d8258410104445c43e060040c500e01641548070700080c0000741001d0081c40150441a4001e6040c80305ca0101800700b20000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 734355017 1250 734353767 734353769
    0x9100515010801350615040203041104150506070501020c15090d05031902030118110f070f020d020d0c06020105010b0306060307030b0112150f0e1303081f0303110d090f 74
    0x40b210340c2c501d041150f41a4540c072406002000302800068414034440003005c0b403440d00c100320080300b04040001910401c002c074482240c0080140581e051149054201640240418014071300b181c9110758490001808a8100f80310480381a074000900c03030030071036050040340d080124101e8105400d04290003e580c5801e100c5000b4010030502000151503010403a02c0701c403104804140444d62540c46046010280c0c1184621880070350800e00710580d1120b40b0300480340c1082e04050303442d0508000b0340d1007005101030030200740c0c0d11042c0702076a800036a989084d241407841c85019410891403a0110190030743d28140d01c0440150024010002c0903202c00c822a50711034030624002803591602401601c0c00801c1c400c1400109241040011602c000c2102150940e00413280780b0085ea56507103440000b2007022917004107800207010720080000d02030001541c00c9031900421a102020054111600840d258419000290b20405c55002c3d0304041c403800ca001c0a452500003041d904280352000c2448039 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 734356267 1250 734355017 734355029
    0x8070b04050309040501122102061803040f0f1d010b0a0503071107180b030f0312060109030618030915090608070203041e0519060c0602071a09100515010801 69
    0x21610024042003014422141c40140c004c3c410421940c66096a0b07407640e8100030110383c0c4036075486d81000041410508100c000e13005500911071680c503a0841500c00070258030714001c0388000d001c00f0401401c50005034024004010001c4d80d0645460ba81034040000c2000c022540302880300140036070383d1280304070780d000c0d4811308010b43d807504c4a50046603140c81c10041d0500501501c01c02064404e400c8030906140c802030841404900c81d09410551680ca031600780c0000b5a1007000720320300641c00c4518181c1e10034814100014011b503a900d0300c005a03001004043c05141d4022000d108154000c5c44880107000c0803082d903500003004a501800c1080c030342c01210113000b031907030010780c60a108004880c0900700d84a906515903050641c0d41160a1482c001c1c40c1c458852000400340840103412240120340d40d90f1f40b1a0080d00c402e8607100000c0d40141d000352240350004503607035500d00032126464003c5009000410301c1d4207601208074101d600c01703032507036603001e0112111952582c0d21032005410b6500e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 734357517 1250 734356267 734356283
    0x30d090b0904050408040e0a0f0c020c1309060b060d09021813170417010603050c09090307031416050a0209070302192d11070504110a0302030601091a040315090807 72
    0x150380c200321101d1b014550001d0144484102000807860131904008007002000d0428003c1c044111800d0b611940c181c00605c0e040030340c10241c0707000c1c906160807500300c3c14080c030000500b07a4041070201d95282c0c808106444100c1d1070301003007003c6040603001031004110408a0200c6814003484030910010141e90140c00440c43c090401c100408036011100101048040c80c40302c041c0303002e0998040c00c0b40f40b0064480e0301a03201c0c5009541880d076030282c8101d0300c40c2d01440c035012090f607050f14508805016070000140c1844800c1180e0320398110000c6460084c001001d091000c1c1c4100001c4040050000042600500001000200d4810bc1c010b00c3d15440c106405072043d2a101840410012080001c98814024514a54640049c269060280000d05075044030f0340791414131080d04c50003100c0340b0b080c0d6010841009514400d0b409103400c50340525214401c9070f03031141003034030300b5110355091840d68000040800421020900700c4c0900c41c21000706014801c9143c407649401e011341c00010340411 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 734358767 1250 734357517 734357521
    0x91a1501050f0a020f030d0b04150305190c03080318010b0d050715050d02160227060409050c090a0606090519030803041b060903060f021e0a02070e0a0209030d090b090405 75
    0x3134004d02400100c0b000140880b610307410068464000380410480150040e0b00e00002ca920700b0032000800015660410010625071011005160b43d510309240166403a484c0c1c088040300140010780158081c4220600c2c200d004c4840100ca9401c441030089424854000c000c0d49400007400411001d0441e1510000160748a042150a5500340b29001c0d10a030b65500c001210b075014030055052031f198600a0350402d00c1c04400f090002030741d80c02d5046a80071800c582000030b010345000d41000108038400c1003510100c1907068042030800d081a501813044030b898110034405145e01604030380003414101e03990009a88020b55500c1505454000a010644004001018000d200f028084c1c400005c5001014140d81c594005107030004a002c12038400e42407510046808203640241c60b511100d015107401c078106402102c072048d030722080039039040d401098000250000c4800e15035205d01c0c12010050791340c802c0b035820181080c088035101e0081c880d04582c140b101440200c1659510700040e02c001030bd603 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 734360017 1250 734358767 734358787
    0x1006020d02152a131203090306150b0d0b090601480b010602120405030d0f02190302010509120c060f06010c060c02010c0e061903051009091a1501050f 66
    0xf900c004030f80c052103042200060707660f1804080280b400109040c10340c030000f9190800e0924800d0389400c09400921258014004910190300004195111320010300c052545c174284181b843d00030290752078400d9034602c00d1080300e0924580c010b034020402d203851146801000e180701420030710600c548028020350300c248540d0213a07540d0800c44d49418100740b0700488000307107032102e8018402d001b90310040c040e41500e020709041c904165010356800030081c00303070744901200072900b120556100304110b228000228000719400c010088100d4013a50003c9000d1410890035464902c21036551510090204103c603000c6401080c407a4000032071030302450070b0342c551a004880340c00c01804040d00640c40c05002015182c0c0552220b00c40074115155800300c0c1940104000d80d900a03d980c0741c40000202080c03203803252190740078541c0883c102012806ea103840b80480000c9820340c613800c580501c8100521205103151900030b99000c03801d400800044289103000800b00c2c050080d030305c0d182e651302080714014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 734361267 1250 734360017 734360041
    0x130204140c0a0804021c080a0f050301060e0915150403030801050d0224090301060f0603180b0703200c030702031515060304080d0f020301090b01020a02030c15120408031006020d0215 80
    0x8120480146c0c002041c0381410819102ea000000c09404114415440521a4083e1040c0c0741290396a49900742c025200805002044a0082162007140d54032011043e55960f0020465a80031441540316100c03800c5240107000a0f01c180c101d80c0c42a00907100410050f07403060000c28290403801a000480d08113490092210b028060305103030300d5405c0c030b0f070082007800144400000301c424a603014071095900035503420390044c0c0010041c2c860345101000405150083d00800030b101151300e040100d00ca024800c0c1c03942600005002c803181e0300009030200a500e010400c28200013050b2019000c2800c001081d10048019110041c0c012a4040006001d03c0a91004d680345c907101c11105200e01079501030300300000c0d4401d002d02d0706010314209a01d025540b00146008150307034040c00400720101e401080080b0f1410a14411569100802242128815841c0b00d2806a03210704a0076840b400c140b0aa14072000e520380210b0115400350003140c030810b41c001511500c0e405a458040441d4840d4161007603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 734362517 1250 734361267 734361289
    0xf040e030706090f031b0b04060513080d0c14161112010c02010903142b02041205010c120b030a0f020a120f14010c0f03150e130204140c0a080402 64
    0x202d1803910302d102041c00490804869203c0c881c0d952005140101224644a404000c130301034155010f0b04001360020340c0c1980503c0d0030100742c2856010507600350f640d2810b198400300c01c0c00d0055444803401c04545812140000d0440102c11a20341050310820245221800122010b48040d40c0407001c84215128071142d0500c4101174802840919202036002e4040c1035213000c00c800142108030031440c4c0001d5070f01030700c1112150310442c0207605c150026803c0e810b121b10700b600b0407140c3d00f00b00c00111711106519005009100d0000410002601031000e481011800068100340d424116200c40c070740c0d80424881001c80e80107042514040a600100c0c02c82c103420f4004440c240e17800700d41013091160409481007400e10500c0210481044400214207882c800310a1501058114041500550080d009401035802448002542c1d66551119041d03074001030f1005c1441001c400303640015400c05000d40600c156030b24204d21040c2c20440c0705c1d240507100d4080c14004101c0ca07000803134215030b40d03504464 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 734363767 1250 734362517 734362523
    0x11406180c09040f0b03060924190e0618070302151b0304090b030111040806010e0901140f01051c12181d0613060303050904021b0709020a0207140f040e0307 69
    0x1140f94504c2000b20024006900c04070311900c165400218110000038441a4044c042e0207111910880c40e10040120080603040e95000380c105c0c40c40b07840030042e43c1300f8520000f8008006007041d05002c5100aa4101450a075040703e40100d0805c1c00945ca13040d010104214082054683e2002c148182044643e00f4002000d868000001c0000d07035101c03036411540c01103d04034000c00a0540c1411501c600380b0540c0f05201c01900148010441d10b242c18040700c0d48041d81500100391125000d02c43c01800c102240c2c0c9400300f25038840140114240031181000c031881a19581c1c540102c0c80d00c0b0020552003556191080080321030701e0616103000e07040725030001c02c0154803030541e074507080d41020948402101d905000728404140c860030603c581c024441143c1e010b858407848d101d2a1000d0001039482080801819101c83d12460034030340d010040d241c0103103042d940c01a01c4140c2e010009081003441c0c3c0c00800600b0784030318007071072079640d441040c200f09000b241d002542403075138443d107402e41c09110005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 734365017 1250 734363767 734363771
    0x403031d0a0801230402030604060e0312010914070201021e1e030a021b06010311010309030512090c330903240114010903051c180801020c011406180c0904 68
    0x8070b814054000010304005000303111000030f040c52407003010807001c4074044d40c076a10680215000c5081603000b401e00304000d02c290791406229943d0f007100b100d8280d1100b01c00c1581c82c204509080c00612000b5080001480254988042550302c1050044103560056103948001007500d01c061f030303000030400d410415104050701d07032031320035040002900720041300720718120703500403010345400041244e0f41600d81c44000e0b05035040040c2c0046000f81090708088003070003c00c00c0744109860a0b840302c5072040c1142002040d00d00648002d0100e40c00740308240c840c8039031120030305000030201d041f40c82c0c00183e07121740d43c42d88030440007002a151844004016004084201403921001d10000c0694180c0f50015080c00a2540b04401103807900d406100240c450340210120104864a00c901200000440e1a089240c10507410b8407589809040c0c4c444482d9070f50008040440301003e008804003005034010214a0746822004924128080d061400007084280300051281803800241d0314103040203002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 734366267 1250 734365017 734365019
    0x110a300606050d0b040b03101a0901081b09091f020f0f03010611060c2a0106090c030f0605030d110327132c10150501140a050403031d0a 60
    0x2e406a840a0340003101c00d81080c2d40b1143c02d04190103402c402c01c0015005180c40c03c0c038181d42e00002d1110546582440100d079140c0c0c0b505549038007095002c4d080d10000b600c403500c854040d10b104282d406030410300072842030701049410741c3c0218400000e503c0301c4d64100319412900f036086009100b0b0501c00440c1d500040b03022015940740c2c1001d90f040c0d0b00d5a46852400b58400b0690035601d00d403c60781088500c1080019034036102a15601081c200c00300ea00700c000d09031404c084942960440d4001a403500d07660021403450039494000d1080310842d10408020075400c0001094880302800c0f00b150520180c91011803002004208890005e14100c1d92103089071201807140d504200b900c5909440340280c01c5070341428900350703c03070b26110f00600b0401008600c0b0300b00c080300d0101d0300d40402c04458001d03c08c03d07200c41e0086010700c0440b21107200714203d0450405d0005050502d2800c00c03000d20400911545038030070380020846090f00d03010705102c4001d40c42000c0d01010703103104000300c80d00200c1400c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 734367517 1250 734366267 734366279
    0x3090d12080c12070c1b08060a15050609011808010e070f15020c1315120506010b070506060603040204060b280c03090b0307030b061903110a3006 64
    0x145103000031400e40e855901c40d40b0764a00c82c085034001c100364031420703504440200d074003940102c0c9603034a1588507001e07a080d803030403e04a24070010411750040000b500030208001c0c45540a00c181c00c00103030361346103240449080001150b00340c0210700c54181400507100c101e6a83c1054884941c00510161000f0711441004020b0541c8802451040c4094409541c50102e6000c0e900c2d03501d01580081030b03006000840759802080141080c2d00380e40545544c1c0d500c50441050030030799100000e46040c1c13020205607100d0786000f42c50402e0581c000316004105000340c0300055004207034190042c50807240b6a0701c9881d140005001424180c1c805c4081c0c9038001406072203041c0c4840071000c12220107414801c00782a40d03100791100b040da000e005002400c08002030102810703c50156030002c1c03051900052a510800204040d60701854644000703049840300044080e5040c000d10b041001c20040150410010f110060100b0441403210b001580c0c14a00f1224002e116918603144c10081c08024418079643c3c4c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 734368767 1250 734367517 734367533
    0xf03020a03030c03020a08040b1008030c0115050d0b01031103100204150e0901060e06130905010303180f0608040807020d020310020705120316050307020f03190e0904150e03090d 78
    0x80c0c0100c001c40d0030000c141d00391600074401e1398021000758482400580d40c035900d14007140c100429000c2441c5014001103401c0700d0810207481070174a0003000181140c143c580062801103540c1c040c0744201c9014404074001102c882c07015044a500030300402031003107820300080c1844d80c5180c0d41c0118900c046400290600005c0307030404e518900c0d46a000c55121900f080c404a00024021075001c681000008965824804010110308000b001d650300020380324000d41041c0c0f082a0310980c000b841d030700448c0250700c59048282000b800c290042e43c655526054001e0031588008102501c80e90b030214500085d51968104140c602e580281a07802041080704807030021f40111506480c81c2c414140c2c69440e03c8407900490340940d210340580c82d8009a4850215503a5000800c2081140580c020601c010801080984000c00035000c8000c80004a441c00618901d040c3c070101e4458601700c0e041c0008a014403001d52200c0e9800b002c0864168988450391f840c6104203c003c0d900204880000c3d4148103540d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 734370017 1250 734368767 734368783
    0xf1101110306040b040c05040b0a030b0907020c180114010c0609061418070e150102070f081e030702150a0c15050106080708160c11091f0f0803030a090206070f0302 72
    0x4440804c0151800c1c401c0c00203c0d00486d0104001c224200001d100307e42e40c84018100c68076039498013084034020352000c90418801500d03140091fa01503c219102858200c0b11420340000149642e140c561402218071201e8030110041030501040c0c1c00640705200c1c00381c000170b1429400800500c5281207176030030611011422507005960b40d58200403003005082c0424281c04071810301e540040c070794039900080c00b030f1034859490450541c443c0b103000143c1924a07644079402052410040d00503008500009205a2038156903004241c00401c0300e0f900503510706007001d03644400d401a0320740b1342415007010303511592911130103131001c941d102201841c6405a0031050507120b0303642ea107a002c0e48407aa01030390312035410b0311000c0c0e5078200c0500d5881c4c1148101c84040501e4000c454000e020007010000c105c5400040e034002c03849ca205019540904c41c0e444025100a00346021440c400a241804840e00c87c040a40204906901c0e11070b0740f4250356410003650759094002cbc07c0d000c00c020642c5006962650b070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 734371267 1250 734370017 734370019
    0x120405010f0606080a02091f0503060f12060a0504080f0c03130518010e071e031b020c0112021612050408060601080606040905092d0f0607050a0f1101110306 69
    0x821000e03440e40c01c582d008280840c3d140342c0f140040c503202e809000000c2d410036210150000444050300c04c5022202c03240c0300c031800050b120f180e40d070b081200c01c2c0100a54108096802128400d1807030800d588002182c540c09540c08000055584851034180054802e030f0508400303140021038164180240800117044085c0c40c5040d40c0b00d99a6607501f4009a0b00100c100c009100b10940c0042207404440009203912514034035040102043c000480580c4c0030f850b01c0b0010002c1e40d03407840b4070781c1090710600745040710b1130600081c00701c0c240060000f045041d90060104c400c0d40c0201e030700d4000d0221600c008001c29800300001034070300075400000f0010341151089032854410500400d105500841d8602e010724405070580c0d18150404049101810740540718240620a010012600070510320f911030640450070140380c040101d450840f46400b10800c59900340390082c60611140682140c01c903000d002550811103020b2020340c20949080a203c02c440d1642d50801c015052071520032001544941c5c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 734372517 1250 734371267 734371271
    0x50a141906080714120a08040f03150b06250f03020a0b07050703050909090c04090c1701110a030e030f0c0d030c0e090609060415080706022503020105070309090212040501 75
    0x242d5240d116a0303800d11842800b1640b40b0b042c0ba0a100d600b0038103001c032018142c1c035013103a025078103503550018258410391000f1020903850b802031003000b000c0316500b80c10041d044410310200c2ca2080000d54103208210300d451840f46001124944903903010341131581940c0180090b2300e10009410060746862a40350215500c03010f81e0300182001e805001500d00d0542c16903074050512000006001d4a60750180c4620800c0c403842c2d01c83d141981e950700646a1b803501c207000c100e43d81450000c2481c101038001c00c2c0104142d04061400780e0645040e000e442c000c00c0c0b40d1602084500004440c103003107125003606022182d03000181055031080c0092006000480c964081242d106050000c07038482c04882401e03540700004074049032881c0f900c0c0c1d1394103400020081000078100034103220405541400d500c21091500054820450103405000303612005952250410a030004041014541c16440c00300905100021580005140c031808400e000f52642500071540c03051b00c95105c08004008550480d500c0d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 734373767 1250 734372517 734372519
    0x605090f060f0403050a0921020a0506181521040c06080f070809190302070302030c010e090a020706020f0424020d0207050111030c0d0f170403050904050a141906 71
    0x29000607460340b042c101c01c0888442e40e203881d41d0454071940102440d4041200b40c0c000410280c0c00c44001d07080c04041000402110344c298818400c450010303a1081e403003040c05014040240014410300c0f111031300122a42c07918407940b0455210940104690390016814500c01c40001104a0071a14000c5010b0741c05810101d40c0c981003200c05c0e06003110351101c4000c109011484282c0604585c64010300c0d080b050b5865010f0507103440892410030b04060f001a40b0103d000c0055040500c1005a001300c01c1c42d240f0381030000d03100401c10114010741442445607001032880103128950b41500c02020040203000d40c6c41c0d0341c8250703007140003a5814903410f1408000000301d801c01c0c0001001e6007411b055802820040340381c0001501d035001c614a000c041c80c0010000c02c0b407001c0d0705120900d44e0f4a40703600d0301c0902c06090340e80105484501c040300200030b44040107200c04290020b0584131491400c6402146680e00c041c0c481004e8420302208500501445c0140300d01005080c0340f2481c2c000400c10100441 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 734375017 1250 734373767 734373793
    0xf0c0b04051302030a110a171b16030c06060f1401030510051509040f0e0d0516081b0106080d020c1903020d17030108010614040e2505040603060509 65
    0x192003188107803940094481d41e182403181003900515841905001d00040020f801c030360382c1803945d000c10896800140c1440ca402021034080321415000343c00d0500380c015408501c501c860052040c407604034000c0d100384050000b00352242200d00d007119413004e03052201e02d5403459440c5807820240183c4d0040446010001c85035407080c498688118040410141c0c0249002c05005007016090590b4030542810841200e4980351405800a2554a014002200c0800c09403003810040c40101241c100041040740382800c00c1003894443e0304036007003503400ba6215800300040c1081d0340c00c1088901c0315400c15500241710003011505507100b00c02038080d14104102e0800b0030030601c20088006c4185102000d00b400582020314a00e07040ca88106100c0d800d6480c2e810841000e41c100341c1c4071400603911000c05011003502c11341c00c420480c0701034500744141c0700f00c4002175407103a0701c55980c07940d180c01c2200048180300405070410010300c0082c3c8100b00054403820008003134441141c1059461040f070f41300e8550 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 734376267 1250 734375017 734375039
    0x11506080403120b010e191a070b0c28170c0f2d0310061b050c01030905031c05010311060a05070305090102070f0803030402010f0504050a060309050a0f0f0c 69
    0x461589540d03042403481400c0022030060071664041410080109007891032515268003074087c00303581e11010130059160580d540b0f0040c00c840c004c0c0542080238070800c40003550080d0055000b40e5544881d0b510f810b1040060110b02108070040a07410348552428441d094109140c1c40d002d810710340790f01c0c0746030343c400019440c64400c3c0002141c280808100c010701e40034058904030010603001000d10b40001000340d8140c00c039041aa060122280e2889003040300540140f14041048242541340694004a840d910f0b100e040803103145040c1a10340246904200050044840c440c0d011940405504a00039500f00181400d0004440d10300c24000e00381038a00d0250155650881c895440380d25002e45039904458540001c1e8106055104680d404124404100512000b4104100066450b4503050000404400044083d0018440100000e2045071540c0700890250360351801c010804200d90301e0300302d1410504e00005807170300340904880f504105002403120621030191a02c80d255a4032001c4100d9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 734377517 1250 734376267 734376271
    0x19140705010e0f04053411120403021e03060702151e0c0f04090903030f153819140c0c043c0606020f0a06090c1701150608 54
    0x1c3c1c4042c14001c8a501d83c64107402069218102c54a00d608030081c0030342041c0307042c003611480303117020700c0312180007081d10b0340401c0d01596002102c000b0051060084100200c51142d804080c2c001e03074000020455040002c00342802d1000007408640f090301d08508000c3d01c414402c4c0015251402e2079004c00e0308400d03140c1c500d60b544100701441c060b850325a454480035541c884018807003490b10500001403000c52600c200c652142c026100420890401203031481120890600091009402c40e42446803a0100d03d1103d42d40d510346401c0c0c01050440e40980c0305801080d2900940b581e00042e0100a0726a0b40c804a000f041481e00c0b9000d02c04d50340384034590f8a000f070b81c850b00000d03840304c090700ea2285046d421110038040c00b5540c8144040320081c5982040a11106458040e03c00854a02c1c2d074a000e072088400400326480a00120b01c1c480070f40315141e061101d80a001e454030307401480148007005c40504020203003808100211220101000d019128000c8185104038940c0c0d4001915409030b04518 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 734378767 1250 734377517 734377519
    0x311030105150306010c05010906050f010902030f0a050a0e07140901120506131410060e06150306040905070e0403110d051c2706020c0601081207120219140705010e 72
    0xd240242e203410710400c0c0d04020100c904014801e10002d01044003841845030f903500a80011485140140140710610411780c852912a0b104001b00300d44084004212904403010340c10214494a40c000344a029010700b00c0300b01114000e600c00003071780c0d4030542100e120503201503c610300141e0743c400316108900c000600161003500f0003800214141c5203c1c1400c90940d1141c8203d80d00100200316062030841c0580f04951100d50b10f400c284840900204042d03846401194034096044c464905114540405440140144d0304c0d00804002c0050034410030010300303800c1d5500c00280c0b800e03040080803850f21500b241c41c54000c007118400810700c101d0480d0001c152400810850194050000001f0b0203294040c14000680740b102405041d03903455003480d00c0f0300903503025841c1c1d20b051071103601305030040c0d0242c0c070142d00000d03850406040b03200540b61400c0c0c1214034072034203c11640040c3d04000071081403c034071400d5040d889080001100038040080c6c2a4400c40b25034030345620040da002c480040341c1c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 734380017 1250 734378767 734378779
    0x1c0906050901111b030f12090c030d05090415080d09031101020105100e0a090501050108030406020f0c181b030708090d02010e03040b1804021b0d0306050d111c120311030105 76
    0x20031103041c051001d000c60345000e14100e83c031b00040381c083d10350036420108401c0004200201031103080c02c800c01c00010115001c07405020601203910024007140300d00d000740c500580d10364120030552a84911108024114042034030a80496070f48010600170f1107000c216420803500e0141d910551051080c0c03803281080c11f091200745400c1803542140103a0091420384060713107810814001401c20702403907008000c07120045072141c1c140030340a41010780d0006170340c0c01948685020081780d43c40400400744a06011075078903840d2161044421440c4220720524580c503000000d100c04d03103034820181403003514400292002450804022402d854078918012102c0d4401d100a0108940700e4000381030440c00c0790f4070040c84000881c04a0103980240300c020841100400d4468040340701030154040380780722840c040000906200010785140041d5001801100c490f408104031a00c0b001c13901d85443d00d0034809484020303003500e0240c600905079100140040d081151240509080780d0540c2d059443c01495 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 734381267 1250 734380017 734380027
    0x31912061517011220032505011d040e030417030a030f0207030801050f03280326010920070c180902030c090a110a11060601090b070b0c1c090605090111 67
    0x3404451030b4080e5050b0b0068520b03840508a141c3c3d0402160710042107590044010700d024107810300410187e68442c07418801d03103040c04480c4d07901c05850260859003c40b400160310203c26115840c0d070042da00201d80f80c920080440210741c5000015001c008190f9506000204010741e100069006103c0c000b070109903920010310040c903000c5844441a04d01074100c0d05000e444644401c0141c00765031104071150141c0a40b4024182e000380324054500201081864101d4016030024800105100d070303201c000d43d55003880060400b0a5002221070340d070301050070780329006810b202d5400c20451103a09032004c6c0d44e585182d03100000303005250450350001d002d0903803d0000c0041c441d41640081c01d40c45110b0b591114a14a2000e60000e8841202265104251042c04000c0c0f5031500e0005048503050207200e2404000442c1c200040301d03100350740103003d038456854101c0c860384c507401004917002c2ea103a80003800c4400c05100707a0000c2201e030300074403003804181c403803810305400c035010780c031600d4042c03a01041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 734382517 1250 734381267 734381273
    0x30b030a150f090303020408060906010302150307231b0706050a120b030706020f0c03120930030913020301060801170304030b040b0a0b0a080319120615170112 70
    0x10700c141c18000059000302c2c84401d80c0180100716560303203108802099020500b84a0f83d2400c200d03c1c0e50107004000100780c554195000929001c00022005025050000c0040d01c218803810f40d4840001c2110700c9642c0907985a8101080354000100c04085e100710a050b02c030340590300250040031100d40e48c50b0ba515011111108580107a000c804519001e03440f40000b00a5460401844004208942c041e280e420f04050b84c443c107058618481700d1003684085070320b1800201000c2101c00c00072007100c3c0c800d14000201c80300f001d800d19005080c0340c40c40b0740c000c0c2000d03512804401444402c0017250100304903001c2c20320360822804207010f42c01c0002c40316401448542070380790224108101c4241180c0c00c0c1952641d50304070036a0119800c5469101b91001e20507510420f0050640c1c00008995031031016007401c203441e90301d000c4c68224000304108150701079600e034000c1d004041c142107224400d1050b0354a5170078642c8844c0854a480300054510320ba000c009120102009040e681c02481620407640152 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 734383767 1250 734382517 734382533
    0x110306250f020309090a050f0f01051507020102210d150b041202030a060c120605031902040b0a080a050304150503070903080703032703080601020c0d021e0a091407030b030a 76
    0x940c840250f10003000b0b45005a558041100d200c0c410b014008142d920b80313601c103007000f440e01418035601c00000c00014800341d076800c000c1e140e90101c242400e9494002c9800100d01d080300405031001c0f0700525903610503144248000030240f0840400080c802000300901500c000243c0d88108840008184070a002c8419461075501c2400d0008040343c0454010792034070720440d440000d403800480c08120048812010794058640240421000b401001c001601a41d51031b03501b15400074443c0c0d507a02e004201e2076a40a00b4040a40506800c560054200386030103035580d8020b0060b400b00240c620541084107101d041140d1142d0710039503610042c2c40c61550780c081d184d004100200d081c1511000c216049065800b0f6a142d1170035000810014000d050802a00c0081c001d043e0b5811900030580550568440803108029250b058401c00d2000048440091070800c1c101c4080783e02c510749450004a101c41500030351020211000d51060075291414142c049980d4440890b0b015048507407900b000c0b400311 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 734385017 1250 734383767 734383787
    0x12060105090c04150914010c050316150204030b1504090f0803091e010f0606030614190314030c010c0c020d060506040618090c0902040f0506030403020a05010911030625 74
    0xc0c14019040580b41c41d0a560884075094020000402003d005c0040070006c60110003003071001e080181540803561642d036141e1103224124440d0301000840841008401c406400150b6080b440840d180d646920304200003050644051103413072681c1d2010780031407800c2e00c10300c01426030018540308040c1e516a5a010f0076000101146d41070b004442499040340502a404880c0104840001130b216101e08400400c6a00303580001041500d003200c24000130b0a480d520660708641240c09035000d010088411000a207a46c000414885000ea080080141c0000250a043c1301c0c00300207004807418454110307819041a4006540070070380590420105001e640001d401c004013030000708949403181e0080c10260401d108940a456a951803203041c0f002004a0720f000d011110015071a15107003641006084105004543c807030b007070000c04541014000c00803000b00301c0d40407001344050005800c20408895010006034000c0c01074000160020002c07a0518250201100900840500c00ca50481e000c00381 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 734386267 1250 734385017 734385031
    0x9100f050c07030c03060e01050c181c0803160c02010f1d030607200703080405010302030910150501030506030102070317060607020306040501200f03150a03120c111206010509 77
    0x2007000781d18a0305a0522220002d035000b0350011071210701e07614221b012a0840360031a00b182e403400003031046180d2900201c07034191202c0c80f90103188d030b03401c18001034695901d02200c80d0b1b00c2c6244080c0ea41046124000346225007034030200e001c40b92055490035213124001c024028001000c3c03126032842d65020350202c2d0800c045650f010506441690003080c034048050303403c00c0c0440c100c41008000742100b04a0f40c054107443c00d002d8001d07245555a0b149050040380200d605040d008000512080360800c001460f00e86070303000c28400700c051000e07400031018440c02142d0020382040b0000e580360030b050007103628059041e591802c6e8000508040c261207000601a240e00190402444000d03940400ca098051401a03000043c0492002001c0c9a040c0b1900701c003218590040c03020040d090048400e690303220080491000041e259a400203a0450007a0001060f036561403031800d40c400e0b80302030901e041314480c1d00415186042d180030480103441c0d1006040351039000000610403400c09a00507070700400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 734387517 1250 734386267 734386277
    0x50c030423040c02300f0c03120c0d0c080c031f08030a02100c09150f0912050c090c04050f06090609280e1e06030703082a010209100f 59
    0x500c0c000060030760f04184001401a07108013072074400c11460b04170440309004990944240d070081211030140742c0c01640d50200030395501165140484d070b030601c115502c4c5001200000c0a0303152042a00001307400c50b48100081d545000a00c1c040d841c0284031040c0500800c0c0b0010381580d560300c0b840d54024503041c04040b00100300401c002000c02040010340010707443d0780c02400c5064110724005080b114004024810001c0700a02001031b030321020051a4001d40910748600218401c1a06480c0c0d031503076070b01c44002c00048507a0071003030080203c1c8181c016001140c05240c03507100e00000c09828010390158030342c4810385540c42d40c4a03241850040035842d0001d0711107418200c40f08002a544401050303203800100d00c0c0340040c4031518051008034058480c0d030b10040001d0070400a0b8624240c2c1506042c40c034421210080384403a40c08000c410f0007950b000504a65403525100c42420b07a00819403000b44080d801c400341d030729414060003942c43e50b00c2c0203824151140000c11088464030710041c02074007440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 734388767 1250 734387517 734387579
    0x250e0915030c1027061e110d110d02121602010909050a0207021813030f0c06050a0e071a030402010804020a170105150d0c030809130501090b040b01050c0304 69
    0xb407509268500700d043c00f6150000756913804250155481d03146580f513102000e80c00000c0c401550443d50301c0d024038090384140761582c011140c007590b6a204140714900b0f00d03c01e008190710b180c0e9100e0300b80000c4000d840141c034841c40d400311050b6070f00e4101c05049042c00f4414032031450707407084810440500074014074003004c0360390f074a649100c22110180ca0b0a400e054000400d2400e60400d200c1401d010721b91031511486a260a02c01c2c43030303c0300517130f1040101081600c034122501c4910441e2409401604080100458103011390004001d154002a4a20030b004070080010b1241c84220300756074000c044d40300c8914641d200c0e0700443d1550001007007241c2c00a01e00001003010b19180007200c40324003000000165506003001c400e56801c480301412751003aa244440480040d840110300b0301201d6120740c00342d0702e624030300340007c95407804004400c075164a0800005400081c43e0400c0c06031131410398040000c8000c2d0001110203205211440003183c2c0200000c000c01c91000c2520048107110390442c0c0d0680c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 734390017 1250 734388767 734388769
    0x4050a0309092f160f0611031306150b0a0c03020105010b070f1106130f06020601052b1103010e061e011505130506041d090d1403130b250e0915030c 65
    0x15000c4c200c1c00b5110100384600c8501080164410110008103506055056141141c0481c001700e0144c1c1c401010725460300e1119003101a1880001d000c0c160103240b00d52a0108240010b0400306c00340c03c10f070015820b240000904103005001c1f240325941021604400c6034442c0c6490325000410f08155402903c03c00c8200c1c040882d581403400030341201140828100c7c9041e02c0240342480603004280b1a0140c10041c100c000031042c044035482800001500c5e001c070361810106d103030003254640c80b6015402c01754001d04103000802e04030b01c905905c401c0411484507100c0100c01130102401543c405d03603428015042c0c00c0340030340060819030078076a290b2015284c551001c910150000da201310740000c810305a984103801d00d842416405015030000f00f204000d5420014015103a0000340e081442c400030100f540c014807141e0030b0400d15040605c64015042821020618140c1844841c20074402004400f050314450004505040001800f51400b07450380d0740c2000e0308900c00292242d0510400303001c4152 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 734391267 1250 734390017 734390047
    0xd110a05030d09140415090c031415032103060d15060b031501030b030c060f07140319030c02060f07030f05190f06030209040f0203030f0304050a0309092f 68
    0x42ca55155880d001010320704006041951009903c3c503220700d00700601d1400070210040b0000032240d0002001c06ea4502c6540c00350001c1c40d031001d12240c40c1c4003810070402091032001082d8241c841c25000c581904880b15200b40c000820301c2d801811544040000c950303680b0707080e42030490290251548008981000408a0455180c0d900403000c2c205c0100801100240e0980c08004150080c00e0034040078481d9030006e42c56101c00800b66105e004007103012101e02000600352074016510410740c02d90803920415a03035694008142c0c600e0980b0241c81d007590018482d02410120070f1541d001090070f620303094020f11200320000c102c1000c1540d580711011200b2500d004140c020350032102441d410b9031414144c4070581d8038000310713120705c3d904146c408c00040e111940d2035580290406001d810141007840043c2c11881011081c80d4400e10101c2032100380580407403194a5503200791501c4d0b03d6036994540d2907082d107074004ca05c0304403062041a44600510108040c84d04000400304207840c02d0b0b10b814a003c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 734392517 1250 734391267 734391283
    0x414060d0c120b010e07050c070e090304050a09050105030d090308070206031b0304060504021c03080f060a0302030d03150f03150f02090d05061e09120901020c061b1b0d110a0503 78
    0x44080c03c0c10010001d0811824945801c01c0a81c40c120349094114400640c0c0c9016610400f40300180d4140060f81d0f00109005480213008000d0100900d03e07a00c90300f50025000030f00880c1c1c400e009442001440c00e0007110f1a10443e0b0780310a8441c1010069020000260401482ca00580c0b514441c1401c0710340c0d03007000441c172a6104820026043c28540140009a11424054a540c681d180503400c046a00700b040eaa5200040b541c00c1405562010b010901194080c1d01c0290940704032400541900c0d0107802c186007240c4176010b10f0303c2e040e41c2c50111503c081041c0c030010304081c5600080041d00c1e682a04280002c201010b809450aa16400422030744204950203035001d40080083c07044c0300c1d00ca10554120816001c24214550400d148519202c045044000892031000511180143d0013403000d2228080001c291540340c0d00c040d540c00d0080c40701900c402605010394800740030380d1b800e080c51031500481d000d01220402c124580c0e0b02e107201903c83c2401d640c0808500750002d00340e60f040020074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 734393767 1250 734392517 734392523
    0x13050409061416051209071d0f060609150a030e0706050901080c07020f2812050c030a050c010e0301111b06100311010305180a060204050f0414060d0c12 67
    0x100400740c1d070110405007801034a800381e0780e0341d500c01d60303800d05501600b0341e040401721000c40c510301c0e1180805a80341181950106207151400000200284003649080e0710604020030089104d990700002c00020780b1410740056480740002d01c00e5084112644060041c0c4c100c10309002510490880c0d0a07491300e00d15500c12800a040002d80545550f480000c41c0c0d001000b11164a05052460380012840e00d050811107008520003040460b10301d40e044081403515070342c104030441c03040d16a4105160754000c0c04090b42c4d148154401007815060018081c51080e80240c0903002d215150001145d90040a5a04992540d240c06642c200d00c520540100b0610034640c1d9001c1030306051155003410080c0040c01d0b120325641c2c84000f000401c8a1443d0365500e04401d20b000070301c69888103000014a0307030170801c8400605c1140e001d0820070001d80d0041c0f054450450708003001140e8002003100355810f140d030448a0040100c0424074a041c20000d980203148200c141040c05034a900100035103e422040503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 734395017 1250 734393767 734393771
    0x2010e12130906030b041e2f03030307120f0e01060e0604060b0c06040803040f061a09180a0807030c0b07050d180809010c031103070503030103050c0405060a0303051305040906 77
    0x3955807030070340381e800002403507100b10038880645103880300e6540940c000c001400740344800500008a11041c8401e10302d46501c901070301074100c808540c00301c40b1220580c4c0800c0040740c081c5440003d1034000180c81c0308101d00d544d18513018081c40913290242c0f210440000c200c1d03403108017400e1004001e00410b00a4130000080f003004e403401e40104070540e070155101d16040d1000300044060f080700865907a5010360000c4032541e030707500c0f18945140b90741c00e42c1402038440762510300301030b5141c20400151940c908045845003040d844550004410060701907003882698485d10010002400c40c601510640d8040e060024816081c2e0301c030050844000c0b503903503001410018190803070481c14400c1091078620f01c1800c6090206036074030290a4444c441800d1305102501c1c519030101485050710a40c8030301454150f0b52a01914504180d40750020b00084900c0d005040300a4081d040502c10b0901c20400140204400c0d413a50301c00703480ba81c0c8054055090711200b844042859103d50068040d103038814400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 734396267 1250 734395017 734395027
    0x90d140d080f10030b070305130b01080a0302063d15080405070605090f09190e0c0f0904030f120b0301110d0b0901050618030a05060709050a1d0c0a02010e12 69
    0x1c000c082c900e009008449041080000348040b030294041031703901074410b0a0008068036108080c044910404034000c02d804c5d1542c00101d02a90042003100b5102d11a0702140d449448800410580354141e0303408403803138400000c0e0030002c0452083d1280794045102c01005a42e03454000d100e84a6900390b01c8007022070a91814441008400c00a03d801003c6a184c041e0420002400140341d96080410962080403494041140c910904070811144a00440108040300e10b6a40c0c06440d00e0155124a2081850701d60004444c200104c04520481d819940c03040550f00d52082a150903044442c00503582c0e03074806003988240c07400d1143c2429040e4030740070f06886841c002c210005861428441c00d02407244500100004d031100c0c2c05550490f03071343c0182d6044406c419404a480c1c2004488081c019105460174080929004924ac0d4140c0d1b8082e501c000c0c0450716510380c0c0050030070101241100000c1c0307074001515903403040c0150101009910001c50080900a030840c0b0f800c0460750550010080094 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 734397517 1250 734396267 734396281
    0x50d0e12011401081e0709020c19050c0103150e0708180601030b04150218150c01020d2a0203090918060a0c080711120c03070209010905040303140c090d140d08 70
    0x503880610b0007003502c0011000c1002500c0e21ba06052294020080d00860301c1100e0b400144182d10080d11510b4110381c81707101300e05040d540c6000e01e641c078a0100303243c50300e0b91009101c1d415080c0185ca0a44614030305035118514100da1043c4002d2480312040034040781a0402541070260707a000b14025200f0815500346402c101080c0c030f07401d4680307406d031038810481c00e411911324800780800204210b4000c1000c1458101e482124802c0f0707200400503501c006542c518030066a40107541024203603000e28410f04000b10b0146500701f1a150344405a8000d0056242c80d01c0c21088440d0b0241c2c01c450006411020350903403614199003511b00f80300e85600c40a481d0034607584501869402820390cd441c0410110300300d030705929010b11010400c410f083c0080c4807034003141c0400844004030b40c050441340580d0b940d2040440140707000c1c0d0301100082d042c15910070040d2031a0001500aa10500318a843c09801000300100c07000350b41c504503001c0c410080301e0340355480140103072014030006132180251807038100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 734398767 1250 734397517 734397523
    0x30a0e09070306030221010e0f25120602030a06030b0403030c03200f0c0c03032b09030e0609030705090916050d03080712060f2c0103050d0e1201140108 67
    0x1070548040500d403400401c00b680e601038240030125480903105180e4240c9810b030a0140a420820340004e200390030850500311000907400c1d03000b0005402103800600340c0100c100c800220b6200300c854140c50f02d15080f0200310a94021500450300030710018089507a5550314980c020b08036019000700741d50310340741c40c4099058069070340420b10300c0d4042c070303001c03192010301c518640504c01c0510382207540851103000e80c078000c0040f041d2408009085940b94003c0024101000300c41c414683c41c07030008400701e120110046e00a8048030b41e4140c9504005008000c107010749034011518060303143c030403403500080a80b580f42e81d00e406464100060452070202d130041100e444520b5000c280039094080076038002ca80d000c512039800000e80e18200f0480341030014190040c101c00c1d006240080d940c880005450100c0400d0707074610500074401c0b41d8002225961020004000741300190003034000060f0050700c14030800d800207039071074001c088421058500300b1860854281c01103101604803244010300c42c0410070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 734400017 1250 734398767 734398771
    0x90a050703200301180905160302030d0f020304141909061a07111c150213060203180909150103050307021f090302102c0a0f0506090f010c05030a0e09 66
    0x4001d0392242e1078071020104603a88014851545500740000011644078202d810210b14603411004840041280e0f01062040c10101d2000301d22911030417400089241c010444078081e003106030065400e042c034150710005416440e050690b4045865465185602c450503800c0c00a00703a07a840000c2e0480c2840e038008003000300d4101ca5018500203104541c001100040c00601710700e4155210700c43c1c20381c0300c90225010403840c04000c1002655050081620344613501600315440e00303c904003003840e51024143d85a20030340401260b0720307010b03048500301030515003002c640183e410412650309412000001c5043c10003070b001140c00c0d030800181c0c078055141a0a9403441c0341651a10f0701c07180b0000b0324004d4051000c03440020300813044248100021401610030980c9081222a50094203c4220702b21200c0c01d20303200314600c0350400d070902040d02030500c200303002a03400103040c00e0f140c0101503080100200401c3e0144d0b0400446a06040c001401803000d003000c07098980f40e00100c9106181088405a40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 734401267 1250 734400017 734400041
    0x30b010f14092137021e03120309060f040210030e0c0a27060e0a0f0b0d1a0c0307021f0b0d030c05060604090210080a11030126060103052a090a050703 66
    0x1101d502d4134440c1d00c1e8405101d2549a0499002d202d401c418010000d0f8000301c000340e541d140c003540d40d02803080034580004502c03804489003501c1d859500d80c006000724900030380d0040e400800f50213850010b00d01a0f44440380044c0d0040491b0341d04001000012900c1440b60400448200d0000310380b10b484000301540580300300311200c24000f950030814202c1d0703005801440d44900320345542c01d803031152a8a52001d0040c2001a003810310240701e500b004c000c1400b41404c0100c1c007000b0000090141201d8030203a900038121a4054128440c000b000752040f03900e6242c011103080e40e1072072110b90582d110010b00c40c981e4071a44a5503800121418541d0400030014010741c06107003446004030040e80d03800d061880304103032070809941e9900d84001802c01420038500180c82c440700000080360141810341d4242d48003203211160300d0082299104c940e281c000c00c0c80010500c0c0e000d440340101030303071076400354132101e40c41c26081c2100000528000764401c0c2054810040b540e5031032007402803683d17041c092501e650311 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 734402517 1250 734401267 734401333
    0x1a090916080610050c12031f0b03070e0a0f08010c120603020a180209040626281e1a010801180b060d050111030106030b010f140921 58
    0x40200041c141d62001070040d03105080d20192404010301403415541078a03060350869404003172550303240c01c065000340c819000d640410300305009910410f018000a564540b01d015003135803100c2c4401e461500510500c00e1f4022184400400c10300c0c0c01580910081c1171039800070412848200d4094100150400014030b50340c07c06a0600160b19541d000da011a07084000c0640c0c1d911031041c00c08000d0203800406a805401d12800003000b407800341c40d9100d0484501142000c0d50180c01d80d1507500c050200e80c107101d00c2c040300c80c0290700502d1141020b030002d01442c44102058070001c2d4400c192082000d085400002c908110300c1c0d107210f4074900501604594008101400d08084034400709080d1040040800900c0800200540c84800184400940c090300032f2050300d42055039040d07a90800d002e28000a850200760034440d61242070040c10380055a2a441a120301400c4850010341c0016602508541e031240902540c602020f50490292a0600a030009602c40d0380518a80c20550216418800c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 734403767 1250 734402517 734402551
    0x120a110a03050d200307030e031209090c090105040302031002070501050606070f0b06030316050a0611030c0a030207061107060903020d140f160503130f05030d271a0909 74
    0x554001000c4043e01c000d0300f015201e1101925441d9190295581c0940060102040403002c141d0004451841081c0c00c80076a04e4804004618111901810070083d0b4020442c00105880c1c4000c60000d0030841c5040c508285800d440c1d4021901e4001e100513025080c0740d0001c1c1e840140308007031043c203420007021204c1c940b42003410344840104204600015180c1a060300109801e59000c0084500054900e9041c40c44e88800b820495110070580e2410b840c4907041520f81e0b10a206a6002c4a00c10801c5040d0701d42007200c0004100c009402c00b900449449035215955250300032610054451030388540c0f07002c5202420303840e009042c001004065014400c001002e186451a0751080d01e50410810218503101ca40540b0404800c01000f071014141d4000015002e07001855079881d001034861600703080e450166604249559543d600c40b80b140060306510b00c4a441c0c2c4010194180e0700c00c94400c90030340003502d4015101d1501d01032481240d80c4000081d4201c82d500b400013215910074501c009018401c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 734405017 1250 734403767 734403773
    0x30f010812030a0b030a0525090b0105161707080403060f1a010f020c0a090c0807090812030406020712030f0e0c03060f04020a0308041e0902031b0c0705120a110a03 72
    0x42d01000d0710001601d51110301440e85038808000004c00c81c4d40080850b410140c8a0041000c41c095100020501c0d20400e480869018124001e5000c400c0f8181d40356851328100341000702000b11401421201115428001504480700c07c002d0f1400c1030248544541e51451440c2610480b88410f0f0303a8580c6604107039080d80f000143c0c9031a071030608000c0c00c03c100001c1040404904007802c46c100107510000c4c103480410700f500340e030788207805031a010f4540301d016894842c1c0030348900d0101e00c100314050344403a5070900e02035840b00c06150403620905001d800c261803545c0b0032400013440c40c2c0d146c00283d40c07001d500f14a032415004020244010a0281c9660a00302005c65100c5000070007004480c1e4080c0d02060454a6074801c05000303680001c013140c0c440c4e49545018807100047c151000b0070b02400400030812001314421a401940da09913040c0c84e03202542401404e58014015103a1280940c83c0c0c0041d081d2149540409201c507040c0c043c4c0100d000d10320b043c0c0b1200000c440414001c02c1c03548028000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 734406267 1250 734405017 734405053
    0x10507080c030907030512070c1e140a05100e0907030b0616020d0803091501061403130c12230d02030301061206030c0e101a0d021803030f030f0108 65
    0x8008903100c015542e0303888003c100e1621640b40d20081080c0f040c2402418440c0085010b003c03082c1c403411580f00c0c8503558911180c01740c29840e0f80c00c0000600d41c641040404a40981d1044901d000703011300d2a0180d41d000020315001040d0504008030b00180301d8041c0d0341c508101c03925404282803d081200740b4203880800c069003c0c0c20f03681da445076600c0408906665030760541e80003a580c400d00c86d680d40d1800d005c41c2da444150a01d01c41c01c0045010b00041070175802003a4091440d01980d92940c215600c0c0e0804840c00105401c1c19a03000408080c04070300b0290404180c98001d0207000c85254180d210030b201500207034101c0034401c083d080328074070725041980403045a0450340d2a2a21041814600c0790142c0140f06a0348000c000c14050080000d0042d00058814441c2c4444a160304142d50b0354441049100f0339880a0b90118500b08001c1c03210319004d030701402d0143d419000c014404103000010034a1036015034000440b81c5030200070881e404074a030b080c440c05042410054184000c04c1e01a01c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 734407517 1250 734406267 734406271
    0x40b0607031116120204020c0c0a0305030414010c03080f190c09080c030d0c02241605060601090e0718080d0903050d0201110702041a100509030c04060e010b0a05041e150201050708 79
    0xc441ea4002502d2340806400704140155910000c20315120305a591a0a954a40c001e01c04d002000c002d00c03490003040e40c0101030f503400182c0c040d2224a0f540e46c03038020001c4141e0000340514151800c1181e101c055140c644101d40454a00703441d04043e250500a20920342010045020700c20307844840000001ca134010980001c00b07030f054070b0300030201c01415001e0350030318034070085148180004079900070704482c00c1018200c800d00400a46910f91290001100c0b0301100c3c0c010304d44c8406010011811291207808407190b01700010484100c86031b1190440341c01d00b4a660b9000000a0043c5030600c10701c40203204040f8080403c0c0000c2280b01181580ca80701da018030340c0064400c0303a40d5000142e540c1d200701c11800c3d2698000380040b00d03080c035244000d01182c1000402d00d000388101010480745041034400c2d201a503074001109003540e80381c003071030141c20b5001c10111401c1000038000000d05003e2509110088a1011085500107041c08148400031806812440841e030400c01840b0880d40c128451903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 734408767 1250 734407517 734407519
    0x3a0e060c071202030c0f07050112020909011703070b0906040b0108161514130e090a050c0d020109150c2105070f0501060f0f0e060103020c0d0806040b06070311161202 73
    0x104100540c42c40683c2507005025807441140246410114840d001040820a640c000d880d10480721800f203440e28100e00400c003a45422003405c4d001031251202c0030300002040d51410088914060301d56840240d07007401520b10701c80c90340c40030301070108016103540850701610302c420080210b803c8444048221070b00c180304003030400895112a5100768400c0940342d10200b00b1244595940c980f40e44072001840311031040740a244020300c081054030001003032942045420800401400003024100000400c11400880c14003a802a00042c04044515036102d00f2038540c6031540c42c1c041c20f05040c40304100050340490504045605c1d0001070340c000381034969460300900030114420720f500d802030060600350040360303040001101c00034803000c0c400c1000c42039600d400406981516148010340c140d000781c04240305590000d4160b100c5507403003525407641c0000e00800109003000320f100801c1d800d5000b1201540000c521800c03240d4011b0b0100412100c84140c9120604e0a624141e9545c03549000b80d0402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 734410017 1250 734408767 734408783
    0xa060f090b04290403050309060603010b0a05040b0612010b04091113060c0c03050729072f0d150b0109030c120809030105070221030403080c3a0e060c07 67
    0x122100e607119040c03161500030340104030006070405003400b9040f1f42003201e0a228034801c41c40007880078103060250310302240c0003034842c099050500c2c040001410904401e00e401071003d001a420701c03c0180c0c006402004d0a00d156692581004458816540404120522203004201034680d0a00b4451072408a034014074101010a0280c41e0a41c909900e41c1c1c00900f180c420150302041242180002c0800c06200d209100740015501400782d04601410740b0161210806020308045400000500307816a00307442308810f82c81d408100011100c10703a43c08150f0740010082000d020510317551192030841242400d001c44694519075400300c010040e40070700c240000d0f45962810421107060300741d4100c101b00400034001e82c60b003284025a54880e007160b411607003541c003000c002080303801401c8a004e950182d44000c015a94440025807962141d00030058910442c55010f00d078071084a14030352009540d54038060f004504600349000e0301c1080c20504440d0f04800c081c800300311304e0b00b01101c40f0982d1001e01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 734411267 1250 734410017 734410043
    0x70914031c0c06060f1e1a0306120a060605090c0325030213080a031701240c06141b0a0c06230c070510230402030705120a060f090b04 59
    0x41214107082c0752000404042c105480840c0d000f01c0400307903005441e00420104d440740a010140c0314401940c2c861062151040003411100d411048021980610060040503030780503072141035460f100403058144d6103140d442000303014610381030000d950005400d401203800c3d400c024a00c42540d002601c200707408920f043d01c40c009900d0103901540c5030000c3d90480d8820195031440032544038009038108800242402c0f584042d02c0f210b0308030460507560b070811401c03002c003d046000418180003482a20a0010429030100040c0b2030b8003603841d0309034404002c83c000b802d205000c0f01700c0d915100030140c83c200f0144180b80c5400d40c030041d040f01154005c2c201040004050088007030810b802c914512681c0400da00b0840450760260081908911a100b12400c4605400400c0b04131038400c00c0f00541e0340f01d0204c40c110a81408585180c215000038152003109580c1c0c0005025404040e203821300507080b625160003801a58800c1032a00b5800000c24880000e0954440b000b001c0001c00c018040382c0d11000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 734412517 1250 734411267 734411323
    0x5030a090611040b0d050601111905100230090316020402040b0313030f03090f201017090109111002030d0c030b0907110d0e010302090d03030507091403 67
    0xc0000030644060300c06035070b01e4903040340c000c1c143e101c811782000880c101070200382c880d4403488860380c0707800c4400d0160020718040006005d100e40c02d088199014804d0f1002481035000c94401081e0848100c25001c600d0001c199203403500d20414511641c0152541e8104052000003008494400000700000562a40103200040c0280241d802c14601c0d44030110412912124183c8140310b514002d0b116410900c2c04200105d0560342c410500070000300c40002d0742c0c00020042c11a10902c000040c50007407a200340400490b460f403020b1104030b4002008940c0e444440a5030b0600c150300070362044024061200d094a078200009824029503004030801d4032201280c5100b0300c1515070540200700d05000c03000455034014050074150a401e489150b01c00b0104e0701003800707204017005a8074410b001e4401541440e00076581040340c9510a03051580800030020140c0e5071100c40d14850340303e5140003406082240f80100701207411341000086da40000c000c22100d41d030000d82c1140300c62080340c4201a05541034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 734413767 1250 734412517 734412521
    0x305070e01080903090f220518030703050409020903030c010e07260607050c0304150804120338031002130e04030903150f05040f111c060518060103050c04061505030a0906 75
    0x10380003240907c2c1c001c80451000f807050b0816805141005140c000190250103210748a10a040004010540c100000c000908031900030780303048000142034078141784481840340e0035504000041c90244e000701d1400d0219502d85881078140b00c110a1003100301a0250710b03119074030310700600210288000412203501d40602003040b540600025001c10551840032500036020300425901140c01c031202ea120162454400c0c4100c00c2044d19401e4400004001501451012510641200c410114085284086880400110040c5a045c040c0103039144035904d10f070b29015056412040c1c1c01314440301400301007640840c40f001501d8110b0340118500341c00303203030540051841c0c1c0107041c0e095042000f00030500c560510383d4034400d400b5404061030b05040c042005641201e801c0420f21610400034050701090142c0c0c03146c1c1c4d1103110300c58000260b1600b001036610b011026801100c1580c005038030f48045003000c0c018030000745500500c01000107503a2401034050b0000030412403d00d59a0343e40241400752617 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 734415017 1250 734413767 734413789
    0x21314040e150103030f0f080a0e0304080d0c060b100207032a140a060516080c0c0d08071406240a09020d020a02010b15041205100c0305070e01080903090f 68
    0x240488200b070740b1010301c1c400080c0e0248000e40210740e9040350041201e00842c01c035500710750141c0e20809243e580e000000008c0044042d210442d1000b4400440d00400412408440c10402c1d103840826214524004041d5440d0340281401240904c0b00c03007141340e030000b8080c030944c0d038050402001c0c01071102031400e001400007005540740d441c1180c0040c016011059000c40c0c2c0600303840c4035215946814040c0d0300c03032185405851290a0450042c030109400901405040101d5010b886d5492020070004000c41c0d41a2829545623400007505410000200f00481042040700081d040b0303882c00e03c464619a04585000346c2d0a0700c1c68105a0f031040e030711150180060030740c191045459954040c500c400035041884000d01542c40c00e11070000a25001c840400c01d00441c112262500e3b0030141d02417403003140c18408542500c030b802c605403510303a15806030040e403400f25500000e03c3c0c60580c1004007030301d60b0b05c08080d0500c40560f0074005e80401c00f01c111446102c0c180d0329142c0400401004c82c038070050f2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 734416267 1250 734415017 734415041
    0x50a02090a0e070f060f02010b011b0807020d0c0e0a061a090414041b05060310150909050a050703110a0801030303050603070302030307050303101a07021e06030901060602010f02131404 81
    0x40d501004c02c80c8602c00c50808250b885c0c40c0d5800408100c1580168203c40352032100070301082c40660212540e42c2c646501e5114075100c0c2c14400d080c0030050b808140c03401e0403514100c0701080096410b120300d50070805090b5001c18441c0051102c075160452583d80d040702360700316060107140040c400c5119180e5400c4203a0790320b0504881d0f0712520342820240305500000e0305200d28400001d0b0005010724000090302e0049240c005000d4590703191a0ba090342e01d0324900c0613034060066541c00003414840912a00b48615001c0d4004034240c6400180281112a004941c0902ca0b00c10f101c4c00583c15840458641540d0781070400155039191640020715000307144c0c0c0000c2d0300d488001200c00400c18080040c5004801021001c0c44441e107414038403544422042e440d01d0b411405210b04009450705100d562a00d0303820f044010303c9016a540482c0007640200d5004816039145c0b5420492a50309204c6d43d843c5580610003141803d088039030043c0303c9410741c8500d05100c0403503074030b44005a480354441140b03089 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 734417517 1250 734416267 734416273
    0x30801090b06040e150301180b010b07051e0f1207030e09070207090c1d0a0503060a020d09060e010b03060c0306060d050a320705460507020406050d050a02090a0e 71
    0x10303001031181c81c17941001000714003d508081000c55841114420a140d29510400212031a820301c041030f01690420103041c4d07044d20549070503094500c04480882c500d00b150101500000c0000c2c4034003464200c50140b082d121410070001c0314042680054200011041156488116117481c04101d140031401d4110381070942c640007891a5098100345840340c8003060601540010b89400e0401001105902c5010742540003540040d5881a1030703070050801c0c040ba16000035003140c140c4c076030004942c600718461001c0d03950758095001c540340422006034815030404040d403641c54040e000c10b000e409411801d28400f900c850200d80d03982c166801c2000052468011074a8804951042101c40550260450000c4801d20041480d59208404803984d2404070f4400450101c10a011507040b401429580d00715110181c0300a984601104aa41d603455102e64505031110700900411044554940c0580e200700c0315490500300003035000c01c5841d08950100c458a002c0e83d030350b8404034060310f0f84a100700700b180 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 734418767 1250 734417517 734417521
    0x12110d06020307111002090303120417130e0f060a060c02010c02060706060302120a0c03120513140a120b01030809130606020a14150402060a031d0d0f02030403030801090b06040e 78
    0x207038030510316a1806000405c40e2224103a01840d14103e10902003a0b40d015002000390170040746089a0041d003081c401c0c0b1624850003c07071258890300b90408101903a83d8500c0d0141007081c1d0200c0d01016402c20404460000c1a086c0900010108845441010240302c0985000803e580c02030350300340010b580160004c2c0e52046a4500a001481a40412841041d0341c541060001c0400200110040e501c40c7c0e44c0100142181c40d6040b0190b0003030f000000b0804200081c00d41842d0101c0350303000030403482039980308a07070f141d408215500105800168507120741c1c28542c004030302d0090000d41141c1e01310030300e10b50394030460011903480038600320010085401c0800c001215580050448400e40c011020322034a410028491600c440e00d443d0f4410902c810305000c00c001d440c0080081103a0095810000785410100260a0801040e6501c8212035004100c49024440d0001c100d0310408296101035864581159005003090106005242c00c42e542c43c41200703031546a80007200d0107031031030412040e894 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 734420017 1250 734418767 734418781
    0x905060306160219080a030e0d0507020f0f030102070506010302120a030909180f0b09010c0305010b181207080a12170703022b15050301020a050a03180209070c03030501060912110d060203 82
    0x80c0d4042041b050000386042d40b2144248400716030b2044000c41b65440038a40342c8960200401c80300141c11056100c00c1041401d03a0300d903070034801040394a110318058001ea6146004010088201440013074081c0c11080013140001d602101d04c2c0166058120005a4100000d601c0031420000707100040528252507140c105209200b03141511a54803880240300c0721201c0070040b816a1070a1045050400c000d0001d80c071540c010410310346c40b104000c0c01c4070b111110000c40c010f241c40001c1e031048035180c202035014021f008040308901850306060820941029180184000b2404010612006c01d580403416402c600304580350b0003144a505100303106810200b910940c014150b52041111009182e41c0003d00e41c01c1c1030090710214812901d81500700300040c40183c0c050980403a01c00400d041c10074412005035515104030307005078040d581d00001400b0a103400b4080b2041078000c0303010700520240812402c030351203424041841d440000841c400100c0000304072241d981910007402640003004001070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 734421267 1250 734420017 734420033
    0x61b0f05070b03090d0201110d0b2805130203040b180304050604060e09090708061b0c0105010905010627060c05241914010b132304060905060306160219 67
    0xf80300c40406030703803031004417150590880b0802050700a050790213100304071444c511580b1025844d0005080d9106260919003070a0040010404a4a00c95401e440900450070401101440205814400c51440c2080d48070480d1500000b00030098041e4104200390318010140140d400400d400342a0741d0311a0b03100d45010b0520401c001d03034036001d80c0c9107000186440c480016641e044030207000151641c0c0e1101c02d0007489150424801456070303003040000010800702413181074020009000f0004d6103505244009008180584104044404480e100c82640040c2140c0c3c101300c0e8940c2c00c2034070130003007280b070071908044486614042240c085044042c08420286220f44560b06805000c54910100542c00c070485002c624404280e04042c0014030211a0000003000d0b50801015024003c0b5500e00d03506003840c00e41e03241c885d0342d408008030b0361942e401d190003800080d1140790000d21044c50403902003035840e030004004864413241fa02440010500078000130420b0440030030707110640c008074245462 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 734422517 1250 734421267 734421271
    0xe0903041707090e060f160306120c0906050a08070e1512070302030f0114010504020c190f150207080a1d0406080c031209030a030c1104051503010f06061b0f05070b03 73
    0x443c20741444141d082841000c502c0304d10070040d0500b0401c8986034051f038a620200c401885005041c0d8640010614034950b8481240903449031680f03001b81d43c2080c0b000c0c400d4130404e6000711300a01c5542d8041c002c003840850701740142c81702e000c0100d1180d6a40c02100220390b4102103c40c2d00708100850944e012400400d089054034020f500316070002e000c5044490803101c0c100c60715505810b4040052140b07142503002003000560450856020421000f0040d90001100314202c500510106480040005840341702c000c0010901e000c50a144035074844120750300c510001c80080207040f9200c0245840002d08602c840100904204091610381c00010758404d02090411300c244110300304002c000880c8012143c0c80c0c000034018180e07030861030760103441c3c21014020481d141b0b81d5021090380c2c1a21203200b110303c82c10341154003039031649000c8281421117420b42000f0144a0915800744a00c503080306400c13803d1034074030611a11a00d5103081030072460000c2c80c0d00a0160240442c0000c8600c10740000d94 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 734423767 1250 734422517 734422529
    0xf030b090f16060e0d050f1b0105090114160503040803040602010b06040501020d050f0705030f070201120608190c03140a021009060c02040207080c06190e0a0c0e0903041707 76
    0x10142079a1200c082d60720707201107100c035400a0011500b8441903119030003400a005000c5c22081c00c01100e940c4083c20f0016060840403e80d0201d031b80c002c4269100028103614040a007840c0d4504800040000c02c11001d0402c101040741e80001c00341a902d00c2881741003000c9400100f42c80c0c8650b11a0703e45034895010b44903e50040d800d041c000499481d100044404540050700101500c907a180c200381c940f07412440072450241c0c0c003130002d503021950500c0241900108250441e960f42803e100142001002c600c60039441c80c40c111042c01004000112080d4441c14100c07240325006441c503049144003003680006180c024440d502e030a45c0c901c00039184880a03c01c0702d0034031a10214074411100c04169114060001e105c0303000d03407809801c069000b407100e2409027a10915190a509a0600d0690207507440321030031000f07030104840316590b40b051140b0752244401900c02846a500d81c411144201e0040904040900000c00c0003100100115002884240f1040c24960300482080341c80726003901c102 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 734425017 1250 734423767 734423773
    0xc12080603071a04060305180a03020d0909021903110c0106030515180a06050c070f0c060f0302130b0906040806010915060c1a0907050a03050105010306060b131503060f030b09 77
    0x420420360340079180da001a07011000f60305003031418004501903d4003402c4000720340341009409411a405000c0c4540c0540aa0018400001d43c0d07400180321035036950269640131300c1403014521040d809541d0403545100341c900400e0141c003e6551044500c03650801080f95860711800108201020070042030f00e050451f169202596031801e581016003102114102c07640040b080d83d00054202e9010541000c0ca100d140360074100b041c0d94011207240c40a10643d94089520400c200840c1d008203c40f0401042d45010f6050a110015440409109000381c9801e108c02090100c815201e08054a0003803071288101e6845582d58410000201b40c1e010310864904405c110100703009005540c00d2009552240081405882d203001071107034480c0142407000640540c800000d06903036039151080107140540000612540341d8a0103000b100c6840c2e01c140c1007080203204542040e04450500412a280806160103200d40e800b41100180459084042c00784089180442840300c8030015074405e10802c011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 734426267 1250 734425017 734425019
    0x4120f1214090c0604060c2607030c2f0d060e010513030212030601090b070f0b070e03060a0e0d08100801020409020c0c0d170d14070302090a0609180203070c1208060307 74
    0xc1c848107200b680500c0022034602071001f40003a80302e00b000120360f072015500c0c00c0790121041c0070418548c4240c00607800600109111000e02c210480c0d450703607e1106140f168000104d079004984c1c01c100c10050309100f2141c0811103c05d00045800c0924440427001c000c100c03c0c5004c0c0c4441651040142d015401403044a6a03c00c00b542c000d4201ca00440050f1110301c10186000031106695005a0301102c1448080d41c02000103022240c1d524081d1005d610383c2c9d481203007050240340c0b0f0010300030950100719050803050403441d18003151040e00c0802900d0415103983d80c4a00c0003015020355444000c00758400500083c001c9015400f40c00f640a60009441c01c86000104205050b400f09801500d564079004801c840c55420b41d0042180700c5031114003042e281c01c001e40600100c041140c6074000710780c0014200d070261801c981500094549424004c04060510300850303141074a56200e1203a540d40000031480c1980a148200000e65003c14040358107480c0b400018220300b0240c0e6424000c0c414180 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 734427517 1250 734426267 734426269
    0x40e01261b04021e04061107140907090e01031b0e0613020904091a150d050309010315030503220807060c08090d020d0b06130504120f1214090c 63
    0x220000810341006001418060500c03809003001401003507803142d804c0142a001c6591200e40c001103003540751040c0d407203600c0d200c400340041894404c0d800043e0407040341401600b01050001800420a0790440140e954011041d506400c16401a41444c1140300c000020040c48060080c202c40c4d480c14004001c84e0f90743d401040340e0b44152042644811704201c240b01d00d602903409070010240040001c11190340c90f465071030084044040c0b0a071441c861305d080105204620220036000030040e10840074464483c5c403001d03224054150f40c83e0415444181048500e03c98a0515018540080030b685e503645600c42c0680003680c141880e514800101e4000050a010200f181d2040700c0203911030044400e45552600e41d1903001d00c407100d90024214865101503201d4920b0412078034811030f44100d80d810414200328900c40342d05403e0034401d0030070080100191741801040741e21403141c103250306802e8021005036030340810090a058001d14051190f00c0e071110451003d4020740c0c241083d1121034000070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 734428767 1250 734427517 734427569
    0xa061401081302010c080d0f0605180402010504060305090c15070605060306160503090f010513050c0a06140306180a020d0b181803040305011104150c02030c15090402040e01 76
    0x26411071103203480b0a0080d0265000301004001c41703100d031440354901030002c607405080302c0c14600b8404450751b13900c4050186080200950102020480d46c0f0300d411700d80759000912501c80d5020304020992104042942e0900c10803a01402c0d41d4014900c451402d800103e0060301d81004409403852800e0901086940c00c000c680d0318000c4000c0b000380c22002c4c84040043e9800e52000c0c15092440c8901e0901000c0042e017841460700961503d0340301e149240d050708146142c51654005036204900480c010494a41c01502080c81b15444200036a165a6940300207032041c2c1c1071152090420021100300446488694010701001941e58402c102c0c01d2070301002c0c0300710340b03075100c90000354910500d002c10b8a0561191111203c80315403001c4032718041d220354859081d100020140072000c400402c0a01160203c1038600c2e11000c070f28071340110720a0701500003039542c0440030300140c014280003c013202d2883c0c18a0484020312005001550b03030303a54031000f4500b00e00003481001c550344c05040c1d41c44400d103480 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 734430017 1250 734428767 734428771
    0xa03050601120c050315090d02010510051e090c1c0225140322050102030a020717190b060405010506120a0c05120403033c050406140a06140108 63
    0x121004010341ea080260b10400d4001c2080705888100001c8000502540d04101d5070180c222200d4540da058100035a0040c90003030350302d1112081d039040204200d54885c102c2211403c58108440fa03107600c14254940200d2140c100c20601d401c00b5141c4200040501c425009155000442060441c0b000c0a51060b9040f80246901e1001402d014244074140412440d14104800c1c0540300c911400241644190300e55440707070312140d21074842420884d0700e04840e1085003000f00001e001440c90805144002910780c0c0144c003500c8202d2250f5811132083c000c04102c0072540c03424803004402441982d04000b02e81036012a0343c80d01c40d80c2000000710705420000280d602000541207406020f1300c0d418950340c0540704400e440b6007004010b005001c615070703d01c050103005a020391000155001e8100c2000251500d460401548a41c60170350011130341c0b40058411031000300004006000d880b103140c000041c082050760319813403240c0e500c24001d017041a9808181202c9802c080d030301c1442c06110054805800c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 734431267 1250 734430017 734430023
    0x6150903020d021e1027060e040507030b0409030215010b0901090b03061c080316140d02281115010f09050a0f060f03050c18130503040509040b060108060a03 69
    0x142c40c2a510050030001c403003000300008480000142c0040102060340c0f070080113603003400039050526a032071000c3d50843c41c003918460241404401810010b024000010084a4500480d569400601402c1c071035404820b180c0e400800078003410140d410b00a5560303896501c510305209902c3c000107011010b40c011207480d10010b03154080f46034a44955101c0c42d0b0802450b8903007000e18004011041201c070550101040e01c2078600e9a200c0c1082c2c0c14040c589031000702c801c0e052001c42900100d017280d4039019a8000c01c0740800142e542c01030341d00340d401401d40101800940450040a2041c480c1d00040421359090581b821500d2110003420180d10030380c000e00c180400c107580b500c02407001140e5070f00515400144070710f01003502502190403034121042e40c1d010522407281e01c2d10a20400c041071002020a500c129165951410075441c10503904102034115419000f240300e28004001c02401654000c1100501c000d0384c03460a401c1402c001e0104480450010744000c00146444c039101c2014400d90750 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 734432517 1250 734431267 734431279
    0x30c0b0309071229040b15151803030a03140a09020f0d050109020d0c0501020c030a2a18020d0e0a030c02010315032306073912030615090302 62
    0x4a081c0302d82c28101000181035505010464926001c84c07444503900a0301d58440d080b4500d00d141c18101041c0007400076080e402e0302d107070844049129590310b400c1d004030703170700880c21180c0c0d42d043e22004001c029007059100c0d909400007040301d60a41d509640000c40c102d019940022503a6102c01603101190700d4844002c0d4040055004010281401182065203074440c034000605148560002280e101a2240c2100c180b510780030b0070320445d43c0c1400f0014603504140c004003040d0784140d0300c81c2042503440510f9800a0810002041070784d00c2014601c0c0148000c801190605140200e4034020754480103007140c4160429010b0824800d000500611642d050303030391030804055580c01107010701040c038456000c080c030749130010001c10440d10045034180042c00c0e1004075100b4a01c109420890000d101d40700740000307004900003019803400e2280d8000d01c1107c0c110315440001402d114098070340e21000e4083d10740021100c85003070300350b07222406403003001800144032081481c0c112604017075404020b400c04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 734433767 1250 734432517 734432519
    0x240e071106091c030f0e070906090b010c1e0819020c2706040b101701090204050d060e0307081b0606030111121e040f030801120803270105010b04030c0b030907 70
    0x30900001c3c21942c0c01403502103151000320204005540046a0120240e000760804004100f014030a110080c4079a0b201440f040542c0c40c00641034880103000a003039072101c2030010309010b008810540c6020341c0300d0000342e1200d08003100b0034407a103070040c0d40388050300c201800b1481500d0701000340311861280d6404400c0d01070100340c0d41030f0401400740c00142c110b52a4001d4140c0c9983e004910b0811140a07681e404900800038071400020106078001c5c20a944100024403c0d40c03140f000d8000c9003a0001c4010500d80405089207103140700303120700a042071f91302164400c6110a22002d52244d110348004480203a11054105800c0711034003001c0f89a1064208804035008603a004115404a400341007030400c03a5242c0c100c00c880000858086610391030300e000c07140030942c00c15082070141610030550800d0000513070310b4800300d00c005440402c2d0300c0000c01d05114000c80e540c0206640d02e81a40090106582d60440c210031078001d40012100401d411101180019202099901c910101c0300244446 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 734435017 1250 734433767 734433793
    0x30c0b120a020c010923100506010f0807021203010f26071505270108071d010516061a030d0228030c050607080402011202120a240e07110609 62
    0x2c0d408072088800e65500c0d0981e000c00b080d440c0c0a054030412215101b500101c0609407080c0c00d10310003d440c150010710f003c050280da0790f481600c1034038004031402e0999032902e0f4030206030f150080d8400313890f0011070000004100100d01c091404121908906000444000380b244804403c078400a840b01641c0311042c1002070f0b4501c4540b4801c40011418103920304906200340c40507203c0142176036085050b200c0c0441c822941c0c03240e000c55100c3c400e0703c0c20303851101c001e05140d04c0650144a006040100102e000c1d011240100700807411154410380c20040324181414050843e40215441442400f030f41e0b001117621400841d8404400c0f0315140040c0604403070700c040c400b00340b000e082c050b01000074840191002030000c0101d01d003d20800d403070300c5c60310b854036200041c0840322249000442034018003502c92044251115250030001620012500341e4506076005481c11100c6004a84416172440010340399440907800d45c0518210760700c00b003d21024100490707a40c0b83c29a400f54655202d06003061503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 734436267 1250 734435017 734435021
    0x60306060f1c2001020712050a0314040504150e01061803021c021008060a0504020711040e010e100f0b060c120a17070503090d02060907090f090b040c030c0b120a 71
    0x1007002404440b03203039801c81e455502d01003028503440c589201c54203440c00141d42e01000070744000c20104080c00c0350301c2501e503a00d984620301008004c040c0030078541202d0341c00c2ea881c4280e0700500301c094010408110741c142031208003d858811744800c40444400400c010f4407907000110300c43c20042030b005074649542c1c02d22120400c45000056218900e0306400016560241000102921a695000c5908211041004a601541c041e03842640b04024980014802c2c154580d4104402c84001540601000360a030140005404480c0b007406900042092010a68040303441c1c103c00081c100484c07281c40040c0040ca01c01d41d6121030300e070750000d04020000d038088030003080020b44925018849900240304000383c90420b94403003011070408001c0124040040040740c0c4040034520041805080244000780c555025009440a20741c40d41707105000c54410f034112060383c55003c4c0c13009616140074140307104203140c1400226064034020000090301c0c941d1005a43c1c00d40004090740c030740c50721030b4050640 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 734437517 1250 734436267 734436289
    0x60f1201021902010e030a11030702040203090a03030509010c0806090709030b010b0a090f030305090d060b040f0606110610060c0c1502031e090a06030b030a0b04060f0c02150703020708040b070f0b060306060f 91
    0x2c1e0030709c020404000180c0f10781c000345004012140052070180704519001d010b40d0001084c10340180c0c9080358038280241c0c40119550071010035a0003c0c0c0315141c0b1102260b50118540028000c9001d5100001c3d541c00020700038214401e071955920340d00da0f1504903425000c0843d01c00a0002541480001c0f42d5140010407595103d10072100050010319900c041000d840c80011201c41c04e60759020104141c0c0e40022040502010303100c0584010702d41503040f1841d5103414001c0c103003013102058607201040b03001d1165801812a031803407012190140b50000b5034903031102643e140b0242203500501c0710704200100b034681030b4000a003d5045103052240840c02401000f4801c1c1d414450100e1301008030307040584150056002d2440420921445d03480c0d40e00341c1e03d51038582c40440d4800301006c000c0c3c1c000d8030002a001000d07450f000d42d0310b600500f44180b05000d250020400f5031000074602c1d0401c000d202030b07010801d20800c40b0a20f643d0b0fa90741015100c5d54211401da0700008158040840c0c2d1525240d0a4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 734438767 1250 734437517 734437547
    0x30509010e06130614250b2214030f041e05010c03090603090204020d151e08151f0f0e0c04050108060d020a0b0d0506210a060203060f1201021902010e030a 68
    0x6081007100d103800c030a0240b1401390b00c201400c40841b00814024001d0805505ca080c90741d41c1c0c000045002100052204400006040340d00900100b0b030400718140b04440101c0c2c000058941c807503407118402154580d551201081c1d82c481c000d000109035000303400d0490f4032034040d1140d500303091810000b40c000d4100034034126845a800c0103a050201103d220b074401448582070340e400c0c031a0400420039049481009400c2130840011b0703041046a0001613030070b1044000d200207110342c4d00e50203403a0f1420140f0700c14003000404030740000704405008910420407984130202503201ea81794030714800841c0c4514003455000130f002d100054a1410f182002401c800c1c400740101e0300703503a070311109064250000d03082c0c04440e90300c07031060060a10341441030f810140c4146031131f0100006107903c90384ea01c050003000100111f0b0040300003601a40d8954600c20b50400142a00840c0990aa1000c0c000c0d4001e400d0000786608180b81c5d5100a803052050075401e00980e0300071403a01402000a5810f031458a07456 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 734440017 1250 734438767 734438807
    0x14010518010c0c060806100329040b040603030c15021602010f09080102030702010f150602070e0c0c0106030303090614041101051e19020d030c0815130504030509010e061306 76
    0x1110003d40d44028010013032100707503986502400e03d40100000628840c0c102400c050402c4e844c104100601c10280c8075202c003044c10040044148008280035190030390321580e21070301e8000c0000c1416000000003810074400d0b03c103130a0700324404810174102d005003d15406100446440940154040c4000500c000528103004101e2a601d0310000d0a981c0102c9904006075111038541c251030401c1c2c090000020b20035401c0401e2a810450025514105032240605c0080080f0100c0c0140c8032103011102544c004000a200031078990501078090081c01104a400b64030308032440c0b00c1039095007030079400b80e40e00060b00d41c280700103000110345507000b21217640080e00144064901c2d41c1610801001840107008400007140801100682803116040c0181e00f03150a21b00100d6003187c0c0500070a9120b15205a070314251920741d00400c81c100c1c1305502c0030060303d00c0c0105110a0640200140003107180c243d032103020100b0f501040c480d0b18025400c484152360071520701030103854000c00c00d1740e200700315031000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 734441267 1250 734440017 734440037
    0xb01090c0c0b090c0109050301021222060e03030712050403231303050709050f010b0301030204110c0d03200f0d1802090a0905010f05060f0f03010209060409020c06011401051801 78
    0x4014080500fa28650b4180c0e012144c519025600004644000e0400318000c505040481c00b201d0381f101c500034981440440c69200f400d1a400214500c0e203510394000008000c10280f0151056582e481501c0b45004103007410303032b85100c0e21003a004a5121b1545581c481c0241c3d030340f1103000c904402c94900e00c00413500007030103a2040c030168451500000c5010780010042c946c50025094200e81d80684113005524a143c0103010300c005503c11203044030782c1500d000900810700c4100200901944110071194001e8066000007154107400903444038990706044410342c0000745e0308110f284200384078528500303c02c1c08040364101c510b620080b507044031400c031401c4e41440e035400180004c4040310f0400e041d07a0388071080720500609102c0c00c0340e62208a9800c0001c0d00340303400015950b12050f1055482041281440c00c1384d0349080d01030b55014440501003540b5a919107100e02c0185d0407241407440244510400000d190306045001d5100c240103850b07191600d8440003000c0d00d00d400070f14040d070620608cd09 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 734442517 1250 734441267 734441273
    0xd1a15120c1e1206221e081c051005012f030c0d0f09090504020f060a020f03040605071e030903380711060c042d0924030b01090c0c 58
    0x8aa03882c921248003d4589840e0000003c44055034409580e40d281117243e6018000519224a11078031070000d481c40159000b04e4505807001d442544003003819a0f140510020440c1c619800640c090b2224000d00f0b24a40c0e1900011108500c2e030320b0158060f07001742941d0400b02040d03284a1118401a82d00303070f80c034140f03860840c149480030a0203180e0000e040e029108074165480b89070100600a00c010900240c00c06400207003000b041c500795507101c1c0d5000142094014001c00242800c41e0b40242030380c0d2a00e507030340005002ea4010030800e40310f42c80600000c88003020040084900554107898010303d05045850b401403480c1e24141ea9440c0140c50242d0303001d075401c4800c40c04100c42c0100302d49104c52509810081428181000c804a241c0c81982800740510a002c10340c1c05540509941812210798100540c220b000c585c200b54190850321280071400c0030080c2c01074a4104008030080312006840c00d18128445194880508001071450051003420b03a6500a802c81840701c2c642203541d105952 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 734443767 1250 734442517 734442529
    0x7060606091a130303080c0909040326060a0303031d01060b03180c130f180804090b10090b0a0e180f13020117060d1a15120c1e 56
    0x60001800725103241820040d140310030800c0b000d150644103485082640f80b0f02100c941c10564003005007801001400181a0654078040d01c0c007400740149a4081c500742400c0c0038001e0186060090131144001c14903954101440d0182e9008401c0600a880d0351071643d10103d0040c0b40f100000c030580c910116015140380390034001c501c0502550200315649040124181070142c0c03c2c9071410040c0c0c0c10aa084c2d0803250703035136001c555840900c118041144010504207170002c0c8102c0c2d18400c0259000d428031828000114050401e0ba00c5514081005096010802240c85618401c0c800080c6410500b846007001201c0504082d03540c0c0d00f0920300e440b078958002840d44070f40c41e10807a4010b8001e02001480804040c1c2160002d0302901c041240035107035000207040d0650261450b10609504000c14000c0c0c94103070300e82408071382000009401030003070807013118078460517145000720401101030303600c05180c880c003c1a0301030540703801003c1110102007400041c0c554424450540d040d611440740e8076803605 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 734445017 1250 734443767 734443769
    0x90c010e0d0c0b04091e0902060d050a33090605060d110d0204060c0c0603110714120c100b0a050a1403100606020a0506011a250f21030e03090609030102070606 70
    0x144c41e012500415980480c6e507080c0b103081e400b924850400b6032160260302c1c0c46044400308494104042003d640d0f400f10000908241c2c039280303004c000903101180c00041460446101c19072000864008507590303074000001e860542c00745a030322076010403e528125400d0f5209000303045100701058100a8103015020480e04a1b904c524085072110990b1820044c84c0e04100c4050035031400d080218400c40c0304a0456401402c40c014240440c207003018090480c20030503c0c10314180e101c02c503662074603000c13801600d42e182e1050043d121803d00e085100a80381c80c0b2a04000e50781c0241c0554056494031101c0707200380d800f82465036050700070740241d20346030716090152002410b0300790000e0000c2480380c03900c2450280160310824400801c540c01e1040081a0070448640c40a6441c03c0748440c107a01364850340312150000010004010000c810007040294010241d802c2e181c4c0030810f600104d42d03007043e401d42d2040c4880001c01d40040000d602d10b45131480140c648044060001030034483d16a071000106c85007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 734446267 1250 734445017 734445029
    0xb18010c11031605010f020f061b0409230906060f06220305030a0909021602040b0a0b03010806040b01090c1e02070302030a1a0123011407050105150108090c010e0d0c0b04 75
    0xc5070030500c8296000f55511b8000003035480140740c40d01c2c0115000f0381380c1101801405040140300b070002d1a48007400180e801030541e0754410400380442c84d4240208000104010501e55480c0d4001200f00c10041040d5204034400342c04000012000c1c000c00c5034650085400d58201129201c854540040d01d0f603001c0702a500c03540c01150307500e40d94038010702417031596400315002c94010000003055909902c131545409030b05480118102e800d1500240400403150014405644040000039600350300043ea540500c2c0038a144440f05e903259112a002d48003080c070303c000441c0040482d0085020381420a800c0d1141d141305540c0b040342c0700d40c00030341401c1031102d040d6944402c04907002095030304110382a0040041003a54101250b100061460602c180c607a903e05205c0b485140e0f60351910241e040b0b5004940c0100200281e02d000e4101043c1000340e0340107580050803040004613801d0001440c1a80780005848101d40c00d08041c0801c1203100101d0000c5510b1011721200140c907061b881c000e8005000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 734447517 1250 734446267 734446303
    0x60b0604032f0415030807051f0207060b2b02030c120604020f0603190218040903080702010501090b06070f1a0405060417040303080112022412010b18010c1103 70
    0x3502101035603901071000103483c4074629080c111a400e0f040140301c0000c0781d0348190003580360311050400c00d0070a2a0303e101074501d440310346d2810044c0e41c684e0b401050030f140b00b1a010040441c940c414860040c10ba046480000c1c0458420341c0f80c0d1200c4000171440c0a44000c00f100c1407000d46202080d1000303115400300400703502602c103100440c03a0507224036403200026117500d800c41c94450001c0120b0b40320455007020117070f0300040c03000001110140d07280d05448003402c280300103c81881d00a00c0740c141140d03a50015441e240c00403528410341d000b40e888251009080c5070401e5007649030044522080c203403c54003407141000f003007031000801701c140d482640100060485d43c501410b0404240000c0302c03440c0c00d4644104010b100007a004404181913035004000c20038020307200c1c80411290600c060800e5401142c00c80183c084003448002010203420101c0310446a036602c2080302d6590041500d1780e11070b08900c40c1c118100c0d511030741d440d117465402868035141d14188440417030b05101711b000d0705000601c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 734448767 1250 734447517 734447573
    0x2040f020c010e0a120c03030b300601240c0b0f060109080303090d0804080d0509061009112b0f0207210801140a0b0f0d0b030a080403060b060403 64
    0x80c0030f1044004000070400581103080e041d0b505c80c1c5070310000c00010b10500a662030341009140c82580107250301e8401804007281162829090701d694561205642e600c1119440e90007815075020614604075034109030800c12920405940000010f10340d0322520801400b0511040481c00595295008048400b5100502d05250300010000c2a8540011440303520030814400c2010b000141c0b481c80f440940341c50001902d42e131400c1e9580c0d11540c150980040d00327040500051a0002c0342c240d0140309007100c070b003144542d51100030082d00c1d1101900b030004541402840c10442d41e201000c1a100c0d4020041014249100c07800c00071154421a511805a4007141a10030841500300b81101940414640c00e0180080e4000411210050090300004034100000118540710401d4100190403031902c0b4a0300e42c10000503807151134104542d41041c1505001040f0042d04020600e01d11440c2c00966091903e411502c851002d80641c50660b60807440401000010038034805540420341c41c0c52402110b10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 734450017 1250 734448767 734448787
    0xd031205070e09100e06030706080604020d0b03031c1d03072d052a09070c05011e090b010b0a170c070c060824010c030e040905120c0d0302090d0303021602040f02 71
    0x80f510003801b040c0698003000d818044030340c000d40a990b01c400c0c11038015a8a5000610020141c01c04482c226014400030490202001c0b041d5015641c004d0403d104101000144080d08500b010090380405143c000300009004203881e0b08544a410f25030780c40c1c3d007202c03e070228010504651001d41c10340d61030b0001039109070b503c42c126041921b016098880315000002e00340004141d07001c0900140d080c08901c846040070820300b9000385004601d0348100b610b60709003031710b58403000e000050f000f1680d0300e904000105160890303000b031343c1e650440b540e0360b4203000d02144d21800052401618100545e10140581c000050b00801c9003c05010f0f03690b106080c50903c9002c2c0c60707070010101240c400306102c401c00c4c4603907a44d0000e0000b10301501031a10901300003559000c14002d2512400141c114041d007220000c01410f50001030560003040c804035961090f002c1000c4003280501d9400030340c885412078078040803a21070b07000380045240303402031448400e0280e80000c08442503140007004254001c2000444 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 734451267 1250 734450017 734450039
    0x305030f04080712120c060b04021306140f0a1d0d210f1e1707020a02010212070507050f0103020c070609150e030705120f07060513050d031205070e0910 67
    0x40c5542c86444504440941e15402c517109001044001c111000742c600e4184003e0b0340004800e020050011541c50240b05100c11180d101c9026030f0f0081081003480002e07036840700e4100c2d4110000c4441e22400c0c10014503040b100c5820640c0b002c3d04500c000b01000c0180c3d640c2c00104241c240c481d4050b0686645401034015402d40072001050501c260304044115840d040117415a01509400511121024600056440c4980c8810301403c82c1580010010301d650001000b404641c000d03001c40b8074602585030800b09500c1004401841c94001020810041c02d01d102c080000d102e05040c05070826213510945864403042c1d81c401000204081e108000d8071a10b640d601148511615180410503214008a507450342184145809021410900203032600d044c40000d41640d010f9007552203642c0c0c0c1d0740008000707401c40004543c52503501c0d20000350707901d000c042c4000419032644a0103428801911480f00070032004121206001e9095180d10265980d1090240301c1c60503442040c0340c1e18200a40c0d101 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 734452517 1250 734451267 734451269
    0x209090601080910020c161d180c01120902090a09122d0905060a1d04020403120f0302041e0f090e0a060b0f0d0b19020f220305030f040807 61
    0x7050103040018890124800f1424025020705101d01580c0c5c0c0341318280710b500d01404280b951070318240d80503010400d00110340300a11480040c0d0501c99407a1254001041c00c241c012469024a40c01021710a01e154010b0001409449104500080c0c4041c10340200c2c02c081c9046034260090303540c071034070107040200b600045140540c0510b44540c0041030003680c1e040c0d41324040c0c0c5007240b40c050540607824171446248010060100075007519103d140c60074026100700242d840c804111703100300305280401e041030300c00c1d1030440360010f02d10446081200810760303e14004600190415408010104d880100705880e9188042150080c03a40380380790883c001c0c4240b200b03800c1884210700304070915070581c40001d60190210b03000b800000c0c6d0700d0024400a03900313141c08800c03c0d4004011650b008203105402c0d4030030303101d200004800d005088808041808a00c1600c09050b045070040c40407485215403c030b4015281d43c42c2da003203500c20302d44a468403407864005a00c50300441000003814004c45100303000444c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 734453767 1250 734452517 734452519
    0x41a010608090730080c2103060d03140c0307020405100e0115171320010504140418080c16050102060c0c2104050a05030606060d2a0302090906 63
    0x2007907080c00019140c4841d958410f030304070300c04c003006070b409032100c0511101822080700d0800c1c070742e168042c5044100740d00009038451481c0251291207000e00258076009252040c81c0c42100d15580e98001080300c81d400b0240251304000c40c20700f0b4043c820004200034508100410b002f551210b89038410041a95030081c40030300d02d41042c900030070442c0414460a07040d541060f89089444030f042030201c600100c00381d24945520204c03424400281c442e4410401000d002d40700c2d11581040e4410a001440c05030121103002a6080004002000c0128a00d00c003140d0b0081011841018070540c08034856250041030315020710008a5288004003000602c0c40701d0154403112040c60301d40701c0040d45608000740782e202146070006000c10040802c1c0244040d5810b1040034403182c0d551004041c50343c0c1c0040c044c0364003960b10140b0110741440c0c00103185114120007071005180840141309a00034140b40c840038600030405451049030701d60441406c1030303440066900180c8441e041002c11100400140c1a5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 734455017 1250 734453767 734453777
    0x1b0c01020c1f15050a05120a15060f0506180f040e0a1a0108070305070302090604060320040528090602040305030a0e030c12030307030b0f0a17010509010c09060c05070b03041a0106 79
    0x800c04c60319295140011994212203046411002d03000c800d04101c100c4030018607103000010343c612074900e40d60000b42902c900030304024039180c403030051100c14411410b480a59900c4000005103c0c40d0110042d0791180c8098000f2518000ca101c0040c68201301c0001201c08006085504400051600209005001c3c1c1c0004044040c03441e2030f81501d600c11400041e000303010b4600006d51f1a150342d00804003c1d648070203d07041101c0b0515070a400304824003421803046040801007540b03902240b41c80c1d18080200825071014501100300700c4000e11031240e049460680034440000428401d0018101c044507545940d130302c010402c410141030144001c441031040780000c9403194808400400e41e68450700a00340014080d20b00f40c005045040c0c402d032600e500c24455040410000030700c0c001c0041d01d2032a030009201c5070b22600315007800d9a4140c0e005100048040c0380030015070b482a460b2001c0d190084040e598010388a0069141650044500761294002c5003002a10b050b02e141410340104014904 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 734456267 1250 734455017 734455019
    0x32e030c082b0509061e09040c0807020c0108100f080d17040c0e060f030d02010905010e0a3815130b1c060b03030a0c14061b0c01020c1f15 61
    0x94189030008205010200030f030100312032090381c41e41800c88800d030480b40d542c1107041541c0c0b540c101d940d51107214114069400e000306c0c07440c00d0303004010342ea000704150f402500d1500c2c2c031100110782030900140400c031b07d91030388000080c1d00103150009001500c8140c014080590300800040d008521070700301e1300807a215100400011448a4600606890742e01c0000511610741c00001001844215081ca6040c0035019810341196015400141400d1040c002031200c04005151143c0b030700401300e0050140154001034410b00e280c40c0c14400012480c003a5044040004e00094031510350b0215104c8140600b03500d0312403158a08044900803803020094180580c2d20b01c0c03008208500080040b07103c40e009201070b0740040003200d0b0000e103c0c1403809001c80b074581c500804000c10084510805903280346030001e4440c0072040124400c1d10a400c80100c032400c42200015102041e881805030007100e5509106600840005010880b1022004003071040c0b01400119000c0c1207500d50700305442c0040000d90 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 734457517 1250 734456267 734456323
    0xc1e0b1014040b0f04050a0605011b021807050c01062c070903110103020d020f070b013011031f0c0504060e0409170706091511032e030c08 61
    0x100c9114010082d1404560744841001081d202e501420307003d40c1c05410310382001480149a072000d400c80f0003d9031041005d00294140d07841000b10950041c0d00154100000001e42c4000000d03160005403920300140303416000c4001e00d007124001e411840600352072a044004c58100718800002011550544d0001340c00d0440015101c1c444a110040c40c03030300c9004401000340e00a5044d50183d42c400d90b4155541c50102410702126400700c081250066441800400c03640e00f41d0002c40c0d1030440014000404000803411112030310150441103070307009803204440c01c03903031001d009000c0504161200d1440001f090300d41d0750306440400c4000401c000051104108280d1b001c500e170104404155800900301d961030410a00c0700f41d80f020010300000001034001e041103a1640030081d107502980d0021207010321494200180c8001050028651800f840480c0c402e0303080044082200c40000d50788002c114201c928001c9200c440d510640c0d001040324800c1105071400d00a82082c86001091650382c946046 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 734458767 1250 734457517 734457539
    0xc0d08100e2701020c06010312050301030b0c07050a061e06060206060330070c03060501060e0a090c0c060e03070302010501050f01090620100515040902090114010c1e0b10 75
    0x14556841e0191940100d20b00305819400c07a2920316080000703540e52900002100d5640348203101c2100ca4801c00111074442500c0340342982d0580703034032031070100071a1a02640c5030f080d03400070441610b450084000100c009426480b86101200d01c0a07007a2005041c0b200000d002c90702190702820640d04941c0801c442c80e540030860a0f0a8440054182c02040c0c08583d007000780b41ca107140c0d042248500180304000d00609041020490340b003008184116a02c0364401c0f40d00c41000440c4580010540c80e05118030f058903004162410300e24507000407241300d15242c11081d44c2d019400012070340c000085241c1415070a008050141c0700907541030104010801c0028005001803261004101200d50314070342040c000b002c0c003a99002088100c59840058100c0d8000a110940f003d403042130107000440766070b0402d8014098400d07002448103500da0710780f01d140105800d05030041e604104600c035104001800c51403925900802c00303081d40b50008110314101296090261000840d20284001007042103000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 734460017 1250 734458767 734458771
    0x12060302010f180e010308030f07030c020a032d0302040518011a2809230a050108060310090f1202031611060d0524101403040c05060c0d08100e 63
    0xa10f49410200f80841440003a00c006400c12075400c20b80c10000024450351002a60141d0b8040307222607000d454555040e4126400704c410034025800ca1040c000201e40503421000042a0550a03e00014001c90440c2c60340316145110401090740483c041c00341e0704081c64041525003c2034101e41e81c95040586480f42014005007040c1e030407900050050034101940034030404603a00308084035082000c1c40025054850902421000d030045861004034000c4c280562a090503001e002c00c840c160800004540402c4018100c60701440385407101d840440c210f1080f0700b101800f0f0480001c2031a00d900c4c14204050340103000d803003154001c3c07092102440443d5545416294000b4190340550400000b044c241c2c016074a000c0d0b203035490302c01000b160800a402e120601c6e103082c403660407604410300401c1041c4841410180014404403d40760314419002c0045400901070400c02c0e80803a640c030001541e80c2d004450345190794003d0610b8640058020507001e402108030603039604000d003410a41c145070000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 734461267 1250 734460017 734460047
    0xb070206030c0c0a1703060f09011404090302011b030b030d05070314181e010305092d0102090406081011030c0901052208010b010e03060c03010b1305040212071206030201 75
    0x2035a50741000c3c00304040509990f20a10310401c0004a44c0c142403141c00484859001c0c41038240c0b00310491520301201416035001d083c0c1850303036600d21400d02c03008054003d002c40a40d1b68840e0071100002410403403412450160703070003103601450348050604114490401009006092005000080d00004450350030300440c0703081c60311122009582000040304002581d0404c9000809140420b41150b015800a0080e00c00340400d80381d10181664444181c0300c5203541240428003034065060740004114031052031000542019428070010b012542c6561103242c5c0e9030700ca206507010f00d1049000c0c1c000010003d40707109042d0b15150b00966038504c500c0d2000c6040003c006141c40842080c48140700e480501c0004281c5415141c10b016802072142c040c100c0c0c00700300c5a4000302440d02d800112144201203103c200c3e400c1d41d180c910150507540101c07907a180460035002002c101030303ca030b101505600241118042c03540c1820710015001d081107660205016050190900260340c00140412800d0a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 734462517 1250 734461267 734461291
    0x3060901050607060f140f1e0612120f04150f0903110d060e06011a0c030a0e0612070315080102070b070f09120501091208010e042315100b07020603 65
    0x102d91401400905e109041c80040302d241c12029140111880221032081c00040000b000c140c03240c240b05420400032000c0c070940c02041c140014030f103040c031642c0f40c040c1c41a0704046401032111010310040b5500402444018180c3c08203007005200c104518400c3c04840b103040c129100042103030020702d8075109000152007499110500541600c61080030740c07040d07800402c10011200d00d070070400e48034007003803284420b650045003012002e400841c04072440051044000e5180044c40a42503a805210070130b001d5201c5014807200b00011248507030644151841d0340c000030751035900000500031840725004520140e1041c00228005200c0d4211183c01c00701904007a0305001d02101c0c00c4a218420342c220070030040f0010b20040c1003000541013201258429644c6111100301d141048a514800f4402c00303d54050301030100e001304448507092044c0c03035800801a6200c00510b2032281c07801c0280d044926080c602101080360051450038a50f01403c00101128078040071070300041d41500001c1c000c00c0300c0e81 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 734463767 1250 734462517 734462527
    0xc0109030c05062802010b09010504230a060803070b070810030203150a0b04020f13050d0b04080a1404170d1107060503060f030d0210110403020901091517030406110102030609010506 80
    0x10001d003404c42003540811901100d80b442e110b200078041e040401e103190148083c58000700742e46c54540502440005007009402140c6004e80d2600040071010b440250820745d203071000306040c3c0040c0010724115004244041e43e6042a060091000c280108100845900c0300024001a40c010815071440c0001e158080c03d15198007851500804102c8403c540c45031000621b584541030070b00182c241000d480800007042690f034000c0c400c3ca403c401e44000c1c100b02003100050005071b08031024040180c83c6e032429a0101d8060b10b600c600d00c1e0f0207500445240150180b40185001b0200150980368203d450040e0210307a4600600d5075400301405500103110010000550648821054400d1518020308076117004880c0034000c0d4980f4469810590780e10306022000d980a0002c2007100e08032a070107842044143e00c0c1161001c0281034500400f910312080300b2000510340c4520501c89120103004002c2c564451500c880a010303003801211701e00741d40c1d006000b084015510703200c21504581081d101341d9551 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 734465017 1250 734463767 734463787
    0x1406071b0b1b0c010911030a020a05010c05030702060409020d0b0d05071a0d140709060f0c02041d0706030203150a050f0f010513180605091303140409050a0e0c0109030c0506 76
    0x460062440d09040c80e00220f0340842d2000c05400030040140190300340c2c1d0421400c03506050700c0d6180980060340001c1d030040d0810442d441581d508205078000c0b800e4078181a130690000b502540039601c42000c454001c01c1d42148000c0503c20b441f00c500048031121040811960341c1520b400103803241c0c10b0721460206928202400040031568800c1000b80d041052803a24403581ea04030605442d0007002500c01c3c000482c100d4010040420b4080c12901d0320340c0c18180f0b950800c03010b813100b414a03d180508092644207959410820742010700300307649003d81c5a1804030b5200780c4030075030710f20128428810041c0400450f221024002c4181d88140c440b501e01d4602d2000584142c03140f00c0c2c503410000802c1800282c00c1150b0f00304511140d02d11501404040c0c0c0d200100450190191003107000e0b00c4030200d10000003402403100701c1c1784a03a0506000d0034182e5552000b81110400c6880310426a200d82c0e11b5041b0280510400c209144242040c8004070305644400114811900540d0301404000904a00b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 734466267 1250 734465017 734465041
    0x6010309020603040b0403020111040f210f0b15040908091002120304060614010305091c090801020a05030a110a0801090e100e100f022b0609091406071b0b 68
    0x41074002d44415901d08041c0707010035415600f00c0f002c3c1c005500c0c102c07629081241500c100d070b00700c40f000107a81500d1420b020115280413104900c0070f41d2106000e41500c00103d081842a83e12400380d03009804c2e03841d24102a00740703070071610342d083d21071443c1820807000294900309482c0c009009450203c00d541440d4816031408000d92001890f011012040100704105908810251444a0000311081402c40010f409880e010ba0b080350207074201e0441c1226541c80144601c40001d070340d10304510305598400320703c1c0c01ca03405a04404009000001003207410301c941d0207a00700e100804009a031412a0900000300320050602036041d40ca62292040d0010300c408121009045200c040304218800e010785005680d40b60807510307a01c20034246450b10066440314030030364280007100d0b0540c0d0408920514040c8084070b038005000c0600f9a252408118070030544204200310348120714001514896603030961030500010852020491030340d1031624041c10032421400b82517070200c0440e2450320f0b400f001c0f0303903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 734467517 1250 734466267 734466281
    0x140c0c0d03030e062208030c041d1519031b09020309070608181f090b1303020c091005061b030a030923150604181506060306051c0c08100c03060503010b01090e060103 73
    0x1c518007005810f20124200c10955401442c500300c10040b4204404180114018148404841000c10033820804101441c11108000034104201c144091701c8502100498009441d07011099001d84000d00c080c5400002950300003820002d9003a1080301c5208403951036800070202503001051390150620718001d60040c00782039900010800d014507041241d05030250507442d040d401842805d103800c0850034401852030107032105100c0340d80d04a060405101e101c0e0b01c1035400309480c502032007002504003c02d0003d00040001c07582c022416601d9030502981c61000a8904e008540e401221214004400607803900380d401d4866030501c40d1342c2d490001074020541d403008205514410035901040204444d5404800c1314100801c100c01030700d4103400c408883c400d02070160001b0340401291130001200100d02c96036403049002410068440101a0a014114506480d00e64541c50019038164060090601411055008003ca00b8507280007c05119040c41105005039140c40810203691090b00024 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 734468767 1250 734467517 734467529
    0x30403050d031a010519030c020a02060c070608070f020607080a02040b120402092a03040507080708070608010e06210c060f04081c140c0c0d03030e062208030c04 71
    0x62101c004144015010340400400310600407400c1e900d1110030b40c0a9400d882c0200881225010203c03d00300c003d41c000c052081e595001e51042d581751800507581c05005149a070b404e000038080b810300d0800e0140012101074a4801401502c139a0715482e40c4d4006a2907030701c40d0b690f183c0b0f091036868a010600091155030400d02c0e081c0d400240c21110f030b182003808240254400d40f4662156a42c1e6034040c2510640764000c01c402d0007054900381c44903510400510b810501a20030303103441c15926003900d4503004030fa0380080410b82102500b0050550070030720550040c40e20300321199051410800250300d41c40c075031005c20491180394960f10500e1104101c0001d981d2805030100381d039041103001241c1c1d0b5402511a040a43c0300707000c5904950b019850f51640c3d420400d8617030746400048001e1585807a0445c603289421481044214121503271010703145120700340207881c00560313051098400b5050080060001c2501c001c8040c85821501c01c41341d551926941108441e9100e865884405c4080e00c50342e8498 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 734470017 1250 734468767 734468773
    0x10c020604060201020307180f09230907030312021e030a1104140406170a02120f240603010b09011a1b010c090e070804020d0501140a0b010e03030310031403040305 72
    0x100b041901540154007920842d103a14000004018007160103441e1401107504120903544104030540d0560070010590902201e0341041001130b061440b0702d00c5c0e04031035411817075110340d03010030a05400c40010303900d2100c5400e056141250411080141c0c600f00400e11289400c00800161a0782041e0b0100d040c110300300246c036545a40e6804030b80d00103c2e040c00740500c150700d420760010700007900e82524002c4d0710801018240a840a070200500307408186000d0f1214003d0000a19200c0c0c0c003844035490b2000c1881080304103101c041088201c40d40001e01141c040c5c0c1c50250096080e9035102d88050449010100512942c504662580c400c0e00801000740101800c91511803007810341900104582001656070300c0301e4941d078500940c080003094441a011030143c42c0410b001d81001342e91110b500e400ba0001180d5035500070064891210100c43c15042c4695990000460f580e2040310b4045444c1c3c110021b42c19818501d20050240c00c140c40300500030403110300400131444050041c1d600864108044d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 734471267 1250 734470017 734470019
    0x1b2b0b190e0706110a0c0909050a05060109020406110c0a0509060d06151e1401032310030507230f0406051201020c0d030e1b0319081207081311010c020604 68
    0x415566071160f0140b50042618841c814010750400622802101d4011803a4140c05284c040440001d0400000c01c1c0d03054000c142003813001c1442044428000c095541c1d006036601c9c030f4042c0003082e42c00030015244a64002d00401002d558442010700300b658801c40b480305081c1c07207850000d1194405074100500e41c900304140c51b00c0c40b0070b8410340f40341101d01d4040014a481c000c05500190144103000703d00d14902d101c81c09540c01d500c41d82c014850400b00080448004800200480950204aa108000144040040c07080010034000c0400501c0621000b900710080c09681030310f2180550041030058448401c10302459440341c0000009080141400c8025403050302c07a14042d500604203000644103480c1d800e6006407192085540c40484840603008855901101230500703181541101e0b032500c601d60000201d00700428000240d644241d04d0305642c0e6540c1402044060b0004050b0800e00c040d0b1010801825081c0d660410220307070240700800b1103c03004006030344801c0303c0e6801039008440414 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 734472517 1250 734471267 734471291
    0xe07121d0601050f010c02030703030c051509030c010b011b03050702150c0a060c0206070509040c02070b030c07020a08010903050912030c01090b091605030d201b2b0b19 74
    0x500385059070f10503210241360846080054800d0004c141009401d42c0c810041007002c28416800c041c03d1501c680160344840c02d04441c1507508500a0364012459040001c140303035030304401d01ca52000d0351030031300700018044c02e18161840200c044201c0035040c045e00288140c115030340c50101c00781c0d50040901094680c10740c40c00c1a030703494244d54801c442c4140f91a4001280d18000103903d81701d03d09960340c1d20b19008205041c030014201c1032107543e042d40b246010215000500c0e00180d880f0b0120520019103c0d0760030300400ca000100ca5002d034400c0e91404807240007103035001c000c0b5524100107541501100d030a404000f0318500c00c1f8074038441036500c2c1c03100b02c0d0104440003810394090607268003110f00e41c940c0c06003103911350400ea1240c5a4554003050342d9100c002d001d006082071000c0c0705801c0780860b2125201c803a00f4601d0703144011030000d0102901313540c5850306500e08015a84214104d01e044d604414411640304107070600903003105030480014140003c4d0482c1007034040c2d030008041c4503505081c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 734473767 1250 734472517 734472523
    0xf04050a090b01080f04020607031b05070b0309010f060e041b0803030411040b011d09070c021503070f0c0f0b0c04120609030905101d06040f08070e010504060e07121d 73
    0xb1032400e001500440c041480320b58500e40d0b0600540d0000c0a00e49092180d03501a06c0402888018500c2c590403840107001082d82840a4002090044102542c030b190101c045401c440e80503a410100ca40307000014442001ca1000d4243e10507480110403801d20340e203007218028480243e00c9101d50380310010408c010488c00052958660006a90070f01850003a5001581e808420700503690701d01344614450440313890881f0040390056924144040411000d40101c0c101c0c1d00001e50075000f40c0400002d120b0034a5005e40c03030802920b0303d40b4142000b04416a43c9055540d8807003009890445007a010401079298402101c0003028050307514035240c41d0600d41300002e46061001500810301c100d0002916050820040342e01550302d9407040760500d500c450110340c840e003904005400c0030050001042c03980c5400c0114020341010001804444d18008140d81a9501600501e0090b82405810040701501610050b08558581072034240000d002000c2d00081c80da0204841c0799413190041c6030564203002c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 734475017 1250 734473767 734473781
    0x2604150e0f010b010e061207030f061d040b0f010614130f060c03080f1003060e0304050607150e0d120506040e1c02150108030708031801050403030b03100c080c0f04050a09 75
    0x280ca84036481174650302004030b107000e204120070b0358034150070009150034480c3c2d00040c001041e04900080582d02c511803082c40c004200202d55907c0100e1060005111189a9442c0e0103d0b002180c04929030404100800141c050710040c24006004a050300b003241480a4400291240707011038441140d072201c000f4528110301c142030300810f400102186a04501c1400c1503c9600e5440c80294500d1079561464010b00b20001c0c080c48500092002140940c0c8040007810850301500400e030750b4a10f858118800c58505100644c91a4040380402120715084a16400791400288001419a880c880400e02a2061001d0003605000b0310b0a50745440c82c0c0203803840c3c8042e0340e541c219400700c001d42648811051082c000d58019034002c1c020603001950300402507a000300030300304060881c0700301c803151070954005440480200e6200c841c00c80319800d00308894204807086032000d0200104100b405000d88102510342510b618000541000c1064080201c0c0c0007001c0203405c283d00540d0324000744c4020f002c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 734476267 1250 734475017 734475019
    0x41d010608070e210a0204050f010f060206040f080a02010912120c08010b070b042a05131a0405070c150e0c100e010c141c2604150e0f010b 61
    0x150010518443c0b14030044004164060705415508201c160320704480071002c484480d4074410192903800503240d0f8020705000d52082c031401190b0b5410070341103115081a507048201158001c2023000003080c1012200740880c0d41150301c255650715004002c0b8098101030340c0141c0248840100c0b0702e007169000750714810b042c100140420292000020807181000d0a01c00c04050b0002440250f0101d003105400e550841d20560606041a072481c4505010154050b0310801280ca652010040ca0401901615440e026220104040340c12611801c2c40c8842034125070340201d27a107000103441e84e070140340c03c41c2c40317180c0101e03003011084a28610b51b1f0103000c081c0454145400b5441c0605490b0504034018072600b14152501580503001400440e04148100c03000d40388030740600d0245844001c04d008008201f00c44035454130801c003080030080c001c03518082c14141141c080c49180351a9a04032001c007504150b00500e130801e0900e403140a00094482c09507a0030f81d50044100600210005604c001c0d907a00c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 734477517 1250 734476267 734476277
    0x31305061f0902031012062f162d02040b030703030804110609180402030c150a0302030c121006020c0d0b0a2c010603020910080a1205041d0106 63
    0x524481012950070a00d10601c0c600810700d072041c03080c4440743e0051984500c1c01c1004405440e075a900c042502d104285050358015070341d0815039210141d018101680c1d28034400e070500c040600401d0401c0503c1450300c5682c80148403a00d010407c540c0300c0d140550000d00d05040c07502240710000320a800344001d00220f12561a00aa51a0908020803588108c80e05034955018540d500d44501030743c1d100c0171180b00e5210f00b0410042696603140c0318030303600001a0482881c0d40e45050310500d8076000708601490f201d5500001451080861502110b0030001c0300d1a02507283e80b5203021164241c001c801b5210010820714040009100210500d001290441e5080342d44142d280010301404080c0c5450152212810301e000400720f44980c0c20005d2140305d0520101e40c10015042c807812031200004040180780d44070b00d0704009510f440c101098100010500b40e00046180c44e039199501d041c051401007217901080d070a051418001d0090390000c02181c0c82c0351203c40550313002c100e9041002d00031000411 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 734478767 1250 734477517 734477521
    0x1202030c0c280816080f0a0e2b110406030602030714070308062214070e0103020906031f03060204031a0901090c1403030408010f0902101805090604020705010203130506 74
    0x15906241c42602c030300c10300c00c8400c4410030640b180c09039a80034895414007403c50345918800140324200412011800344409511a00003070002004c201060710f12038803d14402c070311101941c9031109444008545112482c0c01c8803124074059007086002d81046a01900d040e03c000180501d81e002103214160b035a490704100742eaa401400e2950161480c09000a403409000410318100900e1414000e032401c00d003000d1524004170000103071501001803e000603031345014014560303005649400200070900b025801d0800540101c3c0981c003006103e0030900c1d03000100c03050304039504040780e00a540c000c0d10956031181c50741040400034551010260301620030f480056000c0006201d0226100e5000011049181c50400c520020300c0c2c2e50604d86515010802c03000880303110902c1005040c81c16180d0204002001d801041f0140380000003036010700c5100d00c5032002c0700e01c484030250306440c42101d401d0301c140c030350201190083c00344a4000304a07600c000103000118025110b01000c141c401c000b120b130a9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 734480017 1250 734478767 734478793
    0x1150905090c090d0f0204050915100806160c050a0503040305070e061e031624032f070b09010f0b030c03030d02030618010e07020706090605191202030c0c 68
    0x14840454450030054000d0107119a146460b901c04d450721070164a03200f000c50700f00d40014080300c00a480c40c042560119482065203031540751681d40c0090a203c0c00a4000c1c6050182d0f03841d52070080020402d118544525141c05000307802040c400c980003001c543c801703007561500aa503035200e4007003502c0303d22030860000358410900008520403000a442082003009421034a00d0003914200319036814010242d0130710115254202d40c074000c2c0030140306800745d004070004400c2c0c0307005840146000c15003040c0007802003958145140c14850110a120501448650200c110301d01800d140140644001020b0014075a01504090b4402005c94000c11031110382c4d1040580d15079142c0d9040e505130f002440302c08016485a800356a102c180940701c424805103602c49100e002c01d00740c024900d002920400d101d40c5650400105010700141d0600200e56810300030f0252503070080d007000305000c44241e0744601060788244080c00e407840b2441ca0a644a003400f8140901d207800031040c02d0030b188079250002c001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 734481267 1250 734480017 734480029
    0x1a0a08010909080f07020a09182904030f02030d02040b09011b02030712020d0f0303090b0702030405010206130311010c120b011403180703080f0904181203021b01020301150905 77
    0xc540c0404250304e0040001000c80064000c0711003a40c0c800014070b4002400c20f83c82c084e03134880300c00641c440f003100440c42c9047c016031407000802010382900207092440c0455605079442d00503401d0300303258280b04007039034089107144541c010945099002040009071400514090040c02c80700b40c0f21303402d00e90310003d42c89100800701c1401030b605074802082000f4a8600c078541c4a51540007034044081101242c6a172484d00300e100300202d00203959502c0403801c1c49144600c16410031301e04d01c0030318989483c0c000001d58840d805040c081c484c041d21201c2c1e80402d4002d000718200b8040c0300b0000c0c001002451800342c100c81000043c1400e4504000403003044e98031440e1101e5819104050081c00c549400500e5000703c0109240c3c0020f51041d00d00c0407010907202c0c40984610b45440f0326460f50385006030b00307000959a1690703003040008004003076280041d014000c01520f00701c8500d00180c03100404044544c40701d1040a4880c1c3c15480040003091444000e503e22030f001f600e940ba170038010b42c1d6031003e20603 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 734482517 1250 734481267 734481281
    0x703051f0b0306100b03060301020904060e060102010b010903050d0e010c020d0b0f01050301090b0f070509060708031e0411040c0203040f0e04020306090d080103030309080405060d150f050112151a0a080109 90
    0x104d03001c1044051054001c46409160040301c050001403c050b0075901047c1100c006810007540d1a0b203c800700040da42e42402003028070341080c41e101107090302d503a41c2ea59131081d040103080c060061000010500d83d1150a02e01c0c12207030014140000842c0c5410805450081941d15418410001e00082400d00701400707000d1031142d01071840d000f075582e00480c0b00100040a010700c0100a41001281001c1d0307511000380103440c1c000c02c1159524240451840e030380140d0341890000c04908241004007180860142c200c910000b6100400d0f1001e460204074194070880e009108030609046001c507222454004c40c40c800d82c0f00b0340c1100c42c180c07149816195508030764001840020381420050000034825000f1910b41d130300c20305c46542001d4171200003030310b2500720049444003560f5aa4040701101c2e8807112080042ca441154110840e05010000781014554001126502d888918110051030720543c01801070015203888003000380c10b11440c0c05079a0103481c0b09000543c05a0000c98a004144100f0b8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 734483767 1250 734482517 734482531
    0xb040b07110a0f0f020d051b0103060b040303031503080c0a140a210c0b0c03041a01180e0316060b012709051e190f0b210703051f0b0306 60
    0x18003070001e903a541d2060070391494200e0300725104a1340c2e03100503150a29014681c3d4402d90151910b004511828040740d2031070032041e03040605105003002110344000c119002e882d01454041020b001c441c40900800100d40d1000304001000a040030010b400421540d1001c3c0c0300700c8000ca05845660000d82c1d81ea10b519102400800350364a00c44602d85000210380c5415080b4100003154006130786616002c01c00480706e611505100200300020800380c68012284021000342d003904079414161442d54a02130600ca10803016682c0c003901c11803000802c141e4184102e650345096521a20f45020f102600c0015102030201d00702101c9101840c858404103401800034400e070180c001e190600c6140074203805000c403198994200d5152902089101c615403003012160407602c3c1c404540c4210300e0840e8680186460103a01c1d11181031255511401040700701c920b03e4080d4907805080e00c84441c00c03c04503a200070310301e1040190705201d1801320f03903007807002d1245030380c0400c001c6a541c402d05444040440d410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 734485017 1250 734483767 734483773
    0x40605091c152a051c020d09020f010305091510050402030108070f1d04021c0209070206100602010c020a080705011407110601060e030c31050901060906180917070b040b0711 76
    0xd42c0354030500113007485c40e603a074402c010041003103900a0f04907440020f5490074944c55280081c00d41c2020307100500045400e2030204214940140c1140d11481c0c80003004294848200214040303e07440c112920180a009004640d0381d65500015552000039200e200750014107800c1c0098015074005940e12405000c030302d400250b0381d65908000710402e240b10700990301d21001c1ea041d00941c40d1055070384d1145402b5001071245040002e84502240c60b207034408011a030604564040069010895001da00c0d4045800d42d00e420301c40c82c1c81c0d8007522070304010b10b0f03180b9080010000a9948122400a080e800c0416100140d803036a40868070440c482d007075150558820781482c51a0b05001a0415080078515129a001c082d030102c42c402e0b0008604d044110f40d0303101c1041c0005540e00b882444010b0107280e07410881d1514002d110f01100500c41246595199942e03850000d00c01d4000c1d2880d41021980c1480d55603d00758500b044000109803401d4440856000001e1900d03070080f505003045072031003401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 734486267 1250 734485017 734485091
    0x3010f090c0b0306130f0207111f050c0f15150a0e070c1401060602010902030f0616140904090c1d04170c0705090a020a140f040605091c15 61
    0x100240e82e07800130342000d4100320100d5110020941c507120b8440c643d000d0040160362940f86081050f107079aa540c1646128405886400c03601a407070451b0042c42461900303202c0e866201e05100d260401e410f120381c0030340700d01030040e07401d0000400c40f140f544030795020480b0b5000341c1c40078000e214120740701c2d0080c00c50403080a400b1622030740c00781c2e060707194007031158200740e010320000800a07007507420f03641c440b10140c1c1d100c8459004500e014412480207a41e0070b0002c0403d442d103c441c1001245500d00401d06100e4103c901c5860351032020200c2d51301c00c0c40640305001c4102940f42610658203617100380c1e40300308928101403ca5116030707107103e800303590070031000c01c80450155900c041503031219400d90400c2c07017114400501900c4500d491807060101140040c0c80c1c03c94240e001c1c000a5214070007422910b410025110020304501c1030b0342c180d9000d8617101d52075030f15070404108050700613640040c40d080017038440c000700104100c914040860b0200c06112004170600381d0344080440311030524070103003a600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 734487517 1250 734486267 734486279
    0x9070c12140a140c01090b1b07020904020405072a0605010e090a02060a0c06060915080304180f09140714150d0c0c08070c150503240a050604060201060503010f090c 72
    0x400041c09541110418641302d4581040f60849441580c1103441c50080400c00a86400d05100802c0700e403004000c1038a405165800250f6031074000780000e100315a50408120304d00d210b030a42070440d41048a00b210140203c43d0382c440d20303060b11041141c841d81008000300e201c11104080b14011075040c001050880015403c01030250480700900c07042242d10541400410850301948000b440301c5c075000903004800c08111201e403006900700954550003007008100300300300981c0a0902c2903083c0c20004807198210076250207403264030b401505d0310300b400300301c944402400f0418004a0b96400742d8036040f45100802d108514010754120610030384148000c46000009810000c0001e9061806008050300d641d0341c1c0400d504030100540d8919100c040521440c2ca44030890140c0d103c050500900314a002c5010403031015956407494420440544000c82603152001510301820006201946a41e00ca0200070f000701310503c9614465801c01360b03000403040c600e22543ca03c440c0c1094004444a00f003403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 734488767 1250 734487517 734487527
    0x70b041a1822020418151d0c0f03040b070f1103040b0318030304050f0d0c0c1502210a02160806222306061504050d1109070c12140a 58
    0x403403400c40d02a03000e0301036004080b06200500207001030030610740c42d0f00d0858010000300c40b1010200503035082190300034011290b81c5043d26004c000104001c401030b6803881912013942c026046580f04504002c01032004000c60021158480e44c46541e0b1451440f6240c10116030721000201040c9890700304000038041640c904000b1507019283c60007181c074080e006464945542d1003100c0070344007a0025404e554501c0b0b414012084041d81703600e8150036a00641e1200f142014040c81800d200c001c00b1909084010b000f0310486019000505540c0c42d10390425549440541c040c82c441c40c0140207040094900c0300c2881c0707006003941c0707540b0000c2c8456500d285d400480e00758207103450b00030b4103030260400c0b0006008801003030b05801030070b824000c1d00a416040c940f0300f51000d40b040f48500001d90101010f43d980c4c80668046510840d542f04092040d401c00010740300c004007040e03410802c0e120400c056580c0110a42c081c251103800f1160f03170803000d164101c81030001e007484c5115101c420083d05950318822 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 734490017 1250 734488767 734488789
    0x106080a090c080703030c0b0901020c1207060f0603030503090d02010e0309091b040315141504110708030f07113412060e06070f090b0a09030203070b041a18 69
    0xd00350b40881c07945442c511807900d08268000c41c002600780c0c1c03082041042c0006441c0e04210b0300e00003903081561403070700300303888035190301c3c41d92028000801e481003031080750f8200c42c1d680c0d880c6800c200502d03070716410010915070045508a2403031050012400005105104016080b441080514200310f8140300f0007141da0750280c401700300ba085e81c54403c01c000c1c1c0341e4001080118850b00740c159080600400010030342d88901840311401d10858100400c481c10881c0309030030240200c41c000360340c0f4458040b02d0030a010f40c920140603244003004100007200f014118a000352515141d50000c403003001126640da40e00c01a40c03228101128143c0000c10b101004103d007030034140d9032140c908984501e00650005c0c4003490548240b600c0700668074400c1828000d00d41c000c40c2d81e1034600e41003002c1030b8014051100342d00c034540c0700c42c9001a100b41c10034420b11410b00134503402001e540c4103a690b0701c50050300741c115014500107000c40340e0042007d030f01950201c1c2c0340304004488200510880320204202c003524 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 734491267 1250 734490017 734490023
    0x7080f0c07150f0801030203030306131d030d1121090a080d090c0e060a1a0c120c0c0604030b040f170c010e0708060915180304060e010e090106080a09 66
    0x1844040310411090020394064401c241502001c0c00d61600001d02d03403403070700000c030003409540320051000d0b0b01d0200450340d00000030740b851108110003540c120000d05106440c002050110308100200703043c04401804900b40000b81400b0820b07100491011511400d00c0c00300ea0101c0000120405001041030b4035405000c250036070b0f2007008030f512819466400f50300c8080010380d41c3e40d00401000100300e00000640204801a0014680b24004c0b501088442c0109443c00761410300c3d515101c4000c00031148011694011f1b81c1119250905144075500551098a400c1c00f8405c0d042e40103040410543d01181d400c113403144813944590b1518031400390310b01c0040d02e10150301016078a0041014008283c810940000080c00380b29048581e410899a900094940c3d0010000d000b1403900000c0c0710516014116459581d9853304040c91140c0030f089c422046581c01f0204001450f80d4101c807c19a5400c002e1301c4424a09a0641c1005002c5d0002d010b12400701e10408e000c1002d214131584182e0f50244 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 734492517 1250 734491267 734491297
    0xc0f01020322030539011e0f090f0f051207050319170c030603070e0606030a180c080c041b1e0905060d0b041103010303170a14070f020c01050f0708 65
    0x3c1404800c100301681030340d0040035811899220f17440800c4140801c018090348020040c80f2085851804030076407403c4450b440c2c5444158018500030341da48039078940c41c1c1c4a1690881c8054900e406601c0d03110300c000548042c065411500340b006000e8080b42c41459110b13019501e001d024030300498181d1030400c00340301000014070f078082c402d884040145001c0c2c0c9410611a46070714100c4c0c100b6141103082d0304440b502211400038049552100c0099980002d01d0345000310b011407030340204009810309004040d100c0d103810500092540808101c26142c20000e031018410080c003155414a80d00864420b0800115005d400060900f02000168000800e5250403480642e85500051113a0094800603903503030f550b40325a8002d454188580311128002100c1c0c2411985585c6000d0003000300300c1c12010010008400140c454119640051800c11356004803500740e00384a90010508104000351a0161180130201714a560148043e0b03064032490b0030545182c00c0c110750b070f4480b05410100d00d41910310 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 734493767 1250 734492517 734492527
    0x10303030f0204080607020c03060a02120a020f12040609020301050106050702030a1211030f0d0f0908040e0705130e18030414040207110604120308010e0705030109021305030706050c0f010203220305 87
    0x100c0c1c144441c50081b80b03035034020507003940000c00305400c007a400b03448502444e2040105060340200c480e20a50b00c9181042c0040c1c40350100c1007240302c50b105206010740c90a9446d4204070400031281d001010490083d0300810a0380c1e06d0f002c00b43d900e84507030701c0c3c06541035201011010004500581200308242541341c410081d001c01e840f86403a5401221600c40e4200c00850740c40c668101e94800e0302c0d081072914a0030710842e071541e00d0349001449140111091031758405d00160000d40034000700c41c1101d0940c0304008442d941c801208150300000d80d082641408810b80401110f000007054509480b0f006010035079418410081000940c4105070889409141205408080ea2401c024100419050030202c0c0111030720328000b0845001600800041170004041c01140c503803007800e40b070542e1004000181e1310003580c5040700b22080c850340019858402c0040200b07205070700101030240d0503403480440b140503183d046006c4c03d0b400201c0e0160f408407403a16a004600100d400a00c07040d84c0a810014980 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 734495017 1250 734493767 734493779
    0x90f0d08130317180c03193504030515061f09030803040c0806010f0b030c0304080c121b010203040210140c060a15060c05250e130c0f0e010303030f0204 67
    0x401d008441e0313140703005804207401161500c207001001c58024220090308141c81d00f280c0d0700014590090010b417008400080c00b0100c401100300180c0b00c03c3d0120351440120381030a0114225601c140000c4070103000d01085912041c034a406403900504004110200705050b00303030046030003200c102c41e460402441c1c04000000c100c0301002180514010080c503450300c1d0030b0005d601d01d424410b90240400e00550032080140d0a001c00949401508071100165243c4490403c10114000d640701c01005000345130700890341e2280c40307005048000d0107090030002004040d04c050700300d000031140a5001811440f0a40c151481002d0321070480c10a8143c9030f0070080020149403520004586003800540d80383d2801a01000183c41e1000034007052409130802449581d0700c4e906d403090454800810044281106121601c0000b040050940701c5400c080f14600060160a2040b41a005a03032410f4001c00c08100c103109204901c003522044410030f92184d1850364114000d00c0c5d038142101d512942072002050f2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 734496267 1250 734495017 734495057
    0x20d08030726090d05130902130801140405010510050d2a08010506190617220c0e090d0f080a022704050c1305011803020303030f090f0d081303 63
    0x20950302c281e0001c02c146042c824403440c280300101044c00f400014003456910504450f603404c25a0303d84540543c40b0180740c1151142908190043ca42550030851200002164108402d21840c01f42000f4456919146400c044101c070034095213030842b51b001a10008100c18100c030070401e05030750f400e1000480104010840c0105950001c280740d94484042c815103207858000d800842c004046031701005031410340c000d844901101c24081082722600c0004901d891030031282c84070781c501800340c08410401031402440c4081603000321440c603800100440e82903a00001c040700d25100c44e03158401030682c0c254050340c406400038808550541c081006804103185d6043c2c00c04135510a800d00e940d100317004010001074640c02130030500a00c0c0d00340a40074240c02c5100c2c950080390800e00b0180014410390000b91400c42880c0c00c0a0b40600c000810310070110700103c2083c0c4980e240c0016102c0343c0881d50600f944801804420302c002072004404500000b00003034019214900c40d00b401c014020f403c0703413100e00c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 734497517 1250 734496267 734496317
    0x100f0c1703090706090801050c0d2c010f0f0c14031f090c0806010c26040b0a05090310020c03040504020315031e071d01060c03021501090209120a020d080307 69
    0x1d42c940100c8401c100854016130058082c0450707000030700440c6084800318240e0700900341c9070501709444120141d010006055402e200e188841d82c8c04064041c0c0160345400381202c511072680091412110561a1520344903000d04404540d4544941c2c4c210650b000300c0942000e8058500f880d0303a035030b94803555006860a0801001250000f0800070580307000034080c440002c01c13040c14031039651074030000110040302d081014803510641c058841c0352000200080d001d81c1c0c00294418400107403140c0c45581060103014280c50440880c1d011608150220041c0c2c000c0905489542e0b0041c40144120719241e0007456001a107180910101e0359000700007842d090500764110b6100c100034840452000c0300303220324000b800c410401e45c2c1c440b186400d074000f0400306c140f24003c01c2007400910402003510034041042403086440c03203801c0d1961134940680c000c1d8802c950703c921503000320310010240f81c1c021034501d44454000300086924103164880b49190340c401060300c4104038110002c02c885040c601c412139 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 734498767 1250 734497517 734497531
    0x18091b0a09020a0801091d06221a0f060307080c040c03090210120b0307030b0619080d090501020106060915181e030b06030601081f110a1805100f0c1703 67
    0x10503175454030200358100d4400b0f075200a6a84003400c10b000c00c501c40012229081140800c0000625004803481c0000d1841d042009029030f4916400340842c7ca84910054000c01c030400c1684242d0b00c07030004240e03407840148540c011540000803c486149015030191140c0c200908010601030032640c00296000f10301e07003140000c106440c10070074540e803840c816001340c2c103400c0c0c0c02003078014110f403550102d1440003022a1700c038a0b0040d2601c0c0844140703009880062142604880c0c3e404150385010300000c0542c094103005620788030000810600ca05424001c69036000000c2c0100c1d002d2a0742201d41c041e40f0222620195040140022109600c40c642c12200c841381d01e071003803401d055203080030030003030042c000b00c2c440e502420040c41000c1000c900c0c090080040e5280240c00c481d209070081c06070054050005001001080106150307400c010540509000b1036a11003070940c44e80104100d200c8010040343c001072619512100184c01352074130031440c5000e074013424406441c041c00c1d40320741d42c02140e100f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 734500017 1250 734498767 734498777
    0x6130e07020705041109040b0a03080f1902070e13230a14010c050a180506030a1d07030314130b0a02030a09060918021b010f0b18091b0a09020a 63
    0x240c0560305100300c20291108441c00e008005141d00880e501e801243c00031445580c2c0c03149240307141d59a04c0350940086501080303136074950210408886050300800d980340e0030004500e8a01110300e10101c1c00c0401d484141022074400e03126500c4401c01c078803003541c0450351491544c15440f0703014400c00381e91172280703003100c020040c40c40b00389844854599071090203121170b0b040c1450200220740210603905851460701d05016141941c0c80d01d0240800306512840d002900001408001680ea400c0080da0340b81c0d0707640c2c01d1040f40d00b046d491030341c031003941c440138001506411602c842d220031032006001c2c030b0081c440b1020b110703a1540280413080c0d000411040159200041280140c1d41025880c0010040c508082031401d20340300088410b1250803414041079039000440c00c42c5002034031008801d5403545030007080850900d40b54980242803003c1403920035607512180e60002c19140c0c0a040c411203002002e49640c3c0d84111010624000d803705031580040d180c14089131101191020f1714190b01e41d0344d19 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 734501267 1250 734500017 734500021
    0x10b030f0f10022107021c030903080121140c04060f0501110d0801060c06060b0a0c0b0a1112070c02030307030c110a050d030f02012007020301050f090a0b040206130e 73
    0xc0c281c0341040350904102ca080c0140079100207028900394107162500b289503500d03016035444400b28142484802018852100c0c0320b00702d031090342d155200400244c0b00b51544403007643c8505551040481c045088001030074802c02c9400000d4110150480d4020751204441440300b6547c0000e0684006400500500c511410104815a4020301c030540c461109806424901c0d0311680061055105010b0300c41805241c400e50333800c0200560000c0014641d201010b900c8000c041001440d120120600b40d90220000300030502c04159442032480300c0d504e118000b03103060494070140c0d8441c100280b2440501051440c80700160300c0500c01400310611a40e074000c4545000d151080800034441c58241c09425204014003031030316580781100e451038050810750714001c0046002c03030140054444015102e11030898500340c10095101800304184214000c0c042c0b9038907203940810990085518070501d912040ca8030001c10b070104c210541050010740401c0c40e2040c00c98007034801e1780342ca6100c4c0c1251810801 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 734502517 1250 734501267 734501293
    0x40f0903050c150609010b0f0717280c0b0901062103030c08131b0f080c01020f01151214030a0807020d0806010f1b020d0c050a1403030d020c010b030f 66
    0xf41d154451a204110141495008144625014007806554010000b00b540e1903d50600a03071303504507803013804c09140e59040182360600b600602d02041e511286804105500303008180e40c41c00e00c400c5503071500e80129a03030726490400100070b0700b5640d19540c0e5041c08507034034101c0d99866a80621500340c40d40d0100503071030020102e4482042d100e04001c520030901020401c0a0619028a5000340081241c101c400314000350f000390707950115100c112141c2e00003844880220300714001038004d0b000d85441d80c141d2140c040c241c81d44000d42c10551b1600960a1190222101c0340703400481c01410031044012604071014a50f910060621000c5200b03c0e0410041560400521a080c4104c0c9801a0380b41071545c00a000601c480c0445803d000c1c0009003008400030492065030310a400801184010703425080043d50318441b40101d6008030911034012036101d8007291080c0070000c0c040c009601c0d0a02d6904664001d4205c1700c1408510354a0315a5110b4580e0100100f086242c40c002c00b420900803001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 734503767 1250 734502517 734502523
    0x4030f1e020606010e01051218010f02130306020a02030c011817073801030f0b0601110304060c0c1e0503250311150309010203091009020f040b040f0903050c 69
    0x2403484411140034240555815034082403440d00184207080c502116501d40300140ca05019044511b40c07a4018502040564604540480308036220603008100000d24a0325000591145600c01c6912901c800c0342040024800e50007490741c40b80d603105480c100a503907413140b0300355000c400c0040300c1009440680b400340400d6224140a4032000c0c5400c80ca400159a80e45803807070404400701c1208100c003541e1f58800c943c43c084180f850407100d2005811583c403440d120000c2d00c15288240c03040c814140015030310394040d40540c40040204001181840d14144013244d0300c1144040440710352803140740c006090034006400310920780301a20b170203d41904040c180341c604000350744d0309880b03001048211452010446024030640360444104841000ca40002c252904200a21580803490000c01c202d10054194060341c0100c8400b000e48091007448411041610303400500a980820303500000b0b83e403450b280e404044600e42c041c1000c20600f64060f180c50880e40c062101381c0103c1c000061a9000000c14 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 734505017 1250 734503767 734503787
    0x80105040c061d010c05100606020f070f0f0314031c1e0213090509030903120406030501081c03051f14090604021303080708220501080f0106050a030207110904030f 72
    0x142c41c01e0960383d1892455603018241d035800e45814020070100750703001c0c0b08080c00f070381ca6000400c000601010345d48884c029600c0004608070b24480c015564040b078a150404003074012a000c40180c41031650460b20b8080f82c2c4481050550b01c41c0c481040701800781d8041c0145680d0003070300e102c4001041c00c2c110325088508040c40e800d04c4c03400e83c810048000d212800e05150303c1602d03c0c003403000406665944195185204030135046030700d031003103d0007811400b0490300200191a10b6a8041c4080c5e6030b682482c5036511025110400000410b85229200c14429804298001e1224207418400c41c0101c40c01a4094030542003140141c2e850070035100c050034500300325074101301e090314114580442c2204400c840d2810b4040240003040024400f81400f00c0c001c140c902100c540c1c11420f0801c0c0b0130922000e515506441980d000c110200d000801d1032003100100c504840054407518542416420120000c0d8010042229040803882107510702d52544000a88581d00c40d88078107051904410f0701410038101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 734506267 1250 734505017 734505029
    0xc09051806150a0e130209100302090d0327030605093702011206080a02010f05070b0f1b0c0709060803040b09040c1b0b0124021506030a0b01080105040c 67
    0x1000050010540b681902150510070040300c0c143c40d04600002210301200107441307980d00c802c2d58400c162080c04298000c00a002e0100c58404010782624000ea081c0e00660680d164817050b04d40d00c0001080c0213010581c407860100500108108000d0120061109940c00507103010399140e007046007102e8108110b00d004000c6144a440c00c0c4905000305c0184130b24480850906e01036050b0300411a401084c00000c9421f00704400e000046d119400507a0350201010140c2c0050312070400c0c400308034082c000302d4803855001300b00350090b44d9403150110310348070014107801c14400b80c041c0e440d20302110f501d0283c0340a04011029041c12881c0028440c140c0d10160410b4100703400c1084100301000c1c06600301c4400c0b010540b008a03e000c00401c0941c0d0720324031000c0703c00c0641c10070a4403100f00072840d0320440c141c80501a01190f45928142e642080e080303810004405640300741110b191012002c1402540f102e0001d0444024800e203a03035540ca00602a07204180aa440320140810480301c00900c00c0604a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 734507517 1250 734506267 734506309
    0x61407090311041d0a050c0102010513031b150e0717060f0403030b130204090b15040f030803060f0301090c0602150c09090603070e010617090102072409060c0905 71
    0x20940d11581c000b0031910709250320690740e03000b4601c00600050201051800100140c0b413904816081482e02c401c0b0218155006500e05000560819500303205900b00c1034165072001d03148200d0f50303044083d1021041058a040c41e80d0020551625401d004100850805401802030f49180221032000c1c914082e02041c201e8202004111a880348956007aa03c940c1514020614510742e201085c140d100c9048100076550000801103240c481e103400c503400c04242135490004400c072a00341419907000314003800120b114482003c00104480308017964200300014410004442d104002908661380707410100d50580340e00c2e600b0442960180700c400000d2440c044048850300d030a100031081849200466413040782068041142910200a048050a103018980b0129611010003070a81c82c0c6d0a50940d0f40c12103014005284801e040c0290344402d54000000c200c0780f0155000040f900c40d804154101c0551b8424000000c91030b1401a4080f0000d95160030f039109082c0000d003d0405a0040c804106c50 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 734508767 1250 734507517 734507519
    0xb040533030a0308040c080610031101030c051b1609140a0504050a0b2203030203010503010f02120106050f0d050c12090f0a15140108070501020c01080403020c010c0f020d06140709 79
    0x24402142c1c44107596810304d03140d0380c6035070360740750458004269801c0015030b88100400c00500c1d8041c8070440d01942e000d1803000400c0f60742c480044064545500011001503001d0200000341409680c01c0c400e2080e00005840c600d041034880c4080c091130682c8401c0340c1c1901c401000e80000c143c0012942c0101d40c8074002d000500e800d8850f41d07a507030b0500100030079480c54900002d00e00c403150400000544812a08204540403038100240a501b00f8003615220754070b0030800900f500c14910071500740d20800c3c00300040a03032801105840c15080b503103110590031010480c0e2102c10f030492080c5440b030600343c4201c0e038031070030f124a4010441c04000c0c400c1034039500600120000420001d041441694020086c0010801021111001e01515040f1460344000d500010514440110720349041d6030f0207070b085614001c680c02c01100c40310700c1501d02902580102000c40c90382d5110700d45030700c0c1c0d0a0040e03460507102e40072540421800049264240d4040343d46c1c10b018640d0400400240e85c10250382e02d003052140e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 734510017 1250 734508767 734508769
    0x10090b0d030c1b090213050325140f1908070603022b11071a0901022503030b0603010b0904060902090609211903091508010b0d0b040533 60
    0x200018a502900700100c50100344441800d0300150f001519180300b09549030300100810346440052402a1031207401204c441d004069140d010070f24070103042d1000420040d04d054034403158414110f10280d00102c100c1e44644480d103801c2e0319540501600740d64100010303e02010705e401c2050b00c0d045801098010031001d2200d040181c2810700422240c0c0c601c0300f201c280e0440719002049c9690203200364070008107a660074072909868419920540c0840101d1546d1103044141c00c034420328100c1207030702400711042554000c4c5050102a1300c0c0c420704000400364008000140b00d90400d0740100e540c100000303403818150409010303141c001c100303040080d800d219808000844901407003c015020f00c02c1800e2000307040610300c40e02d214409400c0c064403000304640f1461200c0240710203041d00890503051000a40d80c4c500b01c0c0001c9050125034500c059a401e254501d20182d02084140780d110341c4074191f5a103541d60340d200f120701880760f10503021610010201c244403c3d42c103400c46603c8207549a02c40c0115 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 734511267 1250 734510017 734510027
    0x1e0507120b210a14060403140c01090215120603060c2a0a06021801023f030708061c0c0501050702030109140d140301030506010302150c2a030d021f1410090b0d03 71
    0x107801050012315203800d401140389e4018010428080c1d44100c5800b0511040407140d4000e2034518016600c61a440e520141850f5507110103407220098034134108240040f022107a82039400105000110349000034010120307902d04181008151503055000504070400c1c4d45030145178401c1e460a0028100f808002510a00e00980c000408100e00e04440c1009015480c0441300880c103c11415405880e0b00b000c140040401c1000c682d2a4000e0b22207000c11aa0340424000c0c06503526400b407100314103a820300004441981001c035040f6019901c0ba484540012619030700c0220b142c40507001403990340d84150b0020403c3e0990072070303943d4200c41000140041013011511070305407074064440491440305000e00000e0b03071203000c02d40d003040d0140720a240704002884500c0c4010b00800000c0c40e00540c6880304150700c07900140e4984000d80c0c030030780c0d0007558003040c88005a52540d030382400044030751848200b078800754011902503040c010704441c14840c0c0040d5100f000760400d8165250b256600c066900505 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 734512517 1250 734511267 734511287
    0x160606140f010f030e0a0204060807090612170a05090315071206031e1703010f03030816050703080a0b0d0f15020301080303070e04020d0204091e0507120b210a14060403 74
    0x4143c2c07a41045c0702910380805c80d040c40340358068410007003076607215000b0341c8580850080c2e410507800c1280000707400038800b181040c0c40b50804c40d1817180d001818858862544000000d1040c0300e81407100e00040c0c2c0d801e000e00d078a50002c040d02e407101860080743c001d1420764440703401141ea51a0003000e0002c2461014040342c1d2210784210707240745d038800c1d007080f42001088458100070200c1c00400231800c00030100d5100110392107601d03810712a407101c040c0c1850b207129040314440001e905000c9040400d12800403070303401c0380700c07071200040304404000401d100c1160b402c001c2e180d00103644082d01c108280a144048000703d01c0c0d10450542d4100085a030300c03403101921070707020403920450075401640e4035811180c00042212007159965645c0002001800b05400c1d03e0401e9009018001c0420b802802910321441481c2e661168440491200708020a5010045030b00610450b0f0101c2030000480e110f65614213800001f8076440300d8074a00101c25940e46100b10000350001010f00ac0040c0e08401880 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 734513767 1250 734512517 734512547
    0xd0f0b1e22050309090108421e0a0204080f0a030905060304081210051c12050d06080609010b120703021c062c250911160606140f01 58
    0x4040c072080d07040403840c5024500c80d096101468000006203100d00040130001c0c0441d84410b00c2e100340801c4c03c0424a01e03035404039070715100746800d44074040e5000c06105682c072107403a0340d00e4030050000008050603000101c0c2c0b601c03071260740040c0900000c8800c01405400303000c400700620810040c0d0b07400601d02c16580c03140b20701a6001201060800861340d081d03503031802d0850703000200d81c68448400c2201404030312905010300d00380107400d102114120207810741d242e040614042642d105810850707883d8401102039510b2580c5400c0803074240400d010b200d000f054040c0006c5410321128041200d0721807107400c500c0096100c0001000140c40341a408201300495900030307011350000c2e08004003d044603103500c0e041d040d01440129086003150225100d5107000070101e44507a2004c0c0c40b240d1b040b04008a9210860a5500042046001541159420710b090a030018200038400d13002d40d090002c2d152007110455200d800c10321004040d07141c0c040c0401001c82e050800940e82100203401580546480 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 734515017 1250 734513767 734513821
    0x91003060507020f2a12070e0702010f1a0109150903020d151508070b181c0f0809130612020405040203162702270d0f0b1e 54
    0x20b4036035000b03008040d450000740e41902c0c0c2c60b19000308001001804405004407081805c0520401810584d0502c280601c84100170721149041544841003d2801410001199200c8520707100030742007402003501c0258000c600d030100c90543c1c400507041d1140c61b040305c4d0340b40400c095611221640700340c481044a40544007049a8107035401e240030301703d000501c09108a0700748515402c40c100400c15030003c9443c4030003038a0b541034075104621414441c0c11341c00c41c254a02c02e400001c0c0d0340b038404401c070f00d41d040e5450314149803089030361030740500d00e0010380580704080080b071140104c2c105a0449414000982800c103c0b0364140203500e9404001158040d000b542c2da400020115102040722001c9020404801c5880a586422510040d840c8050402820440c0c1c11880a20610350083c2ca10320300003d04980e441110158a607422201e800040540c0034030540383d40300106140b203008400450184601c24054035248600b0301c006e9013020b0b034410004240104002d80c1d0714506ca61203e100c8071002c10 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 734516267 1250 734515017 734515021
    0x100903080f1605030a11161809140d0f0806010c06022109030d230615040b031305010e0a111203070206030901061e0806010306181515050910030605 65
    0x210700032400b030840700c0c1e40c080b100c01e40b07041e040c410008090190102103035030b24800e14100c2d81e100794403140040d91a10f50f1203007001051102c13000c190600e49003926502c17000240720615440f00803088e800014950020707040b600340c440701d44c0d52000c2508a02d418a0500d15883d0500780002080b01c000c101014144030790218410158001d004d0703210b0150318049820154906201c582c0a8903988128150b6401900c0c24022103802da03141101040c462406114501c07180e0788807414018242c035010603000d140c04041201180c00c0088201460040c1d40d900c40900c2e00e0071b13403071801c1c3c1d08503182501a04003d40c8542c07440710000361308010a020403101a5100040602e00071112860760085420095002c0004010440c01c40015844030301160001d4047c5180040c04000301d01c4203c803140110b4805412043c01403001c43c003160094440c1d540c15080c0c1122545040d251441c540540401c40101e0307989580102d4101d030305400c0c418010704801c031040322141c14480400c1d0404886480020710240c0c40e440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 734517517 1250 734516267 734516287
    0x201180b090f03071a04140a03030b190e0403032f070303110c0c06250623010308090f0109081e06011a12090a02060403060606030c050c0318120d08060f10090308 71
    0x4000e0300d00c07c0000112100c0720703800c0c5005400f51211500316401080e61082002124049802c20300842e01c40b446407207c0e42d15940c9007100078020220800e403061b0208189441710070440c11140140c8005503003080d0300c030081d91034000d050b0380001811507043e810a202515001c48042070b04100781c1d100722201a40c92780510701d4101c0c907805100c00e1102e200ea083d803800c000d100c200d030802c03002058856032004440310540b079a5a103041c402e000180c0284400d00c010720003410048500041d0303030014107114010958075039a103468a000c81d0102c860b00703945204806100041081280d01510386000300565866040d814008940a001030b40e400724031204000c508004018003851650320703006407049583c3ca840e81000005040544118030000b440d0040745444648680305556114030702601652600341e120150706100700c202071446a10000009030514461000c0190101c2c1240913100c4014910301942001031744d01c0b01e0161300d4000e8042c0d484c0ba8603c140d000c0b00030404d81e584800050344034000c01c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 734518767 1250 734517517 734517533
    0x10e090f0406200c100e0a0308100f030f0507140112050417040609140a180506040f05070c0b0903070b0121020307030807021e0906040c0201180b090f03071a04 70
    0x6031100319005606042d20110b021071400030841301002100320b40005422407045000ca802c0840e0781c0c1426040795030341c800080d01c20320a4641100342c202d04121a15201c0d014880094640c3e40101c4810b80310a00030301c204401401020300030000c051807510340504850000e408408842c0740c00c0c020076a1080020200503101081043c2017101030300c000e80352520741c40050700ca03004a01907408084200004d10105151009031907045d607100700082c515001d0241d00400190a0180c40c8503441601d4105a4410500c203205440c81581e00381da854885001c00e003414030103180d000e0301210290f0420040701e001300b40b250755a1811a140901d440d440c00d09060300341090000ba800b0029418001c5a0780002030015041c00303405658005c8841100480d2505500c1000c0801901d516401c81c0b62080007541c20f02e49135010000c0a0f9050002094a402c0d0b605901d140c0c5903c0b050441c0d42c28011002c1c0f14011000300310907070002000748001c513d40805c80d1180c001050406440782d042410b0a0f001500700909a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 734520017 1250 734518767 734518781
    0xf07020a240216061b02060910031509020c0c010503250c061b0f030e100f06090b10121a0423071b11060903030c0609010b010e090f0406 60
    0x742601c000555030364403030951041d0000c005600610490000c101002c0e10074195100300d80c06500d841404001040c0000380c811110242664044001d005403280c0d0b48a59641c01c049090580c0c00081e945020b221a82024910750080c80e44030384180500b0000c614001070800c1881c0d4242001901e80e664200b54001004076840340c07444600e0b60414140c2c65a03001080c541c9040d100340c406205417400d4844203084040030f00d02000000307078421005083c980c002d500a407120329400c801d840c8002600b2081d030090710f9419109000707095441108014000a610402c200c0e1a01200c03600c2c05103500000c01007000b01d034185240d0009a035146103406150054000b600041009002403026400020400b1300640301103003031014038030401d800203a000340b20700c0c090390045403466400e110440c09500c49000022444000d550001410802442155000c0018200302c075600e800410303031b5140c038034012820b603107507401420f050001c17800b541401c070750398104403643c4060480141845a070313480c24010041d0001c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 734521267 1250 734520017 734520029
    0x30314091809030702150c010f0c02030a03050916030f14030403080d0f021b0604110105130308030c0d02132102060403020d0201020109080c01060f0510050316050405031c03200f07020a 81
    0x20392042000400c2c3c4000141c042c7c441c0190081155552800b410310580da504d000c1000143c004004082c2240d02990000360000f4070340c008c071514038110342c00103c40490550019103030041800001800c2047e190424989071411402a50509145540c0c01001c1e0280000b04d031200380d125140140e060146a0545552001c4550306c1d000c80891403025a440c1c400580c0c0944001d90070b0b4036100070300e5014404994000500c0c2c1c109601562540e210418940c00240c0105941d600421000041c25400d00143c450103074101102c0c4003441ca82001207103a1050071500e0f1910311010f95209016998040645040340d8056a0044840e012440100d00404880d14010100c0e500031821078020901540804240c4003280e0130f489503651100104036240c0610103c650000300e040001520321140182800b9000e102c1d410098201922080020f082450030004002c40a404c0480582070590601078480203c040d202c0076120a500020301c0d00e0700d8824048800900b0000165107021900d60840c0000100b40c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 734522517 1250 734521267 734521279
    0x30112031b0317060f03100209011b060c090807050315070c020901270b060301031b03060908090f100c06020a0905040504050703020f120a150f0c0801030314091809030702 75
    0x121a1602901c1d8105800c0f405030310064000009810781082e03415038000c1c5a000380240340c42a038060360034020398000242e060400130400400c0c12000381c44800d642850744030f001d0103d03407808072a0300200005000d90100f003440c1d00061040005481c0030901101114034034841540c40c0c0e6849105950b040301102000390885502000003a40c1810500e015010400c2c19074880030502041031004140d910007900300741d00240c01c000420014034a440542071011509200a8030903580340c0790302c011140910700c00e50740d03105c000803540c0b114a00040c041c2084d0724201d802c4001884461002421240030800003065158002000c20b0071a00501c03600d030081038001c00500c4249010303d01240c81d81e10511040780204580c1001c0100fa2030000318a1381c00c030b545280100b01e0007009407140700310300e02104104c10307045a0303515442e00d8000f8035001e414a0b280ca207890b02292f0b9455840e00501d440201e148442c140202440b0340d401c01d90b2070f21105100c100711000030710400e40b00c1100d5942584203004000350300103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 734523767 1250 734522517 734522567
    0x5060304050705040c2307020f03030a0507112e09080307290405120732070f14040e0f010509100605030303010f060c380c04050603011203 61
    0x410001640d20507200192000d000a80b0345c00c00c2500e0080c2810803943e1110960510310001000d000041c026441c0024030b00f824a03040c070000710342550300980c0820000781e40002d00c40140010410130f138203d11405e40300390031182e0800000e284582c0140b214502110380000500e00710318424811000a0912075003900e82d200e00f2464440d802944054440054907500c541501c04079208c0742d880361044d5000740162030313a298101402540741d40460300c00c032285103029051240f08409403231740300c03070603c50785200d039041c45100c00b0018900810b42e070090481c0d50800300184203c008050a1a142240c00d42d0003040302d5460000841c2000140e664039102580b81c041007201c40000081c1c40e51103490017203000c024054981040c9074503403009005003010200b100800700304440c803c00440e400140100960b480107a86080b84000ba001c0103601002495095001c00043d031444202d41d9400084010009140c40d1400d00800c20038001445400c040c210b009100e1810f02d0300442d04003481d401c0c01050078200e2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 734525017 1250 734523767 734523773
    0x70c060b1002152521140919050d030e0c04110912030403030c03211a01200705011b0b09031b01181704050a0e1f06080a02030a020405060304 62
    0x3403607643c8905280ca4800c3c00210b036205540c80c60200059403580550035090519000654601c07095050b10140d040f100401403081491503c15915800040e4141c4100381c10101203091504a080c080000356100b000d40580000e01c002521420020070340c1004551603045181c12814600c1200c50190402d0814001c0c4a000c50030000802980404451080940c10200d40c80d40e03480c055408001c010a44020661000c0384c0035900c107183c03410f09801e03000f42419801001c10305407200403010340d82c0944008004581981c000000303070900020505612480b01d10805042ea40d403e240c0302e418140080b1b44110b4400744414030500b40c1064100382a21414100141119520390120000d01d80e080002c201c05414000180a02a1001620903050f54a4030060701c541080d44c3c240900d0015006007040001a151550541e030f10060102c02c00983c01482d20000c2d01058101181b60020703101c42c035020510100350040c00603604030411300300060726550745100500003449590040c55100074048200010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 734526267 1250 734525017 734525023
    0x804120507150e012d050a092001031d100504050c03070609030213020c06191506020601050405090d090e070c021c030f0305060d02010e1302310e070c060b1002 70
    0x2010500c00800c8109581403000070b907680c914204a41d1941d1000c594109406141c100307c0c0c0011140c1400101a180b6507103190540103828905041402250b403000d8096030144101203074004420004000070400b003000544551100301d4590341a907a0354003080c24000100406403800f030300541111000ca84412001d84052144c3c40308901c15101194003800c00c0809009a545441c1444010016078807003102c444800160040c0c15190b9a5a41021401c104100f02c602c0005100b15005070911394188003c2c0004d440d4006c07d105003580c01004144c01c0d89600c2203142049490b003016803002d54171402411581102d80f0200030394008901019050b84091b074841c030f804403900c81e444a01001030310708029416604c084540c2a03100707804c4010400554002c5605004c3c099008044070759000100d4040030484c3c001c3c9290591f80540e000303070740c00c40040003429a0420341503540341000703062906d00c41d503a000100608040400c1036440a031002c01c00f16270400340c01c49000800750014800c55100082d5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 734527517 1250 734526267 734526281
    0x30b090c091008010b190608070c02091005120a020a030305030403031107060f0c0c1e0c0803040b0c1e07060302071115190c0203030702040c091a0d06080607080412050715 75
    0x3c20365180c8021000c0c9840c1920517480136072414504554021f00e000000d0303484100042c001c20501281200780700040c1d032282d00861043c60003a0903403590070f0401c000d2040844000351b840405501001140000d650ba00c82204203c907031600c2c2199480d900e0b842d086006e005072080007090140b010030800104186500a101d4441c5035800030440030b150701d1004c07204860720310806003201ca081c80c00b65201d64010715804214600076415880100c3d40d94a820b41745510a42c450524520041a80b0483c0301d0244030a04c494410140e03d00d00c5007070317000c840d139813501c54512940c02072650008490b010450381c01030144034480000c008440f004a0a800001141d110460080c2448a042403444046000d014083c261940160044d414114281e00340001005440c151205120841d0300c0001c01e10400841515040f400019060716800e0b10300c002c0702070f42d6007078100702040d030444403c0080041d0304c07103038a0340c2c09a00641c801200f5a144002660303a485a80000341103400c0300400e5580d0550b868104903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 734528767 1250 734527517 734527529
    0x160b0f1b0a2108041a1e0a0c1403041109070c050a0303050a060906060c06180b1005011d0d02012d0305150d02060d020309340e0709030b090c0910 64
    0x1419400c0459030456007840c080f1402400701d0401e699200301803181002950b4091480c10115018022100c1c0072195920b08075180811035488040d4448d00340e601c40c1801d025146580c0c0340ca0704504247d81c45111111030b9040850044c515034000880e524401c3c240d0789802130b00706083d0b800411450030024080c2904454076007843e0300300b00740012012403a02c0350600311403080c0d4400d030350b4442954561003d459a04020503241c1410f12500700891b028080243c05500c8504064445505c0c0c1800034140885081c031142d244640c808145402d51903d054002c0000d6091074024400b00c41405010a0ba40d01e10030100c0c03e10340840400c041803500f55110300c0c0120b094005004980100400b00044400d6146000750031107018031419800d00700c00d40103950803100000a0300c010000d50060301850030200c8250300000d400343c0d01c4501c0300248105200002d8603000032503410174078100c0c0004d020702e189880b008000c3c14110000078203681c802d00111400c0e24005015461600b403000450313202c010540542c0f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 734530017 1250 734528767 734528813
    0x2070615060905131104050913060b04020306010804030e04060819020a0e0c070f0c090504210f02030301060f09120c030b09030a200c03060711160b0f1b0a 68
    0x1080d0303035020b00101000c498000f050840c040c42606000e6001d4030603202c034440ba0240510002c0b40f1942ea1604051141152400da807000c1041401d0000542e00700040c0c1c20300851040051040c540d90028815030701035094104803511015020114006002603485810703036018001300104000c010021505803e8022915800020f4803030302e083c06c49002c243c8244000f290b0402c00100042c0c2d0741d14411114a001e0b8140a080079a144880345c1941c508450854a82c2140b10149402508040c0001524445840c201c58092044003001c5d41c0c80c80103015840038800c420141121036403203000c40101410148c1c1c60b0540060481c940a4a034a01500045901c000120001000c5031300000544407410115604c0c4070a440220840c3c94006840d001d10030424010202e98842e551030402c0114041c0324a03a130f03010418805805081c4c181450905100d044d1200c01c0e504010030002070080d583d1444040714115a10161400c0d4003403541c40c4050703003600c01e000304602d0106200c41a240b81c900c500b500540c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 734531267 1250 734530017 734530019
    0x60207050f04060f06080c130f031a04030210020306132a1407110a03061a09060103090201020309090a060f060504090c03061d0a060b18150702101b020402070615 71
    0x2c110036140030340074480784101c0030f0a0070042a0306c25a14542c020900d601e20600d806000302290b942640540c03c2a4000d40c0c4035a010810441e1400c40e044240d10084600346081c1010740d0001e48514050a5030302e01c00c0c1d0040301244e4580d03142c1d00502194030781000b04004010b8204008165900c40d003903001c0034200c0303000e030300018079000d2141c8000d81040421030a1401500350b0b6030300c0040a06110940e0800700d018804000100c403445a9800126034645040c0141c100d10b080004512000307000ea030400d42030059036001070360004150f50903450110750f051070031364523500300c00c0003000d03585d014420760340390030b003001980301d070404d005005847e08850305101c0c60352600c2040d070641d9000e124500d000b26642d00918100810307054260f0708030040307500c04100d41d5982c40d000e580b01c0c0c208404c001000c1c005202c03d4002881c0070001075902c116040c150b83d06041c002d1300012266804e0143c1c0205109001d010b01f49074036040c401c00c094045e40100210345940144c2000d00040920017900e000c0c0c01c001d540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 734532374 1107 734531267 734531269
    0x11511100c021b01050901091a0910120b0a0302091305160915051030110301410f0a030b04020312130603021c06060207050f 55
    0x9000305402c51a0120031143c010b20600e40034144001000b02140f16600090400211415105400752513515908032501c0c034400c0e40030003540943c454811400107900643c0248064103100801c0091100800502000c600b01b800003039405400c0c5c8000071002d040644154400c41d11683c00c0d2100c810700d490010007107203603e030082c42c0019101c1c0582e09800b151000d1010042500300c0702403070000d1070740308040d1564010710710300c03448080b1030f040e0386200000d0241c0045a82c0d40d901410009461800d90003401c0d600280a400300700401e00003846151000199008440700350351010b0304440c410860a00d41041c1042c12081d00203400c0803041200343e6070b030305905008600840d90b81450385040d00c100342c1132411a19400c06095420700c0300e03030303407150f014960700007030b40d41078200103a60384800244c4100880110001c1c40c03005003003010114070190701003003481c01c0305c0050b04c80140b0351444c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 734352517 734532374 := by
  have h0 := BRFrame.cov_init 734352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 734352517 ≤ n) (h2 : n < 734532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
