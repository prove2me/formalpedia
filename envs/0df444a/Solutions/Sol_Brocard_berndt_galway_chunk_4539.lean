-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4539
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:56:24.181645+00:00
-- url     : https://prove2.me/submissions/ba4a28fb-c98d-44ab-8966-396b6cd705e7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 816187050 ≤ n < 816366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 816188300 1250 816187050 816187063
    0x903090a031a091f02030411090a150b070218090f120a110f07050d030c050d09030b01060c02060304020130020a03110310051909020309010515030f061b070c1502 71
    0x40f10083c0458038009654185030300303c40c05030000240d0702000007814400d5140c0b50200408006004100130714104c44100c0060010a43d600c00500558401081d04c01c00d0f03404441c1000d400508a00411402400d0001001c5c0006c080803218040d40802803400708042090264541c1c05001c4640c59415501d001045009102650002030303006440000c40c10782d0224121050300c00c19a007000c0300d13060310b0505448610b031096004105210344c0c140c000e070f90369002d4031141c02d4030300c0350b20340044990faa02c8046a0380000000069444901007012030010340c0601c84001c50050f402003961307071401508042c5501480e4a1030100343c0c1d00c1d00082c0c10400c660b071510404181d801460f40f11415418072403502d104103002c030700031180180c0d0005070700f01c24580700f50282c9000f041c0d0048150f50b28541350911901801064501000c0108130f012021040d1801141030701800c14182c7c000c14a0782e442100101d065202024040401c450402030f15010403030140d000c0020304141d0619502280c48044024a0802e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 816189550 1250 816188300 816188311
    0x4090c0f0201590c0d0302030301091a04020a0f020c03010c020a12030212042006090d020411160f0c120c0e0907180c030c090b0a05030903090a031a 65
    0x2454900c00c1200300c100600304007942200586040c608518071200741c1080026036183d4902d5100343c86004541810030030341003480803824011340d004541100c09100303199040760402005a0410300040c0032107006039124030a070021982502e04c1d01100e250115089034080c40d10400002c0302413000001d01901000800303410701d0140d008210740004840300075190400088014110358030400050f07417080c441d4056850040360700000e0007483c1894500103c404e405880050389003551004404250316011041d243c04900241c0360130b000c03002603030030000100610008500308071418081042925040924800b015100760302142c0440003e0034203400408150744011035558500d030a01000070480f03c8094104d95003125049072070348403013015504040d696000785405c80040c20710717030200e00c295030040012211070fa00c0410852403a40780c00c030781d820740074086c45044980c10400c0c0a082480f5074000c50740914034000b40c9013044010300c0010302c02031456101351420070392248256440840082c0954025 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 816190800 1250 816189550 816189553
    0x1020d150b0403020f130501060206070f050315011815050706060510050708070311060c0403030e0927120f45010c1406070e0117060d02120304090c0f02 67
    0x45203881c0300074080344039900000b401000c02d954820019201d03004d10079803000b000310080c0000d41e11158000e5071240d00304d0360040021084c1e001d0015060145084a019803c05030700424042c00d440300660300d030422095140803500344501c00203900391340c00c650340200c44001c0c0c0d00d0b280d460341c09090400507034946402640c800d0070081c0c4001802900705d0304950070940d000320b090b51107003117034142920720f50340600007144a8020081040117900701600113000385c900ca5202c540040e5005000d10040d2700040311048100990751240b090380c510070303004880202e085041154111850041043c2c1c1c01d401c008030000c211200031440790302549090024002944803801044100340516500b456401d88020200e29890b201104040d003d174440e082034882590046c2d851104064200c1500d40d4841046800380300207030703000491100540c0b0800b0420109041000802c0a03070320740c2da040002094161000b20b03403210707445400050740d0b0030900c0604000d000310703000010f40400146029145529440c84202103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 816192050 1250 816190800 816190841
    0xb0c0a060e06011805130b0903040906241b150b12070f061803081303120c0201110c15030604060302150c07090b06070f1506030b10120803010e0604140901020d 70
    0x61008401c0500340350019940107c139160000344d2421071040e030300000003050030301a02203650f1800001078150741d5050244102a01c0d10301c6411669117201501c032035880b11440354060045159a14652003400c4400030004082020100090920800a26640068000950400410207946464801809282011444011b100300000000030381408014001040400d250f032480c03c180441c100507650000c04904a190841c6000d0100c0340224801c034001609002041070892021450382c802d260080c0c4191070804402082c3d000c91b1b040104101c0c0c1099442400001603942c0c090212141c070304040043e40d85140034200e00307041100c550005a12281058500410b98a8800c1110700550f0003007900100b5548500d8005910440404074042d11810311402005104054084901440101c641001ca6540d00c00c41c0c810b0300d440c4418080c201c05024401041000c1c82a0034003a40032800500000d521880d0b03403d00000500c041e964011140e5001c41d0088400a181c403a00d0702a180c1d41000ba1031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 816193300 1250 816192050 816192061
    0x37120c1811030a1a13020d0e0c030307110f09010303090e060301110a0e01140f131502031615060b030f1008060601050a030b030a050a0b0a150b0c0a060e06011805 71
    0x3920002e095005420740d20010b10192180b4030000418070b55000b411740d511091405040006500140304401400b071405c07042550780b91000076005040d9401401441c10324403030b51200c100d0800d04241807a0803000354004403000d50703a14100300d0f019500c0307510352200d03007810506621200d40b402000300e4040d03071410703200750b00d42541c50059800041441c942512110000d20040b2180b0902c490281160103010800020401800019000568035044909042c80e0f5032540c80480803005856840585c100300010343e4480801c1da518142c0714043c460510081402d182c2d85800c45545074051507002c4400700901a40e84d240c0c0c0101900110f00b01502071256007050091030f15500060701050600200080d00c3c1c02c40390180e0000943c00c0d1008041d5080e1203203900f0400e440d600e580500301e5442c0e072010002070039040c1e070344a001c0000c03404d20291182581420780c40f51969004801e241e070b01c2c0c440c140310140041c003140507000742c8085200203840c86502d40800450042440302440c502142428108031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 816194550 1250 816193300 816193331
    0x611060a14010302130b0d12020c0108040f0b130b07090f0b0901020709050a061a1e0708030703050403030212150907211107080f040e0637120c18 64
    0xb4107407501207403554015a0303805000c60060024100b05a00140f02c24452818465038944c0c2d040046226001e5544044c0c041e001150700030400c1340e005242c1c6a020903041c003c1f50709000300740c0c0e00400b84e02c2f450b030102c3c1c9940c5840160071411079134540041c6a03584180401437a04000c1c0006145011110341042800c00000c0d448555501520b40c05607652000076130103c555400002c001c00c03640ba1006030441c0501d0b50045a42e1241d02d5190040c02c112180c5034500c403640c0201ca2816402c00c084130705584031001c0440c054803004e84254100750b024803078540400200401d59001307602140f50074003c0a0030341d05000d101c00d001000c5009018128505101c03461495101024242d41d64600150a14a150705c424a5000301603018102107804103a051244600e10001d01c01c0d10000c60b0134480d16520141003002039840303102000d040424002d03a00000789079460f003d900c146016030f2580300da40c5c1c481c00c5d041c10409070b0140586139056041c2080054640ca0000c0365030150082c5800d01c5158025407250 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 816195800 1250 816194550 816194591
    0x2b1b050a1b29070f030e060f0d050c0c030d0216140109050d080610260709061107052209061a12010c02061303090801020a0503040516060f14040e010611060a 69
    0x5481c04070304d4002c0c1e0040503c21900031101c0c07a0b00400103919000e40303210790002500159802d0180310325180224801c4122407051f103034101d00240c019454500c80310507440203504140d1012a040801c03103107143c0080d11444030100c1d503810784000041c0c2c52a030360030120710703040c0f40e22282d500b8042182d00b80009a02e0b544800440741005052408001000c0d4002030308042008882800a0081200b448811988070803101d0403030300a5910810364a04000c510b989a151354490160f02801c50742280807100e816400c1d09840d8001e5071000a448500344e2503400a07500c1590045810b0b000c000b491140c0c5103001d88400300c01e00d03400300c003c210040320f00e0f00207903448402910b41ca030400400861801017512400c0c201c1c1c054140b6200964846010700d03405032042d0000d42c0c0484080c000c072401e504240c40d001003128221000d0f40e0358080d024030905030540b6100f03504800240d42a5040201058411281181038020301c666a500500d90640c10030040c140503001d050103c1c0c060a100c2001001004445c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 816197050 1250 816195800 816195803
    0x106050603131716050c0f091609180c170610121503030905031e1b121903090603020a1d030106050a1d16141305122b1b050a1b2907 58
    0x20304411182900083d41c2800365988612030b100482640cbc1401c818081d0410288480e5039100d100005411070648103044004582d1f10742c0201c64040c407160214403a6054000e0b640c840003000071807000c8010b24810001c0c080d00305902094444404010034101008080c3d001c0302c5400229000c014040211074850441c0300d2440040110704180260b2660342c20702d2151400704100c11a4507010030108000c15130303208408150040342c609040040c0582c001c1c000c82e02c41c01c0d815030b03500034210804c1c81d06001d40911b800066405650f500c40c081140d40310800004064804801c50007a1590010442c804440c0e004294a02d01c03109103041041ca25040b84000300c1e29942095815100c19031607009801c550f90f0342d40722940c820040787c141b90001700d010550b6044000c507041c01500845580e101c00000000a0101c40d0001d2141d03079104580000e00f401d80b82d078041c49141503620a50107a1500d841041c1c0304844c2141101c4084c10412070350500c0c2452454503864420720040412000b03c4032000c50040520 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 816198300 1250 816197050 816197071
    0x1f090209030712050d030c080708070c030219030815010f02070911070605071211031b0c01090507080303071704150e0703050102030a0b0f030106050603131716050c0f09 74
    0x4410140d941d0a00201001c0c00e910540325040b41c0c01c905280f555804200c60f0a0042032038555040307410b51040d0300e0706100c0c3d040ca03120600705844210048a02c1580c11006400314000d0085240c070035801109402c000d24060b83d00e142541c1002606148501ea00c060414184a0030601480e0300b5074011810b44210707031b00a040055100c0d48110440c43c2482400e500600443c40c010411007140d0300035038040804181c4010402c2040d00c410710303030b464910007038881103a054280c2821309031030185a0300520380916820000b29028209940e0585050180e801010407a04080100034959a0045015000d01c400481c205a02c0c282a2142e4021200e41c032201c9101c152108800d403070244041000c040119070042c004c40d40c0c0d00d4010820b00007080300c02c404c1c920410040c10424a6482c05018500603076000800b01c514648072032207502c113050f1580d0301c115180420940f04c2454012038101414043c400c450b15040c03889810b280480c1803910800d0f503580310b010b10f90f07070100040c0c40c1c8895041d4400315a42 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 816199550 1250 816198300 816198307
    0x1406010c12110a0807150b061e07020a1202010809073b0a05180105010b03010b090d0c030302060402040e030c0705040b0432070804030e060904110309060108061f0902 73
    0x40040720b02c59a070549049a500c10103c00300c08002e2004000c00b9800d0103440e0080303071580c1c034a01ca43c054406051929921883c00d10400910644100c20700101d03045020b40a460000e41c0d44c0030440c000c509a205070094109507070414159600044101d500c148480c0c040e2403e503041100d83c950300141141d14861f02410207807000620102c03040c11401400c00d822140c0280d14040d007400e8007401044a8000102500060311404050140201816125080d2605046a080000d0700400b5000703540d15980c0624011002c0c00482c6c051a01c11004e5402503015044d50b250500502090390b410044002640c0d0040210014445012030410150341003100c0114a02d80014001406800d115500032a003012b011400c401c10070640280001c40480c50f01c00b105c443ea41d0007801d4520140c200e078060f01180700400400010325010700140b1000d1002000007039006a840d28040780ca405c201e50310905503010030018444510100191607100c0c500007240d185020310350a619500d01018801e1400310364010 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 816200800 1250 816199550 816199583
    0x601090c0903020405090f0f03091c0303060e0f060f0a15120615020109020f0303030c07111504090c0e1009030b040c050402030c0a09140f0f031005191406010c 70
    0x20881c290055030000d2051003107080000c03070b2a484480380c120401d1310380304000e488101100040141d8505000082c42d00c10324204c030030305418030451032070340840426079501401300d6031038964165980108162200074400380380038020301a800c40da0251141c4500588002045010300e03d4492039500040307490205035101c600f64010000d44040e40210144620000c0041c50040d415880080924000c5070071102482c449014181c0b41d02c800d6904c4407003001d04010307080200d480c580c0d140490b02405000e04280c241000220400c64119401c03402c0c1e00368030b40039000a16a440840f14076810360440c4c04000010308142d002c0c24441852000420382c0200d0300c0002e023802071764000c00e0001d00c0084c005642d00e190185100d501c2d54041c0c030031070022902d90301010a19400074902c00c08140790242070030074449020400c00c84641a0410001e82c54420312112110081d4030380103041c0547c0503d0403440640940303140b000c0550304244520458900c10740d042000c2a0f80c0034191a07025600f00504080c4070f03484 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 816202050 1250 816200800 816200807
    0x313060b040e0a1e030e010c03050f040b090909010c08130609140d0f050a0210090f1709030106080f06180708071805010509062218060b1206090601090c 67
    0x4102980d80c0c82898602c200b1850100801e1003c0607a110303061141c07850310800d0103424a840c00d0440a0009a2103148051040d4050346142030001d02905041d820002e8a40c0c999505505c150040c030b44054021414201604040000c560031041807402030020039811880200792000c0204688190390400304c0c1c1c0824424203134403200c0400d82106a100c0b0742e0b11001c0c840740d501c0c607030440c070800000c116181e11000d00b8810816a055062658094515800c407008060041c00c418a81a1143d0f0302d0704000c1d40c001460804c0403a076500e20501034548510100040500b1540654003e49040d0080d01d610b0358900700115801c0c0c4d1000304c80c185111005c1410655500d888000c1d000250b143c82240b03000f003200f544841c0c403200e00c80385070881800142c0c3c0703035410b00202d0305040d01c82503085030100d0b0301c030186450002040502c2ea40300b03400c0000e400030b40c2c4010703c0200b852600c4c2507507010341e10707120041141049844c2e04500d215210041640c3e040034a0704554400052050320301c11a907851141030380307610 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 816203300 1250 816202050 816202061
    0x8042313050c0c060f01060f0903030807050307051b0127110909070f1404271202030c1e010c05090105040905060d021003020d05070908031c0e030f03011514031306 72
    0x30f0300012106180341007803800200c0b0800780150008195001d14410030382c8d100b11003540a0f240d00d0355455805440e000f80035280c90304003400300001d21505105020381e045070700c00e1190705001e4a400108034a180701804845504001905800015203550000c011404030a540b0266500549a2410035a0b0b903080140c10104a501301c8503214100034400622079840145641e0a5a021202009003011108049100c1c00072030741ca403e4403004007010003001c41c3d110745042c2d040e441d03180162880c0600f03803400c00f4186004180b101110200141600c0c113070481c2481500800b0b005070408914040350a00040c000340100d01c540002580c442d4001500c0f034a1b040c0000c010035501810742649110342c3c840190294115134103e0b0511340c40c040c00a003076a80304810240803a000c2c600034520b000d4841e4400240014500200740c0300b16190480380840001c104001c02042004402d1141c0325410301c602480002c080c100d40078100180703208056602140c1400f2260041d034900580707003091603285400b01c054071 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 816204550 1250 816203300 816203317
    0x10c0f02040203090a0b01050f090a0932010e060f0414010204090c090e060109052101110304030519090501050406030f0b0d0c05040b090c0702010309050f030708042313050c 76
    0x82c000b10070700a5040001071800c840c0c62049000e01d00356038035a810b1088000c08a030406501000c264082140010194400c183e1f083c002e0300b400f0701d08002c020600c031202c81d50384002d01095101c2c1a044a50001c03e11400c511100d400c8041c020380e08002102444180010b000908002c400e80507210114800354102c070014410f241003070004c5902400d002d024501144100705031078500900180007507100d00d90395070136220000c12048905102c940d8400b03400407000c824190565a8000162021054a014501c03c910a5855503550500821340142880460310b001c0d00b400380d20b5034280910707a080010703101078902e80c0c07800041180310245007201410b2943d04172038116215074050f6061052961b000d200b40c07a810f0b81c00b0f20001c1e080702e081c420714450850324504110018040500150b2094010704070160060049501d81c1040104060550303101210803036408400043c1000692004510306441041c0040070b420021640000300b5046412503855200156075440080c0c071007071003041a0745526 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 816205800 1250 816204550 816204559
    0x10b031f0608011701090201091403010f02040b1801091206021c020a09090c050a091401110d0c05010b0a0302130b0103110403030806240f300708010608070e010c0f02 73
    0x4681c0e88001401d9480c083c02510030700403205410400000050007052042da6043e1f54195141e4035001407803030321a502043c0f066055498a9074401c0ea20341c02c0c009000581740250900c2d0f643c004d1684040b510700c1e0742a0006040c05002d0f08100444100c43c0c0303c032054141c010342c01680d986114203164406100250701010002e00c0403038040121a4070002d0103040e520146802c000000319a442a00c4501620540310001903010714140118420f503165010a084107040101c48000d01814a500b4219041c261000154121840b5000d202c002d008a0220b0a000d840c0401041c0c159000702d04a03030200d00081c02c8613900c3e41002c08999103c0da12143c03a11003007a40c0303d6155a200d02d8005c1c980a000da440038820400124000071109141c00900303500032446180a1614a42458001040d00440701c02c0c08500c072560785804521845d040403c10658a10815401518011101030400c10040c0c1080703040218102c1041440741d005800e102d041d0409091480b403012a40c500700820001d1200000d420 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 816207050 1250 816205800 816205861
    0x80a0c03020106030f0b06130516120f060e04060c08040f14120307032921190c06020f060403020d0e060903070602031c021c091509030e03010f14010b03 67
    0x1b407001321b06085024410440c0d0f025180c2c02100c0e00d14041e5981950300108095115002034038003401030300b91008007100c0035408218540602403240c101c0b401c03a444140841701401c100003c1200c544200840d00c42d503170034184190705140e140d041c00d0b04000c0400030311200b484420525a10010406d005501c22503103821075030b0745040035004000c5e07d0b0070100d54040c9400c214250303107030342c0101c50340d10056000a441051400c0c04c24002d860400795a40340010f6500a050341da05887d51042d50400340d490240d01c1508000d0315110009280200030000c0000176041039090100107a401f041c0c1e103020441c0340c5007a00503005404c00040007031040c555070300d40c148100d400000301c940c1c000c0301401d20060729800d00c80400c00551748030000c0e0b110b0407012000c18405101c050f14092213590007154032071700800000d03800c3c00400c14041c0c2110350b40c3c203040d00891056040701115150901034004020629682400900304091a02c00c403100d040c000d10b01c801001100082d00b0744210485103c0c440c4101402000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 816208300 1250 816207050 816207053
    0x90b03124611070501170403030207080f0309070311011d04110c01020d0f05180706080a0e0f0a0c0b0f0301050d06110313020307321f030f05090a080a0c03020106030f 73
    0xc8184000400c07183e000754a0005807a40c0500d58400e10844d42400d007920716035841d03030120000e500909007100d400400740040b162070700c00240a1441891407100804803d42035080c00c010980c0001400c5040095540c81e0b845a6410314104180b4602e0a44020600d401c4404520140380039000703540100390302c003080c25004d222154001211007805010100241d445401c400d0645900c3c0c51000351407a4403c07582040703018450000c0365402a0450000070306032034800c00083c00c008030000790306140d41c0828607180c28854065620b8000b06966114203152110300c2020364032a010510a607440b40c004041074500748522900995600381c204039005559181020341e004600b5102d000903806032181c0d81002c0b5200440303050010009015020b00e480307288001c1d1000403290b0317010045540001e41031150340248000360300407200c000301a07103006c5102d8118207090070403a00001c0c103844855200c42042c40200c1d030681d04071080503440e458101e960081d1400d080e0f01410095000800142040d4030500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 816209550 1250 816208300 816208307
    0xb04110f120c0426070f120b010801062603041e03060f0b0a05210708100f0209011b03091a12070206041e06060e01090b031246 56
    0x10061550055020741525000e6208120307004071300035622210440d900f04145580c8142c40f5a0410079400212001c04e503d8882c01c09441959038080138008030003083c4102046076280d01d1602400b2410004c000f41c0d854500409440740c0b01086551103070700c1c401c1c4d031150301580c1403007124041c5c0855401400103d03241c0d1760410568129100641d060392800c4440c0822445502428519002c002c01980d440c40c145000c008454601c9803682004460302c604210490301c05118500050444601a20001c0c05074003010050320b00048003144518410005210135030380020003140c40021952038401c0c014010f15003529041041d4014480e40a45420710510b02040740d001412612030700040c42c80e45458034681603a4882c030940c0c0042c813102c2200c1c119442c48888681d5420154002c000200300a0380e035040c20104048281c202c441d0454a0f0842c4050b00d013020005449004140c003012803a011240c009603045581e102840e40860b40105280c41080455404001d40c0500a0002a4681e0000c40029 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 816210800 1250 816209550 816209557
    0x50915030d03021c0506031f0605040b0f03070614040801020d0f060b070506160311030108070515040b0909060a1706040308060607050309060f160b01082e0b04110f 72
    0x2034800d10803030346000700c080d1103030090b40c1200103c0d46030444480340a4038440c0c06040001c01c0a41c043c0b0880c1c44640c2140303006407403081c071042d1201d030004580b8208014031050b62028503140d07008180800301c2d030082c6d40700000c0c4c0d20211907561400c0208025000c1d0441410302c17495100000030344c004031390746580e0070030303540b20525824482508101096442c48802030358007421a0281050300080000341c64801d4200c10340e04105482e26000460505141214025400c282c0203c80c844c4d105080070b1009040c640303802d403981d6880302c01c0c1c00e040a00e04074007140580b040c80745150040340d1036004224141c0324190300300003400000c070300d80680030324090b00c03c0d554070303c2100d0503030010780b088022400c5c40c01c00307404a41620360820007452400c10070700107201c007583c0030314621103400004024400008103028000014548110241c0c80c03d5407410794454681941c0340010380482c2960315980c080100d0300218041c82d0241e5600101c0ca0081d14400140100504403001c0c00c8020002012142c00701e024005 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 816212050 1250 816210800 816210841
    0x10306060807060903080a031a300307210c06020c0102030a0b10050702190e010f0312030513290a020403061503080f0315061603031d03220509 63
    0x100c03507055a4420f4200d4140c1400e210181084c070003040801e8506100b500860a005010008052403203040404119000e99860400c07001a543d01f500c509034900701da91651a411191000f1820107001d91140015905880b40980411400400ca4120240120030110312035800c040215116403490403018040d50086950708038451070300d0401c0b20540360401c1041d0400e002c0c0d84c2c51034207104a690034400348248003090443c2007400d03a800080c14512042020740640703a907070000c1e0b101918620380107404424101c1c0c1a01450b08000401900ca03030101540c0c08400d8025a0008102071f0420320000c03540e011a00902034030041600b00249138006800070411248100d4003080000349e4590343c1c0b04541c50f140001808080200100d801d46050580030710f4124002443c620040101c1c1000a031650340034906c04005d0400641942080c150584154035400012003e040400d100d901e202c15124843c0403104001c1514160210404041405410300035010182c4140e60604140d031010b0030562041c603d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 816213300 1250 816212050 816212053
    0xc03090606090f0a112701180e0a0c17250c0b060108040c1203083301031d070b0309011508032704050414070f0612150b030103060608 59
    0x11410301d00b404034410340301d42c038148002da1164841034500d0002e80340b403244000c8171034000c0c01060042500d0f07080701c5944540e24001c0d00700c0c11600d280050541b0007080c0b800d461150001c842000805c40c20030060b0340c40034840c080081c590307945810580d042341920b420805070380070110822400943c1d90040c2031400f13880c0212030300900c421901c100d98401c5071640c0140000440004140b0700d50244017099042442940b20301030081d112070700759079000340240082d000a841c5800317015a001d00c40d05440c418078410540180b8000d0b480d01d96062031508507111078100f41d034071500c8941c00c0318404144040ba40d004015651003a46c0c901415442c0d4100740c40d10201075185c10f442410a1041d21300010880f001c2e40d020714148480c00f9030000e00242e4021a040d12490174524088041d661071040702d220360b116414181e1240c200341d03400fa26004e455003001100e200c03240c50a0000707a0b04070a1b4501e004001c40804920450b522010302c402a50300d62004c1594500400040b04200440c1c110100742c40c4c4c0c100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 816214550 1250 816213300 816213313
    0xa120e0d021c0c0b040201110303092b020d0e0f0a171006120b06041119090b0c10050c0c0f03070605160c2307080102090f1014070c09050c0309 63
    0x8030b605005118071480c110200e10f620381400000f4500d0080d140e445070050401d990440c80e40d82c051419a81304842c041d0154000712605200204020180e0074401035451000c030018100c1400659200e001045076002d000e64005891003550390f42c42a0070360200094049403400e03a4485041c51041e5040075000702c02e000b55030983c007242c0f00700d11425007101c03074805020061048544503038601500c0a40401e4000d0340742c0020b84443c1289400030300401e000070340075007040d0300c85100c0201100819080002103410070406034030460000681c2c00720301d1144c3e24000135030340c6600c100050f6900c0b5641c15034400c0e010702c0c0d58003d100c82010028082d8107004501c1400141d4803400b410156418144115002c5114910f405e0049442c021000201d0340f5505001d282d482c0901840618100a547c81260203a40016150036582824070715100045810303610001c40e203105040140450f00440030040f02200081146030611568140311401050343c03c80c00c001600f051100001a81c0c4111080c0010b0712810 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 816215800 1250 816214550 816214573
    0xd02070b0f0405030304120c050a12121521050a030503071412040609081209060621060c0c1024050d030c11040605032505030616050a120e0d02 63
    0x5009a100b00d0f882400b07545540d070703996103003458002407074002d10070400c0300200c01000900400c2588009800b0301c16010b10110030a5008201d42100d03000c0c1144c3c076041030302c21040b40c504c0003410703816140c130208580c0e02e15080ba04c0c03840d444050340e0be01400354444c000000d000e040d0007800841c012a6907640c3d0105c07a21148078030346528841c0310580c0ea921701010300060302042c00c5071720242c1a0741c0329410741868074080c441c60002202040d556551550064802d002644c41c22000401076080c2031030110444091001245440f00720080c80c4800322600083e5460011000b4400640c04900320789040019900fa400c1d900b189405840100401681009010401b8a0200b600c0c20b4415490369442c00c895a041c0d0310183c810420030400380d003098036001c01281c5070350280851003d800d40e4811a00e54400700c1e5a51035240c124503844580650072110510051384034044040c0303210105400c12503a54004030074100c070308041072050f01d0541c0d868010280348112020800d0078402c0c0c910f50171101010440c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 816217050 1250 816215800 816215821
    0xc0a0b0a0e030d12090c08100e0105070c0203060112020a0f0f06030c0309020904032a0b09071205150411090c0d0f0b0a090e030d0203091c02060105061c0b060d02070b 73
    0x400d00010040703240c10191034044c0d450342d0000c1c00d140d0b1203031910000b0395079154125450710451140111050b6166020300101650920625600001c00d00c4c010300701d40503640100e81c891006026650900301d420030502c0954650784003682c01842e215100d04049035407540c0750840c2c03208a00500001a0400c254161050320038060181c402d500244003840c41c1d2100d40d0b090300c101e0094088081d0341041e4131898811003602c188072030403c034002c4100d81c010740381c1656800c0c140ba000c0d0300084001002c0c1d01c912000300e0b10000c0c030b003881c1d24035801c607850240d00c0364200b2a880c904038241c8660f2003a41c110030032540511200c05840c400c4c500e050103002c5002240615816180c683d51110780091282100300500c01d05600580540001d060940c0e1500c0e207100f03400740503a40210703516a840e40c081c22040100085020030b01007c0031251020307060b1941014002000c6115090f840c180314220401811a1340c0f81d9a485801001d5009140541d00c40010003860060b40011000b52240e5160800061800f400e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 816218300 1250 816217050 816217063
    0xa0e1b0703020d0f051201060e04060806070c1505070f0c0c05030a0c050405072c060c01021305092d180d2610050402030426040e01150903060507020c0a0b0a0e03 71
    0x341d0960503840381e0230704e0002c6840701030086405070b21540706c01c00015151424030501d03010304d084da518081403506504000404485406405402e21b00e030030104200640c0c046900c007070114461a007003074845005c2c100384002c143c940e040903901d401403984280410402004c80700071510165000c0c441c50740c031440c064a841990070079616032001c1c440000038180e0b03024135006c040700c5002005681800e030000441d41c2260403c2120003c02c5100030f000b0b010924052040e141c3c0002e5a00c1003601c4081c214007a006030040304890032080341000404241509100c40e034000842c542c51084503109102001e008280c0e100d0b0560b5102080c0c0c0c07100d5041c0c40100e282210600c960a4459010001c5107071200b444002d6000400030303101c1c1100004015040030b5a204bd1060804030341d1142c6480c2c038105024640090b41c1a840064291030241d44121684d800101c00000c90303400c014009100e40e14850300b641010380e0b50020301e80c0104144c40115041e612200a40001c191aa60f01c4020301031590900d5a9502c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 816219550 1250 816218300 816218317
    0x708090613082223091e0a060305061906150e240301030c030507090203131202100f060306060806190e070518150406050a0e1b0703020d0f05 62
    0x10200312800c1c040790394030000b044000c20420201c900c1c080c2c440c01c07501c1074083c0ca81004100f98400480c1070040004040103544144085178509030500708004410681144450f07000d603803803074413000928052003903440a001503410005540711481e0107510075043d03c02c04081d09a9a610f004004078003542001010100c025a0352500603030324030b500081040700c5294040401c880d10b00351001912480800d03000d0341c025481005c20ba04011f0030740c0352240c280420f0760401e0018a205200700f00e01c0b820702c000c00405c51908003118800b801e2802c04100c0c10001e5074803c0101460500039903142d2900a40d0040f0201c6e8003c030410000d01d03890b66005920381c803055034074581052015201626180066004601b20000d9034100ca465a59900c0071401e009619003e4440c1280c0708000c1001c040350310800000380141c212001c002c07850408001619151481c000c2c000e21070f000b4000201c0c9188190001513080058003030007a15203980b860b000390fa6003149501c00c000100c140494402142c00b8209541c3c050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 816220800 1250 816219550 816219571
    0x5010b0315040f0f14010e070203120a020a170c0904150b09190e0703020705010e010c14090103090f0809121902040506030a0605010b0405040b060f04030609080c010f020307080906 79
    0x1001d0800c100800b810702d0701c0c50020074940d21a5140740444061043c43d030042d02c1e80c40d4030041580341443d40080c0c090b00500c050255003007040004080401880c0c02a40708080400040e00c0e0160100e041740d0303040005a064200548000a00080120590280ca00a00b041302c09001000c104c0e020018401d54512507400b498001703200700e2201d0315050030700a0420242c01c8988040c140d031002a400105d20940d88040440c0c0c0c00100902408401e004800000750980001e110b6800e020500400c0040070740d0b054054924086660b00050303100341c000c4002c2c9500f1420030010b040240c10001020b0380030b82c0085204482000d2080180340e00403074143c40080f07952500000c414603e400f840301814006007a01e5050181000410000c1c1c1c05210b0240038207000f9003660b40302c906000c10311003103a8226038100e202300300c1030114420542c8580100e0342600e80c007071004a9018103901d000075240c020801104059428590f50210820099014522030b51031603441c072100c0d40f40c060304145c49080070341c2c908064 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 816222050 1250 816220800 816220831
    0xc15020d062607121e06090605070813050c060d0f020f090a08070b070b040320010506030c030a020a031101181719020d060b120307030206011e0608010603090302010b0a080303070305010b03 83
    0x17003418066406540031950b8811034000d40315a03904421164105001c441c5142d032101801002540700750882d078022020682c480c007502054075080e540d82d0f144500b0b14454540014410540c0503c2c0d0411142e01001507015502e6094101d0040314075045000c40d20300440c40c001d00014076610004120045034802c20541d80340c0032103074444420002d0020810341c10310050b41c00d0300c001c0300403081102640501c034500016850a1120815003820030301285248a5400b84844a0142c2c2d01c1c860040100da610080b00440700c4c01071001a80c072455900c0c2c0c98003a14072a100005050842d01c1c01920303001c2013101c1a01d861002a200c0540c0c004803030b02c400303500100e55021820001d2103a030b020400042e002040700c94044040000c0e1480c5d9445510200c0c0181c004200403c0f05612248440f000350844032101c001d01c43c10814000d02c4240d0500c01d41c03003056250b080480901d8001c0d4011440c900001c0d02d40301403151174508055032688240c414400007850400001042c80c096025a400741000c0c5281085 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 816223300 1250 816222050 816222053
    0x2a150e091e0c0a03061a0912071d0405190b04050105010801060609120204090206040909050c030105150120010204060e091003050615010509030114071e0c15020d06260712 75
    0x2c9036000718152100745a5180d002180e0b0700c84444103124100c0c940c10825642c3d200d104284140c00340300d0051090903900c043c0e01800407152440c08201810045180103440da075841c24242e10b04007407400c08035034401c016820b0704184a807442459110340d001d5402445035903a10f0070303079900700d40880c8520000620010828811810000c503560045400240301040e49030340340d000103849611a41c8082d0a19035542000e1040040034441c03210b0002d002ca008001c540350403220031807012100201035040004c013030300941808110400d0400b440400400854441c0e031641d0000e841c000740c1085591062241784009060003220b400c0c100c00350381d071240c06001c06466a442c091010301c8400c90703690500c00e080c410800d060300c091081c0c402c114004904405142002e039005030110400ca5940482001801c065402d8a034002d620095541c1e44461820150030798884020024050060b0200f0800d0500000040c195004403a011203200d110500500c04622032200c0d9540e804203100719035803174212018070310 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 816224550 1250 816223300 816223321
    0x2070f0603110d06080f0f16270906231303081315050105010e0612130f080a09060801081b0f150706020a1b2a150e091e 53
    0x2d81c1e486021809410018008402426160075820200050b03100c451313040003000b003c02104c880c80704070402400c41c100e1203500701001516680204c42801707166124150b0150003008121404a8818500b0050240540307001030181c552302600706e03051041c0e45030f140c0c00d281c00900e0b0a40503044c6061560740c1d2235056682980c44c0d96004004503c21054101541c002c0b80303044058a21451104000188541c100800036100340700c105c0d0064000c210500094510340c011a042c00d80002c0c02c1a0700c507440458a2070041c10481c64250300401240d00800c2550616401075142c00c00e071036103511a0480d81e030325240c100e41d895000c00804a1890703403411405000e818a058183c0b4044405401e00b8140152091108941e5200c400304488050f800a04c109460741c1c42107200f0090058801204180b180c0c03500c07100c81905520300f40800007507503603108140350444a40040c006000441203645482d02254014008008201200d8083d90035803000501e05034400c54106021039405282506540b140308484 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 816225800 1250 816224550 816224561
    0x150b15180a0f06020601090e0304050d0b0402030a020d05010f0605091006030e030706152d060815101d09040b1812031302010f11100f020f0703020309030d02070f0603 73
    0x1504101c0200d0086501d1801241d44000751800fa0018134013540340006c1c04086034101c1010b04201c2c0c006000c18840b9594040d200e02e002e50b000003021006803198000030782042c1c58010020f600607200d4901c0303020040190007140c04c07007028040030807403103940d0b805028012500b250200c0f864400d10a0611140d4066403201d0000b00c4a10b007101c0c140401c607520b0600710361076207a0b14003001074914070401014503400c1000100a648211510310007011440b4078a031602c4600950062012440c0014040040302503119542c240041040c0da510a040c0809400110f5061000c10182c4211070107510174102000b0b51402640d01c0b00708960301d079071980602100c801590721202003501804e44080314449440000e50300800101403103c4036a03109100150080008404600601c9480407080f18020380202d442030280754000400324408480c0f009001c001d114000340462201d0010418405069001000e000e40381000e41c102c07220b07020001c105a954581a01c1011218902c04a05114461194100c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 816227050 1250 816225800 816225847
    0x71809031805240d0c0302030108070605070c0608090a05250e060604031101020a12020105182a010c060501080a03030b150406120f09030f09060302091e0a050904150b15 74
    0x144e04184000c1c10701400d840031241d8805c0020380100041c0718907042401880024001410918500040340d82d0385c1610405510448051000da980010500c407400e01840304096803200643d52807641001d044000d0213010b0110744801c81c4a080302180301c00c0310042a50180078003c0000f81450b156540b01c4052000700c80c0c03c141140104d1310040300142c1050000034480e48543c001040500d0540014903140b0400086c041c100e5000410303106200182103905404581d000e80190b4a580380480186ca0601e040c0500404c8140b070301000060003400800e000c070105d8801d54003407280340900c50030841040c842c0d5003500ca11000411040203200c6c050703c02d140c03c80c80e0742840400e00c8000f04c24608101e0380c04003010b078085a181400c0b000c000341c0c041e00ba21f000c0c03c0c20b800d04501380007181003c51020307008002c004149020308508002c4a50703800da80403005040042800c840c91510f89072650190090400380da00c028244a2070a00b04d18101622a1800c41c03480f072403c4c00c120180350f0340c5c03c481101006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 816228300 1250 816227050 816227119
    0x7020402130305060901050c031501142713020703050a050304060b0d030201540606080318031f05040606031415090f120309071809031805 61
    0x4482441d0031805540c000d6001e0400b400f090315280c031649081d0303403006294400c172880400401042040c0301441291030070083c0703040028001e00543d26803043c440e044a8040111880114410008400902d01c0701c66005403010765a904655103c4820390180c031b140100454010b1044040f141e120b0070140d9445401090007050140400c40490344858040e4000d1b00140d45511003083c5114407014550a1b0b1b41800300c1114020421010252081d00b01c03030280308204d6142000e480d4079403500f403c41e49041e60030180c1040444d6450259560329884074030502c0300703148030b4ac210041c540b40c0030800d98002250b00c00d2600c402000c0081180041c14010700854445544031408800304244d85440b0701c0d007501400082c06109420200d400c103403100100581c0c1981e002408460300f444005ca101c80a031500007000a03180d466101145080c51240e4004688040007815401a980c10603000114910300079154402e000c1c010748a4070300c01608030302036076420280011f110343d0050b52198181c4140080141c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 816229550 1250 816228300 816228307
    0x6020a140c060d06060e09150d080c06010e160201020703050327060406020d0f05010302130908040e04030e100503060907052101180501151707030b0613090b0a140607020402 76
    0xc0099010f8000801d515546030b80e542090003c1c50b00300c040780503041000c0360b030070b10340d0702c3c1442c0d000d400e41441c080420301400c3c4000350b400802403034000366201a14040309484540d0b0b10782c0d803400c0e0b4501c0304554a00c02d120b1b0582400c0c0d0410300602c00c1303e814980507a605491035844031301d00303da585a6510903032101c0b072a000c1004c12411051100790b0199108941c00742c1d40c0c2e26100b40600540346002144003400707240c4401000165290054040020749045010a0300101c5040000460040760b00019400d4800c004000415a0120f510280400d080310001c07402d550040d411107040c0000c039403080c1c000182d100820562400b0f2005404542451240b002090950b15000100a5020380c041c0700c02e0b06085000700c007064054003800d4050301c40405c1c0c0640707400101c45e0040c2000485143c4284e034040700408150b4007882070700440401080540203580da0300300011a114802d0041c80341c40303505413610b011889c0354540340446504407482041c2078051000c4060400089074010f0718203da100d9401c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 816230800 1250 816229550 816229573
    0x40608190f0b0901090e03120c09060703020604050d0504050306040b0406021b071d040314031b040605070201031b170a0f0e24010f090507120e2506020a14 68
    0x140102801c500e81010003092400350b440c00d1048220041e00440c008900b406030b620307440340e000000d6407081c21038014410070030f44a8032242900c81c861142010341040340050510103054000030b02074000c6200350102c1b01c407840722003c100c1d2a8052401800e515030041c0c0e001c03401003142d00e0745c0150028018100186890743c13800d15208506082c0080c0745498001c804100311703040702020340410394501c940f001d690303519040e80c0040559000640e0560440390200c00b0a90203c40000304014800b00d500e861075813607440c5da001038510380064a00701e00103420301d140545415003200c8a0200840c164032400364032411740b041c050390448001c01a5040d180e99005184241256001d510000f588003005070401e081c50011a030307113014a00e02d580c581c0d041150300400800100c0920340c411106040400160703516200380840b0302d14010400b50400c0ca0400480c8031409101144088049c4205081d43d0300c0c0030003c0c3d8485162000d60b2040d80c0c00740c1c1040070b4002c0420300c4007031403c2d400c401c2d000542c0c4600000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 816232050 1250 816230800 816230851
    0x9060d0c030f0c030914010c0504050123042d150f03290a080111030105120a022115010803070809012a1e2003071a0304020f011103040608 61
    0x500e0720180002c3d8640170002e0501c41010351307400c000e1108000a0200d0f204e64000500603100d284540d80c1041000806a50002d088200201e441440c0d050740d00d56039a920002c001d240c43c07058000c40b15445d004003810520070103158600c421100c002c40004c008072003402050303921000144601e414180c541c000004010700108495110240348204a020102300806101c0d085603240c124010b2303685802005c10140940303500b034904544080790740000e00c9180b42c0d901030520402c008020740141e445041000810b601400780501c0b00f00100854071011400d0602440c0c9250a11522020307800400264000c0750648009140588060400d14107845003904040c90a84103080b810200e003500260640402000041c0041030780c003c062580407030039103501c64901e824503542c00c82d03602a0301d2608104480d1018030452000302440f002d550040380b200c2080c00119071089a0491281035013062914070b41d80250b4121905003d0f220095050600345841520810000f40100310404001078829414005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 816233300 1250 816232050 816232061
    0x204240f02070513060f0f0911042102010c2f0301021e0d060803030109020a02010614060a12061710050703050c0711010203041a0703030509070602030f0d0207142109060d0c030f 78
    0xd201f00442d2699140c03103054030032079100001010710b99400700b00410400629040c080000000f0752140d100c1c03040a0310040e500740d4001c11009000c1c011156007880f0301401c103a14249401c1c0321110644c05123a000040600304d100303000c1c400c0c4094594a4001098610300340243c00030f17000c40c5800160040d100d81c90140745400036407040702c4960700010b08010303499080c02601d00600352010314900b4010144002001d0b80110200001003085083e400d40711016a500454000d02c0395422180418101311007054842d1703c0104161207241c204000300310514442e1191900c00c0c0700000900b82031515594036440d0015420340c940b03046110030b004c00b03e402111160110404080c0603802c40d038031000d6103006000da400007403c540841d00020720800c0390755000301c2200d20340d0112407101580c0308040e1100034001d0099203800f80401e00e10610380340e0507000003c4c5065505040c0d0003020b020358480703200c840c4944030b80c0c07440d80c0e001001440010880c8100c3c0d00002045001c41c1008110344076081030a0081f41c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 816234550 1250 816233300 816233309
    0xb0c01020405040e07060e15070602091801080304061107240203070203061008160b03060f0120010e070b091e01021e030a090605070f0b0403120204240f02070513060f 73
    0x1c004200c100b06d8240c12036110300d90f1300340580c5c00396281d080b80f40c0d1031100d602414801401c41a00001c2108680c0d55080085a0011082c18805204c0d41c41e1450713942d60703400070301a42c400b1030140e0b11454070030240001d0b86d80485400714084100d800c4410b141030041450b06400400b0b500c07003880038000580d000d020703892054081503800c40089242c0b044691806529012502990401c04414450303044094100c962110044c2c80c3c450b9070810b00c00040300c500c40d6007800d650b0300c000c036446c00010384001034100e504c4078055001103420540d201d03081901184503076201949d01c00310807000f0705030721000c40c800300c7c00719030b0140169219818120740c203448100d4021322448071600b001502082c802c0d0400f1a0780301404a0346095803c0c00655a80c1c0c544810008070090a8003010800080030503100d00b424109220180200359140c80d5142e46041c888500344079045031104003507001d241780e0f81c420328002c14400805e900401c82c0c00d290509010400089400c00000307280c8500000c10300c013400031413080007070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 816235800 1250 816234550 816234553
    0xf0b0f07150b01030b49060b100206070203070b2502010b0a0f0e0114120d080106020105062e050d1109030c060c0a1103031c1d0105100b0c01020405040e 67
    0x12014040018120303221800c0c0d40740300d501e035440d802604500c6c1900c520720400443c200540b400c1d21606550f110b1044050508a081c9007202c060030402800e41c01240d42e410046c4e071402100700109406a8607000200c4000b401a40b003445650007003408500001c1d00700784410030b00300400307803081c082030400c0462440030009031f03454880b4070819083c40842c040007007e044080b508200d00784450b18881c1c00040c132a1041500d00d41d51603614a5680740c0350b581c2c8407007100c0101c8407442c80320b100203003d40c5001d00c00c3c03001552900f00050402d0401401001403511610382060200c00b2200c04a9200c5400010403c1089410b1060305000302d00b0780f243c0980e072090b0541d400e480d1070040040516200e102c9081030b01034001400300e04685400019540c10903540224560742035034800012a00c3c5000d1001d1000d07808140c0001c41c00e11803080c2d40103101406114058000342c501d1041940c0c240c84094401110401d141c8204101031101c1c032024041000b90007001529056813480081c00340c440c182d1000c902c9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 816237050 1250 816235800 816235811
    0x607060603050f07080115170c03031605070b0a0c02190308030c1e0a140a05070c0f03050d020f0d030b131103090f0a0b01030209061309200402040f0b0f0715 69
    0x2502040090400801c6a00000c1c801c072030b003100c8072402c1018648508c50b40d807031003445001c80340311041c080c6a01e80f0402404803a04c074141d801d0300e403500100d24202940c05025402c1c010070b0040302c2a00304c4000540c0c0d511b600c298008644d0910103c45001ca4803180e44403a031150100029004800450007103004141b9036851301011900290717000300c00c1c01e040d000314000304400d940341070700241034100200b90580300507191140598140c9841c13048100c024403071581e0360300201e2007508980c0d544050f01d00400880e988800010004d90f82c4e0302d0403203072402ca031360700c0720411000013407003a009030001e180013800840710500c08445500c240ca007540b0a01e650001c0c04070030020005c808111030112a01c14100500f008121900c5010354540d042c040071f07001c2c41040e0001a01c940b43d0111444400b12001e204001100860411483c0c03e02c0304134040d01000941ca000f641c061030302e4000c0d1002d51700310307001442c50381c4e16059410318103504c514003030406054244101d00200701ca000300121440d0800501150 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 816238300 1250 816237050 816237073
    0x31315020d0e330d14090d0c052113060302121906030602070b070e1009090b0a150e10030614101407030201060503070905430c0b010b0a0203030411060706060305 71
    0x161a10014401c502c1c3c2c00170000c00841e600c00040300403189035a418225040b24480c2000740c2041c2a0509e500880c2a5520490f4a080c08000c000d01e0218400c031194035080d5240e0008900740e01c5401d000742d4200001e0804662101081901805084190384000407643e59070b545c0c0ca002e90b000500700356142540e120400410720703004000304032450f8041354609480d4079010b8000d0906000e03030250194090703a0b01d6130901c450700c1c2c0c50308100c0a07203040b4588401d0030318020001403035a408005034a016040d0045000c60041c0640540402c0c1c50a2910800c0b481c01c0100501ca00030100702228020800c4500030b0004248045008140c0c0e039019500100708942030800341881d0000c181c0c00624002e1812041003d4003040380860500e035007292030b042c0c20380c0000e40301c2d041001c814000f06100078000102507401071238000000d075480034454a80405e280c0c4e07a8076101ca4032030103081030700300140e041000000d0009a0500e000c0701c2e0303500001c25840c1010140e0310303410304607a480c1c0c1049809a002d80d10703825 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 816239550 1250 816238300 816238327
    0xe041a0909010b030607050a02010b0603010e100501050903070909020621010305010b0102060c07032d030c08011e030b0c0d14060f09010320060c031315020d0e33 71
    0x254848081e2000f403280c12100302c0400d03a2060000e11420400c580404c1804070b030b510039044801c01080045c030b920780f04d507102d4807103c6000d0000d03200d420b03c41a181e81d0021325540144181c3d40c03040c5009002d0a0340314500344866010340102c02c8100e80c001c0c01004001820382628010b81c0c0c012903054042c1690390305500d00035003110040c450450540d480b0b0300420041811280c00c90749003c0e49403400c0340d0341c030244002d526440c12241c417403002c81c00c0200c3c1c1007044180d4180d000021007021556040800e0340e0725001c000200f0a551403010080c07007030010a00101e08d08450290304244040d424500e00340c0861061003c0b164403d90b121000c1e420101070103094948652070500c60003088600030008c0d4515942c603038001401c05000f170009400b60719208075580d01c6070305580d01d24840c101034a03581e003112580c40b001c01005018403841646400031032000144001040404c10b01d0a0b1901c1150304031201c01c21051510720000c0100c0c00322080d6280c19610402510610071030901868103440d04040100304 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 816240800 1250 816239550 816239569
    0x1107081c020706020a0f2003010e0609071e15050403050307080319020918090a062307050403081e04030813030b0612030d1817191e0f0e041a 62
    0x3204543c0312003101d40101d0b036010031404070542e010a51544447c2d00c1400050800103003414243d06529100c00884400300c082045072040000038181c0340360356106c0e1884403808413104408091903a4060050100c04454116540b02101508007a8206030b40c0c2e944403407669019040c1107400807808000d0010b14081c00d6000c03580c1e02c41c01c101c10760a240c0781384081203895100d02c8503c0d04015804000c24415601886441c9403281c2006045c07001103000301d4000c01c40385d42c0701000c40c044d00c008070026070341605c0f4030b040e030702580c0d408401146003a10800c1d20400e40358401c0b280711040360040ac80080020080401081242c100d5019030031110f140d810710f004074200090500d03000f00c0000141c2c12402502200712820303883d8083c0c0000b8600c3ea200b022600182906c4801808480c40000e0801e80c0a0004081c19002c000024064580003014000702d4440903080312998071080c1c1d04807a00d42d0300d0300400d0310095a81583c0b40c4050728042e904006001d461601846400d200c2500700034080b00d041581c0d11 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 816242050 1250 816240800 816240809
    0xf05030717030c09040c0e19030b15060a1809330602030418021917060d020907050705010e0106090b040609060f060c05030403061b0305090105070806011107081c0207 73
    0x219030031803610328103c103000d202e07910707200b4170640e0388401402c4141c0c051400c44240c90405003003464015820301c0a003180300c00d503002c15a00b00e0544000201070b9849180c10500c5080090581410312680c4a0706072102d1640304d100c3c015020401c1c4004c50781000c80d200e01d156540c0142841b80311080300140403421202036140740d40506040d800c090103010380010858080f6040703445000c840e0301400e00340340000d00410300300043c80b541244000c04540e82c8000541c5201003840a000420f40300c100402c00408064000203401114500010f51802c0c010360260007028004c40001c501d00401e00d01e62070031280e40c2d400050415075280813210640c04c040c41848040c3c05c200c041002400e082c21354403023054045114178410040c66040a00c10040e05005486c02554014400d2120b2614651078240200ea20805400042e15100c00a1034640050107407a005524580b1500e070a48c1f65000111081ca010680001541c840d0910004e041034041240200070410740404c0410010031100003820000c43d50310 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 816243300 1250 816242050 816242093
    0xc03061a031c050d18020102100522030513030501060812030f0c0a09121a06100f120b0d0f0302060f070f030c0c060f09060e0a110603130f050307 64
    0xa0400345510300090000c0b00480084800d0700b04014030350202e94030b10501c0742065500741802c011010701400740c0b01d100f210764802d03000d0305d4650110f10030360001c40300c040b1441462504050000d1140b0803c50820411140c003d140c514070301001500510040080c95001315002da540c6d03101040700840500620300003000c1810158954180341c0e0024003000d0016010f80b121407000500c0e0a6881d000e511101c0080c1040032490f1401300c2c0d00e0410401d282e016000b14070f0b40c2805000043c110b03192943c0c510340041d40e240c031040c04002079034000700c030401281e81120312107941c0d40d41001d000765103002d40c08044601c108440e0082c48000c1c0b50082c100f0a010300010075040c00a814810070641040c5c40c002a10164a00050034000d07061044440d001442c202500c82e6240c1050891502c6d029041010075030b00400c8103100090340b000c203060359140c0701c9901401e015040450b00c1c482e45004401145c002021500740060380145480b44d081c001c0140004030760b26803000071000d0412501070800d1810608444 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 816244550 1250 816243300 816243341
    0x1e010b0a0e0f19080f010b0d0308190b030f030d0e0304050109060c0303150602060601021c0c0f080705010615080105010c110120010524040203060604030b07020102040806040c0306 79
    0x4001d0034005144444900c20307441103800e40c0c901c0c0c8420300181d460102c01c644546410b9590420980c0307030319441c41100600d50070a8854a09030074024135030141d250745541e44110941c0d40301c4601d03010090062010125030303101c20aa0080b96000c011102c0e05403d080091541c0b05d1001d01c104040382c0d604906900c0c0381d0000e05c07040245a8220782c0a0342180e0303031410b080d00700d01898071f0114010304021100706031030000c00d4000314840c1d0780000c0d400d00c0b4901c05e808952980703808488203c000c1c2c6901c808a4002030185180500003240403421101c1030b441007030b0050508540d5900c5900b500c006070014040740d082c40178292501507200010a0060400382451180500070b074071a6440000b610701c010341440514400d0781081643c80d12002040190b8000801c840d09048848107040041e01268041020711000003130400d141c14402c42c1e000d5140209806d29242c51960351240c102001885041555424040001d000c0d0b01032164512442c0b0980e0320124650541c5400022a482c503840140200d1895 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 816245800 1250 816244550 816244567
    0x20c1c0812070216240215010b0703020c03010c082d040609081e0307180b0d180f0609022b02010509030708070b04030501060e070e0607020114031e010b 67
    0x1290108806075004100c039645400c0300764030307149070045152503000060a00103041032403d5107003d5044034410f2421070024640d0310072640c400703400690090001d60203004200000d1024024520781d4464010f4410f60644600080c0c2103416000a0401080c0504200400f81c0c40c903007008444a01d504680c01010444484202c3c0c65040083c0014001643c0d00b4100d42800b424000391152078400c128418174141d0a5240c28040740c00a4404d600850040c450b11020301d000e0200001c1138070484000503040120300b451920250224181030a800c428822010020441104a9011b660300600f03021951030114818492540c041e0f4014a0180c1c18245039880b811909646910103c0d0702441c02c2515513150074002810018940d0040c0d5140c440c0141c0087c00303410000c0034100700c9008000800a140c5d0311098408070040488007036000419104049140d0b00d0008060400c0340d0043c50020381080c036801c868a00b60b4130580300444082e001d01450f0560010b00c9403441c2c05800504681d60404428 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 816247050 1250 816245800 816245813
    0x501240503070c031427062104030c08131a03010b1b07050303040603270506010312030b1309050c01050f0d1116080c010c02070e0412120c020c1c 64
    0x18010400300000400400c0a2512900b0011701000513014070940d500e108100c411400c0d800400e485844d10707130f0340004248901e0000e007070b902c109104e881001c04180807140301f4080c0341e4009000f102800700b9a88110041220000546840d0221442d0800802c0c1092001143d840303500d00019410300b800c000601c42e07448814155103101075032044034403569045c0c6111508251030f9401141d09440301041c0000c445d03615411041100c2080c101580708042140200004042411405002a8002001080014000342d0003c005a54902d00010001c60040008080940b1481c4041c205034582c00c114040c00824000454616001d00342280352086660701f1414030300a01c031302c4c001659034426446034070101d01d4085403154800c49a00d0403504145140c100d005800c50707001c1c41c1041d03103400912181e240c00010300c6001d59140308a41202d039038031540d4100c02110030410801c01c00141e50704014903c0d51502848071551000c0d00541501107214041c49038480d8020fa0b261408681c070321245002c61407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 816248300 1250 816247050 816247057
    0xb0a0603030e040b04060e071701091a0d050f2b020606010210090615031b080601080312040f0f202403040c27050a02030907050f12030d05012405 64
    0x800d881c0403130b0742110400080d00411865001c0300c1003542c00c20401001a52100105804503410a0741e148140d0f2074460400864140c4094103030260180458200b691070402011040c00d84903404403039041d400c08914074142007138800401d0251030030300322014002c11040094100c00e4071610003410340e854102d00003940e969201d0006024180e8415440082c0441038004a080c50000411a000e0541d84e180a2589186102c80901900000b03030700405d10140c007050150407541345034019402d0800e684107141030024090001c88441c0d811070000300001d488079043c080c19901860001c113652a0092960281c0010b45001c6407182c408004003482c0895024070001ca814120303c8081d440c0da0f05c0d4500307004c02e01d44030340040d009c6946184146601d6031403060801c0d030743c6400d0003040c401501c945810a09074001602c6401a540158005110303a0800701d1000d100382c0c0c00201026030540318042c0850842d400801550a4261101c0042c0251043c80e208081e154040d110206a5103442c103000a00702e00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 816249550 1250 816248300 816248327
    0x120c150306121e01060b04031709041b080f0a090c1502070e04060905100207020d06090204020d020d0203090606062b020403060f020a0906091202090910021201030b0a060303 76
    0x2140400070489540340e50041d001519101c10441d1480c01c442c450618881c41510070201d035035805c200c0c1c045401a00c943c140c8007140c0e40604c0140000725030000c0011250040d03041e16030816903402d40d0301c030207e1740364040c5521031410781c80e00007040c203240306894010080102201c080c00e086c401040000b40ca84241c007021112a480d000c03280303404c0800c003242459a264480010110414140030031b001243d8800c0310020306c030700d0480703420207901c99080302039000d00e4102a43c8812010b0401c4041029501b000c180740d407004000510f042c0b49020760001b260006041b03000c40683c080b0070000000d2040007280d41024044030118141185d00403807080c40400041070707aa2441441c85105040c80c240d805450203540c2c00001807050490002c540f4009400c15610507000403051440000c3d154041c03003505040c0c440d44121041d000e0266002e001034041c02500700d802c80d01c150141034104403020705c003a01030780030140d003840115403460401c2a025240900415170b51450401c0820000e03402203412103404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 816250800 1250 816249550 816249589
    0x1d0c0f0303043303060b040501030b030c040c0306170a0b06011b020901090903020114160c020d0b01090e1509070e06010c020405101a07050a080702120a050705120c 72
    0x8809100800d05602490340442680058043da501c6420581500d90b1440a10309190760700b24000100110152429449400400c030402c11040c099540310340c000c500741e0361000d4101d90281074901c0100707045030325544040700000d944110a100340e002c0300310300000c0e104080700140704502c000c1e1103d82c40d2090240c072413030606c03001c0358040b186c1d400030714802e80e903480e00244883e9a541e540c4d50035102a05542c981240103510302100d4032032038014544418014051542d58520000c03900c00f050700e44170400c01b002c0e41d101d000c18000314001201150030701c0c0a8580490085200f101c1032412a01d4040c400d0340902e8141c1028040203220a80011a1307411a900d44002e00ca160722400c00617107146c42502c8000e13410608040410030340c8010564000c2c00c8030042000c444c106940700649240501601e0001445900401d0340c1901150101c006840c500b40001c144244020180c00681e240482e00359080712740b9000680104024541004e0014555500d100900752a108105c0051400f0011490402d000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 816252050 1250 816250800 816250819
    0x31302030f0105091c0807080a050a021e04080111031e1e07020a0209010503030a020616090506070b0415050402030d0309171209071a030f06010c0606090b041d0c 71
    0x55540400c0030310141c00440000b0460f6050043c095922655000036540f150f5461100324910a40b05810340c0744520b20310354035000503444103940c00f0054500a00410981c0c0d8080c02701002c80c100603008124800020b0f4a00d0365607500d0721540900396000c1d143c181880010510401c026451000c40b0114000d8920b038081c1090382e9031034208190f4090308000311032010b80500400c4820f940005a0b080440c1c02268010b9507aa80c6104241d5280b140b401e5000c016001900480d000014a02d58030003103660f0341c10000d102d15251070120f40c10f03030000113060303c80003c403105100600203859034074003000d40c01d040305002c146031a4001c42da5503000d00c11640c0805035144104007c1c441c2c45003e4100c02c8050480d4203580b00a418001c880580b001d40d00e0300d605e4040e1090001c0c40c1801040801e080708451100b00d811651418a110f40303400006051740e040c490507604038000034a0074412000541403800700091070406100a010403140c1038080031107100382c42404400d04610005112810300c0703044618040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 816253300 1250 816252050 816252053
    0x1e0e1b09031c182702090d080a080a0605030a020d0201050904060504060f030204061508160c0b0c0a02160b0f1e0d09031d010f271401120504080313 65
    0x3030101000c1c0702041002c07502210340c000707551121200c0c5082810f0248412000c1d110a441d0042c0b445951981c000c050390043c0c0d01c0c0c10880540c0141c4295030009112252003900381d140c043d400d034070075032880000a15020420400301800d10860b4050141a001800e4441d400d0780490715210321a000641481008a2050125900c9030485005880042c000307010301581c901c8012507609042c00300700e2040c0d0a02c880400c120f070050f2100a0b0082d025512000940c9501a541c582c6445800c0020200242e4040c0700c8007284400e2003580c080c0499217030450b82c80041032402400c3c90a60740030810445950350041050700900025212940440280259540d4800c038080d541d082d44001c0e10410914041004080c5040543c408500280a51250060700e4010300d00d0042c0110035941042c0410441110510010300c1200b02801c1c0d00f00349040302215001070400288011a20f60002c01c48000072040001256480550356110000020b4240500c2c00e003070307a41079442d000c01003101101d90155540c400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 816254550 1250 816253300 816253303
    0x3050d0e0f0a12030e011503260c3301031704050d0606030203010c080c0706020306040b0306040c03030e0118090905030f16170c030d11040f1e0e1b0903 67
    0x9040c1140c8504a46080346140341164660503c00c1e00c50011038030306455818104410b0007142080e0036100c1301207010a0455407151404000c50341160450401520030707806100d0310718003d18001000400402940c8408068060740c41e51000d80c52003450300f1010a8854152001c00c661b06496000c0c0004074a100000c128034800c1c000c0741e119580c410300324200601440055405442528000c1d0024000d91a0441041d1003c0c0f0058400c0001070b4001c100c0300c400718525501554001e40e00410120351481c103400064035140341a0341c2621004c0c9811804c000309500800c2c6280303518420700707100441802d00310229041006a110f80c0384280e44034030f4500100b00c130900845401c849482e41071500c0e80d00c000c2540c560900901c3c0c0448610304ad60140540c2450654155010400714000851520310007409a2004e0300c400d00d0308258503c1e0500001c100520040f0110000d4803840d4844003030b030800c112414030042c0950b480b048400d8200810f1051840044400c042c44240703060021381e5407a80100131a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 816255800 1250 816254550 816254563
    0x603020d020f120a200d0c030609080f07060b04140921090904120201060906050a0308280e03150402010206040807031e050901120e0303061c060203010602150906010303050d0e 77
    0xc2c5814003031300b007201041160f20354141c0d00340c024036081c600c03030a21604144445c172101d420000d4019250034100300001103040c1c012042440c4141103103424401504075400745500588422924103840f080d0420302820144100c01190060728070030182810081042a111040c00c0035000d5041840029041c40d0a200411108000c001500318452481c20342400d40c145040051705400550074000d00281c0c1107520b000d00c0c02542c5004250017410b034603503960400d46500941030402e0224407000d40b003025008412072280812426201d1710340540b22201050f0030811065190204100004107100242c1d03400070701140e1282e4000005a45e030906801c09850840ca03800c1c02a01700d05054a00a415a0344400640780c044801e888000d40b01d036020b0004001e58401140004140c2d01c2400040e00a14184040049003211412307000340182058903001d050b43e009030064070250b4404007101078180a5014140e43c88404540542401e506542e8000c00c1c910504c120a4a2251a12406001d5800a0001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 816257050 1250 816255800 816255829
    0x18010e01020d1407111905090c031b0d1506120b01050c06012601020c07030b1e0a02090111100c08090a050d0c0311012309031c230708060a06030603020d020f 69
    0x2141b030501c1c04002054400f600360254a00551100c000729541040ea0410350307005141c1d85a500030210a040101007168009000f80f1000302d40701c0301c3c9540303c881c04802110280016a0746d45101a00308006042514500d103441410441d040000181c6c1c2c22010031500d05541c00890420400ba0902890780c217500358496002240b544005400c005400d000100c20007101e01c110040541030b82c40d40345030b0142804031603104082e506654001101c0f01c070141d00605d400c0c08141007000000d00400c203418640006c0610516480c1c0d501d08075a8101c41d0840d800700d51103884c02e8014003c003400741d620719441c1e000b40b01c441c02c14400624003845c105401180800502a2008000c01500607548180c3d61074204c125030f80c00b407144c08240410701000001c8201d0307103005100462a054030410680034801498000312004140b07103c500c1c0c400d4900b4001264602920b803039036841c180d80c104079003000014001a4000406c2c180350004c10001a16001000d032a101d804880701c240c0040c40402140d00800310598 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 816258300 1250 816257050 816257059
    0x7020a0212100c1d09040201270f080118060207060f020f270a06081009240504020301030b0f0415110d051f0b070c080318010e01020d140711 62
    0xc001c08a400c00080d140700b00d491500003481003c009400955400e81c41c0d02d000e901c0f12061824070840c508080c548507810a1043c5803412030034501c00c5400c03996402902491102041c07181e41004481c450b46a80c0000d000a10002c100e01060b0250f544d032001c0880714010507907600400c0c020180001907000683e0307000d4400d0b0a655034545500b00490b9076100100742010040c43c9184040c1802010700c2240d45024090920b0501c20309284050710301d00002000c1c03020109030000c02060840403400703000019a00c45142406145000b18611407400340c80c2c0005000c0c038414001040824141030310a900034001c00041c01c0c550704e0700c0c2000542ea20484481d250007904100d10071142000d004020440c50000c501e01700708940b98132503420b860480541c0c0d4203401c54601d040c00e0080348100f0005040040c801c3c0122030002e61395410f205c1c02e6410034454680c070110280d40e0362203596040480002140003d10180000300c0c2400d034042e101e01c0c007a016680d20300d0b00c081450783c100036011880803050b807001030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 816259550 1250 816258300 816258319
    0x90102091305071b110402160f03020606120609120a1e080a0b0a030b0601140409060e100b031b0a02070b0d0515010f050d18121d0307081507020a02 65
    0x7041c03103000d801c0540360710740043c5044400c000c40c0c000705a103c60300140d1068082c0409901c0c1e80400019411101113030b403002a40b030003d9000212810f000503681c40c400c0c4c01030660341c0ba00008000d02c58280c0076200400f0382250080201700400485c4003040c00f201040c203d80c40f2051341c002110b020f5140b405001d002461074285040d07082e0040b1020348208407004040c4070008101082c0043c00010340300080403000c5110100d0201d40c0030312211565803165043d01c904269407191480e040d00c3d1250701c008a4074100b1000d200301e14290b00d2020000c0c00820010514604080305151040384031190004080b0302c0200744108941d00c2030191900a0a800311003944450711007442030014001500e41c01044000d440c4001c001354043c481d53390100d1440d888417801c3c842030702000700203082620300c80600b0744030b040301000c00200a900c600f40100016030f07440096400e008007c00400c44407480b828826444130300100422000002ca820002484000b8040c0580702c80d0301c01d9203441d6142d440294080700c9003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 816260800 1250 816259550 816259579
    0x91f03260307200c01090e0c090603040f021e011706120304090e010b0307051503040219060509030c0f06040302060f040b070305180448090e180303010e09010209 71
    0x360941e0030302c4a5030340000d600a61001d80f242c1d69206611141030105400002c104412080030074000e40c00011095610b1420501c600083c0c0c641e8021a011032300700341c240d42460103500345030725030a03031800c02d4100c0c1090408200700060001240c4102c3c9a89007480f2400041541d1604911012200c1d90b1074201d81c3c96503162001400038008842c1a00134640c60300300404205e260008001c3c0486002805501d5105500e03603902a44e030344014400d0741c01a40c02d2820707000a01c1c0d0068500000c01d07440d0b80e815200e81c01841094140700d5180880380c41103607003500c1c1045d00d558803c12034080300c0d0304480701d0f1303601e0091245007001802154468502400017080c58014190400f00800c1d4148800b074060b04902e140500700b00c21038502c0ca50000c1e40e82040807440742a0030313040d1080300c00706001110003407407170703551116000c6146c141000d2140003ca01c0c2c041008101c8040c0050b54002d4100303a1040c00c2540c68500c0e0340d540380814403c4444050444000c520424400c6d8100d5409030340107404003082c055070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 816262050 1250 816260800 816260807
    0x60e0d030b0321040611010b06070f1a0106020c0609030106210b0109050c04050d06021909170c030d23070606031e0515091e0a02091f03260307 63
    0x1901c00c0380307019000b0b403000d608a150300c10f0300c80b500000045803440d040500b0440b003204e00e9024009268881d40d07803010804890340c5c55a028081283c031500032103900101c1c914008000482c6080c08100300040a0300500c907507a0082040e5500d1b08040d18455110f0900c200040d024043e07560004000300c01c60340c070350502054011407188815018002c2010740e66610010141162412500724004080034842401240784c0006a480c0302ea001c1d100c050b003800a2074445d1022260720b0800e601c0800e94080c8108441d421961418000002ca00040e0041c1c800c142c0100c2d440c1c0d030320000d0001c1000b180c2c100343c05900e00c0c241000f1851080000f01113032102e80c2403070302c2070061045000030344038500c0405400c4241d400c0424040c4030f0340d0f4000c02400304c142d910411824018006402d94416002e0a0090f9540c8420001000f400444840c020b103001c84490040c0580c0f004050416000c2c0d070a036804115000100070584000c480e400b0700e2144001134000700910040c5901c80d08181c4161001052000c1c1c19030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 816263300 1250 816262050 816262061
    0x6020301050f0a030f0209100915030507060c030819110a0e030c0409080a0c0819050913050c220e2e1a0306300106120206030f04060e0d03 61
    0x1d64001102c1e00030507040044400040c4001444405003021000050a04404440d0882d0400f032103e072440d40c440d2051003d40d000c03503014001c1e815010340100207100c82008001c008007214109150b81a100b52401825640014003844507101d544881000c00c412552001c440303118600f00c461740318088908001e200400000100b0f21038401e1031021402441e05100e0031030241e0340311842514200c00c00600359604820710005071075610040c0220041c00c0801c10200c00d00b4119503503100c1d542c01c81e030340400250b02600d500032062176240008005103c401e8004603540e8450f4201500d280c0d82c840703031121071448030702c3d001110402444070500103007190841241e500c000f15204840c1002904451590120703245101e01400c02025010311846514200021030700700b81e012f001c862180c2c8044040e1034044001c800145004511100141042c040c284180741c060400035161900320552030700090018040036000c0c80300f984508c2d0100d02007210070381c0580d030615640c90507244580441c1d24050700401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 816264550 1250 816263300 816263309
    0x60d0b0103240c05030a240f091112183a031e09020a080a0506040b0106052a1f0204060905030102070210030b03031c0f110a35010306020301 62
    0x3602d01203402510202401030304080080b50b52001d082d0b540306017081000e0701200b03524000010001d28420a01e0061034a507401504078070135005411860042078038211034108001c246403440c288986552828952000c540201c107881000140c0c03c00d56a0304e50510461070074400c8e02280081001d484040300c1032441045085c2c61607509400e01da40c140a400751441c44404891603c940c103102040101130b640a860080c2c00035002035150743d100c00c001303441c00b0000301c000c0d2034541c03000c010001001029103000e40940003d14201c2d0910720b8114400030781068191080c02540c0302060104480d5204004d64083d040c81d6400c9021081c00c1407043c0c0d4000d50081c010b001c0000d100010100c3c03203042c1402194002d640c060300191049646e070303030210b00524403a604950f042c001001000ba24038aa03011218102418407800141c103101181e1590407145107954a0440311007e01000c241d46030840d80342080050500131240700c07540c01d100384150703003105903058032030b0700d4507840c004424842181d01442c140c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 816265800 1250 816264550 816264593
    0x13b01090605160204020319050421091404020d0b060a0f0210090b0a0c02030702090a02030105040b090f0a0b03030912100501050a030503031303051b0105100902030c0909060d0b0103 80
    0x40e610340e1021500c1d440b490080d45048401801c9100043c103080e40119440740c8100400140350601321000c20503948180c40942d002203c00d01255800750480c3c00e49680c004c941d092000c0700e14503080c5d25407000310071054514402c82e404982d45007400099004403031000030003000295030300900301c40500981d550300c802e540140700d10140f80c01441c43d40e01c00d65030040d8106d003c04996170340300c034015009000d44d001d0420031030005010302c03001a152440c1840c003952400300050303185d604100a0004880070840b030248100e840009101c00125130100e000c0c1c100e4100000810f602c0c1400011a16500c100844d513900700b00d0200c0c41003850355012400407800d00015006100590742d4004010050040d4000030b0055001003006c02c0000e14a4400301c0c1c104c6211b0b0501500700710030100700702c0b150510706054030390302e03510341081142d02c035106132503a000f0385080c110440c2181400d0220f50a00d01603001403902a0f00d004c1e01203210766591007810344900c0d0340044c9811580da10f919024007081c034140c2010105 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 816267050 1250 816265800 816265817
    0xf03090c0e07030509010c05071e1205030a0b180f130b012319052209060b091819020105040e04061b090302030a03030207033c0206060f013b01 63
    0x7001c45c10301620304008626070301e282c2001c00c281c440c00741d4406c00481200d410310300d040f6039400042800703408440b50825503c80075140e240c61006c040070340c1e6078144180d200d100a41e100032501c0210f00354158110494900c0c40c0d030a0355902c038452280000103070000c0e144035007950000595400f01445000301250381d00d07441c03144000e240140b00c0030f40100c40035090782680b4100180514142101415001803003840c5200600c05030711032210481d10200f40a50301d454031401c05050a00300113101d160045840c1040e01d071381408070303060661951740714285070206404507015081560f00c52003e6402500714000c883e130690420340b414900030170f0882200c1000302020746032241880d00441e51082113036006005070560b010240c0e0f0481c009c0d4401c007002c40c01e21200c01e80b001e8202d000001c50400513a130f62807000c0064940c038100210310611070001e400440d801102000890f448420303070032940704001c1c00c0810b012030000800d542625a803400d10210b0b00c2403594010681c0045910064200302c2c02e8880902 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 816268300 1250 816267050 816267061
    0x301050a0c091202130e0304090c03021b15011502121204030e0d240e01021308070519140f181609151409030304060203040509130b04030f03090c0e070305 68
    0x10f0490240003039400034400c1210000280b85800a908218001c03041c0c070300d003d40700d8100c141229003100114001940c00f2602c8003540083c41041c80019607a0402805007200c1483c51103903040c01401020b2001314411102480c0d075000308202004222140c0300f203074070f801511240000801c0d0454041e000a1401002e011460411001118016410030b40c0c00540d60812102c042c00301c1a00d0b000c80901d999a800d220790000028070151290b1000004025105480c3c268036031f03d44407903078106a1062210011914440013401c07002d5045070303030646540343c0e0f031f051002c0000d0054002c03450380740c0c0000d40440600200151092103c5c0f06030320400d8204d100d8048000c0031907101d100f40c0103803e6800e41d007194204d170042c010900018203008129200e0310b0030200d00f000ca400c50300164030060141c0e0010500340880c4c980800c5441d0300031100c03c100c240d1207a01d0b40362a0b1a0000290001c2c00344600e407032850030000d100c1d400c6148202e4201303181501456840d130311441003600c100c80d03190029142001052 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 816269550 1250 816268300 816268319
    0x5040f061707091a0901141c0507020606010207180b090408030a0e06070f20030a0e0f060a08040f081201030f030f0f1d1314011509030f03030b0402090301050a0c09 72
    0x1030300c0611340c84505160b08400c0081d50756101039500703414001c9803103e131321120351000010a0044ca40c4c0060103100359440504509a03a009000c070000c0d0342001041010599000420004503440707001d01c44030810a075541c010045c02c2d449205604031001004110510030b030400114042d46040b13504210b010490f02c3c01523252032007540c0ca68002143d00658070101446110000400b030f01c1036031122040004000020f2655000d00f510001040282c03014001c80e14142c84200c0c1908800c0d03600d5464051a024010214840180014410450b140d0703440144245641520701c02c250f00d282500b44d550b182c0c01c2c814501c06551400b01c0004441d8001c0340d240d540700d6203622450040750b4550644405200310702885801c102c440e4140c000350810701115113000f95019071802020000640d10065051403900d401a4111440003c01d0003c4c004041000406840c5100c4a1603018070780040d000d054040010042d1155204855241d03003040300f070000d5107419500150200110751a0841030f5a52101c612 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 816270800 1250 816269550 816269567
    0x403050712080702132c070b0304120305070c06090f0210031a010e0f06070c032a06030b0a08030705010605012705210f0313090b06090d0305040f061707 67
    0x1800402c0502400f4010300f40002c015a165007610310201e18154440b440d9955601000c0d580c0d02e01035102009040340c0201440307580050080c8010345884c51038543c4404005804000004040650303817070000301541d1055400c0c0013000c1c0e2100060044022604007003121007035801c8240d02c030751030b41e1031500c00b2680244500070f1003c01c1200d01d0000d0030707400801135031030056203014150421021801c0b03280c0c0344e50380001080c260344a10020040c10341182030001183c822203000305461100f9092aa06803902940e80d4000c5075800c4c900803d4499000c0c010521050690348100c1c094480420118104141900f000c02138503402c2c0d83c0d102c3c01d0512442c001c0074103c510368209203c4101c6600a00090502200745a2240a00006c4100408051903100d2401c101e059900d0441c2d0000324000d1002540e2407200c038002c1000510620105c0042c0000a40f148105030078103116000f807006460416010f04240c80007822000c81407561690b071440b001e0106042c10801d0130024141c00001814603000315000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 816272050 1250 816270800 816270803
    0x90d08040f02090705091c0b0a02070203060a0b0a0909140c040b3d0c06050702060f06010507051c0f18031e0809031b0102010b120d030c14030c0403050712 68
    0x1550340c0790034035028400d2480000d401e00c42082000c2006070701548031000304c02188403686070381200d02156030400d0001182d02030300c04400c46004200c01c0015030345c0003071441c0d0030040b007a00025003101c1190000314071307140c00d92000c03540d00e051040300b000b03202501c00f403a0100481c4109a6080946d900304000886038601c0d034540c2d204140d885125500d04110034482c01082c0740300c411010454843c110302d040c41001c0703404180003449a204013030401040d400303100c0d000700c0c0b41e000801c450300b04540590b00021004019604201c40404c6000c00d01204101000018043e250060900c001e44840180341e8150740006034081218204500f1850301045680011203402440c42c001005400314030751103881491000b5a00144240007001c1389503010f2140381010407074504e0f40a4418400030000e82580c0b00107940c90310904070740c00d80e0003241c800800c29101651062400140c00616044140c8644d42c0c003800f902c02e0040084100445a40d1500041054900600855620b15507603c01ca03a003000c40c1030300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 816273300 1250 816272050 816272063
    0xc0d030e0d091a0c01060b070803090706090308040e0726090705150313020a090c03020a12090b16030e070f0504050f0c0f09010c0213051501050a02120d091505090d0804 74
    0x220540e4080c0d0b00f001800404240300000700c1c08550305c24000300301d40c03c5820241d50f0400000144841074904200b07100c000c00603030510b8a000c0b40f03991a03900e0540a1840340c5400c4468002c00900ba140c0b240c071a1001502d521458001e4445242940c0d122840007200d404d02c0c00c0c8101e80d4042242e1401c080d183c00303e0040d141d581807555680b25105500b01076201801c07a004030500c0c030042060413032805018940641c130b590068840c2018003006162a00c261120a251032503e20094040380039001c085d648030380d003580e00484421021078118000c1c0310b440300c0d13095240180c08000c00d01c001004404c804880c0b00f25010310845e1100d1118181c01c0c2c000b5030f507015a441c420021121200034100141c80e00500c141032a6480603002e802158040c0d15825150300d0055403002008070744130004250a400003400c0c42c08504050001002a5943e1140264120506008500607440108540020f0607c40d440580056500ca901c05224043c01d01520a21b00c68080c00d48010305540c0700e040031381c4c1318580144 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 816274550 1250 816273300 816273329
    0xa080a0203070302040b060c0a1a1b0a080711100e0f03040e0f040c2114010e0a06050406181a01060c021807032406110615150c0d030e0d09 61
    0xb805c1100a2060404482c1c0014050041040d00d40302030240f540101e029a503a0303112083c07102075000c0b0840b8003c25516210b03038024102440200104283c41d4a41315a00b0500c0350b944500c60156140029440d03c209144600c00031080a00c40e00e410514500b83c1c81da049944481d00c000c0c41035240d010761b0045005070440c0a0018035144844041550424010800043c1103a00e44940e04091a014440c11f402c802c012842c0c0c80401c10101010995007000e02d00070002d6880300740c52140ca0340d80c18880680003544130303404501031000e40c0d40602c1c0001d048414150f555040da10b003103100c03e0704245d5904d400e44400000085c03142d01030355002034041c3e8018001c1c511071400001c510700001d0090000d10804ad9660280c079280c45074407802144010110248a017407600e44200108404011010311041b42c20840901c640404054020a030b111021205503034500d20f0803401282c2401210242c880510644144041d407680592004403104200d90030f6074424608203000f902d260740b0038070a0402c000e0000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 816275800 1250 816274550 816274553
    0x90b01090e0c160609060c09060e040606050a030e100c091d0906010b0a0e03060403021606050f040303032d05060a080c0f090a182307030804060503071b110a080a02030703 75
    0x1180c030f1091003032158800007072901c132549610040783c00300148080422121002404100d401c4040720100b80c004a80a00c21542820380c0200355010700e552075024580c4030501e026040c01c003404400100d0150b001c0030001040a80001005520a48070301289402c909100b0a00098002c0002c1d116440300001064140d01e041103000003903100c0c3c030400042018401380d09045a0701840168001d500035401403100c405c903509170001821f00d1f40d0101d028000200300d41204001c00340701303440c12650142400a00b030740c0024074413040032540e002410740c925040e5098410031040c0d580290b000c1c01007a00d000c0403081d220442ca03a07a900200352030301d5100701c0c603464012440c50b040c5030305a03000141d1200410202000d405c20700303080751440400c88001032143c04c803818400800c10f0f10510000e100d0014600640380d5180c070030061045000d050100b02002002a44450180c2e558840250354807044c50351240c080d04183c10900101c440c414454144600001580030002503542c00d140e400801038620135155 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 816277050 1250 816275800 816275827
    0x1505040b071502030405060109110424022b0207090b010c02190b1204060c08040803040620270126090a2301060e04030503040318050a090b01090e0c 65
    0x1220200c4080d015400000b06108060010b94002e510070001043d03079504040443e01940d400200802149106200030460f00005c221883c0003480c80034400c54241000034400c1b82861843d00100d90051412090101581d031400d03c0640004041da00b070f034400b280c0322160b12080ea9202c2e00d038280050040901030b40076103490000b00f5949400f1000038a4a242c1e0350041c00c4850300200540c4011581c41030411043c0440f9002d40003c0003100d00d022061441c040e03841c0062404003400281886680b40510260b2449020039203540d2202410516151003210131101c0080300c4110008030303683e80740702b00c030403007940600000a003452074540350084607081c41d00740c0b0b100c1420041c800900b5108500c445130100b001401c0300c02c10284109c42803070100c0e003502c4960f030941c0e03c40d42c0318401d444414420003000c603074041c003600e800075030500d06082d0b00c1c5004180158071403400d410155210440c14400540b84400c0c0e40200741500d03007a00da100001d503680b0301140390031400b00c0d40720300e5000017003000c04c1c2c001c0700 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 816278300 1250 816277050 816277057
    0xc040905070314092b0c0308070e09161206051011190b0417041a03091606020304080d080c040b0c030409060806070905100c0b060604030812101505040b 67
    0x101e460000b03001e200041440303215201c140c9544180340c1000d4058066591792141d001c8042c0c100110040c44d003c00b0140c0280b1100c0010405010028490045040d00384030306c07105141805c005104070395505069100000404074840c1440100d0801602c5a028130b11501400040f9200146050364031f4100d80420790f80705461400c001140d0007440344141602009000402006008174240945c0e4607051506020b45001d07580035a440b0001403104021020400142550150074100c15507101c2d240c400c80d452506c98601c112400b0300301030398408102035a0010240c0100d13204082100d00c00206c4110686054009a6070300c515114200410f2001190b500000c004c5900d02104881c50a40d480c049034003201d620b6000014150006024014101c0c0d00510100c00b41c00c2c05c8941c025050138098010301b1042080800410343c07903d07000050f00320356404055400554101c010780d5034503900800c1c07502c404c4400b103031040c1485810711000b16a0384c0b1ba05c0d60400d041c503d281c9403e46000e052001d500d00e240c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 816279550 1250 816278300 816278311
    0x10911131103100302040b0105030408030c1303021002011505010e03060105100e030d0906172e1e0e0106020607170c1c141f0501030209040b06030708090609060c040905 74
    0x10340320711404404251220042d481440c4003d1100d8441c0d00311720400082e00c1c160222241001414000e00010604002c21241c101180000c0c20b656201541c0055620640c1e0394006035200d03144807800c600e4245c042d0081e20b00040030b6041c21145ca80c071100107460b80c0910a8040d03415900900c0148107c0c00c160a0503505500c242c10304414000c400c1001034540b42e4800908030001d0740074074041140d141c22a034000030182110101204501d09800b1240c00041c00c0c2d95001201c0c01500740c1840059100700110b005440d0560740c6600f40380742d05440a2907208144104c508842003440005030442c80031034813600980d02951030f880c41c5c1500703803a07100801d9070240c030a1104c140200200c002c0551500855500d00840041c0800c0070036100c00e6045215000506c258018040c2c00d00407203201c4100e0300ca000580d0000d090040e00c516407000450004c0502c01c040030b07080780c000814481c0490b0001c2e1400c0c40760406c14200c0d51186c0d960782d02240c455200b40c6010b00d100009001c240100e000c2d44e005103034030a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 816280800 1250 816279550 816279589
    0x615030a140a0e031e2a1b0603060609040912091a07030203030c0c010b091006030507030b03030f0a1b06020714190204180f0b1008151b040f080705090702010911 71
    0x21028555400c20000120450f440d2021491b001c0039045c002d28010070141d0860340c12052611010680030300c0000d26191151000250749441c0761346940c070211b40580c003d80100c46002c0c880707501518001c21b038050941810364041c4184200081e00c0d0448026980c035601850031a00c464480c914150410050131030195251601c03400c1e10748a2155040c4207045c03103603076210340e280380400150442c0d1028114600301820000e5540d120788000040314080d0300e290342942d90b0fa0320039035411500e4480005a600350341321041490024030015801504034a80500b411004022244840c0b41c0d4031080895040340c0170808004d0040945403a500c103480c41441048120f08213030643d540d60005070810700e0111000c08144d002d020b10b8014a400400c05011036600038190340301940c0c1e4003144003600030001e81607189100ba05040c01c000c5201990003c22a01d4005010300ba100c00840d6259041c40c05514041e0000382c0000b03000b14414040da0080941221050001c0c0000d03206000081400f1480c1064070f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 816282050 1250 816280800 816280807
    0xf0f010e0f030c0304171903050310080105060d030f03061205031210030309120213020a02060a11040605180103020c030409050a23040210020f07091409071a030615030a140a0e031e 79
    0x70b08501316440c40003107110340d52741030b940d140207810f800d11048290002c00b80c40c0e00d8242041880c0d111904040f03405605400d00309094200208200c0c0034103d2500001d01c04450070516508211001002d024200900c284004180c0d441800303908000f0780e20711000d00000c503844410064403201000d024849400600340c14216056404064103903031141c811040103a01003410403c07526050310801a442508542c410700c3c2c0b43c5007000007013190040400c52603007100040e1240381c290b0701940c1110124000101603070303203d0740c0e40c401a400074401103070681d070740500302210045548038150700703411004c1000240040076103590f024090015201d8010030158480c0c030100c8001309001300042e10062101c500046000c4c049001003c100c540c0252006e01c00b58000c01091003101251f4412030110740602c0e61054483d602c0200040c0e281900485550480100000740724000341140c201508583c43e800b82c00b00582c851403491803c0312017854041503160424803c1c11990b038103051100c04007810110315a4107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 816283300 1250 816282050 816282073
    0x32120010212040b0412030e0a1506051f0e040903050a0e040906061806050d050a02011112031503010c0e03031e04090c020c090c120708090f0f010e0f030c030417 71
    0x151401520103441311aa5007040104201c4440c1c0c0c41c000d051003914050050804c0084080e03942c00080c0e4000b00007a42d41d0b070701240c0c1131038180d016000038000104003400210408406004202255480d030f000111a000182800d040a016600125501d90348152801344000320499280d030304820441e034001d448020020108400780610009400e00070122200c0e8100d60703200f001200c442d680214081e490002c0307204040b0b14007103290318101c7d80a0030310401d0300416103686814040c8902ea503051811003c070a0000440310540748000446050f002001240e1f50140c0a846840f04000c034150300d42d0040055901c3e6100d18504817800510f601c0c41541002d4a480c91501941d03084480e003130040c1e004600105a80c40c00b041c00f19000140d05210600d0118000360410ba00301b401410300302481003800c0855981d450402c03001012000d142c1c01c2d6114038110015440c041d003041d07940000e0314440c03450305c11807486001c03046901e6007024000640c68207103000d28039201000840481c4801c0d004c0c1e2060b00c007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 816284550 1250 816283300 816283327
    0x901051320090403050c0f010612020f060705060c04051c1211070317030f0f011a1b030705060906010f060504230a08010c080c0a0c150e01090b010321200102 69
    0x78003d512036115152034440a408841c9031058014040040d83c0c107000c420803844288441c0d1080306601a24081c0201e00c13180041511840758000c0201b00303104010401203210b4012001d803003a42c0b011110001403150f54803028141d04400c9101801d41181c0e804814210f0b40908400c41c007210090099a82e03e590300d40314400d00c00701114404415940c00410818848415100c06901c14607550109415505100c0b40300c01c3d603200c05020b0301500400260022103610301109480600030500300703c2e580d41d805071522503101c81d07045d101e8030700b80d12500001081a0303003400d480b8415644980e807080c0c1001e290015080c045141c007c0c0004404040b003060800540b180c0e00484041c080c440004078210841740c1c0024540d13440100001001c0a041c08190085035114240a580c160444450002908403a81103030040454083c0490190f00c4e1400200c1040844568141228007d44042600390003004032001002c1d0280000030004180c0d00100d10ba40b400c109400303076064807000006040501005140c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 816285800 1250 816284550 816284569
    0xc02030c0d0303060e0a05090a080a020313120606050f1e060405101e05040f03121206090e120301050901060c03020f07060c05010e07030b1302220b090901051320 71
    0x240e00090f11000305200f0142860035440d000700d0060410407c51070030804071034488840d03500041100400140740405240b080003513030a41669840c3c05040c40d0782d115042c0100000d1005d013180e0301070900340300080034070b8038142150224802074420480d030100024032100032501d10110540c482c8040c03002080c5500c5a5450206228803038031411100c4021040b5481e03c0c00c2440344c0d600c1041003c110902c07241c841e0302200001c40303034072090390760071980403d005403420301d855856441d03c0d41c60820005100c4102d030b01b1007194160104155082c80007252100b00c885d01c004d019107500540c0c84001002001d20a902030102c00c0e000e441564101c00c8074064150428085038080ca0001346004406c106124081c4140000d158a100c014640c452540c0d841310101e05c4010b010b032105510700800703041035443d28000015091200b0a5032000d40e04000e685400411941c81103074043c28400001500000c0305106580c0034419101d5a140360300350075510195902010444822104481c490b00c08998036030800c0d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 816287050 1250 816285800 816285803
    0x120d0b040e12220501050a050d020d1505131808250507032a170a0507090c030b030312340906110c060301030204020d02070510090c05090105100c02030c0d 68
    0x10345540300381107a01041c40100e4444500c43d0520380b40010411a82c1140c2158441009400e00e15203c9008280307a400134007503002a801c85070705000380548400e503a6401c1105541c0201c0302403100e940d4800008044335009a00c58410100c0e808100001c180c03a00060b01110f038418040d0010744c042c3c1c2c07041850507041e02204541c0e503801680d0078002c218812a82405040d140206c03050751000c4040d40b1030000c40c40e8404e824a0310304001514101c1c1000780310868810760044102c9100c107030340d01e4100c1d0040140002c50f0300024035001c5404c072146004403c0b00d50440b10220300040341e482d5000740224004d0b0b50f02c901c1c420b80114a20100c482501580129522599a2101c40c8000d280c00c60190007104090104a03250b0041c60030170b115642c41005490540750192030041e20f0784075104640c070091041c0003026210b84100c03805841e8003105a0001200f45114140ca41605581c03034003880b400802c20701605a0181240c00071014032442050080e816500080880b5035140b80d034001725100d080c1d2000b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 816288300 1250 816287050 816287083
    0xb22080409270f15090519021c030e03060a090c03122102270d08030618090a06140f01141f180806041101050c1204140f0102120d0b040e 60
    0x240b0414004c2240e07140081c11212942400112446e6488039161044564440071060f030200c0c4480a54035204034025102d401c5004038812030800c0d05000e032101c480b0059a6100340301701800100d11510381d01800083d0f580c081c109e040c0c1141541c0d2400480d00a040c100341c01c2092100444401070013084203803c840303052100050f51610000500c02400300544030340003140a007440100320f10340711000074816036500030071129247d0300d0300030016101d0f03800035010303100c94402c1c1d400f4080702100214004010314030441080050072580c00541164450496110340c140f5032000c0100f0188080402488040c8030051020078081000d01ca10880501d00b03112800c00034650003035503003100e9080300480010302540c40c0100004d24060751000140392022011604000001c2529a5011020000645085511040070340c5454407070011101d050205541180703c1c10030b284202c0850350003c039020710701c1009800a80d14011604c00c418024240403400359811550351000300403d04c80c2031080000302c002100303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 816289550 1250 816288300 816288323
    0x612150f0302030606120618030f04170601060c0506150f030106030b0a111c021c05040f02041415040b03030d02040906030b010503031602040b040e03070b2208040927 73
    0x6061801e213000300718030300402040141c120411030014115520280c1c1804194000c44e031020032074118044c15000d980207020101d00440c13100c0074620b00003094200bc80c2102c80c103a03640c0c0d4044078008038140c0050166009076002c60a65a0300c8120030102c1795024000303205200324007000c1b030f084503241c1c0c2c400ea070701481e0b482c14011400e4090141c201c0c42e0300f102200c14204100c0d0321402d050511001c448900140d40040c658a0141007508a202d2203a00444100924070301814034a03030344000100100d00c1140703040265441c1c4141c21180d107000c0c03050001b0760441c1d100c0010a0100401c40c066910f90315201c1404103600307000302800200003904000c840810120315602d040200f110f03044c0c12451081e002071092814074480003c8103c441e07601100c01003441c0c0d0080010600809010402d250b4601000800710180070038004454058010210310100500112140458030042d00100030030b0f900c420081000f04100e43c2e000a184207101611113510941041d0500e000e44036440300c00c95a00c01000b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 816290800 1250 816289550 816289553
    0x90e090f0d02030a170411191503020301060e010f09091802041a0616020a24090f050109120606090606021f020a05030112030908030d0905011d06010612150f03 70
    0x240305940c82942140003c505003021034001a0192840e01200c0d02e035100403500040c00e001c518504910341c0200644624030103081c2d043d2030151041903001d0b009000d5006500310316040d200c1d10869041716020f40c0c40c0c0e06064181001100d4149c0742c815982c0c00c2040c0c420340030404a40e14810411080803501202e4110320692042c0404e42d503100503070143c0541c1c10f0000380855100c81c400c407101d0340b90380401e030a0381038190310010b0044105900500402da006021f5000c2040c2d02082e011550308403a202c031350f415951500206040340050096900080d0024410040280301ca03040c0b00220b44606c102003655504d40c1c1780c42c0200c4403e0ba1180700180e204107082c007100b1504040218507981148019890420380e44c80280080c841880350702c82039440d0f10180c800b810b00c104006009070000f0401e0340d0786c0b24046c07462800948540c850a651552914101603000204220b00c3c8000140c000c004c0e04045e0b10b003407070680e0139149070182504807a0b10342c1e800c00444a12005e00101030b0030b2401030050340b1030a6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 816292050 1250 816290800 816290803
    0x9030c0203240c0a050318150c0403030806040506062b090f0308090c010804030f0c0b0106030b0f0414131415040b010b090a0902090f182508130201090e090f 69
    0x1030080140050100003000c0295440780c01c80380e0101c0b04280016240381d44003103203032801c4500c48c5940e40901d5180b045c8011074085400400859000e6510400e01351245400c0000715941614110b920440030407080001040700728a4892030022184649400d082000b083c83c190744a0003000c403843c22605404104054100c200340340c100400c64010041b21108000203040b90034081e06c050300307000580c5a0101514071603000346856540c0301130304200782e596548010300a00742e0003411600c00d001e85000d0250a0034541700b288a4500c1c0744c510081280c882200e0310000e024240300640f048007288454000c141000c200701c0d50318406200c0c46640520f00b5040c48480c1c0041038100c08403502007000082c0720759036002500002c1d01e000540040c0c1c1e403000040041d15a1003801401c03a0460342911602c0d080741c61014040384500c9450340b21700755680030024041d003020000000030010074204008508a02d44400c2c0140c4e050748103040c10701702e07141c88141d0000d68160461702403650b907100e5400100c00500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 816293300 1250 816292050 816292123
    0x60d1b0815040c0608043207060f0210090f0c0815010918033006030c05040b150702060409020c060709060206011503020c0c041b030b1e0409030c0203 66
    0x515420700718103410039984000303009a00d48500001c200b41d000100c2c2c180401245204038000c402000203081d89011018900f075040c0c84020544a4080c40c000061210300420541c5120380842d13028011a444a20003600248281e0307405070360303102d5540340340070005040d4405640a808900001c1a400101640b41c2c05a05016045600202d0602040c0c0038248051041c100f00c0380da050404002d10516440103a0307020844080241c15100c422031840c40c010f410f907104009807800344036002840754603681440159042c01c07010607000003400c0e400861441e0304801070b044683c070080a440c5442d9581e08000243d0700143e1070308002d07400442c240501c103a044880640200142d0028100f558503248401800c0c400826800040c55000500d52030342c500e060141a010b5603008008104508000c0b180e049545049045080840d2600c035180900f464002140c1a8000c2c0d00c0172140c3c00c070074003c01400094079100e00101c1c18080c0390618100140e80a010981180d0b80c00c0c08281141808101c0b10b42c0c0a08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 816294550 1250 816293300 816293323
    0x10f051204140109230a08071e0b16030e01050c0306060a090b03040c15080601050f0a0c080403081308011806270605060f0603060303070f0302030d02040602060a0e0f0703020405060d1b08 82
    0x6011020680c006001641900e2000f90027134420824040b001c4010b000715441d115004003862141800c1090041d000e4441003c43e034070395602008110324400105080b244103a41c00d80d4482c40600005400b45004c070000d041d10f00d21442c1c2481003d5070369507980c00315042583c0880d80c0c203807078100c01c0c4a00040611601c0b4281c10907d440c0304a0704001c00040e00c148294450700d04102d1000030342c48600b5025410082105074000d80241d5120360761308202405030818100300108181c4940006035460050103001c0000c0403c10505d011200740f41d503070300c008010f01040090240c51403c180c40d040844502d08a20325030044001242500e000d20401c00382403c8421140e11991092052080c140c80000580b100141d101d846e0403a041d40a00341640756001d50131110200038000500807a031240c0c0450210301400c04110103214190940d1243d6890307046140509000b644410300420140ca40764105d581c2003000174152005c040400d468070810014002c00e91052790f034009500300103414081080c1e00c1b004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 816295800 1250 816294550 816294553
    0x240c03181e01050c0f0a05010e0f0a1203091505040c150c080409050a02070b04031116120b060402040f081515090c090609060301080c0a05010f05120414010923 70
    0x541000c101444940d040c441e03224100701c800b08014001d90020401580f21454003411200780d882c10b46070860203400c0d04400c050030f6024031050141600e600041d1420750550141035225840118001100223001d50941598400d442d02c0b024009180c4e5445020700990090500362213071030906070074031452400554034104014004074140c0100b58410191010340340301510100c0e0ba5140d05403240f01900135101c029002e4540041884100340c2c05c140811424298007040d43c01303400903072024401c9028144284030408140d0220400040c6540346030b141d0000d4010320040c18940c80d0701191802c1c8aa80c1c000708000c2e03005184400d001c4080000480d400030446940340398113100040854440e00d4080c0c244541e1010203d02d003801c036601c19055507850345d800b13080f00d92a90703036030442d03555255410b41182c1e002d68a24880400c055100c1c804040060005464103031509000565540070100c0083c000e444100c042640b6181040c8c0070b015561010f40228424240d0518070030303481a41010740380408080303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 816297050 1250 816295800 816295819
    0x14070b1f0e2403070305060705070606092901090b27190308030a0b221b0801050f030f0a0602090a080109050705040b120d030203071715240c0318 64
    0x200070380803016034075034002d408410001c0b81d82c03401091601410f60030082290080b801000001c1d5800406401c40900802040c09940c2e92002d000040303582c110a140c1400000c0441000703110014005003c6000741031405144055031518000c0d0b03203801c41d040caa030250a08013042d2000020031450250040c5089458a4041651345160130754240d07203100c002c00203040800080c42e42c0c4000c0e0b00421a106000d050810041a003c0d41860b500f4601c00102150310704d0410f50800b01507603004c1c0c84d08034103c507486020300d82e4206410455003501c0f80c005141d051040134100342038520113001e104081c81c46454091386a0703200d841000626003ca4100d0000f03070703141043e55030110741c0c0024000d089810a540c00201c40c031000001c0f880c07100ba03061008480e846a0304003034403003d03896030096100e0741c0f5560b5100b541c01c010310b0790071072221010380d40c008555041459100203440c0207103003004100d00c080c22214014030b510100b8203560f00880000c58580d00003042c0d03645040c400c42801d942d420401c0320f05400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 816298300 1250 816297050 816297061
    0x18100506090a0903110307031e020d091809061a04060b12221b030611120c031e0f070210140f07181e050909060714070b1f0e 55
    0x2007860020300188402d41c0b03d4140034285402581c80d080c40c1a444800d1701c0e9145090b043c0509958008401e07020070f00c1010a45001d42c0c1e1012520304400f00ca140d9514a4640c42d01203032620b50340156141e04105039441d041c4400196041c0710381d4070f800f0341000c950302031510888100001c0320110350042d8240c010401a0002c4800d840c0342c0b0b507a00460f0600000030102c500c80c200c28002000b070000902c0600c00a80300c540424003042401c0890f07105d00000d211881600030380c0c0b5900e014041c00c121011207400b0108007202d0100c800f031944041c6010140144c460f81440003e503600050b100b030004e80000009011381c1039814042c0c620500c003810800e10509075200e8082c201aa001099100b02e05602c0b008101c1081c07003000d26036030080034001d11702d12481c1c44005250800507240b6244601c02c50041000031603061040202d81724101a07000f81005035039000043e11151940b00205c0704454040203c20005200d4086c0c3c58001c0c404000441c61000c01d041c64200118099004803050780902400c106 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 816299550 1250 816298300 816298309
    0x14090a0f15020601120308150a0b220f0608341412010504051f0602030d0510050f010518060d050901050a15061103130608100f0503030a03111218100506 67
    0xd41c49502d403907c018170b070341c03002c030581c8c01103411840f41a0b221644034000202d60309401e0250003010680034030118071040c010301500d4041707002c2c41a0140c80e85400c00400030240034404c02c5030310401240da4040b45104075904c403100b4451007113031000c0c800540c3c0041a020343d805100d01e103100c03140342281c0d880c02030124408113404030148600c610844d15440020000450514485d081d40b1362038149161160f2200340103501e82e0420346030f10201c10315010004075a040f0307050003801190320107442c41c9a2400b140380110f40c82d9000040851000140202d044450f46601d0300429845030103400c0013943c1e0528400c40e60a480c009084001402d0600d185105100405091402100c84505200c01460500301034142103020315060189181d80c2c07010006515500300340e1103445591441d842200d0300e626a0101400f0344804c4c051950994400d01440110074003a6201886560170b0f180c19074140881a01c505104420444105400801142001b2640d4004020307441d5039080f46242406103240560108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 816300800 1250 816299550 816299579
    0x7080306120c03060709290403062007060b01200606010e030f01020313020a050a1503050421030920090408070204090b0c040602061b07020114090a0f15020601 70
    0x1510035410310341e800e004440204851444400c015043c1c07042860a030502400c0d8004a200c1d2019804400c103c9840c0d50100c1d00b001c4601c80c0c01d0051140c02c150454842d100103101d0549003140c0229814000251042000080d1480900c9000c01040c21480035000500f0544c1e40000c1ca414a06414040d4482d028080f4a156110310b0030320b48002c0e00a188030010341b814089481c500b161703510000601040d140950500141c1c0c03802503458003030382aa15001d20800d40c60500c5014480c5150351106070003540720350419a00b05010781100b00f29646007521080104420345200e0002c40d0303584280504100140c0924031107290714090070b20a4450b2000070444080008000811418000681070b0840d540d0380e021000c40303500540030440501c0c040800417250b901c1405003401512800c1d00140c0e034982007003c034000e4400c0d0454400c4c18010694015106070a1402414007015000e024100c2a03450b440c0b800c0b0001c00c141281601030a10b02810071104215108010381150032450042c0009000744c00003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 816302050 1250 816300800 816300811
    0x10e1606230d0c0504090e0f010c08060607033209011e0c08070c030f260414091306020c100b030c0f09130203011d06090109050d030903020f0f01090b010b070803 71
    0x4244000f9000c0c007120070341718540000b00701910b401000ca40242c1e001613018a8040b041f4020440d1040c7c0e001c0907144034000300c4d26150701c480304010500000b446001c08841c80b00c1060840307240b46030f0180aa00410017001c03044550203c001c0b80c01e440030340c1d0150042482e00b41c2e50f00f07130000c0750b034100030000c0c2000840d0744080c15407100020a08200406000b00c00300864100450f06e02444107860110300440d0101c075400c11a0800b800400c100c100700c0c0b82181c007180c039003085a500c0d070100c03c800e001001c60001e201e4909801601411700c0401c4241c0010900c0741050b8011b0051a0600180a011142c0141480303009a001e40c5803040c15489080c440342c1a80d208070b0304203425645032180d9500110308000d0080d0036509044288829210705044540f4520a5805481071942d4010700f80742200c803800009400c6910400300703101c500340a5803003980224060b105603441c00441106091500c1c040540000345a950f0394000e50500512040031405461401042ea280c0310503600c40c11481e0101624 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 816303300 1250 816302050 816302077
    0x203071803020105043003030903090609080613032105092e1e0c0201020901080c1602120c1c0204051014130212071d010504050607080c010e160623 65
    0x1a00c2d000141030401d43c0e00c4807401902c0035106c6a1051800402500d0b616004602081c075600c3d000c50302a0051681c2c05c1551030711030042002d80e46203c03102c400101e10b0603083e000c0c4501d080d9911800091560403071040d81903010085a0382c00d100700d410b446c0500004a806030f0313200d00070800202894103c60000705144801d008905407620040702d804442d50543e90440c21032404500202007901034001d4502100240c880c070306166030381100c1161a229001c004881d502c002001d184c010300d00841500e03404d80d205011543e61400f020081120003031a002d00098066180c003050f0110702d0a401200d0740000d030700c03d842502c1440c024040780c5a4160006251003210303140702900e4688042e5040e00c2d9039408000e8809001d0800100240c40048400690915030400d091070201c030354020320465040380c1014184918004854031040000d4115120540895481c0e0382102c42d54082040300e540c04011080b00c4018481c40c0c0240507144600d015840d40754000640520300790702d6042070640304032054000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 816304550 1250 816303300 816303329
    0x20702030606040911031f060b190f140c100e0a02011d01020a1a091515040203090f0703050f160605071b0b04080a020405011d04290703020307180302010504 69
    0x2170000840c1c44580355854143c840d201d0000c07411030b201d0401d5082030303502080402000b911810f011915125103140710f480c004c0001d40d900c01044c4141c20050084030649810100800308000341c074602d0384101310710009503010144642c10b0b09007070700c14140d03002c190400905045000e9800a0850041c203c182c0020130421410707001c46900130703c50b8014480e4005143d001103920881d102c400d80105403004415442030f00c0d51080280003221905004000300d07000c410300c00024804110107544024081c0005002c0c0c100b151411450410040001c0c40c46400030304416035402403403500d005020390300c2d10140c07042c140c030403c0055007200407108225003040303000c800351110034440054000c56611049504c44005400503100e01c02054480e0000c0c802c0328180181c0c0d9880303d12072030128101d101d01035184400310100340058aa02101e009040c10b031140d0281d010f11804810080110485d80040800e400008101100d64844d181b0440036480c070300010503190440c3c000800d0b500031030003950313040642d54 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 816305800 1250 816304550 816304553
    0x10030819032910110a0f0b0a0905210409141f030b010905092517010b090601050c2a0406150c11120616030b030d0203190e040911010906030207020306060409 69
    0x6a0083e000300000070102c917040d00207850302002c8400180c2042d500170401d030006c6904100c141c0980c0d804103420034003c040b00303604c480004024038480c000202c15110104000240c43c203013800768854110001450384114941107000ca20320441941ea0441c909005210520025003a17407240ca0640e003500f03a0000d101c1c0d885510300c501e04170b40030407242da000704850ba4100b00000000d0110051b982c1c5400b1080d0790700c14208443d82a100700b88180c1d91300040c40d4001038029489180a4240a403c01040319140d0054000510a00700c124004181e034a8200e820851103041c01d0040380014441502c0d21980c054030705034000c0c4413103285034000b4900ca10040c40c0d0401a9141e040103511804248203031a5070b81040345188201c2469002640042810103c49240741d01d0b011400d01e048201c40e401541c508022001c00c490960f000300c0e0760030f080c403000800c070b040c95032901e102d414141403050311920b500c0100c480000d41950b000c1d501c11810180108281e10050701d010581070307040fa2090b9000308054140703 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 816307050 1250 816305800 816305807
    0x803040602030411040f0603210c020904020622031703280b030102040e0414160e0705040f061d0a2105031b071505070305030c0310030819032910 64
    0xa813030b201e501904040c240b010314006a030044049034810304003120a90752400701d10801c980790b52803040100320901c80403005400e06590544d441440188458030745003070341c2003400160705100302c48651105001802d004000c150f81c0404a024401011181141b5000d03002d6065001900882896041d2156a50302e6003803590b00000341c002c070010001d544403604c503000f482c018070007150241c50201030140c0c80385d8080b9001c1154550490080c0c001c102e01400e080c00c031602000040c080504105041100050400c0015541d02c050070282d501c03810501540000f240e402c506925407244100501c0d2800c002503008c5540d01100a048110f0050f1910800c0c10f0950460260618185c107080b400440d00000d484085600701c19249080d1034078200540404045520b8024410002c011070320030004034031485464005075030300040403541500c40342d460340e880314195004021908902d4105460007540302c0d826000d0900003056007014400002e000710440110540362018681c043c4600d00840b01c1039510 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 816308300 1250 816307050 816307073
    0x10507050f030309030904051521071a0304060c1e0318020306070507050f030304020102060a0f1b0923030d0804030c0c120b01150818070f090c091208030406020304 72
    0x48035000e0383d84034079180f045542ca0307911280300340748281c1c9080c000481001445098000304032001d400d14003c00d032480e0704a600000074016110711481140c40003e048103040300351540071442182d4540d103a041a1a00324291640003005d4000c1c400a2811000c0b038880c1207000d10101c03282d51401181c0c000000b0f03503402c4204000c44010390103001d000300f00304180790003000614800e0700c507008980d026030441035040d441c3c3c04182c5000340141c000ca4041220a05241c11021140203c1040054010a60501c00d02400c0c4855040c40104180301800c100400e00c4d40803807040c1d940800560201c00760240b00094a60f81d03081c7c03522090041030340104003894401c1780b6046240c1c0c1d00c40780100500b40c54200c501a05510b40c40201d440510800021a003640b070040444034500d0703140c80d41e20340d6454030758122001880481c0710006a229016000a00a074141c041000814007407100041c840d0f0030070301c004c09100d00d07a040001c001c6500b00880d80015114012030b580f20b50080401601c030348580c0342140040d403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 816309550 1250 816308300 816308323
    0xa120218240301080606010e1008061504090f0b12070e04080a02151003060b010f083103111504030f270b0a030c0e0303070b04020f12070f06021b01050705 68
    0x7011002244048001800c0350203038074262201c070300c007170480001c00c034203005014000c100080c45217005c2000d41c18082501c660003503544913882e0800d80c03268407042c12501a201d00768211510707060343c6440c44c01c1c030140304211f0f0703500d14000c0c0441c41c0c2011103c11072450058402044100c000600c0c400d0b00703109100da0703420a0308940c0e01c0c650030704000740070786c80c41c28045c08103803440352901d011b112140d030003400c0400300814151513402e040d80d940c3d03c44551149041c0300441c16101c0c40742c403940c881003006800c14420b5101e46c07202088881900700491a0542c0e80300828204181c101c10320010940244140200e80c00758504009454029100020000c640b0610303401e100c81c0420005c0340703600c3d800b000750584214076a0300f041030203031040046650310403101c0300c107806801c00c11012000c541c4501005a0140c00074003003040c0380020801050b40d1001081d40d48101c0c0d00840400d001c000000c1010000070045440104a03d0b03410703c0c0148008840030314100d041c44070015058003008000e002401f04d10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 816310800 1250 816309550 816309619
    0x120a08070c0510020601380c07050306101404060b070206030702190b0106031503120c1a13140c0901061b05010e0606030c0411040b03040309031202030a120218 70
    0x14100c0340c3d010350381e02002c1c003a02140345103840d06114000b02d1026403000b020704030f0b2050711078410701d0b05001050b58424400d04650b4003d624000c6082d440400440740210f1603801500c100500d07200f6040c21614040e01d00c14480d900f004d508000d4201043c098407134154044420300e0340c03500c4112043c2c0ca4404a00c034508a0070b680814604d051010b02042507048600d1b5403801d1107030121310780d00441c84001c3c2d4000180440090784c0d190a0440c414003612607250320508812103400e5000d035100c0394009040341c00021151000001408005050b038020b4007030b9500c08000c0071122a91000500e01a205000703020401400214081200c09031143c01c1d800b598005008201060f141a9515102c0c0802c9030414041c4c030450346407801c10304181c1b0852581c56001e41c1c1d407904113420042a85a42e500c040c1050742013104508001c4045045102039405103401038004558540c100000501401c05104481d0300382441408610410308070000704c03440c076074422640682441451000103031118060044250b40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 816312050 1250 816310800 816310819
    0x7061805040209120a080307030e060f0f090f060112170403080d05060d08031603050105010c03021e1606050a0315050906010c08160b18070f090f020d020a0c0b0105120a08070c05 78
    0x6e111040c0c1c0210b001e5001c9130b40a20502100c580780e07595941061b140040d40c0b001141c0003860010341845030039000051501650081a003244c505d034508035080c0c101c2d003050710b0306100a200f004100d411600c1110030034809541490b255460b14402c07802a10f07441c1c42131b6a05c1d00005041c580c0c0d000385103480720764000005501da0600b55007014070060840344041c0480d1601001044560044030301101181d419801405142c4e01b1985140e00d03002200515240e9116240c0c60325442262040004007501c0315681d07481d100c00c1816001400d8031440b001d480303030b003100018040c00203884180031117500031420300340700005940624102c50075110740c0204c040380c0741c10324854108010b12050101c2c01014501200d500284100c07001586940d0790744201240900305880c2003085a0103a044661013801c043c0c001030600c2245800c074410703607208900d8803001030060300540e03080000d14207040b800b4250590740b800140304520041942da07504030714040c2100b200811a001041100240e9001904000d0000340c0c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 816313300 1250 816312050 816312053
    0x207090b031f0e1b1e0a0b040b03070219080d1817040f09050c1605030c0303040605010504180803010b0906190323090c0d0201030f11090307061805040209120a 70
    0x100221010030360540a522412084100ea48203180b400050040c410300e004074041007905440381d4041c0c0000d0300040e0008000a0347c409203c050070041c51202d41f00d66680c42c0c1400000c0c2803d006850803e41500100a20800700d40c8a8050350b1001c0c804020001c0d1707201003820f14007c071300b041200c018618036040c150420001103000c090421109a00c8200c52401d840d030403c00d003901c80498201040301c0081c40303540c0703080d10103201001d401030080c400e4925065100c0c03c260709680c02140d0686042d901d0f10010003590400b0f215244032810fa0700400d4012500700d41d24190980300600c100000d8010100d003020f610b80d00c0404440404040550301c00c00800102009000383c100000e84403056881201c80403c2d418030f4a546031311030040c1e10084c00d610a44002003100c4100b00302c0c800e904040d9a940c01c0d1300b040c0141d11070080404110440356464143c808101460070310281c10a1040000220b44601000c4c151000e030019180b0840740035071100340750008106c2050044c4140d480504c41d6490060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 816314550 1250 816313300 816313363
    0xa02120403021606091232070e0c031006080a0f090c03030305010e1303141c06030507060504230f28091103060d060e12120a0c0207090b03 61
    0x3d6000c041c4030340c00c80c0c4181e131020241d03405102032090280801c00c83c000d4200240c286240711000a86407006000740707030150381c8202c51059104000c0042941b000301c0c1401100840e48500e5841212070f80104e2461602d00094030460206204078014400c030f100104c0c4846440740c204011038803000b40304004103086410140043c50f9544003d8002c2858000041841894208241d101d5203041c00150701001c45a901242c3d10485210880c1c007a480c10702000404070046000c8146940e442c032004034031182181400c90801003140c0c001014080104002c11500d0b40401211400345c3d51507944044454051000c9007441c11207641151f440780150b9641c11030700015a10b8050004200c184151001ea22070f400c8030200c94031505104813540080c0000f418034036069400c4d20b40365104110100c0c140340c840380c4551609150781c07540284a0408503070f07003451000200304d40c1e41c041070061041c80000e003880c001a440701740501800d00d03100e0701c1700070b0035035242c1b02004581c00400701c65520022203001340300c015 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 816315800 1250 816314550 816314563
    0x7080f0303040c0902040b0f09060d02030103080a020c010f02070512030c030a35130c0b0c01090605090105060a03022817010b0f030c01110703021f0207060c0c06080a0212040302 78
    0x103c81d00b4a041401040d24103203407090f0f409440d003040d44c080c5071000c1d421417141c4682010b45d0f0705900c110204844514940d144c0090741c02103114524494440b50015000780c00c106480c4003141c1007000140a8400c42d9a0016440301120025a91080040b02d1250700608503c03c08004500070301c40020b004000c258801c0500304e040b25900354140c5a40d03198404800c01703400300a07a030540751b102400410405049901c03041c9204d40f0071009046a60340e00c88102080d030700a042c0c01111a55501d500209200c2580034003541b01c44090003c105610705100015141411400701a00030030703944d081c042c40544001d4860720300b644035074421010660340b5402810031710050304031000c8950a000c1c646000742000d1115985205008010b005085000d034011580c130a0030350a083d0031840780f414000003584905511800c4000840040e03800042c0180010b480c1c501a80d200c10100589511150007082c049210303c02512002d01d8040c2058645041c0c0d00083c1c001c404d4000c03140c02d80078090204054002821 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 816317050 1250 816315800 816315803
    0xa0804030206130314030c090409052401030b04060209220501060e0621070309060905010606080f041106070303091a040209070504050a050d0f0b0109050a060911091207080f030304 79
    0x3201c00b0341e0b562103010640140c00200c010085940782030859070303201ca0400a9540b00c03082c26061810700c81d004001405841400000392001d030406200300008490a01c3c041d02c00464144008280303500d10b5540c8003030004000c002600d842d5000c14080415500d50741c4441400b4100f0400300e01c61410030f08143c004000a10071140490075041013020030703090079810788240f80d01247e5039840b00e0032100d048980800b001007054007016070715403c80380000c090344102d030304c001d00480c0001081414010b016000c02d6010300149980c01c000307010400041d800200720000000107541440e21410f00345000d402514070140001c020309072148402d5240540c004c04203206074022113400c1090b07168080d041d03a962266004407604006d03000402c0c0600e08007403c580e00b03c0e510560424580d5010b5440c0c01c07189810a811246c210303501c403814821081841d001e42c5015002452040150340c0d20a5038071081c0d032080781e8225018414008404103840400c0c041c1c20000c1441f00e0907501c60104c0c0c268199226802146e0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 816318300 1250 816317050 816317053
    0xd14150a091a4902041526010501050604050a030f0c12142a060924130b040506070224030c070515040201020712140106060905010816320a08040302 65
    0x40e006071441c00e5011075460551504650300f19140b29409020141092102c1c0200c00302564000003040f04070307280304002c40c010103a5a403840030b501200c0300d400e5075411f03449188034520501062125580750251b400072281e0100760324104403010724003282d02005651100101d4044079055406104d40c0c02c1300c90820303007401420780d4071303000b19148962210060200520000b6160000030215420084010044000d00070f007068000040c046540600e140803400100040c6004038001543c00c01d041ca044001c4d21520305034038100f604050125540b40109071003c1e03c0b5900c54105107416481c9070391034054541403864119601d10b00301c11740c0c01c1254010340040722548140d540790b842e00c000035039240780202c2d4140d001e84521031070180261a003121850054458400b40308411444060900c125030041003140c0707510030154a8040058800300c0021b100585134811042a5001d051780000800c0029619015076682210301d00d6801003845000310019400d060000740562403180c229102c01d01c035070711035030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 816319550 1250 816318300 816318379
    0xa06020c15010305060105011b0206030a0b0111030301320a0b131403060f1e010806060907020d0c0303020c03120a02070215040614070201030e030d14150a091a 70
    0x900051166209110203095504404014030682d84100d115120500015045482490094001400960054403100b3710960368107240202c958206944101c3c880d4200061801d541c9000e00805034458908816840b188031042920071b0300c50505e042101d0b0704805000654400d440360785c2e50000d0f50100404a1210904840c00241d24588181c60a40c929002d4064031450303d40c0c0e11841c160f0759014240808805428000d50307042c40c44481501d00928000004101c541054014000c2c4090050840000c42d0031070781408034034542258420100961502d001a07980c507070341802c20300390300507502c1a250710101d0005000b802c1c01e95402a149080c002c840c1c1d8954640c0f4034a0b58030b0305100700c0c4161070128400d91151240c220100700034190080c010704000c0f44000591503518115404821000c400700c0e56080514a40038004486580c4012140d038100b0790400c58000060039024240b2800c8a00d6031254511110200062000d0061030006400d40741c8103c0006080395045001c0c2107400c49104000307 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 816320800 1250 816319550 816319573
    0x20d080315010225030f020402090d030c11010318021513171204050102070e130209040605071d030c061309090f15150b0304020a03021c0b0c07020306270a06020c 71
    0x9202841e100101c0b802d000e0442d502c5c640d0782c1c10343e00001200999120f0744c24000c0342d45a031942080713013031240c0c841e90f220070507010546849241202c403403810504240c03a1200e1003002e00030b451405202507404445a2416031503100f002405c51049880740c031400e60201c040028402c0c2d859071003000140d4102c00b40c035400c01003281100500e0146102e2680140d020b03130b400f08085107010880766080700c5040c0b403c80d00140503401107004404207450840f502c0307a0f0342040007940c0d03501c00c003611030b581c1c8420000344500401c000002d5548640342c1c0701611602001501c00c2104030023281c1c0000500b09a5410700000149041582000a0351001a295034096403900030101010307124032560b22050400e000080350901040d5002a00b00602c00c9820030900d103804005a0b60718022807600c402d0001c805031642400346429a911300740034210150342541030000800607580400c10070f600001c407959400c40001c04544c112a074216141c0741c0480d500854414034180aa690001d01d03c81e246201107600f104001e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 816322050 1250 816320800 816320833
    0x60d1413120c0c050607080702190f0618091b12020306030a1106070507180f0504080d09022205181902010302090301020f040b0408151003060504020d0803150102 71
    0x44800610340c010308928080300e10301034605625203e0180c03091000c41601e85001c100750303a221440c00e42d1411004500340c0d0451038072a1440102900942e03807045083d10300a004d402d80303012405408140301902040815405000e9490002025803000902802c0607400062002d25030500c1900b0001e101c0d29401c14411340d160080b04d02414001d0b00a01140174161910700c2020f00030342d6066403002041010344040340d41000684060402064a903244600c3c0c0741c01e85048a103141d14442e2064203060420000c42c0410054458501c1c64500c08640d5900b1480010340c100321444401d00c080042d16403078200103410b50b100d82e1180103985503010b4040700c0380c2c01c40c1e42d83d821450b80b06412821926102001544070381c0160120b40700140015043c00b902c0640401c0c03c0d040354100140820300850100f1040fa0100480300c0480b0446000102c1404e086154401d004521301018010310b840c6c0e00858119101c0d80110b00c0e9164000a420341c0303078100301307104a00d000c003400085401403050442d030a00116a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 816323300 1250 816322050 816322081
    0x14010503090c060a1103130503010f0e030418090c0605030702100603240f110910080403142802160f06050711030109081c050c0f04030f11060d14 64
    0x10000c020b00c40d1400c01c004205030350344070009050030080e142a0101310103000300040d2460b1009000908840c9060005241c215107804c2c0712025001d06040c010700740d040303000c42105c040d20080319000f41048071340100702c406018000030080030203205100006800c0d40c803c02440c001d40301a4280c80c004228400c0c00342c166007050002520004031900c80110340d02c040c000b68406004134100114001d004c0c040c1c554100d408c0351480c104e240382c00003000f0000346080c03810b1103107454a81c03c040d1410306154500400f08102c078004400d26080024541240208030700c9105500350844121201003180b0060003900c40b0f1a8140e031200c07a03240e089011920a401503110310076241259625400e149aa440380f072200e050104070a5095580c902d00980072800c800b0050415110200043c550100f0b00100036045580c01400441051001d0003052a405080000c4030202c7c1e07081080e07070781325089905000800384c0040d10400d510180010300b0490003501a000b4540001643c4c1c500480c654854181c03591244 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 816324550 1250 816323300 816323311
    0x1103090a1d0606030412080402040b10020705030f161716090f0c02120a0318050d02060405120a0504030308091014100602031c18080301061806030c0f03050703180c14010503 76
    0x7000984441d103461f1060320a5548140002c2c800304003440423802003070380090606c00150060304103280c1032295080800808840000d00ca000b032842a03024000220040b885024250550140000362003c01d0400c1000610b0100000b1415002c2903540002000404041c0300005a41c2c4c20801003c6580d80045001d00450601c03102052400c4481c0e002100184100c489506a80404054840110300d04105108200d10150000e09003070802d400c4c85850169403401d41d41d283d080800c20351700d120340c3c4913007a5400c03207500d03041c0445a6221340e41d0341c034100380413809120b0710145428074489800006a042c5409156080e140200b8103072681d10891b03c0c1c1c85001300e40c00c02c05e40c4a15041d140804030b544039011004c404e6051701445007680e0784402580c0d00a074408000074001c2c0a04e62840210007466100501c22030404104604640c40c1c003402621228452506141e0b4401c0000c908901941080104040104c1e2501610074039281c00d01012405000d14a90958035101c0200294042c6d01124080d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 816325800 1250 816324550 816324563
    0x90f0f03070b1c1103220c092016120302250c030f030302040807060504050d0308090c060a030e07050405041a07050f04032306010b09011103090a1d06060304 69
    0x603400c082002072035a020078610440f04003148141807001046115000280e025401c1056032414540c0306011384d100d45a400355841d00c44890715030009507071440b8080440d102804041a00d281d10340b880d002002c00d00c0440c1284410001b40017408110b200495910035224a40100080700c1601c8128202d01801c1001060304000030300d00d080c841c03101848554524440c068131400c2c0e40d1a561054101c0c801584100e021a0700031405001c0300fa01030040201821030703482d005083c18602400501d102581c1c141c05400e10a010b004100648070074000b1407180030300502840d540b0003c152008004044060315070082d8040c01c80c0100c0c903490300d4010346008640203000c88000c035010440b90210484003426540502c04200303d004814074150000d800194010010072814031103a11801c040365107200e0f08590250007000040c0702d0705011100f9546061028680302c0d08403030b01440200e280d071203541125a03000848a03000103806061002414800300c0c0041c111800707803503003002c0c480140000e44005111 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 816327050 1250 816325800 816325813
    0x70201050108070611010f15080601050d0807021c080f0409060f080c090a060302130518162c0405071a0702010e1003020904063203120f070506010803090f0f03 70
    0x42d0b21490000242407100c000000b80011504051011242c2c5503075000c0051862300340410a010003030142900410041d103004005409587d40d01d031036889a00e0009214081c50b418030100c03400013224400526900030321041e9261000840f603802134000d44030b940e00c014140030002c02c00c0d540004c40078003190301c0403000303084c400b5884040110b0302200601c41040155a1070002000d651802c0780c44d210000002c80010f05800c00c09100c0f84c02d6000000c0c80d5040d03500c0040c130300f02d2103401c1c45550411600035040c140f5046491041c8140c1c00250740700704404246d524000c1c042070000c085010401c60740d0101000c1d01025501c1ca01ea05640191034029010038900c145140d020f003020b160000320484140f800500e0141814001022502d844e008040d403648025a40304020410f070031ba11410780c60000505e1603024031030380042d0755103403401100706020ba808240001c0c0083c5610a81e030034154000183d400668503590501e03aa034103c071644a101c0c08940700c1e002c1007030400b19100070b0701c1d0783c018000c0c000303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 816328300 1250 816327050 816327059
    0xa0c0903110d1b180e0a0201080a020906120a020a030b180406020a120c020703050d090e2d0a0e0c010503070e090619181104081c090e0705030f07020105010807 70
    0x7407141c01c0780b100380c601c0f85680c001d0030703601c1c2c1c04620460040d055605008681a00d240c0080d001ca52030820001d6860388201d00c0b00d00582e800242c0e031540441c0b0410007603591100e40001caa000d004650508680310610014440591619006040d95881e1590308100c0c414440c01003001c801410145c5810215015020130301103007035038001348000d80321030402004c21f1000119100444114900d10b0300141c10006c810b00c1005000c1c04201a0700a40d8900601f20700d003800e2103150104000341140d40c1d0410f015907142650b240c015101d00340c40810070351003000380c949800030314040c005008100c042030007003da0151066000718141d0340503241ca80c0c1c03401c07041171812080c0014203034003400c590780c088414800b000f0b1301c0c0c440e40018005440031404440307021003908005c200342e804a4402988200c2d050106000a00d000501e944407203040404c07001d01940c200b0815100c41c5915000300320440e034100c003080001508038004600400445e24101d103240d903614002c03802c852080c00f40130710325003180302e0402 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 816329550 1250 816328300 816328309
    0x112060507020114090a06050a0e0c1c020a230d151d031c1503080708071a07260702120a05040f0806071b0b01030201050304060912080a0c090311 64
    0x241c1c0504035000003c0c2d00030410701408807060003102c2c80103550740020020001c01007280256500000c8045041c8106002003404588990660004c1070003010404200417458050012119a00e9009803801c500030f600c60f420507080042c040200014071a80300c1c8480317000c2c249280108800e5420001000c0d8846401c14020701400304030189a18201d0815900d04200d001840181b00d04000120605130b08200d2805080c1980c40e103140c04081008400004c101003500c0030122410b5540c442c01040d954074491415102c3c08462100d0500c04140c1c00c01001012900015562a030340d182c1c03c1e4007070901c1103d100070713420003504803025001030700b10f080156038101c044030141c581c020f05402c089040944800307040004c1c00c115808031100b03500c10340c207005005070480c0080f44548101080c006841c9099192914414010712001b4100000000000d0034098182d02500070036910080d03085c0c40c5555010001d1024405484141010340b0703005040401600510100c0d0407a58406e03050900c804d03d840811 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 816330800 1250 816329550 816329561
    0x6090a020d06050702101a0a050901080601060807111005150409022b051b011103070309050d030c050d27120f0f020306070908010606050a3c05071109011206 69
    0x3100303520030020201e070b00720b429002e000300840048103414446184d00040002034231581d44405e0140d010400180221103001c94054151240d90a10030329580b80c10000311100111103241440760700546461129040260b04100d00668102d4025000c0781001c80401007103454002c0000d5001c0492600207484552921001088281c1e02840c00c4500010361100d906054200400400c8000352804140440d80c000c00c3c20300031a07044400940c201001c507036000d0203a419a0203054031400754031407000c0406100301400542c590b0f0000a0b02e60815120390080d1110703000919410000441c9512140c1c1d11551440180c1107039200c0b01414000711a54440c41032200041c001500c2c0c2c0f00080020b0405070302c041080c24040c03040740d920780d040309103400d04450840b011904118200003080151140007640806140f000405120f04000c0401c46d000030000c00c2814504c0c600c0c900c00250f0f024131705030350300140a803090b24000e0b00c80010302d50119042011100302401101c0501071100c940801055041c1c0c080c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 816332050 1250 816330800 816330811
    0x507030f21021c0203130b0c010c03025d0c0c0d030b1201090f05010509071d0601200d090801050108060720100c0e090c0f0706060e01080d0206090a020d0605 69
    0x107507071034003185c59070346c128482c0300d40c00c080c1c200f010006501c812030742d0900c1400301c03d404500c0e04504001d40c031440d120001042104082e814603c2c00d10b0194509000102c1002c13000540c0e0407413200d407942c40c22600d010046201d0042043c00104002a03146041000301d84480c1000700c064008140c030b070141036006140340c2c03c10b250011a20040381e1004502481070b0300c1c82c240100864402120685031282c2500e1000300f070303001590400c1808100c02e180b14002036101c0070702c1d81e82148240c0d81c0c0760300480c0c1d00d405581d40c0900107103440302c02c001d4111000c502602600c0d03290395841a0300f82c403403000500380c030300c04e101d19156503014000046086124908ac40d0b402c0c400f00c40020050020090200d02e09a0020510700c6060340e14500b900f02c07580c0161030003150030b0051754484000d00c0c01c103950001c580284661016151000100c44080080581c082c00151207500002461940c4400c45d160f81c5402040203074016100c1d801c0460801d900004241e00a9940100400071906a554640d40901406040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 816333300 1250 816332050 816332053
    0x301140105090c0c010b370522151e080a050322080312180606010801060e062203172701032903010c05090d06090f0507030f21021c02 59
    0x14202c555075220018201215448200302d0341e90141c51a241c8040d00040da2422184512480201b022703480380007004181c0788441036000c010381402c4e0101000b40c195645010700200000701e02140c01a002403e040c059030f05095181070042c0c4a0320b0003680c1d03c1e2820b0340070304964800d000c0d0003401101c420100142002c86108078035481e0f601d80d5468619000464180c8001041008014061030003140d0b00011081f9030004004c503042c0200081c1c225034040c09103000700484e4070a426a2921480c040b142c5175400b114804550035405140001002500c0c0000c5400d56a0030070807040884200040d42c602d0040318085400c50a082500d0084440d510800031741810b44400c00c030780c000c0078141420303440a80f541146000300d220410416003101e91800341d284c280301d0280201e803401e0b260031000610317040c0d209030006501c2400703050903410011002c100400503c00c210022080040c03035030144101c144900c036003507001030a0900a52809440f0314040d030040e40012085803d1241a0150003004041d070700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 816334550 1250 816333300 816333311
    0x512160b040f12030e0607030b10081b040806011503201c050f0a1b02071206020c01090516080d050702090711030d0e160b07081c1a0301140105090c0c01 67
    0x3980d43c04203c40c0c00c500f00c40465034441d1004584a000d02c000b41d804002868100b00d41e2000394001480404500050410000c00800080d098040b05902001001e00b41d1503450b100c907600e02040c2c1e1350311403d00075003a458540940248659000b401122468400c802c104087d0084008404142d03422a9210312081d090500b200c814040d014821103010340c001d11081c1c0281d2500c01c4805d020303603502c02110742400343c0c020042401c007580810542c05070707840c60103407011450751410724101038001c040c041c6045518200d01101003003000501c010103083c0000f8003075112580c4000741c1d030701c610b240060240070030f05c100320724001403400c01c61003030380b01d105410b1940443d2552484e86107107030401e481c034100361517882c440ad03049400100040341e2090360b021019000343e400c01c611203801d402440b000400c0c001001c9403201c445600401408140d5840c00400c01c091000c4003c9081100443c4103124025481c01440143d1084264242d40c180c0b4006040c850184d250002003450b19030141a00e00800c0d540c42 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 816335800 1250 816334550 816334553
    0x106080703090b040c2606010504090f02031c14090d02010c1e080a030e160303031d060a050a060b030417031003080c010510060801060e010f050403020405040b040512160b040f 77
    0xc911600840c010f460701800641010070303001d880c001d09107211000030040008030501e80ea00187e00c5040d070302d09807030210703040d80e1a18200701609810356000394940122040707002040c90140c2c2152074140c859503900b09050440400220034864007a811b600041c07060204009035020b40e2860305800c0c0b06680604021010100d40b18620400740740444981c000050000c40c4154980036040070380c9644006008283c4100505181301211444000e0030326840d8084420b803001e0240c05844600c242da8203841c140d02d0925000401000101c4058038403e107000d001240c2c0950302c1080d2840307190f014450740c680001c0c46c0341c1c050842d00028566101c040c0e24840100000f02c820014111401064002140034103104d1007140001040b40c0014040109900040180d194454034690700300ca428200341c240000c103091304a80e14851030b0800b94100341014248000c0050302c83d0b20a120700c1c00340b0150ba002680410381d07c02c040c030940b80002180290403080c04d000c0b0751407259054005109001503034001259 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 816337050 1250 816335800 816335813
    0x60d0b061c05031204060c030b0102070e07050415180e070c14030f0c0109110d02030303130611030c0a0906050a0e0906040914030c010b06040b04060302130305010e160e0f010608070309 81
    0x112004c0003280c005001d000070400a4001c090305445c0c04d04040c090b41e016800001d546640744c0c440d006000c0544004100d08502880440d0b0240ca550403203240105036643c4c0c081e000846c80003c108407501c080d00f0000e201d503250135409016a9031655003511500c03458450940741c54003075992048500007040692001c101b01c400900c421100c040006c22490741c242401510410310894040c005d0900c0005900180c3d0080112980413018051541d0303e402603062440040500d6280e240f40b41c1c0001044c042c0d4a04184042c040c2d03043c8035a45c1c01141034460f0001c40341070050001000126404800c0c1c4600f0349458034440c2d5000c440500300154903a9642c54041c04041001400d100c6600006a0390741c1c2d48800307002d2018805400d41d0024946850800345012601c52885101d080581c0807824100c9041c2400400005680000083c440100c42640c80d0340c8036459001e1030b81c5500c441d21000070756012800145442420400b403642384517860454140c441510080680b0304256680c0d0040002408 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 816338300 1250 816337050 816337057
    0x112707020718090c0302090408130b0403120f0801050103020a120504061b020601141c0b0709090b0a051f0203070b041a070302030f041b0317030906060d0b061c0503 72
    0x810340e009081140c80c05010303803000104110700c0b00c0310605080340c4201294441055400700c07541034900e10000c1c2d44904120341c036809000210141c0804010740080d01400c1c1501400036280a946032001c8000001003d40c0c800185da4944004104840010070182d8002d501500b80d400c0710381030544641c0c0c10a001e890454908881c11552503170b4618500b40f643c66160801c00342a00740740020212075040040013401041600c002c148a08404181b0307030102d030190f0060a450680c082c80d50440d9050000c030282c100074803070244142c3c843c034101104196140c4a41008112071002e003140c0311284030782e0020100b090488542d503041d480100b09038030010300c641c0030642c03145010720210360070034204440c0152040c1d006410281050300510034040e4640c079000c016a0460342c4002c400c41400d01001682d001a600707a440580031240d514240101103213032030000c5200e00302c0c0405175911552030b5401c0222070140e4000c050145100c00c0002159400c044481150445000c2c2110701d00ad11941e136258555072 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 816339550 1250 816338300 816338311
    0x81e040b0c0c0f100e060717060d02030307030206070e030d0512040303021c0f18021c0501061e05040617060a0e0109080408030d0f061d0604230405060906041127 71
    0x2444880138254104031407040182103803290004e0403071810005c1004060300030007280c7e85444280034002c601e495849090880d40558068241c0751a2007450501944920701103c42c003010a16a0035600712510380401d040c40c0c2c100c2641c80d503904109016002c0311a5038002401101450b90030481c500c001405071b05038514141ea071044c0030505420309042030090750b00d0070101ca1300c0900b6400100006a46000107003640d1402070503c2c1c2121065801c0150151031244e120721072207141203815000c1280700e4070b807200644070190b4080c4005a44d130010200705125044203042980c0000d004104030740c246030400b160803030301d00c2e0022130740c10070b980c0307881246502079030164280d40e10008542c058001213010718840c0e18003907a01046040d1510b591003040050004200d52020018000a00c095440b617020360002000742d542040d00310b10030749268000140692342580c0c240708a04c009100c9984c00101180709a07403000880e500341020324107101a0012604401802203844030665404071802d80100c0c4c420b4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 816340800 1250 816339550 816339553
    0xf02132d0806040c0e010b180a1a0c070b07020303031f2411010b1309051002030406050f0a0b101409040c080a0b0d2109031a07081e040b0c0c0f 63
    0x1070030145020502d134a81940300201ca4051240100a01034018041c0d0740f424506100b182040c61900000030140d80807900010a02c000e0824080380022072a00031b42041305010044807d0903072140580c04542c0100c41009500d94030402c00540c604000603002c004e1280600781c10720115484501c50300c0301c1218aa012042c40f105200d45d91105035004084203941c04c00c030b07002000714dc00c0040120700c1c0f0071800c03841413455036102c81c000001c2100c00c1010340b800700f044201c2103450341441d14003180900020356049502c644024007003001c0079030a01c220b10b503010004018014802c0b03c560103444070070002c46240c48200b420302060580351034a01401580c0c550720380d070f030191510301003031105c0440c0c1522403998002d03560100c036400007034004280a03680c21911050034194542c112021500e481e09030308000e0500070400d0a40c0c050036400740d0540e00460068503080c02d140e80d4504021a16403120309030030764011001000c5808034011140740c80d08a000c8c0803603d464154030541d16480c11101e1410f90005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 816342050 1250 816340800 816340813
    0x20f03070b190305070c0f0201141c0606110303010e06270a09020a0b0a090b0f160c030201080109050906150102010b030d0e030606011e0e03070513020d0f02132d08 72
    0x281070740b6200d860350004050070301b420440303141c2d207640d040d40484001c000c1c14440f00108a061f102452001d55010014100681d90308407540b80c2e40e0800707092644202008030b8240300341031700c0d182d402006036410b1b14420594020f890780c401c82007120001c208035170414280442146650300c41c4048100354440d802881300400c2c044038500c140142100181e02900914805104448210350b0006260040f0340200a4464403690741d20218078491081c903886014101d42c003602130007040003502006049900036203d2448076030303940d5030320000c0e21411070b802c01290300110006401c842620010b20042d4a061000040d001c0c00840400d10344510041d175500454001c90000d0f4482c941040035903480f00080c600742c4484944003808403041a5083c445405001001d110440c0d281c802b0000c6078000c1000a0001c800072054034020790095001c41c10418105041c551483c2d0031000b18002c40300c1c9640054181c0300c10350b01d40100c400c924075124400f4996075106103a1040d00303ca400c3c01e01006410032001501d40d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 816343300 1250 816342050 816342097
    0x50703090b06010e0d030c2a090606030605060a0809120412150e0303280204141311090f040e060403080105180601020a0b0903122701020f07020f03070b 67
    0x3040315000b07140c01c0c100442030007900365a4071001a81040c103503040c00e00107601b50082c5442038a070f40a414000803402c420a000301200c500b5800e0300411101072941c1007121a840d04411000e46085000c5c43d03810840c200104010a4440c5600e1079001e040b08007592607840c000a881d01080d40143e0280e519211004501814464180c14154085004032410000c0e6411254840c1e1a40001005040d0203007620303030801032092504a40c0d400030f10b035000c002c40d904c5480700740045c1011040e0700313000e0007100f40780c0410b11899881c0c803440040d40d10701840d9a0800c00c0c0d0f0310400100b06503084c030a40c2c0054650703000010108082240b540194400e40394130078598101802d005c094040807004e408c207003000748240000f6903000b20707070b440005400190400081e40d88000c003074a18814444d2460750000f418041298542403114803c1000703c0c0d01280b45402c544498400c3d090b8040c181c4594030703040301040300b1030042c5400d140c0289203040c090190340c8095a81c180106d080e0b08512802c03aa60300d480307001c180d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 816344550 1250 816343300 816343313
    0x71a0411040c182907030206100e1b090411070b0604240b03070302070f03020d02070503032a0f06042616351b01141308070605070309 59
    0x80d030350680c07030450001c143d90f0707120400340c10441c49a104c0c8240d12465500d580c0c90303d222800c03814150301c1d01c4560360390142c1c41d000390755050403907240000c5a406400070842c1e10001c0441d500602c0403000100180c0310740e215410b62030744507000180d4465a01c0c2540f80103c2e1007800a0803070f0741c3c0613183c000a1071a0440500c400d503861a50311847d010204019003503680d0b10b105440701520108860301c3d85075510701405400a04c14a03002a05181c0301d108004101035000401d4440314105500b541c100340d544105041d9079010300558034006002c03000c0d442405035489607009107030000a4040702c000c981d141000d541050303000e440c02d85200c22180520f01490a0401d80707941000d0f000d404d09444d0a8410101e0a9500d48011005081c01c004013103030000000b00a56914032070070700da040c030103200d11018900300465100c01d2040b403411005420745d05040506105140008464004100344c1d661040c002482d0900b4841c4203c0c0d00d80c4040c0442000301b0200d102c6e180c420392003900c0001350701d509801c061 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 816345800 1250 816344550 816344561
    0x61215220c031b05180910020c0309010e06030907030b1f0b040801050919061a130b01030f0b0a060f090305030412020118360504110a090606050f071a041104 69
    0x40507520342c240030401c40d22000c045003410741c0705041c08949516442c42c503509010040c04801c100322300120381e0b11842c41010004049400c1700340c99140e5243c8d152014000325000407a00b903041508103100410118102c0242c4079840b0f10210031101170700941c8680d02c40041016049180c004c100030900340003e41c1c09104040d00494240010301d4014416101c050a00255040040645440303401002e900740314a060346e010110010304694041034150040001019414284d0340000e040650012031081c551085020603c0301406400059040040540e200e080303031034030707401041019040080421024001360026042800e0344040c3c40056000040c2030640103407c0004081d9020810000100b551516450230400009104102c91000c2c2c6001d4582c54104c8000c9045400c11007084100400e07001400c5008100700c0c0e51940f400d4513503076110700304c2d0880d00461020480810003c104d100702180035010661080740442e6800031540209c001002c82503404541200d10840c50655514060044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 816347050 1250 816345800 816345833
    0x12010219031b05072f030d020d0e010306030b04020f03100c0914040e07150c020909010f1803020a020f040603050a23010c0c02040e120f0d05061215220c03 68
    0x4d0400c0f5060721014150405d94642c0c0a0795560880c8a0f004209551400c2c41401002000d5586826004001139110b2403000100340004940c0b807050b03510b0f98000e00c11103095940040c2018855a40c3d41d003800000040c0035141c59040c8200f140c121a81c0c103d0380510140300e10255a400192071070b114400601881200d02103220b64188070a522880310f0004031001124070303981c0d0741302804080349802d5403903141902c0d0194022859038204a0507044c1500100548010203108100d51502000491600a5503000050040c1c102c0514000135150528828800880041001a02a0b96035035601d141c80c980b420221000d94030740c000711a0401d0341c142402d01408820b0002d1207044403c034001440e200c01010024030603990f17401301100451007001080080c5501c100700668400b18454400c81c141c2010b0917598519090100017045801c140d84500800f0898030014240c2e030102c0d042c0d941c2803010081a442034a0b211006421800c06040b80c82d91609018050180049081d818a03480503410601c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 816348300 1250 816347050 816347057
    0xa0b04110a050702010e0a0807090501150507171c050106030c030c0306060912060e15090f030406080f250c020a09050606120a0209030601141212040512010219031b 72
    0x210704039240c100d0115210380e41e0900c4d040c2418480c050010710101c1040c0c02c2141103225030b01c808502103240e0750046040e01e07030044001c04d800c11291801c035014440d5101c010024107214000d00c4003200150040c1c03603c0000c4188a6590095020720390084503802da001c44002511488403a04054142c442c0201c065010f05e4103020b44c6081035006401c0100c6407080d6080c4480c0c1410700030502c003ca034890440455407005403501d07460003002d0189803c07401e03034054030280900652000081c400108540c21105145c4070f5070360301e596414414080750f000034103580c4001c95013000c10502c43d80600380c24621012540b5141460600390041c020401c145401001c0700615080c10301c40c150352500269860402c044541c50504e54032400000c021340151845c0c150075124900010641c0196011303981c0d61504103441018204004010b015661410388540e948100340c20482403205080c01c05400ca0880b02c03c00c005441c00000d040b2001100c0713403601c1e0241c00680d469100054074004041c94042500c0d4a04c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 816349550 1250 816348300 816348307
    0x120207060b040b0901051c17070311070b1e090d02030703050105011a0301181d0d050417162319030b0105061216090b03090a0b130c0b130b030a0b0411 66
    0x50101f004500707484041401851900c190604000100442040e003480c20340c0d186445119a18003d8007402410a40343d83c203018040300410b52480d01070594148030b8180119402c088010b58040d0442d600c441ea02d141c00025490407400941c41c00c000b0380c0000d500c00e100004107980340c5864540700c2c03000d541d00d09070807810030001082aa11b1001c0c070720100c990060000507801178000b85424550034010031680c014001c1d06c3c00188000c0c5c00c5400b5200b11510b04080d004200c0c2c015902036120004d02141c10503080c84e883c414000360300d41741031070a410032001500c5006440114000b42c945d5210b102c0101a00f08021030520801c50001100303401040e0a4a03202d0034100d580400701c003226401010810010802240f042905201d800054018800380712625a641402c80b4079684613850900140d900c0c0c00e0030000700b44880c0c51200015203464100c00006585070504801500503803245ca8100c140400405021402c2140f0303400440c0250a140e8001501000c2d040500c000d40301044190800c040051 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 816350800 1250 816349550 816349559
    0x191d070807090b180406050a090501030b060907081303121a040605060705070605030901020d0203010303020d0f110a0b0901021b070602070501051c05191524140a120207060b040b0901 80
    0x500b904c40103080c400e218803020a00c4004140280010780c06164460700a02c40016004455800641030740d0049030074000664a000501c440884161602d01c00980b50900084800223003c050060840c464035000600c100d01410705001d94010200c01ca00d40c00b4001d41003503103032616104000c0100010b5440c64201038180d240c3e59100c40e40c0e0300c1002c0034004000000742e0f81d02c10a50441e107960b2204107085440396103d0400030b640780c500e088910301107000003148c0007180e4010b1a221a2140400700184040b0045a607400d0603200040d0100141359000d007d641c00c1c00f60b120002450043d00e400041c210355207024002486c00000c0d40c000741c180081081041c0005c5140b40440700c0390140d0351300200d65912800768460000304252101d00ca41440c00a8042c87c1c0b58031000d42c00f04a81d011b400415500407a181000d40020350800802c0110780799101c80d8056403c10006443c8500e8181400c02c903800a13000f4020a0340c3c00100c003211455541c100090cc9480d052242c4220070000765652000c96040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 816352050 1250 816350800 816350819
    0x60e010506030705120c031e0c03060d031211030f070801080d052115030c220b1801090204031e0237120c050d050309191d07080709 58
    0x60180c2409220000006062980654201c40c000d00c15000680e071289400503d0322602c1d002a1000034542d001c5200302c80c0c0d03118070140110b010300c000040291568807144c0c2000a049010401101407000400e40700e004501d50744101102403555013103250356031400005a280d0158020088024001600010310260400150812017020242000b40c1c3d00d030040d10302c0c3c6107140158400f2942a1000f80708100d1540018030345c0082c0e0b40f41c15030445040c01010320400190000c8050000303007500c0c801c0000345a04003c1e401103404520081c1500a40410075601003009050907044040312a8002030300300100700d00380ea05580b07564010f00405d5100c05040d400148100c1c00d0780010780e000400100004021048004406c5803800d40024003c0d8540c0d8030061092007803406402542d841b4051040007035181002c14032000100d030b10074095483c1640c01e404203c012807001641c01c0070b0b50460300c00410034840b205a100c4040c0da211a50b000b07035280445004042d604000d0021042150500703041058420703 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 816353300 1250 816352050 816352079
    0x1c0b010206012d15120c09050312092b030806040516111e07050319080d0207030207151d030f0706080c0702060a080702010f0603150e0a14011e06 64
    0x7030316408405205060540c00b1007550b02c580003c04c1290506407040c610319004100340348150440e40062101d121164002e58400c0c03007130b200e03a903050b81040c00c0301103440980c0d100a2035031030002400030119813400c00440144039428111414511202206001815040f01045500410845090002e45071200203103042003a980359410134003c61010480014000b4800181d01000200d010941c1c488598451f0703503130b014144501030180c051100c0317590382c208000d204441c195400c6105c0c00e1504d850610868000e40c4518004d400314055500c000c5546480b1000c1e591000e00d59035140074441c0c040580c032020302052502410b00c0390748000c1203802c402201040e000c0841e5a42c1c10078250b80e680d481c16114903440f622400a501250000e4010030154211704002d0280701300381c0c0200410b19036519042d041f9082c03800090030185d0380f6881210611a245c108a5171041c6103802c2d2207100180750745240c800b103400500501c0c0c1d030351140c400504410250340b0075011070040e03035424002c107032034002644104103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 816354550 1250 816353300 816353339
    0x1e0f0901080405070503010e07030c0b0c0703080d02040e0f0906090a0b0a1a030303072c0a09021602040e0d020c030105062b0b04050c0406050d03141e1c0b01020601 72
    0x30001c0001c003842810b0184d8002024003800074080380c8803e01015889075802d010441d41d07546640300c0440c020003104156414801c1c0d060003030250a04644524a60b80c2051407440d0206808001c042020b0402d01c1d19140980319064441c80035080c021241307410302c04001d000a0090b80aa201350010680110b0301640202d040100011840040c4e81503808040281050f5909440004107001c120341c0e2200321469a0b0710000d50481d14841c1482d05030503911610700e40c19600540e9140e003030003004c074103900a107040e145000c40322444902542c041000d442110080c0d24a98002480300f07070f44a50148481c4c5584a0100c0c020061031404c4400140d95411200300b110108030050f100c4004501c4080d050000035070041d281c8001e628061914580e20075285001c3e80c011810300782d0005850615413003503241d05a258a8024404001c013403402d240f42c2051404108503803140c0050110641540c0003007201d00c03a2610303110100b1008010500c05e5840862915046603c5803004000c01d61420a900b0b0b07020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 816355800 1250 816354550 816354557
    0x207020d02040f02070f050c010215070f03110d090f0b1302060414010203120906160e010c1202122107050f07060b220b0f0909340b1e0f0901 62
    0x41910f036944020302808000401d41d0041045041c14054002403284103518241e084850507080e107401720040320015280c000200c0c3d080102e0200641c0250805d00702c40c0e80d00c00f2120305242151500105540d2000419184410405809400d00c141344100c00c0d44610203844014a414050340480d085118904c5040314801e440070694040340c0c42030080302c9240c0102e0f4103000b12400c00443d0203860b281c00355038503150900303840c4c4c00d0a50079010340c00b032130049507050319903402540340c903203540c030a1011084d5554214081c0700304a034030b903a40e2900a013060b01100c9030840301510310400403403180c01020b00b1503000c0c0038085c8591004904503000300c030300113a0b00c2040802d08150180104d224100c1048190600c402014400b91030106154414078251004540c55541400c020092040e001b9061b15141d01c1500004a0901d4060045180c02021503190408200036051207805006510340c541140807412400100118040011000b074a0304c1c8000700c0031685001746901500d13045218902170b05052 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 816357050 1250 816355800 816355811
    0x90a030312240b0f1201030c080c0108011508070e12030a110c1507050c0603011401030f050402010801090c18060207050a091404020409230304091503051b03031306020a0c090207020d0204 82
    0x84040c004d0981d000c0b80d01100c0b464549585904d0716905540c2a401411a10710601001243c15032103100d5070b50403215600c8090f02c0700070558a049807401740c0181108140a1025200300b002c0d2215482246c0051845000e152100c4039060020030b13001c6080d10f03041099009582c03c0711380c0c3da103000051a2110000100981d41c081c3d0303181c604d040c04080c61140b81d2008001c0700004941003184490414a40c00f40c0e03040015492001c111811200140c502a0000e11003100501c04054903a004018442c0582000c10680711010300690b2500541e03085000141c101503c10007803420400f0801e806001c62400900200e0080e103088141b100000f00040c2c03295807144030380014000d86094041c0c048035032000c00c0315568245030710195290b200e80705d664417151030704100f5030340c0141240580b01502c0d4804007802c0394040c00c0390464102502a91215498001000780c07a0390303c601442e00c94001c3c0196000307000591168105001403100c990312080c1900e00410088005035500041c80200c1503044400240 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 816358300 1250 816357050 816357067
    0xd050304151403091005090a03080c0a0905130207060c0f230403050d02062a030126060a06050112050c1e0f0c100e07120605040503090a030312240b 65
    0xd1090b5126919030760081e002090040100c40403a4921001c1d4038044203002d2038481c258295511018084060000381c0c4a070082401c3c1c0345200001c2241e846145009246151a01c000520507a030f80c10320b2980140c0c2c00240c0004100c168000e02e194061241030007090800c02c0f81000d08200c070001081c60420141203092030307000c0031810070f8602558025040b6070002a410300080d5881c1d100340d56100d214072209084000030700040b40203080154a2001946c21a468504442400a40000e0b05084080210040341c0196020441144034030122000400d000346000009407080711006d0781d14110a08000403c0142c000d11000c680b980521185400801c8100032042511401400074858a000c00010205d83c1d007100085c03074002002600388100151683c2d001c00650718001c0703100e0807910748162103165001c00c07109c0e8411030b8820300500030780780b600013031000296400c0c80d02d070800c0740030903030038031660250783c1561050640c3e0305444907085002845410a40400c003006200d40640302000044821 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 816359550 1250 816358300 816358307
    0x70309030915080f06030f033702151b1c0f050f0403230318070807060e0901170604030f090519080d1706100c0602040b0a1202030103080711061308010213050d05030415 74
    0x44480b081d29840d00c02700c60888100949440c038541006600158150124012914503140041c40c1c0031200303a0189494503010011100c119110b490307903c155a1031140344a0114580519441114103400122040c50301340741c0980725a10b0403412040340030850001c103a010340b811048070340061001c144054084055102c040c50b0034030942148005000700640015041c0e0800e00e02403660b2001c0f0350b50b209581c0c0740c800d900c0e0007080c010080e8809034400300200b0b000c0390040701a02842c0c0c601c1c2ca0007c0340b05446901042d51070f80d41d0004e1070a9012080b20401503040144420031b5a00361a2404244c0480c0705019400340d00000303840180729900d08a0210300c41409144021281644043c00f5500c440c0c0d9160201d0240c0c0002c030911000ca00c0e5030426131005040e078030031281a02d60000d10f072400c0403140d45a44417841001150240c000b0f1081004d44d4012f050580070000a2603200300260340c0740d0881110742c1c04d480c0b881d40194060304850b65203a00040c4040191002d403007510780300c000081d00b180805c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 816360800 1250 816359550 816359617
    0x30424080615160f03112b11100c091809050a150b0307120b090307030909020915030a0f0b06070317060103180b0405010507090e070309030915080f06030f03 69
    0x40c5601944031001c0109074020801c003403182034a80c15200b0f4800002d01c51101000c0d082d03240241f103014840c00b944014010311154150380c040c00121000c0001a8800760f00310f6001804100108030414420010170f03006401800ca03031240003009200d900d215558030b030760350403080400034145615602c0001c00f00020707900403141b0380001070448519035560a05620b00303440c0c2030b0007a1003804181c40015240c0310300008039505203600d40c0c0d400d07010301c1c03501c04001c00075000002c071030394840103206042c0008071058002c0c500505000e01c0000d031040e0640d0b01c00b4125400e00e003c2500402003031080d180800e41106840c0c40c0800680701d48149643d0b01c0740100c005000704454103240c0c03010000080c0920171100e801c10b01c01c901c03440007041036883c0d204054540d800c007846030741509011040042c5140788282c01071070b08280300341846401d85440d1102072038803103020202e85000803040400c03c402848441041c9401480c240c020f804050f007803c4509440303105004000380c00e40c070a1100c03200801b0580c00711 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 816362050 1250 816360800 816360803
    0xd0f0c020f011b0807230d0f09031703060f0111030a030f060503240f0f1302010908010509030a0210060f0e040816030809010509010e0c1207050303042408061516 71
    0x628191465030701d0704c400c0715001078800741d401341c0610001e041c01c03100c08264180c1b42c50074040240202c0c8032a03a0704407511944c0340190b41c104001d20b440000001c000d10024a42c18400d00399142e201c0c80d04405104c2c0c21040181120304000c2e000380003850224020044681070145464040f034541d600303211070030250110340e000341e03014401e102c01001901540e048401c0341c0201503501038406e4239602196085008150b4800b040b40c41407030003150300c46010b9080c8024441c81810318259a5035220311107400c460080f240082d45400c0010703c89032081e07051201710300515031007404000903410117000e0940d5903000c1c0501c0e480300b503c1202041c2070000c1d42c019183c40e00100e014407000000da5242c0184600000d440b40c404c03940c2007001007820f244042c01555451a00400240008401c000401c548114109500e6521b070107007900110382524203000820182c02301035039803500a8090010b0194103100040302c40e0800c2000c50070302c807140e0341b02a4030380e00d681c60100805440c3c00c10040340030b0301100e02010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 816363300 1250 816362050 816362087
    0x40b0703110c0d02031c02070b01230a0f060e0d150b0303040801020a0216140108060f01180e060a0e0709050d02040b04091113020405280509040609050d0f0c020f01 72
    0x4500c0c3c05154004000d2822000101c1c40c4a05043c51440400c26805402c500800c1c1c0d00701c01c0010722800d14a518085207104030740390001000b45406021407503000951f00041818221040e0502c811500039200c22600e00081c1d42e50080e24003242c582e9880600c10240688c40c59880e00300c2811166810420383d40984140c90085549503403941c80a5078500003000421414590038800151400524440f0042d086060312095000d6441004100a8484400d005c6061145101401005180000c0c0400c00f83c01584c650280f9400c00108000301100594481403050710502c0c03c200800303920006450444806441940c00403205100180290a4101c113982e0411701d07000326038050204044035041441425144810030044070300c90002a07114030f019954004600100e0329010310320825021100d171588007045148035480301c000941125040c0c1d0b06035689074543c80c110040c44814421480c00540b07901b800c2e003d1030510b9101a065000e170000191107001e0100141125901610b44600c1c00c0f6501c03403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 816364550 1250 816363300 816363313
    0x318020d060b180a0b090c0a1d1908280c0303300f0e1612051e0d0806010e0f010302070302010b0901150e0d031704061b03090605070206040b0703110c 66
    0xe50200a2034200341c02c6201b6480c0401154400442500b00c035112440c0d0381e61240b4400d4520641c203942c0703401d805819006448004040450821001010301074480a0046d04400007648504080211111038040c59080c1230012000004c0c0f40303180040c2260b0b4181020110b00020170205281c0c60f07110814041c10b2058180141007401c4103070b00420072810440d00820000400052039540d889022210101c0c000040200740145200303899034482861080c011102c00c13205401100014007180280140740b0b501c00c10000780d4484c5c0000c1c65590001e0280303042c00003c0c0c103100000d0380b4050502a4541816400220341092610070b40004640400141120200e545e46040c1d60ed10500302e44000c20016400c1d02c60340d001481c18841c48840650113617201480074040c1070304490300c190007800848004d035469603d0186102201160703d5500d166440000d41300400b0b00b841015294020708940454011a041000080920001a4000c04c5615002070080385821001c0554440e03602c401c5110f02c50708 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 816365800 1250 816364550 816364561
    0x1d1b030627012727020d0212010636180f0308010611031206040b011124070201020304050d050a0e1518060c2107140606010318020d060b18 61
    0x74031218003e840144400041c0700c2004282012180301140080c10300c801c00402102c030b261130604140426000800c01000400302c0e07030014141d07038441d00000c5010b944400c010040000d03200c070b82c2c0030241d645001581e551001079900d01c0d520156418072a000f035584520103441c1d29910075107000c2c0346510911507045500ba41c140074046001c01d1140d44000f0702c0c2600b80701e01048012040da00400c440c40842c620603100c140400018184144034141080440141e07102c07040e104000b0000d8001416182681489a00001d40700d07c42000b890101560300400a02000170000500341c3c5003501d9030314056071640130440c41112062140c0300c08540c4010480c0382c0c01c0e000c010300001411781804a8400d004001d91000500410b40100c0c4500e1000d0303008120101042c0650160308188150780152103071400b00c032541d4501c551444074400c0041070f8800c504101040d40c041c46841502c04408003030b4250b641280c2d0001d034030f000381c03079a000704100e490b143d1104140d11404010700300000c0a01006c01e061620 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 816366906 1106 816365800 816365819
    0x4030516030e09180703420b010806030303040f0213020f090906010903170a122406031a1201020708031e070e0a06030b0d0c1d1b03062701 61
    0x4501000c8440f078004400e072180d40503201e040300c80d80c4200d9261031003240c0f01d00003540c5c184030ac91700602c41c099070000140c9a005610001c8506181050701c00300d03291101e600c1d01003c8040c004030710000034403101d401500741d0f02004c3e50344040c00d42c1c442c40115444419803002522120109526450750baa0b840c00401c8952124104800c101440065201c120f4003020000002800244006005501600006c0b40103101624042c031070024000c6129414a4500c113146201306600c044a24501e00203405440c81c1c5904820225101c0c0b4001c1c1038a10603000c100e10381d070140045a00003e01040c050380032a00c24603c068141c3c290141056401d50040503400c904030b83c0301552100d48030024000f8240c2c4005000f10320341c4900d1000c03020301c41e05c8081002a004840c20883d520721040d40081d4841500d501c0b2404641000c3c1c0c4c450401017950400300b07244512190201c862002040b200c20 = true := by decide +kernel

theorem cover : BRFrame.Cov 816187050 816366906 := by
  have h0 := BRFrame.cov_init 816187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 816187050 ≤ n) (h2 : n < 816366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
