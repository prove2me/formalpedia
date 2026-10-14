-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0800
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:52:30.624319+00:00
-- url     : https://prove2.me/submissions/2801043a-ea72-4a32-947f-ab3a9fc6a2ad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 143705035 ≤ n < 143884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 143706285 1250 143705035 143705053
    0x8070305071b030905040c030e070623071104090b0402090a20030606130806070f020a02150903010b0a080313050a0b040e04080d0f0c03150b300702012c 67
    0x100080311070b89050b000c1c0c10f04010803512400450305450700072002c080840c0d00d40d18285020708040100c3c02c01407585141070f55014660a00b080809035960300304202c04040490644140000d6820b00d5070b06010080007000a42421700c0c01045102c000c4802340d00c1401602c0014807040c0310b5001b00207510748001f815541031070402c2151245500302030283c41e008641449504c0d550b0220100c840081e1542c0d45c0201001d1030501001081009481104402c5401c81081c410041e00c80300c0300440e4400f00f0641541e10350801201090040c50300309a10366000c504c1c0d480c00505d20340003000805403501246070b0912260f0304c8005021010040b4440c001d490001080100100710070a03034a942c000c0d00c6020585c0c035103890002e01c0420b80d01b00342e000c04072442c1c3d119540c0f008150141b0544141c10984400414070b9843c248034403079140a06106645c4600c0790700c070440c1c0e4549140121002d84417209201401a0400c03440c002d000703200044517411001003040300085644140652881d0249000000b8007800f6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 143707535 1250 143706285 143706317
    0xe0105041802040c030e100204030809040b04150b0a110109080301030210091d0f0a050907031202010209060706052a0a181503050718080a120e0618010807030507 71
    0xd0100032007200c0c40503440c0740c0059545004e07003821640d041d0b0f0045404000d403c0901c2c00c3c1101d04022101ca144100003c000094220b026101d440700101c40014104003140080b4000c0d00500700504030400b070b20800806c0703485090015104808040ea52034808004201400303003203803c07031a000703407020034140300400062415800307000f92103044c0c1c81c002000c2680c8040a03049102c1c0503031402018451801003120455a03031100c00d501565940050009080a00f40141c540d04640000f03048070304203c1d01488400e000350125200680080d080e00d43e500300605002008203007d803003030001c40340c03e030198641f00780c142410307104904402d81006e441c007050084207a9000662072003903610805240b0300043d07246a251900c0d07100c007410f43c4010500d841c05010040003d03011543e00805180031f9003041c0651f0800040711000b190f400101608980d03104c040548502c1c0004000b940e10080c0019500303443c492024424142840030380f1a40c48503200e040060b0144c5070112201800145200c1c22007480c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 143708785 1250 143707535 143707541
    0x5040504021203040801020405031005012102152208030a1409030705060a0309020907030507020a0803250c0501050919081606051003050c0607030801180b04020414030c0a0e010504 79
    0x10310050040b0021000c881c012402c0d0740190f0f20110761654046401c0102d801d00b40041180710029040400c095030511203403c0da00440c01c0c0908980096601c0079104540720940662001c10080849588401d0076060510001388500c03081c000f402d507046000102d0b994000160344460549031550116461001e094900a400c103003100c60781445100c10010306502c2d41002800c400b0101da80c042103401c0103005000386900041c01402c2094034000411004940c0810429810307503020300107591b00c1c0c4440c2d9007000c900e40d40001070590f404150140c3c41000d03030040c0c1031046191040000b802107035103015400d034440011000316503d0395060b01219000500c10002019214501d0302c019520b0746044d211002150380c100c610340f441880c140024014004100a0081c03984411681289481d40d02d56004003a088103110b101000086000c5d000d80040b51034110815104024004644880d0713a01c03504041c2082c1e01c20b24900034000c5009501c0182400346802068402c0c80701109021392802c0188002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 143710035 1250 143708785 143708791
    0x150e120708030c0c0709020414040506120c06070602071202031c060608060114161b05041e0510030503031f0510021e0c04140f070f0806010f0908060f010807050118050405 75
    0x1940112600810003500070b07c0a440035189980c0220401d85d00c0400384401c580300078002c90b101e24080280350080540c00103100e410100c0545000b91034500502e0420040c0c0202500107003810041200000b19a600002422a210610143c207810010342d4042c401155124043c13000080c281d00002a0b46501450f00c2c0f0a542c0b504413800351400e030780450142d0741d9a01c90f0340200c4020b010440030743c43e000d0103011080d0180c07000311020031841c01d2101e219440c0d6400d0780e0035855420744800020b0320101c1561015001035411009499032880c044203180030500c6841c01d050218802450085090304181c011140c410001e6002041244800d0209160305254038004a07240d2054400000d07858645004511800e16031300b0604a5500388100080b1040364014091001c01002d40e89608400384d109101a811103000e00388036407a610300d050102c0d01c81c00c65400000c000e11880d410b0001d10744d8601d0a1078100c2d1070700800d031450755449100441d90340b98a41150303c0258001c0d0801d1104d80392903030240390 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 143711285 1250 143710035 143710057
    0x10308090604091a010f02030a0801030f020316091b0c150e030d020d0e060108010902010801172404020f03061306022d0304060b0114180d150e120708030c 68
    0x8140b030750321041142502c9480d241c1c1c41c021410081501d00c1c550b040086048400b0190002c0e40c02c2c5805580b000300085c40501c0040d012820801c20a01035450600111108807c030600719500e041d11005294050301c0402d80d5511400844001c01c00064400d0104034001c0d580085200c0c0000c40c0b1107001e0018000c0b118a03040103000400110845811a100620b002501d48901003010344183c210300d410800164023050059060820288c0180e82c0000364505481c480141c00c203181a440e07169501c0c1500b15410300d40c03071940c41d01c0c1c40110303800c0342c414007807290f4801c4903400b9010300c2d000c09043c0ca40009813079104080c00076124600029a950f006800901b8101044e10b40d400f92684103202c185105035011005944000248000c1c005a0b02504161540a0904c100f060ac8001780e1003282e4841c4d12038241c080c0c0448001c401c103030f0343d4003885134044682183e0307845150010000144014070702c00c403030440540b0038030130910304c012164415503045503040200c0c90b055603551400c02c016580071640b10f507 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 143712535 1250 143711285 143711287
    0x70b040309051c020301050a1512110d060f0e010b130c0201180308180309010c030c06021c020d06051e04050903120f010906051f05160515040501150e0103080906 71
    0x10805848003034500d401d0f6182d200307050383d410205006140c2103d001410102e281400c00307500b0381c0062840d0141c201250304072980410116200c1c28481260921441400e80c0075410590718014481d00390020540603a44032030800c146041d060000303088804240307210342c11040000d000f541001c002c1e400030000118a00001c0780201702180302c04481c20882d081180810760040601c83c100101d51158045400746800071480c1c048110006044511202c00041c00c2160f58996001004000e405480844104103442880300c038643c59480040e4015585070301c03486183c00000103007443c1010500401c0360a04001d0b8421240c0381003407101409008040d190a88010420840000302816040d4401e82415588010035414006002e09550590b4000e503c140c480064840e9404111903003c62510700c40d040c05507031044014011030304601e04401c003030900d000d580e40070141e03070401e11012441240f080d0001c0086090a40d1040001d074502d0180b00d0070030078800014400204804001c0a404000070080c0b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 143713785 1250 143712535 143712539
    0xd05031504050a020309010501080a0807230a030f080907030f11060c0d0905010e0a03150519060e01050a0f030b040b09010b062106030f030d020d110c031308070605070b040309 77
    0x401e056450580c2c030b0f040340503400401c20644a000b8841c113800740c108140a4481c400349500c48840d1400f504c2c001a055849030002040b403454500969010702d42c090741035803640381107414050701d5803442c0203903400440c0b02400080c9071941e0202d11802540c0c0d00003500840103240b03445403405011a4007055030462130801003414508010812168481c03c203544602c40710f8103040004084c103072130441480c080c45000c0414400151103a041d1003e00090f0380000404d40c2e03032546800d014502d188945100146007580218501e40d00000c00380c1a54416240e42070807942e29200c5600840c0284405489080210080780c00111400310705074100903400c0001c51543d0300e0070f00040042c2e2015110f08925803d03c940000b941d0300c8145080e5100100b1000b0b403100c4440d8a000300d484e0710401c2c41200c0000e900045e00040c3c0000d0380c1c081468002d19045164450042c4142e082c0d40703600904409418202d0701c880010000c000240c45030a4071801c1d51b405052415a80d00c11a009102402c11820300c6895100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 143715035 1250 143713785 143713789
    0x10c15090503040b130803090108060d2a030506090a05030f07110406090209010206060d0803010524070b10120f0206280915080405060414030409050901050a0f0e0d050315 75
    0x10f84080d100328074181c1da44001c202010306250390203074000300075074005000380d040f1070307802c03016090307014905a60b603100c080818501081341c0c44410b07140e010036614072489111203030020102d40c0c00b0303a8800c50031100c0341c1c1c482003400da540f08610700d4020580e074020004c1c180380310300340c001038481244607010b1241c444500c2c20004055503810b401480700d5540c04038009200c0e40e810899141c00901c183c0f440ea20845540e22200b0103880140900c50040c80c42e0205028110710506001d50341028442c07940e600c440a0303141450940400752090b07110006051008560100d0b60210b8883c0c5643c495002408140f080c3d0034840c03541c01c05801c002003440c44010000640515583c500080c10031543c80e980300c3c0d400d01449507401402c001100d820003581c20100400100005401034001d40c200382034240c1403007103140c814518480c83c0c110111040c241010b01c0400041500300038050151440d041c0030ba070102c0e6281000300d400e44820140c490380308404d0511503a0046008580154024000014450729240 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 143716285 1250 143715035 143715037
    0xe09090d0c14031c0f05060d11011205090607020607050c06150d02031603030914090c0903030705030c06040c060305190b01090801090c050405010e040302030a1107150503040201020607050306010c15090503 90
    0x89011611441c3d840868650602485640900d805e4250100868140342e004920024100381c8010a44100200c80c44096030207100781c20440c00194406005514200c00510740b0340c1001d45822015100340c2000c504850302032070a841e45030300120010011640c1d200c20b2a9800d40c20407107415000942c0f4050307517015841c14400b450440365000000c000040c030310328004041407211b03444020140d0007440100503a0ba00d01000581100b03a50038040d0700c400036000001c0c21031280b03002c02422480001181020541c1c04180305100318061521b041a096480d0015000c0d00c104413028841d10700110b2070365005c0807a980c03003410414411324044126640314540182100d000c686c041e01c03002c000c1c1404001c06c0c40c003805002c1c09020030190303040c840d041c199006950f03405082081c00505c82c0c054030b0070116209c02c100c02d200a0404c0880c0c83c400300503000c13024000c1d60060354140c4c014010034000030b10b01400b904c2141c3c050901a542d0142d03500d4070b6151a10b0800c080400b03810681e864030804c00c04514108 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 143717535 1250 143716285 143716297
    0x6130b0a0b0a0302071a0106050f0309100219090927111203090f03030f0f180604030602030106120608070501050703020109050312060112061409090a060e0303070e09090d0c1403 78
    0x148005070384160070709004154106c881c46080800c84850014020154040d0684850704091030b4800d48980b2080c18060425003500b8109000c0c1d4404540e00e04980866a110030018149071a801d10554680c3e030380074180c94103241c52401c860b072003d0492005c40240300100741a40d01421004180a26500c00102c0340e8000e10b2103981c5690010a4401e12490052204012000d00701c2c0114a48103c81754402c48502500c0c10100c04048045a4201c148003451522500004020004d50f641c40c1c0301c1c90200001c0d007003030140c00002202d018961944203010b200d140300791040d9100805103103117000300441c0c4640c000c401c100d086540b00d5429a00080040024005070340800a022082d0b1410600040150704072207580c002080c1050780411440042d00c6101940c0882030310b41416a588104036141303424114200140b001d403410300c4051a011010014601621070b5945a9404180320340401542c2d07041651849000c4d0410340d00c01d41014041e4180d1601d0750b10500041c441e8040148a060864000d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 143718785 1250 143717535 143717537
    0x216060203090c0105040503060a0b030f0a0c060e06090904021e0d050c10230f0403020d12031104080606060706140f060a06050a020c0111101a1806130b0a0b0a 70
    0x4018407140d00c00600c124200f0340302c01e291030303410039140100296843d01d001e481e484410741e072580b40d810fa0f0384043c421800220110f01c1250200001441c0c0030407044020311400c0009040718058011618000049800c51350303008201c0304040e107460b020840348804542d03540406040c2040f0501d2940c5800700012101c5004002030a1715007038503014844684440c442d4a420080d480e09030900e01000c0b00300400e0306000700009180c1300d44a60701e46128900c202e41000c2e40c802d40b03c03900f240401c030400304011440ea80c2039400f4810494080510002c07070081d40244801078000c81d0002c0c030241414800303055001d002c0c10000c1000c04401004442a1b4001d035051190341250344200400d07810101c01c84401046946400340c50a5550400251a090102091410000c004010704810b002c104113821101060500030806285402c80050000d0039408045014107082030754150742014020b0b03114480c3c0c0e00130307080408940c1169409001060512405c551051810314045600303071010028024507051 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 143720035 1250 143718785 143718787
    0x904060311091807032a0e070e03030c030412080708070f03260103020d03020a060c030902030c0603010e04031b0c0621050402010504261b0901090c1403040602160602 73
    0x128081c0148003800501150318240d0710420b100c3c03142030000d05002101e8004080403501415072000c02410003a0f00b03042101191704800114500201031480c038003444043d2a200c01d450b500606141c2c40e4000c0700d03030900c0e880c0c0060000f0440c0c0d043c0306100c808020720a1542624210060359203101e40d40112605480b100c0001912100f0503400c404001c41d4110340040b40703840c10700700c00158400d03410140002400b40700307c49400010140200880000d180d8000310078464190808001001809844001c0e0310074811841d5002e42410000202c07410307541900c0740305407207680350b440596084c1100e4500f155a08003020304040801d104c0740d0b141c006000c19a44000c0107035090301020440311285101c0e40c60b164540018000180e0300320044808443c03940c450140020074602048004074030100039044030f4000d08201003031400d1400440400e2a2088502080590721100e4580c1201c2d071031075005001c642d120014014080a0401440c2d006108080151030020218000d2200d2881c0340b80c00c43d0040d030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 143721285 1250 143720035 143720063
    0x507030f02010909050402060702100e09010e150402040311040c02070e0c0306040509010e060727150206010f0803071719080114031b060703020c060309060f070903080d050a0209040603 81
    0x382c4011500010501c4400512903806c0ca60001820303031203050300003841101e1414085aa040c040d141c99412101c0040c01d9811641e0340b2055003d1342441211015032001d01101c50684524252080d50180ca42080302018140329920a000040248541b1001503124006000482c09a002c2401d44254031668045480c0d0400c48180b01c15124040d21110381030b410860030210594000038025070001c05850040c09502d4100c43e02c01d80404040000b0520805a1002282503110495900010740d5143c0c2180e182d6071781c610400754880007a024200150b0404c0000c100803c0103040403502c65880d016400380751481c00740000d5440302090159001107105040104010509034180b00d00b2184294003424040200008800420307581c095014810200890814103151080000e00c2642e80c0c040c10392a5070703084c07036880c081da0ba00c0112610111000340c02c0016081c81d22030454841220760001c1400e0801d68514910f10281000601503008603034240040c2c22141c1d42c2d4050f15000f1401101c02a001d54 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 143722535 1250 143721285 143721287
    0x316110102070906030302030a0c03030f09050f0607180b0f1903150e060d0602030a020f0408030705100903090e180607030c170106141303022d010c021005090402070507030f0201 78
    0x520b42d0b0b440485040d24201e01000800d40101c2103940d00b85041c0742c101c000719800d10b42a001001072146229500340351040040c1000b40005e07410440d01d00c04c030300b1030b145581ca8090480d84c84001c0c4419108000d5018010002c1c80801c101508a00284400c03980c14421000c2c00c18149802c0d540a900010743c0f160841b80001034150152006071410502080c1d45243c0203002c1060a1301410000300b40d95400000524030302d20650541d1b9103a80c01c01040780c0e541d503a802410b586c9410116096500b80030f441c0641d100000c0c0b40c8034110f17089a241c0c40e140d104d90300e09a02608240b40003041030b03600035158500e05448220074002d00d8400c2c2c2868030000b802c40034441005101015400da01c4000800080c01808074981086170b803902c4c40850521a5a1b410f88540c9200c074447e038940c002904203000380340c0d643e03d0300795003402101031081e58241e401d40d072100a00112003106048202940081b01618040c84080c8260014414042c01a0025240c440c0942c0c885252281560060391008403a001540442d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 143723785 1250 143722535 143722543
    0x7080411030f06070c0305040506070803060a080105070c140f0d0504061808030301050f240304200d02060d09080d0c080105090919030e0d0606050a120b180316110102 73
    0x11a40581c0180255100e03810500c0d966000504044140081e0840420030503110710221400b0b000c0180013030780c6070741581ca00300c5c8140c3c1040d91880d01c58243c1d810003080340e000501c00d085c410b44043c0e07a0310b007203180c00b915144040d22501d500c0700d01c903005480c106140d5842c02c0040c1c0020940079a1019038881c07808000510b01002d511480d1030b4503078440d401300701e002c8002040c1c030f05580381120781507a40c070102000101c5440c40fa03071011802e6071000380c42003800902c00002e10701c10380c0a80005905482c284214108405003032a815500a404e605400302504180b0701400c0c00403a821400580395103d81c4810480381c1040744407094441e2240d550141480c3c0c00480b6130b0041100740e4540526007420784074161600c0d0729013001da00301e4200b400042d044c0740c0300e0b6a00b09100800a0b180f40504107180c180003000d03200754010a401140b000c1f0000071340c00355030010703040300c15001841c880a5450b44241030b4060300909160503600c0c4414485004040f549544c1c01005910031240d456001d40d0b82d000190034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 143725035 1250 143723785 143723813
    0x70f03091701060f180e0d030c0909050606031b0d0612050d03060503030304080307020709020703120c0224190507050c25090c12020c0a0203010f0b0a05060703020312070804 76
    0x79607410050200040b0034040c1412080d601034040700c5a4800301000c0b8500106070f0f0301c41c512407a11a41448103003064156001c0348103903086654031801d940d103e00d0000240c40c0199122600a1000c000007140380c03802992101d00f1a210307841103803074041800002002d603442a000040101d103441c030442d00300a010014424204001d04040c8545440e00c800680c99000061010f408554004000f4a015100340714180260410960464840d80c0c50b09000340406002441d480655107881c00c48542c103030001604e00c00f010010008440413005808144066000c098a10400038800c203c10b913092151500031148540b90076503035951582203650200d0b00d4001800006180040d00c07103081c40c0c1510010060000740d1705400c90101d03840700d05500407941090703810040440f0501c045000c8900400220b4014400c42c02240240041e1020395901002c80e031701c10420903407100024078108501d0810902600c4800e0103401a24101810030b00001c0581074101c0700b440001e15020b0401c002c002403d448120 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 143726285 1250 143725035 143725079
    0xf060c0409020d0e060a0c1b03020c0d14010c120e06010807050609010201020405030316170705100506030a210201060506090f011103070f0c0f0605030405070608130f080d11070c090f02070f0309 85
    0x1086a1040e180a134544021840550082c0643300c0d161003402031500234840030000c1503008100d010043e9400808803919101e805203c6801c2400c2c00381e01910000c0c3c0c8605a81142c4013600703269281404000b900d41c04110618155502400001107e542c00c3c0b010306800201e0400000790f2001901d8201002800d920340300d402d40c00d080c4a40300c04600001004003c00d5000c0d40001401d40341c0c0c400203460a07103600d074001c2018021426401c1c022040c04116400d02c41c860b00284105900c13007040000303c0c02810302c0f80b0340000d1180c101a44540c418804050140e035007005992030b06945d929162500400307032105032540c03488054200b0004040c0c0d02d90350f0091003a40b0b0b102d4114245580c40070303201d0515101c1c800c10881e84a01040600141003920f03400e6a0b4084296000e13198140350450b03094204401801100345441120f412580c0d00200f03c44111b070b801034a4086140c20b0850706070013400c82d04080f20200e5400e120a000107130070400a0002e480c005e80300c20074010700d030008180c1c9800c400c4265039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 143727535 1250 143726285 143726327
    0x2030c0304020109060807050307051605010513110a06080f0c04230f09012909120f0f0303010501090306110d0c0503040c0504060b0a0302030606070203030406110f060c0409020d0e060a0c 82
    0x31124923808030650307401260070300e0583e6440f24041750969002c0854000540154600f000f407011701d803011800804c1040c4074941e2413007180b4000d001c00404040d14130450000c503c102e0001181072902160180d0f025940a2540307052a44407202000ca8500100d107510300e05c020030050031f07407601d8800714120668401701c1e800510b640c1011440c2e0819006100b1910b2099200b40d40c05894480c5901a1044c00d01c0c0542803600c05002c5c10002a6591580c0381da00c0d9a5015505107c5542c0340044110f9050300c40c1a10340000c40c600d1592800c1c020000208542c01080741030080c81100c04140c001c05a031031001e5035038152a800c113070030010b80c0480b0550100b0f114511300038040104c1c6c4182000d48000109a042c016101e58641000c17640c14454060025894000014045203064125018008461119080702d0019191a0800ba0740e00401c0e02c0d90400b40c4e105000030030902e41d26170014580c504542d500400d10b040352079841440c0070350580300e450b100c42c1c50f0802070b00919442020540c2c400703402000b034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 143728785 1250 143727535 143727541
    0x20301051c05070b0a09030606080c1005030a1b05040311100f0e040603020a0902070506070503061e03030d0507111006210219060c171810030f02030c03040201090608 73
    0x420a80d65840300341c020701655a90041400010700a110081c1100320000f50b0340c5054150040c0804500d020441c1c200d0f01d020000b190036040002c0202c5643c90141c80710f4025861610b05686a40005000c41071254480044070b030407141c4001807048540c95619159112400c505c4c01200c092110003040f80a03805580c03c40c03642e00d43c001c42c440360000d003e0a11340c11b100e2102e4086400f030450307604041c0d040414000b0000d081e0595500408001d402881a248540c0310f10b2401c0f82e2501c815902c0c1c41c0d001803002d0501c51185030130860b01c4011100181282c0c5009110380c0d00c10700340c91040345c42c5404a505181d40280d03000c0240300d42071070a1588202009150300700020820040c81c90240c405501c0007058200c02151281900c24440d0400014014522590b9800c001c01c00030076544126580091400c6d0f00d44010f4242083d0340c2604100d0310040c07040340030307041404608007424048804044d1100a5444d0401d040d100441c002c0c6400b40c08941c0d030f450640009403410041b54099030802c1251820 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 143730035 1250 143728785 143728789
    0x60c1e0c030807110307050a0201030506030a080405040203071101050f07030606090302280b070b06030d05090f011110020a091d04151802130221070507030c050a0b01030f031202030105 81
    0x31100c4150340c1410b02620a485a502c211803088454110031941d100004403e018410300082c2d0f980352600c03d0341c0c18030540d603507901450786814101a0041c110b0f2010311050003681f410307401855026019150410512940100081c2542d2007950120207801103542032010150385030040402400d5903003450141d0700c0c039540c046582c0100d0800b0070303c8589880a540ca210704644015000100b5600340300b9504d61b151814075002c03510301622802e200e8403801100002040c003d0040d02c05103003000304440403007402e0303200540360002ca403000a11903000d410389240d5144000c1c4060030229903e55a001c00c1c0758241034440e805002d940c0400006850500100000510200b0200000d80d00100c800b00e01c21103200c0c091040c1a0541900942c00604103000c0752140d6a19806030004100c0c442c5581e00d030380360360b1401d8286110292001d0001071420404040883d0103400500c012600c9203081b81ca141c807072501c0e0b07042d024500f81c200300e0b00805002c6003d02403503484411034084004e001d804610b15454500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 143731285 1250 143730035 143730047
    0x602071104050601021203040c0305030310060314040c0902070303060911090a120f1e060906050a1b08010b0a0e040501090c11010b09190221060a060309020901031b03080403060c1e 79
    0x1150241b610b200000040401100c0011300700255400f4003260340f00c9c00c2c102201800000b050044400080c80c01503826100710501122500031a001076924158030b04181c110006540401c03010340a05840e004005004a400d100d0303c0382d400111942d440d120500002004003604041d4800407241001c0745c0302c0c2d4007141030703032100c100c1c0113501855014560085c0080880318880c4100302902e401e10f03009101040c4442d5411143c0300d014420750401c081007881c208072800c0131803c4840310000302c1c1840144050007070301009018038021420684000d0001d0740000e015070700c00740c200303084c141d444500d00080703650440d58006082c81000000d010856000b000705000640007820700c0c42d01c01610049075901d4210754104c8845419442c8005604554925a2448020b00307440580c01907442c150001192407180c85101c0c0196030007020a00381d0703440d545480041d9200300000b0309890000110004c0003075200c00041c0300840c4624804500e40041e8071018001b40300d1961000c1c408440e82414202140c0d00078 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 143732535 1250 143731285 143731303
    0xf070f1d04110613170a0614070c110301060504060b190c12051c050906070f03090809040207020102010b0603012c040320010b120601050a0603020901050313030e060304060207110405060102 83
    0x144455031641c0e1300428004414511341c0c80340788500800c2c505e903d1040ea0120b04201c059000d10018807603900a118050000007080700d801e4001080c800891002403402000c8030b040800040020601680f40c4000500300d4506500c0f0f890214000103c85248440c1c10460317241c40b09980c02c10040d454800e880e0107007a07020066007442002000601d03103280d841400c0004481c591284010452490048607150b622981a5081e801040d000d640c05c501340d138828000c9601f5554030120ba5030500f4403000901c400381d003098408034195502d03291000c5e015201d1310084c0d17000b00140700d4892600c020652081e034040015074240184000c81c5400c00000c0794100c1c41003d046d600000341030a0245060800c28010300003801126442000480340c640d00d40000503405041e0381d0119050030030f2031703a00c071016022842806400d5010403014800508505405c225440c1c406009040448030704001500203401c0c0d50040300d04640305a400710b49041800550408401610f1040d2401c03c4141051070001c1c1d0340b0b8141e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 143733785 1250 143732535 143732539
    0x213090506010507060905030901171603050c040503030703091712180f03100614040204050d0210051e0304060c08070206011208091201051801090b01060f020f070f1d0411 75
    0x190000c038000ba44940308031901580c02c1001003100020306e103003040d2250701c00482c81d030014020880303280300d0b82000300000d4019003654100740f190300703941501a03025020080c4507951228090100092a48042c401044e10911907920016030728207001018a4811080012503420385c050410541d4241d010300c101d4003c1480009941d8ad40c18103080080c0c1c0103130b030036aa21b5806000b5428043c4151005401c5002a2010089411101c40484040c88224000c40c421198400468103054000d414802212418a600751030080c0c505800d012044c002d1503020761086210b080d001080005110302e81c440e0301424000c070301d8044083c1c20710b000000e5032100306018482c205e03012000100f04100450085602450001c2d081c40361502c4041d02c598002d010803189440e00380300c190001c010140043c030403040034030780c0840168116424520300b00c9d01c1d403580401c900258451a0805030011303508000c020000c11240c4150b4500c02d00300020000e660317401c1c100c1c19003c0e1414a05210001d079091022107101d01d81 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 143735035 1250 143733785 143733791
    0x9070e0115021f0b0a0902030a36170301030b10050414011a0403051b010311030f0a090602121306060801181502040e0106080f07080c070b040203071e0e010504021309 73
    0x3ca541e80070000d0080001c1c071039000c4811000060025000d8020358440c0c004c0d200100a0144000c41d0795801950600450100075007107160b1040703c401c0c0c080028101406884c1c1d034035446001c51084145540203800a0313034040c140f031080059050280c0e00101c060001a06c0500020491402c020241441130245c1700384006501d11440004d00c0e00011b8031f0007940c202084030125400207200b50314540d0711034001030020342400b000128041da2403003100d01410740c1861001c1c01d5a01ca84060004050307462007101d903140c0070845940c4444004030201e0003022040d460002003541403401e0310444001d9888a0360340d9041c0038006000d80c2d26811400c103210740040e110305104484251780e200900c21500311900c807140300e10001c604540d0040f90340e842009100040c1c441612041c10645049c0303811607078070000000c10418000080c0c50076101382d4220b440503044451403a205c000000310990350314004010302c0c3d1030410403c11287c60000d038600401007600c00b18074096038003200da2880c0150703001e03c60090752 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 143736285 1250 143735035 143735083
    0x5070209070e1003020c161805060a05040c020d0e01020705180903040e010f03030e0d0803010314120a02031c0c0504050118080a0f0b16051c09060509070e011502 71
    0x10099400b07614909000b0160004550220b0b0003400940051820313507224031030050700314000c140701c02e82c0b28181c0c0d14120740c641612012013904009004014034079a001140c0ca0310008554680d03001c3c1c4c02d1400900e030050503030a00c40700307402400c02e0075040400d030465120120405c0f080e21007420002c0008180f4005458a0361002e07000e80c954070071680101034064200000060344140d01c450303501030340e100382e40e0140207080880800011325140c0401512029003000108001601003046043c1032070144252604119a4030841d0301036007000c0d0048001d82c10005000001f034100b55403100000c0441c90040104441c6a030005101d070199008450500107148111443c1d811b5918005000300000d0b000c5a25400c2d040c40c00725a00720010ac1c04840c1180f001010034501060404c0b003680704503035030f500c103410001a0381500031902008206a10040d0f80d828540c804182140501442850407400625000b031409568034050b01c01640b00380c52a0315220800b5402550120380c03050b50300030800f03512100c90 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 143737535 1250 143736285 143736287
    0x10090c031107060b2404060507020409020405270105090714031e210a020a0312061805040b13170304021f020a031812060216021305090613030507020907 67
    0x1c0c0c152041440e4080b4107a0208540e03074000844120054a440301c13024200303c140e018044994103901502481800309009291092001d41150780c001403022a200d1159004038080340e0082d0344d5082e24000b10052440552140c14420b8072080300b81000300f03d0ba29003c000161500e440d070190b2400001010740ca26042d507402c01841029508005035074448060f452010765031414103a5074451f000b08503042c0344451345404425034500034090780141640000554003110850201200858074540e06d80c4c021400a004096440000c504880c1c0007415040c2030420300300b9510000c0045820020800014000403060f20803000442c0ca1100c88544984072803001965038641d08a003841c5000c903004002c0e00081e070000c2c8a180050090301d9429044c0000210311507000314502400d00307078001c1301200030000b8600b0f900a20500d50014811a40143d4541c002410300c0b005400d241d5040392280b05111401034180000350b001002052004805011a507010f4840e02941502034403d84100e00020405 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 143738785 1250 143737535 143737541
    0x1c12030e031201060315060c140f10050405150105060f07060b0907020303060f10021915020a02030c1605090402061804020c03070b06100203041502010e01060b0c0105060910090c03 79
    0x4590840103a81c2c03102e01404481036045024404c00e40040d0601c00c10a402e00910b81e468000e0b2003450b03441d100000d01c0c9440d003c0f441146d041c0103240903c1030003803201c0c222800388560b1400c44410740300403074141081d090546c074200c0b404810010b605c449600401040d907558089400d80748a0026140c0ca0f04a24200500200490745600703402c464460108800543d01000071882500101e40228014110a042c401c0f40100300d190800980e10103858407402c8040c403140801c0746441080e10720411003000f0440001d9811000321a00580d00104103480302c0581808403042e42c5041d0b5668041e15480c16000a20942020703001074064100047d090f05600c04184c103100c99000042c0c41035507078003030703030781005540b039001d49019154405a40041045480c02c1400b5800d00b10b4258001c606150502c030f03800202070505042601950341e90005104150800e0250301d0041081803129500c0c1c00c0e00480890031350b040240303994130403550303502003155076030400844200f13850303030f0100000340820815400c1c5e0007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 143740035 1250 143738785 143738801
    0x601150917011407030906050a38030a0813080607050702120f0604080405030d0207080c0f031504030207061202091302090315010f0302030d21050403140a0305010503010b1c1203 78
    0x50f41c80500100054107800d60401048248a0031040155940303481100d0221038112040241e844035900e44005c0b4100c1d8024082c98610302a1100c25141d40c9100006e4505158020121203088002c60010401b030a40c40708440285035842c050301c02860300d01c0005101d803080d0b02d002481a04001c185101d400400c10000c20790580300c4080301c000703040034100740800f50800d02c00d05102c2c0c03050038604500c10344003090b44400c40e081c003401812121881c104015400180c1d50070070b0f405206000c81c8401ca551039a00c0a80250301903006006803609084004204004d08103d84842a0041001100030344410034040206115030307000586950b001d00c0000e003032a038000200002102a0000810b0201146480004882c070890072240e42e03a81c509419914032440320b40010100301c1d08101d031051244140c1000394810b01c20710b417040c0006075002128055400c8008d403040001d40e07441c0103009608003445410100542212002d45800440095038000e0703000d031400400404410210901c428020b0f0020a4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 143741285 1250 143740035 143740061
    0x10c0e0a1203052b06080c04290301091205071109010e071202040b0a03020c070509220809061204061406031213030c030308040c06030515010e010e09010f030203060115091701 77
    0x1400c41c01c01c0c02e0b84d0024240c24001c030702d0240200146000e4a01d4035104000c2c0a68003014440d509a41444001c080c4240304060540c2654a400e1020700241c402405184c01100940300c40b5180c0c0c209046c103c0c89128035402d0907008803005001488040c44890308a9071144035864501e05403181842c108000e8050f580c4085414000400c1c031011342901a006000744110a204032000ca5655030304020034400291070200502559aa41c030742100d001e030b24080a00d42c010082685407a5040c0e02081c04e940c00749803030042507816031040c031080041310b005195489a0640801d0111b0801100194440c2e0039864030050052000410b00640313158070240744c2c000c50304100092070079076413418080d20b480c41c00c03034080391040390f4100d020411074000d10030b040c01440e444503080c0310ba10990005451a0a248083d41d050251800041c0f02c207a49040c80d480c040e06d401070886016510758410b142c0f400314107070441d544510048000b040c010350b010704150103c40b00e4032010452885020b40a41c01850400f0800b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 143742535 1250 143741285 143741347
    0x1008061e070c0c06090302091b0a050f12270a02010203031303031d030705100c0207030b04031205010311031009080316050417031305030d0c0209100e09010c0e0a120305 74
    0x51070f0307802400017000c0f640240d0360102c0d103694142d00900d4403074041000c000402818411030b19000c0c071a2002e0702c2610800c100c3d4924081c44081c0050103138000300e4003c3c050313800320750060220f42200c00c5d01e90354030340b1024018101c0c4a019800030b512408010400c200301c030b1400e40c0030b02c141803107074210403018208124603094102600d111942c1300d40c007100041d00d2500c100c07440100403402c10321036001e91784083e0740601480c0c1d080d41d851000c905400740040c2c040041c0e0030003041d410f1106118580c003c0d48201090501c4c00c0095061504001c10141c01c00b40311361422880e4404280c1003004c49500051200480400801061054a41b4003443e00035074800a9800c081e2049044000000d00310480c5556900140c2c0c3d99400415968251802443c000213942107042d00c014100002905e0f044102c0304000c2c0d445907183d5030816804c0c00304036204940e80e916a1a050b03181500700304810000c0c607094941030006410301008000f143d000000081c200840084e042c0402e0510490340c90185a06200072 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 143743785 1250 143742535 143742539
    0x30901140901020307030b030a03080403050a050d020307020f010b03030a090b16080c010605011404031208180d0203071a22081303030f09060906020706110a0803010e1008061e070c0c 80
    0x7040c001d4000310340350400700303103071003400f0065140004410000382e030315039100c1d0000da40d165821661034120b22507200c1480400c0c03103142004866030020b5072007210154010100b40480f40d02441c00d40355041c110a00a4100700010034420307500c650010199484240e5983d9274035464541c2c00c440305040c12020300260300108002d01c640c601900b084080790400d99078200c156010310212501c80c410703031200606401d404020a07440501500206600100c80c081c6c002c4402c0c0584101030428070450044001a000028a0b07420000e0701100d00000f06082e0340301c00442e01d0011518034414a0741c0d41074004039415800103900304140d100844030030307948112410030519941e03d00605050b0304285654041081d0400202d11140704200902c01c5030821782c02040c0162500100352010120740480885901800c503010380418040c8000314001c20212002030305501e0300d0401c5030345500d0a6040051160441d00c10300c0b1002d06946000d003800c801440d05140140c40c2ca14065454200312100107010281031200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 143745035 1250 143743785 143743801
    0x20301030f0606050109050607120e060406020106030303050108030414010c15180b070212030601030b0f0a062001020a171e0f090111070f14030d021315020f0c0603090114 75
    0x190301d01d058400c080034000c440d1104015540d00c2164040c5c140c110b4424826800814034481c2c62111442d80e6042401d5258048400b00c0c50541c07242d000000940e4644004000b0503905104044c0100314403000740d070500f801c1a114040003244120050704020b2a10b03003086c14004981700c80c06007180c00b000f0401103076045410480c40052076800c165003285120000519450020602151890004112901c0e6940740d600540052042004085e00015021020211a1510f030001c901418498032005502c0d10340d010102030100c0040e00560040e401400340c003507481d400411440d00b1000c81c2e200123846a99800d0950210380c40c80e1401450f140c0031600b808142032440300028010981c1e00020300070007003001d42c802458442c8000080048003039802c4507000c1464003400400089404003600d1418602005090582c1c100c01a621b440c801a02d00800000009840000011035140041c100d4400d90400d2240c84902d41404940a11000400504000300079403042d90103040032441e03a0198102080c1d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 143746285 1250 143745035 143745053
    0xc0d03030e12042417010b130306020f030a06120804090f02210708130b150102010b0909010e1c0e040902040b03070b030103021201051b0d020904050c090a06090b07031d0402030103 79
    0x29504004d10200000068038510840013001080c00d0200b4901c8642d02e0100020002c2d48079075611500e1350103000010000442c640001c0603005043c0403550b45a00b07100d079880e000c49180b03502402000c580901d449002030011010380d4110793700c0d95800074624a0715200c0707078068412198400580340b104600c03042001041c581c01c0d4000c00340341d902c0c25841c0d515403d003030380a4105007002912400110000440d501503130342884140351018800420881c80c50408204410000d58488285944600001c09540b804005d43e071480c0413410355141488100806c017801124640c01d1550040e52160134007020754850344c02030500c50030060b0848050302e554090a80140c0c20a0100b01c0c41021b000540043c0460140a541d00440c02208940c15001030b80800f061164040c00c000b401c1b0b145c00b802400559a41c074401c040c03040194603019503990544400f080f0414405400100c280900c881d41803200383c0c4072000761140140d160030140522000c20650f420410805074103d40d100303000000100400000071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 143747535 1250 143746285 143746319
    0x120c06040b100f0b18010801120b060406050613030b0601080609010905040218091006050d0803060d0f0c09050f0601020703030905191a0702100804030c17070609050303090c030c0d03030e1204 84
    0x91789028040241c03401104c00031001c0c4100f4400400202101012400d060941034006070001c02c00120103503100d000c10700310f0300446101d81c20030000748010401c0c0316100e113001d07500202c00d2902d00ca1074504207000892104c0e040c040c00181544c3c0b0350026007192500040d01c8912240c50140159501d445d10520707070780fa107804641d0b400d000c2c2007a60004482c103142c00c1010342d0aa000076001d05681e10582404540240150b0968211b48101c103140040340900705540301038110b0480c04141440c202c001201c940c0720107072020781154803550003000426400f50744a0107542d41120b1241c0d11102407509072203000229000006611340c0e03c6100903900d0074a000401c0140c5c0709407401e4429000e0f9010558400c802103c0c0500815480c015560000c0c0031a00f00105500c0c080c07500034104a0982c0b542d000b00c81d00f07440219440d0f44008280504104200080b00d03889100310010010f40c0c0d1090049008841f8140008052540b43e2001d650880420b02ca81010100001035168075903a4540a2121508440c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 143748785 1250 143747535 143747557
    0x90a0b0c04061106040206070308070c1a011d040b040303020901020a140d0f020a0b06010e04060905101a0c151510170a06290c031b120c06040b100f0b 66
    0x20011050400f480031543d1845190010101c034100242c3e0b40f0192a00e00b0b00904940403c03410480d078000142e9021020349403210b1030b180c54070013176041400c1c50712481407400011900c0303642202003000203806011281e5000780d044c580940c0721050200140d107004620b43d40184003031020810040008000100c0e550b801040f81d4924004c0c07a12480280d8699142c010040d1400d05101c0004071594002d07207803509208009000042c20a58030383e210310403a1803d5914410b500d13403050703040140c403a0036402d12110070382c1c50364041c1c504080f400b41c04d40c1e9440060403103041c9503200320020707031400a413414940c0042d5005d01210071030600c00394001c0003a24030b0206c12040740080008940d001c882071040e601034a65001130003403042c46810f090354400c03181c00c0c100107a44e9020058400155000e00c0a41841c803180380441e00c00b200030380061403c02c51403c1116a04010a005140180000081e0644c00c1904002101420f882d4505048034290449e0410340d120b03041d03400700180733142000c00244410551 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 143750035 1250 143748785 143748797
    0x30b24070c090b010c0611040e010b0909060406051020010c020a05160e0f060d0c0906171603081305041a010e030f100c11072702090603010e090a0b0c0406 68
    0x140c0d100e680c12504002d084a00180c0c1c00d490100005d0794660048000d820306842a88c02c3c96925800070118003401d8010824503500411401d00f14200410f00c141c00c07903c122014445141420007003200712985180c00d208011000c0f680d480c007a0703108286083e02c880c000000303004000010f0310195480d000000304071040d22414880c03100c110060310b00403040e12250009000700e03443d943d08a10780d00c003014104552012140d0060b00000d1880b24502c8014865118042041072800c03401807100c0140c52818192a007080d800d030801c0c4000d880605064a030311002c0d080c6c840c10070395141d08145055030405900320386003201d1013650000e50f991004046400b60394244c10b05003107d05054642c803049054034800e5100d091000e140104039001040103904926041c000100c3e0a01310701d02c2d1035520382c031074201c420038090001112188a08407030791f00c00448500354988000c0d41c002c00c1c0c0d2444148034582e0701c2e0420340c0204500030024451400400d8100c288107000f800d246140c1501580a03114001c00300300c2c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 143751285 1250 143750035 143750039
    0x1909052112070f03050d0f06030c1401031112071202070503030a240e06010e040908070302070807240c081c0b0a1a0c150903030108010b040b030c01030b24070c 70
    0x4145012101c00b164410703880301c8000c046603001d480e507820500410420648401d1950f24107a4540708840046018800141c500c601c2c0c000d849121003100d010150415052100c9132800c4414403007104e65411001a0140c41d54ad2041070480b101c41c0c40505c071011441c00060003005200703000020703500580b560b400c100704856488015501000340401c0407485202003800401c01152800c40242d8415810705107044440b07101d9001500711980c2120031a465403020560f401807590401c2440c01a101130401131122504181050300364103281c0a42c0302684101d024801400340c4194100142c1c20f034020324003521580c00341c074030140c100d425141601031140351013440c00051034400c403000d0441d00e80000219420f100040d44810035482070744a1402d501c038400781d006000c5842401c96202e40d40603c06544c07694101404242512540c3e942e483c403580c2080041d1001c0e41c0c01080210942c0400d08000425101a03000305114440c206030400460780c10b2106511164074040c010f000d036500c18010107c80035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 143752535 1250 143751285 143751313
    0x6070906111906060f0b071106030f15030102040b03010909110301110405040e011508060901050a060303080f0411060d0606080906010b03011e0e181b0619090521 71
    0x8000c0500e5000c50ba4014600e11142d14480b068503010b1a00460b40400d0054036100c0c1e0207030441c0303190b000a00701a00042e000701404860302115801c242c0888883d440d504001c0200180d01e08087c001041c051401d480d0a01c0a6900b50b04a900804500c400e040c1c0725a9201101e2000f4000c48a003660420801c061007a418035040c0314a0703590b5a840e40c403050601e402c0109110090068840d10141f540d41d1741600c288030043c06a00500515860b402401c46282818040d130a49401801103229942021800d0001179040096107900c801c0c44034640311139643d14204420f40c40c03d45600c4582108000030382030b12303203041c50304039009441c003a40390380d003580c1c50341c1404554603802440380500140003400144002c10384510600307801c035000d42d038000c1180d40303e003e0301c00740070400c0d0352020300c00503204103417551070704244508001c0310003410341720655107000c801190291161040c03026101c02030407406c00c04c0700e00501c9541c01078800176042c10003104013a03040285040d00d109028540e4454250598949 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 143753785 1250 143752535 143752547
    0x1101020c010201270206160f1502090a0b030604020d0c08060315090309061617090901050d050d0e12030409200708120a090b1905060312090f06190206070906 69
    0x80c4044524148a21102e004031046800d0f41c1310300726030000c401c0040c918580a580582412640118004011042c03103103800710b041400242030340303403090040c02a0002039440d900b5260807203a001c12000c0da00e661b104000350007803003841c128060f0320707140035216001c80d035210075400d10945040c1d0440b11101c480d04142c10b01500d0403036040e00280e20400003040310f41881c402414809203042a8648200060390700c0ba902651f0100030440000d00110b107000061418410060051600b510700c03000d04a4a07495003602c81001c14481c0d0148600c0c18881e8195456445030007400980e00c84c103032910341d602d80600c907000e00305c1d00c6c005890749944050450407501032041101c0d0707401d61104210f450014403a04072805900020300340307400155144003100210f0a034403085071141d82c038180c030140d042804c0d41d10b180c12103d0280810b80070740d10140c0707c17590a80101c7c0c1113810070602180c01100b0007070800002034143c806c00c010108001d00f4045410281d071f8000490728002c8400d0348444c10030541b145001c6071a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 143755035 1250 143753785 143753801
    0xa0905071d190b0c0717100b040912030e030f0a050304060b090105011704170c0c0901081b04020903030d020c03040305010b0906090f070e1f0216030b0f0910091101020c010201 77
    0x684100703020410207581414001c10351602c0c60001d881105584081d10311b620700d00c040761440a500210b085081e281898411401c62200440742001071581503216018200d02c40910700041c59036484031a000c0314020429241e0b030078103103101e0b039035500000000180745410984c0e00b1100b05003440341c4003003549011442141038031410307074694030041c81480070041442d2003d001a00d40d000c11030a459904001e440080c06810324650013856440c08681c00d001d80101c0c1603205605c02e42242104400480381e500141d000a041182d001d030300c5a0710040000c0c114031513030078100c0b003461001810020303000006c0040c004032400b030301c0200f125080010a01c804c0e200101ca241d030384040d0981c0020400c4250400070b0350041d0042ca82050082d3b0101e02240c85640c80710700c011040d59000b060481713019810801c0c50742c64440b54807040485442c40d81c842c2c10780e8001074000c070041d940300c1c000a04100c02c1008002e14146280300188032411040c145028188050029130b40103000d03028040071554014001c40344 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 143756285 1250 143755035 143755069
    0xa030e03040605250b0408041e1404020c030c070f03140d08040b0403110f06010f050d20060d0f06060e010f09031e050102030c0c0106050a0e01060507020a0905071d 72
    0x1c500004c0c180031030b280c910501c0414010031110310300301000c240104c1400b44101c0c4583c019a603941d04180710911045007d90815407080c854070420f1220368400201a0000b8030252005078075140f002d030071320b4218003508620100c83c0c442c408001855201c0c82ca80082200d02501d00c00c41030030f0700a0201034542000c2e18084c0081800b0b0008140082c1d881050300754418080d15081611454440b08a801d207500602c154259501407c0140246880c3c1d001c0a00200b900301c40c0740341d50340d0403070b03580c2006000503480459035086441100c094079240c680c11207000002c03050f410007501510340b241300000c290b41d016210015031840319500c1035501883d0605115640e68072403400e42480e43d0303a540045070803401024851281c50382844000340c0c0900256000700c052500080d01c1d14109880c4900b100c800743d106620400920304c0403c00100c0721813805066405a240041c0e9540e05070012980100095024440107850082000301955001d0300301c00c513800b41301510160300c992800800c132004500780300d410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 143757535 1250 143756285 143756287
    0x6180c0f0311010c0c030b0a050405060702010c020601090e15040c0608150d060509190c0e0702120409050a06030c06050d060506030903090607060e07080f0709050103080a081509010b0a030e03040605 87
    0x142e003c0d802940b9854589200e0302c1c548070710030703280d0342c0341c450360301040e80d644800302e0701e40051004200e0248a03042d8028402e100811103400f4840009540314410b00c1620b0341aa40c81021560381501030000301d40046c280901c1c895541000d2418400811161044c140054000b10118031910312454a5164800b4000c20b4001140c00544542d0300500380588803803100c0c440c0c41d544504807884108044241d60169804e040517600d405070401c44194002c00c1d260440d0001c0c2280f83c022035030b01c0280e4055510300040011180d550400020061001c2d0308043d148503d030510000705c06a104000341010054034506010303003941c820034041c880c00281c8884d8003d4106100f5039002c2c0c1854000f60101d44e01074940851213803048030109040c00101c1d0802480d07600641221b4030701007400c101c002c0041840840400440d8516101c038170043c0030340c08000f420000703250085540940b0120003484000c000034201c0286507940c01900b0400e41c024038105000c01d0030103820b0448144003105540882e9061303200c80e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 143758785 1250 143757535 143757563
    0x905060a09180203010c030e011505010f0c0314270d0507090903050f0f120906040f030818010e0d090f05030a020d020d05030c010203071b110909010906180c0f03 71
    0x10405000300300d9011000c0c0e07106420b076402580c2c00b4001c1d080c1c0358240c0e40f800921484550b441609541840c9080807940710803060070007050b6131152421682c40b4482c03420b140148540d141c100e83c886101403240292b0700d400301e8622018101134640e00c1c6191f40f41070904846840e00740601216018081001c1e000e50480d01c02004460100d13003115a00901c47c0c0703052803605040340d004003034541081011800c02c2c0c9010404006000c900000660007906082c0105013504d8256079100c0e01c24400c082c001c040003051310210b6034400d402141c441807e050b00d80240441c4c0ca807000c0d140d0b40da2801003000c4001800c18440040d006610b500008141c8002801600130800f0325028030640304904076080343c20a4040030200040361060002e0512000c000001603901d0400c1c20b0014140b03a81c103410340f100a200e400303022001a401d501c1c0050040d20a40f40d001c050b0b62071161990052140100c083c0c165420314400d45a81c10302256004c804510660040701020380716800c4d1074240c42c07140002020105c4d0403d003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 143760035 1250 143758785 143758799
    0x50106030903022d03031302030f1209060a0c06050403120c05131e0f060203070201021011070210020f03070605040b010b0309030a032c0307031101230603100912090905060a 76
    0x10100c40c0d0104d0084210702c403400034107107032860740100c0d410030703100e60f80d88504070440c42c082c840c1c00c4821301d818005090000034000c445001d0b02c10a508140f042200103200e454460041800c90443d580002e17040000f880c0c541800f400007000c4401103020640b0348a5412100790081c0260b440040025458002490030411030104905040c0d035000302049694034002200e00fa040d01100141100390b0180d40c448406200180c50304034440f020342030709420500001042e25005040d02d80715501141c4888001d00301210aa052601503920100e03e4000000c04409201003600a02e0040d84120103620641e82d03601102103882c002038900c94807980041084001e0240309400403840c004c188240c100050000354140700900c10558840500c9800110300075081c0b60308a404080b0091902000340309440d0310410304282d40044150820001c8500d1001c100c07a42c4040001c050005800d02007000084054140040c905642420540c006032a107900803d001c0e219020701da0180c0c501404c24850b0b5410607030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 143761285 1250 143760035 143760073
    0x3010605070f0c05220b0102030403421a03030304081b03040f350606060d0603150912230901121109040b04020c030a050f0c06010e0a05010603090302 66
    0x7034802e100188800300c2c0e41d0781e03176201d0f076070b01100720940c445400100180c0e40c20a50f00700c065a1410b54101340030800c0400c614145244039181030f100071105d0b00300d05521851207034010b21824481480480000250b203413403a4401c0065100e851032000d070301e80b021420156a84012031780217040850501c0680f6080410303180545030f0741540c4e000d1340d0500745c4072042c40d00d65a03100c4d44840600454160024003503151070080401040e210000b00741c9003600f0b0344680356a01e070003030105401031000007400b103070b203640941c881c4001d568801c55030201801c60511400c007034071090500340e985114840c41e078919079000c3c6606000c584120b00d03046040c0240c51901001c50f030002c584840c188070901c08103200042081c0b0901c0000b0303074030f41d4200740c540b540030301440304a82d01840d0b281e000303900c10040c15a00d45000825115421038a14041c0d0382c034090540c5c420218012002001c03d20b07c150000420340e80310f02c040807032003490311003010407140c3e07642c2004070191402d941010700581c00c40350880c440c10b0341d00e00f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 143762535 1250 143761285 143761313
    0x4030b0601021e0c0a120b07050d1d010608070501081306020706090212061006051c0c05160804031b05011e02160303171006120b150f030402030705060301060507 71
    0x10064450903040b4200608010f0041e2010840503009000d0500303c6142003c14540600481ea800001e0701803035640341ca048080151240041c00004a80352007400042e070806140581d00c0581c1d070501c0030118170001c1c0a05124000c000142c060214007046651050003211b10500c103206108070f02c000303261240300c000c0d40441c5094078055150b00c2c9030005600d682c100041c2104618004080310b203800f00e0040140d00c1c00740c2064080110030000d1141050320009152081550702800268024517080282c0e03031841150210300d104030500481030244961080a481224001d42407961184079000c0481540b014134000d0078041998210303030b420404c0c0c3c143c02812016104c0c1c011507960b07444d10590748140042c0c2da80202c00140c1c070451100ea4444014121a030813840440c0700081407130501e00301500031007482c81e04042083d07a800103014643c2d030352010041e0428402c1d12080e5030340c0c507003644240f0a80c012036080e402489542e0002405e81031501c1224101d51071a910306080040c550754080c20f0640380 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 143763785 1250 143762535 143762537
    0x504020a09020304051c05030c070308090c040501030b07020d0e09160e0418030e0402040e010608090106091a0102010b010f2705041b0f020601050904030f0201020c060c040911030c04030b0601 84
    0xd94082810022840154001c40c09003009010700e0703885503003409500500440b08003c1000070304c2400780c400c5c00718003179a034055810b050540304c070366500e0004c0340b62801368862658458107050000090cc42e070524281d000b40d5855003521501901840d0940f02d0040d80d489150300007a0400002c1c141180d03214400142d0482854400f00072881e020001e42564250301d49410711104640e182010190441002035405005a80c01e40c1054a00300e180c506600d4140b08000c140103840f000140400001c4d4403000c05001d24020410404500307000c4030340c0001c80000d80328003541c68000d540480e5805050140c4043e0515610864003017110000c60002c059804c1d4110315006030010003140303596a5000d08400140ba014401e001d800034810010029140445040c040d50031050040c4038540300d1012440d4441c2d01800e01c000c40c0819144220700902c11201c0e1449680913400502a4100c24040108102c411030b84d0140801c01c0001247c0d02342d8801035a035024130b501c00300401c000150310180840c0d440441 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 143765035 1250 143763785 143763799
    0x10905090f01060308030106120902060307110307140c011403100504020c0a05060f040303051602030708030c190f020706020f0a290703021909050d020405060307080304090e0c01050307050d050402 86
    0x1071011424259505904100d4000c5404001400040c1e4080c99503003800440203000d0041b80c650350085804d030300c0041c14100030041e90b01d15011030020304108079911250720516400303200c802489002d0f1510000d0301d03058000744110303030300c1c2c00c001c18044296400380b02c141c504c491a152a10f800c0000075171106c003080346140240d41e05c100102c3c20a0008910442c02403020650f01e01c0c051038001c0450304002c0512100c0c803800007829490690000c29140b02d40d9100c06410b60b40d4503440540348950040c40140e20341030300840011010030380d1142100724905080d40803100c42b03d0300d40c403040c4e8070f403500035816818591200a40c0c0002c11301c854100380707041a84509109003640060301c0788642c0f4400301c88100100350001800b90410403904800d10100f4940d02d405120181080300003048050900c03802f910070b42c0c880e03010602d655818030101c00100160400c8035070315a070783c207441e0b4054490501c0030740e29400398120542c803650060081b00e1051180d551101d10300703084140035000910014005030380100c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 143766285 1250 143765035 143765053
    0x90309050a061106060102010c0813030309350c0a02010818030309030a0f0e010f122a03060e0615030c13030809100309170c030c010c09060206150901090509 69
    0x2100780c1d4900c0903144942d12024140002031440c2e1034040c0c00341515046a00d0711495002490b404500d05810080300340c4000c100d0f1369141001c4026006114014090128404281d090782c00d0403011011000d1f00d03800741d4a03010401d03205080c0d0600a41083e40701c60b0b008403403100e0040d8030034546c640c0c0c800213000203600b202c0103151090b8503542044030700710007039480040c0e5080115000824005c2e2001c803131400000080c0c1c0180000d01c1000b0246544043c4038014008621342003460700000801c543e0140000e0540c0c191135100c90308055090741e03400101e0724100300410181502c1804920a440c09846003011007101d0491850540c0020071039986504140010f650121200040c100114012a566622103100c01c0030484440c4662001c40241440e040b440b200140c020600d40701d400900c02291620b03400f920547c64118400c42d041c94402e546480c0148000c4c1d0b8001e03540e44103940701343d0300f2991241e07580400c0c22401c0f18003240a40c0e01207a084010408019150806a80440103009a50000c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 143767535 1250 143766285 143766289
    0x1803011407030902130c0e210609100f06030c140a031e03090e0f041b0503030d020d0b09041104020304031103070b04060c0504120f02060708030a0203190b06030a09030905 75
    0x100261070300d10000e91200c54007002c0d40f0f05071504203001d0300710281c01c00801803100303001780ca00009500054010f201c071303400103001c8400ea51100d41c4c481c1840015a521072420681c2c0d1034541f041e10034042d807124a45205080c1c440054480c1c0320070b80f540051254111400c050032603080c4045201580d0344a05e8008021001420350302190140380024410a010320010385005081c8068a07005000c0c0821031400700101e07040d2826495030041c2c0c0105141006204005000522104641003541c26110018150b0304041043c3d0042c0340300c14941c032041162504120801c114040c1c243c8019150000320003100f4110b2034a51b0055421074801d00781840201d15840d451410340d0000141500c44005400c1040288004c50290042c4040c45103402e03440c1c02d040034504541c10141c02c8001e05101242445041152120001c48966542040c032050700d03840c1c1070080340040d50080f1506079030041d881d608208501300b03a009203862488001d040c02d0642c1e0714002c40600409031a0300075420804201b100252075 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 143768785 1250 143767535 143767571
    0x120a0c05090a0b1e2706090a020c03040602100f0c0518040f0c031e050c041e050d0807140106031104050a090204150905090c010807050d020715020c0c0a0506180301 72
    0x3200f80c04214540f91003002c00b00103c080441c4248010b400384408410043d100c01c0d82c2d8158401c00031240c0d220591075148d04a0000c1c000d00310110038600c40000c2c04030785c0d1500000c0315086000d45200901410001c440d143c0290340820b140b0b40e010030702c180701c44d002c140f41c0714104505807400a0302c0081c2d0b03040204a0a02912481000d80c00465581d40031050342c0290043c0030042c0c000840418000e07410110480030307040c8928841d003c1d1100b03804181304074040360311004d0300040800503c401845a20342c103050046602c806022155034103032040f01114200c060007118200c075080744800c00714407000b10900c4042c00c00108115240303035981040b84010b079501d1090000e00c2031000c0e0315282040c03c0100c1c0da000c0f44c0b800341c181503242e8440f415081c1586e90201000350700006d035151054a0707525030081c1101034003502130020311591003080c0c1c40034005040c0d0b01416102c0c03807000884034824550024400c0c6520240502504031f0307010040c00070501c1c1c1600740139a100c00050000580101840300407000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 143770035 1250 143768785 143768809
    0x312020304060f180206030a09020604050a080d081605040501030e100f0506100201051909020120031206010e01090308090a0308040f080d02060f06010c0215070b06120a0c05090a0b 79
    0x40039a52110104183e42c58401c0255407a2140f0310241c8000d555000136807540002450302e968580c98224203000c5454910645001706400350034030105a48541c0060703140d03100781e9117200000e05608001500c00e10074022064810800c1e850700d0f0b01d05424500114054541d10401031814420800150101452446102d21408903c000041c641c113003901048006528400644210ba04000a002001d0040c0c0340488240c0a00d00002034108070714801660220b800540100d20355040b5040c41c8040305021000344801462000b4078981640c480b0015100303904501147d9000901c03070241400000c00400c021f02e400c00c40144240441e030740d01e685084241e0710681010000d00c001e14404c010b0000d00f0812611342c0b060300d001800c1e8a14050368141c2c1f04141c000c14081c10801d01112030000d6451320107150b010001d404061139a074404d18103087c1301c1034a09585540c085c4400d0940319044400105000c11942e9001900c14841071810040026140f8040d02000d1b540b0340d902007040d0355a07101c1c09040c0c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 143771285 1250 143770035 143770043
    0x506090606011805010e1903050304030812010603090503270d0c05040e03160807061407080402090c09011d0a050301091202010b09010f0501030c02010b06270d120503040312020304 79
    0x60501c1c000000520903481c03072072412160090000248542e0381c110301040528007041e6540e41c05040004500700c6a044207900203040781c000050301000340b1000340300030301410040d4000900c0b941d0fa1100c04034215181d40d0030241c0071380c0060280c213500b820020380a07014030701e0050f01c070f04c003a050840000b50183c0150400314ad050b034803014200540e0030180a0b4a2000440744040d42c01c00d6030803202200ca8520520b00240040c400144207010420701d944490501310400d0f602443e18684540060898030094070180e02c140d00d8400080d402e0250341c3c049540d40301042c0d4895003050008035180c1d00124211034034962003151a80b004c2115102481082d482900504050380000c40340d07800682120b08004410b8052445240140901183c0e00044000c40e8020b28000401e0038907204101d0052124480c8150f1050001950842520881b0f14403030745000b02030044042c68000d0384c100002404100001400c28030b00480c0b03904900d0203640915030140c000d040081a200c0d000340d0010480c0c1c0304490441d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 143772535 1250 143771285 143771293
    0xe1614031005181606050a050c030f070605040506180c060c0a08070606170102090d080c03070f0b0106120203160305070c060e0601090b0f0906041a120102071205040f03031b050609 79
    0x1400f0240c0800411003100c4800c0540e04c1e01c10f003010001001c51051400351010300c0320015514016040410494a0008e038401103a5224000b5151400c0076020680701a0740502c18080824541c468410b0084c034403c525000800341404907200780b00542d04201d8441007240108449080420400301c0207041441c030034840003454a0030492519000b000c01c48262032140e2061100664645414401003d6250807100c0603440d8444900d04910b0b5105921009150000100c46c001c10132030700c80000c9042e10401c3d1591114840c5c1000c510040340000c6400c84280204202c54194003400b03540b000350031038002d00d4608140507080e00d4042c1940c0045070044d16540c0a000100f1038941d40344a0703400826012a402640b402565002a015960191119114542c0ca445007501d00030403d0440064010103800f648071880903214540c000c0d0000e000030764030740f840d00401c03103400c52050003268155034480c0b412129403410f5031411a480c1e0309122926071048000701800000c02c200704102c80c403400c4144014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 143773785 1250 143772535 143772571
    0x6080a060f0e070201060f0b0906030c1b0a020a0602011802040902010309231c05070308090c0d0c030204110306030a031b0b04111008010b0d02070f0b0f0403030e1614031005 76
    0x38215000c030b500c1010000003148080c40840812009c4600e150800c071000b6071a030300c5201154030603204072b190900c20b1501c1c0b082c0250074400302141800035213000301c03500320440d5900c04c0700781c0c01d940308503100303030310191118010500524007030f0f2001403000c0c018500001c0813032241d51544070018028040004425007c000c0404002007046a44010071008102500006903402c01402d680076840e0000d0501c07600030b0020303c4171001048035100d0f008004200710b800c09518100f01c0740c030304524003060740113a0401e01200c0c4248002c07411a401410054001c040c40e20045c0c50480e094a54030034184441c8060400d424003203103041c0b100030301560152001b84c800074840000c003c0081611071102040c8251400108100e10303010301640c40d0a52455800340c0d542c02e0618020313481b0707050700d10024284149841442901500c00c0c0805102d1440b9031010880400b040181d036658100034888001a80641d140600064a0807034007103001041c01381c2240c1202210030700c000e0941c1e2007140c035a000e09441c8220 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 143775035 1250 143773785 143773787
    0x30803070c0b010515030402040e0109050d030212090f0c09101805090c0906360406020901080907080703021314190b12060f06130204090204060306080105070906080a060f0e07 77
    0x10b55004044c2162050f00011030f0b075003405414040103102a01c00d80d510340314888802400e4000c20320155010341600c40150300500042c1c000c2d080443c0012031b490401d03000a4400b00002078034038015146100038030b10104210100308600c1c0009102c0e07881c82c40c4c4140f0000709d46002c0c3d041a21800e07000c180108451511805183c0340c1403074404002d00c501c0f54507051101a80303a00002000f206031152401c00d0035000d044902d0440c8455401519040380b441c8100030038402c00343d01030501240c00340c1e5202083d889610000e582c448950107980504d4100040400c014604211091a01c40d00070102041c1000d43e0715000010340c43c00c880520030460303080b8010721080c0c91407003100001c01007210034a4000034070451981d99544010090122107080c1804103a20345d49856082580141c50b200c290356454441743c54030701031740080c0b0541020906100b800714007040f060058900c180c415645100709549050b0040310290350140c00307100c0042d582c14002c07880480c040e0b1510054822028001118100200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 143776285 1250 143775035 143775053
    0x1101080601050a0804110105070206031509070918150b0a0207140109030c29070f0b1b030f060f04060305060414010509100b010e100c02010f030b0f1207030803070c 72
    0x5464100802000750001c003513000520141c1003500400f00c40c826498020051750700303200d0341f840a913000d4404010400c14000d0039508400710703141580c1020250f00c0300384060700c00611030f004036081d44c0d01c024400e000310381d02580314071071062101c14041e046903511865040641e00c0020032000582083c0804e1050f441c0c811103a80d1042c0f130a10f4011985803035501c41c5818081e0324010b224101e00389850100141032560740490010b00384090503581c07820b4a107072030441344020f00000c4540c80703606800034000400c012844c110090462494500c0c5a4030301e18000c801030402810a43e0103c1c00c0da1154446440700d100d04e1001e107100d40c005081c0340c1404e0a0080000f003540322085203982c104000c2000303445002c20070011140d01100c0225051100a0041ea200c0c80d114400c9600910306580200344568416100c1d00102e00070f803140380c0c03001c0340548110305866101c0c540070740082c02403156146a0034200c9405001031a0f110035100c0a6843e95503600017a8400c0c1ca440000818001800041c132050f50 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 143777535 1250 143776285 143776291
    0xa030b030607170901060f080a12020102120601030b03070e1509010801090f1212050709030326060112061a210103121b06110d0b0f0303070803090712110108 69
    0x30010025031504150040c400300c0003494a001c9020f144002c00c08500742500940301605001e0740010051307884c2c90801d030342d803134442206840c0f40300d40c607143d000d404d8010b20846000141942401103a40c1e0340d00010340180a81180f0144c1500c01e85600042145c85041d80342c0c040d04419464821801423201000041101070b00b0580c410303458003090800207070b2403e03081c1a9071a40180c4040709115440c805682024540340846802418034007080740007a0700aa07108142d0f803094031a0f500d100c441841d000144e02c200765590850450510100e0019070040c0b03036003102444041c20114540f40c4800d03807629540064002d10000e801e01060540440e01c00384111910460088045c07102e540c515115107102c45403d0000805000c42543d1743ca040b003500c094000300fa80d030030440900400441611141070f503440380c800009030710301d489520706080c64441c03100c17260f0040c0100114280022512007a4043d80003500b404505d104501d0006155040d2001b200da6003400351441e00012400c1c100017402c000401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 143778785 1250 143777535 143777539
    0x150d03120c021f0e070909080409061205070e0c220303110a0c0b090105160318051009030204050c0919050907030b011b050c0312030a060807030302030f0a0306120501020a030b 77
    0x301841103400c14201e8003c401030404034001107070f4a401000c0040c1803800542003003040504100c402801d101c800b50042c8102c0f28021002c012407039403210091580200c00600405030f402c01681003110030296044540c00030500300a9a00c0c0080f500c034200e609240c003c0a604420784181420000d060b003100340102d030183c01d10007070003040200e075440411081ea140614040b80c000480d5040069201e003082d201c130016032500ba104140914100501308140e000110006501c8091000c155810288030000c3d03886841d8903030101a0f4150ba00300809408020305000001001b03010800241c1d607205c40307001440040c8028040c155041100380641d002004203850145810200e08120036640700800364404000380d003080042002c1803030450704020384000b401e0381c14411440c06100490000c0001d60040806d403800b0003416940701a0940c5030051840f0241c0541c005021010501010320000c100184562038005441078a50340c075120002840502602d03907a42c04101c40760280c0e014030503600d480c0700c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 143780035 1250 143778785 143778793
    0x1413230303040e100302060c010f050901020c030406050d110a050304110f01200124081c0e091302060a0e010201050a060b160804080703030c0308010603020a1403150d03120c02 77
    0x101010a580c1d204620601c00283e280300d0002c1c0c1d000d1401c0e900c60740990750091800356038461480720b96028159040c840d00d401450040030a803208030510031a401c0c1100c0c1c0002e1030420b840c0010540300d46d082202940c0c00d6503183e2600c8040810994000d084109040c1c0324251241064140001607841d0302000c00e0083c21070000002c0b07a41c0e0050402559204a110612008900038100c7c9016001e242c54070100c007030140030320b21079900456540c907041d600d10804a40390041030503411420404a03c10780400700b514515204d506080080d4843c2c0d22050307a612070344600b00b20303a0100e031190b4080d62100e8001090309044100c90360317080c01615042400550240060382c100321107150343d031041c44032140c400740b9844a41c40401c2284c0c01550001c020141c190b501c00359981c20051700c40e00146c10128005020310b8004a6020301910907150134041c25524074100185a41d03d01c030131680050544200410300b0b2241814640d1407920f41c50480d44640d07203d1a04607204801c10342a50443c0740401d080d500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 143781285 1250 143780035 143780099
    0x13170705060304020414040302010b0f150306011b0c0602060103061b0f030c031409072c040602071a0703090507090903050304112205010305060c1602010e011413 71
    0x500141621012180c0302c1c2c0c1c0b61150310000d0000c0c0165000f01c0d2100b28444200400c1c15011340c0644030300103081d581203041d10301000811440340c90311801340c0b448807020b04c0030585651040001c41d0041061003004254502c550b101c28140c0c2e201548403a00580c01400184108841400740004040c9a905041c11515503500c01500044c955400c0d0f070101035440031001d54041c03003504101e0007c0481000070006091454100d03860340018000c64915881e602180c080c03900001190000b5900c040041346c40d44d80766a990300020750b000410540d48044030301a40aa4102a900c803540500c20340d0318009140240c910b4041c0c2000d0080d400822694945840d0b0000b0940000403a40d100381e111280040003130b11040040c600c119904450b600c4400a82c01038200902c40750711003816603014104035217403941c0d8051140d085105865071003412601940f880401940a21581000c00205041115034010081603481054200100c162400b03c500f060421540c20030b9442c103d108281c055078244041c0c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 143782535 1250 143781285 143781329
    0xd1b03020703050703030c1206080304030605060604030314070203010f050a090203120a05070204180b01120507080619020c10110403170901080f1503010c0f110705010f0e03010609060b13 82
    0xb005031080a17007031580316152400020302c1050316088480c41050f0400c0041e840d2030140343d4940240c04119442490000030651a1400c00c098a040f40e50660b01e5803180e1500403201c00540e04044412600b45d03403682c818040c031904038080c05e0b206842030100021064040e00405107007407001400c0d40b019590401c0702c1400d80d907020080b500050b805807400b00d56001404400302420a0502c0c0280c000c1d0400d500110301c9584c0c45009180544c014402c6032421074032920b401e0b0f2a0281900c100c01003103202182100c415071541c002d0b140300f942190a84007200040100c900990707011094103146000006810300420000c807203c04400c0c5401c00103103013042c1c0b440b000a4040c0f400586541d0560206000080f04985a407e80c207905c0d0704068002e00044000c030300c2c080c1c6014051540040440d07000f0060b8000904006500c3c0c04541050303442c2c810a061144040d2003030080d1002c0300350995228040800c8c96000e42c02000010701c5840304250396030038003061800c42c0003265009030300c4208078510780d10480 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 143783785 1250 143782535 143782537
    0x601090806011a070c03080714031c050402120601030308100e090303130c0b1c1404050a1103121603090b030103050a11010507021206060108160816090b0d1b0302070305 74
    0x25440000c00e44003c40f82d024079001d160b0051402c010b0001e1071a4002004100c0b4040c050041c0c2803141e020031003d102591a842e072a409480c0f0f560020880e41c02d40000d0641036504000e801c207002521410315808014141402c1c04c0f001d81065000c2104403007030000080c40b800d4140024481c0003d90300043c03c10002940d12480040c0001d513020007560300d0001444518800b0304000e10710a0350301caa9035007440e55800300443c4200340c1c4100e01d626055001030100026001e05109503030002c003528981c005990362000c3d411812220301d80500c80d11080210340e001c404010800b890f0210f101c00508601450020314141c5507400000e050501840100f00217100001d1000b00d059001070416003002020004030307014081c0d600c3c0654040d004c6140a00241808250320380189800e90350001d05586100140003c420150351820000700d510000840d000c048981201c201e0701c0c2482c01c01b9080c1c1d903030203101c1d01e607800c0148103018090b80c0d41152055041c203a80440210301140c05e065040032581c1d05c0c00792003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 143785035 1250 143783785 143783789
    0x80a1401050907110715140a020303040605040606080a0303150602160b0c330a050601050d05040512071505221b030503040b120c03040c0303110c03030d0506010206060109080601 78
    0x20301e940d00c0c085140f0074012440c1d000030b20842000c45080c180e131108001450f003180002800403d6001d00200c0798604014200e03a140d41c0150015440c584407079850200800c4024400d440065490314040b600c88014800400401d000ea5000308a1100e440e030044403100c1c40ea4403403810741d401284402c21400d0501100d20440e000021a15116103403000c0301c2d81070403040c4819a040305075500e0b44001180300018945a1045200c0c4e00140550711241941c2c11681c0598500340465001e01c08500180c5440d0042c0e5402031055080d2603404144281c1407101d0340005804403080d083e40d0104007510115807041c250300c0b81b407200c2000625403840c0d18000b420604420058021289118044100740245187c9401580d001040b6a541c50381d40d500000c01d40c0200d05007160807030031000402c201481e1241640c1c041c40c1c101000142e0300d4035650b8141c40c01c0000a4009283d4003d0100d1002d1968060024100342809503c001c10703a40761000009041c0380c0c0050005041c0a200c103024403c2010000700181 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 143786285 1250 143785035 143785039
    0x303050c12011503240305100c09120816080306090c03071205060d0b04050f010c0c02030c010e0307030b090105070f020a030e010e010c06020c1507110d030f0b190501080a140105 78
    0x100c0340e040e03c28110043c14000040c1030086100e0002601d0038032a000e958000c40b801241641e03216400d0340c4002d81950342110304032001a02c003840030701c8001e4030519400c840c2d40c498ac00641c03524280c01000711903a08401c0050f00c240300c0c044208946407c040080c903074015044540e9510f1841c0240c006000c81d2004100082d4081c0c0c3d41001030300303a03100c0c1103281c0d916942086642100380b07800e1034015650f03a4606007005455003841a0740e8050380c050300d094000700c0e6009000e840b04084000044500c0d40701c00405c0d503494810038100102181c0500f420354054449103001103614600744801a0085158005c03d80071944101c55420101750b12a800c42c80b01d9400f4685108030800c4400107d42c224528040500300c2032001030100200b130000140000d44551440101045540c0e243c82640c090147d50030002e102d1300029200c110440c801d80c0803080c0840640e100044039004200031600d8240515420708044c40324101c00c0c0f0031580c1100420f50f0085c4868001c3c4032014560ad901e130000481849028 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 143787535 1250 143786285 143786309
    0x604050d0e0d02030a060c020f07050901090c1b0503090414010b120604060b0c0708010b03030a050f03060316090b0a0e010f050d05010e03191e080c07110406060302070303050c1201 79
    0x200c60b9440401411140c0c0e0000c044818440842c00c0900c02031a03041090340151040c100340503011407000c2548401c0343c40041040c2d019030710740484a03010781050ba405004004481100c0c00c0000101100300042c28004e600440d1a501444140030481e4486170b611050928201c0040218901c084110307482c0050041c801f4145e41c5844001c14050001c6804c10541e0040101e040440c0d09000100b01080b00c007000028000400c420051507100c0c45080144070005000b00500b5040d1204040210342182018003110781c820780080e481a900e142c10f40200c0d07040c030345801204ca03451416a041d071010303080d2100940b0340d65242038041101104d03548603a030301030b1012091000901200303500044000100c04260307580c4041c0210321815a4841181c00404a80300203162064000783d07007100e01d048141602d80c10011385804071038101941060500300e030045008503986d0526100c60007800f00070b24454402503126141d40c90040d042c0e81d4010901e9866140a2004000410b4150402c60444400c51250 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 143788785 1250 143787535 143787557
    0x21207291216030b06031f23190b120901050601110c100c0b0408030402030f030703080708181501082b03050c070602030f0601080c0702030c12101b0905030604050d 72
    0x1c1e0050403050900703c2d8000300c01b0041000098150500b070400c00a80030102d20900e444428051140c0040340380e4100400c1c4001e4501030034148914202011040c040004413900d5490007040d25603032041e42038006402d498420b00c03401200074000c503034206d1000d090007502c0382d46186141d5540e03000c180c0c0107803080341a02d4107158654007400c2000203458104149070040e14003814030850350740c003e480480c040d10441181c03059502d8007006a070411641030740d40c01c50750b0f12070500484000e14058400c900386000f0310780c00c0302c020800b000202001c038207107654903840d503141542a6040500b6030a10390b00c044140e60034000c01c03402c0001e17920101e00082c00c00280b5078440c41c503054414015688010920f910020910543c195001c3d405845510244e031141120380d520411201c43d80242c0f90b0080d00356015502260403490001e030440c0080300c0a10407150300c18038a40302c0340f042d60310120030f88042444d2152038054159000342c2c0c2101820040c0c000b080e00c0c0c103040e40c6059540c103d03070f0040b0301004034040c41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 143790035 1250 143788785 143788787
    0x14010f0e0d03200f070f0f0b160c0b07060f060807030b010b0c070f0e0f131509060b21120c030301060318080a17010801050105010e040504021207291216 67
    0x8100c502006880c121380603039044441059507824540960491b00104410000f1160320388158402914500c1d12000d040c0311031103070074075810003c10500b2103d584004201040d0401d19401503c0d4660051030702207a01113460100408a880c180c10400c0107800400090000c81c440d1140c00e0304603000c074803109a503603950300303140c5040031100c2e0019440d0a000a0000809000e140d881500526160400b800c654441078051070300700e06241c03c000c20013200c00d4100c0308500c1c800d0b44600040f50141c400401c04c0c10b150b0002422012941d0741040c412480c100b44286525002c118035442260320356001440c0c20742c655407031a903078001441007400705501c480c45184803c280350091010203030f0001e42c030f0f40c481110800203072104900d00016000c0d01c9507c0000034400350140515412501c3c1a120352008001c85c5c4280006800001c1081c1e81003400d1241c03e00c564107080000038018045a440a0000711400791a40348500403000c1c6038590080900010340750f0031141c680c080d0881c0929840390180314040c94 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 143791285 1250 143790035 143790077
    0x30f0c0f031306031401060e0f0a090e0a052503020d030504030210030e1c0f050a090b030f040b0702060912092202030702010f0e1902060c010614010f0e0d03 69
    0x9040503580c0000300340030300390301c03042c0c020801995016207042c04810f1643c8548800c0d04d00034415440011401d44000711142010007114108030005801c241030a6250260303001600c268500158145d07110400d0442404801d100103101941400080203405080c2c140a0f1408801800080c2c460742e5003e01d603804043c0641c044600a550142010184500041003d4000c0c02d10006180171030040b40c00304015040301c42071010205146403141094100420f50440d001d0b040786201d403041c00f84103103000c101e40013188003030742c400c00c0d0529042d445407070a07142ca1510103802420f070700c0640d8030010074010440c02c042405802018142c1300280c4403a007100018140615051202c5205060003112244001d00e40c1c0081d4814040c94000703000b030808070326100084805039244140b00380c000d1003842555040c505042007145000400b407a0409030002c01c036508492203075018540740039011020741440e58015100101c8450300e420850040003120003c80d03030f007070a013030300050421a51f5000b4032071980c204a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 143792535 1250 143791285 143791303
    0x10b0c0304090e0102070b0f040302060c0d09140309210a0f02010e0d0b1f060915030e0313030611040302060904050702100e0604060e0d0c080d0207061a0a0e0108030f0c 74
    0x182e018808040d0410003107000758017888003642da4041003000aa048620860041d0283ea4981d000b845c0035542e00c000803807203811850042e0207150304c5001d4500400c00790620100100c5407100503560f625003590400000a038107545030701140003000000c10020201103000e04007a80c000440031b184400600c0100e031f03440c880c3c481d542d034040318904080d0300380100081205d01c6145410f1001750070031a80d01c120f10104216104c2c41d800116100d1080c80855240c035002c102d00c0c4201e0402186004044481b1810364024105008500c251401c8c104203001ca00d0046006440103010900d1600381140c02054451041c9400c00d806103448002049410348200b24503011f500904e40708201744409100ca1548414060300c05466050401c10611000781000c2008480985181c40c0d100008055a0702c603021504a03c5039000d58036402d00c03078900801d400e4006ca00d041860b00030a0200c0e84a08010003400d2131039a040880000c01040060082c0340000089130398420038a8159921011310b40c0d4800d10f072941203 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 143793785 1250 143792535 143792549
    0x30c06031a13050a0b011806110f0715021c0e1c060c11060609160c2a150311030105041a063405070303030c021c0203210f010b0c0304 59
    0xc911180b641e189036211500561401c070302031041d40455801100c00798016020841e60000040c010003200b8007905001c0d4a40c0c2c01401900d00d10055100d51500b0302c521544100e810ba44590342c14240136605001c4008000c840001c200c51800800c2c90003080074801c4c00c0079501954620300302c40704141d407007860010101e9114005000d004d1880c0c40007083c07650300f80f8010015100c5d450124030070b40781110a42d482444001c3c1d50060055041c030048590b621030223420f403036500c00b0741c4500740417090480c01c6804900c0305c0000040f0061800f203640c41d4883d1180030701020980f4007a21a8050300c40360080f241111821100861241e40d003c040c100803c420040b00c41d4006800a641c04010001410358070010010840070160303070003124945140c0401c418002040c0303811100003800000c0c0280d0000300244424411079600c1c64070f00303018209400c0c10320940070141e800814403524944c1c860700f0204c290224400b4803030703a40c10806841d514803107042c0503a00e0041e0011581c1d001d00602041a07400802e00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 143795035 1250 143793785 143793799
    0x304031e12090c0609050f0306060f010c0c0f0f05030d0f1202040b070f02090609090a03030207080403050a05070504050108010b010504170312070801081002120402280e01090c020106030c06031a 85
    0x52030f10b1074019001d4441c0030081100ca07400000c00d8a8055a0300c002880302034060805680c0c1c81c41000083c1c1000a5880c0c14418210344001c00b061804500002601120340860051418007503861448052544070350300c6a44440c0f840000554069075041c0034400d1814403c0d90510481081c0d0085c1c069608a130b4200c41d40850a241441801010b15a81500a0b24001c51036101c0c8014081094000c4502d00416486840d080000910030740c02885100c0c024200242040d480b507403100d05042200d40705540fa9404020b06101d41e240c02e1258070b00400d0450001c005502003100080d02038000c40c82550844402a80b220f603000c1c9050003115103c11442d141c50280d4603111401402042003030180114900c10b40014404c0b2101c14403c4520301b60388105802465a00c0b80e0030481000032030702660b071103090141c0304004502804040d2202404400d91501107a40c1400c50080882d061601c0c25021a0304084003000030070f01034040401034611500c1d021599855041d5040b08540e440b402050300404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 143796285 1250 143795035 143795051
    0x170c011809091a070306151d090406090605070f0f0509120609101103010e04020d020301060503010501180b03160b03100e010603020d0c031517010912050309120304031e12 75
    0x3603a0030f4543c0551288001c0e400b50f071038142c07007103080b84c105004120b49403003480c01140c100c0d03000c1c400190b8400c1c030714490b181d0000389800106000301400d4402310361954a980c661004c0013240d005060303101c4800c2ca00102d612205603802003011962800301014800700190a0000740c13590006225208451021660f5a00b80b100600c0e075034940e464400d2100340c1c5000c01d24070040b111842124100d4580100100054990b41c00f04405001c05040480c0d26658900e00000d21352403e00501c1d009000e4a16012520003141901300181c03203400c04058847e8100484c0c00d040010003141315015104555010341c1c82e03594407030905501c611503411550910910400011354207a154005090101e03621000340010004d904003907054425502c6c2d844450303803a0071414051401280341042d101c0040c04004228030101c0e80790151400405020140000d100204001d94854204405002613255990b401c2c590300e05034800500000030105803810941001c42a540740c01d01c68102002d90320344280e02000f603c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 143797535 1250 143796285 143796293
    0xb0d080a050c01151d0a060f090f0213080102090f03060609180f061302011e2a1a1e090616090503101b050705120304020d0c081006170c01180909 64
    0x320103454101c030617082000018000180a0056108480801142111481c00c05d451000132700340c00d82c0c00040966080c442445503100880740217009000c0c1c1c00c0010383c2d504c044000d110401c1d081180b558002d81c009000e200007070f2500e82c5100c0d0f0000030100000001049a02d5880c00c1c000d0420042c2514400c80c030071700512208240f6040100c030300c02d0702d585000400d10f22800c40e0f0280c01c80211008904032603018201541c03074007034060208465a0302c2e040300b10210b90b1101d103100006030344101904000c40421000562041c4069100e0582203042d541070b14090101580c1d50340c1c010900042c401090340001240380c050079158001d0400202940c201548402e248001030401c241c1440a903414608494880c40c05503080701c040079000b00c09092031211414001c0da081e44060000c9822001c04a13150700403c0f0a0400100680b00b11800303841c2e0301d5088041001550416000b00343c8d40e0700104805440480c0005003215251000c0c2800010f40c1010064131001c020340e40e1080da0b042c0d00300040c220401c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 143798785 1250 143797535 143797559
    0x15070609080a0504140906030a0f14011404150b0303070602091f020a0c0e0105030307031419170705090a050915030d0906090803040608010303050f0702130b03010b0d080a050c0115 79
    0x260b21910243c00061700c0c0c800800c802c004080d21a140c140c5c010342448004a0410113202c1c1c1c001e8001c418151580118454040c00c6858040c1401c2c2c90310740b0001030000b08245e6040e18441d881c030b2111306110700480800083d440303110300440207107050b60020348800d807a1101c080b49260f003043c1d030850002d800d003010406500d44000041c110b91f280c4983ca40400ca5124590340b090580f0b034003074002c6082c0901c580c0c0c103440c80d00c019540090304403404d100e034007920b0f20102c0110180152039520030011400d080703601d410001000d0401030900000740680310464854490312011a0401c8400041580f200756050080380d00c8200300a4040c0201d80d907000c0c0f102c0d00f00c40c0290844845941d0844c41a950740504c030703240d0050340101000542d8010040003c00e118401600c03c81540c1807500d440c2100319800249030500504211035295100c12000e10380345802c1c418410104030598001d04030b080e03540e8486c0481d1280b1072681c410301c640811003440b034210035400305c4d140c0308000d007100008079112821200d003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 143800035 1250 143798785 143798789
    0xe0c0702120f03040501112508060a0509030f16020310200301030f02010305060a12030f090608130206032205030c1e0318060f13140109030215070609080a0504 70
    0x90445024001141e00c001411a030305074001e5015500303003400c00c1d004545040081c00655078503c584200d0024444100d074445005c802041c1c02c2e03c1400f4505003119003004002803011741034516240410040003008401c80e60a10300720359640350340781c00c140200c2030a03c100d954007941510a1403440c0034a410540e04c000000580040141e4070b103101038074600068402408000c10407011440c0c0c1c6c80055000f60401e54200e0030060040b40c0c011f4a071040c0c51004508001c00f980001c40d00340541031004d0300305103080003070b109524100d560351a020070b050500c0024071134000c0c0607403030010016404089078008520009100446118500b00d1824000d035240c00c920141c54143c0194a02d01e0104640184d82d82001c20b03886d07000c0d42c103051151040300f013200020211950003030010004d44c034484805030000d20813400ca0005400c5010304000c03142e804540b92580250502c29001c82c240050380c0d45070a00c03030b004188103031140e950b24400e01d0014003400f10a00001d000c840e000c246031040c0c617084000703482 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 143801285 1250 143800035 143800039
    0x1b1b03140c0d020c03210903010e0a08210114100e190317070b010314031207030e0c0906151305040c170601081303110a0210020c090a05011a0c070e0c0702 68
    0x13a46420307104041d11582005c100d200c00d0440522451407220341400640701030003005000046c00320301c0e40d426604010031014100c48190300004d90f02c1c00042d00e04c0700082c0e080981404a031441d810a02e04103a400d1448145500c1200c5040c15800a039100d2540340010903800303450400c0191810a103080520154002228910908280014054000800c1d10041a04003208225907445c503110300401c0e00058000c3c118a01081000f07045002d14004944d024802a40d000910300401e145c6583c01c03c41d4400d070709445403095506001c0c0941e038102001005800703c1c40c00c03981d030780d4240101100300c11142e4401c0340c10a003408280b143c455008813809680d040d950401c0301c11307036698100459804404882c2e1280d15a01d115901c0c010030311074807849025016400449150381d000d900041c56121011114200580c00580303c000d80d8103242c101310b42c02c88040d10050045506200035a40f8060144080d14401180844c803d8441030301000300348010848103030742d03100d21b09004115184039489400164 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 143802535 1250 143801285 143801293
    0x20a030c06230a091a12010303110129040e16030506040b0106030b0105040317070209010801020a12021201030f020307090e010f0b030c1302090f090a0209041b1b03140c0d02 76
    0x102c0039580c901d00300c41d40101035644e104d00490038241e441145c1c421008014030303140070901c00d41c80d10007114501d0710301a5002e07481e0024030455104180f800c4d10302c0c0000300036294184080806421140d00c2e4614070010049402207a050340c4c00700b001e440c0040494010401000d03440001060000c08950302d400707240210668806030380c86010540540750000106030015404000810219003000351001a09404c010b450740b405846800007000c070b480a030031425440c0d5000a0720f4111300d804c801d50001050301080c0550800540380340414103068144809481c810700925108115901400800d01501814604000300701d41c9604c8680200741c5240b402400502d00212030245240020f400700b0f85190061020017202d01480f00080690420007540750441840304030340d1aa5520651200e10a0920140c0141c03110040800c000c1540c80340041040340585506040c3c00d016840700ca4800507202645907542c24440c1443e003140c00c403c032100d995103400004107013805191004030340d0500d090071a41c226 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 143803785 1250 143802535 143802587
    0x1b01060315140903030622050412020d0e0901090c02030c030a08070905010806030d030e01060504110d0c0903020a030308131406070801080105070207050d02030c03030f0a1106040b0a0207020a030c06 87
    0x2104910700241e916040d60743c0f0900008013145090b0201d000d0807803c2203111f004007410b8500078400e88009480480c0c0b10800041030140150781040403c0d440345440c640307100342d01c00a5012901c412410302030003c0107504c2d0010300000500030001c607600c032500d40702200d0761134118840041094900307031040c00c00105a4080094250b12404072280540c000602410100b2040034080e0010040014078038899502d0301d0303002440b650b582c03040b54010940542100ea94100741207a440440d00105501b100740480408280056103610341020240c99150600381072540701c080240d2280c01503480011710020640702e0a07c0040d1020032018042c00a60300d40c864540d8842000509994049034448010f0340919010481480e02e001c0402c881d90010b020345080400380e10101e410b5500c4103e007000102800610b95038040d03032004144101c0328643c8080c200f5400c00d41d0752905005000351101038201d8000c01c0c024103564601441c000250382c09610f074004203079a03000140448080100111848540150f0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 143805035 1250 143803785 143803811
    0x50607030c1706040e0f0d03050615070308070507021906030e0609031602120607030510080703030c060c170f0a0b0306100e0405070b0d020702150c10021b01060315 72
    0x40e942401c00d042d15500315041100d880c103514550024206a8807079112801074502d4903041c8801c0c2140e0754908013900001401260180030b555002e410b09008030b1202c000c041c0310405020030383c0c8541e07030305143c0780c20340d9250244100e41d140541c0c40003940c00140382c08040b460384803042c6842c1c02c84209840601c01c2012202c001515200202d4641c00150001c03c20303140300040c009001c1c010580f0040580c01c48100926240e494490b040301e1300c601013030345d440a10010050700d84c4160001c11003030740148219419030740d00400680c0c003003800a00c000d8440c6c83c2c440c0c440c0d01407908454082c6043d0864000b03880e00f6500d00000071019580061111300d4040c0c0701ca928100800d003030384200c0510003141041d5241c00d45e064040000207000391564021030001044019005004140d031a9102c20007603180d03406401041900d140e825024041b080c802c118940391040c0100301c08650107000700b40141c03a01680c1c3c0b1101030145d1070400c0380304154a404400f104100000d0505014080c0344003040203140f0710562 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 143806285 1250 143805035 143805041
    0x60203070201120b0d0213110304060603030306080607120c050903010e0a030f1716020a02120a0b07030207120309031e03051e01031a060607020d230610060c0c03080f040305060703 79
    0x1304040d08408040055000f508101403454607681032036100203130396117490091207075642059070704603206510b48200304245580342c000e00300504503d401030304131400c0140019010543d901442c1c07601a4071a802c0700410740c0160107807481244090028402c0914482c84a5160041d150084012800c03d80d010483c5a02c038201504584903400300d450107d0b122070380d411b4146c40c850550801144564040e20300140c45145050341c41c1d460900003010403120f6464041c103034241c000e118008151040c4407020100300c8410600140308201d0a0008079810399040803030750f00340c146524035500008045415420f0b58142d01c841d2248050100e914083c0712102000c0c2255902031202400541d1000540c800b410780703690308603810900080c909031508001d940400c884140b403480c103548404281d0260306c02c418041e10810500c2c840b01c000b44ca203515004500c071000d1105401203000b00300c9005440400c0203440b00c05c04002e540c02116003601ca0902048007615175015000c00ca07114000c01003c43e5426010740 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 143807535 1250 143806285 143806301
    0x130e100501030b0d0c0e0106021506091302130203090f060604020408060106080703060e0103080415090f0b1e0c0610060c05060402060f16081306020f070e040c090606020307020112 79
    0x446401145030a004501601c040c0070901e900070b08003114000024034201e101c800410b903103070721100f640d8901031019041410840525074025122410810203684403502ca41e404044800508042030320390010030080c405c1e498a40003c14400802e1181c248d074009170054500b1400320840f1869030f03c03241840164011441881c0040c0d00841c01071004070700a005555000c1e0380741c03400044590742e4040e4900000420f90080c0c5030f40600007028800e03203005180320541200a0b05002c20403078030300081c0d003480301424841c1d0405140c01080700a603490604500a80940742403078400d4a42c504013182a4940070162110104010044800640103000d4003080c8425504240505210340c0d81342c00340842c0fa40881c41c0348040a608205003058115404007401e002800340075100d07251140e1003401451007007203400c00d0b810344d4040811841047c000190312810344008583c551001e4031140b418100400603900941046424100302007030056000000d001614000d980f03100c0c0c0f10400c01c096100b00d4240b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 143808785 1250 143807535 143807551
    0x6050403050a1e0807060c090e100e090102070503131401020d050f1c1406040b0a031e050312040b1e131122060503010b0f011205070e0d08130e 63
    0x3000c12038000c108850305054082500d03125103105483c4569801e9044d62014030200c0300315030703a05855441680e00060041c00b45c104c136980c40e03441c2c0c00c10702d01e8085020841c0c4100c410514114000621075a420740594014540c00b10450392500e13100d103202c10f00c0000ca40500c1c0146154144a480b10350300c0012000645e0f8916200c651406280d110400e005034010301282501d41103840030f62480c1c1c6811302ca164201c5490700c20f510842e0900c5810130056640b8150050701c00c841101060002c544003282a16110100c0c201e00340c001c400c2d030300d03045085015501c8000720544c072060800080c0190342d03d880b031040804030750b100313010842e18546490230311082e10b54010500e5040910b0740020300941c1d05041184000340282d8091001440845014059005c4005190b80b9417404201c582024020000400c10480c0e800c0502c400c0140000c100d0303a0b440009030170143c3c484c1c01003400706004510315030150303c0107071140b0070108540c10481c00070341c040300342d01355000b00d400c400040d03c4c458401202c0c006e100c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 143810035 1250 143808785 143808793
    0x50319050307050414190312080106030e250306060e010311060712050d09060606050a020c040203060f01120e030403060c0e040b09130c05030d030603050f030a120509100c0e04060605040305 83
    0x10710704140e004a00c48190b284d000180aaa42d0351103d0f00c00b502d040045110382e4820808c000b002c480245100c006038060130902d81400c200d0b0100c0e10b0f0225802007001411300000d02504844a407091085019a1003e40954039010000c1400c80d01c54649605a90044180200d000a0b0005001b003a2058030006841d0003013015414171802e11501c01000101040d403400b0543d54116202d044c111281944260085640080c542c02c4450301401000c55255044400314107618104020600c40c00c01c040f0118100001c881c55188075000d40d078170100d01a000c1c2c00031a6100d03a01d92801030002c0c00114423040203e181c90705c802440340b0f0103014680e104280a801962683c41e40a0103c083d16601c01e000c07903140a1002000c82c85850401000c43c6242850768040364561450900394180700c3d1510440703e09030000c00100f0301082d00701c0c8160f0b01003011000002159681c0c0d025680c28441301d106203202d000e040070728800410360711441c00f41001104031f03401c201c0c00759104400e071105c0c401c44c0720050060304 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 143811285 1250 143810035 143810039
    0xf0f1505030601020a15050105010212070b01050d081603021515030c0f040204051801060906050406022805190209060d150b0d080c0708010501050906220b0402070503190503070504 79
    0x100c20320240d81c02540600484080204035034600d0311102100311000b0406640f080104480d40e81080b011481003040003d0901e01091501d410b0106a014014140113601c4e00e000e031001c02c0140c004480984184a1195010f441d040c600252103412890765180710f00340483c04609015003145001040c100014004c10301c00c0801c00520200b001c180001e80c0e030255003403100160f02d85503802813100c5641d1001d0307602010f6051034000350400c5c0750350700040100003040c0001e00520740c0014030741612540000b0540454008014000d01c990000d2000400501503045040f010080c003524100c1864400c032810851036075000300744003031000002c4003d00ba00303043d2000841c00140d598464002090081e0045080c441d50f6180c00740c2c16801080074018a40c03110070f0802006c1002e20034180540011900310240d410080b00180d40040191030130030f0040b01c0440000800030700c0f0703803013200c200501030001c2d5100c0405081264480d081010241a409080f210749035016100e0400c0764801c10322a25043e003464 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 143812535 1250 143811285 143811287
    0xe03030a03050c0c010c020c030d30060906080102090a091b08060406080f0604050c01080c0f1b070f05040b06090a030b040309120b1e01081e010207080c010203010f0f15 74
    0x9006890300006010400854800504c00e0003000340000d801d03001842c0c201c1c14042807520f031400c0c0850f048100001150006290070702c0541c2d036061a00b12107105c004a020825081c4000d244a600903458030b850400d0000b414072040d005041c000c0d904590301035465aa8844440c161a0141e2030704a0010603640840042402000c1c0650804400340c00000e4581e140d00361103181040d41c144100700d03640840c00304020030034100711694902d0420302c0c04101c5800d10020078240ba0040c0100501500d60100d0b4000305061018107880003503120b21700710340c82240d603001c40c0600b200c4a030141900aa00b071241104c050f080440449125400c040c2c40714000f80d2540c0c441c80c030b0803040a0001c40400c0212140020b05e400d546180309903850044c8080132036801c103081c2003100b08030ad003ea804081108800100003020b00414007412400d002c035503480268095035130442c028420740d58010020303803000c0b60b02040c49505601941c107a4450050040615442d05d01c2900c4803d07842c030031700d16804004101000c0329 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 143813785 1250 143812535 143812541
    0x30903021314160309080409050118090308060d03020f011a030d0207050d0204020a111213060c050d050d06120804060822030e060d0911040609090506131103060702011a010e03030a03 80
    0x43e004034600085c82030507035503590003e0f900c2980441c0021362214010b00c428aa618062289217038890010842450940e0307015001d03103001840350348030700014105035050500034011400034051150081103400e20001c0540306007010100810301034030515100701442d5000203000320640310000e03c81000e194295082001940c0031240f00010080c0c105d40c1504251420010300204862440300b0703a4032000360060820007500c49034084002c0003010110100460800310390729582c2107840c40d00ea541d45011805407005000d00d54406403040000c054002c080c0014000500141c6450340c1d60020340d92140090100300c40d540f401d4078403000f88011001c000007805032203015103040020780400e0414000c07041d01012a0002c0b10142c85140e542c0d4a40d40c1286041e12130f2201810344030400b0001c00403030741c951641e52440208504941683c401e8103100344104605284280d110090856000c0e2070910390003806098880e1002350358032051110200a58095125042c4001c0c01900841c00c000c0000700c22805 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 143815035 1250 143813785 143813821
    0x3080105090408120118110301231207030308090105010e100e0403020c0d030c060b0a1208031003023d080408090109080f0109020a290706020c030403030903021314 72
    0x1032100801a0a94606512003000c2c02840080740f05c03a1b080c0c02c0c000071141a0f07496a02c040340c0d600d03010001071140c1c00f00c4100d8600e09182d803d545440d09042100400c01d40404825480e50758404d040340007003090b030300040c030a22800700f82000b8002c603641c9100e00c000610302a1184540021082d00900020180e0918654440e01074411614940c85040218194070006c040c11b40c00102c80516403001d1146a00850303d02141c00d030307001c06219181c0700900e512914000801451218000041590144000b02c20806990018001d82480040f10014080c412100c0350814030000d0501ca060401c844045204040c000141c441401584c5d0310356910107140d1001160906101921201042c10b42c41000118000480c0000016072610b4900410840c010745502c2440882103000144000e18881e012407985000030341d015684030803961410308082e024440d80401d0901c8003040010a142d0f000e03a10310100c0c2d000b655242040c40344809040c0c01d50340103c20342d085017000c83c0e011600203001c0c000e030215 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 143816285 1250 143815035 143815043
    0x7050d02010516170c0115080303130201111509120f0f093010021306030509030715090b06090403020703020f030c030106030b1b0a020a080319090b04060c0903030801050904 76
    0x80e903e40c566403209903036001c2482e40098030030007003158034559109108061680341d040c0600b035549440e25121981d41e2100a048030704100030280000b046900405203032030140100300c10350b00c80c1c28844862154100b411543c402c201c0c0304050184080249031400c42d5456460000031034a081c03000303400940560712040c60290003050b01c12840b401c5424901080001004050348c1c0306482c606440303540e14044c0500c10701075041d441040110062060035003124101d58081c20b0204850f0b440c00d05071030031401140005008000c18034a8140d10200c50b90140411034440d660b10762071911003209100c1003400488004015a10401c1d0500241c42d04824440c07400300020122038280800d07001003402e4030320315071040701c860b103541d82400206400c500300001d9100c80843e00c00e041001540b0020358544480401800c80100003000c55010b07100e004081c030b180c00d9202c0050003800f4003403500e02d0141900311001e0350380c58a01120604050311401e000001c69815070740d032180e00d900b0f0404008102101903c121 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 143817535 1250 143816285 143816317
    0x4020a1701050609101410090b0307030b0a0905040f02310b15030403050d0506060714030d111801080c250b0109020f0f070f05100c09050307050d020105 67
    0x18088401100340060110060002c9414186601070098100d809003a181283c0060380d810b000d55040b144c03882e03540759011a1441a091203240055031041e200740c00001c01c041c0c00008205075190540c03c42c9244d6102070b2500e1144c581e031544118121101554020300e031648200c0244058a02078021440000114031010380c80c0903a58110812402d2030502d181c43c2c541c540b0039207a0907140c000b400c4031205012041c0c0c40d203145401ea074014503070b11410412001e155039620204200d40c0381d54007941c2c86282d01c246199140e941041119590f80c0050781c070b056506080148107081040860140c400340007031130f644c034052010140d00550b4201d4009118106c0d10905000c105111440310a0490f408102c402c4820b01021041c01c00004c1540160433075500180100b00001c2a244408c0071240e040c0382d411411600c45000d844c2c04450300381c4c0e842d0301400501c52031051503040c5443e81e001c0807541202e034a40d0341140355101c082c19180c40c640e01c2001d60103018042488c0155001f4001001d00f00381244201c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 143818785 1250 143817535 143817539
    0x809040f060f0807120f020d0f0503040303050c16030c09020f070204060b0a02060c07080d09020609030703060501090b03011104051c080a09060807050c0c1207080106080105060a0609030809040504020a 88
    0x44001c54190381e1000b02c4940340c01004000328601445400b0103454a100d680440c0c210545551003e0341800314001e000704000d074090018454080700060351240c1c041c0580e56a55a41d080040454014050005290154003602112940c00381c5100c8100c0b030303101104604062404c038404009402c0b807160040400010800e0000691b00c80c41001c025007020140c450311028589402032810000034103c2040020401440000c980160240d514030514481d010940c40c8a610120b001c501840c019150507100da4000441003003502d0700418180c660300c0c00c0030080c4000b0201018240c401c030745003421000c0b200b04407d20490400c1400c208060300d00c0801c02c220f82415945901095004456a00000d030a042e07090241e640c0c0301c10005d410039001c0c80c2c40d81c00c03da175050799551a524400c040c648190107142003801b01d0b8070284041d01c01003041c4002084141e90740c03c0b940c0d020b00011186031780710f0318000c00041a1540542992016640c100300c00c0741c2803910940c1840018000500241da20035600313100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 143820035 1250 143818785 143818811
    0x20301030501150f0609140409021009030620031b0c0a03030903090501051812010f0c0c0203070605030702070e0402011707020109030306050906030a0b2a0a08090d0c080904 76
    0x11802144600c000142425071400403070400d100907000b10301c240b44090700070021103610080400550703862009101c964104100010020301d500c19009401c0500c03407142c100c0190700005614201c0340544014032028203005111001c9403800030002c1c5481c0300c184045401c1016000360b440b1083c1da1114038601c1d01100da0542841e00d01d09203402c400183d140c80a04040517400304842000708001c1c2081c5040040a03541140040031083c0d400d0301a6611010260303064900350411600c0d007500c201c0800c5444880c040081041044c89400e902074440e00300c0c00030750f0905c0703501240d02c100000e502520b070300790401404500814002d4000d80c1000f018410351180103510075450703400b40845070000507004035580b60103820740d14a40d108501c80c000f03190030001191004550380300c1c00da50000f540e4200d80d45034040040c0c0c614034400d40107a03400c4c00400360300c01070032000020214640c240d00c480345641c0e50240b0496503801001c44540004182d1000c0e0800508480c0151059440c02040403d01e601803000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 143821285 1250 143820035 143820037
    0x501050f07060510030813060e0102060402060703030207022b020a0e06011b03022a100306081213080d08040203060f01050319150c0201050114090f1b1b0c0112050403020606060d0f02 80
    0x512406003007c0c02d0030416a9004000e8210188080c0040c0001c0d10303150f00083d52038000c0100c058180354001610004650f21410001c0c20101d801004580c2015020302c0d402c00e00c0c112801c100c1c041c0410180104440020112a41c03081c00305940f885104c1300b00300b00000b00d1410012080b81503108145007180240c5204030100c046039a0102500300c0c1b02c81201c20880800d4001c00a2703001c1c5407038000e00344099800807a90728004015000100d03510747ca40611010942e4140d40441b0003070007801e02d0a41e080c4e07031020040d40154006c070304032959500c565801d5510740c0001c2c8540c07170703056104a0012180d115104160407445004840300c2c0b807807005110684c825106000440d00050f503542006100d80443c0c585012501c0c6003d507036000c000e2410081d1000381c00b201a0060700d00404c01d4099a01651140c401c07102d1020366188003003403121040c01596a515081885280030a880c1040b002c40000240b02d418860358041d0300030640303038542da014404958482e40b0315403800c0b510f4905040c03d90540e80 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 143822535 1250 143821285 143821297
    0x130b071412030601140310060e0112020d0c17090a030f051606060501140703170a1e0207060609140403031d011e050703060812090621090105010501050f070605100308 73
    0x100c1c955520b00d45800010403400790400300c880308070420f0042c0125101445564004e60f031260400002200c0d0480040c3e44640e100b4016980300ea000140d15085100346070071485002000d038483c0e149107040b41081c0c100007031040b10b41d20503680c44100b040b00428492051042c10385220b00788a45019001d014140c0508a186410744081d034840808000b6564483c4000c010080c4072481541040c08550b8001e11401c1d01c0c00995901800341008507480c207502ea0300c242410021000d5001d4413104040341480603411115051b102149400301c00107001c00380340210480e02080700d0001d80d02d5601e0781d60981c0244040111028440d11025800410080034480c0b080114510100300c1c20000d4900e030300209a4000804550400d801c0900400442c580001c010344010b0503211f01c6501c501c565004101207000b075203214941044160707001c0c094980340705082c9004844010080c000ca81e2240f0040d5403074414010b0411254500f0000030001c20116070100307401080029918011598036294108a60444 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 143823785 1250 143822535 143822563
    0x8100203070e18160e011b02030304090e150903040e1f03020406080f0c040b011b260c01180507090902030f0703050f0f0601050306010e04031e09050a0803130b0714 72
    0x20300d0511503d900f000b240000300c55098a000101e43d140a4002005c4d2041c80300b07071901f03c5640e42004030440d038050040e03401809003004204040400c1003d5150307111b07464284007a4a103c1c44001c20501c1d100841190181c0e0b44800326031440341c0340c0c1c1da410210038a030040011480c08030b1200100059955000728001011500003d00f01d000003186118101460010014422494100d20002e40e0341c2201e10405d47d81030300103030304050b40418200117091411420030080900c183c908d0300411610100c001e008200d4a24008101c01c0082d205080711100b0324400c090700039408140d0400c900318a03070700010130262001d8251109005400007517890407486030000c84068000c61240444040c0420030403455224a42c000c20407540341402298032090f0601802e03502c101070400050038907000c1d6111881c1030745440395215411008001c020070076800d81c01401d2180303222440010350b610000050b601800e04040d0341209041c60003040c44c903154880c3e1030844412815681700a040c5500344200000e000d00707 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 143825035 1250 143823785 143823829
    0x6091719030504080705011d010818060103120e01031a090901020f03010305030301033c02040902031b030d0201060503030319061d0604060911030402091f0303030609060e0108100203070e 82
    0x42c1000507085c1342e010b80140d4100320200352091b1007006280703901c646495083c00c02d100552101041003490600c1e00d100e15600344203001c000000c101969501450011082d80d8a00003414114011010340381ca0103190032901301d100003007001e1498980300c210742040b0b56000052502d803202e01241050f030026071081d18660000300c0100306001d2000c0040e080c0e030301c0300080150110706030010000300c0c148003244030803803e4000c60071401710740f110307440b420780550010112164400182080303120195070210b02c074020700801c1c90842a55005024034801c2d5038006000d50f05654500c5803207440180d4501c0d044a440d500d03600c00162034901c40070b4540400260b05480000c628007402030000341e8800d6030211811a29250360542c924500c0703401c4e2074000c0e9044480051a8581c030009280e0f030781c0b6600844010f481d004100100b05500341d8070120803100b42240c140080e03035441e60070082c41d8009200719801030300602000f034100c22040d802141d012032136080007940c2d20350040105400b1520320f030789000722180e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 143826285 1250 143825035 143825039
    0x418030e061b100e0a08040b090f04020d1d06100e10150c030f0c0b0403050c0c061c0b0409021c0503040801290d03050d02090303091906080f0106091719030504 70
    0xf0103070140356561441d040040c41c0c40c813869903a2030790600c01c61107078500007032010403550866a01d030091003102c00c20040c01591610b030414052401400491180c9604005c0940000b0a940020855503c203c0698110a100c5882c0c04108040756000030030b40640c884402c107000c514100d80c1d8002c0032200c4017564504102c0391140c40c01074109030000c056041400041d034020030000303030001d4902d0b47c0300346d03d07240c0161286007020740c940c41d0880340640300e84e0002004c00c01001c034401032404407400c0b204900041c05013124031414481121001c11010750091080c00340040140d411041d500c201c2c600c514104d17440d155452904500b143c00c456030700c0000a40c40745048036403458840e108070040004a030000d010500e030f03503030180c51486a0000225020380202d4011007954040c0150307803e010000c0c1c02c2c1c03c0e00408a840340303080c5580c0c0d4090308020407003410200e058200703034440441c16500e00741c481d01c0340c00782858480c04940c02c510942d001c0604c0b90240000342d81c01e5a00ca02049188039072034440d22030f4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 143827535 1250 143826285 143826313
    0x140d06020301080a230d1b06050903090118181503061103040b0c0c0c2202120406060e090a060f0603020607060c02060a0209150a1710140418030e061b 66
    0x58120504c0c507015080c0c1c1c1204084441c00428203804903586c5040040c0d0b1130001e840c207031031003911481c0068900c03441e1104105034000c01000800e000c5c4400d03a181000f02c5100f400300304038003416010b03600b50170040264501460440c0e80c0001000340700d001c03c80f00990390f2a510441aa1f080f40c2c566150048d001c01800104416084007a4110309405415030510b06942e03603940d600c030b00b4803044030311810408551a0450844840352111a82d202400b59075070b042004c0380c00210320044e42c1c1190311500d41003000070007247c001c200c907000d001c0110107001c075106603495034405044c0700503401c000c0311b990340000401070b50380030014001c0606c030788408120b004800c0f4005c0c0c1408001070011a51500402c004250303542c42c54000c4070080148801e254642041100c111005400c0948101503400c0100034003100d03051480745041180c00b0392004480001101051005650380b80810b03101c0589441c403c0030000380103a46d24420220b010703140b1030030a0030700410844c10090b030300c0d0b100c0d200350411b81c4200710358 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 143828785 1250 143827535 143827553
    0x301140609030d0903060f06120b0a020415050301052b080c03280f08010501050d050901020d020406020f0610061706030109060c050408070807080322030602040303080a0c18140d06020301080a 84
    0xa0200400102309a41c984840907145a180c039070001c102d80400700008062140b640c1c1550045c00301c50500d80300c1a90314800151842c6e0081c0240c902c28840800000003c21018128001150010800360745c1e0398620358428501b07803c9000450100e000074040088070040f600c2c1150301040410750348140f00600d03400040c0402615042c03080c108019100180070700d91700a012948006491000010580d581040360b60090050500c2d03800410300010380095400d0b03001502000000311401640d005440d29041c03100000c01034030564001c80c000307c51588211b50700f1040aa400a4050004108008c290350b03002e04407507984a10b0400f0900c041010301c0600420000c10019041200080c00d4503418100e28517664007a600e19420289100000700184e400070b4081d00d8010740c1d102009540b10fa0302c2c1c0c41d0103451050120340d42c803141d9103484090000b070380c4951000c0c0c0315199a910151034a0b428003180d070140c000d00590a680000082d20b400f0005052403006500070000c140192440400900e800819 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 143830035 1250 143828785 143828801
    0x405040509010e03191814010f050909041203090c1e081b06210a0c110c01120506061608040e010b0f041e031407140a0b0301140609030d090306 63
    0x165030f1610264810512000044421203a040900c041700c2c2101c40703400300e528206818286a0740c84e044c039800207807100900707024040e16509803100f60521110400450305130081003880381d40441c420012901042c1c0c141c1c54a00031040e00e00d030209884189845400440c44981d10940018008040300c200783c0c4020f81c40080030703000382c0b805440444904240c031018000109141881058002a442049a00c580f06419540000007032201c5500c2c6c610380c40c0b0000c2032044040380204da003241001111484c045916244040c0503120b00c007651800060607001400001c0c402604090200701c4d42442c244d2001114803443e10502c60107680302d052410b240d143d0441a400091102e000b449003840c004c0d06141900c00383d07411002c80c1c1c40080301005003c25070703d4195001038000055544e41101e85c20011500b40c0070348252000003104495007105004000350b44c0e22801b1001c0c0c07030074030062040180c02c890203520443d0003856582044d030030100003404c1c079012004100100c0e008480800400c0107a00494074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 143831285 1250 143830035 143830051
    0xd0302040501171015020604021915030504060e0a0c03060e0304060c11010509121e060106120e0a0602160c1d07030504150213030506060303030408090d03020f030f04050405 76
    0x4140352400340064000542d4050010321918a41c3c0020448404048010010071140c000f0680c1d9601620019454000039181170380500d040007403840d54000d40c0d60301c2c0c034100c4901414141c3d000d000100107c0081c0000b81c400c444660304c0f4100c1048c1001c04000303d5100c0c5014040740840c1928601d0b240c01100d2171411103040d1500103000812126030000c0f00200083c1c0c12030040b80517043c0510040301c00d4455000e48903402a40c042007145800744c00a80d100d11081c0400106000f600411b10465a1302e800b44907400026008000b0301c000107190381c01c03c050b184030a07011207070306400907070f035000030781e0000d1706200c6088521300e9001c814000c4070000240204620740c0e17221045804211782200d03031400188100f0a00d6154804a01009802e910080d00701a00781e1046403160002c0a00078481e28803407105440358812000890001d1401104480c040d580c0f01d01c1d0a03181c0000c2c4006c0c0804800c49030b40039019405080c1e051002044c0c1800149000007920001c26500c82c1003104201c00c480c00507040070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 143832535 1250 143831285 143831287
    0xa0207080f03030105150c070e0a0b090603031c0b130c080711030a141201030c080c01110c12240105150a0207030308061207030506010801050708040308060d030903080307110d0302 79
    0x950001c60210849054441c151040c103110811920420040d1244c0000742c00f4601c2003020008201c1034580e01240103c40803030003800382d8004c80c4200010404155113095143d08100a001c41144074441018092107050b000441c00c421000b000130101120545c848a006444442a80125621448996000250741081d2540d681400b000c1d5580b4010003240e81c003030014014443c540d8010490649424400705070031890b10f9030712440d12484014040c032031480b0501c20440401865030050034034486c0e0b04080c3d001094401c091000b00100301c03685950035580780c051001c04150819960000c020a034242071410500740d4980b0040c40701103020310310a04d07456601030080750111507010400308100c07905490101c540e41c9030003000641c14041c115500113140b0030701c000002080400300c1d0742d034100c6041100821440e171743d80d1015a03455104a400500003541c41e00020114906440c02e802014068602440040e4403582d03a503440740e205461030f102203a64440c0c0020310346020031500103d841245401c1d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 143833785 1250 143832535 143832553
    0x7050c040e1b130e0f010b100203040e16091d060f0d030507060506130212010503070b07080714100507030912090f094109011802040c020705150a020708 67
    0x4040c0202c1c0003812180308495948a40421424030780000f42c24420001c1603405089000c51010b00a08a00c0886c034000c0d41e06410400a503400032007980d0403684d0a00710041c0503030f2258071901d55040400b1182c01401031307100300850200101c0365a4810b0040342d030000000d9041c40c000300003e881540e0389107072040c48200340240000e903111050320507a0343e0114002c2a2511844002482c0b0004104507040b00c1b0300c0814000700c030654510311503049803800d4066407402c40d1100e05104582c030820070090011142000210001030020b850466182101c1c015580c40945964402c0c09441c0142c80b00300000e602c03504420180f040703149078081c9036031440c1041e4000324501300440e0016080b5109034110f45540d40b01c1c103072002c015407141c0003a50100090103001d01c01203001c80b140d40d142403021002141c408000040d01c249051140094040c100300c0c03141108a00e030350810010701a900300b0382046003d503010000c0d6640351450300e07084032030350395500300c0d2500b101e40b200a2400f6941c0d4403d1055134400000c0d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 143835035 1250 143833785 143833813
    0x9051024050a0810080d020d0305010e0103050304030b0406090f11040e060f01120c0302041103010f061407060207030507050604050d0e06270a0e010602010203100518010501080a06050607050c040e 86
    0xc40b080c1c4202401d00079010b070707074244c42c00901000c107500c03030405801011200e00c441c03640840d54031503041054504001c541d8031030360700b500c544909000051040e40208014404502e11012881d406403080c0804202d00c1c00d5942c510141031100c0008552143c0c003440c41c0c24651a00e8042e07600504002001030206141900440080e56818030500d400350302203030100750500200c03240781c0c800795802410070310100840f17140b00303c0302d03a100f48034144881850340c0000c02c100f40305242003101c20012042e40b13403c0070503588403030f00290300c000740440034400c081045100044050003c24030450041014090429840401400b4460b2035100e003031180c142003000b4000002002e00c80d0003038030210104041940c22502c0400d2441c400d81e0480c1810394a0788000290569054005521580e100051014281c2e070340c00500c940d181031b0407100300400b120003005020a512074100c6981c0310228180c04a0a1513442000c80d10660101e0400d0f0f8083c3c0000e03820f664a42480d000da080300700000c1c00100200014005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 143836285 1250 143835035 143835037
    0xd0b040f0513080c0705150309010606020f0601140120010608010c050c07181127040c0206060112020d0f05250504060f1817010f0b0f0d0203070905102405 68
    0xe000b03001030390100d15041182e03010801c1c5c001610015101c050380803241450740ca09500100c0c1d060000c7c6d0300340310020484501c04181018403992500080c070490f420303c61203110420340c803c1598100180c40ca5540c010003000c800051440590700c0000841c2400c00080c6800d460f007808003907003804000c02c40741300500070000d01402104c4501100c400c500c24100407100140c40c103041402030514010482104403181c013811300c140c2210381700b0840d003a184100c041c0021703201c40b40d000304090b8101100040d05135000d02c8110f01c074200c19400047c03402c0000342d8981c0840e10030780d4042240c1a5100104114142407042c1241459002500428591004180144107100303900462040022001c400000680104441d50910384914071300c03115540c03106000c1c030881c1101d0356078400540c00c080f10b160b05510248134507101c1c14030182070502414844000c1c01280000c644080b60940f05490740068100380c64401c19001d188004d071300c0a12986400c0c280030024120f1450390443d1408000031882c02c5030414 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 143837535 1250 143836285 143836321
    0x1a0112061a010e13090b0f09010c0e06030f1312020f0f0c061e0702030601060c06140f01060f1403130201090603020f04090509011e0c02010e07050d0204020c030d020d0b040f05 77
    0x200c090000101340d01101016118160008286400d00c1041c058103c031000609440b0b15183c40081065182d10002224111864845250403850400c04940c004502551a0b54041600707000310020b0640d66032800d840030044103100006800c00b80f01d0404480d0140544560191404020550341d1907410001d55a44160440341c0c41840c00c091003114030b82040026a14003e400800b07031446503a441030060400b050741841242c100d80b0f481c03c041203038003c0d10101809203041c0c070b040c0c00145e803c05009481d0404031020100600448940030b844209c0901c0c000c61003072501000c480c25216841c4009030100003070b0b0300b2000c00e25005206059181e18620151801c980c5400404a4191a0045824010514000c54000b658844080300240d54459040000c01c22890740c02044100c00414816448010600a039a4400aa017545001500d0a0b030040c1c0144642001983d02d00b1410000d400101d910140111221b51384501c6401043e14081c49410f040300380c000c0d8244100e103001d010440c10a043c00c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 143838785 1250 143837535 143837539
    0xb0f0109140103051b031006031113051e0601020c06040330080a110f031f05060a08060d03020f0a030908060a020c0d03110d06030b040b090a0209070c1a0112061a010e 73
    0x100100040b6641000550b40001c0c7d040000c0051549031309000c94941d0200e01e499015240901500b0702c58009031041c2823281c5036400602c00070720b2102f8054201004050400c0e4114403410b54070300708581e80c8400910085204450113101704180030b20030a200b5050340c0070f00307075801e1040a071081c201f90810419584404403500000e64100c0403842e02015000c0e07828400640000071040148a220031181410100f641801c0c00d8016559482040010311590b071080c00003c2012001c980d460a00d4404087d46c00d00c0b0340140c0320025202c004562418103000c205400103160208108820001400030719000404840150300c0c00c4041c100081c0d0700c0b40448440405c1640d519076421420180134151010720a9084007449a0b0355241802c3c9180304050750180c2e0901c000e040842d4034500d0003d400c0210b298060a10000daa076007050a440500354003000340c0310190403c145040002e1000704003806031100d41849072111029080010486201075008070242c007145104101d40d0fa0081e051a02070102 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 143840035 1250 143838785 143838823
    0x506090f0a1202030d0903020312010b0406051c233103050a0903050d030603030e0604260a02040f05070f090609091d061305210301051c0b0f010914010305 68
    0x2d8540d04030714601c140c2030141c0c00d0358a8040ea4034201a404402011511801070441c00e4903600c17034007910464440c03031082d40c020071070401425000300414030242c40c2c000c0c240c20740061020440c0e8050a8410b0901044044400081003040141c04044081c103180f81e006c01003104d0044280181c0c0384035074003070301400b90a102c0c001c1000200039101d2440c400285174050241c0f4914002648040c1c0030b0242c1c3d00080b07022071080d03030398800c0c1070800405450440c0d10390040d080b440c4030303050203100e200490140314030303524000c540d50000562524060500d8818000c100083c40d803802460007454204060b007101c0402881c8901001040d40c00001101580d84804002504c402408200da002c40c25800d03401c841c03809014204900e45400088041d031942c054002d44c1c4071706907500c03850401a00c404403203102d000b40900041c407171401c1c544180b40b501001103540000ca10304507280d01521803800c0719400104680c0c02c0040c881c00140d0700820b10f19409550300e0758115411035880a484504e0440c0040144007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 143841285 1250 143840035 143840063
    0xe04020901140d12030e0c011106071b050607050a080a0207050a031103070c030521040e070c032109060f0b03100b030c090708100e01060f0e190e040506090f0a 70
    0x42c540340503801140d131000d19004079220154001d400381901c2e50481206006115910455500070742600500c2c000c2500071f0505942c80e000b09036034104100e0134400d65107101456000c0021001c00c9418029000707619000d481d803c0030200203000d0303c0024007200e541030043c01200c0c0003403000280707914542d9049c10441d08540800f10600d1450248040103043c0c0c04005100006000740810462000301128000000042000d60000c0941c400d52142e00b5003040c05100282e92a4030920240c1076151081c41d040000c4481d600204c054a0250100075944565560603081008050700c200c202c00034001070b09201c00140080003980301d68a119804046540b90a26100c442c0e038107010300a03070384400808181071428420801041c058080700c20514104140401051348a00142100e0480e11941d5512140a00b40141150260310741c840440c0c200703880740703030b80255954070181c084050140c1c0c10f4518158034181c1861490504c0180500f00e581d0440b6070079150041c00411a01800c0e5080714040358401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 143842535 1250 143841285 143841289
    0x230f010c020f06070605010509060105030601020604120918050a060801150611070801050c0c060106023c0609100609060308040b07050c04050f0f060a0501050d110d060b070c0e0402090114 82
    0x3200e4000d603c1e4003c100003104020041c16a100c14140d070403e9840d0700c566030740c14006603403d110643d02140503034070410000700050a2520401c904000d41c0c9400c1250031f84d01e101007990b0390300034409118a00d40790010000820712a104200042254100a204940b1014038045501c1c40d140145400c000c417004050920440400602d170003001c1e01402005289481607080346903412500e6039000074010840001011440024400c03208807040d20504000c01811585190345d41000c0e40c203403001c4070841e0651070010402e1000500c11101700d00600700e03030002100308000700c590942010a28510740f55003480451000001c0e9010303151448007003540d59985017443d41c642040407410941c0141410104080400c0415006000388490003070f2504da034540e00200411110a40680380c0050420701100d00d04000a4000280c5000d1001c1c55038039100a0480c80f000391140e540041000c2c010014110041158407201c01d0014200860600201d0905034000b80c1c1c900343c18410701600f090100012403240d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 143843785 1250 143842535 143842549
    0x207050a080c15090a0e0403030b0d0506100803031506160606061d031c050310030f1416080309010c1e11010207080109081207052101230f010c02 64
    0x140000034400d04800d0380d500e0300150784051000c819409040b515126000080b1080705550401900a1880c1c0d1440d0810003100c1d0ba02c48014010780806848000710200d648803034500c401d05c640502c0150421345001005c410701007005a003d100c01d94010000c204281c070b07981c03220300d11201b01202c01d1551130090095400a12064403006040d091802c54006592a0850f01c4070a4900ca40b1b6099505044a4001c050300c902d24528a484020f0070501389110051040c1c0055920030140036034003000039144e88a074a1605988502194855007814060310202400c2140092082d00c4c02aa00d04c2141000e122a480307004180149050040302031840d010403527081c14608014034500e0b000c812074134260034208040c819800356640903005101d00031444940601a92140d1a009072100e403818039200b0740c5001e0013034000c180e4020018284688107117508101503094015411031400340b801d505190141c6e0010f8282500400c3d0603100d60303007002c1c0c291140c880914001d01c0908003d900c4103500e00201d040 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 143845035 1250 143843785 143843789
    0x2040603080f04050112090201120e120a080f06030601030309030b09070e0c0d06090225020609040e0a03020705011e11120c100501210807050a02090a09140105040c060e010207 77
    0x19090010800c0b1000240c0c4502070310468500f40d03690308190329644d185408a424100010f4001084414580b07584407458000030050007100c0304660344203940600c158910782051400c28009150b4100707110140062409907500f00b24201d001d0203c40d45075980180009025101c0142001c40c2480041c0504600348a440b00408010b40414410f142960b05500e44e940b1078419180242c2c80c0c48004030b00c408013403081e0f4210382188401500300c00c11200f031400b0251056a4126400101000000c034140c441c0d00490720b042d5044c5c80201000001c03807034003a0501c00c0c10740081d810415100225030341d600400c22842c0c04500e09e800e00c0202d190700000002c1c280344258208014850700000d10b2000d07550b0008140340f01005e082420070481c0d884540c1d5254004c0b042a04180741c070401c8a80300085100b907002030118600c00c0b82241c051a0040e40172500c0e5000031102400425030380d0841800780050301d48084d04c25038082d0020090f074500381d501ca260005082c002e0508000c548151803440d07900030085540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 143846285 1250 143845035 143845043
    0x1204140a0c0e010611060c091905030d0e030d08060d02040b120a080307090f050d3c020112090b15060903150603070b0a05040e0c070803040309030302060c04120f02040603 75
    0x50700c0354031100390085403a000e01c10400061880e4500c40c203041c038040340841c0105850103000307140c0f90315070080140e5000b00c080d00342000c0c1d12580740000d442d0380400408550705000d4940c065608070000401d0b050296001503441070120441c00c000041c2d50340725080b50120380c1218001400c0e0300e0707240400d1130122001101c0c0f2481c8181020241481b00d9400510701c941400d46d107146403da151841c11081100700e00c90a071f08020161580c1c000941503594100440390100240c0704000c00007090614210000d803100c1040c01c50081040040d03581c480b007414403491610b80140800307600b994681300c0002c07008041f10010307001c1e040003250350b659000c01c407468200010211421882500030000c070410741607908900c64818820005132050600c0b0075113000189640310b95081c18503041320000c1d8081c00501042c80d8100c20000320740021030460240d401a402950785500c880d0079803a001e0300d8540040c2c113201c00000240010014041e02d09002e01405a04c03500781c0a003122180b003c54050916034000034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 143847535 1250 143846285 143846303
    0x3030518130911031603230d091d01060c020904030e040c020115051005072a0b0901140c0a0609150905060714041802090f0406060c02010e04021204140a 67
    0x420715109500040401806028000c42e1800c440d400c150396101254890b2810350030b20ba60800c0400c503803560020307201c103910000030307001c82100c0d501c103082050858103d40464449181441301d0558400c4021100400807000451541000d102070217100c00c203400207104146140000701050311075410350450a80241c0140324211465901a010b445801400000e1405409000510780307005100c1100190242d15858a00034007516100707440c40c907140c1c082c00e2691000b10b03040d1003884611080c00042c401c404440352291584800101185c1d0382c00001400c9150600090902a0020800c1d44045601c20700004144105280031340032000040107841042e86419512014031002040c0c0502c90340032544c1d555210460300880b4041405240101c2c00c011126005035001c80071660300400c1410300040c242c15417410700c2c800003010b89190b50030540c00204080d84500071541c0060b6488030342c07101118158282508242000309560b0001d001030400b031050004001c210304140007403000385801840c12 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 143848785 1250 143847535 143847559
    0x20c0303030c090405090a08070212070b03010e0723040909060605060c030a170f0a0903360609031e020111160e0c190f0314090a02011106090703030518 67
    0x1801d164001203c800e004504100c00140d0440000c04c0341000140d010310028280110f540901c80d803542c01c4440c80c1000d02c515407002c80c1c00e4000c000558001d15411084110034900302000074040d900c810b0116084008180300d00e05140c0303d46083c0c2c0d0680d80984400038201485041007800380c40d01d0b6105980001c0000313030065114501000501a84815858454448c801c80640d10300c02401214020f400494500c0418a561110740114035190b0191900501041100d43e11b0a040344c2c035840203d20550444c020021010380f0b00c0541d4004150f9410013401640c030310b40743c0881d01c1031560b11750a0740a507201806011a03000341e48601000c124613089480050100440e403403440740071b004904840c50081c001500ca024500200ea9491408660341d13506014040b41c1a5850070b08154000305060716a0446030750240f505804501c0352075944020011115140005405030b061203100386542c0e0485800c00030400d1001032403100b26689480c20300e5880c050b0400811054510100c0329a01001744414 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 143850035 1250 143848785 143848801
    0x90f0204050a2301021b06030c040e0907030c0609030f1401020c120c100b030c010311160302060610020a0803180a0b040b1807051c020f09070203040f0603020a0806040c020c030303 79
    0x3d41844002c1850100c0c9484072401a6aa0740e512051142050384908901002d4201000603640003081070703d9060409441d0b44041002e80002c0b2840303c020b41c0450b4040051202188220b0000c21035810903104041c1192600d4041c0341d0390010191408849442c40d0a90396000d60485d44801c0750001031300c001c1c0d140c40c182c58496901505941040788680408410404607500c18441d035490002e00a00d0b02607c0d890041d0003508800819811a4000f0300016104103c1c40c44c0c01014544030f0b5002d042980f400d4020041140556500300c421540421054400161010116901f0180c41003100102c0039402303d40d24608040034100034000c503892003d00040090103107809003c0c004c0d10748000b0054140f20600c0303640b00c0851041543c000c91000d10b40b40c0011074006142c810500140000300003808080100c0e1510070207540c60801688002020010001c445086401422540c80c00f54a4022140e000524591019006030b101d26503825060240e14020020004188000b070140c2351a8074250b24 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 143851285 1250 143850035 143850059
    0x50f0919030302070303031a010e01030c140d09060f090206040618090c050c061302030c04200f041706010f05010e120d0503180303091213090e0606120a02010207090f0204050a 77
    0x1700c218040f0f8104030540441882825820f000110103a413a0703040c03020000011000742401c0c0d0f04d030006000340405500c80500038000103003540c000035000411500d059241000494401490f002d03075451900310382e02c0041c2d4501d002c54040325641c5c0740c1070710313203042c1d944a81ca0b02100c0c907401140794030318210780549556000009018458084400c0d40d4540d911405211500e0809030002075150f040040e61711210700c2c0641c01900d00500144030380000c0c030304050800300d0750b40c001003241c2c07880e41c0042000c1003104001d211282c11200c20f10043c111951628501980001e11402064103014480e20310792926220074000011401050088a000d0140d081c9d01500b40c0d4801d80b00000f0240c3e5522141c101d1f0398000040340d008402c1c00005000a00d2101d0ba5400701d82c0004010180d01684084e00140070b01e114000c14481070072040280070345090603c10032104007403c80301803640d0341000c000307000944e1300826030301c00304c40c159480400e40300090040300f0001e20a030b40104d035001320100d60100b0031641c003107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 143852535 1250 143851285 143851289
    0x703020103240b0f0403021207030b130b0f0a14040b010f060504060e0d0204060e0a0515040605060a0f051b0601090507020105090303130c090f1b0e01050f091903030207 74
    0x28804200070400000c242e64142d582090400c4280b03a040001c100100c450401400d0428818459030b00300794032940011280d1200071005241540550024410f0120303044016801182c90040d0365440045550351044100c4018a4040c1c04070316480040d0b0400d1503a0420059040091f1001169280615126102c00400c0c05080a00c0a0f400c1010485c01e00480884068881030340315046820308840c1082a00009420200d030400d032662070008120860b4a803450040d0030007a0041103600d04108001c0c5522420302e1501c0c07050741002010041038130760400720740440c00140b40159800401d17680940307182c414080c2a040c7c6400d822601c8203030b503001080c16030584801580c14081030f125407108a090320820b560302083e80c0c1041010542860444108410103441800c0b00c10754a5591104a012199a4990103a100d034075aa4158580714114201584c2e215280c20300086003401c00c00002e0130783c041d00401410082e0b002442d0041a80e4009446140c40101c90020b03100e19100c2c58001d445030480c3c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 143853785 1250 143852535 143852537
    0x105120709091a01080604120f09050409020d060501080706020609070b0a03180b0109020a0e03012307090e0703060519060518031e16120506071d0d0602220b0d021b0a030207030201 79
    0x5442c242c107140d2280070740b43c168058079922b400056040c00c04000040003108400c0b40c0c050000d0300128001080b40c0034882c020110b003006407040300d10b40340029091440043c2844042d42185600b8021000342c0c4058034400c1a0a250010748284605070b110742148510401420034442e2100000e20201c00d50002c10900045a9502c49882c0c9000281030070707038400e03000202b00010001659200700c10000c00c03072a40840c40c0d00d4840c038665a5806500303901c01c019150040080e031036402c24400b60405018210f500004548500b440600d86036000340741e80205104003020820b810b1803140d141d5410083e1095081100d83c1394841c81d2650f42c42c46540d10243c0c03031410345526890b00d0000720544240820010150404007070801c50382c409004840501d48951402d00021841000301c03820340700d580550002d1845414010795850400000c44029441040c0c0348072410036501301480f0b6007200c00e0035036048207135402c4090f860320144c480401c1d51440c95040c00c10607200c1c440800040c56400140c1100310ba0007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 143855035 1250 143853785 143853803
    0x21060e0d0f0305011a09031501300b0c09030c03071e150c060b040204121104270809030f030706021e0a050a0e150f030f0105120709091a01080604 64
    0x3007409030103640b024410803101c1a902007174551080070b204014258000020182c4054200c1810000b212400a805c83c200703001014511107c52408081a0040c0b68035504040700c1295007076480b034049440040c46e450161501140501250702c04001c44050413800030305403002d2584034452400c14100e030840ba51141450b40c40c001504500a030181c035100c2880d541c44007180c0e000350302e4000203011540f0245411a0f401c000001d20266000c00c5400c0152080010941c1c0d50314020800c030690f48500c0e005440080d05240100301c1d011540c03c61175110f1b44c0701d009240c841d0b1b1703014000b84c1071115056074000070b40000114101080310f182c4c020164440303c03a0440d030300b10480c80044203490044c0114000400c1041049020b41401000915400000100031110100c4030342d2110881e070704020341c1046500d50200a00c0006c43d01c1c02c00c3c086c0076103004e45980c0b200f0b41100406560703a401c24841c59031400e40e6024601c042c4000946040108104116910113659449001c20755489048a0684000b08 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 143856285 1250 143855035 143855057
    0x31803010609090f061107060609020a020c060a2106080d0228110103022a100b030607020606060c0102040503060c070b0708060f040b12060a0b010f090e0121060e0d 72
    0x2003036105290025800c441219180390f4250b4400c801014000300c0400e206e1424410340000446030700412028044e80d02d80540c03904802d49020385030400d0480c1e200d210761010b000800c0c2c544d0380109211034003c0744c00f9481c080800b000b03c02e90000e10240d00904441d000715180032280b44c5c1c001410101040c4000024540c0007180400403018110120300144803070408003000322658441d8014084400c0821181250084401d10708400345400f05811a00340d00580400142d02200d031003070b00e405143c2500608010701d06600000d440d4800104454400c40000c038903108603071000d6040d41c2c0a0722003c2e00300d9605017054410083c0d40d400c10b00d0102d4841d035200c40003039505403107003500901030140038064220072203040b42040003519521207a15007101d81001f000c0811001009200c2c00354030b004200252000c40c040004000400c01310040f0148400311038200f00800303084905d141126481208800a00340d05e108104080c014003d01818190505e451002c030b5400200303112001380001d40f1000c41180c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 143857535 1250 143856285 143856299
    0x2100908030a0c210b120f062d09100b030606090402011103070f031e02011506030b0d0516080705031b011b0b040303060927080d02042c0c070b150f030318030106 71
    0xc00e02a800f50206c2d0072400c0031410004080307000715271606c41103244005050040050b00d0705000200c42c002036590000303c94991000c424861071305569000d0f030190405140c0440420500c00d0301820080c1003208544d00402d04e69001d000b40c0d0078650b44102c0c40130b500901810002c110b0305111400861710704106d04841c0069005104c0d00140c082c100c0300407605503181c07502c141c0041c551701d500240c1000c0c409800c10000b4070300307025810006107188a43c5400c941442c000a20700403042d04403600076406104420004103841c00754021000c0c0c2441c28111180d02606031418075100b41c0c200a01d45240402400205034141e0020780a48005036420071201c4500c1e15103443c803450b18079201030b0542c844000c890114004d00f00030600d0181c2d040300545820313030300c40081d02c102d140c82680304011440681c580070a10000311a20303410070803580001d803e00345240c0300c0d41e0803100302900d403140c406084250003401307485140d0402009203005060740c0d21412403031b010409281041c003800d40310b94a800c802007486 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 143858785 1250 143857535 143857543
    0x15020f0c0d0515040501020408030c07080d02151308130e04020906011407030c0503040e01064802150a0302070303110705060705030705090a0f030302100908030a0c210b12 75
    0x750350000024120380c2d0008074200c124142c041d10a0f44c0a5400308400720750314038104020b1074441e0701200145116803405030304a05000802c0700c0c003421900406000c8009031070301c445264001003096000854400e240ca0070702014071072201e03c04821201070b40c0015030a20441c03410751007203000380ca8401d0f01da650b1100450f00201100c600081342803003031144c038000c40d00c103c2046407164440c1007224541a00c4060125445100340d101c00005107001416600c0d40d160302d001411803920303445030011160058147c0d025407250b202002d4504601d954040c0e4195902e49112183c010545c80c1d90a0f40c40e9942d400083c043c0d8031065050700441d050150324000740a07070404232400e843d0040f000d0151030729030240c212516400079103100c08100007800090a41c1da1003005500083c0640d0311200d2b000c0d1b14628010742466108007540304c005140c01e032901d0118a1020450f680802404000543c40c2c688241c03e98040380c0300c0080b1024102d00f000c1c52040c02c000f80e40b0640e42181300f101c2032944041d400c0c15459032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 143860035 1250 143858785 143858809
    0x30b0411120115060f030b03010e03030910020c1c03020702040614041104080607181509031e210504030c0905060a0b030c161110180504020a0801140a15020f0c 70
    0x15035000400802c051407084500450808035840c000c121f03a01d104000909440300c00c2440401d540000003807000e02c1404116030040c60070903560550400b41c0c3d010341a900c035240c9005014030390080f501004442c9210741c0c12204182d82c0100100402d03522482600110303030b0440100da00031449c1c01d6201403a40704280941d01210903500c018580380c1e0380c0b40006c44a51030003400d1207041f11034005020840b4170312907400702d00c80656560751010103461810903401c0c00340c01707031616140d012900d4400c4007c1079001d000002d0304c071401c080c401c000c81090602262940f099500141002105080c00f05d0b18030481d400c25030203120100d4004040c643c4600c92040240b0007a00d081010340390030040080f503140841200d8048a0280004108a0714a2000b15001d0f0b0301da07998400000d072040c0a4400f1203400300e22400060081502c0442c240104a80b01a01d0078034103000b5040c06c4100306448160136030300c240c483d034090604001c0003450044075400207555000c81d101034003d10301552003241c0250410071800c01f8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 143861285 1250 143860035 143860061
    0xd020106050406031e0807050d1701060c0b0a11091309051204050105030f060402160f03030e0c010504031502070c060804030f030b0a0605031902300408090118030b04111201 76
    0xf800003a00c0030382c4e4190f20340c070000c01c56006d00c00b0310110010440030b0005240c0e4071015200c9000e24010b8408511600320160882c800b03001500101c100802d05829250f40d010740d0b504000500c4c083d919206503043d0160181d0716910001c184406414bc108039088044140e1140e002c40d8162a003005201c2c4c40d034000d50045038001141800096413001312000200d0300010702134001481d00d10f0384d01c8841e03424001c030a01952000c02c4589803108260345807103480014400031029011a80c00e4800081182c401c03403101810408103801c1c104404200d1780c0c103d41e1240d0344040261034613691146c020f42a0042110103401090b0007581e03080030503010780210081484010105d000700ca0900800f03907000c0e00003804582c40c1c0380030072510800000040c0700a1058032100300b6990402080c900319901100c41c80c04546a40324a00c00034040020201c00a441c0008003d080484095036581840c49842c005940054042c60003581440103100c01d041e040c00c1400d005071801005000c005419034240e80560450324 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 143862535 1250 143861285 143861303
    0x10020a0806240a03020301080c0301050405120703090e09071e05010c03030e03310b090f010804030c0602040306050a0507030b18070e0a0905090105060307080606060304060e0d020d02010605040603 86
    0x40c900d10b00007040401940c0c02210700d5082d5480d21035540c41c03642001c1c07a01408071742d0000040c040c8483c20041001c4a2000314000c0c8840d14256540a1300c620b01009446401c0c14046a64020540075101c1c09000d40084110180e5038070304003c00d10342e55501e45c40780c0300c0d0003115070042007890702444001900743c0c0c0040c1c640e030182400ea95012030080015030600000d0f4082030105c10250141100d503094003000c6541e82520100e9111009600855558070900e804041041600819202d902c004840902c003402c000c941503441d810191072a11002800034080303880001c0100c204200340d4407440c01251485810480c90b43d89140070380031110f44202c016402421018001344d0107004c03640440d4840c20504d440c1c3e41d00840500072401492490f000310024a850b00b04000f9081c100748206075110700200c0c001c041d0f103032034001855100d860160040b070042d0f10000005080c02480e820800f83c01e480602221b18103420a44001d4460140000f100015400c0280000b064a8240509015290003403484 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 143863785 1250 143862535 143862541
    0xb071805011805030d2703031709120a020a03020c0f0102210c0f030c010f050613090501090b040b04020a090507050a0507140307051b041505130f0e0f10020a08 70
    0x19a0403a5680400746541e030080b01c004030751628113118034988101e96499401c0c40d902c1c0c2441c0407204000303003c0a03180da402403140030404a540030200400541030000d03290b0701500d0b800340103070418500c6c07041a02c01100008816052a0340041e401c00c0039030290703003524070402020040100c0030011001c030500581c0018062005104290150102c11507400c841c180307000b8400203036a080c50f4400d40c4140c41a000814110f0030f1f0302007801032208000d484a4100300b42e1910f41c00068800310559442a103055950f025402001402d500000c4c80079009844084607203002d180680320002c2c122403c0707009000c10500003800032100e0251501a100d41d407034650400300c540d1000c1b11325402411050342c2c100d40e44074040001010900080240c540604050007000380c1103001081004d40300c141d01409145032a498002e8012440036040690f54111000b00102c40064058400750800078400100a45024080c5030390200001c2d071030700203128000903201440b440714480c404a0080e4004040412842000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 143865035 1250 143863785 143863787
    0x80601060c0201030f09051c0210020306010f080a0f060306060302010f0309111504030c030804061b050304030b040f0c06091509081b0d06020301080c210a020913060e03070b07180501 80
    0x22000c03a074008100d0006c1c800383c1544640d8079020444403801140007000349040e81d001d6050040c00608a40480107500d50304110000809050410100c5800c00c81080080340580d40c1c1d0360401400f00107044014003056449060074001070000f0f1008a0100302c0c200d80500340107003c1d008038140c1c690440c460900d0030002030140441151108100c900d241c2c820030000c00080d410495041c043e60003140b01b5502c840c28110b0207000c1c941c41f40b1988088004807490b480c00900f00104503001d0701e40c40440d0340d141c0e440718039016080700445503000f13298450890010441d20351020450044800c61105411080c0040b0780a8900d02918002c09c1c000d134000150103030100c030404074115034151000e452845004000c1d00c070881286c20a0700400030640001350444a030340350000c048001c0305190880d027080f42c8000101030f40d030f6000403040280182d50740c9000540a07400400000c1d80260040c0040c844040c2454105032658081d01c02104c00c099550f000c1040144241c44c421000d9100800c200d80207030038500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 143866285 1250 143865035 143865041
    0x6020901050d020d020403050708070e01150504051309030e1206010e04031b05010b0a0f0b0d05060a0f0905010f08010e0d030f02070210050a11031606090c0e10080601080601060c020103 81
    0x180c180301040002c28080c1406200500032145800d0005072500d055141180c1440d603250b01c11100b50740408001c8c8404500104010304407440c901c500c0c1c80900305c4400c103403400d000c0c40d441164040c3d890b0031111020100f940080400500ca03680364000e0b031580c0c4042000488032054080d416900400040c400b54546044003904640603080006225070031409900e000f00141500701e0b2180d44810f00c4200c01d0428920100107400c482c03840c0c250b20341c100200711328140521490110003d80b21800b10b8007030b80700c8001e0100a8441d2400489a2549491008018000a225142c200300c007420002400d03040610820403003c0501000e00100386401100310050300c400d07248041043d500700a4900103a84010152201c084680c0782e481c0c8818075060098551a82001c640300c0c0760704100110244403540315009180315a000d900000c210080b810700100849198210305420401078041c0510300c80c03220b00300000c4425000c11a00c06070703203030300c141c5071143c10a22810010604900200780158000e030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 143867535 1250 143866285 143866297
    0x204090507050a0807150525110a0b27011e110102030a050403031406150703030e01050705040302030d02070518040813301a040c0b13050406080a02010c0602 69
    0x10301110225034840d00041d4003059250300c2214582d100c03440400280390b40d588010421075240c00d04606040c40e20850150300120fa212040101c002e54000e0342c2080a0513110f00040640038111445454442005003001e600248407110308190a41009c0e000ca01d039485000302c2000b040c1d4a0301440100c3d101c0114541c800b070016102400050f4005404504007407020b188528a00c00740486d8601381810060304031407641e000409108070030001c0206548814801c407a003607034412112641d907100c03418114000c104404820000e5401c002c2400013195000c0046e00c10340c3d008605aa4400241070b40a9035110003501c1182d403c086030342100e5128692800b41c95034403901a00301c8514001e0b818441140c0c04010360807000401c003405800d10708480c082010f80740d00c0c1c0750080a54260007002d403280c410f41d0a90032400c003007206e11040003c081001809c855001400141441c5848003822070051515265a0180c50702843c40c01d40d00280040c03000621001082c3c06840380c0302c0075042c0340c50740c0c4041d602403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 143868785 1250 143867535 143867543
    0xa03080a030e100e0105010501140309150a020f04030b040203060124050901090302120604060509011806230403020d030507030c050912190602040e060a1802031e070804030e010912020409 82
    0x5001c40c228044c003d4142140c4000c0c00096258140b03000501084050211500390b40c00c180b0402882c203400281300e079204c0300f101250741c14543d40d503840714001c1d11840313464144080b4040380c000208071550400350300541c4201e081d607449a885502c003810742000c0340758001c000b0b800300e0342c803a40c606d00803401800c41d074606140a14180762203801040c00f400705410758242d103a02000c10001441824428150010010002840240101c4803000c0b130200c19801c01030700307440e616155000308a0381d6030704032511402c002d031541c803041c86d140c140a074a41c004400d552010909103400251014840d01c5440503008968075054100300031001440f100a1031903078007820364424900303003000060f10580e10001140c0b140303101580c0c4900f00760b01f17101824805132a19005000e003010074801c800d001402e220b440c002603840140c907590f44880100402c65528424150b40c0c0340e04050108065010100300d1180e4001e45808800d404404011102d12045105000034000610180360040c50301780c02400146000d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 143870035 1250 143868785 143868793
    0xa090b010c1205160515061507030e0a0503070e0103060e061e18030c0d1d0609090a02040302040504030329011202070501020f16031b030806120a0b04060209010e0a03080a030e 77
    0x2802015541354020041a070307290b0f025500004090380c14240065000c1e800b80c9101c1c1e6400e6080c0d4200d00c0078094000020700b48080d5001c0d042d16030300c41e41244001000b000b8200ca0440c1d640340c1c10740d6481c1e0701c2030105580340c80c2016084008000300090550151510380801203003110300600e4112404009000354080c080c080c4c1540c2ca007a5400c0010305042c400c0d040c00303001030b0550600301030803802c9021000106801c4014440481fa540e45098500d0520203454541e01036403118400b034002c0c840c680000307500500d04400e000925615901240c100401911802d82a840c21550201580c55101c0c4c0d10780000c42c082112184031085402916001c0e00c1a0300150910301d0310440360340c035a04441c10145e1031412180d40f4a05140c0d11850003581c000301102c1d9110302c19020f4030001c0400c2001003400303008444c1d00c00da2458000781008450016900300c0359444440c00c041c81c00c500a5407210443c5800500c0052500d04980740244030441201c4c0d100301006d1801c1c2d061501680038003205291040b10f030003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 143871285 1250 143870035 143870047
    0xb06030f0f07171609020c0a050d1809090f080c100603050f060f01060c0206071e03080f0603070e160905030a0308071202030603031204080f040b090a090b010c1205 72
    0xc000c001c074444918004010b021602c0c00c0110b1401c1e04031242114151aa01000c04c940b9200d2010308001c0607141d01c2400503036100300f004a0a4901010070b10010603501c5045409001185d2000c9881c10001040c0c2c51505581d40e5000e011007034401d410800361401100c01c0b10800060901001001440000700641e401c02801a82d40c002b01c0707806500a4403590461105070f609002c1c28000030360702c8000c1311540b01095041c11001085c2c2e003040340c8003c1c000c2c64000350b00d4051103200111030142c5105602c043d44140340300d20780101f9081080d260120a0221301010400e81d140c04101d800c15540c812020680304e076640344c1c4001d8042480340c0c00109000500e4030100d9151024411700020b18029240c01e42d250030004030003080d0258202c11010b42030310620900113255808421a290246404403a1407240c48600b4070540034825422640580400042c0003d184000721028121121f81195608000c60b80c43d04c103401600c4040f000180014590101c80380015014a0b0030040340e51607140c101e0801e4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 143872535 1250 143871285 143871313
    0x10509040903030b060409050f061f080a2009030d11100506180f0403020f0d05030105060c1c020a020310090c1505090d060605040c0207230609042f0909040b0603 71
    0x313401900400c03c020b890b1000c0000e03501004e80c4c0c3c25084401682c91000c002608078248bd104c800c16100d5800308400c540110b01529030941205020003403a65100034010100969211035038008003800b4000d0089152505201c0d000b0b4800c80180c10340c40c0c01034119017420000c204d005040c024400b5070b000d14a2a4503030402c00300690a07070f1044076009108800d5050900740a8548000000c0d04a100d502c1040034842c8540c1c0304080c0ea04403082540c1c0f050300c41c407024240c0c4d404c003144010110b45030303404008640e5046a0014001703503594000c0e01514030300401c410403d415a008010094100d030101041080501034100c0c0d0390700c8481a80c13500740c1c107140c02c0c20300080109480c02e0098030010b885070818400c40c541381c401d4019100b0b080c002010303c01c0c0f07000303501016032201c6083c1c0380c0c401401001c14090f58940d40e0440354414402402000b89500201e010070801130040c81e103407021480c45481e65110071884044440c40c0400900d00307501560345654100c01c2d003c00404040c0c03d4040c20801c0103a00d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 143873785 1250 143872535 143872537
    0x429061c0f08070212030405060702060c010902150406182102030a1e0c0602190b060a0305030f070b1b070b04061805010c0f02010b01051e07050f010b090c09010509040903030b06 78
    0x240708030801c5640715581e0042007802c03645c18a039180c0980007000308001680e03580c412102c489074140c4031162907061700380c102401402d403941d01940000600a1600c042c6c4c06039801031080d40c025490342400c008400500b00e03017160701c0c1d001d0a503050070f0074604420100010080c1d8450184001c00721442d200c166550000b05490846012141456006c132441c2040401d5082001801840c4020f220f0200070321072044800750b1198000c0d005c2100c5030081030a6456028014010310340080c2100d55406401000d200103a020b004140c0e58802008046400400c3e000340d150109141200c825060000301d89445250300d01c05002240c02c140d8403803001d0080d051403500042e040780601d000041515040b03c025260907500320140c0c0842e41b4000b40c1075250b80e00075056882c140e9181581030000c54000030402c0319880f640001620b0361240c580c214140140540144140e42da043d22045080d40385c0380503c030782501031000c00c0d038042582845146981d08055007c404814000c0c94040b46102c0300c040402c000b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 143875035 1250 143873785 143873813
    0x150f030b09070b0d0c0306060302070f060b12010606020f07060908120a0e1e040606030519181719080f0f07121a040501050607050a0f14010c03050429061c 68
    0xd083e1179458100b24140c040c03154000820541c24103520f8a149a40c84102c48030b01c1c4100103101039a100780000b45501e4219102101200f1030300200803d54860b03e01943c0c56841c41000c103071070f125046010070114400c00e214801c407034280b00104200072901c41e400545801a0540d4801c014152815a40690381c08a194240100000c0305001264404c0c0238001601c003260415024103050506114414194664403095a11020800200760800d981d0410b5000203c03070004e08510841d03113100c40146142c50003450f6402582c041c41a6038034842c80207030381001080711020045003910700083c81551442c416642e000149103042010484421070050071101e01a00c41141901c8032604a03a4505141c85140e000d01002c98510303082c44002d644542c5d45410558005181201704030341ca01c10480380c5001c2401c45e04200000f408400d10245000300241401c4a0a9078551003510220684803041503000100446000c0301310301603a6801c051004070081e40d1411301101d110400f00c0d80226240404003a1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 143876285 1250 143875035 143875057
    0x70b010e0a0515010e0d030905060a030605120106061e021606110115121103120d0504061407080106110a02030319020606011d090709030f0f06150f030b09070b 70
    0x30150401c0701d001c0c01100e1008090340d008280000c40300c4500d80e0040e0f2841d40540d402c0755450790000306403904a49460050f0b1046401840204280c8101e54250304100261802a82d28110007900c0001362403d0740c401d4480e030710100e00840302d0140300c0780d201c0240c002c203103040d80119000d01c141e484812030308a0380c83d400080024050b5603400c0c0724940a00880b40c021386902101c04406050040c9031a0124080100410001c541d408c0f0004545040c04043c6d01c021849108035203a00440d92804013a01d02100d04640d010f1a00251b010300c18801481d060040010340e03946e840756030800400303607020f84070b81c00b80309207a109000d60315006907000c00040c01860b00c0440007014007008407501031b14149000d42424184001c24000c101000f000e44541e5141c0c400c100d424981d10344402c2020f50715214650009801c0d44104038510342448115400c040401d0722903d030800059000640c06021340010380180c110601580d84100080341c00e48a046030861850404d4458042e80d61012642e65801010444 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 143877535 1250 143876285 143876309
    0xc080f0a05010f0905060c071406010b0a0e0402030c0d0c02030d090606030c0f0501081b040504020c0d0f030608030403020f031015030c050916030e010b09010603020405120304080601030b0c070b01 86
    0x100400070203020705081401032402c1030010f507002c4d50b212621804010042070300c0c0d80e40412444203000302000d4010720a07009105540c100d50f1a0440b201b001c0d440741c4c103008041840141c0c0d80007582018822a40f041092440540c10020701d50f19010203405503003002403c600c0103001c0c2001c481c00900c2492203440c45440e002921a24603e0024000780d01c0750702c81080b00c0311540c400c00a1b40d030040ca02d40da0041e4142035480200599025480d420701803a00710640151000c5028511290002109400c045185e164061030601100b0214151801402202d00c2c0ea00b0070b00c802c0006003021785c1103840ca564010280d0700401504080b05048843c0b80031080210451000c0030828801a00c030408040e100c280d840a14034544400300c1c0c480701d46030000c210300b095500c40440030780c0350003940429100117004100d0240d6503515030005000c0d400500600d88910801c501c503004400000045400312142c03500503202d10707880c6460b92140c1a00080c03040642410400202001443c003100c0c25002c4c1100160301 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 143878785 1250 143877535 143877553
    0xd0f170903060604060305061305070f03080a02010e0c0a05060a0c0816021011030301030f02031c020303010503010f090b04170d050702011b030902031203060d0b0c09040c0203041206090c080f 84
    0x58036261003c2c00c480d010fa07107801001d02c04142c1c0429102da12400d070340095002c02016242031842c1072031560205100c20b148680c0401008000030041400b4100e590082c000d10070350001d0203440b164400b40781e650140f40d050040107507040c60f002610215802c0d080c0080c40c0e09039070702c4410480d8440d02c0300303420346205603040604500e0180145040906c0d030b8900314880321807506140e035980c481808050300b441669486641190f8080001c0009074808002341c818420b00d101c4041e6aa400a01420380300b5400c01d482101c12003140c0c4118010540c10200c20b85140d12242c5900724110003449a0308081441084207100c031040e07500440380100d046500020340641c1202c820b07030000c002c24840800305030400c031481001d660001509942807000c0240700d60703030303807610303c00550100a142c86c014031040780c881c2009024080c0d8809000325140c1504c0501c050820390004903100e2040380a030380e21004440048030003052003980701d103100ea031040181003442d54491102c5031034401c81e04c0b40404070354040d00c04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 143880035 1250 143878785 143878789
    0x20703030c090e01030b06040603051b102c0303040f06080103030314010b070b06030c031e07050108040b07230301030501051b090a0506030423060f0c0a0801050d0f1709 74
    0x54003004030200d02c1c0242c1110300385020503849440611014101b110400041030895581783c0c4003000640c4d00204844400300e4a000c00640249003600e018414402e02031105000b41c0101403545c004180f2042000c00201c0d401d18900c50704082d0204150035110030b1001044101a00704500007411894403114848d41c51480c000301a6422205240480342c0030100400400300f10000303a820956100080c40c40907910680401d2910811100da80c0e41445000c00c80016079201310b880c0e01c4883c0800b410b0710784040d210401515940000d80340140003408160005034074610505409907603440d10311010000200c034590502241d00207800581310741c2d41d40d406010210b031368450750b0314603440100044e0b81000c400350f0016807524550f1245600517980000001c1c10007861040c1042d09400c1c0180d11040109203480b0740b60365507030031246441603014100200d0080d0390500f0030303212001915a02d5006c80d070300b040c7c02d0002c143d500040c1190507e05501089000402c4038450b1800741511076800b80d222404641 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 143881285 1250 143880035 143880041
    0x7060c0606120f0209060d0b10030c0506030402010f0c140115060f020703050309010c080d112703060103030c050307050d020303100e040c0603051b0c150601031406010f091802070303 80
    0x40300082c400400349000000074034000f40c0c0c4001540454014865035a0280411004454004010803000381d43c030030130141003103000040c01a80d00403005d808400741c5404c14406144026500607000c9602c80542c05e002510444001034682c0c881d80024101441c42d015040c2907500448049081003800b8100748111a030020045181d60341d284010401d903861501c80076140d2041c2c501c01030400c0b00704110070003401006402ca61341000000c90400000b0100d64040d0307402e03000f400d51410712a00d40a8810880380d4404c6180c1c54000008020786030301d9103941c0c5c040c1d4a110f4011003c9400d400140401030106100f40241c0b01e6452040d009560340e0319107841003200f101c10fa50031501c50384001c0f400b40004111a204e41c003066903200e050006803900c4002e001a0810201422810004000501e03540a00d5020581c8000c1007144c0e110707a80c4a880d10030066041e96401603600e14450320040014a1a600c00c000c201c180c0b030348034107000383c0351512045410f2241000b240f4000e14560002948070030154148 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 143882535 1250 143881285 143881289
    0x305030a08161b0602090303130e04020906010513060305060f0d031706030106081b0105040f0902130e060105160305040f08030403150204080604060b18040b060306070f210e07060c0606 81
    0xc035006210070f108a0300d0400712407040101500c402e43c04070340303410151001c000300d44483e00c12a581510311680c03410701d0344400310101c44c100c0c00f0322100d6012401950168060300c00a400385c10380300041a040c0942100203101c014180c82c0d00a10601c0b800c0804e4036515a2404443d01035034800c1031406401c10404041180a0b0809021760314000f8208996103000ca0000d40e51101070a51882e05040d10300100e035180525000400c141460040000b0041c3d0b59034003d2003616520aa005806a81c40c2d400c042045400c81d04140070550800c045031000004036000b84038075119040c22824243c990906041082c0240c110002a1340006001d03c14045a004900c000416140c0154038040c00c000c42141c64020203880102829201e140c0780d15196600402880a014028009469440c2a0500c420246010798480e8080d001d03283c0401c1c01c10303124043c418018102c64480b0100c0c8648010191039102003160003642c2a6911007040c4000c480511054000b05403a40d1032245004441c2070040481d0525 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 143883785 1250 143882535 143882537
    0x4060e060606070204050c0c030301061d03030a0c08070c080706020d030e030304020a05010c1730010605040b0d0b060d05040b1e040b070315080304061701031e0c0305030a0816 77
    0x1080420005030b8510b001c80e800e066041e900031889443d91a80442c41d030080308804210380c08084008a06190b1000202400d4016220750000043c0040f091603101d01c90410303034600284c4011215404034446030000c1600a1051200e44c45081d510441d007070900301c42d5003040006070010103010000c154980101915a11480c02652844c01c5c580c2c0050fa4034034840c82150305201c400410303c01407120841003610300b1250030440755a525001e2420107041d035061900341c4c0000382182100401d1481e0000d11070306030303601603c03401d1030181003054000c01a0003100150000316150b092a01d800d480d01006030165004101c80801c3d0740c00c05140c60465001c0080c40000b1408051200380c032024284101c0f9a005034011310010255160400c085003e003c10b1140c480540900c0d21001074030701c000100400440e00150fa42d4100305181c040103140381c0c0028800034000144860320740d858201d0300d02c0e0b032540721440b5180d11501c00303940340e54031030468000721034640c0070480800030092400c031b600280344506426 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 143884892 1107 143883785 143883793
    0xe090a020f032a0901080607092706140a0503030f04090f020405120c0411120c0c0102040f0f0f060e0d0f1704180c02010203040f03080603070512030304060e 69
    0xd0200f101c83c01607240e0030001940c0140859080e00419083d541d0b0203d03240f820015040074184c40083d184800844085c502c00002d5620510000b840710766051f4204888100411826000d140c0c4928081c1d0820030069085240400c1194141c84031154001403408851445000070b003c0c5411560f04200007080c103144880d40056081c0000c0700803101841034182c2022044807078000c11000d10148100040401d200b89002c5004e00480d0301e61800050070a603031042c1b401c0030100c40780d01c40707000c4101001d010720042d601c007030942e4041c04482c2803680000031900c000c144400d0440101605405018504404001d01d11440545c0300702184241c039225504c4103503450445005100d601442032402100b564118010700a59206030f400192a030701108043d201030341c400784000c0c5015418040d501c404542540c9100c0b030000080400700056807640b034103240c9030b022110b0342c8950300d8071940 = true := by decide +kernel

theorem cover : BRFrame.Cov 143705035 143884892 := by
  have h0 := BRFrame.cov_init 143705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 143705035 ≤ n) (h2 : n < 143884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
