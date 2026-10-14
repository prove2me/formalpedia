-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0900
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:35:23.13614+00:00
-- url     : https://prove2.me/submissions/c6ee4348-f65c-4a03-9216-4c1bcc410cf6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 161690647 ≤ n < 161870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 161691897 1250 161690647 161690677
    0x50312071808030304061103220305040b03091e0d05070201140708030c0a08010501050412081c020f0d0b06130501182103030c0e03100207060f0203040320060f0a02 72
    0x403509001c0c0080c010000307480c12400460300c03881c0ca405d1030410340d82d0040301031910309010401d04c0300c4e2581459408003501c080952120360f140403880c00f11f030203103d164843c07000600080180b001404002c10a8681c01c1e03188500d165100826a968544520711213003040085182009000c0040d40a005110034080790300794164144585034454010503070003180c0f0b4a0041d036000030b0b0450119004034203240540f01c28a001c43c00e00f800c20411802d01444e0820142406001007134100286d1100c9801c10365401c580c103030554650225485914190300f1401d2820080c605000d846a0700c0c4c00c201c0e064030791809400d03002c10415481c00006480520f9203003411160740030f1035040810070007004c0072240c1c082500d032034034407400c9040c60400400315080400110704002c03519180c03810b01d41e40000c20101000140a005079581000e1500c0001004034040a07504e0f580080100010726802044001001426003145118103c0402405440c2d6408440b981c04030300d403280100e10203210941c00303400400428500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 161693147 1250 161691897 161691917
    0x60f06150c06040b04031704050a06020f1c021903021206010f0215040506160f12020f04090e01022101080d08060a0e0414070f050d1e12051809010305031207 69
    0x100c42e0408108a9040d00d9000140d814007040542c065640d407810681812000281d00780799540e15140c0d0b110750030180115402142d43c450458510b0122000045102019902c100a0b001840d001e0741140e50315401c1d01c00d0608070180c00038000e00132107030300c0003c88450540036651b1000542d007007440b1021507400c61140ca4421040c1020860803071b40544d001340010162490700e0790310000c620403003106000810850a0a441030107401540508980100d06401751310b075030341610307030102900699204040b62803c003000c40600c200c06600804429000300c040b221040c400503140780e440c110078402d0740201c0d07002e0201c80460b2849112002e0b0019001001c80203090380d100da03108840f0909a03405e49081c1c1e013643e56a00201001c002c0040107004240115026619000004440b5201514054031900d811403076103074007855200c001030301c0607031012000c2c40d07003042020700810607000310b0039150201d40c114080106615000601c281200c2e40200111f01d000c00840d00c0709070388400640802d0a02010981c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 161694397 1250 161693147 161693167
    0x91018060f09142a010c030e1f0e031225060209060a03050601030b10091202042403200d0f02030a05010606171f051002030405030307080a11060f0615 66
    0x140303018a54902e00411504440c452160030b04900a5083c001d001c10844108521743d8001021b2000c0d0b0fa010300f0a00004405a400b06101c20100000680417200c0b94504203a13150300071170780000c822400c0d8101d40e600d2074180240e0000f03124640c032001d450740320559809142002040c000900300e11402001d810a00d410b80450810380004c1082800710381c0f55020060700e5640f52143d926102c0c012510301c26928152003018004900390301651640001c2c280d602d10954985030421606076404644401a00b03611500c10315403240c55000072190800c0c0340840d40c1104810b41134000d05c2c524020003413825001790740c1d55040714450500040340c05015040c0b100b40440c030f0a00c14480282241e0310b071701c81c2c0700f6001400c440c055031004090003690030358681b031103d40310803a0201c00706440040d0b85c0e01910304c060600503480c600070b035404103505110004001c0c04100c586000303001c040381c080d100c0c041c035042d102c45000c0d01c505044400100c2e20440d08000b9100d4a03104a45046222003408160300d01301c0146 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 161695647 1250 161694397 161694413
    0x8030a0b0a1701050a060e060609150a09030311010c0203040527010f050a0504020403050312090313030c050909010203090606041817041e080a061d06070206091018060f09 75
    0xa401801e01c034100000b078100111003802030b10f40c002d1101d2004c2010364280010ba18443e42c003c1d200d40d024000c04141c1c428079858804205000580081441c1d80780c010b400001031101085000403000103200529020040d03105000300607100b4207a4020b942058108000c0c800e44080362900001c0ca208020903010140e070380d00795070501800154510914050411081c04800c940d154840390142d0720400c8208046200441603074100c250405041c43c845c0c546014452442c014084174045181c3c02c501e000040100749407800003295001e844500c000e43c1c1c0c2d034081c5400c0340000ca039401d1054020030b000481a1030540d0011103d68050a9a00c107000510380311400312164400e240f0803c000d00140074800f0520301c01da641a000301281001211605000006489a00707008000b8405078a030b52402240c401c1c0c220003040c0d03003110306d000ca504034501200001d55803041544c440704240241c030303040217890901d0b000d107904210307c6412071551030301c40fa918480188001d08480e44003668800c5160005502e031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 161696897 1250 161695647 161695649
    0xe0d06091407080f120304030903021002010209030d0306060e09190c0503090705040204050d080d11160c05030615220204030f060501210b09010b190e0f09060408030a0b0a 75
    0x924070314105031081c8400d081c5814040c0c0c0111980307034442514a0f911003000030780f000460b190b020074035880380c4883c80c0580c0c3d00710881d04002d6010721000c02424419505601424940c2000c030112842c900010b54290200c0b4030380c0c02010005884856040420700700200e070079401c00f4600746c0102d250044079042400301c60081b01410002940002400010032003000941c000c2c000c101c0d802c502d01450080029020700b600d000060040002144648060f080703940f014559074500f46a0a5561402c0c02102c0b1403041342003c00c030380185024101040794100055103070b1041140743c0d50f01c1c06006401040040c01035000040c44040203811012151016030360000c0c000031442031340c6100c070558061a00030103642d41600403d0002e0444050110180d0104400b107101075000f19480703421346c88090469014140501c070f8590070090f600301c500391030008031001e41c00321414000c6a030100d8607400d0010305101c1c400d4030705d114994040d0b40130801252102008580201c4a00000250041c00c0030104641ca10700b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 161698147 1250 161696897 161696903
    0x7120c0c1401020c03040e0405100f23070f0509040204050a1202090f190209060903120405040b0904120e0120030a030e0604030c080306010315030605090f0d08070e0d0609 75
    0x180084040030480340c0c5081501d4104844025418050a032410540d02e02030303442010040201280071800f0f01c9003e0001e60101c0c034000078148415021014544040c004908d03551101502da01c2042e14999414450140680b440d5aa83d00b247d813030500e01100c0682261001c1a8004d500300800a41d564628202c2da000780307003406c1800540325850042140005004110f80003045d2401f0400101c2000701c1c450480c82c440c41e01d070050b16144e143c008510b8034042e00c40d6103030301440b40c0485140b074071740c2c0c0f032001d00200c40040300c0c1841076061710018884440780c1528000c008914a91040c92007074094122064803c0040c50501d9242400d09080d941c40843c003106500356410006d5034038990340d41806860320010740385000b00114201035800802c1c890b00300304050029040440803e0700c0c0d0f803007900000f1000880701000070350140c482c2080d0009140680c1e091000b4800c81d0155001c03140301044429040c40f0030b4540c0503150350b40031001e44480600f5609e030381c1c2c440010035401c00040d078030b44261000140 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 161699397 1250 161698147 161698157
    0xd0f17090607080c04060806010807030608011a030106060e0f060306040212070804031b02090a0f060906080318010e060f030402010e06030a09020a06020f0717010e0f0604030f090e01090507120c 85
    0x30600405020103e024040b801e04000421061103101d410070507158016400b17207490780c65030380c541c5401ca00070410368024025039403c1c00c9425a40c1c60648500034000c0c0d400718000c101a036034403101540c405001024403600204d00b802d84200500c0c2090241d030f80300c0c00140000d0b00c3d0042200880c2e8050400f02c0b02c07100030034031040500c0b081c160700c0303074409000114410903480c01100d20380004880c3c0500800f80e41c4500e441d190f000000b10015008070000b0a441c2c40c0500681e41c0310300e2580c0d22a0441010036040303000340c09222045e58800c681c0014070311005400d181c985260403911200031340c0000d20070ba0611107001400d0814ac2c4401c4010751251b4018140000c5800d00ea10421001043c0c1e540020215446030000c2e10701c840d408543c880c12143c4448e000340060481c242e12314054001c0004514850082c86000807240380c002c6511486103100380d44640b48120401e50940e6030047c035003d01a440014080140000c004e40da100e02c0e003008440c101010b190b941240d058064403119608840012 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 161700647 1250 161699397 161699401
    0x3010c02060a05090604030c0209060102011d0d18060c03140c0a0c080d020a1101030e0c0a03060606080c0a090302010f051c020913051e1825050d0201020d0f170906 72
    0x50114414160840345144c0508200e090603180144030b1136201c00003030f210740b9615001c5403c5c0d070300135400300c02d010186150980040c202401450384400440701d400e004502c40681100c005100c110f00542070b290261034841c4000129282101c203140d049000300800c1008200355404c1940801c0a15400c40c881c010710030304a41000400c604002240300380da400c2d0f40c400800800010b014110404811100303190002d400100c1001079490650000c1c2c810381c00c0031107680007000740406034000500351885906c80c0741390b6458a0552303520320f20501484800081150000340015846801c040c8407420341c500c6c020303040c8400384800c100c48403090900072060a40c002108001c604045030344980546500c0030400c11032901005407403850302c03668420340800d14a040050700700d1007607550502d44035901e0403c0310802c0d1000a1624070034055844010384130460341c100020a8035025a080c100c031541030f80a0070028a80c64003d0396511700d42c064490502c041c00d00180408004000158803903d0450001c025034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 161701897 1250 161700647 161700661
    0x421050f0f0406030b0d050705040e0a020d0605091e060c07080d0c0c06050c090109030f0309080604030c0201200a1101230304020414090a081c020705060718061d0f03010c0206 77
    0x84032000d400c14002d502000018007c2400803480da811950280d50104600200703c04441c24043d4050000750702c00e24160b1000144401544010320545c031100440f68030601c140c00070a601200c0c40024421580309200140340500080c01a00400344075088490609044000003815201d00b9160700300051600c0102e10103101c1d180c01a03a070031450b0300184500c0d0944081c002130000d40d01e4000600500140300001041503c1604600c00908142040c0c6009003402d04e002401005190700070303400110840100024002e1007960000c0b4031802000030224a5203982d20750081da2417100407981408198491b204110b803c1c9420015085030a6645640c0d07881c1500c1007004641e205158141480c103501d00708060540f0000c0e0b4468203070381207001c0a4684450034143c162200740307610280d0800d400400d8007010440300007070540c096192501c030354003100880400840324002601c034150000304031025103614089030040740d09010300c01030030380583c0d604080082805d40b100e800d441d2005030b01c0002007040d2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 161703147 1250 161701897 161701901
    0x3030609010605040609050f0a031a011701050721090503030702030d20070209040c05130c0f0305070207091a061912060509060907051303050d0e090421050f0f040603 73
    0x352403076007003c0741881d0030704900511640c454085d850241c00d181c480c14030190f0b6090074850056070b1050b0115004100c42d00f000310450801e125204000480800003200200103004c0c540c13160440382d507061040030b010004000c41201802d507807240d540da1941240c01040c42480114440d0045400859490100701c4a50089030100c8a0a000508121074042c0010f4440400c03150140d80481d142e12640d246e41c1004000034a459010300d070700c90b0380e0034007114626140b508800503226054440904104100200781d0950700101d550300e00581080000303020500461b403000b01c0d074801e0032060005044229021030000c0e4810801300c50800404450740c0e40250740040300b81c50b015041038080c80789501c0c0002003015110041d280620450310b68000440a178810b20940b620a0a5000a4403440d03030b0364101182c82d540548054000100e524400b441c40b410b0540410f0b0145511102c8182003502c2180302c8075062440d817010f1070410008100210740d403100700d8090060b80400c05c01c4a5615444c240740942 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 161704397 1250 161703147 161703149
    0x20f0d060209041113170a03051e0409090c0909022d0607050606120a05060c2b410402060f0c0c10030608100b060f04060201020403021305010e150406030210020303060901 75
    0x261b040160760b01254407404102e0f515220340c1800c10580b291051105040c100d046012204481900454001394040c0740e5084103100c10b00803000300e401c0f00e4903105048290b600c90540030750883c0e0010700b04818820002c82502e0008a00b00b918080c07411800009501a031140c02d0035901a80050180040d510701003619500405500c00140508545603a5842c1c0b5540001c00310f102c070f440042406101d400c2d040b065500c00d0011480c600c4030301c03000c03800480001d104d1013554440781c603048450901daa074030042d10403119160b29018240c14881400c140c091980005000b00c0c0c2000041c442004001c406001501c170b0146560082e200c2c24140c501071101e500c103e00080c0c0101810020104420324010418401c1c00f121700c5ca020400c60501404210315115050306684042000100040d50300c6d41075010303005684c8212180742c6017001c643c601c0030981d4001c1c014402c000131f40310702084c00c1b010b02000c508811103000d070020039440d035aa00010030a00044e22140050b800003c10481145002c00901c0c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 161705647 1250 161704397 161704409
    0x1050a050105070302060406020a0903020604060f0206010b13051e04021903050a02090603040308040c050307172506080709080604060603030834030e0105180d020604020f0d060209041113 82
    0x2d030a04800307860081d0b03507800140010b04200d074002445074031284036030300301c0000d1178005e8582035a903582d0307113002071440198000500060048038004924452100103c4000030b4101f1131512509050604002c0c41c0044014803204c0c0d00c0d1040c95900460b203a600241929030120001e81402241e80038001d410741d071340140341c0c1d031006104002c3c501c0300b5500c990a9a0b00141c051904000d966142d11f07184039040c9d01600a80d5041c403400ba000210395000300182000a00d210040d1803540300174213400c000d02e0841201410064510307480501000348261201ca0b4020841c1c43c1c9002000e650311300082c00c01c6410340d01a00d84035200c1c60b0500505800ca0b61054006a08103a000b41d5148007020342a00c2c4c1c82031040540000f85400303203009060307219410505c98116040f0007003040303080004030b4250308940420301310040e01400403012251070012400300d11894001d80007c039034107041401c0040c0100c4207482103c1003542800000005e481b1445502002111000300640d21406503c10303585556540e4400c07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 161706897 1250 161705647 161705657
    0x5130e07080d03092123090d0b0a0b090609070302091c050606011403090618150f0603060f09070b0d11070c03140a020303041505070212060105090703020301150e060409060b0301050a0501 82
    0x2642c1e96440b8241c10702c6e90544855203803050b8803101c00d034512482101c004039030199010b410001408030318962030340184001e086c200640342d91071041c40044c0034201c0e201584801050005007096000b074005116011004200381800d4041000c2091456850403056640c2c2e4091000c101c90b950300100002c202c0322044800604600e0003148656131810b0003411902d0090a171490954030f90010801c142e10344021f0700d42d00103585012044070f20010002c5666910038840c0f8404940045501c0030a540110328803009000e59904010100740b6650000c40c003803101e41d0751707004440ca040ba60400038200381440384102d80d805600d54205000280e500d08441307640c0c2d07044482e9820041c0e8000044508495101d140040e03141c11000064416008030900650040d910751100e500900000c50000c1c180d4104440302c0070796403600d81049003280001d000d45180c0007480115a07542500801c07440006500003011030346040c2e2038600501c242d130110307407208076102c1c00480103105034039011008501a0600f072800b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 161708147 1250 161706897 161706953
    0x60905010e1504200708070218090709091a010608060a050406051003050619060c0317071704050a06060f0303030e03070b040803090a0602070803040203010f0605130e07080d0309 78
    0x9000e1815080d0039228a030f40b0540d0814051040004008405103402e030613440c1c025601b45400f0343e92044004920a560303002052115246107030301c040c013075080c2100a10103035090400000082440c030000352651544400c0c48040c0c5045181742c40d000e03089641d101c0c456800c2500602c00822120380155110f0350910801b80402e40340c01844144140d440d180104940d110680416403015203501824000056044c0100e24950040d607d43e040b94469625054038451065401c02055020345010000849500290040c8c5813640f03c001d8120380a00305441c42c0454a03a510411581907501201c2504941e100410505402d40310b01120041c40c078000d58034058040d43c03054507407a0001c000a002007408004911000310811025440c40d601090440d030340e40480c2054549a0000c6404a100b0f60034500c481120840034001c901c04c844016043c4045800b0b440043d8009e07000b44192000c2602c01c00c080000c803414100894a568110394500190030303400790500d4079031031030a41001c1d07119a5000078 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 161709397 1250 161708147 161708161
    0x20105060a0501051801030b04090c030b0c090a05040902042318120a03180803090102300c0d0207020312090a0e07090902070c0302031b0a080a0807020609030c1003060905010e 77
    0x4129032482c4050b02201119170b400c40d0050b0014445078841682051074890a401004502c0c40a08182c0f0301441d04440030b9a50080805104c2c031070005159003103c82103008110720b09040e0840035a151006102040c04542e00681c040d820b490458800c0f102c00c251000d00c100131a0001468040381603841c0640010f05410351001501e10454600c54101559001c8124180071280c00f5400e041e80d000050565030709003a44050b010390000041c1c0805441c040d10714041c0d41a0a0764160940c0501c0c0300c03400100d54650310045d481d41c00102c6400318094013001140c0c0169003c1c00111a42c0105070f0341c080d01d429200c0148034141c00e490b0000d60a500580d010f02c54042c0d04408103804507204130b100036070b488003a8648410000096400203425125941c9190707020b00000c079280116460590b514100d80c0d654030305166079081004405040880104084005414040000c0c090300b42c002d01116101468000429207800140c0600c00000b5a00c40f0248000c10950050304e0050001c1d124440740b50074001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 161710647 1250 161709397 161709407
    0x30807050708030610090e010902030106022a0103150801020706050901110702090414070e01080c1e0109051e0a06021005060406031e0c0513090213020331050307030c03020105060a0501 81
    0x14040d140700e2003000c60404174207880b652901c4040c01c90381042e1030a40d44d40d943d400d00079410a00648000d400740d4070701b418010021000b00c0807090034801c8107030940300c400d80055000b000116104c0f404201200d1002c61610b00900090003a6881440000b406150145a40b82103e44408031820201300030070081c0050795810b40d005800c00d03003003902d080c1c08009020080e403030501d280d40021403084c0c0c0b038030001640d030801060408000e5003c0c0d0300303640b01c12083d0181c80e0041d95903040441c0450b500400070300003820261040c0291740000010b0400c0c0044640001d4686001340e4041401a84007002d85903291106004d6141c0295081e05c050002900359940d40321034404c000302d54000e40c02c0b641c49900a101750340703a80c2d000801c0090848407a0303a80003411070015002d42c0c60240e0049020f2592111455101e01c21a4825030703000710581e407180c003600c1205008070304c43c49480655501c11807503d00400e4048c001401c2051207034617085600c00b0103290107404d41e0f0f070003400d403482507090345800c000c075907041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 161711897 1250 161710647 161710651
    0x20a17090f06031503060421081605070510020d051e0f0604020307050d060303020618030f090d080403050d051305010201020c0a03201c02060609010f12060f05040c0303080705070803 80
    0x200d0b80d40e81c80365100c658141c070b588070016020703605100313240520051200701070f41581c050b0307804160205110010903058441110903140500c04c1c200e0512080c580500c901c000c2c00c2001d108405941c65101c0040e0484142d070030892000c05500d5a0b10140174010785c0186180c00c2031113a255078070f2a5442d010000e815600802000103000e1030300000003880c11881001101d80303403080c1c0841040000c0c0c07241002036540008271452000c0b844654500c05000c4000000e9524840c01240c01038174002400f400d201c80c511007003500b140ca030b220038080400040c0d4103001e800060038082c1c0e01e4a8840c0c4400d0404c000b6248946c0c8544e040d64410403e0b03000b80c08012500c070081c20f4140c01c02c12171009070128141c0721003100482c03000d0203018030710f01010158030703402c0070b042c52240d40d40c21150287c980c14200081c04100b0703c10b100000202500c1040700c1000d0444011401f80240c00c0004d5040f5055141c50580e0700c100c070308070f81012042c4018410150440f94903a04220745151490500742d040d075400d001c0b4400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 161713147 1250 161711897 161711899
    0x10b032103100503010207050a0209070318020f010504030515070e010921050309030f01090b0702150712060b07030201140f060f06160203030c030c0d050f04062706020a17090f 77
    0x1000801e620110b101d004003d000c081c00866949409003412a00c804404d08100e100360303042c07408105c00c24443d018880307407031400b4914070f8000c40e801e0b82000444011202c03c207051140a00000011450a002c03481c1e82d4018003100701d80c58904080b00030010405c1100ca0b6042c044009400e00441100c85480c1100501d100b00302520014103007402450360040819065061091a4880c03442460640003416031910441100740280c03281041a0b0321241e03c1d4001040880006000800007445007001d20802101002c00280950702c48800e40c0306a400714205801603034544100404c030840da1b0300c00e10b070312100c1c0058042050503d04002800860008070042c03180c2000306910310304648030751f9048045580102200d03a241c2c0754000950b220340162500112600805011f07810103802501250350005c0c1602a040c80c02e400c018040d0341c40c416144940e50309098030160100480180381154001e00156001460020124981580c01e5220104400c1e80c0f404140408016a12180038410b076a01d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 161714397 1250 161713147 161713213
    0x80c06041d04060b0603070c031206030f030f0302040305010504030509090708090714061c0b0312040510030f0912120606020307020303040e060d080403080703200a02040b01050c01061502010b03 85
    0x850f41442c2c07001d412001241c5502c503800000f4020b03030940014aa201030340c440c1d21600020080404500300f102c0c0107210103055100700b0441000007074030441555034a4401818010b003016202d07140c160071036030215011004140009110425450024001c036800389003454500c1d03241c41d095241584800f5940710741041c010800111408a80d03481080c1c032a545e00e42c6500008010300e078104040540940f0080c24040d002d50036904481c10800c000f00d07001c0e240701420f01d0805e41c00b000e90480080070812886000e80f0f9450031404002900b00c5c030308000d1102255114168800700080d610102c800c958040d80944d4030400c00b90300141c0303001c41942d00300c030f0202c500144a5034400d004104103405250300100349500004020082041c41c0c4090031405009070750b50429024542808040103001c82c3c80f01d0102da0103000300200600d400d03040007a03281818940350341080008d14900c0d007036500075000240601c43c5c0040e00f0044642c244543ca0109030224000e10760210240c40f192440e403042d22500b02510303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 161715647 1250 161714397 161714401
    0x20d0f05130b180f070918030c0314190c0c050406030f121e020730060c0509060a020708150f0f07020106170102030403090b03010b09040914060f01080c06041d 70
    0x61800f107108501c840c680b07400d4580100003141142d442e8400c0c0e00030345d50f92500d441c084441c01e1200d00b07926040c8542c50f4484a08440301c1d52001e83c0c121395010b95a01c41100c1c10030095100d00e031151007a84130800c194403000031104691404021140142d0452800703949808130420100c0d41170f1020451054000e43d984040365000f850032243d0490b00312b108510003543e520320144075940024801c0c00c442143c10301715040c0004400a800304015500b0f14194000b8044001c40850525448644c00610508056240c0f524050100fa1a50084001074000da04004010400c4d81001e000224000b0a081d19400007494100f2050206c41c40251074804500440d00001d60124001d5014001a2450300303070b000e20740741084020390301139171049034110001442c0803070016200c000c401c25641a551040e049a00309034030308003840700030504224180c0b222100e440004200400510601d4010b001d00740c1a142258100141c2d28980052011705901403071040004102da064421903480d07510220321070110740340d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 161716897 1250 161715647 161715661
    0x5060105040306020f120414070602011406060d0e0d12060801021204030810051c150507120e15011203080705030402060313020d020910050f0307080607050a090b030a020d0f05130b 79
    0x30b001e001031b040b1030070003044280710621a0f2840c2c620142d0480c0307011141340c1510348030200c1c03d0f90701d42c61001401e60310150106801e860000d01810459218410001d400b45002880e14034014808415001240382002003803980303002801802c005e400c00c00000d5180c61111203444200001c0100050300b04041e03480420303149041049a4001440c0c0141482c24804183c842018030070f02d0040216050403240019200d40d0606006451017000280c4170841d200c3c405038452409486c066800031202d020b45000d5129080380c0e0680c09010380024100100755554901d009451114081c3c144401d00c201031080000503a500000c8941c84850020751406150451021030306c00411090000c0d41f111400c8200605504200d410000300c0c1c1085500a0b003000c0b04070141520b0311042c0c0100d088640020340060405401080102000c0c5c8607032038030442d038a0380d0388034500841e0420744811021613000981d229408156000746000614212400c11141c20406450b103083c56062900a0031111410005000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 161718147 1250 161716897 161716927
    0x91207021801060503060405070e01300603080909070c0b010311010507120807081e0133020105090115080d0e0301020f04061709060c04120c03020402040303031e0506010504030602 79
    0x1c407198007180c084842d616010040e00e10740045a5960240c1c5c9410b0015040ca40703e219402000380c01a140d503e070001000326820740d41026003a04c50400040d0103103880151a0324455000214010004580c840880a041090f5070030003600550810060f80c4108001c02c850182c4981140c1d8024440d1164a1a150058559008298004e40941e02c4003c10741d00e1103800810300d83c405d1020369100302c010703501d540c01101c1c0340c0800e96103205008062001407203540109020541e404040c84100c48441020b8100d4820849401e0700300360060b515032003407001c400800d0040c036440f944412106100301c2d060004295079000c09042e91400c004c8842440c441c203413001e60441c0c9000302e00785d1407507a41d151200005440700751803403000606128100e0000741c01c1c00020413024042c1c68a606104d2609150075507400c076a1010410541d94441300750303400001640c803880144011846520042028202d2001d00e48424200c01ca0440a00f4140003c0014036a13214044070107484d48410b0041e2600b90701c909450b1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 161719397 1250 161718147 161718169
    0x10201090b07030e010f0c141308060117010c0201051e1b13031e0302070608090304080607030f0e0a03082403060406061703040510050a0c06111e0309120702 69
    0x101e0508018000d903140e050b04a24054500b00009010740695002c034042201c001c0000440082c0c40ca6084092000300c40c0300510781101c450243c69611500c03091280d0803c0420390024040c010300b010452403e00c42809240388402072400200321900d03002c40c444030740c04a011301c02c41c0c1c0c03e0444070000d242d52560240031401928860301168503000104a181049001400182d030502c0001e11441004548103803001044e030b902d68094210309203001e1041d2180b12004c0d0407401240810701c40800c40c2081000400c2c0b1a0400d980d0100c0c4000703c00c44014121503136100380d0b501076044218010b02090b00b1034141b03900004021000c520509419014a2106800c00038541c3e06004420500050100c5500440240d64800003101108051440762503600e1213140302d03494020a0b1002040349007409007002d403800c1b20150510591602c8641d54903070445040002840c1094400700c0c00c446d103402042840c642a544104985180d0f0500c4000b25130303034014456810b02e844400060749800c640300c0700e10b03200c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 161720647 1250 161719397 161719403
    0x14010c060e01050106033806161406060a140a1e12120f09030b040b0c0f031e100f150e100c03030f0216020d0203070518010302040e0111030a020901020109 68
    0x11541c4400008014040034905c00382c24024001d1507000035818001c00c2c1008041d1407031f0f80843c00025009000c9960401043c2920303041c0c00e0041c010220b0341d1104100010450040680740f686481c01c200045511150800c11045811444803161901c038076400d2802d03628000d9070040c5054070607200305415403044d000408240448090070040040d408d0000c0c10a502c0b5440b040e070304d00f4a040c4211040c100b00c1c0300140c8040c0c685004500860a00d4460680140d1b136a10400c0c5002041e03042d04e507a9a1003910f40000e9421800e40c11080310716030040f1944c210003840351210310355151030f54403444000180500a064a103910106080c01d01800c43c1c20b450820203003000041070307501500a0720f03444c1c1c035640560201b03040c8824607501c40400d100712815612451030300c01c4101e40680070300c0b2100e1080981207070140324807440460180d40b8505008a0442800c02c070320429819817061206407000030484000c030303a05141078140c4001d407503402d076075101c4000c4e900185c076110280e0040b40504400f82e40a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 161721897 1250 161720647 161720651
    0xf03080315030106180f0f02071a040201120516030c0f0507240507090e16080a0b0a08010f09051b01020703080a090906090e0d0807020d0c0206040515090a06030614010c060e01 77
    0xc0d10300000b140c1c106d480038001280007080807160602240c02a8403903150002e105050812600001c5828540c00580143c018506000c8d901c0380b42030705000f200c3e07080e0340e4001c00300d01c0b08020340540c1d58140500c808141e500c0c03506141c2c5058500010b842c0307001e201030003450061204c658007015403203074103000c801c605940700501480c180b0303007030140c60b001d505e01624807200c5c200d100040030f0215004150304d006025039201c01c003075a1474007445e200070440c01c1d103069408034803988001403490023409800002c89401d10b0014042c0031903c0d205150007800b49034001c1c060a4401c403080141e07004200710049940020b0007582c3c0d81030500003140c08080c00d0b040064028075000012070181c1d82d40c0d01c020081c1d10050300b191840b080500c419a4010012510100181d1090080711b400301e100340c802034205071002d00300c2414035469100096131034400d5a900244c0c00300205a1002a00d0714802c1c5000030b2607181400c002c0d640c2068010b20000084c8280750b41400170714031040d0200729003170784080c505420780310007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 161723147 1250 161721897 161721929
    0x9080f2b0c020310020309120f0a03050c0912010606170f0406090318030606061b0b070f0c060f020304110a0803090103151e06090605090108040210140f090a0f03080315030106 77
    0x3d2130700075001070320a140076105031903403400c1d000c0d119001c659103000e103100c40508004d4050300803800342070000c00301c4a4514040c000008a5100e00004170321300102c40b00041040b0381080c0d4010aaa004c01912800c102070b100144514412f258200d5a0496044240405d018540781010703984420341c000b9902e203590700c2e443d0000070304c541c6a101c1e005176001e03665019080303800780d04007400c0d038141c14202074410f0300000045020140100809400e01200f420041c8680c10141c449204941000054001c219000002c000c20402c0800e0b0f00d00e1050403c50b15412240e05180000da41ca010b24010541450350750000a00205c0f48181360400600e15100c0d501c01101050308001480c5078248100380c0480c8540d030000c200a4003400c1620400362040e0b42c2d125207070380c483e000c01a2000c000041c600500000c9001c281d0b61107050001011409070300c4050556400c0d10206001d102c5003203031f01a402e00040d100090001407180c400b01ca4200400c031480c0942d120704103002038018041540704080210305800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 161724397 1250 161723147 161723173
    0x4050618030102071a011802070822050a140316081009030507020402030108031c052206090c06050705240c03090c0307150806090106140a1e09080f2b0c0203 69
    0x12205d81a1425169034000008081500f58180e018041e03006281101c18056a480381250640700181409610602500940e407640070a0f07403141d032a000160740240c0300b445460682020041150300c0c4400600c0c27200900d282494150322848050200081242c481503481c09140c490020b81c1c180640042c8215030f03a5a455107416641da0011582544141c0c03801c81c81d00740c0300c1252040d580b00c0d46c06c807441c01b0409024518140c0041c03000702d2040300d0381640c0d410510003064501d00281d000d01619203400795505134230b0800750700d0880d07580070704420340c0d50008441e0510500020303816080043e83d1040b90316511a11041801e080c4483e02c441e030148182c810010b000f520540210149001c1074450f141d440d160700b800d11502403001d0103060007060403005501c01000080006201c01007441c0740a400e22015440131410440c0b510040030001400e203102800080414808500d05050711001001080f62640c2c0c1443c0d800034042c00451141c03240c10074859182d0040b43d080f400954010155000350708140d0f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 161725647 1250 161724397 161724443
    0x1020d110a0206040906080c19090b011b0507051201020a02100b0102030c0a05030d0e120a050715050106090302040501080c0310020c0102070507091406120c1c0b0703091101050405061803010207 85
    0x100c0f070182c240c810111140e000b8108020414040000340b0f4107040e24a051030700100203020711407000b0781000386240c01c94de55641ca04114800c1103203d84080c00c2098500010803640180790f0300c068005034410081e10900d02e030001414450781c1a18800841d18008150050782580102ea101034034034050b00310020200000840108501c00d0311100401030082039034003051352a240c25201c815000001c0292800d41070145020f0a6900d101d462918000201d07107640000740e9900382c2c0b0100106074400018411403615014960140030388000034041e21040200184c2c1da910300e04001d0101c01c0c0c0c00114803000703c60a4040750002d54004080302c1e0450303034650880c002400000b5003030b2106400c2c0c0d40440c0741840c042102c40702074141310340104002c2d8244400c10070710141080c01c000c500e065201000000518030a0410301c6024962000a4007502a04101136880401008a810410104424080d6a40c3d540a8401c4108a02c0c02c4014031030601c0b021a00920820308090038441c1c2409201800400399 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 161726897 1250 161725647 161725649
    0x30b061b0f0d03020c070302090a180b01210203190501061707090b0105030c030403110a0213090c09052a04122010050409022d0d0e0a0201020d110a0206040906 70
    0x45a0308850300031403c0381240182140010181c000000030805031030144055a0481a42440007504000c002041d034441440894100c8107902c003003004100b207400b90304904c0400c5103000f507100d00061240d40003985034406013080d155004888100c0e030090020962040c0d01501010303013008640e00807901c0155442001b4411020510b041541400f12035100e241983d004404042980741141c641d907605030b4454121400c6443e480c0304000c100f01c0542d45038260003080600e0f1440008164070f16003442a48200c55800184055060030144200411001c0022156000117189450000c285141000081c800e40c0e111002c01403c0701c00d4403040c464810060401d5030720000b40c03050090080700500c04000350000c14070000c5030041c0002c0000bc00240c0051108194680424003901c0c0c850314001d9000b4a5a0030005850070041084140d4140303912030759125903c1c400040c03d2614080e80000d540705400c0031900c0410496070f90305454810100b2006003003d6008040c1c0d520789807240a030000030015 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 161728147 1250 161726897 161726923
    0x160b0a0b0a0f0b1204050a06020d23060105030115020a050601080312070305010f05060a12061e0f08062208041203140304050a110109030f0602120c1603030b061b 71
    0x1103070000581000c0403401c0d1002c80b0071446000c1e090245140811207450001882521240941351b0841c1c00070341184010803480c440310500180040c03070102c02c107004140d410761400c04d082200080c000c16a80000030b0701d04685841c00000200301c8048001c171309081c5800402821440340da40045201100071018010205415480d500550369035101101a60000e108070306440140b107a09004c40d06200004007100c074010f0501440307104070000c038542140c502d94000046110851040422401e00e5040040205006010b00350b10b47d0406081c01c1d21080b0242003900303060780310007201d60198458100c1c01030f5103401810040c0c0345e960b1748804240c00c505212049000a2510364058810754500c41034034011900000207110305c440326a10381d410384006401060502155110010014502800a04041d0b200308400741c0c5034511503003c80138841c2d015006600c90750040c8620922814071904090b0200d41502c0e0102d124440c3c030303001c40c00620584804a90400c80314450007a200300c000303040c01640c80 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 161729397 1250 161728147 161728159
    0x1103070e0604030c0626090604050f010908030c073206070801060c02010309080c0a08070b0c07080313060b040920030319080a0609020c07030309050109050d08160b0a0b 74
    0x21032908101d000d12450000500d500d400c00c200344482803240100100ea902c02007111a1b07005c80700340e01c00c0120001140c07030841581c04001004100301c4140807084411074000c0090011544942c0c170303801c0718003004100d1091505d000c101c034000e1100b03003806d0040080324651000900c04803081d0342c6840c0101800300d20510f10680010401c1244030b01501d0303040b15034a03501c0c08007040c80381d4011070103080d00810594010303c060040420010040c4144070f2110300ca454441d50310340355894a5640c00400801d280468202032001c0004200040c0813240d20003800342202d901601a2300e4101d00030545007000a4015141250440c100400403141201c0180a42003000c42c0003401801c040d620b218035800024040c03c12001708141601410815801840e12070010810f140c40b902940120303080070308580100c0c0c0c06490104281a000105180985000c2c40c020039082d0400703010a602c104a0103000f89005000526080301c2c040b00000c000d0304541c0000743ca4054209081244040c002d40800144104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 161730647 1250 161729397 161729417
    0x2130b2a03030124020c0306010807031703060109060f02010e010c0819092003150907030c0e0603150a090f060e0d080f04030e0a09020307030609060501020f10020319110307 76
    0x40c0c00015a4100c0741a410700c0082409880000d4043c0900320b8031880030351181004980c0c1c15903040c00020302900112005002079440e60074030f6140d452902c030003200107100400c2408903999001c080c030025a034480c2031400144a00381c5040340100340d501700c4c542c0e0759440c1c01c03c101602c9a0056541380980808440500c4403010140101d00303d800d03d0340300130311800c140c01d2807820260080703c070300301c1c41c00005041d40c2d554002100010325004080b607400241d60009030003841000700404045001e0712b00c402a0b0075091600c100420742e42c80400c8910008801182c0c0007c1d20382d802d80c0c00644043e9485455007601845030300d40440030f06191840d0107070345d009800c041408184504001c6110b42004164074440b03460f507440903182c0302031a61030b0301c1c0c000c02c00100c040b902000344d00017540511704964002400c40d1900c55058102e40b60354200f58115000b1600007007960a0009040020440d03217a00146c0c2e0381c4030700020200701c03080c0800358290142030080160303641104c80040c5200b1500e94403054004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 161731897 1250 161730647 161730727
    0x10050103110f0a051c02060304060527030904020304080d0e070f060201110f09040603080f0a02120301080a0b06060c16080712080d1a1f140301080c010302130b 70
    0xb496880b80b2a900300103015400c00c082e1900d480681412580003a81000c0e040341030700403a10591084074103940c16600c03001485144000a84106246004020f5260505420b41c820540340d00c50302400c144110b80100c0442d080c000f59200700d400c0021074000c20456a0900e0071804e403100350600c10f900f401000d94100140d03081c010700a02c0303c180640b01e0b0b071034070f00400340802a215030031110300703140c00c565104d00c007100044010004207002c69000d409281c41e0540030800038603205000000c0000b2000a200400200800056916100d0341c005040d041640c5d510011807928010b42e10b01401c1803007482295241c0c0b250013540c96080c0c07000324055440a0b42ca90147c101c4d2800606002000510104501c0c6201c80300e039405240581c100480d0b00c401d2240c40b100040810011480103d45260315003100c444880d04803e8201a03480300c004020f0841d03141c442400c2e168203407604182d050640000300b41180c009200c205d5805045c55030360581d00e4007003003002c00c84504400c2103400c406000480a88400e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 161733147 1250 161731897 161731909
    0x1e030d020c06041a041a041a160303050402010c05100608010b060a09050d03030f0f0b01030b1e0d050c0909030307020f0102090904150f0e0c011b02090610111005010311 74
    0x1c180c000b40440745400c3c505003820300302c2d808656900c4000d000901c00401c22000701111035400c88082103000ea00e803410222806c60420701004880d44100301005503602c0c02c803000c100c4810b00e0f50036041c0000c5596442c0010b81d0003820300305008241d4040d41c4011040300d50b10354890b40c1590f243c0c8008000b9840070900780000e070312034041c800d00031032029101001146000b1a0288005101c0d240105a540c030400b602e0081e904031003810f050460712030316064002d50341441140c50306c1c0e4003180c0012103c01aa03542c500d60844d20002d1034040c0305901c1c040c0062007000c120070715400c50040c0c4040c00a203031180016840750001e6a00200601032190400009001402a00e004040007421700507a42c8a0b59120b064550003051154131041e01d8440102201c9400e03c00e8610122480e4003901c075503191840010001c0d950400e02600f82d06c03400c55003101607100c0900960780180c05a60f04400c01050346401d941607290245160141d210703400356a0707119010354011070304881c880c4014000b240049010409 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 161734397 1250 161733147 161733163
    0xf0b010b0a02012904020c070b1602090c13050f030109080c24070801091806020c0d0e01030212060d06090b0106170f091b060c1605180610110c1e030d02 67
    0x444c848010000354140c6010307801440344d000c1c200300304c3d00b0381540c4494411441d005040e02a04442d914003070701095013403000700f46500180105146140a494a40201c2d80d4400e42c0162805080700176070125807910300f544401101900000d40c180c87d0704814020796518501d844045030000c101d0051190062003c541070380c080c08003034945424a0b804e215152006010023441c031050340c0403203e0302c2c2000c40d141c0d00c0241010180324000c0c220038214540040e0038061245006810144104034504078050010030a54000808072801c00724446141051b00c050701200d00040c00020980d07000040e92600400014402400103001e211f640c0d0300c0c00111024028100c6a11041d60400103200c0d000a07604801030400110040c041c5007072000c03108125141003070750841006000006070381030055142c03a12418025081d08003800c031540c980310303010800c242c50f00380220082c48400303814441951001d0000d01001c5802614206400311100b4031070051030424440c0310b009025650403402d1280c03000c12188 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 161735647 1250 161734397 161734451
    0x20102040305062a0f12061509010c2604030507060c0b01050111100f0f0e01020c0309091008030a0f0f030b010219060f0f06060f09030b010e040f0b010b0a0201 70
    0x11196694010218107136a20800c0c244881e0155101450140750500010340705100d26003810035240c0071040032400403a1030117000c01d4412420106000e400410800c2260f40700c2a0038a00104843d200b4948031000c51081c06409194040448580d908842110042c1089034082c004642d51a540c030078050ba460612444c0141c412a800c200511a40d401580007808201d545405c4038004114404030004035021140c00d10001034840d403041e090341d400c2c2d000714014038680d00000c515102103407544a5880c4115050980120354500c0081c0d4804510030650004103d100c007946d0703603101da82000400100b850310b07d500225081c02c03862000c240c80b078483c405c003404c0e060300241000c4199001d410640200100c04a0768a9118845044040c01c14010381d01104843c54001c6406800c180000d8803082003050744004000d01d111082002c29600d20311141120b103d0f010b041250b80711400e1500c501110407102500c1808100d00004a58150100500018006600030003082020120710f25800140070409 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 161736897 1250 161735647 161735653
    0x80c030a0905150f0709060905130b03030d0f0504060c0813080903030c0304030c0609080622060204120302070e01090c050909180604080a140a020618010b0d14070501020102040305 79
    0xd98000e445a002146403401141203039a2440f945481c0403a590048039081342031039480d000d02111a8002d050702c03020700501c2c14410641414000890500031030b034140e40074a07545503014050035032024000c0313500c200c51481080c00031000304040d0101400041d141259410324000f2320708400352043d50402d01540306071030403402040064940020035001048965450700081001e03000c01e140c100024070046110350f248000180c9090b0000c0c024107441e034815251900325800b0041c000204942d00004090020001c0700891010b01701180240070301d404c9460003861107800c8500f032580020742ca104481c44503052601503a00c0f11199010780e001d0810b0b00b00802c006014500c00c0346040741c0c1c40e40c0c1c000581d56502d041221a1400d2514140342940c0c1500c030395034001072040e019503101c032600080c1100d41c00014549284850700079603c80c80203081c0b44240d1000503109209010a402114a80000805081e03a682c024200a0701e0b003403150f80c0304405440b880c8400204e5500600a4400300e90308000a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 161738147 1250 161736897 161736901
    0x4030e010f02030a080a061e09050606070203100e07050d080d05100f0504020f19200606010f0c020102100507020309121b0120070311090a050f130311060702010b090106080c03 77
    0x420740c0d005c50050301c5074650035120f80021030114000000e45680c0d10b510078441850701e28102e4028122a0040e25541c0510380421440c009610000f4a4940040013004000f0350141d6442d59070341004e810b90801d80e4460f00c010010014006400044c20701d4400e400010032a9495800b04145528000d10a254010312545c0082001e854154040c1a003000c0b129180ca01d07141c0200030342e1420407641c0c18080081081c0131021920916006108545042400d0050506003031000c006050442c45050110400202884940459200344020082c0e02000319081c0010305000701d0107512031308107a807403600401284180c20003c6100044d0b80c1d0a03042141c46208100044800449280f0707480c01030040d5202c1d07842d41f4030102d5281040004004c0d8011b0000c41c2014196008120800130080e1081880702d09000520101c071006940e0141c1003c0c00c0b201d480c004c2032451405503003008240d00000c5050003090304101c205a01074100400382c110454a001c0340e170f030300d941050b5150340d002c3d910f0b003003046020704c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 161739397 1250 161738147 161738167
    0x203011b30020d0207080c071e03081c09050a030201052211060a0513030507140402070b0c0307021009080d140c0403030f0903020d0f021203120f040606050603090604030e010f0203 79
    0x1006007043d8050401c09494180d040e00e91424940c40740d841080c2990140c48200800312401c0c0420419056100c1c0803185613145885011107401003503c0e1412070046055802150456648810b8201b44d1140503100d00c802241006402001f0440e402c9102c49406000ca032070201c0c076251a0380c00c0981c00b103031810145804800380407040e00500318041c1403000c100180307080c0f9070003401454000d610070001049098104024a51800c10300203805000d07500522502000442c80d2095a5225164042098481d504c440c0300300e26149140b03043c00b40c2c0743d19028040f070901a40100500c40004204014001c400c600155041004000c88034001019410b100500000b0b1251405481404442c07030107102903a10b0360001031012145420803220b8100190503a811410b02089400041c41c408000d5802c02089084d0b0000f902c070010494946000b00d40d0002e0100000b560020000d45006451181c6910f041080d241e81d4030420354081e03001c01c06600814810750710540620b1101c2e445030780a1800e00b20090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 161740647 1250 161739397 161739401
    0x50d0801091103420418120c031b0b15011115040516140f031603030c1b27060612020337062903130203011b30 49
    0x40000751442c2a801042d04492400428007075143c0d8810005601a240107001c204c1206e514140000d584002e000c441ca010070b90b08503664101c103802d424115001010b924044540201884001c0d100c004550219000c2c0010701c094184560b02c610065901400c941006413141c0e10508810b603525400401500c2e0505d80e2072040c240c220b84540212082c006210860b0f90003415941c200a08004424a003030000385449a40885100c00075809007074905c2d881490300b5181042804058284048ac000e00420042617044c000e07020a070891944000589680340c4955404d40740110216502031004850400c8800384502d00443c0d5207a240c414003d40d14a000354060b40008228840398079204108025400220603042c603009080102001c0c6003001e00c401404640c510f40054580e400800036040400300866440e1740c20441d0311101a80304e50f1200e5000c440489035140007509542014460b10451410f14070b04144c01445448543e101080c0050540f002101c0300c040402541d44e002608200410355 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 161741897 1250 161740647 161740681
    0x21010b0f03220203010f0515041a0d110306070903020a0f060c0f0f020306090601230901060c0c0b0f03040b15010f0e0414090a060e031603050a1b050d0801091103 71
    0xc0003500300840c2140c1c001170300b102c444240c0710020301e444104021801204400c64000b03410115801c20500000b01030003a81103118440d00c3d8020307807050a070f071014000c0440c1d12400e641e030001c04913040d0713240c1140000c0c41154076200490007240400c801065420707030506817000b80c904941e503403100700c401c2e80c50307001c40301e500c660040d24410808400716000d03840c03c0c4001c0d0310800c02040104101d51400d00a9001e45208104201445c202c3d500a000d4550b81d1460141c1101d08502e05181045400c1c140016042105c0d44074500c0d4050010b001901c91960002547c491402183da8a0b03541e030b51000102c00b10b80c0c109034251b001404624244bd00c150044d440c00507194005803001a4412007030140c02c00c0f0400c29980d154232984076008038410800c090140040e441c0c5c0c1ca078003030f41c00c00f014810403140c0c445003040020140400850560044c500c1103002a0142e200f000114020308075508215803500850701c844800a07120a0000c41c40e40d44c00d000344603003118401d081500e1a0385144200903401c400b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 161743147 1250 161741897 161741941
    0x6010c0f050604030306050907181a120a0603060b0a060e040509160608041101020f120a03020f030a0902030c0a120609110904210c120503060d060221010b0f03 70
    0x50403802020030400c0091511641c8240c40003d43c1600b04002c0108041c00109141c04000306a400c980340c001d4149201411100f4007031105001110360400500d8a010302404000c01d0401c03c800c01c020140140c00c01001c070b03402250200401c8100806000c84c0300914022030703000c90908450410141401d80c4443d0b803055951043d030300c40302840245021401c550368000070000f02260141300500078050141d106654003400103203a25104003100940300c11480c5980180c1120108009203a80e00070740452b2001c41b91305410640e0b83c6400e070904401071601d20020382c061301c2220815102400c02220880688a024200c4400c8103415516100a07010307501c001c0f43c0042e682003c104140d1524205030b03019910075106615215017090300469480b480800d0801007001968008022605150b2401c8080103645040d030341e00d40d07440021800c41d03032803c040104254400200d110b2801283c1030800c500603161003850040d03036a503038028821350240500c4004004820030210300250030b06201c01e001070314 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 161744397 1250 161743147 161743163
    0x4110d0213020d09030908010b030a0311010213060f0f0e0a05040b1f0306030b070905010e060c011503030f020d020309030d0f0c0803130b062709030714030a0305160806010c 76
    0xd071042003002d030b800402000505640781c00901d020141c10596240c094000c03c2d000b0001c518040c000640e5805003040003034207200002d41030003c1000290126181c146483e0310f20101e10703550b43c034010b210710300c01c0c5000c0c2c0029802281409000e03120303400c90b8214030300041c0000817160410003004010070b101860b440d8410202032840c002c51142c0134081142c00e41c1d0303803000141503145042582c842c4600901d080f081025514041c41940c0c0c020940507a80b000540312a520785c0d42c884203d03401040c84100104080d100440000205580301007460041c0e826907007940d100d07448240c0c041e6034a000703540c100313a4903811804400010621800140c030307840400707150403911500c0a446108641d88143c4040c12f20301c46040e0590f041c4200d040b0100d8000c1e070260f6150192003603182984140c80581c02c1c04417000c001c10004150582e004009a0301d0940d00244018480840c807100151b8903400f500b01000403078249000104010140b40843c1101c036690346440010366180c01c0111040c3d50342001c01c555a035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 161745647 1250 161744397 161744419
    0x60106120f1107050115060206130c0905040b0a061d06100306050904050307050114070806040504020622030c06110a03050d060f0909031d1809010b030105040b10080604110d02 77
    0x94410301400400180d081d441e203076180b585007000c5003903680c442c044a1b0a840e14a03410010294005180c561000401028000c0c001891900580030400f40e8004c949041c00d14080c0030074401a82c0e221809450311440402c10705070750340c040b0000b031048140b07801c10400c01100041c00c941000e2040b4402c0c400c25140014006888800140c0300d070a00740c0e81594164004210001007000901c10110b40c20807001048005141002005101d0301000701441d005540354000304c1c046407114015036100c4050300948038410955011a644107076a203110680303505090360340000340705020700305241c0a4540600500303444161918140e0b4103520a80040310080c0c1c3e01e020000c2c48181ca041c03510080c2141410210f0410104d080c0245600100418115010090514030096603151005542120400c2944400741e5907074412250042407040559500755082c0820801000080c0c428180b060100b20402042981c0f40c0c030b4426a41e0f40c1c2140c00512010000c0ba107071015140c00c0311040001d91004100100036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 161746897 1250 161745647 161745671
    0x4090b0a030609030c050d18050f0f0a06110c0f060a05031e10080c040614010e0307030b0c120f040f061806090516060e0a090b0120100c0305070206010612 68
    0x1c83e2010310580c001102d024002040000c14009100310710007a24105500b214615410407071544148039049c4550041e0810120710b8a5250425200040040c5120050307642d41d60094080c02c81207083c003070749000e8007150380c00900d0407100849038528040c04140c00c04c009c1f0002510594805071408100e80c15400140c411a0700341ca900c0791142e64070784203034540a46030003141703032904080030f0ba07141c8a10704210080c440d07200e0445030302c86003440900c4d000010f04600303004241400c4d029007002d04003088032020441700002900041c110400c602c1203601c50703591240c103030038262401178500a00c21181c2d2038400011503019040418448034000d0100c1540240b0b607035280032544202d1049402d60003c3c20700200c01e4160810100040c011070a040003150800c80015895200741e004108101d60b807405211002e0b44945500d1742d03c080100e0b0b1006030030301c42c1c0004641d030719a01d4408014a508003101030445a1090284901500080d0010b143d1a42400c20a13a18280c40c0c0760912452540c46024070a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 161748147 1250 161746897 161746901
    0x120c05031c0f0b01261503010204031109010605161511070605041101020309060304060c020f0712050c0d081615090614070207150c0812041b0806060604090b0a0306 72
    0x4103100c000c000007510042d20781d200040d10603c440d014144034400a46400b201c8607200c068018442c0c40c1c40752002980d40250045024241940d0b9076010341c80070401000f0400c03481c2e01d544d5a03600c09ca588200c0c0d03a80e0384e03908544900c60309516030303c4800103045840c001588840d00d08000394002c0320100b8020008400d00c00c0540060b002650300580b640180014007000954821142400384080d5140600a001043c02403202070401000240e0754043d40c0340c41482446203840c10311904043d580d580751b4500c00d5260025500e0815226401441342500440c9400c80e107498006a00c40d10303003828102c010038035800c0c400941e00d003520200341903442c008100d1002e00c0350850b0300d4410100014411402946502660750090a0000303650042c5000d00501201030081c1319032034240d00e428a11343d40c441c90b2172038040c05140407000f600d800c4601800108003900c1c0050b22528a410342c2d00b0122a6240e00083d5076410548500d50048002c1106008904454109520a41c00a440e01440c00da0340c0d620001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 161749397 1250 161748147 161748187
    0x1b0309060d050a0e0c060a0e0f0d050615040b0109030b060f04020d02041a090a051005070204050f160215191d010b18070e0f010c0b0c04060e010309120c0503 69
    0xd0603a40c0d501000f0310240a40701d1048010b400310020040741d6801004180f0714402c0a061100380302c80c28070414060768038001200840300018104140c4010300b8035043c0d9850b401603605042a85501d004c1c01c000d41418854070105440507500c02041c01c2c43c0d0340b22140312180140c40340340c000c4500138000300c464440340000c00111507039001c01070b03031985043c040303c904206480290b800d159040000941550b00c50b03034414265002141c0d00c214640c0f0301340e0140c0f803d10950350000c1d046414881040781503032088030581e2041207607030765070301959003021400c81c1c80b030b000c003034031202e4492540000c03c140050807591000000300d40e090009075044428910198a103400300d902495a4540c0303004901401c20210b130b499030308000821070f400c901340641e025103c110400c40150040c4055081720950f41c1c890310303462068607005034006400c0d08005c4006189507105000e4074000c0740d11144a0507065121b40f095080d40381d04180484070840c2081c4003103403201100c0e14140c0d814802070145400e00100b0b01c02c0d0b030b2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 161750647 1250 161749397 161749417
    0x6060c0328021612060203090f0f030702010324090b030f0a0b150108010b0301090b18130b070c030203030a0507030905030a02031305040506010e010309030203130b040306051005061b030906 83
    0x70448000d040003d00c0c04008030309108822050007401c020a4100401c04d0240300d92007000540c0f242e44d1074082e0740c5442c2039540e13840315603c5071040e07044855038040003e0509500030307a402d0101c0c50f0700703c00d2104030042c6200700194921846400b0001003880341d200051b42c00c4000c05641c40f0005030b4040e00e19100b0012001d0f02c0000e03424040c0034804620b5001400554030038280421113604d040850f0500740014407400300d0603501d913882d0100310f6881c0c00c04801240105c100314510b81c20b0203512070b03401c6101060100da2103004000800d1456004010709a5080c2c1d25a0046207107644032100342000e000b0180489040c1500c0f02414000102c040c4050981c41000c1d030b004644800e6070020410f00801694441401249414188002640c0c04910304000c1d44080c02c0124100105e071904925510420030030521f8403403450808581c55400c80020000c5900400084c001c58031444620b41d045440e81c862194040400c01ca00c0803504c0700d4503102207603105e200081c0c0c5d0034103c420b00401c1166101480780 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 161751897 1250 161750647 161750707
    0x90409051f021804050105060a1209080d0c020f0309030304061b051e010501050f10081005090a060302030c040218120a06050f04060f0b0f060904060b07060c0f020f0606060c03 77
    0x3101c521112404818484003204d041c00b07154504000b041040c461002c5c80e2042100126500360b01c8005600f140b142e103540800c00a56804811040100509a08918100600a280082c8110000041030710074910300107025500e440d10700314003500c20b006040d4541f5101001c035611b44010980c14840d900401900b801c00c4104000710b0143d1500b1203605030001442003104031060116034071103151480340039100b410980d00640700c40000304041c04450b407000d60311900c154100304034040c0c95041242128820790407a6102040302081105034059280c24225882d6040101c600618040041d00c104402400680e54034220513182c1c041035400c2144c40d60309080c400400d10040109610410014081d02c4030100000799102001522060568050a10070708005c02c08000e1b5036a15441712000301f207921040340e50b400b6203140c03ca024100d4540724101083c0c0c001a00d1049600100d1850301414071407016200541d104010801142c0040010301481d110900041200e180c100250b4840d2051220f11 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 161753147 1250 161751897 161751907
    0x3020c0a0e040c03080f1b0c0301060909080906090114071127060f0a23040e0304060806060a0c1a040c0b04060804020d0503160c090506040207020105090409051f02 72
    0x14044400345640c411040705694004100108800a0f0048140ca9002d8101950761410508210b07841c0135006514404c00c40e2a044600001000a80500c0c0c0d508298002d101860740c52400c041101c02032200509210350420038a6068600034008007944030701414080c450702c59400f80c00d9882d07040918126011100c1c1c00304204186410b44028400315100001c20441c90b00d0030410805018015042c140500d03840d104140300740d80d4003a031a0700501580f9a214203400000300319909000b04942016015915110070003400c904088220390540f5215124451591284024403885502c0721035014100540101e15000181d00c2d030f404c4518000c2c65003a01109070809003003c0907111600d07802a00c1c6550704000421038070390000021580315804451541d11000a410300364113520541100b0400d5000b6440d02804101c3d8506541d005d5a052400c104601c2d5101414001240304866021b40812003d200040ca1032810703130800e981c6644240b0503114450080c00e06200b4510303085c40704c035450640102e1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 161754397 1250 161753147 161753149
    0x91a040b1201030201142502011112030f06060a0c0305090a03080a051c0507020a1403040f060f02010b090106080109091b0b2203170a051303080c060f0f150a090903020c 74
    0x1403400082183d01d000d182150000c020604540c80b8a030103d840b0401d07c800c1e5055a0040b44e828503042600010303100f044009298202d81540704413401c284005201c40032880da0309104c01620f01e00381041d154041c60040c251401c6d21a508010000c0358402881034002c40041c8800300503107075951803a02c40580b5100d22049614009510a0720314040e00c0c80c0404000800d41c0c001490030345107400c01005008900c0108656040d84210340180004035020071000a00c6e60f40701d04105140e254650007081100b40080c100244a8028810840055280300c014071500c4955800840d40364801c81c03a91803804400070721207050342840d500001d5090404100c050a8145a1481041a81001c0c1e81c0b142050f0135583c480c0780e008040609405090710100c0c02c1e441160040040702d00310a86029164030390b55076031134446595800403500e944117000714408610800c0319070203150700401120040030300d19511707403601003501c0001b85100381d44903109110000d1403503018842c000c00c10740694051724500a40c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 161755647 1250 161754397 161754407
    0x1502090d0b070815060d0c030f0203090607080a14071101020720130608061305070e040f021005030702070b0a0207031b15020a031e03060e070906020d0f091a040b1201030201 76
    0x100901050800410000c41e16030320b00c000c441910034451000031f801c1001150480003424003a8006440c80d04c00028490440f1000611901c030308442d5030341c40c0e10350340d91480303050a0b109508030501c01386c0c0d00036020429241c05804074a07403511140380018101f8042c0d468002e9103400d40c00d00a0060103414071419120f0800079001031030100c21403000d0015514001d20b80b03a82e410018003510700a83c8041403041080000c0c08400d00910481164100c03a00300b90034803c00b1186564000ca204d81d1030b04400c240a580100309681c0701e0075250300a003c02c149019124191544880000011401400301c04000240e60f1074010019a0742c400701d03901daa40c24140d0010300c090034080c0c81000c0d58448100400029440100c4515030401c80490310110030701c002d4203078040c12031a04480c4540c503c400420000b10341c8a05110304a80b41a401c445862800b480191650b11a28100c2000645d403260b060200c011900c1d07041c0c0c1c5486001e0030b00c4d46451356400403001c3d280c10141c919444001408010019982c2c01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 161756897 1250 161755647 161755651
    0x10e012f060901060e060d080403020a030506190e060f060102010204090c02030915120403050d06030f0602070309050907051e09060301060f0915080a09030c05010203090c04140c071502090d0b0708 86
    0xb40d0001c002107410988407240c1c606000780003a12421a00800c80100000c0809440c0215806040740e04819100c1ca0500d031034450850f104562130f1044038001c0c031600c0140c051b000c0304100c0708001e481070703880b158031038001c031007004000905640d000c00c400200c003a180d10031001607204950103146c0301c0104408110f00b0840c100c820215010081c001c0811720411044640e400942c541040d50361907003410085d4000d030030503610140005040300c10b0403080c003030550001e040c028030130343d60095296268410007801c0542030300c50303000040081c8000c071810031040710840501100f8a15043c00c1c242c4000000d112603200b45c00410014035900903805809820060f803402238014074041000070720303440000401d0740d17400a100040e00c603103035950001494020304042100c690000029992490b0902046a841c40440c24181c06985804070b08180742241d9040640140311030f00102e40340512644583e40401c80200c02841465401c11550302e0340d54440c2051403103940b240541ca000c5103040c00015050000c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 161758147 1250 161756897 161756911
    0x13020f040504030e130612030f030e0706020c060a031803090513020412060c050c01090809030709051b0901020f101d01020309120f040f0f0906060f05030402010e012f06 74
    0x9240500c00020f400400c2913080340000e41d085180300b882e20340d1413005400a9840401b883d5135124041d0285503101081448001d000e450034043d245024000c96900c0380280301e00401a000390b01060543d107031410040c0785141840c5000300301800023100d400d100d03003586102140494180c5000300042d040c402d1100703c3d941009070b0110f083c1451310907044400c07005402c00415081d620301441d19005c0c052005e50b6103030514007008020045151900100540c42070301014803030711a40f500002e0654007030241d28406c1482c48840c41d424400498010899000b02000c00e06502440c18a6222580704100d040e00550303514102182c000b100c0200c02c0f151598110720361071030764010000c005804c10001501d03a05c1a411203403041d0f0764489110590054019600604034174003241a00154025503090381c003051f905046800c10050b0fa55020540b601c0b0b00307512005000c21414400500550b004010700201004103041c040c0e0060b10000320140703c801400d1714180fa0150401c08040c1090041000e0340d40101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 161759397 1250 161758147 161758151
    0x10b031e0411060901032d060b040303090b070503040302031207200325090903020708010b0108100b03060102010612031101050c0a210e0304170c0612010312140313020f04 75
    0x30140c8800001c4004511060f0090500080d8010305900c43d60100c80343c54044640401c5624481000b401500017148002c405541007080104940d02a8803c4404681c0d1580340d4450702407811319030399560b410005003038803a0f00041c000013015072010702c006c04102c5454450b00b40d07101d046240c0042c0d42e85640510001101081c1c00c41078003910b001440d010040c592560010742440c00110042081f000c6030003940140b800d100340a0101900001d0f400142d61120000f4050b03201484d0046904030070031694002540c005120411581800700029034005a0610022403615201d60140e5007010158030114002098500300c05aa201c00b0720501c1c1d0045002e103461440e100d00408001d0410203650302c5150280c10f0703500096103600c02984140540700c412410390351104d03a60f01c0c0040008100d82c0e82c01401780610018000319180c20b204480081c40160071104442c2d0940d1072b1000c0701c410031080402803101c1481038100d48100180903511601c261030710422503007c00d1050007001d880c00148540114 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 161760647 1250 161759397 161759401
    0x80d0213090f02070b0105120f0d020d171015030f11030f1308090118080a05010e0633010309022e020109050a06050709030b04110a120c0504020a0e030105010b031e 72
    0xb685d40c078602411610115034144031908000602c50408001c02d030b46400900c1800a00100c09070049080c10309030700c6540701c18802304c0e107060700707558955801c40e80d036400301002d0300040c041e81d0302c50341c83c18401000b90f181c00680c2c04492000c5000701c9000b0414690484404410420080d900c03104103035002c14009001158502e065491807690b01a0070080c6050185d80040d10383d07442c1500c2c12810040c14a1000c0725174190039810328038000c0c10311890b20b0700240a49000554107a5110807074403c650072000c0a10a542071105c1691035004428000342d04042e200c85050025941da40084450320a00c284408802c402d051402c28001480f03000b41015a41440700300701c08180c02080201c511900020301143d282d407006000c135080509604001e107400c03000d42c10b0209100081c125092110819500340b058191207250701074035017038009d200070484188500b00380101d04154000e08803581c07181c00d1506220b592800001d007920026000f8000701d44003c01040030b1030040c944489405102420038920074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 161761897 1250 161760647 161760653
    0x606050f010905060f0702040204170c1002101a060316020105130b010311060c030d0906061d0a1a03011a0f0105070b0112081207020a03140a0912080d0213090f0207 72
    0x14000502c2543c4c07040001042d4480924090400c44000b140d004104540e90781d01d07049078920305c0c030102c0000c0c0320912400546141a0504040d1101907040b02c0d002000655030049400001e0001d81c0e00b039085c0091260f10a400c280c42c1c0d40041e5004144003d41110310070044107000307013100c0004000030303507542a0000280128003010051819a0f4108001000c0702c000c0402203995842031881c003d5040c4000034502017801c887ea4000d482007031188005128450b643c07024910141e0171082e5135044444038901007100c0011950004000c11440c141100c090600c40c0002421580015080b000380321603807500718070301c1c5052091288030040909002c2c1c00c10340c0680300c2040d0390105000f01019424a5903010041c40341c44010f403581d44458001d1b0044c0c1d032400000003515500400310403008512044845140305106502351440241143d968000407403511b40e01d254401c0031400107a4661208200d51100310312680001c1140303003400804445a01c0c03900140b001141c502c400003c01481c0f043c0a51000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 161763147 1250 161761897 161761907
    0x50406051b03041a0304060c020601051f0306030b0a060914071e142116081f03050d030b030706030b03030906071110090612021213080c07060207030606050f01 70
    0x10142990040070000000c0c4001685944115084804248183d090940783d503d0f28a0003103110300d02c201001e0045020a40b01681d90381e40a0180540c002c1385810014011150030694030101b00c010710f001b10b0312555984074526200810f4400700c0d54243c84031b506002d0a40c0324040c4002c060003000010f40d00d440c0085d4010400c010a40c03007050340c03200707402e01d001100d48103481001c00b0504aa0704180e807501c60041459104a03990309190b9020190300c0000d442c100d99090f900c0304104c00381c540c0112030f911050002c0243c001d240303650040141e4000f010001c0f803400c00287c00e100d85141c600140c040c0d1120100f61a01c48580e10540426003041d80c608003548000c000d84400c09800d803101a11220b1314a0b291885220145900390040101510080c109921a0509084030394030707180c1c009201e858044210071703031140142c09840700f0780704804203010030040401704030500e0142c1d50a505200483d00b40b50b081841c507038040310069201100500030b02600d0b100e0705005250486030000d80781094000605 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 161764397 1250 161763147 161763157
    0x3051e1902220609051201090308150310090f02010806101d040b030f01050f1005031203041e0615061d010c050f15041b05150f09040c08041205040605 66
    0x841580c0105400302a2000364146100c01c144052800e03102c07980310080205400340b0362150324810911408900304040f410302c60030443d06e0305a0740b4460b955441c1e40d0040c2d280d4480f0070349203030948030b800d020b400481054131030080214414114807078075241c039000040041c1c8002d0403451052000840040344690019034170408401580b695a0840c0e403000b0001c0c0c020100e030300c2e9054150180381286215003c0c1035008510840321541d0a641a84840c060310203881058024190035070f00c001c100848101003180515803040c8100703ca4000d018030702048050071070003000115982921604445040ea08030103255000e05801e24044510b0b01d80008503100b0b0180c03a5000d20705000f440c418007010f02109101540d0000c070170704200e440d080c040800851012a04030317000e47c0d03003035050340031110f4400e0510700c12403c0701c90051014100700d00c0d041c454049a030001c18070900c403503020000ea503140e4540e4040c1e42d50214098442422074585811b020301c107400c00c0c2c01d80000300003040009100f007907080001d80d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 161765647 1250 161764397 161764441
    0x12010b1e04090b01090914120a080903160f1401090309050f030c061305041a150a030e0a0804060305100e160c0c0806190207030e090402030c1003051e 66
    0x652050300c0080400c008201029018120b0071940001140c281032a07044184034912920701d00360303442c0c0948500703911101103600f01c540c820410042801640c2c070032403c7d29040b4001c0e03400d40e454182101c0b00b81c14400c0310031504403078411492a50704144070302806c15100ca03484400082c40001ea180c0d40040c2011041e0150910410301c004c00500c1944003002440c40841000d018141c0c1c80e41c404103011204401ca101d502d00c01c5041206606003401d60b842c407901002e0024004810340a05070700c00701c6260f00415448020190750707855462181d403081210f0f610b0740e03014508066482c6d05010004050380d0b0020140a84403981d188208440110010020fa100c8910600c004003480f6001e4111124540401c002d8040043d45034045034110000c11582e0080c07940440c0e041c4956607990714401a40030b0071402501041842030980d000b030030070300142640b06200800b542d020b0740c03910001502c50b500b1816240c00003640c56040010304410340786915086441b0b06400c07901840d08950f40101d006a014401e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 161766897 1250 161765647 161765689
    0xd0905060d090209040303050912130b0c12040f03120c0b060105030a020f03040b01170d020304181409010f0b120c13140f092e150503030403080912010b 67
    0x480109016030110b80c0b41c40c2c0c000c1c0603d0306810603003001400b415056400c03d00c2400344240c900c514400309011610104c0340040400e4000d49404503451440d0000c405000c0c0c2d038051f6044a00c1310655000090001d45112804004064114217140790040e0000419005001080d0746032408588a022240d610000902e0050f43d00c1c2c0c1c551510358040d002c0c4d400000d8880320080144800c2104170aa22810384200200080030820481c001c9991900500310040150f04200130500820500411902e00751080002c08134045c4d80040d2400054101110070014907550b030010b25040d0901401521006101212440e44001c80700440701d032070305039140c186807103500c001b03014100390071441d0000d443c41e00d080e9032280001c1c0350030044440407200032500c1d11203038000d503803124031001500f5a05e1281c0001120381904403042160400c802445540220303e581c640d0f5280004181e50b00308020000345100e800c900fa110014141448180b81d404250341510381d04003250000e090725112540319040d41c145401c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 161768147 1250 161766897 161766907
    0x103020c0c041e1119050306010c20060a02060711070501170a060803040f030510180b060307031202010209041406102303041415040305090105070302070b0408010912020d090506 78
    0x81040005200b480d09880941070201c15005100e1190140c034600c0601700e080c00384045c81c00ca08a07034500c0300316145804200b5240c90000810020503500b003680038012048001e04009800040380c03070700a14020710040c0c5c040d004001c1c00d00e602c2003030364444000c180c0042944600300000607062440e2505003030b0b414114440007443c230001c290030510051423030801380da0340c1c2c0d502c8448000c20102c0328007058134144505103401d24a54031354070075850345c69401c903840107000d405c542c1d45048104001e400d280d4107100302c078804804605810301c052240741c1a90001607840140d40c052105450081c811510044070040c204840f6880320310b040c4980c80001d241c00c030344078a211102c099170140c0201079020880004010002001802e00c0085034080c03590044480a020041c15400302100031100240094024411180036502030f0028011040c0302c0d00540304c2e0f03151038640b195150380150b804844241e450b085503005210310a000121200d034203202070705d016000d00c07001401000862085e10b000320700c00a2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 161769397 1250 161768147 161768171
    0xf09040c090302312f03060604060c300207050102010e0304060507030504030602030106083705060a050405090307030305010b040608071409030d0c0b0a0902010e0405071803080304030e0103020c0c04 87
    0x1a02d044c1c20190300f64204001c00070710418020000541612420310795031801c800110055001c00c1d28480d41000303200d103182500b840000c4440d440040380445204c4c9298405072444000340105141032801c2e00012003d83c040f0200c028a000c00503031049065925007020003a03041004402c0303074203642103810015920b200924044a1707500c103540c00542020710120021a0070b95020008038001c3d101d140c11600e5044801d21800c0c200c0300c040c8802e90030800400e8401c0490802c40d0041544540000c244400469680c0003080985a085441c549281c100003a600c003055018800c25000d85020450b603800c0c04d09003031001c0d0100d0009841a400e2181c4800100c1051854a0844820042c0034064407011582224060301c807079204181103681802c00d00010b0001e0754a03100e090b201940513541c191405c502181070000804003e0209030401034882540d1b00e01e001c1c1180c0240041d40b04003546540c034038180c203000b40203502140800d0304060040009980903080020f050000303844c115000104004519 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 161770647 1250 161769397 161769469
    0x12020a030209160807050901080a09032a12080105090106052d0a09060813020d020a03050105090d03050f1009021b010c050d05010504062103020106030204020f09040c090302 76
    0x29000039030048402e4200545100107081c5000140e000380c4401c10b40740c403190750a03503d6020312882980041e0f444070000300c403441e140d084214018040e013080b07000c2c401580440e00552610f0000008080e01803042401000101070034800c1104641c40c02d0100755040c40001401640c06104050402001184c03000e1b00c040c2e0b407000c2c0c8416203020b800c034103258040c5500f0020036401140c034560202e4100100042e41d1405280c6217031040c420440c03041001d080d1507080160703a2400007000c1c2d802089a14000c00051030900c1054000c4101d28010400d01c008010000c0640340014400320641900c4028400d0104031100224152048214050380b00e94201c20007500a5201c240e501519600b0900548a641d030058014091202c480c0002c0c44107030b803904117110641e00c5511030109070034a85c290445104440010300036105100e4800810115501e800040580c0c11100c08908050400140d80100e4030389480789455035082d5041181304e851070754000403503580040410354521800e078054551520340784 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 161771897 1250 161770647 161770649
    0xd0201121e0501050111070e1602030403020d0803060909070f0306050c09100f020f0f030316050715050609010504140f07020705090c07060b0d201804050f1c0203030112020a 76
    0x10390800e190001841158409004213200d69404203405848a511150000c140003040d40c00781402900245c88181e00400c9000020f0581c6045010034480800142d4818020b0029903008125090b140d085c000104201a900609008000c0d0322580040201208040e550400c0340c1e000080010103a0f41d04224103010304c41c0ea04529805036030f0881d0442141d420201584031454540c1c00c40361803510404000380d50700c1c0b950726282c603194400c1c000107000d444281c0c0010364238050380c5032a901b058030f1591040c80d03422400d0348a40e0801e803500c00308072940c10440e1a050041078202da05101f15100580b03420021240a8500a0b80044000014080c80e00812001000304405050400070f86000654a0740c00d401148085856a0801d40c5107038051078098541250350390481e4954070862005d20300300402180204906030442006120009200403050040744224042c801a004500c400d1a40303d041411480c5100e40200f9285c2ea004000c60340082600d0540720fa104000e0380901c2c090001841001903 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 161773147 1250 161771897 161771921
    0x80721020a0207080c06070506160309050616030c0305070f12180b0402030705040e1005250f020d03060b070b06040e0607180e13081e0f09011205060d020112 69
    0x220300341c107aa80068054100c410341c03000e84800c2c5a8040811002d0f204565015155600c10b9001c103080101464000300c520300c3c20300b030008203041c2030b40d40d5030300381001140c003414022840d243d6400071030303014001c04105255a113000c010314904500090000c16000140600b00524081c3c4044400d80c90b91081441e1030310200c2149040d11a0716040300c21001c2110102d00074000e082d400206414070703000d2440c1001051001d0003c4200d00449403009142c02082880b010001c004014441040740306070010700841030352000000100345001a00d803480c1c03c4000410946401020000c11102c0b905403659650b00c00e040c58a140c40f03035000903003d8030001848030b015008010510040d00c0d04504d002c0303c0d01c1c8070f0416801189595100d01c140049040b2141d585d0141000103001c0010800702c024446844d4110302002e94194126401d103007504a107411340e501394030000d03074070156681000406207060240c00040c4210300e802000301b140c94003a05402030505c0300707814601c0008603ca03004940d482c81 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 161774397 1250 161773147 161773151
    0x150810120201020c06180a0e010f120606120b0f160206130609062a0f020c09221b090605030a06020708120406060302010f030e0a1b050a0803030703050115080721 71
    0x140e4105031b49196005501b01a00c01c0305181d500044440d0159a068101d03404510360000440c43d1090f9541d5401c0080000ca40d1555500008a100007009000741d0304c0500556000750540340134095421401e0000e4003e00d12604030968008245900145456110500488050b0004064607008000d090500c44c01400c0500f801c200306442c009102c1d503814440090201d41b070b945011410181c850601c003054020050b00098140e0741c240c10405a03d5801c0700e94809146e0321003003500000303014084880d000f1250308120781034140740c114000380c044000d8011440100324480c5001c0002c2d545480b80c01c0c0082c44640c0200e040f000b44440070080e00c501c002c100c00075404610700340c0792940081060b408101d0100e1020024121058802d2007850680220382c0000c0a540340300b6100c6a843c243c000d80742c21040220313801c02140a1301d440b248a40242000e030004c42d164101441c025003030301c005030001400390401007080701c2d90315400302d40b449e00300d000c41c01c041c0d10120715200c210b030783c032500c0d6200003030014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 161775647 1250 161774397 161774407
    0x314120c0105070215040b0c090d150c02011d1c021e0a0308070512041b090c0504080c03030c070303032c0c0102060601031b08060325150810120201020c06 68
    0x80d50640000d0b01c03d041a0b403d46803039419400340c105a0400958000d08039111000024846140781001040078100040a0f8042031203181d0310030b14482c01004035142d0440d19002100c00f110b40901914648404006c43d034801c1d905095580399035494020303802480208100c805505048c02403209805034802c1c0001c01c03000b515004051580c44510b90401c41c0007504010000d24072900c03641c25908400300554400030961520b40320b510000c944032484081c0c81503640000101002c0e00e1044407141407140e01c0d52900d581c40d003208203080c910300d406210300a400411142e000700d40080b90201c152603241c00e000940001c1c400040c42400750302030b182d0708d00e03044c03820410901e1100050303011015a026421030344540d036800c004405484202104001c1e040120000e041c2040c0a008a56400f11028007200e01540d100c40030005504008112001c240c008104107005605000410321000346032820480780500b801900369142405a2141c0c0b1081103041e5400c0d030441e80b00303104130440c1c480020300c0950ae138 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 161776897 1250 161775647 161775667
    0x6181c0b100f1d0a09110418060506060c060c0a0c0c030609060f061a0c1f051b0a02101d01050703020d0b03011104030b180f010c0311030f01031412 65
    0x214549000d5650200c402c1100007440c1c90881e4842542d9002640d800d4070a91a00c0c10703514041e01e14148100e80891a0158050180d00c80d840751500d0b0041c80c040c41c3e03260b0b8a6030f00745a021282c001c0d066a0168900704421004100c0000360f003600704188200ca19034801100d0b030202c07409447c20b10700030942e002022000040c400c070303500040000d0303003d42401c0140c92695850791003217507a103200f4480000015644c084407403000201500000c1411015503403510340d065500401c51400d40b409181c610756400500009100306004440e40400b61980146480c2d00720102a6507250542030400d200d40d00c40300c1d100c924001020300c100032414400000d0015050610001e806500081c0c21a2180d0780f030102200b58601e81402507a54260316020050319040c11611580002407005281d042c0120ba20031109010410401428844074120f0b00009050704902c94000d0684407450030110b8201c0301801403050444900d000c035030451381d201d8030181111694242142c20041f440f205088a40004203840b542 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 161778147 1250 161776897 161776921
    0xa0812040209070e030a060e01020c030304081e0406050f0714010f0b01031b0c060209040b0a06030203060406060305061305041e03210c081305071a07020f06181c0b 72
    0x40c9200311a04a00c40e6a00745040300c0c4003442410503a41640300644200204626500013900351082e030001501c0c02900d4a8501c0c55a0710039035045554900008065040f44c41d0150104502d40040801918162801c40001c00750300890400c081610000107a2000308410700c2010440460f50000a100400d58400144002c240004400703010908004440060700181004071501c86501d40301d04201030090380780c0e0b03030013074201e40007603604550b480b10324416903a9a007009030000d041c02d07580075070b60b481d18106000c2600d40591040741414107000a0015650301c0c1d008024814110702c0380080c040d503031400c01030b40d800d003d550aa040b8050960202040c0340c2d0203103c08080c20744400c8009034071510610790604a1318418090030006a410001c80c1c3c3c1d0340718503110946064090703c101c0705165100c80792000317038601c0268120740d0b41000089240440c28005480c40056404a81c440d081ca1084804100012002030b030701841040d0b00302c042c0c3d03045440c0b800b0001c00e65800984081d110f01d003141e0701544c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 161779397 1250 161778147 161778151
    0xe07050706140106170603010b09090a05120f0a0e03100204090e1e0705011107050901060e04051315021c1b1b050c10030e06070207150305010e04020904050a0812 71
    0xd001e0b0900e0300b196585084800510704948495540c0386008162038000b40080402800040c2d255480349080c600320b58030002654051001c0e8406000f014441e403034594a0f01e00c1d1032483e10b034041c0c01401700901c2071540500392803070310b1002d0034840c880042c8080020305020407102501011840071a011401283d00d0748181d010301500e00c01c403490065243e20350440b05041d1818680e0542c401d130401d01c0079520884000210589200072503103150744440c000b4841705003d0b007105001440c50142e01d40d1603d404d01445070040569902000e200d1101d8450304a142a001d106904903500080c0b9181480d40fa810aa50040c1081a040005080d007607654840c06807608481d0700010b0b83c07221000350140701c0340129910035920500820a0281d940203002000f0400c8500304281540c84240d010150814001148140c803158080e0042c1c5052101021443ea04944003104062805005100d603c1b607110015070421b40480c0c3c806c005075201d25201d482c001010b01c0080004802160509241100b50f02e0f4074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 161780647 1250 161779397 161779403
    0x1090c18030804120804090c0302031b030f010e1003080705010204060e0118090f0219090509090d050d0f1503030206041109040f0f0516030b1902090a09150e070507 72
    0x40010a1500120306008140c1c0805001020108010001c14080f5614003140c98800e5040c2810950b8500203a0700700e0b603003102e584001c00c5d000410840d0301800310040c014082e405400f101d0950400e4404810421814052400c2c510000790104600040c52582034004561000c60036070740303c181e440c0650107500a0b00c90311f408601840003070b401560141510340ca14071461107444580da0f24160714034000e42021920f80003180d80c00c20222040c1155412010314445540c0c4030032502c2c524050600480c500700400b660882d41250012140b000d83c80801c441140d02010008114860303d12030500050030b08056826000307116200010400d82c0101e1010300c01d900601d0014021000c0d403042c080303510b001307c8004040460300d032410390010712400515030b041d602030f100b2144520440c143c480c85d240d080b80c00a03108050700c407040040c0b84441e0020302103160440c140550605a08401041d0210040c1c010b110829480c0c020040d03500c0f000c20350050050011403600300d11400c00b154080e2090b40141019 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 161781897 1250 161780647 161780657
    0x506030f0706050c0f280c03020d060219110a0609020a0509100f09020702090103030c15020301080a050f032b0e070e060f0102010905070b1602090903030601081005060304020d1a01090c 81
    0x30f20760a09011a41c0700c90041e0180054040c000c03441c100400125120b46d08503031100b10b180c1c000c409601c1e194840c42c3e2280c03045800503503442c1c2903c000550f4034000c490807010081340a01c5124541c00108499900590140e4081803014061002401000b232981120760404070301e9081002c030700c542c86048003c86181003d520f00c110b1b02c81c48080300743d1180382000b9421403c99801080080e10864001c024180601d44002110368414a81400d990080c1e120400b15800700c1b501d0402d000b8180304082030141414011441c080f49040d492a24684441603401522104d0340a11201c120703540005440c4141c0c0c00981d150b094490f144210003aa080e14040d0181c000e1400e5880c0a50051280d003190315004002040d8080c9480c240a18030740c00f443d01c07a020900b4010307075075005840c2c00702120301642d410030140d600d903c0c003603000414016000740700c00030a00501c54200f049885082c22207030002c0c1c040c0ca001c54456042e082503080c5214a4650512802c0c011000040c2044690700c400402d00c0d0b0343d03032a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 161783147 1250 161781897 161781913
    0x909010605031312050d060305030405030d050c0d050f0f04081e0a11060f070510020a0e0307030818010507020d03020c01110c0603010b1e030406050103060b0a180506030f0706050c 79
    0x104403402d0100b12515410001910000e4022596181003801e04408528003103282aa540030000169061540f08480550002ca0140074610f070612060307440c0c94040c500203040c0207e12022a60310701d2800a40300c2480f1000400d814081c1c4010101e6250400303c10030255544e5481c5107d55031003a011170b0140021060103c070042b40540130842522694002419440c4596294200101ca500c40c0b00700c542b1031002084070b01c1c009035040c402402d003410b132040b0060300c0d0300c01c1c04000b401a5614000c010301c81d400001040c000038a06034240d079038180b2480040c01d440402040162058400c0e220007950181440041004056000411518400003a40c0b14039007161040ca240c0d942d404100d03025907100c2018001480038003000b102500c04100350311440300c00c000540340d2003040c640c416182a100380d51070344014000e01203076003d0000140415a00540360383e1500e0f0111a03040c03070305404c1081c80350322030b00404d045580402690b40540242801e590006580309030140503944440200d01a0b405200d0b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 161784397 1250 161783147 161783159
    0xa020a0e060a0b030c0706111c0b0a080a030f12142406031509060607141c0e0603070503040c050a08010b0102010f0e1203040501020c071502012d0209040b0d08090901 73
    0xf071300c1c0504048810710741030885a42d00c000141000210050801e030003030062111813210303801d08a010072800100007521912020030700059118981000b8115070240300a000042da02980141b5600c0092038060300c1428610446400360000300c507844400300e848400d200300c0d154440c280401000c02c1d8100c41d44081c05500901ca124042100c110240b286010201e54060130071440c4075502080c01031007280745c03082640d2440341c1100000c0310310380c1640c030201c04d602112072800c00307081d40a000c9042030900560b12100250461200408401c100300020000c20100910714182e2400307010700405c15111280c959840038020892401010300660a180001641d124a4454100442c450740e000e06100d07120b0300e5001c61554009801218150341c00c206610070040140039840c0540074009585c2e11900030104000d09580b484801d880c0c41c0141241505018403144510344000010050702507180d4032407000103801000110511900324091031825010130450000030000204111120303031181e42c880c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 161785647 1250 161784397 161784419
    0x180b03070b0f0c100e0d08040c0b0a0e18060406090902060403170c0615040c0f020703120c0606170111070b0604050402151201150201110405120a020a0e060a 69
    0x1541168058000400521a001c0c52500400150038206159858051444403040c6000c0054101c100407542d0b03902c86005064050040a03801307401442c010105003401d40721300144184900c98001c0ba00000038602c1d0310540240f40e5002e03040c10007000149804000380d0341e04018201121218403803440d0003170210b0303c649180318111002d80c000d405142040d081d40e80d22084103e00c1400104101c0c0203102c41c4d00b030b5540401155109440d00703482511162203240611081d02d000d00c2e140c50601c00034400d010f6800e0782c00141c40086940001703c1041d0792400c800305503903820080d1005070410307040c07000200d03400c4050326450103840c42c8400200459107003140500060b02850340000c00700300150001c0360180c0f6183d0080b64201c3c0c0004c00383c140124a501d0b030342032650300a8040741407406829004000e4505d0304410342c80702c40e021b03000038440b0820120381c0b4a85440346000d41845a2403d01c403440c06d541d0200040c06007294003500040c0441c2d02e443c1103040d200001c89034584682e443c0311010640040503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 161786897 1250 161785647 161785661
    0x15050103020c0a0206090d020310090302060604090f170f1614030306030a0b040203030f07050a110f0a0902310e0c0a0e0607140d05180909150c1c020418 67
    0x400034003480e041c2a400c0100d06e6100c80749095114020705040c80150340e007030068104200f20b5110000e1421f00c030f0310300a0304064004040511440c03500300300c03001081c400064881c00d00e5010700c86014001442000301003034015000c0101d41d494011410031584452008403031145409003501240710700c40c0101d500d5403844100c2c1c0309d9401d0b801c0a225240011819031f601a0082e200405503403d018411826a040707030014901991154030694140307040c040c01d00502c42011005803216502d40c5d510001142c48036045e4495400c18035400105044400451981202015110540c41a100001c2007034181202828020300419031966004107a80160003821942c1074406030700d03814507482242003045600d0f00907400c2500c038000488003207003002005001031b00252505031501d80d100d5154030810000c18514050341ca001d130f0f1104003808898440042d043d5101d02d017812980b00d00d59035100c44a4000e010f10152245011210035490000a450350080c1069a4100c42907c01d21855001e41c032043c1ca00c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 161788147 1250 161786897 161786917
    0x2071404061d090a0203030a0f08130b060111030904050c031603020901020d1b150f0e01050402031b011e020601030317060d1b0509010b0a030506061306180b0d1505010302 75
    0x5210100300e0050b040b08840c1d000101c24180c91410b030f0039401080c296403161503001c4c000303070800306101c16103a080074880b030b0009141003150080b580300703503070b480380c0900d01401050501c508001a105102e004004541031401c010b4400d1007281444880503420f0703007080c0c440038404181d00414010662003071090340c08840c0b0503801400d0211044800ba640e90900c55400c032900c4c1e49510b9203001203a1081e00e000b442c4c2030000c40003d41d44c10703444c1401c400c4500d2007000d50701036418082030001513031f00050606880c040e0a46c801c24010b400070016a000c191b401c102402c1e80034039119075481d20780c021038418102d0b8041d442c0d07000c0315140c0b04201da0511600311045603000c1103084204000c12500b0b80414590030a800c451841ea588607000502c4c5040241e00040103020001001c4a006d6414010f01d90070440c03d0394001d0030030902d05080007800e4014042e02040042d40144226040e000b011001d00529a60b401c0703607616a601d0541c02c003d01002d03070307100f41c040a80c0c09000420b544244211410012 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 161789397 1250 161788147 161788169
    0x60c0703081f170d03062102040b0a171615080403030906020c100209100804020108040611070204091101030c0f0207060e0a080f0d020c0108010e160309050303070207140406 76
    0x1c0d40c80c00c008080d281494180b00d04420a00c8042044041d40360070000c00a4a40c0080c0520384102000400355801078120392a040031202410309030b1f07444d0b5100c410903603034103c0b40440c490b25002c0124440a6560744215842c0c801c0080c105c0c192003000c9010580c130f00c0411824106552201000300410350f1707072052440010841030011b00424400da1001d400385100320800351404440103041441d1440070b00001103825030000d200c10303030744ca02005540341c2c03840300e420810076500e495000039190714401231010b0403040d21110b074005030700e00441c00c4450b00c65009008011120043c00c0071002c41c013540c10654046864000e1031280d40f401541c007600840861781c010941241000b0040303450540700c04c41d458009003803a4012034034400030700c0b4060380c45203441c00520b500141544000d00d40000310400c2d07814000d400d4014001c009980b00903075445000c61960740c1040c0546c90048000300805a0060540e000100c10f0080c041c2c1d000c240c0300c0444880710100981c05c21404100011201310780f1a0f140180 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 161790647 1250 161789397 161789401
    0x60b0a0e07030506010903020306010f0905010e0906060d03030b03070609180b0f040b0103140a0c0906050720031e030c10151214070902091507030804030305060d050109080903060c070308 82
    0x50302c81d40200d07900c0041031400070011541ca83c00302c1d180c40400e030080040d004000030107102e43c0d0301601c5482c3c0100300300b8444002c1401d1492000d900d03144054912800740005400002c20301d0b000b90816646501c000d0122170180341c1c0c0300030003461204035004103800400005d42d03400c1411480e001d0005c0701c032001002c0480603092001084014136803201050305041c0c540c4440c3d1100344465a5042c8100e4100c0b01c082180081c600d0001d204242680000c2e0a0080034080c86000c1054240c2421200150445140041e032a480000e86000c440a19040c50b607450342c000d00e1a80b10b000b1001c0e0001086d4070085445080c100518001517403001d401401c4006d403400020408441d090903203a501d2070240d85122220502c110f001401d0122680091040d145c0000301840360707090419101030700c441801e40d003034101070099400810020005d4405010151104081501540c0d002d400340541e585c0328008001d076484600e840d45194000c0c0f091940710340180030010b50b00c0c00701442107031100d9a0507900c0713042c19 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 161791897 1250 161790647 161790661
    0xf03050601122729010605030c130816090c0201061404050a0605130504021e0108040303110d0606120b010519080a0f0c1e030221091216060b0a0e 64
    0xe000100c180c450303945071001d408007406065607903c40041e000300c05040c04107405001000c00c90007503800240d600742d540b00c0108081e550020540f90081c464001180d42c0d603281080e8110407440380d0b0403803c098014041c40110320780004080c03108588803004148582d022910081c0c2c01c071f038202d10400d86141d1407010400c000d49000e44c04a0340c020103001f000149180ca4001051488180444131030b6615034500c10b00040d41741070348120f145580c00c941001d50b40050400020301e001c80c007801c024181340c0c4560940110a944109503144c218003128104806503580c2d000811441c0c2c61703017407024400d1814000c0350b01c5500c5101280d920f006a801d40d48071406a070001161088030040c40e010050350350701260302100e000d50142035030200031075036480100c0d17907030500000000400d01801420316104002103415500343c011200d500328104204200140e0701d8940c860706040403480e900e0286407000550030340c50300c405140403100d54002c40041202c00d9050b0288964900325011b00207081070300900107646 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 161793147 1250 161791897 161791901
    0x3070903170d1e05090c010e012d02010c0801120c0b1c06030b0115020f1902010903050708060906010603060f05041a030105040821040c0302210304090902010f0305060112 75
    0x2903912000c0d80da031070030a44402e15000c560011001c001c02200c0702620044000c51801401c0d00841c078900a410840c811400207480d100c020340b110750620026023240e02542c02000c0140d10f8800100b415103c2035218a08000d00030700042424101081a000c008604150501c1003444056400020302c0020350170301c0c0140030990046401d01c4440140b81d4401166a1060b00840d4000e41c410410b19105505044c40e0b8001d480140304410110741c4501103032208a00c00040700703490b00d41c2403552500880d0050004894094064001034514410410001100800094014411800b580582da541d0340ca51a048095510511034505542780800d03082c0001d280641c8001c07003041400c0e9540400c03040c4da501107400c0d50f404031380039224410301041c188000d040010381c81003407101c1c3c5503444407540760a554160342c519a60201038003420903410140500c1c4110f10502d00c0d0019072004503602c035543d512100f8041e01c01e4000c02c90001d0941c0b070700c424500d170003402407901443e0161203040070850403d40e2500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 161794397 1250 161793147 161793173
    0x30403030305190e01091103030307080f060111031c11070f1b0306090f0c0906030f0f17040306050916081506030c100302130506040f03030804110a0e04150203070903 73
    0x25040c90300c0403600402a91920075100c00e88000c10020900300b04038141f90246031042d800e030030b000760401c200b00310000303a01140301588440c56070002e6845450b0310740122980896891190410311002803044c0800c8090a0485029a901c0744180140902070a81806074012500002c050400104407100081c3c0304860450540e01311041000c02d00d070340e030b0301c4120544051020507220265440082ca003840907082023031025040b0040248042840c584da80400c00007455000341080d840743c0c1c920300801c00042e001601d09465180340030788454403418050f00a01c011750743e20045120305d0164070048204141007004881031080507003141c6404404032640c040e0700030043d0340d140c002c03240c0c610120341c0d0718014042484200d540040c0c42e40c1d000200710402c0c04040d005144206800e1200700070102c810741900301600c0d070615140324180c03141d1400c1d80c05030030740840300303a07100840042c0410b00c1c900c04426544202c1c003410b8810700c50410010148100d100a4400200044841e0390610210320303401c240729 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 161795647 1250 161794397 161794411
    0x102120c0a0309021017070201060b16060609020408030d0b030c0f100e0a0816120f020616020301050a02190806100e0d0605180f01111b0a050607020d110708030403030305 75
    0x12400f0700c59640001d807401c1d134800421000c01c2a03120f800c2c00004601510542c030880c10f0000f085a00e0030300d0854040c5000e039203002845803007040112000c00078503810601c01006940420754031607403a5203c45480f600112400e03907900c1d1900704c184845240014242c442010050176082d0114030800034840b14a90351030507042800440302685036251208590305004040f8580039142c1c040b0940a01100c0340103a43c0042000e8941e400503801103a00300c1c0140c202c403035044944039590210b503803507981581100c6601039415460001000074030b8402c0d40007421210420043c10240c5103165034162400754003540c106070401d0134040300d4a001c50140011030040300c1e00411142e80b42880366035141c240c4070b00329104a01e4140308440c1d83c0c0320308803c11405242054010091245040c00e2803181514001d0034401000d100f80386031544454902800080a0030f50004292070311881d005402035a500c012a0080380000c4a02c050100710500c0843d018041c0d600440c0510320b054510f8404602078400a4504 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 161796897 1250 161795647 161795651
    0xa020306040e1005010f0b07211b0503120a021206040203090a1e0309050105040b0910030e03160b0108160504090816050f010606030203010506190210020a080a0c020102120c0a03 78
    0x5030500d0700c0c10003c0324900400002c01064940c1403080b00701d40c0b400c1c9940007541c0305501744503450005608281885000d0404050580c0340c658000003182c5071300540a0f000c2d03402500c00003000c18094040014480103003050061206520340d0300c034000891080c032400740260b81509020074250b1a00c0d03001141c104a1202c00c4a00700007250b2104480a6420000d0749400f4074000001401c05800254810042209080140c2020b240c002e1025036841901070080c4209615070703030720002c0350082c2d0010312910402d10403680c444810000140d0040702c804400d460f03000060000145c903800011790480320100480d50f03c81100d10b07080c103000c007502420f0341c05c6078600380034826084110884503032440400c0c01000100001000400d1031801c40d00c01707030455002c01d4010801840b40d81c0340c0c00226503050084241001281d1402c0e601203052100d00c10007001c2403400002c01c103c400d0303845600035000d5400104208011104075030700345d080707208940d000c0600c1502200000e40d8484a1009482c5c15010b80c100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 161798147 1250 161796897 161796911
    0x10b12060a09140402131401090e030f07030e090a020c070e1005190603140708060607170a0509150a09060c0c0806180c030706090909051204080f120306090a02030604 73
    0x2d08001e455088880d6051403a09a00308000c0d813920600180f2010100c1e04c0030426080d4601c94500c003030005002e03090344542c40300170492003440c1c100202ca0703e800d0012201511412246001803a01405006151054514101048801d000e520803201881d00c2c01e001400381500d40162100c8418008002011405c1e0846000400f512148040358001d01141042c04d5842d00309203000e400c6441106175070301e40382c046c0004c200f0702c2c5402881142e00001c08858175030f11840907240c80e818411040b0b00844601300c02080d07401100d9006405400b1221045410b8488000032000c0814640180501c45000403001042005040d003e0420418918040d01032607507415110b081c95840c1c0107050301c3d04644014051502c0d80b528100b84914400e28900314013814006151250040ca014000c0c000c4c40c0226507125541010400308001c101d404040c1180f41c3c5031515698103c15485551141d0402410302485484002144014080b20322503032009084003010f8590080040094000415083d0855036802c9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 161799397 1250 161798147 161798159
    0x1707110a120203030105031009050606010e03010912081501020102070506011e030b0103150b03032802030c07030c06020d080c0f09130f06140f03030904021810020105041a010b12060a 80
    0x3000040c0790940d80045030b595251005140c40c01400c21043d0044074603004080d40010000304451303802c02c100340f0349003a6034604200024010107450f8002003d030f4416401c100d24840c3c00000c281d21806501500c451201e14a80041e400d030301c00c01d00d00400b00d81103480180042c075a0b00c01a141c0101121420b60391f05900da90342ca404402c401c0e04103a805011032401d0382d00702665802021070b40c0c0410b6003d14103040403c002160503071010b5162440f010b6240b8000582584200180c40c0c214014104a030740f115a242002c400d441100e011b8100103011f00b10240309647d005503c401d01902d04103810754a01101e202800966400500711268030103107107206500017001500860840003105000042c115140c42520209509a00c0d01580501e200d91400e2040703075070120541e1900c00043e01c025a4a400c414000b010340c40c1c401100f66806070008013104181581503015501c521b120b580d10381d03500c0490282c13401c0c00c14804d1180c0e0b40d120340700300510380311091903003500c83e000f54001e0310494409480b59 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 161800647 1250 161799397 161799413
    0xf0a030c02040518120c010f020a08070e13090f1109040b0106080709180209010215071407260d0605010309120f0315080c190e010506030903070803040c0305010b011707110a 76
    0x1017070b15100c510100750812000c20a1040e45809802040d00714909001ca0380c0c0580010002000707803052129071031601040c0d03140c40301386041d4011120030800c80c441c514079003903444041e201016140900101005851030408400c154000e17038001c4402c00490b07203031550886200e58003c00b1907080082c40d52002a02d80303070340c1800205030600d801d005038581507518002441d10301c080611413034a0796100240100242c01c040e45840c008c101c108940e0380c510050805c021358800502c0500130f41d8803a0345d6007550112000d40940070b4541c2c80c400500110741da0313100442c151014004c003e0a440c1c42200e8002040d0f0141407540007140080c1004104e548402c1e0b03041d010f014030b65201e4617494101444141141c50310200c4444212111140b00c25070030f00b04944411500d005014842c060070000001c240154801c00a0300c00032a80718805568a00c1d0900d0680318006207407008036200c0d0300708400c850a0358042c0100582d1a500c1c1d648010880da078441d82250750243c00560800c05020703032144040815640 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 161801897 1250 161800647 161800663
    0x92c22140f01060e15040c090504090309050310060611070e0609090a02030d0f020f150a0209060435010c0c03050a09050303030a050f010506030c0702130f050a0b030f0a030c02040518 80
    0x905441d01312440c080c0b450300f0003c81790b603045900c1246031015a001a40c1c00240080c2564001c0d83c0005194001d480c056524045c980c00c007a505220f5280c0301e90800c1c03603941000041d1501c513074810044203c2c156200340d580100380520a081c109500c0041c5203400c3c00e40c1d9041d8410b405108690141c06113401190400d030014040400140d600980b00130600d4040084c0703c4009010001082c15550b89103591516240140c502001180c000501540f650348180a0718060001e450720b1010102c00c00689400d520a00701000c0f031480090404c00128180611030b10f4901030b11a1100c1c0030203016035504aa00b50f0101e240070051115440c8007140720380b010006544158003040000a02d410400c40a04010310142c1c4850321801d410410010840c10640540d0840342e8146e8120403d1040c0c1140c140180504020f0b0302c505501d8401081452241900b200e60248002d40c01c2c3c440031101c0000e030b0350720f81e1161000500800e0020f0111001070805500055021914130305480200300c0b090540fa082c800e00c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 161803147 1250 161801897 161801909
    0x302090112021606110a0806060304140f011509020304020f01120e030406030902040e070303050d0f0b091303030e0727110309030a0f0906080403050901092c22140f0106 74
    0x83c1d80d5140c208180d0344981030017903040f901c6160420507022402404904000c0500e8061500030000c101049041030200e0348030248141a11107480c00c3e82c480038002c100e554120300641c4003100340000da1004c14800c4a008580207804040c041462400640758524445401100316540c3e030300c1070b54960b80c144050405403d284c4d401185c41191401000283c1d4203215481c5040c0d00088070801c0025044403c4a152004280d008101c4101c409a00c0c5d0051411074800b03500701c0050030400800460f40340101541c144070f5202000454000951aa62082d040c028240304081c0305650310b0b41450340d00da00d010702c0600a034010400c031940442c214011380080d00c8400503a48041510440290024041c8416011500d401c0c4051803030314030014a0b0203800350025084c440001210200359200310800f001500d4032984031008070010110380449091440c1c42c080d402da4402000c240100c4068688901d1421a646101440c041c03a8403100707102e40660045520900c289041c45001e55028004c900013005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 161804397 1250 161803147 161803177
    0x8060702100509030301150c11040908030103052a0607050c030a0606150503040825020a03081c0908040905100e04050102131202030a12090305030c010b010905010906020a03030209011202 82
    0x4000103202050310000f500c0401103420510040c4400b558115902560300e050b440e12418800440c103000e09202003907a01142c100d0305113a410818007843c800110304032441081210181d2680074030122400301460301862100c01c00003146034681c0380000c0a02800c030700502c191035403030103090002480d2130300d1104100d50303203030b2501810400b5400001400b440a0305a04009140d880c196540010340c1c42407905c0302902c0030500301682c0d40030305140c40525240c1e40c0a0490842075880f41030054060304040101e15052440c040d60035080e1a0b24025407000780c4d807046659040c14280a1020064a002029042400e03d00712000880700b20811400b03000d1401000010395500c000320f802c191412064222650000104204100503140000c4407940346420034440d80210b0f24803041203d0403032103907001528a22010982805401040d48881c0b00b0903000d80b2010751a035681c20054600402a124400150300041107180119000e90010002c0340c10525102c0d0b05811042580400c80c0c01c00781c10050012 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 161805647 1250 161804397 161804413
    0xf0a110c07140603010e0103021c02061209070f0e131103120705010f270618060608070510050a030c0c0807031101050718120204020c03123403020c0708060702 70
    0x40c011885a0b90485815500c0c03d24541c1080303003092980206100090084d01216040459000094000d04003a940140302c2650b13005001d1004008950686401503030b80078078200040c2d4140300421440440c1e840d40088442c44c2c0d5015100c1c164907292040540c2d11740422020071500350390074096409071440c0c281501c1d40f54040c9007022401c4901e6056125002403a01240740910031103ca03200400030a2884140c0b01d00078985005001b90001440301d1a0302c03c10009850104032054200c0f2080c0c41c2824200e030f0b03200d0b43d20000c0044402001c403c600c00b164042082c850400c5c13190700001400040381c10860415811640e43c64410740c0103040540c00034004019080d0f00f20303400e0007212340102407880c040c00001e0085018001c1e46545200c1d1942c0f605581104800b1501d031901503925803402c00c01525190080c000f070759403104004070f440325582036480301101001140d04040070301c609541c00c840304840e090184181e000f5400110300b80c05602c5005800500c0c80300400505200e884030747d010300700c04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 161806897 1250 161805647 161805659
    0x30a050d05131a0702040b040e0105011701050f0103030f0c0c030803010303050c1504170901090e0103060c11120301050d0201110607050c011a0616081b0d1202030f0f0a110c07 77
    0x1080c0a8203d10f0303510400f114a0610303421084280e680741601210002010303601940000c00500c410300c041001e40d4203110000403c2170300e540500342841c140400a11640daa480380900009009010050104403144551501d20307104055000d52944949003241e510344e101d03183d21555400907801100010720020710103240100500c0360161040b44051045441d04240d540c0442140c240e0310702c2c848820010403526410781c072504d921001407003440c0000c2d420356140d042c108094000000f041000c2113911101130320401d4000f800b444214010180c0034290703400c0c08100940200d000340203904022002400b115508001d01c9050301807461911203540e2891030150050075512680602a0706842e11308201c0c0b02174031801c003100d00c141a9103035080c001d003c0c185005a02c50041d801101680000b41d6a10032003200c0003e0b1400c154051500e0303600c000b0389407003072040c140d202c22201c00c7c4c500903010001c40c03610071080f2982c03504082204408605401034840030040c9400a0f0743c4065582e00c0301f0070400031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 161808147 1250 161806897 161806927
    0x21309020430020f0909011401080d1107060c021507061e0e0d0918090f110a23010804050c13050f0a0c02031602180f04020118080c0f030a050d05 64
    0x9805003258007401c1200b5640024148959003080c8900910b0032900013189001d0039445010a0000c01012061f5943c540680980d21054440d0a00200c0e00546114003400d1000076020704507102990f03281007950b0543c1c00e09c80400d81c0746000f11140761051003410b001a400d401440501e200b030f209810340404001010005490390013402000d03681140c2440b0115036440035101064502d40f41c0c100740d9030001402150003c181d49180580702c800c00c07a904a0400c62546464402c80508941441d0b045484c0e070160140c851403c2480c25281d4480d0755090b0180d40219400351b0f119000308141c842c100c5141020a04000e0700d1007031421200e980e0b8040210381c12050780650380021002c03030108406d601e4642c01030351340e01c40d15104484c00d40d4481c40c480c1c21542d40c040d83c401c0003181941c010a2506207503c1618403260b0560303040340803d5664008501c40009000c1520850300b41e08010724900c0d540205002044041d2212550103001e01d42102022074410024464a54503940e5980d0380c4504511440310 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 161809397 1250 161808147 161808209
    0x8340e13061505030d0503130b040803071815030f060e1305060c09032a0d080306040e010908030c0702011202030c040302102d030905060703050601020708030310090213090204 77
    0x100d0b0b164608400d00a64030b000074000503c548a007419030b529100e031100e00400b2031000c1802400c1460850401c010131002c50044c40c040d05054540038260780c0b110501c201b22010500036400240f80000d40c01c40c1991107a000080c10440034880007c410392507034803800700c00d5800c581100390315840c0407005081020802c011a03208210511302424501c0000010380c6401501d84685890950070700400d040b16200294080c040b54000d00803516003403070b49010300c51078004441e007a10a07441c2c110304e010484018011030410319400442c60740f642c2d407030a40c8511b00e41c11101080e0304202c047d00400d008500188010341c007400040b207009071114918810072501501c80c09504003040741c0410004c5440c4100300c158001080035901c4617402c0c400c00750b4110010003500002408612803c0d0500118a41550006008050a034295070016880c4c04510b030b030302c0c030060324000c0c2480b000d80d40c00c000344503055001c0c01800c00001c1c007c198046c0d07504808001c2c0e801c55080f01d401980e0001400b43c0040350382c001c2c41 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 161810647 1250 161809397 161809421
    0x30a150219030608280206090109090e070e090d0c0b0a02040504060f050f18010501050a0e130506090c12060d170a0215060a030203100f0209040e060108010608340e1306 74
    0x3c0da1082c038041c045d02400e1442c000070b0250b44081940b004980c0904104c0028118000d01000005568000c0a0361100d17188203d80405640c040428540303040400e05d01c00c2141d40c1d03210280c81c160b240da100c8001c0300000b0115001c076130f400d12003c1181c1e551400f40100521060701d1240e01903042100300510018030502e0103108402c06050403582042c000302e110304407002428216110302c071070f5000343c90901c02c904030240d115109035180d41d1240c84943c08035016140503102c004844d0f9030144e01040b81d225902000141c1009800000c8840c0b9000e502c0700c920920508803400707001e444001307a00703d80e04900500800340e0080d038040c6000c4080450610740c801411590480701c149582c02280d2251030790b0040c1805c06071900c8903840c10306841e40441e5582440a0410031441e04250122034a0302c400703010b100ca065080c540700090b1160005100203071480c0c91001c80768441300c29100386074001c08042413401d28100442001850302012411184206010b01140c0314070000b1340740400488002540305 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 161811897 1250 161810647 161810683
    0x3070309170c101101020708030406020d050f13061d030a050a081311041805070b09031033090204060804022404170c090106030905100902030a150219030608 69
    0x1c80c050707070f01c0c0f6203081c61814403400c1c120412400c1e52802406403040d100080c1800800105101c00c001041e17000303280c2902450801c008980f9010b09000400c4000d030344141c00446408074241c007158160307020344403411180140c08507040d98880c00c0c9003544c010b00300303580120b80c0108542c1c54050b08806030381ea012020796100050b050840e41d4040a51070300f003500c02c0c011681c42100e404400310716454420543d0b0440c04654403680e648009107600e5200c490300e14007a000704e0b401500da444c1a0f000c0c40c11101040c1c2d5001e107001a101780c4075140b52141a1404401002d24540040c81c0402480284090500c1390b466954a203018010b0194070449000000481da030035607480c0209068440648090f02c40c0500d10100080302540b24500d0400343c41c400c00d9020b85080d0000461075095400742d150704e031182003901d51421301641e15604951030050065007541082105d82e00184100b051200d0ac00200c0400504020105901441185901c0c1c41640820782d2081c3c00c0c00a85420405200320044108203 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 161813147 1250 161811897 161811913
    0x1030203120301080303280e03180f030d0c0f0606090504030f020d0806010e01030915060e161b020a230a0f0b04030f0302030705190219080d120e0307030917 69
    0xf951750f440010000716480c5d1070609022150000b950402c5140020403a06100344c00490b0070303580d00c0341c1c030052651030345910996440542d8248480080c03070b1030b180140544440441a201a00c003945014400c44018990980c075000049080c840c0303801074841010000340ca4540780c44c010300a410703444100000d40d4400c00795603002c00e52041c0c69582c000300a107022000308080f200181d0192064103002040c180039040c6540c01a08540c3c0440c080b150140c950390b04584507030741003100a51a0303a03101c40010b41c0a03030f0406c0f1101a03a9400b01900c51015203044c0c00b4070b03591007403030140082c0d490b010f400307520040d441804c06150401151000e01010010342030182e01e010b44a4840307110781c0c440200071500701c010340ea00345402401170740c070900e4112065404211594040013221104144100d200320003180d00c40081d107421581040030340b01120000c1c160111440c03003e031103034140704d940d010006485646040c0308510920252151510946905000740d0810490340400f03040708010642d0341d800355407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 161814397 1250 161813147 161813159
    0x10603050c0117061e0a0b0d060b0f07060228030c021018020909121b120301030b010b030406060305011d190c05100207090c0c110405010614090a080d02030301030203120301 76
    0x2240b240c0103602217415441d46410440030501e00102410703016441041003c0001311401c200d4010640b044051800300f0519840f0120381c6610700030303540401160007003448540c0025069500800311803081c8804244040148001903141e111000114000130fa100c03109040400d070104200c0160340308140b170030f002c60003048400709036044603848044e200d11a4071010505812090011a6203a100c2c003444070740c1d40704c0d070401e8807524000103c03148502c2d100b510141050700c032901003603a060700d40c86007040906034602405004141c001400a44841d680c604000000035802d2051718008076205c1c40012008145000440c00c0200400719503400d003402001100002d800f0b20700712030641f801100c1403850741200807c1286000300c91b422a004251400c030003120b000fa0000580c10b803d600c107a10f8140e40c10074020a010a0303801c28800c06c400300755192101e940040ca24000f4280380f000103050001c003a541d40050500e81540f110001c00942c00020050066040034841e16180c05181ea104910755490070ba = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 161815647 1250 161814397 161814437
    0x9050108060111060a0908190f0906030e060606030c0c07060e0f1f032c1005011e03031101020c070905150307031101030203070c02030a0303050106110106060207030f1a0405010603050c01 82
    0x20300031500700d1b035205990340400c44960180c52224005041401525030074481c06840780040c071710200041a03d000c00061031034424085d0000e0690280080c19003901d0302c0c0280a030903003001d0502050b14609012020803107208004100c001c18182d980c050180183c0d405110b6618040103026006420405002000c001c640081045201613490002140c02c880b00602c100c200c0b254090321b01035100c0c00c3e8001c0f540700c40042c0a0b440d1400c0003004010b0703666074050223200201810310341e5a80d8072010104202080c0104030854410b00314400141c035120500c43c0113030800425801c410b00c195514018041b00c5d00d2694514003120b1000d5005000003401c584410069441d0540f007141010740010016109511640c0041c90455002d4220394605000d89005400380c08240a40070007c3c089004040301e04c0b00501070981140c401d90040c3c41c5a5046072142d1a032480403010a60380c00c084030001d95291418060b202e481680110300016480b41145409400c0c040c80c180b9242c10032140d0b242d4403140c06000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 161816897 1250 161815647 161815651
    0x7030612020a030210031e0615030605090708040302030f0c030304061503021804020d02090903030402090723070512030c130501080601050d09060b15040f05030a05030324100905010806011106 84
    0x454005117082d0342c86401b01c000e0425140b1800703d8122001003042e402025400100a5034280303030714a20a448100380841c101d442901c0b9040d40300021002082d56540140b441c070707804c00c1c0244140d03032901702c0c0d0842c190380c190301003965142c01d50f00010401007800a1403250700aa280d503103d8100c07103986560000b405910410b20041502444040030a0465840086020b0019130103800b503000c0d481e020401580fa0341049030b0507400f4100c18400151107a10600000c140380002c001e402d03c103503c0c4003510b940706400251080b03400e84254400f10441c00180c6000d144180c01d440d43e055510021403440390100c00701035000506220100040c4403150f030f041000d5a444144140001030b4280309400c00310003400841000e950008950645600d81008100040c41660444841442807035561800d0660318070030300501405a070018000f08140942d507042c0140c0d840c91282d00c1d08d901d08101c5001070b100681950b2240c0100d0b8000c0740803c42d07560000038003607003d40b00b420440f00c00340c10410095104c1e400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 161818147 1250 161816897 161816899
    0x501090e1e090c09070804060f06080d050f04030b0405030a090b1201051315030303061508060306070305090f030324040b1e1903060609050c03070c0f240507030612020a0302 76
    0x2003600040c6142d28108881c0400c0603004010398400d00300355501500b1068141c80aa0b030310b60030140004164212800360100712003800c40240501d480c10b103c200d80c00d42201c2c50700150703c5404c100001c0410a159005801207000340f0145507240d005400c0039040325840da018629a00c018400b03c0011443c8041b518112802650f102000c1d03805a0354060040c240030201c04944041040044181030740740d400b00c400c3d03171908415441002241d000c2583c0860088501c035500d40d120380006003a080c420341100c0c1d00041c0030b100b01c40c00000703000d0103503049d40c0080711840200900303d25000d1a0024400c4900e04441c003d43d000c111103d220000305141403140d610152003440020b82e10100f6442c0d80c443c030601c410300c02091850058503450140301416252150700243c50400c404100e030200c1e00c00449000d105030b602c8800705000c80381e07110002c200c42c0e084103071411910640004914a004035641900c9030100d00001418500140080c0072640d2940202c3d0540250300e180c040103803030b04e001500070740750 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 161819397 1250 161818147 161818201
    0xa020306040b0a080c1011030309010b0f01020c03030f0d140114040b27071209060209030c030c0607151107050606030127031b0f0503030108011404020f0108180d090501090e 76
    0xc2c00d810641f185c030a0100b0500c250b203c0081007040494066000c00c950040c213748159440e0b0702a001240e492303034170f40101a85030300200841503880000c0c070007c003062582c002002c1583d40c00f200080f590722000b688800c95020100c07140311414a054031a0702100b40040301c0034402008050000b080617000142c0300003a050600021440450140309031025030070b403106003801040d0003840c10f08060342040d45014001c3c0f00fa548a055540f0f0042108281c0a0000c2c1c11103080503229221180080082e40c6064056644d51542441c000001c00c01080c04500440c001d0186050810504d070842d030700708003806d24985025030074481c507103403204d580d400c999054a098540e0080b9110024541e01031000010682c10064861504104022010b54102c9074440003c001600724a410700b50000403c58000b907020711505a01401d03980509101038011003c540c0704486101d00c0d034034481c42c0c0010006500081103410004100313960340b210000700a000300d031aa20500e4141841c1800342c5048000500240d04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 161820647 1250 161819397 161819419
    0x609030209130507150210021e070f0204050411130504030e2103040608040b010801021c0906180804050f01030b06040303110f03030a021201050d111c05060a020306040b0a080c 77
    0xc44400100c2c0d4429040700941d0007055856280040a560f02000503025004949141e045ca50192003030780c02c60b20320507011200c0d0654550400c1020fa005140844072107940d1043c0102503259031164900c038a00c14003403070801c4041d900820208482500c046030565042404120010303902244002410300c0c142c9010be0404061f29100c0621021055100035501c4080b40000d80c4580c0400c49900850241000c03c4041e40c807803c03041e00b0303446001e840e214031801c0d05650410050690b401403611500a01d40014028000d007151751225045001c1512940030104050181c0e1a082c059112060400d080c01c11894070603001040ea2401540b0011b01401824020b203135081c00140702c1121000c180750152560303868507003120320081d0402200494070a030f00300b00100315030a100d41018442ca4009040a200c0440b0300b040150200c03410f0110140240d01005000c0040c00801285003e41c114030727009601e034541031003448129940c58400510421558408004c499000b05110400007015202ca00c404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 161821897 1250 161820647 161820661
    0x302030603010e0102070f02101803020d080415030c080921030604020403020d0b0a0605010509061b030f072a0b030103030f03020906040905060a0506180d140307080a03050a060609030209 82
    0x10306100608003c0c0e540002a40401c0002c15003076008030920845002c01c2c20320703280c80100e6095080074150081c10007141014005842c020012812491003550440c0c030301529a00d030510340d2419275400320046074659910084190300030320700784c7e4455522001403007a88512800075041141040b0303022034220002010610989803601120040d50300900012407840d07503841d0019030081d04950710800c1c649080c03400f040d42c1d8482c80c210740380c4680041805050040f2100e08103010b101400ca49040340c80100a189100b40c00c040160007114002c0e10008064640102007403150300000d0112859490500001e1000005040c2607070306503909440c04103441e600c0408107070002c2c4900e214041e4442e1000c140021401c2054000364442c107000da40941a65a4032024031040d4012500781d0301e800311400203102c2c020300b4820841d1700414060b590499134008a44441390071f40d4011074069450310400a84410038a4050180d2600003c01801c00c001062402030001c003c0411404024410300c1220086582 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 161823147 1250 161821897 161821901
    0x6031b0d02060a08040501060506040e040b0901090b010603020403060f060b040e0703060b03010905091504120e0102070e0109021201060c02100c0305120f01090b0a050901050d021f050a170610030203060301 90
    0x9a9400b4002540d0b4040d0841d001e80144404c4078111050341c200007000c19141005019141202c590741302d1910349403034540d0780107403007440200030305801d40d6030300307504008038030405031481c007e05151300c0050fa0349040d0700340303a01910000c903402941e450400d04100b00340a03008044074111890140e4440242d1290501280a00345982c02582c0d40c0401100100b0203110f41d900c11401002c7c42022648541030040d40c1c0390955808603005031520300307107940c4520690301428805001039014030543e42d81640301d028140712440282c1040ea41541d02280051f280034a100ca900e014102a007804c400d90301441d800103005c0c0784101300c280e08004600300050105030140c015a007030000b198802c501c0302d141c24104017034007030402d00c56282c0450070151040078904110240400356100034292050603803d10050049010f04508126008100b072107100c1c0811030103110301d07c030050b400e695595175214440c500401d03001c106440c0a41801c00d220034007100d0b030b81d2041180c101020328140540c59139030344c03c001b1740 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 161824397 1250 161823147 161823169
    0x103021b10150806100b180301240501050705030414040b2806030905032a0307050606130c02150a2912120301091802040617010f0506031b 61
    0x324034811510380480c0110795800441d54040505a45903405039180c1c1c440b81c1d6020180d030400d6007507901034400d00030700d08150014002c14106001c5004c0c400700702c6020900715001d03010280c14071118408880c64141c003100140d00203202c00d281c068181a00303502c8803922480b0300c0c400d001a05109044e001e40c162541e40240001900003080604544440041880c01000002d0440030041c011800400e085000f44070302e4006a40160044d81044050b001c9540405801c440004000c1445480070761003903001c2009025142c4100080c003124240f0030203001e80000900c0c8128402400c00040d40354040e80020404051001c004030b040399529000410f80003024809100907264080701039424007810307039400384100c968054801c9600c0f600310080380b9803a1010600251040e038070030001080350316001c0d000541305801200041c2c401c40120390000302150095403080c151640300d180031001050b000c1c4501104000c48072801e00851402d400080e46400329040124811080c81d4800000c0382c031481c111013 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 161825647 1250 161824397 161824447
    0x5100228030e0a0b0d050901020310031502040915060f03090b041112060106020f120702060708180415061b0b0118060305061302190605070308180604080d18020906010302 75
    0x90030f403644440760400143e01c00800b11940a0400e408100801014422240301d000c0c0b00c0701c602c45143c1150784009824040303011203800541c0a01c0003240e502101d21480d0b10380c1321350354100c42d042841d01c00041c00d1042e48800340402e052800c8409000704459000031030b4025800790310325013130714400310009581842d41002e5141c00c2c030611002103045600080d00444228602c41100c01c07100190410881074801c07080004c0d0400ca0601c882000180a0303000b0381f03d094050f4500c2079043d9904c0011070202c50b41a5210400b003040c45008100442d00000c0a035079645210144800e01c800c0c43e103c804040348d040c400c511185800c0648294400503030350283c0051980030381a500203003000c0d40c0401824426020a9104a1055038100300e00054610400125041525542c0c100504d684060350300e00c500401084903009464034801c100401401051f114520a034007541d241e1401080d03410488961348010301c2c0c03594201c1500400b60b5246d0340d00340e074841d100746000340e5528501c80c11000c951599101d18 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 161826897 1250 161825647 161825659
    0x1020901090806012318070207080f060103020a030b06031009120f0302130b0d020706020d0e0d0503070914012109030908011e0b040615050d05071d0d0314070b0105100228030e 77
    0x10000b00c41d8041127000444564400320382031402d41d01c40f10380d00c480080c80000e41c005002c48081000802c440c5010380d0103031005041c0d800c0c0c1c21480c0b84400c150f4104010803580700345010945982a0f0300060601003100040c83e0031403d201c403142010801761030b5400348803080f60003c5280b6200413180c0d01102c0600f0351011056444249529000b00a464240703d486114012007440030b08042c8280281c91145146503a066460303072800007d080c0032220f402c0000c0c10441100744610205000444005e0461841403001032410b0080c28010503403040740c2c2148030035074107000c1c5400f04010501c84400300703003807080d00003d40b014801001500900c00345d0f104030410144002244940c640143c060328400184034014000c030b5803a2403084076100c0070a4030b8142002e1a0103480142802c1907480d13120024031a041400500310020a040c441d504404d500b02c4903141c0e00d00060083d4200701540c08400150f6000070118191241c1c001e0710300d1840c80c000400c14400c40d914034400d05200f42c1c1d0001100320054a4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 161828147 1250 161826897 161826901
    0x80a2f03090306060103090b010e06180118050108010b0d021e0907050304140105040b16140c0c030705150f070807020913050c03070b2706040801020901090806012318 73
    0x204980301d801900681c1d2190140200003251940a40148802c955104030785500302e038240800c6482800c00030b42110b40006100a4a603d80018402c859010304403074480702454400d040050f00680724141c00581441c4d0411170290707071940361041010350855040b00d040c09205038007100010f45030952143c00754881544030070b02000c0d9030400300940c0154042c1b280410b45109088095090ba82d05940003800f04d4891000140341281442041c1054030342450a803c03a108220720640c0b8a40041d684134030030750010740d8000c503d0b25080100320300402060f07650341030745114002c4103601406031184d40350310300400055171010008540304075507001d83c0c000d0a182c0c00782002c5101c040d2221051a0443e018459018481168503000409800301d5400448c8946024031072500b80c0c0c4910050f200c00d1103444800a0b0544240d580c03030004d400074000308000140c49000c0b020004204042c02c4d440701026400c00001840548114290101003006030108201c143d10b0010216412030b42c08610035803d0311000701 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 161829397 1250 161828147 161828237
    0xf0c0111030f011d070509180403031d070b04091e02070c030b010503061302010e0d1e02100801080c010c08040e0a050906060a0605030a0e1c2109080a 66
    0x185025120484a90803036030b03224010b400034980b28a12021084c107462000030882c07032103840188141d00d0050041c04a011050f01d0702040102c06650403000b107034a851440200d11250441e6403410003610008202407480d05e5000950380c490350083c0300301545c58000da080e030070690050580c5060a407900840d03071403050b8180301d00c0c400c09500080702c001400c0000004d191500050403400b59407501c00c0440010041ea0054489100005c0616000a45010031401141151090b5140c0d04840d20341042d06590500c1088400030401c002c0205110010380140b10808000945210540c5e00b8205510151001c0c00c04415a004941c03040744c200c18803030204501002950010f90180780c40350100d070813035160301c0c0c20000400c1c12400b0394000648140b00007850710b403071600240d80880041003642d4908030226240c5c1d40300f107070081d032031400b04140c90401806180740004104400c2a407950404c40c8130810b40d9441d50501c034000c40d075400c0141a84042d00da4080700541c800701d0381006854171000d1001e0030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 161830647 1250 161829397 161829431
    0xc060c05130e16050414010c020112020c0601090c050720030319020c010e010e0f0f040605041d2103012d0f060801080c0105040302060a0c02030328180b0f0c01 70
    0x8403100d14038119007180b2403d03e400740c000d4400355036008120310180346845004480640500707006a041106030300344180e500706684000c1c4100a2840080c200b0ba60520300550140d80c040205001040703010805280808c0719a4000500d000c101c80802c4095554400000d10f1401404180384c00d62030302c50802c0000980009280d111010f00303803220445402c100005550821504c0b01300d60700068480746880c00392402c40c050b61041d4a008200043da142c0700d001050440315102e031246d140030030f00c1912034241c0008010002c40720350fa015202c8070700c0000c9103d10b940f600042c800c40744a0040041130384440c1114080e03200e81c21004840d05030120ba03440c921000007501074401c1d640481d0801002043c0e12070b010404980300c00c2d040c0c4503a85410301d1039081c1b05996214080d660100312104075941c005a03401c0c0011301848070041c1c4035240e000030300452800d98a4865202c2c4051000e000c1508400350700040e214002c464100d854180c5034000044144160b01c6a0b8024405a52800b030b6200007a416503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 161831897 1250 161830647 161830651
    0x3050c12030a0902010806100905010f0c050d020109021810150e0306090d11070b04050f010c06050112060b010c021305060d0f0503030a0608071a0a0306030204020309060901050a0c0c060c05130e 85
    0x740d84052058941c11f09020000682003c5040010f040c1c010502085d400703001980700503a401c0c980703d500002140c54243c00c141c41c2440074401030f5180e098040641c0b8000e42d6545071a0b103516054112400c00f4051900e091006101340c1c8851030380b105a08801d1401803541c0300788031001400352013191820700d40c1503803180000c01010000c40e0494099041e01440003400c1c1c800c3e111025100ca00d494100820000000d9808501a0400c49800305180000d01c0c9401154028080070114174402c1c643c038a0920b0503241c001e2403660400508408038005030342c44c00c0c01c80c1d00e0298030420001e410380710f07480400c03002c201c411030240603c2d41c011101420814004015441104100d5041000c40c0c0c0301d543c0d00344c40b10300c244030301038500342c0351281c001901c0741200040c10381ca00346041c0080c51507039950210b804d98100705c1e100030041d00f0040411603800703000c0c01502d034021541542006a40350304280a000031241080182c0019a55200c20680c50b02800403110126a0980707001e81507503a441d0b002c902c0c0030003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 161833147 1250 161831897 161831899
    0x1a01151e21140a0902011d03120d020403020f01050a17041401020a0c0b01270203220602120a151e0509090a031d10180b04080106030224030403050c12030a0902 70
    0x40c00000075a40c8400d4130904149a0341691450100040c001d20802100181e0380095454094112003c04140f00d400040c070346988007a40150f10341d440e41c0100051001414001c07410b0280c20080b51007076a503c60035142d0704c43c0007003541004a4940e4240700c00001c003d00010790303466100086039a19581c0049072007900078420a4040816030302da602c000c0c6e440c4070a800c544102d80302d0f5449a00f070f0a001d50091039020318030646916020105655485004003180380945a441d070010750b601c8a58a494683c40e4070180c2102c05104500c2082400309d51540d5078844c0386200d04030446080d44c031034201c440c4400107180007007003038410303050803280d281d100d000803071086021610301c21811100e840144964803104100a20121250300e8184046c0c0302c5400040389070400943d0031a002c140d081c83d02c0b010380054103001000246407419881030000394030707070f050600501a84044220100c00c007a036040700c0d4401d13494600180c59003c8480345505c1e1080c50003100019150200800c100c6a125038800050940 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 161834397 1250 161833147 161833181
    0x603050414030a02250509040807051603150c030515010e03010b040f0608070909030c03030b120a0503040807050102030c07050d1b080d17070816020304050d1a01151e21 74
    0x35001034031009413181403286c26001042d003000203010a81c10030150600364000c0c030580d6520040c88203c0201c154054004841c081440c1c0214a481c2c14644500000803001c0d06041200b0709060489842d081d009440c0c10b81048841c20f01e850480e10290024030184801500500030301e20004036910150100d4010700a052040d0503000030303040400c3c0590400560161a92100a6030b151411406460303c82102d640098400c4072203081c014007003110b8264a402040503584841c1042c2510782040100c4e4080c0d0304550007030041c1a982d410102e0b500044407400c584620005c2924500b9940642c815000244c050a85ca030f40096442d0b00460541c10140b103035501c4040514000c94042800002607038500005200d0800044602441d083d58400350313122401100d051640e01c100041422040c21011211010f40000040e2105c000c191400c0c050802041050582100d9000003060303000e610741382103004c42c41d10142d413030a18003501c4c40c04d00d0550031840318a003d001c0d04103100040c2911a4802ea0840 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 161835647 1250 161834397 161834443
    0x7050a3309032d080c07080c01050907060c020303041205070e070509040c0c150e010204180f0507080f0c16020a06020105091b18060f10020601061206030305040603050414030a02 78
    0x2620091000c580f9100c50504034081851503041250304040080000c0180402040703403001042c814006010101c2c021000071940745010359595040845d84e5020405102c440740b854001270303a000c401d8030282c44041d84419003034412401c01610344001940f190b140100c0b08420310084540c803100401c0f503441c040d0b50510480c3e10360102101c0d0341d001000058008c11540d41d803110064042d0300701d4480301d09158000350070b04c0c2c3c81e00d024107002c80d1008460200709541e5641c24030441d03194040e080d0f01080509180046190050020b0519034001305050884a80003921030300f40f8170102070307104076685c003e000c40800300d0b15108084d000b010240c40d203010b10710503001008500c800600948550f9003019203040718200148498044c481005000d295020310007900d4400c3c55190180300080026140c0d0003481a07514008001c1c1012505008800c0030030304020307003440841d42040442c2d040700c0b00391900048039a114105840254a50501c0b43c1e024000018000e085c0c641c00140c000701c1c4075005458042078 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 161836897 1250 161835647 161835677
    0x110414070f140316230f0408060f0411060a0201061806080c190911271201090308071407021005090f0105070f0201081305010603031e020307050a330903 67
    0x240c00210b1302c5100904016540440407840f0704400080101c141180383c206208170b00c1300c01c40d540c014000050f0820404101000a080100807441d00182c9000c0c0c1c0505a060588803465400e000c24052405620009180d4061038400d41c80b0f60010a080c048001c1e941211440c00c030007404ac0c030300c202441b5200e41034a5580c180707481094058a040380e8002c10441c9803810341d4440107007840c42035003554501c0901920601944404410549102c1401307031400c440c03800c0c2d040186565003849041c8003603241800200010360081c922540000e00d034103211101c4114584443e24510038864000e4201d191040411020f0360444081c142c4c0c3d58080703804071040d4110b0001103c00d40a000d0028012211201704800035500420740e480d08040703e4544c40b100d031602c1c0e89950f4207452455004800040701c0c407401c0c20803a100c0d6586003984045920145180c1140c40e00c443d540e61141000180031500ba004046c0403194401d2440e8100004429403101c5181407840705000628500c04c040e004150308020380808 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 161838147 1250 161836897 161836937
    0x6020105060a0603050a06050316030309120f06110706020c060f07020d02071511070605120105120d110102190306030203070803030f0109150306050406021b030405060403110414070f 80
    0x8070340300180006644030701e0050210b000d03281c00350800015944d14400424591400d1265030240b101000e2000f600b02d1940c503009220400980c4098040c0021520150000d6a480d10a003915504294042071001c0d40d040d4019403440342c040000c1c000b52001610040210f000304e03065102d00309041ca0b001d401e644e001010f0340c490b81800c01c41740044c4c0045006102480490442c40c068101902d0810442c14228811030b182c0103190700f10b10086500810246c4501c070741c0100042c0900800c3da010710607089881013403941c510000742d580b01809803100c1c403e00901c40941c185d500c040c0d40c41104a000120700000034006101a0200303a00074085e008021880d40c4002045038041c5100000c504003c0c0c0c03030301003201d0083c01c400500c584140e07401080080414410b01415003d240203107001a59454400c03103102e49221180000015500248801c2000c0c1e5200c1c0c0544040b2900030308942d494010b030800240c000d00401840d85040540e502c1444000c0c2c0d404001800415410f07100c84594822003410b002d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 161839397 1250 161838147 161838151
    0xc090a091a0603030703051806040806160c03120b0315010f140d0507030f050a0b0117100902150a05070209010305010c020607030207050a02060a0216090e2a09060d0501090305030a0606020105 84
    0x50584d204002d600c0000f4819001082c040c1c4020800c107080600e028002021503105a1240d040c60b4804000d204440c5001d060710100010181080e41c014016542d000e4030300d00d180345150b1b005075900e04070650291001e000700040d140034184040365540e19180703028100030050141203a02074a040902c4004c1c10b00f60420882c05030000e0061104502c1c0d55141c08004140600c100d4a40c050800010000380101d240b05000c0c00803180025042c903060b020341441c003030741c00111500040c203022504015072145010320351071007402085659941d4124405a9040c895928020f410407080340001042c420194003101241c1896401d9551648030384908609038005c83c4e4000e00640c00003007410b001440d00e0001058020100d0055804400301510345ca2000741c12036220156080d15260751a0f40340ca82030200a0720150020f06255103204c0c0441a525a403440b520128041c082c40c2011a01c16515440d1004849900034024481080c0c607181c010800d80040c1c1d40c0003006801c0c0b20300460030b02e0060080038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 161840647 1250 161839397 161839399
    0x70906050604030813080316030f020c01170c040f1403062d060111010c0f02060903070506060d050c06030c13090902010e0d031808071805010f03140c090a091a06 71
    0x60401d81191a22030344d540c803a019030070110034001c800064140c1c6c01d002400681e240541002c00c208440d08001e4001c0f134001086204541007490240c007580c1e003101180b40d0380e2008022038081540c4ac007002c04d081e8071840d000741004000780c1ca00095103601c0c8021101c900d00095003074a5460321000091451980d07004001e020425913040c50081c114418520940d01600503d8800c2d00100d1185065007122200e000303030340014942405000400750104a0303203800491050003103203001070544445d0b80710313000030303002910032015103640005014041041c0c1107a680024540c0356a410300301210300c40c81e4090154501d203444105000101081e03a0710400229603010f84803040d00714100020000b6907954800304805200d0404464a0801d0656042c08043c1441100406605042c6a5031a100009082031003007800d00300341c0184402c011054500301102c0d40701c140d24048412000e0342c241081c903050310712500302440030200005246a0742000301c1c814040d041074640c401c8103821210421500304c0300c0c1303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 161841897 1250 161840647 161840659
    0x4150204030804140402040b0f0307020f0d0203040504090f06060806010602060601090509070c0f05010204181b270e0a05071805061602040209090c072d020103020307052a07090605 79
    0xb000900800c4c0608003618000910046c90262030b03802c0c03040d96400c0428184481d410200400c422284c04000290503c14200c00401c2c8648030080d0096580c030030f03400f400d0b0003241c40e0404001048440e0010046441d40120184202c540321954142ea800d02481030394010710407500410000c1d40a21308032400d44e4009010681203031356500381600c2d4000075a20455100d04201c1031040892002c4c400b40010f0b0074182454030f030340c55820b072810080c1c0320190404121070307140c2c01e170501e200d40d00102500303130001e40c0c064441404000402c40c078640800d075601c200d403c1203c040402519425a80c4079610a200e1a1150800c04034510742041014040e030090701d801034000c0000038503000c00003036020b401c10710040000d8588903806011840e283ea0070766844501e07070000720303c040400284000d00d207440d400010921840c090107102c100b222442c000e0003c1d0600d5030000101d007843e07102d003080360b11403210842c05d1070b804540c107444d0102c0b80c01c10503204040750103615008201c0c00c089000c2d15049071001408 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 161843147 1250 161841897 161841899
    0x30816020a032a06020d0b061914070b01030c05090705180112020c0a050d1e0f03021c09050f01061a0306060901030204150503060a09051e0a1d030304150204030804 72
    0xb503600b14007000c07000351000e10008264140782000f0796a030030510310515002d40c58142841d0000d0a58106440e079a108101c02d200c0034684841e500141e80300000c0038a00300030510840f2014920a00c108000030b000713102d682d40040107124880c1448401c030b07081503800b0201a61115030444240c000d0742e010700300201d1004107070502c2d0b610450040c03080c0558039100500e002035140001386001c00207641110690812080085040d400c00701c0400c00010440c080441c0c42c1225100421421441448809044d03001c134a00001e809103500b014103902d8441d200704490040c80c1000c5684a82d40e441c25501c56003030003008114004051103240031228001042c1d400c5480d200d0800450b40c10102d00c40c0e0425a003440300003440700d46110940503108003034458668906211060208107140c941015058a080c0b8003840300340791200e00c403c080409d100242c010203880d51800c050180400340340d007a03160101100003980d200404002140103034480c07203440341e0060141c4500e000360300440c803010340302d0b82e030901c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 161844397 1250 161843147 161843153
    0x501080f03090910241b0503030f04050c1002010b0307090b33031302030c030c01142d0c0d0f0e091906230306040309060c0314030a09031205100b0703030b100804030816020a 76
    0x510f8032f80140c400e1050707507113a032415004911480e80340030200340141c0d107981d242c2c8511b0030144181800380c42c034400140a001056004180840c0c058411400c2c011012003036209000202d60710501c2c5500a00106c581d41d0401c1c0507207200c01c00e10f0f040260311900800800000d01d19000900f42903090041e1a0000c00a0a0700786807044c98000910b449105041007040d4203d4004504e6001c280301104030300035071101840c1c0c01191a00c004081640c040c81490300c541d20303010f80c00100c0310804110480d410309882d42c540b804820000198421b00201608112021910f05072130055078184002400c079170041d11122004156072824150f80150101e0305002d82400303050710404410021b0346c000e0410b443d001c4c2001c070824a60754011140035940c0d50b501c80c902d6003015400328911445002c2280144081c3c241407041c10741c2003100e0f21a41c2c1500000181d03000c00c050003608040c1501c500140345661140003048090312040c0d080350220001010b4000041ca0043c82c3d40020705640c00c00d0b0300410040000703035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 161845647 1250 161844397 161844421
    0x11d060c0702030115030308100f1a0a05070209010605030601031103160f0512010605270f040c0306080303010306051005010f0c0809011403190501080f03090910241b050303 76
    0x85002da030195210030408001c06013410000000b14443c0e540d081c1641f400000c40400f40c3c0ca107030006406200243c40400812a02c19010082c080170705800503500d50b5540c00c03c1d10f0038850074070000d4107e80c07035200010729150888003035032280f142030700d09020311810000604850f01c0212495030396400c030030040003c1c0c1032107a080c041003002a030a1042c5861803802d004220300900343d0002c1e0015400043c44103042200c80102200b80c2020030259600d0074090f0300148025880c00520b40c000c564071a41034403070520a802080003060540156a56940c480c00c0100141600720b0306180200180040010907512846500e48038220366550034003084425500d11400342d02001d203281c100143c000b070f1000c07030f0801400218000c0c0c040f50078a500317054640241030251003050b070185626410000443d0700d010008000c0f2002c0707003422a400c0e006940e4510035240e030084c0700e80001c1d03850114425003002c072440980d5091004031a6484124840d545180c40141410803078000400541052000ca04c141c5030034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 161846897 1250 161845647 161845657
    0x30a17040c030212060a0b04061202010e27060414010b0717040f08060f160203040504020d061703041d0c09060a02070306021606060b0403030207030b22080903011d060c 74
    0x740450340c40c102d42d80e400080c880c031010b500c241007036000340061042c034551a210f035808411040e5414055a85011000c000c03104804401074184100c4004282c1c9554072000307407803502080c20111181c071103040c5480da000d410040740e65078000c501d0b00d81030750312115035440e680b4100c0b885049230345d18240156071940d0100c019801c1c403459981040c0000b00e050bc20142c1520058074111004014528007403424030703d01840603286c0c44104207201040410a0b60100842d401e50b001503e0240c1d4500b001e1070000d0061183e64000781441c06004407006440e0004001001160302200e010180c00380c64008090700ca250a035a1120708071410001a0041c0c18801c0260103c650b550055650150352601e07220240d0f8010110403215a010440000030844144a44005003e070088414242070455170041d507a032909000c0500314000e1580000c40450007100c000d172228080311100040e841807441c01c000c2170b4000681d010712950030181d030386083e03035111176021b5100d1201710018400c584403c065400b0640c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 161848147 1250 161846897 161846903
    0x6090c081308030112050703120e090a050c0409020c0705030a0f0b0c0405030703030e010c02130501150e0607030c0519030906030506010302031e1e15030609060f150f04140105040e030a1704 83
    0x1d03c080000108609040541c49c050054540038000c40d20380d806c01c00d910718010118402c192030141804158540f54043d00c1c1175990800006035940d0741d1400003490300c02141e11130348e410b10070101148100490399900b400000d200e582803402035103400a1442c61406035004441d0154008039080012911903d01c401d001c4406040002c140ca080b50040b0300d1201072486c120300c6160300c400040000c0c204d44551a0b1001007245805d12040f40000300050042c40b50b4440501080b00c003c940c401030090500070b04400d1001440b2091012400d4a00a030039095a4451017011914010014680354064001c603403045400a80d800742c004100e036030341c152500000d0311008030320085032815541d21100c0c40d0f4280c003403170440e1004100c000f0013a040600c0e00318020030a100b0380d0004c2d002d1001003698461680e4200b564180305078806400c07030003c40d00582c1d01e101344aa2007410b040e5003907004c24040c18418183c900c02d680900499001c2a082550b0b8880c00210a0028010175000c2e0034041d940e092a43d040f43c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 161849397 1250 161848147 161848153
    0x30c151e04030c0615051207060804110a0512010e0105060a081009080405031006090b0102030901140703141c060806060310020903030c0312010f06030b0603160e0406090c08130803011205 82
    0x10141e211300007182c0d0612186041280c420303405106601c2c08114043e81c0c4602c1e03000400140341048070043c5a80009400189003c0c1e0955071044240e49414440c00901005020280d02e000861411406402002c0110101d546090302051150a221550505903140c040060903410240200138004040c415000d856034801804045260f80d07051042c102d2003040c0d408089503580c2000c070030200303c41038548502e0565000b041400403d0740c01a1510308041d098061058440c80d15080a4444889440c060344030180700040c0c01c151030034101c600e0103c041d0326000400c0040d890f9105195511010765600340d1550004c09118036046c85500100310640000d015030b400c0449045005185030800700c070514060340e03442d006104403404118070200410661a003400640105804507000c0d101c081d098980c0343d00700018000b900e134003440d10031a081401400400c8201c0d40c5070745003001001d48007812030000e82514046035440700b075030b2100d8107000d410a598502c0e60746043c0c0208a000c480c6142100c0e580 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 161850647 1250 161849397 161849417
    0xa0c11030f160503060a0506220b030304090207061409030f09030c1201061703030c040501080a1d0f0d1e0305060d0611030106121802060a050903030c030c151e0403 72
    0x70041c80489071481c030304000340030001e042004040c10010001d0141e80303ca46040f0801100383c0e02c42101500d5211103101409030104100b41d440c0c003504520480742e400d84400580011415803030350040c0707031881c02240208141c2c1c0300225054070014080d100408603a2080c4081c00c0c6e5090780304010044000002d0490340581c004002182c00680c8492104010365911003040020003c4141c176a61100c22400140d46540b8040340194000e000b50f0003101c0c108010000010b03518461b03580010541d45003071301e9204101020480b11552040d100305007500340d00031252410f02c0c0c00d01450240020150130500383d000f80e100b005c0118010000201040c0c0d010110030400004140c070f81c40b82c2e00748000c00700043c5940b90304101e000741003e0085034968014500d864948002641100840c01c989941255140e03a035100c0701c80211010700440307020940c035010004045d007000000200401041c0c40003004d60f01d6030121001e03100706081c1c080701e22100100c0110305101d4041e20101c4100e41c050301c6030420314410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 161851897 1250 161850647 161850673
    0x80630010608030705331803070c0303030c020109080d15030b0406020a030c08090627030c16051c110409080315090603013c090c1a0a0c1103 62
    0x500c580d0352141c0b10541001405030140304090114112418070032140041c100701c80701903038410411010101c0140e041c19008259170465401d42d090b002d50b481d40031642c54a1a81c04c2c4403007a1042440304402191a0484280a0600600502541640140f201400c0800000b02e680181030200020143d04000c29800b2000880303103a40b281c019070141d9801a120359003050090101c030400c4042c402800300000401c100342030000740b01c0d40d00600240742c5098902c540c60400c00208008001c0032624000414002d021000010780350258680b15000400229942c0e41406064440024008110405680b5540200d1a0401039190511000d040020444200d84810a494000740da14091481340260a0041451702000c141c0d00a80c00310020409070f00782000540c260101c025014030300c1b01600310002a018211a0352141000124600744070542d04c5140485225650b8010817082e42d019040b02030803406a10190303080411140c44110742480161038a08215070300720b04141d40b501c505c400802e00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 161853147 1250 161851897 161851901
    0x1008100e0705150c210702040c0e10030c1b0f020d0318030b04030f02120301050f060d020d0204051005070209060d141c02010f020315010c02030f0106080303010f0608063001 76
    0x5554040034103e81c413031002c00822801d0488802d01c0040103098541000069024507040fa00c4155044900244000e0010420b482580e001080e05a20501c03248907070b56900d4054004c1403058006d13a4900f04002c100344801002000c18080c080c0c00d9012141d1202d006042a0307801c1529207000b801c118a040e5014041801514925001100e0004505d0280300030960449040b07114900c00340003070400040040107100349030105120310f600c00d207091400d4807a2600c540b41124040301e40c0000c1996200710300200c1b80080d512a00c203003402000c181c4414880749218105031039a461340100411150b03254042000340703d0151620a85950281000c42c01c0c41410400c5880b0700c2a601d00595218445c180c05d02070708440401c8101d07111a8010410030181401c85181c10880404c00d0802450031049800468580f001c0404000003035840d1140c003040c1107500201843c1200c038161540300c3d034103855003400c1710f00240c15100580c200f04004040c8042e4050007001caa1a001d2070303c005078018066101b40ea007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 161854397 1250 161853147 161853169
    0x30415020307110105070b0a1a060315011103041802090f030a060b0901050103090c0b03070203190801030b07090b0d11270a09020705150a061d06091008100e0705 71
    0x805030380300003406810040714146100041009003400e82c205034003030720b400c0155000180828802c541e14030700c980e02061076501c10f5102941c0a400181c50340760004264031012650740416000c95808e8017140100c00c0000100c8064510b20061015050035130b5007103a0294008034400c5c1d501250780d174110300058808004222a4500402d000b050000710881840961a4107804c001d040508110307841010440c2500b03560116008403021564903a00ca280403429030151111100302c1401402a034204281e02020301410707a03028030718810082c0c80c2c0b4402980ea0180a10a100c07001c94148a0000040610b600c25082200726845180c580010740700c60b0103070925045982076003602c42503100010360401d5540807003d040c0a04d02145030401c2d0745c80e240d0751141040e01d807086042c00580062019401508104010310554414001800260405422003902158203078080c0400c0c038001090400c1c090035450440c0c9640015102e0300c02459030300405040900b007404418801d2a00002d030a07150910111 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 161855647 1250 161854397 161854439
    0x80a14090a06050609101a090a08060a0501051905010309031224050301060506160c0b04030c0602013605012417030304080d0b0d060c031a010305010f0303110304 71
    0x68007858038080c03040b500050121030256060780300f0000069840188601640d401000100c411f91000ca80c2d084e00b03216008100350400e01031000022921070000d8414010400800f05126980e05c820500c4851402c0084000c18104048000c1001d54007a41c8540c00c200d00a240142148001190100607a04014075a01000031101106001508804a01e0002d010201c0090114a14100c00140c82c0c0c0a04660020000d0300015a1410807499605440040c003d0384001da880350b55a04140380500c1444c4610390140d420044c00c08598140ea221810984424550f083c940464240000e4460009020210f40da1343d40c0700c11049040d240c60300841240128510045502414901189040141480040c001d9441402844001403040043e203c1a4032242c0740003a1301c4030014001041c030314903e84040c0245180903071001c5a80c0d40341d00400c0242c1d000b0f480a0302c407503600d180110300702c0d5424424108410ba00002c02e200003813240d01d406580c1215201128100394503000c1100c40400011000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 161856897 1250 161855647 161855653
    0x60a03093e0117040c060f0e060711060d0c050306041103100303030203090a0c091b05040303140304030e040e1015050a150315140a0b0f09010c150246080a1409 70
    0x200900c1d42d07c00300d40c8004210900e0041c0c420381e800d030042201400781c03032401003040c104508078001c541c940c2426541d071005041d0003800801181807024015a00685803c0d00950511000c4165071105004481c0208200681101c4c80c03890740c0c07811002904050550401c5014a0201c18040b0741004840c2d0090081070100050b0740141e051810342400306d50040200b071003014801080401e800c0341465030401111000243d50b9130702c502d401c60350a000c1703031360159029140003c0010100c0d000510740452503140b020030046030300d00d50146011441c043c441c40307500c0703601c0b92414000914030f03196840e8204c0050401180300011681450b0100703010340c1104c142d20b001c80591245a15227010100028090010118500020340d01214407131300c6082d034400d0601c02e00c5100f1604000800070b40340049911401c0c11521020000c0c641030b602418031007411142d54820344082c003c0d01081160309486428840300325180003024000307444015008041d081120303600c1441c2710019104411203440340d0802005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 161858147 1250 161856897 161856899
    0xe01060f17010606020105061c02011202071104050601050913090212010504030203070b060a060e0f19080f010b0301023a0c0f020609010b0a170c060a03093e0117040c 73
    0x10303007400c440f4190320100c00c5a041c94103200864483c4020210901c0c000c1e80707000309910050005071141542030810740b03400d40c40042d1202c140200c49142da01d00700710455003072080e40c540b070b801107a00f40611031141e50310008000d0040d1080c4d003568444084103102504030040180c80103078950859008a600f0360150f04009074000c10051a8001c03035a0001c3c00700c40d100c800d2400d01c03500402070960104218010000e10411260669480102041c3c46400072150301a144e144c0e0282516040300d2526003900e507081c86525900c40c901030095603000024007040e005400560316541c04c00341c0b00e003121008225000c3c100b1490302d89117401a860148040d494503403d004070400b0003460200c004142e0105030349021240080c1c1d0759a0b903588000ca0303004c035501e58031451404900ba402d103032002541680c8080000f0718065400d03016042011440c0c0a00204510300c20980e00741554650400d10940558035010300c240c81071107251003142c400007010f150900070343c100030005400042c01964181d480d0191100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 161859397 1250 161858147 161858189
    0x20309090c041508060d0203011505100309110402070201200106060801050d0309060f17040c0509070206100b0d06080316110402090319140610030b13050d030e01060f 73
    0x410907030801d5a4244480c5403503d000d0f42c000907020404980c000704107a107400b048041e0341d4944607801c0c0e260004d0080198100e90080b50082e5040e40c0f090358003942c101a5000c10710b500030710456040c581c00c072440401102600040000a51202808074140000c0c691981800310080d480d501c200081a00005003c80c00c0c0000079248000503403100c1c0c810a41e281420000a90090109048078910300b1302449152071480141c07a10004d4000d407000c03400c0071008010601c04c0e108001c908484094401f00c456803140b0700202e07254081140c10030f801d00d001507010000112a080101400040384070006105615003030502c0c00c5512241402c070380c00804500c010140032801004c0c007440b54044404618004044c0c0210782c407600b6181002580d580c00341101802e02950401c0e500058103508261152407400d0340c003c0c0c103200c01d980020758201107010700040003002405414000103802c00000c2c501c0000000702100a0b0500c50b00720701b1655225800080d01c0084203168902510088085008487c841c02d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 161860647 1250 161859397 161859409
    0x602010b030709020c031801051c27120f090f080109050705010305062d0409030807110c010c02060c100c0302090906040203220f05030d020306010e0d0302061909080406020309 77
    0x70700140c1c070040c410002d40e100d03e02c001044442245880f50901c0721f05845500584250140d8007174242c0c666800f45034006d610410b82e02a401c1d20030842c4000c045902d01543e004622600b0650007407248000d0201050130724090405628200d00380e1614582e4a0346a4200d072007100d905610000f036580d107491251040140610030752001c0c002c03c2c45c0070406440c25200054052105419090000c040044400040110380d500508400d40240003030009146605e802440514100c42490000340c59030740d4201c01040c0829880c0c0c580130140d48a00c4e800c805902007244503440200458050f00c030b40d080040320001c02d03010b5101900c2107500c0058652900703200340840c4010051015204910400c2000b10700c03c400c052131061140d2039072184003a00d007145041e07000760020101c0940184408101e180010511743c004501c641c400780d94403480c0b07000312801d014902804150040250700b103180060702604070001118600743c0ca09901103100881d40e1200d5081d43d006810000060700001a1007805040076 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 161861897 1250 161860647 161860649
    0x15053102031c1e05040603021e0f130801050c1c15030b0115021501090207140109060902040b0303030601120209031905030c010b060310090b0a0504140a0f0902180c12010602010b0307 80
    0x107580c4043d480700c0081000740540b080b0300414040c50340c04a031021030204400d09404103c10210303030361692070383d095103d4000f0741c00106003c1c3c0003041d101408511701d02e043c081c0d240103614040d2200e0620104a1300c40b02c08004030204d03500803c0da1102c00d25104006e213441d500045000c0c0b0f80c102c1d0a075042c500c50340030161031120000259880442d19520002180010b14119030011380f0044c0c03100e44900d00f1084089034113000c100b141d030a02222009100d016801901098400c680821000c0700303041c289071b00da00040745c446010501e1f1034052950389031541c0082c10240c0c0c000701903491195156098401c40c110700402607402d5031012071230766480a02403240c4440070390304840c00c40c150310780100e400e651024a40903950003a6143c1d81d1040c4691144030300d4101802c0c004005001c8040c8504148a200c4070803500101e4040c10880001040c01040c45100755680e0007501640034401c1c5c8030070440c4200d030050216030610b90300f00300561040b03121a2503036010707001690000c10101c09200402d031030032044d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 161863147 1250 161861897 161861927
    0x120a06060f0f080609070323061804080a080c0c07030f020907020a02030d03110d060617071803020405130204051003050705060405090106120605100c15053102031c 72
    0x102c03035070303150700c64020120380d500c40000c603142c0e80c02e41d56554044000d4002c00c449207080d804018968001c03c5a40308106104050035250101d1645174282c103091040015a005000c2d40c10810244e204d0b5440b4040b4164032801c101086403401d6840c0380c85516280c0780790700c19202074a444064904624000813000d0300b20002d03100402e8a40c0b408d40000342c4812032401900d080c107540f940d94030301d00e42a01050740e07a12035107041e00304540c594a0740090303d158084000c600c45800c1060000792813500070001030701c0c511105081415443d04580c00c2c0802080d014094402d6080760f008400c0040e500e600440d4410000130454003151031442c5049850900b550700000d1080c0c00a00050025858541003d81103503150f00c1e100300080c802d00c0417a0300900140d0490740d00101c03010082e4061a42121041954070702c915203902000d0255071141d404c4503016903036584507102580c02111096403001600f8813401079120b0421a413042940001d14240a450039040171444601c407615007660059420b080b403401c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 161864397 1250 161863147 161863157
    0x902090603030a14070510050c1902010c1e051204030509180403050304060515150c0d080112061e020d060e01090b010f200a060f051b07060b06120a06060f 68
    0xc0c440102402c004100b42c3e40344a840c0d03000c500c0909002c1c6c204542c0200c01a070780313000c000c0e6040c40c3d540c90f03403664850f0022a101800c08a640d0103041d205110b804881c2442d6130311800394040c00b0740203030040028064034000700301080c084920303071003000310066005620070784601d0755442c400018446200324400d80190500201010040840d4000084039409070b0321500c006142d0740d8501c0b003481500307d00840b50780c100c2c1070801c24140206091001301401c1050038101d0341041e084403400c940c1d00d01b0901035850032240d0720038201d000640a8012104840c8603032510030411550760141c50482c1c2010607100b001c1915182e00300800d1910a003042d024003500740c030501c0754840d88000030300000700d554803850070040d036181c0c8144c0300c4507044451030f01c3c074004000781c80c20540b081c14600090551590490740e1545000081044102500030360354425104c501664241841034a9000044c070700c50020540000f0100b0000450500c0d0100701d81c85020100340000d10f450806100800c4a004000c070001031203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 161865647 1250 161864397 161864407
    0x60b0307021009140f060907080c0a0306020d110304060603120801120b040804050d110301050121080a0521040c210809040b030304080d020f01020f030a0528090209060303 75
    0x55070114403505222508076011402c284a49882404c41000c256881c003a070090b03580341c11110401144c01170150a004040f2121140c032407401d41c0d01c2e26056007943d40d100d8100700041001484070303000741051041201000462200301d10901b09a548101e034110b0711a540e900c402c2c42008455900004607118514150740c85604004200241081a1101400f4175031400002003c000e40042181c026180c05130402d0403018280c50311031050032044040d00e219500f01000840e019203c0c020f040d0301411444460050a00307103444074900c55200c0e140d92020810104181000b8102a41030307104030b5213452110f203041c0c2c036150515030550b00003900260302c02000c1100d591030502e8142800701d00359811441180e515003070280010020f01c409500c1c40e401d4080802c000400110106025414034034903025610f0075141140c0107800c030b10850042281c2150b050020410000490b445941d00c90000c2e001004d054010199006d644031100b410308074141c0d201c140e66003c60a107600b00c190400705c250002c40c102 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 161866897 1250 161865647 161865661
    0xd0c231621201e0a090e0d080901180b04140a170a030f0504050a0b0702060907090c020a050f010f0b04060e01030b0709030f0506041205070b0609070207030c18060b03 73
    0x384035000180540e4201508080316070350016600400b280e00400030b15650444818041001800a43c0b040c440c000c0b40f48001342650480c01111901c5071800040e0010803042401a582c03440c014081c11102c5d03503070ba1000e101017014000411803050240c0440400c1d454103207018501d42e62440300030f0104d40c00814504000498651001d407072005002000c80e210059070701d04400510042c0e100f0740e09207042100f804140000860955099405043c403541c941d41e407840d080e49d0303d08064601000236031004034204007002c002d030b002c84c66088013031040d40e0908184d07495580c40c20403000000c1025035903030210141965031031702c00e0600c1d02c4400d0743c5c14404a45403000c109214181440b001c1c007601c03c01400a141d16202d1615030000d10b41c4442c883c409100f050500658035a02180c048075030100403031070701c02203038081c0e41610034495000c0029000d50340c0307031011301191a40241207202944691440070001801d4001c00c0e5015090040942034080c542d807241c0825a03940380d0040c204204200240068 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 161868147 1250 161866897 161866949
    0x10f180c050405150a170d080c04050402030c070b040c050102010e0a03051806190f080604050c0d0c1b0303090b1008030301060c02030304090e060f090f0d0c2316 71
    0x44410071500003509982e080c0f0482c003900a45021303030784e10003943c400c08920340c2030302d50141c54515020012aa00c0203034000b01691040c400b0741d5000d00e981c109100400c10340c5015001103a00110250f0240c0c101a199500d00a4814043d00c2c200c400c4040c4400910030307941c0c24890210222075001c010705062421b81c030041c002d840765101c0c1a1285030000c03041d80c0c494071060100c0c0d40ba603044940c0300300c0b40100c210008007404000948440000e20701e001140307182c07805015190150507103201d040d1400403d5000900101940c0c9071000c14841804004410124404140c48165000c0c0d10f020030107401e1403130001516030300206180e40340c000c00c14007441a034400001740e03415a000c0307041c0381c5469100d0b400000c0c514009d035444401600d0600398220b00c401c101040d0385001d8121600c0700d0405448800c0b540c0e4540c0e800040200c0550700415400f00c441c1d1044400152150150b0003044500c40c0c4a04120380c1520a00c1c903032070b2a41d200b5020940ea00c0c04d1004010001c0110702c080f81d013260500c07803c1c111 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 161869397 1250 161868147 161868149
    0x203130b0a060b040303090612050601140306030705090907061709070303140c060a020421030e060a0915030b01080f06010f0e032b0e0a1a0304050703060e010f180c 72
    0x1003200c09500014203018034560081c07000d450011041900c407540c914009083c001c5a0103003000203195400400d516520a010340e500560b016101c0790a5101906103868181e04011305051340342c455640000780300d1302c50300785982c003a40c80000680600d6041640280203441d00048070000309400d074040160195000c140901500d60500c5c1288400e5014019a4028041c83d100c0400c4c40c01032a0034082e0006150340184212060120b5001c03a810f440584200e075103610007009070101d40306c103041c09994509900185030f51000c034203112141c2502ca810b24a00000c10f20303514000701c3e42d0b07200300350103030340c0c00c10141548113811400701c54035490140002841c07010108921070600600c2c1980400d240d600313000c1c1140484480c0c201c81214401210710000038607100c100080400d0404220154a0410442c4007023a145059410a03004102410b505103c2e800100141c9990040c031002000241050080b0808001d1030f80001c1101499000310000300c0b0050a441411540e80b00d274846d000070844407050b0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 161870503 1106 161869397 161869403
    0x203070c0506131d07030c0203070b19021606021e13090507030902040203090c010e060c03190e090907030b0a0e0a060c050d0c050721020604150605041a0301050604020313 75
    0x80d0b12407190030b032b01400268140000a01d490394260301c189265441d81c20061900e006c810103d0310baa42c2c4003504648590b00000c040c54090968524003080103211040240b07400e03c0c41659440c400400c0c0b04681441c0c1e2101300050101c0c0c02a841380c05e520350054419556480d0407039500d40c80709030440d00a80421820194068a41400c00544610040c604000c40c0f4004440740121b029401d40c02000c001c2224901000c0c0702c61300d440b850b203405040c0300320040901600b90b14010300c11010040407039080a01d030030625248070310001420142a900b0882c0011503105180b0200c07031520070800040030040c100002c2040b81365015001340305860203106800401110068109031004070020364000507030042011902203000b1410012508440d108001122076880000c0340c180c440c2600120714080c0d040070030000758203083c010942d01c444100c0b811880c515000c030383c4140407a80d4160203 = true := by decide +kernel

theorem cover : BRFrame.Cov 161690647 161870503 := by
  have h0 := BRFrame.cov_init 161690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 161690647 ≤ n) (h2 : n < 161870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
