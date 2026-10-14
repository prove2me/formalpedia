-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3656
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:17:58.982273+00:00
-- url     : https://prove2.me/submissions/87fb0f28-770a-4116-a978-b671acc7c62c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 657374100 ≤ n < 657553956 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 657375350 1250 657374100 657374129
    0x204140106320f071403070201140a02010209090a15091b080612060c0406110f0d0e040207060f1b02030c07441b0603060616020d030315 60
    0xc1c4014080b482c41c0d5000b611440d095400d0720000d5034160200d60b8400450507416403a00b0032220f28000f81d070300c0683d054071010350801c01a1500100403003107600c1d09a0503100d2440740d01d40e00c0780350009900041c401c0e9065540c00e00668299480312541540309003c460f50000f20010701102d443d000b00c0c1c141d009581e200d4a02480000400801d01c1c0d506080c1504c4d0a00706455920000024209180a80311040c035000340790900c008103103076201a100f0341c0c5050303d4008128040c811020b039109840794283e0801d074003144942c0c0703645000e9151020825000b4002619084d890b8030b850f0156940c802040c4003503640c81f00c01681c2203020040704034a0a1035440030354070700008100050354034400ca004400348039145011106500103118210f000020b400ca42c1000600e8045d030341841021401c1c0c41d417010a0040b83c440443c00081c41078041f011724030083c8002e0558945505001d410341003a4400c0003031071010a000e00c05640e035030000c1840c2d14840d51b404901302c508500040c8200c80d02d0341c0319a2482d180c04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 657376600 1250 657375350 657375359
    0x2011d031e090d15020a1e0503240d05030408010b040203090a150902040903020c01080f07051c0906050c13140d08070c090c020304091407081303020a021008010302041401 75
    0x19a03078600ca01206080300d92202c1c15600010250001c40500400c6450103000c04c840000082e0042c2003070b541551501003d1400310700c03c1ca0602c00840d4010800504100005400d100c81c5440041900d80d01d080404854407420b004901400603201040c0c41030350002c01c080029103400d000d40c66030035031705581c01c0d410350074040c1d601c2d036817440444002003820200c401d9a4044021b140d0040e18402c2d0020010300c601c55403820040d485080c50220a400541d01d80f000031442440022301c3e90240740c0d65070310307140b804a0742201102c1c101c0214403000c81c0b40d40c5618141c00401c915016190007540007101d5203035039481d00c03415081d4000d240c3c0e2050800c00e1502500c010b141c0e070340e16500080b65400c00300d81c2d541c1e04100c0c07401d04c10003400c80c0c020846031740c9800d51031007410360300001610981e84140000c00465070105d000e8854444100e0720140056502800074080100c0f5543c140e4409210b0700480c1c0403c80c8a900142805600304c484400040f096401041036251500941e4a801000c3c0100e841c00d5041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 657377850 1250 657376600 657376627
    0xc070e090a0c0608040305070b010e1510093b0916030c061b02030607020304080c0306131403070804150306060507031d0607020a0b1908010803271002011d03 69
    0x2d6100b00d01c2800083c40c0043d05050052007121140c0360703c490604603546e111003100c04a00030a590407170301381c0001c10f10f170b1081c0c0c102a0229003410429454000c6c8151408002403078001140c00c182903150121500c81c601d46032070418040b240d18110002c111940350040d041403a015029000800049003100104040745c00300c003284040c2c40743c903e050202c6141311581d6040740040008000e41520074801004129030303020024000b9942c040095070964881d2200701642e615096805440c049400c07110702000542a00c41541d0704d41000050302c4c10b01c88142c451500300c0d0460340c041d0007401402c1c0c0c0c007980c07a04c4d03140c82104c003d0111801c0060800b60300d520000e120080d464076507040d00b8034010799420241e6502041d01d441503801850341c0d912548843c1c1e00104d41e08503500680f240703551008821120342c090011035044c5c1c0c810310001e505000350301004040c0b4281c01c040668158111210842958641003a5176143c0c2e10b840d0004102c0800d070b040a4003004a40d011044001d400500801d40032032207 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 657379100 1250 657377850 657377873
    0x906090c062d09030316020301060902070203030f0706110301031a0c0708030610091a040e1302011b020418050a1218030201030902040605300601051305100503030c070e090a 76
    0x21141003031403142e110004003074514454205250f525100110b03030000404010714489102c14400e40090022503a10220801603004805001b5450341080c0710380704550701c045010348003040c040e85000c1840880c40b81c100c40b00e58402c0e0001c1e03e0111040b441e14102c01b0500320480c0d000f400941c0b81c6c4d840c2c01c25070340780c0721034034000500b105110310969225040840d101b513030481c01415030300004e500c4820468409110036802449804140c018510004440403c0c50301c58040341e58042e1103001102d0340e011004550350010010881c0c0c0159158000d01124070050301602403a0300c14001820003210714202540c420021100784410441100100302081140c01503c2c4101c07542800e001c42c030200140300280280c00d0340e0304155046040341c40e141d0300c07904502c2840c0d5410803224208148207004281c0701034882c82c1c24020260484074080c064000f14003690b012662104242c00308406054403280001d086034400e8158600c6076005400601c502c8161f00c602d650000b2516004000410b5190750304a010720 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 657380350 1250 657379100 657379147
    0xf060f1703122a21061305090106140604050d0b180a030e090a0603050c060a0504030605090a210203092b0b3408071806050711010c0b0c0f0c03030906090c06 69
    0x10624003c2819030f2204051030800340d486d50710a0085140003d00c0d5030003015184283c0083c0440791407199400c2c14894129410303901c02a0003821901f8030303038032545841400074100d011140c0781d5541860303401348244500d07140e891281e9120800c08408004128005a02400b40340d80c00749080002c1001440000e2008100f12065604a4a500c85d540003941e2038000c0c4d60020301200d042c0400c0120702c00011540d040b407540720381214009498168416900f140b201e00080000d40e0007000440c0640c548000310001210315429003500d0410f000380030300070600f03007010210384c1502d40100303104020300b110489403245410802c071600d00e00440c0403849080d02080020f502480184d10208503601d10680c110310b200d9001400f8940c103e80ea4080003000395100e0b210980352900d00102d050850742c45005460000c40d00190600320944400000108990025941c1c80164400b084212140c1005001440c4030304000e40142049107801008039007051710170300201748a06020403003111201c4040c1051141030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 657381600 1250 657380350 657380407
    0x6031a091005070c1a010302032a0409060f0f0f05090a051b03031608130609081f1b08010806100515090409081c0f060f1703122a 57
    0x10303143c41d9415242a0248000a0032640850b40e10f40100560301a00c141200c0c805d4080302c501c0c19810452000c42d8110740300d0601074038003042280310949442d0704070745c0c01075009140c00168460110107886c00c507507030340109609490300c1d8403049070341d0107152165585c01565800036144002741561000c1d261440e080b03410000c0c0d1400000c50905480070030a586025502040e2040d21040a061100c000d0300003150100e8800c0c1c8100d0701050581c8100d905404035980030740101001c88038191104001c40900042c03030806c9969201200c21801c2e001d510140c801d03801d4170341d101e50794104803e8908280b0014491032640c141c1140412241d151004800703018400110034544841c0d51400003406008844070140c121a00410b5101c0c0d500104800f40e01e00000102040115602c0000d81c0d178140c505510906480360141c4c0c00c2002425001054a280c4821410649e1f1400300d03c5048101c40403001e68201a0440e4400c4194402c0d07460508900b1903080b00c3c2c0ca21600b0b04d009072454100342c401044155822 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 657382850 1250 657381600 657381611
    0x80a0506370e0103050a060c03020405010e130f0519060803090906010c0f0213052521060806010f08060c0f030105040e1f0c170105030304090b060c0304030606031a0910 74
    0x100000781240038042c000c5010700c01d5407075a5a00301241e64200d03203001510a00d140001007000711340248211030450364180c50700c100b020502c004120b40310b03d4810610b41c00c140c56a06680d14080300c1d03c03540c0e11400050000c0b21082c0e41c020403c20881d0b155400008455108021106003941d80c00da104e6030101091038800e2071003c3d28034042030400f841020007508901d00328128009161035801031071050509044040003800b40052405440110420400c003003808408107008507484803444080700007407660040b9815540385040391410400360b008403d95400d090080c45544824000d664008403c0704146007002e02c6500c2100403171206100b0f062085a494901c40e4940c0340a028504002100041124000ba00610310801500c01c440703620000072038550048204034145060030781a0b070f8001c3c0c019070526080c60041001070524609455203c8814440762129072010402400a94800c88010800500e580b030480403c85400c084082581580402c000400000280d11001c0d040c1d05140400d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 657384100 1250 657382850 657382939
    0x61101050c0415120f06030204051f0b0c0102160804151d1c06090b06030601060201060608060f120304060c050c0409081615090506010806090309030604030c03140a080a0506 76
    0x1902c51900107540801400c01c5c0490b81c4c816500d6002a08480c0282c6082c401c96a8280d500d003549080c12140c000d940400141c2841031ba0305440140180081400c0018940700d1045800d00101d50000e0080316403400004080c016004c03400c0311034090b000c0d03505014103000300401d00d1600381140d02561710b00801858140c000600d5595030070b6070b091038120808103c000c0782d6080c200c0300c1d00ca040710054000c0c400c00380001401c61051084208644d280e941c0c880c1141c031140100813091201100055108504000710004c60505100074401040a40c0301d07684105920304d411070074194030303d0680f480b6600e03107068400410110030031a44403040c00607031101e1109042c9007224446640c85d40d440ad54a00c1c20405404002c1c0014800e410f0300c0b40d1000300c980c2541c13050703583c0d0b41c1e0b0300c5080d0303401e50150070540100740064003600000b0907403442401c0c805543d03400d240150019422540006c40000d09806c01d1008440301441525080361060300c944030f03080c408040f4a80a96851000207115901c131564444 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 657385350 1250 657384100 657384107
    0x1e140d0f03050d09060609090c0e16030e01090b090604030801290c0f1b0405060d030905090705040b0706090204051503062e0801090314031b0f070f0b01061101050c0415 74
    0x2000151711000401490745c0301c031442d00060031400003c0b180d021101c600440d095400c0307002c036440351040d054865003203040c80408401034016407401c4640c543d01d0398001c40c009801c880d0003510500c100c00007041c1e6860a418010702e11a01030380300c0454502603001940c0c80000e00144001041010344180780d64104011140d840d02801c0c54490030a80075071103514100304e480c41c0200c0e40c0c19800b203c0038840c1380c46110410110940543e0002d01140c900e01c820069403c028031860f0340034049080c21f40c181696922113480540c0400e004540b0603560f0042d003000c40c80c05d0311800c1d400c91380c0003607205e014281c901c0103c0e40d90301000e880040703442c0715100025241e0821000034803403030365055461900c0664445642d80603142c2210b0890105010305c06021007080f601c01600d210b80f200c070407145044140002041c2c429400b075050201206401c214003408130710044008141580f1a01842a5540c908100140510f001d07440104180c1d04100922454031107034020b45043d215910701c0361003801413103841a03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 657386600 1250 657385350 657385361
    0x12150301090b060310060810090c0306061415031e18070e0f01170a0209060d06020c160501020a0c090b01050c1f05010b0c06130303061e140d0f03050d 66
    0x55415820040501c08210480c10554082c0000360100d40fa000d0150303610b0b000346c8155008103145c5070300c079154007080b40c445900b10240041c0101418001c1c42e86907110300013540c800d40c00058461580000004075801e00780d0500040704030009045041d42002007034416841f981c030898245800900020030508803008200c02104007480045480342c958400c2403000c0c0400403200321225844c440000607189071050815510300502c08040c20f150b4050b9820400303031540191005401c20703410a91100012510300c020030f0b10160b200018201c201580045d85091940d58000c581103400860b00b0790700040c07074107003200c040e1482400045117000c1140b0040703e0324003c081105c1c10070702c5019100082020a00e4810810070059036052005a0f02c0300001e00c864401c03c00d600008d41e00510001d02d816030030007003050005100c0e160226219965240d268854042c4000507110941003100812506035400001800e0500c00d03503001c4900e13025030b103482080303060509003c0d052240c00100104080c5569000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 657387850 1250 657386600 657386641
    0x503150613080a061401081002031f0b09030606042c0a02040c0f02070b04120303020901140d020c07091a01110f010203010905060f2b02150d0222080312 67
    0x200003001d680d5100903551911184002d40c1c4140c40c00804050021700800500c0c1a105040b0040403e842401c0c9414029400181041501c0c0088144a443c25400300c20400080c1a4021300c0c07501d0310391013401c00d81051400780c4040e204034903003034844100564000500440c081400c084113200c5203028921400c04051980c005d500c01e1510100c004180d03000b00300e80c1d5500c0e030343d5801c40310070503190a170501c60362080d8080d00e81158505080b20000a1180d0000d124180042c50b02500c1402200405030075034010110041495402140c2c60121407020001c0c2c0e00140180102171004d00c000600d80c5445401c1d00b05914108074001d5209484102d00b00701000310091039000071076903581d40d8101c0100900c01983c603a8800c0d58101e840c155a45408025010155954048038803502c00c9061040100702070a03504036003001c0e81000742000b2000034400b82482c00245070b0090303500c2d030700b076083c4d40d61541b800030340c04207e148040c005000c255800020365590a440241c00d6115860b101c01020040c40c50845 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 657389100 1250 657387850 657387877
    0xe01030b030703020d0f0b0a09050c10110d0519031b052109010609111819090f0c02010c0c03020c01030504030905030a0501060311010e010c080306220203010f0b0a05031506 76
    0x83c1101b00441c038180081d015005102803805500c0e01c404117010f8801c14807016299901040342d00106141944034940351041c14240804a610340c84045402e01503e0b204080211718046840240b0341c0883ca03800490f1403191804001d4060b8284415141803100d15000c0200940491a0184100300c100c0c03141ca614180c3c440721a1502d04507428501924290041464050034145d03c00032810f88081507030a0725030701e082104111103058040c07080302034100c040f00d2105030300004006910003092141e202c40100203c0e010960007142d92000e030071340d44124094400c00052a1202012075804601c00c40c1040c003d18020483d500d55050441b05d10843da04074980c140690303c16401003000540c803410403644501050b10b00c04081000640c1c010700704054141c0807400c440030b00707000150b1000c0190b82c842001485020200c0d038070f0f0800b1042d50300a00c9089801640000140121010300304d441008000b44c00c100f901c0c0c0782c2c1e00d0400400e640400b070700101e01d0210b00540c00d11540c3d075001c280c0d43c0d408105007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 657390350 1250 657389100 657389119
    0x2102031806090c040c0503130f051905150618011e0b04060f1409060d0e01110a1809051501050c012901270314011b08070305090705010e01030b03070302 67
    0x2806161581c6400c510203200d5031170610ba201d04140645c0540f4400d01a2141c84441000c581c4c85030740080b0441d035000c41799809000388801480c55036441003807116004100a20111071503500c03610113084040c040e11302c40c0c440340d05201100b08c0c02c56403160564283d02d41e0440400e403070a81c045131004441e040070f800680040b50200c0c0095000b071035040d2144d038540d20300c04400460400002c00340b060038541c9810070010001c083d910030781a0429548807040700300004035501480c84c145004e0b00814501400210001e1400d460182d11450720f00140c1f12400c002c01460510805040c001c00a8040d00c83c107120012400e1400d1100a40c051504207121950094003602c014030140842007040b140079002c14942c82908058864110081ca5102030320040c51511606507180c0c4400c0c2d40c40c6900c96071b229909c4003c548020943c44850f0044a9110380340d035100ea0501c0c1c4005030540ba8010900300c0e199001709420840e5a0f480804110801b500b0700740010403035035010101e4148103154002035040b40901 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 657391600 1250 657390350 657390361
    0xa02130b150a0215190207050307020406030606030311120d1a04060305100f09080a21020d0b0405090309011e17010f1502060103050a080f07051e060105012102031806 73
    0x9000a011004a0b5400d80303013410569607512070072070341c15103482c0c20500e480d44007200c0f0741c0300950007410914003500449090100640c0003074241d40450300304403074032910342c0e000700101604030b0794079030703441580c2c001074483c0c2509421102414001c00001041068440d46c207180c40020741980072120001c054000e01c00c03103481c7d0921a946050000880d48060f00e00a5501d054203082d229582d515548584414548280080102d54900c408082500c0301c0316041c01000401c001880213001e0554400c0000c2014800c2000700000c5500c000d00c0040d80b60010001c0c5111a0307030180c0b0401e03108400c4c0c00c200c18500810903045400c6036940301b070144010784190003c02d0958140703660f0400c031045062545002e0200b403000320b883c0c13142071200403c1648444441c400085074140030b0068038003240307000c5040c802c2c0c0e034580500c0c064108000e00b041402c43c20000c0c04404040c4102405410203080600401840c1c80b40340316065071200940c81d4803540800440c242000485006c1c10221001c41102c0050800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 657392850 1250 657391600 657391639
    0xe0c0904140a060e0c070507090f1e06030203120903060610050c03040609030c0f0e160c0803010e07030b03030a020a02010c021c031806090b0412020414010609031109090a02130b 78
    0x41c056031a45948a0b13001502035035010040700d100652203005000c44a182081400161600b801c10406007a200d60118071820144060701c03801c403103100c1c13000c00d44c00e10f540145410400303000c0d00000e80a80400040c00d007900c0c0044d099801c4503040d03c008030391300c00c1d26104464500850b21000c00c01c0c0030008001800e654803c05a4040d24000c800d90480c0e13951300c4822215070b03038441c0300f1102407c046000042c10307440c042030b40841ea0881030400d4030714000070b552000c5080d402600400741444081c024030401552501c5990b03440d180503002549451316246029683d1b10403010001d040000d002c2d070440841d1508250f4203451500c494202402004030315010342048203268a510405010507000074210707100740c0c201c0e030441d003c00100300e14083c18044250030031003a6010585e0001c0d115000c21b46000000790b2039600078807072680d480c03004509520b010030303200580701c00c11446080349205020b03000d800495200c1c4d140394121078803c0500c4a505c4036801800402079001c1c0e001d807041080b1042d4168 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 657394100 1250 657392850 657392861
    0xa0e060406032901140f01110c03010507120c0e01020c1c080a0206040b0901020703080f04061d030c0114040b0601080405100204120b0f0403020a1514130605010f0e0c0904140a 77
    0x1d90300405140f507070700c0720301180a0000d0107000075804501c40e007450186502034010140504907140549000c5442c40d0f0202e429600c090320501d0001d0300b00d010f00005271a952007071802c0300d41c45282010b4044c4507000001d41d20501d85964600c90003060b500003210584001d00e80b08025030107000161120211a070103516000c02310f40a032030910710f120000d0300c600810b10071103c0190381074444180546562031708411440c00204100c0380160b960000b0110181d1810314004800c2c02d2400441d5a04640004075003980c400a48054100b179084040c4000109040c24840d8000b20a107806050b907502c0d41000c0d4a000000c0b11803084031480081c0c0466282c5554240b8203809025102c0c42d0320a4a60f045103450b031001c100c0b0041c0040c0c00800c0450000b50071400381c0c4400c03400444000c24103517030501002074840c0c01645c41c4a200105110303001c0c1045024000c0302d00401410046c5120b046c07070116013590511008000420207040020040c516580d10f43c00a00c030752051000307540b880e10300758548600419 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 657395350 1250 657394100 657394163
    0x12070b04030210080906011406070803040506040c0504060e0606130f1508010e04030f141b060402040e0105010612020d060e0a0506090901060503100b03073c03020a0e06040603 77
    0x440071a03044030003074051003d480c0170b800b483c4010040c0380c3c601100c0820124126815903403201082200c507003ca00d14201450045024001408031420a441d080d0091006a4080d5001c1c3d82416010080c0500c0f0781001c075440842540e54503039841260301c981c1c3c034010f191742000c110760307900b00800301d0382c0711503015110384913500307a214410b0300c1c0d88842200301c00c40803c8038002c2c0003942080b006d800f80c500c103090300c403005c440a40003d82040540e02c03080c40415003446408003e54040e80800055241ca40207146a10400720000c010035410880c005207000148203104403515000102442c4503002a844071005042076040d02c0d1903420003e42c1074000e400c0c1680c2d15803083e9031040115409003010701c502c1d8225003000f8000d06a03201d51492100250090100310345d0716002c4d07080006000312008415100021a03801c9888d08500102c150b1848010683e4259400340c42081c420300041c1c580810803400c1c1c81800e80603505540e1a60001005080590002425950554105240c0c200ca0054042925 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 657396600 1250 657395350 657395359
    0x6030b01030b060403030c03090f12050114090c10020703060c0c03021516030f181b060e13050a1803020c010f05120609070504091a0a140307090b12070b040302 70
    0x20000000460640d414510706551000302000308200003400b481041c00101d20a0a080d003030140c0d503036824a54004254003500e000fa00644000040240070302c584103c10b95150380c03d070564140018040d5070f0795805407905001c0c4440c54800e002d021b00803c62080159403101040c070880100d801e0040c40300c08024400c8015100722540d003902d008003c00c425201e01d132100b500030041c2c9103690080380030b44840c2400c00301a990342c0c1300080740c03020b501c1c0c9a4050f0714040d080c2c0014000055813001042d000542c00503040200e8080007488640c0c0b8002020400c090702d003030118180c4c40d0070008a00500c540d031b20501840c20342e098514101900410b083c231800d2001d80b14549980d100e2101030702d8911a40d0305c46010748840d100021080d18104100d80e40101c1c1340e2030041c2c10940c96449030400c5130a4211081d408810314a280a540d1a0074050341c0040c01c00000c601c441070741200e0100c0d40e00e50a80c007443d052503440e00c42402d00e9071100c2c8900e28418801e8403c803080c140c5d0350903040100741d0103404140e014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 657397850 1250 657396600 657396611
    0x70515120411180f070f1205042a1203030c03240614040807170a0b0703150501030606050306090406150e04060b010906090b0705070b04031a0f1e1009150603 69
    0x1d00c01c50203c1c40d4494071110600503400c1d60385c420102c8185600e45039440612043d8002e59a1040750b912400e48035922841003100741c1e107800c2232522414a40301e22080e0621041d01810f12040045240c42c030b016592504012034030280002c1c013540902101b4040d944610f54243d1a41c00521040740340608444203602e60b04c1e4007050307000c07420f000e9100b00d024004003603101010400030f01c0408810007051020a1056680100c0300d135031600c10030034050352800d00207900c0b140d462250205081d4000000c00f400d08040128900d0120302400600000f0000ca02c2005800001014007a40f500440d1040380b492500c042c40a80314040450b00d813009407000d60351586041c42410055001d5007045042c0c4400e500e03042031141c0341003954070403a4401002107505004c1c070b041c0000c403c450320001e000a588580c1801840c00c003401070013940140010138980c0b41007403100034003000d650000c0ca0303140c071002c0c40c0442c9800c9507201c1490111518441c2e120604c0c030392508030215000e52222440200fa076200d65800d019 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 657399100 1250 657397850 657397879
    0x304080d14071409031b131503050f03070b04060504151e0e071409191104030510091e02030a0b0403050306011404031203051302130615050408070515120411 69
    0xb4071380608401c02d038150380081c01001340b0300c2c4021948445440c00420101c4040c0300c6d85140c00540c0c0340c180e0300c49098175264500340200501031003000b401910340c000550034251140c94000402601038005040e050b9a003010800380030108401d0b40d41c1d10080381c000d1080400b21110010b440da0020b58880440d454160702c1c0d0460340003c00c01004646404010850610349501040705030803004d00744110300780c0718540080010046000da43c4056601072100c90715030780f640c01e00c5401c150015840c0045203142048050009842641014005030002040c00100095201080c5043c15044019105442d02c400304004c055202c002184100d100782d886c00211400c4c0c000a91a500a5000c000d042c101c1505190446500c04e5003c564002c2c3d42e170150404074a50b40e000710312668941140f030740541d500d49005000a0f0019094000101407074681146810f10b09250691110403a0141903c00c0013400c81481049a088003503803d000e03111b0344c202c07601c1d091074a4020498904070030382c580100350b00ca03407549 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 657400350 1250 657399100 657399137
    0xf0708220b100b030f0a0b0d060510060f0206190c0306091103040c0e010608220f120f050408032712010e0106170d08040c08031308060604020a02120304080d1407 71
    0x2c5c0100d60820100e80240c41e00b004801c09010900304064000c000706101501055103405042d000c4c090310b0384050308150a1610043c03840f400c0c0d0740000709552103d000e00002ca42035407012801c02c1040b80c00000c000f48003a034100c0c0506503e900c405001c50504101e030b00341481300030003540910320070b5280c20442c5076a11048141c105c0b0034400d01c000f00366400b0002d1030b000c8034440ca400d60150f14035aa03078100101c0d6070761701042045c802419680200100c1c00c00c80015006443d5804044560800340d0078146484e0056035a440b588000f07110100080001080ca4880191044a8406c00602c0071000d10303d2019024000d01d041108602c407582803a00c00102e0060382090074500d101101c010b4280f6402c601c0080d10307203443c01f1f1f200700c4100612450000c2c030f841c0140701418009800c5090214a240b400490b14a064800b03040d081c420340c4108034421b140c03500010742946641c2503461a80d2290385034100500c40b1b0007450441e442c0c41c0d081c161040e4114504918451050800f07448400981c070b081c02d22007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 657401600 1250 657400350 657400357
    0x13051011040f05040b131503080301030b060316051c050708010e160603110708030430020f061312090305010609090615030224090a030c15080f0708220b100b 69
    0x40e80010710304502c8006c0b003540345c220788910000031403454034190b900d94031108a5402640160740d2005003100384000e0303107030500198020620280c20402d0060906000031080400b00b91440000114500f0140c1003003c1440500c0041c07801f14000c201d22150304030380546600055095010b500050314001c98001d00920414095a40c4820820300b802c42c960344801780303540050803e54000b006444082c80194034016590303040d042c51041000c003100260400380c038144a140d510001500300300304104a06c6442c040721800c941c3c12440b83c28601820f5841910421582d07000513040d5400d110000c01e0b201c82e40d400c030700701c024030441c41040360003146601c406c082d1029000c025482503d1050009244c400d04031a6015082081170282c43e21600e0780005041c2403103540119035184443e081000f00c542684107501716010941010f80080c80c0c0b03050040d242aa0040480d03041c403e805003c61805003ca4800031205400510442c413210345a00300031045d03001c00c680500c0c800440368004900100b8403400d9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 657402850 1250 657401600 657401621
    0x10350d080103260f090d0510060914060d0602030601111203040311030705150702150a0903020c030d09030b07110d08100803250813150e0d030813051011040f0504 71
    0x455041c0710f50000040b2441d0311017026a503000d005014114081101400050079500d0507000c0002c04030700d040b00040c2554422070340f80300c00452150400026403592250242c3c2c0951048005070b6950350f440059a000340b900285541c03a100314040c58000368242801140680d0081d00e0340a80c1c0719901a00551742d10420500800541041e403502044a0240c109942c10045500540340d01400704096100800b004450b810a025203940c030020034180c0500c08001104825000b9140c2000c41003405007081d8940d2100400b54001e07140000ca00d58829408949805c003071760103035000c8c2180d09000400703102c0c0a844141c00414041c3d4001100b02d0004110760100c00c0307200b1419400d240140440244007040b84060b1150305080210030801e015580c4100041c0151400551074000c2d0003000070300310140d000c1240e00a01c51005c030440405d401640b9a0f0340041d075210801c5000041c0d207020707414a18071090304400f030741c14040c041c4802111003000d80142c40010226801c890754800400003610304000e0b5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 657404100 1250 657402850 657402923
    0x50906010e1909090f0210030204030f0b04030333140d06020d060b130f0605160f061b0c0506090102040f060c11060301120b10350d080103 61
    0x1000041402d0106103250512a8500c0c0384502c41d584050100c142c0e00400780856011412660540840c038240c1e448143c071444520b41181050b042d0350304e4250900412034050305010100000908061281c2c01800c040015048060704c102540281144000303003e90680b520088448030214545521001c011482e050081c040300003a071051700c074100207600c894901000c030354071080d0114403400500d000340340701e0b442910a1400c6c240b41a03058440384003690800d0b030400c10100041c0c40702c40c0110704500c1d0502c0c2c00510044040c4598608180282907580032154800704003998401c08a030044000c001081c02202178401940d15000405d080784182c2c001c4141c3e0440144007400000d104d4400007101c00d04c80c40002c1644142900000c5440e082640316504080d0761807183c01c01c201d007510380e5a4015001200c041c1c50b090170b0580e1000080e00f40c80d4030b1003c1098a9600c0505482810040c218080d1103409482c0c040c802440001c1410f6802d0100740d401c00385294103d07c1d0341d54040d1003050440310500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 657405350 1250 657404100 657404117
    0x1030b061e040b04060b12010f0609050607150207060e010e0705030105090d1b0c0b18010c1104020904020f1b1e060c0702010c0602030702010c0e010c0f0f0c080a03020604050705090601 81
    0x104010092243c1140c041d00f040c3e90320404035032110380324001d01421960b40c41c91549985000e204001c42c1032071b40c20010800580090410035906c0c0c1d1403c0c1d03210a548045e80560300031040d21220000d0040d040b02a040500300610111040410351043c404000c50005071810b60761a00249400d950307080c1c80d4400c03a940042c840040c098803c10000e08025a07442c0d80d208694582c0d2644040250709800103200700200042100d1401c40701507201d251000f00b800d000041186035210360407020b8203a40c0076400790382c00081e04502540e459040303541d407076000d200c5191101d000f40540718981e0821130100032244201c0c545048082c50350140401c1174911900140015078601103802d075540c100e07800490502101410b41d000060550014500c43c450b983d0000411042c680001001c0740c0c0c1d40e03203c450510145c40b009030023142c0000a1100d03165000b0040d60003000d600d151480d04201950b02c0031203680201c06400e402c0550124000b40a14000c8003203a04441d29101041001082640c506010848a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 657406600 1250 657405350 657405409
    0x3111203010e04050c0d2010080f06030106090908031b09060703111c020a051204080c210109080a09090507050702040b0d050f0705040e03040b0702060c0316060501030b06 75
    0x8180ca03030340300f4450b0040e217000704143c03030103d08103100c0002c045907075040c5038a40c1440c1c040e80361805030010408036120382c144081c10700e019110800c00383c04460048520000110151000d40082009124451080000080c9800c10130216002903d49049140710620507070300d092002d80545841c0100241003500c1d01343d05076401d480034000c0422a140c40e00440303603d06003609103442d100200280a802070040c83c2441d00c0c280d801c000d00400b407103441030414801405a1314002504031032904e029a0700c291000b00ba460101c00d50f20f047c81c80d0800a41c00c02d441d100400c10102c020f0a40c40000713465011400791102a1035086e164101c480500040e803d125401c05071030143c210302d8945501400c1c2c1c251808503519810b04007188002c55103a5684100010015170501d03110315001110300c40091030500342070141c4102c1030710400300b01901c6910080f4508407291000d01c01c4488081e040c1300e440c10140464076080c40500424401994424080b100041403401c01c640b4004142c0e41084400031007030f584 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 657407850 1250 657406600 657406619
    0x90a0c05043c11030114030f2d030703020d020d050901021f0f0504120e06131205160906030c050d020906041e050a0b090112050309010c060b0910030311120301 70
    0x7414645410303028800d1104690244501c50705040d002c03003c05403a9a0342c1080424550301e004100d21038002c1d84051262040c040003c2039068100680045101060401840003002030814901000007400006000301c201900022515141000c50f001e4406e10010241c0a40d4203000e80c00700c25001d138204800350f008a03080c004400c4603101c449200014814000040e8008450b800c440840e84080d00085450340c8031340020100040c13050488605203802c01c810950180300c078580c4502c0031041d19103980b12040200510124804122200303410700c0c0705a03209507580241040e4801030b11000204440801c0506060035580a8030703801038251101901c0f007005000050052100416405061400452103402ca5014060240345a0480440c85d42d802704200000c440040e44822840c104500c2d4041c005803002c07045d6101c401e030900b440805014103083c080060120398004c50342c010b068504000d10000c030b05050509490003540d50414036515100c00b00c1d1b5441c1001031010f6840014030040280910 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 657409100 1250 657407850 657407921
    0x1603020a0504180e06130804120812130b01230f040608010c21051605030604090c320a0902090d020d081b12070f050c09090a0c0504 58
    0x42918200b40340c0381d5a94252030103001d8205211076099100c1c0720b00405450704101080e04101c14044d00e0111001d1980c030024a40b066105030011030030a4000d00003400022030540c0c0485560500c80d041910705010041603030382c0780003402c42d88140600004500c900340d80d0840000196014030906c1010145804c100350580100b49180e40b0070b4075054040380c40302c0203014003002c010082e199031203000c00e070b80020248140050300c50035507285000d0400003040c00b103445240c2e0359619070a10541c0ca40301c60700854050260307803102600751195004c00055540f2940e10b2410200b05410f035440c5c0301c80c40c01c01040d1004002a00e075a80c003044100f814401072642d0b6000b0301030b40d0402000182c0090303480d80030410101c005881502c82050205008501501d2002e40d44200c030090400323024000000c212181d0325000e10b04025101008a01440007048402c0001c84d162a0008000e42e0300d500c0c00940380355444401e41d6040365124941c0f180040e19007028014684101a61008a0514a00003205008551 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 657410350 1250 657409100 657409117
    0x618120423040c112803080403030b0d0b01150e0148120c0c091e060b0d060f0807030201050a170405100b060711040b040b1c1109160302 60
    0x22034100300351041e90b6280714072061101262a200e010120074040c45052140d89000c0c104080d00c00b00302a10750340c1080e0040202c0c00d5050529904e252a01d04080b80141143c100181e0080884800c0d1340c18031200c0c803580e604840d010720561100351002441210a08a600c00c842d020584a85070b0504442141c0c4407603201205a03088151681c00d501e01e04010003e8181c0d1003141c08101c0403da10500402140b0091100400d090607600c00010b561414100103491191030703801a0f45255401088181480e480d404a500d6003042c801e283d15400c1c040d00f81d601c00040b1168440c80c1010014407003220301c504208075000540603041003841e41c0c005691913401300d411401040306070382e0607565200114080c90b018034040c00052100685041a650403244c4540700140f0454060000f4000103d00c132900d480200c500342c80c082903d4000030081009030081c00542e81c0d0201c00420002c250081c0c0a0301d6400c2c1034000e00108070003044550610015400544600210000382000100014060f030024000346 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 657411600 1250 657410350 657410399
    0x10031223030a0c05070f12020a150b0a06020307050c090411040f060f0503070b031b131401030609060b0702040c050c1f0f110315010903020a0e092e1503080c06181204 73
    0x40042d62b541100c0800c0c0e010070308940d542c40750b5109090030716080c0d00300030305103c1c0015450144d2584826a480c7c00000400d4420503109001400300201444006c1c0d291202820901441da03443d22041d000e400180661515020300400000b114a000500d200c100e03034580d0605481c507254070082030021240111800c085c48810480c104d10340210086510040a00c079000e40960101c4000040940b0b2540d400607400741e050490500c48036580c0c03800c840c14941e0480d000038244003001c2003a18a4000c141c0300b00d10502030001c0c42c5061882249946e01c800c041108100320040c1458403020854003a40c184040c041d80620003c0d1820882540da07540b016414100512040e0341d075400607500d0040c58011080d11061b5000f0700c0302c50a010000d040464440040a107140301030021805940b5010603c1e443c21192603000d050543d24407402618051508a0b01c0b003603888001e1301c491a6224001c0d1011601c2e40001404001d0766800442d11042d840d00300c000c920301d401c1c5441020103843c1000f0100c80d822 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 657412850 1250 657411600 657411613
    0x31515080c09030f0a050d09141207150207061205070507030810050d060e0120030a020a051201030606060210050105011718010c0809011410031223030a0c05070f1202 73
    0xc82d6410803100c13042c80800b0000f00103412035071500609082e1041011801d000380034809000310b6105107200030005900796040008210070b141c074246080700c0d03a4440d44400c584170740c085003050f6000c118442601c0c46520313403030702140024426404903442115544005601440594000707441083d02035009809000420400c83e02c41c2c002036992a20003804484850b980d400c0d01055440c203000b4101c2a91214a40c0c03c041815101180801d00c4002e086011640c2d0004500590a00807426140e581160514000f00c641e103900e0220001c0c03000f8000c0324094880c02003100c458a4050003107030306960040e96104250603010441c3e01503d039015003554803072007501c144c074a45142d00340f00c1c403805006c007aa626038160138100e04403400c4a1407008400030038161481040381580181242c1001c4940c0002c0c030202e4000c3c0002c0407941140400030f00c0038034a110304a81d5140f002c01c2000f441c00f4071000b44082100540303c0109407400d20a04000610b0743e080703494900040790307502e40c14800e0b20001c0d005480e007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 657414100 1250 657412850 657412867
    0xa0b0a0e07090c0305010612020315060f0705070b070203120f04030f1e03030b0f010507020319050a17070308060f100f03060b0f03040b0108060f0f060f0607030e01031515080c 77
    0xc0d10b10300075030000040d45d01c0004016956004a07007248255250404500c6c60070200a0659a04100300c2043e010701d40004a0b603a402d001c40e012143e000307810405952540c0d071103140001559001c80304c00ea22907c50840381c0369405048208844c0307098030f6601d5003490180fa5990301ca0b16040c80527803d840b10074a41100604000c28041c0760348070b041c0700750f400040c40301c1c6050420040100307011405040201c140020341c010b072000542050301410b004d05114017900a840c145103404c0a8410013840c41c0c400d0032541c1d00c91184007019107070b50741c882d846000e01036a17054180982e0f0501040510751048035a01c1d0428000c1c0211121804006c0074607000c0b07805600c9105940c400d5006003001080c0320000420403040c0016000315034090040c40c000361009003024800000d421002030150041080060b002c1380d220380e0361001110302c519000c4e00d601d8031a55a4100a0103a1a0003051507011a003028030100c41060410484000e50b04e2113403a000303003103180d035a045a8a2400400941c51070104110404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 657415350 1250 657414100 657414119
    0x1050909011404020415030b01090f151b080714010509010c050702060a14130303120203070816110105070806031c050d0b06091f0f180b0d140f16020a0b0a0e07 70
    0xd0b04c6c0d000765240440d9000103400010031143c443e80c0b0061410301490002e2186200103003921703406401c1480c115820b40a48401030750800c03031002c1c0081c00e14a0018420041103129a81c64120f039a106000700030641d11001140c0c02c2e140c6851403900000e8041010360018a008009400318084a1416014800d104041c1c28010341c0059018100e480008008000b007580c170900320008207040c3e1900390304604101501400b484805006151480ea000704584e900c90300c00c420301c16014244200034000f6052010303000c2e0003404181e5206000b401100001501c0d260060000c0c02c80e070a144c3e031810b00e0000b03140807960050190f524540c0d402501000602c170707241d46003d40205c04240000100d80d1800000300c015010384001080b4200380640742c800400280c0c00842c1403000c40d0710034020190b80e50072250010000304444018081080d604a050158005074907144920070f05030b00c03030500b03507010101800340da54044802d001409244034400165032941d05800804a201d108411190301a480b280c140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 657416600 1250 657415350 657415379
    0xf0c0106080705030f0111040b0903030c0a060f0b090f1f05030a0c061e050a05090409020d060902100e031c0207080706181418041103030406050309010506010509090114040204 77
    0x784065120b031000303000a140600c103201210804100822000300c0080590019025511844060000c0416000011780f020b0044032184144141130340c01000e0249040d40c002d01c042095405424580744403403120f410b00003000c07405007410b03002e81072107951550020001d5403281c0400c503464038050400010145c804001c2d4000c842e1080d05550b228608110f001001c0c1031616070345e060296140a00001001d0300407003203a030403015503d4074656408102c000304014000d4071100940141101540d6014081540d01c50350103036108079501e00b5041d41c0d500040b10071200c202d441e1a4590403906141007012044a45c65039500070500507102040e6a4030702c0241404425400b03040450010b0b14100780316a0801d441e0009807105200c0404d080c5501800f00700c0d00b01107002032000c00940c2801203001d002e8040d041e600c250070010b040300e5543da15424000e185410554402289600b003602207841980180c059881116005c0c00e1009688c0c6031100902c12201c3c2080301c40e801950820000c01c500c039441404 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 657417850 1250 657416600 657416609
    0x52a100507050d0e010503010e0901110d0b0a06030522060b0306070c0614010b070b090109050d18090e060408030a090f030c02030f01060605040510050415032301080d050f0c0106 78
    0x2030640721001c0e030810314105890343d0200010000d01c0761040d130483ea01b100589064170b00c21140e10545548080b42607004100c01c8020000c00c0c07d01007004040e08440d5009802a00426135011104070b40d1000d040e020355405803052120208142050120070000c0c0e44606800d82c01240301041103074503440424104030041c1c911000040046d80d00c0c406000700344c01103407640d0800046400c0c0c19131401d801c800080c000c4c078000a010000410100d0105070094108155681d044000e503081000d03101d20103801042c10b2000704003034560030100020080301900c2075581c801c9100c000340c2002e0380c541c0d40700c0829500040401540035a28403014010445050b0f8040180344280ca4980e0349880500403d0b00d806c2500c111014560b042100501006601400b5035003240c00030303600c4a00021200c0010b48283c0529040f0440030003240c24520000750341900032100c4d001c01440074550800f0000b000000141090107000d030740d035000408104045200384001c110890714200a80d0070300381314040f0b050a4440f154031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 657419100 1250 657417850 657417857
    0xb1e04180b03071406030a0c110718060e1509100b1911011a04050601050c0a05010b040c051213031e0c0203010f091a0c1b030a0912052a10 61
    0x40000c6050402483d0041d211826166400795040b400003011880010072a80704a500c403c940c8403402d0003082058007005140c030540c1d40e00c070749130284100049658282200510309003207000400c0d01c007000b600c60254040c0304102464654207000e10410328005861501c03940b015a000054030000c1001800704041c5046003441c01444030309000703080325018216400c13141d00d840c141c01d03044500803400074160326050720086000e0ba6810b0044c1c85030300860818006070700620450208009040d4401e408000341100c1c00c01c03002002c018219040d00417900c00d5241c80140d44045001e40300c00d00540c40ca202e1091500d20405200d0301100091411080340010204062074004c200310302e0280141c00d0b480c1c0503094200018080c0c2c4d05c0b00031651070b0001c0d50301c20007540b40003c03a001da0100012692480c00070945800d1088030504d00590785c0c1d00c00050000040c145580c045800001c0b8643d80060541000013044400e41b0006450141c2c44101000b90184520000300c924640700d101030000042101d0b107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 657420350 1250 657419100 657419111
    0xa020c060c0109110f0f04090501020f070b0105030f070f0612060513050f0c03090706140c2a010206010e011421030d06120302070b0318060f011e0b1e0418 68
    0x34180c0402c4c00c200031024401c20013128485010f454205982650803801c80740030a0001440c18110b00901c64480c450050410008045090011011080741201c40a808481034032110500068035440c0380d00071645005038400c01000300d1031148082c99429044d030346001591a0342c03480040c3c151140850000c4400c2d840720200102c0c1d04034408510f600042061004d03182d440c0c10150240c6070b8084d8060345060004105217030000c50070f034009940c19071405030100c0b50644844000c04c0510b01c80e020700c624100c03d0407228241c240d44081803090403075446e2211407a941c0d090025111004c56201340044d0807503071601185005001c691161031101d10082c1c041e60761130b80c1042c259001d40c1c009402c005039420760725000c40000399000940c442210400c0741442c0c0c40b6211100000b4001c0d80c0300714600054480d020030300c5040c007048031515048640a8880b8441c1c06403121101440b01e0943c810440007007010700101c400d01c0a1100480d01000c601014903207040e4030b43d66400349a0007140c0e03248041c181e603007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 657421600 1250 657420350 657420353
    0x212030a090308060f010e010530010305070909050604031b0611030610031a04050709030615090b03150c0c0a050708061b03191805100504031218080a020c060c0109 72
    0x10030644c2020742030701c01c000800c5003040043d0500c02c1c0c40030400d04110000505040081d0085c072040298050100081d1440018a01d0400b4140d8280001e4a5500072407500103500301041c03141700c411552100c0640490343c3c4945090758504290040c1c034980c24503d00c44107000940e02d00c00d860582410f5403c2d2502d074113111060110f0305429003254006c0c18602950960921804450302d01c400e0021100030915917a902d0003103501c03a096a000a100c075060541c0781855200c82c039000019100100c0d020800003001e401015614000d009406a0041000022a1020322001c00401c20600c1c00000c5410301199980e540c0d280000302c0e0f100601303e03003140040c0400d00381ca030302d0700740c410380b011000403401c509051030003d42c044c25035400c81038000d0752024440c10380704900c0d240c1103017a5000420b803030500d10f941542a002c0c01c0100c400b04e000850884501200c12032034401c40790026004642501c80e00c00d155214942070740010b00f09429403103013110001c80356451100402400201c1400403401e0a0113 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 657422850 1250 657421600 657421607
    0x1090b0a1805100804080a0504030203031201330305040204020c0a0605010515070b0106082d040b0a0216080d06090c050703090803120a0207060f060f0509010509010b07030c030212030a0903 83
    0x99041184140c0141038802c2c0f00c0c540c4490600c1c0c000b81c10540c607580d0380240d400159011700c22540000e4040c0004034849800700c043c400402d040310792812041102411703012945c580106505800c507207010b034030700074500050700c2540a5a8000d01c003030300051800d2a10b03101c0c82d2400300c241c1000c03100c15440300014030140c100070520041c11041d02482e00d05000650780c1da00440841400380c0c2c0104903034040054160840d01d80d41040e889c002e06c111020010020803045016807049400b41d545032081000f1800300c0c1802c0c400c507400d14501e00d16000600d51550b440c5007040d40300c141d00300d100980700c0c600418495824807500c03150361400e4491030340d40c00992038081d0000049501c4001950014014065502d444024456104070390001c0165200502d2820900802889200e141700a107030070004602c04906e00000300c19194215450702c043c1c2e90301c200300240b2075024022824141c2e018081c18000030b0154495018035882401526610f030025442041550011100481103d49980503082490b81 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 657424100 1250 657422850 657422897
    0x90503163c0810231b0f2a07090906090803150306090115030b040201020a060e011a0a0f050d021c060c030c03150303210501030503040503010e0a110f01090b0a 70
    0x444040c0304d5406041d81c9554401030741840c43e820310748000c0000f4002c8050041040d121204072449549400103a1403510645d005603100281103614450317822840d03000440c3c0300e45480c282c2402002070500301030100014000b8008115416074848d844400062400c50155100d42c03440d460081000485504051400f6000703001d0840780e03490b0400c8594441c0c0c1c0f0321a40e01c103582c0c000c40003280a840714030040380342c0021036038060556890400018640c02043d001a10100c070306007295031069a60004004104c000b41c421071200001594041200c1e040c8218403040050000304251504003a003482d1607846603a0300d004036030321950f400111480c150984224141da540078a42040780da01d940c850200c84441a002c06418020303c0c0400788c2d000005848502e1068101e20028002c43d40d6910303041e696508140a154441d50030321280030304d031220003c0c24545147c0c001c04500e01048501003400307141041e24200741d04000d07180c84003040c031a08441c010145003942e80d0314800001d659400c0990340d6075 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 657425350 1250 657424100 657424123
    0x3051c02120304120e01050c01050f01030308070f1220030903030a060f0608041112011817030c180a050418060e03091302031f15090503163c08 63
    0x4818400c1c440460b5640c204408004d4160420740204844900140d0f1603010307480c1c1a030342039030030482000410080d015426040320311a0320307140800e407234148007901e800f0115800c000008000156248102c412600301c0f4440e594101d81191b810000c1e2005030120390b00459089025610002c1400180301c282c0c4038000c001c10040c02003807000390a1400042206c00041d0024010070842141403400b075548550801c00500d0703241c02048940d007094a5001e0083c8017000c103a60152100e0b80d011020000001124030400380c5458552604448a046001c20341c01840c132240c0040840c45d0108043e2561312849c0c6075a0040e03c004400d00086203043e00079521001e0242400390018052400300f0340300d580c0b0b01c02c00201c4401c409a1a9907410404081400700e001c3c0103100000c80c02c400182100b40982183d10004440d81c0361100c0e6a01d603010305681d200600210004009001010820804d01c0c081790422604084804a0740c410728a210004040741d0040e0703072820300c2e91007074100000081048a0700200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 657426600 1250 657425350 657425383
    0x810060302060726031017010606080c1b1e191e110303040b130e0408030402060c01200c1006050d02090601141c0b06120c0a030603051c02 61
    0x80c21680071a600340a01e10f03004210703254000c0302955600c0702c04104d00581500e1026503485c1d29001784008000341e0648100c0d0030360318541e901282c5015060007840d01760303811a250800741f0303203a0040340310095005c80345440c9e403030070841854403544c80c01b131010309c3c0e00c42e4482616040aa428820309800d08168591884d07180c889040f030100043c40c00b070030140c0901205102d5188251190070949407415021942d181e06000005010072810100005402c0c1c285210001100036502d400383d1800060090710b000d06800000d00001e801403500c2c100a042c5011031781c00105542182c0305044d012500884401e40703418101052900381031501704201c400b000300c41c0c4001e2020070300c0c1402041c1791030601c60001c0d008031040e0000840c83e9000d000c10228102180002654905c0d54881142d407841d8003140f1206032604101d600041458420142e2780c482c01070841504050303e03890380710b01071980300c40d2141041c1501c4410020200702d060000850150040983c138040a0b08000c000b07062020940e4140441d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 657427850 1250 657426600 657426611
    0x1030c0512072f0c0a0b120c03060a09290307030f060504080d1a010f0f0c0f0503070209070806041401030201080f1f0e1506270f0a080a03120b130504021503010305070810 75
    0x40100e081008d800c440105840d5a0f6501c8500c0414488100d640014411900f0840c10344a05140050041385801280c0410001c6d00d0b41c000400d52540f076a0700c4040d0204411101001c0455a507074032082c0c1080c4900140c0740b40000344401c01060310074013104100340c2c41071100300e001c1c2075800c40008200b914180c0b0703010890310301c40c20b00506040b10f001000b0380020724101189041000800c111403000d40c0082c844940c5180c034a10007800f0580c01c46049020324108044143c025000c0311405050b80d9050319440711030307900c161014506a100828805003c425003003100081280348509402600c2e150505400c2446c0ca04814100340404403012030080c00c041014280103180100d1000d0280b43d03400d800740300700d20030700002800700c100808000c0c0c1c4a403038407500192070280040c50940d414842e80760a40b840700b8040803041103a2403101181d80010705042401c0043c50039900180e4080d1004050f8003044844103c075a0310740c1c200341c1017190a40d2051006106000c400c000025002d800213406019 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 657429100 1250 657427850 657427867
    0x6052b17070221190c03140d030b09010e13051203091e0a0507060f020f030a09090c090b04210506070201050f100f0308030705072001030c0512072f0c0a0b 68
    0x9541c4c0c4600c641d121865440100d080c2004a0604002c00440d0404210200090040310705516080d000f2030040200f403505004120390304080420034100ca040002c0300b040c60707072188500c483c1c8101050084585001d030803001c0202c1145880130314003800400340200802c1c5239404601440d41c005940c2000503520103682d01300040c50010f0924155032840c0740907200c9000c0404240e00d0181c04024980407030101052000c001540a01c0c3e0308101c8004071010b020100031040d0030baa00b0041f601888119001c108000c2c052042c54690020f000c802a40c81e0f5030758004951039950820710309541070001070f5156424440e00303400d20140c881e085943c034041c0d1045a4030b40b1002a407003110703510004205a80100004035003902401c1034a45040d0002da40301100035014007041000c980d00391071180400c1c54903950200c0d0501c10820385110014034101c0003210346071114155200742113048982c080796100901500300d03200441d1040000040d0000804419114600300a03801c00c941d0020302c190001072183e482d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 657430350 1250 657429100 657429103
    0x5060615040f0b0c070312020d08071e051309021810021504060911030a0507151b060e1f02040f1703090d17041404050105010306052b17070221 63
    0x4084907440081140d03a0920050313014204011944041c114810a20745400c0050300491102d6482c25641e5505c0003da44500041d10715a030400d020161510080c95204401d6004100409010350301c1e804102c00a0768802158007079900c0f400b0030312414001d160442031241005546a080a5060300107010241c913544181001c0c0344008001601c0103480d00300800501080000c40c00351094041c1c1940c00181c805e091450740c910300c03031007840d074181500100c40040f5032191035030f01e441b0551001c202070741e103215072651000b601c41108040c2d42e078054040c881040a0b107074032540d28408100103015899038135000150b0301c010001d52042240704800102e280072a0b2001c000c88545900460302850004002d05048880f00c000d02400b5002c00400500464072658a45081c0e43e034243c1124140a560b8a030001102680c80300c0c46031903040810181f852201c0076074800010320150b040720800c10101429143c800c409440002c118000c0c12000400ea000e42c00e00e210020001160f80b5440424003944601c0e05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 657431600 1250 657430350 657430379
    0x1006170303150a0312180509060102341e06030b0d0f050709050705040801151212030b030109060e15040b070e0f130606090909050c0d08160506061504 66
    0xd6400b61080b81c00441c8540d00c2035807820103150072541260030107041c5007000c1d08002550448a940c1040c00900040628119910782d00c10a01a406070000510030022900700d070202c0f4840801c0101144010748007506652496001000c0d4044400591105500800200e50302c54000108150604a8640c2c107516032580014900780e0001038183c101805080880c100001038000100c100e0904040c0070103e9402405070041e01c001c64020400b442d4170003000c0b20178001c240300710300f0100080030740040807441c840c12026900301c0c1800e0100715541d5210000c0d085034114182100c81c0d0340e403800880e0b444141008040c911a848540f80489403d02e038a51010009001f480c02e010461043c40b5142c0689a81410010500700034051120444040d08494050240c0c1d0040d0300000345400400100420706000e111103c5030040e020b0450307800000e0a226003050200c005503502d043c05c21170402030780354512820b40d41d54080c60103000d05003007180400103c3c0803282103912081710184800e0002c0001108003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 657432850 1250 657431600 657431611
    0x203090a0807110904140f0106080c0402130b19110321091504290c030627090706140c0304050409020109031b030201021218010807031506021006170303 67
    0x540341c2d001c0d45082d2082102e00e00049800000701c1c0148020000c0035202d100307140d4600c5066940702c181a5520a088410038420b124196004019055580c10940c0c010302e581441d506095035056180e05451042e5801404010154948150b40c102100c0c0d00030840300032801c503800503616042c160640d0840e829180000d0707000806902c0081741c4d005070204039a08607607203510240c07200c80c40c0c01d0800d80109030340c01d501e83d030380300035061408100e00b00c0c240d14040c4204d1880d0071407400e5450300001e001240454000411128500310b103803020b1180070120042c42902900700410019090403002002d450a0200e0310503124814070009900f003e000c402c0e1015190113442c0002d4055040c001250000c20984c00070380400030856450200e6140484d81800b038038001c0e021a20740644480f006052481042e1000700400c0c850505103185d07600c614480e6400482a01d030101d0f042c0792401d81ca0500d501142c2c0b00c034015030320512114501ca0b14602607500100440c2c19544818080c01c440142c5074403000700f0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 657434100 1250 657432850 657432863
    0x103060308220504110711030c1302070206070605040f020f0102030f0d200708070b0f01180507020c10090503102a092c0f070e1306030204110318010203090a 69
    0x14048011032692070b0389000b044000c1c4107000812a1910407401d40d400048140d9040b00103001d21b021301d050005400780d04410207400e02d00e4070005003844070000e410009080386d00441c10055a8040361507400b40b540254000c40210315500000c6c0704104600c0119081c45043d5081440000d0442c100d50090324204440030401148002540101d00304020201c0c07440d20414001003451400e003c08203000d400b04a204462085141e259a5400c8d500344509110b55207103100c8004841c12007100039040b8a401200e0780c0111b40c5180d11030000150b6103402466000001031848008004a142c100103a00c25509810b00404c140704510603c0d00e041041003245004640e810030105990900c0360b0543c1006200350560b9030154240c0c140d1000405110a229074080c44c00e101c007282c114202803003414010106502c400a03d0b1680c0c00a12007855a00d03400c104020b6507a510000260316076010340d111100e016401180e03203242640020b8044440300f40b0f840400c1e803042c02000003c80c80004e00e102503540080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 657435350 1250 657434100 657434137
    0xf060c0106030516031406250c021e1e03071401021006030b07080601210b0f13020903120403030e220e0d09080c0117060d1e020f0103060308 62
    0x2481602500e01580010024850002e0b69a40da0940405910903a0b200b0341d82440c040000b13000c0b00703640d0b90098905205100140c0c5404000800d0002001107458941c10f10140c204415000a08540c00380c524030a04010000402c03041490010a40804540c14003101c1e500c05800d01d0110355180da40c0d01407503405c0e0403c141c140076560b00800840440700d00c80042440010381340d2402001511050702c83c00003050103103002c5401980030b03101c8007884e440c410752005c402e800c0c02c40d60301000e4150400352f1901300c1e02c0d2051500d16074840202c4030011f850f02d4100969188188414145006800300f100741864070f09100600004e80d00080102d0b807180202e4003040501c0d00380d0307a02c9040c0040400310078501e030316110103488050000324509a80544540341c3e243d01542ea1400c10b41c9034040203669038000340041544480c0889091402900400c0142807041e080001390781e5490ba00c1540c01b8041091aa8142c04008500d041ea1140349450800e04c0d00b4800c4c0d910356500d82c00380c2c2c0504c6c11842c0102d40e80c075 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 657436600 1250 657435350 657435367
    0x509070e06070609050d0804020303030a1a03070f0f05090405060a0c1b050a031701270b0d08041802040f151e0f0810050105040512030c01020703051b0c0f06 69
    0x11203031604121001031030959214100c0c07419200410300007808440c1c500581400b01d008500408113030707103e190003174043d5255a84452480e001014050229020b0103501070712100309442c100024070141c50107601d4103a000e420f2800540b17510906901ca40c1c40b88080004010025002180d03841d04808040004181d0b4400da0500f562840c0c144240242d100715030031030b070300248040003035810159802074484050303a9900ca441a0745442c0700f4000d000c84250041d1203180319055031503882d5048103180c0000070315104000d00203032110b40030000541c2c0d0312201060500000c0e00240c1c48004030b40b0b0400085141c10f142415108450440b44104007502c2444100c280c42540110600001d0f0290440e05450030805010080c090866410708140002c404400244e00f0300040d06038a0195081610b07a07908051900d010000e84405080c180c40203404107000e0404450006d00191a01380d20a45480d0f4036591031154a28200070034182c0c0d103810b5032000c0c489080e01e0b21650880250044161141540c0e590361 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 657437850 1250 657436600 657436607
    0x30316030c0602160f1a090c0d0f0507030b1605070f082208030307020d230a020708070b07031106040b0f090a0b0a0b090f040b0c0a0e1e040c05040f050907 68
    0x1404c0c0d008070b07102d5140500d54100001d298694403241e02c910150200003100300800b035001c0d1401c4800d00032503801210055031030f181001e05c69980c1807140c00a052803113500d540d02414010641d03c00c59080c3c2c840000d1102582029004101c1d08031145070542c2486a9511030407203420070000050704010000801c522035400c83e81e01c101c0c5c404150200c0e413071080d03a258001940e940c811915040140102d24000e0101c0f4400e4040d66039040d001040c0e0303484001a0045011190310038038a03403040d480b581c40001020b050912206005144102806407500d8181c1000781c1a480c2152060b50290016020080028203101c5a982c0003184408070440c40d0f50b44000c214600010b040740501000005420804d48140f80d0304081c04030441aa2184c680392580c01240e81ca204082d14000c105210000000d0b03280da455001510003c0e24038501020f032004420081504490541c10a0011014202540c032840c1094060351440e20080d103451807a01e841d04029003114203003406820310407450b100110322071511 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 657439100 1250 657437850 657437857
    0x150304030e010915020a030305180a061d0d02010905102d020c030c0618010c12090507030c1202040606020d02030406140904050c030907210204020a1707030614030316030c0602 77
    0x810031003039400424207007400b1b90795894003075044001a05000001e03c0f40007401407000481d4800000030204100b003070b500d2802030800120081c501c1030411110340d418031400c00c580c0136168007035000001c1c58400d508085040030503007921b0780312503420001034240024640c2d80d04441c0d010410418440c5d446e0410700340010f84200980004e20380310228444103070520100340c4d18020030b00880203402d02c800c42c07207070070303090b030f403540d13080301c4c0415034060b9028203030801900700040f1036110b07200ba03a03c250780329965149030400507005035400c0000040d4000031410b240c4141c0001c0c0030b50f4001800004840c1a00a6584c4100e000e0441002100c441c41d1800075001c00a40d030402d500144140701da0300d0520f0001e030f41a00101d524070918410ac03000012044107424108040f101d0124842d1440030b415000d0001950081400c2010085031800c01c1c083e44d05004082c6000b10720f0b90343d01280540c900040c100c3c00c0011502041e100350810001008056130b9942c1039201660726042c00315400100c0c0c2041c030002d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 657440350 1250 657439100 657439109
    0x4140a050604090c02071205120a0306030605131104051b0702011103310509060402220b0c070e061f1b0809120604020a0306110403171206150304030e0109 68
    0x3101040205001c1c0442d0420501413007540d08882089070366500c5641504450b507005001a0000d00040c1541301c02c0313900504200c0028180410380b00c0d981e603101421260100c801401e141842040358003042a503998990046000303ca041c08a03040040502d00e14280d280103091a50200140720002c69010b01d45444c003800b02ea000360380e1144e03030305821650f1030900e200100c0c05061906010f00160400c02201c68280e442c0176020504985d601c074180002903201e0940241c5034002c41c0f5420b40c00d10480c160590243c418140d01a44900030007001501d031802c00e80010240d254100204255a00c0d070b04100d642c0d02d04400400d103248030b0500c2c800c0e101c12010300600218207502d81c500c0403d0040c5900100342d020015560b0301440c03640401c5558aaa4090700c0003944000410010804908107030080401158143c454510382560b958850010003140d601c0c8080203540421040b0380f800045444039407140381603406070f104403072030100c425a51000600090a11544d105200700c40e9104090841c05003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 657441600 1250 657440350 657440359
    0x90207120513231309020108060306041e08091201060918050a2a0b0304051605031b060906130509060103090305070b100e0a0e1b0627060301030f050607030c0504140a05 74
    0x3c4c04140c03180c4010706040b08040e0301040385000802d4441c1000241c2a03c5207420005000d80502c110b8000d5010b07000070a02525904800c0c4914142e559400300e560a0342c00384080005004d601d0b01d07420301d0a03108100f07443c400000107010104045040840d5a0f030010368031105603020031045100780e4020032a6480c00c2c17000c4075020312010810000c102c00441c0554020340c2140c41401c0c202c04c004007a01070340c0c0103c1d90580c003c2c80203008041a034150a004010004015a040092010100d0f02c1a0401348000450390858102004203040122485802402c20311b4248501c0c3c0c1c072030b103015040c0d201d8400300a26648102001940c400290017200028202c11400c002403410720002c5400582100c0c035449034a03014401c2e02c00390f450280181c04031181409000030f07081c6050400c000c10031300108500006191003110201400e543d41030700031800f075407142020f818418018189a4600302e0000d0841080c940b5101c01d2510440d00241518120380c1600c2418807080021800b141c0c03088a654001e0303400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 657442850 1250 657441600 657441619
    0x40303270f0815041109071103030a0603030908070302090705030a0b060708092107181404050a05060114060403060b01050c01090b060f010c080d2409020712051323 72
    0x7900c0e82550030034101d4951004941000b55000711070030781d9034020b07100100a00c40700716408115052520141c0d900c80003a007400310400e81d0006074181540e008445d400d0400e591003206104042c2c00150560140610700001e01f2584e0641e40031880e0043c2c040c203608244030000c0300150010505400040342c02c0c0001c3c000e9a02d03400755151078052600504051403140fa440403803139800c01c0d04240c0d2141d008508030024420315180c440360b1a8020300412007e40c02c1d64445501d030340d0341254082140d00036441000100709180390f07410701078203140040c0c000b0460902c0e49001c00066580304019242a0fa404c0000080c1524000340140c0f007034841d442001c42e6a50030b0880580c144203225080500c9134800b81c3c1e00480d051070a070011184c3c0007078610024880b10080c0002c284216255200080c5501c4030511080c1601210701d036407840001039840b02c0e0001e42c000030780780c041005160301c00c2c4280c44a07080850526520403a07803030040700c95010740001c100c00c040041500f4442190158090080501180341 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 657444100 1250 657442850 657442859
    0xe070b04062c030c130902040e0309090c040b07110d0b07082a0f090a0f03080307120515010c060f02280512070807050417010c0e06090604030327 64
    0x2107981035600680e01e8410640c10250303520030030110302c40c8804003d000e030011440150801c000715121903441d41e9042e0ba641080001030304c81e8410034401d000000015521405c21404000540b00001c0140d002c92106210800c161800102078908165100c203006601c0d03188800400c5c4940d0f4500070213031050124009120045400001d494014808510010b00603458078100e1103d0407800c040700b07526610100414107010302940050310380341c040200f0140b100d55980c44a407078a04d0071500159642000003080c801d9141e00100074000888461400380050b107405044012400801315256040c80007400e1100d04000083e0310220f44080400811901e8400b80480a10801109007406440003003015507034002d5230290058842140070584840c0701d070b60700c0c000300301d80c0c205015004406000050201288000324054000ea092945200006143d42100801000c000c17100b100d890280350100403503045a21080d003160b05494140c1000041c038003142a1040b1002c2c8580b06062030700300140c4001c0b4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 657445350 1250 657444100 657444107
    0x21020f0a0809010b0a05030a03050903030c0102030f09010e07031212060f080703031704170a0c120e1f09060e19030506160509060406081801142d0601030e070b0406 72
    0x18011000c05008104c04000841409110f10a0340035195244d4408a61000002d1084001307018220016040c2c03400c054441a64031b00303a03041503840100c03000b043c01c1040900c0b807003407145081c0001000010507440e461500d5401404443d180360300c040010206010300d0001d8107400c448000c00d03200b03460004031640c1e941d0b45c54440b0300324007003200021100c0b0034420510010303100c1180241d4200c80b00c2c0c040d800c000500c5c403000c0e42c1f042c040c5605101d03050030110301040e0359106020302203c180d110201c4111140040141d001c0c1207c201c0c01b0307111082d00211601d9036024000005841142c20040b40202003000080d50350b43c581c003404924012110004400c005011032414041c14100d800c41415100112003695203025884ae841e0700a14188010000140f0a0100341d03042101011100b842004840300d8600f274070a8203ca04007410310401c140306098000c41c02d40c85d0345102c1480a0f07166058012421452440c1c068074803410991034a003103034103040040c04107800800d01c41c520300d99259034524029 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 657446600 1250 657445350 657445367
    0x13020d050d090602061006050c100203011d09012a0309021203130f1202010516080d0c0806040c020604110604080604061e020f09041a0d03031407020d21020f0a 70
    0x250004400b0900001c682e400026a1800350785404007114480341820380c12205a000305860a56a2007803004948904a8a200440c044c00311400c00326403054580703880c0c4801110240c20a07081ea0315005d03d51207a42c002d00d05183c00300100143c5003604403a0250200e020300303c0e02e1006540175003c404c008028007000401040c1d80055454000d0350140d0322564240c228000d44269010840704060400c019071080f001440d0710701e15000c0042e055555078a83c9030030f075000360000080c2d00d0ba880d60300d155081e400007c115405541204d05001c2c040720407100a4032524050402821140040c142e141c09945440550303020300720b024202c034264505400d10001a25110251000141000620003028422802112080440041d1a61400300c00c40248001018104025401e0440f0309000ea200b079692503842c140032034025600482d00c2c80d03040e40c2001c40d000c0d003e440b020640d401350f278004034155003021101d0000f4100c0881c090011540e060381d42c01900c54441090918a00007032828405070700082c25 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 657447850 1250 657446600 657446623
    0x180d0503090d03050408030a1e06140406090203011a03091c021c0c020d080307030902031c02070506031308030c0702030703030f11010905060105060c070e101d0609060913020d05 78
    0x1100c0c00b0392001e0400350201c40050341c014084680c10000903529881940140c0b0b500b142003002103140b501d04501c400e0407100241c101905500c800301100c0020325290240c803002e4054103604501e1540741c00c82c0005114030005060302d40c00c00101c0082d002001c1402052001d400322885109030a0003882c0080d103519114400843d081e0321400c00d403100600c00c90825010b00d5000d01119299015911004010b800040c03555081680300c9041e4001078078180251400e203420013408007660340d91030b1406810411036422503801043d051081041000451803001245504025880e5032911a804008024440c03028041e402d4450781c2c0001040651001110b403505240d079603003d2074130700c034510401d00380c4021303000c0604264003040060002c2e01c2c01d04002c10f00d02d0603040c00c5580d50b0381e035451100701171001200d50b1070106038100300800c91210b642c1d05d0003034455110a00c00d8418540780001940d4850f01400c0e46000706065000245203046452081035a03603001001030040d481c3c140740c200d50303d41a00c0315 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 657449100 1250 657447850 657447853
    0x70b01140901150f0c02210d201917041e0b13140a0f08060702061b040603050402011209050f010c0c020306040b0615040e15100c02010305180d050309 66
    0x19038005014503004030603c89a0710490300440c14101200c0080d803140303090364003240c0440041c54400400250b8296522264080c204802101601801c2c0a41c107003041000c0c002e159240ba880d1b01c1c8003088030464482c4c1952484202c101da82080c8004094500100041c4003002602246031401d1401d000200c0c2680400d81d02220740710010f8024a006040c130000030200e40d41300902440c0e00c800018108603401805c1101496903480c0c0a10070301d2060b40c800c03215904200e0a100c2050342c1800000e42c0f10100d98442c43c0313150181304800a05101c0d40c46158201035845000c00c003160700c24040248070f0030590f8824400c03541542007054542c000c140143c600e1358079100074030300900d00503c910070b14550018081c0c0215910b030746400401c10700007040264050480c6400c0700c0305005290140c8085e241604802035645082901451880d0140c20401e10440354a40542e0310b095001c03044035001942887d0211356925000d10440d001030403811840414021035020700076584c2d10a000d1803285000e0700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 657450350 1250 657449100 657449119
    0x7030c090c0f050306041a031510120c090f020706020a171f060e06070b0405070e070206100501230d0902040b1c0f0809030601030312050a11041a070b0114 68
    0x140580354205420b200201082c024400540f441c5059030200d0703815a44980e081d10a04903c0340080d04140468141410a10801c428004c503916501c211502900e039082201d05506110b4071240c2030340001d44a400d5041d40ca9800760070201c480d43e01526030440d44030340b040d500c1d140d400c00c024002c112200c0402640240e40d1000407902009190b00038108079018100d00c0000d82030820450f0101c41c00302403250446810817074040003401c0d03180c046224500031405802c80c1400c25880302c10002000e4031800840d8040f03000d00c070705041141100e4003211070900340004246445c00307030f100400c0381006071008180c1001c100c01c071802c100d640105800c14800c1f141004100c48500c00c00102424090300072040040748690341e40000d164060080d0014090030895090184180000e0b1404c0001d810480024183d03a440110000845c0a07590300a0190b10040c00103031400c15180020b03010314412000f08010413696500303880c40d0700e0200c5140d03540120b194002503840741c1106201000302c1026a000d0708140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 657451600 1250 657450350 657450371
    0x3020312131a12060406030804090c0c0c0b09101805330d150f060f0c080c0c1206040308070f0908030c0a020f01050f0313060e1902040f0b0609040c0e0307030c09 71
    0x248191b4007070700c0d48160440d090904180f1120005d2400304000c0b400d000703032a11040d001c102e6140f64100185503114085036942c81620501042c072400c1c010340010300038a005414071441c81940036605588055a041c0750840d40300101d00280050450903102c041c2c42e48900d125403904030340c01810103507503040051100c0c1c51417a03045500d01040c1d108403d4480c690260602056115000d0a0b810000c6c40c609941080d00b2178a440c41c0c141c0c00341f225589a9800a00740308024204100a0161000c1500240046242945028041c10310091840c1d08110501259024542c0076104510207418160100d83d202c000c0e036020310b40c0d1a203078484180d20401a01c0c020f032100e503204204079580d84c2d41804002d8203540710240d1403003505146003412622280c88015040d64690200000714041d46505001218404940140000c543c0c1c407811007000c0b05d003001c042000648469080703e110030b400b41d0f400107000d51070010032100c000300100403c1c2d050085620010611409031003580079544d1075102000f0f580180d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 657452850 1250 657451600 657451609
    0x7110c1c0b0705220f05010504081b032404140703120c1a0405030a17070c0b041509080a030e030a0905190324050c0403020312131a1206 60
    0x1030180400ca0480309000355000490640e00c00e500b102e054141241408422001d4000100020100c480e65502802041020b02c26072410704000303002c2800c1c4030345014140301e00240c0307580240c43c11048200e00c0c000d01222580b000c1060389032640601500020b001c10000c202090b11030140c3d010703500e003120500d20406101001c82d404003200c1d0700c40d4280c02c080d01080010341e0010b606090948500a0701402003411000f480c0502d0310840c4240040d542e0740090800162445090880d00c40e2500742110420140d0b6421020703800000f41c110049050076602d520b8160510810300c544100c010303040480b0030003004089000b4111f200c02d162410700c020a025140c0e030781d59014079040c00000480c100410403807030a01164940843c1c2d60100348560803600d985550a042c02040d546038007020403498107804030701a43c416250414103400c40301e03203824959000207640781c107820442c0088800c0014a41c461090a054001c001c080b0000030f2615124111044900d0341c0208860205681e1400001440ca00c1e2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 657454100 1250 657452850 657452869
    0xa0503010c08130503040e1e0a0605100518030304030c1d060108060f0607050106060f09060905090621060408030a0609050405060f090c090c0c0c03190807031707110c 73
    0x1e1503541c5440c1c5a680d20a0014100d001d450300780d859000801c004a140d0540420640c41010a0101d180203414013130301d0f515240d40001c1400d000e491810302c062145a0b0303590705140b803c1015140468850300344412184d0414140703811560b07d48400640081040300281d640c004568610340340030354002d48100003101450f01122518000f4400c4800580c00c6d161059540c101100c010b40401e040c5641d6039030320350850f0b40680182010400c2261610340d50307a440510346018100a141c00500c403032034400440c48110300507203001c2c802e452115150200740d02c8100344800d41511401152020b05043c20901c2032a4426100422414140000820103691501800c1c3c0216840b00003000c1e50341e54490301100c0132002604415080c02008215080f6a950600c1103008043d50f042c003d0313458161010301413a020003225021701a03001403c03000c0e048808004210300054018591590340c1455107022181000c0446054145003c80709c01e2103d01940036050307080d4414001c00321030804c18078804009542c0d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 657455350 1250 657454100 657454121
    0x601060f090311040f0f15080c0301020403230a05030f070b010e150d0c08070e090706030b03070603110f3001120318080a08180607080409180c0b07020a050301 70
    0x700e418841041e0819034880646480070010000b94001d0306da0004040e01d4880926188088410342c050100c40307000c1c00082103010086000b10300d000c0c61035944042101e042d181d0b030601700d0030307884030199114018850301c1107041d03214082c0ca9a81c400c640941c46180c01c0070700182c55116000002146021600060501440000304503200040a850412a81103c400b00c1221a60201c410004201c4410040a000f4000c0c0303004050350f91070f200300d015142c00000d0344200209420108000c089031000b05120051742c0035850082507808000500000d00c1c4181d800c0110109000100ba090340d5051001d144407078980c05c91300310b004003560400044801420701904860b0203000b2031200000727018601e04001e800c2c92581140c05256103080300c5091110039882969107c800007058061114480300e01a800c5601722260303424800103885d542d50f0b80c0118010f003041c40355503000c0c441e0000195815140d8035980180003074a450785901c0d41e15456004070204034040c2ca0400c2c000728140c68180920701000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 657456600 1250 657455350 657455363
    0x120114130209010314010801091502070f14030f03010e0405010e0601141201150b030403180f06050a030f0f0c12024305030304020a0b030403080f090f0f0601060f0903 73
    0x120403441060000e40c40720710740e581416514603160b500c03e2184040d29008040100c000201c00e0181d06002109080088001615510401210002440c8110340b078030710940003683c2107401203a08036102d00c0d510440d0207440000a01000010700c1620200c080ea01c101d00c560700034450311240c1c80066039200c03820b01441110710f00b04000c2843c241401213203403960016000002c203101c400c1300100000360001307420295001c43c001080200341600b02803000325034011541d5040c14245001d20038240203d03036004a504002000540550549c03007034001c44800001004204100308034440000010f151a000e04404103c00c03000314403a4541030f20030345001d000c816075040400d100f4480ca139403a554040069a9803d601071403400414502c00754805031440c8a440296941d0401d8010082d0305c4256a0140248000c10801c100c0000c0c2d00c001016040043c2c2c025541d41d87c1c850181c2c20b414400c000c0c402d40d42c648101d0000146820b000035810341255001c0d202c018074000414000c0312320708814040a03050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 657457850 1250 657456600 657456619
    0x50d0e0303070302060109180b0103080a200705040903031d070306050108010b0904260423060301050f010e030705060f13060201091a0408090607050604020f0613140303040905070203120114 83
    0x640708603800c2108c0c02da8851040b541300c690585ea5501c0240c80030780080e00c5045000c180e010039140c005501200d000780d40c0700b0740201030088210b03095079150180501402251944044420103029801c2090084a01e90404082d031440c0c1407040ea42d0846e40c44140ca042d4103007000043c0700001232062190100001d44481440c0d915070300d400d400b629a1941c00c000c11820f0217648542c0c9141c50700a0000303020304000083c0c01c000c2181c440c013040c5105011031413080c0c8041004020650740e500380004c0c24182800c0c00d481c0340d009a00003d0401c0c01c2903004030741054000038038141902c3c1d950010710030400003440d0020740c2516613004034226080d0302c900501d90001d015685044919020303005501501ca07040c61440e166a4502144103900046005c50395680000103020440c50f20070601c2040750780595510b41001c4120022186044e050712a142200040d41041783c03903134a0600840f00907100d02c010600c51030618490096681d4440d4145440d040102c07000815602c803800d6038110440c01c02403d9a08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 657459100 1250 657457850 657457859
    0x1a060103290a08010c0f030e06071d150d0b030601080c0102070b13090603030c0302060714040b070501090b040506010509010f0b03070f05071406060a0603200a110604050d0e03030703020601 83
    0x11000258194542c80b44011500240c030030b6090080e0384494005076180d154048000070064281c1c0d0101d203051000f60080420015000d070710000068250070014243d00401900002250214480c000020440000028220801d421070b421a0b65004000e0f411150180c0c0e0b1421215202e021a005090058000c4a420071000034240c01600251404181811500c3e584020f0b40f401c40701d207940200c0115400d080070400303154060010703981c001018240000c401c0c0da12408100d55100342c2c015141c0282c8003040d0b076418420258010a10309901804083c034504090500d5507451a0074440d0078403401c810300c0003140b0790440b24450001c461451140500750f03203800c0f106842d0309002c143d1030010000c05024400101c2c080b440303c00f503820b9102010700700c5410884240954a04140c00800a040c04e01b40c0c001a0800c00042e8506001c10b0031104a8032511070400860315541c0c41110140e05200e8002400207000000c03131703424801400342e2036204484000000b0305490b0300900c6030140243c0c004400400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 657460350 1250 657459100 657459161
    0x1b080d0504050708010e07030605010617010603020a113a0c020603130f210903170901090f030c0807050907020c10050903240c09280b071a060103 64
    0xc1c1c0040c401d40c01d9030710407030321000440c0c211a2601c48210896100d61010824041c60b4421940501a00c0c5410506005001303810804401e040c40340000b0550b000410a0311a4890b4200c0c4807400c2198003a90103103982c90f42c0d4070088901440303001550102d10500c60005084080702c041056220b42c850408103401602000144e40006024031020703456085040c000401480c0c10b030001500c103010318078a1480a401d144a40d110000c9510213100d060728080c0040ba01d00d0448080c41c62420040c0740ea0b03290900012100b0a6203507004200c8a51414400720401c60400302c200c1c20340d15540e04440b100c0707640d0130030085120420b56201000d0f130400b0184440d6800d2040702500c25880c03174105185412a50004640340c60312410301d4608004020301e0360203041c10200441c0e500501036080c01c6052101c00301c001424101c0400112503004038072103034081c3d03840812142c07200401e0000c1105803294058208082840030b034505110a0240b410006400b0758002c1c0300301206c010709800004050316421107a078 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 657461600 1250 657460350 657460361
    0xf110a020d110c090103061a09101a04080d090303020c011706060315061804050f0405120a02070909061b171302010e270a02030106120b0d1b061b080d 66
    0xb00c1d0340d0049055410751501e509000e2402036109090014100c1c055090741030841d08021005403150101100340000341804041305819141d400511030f40203094010b03400028400c9600040c000e0103004008a107440e0052a20300840b03000f9029940300c1c507101b900444a80d10084084441900e00e2400f09005040001c041e560114810036400e080035102e60005141c0d4204006c01140d520880080e40c3c5c070b9041070b0003003d03000951400c2c60052130400d0b81d2002c0c4c4802030b800341507000c0d20001c1400c1d410300e4800c00a0348000c18800318100311006090900302c010f445a4150402510240d0600401080c03050107030060f404081800241c07544c48450384545817a40c10306d0164100141c500100c00c1640e200801c103030016180e800c1c010001c20001c9a0071416200080020258038818001002840c1d00000c0c0304004000760040001d410003484001000c00c0e5003140041d04044002d03138100c240052400103102600c4054981681ca1780d42c1c460100d10021803c1001416200c0a0044200d43c80c00c54210 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 657462850 1250 657461600 657461627
    0x130b040b13050a0c0c0512070c0f060804030807020a020a03020f030106090e010b0f01051309051e310809090a0612051b0916140d06090f110a020d 64
    0x4900003140900041079912003500c2156070340d641e40140030b64030065105641c41081242030843c081034071034540b2911610000c1540481e440001071050810007016908030181c004031504070744254036214000c0044c0700848041b0040303a0401c0100350114000900055010f070b0040c0b200c10000e003980d003032184c4400d0340310301190150340309c41e0081000301c10b500a22114002c4a0000036110301d031002048144036100c0e08040c14410200810803124405111000036198a1000840c0301d413a038207210001c540f680440480610310090074808002c070140d00307002091081d010504040340c01d0500701c0c900f0746080c41004055540030030591405052000ca244c0c2c2c02143e000e80040c0750743d900d05a160f04103005000840d03180c7c000c2130b502680c0c4070007103102032070160090328560410b15081103001d5400c1c4440000307a0900c0072a2601071002c041090840b001107410042c00d205d0b03d6500e01400f0094139600b030079240c0c007a0908807a00e060780081c5083c0c0ba05100d4550080080101805041da10030320310303880703 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 657464100 1250 657462850 657462859
    0x9020703031a2101110c010f140f010b03070903121106011401020709050a020f07030c03020615062703011508100e1507090e010303051b0609120906160809120309130b 73
    0x100c55103485e440c0904074003c82c8038000f01d810500e4282036412250300740210455440141c0a20010318000e10006065030b506404807941da489442c800d5401403055800185542c2ca07404403d8415684808040301d80422503044464590306d83c0d42c110306441088180c00d00580c05401c04221042c413a4010325000820781000503d40b24203200c0094047d442104240c7c00301c2e02c080007800405a04000844d48041500c400c9290700b10792400090b001d10441d00740e0701c000d48074080c1c051400001d900c0484002172004008000903004141d440307040d2000f6200746180382c040d04da03052101916030b004034109510000054401803000303100120107508050706580400c00c0c0d1582c003003025503104138000d020f10f0090700c0712600d80c03214140000e4100440d84440030b043c0c012105009101e40c0004125100b00700f8a4103054a40345144007148050259058581c464840416400c06210b03040008000c405010349001140c07075030b40c2c48203a83d20300c901000c01d03411148540912243ea0340d00c0d1320600d00c0050040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 657465350 1250 657464100 657464111
    0xb030c16021f080a09050d11150f090c010212070204091b090515010519050d0908031005091012021009030b10061e0507150b030709020703031a2101 65
    0x20007282402c1e0018401c41c1104008200c1c2080039500301000d01e5010084410500080742c0342d0781d034151100c0b0b503110384400780040821044003109081c40501010002c032410b1210303918001d0040d0700440b105944c0e042c004d0146920a40281d4808142825519007029000d441d040141e4240310040c1903400c0250364007040b0b51202ca10410482c08444020030301004081464107203070300c0d1644240f512466650501808000700f100058200b504074084c1c003c40d003001500e52480c480104d000c1c1220b2080180075000c00020080000070720302d080d81c2501c0c0b0507100c0100a568606500c4a000d80901945a440905050350030061800543e014010b0003113180c180c424917aaa5240401c0c0c00040c2e4100120750709200c801e01456520072650b045416000c0542c1c00b069005250241c194442c58502a20222980c042c101c60b10015400114000c1c001401b11401d040d62006506e00941180d0300c102d00180c2020401c0c0303a12001030034020180040140300040e110b0410803200e0351025201e9080d489552030300f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 657466600 1250 657465350 657465353
    0xe090717070201050a1401030b0a1a03030403050604060c03140a09050a020406120b1f05040902030a0b04030216150518030a0c122102031c0b09100e0a05010b030c16 72
    0x1403880e900804040e00041118100412031105448004500e95056401e50f4010004550310780c0840c1e400403c8418000b4009100140e000d2685840701ca8075501484002000810410005042485203024140030030000814402c110b0640b441441e40400a00700c11010914030f01c2942e1007094110300c40c200711241c65805a021500351010b540c0207004d00360901b500901400813410809034001500c3c034070b0140c50440117001210228240c040d2600466842402e0b20441d241003001c0281e00c3c0d04401170340014602490000c0d960116400901131654210700005140f07044c0000c0c004004100b078a80c103090040c030b5440c1c1985086c00100c100e0313251103544080c001150318090518081c00721403d06040703402d5581000070310091991007103801414102c0c1001062580030095130303582051400c20104074950074040c4405000540d1525501004110074403210800c00810345007141c2e4420300d03502c2903550b9000802c00700c0340300340709001d5500b00820000e444c82001d10b00800f051b08503032000381840c5000303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 657467850 1250 657466600 657466637
    0x503030418390e09130302240108070602120418150b09010f050306090c090d0c0e0717090d050306031501092406020d030c11010207030306051c030e0907 67
    0x50281c04188034588000c11030103502c00861040c40d880c0906080322565401c0022800c8000001d16094000204a50310741c1014400d1006001c00030880450406d044040c03141031302620300c04c0c440c480440c0f04900001550034004905484c0284820051074101840d001e407501c0b00044109442e00e1a5585408280c0d0840f4016010000307807c4540c20f150b101c41001c0000350669003800c594405000060041250a42e200328003668003030658035076540c64076900c0c0040741030202c40107002000c02d0080b01000c50386c3c032113412030207110f1051581e8424001010050f81c880210307055aa403c015003101e04a620842c1c0120000c5030007403c00b801301c0e11280c2c88100c2d402030341803003a002032502545410140a40702102110404c00d240304500c0b44051614210010350f0b41c02d16003003544c00b4035494600d070107001c40c0542c11101060101d90000e41d6108503502e070003401008103024151041e624002008003e10a01e0141130b0130543c10380315000103150203000c01400c80c0d001454071b01003007071011500c8000c560 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 657469100 1250 657467850 657467891
    0x9050d0f3306051c0f142b0f05070503030708102114161a0412051c030209010909020c0703050a080d06060f0f0305060f0303031612060503030418 64
    0x80d41d88001442410324041040b0207261403130322224000d0540c0d0060115100c01061441c180e40042801c10203400d40101c1c509041098060760a84048002070080700300310950a5098070000b6a581d048481103041e003650349000756000076050790300c240001000c40c1c0c0240000c071b40110200b1655250320303a0301c05103060014000c88964001b112401128820013840149550344800d0203000b400507510600e00403120b103140c0d8800d81c0b0075190500f2001c1f45002c01201182c01a10f203d04010000110300c0c141181e4803003030240c41880e00000009002e00300c9111b8800d640c0314060581d01d03001c0031480c007861003010790455064400e4600840c900040094010012030a0343d5102e28503554403400075039482d0f0110b40556000d4018040305801000f1200c1d480301440b04026481e0500090944810000c280320340a00519142c261000100b0700c16407540740800d6411070300703036982c0b0180c0322890580c0b10425034401d0302c43e49030558414032050182c0e0088800340d100104502c0b100040060300c507002c0380a084c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 657470350 1250 657469100 657469193
    0x50616050d1a151305030325080702030d17060904120f12060e010f060203040e0c0f0c0604060e010e0c03060a050c0f031302090901181209030f05070609050d0f 70
    0x10b01c005001e01342d02040010f100020182100514280904142c006002e09a0003070095245000781c1c03c4201042403080940f00c01c1c54014088580303051030500040d05003540103180c00c1c05144072200041f01850410b00071071080d80c1c000321103072500038034182c00d54440240313025803000d120741900042c801959500c0744100602c14001842090751400300088005802034010000f107400801003800701e584030201454000080e422441d642d940791030030002590103101020b100720b01480c000e1206003c2c10b074010464001020000700131388400281d400365034040c0754841d160590851000a0001c000a606c400e5115040410007494041801e80d00501070703204440341d8941060345003602c000c1d420503c1e44580d22510303060082101542002090b000315a00240003050f81181140702d00241c1e2150940307200541e8000b1302900450842c0c50b0142c0c55140038003680d00001d08000000406140108042400c0c540104060048014035150710b1001510050060b9aa90034441c4070001056540e42c00800e18 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 657471600 1250 657470350 657470389
    0xf0213031b03081c110a120f060503060112030c2310021c150b0a030b0f0f100c23010c02010e030c1203040611070c03050616050d1a 58
    0x1604514041e5509003080e40e20305070310042801c05200184159085400350001c1c00807040b880a18641408041e00290f11444a0040c0104980c2c2c191600825155001e80300003105008801c0342100300001c0300c885100c3e4961680c002c0700100030181c0b420000140d094001d02d0001510780154440c02e50130350944903001c080d11982c0031071052104043c0200d03120b66034040001c0d8500380c0b18011106004485540e01c6201c3ca951301d91807003850354801c84450080100001c50794507038248040107001170124611050040c255003080c010b02d0300d005100200200402803900b400d498410340211001007000000f2198032120046050742d44a080d034070910400380301e01c008251180341f241d00a0940d6058034107048190300034001031440c46808524440c8140b52550065100c1d03a0b10b0030030601900080200b03c20505001400c8410b00c2011038021003580c0c0a0030031628192030300c2c542e401580010251100020740140217803543c9145c140c0003142e4610f6010a181b44040d07803000003403c00320143e40041a079 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 657472850 1250 657471600 657471637
    0x60209130905060114100807050306032514091006110a0204050f09010f06031e17210f061e130507020c0f0a0509270d0207090b0d020f0103020306040f02 67
    0x40344800105d13880d5110036140e41039200c801002c0504441e00c05801d4509110300880055400e45040012500d6142209041000798910510381810041c0700c0c0241c40c10000e4141414100b424032401c898068205103041b200c80c1c42c90300d50708030b94600e00b482c14400140034039070804000d80d079075010315402a419808000704d01c1c10720300f00103804c490300c0300c111880280c2850070803c08651003500c141895800a140c0a0905400d40b0340120b05400c00c0c05154125600400c03900d41e0742c00030700d100b6441010508100a030a4031400d0241c505c00008481865100300c031142c7c808544210b14212106404010b440509250303154807610007591002c0b80e0080060344100e000401616090a06800e207400c15070300d61070141e04290120304000070061030150998504540c4011404c4410841200301400e08156070748111030100080d255500c5202d802d075841d0400c50703680124034150060002655006021002200384400150003a4000401d400e6000d070351500c001411480600040200c5045401c00114 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 657474100 1250 657472850 657472859
    0x6050708070e220509100912180806040f020f0904030c060f1a0d030c0c090219030612060c051605060108011107021c05030d020a080f060102190602091309050601 71
    0x70007600c1c080c1d54854415612584501c1c081c1094000c094070f612940411280d4030320b0f240d03078138140d46000c81a003460325003600c1e40d0520005030002d07403e0f03603215a0307160004403c064401001c404a40900303502500711802003400249880045131117144054001a921000b110001340070324800c0354180c002c900e0656440042141600c81c0103081d00c030b25001045901c40d10310a51071521208a090b41c0142104003a02007814080e01c022a0b042d903010071072910083c0c4590701000690000800c0780008140211a12980b41c0030703002e528107680b1003425000d84c07a42c041c1c41d500045c00c2846031003802d108081010104d924100c0c00950040e901690080a595152018841c00c540070300c2c419401006042c80800c0050b560310b1f85590404c20301c00e42c0d001289066041050651003080808540b080c800103190323100c0b9801c0b07010584140300c40d17000404e595545000682e2528040031006025641d908000c40001d401031b4058120101c0240c122610046003c001c1c00844031020303010b40311540702000401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 657475350 1250 657474100 657474107
    0x30309010f061d09010b030303013002132307030c170f13170d0609180c15030b100c0209011e17031216020c0d080a0c0804030605070807 60
    0xd8551049030700030425140b80a40400d6111002d01c02c000c2c14007070740b40218007490025004403800103001000c0d030703640e940c2d104202400c640c0c0890445900c00005110036659904030409001c1c0990081c055540d00404000100c0043c10f190047d4540a00b01074001c0b2a074101c070050307a41c421086501c00040304003039000098a030300340700400d02001540c8001040801e451040005030010050341d10b0514030951031410341d4821a60194184402401154100c1008416045201250110b501c200040d0350325212800c88087c40c1030026100021416003000211040c1e02900c4400b6001d1400044203548000021410868180d401002603800202c401c02d6140c040c66541c010f040c800c0000510503a10040500580c85034400c1c4860100d20051669180005008940c00c0d01440b520f8034a6502e000090484103a41041c4610014424111004c0040c20080d5214102c103400c207040e40d00384070101c002104d115501c907100301c807180c00510000000076010b000f11400341c0c5248d11031040510b42a603005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 657476600 1250 657475350 657475361
    0x9192a0b09241803150708150103200d0b06030408033907171318020a02030421081b120a082a120108160503120a031b0203030901 57
    0x301800c80c880114240c10446103412141e04003165143c5000d50f0146800107820003104492031038480d401e4904022190754407040b101c2c46019409031081405242100460488002c1c8000c4940d446034050070044000c5400090690801480000b103200c600314408101c2a42050b101251a5240882880b1118110170103401504d0b4494070940c403d0070380a1030703420000c04801c8400c01800d000003145024421114142004044c03415400c503621102100c402c03048070703281e00c0344402e4055180c2c40005851414000c584044c080d9a0003541011b082001310300c0c01c8200041c0c14042148201000780000e08854051700c1511601094188007100180d54a4280a82801c400d0306207039042040103111a00070103442d4000040b801461508071302a040c3c072550f1188441e0170303031182c20702181e01507102210102c518180c0f0f90b0002a128100c04c819288040007110740141030707264008155003000328402502030b100051044c640405c1a51061200d05017510f41841b45000582002003049400d035000d0285 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 657477850 1250 657476600 657476629
    0x109050c0d02090712020f040320060301050117090c0409080409061413051302130209180c070f05030d0f0b0f01080103050c010c030c06050106020303060909192a0b09 73
    0xd651414090740000c40ba030700f0081640c1c00707101c1d0740d149240000350b0a90555645500e600c5100c0c0c1d940da12230a02c0c03c0b1080b910280c0c03031261040a40038070304604003502504c1c100e400617100c001e82d10210050785460842c000300174809a1040075119140c0f5a21402103000755130040c1c0c001941d0b9800c0c1054441910616084120241c1d641c1c4220040c2d0384a004220081d504140000034040e124601d01840c4064264000307584558101e5401030595040d40c000c4c10101401c440d607100640030030070307010344140085580b00d1016000340a040042010b500b45800b090f403180c42602e1400002002c082d007101c0008540300d4a50342d46d1661412141426950f0380c03050030742400c0c488010341c5180e81e1203540d00740e4403840904120322070780040101401075404010455120505000644e10380c14000e6480d001200c48a215003003550105071000c2c80840d210081008a064407074200d0f109448104402c5103091404014150345590380e6255024194104003a00b614090700c0c5d0342c0c407040c10400c14800760300a40f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 657479100 1250 657477850 657477859
    0xc0c0602010509030a030504030c142503020f0402070510090c0f0e15040b0f1324080703020409020a080102271e0d060e0709091203050705030f150a06020109050c 71
    0x3071144050f0000240c880d91242840d001c41c56507118039048031400114040208452010f09460341121008140f100b15200040608620400e9543c2030644009140c8030203908804032251100003420325400401900380610121003003005904150360031503d1402c42034030010f00311001848078210610442008040111092180b420044030b00c120842c1000d40c1640b28503524506400103448440d102c0d0f406810043c1a8003205d0700c1c0d402404080c1619104250180450700c9034034215214400031041520f04800050240a05690900005004d61300d02642e20050030a07000800e00400d00042950281d01c030800900c290b91428400000c030b111407125840b13076410401640c0100310018000b1034601c011600e0000c000260300300760000303000c2c142400303209008901e0042840303581a080000d14900c288454106140302d5031049040754000c0d10007900141c02003020070008402505030640007124150701d1001260b086001071034060a5038007200c0540d440d40c00d0103090003428094814001800c1e80c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 657480350 1250 657479100 657479111
    0x20f1e0606040204050112050603100f14070f090e070315060507020316050d06020d0908131a04030b150310050108150f0c0909070207080a08270f040c0e03030a0c0c060201 75
    0xc0c0042d10388101141f10200c2580d032080003440e9035070104240128418250000c001c1e03103120344c0c0035002600c604001c45250002d1800840d910b10b1045001d00c070300080550700d40301d403241131522403203140d0306c003501820400d6202c0703415819510003100e00b4802013015881e180c0d0b0322080c6206050a14105000c840d4100c21000800c00241d01c51300d002115030f40c0d00000042e541e920702034807400103000405003e0031040022a82c18290404483c081d810303a0f2800c40a911400880a80c03940c55209602004200c0203003200407482e001e80c040d076101840e01c001016222207108036030185040f0b500c01d078401e0099620800000d4810001c01074000e4221a803000030f00b1070391030f25920440c0c1c54400c62101724090a81c910010305164402d00c0104058000b00741924003030031140c28066802d8120b10409034460b170159106440e0021301074071400720300130040d241c00d0310070344031104100085c50851f0510050040f440700c4078065550500041001480071384403580341c00f11505004491200c1604644c0030744e071600 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 657481600 1250 657480350 657480359
    0x114190f0524011b0c030b01090506010f0c1a04030e010f0c0c1e15030b010f0f0e060c010207060216060b0d0f1b180b1903031707020f1e0606040204 65
    0x5010b00c03640119400b05900644a64001203842000d4030711210040c2e108100e0250402c4100002c0e082240c2c05400004100d9032154100c1c1c00b156415200310340859840d88000000a006072203c92120b40110100c0d01411941d01d031000301300f4000c5608a0000c0e210760030b0401250303042158a03004100c949080c200d824590303941c1410f11492402410b815842c5c1150b0050070845041a40016144102121041c0d08400c1c4000d8040c140e0039420a01196611251110b0326100f504a45095032469940000380070241007032020690040e0410080b40d5004c000060101c3c40500007071034400914660400c010031a410200700b00c0e00b880c00b59901c251f00000213403000c585c40d100c104d1100307504450032502c0714881680214029010364410841100c082d03400b00d91450041e0301404207004107442142c083c0042620004942940b030200501040c00410f04420f4403040c0c0b06440c5d84020306004454104e92a08031003454001c0d0080414006051081c0c400205801440810f401c041e069400354101801c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 657482850 1250 657481600 657481621
    0x402031e01360216060203010602070b070b160e060c1e070305060a1802041802090a0b030d0c0f1a0711060123010306032901080309030a140114190f05 66
    0x2c01804000025000e20590240007096040b01c540191003420800c201e100b902d4001e01035002407041740e016010300c5400055660702c000480b5440343d40861b030300220b59034080740c1c1540e90300607100103000c10142003c00c440c40c1e29000d000b0b00086141c1d8005100101030147c0051174200004076002d000c0c0c00802081000510014480741c00c025150710115220481d02c0c014628440003182c06944a400c0c0f070b08461404080108004c10b0b507009a81119030303641e41e4550507007903030102c0c141e80e80c00d68010048012510f00c50b425880303035140304004400074180141c84440c004082c0d0341c040e1017803120380c00038050426001441d20000010782c0c0041c00c3d00c0e41c942002c0b111a05500780301e894258040a070080d50300c3c1e12a030700c014003442e071296202241c9910951446510328100440c400c0045a5000100d00b84500009842d4100f03401030080c20704144c5a030b600c0840401103030b00c4d0344d011364035040c2088000c4101c4580754800d40d040c0700005881803100e140001035403c90716100c83c59615141c24003100c400c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 657484100 1250 657482850 657482909
    0xf02122b08060d031b080a030b0103140703021305090a0501050316030507030b0c22080708060912070212030729090a0b36010507020303070504140f0402031e01 70
    0x41103a0840c82d850081c1810344415005c003401d44107442c03040740741c0420404080302500c031410080da810402d03841c00600643c122107500c108206590300c080005240184260000e1001301e501035100c000700c99941e0b001c92540d1800340c83d090699a10307000103010360708040245002e82c0c80d0140300562998616100e031900d50f201400302509a4007504002143d40741c1e98001c4800ea50080244200303a04800c0c001154454820302400070715016140c00003410f04000900c00f8001c2803040080d0009c0045134071510413541c05402c00301e0b004a0f007150404034500040c400340c06c000d8003c028622014103144103208500d002c050ba003060500d0f900083c0300012800080c1d02c442194000c140e0fa043c1c1d2030b0846500c0001032564010b1011001069400c44880030b510070031001001580024006a150681c040ea00d83c00104c0707001c000034405000401c56101c01c0604584d0303004029000801c0c41c1055000306040e46e004658070203105010051610703041208600d0b00d4014140c82040c54040081400001030180 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 657485350 1250 657484100 657484111
    0x103030807050f03090c01021e03030a050604061d04020112090818010210110d060b2502040f11091504080a02060d14010807181109010c0f02122b08 65
    0x1140000d1075540c050b008480803400940c01c0d81c1d80700c2c588214220f5940401034803840c01409118084d003c4a8200039623a52441c9030a0095030a56442142c608002d000c000e1145030320a4a4400019a00440c101d5060000320400720410b5180740900002d00071404060300b094100c0c0c03500c03440d180854285420b9032122595202d51840001c48400103c0c03070101d4070400100214901030a0807543e0b801c2c0d01c0108041500014107014140d5900c2e8400c1c01c0740148412a424200503c4610310a0340ca048105014a8401000000c184134101e04201c100e40303680c03c040c256440001100400340c5090440b40c0e071403016800b986464030381000c5045d81c40e1005010000c0c026100070580e0352549185402207505084007401c41103642da940c17585e066036034540f881441c0d00e041c18240310b8160b0150a006000400c1d04000d191450b004c1d0b42030044550440c0c7c0328040c0c43c200003004e08080141d40e5000d641c41e426a414000f01114101c44100340041400e40740a03d00005080a8004040350054002a4481f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 657486600 1250 657485350 657485357
    0xc0931021005130807080307060f0204030201080c31091a10200f0327011707030e0109061a030a1115120703090309060206190e010b0301091217010e010303 68
    0x60309040504801c1e243e0a4008200318080c246001c80d6459000000e0204135001d40c0041c0310241002c803030714003284520b0002a00081d0030030001000030310f2100081c145600300c9035552601200303440c00c4460104110010b0f407001c5e2011201080307007103580d01410341d505034500c8142032507049010000e101107050440300d1050000101c418040c003c0001c0c0c1443e504481c4c242513401480640c206d103610307944484140011000c031148880f000f80d0702c0902c512110b04c010b07100e900f8517002520810300000c030010480010161a1103290300540000e000d10051580305020100d2450800400f8032880c032403100c01a4080c0c3d03c0f010030300000c11508810301c0804c400503143c0130101080260310410030702c02c2c2c0708200c0d00e0340c4296040c480f80e2a80f6a010350a4540070396a280c40701522141c08070707110402920307140c00101d6900039064281c82c1d2984070110300d543d0038000040d11f100f00408a1b007501c0c603000e41500d0260040c40740d03a100c907400c4488100712201901c207071103640d81001103a0311101010700014040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 657487850 1250 657486600 657486607
    0xc03061a1e10120905010f050c07050d0804150c020f100b130b060910080a05060a0e0403080a060f030b011d01080d05090a05090405010b0427060e0c0931021005 70
    0x26a03018054040b40d0f40b890718003d000d40302a40c10000d02805020301c4001d031942c641000030b040b005039070b010b440000394448050442a5030200f01281c56142c041d02c04c1d83d1320310700d03618040c1c0d07110018031070302d9080344c0329802410f41158030346102824404009031032501c6608208020000307a80e40c207004404030442003070004225604c00c001c40c07a640108640e0300d4004e800480034000c29500110102c0c4034490350b0302d05203e0b03075032150240940c0e140c0a100f5100002049404a00043e001e903c0c400d41c81030040c40005100395403020001070f180025070055078011015801401a404040a11150003419031303160042c0d54500741140b5a641c210101c0c03482001004149648a5a1034844850052600030002440c0303007020b04020b130003060300c0e0021510452900c0381c40c3c04090204900f41e2003c01e18040d0784440d0a4080d19868058004510707400302a020f54075604c0040e94540d0512405610496100c0090905d801c1c10b0302d03074100d400c1040c40b0080001e501d01d0001a9104411614007080e11714000e500d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 657489100 1250 657487850 657487879
    0x110726010f050c04150e13200301060c020109081507080406020f07031706030a030e10050403080d060602061f03080c030c010f020d06060e09010902090d0c03061a1e 72
    0x1031100c80c1201c1e40d03441c10201800958020007000d042628994481161107100e0000155284503602414680168064a40345c11111f82c6034490142c410324510080c1c0d4900300d112500c103050380242c20910104a100744213900703650307020440b00050146030000f402c2502404608040c0700100505100c100101b80c4001000c000c40d071740544061a059003081c40d00c0d40f02901d00540001d180c1d1902c08005507a1a000801501d0300140c000c22164054950303c021a03540b10501c102c4c07001101c00d920900c10200000800a501c006c01001003281c012000551745091410003400c20402404080806580d14040c0c4050124820341c041102c0d403080b90103541d50b00c148640c2c1c2c158010b2074107400c40c0d035181c03280d03c05104407035030001d02c24051450020000c05407035a8040c0d810003034003058540c000000c40010710200f0410384c014034914038000c0030782400522607074451702c03182455002141e065842e011140101c84414944200c1c04074100c581e482103011400307144001b00986400310b0302c1400c60700740900 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 657490350 1250 657489100 657489103
    0x100f090e0a0b070c060501031a0c0a080c0a03060812070b0c03010b0f0a1103070b10090603030921080c0c030c09091b010e031006170708030a0f09051c03110726 70
    0x1004d00d51184050241e50780d2420300b42100760508a064080200c1c26000a400c040041c04a401e0545241c6522042d525864141036042d000001080240b40da038140215090004202d811803800507900d00680d191880e04d4520140c10000e0681103031180309000500c01194610b084d119030b0341c20080040c1d111002001c0803076011440030074502060000003490400e004480034458401c401d42c1c40c824007160b42d2032513031a040315241c0c0700c0940050b0113082c05118681c2a030f01d52000d032010f29800c003a50041a5102c4c1d00300c99001114121650b84010480350081c06c007031016003006201240c00003041c0c6016411140c0300e000c688908803d022031050401d100341c2c0980c030004a8020082c00311040b110100c2c2c1900000e2006000d01c81e4040f82c3d202c400e05101e05c0000300642658030b801c001e941000301129080c1c440e00807000d00034043c0099001301040a44035595138001050241c0a06070211100d03040c05001405550042ca80c1ca4000b4001070100d002c210544a2035600000c3c03120351f503e41c0340d40320315 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 657491600 1250 657490350 657490367
    0xe010e010306020c120c030307110c060409021e0a110705060301140415081b01032f13090c0f1b0804050f040e06150a06020a0b01051314100f090e0a0b07 67
    0x55103a2040411095500031b07000010303521800d82ca031180290b12140160303a035a548000b40d0f003580d02103410001031100c0100b40c2c0290155000705050450395155200a8440b190040d8443c000061850301444020401c2000514018507041d1105440c550601303c1a2040f1918289864040d03a00c9143d00b002441c5480c940400400041c002d4a41034910680c2051034202004801400a420710b008104858800701909100c04840d452030b0003507258a06034013281e500031000302000c81c80e2580300069180001d00031841140510741c2c45800c0542c9980c4003408144c003080c01c3c0c2407500c60010745140040e080508941c00d940c0b08035604e00710f0064107000500580f03070801d030404c081d0050205102d08003e000340c04001c0781e071046030b402201540741c0340102d80e100c4104070003902d95039408004000b40e0408050301c0300241010a00401c0305049142d21064581090307604035503070913540f03500f00b143c0c4600d4074074403029020507013040c094048250081e41e03441112400c0502480c0b11030021a222a0264031507 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 657492850 1250 657491600 657491623
    0xa03300b0105190801080106080102040e0f060a0806040b040605070c020d080d09020a15140c03121302030610060e0102032b0b2115220215220e010e010306020c 70
    0x2c0910f1601020300007803605800f803082490941c280140032540c01010300a07182540c141030700c020003a940e001c00c51141c000000e030589400041a038404609000309101c0c1c03502c0b5034014007060065052610304481241e9000b041c0c80c007081400c0514200503a50041c942560580042800e070300d98155900d40b00040c079022400035805000380071b0001d04210781e046406c1243c0b081c0e850311810350020004240700ae02c1486900c1c1540c0d0030420005004000440289412405842201c0c0340d42d403003940464906002625010744180740c495040244035400459401c40f02d100703101550038150000400d21400600309156501007500d095a031850700703402e0344082001302d8002c0441002407492110400d103880e00001d6102d8070301801e00d084014042c2c0c0700c4100d02400140002e207007501c0d09940e40209500b15540308903440382c0c40526030f100d0300d03c0b034a01404082007030300c800610074180702d405420b80f1700859020510503180c9100411040001c00815411039030400d10260780c42e8180c4004504110f14551b6 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 657494100 1250 657492850 657492877
    0x60c020c100806220e0a0210050f04090906090b0a0e06090c030d0e13020a05070605012c0a0b03060709050109090e0c0105030a060305070b180301090209060118170a03300b0105 77
    0x54032014003000182d071b840c014025246403185006082e412549403243d850182c50312030701000200300c000341c1940038900d00c07402082d0020314844550b481d4809004180c640301d10a580703c1c1c00c0041da0500070b0100d85c0c0c0007442a0b008011044500b00800d84410540c5444030a100c4c016111003010307121004860030002c1a100c04564070980c104020f8241d400590042d0b035010b01c5c041c00464210b200d000b061411500d00d0703004508490f4403100407a5040c10040ca120500f548548040380c094404111803402101281c86900ad100d00301800108042901c0c1d0020070340b40d050210000c402e101c04201008410020701e06196070f640c0700d8024401601d11a8401011841824000500c1c02c5115010b440959226040504400126010107090f41c0d40c0410180d0700450120105529600440c446c220302d0b51007003210210155115104801c241103045038002c10f81000c0d412100301907200c418103501c03104d03030486541c8004030211948000565805032488031581c1e03905044151780074200340c62120500d1178 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 657495350 1250 657494100 657494111
    0x4f0903023703030e06090304052d1807030e010209060322080a02031e070b0720070b03040201020c011715150a02010608100b09150607050a060c020c10080622 69
    0x2074018014600b525105045024000200790741b03050100c02c030f80c2190030042011004000c00021010110320207118016080e1181940d0021034a55959056940681d0300d0014000c0c034000713070040c081d03412030342c4461001c0c0d1041007040c6407a038400c0c064030f4000040d0300c040c3d80402d6100028101c0744e0000500500b10070008075219400c0c0c2d078000010904c0222004080b0580002015107650a00412000910101c0180e00003080d4621032080e6160000080d00388a043e0745203280e440d42401c409030099071540f00f00100300700030340d40c04105c4031010140a00c2c00820056605050000c4c9042c0030700401415020700000e4001903031080035246191080080d10380c4d40f107044d05000fa009001e00d22aa900318000c0d181003200c005140d02ca40308a540c0040c200001c996201080b07012031040b002c1c00ca507489030080c000da0012a40c00c01100c1449442035134002251036941d0300181c07801071506105881015040031558881c0e82c42610705800ca081901c60060070619001c0d400e03400144000d89550b198540b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 657496600 1250 657495350 657495353
    0x51602030f0f0606041a030a0312110a0903050d090b07140c120f0d020f030909040f1e150513060b040b0907120f020c03094f09030237 59
    0x2080450140d13404480810072407410100d02203180c85081c02c250303816080003006a02080c025500392081d081e06840001c2e00c0f1021411114664100c80044030028100c2107042c4108441008100c401180f01e0a141e104203281081142c100d00c900c1c1070040600d4584075180200c05010450324101100c010321203040c0c800c800c1c6140303030307981100080c040c41440ba0b50740328600b032400810001400e001c660003071460803d4000c144444103401400c211580b40070540030b00c0200d51154445c4040448011b843c0180f481031f0304041c52860304e848400b80c070840c43c2405012483c20081d802c904402e40c8040c010070701c070b5429000100101469001c0d130340c01c403070b51900b0044556031210100007000180f00f020400c541d81002c03030000702d000d2110240f0040d1b204006c1281a031420f041c00d0810059200c81030b21294000900c1c80a108001160444140080b10003292207418440f03503004400020000c100141c0000382c5000b5528041d030482c4214803001c00c900340143e0186071440b17140c8808038a00a01c22849607 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 657497850 1250 657496600 657496603
    0xf03090609080a1b1211030c0102030405030903060703021201140f04050406050a1104050a03030c050a080a0203030402100e0a090f0605090c0a2303062707020f0d030c051602030f0f 79
    0x100d40f510700082400740040c0006188241500583d034104c4c14008407403085001c1507070a0102d02941c0ca000b4882131120310443c900900082d0322941c4160080d580312041d10007814a003402c003034450002d2500500c94031405103809140e082c1194280c154a0500590174404620f41d80c2303d003038146801601b05020481844601d401030b60188907c100301304404084280400e0103802a4001c0b251b1044103150208086846005105051401503043c1d404200076030ba0f80c202198050704041001d070308003000704010351801e8191440b4941d150b04104520070b03840400100201d8080c090a030000c0e0b6995036990100f481540044090000903200d000c160030000595034840d00140041d800083d81c1d80e00f07a0b015078101c04039500a50455852441c103545508007041042c0700820b4005205007203405107605c0d2040d003417030740300d0003001c43e500039000d05243e940003241000740495800c0181b40c103018110f803080383e00008490305181c0001d503203000c1160710b2001a05103000d80111030124440d1081b2044801070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 657499100 1250 657497850 657497857
    0x40902070c050f040b030703080a11100b1c030206072003040311090105060f030a0f0906090305030f010806070504060e0f27090a030f03091115070303150b0403030f0309060908 77
    0x22503100c00c0f02000e038801c0000f03851018800a0b0075400c4580304000045e804005094461040d0800a0f0203a201249040c40c14013000b15034001c0c1a100d29408660f0308004503603820030008070100c00d14049051b140a544ca25010b0050700c1044078180940c020124410720f80d8018040c0341d030949603540d07624105144881d02400c64903104086070400021720385054411a190700c035440c50b2460071540c90760310000044c00b061410701d1b4010744030003440c00043e00360b101d6417040310700c40d031660342c0c9038100380c441c0b1044940140c000b11000d5200c4814803a0407034025066800701d40c0c1c03919000c0d100403141c0020554100103e221144c01c64195080545800480a00703c42e1140c5020300e401010356800d140703030350760304010140036011803100c3c003068a01d60f2183e040111a180107001407409440c6a0340803070284014042c9481d46107030003042d10001c02d903140c000ca11140c03803003803429080c0508125a0400c5441148001810f00241a10400301b40d80650000281a90480000c0000c2245401c1c952029403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 657500350 1250 657499100 657499109
    0x1210020a1d0406031a19090c030308070e010e120a0516180204150e0f0d080307020106090603020901060320040b041502060f370606090e2406040902070c 67
    0x1c000c444071080d03030405100f03407004c80381c000d00c6000c460b420a00e5814440e54001d07045640f04e10200030103040c1c0c000540950682c43d4840c000b0900c82e6440c50a0040c0f60b00f501400202c1000844840321407245c2c1c0c040d0f414441986c048514140400400301010300d0810580e000400900030b4040900b62000c0181c001800c640d10a000000b00e4540118150101d20981c0550f10022201002001426209402c041c10825000c0c05802001030341200040c91802081c5046410090000401c00342e280d0a004d008010300b0074200500410381113500041034114140100010150344001c00c2c2c2d00303810b1000342d140c11040180f1400e0b43d29074484940803443d90150081c82c00c416105100001000c0c0b0002d0418490400c0c81e0149030700d81c4807d0a034041c59120903100d03082c0c400388042c501d80007e1214403191000407000c80e00045107850003101418003c1329034495058200c4943c00c02c80c448040d0650100c80d40741960504d019030a01500040490081d600001445440880d21004015070406480d054a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 657501600 1250 657500350 657500387
    0x1020d09050714010906090603270605220803040210090e041401060b0412060c03060506280c02010206040f020406030b070315050a080c0904061112100602030306010e1210020a 77
    0x241d881d0f030040d100000140b2585c0006001d0903820403040b4441d5000444045808000c10030b0350b05008240d01600d00c4c080700035501031759280d0a215501924020200c01c00020a4510783c0c075652546604201d400001c0020f40982c480e0310082e4062032050708100c2c080c03e1080b80004950901c0d041c0031280454003040954950300c1c0940100314030440c2c50548044490841c2080215022a600c400141003040c07806000c4c9510342c84041010358070030028080040004c50350180c500c088801115880c03131200e648005021441502d8009070340d012a00310b50060b00207421070900c21039403010800521080c0e2024000d00500c1c0300f4418020b500d80c000c0760b05410190354240b061034540040110341010761048a403e41e00003020b0a403e4103002c10f400d64014010100052680c502642c402055031043c6051004003054004001c84045039040c601c01034107180c4010750a6140c042d0028081001c540f90300c0e441600303414525101603900704800214444003000030b40d1a0905020003520b00307800c11a010256 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 657502850 1250 657501600 657501629
    0x12050105060603040b16121e18030203070b041704061106100e06040e0c03100920060d02031909030e010e0303031b030606070c15080a0b03070b0c01020d090507 70
    0x214030b00300041e40c1c02143c11003400952070705da0080c22000228011443c406200c0ca00755180c42c4001148190b11070080c2e4a40c80454014446002c0700c100e07188003008400c01412001d500020070b60010617102d4280d84002c2c0030855403214100300b10a04100540440a5400090042002c0b503001c8092040c8c90407000c01c991641d16103000024511342c65009548160391a030b03000031010b2034103810010780340c001c81094035945010400401d0410782c0403201c1c01032450b11a10b01a003000104110084150040d010140c040102c0000148461298510020600d030b0003102003120050712001c2802c41d02149001040741c88500d1030040e02000c94a11003d000c42d861007918250707801c3c0801100d01c591880015010100400000c3c0350a40e0405032089401c030300240088800200301d858140003610003500740e20008900300c2801030038071200904512000e13040080c080b415880008a11003500da008100700d8a400030030400c140240215112a0021801c080f4040b0600c000030604205403000704c00d880c002c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 657504100 1250 657502850 657502861
    0x3060510020d1404030c080f120301061b0c05042a2a061d1b1002190201021f020301150201052403070e01090f0c0905010219110a12050105 61
    0x80c020321a4000c02581000d002014500d21507103401108080070081c0e035080a4a039218000c0d039500315007180f9490f500c103a0380d25140700c50400a00d2050816000c05034699810104001c0180000c1201c10b008030482244041c00c20518003d1440580000342c000c0128203c03c070305c00c0002c0c0d49401008901c041403080410b00340c0f03100342c09074400e5407072a2400500e410b065400c050300c0c400c0000d40940e80d86c1d40e0340032898844441000061f10b05048070005205410060714850050a001560302d481707418a01c001040d41600071604090201c1540003159880da01800140d0412188400c51b50b19060503241d90260300320ba0b0703800307541603515510403810320340203c000680c04c0342d20a03100101041c1c5094509420400301045500f0400001780c00d441c102036540800b04c458280070381211407081e80b500d104030440507051042c0303036100480d450442110761400001079103549030850101010b510100300e85043c042c1ca000c20003071200014082e541110398030380b5403821802956800325800e500b09004282c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 657505350 1250 657504100 657504109
    0x10504060c0201110915090d0b040309050f0f10020114070908060f04030804080a0504030206130e130308180106080307060608100e0c061810020f0d140d0222090c030605 74
    0x22065418201161500403840100895038107606e6405894106c200710a007825141d080719080114400c8036401c281d0b0409150280038401d80d904100d0240310b0219004e0b401d42e85d200c0e842407624100781c6003403891580c0e0003c12030160169a810b4007001c025801840451076019150b1401c4030490416102c0350345490420350000041960058000341c0e20710040750104070003500a12702c1d290142040c1d032805035640c2c0803070701c181c000f14000c40404038142003c01541c3c8005e805035a00c03100164160ba01d00000da500584102e40180805034280050660b40e12103841c00d50203540a0200b038412030752164503a10741800545000e0080c01c45a010318006d11107880424001c421511422001034032203100e88505011254200614040082140078034440241c1c0319509000b1100b07910350b0141050040051401c0c5c13900310410121001c100c51030019a80d10070700c10051341d8015005020250740d460071052800746c082d222105003a84240860b600094014581e40991080980d5860500c80030f03940300c0400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 657506600 1250 657505350 657505361
    0x20c150c0a1706100f0903050601060305011701020901140307020f060406020a090b0f0a030c031415010206160903060e031c0608240a0b06040f08070302040e1c0806030a060e010504060c0201 83
    0x544c0103011a05000c50907405501100740d60f03c8280380842030300eaa2174550381d00d804420381c000f0020075038640060041169004403014403840384e030025468441990b00003403000050b01c01e4904451400710100302d0203803003403100c1030100480500311085802c042c01c08100a51040f0340b02000b0070b144405c009000989081903404c89002005000c0c1446c0340f11201364040c0c01c108403074908056850300c0450800070b9031a4410f0280d070030103200440c80b01006001928025010300f50701559040d541d0030000e41035001c0c041d14240c0e0f40c04940441c3e10f240300300900e40755004607040c0003c00e81151450500d041c242c1d912981c12a900c01c0c04903560059140881000042c05d68200008501c2040015802c8845a000300142c6500500040d10b02a910b82c1340c4404812160408100c50308000410400d502d8980204102d01004c43c3c064101280c2120301400c0300345070740203890240002240001c005560a0014068082e0004024004038000d02030040c020a8100d0b002c580c441d143c510790165240c03051080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 657507850 1250 657506600 657506611
    0x5100e0105090c01170c03190504080702040f021812030c0303040f03080106080103030c320124050904021003090b070c030f1404060e030703060f0213091b03020c150c0a17 75
    0x1e1a09075214030006400031347c401490301e01403240341c09003244622880d01c07800b403046004520454031140b1502c10041515814400031a049006010000840c40b880c00b910f255110100d032510040540c1a040c2420b50040b2454204c4d1400040208014051030114105c103040c4a0b81d5511443d0380c031400140c80812003804042d000600b0308860800140c00a02a440c84812443c00340c01c1d01d814184419800d024100c110101c83c1e5140c803152201480c150204403004a070003010088000c0c10031001c104041c0c0002c1000e8495403410200d0001e00303002c2d5000070300345900050030309224541031201410f501c410311011400650713410207020400703114001c0cfd5096144182d1040385002c0c58540215040c841f4200300c00e9260040010000c00920030b0310501411082c2b00102680350b440d64408444548195030100c02024100080c804210300a0100600d500100c4d00740184c450300041c103030b5442c0044044020488000707000902007600e08040207022000344070f0f0303514940700c030b4540340462036075005070740 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 657509100 1250 657507850 657507887
    0x8070b0708090a020925021b0409050c01052212030f020a0f02091b04082d03040618080607022104050306060d03050705030a0f1409031905100e0105090c01 68
    0x283c0754014544a446030740c01000d00101e05520b04601c1c40c03200b00c9210345021240169000d01d414507a4541e00c3c07510784002c00c200b1901040030f940c3d11b458080e11900d62992290401100066507000355043c0c100c460b031000c1d40a002d1948503512490700030175000c2620760540100e241000c2007044030784001241c0d46a241e0042c2030040100f07065090016800f0080d28210300030101c13202546000043ea0064001010000010700d44280f4100e2051386a10004d041d0b005044100c00d103078500b581000003150101d0f0940d01d802c1500c4600b0820740b12441e2200d4002c01c050b4000e410a2041042e8002215821310811009016400040600e408401d1145114981c1c0540094000070440d103803990221468074004e050940c9000301941c0c4890441e40180084404030302120192003402c0d074020980841418030120040c5407480040000b5038501207440c1041c0000c221030034000800005012000a08000000903c140022600c5150290108460307440e0326201d4140b00d104190b200c1c01010340a03606032030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 657510350 1250 657509100 657509113
    0x10314060f0f0406081f0b06090102030307180312030e070b090f0423010f080d05070c090203040501150801020d051e070f03090c0b03011e0e0601110a020d08070b070809 74
    0x1800b40040c56144440d6000d41c0e03481e800100c100050001000c0701d01c80300150a495054661018102c41f084403249005007001d001c0030800366000070480c1d41203005410030b114544541131501c40200c2c00754000900d02124003004910854041c0c01401115003080181c6440d01d03200c101c0e600040c0200b45120f540560040d000d4841410164001200301d02c0c8a007904031903810541c4040400380c400c0e44032200038409071034200a07190062001407580a140d140c410b00e040c8560b01e41c41e00140c1c02d03008500c030742903002010604109017507022801030100c01c211803000d5580ca44041c0c0c000d41182c56800d24003400d201c0040c042020b100036040c0c0700407001d9400425a20b400c041101d441480c0e81200c17090569440014000c221500c460000400c90102030a80e69818014540c0c004a10b01e0030f07007007114500c044144000e54244e6002980440c080c43c10110b003980418409203840342110303020f07411140b0f01d40c0040902401d40002c16181c1c0c0290220016912411001c40748030786d040700d00003566004030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 657511600 1250 657510350 657510379
    0x82b05070e06160609050606030f0a031706010c0212030301080f16060302250b0106030b0907140a0c140703060b1002030a031e0c030906050105010c0b011a041a0901031406 75
    0xb1002c0e002c400405500e01c040d54080742c4c4c03428200c5250640550391030707112030b08000341031408110390404004460301403c9400d60303956028164007480441041921603040000e0f41c0d6034811140340100640013810000707000c3c802c0b203e19440e82d0080c050b0400f0340c050a40d0303204207003030700050141d62084020b0254624900c0c1c48800c07002034114141c0703100c14494480f80c590303072445d000f0102c5611034050050907042c3e514095000d4101c880000030540a440d41404100c3d8980d008212019400f5001451595455640c4803c58038000300c010024010030f400c10b174842c040c070800075902040d81e03c00d440400000c00d18400308881d400b4440d404500680c020005120464480d42010799a180045950107010400c1a000015544c4100607000080c0e615900041800214003070240100000e08052403484039580302d40501e92030501580300703c0c401c0c50300108400e81c03d510440b8000d00091203070401401c0941119603043e8048420305000a003043e0241549600d20b4030030130f0284600800780d49052560 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 657512850 1250 657511600 657511609
    0xe0f0d080c0d020417030918090a02103c0309081b01060902042304060f03020603101703030103050d1b060f0b15130e010602030a110a082b05070e 64
    0xc45000d042c0c580074000000c0c1d5000903040035003030000a401540e15040c01b034003031090b803107036004c02c000301c0050b00030034003000c1103000c03514540c503a8042c2d80c1c480802204103419243c04401414a00d01130303d1080d0544c00c003004d00184400d007912403c000810b400d0802c181141643c80390000905a440304000d0050070008020003643e4850f44207002280483e9203900040898101e80d014151101c0d54642c800c0c0c10142a00c010100341004a46c2004400e0901090103111a40c600009008090000102c0d80000c150b148410042c844440403807503804850781d21039101d800130701c07003118580f08620050701d4080c0647c0d1028150144032264503044403441c0c99401c054089088807501042d5a039038040c020f03440d4202d070102010380e03410a407aa100c01a0f001d0104070026548444032904519005018103503005c41203401100b034510b0a80182e1010310a000d080aa0448000740310010000d00d503c803600281800060721090485c68003030b800000c0807200e0542e082110792800040140007455080d06e403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 657514100 1250 657512850 657512857
    0x30703020319020a0f150b190b0d0608012a1106041e0b15180402060301050f060d06060c0309050d0c0302040c030e0303130b100e1311090a0e0f0d080c 66
    0x810b2046402100c640e07291621707090040038040c2c807500d07550302d40c0d4184c00300e0601030708031440c906440b8200c0103494818a00c66102e03490146500454001030f070140301101a4120723a000e44403543c0208071060400768500282c0c503411100d0403040b101030b038680c042c0501441c01120b26100080207416076564a03a5800d07007001440401440790305202082d180841c04c1460041d00c00c40c2e131a44200700c440680c004121015142d01191200c49004800b0080142c41e40403d890459000340c404803a03100a01002031610300914400d032480c0e900c0c4ca4000a00d248d1b201e15150116402070b103c0301039554a810500c86801d03101e420140603248086010801414540d1104041050a02d030019512890041c42c50455100303407900001c504818800d0b000303202181d10025003210a49000030700551401c00125500600242440c00c032884807113055052100c2420b00c94013a60b40106071301d440e442c0c040c0703d100041500904200c094850070043d942d144000040d0190100000c0e200c0c0900d50b540e1900305d000561 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 657515350 1250 657514100 657514147
    0x1e0c10052815080307030207140a0503190b010e0103030519090f0f0f080f19030516030c050c0103111c200307031103010302060d020a031103100305010e0307030203 72
    0x7591806981070084410414480c600744007002050503408404110001d0302c2c00d40080741d16800400c8288002030b00050104203c0341c000c01200d181d024803800140004a5039400160035020764800d0b9005619050505520988034240100c0643d0300c5800131010400240402804078004004d98642000526491b4500702003d2070400b00f40c42c2c0389c041c1c114022404d5440000384030044001400385641102002010b04148402002400f440003400c6079100540f100b201c554040200e80036003810321034002c4601c25080b14107040c1382542545402080d00040c0c20054902e4012440198801d620a0140c201c4000d40030b4101800c120869560500d501d01382c1902c4000259107034600807402580c03036440180c020069540d00e442c0d00e000480601603c2110003a030000030000c2005200580d42d40b02a02c292200c00d01c3c0060725440c0d11203007580244101c2c00c0003076002c10f004c0100000c41005411503002d80381703d00024172941c0b4120400540d80d0040110041c00341c2c2081c4200ea198550790750307030000c261 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 657516600 1250 657515350 657515371
    0x105061606020c2118100309050114091009262104050d0906231b03040515090a0312120c0f0905100c030302030a11040b1e0c1005 57
    0x900150341d04012a880740d0141e02c03494004240c880e581d8018007070740c510188a180445844d007544c4126074081041018030461140b4040c2c002401511b100b6440020700c00d80c080001c10103001d001d18441d0385600d00315044441d0b48100b8040c0703601c01740180510711006502459440b03881003424040800d5044601c0c1c4200803200c18003516000c81404600c0c0303d0202c00181c1c0412440c01c260a15508080c10025104180044110100600f5600c460224009800401b8401c080348105c507600980b4412000c2802c400d64005047c101c041d00044000c1c0200c800c21106a82464000568043c560246801095010030341c480c0820204222040520f040b2001c0d1800d81290340c015481e00d400c4880d612141c100054540319000110364214025801804080700c01d4100b11140403c01002081d490300e00a08064002c00442c64035001a0015a0950244000262501e480e512182085d4011400f107042d00c0c14017500d1040b002c07640700c0403140f6501a020250000b40c3ca50440c484c041e14003d8101e2110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 657517850 1250 657516600 657516637
    0xa200f0f130f050604120f060e010905070e01090b0306011401110607030f0b010512070309060605060a1101050105060c12070c0b210105010305060f1504050a0321020304030b010506 79
    0x20040c0310002480807031a01e5151114090410300c071403506607040c0d000305004280c1048140000c20002c101612141d0348a40c2c1c804940d50140340c01e5019001050f2110070a6003007060403020810f01240c0101502c4800e018451307107a0740c0c0c500740310503101d010b04926003681201005000d1203a40c01c000c410072a00604000403801140b021203850404200d581e08002036541d18000d0a41e50b80d80a08100041c0074038082d81440c0c122401e03920b040c6c40c046d1090040c180e0752001c0100f00b0103580c000c0c0004102c010303c0c00b621464407000181c441100080003084c03551829001242e00c0c5800016120010186002071614039442803410103d42c2c0040801c0c2c500031500140003d03810301c00350041294008980a60342021000a0105031145040c3c0000e0b0606082008105060722542d403018440401203400c00300c00a21440310000610541d0050394000d84401e50100c18011200a07d01840303c605281c2001003108030301c00ca0700c034007640c00000c22144424004000902c0c0c171502821703807a408044800d07075 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 657519100 1250 657517850 657517867
    0x60f05060306060f0a121b090b030402030703081c05010806040f030c170a03020c0624100903050316030f0e101103090a0f0510110319120905150a200f 66
    0x28203400c00109417000070011080008440140e011741c0300007140b81030f071054081410300400341241d0028005c800c0c2ca980d01100180942d9010481d08004603001501030b9503071408500c1d0f0503401d2501c0c02d580708001d03040000000c2c840a00080d41481546c105080d081114a6a50115000200e0440a40d00c2548400f088068044040010000c11025407401070703413100c443d00034a04041d00140390b60b290002030a00c08072400c900e05d83c625801d02c421500e0b40d4001c03003200802d490b03852490300060481d1002058889081081d29031070500719019440b000c2c5584c96104084800c0301407010b155402144040500c00b8a0303009000605407003604500340c034203080107070b00882d64040540e03000b0702185030000750130410340c10325000100c0c010240b841c004100703100e0106d04507a00c2c030445a4020001c05440201c40800348920140402803c00c6c14080c070051500c0d09015681c0c1e0319643c103880550f40e04a01203207c01209110b110000100c10b04d026000200503101c1070002d410540e82c1a031080010080d018 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 657520350 1250 657519100 657519127
    0xa020108190e101b080a2003010b04140303030c0d02030a0605031c030c050c03040302310902090f060f121c0816020c0306010b1309090303050f0901060f0506030606 72
    0x110a240c90700003c1490b018201c0818040c4c0312100c881280c01a90107802011080c1d210b250a82d00c0001c0f4000483e1036100100040d4040e50030198600c80750002000100310b81c64910028800c40e800c1003e890900f844800426032a8070050703a202644200030031681441c802c5e00d801441e8000704440780041c403030b036842000c01e061003a4416103031403598050811041440c1c040c07040f456504aa45481c50402c80c0b00d004181e42e9118601010344aa244016151469490710b400c040107025104c800030714000300760106002500345054124418000c00000580109510760681e00c6200010588810300a15005111000c2c1044030ba207020340c09a4949050b40003040d060403004800c1644c1c03178002500e440c403100030300300070162034400c2190801d41002c0c01d95600060755a055400181c43e0319940d001040e1006100c80381617101e201e210f0b081c40b0300c0d40c0601d6010340c820b81c824080f00e0300300c2c1955070722401240e00705c0d410f03406801c115208024040c0568207101000e1640144090308045c0350a50305039030315 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 657521600 1250 657520350 657520361
    0x602090409060c090602010b0a050d05010b06130312020d12090c051507140a080304081b070f051003140a020a030b12070303021507020c0f18071d0306090a02010819 72
    0x25100203480b03e20184000b9800b10030000140b41c0303031008104588c085400644040c2d4107100f407910546062031480705119086d0300450021320000e0043d9500c2d910450030210190851100380c0c0c1c40c2500c1c01c841c21901e0f0001c5044c906100d03141d502d411503100300a00c042c00a200d0b0f5001a01c851030409401714158440d00c20040d11480034125036500d4103da403400e240030217000c0e00600c859400021015002a8240d02500e801584c400032103a25036841e0140e44100890b44017620300e0503c11198001a020950300302d05095400075107625030301100c601803d40076503142c3c00c80d1305d45080560000903d40040303603000d01032241c29450080703016102c1200013901d240c038401d01540543c1000c0f034108205a0108800070f45503c10311004140f0b45400b64010707417070b07038500c05080e805480c1c14040301100c0d44e1012200340303c00003011980495410007800061126182481d408a00414000100410318001030719034402e4920b68000d00219807907600440b1068005441c4103144000d00040c0c5055081d60b014a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 657522850 1250 657521600 657521603
    0x80a0e0604061d150114030705060702120f0601030f0b0a05070c060b0d170d05070c0804031e1a06030d09241808060a14010e1f09020a0206060a06050c0a0f0602090409 73
    0x1182c54550525503146a06c141e00c2c07584170310a41c00203a00300010b454080560f182190100d42c0924106c00d184801402c04090680180050003450008001c00110100c0000100d005456040859548002100031601d00362241008207120b003008000144590f0043c204200029003442560f2025555072540315003a00304480d10392401103984949420a44a01daa00510910300008070307202e95200e003440340c0304500019082240c4012090040d06044080c4030180c3c0d400108007444090200003101084404d0345c0302c0e4424000c2d54510419a0b1041105000b41e8602e07104094041c0fa0032011800601c611000038410f101080703c0e240548440c824000d0001d10050000e0081032515804000444580812110315020004010f03c410a0941e0100c1e44c000c003e59860521882c07118441c1000d038056a002e195024000103485101c1c6601268030740c000d2005540c80131609071100c90940c0c65010384400310b003c0c1c0e0f2050040c01e0200300c5094140f81101c2c0140401441e024600011078140d48000300d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 657524100 1250 657522850 657522883
    0xa06090606110d0212040909020105210a06172e090b01030b0c0f0d0209040905010612030e1e061312060b13050708060f040b0a060f080a0e0604061d 65
    0x30218144424400d082d2030b52844d201030b0010040a18842c0440d0245015a2101994405882c02164040c0003141c0800f40d0030f0100c01a1600c00c0c80a580c1080011103015030102e040c0400081c44040c16500074a181024002501200301e1180c082480801028000703990304681d4a580245444140718003940f081c0035108505403503045003820308024401074111145003004002c0c0c5c07080044000160740c0800e4944901682e03440310280041c01820560300040d02c1941b0b0648002420340d080100c03000c80782d11986035202183d40c80310401046024000058150015500e0801000d143c217900070410f001150061055103500e504120f51500c2040d84201c40340365582a41d070300c152a00c09481ca102440c001c105010b50325103240d0080000601402060080c42e82d214810303460f40d10354000c0c455048010f402816186e0f03441d2002854100c1c3c1c1d80c0700002048a06c1c0100d55a810076018a0130303041c100c83d0041c21291216560314005110b4018040d40802d809401da0548000900c4036018400b8250f0b07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 657525350 1250 657524100 657524117
    0xc0501090f03091a04240203092808190f02010203041707240c021e04091101080702061012020a09020d292202070f03020a0b06010807170a06090606 65
    0x11981c0084c0c2c0881000100003c000703102c01c0100d600c59444c0c3c5150403041d024010001c00c044102645140902c0820a034040c041580210400c0003403160381c58992800031851080c940c0d140c840644038482d50003400240110405404045400c084102484610602c1100c2c0360560b6142d842c448546015800c00b19508048000c11041c000c2003c9104540c51401ca01094268840030140a48142d140001c0c0108500200c08a0800440d48000c0641c00064000c0c85411618544031501805205506002c94130f020003040d600d61000401c40e1094801c00700e444581400c15402d2200210398280880c1d22a0b0050004216182a40040d04c003680e1000b01c003244407031ba5034440603404062103499003810b44082e0740f000001e40c1c0328a000d0008440c2200d00400540c4a241d44002134801c2800280000d20224201800c150740003500342c1100d4042c10401c455074854030011198031030241c450000045c00030f5001416200c06510803074200d107035400c00180542d95213002c94203440702c5900a0012610380c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 657526600 1250 657525350 657525359
    0x1205030706060b21100801060305160e01030203030409050a09060f14010527150315070320040506031009061205070902040605160f02061605010e0c09070c0501090f0309 74
    0x5014a0000c2e01c4205215803d2000c10180d1310720294442280720201015000400c40000300c070204240030342980b0b03009011140d203070b040095403001d10b56140048406802d400003410391405190906036030740200658541460045480040c0502405172101e15503282c41c1500080c10b90310070501110340684000c27400664004400446a4050b0701a60244c2044c02040c0c0d4200000440d1128100705a009a00951078290800b001480e0300700c03103641c142c840d191268081802038050a40300b07070711559083c8105410300e43e103820407200070070401d1405c48040c0400c1c4000e02d80790307000e103034422101c142c11884d5a64a04006040da6203943c44000000d00c0f142c0d002d401e0000030310103000a0b141c00801503182c2440c2c42001013551190b02c002007840015092202c0c01c100800e00f0011030f26400500c2c0035161007407801400c0c124541a0411034141d0720741b10b1016080900403e840000410041c240c0b0a41c1e0703503030302c001c1c0e03061015100100c0d055562034240600203400c1001982400d0300a42d154894503040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 657527850 1250 657526600 657526613
    0x2d1206180902040c02010507020c0d030e030d111002090604033009090b030703020906092a0904060801090b010504110f0d050702010606020a0c03030f12090f1502040311120712050307 80
    0x80504c180b00f1641003c3c200411141c0009128071350b582c0c01c3c1c0b40c101803e07003c0e080499441c184480342c11ba05000b080185c00d8503962040b075802540001c082030380d100d0544c0d0000b1604911030340000581040b41408100f0115150350f202841c000b503401609107100c09117840f11a40061034140090228a05040a02462540e44108100554190018a02d090854001421014004085a101d082e94400141c00ca00039411420b21000c10441200d940c1240042e04510f20f03081002140e0141e4070700000000c400e0414044d1002d81c5811010300103a076420700c2c00f44030107032092000e403a6181e41d08205025460702c00c540140340301c0b00381900c00111414203100c003d09503941640004215481904148041078998031840c0403268035003031000141507150020307201e000f5081c2d00c1c08001c0303141900720001d0040000103400070504c038480202401401155400403070041d800007070000c008807500f04040d420041c0c1c031603090700c4464040341d504540e500b03c0201091100c0c00304880a8102040e220100702c003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 657529100 1250 657527850 657527861
    0x41205060115030b1f03020906210f070f1211040807090615200c042a0203180f0a0803031018061406031b0d0c2d120618090204 56
    0x583d00c2c00f480900c0c020000111700e040144003001000800c0101178092901941c1284d114080260040d512407542d2000700341c440400010f207142c006441c40014901400d2600550301c80d0450b501c8200f00d0000b5108200d03883c0300500e41145510303507206526088144244060f00080c07140320010305460782019410800d07510180d0001280511080c80e6840c0f0396008100e0384003160100005201c0400405411840c0140480007145c0282c90141503102a1211454140d060b070303514016411601600c013400c13a40e80c82008a065a113183c0002212014a08120001d9461100404405000ea00c4040d5a800c1d0f510959045150542d240c0c006c004600c0c460701c801800c0c0060b01e10030803989140c06801d0348428410a0301c1445558000001000759800a48071b110642d0303001d8aa84e100c44c03c2c0326000c4020302909035100041a03546030301005003041c0400c422003040d0901012a10000c3d801420344403001e0700e00c0140406a21900040358080d800180720b83c400075105004100201680103000480304c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 657530350 1250 657529100 657529139
    0x20a033207060203090d1104050c0301090b0a03380a0209130510030f21410705150408040e07030209010c2003030d0506010f0c030c170412050601 64
    0x4101c030703904000283e008015a00074081c150f401c40c8114146190944540070b00800300d951017440c0c8001e0080800f9034501660595281080411540e00203a0801081d04c0140c0b10080c41d250f01c01d082000680c03201c07002c2c0940140707404207001100c1c58001e0400070242040f0342c02094a68082940c1095140c40520301c0d803160b031031040800460912800b501c0c9080d01c1030102414508025030410100132000522080d50814400e00b10102c8007116030040524181e260100002002e0101006420700505408070078982d5104080300090240402074606400002c011b9416010b00c0602c00040b15240301d49174821071107984400d3703640b810802e804c1100c000180c1044101807041c892806180d8106041e0036105402000001c1c107450307444c0b00c0008825540c0c1607030b07416000104050b862400305030040342c010b200980b10318000c4141a06c08480c208825440a000119075011282c08600c04100d02d0034020b00c0080c4440c0f910703440b00040c6c100c402c0d8841c2e0440305030740443c00420401a080c0310605200c1d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 657531600 1250 657530350 657530353
    0x6010e0108070605030717070906120e0c0d02120a030512251413060305010305061e040602031b21160c020402130f1508060108070801030f020a0332 65
    0x194180014103640d078030b09000e1502401000804601094000d01917000000c104040c01016486c0442008203540c66034030441002c02c110901160403142c5ca4042d44a4084031000200800c40d041d604001c000407240e541a60440040c0040076a024020704c1521005402611101d603201c3c0a425401c1e003d00c002040c01064000c801044200d0103d14900c0304103403105440c0024242164000703080c018891204401d1300a100d0001c0000e2854154000b03070b04a0b03010b00c06440c0190780e0301040c0c0c0c0144440180e91908162610300040004081e030380a140c001481203095100c94208906121484d4040c4500c400064580c1c01400d0a01c11200b1007254030440003d0303a40301010f22110064400740c0c18280092003290040307000012070801c240b504000300000e0055101403503546203552010345c052031204000680480002d10694001c10f4150f0044800b87d8038601507a1075601e841100c002441c0d01240c0c0300442c80340002c00300d00364841c032503440f4204400e003017250140e40446505030281d88039044000d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 657532850 1250 657531600 657531629
    0x6070c140c092805160e060726090301060b1b010902011418030a12080f040b010b210906091b0901030b07051c0b0a05010503460e0601 59
    0x66100c1e00b210503040100b140901d002003028291001401000c01c000740ca040303103010100502d422080c1c3e421444a4015202c1d0202d0814441c1800030030305c11100090701c104121914011721041c0c82043e4694040c9a078942030600c820500017a094a0440c1d109003160300f00820705c2803030140c0b00c801c140040840c3e10020060110240d001030441800144d4440300c030807000c030b8440c0c842007403145c0c10340700c000380181a10000c580394580382d5140c0d0680425540064002d20001e51048400c0340c0c00d9005030307003048440c00030341e107403950324511030f8084070142c540c0c4040900f038140c1280d035002e042d5004040740006098146080101c02c0d14028544003841d0400392401829106922510080c034156508a42c41000a030f403054021b0700e451043c9150b2945100308041400300d20ba505038090f13451281c0450b07d0b420465624401101d1500065581c8652020b2a56a01c101410b229110a1010015000d118412203050140e65141c5181d145040c00b000d440c3c03201d0b070b00061004c3c41090701515011940605 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 657534100 1250 657532850 657532873
    0x427050a02190806030c04050108060a0e030f0706020d0b0d0c0305060a020f2a0d03150e0105031b01020c0d15050109020a0504090e0a0b0a150b0c030909041406070c14 73
    0x1050811482c807400d00607240045180c645040c07000a01c0140050020f1010f541c0d1240718950300d00003200c450300200c3c9840d54401c0200008401c9411480361a4111410101640c44500c000e60203011503056195441c08101a16154000707030710001406040c210480d036145040c2507050070b000a000d40000c0b8810030048018440c110b050fa0b035980c4078410070040c40341d52079a008000c02d25041a1000522035000a103e0702613051300000d038601d00c00c1d011041c0c090307951110088088000e001c3d59506400102d4908118080d07030b401c2800070f00051044440101e40e40d800b048441c484500140c3e000c1e840103070180b0718004107000c0e60b4010080c8000440c604070300f941d8010309a000f00d0045030b103e43d0b11113001c0b10030100d04024600c4030507009150450b607410107a0400c030080c4881c8a455400030303c035070800580e00c0380c41000d589040e08e903000074620b040c4035003003080f4540304020400c480c41754680f140d25540b0102042a07510501c80790315050440b401c5814865075201c0072801c501c82c258020209520b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 657535350 1250 657534100 657534127
    0x40203010c0327050708033106090e1506030711150402090103140307150c0314040312020c030f191b020a0306090f060f06050a1208041205030427050a02 67
    0x2000c2e44400c3c02402000315403450300ca82010100d41c0190401d120119500c1e641e000c140300c4019000c40541032403d404c0210440d80c4100c0c4050788200c1c0c01003107040500700b084485118038964403400840e1802c2540400e800050800d07001990080c00143c0d01a08014031080104401d80845090500c608070030702d0140d000454070340050000422604441d001c0e0040c002e4104242c031446984a0408080c00c41c80755540f0300200601c0744801c00103030074008040c0000840c100e9082c0550380554812070031507048442900030703500c11880a5001d1100700101203a40e0711400203400c4c0017030b144108148800c05004000c105240c0030b6480806040304094010050741d5040c21841108d030300c520041440c0c201350900302c103041c0c0c0d00706001c1d203403a09088608080344030031b42c85402a5841150322244194981103d1f0352079040d200d00091050b282000103100d50010f9070507000b41e8501c6801228601600c81581031501c54401d80e030a0a1003c04200031103000b60b107401000d901c000312a10450801040d0b07031a10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 657536600 1250 657535350 657535391
    0x60b031b070f080d1e050402030c0f0a03020303041517010f09110403080319110f070605090a020d050705041b080604090309270b19140409060c0503040203010c03 71
    0x940c206a00090800100102c10b1200d9102c960000c04140d00d03010b051800c01c01600c44241c00d000341c500c000c1040448002d0720701c541c41c0941d40250081003004556828850098049410f10754003809003030b4000016a01000200f0191150b10300300002589049000780400c04000030328840f0400c1000140081c01d02500001e04881c44103002050b510014060240a4840c980014018443c00420800100441e199840d1100d0840030200300c00d440340103911750f44d802200030020b580d14040000e01c0100e220754000076040740d070b02025204941d009a0015000c0c0c030186000700d6094116500800481ca868414082c1030b8542040c400c25000209000400f400402403842e840b869481440d02c1c00c0c1403007418800060103407070130039030307440c0407488800714035100100140c145036410038052980600b0103101c0d0a0044034440506401e5a05202c5103c507082030f10840b254000303940714072040104119001c1c0f4410049581c4a180d0346e03042074018182074a0100100c0d006150901e00899034400307802400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 657537850 1250 657536600 657536641
    0x605030727021606020c06010603050c09040203090c030105040c060201050906060607060e0a08210a02040506070305031806040b040b060a0e010504020f07023c01020303061201020d060e06010201060b03 88
    0x105520800c1140644000f8080c03400303521040c082c0141c0300001c0089581c01441080c4902040700d10a81c3d0f6600210150741040b070355003030003400a0042400c1390800b5000345400210010a0703c0100c4c8480002ca421604101c4064030041030704101000607a40a11a031500040d18501400d101c0c6014000b1910314801c20742d008010036521340c641c8030a520300b4001038580c20351080312282d030707032802250300c414200300070459031500040c0e00003041c10721080d803080700c080f00c1005e4170f40e80c1440910345094a898100500d041010301e41c404598812030310500400e442184250200030003814141441120b400c0002c0100d4000d440c01c600c03d2007004203082d0041d0440c1c8048401595500700080004494055001e0082d0852007110807040380c02c1c801818008030045080140d198401c8101d0040703000d9001d403082501603002000410480d0400214480c0e01540e42c600151a242c2050a468100c60041d48202008007400b010300c0030b0b80d0b0b4280101d074002d00d502c003241820740c200444240703410f81d030341e000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 657539100 1250 657537850 657537899
    0x1611060610030905101a01030204080d081027110a120b12061504231b041e05030f160b031b0c030403020a0f0e0a05060609121006050307 60
    0x260031202d10a4021040c041e82c01410380d60041c02c8500f12070007030012111500c043d4100340d60020034a51185c800c2d28129400440101141d4040d01000d46c0d0302d08003c1d04d10303c0390840301540851140d07000710f55940104188503010000404050700b031001c56030034032600c5401d2070041041580c4580d0140c0171040c0585281f03000144a03542c800082c4c8500c401c0d080802050003a00c040000391588945810001a01901c00f4446020780c1045800011500c003100da2000000e8030118415403003040903118000e5190f014585440d032560607040c0500d6860000800742d0600d01e82c1480f10741802c5c03088000075520000100703510b1841000b44c0164002c00c0c003a500b0740b03d802000007042d04e0441e1422041d42080c40d0200740d9035452220000740c4940c09400103034084d6a00d08800260020800c1d200780880716903801501c2c10340c0b20701d5009406844007074442e541c17051040c066401250b8440781440d00b65070709400102038842d4004034400036100e40d035124500c203402c40d1b00204030b42d414811038a80390107013415 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 657540350 1250 657539100 657539119
    0xa0e04020f1002240a0c02030a050403080a0905060f0705250902090f0402040608040c081f15090e0c0a122103020c0105040b0415110906090102070b0a030516110606 72
    0xc01c91411034107844e0340501e032041648018412840007841401010114018810345c1011017060f40c1d0b9203e051102800208100801c00c08140b000d00a041c1000851804604031950313180010a42d0f00a01004540c90b000041c4074810440108003085e068080031280f20044018203501c0903000c1c11610802c1c50300c03900002c1130780c41c9070b40c2d0710134500880400610071919a6150703030b402006484110380484004e6103488001c0344100c0005027110b0400ca030040c0c50702c0c541e10301303128000180c454000f82c00000f14030300501250b40384a5000c0e5015140c0c0540c01400010076581c10860802c0c21a4441041075016110394004101c0d9040d850034003082c04451041a0501c101e004c4000348224100940f0b69440c11062000f045421007085004a000304d000403c0c803580c1e08400000c4503500b1104a0203940308200c0c100c0d45041c00d00240070f1002d41401591002503031030661888d03d41c0812901c00c0040da45404110840e0404103600d24031654605c1c00710503080701452201d9031010702600d01ca01c945ca210 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 657541600 1250 657540350 657540379
    0x1303090501111207080c07080105060d030f1b05250f0308030705070f0c0e0a0e070513150e041b03050c040f02070f03030903020f0d200120090a0e04020f 67
    0x1002007440f01c9107030000300c960b500b0040c282103c19822058145640c1c0c02260030008481e04140556405810000e0000c010108269400d0701c1c111082701210b810700c2076610545110700244550030b0010f5000e04080c0a0b050074400c81924200300102c80ca40c0c060f00740b104180f1414102004910035a544400c0c2c55070340b602c58000c02e9a05008044008011000d502c24034001c2113403010a076401c40f5031081600d20113482c0d6014102c00e4501c1071002c8803003540940010006481c10503c00c0748041c103c4140001c0104100d04526010006a0015035125030240144010020146000b1309480041605034080a007103640780ea450b00f01d1038641c24130942e100d424107525103030a03a0480d640c0c190310289038850010300b480d0290180001540a81c054022005454520700c00400d5040c140d00040c0d4403a8403084825092440d5040d241014902c00c1d943c0d901c03010120003100030507001c40c184600e030403503c41031030408004055031907802510b82e80810b8418800180c5030040d24140d881c0044a0a942203150f4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 657542850 1250 657541600 657541603
    0x20030301171c05070c05040b100f0e06181003020f0a0e0114071a0a050613050408070b040c030b0903270f03011d0610060f0804050f03030c03010e130309050111 70
    0x701c81c01c0c040d20040b4900b01c05201a008001495024480c0300b070b0b031171401e0b62070301008100c405503921107421101e4455030880d29440340c0501d6075141da19080856819134040013140061700813004480709002c80154054441c0b40040e0070780559001480c0661034040741c0d4281010902807090303100700303200302180c894034168010450200580d0b110450a6284d980a00380b0f4200001c1d0200c5030707042d080b02c00303010a07003404545c01240c5c030600d4081c2c419480f103800d00d01181c0080c080200181d407444024041d070800502011002c502507802010030128035411400c00130200c034000742c03551690754400c204c5080e0f404095040084042c400b418014131035074034240810986002044480d0b419440c015680103031240c241c01000964120004a8043d03a440c41014032900007107008110100c1c1103d1098070219114080d45036100388150700356214804c1817a80549560420f466080013507001000520800b03104001d6542d00c45c51920001c000001300740c0f400b070010480b6002c0c0e40d0410031203071039501c1025070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 657544100 1250 657542850 657542863
    0x5030f0d0c12110105041a182808030705041a12010308030403020f010f0c030c05070b0402040209151215030a02130c090b07050d0906050a08130c03080d09032003030117 74
    0x2a0000174400303031410340391501d9103074103013403142c814412100049100107100201030114840320708001c0000c461804008428a8144900c0c8039054069880800c0001c450101541c080d8119444954607642040c2a4600b242e0351040b8800005409202c0207501004d8004482d0450b80c000010650380d8407641402c80c20660340d00782c0d0440642c2019501c100300b48031030384011400d04403940e003080b01094028085030103110384540a002c40e801040400c001d49441e60080000b2803004005010001f28145d490415411040800b0780d09e6455008000b00609500c0881056800c210f001e0504030700c26500040700d40d0700081407152525501c40e401444140a0801c04000e0600144001d856000a181c001d0b61125a04c1c90000000d84e8110009103c0d80524140c4a5400e0f0b107842c0c2031700640d100041c540300b0008007042038404003240b04c00040882d40e07850003000c1e00d4078030242c080f6114030b05082c050000c1c071034240012042540c3d04849610300c070021040ea4152500c143e4880c00400041e8001841d00c2c0c07 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 657545350 1250 657544100 657544127
    0x6010b130612020c151602031810030e060702010b191d06040b0301060f0510020d050d090c210203060f0106271a0301090e0109030e010e210705030f0d0c12 68
    0x4a0455120011441000106c0c0f10780503a101d58107004000c0d4001702e860740501001c803c800c5100c1010907482e071900c880c00052146c4d20b072600184180c015a1058900b0318140e9804016075580e480003102401c1030000002110a180703003c400032031806205014000303107a95001c850b011901d020071000d030b913680c100c0c2c00e003504010024040b60392100024400c2c048a0300c00c85100709242824030780c4480c008101075100d00d809450319407e1000171180f20019200784c1c4c03001c4680c403541e0003012031098a0500b1121342d03030004d1040001c0c95882481418601440600740c46407024003840100320144d8408185040e01882d411800151301c144081c0707890000240c0c000301030003a0346150000551483d200914100c8840f00c03c00e002024401107118220b07a90184090300043d6200e0041005500038264040c0c2c1143c080c00120407260b941c881d0841c000c004821081045c0c202c0f04040009203000c201c00000c20304020f01910440b02e40c0780c1e010700f51610500004207044800080416100e01071601d841910 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 657546600 1250 657545350 657545353
    0x609060e060c0a0e0d0f021302041e0819050706030f0f050408130909020a0501030e1c02030a030606030b0603041e0f03080f01120b07030e010b030106030807020306010b130612020c 79
    0x182407041101c141900404074403000100203543c85002850039002003007401b40c005042c40c03540446074080c8030f040542c1c11403030708015408010010b40c928080d0b00d100300c005818403000070361a0806a51608041d1484500d540c01c035403c01c14480071a8011920808540860070005032030b400e02c842110141003080000d00c0381919150810050086c0c0e84020004a040e02840000c0280c54588903000c48500001c069000103280710300b4040340d4043d5000481c1c0342c40c0c400860300d458646040cac50620500c40c600d6440140c0011a00f80c41c80c0740c00d8003410001e88403500f418000c4052450104007140001407000d82101402c00519801c40d9000c0600e90340d480d007004480b9000261410060640c42d41a52104840c450702c000000d89801e0000c142500240d200c14000402d85030900120003070b0103650014003442d50780b960000903540d0240710300001188904aa00e0701c0341c0c6680109400c0c403d059100501c0c2140410150b0201e008241001094992904080200e540e494410710002c1c02800c0100419 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 657547850 1250 657546600 657546613
    0x7120509030a14300d02070218100e010b1804092909160608130215040e0a0f02030702070b03191a032e110903030403080310050a120609060e 62
    0x2100707000318285410203030642840c2904204a10181d1201d4040c04c40ca4043c05824040310100c1181c81c0c00600105000505200c800122225604c860b03400c10740b99200c1d8140c01980401280528003a1180100360910100b42003241244005140c90074011002c3d100d150f40b8802201089040100d1440c00f01031044e80c504107503020308445040c42d40998054646c0d1041c0040300c0b44402c610303800c02c01036807800c0d0b5036240e050300c950710060340c04000c20001300d1f07000d0071181d11550300996220240004207490b081610702c42c201440c103941181c1516010510721401001002030f125000121141143c1c1000c117119074a548032030080300301c0324090801c03104003824105a413034290807071000d019408008909450700e012600744490500d801060104800c4080d036840030382154080c2d1b02000743d01258500507440e24940320002415540702c0e800854412001000707025204041200e4040500015641d202009041c86058604603c0451009000f251100302407020018650420003c0140031005c9510 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 657549100 1250 657547850 657547883
    0x619031e0c18060e0402060706200307022a09040308070203130906090b0420071e08040314070303021e03090316050114031911070b100609080307120509030a 69
    0x60801203502906042c60a06001103402c4008290705405a640144500d15100c401c1e41c4d44030141c0700080d180d1800035800b83c0d0b071040104001c0019803084030194003a04110444c0700c10880900400080380059903010a43c0c0d000796119400115001901414000415036925208034518490070444881015a92100045860068011a051b1205030005110360300c8800107100803038800c40382d0810780c41400e0541121b03404140004003d2280134111900308244034080c2046520184101100c400c4c1e8005020424090501c0b102c9110301e02010182103258510340b0000d540700744085c100b218503821003461003c140340400460320030382c0000e819200181c03520328110690240a2040714042003e495100c0000d4807464101d81c4607694010640e215014200010030003081b101481c101200d4003000f4500c00325072000803203480380d01001008615582015001084102241d004241d954400e01402d0b0028a16121018030302c2880c5c5010350b100e0009000107440c100c0d5030300b8041c0103405482035411 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 657550350 1250 657549100 657549119
    0xe041e050304170102090d080d0b03190204181709010c15050f100b0403260706061a0c15060f0a08010b0910060507030f17090d080619031e0c 62
    0x11603030002400041c90f075036039503524240d100381c000f90381d07000421985001c00980c801025186030b103041e800000c3c2c241d8100001c0303450145002140c4003811018900c00c01140b6081c003680c0c2d41c1d02d100c0c0300ba82443d201c507603076450030641e1113400940c6015004038078512280d2240500c070f450690403a05194a031082210240c0040030250b40f200c105081c030100081c07542034902c815201300d6035400c0341c1c0d52a06155403a92204040c0c921020380d00c1944d1501c15501e20041c2c43c001e0b107211030042800060540ca86080030000382c0001c180c1054100040c04010a600300c08034111f1030340b8540d541d00c8065650f4141c0046d042d4100700041c030760700100c8801e010800600562103078042c01c009903401c1100f61200c00c02c40c001e01e2050301c92240015010444800000d100c0d035003400b0300f0241410911442540d01c5040280c4000c111900b06091f445010a800c040341d1000c410780d0031801c00d031841c6030020400c0b810301e07140ca0341c01d0001400305803403050f01e40c45980d60751964040080d004507103000750a4603a000740 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 657551600 1250 657550350 657550357
    0x30309050a0210030b040b1002030a1206090501080d0806010201051509070c02030f010b0301060f05030616020f0a080307030c0e062502030601170708073209040503030601031112010e041e0503 84
    0x14040c40c944082e87c44681451007081164580603001103007042d0442e8011100050101001d0710344035101c0d00e000800c000c00c7d009080c081d015030800703043c0013402410b0090003800014400c60445e81018140325448014000d22900100251401c2000742c0c0c540d6002d0301c2812091318000c3d0984600401200c03e00d0065020a4249101300c0003801141d40d40d00040c00070580d10302489a040d0000c4c00420903044149010007805140da00540d003803007642c8000c0302d007003a42d450020f0351000000010010781c2d070707890300c03425180707000d1030518024040c4c2071310120300c03180110798501c2800d000c500081124001da42141b1003034240e005084409541e180c034483c000000105034541034902c50170390b01060054000c6252000c5e2592812001101514804019032003c503170b141c4030000003044011050a40c84100c441c0384681c0c068801180d4a00b00342c070004007110000040a5440d81c01403007484a65103082c61070b03a04403542d50f40d2040e02501c480c2881401074542410f15131120b40304440c0301d0100240800034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 657552850 1250 657551600 657551621
    0xf0307090605030d0c1101032307050415022407090f0b0403051e0c150f07030306080f0c010804020607030504080d0801060e0603040f0b0423011b0203120103030309050a021003 77
    0x645101d6404000300355200c01d01c080c170050846d61080d045546a500c03960020101c0400c03800c668841c034174143c0d40c4954200d001d0702c05100188000406101035010640b2250b10032500f44010310f0309900144802d500c8130b00aa8030a484165600c020681552082100c00702500c001980d100d51a6036909110503503500502c011101405500c081e4120a440c5a08000c16004110b010f040c7c9040e800c000c000545007410300483c0444024000c0e03d07082d1a03064003801c9814881e45000031914241001585401c6410910300704680c011a50504241d9105107040e0300280d0640b8540c1d26004146001c0e41e060140360002c039001d200e02066800d8079907001841504031903050302c41c0c03140381c0e00800a1025611040b00d01424200e5802d8030000021102e0000d2540700c0d000321040c11110035050608140c64202804001483c2e44a103601130030808a0f00e160400350070b50b400210314001101026610a140520010f800d0507a58a074040c1402400d0101c0c0a0ba1640203105800740204050301a0040005411 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 657553956 1106 657552850 657552853
    0x1804060f1404060e06071d0d02060c0619020316051b030c151303080117010f0f020a0e030705030c10051306051905031909020f030709060503 62
    0x28074545421181020a014100340c01c08078140d07600361000580301e800410500c403901d03802440d89000d00b260003444c020304101503c00501c041c0d03205031020b03400c003000107004c1c00c1c0c4160101d20244944d07082051541c0c0d00140361000422070004a40c0c142c01600f0301031040c00201d001714090103000c030041e420b444042000e005030a0541c2c00c0003010b5815a8403011110703648101c120406548034820909a40d03500c09143c0b0b0040c1500810300c0740c0d0105800d841680444807100790001e40703503052010001d00c21000400c0c0b10b50000d42c84a104000010342e000c000712070700d103404101c1c4011281c0c010010100c0b10b20035420880364006080200041c410104a4502d43c5680e0144074801000d0303075290b494880c000c450f034105102c0c030100b404000f040020004c000d91865200d100c80c0c0400b5120300d000440c0705887c408100c000750704c20381da41d500d407081c400005080043c9400c440d054405c01c0c2c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 657374100 657553956 := by
  have h0 := BRFrame.cov_init 657374100
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657374100 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 657374100 ≤ n) (h2 : n < 657553956) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
