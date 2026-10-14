-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0648
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:55:35.661981+00:00
-- url     : https://prove2.me/submissions/dc3ee922-df3e-4bfa-bfae-a0a4934b3a65

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 116366906 ≤ n < 116546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 116368156 1250 116366906 116366909
    0x40f060306051e10020f06040506010618060507060f0f09050609010b0f1810031520030919050c0406090e0f0601030b0c0a120245040906060b0703050301 67
    0x4030385455000521410890a242540c0850040c444054a141e008020101c81c0300103d500841c806c007041c000c0a400e04100c2d5178081d0f030003503009144541c5060002071034583d00440c400000d80c0309020800509401c1410760f24219800071000c2101300241c49918000d100d00707204040d010381020341a03414020040751150262910714000c1c08070091060070b210136410420074160f0000c0c02000100c3c10303646141419500321b10034480c16460590703207443d4110f10398046040c00d25110f03921407441e01c03690307800320850011840039a4098214a040020303540c940d1404640c105c0101d1006036100f04103c81806081d02030b00000f0420403141e40c60b0780d10403004246007015002d051080b0140d01c140414005900d0741225484172102000b9070392102c085005800103030101c014000e803444180303074004d441d0000c0e1118000f8408801c0d2850464446481c400010040445560b1121044460625085140003819080c1501c01240d0390f04e080c580707803008003001e034000001c601d40032500e00101584100110b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 116369406 1250 116368156 116368169
    0x1802061605010b0105030618090c0301240e01060f0f0e0909010b04050906010f150221033403020a090902070303090212120a0f020a02030a05010617060105030703020f0a0b040f 77
    0x201c5100143d0056a05103c140c1d41290710a090f0141088008101e8052503480f044c10800e0b00e1291001c080406c5c02d60780040e03082f40ba10a44444204400812120104010200070030f0540555142200141c48500140919001c0000303d460310f1420901602d9100b03481c800c0542401d0b624500980000c2c0203160401c0528451820500803c1d8218000188541071300c8030222840b0540e0b1501c00ba000381c48a6a480140941c050318000882051006c0020882000100e407074950b207240041001c4000c003000303080300d09020b0000c035604c060082d01d008440b070b020195090042e0b840c600500144ca48141075402042e400e80000350702803c065054026004591082d00c0ca16100795000b44001d0300c50b0207810724981828018800201d90328800e84001b14012402c1c0180d8501400d40c0d00828201002000e09070ae040e074580c0020401070003a0641420b0f01e000700800b0380b0065040200082e02d41e04103220223880f4544504041038a03541d11100040142483d680042e86d4583e14007030155022804c0c030a41 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 116370656 1250 116369406 116369411
    0x509210f0c03012009040203071209081b0a03080c0c1608030703032d0f06180903080105010c080304020405100503030307030917071e03020309060a0507060507050c030d180206160501 80
    0x1584104201003020050184c2000f60034103198060b01400001d40000344204204186051040c1e0308102c1803044010b0180140019039807004405605140e02c404004000c141d5800a2000320109074403030809600aa00c8194a0381e40e120201d000c03514049070491a020206404500001c440000000525040c1d200c1c0c1c03018809111100d04000e20350900500e6a182501400920714141c20300ba4010a07211244000000710302c2c0d01d503881032040e4010b40741114941940c0b140f0450034103070088081340c0101424600b00500414a984115007400040c0009000d076480388003003001c0c4038810001c40e001c1c00024040303a07220b02d840b000017000f0b001e513003e003a83c20080031b01e0000307040c8800f4400c44041e2900424402030860080c1250000344110340030135021030105004544203603486400a001502c80b5075103440e1605900d05110044030000341922090142c204100301180c4000b0042e20500071000100080260983d0100c2880c0f00070810f000f940000000fa0080c40ba8111412441d0128006c1008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 116371906 1250 116370656 116370671
    0xe040e0a02030606090712020d180812060402090109050906120a0308010e07030c08041209050a060306030c050603010e0c070c0305030d061e060e0d051f05190209010509210f0c0301 79
    0x9108581c5c400f0398444000944040d0303100c0074480300e50002c047c583d007205d10015651036256117a1850130040a0300302ea11030400241007068140c0c0b0a0503681005080b101149001034500c0081c10700c9115210b6540640400c1000031100d40d950386000009082c00340650b019807409290062143c1c0d024010100a1150040800c01561180c030503d142c000c526211115507071102d80340c5440c1c180d107618480082108001012860740c03600e00d242030041c80c850301c0200d41581140303082108801d032508094003803981400100440e42240d0201500a6002c090143e582c0c50503040909545034503810140c009d100c00101c2052882103548080125220010f00849a43d4004615000d0500c5071246100003507641002840da032a1221031100041e2080d401c88508501214250b641d42c070a0500312807015544500708180e104851400c0641803c900c2000c40c031303008100d000600396018402c01e540c0510703402000800e00d07070030150175000d000c2c0c1d03007000308c0b410f094100c44000c1d5290040c4c1901c40c025400c00c0340 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 116373156 1250 116371906 116371909
    0x307031205070c1103031b0f010f020c0316050a05030403080d06090c09090c020f100b0906060a09030807060e030d05010801180804090b1908030c0d140315010e040e0a02030606 77
    0x621030052896039110621030030552114a031910780d40716441d5160104004810b0f82c1d1960031401d081c21003144001d8121190100041d500311642d0203918519280104401001da0cd0080100c40407030f40d141641c0c0d0312081030740c00c043e40f408a41a0004033248000034020080c014503001401039072164410a0200c41c3d2200030940c103a40030241c5141c0450a180307024000e03102e8070382258625072a6441180e00403440b0301085841c200304087c40d20180e9031398020448150400f00507542c0d00040a4422614041d526035000b03141074280d00c8003801781c000218440d0100305e001d40001013008c3c40d19003141d46901c80ca8035200001d10081c4a54001d41d880d00401c0740c50b14a02c0846601044d0b00440c40300c1c01c06240c0300c804806850f4403250f580e40003208405000c2d200b03042c007160402800c50400110f4860540c84620317032034102813a1040003070006580c140b145c902008000c407a4800c964080300c142499511006031400c0010f00c201c03c0d40107041424100b4400000a00600c0c0140200c00725044ca858080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 116374406 1250 116373156 116373161
    0x41e0b040b030f0408090406030b060a0e0f01090e0a0204060320030c01050d090609050303010b0d050901060f090b13020c0d0801050d0209040b040323040e07030608072904060203070312 81
    0x200c0c940030740c101880001c40c0312020006042d48103000b1100307607203000c1840c00000d0840b002c90300200c41c201e520609010040c1404458a40a030481c1c080d10350050415070070325034445105209900000340c407200f001c0761a18081c4018803903164040c10030311200c0e889182c802e080c0007540b42208194100295080c40c80c0c42c00042c610f00141f41a101c40346402041d004442c003503e800101500c940c3d03203c022000000300200015802480c446541c0703900c4400c09940c0005403500a03055101c5603040c60f000303100c0716070030140101c1240d02803a80041c41c5048800401c55001c0e6690103000045e102040e0340e20100004510ba18001078070341d80d40d01c56030b03880303104001c0544e84800c1c019410003514000900010407494049400c1802414032034460950b10028010203031a07d101c10241c004003140411405c1c5015003800d41004080c2001d115035410100d40384d981e0281c9200b1019401c1600094a18905204120f0b240b1864821181980c443d01e0341d00c081d54940c082001140041d01c8001943d400a4451 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 116375656 1250 116374406 116374409
    0x3150d08030105040e0c030d03020909180705010809010f0518070803120109050c040306050403030204060905092a130b04080d14071101050c0609011508012d060b041e0b04 75
    0x1a4214196424a004e02004001281403484640f1402c50821102d03034003001000c3c0e941c6520f0b41c0150b511f00d605005c0c40010762025180000340d1b030711003401042040012483c40c05071002031805049640c1c41100b25800740900d20030015141c1c1c5013406001d010000c04420000d5000d42000300e4841940d01c1512960740c0c402c0c80c032202019070b000c000500501d4801c2c3c101c10b4001d840d0064032070401d61030388c5450084520941e8110003090740007808111650f001a5050018207085034211024544404081c0c50314500d28074002c05171a015a406040482c1d0f003042e550804a1902e003544041e88800400030203a0040c01000a81d01c0f908503c403090a104100c420070545441186c00c1c140005a0740c1d4441b01801c2d14815814090144010030044108200541c4030b00000c40001c180a818600000c1190751035800c281c5150b4106105d0030b00089200004400542010100d4690481d0b03411055004250030703044603829080c0000c000401101c0e011035144100c40c100c8070000703400e40e54000c01d10f442c8200d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 116376906 1250 116375656 116375663
    0x6090316021005090307120203011a030a0b0601030e030c0601090e1207030f090b0708071709030d08060f030a031e0509090402060904140a02040e2202090405101103150d 74
    0x4040040c0040c1050300301e02d0042c03422820914242030301c0c4030029040072115000000030700428143c0720107619090140010310039001080303000100c00100800e84600c030200010307003420344a20101d000307640300c5d5210244519a4030203aa889440140401c0e03141c42081c0300340a0300328103100401100c0303840415000c0c01c45200e85403c0c0e2521005a5055408900c851145000c1c02080c8200081402898009000d401d01c40c80c40669034a100e0f01c1c228683d2071440c000310131140d4081c400c3e05840c0e100010384401e03034042804c6c401d54035681c0700c0004101207503d441c504d0f05400782504110426030061140361028010380c6c4000d240e442c035004211058010324600c0c5a000c080781300420094113081000708082c24001e040407034100300002d03201c0d107e00010741e42210129030011f41000604050101d95801031102002d24140c070414140f14001140149000f9115100400c042810010208103281d051400b0f00e005016000140740408890f40048420038401880f23400703440440c1c50b055115401d50382e403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 116378156 1250 116376906 116376937
    0x106080616120e0709020a02060907031104020f090301090813140303030f090a060e0d0e01080f04060c051c0614030a15020a03020c1c11060705070303090f060504050708060903 77
    0x34842084403890310b141c0140241d5a5154942d80c103007801840340c140a41070b4481d0160f43c03801c0c1d00320024174200300203003900036a8010706028400103443c00c0310300350000021036002da1601005140c900692188040d208c1d45580b8103403404d402c128042002c1d003101047e8045900109030740d220341c00c12902b4001c0109600d600100000344030541d104003115003101e07511085a441c800d695849108039a101c8030005240c1d03011280800803198000c0507100304200070b20344a641c5040030040c601d003030303000a080240482c1d241c91914044511400648046002580c20540c0d1242040e03000d82c018420f030300a5541d0072180640c43c8149090000b0841c80c042c4d407206098030100c62a0030704000135006104202e041680810100d9805482040b0752441c00494202c0c143c00340e215180d001e032130f0480c100c0e071259140d04001e042000301c54210381034400882e09804e011801215914000c600b214240340c00070b00f414076000603c820b000e00051100300b03844501080391303029120042a19a00c1c0a5107503070445802 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 116379406 1250 116378156 116378191
    0x2030904150509010e010e0c07380a0e07150e0a0f030201030506060c030a0c05030f0c01050a05010515030c0a090b03040305030f151e0a090509030706060f050f040207051f0209010201060806 83
    0x7100c00700285500343c055200c0035209243d51208159a43c0c1c40c03405183c0004c07442c8c41c114144005038100b56042130703440f0410020034803112005070312102943b0a81c00c2440c07500c1030500105000c5d0301e1804401c6070041a02c1901c5e40c9641c581c0b0a1485039000c1680042e14000020320f0b0303802c21000f2140e488200c0c40065041001003482180c0b41d240715001203490380018442120420900d001500c0c18800705400801d5915011030075a0842d40140e005034820001c66a100c841d5140d440300b00e940061090010560b548500101610b40c02c40c9a2b01400d0400790000c20441410341c080080c5000e60421075a4404a48410000171041e625104800b43d00010544111102412040f998440441c010700000522a942c26501040f1081119000c586404c0014040c04100a52140300d01500b0390301c076141409420700340818806060124801c2c000d0354009421400e011080052284101c1500b030407210522001440303030003941061441c4e40c05076090990100314100c000c0f614901c51a903a407a0100e011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 116380656 1250 116379406 116379421
    0x8010e06040206180d1b080f060c0a18050a0609030308071809020c010b09040308070207060206150d060b0d35070204050c040e01150f05270102030904150509010e010e 73
    0x1042048010785d032103140c140c070040001b414010311030040d520300c0801c5038a040c60281030364106440c602c80c1c00260f800c03090801020010318001d80789400124500110034803554450750102e6179058000340e03400014030000041c504c1d8030450341c900780c0f4401e503102c4141740c0741c022059507840c90000e0316074103000c044d420510800c203d59020b00352620030b0400220b89803c0e80808140c0048003a5030690014090345d003001007080d0100140c0c401000148010032140c9018902100141d0004007103611400b581c00342c041c280300c9190484807600c80000c01c10380511100b440c1c5982c2200382400b104c4c1c0c110079420b5050940764040e0070440b42000c00b2010030707454441c0650811006010090840750085014840460410001a411800390910050741c44400c48a4007000e0300341400c908990341000302c10041c14000d2600542da1900d621440c020000ca030183c0b40005038118028500340076002441c0000c90500e09000300f84100440e501178840300410f9890b20000c00b403800e400d0042214056035040491080e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 116381906 1250 116380656 116380687
    0x30e0a060e07030c08101d03070b1302060a0f0806030102040b04030813080d0203030403021501031a0703020d020f070606080705030a1509020d051617070b070606080d0908010e06040206 81
    0x851207803401c0c1c0d0461500c941e640c003245411030304000101d80c8500d0a01c0f500b2100b511900341103002c42200182c02d0b032443e1086c07075134900c00c105004110b003100c00042010078480c44154203081da40100a29122110408020180551200c41c1c8000900138400301e0414107043c42102d05031042c0c0c079841454242551105401540000f80c3d80c040b803542c0359000600c4040a001007003011620b40d001d56960300b01414000c0c6808888080042a8a6035800400c0060044d01c6644070b903800003070b0402d2040c0d8800406900a010300c04001c5441c038000164843d0315842d0000500403540305d82c504000c155216802c940c1e40c2c0e1140c2c0140c542561011102001180400d850044504180b40700405c400400c2e378003007040f070221140100c07035076400740320384238070045048698502900048907441240559500065a00c6405118182100c1c000194603414020385030403020107440000d003142d4403d0020344008040000e00d00c11a4600c0d40b810b03164000c45a800324100340034613001898a8100000712800c07804 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 116383156 1250 116381906 116381921
    0x30106020d140c03161709090105010e030c030118050601090e061b0d1404150b060f09190e06100207050915010318030e100e18041a040f1101030e0a06 66
    0x2a808810f0040c5100f00d4001c2000305889542c6229800040c291890202e018070840786070840407250901400b440c5440380420315044a0307003480c0030614039403480046410440321458007034041d403e20350707091428070415640d052018866800c89030b05aa9a001400c02c07540d105402c04e050350040e402068100c030f0038003c90f00710985a9844146071184201400d02102e80c02460711405219000801c0107020900e00c01165010079204203100d01d600340070000c0d60034840e115810f07071501070102d01804103494050f1900424601d07aa094030782ea03030300d0740c07024059541e00f2245503100d000444010404e20b840440d90b1021580f010304103054a44556010303031202c101d842c2200f070401d50344e104405007002611400706681c501a0700e0750b40b140c14511041c000c181c20841000c03021b004a01520b82c207c3e85420b119200c2003112a00300c1002601c4519100c00083c000404800b101c00c441400c0c0420300c00258190b06c4050b104001c0c900303401c100540154180c900400c400c040302d81060b154580424200d070080710 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 116384406 1250 116383156 116383187
    0x3020304021f120e060f0106051602040c030b090414010b06040806060f04111c0b0105090607080c010207050717010c03050603031b0120120705031902090a050d030e010212030106020d 80
    0x5410781901410070b00b102c0081000c4c002c01ea01c002c05006102d004a0b54650140c4180d02d000e514201c8901228204121484c40081c002d035908e658660b101c510a91040044020061900d42641882e0174400ea20303c80304d140c0d42c00c0551030440c10310240c2c5060300c1250122507034100501038942d00c0c3c5080144001049403015042911200104049543c1d10000c1c0003000300c54070b4440100c0390302c0b01510119039040b079000f8188101044210300c0782d07443d8000d48003407681c41605641d03214805440e560190051a20040a07403140340700101d00c1d440c02d114004101040f2000801c10810009401c0702529015a0a260141c00810030130b810320f800000008000c00b0003c0011404850118403034109801101c82c007600c05c040807600204004c150039401c3d80080041c5840e904500b0034980c0c0b6200100c02c448504200e0303500190307080c5075442c0c202e031510061000610070f000320441400e021701401344160045005004000318106035a120300c060324103a81c0664020500c02c0000901601c58910624415 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 116385656 1250 116384406 116384417
    0xb06180a1a04050c0d020f0f07150f02090d021c0c0602030d1401050121140f011e030302030a0f0c050307030c0b0106020601080a4e03020304021f 64
    0x2840040001214a008064020000908481c107000060090300340106062041c1e0400050240924952051740c420302440400141d85115642d00007490344210228044001004141c08041c070905054086d01000700a5060000c01104105007089125100308503600025245410740982401100000c002001d00318800366050300e40c40e52090003440d5400ba00c01a4400107201c541c0e0001c601400715005d0a1040380700c507550511001a03e05030700e03900d602d41c0c50032032032900000d8441280c01042ca03203c5102c540e40c1d070ba81000c0040c01100715090003008103849070f80000e65190300d40c04030400700704d90b00340e40a1810000d0140044810304a00140d00d42045083c0d0804000f007241071009042c200d1290f1a20310414010340303464810342d04160f000c40d040d50041c0c001006035807004201c20541d640e002118030340000154071109000a00360003450415480d00d024210f2a050990000e803052840204581c40901610001c0f17059100450f0000e40080860034a50b150151204030f44500e5035050514 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 116386906 1250 116385656 116385679
    0x21315030e060405010b2106070c020d060e060604060e1324020c01020a0807091a0304210e0301271502120a02090109060c12110304080307050a0c05040e0a0b06 70
    0x40d0b403600800b0764007680c4695550520304038601c1c0c03003288030601405040d10141e4060085981a485e1304008100d00280001c1c2c41c031900440d5036000002001e641d11550800201110080655480c04100c0d1500d024500e4220082900464a4210740c89150801d804803044075842e52024070742800350100004401502c80030f600e01c001d441c0058900c24518400060321080610f03001008400050a50010300c0008038050003401072030001c80e8150f0f090121116074944072842d0440160001d080015505100d81c280032340b00700c2c0d200c00c1594012200718000d0040000600c02e00e03101740c1c0220b103400b2140340081040381c00541740503040d6412040e8205c0060403c0303040000d005050b14103c0790081201e600281c6407500f50303040350a0101a00b0103140115031040310780d680065a02000000c5c40c140080090b07890680300302081154007504488064917126a000c1c42c0c83e0795100d500030350454604c25081000314403400e081c4500b00c2c10710186801082400035548a0482c55080540015080140c80c0803 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 116388156 1250 116386906 116386931
    0x80d0c03050c030d0b0a0b0a050703030b0d0b19060905010b04090b03010e0a0c150912081303020a06230903070303050304061112040201020105060f10030b060405090f0609090102131503 81
    0x2400c4d884048400105640401100700410f4081d9074020032550941400203410380359000041d140455490f00b400100082040009130a050004034000c1010b4103007400c1007480070a000103002c101e40343c5041841684c0d1101000c1003075036824003946480c0001030004020110043e00002c440e042c0c0074000250b0302d0007200205c2c0c1007020111050307401c0303541c1403000c0107441e5440c5c24031204000b82c1d15181803690705005001e113901c9100c0e200a00350100105c0e5071000b00d844c000c00c02004590007891017400320794034100a00034204070048040d42d69690304c0c001e07550380100b000b02c40c03280e10001c000e001860b00b0356a003903409401c041d0090740e14139a15100c40c40002d001e600201501d0074140807284040c034081c4002802c0d100001d000c14094540d4600c0228141c5030060048560f07202c1c2d0801051924a98010030194000d81d8081503000048005012080800c0310049000b4141510031094541d50141600e0a0780320341510582c20034410081040714517140ca0803070355080d5030f0b0710b00801d03407094000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 116389406 1250 116388156 116388163
    0xb2a030702010203010501090f08070909080c010c03050916050906280f090e03120103080309010b180402030706050a0215060609060a02010b01030f0b09061011030c0604030e0604080d0c03050c 84
    0x2203a510260b94008014000b943c2c0012400c00205004010070009078180684135444007101c3c42007040396921690312030100b204c9802590340104c80d00d00200811030800341c009000e044140d61002c00c1e8018115400300305400100c1c140c4c04c1e280e0160840300c11791141d800b880364004034003914400c034101c00012680321602030417a2030f0042c40513642c61035107617003850ba516040b1072070100c580659510404c207031f804052450101604507074002141c40d0320303561a118242e0150050b8160150310108400b46030b0364a003009030700940518000da0413501c0060716481d054595110309001c807000740c0e000445500823202410482d6901420140c221814244540b012461503006080e048000d41d45914841d051544d051007050080c42106405001003442940414803240000e00014056200b402c2d00383c240b24020041c2d41009440b2404890f5a0000104082c1e103c940c107889c110002001c03140c04104503e0400c06a800b9600a107010304210b10b100300c1d0548009600346000c505002c03007032002d00c299481c02d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 116390656 1250 116389406 116389411
    0x9210d090c1401090b0306130b01020c03070b18030a05101a0a06030f0b04060f0501050c07031406040302060c0f161b060302040801050604020c07032006040303050405090601020a0b2a03 81
    0x2c4002c02c0b0070702201c4001400b101c100da000061003060902c200400c1b0741d100a10000c1c1204203400000701d400a1800403810040c915038869094415030000040b10440700380104003181802941d520810742d0001056210450000c000d4180c1e40300481000d10b003009603215606080b02c520b100660a070341c60740802d2586110354404004a50b4600000c0031b20300d114001c1494411040380c0c00c202c01c0f8201080c0c440e040c010f5001d41410000003040708000c1d0501013028070095a0230481c0c0b4151503000c0042180d442108881c1200140a4080491101c501c045c041c0c2d52b05109240120341440e014141c40028108014030554480100c08070801c00c1c0c10710125688d014240070755003d650390f401c10f20880d09480014181d00d0090b8410040300b00c0c0c0301e5011036100203803544003282030074a1201014669400f40c0210303278142c0c4480c00282c00000c05070002c005008582c2c054401d103402e03540300001640c071164050409001e12001c000002c02540d51031001c0800c10a072800703030f103250132402d9103100380a4004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 116391906 1250 116390656 116390669
    0xf0c080402030c0a03021c03050c0a0804030c09020414040b010507060e1606020309030d030507050c1b010e0405040507060302090111030d0b01091e12080405060304060b01030509210d090c 82
    0x10080c4030030340c24284185040c022055500443d820301d90780c0807e2802d03000181c03a010140114441c0e204242c41103040301c81d50035603c811184400a1030a056101d80d0092001711561039003110006050f500c40d00990f400c40740140c6010b904004920288000780c5090096141040406c21842c80040c0d142c0c45418a00a5002d0082c4911340f00310340303c0078054400303400c02015075000740105501c6580006000c03d012103545404102c94984440586141c0100d0f80407000b98020070a01406a904180040b010305409070303205108510240180070403100c0c10746024040f83c0040a0911500707019400822222030107260540c810461400001e0071a0002120212040c3c0c44045c03503036140da80060882c0103455441030804c0300d1070350140807012501103482501c00410000100c030040c0403000303003940c00038070000e080d656607071815280c650020140c81d421103000c00c4c41c0402050304000000f850407925030b000c44042c40b01800825100c5110340010382020700e804e85507803404000410220020340100300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 116393156 1250 116391906 116391917
    0x618060c180603060b030c210c07030e0a03080a081506120109050f0606041413050405010b04150506071b091803020d0203070f0f020a212303030601120f0c 68
    0x507226800030320031256070041d001c0504011003484483c0e102021640c00c501e1140c10b056132101812148040032207080d20750107484220404000021a049000f0820b0b184a0340d24501e52014100c10000c040910340406400c00d02e0500c800e4141034010b002c0d0b5500000000c1c03020100b524424005000c07a40a001d401c44491520300040100000350b00420ba084036213500c146109140c03c102081e03e60240f4440ca20528038030841800a13601c41d060b040607003081e054002d219510f8241032140c0a0001544118003c41c40c06484002c0598200000710076903000410081c54074401d0b071a1840d8615089500041004000310700140070342d0548202028480b98070021501c8003581d040c041e041c0ac0c401c03c0d03d0020340d0400c128820020340c0d034005c50b03200254022409203070700c60742d070000c103240c240c071600080840c802100d00000700340c41708c1c8024500c151007011a0700b100682c0743d001745083d0701c5619501c10103600c1800070856a600604c803c0d42c0c00b880500c0009080810f0550075010380b50102c2400c0c0200c1d6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 116394406 1250 116393156 116393177
    0x30d0f06050315130606080111091903081b12040e01030302070b090306131e06150b070b060d03020a0f03050307090e040b0403031d0616110f0601030618060c 69
    0x41a00508005180441c0501021440710b400e0040c8250010004c81c10800d24141600400101d503000340040e200302c00007000704407051551880b00e54032140401c0c0c498041d545007284c00700c060a40325000e40b0341c001c3c100c42c245a0502141540512100e010404038000c100444c000740c070006c80a00001c000001c01c404042d491420080d08140040e0041c6000e03406c100304102c260b4900080d401d8202c610142440980e80d25401e00b0101c5400850011341c410140300501c005100d0903410020000503c040641016030360f034805441e961103400b80c02842d41200000150b03170361603c901d139406194001c0c0143e68110322a5582e0303003071074039031004100c011a2020080c0581e4540c0001200c010b0302d2a00340c4e80c0c2103424541c9036a1901c4400400003401c1546a06090119005002400103140810700480d0010b017810328111145d28020b0441e500040e43c4081c8100da82c40000a11401e040c2c1582c001c1c000f1070b401c58542a000d4041e0550242c0c0701d10640c1c03480c00015905200b024510360560b07a0b08803012 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 116395656 1250 116394406 116394431
    0x5100507030e1c030605010908121621090602030a0e0d05030436020f1e0903100518070509041403040e0702100605030c03030a051606020412030f021501030b0711030d 73
    0x49046801c418104090301c1c2301440214800591a03500c50002c50342192520515240380340300403504c91005110701e4041c4600d800c002000040c41079050780a0700d4180d40c0c0c9449200407030b030b6805040203800002c3e16058a14919080c01040205454050b005032840e05846800101d0786c620094010342c50012664070346010150f010021044d413091100c419131411a06200448113801014503020341e0f1070054138a4988410b03d441120600c0c10040d0665a171081ca8500308030090204840d10b48803291031640001c045000425000140c80c0000c0c0051115125920748015818100481c001244001c100218840d0980006280714070305540c010448440440d54400603554640e010703500076880502c114400d03603000f1080d0351864200b4680b05444806592038407c5d074500d5840054415071000a0105650258503026844103000c0e44a10a201d01d4140c0d04036512040700040c00d851000407001800050010349126401008510b010304a1540942a00d401d507408042e0402c011a91202181e000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 116396906 1250 116395656 116395661
    0xd050a0317040f030e040605040f06081b0303120a021201030c051309030206011e030209070206100b090f0103090206091906180f0605160605040303150b030405100507030e1c03 77
    0x707140c030900441040b030500340c0d00c1c1c1089a441c03590082c28012610900400c64585074850401840c0c01013003801800c1342e440328a00100700ba070042c00094040e5441c2468802051700c3e44801d0a00060025441e10300c6015001c01e0090700078101940440d0200000c08a400190103918042d50040c1d00300b0300b03054940410044000c4921a20100150403c58050080313a00401d08604403003034440a030040321030b1812280100b03a45500000d5020182106004600740d0020b2007900c101c03070304029420403a403201020009800340001c1668800d501a42c0440d06500c01e070804044c03580301403c118204044440010344241c1200082e01d500c0080e40070400200d136010965010b03582e01240868461810800d10f858001d0785401a00d0512074005240d0240709500c00542240c0707500840208202d00b0140740c014040c1c00d580102105048017190b001c91500f016000302c038050f5a0110003000c55010140c0d103007000e084014038a40c02c1c0355940d1820442480c0502074004200d210b814003500c04504050701404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 116398156 1250 116396906 116396927
    0xf0b04051501210308070207030b0916050d080a03020702060702130c020c061611150301060201060609060801140915060406020102121f03060e010219110609011a0f0a050d050a03 78
    0x1c04444003e508a403d245262a1100300e401d072400030140c1e941d044040c3d00d005000e9100410f08214903082000e06240441c0c904900720700e051000031643e655100300226443c49041c094030412081042d4120207020380d0041001900c040e01e900d040c2101600000c000200c034040694000c0d4554138000d0b002e540c180120002c0480450740c050401200030b02e8807201191482005000b40d400c100c4d4180140e9648001c0e01c482030342003450030307960361b10348a000f4083c021610804021580e20303000482c000d030040c2c0d07007241640e03500c000d01d00c40c0305945000c002c030590000e448440c0300b6100481003401503c8640082c4050078854001581d1030300140d41001141000405612040741d001041d1030341164044001001c4940004c000b0580d070140085850081c81400201c82220510303041c110600b81c0c0254180008000180a6403c50b548954941c0d00f179841d07580240c03101c40080c0c045603000f071074011007200503100003070700c0400a02e80b503002142260b804100e0aa903650f001d40003d80805510164040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 116399406 1250 116398156 116398169
    0x601050a080a0803180607110d050307080c031305010c05040611060402060702010f05040806043806060a050d14090706050c06040312180c08011a030709090f0b04051501 74
    0x100080c5000c0d01582c69448400c0001d00b0140c00102090845000d038403881d54540d004002d5032150700f043c29020b040c2525000c07004040e8011030305001c7c022801a402d83e80300301603070740713800c3c40715a1110212001e82c2c2c00181300c101c0b0b000c4c0354201c1c1c0010030000d105607642c0c42d055440302a580c07418864060f02250005010642a50249080100589660040d81d1106a0a00300307483d0a610310101a21a0b02442e00484001c0c8a44420001400403aa00d55000c020002d10065083e00000c60001c3c00400215401004140e005010600718200203004108058580ca007007810b0610701340101c016100c210201031082c09580060000a40c0e081c803021000b040107050032480c01e92031040d0261203000c0144081e0500400c01c0050003208100d400c1944103440e580000d59980d11180381205141010b4016224558038103c0441c150791134070022442c1c8100002c0040c0394241c6000c441c4009000c03209000c0b00c08840c80680840000d1112200c02c0c01070f031180300684150065814101d10f1041d05a2200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 116400656 1250 116399406 116399419
    0x30106080f0c060901110109060b04050601050a080f0a0212010b07061b2106030b13030f03060506040302040905010b030f070302031504020d111c0b0603070806010302060f031b040b0c060105 83
    0x7480840c001a00c242207032015950f40b80ca0359140300068a80000d041440d415550070103001008001045c0d0100c500c000044030104280e44601c00111000d0150801c0d2102150b103140c0800c444e440300300b40b000d40c400030608016140070b18880c45156009001e034800c0305070075400305d144401c001e0305018000c00754000f0024480b06204c106001007a1742d124001d00e4880c60b0465250b10000411a00040c0c05550416a000100c1c2001075880c0001e2206190035030009040180700080540b00e40a60303012900010102c5061908607003c200007001d40240032a610b41d40d030000d511064a0a100481030003070040302034071446107140103241c00d01c03900c0c095200459091400708001a5504540003c5894002c05141901d40140005c581d0090710422000b10748441c101852040000d54503100f80705140580684001c035945840c5039035106001c1c0002584240140042c40401003001e001d90740c40455030080d1600071960000c1600d680d0300940080283d1074000403144020001001594010502641c11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 116401906 1250 116400656 116400673
    0xe0702030319110d0c020c0a050a06020312090321040303050109020a050a030e010b03070902090f0913031d180a0513020f01030c0210060b1216050405151e030603010608 74
    0x80450348040d4003820101959808180740000f2040159050f040c11000c017000540300d4181c0180d030b20341005012502c601204417000c21a070a010f210002140c04607002581850b4119502e0355102400910000d200d10080c40045068014070344044044044408081c03054200303400c0040c2a200305800078001c25004001080142c0c0d0b11404070f0340c51a40914000400d05803a00ca0b0901601200d60125814420194082903120541c1c6c0200b04c903040441c1e00024202c418000d1203580303042100d030301618018000100c40403d000d150781840490120f85429003030b0010400254101a4460541000c0c40b41001003198042c0180300c3d2a41240440301c413981c902c03039a0743c00505071030f90b0322074450704142e164180c98807500e00800810390340401e4003406104641e00d809240400703030492035001d80c08a042078041041130314610b90102401d8810703581c45103451300304010f01c541d580c5652202250308034200009a1404210800030020301500d203040c0c0e40d80c0c00e00c401007609482c07441c1c00041c0e0b88d4020220 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 116403156 1250 116401906 116401921
    0x6090405040c15030506010903031b0b0c180405010302090a110c0d050315030f0c1e03070b2d0d021303020306160f0e01120e0109050712031202031303081503030d060e07020303 77
    0x1123000440307a040c80e00d00400049000b0000100e0070b40c01000341444108410701080c40c1c880c001510030300341100311440c08000114201f00940b00c00303220294021150b040410166042c030341020750b51922201116150071115281c20380703001421921800020400b005009152885503101c29070850110010304076201600981621002101d0b0103034401c5c0314240107106012034a2402040a240040c1910700103903580391019107a81c0a110480f4140302d600c51620503601c13045445072040380c92014018100a143c80b23400001750300c00400c0d0310300c21240104c00001a5010043e10384030300c2010412a6001414001c00303001c100004120b40c0a01c0590058020643d82c0300c00e0ba0803002420000c0403441c0001b003900240101400440503045006104010076424800010040b12521950311080203c50000744030b01240015030b0f803c0000d20403c40c100c40468810014a5041004110003502d00c0110600207851603100c200305101158036114204641040034105130b80c48505400510b1441c50b0590 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 116404406 1250 116403156 116403167
    0xe030919061707120b0f030f06160915110a020d060207060c03020f0702370f0603090f12030f02031003050c090f060904050a0204020a050405041d0d0302070206090405040c1503050601 80
    0x30700e1344440799481c40403002c00c0e82c88100082c0c400c0405415210509030075520705440d00c5044840b250034010f124410a5171510503441c032001c403800800c01784c6d00d03074081c820215101d400c3d412001a452003074000356005a960041800b60203071140b10016039a03d0507103003032002c0e80c000600500a01d8814452103059990078012140c101d9070444090a944d014001d0300301740911000a8050304c1c0440040b001c1240300b0b034041c820305807110781d0043c2c25035a0f0350307140440613103d59010003080915200100c0c8001204500c00d68110421828007041c9503814001c144100d130001c950714613100b5090034040040c0f00c0306000d49014464140e480c103113245072218242d402280f0243c0000d01a8000c071002400b8003006005044505134000d10540d55143c20348001400c40e0070034041c840c8a40d2a01150006401d40307000020442c00017540074161407200200e045d0029004544c059070840c00420194146075554070a0a200d1403142c5240040d82c3d080403041e0841c10000b102030014903180800744012031780c210 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 116405656 1250 116404406 116404427
    0xb01081501230a02030a080a06031a090f0a03020705011d090f0912030f15030d0c06020c010f0f0e0c09010f050d0201050d020703022514040e030919061707 68
    0x30b0901108100d0401545048420341030200400d500d0049086000c49a01100518824800340c2d1054001d481e40016001192283d220041a0540009216191491040a255000c0784c1b007016152090703045014141483d000040840041e04625414461986c010011019000911200000c00c1c0710f40383c0401c041030f0026125840a000311000160140b1007003141c0022041d0003000c081c0c80f418041808180c00e1000d5504250300e030400c941d0303161903090001b12004001c0c0640c0d40c0094102c620785401d0300942c8a048100010f540b03036094078000740e52500400c01d000883c500006403a99500802c5030900c500300c2202c3d80301300200b800400c440703c0180c1016003651821078168902c1201e92005a41d80c0c46a02488050b01d80003080703c00c01e241d00450000002a209401d110141440c0c0120b4071900b0311070b0080b92410700d0340f1240001103044c903901810385081c4c064200c902e0715200e07100003074a0070f1603140a054a0042064148a2141c1c06414081aa404410a408281440b900150607980f09 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 116406906 1250 116405656 116405659
    0x3060207060b03071403060a0b100e15220f05060d15090906090c06030c02031e2a0d03020403080703050304031808032505190606030b0a0f0b010815 65
    0x800c4400c00e0010716480003428403001021a403d09540b0302140810310280c40308035210740076030b0001900c800d10038000c0c50300b034060003842c6000b60784d2855000d4881032400701400f41c10580c11401a42d00f10101d5009182d6490107401001c00e2410300761551010309100e401030b507600302084100704400e40b10641035440802c0b5580000c10402c0fa80e814aa10130016a0700207500035041003190002d2007403650010940c02e001d100050a81038444100f80c099a4842440500580c420007294200940f54a2503102c0c24031402a00c5280c4034003081c84081c6914500184480d00d0214080b042054004104101c0d40180d582015428a0310b90780700e1803c5805000009401d0000000c0010700701446120260110b5030a0401000c5170b523100c1f0030003540c03a00100103046040803d82001e6030f41c10700c0010040310007035100008100b03482d0125080818a0b84102080b2001c80d01c80c007000c800110350788a1a48030f0340d00f4040000b00d0f0340f002c544003401e50f98a9031520b814011040140310107107aa03c0c041d4072107000c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 116408156 1250 116406906 116406911
    0x1150f05030a0e010501170c031b040c0905041b08010e040302031b2d010f021314060f0a020607090510090902090112050f1e01061706060d090309030204051501020303010306 76
    0x465100b01c0b0043c10b03843d00d01c00e40c0c0c0c1d403800001040420311001004060111201110031400998061540c0c4510090721038110441003580d500301480c05400030040500f86150031074006a54001040075a00c403070729545212042107046145550b4841e00a5004001c5600350701c940d0305194138041c1d00c1c1c0c8a4165000c404001d101250110441e041008a40c0e100300700b030701110144502c0141d0041c2100000d0550015400c04803109e004562900a480182640d00215103d0901d08208200103e02c0e41c8d401c0350b005102400000004441c45015000c9400a90060207440c540321500808a80058102c00d109004140c402515a6441047c01e0242c620314980166100c07503000069452400d600c6902c0c4c0880d003004100414042c0090107580103ca00001c243c4054031760f544403081030f440901509000605120a07001c84804801c48280c01c82c0010b004c1d14a007807859410f980a5951448040d03000c50140181001103042900c980f47e0301c800303010780200c000310419000030745901c010b1002500c3d154 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 116409406 1250 116408156 116408161
    0x1e120210090b0d050115020a0c0e1506030915060d050d030e0304050d030504080706050a021c05071a04050606010206060d0212121b0c01020d0c03030213050a06020a0b01150f0503 78
    0x80c02821010040c0c151040320b261034080288081010f00000d004040b00104000c203004001400001c1030341e40c103980032082d50100750401002c0c1346840e00050412071805003d9600c5074894845000440c020104440071b41418a40740140b241041d030054030940c01905485544c102203200400c2035400d844540c41d020803494514100c403440e50040c0d4001c20f40c0010703004031040c00c054026006000b150031100995081c5581c52506a5480c010b051031000541c001c0317100e032485001d404110507207072941401c1040c102075003521105c821204050110b15080340c00070900c4244070080040f907a10070000d02c024000c900d40800844e158a0700c2c0c4000174044d40c2c0f0a840c04200d44014045040f11013004400584c5445154500d100803408407440c3d1080c6005000c40b0f10402d520103c0ca00345424420344490244580580d0704a00030f60000c20351500d640850ba0021039241d5078051000001c0c81c140d8000c11261125041440300c003d01a030210800094299015012070f40200152042072454103010f030312035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 116410656 1250 116409406 116409439
    0x609040b012102130209090f090303010b16060f0b21031803010b0907020d0801080d1409010c0f0c14040905150405150705040f0b09090610030905070306061e1202 71
    0x401c2d8100035401960311480c0c5180744d140d60f014211800c0c0440c0c0040c055265035080c1c0c0c100c85803d031030984650708204010b10212203940000c020f0340003441003100e429265900e5090440e2035560740706030300342c1d1251003c15081c5005a528041d1003411001c4040b001103c0b40c501d5500d01ca41c00c8001500c042c0c64034420b02c213035401c0d0f10059003000d01a00042c851b05e40928000d4544c00101c0d0b00a0201c2c02a20010450000014005190f030811341c6400c96001759014540d8000c0c1c000302c581c83c0c100b083c00d648141c0081d203041c0a0a07003071032203114851541810b003000c0c06400d1480002032030013146001802c02c0850b4000468202400d8100c0504040e522241070440c140030919003195415290007041c00b004584c400001c00858031010780c001c48841d1104400800d078070480e40340c141c0c030180440200d40680f9201020415a0303e46050014035150b043d5149410603d03264000d533985550b451041200301c3d81030380ca0411a0080781002c00409080c801c0d4804e403c2414003002c0d01410050100d901203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 116411906 1250 116410656 116410709
    0x2010807020718091e05060406200c0708071a030a0903050c03070c08010b0405090a1b082e06050102030a03050603030708031503071401050403141504030c03080609040b01 75
    0x50401c90801c0a03d1102c2800f0f280d001e490900000c461040c20b605051202d001004010a050396110018100350b40b240c1d00c5083c080c0090700b43c881c10050f0400070a41c9416450b070000e1400300780f0b89010b003c01603d00b44800c0d00f4203109500400c0c00b6039840d50880c01c12103004c81140e6001358008400680b025080c01d0440e02c50050131602d0b00c0501c4005454810701124040200407070320160001d11a10f065501880141c1c2d070160307020006544030011703d0000402c02c02075103644c85500c2d400c2c881ca0655a0041c82d180c1802d581e91100f100034640c010710b41c081107041c2005d0b0b881000320002d200162070440001c0d0740e481040c504a00b09a0b8807004140c00755410700407540816004050a510fa0500c4017034403054a222070506d6100707101d03002d40010101423000c0c0100c0c010105840e014102490740d02c0325200d00102d1845040035005e2160340f880d400c260300c4150b134080c90003662124140c070442d103000380c001c107000b600f00380c40383c00d003041000005440300c4100c1e4195507041c140c500c1784640f000d003080c54 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 116413156 1250 116411906 116411909
    0x80a03080c090a1d070c0209070c0303092306060619200102030f01170619020f1201080f060703020301080d03020c0312330d0305091f090611061003020108070207 71
    0x18080f003040b2001035450010b565000c4401504480191035885041d004d41d000341c1001c0c070003900000000000b5841d103000701004221a8042e080208110320702c1d40d14002500b00041c0c0343d070444605404100c500520411001c0c1e401842916824502402d03584400d04261f038507c000350401030614582140c210254080c032910030040e10095481c0d0a1041c024400502e09018100302c803003c030114441e00f41000074145000312480000e005822000108020103903000954248091b42e040203000110b12142181a000302880c40c007611001c640400f40034204040076040d1410140140014040003602040c0e141142d0000d01f0010703541e10750400d00c1815400f60900181c0010400c1040044102c07411b045180c20043c07645100035240c078090482b41654210880c59a01f01020000240c0000d02841c010010030308018406400899034540b40601d40005541007400150040c4c0104540754210a0074001c1a903204090f12207840e10241c0031880020790f110184c10000508007084080f4000d000450 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 116414406 1250 116413156 116413159
    0x306040605060a1d061c0b01060e01030b03060a020c010c0503151011012d0608061503070f120302010b0f030604060915020d02090a05090c0301150905060309061f080a03080c09 77
    0x80b542c141022a10782c4011144680161b4074980070301d084284410507841c4517075120101c50403a03401c042d0101c0754148002001c07818503949050145040c0c6d41000f0079482400c0042c40540c1e18640542d55a003500c03200d440315024041c00f481400480741c10490f042d0500182621049601c58421000320b1301490a003e0182295290140c5482d205155442d0000700624105489802c6440c1d02c10010480f012807040250507000000821808480e00303400141e047c00040440d0701e01d68551003102d001946982c01551042c0d5003042c1c0000301030302030003200390154003290f01d1042c1c24010404682c40c0d0000400c0100529030740c8000750100270b0a00003010781403070f000f41c0c115292515406400b00035440300d0041c6204d0602d00d14001003503c3c102e08801e1041c08520303132060031a40b03008001000590410b0258080c040202d0700072505441740000b07503100343d020a009240c00e040c020a64541c0c0d8070b00030300c10120091030f8903051001c2d2038006600d80d03a0561501d001174090350344a507144014052101c0c5a0b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 116415656 1250 116414406 116414429
    0x30f0f04060908030f04021011030d0b03070803041508150109090b041515090b0415051b10020301030605060a061d0a0e04080403051005060d0201030906180516060203090306040605060a 81
    0x1080d114800245c0c5840b461003075820407044860500103580014030031517075440943c410481000311400c140c1001290b14009007c0768040754860382d1041c256002508074050894030300e01c003810030301da0003030205822040b000c082c0342e505211400001c107200c8050095041507600c40e000340140341c80c0d940c0803042071460071103202c01068075812000d12561040190400207003460303401003035884600c0c080b542211104140300c1048201e032141655a40c01c1034400c101003e0404410100268051181d0148419082c00c0140d41c2e40c1585803003030441d41c01411840c06402684400e00a1540100b0100c20310b8600030000090594034100044005100c1d4104901030720401d401e110410801740044d20569204100391079180c568184d2140441e04221505540b007548942c04d40050b502a40c403c010719801038001040102c121009081780b0010301d030048440780e10a00c07500d6118620014500041d01c101c2c806903207440740010001c1e0b81c43d8000341014101d56981c8000c0b882c55901d54200900a00042190 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 116416906 1250 116415656 116415661
    0x11090903030106030e15060907170906010f0803161704090e0d0806010c030507150e0604030f08010b070c0905070905090a0213050a08061503071d01030501060506030f0f0406090803 79
    0x4594581c1c0082c4500b00119051200580003503401090104441c0410100060180c0d25401000203260020705003205210454811442c200c0441c0c014521861019006000030b5260400c2c1c40c080e40f180390302441d540c0d041403203210080710f41c0411340c003030281d00850139850342002600015143d100e503520488620380b03410f400403054403001c0340c21003504000340c95038102e0707a480c0c000656080688240003000030b10300f0046400040c00c81e130714220f2001c402c0e403000580000b030144401c1c9400c0e000d4800f580400d001000041a15038030100701d40c0503051084500741044465611940e810301103019050303500c1e0720b400c00190018400c841242c024072000f0000d164500381031000740d009602414180721085c1130040c002c82c040c00d001844100b00c070901d500811580d90b54242740c03a030310440910750307950502074010002208071982248a0203858004c2107000d003545140b80ca982107680d154400c90190340b0500810450070099183e90380c1c418141c0300b03505c07100e507900e113406401041c02400c0140011000f006 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 116418156 1250 116416906 116416921
    0xd0e010f0c020a30080a06090c18090605060403080d0f0501030c090f05010b0d05040203010b1906090e04081603030b0d080309010b01020a02090a15050301060806091e03030f041109 79
    0x8405001c1c0d80254110300b0f218071315034081c0000d020101103048a034030310074900440c03162259202c543e001050070b10000d800c1d901e40719420300390382e0a0003036040003840c10b964800b089205120b2300001440b00e01070030070a40d0b241c60041200e9009521010704464004110040c90075095000714030b00380c4002c4010029580c4a240001000c03405000d1910340d00d24000031111100c60360b2045906980c40609601e040180078543c11003d0a03004004903050754907602400344503202c110144000c4954144407074038850030010010f00c2641290720540500c0d000780248804980074204a41c01d1001c00000044068101d06041d0041d164004c00c464202c01c0300341d0301c40240059000170714051003503280203001441400c2c00481e607918941d04040d500494034004941c1e03100c0c1c2039002414060410071480c1209644500003801c59089600c0000283c00c04c404108a546c0c1c00c2c02540a80141d600c0003200003d03a0401035507882c08020662000b003210301c00441c003846262442100e0142d00101104400d01d8104d5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 116419406 1250 116418156 116418163
    0x1080a0c1e0c05100e12070b01030f14011b02210a03020307021c0e04050105060a141b0102130302010206010b070309060f030f02160512070b0f04030c21140a050d0e010f0c02 76
    0x182180014025450060038421b03e10b02203d0b0401d40103800800e0903400c42c0c40d201c050b143d0003d42140c42d000e140e6a000e00c07040003030048460307030744400104c11311030101c800700607041101040001012419080c240e4601c0039001d401c0e00d03030300d082600c1d005803665a410826803038066100c9450402c0c052000070002d600e07038040c43c800000482981d0900240c5d0b65042404103502035507038860045110010000c038150602c80c081c16030004811001520260090551422030f840301c1030481c00e441800b041032065580400207240108810601240b42481948005002d011103000d4201005030400d4481d1141c0c0c80307a000301e1a5041450b42c2150b491100407440300500340240400c980c1c0340501c600710700c8500710384410740e030300240c2004134060356070f850748000c5800c040001c0046003841504160000401c40a058030b119807142d0350180c1114081706107010b4050080184501c010400c10004004055400416103038002c0d180304c0085030308003c0641c0d040c05410380c0d240d00b810583c500198a4030749503000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 116420656 1250 116419406 116419421
    0x50309030d0306050f011d0402120402040506010801180506180a09030906020712020609151209010f0506130902120d0302040504050c07021f05071e0201080a0c1e0c0510 74
    0xc60403a900001c41c41020340c2910114820254840300901448800d5405808001c408003104c5802110400c2c1d2000007400b2a04034000e02c407003140e400001c210031800c1504c01d42e50400d6003420b00c3c0c14507600d8a04031004610f04c1e0034a8100141d110800b182c00b588910080100301c0b070f4000e07d941e18910b0720306503000050622030020343c0007990200c0c002072400d00100b02c03134003a51190451064400c2c0a6000c1c010300f607208004803904510002012244544604054052420b03c80301ca0300396811310014650942c0c504080d181c180354545014042030b40d83d000c02000010180750800700c0c550b100c500001e045281c13400d00c3c104641c010080c1040240307034180d00600a4542c203c40070080c0303895a0410301d48500031a84003e42000400c1c13040c0e14144d100c00055241c440c054a8860710b065003c1ea101c2007044450000c01e1880000c5403c80401c66030404a025404200400700300401045410300130203041c140c0c2e41d03405043d050150708680e918410055400c40c65002800c8414402e545e070a40002801d01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 116421906 1250 116420656 116420659
    0x60e04050606010f020c04020c1501030602040305250e070c0b04060c0f02060105031e0a051002070b06040504051e0c04060e090712080a050d0603210e0612150a03020a03050309 77
    0x10000051103644c000c01c1d25010382a155030051401c0c412103c1848029070101030034004900ca8901221010060501c3c500e0285109100c00f40c1c446103103140031854118542848400c80b152051031801c3c1c54003c2c2400f1044880d030341066500f0340c440c0f4506803040c180103030f80503043c84451000c00050201c29001340d400c40c0c2d0a50b403083c120f0810904203d03110802800b0700b41d030603000001d94640c5040011210029111814107840007000655600d915100d1041c01d00c107807194021921344240310b450306080303502800549050015240c02e0b60758a0f00d491400f6019080420b003030000002d078178400c00012101c2040644100040c6455081503001f205080b501120140720301c0101150f1014081080403c00b94401d80c0281009030303078001070760180c2054190380314059664a0010200702c5016002c001c0344000310040c1881c50039a140108803003492a8840c3c007810080201030302031640d4002c1e0707680c090340f0540380b5104108298002190100141d201a51104690001100307101c80403000b032080000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 116423156 1250 116421906 116421913
    0x60e151002010c020a0b07140c01050f060f210106050d080306130902010203042d03060b120d0e06030a02160b09161a03061306150207081513050a06060e0405 69
    0x15440003242039448403a51140142c01c1043c10740c001030091070090341c0087d010f041800300c2d841c103010082055040386000c1400b031303074440d000d01403022015000d0503040102510201c80945411010505a50050b5000700c00d1450324282c0c07a60328030007980030300043d103001003580308400700b5410880059001030b0358a138400c024a5003001030401aa2140700398160703042c0c0185003840d140166240d55103000c030018a01240f01d1501c01c080311104102918041c600c19100024051000e02c140301001020182c01d0b1b649500c0f8005c019003407600603a0341410b00d00211192a0745e940c401020502900400104640803100d01d100c0d1002c002640181030b2080e0900c108468014200c510000103641c818402c07441070b02c05400c0000701c003803681c600075640720101504c4440081d1513601c6100407a40154002c59143d0b0803903000b00c15495041c00010000d03d40600201800c0d00c1c0416064410131015002c2d2451070500c0141008104090088076409508a402040342a43c0d44082035500703001114110740301e02 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 116424406 1250 116423156 116423179
    0xb0303030403080c030415050c0d0c1404090f02070501090302062a0d093e0402070503030a020a140a12140403080f06030102040302030f0c010f0504080606010c06060e15 74
    0x5000040d6840340e601541c4100c030907101e0907040c0da259403020b0003c1d60a14000004903159200c0c03400b9060090140440c5243d032a602500c1c05000c40702380fa000e4000300591030864802c00d0342d91f00195010343d0b2070464001400b01009000000a1103002c000078060b5007808172400c141500410018030451200c40200384c1c07030381010b422a01d5186507002c4a080c10b03038240100d0f90a07000c19448960b84a101d88900c0301c1207240c12a8640c3d0044066012401e4112205408100c414600403040d5440740140e50075410f0a000780c0c0c85680701e02008000d132402e6640440c11f1104d4078442c080d6141c1a8052a46003076881c00c2c21480209aa006896041005401c1c100480d0044210405161040b50580e803465000d403144a010294090003070012589513400f1300c400300140c0d41c207102e10b14400700005c0040c01c00500d4000050319041600d0340390024088140400c018050000c07a98a83c40785091a110010040520f4030b580107011a07002a40c003854040c0c01c0020340c08001550081d0300d101169a5403542 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 116425656 1250 116424406 116424409
    0xa050f070501021603110f180403030c02010207050304030f0813060e0f01090e040b0c040f0b0403021f1d030a0606140a0b0c0c010c05010b040903200105100302012102030106020a060b 80
    0x5190b01c002d13545a00110400420100703150702c180c129601c00052501030002c8000c4005041051040c0c925003216824030140010175070180300f45144450540000c1d0300340820f0b80c641644a015501c0041e10405d450043c0c03a00f0030048004590408804100307002d541921000000c21800140c140a0f0260017102020500d640c050390f1040119145810035a041d50b440d907681d16003501d00078100f281f051400b07002c0482c14012203c800d5000d40f110781075a42e2664550700401a51414280b007a0500b41c0f880100c507401c81d980100c208554142e28040c0800004600e400301c2e2034007010803000b4128910302000402e14106e514074070141c1d078a044620403d00c0f80c0b110389001c1035118245086040f030b846100800d2142d401120715600041c003802c000501c4034441c80200d000e0301e854440c210006011040c0090352800c080034140c15103840900208004d00d8000800c001c6513840b800003030305028040a41d5042c041d9061041c8000140034031065440e540e64400181d510b0003290000c0314040d09042c07000d0181e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 116426906 1250 116425656 116425663
    0x507120206030103060c091518050f030d080408130e07080a2a05070209041a0a0b010207140301021b0607020f03031510020f030403080301031109060d031209050a050f07050102 77
    0x8640c0c00526052460f442c2d642e0745001064944014018049090f01c0015202c80800302c14042203640d46404005c0401c002440c00b001c40c0c10b070000d034480c44c0c000c030750a0550385001602c489089036605104080d81c48500308400c90b405001d000ea2480c100c40c0ea0049040b19100003503c0c042c5d00c050300c03082266242c400154060b218800b008001171010820071127210941e10341070000300812800c041e4a03104041d00400da880104987c1034070b41c1c040441c3e859003010380c16203403070b50b1103444100c0802020820400007034079440343e40b058228034070040d042640303165429412903500307014201901503140020300e0700c141c0ba070b682101ea03070001d4012044007a100d40004011030b88200c03903c00b4041348021000c010001c45001c0d5040013401c501c1030015000316043e04100400245005031181c0740c4030b42c5146007240584016945103401583c07031f02c06106441d1555000348101c80d41c0350600703411941c41070700c048004100a080140c568810522400244140451030b44591044401514669901c90006995 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 116428156 1250 116426906 116426939
    0xb071a0702060f150a0f030605060a0807060c06020a211e0603020a180207170c1006050105030a0e030906120f070906020601030311010605040204170124120c05030a0c030507 76
    0x103060180e00004801e208130030b822180350a00180100280707a2601c0140340206126042242e01d50394902c288a01c603d0321901c108001c2120000a00c58a41000c1d0000e005071600f440081c8415008240c0c0b01c44940034104090000c00d20411030640040e0380c0d0585c00c080e103000d44240c081e0300c0c1d00b01d41e04446c82d041406542c00743c030340151800484602e082d02007101d0360600030050340c806500f80019000111001d240d511000003500c4203030784509654010a04040a603000160399502d020b00400490760802e0030740b40d0050b00c41d800000c4561488011909501c00c0d140310581c040c0000501c540402d2540103007502443c0c0c2d0405000303140d0384215080e240c481d0103010b6080035a000718010000a44500e6941011a502c0000404c0c2e46503203201060581e00b041d0003070060042c1300504066510303400d1240001150944560021074480f2841100c000003450083c10000c01d21044014148690134040f8070003400e0207422161502d000d4105038a420680b0b0200300e0359070040010000d021070500101c0030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 116429406 1250 116428156 116428171
    0x60b04050d05010905070e0709060c0b180a0b0a02040612061a030405030702090709090f1515020304080601030303020c0d0903080901120902090f092505040b0a0b071a070206 76
    0x249000d061104105511810880445035592190000350000394140030352001081c85070107181c5542055034000c0c10354907581d006141040384644145020454407e0130039000b4003000d0b0600600305800c07070140e06007940d150016003480828414001345542c00e50040c42129283e5881d0120300780e840d20180161940e0707118510052198030310401801c80050002d41c2c00504c0340e170450f49009040d0303011418102c02140c0701d001090a0090412541400c3d0107003210404243c17504001020354030104000e5180b560081c280f20711800d091407440d0324002c10454010741304035170440e640f42da5280f83c010040d511019810101e0300074680d4400700e0500075580c18040d03035030045403141000c800000440740c041d00440205407032900c075107000300540c68450f540c82c040c8034807440b501c02c145411040b140c60501c0c4543c44900201c81d0800180d6a403001010103400c0c0c0f401183c0120f580454103000402e0b8042e2500404229200000c040e001c008051151414100b0302922601940d581d041c4103030303111901220141c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 116430656 1250 116429406 116429429
    0x2120402010806060706050a06030b090a020a0312020f0304140312040602030d02090a0510020a050d170402060d020903031602091003020d060e0118290603070311060702100201091506 80
    0x800541c011a040c40c0e00c4200607061505040e03d540344c0c1c50036900251120b082845e600c100030b01c10710402c10041076100c0034040003080c0e401090742c0891010501c0d4031014100a054000075030b90b0303031f10910020200701070100072203172a16180c4890f6400d601c0303140c950030311178400e40390b20342c5a00c1280c4047d10f0480f492a0040d40c1414460800c6070042d500403038002e40e01904a600110f0990346100070364034400c01c03660060100d014146030046c90800c1003141102401031046511a4038800b80006552066040c1c0340325840d40c0c09000500d01900854040552500001ca8803c040c0007071101c540d41d050f4002c448900784d84c0c41d49225440c0d1075449000280d00886c0001800c07000c0b50b0b5a07001980c80d400620000500889040c90300a140c940700c0303108407242c00c0801c1c1c1600d6001e00c140c0d08d010b0400c040a00c030400504000c1c0010b0360380d04152100821b910500d0010102d9582e90301c0940c9c04254010f07000c8a1031000b0384070024001c119240040303500024036a0f42d9494480c16225410540e004940d02 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 116431906 1250 116430656 116430661
    0x50c0a030e0a02060a03020a0801090203010b0714070909080304060606091a07030905040f0209031b010813050109021504080f1c111e06010302120307110d02011709030d0f0212 77
    0x2280600340503411695035102d9081180016100e1130000d103040c2c02c40e580d0050f101c9208071001411050183d1140c1207581c0140300520840d00d0302021104010742c04500300b45071410150005040108030b42c800009146000703043c4040c081f903030008510a81c81241c081040c29218081603c40c0a03960007000d0408503642c49010f0400c42e09030040c06001e009042000031a5503c0f0002000d0b680c41300d40f2020465008505e6154900341086480e690346600b00f1907075960221400000c3c0301c2c0c2c80040102602a0880e4034210500c40e003980900c04994020300310801d90700202582c45000d07401442910024480c440144424910100e002103042c070179078207510325555220b441140d82854014086901b8041c0c0d10400d026003103015950510b03010f51b203000d00841d40c0b442c010407151404002c1100d0003900104100800620801c529105100d400c42d51085c681809000480e10301c0303438a2030107400f465a040300340004494004003804400b080b00f24180036241c00001e0a20580c007c0900b00701407881000007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 116433156 1250 116431906 116431927
    0x2030a1103180d061d0c01030f1817040308040306050402120f0601050907050d05091c081b0d1805010504060b0d0507090f11070305070b1b0a08090c180118050c 70
    0x20f00d0301c009000f250042024624152000c012071500d01440119602074003810b056942c050203010f901000031603042090344c1240b0349103600b41c1007150005182540050001a08281000644010b56084072103540c07200e840e840d21400400d01034600b07a106e01b0b42c404028444c85000502410705429a00c050509030340b802d410300080c0140601190280a403e201c0c05004103240c1c4a080e1280009130024503100c580c6c1218524000d01d980ca141c0c04000c205410000d20070758410f101f505428102d05642d6036403613601d0000006008003400d0300307004240054042c3c10b11005400c186d0056005201c200414040341042040c549160000144650800001013055000c0e41d80018040c55858001150000700295003001e81d50200001b14003050011417030b030045c4404c4d142e142c2d41c8100e0240004100100000c2e600449000e004000300401c0408000690032050601101100b08000380040c4881100da400c080724003d8240640361600c0102c14088411f2881400b6050003051403050091038002c5541 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 116434406 1250 116433156 116433169
    0x100b04080a0f03090911040e0702010c0219022209060b0f131802030706050a0806060a0c080310030c080c03060603012a0509090103030e1002010608070605070611040602030a110318 79
    0x10b040e003d010340c10f40b00254070380da680183c051700000f4a403c1569603003400b00035805804080c0040c1d046a02d0104404102ca800003130f100340416820441d08050802d51002400080b140944401641808804c0800c41c81440d0003803450310740307d00c1c8188040140b110500848090019405038000710140304220840c03015408000c1c01d0b82c00746d01d1041c1d06d280940100349403441c240d2080d4006200012114451540300112942216084a80c0b0389040c43c1c14100030700084080001030108034000002c1000140ba403100d4100841d0b1001d402201030307507580b00080e281d10f03a4401c0700d03009018840000700789140c184143e24522038414202905d40800d03c3d8401110403950301e1000c14002c042001d03610f1940e803401d40500a42c880c3c0d0710380c0c0002c0c500005005003c00001464019603040030303c248005600407540400790703206c3d454121b803035440604051010b0104d5641c20060b800c800030b80410b08543c0440207241c00585604c031030100180c54000c40b41d69104114070740e540c641086a40301810b14114 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 116435656 1250 116434406 116434433
    0x15041106070c090203151e01090302060f09030a1506090209090c0a1403040809040b0607020a0308130306021c060b030c0405061b0607020a15090510020a090b04090203100b04080a 78
    0xa030b02e515000c60701c88440e03034200c1e031050b00d491141070800c2648059a00c1c141001c601d440705044011400c151259001030820300081c000244030303002c082011444074a5640a03140f100302d000341141c44c0c80e071040c24214071003d0003440503090706080030b0001c52510880c1c000c071180c0400c00703400c5a40c00e80e14003482290a800074050a002c010b81c1440c0d14803501303003180255005a003d40941d030f984a9041c400c201c125405940200c2c02654140283c1b405a510002c83e00100d0340c101c0303901c1d560f400c8040200003000030301740c02c010169440030407142c1261103507502c20b1807905500c0c041049119116940740d00b481c001103d0036120400204000d10060901a0180682503040e1402032219071100c07120034140700b004c84100b40180d108045880500590450f04407007958030880170860030101d5141e01d910b50003400368121070070790006040c4a110384200300380300061800c007000c603403119121144d40c4060351054600f690086181d25011944103002801c44044690100c02092180455a500140760340d00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 116436906 1250 116435656 116435663
    0x50f0703030b06031f0609032301111204060e03070c1703091c03030c030203071d06070c030b01080c010f05070308060a0b0d0608010f020c060103031808030a050c1504110607 76
    0xb240c400d200c060721000059402140880c1010380c2500c410380348504d090f413140d4085010001e0006080011529080c038030002e035402495072681c5444d2644001c0c0c00f60064404040d58500e00050043c041c0a00c0c2804a0040d03124420600c1485000399034a80e0301e00820702c020701850781400f000c00005001511150b5401343c00000c1c2c90900c1a8040004c03140c0c42c224040c00c80303400006c1c07000300415a06200c0d8081d9032105090840c01c60900c600000c1c20500307040b07206104902c10a03121002c85d030311602030ba1f00ca02e80c007134464034038280c0343e160000030100c080c0310700b02451240021045403036000e54607800300c26100d80d8a4a0505249840c21228000d0203000160010b40030240810058003040051400080180c00418500e182003411400c440c1001d401000c0b003031041c007101c03c0d2114041a1941101d81529180c1c02150003192449013446099210040f1484006165041e0540103006400318068840039520703000c100f201d0450025400b164000d01014405600300724610b0100013030801c0d10701 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 116438156 1250 116436906 116436911
    0x4082a0f0d0309080a060212060108040804120302070801050a0c080114010c0b0a021e091504051305041406040c1409090d03050703020c0708280507140f040c0801030b01080d050f070303 81
    0x560b0000382d8204045d03c0016100c403600002c05007000c076a20b40450340c1141e82071804a406103415281c0354203d00581c043e019000101d158003100745482045039502030510380c0700800850515030300e110001c03d141600c050101e81c0420002501c0040d03460020507000040e120340303000c2c003807039a0307004030806004100b94000780e401d01480742c1f16940861600390800c10882d081e030b83c510061042040085c00042514841c800401c03082c40151584070300540080c56520010034aa210b5152145148004281503002c910841d0b0806c000c1c0702c10120160f0440d52400c0b00b100c401c500000600c8242c071000c9800c0c001940c400700c1c1c2400303500d2203640020340c000040d04d0010f05041100c1000c1e800c046580e805103440f03074004c10b0020b4510844400fa07000c800841d2022503050074207136070780907190381b203500c105141e4001c542c840800710b45541580d80c3e1047c00041c07040110b030403075100280c0300301828041503400c8070000c000825911000100d402002400e525054100002c01c3c0c42a9480d500c4000101e0400d074 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 116439406 1250 116438156 116438159
    0xa110a08030a020d080a0c02070e0c04030b040c0311040905030711030f030c010609150e070e15030403020609060606030709120602120c0307110102030c0a05180604082a0f0d0309 78
    0x103009001909500450f64041e008100141c04000c046560291100c0c0c00300e844c00c1d0f40240102e030001044030444940c1410481c0c143c0e115103020a484c081e82c0e03c040c1c0704803480020803042091500d18001524818040b1070744002c10034040c08210380d010300700109107500401070070011a189003071f1140766020040c2114000305000103a03a04640002c1001e1140da9101c5005000c5800e030350056044002a5440c0c03080071071726141c061843c860b4050305440030b004069000421907254107141e620910034120750303144c0d641000e00d0002d6582d00120303158010ba020b028042049407600e203040300c1c0141101d035609020541801c1c1145e40040d150308049620581c200511987e090ba900710151003040340e010069240d1800345d40c040d192840c81c1c1041e4100764410802c00c40e040c0d851360103540c8044a54038125448a02c9034800411051028901c5a44150702060028220600107840d920801d1040c003000c0c1400641004080a0b0f000850440d5204000f44000481410b11180d281401070180c504000c100303 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 116440656 1250 116439406 116439419
    0xd030c030f2f0703150b0f12120c0705100801030302060f04020a090f0e070e041a07050d05091006080c0f0411370f0f08060d0311012d050610020a110a 66
    0x501e8405624550b154546c607442c042032410f42c904030186201038070f0710840429100122910f640034040d14910549004c02e110704001001c103d860301511000d00000c0400c00500f9001e007120030f00344011001481040005146607544400050140354050308500c52103091410540140114503582419180d440c4013440481004201c0c110047c50003a00303000c0b4a04040c10800790480c808000c002d61041c805041c8030406030b1000c2222404180d6400002d441d031152819103040919444030703c101d84d81440e00100f28503501041514802908680c8486070780c10030000e200694059040c20750381144c00b40b0410841c01c01e040300b4428a0b1703400907050040017004010700d000780780d65041d84900242034a0314001c0138a8006800b12100c50240c1405421803604800142c0e03d0503100100404100c6850702a44009400f500100c5c4050700a000d00d2180317150640302181c1e0403a0948012205904207800b19525040030884004002c2301039019140d400707056160458180316180c401a007201c00c01c1e0000404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 116441906 1250 116440656 116440673
    0x20109090c03090b0c030f090f1015170706030f14060d140708010504060f050121030203041716090b060a11101109040b010212120a02090d030c030f2f0703 68
    0x100e5200742c100c1d88908003000c5903411f481c0010098942944000440c1c101c001001440184c042a034540125081c81ca028001043c0f0b83c07254094212441d0401c0c80d040320003804114441135901e6550100211101d0090301c0301a03502418148040c640f001c40440e0290801d81d610640c01c0d401400119090112a10502e180420780d40c09001c01e07035918000d1108020072801804600c0d0700c1100140440e50504218070084000c240c42521400c04110310345080500030b00580e0000e00c03a61000d403420020309444181c07940410002c0041720301c4400400700d855890f81c03045400f1000060002400d0440c800004c1e91502c503280e1481040b48260079500c005044c2d2801408641c50401c400c240c3ca680702141070005442d00c6849040c199040008042c09130780640c0c0550340c0701c40c03a0313000007401c4c0d8560090910081c0710b03c0e6100340d08031765100c211384141600501410192440396aa0200e51252030100725108c002614141c01c076252103002c02c460040c1c5a204110303c0210341e000f520f00c0780c1c1e90307540c48014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 116443156 1250 116441906 116441911
    0x160804030b010801110418020a0c050d02071806080d050f040e0a060e13020105091e0301090503090306090c030a030c020118090516090e061c0c08031b010207020109090c03090b 77
    0x20710040c034000600100c8400c0c0158206113104828039070070079003040c10f00c10003014003110b0040c10560208028030144d2060340141c92540e00705003907411a051801d402500d690ba80e01541510410304100f072585000b03a8880c400407510402d001d0481e500e4a90011912039020602c1c4203e034510900c008180340002e01c0c1042c1c0640c0a90a0004803036107070141501818038018a407444000c1801040f50240c0d070000700301ca48a1008035140a586240301c06001c80d1140002000da070507601e040340c548104003001000b070189005c200c0c1115069a20b42c000255030b4145406c3c255019040101480d00080c0100c400c0300d9854030505009000300000207400c00c0a510661182e00380c81c2e00c03881800b42c0d0b942002c0c048100d140702440d1090203d810104000c06641000d41864025669048000c107170042d0022070702105540b02500024503599140c04658982154008440d0305010341220703140c8100510031507a000c7e6041c7c444243d4140b40000c0b007001403c50b00c8540041c540c07200d80301c0c40059111820f291 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 116444406 1250 116443156 116443163
    0x11030d060509180d1b0804170c0907090e1803160c050307051804020409080c0c031005070f0c03030615020f0606040207170c0c04090303020c010c051e16080403 70
    0x550107281504100b8900030250240e0710b145016000800041804540b040004c0c0050070005000740706080d00f02281039211601900d500340100d00810398140d00b6220380410034000701118451025101000206031080d11988046060343c2c40401c0301005a0391305507030090200701c180420640b91400d09003035a0201e03200128500300f11081204101c2510316a4000d40020b0300280080307401d25010031446c6144000e03c42c01040620f00280442d03665030000901564040c40c51511010003004081d03076660711210091181c0500c180700f213400041441003c1c07185e03905a4600c0c81300784803c1c0c0152039003052200154101526008040340c110b2070841181101c04140c0e00902c4440c40c10145141000760150a4602c240c2c010007018010070745804141802030301400301541c2e501c6440b17141900c0c10321800c0020350014106802c0105040d0113901800f00003c40030020f00016000140444440c894003403250080010348280003c030441c40d00180580c0d14880c8003d0950002d17946494289411640c4201c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 116445656 1250 116444406 116444411
    0xb0d0c0305010c090b031009050a0f15170a0308060d050f061005010908210a020f0d0507050d030e3003090616030504080403110102010b121c1806030c11030d 69
    0xd040c0c83d40c0c8406200700401104031018150309100500c01400300725445010340320b81e100d1001c2100b4080e1580144903495840008000d20408084d90701c3d0b1980c03981c13007000a001a211804100d035a404200c9091250b4990348101c0940ea595040011104560742c09903100c1c0714441c000090324004003c80c901038182072841c2e90700079107420300040042203150030030354640e0400350003d801c5111034101d08150810040b8203984880c00101d00320301c0d00710107085602c010b105800d0002d0314660070070001c11180b80141d06403011801c5000080c0d0a40703210a15001c12035000e040d031a0000c0d0324400c41c20308407619000c20210f00c015400c090000b00e800654a1810a401c001c1c107020703958203d4cc00c0c0c20306d03030041414184601c0c503080e22902c51138042c0f8813014240000042040031141e00c00c0d4000c0b8410701c0010404e0340c00035880f0880702d03a900d40c05002520300c84036501024030100c1c042c2600103035030400d041c0c500305401d0410800b240540300d0341c0005800c6c05a0f00703048079850b02083c809444800c1811600 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 116446906 1250 116445656 116445671
    0xc02030708010f0b03151513020307030207020a0602010b15030c0408010603080306030d08010305030304020405040311030304051605040605060d09020319030806040c0906050a11100e06060a09060b0d0b0d0c030501 93
    0x208001c492200081034401d51052144140d840d0641d0350032a0f21084011095601d030790b210b80803c02d2600100304603d1800d05c0000bc11107990381607405440241d0081c0c1c0e941d103219485000c00e03400c07280c9482e5150782c80700d01039041c04092400c5500640d030013102059003906040e0740324105402d40e84940c000f1101c3c120080104082810304000103d092007d40c50020569451a150b05403603101c003500123070050381c4805c00101814081c0344441009524003003266602d150a04080f0741b00d0041d007520721014016440f00141038a8140030300300c00d4230b03401413260346499484200c00000b00b001c510304a8040c00b54a050b284002030920700c82516030700940314000540340010030001180c5120f14100c0c00d00404070030500440b1b03448400ea4409460b5401c091104011010020b464030b21640c4101d9116410b01c2c0d000340c2049004204903004000035242802c8454640400005841c03060050010a40c030500244d4519401034109952050019160b07480600b91500c0d00b04000a4a40003914581c1d1100d01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 116448156 1250 116446906 116446931
    0x17060f0406051201092001050403120203090907020f0d08060102071403070306020f1309060b0703180f230901050d02090703090c0b0c0f0606100c14070e060102060109020f0d0207030c0203070801 85
    0x2941501e100140014044860141b001a20500407400060310110501e20b64185160081040350780440d4001c01c11030003480c01d00d10080d0354403030511004040780103141003a01c04034040d0208a0160805030050502103060031040f4071302c1d444410949030306100348130002003c40c4d8544010310040c0060814160341724402190300302441d0240e4071128001c2d1a00380104400d0b00c00109961080d80c1c98980740009110316242c031503800f403180d04110000308503540d000074011070801e143c84041c0705940b140405aa40c40040080c0400e0901c50301d504403504464034801403908800e4141d0102d131600700013030754241503100e031040d4940c180c0142c408801e000a0b035a01405e1704104094032074003504000c020760300c1c00c0740210707180140c10009030341482448450b2204010004141d440019220f5040712455903a40f14244800b070301c2520001d0140c000d00d000030580f4000c0307008640740d11740c1c14140f0610700a44203203203400035070005206808010a030300f802e1005980c14007455000f4000c5c2e81c00800e101500c482c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 116449406 1250 116448156 116448173
    0x308011202010c120c1b05010203030103061a0307080d0906080f01090c090f14090f07120e030d02030a06050f0307060503010b16060f0f05060a0302031c0c020d030804050c0117060f040605120109 85
    0x880b03056446d60748400300302603a40002220305480e803148020031209000d0420501c2c401c441d400c2203505018051000c1f410120014801528140076a02d135401c29540b0130041e036100c0e400352400c034280c510760300041c08044116044000e0110071440c000400681e20515119504415008015207100500c803c2c401c5181c0242c3c220b42103050b02007040b04c142000000605008260403410300c03aa5201c0640720b03124001481070703850a0032401002c6d03640c3d207800d410400c0240041d000d05407145c0c80c240203040490900103100403c0c3c498a484084c030f90b90a0032000352081e0441001c0c210301001240c0c08800190035405021a400101e0f44041400d44103905076006689008201c1c6010750081c4000700056540055146240e81c80e0880300c041c8103240841c06c0710403102c014400707500110141b04110816520624540c441c601840c20b640700c00a0400044079080044590f581d100081c1d2000700d49145007007044d12558807401000003070034603621004a0403801f20b00da1a40384523552029418140b08400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 116450656 1250 116449406 116449433
    0xd050a0b0f0c030a110c010f020903010f0501030308071b0206040305030c01050603010c02070923090d110d050a0806011101060b1c1803081b040906090e06040308011202010c120c 78
    0x141d070900340780c9064420450b0902004142c145060f0300e4a240b100f0791050b40b000c83c0c80d500d05110003845490074152aa801035880a060135009610301200c0e101d1030091032107054140c991580d40d07100982c8854004a940f41843c05000350340c15002d03201b030001655444c00900c000d52085000d15100c42e08034000c18210b4000a0600d80280d060240f500049030380860413800303440640d0400599813003040803a0b208400c100c6c1500c0a03c814000900041e6a0000782003107842000d9900d00d121200c0110345192034042e010072130740125005200c1088501e020300030003644000180341040100c10401d01c43d509445030740c0d009641d510000502e06c0b400300348000166485006174002445107402c078042004a4603992100074040008210110301c88414454080d45031009100300c0c13645454640904000030000d138815110484e02d042c0845000c03a45c0450180d20640d055254019543e20740803050311010003516080303040018224424000a1104240e0b01d0016100d80d26483d41c02c009203401c84808608 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 116451906 1250 116450656 116450671
    0x210515100305090c0d05010605060c03070b100b030c3105010f05030903120612030a030605040501060c0c0b0a0509030312040201090b0715090f0b070c030e0607020f0613050d050a0b 79
    0x104070030030103a04000134859401d6201960740d07840000040c18624010981f6803c01944880c0015814007521000400340150034000c00d0545600e0300e5441c00e110802200c3d1045200500c41480005d20340800c0c64050100140b02100b1400805010400102004080c580564020440c00014442940d00c45000300e007003ca18108185903091007000d01d0741e01d0041d00c44042081c602a000034016443e401500381c900d56606040b0713170300c82c4440c04000d0080c009a025290186141100001d0120b116100c1900301c3c3e60804038240b04242044000d400d654030194840d010302c2820007503030240761804c000900c80d00b0155450302d030550070705100040020b0310300c0d0b00c0241da041080c03000402007855041c050035a02c05e122000110301c19031b85051147c881c10b254001d003c090250042000068100e4401e003020b0348640c0c0c3c2c4229410035041040800d01507410040d4204240704402132079810a400180200151310b0f0383c0080e03056859000a8000e402c03030030103e07416004440e201e01001010108a0b810803034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 116453156 1250 116451906 116451911
    0x3070908190b0612070f0603050a0c0e0607110406051e0406050312030f09070504020304080c0f0d0c1113050112151a010f1701060c051b030304062105151003 69
    0x407a51640850614050030507845040000903080000707400300b000b02c1c0148003003171400130200e65805000e402400304a80350150a820105080d4560784284404d07501488000c2240f070411000e902c501401d815a0304e0b5880c0c100360f0322a404180c81d83d440396040c1144400414224880c0c4180c000c0c4420b45400b60310590082d4000d03145080991086425a9032000b48103484000c190340e411940d80c070703040b4968040c941140c8000180014841040d00030044800c1d010102c45004451188042d5980c8002002c9000190240220000100110039580340e040008203980c0050107101c0c143d004590017a481080995000340f40141002541540d46d807500f926410100710300300c61035410021036824152100c4c100f00000e40a24002402100460180c0c010340300e031103074291303114100500310b001080c50941b598814440111a2800301d01560780d05080060051400c040c94104191848112045080030700f100e05c0348000c001c0c0060b0300c903e030b103d0705500e21071800c51994031044c0214020b400031303186c04060 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 116454406 1250 116453156 116453203
    0x12071a0a0e0603040602040306090c06032a0509062703060c071709060714010e0c0301060f14030f0d0f080f04021806040b0a080a0611030906040303020d0204050603070908 75
    0xc0d0048140074807540d0a0341c28a50726612441c00710024812500700510092500030320f90180150422240d06031000d41c1c0342000480d11240e0750101c0c000300c1542410022101c00740041c501d87c85280640b204400c081c02da0307801d0001044200862850740e00b18440604014108040c01d0318042281c02c1d04100c000c4081c510303180080e103901d034081411000740181060700040c02c031042d458140848070f44607001000c24a00320707441d00109006e0034104c00d070700720148105008144145010301c140000c85001c2450240141e15000d40c0c035040f001c0300d0581c0340d0f00d0f0181c5d091501e0b100109002e088071001d40c9948100c02002c0c40328028201800c0a84092202c00000d010440180ca41c8200b204e011148549051402c0d56414001005411015105038201020480006130800300080c04101584510410700802e01e20100d00c5882c0c2c0030480d0800c000d07602000c00f00c1e007c24002da0080101270610030002d86031548030008a56030741c0c000d445030740c00544c00b6802004094801d00480002120200c1801c141c030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 116455656 1250 116454406 116454427
    0x615060507020f0105041205150c090f040e120f0a020111192016050907030207030207030803041a1906080c030a060e0f19060506010c1208041112071a 66
    0x14007408900a010712140c0003030511a0b801601034600816800c0d038803560300f15451820756210440502c6084d502000a40411041c122502c10394841480240c1030081403c440c40802c0050081c0f0640c8078940c0c0255072429007422029001841c6680710a2481a51807401c40402800c54545501d1900344180c1406030300122407034030b1740800046206103000145025031060441030000c004002d010103110322034080d401e45a007102e01074200d0340d04403101580c6585504003030f0305900c188040100140c1005800f8000224141c028503007240c02811680e80358030517040780c050a240c0943e585120705031850803c18011040380101005400454050111107010b0f1010aa85001410000708807640315010241c00800c10451984100e25070350464603801001290881e41c00c006440030f072203590601d0002240da5002c0d280700921213501c514540060846135070111001c15010308211340c0420b111645e40c44990703074240d140480c40d00d95000f0307040192801d2000e8840c80c03403141588904110500148418 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 116456906 1250 116455656 116455667
    0xc1005030408030a0605190f0e0c0301030b07030905060112020f0102014227050105010f0f0302070507080f15010506030c0a09030501050a020d0608031204080903070b0d09061506 78
    0xc0d520400c0d643c0c503a20741c80031000181007140c000b20f81014501220201001e02c0e000420100c502d07144070204081c3d154514001107034011640c0f218186401c100401c00200040c2c032455000074140307000500040c0391754a09007020400c1c1d009034109500343c100e00d400c0d850030540000f20031070309000030403500705018002c10200100094203d54000408050b103803188400106d00d5448498038070304029a0340b0ba02411400701c12102a030500301d2a0740c8252090405c0c81c1c407416050701c1050711a500d418400b20313421144800c048058004042e000c0c04142c00141e0308004140141917040c01501f50050740c0c10a0501d8000c05042c0c119020415100421050325480200c0b5004201448400e969403d40c1000340c0300c1440682c80102958078010400c0501c80b55940a4003ea0310301360003d01c0040c1e51a850203582c0d004100d882c8081c80480300c003240c0090b000d800100300440340070301965100b55a900f1040c205070031015442401c642c89000440c1086001d01c0340a042d00d02000c0f0980e82c031030600300700500 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 116458156 1250 116456906 116456911
    0x20071406070309170c030a1a09070e0f0a1d060115090f03020d08041e0515030c090108061906030f18030503010603020f040f12030215150d02040e0102030c04080c100503 74
    0x4114004403814412844c2400761940c3c50324064103c4042a42ca8585169988540d00803e00343c48031400c08250000400302e115407c54050004598a40d16181403c0300e000c40040c01e5414820f175580c1d426413031003004807945030409401c40c000d8a1250f15040c1840310808081f940d60b010000900d03818040c5d100200044415680c050720030040d11500c1c1d191983c0301e0b100f66007110407140e141070154101140c94107806400c3c0d0b07005030750f0301c170281074411500011800161144140c402c411301000701a94455056641d009070000c00080090780fa40004c044001c407507410140009845d00405800b01c0568040c7d01108a0180450301c20380455482c020841d01040c0a480304047d0002202010030758240b0986010781020400100343c1561084403450080710710904070f015000e204000c400c07550030070030003520800d0441c100803601000304040001c54003241d030080fa4400c1d0707030760810001842c007403015511030910300184503030303075070510007824a04504840f429105145d4902070070b0b07100ba400000d0380e8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 116459406 1250 116458156 116458169
    0x6050601031503061a0a081e03070b07080a0609020f09150903120c0f070f0314010608030409020c0316030905150c10091a0403030c17060607030c0320071406070309 72
    0x2030b45c568030341d0200041c0407004005580316031404800f141c4424003040c080b800e80c403803040003441c4882040145e03442e80075030b84000d0002021000080c1c1020301940307220b07500024602002403601c4d15400c96804a81241d0f01000c40c0c0c4001246c211451304080c826021007004a2103100d04203030305500000c0d40c130340149a82000551021441200100c1c080004440c171a44c03000c00d98005940303e0b01c40030b2410440d444181e5001c15520104014000f040c820380080d510050061480c007828802d502019504c0041e84041510003041380b01840140203296583e01e9103c0c2d907400c12605e01d03000400041c0c407a41000944800010031105202520001c3d5450600300c40c40300100d292846410201c082c0c1001c0c0c568030f90110070441c104820154141c1c852148a4801d843d90490501c1001c2d0f000e00703c9a0440f080c54001600f005a207011038003a440400841c1e1007854800c0300e4480740d003c5103800950340410141c0507800284207001d0440c0e90f82202ea03a0b84010b4817420309092070f40c1c40080649169100302c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 116460656 1250 116459406 116459411
    0xd0f060602210306190909030309060c081003030f0c1a0126070e040c03020303030f1006020f060c07080415090303170c12191805010501050607020105030f0601051b0a0605060103150306 81
    0x1754070846000600e00070200700000103107401d0140c09002c1030481210501d103001100e1031090b0003802141e0040c0060081c03114040c1c11982c003900e580140300441800d00002401003000503100d070303030f4455000014112090440d403406001741c0b140c800d9002c6443c1501c0400200445680000503420100c0d2851010500d0940b60383c10011080344040e000a5018000003082141d01c0421159450040e4140a031910321182c2d951030490704c0c1c900e102d40d040900e4000002280403428910050045580181c2c07520346099a078100c140c000c000117544850200310814420000d0580050b00719100e14941a040c207420b282454804c0c03030074482c0a000c0c000c00901080031400503548000c4002062544500c00c0286000d0201c2d01c1c50324110344d2100b100d266082400120340d03820042c3c2690712040d03040e1211030071030701c814a0405c90400b00814242c1044414032284101c2035000d088080784e000c0f80d00103090445400d01780318007a544010030703031410f16060503910305540060240320803c8a0b04000300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 116461906 1250 116460656 116460679
    0xf1c24020a051602041509020912070f0302060d0e0a290601051605120a09050f100206060105072a170a1e0203030d05010803030906151e0102030d0f060602210306 71
    0x340104405000c1d2201b9540c000400302e00c0b46c4d0b10758010201100202e405101030104100443e03513542d9580164080b40789591000c10050800d407010b071030050081d41000c0741d00301451a40f5443e100034940c055a1240c820705410089005294400481035201d8003c0c0c0d81030301e42072001900d14400d000e1000340200c00481ca030418080d05100ca4072180124071106a520785d640380004110844074022544500003010071242070b861f140401f40551801c0307070045d209540d5105d0040d00d080d082940c00f903c0c43c8205540a0022070017405a030441d20068110310007005007007001c00c4154207402d0301c241d14680d109243c071402044003c00c0b4036002444445181120803c40e20201c2c1c00c60203a00420384e90070b0b0900002283e90a80840070710702c070b041d0042c2190511703641c20700e520080340207010707d0315001400450800001c0182000b007103c0c200b01801142d16103241031401c2003c44a5140e956020b113a0768520901400b54140050b103a06500204200071100d94045041c11070b03c0003415003840342d80d51410 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 116463156 1250 116461906 116461909
    0x609040201050d060b04050109060302041503021c0203070503070e030d09090c050909191103220f080a02011d07061e021f0b0f041103060f1c24020a051602 68
    0x1102d00000c03d402c000d01c003c595841800030141c00030300642d0f02140300754030045000740c0f0a100f13a90440c1c0820400f4181c0c119400f030140c00a62201108144480141410350b5980510740011402054a80e941c3c42d170701d2401200c02484000c0140c58580310f0740081c12180b403c55442146d40c000c0d100007040018901c5031541c0141e50a2040b0402d01d504002001c040003544011045031030131480303183ca03091140c0c1e1602d1100d0721051000300e6031040c0b5010b940a0041441c40202245000e80d07100e00c2d0171150440c45500c442c07120f03800040314900140c1d110b1403012415405041c850010001581c000d00c410b5003003a0018202c000c0c100d844080117401401c40d600c40034400c000c0340b01c11108078001100203129000110b0080c00c074a024041c060107000c10300c0c0000341840d2003080b452107824080c00e41140c480000b04900e0310b00002c0502da20405007015855008a42400c21510038450100503000b030703c0810054a0501201141c210002d02c14094104283c0d0400304a07500d000551106c2e05082c1c46a10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 116464406 1250 116463156 116463167
    0x80a05061e280f0806070e1c0c0909150b120c010809011103010602030a0306140d0b04020a09050a0c0210050601050909040c0b040b03060f040c020c3706110c090609040201 75
    0x600d441e842c108408400210141805a184180d415600a6510940d00d420b4262994030788802e101d6007061b03400310350801d108002c2c0210300d20030f4030542c0891200740c0d603007084400b940d002c0300003951b8440c140240d40d64aa41548991104214150384003042c00b5190035907640c03560416041e80c2e06210b485d5001940110082d40041070b00c842c00d0040310703229611040002d69a400020300d14005c40d160086c0828210341b00e00404000d15001414440c01130170341c0d6a04402000d002e001280c1205403400c0c00320b400700d554010b49101d20b103d9280014040111031000703180c5105003000c80403032803600f0b0a00290b03980c40780894140040a0703a0300010794549150060000d080343e840707920400400310300480d51510440080d80141002c036140b2070710010010400049948c11010500980e1100d04060703020304010071202e9214024089001d02c26664a202d040070310003003540442d200310000400d1213034613000000c418440045030700901c4146516404120407550182400784220f003850000b50443e0b1095 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 116465656 1250 116464406 116464459
    0x32a06020a1106070305010b091201021308011505220905031b060f150901031101020a0213050121080703031a0d0605060108060103020703080c1315080a05061e 70
    0x1010440d500d80761654000c1880012900766820360040d200810132141c4240101810b950490104601d000c00da0340801c224040c00381c0e0155455502800203030b10180c42e9000380130080441c9000850f0707440f040703103411107007803016003046102d5414000104120308003071800070f556208084001a541c1914280180346002c2c0039205c1c08070510086d4074105045000c5a81405032048140ea40302c9601e81001c3c4141040c0010074558000900c8070041020a04400d509520f584041c015900c0c94026a00802d400207450a01c0703001d500d440304010003200300c0880401e209030701100000114010181d03a242032601c1424005010551941440c2280c3d8480e42d04d841296a40104940c2e840d4940d4038107940500001c444960108040d030000a800c0d5000380211004c9507403555800310f2598901100184503044440d1400c0c6209840e503010031080d0008810071080700c3d8039190910503252007a000000c0d1174004190a0003100c2c00084d841180c0084000c0c6013017040c003201c2c441e449a03012207400e030349120304 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 116466906 1250 116465656 116465663
    0x201231902210414100206130615031a07020a03020a060207060b0604151211120c0f0c060a0c02010204050603072010020a020c030c010c0305161a07020c0409032a 71
    0x2c001c200080c48a14000600c01ca40840ea079010104440318200300c3c200915501030f1000d07810000c0024681e2a09050551000f8170941d00050201034001814460300071135002164446070a55403000003001d040c44445d40018544020418109a81d50003910b82d0314000713004001b1500820700754200004d0360880e034040980501070648403952178a91508040300889200c01181303003011f51b03d152412501a0109003106000c14510f031066075603160720300308401010303c134030030106003c4003d00710000f8004102c4461540014401e5081c02107407074003203031003400510041d684100010401500e0382e80640e5800902420190500c19800607119680f03c909454400700d0b00420000001021075680500340ca04107540c22200595120003d0656450661a500740419122980c80d00000d22410041100c036079031480c0141a03908554071303044410300c0d003100006080d1400e41001440307a81041000348001088a0512262002d5140900302807031140031040024556507160b00960303034000400303d060b0351 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 116468156 1250 116466906 116466943
    0x3110102090d080409051302010e0f030f030703020703120207180e0c030a06020d0b0402120f070210051006260f06011b2d0c09050a090506070c0201231902 68
    0x540b600750002d5004d400380303c070004c0c0780002142600c0004141a43e11a030f042c1c6411103540007182c20019280c030300701070031076040c418030340c002c803000b0707824800790070072902c40e400503e9401d0075841e1000b6004000425030045510080302086a00c41c1c180d1460280e4100e0b07407000446404005410341000342c005501c6800d4417030040b084040014943c024030140b60031000810001034a00e04105c20303440f8940130105403900f01004039466200400301103801c0503190049132008008040321078142d82c8100d5212035100340301d0f001046000d4002030800001c8400c2c200c00310a1001c50350818447e4407002d000d10300310485900c0042c0c52640200800f003890440f1000c10100d60095140512400c00102310000c00708803611007991030850710030340148810784d2100c0090406802d01221314000d005c000c0851041a03182d04040c0301044007480103502504095a98003190320340c500024102c000740340c4204c2e09002c0300c0a01512540b07009402e44134212160b1a008501002c81e20040303150407801c0542030301d220b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 116469406 1250 116468156 116468179
    0x18090108030a0c030e0111030a0207090509010b0f2704080a0f080408070f14070e010906080703020315060607020402030a090201082a07050f01020f04140301020a0f1b150c0e030106030f0311010209 86
    0x1500064030b0380840304d01203400d103721740c3c1e03102e103490076140041c3d501c40d00040251810b100514140c03c4039070307180107242c203100b42d019507a03500700c07407041801e0f1019100d80300d0004892004c6a41700011a40c0c1e082c3c3c41c01c02003214245079039800034a100b0880c01400c07208041c4a100c04010110700c20440c00c0c41003000311507880e0b443e02d02100d030b044002c0c8150701d1507a140980019110001240c107008580d0028060650b8000b42121141e000170001e0015074080f07020400c5000580e9244061030107803020b888002198680ba00c009026070501400400503400385504020a40450b10b84545440c0c4e00407012544440080ca4140e181a8001c5c11026255002180c10025030743c140d005442110340c61030344510003201040906080f88546411000001c03258903040410600034003401c800340307010b040c0074511000b13240c50344114803106492041c1001d4982010070b512560102d13120900e041d00720300810440f40b541c3d1714000c4018050400134244485045000c0301a802035040c5c906002d40a0500d00300003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 116470656 1250 116469406 116469427
    0xe0402330a0905030f0d0f110d0e1309051218090f040c09060311040902121203100e0609130c0305010c02070302011d1003180818090108030a0c030e011103 68
    0x40d000071909000041d4940c8001596142c000781441d800c500d2100501ba5900d41c00000311030f118820302e0941c0610001b0407025420301c208200039117507041d0700d90f2486001d00c00c810804c441080000d040140745400c080b0818049903010944116110591441540e40c4810f0018444042170554603160701c0403294040000354100d01400600c103a00c288240c090081d124034104007103800c00d01000d813070001c140d8040d1105080603442484120300007000400c029030540724845c40c000c500081c0d04a80100070050110724078101845034082d080d82c0741004028900328003c03030203e8800a1242005c01e100303141041c1408aa54402000b0310b030820004d1100301001d00d801fa50342c40b00d511080340055803a20310110901c912240520301c11310010641c07500e299031080d08801801612407083d43c0881041d0383c1000040058009184112010864200350945201040a0300708140e0200341e40b600100725402e004c5030722441445050b40e050411a2008507014012100c4080d03058403442c852000040d0b04e10403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 116471906 1250 116470656 116470759
    0xa06050405010f0b102705280f0308071203090f0305030613050402030c12030d0e0c10030b010807050d0609020403060203060306090d050403030507050f191b0e0402 72
    0x2c80c50f1001e0b0a001e003144080900290006a585004c00a84c80501c841d0030b580c0c43c140542041d03540f42c010f02c0010303903c0c1d500084220a100c5844c40c8028800f050744409500c4040f1280c00604003201d51400551564440c480c1c07911a00350020300040c404528100c580d0b000382c1c88001e200e50801c0190807580114039001d401588203880b03c2e1700c17581266401c0c2072400082c1c05103a01c0b403940034001c0c0c0f194409503018007034401a0b0011002e00c40c0000e0158803840e550760300c107000c2a100b420005000c440200000e00510500501e8003131b04050a00400128990304191081c1e0496214034001e80e8400c00141030b4801808070350003120240740001800024000c4940155005200403001c3c0c440310b032101c4040941d01c0fa518194840820414802000424004c002404000e401102680d03142002c41c050ba0382448203a41d50321550a1840c4440000d100b80900380105000c90307995a83c82c80f034100f8900818032500284001e2040c003002000c859150506084810500000c560b410840090301444084 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 116473156 1250 116471906 116471921
    0x203100b0c03071b12060207020d1509020f2b0f020a03080a12060f0b091206070527220207020405010303030f0b0901050609011107032103110307020c010509030a0605040501 76
    0x4070304804c41c140840c061a031013054000c40300807a103492503138040790340c0e40c001940003814103982c080140442003021800300405007040006088000500c5840b600c100501e450942c01d103640a00b009014801010680750f81000503040e441c601c0165582c024a010803018112140c0203410440c29040002000011009460391105944480c060070f84404c03c642d003103070294881c5044040142008005120505004090400b0040d004460490014841c9450580140ca40c200000c10000f082a614004580040020782c003010500c00801c0c00320000541c5c0d4501300e80210001c20041407408081c07209070303048500c0035601510512071980e4030708000d001030114009044100b41004800d60041c42c0800f84035060340c50041c80181010501401100ca01030941d880710781d00d109540002c00072031070440825050101c9480c0c004003c024010f0f0042c2078030001c5046c0702c18514140140030310503030080782004429100303180458850000400081ca40140400c0244c107007441c09043c4002c1c840190400c10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 116474406 1250 116473156 116473163
    0x61504030308072714060403050a0503031807060906120e010e0c01020d020d080c0714030403050d0e01080903030403031e06060521010303081602100509010510170304090203100b0c0307 81
    0x825810080c03070340b4003000c1e40c0c0b051801003083c4c461420b015450815503c1e0141e41801b030503403410161030355100342c60b04591070400e8845600201c200f1502001d4810000002032a601c094481ea624000001c2d0460f0b183d070181c4410700c25001c92940c200c0d070007a401301300b1004101000740308200452410584800c1c00245150050240c401d401c40e1003800090154902c0e4110740d62001140d441306040c0c0306907001888100c03201666100321619400b000c001801c0074501543c041d141c0002034200240840300d040f03200e24184903111040001000001c030580794055018103000c204440300024182101c20880d1460804520b04080400c03119407003809002c40e100e011750003202c2402d4a941c00180c0071000d21004001403100400210324105440781d0300c0d5079400c2c40c0111004c0399055200541650030480344114541c0d90743d01000300040c0e081014030000e140000100728004040401607450384514025040c085070004049220300c00f1982540d001001714400c815251140c030100f0317a8507640492801da = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 116475656 1250 116474406 116474417
    0x13050603100c0e131109060c1c0815040507080606160c0807080601090e0a0312020c030f07050615090c090d231c020c04090303140103052112060906150403030807 71
    0x11480340d0f02e00d00c5445642c0d8810035174181000303402e0081000750742c01103103c0c4030180615485040040500c0303036010000c0c000c42d11610000d140001100e16580c0d98221041d10803410b100078050060b410000c5550445019a2482d90786c1c4100d0080c1c104441400d0350003003d00e801c407600000e20441c00300b2550256201c0106581440e41c0c1c0d042850251040390740314a12941082a880303000a0040280000f446003207003000d41800200f2102e6400c64120700da181c0e00610001502400700402400b4265209042030408070049014501003242c2190080001c51305c0ca50008000039a0380d12800e080c0d003e10781c401d80c000b5106070044554010030300c5001e801d284520400e1648818070110850144003c0e5840c1e00a0004d007a04070100005488882001d80505581d07051510006100e0702000c3d005c1c50080c40100204200644442c4202c2e00c010300243d4804428492041050b0b58078602981105045800c6c00e0980c47d06000030701502d0041034040f1781000009000020180c110724454824200b94445c1c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 116476906 1250 116475656 116475679
    0x9100807052b0b0301050603060c0c07150903020a0503030307140306030102040f17060601020a0f03030c0e03031303020f0d08071202010209030307030c030e0109030f14030c03040306020d0b04060513050603100c0e 93
    0x141402d83e86c007651080d80c15000f0314001001100000b004d841d596004c84100d400300c1e655030324002080c0e920350803400001811070001340250309080c2041001454203270015807a514105000a100c4010902d03098804413001011a29943e000d4041d00c015100c0c400380303203c505607174140e00d65440105a5a29410307000c0c0c100000c44544c0046071031205203404c11740d85070490300d5558048009144806203402804007006a2401e661810409012401291140c140c500c500754010014a0040065000d114070030a0712020b0000d0826001e030b400c55540000e04034030344945504280d01a00416030100d0709440082040000d040d4003500c081e4926002c0c4c0ca4864245c040d0314011130307406c40a40400781c09607031003040050016014524030b100c81c0144005403818030f4001e021460540e4425801560161303000b2401c031150541c18804c8004441088800b0041ca42c50300010030302a0076042c010410b000c0d0b5030360000f107030303510140013512819031103a100700f00d0802e00803400741c001c0d09580c1069006036246a103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 116478156 1250 116476906 116476909
    0x303021c061a090907080901061d0702061506180402090402120103110303071101080a11030c04030501060506040311010c080906030c0307120b03071a0408070b1902010209100807052b0b 81
    0x110f4026000140c07056078256650082507075906000341401106640e0382100007030114415030901c6004203180360020640c140000024a8030401a100d001d034040d0240841d40079954200866050240740030444500f1207012001070002e00400d28075517001030001420381511804007031681e040c0c038421100342511110610914ac0c4e03d01031200700801210305040018481e42c05108156800402900082901c486900100100750015907481d10f82c5000810103000f04102170280101070041030303400c0344c00c01d0f10b5038031015810a4810855410b0200c410340500030320103000201c403c44c402c0a41255940e041c601c4442c802a801110403000181c1846007100803101c090162800c0c0e51001002050a0385c20700c400c515040b241d88052a01c03604d002c0100107410402409500010300c100344c006900e41c0d076039180c541d00c000701c43e4035004c08592040110095030790301c1c800c0014a8010394030344598103a4603a40255070b01d01c1289440030800049c55600c031766006908400b0035840800460502c0440503000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 116479406 1250 116478156 116478209
    0x312010f0302181b03130c080105090709140c0703050d15060e01020a0308040809030a0f0501020d0b030a0305030a150918030e0f060d020304031e0801050901230108040303021c06 78
    0x41c0c0e8801ea0504140101e809a4120f43c05950401002e040f0701c29080d44603a550000020b841d2302000c40c40e510741c03040101c0603006010782001043c9455041c810700c0c101e060070b00d40a200041070101da070304000c03920000340b500c200d0650b000100d4140d0308010006104032880c440700c3d5141306190000c1c45070094900c50f9480800c101d0031155060702c1c0c50900382c07600c0d622007400d0381100713001c260107114002500020800070301c03501c1200d6000c2d0000681d5800201030b4842500d50420106000b64040b505a2000903848003c50b0b0740020081d500085407098200007003070101c4680e00014203641418030300140f40c1d9503c08415426842502c44140c4c000814050192009181c20700310381c808010b100a08800903950000c40d8482d10078a886000c60142d0b50f8100d4102a040f202c230000254003400511490820303929285c0544418008101012450316001842038845403c0604006950020608040c001d405490134040300d19008400345002c2802031000300494440d241c803025130741010113117200e8000f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 116480656 1250 116479406 116479411
    0x12160b071707050c0a0f020616060e1506060a1803021201140a05190504020a0b071401051f1e0315020c010f0c090501051b06070f080f010e0601110312010f030218 71
    0x207005000000721700e40b61200420540201640c21030b404015070f0b1404000b040c0303618040d920820b80020750b04800c1c190380d0304d040308a0307100e08102082c00050010540d210740c1600c0d480504d42c601728089021103425540d0404a6a00003034229816503005060440d06400080d603030044c01100d042e030740c1da60143d05403d40c0c070241e400c03034051511082d41c40c00f0106140c00032648140042d00038140d0650710711074503950741c1c03090b4801e070744034040c1081ca4601c030300081c0540f039005801882800c0d00751444051807114843c440c4210169800d1442d0f070318582420b841c2202d00219000382c1000b010340d0210400501952185101d90600c0d443c01440703581c0341c106489001d25070300300d560304c0c044482e040600640741d650089508602c000100201c44091386000c00040c0d10035400da0351041e180c2c810844014000100c007900c8246152081c40040c00401410f84e0302d650b20020034a0b24015a04841d10340b14254842e103880011440320702d40001c00c0038514a540c80c01240c0c8252408803d091242d12602d4201209 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 116481906 1250 116480656 116480677
    0x12060209150304111801061409030a06150e040c051309230c01020a050a1205070804180606030504120503130f140d020a11011206080f01060e090a030212160b07170705 73
    0x1c0052141920803070100e049230b00c07040c5219152085003c0081c0c50503942c810304079005500c0700d41802c042070300218040300810700700308100400d052a41d00c240c01000741c1e009241c0203850000610007003042d030350001c458070b03500f2401e00460001d940301d00c4841d07a8044500540c0707074031903400c0780c2c0f0702d652000a0140000b5084406000d50b404143d0355400c00544442085c0e003005400d000c03000101d0302c0f40000300010080030b81807903403041d8070103155415545541e200300d09041c501400c00021880302c001401040405141c001da40fa51040710305041c5500c004009081000e03030702511000c10600d20350b1042c600140700200c6189005111080365911103048004004401d18a0350041950041745d0b400c041030840078020410300d899414241c81c2c86203482d440401a0344a02c0c0400100043c442c0140d005803008001c1d1107452042e8501964410b21516199034801c000180865903d454000400e1442e40c00000c0b80b030f0b9410b0450005250005040c04026030b001107901003480240260100c40039240c1c0c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 116483156 1250 116481906 116481949
    0x30e12040515210c0309160513050403090b0c03030402041b0219020a170303060111030f16110405010608180106060f05030612030408031b0a0c1206020915030411 71
    0xe01c0c00802e03580e03000032251a440402040c0700d407200286950401d4480c91120350129140e242c00c488007407400c0500c0100b03e04034080b910085c8031640300c0c09415030307125001c40d0001c29107032110310342110340c403089600400426a0204200b8942103001c0300543c010b900841e010702c6084041f11000541303020792180d9001517440310344102520140307940c00301d01e004c2c0000e05004100d030342e60760100d0142d42c2c00d0b00400d209030130000030003c640da082a404581700600600460074003021003101740c0c0f0303489000480b003078407130b0b80b90fa5a600304000031514a203000b1000d0424000382d6524400079040f660140d1742e032401016130300c1d40da0300389544c14800c00c01141c4050f560102c1100c001c450580346540007800040d044401c0895a491001041004100030b058a400455460600c000e060075150b500c0310a011042d000100c844011581103a210810358640a1081004428510340800248038501100342c01900340f0514441c1801d501c000703036220314001c00140b203507030015004100d282860440170060800b03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 116484406 1250 116483156 116483179
    0x150504050c090d170408010f0606030e0c0102100e0106050310200c1504020f1002160f0e220b070305040606050f01020a0b10081b010f0f1b0602040510030e120405 71
    0x101104c642000050003102c0040c5000d4a40303100c1030940344e00701c800343d04076920f542d020004294503124607124500d5410240650100742c0000035200c525003040c00a41da61075003102000e040081d030005006280050171a80300c4200c02210101820b0301c0038040043e440d20f45414890f503440030040344d020a9001014150b0101c50352010b10034200054420307a0423080304040c7e80c003603072a2589024801003540c1c00500c036041d11204080e81144490700411800c16209004102c03040070700000540060460345110720f4001880001410442d40d0603000d04070102d242c051114140d0164130181c040d40c01b0710350902005032078205102c42c5145141c0c00a0040c0d0040807180c020a107518010354000c800c481030025040d9803040024030b0800801d000c0d4151080300e2214072455038001c18000c80a06441c200444900c55140000c0c5c072081d15440d8085440305084544010000168102d0700600b40041c0352004c041c0340090024010061030540003440d20480b1540014071038907200f0f80d400c81d54000e00c04026003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 116485656 1250 116484406 116484413
    0x60903030e19030605100302090601210506030c030706090f060309020303070b0711030403030203180405010f0b03070309061805010609200715020c030a080115050a08040c050301150504050c090d 85
    0xb4810342d101c03400c1e0000d41e9500480003801c2c5014450041181003406440e45e41940100007040a000c0c3c80c00e4103101e41e071320b06070000f40903440401d01d030b00500f5040018940e40b2403010030f00f0610780c0f10003694140144840801e0240e081a031030405c0d00e09070f5001d0000c29450740f5041d4115800d40002a6140e4000e0050900045010034030f1030b072001061030010740b8401e482c4403030742c40c54100382c0084015070404078003030160300460145480d80350300c00ca80c140119403600a5a02078081c09003e8411000c00000004034014029000940a16440001001811010088000840002c55007103449500b170a60008140009000340c1c1c00d1240540009202c0d0005080b90074440c0c1e101850442d0000121040f00820070102c0c40a44001c1424401559507080401001444444141c0008042c2c2685445030142103900505032800b01450b13092a4110b0b441c2d0b8100300d6820700090744820342c55801c06c03151200c05641d500c0960700711401910140040d8a81d00103090060195201c4650803401f03034042880031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 116486906 1250 116485656 116485669
    0x10e030f1803120d0c08060d020904140f19051c08010510090807030c06140f030406020304230c1011031827040b010b0a1e03060e01120b01060903030e 66
    0x303a40000b821551075102c0c4043c1002c0e1600b04401c040241d075901e404811a540d0000c3e07006500120440f600640c0103401d50020b0818000500041c1400c01c6000c1030012a1804010396010182e0003005c8580c10903044225800d500c801070302c1101d0502131410b40849011300180042000c0351140c54000c416820101840321ba0044154500208140c26500207030070034090003504d0241d4054140c001001e8205400600200c01041d040d401e468410002c554500000c030050741d410941c0403401583c0e90f181d41c102948091210100001c001c032004503c100c1c1101c00251070210507000303803002d078190042c0c1c0358203131198254040345407015041004010b5050355180004428920001c0202c4010440580707400c05c40703040c5000319043c01840b84c1c10b11003404008050b45005040103203106e0715004401c10020020703104003501c4800d002070114400003040c02904404040c108614002605603510100c1d548056500001a910f2404103400400d2184c41842d1003000e80f6010f0701c6907a003800e8070100380410b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 116488156 1250 116486906 116486947
    0x190212070305090304030c0306020d0b060c1c0309020301020d050108010c02280c030515060f2b060204080d0203090f0901050904080c01020f0a02010e01060503033115090305010e030f 80
    0x20304d000810000c8005000700b148003002e1409034a0050303d400c0c0343e1003006c0480704152101e5120300d4082c0800702d16401300007a81c40054542102d0072045901280081d40a0040664002c2d4594000b1403c181001013960103541262143c0c1c000b40000c00211070b00380e0702c618026080301034003c902d40115441048040082c49146c1c400ea0f100c403c2c465494407514100448031003945103041650050112a10381106e22640c000030441d40e94409244280b02c111484140d106085034003007a03000150240007690303042d44c00514000d030650f54080e0011900a4596108540b0316101c0d0801086d080e40e0740c24400811410b0b510083c11040e000c2d15030340c45020304d030703041f850a14045640800035440700003034002c090710850040d50004907140d82c10032000b9007518107541001c1e003c3d6000340081288045441d04504a543c1005000074521a01942c03c4030100708a81060321014805010b212199902070300c10350442e0700840003045000b082c08062522449140c607150302200301030014104401c1c00b81c04410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 116489406 1250 116488156 116488171
    0x9070302040f141201060f0e060301140708070c05030a03020405041d03070803130611030901050702060c19020c0603070e030f030703020a02100e090a02030a0b010804021008131a190212070305 84
    0xf03101810844e07642581e605802960f200d8016640c1001411020003803d0f8001d00f040f002805101b49400003002d42d2040140100200141c03500814134680c041d100740e24015030004103a1340c0c0d0700d081c02c2002d03001c0d501c68819035004038504030055480c0703400381c0407003080b1440b5038001d9441c0021648681c04680c0000e0960302c1c3da118908180e80016907148100c7c4103403488032410030340300c1c03400f0a0039500716070000f401e0b07000b50341000040080108103030044035400380c0c10019010f144010b81a04a21700400c41d034241d604032100206114400e600141b0f4403c0c4408220111480b004040700348680703d001c0c001c0b000307002da400301c00801e005150248ca90f5542a2481c0340c240f0400b02400d000820a400540300107561940c0041480004e0401b070150004219080c00c040b40d944c00e1581c00726040c1540b0f40304580070008000080b8200c1c1150b0780c50b4214958106c01e52a00c925802103c080d01c905003030b140c0f0015560741403229942e0720454000d03a54000350b04042100a9561501c3c01d5014140040002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 116490656 1250 116489406 116489419
    0x10504080d081b0c07030201121d06040210170402060702060d050a0903180e0117031b0c010807081e0c0c0a050c09060315071b0f0303090209070302040f14 68
    0x11560358000c11240310092110b40d506105410b01041c0020b810200380585503000c1010803d0901c40700b00003421204807a42880c190144070118140d207001001254801b107410156058104c441c29800540103000f43d000f00c48a00a140d08880195441407590020f260101e0000c6c001170702502c2c01c04050a401030001e000341c2c0c907103084010701d2005c031101150501204e07503035041914145076011000110440555455135461400d0110002408405100c0d100d01454442e801c540201400e00540e90b1600c2d000541100303842c81e2580070b680324102c0c0d1512034001241c4000103a8224400c0a075680550340046102805011007118000464802440949440410400281e42804c200060421a4003400190482a074144200720b040e040c0030705014841e40c006820380e007136a085106419000b1102d404d20301d151038140c1d80d07901c08902007900080c25640c0d0904400052642580203d0380951003110a507043d5900d00d0b80c2513013240500d00a11070500840d100a01c2040c0d0710100320700100c0c0c401010b4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 116491906 1250 116490656 116490659
    0x5030a06030c1203090b0f0706020702240706050717040212070816030b06030615090a18061a01020106031106070201020a02150403050f0303070804031d090a05220210030b010504 78
    0x503a000c2c0680d9034002114a258004070304241031748a0f40f0384003d80b01c1c3c103400600c1c002041c203041c409030013145000b4040550004061b42156218106c00c0c45104101c100000c1e040114501c4940a4100000640300176040c6000101070034130401d507070740c014010240e401146407100c1c3c090009540e0354681600140c441d480e40803410070001c2210100442d00c1812805140c0e0641c0782161840c0001303402640258011024009030840c40c441c2c40c1071412042d00c20011a580d214100d0000c0c14044c4c96062020315001088014003000d60021200c01d00e00e849240b002c0500c00004a081725803621020704a8007440310280441d00e0329030000c000c46801413048910401091300000c140c50b403000102900200300040c10403c2080502c5009000d40b04800914150f02d003801d0068500c81004200508101a5894020b85841c1c20400d07a0a581d4000c1c0c5400f00600d030907080c00d070080405440d14400491208401e144500c0d4490058174400d5001e400700b91601c00c0301c1d006030b014216100505060100c103100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 116493156 1250 116491906 116491913
    0x3021603081e0f101403060604150e0106020303060a080c0d0303050a060e09010212010b03010b120403030603050f0c1f020304031b05031c0e040209060304200a0f031407060206010605030a0603 84
    0x2c0c0303203000f00c028410004141c10001c86102008046900624800c0c40f08402c840c1e00d5500400c807542d000e40c0c250f5020510301c10a0a035520401c541c0d03001800c031100c0140000c80c00c0350703002019500c2046c069841c20001a21000c0190380c603400b941e00c20703031b100384046c0700200021b119800082d0003502c2c005010400540701e100c0320126604c111219034145c0c0d40030444080d0311180088060060060580162071541001400451449045032286800d0380d850b020800705486603101000035904601607601e028400540a030311011207038850361185440d10401c44070000d41c418540b80c011032a070000e6140c41d2540d5100c0340349052200819482803014000003c6545003440303000310000d00c2d101c104a0600c003042c4040c00e641d81c90510540203510520401c9945e41390001141d401c05e4100019003542d402c084107156100c50320011007504035090240002d85d1070000c40c20581620300c114803a03050303038021088880e42d44c0c0c014440c0303500590003600100700c4903008400464025140398408104141c41e070b02c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 116494406 1250 116493156 116493211
    0x4080c0915060d11300a0e2e061d01050102030f0a030509150408030a05010608040f060b0409080d0b2701120c080d090623030601031e18120302160308 66
    0x100204541d1a0317404410b5010500d2040841d44010044002c100d07403410312100ea59201e4106948203d11140c18604c1d208200218035600001c03d00584107119203a268071390b0700d0800d40c020a400c101c40003260b0000c10389600210590301482c8846115604040c8070090450113440041c0c025590f41c003410340f1201c1101150307020988680c0c010280303113582e410503041010413214141d01c04410442e40c0000c4c403000840c440c2161800a4106c0e030040b680501d100001001401a2034000b010220300007415440104144c02c0080140e40c100c900d490301c940381ca8182d44035807481400507150016508018007003254481d0002c40100d0049840325081d54443c41241d02d41841d11240d90046580503104102c45035200044c41e507510785481c00d00e180d003000c1403040015030101070310355410306840303c0500c1404540300030f440448074000d840074814000c084608020214200310305951444180410851090007030007290500c070b0748840d610a0b00d0150b43c034115003c01000d081c1d01c0901e0382007040183c0192020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 116495656 1250 116494406 116494447
    0x32d0f010504021009050f121504030e040e010911090711011a120c01020a14030d02120a060e0f011a07060203040b0f100819020303090604080c0915060d11 68
    0x84000240380d00b000d004100006100049800401c02c42e000c0c180016201e0405980340c151060300c031601c43d085a1031100d03042803641c604201d0281030002c100001d145c0d11100c0b40b550b20106840030003070300f52401d283c00d090ba8540e48000c3e102c241401c05241441c1022103010fa8032007180d103031000d6000d210340e1410303080d581e1b401c0c2e5802580c80803001520051038640e2a10703000c21000d5005040860740000041e440309070403c0c0280c2110400f00d008002541c05208883c0c1340000304400315a1090520702d4401000025a544c074a054a040c601140e0b0f0661310290b14042d49180e03003801035a030b03e005040d83e40ca010303064103401821000d012580001d1030a001460055105030401110b03450481c0180c848030f6001001d480d030f6a48a081e0411452901280c01e40e040d5036900c60840883e50740d4008245544108840380d80c10400001e00060001382c0400c0c00307041241c003100d544450b40c99094032070cc9624404c0320420307480781c410000303081541800c0e400101602d040098850801480d82080d00d13001001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 116496906 1250 116495656 116495683
    0x607050304021309050a2d060608010605010f020a1509140c130513060e030f04060908061005060301140415090626060103021c080a050a020d080105032d 67
    0x100a000031840c2c5038440c125112207541c004c11103540c0340d4607015514160440d01400004009a0035204d0f04801c1112080d41c3c81100034004070b5224902c3c1c0381c4018aa00d10440c3c0c001d502e002008549076114001086102c841c3d40d000b40341201e15a1100403200710703410030301c01c9610b644040b050b00003810041c0c500d04200b05070001c2c05505900f80c081c0a85d088a59050f100c15502d400100406d490407108a0104149c001c0d1002551141d1703400b440745184240040c2030101d460100d000100c080c1d1110b8030750291b07081d06c419540f5648604440c0c141d40d51180c055158044014001803056001c41e030b900c3c030f00102c8020300c0810080041e0200030f21800031600a90041921001c0501440344984000b0110190458000e08442000c850303060301e80a060000900c69100d0b41c1050801c44a03245240d4049500030344802c1d6600ca04072806040c1d540f0046403034015004800d4004070f09130044105a048610145c050510080f00d12204a4248449800c00c170300d60080f40c128100198041007024408043e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 116498156 1250 116496906 116496917
    0x1050d0b03070f03151118030109050604060504020114070317151503060f0d050c0105090316080c09010501050307120e1207050703030e0d0c05011808190c080708030f0f0c0607 77
    0x1103040055007405c0d81d80310754113580d041c202555095042c0f10121207482c42e00040020141851000090241100700c8019010b4801c0e8400d0209004040d81b003180903074401d803510039141003014241e26440c010003001802003800904440651400b40c400c4e0f40e0f0188074031400c0002041c1602c0001d180c4030715484c09210540011040220728200340b0b82c4032071019402c0340c07034903040f0712690f4603241d0340c011761200c0300e040240114040000792410042801c4000c07054408890040c1c944075100e5941c1c881110862240c420310300005415400780c01204d00504d850365504509c0740e10310040402905c0001e81e0042a445405151840d005c5041c000c0d06400384284058040c180c82c50500920034415002c04070b2007032035807001110003c0c0c8400603640c115282802d10505649402e50050f101d01c000b40d01185850103041260300116a0000c15411101c0c07040990480c000d444d04802d030f5851405c4e0041c852664004c1100714140c40f918009447c1d812501000303d827900c01c80101c52400d00406640c1e0602280 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 116499406 1250 116498156 116498159
    0x18040f050106080c0303040b090103090f142a210d170106030e10050c0d020304060c080c2d040b0f0309010c1d0f12011805010e0a020f01050d0b03070f 66
    0x30300568000300740d43c40040207081e0388100065101d105070f100f441c8051500045036422a40260003542c541c5400c900e00700049506410602d540210300c104841540c050a08504d0109022803103005447c0c49030501502169010401c3c02050040e140030b492508451481501d05040e081154819048540c1e45602d00c4803032100e010090140103030805001e1604044207100d0048002580388201400c40c0070206643e150b20301e06003241d2041c01c440c000b0081c000020081401115008010201051ba81d440007950b200b01e9443c3c811b008501044107070041e000c0302c4020300d91200c0382c20240d200d400c5108500c4d082e03403200d07441c0440e40310040300109048007104008814200b071040b4910039030315080507001001d1202c45190f08607101c0201501c506114030140445881c0d240b01014040e01c150003c0010f01c101c2c0f07501c2d0310520600c400440303080d800e185000c2285400460301c151125800f07003030700088412003401990160040550521320030340d0b0740f080340000c3c1e40800100000700b01001d080c0c0c2d01903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 116500656 1250 116499406 116499413
    0xb040321020c0105010e042111070308070b071e030f021207030507020607020a080d0507030e0105010f141801090207030216030804230d020f030c090f010819030e06070218040f 77
    0x54905074840c1b0040000e95082001045000300e0880501e40d420f0440f40f00710083c2c0303070161400e140f541407203207662040c50408001c1200040003800d0080c080c4404041c1651000301c1111081001c0b00d21200c0d11450680900070180650401c60728030000c0d03540541046885c400c800d03840c600880751030b0700103034903a018041c9a54062102c6508000d580c0b0207000141c80710303290207440e480358001151000396120001540b0f00c3c0b0a5000b80c1300d03006084c1c000e00080d65512115074611405000392200c40700c55044143e543c0c504601c9040c24801000c4000055038a0911001c0094026071001d80940c010000b075001d02100342c1084102443c03189200b281c0390381c01d18107840441e554845030b43c4102c00840c02200d6540d070f1031607076040c1140e604458810928102c40c000c00e0130070001861191300b114001b4207210f503004444204a05a5025004a81004a08162030440040c01c503d028000c17440401a026850512070300411041d0b00140901c460841ca2080e0f4803209a030444095a01c411038a98103001c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 116501906 1250 116500656 116500661
    0xe3c0a02011115010311010e030d02010b01020d020c0d08161e03030c03090b040f0201020f01021305150702060d05091c0201020d05060a050f01030504050c031c08090a0305070b040321020c01 83
    0x403030714001020690709451040443c0388040c04042d0070000e011030210007036031107061150410b60028055818800c0081c0c0041e000e80f86030300c0000d001d0b02402ca00b08601e1403001410203941540200401c42c102a5603c84000c0355003c12000e800300140006070740c010500004035400c0c0032100c100381c040c1800c0c1b6400d0041c02c841c4258040308c205070a1181a1000c50444281281c100340c122404496a804a1005070f01e4003245001c031101650002c0341d5081d1401c14260b0700780c1110020364813140c01d0400d90301c10b11454402c50a00035880001401051244c0c44168046540494035104036045480c0d20000e01001803020006000103030740000310b0f0040040c80340200e64002c44142e8194082d05d0030000050152260b210042e8101503803100010140300c010042d88100c13047c05004d034ac83d41c14408440c50900c01c545107581000c101c00401044400b035001814284198040e687c19041c54a10b9031203050744000500300350100468020250002201c18005c0c20004000310700060340c0b0400e0740845401e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 116503156 1250 116501906 116501927
    0x21501030210050a0c150b120a0503031b0408060103080901030b09090334030503010f060509100e0409241406030303072f070f08010e3c0a0201 63
    0x44405100104010303110700c00542641c0795142082ca44a5000c0d10044645500102c4050466000018206600d101d01e600c07000805078255064601c0e101140d11555403682404001000c6038801c20018914001800900020315207502030315140c240e90f40b00d110301d440801c0c0c01c10785030710f41c000030071900710b603050303c96400d0b220801e407030351060b6103004001c0303075240e02484030416200302ca041540040000300300184520307a039421020143c28441410010100d4209006206400b041c0c604042a0140034205940b00020000d0030380e0004d8143c0c3c2422607192009042c0c95070070940343c4600c030340016010342c84c0022204042c100401005945603860080e00d505030f24584202000b2000d01542d528080110380e44243c042c241442484140203514117a43c0c40c0350407080140e4500f0b0f1001c10b900c10003040050480e5450111540e049032285c000608076010742800600643c4044c946071100302c2c4000c1203454003a850003006894405144403400100303204001103410740c0003c100241150307003003400a807 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 116504406 1250 116503156 116503183
    0x30219080414190b030c04050612010812030f010501180312020a1205090105040308070f020607150f1109040f0609110c10110d0209151b0106060f02031b0a14060702 72
    0x240110102040030148200c1e00900390810340c0000003031b4a034414141110b0040a020b050140e40e0f860300e0039200ca00c0c030800e00070040d940c0500b002d079801d032800742030540e0301030040e004048549900e44801540c194190700480b2503456180c50001020034a03008175001c83c0359050300034060900340d40c6012101241911132000a000051001036801d9034400245d44c1541d030712000c0f0aa440d5a11304003003c1c80012014000d5100304005130380700c1044109025803005044c0c0103403d0285020000d4400e041c0c8101001e1500c4400090150401501d0103030044e0f2003e20142100040c0c2d951151703e01010780e21444480d40d01c5500000301c01c6601c0c4410000000c94034003143c01001030407050250b00c0314030b20401140814040c0c000c1a031100c6580d5810f03049032404c00002d011a92503d80341412121140e5600c0394002a500e001c00004030030780100c82d000702c040e1084e0f02031032030701039034585d8a440302c0c5050030b41410381e00c141d03201027001813940321030b29036842084001005240b92900009250501d54003181 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 116505656 1250 116504406 116504419
    0x100501170d03021903050405150c040e01050a0308030a1a030607050a080c030105150a020f0610030501050a0b090601120b0306010b0403050d0905010c0303020304030201200405042301030b04030219080414 89
    0x4110501d013180c07052201182807402060760745503814403074548901c103070240800160110501080e11000310080086440c40101e00d40c45a90340e030104078600f0911b00c0003501455007040014241c9134680e010300458245c40c038140026408502c0441e1510700100ca40f480031460005094034225000350305140e000c106054400d2071036042c480410144c505810121441d548007080d10704c0258000d00c400d810900fa843c007240d54606c0c0c4034a088500c0e59881c403055810f94a080301040700c44030980144c030004400604100b0341d40e01c5110046404506c101c4510789201d548084281e07085c0c4d41441010b0080410122603a200e50540c101281800c0e034008125040c04451601005180d8000402c00706040d050304005849644504040c0e0241400c079402c8005e14850324400310781d605919028000f910826141001219022144030b000790f1000020754103030186840042001640d82003006034468424415a58540307600d003410702c80203064810884286502140511441b0f81c10034108a10180481b1513 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 116506906 1250 116505656 116505667
    0x60d0c0b04300b04020105040806070305220309140f060403060209010816020c060304080f0c010c091211040c02070503060f0a0c0e100e04320f010f090c02100501170d0302 75
    0x100b10400c000644000c081110328800201568082c0c001d0350300400352102582c00602e00307203400a0040c042258a500210300c81441e03c2c140052400c203406802da850703103903c0d0300103092052242c05400c0110340664400c1000100d10401c0c0c0300c0c000a8001035205060140c0caaa2420001520503c0700400300c5500950350055405100d0340003c105a0340700060300c1c4959603480e40d08002d02725115080c40c4210308140000c031070001040552240c40000003580c0c825091980390340c0680c0001501c8200540241015a0300966515082d484600405243e0045a0300c00f0b50782e201103402c0800c121483d03c0004425810480140000c1c040c0e1000e611451030035045d14120741c0c0c00902075401003030a680810203001c02c0e00c096a12030780e003c4140340504940352a48070040314850426500c100e48040403481c84c40000c2814000b01d654481d05903000c0c5403500ba01c00c0e0800e81071b0402031a541080c60210b218820030b0892990032031094502038814950380c461080848480030703241112104880c070402d4810041c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 116508156 1250 116506906 116506979
    0x909021206190507020a0c03030c0b3601060302040606081005040606050706091419061107050a020904050312010e0105040c0e090604110705030c0106062006060108060d0c0b04 77
    0x10707581044410460300040d0380e00d6101381240b0740b50041d8001800a10b50f800c010007456005028618007520508071400165551500c081e040b0181c0c50700403152981519a00c50b07104d03111040f000c080307407880c00001401e0b82e803500007800f80e843c1944088080b428035800e0006800a00000301c1c0036050039202803008510308000102503129071640984141c0d038401c403074410002194181b01f0044001400c0300c0c0800b5a03640f4482040740084411079840b441c0004420844101d00151041d142e04240a045245525000e1128000d03008008135140d010801508500c0c0b4920002e1a001e0540004a0490396051074140800c03201d80b41c00440074880d650514080c0b69407490389240c0e1000c001d503008242290200441c90b442d0103451b200801c140000706551075240360540c4040c0486590f59610b800c28041c1031042072866079030030102041600300b400001c0141d401200348a1b00081d01a18001407a0096225088590002c0c1c10840d4604e000180030407009826450b032041400044c00e0444510b2003424 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 116509406 1250 116508156 116508181
    0x20307080a0e030307050d03051816061404080303040501090209060402072f0618040b090106020d0305060d080c0a05100e03070f0201050f040603050415050103200303040506040909021206 82
    0x480e100e0400081c1c5020801c40d481c04d0040d84c0c1c6159002d001c886407030b405404040c1c040d1504881c503504201c4031100420700c4080010b46d500d0b4400400408200407403e041c0110799640b034441a2500c02e42040000094283c02040210303c0b45001d41c0000807804031074410004c450f0b01c05864184202d0060241c10301003904070080c00c80c2120003c0f1416000c94008208503185640300300d40c16800800400c0655000200c1d0750005002181154100040d079050410401418420300403400103910204040300d07040e000354085508810010101c15015460341d80f0550607502545a4401035044103088104001007001a0041c00c20300071002d00140b40526001a500d0017500700141503600c0711500380c815a4014822078114130311040d0075995031038441c000600a4201030300c0440e04c104001c40b9841c8045294458035040c0d961100302d404e0b010250003104510104d40c10103266050200f0040040c40f03980d0f16000b0700081003400300128040f80c8a00410208207041c0c1801261030f04040108a880d20601 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 116510656 1250 116509406 116509417
    0x30a1e0c091e090203010b03010614040606030c0210090c1205030c060703110a0c0c0f030b040c15080604051503061503070b04030c0b0a050d060608010527060609060d020d060303090602030708 84
    0xd0400141803c0500000c2c0c050590070250760303019403801c0c2001c00c100200f84025450100705580a100e1260368010880880b50b2003174a550050b00080010000c8400c40c0e0001c84945000b2040d0148040d1a40c0e2804c000d05103041c803c584d035910004174201100400e02800ea4009800e09042066001601420443d449483d210500308081665501c040201c08240c98001d00f1702c40d1440111940c90340b03080101e1803000d40d002c0d00d01141c0c820001400700305044040c0c01404881e0780d0240f581d15414140005090090040510400100c6204040d62800c000780c5209140c0380d40c146000548040034507040484075088038034800380800040c40804c24501d04501110500400165180e44208045a190258030418515142800c800040482d0f1098441f416100112114009000440100c41c003040403500001c80000d80c040000f015880c00c00003615130801c003c0c05051514911a6180c0101c0c0c2c00a04a40544c0e5550300040c800d065000074103801401041c0020351411409465000060060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 116511906 1250 116510656 116510711
    0x50706021309020c06092b03020d0204030309240c08070201020a060903020105070e19030809190b040f051c120509030a050715080907140a0513060e0c0703050f0306030a1e0c09 77
    0x41036083c856a100360304441480fa0b414ac001c549480c0c592400800310b030340341d00c5944403416040000024000f1440c44060088846403503007070544269550b140d031240c00c0080d007a8158040d0729031070f1000c07402038085c1e000a113129a00000e100e240028014003442c6c0412001030203010070950400403070151740c01c100260303900143da20380c070707185c2243c001030000300b000c3d03c0085245407007040061201364007805041a40c880a00c0c40c0c80c0540c5402c207001c0c0542d00c2118520310a609250f420000c601c2c420f081c1c062121a6140031850241440086480c2c40820581214283d1007203000b005109003112040b0089022072400303400f903040841556136500f2380317405841d40c0c00c12001030344041503482030088401001d018203120030a019403100c7c2002004a8400c0141040c091000503c00e21001c00403206129450b880d10f07030400c016800309407a180c1000301016014481c3c0c10a040102e108506032520baa0920000302c0c0ca045851700c0d107020f103050f41c1d03442524694117041c1d90b047d0034581d178101032001001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 116513156 1250 116511906 116511973
    0x120203180a080d050c03041101030c0e04020c1b0906090417091807091a07031b0b01032603070f0e19140103110901090303050706021309020c0609 64
    0x4031244403040c2240403045024562103031020300d6040200e65005000b62221107502003120f0795811105a05a11040f20010314030781c010803114015601070f6000383c0c44c01d0070606d4244404a10440450100ea103c8075030003402c1d07800550882080b400c1c10301c2554948909942d0b200040c1406030118000d1403014100400d03040310101e650551461200640d4105003000304520105401d42c0c03481d40902c24141c0c1e03000001108058042080e600c4170304030306d4020340d80d5040d1520f056810b450840d04440e241d0013004844000105020109400d160614040d6006884001510302e281391529044600c03102d2009640d0030500801c03404540090107a120203407036040c0481e601c4000d40004181030040c86160b0040d00115202140c9480c849502d140d80e02001e1305d0030042c44180f255004228010514024002241c0e40c00510000e40302e1006000310311300c0780601500380030780380218405107079150b04004e10341603022400320382c0c038441049490341054040000d080c0c01c040b034800d0120500f20f030008160300d050 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 116514406 1250 116513156 116513161
    0x417151302130933051005030d172701020d0e0d0314010608040f02040504030f260106111009050c090f09100b0d1b0f080304140d080c0115050a06050a120203 69
    0x141d090101c000800f180801c100519040e00031451851b1280900d601030f200344640c401d6210b0054401d50b0841c5081300441d6040c3d0340344101c5001c1880282144190145555006603a81c00c090015244a0741c0c2d0a5020902030002900d0500e01400350580000300360070604044d0310545000da41a05442e068a482240c9a07246e0030f0841c00380004141c001e40151800b020003081c1580b101c5e42d0806043c031507032100350141210300c0c24a03001e0302402180303104c3e030f1511004000780c0740541c001d0344100a04905640401080007801c0d001c8034144c24080c2c666801100d00703103005140040c400c5501c1000d60701c00c0891410192600c075550903555003074141c465601c0300703070b11015541e00005c034079050341c07090040303000d02040c1c0d040d0b0b40f4000c42c510511420030100034012415007004025207040e2082d001e00d419555450404010000c00081c41c213458000c810422085040c07020f01541c101c4c0c0050492001c2001c2c0341038140907682d03400d5440482000b105010511b220b0768083d016103a2500000710240e101e4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 116515656 1250 116514406 116514473
    0x403030509012109050c121b0a0e090705032406040b150703030225120c0201050d0c1d0108010807060302030903090d030f1701060504171513021309 65
    0xd0040480300c041c440340340d04180240c001c0d030350042c1310560f2240081e150413030f09400c140010050050180c3d00c1c25000030801101610400d090f0301008203000b0b0000780041c0d582d03400c00c1c09560007945c203061300e0b8000710003e10082c10300300180481502c03501403092091240a0408403202c40140400b80b06503181c481d60070307941d0b40d0102d001409030102510710303a80316000c1c81d0241c0203600c807441c005000040f0341c200c012025055096600100d802c000303603450242c030400c0201c4494280c240701303c0c1481414010054441110b22818400c00100c4d00c0d02800503102e0030700700d0302282d0400940c0381000074950040c820040040703a00c40860b510f600b800f50300c030f80702c80c0042c0d0300314001c03020440c0d002802140e55070141503101c403406000c002d007501e41c40c070f221b60030702118400142d0034069980425000c0204115003c40380c2c0351820401948004d0f40c4818400004410800b0019038a070180701004680d01425460128020941102214010001100341e550307082404101220500e081c0190035050040f903 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 116516906 1250 116515656 116515667
    0x17190c0207091a091003050303070c080f03011211030105010b0405130617031e07020a14010e10120e0304080705010e0102100c0323071d03010e070e011403060c040303050901 76
    0x41d0401c1d10041c043d8000c2c240c100868010b00070000d070b01c110400300204030349600103841003003030301e412402451440e07442035030a503994017000404440b460010403401c070743e80c801031015602914803540400321803201820145450402d0811a9101c0e914142c01006641301e0003080710122030094503070410204100b04580020000b40c3d201c60a0038450640c2000c20032000b100503d000c0038070614034031602c06e20386610340041c010480020740050b1070308010b0111009c50440c038a80b00005150400c0d000030b83e80301203407040d034000d41003002060390400b1390704145201c7e00520a020504000545c2030600d006101031b07541c0950300c00c4078140000c0c80d00224480e4428081c1c680c00c0d5507071a0301442000c602040003001807c02d000c0304088e51159950303070000c02240c4001da60180209036142c1031030141e00361803030440240c1081103e9066603503045100c1e0703e080503c509401811240c400407003e40c90000024980c8100c8402c0c50302c80e0f0404410020004400403d55066a81504c0c00c2c584880740320006031398 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 116518156 1250 116516906 116516909
    0x20a08010302121f1b0c030207061b140a120e0f09180f0307120503010b0703030515040c0314090d0c03080403031401080115060f0c1b030b09060717190c0207 69
    0x12000b07011180c04814550340d003101e01c405010150541105e007041c0f40c21580e0792050b403030090060b00261410441203200309400c03903c050210181982c01d403800d030307038242e0082143d40b2424260f0f0440140300c02800950b0a10810780c02c20350410341d50762189c481c00149901c030049030b407521500c140d60129220f0015040d01d4031090b03030841d003203410640d0840d608540e2904103e60449450100c0782c2c504040078170034030940c5e049840c030318031703842c01d001301690250301900e03008021000340c1803c0403070120b0b55510b43c001c408100d440c64a0000c0c1040030110344841c1c603000200507040b65445080c0031440c040e8403100310203029406107481280b80e256842e0485c098965000c2685c01c150301c0c5000420302c1d500640c80711903584059480071307610365610b507800c0e0b9004464544101c08901c40e00e11445c00303d0110108500c595450040e451240c5403203039a4284904400c3e60701c81c0c0c0a62004003000501e40d0060705048600003c3c20b80f8080a1914204080c8986a4607141011a1b0744032102c2d081080d00030000d100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 116519406 1250 116518156 116518183
    0x9031e0c070e0103050c041104050d02010e03010c050909101a0706020d1a011106190209030a020d0807020a0e0f0c0903160603021801051c050c0403060f05070f03020a0801030212 78
    0x8128950300c40420303901c100c2c00c0c001500c0500960b116540179103082d22440c12602050030056003064500402c0092150441d14140c5c14442a00b01038500b980c0e00703104451360711010b03840c2c40741c03101914030a210340039074010002001885891801d00854802074601e60b0300c644d0740f006880c1e503143c00346000b4029019003c003c100850400c4003114805695220ba40b0815200b0790f00d0107150303011009200d070b88290984000c00103210304031000070644030980040860401c0078084584403030b0b50f035021952482c04a0403d40d900300001c25403204600d0710844080041030001c0b90342140c2d0403c103414034100c1c1e10141c124586518005210301c900c2c1c4041c480c01e0f2622000002c44006543d4070307103010780a036020000141c5800402c0401003001d44c010401d1b540600d00729080007800ba24007001001c01028090100101c0148c18080080061070394000c4a00741480300c040131030320f402c00c1500604099119044102814014440400c2280c0c0c8500c400e81101d8049a01405200340521958101700482c031070748 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 116520656 1250 116519406 116519413
    0xa0b2106040201030b0402070b1803040f080f1603050d03021303020402070b041202070f090f06080609010c020615091506040504090506010f0602030405030d030c0e04021b0c04020309031e0c 83
    0x88410128846206034001c1c0c8040c4400c6080100b084100c1c803e0b50001006248c100d004a0b180925400f81e00d10a268504201ca140640b1010100e0080701c1c1d42d0f100d801142d011000d00b078200c8a05001c1640408003031080302c0581030a681d220390300c40351a032081504147d4040b80446880a656483d00015074006e81304541c0c5140700d04040d150710108513410358100c441c0b068a0301d59584006844011581c2611501c07541605280c00f24014024110850303134910b0704e5203008075a4080a0140c02d014107510300c000200e500c5071a001034142000284030310740c008101000210a506c0e0825007036400b850350540704408802c0f0030006245130040313800c0f81341c000f8588251101009000101203060307900d070805907160b41e81c1d80d80c0201c2e80ca10a6001d80e41d0542c1041000103106030085d0089954441113081c540c0481030010046400c1f60000100d9814203000d0b404688200b403800d1103040321100c0103640952031860200c2c015540d903c03c0056502c40540001da903640c0110f203075403d031064098510190f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 116521906 1250 116520656 116520709
    0x70f0b090109050907081b03070c0b06040b1002030c160f03081c050a06080601050307030807021c02060a0504030b100f1a0f0c060f010b070f0308070e030d0f0306090605090a0b 77
    0x7452821b048544601180b90382484242111641081d20300c50b071660f50f0b510074048484d070303141c010f1030341c024000726003103511f8000030941551044458010f100c09640190380303806c03880716568a00034401d014091038030444c1d10148640c9070b0641d20038080d02d400c03442e90742e41e9000303a84441d581c0b50700104020001e82d1503d070502c80300d503500d0f03000700c006c40b070450040382c9499803541c00b0582c0350340f094800203158040c1005040010b0425540c40201d240d1000002c060aa406030080b62855216402c254002680000d051040045049405070000c804520006100b03007010804030b8040c0e0f981c05000c611440040545840c1304454084a400c40d420300d11047c0c642d80403101440c2e92b544280c800c081c4c6503003c503002181c0264010192031820340c1100d102c1103c0302903920305076410640940810100611944c9252040d24100040c5800c007020355a81162001c02290042c110743d02500452000d40c20841c04105076a42d080481e50402c0e6480d01c00280c0311048000607a0a0700303c1c11000b09018000134a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 116523156 1250 116521906 116521921
    0x30f010c051803060f0a090203031303060b01030501060e0d0813081002070302011103040f080a03020c030a0f0201060501110a0602031f0e07020615130c02031308010501080d02070f0b0901090509 85
    0x207407403809840e11182d062240100200f689030f84046884141004103200010003541d201d8001d0030200380003400f0303246060700030540114604d060f50030a440a0741c40b6042802076503030602c40d940c0107100750700d41881128440c00009450116113003000d080b0b40c03808a00e83c0155140024500000d214081c12200d070101c02070324100107034128a1056001d9464032000c2c0340b42c604550116481641d01400030f01a005013999460015000641e0507001c1603424800c48405410400040c5800080d0361103200080340841c40013800d50740107810580c100a4000c1a0070100000000c0480c801303640088090303103035502e0030305428011801d038221104100d01480001403800d00308115500620065081e11210b0b5614482905841c01400720b00b034112113200100c80740c61805074000c00360b580c01481580d107080c070a10700459280d4000c1d08180385c01c1e5921001000200e10801c1842061900c038005403403180d1402c03d0b074061092843c0720300310481d0b40c00a0182180d030f110f42d41c0c44016040080010001d07061010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 116524406 1250 116523156 116523167
    0x11b020604140f0a1502040510080405010b0609010f05070f02030304030f06050f0402010f0305040f02040e0718110a1b0501021209011503050c0103090201050d05040308070f03020301120b06030f010c 87
    0x1d800351460511804414060b00010580509682002c401090003441555510460b00c030404801c0700140d0382800003060700c0da1043c040c8484000385641e101d049003418104a421194103418031807158004000651303c4da6084412482c100c42103080241d02c03400702d4280302401080400300294503004c002030100400c03200c1e00c0c4052400b03005e400c1c108026a039410340007076280c800f0f8174040d0105440c01d50340c01e4a14444d40017181d20505c55014100441f03000e40c003050945440c080e46a0664000d05014001c140b52012013060031641d99000340020452003036414020710900c40c00c8800c01c0f20700b40f14001031568103640e03032048030340c440b0086540c0d052641300d050401d1401d45582c41d165082c1040318203200383d01441c08064a401c0000b0f0030728500d8000054004086202c02241030050038420340160301041e201d03041c8618001d480702d200c149403607000140085c0e864901401030610500c010b0002948951265400641c810820030180e112007001901d000c1c015600c0725003c0d801c0008218500b503011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 116525656 1250 116524406 116524411
    0xa051305181609110c060108100f02030c07020d02061209031801020c0a060807020f0f010507020c121f0b1002011b210b0a0b07080a1b051e011b0206 65
    0x2801c204044001141040c0e03281c655010801c40080d2050000303020078129544100716102c1e4000720301d17140548140401342404d000b41d200c0c0507960403401440c0d400c1c0c0c00070300030340c3c001c20600324045140d0b280c0700483d45414020b20f04d0190081c0c943c404c13040210b44410307085402850a9110000752803511404035030740c990041c0500301d50581e020320103100d65400042c0d002d5900c0c82c010031301d0b140a400d10030201c4d80540018403410451040c0d03205070081c1281407007400c454407030020021407070b4500307110064a408094611240904540b4000d00c03004100401c0c001c00035038682105552a07444002548041e020508995501100c2074110a072450b80560080565060b000c9596510300e1806d081030342c503084407100050131041c001009200340031155001d00d141400003400d990955482d4818500ca0f40c1046400302c0d80403c0008080c1c4209400500e824065200d9890b100552190380c0e40d20f644442c3d0640040050000000c0301d50351421081d04030321410140180004d07072000d03400030000e640760f406 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 116526906 1250 116525656 116525671
    0x120305070f060501091a0616051213080c0924060f040801050403030608010e2107080310180b180714161b0f0533030a0e07140f0a051305 60
    0x21b100c0f080c088138a10041120000b02c0080a0f2801c04103503000b06000982e840c3c5e4115014010041e40b003031740c0b0368100301a0800c5241c0410994400342003003101072400600008051043c03c2800c00c1000080082c03070206102800088403c81c104070000124049010f03684440c040d0003000726010506560541c0300d148140d0081d40c0521102e65076200701070894004401d0000c05400858941950404031409810003400d0766034410b241174040d031250096500b041d56144902c1120078000c00100e1640300e01008030919070001005002c1100002550188046202c405080700702400682d03c50300a09240c900406000380031580e580c0a003141d1a1380c101e0703841007203d000030600080300c00c910301030840d14141c545c01074420040070305100411480003501401010303440203440e184041c04440d00b600009001d81c00124585905143e41e11000380c4540121703880d5a94081d550811494072181c2030724500344c1f0103845034814030040c40089140b1003403d401082d0801c2106400001460040c1d10141c800d014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 116528156 1250 116526906 116526911
    0x2030c101b140f07030c0501020d0212010b03010602031206010e030714030717030313051903020d080a05090607120f0e0601030b06060703051804091b09110a0801120305070f06050109 80
    0x1103a0503204402d003000c0814036074a09125800703118400c41d0090800f18041d0a2003a82d403942035480600307990080c45403404241e0041403030802440d0010400d809844150fa40500310760501300c00030764030b001c1c146103010648052404560340341d001d41c10f40c249544014040e42d0030251500405a110241139821900a21502800003516800c1d46030340250049100055880c42c0c0b52250002031b140c50140065840e4081c8003560810007410b02d400b55003207403094024005002e80c03108040c1107080024616a0308c1404d14007048070707101010a0a9510565900b01014540d4082e44e040d40248641c1c08800800e40ca04201000e64100c00114a4100d0340302e0b4a0340c00d07869494509000300380c003c2110080c007248041c0320b622545034910244202c24080a0b200152240b5151992404001d00340303200f134440d45515405100c40034a81c004c0da1709031110920103d1031b02d00e0080005110b2001403080c0800410098103400c2018801d1044070752190304206c165002c1c03d82410110018103080c4903800b162031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 116529406 1250 116528156 116528201
    0xa03020c0409030509091512060103030e0d08030403180503100b1003140a0f1b03090201030b03010b0114030c040b0c031902071a090d02040e0a0204050f010b041502030c10 75
    0x1d4140115441c06900d40d650390304060303140042c8480d01402600100341002c860040b41c081d40c43c0d110948401c2031042c07000741125499414060444222200400e00940c50798180001090b010001c4a0b00302d54103281c426040d001700384916008803225044030b43c0c14000e06900003510034030342c2c010341240601150280311f40c036200c80c4150115000d404401c22110a007400080b0070302c129601400c0c865503061400304030103192005c20752210325a1080b0401084e5140518001c0d03590520402c05041001d9000700100903244001810300d0343c004115010704880003000078480002d14040e40c009110001d01140c40e918a03070f00031a240c1d04001401c1d012386401e20544000140b00003860b008803a207169040000401300140b4940503800200e0752030b0010440e010440c0182c072030307100d00221400030401414103090f0b944104015104058072141d80c411407800140001c006090480e42101c650455111442c2c01c02203040e420b60040f800105c55500540c401c07401201d0198200c1c00035804498102d04111 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 116530656 1250 116529406 116529409
    0x30204061d030d12020904021c14040c050409060b04020301060903050f070e070503041406010f061d060301090b0a030f08070c0e131205040504020d090203070501050408060606030618090a03020c 85
    0x30681001c0c040d616600c070b5410442014080c482845440801807805442d200d008004034041c5e03030240300850300050745070241070b060380b0303240c4241481c51a0070244011141419103540c0008015070041030310a590354018982004030f190f0000388400b40c082d00640d1290b9646502400c00f21103407100f564075020b41c0d61025840d000104000059a514107017041c482c1c0c82d0b0800480b1180c100804c2102c0030003100f15205585442008018001c16429103100006420800010462038909407154000c5240c800d0842c01070350303000143d0341924048140010024464000900c1da50380d03581c0040d0032986081a85c4050020170001030012074000c0e1480300c40f41d81d66180003101103900325404070f4541558188000015900185a0f0480c0b102d45071040c140b549880c00101203a000c2401d0300b28080c2d407000030904505090040380002d100900b801130516107440145611840d00800c01d030b1142c0b40010000b0300c0c070307640d1101c00c2e032004881141021031842e014810039a01c4500c1c81c001d0b009881247d54000c2103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 116531906 1250 116530656 116530697
    0xa060501110d0804110d111302040e010b130308030a050f0f060306131b060203030105030d08040201120e0a0c060f02010501050906010c03121107080d0b03060f040807050c1003020406 80
    0xa002402d0b0320140081c11200c0d8200a4030498841c80070003042c00a954401402e4264140a1030809000c20070881c20451b10246081908241134010700c0108030b00b0300c5102c5154111242109156507030102c016880381c599135190070052108101005221800b021980450311800508400138032680b52061030001e440c80495880f54140d00c40400260400b07109880c01c44c00e21b100c0d01c0c4d21400040031310410810301d44550132500050f400400104460b240810000c1c044c03c40a04103c680e50519800080c0140e0030240849100c0b134803880d10125a5500700184140c3c00d41008100c4180381d21244001c08039650b00300b0100056081400100e51480c01d00d0005010703000585078410b4986003540c0640d84450a841d0002203555114140741c241041d000051085034400c4080f19515125640c194007105c0800d400d89000303030310080c02c03c00000f070b0607040241c12942080b0156181d449610342a464030410180340c03504500c1403450741c100c060b00f50f0094411750305140c481e100c2c00c032009040c1c0c1c2c04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 116533156 1250 116531906 116531927
    0x50105040e07030903110303070e03100501030b010608090319080103060e010e0d0f020a06060602030705060c030c03130510060b031005030a081213081207110f070501030c090314060a060501 83
    0x88020300d00010900850003a030003041340900c00c1c200340f07000c04c001038089803c50300100d5070f40008ca804105010246d1400303000041c50035114820410095045480b042001c42e014000c08050003808800b02d14800020026910040d00429103441030520500005000801c203100445a080c10a02c50b00607419040c050501d40c146150b000b401111b1541d8012070366018a10004815030051030042c0003c10018010f0002404984d00203650710102d03460103500d003800c000c204010000d0207109014a11000108807034000300c0254112000d46100d08206080000c2001c10440c000d2405100140018200c4051845070903110410602e03130755200705064581042c010300404c050801c2080a03400707900d0010307236500701c0035900d80385840d11591340c2d1700c181c140e20101c0316143e0302c507840e010410701c6030f4409043d0b4200c41010028003c1900000d8103d41e8520306401158180b5840e50103075450644500302c844019904000c014129440e66000c5513103904069490342e2009081600c04101c07075025040011 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 116534406 1250 116533156 116533169
    0x30c020c030a03050d0209040e0604120207080a0210120212010f0b0f0d1d0f0a050c010306051309080c102007020607060f060509040809030c0f210309060c0303070905010504 76
    0x2604070040c3e40840c0c41e0340c00849225041542400310f02040d80b2036100f0402c440346d03810b0003002d0b030b820541041400c20709000060000c56014074028000200086044061268160303102007000340c5040090359004c100d41045140c042c40490f101104440d0010f44034100c80704070140c03400103511001c08503680c1c854015810b54031a400c02c0707d0310500c43c0036401510301c0d00c2040000c0c640c00d00d00354045401c1c44e44416402085521521324103060110901c54410000c40034201005414941070209524068040040340c28955940090040c0140030080b01c0301c4406603029a074040e0703445801c000040c003030710242a80c2c51007100342a031070501e9072004807215907400406490421019513543e0000e0044641d010501c0c3c2c0d1100800540c0d0780761242d200d40101d1194245649401c1614103051500641c00c49591003800300740400081901d9034070701c40340d1900d45c294000c0b00749011402c0d044d1441c0300310f8404a41051380000c0c4070707107a103101001640c000c0c2c3c503954521002d26510380045030b040c00356010704d6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 116535656 1250 116534406 116534413
    0x6070f0906021e070302060a022103040201080f06040609050106050a021002040b03041e080d0b030115030314070201030e0a080c1225031214090c030a0f060b030f0703050706030c020c03 81
    0xe510359085101c03c2d00408a91002c441000b601d0358003064260f040071064801503071103180311341340e08225001d003800f000384035441c1700c0d09518190700024500103014206160004080011511540715504801c015020b03405c000d00c01541e40300780041c03880d480044c04c4001030040c200120603101d424021502180c0c1c9a550182c01c64499884032040c0c400d1110840201002c049501d1000882d0400a40590400090005181a400021f05007940c034034144032950421001001d00c0021303001451030b590b15004011a03501d03070400e440141e0040c040384200c2c0381b40d81b02d4950008200b0079a01b00070008100c501c41076441540104411105034011580c0721520000094841c00489107082c451100541c024075190340308041a04114044900c01c1400d006400d140004010500380200a14401400e05800074041c0041c0f540f43c844400c00700d5400146034a8943c901c0384c8081e9020402d02c1c0c9140d0b084400e403910295285071886e0b4811441c0300b0301c0f02180c2000905200140003140d280c0e007091010307028 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 116536906 1250 116535656 116535673
    0x4050a0b06130f0b0a120302060a0e0114010e0403021510120611071a070c170f040e1806060105030405060a11040f080102130b070c030b0a1d06070f090602 68
    0x240124030100400031034000b41c01001664201001d4010f090720780c2c1c0f48102c0003821640b15010f01003c1d04590700081c10b640c44820807040042e500140441c4e000c40b0006d00021103942e14003400b0301518410600081c80d011040c0089102130043c1c40300c5000e648245c003201c00c03480303c014544c440e03460101e9170015600c220078410003408444440c1c81880a12541c400616a824058125845c0c0c00c03496042d00e00280c0007018200e41c0a003490020740112540c10203641d00d0210f580c500240c0c082403144403001e620086800c520703c07642001507501410003045441c03207910303180c02c82450020441c0e4541b500c51007a03401040301940210101d1b40529044000b4041c1551f40c101c6140103806502544c000c185802c12000034903003c1220008003400b14600056551581007940790307242140d6030080b90b80d02000300041c9000a038508100801c0320351005500c4020303540c041d00d0000130039510080801c020300304c20301240c000e00301240345e61242500b502c030441401d5404008907a0b0100c640500380c05039105100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 116538156 1250 116536906 116536913
    0x9030a2a03081b010609060b130803090303040b0702030a0204180b010b03060906040c0908060901021b010b06042313060312031b140c16050a080c0303030c0304210807030b0301020304050a 82
    0x843c8008880c2460000c1141c66542c1100300444046510010000d003000c81d15400420f0088503c000404074075004500700310b100c10020783c4910851081425002c800a840400c549060082c0c080d07454004004001c068214002e0394017400c2e03041400ca60f1a10900000b2604001130000d49001d2423001d4005522540d46100b0711000b81042d040740310900500142c0040c105008200561107010180000768844441d00306801c02c841e100140d5464603410951070b0592504c584056074201c440420010420004030340b0200702010305c040203a9000f942c0b1508005042609400901c1100d120342c01c5404160748410007101210f0401144c04600e40c1980400d00540e48110011100c0c1c0030031800803440c2032007412909103880840302c03880c00e03406505c1404000300e14003c3c481c00010002d000150600c0384121001a0f2688070082c9110084e15012020070180400c0842001006c881100f260f102c0c501c240b1000381040800302d520703000080c14400d40314020304060080c0d9010310b50180042c0003191340c955 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 116539406 1250 116538156 116538187
    0x60102101404030e12010509031305010306030510020f040909050c0a05040c091403030904090c09060b040305030a081b070303050a0b15040308180d0b091c020309010309060209030a2a0308 82
    0x103246070ba11682542c1021750f41403003803007510b00802c0028019a40c130380e5a14140c3c11144819440103040c14500a81000890030201d850030a08090080c016918418403414040c203005681244103040d280501c00404c01100140c3c0d9058004210b0309159855590b00800c001d8a510040780c1c400550911800c01c20250392844490108030010113880c1003183d40c2000c14100c40c1c120f8410385512105c048c042207034000074030848010340030300c041d0103260070708684130310343c4d030b4496890f4400800610717a0000381807089000081d04d40c42010140715907614401d04006001d480705854201ca61458162070740c01510b03000da01415801c4105060300e043c00c0c5151510311154010021618207409070351034a52250b42c0305004410010302c5860001c07208d08002c4d001038070700080c01d55503040003101d400307006001320340020907111508400d103004a40e104481c9003d074081e0140c44411a018842c8404074400c2000da013001442011100907000c0e8035001504000801c0302d15031002901d0354004002c8569482c0c04070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 116540656 1250 116539406 116539427
    0x6010e2502250e060d17030709050d0605091516030509011104080d02010e060705040302090612070f0608060d03090509070507020315060102010b010206090607050d1d010506010210140403 82
    0x900603225580000070401c120b000440007440300b519010501030181082c801021504004c0c00c1d0f81a03007102441e5658206c03103c2d5654664100140c001c40007464403485903407000080c14028096001801d4203151100280c2001d9404074424043c103d40451007001c0008990b21424100d180b0318200212010154014500503040340703002d540300c91850114078442e80c010802082c000004040e500880d88009003102c9081559481c5600080240000b046e0303c003054400f40ca80407211984036444040c0007589103100501005400c1c040c4081c0002c400701115503080417224551100d00007969500100301c00b448610b80000d0215030362034014091414140300c0590f1010441c01c20501e00161a0002850b080c82d0094100704100940e04001c0c2c1075034203004082010300203000030202d5050144050762600c100a00060030007030080f0b00b1100428094100000c1e40350010743e0200d83c04203a10a940c0a048100c40c401e02600c940b001802c0048030501c030700c40034000400c1e00c488058a842d46d04940e1501f18 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 116541906 1250 116540656 116540731
    0x3060a020c0c0d0305070c060201020715020c0109200a060207080304090b060705190314270f0d0b07110604081c0212070909060812030c0a050403050d020f06010e 71
    0x8041c00411907483d21000110014000d0b21a04c0d100e2000f841c040311150000d8000c401164018803038003000841c09201e241012085020240e140c1030b41e0147c07180105203d0300064421400022140e0403c3d401c240c070000b10342c40c03e907013040007540c6503141a0303551400e51007221220b13130080204110ba0707440d035444a401441b0040015241842d980c40d0789180c091148440300d10b288049112004141d04079040c4400840c5184025080003580d028050340c0d0404400c0000201c0d51401c4149203540d2480c500d40340e41e04001342040d04107442ca00b45034108050480e039242c00300d08001c0e0003a401500000c0c540e0b1203903078810441450480c030018020488480e00c81301c001c00c980c0920202203115000c10009100e00a103544554510340352030080c00540d091584103a045400096180040b04c07454002c072030303211a2a00041e965141c00c150300712444c0c0718691000d860750040c800d6114400307a0128400c50b1500c0c01a045401c6642c0310441821802d400b0340e64000007404903c40c5106003030320803101c48000b161 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 116543156 1250 116541906 116541913
    0x11112040f1a070e010f0c1103010f0920040b0a12080d0207030e0a09020c07060c08090402041d0c090108060d06090b0114270402090c070c03140c04090203060a020c 72
    0x505580b40c4854000500d07590b4000c81c6002e0812050070740c802840181c03543d0901e424444404803400150418054144c0035044501190800042c2d860035000340700c03110200c9a0030402c401541c1000c0382a0100110000f80030600700030320004c1d0303241600130b6040e2a4001890103403001c1c1742c1298a40c2c2c02ea07240c1d0048819082c1440391464500c06c80c405007080070300989549840020140821459420070b4004040d1280305000d010000000011102c3c240c548504005082400e01c1c1080c491600070f42011551043c0001404552c1c11807100208005404000546480c1e4542c11501402c41c00340140650005080900140a40c83d003010401d520f240180070020b800001c980343d00105800903081800795402040c8081040d0801c08810305011440d1850210400c8840c1c1500c4410700000d00040d10400d0f5010214042d0080141201e1a056200c02011041030396803904161041111900d00c1090086041442140c245800340c01101c1d6401809400f190344c5446921000350400c4512580621 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 116544406 1250 116543156 116543183
    0x18050a0909050708151f050d0b0f07230a0905030319080a05090d0309080c0d0815011121121005130506090103030302130504090809042d2a170901111204 67
    0x1180c1d231001340301e00307030041c01021854901407020034074409000c0c004c02d04000010303d40000d60148403c51000038031001940c103903203948c5024100c51282d155048913500d400006a041d0f100d002809040902c1c80d030a44400c601a034a0010b00011940100c6045100d50804940140511700ca640000b000c9031003a246503060a80c0109282d103031043e4074031010003281da9241484a6140300400c0f51800001c0ad2810000310702a0038281d5032a501c90000100000241c0081c1c400b207055a5020342d4840111200c10b184140760400070600d01d01d03031a11445004000149211450740c089010f0580b003150701030701c2c0303455036461070780d00b02c0003944010460010590304840106580c1e41e0740c001c0460450080100507291502c0000300b01c00c035072242500011400b41c8008061017010a084a25032800740f642d00041c0f0310b030341407414820071a00003941500700c2072103500c10b03010b135904040715916800104014114950b00d450181d803c86001c0d202c44200f801003403080c081e1040d03404100a5009100d040001c003040c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 116545656 1250 116544406 116544409
    0x3020d05040609030e030a02012007120510060512060f04030e0409080304020411040303080103080c15010e040302120f04050d02030109080309060403030b1e0118050a0909050708151f05 81
    0x561090724121072503500c07a1000418181e00c80c440179800001140588601c10b00303a40040c000b021116001e000600c6201500203a01c0d03414041d14000b0064208000a5042d0600c1c0840d00c40380910040510076150480108190800c3c401810400d4601c000a00c242d4581c251140741c0b00000503c12400c100b01e110751402503031514042c01d01428030400c031a5880742070900c10001901d4205601403000b8400344020800f2075841445181140d0f045440c803a61030382106c081c68142103940004504121502000190424030f000c0d20910850195003070b80d00303030845485c0380046881040315281144d001480180044d00d040c1c0a00e8008a10040c00007807100d109070386482c03440e0030071501c3d030f00f55800ca00704100c03c1c160180a180b42803a8110342800008003640f9003c0000c02c407110f4458100200b0303604c40d90034900c0c0d400d00034001d1b1070020300c0c43c44003c1da1951900c000d401540c030b08980358010400c00068400d4000340c2d2200610a4007402e01066542d0b42000c620b1655180030704141d500300d0703c40051103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 116546762 1106 116545656 116545661
    0x30906010b07050c041a1f020606060a0203040905090c0909060f0a020703030e011d0d0302030c0703261e010605070506220203150403020705030d0c0209040303020d 72
    0xb180c800741001890012500c00ba160840e18052800c00002d40c0000c2804a100044031540820640d9440901c060070213036141401681c01140401c0360351410707001801440d030b1144100e9040c20303500c410a40590b002601d80c0541c640004460810a0914165007903000850000804090900e6400b801d048100180a01012540803801c4800c0620035045650440f071610028404550000341d0240030410150b030143c40c5115060703201d05407070b00078000d0740d00c1001d00c0781ca2582488000c0d102070383c808110070314041d2040c0e0005c00c442c9428402140c2107000c2c500a4101d01191071304c0104c03080c440340041e0002e41c2400414450200003810014400e80d1041c0814600308030500d068061070551203180200035410701480c00407003903c0112643c024401d5000f030f4221081d00c0c0d9640240340e2120880070740300b00055030820160003d410041c0780030f50040e201c0d01c0c00501c3c0001122100c0f04 = true := by decide +kernel

theorem cover : BRFrame.Cov 116366906 116546762 := by
  have h0 := BRFrame.cov_init 116366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 116366906 ≤ n) (h2 : n < 116546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
