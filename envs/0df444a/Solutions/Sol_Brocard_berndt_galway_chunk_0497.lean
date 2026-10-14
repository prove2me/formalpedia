-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0497
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:06:35.37082+00:00
-- url     : https://prove2.me/submissions/81d3d363-9375-48b0-8902-7397a150a960

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 89208633 ≤ n < 89388490 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 89209883 1250 89208633 89208643
    0x1a0a0602070807090e030306010c03051201090c14070b04290106020303070e01020316030e03070305030c010b03010507080405030304060504210f02060a02160f0303090203160503011109010522050a0611 88
    0x144d50f81031241c80138038042c000c81101c0d0003403c01d00b40794101007030900e01540c80b80658072800d00c00c80c04950001031040210341221800300719a68651000c4030301c0990040b10f50089440c01343c0303000c24000000d0000381e11244401440e01d01c0c643e0f00d54584260405203014104240c00c4000160400300501c41c40700c2d00300b21541800300302400554280b090300015840110ac1d010400b4003004103000000300684c47c01d009403130207150841c0c20b69a40e03043c40d203400390103010b060007050701079032070503000450f214810000e0350700895004014502d982c40316260034003c1c00d03000c0d000766414118032440341c0e440c2c40a0040c524015050351228948000d402801a0034008001d08414080e40101302c1c6640b040c03454061218440c1d840b208844c04001c00e402d0407001494000d100035018881c40120310300c40c000ca820401304580781100240100204c01c1c4000e0b6884c007440041a01007a01440360207010030790070308404d0980b10802415684c07a81d4403400900a03181d558003280200e003005200940503001480 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 89211133 1250 89209883 89209889
    0x6111314011814010e120307061d0609060f070509041802040c05090102030904090f08040e010801051003020108070503071806170a150510030f06090c02100b010806041a0a0602070807 80
    0x2645000a071070700c801d00300d4040c1e0f4001d64030b0400140e55943e0b07141e503544440d07680310443c0c1003045a031038131709900d0f240004140c1d000140151846003c450764001c01d0020b07e952140c1811400b4282548941d055128142c1002e0f0084091020074031003000305440b04d108900600c49408441c2500003002d0051000321020281c4071420450108250506030760001f046032210789041d107000070003c680b4101030b02c0094410384014201c000004c0c00154031401458600e040e44d00c410007c02c580e442c0d09042c001c103a012440002e011a050100045e80785010b1006198043e445040c403010b86824131078a140d00f06110381001c00401c40c6004154040c01903803032202e51201c0424400c0101810340080d040c0e00c5e0780c1d1485418854800341c0d01c4600d0f43c0b803090300601070400300000103100282d212141c46000c0d102600040300140f1500606181059442c007458030207040c1a1618401916500e0a100203072180c042051803a04841c502107a550b12680901c2c001441c20390702800e0583e060200d91814078035268 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 89212383 1250 89211133 89211167
    0xd150b011107051c06050a0209120601120206070213090b09010b01080603071502030c010c120e060f0c0306010905030a0602030a110406120b010c060c0c021c0507030611131401 77
    0x456075a1401d000003420100b6110b0444040f0038800e011088000c98000205000301014205824002c4203055a00500b0b0051411204215a51800a6215500c203401d00c6280b482c100b80310b03013410141c1082070040801c2e500240c8240c5408000044405c29249442130480360100742000700481000280300781d1802d40000d203442440c41c105000081ea542d4064080d0140141d0200f5005d8a058000c1044176001c2803600d0090080c0e03910074001a01254a058440c8806030070480d0b03003105454003198503445a8000088400c0944400e686c42c944c1c1d4000a00316418450309200205080ea000c10082d48c0080c844e80380035981c2e1804400030401e4400d0004080107207203044c081071000030b80100340e0480e5003516074000201030a00344012a0034204821001d80741e9840c0c2a4280d0380d040d070284041c200d440c02078442181d1171504000100c11064980300c00303010b5801c0040b0500c0042d220350411900b00807010561800c0188641411041004076031044207411007904070480296000040c0303000c00078400c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 89213633 1250 89212383 89212397
    0x312060f0b1809150a06080105030a24020f03060a050301050103080a0c0309032406060203031513090b0903032e05040518010203090c12010b0d0803070504050d150b01 73
    0x450290340c4140c0050040340c1d100e00740400c2c000010001040d0b02030305408000d00940090a2021401e110110151400780c012000d03810046820380c040d002c0a4101c0310090024002038080da01c0701da20911421074658201441c584d44e418200c0414006802c0c1541e0961003d5031b43c0c00e10340b041000d0404603074405400b907410701c030040020405c008241e4500c81d13110f0078091550038880c98100c407045c056800041030a41c0701854845500c240d2039040c408651008403c01032541c5600c016030756400100c5007c02e4100d910001542103080c080c06249944000320400300318109183d440c480600011165044a83d0000c0108445a2040f1111603009407006c0a0002c0e668101000c120428a160040c58066629a0041144120140c040006c07ea07880f000854503800c00a0810361503116290b190382c840c000320031169152100602c1600100c46005042c0307030101c1095590011260001800003050100070302001445071140c40300d07458060b108568500d4050b0700503002c03804130703030364001c2e15810080741d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 89214883 1250 89213633 89213639
    0x71707080f24130f0308061009080606130212010b070510090803010509070210050c03100b0306060a0e03100230040b22141605060c0c09190203070903031206 69
    0x2c46004200d8203101407512102ea40d282c03000c2250107481510010100514089180c0c00c0c50307030242c1401e0088104442c4800c4183c0c86036400c9841e11075034003620355185c0040300468014a000d42e484170900e220028003508006000303403002c07540301090340411004e0400052039410007000f4001c0030401412841d0401000c0d0040d1107030b500b24041400303224000c41420f0049109070b4020001e109040d07400342c2061040e85443e000c2040e40b500103640840c01c1c40400e00010544100074402d82c0e00c1024050a00e80c01d01c401c0c10070440701b114110780703603a0700b6008a9014101841042c001044034000701c8003015804417071544410103002d19004000180002d800c103100002c1c406864194201c400c841c84550b000e007aa807440420341d080c042005050040445411013400300c00300d130381c50001a2101180741c609560700140081c41c0300d0008580c0494100020040044c68941c04441e0070014601c0300c1c1289050100000040768000e840e90004900c0c2d00b41c0410401d507100344070346040c001450f801e10203145 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 89216133 1250 89214883 89214913
    0x607031a0301050117240a0b04090203160f0902070201080406020d0908040b120606030c07020d030201150e09060108060708010608070c0c030b06030609010b0105121b040e0106030b090112020d05071707080f 90
    0x40d003e001107550f1622230030540f10f207641c0c68021110442c2c0040035611442000c55000343d465045120360380c01c00144a0340010983e045100b0b4900044e0103071200e4140c6c0c6c0d5580d84180c0290b1204e404410800d0b80e0704270003000300d00d419002d00081c240801c2d15030f41d90b216002160022040050205102d510204100b0414400711030503141e155605940d004008541c904c0d09901424400c000038808009600002541003841d451150060300d50034140d40c90b41e41c0751000240c5519084559a000c030700200d0040107071702e100d680e0265200300280b030029043c2980340e5400c0e200614a9105440070740815090082c0c52600344952501f261001000b005000300050001c1c0883c000c104489003a009910001903482803201c4008810f08800189203a030342d40c4403000d021000c0300a0240c040068a444038000c42c41c02c1500c1414181c1c1d10900c8004c038811842d40c204001c001c0c144904403001d008001000914003811082d05410711040b0010f00020307800c00f1216441c1000c0d0003180c50041c1d118202c02c1c03002603 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 89217383 1250 89216133 89216203
    0xa0b1f210206033301180b160f080a0504050103050601020a030f05090102030f0c0a0b0106030e100b0103090b0f0118061404050907080307030c030e0d050607031a0301050117 76
    0x564103550841e2680c3d28505001c0b0283c0921213619000e03203500481d5400c0c20510005000d81d00c901742c9a0301c000b18070000c02a00300c04018001d1382001c4204111845201035994000daa4441c45108026440f1101c3c1d582c0e04141d8105074810001300700041000e00c090760300350090a91000c3c0030301c0100f00c03004503514010812503606099400b40880010600c0540e442402200d208540500c0181e0f5521054404e280e512003058a040d50500c20703070340012a10754440d0281005030070600008010b543d0070740d030840d402000e50280c1e1034141070303444070352000241a85661b1846400f400c50910403662410070990000c0e00d0104480d1b0740fa62030800203010349148422420740c459400d07034000440d07595030b118840c42d20155400c41c60003403102081090400d5400704030b041605111741c4c0c13072aa292001d2028003814801c106e4005206800240014921a210740d005031491030341913180032500c1c24040f0101c0e08440003038000c120000c0b00b001485441d0b5000708810700184564000c441c040680c1c0c1a0f0740c90b119 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 89218633 1250 89217383 89217449
    0xd1d011a010503090c030f0a03030c0504030503041e170a0201030e150103110102030408030f34111c0f02030607050a020615040207080d02210114120a0b1f 68
    0x2020001c40070030100003081010100e11030300a002c0f254501d00d5001f00c00c0e80c44251620440001e81894810040a84520192000c4950240040d4242400c0807030a2078600384859102091381080341c40064540110894a1030601c65000900440c40150000600351007500b07000d800c03903501c41c5041c07000b00c00c1039800b21070440350404a04140f1164000040341144119401100d07580f101080e0041c42494540c010000c1c407802304068040c082155a91101e101c10442040201804121030440072804404007401a240002c0414410429641c407480650400c0f48094400c0100040d030702085040800c0b0246e00071016007800b0f400e0245443c4000d41d80d43c001041c4600c0c080340482082e800c0e071100d805882800781c2c00505542c4070a0090311580003904080060042819800c5035004081600c2c0381e114180d8000c00d401402c0100ca0310140407890010200c0041a48511240b400106030121600c40c050070348249030800c00d00700c0203d4102d101102e50844825500b503040242d4580c0d042407006401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 89219883 1250 89218633 89218637
    0x7030b0a031b0905180c101707090f06030605130b03060402010f05071a0403020d08040507060309031206030605010f14030c1302091210060801150306090c09020d1d011a01 75
    0x84881010303030600340c0b09150f44410907150070304081c8004a021500742011a140b100d040326000c0d50b4032420014080b200082c028085640c40711480c02c1e403241100a164030074010b041c15500140d0300d0400c0500222030f030380140c00099a503081440945000a042c0c0d0078020001c030140201840d99000a449000c0a07000a041c410b034a400ca80d0154050001d5840441c0c21802c80100c410012038159040703a4102d0341180103004500038540180e00400d01d150080c0d4108004104150408000b074000746661803043d024800d154061042443e0240a0140a144914030208a6515100e1048070640e265048103805030300701c1420449a07100005c4614081d58200c4a1400710101d4404074002813043c0c4600b290809030702191460301c910700040390800c090000c44100800c69031078488a080795a41101c0100b5042090410030204200c1e810400400d03026083c003c000d50359a08040c0301b264056040b5065168a03a0900c54a02d481c03074040700d10444214000744148107181d01d01100a000c8400030f070f81 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 89221133 1250 89219883 89219903
    0x1206140904020310090501020d0b06070c030b1b030405031803030f0a030c09050402032a0408061f0b220b0304050a031d0a09020c0106080d08010314010b0d14010507030b0a03 76
    0x70941d0340401c41100c40404804c400c2105003100c0c02c00b94040e40c410000c1c4484281001c6450060f81080070481d0402500326003c8100345045035284c100508000d8030039540640650141080c00802000450140e40704500a5590301c1460762403424509403a44a00c1c840e0b0000d0107003c0481160b1000c950441c2801d00d000240320346410410340f0f085907160000398100b1f101204010040d103481507043c4a110426666450408641c0c043c5065407045014400503078000340082502460041c1403100000c1424003500d14980d100c03450000942c10000c4404101090b110400102240e0402d80802410030705549034510f15050302c50315521444580014100501c425101301c042d0f828100c54003400360300518841e50300385c0c5c0b100c500f00650020010301455520f050000030f038800000400c110401c1e029103989405a04e1a2208824003001c20f0b400a0749540710111019140d1364000c0070024107200c0c2c214160a044003040c65402c407040241604141481d2030140e150700c1c0d44192003042181e0340704070066 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 89222383 1250 89221133 89221141
    0x11a150901140a030f0903080411060313080c030702040509150901060b03071b150207020a150806012d090314060105010e04020a02160b0415050913020d0b030d030c12061409 76
    0x800405d0360352000d589042ca0403100c041015030000700140164080e2020406421a441c20030400303110585620031001403040b104c80000303101101400010008070152410101c11307030007103401d8031011203200220303802c50404500f480400d15000c5030000d1030b40008001c07403400c004078100e040c03001503c5501031006120240d080882d10458407084d195206419108010b420480c07100a90080c08080303200385210600481c02010101070101c0c01c00f404d82e555245500e0343c2006403404410b600b5000c4283c401e00310900d100c0101c003a902c0c01003004075030740e00254034510b00b00211807030040e01c1c4802c103036046100108621303a804900002c124100b101e0041c2c2e250200001680f8001110881c4001c0c00c2400034002a441e584c00060403c941d2010b00b01e9590a00715042120940701d81045141e200030107280140821001d03901511070a101c2e8800090013580c00c034002032401555500410009813111822030745554001b84025010800842c00d000c0e003420110001d601c2c6081d072801c0ba014081102c002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 89223633 1250 89222383 89222387
    0xd0503071202030405030c01030e1203040212030a0914030c01020703080c03070b010909020301180c0b07020609030a1b090b3a06020d050c03040b0412050903011a150901140a 76
    0x6032011948448044140c40040c440a9100d412500c40c0302e2190091040f02282540207000300c0c0c0c0810811009441100d03449512001c042c0c00250090307820103a201901001098100014816100151a01006107250501030300c0d841016825143c001e8115445000483e600040c040082c1c0b81d00070b90715034443c640c0c0200c652450007a01800b41c8464960000000c07400d00f9544020740490080c1e00a202a01007036100300801c4411140c02031000141e14070401065600c000a4002c07944001d01540c42e080f19900042d140c01e20070704c406c2c4d60080a46a42c600e0303c03030081b4882c10080c03507002e40a000740f40c240b0700050540140c010b1141c4980f03401d403d5229100c0c0c40e488a045071072103007005120b0201281e081041c002d41019440f14101440c2c07401091201e810b400680744031f2544524100c2c440d0b502d0783e64114064200300052014800180441c8a0f44c3d40c0030702801d00000f401030054030060303850b40c041200004401c030341c03e200c1c9107007000301103250b9074012503900302e8401d006441d03613a0328440101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 89224883 1250 89223633 89223637
    0x61d04150e0321010906062c04020d0507110c0303040b0d0207020301060f030c06020304051f0e03070b0d110301050607020d0c0317030a1505011b0812100303120203040c050d0503 78
    0x8428080003808950189007684604840c0f04141042d00f80e42e82ca60900744200c601074003032600800c10142c20494a494240004c2c8880040080280e520340c0d11744011509903085014148043ca4862040000f031940c4041d9240020142174018040c01c950040444d03101d00c1140a40c0801100004061204e40c0355601103a02c1168098020454142c0e5000d211004d6101e50208640b25040c10400003003c0f4400070544058400091640d08444000e0f20160032418000300400148821499651282d5405010402c0107010300d942455407580840d514104441003100321030a80b076411700c0184519142c6000713813203d550741550380440096240c2030044942540742e00003402d00200c1c1ea01d80b194662000041c60044002206c1489035620200c410600324036140510340c002034000483e030528019a640302d03000381c1c2c046d4414525042c2c2487c41420f0074242120483c00d15500302c0300c1041010f62118110100c034221440850450900355501002444035200e5548151090402501407101c1401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 89226133 1250 89224883 89224901
    0x11070210030c1d012a06150603060e040b012606010602031902010c0e010302030c04050d080c0708120715060e090d0e0d032003130303050d061d0415 65
    0x810084800d0450000a01808116500c000002d00428040006103500c3c4900e0f0a4680140c440d004414504600060400300c05008140380c1c460546014011900500c1424040c1184020101c115400e00d54044c3c180e40c0a64040044040c0c20300410010901244200b41515a4070070409070402120045883e100c8190800c08103c4c003a0400000340715400000030104081400404007035040301c400107900300c441c190881070101358a02c199001540c480d82c0299880314180c85018202070701e890100313003488404002112100030018003000040002c0113040700609a010080090320b8402c40c00c904a8098007400602c00090031401c3d148c0c4011940100c000741541c81281d9440d03180c801d103455a2240798901c04004540341c010020b03e42c2c00d00e021030707c0c0d1094040d141d41091705c0280d8207046445a0910170000680400e00c840b1240d4a0700e200080001d50180ea030f000d4868502d14070307480031180030b680445202c4200f111404c029104e2402c4803903010742c0061a114021214030700481c05801040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 89227383 1250 89226133 89226139
    0xb0606070302031201060801030b010906030807030809071a0403020406080606030a1203060e040f02090106020606060a050d15260619050901240317072117070e0102010506030c0f04110702 82
    0x3002260306c136845400e0b18100e074064a03880312180da0381c0308424116009404003400c4030500b0050800400d009120b5150000e107008122005256204415800c1d00e466100e60b11070554000750400c190f18150083c0f00140010901804080c100000026900d401ca90390051000000c61000d2030014001e0f8001002098501d80e507400c945410710708000c8104100f00308a104038181d6001003010703480020003074403515014100d1450800d1641c8162082d81056090440d056252000000e040c040e0844080040801203070406504045041c0c3c00c0042c0d00a20540c1c00c2940200e040004200301c6403c90304000329414800102a00c818003041c0c00f402c140c20f00483e803248165100c841c9131001090650480f4018070310116862079040c60040c1a2182040242c40e0724404e0346010310211200f41c1d4555449414100403030b409583e100704c0440100c04031600303408615481c416100c02e5030280200303507200c0e000b14080d040086100d00040c10018a001c00075002c1c59031a00115502980d100454140319001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 89228633 1250 89227383 89227417
    0x70c031202130f080d0e01051c0b0406080607080106020c060a051803060103080c010b0301060e061009150806040c0c0201022104030c0e0103051218060304080d0218090907030b060607030203 83
    0x10f8484010740304691003040200d101d82c2d00644003031032003034031552500201692454944403040315100d40f480c4141c2d5843d001d080e9070380440704840e9500d01c680401030958078040c0c1a24541703030002403c0d00405070700600554020a40b07403002541c07104200d070100300d0306040003a102d8504107214007649020540c000d80500c108800072052101e0f4801a02c140100080240b101101000902d030030703070b00e8501c180102038920074042482d501d84a400d0526403030f0385280c02e2000b43c1d40d4400d003a001c80044015034001c600e59a041c0b01c83c504081c00b030b2898850721820800c0d00c40b409a40000c0d42c0d402d41901c0070510051000005590401c0300044ae0000d6800c940440d03405a121403400043e12400c0c441216503200d49101000e0310000c100a070b64000141d4a03902720b040100302c092180a030310041c0100c4480c8001c00038a00481102d2014084102e214010705041310005428084000005080320a0b50390011034204001140307030b4049540194103a50240d00c403260352400340d02e907005020f11403007d20b200b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 89229883 1250 89228633 89228639
    0x5040515040504141c0912020d0506070302091309080904050912040605030a06050301091205090310050a0b0405250309020319031e0c030f05090a08010f09020f0306070c03120213 78
    0x80032602868201100064030308184680382e801d404e5154a108000c00329040b1401000207c1310b010b507201c6c035070340007030140010380c6126a00c403400c1200c22500d0a02007079005c1200c41d807505102c5010b4880440340c0c40e040022803541e4503a10b21901502810790701c9180c98800207042e2807070134862002c0424110340002d403a40d4650401030940d4200711501a2401d00e010320004562805001c0c6031526034112542c03050800c0200c1e0200d80640c4042c411640612170303c1c21031607013080140f20f403600c00c140042001071100c00000410080c0c0b007014119410000741e6078810a0400c0d00c9003a0b00c640800d4034200011051020b10129040c40c50b04070411710314078180802d44042c103800c100000701c00c210034a580928034103000ca082c0c440102084004d000100c403580d504124600503001004903040040040313a00594801041c0d0a65104a14488007580c659039640c0071030401c070502510402c8120054485403400f03040040c103880038044040c0c10090040c6c85089105c00c207604880e000c4140310b000c004400c1d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 89231133 1250 89229883 89229893
    0x102070204050901180201050c0c0a09060303030b040b0604090c0c02030a050618160303110c041e0f0228050c0601090504031202070b0f0a18060b010905060c0705040515040504 77
    0x1100103900503400d010001e0030651061152083c185020141c07210f20110b00d80044456400940d888003103842480c060115641c0c030044c201c802000d0610000c00c2c05801d5117001000c0d0350344400d489005a003880c00b403020035501c600c01e8906843e01d101000480314000c6604482c9001e000307802035014002d024007041400000f107049480ba40280800d80fa00512110030280c1c0c0f640441c0c44583c1240c000e0100340000b0f4410305151485050741802c90310760b0070350b08000800b00da52413040355080003e600038090000002d802410100050311100310b0610300000030300b03011182c6a0f070002c0b41007403140e03190788100c41c0500162007501802ca42260b0303441da142d003c140014102034509a0203c0c1981200b155240f4541c02200c0b081941b09841c194a0340341c002c0103c181c000d01920a0f101d464503600c0ca244c280c8001d18030816800d00a01d00860b50401c020000340c4146c2c0203800581c0501e0f0200450712040c00700080c3ca000303e4006a600040560311003540280c2c0c00c00400720594014200400d000c1400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 89232383 1250 89231133 89231137
    0x90102120d0905060919020d02040603050613051c0203040302060703031d07180207051b03100e0303060f0102030c03070f110612070e010206060a0e0901061e18020f1602210102 77
    0x903c03034011545a40c9408042c260345503488001308940e28140708106006007440e00718190f0051007d00041107840d00c0f0303503819052000495003c10780c00c0c281d02400c01801020405140b41401c0e5504292080d546004025102c0c4542d0001038041c00000442104040c801e500c4041101c03040101c052030344e900024031750b8030b600180c41603084d456070364500c013080c80c1c0346072088560a584c008001d00680740b0f0303448414102d501d42010729034503000f010700c0040c40b400103000707400e020302088001d999245000010001e503803034860307a01c41c115071041c008031001c0d0300c00004031a1020303084201d4a044211620b13000c10301c4034001540c207401440200b0320381592282004218011315003078880462281c0380d88012a5078070030440c0c40d00c1c1e00c803900389402c2028402d101c000d560405060000450010b443d000e5120346000f00c844460301c03894081004104003510713610303081900c2e01c000005520300f04402012a110340100300c9800044600e10541108543d6507520080000080080380c0455080564550b03000b5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 89233633 1250 89232383 89232401
    0x3010b0409050f1003140705060a020a03030608030702210f0d080a0506090c0306220e0606030d05030417180306040c0512060108031806121003150c090902090102120d 73
    0x1090500020464450701d41c10068482e40741290243c005178603540f03e0000c0980e1031104240c0f9401211004106503c0b0340c0020f03d040401600101240043c0d4600101162015406a03086070030900c81c1c0001a40c80003a2490f80641110a50f03201d2040e100b0283c0c2441100c2d00c6140032445065094014140c01520070f503c00c07041584104010340d241c80c00c1c0700001c0c2041b982e9141000b8108009091440c0c868082c003203071480340803210020481c9000807021654816405012603015400f00110b07031408200518201020340f03489411414540d4810021003800281da692701140410b00780a01d14000e0070501c0340c1c1c203006080350018241400d01c101014078034001d07240110902203003c2710492001a00f41e04990b01503000703518154810101c2407000d858020402e41c08030081000502c4080c10b041c805002c0d0a542c400c82d0202455031420201c0d82c480c0801c1e01c031030b19051103040c0712080d4000d100c0340c1c101c2d9414103015981e8100c240040f070518030342c08103c25034080082441409522954804654 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 89234883 1250 89233633 89233649
    0x60103060605090403120203070c0605010308030a0c140702010e060f19020d0201020f03160c05060c0c010c0306050907120e160305070807080d030906090b13051c09050d110603010b04 80
    0x401a01d50b001d100da07441c81100c001e4040790152a0f01c1d904003103598019540141c00d4504200a2845543c40806540b8207900940b6216408410300000c85441e01c0781e61018280780c144023400c00414400b448050165442c0607060160321804400940c480c00b04481104110340080c0380d50b040031401e031004a408200f440001071140c03101109650f07005200b250101c04440e5021030542d5a0400c0050a2140c0d00c000d0303404110220402c01c0008200300842406515036164298480c0041086142150b041c80000000c05052110030055a01c40980c5250455060b00e006075a02603802c0794080a40001d01c0340240520a41911144c0116074551050035244514142c8414a542e25889591540a40200300e04c6412040b45403030500c5c0694400030000d8030541d0041a03011160702c07600c9250608680024501004009020801c001482442c00500700140c26030700480f040c4e80c1c018117a130f88034080caa009510075841c400070b0007018100300b8030403840140590365968440c2d070000c060307030014030440c05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 89236133 1250 89234883 89234891
    0x20f1909080c0105040b0d060909050601030b06090105060405090a1b0e190b1b010618020d0e06010e070e030f010c050705151918020a060801050f0303030c0a18080d0206010306 77
    0x140071a0042005906014140d4940341040d041410601d5554022904402040e98601000a41503082c4c040d140707956001d031025000c0ca42c51030404500c0c100d001090075100c6c003003202c0140846d55581c4181ea080e9042a11526281e5030341146c51801410f021781e03840072141c449441042c8490703011800c4915800280d464800307500202c8070b681c0055905000f0410501c40c14400314160f90443c4001c0c43c42d00408030008104c0300d690302140c4078110180710150f03100e107030009580341501c3c0c07503170041a2450400d40d00819140d0b00d01503244005000c080c102104201580011020340c0e50200030420350207440310020003c12012920140c020703407042000701c64a02031544003440c6d6018103a4510300c2100c2c00022101c12070a10030a0000421418020107a0012100642c9015072120308150029007a40c2c2c96440c610b5040104000791402110b4030244298010810000c03540115002d80b0030301d05290400c2040030400403c0c1c080307041c54980000c8018072808080c81036959000643e14101c90040340b00300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 89237383 1250 89236133 89236139
    0xc08010605030f0312060102160f06080601021902150d02030903030a0c020307031e030905030c0a060f022d0405030f010f05060d03020604032a0303020d0b0d0c120501020f1909 77
    0x40d00c83c1c09070b000700b10041e04240300c28500c0803070400ca2541d0202051055804050b04840d4a26508040b80c100b0560070141d880144505900020020f8100200340001d00051841603c4c1c407600b40c05491000740550703030155001d4900c0d1103190907290000019082503440b450140d1002c0d9480d0002c6a42103500380c24000f90002d818001b1045031101c07509965504816030409031000134500c4449096410942d0301c90074030b00824420700c0034101340f480b100d01034002940300b814100e0030f540e90400341c42481031040051103c14213a940380f81c045424041003118505205620442c4903010300d0f0f1003243c050007a402d00c41c506c1441076000d05104605548200f00c0fa0b04c80f8000c0c4a031a607015100100560f2050001c140481c0c06001c000d00d03021544003050448121540c03107010a4000324104401090300850b1400700329801d40100c000e946010ba40c11007550381d070742d2145902c070400303807240f0343c00c480c90850640f050100a4040312421605850b801c0e41d2821a1f000d07001010940c00e44140004190305004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 89238633 1250 89237383 89237389
    0x30c0604020a1208030703021c0e151006120f0e07150305090102090607020409110a06021f2c030405040504150c0306030b19180503071502040609030b070203070b01030c08010605 78
    0x2058150340040f01300f401c6644024058009502c22881d140d66030560012208004226000d6805213002c001c0c05801e8028007600500f05944010303041c100c8101103985c0c00d000c12640325485e13690b0010500400700f44030800031252001400c0c4004065074601a15401041c440e0b400d040c4014400b000e80c1e400c11044e500c840f503407803c03409202ca00790781c407034002c000e044050b00d0300b0381051141d58080c0044900b40030b401d100003108900740782e00800150700280c1400741c007006228000c6024269604003800360344842a00c18a0351250118000c070b0389103070080b000040f01c40410540c9d001d480090401c01c13007414241800112010310000c426107407401d050b17000f80d05511a01440084960140418404d80c80e00700c181c4e05140c0700c00c12060f011680d1481c0200e050500c81c0e007100c20480c0a000034590b03035001d905000b0240c44403d10302d8441140100020007486174400741c00402c59811032040d4500d5207862104038154410228003a219105020002c410700040c0307074000049404440082080d00d0359503080c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 89239883 1250 89238633 89238659
    0x6020d0c020a09051e0103050d030e0a112202040806060f0d03020a020f060906070f0209100308030c031005091504180c050f04110d090b011a1e0c030c0604020a 70
    0x1009421030b40c0014200004403681e08003035001103141c6900452210641c1d848100103000341d0003602c980d4800920801c0c040d4140c4654411001a5005095104600e4990314003420709900414054610308010702043d50012410080d80000c07d0015560340355142202e03130341c800c030070351b40c1d188581e90350480602c5e5482c00c80303902d5113100e034590090080070141d50200f00158031000c940c0c40d08900c08100308940c41d6160f500401040744101c040100042d914018480280700061401126502d070120030720224042805a0368003400d00300d841580c1e60349000032420b0b81d103042d40c8641e404c0f0103200107000c000440000c01c040c91040c03d075010011890a541039403405102130705c0180802085900070b01007801c2c92054032084440180003ca1541c08100360300300d0b140d00000640200d81d0b62000f41100300040c01e00c00311f0040800c114045c005011031001c4801c584075615240940c88005840354124110180949010810305e03030640351902142c0b010951941c20484089100d100d00450110341c10304c034455 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 89241133 1250 89239883 89239907
    0x30605030705042c120c061e0f1902070c0b090301050f011202062503080405190b0a020a031104061106010503030301061403040c09020f04090c030e100c0c02030a05010606020d 77
    0xc0183d0041c1300c00698802c4600400403a004140600d140c9003580d480c40000409003442180c009001601c0c01c00d00c40d800c0c400f04c05a502a0990b080c5060044c0b80c990f14071070079041300300202402040581114503500034400d415000346811500c030b20004040344080058218203000f03600074002551405074104020101340210204000848102c00140c10b1000182803038850020981c0070009480c55001d0100b080c03064110300113017010040001300081801030700c14107048501c050031400c0d0159158084401c006001408240d0b01080c040e90030391194001c0710061040381da5441d512030301d8400c010246c0c6d02e40111401244551170000909060020840e41290300560318290589084462035009900c00741055921410b04000400c801110744000c0406180e15086140d03101d1408100c60151b42d4800052024589818000c0703078250000f003403d5150f0a41c0c00301c0041d10240ea540d060310444001c2030065098841c2c6050396041000550008090311200d4084400c41c449414042b101c0564102b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 89242383 1250 89241133 89241161
    0x20f010902091b04030506130c0e06090609040501090c03030206090c01020c1305190f020a03050105030109020f04200309100e16061b120206010303030f0b0a0e070c08040603060503070504 82
    0x1d00003c454200001c20920403018079030800389004d0340ca40360a403421406590300d654904041c06a1340070400c20b03c000c1320043ca000740300158207250041c002001044010105405001d5503800a4104a420b40c4005000703a070100b0710028071038880c1002951410111a110307018400c1c1842c01c5560340c0001008015918020407049015800b00150000b8110140201544c10940c0b01c040e42e051056014104a044081000507121781d084e0f000102942c4d01a48007501a9152035a0b45c8050380358045038a14021048d5400302d0040b0105090004c248014030840f840c1e03540100600c135a032200820214842c1503080c4050110f540b59036035203521901d046000b2080401c004404000e1070b0302a01d100e90722040b03d6440c40544031119111201c0403c0009400801a041403005008140d0907100b0032204000d107420800034076400401145614255000350003400200d0000200c040348212080c80e1030f150b00448040c0c07607a0342c0b404040c010385200d01440d88680140080031400c1e04251003140c450001d05 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 89243633 1250 89242383 89242399
    0x506041d070512031e070206090d03170a14180705040603060b0307050a050907081b0304030201090c0801150306090c0f0308180103020711040c1205161e020601052803080a020f010902 80
    0x5e4504080c0d00001c0f00320303001172041c801d107151681c450b6006090f03640251503e00c011210140040303c0c00c04018405031174180303014405070340690320304489640048441c8846090043c50a0b025180c60201d903c83c0794000d050010100c10001e031500913940c10b5a0a40031154072070780710020424210b607a0f02034650056103c00020720305a100e003502c160040240d20074000c46244c4128126601d61003103600740d0250703440704040401c20040e00f61048c028100d0030000c01210303000b100030000841113844080e1643d0340742c00d00789062000c40c4e03000000400640540c6501e095503403412200d183c0011002021032060401030038515406402140c7c21154030442d0000031202401c1000002d004c014090340c1013150504540210481c4e81c03194034003031800e1980c0f244108210100040081d000c2c1c03d1601980046d40b01d420070190f80018400c0d05582d4200c2d01c2c461180440340c000d21040d03102014644c20140c0f2800c0010500c41650018110382c8459429644c032102d40765502401d0301c400c884000d42000034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 89244883 1250 89243633 89243677
    0xa08061302150d02040b07140d20030f030109060305060903071703090316080309010c0e030a060b060d0f0203060a0b030603060f060409020310050108071509090506041d07051203 78
    0x3214003400820682e4188a90410404800b08400c0b0782250b08450008000082d00906000c610280000454040402003c10250041e4018140e80000fa2102c0044248511020654005100b6200b030010f19a942c0c03612984d480c0010b40290040380300a5815005100108e0480040401110800c0e03801140074003402a0192103043c003070740000c010000c00c0c0030034007084000302c1141070801203983c000d2030f0003512802e048040508442c40c2012200034440d2020110341c1c0c2d80c40200d0403403042034000000142c802114000300f9500c1c8194980c00c0078030342c03401c00b0320300859115502640c003c000a07642480f607183c48201c0e0100030710058500b00e5040c0c0c80100040c0300710701c08040099101d800039002048003091580070070700d010203419440c1d800c5600d5100500c4803030400c0200d44c00034202000764103180300752180080d010745041c2c01082c2096071107100169039610b890308001c504c0a0b010080804c803198000b480d41e203411442c000c00c0e200700d02900700a00c1c01d0000005498a82d042c202c008440f240e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 89246133 1250 89244883 89244889
    0x605070318030204050a050405120a08060607060902130207030f05070203150403030f02040f14030c060717040302130506040e0133090518010e1912030906050705090a08061302 77
    0x4995007405100d01c1a0072008001030300c0c2c9025040c014550200c0114280c1070900d440c85c203198041d40e0040324400705110424807280d002c02c0181c0c220340141c4503c0e66402160520501030f203000d200207900800c048a0910075412994000c20001d03000307035600e0290140d0803008a0b101d101d1204065890b900c8a03140786030240703e20303400d190028031074200000c42c9200480d160059030010740c0001c84014070468100b0854a207030303e50051044089010b492200074100c0012014042c0e003401502c146813940142d014580500304031805103400601d2800640400340c2000081c00d021a084e5005600303140841e9400d2005004020713074805030880800c0621b8401148908072949400d0b1000d00740507068000450701687d204641c018030b030106800c804903032102c2c0c0040c290303242c7c03100c441d84941c032414400c280d4500f40c992001d44994032139001a03800c41f440354114080c0c03283c894050150761038042400807490300000101040300003541d01601042d03440b05819290a400c030794070781003071141d952601c0042c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 89247383 1250 89246133 89246147
    0x806010501080610030b03120909010911030c0703210605190501020d0e0411040303230903070b030a09060c0305090f010e070506091c0b0f06040b0112050c1204230706050703 76
    0x1902c1380c038000541a0030100081d150001c0354400c0b894004000031380c0100c0c0c0c2003080b9514098040044284415030304c4203030b580010f11008080b5000d0003004220041058490040c071000c1c0501d1212000000d00c0c542e074424010320f443e01c115446020301d003002185000c0c0841e13034842103030016000707480d042000324000c2d2506500814240d0780f1a65546803407030f03542204006000654080e555100c0d202001025605988201007c03440000d4014000c0c01c00b2076400180401c1a552007800072a00c030345510b203488000d8980341c13400402ea541046c50b2001c0c40c1c0d42c5903200b588540c5924040703d4a40455803105800c9407130321103407401c450704450740604c1036080580041c8800d080280102c2c24500341a159402e01482c4c03040b08454902101081c400b0b070b104d11941940d08800d0803070381041040103c4002906440b4a0301c6544511902d035400204c010142d00b003585c501042d0615013480f41d00e850b00e8046400241c2d000b840d200c90030803220384130510314002070b044181c84c0300d41c0b2698605001618151518 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 89248633 1250 89247383 89247409
    0x1050108070e0f0a05180a1503050c1003060b07050d02011d0709050405070302030609010606020c0f100f0905060a090806070e0a1202060417030304020f0f0a0b070503070f080d0608060105010806 85
    0x12081c01364000515855144c00c41c00d046801400071541030074105224002e4424140a5003401d1048110070f101040300441e004003005000c40f41d880300d84441d810182c01038400f0354852060202c0c08150201031141c00f01c1c030b0340382d6440268020070140755001c45000d00b1200409507400306a002040a00841c080ca91041d9040350140044617401130b13413940020704d8400103d90380080d076519043d040181d40e80401c6240c09045c01180c201c80060600300120310125100c20050003008100032a44d00c10600480340080640b102401c416a1042c03211f0b4054600d80c404c2c42405c6d000c0c800e003030014240c68400c00d1069651903004050314111881c000c20070b070009007060000c1c0c0c0d010200b008005160509034203080c0984200001860b00c9180a004000c1d03030300c529027502030041d000f20100d502d1a175921040d100c146c070401c5e03d04d41c1d103407a80390414915602402c1d070010301035880649000c4c103102e10400135291340300c4110b005100c603548a602d2140c6821081c07060074041030078030b07000c5400c92602045081c50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 89249883 1250 89248633 89248639
    0x5100504021b0109140712020603070f030e031914030108151f030605010302012c0d03030605030d05040513062405070b011e060302040b0901050702030f01050a02030f01050108070e0f 80
    0x10501c11142e828210745000700e040b52042c0c0e40c0c1058400034034051021303400070800c802d2030b1880350010390041391441c40300414882c100b0985a03503070010705019911031482e407000321081f04d0705e44204d00311030300e00d1280c0c102c8800046a2208550625080e207001202c1c16140c240000e005120180005582c200c038000d04000603196848a4044007141c080340b98400660141d900840c0c0b5502d180005006118094220410004042940d0803003002c100c031003600700b00703081d01c1800c00084070b820110020410358100703550600640200e0640503901074084c2c016180300701c0f80c000000c0001c1c1c00520858505101c0e500c02c9009100201d02003041c0c01c2411011003010f03081c20742c50f0046a9640244103e42600202000c0306841104220104140c40d140003070039060404501d00750428a6000707403800740713605030f6040000c000b40220440d2414050b10202e04200b40090040d07042c03096418001e900112800074689419000001c0c566205405490103a046519003800c0700c003101c014880d90020202940da0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 89251133 1250 89249883 89249917
    0x15020702010c0b040b01090506091014030f010204090b01021c02070302091509040c180207020102150a0222080c010504030b060f19030809030f0a15020705011d0319030510050402 78
    0x80803c81c2e0451842c41584501030000856043c9078800084880150105000d80c0a003c00c2001d05000300345d01000741d40c503181642c0c16010342e0200003442e055541051f90100c3d4008200054011850340083e03c410000760240c611802c1c04800c44603200741c51098000040e400103200b0005800c1c40301c4001e4029801c030080000030303080c1d90085001c060081e50100c6807017441100800c00340078586c41c0b420003c102c00b40294503001704d64000035900c40c1c0d0b15141200180c0103401040110b2160781c101d51500000d1103107450030002e8599840c006142500c51352101380107480d52500158402e404031400d07039034005d851050503110201441483c100b01e0f841150003406042c0785446101458050300020740c03140310055036030104542494100700303908064958135400708500e02e0028200d4000a5134400c042d46006888000504000c2e001d800b01585050702500a80e0408080107000b2004013102e8203040f030300300c02c400c1103400200e0403100d04071625a100038002e4818405803070184c004080304110071340d50700 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 89252383 1250 89251133 89251157
    0x11030109080a050a080606090a0302010815090403110708010219080703060509090307030306090605030a121817061e0c070305040504020f12010f0302010f0305040317010e1806041502070201 83
    0x11400b503020315080d2003c074401280201c0081e038032800c5580d1000003901c000f41003019003c085503403031410b404000d040c002500002402d005076088030314850314005280b20010f08243c10080d10b0a0003607020040c0c24014010302042031101402202e041c031080800c40c08e0b2010350b461045862110180082040640f02c0c00000741d1030351030600303041c0104e0001015503070b500018503002d42140c445a0001d4406400c014080000d030f0390126542c640244c2040d0a41d20440d407601c0200d6500c1d9105012000414581c2804240c008a81d0404007803000303400110b442d00e07140c502c40c200d020b00342c40c80440903084507000020701c03580140c3d0160101d40d119042c01400c080c2c4940009040ea04101002c0030381c100301054105560402082c03083c014510b8001d036810150441d000200340d011155007003001e0540b6003000c83c04040c410b510310503d0300c8050360420010358450130701e01001101540c00010307a8001d04440c0400170790100362107000300c2d8440d0f10501e140c035003243c844020b0341081c1c80036410700240c08441c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 89253633 1250 89252383 89252393
    0x5041b03050c0f04061401030207080f0a08180a0f081c060806060a0e010602100207022d040f110405100306080a0f0506070824060d14041a1311030109 66
    0x100040c40c803840c082c090340030361001805110038404610030311440c10104200303c85150b500d40400707420303020f103000769507443c09060001c00e92081003000d1441c0180050b840c3c3e519580003511500812145000ca8643c441594406640741100704000d083d08030210342603000510158020320000c0e00e10803884182801001c09002140c0490380700340c0281d00660704105283c0b03400d40806000e480146c400b20040d504141e0b0084d40ca581186034402000c2c2c0c0058018103650722250b00c00c0314008000003481400369154940d140804050074510700640c10503254502e02c2243d07000b03030300410380500885401d041c03500d001c01031901a030014440030f06981e007401040c000402e22454403403034041c08040c0d680e0146031a066141c100001e101504200501d0140010000c04c03c41108401030303144489135010f13511034000740e468452003486868072450130891410b03298500305114440c6004618488804010200519406070300b11807170720700044052078800c00150644541103284401600004461446540d5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 89254883 1250 89253633 89253683
    0xd030201110a030504020907020f060a020a140a0c03080a06050d0b13170c0601090c09050103020c10050a0902041a061b190303051906061409060708040902040e01080607020606040504 80
    0xc2d540000c0c0c6440c100019401c08181680c1c2000d800d20040480442110b4099191880581900a565000036020412507c03600c0d07240d00b03404121a4a80c0d48098003100a080c1c480f040384102d02246080c2d001560b0403010744a00000c841c07000c0e10070010240c95907140e24803a800209012010765200d030003d8040b0700203410300316030480b40400c0301d42d031a031280d4111403410205901c1690102d041c0703d8401405548598000708540082c03e000d610399520304d640c0c9007040e904240c4084000d107413608000500109400c04140070740240c03070030003901c004943c1e504408074040000d143c00400c200b0075210180155646002d5458a240a4036030b8401c00c4012038030400a41001680000d8a88060191005001c035007201d0118800c8410003110b403400602502808541c00048404203010826484545450b82220380491f8004d054941c2e43d5168031381c1c0310007904207028018482c0c081d030b400440e400d44001a11801940903400408042c0d03150810000600300041c021940399007c200100a40201600c0e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 89256133 1250 89254883 89254897
    0xc0d180b06011106010501021e0a050d030c0306090b030304030b0c070f2405040b010b13050d05030a090602030310150c0803070c110d0312052d060306060a140d03020111 74
    0x88044000d0a146000600e09000803842d2243c41d0070204c01000a680c000514041c800c3e011090240b10303032a503029213030603c00e00b100040c020380107110080e40c81903815404504030f807540380c40420000343c0781e0f200d01d0308071040c20768101c0d0154070411040c80031402003508940d100501c24441442c03c00550349401000c030030360800b240c13124080c10321413441d1242d80d95500040d540c5404204024034041c1c8036a2044141071060000b401c1c3d0005103100e00c1e80203000b02001429000e0482c50128180380b90032581c1c0e51100c0454000510450300101d462403003c01181c0c003c3c3d4216000d1151030b400c004024280c00c891210b00c8081c000c9200404000400307001c0594841c0c1d0843d200d0110380350751411300007003c01007102440d125049444101e80040d401000c0b045421218000000305592881d00700c0001800e00c40c181a119540c2c0071140c43e00700280d5008501c40d800075403e60303178541c442c0b40c03d10075071600c5e901911421303000ca8200c40c080e5041040051509034020310003c105a001507030316903050751003c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 89257383 1250 89256133 89256143
    0x3040504240e22020906090402040204090c05030a140c0f0d15060305160504061b02040b061c200409150e0a0c02010e160e04030903020301051006031508060c0d18 71
    0x200810910300c003c10206114590b20440071104108558002001c0b1000100542d110703811442c041010340d2240d43c107803805041c41d60740400c014045c1420141261700125202004181015081003110160203401070050f0b2581d1900c03400e00c044042002a41c2e00000024509150381c1c10281c050a182d800c14040101515100001e95040861503000348210301801402404000c0004212181e40b203556011427180c1040f40d0020b068880c0b001501400a2945280c0e1049010030307810201040c8052840443c4190b0f2404c1103020f0082c42c01020280e1445003e9030703060b0b800d2000b0802c0e40e285810102c0c0b040088d80c51a6040b80d10740021000f4440c1c00c1d200c46400941d00d800c1003200d036409100ea80d059107403440090aa071440468070841124282c01205c02d01c44c0004003103000c050041d0034000103968014000d200030b00c0e1003510070301940094400c1d035001908100030544012582000c04094502900141807103965524000485610202c1003400140d40c60842d000710903801c0010201c1d151080c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 89258633 1250 89257383 89257409
    0x10329070908010c0e010518030106050406090c08090a030e150c010501080102210f01050f01110102071131050624040602061b040509040609120c03080a0903020304050424 75
    0x40b44030742115180c8028109016a40068500e0b1781e80000c181e5140e68881c841400360980d500e00481d0260642c2c1d80306582103410680f020070040050703088441040e410380d076032500340c0d610f0400b0107680f21002000034001c100035020503256410040f0003840380c0d43c19800b106190501c0d40e4252821600d00741e115070b40c2c903540400c00c1d01d91396120b98075600d03d0060303051070220a2306044030304035407501042c80394a01c100c85814520015901508400c40e40e4400c1d6070007151680d1650525080044501d207071b280c81011411046406950b00d100605011449100300740055021032075910000d09010f0031169000305404140040301414038952000341000300090307600d0758500003000e481c122000c1c06021280302401815102c1e0703648174003034504444080f1810507154959013040c01c02050110310103004140040c00c0c8400d100e0f0082d0140050a10aa0b50550140d1740c040c402d01c00c5800c0e0402c0240103800c00c00c01000f1070300c0c0030780115070103168060302c01484c2c0705000c001e800b01c0d6995078820b100101301 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 89259883 1250 89258633 89258639
    0x3020601050907050a050319060803160204050a0203070e04090203121b010c02010516030c030b09180732060d0204081f020a050a1808060709031401090b0103290709 72
    0x541c0714507400c043c40b420518140f8408110140050000a048070010541c40c42e400034081c0c0107400c1400200b03e00d1050780d50782e100c030b00e0250600340b212074400d038055410140442c41c0c8440354403c80e07201d54040ea40b2102d80d01100030070040680380100b01680e2511921000c44c500c04842d80c0102584800c0c01c440800d000c4003034140c6820745085182071401c4d64036141c100700307500680c1441140390550510f0001a11106818150010106d030074155805c105050201b1400c01c0302c51149480e1301841c981140c009503921030708000d07044d40b81c800d030044160710b9a8001003604000544160805001030842d802d2050482c10441240c005078000c030705c175a0110140d0243c00385100700140d10036007849010361800380f0521003d00740d403081e46038a108002610040d4055840151480303400341241c642960711600741740400508920281c04190341c51800c48000004078a01441602c1c80742c2d501c680c003c1200d07841c6d07440d0440341144d042e10420100a030000740c8040132a8940c01c0c140708a149890755248241 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 89261133 1250 89259883 89259889
    0x1051602060c0c0a23030706081b041503240303052205090f010e1003030c080d09050106090c030f050915090a080304030c0b0609070905040c0c02040905030904140106050d090f0f0302060105 83
    0x2851171500340c0250403900c03041c044c0c6944072081580c40362017035003605070324800000309240c140300d203500c91040700c0410350007540d07080d0b8187c010aa40035080d4111121401005017500301c440300354480100404c400b00020141c0c040001c407010502e461b03100c00746140995802c017090080c0300458070181d81941560041c00340342245890a60842c107140c4a041541d8190b2b5000b40c40601d040401401408022540c5900980c1e1500070100d02503000000f882016a522210b10240000560700300101e0b080030700d800c9845140e81b150f00c0c81030303d800300240301ca85c0300103642c1c40e100c200c0508003000602900c03010380d01042405006500581c803c0c0d98003411032506042407000c8a0700900b00074821400030007840401a40078590340103451742103030001000f41d642c50b8296044514608020b41003800d1150502c00d100001c4090003940c40b05550a0254400e02004034800100c24003c40700420004c2c4001191000b095100d524418455090040013041a8944000031662400100c0060340410014000c0e82 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 89262383 1250 89261133 89261189
    0xd0b0405012a03090c0305150703050a330b0c07030309140f0f060c0106031a010b04050616022209030e01020105010f0e1003170304030e01051602060c0c0a 68
    0xa940219288002d95900840000b10341c5659030500405845104034018040c0c042c420300025507010040b00c001d92030004a410f8038241c222a15000b01f480c00c1c0028880c6401c40c0035010b428070440e07624580401c03030301d00341d070b003804c8046102c01a84401e07076000410181d4001c0300a00b508100c40d001095a58a58900142032091940004a0301e0310328501070400b580f5020307040c0c0c1300f2000484200c44144410004140350780a141c2e5242036960070705c80700000380070004110703480b48000024211620785e01d03288603035018417452246580241c030411491116522803103203e1805880100700300000e0326034555030710f20700c1075009108030415034138070343c1c203041680140c020165003a00b80001e2189600d400b50008421704503129880151100c140000d18070b484000c90315002e50750201950100811480c0300050365001200c0c1140440e0a401400400358014016181070318007400700314040c031745258280310883d0000c0014bc0243e00c2040003098031035440c04031a40c003420311481e98451403a81441800d000c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 89263633 1250 89262383 89262401
    0x305030d0e0705150307140a09050a0b030112170f0d0b090604110d02070f0210030501060206010b1c0923010b0a090b030601050103020702060c070602070302100503090d0f0306050d0b040501 83
    0x756201c0403040181e41c80350070001030540c825684003a12552000707403d551040c6801e00021803000e000a28100968000d4403070800d64006950003022203460f010005400d21081c01106d00d40a1075840342400100d107254540c050001440a036403d20654520600700c03070300400843d1401a440b45403000da00c1c1800500342c2d50041d0216418000492070b502095003921400700e208000c02d400240580601003545203604105902070304100b241051a81c004000f01820b000c0c1c5401409100300003d003c49000003601c072005500e0100a052000d10080e00c001840221401c482c0aa10545424000d0010798105901e82c900200041b941004c80d0040040b540300541007071820900c0c100100c1d8841d100003641d20b05480080c01c00690740c8240c1d00000300380e40503901c40000588285071001c40e00640c08103110085910a680b074210301c0b441180c06030b645010454010140358480e03001c440243d8030840504010146078140007030308685a00100304803030b0004c08199404c0030013405110030048244034941c09 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 89264883 1250 89263633 89263661
    0x71503050103030314151201060b030109050a1107030203250b040b06090a09081602120604050109050606011e0807030f060e01080f0102040f030312060e15090f1005060d020c070305030d 81
    0x450b01d40707124440c00703680341011000d0007000a4507c010301030070250700c920060080c900d00300e0348075a903034070400d03001e0a011240e896409040c5200203c01c0424402604c0d14558141c02031410300d000d1094500070080c54800c1e00c54403483c500109008103410710502800ba038002d8000221918020b0107000304004003034070301001d081c88d1108290100d070220054600400724242d083c0303010b00c510300000303910320000030700e409850103440c0c01e11081110540c003514240d80f00d82c0079105030b03580b078500549110b1400e000100000c41100c40c0840d90074410320241d41e111001d4180000c4042c1da642042040300c1644d0800341c0c01c010280f005011140c0100003129064020b030000350b24003405c0148280c00020b03d840020240050204018200b0071144c2102c1e014101040c441d82d881d1420181422616020904c5ea034014021400810140c50707040765054819503504c03928840c039628200a0100c10b80c06080d07840300990b4240010606070301c062107164010b600a8008540b207070050f1903800100c9a0500021030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 89266133 1250 89264883 89264921
    0xf060b0a080d05040306020c0309180103110904080d0902030f0303070c02030c150927160e120601060507030201090b101706010e01030f11030115080c010309080d05090715030501030303 81
    0xb202c0b9500c0b204a40540b984502e0258965101040c02407030b500425078415400225011030780c801410620300d05040b2801a204500d1540912090000d450015200508510310070001100c852903039030001642140702a08840a21003044811030554001380d1340c8000241e9202c40b030009601e42002084074040c411100c00c0b01101402800815a201c0c07030507141d0094841e050a104400510b146e5041c490001303a41d0403445180040c1d582c140c8442c404c0350140807404040d188203050038150119400400c005000f40200d908210080d2816000804114115034a8103418400107000074182402800120000c24481c1c1c14908014000d03400e0402c528901c0d03000700c0041054803803829400c5d04694005a50064030400da0401d03460480c00c551000b0740641c01c00303a680c2d120318213802c80b00049078088070503584c0c032000d2400110181c0300780540c058030a01e003d20ac80c2035900702a500ca9908212100212480d55555001a440d910000e90f505e40110b03079184010001e068050068550101490080d04c07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 89267383 1250 89266133 89266153
    0x11412010302040504030908100f0608151b042102030111250206040803030f060114090105031b070b0a02030a050f091c02030d02071115040506120403020a0f060b0a08 73
    0x204051414071000e0310603500c92001c101454010214480a4100241a00e901e02035040d050b401501028484100c02c40c40d26000144109002c2081205100f502185600e161554158048075104203144846020000c0000041560f00015581d566803120701d9034014425050040508550000d046111040810860040503181c0c4280150008156448009003140640041342c043e0140350410641c81c4000020710502d000306071851441154243d80311b0400e03880c0c21403030b500e0718080d800300b103802300b14144049030003952448100f40200505080d51420071040c0c0c1c88000c0088000d94404007150350010501030241c0b1a8001c1d541e2040204000c4c1501d42841509659101c136511404169010300718940060180300740215040d8500189040d5211a45810b25404030380004010905c15800e040c1e10344410320b0104140c50885100409140c03d0000307442c00d10404400090048003140949040d410021308500140d001c41d034041d0308005601c025130002d01c407480c0d10341e411014107036101c0350000e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 89268633 1250 89267383 89267407
    0x6090803040b0a1e0c0b060a150509030307080406050a1b0b04060b0a08010e1f050c030106120b0301020d0b090f0606090f03071502030a0215011208070519050102090114 74
    0x100c0031a0100d030716890b036490f0091401c4800c00e805072080b12514810301000c2410551100030114021701407402420345456170340070403041501d18402c002a14400b40038441e8418040d0020f445170b101c020381501d00e440ca1694650451b83c4c401c1d000003000ca040400c1114080360301010200c0c101035003044c0c1034042465620350b2000804001d00040c0507075129855072025498010080300100503070310083c09031001038021180c44004490796400703070789440400000d0343e8603030740a40e43c0103402000d5240e02d0740c0d0809004440340b00f409410321311110380310442d20301300303480c01d100401d03031030007179080000c0c00c40c00030020040c94807009001c0702085440c000078000f20ba55514201c0c0e42ca15000c071240d03000300e542d440109051620350750000d10a51051498803c0083c0c02000416000c01c40e5401e407034403101188000908480280112900c004500c2c094100048010000701070b0b95000d54125100c444a000008411003100c50003100d090b50041401c4045503040803816404007100720341c00c3e0070f0031220005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 89269883 1250 89268633 89268637
    0x1902090a0302060f07050d020106060216050901060806030a080406080105010306050306060102070603050a0b2707020a1104052e03030f1b02040515090c0a020c06070b180705030d02061006090803 85
    0xb0f8810400020405202e041d50b0303040707420700380d1700505032651140c405070003a0003012a849014054020800f226841020350314414050342d07801802e120040e4240a022504541d0007000180c0610441903407a0200d00488068402000e4a69464659604100006080e2401903228501940c014400d00c445a83c0114002c400d90b05185800500b55030b0300003000c00078080c241c008942080041c0406480c1070000f890a40361407510400290150721103090403640c0d007040e0480640300000d064401d840798640380d0051a002000c901d525195a04041c83e030340008443c0340200b140c892000c00040040582140d007800c21050740d401c00030324006103184813107071001c002000288140da4402c0001e03031248500c103004e6448203020b000c0600d28645900d405005d680042c1c04540503206001200c10710349807000442d507079180d00040c4840c0644070004103d900d15007601d044c2815026920004c50661403c0204c120720620b0740e4018285810008152410510b03030740c10502c10071489240174469000c000013 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 89271133 1250 89269883 89269889
    0x100902030a1a1e010605032a0f18030c01090324052503050919060f020f0c01050a050103080a0806030c1306030b130305090607050c0414071205040b0105010e011b0b1902090a 76
    0x2511040000123582d5410100303900001c00c8803080000c59070b44541880708010340980744c20b00784041c8180a10708109561394443c5020a8006904204140000386032807071410072402c0750b10905240000c5505204c015500c1c00c07900b000c40402e101c800054040e030344040c0d04005000c2c50508000314104014040d031501d09100c80082a01c542c410500b00300401a88504017400c0711050440d16482d043c40a0386c250b901000070301655600708804901622050300c030740b504803035200203880e15140c4c004100b03079000040280582c0d4540079000c5014400d03117955032043c521700810740e0300084080c110701c0c002c00480360281000c2c0645a1920803d0f000a81180407a5800a4212000381d00c1e1295858000d10b04501c6005080d0003d00380b06100340d8103e034006103075014111071340b5128046050380480004450341102d001e444904083c00412055000709008545006e040c5000c0d0780e401229030100c40065214181141e140c40c0c1c48c000c11001c41d5601c0e000d80b00a0380300310070030761501d4051000101120b200b80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 89272383 1250 89271133 89271151
    0xb0409030e01050a090b0c03040f06020706120b19030501050610090e010e190906020406080610080a110c0102030405030a0206161211041502070807060306030203100902030a1a1e01060503 82
    0xb03604c01e07454003c2c10110300a0106182e207958808038a0b69a54032604a0700c102c811000001c480812000d00111311003007900c00903680c000241200c0620b5070040d1404031700154005800180144250304410040b002960081001045504001d4188007070030392003500c4001040015082030254541d00204d103411250f01c83d403c000c003130300c0700100034114030b00303002070078006919010403141084039540213001200c0140e03c035a1180c1e51003105105a4081600d00880082e0400000854a040d40c4d44100d40e41410300007424200a086481a82240e1007a202940ca9030300100c0c10880c016810040c0a030300c03400c4650140000e01211402501d50a8020a020105616440d440021014020030b03a8010065010b664111010422020b902c070021401800103a016004001c15103a01030302490080b294041c004140701d2019042c064010403424101301e906000700c2001c1c4000c1150390200d007800da04034885010540c02c2078001014480c01e00d185a107521440c05004111040c1c000c001d490b0f002c40d0311 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 89273633 1250 89272383 89272387
    0x30318030c030b15030604030804061a030a0213020f1c0606110a030302072d110f13090804030206270324091005010f0504050603031315050708031305010b0409030e0105 74
    0x1410407220f90008151303180c2500ca0b8900304030501d0f5101042c41d0007940282810014540107112613544240c1128889426600c06020302005040c4082240f0468105000050600c180507818040540c012041126039801c0105440c006407600e100d68030052906080695000d800311000540305c02d039038a0080c09065001c81c180e818040100d0103284004100181d4a000f54504107800c56044580c0405450000c40c00302c0500c020300b000000c1d810100001004500c1070f80c0c200203040e01a2060100441d2804814000000107881d244040d04081402400b4a012981c0c1c280780f5410407801c0c041e07001e1007940300c2d58000c0746144040210f5070244045a20300001507981e00701a601d0700a04049403140286050300004a01544403104003c0d2441103a0501c080e441d0081055075038003a5034240a40b0b1020070208101a800700300c904265080c2ca800d00d6410620745446214031500115031400c0800310200c1c0320020000d0a210710090220211410440342d011520300074440d601c1d04041d54144400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 89274883 1250 89273633 89273641
    0x4050405070b070602040806040311010c0e090606250302150907030c0e040204020c1515060906040b0c0a20012d080901090516062c010c0206040504050a06030318030c030b 75
    0x513135011140545450310460f4900d05080c54014840e401da880c0208407540b820314604a000d10540705101b1008000300504100d448000c01c11071140e01034000382d03100c40e0301c0c02c183c4869400c2411540007001d000342c0107014000350300700301e60002030401418002d01d41c010400c24400286c21107404010b48500c2d03a501014ad40d55840410024810401128034610680c4003c02c0c0d0540e166409038450b030a615860005100390605202c001c5c0981ca01660b40150244014070070742403c0c0c0003412070143c55004660305d44460713031210900080d103c8200c180760003114402e00c01c5560048409200c00007584120301d2880018450030359a5803030074201d5400c02c0400408a64541000d4211084c060b82000030b6460780c0c03124809410383c0340c10510640c0b02107041c0b542d8459510902403c07244003010006420b18a4203030b2100111403d800c516800c80c0d02013814440800e045d12544a0355100e0503401e100040c0305c42c2181406002d003800d00a07080300701c07420310f5000c1c03000401c0c41003450304a9038004c3e00403125071a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 89276133 1250 89274883 89274893
    0x20d080118020903060a0617150c0307091703070302070b0f1204260d050919110a17031803030a020d0e0d0b1003140c010816110102032404050405070b07 67
    0x2060741580ca9241c81504244806c122181d440641124108103c000c1c842c08511905500c8080c01e078200101e00c81044c0014000004a400a642c0322107685001c20002c0d0321808085220301020300a20482d030310108191003015010071408024000b401c1d216401d129164442100621a48440504150000020800b0040398030a000c901c501d640e0102e02294031401e040070440d0b04117403104c261050819020500101c0040b516000b00460400c00703882c00142500c0d0341da40c2d60b19543d040d5402c040d0604000a00c001c101d508544045c01c0711000c0e503aa40c43d040141c3c200d8510360b9100034800c1d001005000c1c2c2c0907400103484440360805007000403070340c544000003c1c2d80a1075a60003924011122040100740040c000c00502502d110349034a41080b1000c40500c1c0c0c1d41c0035001b0f40c05001c19850b40114510002d9940324900300d00440c40d04c8182e1590115045080e46c0040e10300c1050000c1071000044062402c000d0000c018205070b41c100114541a191141e48800922400c24a0340000400e041480 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 89277383 1250 89276133 89276137
    0x9090b0916090b041211060906091507080a05030403020c01083306041202090f0906040807020d0f030306050f0d1a1008070e04140c0f0112060f080304060807020d08011802 75
    0x44040040f5445a948240407103800f22254001c070341034202c00303240031340c2481c10700d09564210b040a440390303044c001c0c0d06051000500c0254908914034005000c00000902510018070b01086503940c3c2c144c0700d080910300686495803000803213040c404518100903402ca0150a001010126803000b8003003043c00046e0b01d900e030110308c100b81c0e401107400500814070001c019000010319109440380101980c44544c000d00000c07003034038203041541100011802003004c442c060442e11340010b100c580101d00941d0740d600f940c1029041280071030b8984034104160700d05810081c0105400b42c6a065038010f8642d141108500c9942045101a05500108071304402940c25100600841c00407554516256588031a5022048404072007c070b40e11000000300c0760021039020400003015000100d550031100c015100c0d64041c00441000c1c6503502000130714807032049401c1005000701c0b000780d40d43e5400c00303800828030b0000624000540d40000c0c1d0032414658005041d03811540580e980c44500c40885050401034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 89278633 1250 89277383 89277389
    0x5030a15030501020c06070906020703030c0312090b0f011517040c0e070203091005091309110607030305011403030306011b050307120e04140702030d2f0a09090b091609 74
    0x32102032000300400c201580202040110181111800e9642c444200d510402d10b0040c200182c020300c80420000780608501240070f4801d003042d0a035002c1038a100021541d0795041520002c041c0c0d0180b00c1101000e00000d0301424020b00d1b04042088499405000040c90b0291003544030a280c00260034484900d0450018088103040300036a0301300080c0c000c0d641e400440103e841038a071207400021050007842160a024000307003000300800c845804d614010030080c00140c8425850310320000f203550340d42000302a032a00c80e480c009403950401d409000514070300105940a94410001d10201c5e81c0c00180030702c1d10361141c10300800c4802a030301d440d034103602540c0001000d0100c050035416400e5040300d00814120000d41c2d0822290110310742c0b84c02d002206840b54401b58004120031000c0c01800d0b040310f80c110501d0800340a0480e0064046078800c0010314045c1d07075030807000c6941c01c0056031100090004001e003150511110a284000070b2880b04058000c401d04c41d005003034a1481d83c012102c0c4401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 89279883 1250 89278633 89278661
    0xc0c0b09070902030f010f0f1503180501060b0406030b0603010302090c0309190605090c010c17090f0a0902030601080a0c080106030207021f0e01020f0f0601151b0c050f01020f0c0105030a 82
    0x100e08081703068101e071810a01a14030f004000360b1010803404925040340701280c000e82c0341e64114006141d41900100030709900c03885800407105146c800700302d00340500c0c03005148402d580d607600c03480d0400041c00c640481003410b1003864200010000350366000281904080c807c1c0440d950303030b01c840103154a8401d060482c06c0c01e0400b0b090380d03502030001c0380e40054402c40004042d180118807101c01110090320148004100312100c1d4190021075181d0000303404080c50107000d40d881c00c0e01c60000624895556481680b03100c0c0c0000401410717580c018038403500103034100c03c10f00a024030880d01420101e81405150304040c1c2c0400e800007035598211812810084692010b0501084800028020f0703035048081805449a400010007510b800a5140c859003511005800103034240380b0760341021000446030604119003008040c014207070740e14000c804e0034400c01e4001016817503c000d0101c2d0000d60440a815034210000300909800003083c2c01c103849000740307800c0f07039030341c1d030392040e180042a8460038412 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 89281133 1250 89279883 89279887
    0x1e1602010b0619030209031515040b04090b07030b0a030b01080105091204030308070c0204060306053124020415030b03160b0703200d11010b120a0b1b0a030902040c02010c0c0b09070902 81
    0xc821000b84c84400e140354082e42d0038032800c0485801c0c0010744248dd03800030001c603088000550054444c1d030045a2061008211145065590701c03210881c401c2078001045a0355030f0414440d1091081142e40304c58880c2c1003405003014030b1510b0140002a0051400061282c00000402103580d113a100b50055a4003032000c1199042c40140304808900d803000c614400d9110002040c840803041e50b0007400b00d80d01c5106607a000c0c2c5c20b1884613150101c05c1000c452521303002d2201242d120191034401d2030034502994002500303c44e1104041c03800c003c2181c2001040e0030350400b40428100c3c0c00444481d507405050a01c0c00d0304810402920b00004030202e0b41d03041c00780c84040d4a1140e4012081780c2841b401000902070522401e00f0880348440e01d0001e1501c6074040c20300d06d80060010700c062984203500d18418040c0304125070f05e1140c00e034808c0100600181d901c0d0042c100310701c0c02d0322821144041c42d00c000c00404d2841c038000b40003c554840c020340907801d075600251250720300300822070107400d0b20364040d9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 89282383 1250 89281133 89281141
    0x80705011506030b030c0f040b0a03030c0c050628120e0102041701020a02070e090a02040c0e1008090601180f020703030510081b01081e1602010b06190302090315 71
    0x50080451840103510140801c400003405032007806008a1010018050035005a46a0810491403245440140c10544403c1150016603940d000080154025141c02035159207034075064504a0b09600070a10482042c0038081c0c580302041601080780707013042d000c5010664030308000d0f1484d14800e0a4150341904002e10818904019005841241e80500ca5031500a82500e89035003030340106102e010050303024480401c2904d004100b6580c00a0544c01036a43c0c1c01d40e90780108050390300441842010900c0c414043c052803c05808015026001c3d181c4030700c4c81c0c10100409a03c4070818880e010251060049201000003650b00484040142e046c0c215582c0e0180c1c50081d001c1e0104690001c80c08a0301c410000d00c140c0d0100d0030f0251500410300c059444d000f50001960ac0c00400b4010702196003c4011403042d600c0202039050083c071010907810f05c0c62120401c002d0035039507043d00c114081c1c1c6050000c0d0b900c21400340f42440355412039040150b12541e9a00100c1d1400c00051507108092042c00144 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 89283633 1250 89282383 89282393
    0x2130908091005090d0215130e071b03201002030f150604030b010306020f0702040e01150909050604200a0603020c100c0c0204050c0405040c0509090106020c0d1502070807 75
    0x2003034401c034203a641d16503840700c00b04103603030501400c2c8905070040750703c00144005142803e05d801940506000030ba0a010380340e08c0b203e60141c8980c200c1000c07082064113024407190402d200c500300090b01c809030706206440d581c006010a090040c07500e51807102c0d19842041d68410b124541581c501498210344078640040c41410026040d41c0400403440e4403c01c0070698144042200c0559801240e08a0180d2942d80c4c0c0c14000d5114644080003000c040c0612070060340ca5005404070745010000200d030902d074921540080390116400380e80c10501c1e1220081c001a804580294055006041008e400d203050221039400040c00b600c45602203551240441c18a8142d4050910400c0c02c00c1140d401c000c42c50102411100e996030214040745d12048140014503003a040130340c0c41031042c0511414650380e03034082010f03200b000f006407000c40c402045265840c24040c951500514991004012500d2a540411054031000c40040c1a000c54200c808040604680455008540c080b01e0155114040c0c186 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 89284883 1250 89283633 89283637
    0x615032315151311160c0501030219120b04060306020d0515150903070e09060405010e06010501080a0902030a1e0b090303041101050d0e03070c0305010e0705011e02010908030a0b010f03020a051602130908 89
    0x450b41c4206d004004980340d4801d200782d4032580400300b02c044903140402010b031000c140c0b890450402035200c1c00942d80341c0e00d603030203018029480383c040503031280b01580c03010040c0c9200034039010314401c00d150036501c1660345090b42ea90710b4030007003841a5905840000300c1d042c111950131513590a40754400b07000c810000041c09030720450203500208030000c912120a919074201707200e51400154100081803c1003226407141d20b006100604880b030200042c2d4400a5403e18035038580381c10903224020704248072200480c281c0c0055000003941c55840c1954508584a40f611640c1d03040050100352520400e010780c2c020141c0c503520791f08894642016182110202c00c890004503071550800044180e1081d00140003015a00c0585841401c200790007032007a00149600641c1b1300b10764031001c03510007083e1507000540c09503014260108150b903142c0009080345d1440d1000c2c20425104004008030244d00c10280d4000d8400c2d850101010406800010109030440ca441d401d0603151400d1002008a01c1c40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 89286133 1250 89284883 89284927
    0x5010303022104030b0103031103070c09050613090503030103062016110d0308060111010f0e030909100b0f071110020607020607050c0304030615032315151311 70
    0x80d503114680e0b01020580c0180c052880000c00820400c0c00520009001d00c0b68400d00c803030010216402d100745a1101d000b4141654440c403501c59840f4140b014074100655503c2d05d010960a061004601c140c0d10950342c0e100500c006001c0e2941c640c0420640600d40109891118600320016214600c0d01c0c50588060124842110032180d0f00441222504200158036070254240c3c81c1d030030540e51104019108004260440401d9540c2d40315101550310b00b0f48200303807205000b4401180c95003072010601840301c801515062010511035810000111a6011581c034020681702e0365403203001c0c43c642182d0740410801001c3d80708641701807007140b07240d0028500f441031110354212050358035440c00c00c0d5070038890b03504002004d4200304001d001060b465081502e0551107810741103401603907070711500a0391100c00b182c54a8000410050a0075006c00c102e0301100141d007004510750360804440c040c04a4543c590000e0007421760b20400c00b190151613200c15a0802103c01da21b599582c0c214440320410394a00f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 89287383 1250 89286133 89286163
    0x40e0714040e0a06090b0108060f01030e16051002010b060a0302070206090a06050304020f0603330607030504030b061f0c0f080c010b0102010f020f0306010c0c051504080c010e130f09060501030302 86
    0xc0400140780d00c886c0100240004113850303992158841500b40303e070b0b640c1c28507089818036445103445001400304005e1800d41611031080504076038284000c1048800710703421030504681c1000c020451540d2503104840b07040d0f031035050040c0d0b1007500c1d101285040c00350030a01c0c1e41c01601021300190160704800154465442114440d045c4c0c0715540c20030020340410360b030310700c1300902c5001c00c0700309031880d24024084203420307240704c21505414000007401d0b580010000c90000c5c00100d8200100081503040d6a08204111a80c01c60000d000400200d2583c80010000c104000c0090410a0050b00000f5000081e04a0580f07a540c00c0710602d5513028001442c460380c01581b03084607811640c0018400d07141c00520701c1003580d00d907031151401120014000107003614904c1100c440025155a9101c0700d01031808002d070019100c9152002a40c1007800d021007032414031200c41c04200705a980e08600030b92165181c000020301c80d810960303076801062181002403440389020000300a01d500052451324080c015 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 89288633 1250 89287383 89287391
    0x7030501180618150305010533030c010302030406020c070902130e0114060a0915030c0e1206010303031509090c0f0f0305030904090f12090503071a040e0714040e0a 72
    0x40407140089580c18401c2e400702c00c000e41c184001c07444075074015138071140403040211111620781d210203084503010b031103800140d000d100303c94100f0300d00340016600101181e03000480d00c1c03103003a0100c0d4075000d0611203281010750000015040007490740c15180d800412400f19590b40d41c072590681d009602c030a1034020294800b4000041034002000903906841c0d6001c480c04c0005d5450080c05441e40121a0741003d0180882d07020501071524450506103c40668012070507802c0402c0107800e404080c1c00307540c010302070400d200f5818034000a8603411030b80e16207000190070056219028960cc03041c2c200494140c10290f4560034413240c1e0780c04900750343e001501e02e12841c5e07440101104200d1039210080c820b4100703022a456514150344000c0b100381c00b480c024040c4080c1a40c9203080e8a42c0f460940000c108400c0050049041c2041000c0141c190481440c089558118046103140642d20a10461821b444e00141006105190800b403c010107003240d911162111901e0249410450b84141d0441c0b038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 89289883 1250 89288633 89288669
    0xc120405060105120f12090a120309050901140108040308060102013c06030c060302030417040801050906070509060409050907050301020a09060305090a030f080406140c0909090105090705090a1407030501 89
    0x2c941d41e800c1c00003040c002c3c20820030726404051b054004200083e400201c00b100001c0e4145036061007060244a60f4549800324148400c002d90224103800884803800e42c1d0f0303003141c06030740c001031559003054042c00c0c0381009a903500c004034050308400b00780e205c1001407040340d10b811700d1014110b03603252244446000110640840328504880301807201074420a1007900c101b11480c0658011070300b150040a0903000a8802c440e00303103144d48280c0c08a01d0b030745c0d518410040444024080d19800180524119140c45c0c1100c0000c0c0b103a01480c0100e029641d6564046241c01100304101002004040c0095440d48840740024285461622400c80803d0402c00000c40440000c622100702e1649521403040c4084160000c40b00307000010070031141c860395220400c0d03000c005664035502c13450b44c82c0045603441d2401010b2180c9a000038100c5110307a03040a0522044550100e50386044e150f0941e0b80006641d0b036240404081c044540b5070381184552803092120389985900094140d41030b20204003542c0c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 89291133 1250 89289883 89289919
    0x20a09020c0f0f070b0708040e040c030b0a151502070801050403081602060903120a020904150618080604030309021903121b11060d0b030111030402120706090501080c120405060105 79
    0x5844009020f850304041c205024904c06140034203078990107a2881c50400781c4980d0640302d02081a20309071a1044024030800402030390724002a070012444a051000726110780d8103c00c40700c01030061564a0503800340311041039208102a000411003000248004e0905081c0030307100e000d0a6540c8408000394684141b4098000520345018030303103040c000c61034980d410f1503810480c1d801070f0209101a80811114607569940e0184460101c10361b501022020326040e009005900c00220003181a01501000c11902002140e400da006400d070401181519042c070005034200380d16102c040350500400310200c18030000c1680b841c00e20b90380e81c585811143e00d40756101c3c18041000170050104c0c400e1508d41845044c414064034542c440050040f40c55003144002070f095803129400701c04641c0012003000198078002402c0c5c0381001400002d820200c0c01d00c40001d0400341c10380521414803040070013051041f908032044030315013030503219040c6d610305091034240d454034028850781d407040714508208601c0300c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 89292383 1250 89291133 89291143
    0xa02130b2e020303240d02060a0801150f02030405060a03091a06030111030903070f05191b12030206040305130e010e0906061c0b06030a0501020f030a0e0a150b0d020a09020c0f 77
    0x15200d080102c014004801d0501c0000d0a004d4001484014200061321003002a0089c0780c42c548074890345e5070422070b40340c2510707021461004c10402c801c20808902e6801004a40584a05807101541c2c1c04800c5410f41c09848041001495000442c0200e42e1204400301c00c1170003141c1c00c4009008450b100d80e0001000e0100740c40780d500ca41c0041115000082011a81c0501c2a101d0010748040d0030500c01c407103c6211200006443d80000043c003806554482e1800a02910780038512211524080e100255182e80091008061150024002010752040e0426200810a00c40403014960b150080846461300640d146012845a407001c03c0307151a10651907500c0a181c0c1010b1200e081d91070719003100580020380050b825028030341ca0400410001e000074010302401c46c1505035241002041202195441100c41880d0b400801d52840080c00c20404503001c00080071007c586150b00a0004060080b500f03c000d5120701084000600382003650080c01d0780002c1e1000b40c4012080301524903440f5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 89293633 1250 89292383 89292391
    0xb090304030804090911101706030d0503011a090d03050a0305060a05030303160c0507060f09060206070e090a0b18060a0902210403020304080106030b01051e01020a02130b2e020303 79
    0x1030040c0f0060081003580d50100c4c0e21a07000b94200d104112107903000c06c01800c000c0524600283d040b0f84e4404084490084550304503a040d0010000242c41110040c15800306025400d950032030f4220b00c01d4101503240940340c0d010001089400f00684034a4081c0c01c0d50b100c0452200840d0030b000c000352051411100510440f1406000356286a4807406110880d20f81e400c1c01800b03000ea580e009802217134040141e07401034070f05a02e482d580032042c003030040e03d81300c2541d0152045612240030403003000c0d0b22036582c881001081d5103005403a00c1d000d0a41010b0b090310030b13031103400040b10080c800550301c0c0c90f44a035005020648003c4d50080c1c9940000c803e0307115a18540c080040741291051078242c1c83c0c90f02d03d620500920641c0d083c01e071695070040c07e58015038000d0310b2151005005004921b401c1d599181d03030319500c1510b90484408100043e48900310000042e1081a4030002c051503207109405c90014460002d2589254100d0101c0b0400c0c06d64115003c2141c01c5a006280c02203640004112401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 89294883 1250 89293633 89293643
    0x18160306050607050706030b03030f0c070302030f16120201090803031f06020c03060c1e0301030f060b01111e03040f06020318010206060901091a06071406090d2c19030b09030403 78
    0xc40c40c20980182c0c0078004400c8c00c160184801c100410280301c618000c0c0011502460140540e5403550040501d00404803100500e42d802c0101954581d50400e405a8103c420003008040d20091600040e01c900509601c400f1032030100004000900c0d4400c42481b1205140441da042480d4640d04100d1b5603160351440b203a05a8808008030341c0e6000380c800500450080c3d640104a0032400308069800c0750821791046880304805040402042850701400c0c2c1c000d5002c2c0b815491402c10307100c50b183d0700c02c50040e122504140345080490489010b20440b4090051850710049840e502d0000035600da114544018070788880c280d215406610115500703000d480c00502c0d800c110307401d140785200100ba00c44600c1030720300d2042030780000f036490b141c0141c50468000d02c0110014901d602c080b60400400800851880c3c220f411444425600703c264610729840e0304107044890030b5600700d40e00c12400560303005544421034400d40c5443c6504601f01109480c4611000f05050304c0726900156640500e0100800e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 89296133 1250 89294883 89294893
    0x2060711030a2001110c0604060c05090d15110c0a03020c09010608060603070c0b0705041e03170c0106051f110105070906030f02190305011a04030203060a05061816030605060705 78
    0xc1c100c0030102c0f0b035a0240c00b40000080007030700110010840e0344800c80c600729680120b8101b006114591203050002201c0d81051131520885c100000e40848000c1401443c2e80c8502103030b078500a080da030050200c0c0d10051602507990200580c01c81d40c030444500c08034014480e10101102c9c0d4185100d260741240c0c3c180c0c54105181d00c441c01000307160b40000340072104000102c440310003c2030300074001c0b038001e19454581c82e0350713282004400caa105000d081800c410b084104405c10001d0680034000c0d000c1c0a00f000055191540410b95502420595003c0790b070040b0b007103070704071445c0065902007680c100b111744075180d480780070780c1a290070b031001180c01c0d10110341020400c128590198202c00864042b10a0051501740c4040701c03042c0c0c1018403420b0f4800a5913500050248000ca100080901045071315040d040c985980d000a81d0f0380401005c1d0b1602e6510317040480d00540314010314400700c1c081d40c07060104034544050f00b00300aa01c210b680c030001a050010014140c03c0c040112451190002c01400f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 89297383 1250 89296133 89296157
    0x9080306040e01020906090405040305130603050f1317030711061510091202012115150c0c0b0c01020c1207020f0103060b0a1815030609050c04050901030f0f0204050702060711030a 79
    0x110027400700070030139024003404001c2502c680304d4079800350000c0c00345620001018105000c0210341c3c03010080c598002a00e1070881040400c03611060307040d122180780c2043c0d940c0d50710130004454a600c0404454141e108907018800090459180702004e00801d850701c840540c07907904203d41c4c10015200350003000c1801045100075501c165003c01e0070140c500b060740301d0100900b004500b00d84901c2445403100601c0e100520213194030354101c0c0744e1130a1381e280c01d1000800d291151031511a035441508a00d1100080480416100790140c41503511010141c44070043c8a40100141c0c0e070041508910a4900c0344e2544032035802031040c2c00a6400d000201400e10308458070079115520a039911000070000110300080320030300e104400001500c01c2d1f40100d8240d1428001d01c0981d44003801000e910401880140904d03221f4812042c110385d00100000111211342c10010b0340b1840307800e80a90002d0500d0208150181c000501600569103580c8206c2100f000e003c5058580c05880a11030001e01a00702c40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 89298633 1250 89297383 89297389
    0xd030506060a0e06070f0308070207060207080309010c0c08031614030f0a0513050901080a0204060902120c0a030908040b0c0606040501030816020301060503030706090b010803130e0702010f09080306040e0102090609 94
    0x39590f240b034050511440c0c0f9280382c03600303800c030034030038034202c0008000c60100000c1560600030305005200c40d0005000d051704010320a5120301074592004c0c10000c50001d80000d00c03c800094000901c0421b09680d40e030701d0030a507600d04c03140043e0400c1d1030384446520181e001890000c212120440d480e1902824510504000c13155a0b00c070841c101d1080d400c1410110307441e542c84c09407a00901c5014001c0150344003a2050000742c603034aa002628262060058107511800042283d034032072102c80d800f40d6074070700e02e4200390002d0088410251407444042400304000e01c0c010b0040000750701c240100c840541e291030411013600c0007404000d000c54403c0c01000082044400001e40d00348c80240042070042e2114042882d5821002e030550300d02780c644072503c0c1801418540f69015003a0300700518540f41e0302a60480380311006100c0c01030215488000101a03c0c800e5225140c0040050700130300c0441190305240c01e1a8000351440c900c1589040c0300d800b49120b05108030340c0080c2c8054038aa080900060070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 89299883 1250 89298633 89298647
    0x6030d0e010912031707090914040b04350702042904050c0c0a05100c090e13030e041a0a092018060d051f06050d0c02010608010c030501080d030506060a 67
    0x3c00c5007880b485215003c01e510a61440700e205030110356802d90301a141c4048102990343d641e600c0c5144600700d43c1800702050b505003d8035801608480c2034030408458451342202e40d50103408810001114208c1e50203445400b04c020b00c4201d000f201d0031b00040200c00032800003100e800340080a00381044032440004d003025046207074080d00c074001450920851a00306404c01001c01d800721400d800586044168038503602c84c42c400101e003480c0a00c686400c0c040748500155000e0031a040748506005044100740c440c034a400440d4130058000d000d05001d040c0c1c04030b404143c208101c0e20914650308042540d500034403502c1d001c14a107406c2d0990000454106041d260b110703484141c803903d080907030440c01c1e07100c100041c540841d400034001244e1800303039113071035102ca070800d1410900040003004100580d0b2100903150201c03041c03039000854080410080e07004010945c44a0036a500b421200141c0315050f078000c504861402d0b003a40d00c0b408030740070b048045030380807940264080018404540310b03502c2400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 89301133 1250 89299883 89299919
    0xe06010c080d020406080a1406060d0b060717070327140a0305070e0103120203030105060703030b0315010828030921150203012603030a09030912080306030d0e0109 72
    0x41038504051103080ba001e9074081e0b0007440208a9076010b020f04540741e849034031401c1400101c003926a06000000580e0791141141c0e0113002922421001126510041182d4509030310014134407621040d500300c0d06107a00404019408940600c1000c1032110b50f500395400040001100c0d4041c0600700000030801440290a440e0010440c1c03102000055040060501501c04a000c04407590b2441c6804440d00010300380031001c5400a000401141e140c01d015a6009549410081141381c0044082442c20340590031406550031048000078004d10040303501c8501e150083d400d50101c4006001c10f07004101e075203000800180ca011000c02c0035000d003540000a614810100c5c0d44e41400703a4844a201c01b901680080d0413a50001c010440360200a40c031840c0f07070f010003100c44041c8084054480d16408000c181e03408854403480d1100030140f0508441000d010001100503140c9964180400c0c01d8008482c2180a840358400909040e40030f50709898080b00143e480010301424a5691401d0410001c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 89302383 1250 89301133 89301143
    0x80f06060d091b150905010e0d05010f0f0c030b0102010b0a0603020c15011d0a0b0d06021b16090c050c062406070b070e0f180705130602010905060606040e06010c 71
    0xc50074030000318221520411183c03502c40400500d42018180141481100d403240180a03254600f00020f0b40c00c117606c3c608410046646038103280c070504050303000d8180440c50b1120b5910707000c0300c111203a100364005802d001180d60108010700c548401a402ca400c3d000101e070744a06525800c00070184650001c186080382c000607103800c040d1141e18030b12075039000e0700a80c5481c0862000e03054100e000203518ad50080310101c0c24060702e5002d402003a035010643c603029003010780010f800081c1341c0c1400c01c480c0600c601d800440e134405800d0141e00c02006032901521050a0814000040d42c41c42031003a5105c981c80c20020300303025151180301d100c80b032101595001d07100501c1e01400c4082e40d1010b01401000d40150709c0704442d4079000b0f100811081001b4580c0b80f2030303184403411030003c2d1104121039031500491f002c6901a40c48080e0b080e04c80c3c1c040c00160145250040401085d19a07045d00640c1106120f003040310a1902e0703000800205018600400b010403040d08005416581720f45030455050f4060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 89303633 1250 89302383 89302391
    0x1406090906010c0b0405060f0a060501050706110903030d0e10020a0212090409150905010c03060b0403110d0602042903150d030905030102130f08010e0c090717010311010f080f06060d 80
    0xc0c2d44e0b1a581c022080b2015501c5400c074408100201700b00c1e00c14280c0c0041d04c558104003650800001034014090000b014081c1c1d036981d103882c9010f0032250201c4001810007000c481d264106c0141d080e01030001400c060a15020304072254040b24100d00030390b05110503907000b4090700c04050350001142c1d0010648150301c20384402491000c54070402c050301c0e498a89400120301800b0500381b10b400d6a100b40822410140340203130420612002405441c1521780c000a4074170000402d4000400304e14401e60040c056500c0081c0014440c1c21382403450305003c0700000400c2c8007541d648107401c1c40f030104a60301c28084d201e003080e8248a01e00143c070406218031a05121407619180c10200e42280c20130061b01c00a118641801c1c0800240c1c066032800404044000f80503184c1d440d01c0480c0c44611406156014914090124185d103016003124403020500c4280c02c1c800e50380d40e04107244032500800c2030030701003503003400c1a5001900c1100e8040c422801e040e0b0f8008240c54440c28440e09078844000b81e42c0c00f59403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 89304883 1250 89303633 89303657
    0x5040e2a040501031202010c0c170705120d020903120a0905151b0d1701080a030516060e07030b060d020a0605030a0207060203010905160512010e0711030c01050f01140609090601 78
    0x25074442c281c003950141c000c00f41504a032110103421181c2800001040c80380b84c1081d2000900040340c4200c101c008909071704e03254070031071034010714043c0303581d0500102c03481c0419010a01081036025040c00c000407030413104200c42e0b0f40b02c0005140302d01c0b418440002da42c20014031650615a0b2107001107403000c0300191619104420122020704079800d41005a0170940ca86031504e54801210394000c02d0259141c0c04951411500700c1d034948281070002c0c00e00001050762042615113401e2680c107140c20881c00d01032814070340c4001d912015a4001100e40e0721014000c1501c0f400c010a00f00e402907400340540c2600d900b08402520f198000811020100b03030208820000541c03a800918003d0958890214403030818101800312041e0f02c040403810000240950121000c280e200d450441d01d0f14281c00d405501d454000b15522030110f005aa0644400a50018680d105512044c454146042400c440381d0f2107080607050003071000021580044144050003591a2511406402c0b82c0c0c14180080d0001d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 89306133 1250 89304883 89304889
    0x51e0a09030e130504110f060d0903020c060309030408060714071709041e0b090402032802090403020c0909030a0c06151203020a0302250605070f17040f05040e2a 71
    0x30143c960b0340800c0d1540c051004006a5401c158144d01e01110005080203415010400714000c007400f40070040e40742c10060080c0340c02480803503600b120240c400c88c0d070383c034002c442d41c4d0741d82e445482040d41a01c200c00015050900c5503800a00188a2030600351808005440b54003800c94091210017200c0030412000419665511810312883c404000c240c82c10302c9144011022100780c0c15070fa03802107041d8410000142e8010880b801d4082c8110004d07034072465003503440f03501441c00c0f500094000c1e900030280701c10f260700003509003181c010495802010360b803101e8200c0d8590103040d41c0c40e008a1049a03800000641c00e4000540e620140c2024002d1503a490356240020b1206030410307070150304840d03000010f056040c080e65028928402141c2c03002141c80d02101d42c05072952240c18100500420a030040007800b03c0b0040d503090300b0281c088441daa4099001d001c1d540213101c0c18420f1024004001024101400b551813512200c0300901413124241f000303589071546010009503010030404088581e69 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 89307383 1250 89306133 89306149
    0x9020309100c030b030c0306270c130f0506010908100e030c01060e0603060c04030803040320011a030d0804051002030402011103030406060f1e06030c0c020406150201051e0a09030e 79
    0x2070b409a81c0840c51100c100c060500308049102600d0290b00580200301d5102451a900800706c04195404424103806009082c00c050200300640d41c02102540d610034911000e03002400e0b52400328004101c55124031005541c8842da6206023441a00549000f50440e4003035405400081d1040c0150f0307181254001509003101e850703800a000380010320702809101e080810081ea4020560020145000d0075a1548212400000c10040801040000010000e420a031024002221a900070f001c0b00d14001215180d0120084980d80248560055682810311034141140100e0b081000740040c04030040070a0080e40c4001e105178180410800c0c44480c0b82010001544118018140021410304201c55a0b922074001d601200424030220000f00000c042c00003100c044802030b080c0000c0001103003506641c15441030b000a5841450441c0010f148a03440120000700c18490340200510740ea883c40d1041c0c40b1074200310140c40504031600084160420f0b5001c440e4444c040e0408441c5c48070f225000030100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 89308633 1250 89307383 89307401
    0x1f090b041a0705130306051005060705070503010b01020d12090201050c03030103060e011a0f040b040605060a0e0f24090a09050921040612020d02070b071808070f0902030910 76
    0x58041e00100041c40a111990642c000c59149041443c040b040008103a200c6082d00010b00420b9460300803c40b66102c08e1691002050090801a00c0784098104240c40300d80350b00c5128069420301d04460ba0317540c40800c00b10703089a45919a1403c22a0348400c00c0001d00e8544400c074188942080000103d40080000e94025480fa081c086110b0802e02c0c0b41c0c9003560b904080856100c0d40406400350f00c1e5950394103071401c1d00001c1c0c030001815007105002502420343c41c1d001c1ca41004000484c2c03010160302c031042e1030400e203080d1004001ca0b44901e0501c0302e07451203040c02d924001420b400c0c0b00c5045100303400820243d48c2c010581d0300c0c030940721030a00c000c5a00a5510075403e40c0403410010905400d108000011202d000c078890034540303040b5000d0003030f0f80e8600c088000b0680c00146200920440d606940070241c200d08891400c1c5040e0344060616001011001c0c8400290300300022103520006214003030325802205a8a01c3d4500090200030750800340044005004143c50041503c0d450b210300c141c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 89309883 1250 89308633 89308643
    0x20d09091d1207030f02031908150406090b040501050a151b0606090516020f031905040b070602030609090304180504051e071d060303070809011b0c090f0c021f090b04 73
    0x2e504030514000d1315502c0c4420200e804d41d0000d0104154040e21000449045801d60401c500203a44107680f2205115079030006d181d2050ce85200440c0e003400c4c0794001401d444054404000917601da00800c0801861482440d5200c0300d44618061554032400031841c11170704844521201a0050342c4002c1070750116001855803643e144200840e510541e400440745900b107002500c1d01640103401c06459228142005000b86445603451900398454012039000746240310f8904d880d0459031800300065441a20118480c213008008038a050901100700c40840e8220710100001d03180040c0c400014100c014400d40b454020b0f61101001080103640d01c51030b03c00900302070080030b030074090901405448040c1203240b0061003410040961800421254850341000403c0d454450400048602c240174011562083c685145071108110b040752f12902540c8036202d09101e5210307842c8a07070044a40c2d0f20102801a4050110009410b402d015034803840c40f100c21020485962070707104d0560320401039508480c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 89311133 1250 89309883 89309887
    0x120602070b0a0209100e0d05060c0301060e0a0b04090f0209060a020f011b0e060d020c030c0706030609020f07021318051c030905030f133201020d09091d12 68
    0x100540059107660010703021404500b00a1144040744544103084030000900004c1c408141381c1e40c7d00e4801a0502980c04811511145040036140405801c280b06840104103407c4c00b0841c83d2401d92107881c203460712021010304207458045810003609003e4070250340381d0350800015050b07803140c00041c18410710640041203500c918046290864a915031a111a034900f402529016a485000580052403c5a400313440300c2c40624039200900c90f03000f040900d48400550104000000300300d80381107940d152020041c00e9502c00901c420b074442c1c0c04401c01842c404202c140300502e4103072025054034016040014004030040080c80c05848003410030350f410f501842881440f018404481d442c3c142151400b4481d1000e07d035100e070360301d00900281540d5400c2c045160442000400314120090844004001700a410890302d800c2a410154030940c0c403191107442c1039615400054410148000c0741c1d2400365840c075101e04c0f0b10042041920050b00f81504203800760f04040d04019941c8002800c90850f0317 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 89312383 1250 89311133 89311147
    0x80307030b10030504031202090607020105030618040309170303011412071703071416031211060f0405060f060f010e0112090305091807020c091807080304060311040311010315120602 80
    0x3130310140d1f041c101d80c80c00c01d00420903917541d51114403d48844960a007096501c03a100d400000704881c0011020702e2180d0f48503010001413650000303900e4216801803100d110280d407400001b646a210174012081c03c0e001c0721070420340781d0404002d490303000300704035054900b915200c02c941c00c0101140308245049510105100b0180300480c40140c6ca102c0b210801801d5864030014003210000517484050400c06200c4109003c20703014140f8545507041040031703500145080301da005840d080a54003170f29144940d00014410108484205001c0c402c000e10049161a040004581c401d800c80903103410044254008201c41465009a40c0094441e484440e00c2e40e040d8000d10804113900e51101c40c407012088140032031282c0108154181a5064402c1c035447d6a0f96090110780130300307861410300148030f880000124001d0203c0640140e41c1d05582c140181a200030b0302c0c034043d0140c2d00024021684040e1b100900750301035401841c80500705000c002219941c2e42c6c40e0b841d0308400c14420b41e1243e400180c60317 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 89313633 1250 89312383 89312387
    0xf1202010606181a070605130b07050915030718090203011a070f260c060403080901060308030f100509130c06032306010210020d09020f030316080307030b1003050403 73
    0x14601500c10b910700441e00c11480350286040a5103031103034a03c441c8908441a070000c07806812242c199401c45c0007030045061200d0703115060105e824090b00c2151074074010030b003424401c00c219024400c004003001f02485110803c0d181036840a41810144030850340c0683c500144a403010f0010203161000603101d41c0741c00c011520b41d10a00b2030441d1000410041440042d1022549000703036a007090883c1810303a50382c00c6500c500d61015410301c1211304085580c840100700014214400d078844d9541d984183c544911041c00c2c0c41c032034007004150001c00e0000400d0701d01d0721500664010204840b07a0a035564a001060440200b552480548051003410200b4854080340b2040100120700d000c001e4031005049001d65604a07035855186100d5580c00f1805682c801c0080c04600f4541920440d55168116071210080400e40c0f01280281992090344005180c04401d03039150060078419072003094429a140c81440d4402001c2000781952490407807103030f440f4a07003000080d404540f800696070500e4100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 89314883 1250 89313633 89313641
    0xe03010603140f01060e07030e0c0d0602070c05100e01050d0f05010e0f01080d1d01020a05060a0204090515091303020109051023040c2106050f06010801120b01030209130f120201 78
    0x1010090741c3c142101048560680307900039030701207c240740004105802018440c20842400f4213154410040c41c21141071100e1a402481598414408440b0b83da0303850042c0f07e0f120f0b0b00b141c904000f040b42d125a401e120b50152005001c0d01600700e0000400300c01400c100303012501c0a070003a140941c10201040900311074021101d006d07204080c0106400805114010044980101e003c00d510101c918070000c3d43c0d00800c524000c869200003551458605166664000e40080c400c0742002401c0001154091000c0014800070243c0a011205a035a44880d100c1903000003900440c115981d94449001090041c4081c642440c080800800c000c440c90507000030b004003c62052041c85814024400040c140c0c1a2000c100c5980e90300100754800b26940e281101d121a000242446080008002c0c200c0c201c0c841107449200240c035844402e0340c8401c84481c181007641002040108800c0c01840545054180b0b19402140300b020000b10604940d212841609810313411941604003c80a070305058083c06 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 89316133 1250 89314883 89314903
    0x17070203040812090303070b070e01021e070e090a0503030a0209011223070909021603030e06070905061605030a020601052b1203090c030c180e03190e0301060314 71
    0x100440c101070800c14010f48880c8104000642668001507201032601c060007907403401904241d91f201c0501d00040060800b0551001c1c441c014054102411900550100c0e890a2600600300502041c5d00b05031458020010190034070689119801030140000e100704000d602c50081540050b85424080001400c0362038000e00b4405018100b54a191041c2600c195010704500c080e113020360b454840c0c24082c0c0d40224190001c2180e80e000003080003150000c1030340c40000902c02c0d5820400b45040764000e07926490180c481e100000c460b0ba03820049442c001000d0b000101c83c0107901243c03178005555551942e40f060003014003603000b1500405c0320b071070039000c400c02d42c803103071400d40ba41c0c4960f40301c40d203001c105a01d20082803460035482800240303109500c0f5908a650106c91165015224140b02c00c046d6800e2007400b220780e2900c4240805070000c1d000d00d981d0320403444020f40c241032004201f05842120003107410100030036640620303060703982400780000550042ca082e504203d00c02106d60705080301c100c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 89317383 1250 89316133 89316137
    0x200a03060b032203030b030706200309031e0705060301060809070e0702030d02070c031a0115020120070201141b010501050405060303070b0705091e0120030d1d0105071707 75
    0x48104045010480142c0000c0050700280f0480c02c0d031245015001428070f01c1b40160544200079010860030f0b0031518400d0011091a403051030001460900c55880c130414440c8e61301074120482d1101c80180e8542922641c44094007601c5145440d1400300d4440e40090f808580015110801e00071041c0042c44401c0192943c8400e0000c14507029001030364a109a4050343d04030ba600080c01c0c010b05c07142c070190340f010315480b100030040c03e00290079603100c0320000e0180c1d410030755507910714441e11801441040d03100030748030300403c1d01e8a00d4a4680c0038580c0000c031082c0d040c48192400940f110a011000b0104e140c03140441c0c0704d0400a6400040c210391050300704c1c50040d0b18100902441d607500100b6100e10342d901c20384900c85c0b0340d0782180840d001d0003014540348c0c2000b14a006030700220404c50401d0704041081e620030300505100505981d0001a02c0240c000c1504100107281540003903400854007075003201846094107011900d8242114011902c20001810558140c00401141d0707101503040b0320f1034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 89318633 1250 89317383 89317387
    0xc030d0213170d050f07080403020d230606010c061e050109021e120a0209220b0906030a0b041103011d030309120c120913020c160f060e100201200a03060b 68
    0x402009003103031107503003084172816401160040802c501c08040303c001e15130241040d20440858542046c41e600c4610f900080202d4420b161105038a00280c1ca900c5000c05031340310f403c5044592149802000b80c00c20540a200f100254400e07668018051240202720300c500042e40e64076000d5040c2c0e4684c000c4002218094070421150504606150805070004403100c40180c0d644620000a039840100c001112055020622450030340c5c5515070002090380d40030303a01441281c0c1c50508064136880314240081660342084040b501260540840a003040009400018140c03030120301080d00041c5001c0e02d100700d600000030002e510720140402c048002c0000555818142041440b58585601c104c05044c000d0020401080316030b0703281c030341c0c49200c800c0840841d9919141c12425440784495602091982c1f507103d000a40b44a03480760740c00480741940d4651880e0580d0314100010344c0380d080c0b061002c542d2205075825400c4400c80d4400903140b80c0602295a6004c4100c1c00707000d0320020343c04943d40b0002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 89319883 1250 89318633 89318653
    0xe010504030e0a0b090d02120703050d03060905061518031213080c030a031e05072306061207031112030a090f270203070c1506030303050c1e0c030d021317 68
    0x64004111010b56040f11015110300b0010202d61600271691700c094110300c1882018a8480e815503c96030030340700c5007141030090b0703512841441400c4104102900408e0340030480d0318005144146441d180d0340004081d146801c084c024145c040ba0001c0230326174540da110040400000074104403c0284176800da002d040d140c10140c802030840d8001140700442c0c0032030035641c1c0307035941e200b40d04030303050194003075200c2d2142c0812404940040079440c5c030011039032040e0404180107241880c2020742183c1c503c0007c00800341140d803480e03140041d502d8240e4101e101d0842443c10884140090305100c0311580e18100000d00d00f644680300044140c0c000300f00c500c40e07810401c500b10f17200102001900450000560b403030b207030f0310012282c0b01c004030405001c1044094100c0c1c0342508542000301242c0c006d5405000584400c540c00d40342e072050320a011210300300c2d881507401c440c808501501d030f9040e250781a00c0c180302c441410ba5007a40d001e0170810009013148041448100b015680d01071740442400014044440 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 89321133 1250 89319883 89319889
    0x303150317090315060a1203140301060302070203060604060302090a0c090e0a020915040b0a27080f070501030b060a0806010c06090b1602030a02070506091207181404030815040e010504030e0a0b09 86
    0x6180107504440052083d604285801200c100303420085030340422b603032580c1d40e40d4010000e402080040b4802d02414020410b00d2810340594419a07400828224403070310792291090050001001d071350240107010b41c0c001800748a881407940f043c032100301c0250b907406843c420001c900d40d603902100213644041c8000d00c20052880113580c2c2086040c2802d02c10848000d041d14224000b1003c02c40649020303400c080303110040400c084580c03949100441c1c00d156111001901a5213040e1251031700554103012400706c3c0f41c868480a40c22a1042c10008002481500c54005a404110341030f00d441d810201030042e01e0305070380d4444848060f14400b842c00c003003200d14020b480780d442d481138038403543c8042211111607075000030001122010908440b41107540d001c840f11000c84e10402c2f41000d51521018040b030003000c43d201885144c0c190794854a6030f562280541c08051504116500035a5502207682040303024400c00340181e00a4485404c1448884200140d00641d5008551101d80030300020b80251 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 89322383 1250 89321133 89321149
    0x71a030606251a0c0a0e04050c250b060402070b0a090503090402180f06070201020a06051b04091a01020705031e010e060c1c0501050607030315031709031506 69
    0x140c00311034080c1e40703181005080400070b0424100e40c10042d800c696510421011031200d60000328400003940c0e107070781c90050070022030007906569000f0903015428907a880c075090740300070b03801301300341c8404c1e42066680942592001301c140d81c07200c6048041c084a01c1448420340c4120340c401800c2307030150701d80052983c0c0c54540d00c0c005404c81d13909075202c00703c0b032042210900a440c80b00d04050800c54581c10030040c45403c0d2018400410f0117000492440034035820400104c44041d5010780007000440c070a079030fa0800030030004011612818101c0d0007400000d0410005000802c070300c00010402c0000021450745010354000b07124107551000c0303402c01403510041000c0c000c0e286121140b490528454001c140501140c100f21035490044400b08501e1044040140c5504000c08105c880d11081c4c3c0712070030003124028010984c0c014030a1201c01e0010f4071a030054440c403240341c404c2a162541c1c2e03544034100c00d60382120001840780c000c51190100c0c24100210800048840556411420150045040784d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 89323633 1250 89322383 89322391
    0xa0903030318030912030c170909010b03010b07080f0705030d1e1413060908120f0106020102070503031501020c030a030503180a020a0501030b1801060906030515030601052202030117071a03 83
    0x40009175a50509150240c0020f0f480150421464418000c100e10070803245d80c004041180b00d2424140045101c05400b4103a83c1070301c0040003124034000c00b648480d80d040d0000c046081740c114040001c00c00042051000d0945a07031203010120b0b04003003c882c460042d9006103402d0030440c1ca400b110208400c61111940d81100840000e800440c3c5207050010291082950281030700b07400142c0900c0000c65109128440d100c001882e40c256600d0320000c038240e00c01c0d5480904141e0060003c01c0581c401400d4815022605004a52a01c0140c3d03000c00e0510070990000c0e0045040030041100e51a155029006008a40c1e00030300920b1500e0f900107280c1020764040c0c01c0c1011758482e031220701c82c1c841c42024203522070103943e400180c2d039441800511000b180e010b6000000c0c14400801d41c0c0d42c1e041e01041485001c01070152540d40c1c20700040c4804465611110003801c4120740420304e520350305200860107841c88201d081102c070082c4600c0d51910400c0e0340307e88041200244110019402d1000303603030300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 89324883 1250 89323633 89323649
    0xe040507030f0501030821040503030402010e0a0302040f0b0906010c030c060b0109170601050f0603070e13150b0304050106050d03050f070501110309010b0a050a06090909060e01020a09030303180309 87
    0x20588035620308400400001c0c4001d06a42e1800f40040240006200980395041e0190a01c543c0d81c94a0241c0c54401c6000303075402090f42e842440840c00541c080e2441044405001e0500784607a680d0740c0000b01503501810301c49071065603400841c1c165050003048198090003e00740500044250340c7d00a15900280c2750142a2568030140f180840e88182a41300040c0764080610002881060000b0785400d420f1062601c204001c4001410130f080c0300c6c0c10741e0303c1080a6259403448150000c1405a21001a0340740302c48903a0344d043c100c041c01000401200030380004103240303440e49894980740e0308445403500818800c903113041d01c19000a51103c1107030090441032108545612592801c64090500004502054803003c010030100200552042070511800c440c1c0c0144565189c003841100d00707a81c0901c3c400205114000e0040750f01e10b800a45000d48940000503c190301448020f003260003a0303c8040c0040d6519100700705040e40341c0104405030325206100c1650840070366002e8402403061142c204 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 89326133 1250 89324883 89324891
    0xc070503070501120f0f06030302030307090906030b13050a0206040914060406031211030d1107020f0901050303090f0315010806040c090b0603071202120705090a0e010e13020a0b0c150112030e04 85
    0x10000d170560440108503400070350502c40c00340c691401941303070307001100d440380059031030030340058061103034040c00045039000b0f45c510881e601e0355510080041c494020548451241144010051311840010b1000742400c4a00088045803802181395144002d4512849641000b01c00d10116003020303400c4180300c0180c20700c402ca10a0000c1c5d014118012a0555001c4600d4810280c030903131000b10080a00f24806c66041c1c00c0d00f0042d03010801a12800c0c041e050f0550f000b408566400d08003208030007000d01000381143e040d0a1100410299104242c11000c060740000060004000c4c2d4008141c02070180b1440a003c190208004070f80d440c00010240303c1003000130b543e2124041d502da412143c4c0b82200d4000281c0c240f40554000e0601d50040c4109030045041e410001416070b042d0240354141c0f1203c070949541a150044240c144078217a0900780c0c0c0c070100c105400a54070f0103010003050205030440103040030914104111804000591003481040c0441c8124000030340d101d14882445c0000300c038005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 89327383 1250 89326133 89326151
    0x60f0e0a090b010909020a03051902070c05040b01030b060706090614040b1f0305030d15050a05010203040311060912062505092202040303120e01020a0909020a02210c07050307050112 80
    0x1310b00042d45d07801400950703c006078060442e5416002148101a40916441c8190310310315030074102d10529101501c06201400244901d1038290024041c09038149030109a18100c00e0000d400b507400124225061641c840a2808200103406044117040b602c080041c0c551415485004080c10b0003485819068052034403000350405504010300913581001c203d0b0b8480182408000c02880c0c42c95804030b6859040b04009078518001c1c00c0c0e40213481040c0d0203541090301d03568038140e0440e45040155448801400200700c00d4a42c030700002d04150704400109007a00b00050000c5a60400300800031814001d404220304054001e400c03a000000d0641c0d000c0e411511013010400c00400c0e8104920015000180c00001c0c103901c940f5101d604001c48504020341340040818074203e00c145155030001c40c001280030814210103602400e0b18440a0050b03a100101c00c0e2201132405c14007040c01c03041c00300302103034140e0641d0301004404007800c8103800810800c0e040a0010b000f02500c00d008050160300d902d111 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 89328633 1250 89327383 89327387
    0x70311060f07060504051e12030c0702031c1d01050702010806040905010501181a01020606060703090519090c0201050c090402160f0f0b150f060906070b04050304060f0e0a090b01 78
    0xd80e0401c0006855507101e01c42403529001034001503800b90703140d01c030f10f240e00e14040c0742d0850302e116001d89140042030383c005218290469a04000c01c007410b81941448890050388051007140912240e02460182e4400144006030404120207140b584d058202004085a80d030018116080660242001840d541e9840001005003650b01802400f55080030000117240084400140121048a40a01135044404440b41c2018a6000105e005030301a8000c21803d051003401014454041e240c1380b487c403520707035000c50401286c2d84040607086440544c02c0140d12183d02c41c08605182510003408a418a807041030b0440c001d907080300f4442c550005102b54248944000c0c42c40d0140e0010b2004100d00e02410109083e4104034000d45810203030000040d00300340610300a1001c00402030444c15004615030910203250803440070150428010821030003c1203212030b500348034601c110300441e507031420406d0042401c0c41440080c024072021110301907103071752000c84503001e0700c5140750002020a024401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 89329883 1250 89328633 89328637
    0x90303120b21030c1b09040b13060509030702010e09060f0103051906080105060f19061d09090f010b0307050a2306031302030d0e061207020106090212010e1807031106 73
    0x15591a01c40054841141c0c42e008006000c0111851081d03690300098280d40c1a030107150346070481d5005d100c01e40001d000900c6044902d40220101540302c84250017560380700102e031001c0d01c03440c4503640040b81e80740456034080e10100c0503201c01d40740741400b400c1510110300008200b0902e00d0501d40c03100c00160f03801c01c06003007070345895003104024480a0784d1410030fa40200010350360700340186880401c07454a0309085466074038002d8940f041440003850404120740c03000d800b002e420440c80781e44d444e640301c60392010181c0d4041c00d0440d001c0c04800f40d648900900b11510300744410f000e9082840c0800c090f0f40c8124105045403004030201400c100d00c0401c2030a64200503a00d00c1c1d11400200503c6000040440c003007038024402d42c2122040484d1040544414503140380150784010200003901941c00380407801d0303030001001e000124440d07440f4102e960980e0003000c0d400d0448000c441c01044100c0c12100c0c000e4000065010100c5290090041c9580b00c2c40785000141584811000c095a20784030842 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 89331133 1250 89329883 89329909
    0x50a080a0e100906050105040f0b010503010b070309052107080105010605040603090c120311061b030408090a0e010602030a0201060f0b1b0a0206130503010b041104151e030b0907090303120b 83
    0x40c0412507401c084c98100024402030154500540c41c1001c0c10008410600c5420005881611260700f0b688c40d000c0785040640c00407108400b00400010300003040d44030504621809428410300300504c01001c02e0444c03401e59607600000706a03050000410802d508101201d00b039489034038000c00c9400c414200000d94003820b61200110b883c840f42c2c2a814503a0200160701010040c0044c2c2e02251500206d445900400c2100003031820700800226001a60750350050641d090090a03d490540e42c5a400c0c40c1040804d81c848070142c0c1000464100751035081c4903990280440341244401181082444040c0c0c0c014902d002d9185d46031510041c0d2904010403040712559401840d056580401c400c0e10320300072445100f103a00941c00e0a5001e50703030f46414054003400440a0382d805061030300d816078200301c80c410240c0407800e01c011008440d07002c5a4114500d40280d05948000c626800d1860910101807401048203042040070002030001a502010b440700001040360b010501160000c000382c0400900c1c6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 89332383 1250 89331133 89331163
    0x1a060f0403080d050402030d020105040506060405061c080c070509010e040609081b100c0219020f12010e010b010e060c030d02030c16030903050c01030b030c0907020a050d020c090601050a080a0e 85
    0x7180402103c0d195410141c4100e10a0703041da1800850590300b64203844082d07a0062140c0c0143c80010b00380c5c2080d034045540304030010080b00800c6509010380010000d0030380183ea1400c00010820400310040003004002e01041d900d005c01076141a001d80312401020703000404682e2981c0c500000d01803000b0a1f201208140d00340010701d80d05901140c3d0b540c059140d0340e00c1c401824030031403941c00c50000c07518030301400745500d108440c01c04c10350800540100140e422030340104001800d03000c100091180440d0881c8a4000042c040740000024180702030501c0003078400d80080181c0c0ca10004080250303080c0503241070015032261248030300b81003503024a5050740303810f01c4010212004e00d41d1007082107044a000300140c0e49112a010011404e551380d85880f65010380c03003102a02e0207410404110f980c84850340c415903041d02e071940d681e00c0c20100d8080e060760059000d0030301c01146140004c030003900042c1c06d003001c61401a50300d6014003604c00c028540b401041e980c0c0e9508124503000c2c0070442c0e49180700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 89333633 1250 89332383 89332387
    0x6090901090b16080a0218010e060c0114012102210a14060f0a1a06030a062408090a030c02010806130c03060602010b03030c0303011e0f030305030f07031a060f040308 73
    0x44a901d91958800d4141100010791305004205050124403c039411074100f2584606000c0308400150b501c0d4810645075500200100140d601004003031203280044456050007030490f5140000780003640c2010701403164002442d5241e440183d0f9040a8104c2103c80300c9051180c2c2c00354805800c0c14403581000240003100d03070a125a2021801040a5200354820218025292207070403c00003200e851101c02c00880e11054402101480c00801865100c17800b4480820b00d81d403a080c0508032010840c4028900007882c1094002d401e402c841007581c4a0307134a400403c080285c54030010414007180d900603050200340000300385d064450903a620000c0d80b40d140300744404110240010010101c0e0310919006501e00301c0d0150b020304d00030084500c191100e030001c1d030450b401d04000d00341134072090340000c030038844200d4002014000c510504000358041d0722960380ba49405040700c40b0302080149110101440d0089000c80741c2186900034404110075651940c44102150501c01644036540020b4016480 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 89334883 1250 89333633 89333641
    0x30c0f06160c030606380a18180204050109060c2111010e0f0f031903051008190b01120c0b0a030b09010305011a0105120114011b0b06090c090906090901090b 69
    0x2942d082501020080444502c001c0300862004683c85060321028a00040c100503087c8002d100e0a405200a000c01c0d45285d40107558401140e0900395011844046c540c010400704225030300000030741d000f4010b90030103002c614003a68624946d201c2030842003040c02200e0140307101841c42941c080e200c0d515440c000704480ca019040a566640091016000e14403e140e01c18801107004030a54107103034140e0b80001014901e050007903000d446c0c01031110b4107002d80c40100241e16141006024910940007104c8044c1c0721240c100410f60400c140c00081000001d041c074840010b4011a24000700c50a0700740c0035440f0149180c0c00c41c06004680707003c44d8045004c0c00080b00740b04066101582c1e42d480300d070981101200130801500d09000700700084143c03076461001040421905115044c03a1041490702100501e00700350824500414000d0035507072100b00c0c2080044505150660030f421524907245141844880c100164204100a043c0750007034600101107001409c0940101d204203500c0910181c44d442c2c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 89336133 1250 89334883 89334899
    0x90606051801080706020c01080f060114030109091b05060a0e0112090c08060f0f04030305190504030e01090801020c03071e0204020705060703110702010c02060702150d0b030c0f06160c030606 84
    0xe0295080f940220400050303080c0c00047d00b01b84504c2c06840d100407c0c1d440c0a804180c00000420840c1403021608040b801c586448000f940038000c40d0b413000a010020381084d5441a40100800350283c5403040248541c0c0e45440580b445d0403984c0c5818a50760081c81c00403130b2100c1c0030352004d00c407103800c1969103020021016208015549406c003100d40b135503601ca280c003203288003c1e00c0c034281804055001c900407a1103900025401252203140303c0d210782261003440212001120280c00080b50b1080d8403c039980d010007100020141e5000175411302c038001d81d80b80d440e84540000180f0141e06503040001b12071301c0b0611800440d80040c03045450b003119083c899100c0c1811200380c8006803808841070b882c4681e203c2074400686e01030392001001800c2d6400d0104542c414401030340d0080e000c4501132a0781d01040000c1c50849100100400c8103004c107010705140c0350100c0c044910a06840040c0010741d10f40106407404055800402e41d003288640c01d115032400d24a03080506024103014010403024 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 89337383 1250 89336133 89336179
    0x1b03010f0e060301090b13080708131508090d05130504060605070b0f090a02010305060103090c06031e0531050d090509090313030204020f04090501081e07060203040909060605 77
    0x4404142011841e0b480404060807106800360007851040f113040480c007440c140d0808140c07164031915002e440e0a005840b028500d4018900e092126909080144480c801020030340c03181c100c0c42d0400d4103ea0905070781950306d528141ca401000c02c840400c1c1240740d03a0601d43c1c2c0d0b20045c00d01a208111064503450020710552100d08103403070700ea1301c5501181c9800406d8123030a03c969009000360200c0507940c0d00440240c030000d007946041580f2010203801252041e0003140c020b040039140022040c2c00600c0b040011101742040324141c03450802040b1008a402051204102c5405d102c0e00c0082e00f0145503580008030038001809034800c0361400d2550716007020080c82583d000712980349680e030360042d2195480c420070602c0c44003004004010401810150007500b00f54582c180b08504150315800c6984c0ac94100345e01030309195102200d111420742e800c1c000140d80b1031165002e0821039003044c1d400380d07807441103120301d440d641e545100c100284030f090341c80b0101400b0300521515011441d4002c81001c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 89338633 1250 89337383 89337389
    0x40b012d09083405120c030106080d1706010507081909050a0b0a0c030905040f0203040b09010207020108150103110a0201091b05100c0510020c10050708010608040b1b03010f 76
    0x314a161401140010700040e03042d82402603c40d01d02040b01e08410f155490310b8155001d5610300807a03a0000c202940c407000104032400c1140700804000030303100c0401d400d6400b254008500ca80007500f013500110790094180c01043e03008000000240c44000040341d06200714180a000318001107166900700c2d040c10110780f00710406030386824003030340c82e641004002541c07442503042c00e0301e00304205460030380100d84204640303010b414880803903541c1e000840d003901c0d498511000050707400070400041280c000d654540100000c0001c50510f6250303800a407c490001d0150711900307103054480d1500340c0c42600807140e940c002c000c03519100e4002035806406840c804008442c00480b920781140240c41c16100c810803941c0042c191100e5149420042d1448000c02c441600d160155007921200ca0460f800103000d40c80c024002400c600045945542c111000030340700350104135401c07004001c1c4540c80031a080d0095084801c400ca280c030b030b83c030000e110342c0c8204240f20040382010000240c1031003260054021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 89339883 1250 89338633 89338637
    0x70204090c061404050a0e101505070b010b0f030c032d04030816050405060702030102070602040608011d01050a0b030a0212010308030a0f0621140a0f0606050f0906040b012d 76
    0x4060401520400f20f401140900c681000c3d03c081c0c1048071240c4031403d150419842c5071070034a902c2d2550300315809000000b400c0e8000c2900041d041040000565505005101c10310301d00b4103186002142d040a84406804210320302000300c0490400703005d0096900a41140700c0150392071a0b03c007400030120070340485d0305070080b038200d030000b0716036a070901113500075905113a441034503150410b400c010050f000503800760780640d420f1000b000082d882e41b000340043c20341900da0a08561401d0854081040d032071a81c0d0801180510041020b910783e99030500a03141203241d6540c0f82c0d95081c1c1d18000070f0188403540800da071614030000041c4507003d0011806001001c00030300c204280712140b031040e10500e1060f400180040d402d03039603648840001d03c0101300c1c807400f180612401e03154212480c1c480228400d9803c40034406821040100b144107120050000b55030655138000104006030004500821a03070265407100d0100515038800d200b0401e000281c913131002800c80000c502c0c41c03a0b02c4000b0842d440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 89341133 1250 89339883 89339897
    0x30718441f050f16090305030408060f010501020a050d1b0f03030c0e04091a041b0611010b0a03150506031204080105090c040605090a020c0c0a08010e12160b0c070204090c06 76
    0x141d200050180922900f01d980b1045416141c008084400c0c0c064842c0c072908209801001000149090000708018180c1070000d01050401c0d0f40d2088000700182d024606640c0011000c60001e440403a0010244040e401c00c1442090f58189001c2c0e80182004001e0607140c0c4420920100358040d44200b040150039620310807540010390901046404481009c2c040710030303d40c0022040340c6441407031980903104100072114507049002d00000c00340036030003031000300d100b80042d120052024460301d9403a503021180c0080d62841c5440d1110b40380204000e244442e5101c500044107610104400300b510707240d0880d11607480b40d4035009503001f88020394504846000307410b160300701032500e0302448068900003041d0074110345580d03c5100096100c0d0008010f240500c2d0310900850b940d0040d03007401000c14500201e80c1c00c0b9403030741c10b81c20300000c1000302c500100103100140242d01c40c2510100510707484460402152210710030107500d4095244001e610a050207480e0341002880c010352011107226803a080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 89342383 1250 89341133 89341183
    0x8090607030213030b0619080a050c03011b11010b030f030d0e0303150d0c080111031906080601050103020904060504051017010e1c0318060203071844 66
    0x500340e00c16003d000503140d6a60006002040c0d0742c4004a40100c0b0080211308418081002c4c5d07040f55030603520040150300480c00640070b00c07030203008042070823a04900030402001040c4000d20340040380c1020000f08038080c819404488800d40c044210000e000f8121b4014040100226076603901042940c04003a08100c03c100340170700300100781c0f4040e0980308007046001c80caa00170b0010556901000740c401c00c004420001d06020207101c0c803071442c4402508190b1303034a040000b030f031552490014a9200b480c901001046a010302050039415100e003480c002d6540e007410300000e0050441a00b001c1d601615100c28001d4076148440b8240440e21402c0c640440303000f010754018200c1e0030405248919422807122000c15440682c0c3d00d0040210901b80000c0e00d08002e1121904d004c1103a40842c1c142d0b0f0b002042c005e05d00d4001a05940d07a00480954000389418004100b107590144001c801c44404005a0710f001c52100c2c122031840c0b0952010304c400c149005101c0540d40d46900c006003031043e03110300410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 89343633 1250 89342383 89342387
    0xd0c05040b010c0c0614120103080301031101020307022809060b04051c0f08090a12030f08010906030201090b0a020f0a06091109250306120506010f0b07020916090f030308090607 78
    0x3c1c1002a8001c0600c200b8645072802c203441100c1100220032030400c0400034400b04804440030140070f14012003005407a5815881d12040a440c1d00103020305651040c080100144d454650380e81d89034118604045403d440c4584050501019411229841d81840e0f004545900040c003e401100c004076141d11240100032191a00089550f80280c015021300324032402140b100402000642c0c0d0182c41e0b10880ca550710705da0201d603058130100301c000501e000e15501e0300715445a661405090300c040200b001600d1a400a01458004d219220300000301244551809000b8440b40031985e41140a4415042080c50190010704404100b260041400c201c00c441e82c3c180003220380d1103100380004000c44160440400700c10900540707040342c101a12620007281030394168900d1003550b07104400801481d41024860388031400a1b80100110020034800003016076501a04143c1102404100001260764203000300c8070412160020f00c05850103010010805030310261941c414450003094640c1500d80d1002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 89344883 1250 89343633 89343647
    0xa080405060711060c2a0a0209010905071d04021201060206041205131403250302040506060a0c020d0302070e0f070e03061005060a05120109020301050a0e1e150d0c05040b01 76
    0x3d541c020340d11010006802071010030007804051920b640941890240305001a510803402c0b40610b4150051103500c1d0071030a10b14809405819680d40c00d20041c074203c48001e00d6083c4181d16188032400790b81c1d82d403050f5129a4100d401990980da00d044056849070000781da200d600b41c1d0100d6210366240c2c01c1058a910078011343e0002807e0011020580e032820b10b40a40c0d0071340b40e152059045c000d154404591a080201e96100d8054045504d29540d02c1c0d80108000c5502c011300702d9009407400c024425590754131210150031698104c070000c00c40764150501705d01c0c144490300200401030304503007803146c8004d40040091007002c1c0e42e6590000c0e18079503001c0c1503c652085d22081900000568140032900e03249014054202c150704d4482d042410b01e0204580c1254280c0c810001d441d4004018040c50802c80c8400002e8180d88503001114148241300000f422410b56082202400340d00202d040d82c0b4845502d500c8215000f05240800c4001d81005007044041d40700d039910039172400740182495402042 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 89346133 1250 89344883 89344907
    0xf090302010e0f120d0e010216030b0604180b07020105100602160603051801021b01050609040807061d1f0b0102070302090c0c1204090603060b010c080313020301020c030a0804050607 80
    0x140700180002d1140c00d210000e0101d8903503da01400420010084800070844d022060103980d96404d42c84400c6800641483c141c03003d40c09401c088400c0c280f01090301c1814040d003143c0161000100c2507194002c0a00e0400f080720028400030070001413091290307054020342d000d06e400ca032400706903a9031444141c2c0c0e035141030018001909125541084454044e90041303902c401100340b5005040169541a401c99004d0300e500d21a4040042d590001881b09110352070303003c0426a03000201e4205911101020f0040a400400d200d84030310b20340c60100c811900c2070008002d03a50131a42e0407150303501c3c0380716444024a002c030000d42c641406140e81d0342c800600c003800c8940247c105081502c4a0704024216030011b10384c10140d1159104001941c1101d40040008000e0158001070303039400c40c50030100781c581269140d410000034000700408500b680e800c40ea040340e0307000c1d04009403002920101c2c0c0680998001131a55000c04a01c0c40c0c0529000801d9610407440341050f20b0240c3c0d0f9204055900341e89441e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 89347383 1250 89346133 89346137
    0x10314060d060507030e0a0b090f06010f090209060909041a10060f0503060d08070302071701110a0f02011e020a120504080403120e060d0e160302060d090206040503010e07060f09030201 81
    0xc001000490010f078842e58105183c0e14022413a442c84482491034254000c10441d42c0c4903d50003040420b031400c0c070501e0050503414002e01541d501d0000c01c0842810b490280038442c6500050300326940c5d0320725003290108000a4803000551034613042c03c40d840b056850f9071898450103480040e011020445201041e54141c0c2c6610410b1420500700300d60a42005040d590050013056100f800300c0c21420141c02c2e802c6c0300b03900910040c0d00340382160310211180308a0f042c2580c101020782160340c0c07209003a1070501140c1e1604210000c5924000c902501682281907198440000c000800c41c1c6141c0085c1815402c54035040705034810603402c43d0885608840151032800c00b80300600003d0034210741d6011001007813400304640481580050740d00c0c0d10203103640d00b00781c2d40e40780b000e4240342041c82110342d085403c50121039202d02c0c640205541f4401c45205c1e000e0507642d040c41d142107607a24810785000c0e00d8090000c026141d10801c820f030780c030308c00760013810080381c0c11010806109214407541e50607640d041e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 89348633 1250 89347383 89347399
    0x11030301061b0501020c0606180910050901140702010f0c170c030601140a0c030908160303030c0203132903010b09010309020f040903030506010e2b060905160501031406 74
    0x99048030b000d0001c03842c0c1400307003925080810200340d003400036004c580b0303900e405085141895010000e0b50b06102d0341011844050008122205202041902d02d81400300c102150540e07552130414010841038904201c3c1c40c030b85006001e10b0540c150710454007004c00ba10304201d01c801640040d40d0582070742d0304008041d10072400203101e09070034070007454110390181032804c014085c401001e5002d400c0b00da003290004402c10308100c01d040d07010410320010b0550102420b40401c04055030f84105855001c0035060588514592011038820001c541c0003844200c01d6150458945000d002c11260343e40e90035400b05200000c00c007180500703204032030403118440500c601e007034049030041d00070705000001a60f00c241104e0200d526a100c9000315810103100fa0740000f00d611741000094039a980d40071195001e1040c4190010030600504101206200104824a0300c0740080c5030134405005c203a00000c0480c02880308955010346c0107440c0c1c805880702600c06121401d5140e8115410480442e0300039802403130 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 89349883 1250 89348633 89348639
    0x302040c020c032a0d05030c030703030b1503090604030e031603081902010203071e03291f0e09041407060206160c0809010f0309060e0c09060d020f01050a03241511030301 75
    0x4170252141c6103200d20b055a04001403899485d055030000743d404d0b4040f0703840da03122120300d1802c0904030385640c100351041c60843c10b02001d582d13a1582e008000800348101c052000c40140c2e020401100b40c400042401101151a89018201c81d000307900942d40000c0d508296800c1c030760041c000c0c0d0b071051003103036a09030030540300c1c008070060411182849018180d8401c1c0044412040c0242d403118444103146241044401609000200c600e40c005a20301c143c010a103460f00d180d0008602c0d944450845510f0203580303843c10100d415281c00000400d983c810000000b071003d401051841c880d003110951499501800ca10a6540205c3c1e80401441c02d40200722444496000b20041e0a03030034468a000a50b00c455556941c0c00c95449400d900007513800745142e5a01c524054045030741c41178060750507d2400c17107180d011902044041e607880741400000701e503616840d803007940030810038100641803880c034800c2070780c00c2c1e1091985400341d03090010341e03940070614060060041c0004407001100035891680303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 89351133 1250 89349883 89349889
    0x18030f0c01080a020d1a0102190c1719050703140a03020a03051803011a0411120105060f220509180714130905070f2310090302040c020c032a 62
    0x24001d180034209982404070170000c400a114201601c0c00f101d40d881d604000d400c0000e450f006001204101d102d03403a0f1200d400099085403a28126803405890f078607048140302075581070040c03107031a052840700e81407803550502800089005c01c80b402040c40d500c850303c00382e01060300e9007100745020380942c0c44490203000287c8140010210042483c0c00501c0f02940800002d0969034607008854845e05140184403680c0b80603c21200031104a030032403442e00300c0301003054000d0001441428070400002c51301081d101440b604554403a80400c0405152549040210600091901607240988000000216030350302c9290001d1648203510000c0548628000d20041c107008254a050b4000d1042102e014600400c3d0141d10b0440c3e210703202030031006062120105a0300055407001441c075800700e640030784400791160b0503152440199540b40c20300f0401d10054402c03040680c0000d411620704001200980c0e404581d15807401011400d8412080d188a80c507600d036850000f0140c001540040e002a50745 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 89352383 1250 89351133 89351147
    0x1b0807030807110d080a021005060132070f0803040b01060518040c0203040911041503060f0e04020a030210080402040b04051b071403030c0c0c03071412011104090218030f0c01 77
    0x2d04024008010703138450f41c1e40d59031141c01101c08000542c0c01010182030912150080076840301c02881d1003c070307111490103c0e030084281803000100c100c818213105407500000703500710703140a5000a0702c0e075805e40c11031038a41060b5000b10390952714140700c04004200d0350320a0086a1003066000c0000c006a010402000f00501005000c0d0003548410070001559a00c00e00546201081464171641c48518040c0352039503844824084004162400105102c1c1d02c405903c031500b521800801071b40103584510101e024160f503600081e40c0024040010154141d0104030588228403d89050001860440901c400e840c81aa404542a01040b164803207424003140070b0082c15008103a01c0c003000b47c40409480c02c41e4005d480c4000701c21400a81c0e0200d641d410080d400440005900030b0600038a815480400428103140c501d02c40c1d141481e4006002d6025040391003001510851540d4883d42d030204c0c20700a500c40c0078410461103d0202140c01c511780031601c0740000802e14080c150340c0394100f00441c0c1d41 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 89353633 1250 89352383 89352413
    0x6032208041e0e0408090f10090509010f030c0303120216060506041409030405010f03140108060708010b2b0b0a06030c0e0a030506071407060e0c040501080f0a140703020402071b0807030807 83
    0x60700d02d1036035421a51003070b07032292300d01602d034a0301a07080e03050009100c0b21400580181210b44070002c000c1001a2421140381c1c201c0390540307084030705100c03006c003020003038410f454060082c0d240c0f00c1d02240500039580c2c041405035108440c10091303440700f070100591501003290b941c4115003040c4000c0116501a00c01c000d036000f82850005801080f03844d556165107020382011403254040000c1011480d08081040d0160444001c02400c2c9160094800303181420118450846d18088a15840017000c41e0040000b20000070300601804d0307101c860007002040300c22000d0000030400c2c0c1200703032030341007119080054079041000b80406a076050710541d8039501c03200211560300401c2101d40042a641d10881d08004416006803605510704001c01c4140c61043e0060741e41500708100e0040101c6000030043c015541c03042e11126071500d0001080d090046650005c0d420500001e0740c401041070110401000854400a49070180d44070344c50207131344000c2030100078807001041080c0700106036282c2406200d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 89354883 1250 89353633 89353639
    0x312030702070923090f0a060902010509060c30030a0b01200304030210030509060610180f050310090203030a0c0609021c02010305060114040506032208041e0e040809 73
    0x8030564595144084940a841080169613190702500301d0000300c2d007900380c01c29003040040c055050444116512131408140c0141155503850071a8216400340003551484807000348201d480e00042000c0b5521050107107a401594021a1400140007020b0710401c6003004410880c0350139136842603c408000c00100d02554148407038107000c03401d0401d600046c208481c0a141c00f940e201d40c80d51043c80341031900c2c008450149030501080203002040020450b5010104071b03104481e1060003c0e0507101c0d50100141100c1d441c0d401007000c564403240342140700442d403003a021100201a0303524100c0440ea01d404009502d41c100704040d0050a2294040800c4640900c0c00020f0b41ca890360300045e0791841c8846120403590148078003130255078142c07280c03c0e800b24083c00c2c07016000c0d042c81a40c2c0540e2281d40150780c80b030710b4040081200054045820b40c40d078211503140d03070310382d07000c42c02c4c01c80c81500144200a00100e01144184401da075413001071040320101d620b8040f80383c9665a4024168000c2610150 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 89356133 1250 89354883 89354893
    0x19030506030f0f030a0305070504050607080703030908030a0e1c170403030b06030f06094f050f1018060f18060e070e1e060114040f0603050106020105060312030702 72
    0x1e0010a10910f01c240c02401d000b180c4d1154401030140c181c0300c00030000000d0083c00c0c40300b0016511136408541060350b0110130319541f000c181c941075005000cdc3e0340000d0518000441009001d0016601400542c2101c600b2540702c0104254590b040c04002c654220000707102a00ca114018070034040c041d00140701e4203004c0342000d001c1e030114115401c116401c1d151421a50144012400e00041068000410803400d01500701410982c402000110780c4814060480740311040309040c1c00b2040543c1080807030b0700c2e030304550050f0402300d954441003006200a4014103006001c1c149981c130034007181e2a55807920311200c0d0400d40b50940100043c0c551340880644840007201400d0301c408030a00c4040c0b240030005010b1007099003807442d0003403980014408011040600c00400b40c1070030300e901c8102c00d1840b440a41c0e51803500407282d0060801e50a0b448800c0404c000c038804a4465665066680e07a640800031aa600d4030300700c3c2619400e5034699019048000b00f4142da000f020b00443e4420310a00481c0c1c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 89357383 1250 89356133 89356153
    0x30a050a03021614090624030a0e01180b070c06020f0a03050106030e0a0314090f06030705030402010806010305070e10030e0f0705030c010f09090203070e040203040f05010b061903050603 82
    0x5080c4805040120016080149201034626072140e0050140c1143c0c920740c0c0c0141c9000c008949010f01c00703080716204c6c6240442094050b1500800d46000c40812101300d07460741440013042c005812002d0f20080d032542406544500220f40c5050001801d4001c0c801005070344500300309451280f0307900c101391202c40d000c021409085905200501c0007210035600003401d580342c01c00003001c1340c0300f40c00c1d0740b2040c0d0458010000400c0d40460700c988079107900354a030b40d56804180b0004994140d00c503001508072a01004200025411901861150f03000781c0b14000d80d69904401102160021165080401c40c00c0b51a03480c2800d000401c3c0c0300c2c992032800d0014854551079251881c05031740101003510f0b540140818051400c0900510940380020309208242586417000a00b0444040c001c0c100b16641c080000f0380c42c02d20070202e000405001030030842d40ca003002d050240d000700c1190320035602582003032041030507414040c1c1141c120b00f03c44405902520307001d99085014240c083c01556051191603400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 89358633 1250 89357383 89357393
    0x20904091a1b09060f0d060b0a09150906080414070b0a02070b09061b07031203020c06160503160c0b01080105010612110906030c07060e010605010e040e1b030a 70
    0x300000600a8549500024801d00414203200006101008999a2410714010640d07000b040d6100f20104903401510340383c0b28081d0801ca402003e14500c440c9040441c005869200c9400a016850035513880c4680c00d602c840c41a584000315540003000505094810080309128051658001d4881c3c070304101c00248165801c0d14000140e0014000100300140359060382e50104800d0004010b1007040508200d25440090b1403402040740302d030380d4443d0f800007800d030229007880402d000d10b0b800040c603c403d0f441144c2c020001d411074180b06800e80b040708081407684541300784005000d034240c0e48407495030fa0740c1090700c080c0b4104070300000d083c00140e00707050380051a030f50f410b039001e00100800019198903225000b030002000010101c80d103450000d81a030603039040c0c1c0031960180340c251900e0780d40341c50300a044d10380d03403140c56030180c4080d240c120344040061701074110004403042680c800b0041080c00d01044100d030142c0140c02d10b254410b50301035000c28040d0854107000e030302c01070a1302d0540045881e6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 89359883 1250 89358633 89358641
    0xd110a030b01050415051507050a0602030f0a060e040f1407271b020a020405041401230106090f050d0807080307050d0507110a06151502150c0304050d030c03020904 72
    0x8116a080e1001c4010300450505110b80410b072070030444914011407504e170224800d101d100101c441c081348000b07181c80270b0003820020421700c264810401c559928102c594000103140c1a24007503c41402d03d0350026042a04110040c00745801034480c1a12150960390302c6034801e010200600315004041c0009001c60581c16184041c0c400042c00d210144c03080c1201d10308440e20000c2c10005580711003124130b1100d60001e5108512541a10001800d03212403c20200c82404c52004070920742c00e101c44022005100c00d04103017000304801080d60b01c4d0f40c0320101078a8511160180c0c01c03002c04000c0e81080b280c5007031075004a5690082041d140b0704481038840c0c90300c0350301c112103000c0401c0e0001040c00f01c0c00b826110f1641e105140e03152005003e25120b00704c5031a54094400a08007d446c0c941d060354140040702c0040c02415071403498421542541c00194640c108900c921022170580800140170590442c01c44e4807450380000588030401c0d0035042a802492440400820950300b400400703038645503482 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 89361133 1250 89359883 89359889
    0x7081c1e03050924060a05190902090406030606060c050f060105130b0604050918100507080f0414060a0e190203151b030112020306060d110409030c020a03080307090f060504050d110a 80
    0x1003003131383d600d82071341804507844660348900d02400c2c103901540b1080010402e03282c152000c08201503a2410300100140107007103d0b42010b03007001e1400d80001100d5400c5109850840d01c00c0d41501d00249256448540b14242403190300c3d005403030800240b10b0501c0c075910041c0c811100401765810184c685003c00e8440c0c2c0221207071850600c041d0490b0711000030070082c6480760341c0c1c0400c0038000c91414800c010036242d8040c1414095200400c00b0400b00803054840205c00001c400841d209440c1c40d855100150051203c00790207801a0100c1c28180a03241200b1b80040750050700030002c83e4031803100803a80c00700040034130199203032200c1420507006080e0f00850080c03030409084130840b6485e00405040100107400310b489800155035010005e03a4180c2408480e00080b01c00182085940c101a2501e01b402d040c000e5006681c07807804010418100d001c1c5000e242203a840010040e00c40554007504400c600445010482c103000800c05890440074201c20f903481a5a80c60240c0110341c085061100030360 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 89362383 1250 89361133 89361193
    0x70e0d14010504140307030507030305151806041503021f05190201020d0c05070f020f010309051c180303080109150816050103050703020708040e0403050c07081c1e030509 75
    0x8018801400144c0c008038a010036200c0183d4502104c56034054014407902c10020241a210310001e0801301a117921402000c5024000032200e1042ca4ad4201140780e08071340042c800c52422040c0b003070350307200342c1608815280e01404500200720f91084294015101d50030010800104000702070b106030602c10311418450183e0005a00e13184999440410f88015048240030001c051010101081d213a0740d031507500035016118403080020041c0101c010b07244136480680144504400d5072000f060030004140300c4591541c0344070406030a4508451402040e10001d130024042100602410100e0b6101c00320f80c0c50003405444a0300d070340d4001c00b414080c1003100c11011000942c003c0000b96010f0003000d90104042c42d0852030820a82d40750080c0f4040c500801c83c0111101e0009020140240101c800c410803450458a03090b585002c850390ba802054480040d2442c8030f42c050381c045010b040300054007401c0e111034039503444203034508900803d1b0042021005110300e80d25110f0b140994040d03260700c1c120503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 89363633 1250 89362383 89362391
    0x191509030302150c030a090c15050301050f030114040b091e0d03050a05090d050d020f120403030e0d0903030c020a0504020309010605040b03150c1b071203031d06070e0d1401 76
    0x40c10080c3c1003121500b41c60706884220001c015603a180c050490354170012284002440044a0800d84c840d0001600040034102601c8101c1c002c50707405c000958102c0f503080350b0034000380c0c1b4603505140c280d613145200008407600071000704000407482448250301c41aa01d080b030703c0c0d42c981c0903504040701c0d048614494058100f50f010603616545030040d941e10010811080c0720703504000040b140c1d107180070030b030308010010302141400e00c2100701d40403205419041010701e61150000d0344a01d108400565046011a01d4082c04842203e00032401503c016078680b5441c2c4a50300d103440603901700c100c1700c0c402c9134060305c440b03004116580c0d10320286001c0c0c0c015200003c0c145040c04240011644120003091081d401510304808110351103566651002d01003441070746502280d920480c041c2c125002014260003003000114943c408e510844000754003d607010300ca1015040311204000741e040f81c50500e5034004200140d0860300507800e00482443c082d0061030991940d8031140694011141025441e9440d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 89364883 1250 89363633 89363639
    0x30d18030e0102010506150d1805030c07080109030806060903030d0504060506240a031d07090504020f0d020a05101b060c0f050414190e16032009191509 67
    0x211041c80700648500780000c1000c6e050503800200a0001c1e01c03220040000b001070240e80701175658000f82505500040143d60002d0030b0314042ea04c903002240034040714820703503400048250050045052450b0962103010651b1685030900400c0c0c0d1203503c1154042c48204400d4811000e207100b01071059005043c0010282085030411420f00b2400003001d42e0301d2902e40c8102103100780c010441d51415143d04000036882d58101c00352001e011060356040103030042060010380411a0b41059200340c1c802c84003070900300d0074182000614000403d0285d00f1911803801840309003400107591400800c0da0030304001d200c405109400c43e4140c40041110303003d44840c090180e0581000198407007400c5820070a00f0300d400c00398581480b101000a80d40704800b480d0083c4640c80e011034030603019000c000c051304418036001d6205002c000c400071000c400a85003406c0015046000194000f102d146641503514040e048000c00a03d80c1004a8501d06c051181100041e181000c510300152141d090303c526440f00c0c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 89366133 1250 89364883 89364887
    0x20d0915090b060103060e150109050901061701051c0b060616060209030c09070c0605040812091b0105091c081209060a050606070321090804080f010e031e0c030d1803 73
    0x1000d0043c906041c10904c1c14011a64050105984031110b1020720040c40c0c6000012185c103042e0b54802d6410844150010401d83d40c040c0c00404110508072030080166692410301983c0b81d850040200811006140720000841c21030003940c1184001308003d0a01c80c10115808017203880503005c4402550002d01084281406d012001280070125031070001803038800c00140000d4489000208110350760000031b0300300a0280d055039038220b00d080000c5061b1603e1400d0342d030b03121140c0e2a400300710030301d40584000542c800c80840341d003a40d02a2541a01020314042151450000a001c6401041c107003e021007802425034480d05c08c8540000401240c1000341e1034404a0b071028052500403041001400d0200350402d207035221142040007500c100d140c00804003c02000b16480061a198001074005483c010014050960126080080200d000e40203485a528429111000714601c03004da40d0340d2160034043c01600340c2c100b000041c1da01c3e008525101d101100e07120715414202d210a100c90f401459 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 89367383 1250 89366133 89366153
    0x50d0f0510230a020702061210090f06081b031c0207030204020f030103021801081e0a32010203040507050120120703030617060402091e04050703030f0801140103020d091509 76
    0x262498000c61500e0b030175402007101c9114030013200c004642e076000031a44c0304845400303250040008110400c14a6240e151040c0644581c4c4207240b0300c0e10900c130085400d00001855040d18450040003814401050700d030312146901d824482c01d0642c02140c0000005d078545000030451800c80d903000b26520b604520401480100d2200e030007089050303040061003034420000e03d840300c40d4401c801e080e110080c544451480d2014800c0000c24141c2d0003801c2080450055001c080007400c1c0640c045403041c0c00070700c254201c0c002203e0151940d0321040c02009154040d010302c2c84106e205444020641043e8894940303484900703401d03036012080000ba41003e0641c10711805000d000452005001d034600150300340e69507240508003a200b00100408250300c4140100300322400003101e008a031062505060aa490384071910050340481e00015000044611a5100300d05a44610300c42c01d5060004800440094024550344040c85035142001000302da0140b5240b903120050300343c04a0704100c0c07031030b1400d160 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 89368633 1250 89367383 89367391
    0x90a090f0c0e07090803071b03020d0c0305010b19030605090c0612160906050304020108100f0b0c1b0d0f0305070b01080a020a050f0105070201030f14040516060801050d0f051023 78
    0xc00e080c0428000844048107d03240f8a0f000f0542101340d040d0510402c0546010f54002036210010301c041e0410030118102d00d80441c0e000303000800c0002814020321200014940c8803400d0b0303030400481030001480c5130344059080419902143e2a464250010a40700c0d404003204d1003101ca0300304200722042d50085c2c01404490b11903d0645011490705002030854000940028140815440045c2c08d500081d401c4000a04060f02642d165075130340c1411402580c03160004a209000d40da181480c4941c4600c00c0d2a5072900250480c0000111a00c80b12082603052100300c04025081000c1c40100700340c0003071a8083c140100c0a4188401300d031041040c000e070294012402810f100034441c1d000ea8021059920b000e40a08011078050000c021880090240b40d001c2a01d07070302610140401d2010019581d00002c240b00c0700b400100d0740b40d10701502c040e2424403500340d20204900700c0d0000101c40d524000c2c0000d114108032000c90070b4444000003665402ca2011100c030b00818403100754004001120f60300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 89369883 1250 89368633 89368637
    0xe040f05121606021c0c030204030c1403070e0c09131a040e07060e060c0709020a08090a05030a03020a1709101103270a0c0e06130b0f090a090f0c0e07 66
    0x107001c01002c107004540280d028042c0c0003036030105044034112060007004640c6044820704101091441e00041c000750494081941c0344505040081880003041c00c1558202200400500030546001d21901e20b03c0e00003801680554410701000800780c82e4031212807050b500202003c5422a1007801d050103103840807100e40d110701d05022039005100b4010509806a0718146411940490320b0301c0481c2e114841c80c0b071101500d104240300001c1c0000703683d0107070031690050707034841d4141c0e2074400400740e485a6912001d0015003003044100710050090b8000c09124201d0f0038031f420326040d11072440e1110300c812604816540c0010500d42540d046034441c08082844504109085080c1108141c03090b424024180200700c0d00650024074850003000b420960a83c04103007054240d4a9981c0c12081c5e00043ea104d5003c0c2a420388415010580c40c0240d4070300700c8025042c43c00d214264020006e007101c01030460f5068598451004001c542402408090140282d41c1c0e07038812454000140302e51280100300c681 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 89371133 1250 89369883 89369887
    0xf0e071403041a0702070803041502010617060f100306020a02011d070602060612071509050a091404060518030409091202010b150c012d050705040b1e040e040f0512 72
    0xe20300e40c03120b101d22584550f1820b115a50007038164500404d43c1c0140410344004207001a824016046000c1001117960083c401c484d030310300b9030581c07119603259411951340051000546c0909a00d010300d03400030054201c041a1076803925000200d030b020b2021000141d44400c5202d50000c02c00350f040304081840d100070f10704545010302c025140c0324040d01d010b214200c0071fa0f01250255040040170080e0000090104040401d9100135001c072103184104d5010f004080c2d00011003010f1440380c811780c0c514041c18104c0c2d65445980300070040000824140329000c9200b1083d041c2801000038001030170400e4400a80300c840341c1080046490b182d01014110380c1080d03d8244681c6807410007410348030300042a80c0d02c80e6401420b00b8050b12219902a0081d20071050b041d441c000818030703014040b4284131080115031912a4121035030310560241e82c502c00810019401d42c0c6040b00c0b08103040790554807105092546490b245a160101901d050391103078085458a0b007402428050344c01d809148007080340c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 89372383 1250 89371133 89371141
    0x904060e15060306031c0f020c030109080315011101060b071a01150507080717190f20071806050a0e0105010c0201032307180e060609090702070f0e071403 68
    0x41400460710540075840c04000b08415880800201483c64052002001c2d120046da10050880c03400b171700300c0e02c010700c40c0c248021ba00f4101845200c000070b40001d0070741d20b159a070260001140039007419150400c01ca1070720b6141c1c03181d800e10480e03010300b1454609564030042ea04011442400c0c5090404100d550a401002005200309403240c400c40b1a003402a03c1d5205410304207030a014502002d032850514025010700800c0d0030340101146400410f81000714815444100c0c2e02e14610300038030b0301181e000c04203408040d03443d401810a0107810002c03980480d0f1503204000d01920021100310005031200c800703201074504844950702401040440b00c855601d060002441083d04080c06410700d0759941a48001c000c1d101d0109088020f6100003108608000034000c114100c1c40e4091241586074900114404400414140c0201c1000342030f9030802d0500740802043c680041c1100042d4860700c0c00024141e0750648000d0000d0840c4200c0075054900301c0c0015040d5a07a0082820010004200708 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 89373633 1250 89372383 89372401
    0x90e0604032001050a0b100c02090f06030f030c07050109150f03091a15120f03070b0702070513020403050705010309031209020a051503040c05060403170d021606020904060e 76
    0x5521503018a807500c078414070b09600151040c2071010800c400e50801c07003084800c0100e80c0008a29683c00d031201c01b1840d02100084603545644c0000a42c400701c0d41022845034004003d149400000003001d03543c0b0313100500c036190700d103501c9a0607410080e00803400c04c220f15130308800980010100f80f03183d82044130015400070050944082000103043c3d943c9210010f0010300c440d01c3e5448400001d07802c0789410700890420810340445011445803303c0d482c1103c0e081c001162124902d04140029424001c01c0d41e0340702c0703600c1c00041c081c000318450702d980010180e441a2420725802040c039001699076081d42040350078030342960003407414141001e18160000e0340c01064800f01d80407071000013400381c0c000d2000410004203544190390042c100c003a039030711008141c0005d600983c171445d010300e80950342c2c0c070a21050b409940700140800116524a0b204441014004d2608000300000141f6001c904005003240303080a41055074035950214195004d41402c3c4140d1000c0c3ca03510b00810017510b060500303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 89374883 1250 89373633 89373643
    0x601050405040c1502030d14100f06050403081b060c0c0106140a090209010309020402041e170309060a17010e0f06010207050f0d02040902040e0a021314060f01020c04060e10090e 78
    0x9001e4250340080e070813070310f2600c2030068030390142c003290045c07080701d603007406005a825054919030b00703c000b00200010007842201903c0c0c2118a5030f110a0706251131501d80304a0381e000788180596001c0b40549009040a0510005104078801e00002d511509003030320709421151280c20000d05c409989408002690303d5018136022240000000346c0d80ea42c10b803004801408480360000e42090003c1004260042c40301065680341210b8003445007050703039540782011602900e42c843d1640d40c004026009060901100500c40036140e81003001790140f042d050700d007646909a01c901a803c8001041c048010426078406810000910042001030304080c00180741202d10f5030254412020000c1000854442c1c0c1c101104d6560020020131001035074000d0a85c44510101080b41301b80030203e07041c03605884621a940502500b052100c86540e18181800003695200302c5403410743c840d1030070715072541d40e440c000c4001070814401c6031215828a0640f00c00c5c901070741d0f000300c81c4007414140c40204440d80020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 89376133 1250 89374883 89374889
    0x1c08060f0301140705031807051005070c0b0a020a230705040218090a0902240f0f0d0e0c0f010c02130c09030c0303050909010e13060f020c0106030309080601050405040c 74
    0x40441010018800090061103c042007801042c0f0080030082c445400401540c45030b00b03551404008019242245901c51401c1d004403903000ca46001100541d52040005d04005c5100b0b83e507a0204545400c2001c210343c01000503a801a031048020320100032440c900e100803903c00b003141c4407040c5003803c01252a41c0050254074050b07680490bd0039100200952035405042010f000c1e02158200428950043d002009050b4007503520168428030313041940c000015003500451109052550040e58100c0d80c0c6d100c112062008581801404160f04091069404030008a0001c01d0041e03900f505010380c9231490200c150500441018540160707c92104134100224660b0340080d08103000d283c1520742001c00e07040508450301c00c0c3c00100805803c10f000342180c00c42290590a01d03a03803102d07000c1c603c000840703135600b50a0f0081c9010340025003a0b00406c2c3c5603805c0c01070140c10900d801c40842d003100c0b0207520540c005101001d08010108040c0402070151000b9203040c495032810740c40d0152807448a00c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 89377383 1250 89376133 89376139
    0x3010503061303020c10020a0c081f0f200304051b03030706090c0b1b01050907060f053106091a19050408010c0e09060d1709060f070302060403021c0806 67
    0x440a8201031003480817812440009000d40034020800600964842c01d071441110000301081c0c01007405080000c224581503030601f41401240301d0444808040e0071a4000148202e0304c510401102c01258000102e101e828006035540b40e1074103040c40d902c3c02c50360700c0140c1004002c01c0702c0140941c401204944540785c00c00130114031620726140c087c1c1c0c12101503100b40a140800300d281d003041d0000900100291621800034021510342070503030b6481c0c01030f030700c141400700f94102d10300c10b00030740264050803540f125600f01d041120304d00c0880760312080e0046440c4203d100501020312419800c400684081c02c8801c12030044811040a56502803103801c040242d40d40c88001a102243d104000b1600905009802803010024101c030107449c030360040712664459100030000481c0707420140310f420b10183d00400b00c03012203080f00f4104d001070b5000c0b81c811070f0025400c1052f076040c0d0080b40c00801e03515110754001d00240c0341c00d09000f400e180e1034020590201d04501454a80950301241441e0000b501b1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 89378633 1250 89377383 89377411
    0x80303010501030b0f0a1202030714010206040204050403051201060e01020d0201050c1204171206040615090b0306011101060b0307300f020904050403020a0c0611060a2007050d03060b0301050306 85
    0x41400103c6541c84c5ca6107155018480b400e01191120307501d81c00030b400c00d2003503044841d51500c48410078940803682910b80c1c010380c0030800123005880c0603040590024040d050440c640b083c1568034901d00b104c241c01003004210440c000441c01d59040140307041d0b05d02c0a20003000503003003d0100000c18032455030700280020031400850240101d203400406d07008250202c0c42c0d82c500c4030350301481250004541c854440e607d440b03030001e0000d80354655442d100341c02d82d8070840002d0808205100d1a00064030450410040c850400a05182441920003800381d2107c0e072512450144001840075421030111028045010101c055859004c0d02c6e0020260502102203a11800600000000d006002200703a2003820304007480181900400d402100364020601d0090242e2200c7e0f0035266004452044101c0e5401000041c0c800e405540c40880031001c07000b42c5150b4058003802c440d44c0d64201501c26201c6e40c003c03050342c3c603425030540701d03020040001d0f06a281c210362602d80041c2e102d02008200b04040450 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 89379883 1250 89378633 89378651
    0xf0703020111041715060108060d110d030309060f11120406090c0e0702010b0625021908030a0f0914010309021f0302070501230c0a0203130b030910050108030301050103 74
    0x2e401102e60341c4075204442c0d40b02d80ea80c05000a060340494154035032800745000c0a4072140caa043e00500c9010181c4490b18a603e0303036400c0c48140d1000e842c056502044200d0052001c2d5610103001180340c0c003964003c2810b034681e0601404403030fa40014040d0041c5071108611088020320261005036918152000840d602c40c00c050003d000c5081004103030250403980420b00c1c0b191000b4290007100954000c02a81420400b401410b10818940044a000f000c0030703030308000041c18140d140c2c680b01508000b00100411000300340d0308943d8010140e113402c08200c0d00c0071150b2050f10b849854040d441e04d9803079945400450006046107088160406031141d8050081d5110b0111301e19203a4030300c1c2c01e007040c0b04800d05030040080d0080c0e94211515400c140b940c00b090008130049103036130200c20031850340303d8807003140609140d4082ea50000c1940000c0c090319041300e4a10202900901c490304201d82c3e42d140c240d809500304103d907078403412240d28140051248000c0041600c2c15a202801c0000b042d5032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 89381133 1250 89379883 89379887
    0x1e0c0a02030c061303031a0a14040905060c0a0f0f080a050705190207060e04020304050706050c1608150a020a0f030b0d14010b090f0403050909070302040504090b0405060702120f0703 80
    0xc02d0100c0c451031480b9400903c0800401040e1004205001c0d03502000303240000e05c00c03000200045108a07a04c0040b112050040580d51a102919540d009000241c540721a80d1400d04080701161903d83ea554082043d40d8225000744807860080c401e4030f00b40040500d1200041c010341409048801e040e0ba903107002500d42030086e411240244010208400d0300400190001c4d074504541c041d8200007524a080040241854000e0368002c030381c0880501b4501d0b0500c04112855001024040b1140c0b007101c0042002c01d000f114558040c000d500c01400411500820389105108090030382a40c652042000c4070341550b05c441e84650048003032401007181041940060018002c0e0303c2c010b008810000440300c2e01820541c0003440d10a001d0b115400542d545a41c01296608111000350208400300000055854040d00035588030310076040050400d80c03600007090466441841c200c3d52005240144030502c503003004081d6008001d4070003000c2024000e40c004206003d00304581001200100e00082094 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 89382383 1250 89381133 89381137
    0x50d02130308030a060303020f010c020a0b0601021e031e09060a03111308150901091e020a0b04030809090606031018021909091503080405010825171e0c0a0203 70
    0x5030070101c0b10f522030400084100003040944022000341c802c05101550946040c042d001150603240c0103811208469162044840c400510841c118000d08201395003907104110800d00e000c80360f8008685422140b01100000700070391100c0041500c0a010703200180d583c4200315001c0500d145804241600b500204080600621854808090b00307a0ba0101e070f12400020f00b40310f021a00058640325031100080c443c222a15a41c1c0500400d40c04c52031202002100c501038a446440501382041d034969030118000c107504140c00403641c6420000303020086140c0203c5d8650046401c0780c040d455800c20070f031341810b02010b6200c0e40c05090010645001164001e506603000c1c1c0ca191081a981d14001d8800100301c18018001d0340103407032600580680030140d07030400f0411750f82e00582c101d10345400d210054a07102801042d24000b481c500a0140710303881009a80d4030001c2c05a00c031081011490b40111030901c50090420b0742640e504201e412125508500f403c1e00131022a900d03aa9400d0784420481c02e40c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 89383633 1250 89382383 89382389
    0xb03010b040513020a050907050f13090204120308070905090604180203010e0f060a090c0612020d060306051008030c0303040b0415060f0603050a02130302010e0604050d06090b070f050d0213 83
    0x51800c01004283c032000da404580c090710844250300b401c1c0c1c9a0040011520f02560740000260f414050302d001d500d01603000f000e00b060310125065145554092000682c0c0c400d070040d01821600705ea545c001c06410041c4030f0340021003070900e0302c0d030141890046660b400004000603c03c40c0c81d5079512014a020381d0303258045640180090101c550019413155481c60760744c0c050001d520a41c4d000421410052048044d130303692195a03480514541281114801070343c0d820821402d50800004184596500c00c2200a5100d00c0e8082468604007081071803079500c561045403250010450340308045404022254481d034440f680700d85940302c40c109811020700ca99a05401945404408107001f0710407000c0708d08491040c0d4040c8103d84d5411005020380c0940160703685075140600081c0015800350004a02250000e840242401d595200107001c42f95801800d0ba03000d9558001d150a00002003585036000045081680f100003040e50300030990303c950000091690350204440602c904210b40100007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 89384883 1250 89383633 89383639
    0xd1809020309070f08060921090d1505070f050412030e090a020309010b0a05030a0b07050c031206031002031b130312030f05010f0609030b0405070803031602010e0613060b03010b 78
    0x1a841c10140003642c48071503000f212100440040300007208080004c4091040b8869800f030702032341c000034084c206031000c10b51150006400901c0001c1c12034844898490720540030385034030320113507540c0c40e80c11040310070240c820410490980e07400d404560b005801c0710111101861550303000740c1c45040484407543e109031015440401c0038140903c004160b000b0318003800c82000200004000c0a040081095a41c81030742c0e00b503044003d495011aa1540c96158481c58508103103160034074854046d4215808418500042c4040c40c0912507541000c100a0390510318881085140d0b0800f1520320500108040000954590005456102030314100c0500011684110711400d10302e040003010740540305809140c6640c40c5404000180d210300d0913650700481c1e010741c4401c0855410342d150f800c10701c24014001d0b01e41d48528a000506075030200011481002c030640403800e84c4410000081c00d541302601c810b01940d004809000b82d50f0540b1924200b0664441d0002500c2c0000c100407a0150005408032a8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 89386133 1250 89384883 89384887
    0x21e0a0c03050d09050a050a0506031f080f060a1413050c0301050408071b0b09190302030a030e0a0e0c0412050a0c0303050904230a0207030903140109060f0504050d180902 75
    0x402c038000558186101d16500da2001d855140d0f02480411941d501c125680028420000c05c0344d400d00c02c0081d500410031403803e482556260711440410501980034100c2607100703506102c41040b040c4600c0344c00c01d0384440140600280e20380390b00da000c08050202e0036000000e401c54001c00800300481d2707402c0c40024002340043e01c0d1138203040756690022001a1034500000311003466010b030182c0ca51090b2040d0804080c1001512024007a1041d01c035080c00c80000036641000c409aa410801d140a0500c29540c000c84560014284000141c40c3d5006111b607201400a10044981110680b42503400d140080520040c95080c481d00e0200390b81005800311010a402106055005000b440040c2c3d080e2014011615440c81d00018040d42c4c09040c1c9040201101003520400d10360000c001560103440c2c00d071900341e00d0391038440d2080710400076a20941e640d025940c0402031140100c05450f000314104122a140944a0944602c0580410010000700c101d03080840800105090090604d00074115 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 89387383 1250 89386133 89386139
    0x24010e09030403050708100f0c0c12030906060905160813030c022e0f0905010813020303090a0602030a0e0406140411040f0314010e01020a050d0221040303020306090c0307021e0a0c 79
    0xc2d84071440420547d1070107081c0300100045861a0155080142d110b5850f02d0100801d1745500c4072041402a01078100b6444401000202e480c600958020b0b00c05281d00050382c0c203054041102200642844a00344404071007088588080e0041302c2102c42c0e01400d001d0101c4000b840000e0f00182040c0c07030550442c4244511215200a800400101e00041d8a1300d0b40d04504001b0f0694505481c0d1141d0f82c001480038002914200e00e0b150a00f80f540e1001d000c407030510006038001018440b00b90080e000607400030039a000700541c00b000c52014140d050f681081241c2c28900794030090800d06040c3d07400b40d500c1c4e0745401203203447e010440f4020100d08149554907a240d203007491042c2d03180340e2100500d6007420f80c00c0000a006208484442407691115864240104454806508500143c28880000c440201c0721252000d070407603c130b244650b40060b030300e1605408010282c3c00140401d081c0450620421050f5a000170303d0f0009402d80c03142e401d0241f052154141d02d48030828900a000000c018000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 89388490 1107 89387383 89387399
    0x20312033106021c060f0501170628180605010e0d06110d051f150e041107050307030f02030c0c0402090f09090d0224010e090304030507 60
    0x800100340d03071280e900f282c110449422404154500301d844410840c41854050034140406900349410440020100c2d103134221245214190f240201e9a00c0da525403803100b040421400c1d0404410003100000d50b081c42d20b2003040d0703070401d07000004c130745c500054050304060741c8040e135404684000013420094034030030a45d01599400d42d0307621500e00381ca0100c1d0080c110001000008070710b504003003981c2c24481084054003170f09520741140510261140d01b082c1e1140f0803441ca00049599070020024000303052840100400580c000340781401c0000100117041c509001351192645081c40f200c0c140d89a1290305400c80c2c494004646400b1207241540c041d10243d6405071405031005850304c046040003c00341c0384103140f58000e03a441c40d0342a504100d103594412806280f0000f141012030200d41010060080602072424880094090001001030354019500b1204035410740380d4625207 = true := by decide +kernel

theorem cover : BRFrame.Cov 89208633 89388490 := by
  have h0 := BRFrame.cov_init 89208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 89208633 ≤ n) (h2 : n < 89388490) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
