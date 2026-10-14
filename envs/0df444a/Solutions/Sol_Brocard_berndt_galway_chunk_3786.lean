-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3786
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:39:48.149294+00:00
-- url     : https://prove2.me/submissions/bfd1ab40-1c1d-48e4-b6c5-6169106b79f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 680755395 ≤ n < 680935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 680756645 1250 680755395 680755421
    0x1b0906070602070317060d0c1a0409021303050d1d0603041e03020708070f050612070207050607050319260403110f01090b060307210c211b06090603020d 67
    0x543e035540c5240040404491820345240e009006011400c0762405e40b6400188907000715900c0b001905004e00301106c400d0702d250100501404000020790055240003610f200701500d062018661b185040250401c245c04051404000d95044240c034122045400035400c040d041c2e40700c5840b41d0307031480e090070289030030b8108070030140c0d10303410301001c05d60300081a83c140c0c1c1c1c0c0d480640d000c0540c0c8408880c820701040c014103501100600030140e4440180500d55409030492040320002955440410f405a21401c4180c0d01604002003004200c0c03024048425186014a841d91041a01d00b203400300d9501e5074012050148410320109041c184200d24861207041c04505640013045000e200300d00030030580100705c61283c1004000380c0c0d00d182c046080170444410343c0580803c100030640c0c20f0b240c10100e420448250701080004900003082040200c5a8840d03650040d003d081681030484a00720382c80e9021420b80d102020500000d60b100a44400326001c6090158484008400d003002030046001056 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 680757895 1250 680756645 680756647
    0x90305040b07060e010605120c01053a200405060703091707060e0d1208130507030c091a01051c020c1005010e1f150513090e01141b0906070602 63
    0x100f0b0210a501441e6001070301c600800c01643d5920602c01c54032010b002000d00c83d0810048070086e03500500c020050118521461162a9403441c142095024800344000050604005912001c6241e05c02c0e07076020417440d0280c80b513040c0c0d1280742a80d070f0300c20f0b0300805008070b03000f09640c02090302407141071001d03000c0300f151619004104880300d81d960101e8810700002420500b6034a0250601044440200390421221442c180c103003042901d06040180043d12075984520700e03100032810911005026610404488400502d0280b2680555400d01415142d500200b01c2114144e070300311003100c8201a043d08042d44108081580340000d02444010190901841131280001d080300d03480581070b1500041c41c1407480d21200d016002c50421040000794070f1640c4403080c0258100d00d050300800005c945000c40c81c185d0000e0260b041202d1315070144109684426450070300140a020308120000384c440901043d01e00f00e82c0c00301c0d540070345590001e55100000ba0001880d110b803411035070040e030484015 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 680759145 1250 680757895 680757907
    0x60209040f0b01090906050f090903071a1602060622020c030c070e010e0115030911060d090b01050d03090e060a05030609060a05010f0308072d030c140607050d090305040b 75
    0x50040b12074003d0015001034030210b01402c81d442420241c1e20050580488002d8940500c610740e58050000340c1548810f000420014504484400094100520400300d5052660115000a84100c080c0043d900070b0420095642c0798504030440349012100780e550140680c0301444004e1241a449100ca8000042c482401c500e00003407840480c0c420b0309203482560390340e0704042420780081c0140528004044100c12005129402c0700c211217000d81214800481e0380340000e00c4691205c81200100c0d5191039040c401e10401c2c18056004010948006815520654008000c490342c1c1c040d516030180f251020070b15a460301041e80003c0d1101908580090402d018041c2d500c10040b90b01c0b402281c10500013168440300003841504070703039004074000d05119190343d5010401d0711580c03d82c0b000144a0002401002c0300f4507440c0030140c000d894002100d00c040c01c10100f800c0e41140d0800c22039100e0014024240e03800000c480c1640300381c4c0b0001601000514040b01e044c8916408140540004281 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 680760395 1250 680759145 680759171
    0x306010c1b0f170303060d081c050411010f030e031b0f0109080c0d030b060409050a0b03060a020705101b050a02100501090c11010b010815030a02090403031d070f1206020904 76
    0x10040503100c000050f0381d841c110081c512039491104030384440d0001101460800080d082030040d0030314a028115503802c48040000d448103d8004450540b038540611f900c00e185d55800c52804210300d940c5107410b1200c0c1c010413492681d03034800c0343c0701ca00307840f2a401084c004c0c0710740078400000e0024148000b40103448aa00302007900307401c2180901c15034041d1405101074240207100303d1a01d07040c05041c00f81098a0040c255008003001025070300c600c1c1c3c450304803190b41c1d5402d0152502c10703082203d00603181c19040c02d21600d0510380131502204c03940b905005505600b4000c3c98407840031828600b642e521100050f00701c0c200f986020a10381e01038101000855014220782041c00d00004543c1d1712010798804009050076100408146408152040f000c50380b065401840d00300350a901508131040340000d41d01040e0201001c44003500000d6503158121048154202c0d0700b800c0032a070100400c899410000c40103440070b468462080003000d01c4030040c2c200501901500e00c50540107000300105005244 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 680761645 1250 680760395 680760419
    0x23010e03010c05130e060d08030703090f0b190e070e250e1c1104050c090a14150403110d0204180b0f1b16030513030602070c05060f0306010c1b 63
    0x44d4116511418804203c000244400c1d510032140100f0502d00708150b82c44844040d8400b814240402d501e07504000e001c100c514107000441c51140d10310761007920707000c0d40743d0300c0b00c80320010340c89495800e181d0880d07080e20740000c0100a4800c1c400501d4400e0300c0d80561b4404044c03111400e0745890b4917101d026206c0c5030308003449808800c1d0540b051400e03d440303580c50340400583d007a0004c00440d0000307135000b0303581080c0e4000c41d0710140420045240401d0140004c64403005680000b2026584400c2d10085080c40081003840660b0070105509043c295031b117180c610141449054041c84008407003405550b9182c11071082d444219880d000d039410355051072041e1160489041c01c0320f103403082c0420003c89040e83c80c80910404c000700baa0070515403e10801c1070212150082d020800240403840320110064491700c002c43c811800183e688400b4940b04481041c0344c0c0c0a1480742409105402070308001d1402c5a034058000d10b08800744010501c1c001d60442c110210302d69101240d0709010441081c210 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 680762895 1250 680761645 680761657
    0x605090a051e09040524190c26060406053304030b07050901080705180d06020705030408030d0609020a0c26030a09030e030d0f0c0c09020f0406030c0923010e03010c05 73
    0x21148400d070110000030fa80c0306d0142540c040701600c014207001c8000d04140e90240070900100d15021544d100d409940502c845007611440c0300d04151030050003241c3c9890300c10b0400810094405035480c00c0d02c1c1c20780707144044c0044040c4002201502d000c210300094181102c0185520110300016410315040040640d0800c1d100d2a002c41c000e6004100b00a01a900781c03407481641c0b0300d0b00705401c031036803042c05500c5070170b10030444143e6000d00003400020300034400380000d401503400031a1588032800d181000e40310b4a62044881034410017003a0412b42d0702c02500c00d10b5580001c00b461403000501701d5402034410302d00d603d5903114004018404011085c0c3c02111059002c0e64440d80640c80b00c00c02c064907000c50f094030202117400c055507445e95038001c1c00c561802c240035515103902c1954658012080e64407009644040140000e41845480d80501c03415810310315500c2d2015016090980c5c51100d000001c0c0c90000c0641100c2005a46030f104580150f03c1c11000b90007440a040303210006070140e0050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 680764145 1250 680762895 680762923
    0xc0304090209100c330905010c140a0906080c07021518060910110f0601080303181501050415080a06060509061008071209050303070801060305010605090a051e090405 73
    0x83e01c800003900344603210030010260003403101113082c001c010400041510305000640e002c00d4001c043d109102e030a10810300d2507800f480000c25021a103c100606500c00c16000701c030003030f0042c002800480e500100b0402558618100b1340381c66113412100301d5060141d070900075886102050154542c00b04400038110f84500e40f01265203062242c010040707580200340e8030641003205000d1400001e84107031003800000f9180310581e46080d414007201c0742410002d81125035240c0c80003081c0a0406c1b000c042841081400c080135049445901c40c14405001d03061292501c12925503001c9090400ba4086040080400c803084070030303400041c54414003038401440380c24443d446030000100b60b414002903280001205030342d5112282c0d00c00c6010f968002c1c5c01104400c100d540c2d503001d000010001c100460080340c00d51501d40f5190301d8601c0007001d9401c16008142004814131800700d4644444280c802650b00450785d4400481c002c004003035900140007241c6034000540070610040c0100031a81056088103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 680765395 1250 680764145 680764159
    0xf0c03061b0306050103110306060d020c061008060c0a08040b0405160f081b1516080406120c0e21150712180b131a07030c0e0907080103080f0c0304090209 68
    0x4c0d0318015000c59054044d1004d01503402c00005c0d01501d8060010700c2460050f0f2401410210b02c54030032441d1000c02c80c1c404401c4147c840c0f0501c0b01d41d030204003142c1d22081001d1510f00d40005508010400200500020701a800a0b40403400b00030051103000a49a140506601704030303600c01405901032035030b10660019015152021142d00d181624030001303020b0203002141c001d444810518484c1d03200b54aa044510060300144000900000c005d00040900f0750b14942d030b100d007a4140d007089a2136425184240303d0704001102c81921208904554a142e0440c0c40c0031000f07407803030840e040c60203a1560050764942e507030800070810303001109020100e02c0f0120070030090740c80a004a03040010382001902d19600500018080c4903131400400089200341031043e8130300500b505545801406840b4000400d89585804d0304a95008506500038601201c01d440345040000001d41801170600001c0c00481000414200c420815000c1390700d403852907000c8070390b0303503035a0510311009400c0388c20341c1845100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 680766645 1250 680765395 680765399
    0x50f070512011b050c01090b0a020315100e0f010c02030105010b0403050f01060605040b18031b10090b03060603131401020714161e05090a0e01060b0f070f0c03061b0306 74
    0x81e052107a00c808644600007038200104400c0103442d02d40090b00300b030312659240c10b800300010385a0051b107800784011000c0940c903414940815051101c0203a95240204606c001c5818199800200d080f503680007610075040701008000104d959641011000e905503003801e000050400340140200308490180090340c1d5105016900142a65080d11031980040d07024402882142c1d00368004103a0501c1c0622141c881403852400b29090042c40364020042ca0440581c0c09064280301000882070304072841c11040440c24003412545034000a050107008003008130009a00c40041600056840c4d040015078021208580d50503001c5e500400c0c084403040c20016500e1074860b000121420f0715500800c08040d01418184481c960381c030380b110340c6120309003a10800111911410300480c000d10405402041003101211100d0039100180c0c003d20701034174100441d85002c0c075100700780c0c2c80ba240e02c1503d242c10501c2c00e0038403207085412500040e004914007400450b51824030350550308000050785040c42865 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 680767895 1250 680766645 680766679
    0x70b04240801180615020c031002070f0b04050304030f061e090f061113090b040501050f330a022a06040b2d04090b1e0405070c050f0705 60
    0x25510500d40004144078800610031940d80c100890203540e40c2180000c0c52590300e03030000c2c2540c412510504050b0700141c030213074500d042c28400718220116030101980380c9a9242e481d500000d08150003e0700c2010700001040800c1f41c01e00c01c4800454000c100740000310300c01e08209000b40300100c108040801d0043e04540451942d001328480d06811070000304190695840c1d51024041345001101071400c00c000c03900000003414440342c00b038a030013000000c40386407070340900003140c01c180c00641c8244d00e03604814106983c1c3c0141d0344400a40d800ca482c1c0000c4c4806011a000c1e00c100c004440c4004010802411555000518070110100d240981080c00c82c0b06c0840501c41559210050300801c0c01c020030311020b01024000c00c80100040450725100114882908200e00c001c3c0c1d15611446001404000726000b6004841e03240c88121440900d41e5100117100c03045031481c10596004546235800a07001e140030380c071045003468010050b2510704d142c404040b9100c07821801118841d2150b004c0c3d8020030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 680769145 1250 680767895 680767949
    0x21506040504030905041505150409050109021206061c020a0e040b0405060306131e03090815070903120e0d0b090d02060603030703030b1203040303050901350703090203070b04 77
    0x40d5406483d403920440c100006c1c800a802d00140415441061101c0080c00e511100c0c400080c110650544607101c90902c84104240c4006030b0003e135407070380107120a40c0540b5407006950740241d412903a00b0382d602c020101c7c0800542c040f40e8240001840072900c0c0350309580200c200442c40c4002c850410007140c0e500100402c50b4070036200b90390540e000300002890b4450ba02c41103007600340501e158044100070480d4510510034455001c4002544041c2c04020b00c141c20080015460050358614060b403a0416009010325402d2001811006d100c103400e042d0180111294032902001400e0328015058900b0095a6407a0980c2d68200611070f0003c00d400c1c00d48041802409040300801551401c4c0036a1012405402c00c41c0620794803180420300442070780d80c100700600c0154403a845468590310720070005070280d442f080c0d450b451480001d4601100e80710441800e1440080000010100c2d01da40004400801040714003d4040c85801c4011901c00c103503001030403c031442c140c00c0d004427058401800b0b01c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 680770395 1250 680769145 680769151
    0x170109061505031b1c0207080c0118170d2901080615160c080303072307051510080708070f090b09040b060409020d060b0a350109080a0215060405 64
    0x8481005416130b080300d0130343c00050103035172400905140102c1d12941c103a400c0b0b0b407100800303c2d1703001c3e0000380f140c404002c20300908015000c408000010004591a82c0c500c680c1808007640c000301d4009050782c2d042101e40d01c1a480c20091207070003c42510111801d050710300d41c80040d1408603405400040051805207601c06021040d440701d6030400c0e20103d41d03c14034264881d001c8174090394400c408241d0311b00800255129036a5540c511040106103503900c05c414034440d2034195816003c1145001082c4001041c02d0b201c1c4041c03414101d1070b40d455a0740c006215085d00608a1400350708000607044400289440c1500c41d4001405051541e44000b101150380c0750072110340250841c0f00160202c2ca002d0f82c2590312070000b030008a10f200c0b69500240b01c654070307110100e522550741e140c4500d440c00c0040310400a0042400703820543c00040440a000030b0040d1f8000c00302040f2843c3d0ba18200700207400c5111001d92059585480d002180b0019403a80100764444c03440c450684002141450140a40340c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 680771645 1250 680770395 680770411
    0x1080613030507050c2d040506090718080d0309030801080118030c0f15020d05240d0519030206071107030c030204110c0d0206220b0705030717010906150503 69
    0xd19965400b0345458004076000e071042e0096041440f074036261040c0d822a0070101c6400b4503150102d440c0101d881d02d410421070390107149841c0c2000110f44500e4286070b081001420321844d08242c1000100c403c010302c0e0001d08050040b00da402e540140c05800070b003115442500c2c4c0200607030301d0b840c4203801c07511201030480500001d44446000300b4055001080b0142c06019050b0a00b00c150b03d40030b0421103c80161040154002003160344901c60784980c40d0440f6241d02c2c81e040811019503040265520318000e240702d01314185080301000350800081c0050400005403195507030082c01d010391200300440300440402d42c001c42d0180c1903900030a41d1380580e035012a181055500319000d0100400580030740300341000f41081184070b068400c105410700803000e0303070041400749031a078009505540080c03907100c8840c0d6000107001c0001c0d10400c1c2d03980c1c0518a8030301244c0304e5884030001c40c2c40d10b40e4840e050465418541c0081050102c030740007501641d00c4804080d0340c04000740c0c01102e1030320040710086 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 680772895 1250 680771645 680771671
    0x10c1d030703080c030c03031939120513050106290a0e0303130f090e03040b070f0c06030903020d0c08030601140d0218040f110a0f0516120206010806 66
    0x480020b03c2e450107842000504821682040c0b07291480d90302d15070065070200306495204a10942c40c45a03801001c1402c24040c01c195440144c20003024007030900810343c02c044406c1842450b5501d4810403040f5401981c002c810301082c00c1801c23001d40d142c100e43d002600c0d254200741c004115100004291301c0d502041c0c59291050f050103404100c210b80146007000c0030406500e9001034a40d070204041c000c2e4070311a5410401641c078011004400428070751148032070a00702002e000c412a000320036602290b0248001c143e07501c01d44e02c0c20151842159400402c035801041001c0748095166221801041c426001c503a4911510007003981c5000d9408801000c2d40c4041000800c2548a580859143c060b08a005c50500202e001d0240c107980003064007074044559201c54840c2407816002e840d040c581800b80421064200600d980c1c1c10340300c0c0e5003502c01401021034044400a10985c1164004000c60200c1318500d18546404500181a00b58007030040c400e41001080448010030600c2c0140e8445200b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 680774145 1250 680772895 680772899
    0x6081306050702070302061b061f03030806031207050f0d02060f0112110603011503060b13030b041109040b0a23011206020c01140105010f0201020306010813020f040905010c1d0307 79
    0xe001c00504800841c041e0100c00001626406c020b404554512882644150a0000128903040d4001e0840012480000e40c440c8031002c0c0743c01a8003901c2c0c0600d480105c03541c42c540864540729201d5206504060001101801d210010900107403c2c24000192222101d040310100d913505000d403180d1100b00241c0c2c004000b0b50103031312000b42c202d070301c11400c0b121140107204c0010f0741d94200341d1201c0100c88400780f0300400d6607810704c204406401c04000580c24008680341d400b40c41101741c0002400581444041005c0c044004034080001c0c100034290310580c50f192800418190303081d00c4140c101c9013040000d000e092031210003410381900d9156400f00c142c0c40c060245002014004d010740300740313900f001007102c0300f04203005000b071685904d420000c85501d40301c00181841c041804002c00c44e4414021320031303944c1e44205143d81140d50b4412850f124802400024842101500d102d6800752402200200308101900310104204058846a103404008400c3e10b044080c00c0c25090361541040c0c100b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 680775395 1250 680774145 680774153
    0xa20070c0e07050a1b05010b030a030e010e012118060c0c0c140d020105160503210c0414010e0f1206150d020607080304080403170c0706090b1e31060813 67
    0x17142060030700681c00440c1c40202140402d0512040c090140c0024500e100d0b259107650704000d000c0609203003860b0003c8020b241086068541030410717841c0e0003450300c42507241240484141c2c503801081d0494001c20045141000140040c40401401c840e480c4280c2000034100110a00c0c2c001c0c1d001c40a8250003200460b6801180c1d190312164080d14070041d2040950b021071000c02c0503204400f6900c541400c494400304200303001002c003c108180181e020001070102c2486003103041001380d820b0822600c80e414030340016480d41d10010000b6000100b51400203001e1000050340da000d408010111481401c2c11000d002401e006a071002e50025002c22182c000107034000011a8040c0c02000f01c82d040c2901c3c0d0351003005510001c54281d8101340041100c3c4503640f0144100c40c000d0030f9600300a01303010b281c82c1c0841410700501c2803801d410035091204a82c080c0c25142103412801c0d40300c7e04c0c1140e08903809480b00130903403c6404007603485107818001c118540076015403401750070b0742d005203100072100d0b0792 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 680776645 1250 680775395 680775437
    0x711040b0d0b0c0f07060207140109050706030902310507020d0203120a18030507060509010b0f121f0911030705033301090509010e01050705030a20070c0e07050a 71
    0x1000700e00a030700030840f030b01840c84c01101402a6511404000d65500158204003592280720598801c0b540d242401c0c01002900004825080350400c2c00e01043d4030360540002038102020015010119506a215950150040c0461911403506440420083d168100200c3c0c1e40d0642109034400b680c4104590071500101d00ca80560201c4a51008900d04854081251075240304580881c081600418684200314141c01400d500c089404003c000c400f0b40350000400c81c0e000031403440c1c019800901201602c0e10144810a91401c03881201800110000151401010700354416a100500a11078050610300071079400102c40c002001001c0c400d20300000025107041c0c05d0180006404001c42c850030300d180c00524240200a018400901841d0249a560950302d010149441c140d00d08030801c42070f0f54001d42a640c000040303000015281c2800074a20098200036618079114075404150030081082d4007042c0d2058030034000e40c000700794a500b07005440034015040b405000c984031500103030841009074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 680777895 1250 680776645 680776651
    0xa02030d051b10020a080106080408040306021c05070207050a060503100504020306030f0d0807120c08190f0501140315010e0c0a030207060f0605040c05090f12070b0f0711040b0d0b 79
    0x512080803206000060b03510b801c00041031208101d03000b11710600410b412070074a03801401982480300f854607066860a10502c26408020310f225400b0519001aa4082800c0c000b0816200741c200b01c0b6040c6004083d43d900d4040c82850700c40c124600c00418283c0c496000c0d64028a1080c80410f0100e09003000c0102030b4000400c26031b00b5108010f14000f140c00100055443e0805945880455003441c3d6030003000c03040e90072206500745042c4005029920360216610707a0103069888a410000c2c0800d051401600c901018900c09505207000411510484620700c00e100700d0443c01c40340700703885855641d4440e820910955125880300c00006800f030002c0002003c000c0720920b0014680f99540e540c880c1190385034503056126650354002408503090600c01c0d40c07196003103030407c103060000400c001840740781e0b03403200d49026840c10000340380300c10302c204031680c09002c180d40a0703a11081c3c0d401c40d02035a40c101501c141d6162201c0385c1c2101013410184290740844001800c4148610226102e401d4000006 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 680779145 1250 680777895 680777917
    0x60506030a0507090501090b150703140c030a050301050405070c0c0608070309080a0509011d0d021e0a080d0f030c0903231002070224120c09090708010509090a02030d05 74
    0x30038034800040042c03083c03a01805003e2000105541001c21040072a449450454003c0d441e0326071480b403000707138081650720155062400344003802140c1c2c1101d0280c0a01d86021813944004202c03d50007a4205002c0d5058800035242040503a580f12807c517400740401e02c01030321800e034151040c04060300c00c100b00c960080180c100401c2501e1309503910b4509900600f11100042c4020440e21510760b4001581c0d00c00e2911104020204050440002d24010068200921076801c003428100316540400c90303c84069001850306070400da036a00c025449641e110b11500024008654841d172142c068403821503a9030310703655062000b50235643d4030000d440c41d0300042e07200010040034040c00628108504840200b190718050384a0b00d161050021188010240f00103865141d1400a0076520300300a0750b90503415801d000d5119124048910010f1041b40c6075203810500c0201001200c41d0070540990484406846418103030b03494600103512040d039418001c6d0315411540c19441c510b40320300042c20f044104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 680780395 1250 680779145 680779153
    0x1a22150e011701151706070206041205070611040902071401020c0703021002030706051015020c1311070f08120106020102030402100809010b0d0501090c0f0f0b0f0702130b0a05060a080406050603 85
    0xf6000b00c0860b890132a0310591210307140c503003840000d074410b10005070868600d00050a070303401c0a44d10502d242104880901c00c001000c06c1c0902401860781188480118a20100b070742e8503100c44a0001a50200c181035030900c450300101c41c0315000500c2142e100c01100c10182c807600742944d003040301016084500004602c410301a03c0080b80651098074003a1090484040c1014500310501c019444100c80c848159003001d207040c40340d44ca4410b17110a22100e000f0000074584074282900b0392a0043d0300c80900040000c02c80c01d0108082c075802030034000700c00652104d8517030b80c80c10124240c2c4001c45000b0b4011a580403d10102406042e20717903003040400001180644901c4045580380144134002d6402d07a44912800091003c0140c001010708401c50115034414103100458201440318030458803040e00000d000034842e070500058034401030b40282940c0f0405500113100003e8800d5990040c4101c2c41c0b014001003624020080300c01440043e2a01007056660752120002004014116501400b03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 680781645 1250 680780395 680780411
    0x6111213111c02100804230a1e080a0c03020c09060105160203010f02182b0f1e050d020601060509220b030a080d0b09191a22150e011701 60
    0x13480300c00d4003200d002c0b5980c030144940b42a05024607000889404201602d40d4105050140072010032403d0340e068003d440700c04000702c500904503c159190b00090a5000081030030540644d026070030801c140c1c0079a080303404070402d0030200001880190782241c0170880c100812450381d02004200841d090006000003241002035986c44241d0784003020200249005174401c0009243c844141c5513107844401d403400c2045030450184445180c240303c050210800740d104007080040341d00140398407020120040920040c0761038015680c21040054a001d40115000030810a118606403110690001c01c14510810058044400050302c1d0307101003c0b0a40703889003084152010031655600700d100d480f800d41d0ba10030b000d401c0001c540c0c0100c45240310355806030034041c2c900507001e41d148404801010019440d0100c030400c5002c10700c074000c51fa40040d20401c0d00940075060724400c440c141c4c0031040030700c40400c00e95064642104280904030b850401c2100500c09001c0150514800410300400010103a07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 680782895 1250 680781645 680781649
    0x30a1d030a02010f0e030f030601081f0f080607080c0901030b13060e01031b1421120c0c1507030e0a030819030e010515040b03070306111213111c02 65
    0x40c0c07050100d400981e455084207154489103100e01001c1402d9200694200070140b440d1880500c40a40310604110300705000c160888070010072400410700d5680d00243c40d66850402d698480032034496141705c0d02460703000400190241a010344200c5050032842d03c0e106d4013100540c02081c40800040d00591407900042e00300c0303080c6c821130010340403001c0a030301d0a6240d441d2102e00c2120040c04001d0703d0b51207071020080300c244480701d40c000d54011100d44c81d0040f0324050700c685060501445c01050302c1f40241c55a48841c2500060400c41c050f10140c2e0340041854092003d80a459412048107040411508001c01d10440c002442c542c0014405000d0f1607594844032000d400c40c09101c011090f80c0b0040e42c903840c0c2c240c801c00c110001048000d0209141c01408036440d5600380803898019915803001811603079040c00305201856021108000305a540040d40031607030030400000740340800c4e04c00407aa0801050001e10882940507402c2041c900a65045c008401922041d01c8104904031120fa0300503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 680784145 1250 680782895 680782897
    0x15030e031602030f0706091a1204140706020d020606040e07080a061a09040206090d030915020106030c083d0e0a02030d0e062b02030403020a031101050c030a1d03 71
    0x1a407840c9030044441c03030041500b0f0030038800d400d00555002e0345041107025002104a011601c00204100c059440050ba5000600c0341c050100000d84043c1d040004100c1070406034817000b00e02d80700721071a00e9129002603030381c1d0350450780e400007503401280019001d03e0550042e2008d882c001c0140c403001030356504e03807901d0f02c1c109030001c480f855151580c1c465681c0c01c1110352441c3c40340485a506450a054000c2000f81c030034404124059142e04802070700b4107000799904030040150104140c0d1110319090000c0c000c0050303020481e600f1540150016225400290185800d1200b0020941c0103803440080780c40328010680c940f10fa820740c4114a00c091080b4412150548043c0001d0012918030b0310406040c98031591001041c040c550303c40140d181ca0309800e5460040754100350304416135846c1c00c2800103880d1410384804040c000010841015800b2803030322140f074481d0302c8500305500c01200c118284e407401c8585440580d4103000050441c02d850700200001581401d11009504a00d0411421 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 680785395 1250 680784145 680784157
    0x4090311061e010b0904062d0b04030302060609070c080f03180f19050304031b05090a020a021b0d2012010204050d030e180114090606070c15030e03 65
    0x1141100382118030250090007059482070000c03040d0101c02c505808000c03000c000600940c203a4200201c2c2c08801d94890780d21441c050142841b120101c00e50b4205590000e82c100c5d0240c076180f9602c01000201d00d5031030f005440c1960340c0350700509030990381e1200780166120000c111307900b0405150000070201d15030308020242c9402c0c030000541d8a1810004d00c00069800c1f52229406a0148039400181c040120b000085003031a10307070001c20300b102400d00e6490745c042d84d04060301c1c070a00c0c14490180c06881c01109405c440d41036518503599564500c101c03041380a4429410090303000813102c4d2940c882c1349402d201900c0801400a1943c0d2125100c84264600b81d00e140c9403002e0031040c1103801c40c42e0082c3c031140454055030095151070308200c0400c17101d55016500900340090096014002e9550b41c1030f0102e21082c015400385a5a5070310b56121000c0306140406003e5050301300403d519091400885461580103281d034038005141c03c05240b2501038645c42070013050390307030902c2e034502000910043c11 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 680786645 1250 680785395 680785397
    0x60a0b0c0a0b01052e0918140601051e0322030e03010605030d021b0102010b032a060403120f21051b07120e01050904140a11040b040302041a040903 65
    0x40499420324101c2d40c40201078100621072850308260042a030300100d0550f51403003814010100c00505440161640768050300b04120740c040001289440d499940d0090543c140305011020341c0c3d803280302c010b40d868403844542c4c074128180c0004418110780b0304001103400c00059400220059210040c4e000200d1155200300d0024207148001c000500d024096038000d400b00300c02034011007014401c042d641d400500d0020004001411010445a00039801910b44040c060f080d505051800d843c5040d14200c01a21101030780e0030352010140d1400c0c40c00030396090381d500c684030100401008905460850008140c0801c00107440381002c000c0c600d402e849069078000038400300d050f00344105101c0c2d01200360800b1007200e060901035000414140400d58160178180e0400000300104a80103e88030302c110040103400038104050008001a000a036500c04e12030506e0410031001c0302141c504452240344940c2030100c005001c24030251074142e2010141d074000d4400d0282240045012a0584004d10002d40c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 680787895 1250 680786645 680786653
    0x303070f020a0906030f11010918150e04150606020102030106090501030905070306061d0112021008040807050a110418050c13140a0606140903071503021b1c030204080d0503060a0b0c 80
    0x1b04022120042048022007400c1c005036190a00603036580b880301d4180114001900c8005110000d6945452040600760038040c0203400d00e083d0811200310f0900031b041940c0c5038608400007501c50301c18800e41c1e050310450754070409030b2403a00004501030304e10342109035054050b142000000401512900b0020045034000311100c0c50a8102c0982c0200164010040302000460100041e91100c0c201ca5240499082085240c0c40d50b050000c0c903402403142c000c0c21442446200340500c10170310f00d01491036408640501c801c00c80551900741c0507080309802001c9a004010412851038881c2c080c07034002182c200e000801400c4071121101c01501640d582c1940c036036441041c0320b240d0340141041240030780758010350314280c40b100100e5a103903407030f10400303000d80e003210030006080c3c1c031171b4045414503030070342d024003c00041000601e40c0b26aa98440070703089182421540609030b00900079202100c0800c006090000c107800c006403801c0c1d000038811030340720804000100748039500c80003612a0ba14050010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 680789145 1250 680787895 680787923
    0x91407080d110102030f060d1412090906010f020706050904021e0d05060d0f0305030705270a15080a021b060405010501050a23040b0111010911090a0b0303070f020a090603 75
    0x1410b5901424400003160b4010810000c4e146040188140c001c42d05a034266400d121604118545013484200040680140f161008035503c3c1c400c051f091000d8115401652078484000565490a0b102d08034400b40c0c0000108110302c9004402908000380080c0016103440303410030300b01e50204401e188a030a0007101103040c280148041c402c5940c046004d0b00c121072022850340b40c40c04881c0a030702000341080710000008400512543c1a9490ba90f17601030304c07020600310000c2c04428062040b151901986001500082240e207002c1103622550042e1030302c03070050720703008209030123540819603000c0003904e807644c00c41080e5403c001440c0300b81d020320000169941000c081041402280d8810880c20a2611150200594000101003510421500001d0103484540103845494418002c44917075403070202d48001f0b010140b94a0702d0f94081c21500f05116548000702c500498140dc0c80d100e40550007840342c2030003e1589456215151300003080d244109a8906401081c3d55198104803460301d948016 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 680790395 1250 680789145 680789147
    0x80a0b0919060e0607020102041a03040f0606080f062d060a030b07020609120f040b090d0510021b03210403020102040f1502010c0905010807050d1b0216090504020a030204091407080d 80
    0x6a45e00031400d40700039031425240c4501649440c40c0d524803580741b60f4002022408203c5041140741d121a48070b038051020a40c0c960b48580c6405031000814040e00134040000e445034980d6500c0d10140540c1c40801700800c590200035440e940000b040c3c5900721080b0140031001c03030010042c40780f041080b60700030a91032800c2c404103810141d80811000cc8201c003800040e820349428001d450a4400c44000f05845001080000c2c864000c0b4580107400d0b406107140382101d1000b5a002046a074055200161150700086003007541e0f032041042c244d04000d0b4440c8002141c12460000b00c0d0414002c2c800542402c0d12004d210440e4407042d0311000503155140d0224072070640a0041d411030442500382851094036120028150060003007030710040210020b0203030004440344d442130584c03a007602c600c0100100c041070060354481300c001800782846000f003800039004080e030140314030030340d03010b00701507100b500e503500b404060901e800d800c68407240d07070051400c00480c04001200062030044000c01c04044a050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 680791645 1250 680790395 680790403
    0x50c0d05010b01110a0305030411041d030a1409030c0d020d0506090c0a27050c122a0307050a0804030c021804060614031c020f060a090606050a080a0b0919060e 70
    0xf00e110345c009440c0e13100440c0c0c0150959500c40e4120300b41c1c4160040c90800100100021300120000708001c4a89004013500080541b01340d0005403102d00100c01150080c40050058818043e40f5038003640781c081ca00e0400b4030f00c0c0320b22203101404602001c040f654489080c410100c898003125807060004540078034100ca005001000c0c036900360148940e00020003030707500102d01102d400c41c5484002040540524404a40305d00c80c404c004c0c0d62007400c11134480401e0382d050440a008400c0d09881249000450000300d902615194840d41d252072500c0509036030072500100250305021301954141d0141c1c890758014040340982c0c1103448924600340ca0000b044450580102a01030040c148249454a0010b103000351100c0d501403080c00c11001c0304040745441402e024a00480c011103050060082c400d8001c0c0201c140300340c0003400400d4890043c0b0025002601c21a29180d0004038040c010035605281107400c01c1043d004d403281440b000d441300340d181122a900310350b000da88108045408c00e00b40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 680792895 1250 680791645 680791667
    0x9020a0e240d030305070207150504080c03030c0307031b0b0a05090114070c080904020d020f0706060b07030903030305060d061802090a0b01140a020c030106032f01090b07050c0d05010b01 82
    0x40201d61000d508803001c500e071101140801020b2540d104007244003d40200aa60300410380c16004030b080761081760300101560058440c0300070a10031240c840c419880c0110583c1c9030408444019401c2800da0388084641c0300c1900342094400444018a101190101c41d0051007584602030205190501c10050743c00c40f6031070611880403c2540c41403158080d44a09000030081e00b00140b60b44680b039441c000380003407003601c1080d0703000c1d440003401108454400c405080c0d00f44c01200b0030454141c3c1c1e101c10030020b107d101801030024162083c2440028041d6101c071b0b401c018090241005881301c0d694400c1280c2a00b6803a03000800ba560305102146840c03940a64020f000000610000c0d000da800645040340808070030211020124011443c0f9100300a14952214014000d000c25603880c1440050300c9004104032500c142c0c1418040c2c40d00c2c2c000d2201c2d070023410061b910003004600e41580d81c0c009800200e0100c5041c06080503000403580e508020031400e900540000035038403002800900b8140e080 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 680794145 1250 680792895 680792941
    0x901060c200a0f0e18100c05121017010608030406200f010f060b09090705160b0f0105040f022b0b03061005040507111015170a0501060f050d060209010309020a0e 71
    0x10101a05c44d0500800c0308508044020000715828400382c20079580c0c1c1c024035031250321100f102402c1001c201c860792085421034040c070404600e4849129446402d90f40140035070b042d194020081001124418000340014001c1901210200480c0e48645801d00c8814907000240e82e444000651000400340302c0c600c01020081c8034640307440c440c42c2c00310303404400040c10001400070205903495440f0002c3c0e0001c2c1007039800390142c513540c50140c00d20303003041e9070a000307840c0190300e44403048900e140e40748200d500c40540c0c1c1e84171020340e240485210450300950316501c080680c840d007084509031410011240180c82d1401d0740030ba1039007044144000c8803030041c260001c214514031a45003000022800d81d40401e141c031800705107000c0007000b005132044a40c0c40040512034400d44c0d1034510401140303020304a4403860090000c603548401400807049580909640007000e00090400950300b075004000701001814040385180150300001c07004001a8003040c14610b60b60100030016881c01c80c405807000360 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 680795395 1250 680794145 680794171
    0x50f0604020c070315020f0c010c02010c080103110907020129040c020102040e010b070c05063001050303040608040c08030313060509120319200405040b0901060c200a0f0e 75
    0x4a00d010681c1c3d048940700140c407498403455155411102a01240d51074018209400d54500c0481041780c024031500c04e20400552810317042400035803048007014122a0803104d0748180303441d10400c10100060282030750701559a80c40c1c0e200c030304c0305c1c00180103008051071440c400c2d410a00502800182c40d8659600c00459104100c14020302d07155002c054150354261607840c0e210b0700245004034a02030550415540140040f44020907002c03042c01d24039410b01e03401244011040030704a2610009001e00846d580f40d0014401406518402c032442c903800360181c01d909103000c4d502c0d41504d0944c0d006503a00c107400070004084c0400e001d514050550441420b130011300e105840c040800c0361a000240c5406030039001c0044074100500340d5000500b8524030344102402980a084448030203a00c5480f41a001c2c41c10000046618034210f00098122001502e4400d420030203540c4220507000642c102e00907601c080b00b000f0b03516448184100d4080e14841144900550034032000030103c240041c040254021 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 680796645 1250 680795395 680795407
    0x105010f0e0c13060804051906020403140c0105040603020f040f030828050307030b060d0c03020405150c0c0420160606080a0c05040c0c060e0c0a1a03060f0109090f050f060402 77
    0x6810f0b40c0c06401c403406031a10b000945c40c1ca241c028180303c0c0300625003400101818400080c441554001d0080300c0c0708606504141c0109404180c0b01d11444444d1030110714280000c00085001c1d070020b1442c01886002d040c0b82c02c0e20340c003400500141c40c1c0c0090f00c09100100e40313200301c143d40040c50304010400740708005143c44202c900811600c8010702d54800c1544801c0c4900c6544c80d1030003924481d04130810180496440c01e04020029001841464410341c80301a6000340d485418045404030403201c00500f6150740c1035024030014207090010101d00d1031559138002651080000503101184c004c1c00303403454005031401d03e00d094804641001209400407010000007841804800003140e90556010444201c282400d54082c034641d10040d046a052030207580074030340041507104008100702c9420644e103850301c00301070550b400146c4d02c0f2600c01040001c20520b10300f4100f5810910030514114507066281c1040c60103864a141d28440e51a840d541440360016480d080c20b0b903c04403e8a007141418 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 680797895 1250 680796645 680796667
    0x2030114120f25080f0a0606050a060215060f120a0c17060610020106090e01020d0606171902160f0515070207180f020a0f03050105040203010f0504020d0e0105010f0e0c 74
    0x1a00848038a66103081682010f00042106403118003c026400030b50301c1c1c4924030f4000c0b68444c003e45004986851808002084a28104008600b55211507004200a0302521106c2d001c0c6000035040940c450040f52540c51547d54184140d03801e481c0260140a44246a00d000011080f5603007041540c4031000f0540c0480c03440000b02a5400b40c81240c09180115513001e040e8014010b542049000c24201602c14004d00d40540060500780c181c0c441c208030071035039907204560000700500d258140e003401c40f0102fa4000403104803854203058840c00180b4100480d441c40c9003080301c20000711841c0e529030808a05210b000c0c020070400c1d11400507a40341d2807503c030304002e44034000740c015206004040000100d414000741d00540c031803d44103030704558916080300c000e4000b0401198010009080800106444c1014002c1d42e04880d4040d0640c1e40309403c1108210103900815030003c5640da07100300c0c031212000f09019060081060001902c40039041104d5a159150010001a07035941d081016003840 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 680799145 1250 680797895 680797903
    0x3420100b040f15240c020f0111011a1e09061509090f0a0f06050303190903050706050304120318330507110a1a07050c0a0318080c01120c0e030102030114120f 69
    0x583d80c107d44d044001c4102900680d02e000b00380042154941c80c040c20a0380c1010f1108000c401132504484122100581c0d00074904484405081c40d070300141150f0224166080c0103100481c52941c80120303604002201d000724588140448030324a40d07181d148144620401076104440c194454041c040c8241401d19001c25503078440c450380984800e495840345058584140c824001641c1d0100c19128520b54540d4001d00c980c0003940c05031800210400301c00540d0f40248211800301a103c5502c0000b06407589907081491040000c00c201c2c5003800344600c0040348245211003000c088844006454203206200500e80e0440300c1d500300b21030307006c040d5032030205004802d030300801c4400d0741d0b01351a0741c1da41000490f00c501a10b825259140b00d0004028101500102612154095110840850395680003401d98403110f1184690104034407135001122411107030440c0d852790380e07141815610b4a030003202080c00c81c1e209a001c0e06031074611142900480c1381c1541c1c4100d01652500c010a0a6148041d0041d12 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 680800395 1250 680799145 680799167
    0x21c18021302041205010c0f0206130f081909030b1f030b04111305010306151508060307050a061706090c0409053420100b040f1524 58
    0x105884007004a11405020340448000e03003291190705a070600185001c1707003c0d00c4007000310b202003812a0b075a403c0e51440001c0d52403280014804104504440303441d604500890000299800481042080702c8491180b200107040500f5984003500b0300e2450429003d2a0f00203044411105940541101c9401844e081c40c0181c0707810080005007038450b881e1020051416101c02a000080c9176039003442d0540a0384124101c0e40542030600540f0080744000407004040d000e0200b8020f90310404000040c4200302c01c1c0c0d0311a1002d01101c442580f10030000b101d0784103e0f4009400120100c00610101c0e144055860300301d4402da80d08145810030a07d9215a409a40a500c50040c2e440000130310240380354521182e0310701c50164070000320148500d00b03641068446524030100d258000310b0001200140505062031040344e018000b0040d510300680003400c4401e95055100351226240580c0c00c800b48200143c480304080c0040000c3c2c9001040d40c000c010071248013001780c0703051602c55a041d40001e00804 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 680801645 1250 680800395 680800399
    0x203030114060f2101031202010b0607150603021207031502040b090d03030207061a01081b03270f03120702030909010b0901180608071b0c0b0703050418021c1802 71
    0x18450b402811080407601411280c190451500428000c003850b030f41e032a44d416a80100000382c011040d0b48002d9082c0c5001c00611604030204100120224460781070480348001d0001c00030403010740c3e907000141d107541640c040c04001e4125030000c00c1080f680300d0703480d02003850462040d41040e01d04a80700f109801051101805a400d844902c401c0610a504a82e0441d600400c01c000075400382e414201036400c018031013030100b800500410294036141400c183d580c0e105103003461455481a00b00744083d485408082c03da400182140003886506001903036003072451200545e241d100c2102002c0ca05400078000c0740542d0000c01c00c40304030361030b0300010b1819130f0707001044103940e800b00d140105c50400f10f507540b40d15001c926403004152603502072181406040340c0d5441010080c620200031008894070203004290103051481009080903610141881c54064184103080a94030901407503d41c00b4442000342c21030703000805c41a5200703104080300f406005203104100645180320301c0540c44841c1c00b401f0b4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 680802895 1250 680801645 680801647
    0x20a0c0b0a1103030108070f06022d03040305060c030f0708040b0a0513060905071829042310271116060902040f0b010906030c02010b090103150c020303011406 70
    0x2141d90b4059128100a0445102200e942c0d686d2540c40503101ca9050242c41c00c441707008200000ea4604c0026002c184010792071301140f10392008940f21030003802d001610806400709100000114071b0a01400e8810a044000190b4a241c40b007400d82c8808001880041030140c60401d01c800314100d01090ba9000824410020785503d60408405400c1d1114200038152410203102c0410001c01007802d508941c8940c50040b4031440708641ca0382502c4000d102c000031440120b541c0079810a452104803d00c00e00a40000f4030a1a45c0c10240c1c05010301c47c0039039846402072000d0102c95480c0a640c113000b0104d102e190701c640c2ca580c0c105501c0740d868282003640401e80b01e0b0140d040b14082d0201311404140319903806051141a898a0f0300580080402a440340d0719003d00d10714030b0f40b003e0107540b00c6000144c2d22140c00d1810900254024130110b030200c001c540d07840c010f0071026207034004504c0c040c60180340c5045c03074690501c0b80b0030b0030380d410a1121821500184010002c00717001c20b400f40c22595080340c4003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 680804145 1250 680802895 680802907
    0x605150f07060b04060515120901021602061e04080303040506060d0c05012d030c0e180106120f06060e1002160611030c010606210504030207120501230610020a0c0b 72
    0x18024003521b170011980b240f4a40c040400400c0b40070002e2025080084ca0030040d036882c2e1790450708078080c0c400d201100e901200d40101c010300d0300e40000c040c01481d501c0600035010700503204200a420607040498030313600000500080c00340800081e6440201182c000312062a655107141036040359100b00c80c14403442c0d0070880150100200c1c0646281030901c5610307462000300d000100601641c00d800350105001c02d12044050034000d2208000e0482200400003591810074204e44060740c032401424070316a0b03144121801c0f0210b0007030000400450f41c500001c5e0303181d035040091414002c0503007000d40d4880303825000b101c1d00000f0484c045402600b4440425800c01d00c01c1d6046100e6041d6a88a551a10303030089162070704444141c5104c0d603400f440480c200072034484802150300c1541d0180150380040c2c41000040e0080c4a805c2c0031512800000c22101d00c440a550841d0b0101034020300b080d00c1c0d120401581d4105204211081c9415100401c2d00383d0103070301c401400c6401c0e402164078150b000551 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 680805395 1250 680804145 680804149
    0x1d010b0616060f1506030b060309060f0c040f080a1a060a17240f07080411040b010306030203030d05070e030c092e06020f0105010e0601050315120304090605150f07060b 74
    0x1506100d0020f00c1310707020404851591041a008801c0400c6ca0a2100c0385503083c4042542c0c401c01781280145000e031652406441c400f80c0c01040458582c1c420800440ca00250701055402854100d00924110703025107441c04501d021aa4500000c00148007049600d96520020000700c80091000c8880c1c94202c3e03030030700d00784040041040051a01030140c1c05464100c1c0300503070301c19030740c0f080c002419807110391048509510544016041200c0900c1c107121914199019404002c1d050400048040c0d8070341c00300e400d40d0000540c00048541e00c000700030344290402e50421026101310041c040d01c2c04910001140d02c500a001000140049140f41c3c41c81d01402e00c80040d1404046000c51a40d131381c07000025600c0c94114034041e415400c040001664215000c01c45004542c1611024110764810901c43d441d19088043c10703602001e2240446600c81050008002519031841d000c12a14104020f00060407904901e801618004000101c0900341c20020390f6001988282d002c51030741400c0b40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 680806645 1250 680805395 680805401
    0x603050a0b04091e05280b180a171204121238040501120614011203081b0a0e011704020109120f290603060c0904150e0103061d010b061606 61
    0x150710b184511b04010307900102c4400d4034070703402c80e20650707201d542c0d650f900452004a801c0c07840e0552841d409103c440300007400c59089440d27000d0081e5186030815003d020b1211441c041030b40d00742c0700c00300c0300e86002c0c01d017991001041c00701070000e5500340b00c252680d0598101402c0c0407014001c07000e06140b244005000314407120f00060400078410701030b55854201c45034901959645c00c40d0420305e00250520010240804103049890b11546844423603c607840030717146480700800e551100416008111251001c1c100944401240c2c0e076941d28401c030399030001400d1b1203045001c2c00001c400c0c400402006030391055001060b6031809604185443c5546400115480841c4c00140074400400800c090142d54042c5450b885400b107480110584403a4145901c90405503904524103c0c2006211442e0034a5005403040607070502c00c0c04890381e5140555144120281c00481c2c020b920344004c4940000084541410703800901d00801052600800292030ba10507000c1c8200c20448030100d94062207107981c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 680807895 1250 680806645 680806663
    0xe1f0c14040905060a140303041502030910030b0f040218010f0504090f09170901020601050906030316050f01150b0901030c11032b02040303021002220603050a0b04091e05 75
    0x4803125407034a8079011560042e000c00c8818a0051018080015048102d8020f00c1c400080c003074080c500e002d08100f6015582041050544c042d0300c010003080f4419151014040f00c201c4441d40e00244a9044408001106801c481101e20540c014401070b0740d004004200c901c1030310024205200c0000e00c0c0d20080d01c09000700c1e84080030052410a411110080b240c111201e070360b2040c514501c0c07803000110b800510b0702905001c030740140e00842c01481981131640ca555048140142100d06045900140a0b100760b0600d008403065082003c465260715024003030b01e1441c03800c5808800c2c800303042c1780140d1518050901c0e014101070300c035440c45c840c3d5400f8070102103440c201c0c0d1050f20741c0c420f5000c4c103000c0a202c6503a0101d00c40c4040c2101c0303120340e11355407090340c0680b9415800340c00c04119000e01d480182d002451300300200c0c02561030b0a0700601040032000c0040074507803800b04603403604030803030380443d0280c5010718000c40c20418044d00052940c190040a144011006d91034400786041541c0f42c0041d003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 680809145 1250 680807895 680807927
    0x70b0105100c120837110c0106080c04150501140d0204030c0b2d0a030b0a0801060e09010608010b0105070f03030f020d02120c070224090907030e010e1f0c 68
    0x6407041640140c3c0714a01502c00d18000d00000c10320900007803940354070680e04034082015404a503c0d020a401341b41c03c090f101c20195043d15041c20055103101d030031510305900c1043c41ea0b0040000d00414180b0b0f0241010a030304d03c449086440d480c01d40040c04407030032030001c09a1003400054980541406a055030051508032608000a60b21120b42d840c640e48030307a08005200c1c10840800d001500440b1012040c600c4c4031510608104440300280c02800440844590000440300003290f0601c00344078a400500200211604c0c80c00c1c610039450031180b440e000540740ea4101002d828481c4d07040350442c0d0015a00c8100780c46036900c6800c08500500c580b09212004a00000e603a140c010f180340c010307008060b420340120038951500c05a040e014801c00c44029040001e01840c10200146c4003103001c800d07540d003401e1914004407140000c1d41c50204071071003004650342c0c02c40c88520600900c1108009900075000b03004d900e017284075110303511910748050182e03651100d07803294a051192030050200c54030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 680810395 1250 680809145 680809163
    0x90103080a2a0f0b0a1109300109170c0c010503060301020d060e063f0304080a080d110c060c030603010e060108030408010c02032704110c010b04050705070b0105100c 73
    0x40c80c41c22114204101d43c3c20740c4c6801c0300b000032882d5140280f295044950004c00c040e890000c582c0c051028a4a45030600d0400540001441072140907421120b060342d075002d40006030103405840d14460b0074101c100c41d0003a41c40b090048078448030000403c4400d59100742001c68907540c516001a002e48541040000409d00b41030300041c5034151000c0b4140900380845120048c6c49410203e001400c40c80c50025800c02c8020105070401200c401440c440c501c0b00805032071a040c0c4808003186440301c040000c643c3c4420010b42400c448401c0d04c074400520203c1102a4945000e210300c455880340050b0400c10400c00010220b030117540d0175031080c090710300c100068614541e540c42c81b8603180e030401e03c9124400d50802a1135000705101008072002c4521615452803c40c190301d2081c50702007400c06503189c00590f1201d120040090715006040c07408194000820107038071400512083e1480030b4460303002e001e41403003920005030740400303103038151813055820248542e1a80002c80e0800c400190203041005 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 680811645 1250 680810395 680810477
    0xa0204080a0f02030f0c01080c1e0301121509111203041511190206190e0a121202061504200f030702010509060c0a030b0307030c090606020705090103080a 68
    0x310100042e060007201070b5049107030300f200e0030382d01e688280c511356001400000001d01c02e80d02680142c0700303610340600b45999540d2802d08030115907100b0b812405240e60000c074031004001c101e401d0f10120500c0d15030148100c84440d076603100c11013a0348800c42e1144d4503150000200c0042041074a0040070840c07422100b00f0f02d2240090209080f00281400320b02540100c041c09032403840c8410000765028280030701d800282105405144103038551201040312480d00144c41d5a96045e40601400b0301d50160140e41c1082c1c030300f045010081c60b29203400c1d501324508001400c41c03568044400d41006907400f041c40402d1a01100c068800c2401d010300a04011990704800ca50607006103124a216800800c0070b600c8141086642c0c0004132254000d2043c20070424400c60311035041160002d201a04844807561240c4d5611030907610740d04a40601d644c1c1d188204215941080800700611054824081c15415900d442d0201c2c800c81140209000450a03014800b140e16034070041030f55584420b0b014621 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 680812895 1250 680811645 680811653
    0xf06040b0901030509071a070606151121030703090c03050604030503042d140c0307082d1c17190507110703020906030309041407110f060f0a0204080a 66
    0x1410100055000900c0d0000180e805d03000010442d0a8880c0000129040408242d8580302079000c100221002ca4032201c0016002124503100383c04422503445205e591107002d21201e01d071000b5442c0204500700d8050b160f01e62100c0100131207030401003901c0c021801c0619401c040c10000207640c0000c200c0e100c0c0204110505520401443c0514030a504c0d40b80c242c80801f5078110b0300c0b68128554003041000040d00c0300020103e21030f5035002d00511054517070900b0f030580002d00300324080d07011000a03000551100c0c2c0c14070350000b074040c0340300240071040400701c990044036545000c0f5000d64082c80c000c0003000350031680a02c080d01e0702c001e016070143c8800e1070182e40fa504001c0340c40440c0c113103181c21b10010444240c015052005030b068504014020203145400b049040780021784400e4043c00100400d0000b80c45502a400700e40e03541f00002e04090412407c003d00e6140800414a51500049414816000003140c5c032500b055046903103420a88480000c20024403555000301058864841c4030380400c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 680814145 1250 680812895 680812897
    0x6170606040e06010b090105090f1002010e16030804031b0b0a09080c2707120906020702030705010f02030d2a080603012d0e01110a0908060703060e13020f06040b 71
    0x490080d68207202100920141ca0343e12039083c0141c100e0403000740149803165114002a141030f21000784a800252050b42c0414100110b024081006035140c440800c0c21100c00c1120103812941034081d21142ca00e0350300d4180c054000e0380001403021441e8914005a401700b00c00c11009001c40d003040940ea25583c0101401c8864244114526401030020f102d81c10f16204c0d0030007071064605954500c1003900c111030051a138000401450500940031341025400e0154441c0039030780c91048030010384c0d441444c0101440d00c05182c0c03000b8100f00103d88031100c0158084142c0c0d902c42c05180c0d011485483c4502c03c00e2090340104000d030721140b07200c8400160503034000c0b40c51380200025002000940c2c4e5a40c0301100740184600c00403070b948010100c1c40c2241849501c003207c844e002400001d156403100c4401c0889030f120340c25940c0050740d103502c107001d4954140201604201c0904042140318505a000900d086000f0b0050107060310311071020065448000e040f00c020b83c1d00500d01c0340d03a1600c0704807120315 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 680815395 1250 680814145 680814151
    0xe07080d18030305210112050105090c061b0c0d0309090f090201020309100203070f0605070f030b030c10120c050a030e2103040f06090809041407080403050d061706 72
    0x144100d10300422103038018009001c003000c141080c0d42129041da00d0683e182c0c0d004008400300c241601d41400e5400f0b80500407203000c1e001035400300c4189061400d181307080d144098034550603600328582c5801036654000445560402800301100e102c00403018060a1201d04c0005641004850300c5400c00c0683c419824010b50340190820441018640d120904a9610500080c0564070400000b0b4251502d601d8109101c03c0c14412280f070400302d035542d40b4191050600440d900e54440f424005600c2c0c010780303002011289450204284d103100000030741d036a60220980c1e80100c0c0040c0a0a4805100d0f420181c01c004141c0001d122000100303100400507441994070070000791a04000d03481001011030711070314400314444016011200302081c0451680050811140c21001143c0000050b503a4065016800e016420081e1691401d5013804181c848041d014107101803c8420402250341105181d5000341d0103292840d110b00201d034000c4014201130f0040d400c840c0355181020760841d00066220f00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 680816645 1250 680815395 680815409
    0x4120813080c210f0703081806120103060b1c050c01091205070b2d03191107060f0b060c071809150b130c050a0e0603012106060305010e07 61
    0x58515a601c410640702d102040400c1d92102900b6050511000c41d500d00c1e952468800c0e050360100380c2160742c61840c008103039104030340c2d40101250340054141900500030081009a80705807401003548410b06580b00140802030800b039681900303100680305c00c4400010404209a1041e0031255810480c0c1d60300b00740c0f2090343c006031519101144c0d0004110703a50a149034850020b2a02d00c0c02d01550742000d4009807020a403070000324609280307101c100201c6007103c1400d004056038131704201c249100d808a852210301000b9080a03050403003000307080102c400441d0040000202034540841d41d1020b0420b52150507030040010880700000a03020440a080b03812203401c1d8101035060f0b441c850140d44041c0300143c0340303910401e8800d1018016810440c0401ca008100c0a00184041010b0084444c0341c840040020404541912490f41003000400c3d81d13082113650f242158500844035202d04940c440041d01c030340e070622400341000400d4008101540c0c3c01402402080c144842040c3e5500440c03281c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 680817895 1250 680816645 680816677
    0x304030e09090c010e011b02150a0207050d030c0f0c0e01090209030f06091e210306040f06080715090317121e280c0503160503131403041208 62
    0x280c2c00b2000280800c00300d181a141c0d01d4002c5000300040d00c8074410130304d55019524040c0c0b00e040040c0e032a902120451604224100c1d21303503100150017481c28200350003050040316103404a0010940080403a03000c40c4d440280307a18004020b1500001d11129607100c0d00480b6050720001c520404560043c0403400020383c201d4202140f43c108140e5180b03016501d19a507504a002c07044c03100021082c40c0d0304c152a00740b04855400c9044801c800410360909018000c0074004402e108503490580103024004152080034000c0604105c000d075203a001070b01c01c0c0310040c00700c040100146401458800020340e00942c001c07050b40c3d000903c001d850b5004540c0f0420a06841000400d100f4002c042c06007260340e0322a0102460f9143d10390303144890f100d101204802c0c56004030b50041032100c3d014070380c1e40034165900c0380d40b2030030020210320142401c0203081061000900420003146101410f81c02d226400041100100b821944c145055200d280c12803542e51121061520038880f03030200402c00d40c404110302d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 680819145 1250 680817895 680817901
    0x31e04080d02030f0301050f01051c0b011b02090f0901150305010f050708130602030a1103090a050606121b0a1a031509040f1202070512060a0615140c0c060304030e09 73
    0x2262030b40701d50941c0381c1c1c640da000d0005021f01d04080c025030002c0141070601343e20740084140c504020300c240c1c0c2c03175854203070b9120180e4090a503072010364602810011040901b0200143d400a068214009d1000c41c1140f54900090391480e07094101003031110541e48460b41560f184d00f0318a01810310550080101810b02c808548050302c2105d030345111340041c4250040d00c0101d0341d65200a0f60014010041c03154607545109040028a001180148009402403130541a9854854104400248031a00c240801003c801d411200464188032811a080e5001ca401001070001129505540c101c1c2110245003050207c0d108840b0f8010f6020310002880c01801080340300400001c00c4c0110342c028101d02034800000c3c0000d00c4110030f0b201b84000f50054480850300e038001704106035600a5000310f03a84c000d1050080c4150b40b84241d1b000b50298514105003a018010068058241980006820354001402c00101c150503c100810160000d281c140d403410282001011180e003010700c80d101d01042408 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 680820395 1250 680819145 680819147
    0xd0917042c13030c020f040f0c09090b01020d1b080403051614181b03090109030e03010209030d0c03020a0b07050304050c10080a150305030309060f10030221031e04080d 74
    0x72a00c01c14415600c0024440d10355400c6480310382c070000498204401c40700080c01d82d0340e00d0003020f9510507584030000d440c0310208001408245260301c600020fa00c0c101140c10b03141da004c038255006096900303110028581c04110718909050400d0050000000032801000b0000301062043c100814600d40346501500d544d0140d441002d51400300d82d20840c11107076200e40d009155075182e808821a01a00402200c50791000c0c5e0f076900440300d0000c0f2740d40d03c0c09508101600300d1a6021504000d400860510381c8840c00300c0d90740c4044094840500c040106882e080510810003142801e6109651402504168030b0241843e041900c00312114011022520450308103161100e50401e07940d698904540c0381c2581c240000e0580c1c50104041e5241c1c48804404a04200f00035030013600804010310301460525103c2d82c0031100900894544800c0790300402c0541d484184002d1000c00d500c0401402162003100c0741d00d588520380d514146629400001005001804050b0044810a0003951025501804 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 680821645 1250 680820395 680820479
    0x120307080307081f031713090b0321090409241a040e0c060c0307050105010f0501110718020f090415050a060908060103110402120109050114040b01050d091704 70
    0x101001041c4020001704089603c02d00108131074100d4610503460500d1300c04c070017403062009070050032501d40c8440c0d10355aa4241000004001052003400c01c0790140c04000d414914821621468407482c0c5444258080c06418949240001d00c1c0d040d19a14694081200740081c04224801400f000c44003220b01c01c66090a0080300c00c2000304101804ae00703c0750a0800800c0d402c0340c48a849103110601170765002035070034480e090285c02d0304515428060f140ca00010b04294022140c04c0c0207030040c000403c00c60b103451f844841c54040b401070150301c2d450a80300c006078a014100c4025846030504c9050070f1601c3da0704a481d02550710541d4801e621a03154001034911100d01c4c803900101743d02803001040030480904820100c0103006001501d0070401d02e1500d00420000c0c1c0104440d0781c2d13181c00401c41083d040780d401c0c04605d8142d42c18400b120000c000070303142c1d005107500301c10055207420260081200340c0391022220114000c08903112921420100340c924445900c0c040d480385220300c040103e42d0001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 680822895 1250 680821645 680821681
    0x10806010f05070311120c03250f0b060607080a0c02092202010e0406091d0f0111040311120d1709010b0d02010f020304151d010e0a1412030708030708 66
    0x10300c0c0c062400700f65540c04c0310120020b03000107000e4000c240c0030400410152004000d000c45510041d511501307000c0404142904044840e10b10b01300c001c581078001210b41e46000043e5030880c0412040d50381c0d201c0850344c2407184060080c00c2c1e03000095180415030f0440840303070515000740c9000c07100d45c0c6d0342140c031000c8000306400c580a1512202d04400150720030081e00e00c0460014101080c060758a940400694040101100940c2c00300440d0f9148c10b601045a040090a003030300038050b81c1065000d004052240d80005000001000b00e1406951030b070314940c0c1c0f01c1c81c3c581e13411207807040b0440c0303001051000c1c4440b40d80022000c2d140410b20f01c00b014010021003c4c0020060110082907600645d1842080403120082d03000900c800103134000ca2811400c2c5010041e00c400c852a84d20f103902c2190841110700a03814020308845464094940c0c000300f200f0703641020b04203000582c49000052318860220800700e4144000104c80c810020124061405101710340c80d4112075441d2492061000d46440d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 680824145 1250 680822895 680822897
    0x906180714131211040915180804030b010503060c040f1503021201090605130e07171c020a1202012d0b030703080c0c060406050f160206070c140f0d0b092802010806010f 74
    0x56114249000c1f0503920042461880035a504a40e41442d80e84000c1c0740c020b607005032151044500108a141002e00c032041d4080340c2500c3d0b80c1d00e003604140991840a0311350182402c528401404410300a01aa04031422001c81c490428250369585a03890050003280c01024094080ca041c1d141c6460380d28055880700341c6040c40a4404c5070305060700110441c00348c800e180024811a00c8102440c00c90300c0c1d8110848150b540030f030072000d1b028200424a402c0c1c07110741c2000c581c50000c590419041003c0450746404c040111ba00c0302c11006071041c0050040b110405505001e138101c0001000b0f001001000000310080030344205e07858020800031240203d22903c00410b90401c00703e200c0d000d400c00200b152180701106002c52007043d03008280c40360808001121800026030080c425400d0300c90011345060b008036640c054841c000d0010a59440b4100c400400104e80c9601084503d442400125501990300c0c0007144a1100702030040b198070030f20b220603400301c2c51a5001c6403507941324035a440720480f42 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 680825395 1250 680824145 680824163
    0x7020301142e140117040305070516120f151a180c030406050901020f0a020c04060f0807030b040c2705090304030816150f060509061807141312110409 66
    0x9400c03d00001050742000040c1005aa03403543e580240404132604c0c0a6402582c0e95615003005181251801e40720340314112000e4841e40c420444060882c1000518940c854800c003861403840c54554404400543c02c80140e03801c1165180c61001d08460071840d810080303c02400d40d107105800c0302040001561521714188080000401207500ca0700441e40050414000510f400708148a40000d40c11100c0e81c40e005170842b80601e10140380600803d405000302485c0751408514041582d0358030030262100409800d0004002000e100031540400014880c600700c02e5140762105807801184842c00080b5049a86803202040c4040b1001060b40d040e40d6001082910f02210501c0e6a480101d24020843e0203c00301010000d104009000381501c40c03540301008a51a405d040410801800c0205400c0c0600c690703242540d000e400a84045402000b40c0c20201040080100b14290610074a505250302948210740015030100c0e030301aa960b0751f8000c1c08005038070780001c1c0402060310b116030805402651 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 680826645 1250 680825395 680825399
    0x30a021501091b05130504052701050115030b0d120c170301080615040b0d0605060a05012c011b0f030f0302030910020c01061d040323040905040807020301142e 70
    0x13010b4001050a1280084a0b0000f195603000007420b94000b2a00e001e852110802c0d98141070041000b64460882000000d11007981454031903503d500c51440c034401059201c2e024240d4a84484a41c0100182c10500298070b61241d103001900c03020600c0403c4a1101e02400140505d03010242600d040e20301c0280078101d6503d55003803d42c103501580c0b24980d4816501d000190b590f0781d5040880b5a02440751300040350342d03c2c09a007000000c61b2148d00c05410700c4210142c4603114038240890691a05260000140440400004a4155810700105810420a00c0a00c0b041c8201c1080e0030766080d110740c0d42d0510290800008905a0005448240a0780c0c03180ca401c40c4040d806401611444020720000a01159949520a81200c000da04200154084c0c0140420f05a2002880341601001e0000c441e031150030801d50302d010301c00c52188016450b503c2011030200302100c81240c80d82c50300100207021440100f10081c0410600340c0d40c5804402d4042c40011007803034980318400d6026442000100214 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 680827895 1250 680826645 680826647
    0x180b040e091e0c010e041d0604050d090803040e180601030609021306030807060903050c0d05090a0f0e0f06030a0f03020d02010e0d020a150b03071503180803160c05030a021501091b 79
    0x406000f030100c4d8815120328410b40c10b0001f0020440001e00c141000302080c0c101070401508102074040380c1010029083d000b030095100000032901101c2419200344910758845451030144100700440005030700580c000001400103d4112405050003220b10402e081c4014602d0303403c450441c40003c2558500f40100c0340407803059401034603c3c50007820054900542c00141d141042c031002c007103002207440403551064600780060070314007400ca0030702c00c10b5559081c0031a03540b65800003030010035103a0005000450710b85040c41148170241d07002c12214803001f0b162a0203510364a100c890303400158a070070384a159403080020101100103094001d01002d124036141e0804403410a03000c40742681c0c42e0302980000303440410060300145601403200302036501440c4001c05455021031800a40000390f800500483c07200b40889821940d12180c10381131100700d60b0140c6140c2c0301c0b041d0140145c080420050391240c0c012a0034030002114810001c0e540e070702c920003441120082908410008800070001440c3c1d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 680829145 1250 680827895 680827907
    0x807090915030311010f15090e03090607120509041d3a110a0b0103050709060303090e0726090f06220201050c010504030924080403180b040e091e0c01 66
    0x42441354004115140f14089010540340014204018461414410000100070344601100b03600e414018620700b444403c0021a06c0c040c5050143c00388202140c890707940d40c0544202ca0304020050424072102c4a000700100a40c00c80044000071030003409140c003180c80c0001e0b240510882102810210050041f031220440000c50a1a4080c002030380c802e5241801d0401286401c1885106d4011456065103045414400360784d0003500b00074244103007400000d4104080c40d05940b020002c241e0150b485040882e80c009200b0403950600c1d40c081d554420785030007038101500c605201030031035030340043c54191569501c104880c151b000b4201c80d04505022801888000652801450200d0404606003102421220140d070202d01086003120200040c1d004580401b001074041c1600b40a450032500300039200c0c0d003004000400300980e60304546442c1b200d0042c0b4002900d000940b40351105d4031000c500c10707180c0003690002c01510480804031100c844904d034124440703058001400c42403103094019500c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 680830395 1250 680829145 680829167
    0x7090e3306030f0403030e06090c130204090f15050d02060421020310061a090d120504090e0f0106050a08070b0f0904052a0309030414030c06030708070909150303 71
    0x640e81000c901560380d5118409075015140340c031058100f034101890040c0481e400c20041c20242e03081401008400030380451084107000003525200590407080341c00b00d0003840b4941084001da8541000c1c00000c0240b030b07000c1c1410400344003e040d027075138884040101d03103558aa030003035002c00100800e1049459020444502044802c0036051a0a46900090070450014060590256102d00410400a00b50120880900c01c056110300d00088100030030101a449800a4a038a0b15142c540004c50b1146e01200e00500d802c0c0b40170001c4c2c00704044403540310160b09203510703484d6082020109080c5400044403003190a0000100240c524040e1394000d0b40d041b0b0304988005000600004500e91070340e002d1184a0340b800516041450078200c800c0794070018100300e0030395400081c8100300e00c075600001252300381c0f410030500c01650b0840000091915110404850f0003030740100c28021095008848240501d12580310000602d07107400b414421100403910211520036400790800c00300c1c0c010070800c46 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 680831645 1250 680830395 680830471
    0x20c030d05090f1008040b06041802040203060d14010204080c03060601200c04090602040e0f190b03030f041e06020c01020705060d1d2a030a02060901090905070807090e 74
    0x151140c1800044141c180c0884c0d90300898900002c00c01044800203500ba84590211010400c0402490a050b002081030800078040c541c00001326002d80c1c1c0d01c403404100154030ac42c190300486801000345001c0d400503c54250203104171101140c440c5804240755105038410b82da04060300c800306a07070305410407044030124418042e87e00c02c3c103a08d03200c5002e60f01e551401a007002d40c2d5245481c0c0b03403095a0700b0091001600c83c00380e4050090101c0041315403030b21072207540c40104440781058002415849400d80508001c5000900060601c0084400c41459050300d80b414a43c45c4d07841c9004e90f01c4080c00728800b8010f810040060090307103000c10180075840d080c0e0100082001c3c140c03013010200e0910741500c01032580710729060701084c107585c00920341250220340b01402c8110700310040b070340e0358040c000020700c1010085040040c5174071611482004104035074090000d41000300f0052700c0c1d810241c5880c400210510004142c0c044624042802045603680d01101c4030003442c0207074040040f0301d00307403c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 680832895 1250 680831645 680831659
    0x70e0108060a020a0917010b0f04020909010e070516060e0601050307030c03031d03031b01060b07110d141006080c0d111009120312060f0803030103030c050c090f0f07020c030d0509 79
    0x105403440c80441c0f014080d007050700005542088c200c20404d4014100b000d0300d2003680101708507850b584490303000d42e0445e0349802420003140c591a4080d915401a02c201049001091400380240022504003240e6084250f05444059807940241612034505c0c0c0000780c22610044400c1000034458024808001c00b1500382c0300018110900003400d40d48001400d0003460705200d0000c0010400388284002440021045072a020003603171041c00b00c07200e02c442684224400d0110341c06200c82d03810740c0201004503000355042840d81e25882c03401030206000e003248503c0f50004000690400061140d8441e40006880e428445140c0411410385c211441c08800c01a282a00049011500c40c25040361403082d2a205004500d14215100301c1e8210b522000800c0c072440c108004420000c011241540d425241980c0c0d0391038035051583c40e0900c03000c40590000c009504000d003c5007100480380c02904032907072b40049512041c804a0f42d45240b01c042e41d03850780004901c0d0a00e00c0c05180203128041c0301074001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 680834145 1250 680832895 680832899
    0x180105031e0703060b1b1501050109051306050409050a03080c160f030c05100609050619050d0c0803040e01030302010e07260f0d05190908060613090605010305030c070e0108060a020a09 81
    0x4110150845510001d514908500468071b15400380004158260042c00500c419854400000c008554070303ca001d00401c03510503001d940d4241900000d01421015005100c200054078000c0c1c0d0341c9403126410b034001001e5001054580345040203c4410941010070031801880035280d103441103034000c0048060040c0042c012002950600c0000302504601c500040ea07140781c105c160069580040c440e42c0701e400c0180600701c480080c00030040548030b007901d003301503804502d400c1503200103d0f080309016100c00f050010b08168a005000d0580384aa0f000340000241807000940d0780c561401010400000c1d103419184000740e00000041081c0c155044501400544180c1410854807410840009400044094580c94807040800b40c0d101c041c600090044c0c50b05107030f03684580010b09024422070b2aa10292090041504a0300c2c2a03604010708103c196580d181c0349940741c0c040326030248607000d5050700041500c140425241214102000380c0300326501c2194041c000d41c0000144010311800701c0300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 680835395 1250 680834145 680834159
    0xf0d0203092412250906021b0d03052208100c0c0506060f03030f070f0c050a0b0301180209190e0c130510020102041707050a170a030e2202180105031e070306 69
    0x49015601c3c4e55440c4d00c0b000f1401c1c2500203007041c58007451280300310710b8500c0c580341d030340c40390318101d400d20341c040ca09a80c9626510142c0c1d803030070078402e041135081d0507506000b084141010540d02400310b1803000400442220a400303031070081ca41074014110780c004100107040be0509001c55000e1a00040c140c030b00e04684611041141e4000e01c000f501e9511001e0704200030890040d4036032001d81012504012034a28044264400d840140107035801040c0004800403090010b805031440c084004001100c9031040c010040c5d00700711148210078001400d9004108001002d600302d403180b60304a4080042076081c001071008040400c2003103000c5640c00c010000c0c2c1201840c903d20712280720300002d09800c603d840708002c1d040b101c54100c0f070101c200200c510036480400140d592a45503050404510351358480e80004d030201042d01107000c4018000400900000c070650040c8440d50a441084034522110b4004541d940402c846060000c281008510541c0180221403a0b0000c41880c02144664032003607 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 680836645 1250 680835395 680835451
    0x1e131205091306080f010e1c17010e150f012705041d2b2f03040815040b0415090c14011e0f110f0d0203092412 49
    0x6094407501c3e43c42105002d444020b01503040c8a04040000340031050584400d02c0e1219400001c60001000a0003900b0380d0901404041c40550280c0d420401c42e03681d02d0a40e02030b00c1d501244c43c0291080130582140240c50050b1a030350b00f01c0c40607560607000240e41040d600032681c04014401004a0f8003800040a035503078041c40100340c07801a600d28822a502d00c1c01c0e03181119880c03a104100041c513030888600403d6241c4c04800d15914038040708455540c3e00b1201101b81d2100e984094451503460305403804400000030030881f5021411a55402c0b501140c02c079800c9800d8038002e01941c40c078000f040105803205510a0702164007400058030007a503607514154507500d070380010318039500c11541d03c40d03c4d83c0000112403186041d501c2c842c2050621040103004030b205541210620241c034804506058042001410640e48841103404007049032201070750740c0d0402d0782014456030040c2c05122120b21440020403103e041490a0350900b005a814a02400070051104c2003c800d4001c20240030000c4074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 680837895 1250 680836645 680836669
    0x90f01260703061d0d08010302150304020105130e180a080301050103050c0c010507200f0604030809070503060c091005120a2013030c0b090d12021f02031e13120509 72
    0x41c4890204c00c090405041c10b2411008030320050000d000300400140c0c07104091078510605200c1031990b40c0d0703500c2c40180c41d2401210452582280c01d881e010030180c2070b00315514040d0701034803081d80850780c0c003100540e52403003108001440c096040c0010400c81d4000c2c1c201c0c68015817100d05135424410200210342c2140c008840500024440d203034900c5a2019000100b0030114803003015000c2c001c2ca4001031555514090401010446000d00040c0c58803018803009000c0e040082c1518617a0501445503440d41e00609581c034412000440c814180601541c1100c0c41002210b410f00350a40c3c2c0d4080100040040c058140034460010924140c05118000140300701c00b281c0500b00d1016045040c07404030500c440e0460080140f040180b41e0b1260340b4055920b15660f440943d8058029055208a040882040c4e80c00e59070404001009008030254000d0f5200c3c901c0e111422805151040382100c01c50410340d0700803044840f24108002140c0103110102d074842a1781046071502d0944408244908020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 680839145 1250 680837895 680837921
    0x20714010e0d1e0602091302040608040f02210604061104030b0c030408070c0b0a020c040b130f0f18120e0127150e0901150503010e04060b1e090f0126070306 69
    0x6a4a006c500c1d1800100740c807141464811400e05082981c0a001080040c0c03020b007007010700c44004803c6558800b000c13480e04100d02c1140055400300d04240e56900703000c2d40d0413600603041541d50703410302c800b103000d48084a8200f100000183c44025120400d540040c109503440441000740a02244901c14070360020621541160303925031644000038100019034514074130650405400f401160740d489a0496039074040440080c5081c03900c07d1340c0005040c145000c1d42c6441c10000700d60304000e4164412443c10f400341c100c0300b4070800201d604540442c4920182d0340401d803000248505800c0c0b1078580c080421000d601d003e003003922081e40702d0161540007682000640810f05440c014141020424010010302284030040e521001e8098070ba0b00050090704d026295a03000142846000d4002e41156040541900742c00340299a41015090180420034090300544c40826034942d640802c030b034101c2d4800c3c4001d10400c884451524450340341c00300c001340e10b403244400200104080b1302c00c101c500480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 680840395 1250 680839145 680839147
    0x2090913050f03070b06010e040e03040b1b0d020c09011e090b010c0f1103150c07120203211b0c0c060c01140a0507020105010f030309030303091a090a03020714010e0d1e0602 76
    0x6c0c00100a0141d260000780107900f80106078880500c00410781c2c082c1d600054215844541c0b802910090b00d800390205455845440760700030003250003040c010300315a0142e6018466a80740c21203004103c0004d4881030341d044048104000ca61001c0e406204903480500d0030038400310b8a910f40c0c80c0d0a1105450607a40f907443c51803c400c461608101150383c41032011202d480324178225401050714020303c1c0c00a0403c0c492040b100e003107544248101e60124400c1c0b04224010341c10409140c40c01d6104441600c0e0400c2a40605112001803000b80c82001103e07000400400130404140020341d0403002c8042e20340d41d01e4440f0b1082645242c0b004c00e103c2d0208460000380c61501150082c2034030011b82c4142a070f1441840e052000c260f02c44c00c5a0103807501400c01251445c85441e2800d50912007100da200f5a84a250501a051101251030816540240c0c01ca40361a42c071901010031001000407024003240c1c41440c80521b40c1800a05000c802d030280b40300c0c800d5941c042c81020b881d0103403a20200c070340c558 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 680841645 1250 680840395 680840401
    0x16170403090b0319050717040206030601090b0409020d110903060402040b040e0a030203090a050d02010f0c1707120e06041d041104110307080903040621060807120501060902090913050f03070b 84
    0x28181c420175605c8000c1c4c0c039041038110010400c19500d601d0113040680507110006c000340e1240d015100d160000e003054880395a03155691540440250042c0707200400391401c1c02d17400b0904184a40595a00842c001c001d8004c98450346c1c20800205000d00d10980c005803903d1074072000427004e021407000c0c54080c0c1c004d1645d03800d503031040004c6c400c0c150304050300c1080c54052020262f640403d8201103607203142081111000c140c20810543c8541a1811444000028400741000150040c81a42f4101074407480102000c0c01c00b00005130040740202011103421390202003243d1203407030009403c035000d03500042c3c0c1048a080030a00b55070812004e040800400005e0203c00307075102100d0b5520034001405141010706160b0003d0861011441c15409a4407400982c000703455580c2c8100014150762084901603552452000703c10410b00d481540c90b03510706038001075002028021034000310801007034001c0d56941d205107190b5008500800791000e215100d000c82c00704100b000100400ba00034020340e0240e10f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 680842895 1250 680841645 680841691
    0xc030b01030509010912050a02010605030d0f1709061303180b0702090a0c05163f05070c272c1603060c140d1416170403090b03 56
    0x10b03406401440785a141c0061207001c1034000307801c0083c4403e00c2c50019a41c586c488401c80c003501d0150026580340c0115020030780f40355001403401a030003000c2c3d1101c640c4544042290f4400440c2103c82030360b541c100000040903806514082513045109007802910b14400c3c101108010555400c400c401d03034400281402580b0704a803030180d001401080c00d02070110840e1004141340a05000084140300781d4107802c0400102208595000d840030305914410151110002c01c05030724400390300c010000c004000b081c414403500c12a01c1181d0003010481c81d00b485c080f244100019244140d030340b84007030341d01c284000c05124000c49107903d0229618002c0c0d8260030b50b20b00c010600080109026078440c0070300c1200c0e55003035100402100c0c1c221000040c441c41140341600c0d00302c500702255200560003c0c10303400516465000414444455042d07070159070350000d4024585031803d041101040c030198100c500c0f0b0708965000c2d87c0c070a10174a0300081540c0c1d50300d000c0300c0540040c0e64100404525580c20803143c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 680844145 1250 680842895 680842901
    0x20301061b1203090c0305030d05040201270b0307170c0c0c010f12050a1e090c0e070c060e1606031a0910030204020c1501030c060206070810060804020111010c030b0103 74
    0x16241c0440c0490804109035214880080d07940321840c01e03d07072681009010b006050181c14029900301e41034903503558002c42d00c00005e0504a40c01c074080f070b00034050055121006d82ca04018001031302901d42d98207040082131042600010314800c04c00040c0482d03020a000401409401b03810400f40c41c1d03071511031400f483c03402d1601c8443c501f41082120b801e10700c502948140c200c3c5043c890f080d00040c0b6034550402c1400580100360240940e0b10310f08807a0b5011400c5a030007200294010f1224072000783e02c030804210450020781d51080041c81c400c5001010590396440801c40d06292021141d01e40944003d26120004a50080011a68403c401090012810b4011a0f80c00e81151440518905a031a201e82010782d4000680500d50100300c4141d001c01c01c0012080782e609a00740d1003455a900e2030b00004826081c001e0000500034103000c254190300800038540110184642c0d021003509010b0200ca080d14014002d0b81003250311500c0c54201d50081c821000840c102c0d0760701069a120341d030005029 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 680845395 1250 680844145 680844167
    0x120903050d0806090c07062004090f06050f21120304031d01120b011803081b0606102d120c090b07110604030501020c070306050603012a02070b030a02030106 69
    0x207110b242820400c259495072500c03a4404010010181c0380d100d01c0c10410020605038118203c018100c4012101c0708402c0030151088401110040c06030361542c4182c5004d95034540b0481b42c02800000d1824800c0c940340043d04607140800130540340000380456203516003c2040e10740d8003481c02c0082030101741584030bc860240d42c000c100781c0e4071284003d500000c0c481c21030504081000c56440c40c1000050b0700ca260262844003d021521000b90348900b0508001d0b403007a885140000024203010300200c001041092081a00802d810000d40601c1d03026200e04080411319984108120001260590010b02d403000000b850340d54a81214180302400e401c0781c000d00344041c1440056001041403c02c220125528140d010001c2c410184031a004074009001c2c2d42c0000300654004181343c504400005400b0b41103a00030181806103440d400c0900d401c8850a000381c02000f4109000c0100d090044984039005000901c1102d022656030786c00b010090704113840140746c85030000010405c4552003c40411 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 680846645 1250 680845395 680845397
    0x405100818250e06090c0307030b060c030c190b1b04051f0f1403010b0c160b0919050d0b0c21040213140f0c1c020304032318030109120903050d 63
    0x110f50400b0703c000f030b03900da000500c0e14444070b42c000001240700b44a50400c081c0e4000140034184c4804c0c0210f070003038498000060300c0000e4812681490201050300305050800d40c0c0014040350a911180e200c4605005a09081c4a0b1004100000103c507117421a41b8980c01c00c1111000360a65404d210080c100146003074504100310304507071500c140c45501002c40b4115139811b0704660351800000e89a608100d4445404507542030f55450014010601c540102610102140d0340664072103000560103402c5610700030503030003c840d02c803e88001002d01c0c1c0000d4000003612a001d0424018040040a600c6504204580341c0008401d00c4210f0400c0f0042d079240381c003014820710980c030a07040701282c04900101004400302c020b802140c04503441030100d440280d00300600f4102602003030481800b0350b0054a0880000350030101d000205c480380c20038141c1040c00c10b07107040c0c9402240480c0815190068005d150300d03559070020750300010316100b000042040d03a034451400f507902d03505000341465101070b8100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 680847895 1250 680846645 680846669
    0x80708030609090d0f030f0e15040507050a060e040c120509030c0105241c020405070e011206081b0406080601090e12030f0613090c09020301050f06040510081825 71
    0x2003803860f0040300c5d42800e52101d00d40002e02502140e407040181c0481d061009481c001c420518a0a82040030700a02c100c1c00b41084920840e516418840d400e07900c0d200712030000d18072001c1402145041c4e000807004024500c0c25160441030340c5403a20807100151140e40d150b034400203815210000070700555501c5829110b454040c01c01d00030402c441d816160060364800c0c0c0007030003c13403000702c803001c0c08503842034010340100b00c545400f82004c0c0c05070345508803081c0802d05c12149400003903014003c401c140c41a10000d03100c1c1c011075400102c4214000c0903525803050f1a0314010605410400006008115140e008107814100c41041c9003040c940c8244d02840744003c10400a40250039030116403c1001521005d854026820a940c000c14501c0402019400c4010f000607540c85d032500034605894084031b080b018036948808104180c81140700345500f0002076107521808500800307a00e5400079120350158038000325501e41034200800c9072000c82d00703080607281601c1c80342290030a1a0142182d01c040e4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 680849145 1250 680847895 680847913
    0x130e12040f09050c2a12120c0c1002090303160b1609030c0302010f0e1f0801080a1a060609031606120e06181c020a050d030b010804080d060308070803060909 69
    0x4182c070352140040507250f1245c8a01c403e40501d40b10050b080f040051343c0c0c152924620003180039030065200c00c52900c420f40611010860608420040300e240c46a8000180401141c80003240040d404c0140b400b9030600041c000c510441c000d405103c00c420780700e0700c916030356403078810743c0001d005000000000811143d07143c00d00006078050003043c192138090034102a040042442155002c0084010795000041c40708a050002e080342000804a5440e4403840d500d40e032200c80c001e40d6540c1154018090a00703584220780c1e08403004981d1a00840080c040c07501d8039481501103440c1c06441207402c240c07a00018410042070303610041e40c08092407481424402f03288141485a41c2e100d018041310b03c000012030314500418000c01c003040d105000200010f02600c08507401a442c0d403844001520700e4001c00003044c40b050701c20301c43c40d0440d0005868030055502e07251180c1047c0d4001010304084540c0c0c0c2d02001c07002c00d80c10000740000902c904a000d9891410105010b81c280000d4038245140d8002e242c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 680850395 1250 680849145 680849161
    0x31e06030c0a0f09051008030f0c2404020f1f1b021002033103030305180d171305060c0f041d15190909020310141017030702130e12040f0905 62
    0x100e0710214032000e076485e2510a10f41d2001cbc2000202c00c24102d002c0340c00903603003544200b1408020b1085001326810703048002868140010440103480f5103080c20604924040c405000307218804440b4421004080b018100c0d030b0114800b040141d41d0080542d20108017a000c8803400e195500c0381962054021080902810011051901c5800014149511100041c445148406442003041c4448080343e2030b0962490300948141c42981c0c0303502c843c08110000820500d040d000070714045030f21600904443c2d43d07000048806800004000c8403145d410400010360030b040c0804824603004040800300c90b0309240c42a00404090000182e001d40300e410103810348058480011f204803204600b0105613810a07200003070520001228401940d13107403c100e44109403440f1581072080544102d41c80031592508410812424031030003440081d441080100f0050418080324201c11004240100340c0180c030340c0f00e050a201e55440c0c110009000802c040101c4150240c40800a14000200b00040d090200f0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 680851645 1250 680850395 680850397
    0x3030f18060a0209030a06060b090118050d020402210a0c080a05070e040f020c0f1e070b0403060f020d0e2d06011a12040c050307060302031e06030c0a0f0905100803 72
    0x10001d40480d41c041100d031605d850a10441a01d6940808100506038460002101382e41100c103649001440d0005c85642a092100100e42910b000602c142c00c01c1e081c035400c00019500c8802d100706200d0210090507a0012500d5211307014480324040490b07101c06650f4018180c2c40000e000708a007a0608050120300d03904840ea5440b10701042c1c9000caa11030201d114a00a446a42410507091240b250300074190540400c411050350000e6000200f02a103036804982d55810500403040c02e000100b00420008035203910103288991840405400c01401c00640e004540780c19019941903000034040c04c252542d604042c000c00c10006242760420ba211030b00b0941d981d64140200d00d80c1440002b810300000c08950f0680d0079090246003604183d01c1c10b40380c40300c0c000c070712841028002d101d81840400e00714024000d03280b050810400b000505a0300c0e100e007000b40040079001c2c81d094050104100e485440311000100a002040402080103150810b24003c4038801410352051007541c0c032040c428040088 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 680852895 1250 680851645 680851651
    0x8040308030f0601211d0304090501050907030c080f1005130212220f050a23101a011d030106060203121b0403260412060c0c030806102003030f1806 65
    0x14030300040300a450b0000506d0441d84803141607407484007140000382e035255504003e040c1c4000380e410386a1a140d1880035000da030140c944800201300d0010004440d6014568036a920070b0050751402c000716070b11070100382201050000c20b542540c0009020b00d0082c481020f00c1c0c3c110b0303d101e0320943c2d00c1c2c00c800c2a11040c6a0150303801000e004584150400f842020000c0340707100d81e040024003044c0d0799007050b1921091014100c0d00c10500450010070000c11240c030130480c1d82d008905d440c03461101c200c001150f01c10300080781007001d0002c0b4070407003400751030900c2050040c14040c0c004550f41c0e40c03141040c05c49084001d24404282090050304040c280440c800e0718100c0e94054180080ca24a0030176942051400003400f1100d0b520100b80003c014503455a644002401000c040150b62a11401103641401d03021003c1c1c08541c80e0f20200702c450400045800000b12503160000407082d44150101c118032071b4480100d20782d030002c001d10800045103911182c0105290788101444461040c0c81600c5407802 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 680854145 1250 680852895 680852957
    0x309021c020f19120f08030a05040c060f120506120607080105181302010806010507060e0a0c1401140c0102040902040902130602030307020c040506010e031603060c050c030702040e01060308040308030f0601 90
    0x386030000d00b0010900788980017580e105403510388a1070055100c00042208842c140e070300c01c1041200251141c010050318103e80c1183d0303160710581c16074a01c41809414090b041c0c0c0e4001c001001c1e92500070b00184640d82c01008a51b17602c000c0c9514100811140d0b80401c242c0c420201c00200600c02c8160b000d80f120301c0450303420b080c00240c47e80c514005984a00032030314080c00d8181016001603c0320300c0030607040b60700b9101e00000b80420741c44486540f013180740700350540d011640c90300384481d1104000c405022004c041c50000f5142c161200c00c07040c01e0380c0165020191507900803c8062000c070766540e001019100506c021400d52138200802582c924074004d010b8019940c0c0d001141403644156091000c4500c058121081c0c4149490900f464183c540310a0324114904816041111300c10002c646101c0114402107044c203107030b0307002c00c0003c105550302c640c420740da0341c2000000110303500060300080d4010003849440745001d04140c40c0d1200c0c01840c81e030401c03404000c0a081000d802900041000031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 680855395 1250 680854145 680854169
    0x3091e0e18010b010f08130816050309150c1b03122803020a09030f0812011203080a180204151205030d0e0703022b06020d0b19060215070309021c020f19 67
    0x483c20560f10034400d65001c0c0c200070b441401c4449c148500000145107061042d101364680340070005142c1d582c0e0050000c0305010b0303084540303403034111941c10481d81c03000c0030000d013600e40c04a280507a40e8007590200f10402c0302c00454415901000710100042e441c0c0e11610709066180891001008107480d9950100410411b00744001d0300c1401148c5040d07e411003030020104540756101d0344603402c40c2d001400b00300c00180d2134900040381c1d000c090080d4091158186a807101c00600c0f5402c01000d080304003140f03d920303036898500007205000c50a0002d0068040e40180d503841c103401082c0c1c07041c1c65420007603a00a0307100800030030061300d45120104140c07145d4042000081024807440c0da41c0c00300f20002800450002c561201940500d0740120750401c01181c00381c00c0d1aa003810062044065881268050f03080344410202c6800c004400c6075002402e0b140001e0b001281c5e07400516048060032201d00295022480c000442c2800703003202c9007000c01201d0750300c5800300e90101000e91517418028841820f030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 680856645 1250 680855395 680855431
    0x6060c01060b0307170a0e030a0f0c0c0303080702161203050a051603050306130b090c090a080304090c0807021902100201090803041407050d03091e0e18010b010f08 72
    0x5000e61100c4003034100200c54540d00e044c6120010329608002c0b00006024034401d000c98a03448140c42034140d01085a000345081ca01c0e240803e03260000e182c100803091102d0b00c10050700280c90780ea1101c010794440d4030b0703103207031414217400081c0ba0944004156650303107034815003440140e5107040403072140d84d458035083d592010509000c454500807038407101c040e8070718200d030601010341000296114810030703603240142c015066250b609590800a050790448410004103507002c8501c0c005180d694406070803e14604d5607070302e0180c5154440d5000240055071912919002a03214100e15084035962008041d20a680ca494401440a02100034400ca90842e0ba03c40090300070741000c45241c5c1c001805030340364503250600c1440702040100045543c0504000807c651400030000d049098041c1d440c201c8490800d541c0491041040f005603507044080c0c800020441c045003050791250417403074603030102e580d4407201d010f0a4483d66140709051050b0a1800c0b64105c0e444031200390310803501010203503614 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 680857895 1250 680856645 680856667
    0x20d0617030c0718021207020a110411030c0309010b100f030c09060e040f240312170a1a0402030405010b01020705060f070b060a0312021605090c2a0f010b150705060606 74
    0x120405104905d4a046d801c02c000c0200d4011405840003800b80c010561074495200c20401140c0810281518080e010310100341030801120140d94440403d030000079004a10400081a054000c0b900000040c4074a440014903607060052140040c118144840c1d414142800500b640440b80704941c040c40d510140c00d1005030083d000f07002460101e52410b506866038000082c41d40c0c07954001520f40d8240c0b01c0c52252524481c11284400d00c43c1c1031401d82058840b00b600b00b018000ca40803000d82c101c40c2d522030b905156110300c0110b0051303208400015581c10340d000060f04025403a400213110ba80300380103007180302005504659100d0b6015a4900d0955030f0386000802d0b800e55500084c0545251105801d8038940026038040403501e14516a002190743d041040340d202c200300c0b21214040c1040c801424008a00720030151400340c4a030349080d1400c91194854501620907140a80507915031085c000d10741000c1e1559045d090043c80068500f20040e211155070b40c078060070490007460005503c08a00d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 680859145 1250 680857895 680857897
    0xc030b071707050706180204052e0509130f0209010b120709030302061f080303010801050f010f240c020411040f0602010e03091002100c0504090b01021c081504020d0617030c071802 79
    0x6647c0200100007d05000009200941a0785000003030308440448079074541403220b0000080703030f0b0000c05040c2c081d0f4031512402c6000b107030001d04458030442e003241e80006981d10030fa43c5000e004000c1600b40c84a00400c00c2041c0c1e00005001c5005104400d0020b0000c2680880e01c2544142811114801210b0920320407110303031a0755110300200e000100010030402c0301900042d00030300c0f550f0b1550100342d884a036032910517070103885890f802c00c2c1569801c41148010b000c407801030300000e041803102c3c08002c1d004070782071b9a141c2106400303909000400b445501c0940342080042c018038030003001119102170701280d0700d00c6080d031482e20480c820701010000c10b100708603140aa00039100280242880200c1c05492034000303002d8450b007282400c55408540d4400034000d241e000781445210002c180515040e40c0c00b010142110000004040b01c44449882e00e00007424100e00d90b0100140b145c3c5004000103004042c2031074002c2c29001000b000d5180e81000a00f1000d039200e010014410040804200c402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 680860395 1250 680859145 680859191
    0x4060501050310090506031501261903121812030f0902010c08031012050303060913050312060a050301020720150d0b03012c060703290301090c030b071707050706 71
    0x18050890002c00e000034000700e000320302c0cac540040c04803076400030342441d85d01d46a200741c00c2000880030800c0503000c0303803103803959540ca25a058800658040240c2401c001007080800a48042d6400348801d1200c07503040c4545014076503221420444400c456000070040c8000318800740c00501d0200208195029860f0950010706451310386481000c164900b40b034480e041121068452468000025800c814148119050680c06006146403914140d03203613400d0030010f080160021000700c000720349614244001c1c180d1900440c0031036514000180703501d000d104080b502c580100ca18642d0002404001425503242c070700c0e002d80c0441c204a0440103c1c0c01071440c80c0c0803101c500080c541980c140ca42410014070b0b0440080150780907a640c5c0c1200307a050300e00d8040d11070100e01014010240c445d885410110b9904c100900120b180c04651716510401d490581007075030740003100c038140031166070481d0030001c5440c0e10150354501860a410064030390300034a42d0207003c560700c0c0d940c1101e0300f442c0842000d003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 680861645 1250 680860395 680860423
    0x2042303070807180e03040e04080703020109140a061d0c09130615060e10050d0903020f0102120f07020a03020705040513050706020303180106050a03020f060c12090406050105031009050603 83
    0x1006a80d466003404488491340c0c00e201c01d145020701e841d42e440c2000c0215010341d40890b40c000a16100c0344c2e1a040d43d039105c08000d8003155a100700301b0001443d440d85286019091030000c0030000510704050048800e114078501c81403070301440b00c651028001c584c800c003141d02280d07101416500d1640007509150681c000400c9036117001c402810329090701d00014141c5803156034001c81d4501040a1150802c1c001828001088040c0480114404950090701c0594468815501d42d80d842d0701e0702d242a41c0080541d08a8602d444041101c4080e8011500b40e200880348010081c014454a0113511580e2034051580140d0b11000092882c141148040055941c0101100c0a00d944d8403802501c0350816142c5909021000d508120038500500074038041d500c0003040707058140d240d642040b0528507840242c1e500304c0d609000703040513078009008039a00610f110207002e94511150702000308032030040e0001810f1140c00d1040c0009030060694400c00c0e52560300740015251036620000345016a0315140107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 680862895 1250 680861645 680861653
    0x1e0e0108060403110f0f03180306060108360a0212070f0612110a0e0f0d211b110a050402045a05040207051b0a0909050f060703020423030708 62
    0x8010a1b1001004010054116040c1c0070082601000c142d01d8000c00c0e00c11500241b043c3e07020031a40c42c085117000c1a040c0c4038030000684910200051a514503d03030020800c560022313002103056080c2442c0d4050050221030140c0f0600382444c42c204007451244c0680b03003c10508400d201015980c0c2d1340031600e10240036605944882007800000e000540c810308682c040c40d4140390140741424848103001d0960b61200600b17003900c4240122884400c3c07100902010004003180c404075002c40f030004900703000c1c06590f80e200400e8015050204180c40c41d44102c2c01144108001c0184400007001c03025444d014401051002013442114005040301001c03e8284905052100c0442502446119100320309440c4021f00c9980d0303142088101c2c016400c020305646c11070f00024401e5182420010740c015001086035800641b110f50070030884079056021100c683c45546030580c084070400403a03900000c9032405601d0300e418504201042d02d5280d4040f00d0b400802c25084036141c0d81404008080d1a21404071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 680864145 1250 680862895 680862913
    0x41503050a050c01050c151e13061b0815190f050f061306050f0d1415030c0a14010909020f04050a0b0a020303070c080705071e0e0108060403110f 64
    0xc40d440d030750345403422101c80c81021103c03071055000e44143d0740d008003c132003e07090380c03910390818410114008080e05e10b80302844544190090f620141c076800b80a506c00d9480d00059140303011000c032006d10300c18550f280280c0c3d4102d22029441040c0c0c60f4040c1e00702440400c0324041070301007619002c2403461020098800c040110340c410401040c0012103d00f161444501c05501c41840300342c0c0f16502d01c45d00daa0131000f205018860040c2c0084c8204180124040d107000c400703502c600708070781c21440000f000030046070500101a001c0c4d003d40781c420904030f014080e0301080301c0000c1c0300342c0c20610810a4076100d0010320305482c3e01540c089801070404600655541d050343c1030344142c551050046130b119045d43c2d6800305607004402c0c107850b05000e060300114555100c020007903d1031001d4a4080360419000c001f2000012802d01c945d10007001010041116890403104134520000d503500110b07400718207800100600540000c11640058144c01c11031941032500807454200b96102c100c01c1e14900c101060 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 680865395 1250 680864145 680864153
    0x20f1f09110904260327071a07120509130506120715020d2a080c010213090b0d020a120c05030d05030109110a200f12070b010b03160c02041503 63
    0x1348407624584c5104440e42c03811000b291400c0c500054a038019603500ea0307141e21500840002c0722103c01c1ca0180102c4548542c1c030009586801c044103903061204102081d400100101801010f103028064140320742401c0c500342c04036410350006905028407688610204045807941200c490746007403c0303400d4941680d11800483c9403042c062842304010721491203140c00440c800d0381502c01c0080c81c0c0308410201540c00000c0780c12540300079410344081030204040740d5240c4091005101141908841d41c040b04d2500740014200e0b03003402d0405002e820080ea820340141c4d01c60a078403042c1c503001a07608052280f907007031118180400341c016942522504200c06500758010000e14101e82c1080402e200e546103d440c40b0044c0d006051407403003c5460304820f9202900b1112503004524645800c60309001c40003c3c07603e14002c0703c618410321985001070b5007c24007152090f2103024243d0503c8051460800790411004500943c0d450340c104201222103400319a1280c02026140400100c440300c003030b4580c14 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 680866645 1250 680865395 680865413
    0x31b0519120b18061224040201180929150d1803020a110d0b181011090414041205031009060e16020109030f050a0905031606020f1f09110904 62
    0x21303219109801c00c42101e00082c400282200d20f25403410841882910004206200000041d108a05015401481c00240b1050b2540c82009041040d0003040700f0910800c01c0e082244001e181c0016143c2c040e101c0122911007070040880e810f18000c3c850350b20307042d0140e2800100b08100382c0b020140c242d000e00c3d80c10700d5400a02c454040e030007589000849070070102000303014421300724001c140400300400285042681540c1c0c0214010110903248050880034110044401c0c2d1114190070820200b0159018242845403418440c204141c68002d414142c98800c0c1034002c1100c40c030104000000024400325007070140340c00925180c1c0051090300e454190102c2996012174202070405428512104a0b600c14090300c082107070952295420a03424040481d01c55101d01000800d00c5002000000c180d1000c0003880410045181c0d00300c01c1c61308081000b41803511f008881c0700b646c1c1c07146101481c010105002c0228410310107400242c1c00d00e261802c403903002d0206400c150301080d004200018040703c00c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 680867895 1250 680866645 680866651
    0x3020102071e120806030c031c141c020304031b050309040b10080103061a120c09070906122304141c02030d0c0e090106031b0519120b18 60
    0xd06000040007100200c031800381d40d50740d40540600e040f40307000c0c0140e90050001c0c2e034000c00060300fa81c90201224011a1614103064507080003070310616016020594046422811f058002c0f400b2890b0104000000c00340d50007112500341041d9000012070101405410b60079880156035481d10701a01c441c1c02c00641701e411055600380118240319070307051140707441845541c00da80c240d00e60521603403c548444004045100700c0100103000011030390380c83d640ba80c2c5008906600301004000c04841d1100380800144040c116030180030582c082030144903040119080d10000e19000003030101440181035800034002110310303000c1c04001040c0070501a9084900c280942c8007412914100000f48004040c2444052000016001840300d07104842154004802040d041d1801c0303e4161803410014030080d8080c1e0102c0082541d6103c42ca03034091040c03040710b5000110342001c1d8201500b03403221003403016001c0d404104000502c0742c049618a01e42c0c4c840661501c01070200c200400c0c401c800d83c94015030039 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 680869145 1250 680867895 680867903
    0x1031e0b1f060905010503040605270a0210030207020a031103011118030d0e0109030b09070b03010e07170408031f15110c042f1204060b0108070e011d0d020402070302010207 76
    0x3581000c112a80660020800c0303130342c107a46140c1345035200c0e00d40307a00500c40980b401c070090b080000003182103852545001c44000b281409841c41c000140f040111181c4500c2084007410300500000d005662134025140c11650400c901d030300700d092000c0000b40100200720425060040c00308407407240071011491031040d14403d804070f03100ca0f00b5441003500c2c007400b5000000c0c0003950030701042c00096000107602c0d030030945c4007007101e04080d100c541080e007a81090b041440c0b00c144030000c0080299002000c9a00c411092181c503c036402e02d516003da062000510040c2807041004015000c00125106200103017008802c03036080b000c1d0110010700d02d0500d00c407140b4591184000310802441d01d4410822403500c40d81e610304480b454107010000300c8190301c0500703101c1e000c14007203480d59003900040c0d1031180307200f80f10005100300d58900240618030050121000c003c03801000081590300080079600d808030403c902c1080b241c551000406800380440d000b1740090000c0303403602c04c040d015006031214503c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 680870395 1250 680869145 680869201
    0x50d140f010e060904120f0306090c260c0a0c05160b0d0e010b0d0222020a0306051008070818070305071d0601020f1506210c041d030301031e0b 63
    0x200c0c41003284c0780b002610003030000c2c05000c80f00404540100c0b0030f50000c50841c1001310300143d5482e003840c03c840d1010700b0300b008140c03181103007028000315640701c50182d524140c0303640d03080c2442003250b9024002c1941100602040340c90010a12500308150640405803c541da00c0190300d8500d210b5080e0008000c4001c0b01d41406410400c242d41801030314803020000e0484003082400d502004010b6106074505c111058001c00264000d030021f00081c0030302d2409860110340740c0d20700740c01d0000b00000130702e41004000d1600c007840611540300012039003000c000c0180b454400c41c010f9a00d41400301c1c0b070340001e10b1481800c20000c1c2054411b481e0a0303007006444285403e0359500c0c0016070701e8140c891070000c8c060300040d00d001030f400d08001c4d4171f0ba040710004d00101218020800d0a100c4580100c954815650101e1441403180ca0b25000340c1110808070255181d810b21507511540d643d00060200502e042c810038140301c1962640c0041d0180c09401040c0850141015803460884440e642000743c40d91107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 680871645 1250 680870395 680870401
    0x30b01050408060f0601051c05090c04020702010503070305100801020a170a1407140405041e0c260c1207080a051506031f0b0a02010218090103020907050d140f010e 72
    0xc06001070303404482c88500070301020f5884508441030708500a00d00b6040c88410b202d05015030b000500740d04810418030500003840d0400000d12480c0030b0300c01701c603148141d004001500c0140d07440b00a882d003258080c1004680340c0c40e110120820466160441c40307466201288070500c140c7c0c0300c43c542c00c0503003880c401d840315078440e00001c0f02524080c100c0c810038003562501040d030700392040740883c001eaa6003600d124280b58503440028142d07001e40b5045800c01c440e8112490f00c00b00e032481500e400e8070340b60510380c00a80307901e03540341881071002034245d002104c40f200003541e0024441c03c40b07040c211055050f40940c9021040a40240030903120720b1229403070400000d80314843c1c410b2440184400510035415030b0303601080881d00100250000c00032583c1e50b000042e0808030103014000c1990315400241e00c41c040d40f41c8600c500380043c40290f210b19010801000561564051660480d141e441d0040c1d07601821032010028002154004249446903010041e181d5503010075036040c0d56030a5441256a1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 680872895 1250 680871645 680871647
    0xe090c040b1005310f08010507180618031704080d080606070602160c0f06020c06091003020f04120b0402040f1a190810020c0106080a0317180609070303030b01 70
    0x107882c841c040020800400202800c10f031603520b006000240c555a401e494440e4454554001060b42d00c565070b0700480c40700c04e0140003000c0c001c4036404001032401c1c4507800d07800c01880300900c015100d0300d030501949003020a00b98850b01c1192001d143c10060030440d8501400e280c2d03d03550b12510806000e40200c514502038180303d500010301554000308214180f954940380c40c2d009511260300d1080000700c0309542000107010000c0800140408030f4911405840d06902908040030950303198800d5008110812460740e80045507440d6041e145401619080d010081003540d1040d600f200094511420304a030411603215011481284295418400d00c0c0280c1e402c9410f581c80c4e011003c4680c107440003003600c1400c00540726480b070360102e1910113086507201000ca0818800c41c11000c1c49076000110138111039824092100100f00c0d00c0001d265182c5607440040c6160722041005240110315008642c8000442800d13801040007001960902d003040f0081d41c0d5a540c05200c21400300c0e0404c10f02203429 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 680874145 1250 680872895 680872909
    0x9030322050307030e130c031506140d110c30030606091912030305040b0c0901140306061e0a0e04020c0309011b050319180b12070201060e090c040b 65
    0x2099001d00114240000f5a40039540b03e030300030301042c1d0410781c09489610000d4050203803038040c00c40c54900203400984c11001d50070300c2025410080a000c403d144841480b4002e43c1242c40c100100e00d400a941590328600351207a200f565000b05070341c1b1603070940c0424050b07840d41400720150500c0703a840c48a1600254007540340011100030380d11032403d2052003001c0c20200714000c00e102c01ca0803003400c07240d100d058251402c807a06405900096444c02008104007820b071400b50885c1001d541d042c1000c0e40200020106040c489501c2005040030010450f65140e04060390f40000f9107102a00c2c448442620300f10164102e000001e0002b4440744420050342032903c2203448041022001d0762401120380010f448280b440000d14840b102807181300c2e404a10140040c0c001000748020b2240e24030222880240151004400200c034070903c80070410000040404860b4070700d2a4400002544d078400305c09034010075140e8040c5a03c136820f84108481002c000c01d2000100e1030440c0e007000341e004118140040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 680875395 1250 680874145 680874211
    0x9020d120f0909150909060b10030b0906030a0b06120f030d0905010f11251a010501080703020a080402270a052d04170f1809060d050a08160b090303 65
    0x46402002044c0922485e5811078040240140808606060420003042045010000c0c0c1c0c1d0000f950350803e075103186404081942c004904500501111185481304001d14001605041c840c0409007928829250180320501140301804150b0b92070703002c2c1c1640000540f088842c101c3d01c035440c20200c1e921500c554400c020703110710880c40d441e00300301008000c8450403411004100f42e6001039144500002c0c007042d609409040004031041655262a001506240010340740509050040c0b101200300c076841000b5941c42034048400e04c40d00d504071a013039020703c0030749907404049203a01c1040260800d400d0700114010414089098030180300b60f100d00e44d601400d0f25880c1403040c1141c010601042550114041c814103032050b85161200000c0c06035000d0b401018106648021002d56054600d8032140096110350150746d809035580541c4d555580340c2043c041d0017040d080002c0b8124000840c144034068205070b03c107940ea02c0500302490066505c4c2c0040301d40c0a80321629440126552000700044c0d01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 680876645 1250 680875395 680875421
    0xb15041802061b1213151211040801020309013219020f0a0c060606030b0d0204090318090b1201021905030402010302070b0109050601140f040909020d120f0909 70
    0x25011145a081002e55485080f071218640316042c1d50035060941440924401c0c0c0e500c0d4455550756031600c1c11040e4032282544403990a00440480107140b54000c10020840c11181c4000681a410034200851500641d0800c1c44d141d840401001340c481d00551020041036500c8003001101000c1883d02025840d51406d440044d0442e5004103500f800b4003644910720061015001d4205420346840e414a60401d0507910001018200d203002407002c2d038410171026000516040c490a006580400c1000c035800310300030701843c0d40d45c0742e21051520030f01403070720391404075884e800c00145c0d06c2101300d01030681010f246108145080301e805441c1c005108031844801c0003100030070303041c0c1555000d81700c581004000b80d050580810620000070803e040381030103003800e07400004907420048001480c0d02c02052040b203641c2d00400802600d0280d10050350b044400a260106407070b211480400d045d03007080400207201c0342d11020026005038000100500785099aa120b20082e070b9038203021029100b26200c145 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 680877895 1250 680876645 680876681
    0x3080a05060a18150b0a020a0b0901090215070f0b01181406240d0f05011518120222090203160302011704021f0f0e01090b030a0504140106030b1504 65
    0x602112101e8020321000c0311002e055243c91303560707100380c012030b03500c00701002d0010b800c495260000c21044409442e042078070f55008021001942c0c0c042000051903017684e020a1001044400420221240c0c0101c40340d071080034105d40c3c4d45d660790800300d015070840306080017506055010030071898410205d0322510004140e28501000c1e2215140340c003101080d15542c07d8403c105030720495401d4002e0b282e414603803040008444d031410520684040c5408081820084803400b0304800c804031030406810b03074001c5244100004084c1c400200030421081318a02c041c404140d101d5189010ba5020600360740c000d0701560b034124406817140c80490741c1400001e002ca4120120400d9622505080740c0e4401c1c03019001c01c2060701c00b4070384d103403c4c404040c0110b4000390a4066415160398400d80301d400b000c00030b0800c50174590800110400e50302006006a6110740c1e51400107003401407440525140700030320301c000c10600780c0300e01300032482820841d4a0505084034104e0801d403410309104010f902040c1c66050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 680879145 1250 680877895 680877929
    0x6030105040e0a0f0f03110a0c032004110a090b040305100c03020c150601120207080d0902040b061206011e1b0507050406060e13020a05030c07080708040303080a05060a 74
    0x403006020140300307403545224181d40f0a0004010040240281e0b01400112000c984545001001e01440346080c1d1000d800003070304400080c1403401c100041c2c95120040170700b8100c40ca030070542c50002040d159603001e07060031002525000d0701030080100c100c0d6680da040701141c44c0c0080941c684a903220042050b8440104a03014000c030f070740880c0910003d49805840c24107042c9050b40303042240706007026880c2c4054103211080d0703005092a004003542200c10760604910703403290304090150500ba206090380b10094141150354070792044e84005d800401e0203441c1d045e02c106640c2c0507002184c05601088444491b0820409041c40d0b403101c80000c4e83c0e520b028000b034030b51108030030704148500720740c03a109002d0040740b156a1030052801400329517a414015a400700208420181c49601c0303c0445031040000c504556480805c490740007441441080d95501e6074079150009104280000e0400769002c5404010107501880240c025455681b040c0070b29141d031020440000403138459410b507081c0d0032400b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 680880395 1250 680879145 680879149
    0x50412051c09080a02010b0411070204091e0c0e060402091318061d150403090302090c04030b0a0605032e0b21010209090f060a0905090102091002010c020c030c06030105 74
    0x8091000200115090200c00074040c00250b460290040b100f042003ca0107143c1294240300304020200c040743d040c814500f01005118440c86001d0010303003c1c5490f40b07456414805030104185201080d881c8502001e0f10b036060080e4011064051038404c28407850220b00e807881c0a00940c1c694139001480c0000d500701400c004002409501c0c403c80a84d4458040d52001c52a20700c104100d229032030800d600c0b03503c9a4501e0314100822007100c0e1050110b940284004698070803640c10540e40c0c146c1e00c10b4141d850b09420380210380615440241318104017030411021118580003d004c0324000e4045506200325006004201c032050068006198001c0340c040000409a821404000700c01800c010020000801034401d012083c7c6903103005a900040d0012030743c10a1603800d640300b92100300c4606503040c0070002030310741085446800900c40e115808600b90a9003941224940e1000500b0b11a0700010f141019000e0000403524070054010090804454100840c4c0c103c16850000d14007480e6a0074901 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 680881645 1250 680880395 680880397
    0x509090a1a0a030602030a060b07082b050403032309060601051e300f06060a05040e1006080a0e0316110d061a010c05060a0f1e05010f06020105041205 66
    0x101c03505902403100403210864603a000600301540c00307010007584d00d250103003405065810581c0010f0400320100446004030755220140c071036051001d500b0841c10833034010000f841d80035103211150060f1624040c8000c05400d0350240340c010240110a031240d04401c0d102d442000c1084485240c50b400800000e0800d6208070014440d4075100040e5401c0301005984108040d008a00d03020300034840c6601001354040580501e00801c5441d0f400d800d4189007002e2100a03505000d020380d40a000c003c914100d1aa0069055402421a0458540b06440c0904162019002c180b0890300030945010100d0752800441c040e000000d5148401035152020110380e108440d40004010340d80c03882d0080e9054207d58400301e1030b00708140660808291140300b003040286c0e41098211040c1031180c0c80031440c00168000c64865400b800c4e0090024441c1c50288912010b00f10002480008003000100041c0b03c0030541e0100d8140d600c2d2241c0a00030302d440d0030040c1d00300d88060307a028100b4038124000e446920320440c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 680882895 1250 680881645 680881661
    0xa060504080f1206040608120d2a0804060507110c0105030a140903250f020d02030c060d020c0601090513021021020405030f0105011a0c07051c0201020d0509090a 71
    0xa401c1c02c1c6408030050281c0788a400001d0410002240c043c1800403620f00f81c06854090040d035006042c645090040307449140c802c980700c80100a4480250b58241c045420032501d4001c1900ea1152003041150001459070310708903001c4a1051920f008651018800c02580c0d44c40252000242031140002006445a41009000742d606076120000401403154244660740113240c010700135034940d000d20011f900074075040b20a911441a1106100001c00d041c0c40c013200c0c41d075805480300c6514141600120f8142a000e009103a0000310001c0c1c00581d200d2568014010200d0403030a1b5800b070398a50483d40207803902690281e9180504a10300c1000d8a04104e401e040a111400c100400c80030180079007030448040b03032038071070310540c00319041003e4107007405110744000e0510020007803907041c24134001c0c00000074808005000404210101214010041840a41ba0042070b810074030303e00601c051010b5091120032401401610506110540240203681c41904002c00074421540c0c0e102541c40102840 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 680884145 1250 680882895 680882903
    0x30813080405041d100501080708060c040b031504051906090207050303071404030f05030d0c2c03030715091a0106050a0804031704050a0308101206020306190807060906110a060504 79
    0x307062080a120130802003c80207400f58940440c5c1c0d0741c9030001d41804c00345164060003658115004000a10b030030241290160741d0700d50714040e04c0761200d4050340d9020b07071289011034209240c03009200c4241c00c1031165001e034000310310040c44000c1c0c0320400b540c141c0c0580c0758020f09a50090011402c42401203580000c240da000c0d907018185035680c0c80780340c55480c5010341950b5540001504480b81c017940d0041f180f4407842420310365940d4203280402e502c120b032108501081800b500c0611056070b5014011114807030740040611403000080540702c40206140801201c0002061201c90380c0c410068000780d0403619180c4a4606207031392802d099502582c000c008600b0410000b210040c4903001c1ea030021b0140e40140000d00444c00645400780c4081c4000d0801ca07100d4000c21802c0001040405e03900c2c40c119403040c400f40c0c89403940408038072085269248403a20071080400401c440c540021142c04450913a83c509a080740e0b1028140c0348031091070b5030040c494100180d01d402180c100e800040d000351013 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 680885395 1250 680884145 680884181
    0xb0c0601093206060c060109020c010b010305071b0501060b0c0c130e06011a12070215010905060a0512070504060b12280207150c270617100b0708030403081308040504 73
    0x117407030100c900700402600041c8100d640843c0740c801c5010300348150070f8400750a080801282c101002c020b002a00da51090348030b482c1d200602c01080100c01e400040082c40318404040d110b01c5283c6031640c0352880440803d00a84540c404220891564010b502c1c0440f15040a00360382d134203002c0c0c124191750081041001c1d1403010003025000000601d48148554800e602800034001c8422590504447c1a81700144181c10102844a166141103868045590403100c070f20140b0000c050b028180a034a5100961092803d100001c007040e01c2001420b04510030070394180310ba1743c2c0e1f030342125110120148e2000031484420541d046588103500810072103010700c42c80518007810403614401d68046a180500054075510812580e09001d5a1058024411a80c0024590603c0002000d07101c0c0f100e62401c3e020f0300c040c00b150b03038140000d002c5005030007540011951580d5a051102180c3d209a400300d0006010100061020b01d810008980803540080082d1030f081c030700020040500044405610071106c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 680886645 1250 680885395 680885407
    0xd05030c03070602073518090115320c01090b07050c010f060308070b180d05070b0108030a09030206090612010801061d070e010f090b0c060109320606 66
    0x1810000b40010303900c210700c090307599000e078070300401170364010980c01d2a0110240b00c4105042650104141c5e0070380300d203a190391211010303080d464640c1080303080f054200d24100b0010680075103040c1c801403c40b030b0544910f0300451014a481e130100c2140303a00d080c903444000c1a4100d0804210005159002c1200300100b14082507480c0c0c40300080054415102207500090f400e02a040203000c1d003075408034519010003205203103807941c0076940f14041000348480414400144191481400403182140301c008490340c89400d60341c040c0c01c40d40180c10645400ba41c2200010300254000308842000a6a0740c903e4406465a400d200c40340d08040202d55009406002103807019030170308003007402000c40780000300e801c614003c03465a500500c40031402c5150400710804c003084d90890502000c4950078a06604108038013038040318030300040c4d082001c13070003800900300c600340d070001031200c1c185c6981079000c2042c422201004a15880c0d141e2074400b0740340c4610b55031401d0141040200f60310090190400c0c1c6000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 680887895 1250 680886645 680886667
    0x5161416050d030c092c04060603051504051603051005071b05150105180f0a1128090510030b061b070f060c0231020a0905010e0d110d0503 61
    0x120103908a503001996030802a214641d000b41e0b160014035519a805080200b0019500d040c0b80246040320206c140003c042001c00c00c003a88194010754200f41550400764140c11581c280320010703101601e00c0d00c03070118011101502c1c40c2c648001c0b00c1d4044002c000c0e181b41da102040107800010410400e1001c8804109014890340508403081441240035151640701410310045800040e0082c43c0240400541c03141d400226607091500142c0640020400c3d41d108040007010301003035881070505000c0400c0100c0300c3d12940203561760b03484004c50340103002c9002c0342017101c0b0f0002a01c0750f2a80018411429a14203000742d2101d20600d00203448949407400c160008024080c1e42c5640040c11303402098100401c0d000c00544c0c0c80501890324004100030102d0f00040c02104503048240010104a0524040d01d2202c0200b045200c0f0b50103825900c8601c120005491f86501d0303c511404a0450000c64020340751540402c02c89691080f280131500c428a824440300c41032454003200c00348000c000b010010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 680889145 1250 680887895 680887903
    0x111c050601091e030201141327061202040e0a020f0402130b0705060126071401210b0307050d0c090c09030501050901060f120201020a02010e0103022701030516141605 73
    0x40920f140103a400f601d14400104028600a910f490400007400300821000e02e1610708030466100a801540708403000c004156441c0c0b12070000000280313403c0c00010200208035030b8101040c001c6404221001d0910291516082c80d42002544a2204000e100841c500b036030107005500240019070006a0301d8910000aa5205220558440e800f61004000b40700968408100c101700300c201044880c040c803508981c1d01c801c41e01901d0065164180c0c104200c1c3d120340701300d000c000001503071803090044594400c4000c00920f10101d0090044100c00b10b01030a204403984a102d03400801e04400c4ca241030510001004052022800c019194a000001c00e80c24090385000ea0b0840000086d41483c100c0000c580e000340e07034040352590000340c0c81d04001d0303078000c80c101c2a904d0302800c001d40303c0300c041001203000b8481c4128022a000d2140343e5540d0384074903032120402015003030700c040000762562440303034030780c902490241000107094802500c00c00c0030172805410f0140c158002459201041e590302410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 680890395 1250 680889145 680889179
    0x6060a17101107020901050a03050c04050408091309050606010504060c1e080a0e0306180331030b04110105070804060309020102031207021507080121140102040e0703111c05060109 79
    0x14402c0490040d05504d0700111081c0107007000c960f00560a8030315601d6540729103180d81840c2c030861780c81c40040c0520049604440c14500d0040c0400c040007030300c10701540101280c510594403481401c00050146d406202244d00751903164135082d00700c180f43d989103052a50301c055500d5260740003c03042c0e00061170b800b0181051003001e0701d4030156003180c101810b1070194000c1a1401500004110102c03c15010040310f10070b00c181c0b544014081496404590100b0241c2d01c51520241c1051000042c400900b071014041d511504002d80303502d2501e00110b4140c09030260242403003104000411125003c0e51201504134418010f0301d0411310200704c0710300c0c80b00c011203030800903030011038030031550355400381030f90b9440644d5040c803c1d5107504060b552650700040103024406840c2c270314800418015051002715540c0501e500a560384c1c0e4440c49100c110280035508180400d042030358050b468858502694401007040d080ca0856481d41c080e1507002d4280a00440d0600c241d8170380c00700d82440341901c4100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 680891645 1250 680890395 680890421
    0x504050313060905220f2c0c0f01050306180c07110d03171b0f0414030a030f140f0406050c0610030510090602090d0b1503010203060904031428030c0206060a1710 71
    0x141c1d01202118210b01c81c09080041f003619000b110110b00c5943c0d84010b0703010820700c2071034266120b80d918008a042c2c6c540380c0300400f1002e40c0c414104a0180c004100900c403091241d41c1c81402041c0100c1032040b00c10302d450009000c241c0011450f40043d100c41e9140d40c0c000184100060f0f811484282e0f458181d2215a24001c1594006000e102e040007516050b580602c080e0000c4c0302501050b10002c108402c0800350204000c7e21400c413100c0f500d41c050580baa800c1c4441d0145503240d07138a0002030610703402681c205429000f1307600021994a041d901c514200ca0700300010f09480c1d01a44142c600a080c586070803501d26034240f044145a880d11004480e481b48200f070003800c141000f4420f4942c05081c01050b0748a07030b004004104494941c0081c940c4c00075414200b0a880300013071070003024540542d111241a80111030085129a50849000c20090407161001c00041d0403031401241c84010464005820800d09101005465400c0c8070392103600708a102942c108078400c500c3d000a48540e050340c82 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 680892895 1250 680891645 680891681
    0x10f120203011511060f0a0c05090411040501030c05130b03071110050f060604030519110904052506230c07030b0f09010e0703080a09090504050313060905220f 70
    0x14600310740111440d0840c480000c0180b5003032500c01c0c0003048907080203241200d448d840d00d2490030b442e03004c3c1050b030341c000d00028800d0001580c48ca0541c210354001d4801c0b20300203401c00c025001d089024404940e031a43c42e585000d8211401e05508074041d81c0080c081c1002c101c4041f000500100d028445001031041c01c4001080d1414071942c8002d46001c0070340b1082c440e141c1008101b001500c005181403105a29162000c1d45251504200844220b21050340e9082180c500c03c2104019012a00291820440704060039071002000b0441110101340110030216000f00d000321412250741580c40c2400c00c014501910b42000c4a0f00a81070202950080b031300824800c0512121648205c1d041e0307841917980008200401503041030320b64400c00341c400035161030380008540e0036461060304581c3c040c010410f000e00c0141083d240085e900e0340407103145e25801402070b2001c10307680e202d005001c08a41c80100044c03c20700b070481c2144001c10f0050741c0708014580e00d00204600e01810b0085164500e0070003204 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 680894145 1250 680892895 680892929
    0xa062c1f080a0204060c0201110a0b18010c08040c2303010e0c0102061602030403030c1a1e060f0901051003020d1103040203100b061204060b090406050a060e060f010f12020301 77
    0x107071103400081c011030902c83c0180400d10100b503000140f4920f21782c0920f010f89401074503130740c45400c2401d224405011501381d80100162010300078002c0b00e86e9003910300200300b5240300c1403080714100e000f681c000300358503128001000148142c417403c400106000400340e005030f4107403001900315080610129841d42000c00f50000540e014071250380e100c51130306209140c0d50102c88009440f40300d1400001c4c240180300e9584014011084e080071030010882c416016182070008074004c1d105194200c1d21307580845040043d20718281814036800c403d1b8060f10003101c3d03900345410014048920034000080560034000c101a05d9400c1c080c00d40c07443c00d07006140d540ca052500501d410440c02103101c0440e40c0c241000c078659903d410007180c50102d503043c81900b042d2114503000000e0b000f1044000d51002c1e07002d050009211865108600036100c080b0200003055035074641400411003160525400350340c88445410f95400740c2c0010004c00001d01d000d0a141d075170f41e807481d001c9810a0704018400c4e0198581 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 680895395 1250 680894145 680894147
    0xa05040515040510140c030106050a05190513060e100806030c0621060901030b01180b060a080601030e0732030a0807060c090b0304020409062d0b0a062c1f 68
    0x2e103180c03842000e05c0784011490489040c0d4224130040c410030f01005400542c01026031b1203042501c15000707a00e0142e1400c014000401030094002e000003101d402240103001034a18045c0b0303039a10b44207a015000d40b1046e0305d03006054504403001080d00da05806085101817203552460000e01d80c504010015101c030703d40d00b02d910b030b18a83c002450760703008440440050000c5140c4a001d68111103801c8a502205100c00307540c90003810041c1c2c00203400220200d00c40e565644c0001455114041c01ea0701000f4825070035080d15079903034091048048040600480c078108001d804071480099440b00c5040c8620100c0c20040b910703008040c40d003915603c00c007140c0031040000e03070b0044006070186407a01d640490304014009903288009800280303d140d40d210b965040002a4104203004e50156080c11050404c0403154201c00001c00312001d452441d20800c090b052034910404010b41c0c00b82c1c1d44007640c0061407290398040140f000c500007803e007440284032009542ea0700395070101e04030a1444116400d40050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 680896645 1250 680895395 680895401
    0xc050d051c05030f010e060303070602030711010b06040b0d11070c0f140a0e0c0901020f06070c031e020307080d06090504150f060503210c1b0a14090a05040515040510 73
    0x2001d010048108248903d1450101503641914010f004940c0581c07030302000686103215103140101440e00201c10400520380003804000140211b00092000078282c1080000b984218014cc60101c10b0500045100456590040400800d5486a6440d00321705407244002c1035030070341c4a480c415440c90003c2c844207441d10107500b424142a20b00d052864108000388114190040003900c40b88004201d00c101c980c801c000710707651000b460080e01d1040c00c04400090503804900e0701a0b021031504006140c80b422440350a081c0d070605070f4055402e000060b940e50750f8607804070324081c0c42c1c1c9407103a0780032840011600c603450149105510780c10b00a0110300000d02030380d0404401038000c13803030148200215100030540403035082c4403d4002c0d00070b400c3d20404496038011000048018490030a80e400d955441142070300c5002d2086501d607201540d691038403620081d010b00125007120090f00480c82011280e081941c020348100241c03454142620b80f120f000c60f0341103c0c141c86a0348100e0358003051001c80c1c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 680897895 1250 680896645 680896693
    0xa0b040c0f050a0302060d0209040c030e0c1905040e0703080313141609020a0c0c033203040b070c120c03020a0b0c0606101806050a03050c0319090c050d05 68
    0xa07980748181c03820002454808451102031b00802d40010040d078403041c50390450707004d210001c008004015144000500501e180c4c40140c2e03a9201c0c03101064464a8624170b90740101d10180c0c100080079081200f0300c0050619400001701610980e04040300060810740074511810541c031320442450000c0c145102662460003103525550403440d640481c3c1c000205c4190300f9100e440b1000742c1e5842d0b5503802202c0050040c40d001c4d224408845010081040c0c5400b800d0544102044008020809075880160510400c240c4070b510b61040204000c003074040e00140c0907003405503100219207599090500000c54040100b2220043c800205008500d010740d40c03500904810071410342451b00c1000f0140c1d90742c030090903c6105c1d0300401c2a0482441c840e0281c103046140f21800e100040780e48007000340c0550015040903011900b80000124004035201c1920310546881110350700c00700180343c100d40180500c5109950038000004041155110548100340c01c0c0e110f840105200416400d1031740c20402c0d50703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 680899145 1250 680897895 680897909
    0xc0604050d090906030b1513020a09030b0601030b18090a0606060e040c080106171003050d0206091b13050a060e15030f060103210509041406190e0c0d09050a0b040c 72
    0x10004c01d10200e030b0211022903100560004448200e89030714006500d1094007203c2c1180f26000081e005201503018091004491045000e04250745940d401541a604207045d1640c000540324000c50014204103415a042160f00007642d0611030540c0710038040d15499008400810b505010ba00bc2c035080622034000021043e103444030351541041e174002c01d88a9100540440084d640b030108001140d0300000000556200040310900c0c0038030200607485010440d4452a60300515654010410800444c07010152006040c40060100400594003d182c040c003d01b030709542c1c1c0d0002154802040c0c1900c1d0140c1c4002d98a4001c008400f01014035203020000740718140e800000041000907070b042024406145941440880560b1084084415000e400d001c1a030050608200480030500d80b403c450080340e0507940c511101881c001c0303c50150031548500f210002c0e034980040e1401c81c2d41350181420b1103642d0408104680b668a5540c5000c0c800c140c29142c004000092204115540310b164004080e2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 680900395 1250 680899145 680899151
    0x90a0603021206070914030c0405070228030e0d14150108010e011e020702011b081c18120c050a0b0702010506010c15051e0a0b03010609110702150c0604050d0909 71
    0x1301030f6004000000d1403040078101503000c0e0f140140d0703036014010041042030181c000c00c243c5c544600000d544240c288103006147c1c0c00d10000013190510700040356400c42c2c0580fa5207000a1701007041c881100300740700c0f055900b810714818450030f00c0c0c02401800003030226800d134008594103005a440c00c49031204516100c0361314282d4004582c50038088a0f50301020746c00300043e1105c219000503102c03c684e80d2441c9100000c001d10315400c000e03001010b02524040320310201c0400b50001200310440d0100321048045e50072440544002800783c0c0b00207010003801d460403200400a030b59802d8a85012106d08440424034481044802070b4244691503001000b46401e07241c0015a0300c0d04d8140840d000440006a9110300c0040c0c0f241c25142050041c06c40b1020303281c415490098042402002c4182d1258869401d0450008590400b40510001c588100440c680340403202c0c0e08002c16486403103203d190b240410b100558021109201207845580200081c11410000c0000141800f81d10b4000c0018145 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 680901645 1250 680900395 680900401
    0x206070b1b041202060903070315050115050a050d09150e0105090f070b07060509011b0c06061e12140d09090c080f01151e0320160305030c09090a0603021206 69
    0xc80d14020b550f040d0103a55481c3d0701d40c05080400e0402125400180803072810880070300c107115660340440d0483d145080d4400401d80380341d404580707510071600280000780c401c0c41400100c581690200c401e9a2003452035070451402c0c04c03440b90590b407854071201e0301d0341d42d601c0801c005841c051080c18000300c00305d8082e113540d9042c1980f060381809145c0f409441c4560341e5000611074240bd5100c811580c0102d0034100840e0074a4000030210581844102e0300f680c100640002c00ea208480041d80b0341c0341c00030803883c0c039a041949c8842034400c5e4242c1907485040c000b41c40c00c1c440c00d0074805001c01031096940c0c0c0050b282405a000f054400c185420420410354000300700d450780041080034107440051a201100715003031801100c8102c07100646250303040d50440600c1040c6d405074408035109100c0321480da4072640156a5640c1340c015001aa06502203494220002900c40c0b00210350002e41282c3e902e08280f61640428040315049400c007684680d00c0e91700f441540341c6035895160803150040180301620b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 680902895 1250 680901645 680901659
    0xa09020720010c170c071229060103180c0617070c05100209030a050f060a1d0d0e0a0b0d0c08010b0c0a1e140303100515091009030206070b1b04 63
    0x109004020b0070105100c00f03001c4a00a0784411210a021000215280191142d47c075018401c0c0c00f07039040307500c50360a840484a0408234040685149101090b505045d5070300700055000d05040303204404212260008100090340344803052025104030340d070b00312504200754020f00234001c02034440c406109000c1d55000014800045440c10218581c002503240e140b5031010914010101030024070301d026940c1081c0726143c0000d00705204000c00d000a10492a10440d000005c460080d5001d8040c1c11080d00c1760942c0380290b4254a6080004d0322070138030305568078107094a50b0044d01c05140460b490740c1090460b03992055074a40940b00d01038010345014400d8080a40e5003840c0e4000074221610400440614000412008521074006100500e0544044816600d83d801150300d81d1803450b80e510049603505080c2110000000b180c540e592804d04001d003001410050705013640c01300283d003100070005072119400b6024041c410100c02c1907034180303029644407504980c41c0c0e02c0b034920400d101c100110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 680904145 1250 680902895 680902907
    0x803060d05151b0f0d02090418060b01120c120207080f0705030706270b0402040b04090609260a03020903010216110a092306030c040507020d0809060c0301091a0a0902072001 76
    0x951000c070b00181c7d112801000303e000b030940f0a01c04c0100c107002401102c280f00301c903081009103010998034141d098558859220482e8400a103540001c1c0c44031100d030002c1122503005000003400b4034070440c100002c07501d03038605603800107004170794075000440c41508005180c0170303503000681c04400f02616621b1400c0c12140480c05c444000e041401c00c4000300b4255115540000c820860152040c0082c0da124100b0201501143c2001c171803806c00c40309051110312644003030403101c042112642c0d1920030b6410007203001c0c9d04144030203075055600304150703a20100201002903070306104088214910380c050b010410000c1080d030000010906040c040c1210b08180001c250710340e04a03012206aa484400100c1d20300355a07621000e400c64903100a1202c4590009035140ca0f12405035140c601503522401c1071a201d0030107480102c1c008202340018032030030600342c00c40180c200200a400c01c0c85420100018800341203980321072686580058058244002030260720b0f05000706844451003410380100091078 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 680905395 1250 680904145 680904157
    0x503060409060608010510031a060904021009121a0703050405070510020102370c08090d1103011d0106090905060402040914060a0c031d0a0803060d05151b0f 69
    0x850350707841c40081d0030014250b00800c058010700008000c2494240c9080200308003500003030750105a002140b0303502c610a071081e1403040001610810064a0f290b080c49030b10804100072038180044e1840114038060449000300d41030340182001c421f183d0450321b10121b110f001800040402d82403000300710202e40006155811114150360300710801d2400c43c0304a00a006031411034030034000c0c1039400b102c208681d52141588840c1d500004042d040d0a0109075450320306a00c3c01061403030f0905c646030980c80c141c0076118245000388566048501e103213000a0071201e800c003030301420840c0d2401b4410304102c01d110310700207403510120800590b0034070307113070f0302c0d51480000e00c020b01c61f40d03c2d0103016040002e4020511109400c00c0111001d41c145850ba41026200034044440001e18010055401f0700c4415031035000c203034500740a000016415103074003d180c0e100404064101102404010001d0000c1000c0b0704040fa5811a69003070381090080500140340311140300c25448010300034240e90240301c400b2140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 680906645 1250 680905395 680905399
    0x402100206070f05030901020f04090e0f0718050a020d05072a0308040b0a0603021e15040b16060b060a020c0a0b0301031709190306051f1a09130c0203190807050306 72
    0x140b21b58548090300c2c007902c14050b0741d4030501e0340810b00050748465600403554021040055600c0d5003950b0144590381c040d42c1c0301d2241454862005203030007096961203903800802c040b0380585421008a08402510000d82d040700c0010030003405124451480001c184406140e015500c61009a60f10010329081000d00702402c00d0002e203021446624842e441180116405804e022102c4460682403000c90000c00207030b40140703200d20b840d00e05409580b08031401e8071402015a4140030f024100700d01902e21542040340c25070350312115208142c3da03480180401d40d510b9401805070101078810f00c03c0c00341031a40300d426003140a000510000306607003800201c1d0312428201640304c3c0d00c0c0d1000075000c440c580140070701c03c0d881c01001105101c40d60b040a031040545111250340d0b50b205414825040441d842140c4841400c62205840e16103404020002200010301c02009115000c00032002c484d040005000541d000080c0c2c403103ccc0507484900d1010035001c1c10408110320304050042c1242c40b000b80818 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 680907895 1250 680906645 680906647
    0x8091206090a0320060906070f050304080f180a0f1703130512030904061403010c0c0c0b0a0311040f060215060906210d1214040c0302040b031f050402100206070f05 72
    0xe84080c0a00c4013940e40c5060348012262103003803c0c15076030b460760800d580b01d6002440f03a002c00380205005000302c034061603201d498030b8600084171801034001d402850380700d405081c030780f071743c0d2641a9210041da80150810010001e4403c3ca82500340c49114092031180d42590814441220407801845004040321410b903410070010200c2032003030f0f05500c03625043d258024940900410300c0071020300c1d0040306210990003048002d100040139079113491a80c1e4001d202c1500c4140603c2480c01c40c00203442000268100801c4181840b80c000116801c04c1e0440c40d44000b03800c00400000c0d60400003000d054007629452081401c010000c620425001484240181000b05202c444911581c452203810702625080c0d0351401324041d40181031455400038802139604280e00075043c0c1e6642026240281d0b441402d0075031051031f42e03003880058400c81180c55071502410040304511780010350f0740d4003203009400d030025881c640340c41000100c840340300008045500503020030100329080340029026194905110f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 680909145 1250 680907895 680907917
    0x100b031003080a030923100f0e03270604080a060b010e041b0905040c0206130f0804060807090b04050303071113090b060a0e0c0307030f060f0308091206090a03 70
    0x64400e88101d6200500c40e030b5001605407100c0758103500c0005141d12500c003c3c3c2d80101d2080040c810800140760131026500030748541c92000e58a54050303c0742d044101c2c0d020641164604060341150031503001c9d50010050504204990440c0c807a400090540c21182581814200076880e9511800c0140c01030881c1e82d15143c0501d143c1c0208460044440e00410a01000c44d503c524202d203900c040031f01308041790025402003041c3c6040e0080d000c1c40549a8010b04150780c9a4241c184100c4e00d080c03003034800c0b0b4440c804c4000490b920a008201074142030316450790a0401c808020400841c940c03004a290328184400c0c010b0741d5000c0200d41c00325410030540c1340d00020440c0060401035150380d4044040b407900d80e40000704243c0410303481c403580040710700d00c8810381d0715490030301035080448200407803000c1080040e900c24081c0d40084030403440124009050743e1030351350107800c8480540013614050008100d16a180c0342230100039120f4900700000d03266a0030700108542c6e8232000c00c0d030014140b101c15495 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 680910395 1250 680909145 680909161
    0x503060303091f02010c083709080a140a0c081b2e05130b0a06180e010b0415050f030f03030f10120209042003010c031a09100b03 57
    0x1e586400394000e101030340802190310100f035281c1052480c40095400d101d0a00304890240100c0c0d40b08142031511210185811004101d03012103201401e022903042c4485a10200c0e03944c4502c80e074a17482440c42540ea00450f00c2c0207000e80310203060464511004003c10440b207036016603021001540b0250079901c40d01c0e422516900b8007040c0740484620310540300c102c0b880602000c80c80f00c0c0045c000700700540348080807071007400760b4030120350452150740301281000c0090031000010358400705001000031807648034504200d4100c1c103034400b000000e41b1032800084605003845204000f941c211801c2010100501c00801240210b1240510a5100301c0070180161414410400c01207800001e40c1d540385083c01b00303c0c15904064541400007801c203200880d101403035126881c0d54030340052188529607990781c0d0b0301c03002c00001240c01d400c650b075240540c5d83ca40c03000d00440a402290b44c0b03010421060050314a510111100440e40c031401c1201e00b8800300d41200340005d41a00c440c600c2141c1e890780e95400f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 680911645 1250 680910395 680910397
    0x3060305010e160b03010531151a0423010512010305062e05131509020304031803050703080d020405030a0f05011104060903060c051204081c0204051809070b22060c05030a0503060303 80
    0x5580c620050074a000341400840827410b00054a0401d14001164403043c414010700707005902070403552040c04401045135010b82503810341e60200514103146402c40340d514107402c01c0400ea1086417594040c0040c40300314405640d0380040c00344400c00c41a4202800c0c0b10b010f019404c50320509020714170b11a2801d82800b1180c00405220420802020f82144d44056200003944211020380000b225000d41d01455601d000030401201d030408000c02c0b0321802c68803841002c2d440304040c960040d60804c00040e0903202846140d80c1d940c05500c103030000111a00f083d034250307843d0000000152800b04400d0040642200840c0b0030303130360021400920482a07000c00d8591303104620b01c440e850691b03042007200b0088044000c05650200d4106101c00302d4080390b00000303034003c5018050b0b2180240507401c0c4030100c0d58186641c099a507004036031f143d41e0707107090301a0f50f9800707000c030380c2c44968100042c0840328203842c0c1080010300c01460000018000c80c5c4850381c483c007440c0c1c949000c01000001085003a50204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 680912895 1250 680911645 680911729
    0x10203030402221a090105030f0a110f04061403010c050408120d020c01060f0312030203040b0f190608031201080705030715110d031d1f0c03060305010e160b030105 72
    0x11041052111300c492103040c0c925441500d922985c07010001066904021845d0045030003030314004c200100f03160342d0348008141012040780d0030045804440303086d40d4403801403c0c01850700c1c180080c1142040e200345400c0da41c4d40c6c250b80b0300b8860108410041013000117919445c284009160701e440340c0c00c408426000c0d106545468001790308082011a00e0210420b0310012680f1501401da140741400e04260164082103030090070010b500000107080302c2a01c84019401004803007000e59040000304840c080f520f880d04000c410740d00c00b0400b000c140e40c81c85606809041a1402490007510b00b40c00a42d40703000901812111000b14502008024000c0e490800d4807021401a60b15500701d00340d00030300410a07480301001c1c0d442003003d0042c1c0c0010104078400201d5002200c0070000800da000400078161401003d0b040564070a800070200c0d80078860162040210000303408981201c010198a0f00079039040310383e80d442c0400040100386d96103c40000074800030692840210803601000121200311 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 680914145 1250 680912895 680912959
    0x405011a091c1b0807060e0d02031c020c0f0604030c03031103070605090d0f05130605130f1707150e01120b1801090c111216140624010203030402 64
    0x260710510030840d4802c80c0c28421403083c0c16801203566074881042d620f0341c0702c0c4203000105810310f100c400c2608146034403000c254006000c450011088c400d099140d80480d0130f007540180c00141c003030100d80c6002d800703400351800c003210304a003080d0940d260304081d52203920008082c84500540c11045040510644a038150044800c1107286000c420094448000110300380000c0c2c8442c1c20b1180c024068001d40d4281504511404c18840c14241d00390740c4c0d988039005c0e00000070a0210300141c003608001c8541e000d03004040c49a180000082d0800740360030030710781040c50010012051039121540c00280e115680c0c0e000d01c0c00c0e41922a4141c6c4000c0117103e20508281c02450920303500007210030300e01e1220304070366800d1f03800c01c007007410444202c4a00188035481c00c042e0700111604141c0314042006003060003a100040e00d080820b035615503801e4181c800c0c084002c0d030418001c104480b900c40192002c280e0b81131505409039020540002d48921000300b00074070817a040456100c00724081e00b0b4002c004082 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 680915395 1250 680914145 680914189
    0x10503191805031c1407080c0c010c020c0a05040c050a03110906030405010b0f09130204110f03100e060904020609130e03130f0803040503070312020f0111090405060405011a09 77
    0x92810002e840f98480f9403112000e43c41e07038100d40d105500c20301c5080204c05c11881940d040b902c60b82c40c1161141c501401800d0304080a00030035112030002c5c86048010f011540043c40004030541c00d000c1d4162142e40040d100301e00d02404000f07266003200440340d00e03809916000400d200380c2c9000c100240107020802da08100007004110401405500c105162801294034554006504042180345e1400f200d110540d442040e503410300506258002481c413100c5141800d04100c80c05041d07444642003154031040060540104000560705002c007990440c1042e9914402d5107407607004140d09106070900300340500040c400781e150401195211107900044034007502e646588080d8414200350f5503002e024940b40c8031030317000210b840c00001107404a58000d800350122030710315180d44180b40120041082540a0900c405030012028800d0442145c0c02000c26500c85030740006000456000a200600803850800140304628008001d0b600031600c10045035910780c900030114040709280e40508500410b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 680916645 1250 680915395 680915441
    0x23415030e030d060509090d020705010c0f0f03080f09010203010e0103120c0b180c0a15050a170108060f0702191b05060705030a08130f0303180213051008010b01050319 74
    0x10f403603085441221401c6840d0304c820303122001c01c180c45140e56000300d07001d640314000800155001754410b0481900030350060a81c40300a8880c0c50780c031400c00360b089001a0f4030004100e403071440030f024035400c0f410310310003142198108004a08103000602001d40b2582d44410305d1045a0700c9040407801d200c3d03015481c1d0105003050050302c414190828031482a900641c101034116042203e90901200c0320030010420000b03080c1c0054526030f120790015003c124254440d6a009074484035164000e0840100420340d61030024141d10340100094a14421500042035140d4404044202070b00790341d0300184500b4001002d1440300b041ca0105a110b00c0e04240702003000740034400c0c04070140c54004215101d2241aa68901c10207026100c4028000c2c2859102041030000ca0300c00d62084140c140f007081151580d03049500000c04a1a075090303000301c2943c0b1402000303210101001604028004400240803403031200b40040c01c640002415901c03181168241c0140c0f120310303074001036800000012140d0300c9071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 680917895 1250 680916645 680916667
    0xa0315060804081e270f13020d09140a120804030203030604052806090b03030304170904110d020c0714030a0602131e03050705090402100c170a023415030e03 69
    0x1003a103203566402c0392251040e8807480c14103c200010000d40101821f200d50451201c4200940020100041640d501c020307a000198480141140c9442510001e000e5480760f4500003032240116841d440800815205200000350000203403900110110b501056a50302c00101e0702251f41d5a4480286900c1107003250010080305038403800c2510005e050901600007080d043c540c0d6817209560050400030300d12841540c0e030040c44043c03d001c000003070000c20f500500c403161030601d0b044112564007080d4009200c0c0700b04002000f02c440100001050f1151030007010780001d8440c40340840280040341c0015850300e90000403060503000c1d0562442c009180b01903141d00502500b06400111150300c940300c4042390b0351800071505803240340d00410581454140b81c400b11030703800c0b04100803900190f20f420891015204000a0087e10a040e8010540d01c03d02110042c0302d00381c06c1a0110181103060480d140400f407414501c0d00751540f80707950481040e00444c08800030140c036099400140070104112141e2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 680919145 1250 680917895 680917927
    0x2030d11060114010509010c050307051f1d06060f040b06040605070b070809030d090302011503050c0a0e06030703060902031f0c0905041b0e01030b0a0b0a0315060804081e 75
    0x1509000c4200ca40603030b01e44401e10a1080121449404a802840000c8003584910001e81c100ca00c2941a642003000ca6580c0924141400a0f4513072281140320000381036a035030703110b51490b030417250b801000c6151013100f400da221103010f00f2035400f59060b040e085000d62142d8001c820744140141c42035030385980e5904000c20942104404640c0a01c06001042500344650405801820783c0b4014510340200c0f5440c000040894550807001d554035440003416031601e41c110200190701035000b0303201d901100410091140b0258225454180c80841440100e4400051560507264000c000180c00300c468000a4a004642200070002201c0510790901070240c0c0e07003140700c082442c3d03203590740070949900401c0103650f80d0802680c0341d510315001026844d8480c4600c0f02d404070060400050000c2c0c03110209020344e032207802445125100051074800a0303414424520b20a41600504244500780f150003429004041c0000e01003c401107400ea040c3c0f80075551100c0040e107000030302569204000e200c0120 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 680920395 1250 680919145 680919167
    0x30103080309010c0c080a0c1401050403030c080a0c080103021201110706140c12041214040305061e190203041505090c09010623030c040f081f060b09010f020a02030d 73
    0x10b5500b4502c0b2001c41a001d0100c6a02d120791005005003820b95581d0121080c000158042c1c9640d00441c4201016420a01c24a03001c0c81c081c0d81d0203d100c1c0045140901503036009400d0b131034502e28010034514469402a03206065170f07030407100c141007103400b60102805003421003054150b64200051100c20495a41d00403011020f0070448242c02d9903d040e0055028024106541c10241c800380c0050001000b55416100203210350074603180ba05056140485150090b810407505a072240b1b05000e800c1e10307030307158450b0501e0034050b450f8406c0c07510107003211503052007406100d101a00440031800300032440e0f0310b030041401c60040401507450000c4030240d0700e60110504e0f50051104200101e62248503014804e5103942c40c0310054800ca07240254008a0350004207000010441448003040801d41201d4940081440c10002c0040c2c2c00342c2c01d0b48503201c0c50407010a200d034518044c010041c8000c03c800f5a203401e0001d08200090710f4081900760b00303240005a00075414014088208242504440080b107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 680921645 1250 680920395 680920411
    0x313090e0d120207020d21030e03030408120403031107060b010f110618102a030903120b060d110a02010b12070b090a0f060207180912140f0301030803 66
    0x200440d8849080c0d11403001048610001ea640301c1c14120300040394000f44402032010300f10f1560b00041c1d8803a005030300b843d0511076204640e0780b00e040d58240c0d4580500b18902042d00d014616500345565411454400d50655440b42c3c940c0c0b0002030b007032500a0f1321544581440395602a9114014030f0050010181701039424003050036101c0d500746503889010071030a0b900c2000300500c1540c0b0395411454459038540c80045c1d041c0309040b2060180403042c054121910a041c00c1d4000c03189218005a0025a50816201c00c0526150b00f06000c00d9003c04010f00c0c03264000301c002542c01c10030b400701c0c11522821815030320b90b908258401e52011000300042980c0c05c069402008800b00340c004004c001080c094251295070300c420340920900005c04c0c018490b451000701814900d96030b5050313081d10301d4a00d0b07011002503000100308100914400d0502503070300030001010007900b821595134081e0030100310003100030012030300c142d4403181c0881c400311040c5050719642c00740c5942e5240b41004007607104580d445 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 680922895 1250 680921645 680921651
    0xb1b071a070b0a0911040b040b150a090e09150c0c16030203010c050915090607050f0d021516270306060512120a05070501090b0103111f0c02130b03031309 68
    0x198001c0f00e244260b40b55140e00c491148441800001040040c2240700c560a600580e1100a00c40303642d46d22812028150303004060580395020385001408043c41603100002c8071310744030b0400c29014001306015540455550301803c80751585060000320780140c0241c08424803c02d041019545078140c90f11080381d00c02c8000340a41800c03600c00302c0703803402696100e542108280181070070520320b6101803d6501c2011384154105241034558038540582c1d8440814140c1040803071403a000d506000244151504039008803060504c0741c203820006180c820010708004038508100c240015400603510000600c55011240e91b440e41440c100404d044e00c20720784911151503844200107000300d180d40a040718640c1c0076082400c2e829090b074413139000e40c6003250700c3e561301c1c00248006080040c810740654012116644460b1103501400044940e2250b00300702c08a1907410891025406043d038240280d055441717607003440c01c0071199800352110a000d19410f00000c6007844031b05c0680c4a10804441e40700380b043c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 680924145 1250 680922895 680922901
    0x30f01080c01050f07170310090c051c0b010e040c0906090807080705060a0314010e04020f03070e150109090501080a0302100635011a01020d090b1b071a070b 69
    0x340d59206040a07035002c180180a6203c0c10701d180000307000000c0c000c01e070f020f040d05030125100c1c8580d4001c641e07208241100f2501402001c5461041036803556041c01c100c0e1500c050404601d41c0d48800e1034120542c03944448401d006640700312803401000802510a000c001c4103818007400a4002d4001c90001403161940020008400918941211903402c043d0141c1c41c204000c0c01400d5101955500a141c0c451100d10109002d1079412070081c9000716480030641454030420682040100c0d06038400c2c0e0080c00144000112001625001a019090080180c983e040144c80029507170b44000b2089150200005055a0109130108124460343c252860031003419903240803521180034090344882c0d50405d4485070880c44102407005024a041d1680608214080509503103000c85405000da10090f420111540c040244041c0510383c4d040001d0f5160070201003034100e004001c1d900311400d10f00c0244114140007800081c018040350040d0103220140b0070958101e96110070000c076414180e031000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 680925395 1250 680924145 680924159
    0x6180606080c010915030228080402010f170105040e0f030705010614090106090e04020109031e0201090807030314030c070f242705010209040906060e0c070506041b1208030f01 77
    0x4131030f00b40c03041180d0500c01a50203842c120003d410040c02c10140f4034045108070303224007942c4010350310741c4c49691b035481c10781c0b6007803000420b8013030b001d044003060200c12202115106844680c0700c2c1505d000359400030355500d4210317685c0e14110000ca144850f6000000b120000c0c420103420440549000190842040700075000303002906100f48940b900081c0b000c001480516a401c03a400e0f0818014502213a04640301c0c0c0390350f060960f807000c166490320341c4081c2003011540c00100c0795000f080400050003050f4a9901c0182c032049041e8400301100340c0000014610b05040c1c42640ca13082e8106041d1100c4414916120071000c00c68110740c4d80e05c40010030b400c1d03406081401045161184a1035500c081940c001070011041c1036040d0854041d5003e000c071109039203d51042802080c003075007000c40c4142c41c088100c0c0302c490028100c804007403810007560020800c0051001d81003030f800118507421002c41e050125002a01d60070008403c030114107000140100000070710300410400300001c4640c0d0784c95503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 680926645 1250 680925395 680925407
    0x70f17070312111314040e030f0901030b06040b030f071106161101110c03130f0344280f030e0106081006030302060703090f060906180606080c01 64
    0xc0020b0b10034001d0b1403681c455a009040c240a000301800d080000440d00c1400455050b084042058440100785903030740750030f00841021480800185151401d886940b0000744100c0744901e0505072110910030254560707100300c03001000c3c5060450b4503810054440003c081c01611200001000c4904401c002d0304c01140e00c6016051140302ca4580d841080e50903130b01c01d82c6041000c04e2a5603a0740011804001a000514804d09100301561b0780c0d1341e4109461094001c05e0300559400d504000f0140005002101c2e80c0402185c181050b00b40401108a20000148800e82c1c10425000c000c141a20340c0404c0e101814440c0c0e01c1c42c9400c824501c15100409501c0000f0600348006026602800e150a010380d10400c180040d0800101d9802d4445104c42c3c40d10000e41140101c256607100204181a818880285c214055107030a01100507161640c00d44620407503400b51849540f04012410448641e00c5242c500900c40300788581c105090404800401e01d80c8200301c068010a0030f140c0c16588620 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 680927895 1250 680926645 680926657
    0x90c120e060f060118141309110603130c090f050c09090105040b060c0124061409010e0a05042a090305060f06190b0c0d05030c1b030906070f17 63
    0x160081c2601d030348460700303507480c404050400340c10700080c50200e04040a40000034400344c48002c10042081c0d801509008200d40d00340801101a442d00780403000049000114214940c41202c4082d1aa11907251026030700340407100050510b0502540081c81440541000c12441c5d4846001c100c19a946111140b207885203c0005600181d034070018091882c09500c40d10341c64002505c00c0b4100003864140500f150b80300b82511000c849024401161100c20450b800050060b81c500404a1445030405071014025041800e044c001c04032160307501d9450309506240201001442804106003410340e6809038070000d5961132024500e00b01402034180954002d6007100e034848001c21407907030303548240c04055801500e0142c1c02101c1c4501c0039260141d60300380002a0640c60540c07940c50070600c0005241034031058140050100a20401002c0101c00c020703580c14007000081c0c800c090b501255102d045220f050784e142c0d40900b01180540510101c1030000c440a81308905410307014110440d0b682d070500841e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 680929145 1250 680927895 680927921
    0x2d0901050702010f0e1503060306250804051c080402040c09050a0e0c0708071506140a0905091f020d0e0312041403040e070503070e09010501020d05090613090c12 71
    0x100014001544503940b061311442540c0f80030400401213200041c0c0c3e0a40144240d03400d0311010090000504c0e085c04000d401c8408680d822140f0312a00002000c41080811550240005c00000074103000e400d2001c1182c440340402d003261140709024002e4140c200a4030144d010354a01104107884070300400b19802aa08001d01280c5100e180a0000c054050010b12007200c144045c003002c00020704002c090552244135818284029804007500d030125030303060b488901d11b42d01c1c5454212458035031880038000c2e00e40c0207801040c41d030340e564001031a10b280d03c0a2120700c1d010601a140e9032001550103040020315aa0090113950103404030316030380e409003604942c0f00710642c5011800003184a4080308041c0c80120560741400e94450010203103100850316040815000402c005105600502410080030101c40d030401d5035040c100000d54a114075905c0100340040040c200099540786801e8440b403684441039220801d46030500d04014281040c0c0500220345520400c0441e0b8002c2e000300c4110f9502 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 680930395 1250 680929145 680929147
    0x15130e0106020f1516050405030d200c060a08070203120108031c021e07020a030b0703060f35010e0307290103110d081b0114010518010e04080f2d090105 67
    0x20340d2042c100750065004085086c4101080300154544080c0109240d5468542362220f801a02d95400c00255600c0040790b40b00d504007080d04011913940f0390503a0300365001da1600d04050743c0c0344e0805910310700c2172a00b941c2001d14148000521400c00000901c91142c81000b000c07034440c00403121000b80d0040003d6441150b4a401c03090601c0709121020f045902d0004000d0040c0700d64a44410303420b541d090301d40d8400240c980d4414400f809082d0207aa0040c081000c0410b02c0301d48400d50284006503800b4010140c4a00b408108030b480425045543c029004c0801d49a80c0c1050703207000c20003903c0007a80d8400704540024041c0180d60482c07642c41c1200d41191582501200360b82c00c000c0900c001c808201d03a10038082c0440030580e040d08200d26415500706000044c0a0150b2070200342c4040e05034000c5101c0d00c010b00080800c203210f0800c00381110500c8000001c4c0d521145080c0319540078040301c0345082c02c40441e00141d81a50304419481d04603d00300c0c06058908010402e10b014403c13540d11901180c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 680931645 1250 680930395 680930401
    0x501022514060f120601030b0d020121060824130206030a0203100f03080705160f090515040e030d0c0816122a1d0a0515130e0106020f15 60
    0x722000e1640e4285a008003464030b80400d5410741050758200f06903541c10440c4039010480196054401d030982c0107405c4910185401c8550700003400301c0c6030207502c0c0d000061010721442c410034464102102400c010ac041d03500c030207403444c00104000f6031286100c0c01d0310001d4001c140c0c02d1013107803081a00260081d106529541c0c590b500500a5440601144148010660001220080700c1c0515010b5031258403a241c0c0e60015042407031400041002c82c03c2001c1d540b01081140302c6030182e0300b204481c003c0344080760b56a41c085081003034804843d80702c2d8120b0305200480d40d5850000c401041a10920729081001a4205400f00c07001101140c0c282090f91540340c1c0d481701130b0b00883c4020b4007074038030090202c2c500c100a0b503a80344000400007680c040d10709021940c00070580003098500700e40544140303050042004800604503030424800c4900400c9175010844100e000402100c2c081d41d00800d07101030003540e4185000f0503c6003441154010b02801ca4240744990300070401ca4503026401c645100c01b52 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 680932895 1250 680931645 680931659
    0x20c01170f13031b12080f0903041815030602040509090a051b190609140906030d082a04030c0503011a120f0a06020d0608160605031e04060605010225 66
    0x1c82039802682409540000c00300018108201c0c4c042c201d2003001003045005806001034105480508003442c125202002c1144100000050364100c0702c0c2c1001052018990907a02d40003460600c40c3c10700e101072004808002d202c1a130b002003003100c00603a440d0340160341c4d03483d00c3c1e0344603000744038000d00c160410381031001040442400c0c0d0350014001001411858002c1c000f00701100c689500ca07030040341502c0c10801c4034001c0c1364004c65000d0000c0d40d00300d24510302030000a44030116030754604180a07102c40407551074420b803c039441520841c37411518980500c0d04000c1d400c1c0d006440300311855000c00c0000724490406010301460300b0385a4020100d081034140070400b105136049008515889640d0040c411150100700c3c40d04034070300805005030388022000500e8203894450b08055015030084502034410642d540590342100ca907850241e8503a107442000104511405a814030030f98081400e0005010150f40404210741c0c0903001c44e0240c0c4490040c000301e2454a02414051480200d802c1141c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 680934145 1250 680932895 680932921
    0xe09010b120406110d05040203010c02010c0e0607060209030303070c0b0a09021809010e160510050f04061b060c0f0806010e030a021201020c0312090d0201050114060a0207030203010c020c01170f 85
    0x611510004c02c1d446880070525800303410050110341c01300e8a550922043d41001e2103a640743e84400d00c024007500d0800d1101606440040406c1402740d00002189414803040340c0c161040c81d100241503907a2070506240041224a16113401c1e201d10914001007003900640d4424078084540c06080c0062819426a14a12401009040d40d405540b03c02c10902001810301805412a41c81c1202d101d50074104024061040e070012000c3c014008200301c03182110000740d041e10100c500b01d2800344d850828619001c40c0c0542e4402000f004142403a91340b01c59580c10044000300040e05039074103825640d612004440d811200951540c142e04134102e0b00000d03041c200020410706d00c1c0b0000151428040d900c040345194401c01c46c882d08004c0741d00500c128242c0030301943d02001b1807032000307101030b50502c0e244825401c8943c404500c95500007600004030307402030141200031600100200002001854040e44507002c6c03a290318001104d02005004068038041128010900752440700325940e01d402c3e200481d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 680935251 1106 680934145 680934151
    0xc010e07210c05060a05030f1501090b0f040e04060207050f0a1a07020a0b07080105040b0406080a0206030709030b0c04180212060108100902190e09010b12 68
    0xd022000581084000305480c66469948041c1c0b0301815151500d41c0002e800000200310b00c02903980201c0610312400403285682c0d040d0ba960f142201354249210b4209021503c1c115060081c40a0036002e0114600286645e0b8601900c8215081d0181d000319022141c00360001624820043c051024106100b20b0100030030400d0825a03885040c0b00b002d017446461100120001181c03a4420070498001c02c4d004690b035400c034200707d0f40060141e1030034001c0c54011414059450150705141c802c4030100d41f40d0502829420306150300700041e69102804040412980740c40101c08070700c03600c1d010390242085014041d940ca20700020002143c07821413a10010910502c1796002e0749da180f0f074455070300c41824a411142507035042d0300c1403585200383c0c020079640c500c0803803405480c0000c4203070038010703250940316880e05241c0e0800f000003196090240d010f070b1a17400c2c0560203040034910a8190 = true := by decide +kernel

theorem cover : BRFrame.Cov 680755395 680935251 := by
  have h0 := BRFrame.cov_init 680755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 680755395 ≤ n) (h2 : n < 680935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
