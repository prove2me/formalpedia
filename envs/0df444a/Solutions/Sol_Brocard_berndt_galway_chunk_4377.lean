-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4377
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:25:38.186878+00:00
-- url     : https://prove2.me/submissions/7f7c5242-d8a3-4f10-8de9-43bf914ea45a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 787050359 ≤ n < 787230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 787051609 1250 787050359 787050361
    0xa050f01020a120b0d06091b050303040806070f1e02030904110309060a02031e0a0917031608191401060e0a03080906070203010b1f0815010c0201111f1a0603 69
    0x782d802141102d883d81c1a0b00001c2500c3c2e500c00001a800e039032103100104001c1c640f09406c424081c400f58203040340c6a4030307240070502c0c030340352400c15580340154450790083d5800980012542c61180080c0702c601c84403820403180742c0824003811294180498000c100590000c80c002c00b90303145c180034184120385a0b120751407940c1804c082c0340e5100d610041481e20701c1c0b41c00101084005c200701d0100c040420300a00030500340d04002e444000544008103003a211529010001100004060100c0e40180100009070343ea0406c0d100b400d0307a28050080007900040074003081d4000c3d180140c0140d2140080c0d11102c1c04283d81031010103016146070301c2041c0e0003404141018000508668222213618908907002a160b4001e440024058203c54800030b4110f9450340c8441360060800c0500b400c0701d07001c1e480d0007000c5d40e200e2503903230b00c1040c1c00e868007030004000344080c0c8055401401c40655955101e010782e44144002c8100c40300d184144018840d91541e03c44d01d144148480c1002c18801c1d182c1101c4032451 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 787052859 1250 787051609 787051627
    0x1712030103030e2206141305060d140705060f0c121303081c1d010b04050402090609101a0417010203090a2d0b041101030b0102030d0c0306170a050f0102 67
    0x1c1d1001a01e519008100d40d6440501607004d0307803580394a03c400d40c2030900401343c491501020084460b0310290250085c08080111015203001d054030035003014000d9031072103196444611483e03100501652081c0180715011900740c403000014034682c8550442581d8403e0064001860000200c0342c0803171b103041c144041d035501080c500405085a401014154403405441000090003091a0f05400044d25000784030600581441d16450000202e00c02000242d2481e42400300b520421100294800105000500107140150005800200843d900d59400741c9506481c28840c0400c07041a08001c80458100045200b003041c0c0301e40324005070000e60650404041942d0761309046000180243c16103417899440700300c604100440c0c004090396440c3c0150213810254840841076805407840011910424401c4d4000d020b020070f20441a030085103080320151150b4003e000150b050b0081588500c6e0000b04549d81c010307104002c0742030001400c00103450b890014034018120b60100f500364010b200304a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 787054109 1250 787052859 787052867
    0xc08100e1c020709020d0e15060108011a090d03120f060512010908040b071a0a140901020a09050f0f0d08090108010f0e0105040b0625050d020a05102301171203010303 73
    0x8104d50507441e016031660035440058028181e8070f4200d02030f9200e0201c0c0c9102242c041c600c01400b80d1800c0c0c8905115903200c24010b0901002414a590340340003c0007107a880381005400310078135500a14087c03149000041c00002038403112040015081d80701e0000f0300c400e240016008650041031030081007130300101d60b241d20700ca010b144504840024086011014442d5407c2c82201c03a10404802041c1882c00000c9000200756290351000c40c4098000080c5944105108480003020710391203280712245810100540280296001504040100d0003240c0a0300c0e603040740c00c01144114a5241c4078016400010101c0708149d001611b08c0700c030380e03804000702c140307440030305054800a6034041030b0000b410010a203d0320403204070760380d8105082e0103d121144c124070a8802284640c3c165040c0d4501c1c9032003266a140f038614068440d42140d42560081c420550004020014404501008500f00305080302207090036888480b007041c45480c1c1107100d09040c005114440c181d54441400e550450701c0041c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 787055359 1250 787054109 787054123
    0x1407050a08040f050304080609010203190204060c151113050411030610080403051306110120040e1302120f011b080406090303060509240301061d040c08100e1c02 71
    0x2403d2000c0c02c02d03104040c0300041c4211400f50040c1c3c021540301d410207140860003980704951074441e40c00c20503401218000715000300d80c2240da00f41c1e2100e9803140941c0f540c02011201c210b00c070002c10764034404081031500c5400600030302000030b00041000c901c0c5c8010310054a00614030740800d910200200540d035a0356a141c540404550714203d0740543c1c0700e1400391110311400f2540c3da000c45010b40700141e180d83c07000c500c0064902580007403241591051201c5200e00d045607607001320800c107200030711004000064281c0d001d014111031542140c141e40100c0d80b800100c5d03a00840b140c11000141600310024000c1d40c07074000c104841c0c1e00c071030160a0310040060f14007500040c0150b841e461550140351281d04004080c1c0b6000b002040302d0300f4a1603002240c01030003440c80b00c0701510103010f51000d10f8103206000803a4250f00e10a40ba82404003000078442900410071514065a60b9011071101c00402c4a072820401030b84001481000765604580b8003080340d01b0000480006c40400420958089406 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 787056609 1250 787055359 787055363
    0x71d100e01060c0809130b030c01090f140303040302090a05010e160c03080a0b3102040e150a0f030602030a06050d02130e0a0819110a0f0f1a0405011407050a0804 71
    0xc03e20f0200d40b4038201006100700303840d09a0190061508046040c004d40c4000c1e03c0c130004400300d4881000000040d40c4c00146442044085038000d0400c10035490b0104000c07a00306030040c240c134078050b00d0340e000428001c0180c0307280703840f42d56503401071003658289090310303401120302080c2c0004a03050100040c008bc3c0350903401070030404018082221803003107400131402130394020300d401d414130800480b48801d80c810410810620a5148034104010210320858080e903905951340046a6200560001d02d030002c10012500017984520000340e243c42500d06401440c4101005680c07070074070138003000075680709802a40c800d00b4007524840040c0c1ea0b032030203880c0030a61a50045140c00c845440c840c1400b6080201500d4224001b901d411414440c41011140300b03c41d4840c0151843d003500c503030350782e003684280003860a01459480b5021401c0c03680ea40c20b101e8403442d603140c001340c01240f060440c1d074805e40d011101d681d1a42d41040e00c001c0e6100f0050750244c02c91500301e00b040d80c090f10003080ea031809040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 787057859 1250 787056609 787056617
    0x31212010b07110112020405090403030b010807110705100c08030901020d06140f0d080408010e0a02180408040b0f13030303090506160c0b0901061a3004150e071d100e0106 75
    0xc5d00d5034812698060354010540200311b901c86260605002c0c000d0300d03210300e83c2da0008a804c1c0c00241924041d40d101448440f60b84001c003710760404c010711800c0d41da04684102441329104a00c400100b420740114401e000000000d13840da141038014a09942107900001021603d41031185070300c3d2100f00c2d2070a0a00c9084030030301a42d4040741000e100c28411504201115403e003086600c0380c01002400c1050380344255a2481c40c0c484030b600e0307414040c0090b6401440410100410407120852002a200c5803000580d80c900e02026070b4039a04d072040c41941700b100481c3c1c03248000b505109080c010315a010000901d1540302e603e4036a030040c8030400703c00c1e00074200c0c8608404204900740c250310a601400000c0c400e00000e55100428040d55048854454128002160b9014080785445450a0744c00d6044042c06840d480350355840750715103900030072003c5065488000d024540e40070006140100040620100c000c81d1218050700c42c40002007100382d5802c07405804010720040700003e5070441d02d043c90 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 787059109 1250 787057859 787057877
    0x10020f0c090114040c092d050415030210050c011401150e03190519061b0203160308130b010312110f0a0f0215070501060609052d0f031212010b071101 66
    0x100f9a0440f074650000d6070458104940c1f5148861416001d984100c0c0c11780740d00c150300c1d6a902c20003064500e40520314050b1040c001d0208010305000102401794001410250b042c0f00e84400e0140c2101c141e1110320180d40000c500400c444e10009030207480001c1d407494011888070302c04021070f80e9082480c0d03000d5488444c50f00a203040c0502841b9408040302080d221402e00c420908010018103851441641c052040b01e4030106c00a00001c12102d2414070b41000c3c0041d490135407007e940c42c8100809824021400c4c4141c40c00055500645170b018501c41d4070011503000000000034941d03840c9010490032680300443c0c005e110040000c908100d1a40880840c04406451001c0f80300c03030b16a010760007001000804d0033003c024043d0041000ea07071560340d4903041d40ba5a0b50400650f07041800d00c0c1c4d0904010408004c03601d8a6030852180700760005801034540d030408001091400c0d04603c00d00503200d078049160b01c4401440c0052500400300035590314241115502c458907948075070300d0058103101d139140d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 787060359 1250 787059109 787059131
    0x7030603080c0106060915080a051504090b19091e0c050907020c030d051602131b11010506030303091b0d0204090b070306060927090210020f0c09011404 67
    0x142014018641c88401c003502c2e0b16125103080d000e44001d000d4031011510ba0f0401252a0f82c00400007041b030b0580e59030740d0700780c0e4403881070000090401800c000b90700c000034102c09040f901c4601900f03101c540b00301d4008400f4070f410640c401020403481e036104d1001c2d04040c255400f003220308a004a640c041283c1b0f4030390404892a0a01c0564166442503402103a2031003003001454003c50640c1d8100010350548485900b010000ca40c5445601c21011446119034900d40240c20802248128008034520024110071000c003c600b04080c0d1840c01800904038001758110f6000a009180c0c0140c8160000c0d41107060901d092902e450072403009500142445120040e140d940400c030141e03907038001d0001c0200700034600b80310b03651f03410482c0c031400843e043c000b0004120b84540700c41c03411220b042044540ca207000e0700d00d2080c4010034030301304c4c54020b80300c00901015981c1c0030081d040d07000458004160404211540d07900b413168624040d40710b800d05000400c0501d100300300428090360100c40000701e000041c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 787061609 1250 787060359 787060361
    0x30f09060706060f08120424170a020c070e0601200c0904080403050c030a0c090b0d150c020f030304030e010e180127023c0d0614061603080703 63
    0x301e0024140d181000c03400104540340c0b480c2d801c1568405001d80b02d9100c0c945107100080d101d0382c400c64200b1114030110b52442072480c10b0403942c562503440d0990702aa9900a4a41d8180b0300351a15008150300040407070300d103542080101c006003000709100000c0d142010000e45600102c607824102c4482503c82c19501d01018020030b050100b006180902c28105400c0510352600f15000466580c41400350b40d4000c0d01d400030304040500c0c1d000002c500d160b030030900d00c0e03000f509003d410560852001540e500008050070126202003002c804002800e402040c40203152208a21440c0034540003001488080ba50151881480714000e003000302040402c4000301d50800300b280c601c852003610b2100046080380344d2600c104060140a1b448105074081c01410200328401c4010400c40e030840281070714880c00118404115800600c00d028018141400c044a80359103c0b224400c01780341e580c3c400780030b102c9000c46010407850080e5015401c08843d00c40b619180b4540c0503014044c003a0010025643e2486 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 787062859 1250 787061609 787061617
    0xc0e0d1703130804060f0806030c2107050301020408030a08280207020f19030533060f0315010503060c090306060f0f0a14090117030a1b1a0604050f0702030f0906 71
    0x31183c00c40340d60701e036500c10080c2030949104040c00000c514401180c3d451074001443c200c500c8004000300c481100c0c015407026000021400d44403140503001d400210395400f03102500042c401d2901079a0307190248a002884040b009000c1d4010951401c15a000603c10b00500c00c1c144020341e8006035190030034000a1182507a24446079804061229001c00036500c003040c03035046900c83d00455800000303a0390a083c100b400043c84613406201c42c0300c5039040c4d02c0045141034014001030a5122021404c0001c2800e10044c0d5403116200041080100318034103041269552101d500350f0028103019882000903180c44014012600c545800e0303240031003564640301c41c4402c580c002403846103480c3d500c411030940da060070203449108004000001440b4600b0800c0906480f0740c90002d149051014a010b0b1800d00c00e100d480c0b10400022015540001c22079900035000404d4954007000c20b2400700100b01c00d603200201030401c52030202c1309001005400000341c800420700707402201d8882031107070040788041c05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 787064109 1250 787062859 787062863
    0xc0d0b0f060403080702040e0d0203090108252c060414040605040609090213020304050a03110f0a08120709030c2c010b1c0b150307110f010c0e0d170313 67
    0x900003000800c10130400014454030f4401e80301807081c16803035950140c44003260701d01500560000c00403255158400da1040da800003040400c10700c0c0c8202250340030302007003034101e91314081601080307040f5280302940d000411411101103801c104000040125581e401a0b200b0020440d0f0700c80355403141c0e0750300e42e0440b4029150181041200710703038800c008005880c0d1400146c2c040d095200c6042d024040f0360003200d03c100e030804020b000c10002030390112058400c1d01441c034143c0c0581618130301503c80c00e02035068030500800065440d40001c50180341c010a016240209009680d60104002080308000c48115090500c0c6c174a40404540e600800c01c0d0301c00d00710f1802c600d9440c0004155010040c0c080c041c03180c07907a00584052040da58045040b6640101010340c808500100100c1d5022010021a0b1000b104c1c03400e40d0940c85001121881e11003584c5000720705135100c3c0c001590280e8403280b1049025000c50b180c04416410b0f8841c1c1d4001710580c41c01000ca00000070000314503e400c8070281011329 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 787065359 1250 787064109 787064119
    0xa0f110604200315011401053105121b04020c0a050304141219060e030309150a0c12050408130303020304030605060d21020c0a18050901050c0d0b0f 65
    0x100c0c0c0362401441000041c070302d152900d140074120228a0a0000f003100d8040c111006011030f603401e0803101d00400900015090400208100095140c62781151030003008403081c061541103208008507600d0031140b0380121f401014400e00f900d40192001620010700405192000c00780448600494042d00c5404225101c1c0e00c5450001c501304000000204202c642c0d0070b0128900c0c007900020441482c03494980d8001c9544540c0014000c0b040120b120341d00d0138444c403130001e011000114860b0464108031401c00340d5800801c10f1803503034600c41f0103260b441100c107402042103103103550b03014094140d00c01440300810356400000b1300300f00c0841c003100c01d190402c04541c44095902c3c60000c0d601c1d409030104a03041410040495440c1c1001d81507206d03c00c0d40310095000703d1b04800d803130f00c00800c01da0652004511426a6008040e200c850505003c0d0028203102040c40d038541c1010800d60320082c0442d25568509404c02118241841c2034440b01c210380f400100382c0d8000713000050240744c00c850109503c6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 787066609 1250 787065359 787065361
    0x6010c2d080d0f0501030302120f07060504081905030705070b041704180e011a0123041d061801120c030501020325080108030a0507060f0207050102070c17030a0f1106 73
    0x1005803403014041c2c2c00c0400c0c200740072603d00e01a1080c15a882880010056884001c0002c103100c5807001030194540130840c83c5003401c45580382c02054a2040e82c0c241c0d035143e030008020141354107203140c085a2180c6070030205c2c0703036003480c2c18024000d20038141c02800c03907882030010504200c0b0301e03440c3c0030201001451650b00c0d1900d035407401c260740c508508104089407414110480440e010f0280e68034500020304444078044072a40107482039a000c80d03511201c004090780120b000360501c00603001034085d0342c0b00e09000040e0014200181c010107440c442c031501c0305801c4400900604405241591810305440e00c448095180a904402c02c5810003001c4d94000700c2080741600e1183d40404808030000d070340d2034980d807003080705440c07101080c00755050030703001000304045580c06880106082c1e80300d21400640352801d951a070b030480c0c00150044529940001f135080c1448a51540d8034040c0a21032803018000352819055540e91113414403030303014040b10012101501d8003c0c104c44000140c610166860317 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 787067859 1250 787066609 787066613
    0xc09030708010c09170604020a06141b0c040c0306080304060f110327090405060a0c050702030609210c070e07030b040504030e0301151a130b040308070c090506010c2d 73
    0x1601d00e2034012401a20040403103104504000222a801140c02030209e1006504242e011100c4541c848414501580104403010414280560500101d100b043c081c11166041204110a5410980d030100405041041c00d00c8a43c034007000b21011110f26080941c190118070300d060362100765039000c8803003a000c0418581c1c160800c8805280710304214031a440102d0440c002042501c95003a05d001e001e584c46100004c4501c082a440342650840e039041c000d00300090340d03000034079101d01110080c0c1c8a402400d2942e1211490b00ca4007a01c841003042007505080d4126103050b038070301c0da611440d4440e12140c00450300583c000e070b10902c256035001d0410301080c945070a003c2c3c41c12800303981d6a4080e620f0f1088080801707003c903c10b0700c262508500300804402035502c41c140590000c04859000d00003074900000e4030034822000b4002148070350410b90319518941080e40003403074181c0c080d8510500341420009580e0384885008092544504100380c645401c1010108000203030403507040c90b4400d0309610b02 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 787069109 1250 787067859 787067867
    0xa060503060a0c2705030717010605030a0b041e0602040b07021005160201271205011812050318010203070c0b130816030203091e01030507090e0c09030708010c 70
    0x41515000d40440e1019100d0010030000c443c0a600c0a0b000208402030202c1002000c110134507001050203030700e000e01030720342c00041d0030100603900c114481d5840b01503407402d804080c060302000340800c40c054040e19466884004c45003c0080000b441440710300d043d190802c104020603444950484070442d11607445a94040a681c094001603111b0140b040201c043c1703610400441d0600210664401c07101101c0764010340304072080c10a90250f0400501c601c01c0030904c1c0003003403402405000e608041000450800d642107900561030a40c0c004150780980300403440d000c00030700d9078003004d2609030350b65903801c040c0340020000e034810844103500000c28008500e1740110010242c5005403030341040c5485002081d625018a880c2c0103094003410b00c0607162940207951909030080c06030050b00c5c46d2400c140000780c0c810f1281842000600040004084107503407501c070b80382c0d10070300364140381d000c26003845000342c070f43c250003001c81500c500e00241c40b20842d00c003400041d00820f4190000d20406082e600301074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 787070359 1250 787069109 787069121
    0x1d072a0b0a06031707080705031207180b1603030209041a0f060325090305061f060302030708040210020a0b0c0706151503050402040b03060f1602030702060909060411030a 75
    0x600c0c005060000300d07031003094078403800049a80c4900c2440040c503c408092040e5000008142c03040d0b0824042400411010700003001070411524075250640740c28140039200710300c00c2824000543d5950301c00e02c0103500036000c0782d0b26650418860035004034185401c902900c102000c0903000f03410058054a00640e0300c00d10411054100c403c42c2069144400380101030000301c40039448841c1c9172801881420002c441e0311a49165850304079413a039200e0f2181c600d0458299110135030030300c80f01d0503800d00710151180d0038080e18840c0380540c61400c00c228001d2180c140640064032501d40f42641c090103030300810010140c2030744000344140300d2400c0c401e03402698101d01c80644419082002c203800717080b19203d40c041038440060803010420f0303132090101d0041c02c0040089070419980d0f807807402c0c65501081900e20903c18005600c2c0b0910b010a0307a51007100d56035040c1c0c800e44d4024041500180c3d03503c07055805000702580e03402c0056403800009030260038601040c500b5000000140454105990429 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 787071609 1250 787070359 787070363
    0xd0e10050c0c0c04020a1b20010f360f05040e03040f0314120708210601020a0305130e070c050d091a1305371d072a 51
    0x4109070740d21050701c1c1c0424420b070300e08400d10303412032030300314072985000d5000d0881c8001c507142c5490001c1d0702110341c2404003050002a580f0580d910110000e151100c0a140a032400a10301040003009814010b011540c00104229000d01002a40c01081400d043c0003000c5155900e614003d9654408800e02c42d4079950048601440c2003005106564400008607400c913004060602c04031459902ca450801c407840745100c0549c007540e4401480c41d0b000a015040711030081419695500070042801289004410508041e450120800020f603801140580c8560b0701800c0c059560041407032904181c1e01c860304280c0d084071485050040301e035400800320812a211300c044031052403000c0800d8400c1181d074030800c4540e252508580c0d984400c03c03009440007502c4030000848854607100010040c1c000c001c005c243c400c64000301041000b074182d26070784000100302d40c1403444500342200c1d03803ca0003121040a900c01d00100100350f00c5031249203030415480701c0c47e11501c0707400001b00b424801a1181841 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 787072859 1250 787071609 787071611
    0x109090c12020409120c020108100321030b0d032d02060112080c15010303120e06010308071103060a0f06050d11010f0915030f0e240903070f05060a050c131a0d0e10 72
    0x1800c034119a4030b0304015280c2033200000302950342800301054a00140c0c14404254a40c2d12421241c0c66000340c1511442c4240c494440c6c40f910f48080305103803a40007d81c1d0030402c03100b000c1030f92540d4006c107020741500d000c1900c81e6140c854500b0300c2c020380d102d200d402c0c4405110f1120b1030440c14070000300fa141600d10903a01c000050101c0c4c51001c00b99500f0001c40d1501d034100c00010400070b08054024610740b4824003d030148080c0040000741412030440d1403040c00303500c482440420808600c2050003030b081c111030046420903e074840100c48410030001c68180aa4680000d803003034043e0710410003e1440b0040750402580d4a080100500490204005110309080440443e100d004c640641d607441c500485003030038121032003c10070030b01000e40200c01c80e0008001180101e24503121080364180100700500711810900d903098201e480003001e040580006001c01000034200b03800342002c40346031050501c0004000c400801aa10481002e0300d40d0b82e00c0c1c00c0d01310032804030200b18142840c1c04000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 787074109 1250 787072859 787072861
    0x60f0f09032a010507020a090507030b01020c180a020313050f010e010f0e0d031d070b04080f010603021503070e120a02091006090603020c0a02030d020601030b0109090c12020409120c020108 83
    0x10505812400002c4840c514103000d10702e02c603155203d030010b01011400240014141a42c0b4800707001140d83c10b49050002941390046032159580420000040701000c0e81e290198003040000d4145500000e0700681032550000045403080c2003034603124100c0c5070040c0980e4104011028914020301c8c58a0a81000d54240007202018040501c02d03810103c080001078818101d03206021402000d9080c4000c80c40c0103c14201c0c0c1a0705010404100900689020141d58604104040385810300100c00b01d0002ea041060500044c0ca614610f100c000365841d641c1a2242c480e08401d688c40c0c40480e00c0700390006038541c1c80c6840300c20009248a01c15000780d44500642c0c6400d0405c032800802e40c003511340441c04607081041000d12035402003003455061000da070b1228001e40e00003030412600d021041c0050b40010010b005115480380001d00420001a0400014065545180c180501c0c0c1c801c0380c42e103040701d40607a03007551580d4001034049548040c0951251041d0030000d4491140808280c0c00504040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 787075359 1250 787074109 787074133
    0x9060207180f14041704120201050c070f0f05011106161b0b0408090907030504030516020a0e040311190f080a0513080607020f1527010603080d0b010507020901090506060f0f0903 78
    0x100c201c40540b07144207c00214443c8580040d2407039809052030049900c0344001c0001e8000c111b8050764041d00006150001d140d20304000104a1241c021000080340c1040003400012194010244161070a604000c1d00407401b80394051041e45a5a0303000e042407006a0800003001240703c014103290742c00301c9002204c1d1300c5111085085410454009000ca07130308000030500f1300e41003840e400b0420301c0141100d4180c0c0d26848401656103040c1c03000c07008261072131a1480342200070300c04081c0c5031400380074000003c115600c03144004488642d0141c03000701c000940f210064801d4040303070800c00002d80d440426550361100c1d80e03956401200c0300c0c80107010f14252040801d01c0420b0103441001000244131550300d0748030f2088118840180031074002e892140600700401c4086c0a0400118040c0c01d00d0b0b5180c55401480138140d4016440c00c0c0e04000007002160010303170711407400505403040380000083c90360303800001c98954402e0320320500c0c5141000c01c034410a925182c00824140c00b06038241c441040100c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 787076609 1250 787075359 787075403
    0x225090f050402010237060f0c080c0702061305031c0906020c13020a030b0d0605100b190e0a180501050a090219030506030115030b090c0109060207180f1404 69
    0x1070b10020b0040c1c00c00031040c0000d204080c021840e02d0100440b0b0310340d00d5a0740901c2540301e5a40041261803648451032245c03001d072903100e0070f11000414200fa28162420080f281c074113225200c00207108600204c1c1d540f0800404048807405080051b0860b87d603002191504103450f44042d001034009680c07128041100c40c408110410710280142090741802c1111141c2d4010b500803002c4d010415a49001040d5036a40d10120b03440c41e540100d00004142c02c056030a50940a030b99046040000d404220341000502411084019082c9602c1c1202c52006d15000185c1140001d40c0b21400b0b0a4601041891072442640894101c8074100c8800c01d5495071080e01105902031080e92180d0707410302140e62882c25000703130025580100001c0000880381400c802d880d00c1e0749201e0b08155902c80402e002c000480b40b04000f07070f030418202400c2c405a500e02d8900000c3d628161030140b600b101c001c0901428501c11550402402d40c03104013800c0c00034104905011a0007481128151401c00d00c0201501d965500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 787077859 1250 787076609 787076611
    0xb0a060c022d01030b040e012a0504050114070f0209011701180203030f0307091206020316020105060f1215040b10060e13051e0a0c0f110d0e010225090f05 68
    0x11020210105840c82401540244100d590582e001a141d040301c7e800d00380700380300300c085504400030420407110700030303030110080c0300e0121a02c000c1c004104014805682c0281d10540911041030140d0394501e80c500c0c5c2141c0807483c2a00003074011455000210b20740c1610003005a00040c01002081683c03590031b00078403800d12800c000ba4040c2c204120400c041541070004582c41121810416007081d80d80c000c0c2d035009101e8181c251116039010092141010701d04c001421280b90a00c000c0c0806e04004000440740c040e0f03065001d00c1140038058080140d00c090104082c01d40564550001394601410600d5404500701c469115006210201180403801001d044001d99005814609817054948080c0000c104c003418500900314200e1106c4072000d100b4104502c03416901170046420301d083c0c14082c0080d442c0004040c14801146944082140001400388806a403841e000d1a00c404a60060307040004840689103c06040003444e0110306803e100e040450304c210208006076109034000f101142d0b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 787079109 1250 787077859 787077919
    0x9060c260402012303130b1614030a09050109080307020c060a0215060109030210032c0a0b04020f0a09050910020720011b0303060e0a0504080313060b0a060c02 70
    0x30031200480d0255104402903825080440505034079214a500403081ca5041101e90010b03007071440d100d000c1044440892650402070b48092403440c0c45030800080d00741131b0840440140b0000c0800000c1d1190259045200c003036030060000c00511505051031861039100311054000351240c60b0340000c040c14007008550340700245602904003250018038178402d00c0c00191000741000080c00000c0056038401c04035500070b8442c1e80700019a0b00b05502c840911000f4404801c60f04d81c881514103000150105210340381d11381c003c140d038007103a4451001035191000c01445c10b812007401320700420007003047d40c07203140248017a1085505030100300d40460140d1080314801000d0f44a8041500c40304850084242c000c0c244c141840d20341c1d80c2c582c018400c40702203900010342c0025180c00c1c080183d1f003401d00c40b0a030040c01e8040140280d2409444a174036034400035058120b01e008014402013400120750144e644018001c1040680d03603900d1a001b403491011010a134031030605281d146007000110710307406004507 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 787080359 1250 787079109 787079177
    0x23180d050303131704060203030a0506040501060e01030e0a06020f03040c05030a0c060c020a1a091201110703050a1119050606030109120c030201020c010c05041a0702030a150f09060c 80
    0x36440d6148039500c4440f0440031078010305800d0840111849180103040509840d500440c3c0760701e030052003001a15806804103001c0d03440d102c014003c00341d10980c91a070304c017028207012a401056800d00d170700d40303581000040d201901c041010078406000200450040d03000c0c8055100541c0ca4504140d203130301105c040189286c0031242c04229403801210b000c905540028480400f86540e102130740a1044170b12018050040002100c0e041c500c0c05d82140c907899440600200302c94015000e08806030312402a0190900c08046502d1403864440d400c0c80c500d0204080c20f40d401c4400c03400300e1301c4000200442c1215207014000000342142014410204126045480056002d00024040c2d4185905840a9017155020000b03010540024000c0c50340480003a034406a442d0b244c0504488010751040158021076810070140d0003698000581320f02564000107203100420362000e0a4006000c9845001c400d1418501c103038052200783d0348000038111243d00c4004d45c0e4001c40c003125816641290a001d12a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 787081609 1250 787080359 787080361
    0x330509181504050903070506090f0d09030507061b0f030f0f031a1c082701020f060f1008010903090302010905030703020105030f07021e06070306090606021c23180d050303 75
    0x242c90160490750700502001c013034900c3c04545844071803c00c0e0301100c80e090079030b01003884400340e020100100c003022600340c03504a100c0307800c6030744a6459074034601c588800c000003004042002d0b40010441400c1030f6010f054034404003403626024103a840700c4c68800d804100d841180240c034038001d005104917a481d040d1790710921030800041102442c80b81d4070b04821056052500c80c00101d10348003c0c5003010842c3d200c0500d0b4030b40100301201d9483c0c039402c0a13046400031900c0107109078002460642011071081035000659801007d004401401c1e88421510343c207081044080c940c0000107841520300070398030010015110400c0c1903030b4040c0761100900040c0704000051122a00a98403504882d680c07041e100446c04001ca948011078440701e00c81840d4001e8002c2c860200c1c1c0610940d0014001100709108080c9049006903c3d0050349810400c1c0d0401001005002803090f042c0341e8100e4a4007280c80c1c80d40201d1020380300e407500265000c00b1151454104135449182006c000030003ea8000001c40c51 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 787082859 1250 787081609 787081651
    0x215010605070b1f170613020901092004091406030313180f06170d1e111509030711040b0303040b07080405061b2533050918 55
    0x803d400051000c00d000b403aa403e80d05a090001c20000010002481c1c103000101403980c0b001e06214015004558032141c0c9020000140c0320b08030420b044403984000016804070004620b2010411900c40c1c0742c02410004011403126803a601c01c03015200f02c45e40007041c036946c03402415520322400c0b4036a412501d0201c010440d0000303031500328820042c151408561129040c1034242901c10b40d1304000c040c41024103207219840d00c20020940c0d01c210f5850584c1900304402480d1308160126000101040019000c5188a400c204444040e400305400314194603d00110401c1c1c481e00800400c1340c14041c40e00f031000252401d401214028200100518a098500082c0c4441c3d607203d20001c0302c43c00070611000501c0c1d0b41c0d41014103000f110003007824100303409114103142403a01c0050482a000c0101c050b1b20007505c080040d80d4103445001c01800010030f100c0c542c1e16130002444500d202036076440d140010741140d12030060800c00c1c0d0195075210320b106500b00745854015017114000d00244070190031900d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 787084109 1250 787082859 787082873
    0x24091509031a042d140c10030501030f1203150602301b100203040302010f0b040e0a080c10061502060711061603111b0c041406041524021501060507 65
    0x40c00c4c035042980d0214900159202e0031501c032441c106521076040349100c140241405d0211941452807454104007940c11136481e501f0300c107610840503048c003981d01c804280c014081c0d0b00c4140708140078002c020600750360307140086da1400a00c5110408406c41d031307140d69207001c001c00f8420700091403014550800c1c10702110b05078001d00021000243d0f00c19080c04036280c1045100035802070707000c1d034004144a2507520080081c1c41e070580d0594056490508001c04214010030b00da00401e501910556417400f28003d4180341c68980e04000f01c00500d4070300001154008020340c65080b404607004ea8003a5070304c8d5942a070300103200e0422803001d40c00120000c0d90340c03428440d4215000419080000b141c2018012042190b08000c041130300c1c1d22500c107000959000704100b174140d8440300311000e00441c202c900407104145000741c83d8030b005548600884001c001c100d40c840d40603100564010390240280742c03004c01c046004112034009402a10109442512000c2c081810703503816032038031440d0000300e964244c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 787085359 1250 787084109 787084163
    0x14090a0e0705070c0602010b030c0f09040308040204060b0a03140f07080435090a0e0c120405100533060f1b03031005030708060124091509031a04 64
    0x10400c94100f040d58009000c2c2a46a0f002d821194000103418042100385031a0800d00420b0038401e82880f803001c0c03043e98826000d250310607418030300005280c0b074034400320f070241c42d51750000d240403880482d00025056056000c9038076071907190010046500c0f420350740300d0743c140151203850014011000003400300d0000d012503e110b00c0c0108000020740866680401c0c1007040010a00b03e00400140981052401e1417000d0003034982200c0111640c200b1150304409845451a01e403a100c85480c001001d2200a014000300305003021018803c500d00102918400601a141d15060214840b80c407401d41c5007844100080300c4003e05424035110300c0c4030700f103c0f154000c4100d40407142c0c809035510802d401c0c01e00c0618052040a20311210071402c0c10105030904106070042007465000c0c5004001075040f01c81c0041d12130000d00c81110290000c5802251a4a8550060745070514a6522000380c0750f4080c100382c0c100e90240c004120308a02ca07100340c2c44841c1003a580038140541001c80001000502a00c007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 787086609 1250 787085359 787085371
    0xf150509090f0703030e18090c040e030d0c2a0510020304112101110f040909050304091401050a050405090d030203060f030609010204080105100308040306050a020904020c0c0114090a0e 81
    0x1203082d010070690003407414545410403000550f0b60484910340e07091514016028102d020300800c0c45103001400c15942d040e403000041d20503034481800042052042c002c42d900700c89404400c0c0900890260082d2080c540117407520130b480507404266107001e18031502110000c5c4d10601420041900c000080301940010700143d44660601c0c02c60b009a9a032010700e8010407401025100c002900421601d00f110000b91401001c1c5500300f12441c0da6602640440301580d580c100005416842410503a1860103230350008100c4501c0d18180341c190f51500703c50541215401c540e0360412a8890303003404140d90042d5244c3c00154080324143c54628000d4000e580d00c100050000a5400d40b4800002e00d08041a00d41003600c0e540080c040c4003644082c01000d900104c0007200b502d041c6d1842d0b5940a0904c12440054449540c40d0082400741c13209804652020100901c199180c0f20502c8015840e0041d000b051400300700d400c17448903284001102500c0403154001c0243c40e003149020354003a1800c1e4001d0070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 787087859 1250 787086609 787086613
    0x6010501090b283b0103061a0a0201380a050102060a0f021908091501060507060c050405102601050a03060f09020607050706020c0a0b0307112d010f15050909 69
    0x602e901c104800e00071082c0c200c00d04007070107480004d07610000304040c2241003d041500b03110041c0407101c010703a604010031a81c0e03119590f07100511201240103140720445220880c00034141000409101c1103038580303000c41c101e010a410100c000400c00e4080301482682c0c09600450002601d4508542c4154108018180058a000c00310213000031030000303000200e07000c5800c01d0280601e00c0703000c0003000307401c490f5240366202e0355040c1203000c1c00a000e10300c4001c2c010f42d05c80d010810030511860955000700070140c180d808048001502415500100e039443c1d025940c2d642410420519a0709858100d07900a00f80304c11040c1980c5400000c3d00c000781d609401c05850700708000042c1c5505000300606030056010302151401c00d040241000350100f402d500c031760160030702889a102c80304100c9801031004c0c02c2040158030400300c4241041c000c407900c02c02061003034403118020031007141c1845640a102000304400c2c90301c00304043c1103942c1c050100c070380344148803014407035420300130820390b007052107202 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 787089109 1250 787087859 787087877
    0x50103120212040e0f04170406050a1d031509190809031c0917031c15140f060d090c080d03060e09070b070203160b0909091504171b06010501090b28 65
    0xd00125803049c0e001800048002803640c40c41680a140e200c07141c0c4100042e0852440310300700084da204519846101032160a40c0440c200000c2000742c160707041c0141c81100ca04800b0b506026840c1d810062106019008031103d1000c00780800388905e0f20441380751201e86601e410f0203651104003100c2204003001c0d220407c07540c68290b0366012104203900503600d02040201ca030b50465400c401c0158840882c49000b4401484243d448178440444110f0580e0100c0e00c52501141c031a028090002014140101082d4040380000c0302140c0f12207240e00e6510103002881d665908501d081904581d104e0316070f00060810b1220900e08401088550b00040407916010303501c01103111000f006a000080340c0c0e8000500f55950304000c00c0c01030b0301c900103001425550204903180139035040001d100500900402030704d0440401e00340240e0308547c3d40319400300d50800c1102c80081e6203e20a001d024041800c1002c00104145004101da248021450512200781103108910304184141c002c02c0f010302039410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 787090359 1250 787089109 787089143
    0x8130311010603153e0f0706020a0f080907080a020409050106080714041a130c050f0c0c090903030c070b0c070204020d0209090615120c0d050103120212040e0f04 71
    0x724446000e0a40038000017a2401388034400600300c24030350500b08103400c3c0c1040303a1003c404100511200c4030591025583d40b050f100f9200b520078850000028102c61002c91882c10360341c1d101d21001c101102c152148209516400503a81d6200d030325114803049540079103204c40060030141c020910301803041001203030140e280c030001402c0c039090f03401003c042411703404050740b20b01e0140907280380449002c10b10003500d01001f011036400000000106138042d100e0082900c440d10403022160b450880540d11502d039002c40c035516481c0c4100a2113580300302407000102d40d00c10000300c1143c3c0121f000c1c40307041d450203095a0320a40300e13544c02861940703071070000e004c40809a00c4900040011080e00380c40140e40d40810702c1040392020b0080c11907806071104000b0100400008001c69140441c5100c0206569590015400c064403c1d515140e14243c00c1c080000b0420200c034501c94081a002c0d0252001ea840300f410220050140744120b510001c00c3c10040307080002403410583e04036029628866070a0303192 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 787091609 1250 787090359 787090373
    0xc09040225030210200a270b040e010b03090d0f03060308030a09150c120906111308060a02130905060d140c0102010e0f0c042403030e010f08130311010603 68
    0x1d528181c01503040501030070a450660711a640340c080c0094440f400f8040d03003080042940c001c5075014014080060031080882805000b04407113602d861000035040e43d03d070240d8990581107403190402c8446094004038000d00d500040d40c5c800c0708003c008006d00345003403108513460f04040000106050341d030900400440c484400541c41003210920204016002d440c150003402d0306141250420762330004000c02e510303401101070080a04011012510200c00d0811900920720707256200f1000d02c0024080305020500007044c801c0740d0f800740545080355a2107481d84168440d000c400321404003505428014160325612841e006400904000400001540e03030382d5040c0e020341b19001065002c2803030040d066909000c0c000340600030030b0207488010001c0b40c0c4665118083e1200f00c4c8101d03251050b60918800700080c4403614280049980100c2e6601d0902805401c0b800c11846c3c002400001c1d402407903400341105e5802403c06920b40e0a542e8400d0b2170440b03d9215280c000a619500c44030000042014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 787092859 1250 787091609 787091677
    0x12240e0109030f0318021e1c02040606020d0e060d180f14070e0a020901020c1005070204060e0411040e0309040c0305010e0a09031407050c04020f0306090108060c090402 74
    0x44200004800c111418007611129140c120242054103040110700341a07683c2104880c1994107949042d0344031591982c500152041c0c000c13aa03040400b03c882e500103e071401c1c4003041c0540c001d48040040c00d40782d4030120384459400d204c403c0490410540000503040100c01415210085200015030590000300c0403401814281c048d02c064103c1c10a40c018401440000380c21002860000e00f440c600e0240e507020800d0004003002c500700e40c0410f01d0300d40c69000344060018807d008010082c9980304e00005000c5403c01a02680920310b004004182d10341000910b038092030b00301614202200c004070402c00600401d41890f091030100b840500a180ca544c0290b92411007135403000304042d0705042e031140711118010000b40f10541468460000b10750021003003140451380030a415031b1181c1e9400c0140c50b00c1c0f50b084038660000d00c00a1044001b800c850003070340c0190341c1151300c19001c1c2d03610b8108541e03c04007601d004403417040800c01002c16140c5a070007480d0f040c2500c0b6200410010f9440c4480701c0e07100b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 787094109 1250 787092859 787092881
    0xc0a120501060512010801020c0a060e010b0603090609010b011805040513020418031b03090302010f170a0b0418030e010f0315030605040302060c13030b0603010207060f0617071224 79
    0x1400b084e00020240c50010490160041d0002141401c04400e02c0b20340e1001c85040140c41c040e9200c41c0c40c2004d12003900202102070000c0c1206030703203007012000c05650b424100c8440e50706510709a1504405c4d07100f002c00c0b6401c1c0c9500042c51002508050411006120241c0703500d6000026909500040c0c442c1c0c09000a15040513494900050580c20060084146582125025265201d0071800a60024100c44c01c1c0c03a0280303842c4100200402041d54124100c445042d42c55413003004000940480f0342119125640c156018480031808041040541070540f2000f0040b940d05a036201503944524541000361f411032501280300000c1704c0301e0340d4030010181c0003500d03c0e986030745c10801455010881950040010b0b4880ba19000c00c1d0b490300c0e084442d00d404000c0030f050488000c00c040765401d405440300300390800b07020044003c85180940080c485c030b01c21013000d1051061a05208200850203508842200039200b90200090b512036600c684c3c02003140b0700c2403031100c001c1e1510402920600241d81 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 787095359 1250 787094109 787094117
    0x120f0604080c0f0f160506130e0414060c040306110a0f05160206070b070807111f09200901120302060118021c0501180c0e0405040201093b0903030c0a12050106 70
    0x30303050b89140c0300c20300c81701d420413409a041000b821000b14004002c0390200d83d0030b003201100310789491406040c1e22880d5034903e003182c450742090080c00f020900080003120f114290411410004d0391003081e0303500480c80c020303010074051180d64140f00d004000034078015000044080c0d41d200186d00054141d0409142a6a940b200804000c0800e40007000c11742c0214403403d11001d80d0080300100c5907201903912502c24400fa0310030f019000000103403c50950103510107001401d900c074962500381c0301210192450f1142001100004881200c8004d511000b9010790140003280c0c01e00e0f800c122011401c201090840342d003000364148101407800c110580c40030040c0b021565514000c4031080d050b5600818141c0c0074a8031034aa01c6094012018201480f426940402e156881c1e0006a07a01e40b20380e488050780500600c9900c010048030203907417404a603104d80c2030719000d907003040030101c00c5801c0310b8115556104102081d60704604501810400480d45401c0340d107800b2944520f01503c5003a48441c02203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 787096609 1250 787095359 787095373
    0x501030b0105240c07032001230405371401031b0f230a110f1905070b0f0325050a050c0a0b15120f0604080c0f0f 50
    0x220900c80e04900400040751125408504500c03402c4211002041c8030b44606000140c401c1c0d0403c0a0194000841c0c01104000741d51100b0540380c440041103491060010f004050b04440490089140c0150300c00601880790802e8200418043d900750724480d64840e480b402c2c07143c1d01401070501000620f60002d5600204810300c0c2150450480c1c15080049061500b4002e441c03110b48514a4019042c16983c50070000e600201c10099444070720780380901110504141e4401442c862802c000c0404000542d01e403c40118a040341644078081031814a9103a080030030718102841c140c00246000a00503010741c0d64550759250350451991110040f60800d00e000b10802c00c00d85108030b441c100070700d10a010780c150700006e03c4004160341b150745045418084042040e2280340d0040002841c42a801114609103040c089010800310120040040c401d0803000d200c05065100402e452018881e40401003030551256560300b0b81304e40102043c1d030454403841d4500c40c480700c4104841d42c0c1c51510311010b0594 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 787097859 1250 787096609 787096613
    0x30d0905060106020a260706060801060503100e1002092b0b061f140d0501090b1c03050708070812042a08060109020c010b03060c22030809102001050103 67
    0x30100141d10200641d00417030140c0010580384100c6543c01e13254410308000c8046030600062250250410241c4485d03d03100d408224560705510036002c1e01e104400f2208650750305010031080c1d900c41c9084902540000c0c29501e55214590060025103070001d05982c0540d420391200304244511040245150f680f609100c001d00680000d210303002402038561907440c40088491420515100360b001040107050242e00585030026010b440c0560408a802c1c807165a44902d01e00151084d44c004a108a10f814840f080d40500340c102004d079035a05858090030404035807a4041c8541120f2015603400b40300704119214005032056503841140b107054141000039115160100491001000c14007115152005010b082d000103001e40c1110385203480566900a0002d1440c0984170010035503405210b0882408041d44414016140c01e1440030810000c0c7c0aa005a007016507845110241c440e1500b0481d00f11396080100e00d1000f50f40309800d0543d81215032007810b0806401b05945c20f14035075954801403017 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 787099109 1250 787097859 787097863
    0x3090b04050105060a06080f130201020f0f011b0c02130c120509030717042106020403051f0b09070c0308150a181401030305190e041130060d0302030408030d0905 71
    0x5c050180c078601000c0302d140c080703012004c0348030191008040440441360303003085a01c01c0205000a081d52415212620510f000740c5003e0b1105d4502c0303140c0040111810080c051288494010207a001810070441e00c4160030701d04000e0030814800c40400264565050f141113117030081d84e0080c407034800295540e00403070500c000450a08010b100d2005406c120402024165155050f2082c9424920480071002880e00704020300c40c0c2c4c0e000800314010951014031640c80d284809203c004200f1040c4038200d441070400c50768101c11505c03000480c0c1101007000101e84142030b1140e10110407410481c0e641038040004486a000e640324080d04418100420440c110500403160344540000d4401c806d9411030741c02401c140142180d55580c0c400b621071400c2c10520400b40707092074840240040010407031000314944158002d49402e0300c0c82d00d55228280352203891000707144424660404214a0351110f40822035001d5040e0021741c2144000c0c013000c03803043c8060000300740c031900900300042c15008500d0228 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 787100359 1250 787099109 787099129
    0x30c071203021510090c120c0c030924080402010e1f0e0913080903070f060801170c0a1e2318070c08031e04060e070506040803040e0703090b0405010506 67
    0x111401143e824441c02c00d00d42c10303002041d540c07420008240d0b00807624045814540a240f10000503051005110003990840c040014450103507a1b480d20564031030a4140c3c6050f000802c504d041e1001030400c1414521400b0f01c1600305e0f20525040801a4030350303000448c03041840c11003410340d680305100c101c03c0c20b0b004210440c20440a480c080c4061502901c0e9110210506201508140340058840c0b50b40c0c9e0280141c3c03020300800101d1403405034840c0f0000b0401102405103d4154200120404c40b500c00002d0580f04904010600b2000c81d040c0707107880c460a980003075034911100d41400d01045448a240860065030b00d070305c0e010140c8114200c204640302030700e040503128544014062088041e40b01c410200c0c03040d002034150382d40e03495012002800c1c1082c602c0d1088000664010302c801c0000c1c03500140c1c40e001e02c010885054035200d00c1081840e02c02e41c4941d040035841040104013030300805441e1540300d400c0b41400644175001c0d80320548001c3382103030704840e20f954a034200001c5203805002c02c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 787101609 1250 787100359 787100383
    0x30320120f13052104120b0106030f0e190c09061205010b2b02030c0904030e010e100f03050a110a0c0c081207020f12030a02030a0801050303071a0702030c07120302 72
    0x1124103001d41e44856813a41e00c400b1100d000c0f9021900400108004002242d00410007201e104005805500741b00380e41400c2070040000003030030100303401e000c2000c5008150015210307070094151f100000032580c40400d0800340c00c0b2444001d150002900388564421b1000600c6112306000341d020b40d51503c182101c2c0c4207940c40e0700c50f6003000c03600182000181030240900c90010300008140480780000703072401d284201c1803039101d95a00d04110806900c02c2c0c0c0565405401e0f00d85034644041941080340700540c103600c080010303200c1c4981c04441d5209421860300508140c0000446140c1381e0404411584074501000100d501d0862103c00c000d442d4031028001c15249002d40b11a4a80c07060420082c07084605c06441203065200256603650b50020000300f86c07242d44105e955445d19003030065101d400c0500e01501003110040005043d00307010044802c8103501180301003200d84003030a221004880038044100b14441032043d66034280c0704010f1340d00a00111807a40c0d11900d6603160081c544040529a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 787102859 1250 787101609 787101631
    0x216090525020f0f010e2b0c050319090501080a06030b0c0a0c14060f0106030209030a1221061805061003050403020f06010e10080d020c060a0216031101110a03020a030320120f 77
    0x801f01d40031700c4126466002c600c92504458040c11070070300c1895402002070050040c8070803d0303800e25041e00046850102c80c020303202c0e107410307503107600c80c034400c84034144005421245aa4005525101140014541a00e090a09401e090f08030b44510150400c1c4507010402c1ea848407083c40200680543c0f480c0c0181410b00d4154604034603400465198500501c00130900518901c100000c580a1041c030160b0144400c044448101043c41042c09415184261400304e000b00c407004406030402d00581e841594050040301035860014001c40c02040010002c0e0304500803502d507000b600105100d00341c02402050252983c42c1400011140007007850762180002d6403291000785e02d4075030040341100c80440100d98003030b140e160004050b4180340d0100d60b0b0000d20090443c0110800403035503a1304800407000e98a8a0030803080b4407025950310100e41000d40075030301803000040004c0c4690000346440412510400f880c4607803900d0040306400800f035041c003403c1100c0030051400740b505041540088113103c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 787104109 1250 787102859 787102903
    0x70b030a0b030715050a2007140a0b040509090307051905010638090a03150b09011d13061404030212130e10080d0216090525020f0f010e 60
    0x5908030444c01140c04030028081c01003400007136603018010100c108130068400000d0f414440d00510b48030b5045024480c905a000e034020815070500e04000815204403a1001c0d01e02801d0008200722654014202229888208004800540207000c60740c013421003003052140034606880c0c070307a0a652440e08070624028002c04500e03a80010707054020360b500c0740111822a881c044107042a42840713691403454100030b4900d000001c1012000c0e00d902d850b882040108a00c40c440d40411800a00a01c2560390041c0d460921030002c03050300038010342114042e1802450206103907280343c16500c501c100c0c0345505810404020078103805100751043c0d1401011814070740360700840c005400e4510b41c06040c0c110b0200200181802c081603004802410000d000c0341c4035034030504002959402c0441d110030b89070b082c2e0740c000034040426010b65800f400700c80c130640550400708403810100d2003005100c80700b14411118043c1b1405821302c51002952001e800200d00c100c5c100314001e03d0560034207503034412204603039 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 787105359 1250 787104109 787104119
    0xb030109120c02030f010509030a0809030a0905150702040504060b1c020319050c09040609030906021f0e0a022e020c0d1e0b01090606081f150908070b030a0b0307 71
    0x20090500301c0c8654242558482d05a0000c40c3c40d048040d11005015840c0c4402d0103504a4004050f000403503960b59002c4080c2d555220141d164000c5260f0725000c100c420344213014a00d00455185a08580d4000803030410308550001025900c081d01d0030345000b56074015441c10390509500082148188450b024544121580800c0e40c450080c0b064035a2031641100721001c10400b84654001c00303100914203c0c1504050130940014641d8000440118004450014416001150411900c000c44c04580c03010504210b01c035000c0d000a001c0d0a03014001c900b00c200c01070750f80b0b46014400c004846175507480701001d08840711070020100492000c0d075102507003081c3c0a5550070941a1034a61003494203030721821002190010f08005000100344d08035860010810000c254818806c4440071b0341c0307401003510340c0e4912070020541d43d10584ac07612030856092214021504902c04103198505d0282c8446c0c6e6610003a905080c500d13086840e89000003c05d108420029001d0f410b0009400c03400303002d442d8a80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 787106609 1250 787105359 787105373
    0x30705210601080105040509100204170c09070c063306260103080702010903210201050f04201306060201050114220c0311210f15040207052407030b030109 68
    0x52084a22503501c1f1030004d01000700505c002d110005ca4050300359101c503165802c00100400700304150b09144038000c0c1407600ca1400a070a41e028446540712883c0840d803949409000c0c00500c23280120801c407104150820301180320a041203182003c12079141d03079003844001000d0b5003040e110001202c0403c00c042122081c50640a4112035000b4030740b43d40c943e0ba910040e0342e019200d600240a803040c10b11280d06a49842c080b10f40307118003560080020781d8807503400041040050f1000f502d0304001c1107985100100514884484880003070a044a94405d41400d10641d0800d07044000140d441d04010441005506032071900c01100300d562801e0b180ba000071811031016022900b01003903072150b000c140741031b01036804400e03044000d0000a84d151014802c0c250b03054800410740318100c55903000104000e05c3caa40c10750060400c4030f544038204007411704020107500318050039603042c00703458403801c1080603070841140900c00c2d01d0800f48440c81c3c1180040e04441138900c1c0366000380d0400d201d240000e600 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 787107859 1250 787106609 787106611
    0x11b0f080916140a051504150801123201060603051605090d081309020705150c0901030b01020f010c0f021e0d050322030306090c09030f14100203070521060108 70
    0x3864203c000c054481c0043c2e00080c00b07034000c41d0448210034a4a44058480008200b074036222100707140c000340d16690441c0d003028244200240d03071140f0404040001c01c00c07100c030402d2012107400008000c0340c111400f190311504601c0541c2c90f070365a00041003015098000d5689c0100e80c80c61240c9120a84c94002d0300602c1406175692182c4c5c010004da2003040040419283c01062041c0c1000c1159102c444000013580a034106a0b840c2c071400c500781c100d9480103001541302e40701641e0020b042220940064014290103801130381503009114207110050424413a00000d68002d51f140402555824406402c2c036804807508038040d49600c07540300c1154000280301c10900bc0500e0016660780d2480015500b403d0809100b20041107280051802c0c1075040c0c0040d41514200a02084980c43c4050305a46c6a00244401081440407503c0240800e104405030011202003209441001d910750084004070382c021245400840d0000c941600c01e81007101e03046100035110700b0302802504161001070000c0340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 787109109 1250 787107859 787107869
    0x8061201140a0e0304121209080102030415020c030d1b11070e150424050906010c05060f0406110412030909020c030d090c050303120a0f110f0309011b0f080916 70
    0x303140d800a0442543c200304450003000707180c0c0d2500e15808030f40f0300003041d6040002d1000000d441841c0110b4809c0041c801c41303002d1540020722105c10030112140a001e504a0308250030240020302108070b015840b8081c2d4915030b00c1380080c1702d2240781c8000015014400c07800200000d0790000500f4080c0742812400c031758204481c50464807101191170b00140140203040004903560b02301c9151140d051017181c03248010f407442110741541650390a0011184051b4402025006034407487c04030b41018207046c0060382003401000c000c11222040da1a944d41e0b1307449944a220034858003025917060540c4030140f20040c2035000403c2d0320b070a10400400f9941d01411a01005240d500c60b03a1400300585100084020078000e02580c1d202c50441004905480c01114075034071b000d081ca0012920304596200f407551a01c04642c120382442400e1903542c015400061050035a03658941002129242c4074000010404a55440020113030040030000e06001d8054803400c040d51001464150380445840c1c0081034034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 787110359 1250 787109109 787109111
    0x7060c03120b0a0f0909050c040e0a030c050a0215071502090906040c120e010f18050307120c02031506100201050405070b090d060509071a0405090c2808061201140a 72
    0x4040d0b1400100d88500c40c0c1d0220250304900040000c2042654100c481143c1c065010755103040c00e200140f20503525030b41c000ba60660088002c0000103800f0748288070000d401201290128071150303001c20400c0c1032142804007900000b0454004101c1d00c1c1c50243c0401025140560424201901052803039002078041446a030310390b694000c94910500c03c0030801c1c0000c59040c0306040c400c42900e8000c04500e08a0407169040c8803481885403003007100814010391020055140a000d42c44a12100045503449020031609400000159608004615681d0b907492400c80c5c45003864001c01041c561100744480569040c01c0800c404075030042200c80460324030006960741c428a03040014003144a18000410303d0303180070144810b203440021800c1c151a040c140f092a6162040660600c034022031040759804400074000800c0d82100501401d400b82d214900070090b0409060000030380e640c03102c080320015080c60100412881e00c8a898640c094800c802045041d00d184400c03201520020090741c045 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 787111609 1250 787110359 787110371
    0x203190f150f050f150a08150c0408030a09060e01260c07020603040f03111605010e0111031c0f060e0f0403200c13020301050f1909090b010807060c0312 67
    0x10000d01c1d04014142c02000340108001d02d0002c8001c0301410f001e5412407124007900340118214106100e040007a205d40320f00170044118581c0400d0b14804001304445802d40061100140c03100d000c0000d0b2500d8946502d880001a080c0305000381064a5151401d042100100303485074505102030000aa0203460074a41045950700f140718103144c840d5040c02900414004100014003050032203c080315842561051801c4442d60805551980051403811009031224410012907020310313100401c0f400306040220000506c2681076045421084400126202c1c19890022504062040c10101440c03140d04011140c140300075081c1c212401800707400030f842c0d90800f250030b05004410122681d00110003120303640103943c08080e119900b41c013000b03025820b0003ca1142200c000e0094074140c80380501114015610072007000025100d010111100c01c0e140c0e240890710b840f0b1800780c1c4100c540280030300c00d0554548481680741c5441544200c0820050f4850070740082d0344040d40c10b0380c0850606000c517403 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 787112859 1250 787111609 787111643
    0x40905030906180307060201051e1f091d030c030a050d0605100903030f0903020d030e010309050316030924120219110607030c0f26090a0203190f 64
    0x65403084010407a03000402007000001d52941c0c002400b01d030b000503803c2d1030340c16a0b01d1b44240d081e501e0580e8a4001180303021130003041d10113039140d121303409558204011030a02141c44010a01551a00801d400740c0c1c89010450280120300840030640da003601c0110314005044403200d86a0042002c11410000e00040c0380444610540140025101c0100002c00080b43c107070003d00034400c640320880101321030842e0030303164500400c1154205c0c3d801030f03c09007070703040a0340d421a90f000d1114422414141d480c0481030104000300042d1070990348404a034040c0b9001d03418080d0112031554071403c681c42c8944806490280b5141c014070320341106042030f40325000c8031140d900c040c1c01880c01c0010303060500740c00b421481d43d220303c008170300039013000c282d0399144c80d105000c0701686c10f2220040301042050003140b000034815100450561000040c007804400d09041224200405888000e03d0380e20041c2e00c070b000c2d403500380109103c9003181e02e9000035488140e510320f40641c0c0c03500b034054907007404a807200403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 787114109 1250 787112859 787112863
    0xe0c0a03080d0b1f020f070f150f110604060b010210090510021327060e07020607050d0e010504120201150f150e131a010c030c020907090503030304050a11060a0e040905 74
    0x104c1c0d0902c0c41d0301c0314402d080c0304800a640d11000880007015204d148800143c99030358030005415078445101d0940d448180440c151a00e012121203c0204a800c801c5121000c43c2440383c81e004a2240354003003400e03003011000a10700078030304144002d09850002181e00007400019801d41c07085a40c0f03000341e15a46081011211003403107612400d46080320010424080c0141a00342d114055070007010400251034268003100590100d80003009a4040c00215050b14080e4000d0080050f0090000c00ca5801c00c00281e800d6030400e5a04a0307140c4801c000500d1000d8081c050030f003410f100901200100c0d07203090002c1100d1b040e24440d060740d5401d1094008500c5114120a220311f00024000c04c0f41e10380d16968420003080c501c0808282044120000200d070740c4603191041c01c0320b030580d9503500c20301a40e400700038001c0005000340c1c042c00f05c00c0000081a440610145109030300460151145480c14101421518803015039544200001c01522110390b4020380252640c0d00e082c0c0e00020034600303034608130b4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 787115359 1250 787114109 787114129
    0x521060a1806200c0f010c050c0a022b030507050c010206070c030c05012a02070605160201260115020114060a090507140c07080c03010522030c12030e0c0a03080d0b 72
    0xc080c0f030303400905015a96000200b11010380e401600800030340341d45480440c0e0502410b59110010b40000f000303c00075250525203081a07082004102e600358072180d074260b690341a0144200c001c200086020030a1250a110000140710203002810941c540300f00014001d400444004052105a500710403c2c40b0b400d622000150910490100403182e200070310740c070101c20001c0342d0b0005120320400071800521030700c10344403102e40458a04110340f11a0780191a43c102d4003051004086199401c00c07140b1030088ac0c03150007414580c280e03521409031900003d003503500400b55500320409050a01c100d41e1545c823402e408549104100140940743c4e084200c80f02d81c00000005940039021030351382c1036090041340080442c0e00b52805c903441305006000781401d0780c038126098a035060f10143c001c0d00d282c02c001c0d40c10300664803c0c030380786a003141140e4400280200d00c3c004503000075614500045c0e404800c000c04c0040d18004c4807010308491031952401e09074861600400006511920f0495054803056480 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 787116609 1250 787115359 787115411
    0x4060f0b27030601030b04122111070803040f02120615090606091e0a230402070201052b0c2d030902330309070b090a0521060a1806 58
    0xe0f48855075242070550000300d003520161505d0307030510100c1c4119400703208a6120000150080a0301a0265081000a10f4088240039162004002600001e0b030058000d601c201c1c071510071703d20200054014000a00c94610306031441c0c0c1d11142c14000c0c00c81903041041c41180080b035809141c0d5685802146c0346010300f410007038000c0354019000a89a501e04010030074001c058408070b04250361444088016403815050351000a10f129080e005402c05400034030244d401818076030310707090f04442c40e244104070960b100c6900700084011021035003158082c01c3e107103142a240c45120769a00101900410b84040201780c0c4940e4895440ca0000d8020b0308803205841d002441c041018411501d41c251640c82c07119100c40e10107900e92030060300e0845005603030241d0307441c1d40145040b50400c0f5a51176180c0c0601113099005c0081900082c8030ba4404441c081d20081e00b015a0480209041c0440d00c0c00c90044c0c50b0b164990b0a04101180c802840f001c0d681d142c5e074000ca03010a2205880700180c038210820118 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 787117859 1250 787116609 787116613
    0xc081e06191203201506060702280f1203120b0301150e061003140703020a0318050c18060612060a0801020f030f011e1403010f0f090204060f0b2703 65
    0x914014190800d0500910400c0d40e115100130710f100b01c141c26100c2082d00c01500d01280c9013004540c0d0340c20204090300303040d8405400c1d110b038507a0320041d0000000c2c0070108200c0f03030a4640b02c184070302c80c20000a1002410003100c90031007c4140d41d030242c559170368079491501255680b05000d00c90741c2d09410100c07140d003406020341c3c0e045844240d00a070240c0d0445401e4012204502440c1c05070f8464031880c00407000d82500b1060907111040300314041d5000500e21020582c80d44600c0103e41c83c3c0000030030742d49100310014907603052000180300c00044407084030360b80003c54404000444c0c03901021030350304500c43d10b4031b0030032552010001b941c048616089041d03150710115814156160040045000e00c801e910b40f09012380ea60303c481c40c586010421602c0e0030b40400300c41001244540149114180d10050001c41d0000712000e110307044440305141d4032200e58842c040300055042c03510465028091000802c0b00c1903052600c6c9000710300c1200100984036003040d40002e01c0200340fa0100c041050000e007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 787119109 1250 787117859 787117889
    0x10b090108011a03060c12130b070f170603100b12010203010b0309100203040203122a010203150d0f030f021908090f040903081b040302130c081e0619 66
    0xc03846008204041012400c80f0a9052000c00b0b03150000352a841801c0c0c040410346020501628400640700140003401081d00401c030b000000303900c103120107110300c0065407440c3d54070000220081110840d92103030089002c40c0c0c001e1012a85012400c801c034411503560100c3c2414580020500c004443c0d040070700154404000450900302540045020303030601b10890b00145003281c40700342207203c199030082d45a440800400c001c1712080002d13110303410314088101c01c3c0011141006030851040e00c00d548031a540002080b070074800900c9050b5031444140d07840d0785d5005d590ba40758032008201c0d00c4090140324090115500b844d108115040c83c0e120010000d6400245601d41a4420341040d42184c0c490b0f01e003417103100b400e41403506c02d023645541c040c1e88200158881c1102140d04845030101e0003c12a4100000b00260700d4a250141c054002260f0016000841d200e00030316106003e03100031170326007514840d45450a05103080c207802140071905c8040c0c40314040740d1a03500d92102d070321040203100c03040 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 787120359 1250 787119109 787119119
    0x10e09070e01120c0503160905040819030905160303051e042402010b061206220213050901050a0b1b032b1a03150405010b04020705061f0f090e010b0901 67
    0x1070309288981d840744c2005402d80d0340341d408042d1140707151202e85600d905a1001000030a1564102c1600640601020f5141007203c030405c0394800c405121840c0440c0d101e103d041c4c1049030030440142501c0c400c00b00d48110a00f1698010100d1240303030b8903490021f101100c103119404130001200d00a01140c011603540d000441c02c03030394400c0f907010620340c090351800910070317170320300307189044440c0364840b400300704455541c4101b042006d0f81101c0c6504285100c14800102c0c0d110345200402c0001c1e65003584565003840c0c00c081002880058104500400503060108413418100701a42d48200302c00750141292a60210074500c0c60146815802c00b902003e0b030111003072400012a503d1480894806200984c092000140d480851003810754140c2d202c00126104e00140c11480c6410501c61070020912081100009060303070007c45064800e0342084003442510501100344911780c000300c1000c014490b190820705201000107200780c0c032107580c413114005c814034800c0d8410501c02c00e0041807401035585403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 787121609 1250 787120359 787120379
    0x1b030f0612030f020f032a0708061806060402040506030708040f0b04080a030e011506110304090627051005010c0515010603020d060f050a0501270902120703020a0206010e09070e01 79
    0x1141c032600141c043c4420051004178048121b62441040c1101c8204000b50070380c011a03a100705640c2c14003a400361801c0441d404009216150245440310324202502003500d023201d050420281010f0721884c03041008000390303100c150640e9800855070411603000c0e600e60510041c11684480001c20003043c0d1002c0104002d26003007c0c0030201c4040e0b80420000c1140603041d401c855482c255140c00d41031900d800c01085124008803003034108032100740c17400e19680b6154441600c0d82600a04d40000120910303a10344081300d1440381c84c204200c00280303c282021481809035000e40e015590410400c0c60b2160180b0204020042e04400800d42d504000d40e5a150010000d40041c079a0000b840d0500d5400205180c8000408080c1c4030000c110b52851481d00340103540c2041e0455103c03280f843c914800320198040c464058009003e440070259a40d05480d1101603007440041c84030090600c144403020507250f0008409040d47d8092101c111030ba20759440c0d0b10315103019648132a00d000300102c004299482c0c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 787122859 1250 787121609 787121627
    0xf0105040b0310180b0f13060e0f06100302010324030b04020a0b07060e0d050a02120a0e15070303050601050c1c1e020132070c110405010e070806041b030f061203 71
    0x14201000051b215082014100c5109441004403c1200d0074190049080c9500050102030311004a54001100242050402e03408480544c001d404104041041d543c04d8002c0c540302c1d6901341034403520707050541c064a81d0100f95002c05400e00741c0040001d8119140d0f0f96414000c0e060003121943c540c1001d145c4000036003d40181d4102c50f0048440c0c003a01c09000b9000d0703481c0c2c0e00581e009401890044921744c8819040903100808005c629035486d106510388181c66454100c003d0001541e605140c10041c0513901c0241c1103074100301003001910100100402d01000350003000900401035208010120b0b00c0c0071080c1c0c281d01815811002c10000a90154050282e22100304031804100b0400000a03c2c0803e21801d40c8a1001603e00006d41162040c08091005441307442e001f4040c0900c2d07404642265002d03000380048026120a2180c00d80d001001603a1103442100c081c003109038440e04a011801966100c0000c1c1511248200311600d034a41214020341203c030006a01c41c0c0c0d03241001000307801 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 787124109 1250 787122859 787122863
    0x20706050a020c301e0c0d0905030604110609240c011a03072d060e1309080a0f050903010908030708070206160e1207091a090f0105040b031018 63
    0x842c000c00d0900c13082d86186040030415804259035070f40d4148926031222540700f0480a03108078001036806031450b0361a00908a1200c2d038400410050303242d00703400340007030100e50001031190340203400b080000380800c82104081c640545805440385140c1002c5181d40e10000c0506d4841d58801c8500034850980d1805000c000c1e240d10024420176820a0190006002c000d04c12501900954414011900081c0300da824400d1150414038603540381d4001290302c2d4220350040030010b02900780c2408545003040c41c5c5e21011454401c10401c100b00b56642d50068030a00d9596804d1105400168002c00d001e10143e804800c0041d00900c0581050700e84648141d1045946402281150000c0364140d44000381161140038050111800a4020841600c1c044400b20f241c0c4e5200c0308800354003c1e442014400c0f4001403005000c003154402f003000b030401441036416000e90261005904000c4468544160141101d0054900286001d400ad0200b0308082161150701d0101d404d14054824a4410440d014a024 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 787125359 1250 787124109 787124113
    0x118080a0210060e15030f0a08070c060527061e041a0708040e0c091306030b09010213050f030a0503040806190504030f0809190506010509010e06060d020d020706050a020c 75
    0x4500c82c0040b0841e090b5004009101d802c502c0001e500c0c915400076021445c1004003200e0640d60700210803441c0150f80750040f92041004107414040186c402551130151040381031030360500c5442000341000847c8655481d030803010364141d06245c0d4981004440045038a840040313049180e0408225440d4824401c0c10324622030680341d458407031201c01c19070f0909544852040d14244c900441c001d803806001e008010344000030440000d00b9500d0349400307074410421a0002c1605842d500f000340c2a040020081525640100070704c80c0144d00c0d0170b0015041c1c13a0304440988400c400346011900d044981d190091807440009804103403101c001a083c0c0c03050030030100c0c41c0c1014180c81c062078140c91090fa0000c02154545101d00c0c2158010540160b11107000c800310b8992031016154144c068401400544060f00032000601c11400d100031440e0142680303501c0004182099004a641889410981e8003202c0c0c0c0455207079109140c03901280c004a1b0028800d02c16401c003205500001d5000e404a20014 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 787126609 1250 787125359 787125373
    0x3040b1c0207031e0e060706050603010606180512030c060c0c060603010c05030a05070c02031009141912030e030301090506040c022e0605040204060305041b050a0b0a020118080a02 79
    0x24003810300858030050382c150356148031180c20070700c0603900c0703031402a9960a020405c42d2155071615440c0240c00807900410300400c06041c04403d060840c0c005400001c1000a000001080300181d10340c440111201901d040618052414485080d4040da80341e83c41c00b4003400e002e020402e061070000e40a000140010340f5541e894000070182201d002200000103d2404d0000900080240d800140c0c844203e0408680720021a0300207400c0212242c14845030503520340c83c98051060542581d1524440039004007000024003001c1c0015103598400240781854403807044012622a82000e00312203140300440e922961505112000b03004203c403018012440c2440f044882440001d8002c0c0e140ca04001d0040318a880400600c1025501b07220843c80a131038100025080c1c4403403006000510069400048038240391030080603003480c0710a21900304808000c00d00469541c60805400c40e609446401d544080d194000e078050710f400c02c0b2540054807050021401d002810008084011442d0b0a03174500b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 787127859 1250 787126609 787126657
    0xc18040f020309071707150e0406030602030a0f090512030702120c1c021519090213150f0605030a150305060f010302010210180f02030c0d2a0305030a0f090803040b 72
    0x22080d501000c00c43c190300c51b000800140480d003a1140380030f10306103049206008001c01080990707441e98000c0720840d40c00410407095003940e102c0d4501821a0030003c1c001344440f038485603130313412152083c61641360001000c0361059000b04070341410242d01281c21a1665500000d29458800742e82c107c81f282c919840d030184890340b021032014108060785004c0041a01c81001101800c4200359100144969602868001d0fa0702c0c0d0044c030010320144000440c0039030140300c805240c0b000c10384c030001180c11100014000c030f54006061769444407e001d40052080f01c40800c042d40c15546600c0641035002e4131007441a400800040541a28001c0c0c0869a060fa000340c550803c40d180300c0313107641c44108098400400602e11500f040c0045000500b2110108080c400007041145c3c144000c644610741c1012a030011010f01140c43e100070300d1890022202ca10f1521655101c2c4903003400d540410070209100810180551206009412104d0880342c85580343c5140340f580b82d10503c0148900c031508982044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 787129109 1250 787127859 787127879
    0x42304050c070308041101021006032307030807030e0a05130b0436051507020319080103170d0908030a0b03060117150703141501080901050402090c18040f02030907 72
    0x45030360f0542d20300003a5651925900c1e1820400d08241c0d04502a214030404564810301a10015500984108065008107400ea040070000903030490050f4100c1041000400c2c03c01c0292038402e50981001310b070300c050740b90004064a4090b00660f0380064072200300000b044556004039000c21040c0c1302001128000c4131b82010300340d10203401100a00d882151004c01407600503812004c24801c60883c0d4001440c000b003550340402c219401001a070000c03d240788820041c020482d00c4d44120b090020a0703506607103690601002c001e804988078180010003040001c2c1c10b13400b4203840c54214079542e45a0800c448840301412219105500c6841044008600800080390b0b01034030382041c0c0d00602d60601ca003c2c500301c014034000e02e81c2c1c040c96514842400074541d08004684100800c1035801c07640c407a09070000d0304080000c2e20030140d5a14003010080140c9942c5c40160700078403071880d50f9407500c18801c070300407681c000c0880317080c0c00c1414040340464084640d00558000d1f005141514145038071040002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 787130359 1250 787129109 787129117
    0xa0b0409020a0603020901020f01060603050405060a060e160509030f0c0f030304051c021206090703020a0608240f06040f050a060f050a050d0902030a12093201020102042304050c 78
    0x1c0c0d8070441500040168038001c1c2d005008580040c01a01c9005000c06d240b40c0c01c50308294444030100340c6840400003003044c1400803940c06540300c6010407035103003400031903012254020000c4102c0b103400321076000500d000390250f034400180141216500e07001a0b141c05e4842c0181c4103120300414014502d403021345030100640d000e480303003c0c00313001b080300d0180545480011080d00a90300051484440111000c00741300d00e51150907980e008000d41c81c0f07503206200ba80c0c501c40d400501040014401c1c803045070941a00314414251031600f00190072055800900740b11906401154000700003d0000340d0b4280c550f0702d4008039402200e00c0e0003e186e6a1a00359005003410007441c000600030030084100e80d01a00243c9118226424005262041036001c00e150130030303202c015a04c50400c01c441031344403903110941d00007a00720003001c80d48004d24212481000003401c01e0014104400c1101e40200b03910035415100142203004a0f8070400c1c0d042446030700128442d000c607602450620380051440401c410880e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 787131609 1250 787130359 787130363
    0x230907080a06020f0c0303090a052a0f060408101b0c0b0f1504060902070c0609050a05061b06040c0306060e0403091e0e07200c090f0c0c0a0b0a0b0409 66
    0x141c1892078841c2c2c0e4180c0258410318000000c0e100c00c0c05000d403084000c2024600c41c01c149002000940f1041c240185840341d15114100541c000c0c2c0344003007042c11440c0000c40f2842d07068a60100c0c0440001c0014034501980d00801041c0c8191524140c40c00ba13290401800c460710001130140c10029210110344000a0040141110500c034001c1000310784010041940440d25014103040d00e0802d000140035203689600c000303259900403a040040c880340c1c40040d030003801e00341086010780e454040410441c252030f2103503500c18140403030b08115040c1ba0314095a151101c800c00e40300749142030310300031041030120702090fa0031500e04607000c94050110105180540d4150700c0d0a5142c62500d55908138140c15403401c650520300c02c0c070f40010001c41c07000302d05000e407180780c4455180d6141c041c0902e480c3c400c0e20000a14a5000d0501c41c2e6213234455100c4607405c1403242034100c0055882c6090328401d48201d201101c601c0c03250340c072001e083c45012040a4010405a5010b01800c040340342004242c2e03040c8100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 787132859 1250 787131609 787131613
    0x90b0c1305091509040c050405060a050102061311030f250e0a0218030d030219170c0a090305060106031a040e100e0a0807080a0905010518091923090708 67
    0x100307104914142d2100d5902120400301007090400c3c0401040c0191000d0f1030459400801840503c02443e15002d51540b00e241501c44002462916000070764940014007a070036845800c500000034407903030100ca56400c410150483d081403100c1280203554060b401c40200841c0041c000008100c1c0044004100302e80903000007076520303143d19504200a50102c0b030071394141d540e20348002203103450601c4140600222030718016102c01301d48446800d00c003840c41d00901040118601c82429800c000d0100380c10014001c0d00c00e40b03030b0341c29050030780b140116a0409002d601c211800000e080307500d0707041862100c458100d190081c0c003104d020b10040d11441e272100c29094000c0c0c03000c0415410964402c160041c444001c17108481403030388074a400c41d401240141caa009002613210131540d00b181103900242030078030307000d0719100c4650400003a4200000f000341c4204010310110300710891001c0c0c44841c00300018403c002003948111880c5584400c00d01c070f80b9040c00040c5c0000d0704104041a107004541c64040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 787134109 1250 787132859 787132897
    0x601090e0f060a080f06010603060b0405060d022d0a031802030a17041a040e070c081608070b15150a09061b1a340c02040f020a03090b0c 60
    0x103003180740400500e441d030450104400002c180e642002030b03100b40003c003000340000c0d50400750000c084e0358007078119907540c82d810081002503031110002c440c0c2030000703a44016151811140030030613520500340c1c02001e010a00c02a0070045125030001e11400c40b403030301c0820544c1d10051885000a401e50406507044d008501581c01294081e031245c00050400c2d078400d464651121700001d2041203004600e5404007000c5810301900011820b02c5401186038100b049800c1ea050391040d04074412102d406910300d550344658000c000d1448180d40d18264010034009039840e00003d81d8200409183c00248294081c0c003012081307040100450390346400c1c42d41d60034007241c00c020081e035287d0b1880e400781185034900445003020030000552400c0e010383c624503420740750906203c0400034446661801000d00c0c4400c01d1040b2401c0c04440c803104004441c206182015403500008005080c0f4035440b00c1c440380000b5800070f905a0540c0303c1c22640e40b04440f0310130315843d60401108580103408031000d034140945 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 787135359 1250 787134109 787134121
    0x10603181110020f1e0f070807030212120403150b040b060d020a02240f07050a0512130c03050610080f1902060f04060306050a080312070f0e06130801050601090e 71
    0xc2c8070307405404424011594060308003483c162070040801d600e080215100400019000d01c20711020021805c005c0090000509007181e880d151040c0d131000030320a00f441c1001d51034030300c0d00344400e5000d45110311140351600e0741c80c2401904030090002101310b240c908000c52890780340c24820072860b03282c050802800d02100400c440002d501c440209002d5100d60800451081d0102d0300c0c41801c2d0501191141240c1455280340102d281c001d00306078103010b02806410700d880e9001702070712804e51140d10102c1c0140c5a120690100940e80c5401400c0030b040c0d040301000f030210000710385001c1c2040020205034540d481400b1038490b4006501ca042640284100912850202034a0408280028034003413604031a007840001e030741c3c42a800305000c41c0d240c480c00c0105240c0540c0700c0c3c0040400d40055454500e0080030211405c2c00101208180300600c025500b103075104000704e040303084000d0b0100d80c0d1141c00e4050400500424480c078000b03903003414001030207544614510b80c11100d18061030001601c0d0381e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 787136609 1250 787135359 787135369
    0x1109070f0e04020d0516030606082509080f0a050f1f0b030f1e0724080a060b0a11011d0714011803061b080115031a090405060106031811 60
    0x35401040d4803d4090241383c5041e011071140c0c81c0540c040513140c09600c1d80c050005402d40f5900e520200510000780200000e165802003007061105444440d00d12250303105c4000d8440d002541c2001201e4803600707450051180300098014080760080d0200e40fa0869031a280310354401045107a9000030451040e06800c281d03007500704541c280d800030140d81d121900c1101d0380e07280c412040e03007140c81c0703d13401408401004010321545018208040000c1e0580c2c914a0b940c2011007a07030b4281c5000c000710040010700400ca079a003c88041c0c00355141c3e5942d01c141419000300015098505100325500e0440e0b280ca001800c200302030880100c031360151002a1511110702d10f181003c1e4425814041401e100e9114120640e45c84809140305142c00160407001d486002110203050060009000c1164018802841d0701c030708807a41049a841c0214038958901c0e90311051103600c84210b50000350110603c0100000407401c01d050710310662781000301c403032401000c0c1008610302c54058070002c45680115060708003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 787137859 1250 787136609 787136627
    0x307080f031b0c061314030a0f0f0c0b030a02220602070510030209090c070b090a050c04090c0314011e09080d09030c020a08010209030c01181e150c1109070f 69
    0x5a003d0350419a0203501044182e8420612072020100d06201440076505030500c5408841066000f0005180c4035902d00407071a07000d0902904210500080c0020080d100319814080c1c0701d0b655201d0b44a040c500c4c04c41c00a90000707002441d42000500c000c01800c84000d41000454074194010650399141030240024a03001ca075000c0200f640030400341c50030f44c441c003460302e0050705508040c9941d004542070142603d14040c12801d0582c21825002c4080f44d40040e03101c13415642181c00107290116481d0280e602d1403590320082648081c2c002d0440142e0301940006002c0b54400380600300e02c3c120510f181c02300c51240c24010181d0f5014000d0702d070710740001d60060008500c241080c4400c1c1456400095040341c40b540210807603900011264107500782440710001c113403002e003410741c41c02c46503040c0125101c0c0e03a8010a00040e0040386007070950580343c83c2490080c0b402010000ca050f038040001021b05001d41c2e81900c3c55124480240340f00d081500c03011b485000e10341c2e00d040401c01c00300320480d08002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 787139109 1250 787137859 787137907
    0xa0c05090c1b03040501030c21150e0c1305190e0709091d160b03040f02061902010b09010b07030e0f01020c130b13050402010237030e0307080f03 64
    0x803040c440c1d900e04800c420b02915070700c914003000359110f510302400141038820b00080e80c0204100840c100300121340214140c00701c1d016640010a044a40c0c818041640b280c0c0d81c84205251081000d00881000440081c110541043d800c0c41d55203407501c0601019220441c00a80c84240700102002183d000f40240da400c00d216150003010b241d0f44c0c06080d0180c40b00d1026110408403200d4100312091000c100f05218040442140e850301450003000d5035440c040200041d040200300c02c0600219500d0004540168410a01100c121010060024020000f288213680500c4030580081142218882a40e1402d40c1c0750780c07a0141684000144840c02840c591414150b1007403030310751100e581d103a01d25407120440c00c1d9170025601e0348010070000c981c1616401c2c0e0241d2490601440090f0740d01242c4031450000a0302c4001c150307002c03440c0b4500c2154100350499800f1071004d00c5041019404160180b14050440444811a4842c0c0003140c88200f00100382d25207a02c2041040b0b210550000580b560326 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 787140359 1250 787139109 787139131
    0x2071205041a031b07060c1d06041728030206060d02060a0e01200c030c0a1a0307051c0b030c09010f060e01031b0c12020706080a09022709010e0a0c0509 67
    0x880404010913141d04610b40446015880b0011306490a6020b003d42d40d10003000c030042c100c0030180b8000b0544500c00e6008002880729286a45d85030700c00308000c4090b0202103000040c5481c403400c4004103500c415550304500500070040030940510b04440030992540e0001c04040c40d0a400120507110f441140e46803030b043c80b40160241c0000704c1103035040f02a04202c00701400c8240b212500b010b08065030011f03498402c00d002c5005000310711100480303201c031006201009617643c8a248043d03582d8000c010981049000000003504140c20903000701180c1c5400b034049a40080000e010049021001d00a00503c500305070000c01040c0e2084039103621a02041c1030008020070b00c00380c0300f482d1005503121040400c0d4958806810884100e2200d207541c1800c0c4080d05d011400c1840081003580040e1500301e82940342d442100a540d43d070011030704208a0b8640d6004a18050700390303c0221101156540900c0d4070b01044584070300c030041407a541a40e80510f551180c1c0b420030040021004029040207944 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 787141609 1250 787140359 787140391
    0x20609162705100501093503041a040302090c1c1a131b020304030b061905060d0c14090f04150e04082a0c040f0b1302071205041a03 58
    0xe1081c41c070502d0b018824400351030040608020024000c0041548500c0100700c0351003400100c0c144080e00da11201c1c0780450341c0c40308858601c42c003901d10701a9070002d0700c1c050007600040308400450303401002103134402e07a0030021940e03401c20801407501913070b460710b4140e50740360009884c80b500a03400001000d8078140060340b00c0f0409030125461214208242400c19a114698256001b51101c1a0710800071403000714a01425540c60011310750001d01070700c0c0075046000150348a02170f59480103026107800340009440d0b00000c03031802d019101101064000ca8140380c01c54030010100c00450340e4034040a0312100c0548a008284002418001d01c0728040044118001c0b4910020010050240340120034a549948150000c0f2a01c209650411119030380c0201800b0359841001c5081c40c407541040310b0018100a00010380030251007840640d55000040c40310887c40c605035913001d0444640101c0210103202550402550740d4400c80c06800b039001d032030b80d071038604110b00c2c03d008650101d8080601251 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 787142859 1250 787141609 787141679
    0x61d01210f02091c030f0311071403120615070809120f030301180501061e020109080a27050306040b091603240515010f020f070b0a02060916 62
    0x71100d40a1200d107889400291003101803410300e8565800c500760b101344541c0001140d034080c1c012031a1070b018005054558940f003d441d050345066940068008030100001034000950135140d501541c86811200e040744040794650901c0b03238400d0761590b641c003004c03072070301c60310740c49a81c51a00324991440c2e21420b000031400404000307001800c1846025001540c90f94140b812468281e4403081c01030000c030385480c00411205512042d070078042c0000002c0d41040440c035010480c0500307a641d03400340480b54002007541e8010381c8900507159031105400280c0007100d4448440801101d18814194107600180106001c9007607901c01c10341010342c0070103d60b40c1c2025440508481c0ca2940c1c800d603010144050b84c2c203500024900106141c500c1d010040200c0e14040714101881080c0054590401112900700c41c5154020441c040e501c44111040302d5207103a40b540381301c5450b840b0554500060041102180b88150001040e202c80041d28130291001400d040e001d07100f0b06640025040040402d091040c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 787144109 1250 787142859 787142861
    0x2060702301c0c081e0f06030102090d03091409090705090c070506040c030c120203070603020a270306110c060402042012040b091506190b0a08040c061d0121 69
    0x10b440800d1001040b19250400090003006008003034001c10005840c41d0707140003101043d0aa841480940d18000c80c0e12150301182c0240076045480c0c0d0400340e00b514000c1410b1b00b0230701800031100c11900300d03080c0d003070181c007413183c003504c19110282c4551141105001e98902f0800f195800010fa00301c5130f04189542d21034620b0104160340c1070703d000c0c2c8038040500074003c4d4901c0d043d0140100300e034110451708a690100e40c0c8c0700114030644013019400b081a8141714440c2214842542d1100340506000050201c00c40202503503200c2204e80300d1800940c0c0c040b02c1072400a50760031b40070310382c05048943e0316502480040e00750751040400f6440845511200d80d041c00c030207050060302041c2008064a46403421030b40920b00544500345a5100c0c0059401055000c0c0303040d83d01c51411748400c01c2000300040c010500b000e05030803503008031001103510180325601c04900c51050703000d04000e4850555403002507411062000a24141d41001503c0071440d50007400780d0b8034807600300b4425000d05074040003010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 787145359 1250 787144109 787144147
    0x30507141c261503060a050702060601030b0f0f010302190e0f04090b011215020309060402151813090507030515060109050d06092315010902041d0c090306070e010206070230 76
    0x4080c0702e03540c07c140b1a070340307504000d82e6500801c2030804100080c40c400c00100c0713400d0b8902444e442444601c8030156240d02c29010350b05080b40d1816901e0030714a0f140320207400c081240d2821406040101004e02451820380030f00d855140c2c22212640c401d90a044421003101ca100c04141c444910010010f02122880d04c02140300315800c6000e00180e04203032040191024045c204e0700c5070030b04203001a40880100380c070b445484000c06c8541e0407050390b803034000c07001a14031842d0140c10f900411000105004002c03402181d0513800c4a010171003a40c0d10790040d03404903410700030340350482408040000064101d034012501c0c40c0c01600541c80d020403451070156039120b01d101340c0c2c3d02e50308480c01d0b1019120075000000e0250882c04001d50800f4244142c105540000301d091180303948880c1c000c41d02c0c1820050407152400d20260139123030710b0b10348002e0140c0044180a0310360f005200d4074001030400d80c404210a0030a410b040d4844001008118124944080410800340b648070204844071805044808203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 787146609 1250 787145359 787145371
    0x14040b062e2a0b0a02090f0a08011d0316060b0f040c0908010c171501170106030b0a05100f03150e090f070e10060c030507141c26150306 60
    0x858204034842c400d038061100e1030440d1080d84007041411000007104885000d5101440020058482d44001c000030400140c001b007886d005280803070701192051040d04108951030040040022610541c80c00d1030f40d91082b008003114903070400d400600010f0742d9800c404c512050040c60848003900c3c410010b411a13007034410f0300e40415021802000105c0080c050258804140c1c2008e85646286610342c5030074a0000388021210711201c00d20359a0350b030080c407040d50046545041921a90303100d013006401015480708803441a1091080041e00340f50210141240c10102e948982d1000640482500900852014030340c1074019000e0100b0134020058115104d407032504000c0042c02c016401050a250407a00403500c040410f800b00050b00000c108071404031081072a0290744282903041c1207030170b805026070007051208414480f84ac2490005111070540e0280341e454010141c8154055a1031501c1d00a044070300600c0807001c1690050701c13440786901881001c0103010741029034001074103120080328a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 787147859 1250 787146609 787146617
    0x32e0906020c280f0b07090315060f09050601120b0a1203020a06050a090203060c0d02090d06200306011b05011b0504030302010c02070e041511180414040b062e 70
    0x2044500a1045030350340b04031020f40d4404058640c00400c103280c44010344001006408152844c4c41003d069004580040881e49818101c00d2108080e00c1e0311710410100f540c000101042c12803542c440e0354005d03141610355541118a481c415805419070b000140d81c86007803e01d00244000a0360940e0460034031aa001c3c0a8154003850510221100540702c0c0d1070303c2d0301e4030400b00c0040e02d0020b00140c00074141c0441689400002908901a118190b000c94201d2641403c09040000d02d4001000300314002040c14030890311044041c4a038003044030028005201c504508401c00c3c0440c0d001c0300c03082c1c00394001191800c03c0080300c841030780c0030f14102c2c0700060000400f0400c1c9070b420b00c40c1251900b542d1000d81020381c9402c10038094920083c00150140100000c40d0316001c603164486401d4048510446451f060015402001100a4032586000d50f09000306100c1c01d03005090181d206982c1703c0340e003101035141d610a001881c820b403409542513550300941c0420b0f03140c1c846030000701a442d03035603 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 787149109 1250 787147859 787147873
    0x72114181809010c030f0203040c06050c0c0a14090a0507020615040603080a3b01030c0c0c0f0f0b04030f12051b0102040303030c0c0b04060b06090a081605032e0906020c 74
    0x1078018201c2d01001b5020980520501c1880000b9490400b1b401c01c0307560500e050390321b0f51840314072141804010720046601c81c2601800040700d814000c545c20412204a40341c0c00700f0b0f918903c100042c3c030000c50340940180c11840004155402983d030b0001c400c20301400001e1981d84035a0b500245610029542012030300f200c00078440c03c0e4032041141e00001540382e00780c81008640090803149202292100c0c10705480b800d4030001c1601c9220404603031a000503400c9406603031042c2c0f0300308a001c28010001804001e40011408200000031501126400345004810301c0311900c40100000c2d801004008104040200040704120341066807402c10031507000680d0b851442c900641182d8400d000700003445410401c0794080b45a0900641c2d00030b4003c04003185007001a80054401e12942c829103a001d40e01038070100711a400010364864103021900044c0c1d5107512102003650b80d60030305440f1000480c00911560481201409002c5048240f41c404140d550b10355403080141c0c2c10105c0403c030243d00400c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 787150359 1250 787149109 787149131
    0x10512070e2a071a070f080103080703021e010f0b0d151104181d0c0a0303180b0403080a0801060e1c050a020607211418180901 56
    0x19020a600440004020162034040c1e0400c540500520402e21640e1560a540c0d0402440c034240e50341c842080e0045644441c2031905180710b98203a10141100e180c900c0004840500404030342d903150069446005143c0c1c41c4d0350701c10003141d001403001c400310f014883c001030504802d441070782c0c0250041400403402d064a11020000c039183d0642480c8640b100c03c5405000c9045252001d80e542d0002d68003064240d4020754240c0140f04070783c84203035507414684000010700180d9125680c1c03450b200300b800320b01d0a9100c480c40d5960240d04042e9a00400c80c01c0208002401100c00703452a540d8020100304443e42ca400c402d405800541c0700780d50a20000464500155014a5880c003410341403c28042c1000d1400c08144040540800c003c0f0f00080d4100503014410704008040409500a0256603680d81030700c1e00400003540880030700003007180000300400c42400f0b1695007210f0421500003e052000c0c0c0c0c490b600c400c44004c4180c68020f440d41800b04d00e04084101c11a208040d050004a4100007403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 787151609 1250 787150359 787150369
    0xd0b100315020307270308160506130b13050705060a030e060609091009050c06070c050109080d02060f0414060a0b10050408030403030c170a0804120c0c0302060307020a05030f030105 80
    0x105084a5442e00c100300300300b2895081418401058800000c00e090781c80d2021030519249081d4001400300040450b001102c0c00c00f6020700c60480d803245068541948450183c081104164034008040100f0a0001100c03000e82c01100b11403903000e8022034140c40e90301d2012032031551119000c80002030304d03429800c2d0428810009540c01c0070064401c4422854050301441e00d51069003141c03034005844660701400d00804202000c0000c000a0500b55150080d14250340e001c00d061064502144002d00009084c0d18081381c00e404441c03090300500b40a0744c0d40000703c1001c940c0244100e1300281075810010107103000308540c2c0e00c00c0318011030002d8180c0a080c10480f8030078013418500c003044020801800380c200c020007030700c049a626040c003203800720301c0749840c2d558604442903203244684081045620701d60b111981c0c6000d035015000400ea001400a0700b100c40c0c1c40c0802010b0f1101d9001c0d2000c0005050420045502002510603903801d07200c1c580d146410750f4000c0240f14010340020006101c10320740 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 787152859 1250 787151609 787151633
    0x40308090a05120a06021308120c0f0303070c121110090b090309060d0c05070f08070c0f0e131401060806060a05030607021908040b0403060c08010524090d0b1003 71
    0x10403a14150f00140380201c1a54070124080c000f003c030354020406400c03140b03800d0801b0016003800c1c13095640121402d0440f40380c076000170500344200d21642a640c981c040c00802201d000742401d545400001d2069114042c03040f4a9a031804204002000450300d0b0201c203001c07034540310809400c08070305240d95080101040e00081d01c101d00ca900200800501540c0314402c550140a0704640828581e0f031030001603c003401070340e00c0904644800801a42041070580c01480304070710554a1044e541c0c0ca6000c5000640010b0049644001400307010450704c0c207518880c4405503110340c464007040c4043c2e500050a40d0b8503a48035805a5211006101031807515240800c041c0000b40c00405c518a4600c1000750750741c0b0310b089102c0c62008000c10803000d01084c0c02c22180640208000107540301d47d00d01c0c001d401400c0f10200c1c08006040c1d400042200c1c0f03485020000c00a0058892900501c04a1454a02980310b90030103540400c800544000141040640e60702ca10001d01021446503e58109003000c081 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 787154109 1250 787152859 787152869
    0x11060c09030d0305042108010e0a06050f122d0f01050717040c050d0b090f16090f0207020d0809100504050a18091401021308070f0603051b040308090a 66
    0x10500250302280c400003003640c0780503920301d400700d116292810b0151800905440000c001000207007200d800c0b54111180c40d04840c1118110001e903640e41842c0e0040740c0b081d00841d5404001c65615105e2890b00c4240c4507420a015429190031180c012806101ca444d20280810918502c13040907910450902c8801101c0135a0070081c0198a400c42004010424100c066140205940c010800740320080c010b2602610010709199a441030394181003158101c2212800142d10810b545820340720000300d4600c041040390000c0c03400450400150b46c004e822144016109580d0078070001e00980d80e070156500c41d0902900049079580d0300c60061010f0000f131a0700c04000d201003000204080c1e02c0f1000300800300c84a001521100755400d505540241c02481c2c0003030840b03042e40d004000841c406500500900040c00b52420070960f8135010640c90746118801c00d214415203500030004c15002e0340100303034071456540300c0e4000500380b00350a00842c2c11540007658844004240c07604d09090108070200500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 787155359 1250 787154109 787154131
    0xb0a0906170105010509060607150f02040e130f1101020f1c0e011e03050601110f07050f010f02070902070c0b03010e100b03040f060e03130b0c1b1011070f061106 71
    0x9070404011846c5000b01501060044074005082010310400c10801820f4400c0d150090102c80382c08109a80a5001400303100021080c030808581a00074414246080701c2e8010a171400300340321511541e004041c180119030550181c551468000e1000b801107040c40d8000ca1264600308032072402c0101503c20140d5114103111039a080d42110000c10810454039a20618010456589090040306c030015401c050360030078414211308124a03100454188203a550948030409050989030046842d140ca00c5040310168120510610400285400071304103070740540c50034440a90f540c1c0303007400680d200342c0c000d0f144006901d085c0480e01c82c1d40340100d40101000425581541080d4a8180800501440061900e0303920030f41030302d1b000784c10310903240e011031b80900c0520140d03910b44602e0003a6001c0641d51311a0700540842150070b402d210003019041c04041c2081d50f0301d0a24a00c2a9191012801c14100b14882c2102c00100e585541c0010b00140090380d490007020b114140820386000400f4206480c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 787156609 1250 787155359 787155361
    0x5180f01060e0a050702030d0b030a200f010e0612040c0b0a11060903090a061206031707020103140403210204150903050c0306160c1a01030803040212060606070b0a0b0a0906170105 79
    0x900c0d4000140e4208c0d038000d080c009034141150340081d203001c8110a0080400d1200004664002d80741c1e469146201301c180c2d40716114806031001190f550600c200e11590007401804015520100c4c0c07050f6603882841138000035032041d10359000f0440c540001a051001032001c0c03c40350203000040c080181c010b242180154281110390000490901142c00389038200f000044000300c4c101c1c1c6a0b0030440c001c580100036000f003c08026812200c59001c604140d0201e41014014415810300807c100c1c0301b0381d05552261425002c940801d400d002030001c4214031030760280804221000c1c800381500b6140641d898041200f481c600d8a1428200312070b4003076200340c02c090104083d40307a0024072001e8180da00d18002d0000c901e1407031320600805a034401c001444c90001d00100400c030b142001140114003c9580c400310a136104086030b40e5180403680d50307401040a004040015158403c040d0300898030640110342d503100740c0042b40c0041070b182d01c82289103880b41d1041080542d801e1010140420403c000c0c022 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 787157859 1250 787156609 787156621
    0x30406051f030c0314011d0303071b050a02012f010501050913030905060a02070b0f0318120f0f070204050f07120213050d0f171e07050606010305180f01060e0a05 71
    0x600380c1e203484050017803035070559800c120103001e5101c0da204a2001c5184010308946940c440e07500d03041100c0750700104030311044d222403a011121800080540c800d00800845006a00444625001c041d80d02a00c00100301480e081d400d0500e4005e90f820745d030000000e040e6140400f00440100007402e4500d1854121402001003540b118200d4141d410a135070455642c500420101c0c6040200ea01002e1041c50200c1d040c100b086142d4025030103840004001c4070900303500c8100da9280e0b040b00d44070b6078400004004400c1e080b0549800b40030746401c1d407010213081c040b241e0080703011b842003101c0c04851010032200300822a81c001d59140c20403a0401c0003182000011140c003c40c8034101c0c0102ca1007520840703240d40401800e4407004800c181d000c02e424000d001c05512030343c85900714100702c08800d20f0a02156458614400c00e90b00d049400400400c25520380500650007000050a040003480e440d00e0344210041c0c0400203040a61051400003034024600b00018001e01c0010300312000b404d007003a040c400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 787159109 1250 787157859 787157873
    0x30c080402060a030b0a0504060905151813021305070f0336020301270c0e04080313060e010c0522050a0303080c090907030614031609021e030406051f03 67
    0x683c0242d03410001034060508002501080255200f5907200d030501c140480e82e05030315000140036015002c0e016032100ca0a00c01c00c55100c2c0d150b44500c880c00c00175130001e15029103180c2380d0200380d030007d000c0c02800154503010805454049602201041c01c1c00144031700c03550715210745058001d01d101c81c02000441c5128855101100d008001c041c02c42c24031030b013400e640e0b00b94030a03080300d2100e21942510980780e00460b08081c40c01c61090b01c0800b070b0741c40009460f1085840242c415030307000c1e0345646990344025005018099136001500e4141d41c41c01c207a05800707024400d4180002e0745461f4552141c80d041c1d2a14889000350301404541002c6d003904108940720000a44203a071340c10700b002d2113555148201d22555001d8100c45607442800f0f00f0601c0185500b40d40004142c8410390781c1048504428014540e55840b803c0070600086000d107810001780301141c3c05011615000c4101c20403002c105944950390743c00640b029140a503035403041c481d4400040e40761020300d6180a0b141040b140c42c40d01e4280c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 787160359 1250 787159109 787159117
    0x170306010813210215090c1201051510110706020313050a050906010309080717030601030c0f090314010b0406030809120a0503270303161515050d051501080d030c08040206 75
    0x5203061001c3c40b18055058001d11040c03a410f141d140320001c0c28038007600d01e169502007a408180c050042c002c0b040300044010b0084500c03843e110801c2c00716000d40e0b40c09000340b1003846400c0c02c04204980d102d114080700188604402090158000d54071819120340c1c201100b0600c3d40400d200d00004a03040005846600301554024400d0030001031014950800003591f01c14800d00520940401500c46c060700c1c013a4020b10b01502084c2c1c1d00300a040c842c520165805030300241140c011a240050800010f240c0e9495039481c40111400411409141c101040c10344e01e803a0001c5440085c00b0454404c0340c2480083c820387c100d0400d000341402650b949907140caa00c528166003c02e00f00344070f817814081c4240c0d12595030015001d012650784007007104c080c4560040b03080d01141d444200250f0102000003a0081d512101c1007846450205072038401004107803050740104503014045c00708900c2c880030440f0070550092200350301900c160000008020700f11a0602d6901c02480701100507c80940c8580b8203403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 787161609 1250 787160359 787160393
    0xa1104020306220507030507050405300f03091017150d0c0603020a020609011b11070911180607030903020906031c05040e0c0a0c0b0c07170306010813 66
    0x1603481e1514030203d0b510076100400041600c05400000c10820040ea104034800d024541d0b00304030b44d466040003121300c1e206034440c0703607403200680c94141c2012000c420481c01d41140c0c02001119068100c6d40039040545000302c1c0101900040713104013241c03c05100041a14105144c11881800c4840600d4040d03140540501c0c441070040352400c04640b128101c0f114004e8111025000140d41d401008010307500c000f03e141d00500500c1c0110390a440305014103024074140000743e0325038500c40300c0c0c200d6200d00c2d0301030f2001ca94800c0b81d41c00038440c041c0e84103441403504410486940d800880105c0604c500d451803045010f10020010500420f0b44a11018152a811140c1e040581c54050000386040b102c001c0c80e41040c204134554004550304a002002102e841c4072000c1810342d0380444900c8076019030805c02c00801c1c56044007500107070b09064030a43c080c0c0b41d00c09903030802c42584c807240c490309a080c8001c5820503000050180301d60b00b0506550380310300e518a41d11a16421941c5506001000c4448 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 787162859 1250 787161609 787161611
    0x40f060809070308030c041d090c010c020a1d160806010503180f0d180905130b06010c05120307030b04150b0a020c04021908160c1b05100305180a1104 66
    0x204101c2078060103514025508070703140b40c0c3c590500080e0070640da48548181c101200740c2851208003812407440e42d81c482c4020328098402c41301000f0065603070988042c01280e00030305010005c2200b1480070f2404400e110004024180762a10422001c80800041c41c2ca1051206030020000d007070b81d01008887d40b0820f0240c014410001d03801100e0b141c006400c000310050b0150503003c3c50a203921100ca1500310354007624280d02140d407205840115001a20004a612008003c90700400c5844904680040061400a50300f90b00d988034941021200c400702c101484000040c401440d40c0b60041c120307401000c480030413050070282ca88500300241c1e031140354071040d0085000010140248a2080c0e182d401800a542d908a030140d02010301100031540f0000c03039172410200700a50104141d00c407401c07004d9141d040484400307444042004180341e12034400b24800e85004a40c80e01c80c0400b002801e206502c0c04203050920041d2310035007040c1043c4c004a40e41c000c51449000c180400300480c81107030140d030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 787164109 1250 787162859 787162861
    0x4050114120429280603050a0204020c1504060c17070503070804080415020f1204030206040e0c09040c020f011a031513060c112104053a050c0303040f0608 68
    0x30b1500f401070300c594070311503442c40102000702000a140120a00311014242c42040b102c0d5071503450115000f46c00080c28030382c0440150401402c248e8010403034101c0746001c03035940500520908125810413502240d61549402d00040c003240c11901c0c444c8103214100f00d000716803800540080c0540401081300c2c040007103c601080c140144c1c0402c860203030002c524280d1f14801e4102002c5c6d03481f019804c45402030700c1010342c00d0045d20315900c1924107a9500808140c50a450459026100c90001d89100c1c0003560400030780480d55101d21490402c00030540182030710000c0142c075282103400003155903203030b03002c103110391000c2d44c4d004940c607018041d4407140c0f01c00e1900d41c03a42d000010f520030780005081625100c00300c40740d16000120740101140359400c4420411481303a0031100030018000e4105c024009010902140c548282d8480395150b040e1000070010040803050b0380341e03050021088040d940c0710030702e03541031000606c5a041c20900550007140ba0a1801440001002d900d1040008111084c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 787165359 1250 787164109 787164143
    0x6050f1b090f091e240d0302010615030b12011e020d0605090c0c1608190204090606140406050d08040905070507140d1b050d03150812040501141204 65
    0x442102d00c001500003100340c03924507a19030184140b950408401c00050000403188240510b0582c11019000d000c40c1c030144241050240f650081341c001c0b0155500d4840c08590800c0d00d00220800460654010400b172a094040c80002100311000d00641d90400701700c0008108044210108100c00510040c0d8402c2c10001c1c40d40100416000103900110130313020b0142c03000c0d0440261040a1800c015141d00c0001c480c25045164054440e03821903070401145c000c1081c0004082207401c50001d40085400700c5941c1d101d004644194101c8500310300d00003145c3e00c079400c0c030b4442c01014150648640383c0540581d210000980224403d1210240e15040040c002310311940580303a045510006400c0c0b11501201c0d0300d80c8400e5001302d05400180ba518231958921880104941d489402101510402416403802c0b00505241c6582c013500301d4691000161511040101050100e6400d000c00d1701c5904203000140400d138a4800d00391038103002e200c81e07850400c00046640e0000d600060842c40120300c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 787166609 1250 787165359 787165369
    0x30f02121911070b072606060a0306091d07060e090f07030221071d1e0303040f0e1b090310360b010e1b090f030d0c06050f1b09 56
    0x30800b0300d050301c00302103070000411102040c4140504503d03140d05801d02111000044501c00b00c07001c8014070b2103460b0200711941885d80c010f0043d40382500e0701156060302c991107003099401c00b4001420340c0703130ba225000f20301540c14480240900040e2826104035200352001030103840c03002c3c04664a848a00b804120b25078001d504992102d03240c0d00c0210001d01500060703036420101200c1c44800725040c22501020151041103141ba0702c07074000d00001a580d40400f400c003141c1c4c0309405868140c8400c10000c00e066a0f62034152000384a00b40c1e682c0c011303140141c0340c10700300110310140104203201400031242e183d4010640905003041c40c5c1c0300240c042c002031402c10080ca480000b880d03411030b028400800310b021620003402d005015001c80c6800740da07a000700c045640c008451400b5541d140805000b07000c180b1200412030501c0040a04000d00e00303010002c1d0078144c07a080c038540420410007801c008c1240c1400740c00e03402810711a070b01840745841a503030305061140e4010f008140000181003201a524 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 787167859 1250 787166609 787166621
    0x2609120903070f0e041a07080f040c1806090b0303180121020706050403110d050301060f0905060307090806070c030c0816050a05030418060807060c020111030c0607030f021219 77
    0x80da0f9a62040c0d910b00080e00d02c0d0b00280c50588900416100c2d20038801c0c11016918010b0301c1560350194079942e59001d00c6a03882c1d0240086456101203140082c000c080480840700c144c2c00f48000149240c035203a04c82c0c040700d90364100a8082e03041802414800c0d444110820420740083c28420740303009081040e2100c0301c01d01d81188201c1d03403003c03d0302c0301400003550005125500c01d403540401801c2800e2015598030b0800107213030024004000520009104040e6904220142e040040000d5160b6002840c0c1c3c0d0400c842c940e000420f003030020000b625042200541103000d40c10195244841d50328024113098900d28040c203581c00000f6150305c801c01c582018480c1d141c00000ba01e10902e07641c94020f842c1c0d406441482d0003e00350f00c4000000c0e001d40c1c400c860451382008000d000e110b02e06035050341c0503052603006a045c000d04010f0346282d01410300051000d07a6048010309810f103000741002e42100c42c40450100c4052040c040e9090a8031140e140c1d54114058424500814480724024000307044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 787169109 1250 787167859 787167869
    0x1306020a1a1e010605070314090a1a04050d0b0412110d031802061b010c0908070920040f050108070f1b060b0d0305070b06030a020d14011506260912090307 68
    0xc01d42c0c00000d07240340d200029054480c4640e5680c00101154001510715004840000754012070b1040104480007200c0101c00c0344804260002d410250b4420004041a4040c1000d0302c076058150200802c11580b04142070b1141142e003007810340d07a4030f500001a83c5109007500e900606940b441000c4001e50b41d410100381d03031a4020100d540d16464404400f9250500341d4000b0f0103582051142e2030f00d40c0c0070303103e0703001500c1445000b094681d14211082d8040e1031406848007072000e00900340c0d40008100303c000c04c041c01c032614400c0b18030b901d0100010b0040078010460020040102e000d100440e6120348186403000f20320a048020b0881420014001c1c40900e1805511000362080201056082009002e0301801a05210820f948413024552954607002e0000d50040c080031090001610181080c525030000c040001808848040340c0000a15190805004201c0d182c24044814090714080342d43d040c41c048043c4c0c11030503c0d01103180d40302400342d08055110790210b020503441d201000310f080105 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 787170359 1250 787169109 787169161
    0x10815071808100e010204080a1104091a0106090902090622080615042702010f1101020424030e0601050105071a010603091401050105060306011110111306020a1a 71
    0x980e1044890f81c1d40c00303680c1e100e8005a05100341140e56a1040c82680c003260041c1c406800080900d40c1c610000c1424032617180c1e842940c0306010b034007213400d103003251005c8000c001c1c50070714a50501c0c2015060704950f5110003207050040081ca0310381d84800703081e202c82c40c0e003048281850307000b040644a51700306140c002038054030400c01081007002112540194998003503400300100c5200406007200c3e074080319a0100000480306400d0010b501c1a501080141054500101003415200c01c03903080e41d10a9210b2001100c0c191700c50450141c1c0074456440341803160800f0030810f541001c400751911300504c5468140000814a1402d00031900710030381c480316540281c040c2130b603141c00d40500180f540400c1940c0500208080130900b1605214030303410b0342d0b8010082030a40c0c1d103200044401d10305162800c200c82c01410b0b8440035403d080c0c001c610100d4489000e041d102c55620100c0041c2d1191070348400115406607101801040c050130483e44c58220100f80700002d59550002c0c03808158810b9180c078088 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 787171609 1250 787170359 787170407
    0xe0703090f0503181c03080709031209230a0303110a0f050610050d05060105060d020d0f06141c1e0203120c0105070e01020303180f300301081507 64
    0x300c000300003000d42c1d05642c002101c1503242c0c40c0600c960175000741c42c000e0003420074003520740c0424000d060140d03200341d0f01c3c5054040f03a500c1c2c1e034610680465180144c8080341001000b408404241d40c070f0000320074680c5601003029842600000da0521251001800b889010120100781e05004e2100a8115421011800ca010300074500030343d4403042100c112989044013640810b40d841c003441e10745401c9801800400e13007a4280004c101d41039100303128041f0715550820103a206034200f0302410b00042204040047c403245003070001c1021b50741c100c2d010340c800d00f1100d9a00d10900201c491103204940c002030b51031140f44400b0383d8036415680c0d0900207903040c450088522a4540610b0040030f104440d80000d01c10303a1648042943c0c00c0043c07030721b40d0303000d6002440001c180640d8102c480b08071586850807680010a002c5141d4149260b0308a501072038078a0400d41c074200b80c0c4104903001c0f400f102003000d80c51580340084140d1108004110b9800c2469840302040ba6a403060407902c00c1500500e2002c050 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 787172859 1250 787171609 787171613
    0x20d0b060105041a030114011106010915090c0e010807050405010f0e040e03190e01031503021002120a0504050f030a020a031506090f0e0d21020708130305030a09120c0e0703090f 78
    0x1254209115900d1f800030100c0000a03c0c2d489820002d4109401c41e005060b031b80d09000184000e8043c109078080401c030f400d040041d00d010540505520505603480300c2c00c4900c0507000060511400500210522904000c1080f040c0d900110326180c51506190038400c0340c5685000030090408241603101500c0045146007001341b03c41c00108d1140d66036215018088814001501900c01d9004c0d140d100c9001000c1c04c0000d4205000e58050020007441070741c461018480b0f07079086641150409400060b408902408103040c0600503528030001180244148103465000800c20303082400700412084800b87c1c0d030030a0041d42e410440140c41c0452003031086900603140d10005008400043c0d40c1481a0300604807240d004000fa140460100c0c2c4503000d44140c0c1120b003c000c2d6000d01c03030480c0e1141d400c0044095040703203050200d001d188103d001d10b42c1c2e0303440344800905200140d00541c8421170000300803c006510080c40e80104c4d9038104018100d0395415200b54010080440007524003c006405402 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 787174109 1250 787172859 787172909
    0x907020706050c0102132c09030301030f110d050c0f040207150914030705030d180b01050114120405070504054005010207060b091302090a0228050a0201050a09020d0b06010504 77
    0xc440a00c10f451500f8030a20307d0f46e0340d1300f1003800e540900c29034000300700500200351220081000280501c00611002d1340c240046031002c880c108080c6c5e9241c002d0b2141c00518500203400c810341d00300c104e9043d410445d05855100d102d040001d00d0f0f801d0180d586440c1403c0000308180c0c0030551204e04183c075101c2280b410525203990142c904a45041d00d0040054100c1c0600809440140e810141c80c41e00e5030300b400010b40300f40007040d40c13410005100f8071201008080c48130707210780302d58490000b07011300702d1800041c0402c2d02c0b03000e0002c40406207000c401e46001100c0c9142101c840082c035010320040d01e80490300100407511400d014105500005141c81888001c5e00300780c80150040e10b280c0301503500d155061400560740d490003984003404c800414583c81854024101e521888201e501901c0300c24400c4081511000545402013030012610509ca00d40a01c103246e803006041d102480707c030103960b0006006081210005103540c610b000800c85a074030520554014000805141d0f40160300182c00076 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 787175359 1250 787174109 787174139
    0x40b01061803112806111c2a12030509100b0d021e101218020d02190b13030c05180609070509030d050909060907020706050c010213 58
    0x410100c151050300307031000e031098000326a0000000c640d648880010000c80680d0780b003078400c03000a1840c0c9403c1c00d40310003000c40002c042d2074542101c124180c0107441d04111010207039015680b1510b0f008200c8503081510310303071110740c628132207513000c1c08215800c4110541004040c010819050070740140c0f0f038060b440603000f46100000c8905032002d53380c8010581e14104403407500090450110001810880c20258805043c0503001000490f22800705403201c2c1c41c0b00c000c100140c802c0e40d14503440d0000b842585a40b00141e070303009100491036000f040c020004400020701603000313280f915080400c01c061080107441d061189940d1030542d400050304012080c0000d440180c0c0840c1d001a4034604007601090003007403400b02e008e082c0d03140345c100030400c84014403401c144041003202c000180da003400000907074103154403140c0d10381d60607600784861034030003c000b075000b99000818061080d400042003812511103140455a8600c1c84206601a0090341c2d2403a2030f0201c401ca0120b02007803408084 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 787176609 1250 787175359 787175369
    0x6021306031e050903090f0111030f0714010b060a110307120509010f05031003290a1a030d020606040209010315031406070c1115040e040507031112100c020a0b040b01 73
    0x1440c514021004840103c0380195070070740e100d52042110a483c0e08101c00c903801d4900d414182000b400001280304d80c11540b2100316113220760f600141400070400c2c41d100b0303036251580080c000c024184691300851b0f46445180300000074044801010b2220707034001c000301c4002c0c69010680c9500e8000d9401e02800503009001c640e8081074142c6201c5072264031520540388645e94032803040f104c9900d99280d8207001500c1042c045101c103800d10061401c2c0c0c886840e11030092101100c005400c1c2c0e0365409500841c0d0400591600c281c020042c0e8094455001035001c2d0050011500142d41320304a20040e0000d050441d404480308408800c00402c0c4405d1203010003c1c03460510a54000360b5803118116503001c01034400800e242010000c2c05c526041400800f2428a90070001d6460141c0710600f11841050440382100c4950001800744104690007000199030f00050701c00b05408260082c0c3c0035290b406041c00034003c00d80e2154900f04080c402c015003021180c2010000c2500d0a160a010410140074000c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 787177859 1250 787176609 787176641
    0x5060604240b07020312040609050315040308190b1806030607020a0f0602070c05040f020c010c1809110d1112090712030e040e0115030c050910120602130603 69
    0x10030320307028850702014007020485801d40c5107590826140180c15001041c081e0781520500904101c0006040c1c01400508016290441c1d050b2504081500d08101001700340018242e44042c000080e4006404580040b07580701904004000341078284001c00c00a01c925500501001c1c240710240002081e16004642c00d030143c1380c040d034414000340d0303603001c081d01c004021500e1a201140455441c1d400b411419101e84580c0800b80d5030368000500380d5420045140c40300b43e0000c3c48030703c00b1201b48150040c03070f55107081c42544280b040d0000c510300070f40361107010305031516240e501c0d40c020301c2e02003140d910f920300100810560002c007220301001d8000300d14000f011114000840d051041c00284801211000355881c4400c10311940d08661403181c0c0c0e10718540060303c0d00800580300c4000e0041c80c29420000005641c040d10314246680f81401550040c2d0003035000c001440307080601c1610160039a211010681c40301b904034036014009101d11120b01040360982d00c008104160302d0f4020a8415141e600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 787179109 1250 787177859 787177871
    0x210150f0b120415090b010605210f150a1503050105130212131b080318010e062d0d021201090b0f040e070909080a091a03040602030c09060705060604 66
    0x1400c070765071240c0042d100e03200c40000c00180c006900140300300e5010700d090300042022103055a071800c11280c281c0000c4c020490200c1c0c101c2e5107068904801c50005100c8003180c4c0035017020209404042c50260162042c0756821144408903124082d20f40300030301014142c89103400340e50100070010a000c1c0038048c4240c0f03403400c03800c8410160b03009a401c08030040b001c041d119140d55000303050300c14510500715980c1c0e040ca07020904100c0314801400051039000301540e500c110049038078450103460080035041c0400c48250312240d8407900705491031107036a1064500c2d04241501c0d118803174a426500740d02c498000160f41c07824404150007400b4a00d81140481c0c2d620f0741c07694030220903100c5072400540c20000e800c480c48250b10f869040045034444103010f80c0c035060340715058070b41620076481d001d840c10034002941d000000d0344a540e90740281001940404024280d4528025a100103080500301d1030b008030128286650070700450b01e04a500034103145d41c4410510f4030603141c810854840b48590b01c0d00c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 787180359 1250 787179109 787179119
    0x100c0311030411060d0b1f0305090106031505040305040b0a0201020a0306090b0d0b10090f15080f030a140f0a081009050903070201030e030708042607030c150210150f 73
    0x241030740c0c002c41c3d010607401d04000b0000280b0007a500001980c940c45511501c0010a544900b20521f00c09030b140750201e6901c1d480d410026040c0c07180034142086980c50903c00700085030880c0d03140c090ec01c4601c100440c99864605048895005941201c01c0c60f660000380d112506405500410f1410700030f8800f0303c031300d95441c00400c08071650075a14030b4004411400c00070000d00ca8901c1d203603004960081c01043c1c2522526014105c7c0d00112a00b868190740d800448074500c503001d4844003c05903400101320602040e0f100075100d0017210061001e200014000c07400401c90705055980f84a003003040144c0b90355840754001c1c46000255403103110504c2a0301c5c04100d00041d4000e2902c190031280080d0b00e4448a0340c0110000c085c070940781c202d580814459440040d5650000308024090000c42c0380c0d000b1000010000007401c81510b042c010b6205d0321003000000e1058a40400311902400c8000000310424800d80c2440c00030040d49005500c0c00f154010031174010313003401d403e0310011402241029250 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 787181609 1250 787180359 787180391
    0x106020d080f01051908030a230c030f030a0605180a0c0c0804060c03030f140402120118060b01050903010c03020307021e060105190308040602070504050f1620100c03 73
    0x64803110b42c0c0110020041c851400c01c03000703806031100102c0f0312840859448000c07074116040100d0341000200102c9001c44001079031645511070140b04c00166103411500441d0540d2441041d582c20110b4001100140c0381c801c150388004014800030700b96940b03044a8440303002c5c00c000200e9038101c10314034040c84192003a100310021203245a01294244c075003400c018054a0720403450900710101521041034540039141e9024601d03280c8148254020b803801d242c8100320644050440d400f42c240c2c90214101394000045401084960b0000c00001d114011100125481e114000c000358140d03091642c5641140c1e03255004501c5811941e00341c81100a00340344091903046030384499001e0342d02505c0180800d03d40b00088404802101d0615007295541c0e82d00d40308031350440c0d0310000258000010400090400740205540070310800e008a50501d000e02020141e21445490903013082408210300a144034011085001c000d000c0e400ca0f401c851400e030f44030003c0c0822446800c0040e007030034408240d0300380c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 787182859 1250 787181609 787181611
    0x60d020d090c140d0201051b0115050a05010c11061606090f02010e0d0b0115030905100f0f050f070e06160b0108150705041a1201080d0e060901090303050c03120f0106020d08 76
    0x107000c5000d0044d03980044803103401c1403042200e54100804c512503202001d1081001c001100304401803100d1412040103414a840e41c0090306200050301c001001905110202c078020804070b841c291105000c0290040c1c440d6103101c000d04036442c004a40c41408250000c8268032403003660780030340d03203860070081c8009103c0d01c020041c055030074a40184000e807484401150b00c41410324000a404d01c4644940e80342040038400d010b42c16540b0900001c0c0b121241c000c0300c24030300c01d0750350500050422240e15841032000404e96004c1110040403a9101c0d07542c54102e0301c4642203440040e038203a03102e0408403040d140c2842200c2d52071280c2c964007142d1070314035055148681d095444150900b890319240e1186c103101190152111901000010142c44140c800c440c086e00106008059a000034000a8481d01030701407541d00c1001c05002074101c603a404a00380c000c0e6689440d103035491360454000d0034950f000f079601a820031941081004420040303c4034241c100c4889500301c90100d458504240c0e92600 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 787184109 1250 787182859 787182899
    0x210c0e091b0f0d2612010608060609061606021b061e070c11150d0b0d05120901050408030313021302040807031121010c0314090d0e060d020d090c 64
    0x190402969560f49400041c07001c0d0b480c0100c0d040300350565691450003020825a2507244150004948542024038268506024062504021005041c55000542580940550148100c400107641500a20303a032003034030300d17150384080b00f036481300b0004060307040d840109580103071588540d20000c2c50003040701d0f45501c8420030956801c3c0c0396071a100402c17201d00b800504240c03411041407a85680c10385912002c0140344800c1d81c1c80e151030743d140c040018140d0302e80c1d1180c18400d014581c02030000c114003003580801c2d10100c0d09029a1141802c005840b203014984c0030006030302021080111801c00040d58292040c42191800c1111000039100404c84c0070703e00600090782c0c410344081c0009141d000d1014407004005082481c08071341e1001d048504240b00c03640c800719035195081c000c246901805040040904013403e501d480c40c2c0b1040c038643d0749248022140400c203c0c0540102d0588030f04041700c281051094007599200f80401d40348000c2c11300d0000480340060955400500d218010020b0350b00380d5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 787185359 1250 787184109 787184119
    0xf03060f090b150c06060a24030507020a0c090e060c0f09150702060a030615090308090d0c05060409090c0506030f042a0305160602070f210c0e091b 65
    0x342080305800003041c0001800382c0180001c2d0440e50f05140c2c60014043c035228420080070030b403401c5800d10045800c9070703021449501d4248000a1841041d42c0c1503610040035140024896446140c202c1c501160310308007600c50340402c40b01140704017a0340c020b07040d0f0340e617045c0442d1140e455022140e022032040d0b147d085000d10051150030914a03100c01c070018128100c5501c1c03801c06c08c041c0c0004032290b22080c01640441d9540780c0400c804041594040820a10750506c000b41500c1d5490303040103881030f1561305100e951400c6404042102420301c84000c0e01c1c010f0030b465120b0380c41c2c140d07110080c110003c0c151a44000207800140038a400d50440e842050f840000000c1a116981c400c44001c0301c54129002d18604201080a450044158600110b000740000e0108a11883d92800c0c9000160003010454010500c10300c80c0f00400480d00e400c40301d131882c5031050381030441e204401482c1c010b80d0041c10344000840001c2c44000030003c140c0180710300001ea40d0910544d0b800c141c03006000c152855005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 787186609 1250 787185359 787185389
    0x106081c0912060204090527030a1209140d02030a0305150109060318240f090f03050304140d090305010b030a0506010506180301140702060f0708010b210a0c0f0306 72
    0x20745031075040a0b040502c218009410281c40c0d000340c90907280200c981210011004036000d40f000c600e4101c0d0302d21080150043d51130902c10010091600304031051900d80c46440703d60b218100668002000b00070200c030b0050355040c0002c40402512a4000028200000d0401e004142c09800101c107504500c0030507189c640b00140360074419030250008030301c020410800953f901c404036007a07807925000007404681d440d801c20800c80c00ba60403580072900000c040d03071a180c0b0400000768400b801c886d00c0723074040c1011a2680e5803850300c443c03114018450b106890158110111000c1e0304018800c0039203108c0c40c020f00c44d0010803014503680c0e420a02010700641d002c41d004105904101c0000c2001e480b4600550b4034209240e00442d00f510701c00d46003203441100c2c0000f04100240c1c180101d0350030020686400c07140d400c1086004200030f1060140305041400003500c0f28801c500482d46101400025008224030710f07081d94111b00401c41d4040340c0001c928440701001e400761180c401ea00648441ea801c116207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 787187859 1250 787186609 787186619
    0x180c0e01062001150b030115050708030403200a05010b0a08011505010e0103112a071202100324060212131502030f0d020c100501060203030f0603070b0c0106081c09 72
    0x10500001ea10b1401a550701c401ca02161104600c2c114060000591001e60320351420407006d0605140e0301039601000800c3c01000d000501132811a0740040c1c040c030b054071034840112a840b00299100001d85810311a0805034402c004040d001070030703e240105c920000c001c0ea10503a80b4240c824a120044084908a105004075070281240b002c640e03006240001d9a4180d0b00d9a140d80380d4020313880c40c00c0a8030441005a100e58011421800480500380500401c500d00031100c0044005e010703009208200038411111554425880803c02c4801d100d10010781c042d0360410b652010605016580042c01441c5000000e86a918100d07a959810100c45055003450f003000003540507518484881103010402c06400d00c540e042000e00041c4192150059550102406241c9000c205400d102001800c09004101c040d401005481e88480c00110b80880350703882d900007d0501c00300d030b0010210744178085543c020310f280550240c425100020210394201c44040160507405c1d80c035400200018406d0581440 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 787189109 1250 787187859 787187897
    0x10b010507050c09091906020d05010501090b0706050a09060501030812070201050610260c04090b0a030209010e04051516080a0504120f02011803030b04150b0306040c090801180c0e0106 81
    0x980f0910302c5080e6a103c6d1a0690b0a043d000c4100d08182e81054010030806c420200c0c034415039004010900700ba901c03480c60003009030028003c01a015055079500e00020f4000195030300001840c0d940840204410f684070b1401070102e8002c003c021810300311280000e2007050052050f40d01502d4020200c14401042c0c500c11030700030380303086008103c2951080310a13020309076100300079000ea42c2400d44a41c440d070034540540b0866100500d900d2080b00044010401341c0c982414032815161881600e8141d03984d1400c1c128034007080481d91000c1c0381c00800c108005420030507410201c0c4500d41c0c0d81e60102d034036500c1e08e0b00c003522010f03a4082d00c00d121070070400c00018042d43c03200d98000200d0001040124400035030496091541009901290300c3e04e811400700e00d0300d0720511800384180c0c00b11241c540c3c00e001d01c1c3c4169000040503580a00d9603104206101400b400e40e40005140d4080240900d85600315180c00340c48a05008541107410400d000c035642c0c071240540d505131851a56202d144c1d031944d02c5564 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 787190359 1250 787189109 787189111
    0x315130327120b28020711190e090312010b070311060412030608010603081911070e0f1f140315101406032211030d1106010906031e230a05010b010507050c09 69
    0x287c0c3e000c001110140c01e0307110070661803d440c1100c0500c00c0600c1c6400020010445c00a040d0700c17a540003001030400100c80406c83ea410340324a14079a5444031105e00c0c3c00c0c0d444a94800141001e4455402004108500c3d58a1502c610b0703480c0e035040c000660341c3c0c1c2c0c485082e5611400300800c480f8007440055004c0d0b170303009100080c105141c5002818500c042c9240f5090455a400c6413019251510070803460b01c8080c0380360741d0042004035041603d2a44140c1d40c2c011804680141c0011000e40c0f401c480c0c20f940e042226001140018a8100d001e04281d104825032184c94400c03605e94540d04003600c0e00d18a00807080d64410aa41c1d8000302040c00c58000201ea40c258403281100c0401d4022441051600d0410a911312404030791204c4511000031180c0714680300050307106202542c1060030074400500080204400c4c00840384030001102c24501c1c10001d2500000280000d4850030302d03210049010000c1c404041d58024002003000496079001110184660000038040740c1c04a4028102800c1210120b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 787191609 1250 787190359 787190363
    0x207081501120c0b030a020c010b0906010f200313051e0d03050d020409090602030a0b0f0d020120060c0a030608280204060902030a02090315130327120b280207 70
    0x5403529140d0402184c2e503017065403103400300d9070b0110724000050320074810500190411910103040e4035162000800c0e1041004900f01000003001003912010186801c294000a00d08160f0780c4035000d5904200808804d88980c520600c1250841850800c41c5821590150700182005000b0700d59901c040e40c04c0d03441000c0410069a080000003282a142e06c075181d8014440c0d00c01503544e0824580d43c0c020343c0c881814507442140c106601b41066030747c402481c0c07030285d42820100e2064501016105c4042e24261361030080c2c7c02207504006540c003422006000307459950310b042107916200c6601598480303202c503051b0301c01d007000002460300706038021850f485644003c1000c60f003540c07202411400ea0b0016215000050f8012900004915040c4109090002034254450003442c4c0641c41041c06550440003030300f80020185d4109954200101e03000340a000103100030903c0c0ea903014044001045c404c001e0321080400c0022400e4601042d0402c4001c1c4c0b400040500c141c1100d80e21700009622039182 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 787192859 1250 787191609 787191623
    0xe01051507060507031d0610060c1104230901021321060903030204050f0909030a05070302150408070b010603150314010213170106151d010903061407020708150112 72
    0x390754009051400b415110300420764021882028941c100c00c2850510100b07034040da003010b802c200201c0b260340d141c03e04a40035441c140e0760300144d900307104070801050031602d0f401074100b01c0c414022154a0031030025040c02d06140e034905a0340c80300160700700d008143c114580c104102d4810000e1640080d09a10307020703a4100ba0041d45103c59503110f0484080c04000c4010a4012808101c5807038409010007000c1001d464a0407145003041189443c0d106132100f2005000b00840d001051510030403007a5a00e1640c1c10f82e02d07089003071a051181c021303001440101c581c0e044410000c941d1b130b4840e0190881c0c41441c01c643c1443e80381140d07100741005e4188002e071a0950340c02c0c02040b040b51180d0007080020103c504018045000190043d402d65080c2d41252521480ca00f4821103129803005944d04403801c043e01c410342940c001d4004132800c0009038400f50085040c2254100b0200d2034154040c09202d940e021038070100d98034591f040d1581c14401c1c001307180d186601c004000c181c4040100030042c1e440b8040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 787194109 1250 787192859 787192867
    0xd020604081608011b021e0703080a02060a0f090503270a17010c0507020a0e040303060e160f0e01020a0b0a0902061603030506040b1302280c0c0504060e010515 70
    0xd000b403902640b115030700380d01640d054040242c24000e216191004586411407044100c16010180d83d0b00c41d084908541c0c6615040d132044086c03414000e100140d40e106401507541c0c00300281c02075071804252048144949883c3c884407209146104485003241d001d00654100503c943d40c40d41c6482e00c0d05c401e512082c00c49013180f140d640d240e44604024000c40014501c4079400e80000900311407407000f6090902004100d0240960390b00c0004800722002c0304858100c5955601d404c8014000742c1c0e1050300d040e5440414481c08880c1609240c08040b800c4c2e8425000c012401012240a64034030741d03203400358000440d4800071440b031340310455100403c0b00b00810a0040c1d1790101e41107600c070300003044400140e18516020164180145038100c64201c80600c155007681300000d0300c50340b90307405404100f640002c050703881e00b004001e5482c05040343c0c600b07001c072071540369006444411070a00890300120003203800710f90717403400c0d102e40400c0c2d91851903410190381c04c0000303000c2d02d1406003400400b006011700c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 787195359 1250 787194109 787194119
    0x21070e060913230a0e0a02060a0e09010b07050f07030803060d0f021903200609010c15090c06030b15032a030c1c0239030705011b0207080703020d020604 67
    0x70041c1201c115102c6248105400c3c0710003401200907020b040303880071a0030301c1620b640020b00003544081032601101e85036581d065810007602d02810401440d900025440000900600010003400f4034074020000d4034009626140f035261a4410713130100601511090012176402e0512a07502540b4034800d00c2c0d207401d0788855400242000145510742c400d094110701c0d0900401c111800d840745085030182c400b04c40c110706c1e40e0001e071013030007904c080f6070400c0354840e6450f041c0580490540035800b04c0c2e1348100181d00e82e50510740711085160140344042410110325102c9ca00b8641a00018505900c13442d60954444c442c0c1c500c40c21401c4026040c2021801a05004c40e6804500842c003921441100035910b864144e5141444065402d40d0a09107206006030182d5004181c1c0511540504100050034200c40440c030b507603d5204410504c0b901c6c8004103091042040541c8045410484e2911001e020340c103038a0201c6e0b41e20884e0080311101d42060303c08000508041c0710303440c0803505c020700d11800c181d00d030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 787196609 1250 787195359 787195361
    0x6110c0409050a0201021c0c030323040f0201080c0406080a0218270105012c0a08011d060a050603031b0a0b1f05091b0d090c060521070e060913 63
    0x10369400d8a694010301503d40440d80c04000080d01c580d0500a880b07241601d0300005040501c80704005030038951101c100086041c0c0703450180b00c0303503503021065a42e1801c25080039000004069412800710321b842002c08c05400c0200152001c80786195142c6e0100d944588144010b9003140d07940042054040110020554445060041d0502402c0382041009545c8000600d240010703070196045c0244104201d1807408039011311313541d00c046844889683d90035000407850014655020b0900341d440c007503e44a141401d07822412a944280d000c40d4500c0d00e50039424812905c0076940341d5416071081252040221313514604001d004148401e40e54404000d44640c25500000c440042d01d60700042040e0740c0c402d16614000c00070b05015942a0080c0c50207040da9407040d15260005107003000e01149150711206190040600c40d80d1264591326810354842c0040d1068101da40b441031400944030b161407801c0811604288034158650300c010b54148941c0500901764402502141c0141a21100e56481419 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 787197859 1250 787196609 787196621
    0xb12010618140607120512011a0d0b01180807140609010219060902061809150306061207030c090c120207020a06050a050d06140f03190201081f0803041a0a080106110c04 74
    0x1151038191f544c5058000e12844240160051408804075108107803061031614203643d60540c010000003400d601d41d10050712131804014034810f85c074103102000b15030242e0104641080310a40040805582c0d0810b04001013070044401135801a03010f886003101c049440701d01c40d5055801030308006551140c580109100354484019840460b01030b043c00f5400303080ca143c810f0342c0201c41070440d11840b010100000d0321410090045071040101c01624001d140050001e01c004503803005211030901d565280c45d4000d00b4050079468040340c80f0410301d484d8101980212074155a00800340504a42032800c269081e070081c00d09035003004028046107010827a240f01d5000074103185413841c5070f00c100c1d0008102c2c482410150310760180d0081d0001c2600d036881d035076248507078590900781100702e0766486041d145401d141d8015080d14100b1a1070010300c4490110080007512494a6810729030014642c0340003a5110300807091380090707681c400401c003542c0720f0050046103d8801c1c094452030040f004c00101030f108 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 787199109 1250 787197859 787197893
    0x80c040b043002210f15090d0203031015031e090501110c030d0c0201090803151008040b1503010b0a0905060f030a15090503090a0b12010618140607 65
    0x80c1e8151441120300c030054007000000081400a0316550110b0480c0010300050506505580a001031905080c482c4658a100c00d10440e005015040b0702c0740104901031f60030384124040c12410480081c808006c480c03050f80a29581001c90b0714102c000840c88044000d40b10405548103108a682280c0030f8518400451504002c1645403a5003401400c41300300d2200106409801c20042803041030101c2510400031508500048000c0b241c00c040e030142c1081840201001000010003429610600c4a1050200282c0f2020021840d520080c0d4013010180e60207080f0380d2443e0005501009400401c41400c40d0140c004501071500c000410803090b0143c00c18524a502d0700304119681c20411800c3c00b810500710010324025890392241c0c4d654286421032803c00c180c80d50850001d102e000c00403101520300190078a010b4039034900f11a00035422990040c154805070800004465200302007104081c100c84910124a0346001780c112114041e0902e81a0000001d01404000c110303d0508050154 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 787200359 1250 787199109 787199129
    0x20d11010c080f0a030f0515010507050712050610060c3926010902100c0606030803010603020306090a060e070e030109080c160f0609050411090a1715010312080c040b04 74
    0x110030300025050b0740c00d1101006e030482c0783c01d040025100010140c0c40d01c1c51070a0030718554907007190501d2800c0200d507070030500c24000b00c420001e08003c00064414403c0c8040c1d10400303659512071004903801200c109024107150084050204003501000d0000c0415042610b02010b41c1c4c0560080703004141594810003d1503d55154800f000703200501200080306101c00800c0045141da002990510b01c0e0180081040807564044040180e85d0303002902039a00404210f03100d60307403200c00401070f501c100e610b98001c01d402008150003807228041c0c0002da03413100000d03030126130362504115103480d58500c45039417540d2603c1c041400f15039804000c05490312040b000d0100d03001c0313404000080b5100d561180501510f01c2d0350400c4641d5110b124102503440444000c10089172084402186000b03601c20258003c40d2110001043c9008007299092100c44500381c0e180c5010f040b002d164a20000d00c005041540d42d14219080c6a20807400f0b07903484240c80c10407d04040c1c9481c0c00c0e1109170041c1c0c103c0b45001d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 787201609 1250 787200359 787200367
    0x60d050c1905030f39031b13170c04180507080f0d0f03021b16091503150213030305031b0901020d140f0703090504060b0304020d11010c080f 62
    0x1c900380d84030807800d0300c0a0030441d10f03508046401c4015954001e01e01c03d151785000c80c0842c040e2645040328404200308003c1011542e5a4040c1040c50350b005031040000b400010340f4440325403912a0550380e64140050f40088c1c00340c5441c0300000d13001c0c56210f40c0343e858003403851801d20550780c3c0e00c682010b0700c080c00c0583c0720000041c900070f881c0080540103244c980c0c0c4258151600300d800040e103c44400c000c1e2a02d5100c006182c03005030040d0007002c03009880c00d0f42800c03001d180c3c2000000c5c0002840c00c04914410059510141c2000701e94141c56074514114074440e0a00c04180c0c1081c40b820204044000103142144410f141442404a1741089000900010521a401500c0a40c4c4192242c0240f5681e1130034485900107940c0782c2c0850740710400d00490b25a0401180000c9083d984a80c03030305070301d80d5035503456490018055030040c054180318520700300011403240e148100b0389100e650b018200100c410b00035201c8100b840710f05a20a410094450607242c0050100005031404905001c0c0054032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 787202859 1250 787201609 787201627
    0xc010501151b03180302120c1509100e240c0f061005130617030c151501110a020402120702010b030d0f03091a0903041e050607020f060d050c 62
    0x680a0040c12440400c0042d400301c1c41090301009107040003603450305016070345251901604004500b030f9440a98882c141911034190b1100124400706241003c0f0317002c60300d06580701031280c502d000350109540c000c1e080880a10000e405074020503540e12009000c1e0968140c01d804c1461256195040c00da10440082404040d40d402084201e64500454010b442c0350300d00720807450000c080b548540c9128810380c44210f030000225902000c041d0544001e220b400b903100070742107903a036030106901c40c00032710541080d10144c034881c080080c0150050031842e941d805065004403048040c42038a03034081d002d860000f500682c0d5520003040309d100080100104d40c035200c040a4211418140f640c4d0094010f10449040140d0001803045042800c1c100060039200c1411721031102c1d2500f0070a034207818410000d00c12a040004041c10840f1445500182c11034020484040c50640a1181603000b9609200303420041c23804082c03620341058003510650408003120713170007070130b0b10015200c1040c144000542590 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 787204109 1250 787202859 787202879
    0x3070602030a090f080d0509010c120305010501020705030616031104120f030305010b0c1e031b070302100f02030f2514010b15071112030c06010602070f0b0d200c010501 74
    0x10044c005108070b000420302d400260354454483d018440708010002951101c5a80240d01c8510043e41100055411341000f01b0058000d040a00505015100c0c0000000e140d24000505034800d945894018103d20300407001035000c4e0005403440140e2500500c804034600c0600702d900b002c079901940804c61141d2450a0140480c2e5041c1c00000400c24100408400024002020781c180b2011081e4000d2000c0031144840c20340c019654041c00d40c03004120700140c0c4c484001120740c1602d0080340c1c2e0b041a41c54010341650031500000722080960024400c01a0320540200544031514020240c00344548802c490845031074000c05041701c0ca50b00d40c050300c05949409125541c10381100b0382d802a012500300d44c59007042c2c01040130080104400400c02d800d20b44441c12481c6080e241481140d440ea00c00f03102031313900c0314024068640148030380c003030015000d101880c098040f201540b21051030724071420010400340203428023205403110304011110030160071f030008002241c10600002403039410141201 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 787205359 1250 787204109 787204127
    0x815060a06111b0a09060b030108060702030c280b090105100911040909020303070c0602030703020c0f06040303080417180405010e07080609090f0607080403080609100b1803070602030a 81
    0x203010080700314000c03011054001030840c4038900329002c3c3d0601c0c2064500180d614402c03a000361160f00d05006000030500c190304090740c1030f40e041d60244c1d80c4640e1141004c90f50b03070003242c085080a03802003400c90100703e4900b03408600056003003682078810f107181d2580f030f03920201660420030307580d51801000042d200590412001d130602d4401813003d090380b511040c2c818081c0d4095022131548e240f1b01d40c8110f5400b00201d82d503450f0300100c10699143d03900c4001e0345a80104c201500903009080718440d15150a0b2110b44012200902c80c5041078111348040720f60f8a13004004803401150802c84040c8508010013400b00c1c440c0c0b1142c0c212100301ca606c1484103440040c0d200d40300368106070040c003d0340358102c441c050344040f0942c1c0c2500c030350fa01c81040c54640442142c1e1104c45000d000140424568400419485107010f925070f032006403a45401d00952480440d03818007c0b4582080621014103901d0092403050307014000d101c001c45041b030000b400e2410580c0b045005da0b2001501c1c815680c1c10020074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 787206609 1250 787205359 787205369
    0x1b1201080d0906120c11120301050a0b0309030d0f02130f0611340f091a010e03060c0315090a0603050c0d15020d020d090f0314090f10090815060a 64
    0xa0b00e9440d00d8000044d00000341c2288038088141c8035221034840d40d129610b504080790703002003113500150288003e912654802e004482c041c100e0180c01180b60300a403802c030780c010254180103514021101c105080201003442c1130100f0903400f04a01c010300101036400901900c10407111201d1185005000b40942d0001e000521180d004202c480c8224a49840c0c0e0140c81100c0004031140c01000781c202c040c0c0d40080b40c00c1044aa003100d080410390f00388035403045030038407114450244c4003052000199a003141407016954181e0142d400588152401409981c101020b07002c410403807c0801d001840400b070450b0410f80441e40d8070410810300008100c8104049001e440e1810442d4154a8a40e503001580e0800500b803034001408030300480e1290f048420106000208000d039100030710707120350700083c0341100f90005040c3c491041001c0d80400111a00a04000c002c0c021b03c903911030512a50b00c40001b051000c5c085070080005030001c062240755840f0740030300400743c11460074038100959500a9040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 787207859 1250 787206609 787206617
    0x10f0c050a080c16090501051804050666040b0a021002040303020c10050a0903020d020604030506070f0f050405060403061e0c030902031002120408031b1201080d 71
    0x2441010a4011481c0c5024540169200e40c0e241c0380c645400c4d1500800d80382c00080320111510000e000001d990105040c0c40d011907102e904605045130504074484292006801a003013003022910740020345111030500b003034003c1c044601128068041c2000c652410740c0e60480410900360024031030803860942403410001d4a400300402048414001c1406117004170344e00c410380000c29442c054020401c900310b04000c0e05040d95569101e03e40292a5100288005e004101c003004404145002e0070580f403400810342e4902c04514610380030010340010f901010b80c3c000340100b00100110302d042c01140e11412054860744140c0c041d0382340080000320404210002c016081c0402d001607642d03442101d02301c03a084540841c05810a400e60006080081d01409400d0301d0300100304001505508404410b43c004c40681c1c00000c0b41c400400140c1c410003070301001310407a5000060014400402440d04a5030800c1041000300390448102210303406000a5441d84280301c1c010062042d04001681c200160351170 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 787209109 1250 787207859 787207877
    0xb0f15041107020a17120c0307200909010605060d0c0c020310060f0e06211e010f0c090305210d050c0702040b06120109180515060f0102120d0b010903020618010f 71
    0xe60748450011041070100040050800300d072290410556400e40c0c1c0152b40c200c56070100c00c2c4036150102e00034000500807640030000074404101841070108444001d021300d450140400d4015008103481207000d414001790300c140300c001d80c50801c07030000c10034140c48000a61508003a22034009030f425521211140084008014107603e0b1542c1c11014044541c143d0b00d0415540c440c201c0c00c150f090800e03003210300800300c0c07a24105001500002900c0c14480301c20040503880b0311040700e03013010902015040d80e03c086011440b00503400c00303041c20003000303c070120b090012001e600340c00e49605940c565000c0101107640341c00c2d89014412103a8000c002c80750589040420040f40032825014030a80030f08541d10f00e1000301107800d8001154035a944882641c41c15824801c00d540c410b007040c1c42241c0a01d045500d0000f113540009802d0881d00d0000126034240210029190b01801034401c0d05410080d2a20300080180c4905020340071502503041c42d1640134042d9800101020a940c03c44001c101000c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 787210359 1250 787209109 787209149
    0x6070b0907090e0d0e060d0f09030305070809070317130b070f120e011b0201020f0d0201050a051006091514070510050609060d02040506060f04060c0309080a0b0f15041107020a 77
    0x5c10590705480702030b80c910740c861001a43c80402802407084482d11035042c0640b0104250b8036074031413440741c44d8644900c4202d0311a1040540e5a1499000003010600700300c01e065003114080002e0455504480d00c82c0c8442c41e10ba400c011402e42089500322240001c07080240100031452810300800c84080c5007881c500e02c21040020800490a100c42d4403c91409030701c1070559100f03001004007103000c0021124001003e490080c0240340c2151a03012252800010800101e82481007600312845aa280203040e4182880c81d210745450000c1c8c07005125840100000500340640075040c02c9010b14041c1528000040703403541a550010701d150310641d6041d0810045a544410292106805072800201a075503440403238807d10824621070b201d58404540050300381d5008030720820f128071a50322007050725030380c5034401e5071404001d000030001410b250000b01e0541c0013030100f50740103149620210720480d48801040880c2c0c00405800032804000805100758141441d06800800c40404a4075000500c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 787211609 1250 787210359 787210367
    0x290702071a03150f04180b0a05060f060c070503060f0403020f0705130c0203120a0c140906070b2205010e01201204030c0501151805071d06070b0907090e0d 68
    0x420040e40f540d512030000500303869140c070b078001100010f042000a52420f0b4120b015000381d0500441d4040002000039182d28114041ca90040d01c000c2d000e104006803c10400c107407500032250404207840f6180c80080d090342c3c20841180203107030b00c01c56660141002c2c1030090038000c81181c007040640c000001007141d0744030003003003800c100000705000941030b02408d4101c1c2075105862441401e40210401d12505a0b00350380f20300c80d01c9d0341b59150180c0c109140341060006004500e201c581c89003042c005140810316507000740c0d0f4082c20300d100d0341e110900f03a81894004804156800d5810360354400304540000024840c1d0075018022000750f4100c070500702034002052040070100000400d0303030b5010034100750049000340e100703d600000a102c20b00e451080f07030040460340e00c140c500d80b20103900000f546c1c1e5040d1007410b0082646544c1d0300000316800f41a40c1a0f14000305105800200810070b8001064908001c54012249a0042c0250034585404881601c1c58450109280d400c0989141055600 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 787212859 1250 787211609 787211611
    0x10f0920151b06040c14010801060e04021b010e071406040305030304140109021002101103010b1b1f0501081624032d140601020a080304290702071a03 66
    0xa5041c4007541c445050480848998030109042118452502800104120120b02006035110752400c81c50032042c03800111040c3d1002e00c1014041906c1c1c4280c4c04090500d1740040c07030503220040490801e030181e0301c401c500310303099074050505070742040900380100213030580c0b44a4075100403140c69080030b0a60301c41c113842e480003038001000d010080c0240d481c1d0740f0b0300390029440d094000302580e8070f4404070080a03440f107403040404644c0500d041000480001404141c9040e40c1c0c0c83c200c03260070260458608645047c8050107590248a1200d0750b610b908070ba0302001c10f080f9150400440c09516003c1018035110403a0503440d05c405440c0c1e070600088a408400c4400001200c3c40f602885000020030b40c010300b4106030071410300540e40004000000e00e03a248802089261204005500034100000400c840a0320303004d0041c0c10501210000c10400d50255400501944e00e07020505032140c80e9a00d500007100c1c0c96940130158008000302d8540501400c0010401082d04101c0c1d54905110355102e880 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 787214109 1250 787212859 787212889
    0xf0b07021f170711120c0c0604060917031c0c0c0615030c0504050f04030c0809040510050f01030b06030106052a0d0f02010203060a05270c09100201110921010f0920 72
    0x85d02180c0c07003400040c10040503000b1280500391a0b55161601c00041510030180100358841a1007030700c10180d80c4000040302c0c01459107003a8410003201000f14000548410300e10003042201d200c041d000070800502c240c0f0600400c046002980f40d2840c9400e01d10070b24284d0000d031040f031403d420400c1c40d121440b00587d000d90325203004012a412807a0074112400760030351041e080392612081020b0381d0640140a41510811a800d81d1a0031042004400f5642000f02a0f5040350050004004982c018000b034117000303a00320f841858014120f90003505611814210701e0440d032007030764043c031402e40048040040b000307248002e5185140110108129008a03c94280101e124a203210381c40d12888442c001c00059045403e038031410400603025143c0c004824051040b5241400e14048074014130404e2a02c0d4080c40742c003401c240c010420000c2c481c0d8000c00d011090800e0301d0342280003800078821135014880e14100000c8000c0c0ea814038401401400d141d64900c0c0910b21070501ea40d580d80356500040c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 787215359 1250 787214109 787214143
    0x503060129071509060e2d07080102070c030b07140415031b03240f051c020d05060f0c091e0604090c05040509100f0b07021f170711 58
    0x1200908411041e48985100034014505600d0520040310407a04840d031107900900090004003250112140c41c0d00c2190942180e07030701c1600000d116500011401c010102180c020780302003d5a0b0030742642a41e00c000001c840c040c40982c028010070452400542c1c010002d858220b120b00c51064a00c02c15101e180161034041c42e1b16541c5095080c880d8120490f0890356845100030f004d00d0003400740c050301919020210a42c8a80c14080500d640c0354070315021142002000c5008038584400d2011050010310801242401c1511110143e1175160b1007a000a110b540188418506030040842e5102c0107400c150903038104101425059507060030740c14040b64a060102520040f0800203001d1b48100e522924260b030400271090348050b00407004d003084503802d0310020100ea8036042000100c0c000c5c2d000b81a4206072420007808081d103814090921141301520107040c0314052024102040c50616800c0000b035034400f45c141d0031a16440c02642c0002c101d00700507000d07800c0c011616480300c0c41002030440301 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 787216609 1250 787215359 787215419
    0x2030f070c170d0908060c0909090a0c06200a021f090819020111060417210a1d010501081f110a050903070e0906070f030b0316090605030601 62
    0x10000c0c1103010780050038011400341d0511040301101d41c480304411140000b0910030200003420b000081072051065084504952400e00c4001c1048250751703000d0040ca55174400c10440a000135481c0301644060202a02d4001c03420340701e01c0b4035981d00905205480c0003900b0001c4044010380f5030391b06992480b00e071020b80e110800950042241c40d2001a4443c0442c0e01c156800904148000d80da0100c40c01c2c000ea80708109501c010741d00c2c43c1e40700c10980d0010806060303140c2400100000c10080c0c45044201e08000000c032410328400b1006100a40304c6910f010f070764075184405035054010840c0e458200c44001d021640c540f6488548405244a09034171442c27404492500804544d4040c088200c1d40d2164103031244d8524200070016044503007001c0c0240b0400b00089201040d524810340b04880400040008d0b80d103c040c11104d0010340f4080c0ca00b81038907224405903aa400b4024145100840c1c4000e20026180464080595826511580c0641c00c400c0043c0194098202c1c600d07031b091610100f030000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 787217859 1250 787216609 787216613
    0x15020d081312030b041802090c0705031303201e060306010c050111040f12080301030f080408011a041109010503060d240b0414061c021f020303040b09060702030f07 72
    0x8a00030760402032610300d041c504015060b0300740d0b004001a801c15a0708000300142820b60950800f40d15002a60090705240001c0790718070001b006142d003c0c030940513a8100183c0320411280000240c004a50311054044060003208250400d9801e0384800c032402e071071001241981d002140140ca20310350180c440040000c3d84e590044d800801704e80d90103c0204448031200400182c00d800c18050b104203c0c80f01340d4000703100140d41035041d10298101e07480030b2941e465940d0300310190000c0441118168018400090100800e2054064a0039845464900480c9010400c0308a504502d4042801017082c0560b040036607000c01501d5110300c06447ea01c00498440c1443c0340300560a40360f0141c1048040c1c1d084104082c140c006120b1220241d07400e10002004c01c00a9001c10001c540468100400c45154070044088100c08690342d030028011800304050740d00881c002c29012411040507910000071b000420214055642d400b96501000d0601c50074419002900c9e0711810071009004000490202c003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 787219109 1250 787217859 787217881
    0xc0313030f090506070c090e030406050d021608030f06030f0105100e04170f0c1501050f0108041b060f11060403020a080309010b0d152301091503171315020d08 70
    0x80c0c480200740790303103500040c1b80c1070381d146401d8015000e450b030420700e1400c0c201e4000801c0c1c84c00c0e00d4181c0c44940c104007140080e82d009400000d6412103014200c03103480c3c08035400030000d42c0164410301a03007080749480d10070b051502034091100c40c0241e25240401c40342880c440c0b090410741e10704a0041d4410b41385c81c184041c002e107412000040340317180080c150f14000c540100904406030303031400ba9035113644d54807a010707140b010900c126600011780d17616078081503101c2c104550b803291040e00705917410038210750a81d80180e01a0811400b10340041d240e18560764114000c444030005c404002c000c285410b07075000f511801400d070000c00e40c4d031001c00840c8030840c007034100002846d400303400d107880c88500c2c1c105000e900c084400600d038050301e1314812030382c22015154101c0f0300f500481400074050b481c08a03990018144044036540d1a00c0d00072020000541c80c00b8031281c20f40c443c0d18039985603403000d002e07102c00c0c0140754042007080c0740301e2154024a6401044015072041c00d4246400ea0f0740d1078000110b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 787220359 1250 787219109 787219127
    0x60519321c080a0e1507030e1c1407090e120406050313060c02070510020118081305090c0d1d2a130608010c022d1e060f0c0313030f 58
    0x10a12040895148900f5070300c040600300400003150991034417a0f00e000524070a118240c00500050081c1000880b41c0c20468041c08a45030310b81d081308004080c81c0c6a2003c07020148000c00044d801c410320820000c000340c050043e04400030310152140044540e0b81c0c1e00c56208500c1140309000f4084002501c0100170748040c1c1106400c00c0f402e2224160b00381c00291070740c98a029071485041103442200056105105100180020b600601d03c41e00c09501c0781c3d2400e4005070f9904405110b400b50205194507040b410901038500c5620854a070219482a9016078090386501101d071425419801c01030007000580c405c103510402d107640c0700100300a01f07407018002c02303603010380c1c000405044200c0d52b009241d108904540240000300808402c200341240c0310105d01d8104003120110780d58000d501c08800c05800402102c5000700c54030540d5103903a20188050303460202e2402e41041041000041004a015038400310801c2c00c546103107440a27004c1000507a030180035040010034095120f40c2c60044003a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 787221609 1250 787220359 787220363
    0x51e270703030305010312030e0c190801060b07061404020612060f04050c070b0115020d11030c0a050a1e031403061201050a06032603010b030901060519321c 69
    0x80c0d6182901c905014000c0c0400b03200491301c44d0b50307400f10091880e1103031007201100c1101c0310140c03485d4612401003100011007141e2041c903140c80100000f850325024800c0c4001451441000e9855100031701f480342c2154803031144402004090010080144d81d9072040700d030040700100d48440f19440e44c2001c1046080d4030a13060f90400d190078140040940084060000e007841000314035985d0b82c0314161800b4822030b400b4113002590064203501c0440c0c1c01417500001c1105078504a03400c0c241d49907182c610300080c10100707803129080907100c0420300151290300c0c0e4280b003802d91034200d441c03a40d0381c1c01003210340d420003810307110308010000c10b41c1d0380d50340c3d210f0701c0e410002d47c2c0003030009040600c00754005022a10040744c40c20900140100405008650040d8450004017203c0c196840c04103c50707800e40c07004011094a55845c2400b00d201da41c4e0802000d50041d01d0980c000e820750404200c0008203001d52911514100c021041d00900f4514a840d10783c558015105c42d2820381542078132102901e000800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 787222859 1250 787221609 787221613
    0x6170912070b182a040b15070c0902030f180102270307080f060a1d10020307090605070c0b0a050d1107020a151d0f0303031603051e27 59
    0x604144501008403902981c04480380e020011403c0300d245565940e03440303900007030000c59048101c58200c0400052031611000d0400f1490b41202c3c40060701011300b081c49140c03408404581402400480004c5602514003103030114030b0350404c40c88016031322200130402140c2014142c0c0080c1020000c0d01030b2a0902c0707a1000003503039000301c00e80000c074110490040314024400d1000000f90703104006600b00560509001401c804c2e20341c469070b0000340403025150b5440103c46030002c03200700010000381d407034001e01d007000613200d00344000b0080406040d07504c000c08015040c0030030b0021800e02c0c03000d030782118203103031000c0c3d030f540100c1c070090b11503004450643d802203180520741442c4107004001002a5842162a030780100d8840e500040e40100568000c0001002c50100704000e030704040800c00c5208004001c2540500e07400002440d5a200715480c1007501c8a4214a112482c1c06009264002030103071080c00904114061700544000010304210784500c81c0c04800022102201ca0990404002d000f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 787224109 1250 787222859 787222867
    0x60a08070b031803280c0807110f031002070201020c040b06030a050a0b040903020318241315110706050408120d060b0403050a111e0d0501110a0207031b06170912 71
    0x107058540b00e0240c1c100303c5400545e00e400f851031900c0b070b46540b840d80d130744510703041c0c2005003c0c1c80f42c1070302c1000b070411150003448585100d01140c0c1c08020080b0031170140d0b04050781c0c03240640b000904025066403050701503401c05880401c00d503030f141d00341d0354070a040d0500000c1981c2d0b0110a00050258001d40c26001032605c06080305240d408002090f440108a4074000304109110900845400c44e03080d8041c452308800b211645070490718001d0020324a0321054000303c0e52034142c1c200326000240c9a0030041102800e0a10007a0001d0000b0b10003001c960900c03c2c14189410a400d44400307400d01c00404000700001c4070801d030080c81c0c0c0580050121061070903150b9403289440396071011411001d59082e00355860b407180c1c80c030b0318003c02c00d01c0644880d040d1107014407100034099104181041100c2e9552510240864001d11001a20f04690305500600b2018a1814011014040c1c80101c04600c040c60400380980798110066101000c50304844a801d583ca202510b810712409610070b00242100003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 787225359 1250 787224109 787224127
    0x50409060b04150f08210f07080d02040e0a0e10150807260703030c1103010b180601120b0901030b0c0c06071e02011a010806040f061805060a08070b031803 68
    0x10040406072031307072041d21580c40c50311030304502d95600321402140404401003000e41d50400baa00054a4807030350f405559814414150340f400d881c0e82020003c161615400b160070400c8a216254154100a0b80c140400c41e07810105030290321075403040f0280300220303140d41a1035000c840c090f41d018020300c002d0080d04e108035103505160090314451040310364003a082c9040100c0410000c507100040341c1e40354540030390a4241342e442001d034000440541d90300d556508008000340e210400c3c11456020302c00340007031051034800005082c0c02558080050401d1034001c2c83e08040e02c2d410111f0341900c1e0031140c140410740d2214000c2d4514815004501d4040c024801402201a00141c448a10184c2d86409481c5104041d10407401c0303885002c0b68070310021003440c0010065005080c0903803c240d0203031001c1905c000701e50040003954942da00c101d03074446685810100d12001881540c2d00410200c0f141100a850605490360300c001078000c82c0c50203080017011070140d112604003044038484400540e0749807400b0b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 787226609 1250 787225359 787225391
    0x207062102190801050910030308101214060c07080403020d1e110a0e091c03150f090b011e0f0203090a1202030c040219200f160b09010801050409060b04 67
    0x8500b50400710303181400101d25840c001000307138840c031882c80443c103c0501d1928222104000030b000c4a80340e09a002010411000ca60041241c8500030181549508928410649402001007100d40d004205100080010304000119412280c04444c0e640c51b5040e01d04281c000d014000da0100411402a1580c40421000600341500060103d422560b981d68620101000702c004907210342c855001080c085001c0405407050107559009490000f400740d1404040352074044854000142c00000408104190056802008540344003843c100300c1280c440203040d803400115080040c01c5c020002038151601c2d1013041501c0c815907000340508005540d40702c101d403220710140c03010790180c0100304840600b41018000c480b404001c1c0c8a07900a0040501c20480b406201c4044012025210000c00701400340c0400c0003251f000500c001030454081c20907a113405c40e02a07507101d44210395007030080342460380c0c04c60311450440301e00f075034081202e080742e1030070700e00070448250810f9010740b80102d410030300559 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 787227859 1250 787226609 787226647
    0x3100507080f0a0603030c060f110f0d0f0c020c0108151503091b03031e0702030a0302010c1b030206060103180b2e050d0f0302030f040b0304020103060b0a0207062102 73
    0x20200c2d400306a44448501c00107a4000307000c040d0110b8105801e54002032415032001d40f031074a01000015001e81011400542036115401c2c0100505008c202d51200c4a0305110349060034207510810080500ca031107003c3d4841525081e060b05019000c00020140e128003400b054600900800001000e0f17000c1a1459544c0c00c1511552090311844010104c04407410008140d00c2d0f5004004600b01a841d480c60031a9040d10315006001c96802d114210050b00c080000d54601031282e0004240032a000340e004080c088122803000660340099502004a600800c41c990062021302c4c0c00b10f0042c4209020440c202d085050040c50203e0601c20802002740d0b02526000303900464501081d0350007041005c07a10b508003401210391003250440c940c0c0000d1310301820f041c400351290041c0c0e07042084400c6034402a42080e802000c0a290000422046607810b100350005428460610b50401c52144402903498009010312024800c40742d400c48600d100361450051983d000080c25075941620f03c0c6040c13800c5070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 787229109 1250 787227859 787227871
    0xe03041a0403060b0d0c14010e0d0b0f091f050a0e03070f030909140c07050a0b16080601050415120b1504030b0c120c0a090e010308091306050a050105090310050708 72
    0x114015100d40c0382d1410000c1d1101d80c5170445a058641400c280760b031000c07d000300c041d20b411301003880c80104050f16400e038081e030841c0c01030728114094030789810422041e20008201c00c6076074001d5600468a010512211003c44e405d91030001450307603130840b08000400800079080b41a2001040342020054610a000f001350b10030768511800d143c2e950b2117042030b16201500a0603090811002810104941001d401914000c008032100c2071161340b200c940950742500e20b075900154000e002c840080d0444451030b003080080c40c2140c030b003e02d0040c0217148400029001010446818002244c0304143d420912040d100280042050303280101a18541c0c0c5c8a440700b140c00c001c0d047c0004503d4000782c0d050b50900807207a0144181e0f542c941c00d282405510400c0340b0014003181c160302040f40e010303004945029600c43c00348950396404140401c04004c04045014000505024083c412a02c6414000c4112802801c2c210b4485007c180003e0070440400513800915150504000300e0315402115680512 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 787230215 1106 787229109 787229111
    0x501080a060f0207230c060304020108040308090f010507050a02160f0b070f0606060e04050906070906051e0a08180615270103080c1b10030e03041a040306 68
    0xa0300f0004260304610040c0005c002041e41000000f0a61204071102415441c040d40002c1103200c00400050811100c200030894020040040c000350a240c031000303008a1502d160014020380044446800510039030310008681d036541e00f1103205442402e03907040300b50382c03c000302e01c4c032143d00c4500c0c1150a0418000381c0c1d80841d400d8441c0c180030b080390b507644111901c142410401641c00c085c05528250b0000e42c140300c541608840140c1c02c450150500c1c6032202901085400c05e40300d103180c00714494400041102005910403240ca21615001c0b919240c044c884000c000e58803801191981244a90032601d4450351804542000000344108403903440308444800000e000c100070b0b40304603407411000c0303001c038101102804031929001d0204e80181c0645450720006149980c1c0d5040c50f070a0580e9050a08084c0409008071005402c2081960582e86c074810940d040540c081e1105440c41 = true := by decide +kernel

theorem cover : BRFrame.Cov 787050359 787230215 := by
  have h0 := BRFrame.cov_init 787050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 787050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 787050359 ≤ n) (h2 : n < 787230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
