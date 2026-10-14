-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0881
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:25:27.403777+00:00
-- url     : https://prove2.me/submissions/a24ddb52-34b5-4bde-b6f2-ed77ce0d1e62

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 158273381 ≤ n < 158453237 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 158274631 1250 158273381 158273389
    0x301020703080115020c03010c05030f060a08100f0603020307031202071a030408070f02030a060509010e0105060d020609120303070302030403120e150c04050901080c0108071b0314070f050c04051005 87
    0xc1c0c11100150707000101380d140060181d041100c4001c0f80c580c154600349034000303201d4100000c0e40c090101d02c3c500180a68404052000f0a54503002c0c0281e258012014040c075200b10342c0043d40251440140804c2e4141c2c0d9502291402155406c22202d019941000d00560355040241e20010700001c0840c2c4040c44d0003d0303110b400e5100107480640002800101c00c800e200511901d850794580c081e08550300c1d04000d041040c02481c0c15030344042c6079402d01401d40744002d414019107000713050042640080c0052a0708000c170030740c04064a15001070349200940341226041c4042c5100b004035880142c2e032032a081c80c0044c201034024156402e614904001c200f490000007a003420700c1203c404006120741c0f18050900454007565100c00d40c084515800481c0c00c0714041401040800c1c00e03201d04445849022094400c0c00d58440e07a10219200700e000540070030700c244107009036084907488242c0b070040c107900d4a44442003076070701c00c1c0e4640e03001c2008415641040c0c030600e58801d98070b813103240384241040002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 158275881 1250 158274631 158274647
    0x10e01030f020111030c0c10050c070b031f081b0406030b06090703061a04030515010605030c03040c05060324010503070c060b04240f050103060f05060a1107060216050301020703 78
    0x361030003104038200700c1164002c14001d031100b6100c508482c0c9400c0301060a5541e55040f00d1902e000c1c43d4915002030f4030a000e041034038921a409005071400a0821103032952a0700010148080450001140403074001c205401e58044e29551019000c004425104282c0c03e000003401c2c01d0142e46410360402c0410b40103120356410490031640c0f0304540c2c40b040400c8018280c140c11001411009004072034581d00041c0041c81240e12800683d50914881c0f00c203640c846e0000d204010110300304000095000054030004c1d07074018450714440c0000742c5c5440101e005034104840350034802d003d800b000c82c00c141094225010740042441c06a14524000c0380080040d40102e9006140c4e5803540c841083c02e03511a0409205514018406203540c144100c0c0614a802c85120b26402d2034034032240854503500c01d00038101034990071950840054901401c0c03005540c41104800104508500d0b08842030740c0c28040f5030000d0100758014110f0101c003804151160480e544100d109a104000ca140000c1c0c0203422 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 158277131 1250 158275881 158275883
    0x6080a0b0d02100f170907051806060301170a080406051803010c1218120906080c2a011508010209030f0102090f091306020a05190f08040b0717040c091103010e0103 72
    0x4101309141c0c030b0100740e07181c0c003d21042460a1000d0410000010030000c1d526044910403200e000c8503c00c031084444180350b06484c940c0e0001e83c1000144201c8120030440311f900b00100701218a119103546907202ca42e0416002030000400000e543c02214442103407440b0b4111b400c030000c208410024038098080058107115074181515219490301c25210305070306aa80a810450800030030680703100044c0903c1060141c00045802030010500841d5668141c03103200ba01e8400e42035000440c081503010101c2e561210034120342d00c45a0038404480100e008100502042c030000d615801004201818828000781d8442240c0c41840038042030f0385d5085880c804045c00703031006803050300c60342e82c248410720000034082c04a600015180f1842c991100041c688010030006100083d0380b201ca08940d9a04111461000210344002040126862600d20354009905003820202da481d8400030301501c4908442c00e80300790200810400c541841806a0050b0604110b052880e42d8141440c1069a61041c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 158278381 1250 158277131 158277137
    0xf07151b062d0504051c090e10090216021311030402060703110a0f11010e18060f1903022106010b0715050a090c0b0a0f0c051606080a0b0d0210 63
    0x181d409625024035074200c460020002510101c003220b0030811010740000d460441c3ca0f4401c030103040b03102440032140104c1480b050ba0303c01401d02e00c1c04054140703036400a0301c0c81100166441c000036a030b0505100405000400c4144041f81000d18010048410740036040d00d59200d09042072a400030310340d032040782d40c130030381c104c4805440c0d0005080443d0031a0780d400070b4441c82e101e903000000900c5200085c00704070310302c00d21000720011070681c01100d040d000340d21440e801281401002d14919480080c0c941c0c00240039203110079182446000400c118058141141c2e003a42c948010710550800140040c0d5181e895403070014900f4104412641d5000c051140c5c2c1071000b03001c604401008a240d010155120100d5030601c42810300c0d218210040000100c110307110340c441000001c900014505413408402e0b20307121080c050b240d150b0107441001d0000002c4a4074011405c00300c1c0010142c0346503038084c0800ba41c51501a14210201c001251a07280301c4070312034440b000c00f800c0143d68000f07501805104510f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 158279631 1250 158278381 158278391
    0x170c03060f01060905121002161104060b031602010b0916031406030a12020709090605060f030d0207050d0c030204090303021c090b0c1605060403050a1209020d020607030507050f07151b06 82
    0x3040c3d09154100c90025503480c00022841011414414041c81160141d4600d0300d0392ba1a220800007192014410800025000e200090f0008100d401301d40b81051103000104481071b03c1c1e0006980413104407845444204094000d860701c9a25204161111170848a101200c0c01c0c06800280d8070a00480003e002009009080008170310903c40c00707009008660301400f10004a00c2c11001405c81140c40f14091000a40241c445150025841c09010502d40107445a9070902040c8540a4258401903501400c03d070000130060300c40b8800c0d0500e490099400580315014100340c00035a12190301c0507500f0f982030440750404100d40c0c058a0b500301040741c03111961608441e1140c0e241c40500d002c01740c82c50050303004000626400c0401010301d8142a6904405030403547c201f60121000840301079040307540100c440c801820a00000c1c2029406420401c0c20f1541507034419261000a044405098004880800c15070300c000000301135905580c02c045510600386000c0106581c213044024007404d480e4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 158280881 1250 158279631 158279659
    0x70b0909090312040c0905060d021806011112030a1b0801180b180f0a0908031b12010807210302060708040809060f030414030403081210170c03060f01060905 69
    0x4004803510816083d50441c180d2605051110741c50410348136521072642804005440d42c40c0500300000345541c0180342e40d4882c0d41c400d1410714003001c003c042c0c0303042c0328980c0d40c84159208108000c294094041c1d903000d40c0d914082c20348000340e034840e06048161340da0500d40e855040e90803580c042c0c103444074081440d02e2854214003020281c58030301d00b480d8001e120410312030484540c1c83c071514401c1c0d0710a01100c01603281c2d404803c0c120b903101c0d100940540c00034400303c2c00e40d00c42d00309000c1032850b2042c5014109201c6416107c4007000a07400014035500501042066244803071306c112031000280c07110807130355a46c0c0d20301a40303882000300401c0c1088020000030b0b04005418013074820f04070303002d020247c8640e20414003a0f80d990064805440328012103060400ca100e00004940039240d01c400c040d82003001e24030520882c10406031103424428203224000c51308002185180805600082c0140120f00140d000d05003441400346c42c501921032845d00520a81c1c2d0442c01c08401c64405880000c10400301e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 158282131 1250 158280881 158280883
    0x11e05090c0d0510061406070206070c1710051506040608060d05030d0c0201060f03020a060810090504060b041b0801060e01051314030d0201020307090b030603030c072402070b090909 80
    0xc0001e0466020003014548010722000003100da00103c5200d00400040e40c551280889859001d0341542e805241000b800006040c10380103018502e20403560400c14980314100b0820700d44098100c3c00700c1b584102c41c600e4560006000795a006403480251016420b18200030688600c640d020350020300000d00c002ca061900d8548142030044e4100c0e0a6030707110007150702c5c0c5078041c1681100071030041d07080000205040d042011503100b141d9000300144480340c41c01409a441d101d0083c0071484022100d000001e4184072801428407a500ca5080001c12450b6401040b00300d81200f600c0e04c00003540c0d005100101600145a1419140350b03050005007034801c0b8004072800e2040c00304456421100c2c80340090003a80c0c031400c00b1000c80046003941c11404402e0412402c030b00007251404005814880c0070030044522400454000d41c0c040c4c141ca141c100034402040c030b418402d40c45903600c40e0300c1549005180f0380c0700c482c1d180031031814030141c0101c4e858102d2140c0c0f907006040c0308510030043d581c0460a1007070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 158283381 1250 158282131 158282143
    0xc0204110732060621160305070f0e06090402062b050907060c0b0c030618130204050108030a0806150417060702010c050306091b04090908180102011e0509 68
    0x3901c2042d5200340d001600030007004400b9000c4162008070322001800c0c0442c00400c1040c400c00d006803200c20051084644030300559100950840c845c0604000c0000644044000d24041d50284005080740c51801c1c0e250781c1c05460b60b0b4000c1d245806540c0a1007400e5541840d42740e0000d030115211612001302c404081d03400401d98211760348560710602c100c0b9959103550880c511812544081d902810b640700f500b03070f4001800c0f03c0020b06204000002400301c600541c007541c1c12140c090030012607409174050542a401040c3c82d58080c507110481707032000310301d0980a100e014006503c061400e02003000c80141c034240015040c1c0b84103503000b402c5400030824410558000f84040d000750801ea0010088180c1c1b55082559107000550810005e46581d80c001c1c022240280006000c0941c95500c0403010754107a001205448900740d800c120004000c4401c0c015a4289402406ca00c0d9036001c603258680602c0440040407410740e414202c007002005600d007003140c6404003521011034540d6400d1071490a140c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 158284631 1250 158283381 158283383
    0x4141009030e130216061b14070b040c05150c0d1b02010e0f030105012705060d080309070b0a050a030e0a0503090108090a120816080603030d0f0b060406020d021209010c02041107 78
    0x5685e11501409200c0543c001019070b1f010181650204002d001c422100d00b1144201c210501c0000c2000d00c00158400a8103507001380542c6c82c1d0000e042d10790001400c120240140d0b94811403000c10b091243c000280b0002c000340900d414595034940010b41d442c203442840380000707070501c5802101d0b031140da11000d20700500300b40018007c0002e503031a6500e10100c90100e110440c20504e0804079007014070954881c42c0e014160080c030800d0b000355a6640e160240d80000c010150074062601d0014000d00e240b0080c114200c110b0312982e4441c805400010704a452060445040b64004c0b55a1804034001004036a82c0c901c003860903080c3d07965551882c514000441c440100308000303c0748840b29281e1702080c0c1c213015030382c8a00300340e5440c1d07460b03030302115000020745000b58503400800090744001d40c542e01c9102002e281303003008140441c03060002403807504294000e0001d40c229512a000081e414080f1000c601071320443c45007000c1406000910700e29a451f070003401240da40c15502503098507101030300d07441b03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 158285881 1250 158284631 158284657
    0x50a0b031c050d02090307030b040308010e060f06180d05060118052205070b040906171c03050603010906050f040b0916030314090910030c0602010605030613020a0e04141009030e1302 80
    0x1155249050527403140125070a070b000450b80e80020824880341c08a081c000c1034018440001c0000110410103564072091031042c884281182d400c00a8444d520140c08090007480680b031950b15000c50000034944071100c40c540946004200031414250340c4d5100a001c040304c00030072030040f203440d0207850b21400384c108107a0b010000c00e00155400c0e8540102090380c501800d180c1032201c0720b4141c2d51f030310102d1001850301e0b01102c5805114a070f2095000c05e5100e03c008002081e180e5040e1640c1c403c40f031050301e03032603d224000d0040101f40b00c0c051956503000005000184956000580c0400c03070700c1c204e40401800c03c54020300d00040000d270300c01038440c0d03100d0003403e1310150b0401002d04000d1000c0c901c8126804040306031300041085c01032052004484029020300700702da560a105804440c4548022640503000981c04100003440c929114800c03442994002c900104000290745003071b00911b1000b0000781090024000640c0c42201010f8042e030a842d0018039a2048031202d0103800313150300d040e0350 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 158287131 1250 158285881 158285893
    0xe060d0c0e100501030b010203180429030c0a0e01030305090a090c0c150e03040e04020a0f0b0a020601090b1c050c030319090e0c07120c02090a050a0b031c050d020903 73
    0x4654000212540680300400902d00d01c0b95a0700015020349080306909030158109010704410300000750704915114000410005e00842c41c0c00e54a042503c00c0800d0307940007400303251003a2442c04c0801041c0c0c2100300c02c44003900341da03203050f01b21207007101305010041c01c104000c84c03440c9158071041d0407803014210440046c420b0091068005140840020b016104441c2414007034240101610070b000101a00074065403504e400c0026450a00101510880e0016583c07000081c0712500b440c241c1b4041c0200c5a9403955449600304000d1030018180c202c01550b51a0148600700350f03071401840e14950012490b070080c9280d007818401d060105941002d50540000114078000c0201d21400f100d40701c14945a90418540b144580c0411010484960b007a88074100512404202c04c91403400b260521450071643c44051603001c0350003943c05503119a03002d07446000303005011200c1c2c0a101c0c3d203094182c00801d0314490042c2640590b2036071401000510074001908000303284180c0449201c920050100c41c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 158288381 1250 158287131 158287139
    0x616060908031302011209081e1c05040309150e09040203010b041401062006060607020607050a060f0b0d031215080a0f1205040b0a0f05120a09140d0503010e060d0c 72
    0xa0b800c0701c001004c0740001c098280c02c61080c80e1900c260000d65822060383c60908194a0020f9030640c9400402c0e0700840c03041c0b0ad10907815020030800d180a8007178030400f00b03507424030b460301070820f11007904074120381112595120201c80d03010300d641003080802c0b10a45829246d900200307004003080c906c96900141850070350b440d00000c040d00c0318100c8a480d40c41403001c0100d5134200c00c0b8046074604003900ca8110002058851030500040e20032180001d0502c1c0c41c0c009d0f10340d14180f82c501c0803c0100c0340141c441c14003050210092280c4141154103a40880d044101664010003a01151103001e541594440c0c20107414120420b04038040c060140454404000504040401e03200b111022036282040304020b894030740c4140140d80c01c0b0f4070030040f410304118125906a64150600ea800030412a09100084030305140745511809500104e600045000b03c1c1d04105a0200105110340ca2a612040450310026446811641182d000d000141e482e520f8407800034505000c0e000029260742c0c410f5001003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 158289631 1250 158288381 158288401
    0xc0c0503030708090d02010b010915200703051c0215090102270a0603140a0c021c03150501080105180604020c01020a0203210c121b0a03060e06040b061606090803 71
    0x44d0007104c1000448801e100f810b1401c034282d0b030181501d54006001d0300020452040401c01c0e0a60b40c1601e070425055403061450f40e100714100176208002e0702ea0240b6030030400d000b070900035103181c4040e48100d0300030192042e4001e03549071405981040404429030000d02914000e50588041082c90b80002200b444203201d921000e29840d11003e01c14240c68000055040c02885051203607011020b410580d5900c030007551008040503105141903000b21080d0b80002d0402010308d803e0300d5a03948002408a0340158621840e0f003440e0802414803c000c40107008070359908003508200d010f00d9501d41c206543c0c01001c41d02034002d001d04001d4641c000b00301e00743c401e600880076044003003180b0607400607126103035464a080c6506413405900d40c1002c022608a9425841c2459448010380f80c00702c0309030104012501080d800f800702980000d507942d01c2400807a041d2080550071070821502800b00c50070b03010000343c65224105144078032800c0c5007011410440590001d0405079046241c950b00c82c600940c00c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 158290881 1250 158289631 158289647
    0xf0603060f0504050a020d06020d091202010c1701090b0402161118070c021017010e010801060e01030203030f130b03010305070e010e2e0b03010b1e0705030d0c0c05030307 75
    0x111059800c1040154480c0c0551040500c19038000c13008040c803007116001c0c032081040103641030765096000c100541c550070581c0101011036228072100c215001035000001d0844a01b001004200088404103030074080d8081c030501e041d150f9070800080c10640b440300083c024450094241c54402801d2082024000c00425007841080c1c05e03100c0c00100700c500c49046404c000c0455029002c00c4081c0e00c101d01500740701c1903500100c0302c07030305090b82d40c2c5030b4031000411400c0090380614030b80080c420050002c6031080c0988c20040c0403906480040e541150700281c1c0324081c81c0f501d60b40c04180403038501105a4003040740740007082d0720f402d426907958403800e005440c0e4800703002d1480c2d001d40640c00016001c0011440600c55450b00812045400015205808441d0a124500d8100151100100d015042c1200560081c101c00304010350700c1c800340d5010180c000716542203002001003440070201144010040b55010026000e000a00000314002600d0300715070320001411501c404401c1064040c0c00102c0703 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 158292131 1250 158290881 158290883
    0x403060e0c0103270809060f030a1b020f07050909010b0d08090405010b070206071202010b1003060503010b1903060b0112060306090314190e042307140a0504060807020c03010f0603 79
    0x810701500e4500b404c00801c501c0c002c4402c10500748150303010000b03e03030045c0181a800400170301e07042c035001c04000401b5a58100740c4070a840d02e951442440c0300c640c0e003500c03218907680c02e5002030968500001540c94540125109980c083c0e0309900004030b00d00001e5000050010000300720010340d5420f4288405141c11800da424010b92a10002158101801c0251406154010031a51410400f43c3c1d030344c1d540c444844901000d40d034940911402c1a03036411404c0861800350346e800505546001c0800d03003991242207401d030107240d07039406200242c01c50f2000e0b070003a01e402c0500815400030746e50048414210039012060940d03d013500100401c16542c0240000c0f6000c1c0d5a240a84401d110b0610410320408200c5220b522071841d0b8040d84074090f01c815403024500400c0003510582511110b40c2c0d0022043d210054a8103a808120340340b50412041d480c0c000308018160f00344001e03400050210322a0303020700410302c00c0076000207211306e1080008030404100640281f00c031111001002010b8507031408 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 158293381 1250 158292131 158292137
    0x6080a0803040b2404020d060302040f0b150906030f1e240102010507050d090219030606060f0305151e041b0905041107030f051b100f05060f0906060403060e0c01 71
    0x11132a00308050315015841014040e032150030300072080c00c000003944003c400302c0646843d00c0002015907030718410b4030f6904003c21000728185c3c0300032040000380a218201e203a2070768400e00100b296505c0350030549a102c2c1d25104000d2a0f51254001500da074079404044442c0c0500e00b108002d021030502002407017408440c0140040c41440200582c03c1ea8421140352002440501c84802000d00c140c00807045a8006852018001d07a405180040085a5001522460f407141420449990300a606088481140ca000c0009041244085828509505209100f81d412007508441c0d05250554030003101310007001004001510b07002201521480742d0b81001151001400060301e08017402220304182614038400d150210640d000e441d0203240304070043c1000b406101c410200d1840419125540101c8030080403075803045d000d0b2000795040c004031608210304142c28841030743c50b0486449442c0500b00d0304403000e03a89880120f2602d02550b440076098508008482900b00c01c007050070810b00e4820380e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 158294631 1250 158293381 158293403
    0xa0f0813060807020c10110703080a02060903180915190e01120c09110c0d02060108061b0d0f0219080103050d0f08010603020d06030c090209011106011a0c0106080a080304 75
    0x2440c15200144121803c0340503820100700e82c149440d0074542ca20171115075003000c220800c84040c00510b800f0140d00300b1590180c00042001c282e41d01046010391102166000754609100540c44071030b071403141c0384100d000e5483c1c0300c04030f12802c06003400d819405801426060f480e0a80a100c0b8505c83c20610031a40c8079592280041510071950300a4042c041e04070301140c182a103418001c074010101400000d20460003400110708404007444084030b03285041d8020400b03541048500b500300b24015100400d604461442140c01505074410382d00941a5001c00188130700300500d21a0292044003003032201040009901c0444941104640e81a41d0040044990041c50564281c1c6c001445007204030108000000401083d486031b0014594444440740211740203560341d982c1c445006d200e4009026468002ca01100d15580c440c043c01b2201e034208006000c95403404201c00708148801d081d240710081e0002e003a0910807400d4010030000d00c650000c51352103080a051145080d00705507402c80d4903440342 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 158295881 1250 158294631 158294639
    0x61a04020a0c021206091203040218010308190e0d030e0a05120a03020c04020c06010e07020a020303070c08190c0504020a03020f03010306050106110d0807120f0e060910050c07060504050a0f0813 85
    0x81c5c0c0f503204071041030083c81c030900c80624003007098000400c01c90380440e42c0325803d410b08a101d10020b00861007001c2161300c5804010840080484c800d08040c2000f0502a200e4082e60340c055800300d100742c01d810460440c103440000b207111200c1941215070845001c01c00c100c6580d0000401d003684500030360036111034141034400c000c1079115140b2040c9841e0b20002c01400000ea03c400d80f00d8014403c1e004403500000c1641c0840e085422400f01603510941c44102000f1441c0709110038180c9600b4060340c00b4240049903580e42000f03099003c1c20303003d1607000c40c11030740b254001ea048502100c1c120154589941e96854564068070090148000085c24007811341c1c450f07000050540140b5000b511001c0da240e4810b1422a0440030809800c0c1c4595218190a00c43c200c040c85801c20402a0038080d0030700e89840555070b881c100c10104c21030141441d000030404040280303026034000070341c0107030041080d03102e9003012071030b200c010795018008120103102d140400001000504442c20b6080c9040045959 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 158297131 1250 158295881 158295883
    0x703141807081209100c2001090509060d081c09060b100815041a0904030c110a21030e090901020d050f04080a030b24040f080606030a061a04020a0c0212 67
    0x3ea0700c0f485451840601062045240002d07001d2620a0507107492004c4c0c120703035102d00036085400007200882e0380032000081102c0d60700c942e807080a040142c41d00760160a01c1d41c0411000f00d080c45002d030512002162020300c0071108401100003080c1c250302405103001908020004050540fa45441200100404e0000e980600c4800707101d42c3c10441c4150310240003800b44009030a12001b0461508514a00e514203a034a0300c00c4240114007030342c2d5004403506107182003160a451820001d12500e42603400700408004540d858600c0203075203041050381012803500b990050340c0c070001c0c150302020560400c404a007056025002801907803c0506c080d0b107034010411100101a43d01814001c8100400300c48a070107030f0450307aa4241c2c0985800e1040c4408001c80020396030300c10700c004424100040821942402103904405490704201130000f600b00500040d50314481e2003802000c6540760311030340ba141c41d1014095595402c000d4001e655a04018000030408441640704920030000c101c282401b401e8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 158298381 1250 158297131 158297143
    0x3010606120e0703060f0f0f021303200306042a0302010e0607020a09110d05060330040b120610090305060c16020301060b0702030601170303060108070314180708 71
    0x340d1106011900c0d0400c1e030401409210300d22040d10300c2010070000c00100b0b00e106900000b101c1c2640090403003000d07071400080d91034038110440500c0c014001040300c106041000800c03240c1c807020040940c1c1038440141d5900f00b80d41c801540c18040c050411080c0440c3e082d490a10451070038041d0640f2410a0740301c031401856000107400560018001080d0b07080c000020038030300b400101038800040d660081d40e0290f90317034009440300c5030300d0228500b580030003c0e0240365044101103018141d1000e0300c00c110380b448490990070410340c180c1245407a8018044500300c4000d44a50300b05580c1d40c407007100c190440304c04c00766074540c040c1c010440c110180a01c50843c07042070701c0e40403001e0801c0362a1140340105a03000010f84c40f42070410209460016a400d110302e41c0289000040607441d44243e004240c24910140d0240d8403101800900300504540482100e901c8082400c100701c6a8690780000c5005041042c00d12500c40507200a208000300741c420035001143e4580d08507502981c8035031003992114 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 158299631 1250 158298381 158298389
    0xb0301060c1220010f0b0402070803070302030618091506191404020c0601030c05240a182715060504090b01030e0a0804030b0f090a0f170403080315030106 68
    0x10403841c604000120366800c6020001c07a1480d01c106022111014010348000245520003160342d640b03c6031250000c80d00950b0345a80c1c04031070840c14101c0c0e645030356400703200042c50b41081580c00000515160347c0c0040700c2d40d261240d054855440d07d44405030340d90f50004800300c0d0521264010000740b403450030f003842c4d0420030b141c8c24901000601d4410300c84079011a5040305c540c819000c1c8802c0c03110540c01c00c5181d00031400303029044062481c0005114003011410329802d046146502640c0d04180340300200c074800d41043c030f8213800c22121172443d901c2181c050b400c10a0100c40c1c061307005400d0801008103e54003042c9810401442440b040d085442a48a11800300414400d0008001c40e400307980c440ca141c0b10060501059041c2c1012000d8204200305d4400c41e800c250114040c02070040710420f03a640700400f0b0000840509040c00150fa441244038001000e20072442c0322101008041000e620009400341c1206444503241d2504100039002110820107030f03940d2104655070340c134050060900715 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 158300881 1250 158299631 158299637
    0x13151505120c010e15070302030d050a0924090b0a09110f0a05150c03041707120804050d06063c0b0712020c0d061a010305071e0309060e0102070b010b030106 69
    0x41c1c00044015030b0710f1100c13010095480540c0d0b64101c018010309400808060b807003980515904c40d080d0b0780b50401c03680b015104140880c64441003000080075503d00040b105107841b103824910f1807224804015050340040101031030010414020a404190811000a4070403103103021801a103409000c0080000d000d070a40c000d07846502080581011400c0c20001884118441e00d440141c0c0c030460710395403246d440742c4094809108582c1c89110b0511031080a0301d40c4006590b03210380c041c0c0b1560010701407401014820042d01a45c80100640da510070b90040c0200d03065039900007400f850b52070304054451242101510030301c85580c140b0703030b04001510a8680781c2c0e40d4242041181d031555100f40324407404042c294440e00c540d0b6a1250749191904012510500c00802c0192018030200c24907411800b03100e05150410051103185034010880e00f0407070b0408860002c500c50071a0086019028600c0040c20841c502040c60030540703c1034004014642c0109105001666182036100d4188400d01c512800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 158302131 1250 158300881 158300893
    0x8070e03060a18060c0903020a0f030b0601111c02010c140f0304030f09030c1410020102130603020d0b0a0b07060606091a03180609010c020601050a030314031315150512 74
    0x12640041e0721800909045007818030f103d5825944680485601880c40004114100170030030841c0340c00300855002d01080141085491328580e41e1000c41e10300908401d06004680609141c004820480f2101104441c5c100000306095190040d00130701d04000c10100144d0703490b440030481000c1c0021a1607480d0424145895903980b5142192003c80c0400c1003010001040300000101e855031000303401a08102d42c0070500c018586041200c0f003d420000c3c0300941e4018405400038100102c001003c44583d81070140c2e03109800710740340004202c45450709138894208000801e541415801030425141308031030030803000b501c03224140e074442050300c00e440b042103c07015000164104d00015682107034169007001c8907010140441030801004a40241ca039a550b4480844030a0b810000b07a17004120541e58451030138255100103003040d140141d152956a80000400c0c810201c0c42c64801003590041009510010f80401650150001c03120300e8010300700e141c0010445150405841d01c0d20b0b2020030047c20 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 158303381 1250 158302131 158302141
    0x1050f15011706060d1401060201020d0c080103120f052505010b04050907031509120507020108070e060412210c03030507020303072a020301020f0901180305150a0b030d05030708070e0306 82
    0x4469401000741a0704286c68021801d582d151003002103019010704c0d00090b03142c92241c0200d40803501e0741d08030001000b00c0c04004001180904080550011720742c5030180c1000c81d003090541b200e100d46d841e42110144a1503c40ba18901405001041c0d14801c5000b488203040d00701c10070060740c006445034070305078211050800005401c3c220440d8400845070011a022106466800d950150000c1303000201d18009020411903074800640390307100d40b150425010128640f80414818010b0703004200000340341c0e044c2101845501c000c100b9071600e03034505065001d90424001070601310000c0e803c030b0100e4101008904c1c00342c00842038138400c00c5160b9800d540404050308032070200022043c00380910118404071400f50304c0c20700050040d00c101000055076080301c0c500041450ba04c02d802c24076100428001800060f2b4042003102c00d01402e0a100401620b9a00c4181c004203e801d51041c0c0c10f00c0782d003109005071500880614030580080d207902100c0d03902c525041d94100b80c1e1400c12a4142c0065001030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 158304631 1250 158303381 158303389
    0x405010b0a0c0f02040504060501050f0406031203020d0e06070504081203130807061b081e01030506041b0b0703021011071a09030405040203090307020a080f030d0b0607020301050f15011706 83
    0x5a90902a000c80c0b601090f00303402040c04c407181950161421a10345005100c070f41080d4018892030801510200401c03441e6440e85510300c4c86105103a420150000b8881d140403881e504025014020041a40e030141007030480900945c0c4280f007844006c1c06101c0c6001c20001da414180c9100d4a410440390f20140b050341c0e10178556030702510302103a0341c603a9059111081e0140b1241044400e1854507501114203154410220740c4000707030b84010b04044904014000640003203540368009038000d07124554045100000c210401d80e64000505e40c150110304941459400101c401c0540810a01080507842c5040f5058040c070503164064140710f004480055210501c8010561008200090724105501c61001078140da2041e10101155400072074140b0a52500307800881c01400900e00904082840c015034076100d005080c0c010207203580d25207025a042d1030308412600c1c440c0e8000c00810080c07030031140d0321452020694140158020890414084c2c0d409400c81400032000a0102080d640d6000100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 158305881 1250 158304631 158304647
    0x1020610120321051003050118030207050402160b0405010902190b1b07080102040810060503030a090909020609120a06320606070f08040e0604060b04090b1503090109110405010b0a 79
    0x3c0d0359040284180740d14042e0080c8900303401402c401c25515046450744c00d001d825036100211031800480e08a10000009400140c1c01084910654000d40c40d111521102900507107600d00142154030302100304801c01a0650083d60300c00e10845958591022480a091015800d030050403040c210411482d05080b03038480303003d000c003410401107615185c0c0301c1c01c810742a0780103a4010002984040310144e8480c0343c40c02484040c0c0f1090303008500b087c8144000402d0907400d8880e0f01c00b00ca581d441d214081d52101e40c01c82d0350202c0c000d0644c101d000310281a680c0c1d10290207030300751606440c0041b40d400008010100040f0400224a440000c40c10081501c58a61010f00b40340d134094020450040007699020007000e05601401c00552520316000200c11813140081c4180e00c81da00c1d04406000d800007000c10389040c1d44480c44001458803030080814003181a80500d004204804400c016402c841500300707400091049040d100d0a0000300d041c001910405e000e0b1f070002850034441c81080c070340700d0782d05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 158307131 1250 158305881 158305907
    0x5090103020c0a061b090e060607020d0303060801020a0c050c09010b1b1507020a030f02060103020a031202010b0406080c010306080f060a09080f0a09050a0b190810031e02010206101203 81
    0x50ba07040042940c3d0f00c40c1102c17181c0c00b01215005001c03c50b2030038190019803d400400c0b1150450066141c2040002e84074401d038070340244106030740c140c2441814402d03403161018140050003196601d100c014003500d10344001204440510403000192141d04010504034104c1d000081c680c1d0402d03060030b0101885d40c0304045621b001c0d00c26200c05004591072007401502400142e00946070b45110350034024032421440300220203643c084001000141c60b483e10103412030360002c092011107a102c081c202d0241c403110301d41c0d075889800c00c1404165814040340000c01490262001c00580d41c0d81d00556846c2d0a04034540c0300e00e5041705000a81c015142c1d0407070f802d074510610b22180303000a414018109034000c8011a40002c540300001e00c0103092405180000e0708000000d2800c121140d08a03c0d00444140032400c100b04a500200b4000c6901c0c0300c072140556030100034010301d415030070341c0095010040741040e4010710660011400720528980c1c0d01066800a000b55800024603803803d4494004000c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 158308381 1250 158307131 158307133
    0xf0d0f0206160c030609120801030b2403100f18080d0513170a09171e0c100809120903120a0e09041113270602040e040308071103030705090103020c 65
    0x1070410b000035103403403044001c2e5101d24000590741420341000d118041e0342e00350140034041031400600110b2524079a250340042003d01680002800031820b0070000c1050041a405100c0d400d407140700c40d6450340040c0400b03420200104044080d05044601d00d4a01c060092300340c550810201103e0442500400d40c004001d81c40128280c00e42da43d01111307641000901d410280010070240302c0541d20080b440001c10340100011458610003041c2610340c8030341612802c1d02d4503c1284010042c000f4840d00e021008010b060350111503526001a04020003102c15021314050a0480302110f01048191020031a0184c000c0040e0480741180e05a24be1000f902c041c18028080b00031091a5154175440c1e06c140c2c451801d45030390a508006124411980d4080034980c54200740c080080c018001c0040a050b10041e124601e5001c40c60411400a20440d004280884002c038100024103803c01d801034010b40060b1b54086051010810b45501c0b40026076140000540410034241250300c02d802400580c1d0550f0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 158309631 1250 158308381 158308417
    0x320032508040509010e0a060b1903150807080304030506061e01110c090a0b031c27080304030804050a0902040605030a0908130320030109020a0608040812150f0d0f0206 74
    0x41d00103180c44c0800d0344a0308140c04c000c0100005502c490041e580200304c2c0c0956103092043c20301d0002410050b008100d02055543c02860102e0b001311035000303000346a407401742e440060b03d0360f581d60348a50180c007060b55184100c002151150418022801c6424110700740301d0440c0c6141c03801117440d0100c102c0090307068441c5920540300340d0303160020140101e0400c0301c0041d11081070000e01d82001400e078146e40901000302110020075400200b601c284014400021101180b40100b40a14440d0340e0046004e907c400304000c4100b09a8a00070011707540100c1c0c1d102d080541d41d1111409a209500038400080c01c14808654144180d07082420003511850714941010b0348042d41800c00410399000b50380700380300000c040100034844c40d200c0030905420703802841500d805801080d48103906200310420840c1800008082c01a0700341507528010070020040204e08200c04813011b8820300c940941d101e00c030401039004c91f515001104003030280c0e200326201d04102e025020401c09401540b00852440031003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 158310881 1250 158309631 158309639
    0x5070f08011409071e0c0b010e04230102070602031e06150f16060f1a040207050604020907020c060a0c1101080f070f09090606050d1103090601031419032003250804 72
    0x401c0c003000030000e555946031122291f003400000440181d0100550b81c1012003444082912100304503003841252001e03038819604504803e0080c421a100a040a4804020304c07105c100c0700744205c942100c1d44500a07019407140400c1103422100c1080e1900109402c000144028141030050a8088260060884425459119403050310800b28404422950707994680680781c08545519455000c19107045040110550b04d030703551440b018001074811070310341c0d0016588034401c1000d011107000203058240c56615000c406004480300c58411131f4012911254400254868240700e40b051968159501850322a03103001c0c0c660303c03041480300041009106000c6010703490780c000c50740140265a503569986236541c003a001250302262403d44264010014415903520000380c075815170781c005100d44205820303010100d15103541a03c100c82e490115074400401d250b000001d80800c0813145094400100030551348945034824000002c7e109032400c0304400e40e1041041a40380b40074481e103402446c0c6925 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 158312131 1250 158310881 158310917
    0xb070f052404060c110d03180f0c03030806011403010e040c0510090906050d030203121e01090b09070c0c1710022809030302060112081c05070f0801140907 68
    0x50030311599169552109000403ca801d214200c0c4030441450100340840480c0003503a21420949840b5007010f4a6240300c241035084604141101d80c1e1208000c0c80c071004134a0003030349002582c0303c00d401042481c00002e0f000d5019484801d03200031403520281c1786a082054a01100034054403c1e40c2100300d041010406480b03100010b04804095200c08000c03901d400d00c51415a09141c220600900c108255000000c1d00003080d00c1000480b045105110b585240741c503924030210b8211030410b06400000054407c260740d000d6110068241c1d1505116a501042a111407408050007042080200400c01222341160b0f00d02201c52040f50954802885444e50340701603800c0001d035001000841f070348207140700d6418110b0207160707030b91420700500321407550302d0194942105202d40c022202c0701c00c1602d801c10001170101c41002d0406030001d00045282030145005203012500c8601194000150b40314980c017400a9604072208081e99000c013007031003801d2000400d0091b29000a00401460085030000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 158313381 1250 158312131 158312173
    0xa12060905250605070b07110307050d080703060b07020f04020d1104030605060102060115021b04090510060303080a090b0a0c0c0f0f1704150309081905031608010b070f05 75
    0x46880d0300caa0000350000814038102c22558003000c1801010020200003581e8101e125901114a00b010140c1811048100341984035035a0f008000d40603109001520980002889000e240c8980c1c080103c9a124075030801c45102d1400c3c0658010007442840034545041d400a0220650080c00490588404101900542c0040d082122400d40703903c10011a5681040254018503001d19030b041345500800010b511780142c80b20351001c07000c4591000c2d005803190380105e003400c0d60040890b011801921420001092680422070000e030380c440200d6524142c500032150000c0e04a4184601c640b240b100300700040c03406c01d0328241031210800a9201040c1e203400e90f07170952802030551412a00180ca04010a201003011b0b10500c44800e020a000c2c10601c0c076000f03591040103080020b45101b05083c0400c1c90300038107510442c1c14101810203035281da4840040c40c000c0c3d400d8080141c040403186825190081c01b40501c008000d8240300c2d020106e071071b04084900142c014419101941a00c00801890b94 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 158314631 1250 158313381 158313403
    0xc050d090b060f0d0309090e032118071508060415150305060303070c210503220803070b28021602010e1e0613090213060212090a12060905 61
    0x1803008042002d14241000002140c2008440400d00c20340a940c0280903035900f030043d88203d590303c41c0300902c403010800c01c454088100e150341000740380d510b00100c41c0c94401141d4030801c0304c1d0420841071041c42c4c0000c050098900c550102c4000c804406022502004014459948191908030b803450405001c03600c0b2014103401e444120020f10241405800c1d81d070302805041c060f034810030601003c82c0c6980c03850404d580300c00d890304440e02d0820740807249000071040c002d40380f03010010384410b0241c0c152880c8040092100d4082c680d069413400701c507460307000308000903041c52a948000b900008001d0031508030341241c40c4650454000c3e02e4290000ca0f001907580000c140ea65240500c01d568000213003003c09401129104400b100741d04040a150544442d042d0040c0c601103071b0030385040c000c0203941c0c0c0904480301045488e2a1701c0901140105424442d01016002d04101c40c2c01904101c011a0100d038806000c800c034651400500a120b0079032040e042e40c0540e914110a00080c2c000e0144035191 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 158315881 1250 158314631 158314643
    0xe16021c05070512041a0706150806060a080f0d031104030b07030501030b16020a12020c0414010e1f0506161a01050a090b030604080901030e030705010e0616050702040c050d09 77
    0x207032600d20f496480c0503000b42d1526400384040c0800c11250360b440c100311206540c0150300070303210300307451409102030210440f21100001c0c18160220b280500002c00500c1110100d8a8591059a507840300c1d4984628541c000300c1c941045142100c024002d400c8106645551a00c051406607030351521564143c05680c00c2000a0b280c0340108280006407007459009025107405050340c1504501c003035551026a00d00502018060300b5508006000740302c10040752002510900c09902c2d1100d2540c1c00c1c2c00c2c03d000b070044c422000f40115855044800522001071408842d0a142074244020488207820810040a549101d00b0218000844694080d21860b84a01c01f14059504150800c003026141c0d030004c4455910f81804e80449a400046130b0b60000c2d0420300640c1d44113506001280640b41024035a003183c030000444c4802c0240560210240c8a80001074610a442c1c40741403da82c0c0a031400d1000015030240300c00c0c00945007035801601c3c0a10181026480d0000b64880f010654200307002c00e84032 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 158317131 1250 158315881 158315887
    0xa0305090306010f050108240303040305060105130b0a0308030c0d020406031a0108090a060506060d050705130501020a03080604051806010612240315061e060201150e16021c05 77
    0xc181020022240586003110107240428242000240a000004c085415407444010500b18001c0190340e000a054400341c1500d98590b00da00301295580028410300e170054012540c00b180d04226842074102961b0020510505949592960703906900302500340e8150460420400940741007078402040201020340b0f0200b02c414a042042052010f024540350602c8141d0040240100e07000c250500d01ea42d00c41c1000a46844000c0820010700410000302800352a00051024032600107001e4403000840c6521304d807c42d5100c0004a8485004a500401017200e1901041840c03520350040b80d130001780171200945076120b81c0c0070285802d01c00e030701600100ea14200c508441d0031250151040310081102604100c0d02c0a004403141106030344001b52600c0a0301a0003140c0903420b403c03950003000c00c4004001c0c0304008a1601100200510661015618101003104070000a82042013200d440707c4ca0100c655403003c20598045400c2c0500004600818003402040d2505000205c60540700360303103280e1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 158318381 1250 158317131 158317147
    0x715090b0f0702060108071a07051005011e0305070b03070c17040812030903090105130b0708090f010206040b0406020a0c080d020705010c05070c03030e040f05191d0705040e0705030a0305 82
    0x445104003402c80c01c11500084010703caa01c000080c10011510f5080c041c582c80c034100702004407980104d0360001c2c010300480002c94111046e030780080b41a14103923125460b48021a00183c48801d0803448010300750f402040c820443c0c0303996500a1503202d001030411200000c443c1d603031150b10440203900c40346001004103060119010420070090308424070414a85141450b0201c29074a024a213445410003400041e51516001c0002102009081508a25403241181c1c901448940c0100c49014007500c0303000d41075141e80d803000a0650080b50071041c4500d0607216601c0e000040e43c441201c140074820004d001c03c00203240c0b6802441401f02e2002c4c0140c80341e030b02e4900b0b1402c3d01d282c052440704110b82800440f0101d2809010310003207903818100b12413054180d40110703010f06034a14003800d10518110821129801c040c0d203a044051a02108028201d03402c90201075009000410b00c1d1141d101d88000d01c0241000d42c400142044071908540074144d58000086c980500703a401200000c5010484103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 158319631 1250 158318381 158318401
    0x15030b0a06061e02070e13031701030305120a020906040e25080a020c210703170c070b150301020a1d0906060712030603060608031e040b09060715090b 66
    0x160059030105090015030302d0640b0003005000c1510000c0b140300da690300c805000d203008110b00b100400e2546500f031801c0c0b40880100a01e00500041503011842141c08881e8044540c5202c5050307079810384407641440c0d541d11020744004070040c0907103810b0750700708212012543e40e02c0c0513000030905c0c05a1420140307098001c0307200403880032108a20030004c2c01c40c0c460100313400c60840c5600001003080141c5981007250450700d0b050900807031860b02c20200c40c05400342c0740800010508a800b13a110b080140044001850b01c41a08a07851541d4400038420f80b4001800c1640c43c1d500403503404c030611180050359000a003243d000c00180d60100354003641104074503284210b58141c08208841080c060302c0c081e40800c40c0d511900324001d15100d1a507240d0311580c4e00907071240d000f854008104200c1c10f62500e1040b80e03260310005c0800114881100302d565250755020441d001d82e150030107103034100070250082c0f2406400c400c80854640c41140401405032200384190f2200b58080d040d07069039800c00d2401d02c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 158320881 1250 158319631 158319653
    0x10f020702010e0a050616050a0b0408070302010e0d0807030e0c06120402240f0c01090b0103030504090e0318090910020f0403110915010f0210110903070b0415050310091503 76
    0x28050203248100700f080e5a114003d035894002e44807d8050042410304c1c0490510b002074200600c102c050005000910440b10060001d85110303070000c0241d41c00020f44242e80b9600d086900c1c00040e1000c0c000780246209400141041826400704c0d4426640000001c841c0d03001402400e4440124600700b000354070300801c00c0c82a0030110074880365008840b9003050028491740c0501034a41e800080c043c090100b09501c90012683c01541101065841c2d2800030056071243c4070b003400c42070038600c141d0480b103004000c0318003421190019182482a4900b1b01060903801040450390380500c400341c1c00000c4c882e000408a03811010310140d5141e05614150407005d1542e10701c1c5001d0310840c3c00b04128841003604000c010b05003401c0140c0841d80c1c1030f100300e25140c0741210040d011803e09a031110401038540280040360001c4040d10442601e0382410301103801240f1030071802d013000c0d040b07480e400744c0030300d0013035411481c0655004611510b503031810041d16208004441e00c0c0139500020407c0c0001c10841c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 158322131 1250 158320881 158320907
    0x1030b0d0311120f092106010b03100503030a0c020a0801060806011e0b030702010c09060e06160618050a050d020c030307081c1406010f05040b18131b1707080703150305010f02070201 80
    0x11300c00c2001b000c0a8282d883c98140141c441901000000c62009150110140c000300001402c40340d81d0a40d20350020021009000c0032070248024a201064016041c000d400c25260391200030006070f860455095010003500c0303e201c02031404a940413594001100040d8400c020a4001040c00ea40f2414000c1c120796590780200304004050200800568404c2e0441c0c05000c2160f00c280c440c801d0314185800140f01d03e00d0000d0100401007041c100b0844081031071f0b580c650050f0161042c82e110f03101e00307030b8483e0420140300e5810707001080184001040f110283c40b4041d094403020600c0349842d1300d14001c50700d07061000b079020542c1e0703004c0007500d41c0c3c80103041240e088185000d50500c0e1900c20b803000240100c40d628074100c00c0e00982030314251100c052222074a410000300348224400d003202d0648032501d2407000c500241c07508107440100e400081e98540210100d55600d401a950b0580440c003c04200041c6007200103280c40001c0414024081d01000c10381007980140c1c4d4450a200142c04818040341c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 158323381 1250 158322131 158322169
    0x918060c040510030b0a090f06030b091c0c111804050f071505070f0609060516030c02030405010f1106070f090504090c030204050615072001030b0d0311120f09 70
    0x2e000c603403510100b05030100c0707460402003544a800e0000031262020b58215185203450b03e00c004520320800e4100c00c08aa004028204054a40800d540c0c2c07101c0317901d264240c44038043c411503105140b08401c0d030301c5858015107040f5200d1070b0910005142031201c241c04102c1c1c8484200b8001030010901802c0c03403005491005040f100d01e80001034200c648021030301d000b40400818508140110001080081944442c0801500340780d481d00c403000701b809507602210a040e0100c404640350103842981c607400078607001941080c1c039140c0111011034116071107000700408403004c03a51004041180501940540d00d0f6000129000322000b4074a5105a0219200d1820044000045000c101c4030000b942c1d01610089010b944100200d84d0182803030611220310781c0006440e0052204503000c031010464030b840100705245101d8011029115400c0c110796008040c00c000000080c000d551745c070858110b01003901d0001c24401451007147d044415154040c54000654482e1482d181501d10920781640c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 158324631 1250 158323381 158323387
    0x304080715090e06010c14100908180105040b0904020d0615031d2e0902100801030506010e0c0a080402040f140906010501020106081e030f0f070606240e0402090918060c 74
    0x1c030000b0b01c21b4510f890068003150361072800c0b034400c10040c0100302c258880400107005a110764580b4402540c00030300710440704c0b010803400100c15071042c0112401c4500560000d810044008100030003903001c030120004190b82d50070009490001000048140060b039280001c0c103007504400201e4000054050090b990000d400d1801440104410034481c89680e80106040c12554007450000f0011000045c0d840b1f101c200c00011042d90207541141070301d110b40140c5059036a07a0003c0c80001a0640781c681d0b16200c01e100584040348584080c0d075006c0d000038000b140c007000c242c0e0501c1c200c43e40052417038490801c80c81045042d0300308004050040c9028130081111925081000307440d2420ac0d03105004403060f5a050001400b02003066030201ca02c0d003518241d40702e80c0c4110003002c0d039002c642c0880e54981031540005e8421558060241900354841114104ca000c1700c2003120000c20100c041c1e82c0c03081e401d001c005e9290712203c9260784220300000c09400b440d0f003010704d0300d8034001c401411002100c00c10 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 158325881 1250 158324631 158324641
    0x50603010510050702030c0a180c0f0504060f0309020a120b0108060403081609030501060906150c050c0d03091d0415061202010804020103140a02041a040b0a0e030304080715090e 78
    0x20140000c91140910f0b0031501d0792020300c00241400125884241c1c01354486602082882c0400f07181300303403000c5405c410801e40c11086010380b4040c4051004401142080c04104046c500440b0907001c4520a490001824926540042c0e074000c40c0b500b002440390440b00100040121040f0f01c6405040002c0040c181480d00d0f0b40d00400b44240103228980d2603048060b0230840902030408076002d9540f0074024843d40e61100c0300030300140314034031030790ba2100e403503d880c41c50080c00350044d100c1268210018100f50441d0380140600f07071502075000c80401019600024103101c00901600020540702000b02650405040c10724592a05060440c0702074035000040210300010407407100c40c56820b0030203002903582c500050380109000e0390300040903503c010420980d01c3d950360051055814070f0306a5116040170b0a000360060040f4010710040c0780c0100980343e0714a002d1030710020314038130040881e49880c0d100d410003414510542c2c461401c00c80114881c070151070304400c404000d4212800886160302c2c4c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 158327131 1250 158325881 158325889
    0x10513030f03020a0503030702010c14090a090e101401030506010f1d0c070b07020d0f0c150203040203010603080d050a050c190807020118080c07090b0a0918060501031b0506030105 79
    0x59888000c0c21188074020020030035000303000701da208036000003d8030781724038000c08040e0180a01c550ba0200080c0400c091411800d084002d071140c40d4801303016680414101400c0500a000001c03405d0014461a8480c200c82d00b4640205109041d2042c00e40400e035240d46040f5151400603044000410790074401401484481500c3c0000c1254502c2a54841c0d180e90075020450701c203149019141910350000c11a8040c1c001035405403000d801c0d505c055480609038011070320716a031003078002e1844040f80488100e01c661074010b1900140001d00000d9080c1e41c030742d510180c662000690701d644070307211010001041c07014424103510002521089107400001c40c0204900015400581d040c0a00700010610083c800d5009000c0303806c3c038404086400c14981002c920b25007044400902c01c0c4100600415040018000d07170010715005499011514100000c1c0405800075000c2405070301102580b5501064090040c07500035400f4400300c0c0e051015510b0100c0d050060768001030b005000c100010440c0780c0b5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 158328381 1250 158327131 158327167
    0xe010504020616060212010806150f0d060e0c03030328060506030403051804020a0309020306061008070c031701090614010f0e150c03070b071205060307090203040503160302030c0c0105 81
    0x5203c900300802e0102916002c0d00a015502ea85500c1c00d20020001c12511400502c1901846401212140d003030410820003e00d010091581604402e85000c40b0380000d01f16006000189500c606a90001c601c0501081c43d50f0000c440522013109200d40c101c071110b1010759507880e003015460091004504000108800340305c0904000c080000000344408c6018003070104580c030400c0100155a25610210014040c04400600360710901940010032902d00c0c02c4000e403900c40800ba111702d49076981c1c5090a4400d005611416010701c00055140c45084202c0c8c80f065000e44040c0b1400140d01d0300705030686c910f5080170346d5628184203103105440c2c4414dc000003a501c200400b02c03040c00e4582c901c0c00125001c3e0280c145461820f00c00454000c040003d85c500592003440a903645c2c10740381c1060103000c02500c41c01c1d601d15416811050052061001940081d0fa100703000d5021249020240030044d2428002803030305500503080800d080845041c1070041120107003092801c0c5007455aa10750f407284601c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 158329631 1250 158328381 158328397
    0x212090609060f06010507050109050102130e0103020901030204090837030c2f01050c0304110316090504020a0519051005090609041a06030c09040c05032511030c0a060e0105040206 79
    0x200c3c2100080c03a6a1064080701c00e01980300707000340700b0418503242050103034100504440c0c841003040804160420891040c42c1200d400a1441120b6460f54007484014000520140c03540c05003041311030842102d400d030700c14a80705003200b0b0030110013981203440340b1050080c91075001c05080c80c501c41b80c10756014a24003c41010f41d02c035903842d0700800311450510800c61b5500c000d1035090004020007640c200003d984a1806400039600401e054820940c403840d0b02051980701c03112008040c0111902984429072242c405482d519146845030f00184c0958001c034100c08042c4041e0000340f106061814040708003840608150b030a210360040020f1740c5010700d0403910f000340e0395000c065601e5a0f2101c0c1c1c1d01c08001011700003507a82c2c2003142034160300b50f020041d86d0740154207000345414441c1c425401c9a00c20440800300c00800e41d50610a45024801d404a0038200410070301c01c017810150070700003094104101c100400070000c0d01e01e401c6040d1100255070005a900d040300300005a151707003048500382 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 158330881 1250 158329631 158329651
    0x50a050a031a031209040606110616030f020304080703140324031e1605030303040f03080414060c09031c020d180f06030618090804090b0a090e01021209060906 70
    0x4050861295040100400409a0b26104041d56031420004d01c2c0000c003541c031016582030100307d8440e0401e407402066502040c0f0941d2120b00000c0400a0300325024040201c2858085460701e000c04120080c2e03041a681a40c81401c0000d00d2802c06420007203280059402d02c0895003076187c00400801601c0f58001c0d2081c0f40c1c3c81c8013a06400f556014003405040450802c40c1c00e001c46034400520303658143ea280d000d00403104058000c902c81c5400420b40c0c0c815a0300c049c8035803095240303a40403280120068402c840181840200d100e070034806118292288100302143c81d01c8201510030145002000200807800c0d900341d030503080c0d8850307021400c0140100127080c00700603410901c0c400000726020b03522a0380d0320840414041402070389a0003000072510510f010100d4005c114081c4c0d4211050f001d0000d00c810f00400c030400c02c81540e5081118181002420070013502e88e03400901090b148511039440807650b0024100d00440c01e198500c94119440000903d0a89041c01660b55614000340c01c1c8109 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 158332131 1250 158330881 158330891
    0x22e0b060c01020d05061314060d02030a060c05030709050901030c03120504031704090c0305160e030c1e03010e03030106020a0305070f050d0305180c0102100504050712080a090501050a050a03 84
    0x15615050120740119004400855540c034528800d000105000e90b84e0742d21a0101e1403005100040c6402000040170103003a00a02c0360301d4241c100b00c8a000b40390412070301070281441c0040032035910320940000e0748140d02c178160b8070305c1c0003607006105803440e0704404d10442d0900018001300360b2040788801640c1e0f0000b6803240b40e905031501926035000d41c2e400101695030300c81c01184500c01c008064401c448450505100390703218510309400780c0790200c400031a0300c1a4946c00904c050f1081025604140b0050b081e40c04802402010460b4881406440050070554a1245210b41000d21811080389030550240d4159418050000d4840b02081c4000e8200720703003c07074402c044c0b0020142c400c0700e036580300084548240d01e80e032024014202c210348068043d54054941c6121a030041440d42c01c001e030590203818460b40143c1a4801800050300179a0b0b644102a0080350518040c0e01140b41d26009000f203a0312030f19071a0008200f500182c0000e07040080a10500203019000b4080d100012468140411 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 158333381 1250 158332131 158332151
    0x100b041401030c0303021c080f0613060602031903090210080604060b030106030c11070506040506030405070812070b01050301060506040e041716110603040309060807020304051807022e 81
    0x150030048014000003012800000030005102c158004683c482e4080e40ca0302d5040d80d455541100c014490000410b043d100003503109a404248030b940f00c03200801d2822040c0c0800b04c03040071140341d9006100581d0000803002ca1085000d0190900141645814070012a10b035002c20051220745204c142480380e4140400c00a640d030390043c01c0580941140240c0340e60351030a00401a1504181c18004038590b0788001c0740c6c0141c080780500a40c0c01c013030036072072600c1c0ca450240300041d4401001a1135a009201010030200d60074400500c41c0025802d00c2038a8210303030b00700f0307510340e00c410381c0510720030b07803402000300807580b03502c002d4078100c0f003903a0034200403070362a030410aa00345c030401e8641460880c00203105d4850341051482d0950640030f501c820041003007020510002303100645002d004a40348400410000d0305c1a030180ba0300010f1881078034103055444000c40d04410b0403006201960000c64100085140c0c10052080743c00d00344501940c1280a9150011312402c06000201e906038560b00f1100f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 158334631 1250 158333381 158333389
    0x6030702070b0a2c0405060405151306050a03031e02030306030a02010507080c0111041418271002030a0e011505060903071d0106020618062215200c100b 67
    0x3000f503004d070b14030202c5143c1c1200345100740000d10521912951800e00031070703840c0c00c0034425140b1a094414580130300d60341d41c03c10048000280e14501000c00c0d11001c02103600d032030314200c2c0e5004622a4a400149070507405140e802082082140b5045500600c10030500340d030001841489950282004d0341d03201d181c2d003081d030b400348164500d0314a81d601b0030001e20703000310f144c40040c412a40c04240243d00c0160240c03c20101100f00300010a10303d19074403301d12300e42c88007144041840d040440241d0107400d0f003032495042c000f40c0f00c000040607601104102084940b030003000310105100b402000a4540042110a4001a030203a6030185c02c000c00c8004003038a08001c12401703401400860303c0c1c0c80702c08040302c00140c0c009008840040c01840b003c90054030308650144100381800707000d00300c150b40740c440c00f05801030070300c140018007840303441d166005c60864211010700e03082d011800b00304284540d55454482030801c01206038202d042100001004000c685001303807990220012454089400010f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 158335881 1250 158334631 158334647
    0x60f210f0c031e0906090106080304141e090903120f04020607031d03190501110a12110906030a020304060525050c1002041509090501050d110111100b010e06030702070b0a 75
    0x28030f8103080601402401d101c0000c0e0940702e540c40d4002801055103440302240c8038000e0f40b00c0c00c841152100384a49162400d003483d1540c03003107020903403d08100850001024403800369103003481c942001403180707008801c0480540e40304518860200310741c14250b0219a081c491440d0203002c00c404c201c0068030b440e4151030f0010035914000c0446080102811504082c060442404c80b11580b030540c0d03c03205440003200783d0350f48201136242c0c03045107006c4404007070141840704a148140711003000f07a658107550b95001385000b00c110340c20043e02e91401d454070300110350020b002c1401d01c401030380006038950750b0580d04221990051401c2d0b82c484003c580083d10300b034078011070046164000704010030f00c203038100350005203d031142e81c41c6800700740d450f0b00d4002114020f005060700480b1042001004c68440340c945400c400c010b150220381d5560200c900760812804400c0b0100c1c07551280c610081d10341e44090341c40d41c0540e003240e40030300c1c40c201010003a60340d00b200d100c3e10408a00100b130525085010f4150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 158337131 1250 158335881 158335921
    0x4110d080a18090c210b09060111010e0106030b040b090106180e070f080312010609061707020c04090c180b0a0e1b0a020c1c050601050f0a05060f210f0c03 68
    0x203004851100001800c508115044c900405c40701e10841c807410701c3d81d8000e4150504000d05032032941d4a0b41001140c0010900d401850159210510180c41c500d00348141c10040d402228000e56900b002d0ad07240f110041c0290507140399130b040c175005201203c201030100a0076000d45000082d0340c04d00710282c1d070034403440380d00000c14280b0f42e540000350f010000c0000d00b854800920100c100d40c1c1c039200c1c29654010385000c3ea8001440034401c200341481e41d030322080d410291500455100720303a5080081d040d1004010200c0311148049810030208aa03c0b00106000c01500300c103100405284004c40c0048090340f0843c412140b00d800401daa001d2031380714450700c0700c4070150030341c2e900c003690000a0356400001035018003c240d40c80c1f010040100941d040100780340d1000142081da4640310801c40c1e000211490305501491541c0c00142ca41e86540042440300c001c580481e480d044e05544003021143d24640b61854088200100005a0140701a1552002140d111951207850320810300c1107100300e07082 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 158338381 1250 158337131 158337149
    0x1d0a090222140102010506030604051207140109060f0605030a0f11011704050c0a05100f030b04020f070c180203060a06050a030902101808030f1215030601030b04110d080a18 76
    0x2801189546910b040400030510a8000b03005940b14502810307610b02c400c8038040d2081e005800100480300310100203011107801502141004055090341900716030411800300c0e08a903550034a603020100d540103880041c00114058001c0e2802c0341c0307a04441c0810924003c2441c0f440c2600c1c142180c2c050150b074080300882c12406002403600b881d104d50754074010796849100d0011007400280600d41416200381c28009640c1c0c106002c010b10380300f9806410422421a40a60284641190600c007040a0043d05009403c0c2c200102d20b0328103e4030b50200300408480e4414010400c10002d91108ad42900864180e407805541d290b130042c20407030081c61002030095010f0a002c0d00403c88503400801c1c591990002075100201941d1809010342da80718262506c0140c01c414821714079045c040e01c020951090528400c008210042c400090422200340c10480c1c0c2d40350786106000a00c0380c2412000c420700f100340c41014186041e42c403448414007813402054100807409550004400c1401005401000e81d11 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 158339631 1250 158338381 158338447
    0x9071a1b150405070b040b0f030912130e06100e100e0411040e060904150902060415020f16060203070b0402041e020913020702090c07230705011d0a0902 67
    0x403124103450341c01d903001c1d10b0501c6461404035142c00800101d030708903038038206c845207003001c1c2c080f0350072054200801c035041038050f081183e200c4e071110300024824a19000c0052500f68100a500d858000014082c140941c1002d42c1811043c0d0304800c039894001c000312803c034440000660103c9440b61000385403a04241000d10f41945404c0741d502400540e8111540c000030b40e500e040030300c12030a07001c40740a42000c0c0b05030780c0100c040b66180d200d040001d0001d008185800c0d200d003106881c0200d01006240168410303100010085028070180619080784029090041d24024000f9580d000d03079040a04200a404040350455842c1c4d4004100265600d80c841c20300c0c0ca90300a04402500300942d118013511200010040307aa07140d10072a0f800ca60f00034041c800507250403003a10380b103420070001204c90b00028811040700d201810b80c9402000715140051038031601308000140201c007204a21b804240810a5044003940d981c0c1a0300240d510082e80103849060708044001c2d400d0780444106500c140c00c1e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 158340881 1250 158339631 158339653
    0x10080d030c0e01020102070b01051314040c08010b0d05061b07140705100903020306010905090a020303040306050115030207050d0c021906030b0910030506150a0906080a060509071a1b 80
    0x540001d00c0800380d41d11100c1000855000581c2030703100f5944000c103105801001071205140c000b002c0807040d8454100080c150a011880c802100c400391000c0d04c10380c24980d07081261403402d00800728007000039620030080210075501c451b620346c1e000e0400c4401c42e8402280381a842c00d90303416140003542081c100d08400f00c01040740b1761580c1c1c0a014850240303072200c001000e078a015074121800c43e9400b800411050b80380c010102d0081c074001d031418040f405060b02500c00350341c0800181c4040d40c01031000003641e515020900c48900201c1da100e105250050000340e020030741c0400c030740c429004141800c0c00d00100c184006145200c00c903110b03081c02001401c0204000794141d0001441103c180c842d01e1464464003a404248c003d18840201682d20000014141c2c1c46444064012071101428048501e0b840f9850501a503c8580112045600c002c0c460800d02400c0d0141c2508042c2540280901c9400e1444100414001c03050180c441c44000a00c0981d8030b0f00c09a07171140051801c400c1c2c81c515402 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 158342131 1250 158340881 158340887
    0x190602071703011706060102010e0d03110702090f0a0f0b010c062a030605030105060402070507151205010e040b1503062205071401090b040506040905060d050a1101020d080c070b10080d 81
    0x5504c025010301e1041c540060903650051065071400384030740c4c0080c24211a0b00400310701400010848006201c0203004600042c0c88807004140070300317282d41e0815a1860041040004c6908402e40404498101050060382c0c0e41c210302420009078200d00b0104150000c14141c046111a48820340d441c900b0501d807100750340f48d0560109055520480003407085481c0c0c0b00801c82071303014008001c0c0c03441d00498001c21500d158100c540b034000c0900e04045500d02000ea0b0843c0c12100260301c8607c840c0008030070001000b8990500540c02021111040843c04103080031a55550300140b51039150140800c0e82c07440342603044040c0300c0140e804400c883c4415220000c0394480151428202d0200c5c1d85442c001c15a90419020b40701910409080141442e1510842030094030000e03043c2a0018044280707400132803400e0021503e050300a103400d00102c40000002403904024064030410000710b9000c1c00804c807074001c103d803d103a410480714540c40d141c0301c40f196000082c5074807400e528030610a03078841c0c00750 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 158343381 1250 158342131 158342159
    0x2010c12021c08160c0b150d080d050412180605030a0b03070807260d050d0e0105040f020a0b0a02210c160612020909040f051c0909060819060207170301 67
    0x2208996044061368400f2064540e054078401c010140391036400011a914000d0203400000e4130000c1c4810040c1c030050721903e04a90101e9400c031400be48a01c100814072410190401b0b103144185048000025540400300864001d802440100880040445c40021458111886190b00202594140d6680e440c03040d5599800c1d1061040c01c01e03001001d0607400760840c10503101103000101501400c40d004400f00c0c2c442c0d000b42203002035955a810140d00c3c024007403040358440d03489111450341da00b81e00d0040007583c03000c41c0c3c012403552008020160320130750f0124080c050078503805c182c0c0001d10114010b0b810f041c003075440b4140300b91254a03440240e40c0e40040065007110a9610780f90300103c1c09440300b605030304c104030701d05410680000102d0700007129003101548042c05081507494502245109510341040c40242000280001c0b0052101c02e41501c0f03a50020018280205140c1c0234003804600340035071600015100c2c550120303141003440400c99203c49071915000301301d0b503a0360b110b483c6000185 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 158344631 1250 158343381 158343391
    0x2040807080d020f10090807060e010c030b06090f04110f070c06120b0a0b0901021509030a1e0c0305030a0b0d060207050c100806060d0b0618180402010c12021c08 71
    0x321400b404000454000b00b0740c500ca09840c3c3e0702030304001000b0110b84016118800c4122010b05040040f80c0204400d84904034606209000102e108841d0340f03002000d6441d0081050305c034000403c1014180c2d90707121300084035108240c0d008941010140c103c48458050b41d0010b40f503c00c00000e441d404c01100028040a440454540c0c0392250f40b5030010b4011a6181c403510358004803914020b1180d0305456000c0c0048600c1441160400c95940bd95851944016a449040d0358408101c83c444507810110300c250814401c1c02200001044201c011315001882c0b10140503c0800008285d013050a60441e6040207005000c50b5903100c0b0620b080344c02540803c00640e181c1c0185000350307040b0b28101c801859041f084d0b40c1d030b1410b543c4a0380c04104c480d03409009605004c2d5640ca000f004261101d102230300e4841c1041e149280c1e031030460313424004022110380000304282524000c010050385c00540550070700d508506103003400c030608102079140c071542240d111030300510ba000f11800c0a6000845600c68 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 158345881 1250 158344631 158344633
    0x8030d0c090e010b0409020906091914030609060f221a09030a02060606090102012004030201030e03040b0a03020d0204051e1c15050402031608060403080609010b07030c060f0204080708 81
    0x156950b200b05051200082c0100341c8407102c204400c110707110a5402802c900301d0014401c6192188100025038182040c070410502d00058260411880c151880f48480c00c0c081500038241518011140580f41d10b80100507117410003204011905040c00303400e62501c4034041036224115800c3c5418010700b0341c41d13001482c1144090680014030a0703c004002e03611143d5140d001802961550010002d064000018050440d962103403420300001c0d0705a044602c401c1018031a0b9078850030760000401740c3e00041e44c204000d034420401040002d2000044420f0f003c1145001611840300c564000061b10651b400650b000868410480030003941c0043c95121600407990040c0c1301404812040f003500c0d49810180454660b40f40d18120102135411403680580f00409684d0441010424069680d440b03401440055001d01c0411081641109030036800460444400d03102d989001d058488505c02c2800040c10031200000345010072205401c03580308800c40306000d54595840780d55007070740d440d8107101300380c81 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 158347131 1250 158345881 158345897
    0x90d030306150509090601080a0e0a080c160812090a15020606030714010906080a0204031205070c05030109110d03111b010306050612011205100c03020c0d023408030d0c 74
    0x42c4500810840b0f02c2801c02500030300e86580e4120066484800c02003840790280d03151091954500c506202105841c1d1181d94199118a01c0702051454500074100b00c08440c2c00c510000c0c001e08800107850076525101c882000e0b69030030720b0800f14419080a5228001424003503881d101d00540100381148260015021500300e6a500d08040b840d80d40f241d0650750100303101a40a00c4080d124241755541310440280151615070b40e5600c0600804402c5070210004030702007900020010309601180003410214020b20200d07003181c850044490301c000460780704220030383c0c401040500070f80340c4030800804001680c1e4900254007107100442e4505c240c0c0d6001070700c0c0410101390340c0743c400c0a9954069070205e045006a080ed140c100740c02130b04501c262090310605644040d22480c50250509100c0306580258407021403800c42894070241a011070103642100d0010312901104004060117210004814940f00815a1201e540712a0a0700014000d00001a041c000013699400001d00303d0083e59400d40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 158348381 1250 158347131 158347169
    0x30303090b13031b080c0304030804030215030c0406080601180b0309150112140a0b150f011707050d0e07030c03050607110a0b0604230103021c0b0f0c090d030306 71
    0x14800b20b0401408188141503105070754a01c0c1501c0101c10744240d0300706140001c408007951854209034811182007000203002e1045040500c5641000c1c501e90300c0c3d540c1075003404412a080c50090f40190003c000004c8001807881e8807680500200180040c0c0c5030b0a0700e600c4000c482c0340f5600444404025214030078030000300c01c981c01c1040b0b0490b80280c5040310310750580d50b52160b0384040c000c0e004c00d56200d4001c14001041d2140f03005030203003c0382c116a1403100058000e011030744020880650500c005c0d0030f0189035040e003c18a999120009142c115035030442e80d40031800400e0340d903103403903c41e114010002c42041074021004083e640600c0460714150740341541140d101d40c941c40195805d400c00f8a1640c001011500c0041c2c22050040010404ae4001d21506410446903150403e03420498401041035040c00d05581125651161042c4040441e94980d00410704d00a442020600c204a0000c0d000200a03029600b00c00c0000f007200000c001142401800350405010f544c1c940906400e00034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 158349631 1250 158348381 158348401
    0xb040f020d0920011706011110050a060909050c010309050f0f0f07090b061c02160f060501061b08030901060803070305071e02012705060c0f1506030a15090804030303090b 75
    0x120040c0c805a4517141c1200c2810400c0741140c001901250600003e0741400c0c5240000380f008011100d80c00c03500085901d00f56000c0700995000d0b9204905142c40e14000001069010410103110042820042400191807074424a807840a00d181c4034139000700b5000e4416484007042d0990b150070340d43d044551480d201c3e00c030442203071580c0388a6079020f43d00304288111b1014a4803c13000f40400c0002c014185840725010500410164504039a034140c900300300b1041002d1807048902500d501e10f0085014040312608240450040502811311a40800010520b00c001d42000700901056826030b03440300340c2c1d89006083d40d080403004840c0d0580c14240541c0340c0001c99041440150160340340c3c48442454101c14401900414480c1201c4840e4200400c0d80d841d000c00510325440c1100c014140d6030410880c850038171881201e090f441c01c0c003003024010181d03400580411040d4002c0a41d4080d445409031040c020105e03440001c0204074041800411300d50158440c84000303015030300e040520b079130b00b404038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 158350881 1250 158349631 158349683
    0x2060c1f0501061b110904030503070315081b0406030c0b0310090e0606040b0111070e0a0609020304020a0504150e19110903060714040506041e080a080307030b040f020d09 75
    0xa60005400304d02485210000c00703030b00304d44031400f0b604941d040c0b0005c8004244034680031981135001c102e0000610000551520491741e010302c51044500c00305081c038400070786510451b20300d0b000d00c40d5050800c42c01940da680c0584001d551140b058100c03595101003070812500308480d004400700c214000010061910b0148035032411420028010039520b5408100003444000e4000c0d0400c900800300c80045ca1040202001400c44990814014075204503010103a03091900700d00d00180c014800e00c001030f00d401c80600709465040728045461302c1c40401044640c07066500056201d1010030500c221401007401d0650520301d054024408a020f50a5440e1280304400c821909503108100040c40e06101c0c600c810080e00130400400d01c0c0c19503075000100281c001e6040f9403603168411102c400c1120301248480300508101014003202511500c414086005c0140031905050703ca2044d454542e4481d401000d491050502c110f4807150680d8004004202c030704800c407002c1590440042c0c090b0101c03018 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 158352131 1250 158350881 158350889
    0x621110102071203081503010f1a0414060d0809060a0c021003050c1902030417070503010b0a05060a0e030705100f021e03090402160804120c0608010e0a020a020a02060c1f0501 77
    0x34444a03d00140c0e0704483e0104010404a0901035101e1540001d41d070078080c0380c40004007284046264220290714290080c04010742601c01d0b8a45640d84903083e950380c001c980d00210444588881c0c54083c200954a441001681e95100100040c17070740354190411510315030140250340128440c01d0102c03060b401c0321001d451000c52082c0900c9258442180b541521850210a1054900b8030351307220b50501d1103000034417100071780d904401e100740401d0500f482455000380045644600c02c2e4600804103410b40309074828101080488030a02049031010410000208400b52138aa403904840a004000304d00101303d20b001070240b0329603140302032503000c3c3c4002c691900201035840c1010540411009600060104101003510b2110b000405c1010380038000030070000c3c404180f03105040c9003c2500704015040a401e105a00d00140150b1950300400c80c0d00020041c00140d8900c42403000340c1c82c0c0794004000039400030000803c8804107201151022a0011403240290481a141190025070340c003409 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 158353381 1250 158352131 158352149
    0x906010501081f0308030126010c0818011b030906151406090307170706080f0f150f091807050102300d050a02070b06010f09050112062111010207 64
    0x400c00000f880c00310841c00ca40302072141030b5a16600c1d40c0d080794075002644411074454802d003900003010143d9180d1081c090101d4000c0004461000b005032002d0703005860816100d8000b0009000380e62b09500c0020a00404100e101c00503074400801409802280d5040701c0c050b0030710500c8600d520760f140c200c0e41614a4502001d04d407004942c00e2044030340050800642c94465102d000884038407100c900c900b08a5000080c00c0504d00f00100500010340c00340ca4038803850754032010081030040c0441d42d90f07000100e4103000c2080780c4908001800102c100b02000c0e80c400d46540c103001924105805101c404101132042e81c0c03020f607881006a840f5044c0c80210b180c800a07014404000000c80104008454103e003005030608040640b2082254802c84007615405c0e800989802031080d182c803101d611140034a400700e1803048880e002400783c403140c441e0394188444400a2172400013250003102c003a200d12003800701c40c440da11640100d484401c0e102580c1180090099200551000c10340d0002e84000c00c2d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 158354631 1250 158353381 158353397
    0x2060103020108100b030108030d0c0c0b0a0902010e060c0106090501060504061d15040e04061503020612070e030a05240108070b0c1e0615041b080a020702120607080906010501 77
    0x140043d1544a40100150402c92090740e0104074903038281d000d075003c0c154120046440e220307840e0310b0004860f002e41ca6002803202c3c3c3c208001c001a01d00740c507541d0001107884041008445440107940c401c0310400c031381c0e60042001c00c0045c03036140158402001c50303049003003e0206903a220420f45041c403c5000b02400943c19000000c1c00d400043d1071100c2ca401c01800c2a0b4249281d03650301012500300f0740111003003107604004c0c0300510286000d42006084004641d08009140d0f81c000380b810702c47c05241c85c0d961910080040c440070300400101d180c028025040d0345501c0e04510700f80744c580005000341e0b0039008061100006c00009040080c3c1a20700510051071100d00b060711410b02c070703001045800500e100da007040c44070740444112001d840d60030038001030600d801c00c0c40802c644e003603800000714011864440e02c10b8071550000d540c0d001c46116420412041d48400e03842002074480d1071000381d0000c0c1c035040708051070000012503900c103030229903860820f61589085039841e001d0a21a00b03000a03043c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 158355881 1250 158354631 158354633
    0x290f0106170907050a03080a09050306071736070905040c1e03080417060615040614040e13120906080711011b030c0f05091503090f010e0318090702060103 68
    0x191120340e4000b90854216807515030f44038002003608400750402c50f080000856000143d541001100c1c01400045002d03100e103140500c0c0003000c664450b0f01c04c2c1c02c0b003d140b102140c00c0400e151380f04502d2450700084403c1400040e085c0460000050b0b02222641c4151500010b004c03490b8400c403401590300203502e0400e82d00d0720300c208691203030442402c034101907082c400000040030000240f00601c2510441e0030031030124561030741000310084c00c2d070740079140c0c49212204461501c070444040d00e02d14100301200e2640b01c03402031218002d80e0052000d040405003441500342c01549040909441803e0f80b44411090540450700050180318010104860001090602e4016540c10140341d180100008407149502d0300d480c06880f10088000c007003030b40c680e88070108a5215842185000c40f6041580ca00211900800d82e001c440c0c03040315114080100100e18400014002c800d556074510000b400344020705016103031641d02070481404c400d2440c03a01152181018094184108202d4016140c103a00e5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 158357131 1250 158355881 158355917
    0x905030c15031012120806060304030906120b061b07061d0d0609050109110901050402070c121103250905010e040b0a0b1c0c0b030c0a0f0c290f0106 65
    0x3c0c008103840b98600030003040071100c500d4151903942c06142d520700c5e01414120007401048024240c1401600708108110101e60449100c1d03040742d89a18190b80020800d552880080c884012600d070b01100000301c24100f90080360800c20340c1c5140394269214141e0b603800644884d0042c1400e61003001d00c40c00410001d2070076010b030751046030260a001c56020340a9031a075003180c0e0b07680b5045406400307282c4403a0403824400c0d0342c00d000d800141e4003140b41c1006070319029070b070040300c0c451603103075101c500326107802c0184841000c245010301074211000c50b41102c0403881c00070301100c107449000c1040c0784001143e0b1854081d60741200c81c00c034140502034546403910508444001d1002644684407500b449840d100c10b031400080c1d010000014900304180d240c0200b4012659200b00421141030090000da602c0310760803207019011328180010091000ba0050790f5a641d2101c0c05029240d809990100b1855000800d400303200e1980c5543d03188e0381e651549602226000e008101c0001c5116134103602c81e441c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 158358381 1250 158357131 158357137
    0x809060106030207170c030d0f0231090902060c03270103090201050a05030402011e0e1c0201210608070b03041103150a09060e01020304051f050601020319120e0d0905030c15 76
    0x1d00c00c807c0d00c2c601001d445551080e944122034035200b4a5000030810265402d03904079220b40385442e00038480c080039801c039282c81103603c0d00904030b015980c0c0100303a0031556444200c2d104400740c0c0003500c4d210b00500c205018903880411503100641e011600d908411341c480c0c458102c881e58140c54440c10140c5918084403d600020012814014042101820010b0034521021441c1c2141d13a0107860380c41c05014080d581030448901c40240410028201c010707a0800c440301030511300555405a4414092a400040c0c602540128054018414045100150400110b00c1903010b028000140b240750300074559907001c2d1800201140ca000c4003c202c01400d55001070f80504c1c0203c0c4040f42903078440760624220303172054608239001d038070011000d0401980c50381c0340606146c00c00d500300b0891800500207501c0780301d640c1c1d40507055214900b2044400d070140f100c4500403181c1650800c0b101005080313240da51a040e5883d500800c489240010709440c00003220798100c03101821601420748048288102a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 158359631 1250 158358381 158358397
    0x80306060705150603010f150608060616060b090906190203280501031406010e0115050706090c0801111602060918040303060e07030902030c12070b0a080906010603020717 75
    0x25104201c84008503008001280300e030049599140c81c1e40c10410105801c407080c03480c503100080d0801d480440080c100c1605001118030500b40780d00196228800203145218184a03440c00200181d040c03810b00c00c2c5903006161040d01960321803129207540303104d103580320000c4400b0004d203448270b50003901050782d1350081c41e000307000310607543d401008024404a0000584540d8412180d07114010000d2007a0071894810014520000d0811941080c1b1003c2810005000c0d50401044005034411178600c2807044440c3c6030b8002c1c02c10800390340c072031a04101c401600e1103422031641c01d005200080400c00b00445001201403c0c41d170809031660707030a01c200d5030131492079140e101d0000c0c00b03068442c0e9050014075101d00d200341c0d80040c901d8245a440200020081c1440003051301d450000d01c01038400248401e150b4404030344241c2003901c5001813518107031240d01f0480d00c0c40d2010482d440229004900d0781c0c09003155805480b81680c072088110300320700032802c020b00240820b11103012100c003103800a01600b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 158360881 1250 158359631 158359639
    0x240c0d1505030106030503033405070f020d0f140f0703020f030102130608011d0f0601110a05120903010b0d020d020d1b0b04030605060121181406040c0e0f04080306 72
    0x36562800039085514545c01554660000006c0013000410345a035240906421a40200c544520840101441e140804400c0a0140c001503c00030b000d100075111900560007030505030400010300d403414280c1101c40003110302c2c172007510043e10140c0d004101d468102c43c000f402040c45038515002c02c11964140001550155402c008203880b040f0100c4187c00138101540b07814001d540352500711516a00100c0c4130300a41d5950009000038a21482082a001402440c00c40392000d04440c103641002800310008180f40702d414910005a040000a0082110300301d000300b01d80315010701800100d40105100a41c03206604d07541100510f841a56460103500588403894031001181c0724200c0200c072600302a034004d401041c00c200304940790154551015080c40c1580d4880f84040e56034031707020b0b0240e502030451031b12100c1d481180d41d04c80c0c2c080c81e401c6070044c055403003001e88071407001c2d101c802c180c07415660b41e00700581c04200070101e1100c45001d00c6c14804801e160343d50720f44540c00c80b9040a041c981d44 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 158362131 1250 158360881 158360921
    0xb0f060f0d14012402100b0112050a05060f040509060403051c1a0406060e09011412060408130b160b07351003030905150405090108240c0d 61
    0x300c000512079480100d08400c124011035050514000c00c0c0d41070348500d510040c401d13540c803041c001e50110f500181140c3c1d299010407000725010040e6040042c00c000129943c2c0341004002080c98150000d6000c0e2905940440300b2080180170b0100f6a0310490712035180354092030108000910500013032180c6844007008500c8d420340c1c405000309490712026800703840540e10a0005507840e00c6d1240c4001030040b406e04181e01245031002c40c414901c140304800410b0f180841003031941d11000050311000d681130041c0c80d454a0b15103408181c0d500315040c0c0d2000496160808505c6401c02000c4804102c41080b0980351281c40d03130750341011090010300c0c1c6d404104e10f9039002c0c03003100340d9060a600c1c02084500c0006c0d0b40c600350888945800c43c018200e52102d00f045c94208046500005070704183c0b803059582c8400d540700c2840b0034170303030f8452580320307580003681240001200440030445140c2e5841c40002841034901c40c0c5820703000a80e0945e20020707034034810081100303d5105648141c5584007400244c01e5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 158363381 1250 158362131 158362147
    0x203040b03100e1602100e0c0112110d0923071206060909050109061515031a030a0521031b0702040e030c0c0901080607140a09081f0f0b0f060f 63
    0x20060a440d030380c905007200300c1340c002500c0d0140f02045c5841c4540074204902d014000000b6a54440400110f0502c05a080303604042402c41c1c0142045160360300c480d030f990700748030728030840282011942610000c40c1506104c0ca03140c0d01a8840c0319000705000100b80080c10103145008050203514200e40e00c90f41d80c440040c00c0b84540c014402c58502075000024280b4940c144a010345000256000050b10161000e00c2030008840701408089000d10f0002003c044100d038115240031502950f9a152150468032410001c00090307a0f0851000b45c038107100241e09072030715030215000039102e0907544003c19030014414507410015003500f500080000c02e044986400081c00c560141d0780c03d20154220114a8401d800c1500c0d01d280184600350042120b46006c8200621001d0b0005260340780000018840d40211310921291018000040668100c0c807500d11007049110000030318a183d45081a00d06501202288a02c0c403454001419420100303012004000070340d40400c4030444200002d102000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 158364631 1250 158363381 158363399
    0xa06030506010b091c210e03070b09010f0f05090424140f0303180105091f03150905070210050703180506010504110c0705150f0a0201060e0601050a0203040b0310 71
    0x1c1d00a1000d44009980d41c9807207014401001149a01101400d03034a00203000050440e6070f0351350030b0400d074107030340c030201c030030507401260080494200c0582c148641040171a0408d0701030010860f4801c01d0302d440c00c90300580c03a0159044003031000d6103c0802c4080c4020702e140d0515421011f5180303001e0382c0320b80350400c4180a036803071107410343c100480c0041021814107075410f1008120700c419000b10002d5080c10f000070302440f4a00c03480c00b5031038100030700481c024005032200c00c03540070720000d040702912040442d00b000600410802c0c6d0b500400d45084440003495220b030703201e014010444c96014088082e8840b8003440600809004c50003055601d0400c0c5103088030100c003241d0740c0d0340b080c40030304138a52503c4200410b407a070120300c84180020030400016000b400251000403984155283e10704140c44035a00151409840400c0ea01c1c1303400041c05d1181141c1c107510800c1600c60f001c141d61300c0d42d112000110b40c1400b40394124005070f40208010300c00800340c440a90752104041c8500e407411900c4031210 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 158365881 1250 158364631 158364643
    0x3050a031407120207080f01020f0915040b120a0f110a03051b0409020c07080705010504030b04060b090a0207051204050604060e04090c06021501091104060c02010309020405070c050f070b120a060305 87
    0xb0300050b0403119086c030008005004034452010001c009505040c1072140c080d05c0f0b88a0f03030498620072410094901e0340c418200095038010a42d281083c0e031a03d92100805540000440313400c05c2240c07a100752050a44c02c42d200303100c1d525815103181070074820440c605900616000c1c0500c0c06c19002a02550314450214005001500c0700d02405600d07811800006494482c254003c1c0c00103070007410003800315982c0081590201da801c002403141c03a803144d0510000600348100782503009116002000801a066002050114429804c56006030502c0741407101a02a50080c541d10000c10031082140d240305008071899400d00610010300151269111a802042d0358014005a00052440f0343da0303c4124646034014200001c0501c29502549401181d038071035401000284150b000611046da4480e500c00010f13294050700411050a0406024000c000e80f510100c0d402d00c1004000d0940480c0810b4000c200e0b00b8030101c035800c02580c40c541c4850390318010007810010b035550f070001012440c10010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 158367131 1250 158365881 158365913
    0x1030f0c09060306080c01210908040608010302180613090215220b07020a03060507021005040c080706110a060905121809011e031203090501020711030105090703050a031407 76
    0x250001d454640180541510320310b6202e241c150308140c24080f1039917086140800b4010f0310480c10381c5905102200ca0000b0015030ba4007428107000071070007144064000d541c10341178074002c0311656464141d2070a02242a1802c492168005802d207030018110401a040030418a100400c040036014000b040d6003115080300d54001c61040a0303024544020601c5002c1d940503000b01c103105032420b441900402c42c4c1a05070b2000510003980c41001440e002d100f4001c0204e03502074107806000d94241414020a006014016101c10340280380c070010b045400760701c0f11001c0c00c01540181170445469255800107089034503064446023b1f00050b041c00381e5a00000309a0140440c4035200c0e40e820311000d106846405800c034034900c030785401c890500365070070f0040325088030b0303110a0901112a114004401422030444000c100e580007280ad10200b00400c3c041e44c4041105030b008000560322007002c01e035610a14403015000e50007075820705000c80d215500401c4a641015825450021166203d014028a40311 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 158368381 1250 158367131 158367137
    0x501090503030a06060903030e0d0602040e10060345140610052e020c180618012301020109080307020f07091a1909020c100509030711010e01030f0c 65
    0x8104a004034544c407030240600303014600386540d9410341c0d5019104512800b081751043c030814240710108405038040310041c10104224030710300d04206908003035003a850700034040800d01381a8040c95102c1800746500040d854040d02e151180950444180307000001c04021440024a01103080428180a84540e54507403410003451149800041c10310b2050090304600c1c820550040c181c6802e01124510707070312543d00c2540054003894805420382c03404d016001c0c010303000380d003800781d58402000740624203110709800cad2200b03440880c030f0300030150b0500c609028400210707030038004445074500d151113181590310040c00000344848041e206c001c2941c0080310b90034016804000601c0c1d24007000c0c40800000c0103a640c041c41401100030b412180c40306040c603e14012401e030050721042264082d800401020002000c65a5001484039161541a01c140f010071b0710381400007144110000100300e80d04280c10411a60790078001800448810348100541410151981d032030515640c0240b08a000710502a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 158369631 1250 158368381 158368387
    0x22103071410020315040510150c050f0d3203040b06011d010e010e03030409050405010b09071e0e0d060509030414040209030604030e0321040f08060709030209060d0501090503 77
    0x140341d2a02c0c0c0420050011500d500620a1111000d10081e081040300300841d0042050358890b0040124010b0a40c420340c203030f0304155039a0140720b801c1111034910b28003400540d00c0c45404500410754035401c1c0c1058030f000a46c0e500081c00e1002a94250303040754260362060001018008814150a4000356001d44078181280e0500c896580c010364500c00c0d02d001c007240b07014035031840383c0082e124101c07803e1003d06001515480325140d40d024001c5601400d030b88a020003944c100750501500912850f100c07140030f0852600411141401010024403000c1000c82c040042c08040300201e5018102d003480640040d074104e0140005105070040603c10444130f001107440380d1a007810207030032020141840d4003a920400940c8141d46002c10016806601b40c20b200f02c000805202091420030103446482600c0404046120000e41c4d03140144100d41d040349011000076200d4100d251145400c3c0e9494011a646080400060502c4401c541c1d002000814401200c12551501820340b0841842140c03150000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 158370881 1250 158369631 158369663
    0x7050a030b040b09190605030f030c011d0318040207051b030607110a08090f030a03080105090105121c05090604030b0f090d0c241d06010806060d02210307 68
    0x1442007580c9494100c40c1403001048a0011607001d05000e4101c0b0710080041401162084194104000031301d07001d0b04039203410f51075000c959140e800110749510f580d402d2038828001c2c2c5035410081051400d05c840510302d42107548003000c40c80075142c5080c0383c000d5002d21003200851030900441108820a4074845c2c030801d040030815040081c002d10368018403ea021004c0364416002a10710030325940300c014142d44035041d00c00200144e086440d0560701d40719010182003055070104005040f500b05403512600e5903240c50030424841e012000481710f550110440701d82c0058002c6002550005504106d85840104800b190f01e6601607003042e24501030850502c500391494203440d962040c0000050700404100040003092001104406444440c2000c002003042008154000da1410300030000c00182e503808100200f031103461140004e8a016803000020380d20b2010400b0b074864600207100a224402d10750800c0101c00d90701550b15034010a90034011035180c001c100806005024019190144a00c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 158372131 1250 158370881 158370887
    0x21302120f0907030206031e0c0a030c0206060f0d0f0210030606020f01020f030c070303020f0a0e03010b0102060105030c060d093e030607050d0212070305070207120c03030c03090b0307050a 83
    0x3000d4400d01d0300a100d20200700c0210400b0074410141d95045510a50741d8441c030a11700c04803d207403110400c0ba812100207202d801c0119600074000910b072520300344a0001c440800340c2c0c8401017101c1d1542c0048203081c11620618141281c24905c1d03100340080b10100d141900840c0319055103000c5600440d658140910105070100480031f40300b5030342002075181c505600c802040074000a02049103011000c0385010816002750143c03642506a12030107a01c0f940c648000500b40055005014003035440c00118803101c0d440400c01c1c9058507400f07801823500108503404e1052541c0810701c00c51036240e823084400009450f0b64600c17070000141400040d14132002c0044200c8d01162080c100504503040c20070105541c402181059018055080c80c0d80c07551110301c2940060302c1600d0125007104094820002c1d11600765100301e00800d4035500711541c05031604a1000c0c05c03a40440050480a0807010400019100d1705d0040560341c4a4079040d03005c0b41e03641142601c603420694030715000c1070002c40c2ca8035007036034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 158373381 1250 158372131 158372167
    0x10e070c2117010b0d050c0c01020c0303161707080903070204060e04050f0d0e0f04060e10030b0c04050d020f190308370e042003010e011715090a021302 67
    0x10000a00349954540803205941e449003c60310310055446d4070000d664825081c090f110301d9003070071009656418050b40260346030b0380100d42c0c68000240c6c41c0040f400c92442041700445240c1040500720168454440a83d5141070040c0720001c5480b00304140070050300c450092500800004130b0520850605203405401c040801450007429808007032000c050b580e000542e000240ba040e45d4500e1004401c2c0081b0b0041c5c541034002070003001c51a400d000b00e0a08001d400811207000e0a8003280c20380b15030502d08002d1007a80701c0c042d4008000c6450401500d007040d0609030096000b001108070881c0d4030001140d281c40c580c0140d41120001c10035003c0124800c40e2900850ba581620400380c402d40c01c0b54100030131060000000b001924070380324445848551050700d5210030303120044640703100c501c1d4203e4554424010100401d4407078000040d8203001100000d540c1842c040074004110104041c03000c0c03020000e000112520940c0409009601c0c3c4031485554144207050240c0d031484d4105a44030b07020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 158374631 1250 158373381 158373407
    0x1050105070209040303090510050705030603070504021305060d0902040c09060e01020601050109030b0a060b2a01090221070509010e0403030b0a050102190302010605060301080a0507080307020108010e070c21 91
    0x904010710740c01a40c5405980c0d50003949410001102c0d13015042c200e1501e0040041c07428414940018001003940190256110b800100d04440364180c8820502007a4090701c100b804545009182c140070f185048400303002c24218090340059030099503000203064400058030350010656800c000d100c0c06500c41412450300400f070008080ea035161500007045c880452101030600905040401d282040c179400039030080401d04001e40c0c5850031090102c200c0c0300c000c904d1038540001c41081d03c0c190401809030159064006020008860b800c0310103003480b080e00014101079014041d004240d942d12200007030302804010f00c0090b400c1c500b6140103411200078481151186003c3c4004201c66030b40000c0125484030204810380050b80f551406a0141c019500029445031021002050b405000500d502010f070081c1e003140c0d105640e44922648030b1041480c080d0001d09080010300146440300c2c0b03203a4011a4600e844690f01900740c407071191403200e10300f64101c0c4041c1c4121702c840741940891801955 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 158375881 1250 158374631 158374637
    0x30902090a051504110d09030e01120501030c0e0405150109050f090606031b06090901080c0103111806130b0a120e03090603060d03030e06090304090c1d011224080105010501 76
    0x250070030742c0d20340f030b80e5080d48109184a0f948501c25a06100b1140003a50000303013036458207001900d40e514014000f00c00c030f001c41034001040d1180c031321070040d21800307024101c907008200d6240c04d60a0030000ca040080080c016030701c41c82411110030021401040e894001c0c02c181e203002031035081c000302089032a54081c00760441c590104040c00078903a80800e44150440712a074410700307078100000c0480c031710f800380c8101c5940c4109034200008100c2004140a0b5881c02d090340c082028403400070b0b05207010f0240c840300220405512008200601b172000c000c105241300807402405599032405001a680d0086000320005550061a5210340c0b50034040c260032020041d001e90304103000c5101180c0580002040140b04000100700300081c180a540b241d4a0610302c1c100b500c13198035004509940d070f039000c0d201e070714222898809003041c528420110b00c00d440400c06006050039207654011100888040c0e40a0080f90780e40e20381c1d6810b16050604581900d560088a00d0030b03e140140c01401c58034164090b6040c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 158377131 1250 158375881 158375891
    0xb120106020c060c0c09270312060a0e0f0405011b0e03100c120b06070b07051206030a030f0804051e10060b040e0103021504031b03050c030a051e120a030902090a 71
    0x4050f0300171403100c01c0c00d0000c0d1002d5059a545451171f8410256103c2c0c440440310540c165140045070200082c0f00d41c1c1c010898082d2079844800501c0035a20301440740c1450b00382c030080428140c1f0b429089464121780a40c0011410403503000c80d280c01c00118606410114954000c0510241801d022002d40d0b140001e81c200407100340c0040183c1401c904000c00a11959110109441e55507184151410560419440c1d42c461800d2580a41039602814240506485860000300280360000d1005000e66159440300a13a40802d04180e40d001000342c400c0b41c6e107018008005811441130036048003030602040c010304048100803045411a041c541007800034220400c41400108810742480381125030555591254429240100185018940004110091100515200f9412820000e0a90380204151191080200201f5550b0f14005800501035080b809120050b1200d880b80703000f220703150341d00707540840f104410b503900b041d88051030020200fa95425000b056040c0550040e5002c00342c1c59017009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 158378381 1250 158377131 158377147
    0x2e0611060f13030519020d090b0301060c030c02040209090c030619050a1a131202090a0b030616020106080f0d020d08041104020901090506280e0a030f0503040b120106020c06 76
    0x10301480300420300103001e02d10711500d100f09881a81124010b84907000744e82d070589028030f0000d48400d44441513400080e244000454511031440c00c40b4120fa4642c0c8a1061200a07640c0961b0b0383d141d000710a90b4030036400d04c211210b5490700c0c28980d00c503071100c2c00391613500d1070800c040013444c40c05022010001e0702013510612541d2030700c2c08101c0654031103911480c0c030111800108152885200400340741010030384800604031803407244030041075100b2038030701225548200010040b038084d00c030304a0f80350707010a011900c40e01b4bd000c01c02c0e4a0481e01c1c8000b0038039948030032802c0c0c80c006441c3c105100a9020b51001151130740c2c1400800300600c0145804030080c00d042e11850110303245400b00340e214503400030740380c0b031207a000c0d401d1714008010140542e91540c20010300031407030702c0408191518410031945003480303e80c852103419072540801081e4440703150542d15292040d24100c0c0049940b407100708000b0410200c180068980741509481182507513040c428005e01741581c09486601071402401001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 158379631 1250 158378381 158378401
    0x60e07170402090405070b130305101a0112060b040321090303090e2a0c120a141803060c0307090f0b0316090302041509060f03080901082e061106 64
    0x80d40040d01140c1c8500b40f51124280a400e006c910783c0b1250f1081070014034646292892160401103d0007041554026a14100030405a44500468140600740c8082c041d82540c069844812401d41d40040024110b48034106c40e00140d000c1c0d081551400307940140748103a81c4141510114240c2070780b038482c554910350754025210540e01c1c01a211032141003800031704540c0346e28002042140700307170240700300d000100450602e50741c0c00011000f10a01600400d40c0300445c0c68030840d004c1c0c40c40d603521490400807002c0e4842c815040001103400d501001e50704180540c0d001c020041c003505070010040c2c0d076428525000340401846e03a00c00c0d40016070301d12040213040900c200b5a60710810b0502003030483c170b03141c04003200c820126800081d8403a2901308004114208503140d032095680c9e1100c01c10241c4d40300c40d1880c2403040766100080801d0360401860200f548211801d54000080c1300044071210004000c8205034440314994941036030340c00c94200100c56111401551081504026012906025900c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 158380881 1250 158379631 158379677
    0x61507020d030203090a06050301080f1b0f030312100509011406030a0911030a05010c030c08040510110403150b0103050c0c0d230409060e061e041112040501060e07 72
    0x19101d00c0d104550601814000d2040319041e150083c400049a0b854800240c41a0400c0c0641441031265104111803c0d030700154983c4000c0e80c844d0641081c1c05400c00300402840d815000d0382d0940002c0c4648801d4803a4050b206014800c0d01e88038120482c1801d09002e50540d05a000c9480c0580d00340c0040d10b16211182240e403c134625081c003184201d014240702c10300d040e88104182c0c06200d102020001d000041d0301102c0741c0c0c0040e030303018440004100c0c422181c0750015540039000d5000075202c0080741966a0045518010000096062580c2c0783c8a40880c20b03040c0800b20805504e41240c1415503925105590384000680c0d015404c100d00e5a00340350355003d08032400002e008801c0c0e466142d480c1d81d40c010241c42c000340b0001c00d646580350340c0a000980b01500c121044034030340c0c9010071103c1ca8201480c03201c080b800210f0804100e1200c042101801079444a010241810400c43d4030340c004000b0000d00c103901440000c60203529244000801880c028420410050f82a00003e06081c1642c80 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 158382131 1250 158380881 158380883
    0x5030f0c0c09070c0b0618040f03091502100c1107120b061005070f02030316030216061106150105190203070b010603110d020f13080d0206010605071101030915061409061507 76
    0x8517100940c0c40c18041f171801c54148440b414050b818804002c20004540650035429200741e80340c061055a0b9060409400300f04a10940941c008202c50b503103503a02c990040f52445110300d080802000403207950ba0a001a03038100c084194451201c0d4005d00c8010b50a65400c0042540c070b081a420301118014941e001c0cbc074000500f100c0098250302e06550f020400d07500e840204141d900b41754022850b02035038404010382500e140403560500001c01600403210030a09030130700000350503aa51283c0e66092580c040b0400035040c80002d01c2510800e03102d01c9003031254000641c008607a9085c003818008001e8105071312420406080401c808604100b40d400d5856240e1503c10168a4880302c1e46203c046020380c09440c400d4000c28240011003d80c00255104003921540a40d05203988442040341d883c4a1090f000e071044200541041503940319038171900c5110b00502188000c982d07040460340503a82d4130390007098400b441d102e4440c6a86041c481c840d800180444410903081e030f101a030841d40d8000c0480c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 158383381 1250 158382131 158382143
    0x160501051902010615091805040f0b07020114040807110a080705040e070b0c01061a03070c141504050d0201061d1512030c060a0b03010207030e061605030f0c0c09070c 73
    0x10703400d400346000750007007000b400081c0b00400d895914003200511994041c4520100012079000480c03030018984100e500990704804041d00c607940076110925000c1014010303004640da600d80d0344224070341c101c0d41280a40e01c1a50101c2e80c40100b8200a80b01c0c1c1c0c141803100384184114041001034a9001030080e040328070a0f41e000c540c2101c0307500b0903802d000e000d60040703404d4000041c1c400b204030419800076041e695001c1d000741368001115108a0140012036003007001c01e05100381070010810700c0500541040e600421507042c1e2043c81403003a8816000d403011126a0300800c14102d000f034082c02aa00540a0059803a4601c1010101c0c6a02c1080c05070411940202c5000e030040309440d042e011400f5050408122550b8002d151940d41d84c5940803143d840e6228030300217a506c0d0600d4103000720340700c0d140c0580d10b040000903004104140d95010414031001010300565000c0080c4003440a484034900f461803c8ae25481c218841908040c10302e10b011303109543c01c10402207010341120303400e402250884 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 158384631 1250 158383381 158383417
    0xe0c01111203010b07051510030b0402040f0c0f0f0203121803070c0609050108060405190507120608011a0d170c0c090f0a0b0603150d020f0d1416050105 67
    0x1803000d5081c42240a201d065540c800400407802125500c01050460320400458000095076505000e9102081d00c1c41900d50729800b0040020440d01210260402c0c00240f0010351306103800384071001c0394031200341031000c82d03110752501032001d40117820300130f0804c05400590b10740400c0d03403121405000014545402c20703041c2c01c0c4140000b41c0803c19207001c16401841400015241d10014051160070b11480340001c04032000500f190820340605030142030280d134a8140b00746000303480c20140400505650070001c11890005c00250796001c0d003801403070680300000750b4540d20300701e507031710403164107191382c0a10f60515078600085d50301d0625072600d107629402c4030740f24070300e401e00e507420804a02285a48840d00c6000e00004c0c0011003150350041c400c00508018100014044c4030f0300c0e000485000c0c42032100443d0180c0c0d01c1c02c0142d41c00304002d200a0000b003003410b4120001c0c0003098070f1282900e013803050b94142c0344004001c110610401500c0c00e08ad004541c40c14000810317611800c155a4594642c103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 158385881 1250 158384631 158384657
    0x209100810050306100807140d02060d200a1b020303030402150d0507050a02011a09071b06020705060108100207051c020f01050c0d140c03130c0e0916090e0c01 70
    0x4440280042c00004041d079805007024045103c40108074040c08640d4040c1d10400140e00c011640c2c8142500310242950f2084281c0b03400b0410150006a81000160f44a02c0c800b110002d003070345407000603080c000c0f0f010f44503c0200801417904501c4401811a03407542e0060001594000050b603500580c1240d000c1c444041d03070a60058103010f41c0b89104481414442403101c101d0b001806000c407011258000c1207042500080003c6488040350104e820081e4107000c165404d1291000e420740d560601500030200385182e542000300d0380030030016950741e04108014451428181b100d0042c4600c0e8080079410203034140c42c1c0a4407410300140480c2240a1364103545003584c02403281151180d00c401c020080c900c0c103c0c801071525800f4400308542140b40501e2240d480d45416092030180c40d004030381c00e0440d40d0340c84400040c80552032094591407048000080c400c0b0300158064803448012018111542003405844a544456004081c109007002c20b010361041000030304011810003403170540d01c01040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 158387131 1250 158385881 158385901
    0x2b0c0207260a06020a020703060507020a02011416050a0f030e01110613060b0306070e031606020c0402030c1605210903030304020f040b153c07110406120507050402091008 75
    0x100b080010142c074004500112480c3d004210b045c1100d0044c02c05100c1e50303407202400c1343c850040c0c0780700078041b0b071102c00040350254201d00501074500311241045042c5000e034131180d00e04040f600701200c05000c90900c40040603801800c000e00100c00382000820815020300c1591140c80003040c416a1840a40c1302a00b407201031340001d0841c68026041c0c1d680741c01c0910004091000f20940345010744244c1001c0720305503400e140c0c203c0850f8400d070b0240c050034030148204400303544040e08111030284240441416400041905074400d8801c2004050b2a40c402c079020440403038907115a000c1c00c00a0040140326140171040301e600c1941280e400d0240c548140014004003003081c69160420034208403000902d80440041c980d00c81220307407010462840740425a060b40d2020402c030b1304401c4070000c0c104490b0080000d461214400e40c40e43c2600f40c41c41011804540031a84611041040e28017010107000040c01401e01030041590190326119604000c80c1d0029008d200708410013500800003110003503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 158388381 1250 158387131 158387143
    0x30a080405161509080c0d0209090f16090c03061503050402040e0304090204050f0f030c150d02030c03010501120c08010611010204030f0303240305070302060c032b0c020726 76
    0xc00940a114025140c240c1da0800000000f00c4a010441c004ca0103c0c08080004a852005000400402d104901c42d400d018205001825604862241100240100905121185c25000c607030743d6803040203181c00e10203000d40d4800c208420a01d882c0040030702c40d0f07800000841c1c41d00724a40c200491584c039140b001c1001054144850f848900001c9004222040142c004004175a0100c4086c88250390680c1040183d09000d000c02e2340c12b900440b01c05001e400d047c00e107255a121318080326420480705610003c143da10460303840c8880d40c00000140040d40e00a880b01d54009501d55042140341d079200c5000e490304106009000a02150a281c012980e5003501140c0c05180c2c0020003041207d01860050301801c0c60345120708020501861039005055003880a00880390400c0c0140a040d1039a001d200c40d13680110081c0f480b47c002000341941d060a411002070390792115960b400c1c600081c94400c1d000b1034154245401c1190402e0720100200e4104031074180c0602801070a4511000c140150b42d80341107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 158389631 1250 158388381 158388403
    0x20901051605060912131214030301120b090303072001110c0106090b0d0c061206080607080405010e010c091809120c0209010501050702060a0e030705120109050f0d02030a080405 78
    0x110305a1a042004400316080b8000c00c800344c01c40e00d4025540303070307580128003403001e40c0743d040c4545031070402402840d5a003548100d40516020072100369141200c50441e4826080803031000d0000d105e071030800801400b920342c000000c5002d107046d403c01c0c2100a116201181d203008440c002c001c000301c41040290b00c50b01d40802c0c40c040059642a5018200b03020b02421f1081c0e00c0070a150100c00202d030308001c0d8000c0d0030f585d8020180510340f410f00f9402e80300301c8071010907980c090340c0c5c400002c5601b600130003030036000388c00300c0d1034007142894245051801c3d200c1100038090300ea4100b0301c44145160b00308810400784c600d2041030003400c141414800000703022204015000b811031a84022800b504002601901402581c0b144100c1e0307202d00054646104145000350004000c000081c1418860300c081e403c03100e0028140c0f4405966030f000185400042a0501c485c0d9641d110844108030041201c0410b800c4c1e0b480103007a209084042c0a92070b80100003002060041d500000341c20018280207455450b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 158390881 1250 158389631 158389657
    0x20a090c1e0f05070b04060b0402030703020309101b0503130b10060e0102010c0c11040933090201020607050a1101110405030f06010506180f060703080f0c030105060d02090105 77
    0x150210007404000c5001c1e040500d040e21550452100d0711071000e10515510940364107160022556400b030015000070015035070b441d07650302c8a500507901c07800210b0064400e40e0b070160f101d080101c4486d0034110710814041c00c1078034011000004028004080040300d1041c2429522039554490010640140110090140c1c4907201000b04840d005640c4c0b00590707109a95a203d040944401a400c0740c0306031504001107401c034104070b00062404503002d407001030044c00108143c242d9a4070680242030620124148825203803448071100da0703d5004d0511200e04230018071100c8010340010352910b1003d0806002c00100080210b405070003201202c15a02d0000002c0096011060010300c0641042c05071a05ca401a0118001101c0b80081e500c0c0c140d038401810b692802d20240407004082c0c013480403032070700030403a0001d60300b25070303946005030020f14025201c03050b0310320700310340d0903408220010f000030307686501880180300070740f6180151000c45108000060352015000d0050302c035801120004686 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 158392131 1250 158390881 158390891
    0x40c0c1202010603030f021615020c1305010513110901030c05120f0109060816061d0301020301030b0a05010605041202042d0c030b220b0a0b0f13050d0f020904020a09 73
    0x28a0303030705600c044100d0303000340c1e5040d12196184030200c1c2c884070003400c84440c0300c1c660281400364105040004003040c1e05401203c441c1056100428003000001620506443d03450004100038205615407004690f40704008001d91108011441014091040d40c1410145d8492a101c41c450081323086600302d50380950040340c5880c0801e000e02668100340210141b80d804d100c4001100d10300051003100d140d80340d00d1741d04806402c0c41c00c11201d0381c91032481d40b90342e03c800d1040c100c05038400388000d501860150548a10603c0c1164801c000c3d0351040c0d00c00d000f0424100030410110000420005400b40e040741c000c40c500034086901403405031031000e241020a0395105804141e40036501442c0c0146903a101484020f0051042080e0903121400360b04111040d407440682202c62580990615180200284d1007a40c4070612440c6942080b8480f01100c000040c642c1c21007031403034a107100207090850782c105002c031050b610103201003c0b1150082c003448804011404640d20dc0103007402030b05640b041000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 158393381 1250 158392131 158392163
    0xe06041d0303070f0507200406090e0610080d02030301090213050a0b07030e01020c010c0f05030f0309071805060a030f0606030203010f06170a05030a120207051902100c050c040c0c 79
    0x1403254810b0b100c0f6000f25040d4400c8030142e50043e001c0c2c0d2206d9400286084801c1d440c050380c41d80c1e15030620000760740140d43c0c500110f1040351622490100750400c4005000b54a0061114500981c0903044501c050380821180c00c4d12590000c1100c1c195901154056110f2140000c545107502041d00321542c0400464404282c1c1769032400503020843c0283c1c2c580300d031410410016a01c5080e40305046001030864540c0c5400b05802c540004442031040b000c40340b0b131006003480107001b03070000e4416280300c5d00a003604000c1428141c0344c8007032041400f04100403909100c000244d0b03032170541c400100341c20414000780061107880d9105000550b0050b009102550341e0004c143c00800c080d000742c444c191f80c0c1010840d045000050242c01d00d59020b4011440c2110b03101b03081d100320034490070b44603076550200214000544180401402d40f080d020002d00350b650035104001e900d241003e0700c4420800400e40a6000c18000144500d10280583c4c0001c4d400c2105042120159030702c1401901a4484a4200c9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 158394631 1250 158393381 158393383
    0x3030d02070303050f010b0f0c16060503010806070905030304092403080417072303070b190e03061003240203042904031d060c06040506100b130e06041d 67
    0x1220702c41c1d0390030821a6a1400500080c00c000c1c0208464143e0a0012a400e04040c00050000418600032900040f24070301003207495800c240c110100064000c00100700580d82002000d810110500342200c2e494103000100c1d03964015441107420064848068503181217440503001001045114401c2610b0b4172400c1c501d8a9034030511405c0520740c1100348500c00490046902c205031202085401e40880b8000b00c0c212640481c0c2144a5140c0591000083c900412000a0404110001540e103024610801c040d0008605607245402038110101300010804d07000716000c1030341d901c80c1d4045c60707115000201030562004c444040034842d1000040c0414020103002400e21a807071103400810142012000d120a454150703401808254600d0041d40c009a10951100e10010040c00050034030a554008602e441070a58090f555134024506000106441d800d0080151000c5420549090040340b1041c81010883c0304862035085044003282c440e6903107070409203840c00c5540c42e000036951294115 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 158395881 1250 158394631 158394637
    0x18010c0201050601020f0a05030714120a02010903170f040b07050405100c0209160c0b15210c060c0a0305030a1b080106020601051804030f02011401080d12141f0503030d02 75
    0x6025202c0c20251403000c0b03400041c000f12680d07004009d1414424981e45143e00b80756950603001a0780074120290701844000e1000e0322407034076158000b26120410f8240a0b14a00c050074401c240c124100041220b00b40c447e88500c5d400541c040d440321016640d81d5805c6803180515003081d544014202c00010000d544411158040c0b402140c11080648540c1151150401c000030300d000130800c4c1c0001c1d01c01003030344901c0c010b81c0040050010040704080e1000200d001d031131544801d0403100120319084158508001000041c107081c1c2e18185411300c442005039441305204070050400c0030010003d41040b03c150480c1800c50244204c1c00c5551402c0790010300f01000074014080148100400041c05240c60803031040503040e400444192038440362030840d411050310f0b990000750b640b59482075201c3e50349004110700806c1d015000c1d090a13000b0280080c00b4055025400c0c00341809c0a4810000744d48d00f81103141c0200303c02c1808541c403c1c60790780c202c1c0710080a80c030040e4940004034a440301e098807a001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 158397131 1250 158395881 158395891
    0x31b0103060807150f090e010e18010507080604020d09020306010b03040510050c0f070602070c170c030619090f051b04060504020c0d05130314010c1b0506040b18010c020105 76
    0x42442982d8407640b40d140d840d90f41c1d1080002481e2002072800155000345036041c3d200902c1c0c5454480c440d12070308000500740080c4c0c014403d4140e45004c203c2c3c21600756600400360200040203002c28101810010305618024001d24407ea600094103520000300307603c1200110340c050107171002c40d80d69040d1030145806c11102520b02d4001d00c50b01300144061403081520031500b00c00e10703604000e40a01c0c0ca04054203c1c00088a41603801c110410220f1001c0c0f1030b401c02400103100c941380c1c00760b158403400d0500c040c42d05518002d90140d4144a000c103104c80d2009012208071078000b4520f501c0d400d1201c806801020050901d000303040c0c09080c1e0300705000c1a082d00d4001507800707116555603201030204a1280d904948c180e600311021318554680300e03500501c49943c890408040d030316280d803180301c00a15440b821551503952000318240094000070031150500c1c50313400c05504896030ba00c685481c4c1c14010401040b20500400156400440080e50007550a90600820903d0a4103101034020442903c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 158398381 1250 158397131 158397137
    0x6050901090606030b041a0c0316030b06071506050109030c05120a0210030507080c030601080a050c1b0304180209150c1006080a02030f0607020705010e04020c01020a020a06050c03040206030112020d02031b01 91
    0xc7c82e24004412105d0f40a0714a42100c1441c5965020144200200d0180b0081c10191519289441542d5100c09880f80354054081c11416040002c560700c00c6918a0344464140440110200b000c0b4613040c042c074049400a80f51106690005442541461600c2100030740c040c40344048201a29850361009210355415120351202c1e071560341c2a120f0a00088030564001100180003c00c88030441d04801e4009a4070801d1030304040c900713000400c411a9059018000d07a202040403c0181c2805101003030020000c04210f1411030081c1c00b040714900c44601ca0050368400107008400b04404000c0c03060800c1c03400008000302903c4a0226413150b402e030340b090748684101d0605081c8045e02080090088806400034138a40d80f901c2c0040d280403c803d118640d10035400d00c800d010024081c001001214034983c0075104039a098a4000d0803034001901c40c21a50000744104070050302e5440c101e9064075840e0140074810401c038400a0080031028070003c0d018058080e9041d4192800f502403107511909807 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 158399631 1250 158398381 158398403
    0x702030115230603040b060d05010603170c060c0c071e030804090b0102010507110303070318020d050105010f06050a080613020903120901032708090a0e1609051206010306050901090606030b04 84
    0x10400c00340130603078002c2c01c0e868105001c00c4180c0341c1250041e0030710340301d5030004c02c0c165920340b520740710305c0700260081c0e0f009a00010b910601c607405201c03865100740040c81984c00d00d083c10400903500d10443c052080c03404a5403600540301c10103031100710015644201e90a81c1c59407510000c001516a4844480c090740c00c0c4404241254007030f400340110310079124010b500310f039a0f4480c00c80140c1200c80c181807034034001110400258492031408940035008000200c2c90f549400026010952541d21440c20441e0a10078604000d92203400d96030010411100e00c440716103e03603141002171081c401519494882c6542101103d0348400181941c504240c80402c0407510343c6c0d9619803201014000080c02e00c254103810000581d011016201270040540508811600c03166003980e025001c0d12011144208050181d540726403282d51200980b2054030060503480c5000c8405aa0701c41c103001c01401c507900d40340000c41000003544455403540d00a2020720180da580d0406086d24201601d05a45000e401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 158400881 1250 158399631 158399699
    0x903180103180602090d06050f010611070b12190207030e0406060302091305070311070c0f0501050406080708090c0a141309020315060301020d0e0309120c030c01050702030115 77
    0x1d01c50034158102010100403850300c26034903c0001d5010031121540b050a04031504041490762244034418820221400741c25418840e010b005007452504e0000c0551107c40140320341c0c9650819039010b108030441e401c1c0c1e503803541445d0100c200c02d5011340c83c442e00d101040e41014954000c0441480750b1066504201540d101c900882c241e05c19001155007107001003000d8051441c1e240d0202e0350000442c50009003180d8401d9900c586035014510035035001c01034210901c0218146080000104401d01300070389080d18040300502130120051011041c00948c1001a803041014803207940461402041184a9521103810450010b000d801c2c182c0284004207003200040703403501c0b40d40040345e002002801c0c500110f6840030000c2d04010040364040d5000e110440140c503a60045c0301100c2d181c10302540d15980c804007408401c1c2d1040d0301090199100d1b85001d0503945000c00d1420300200d0a103050350b56820f1500103c2e000d00003408018002031140080040d21044d070a101401c42c00756030003403c1c103041007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 158402131 1250 158400881 158400887
    0xd050f060a050109030803041703010f08061f0303031d030f0a0210020a050915120a0603020103050603010c14090612280b030c091f09020901020f0a0b070f11010509031801 75
    0x19000ba207001c034400103000d1021401041c080c41c2e1051061201d11800c0c10300010602c0742e60020381c0800b00d44014244148404102801016404002d45944910f51084140c07410b880361028132000d0280360f65418212000c88a0740103042802d40d4190480303035204240b542800c50740e400500840014085e150003d5120030a0b4001c1382c0e080d102039900ca5003020302440400c00910b0804113a2500c11400304074244090184115640c0f1640300c1d1800040c0a42c034600014003900c80090000f80f01e64500040c60100d543c2092013003010010b03140585444560a04c045100e0384034101003800d0507480f0300108403000702180240300924808003595110300101800c60300a8500303009000e80e0603008420706400c64104800d440c1d0340080c1c00300840b8000c0e0300e41d000c403042c0d2036a90340100c0d1600307400040840c45c950301088040680048a0002c00003205245c03501c90603020003030321920411080040451032503200c0d00314420400a801d0003084a4100681800d039039904c030030f8588520840c0e5000c15400740d80 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 158403381 1250 158402131 158402149
    0xa051605031909030c0618031209140612180109022805010503010b04140103060519092301031101020c0909151b0306131803170901090203030708070c0b0d050f06 71
    0x44d00030805c810490034100103136a0b00c00b10440100c24140c0c0800e001000c01c00c0e05101d0038840030700340c441c214840d060411080e440075855143c00c0c01500c04010581c0008a113141240d8040001240e100c0101d81280c8424050300921a019601084801007824100c4041c3c00400ca69902203030818219a41da000540b00d0340000d10407400110001d010401003205002807075040503105140004045403188001005413a01000e185038000707d66030140074014082c4911a50520189540200d046284500f245c0044050100401201641005603011390081040c4005000010050501072402016140d0f0f5011800040c115143d00b503004108402000402d0703e0030740080e4000c107407469070f8070001c0c03000100422030301046480d91201d41c0348003030b001c0924042d0424403980d580e040800d205144035030140f402400750b4100d42d14210080300140d4000017107a5000e680503c01c592540d15606005010000d07651204440100c0041c2c06075032005c2a5105610803400d0081000d01e507200c1c2c0051000040c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 158404631 1250 158403381 158403383
    0x9020c1b01030b0d062301061106180a0201031a04090b0a11031302120a231002130e0c040e010b0c0114010501080a0e031605030c060106050307050f0a05160503190903 73
    0x62407880c4107000300d04543c00c86e1150102034003158134410711240900a403860264003820000301c080c940d210486100344526504044803682c5192440c031516681c81e2101950900203042c540e8548941c0310002e012554101c0042e0b005104000744c05a50a00032084407003141d0b402c010030303d0103400600b0051440c0c00d40e401012140250344643c0d040b582885015444000400c441d885041c659800189191311450300244070034070444482e1103800c46061a080441a07501042030040c458600c0030240100c060040310725071304d1031011544403c00c0f0b5004500c500d07040441540e10308000400c903410454020f00c01b85034104000c000628071440b2509950000707025050024100c4008100c0d004e25540054203081e83c000107480c5807201c2e9440401a0502d030000031521a0004540c1c00800d04003401240e005024a080080c614600800014154451a41c40108800010a290ba00030384500152410301071003281c001d013058401e08149550750000700301c1c10403000640030b00c0030380c0a01c50841c20080f0b03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 158405881 1250 158404631 158404639
    0x3051005010b04170c0307030303060f05030609121e03010e04020108090d0f0302030604180c030b07020613020d14060a090203060a1e090f0c0b12060103060501050d0b0a09020c1b01030b 81
    0x40341c1040707140312130540c0500712101036110f1200c4201841e0f800f403002400451007600e0008045252401d02a070750070f903d5001520035000035040284014000c02c404000484503490155600b8601c01101c01c450031a030440d400c4102d0202c004604a45400d012a004a0003621412040c2c2d4031000f640707944105500b4000d002540034078034031500c3c41c083c2d0080c540150008001040c41c01e0103844142c90314080c240180c5603a807110104100b4031030b60448541d081125032010307241d80e141c1082c0000240100341402801902081110310501140076000d01900112509443c05820280690005085110001d920a01075400481c6004c00f040c0f007652560301e00c1c54075035a00c04103250750400041480741420fa449001680310500007420300d4040902420906c5002034403004113000045244400500c0c107418146050402d0000303a801100759101070f10300b040045402d46c004000300d01d50000c15485006924004204090144000b0400440a0180c00c01500b074080444004600740d4074045039480d00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 158407131 1250 158405881 158405887
    0x604090f030c060e0f061f05011d0d0602030117010b010306080a0224030f0a0f14040f0c0b030106050406120c0c0b040321050a0516090b09010e0d03080103051005010b 73
    0x901034107460800310b010f050005007078820080c4550504d9103140c1004081d030016000c00840303102000105100b119a02203120b0405e05101c00030302250418207068515541c002c00b1008250780340c0a6070284541d100c42c055469594032403852580d00310046250f50b45500380801032030954402c1c801ca00071100808005c003240e00140d000c1c03000c2d000d102e07803402c0d180c00c038610420700403445e450b40258080c0c481d06410312103c1c94174141d1a4119400c000b9040c2d03c06051000815001c40c40d00f0043e0f802541104140307881403964a40070b07414401a07030001000c600d020000040c941c1d00071024004455840d1940d115040c540460942220f40c8503240e0b00103d0000f0420344080782c0c102d08080d611901c207040214480321010110b0035916800450110314a45680030414142d00b28000c86401c02ca4840c40041d060f5942070340900001810b0280800298000c20400456032160050030000c4001400b20030300690780d4100104103040901042d2075902c00c1d20704c018401c198902c80c05040326504008181 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 158408381 1250 158407131 158407133
    0x20d1b020c0d05101d0304030507050a0e010501051c0e06010308040503100b030604062f04180c0e060901030603020621060d05030f0702010c140703021212091005070f030f080604090f 80
    0x400001c40d075105c1d40781c1454560011604c00f040240b02031030044008045036494041001203008494203d0140140300d800100010f036004000e4aa04810b4607012403100300614803520b008010403001400c2c076214100001051140700001802500d00c154252094074030501980d406a811540045416900020001e8041403080d80007102c2107400d0b01d6107003144000034844070301c00341500c8000b59803008001070410000020610a10703552407200c40c2807107040964a4080c2c40d501c2a20b0104c0d008110015192070745a01c00d40c800006150300500e000c4d2100c120040034042c580064403908061025600402c1040c0740c14000005c05941c460000d40c035004450f8401c0d80c2e207402082080341441141e21001000a11400c0840481e4203190002c10841e403a5004108070356141c0480c540b01500209407507a944950081203944810b000e0700e08413100343c1050421a02d80c4200031010b0074030201d10550808055000d00c900612100e20742d101d10240c0c07102da04010403600c01585c01440246107050442c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 158409631 1250 158408381 158408413
    0x315070e060702030a170f0f0d060918200a09020c0609060417070501020f03010305150a0221041110050a020c03070b040303031a030d0207030b0a02030402090118020d1b020c0d05 78
    0x6c1daa121440d40e40c9410510111b00e1f0200c01e400103412030004186c040b8110003061000d203c8c64006100c0008140600c3c40300464000b407030269040d014240c10400c002101c1818000b203030605c4404006001141c005540c4d040550094105682d018081c0c05a10042450034400080480c0510b07002161842c1001503081600050b81c1306d50000c135041d54013400124403440da0500618001c3d4045c1d0090a41030841d81107540e50b0b448010300d001d0782f003407040c001140174441214110f445015410028505a100c604000700300c4240181c5941d4041640c01c0f01101d810f40c00000350490500d95002c0303a5102150034105901c51056000b40c030b42c1c941041c030003000841e05c00e030000c0303400e000c07481d074108a45080031011070300b000000c006100150344403100402c01c10450300d00207580801d14510450030750030654002241c4c40410b200c1c080b0351140910100c03404015942c102c81121400003030411104c0d400e546502e00141c07003d8010005400390980400c410700b8100031090031a58490060116044099000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 158410881 1250 158409631 158409653
    0x60702010504050112060801050429010e0c0c010906051e010902070302030304030e0d1703090708030304050316021302071a01050117010e070c050102030a06091b081b090315070e060702030a 83
    0x103860086d07111600020281b5080c481c41d402680503101c01694015400d0300004c0ca44085210045100756220041107800c1c18440c2190300444200c41c2d0954a1600c1c80a50340035291404d006081689031405100c1c4000c1c40d140d4190341c4825842e03120343e0301d030707a91002032040380125176016002d60003c10004000070b200b5194a0041c1034000c1854a096205490382010a04a0241c504440d1400020b004d0221010400b0000401c1c459008624500d03140e650382c0e889009200d446d2818a5000f420601196a0380d00300c1c1c1004224204119112a017500300810851a070b082d0031504501d2120001c1a01e500c252680c4e00720030412802d44002d44d20785446985401e00007829041000210201c2d040010800c0c001980150414a0f01040701e900380b148030011641020400e12001c2c424100c29040f0301e0304100000d52042400700c1c2d000041180710450202d921417200c0c81c652500642c20740d0080d20000548050064516541c1c0a1040c00d42c0b00600c201e40c0308041029516501040040c0c001a001e0800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 158412131 1250 158410881 158410907
    0xb09070207050402160807110a0503010e03040e0a02040b0d1a0405012304020f0a08010503060115021c051603080a1a06040b0c120703020d0206060324040201030603210e0607020105040501 82
    0x21645d03012a191000c1075048820210381507010030100c0d800c0e46c84e00030741c8400030700341c00c0300200310081040c420242c1e83d1245115041e16510040c0006080300c0782c1e641035900500c0d0303110b41036940309071080c49203006101200200c400140c41c50069030b12410684035241c161040d4444e5001000410206004110101c0855a521503001c00c042641889440091b00d14200c480c1ca4010403541044200350a0a105800c220400e4500c1085285415400a41c2040c451402c00c24a140f04000d1007003150203201c0d64806004c801c0751001307213904140c6d120004501c42c2d80c03044400c121000b01071110180081d101c81e2940d07405101131005008210b51100101000f1128070101e942c1444001c60b048001e4202420503401360300001c10b0740c2c00142c1c050104540c0058202c1c0501000d0034003c040c1e60181c0e0078110380b9886242c0180010b030459000c2e6010101030340e0000c4a00702c1e510030540008410641006228002902d480c0802030275080500980e110564140c40d03450505007054011a0301c000d02c032507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 158413381 1250 158412131 158412157
    0x40e010605130323030d0902040509012003090f12030708071d0f010e04090b04210f0e010219110a09150e04150606020c090708090a02010807022401090b09070207050402 74
    0x313502030207120100010440441c1100c004114001ca500400044034030040c94564680d04028007000602d03a84490009403100c01740e00f1300d4480e00d0f11680140350442555805985102d81116a80b01480c2000590b2099441d5943d00009983d0042c007203484204090580c14040b603198084495403800070ba601140d80810b00d040c00100b1203000000342601d058540a0b0351020650080c8020302c0039244001d03590200c45a07640e0300c1900380500060030a601c090840c402c00003100d0981070540e10a207c400101c1102043d0004c10029070305001d00c0c811847c4020b68840e100703c69000412003010700805c488034103146410180c0600e000302c00c2000c0c1c10700030000ca90848981c050302e94002c0c49072058101402541d401004030160701c0c0c040c40030f0850301828107414080f1a204010240c0d40c000b0f1000d181d0303682803030545e00b5601d51000c241d140507401d4084d101c0740d507982007050150303d242c11103803030484c5c1d140d202c140002140b0b00c060000072041990b4031001a00602c80034841400e05400629461076560 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 158414631 1250 158413381 158413433
    0x6030b040c0e011e030b1306030201020c090705030109050a02040306021908060d0f060c0302070c03080d0c0e330d090507060f0518010c0803190e2e020d05010b040e0106051303 77
    0x840012030064611031407c44032683e9400900235968100b000840c640001c0d1040c9040b070420f00400383c214001403007510601303910b820004070802d2982d0107075001540e12101c20740d20780c0481c41070b0000c01c6003401c40c0c50300054550000030352a45007040860f140c040e0000c1034000000042d89034140a0302602100c038041c10f40070000303140041d0780805810000d41c000d15150b6114070030081544140c4141150810801c80020344582c500d9441c05591428283e41a9090381400180c004604e000505a81c4403420140e01141010003500070f90045595188200181e48103140c4401c0195000700555003541c2c00900184081c8040d046000d240440c0031205062080c00c0d0700700c035500c0c51190342c403c8600c400000d180c0c0701c0c3c94003c0c400c64018080041030f0760000e010708041c0403090b000410300e0540c070705141c0300d08600c015800421650481d001707007c0b9031030240b10301e41e16411781c844698043d11615942040a40000a80d640300e801074403485158146501c04540c503503140d80c036003089901c100d1558207000c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 158415881 1250 158414631 158414651
    0x8060a080708030c010f0b0f061305060c07030b0105120319020a0c030c0e06031c0e0402160f290c030703020c0d0201060807080f03040302010c1b06030b040c0e011e03 73
    0xc00112000b44211002144d590001008507070035510301d5983d10100d00c0c10050280403507a21761040c4405d00c80140e13205901c81e0046109840c445107164031071074010000260131700c0d50074404200d082c00c0e280100c0d00034400e40d030f1300c5090000c4015182003042a5410902ca40902c4001c0c0180f0b40c600b01c112881151301d40311803a1149407047c0c00c00e61048a441c484d0000400c9461a402c0e00154401e2007140505001e0000c0700e20160044414060b0608104100c0c0400c50150745070303030540d44075076800c02101d400e04226103010302d00400300d05130036951402d190040025140d001d1080c031405054003061090180c5880d43c4e4100c0503003002e000c02c0203264091060346140042000035007044103040c0c1c000b003040b034602001c0c18202201c0350088049a080a4541c0644c85070002c11a002c581d420301c0e04400c5c51040b410b01d502c80040c040900d26064509490000d500c651540001d030360510304036010016280c3c1d951007a100884042c010701c1c042880d48580c0b408580036128101c658811508001c1010564 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 158417131 1250 158415881 158415883
    0x906060c030f0702150c071701022a060f0c0a0e01030902030a031d01030207031718060702010204030b010e062d030a080301180506130207032105040b07051908060a08 73
    0x104040c420b200700042406825031800340b50412821286818882c6070a43c203240058030354079a4003c0e1501c0c9000341b0701140040340258111007407204a41c0540e100c0308d44110000301c510b01010718903021361140d07002254800e41c0c0049404e004941114503c2d1602c5503076041650f100c0105a80c180c1410b9895905070f0150310203000707500103680300741d03540e000b00c1114070100d803041034106580c40c2c1003601c1030251100007034102510801c4a280c003800b41030396554480341d0100741c0803803a5140d5802e000341e0084c040515015005403060b03038450141c44142e42c0c5c980840c40c14003142141c0740c40d030014103510945104a48501100c030070f04810795101c518101c12502003881c10f000d10200304d070300680010040182c44001d070220303241c03020240401d00150800c0400182e040010648403002c5550000d12502050b02130340f15956a03083e2001e42c4010750400e4411003000300800c99040e0b410040b03020010b0155441b600440d010340d8510350030284010340c406021150564018003c17600100e960b4400b10306590 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 158418381 1250 158417131 158417137
    0x2070308030903070302282604030803091c0807080a06081603110901030506071407150603031b080f07171207110a020d03140904051801110301140906060c03 69
    0x21448011642d0300551702e0000d1a058102c3d00407120b00300560300c008980781c240a40d47ca54507801c00c0301002607500350f8500d40d001409181d4144402080001d0000c00c221070400610320070038800007a01e0682c0c064250034520b00f1606080080091050400501d031613028200f4640c0003429460b00140240c7c4504a01345092034001d80c4007030071662980c0410411480d0321042e889103a04ae0340c44240c5514655511b90744000140544060010305000586921081d405a4030002d0700648105441201c060b010310003080140000d43c002884000c01d581c0007815600140d403815802007800b0300e1702c00401807903c01c581002e141150420020585800c10350f00820140c0302da00481c5001e00554109108040c02c100d503540485041500000c03500c802503511007003840d040e550142016070555142c020000c809200b03842019601c1032030030741402201c0c4c110600c00d254085c0400006c01101c5202d81414180c1d01003441103441941d114000382029003003030051140c0140010f8845402c01940300c6182d429a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 158419631 1250 158418381 158418391
    0x303360605090301060902160f03020f010f0b0f22150906081b031b0103050c041e17160b0f09150c010b040203070c060518030c01020d11090d030f0207030803 69
    0x1503000c42d0010051500784544c41c002c0c690320004500c2e103060151105107009101380094200d4251000342014035009101040c44103004a00801940006090100003040040d4105010301f080f10549161400c08030800449450100e52404130800d12480d090060145e108514040c00c900d100000760010b481c1c000e0342c01601411000c7e03c50341d6852072090000c800210302152090b845942c1c0f20034084c0341c41e101601004c81c20310b0003150075940c4a14100d0548565408135406000300300d01200e4010b8680400c00542d480001c3c7c0e400c4451956560941c1c545114414000e01c1c1d41c05070f810091541400e0003011005450314280f8104401130001805c01c149400c84104040c10004031082c2c064405e10500c201114211000c6086003818507004080c0c281c00600105407541da880031a0034805840601c901040e41401125661001a42080c1c040c0d000b0045110034981005180280c000c404c40541d1503c98015000a88000e443d4808440d41210004100c0c15402401000310210388440d00a45c450 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 158420881 1250 158419631 158419637
    0x1806090403020f0f15060607080712030b090702010e060c03010f350703050106080a0305120402190b1312020117071e0e0f090402130b12100902011803033606 69
    0x850750584102e100b05e04c5c024000d0f07100c1d44d010400000060300c4030041c0c0341c000b908442000d12059030480190000c00c5501d819aa00086800811180960541040110b1a540b000361103131134450000c82c0c1c80302d010a00588402e03208100d81401090700e00810051040301d00c1c00300c40704101032800b2080d4094002205410320b5040150107100f84082409044000e020b00c000500d0315007250303140181309000d5904044160ba0503180850306550b0303600d8103e00400341040103424420303a43c47d400d07182c56002006006503020342c1000051090704e00106050440d4068484130300c5c17250703031034140404c0800080c02d220500c0740b0304408448004615903910001441a00c030b0f42c040311565420014142c0131b200c88a440f82194500300b1005840740010080c51402010010607040e810000168a0200d5402485950303c609a11150a4015500104c82141c000c1c3c841c6c0129564485403034034070000600000c2d004c502c000800d0515001c500042041018440c403403040380c404a4558000710981c640d10403400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 158422131 1250 158420881 158420893
    0x20f07060b0108160806010c0203010b03060705180306040506010b13080f03030403120b03070501180506070c0e160806090604180b1906030f140a021315051806090403020f0f 76
    0x71560440e40250304a1400c50b04c2c580d00710315203c8000c01e02c00000382400d0401440783d40c07401c1103440940007203540c144010305031022482e0001006119812003884001c03440d03036240301c0308140d05020545a0207190030a000d840365078203180d0841e0b41c6034812070b0f103c500f0440f00070300028100d0741802900281d15461002e10394030f00345800d000301110424a40d2800080c5001000c015030b13036002480c4c4040b58401e0030b0400c1c0301c0d080c1c140c2812066203a80d000300d420400004508080051104102c015100c4403405080d01c2d40b01c0380c403035602c00c2c1e9809400c0300c01324a9810200303250313207083c1324055400b0380000c202081508124204280c1088034100489145140c1814006410200e501410f13000c2c10704001007001910f151506185120000005400c00009195021510506200c010492a00034040320a0f144d10103c0d00401821118800080f0103404000440d8a10306820022032005180403144155103c1904100404001520441c00c0d0303c5488958446060180300c802c4606072084003800c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 158423381 1250 158422131 158422151
    0xc0b01090605031002190e0103150e011d1003030804020d0609080307020f0f120310050910080d21020a200d0207050a061709010216080c0c0d0803130204020f0706 71
    0x215204e1240c0f800b500700f500612880102c03180d0001c2c022403501c02803034020070b01108040140c3c010045009030019814620402203202a03490a8907070490b0541000c1e030440445820800b1340012003a0344103041180b60071410804a841340130600d03009400100360b0f850b04030711039541000311880200c04540c20b60000c010810b1454041c000482952404006082e40c0c0e480749125a46a00403d001e100c2e41d070b200400452242d284008000004d440040e000224605007000c1d00140c4012500c2203614500c00c04828800c3c0034820800a185c03003a1000c01907900c0710707015170741c8000394003c1246081000302444e0640e1000840f002091005031810014003000700a2010003814601e481d0070407401a911054100015030380807591007201401c41c147c02030355845800615003e031151060b1012401c00e00200c0c41c043c0801c20000301490062079003108c400b1800d082c03d100645560320350203040100c0070f00005107107204905111604900c000c0c001413411002040d14040c1e43c22500c400c0d26403aa0b1544c1d450 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 158424631 1250 158423381 158423383
    0x507031406040b030c01030e031b150703020c0c1309020310150905010b0d0c020f070f150809420105010906110c010f0e090405010b010201050610020604020f010c0b0109060503 77
    0x1d41114040d907080c0a03805510010940e24003509102604240d03071040750407102d010500c16590645410000c2d00f100010007508981d50f040f5000c070035522200400041000340c0d000e071086030200c0003000702900c510240ca000300041103070300307000004000303440e45c0d0020010380d4140022240d0303a0294a0000e0040c20303040446400c500786400c4883e800e45000014030030084e083c000e0b2034000d0903014003c1042d0700c011200b2030502e9014000f40c5502d2050307d1001c07443d03c40d1000c40c0800c0c3e60f1001051820840402c3c02118100c07029506450076400c00c4500c4034140c01802d203100350f6000072078040c1c021401103e6440c01300b20403c2016000001800c00180015a40640144000d1440f4074020128992841503240c5032141001d0242c1440300d128101300d121b500400100a42040040a056040c902410b1260180000c401d1450041d4030386000200185030981c1c800055000c1d03580140801d0b0782d5603080c040b01d64480d0307444505001d245500000080ca0b2801581e000e0014560041006403030138080c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 158425881 1250 158424631 158424671
    0x12020103140a092102071202030c06070b06031501030b041515090f050703111801030b060c010509070b131a040b0705030c0106050d080f0714061509060901030308060d15050703 77
    0x3c1c0c0b0131080c3c40d00d0816107195001070401d003503074204080300c584140c2d00d1001030702c0e00c2104100690014400306900050003040c1043c180310b07480c141c098a00900840f010440711540900000780910448000305010810705154400e124001c5000001c50f4045d041d91850202813591011094544030741891400302030300e01910360407042509007480103884280d1554001e001d031440781d0311b40304583c4081a01d582c3c4242c10218485501800301c8bd661107854001c039001c4c1c441200c44030741501c90000c00013042c540c04801c441409090310065070515081034030107032240344140300010095109001c040740c2407a030003005000c035a00c507400841d0761381100d821503825210540d01480c460240c0e11200008076400908076108600131891903950780300d0900e4019041640304a401c01c96100341c0e001c100002d01c0c0400340202c404004c540181d802c0e62800e0400540141c2400010700140d150000300d61a400e00d1070001c07400d103103c1c90b000c40640e07030114964411900101d9501000a480301500409410546130f8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 158427131 1250 158425881 158425913
    0x1030f0e0a020111030a080c0a03021210030b06030a0308070c1407060503180d1205060d0b04060209030c1903060e15160305010501021603020603190908041508010e0112020103140a09 80
    0x5941040c0d20f110001d4541d0000900700503840c23000146400700c0c14404c0d07044070945c0c145d0085140c11410300c2482107518410b18001120a0404c040100d42145400110080e03c103074190740703c503501c3d512072108555617016440101d0380c8081c00c2d000080001d10600c200c0b00074000d82da441075103a280c44003800d032642520310000d20580d0000d00c04592500e40c803240c8500c0f90740c0e00000114070b5407681004a6008104070744e007e000000600309020400506400604440c5000c40c100d40c043c5620904001201b1038400d0b5a40500311900f50400000760140c2080361200a1807094a4554032981c01480114500b00c4003212210301040c4c2c1001d2171a014400c0d9405030000784014812203006403030200c003240b0a8013001c1d224410100000c0c601045c50840d01c003040c14a00402d0002d000c0303c0c03600403400d0b041070050380b54141111141111692281c4545230403165540c10200f06646841c929000d201c400e004182c2c100368881060b19608402c0007140c1c2c0c007803040f580002030110b8807070811400003054804 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 158428381 1250 158427131 158427133
    0x604050c010906080f07030911121c1815051e0a02070b0301120308090c040e070801060504110f091903030e0307061d0126190608030a05040b0901030f0e0a020111 71
    0x3c1171018045c1e030f03203901c3d41d80070a25040c0040c101c02c4a0901541400ea509040380c1d0000c14140c07030390140c02c030104a454600c88000c00d69229a6410341e4280c42030840702d086080080c040000401508001204039100e2101d1810103910380003c007503000717817140c000b00e6400f806048d00044450515504010174070044c500b03040b10a044d0f50500c810100b041c882100050304001c2c050011404104d403e2001925040d4004e00400004402d105040c3d21080284a04000744d4604000020942414000d003481e41d03d40720005449c2c440104102c0c0d80e00e401640c180c90300204d01030000c8002c07220b50201100503500a8840d03110900b01141003600d000d01a4000c00100b000650701200b0520000e4417183c5415030909081060402800700160030010074007000b00c000c200b00d000c0c00f041d001c5070050052030070412503090003000e40703460205942e4802e00c1494000150b0170002007204e508448040e003003001c0145004100e5810f42e46d0214281e5692061400391500071140c0d0800710f68005803440f8510510310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 158429631 1250 158428381 158428397
    0x504050402090411030f070609030b010e040c150c0b0c0405032a0f12030f1207020c010503010e130c030b0603161409090a0c06020c01110f0d0e030f0604050c010906 72
    0x5408101c03542c1d006040205110740c10005071140b0750b000d200321400c5c0000101102d03820344e80c4a100508145e202e10058441031403072070010070000c081d44203503803145801481c400800f0b0310308550740c078032818244140c5040180c10000f04002445007002607010f0308920f41c00f29220703401d000406081c0308106d0032040820403081c1018004800c1d100c5a0018004111402c40c10100e034080407810031001c41421030600d00001450807080318514000c1d080c1400e0802070307116150f8590b4400c0c1e80d0389501441c090b01103072060004114168080c08101d0340000c4903101060505895540c005074100c2d56001128034030590020408281410082da081658925101c03094171880c02c80c2015a60559403503560282e05090006030000b2000c100c0744d04210351091205d044a81d8400700252254094140540007602c4001e14450f1a100050010030001c6500c000d000b92840c040810f40720414401900c9406010b61241110314001c24441e0070700c100d00480c013909041a803080014080304460704003c00b480980 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 158430881 1250 158429631 158429633
    0x204140108060a090506060c0f030304050f0303191a040c030605010201053702071202061f080318030c120105180102070302070306020f1201180507091802090d050a0f050705040504 79
    0x2e6403d2004490081e000081c2c2d58899201107192071069880788003e41c4148250984008000001544914058802d4400d01e01c0481c0c0071645900c4143e90182c980e080e131305402c20720280743d90b005440800c806042c00346411340300e02c00b2600703032000d254a07203000c65a10034041200303580a000c1c80d54403941c8070620095141003000e22021412a0707032050294508454486144445940e04031041c0d6500880c004560740c001c898020b5483c0380031030350080070708071a00e00310340c1410549124906881404001d50305008400c0c00145c1d03141c02620f0100da151007210305612302c903290310080038402c020700e00011850f8508040802c101a80400c0c0c800000e03031040100c100420b41c0170580d0002c0d264082c5000d41d580d544420b241e40c2030b0003a0040e01c1c80f53380f03050700000ba00041c0f41048090301074550030148417644c0c402c081590b010b03a0341d10604501d002110620700c1015160360007070482050050602843d00015200c0c06e19014a5160803115a0210407100701030242c100204802004100c07001d100c18030341 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 158432131 1250 158430881 158430889
    0xc0e10080403030c1e05032205100b010302030f01060e03100e07090501050a030203190804050402120a0c031a010516171b071503020f0714010b010e01021204030201052803020414010806 81
    0x2c9171112204105003c808900307111a50101001140e518608000515089040c215151200c80c070540030350501c0c4c0540c19205502a000350703403281d04603107125503050703103820740940d40f189003592500c0d0700d03000c1d10b241040803503001e2150542050409004014060410604408440c0c06030084d40c0320300d00383e500410051781c0008154000c0f80145030700c80454035280c0b51105080c000c0c0c0d00020f034014004074481c4c01070201001414465500c4240c00d005240d42c50720305408a8145002c0e42c0c40e4001d52120100789540203c0c01051262405000f803046060315403034a620011452001b00c19948000030202e031076510814030300505c0203c4201030b2080d10302d401e0407140f0382c05822201d0000d142e0040f40128005105009036001c058018000f207604841d2148001d009000c1d1540c0d0740d000c00d40c1e400ca4803069510016025903811000f50010307146c41d0071900151200e4022503402003028a001c0f00c0c1c41207280d59880b0300c246406441c6c038003586860800300c20b0160310702c0b022110303410800c0e00401c0000d6651 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 158433381 1250 158432131 158432177
    0x10b07240204052407080f04030501061401080a05040b06011103091c020901060f020309040911120c090a060b03040209130c03031106010b0a020a060b04020409060609151707030c0e10080403030c 85
    0x203031142038207640d640407151f850348500559101030035651074600b0004222103030382c21190100009a0b2002c29a07914211841c04450342a03401402c101400d1307001603019401510001c86184018040300d00b428080c00000c0c810302c28141e00e882140000480100c110708000c00d865014107568100341e0400c401c4c0c000002c0d628040e08007440d200340d80b514040300c2880340402c225460300c500981000159001d80d1401603880c0d05441400d03001d00d900c02c0024411681078840d000560b040620418515290ba400f0041c0d0485c01806a160640000c020500010003400c44c890040d40310785c8809a080a00740109810000c059201e1242c001040040700c1100e43d0200300c1c450115072000c3c0c0020039100030004500240211307044a40e11500e4a480401c0458116041d80d0884e00e08500e02440404030701d00807a1381c0021071002140c10245003010400040c004e4010340d120501c2e5160005005000c3c3e800190210043e0703040320b01003070703003c03050006155060084480c10b40f2941400c1070b4101001841c250740070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 158434631 1250 158433381 158433383
    0x203030f07140307030e060c0406090605090a0e01030c030525050d1b0f0504061d060d0809030109062307020601090903020c030a030e1c0b010b07240204052407 70
    0x140c00150124055050000d03040300c100a959224540260068001d00c203030400c0444511410000490100c425802c07981076401c00e5072060f016915100b401d41d05a00024511079000e1184100807520180c64071229008500400c01c1001092850400c2d9052154400040c0011f08145064001642070500701808907001900c2c030940d00d128505201c0e000019240b410000a41030900005074800842174210655a00f1541080a10740e0381800e4821802541e441c1020741c54404009046441c1001e606084d040c0110320300c2e468415084d00090844948280850f04581e40b000c0340100c0c041c8442c250745165024a054001c00d003080800a95501c0051180881a9403a110319508061082c400d0001760a00070301141c0317400c02c082c03401400d04242d882150380600101c0907066411680b0581c3c5a03552904510075401503420301040e83d0555005c001d054030344042c001041003400ea40070036031410451a07200016115030070101009581b07001022800604110381c20302500d8110080c04451100b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 158435881 1250 158434631 158434651
    0x250503030f040305090a08060106020c03150a02070201050d05010b0a09091401150306030c080a05060c030c09130b090a050121080910030e0303041401050c19120b120c1f020303 77
    0x5540303615080b84c9501c91031001c02d403c1100441c00180451001800905031801c0e40c0a07030b10821924418980e5510342c00180443d5003030300c20041848400a58001c2505a00603d0a64a040344124850054450a0b44046d52185000031f005894550007222000502003502080c40700304011004c0506c401e00601a05060081c0f0b8100c265519000794800360046a00208001c5002d43d6101e1054860000d01415a031600031100060420344840e400c403445400441821801e05582800f4422010f03d80c1c2d608440b00d541c0c1c2e400082007607841d108603034840c1c885048086070540c1003507240c2d80c0c4032101c11406c2c001c8081003440034000802c10b1055541c0c2070001d9900342d158810b6448201d0141600d1041510320340800070510050005240304440103585020081c001c03901c0b841c404244a200e040214440b88080c055025080e0348540c0210b0605243c00c080441c0d11000e1100242d41d4001e8030925840d260b000403011009401d02c0c00707060501200c1c010104c81d820602881c041d459103c010100c07005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 158437131 1250 158435881 158435911
    0x106081810151805010314072303010f05090f0705011805040218101116051c1401020c010b03060906060109031518030c06180c091805100225050303 65
    0x200140d664080401001081c56683c0d00c125203071a12001844213020599000409024000d0b40042c00641e5170200c4400c508030b009440300b4021200701c01049000074079419520313200352800340c41050081601840d080c0026009414882003c00d2601501c0c2d48014144489a40626549082903134060304842043d100940d84001102800e14202c0c40303c1d003415403299692141c001100d41c000344560384000c00008a030f80403a0104201440301c400782c03240c2e9900c00706404002104030350322038604800e64428041ea84680352040303110f0f4203907040b4000f07134890360790368054000c145d140401803d500819502c010b4601c606010000030009001b5000140040281c02804020919594407840c0340118511640e4980c2180745401880742480640a4841c9070402c241c4c000b000324002d0304003800030350001d4084681840c1010680c00fa020000c032800c02c0e41b240600050201d1424000742035001800040181c0d19023440b419084500440e0002d200d42c2100c003411040007400005c11290044102c00c250b5039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 158438381 1250 158437131 158437151
    0xc02030418020c03030708060a080c0306062b1101020d05040f060e01170103060906050705360607080d1116030509040204050d050c01030b04230601110f060106081810 73
    0x7010307200b5140e40c09014070001040003580c943c80003540740580e1080b81c100c82c040c1c0c0d40d960010f644448400565030706030011804a4250f00d007200d00e008001c0744a40c0f030362005040e994410100c210814006035420b41040038035003102d60341032050811880050600138100703030400c90040089507082c010300b030a10049410000241e0302503510020070144820303446c400d07984c4030b01c1c1c081e01a18440304101c5e41c1c0360038600800d13403450040d4291040c400200c4809648988800344a082580c2d12070520018050900200146611020010500d0304d0050307591a0351000e000c1e0110b4102e5a0521050000150610a01c50692030f007001c6111410b41614041c0d84861041c3c0019009108650102c1d60181c240740c2c40d4000c000000c54108070403542603e0400080d5124010710003910381120700e0301c40504a0101c0c4107000070603800d00035008038041c907041c4150b044800426242c17032441c3c0c4840340c555000000401040d640003640b84e6000f5085c11017040000c03442040180d40da052488141600b90311039200348 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 158439631 1250 158438381 158438429
    0x80f090a0b22080310090b060a05090d060209180f2203030203071202030103120f09060507020618090c04030c120206030a0b2e030f060e040b0910020a11060a0c020304 73
    0x180d040d801c2414250390707050000c4140c507148094450340c035145050a06030547c501e0544155041001c054903403901c0c1074510b0717040040030740171108111030882d030a21a100c0541c480c0004a980114600411038880c20b000420300305600f8001c00b404c486d64545081c1c1010340200810002d145e41e03041c107000d601c90701d95003010344002c40b9420000e40354600c007000000500201c9507180c0380b4201c03d03031608285c0c5c040402003100c116015002d44004580c1c00c10a00c0010f045c504010308080280e01402d04c485008a030024140178402d030380300c200d0110f011031306209000c10050500010078601c1c0d91a940754810f5401b19909010007880881a142c1c0c1d901081071588556203511078804c0048094140481c05441d1000760421690028000071302e00300c0e211030201c0d01c0d840b40c038084e6480744d60300d00c1c8141e9541d5101006402c008055801a0040c07080c07031218403103280068041c0e0f000130b440b480c050f03001d0038100c1c519003100101402c1c0800c0c01c1590300650142c000c0100c1d01510386c441000940020301c11010303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 158440881 1250 158439631 158439691
    0xf061a032a090108420409060203040512070b0601111912020d0309050c0d17030c03060405060d02010c26121006020a0b06060d0b060a080f090a0b 64
    0xc2402810082402902041010000c2c10405000d894016482e104c0b0094034011020100144900300d040080c01c0c4901c016030050880900400501603016103080f00120b01a00c40ca56004c40b94107401000380704c200319061205102003441240340c107003482195280e01050700c102810310341c144400881d240074040b005000300c5c4040b01900c0c80c0001c00307000d94a050020702455848840040c0903c0c074020071018400d0160410050b007103001419851603038400c1002030014140c0803030b6510b015490086042118802440c800c0f180b0703540980e1607240c02030521096640c001c3c802482028198800c200607070700072002154098000c1c041040420255050703151651071003543d00f205500215a4404600c03000190901c114881075000c4d81c015030311502070760794030180344c4010301d0360516400007030b2030b4109140581341e140d01e1184040341050740b14000c503006910035812a00050441c1c0c081048a030721210301c450700103031020000c103041010790301d48800640d40581540443c00004081d900ca100c840d001c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 158442131 1250 158440881 158440921
    0x708090607030e0a05030c01021e07051c0302010501050d020d1704090f0603170702030a12180305030706060b09030d0302071103010c09030c15050415021002041203030f061a03 77
    0x345540d41c512030708000c0d2811000e00b03941482840780c000c01040b00d05001c1140c1e8280c0c0310680090845001c0e0b02c03465941c1e840c81010502c1c0c0c621665000149c984d440340faa03070076000a8544014204041801c3c028207580c016000507001d005024040e0b030060315910505554283c002c80d030100c0ea1013442068140a1042d0340c8102c042a090003921075082c52103034081d40481e4482d024114006900003c82c03c0d03c0d00441c40040d5240e00184060310104004a11004031000e0b1740c5000c40e9541d120101400059000380c000b0b540507840030401d842007002900c44d10010303000310203449080800c0540060b90700c02500e40c141003010b0700458640200045c00c8001543d50b20010001d00814a000a0043c4502c0035803100b42c400301d681c01b50000741c640e82900c5070145040c0641d2070601e041d0400015004a40c410351580c41144100006241400c41a10180026003200c00c41e80d1162809410014260340d00000f0a0b0240c5142c29010071421803000410350f4807003501e220194495039680141e1300f9500d10126 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 158443381 1250 158442131 158442139
    0x919030e030a02220e0a0f0b070903150903020f0106031e0c0b0417120a020a23010509060601030b0618010f120507020a150902030a17071a06010f020a17070809 70
    0x34070440c44541d407141301d0499000f09001000748a119488955655140c800040c00c0b10b191140554046110f1080280c2e10501c6130030280e0000313a480d5206803050b0321410a42c200595650304070010958140900c061040b64030300284050707400e40d103850702c0e040000700301c2001c105014203141d02000704c580c1d00306009121446049845540da44501110144007140c1030f4400e02031404140d81e03060204041d42d8030171070154001c14000c4551340d81c688040c0c20010100804456414107894030f95400d02400780302c0c074030a02c050071403401c1040001d0251100d210140b40700b40d0062285203805189402d404031000c00034a0102404180b40000303864105003205280100c90800c8100000340c0d400044189450b071041000541c90641c291041d0100d404c04c06000798181c21013018200030442c048601d243e6020383d980b407285845440c2d5203c02203022070080c8580250340d500108511980c00032000c0b060b9a400c0d0025102a907125030716101030520050b1800039207000400e1000038001484152000380700e0242c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 158444631 1250 158443381 158443399
    0x21b09101502120f04050108090706080a0504020f1f0f02240621010912051615021308061602010504050d050f042d050a051027060f080919030e030a02 66
    0x11303601601a07000303004480c0400e20f40000b250811000080da40105c2c0c060b6502d02c20310b51038196520700500740107001680e101c40c0e12b2501d10382c156984444000c00c181c1c0801105021802c40d040a800341002c4802d8206540002c002141414030389040428281e03800140c20200c1e58496000412150551181c161604030620520b0013151701540400d405501400d01c1100408102004582d18403170b40b1001f090501e650004400007881c007429050024440c2c050141c1884000c00c03116041908550041300d41d54000c009125903000e82005c480882da0403840240142e00c0e003038031003a95501134004081c0c10000e0009224200040c5a0150340150106403842c2500030a00c0261811140803041030307001d410048080000c0074500010303404102e42e00580030105811401d1001c0d04c82c0400071000126011001c00003030441241d83c000103020b804151a038041d6203950007402051050003c10007103095100354009110107145142d9035241913498541041300c0b041c080c1c042810404500002034010b4299 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 158445881 1250 158444631 158444647
    0x303040309140919050907090f02090406080d0503040f290601030509012f070501050412180303022e0e070504150f090203060d050a03021b0910150212 66
    0x401030020450b00b50460081a0560503410401c042e101502d81c0031040300c00c1c1003040103401d900e4200f594888241ba05840400d9230790044142562800304081d00420350000302003902e4546031041e84060200c550040074084600000905581300c042c0010f031080010740b010008000c40d90300d08200420070414080311941e12652504900501502c030361740406e0401303000510300c60051260742c103101140f8840710b00d1020030380101481d916002d84c0b140107864080180c0d0700441d40900640703020360f1090700322401594400800030a0f00d1048251085250400841000801e5000402e08245101d503c500d07407e4030b0745801200810030b014856035220506203081c268042ea80895100200e400944091040240b1020b054045030194056101101c0c0540001d2000d10807560207168441400761200481f90800d07203d0f64a02451840c3c11001607002110000300b60400d90701201714258251450103040c00d18403c038614400307640c050756140000d54000b01c0c003814820480714160160070014250b40341c0030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 158447131 1250 158445881 158445887
    0x9030201060e0c0306011d0102100204080d0e0108090c04320106020d0201020a09090906060308030906011e08030a08040624030b0c0c03070f02060405040617010b0103020307020a0f021203030403 85
    0x4184240c564250401000841c850080f200301c2e07220309416543d4464041041c0b800e1417141c040440d0082c114801d103902d540b141101840100702605420009107221400300500403c040b090b220100d040014000a00c420284c0000340b01c803246c0780889010943c2d0240b500b031000d0403044d50465090540814203900b04807407c040c035680c1620500e42c2030342d078450b20b80981a070a070b1065959031000a2403059003080812640e9000c00300445c801d03000030510311307900c1d258042a07400a4941007001c0e08108010890340c1491410b9007402250200c2120303205290103c241d40300d000c2d100d042428091050005001c002d007a0788500d4590351a00c00f0f210914107042e00c00004181540401c564101d000300c00b0031030400400d82940c94440c1450005c62a00e40c1a50b10020444040c40c03049030408814800413a456456000c1d8402412521440c2014181040402ca00350b8210140c6c140c141441001030142ca240e0108510390115003103145c1c2d84101689201050b03150300c813180d41c00c0582c0800b00c00c0c80205a4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 158448381 1250 158447131 158447141
    0x13020702040b0301050c09010305060f0406032301090b01090c0e030d050a110102161e0b0a020c0d030629040b190f0807020607141b101401290d09030201 67
    0x4000c1d1000c200903100d21003898200c94091b01c1e90509040d0520081748198465000503a0140c805088000700c200c000001c541a259070b81c004650f40e0600500c0d042c1d4036400d090f2041c0d50048104000e10142001d500e03544120107041c002d0302c1c4a90b8542c5820f00001d4000c41c01c02003205005421038415070200030000304144c2102d030384600000c2141d40303d80c149807030500944e10f9034456118000c10403000d50307441c0d03419580e48820720141100115a050b012032503001055108024615000d80d40b00d8243e020a41081e9014660034203052810409210743c444890346110882c3d650306d203149007207028004a050720300681c2e02100a40100052a074202901c1c0184644603000c2501c1c3c80c001d0041d0464160307041c4d401194950016801000000c0201c1d100304058a003284035070945c5444c085604001c08040d01418030689201d90003403d070b1110501d00382c4191180d808030031307503144055418040f20040c0c02d000c40441c05550103440032440070905500c02201c132848d0410104001d420b0039403134042d010785 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 158449631 1250 158448381 158448383
    0x8160e12100f0b06031512030a0807080c07050d03020a0909090804030204150617070c050f0a0203250b0706060f0608091002040501051204031407060203180c180c09130207 75
    0x180c1000e0800b03401c01414002c1d2542c03004020100e50455480400c600d40c0307032190f224202d030301807560a002030034080d081c8003d040038840c640d6a12844d1502e203002514030000a401e580c0161001c1051038080b81001c036800a00300900e240c090382d02d90b040c6204540c0c4140e00c0e001004080e10340001e10041142e000300401c102e920950301070081000b00500c020340707801113116620214182100c1c4030a00380c900b0711415803081060401c00d05400c400d44401d482c00504810980c005d038858101c880035480d0402003d54818450036a41082c180c52400c01030390042c2c0d034030804d0201076001c6a0b903c1085003d802450140903401c81c000025562400300034001001130b200c00c10f007401745910f0440c08140f940216011390b04180c42e06c07403600402261480040c04010000c2d400c01150a8a840350f05d1084801001c0d8903000f100f0141e01d030700700130350546081001c03074031002d100d64003c14040d4029110306240682c08186d07170a0070701d015a50783ca03807549a8400c003441d00b60300184030150b0807240140795014100076 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 158450881 1250 158449631 158449663
    0x16230c0105010506130b030403090906090203091204120b04050a060e0a060f050105010e2815110a0b0f0c04090204060f020f0a15020c030c01050c1b0d08160e12 70
    0x2a6603c2e0140b1041e4803820818144000980006200b01d800d0390307008640080c03091400207400c9a0b18050801280d00540000003404e400109000011400b040239141c81c031640c0400c145040d1400985c0c0a07000c011020092196443d14002403c0c400f05008004200c0d03000030b410701245d107000d070a598448013102c2c011200d8501e80307841c0080b0801030b0710070103051700d030182c54815108032950108403200c144605400603022649442c52403a03e0000178800041044c0c05885204000303410002d0f02010200501088a5100c0d082d0340c0042000c14422540000c95180515000e448a000701d002601c143c0c0c2002410340c0c0000703800900b10f5030200d180c1400c01e941c2d03800d0b00c43d40c0070641c502d5900c58024240160011081f840d2840002c0c030564010000c0303032070742000c9030700d4241690030340340c251602141d80c00e492140101d00140c6807a20a1001d50300c50746070b03102a14200034651005803041c48094011410b98800044021409005100380001900c004025000300c510303041000355198075250111801c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 158452131 1250 158450881 158450891
    0xd0207030c020108090d080a0203040609020a090b1804020a030b040305041e0509010e1902090303040504061412030a170402180a060f050103200309030412050601030308180616230c01 80
    0x14110b030200304441b0004255803803000d00e48072005480040e410281c02551820741d1600090010fa645501c143c1c010250039101017a5000b00e00108400344c04154121103582482c1d03001c010050303582502500903a584102400c0300343d00d8a0904603600d0007190410342c001c201624442d103900c48215041400c64104480042850781c0b07401072629609070555030012a0345144c810b060348210b036600135003500e400c0582164201555500003406643d0250b11440002e0b545418954181c03c0400404100c240c6640041d890901000f000401e01011011144001c09000003c01c045680b01c0f1180d140032000248200c1103070502100120003020304d4070401341204a2014001020350190050201200640d1000d0f021002d481c81c0c0c1e181240d00c0106843d896000801c40428603004010416001e540a40004c202c2c0d0340c114a0041c20b400c401402c107400d132210311201c9412014000400d03661100000c41700f0300184e88850801d50340d5506e80410740c111400f980d0740200000e41154050071221900c2802401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 158453237 1106 158452131 158452141
    0x30c121101020409050412170403030e010908030901020c0120040e040804050a06110d03021c09060908030a2a020d050315030307060f0c080c040501030e030d0207030c020108 76
    0x21600755a6014442440b01c004050355100407982009008023903205a04003c0c0440100020304258484845026840003908030840013544102c4407901da05020150310302070b4103c3c00c0c200394035600c0c002c0c00a1440c56140c04000b446442003410910302400c05803000d509003401001070340d103904200b000203030300c2c0c0380d0060010080170703d69500d080d15056a038001c0d0403c0d96980c40c0108050050002450005040c0c01b80c000e5050909000070b03408250349070000150003200c20180043c000481003110049641d0800c44002031402001004618006952040c2184030282100140e0044001e222030318025001903410000c8250308004000d14000001d2455103d500212043c03074031420409200500d6004000888009040102e81c0f403400312800d03040d500540c441d00c2e0402d03445000403000010700740b08441c004d101001066580740b8041c00c002e44048519a0304900003210000024 = true := by decide +kernel

theorem cover : BRFrame.Cov 158273381 158453237 := by
  have h0 := BRFrame.cov_init 158273381
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158273381 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 158273381 ≤ n) (h2 : n < 158453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
