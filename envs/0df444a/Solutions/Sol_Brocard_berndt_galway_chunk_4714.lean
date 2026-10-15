-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4714
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:30:00.809539+00:00
-- url     : https://prove2.me/submissions/72c20b17-938e-477c-9506-2476fd68cf98

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 847661870 ≤ n < 847841726 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 847663120 1250 847661870 847661879
    0x20c010f2901140d091a09060f06190b0915070302010b0108060405130f050f1510080105160c290601030f02030601021902060c01110c12120105040b2206 67
    0x119264090301c00900b070210b414a0040040205440f800c0401c020b43c0361030b0701a1808002800c1c041e40c00d1218000064649883c04c85003090340e034842260320f451119141008541c140c1080804d0001c00b148074085180f4290a0203503000c00d5034090382856401074008012545055403507009080703ea842640080f0b00b911105000401c02d0401400c6140319a02d0311043c09021410039420004280d4085d80603030340c0c001c0701e0600074100700c0000101c2a1600800c9142111075880c80c089038882c83d0030080001c411921144902d080b11411104a1219201e840c1651a082d00601000c070145100e42d9800110140c400c56a4600510550781608070310401803e0244a6030036000d124800e843c00c0c00f003182140f07000030000356a100302c2d111500d041d00002c20000290748407201102d022200a42c000d010050001c02d003461994040c9030005154001c5450300c480c60b510f0b003400c5960b61829000545c8040c1d081c4810000203000900d50594014088148001000c0c0b8a0000e9030b5091481e100001e40a49403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 847664370 1250 847663120 847663181
    0x10e0906060f010f030507030f050109140109050408040e1005220e0c030c06090f030a0b01150207031703090109051c110304031713080a1b060e030d03020c010f 70
    0xe00941e104030104401d00c42c1a0364015260307007941203d45008642912404015001000002c041c1c10f4002d040c00000315100007680c0110f0f82d240d00081c1d020841d41ea840f80b2100c21501c09540082908004000030400c2180c01800d090b0450b1600361012403595450700018000412003091542c0000c488444d07002112652092a00a1140d503024014400355480020b40310103480300910700c03800e00412030200c16115039044d01003140740641190701003072403420090554102482490102c896071411071481d20f10228208044a51024242188403041c0e4070001c095000106041d84940d40c0d0390149001c20002c0100404040c03d1440503080442c1821008042d00b49515103003446600030042080000c118984c1d050030101303440c80c0c0b2601d941100b1040c0c480e00b5159405042c252061351505020f0000d003074414180d400f5050700b04880c9035640d0100762095000754032102d5154101ea010720403464060b070014403181401c1c0c000040c22508040f0a030b0201d451a0100c6005100324081c99030a6001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 847665620 1250 847664370 847664383
    0x2010807020f1002031306231e0105061608070605010312050a1202160f030e091b030417091c06060b1207110109080f03040b180a0803040c030b010e09 66
    0x45201510180c411400c2c003da494410401c1e09450b03d500000140564400d003064948896100703009000380020f8281c114a450b038940740b00f450b88400d40c004180c520024001808c000c0b00f800880d003000d41c0c0b0300810010a9003110f200c00102da00c4000032800010701500082100310301c201000a01541142061910803041c00e490b07805021082020201e03c9401c0304844000c90a05000940c3c0c44c500c00e8000314184c824100000c054080003920710080540100060716000d0055440038500e03502d4003005840c20790300d00d081024885080000c58049511100d43c20f0103c1104202289041115400309910380c4010410090703c80c09460420100902e40c01500300801035440e42c1e904080340400d00a00d10103014000c8802d10652440b5403007100340c29041321007a00d8200401644642c01e0294200c420b0b0300c2114222000c42c00c48001400d44241c2a06e50100001d944000b0300d00d610030703540c40940c1640042c1054a0504000304c000000a000c8101d850181c1a80c080c094400e06050905d0381c507145 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 847666870 1250 847665620 847665631
    0xf010501030213030f08070c0b030f06030a030e040b040e03030c04090b04021908090a060c0507020102010b03010c1d04020c0706020c091303020a0221330c161707050703020108 77
    0x180104015000c00c401c410301101526001406501000179505d0481501d10a0307130340c02050502440c03800600e41e41801c000d5403140d803110754035200540e00d103020540c40d080d4401c0f009000c00c1120a021406051940c400740581030043c000080c00111140003034030b142c004680100030803500040c06c0c8a0700030035001b0080d00050a40c0e00b0b40c14144c00c400350300005503040480008104000000404a11003004072030380300d40e0001e0080010440080c8001c001d0f503c0980c0c01e0380990700b4400c1c05801030505101d40006072482d0760720a041c0c54101440081001618840d003640241c007072007902c000103800c0c41400020810380c0c0081019100c01000d208600301d00a10b8075254004141801d00802d4011481c00d22055048408450003150340c2c00303403422080160122010ba20031030040725440c18071041c00c001c900300c0e9190043da040e1012880c40a41c09400c80301700f0f010010a20100e4540560040898480ca10a0115a01003140807240c810650130059040e6035a0f442081d0800035960004d10040c1c000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 847668120 1250 847666870 847666877
    0x230d06060807050a1a030c25110f0603040c050f01090b030f061c080906030a0f05090f2a0d0c05090406150b0c1e0c120f07050f01020a0803060103090b09060f010501 72
    0x175920b051003408014002d034010704000682500380d000e0540d00300314000d0646001880e25200d4245a94140100f640890142c00f50001000341842c0c680141d0380307e15403202c007901140d8200024403482c86817603030940d4180158514086500c030316010145201d10094403002c210b501d8198100002c01300b030341300d03441e1510344490308110108044104980400d0130036140075070303203494802e07440d0010503200791032041d01841c1609211604502013014021480d1501c1110602c0c1200b051441d40e2070810880b0f21703411084050f1055050a01155111480d80510247d084465441000ca20b08403c100d40c1180c1c159501d00201030100e419030300c00f80c05041c030501d00030305010403094250f80c0d4140d00c5400701d11203071804002080f01e030b00c20081c7c41c2c41c264015006000b82c0d880c0c2c951169484102c1207030201207000701c4801203071504004c92455149541603000700000382c003903240c040795035002905590401d0f45480a481c04074078050b00a0340a4a1000024030302440e11141036500d0504c183c1105040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 847669370 1250 847668120 847668149
    0x90601060e1807120203010914100f170a06020406050703021005010303051204050a0c0b09120d090303080403020c15070605092a0d020907020d18230d06060807050a 72
    0x15164001d00c032503500040d15050355141c0b83c484003551821015200242c0090001001280c49000703a080740b2038800c4014000d0100d9111100030100300c441d5030041715003152903d082007015034019081c17a410000200c0075183e40c0540c944030750b0301b0f0fa801600500081900060717003904165040015454420510504005035415958024007a00c641c0a03440d084146031000319060190600000515542c003084440145990307200c1b0241c0c54208c41d40c0c1c01c0c49205a807644141a68012940d90340c21b07031440c2e42d2030900c14210b60303080d42e85200152041e000c52043d02e075202405c2e00d83e11448500c42d82c2c0914030a441d621f00c1e203070210a8503c0182003e039a60013280d1190004041c2e51003800b808580342d0891302c002c05054001c4bc00501c45210069441000d082c18005ca180e00800c400c60288030541d1083d4108203003070483c002c208064441c1c0e10b1811101e014400749810100d0360100d41c214010024280c1c401e1a0725036030184d4049420140c103a0300f16103800c02082c540322600c1c0300100504000c0e00700 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 847670620 1250 847669370 847669397
    0x90302032e020a02071806081f0b0a031b1403100c02030408011401030b0c09090105040b041e06030b0c0f0d0507090803030717280f021b0a05010b2b140a0b09060106 72
    0x456049e031401513200b84507402900b158850f00b039009801101e10281c0550f01c1e16560342456215896280009508902c0e48100880d12003e240070352056070401400506080d092007009000a00814404c041140024040405c02080030b00500b8418990640e005032154114144000303400700140044036001010400c64483e900e40240c1c1e1411281d04071800034100300404013040103402e0340c03081803044110414105034001c00f40e40c0400140c80c01012404843e40e240707441e8800da48201c2a543c2161036090014405840407074011642c0031b0480d01d0645082591400100c1c0703190400d965080c01f1600c00c01c1d10ba5041d000c001a0aa803001d98803c1c004401c4200c1116201c1042c140640700d444a91508032003604c2160382e404039200c1422900071500b14a08900809403140c16804045810b5401d04541004e1464003054440003001d88140c005071041c1140c0500310502080041101c00b8032030b105d00e50b00c03284400c0c0070701c044442c000c1c81030403210301d040c02e2024140201600301c041840003d014042 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 847671870 1250 847670620 847670623
    0x1b010507020f0f0307170615040905101109090906090c09150d05070f030c060906020c010e060d09170a090e04051f0e0109140d090302032e020a0207180608 68
    0x30545038180c9403c0c8400c00040007003410302c0010307003004000c101c14020360100e5080001e8450302c500545030f42e6450403110031080209540840d540a030542d482089400410800380c0c0c4071100d20080601d0440c81c019401c8082201a1012101c00702e845d00008100700c84800103119030b181001c012208200f036850005d18038415044030702d40c1e1600894403003102108102c3c00300141c5010781540da00504d51207507030b403a0010105034075004681c00141442400039030302e400092414000501611000040c52040044c4410303500142c4151580c0c1d0b4440c43d00c540840d00382c0d160580c00d00c2d01044d0581d40e950201d0030141c0420020381c003202c0c164210344e0420011800224000f00b10a101c80301003904a1f01c6929a07402410519002d6681c44d460545204104080400c1c0407602580242c11b88000e8800c0a606986003e128400a501a004850ba0f03d460002410050001d0030313400c41d03840c400c0059001c1c0141243c200384001409640004828408210417080c40394a02080e02d0303040c4074240c00d1a2466 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 847673120 1250 847671870 847671889
    0x190f09121a1e0a1107060603081c060f032a03030e0f0306011d2703030703062705090123060319051005060112090c05040e0d05030118090803091b01050702 68
    0x11000e940d0f1341c40003d02004450044a60082d04140c007481815101e00b02441e242e03004450005003010344071290404e03040d080c091007084905e4850001c4190b0320399200d12103880e14500e000c140a5154002c80e000203210320704160091800780d80c13210103084640c01803200c1e00c50111241846648480c0c010040c45400e89100e03542c148000012200c40c0e15480044100301c060040088026001181c110a1110001019601c00c0b0240d0383d090080b160366020881783c5044c10150a403004c0c98500b0640a2500d07a90481a088031164000003615071a00e0849441d04442241241001e4041801e0200500e000c0242c002000701034558002d4080711984d4051365401041030394003505031150006040c980c0604614501841200c40c2481b0703245041c5000c8442101c0c6014140c07140f0300d04903040300d070701c1e0300010107020b0004551141d616590800d000c24000e1782102c00a84442500d40941c240040d0742500503502a15403c0700070400e91050074100000c440c241251641003060074061140541d4880700e52 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 847674370 1250 847673120 847673131
    0x7060c09081209090a1d0a050309030c0d050c150d0f061d060a1a040b0a0c0605070207050d030e040605190f050114030105060309011d0f070803190f09121a1e 69
    0x2031b920000c007080000d10071145d114401e0768080c07c0410000e1200104c000d014420048040d41d00d451599410081c8010801c1800351250740035090f00002420308072010180c2009003203910303040004424117070301610b054102c83d0381d805031911805c1007640c50804100b450168a03040ca103100307140c8a004035940e0b2449104403101c425155036403421500f0b00030101d0b0040c0003400034065a442c2454009400315070001011246a868580011405840440c2c0780703044d41c80062418000050b41d840807160492a40401507215035a0180001d80c0d98803003003a400c0c10300c289054882e880b0715007246442007144580c801414490b824660034a802d051000b10ba055500c221141c544a40b070300b420302ca004100b02c402c110401803016a01000c06000047c4c864030010078401100d41041d00c1c3c0d203035161240107454003d99840c203801e415030703420b03401618500600c000303034600100e04070354452900c003d680c0122010b480d0480f0b80b01a1080c207402803210954042c1210b6640200e1048030420a010350000070300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 847675620 1250 847674370 847674391
    0xc0b160e010c0c03060504081b120906090103060806010e10080d0905060307021f0f0f1104050405061f0f1b020a0308090d060f050601180f03080f07060c0908120909 72
    0x22000c00304160f03c40c80c42d010b950007640401480c0340a10706656154401c400522045103588a04680d80d03c00280b0a410001c05003038282c00c0c4030069040c00560b81140072194141034542d000810400c03020001c0a00030000c0a1003c10130741007080032040c00f007001d5000840d298202003107a455039500034040c401143e4050704c00603a030760f4803a03d04074200f00410150702a101e1049040c951582c80030f0b040560901c1264a0800c02c2c0c0c4180a10381c811508055030090090b04140300030010340ca0242d210300c3e07100e040680180c0d02c0c401940103a07200f801c921440140400d0b003c070280011141d100c081d0101041034a4480c2102c00c004c4d170000340d2540c60603c030081c40f0f80b100182e50740d034903203507040403130f162a5001c1c038140082421580c060028000803103d01e40020244a180d18514089851140450380d4001c648400e503402e68480b40700d540c1c01072908c407001280411401c0c00142442c4904009100e050b0340b400f2089041c0081c00c1d041145103200075191000500c1992f032203940d002078803604071103a01e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 847676870 1250 847675620 847675637
    0x203100c18290f03040c0e070507030e0d050a0b10061713061109030f151e04030e0303250302100c17090c03032a03031006050a18060c0b160e01 63
    0x21150300c0b180310748080d52101c0000441404100200e151207142621107481c08020242c5c1c81d52002c40b45402401c50250000303020710000d500c035080c400440d5884500a0055800403201074950240c112000d944541c7c10b04d440000c2006401d500c01684003480300c81c041804018288640007400c400c85911015100f56a600c50000d4292000b800b16418050040d0a44500500d040c0d00652a610880c0103640381141d40d40000e18540c00b41c0007241140e8120149032405900c481d1070840d0440300c02c4244a816120420202c046880014042c2e4800c1803400003d0b030a014180c54000c0c1000301c5100300c0880c00d81031030155081250401d06524414a000403a01150380d503811040d49045410302c2d03001d400d408001240701d105500d501d40700046422408003034505036440040150b4a20084841070400c1103000b07000e004851142d4010190440c0070325288100c0d804601900c5030b180c80681c840404a0712400c034007000c0181c050b4400b03901c000d00c0514004044400300000c0c0040c2d0714501c100d8100260345 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 847678120 1250 847676870 847676939
    0xf0c0c0602090f120102180301020304032c090c0304031707050a030e070e04060c0914150a030b21010c030603020f1009031209140402180f030a0203100c18 68
    0x20340c5040006400401c4c54100e0412100510b0003580034100301d11001302409101e00701c1e0f04050003124041c6074190360f010740d450b250740300f2102508038940419030a00420701081d0f4041d61441401d0b8058980c5440e03140d46c030f003018900a4043c0d144407004002d0a0002c104012449800406498105115040210340a9445840320b41000000c4d080311900164800030b000600c0155130150303c0f510a140c0b0307604c042d43e407201ca420405031440000c650b444030300b1941c1002c928030b038140506589849801c001c40d1900a100c000f0700e0b5451010001080c01c1c1c155096119000c1003400344001d03451160404000881c00e68000c104c5401083d4082806000c0301089800d00c1407203240c00b0300003113400048001420040b44070051a841c0d0b80e00c05c4031200d80d004003401010345058401c03601c0500d81410038000c0c003a25041031000c0184e03000c408135070501450000300c1c00f5807001d1007690700344030040e900028059040c00c005400f201c070440400c5030a1b100e03281c080c86510400080c0e46042c1081400e00800740d04107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 847679370 1250 847678120 847678129
    0xf0f0c110a170609120c2a1305040b1003080403021c0f0c1d0f0a090c17010b150415110106050a03150e010c0f110c21010f0c0c060209 59
    0x2960300100d840601040c0b5000c640c0c01c0400c50600a440c040190b40c1010400600107420b40151a4026016000b0050320040d00341c01120106030340b5560903075410803620001c001425622004001800329413144104070800104003c800d501030b80c0004543c4d1b0641c1540c95118650195000c02401400da90081c40840c54200b410150391070752010a1040f40c0069250079032003c0d98600c10951684407941c030448010456418041c82140e01050301c403015580c0310707440d201516595800303640c0c2e01d20104010600b03180b00c203c180710345855500003103142c03074400c0c0501619841d840100384407240c09001c1800307003041c590b500f2003059641e07240030300c03160410011807401401c0590186a210100070742c000100002d000d000c40304001f13141c50410115803d181d85c28240ca1050740c0c5030000400d1941d003141b41c98080c41000c1c1c501000340c4115005041035101240c1d012000003600c1000342518080f0101ea69030901070110352841800c001c3c80000b4807400058041c0340d50701001060190003141441c00d6496 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 847680620 1250 847679370 847679389
    0x106030e07050d06090f0f030305062b020109030c0815090d0507033b10082203050c01020a090510021c080a1404060b03150613092604060f0f0c11 64
    0x200800406c16010007440c1131000c2022604007100440d046c10000360062400c000d00039481d0360394660f800e0400c10380306490380b46044440c800301c0c1400703103c000200102e0b42c0860032801900341e50008000c140350360004d070040c081c0010032000c11948500c1c003045403d40d0210685007407035410304001c002e2004000c244440341c211100c2118140750385504141c00c0c000803c61030200207100b543c03400d600040c000e0044445540444d04658900d20ba150160030703592500203201c9500740240340080c14417600d1452242641c0c080039080002802950382846645031403608089120818001480d51a15030344d444010590a1454001441108400a003481d80b0740d401a40c0b19002648030350b05107107031a1410000600d06090058003e1007141c0002d480d82c60302d182082d0081600601860138804110150320203030000020071101c107501c441807151a600c600842819840300540341c5034803030341401300c0102900300040c031a10403c00b82000d600040c0b07030090110107460340c0007460400c1244030103000c50031829 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 847681870 1250 847680620 847680623
    0x812070812100b070b0402040614031c0333051210050c0415080f0901020f030f0a060503070b03061f0c06092103020d05010f06120e0c1c06050106030e07050d0609 71
    0x10000034582d4104680c45c480248210720803202000116240c518003000b4100c102d41203038141d8040c08144042c88140044001c50303405a00d80400c5101d120041410b0017a003500f1800180b0303d00304840860500501c0c03030708000d460145d5010300030404038003040703079600d400d11b085018099031500407400c2c03481e00ca02110007804902c000e400500e0f00c01c1700010640b030f20484100c80d0081d660f80c00f00300f03d0b400c1070084030f1042001001813411500d5900b40c03c05052406400011225500c280008098405114400045c06822041920b902d844002d00c80c492403c0c405400640f8076255443c42c10b250840b4a00b080300303401640024003d055031078010071001d0000444201003203107032039600b80d265058000f0b22120060034002e010341c0e603840a105505107140e01688020a07040b109039a070400c0d41e90f00c042c07a07500d400401c546500c940080424500702c20301d02054408450020001c007800114015030740140f00300d140400c8205a0790041646482c1d02c1d0144d58071030500550000240a5207070040101503 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 847683120 1250 847681870 847681889
    0x910030c020c040e0f0d030e12031f260a031710090f1a0307050a27050c0306100c080f07030509030601121b03020609060903012301081207081210 64
    0xc2c55816915959005e540c2e40f84040c0b84202c0540190040c400d01902e218081660020309a000302041e2070966508014403450340d185580c0300321107604000185580c010a02d084070043c0f106010340c15802c0860340300c403441075554800001100025481043c00f0030780d506480300d005140d10f807840c820304060a11341c020a441800c02a801d0700c2140d84d50302c0850500114881200c91404240502d40c9440441c0304040d03020b141d88508000c66004800c0000d80895202c0703105005c041e029286108590003500c1140ea00e20020042001504124103100003441c0503003000e000205241e5140d210611480716158100000800e0920405024000340c2e440071341e0050640d80c00e5038540c407400802010030b14083d1104980c224000d0521600f0f5140c00d419240c0140409107811140d00610035203500c49106141c1643d65411040c019040074080640741010001a600b255403400c41282c0c901207444124101100041207000000703a81ba200312503c0204144419010b6595003584910316507080e48400c0f0031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 847684370 1250 847683120 847683131
    0xc030b04050a052a0f030601090b0403030512060418081b0f06060306011a0d15080102030f01050909010c120f1401030501200301051e060f040b1e0910030c020c04 71
    0x70758030720f0b04840d215070400d40d0001c4002620302d50804100e84031101142296a04000070809040d540000350761066040c104481d90076600c2248020550080d401a00002e801117a1360030412106241c03181c004008540c03d02c8003a008038100a42e020200c5002018403100250301d1360218800c910903003100311000f050f0750202e00c0f0407203060340301d440484400c8d100b80204000400c096900c58203070940f90aa034064141032074000e291100c01007206401c0c44500c40449140029816000d000851098181100b0031416500d0301050056030007010f020044242d04040c612907440c2d51001c000381c420f0620210208170404040103040041240f00701c46800c03480074900100602c40c0c150406444006415035054201e03c503d040104c0c140000e00800750300c5241d100d50484140d58540d8214680074008207100d01d06070610781f41c6107460f07000d5030000c1e0016902041c14081d64888a010420102e05015010316002e0002c00044070003050303600001c14503503103c0f010540d140c800c014541d80c4400140c0108107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 847685620 1250 847684370 847684381
    0xc030a230705010b041d0d1b0605090a03030c0509010c1e0f120f030615230301120212030702010c0210030905030706021b0c012001020723060705030411040c030b0405 73
    0xc0c105005640e0b0145040c42c80345000d03c000c00320f1b603200c14950344c07000c0c2a1400c6066000c58044c05143d003c8201448540c3d091000f14007603104d0680100c0c185002400751040c20301e0090241c0394507810007030130b00405001a201603608480308408a46d4400d14051f403c1e0303907105080070403a4130a503000e0701140300001443c3c100042c18420540a405549800d40790003c0d113001201542e01c2d60282240302d916414444031900c0c090420b941c00b09084e141d551001125034854800e07190026480701000e1508407403800c040d82480c44540c40003041040281d458200c498001134038821660000a004180c2e0f5060301c1c02c1d0300d110703a21503110503a22405480d61841c2c14182400030750810841c5a45d407417442c00d9584140900080e880b04007030010b8480382ca0000682200362030b00c03485d1302c5501c03400e550200000c900044101003082442c00300701d0001c1d000a40c036140b40d58507010005004109000040050001003840b00c03a42040d0024120b6000c07405c10410b03602100502854030250750410f050105101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 847686870 1250 847685620 847685623
    0x6050906010515210403050705010c0216171207020604090c050d0f020901080735010807051504030206130b03090c030c1c0f0317090f10020c030a230705 67
    0x50495104542d007048a1400e0504600c0d94440e0002541445498148200d89104c0401c0510791007802030829505200302c07511024203550480d104400103810030041030b10030088020746035000d0f2010609a541002580c1c0007241d07105a203031807081025402203001c50840d615001203401070168018140812a40f40e10064101d42129801c0780070709007490004200d008191081d1040040145c1da08001c0781c8403100141c40e96a0201240c2001c240001c00c442400b411511880c1006070311703094070360407075850041018100850364015030701c00c8034540c5012407038003103403005d4034281e0740c04650356070342d82559400820060144d54040d655000740807041101298003c24001c40b40c900c15020b80b00201c0076801000f01d0088090807800d4034198903403040010071591440510380c640300e13051a800307245104103001e107504e90850303040100358005520070b0020347c024042c902c04104070040c250706140d206205903803603004604158007001b000143c1e500034801000501100d6a240600d440c0c1e07a00300724200203 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 847688120 1250 847686870 847686883
    0x80a1a191e03050c100206070806040f09030c0c0f180203071b0609060c0513030f020d050a140f1501030803060a0b3001080703140c030105150f01091a0c0307060509 72
    0x5a56070f001c0d180e0204258142107542c4000c035a45c60703002d070003e03590b0050107850180010701722641141d81c50307403100090501440754107a858040e854088003100b4500d40070b402256607401000d4882e04050003000800080141080d8001b02c90307502586a0791581c404030785c600d100072a0000d43c0841c80c0c1c414000d05c6103076884040254082c01080c40038114600007030f1428072a103041c082640e110142c040020a40740a9441c003154401080648441780c503484131860401e07040010b4603a0144107816400c02c2008101031814541908058010f0454403c101c1100b0b04051202504036003001001540b0b80d07650b04080d4000e4110041c100b034844078491401e5984550748500001c0c552504509568004107180c40341c1e041b556000024051207041d035032203054000262400c04440d101e60003551406640a01400d0320a01060724200c40d01844002009103c520203e842810303c40c0b0b800c1c0070f2110440300100b6001c1c0c0d5502d034003059a01c07107803003859038694030502c00c002d001c49240c2028409507020100d0398 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 847689370 1250 847688120 847688123
    0x50103080d050f0105010509010e010302070501020d0203091005010e040312090c08030c0f0601030f11150f030403030b0d11041512050c032109010807030603080d0b01080a1a191e03 79
    0x2c10031551144a8000c00074000e0040c940810018010340da07066208902001c66240306140140c10116150b03900c3d401da0304038801445882c3d4000c0100a4412301c00c000400300c56507035507400e0100354513161802ca041100030303001404001d01a061440c101070290000610b0950000f08410001d03500c20801c1c0c0c5940003440c0560081c0078650802041001c0001e070941030700e410000003222007000f9074039140170028441d1200d40094820300300d00010240c032800b40262805901480f5601e00e001e1900804450160f24098403070041904028046004d0f101c040240070015940082c1c2540590800b0b0458940c07a40409412500c0201c0d0008000010030908000501901143c51001c10155440725012600e41140240300050006020035032141c000a0b400070107605002800303d03140c0d20303100142ea04c806900d4420a0f00c905118500c0c0d40d001884641c00a015102044045000401aa201c400080c0780341d01c02e841008140d04c1c1c0d440c0040d00c01000700382c3d030891052082003856480b9490203d9100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 847690620 1250 847689370 847689397
    0x100504110c34181d060415050604090305030a151203020102280203032e0303020a1703060a0504110d022101060f0e040e0f010e0307140a2609030105010308 68
    0x41c540403080d41c000b100b10540c1e0540c982407a0f9242c0c00000c02005041d504000e50b51500b0007401e4000070001406518002c0e406072140c8644030105110444c2aa0800342003d40030b503142c8190600440d5000040da9003101c0c0f0385a010030305980c00340425241300200e41001290800b0380501400f055015030052a9040c00d09800c0b060300246100c403120305100c0c1c041c6410140e041040000c03c6401d4100389000840310b000800040302c100641c5201b68240ca540007240960f00c04010141405420640003817019804000c0e649185449c1c000310300040b88501c07480b070281392203070761400c1c04e00b43d400c0c10b5a207070300b540100443d140c0320110040c120702400000f02d85045880034001085042c418110500d0440d0300c2d07214034a00d11030b204240002001d2981c1100c0044c000c400030004241400e0280c0c20400c08000001c540b40e52417400c0c80e00300c2c1a1200c0a84046034030071034820b000143c0000740e2035060582582b00707402c0489214000805807140d4007442e070f419403900c0300100401c1120005004074000604 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 847691870 1250 847690620 847690693
    0x1302040906181814070e0a050a0b040b060a1b142a03060412020c031c20060f04020d0b0708070f080403020a1514010f0302041103100504110c 62
    0x72640110341032000d40101035898900202c000c180b042889141136a070b00b6040320351155603409116203024007034600301485600c40040c4000c0e51202d002e030400e00b00c400c4a0420403054500001103003445080f0f10707441403000040f400c10b450700360313401c0108803a82c1101d000c040b5140010240f5403100b01615401844c9045c800112084040b4000314807007a0002078014030494455440c0c0d1082c12031013040319170461140d240c0041098805100400800d60300003000f8100f1141118060302d40644503481100150242c0d40b5a941000001003454007e0f45010580c5696160760002c2480c841d00241d005c0c0c01d48411400748405035902100c40f81c800d400c0342e07540426140507254200d44900e006c0c0c2e001303001640910070700c81c08110000340200e42e880390b000001076800e42640e9240580c101c00d07408141e55503c4508204158141401041e0b82d00c000200140e203945864008506024100d020b00340c0640d581d0382c401c60640101004503050b4a140e0001c81d460315078148042c442e1005000a205d088040d0714 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 847693120 1250 847691870 847691909
    0x18020907030e032818120c09150504061a1c111305090109050105063708090f010e0718091a07120b03031204050c040c090306200708091302040906 64
    0x34045103400c50080401d07410301d17500d410008218542d03c20001e84902002d1100042c07031000307501c100c0380c03140103150640031498178020400c400c840156000e0344604c2441242d10412194a80860340060110350010181002d40c1107214010009a4601004004005449860b964030a000b0340100c0d40d0849540e55030b40e0302e859410003624003e01c54960404000e120740e043c060305150f4011510000c084001c00c040d0340e80e0035840c00001c10500210081484c40d428482014014072100d04d03281007050007440624011151103654168a10510300000380610902140a03150b030804031115401160071650108205659410700d4002d88074400800c5500110b805040d030b06000340001141d00602841c00c042420ba0310807071046d4000c0048806e4024110a10072540c2c0f148100424400760750b032030444180c25440e000046a1480c036052001124000000c40600600d0044403022584007041540303441740040845d202c021131451103c0d08034004603011071862080c1e0b002504940740e60102802d1280032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 847694370 1250 847693120 847693127
    0xa170304050d0c0f20040204180e0f07052116080c2d011211030105100c0507031103034317090d0b0c030601030501060318020907030e0328 61
    0x210f140200641e143c0365222011a0a2071030301c4c1001c4640240724061902d00038001822a030068000d203c20801000b4440d00060151180017191200711000300103400100460540da1102d62050500c200820240306001c01d07800a0f0700c58a500c10041106c1503078540301003c0f488501e4a0050205920071141242120b141500200060705452002040e40074139804070403c13507060500d446810712020080030344000d5518440c485a2030b50481c0e1254880d4104000c00100202d40b654910400407000111404150041000012039600640d1413882001ca070300441e0843c003e1603581000c04881c42031480044580c99a00c0e404a506602c841d0600d500f60308007002e0004800c0005491506980e040206818910000b81a9004014401254183d03280d83e500511901100d00c806000030110510001d03503014062a0301401e2207080c10301404248a2003101d000c190300f54003038480c20401d4003090800b07010398800209051100240c9980e141700140c504044a01ca8894801e000560104203181602c03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 847695620 1250 847694370 847694387
    0x70b090601061e2003130f0311011409040b1201050709030c0603060b09040b0f030f0709200304020103050402012f15070909090206090a03030e030606030319050c0a170304050d 77
    0xb25929407519400c0b000b280c0002110094004c2c504510040200d0305409200381c504800a10039851451015401e52802c0052103908240300f43c14002c1501e8032010320000001900c4001c6819900041e000707103618002103c00c4901d407441d803003d51800b01800107160303100720908282e07409050035a0341c265a403c2d044084a0300761040c9070b200001404601802d00c2c1c141c00000407510300410015100c2d0004001a04114041c4107900c9960f01c200340410441c80140500c031510111582c5500440300b400d50018424400180300030304040d0b4801c005411a030082c241d50342c10b100b4004d907035601042040022200d4140d0291040024407400c3d00013030480e01e2060000703118440643d00c40300d105261503184000740808d0003080b640704405026040060310361102c1403000354000d50306c40980407000c8052508094026041034020b030000c2100d6410b5814825074601242068501541d4601b00c0440b1030342041e03110f400080c004895a003480045051010146026901601c10364065605100c0c059a1418 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 847696870 1250 847695620 847695677
    0x1104082a060405010e062214040b0a060305040c08030a020a0618020a0506030903120c09120c0603072613050d03090c12060b0904080d110f1e070b09060106 68
    0x1c408100c01d121652007070b1020341009102600701801e20103110403045100c0c014801580051040c0c403800c110407040d801c0400c0002400380c4040010000031404941000e00b00e0050206254488010608018200350705400034141101607a464034101c440c0291a044407003c142ca910703007813242d440c1d8002e40340785803520f400da801403c9401c0d0a1400090188a40004203000380d2030106210341803e0200c01c1510510424184680b140c1d502984d80800000603488483d140065100c001c01c03c0c2140c0720ba508403034112000f03082040c1e0250700c100301c1078400c125a0003005140c9400714203202c0c4d00001d9440c4060034904c00c0064902c0d80b642c1c01021030485428010141407407240040c10040b200b00b0f0140b140159002c0c1c1c0c0007007414681d400c0421100a81aa412661840001840903200c041c034490140d044c480c0c030034003508d000007a41c00c01c0b11b540551506400b80c5109407840404542c1884100da0409a02220002c901e161203040d581c0c681109110312404900c1d080383c040c0940203040014240315 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 847698120 1250 847696870 847696879
    0xc0a0513140f040b0306061203120421110709110d0906020702041404030c02091806040b07021c202404121422051503150102010902030a060509011104082a 68
    0xa60700c80c7c0401800000c0f00b0f8034007159000403c42005000503d100c190702c43c5018024820454405210242d01c1c096000742c1841049014240445c4483c404540e09045507051440400d01c6003000c285c102a0380b013003040f440f409034540f0040f14104641c540240481a000300c030308002e8580700390810100007104480007000103414641c10b000501e0906134058205100390b1040886494900c900c0345040e1058400340c58802250b0200000c865040007901c1b1000301e208000c143c4109403070009040d80c014120344403d465405e0041c0034851340b00b0028124510160100320310307000402c98894002030801c1d1003d840240044208081042c0103000100700b0645d951629888c00502c00c070b51134554038120a01ca00d001043d12000076043d0b0710304070520907003402d190b102990381c20481ca41e1078201c200426040c4c15a410f00e1118030160340c0c00301c3d0340500719822000210f415a1406a00c5004040c80f00301001800c5c00420702060f0840006240c40240070701d61041d038120084080340710b101e14400300c1b0380381d4403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 847699370 1250 847698120 847698133
    0x1180201080c0f190c060f0209220e120d0b060a0c111306081b040e2a060a03020d0c030504150b04060305061317090105030c0a0513140f040b03 63
    0x1140000b0042800352a407030344007414142c03060400580710403000400400100900701c5001480824030071500282078900003189030074a5000800c032803156030380040100c405400040c070003596450b0040c1c541c0741c03500c0c000e8414100d1241d40d18809a000400715805207850b03c2d14012080c288200ac54500350003980798825550155603a841c019480705040581006000a400340d5400b042e00580000c0c3c0642d07805000920b01c0c41e10141c0904810030300c0e03a8815824040314450412010400005402a00703c9284080100000f020054180d48001c40d0300184001f0344219590790640c081d2040030040c10f001d2082d01e0006a044041c0d45c1c06840181a220149092070380c260002d070b100114001c4060070100712980c2c3e0b500d4080c1440b40c21610f040b24a600100748c04100821425a000c0002c141c0e4001c900703158050000030498040180804022140060000c00080c095000c0c0e8804a6240400000080c2c607280001c100b00710250203d40103803003280e150641c9250070301a1029204002d0000c019 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 847700620 1250 847699370 847699381
    0x30705030109020f27040e0102120106111507051308013e04120209060a030b0403180b36010c08030a11210a0203041509030e030d09080118020108 64
    0x35801524103800100040105a8000c0704031071020354201802e010380c4000400c680c0034002524840048201c1f01e174410403848000000000c980340c150369051030b0540b0301c0d40c400d640307043c5003100b412040840c02d140cdd8010404681d0b801002001000c04844110100301d9039180c5842c261160000c4440344916290070210701202888203665900c540c00c244504648050896150b06501c02c0d04025042000400701c0801d5080205801c0c3d0400000c0c2d8400c4451032079600d036800756a1005d0320044c00c0017045150b50503540d0342a10408080c001842003d039071000c0032401c00c5204a03122040082500c910a611500b017030401659115007a810786680302c1c3e1012541e42c2e400f45070b10040124000c0e9540341c0e1a05023034480c4070040c000001009500311200c0011803070507000414014481c01026004204110024070000d29100c1628001500428540113510742521200c440c290310381d4040c8036001304103c0481d40581100d0484074004000c110050750310001511300091410040e003c10341020108a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 847701870 1250 847700620 847700639
    0x1120b090723040f090c020a0f060203040203030918060307050f150708120c13050603070c0b0612121201050319081c0908040501080a1b030b01020c03010f1b050307050301 75
    0x2020b030668000e12402c1c075440320000340c0007900940c22024000d020a801030101d103800e446500005960381c001080780d00100c1da0341034120040c8203401041103402001007021502c01308240c481401c0d005100c105800b0004081e00018072045031840c0c481c0c0318000c030019a600303201040b2807251034040c1154240380041c401e040d002c1d6009200858400100b082012810461704c4c0043d07000319016483c80d543c0e034410b01e00103040551550041072283c8001c0060142058000000070301c8a81c0c840c110b45095036070f80000460440001d0048140c0f4050742c005011070081c000d006240981b0703007005001d030603625081415940d40c0001c43c10180320701d030a0140030103e500100900101d11052106c010b40c0140c0c601d805040d94003540c41116481c4021400b03100560704001c1132680051211410044c0145007680d01840c2c09030f070300c3c0d414103256030b50440704100d91083c440041c4105024000f80044181503c540000b04424501c81003242040380ca070101e800c0c4502d086a00404841c1d9a16042d41d0a142542 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 847703120 1250 847701870 847701887
    0x504090201090e040804060f03060506090d0609060507050309150108030702040506120703060f05061f050a260708060105030702030307180314010f0f060b03130317090a0201120b0907 80
    0x10380c144407200000203214503901000d2441280b24692050f243e915011001d081070146122400925051010a02041e20340d2030540d4800e49003201c50010302815400d28100800140304040c146908101c1004079407a002070095015080700c0d01100c040c0c00350701c0460845081c080c00b40b1540b60300108111b602528007904095000344004085c07070314410355004064070381351466104841080d1070794407408070404188070b150b500c40c038141c1d02c1044007511501c01040c00c40e980c0507030301c1c207100010824440443c454070b0b4081a0b4900c000307200c030400703e01c1082da82e07039000d00315038005c00208003c3c00030301994807600030303a406910700390001d6007103072241142a503c01c0f0079403840c61200c101e06100000481c40c2141106a0307142d45200020741c03003980200000039221640315100c2c226080010070040c00c0000c1c000c0b82d03405000e010f081ca000e081a86022966664030700c8507032080c0d20480c0c06200e0044404280c1102480c400d89603010b403441c0d03601908003503801071706103a54001c0d041c000103000c103070140016 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 847704370 1250 847703120 847703123
    0x10201020c0c0d1b12060b121e160305030417010212010e130f080c060906010f09021b0d1e0e130209030c04050901150b04080607052d030403031410050409 68
    0x1030502e1038080d100703a1440356184d648a0220301d45c0b4014090188410b43c841d00c00f10140a03502d0a0742c0320200803541d5500c1c148001da04980340f8450708240103035002400054101035804034100d0106549003030855607500b050042d03001007440045002d030100300500c01c503105d03201211a0102d60f40e00c0d00c265160420801031503000f82000d00200140041d0f00c01d02e0342000d00f44560300b103688614941414514000d80140090a194000c60041c0550b40072124800d003100c80724400903954980e080220700e40705030340d40b0341d42580d4403a50101c034130000e80180100382c0c9128003c0140b10a0091010b007125041c10304441c09420a400d2030345803100305003a8004101058002e009c0b502d0381d6064401003011143e00f22a80310361650f42c3d103204440e100c000c202220041030405205814581080d0f42d02d62926409083e220a0090009030209039080c0300c4101d108000e00f40350100b12805c080c16011046500481e4200c000030318249080c80001c0400505038050001940d05140e00c3d07042500313020040491000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 847705620 1250 847704370 847704383
    0x10513050303031806070306061e0c0c240c020109060509191e08121218120a030e0307050a061107020603010f060e0a2702071b0311010201020c0c0d 65
    0x42000d8a00304011402410402042c050720700c040b9a13507a00301040605680101402c0c550b040240b02d80c04216a0410001c0c00d0314121a9080544150784490000200400070b40b40b18000050001c408849803640300408043d12aa40c000108100c81d214500b080c000d022900d615424080075200c0c3d00506030b00e03c0302820341d824140082508880c03906059014100e00c130300c6e510b0201c003400c2008200e10024581a80100203903021910a0380490152011810452005100091041d080303110010318161006090310305002c0040000e1950b0b40c440c1c0103480120b0b0600815810b0100008100d03008180c0103005821000303200d9030f6000141c402400c0602504109100160241c0c0c0e84000441c001c02c080010b2280307451801a0191a040180260300c0c8290600802000b61000120038010b800300c0030800f030301c0e8401e02812824024043c104000d0504607200740342c64405201031007054240e0740500b2401c6144050038004900717030300c01c440e04400700b90406801c500c4e103401c00440c1140034511a41 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 847706870 1250 847705620 847705657
    0xb010c1b03210207170d08270c0f0d0b01030206130513060504150e1b0c1b031207080d09030c0f260307050a0c06061e0306060806130318090e16170a020105 68
    0xc41e123851580340f001406031160094100303071485140200000004010984181c000c0300265200c0b4400d4030b0052101174024100003c2034104100501642d1000d00b00c0181b40851900300034541c5c400510b200d029281c020707441c025641c0102a002c410000c211600104000c11a59460100d186000741e00300c0b00002c064800d2011080b440001d000304480311007071002c0100d0f0042010b040519000500011381c0c004e0000700400c1c0c0c00b08541c8000c46c2e030a150000380c040f5030b0036501d18040390700410601e8094000c0c0030f0b090000c4200a40b4100c42195075000085003c28140e91540c08080c510058400d000825000c100b04402070303010341510640c0c07034061a000186c169840301e40d0401c560600c40c00040e8140c2c052014420803803036104880103090044024029490550701d035001d40d0304100000380a2210ba6609070b0103034451003003600d002e4803003498248500100c4045241c2c6d1050301c1484400c00c2445600045652200240154280003140c0d00804000c200340d001518158040503a03201000c141c003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 847708120 1250 847706870 847706911
    0x604020c120a020d030f0c1e180b0405030c0f030714030a020402040807081b0102030405040f0f060f061115010308030603070308030c0414040b010c1b03210207170d08 73
    0x2402400c0c01d15841c0d0083c000101d07030008002e01b1034400301c602950142c501a010260035074044120101500414a000060030341200705460801c070b0404462100b2100d400c0c04100402c00c040034004895050341101c0075030351001e080001d842105400d03a50540e00c03648003040054210030840c1d483d9080035040c0d03003d49200d500810181d9006070041810313070344882000c12800400b00410200340869104444080301d140300002c1d140c0c4a5480f4251140762211040c0217028a540d128000301030b03903124200100c541d10000c0c840645018841d110105030b6210040401580114800030146810b4083d010168290fa0754004160005400103030184180740c4040001031500c4000c5000d10f4021003510703225440d0010031900e03042403107200350045080c40c1301403150303076080307854003444a03403140c0e105600d066148094441d5912a50000e0304000c102c1e40b001c2c5401004000c282d440510341d81c00c4d103004a45400e00d11120301c1c03e40740c3d0b00303203154420b149080c0e026200e410740c242c1066030706149902500c5207 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 847709370 1250 847708120 847708153
    0x60c06040803060108010602060f04060b01050d0c020f0706210504170c1b0d03020c0904110316030605010503060603030406030f02090a08030910080610032f030a05090c090604020c 79
    0x21039045403036100000070321031150303040742c00c443c0184280e1001b04902d240c12410714420020180c001400e403034980070282c100380e0240c8141c40d220a03010000b04605402140001d540d806407514101c2203000c1c140000c51914819960030a0040100003010300b00100118058001e1000071b00c00c2d150180b491090448111503400202000e0354004000c06200e004074a10a41c104034040c1d495100d5007141c130400c0c0c0040d03004903d00d040810220b6485616031707242e050401d012101c0b8420303070394940074046c81719201c1845000043c0549000b1070080005a81700c80a060366101c0c1074179055407550040c4402c11a0030300c21781180b08941800701d000340c1810301c14004142a0f580c00c1d08040d00a03000803035100d0150420803401c0b003041d400c1d460f042005040420105a540d081b40741d88108140c0c598114550011a00d4126003003c2c601c143c551901c4510b00002c00c26540043d50304d0a8000c1c00c10700030540d10240000e0740c540680000700380b43c071a61103503010040250b105550381a60741c050b2440d138250340c215 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 847710620 1250 847709370 847709383
    0x40213020c030310090510051207030204061e08030403080f130f1203031514010f02160e04030219031b021305010b09101e11070b16151a040b060c 64
    0x100400641c0c6908040c04601c00f80081c07071704141901ca01c1d0004000303800103098284c00880e081a83c00c4200c2152580b8442e007810351580003c0c0d0484e003040e40000b17683c00354200c2d80a144245855180131292120813050700c902c60391002030908403041c08507030203441c0c0d02002442e6882168139034030501035541d441c510302040c80758440110f0351304030802e100a1540500130500c01c400a4107000c412107040030100b40700b80c1e0b8924000b42c10404c4c0f07280c1c02c0461300d000300700b0407200d50f40f6000380800341650f0312409400c014003110100c00600420307081c2151000c0c084a290b444c00d505842d5803a03064020400d21140135241c43c0107917800320001264040e00c0b411803043c80d0103040c994605942d20b0040c0340510218004015243c0300f040400f4560104c241100c0d00c0880c0d1082c3d480c138207550060020030495103005403e41003060b04100000e6901c0c4c4c4409610326215800c0e01ca501c00c0b12080001201c804201e40917100c5801c104400034007030000501d880d50240940301c100030704c032609005c0210300162800c0e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 847711870 1250 847710620 847710637
    0xe010810033005030a053402011e0c1b0804060f05090904030f110c06072907050406030c300f0c08011410020d03090507030f031d06030606090904021302 67
    0x540000500015103200c2c061647e11044020004548181e203400c0d02c110300d21301040d81002080030141301a5518401c0d0000000404010090000c100240c220f0347c00400650312080080340070b003c84e90a6488805952a41d031a800ca110b10b07040ca46404000d40d0540e1940c5010400c0000410403450991788400c4070a0085010759104158000c00c040e0162055500180014041d48168001500c42e038865003103420302e0b54422406040d51645100103031041181c03010b10024903a002042106469100e4064411507981da80c0501081d0a11300e420341d100c0c40390720462017008012080c00354080007401c1100701c2e41c0401e004d000940c4261424003500711009214030030000b0b1901801000044096034004114120455a1107480034001201030740d0f940080301c1c0d4030185070310303180103405001c0140103d1005607000714420416030b5951400920404110f4000c1440c1e072089045100c1c14103110040c1d911920f00900040d00d099030500030407100000040c000ca0340804240b126a189400c21f001400c03461 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 847713120 1250 847711870 847711877
    0xd0b04092d0b010b1e0405030a170c0a0f051002042103020a0b090c150a051b011b030f0f050606030106050c10060f0f140f0609040f09030503070e0108100330 69
    0x25208480c0001d040b554a03000900d810501b400305002617134010903410a025030101d0502c0c52030210160520032030050110190543c0501125101403094188101c500c1ca40304001740c854200007421004101d001d11b0040a103c6103541d020800500100040c20050700e0103401290030300c3c107203641c4003030300200304482401c0190000c0c04402c0041c18104440c030a103280c003064003410101207010003001d40c02941c1e0040003201d80c01e0550842e0300400e60200a44802c6004a80602c007900e18003c0e02808060104203401032402c0c40d800e2100b4064814103004810040a4616603440c0c408200c071260010b45001009002d659050100e2230a5442084003c000c541040d609007858030b1010a400805c1d54070046428045400410055071910190f252142003140c5154a40030f0039000b02d001007015412101e203603032404100300185034120015622552584d50b6138184210101b00440c0d10040a0301d80ca00d010385420740500c000340c46910f440415129101e8503012212400d1842244a58019500da012 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 847714370 1250 847713120 847713127
    0x261606150b0c060a0207020d0506072307020906130605040603050a1a0f06041e0914101a060a020f0303040c060f030c020d141605030d0b04092d0b010b 66
    0x44000c120450004200810200b401c1114180519440d0100140400311440d40040d1003411503407100e0000031000d400c001159620f15000d0806405503800c0d00380f8451031400207140b000c8184015044880a07a805030401101d61119018000240c45804501c0c078059240c10000c9402d840305c1c880e4000850003100202002c0d400750900095107500e001c02203c03104441410800340c050762400d025001002581c0000e1200001c420401c2100f10584488003c14280383c0010300b1311005c0c00d04001c50442c00b1b81550861440700304c08108403240e0749000405440c1e000362107160380c03400001500d14180b00c2c3c01518904403112115030300796402110102c846803540c9205200c40c030b81c00100b001d6501541d003000c01c200c9d80070701c001a5a61014695100030000008440d610591645086e18003021401ea01170303005903490b103003003526074100301170171034010f0320303000c004010740c605400303220b140c140c02c01503400710a07400502410040c1400d4040340c0c000001100e80030005044400d02500820143c0c118988 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 847715620 1250 847714370 847714391
    0x9060902150306100503061314250903022206151106010605030406090c05120a0201020606045007020c0a080601150207030503070b06100309261606 65
    0x152440101d81d01600005004014090325004c450059164841c01c3c031a4503a9182400180d0034504074288140f510304080410090524811495001d40030440c4d00051140852840700d100c0d0000c54a4440010500241000075044c0342280c8010a8024048407122890f200d00ca40192380c0c00f03501c9806034000615030406000c1d40718851a42d00244a03010705095490414001c0c01400b010b8000340000b039440400404008126100d00d008010250400d000345110307640035030320350b130400304281d0150045600251243c80c0511800686a03043c80f401089018810102803650710912010784058556003038052042440c600980f06440449a1840061601c080003e09080c0851260390060880f140c0c103004400001ca81c1e03605582003480003408403005600128035207103150340090140c0c04005184000d00c000d04400170f00c582002d89115051140c0750b40d0032400c40307100000241c4000340075100044c00400d2006404000381e0b220711203030300300030043c00d0600b10350702c28283c1181e1040d55900303601c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 847716870 1250 847715620 847715629
    0xe0c04060b0918061311070203060702060a1a0904030c03020f061005040f1406010e041e020c0105010f08030f070305070b130512070b011415120a0b0d020102031c0f09060902 76
    0x181418003251100d06800c007400819603111000c40103005894030b50b0b5016046c4400c16055810a903001022241d060901c0f18010b519410305448110b2805d0511a079024180b004850052040e00050102c0c1c6160384c498500719808080700d0760450460085d00101c2c0108801001058000d5a0386100a040180350904110032038007144900c10304a41004180106002c2c00c41d441980b108080c240341da0b1105140001034000e08181c00f500c024600d989006d80c2e14a0b03144d5001c0c3c0a0001074100070401a40c8843d40c84085c0300741842001d045600c00c0010b4403154100d8000381803c1071003030a01c1820729229a8404113915400c17501d82d105826400010401e00004000500b40310188c400344916000c915100c074206403205000300da00001450310800c08649502e03030701c001303c0c041c0907000c070b501d0744221234048101640607039183c150030342007081e5001645041035500c2c0800d98160000e41c40c01c000520464400880811034480e490784d28050402c08540900030654420300c40c4070700240c200c4484c4101b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 847718120 1250 847716870 847716889
    0x301090e0714090601110c0a06020606030622120905100210050a061406031302040519060b0f0409180641060d140123060d0b0a0e0c04060b09 62
    0xc80440440b00c410303070001c2e221481081d0700b00200386055000326400d030441c146801040440f082d084110300d8030014030b031030740814a81e010b00c81c21402d9404580741c03100e2a000d610179041d0200700320b030341241c0a400003805440a299285d0018101000c02035a5031b00085e81d04d540702c08040e00076030054422007500210318030841c0d501002182041240601b070044490300d5510040340280603500c0040071503410386503500701041040c2e00030401e11240c43c0c00d00304944241c00d01c04010058606203035010170300d10802415030750400060b4811900305440d022110300a0582d210050245070750f25015000401d59a0160b80704024000c0c8248082441520807000d080b1411944000d0540d240c400ca200c0fa1505104031a40104c4200c580b281e0301461402c000c40d01c00c88800800744190308c0c0201c1c1080d6140e0312038201c0d0781d0712000c03034668845581d03500600040500740900248240102c000203032150650303501c039564840340c100848949045081c0803e08072159a08004c4a503040810350021600e04403800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 847719370 1250 847718120 847718129
    0x7082a12180c010f03020c0a03111507020c0f120d031a0d080a0f02160f03020a091416120e03090306060105160201140f1314030307022b080301090e07 66
    0x401e003150a01d462150700c40102d0229941040030034800b01140d540b1a4058032080f9074031a0542e002540907142c05410745100da86402c8440c00303103450340c40c1a0604900c04a100d60181d4025202e0000064100507000b014160f0f001d80c016284170f014000180100625a00c3c074200780c4000a044c1081d00c3c054400c0301c541c01c1014444d8a46040b01c4d0000341070703142941c40c051410f0501c0300d1441c1060009900b05034500250340f45072800c08070005910b49000610400312802642c003002c0301d94a4001c120700380c60341c0549048d261010400420000d010307500800d4101d640c185000228000115050300584803039044e00d54030307540302103510780750f44c0780034008141c0001007400c00a00c0c00e00700b1450302083c3c0041450180c184074031000c0b03a80f11460900c00300c985143d0750041060351b0304c030903415291342c0490502906000e0000f05e03500c08100e00300001101c03071807900113040103451003541f820503c0c01040380700500000003103501000d0001710040c020b5400391480314404100301156010062805105512 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 847720620 1250 847719370 847719391
    0x6130903050d020c0111280309020f0d14030d020304230604030e060405120307033f15060c050c0604150e040605060408012c0607082a12 60
    0xa4000c0219502e680442c8030240c1c4a5440400f140c0c01440d9051a000740da035000142001c58610341c4038003000001404641080d96131100c20304600700d60900380025040403500c041104a07113401c0c0c074031644461003880c608c80301100204c483d07401d5410504543c1c02c90758011040c8000c2014404000c0c01c200e1403202c0604c41c10010700169603039000040e00140a01c2900480031040b510340c8411034000c0d220207043e440c4404500304070103030340fa800390606800080c443c5081d503802001a5002420342210224226513011107861510340d66012040c5400701e0594038041e501c0c80400007959040280203503204c81d45070515500b40a820251900e1300c8a10411081000f8880502c40701030718100f42d0024580703c10308440b0f00000c98014a0250000c552043d030205001171041d0054105000e240f018101426928107040c2200402081344d121a1440303400000010303c10b01e00c20605c680d4811100c00051503040021904445018502a50310350b480900207120f49904100c1d144864000e9075816 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 847721870 1250 847720620 847720631
    0x16110f060702092e080d030e03042709060501030b07030c120b0d050f0c010201321f0905150d170f070606080a260a0818060405060613 59
    0x1400640c40c0d20030a44000d00c0307112104041a41a01110700c46515004000342440036104c0c0e0001c0101680150320034402c45d0710405c0013940c24507111340901c0100e031440700000c601341410220b50700c140324141403a10300a4a181107000014100c2402143e4106028480026995044d03050103000c011000781544285030400001c6500c2c2544903c2e03d452404a426000440054580001e240c088440401804611421060b411280d00c046010744040d4001d0b0001c1150980e404207a2609961039030035550311021419403d407154202280007540802104e0351990341c0141c6014206620505130002030b000d0750342c1c0302006644882c03406076040101007111000b00d10a080e94807540301030078036050713841d2110020424034540507110301541c07612a400388003070001d0350301c605500b40d030b0700c030300700c1d000e45222110b81004200b84514041d40e43d4008560110030b450820b014405560520019100103102c2d031810b08d0307206920005105981c02544500003409081c2080c07010030110b5101c0a60300300d42d251925 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 847723120 1250 847721870 847721899
    0x117070603050a2a141e03060a12030306050108130f11150f030405010c0c151d010e060f0a1418030d061508060306010b160f14030301090f111602040609021611 70
    0x310382c8101b4002d440314080e070350f50744103030226507400103940c0404096925120240c0070150540c002038242c034000e80e81c031042030b640d16440c0b0b681078500310009021102c00c5180803020031840e004c101091b06014100034202800307070a90380803a81c8008281c8485820101c00d100802101303001e9104011080e00c0c003c80d03a0441da0710784040fa60520002d0186280ea584803103103079000c50501800c21791300280300811800d07682d00c100720f8603400200c880394016182c00700000c40100c0148140b030b424158500c3c0182203030b0b641860010032000c4e41507040080b88814409030a540f440c44c002c52000d049504802061504451005072401c0006000c640c4207811100060240c1810300d4141c0d4840101c07030100008000031030400035800c810a94014060040d600e2101c1d41032000040198100e4100e800100144a03640c640e00e0101d0b400c1c0e44c0050901101084074680034a2120700d0303818074034002040015226a120a01c100302e0b03015512410341d00205c01100400e2200250305030109000c183c4900b2016183c0c3c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 847724370 1250 847723120 847723147
    0x1090c05090f09040f0803090703020108090604030c140c13141006020d181809050d0203090102071401030f0e0d031103040c050411041a120117070603050a2a14 70
    0x100c441074000d140780e0700084c003800124401d100400d600701c030305583c0d0707402d01281d00c98440d882070100364007150100340810f48652002410610580c2c16548a00030f0807040d54841c4161000d5800d1800c40313200741325205005681e0007407102d40241c189040094250000c910103803000c017004100301c000320a1203504105064010075803140c0541d144c505404a4411160750042d200066045010071407401c100c3c4a46404003640030340400760040c022503d03030780724080c0101e90b02d106400700c050050b004a21304000303412546c903854070300220505021400100d06a441d60450380302c0d02d00142650310154150720311580500ca075004040c07442c0c0c0010f24620705a15103000381c144c21300c13405001e41e5440810f40809202001035901600ca41650989950b040600d8078499030042403c4510003500c9100008140b244880e8489100080c1c202610710313946056816801800020060b0441395240c205032010525400311080e651109a40558410f103466100140911002000b0240201c02040641d080400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 847725620 1250 847724370 847724389
    0x201081504061e03020301110c100c0c060e0109020906040c05030f100806090307111f03090204060f0f09050f060a181107060915020f0d020315061201090c0509 70
    0x8400300c5126030398680c20081001441142e00500046541420000c5500c0f207106410045034000c41c004e00101c09410081c0c2c1440c4510200181198030005401d5580e4003c1e40141a0082e010700300050307070f80c405880e400243c0b100712681c141c1c580d541e454071404501c1d00140c4550842402e550411a4140c84d0384060f085100107021100380713201c00c20000e0140343c0b0952100340079200b0841500c07400d08040c038540c1e44d01d800182c1c040302c400503007144c110820b0803d0402d410443e502000d00030000310415109600400c100c0b6401c5c0c0e0080e4840d00c0125811004505e03240c0180440000241102d03e412050303801c88001403e400106540750003400300300d45d1603035883d80a640415100590b000c1c8140025070003403083d500410070524000c200c44003400b00d00d0b4407601c4030600555000c851121000500e100700c2c8109030340e59846600c10f0100013100440c59010b1176000b8209422210413400d050300140b51500410b918a081da02103070010302002c01c0c24040c0d0100b021460504904010356800010401e00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 847726870 1250 847725620 847725631
    0xe0c0a090b0a03031107150f030501050d150f0e011d01050a05090d05030702101503111210090503070206070803041a01060e131d161a030109050c1207030f0c0507020108 74
    0x1042405c0741003d008103110800c024030201c8407801140c41810f00c0a1f0006007a03444d0034010914020001803d820200d43e0b62500c1d680c020342405544858200540050101d01007030301115603592000442c0e95000d10500c400550726901c21075003842141502d0b0700b034900c010140b40400d03045c103080c40012a000213509030820340f0340c24205d849a403a81e400b24600803115000700707a4182008241006807039642e80d03d2050301d00601c05a01d410041c801031007405800c0074001d8603542d014071a100c08407042540540c1c24144a401503d1514441d07400140d92274015000a8450076000000d0108221079a071118415680300070080080790b14018001d009100048560b5000c2d40c580403405c0002d1034282e210907446241210b440d4003401881c034031103a813104480d52419241640781408148098079806400e81802d1049120313256038241002d401c050308015100d122800d10600005181905990100344100119940090b80103180c0c50034200340c482224400051000401905002d030741e002d01e155a010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 847728120 1250 847726870 847726877
    0xe1516030618090f06021603090b191d15040e01080d1403060d02031b01120209030a1101020109050d03090506010f1410140708030117061611100e0c0a090b0a0303 71
    0x34981800d0410707001c0c190060041c0303124400502c603201520360035101c0784c1180c0a540c0c2c10400b00d03180c07002b00d18207200303211800781520810314441500c180b14070030141429600031207014803011203402099103021410309521a1081c0484c2c00d0040c03983c1c035000345005106030320090102a9285001034000904000700840020780040050000e8407001c20080741c0c540e0140031104c1841480918506211000d0a0075001414a5072500309000907402a203e51038070043c041c1c1040611580d40b040400b07115417556040d0f548641c1138001180d4240a9041c040f0390b41e841c04036402400b80f524900744031050f000410000003100c403d020000e40030a0b07800009105460f411200c0300380e5242500c00201d10980d8030500640040e6100800c58a140950304035882d01c10000400c011000e843e0313442c0c2c9800c0391001051142c0e250700449951180840000f914000e2064402c0000c2540c1d1690596140040b1010158489034042200f07040903100c450061094202c10030094100300f0014411546911014007003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 847729370 1250 847728120 847728131
    0x70c02010c020a06020f2b21050f070210060e18070305011803090f03030e0d060b040c03060e0a0504021f050405100e0315010308030c0d0e1516030618 66
    0x1164041d0440086490b0010008603a850355460001d6480490000440b4540202410442013044075101c817694120f414001654242070018111218940b05900c03070318500500c40002c41e1500b080c4902d0740242e110a80c00b0b40305e032500d184040c0c5006d8104114002a40c0380c0701003002614503a10340d1030b0b0855003c1d9080031034031041203452460100283c0000e001940707400145200c40c1c0260300020140f51181d1140c0030785a07078031039004c50382c04403900c000350110b0b50521030042d061074884403030207009100ba080040c0e03030a00c03c00420216038800d003416012030759404052058048402010b94050041072050059140c00d030b001c14108021010800c800c1101000d0b009404d038001c0c3e064802501c0050030103141150303081001440000802e407400d0081c000c074440801c80d401c2c100744e0a81a00e802c050014a075483c0d50b0030600d401d0303000c01c00311185107a0316001500002c2040c040c0c481c1802910460001a0816200300041d00c4c0c001034520061514200d810001042c06410b510004034810400251 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 847730620 1250 847729370 847729373
    0x6021b07170a0c05220f0b01120501230d0f03080109380604030611040905010f060c03120e0f10050903160204020d020f0c0109030909050f0a05060102030903070f090510030b070c 78
    0x940c5030f031005905409820402c541b03450081a50126002e140300742d0310300c1d0b8036150f83c1600701c08840084c05a00c0f103255000401c414100380e04805009222409482c19074000d07402e84440c0001d0340803040840014071243c004105080150250301544941c2c640c0060111541400301441d1168180c80007100c20032400151400b903480c907081c1c80003140c0000090180f1107103100362007003680c0140102e0403550b00d040c0010503111812a803500655032581c54000514100b074400340c82030714003034407480d44568955000582500f01807210f40c070188603520043c07032140e002a9020068400043c444082a4011f2291001500c08400b50b10922501501d0040c0d40740700b8140e00300040e07c80c184101604040c00240b01c00b6400701540000c2e03019029903980403031300740c42d801000c0a07a1416260300c0916440c5001107014400c0310740c40a6007006050049916020711200820b041401680c400d01e401081d5070820403d94046004065100b2000840c3c2260b907400c3d5616101d0101c0c020b000c220400c405180c0300c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 847731870 1250 847730620 847730659
    0x9040503031b0412150f0f050405100c1713060606020a03020129040f0b060304080a030b0607030e09090a02040f0b0111070521070b0f0d0c11071206021b07170a0c05 72
    0x101914041d46c82408040c0c00308994001400c4151022580c1d480786a0303000d082000940304105620207156035407051854910501c40c9105405460444109810351117200000d10701d12a11000301b06070303009002c0100d0181070180c01c442c0380c44508000742026500f070300030000420b4948203020008a41c00281d58030300001090040c50b00d2581c030381d00440300006000900c1800320141c40c3e00d588544d814410b660075a020300c0350502588900502244911030450043d240c00400c89034032034100350803038100d043e00e0740014090710701840b40c4103512999049909025640074080c42c0c100d000c7d19001380701c020700d014085031580100c92402c0c0d11110b40b21810768015201030000c00010090094119210207020700100301d541e02584503941002d1415810901c00760140320090468002c4801520b1b030355140401102081c400000d007160762903403c04c16035070340c0e9060384c1c0a50b80d02802d250003000540d080074a00c0c8540c4440040a0a250340412103207000250600c401c642901c0082c1c84c603110b10b051968414 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 847733120 1250 847731870 847731881
    0x1c0602070f03020303010e0702010c020606060f0c0607031b020111181908030301140f10080901020f07050d020705090c090d230c03010c170c03060a0509040503031b041215 75
    0x1041070340c1000c03460301030540c008040c505a690a00c2039501c1600c0e0341d0070a070300300c62401a040c2c01503003203200001c0380761a001e0081c04e941700158040600e01100000d245007090003c6800001003a40d48442d0350703050f800580315200c0b401c03070b60008001c02e8000c803040391924007400c1c0c10500b2008800c41c511425440e00030751040c0b84440c245540804d00c0c2c581c042c05450703800901405004003012044003804e80b070010407a40b4400c2d005015143c4011541c00c0071654900c0003070110583d903400b04070544103c240d0784020000036010750007600c181210060000d0900c1a294016441100e98005100b244501501161525003084903003806000a510b4800030f011003000b2108144008072081c00100d1002140b007003514641100200203022001100780d41c0800035210407103030b0740c22410002e628100b54000841c0c1000300100700110f03440c2e031000000d0b09030104640441e83d40e0001300901c030700007501c5481041100e2140800d203060508000d142e03003483c50400b50242c41c0e00380d408100d00c0d0300f2500340e010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 847734370 1250 847733120 847733123
    0x203090d020913050a0809090a180f0c05060f07060e01060b2205090403110c060309070e0c040902070f0515011a030403140c0a03020c0a0e010605030a0b03010903030522021c060207 79
    0x55800e104400c1c06c09007619000008502e00900c01240003415468041c030030b010001c01541c03007020303c46002c0d4a42c1c00250100309800c450019414074041400e544003409040c180d5610340c9880d1f85c0340740d903140031740c20341d0101c90300d40e0466814001d051110a94070010340e81d000100c140054410003210382c01d0000c01429500854000c644002072005050b800544c040c0301c0d10003031045862078000c403010b10007648421100c410998202c0e1000b1300594100d030081c103400c03551a03400d140c14039880c3e4409508990001c4012140032401c040180f00700041409100600ca810810880c0300e98581920200c5624444084200c6074030300200113420540104204800d60300942e4000c1d4460043c0d0070340c035aaa002031041a03025204800c801c11f19880c0844601c0296111040420308507441c0c61801c1e50107420142010511a490300c00c07003400c0d51024441c00c3c405a009513804506c0b41040903e1000d1800440c012071009402801c02c880035031505800d940440004d031f0103500000c4400d0402c4070007401428030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 847735620 1250 847734370 847734373
    0xf060b0a1b0f0c090c020606060a1b02060406030e120c030d02030705072a0e0c1204030c05030f09040c050a0f0f17090703060e06040c120807060e06010f05010203090d02091305 77
    0x1055051103203003c410b00c00d460040b5010082041400010f0380d540408030303103141d0f00200c01c0000d510000c0c400c0c0c4108401d001004a43c0e13500c40071076400261940c0041d00014002940d0f1034899000a04c1000ba030071202143d890554034104207507502c50344a1003685541580c8603000004602240c0c4500100c42580d9004000404108840d011107a401c1c0e8009034080c05940840c0300c08035a00400110050180c06614101c9241ca1100e04000b10426001441a41800032001c52040440d9007440240aa410a8462540da038a00c4000704022a84040c20f000c080020038060744920a40200360602d0480c91801c0440c94003d1191088481040604180b903c2042400600603198800203010301a03910038030042c8105842449425034600303044501a141c910514810080c0150540101c94a240504030031450110542c903a04280c0d03890782109403d551125004001c0c00c0482501c10020f48000d20141d8940bd11a000088a0014100300039200e00c0800005c1503003140100c0d1241e404691280 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 847736870 1250 847735620 847735643
    0x7230301020d0905060c09010903060504050307141005010b0a2c1504030b070c020d08030c09061b0601091b030b04020d0e030301030b01080a0c030b062805040f060b0a1b 74
    0x4810340b000c3e00016008450501c07601d00480c9454558a09480240c001a500c20b07060078555210600030708000b0700140c40c180020080c03180403801c22840215030001c01402080007004142e2a80103c2d0390580c03042803008014001d0640040d4810110028014840940358010302d103640100b0103081150001640483d195011008820640c40a04100c0b4007584c2000601d60320180d055809011102000750f006030240c0c1000c00160b4428007a540050070303080c0190600c4e0300200030a48a500014a84030404000c6440d040200710030000c40d4007410401009111249408490109034040a00120103058503188401c80ca52541e0703041d101c480c3c442400c02d00c100b004504d600c948940c820300081e6100070081300040381c50310b0005081c024070365001501a100d02e1640c0c85080070243e004d0460b0703a000d03d10365000030140440148001c0d1140e640800709a0b0305281c401040103c07140070140c8a1141e0510808010b2103e60b001651120000c03401c1400c2192581104542500c55170301b8000c101c0071085 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 847738120 1250 847736870 847736887
    0x3080411280614030601050a1d06030a06090c1e14090a0914250806180906010503010f2c0a0b0f040c060333210b1003050723030102 58
    0x41c9100003116142c3e00c034070f4000f00800649480b28031040303da00303012400030042004168031550014504c0c242d0485800c07038007510200055541d070320a98240407156102c81040c4050381c00f52044000821090900d0089102203a01440328000400468018040380c8010034056903a140100c5c1c0a4981c01000030b840c8644a1443d00b00034405940209140364601000406505500c4695401005c25080e48881c0c00001001140e0000009202c2600203080c49244000c0b5011004e1060003105c003c40a004158101024107003111031999003801c41c0c80c2003060f10300140005e2a500e2a0107071950001126425030b01e55010328006012f00d00600480070780c4204017104c040c000d800da008501c140f681c00c036211351b107182c128103803002c14018800c00c12016007008503400c45d03080d080ca091a074500300c54020325070711880e4940a48060f0b4400d16416060310100b401c0060200c020740c0d0001800c0086102d40b42152076880d51a4014000d4949844071203800d07031031a00d000140200f520788010000d45d61031400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 847739370 1250 847738120 847738189
    0x204021b030d05160903080f0306040f0f06150e0d020904030c29060103051504090629040e01020c0717100603030f09140d020d0c0803030f19020703080411 68
    0x440c0c1540000000c452100130903031048805a040300c0d00f001c2c43c0e0781407809400b81c011207030f0700181095038070035510410410410b50a00418245a80141c0001112880c0410703218080b07507800c0320b2108000f20b203a0712003035980d140000240b0040d0169800c0c100d0b0340c0c7c0d626003918040611800074142180c10500020384480340400d42c002500407013401d01d25a1100030044d010749105564030413421010070103904090a06606c220549405088045400b404172241d105003100300c00951141c811705440c0480050403c1e001d564440700341d201c005c40ca0010150350083e03c405580c0500c82e41c00301104070382959040100501190101c0c695020004070307030b90b440d001d00856030f03903030403040440c0b1250000103601d00680c00719406c041c03000e8030b44150140d507030742000b0b1000b902c0c02089070300c603070405804903882401f00013561103810703003121894580c140920360243d00c82a241002e028517004029202c0066032007801c46030000d6104004d000714210400001c0c2d03071404466480c290700140540c020760008078 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 847740620 1250 847739370 847739381
    0x11150406020909040b0114011706011b120f0305091504030507140718051e0c070c0e010e040203100c02030a0503130f110a0603090221030409150626040204021b030d 72
    0x64604404e4036050308540150b0305d814513827a0740c215140c84000012102e50081e0004041c44095001944a0f4020b650f034440c1c00c0c0240c111420300190100f00140d200c29003500c01d40da00100709000401d40c03c00f810050104d00b0b60028001020000b021810400b003040758800070801605660645210350788501d03140c4800a0300800071840141840041a170003c0405e200200710258680902010b80d0f58420001c42588141001c68010704031680c00641c507006001c135903000e41a00380380c0d0320041c1030a00400d4608055400305500c050318200c2c6695a4a40000485500c850b031402d001d5242c1e80c903c111800640c01c0400042c0104111006d000204104000007442404007204d642a00c03c0d114241241107900c1500000d400c105510401c640c072203003583c600549030700e000c81200c3ca0301d074685a50031305a40720740c1810039241d504424203001d00b079000751800c1c48074038908903a14105040040d000c14610000381000e40181d07400540b818060701b007000f50140300c140302d00850713954554030300d101002400b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 847741870 1250 847740620 847740629
    0x120a0c0210112a0a0618020405010e07270504050601090e2a0702090c0310050a06050a0207090c0c031202161103071d040305130e01230111150406020909040b01 70
    0x440194445440340c1c0e8694440385a583c8907802001200c8841c1d8885c0000d1401c0c0305414010f1103443d07110001a513039030240601030019002c1c152903d0800b1000540707075103100040642c001a1641041c03281d401c80000480450718211408941c4c6d0311400016035001c00c5036000345a00200140030001c605003078110400801000f210b60401d4040542e00041c1207018800e4001d5001c503079040440d07003c0700000c02440d000a43c80171007160540d6503000140303002070641e02c483c02061000c0340401d050b98050100d000101039040e0280041c04462000520180e42c6504c014148031074486c2982c0e00010035819503001c07800402c039802c0b0403041e505004400307941e00c45003244079100300e80d00031454642c1d41c0401c2e031400c900c81020501c1900c3d10381c0c1c2a00e076038010b4000305161503210140010410003124815009040c89031805550b00040201c1da920007181900d01410f0003000c1004204007800000c3c103907011018660300840395212440c10501038403880300d0090780b08506209110900078a010501d0498 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 847743120 1250 847741870 847741897
    0x10207080f0709021b0303131a06012a141e07031e11030a11040b0a03030909090c0f030309080f2103090a1b06030e03120a0c021011 58
    0x5a40e8844096035405800070a05281d04030100411070020903401910344810405443c4084811807498940355401c00c0b9100001c615480c00700d0350a2004003a07104c001c03854090410602031801000281006908003008182580903901030f40c01920028100b01c1074651040603085d8813806403400341d54a80d0205a0b002000e103130100d064650700d90015244046039070191a030007108512071040c01400340f440d002640d035001c00300c4000c4199070b410b11a64445034460010302001da00340c2014482103030600c0e4005401124101c0052001c65080304180c800c4403101500402c0c0d04405180c030740c422140581c010502d07072403204008410140c000d007000d001da0b118032081700d40032203810070826517815024421810072684049a20110b265140046500030244021a44040d1050382d0742504030030700d50162284180001c0d0b041c002d06a140c080c00207881d4681c0c008600703020700c02d040b0400084000c3c100780c1c14190f8a00c200d06a490007400304400403114070b042041003841d4100041c3c01d0b603010f0901140c50 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 847744370 1250 847743120 847743133
    0x60307050307030c050d0311010203091b0d02011d0103140118050f070c12050729060d111c02031e010b0406120605060a0915080c011704030e01140304050c0102 70
    0x360400081500032a0b07044029111058640700900c403200c0e103480c1054007000303018a4966001e01c002d00040d40280b034024000e2100c68002126030400d6540c1c000740c184a42070551a0b41c0160381c1c0410101e81815500c082110301c101d4a0006038000d010101c02c1602c11400a0000680703080c20352220b5807090b00402c0c0a10145e90740d26038a2406400480e01280410b90700311042c800300f18514500d03100005203048c440c0c41c011031070300c440e400844901c80302c0801918011014018140d0318400035044a025a14291a00388a95440d042040c030009030f50b015205000c6144541d0000320b02c015081c580145c2038840440e0300c0803c81c82001c103c0503141c030156017000c0a140c01405e2a115078411100c6a003c0070b44491441e54400c0e003e490702808142d401060390306d0100d94220305106541d01c0300104104403a44900d40300100381010f01e0140d001c1e051090803010f84081d004400c00840d071180d80b614005142e0f401200c01650301d4070703c004034004510b901004000c10440006582041000d00360200e410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 847745620 1250 847744370 847744379
    0x80109081e21040c0308030a0b120f0d030b0a0f2c0c1c0b1302090112150e04060905060c120f0603100f090503070b01051503160c050307050a0605060307 67
    0x2007074414050311035422020300d054101c159081100c6190481e1060492041d010359a454401c1180c00c1551074015455030361104c80198986088209005a4024040c0000361403d900f13003521205c1480e685400c0c1502e501c13040c0e0040e41ca21500d04040e1804500c0c4010454483c0d20b482c40403007000300030445188042c00039290b180080c9281c14070500c003581ea00c0c0c0c908141d00310b801600d21554032451000944402c8804000e030340308504001180b900e00700050301c400351400018800ea0070540071603040b910303000c400c0c2c0d2007964a25460055a0403004040403035242c5107010b100a110346480680781c0d000f8281449502d1166100415141c0d45601c00c08030103407102001800804020b44071150300d540400598071461209800c424400c02401070000303040455500e5440c1150b01428084501546450043c0b003503103051500002c07801c0d800800e05065141086c80c400401c1c076504101d40501448502180c2048410408c503a00554400d00355898401c0d54605900940f009603010b030700c00c1c010b0a10118 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 847746870 1250 847745620 847745677
    0x705010612060b280605090d0609051f0b0f040c0203070c090b10080f040618020310020c011503120507111201140a0e0a1209082a060c0303190608010908 67
    0x100d00c8101c910311440c41303403901c04192070783d5000401182d00701c1075040b1010045031182c4950141c25000f0030181c000000c8450414041081e0042500d140900d000002011a103c0740a05e00320080c050b50000b40e00310009c2810f80c51402010710040503501d0300900818280d4068200c80c40744101940e0080002d011148242c601c4442180c0701d81c0525140000a4042102034102100c640e01540340c0030031071070440e0040380c2000d0203921400740043d000a0141c403c140f0074410402d592700b515500b0300034181541d64070040c080302c1001c440108000882c4140900c00c0021071010300307000c010104051100d0f10841103000e0840032101d00300c0c0c05c1c81d203400109000d04600410b0125402d8501416400035680d49009045c04414524020080c03a0a004142900c080060060846078800e240c1100b40185601c060703595050388110307009400501c00c01907030302d0002090340e41182c032840201d00b005428040703080003801c85912240c0e5a6003404201c40034442140003c0c8820031084200b581004036031801d40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 847748120 1250 847746870 847746919
    0x1207020c010f1b0627140607090b04061404050a090e25180e0613051902010906110a0804090c02011d070302010807022a01020d02070602120705010612060b 68
    0x1190f00004188038180081d850b58042c60051803141c001e44100701e4028509010042c06850448010703518000084102c081000343e107034090164980706000505121740078109009504c105420321526400040802d10284155009028083c00020b01c031641c0700c3e0684050030503451164078500400d00042801e00d150504d090120940000001e1410f1900700e080f075000d020a05414a110791350100039403008001e01c40c40307019000414103550070559506050b07080458040c920410790302c10510703820060b41c004c0908011070b0070500700301c1e00e40e0380c49003037090810354600030007080010001004200400f141d400000b02e0001c80d4001c0002100c0c22080845c24a42030711041031075809088100010341c400c0c000f165200f2100e205a541ea005598a110b00c80c1b6980c00e125208103003100a046807a507030420414480e00c072148000d003502407030150302944850302410b1603509003800081850501c103094000c40020070464039207480284e0307a4180b1344001c25410107072510580b250019485c1c10203041180 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 847749370 1250 847748120 847748147
    0x70f090608060d05010e0604080309060c180105030405011409012c0a020f0310061805060103020a0f0806010c0506040c0608090f12250f05010507180b0702061207020c010f 75
    0x8003410350b1140c40c10010306220005045a06640340c103030003202c19000b0700182e4011446407168980341c0c00c0120300d9506004005004800e400380512004582811890140004500a0078450303580c1d229800d055014101c034600703440150543c40d0501100e00c005500c94a40100c0c45c2c5c000300d103d4030880014450103c44254260f5403580100a0314026142081140c880d0760f100038201e580c0c2011030030706202526266804000c107400c405000003402551801600c0d8461800d180451400d040c1d0b52015013891405a01d100030040344000040440c1d00640e4801c03003081d0803804030b504500e8540707400003070346095000c1d031400903200c000420100c40300003d0040301400c5000203070101c6404440b000c01d0582201340c6145090384546604800c1d107452281650301e1500503261100a102281805420b60790040d01c1802000510a0382e5081006071403110002d8800309038000d40d132901c8030b000040c85030086001d10007100e00c9050510010360f03000594012403101c00e03250081c00301c500b00307415960785d07000389503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 847750620 1250 847749370 847749377
    0x15030c01050403080c0106120c06020d030c0c14013314011416140109111c1410230a0212071206080f01020a03060f0518220803070f0906 60
    0x410f000090181c406403500106403000094241c2e0344e25224010000d0b8903100b1b9640e41000701e42441213541c103000c03000728458641001e02c40280a070500500c0403030700c80c40142880b1403105901826060030f40080b11800144140400881c282050221504411012040e0501600d01d03000410301c59613845171035003d030141c441c0c0c0b955200a0510158941c4140c1c0c00440c000c101300340310400104690240c10604544200014400105e0305d05103414114a5806900c20344201c400009508902014008a19485040b40d80495000306015240aa21144007042075051514040900038020b841c1c820728844080c4040b03107610394506005c100c3c4a80c1c81400d201f090300c0d170300050b11203009807564a014400c100c000204d056884a00c0f500f02407204942c108507035000248080c040d9814007941c4040c0a01c4800ca101c424a0319001a08848031807800152408044000940d40c48040c11140c104074082e4441040c441c41d81d241901d195071040359481e02140300c0044150000340320300a0442650690307107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 847751870 1250 847750620 847750627
    0xc0b0a15172d0a030306080c12032b1416050c0a030f021507030509070f050d020f06160f0204240501080a060803120412080c0405040902210615030c0105 67
    0x12065400b01002525460100380c81d010900d62a4104442e95105019540005a42e800d00081d1403c0c0300c206101e041c4240d4006462040c20000401140c0126440c0256401c9214410001800c0445040402c0c4411450007001ca0452b000440780d40e032191000000080ca42241d4140541d203034001c010501c40542d21405450002a01071a44078460914074011245148492458404683c03030803a10140000c1c0c4404c01e0001c0208200900800303010140003428600d0f04000106582c0740031703410003134441c42c41030268607400d07120b11040b1414403606688040005000e8140300032044004181280580e24107055011031001c00c3c85890741c070b25000298a00390030302d01070045628500113003151610035940d00700060072242c100014003055041080104043c581400c280c1035041350303d80c0303420030f01c0001c0c0200312125080a0440741a02c00840b40000c40b18442d002040d862040200101130b0341c1003c001c03003618608009101481885000c02041103111020185915400d00800c3c0b07034041030052 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 847753120 1250 847751870 847751893
    0x80a020702040b04090309080c030c090c1608040b070309060e130e030f121006030e060a020a0512090114090129181303081b0a0f0c0b0a1517 62
    0x9400900c00180000c00100b024240e080c0014100e410640d0104c002c600071800402c00c0103810b002c080c3c0e01c2d40007100a8203418030b04a0100e424050010411003901c04002100e0102105074485840d400350061a030755102d40e244e0700c00e045146d00620341130b03010030140000068010701c140c42d0380c00307040c902a0080c02d070764081d80c8a80d4064143c10301c048005000a101e803001c031940710009080803a40e00030400303440d0304100303511107880200b0340c2049042501785202c500030b045d00000c202c1d4100c40301890043c1e4405242c14200d55501401050800c2c031034008080c405c1002c2c054001460041c1d013400e44200685407401142d0807203515190341c0f50040741149480352844211050400f00042c041c2010305102480c80b04000822800c4030b0000d05030416003804000d0503407044e102c95200000d142100503041c05c41c819150725004121044080128104400c8045881150802d200c503134048a00e4115080205170040030b822030004840b274094542d42c000610301000c80407002d0060000010b4540c1600c1e4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 847754370 1250 847753120 847753141
    0x10f0b0306033309030909220f06020414030a0b06040b0a180501061205060108040b07031d0606180c070303020c030c070b032401020d0518030613031107030308 70
    0x50015500d0b00404004101d000460b440c3c0071090f0308411080d110250782510030f1200010090102a81ea40c0140b004500a8941c0f04046410800c14100101880e60410703800d40e600c00c0c4032100414441b102038544041000d190041c01c103862070707001111000034a002c1416500e86135030302d01408010500e00802c84500f820f0740803940707101d4043c004051141c0c803590745240c90748000e400340d6041e1b5900c000402226504c141800c5e29504a100103000d24100400004d185330800703030000d0030010605020034401d40c0654840c0d941c20448800003000c0360490322589071241e00441d80503020b181214456002203c2c3c08564074800c1182e000c2c0e09081c01e4540d203045000790084c0d071541070984000c200a1504c00000c00004004141055160340d892500ea182e6003d03821008038440b031a416403946103141c903070300400d0300321480920740b0f403140c0c4070109661060740e154400c9503c0e5070035020b6034060191502007003003180c6000c0c0c00394603030810607081509080c0d9900b95a12018000030407000c003158070341c6070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 847755620 1250 847754370 847754377
    0x160905060a03051e1219080606120a0e0d0c052a0303031006030605062a100c080a0c080906190f06060e090108030412020f0a030c0608180105010f0b 65
    0x90140c010070016440c0d58502e440c02070f8061008a0140c041d0840c1c074002441000f90030803089003101c600e81482d0300c9903e5440c40300c4c6015144818018542c00140f074507280c1d40103841044454418148840c1020500388006090080b0f6030511405007400c407410f003d02424480c142035070310074010b102070821800450000c01c001801c485480041d100910b40c169401c0002c0c500440002d21301400a034a0710340040d084451541c0420301030003041c0080b23860036150200b08032107580c1c003406282c0586c903509240360500c03007010070140704d043c501900f001c4440e611100c0c070351103803000075420041c4121822040d24084811a00b5149a5015900050401d405141c1d4800c103e0051200418154150b16480c0144c0d845a00000e001a038060104007485c504030380c0361401000b0710805103140c2820003c0300d0521118022010303020701c0c80c150803c01c2e00e4650040c00c000958009a88945d10b5841d00307401012f800c82940c5000e400c00d003161208910034410b1060504031401110f00c401091310f4403401610941 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 847756870 1250 847755620 847755631
    0x4050904020d05010207120f030b010e0f1503070c15090506010515130e07030b041406060f090306010b0a0807020d021e030d1b0212030114121f050103020f03160905 72
    0xc14020050000f0002d00140c0301107403041c810b01440980c0000002c180c0342c151802042050b041c694040e0782a604041c400031124415255031500400c0d030004104100c1c00e4007205600b0030380c0001000241070384180c6090300f0f01d1044010241841c101c1c600761043d10300f40c680242c080d80081c00104100d10341140d4440205141303a21150504c640b0549808070005194000d004005240e0304120403158503200781c442c1031340100e900308450344109614080ea41e0009080c0703800740070b000461464045100043da010000000e003140e00360760b110150f2881c10f1b0130881200000c46c1251010038659400420205401f8525500a00c0d40d1605044054440c0c0c07900113041d10a0300040040818101c11402840801e4101c0da007042200160504003d14220126005050402052006221400710301c078000c9402c98007103900c4048c60048800071410a01c1080072103d82c0b20501c445424034200b640c02c028120ba000b00c0d2102c98a103040c1042c0341d1030300c1c180d030548003240380d84030810b000303076006a8003094101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 847758120 1250 847756870 847756879
    0x140909010b16150c120207050c0f031603050709110a0206060906060712080601021c090311060c03040906180912083c2a0d0b041d060703110405090402 66
    0x884181c451040d40f0408195030ba014540304c0040d0318640b9000210301e00c03003182c0240e045241c5442c90b201c1036140d04d00707041400c0c450101c3c1100340178107a508103c4541c0407a40d4511072040e0542d2490590790b40c0b0701c280301c0d443e0303c2d0741060031441a0350304480503912803c005c2d4000d80f08683c0c07540100056032000504050340190140b24000c0071a410380c400c0b40c2d0602a0752680907850400c9000a440e04500030b04042600b1984031021b0803895014030f00c13808032544542401c0402c246900062914012402810020f20010800040c0303c10340360040d4048805040b1083d00da0b0541348209400e4480c9028060f10103401e01210030358041c894450a5803001e180c03202c5188001284021100800800c6084092000e25071204410940012885a04404054444085403030004400010360001400d0100d46c0c1101194240e01040e440d0040f291240f4010030410402c60008003003800d0400401200c42180f0611002804aa01038801c904842080103500350070240ba0a042100c41607000b03200b280c11 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 847759370 1250 847758120 847758157
    0x3030215040606440703110a082506050f0a080402150a02150a05041a180a030507030806040b150f0903010c0302091c02010f0302090d051606140909010b 67
    0x951518102454512091480301001e400042d440d01c0d5100c880d458007451044000c01050b8502400060300b007081b01d6002401c1b400300542d4100040001035541d000c0074140c01010000b50143e00c42a40c01002c4050310300d1801d00681e25080215024068403050b015001010031251001034003e0001c82c0e481440149805c0c07407a0300c40c1c400504070380c200035038060159203c01c01001c08244940c1c2400e600005070301c420001854941c9500d015248000c051040946489011610684034440c0c07184554640000310760401c000c900e8000c0c010f42c0000700030b90000d10302a01041091400c2d011b00283c803a4002d200c01c0c22649038094001180d0721a42a1f0480c1103001c200d40704840d1030a015100005423542c80041e1a504400d00307200003450340c40280b0078801c9500405000607070b0042c00c22403c00d0341514006880e40150030110780b100060b018060310701e10407404ad00380220f101c1315041c2c0940d20603994852805030115030b90b070300c9030068a159a03407003030000d401400381c43c000a0140c0a1480c0c2d25181d03509 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 847760620 1250 847759370 847759379
    0xf180b030a03050417150711070e150907110a020418060f09060b030f030a0305040f1b080d03110f03130b040b040b1302060a0315050612090f0703030215040606 70
    0x40c00d0321520040b00032600c081810846000200c1900b0110959840075005080c450301c80388040c004014044420f03c400040c12503004101002000301801d60301000d03000c2400e11025002900c031018403020b00c198852800180f403941f04034411159062400c0c014980b00d54940d00f0403010309250322005882403a000303031840202c2c03000e0140c8411011310010010300c220480c1005425a01c44c0392042d03010f03500910320203a0880b000411900740c29001d1074001144d0f25a8901241d01144516010307051418034180c24042c008001e0800044a4040c4115a00c90110310419416581281828030f1041014000d592140e00750000943c0d00541016120450746a01d0384c0702d0b150903100340c0d0162501c0300c146003000300b08500080c40940019404007030300503242d0590300051a130b10030100300c0c000b0942c07102c24101001804400c0c0c840a032a0080c07005840380550030b10420079030300071607008803144105803003820a44804502c070403d0b241c142e0b0182030003845884603a400a900540200c4085595000005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 847761870 1250 847760620 847760623
    0x11010e010c05090f030d121812020303090d18060503103c050f12070515090306010b0f040b0c030d110306010e0a21050a0602030106030b190f180b03 65
    0x812598060b1107540d1a0300c585402e00ca1070001d6019458000c0d4021001343c46215000002c50710100d0070094049500c001744200c10140c1c0c5140c0600801043c01c50741002c0f05240c010014500c44e00c008402c407014a1101801142d0f4580306504c00900c13440d80310b00c24441d2501c2500110303444110146042c00c40c035614807140b003c48c4254008204603103015048400014281c0c0c00050343c0781107110100720524207240029490456510302a4412540c0012004501da01404841c00a090061490514600d4a454007411f940000c021074428017a020000c501c402081c029250403001d400c20040c181400d100090070782d540075917101540c511003407000511254580c00303404c00c51990f40030000d8890070700c50300242c031a03076030400400e104d019004410312030442c480424441c004405030380128180200d08002e03040ca00304e0240903020600010021901603055040004e00100980c0c4403015110625600710441d0b0a40c051503010700c01e07000003003015100724920401d41a80e83e00c0000768650564000a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 847763120 1250 847761870 847761881
    0x5070e07020703120302040f05130b19080c01110a021c14101109010c0b0a09020d050c0f010507050a020103200703030c0810061403070905060c0c030115050d0311010e01 74
    0x10030050b4051203003071040080100490007030745060b05095007014144504800c0040c0c15000c1c03507025080d0090441800781103500400800d84004d041c422462a55041c40d0303419001500555880b48260003001059521451101d94000e501d900544288c0303540f5800c010340d00749000c0041d5410b00d074130b15180c2c01040740c1c400c04c40391b0503a500008040c09400024803900f564629000c00080c00720910942c022a600034800c10300d280e80c820540e24482e0707106c1c011040209600c490203504a15940170180400000051805508500700da80c4040100302c40011a00c0d0320907148014010b8105035112030065011340c000c8143c0030301c002241d559006001c07409021035000a08241c0c0000d44070444204500d8000c0221134001400400164105042031009840000c00c10350080d51300c02c0001c00501c1c10b51103141c450014100c01424540c0e101d200c42c2e0b100340d4503174849810f40d20a519001081c00e0005280e00c0070811184050a4903165011507141511005072802c072a609554841c2c601110f40303031080c401c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 847764370 1250 847763120 847763131
    0x1b030b0108030d06050904151e020a121b350a1b08010b0f03130c0303050301031b0510030f0b06030117102309070b21090a03120905070e 60
    0x641e210f4030f02c8140c074803e484803580098051158030082c440428012601c074a83c800c1c41d07900101d540303034458100c1c0486422220081000500c04039004880d90f500803038511580031140d1050201c44801d441c0943d2a811040300480460190794205144440100c0610240c0700c240300029058001521042c41d40d11048a070030801e10303603801d040b42c081c186003440c450311040f1503d84070700d040d0b042030ba5821861240003420f20b0a040040700092685100b408a8603403180d000d81e80300c060070380e02d1801400607003080c0000c45050742104050031003600307042c1101c0200e80c0d006080c110202c201e0a410760080070f03400c20701038606071603d880551070b4544000444c001c00403001c6401d95003072302c01c1115040080051040099504100e01c6600050301407090603031a6400000f2101980c962801862600f05180e125081199010036901442c2c007080e400007001c04d880410681403940d5960001c1c4e00c07511240c03802004102e204113424481c18071648800c5080c0d100724100c81402c2d40b11614403410b018101d40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 847765620 1250 847764370 847764373
    0x90b031f0f11030f0702060105030c13180b01060221040b0732120f04031e151e200d02070c1203031107030207050108070c080a0305100f080a1b030b0108 67
    0xc4c4048104604140c6074080b0103440503201c5035050400190322072400c81007880c403400305050b54541d031149a61105441412065800c1e00c0b260403840e0081400d9024490030015000c0d00c3e801c02911540c50f2800d410004108a40c3c0c0e2515007400d0208043c0d8100300d0040c1c1b49981c04c00a04081e80c40700b40951058541d0305018aa0f04010584006181c070031401903001c03441006100c118540c0140030305407000e582d1321480400951107240c401ca0509204500c02608099402c0c800c0440200e06070300c0812041a0050b80c45a01d10004c0140e0040e150402201e1130104250a00c5504d0145981c014051001d00040c01628017201c903100c3d181500300a8010161540040e81d084040540601c41e07100001c0742011900d051000b07588000c7c3d101e903214070900f8180400c620016001c28071400400c1409648401c0854440c45c00c6500240203007801c6418032001000b40c500403400ca01440c4203001114003800c0240403240465540c401d074000c1050b82e00b0508000d06074040000740c5140380c20307800ba0040c1300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 847766870 1250 847765620 847765627
    0xe1209010f12020d1401050a0302090105040e030708030705130f060503041b081506040507030e280c03110a09020f0a03090c030f05150c070206030126010c0c020406090b031f0f11 78
    0xe4000040740c041c7d00c802e200d80001042000162200a04641103582c2101c0c00541440f540360130900314841c580c00244501c100004005143c3d03002000b03015100c000340b0310901660f4407842c215001288501540001c18001d000040005541c00c11510488030401d083d54140c2d07913103104080c640071402403120f400c210401c0811045041c43d2180680c0501c0f41c1c0340c00c0c4207400d4003d9400e0f85803603040d281c00703103a0441d407a4190101c3d00070740c1d850108250b0040200c50703016541c2c00d000820207496151244108026400007070000344c140203541101c07803600e48452500064100c140d0003000c0b00d1700d045504000044c40000881c942c512030300c10007801103014100ba0b00899901070314011009140074a041030074840180940c0351401a80e05403070071450720700c0c103020801000b006944070816104c1038940c281201c1440ca11340c0300c401607410520980c0d040c0311880e2a966600151101750031155010361001e0751582400d0303111900011170030741c00400001c900302c600c1c110005807404600f04400a64000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 847768120 1250 847766870 847766891
    0x18081911060a24031214090a030b011d040c050d0507030b01030302060105030706052106130509010c030c0503130809060408030f031509040506070305091912030e1209010f12020d 78
    0xc812128200c440e5002101c160340c156610032010b90704442c001400c06c450201d010001c5c00c000400c49040303540041640020710744d64503045056040901a50040721032101c1c40c02c454a00300120f0740c0c02960700000040034103040c034051202c0740042190644003840b40c10000004101006007240c0a14025400b400700c540c1810145890302c4240e920150030000100030403000e8980c0c6190f00112076000e00d4904400d510f4107400640d182221440b44071100f8038000501031030400561004450b1030741600d0600028041d40000c3d150303800220b41700701d0080d03500c0860000294444004001101c2e00500440c1020b403241c14507443e5030018075031820001c00c00018062240c55008405c0c0b007500003200c41080700d1034255134958039444007801c03400074107031a50082240c81c101840020100d10900502c60071416850a181400611020003034010a182804100c80014041070710b05002140400c620300d0700c1d045400455201c402c190b16802086030208081010441d9070000b0221503030074080214203001710 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 847769370 1250 847768120 847768151
    0x1062111060a140904020d1d060106170a020703140304050105100b2505010b19050f060301031e020f090403050d110c212a0118081911060a 61
    0x10484948203580501c1180d50059022107002c2002160340d00150700c130341e4074502040180c05001c0c4c1084516061510141c0c0f071414001d1070706a40107040044550907640c4100075518250040902009105a0800a10f00c214143c0003084058800d10380701504996050444070280c105075030403140da944450900101c03070010101507019042c0ca03095a46045d41000d0089001d080100c04061081030f452001401c0c42029030006244140c0540050398640201c84d031083c00c00040d0190500c41d04002c10f01e91440d01700042503074140ca51014280c0e2014220025441140003007540c00c903848068038421270307590b03202d21010321700682c8251038894981648014481c10f48600101003500c200b170070710090701c4071500014000c1c07030201d90500180300c111095401c00c00c1f130700ca50007060340c94100a03c84000616110380007120105a03200c0200035070801c1500080504e2010803015014500a20000600c60090f003018001ca07001d42c00c125240600400d000c9040203030032039072841b5191342d504036200314418 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 847770620 1250 847769370 847769393
    0xc080313060201110d09170c010f06090b01141803030f0417010e06011e0905100302012003030103080c161413152922140114030702010621 61
    0x700c40c0001c3c014404160003441207400780d4200d03000d106465140e40c106101d091281038116440c0c114800d0b03922010324540340d01038025080c6c0c0c411550b240c0600050b58400911804601410584d9040d0b441c00350305000507660741000000a9091995500c81200c60350104001c010351800302c481c481d02c5900e4403c1c1709221049840701c1d034100b41d0418503444107000c0e020506ca81903030949212450200f201c120104101c0d0401d4209214075454003041c408a52007080c0c0315400c9a100740c0c2c1d2455020107943e5030010035428488800307416030080c8014000640303000c2c00780c1140c0e10401c0445044d0a9000d001c0d803442c9000d640000e0740021100950811030518003011801004540c4080c41f45c082603016145103402544203075202c0121142c00400c3c502041c0101c41d8205c2d548819a51702c0f92030142d100000c5e0002160300e8400310308262000140c544411600030180a030503102e0741410a050f100502451780000c100304d04655813030700040307040024070080c5c4014070750007080039a00a0a9240ca00350303161 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 847771870 1250 847770620 847770629
    0x604020103060b0c1e010906021b06060d08040e06010c0503121f06020a0209040507050a060f03141519050a091505012a030c0f150f060f0614070c080313 67
    0x8000c2120420100c400200002500314590002d42e08170315a481407401095940802081c10307000085001c110302d00180701c0c12490b0410310685c0c9650f03c8400400030640303803640c00184600030070f000c1046007807004007441d035104106042c00050101035503141815135004910f29040b2441134418800c80400d402001e2400c04200c401070006541002c01c003942d1000c40d00070003446030780c0c2000014100102407000c0c4004003006000b0858080d110a006000180000300d290006807501100f16505412420b040740104219060b00b0300c6030156009000b0303c00041038120246a290340c00020f02601ca40349002d001741041500001e005c045400c081003103c5103503001c0da040080300004a919243c0004000c14000080600c0e12031108861805851a12401e0005802c0c144c06410003c103001100b02e003d00000010345d0200072403d22103160408a607020b0090400c01c4a104005005140c0074600488100d0450181a070800000b55070300d0800c22101e4004203500c1d0408900741014074179a416190281c07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 847773120 1250 847771870 847771889
    0x513031212180b0421050403031106222102010204080f2d100f050411040504150f1806090b10030b240405240906033c060402010306 58
    0x596941c2c4480326400207900a4640d2032402c01003802c201c2d014844201050050565600001c602c3c040a8281d411501c003c0e80484d40900450a81c0d00d0003043c0c1c14443e5101400100c02507900da413110030940c000c2041141c40740c01e01985503903907480c8001d0b14083d44005a00159035141000f141609005c01c000b6540040c1e4030100e062810224100055081c142019402d20fa0540c4440750032482c1021002c02c03402c105242c04c4120580c1d420540009100714040e0414080f0307040381c001800b00310380e000c031070290154030f41c2071160f6444600c41d040340b00701d00c1d440400071443c4030025115014540586104940c0c2c1d0359516982020481e0f0001000e41c0500c4800d807100d1400c7c034585800340d50140041981e156082c2d802c008031f2403902c0300346582c015004003600401c900e1800c07041d5401c0000c00c1180143d06848403118450b4a8a4074508891040c1d40290140c1003500340134420600068071440d8103030310180401401100b2103900c00500502081040060500f41001e00000d01116a10342081002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 847774370 1250 847773120 847773131
    0x6180b09043818010e07120908030402041103060d110307030203060903030a0501171c170a05102c06010306080f010207061401120b04020604090e0a020f2706010513031212 75
    0x10f89a103000c6031411220f80c1e05441d0081e550f4110111042c1c01020342032280c0c03920704a020020301002e400a14803843c03003078404000940b000c210444c4a030000b1601c1640c0000e108640500081c1d203055201440c1038040c0072980304546030780c00607051980403100a0191780c03005c0100400c4140380c1c06817030300605080c498a408200d54462054075280042c16054400c0c4070038091011592058004c6045828140071703d04403401c1c001208000303003906840c94074100b51405408220f24140c0d15020340c0c101e0301c6404035401c0182580c2c03003c090240040103e814103a03140000105800184601c948a03c01e0340c0006035210254684801140e540c0c1000070919850000140700041d500d1000b1101a5002002d13041aa5a07501c001892407166400c003035219403c0803034500c2e42001c00100c4405840c42258948a5110f058041c04201c0566a4400741d204540c0d074910200c4102080000e0b8208406252440c80c141a50410f070303000030056441111000c0c0f948503c2070800c0e6000220585905200d02c05114 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 847775620 1250 847774370 847774399
    0xd0c0305161b1b0b0d0c0e03030a1706120d020d0207080a020f09040c09150302040b0414180a060218180601021b12010e0a03020706180b090438 63
    0x201205454002880c002600761043e4001025800b4100104020302d025640c4112505008002c1d1501d202c681c008190b05018002c824503010055070014030242d51020840c424041c3d408104810192400750010b0002c14504c507403c1040c054880350747c10540042881c4244040001c2c80e00305640c1c8100260b03003200304404016501c8045c64150030500311000c8079541c6542c100304d034040f0840d41c4901d000514110610170043c2c203c0d591b14040341c0c001c40301003080006c40800d02040d2140d1004000c3d01010b03000024070400c030246001c00d060b00b81d5a00b140e000b2600c9030380d0381d0200d031320002d882d010a6040e0364058800d450064050004d03000b81180d4038603075041020000c2d50312450191540071421191408800c0c0b61a405221364804040400a20000e002d540c0301640b50307002000c1c03d83c018021650003044050007415442c41205060b910710801e9883d0804100c85504210700899025031070b02d000b000c4601038901107100075202c600b90303c21018203ca042603441e0041760551802108488089407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 847776870 1250 847775620 847775657
    0x80a03091502030108030d1d0d0e040f02130302041d03130312020a02010c020405090c0310020703140705100b041e0c031b1b0f021905101e140d0c030516 67
    0x242d001c04a680c0101c0e0141c808906043c40100348c4504103030301c0c0308040d0807014259000411340401c1e10151400c02010015080c09000da00c80d28440c900080c00c102c8003040181005d600a941c6585195944501032140c007100070300b160701c05030320001c200c001190113106201200b00c0e003404d0b070300c1075000612440000e41c0c0041c154002d41d984c0032740718641d58000140134030710600c40c8000c0c140005040e550b8040ac1d00490400a400120007580001c0031034015980f440880380480740b0780354002005003940052201c440300501109103189421a0b201e0608c5083d12212014a0408240c0400b0114204601e50700c02030860708500551315500050740441c95209400030b00c00503401d40255982080070110b410050b50115914000a400045908600707800078001085881a18030480ea0b0f011081448039040365500000301d01e5086c0c54544448000c0c0e46800f03090002c0c0d490101c0e003501810260030800310012105184011404a038940b0200038031001d074542040811411800c040071007159101850 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 847778120 1250 847776870 847776877
    0x507030b100c1b0504022b0603080313060b040e03270f040b040207021c1b031203020a09030c170606060408030301060c110d2a03080d09030903080a0309150203010803 73
    0x14002d80b415091401c0c0600c040c2c100c190181401800a55483e100711100c00e4482050341d201728400c0b1180740c01029150300038050242180d030490612b0342107031201180051001d10b821401c49129994010442c00f5807140c1c054400301d01e9494003e95110005d20303d2018404011f0041c0ca112510540000165541c0d40c000350084c0101c25940042c02b9102c03034002c60028810000c0203548844074038071100d0f0316551011001c140e644141a0103150b1410b104d039a4a1b100e509010051102104001c010b442c207220390f0240604d4441440c0030210507030780b601e90508590454201d0100c0c60300d514090072480780c0070072101d07400507030544146151501c0c20010030348900042c0034100130005051050001d0005004541c20b070128000c111814000c01403903c10040c020340c5d900c1610189400100303102e4507813050107410440f5005a11640382c802c0b5044000014144080f00b2810f128003040c011010455410142c2800800c82d1000544405903090074600c82c210b0100c80d0441900410040c4044080070041c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 847779370 1250 847778120 847778123
    0xa0615080f33120a080c1b030a020405091609150f0503030f1e0d05040c0e0f01031101050409021209070b042403180c06110d0c020d061407030507030b100c 68
    0x2031984010b4141c00564608108110b82d54684590915041446485001019440c1c0040200e58004886034031150921442205880e4143c0143e0f8014015081c0303500999404102d900544000c0c500100b902c0d1116140d5401c641c08081d941c894407080d924598803120054005030040142c0140f520000996038412086d10090345180841c00701d0000d04800b00300c00304480100c8800b80c40700ca0001a80c0020303c0125402d03610072040800c00101006105e0a8502030b42022920402c16821501d41034044039061800030304000e81000006105030240c40a02800e00503502c1864050500640291416606400c0902081d5040000b000281130600584a0381041c590388101e103640da800c8250004c20448040282003140b1644030010001440030709825513400c1d4480c440f4460070542c080d6a9002c1c00d440c4503011490058441c1c01500e000101e90008070302c0f40340c0129911a0801c0328480c00c2200341c1d10100482c3c1c80714188102c10303815005461201c2029540c034583c0c030590030300090000c50300400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 847780620 1250 847779370 847779451
    0x10091104090302030c07230603060d14121c0c0203120f06010201060b0d02030f010632090406030c0806070c0b0f0405011103010803070c09020a0509090a0615080f 71
    0x541c02003500034020313250701c01e80e49001d0b52411503540300c1c0381200040116240c1003000c1c840c950f00c0301e640342800660b40907440103407495100921680d140155000240300c0440c05214000e210820804030700028402040c410005175000d60000400b071096031902d04407101950010300c214201e68108144c00381d03115100311080101c075107403280140d005001c103800004c0d4a86000464038030313000107600210b00400d40644c15100742c1e81d03140c2e411a480b00c0704a62444e05000355042c0e5100c8112a0083d1684040402840d203151407096400681100c8107988104c0307080080702801c20490b00113210141d80050542060b070310507a800d9a4020040300d006014006440d064004102403000c03d43c840b140f440000b8140541c2c070350f12110b030596a82c0040d0003c0740c01d07001482002c210b581060095070845400d5459003400e1060300e40c100041c90314010580d56405544003070006001641c903035803454201e1103031103c25250800c00c05e00301c0c0d141d0008107200e1140782d40d07401c2c0448a81528100c0c0740031514404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 847781870 1250 847780620 847780631
    0x90105010302220608060f040b062d0105040e040b01030c0b0c071229060f010201060b19050d05040602030a050702161a0f040b0c150f01120c05100f0210091104 70
    0x90700c600901042e04036005d64811502003008034251020300c1da000750300501e0b90360b000355111410000c003d0520125100092500607103441c54070340c0b543c409400701c541414000c0c100713501c44a0720182a80d04413015514259100010824007000703013070340005414031545607032030a010598066034414981c41a80740d504070b042c800c4d409120b03040882021345244100ca03000c0e00e142201300c1104e0520107444a0340310b854940c07510080c40d0300500c03500d4103d8901e00000d600305484103003180303c8200119140000e0210030032141f46220b00511409108134032882c0016100d0414200c1c850454200a20290540d407089202e000c0c8548080b000c101192081011030020f1100003c00020a00a00d0809410760a0108011880c90a064041c02c2d40c1c1d216802103c6004148074070582103c4015035a066441e82c110700180406581d09240381c9442d4003a00c0440801a55400810f14a06c1c6051055001403407500c1c00d1a280c40d4180711303c10a00c8a290818440030009485030070300484062829441141d0300c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 847783120 1250 847781870 847781929
    0x180103021c122003210907150503071808060411420708120601090b0a05030619081203130506010308121024092606090105010302 57
    0xa40141c00c0729607111002550841000c0005001c40300406991030207a60001001070034000c0000c1034a001900300200c514050565405181c0e00b620050324410a6004614010401d03031121040050207031019a1069543d240001c0028144030f486248581e00300029542048502d0380010544d07000384c0c10140c036900b44804200015120401050383c1154190440403000e000d00d500110015005280d801c000d940010002c044003a1f4403811000400c001c41c144540400c409800d800706620000c181003000e2074980701d0000f000c03e5000300d80e0820000e4000800c204bc2c0e81800303060300540c20300c03228600a00500300801c181d20350504000280030f1810210024450100c2c3d44400c1e50002e0b00f02d8107032403ca503141d040c00c42c0300f5403049131180000c2c00340da008a5042d80094034064212142822404240c441540e1215699190996605c040000c8000c0c0030510f00e4031900000b41d61040320600c1440124200001814072100030460345003a49810300400150b01d400091070381e0541018400c00010707444 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 847784370 1250 847783120 847783159
    0x3070b120703140a0207060501080c06030f1f090b040b03010b130207061d060105100f0c0809060706051f051c0b0612030304060b011b1101050309030d0e011a18010302 73
    0x20440f80c82c00050b11050111074241d40d4001e1101c98051502445160b0b207039044a82c0e950014803c944c1c006204000040011200c0201160040301100c01c0d0000d01c03065407808014070b0429040100d07040d5503600a80518901032041c81ca000c20190003c2c007129030f0190005800e06402c40c04000d21640020f10103040261b01c0e40881c000c1c00300361030603810f46030703080300e1595441401b401442d001e624040e00c000e500e00d01070002069081c66070707540c1d507a03882a81e41c3c07a1070b000d400c003030840707500141d05102600000b45c85029041c0b040351204076191011064844a0300c4611256004070f0040540703030104a10722400340000c050594101503046007580300c000101e080301c0001001c80c02e90b40000310031300c000c00c6103907080b8403203140c0240e80f44d50020801d07964103030b140e03002c0031801880c46172007564004084d4003400146600c003009000b92410f061220322420161020200c4680c001c2e59151081c0d031047c03042c1c2211200c1d21209482c0d52180304102c07950710741d01c000107010203403203640154200f4406010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 847785620 1250 847784370 847784381
    0x90c042703051e040305010b03070611030703052514100c0203030c090d02031b040b091504091e030905032103071107180f0c111f11040609031103070b120703 69
    0x446807000340c0e40e59640e05100d4004c14542440c40c0c482d0241c1c8400048bc2071089210800c0610380340301031882c3c800320765016100c0d0b60007030018501102d510000310141284241c0c0105900d40a00c4044e100100700903400c9040441480c1948071481c681070b8140320055002084d40c0d40107103810a003ea580c11150002020030140b503100a40c036100f00c03186942c003050700c0218290501d00c09c1c2c81c2801004444810020744150403a9000c0d12110203150301e2845103003075041120a140103000e100d20a841c2e604c012041100e07206c3c0b058000c9110f20408000342d0508000008100c440078018001d000c0c0403031181c244a2001400890802036041d020700b041c0c0071b080c0400002050301d4040b08081e000e50b80000d00c0900340180180400b20b00c2d1481000c00f15015101010b102d0004802030091010048480302108058009201816030340352440c0c400584482c00900c041c1c1050b80f41d80b011180782d494090f1589008002d0a4005d8110300d41c100b01c0c0a200d001603803502c5c1c00f20003a101c45031b900e41c8030480c010305 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 847786870 1250 847785620 847785667
    0x90f03031e0c040506180103150602070e0a02040317030711010c121503020112090602040504140916030819050d29030c1f090e090c04270305 62
    0x1440241e510450303600d1004110344100355290740d40c124401840c0d004a203d050b821000421440840310030710381e11068411014140021180700c148007403406000150054009a408041c0178041210507000b115400010743d10309500d4142075030ba1b5100d60078000da02013100050301002007155107004400280e01c0034501c800170001d003000c02d28004c0c0100c00070040034516a1800d110800010b01e4102e52034103a0b034041c1c50307941440507101c4003040101180f0b24140da0b040e40c01e0001240941d108d00030441840d0b1440f1640720581010414a030404811f800540600d1070200010800030399034805551540c07500c1c5900301c5994124540c16a018491080d40800c210314043c40032008090f80c4a620355600060a000f5100c1e0701c0d00c006141d52100c54514080d03108030000c068507030404a083c104441c0d4540361820421030381e03545a1040d1040001e84d1600b01030f801c141b00a540780c1c00d19100f010a40301c40d4900314040c40216030100f00325152031180103070400000003850f00a40460042c0c154121 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 847788120 1250 847786870 847786873
    0x60b0c100914010e06070f3b1509040501172508060709090f0b0d080d15030f05060c07031725030203040b0106080709060509180406050601090608100608090f 69
    0x201c20000060315090106d6030200801c0602c03142d0b401c00c1b0b11544142c08900c0903e10005000c036940700c04115810001e81c40c0e2160425946030044150b00c0748010358003203100c0c4400d03160b120b401070780c200402e03a5016009204c045c941169124a0710301e000400c040b49244180160b04810030300600c00b64542895000294039205580c01e000710310381d018400e0011a001d41504114243d01a128842a2240324005e04e601c119055119008280c01200405072521664400910644038420301054544654400e035601c104000f03a64042c4001840002d40c01703202058294508000c983c0c0162400c3d902c40f046501403100346001440e04100210840345038050026046c680201d01c50300100030307600851f0201c481070280703000098150b0158140a00a2115840e928015420b05104581c1500040d54031030f4001680360b81c0d580d0404500350b07000c0c0a24001c620208241ca0b00d2030002d081001075131310003401c114940c000c2004046c5c1c44005542034803502d181c0749545072034045040e0300d0000c0c0e6800c0101e40c0d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 847789370 1250 847788120 847788131
    0x403110117010b0304150218060c070305011b03060806010302060412060b0418050c0312070f080909100602010c0e0906150708130608070207080a0611070f080d060b0c10091401 77
    0x19a03490f1030140d4400e92103102a8040500d04074081c0090b809490407840050b01a861030b10b1882c645280a407022068071012900119a261507241c03c0d108030340c3c1303c0c00e514204150701d48001e070340c1409000c0c0540380203001044254910390211382144140c0c8500b445403070125000d40100415600f298070803000041050060b070242580c007070507131078109a04480a108042c58044141000701704196000c14100c0c0f01402c0a1440d180c400901d492840b00f111182c1e01000040a142c0d00d1300b8142d40502441c42e02e0701c4240f410518040e085a1051009005004064094490755550303040c00d19840030043d104200070074100b896005041c0180f1000810f00d03040440c800c004007c0c0c058080301102c550390349180141c4c54120041c0e031548403a0143c41030ba900140440d4012411980101c2600752124032000c0c03400000e5124481a1000107004540d603030800102e00c96a40614000c50300030b44040d01d0300341d15144603103001036550301645401c1c0060540f100124030034041000301e40c40544041700000e200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 847790620 1250 847789370 847789379
    0xc030f050c2505100908072013050f0a1505061c0b0904151508061008060a060501020a0609081c0f11120402150f040801050603060703090206040311011701 68
    0x51540011180c5640025907442c0d41d40c0c84820490189070711a00500504000b01c140f0901c5005089140026140312070104840000a14049107422242c141455035404c0450042e003000030700340c040e03010f0740c5841d0708200600c40f80440c00040c0c01c0e00003d6500000526440807440c0818000165204550020740414880b43c20000801105c2011484060400076160704808014214105907400b80c084100c65070200c80c4242198080b000700060300c00c07400701990b55011941d1070b101d0304070303410050422801e1003080451402c00c10741d034008003a24030500c01c0e241081c0000750b172103030f800c200a00000c4d1244111001e0110940403180d001020840b08546e6120300390500d03010300030002d030710721889240c10340c0d00b92034411250644132a1000c108900b4080d4546800f003104c5000c031803034100362406040041a40500d8540020001003819500224045c0741c107400300740c100701000788410181420141c1341030050340e41c003040f10f00780c0e548490f610040e4518680103c07000c03007208c42c8950217415480300101c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 847791870 1250 847790620 847790641
    0x8060d1b0b1b030f0412051f0f06080d022d0d09031202060103170c150702070617010b0a11070302100c0203010f140106050a020f03030a09052b030c030f05 68
    0x2c00340380c070007040d050501c07804200c1d07900d00c60100c2c4080980414001404a00b80c0084040000c81c0a8000ca9002038114442000454091101914080d581e0201c044440d035060080c00c00038443d08015260052070224065254071180340070422101e40c0c21241a0f803046a80007140c0c80212000444201c02580c1c40003a0070007040e03000a407507400300035420881540c400158241070b683e000200e41c80450003401071a441e500b14080620043c0030b031203064003482110842051103010035a0040002d90724107100601400724107810313050160b0285005103c2e014140d0125200f815031881d01c0521701c21007d1195080081e2504001e41c4203095070600650983c0c011040707551107000f01c000b003140d5204010880112044140004040500b880040080a020b00301402417598140191280c81c1813039080a8115031040f03410758401c1d03680350310087c10301c4002c0100b20800c500741d903039200c044960641a00c400f038180403059400c06032122036203002184aa00700882c641d082260903c035604142c007400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 847793120 1250 847791870 847791877
    0x50307141e0903100501060e01031d0a0b270d08060a12210c020f122803032706051008060f0a0b04020f0301050d08070b1005090f060108060d1b0b 64
    0x1c510070320400040036007100580c171401341203460684a41007094105401500549040c00020b9200382c3c140c50a2040d00005220000100e8481d50034805149000f008070b0600300f0390030000d008003d00034404040803145c0010f140880c1e18150030801d49565946000425042481d000114803844d078800351020003910014200074001c1251001c0311018803400102ea44440300c00010350700004106a031210340c142028071036162a030b143c00b901e40240b5105244551048207a040250b504034648a000034140c2c5440b5481c1410081105032015003008400a41d109101e07000207802d580c1d4a801050480004543c2d6000601c031990030b0b1507007803a0201d0300c00d0410008440b580b0a141c140782191031540307001e04c01c48030815038030340b00f4a0a59003000e05020100e111010308480b503103004c00060000c80c1907100305900c2920444111001c940c180070500130170341d00240039440001e0400e4140300080e80c20403540c45d8050400d9400300d50200700e500b03110700340c10b25072103888145924098010a02c400c103c1d008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 847794370 1250 847793120 847793137
    0x31505070801090c020c040504050316032313090b13050a050711120715061208070c091503030e131a09090715140f0f030421050307141e 60
    0x200c4601d0380e81e07011403c007a40c00c11035042c0016000000e40001c1d610b00f560010b0b8019000c0d00032030381454001000d40c00000340110042e400300d003801c1c51003002046508200960707003680600e182c0c01c0001c44c0b0010381000c00140600082640c80708039940b159242c101604516404100c0e0901160609600310f0008000a03030300c0ea4002020a00d220942000c00101004030102d1a51164034260068441c0c0c1c000104100d42480e0781c98491800145000406054241242c080d115007a5071342042d1420240d55541c1398420240c0c9400c0c07071800c02401c0400414141181e41604040406058181c0011221851005d05220303a910307080d50868070000c0c00325039140c0600151600800c585660300721a80d10111480780300c0d49036030001180e400b0a40303c2c0040368610001c2500300f90074400c60281c4a290764108a104c1c00070000007204101c144408120042d10114031900005809289450000c1180c4001231115081c81820b0b141e1903101d4040e00c2c00c03940030003250607440780903210280d61f02d602903011046 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 847795620 1250 847794370 847794377
    0x108010b04060305030f0901020c120616030e03091003020d1b03060b09060405010c050a06050c1305061e090120010605040510060206011203050c1914010b090f0a0603150507 76
    0x122442400d16100c0c070b509a80e0000000c5040c031400e025120084d50050701d4060460040c070341648019140c0716502c0c0b031402c0c1d10a02529461600041909242992410060405080c211041550400442111483e00381030302d01135a440b1030b510b01940a03204117020503d55078235081d0155030700c1c00c1010440150f801d0507501484820364801900e40701c0e015418045920450400042100c0e40c02820b07400c3c3c0c03280c86030066400c504500c3c0c83c3c000c00c4a0048505900c61003000484020350380340c04440c60040c2a00700e030018100140190006c14030351441c3c03540c401d43d050000c0d42e141c0e0f0342c0c0141c0800e60149003a9594108140d44d0390003050103803a80780715490142c0d0400d001700d0100411b811811065070700550082007140e1804061410381050007e083e000d1020070044044454418041c14070030858000e4224107035400b502c0e24034071180ca000e0f002001645080304a0606031344da0b5040e50341000707184000305600d44400d19810010015940020446c0c03050550380303951081207400c0345105507130700d85 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 847796870 1250 847795620 847795631
    0x72322030b070e010503010902090d0503031006020d11100c02010f061e0e0c12070302090a060e0109080303010b3702061801060e0406050a0f0510050a0803040e010b16021008010801 79
    0x200c00307036002d80c107030b0b0f07081408200144014004085541d02030301d404800213000038496421512040c0c1513a1003a1400c200e0460200790a005140e0100314003032380400c0c00d14000c400c4c00c0c0b403001120b44400341110003c41c1d10345c545020b026268402d4101350148111080304114003680c0c2d081940c0d810f1101200c1c1c2c0341210b07000c180007481e22110382c6d0705440748205010492034404001001448500014569001c3c0356003030049025944840c03c0a03000790030151107100100342054009007442c8016400400302e0303401000140068038004094441c404403d241c0e6a90b8407545064a4050b1206007005030702c01030060380c61515041c2c0c00a40709000301c80340c2d0310401c02ca081d100c024500342da80d01d009030702c00c44041d00d02080004106600482d4814181c40001480705c46250844098031400d8412010034950354200b8030135450000c20a90042c10003d00442c075040c43c0481d0000c0000052180d0741000c5e0022031135034044400b004960383c1d03680c0c0c000d010a19100050b1b501424107030b800e0064400035031901 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 847798120 1250 847796870 847796881
    0x1415130519030f0c0302100203010e0a1b0f030b03030d0c0e09070509010804030507140a0b091510060e0102100e100c05120c0c03070605010b0d0b09072322030b 70
    0x12140d071019405a840340e8a90001600a5a100b000010218118495524003407000701ca10b10146020303100c43d0f4800ba01a003000c681850603281a10240c21400024801050a10790441e0218028400d1400e0216810603414002030448c0640b13003410b058182808001c1640311390009110b89000001c50b07262125450342c1d40c3c110313210f0080140300c9010070704920200d0046402040503102c1c00b4440c0060440350703d01e10446908000744074000b04d85084643c4284200c0c2c500a1100c0044026420b014074402d00e8410140304000082d0301c0391001303001040100c421143d20902400c600018010020b02842d100e00c1c1a20341d403646910f140905d4035280c48038030980248180c00b12980c0e4880c0e048000c9080e2112948034406034003d01e0648541c1c4005c22180000403914018140207090010f0501c1d10303040782d401040b0903142c600400c2441884c5040810034130b01e0b08010382941000c4a9a0b40d40c0d803a2907a904c44176618414252130128280c0304030071a400203407541145809481c4100d180c98110b8480 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 847799370 1250 847798120 847798153
    0x40b04140a0305030a0f060803070b0a0b2d010201180c03030e01050a02031b1f2403020d0b09101103040201020f0111070807050705060a170c03060d14151305 69
    0x207001004000403810000b048456580d074004109000b16030f440011f02c00d954808991450340052002c45820202c181082060303c40307442030601040c0140c0e40c002090341c460061000311520b80e8070b00140081018040c0c80d0b280d08c00d5000c544801840301903a0340340314282c200006c2c442d005110407000a1124030351400c00c2d501c541c2c2540e8200c81540c00071801c020f000b04800c5112445003040c0e0741070b84a1080c64610036021030010041003500800d000662606900304103009003a560070312203200d042510f013040140c0b900f20b100e5805c107400080300d110b00c0d101c190340c40b4208508060102c081504054481c3c00c01800540154010341c400d800b16030002a00b01d02c9142601d09004c14804111414041c0b0000f040c8408020071000c0c0c429001d5900043c2c441d000601507810600040000409920803100c01401e40c030300d00e9030452415141e01e070851600c0c4c00054079140845500030604030480090f01d40100080280401c20740110b00110818500010460340e00501d144056a2501c6840d03503010300702e0503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 847800620 1250 847799370 847799383
    0x72619120606140c07321503040b1306020a0905120c010203030705031e070f021501081b03070f06210b0913060219050d2016140a060b10020102031e070c050303040b0414 74
    0x440c0c20081c00c41d0340e52b4551141c0003400900c1350f180342c595031040b04002212403000f05000211a00d410a03000e08100500203090074030100700744941d0044072414401d81e000030903281e012078180f4245aa99864500f04e40701c40c070022581500d5210184140400f158121410074411080c940c02c48403110107103805c00140f120b00384107140158124203018907ca5402c0365807412481009070071100310542e40c030011b4404070b180d548140006960001c200c8a8190944030170118001104414440000e50500241600748003410b03151329014552281402c00c141034042d43d280350b034440841c004841d9080d0026003140c2c01280d65185241c5801460140c4a40001d5586c00500c400100e01c0e0030035504511500324000806401d413402201d40304501480b900070854902400e11401010842554040030302c990003070002400415a4014410444000b806140303040030300d40c0180c000315164035045000d07a0000310340e030805000d60200000f00030a101d0308041d100e002c3c80c4203071508001004014100e58403100b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 847801870 1250 847800620 847800649
    0xd030b0f0a06120b0a090e060c0c12070f020415051912062c0705091501120c1809050f09030a05072619120606140c0732 53
    0x4140c144280728443c85541040c0d012416080001141078228000440c0d5440300d5000c4042c90b0744032690810005018401070307402c44090f00e0b10038180103500100a032500501c95080c1c1e902040881e801c401d0141e0101341c2c41117250080e04c1000302e00c501d601c4814119050f070150b10300840b070880201741c80035031079039155084894400d281d014a0800e60790700d81c054034058450445230000c4c0500000a000e88800c030700008508480100320325881c0200b400000c12004000030042c3c4681c040e13034003003a600a29000301144000d0400211241c420b901602d03102307150480301c0060180c4050120350800c05510450140011030000083c6554041640ba035030301c1005801c6c80001d900b8000c04000480100d1030710040580c1101c0e00504180c104000001608200006248066440400b1051a8002a17a03044010950304244600d40c10040302a114802050720034200321000a985042c45000344007e5001d000e403481aa21500c1460707040300c6d143c504107e540045041c401100411901d4031280c1d0301c1465 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 847803120 1250 847801870 847801879
    0x140f120c0a0509042301081b1905090a0912020a03030609050108030f0f120f071709070513151512050f0a05070509030a030305011509080a060b03030c010e0d030b0f 72
    0x691800d004c0984000885107807411a40074000100d514040d154078041d00e0b030000100558508440100b04017105181c1490080c50b000040340c4141d4950000a070540310141c070090703500d845000019006049009000e803064504480080300c0c2d40c0d01044071680680250f506000c020b440c1c40314902160420300c03409246900801940b4130f404c0c1c042010300800111507403664200380741102c04801e41201129200141480842000034013500030a054503044a441c14061051400c0711626075580214019140f01303500180b85804240110b4100c581070b002c1c034034051280d40703a03200c040003480340440106102090148034601d81004051042764810341000001c580191219108400108009030400c0704000302013010758102d443c100b01c1482200d01c00c0d60000b074158034042c40c412040340484000c60802950030383c20418140c0000b00d0030409600701c000025401c4c0090002459886200028a103650801220300302401307020a00d070070781404070744051041d41d0a1400b0440d00400d003424680d8072 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 847804370 1250 847803120 847803127
    0x140a081203060904050a0512070236090a0c170f12030601030b0103060b21010504090302030306100207030c030507031b06050a08060102160315110306060301030f03140f120c0a05 78
    0x80c07400c0c3c0201078105001d18280e440071606511250305007902d110540104039400035400e011800d1410815a0032110040c114819481d07014406401540400940005001c04808a042c0d46414004440170390303400080c0d101c6940d99043c004030100041011b0310140c0c01254044e6003070032404a5108800e0341500242850b6550b0a00158018003415012a04040d540c03100491010103440041801800030580000010b0800740d100e5040c240507004180610305141e007030400250000103503500080d0460301800b404410040032868113003551300161000500d10000018010041650000e9902a05060824180760000c82450146074420840090803c0113100c118074800d070304940d002141441960310604440c2440d030510003541e007003500c0d0740392008034122848100c1e03c21444146165a0541d046250880004815020505c00a0b186a184401315010103115000340300260305e4403d5903540f07480217034001c040da0360403119404100501d682c001c039880700046070036100b510440d40e4540c0e26 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 847805620 1250 847804370 847804381
    0x90c020c030c06030603060705030406090c06050714030901020a26071202010b031606050a0215151c08070b0403090909120e03061021140a0507090b060a08071206140a081203 76
    0x464ad80000d20503603a440e902c1400f08000742c81075490700000c6c90b0f190f81d6140c840c6640c0c2030003191120310b00483c0603640e2040000101d03598000c21050714040d0449551140d0900040705c0380700c082245242c42850f10400280042008200007562a41c620079034020022600c651042c507690350f046021aa1030302d0b0281904201c1c040c815401840740045503c1a03c659014190700c0070746200069402070303103441d281d10b031130101402c10603440101e0800f04860401c0c200f809403500c0203184200c0d9009002c1d11940d1000070141402007001000a20314640b08200c0600f0504001581000d580385072800520020783c040120718000551030b0040030380312015490075141401c030109208420600303842e0002080614030100d50807000c0b4483c0503000001074201000e2520f005420500d19130031180220b0b1500f00764443c1e540310702040d01d050120301c0c113100c1003e0716607510903180f00403a0b244842c80e05050000c080344c0c2e508003905014005c441600c030214515202c13070304e15484001d1007458144d504d40c140002032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 847806870 1250 847805620 847805627
    0x1a070c03081b0c0306220f030f0314010b0d020702010c0c06120e031c021e040b120f010819031209060b012307061d0607090f23011404090c020c030c060306030607 71
    0x4062425181ba01940e40c61540d4980c04804d41c5404180c001c21103503d03203481e00340c2e0940108625084104241206581004280c841c180210324481c3c20541d400b050740300440e400b0b140c0903014640c016140c0c0501c40c1d51510f00074403600c02c212001030400c3c02c18074110340703003000041a100002e44000902486480c1e458080c070094120203140c0e08942c42d121400c0040000c07080c001c1c400391040d003480c00e81c0c460050100180040000d07140301010300803140100071203a0302190389080111178000000390342082d41012541035040c140180c844601d06a00c0d4020403200d6807046030f508074280c0b10100f050289000c0c10b000071304001e080445e0341204100c2c0b900044c01c15800240c01900780c0021050541741d4098151034840300310341031400709071049014070000f402400f00e54000c101d1041c130190485000740d25550051908004603041c0300b00c0c0c5010080039803254065601801d407a120030802080c42c20b000075541c002e0448814001c1c05401c0140d4424280f1204480c400c000203070007820a901c410750100d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 847808120 1250 847806870 847806901
    0x1a01141c020f240d05090d140703080c19030b010f0327060906020c060420060a080925051801080613080903151f0f1a070c03081b0c0306 60
    0x6007500303c4072a80007500007000003e45000d604800001803245001c00e00c0c01c0ca0040122a400180150702e2001030884103031808a407841945840c0500310b43d1201c0c1612407403030185407000c8140141e0145420031142e07155001c1c0040309000d07a2078420180401000350f08481c08081d61380c0740404422410301100c1d400c0b8001070516803080000058179610f9440780401ca0b00141c41e80b183e0f503003042c024401448119603e0580c0380030640041520780700100b001801900c20110307d801800011070005071100f005018103000151a174240440c40c4144216080102c482801881c6c132480c0c101c2000310400b00c01000f00d03410b840c503c070010051611101070710510130b00d44e50400c80d03444004000d00702d0f094405008826441c1404100c42c0d0303840c1000910300d079031921211820038100402841c1080764415003080c02c000c0b03501f41540782242c01842036104019100b07031000603001c0c1081100000401941710000c0c40100040c0c1444510f403585031035902d4640d02c02d4501c50303505610a80210b1040f1000c03650701c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 847809370 1250 847808120 847808149
    0xd09060f1b0203060406051b0f18040b030d02030d06321c060603020a0816050121152d0302011d030a0b0106030e030a020a0b041a01141c020f 62
    0x710032000100b640084e1030000c0c2202c089595548a40511060202e000b800d0291881c1252015041c01c00c103482c0030142c1d004880341c200c044c5402c1000018907480b01e038841c410500d0003800381c5409845000d0701a680e0b42c850a102500e0034035004d8002a41070301241a2188030b06907000b41442d00546804241022056403581980701c0c011b40d00400102d110030070288070b220300c1003a01190741c03840c50040040500c410350204549400010080b40100311100c1100d007a21000d007004c1d010b42c1d10980580c0040704d01b0200c8000540e14152781005c10301c09400e40c0d4800c03204120a070014040524640c503d005c000780c09101c200001c1d80b07005000642c0118022405440314984070071070f40242900203454410218015207a860391400144071035941406000c090f0000e980040d4a050400d800c002c1d590300d081c1c40041d250304900c0011404110402100b5005100080c202c041556121000c5802d5400c42d01e01d00e034800d001914032342100307914100010702c4090b001050308a041040304c0c144a044c1071600b04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 847810620 1250 847809370 847809407
    0x140d140304080c120304030905090703020414130b0d0818030a150f0b040603060506011205010810110f03040c080610032001230706050c0304080702011b0b1303020d09060f 75
    0x2d002e4000400c03139000c3c51182e030107903482e00d500c1c616110501c004840042c09100400d401000103000e102c0c186080c540c9600d00c140c0d090500c201003040701c040101030041e00c1517404410100124140721040c40a4842105824100c5d4180100300042559400c3c921000404031098100f101c000507940380c2c441c4005000000b004141a107007200040c08407102d82c1c2040f1203150790341050007001d5a200940b035400f40c0014100300001e5040c80c050356610f40b0b40107038500e0310f240c03503601c00301c1c1804101c401c1d102e00b0310848110a40f24280b5140185410394103014166a45c85008000741c0ca03072038240c030180100d941104104a400000c0f00c0a400c070708804a0100707041c0701122650b542242612500c184811441784101a11030b129072030002705850002d00042d030050401e1040c0804240f5039000c5a02d0b003030342420002c0d040302c0c40c2c03120000d0700310115001030240388102e030800000280012036850824842d9094649003003185a06980b410554000c0c180020080b45032004068020300d40c0c620f07031001450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 847811870 1250 847810620 847810633
    0x1120b090703020a08090a20040207020d0503040305060c070f02101803030207060e03010209090a200c2d3004150e0907020a030e1201020304140d140304080c 69
    0x2020860414080d00c003000001e5000980b84010b40c0d10500c0160000c4143c800b0303008000030340d2202c94446152102d03482d405111244500e5299031154100e80003554060100d0b80d40501e541401501c0741c005100030340d101d0090000080c1807651f00000c5410050380000820485c00341c5070280007104083c022841c040c8240760440d04902103401c40e0b024003d511030303030040826078101000104600310001c07045001c3c3c3c0c0140a00d04a568030366054940c891491600051009021800b00d88480d100042e13036114068001500e003810038011910f0401040610844403002d440c81030002808406807034040126080100314042c04020720740740003070101032a0b1600f0704a5201c10710000f81a030280d440b003007883c0c242d19102902c55402210794110728901b00c074010250301d400c440194840404180c010204082d0005070b00d0035a990754405850f204250700219100d2030075103070030210701c50000c00b84800c074401c840741c1e00c01c5d40c0c0c03013009601ca051110071080350460722647d56030200ca8100000d0800c07540a8a07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 847813120 1250 847811870 847811891
    0x1518060518070605040f090c0c0215030402031209031b030f0d090807050102010203011d06011808060f0a0e0a03030203100302092d0606090d210306030b091504020112 73
    0xd0191600a00348541c02002490030000c1252038007241d648408140581404200300c43d0340e0041030b800071104c400e9004160b100602c80c044842c0d60681000943c4032140310001c540718001b560203148030b28425822580310043c9010714141600584410315410741c0051421f001c1765521483c0b006039560084c0444992840340b40d29a8201072900061100043c401c08040010000400484004202c00e0001314075550504111240503a605a0740c940e01800311008540164801c91590328002c407082ea450105a4641043c0c680340c80054640d200ca1542e0940422a4105030384a204030f0729a400340145184243e42d5019006500b00408410518070503020000158032402c0f01c40d44a0100e4400c0380901501c180c0c1944a0356a50844a44501003039008109640d141d003c2180c00d40d550072207003811f04241c980390107159807041520726403056602541003105d4039003681002040e00e10910403000950b171200d480d00d41d0b0b400380455050b05a00c100b07010034090350044091010038030500d000442c0c00c48a0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 847814370 1250 847813120 847813133
    0x203070f09140105041413081e0307110d09120201090b07050f061608131b06050d140402030d0810030b070e040501080a0b18011415010f0c1518 63
    0x6540726880c01921221100e903400c4400b0340207405007808440400c180c90b8401c0c08010070000c024500c5c0d1100b0162403410062000107000c1ea440012401c5400b50210610a03039544950429107010010403440b1860b5081c020012034801ca404009035105500103142607442c0c0d03165282003005a051000541010070300306c00940c002c14403603014000070541d490030002c100c4d10340080100804142030522a004021130381c0152900d41200c69045c81c403081800a09000d0300c110b4021301031a4000031b80840014031160004083c0c0003c0d10031210400c43c0006807842406011005c507402545501b1100034010800c1c05110f500341c0044181521f801c81d02e450390f0729440b4400b401d071400804549190041c140034586405242d000d44103038005040d000c01c05507034009807003c000d81030030504011100349141c40f02095000a0002d90402205d2a10741042c00c000c042e0bd041031100c55000a080240d800304d2130b0301440200d4001a840703462180043c80054016000700001c035940741c415881403d410303012545 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 847815620 1250 847814370 847814399
    0x122a110a08070b0309070e090705040c05220e3702040305070e04060b0607030219021c0f06140105010212070f0b07080910110a0810081501030b0a060b040b07020307 72
    0x15403040541c0e0f00d085c02c07028181340010552000b41c01c2d2030720104005003800041440c0e4100c0390295008603c03000c01441c1510140910403000c07001006800c082d0306400c503402000d400b12516591110341da5141c101d0f000c40c00da8000721120345101d506100c2d4055a6070700c90424801040a00310042c2050344954840b41004101d50014410203850414017042c40307203502c24102810021544545030020319a0b000c0d460b0030390703000c0804040b91001c0034003095440d08440c1040f4169401c58a480107081072030100740c00c0d5580700040d078585103448240a100e4040c000d141e8141c4a0580080c4103050005207441000d500c5120200d90900e4681c220b100001d41940f0040d00840094482041f98030f0100301083c0307040d01241884011a09210030200f400c4d04132070480314600c0151038100d140703903624246208e619607254070a40c403074803416546400e007006161810381603a10a508055081c0c03140d5a550081d0b83d854010207d00e110100001c002c60304004004143c076500c06030a6170080d680d0361029036641c61 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 847816870 1250 847815620 847815629
    0x50303032802270a05060d0603031101060302010801151403070914010c4103070506100503030301090c030e060109060501030606020105041e050316122a110a0807 71
    0x2039281c0d2509240c002400100c030705918094085050800c050390345543c03c010400c03081d558480c02404102140c85003826440134080182c44565128803074a00c50b802040d00d03100c00d070005660300400224180040c0900c030116901603551780103a0342410300a4000c0c580300603082080c86a681c00c2401c04640540185226083c43c0e260341c842549403a00e04e22440050045460412000c518424002006500344804e6641c600390028240c0e00410810b0f140080c00b2281c0c1500b0821407000d407080c024002009110701071240080c2c6e18141c8580900750f0f01030425000302d981c9070300148014820114142d200c1c04440e41c040c640450b004a0005c4218204002a04070742c1685440e10707414415560036004980003801544000c0116140c1a2541c08a10b10f01104d191035184501c00e1800900c4000c20650380c000d40707190554402d0403c0e038900044606d28106038070011403600c0d40c0314010b50702824031028108084290300442d901d815901c0d81d0005224041c0c140e0b12800044000c1410f0508004000103003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 847818120 1250 847816870 847816891
    0xa0b01060903031b050d08060f0a080a0611070b0c0a0e091501030e0c22061a07050d0305010305100b120a080304060609020405150c03070f0803101505091905030303 72
    0x240c2c207506004040c41e2880b59400c51418409550000190001800200c3c81c010342c41e090320715444000c0000d42c61040003520303e034000c0d80403002081611001c1401c0c500c80d44100010082c00c400022038006034000c00102400c01c00701000060709421908000b4001280d151900c428201d01e03280008044038000d03121134202486140d080d6441e03507003600c03680c058012510b00401c0358840440010308800b405801d0904031800c0c010f2404400e0080d604110040c0032110700d80c08909461250301501508542020382d203500c0380b1014026810700910405050304c3d0848040e0100c03406080f503d8010388141500385030007814002c14034108400c1400fa000c1070620803030b100352b92820f080c1000c900f503c8003a0840b640007441040104441d69880c080a42d6807148010103544030000b025140707041d80210807001c0d00c2c3c2e0031401400e0040014182c02940305220740b0b9100308400341c0300d103030b0881c20900c0d80000300d021907400c01050381c0503d170003580e031802142081c20001e044c1c1d8443d00840d0541d04282d41c2074803034 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 847819370 1250 847818120 847818137
    0x5120115020c190b09120f03190504030b010b0304021f030f0e0111070b04240912031a06090d140a0320030d0b030c0a0303050a200a0b090a0b0106 64
    0x754148400100703194100c0d0620010199070700c40e0542195980310f126101e04002602d840c1d5616040c005001c0726013418242d44043c4a00c8074200e480381e024101000c900c03080740c01d0080300c06001d0300541e400c1e26046200b5002c1a0f0810294a4107944060820b99210304007090074900d8658005499401141a503000719145904222580980d810240c1c84c81059051030b83c0480b08000b0801503803039040e04420203880319110381c1803a6100c1d0300703087c548071449024000e44102080741a00840c41252182d034003401c00c26103465048040380c07003410b00003044082c0070100d01d040b45401030140c81c40d003c004000c0f0107040445d66600890303503030284102084d508281c81c44414107400000034104640016074589080803001e51040d200e00c1008021200c442e91001902e8150702c0420016003400000307000145103940b00d08015160360000480d000006091900044200f60f11012030410341610070300030501e0b10b0a41d070303c0409810004000300aa84a900c1e0448040351455412a000305669207400c1c81 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 847820620 1250 847819370 847819409
    0xc1e030706051b0c100f1b1a0a0515010f030b2206060503150108041a070c11120a080a0201140109020c071d0403080709050604080f011805070603020a051201 69
    0x3184004403e116429401c6020030755695115240320100c2c046543c82c00820340001d14209452083d401c05614803040030024241e801c100701686a00011200b0340544881030b51902d0608083e82c1007181e0342441020650b0404150b9402460000440001400c0100d100e140100115048900004088030044062040030300b4220080c4504405420b40d072605500d14036144400b002c42088484c079440c10000d07280002000e210082d00d40c200a5044203001d5441824004002440f1096922061310b000343e154600041515050b95a0031900e0319900241482000c0d03130301e03801d4150f04006426002c1d5500c4903e03200c4085113040844c1c0c041c000702c9600684030500e07801041c2c60b00340305400018000918580c0080e400c050904001c0e4403542c103180034a010307a1031440c01c40c3d00454580c42660040c1010401140b90321000c2142510744022100800c076420a01c1c5800e56255035240020b08950440403003400264801d4004100307111072030070500d1a1400a0000c035a10302005d0303011031014201c0f0200d586 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 847821870 1250 847820620 847820647
    0x4024009151503030e0a0b04030501050f011509060311090411040810020a0c150b06030a02041715180a0c1203230f070f0c03030206040c08030c0c1e03070605 69
    0x14081e0852082005020041c00032500003000a0001809020514400d40119030f41c03a111a8080c3c141031450644031952032800b1400381500380c800d031500101100000c2600c66800448101c440c0403643c0e01f0301081c1c60050207a004048102111003481c0d07003000008065100d6000d40640084c0352010203545518004d500e50a1060340300074840710600402c20840080c2d81f00b03150051060300300c4645c15880d002c5000140041104140c01030300b2240210030006901d0b051b9000d8422a165442c02c81100c2002e1100300742c5581345d20000c50140a48080440e600084810b03001015080110403204582800d88503501001400e0788600c1c09140c410000b08109a4060642c404c4501c121400f100110442210302010b07014801c2d002d00300c00d02c00300321607040c800b0701e0010039815600b10b04880842c0da100d0034025124801241c00380d03100e222003c0002040368000003102c8a080c0c10001900b4039844402c00c010f400440c501301d002c81c140e00315459002d9039030240244030080c41240c54031a81d400f40a00030304c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 847823120 1250 847821870 847821893
    0x3021c0c08120304110103020d14091006050607081b0a05030a090e190c050d020705030a08010e041a13020301150602010e0703031211120a0f050c0304024009 69
    0x41d025904101800c0c4101c90b5080306032900145d0040c00600c00710405030040f0001d00940c8402e8404c2410401ca003400109c514031480d0180010109443c11885400480d4043d034005200e22504040c040103034402207801f010140101e50002404007060b601ea045101c0d10700400b059040e50282c0002840303c0340c40340c22046500040800ca01c80c140381d4074080040740001002c2d00303494040355846a07001c2000303c3c132030341c203d48203400e108004545034042070422556075004155000c01051482c80045509a61284a03074861980020600741c0c80c1500041192050009800c101d481049070031040700580d420b004800a0110b8088882003140ca4807500038252a0505010754294000c070b4000c1c400300758403c58a2030204000030003c500100ca40709002030380c1c4a0030100440664101d428040308101d00d40141228003041c90082c4030b1919490f030f030885284801d0f00c1c000d40c8540b900c401291a030814600c0340002101700402d00d01001c0c030840d01c0e6020211040d40c0b84002c142e40d0806c0c102082040c01c1d01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 847824370 1250 847823120 847823129
    0x1020405010905041805120a0f140306040e071203120b0402090d150209060d0b04061a0a03023f31020f0303160c0b1305060c03090616030806090c04120c03021c0c 71
    0x4040700b401cad28400700519210140a060059444034008480381e00c2c00c21100005100990340c2d00d59030303807031030a008182d00104808007150500301410104513140600984205030b800600d80e0000c98626079a0346e01c11002c40385a01381d4290284a0448250341d104c000c1c0c460184154000304968600c01c2c20401240d41075040912050b00b025100803600c1852001d42d09020f0b180d0070f0040e07441200d040607400d42d141126100b8404175180942102031400c8400d00716110340c0d24142080380d5103800c140301003015000c0c2c0c543e005201036540401d155140760a8500c211303500261868050800040100f82142d12902c0402d4001d0b25502d41d1b841002600e1804d04c0080a03070440175030410f0034100226541e11180e22440c5d00c200400f0a9000400c4414011500500d6004020031340e41e5919007070441c41101201025004500750000160355410800c03a0319204210b5052480d140034100702804682c462800c074141e441e103406400200050702c0f500401403102c49111030b141c0b4103404a2130140000d26090300b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 847825620 1250 847824370 847824377
    0x36030d02010c140921030712090321120e160909020f0d05030d05041a1f0312090308030907051915050702150a030c020f01020405010905041805120a0f 66
    0x1480e0340b0840d404007007488a0402502801e0f540c5a00760000b40301091000709140300d840780e003600e0f90300d420000801004080c1c4141c00c0104d8150007e102540e10081c2e0307100185c901c070107003800740001c452400300c2190b106c000d0307040c0316a01d03201c034000001c11552101d085e01b00690202000c008445240f960b000e0041c08020000d000039140d46c1d0114518400d8914424001c03c0240c40c103c0401000f4400c0d45c01665644e103042100345070900b000c0060040100980c6d002c01c0392000400d403940703010403001a500341c0d82c06036490400c0c030b9070307070780c7c542e9120700340c429504001030b00c88084001420880110f009084400080882605101c1006065544911001300c5144900c0c0300300000864100ca030080d440c105d092080e190b031302b42d0001c10440007e400c01130140c46000101c0710081a0154090598501d503035007200c030184c041040c0d007801c03407146000e054046403e0700340030005841c0c1a00a07180064074100d0681003101599071b09072900900711010b03c45500301040810045600000e60b0030184290324 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 847826870 1250 847825620 847825631
    0x100306180614220203040c030515040314030f0708091c081e1015021009060516110c060d1424090f340f0207090e0601060536030d0201 59
    0x2070b4818000e03d4846903068241e034002c07000805210340704504900071078001b001d55002060300e4000c040c8000342110100c0c003150181e042079035450f4510040d1b0784101d0600c885400107450348202980c070484010301a1802c2d210701c074403020b840e2201803051082140f194039800101d0600d48a041d403004560740680d0703070000c1282c0402625140c0110394008581407002c030038480c0402c910003203003030030b40203501d46a100e820015460100491036000c9403281507804240590f40c0c000500403100180f00c21040341456200340c00d07035100c1c0d16203c0000c11001140b900c000400901e02101640b4023034003215002e141f00e0495906c408c20720078629214140c800301b21181087c1d450400c41502c2c056201801134141200c6d0f03140a14100031002c02e07004018169501d0505008440d004010300c0b2803c880c4074100140115000001d06409501500c0c0500c0b407080c0144c019a0f00701202141c840d000060030365007940c517000708018010308444020307016680070144000d006041d801410310b01480803c03450116032400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 847828120 1250 847826870 847826899
    0x17040c05100302070614180a02060318070509010b03010f0b04030b0c0a0c0b15040c020a050c0105160b09010606030c05030405060103060509010902150a200a02100306180614 76
    0x180889059590484404607150780600044000380a48000103069600d4200340400307462003040c00c0ca2091309040f80c84940c400b9010301c01a202e410b080d90003034010409202040420f055110b509810414036003c86100725031310030008a1100c004c1c3e010720b103500c1c000401480091b807a00244805007100e80c1c00185401c0c82c554880c2480305004160700c030008008140c0d410310034407460350b19103040d40114010080303040140c151441c4003c0c0101880c400c51811131106000b43c00030034840b408a4205002c0c000f03002e03411b801554035600c1040080c803084030365104080015071810311540103002110000404506244020341221044140b400520200380304010006100084072410b6030b9003d0340c0440c030703903d540080c00c0c050103801c2c1c8000e40c0103000440311a5100003202c040c116015281da03e04512000407842d039a0080c240c0090706120350058010400503042c25030a129041010349000241c00307640300300c1c04007003454418240c220992100c03006c1003141400d010007240d51030201c440c1131451240 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 847829370 1250 847828120 847828133
    0xa0f1a07080c090a03020d0506161103030f090a14010905060105041b030c020115030803040209011205282a06050301230f030114010f0605090d0807051e0d1704 70
    0x300301800852000514005a403241d813206070045501820079000d000303542c81c3c4580c90369012036003020400c03650106001c400d48036196103885914244091440d64450148000d48010001c0401d0344a118403490b081c0000c500010200ca400351503400003404200603c1d0040c1081c0060744818072550401101440010603161078004130401400d00083c18888508243d001d0400002c0786050000030940000500283c0001984036a1080b50a40160fa0700d88407000c0c049800301c48058010307800343c1010b031310002a081d402218480412000c810600030342d0340d0b01120f1000c0d483c2101d00036200c0d1000341503c030f40e640e002401a100d5402d015085604142d10003038810101c10012500341181800d00c0c420303031031300302890080d114003400a100201304901c0a00c4050303000c1c4104010826103a5000441511450a0369207140005215403910003640d01c84420740c1d0400c00d030594090040c00340180c0d102103006c0600d04010385490241c4800101d201010707103581c01e4140018400708000c010040003468 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 847830620 1250 847829370 847829387
    0xd120e09101401090b0f090306090f071e03150b041d06060f06270117041a04020f0a060e0109080a020d12050c0304060207090605031f1d0a0f1a07 64
    0x40c2e41182c2c919480c0107800480c0c111049500c2404103100000389810162400702c000e0084000540c129105500d4801d1902c0e0b171503100c500801d409802140c020721440200290245403a20712484003c440b07910383e00c840850703c144054800c0180d03510002442141418090b20411130b4400030022501c0d5440b407160394075010001d00c10342c4100c000d040c580781c85130380d44010754a0b03c041c006420340d8121102060941e03541c0c04002e4690100d002d0b070080c4240d004c0030740011403245900155074035440e680381441a034103190140080b688800c45481303101d1a511010000310061542d80e880700a030b004001f0000d801d00e03e02d508004503542001510001589a0300c2c95041800d500414401302c080000000b00c60030f000f584880b005a00001900142d45580024850280c44071000100300d2071b47d0742c204055841d000000c04400d0060803003a40d5004410329800000146625650441a101050700607414010443c10480d2540320800502c828071400c007001030622a507100015210f4204a480581481d6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 847831870 1250 847830620 847830629
    0x402090601050a0315080109021c031407060e03030403020115090b0303040b130806011202011706011d0112091b05010905152d0d0e0d1b020307050d120e0910 69
    0xb200103101e00c89107200e50312102031205500c070048142c40e242c02030180680681501603108018030412080380384891a442242154103485280c142010f8210100c0960007030901541c5650340d90380142e1024105100961040348a6030000642c3c12280c204c410120204c0c7e00306039506450042e80b0101a140002100d0585904101c1c03e030322885144e1034045c9075041340d04002500d000d0358000055002d0810200728a040c400d882d50714038600b0030809a0340d4030100301e65680c000781c40c2d5400e600511415010a10b640d03c6d043c50000c40d8405113242848c01e94071200000c542000050b9901d14000c070030f00316a000501024079000500525050000721380c2b21840c2980841c0c16000280d12850a0040040d0020741e0001d148440c040304e0180035900c0680c00400101c5001c604009510118590204001302009440d031100301000030039a507104da460700b09201c2241c052003614400714060b62055400c04919100d602d0b901c072082c4c0d20f20001000040014940d90040301c402c800e200b004e02c10041500305a6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 847833120 1250 847831870 847831877
    0x50f07122304120204063b22020109030b09031c05060105040e0a0605090c0a02060a0905030307030f14330d060203040302010b1009051c020d12050d0c0210140402090601 74
    0x18400c44c00020001c2101d81c0c44020124207000b8103419034185411a00201c5a48802000002c0303100007a04941110441c5c1a01e1001882081c008511041030182a140c600600d051824030351280d4031400c1e00c08094548140c1a40046108045103c0940c14288046c0a80b5014401400c110001800c14026070048020484d074040c00a400035000f548202d0080400a101c5061400d2007070740c1a50542c007003900e16005000304000030303120b4a4a0300030790f400141d20500451441d51502805c4000f414100d0f0390404c903640300d21541000400141840b801110011001d400d0040207002c0305800004032003800045000b01c6507400003540c0ca4520521103250001d402507030729903ca280807401401c1606405034800c2c05030040c401c240c0c0e400503040d8244d5800351902581c04034100f589150140600c00001d500103004d014010001d58004030b44401030255007031460604d61450040010394081d403223440c006a0000011b240031a105028080307207440441822440da081c942c002c10540400288101c2c1407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 847834370 1250 847833120 847833149
    0x60c0f141e070f1a21010504050c1204030f03090f080406020708072d0302030607090317070b06101b03030212070f12090c260d0807091203050f07122304 67
    0x2284c1080085418018500111582240403218100741e21442030168502580c50a000203038150008000c40f49800c1812203400741d44c1c5c0d500d40c1e08031022140002000f0400d510354170940e0004030f44501e00d4682e9032013a4255034540b410040028a86042c580c001c076a254048c1030b0800485a4a0003a172196009a903817480c000507500000520701c0d90030394030081d00351040c6000c10080540c0150101d05a0b0300c50244070f0000f41c9d00008403684c90040c0c04e00039040c0100d40e00420380c241b500000220440000341000040da0328000190700182d0900c0005802290300001c2030001e58018030100342e032040d25410000750540003e1070082000b9000003181820307039035440442c800d201c281025040100000348460701c2c640100b01d1b0300c0b15001e1841d5510301289c41505039903115203001d00705580c46110203a803907660151402d1101c450603020401d060717040c000100004000b15902e10300802542c2d000c0c060010f808225843c0003485401c1030302c081d42e064000d000e6034285c0e600518044030203c480c001a40d050 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 847835620 1250 847834370 847834409
    0xe0703290a15022506140d0f02190e030d0c12030b0a060203041a091c03090816140108060102060a0b010905130501151701060c0f141e070f 61
    0x1a0010142c10032840042a215158101640000c01c006001041050546115205800c0902c503500342c5c003030400402d0003407021380500250140030340652800c1d104089070b071031010010b8000300d074040c01150b49203180414801111540042c000540d4590580081c08450360b103900042032070340103010041a0011040b41100e07a0340c865000800c082c04020710b50301250369907103030107981c990091040300135003200d0710340301d403262402038042c0c44001c8005040003281727540d00782c0306011a000d070000840601950030000f0a07000d2007000107041c00034410001486190030412081504405e921000b0704102d807480c01c000c0d860764007041198110302811004030b001e101c0000141c8a200840e04400d40000707558192182d00d480302c0d00801d048403a000515020f1700e40701c2404549198100a01b2118030452a0040042900c90500a0314183c0100500012044180c0d07518400102e6105590b917103500440801c0e4401140e80780380808808040c005150040c80c1c0700b108806d40c0700510640c1d46032200c5020140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 847836870 1250 847835620 847835629
    0x201110d080103150b1e0312030606092b080918040f06050711120d0b030607050703080a06030218041104020c060612070e0106080f0610020604021e0a0f0e070329 71
    0x1e40242c00600800351004401d00c50001b900d41c078150f00d8424403529080d10541c8800300112806070a001d01264a800991028000b851840100d90344807030601412000240c420913001d0700e10907100e04901e903954401002008042c0900031005542141c1e0103080c0400150a42d12601c0c1182d4071820200d5143d55022041d6581c1034542446e15042c0101100d420701d00c0e103000f004140c0030b9600601040011010700074942d0b26001184c1c128007041c000c10400c3c000c00d00606049030b02c841e030301501140254a81d40410940d90b21840b0407603011060005210401401d0b0385003024640007500d04500f040003d8a4250756041c0c05484940540710414075070804c1c56040c84610041e0841780220310403075030744060003011980111a4192200452000320305949022101601132003d0743d0300600403030700d80381c00b0400c20186003203041c00441e0080740da001194864242201c0185205141951668907000d64840030000090800c002c16207410f100c034030810403400302c96403103004046034504145003980108 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 847838120 1250 847836870 847836881
    0x906080a0f021f03021201090e0d031e0914060105300c04051e0105011b080901031e0905010501090504080a0c030c020306040f0203100606050d020705010f090305070201110d08010315 80
    0x201500640d0320900b401136010340041c070524250100b030078256031340d40e135901c03080741c15079401c40140d0f803c440c004141c1c4078400e0304906000610400d10b04a0800090381000403103050613800c95a004c03141c1d10541070042c0901180380104000c0d11410140e404074103070343e01d12280b00e5800c441c07803907207080c0300100e840001c2016606800c07020340100000d041407250074030541c25032035408184000b00c100109841d44100000f00d24030790300d03c200320141402542c07217100a0700502000c504165844a01c0c0e242001c10f200c95440c03209010314001403070250f0342442800d40780142c202d42e03a4181008244000240e407a8210390106240c1d00e0f041c440d42c901d42c90110381c5c980036043c01070b41c544145010b01c028001048a540007051003141140d61400c08280640305a84040c800c1c0c1c4d0124509100e00082045690010590b09100b20000140c8641008400c03084954400f4280c0001d100401d984085503046030b48074481c004490018002400983c1d0300a00344041400010b0135030140c0340f44107485c0340558028 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 847839370 1250 847838120 847838149
    0x1a1041060a1412011202150c0d0c05150a150f0b040e040227240306041b030b101a040b090103020f0c01020c0f0d0314060d0201180e0a060906080a0f02 66
    0x1400f0f86965241c80b448011003440c0b000364460342d171410020311301e40c54010880c2c2401501c00c0150040f2055401c051302d0140b0030b45025606401416903e900822041300c503144240c090210000340d441171680c00750030400310350700081701441840301c0038440d0002003400d823421035141c1030241d24135981d640b0109440040e181d400f10070b10103a5541d03d481c1c800a00c0b5625110b1180c1c1074002c0c401c050b400010410005070701207016059002500401c000c110b401ca400018010b00300754003031441d540ea5035000204a012610040250894542801408035800703481d049074000c610f45034200342c2000c0705032510b44100290744d0305160380010340d0403281c9810300c103030765090301440000c40d11100da03500c0c0f40340c540d012000ba2501314003d0140d0b00a2060191144088102c0000f502c210140c0c1d5403400c2c8080c40002070800d90500080d40101c50003034503640303241c0b0050846051414200e081900d071a0082c1d51198000c94005d501741b8005000e401400120020311a410034203e506510640c00400e580442c1c0300325 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 847840620 1250 847839370 847839397
    0x8090a080307060c05031509072a0b0603030306090c0d09020a031407090614010503091c020703030e15030a05060a1707140d1a1041060a14 61
    0x2510003800300c0a003600030300600061100f20300b6a00100da892104843d4000d910203d1040030186040c04607a45620a071a42840415800318032000110f00c004014040b0510045c16031640802c80656400c0d904500180e00860541c240800000c03a11003000303002d103042c3d290201d10f107030080001e40c00a248103500500792004507612410710740300440c11214540080e219a07100000c00c800248501c0b0304031403190303844604103090100115042e41c0050310340416443382080d00e803448000f100c0311156124845d002040180d00e149006801c00400351030881c4078034000c3c04080501440c031400c584c1e000c90321b014002101e40d5180000740844040c2c0e0480e03811500c141000e003585150008044c0305031881e80009400711015441000a13100311310800401c0006070f0068400b8035000d40541a4022403d14804184591540c41b151030348074810780d2140080d10400328040d9054049001101c0c2c03080c800f0700010100b800724000c1105407290240c03030b07020003688003c0180c4910303100c029640c05040c2e01c1e4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 847841726 1106 847840620 847840639
    0x6050103031e3509031c0203040c050423040302030418020c0a03140d0e010b0f040b400902030c060a1209020604030f030305090f070b040306090809 65
    0x2040f0000c2c0280c01c03101407203108503c8000c140716200c5100210740300e684050200707001ca44001c2649055902c1042404049400c0005120a440c010f40303000c2590803400508030103260310f94103085014180d5405210070141e020004100715000441f080c1e42d460440b801c20000c912500b106001d01b81d0220810000007030190000c0d8800b010800392080c00c104d2288a21000e03500201520b10081c1d5450f034904130589400d01c4050a040340c290f408026006600c0c0104000891403488008148010162003482c00011014400e20040c2c007407080d0001410754000350060b0603039440c22846401003030035001ca40d0405100380d81000c0200c1d0b4a8840008070544180c1c014501b8050580e007082080002001003550030300d54544051082d40c00080510703001c90038a00704000d543d0412081d4118803810001082004203503826203800c0640080c0400007450024260300c910b900c01508000c414 = true := by decide +kernel

theorem cover : BRFrame.Cov 847661870 847841726 := by
  have h0 := BRFrame.cov_init 847661870
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847661870 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 847661870 ≤ n) (h2 : n < 847841726) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
