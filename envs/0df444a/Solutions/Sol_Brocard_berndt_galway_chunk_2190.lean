-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2190
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:56:16.997418+00:00
-- url     : https://prove2.me/submissions/52f4c77d-263d-45a0-af8d-90bfc1721193

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 393705035 ≤ n < 393884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 393706285 1250 393705035 393705047
    0x1081302100c0c050d020a2c090a060c080402060901182303120a0512040602130b0702090a05010f031401020d020301080a030314060d0b1305010507030903260103080f040b0703030c0f 80
    0x4000e400031032090041100e40034030b009001c48c12111108540b210101d0b08505c0c4071111080d1002c0380c00b038000305c0180c3d040000c10701c5044204c10607803c00507964540f40d0000b5a450080718001814021030040c0d44000c80d000002034005401c00f5048824540010a001d0682e44280004580039214a07004240501c07076210940c0c030032003d03603503c441c50400056040031030040301420444509401384595181201080f070903402800302c4000c002e4580a1900400c954904081c0c8007003d641e10f42401405900180c540b40c1c016690080d4481d01c0c0211070b12a402d00902c11042820191031011002140720314000c00c030f4081a034000d43e418000c00c01190b000300c040c0102500c95030390185d2807082c108005202e0000c044e5204841d01c204100e4024151203040c01d50308115210740010303540b10000010507411030380c2d0640900142403002c0c00c0c0c8070048002d90383c640060101601c0003070b0124815a01800c0c4008650103814001070f13141d103842c054038019002c1c01c1d03d209090701040441030501d940303601c524 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 393707535 1250 393706285 393706309
    0xb0103140f010314030418050601030f06030804050d210315060203040605030609180a0c170c0d0206030c04090905070302130209030606040c020a020405010b030f0903031501081302100c0c05 83
    0x1d20404403592840d5980b00b100a0180303002030080c041440002008410364000440e02c000b00310700880e4500c1c3c42c00c00181102d90550000d444645807807000c1c00810002c07401c1e901074a1084d00e4007a0f40e81a079003440300c00c01e4a0258200b01000c15850b004880a9254001040700c5507030307a1001c3d402c0c5480b01e00580e200d01403801904000744080c00060803d19084a401d9000340440b003d0900108001c0003072810503100301c0040d50a00168203003008490b000014a40c10105a42c016160746401d00c0c0001e0010200713460040d206030300c04001304010380310f440304840c010104034004101c4840300f85412030b03c51280d0310041c0e00c19480a4103800208005008980900c000200035054541c0d94404100040c13000c000a681180309904145006885920905010b0559900915100c0c508046122001ca9000b419203a86400c140240950306049621040b442e103001d080104007a0350380c1002c030410307500180c0301a620021b402d02030f070443c680004084010f00c0c06001c18291a544800c1804800c01d124 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 393708785 1250 393707535 393707551
    0x302030d0c110418082706040503030304060518100b04050f0702061b040812070212070503072d151106060f0618150c06090c0603010905060103060503030a030b010314 73
    0x1030b1540c0d00b00d2506a0243c0e0030318021000f8000c1c100e03e107455402d01a040212a03a042184400d0b0304180d1403000700520030811802c89900345450f0501c80882d4581c003014200078003554680b00460785a0500009904220000004890300844c800d42004040c2070b401040b2401240b5040210f41023401c0080c0305485640a50014045626005c215a40405110f9202401603d0912000c0b442180921583c00a0804081c4036070325000b26004110582c2503201c40c3c0c594651201a081001b5200032807d1011214a0f00303130b1442105420030302181c060350040140422002c1c9240c0030550f03150b4500143c01000081d96055282c0300b502e0201d42c0d82e81d02c280c1b41190301500d10364036046139140110081020111030703409200007400c402c0c089007403028103030000c0b00d0398880070408601c2e110b802c000c1c680d48034140b04014012b130700d1050f0119a2500c4107000e441036103a103d80c0012070766401381d0001c0e401807501170200d0f5510a91000000c00410780604103c1c0001e0030409151051524208124040c4a0b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 393710035 1250 393708785 393708803
    0xc090302061b010f020a030c02100507020616050409020703051b01050108071e0509040b16020d0813080909010b0318030301033503070c0c05100c030e040b04020f040302030d0c 77
    0x42d020442c8082c038152100240743d43d2a1100c0312031994850000d071a0402003030300e010034038030001800642041c0e040800c1003d094031346410808166030000b003a90f0480303031040d041641c503a10600f04076020700c90741c6c21501c1c00764000181b10003010342c01802001086441c44030004100c25020390103080c0d4100f84030341030301c69001d00000e100c1c1d411144413004170a41004d280481081d51f6502203180701c00220f4040e1303200f031000760030071a04800040103d4a59200380c400760140c5548208080e20340301c0003601321041445200b25042c2001540340032107901940043c80103403e0b603925854024998400c50f07810080d00811241012a201c0c0002a030303040e20707401003240050013004034238142c0310f00301c01e0001c12000004480400c82844100c00450050b01c155803000c841c0c00413420400e0410a05a01140c02141c110307045602940d80000400c0c02543d26292542c1a00c809100280181102c0e0f011154400e1001441c1540e1010400040040301e1080e0299208415000c4099414600e200c00140805c3d003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 393711285 1250 393710035 393710047
    0x1403150a0507030e1518060f070833100302040513020d110c01090b01051507061e0c02011d0c0112230705070221030a030b030f010c120c09030206 64
    0x18150041d5910594610b000141d50400034102468a0b000324120b0560160348000d00402c180b15111080d041030054006140d40c0c248a6508001400024105e20030043c42c0d1000c202001410006041d02c42a60900c1e40e289040d20803190f07143e0400b0500741d0f48950210300801c202c0a00900a9500f201c1c40100440300c41141e0301c070048060350124485019040d40d402c9071141030b4900d0b60103000702c20060070000508074501d107005040501c0c181c0009202d440c14440e03091642032100d04680803554460f0010981010a1a190f05410588035450303c1c002d0502c441c0b800d64507030562100200e00e1028401d9400001c4d02a2a6070b11846070a8000340000c2081000700c0c03405c0b1040d00190034030b40c200880049060f9061218505406c0d0a40f00300c0000385000407294151301e8140c040d0044021040112822010130b6400b06560340315400c841c505040e02c910801003259070900c041e40b20a5250300081c016800000c5000300561348849002101518020130981068030446002041e82e9020700014a810 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 393712535 1250 393711285 393711301
    0x10f0e060a0911030f0603150c0c0a0506011409010906051c030c08030a05040506090c01020c0d1410020a1103160308220803012d1715090601140315 65
    0x201000300340a030403001c0050005103250a0344159444000d1071401152a810031140650750130f1406064030780f0070390008002c00250040070720303010340055248003482c0d9980c1c8010807031414032090220281040c02400000070380300413035400e1403060080889942019a03240c00e80741c01207481c140200d175003042d40c1240c3c19900361030b20175443c150036000b130504503005151a560407482d50b10440c0c0d4a10141c4e03c0b5000d0004004080154581254401000d05041701810000030744c0c9002c9250b902c1d204169041e107074404c1c040001e6600c25010420015a0381c00054802280060345c81260b8201c0000c1190402c040000e1002c82541e10325241c0b00045030074402e0b04c0d141150700140c00341c640108110101000d284691346002e80f0070560340f00340c003815181d41c54108050454400943c024404290b07284039006180c0d40305109030f054030b0a5120318101c1c1d5501d454a0b07480d24450810802084503403e00380064854000b03181da04030356080711b000005003c05814580c03074410400c001c00d01c42c505500494403207 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 393713785 1250 393712535 393712559
    0x305090a0305031305010501060306090e0102092d031b030f0d14030408040b0c0d1e050904050406020f03100807140315060319081903050105060f0d1418070e010f 71
    0x2c500b40119960715411380340c5800d421540281d0280c4080303961000100141c000c00d00810744100c0b03c080c000c5080c410810040b40b40100354100d02c00701154040401d442031a0034602d602603c2c0400740440380da00c221040011140000096024070a1040d150b50b5800c500e800649941041d0440d1745000e96062a04d800724010340010380121224441480b01050100848002d404403038004401041032418500010b0079030751034082145042808401000740c020f8118089683c2c0c1c40c010340f00054503a4640c100702000b80280c020603928041c0020a010a0200c001c0003441511125015034868a6030369012242070f49000141d141c040d04409201d52a00303104445444d8130040143c00d8400607030440e50009215200c140b01110b030384902047c000c61514280d21641201501810100110350403c0c0c0011290b0092007400c404250300020601e2000a054000303011040740c4101f2000c003800d210360391040c3c6c584000100300c810b22490000299503003810448904948202d41c4007944942014090101 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 393715035 1250 393713785 393713791
    0x70f08070305160b070816050403031101181a070203070f030e030c0306090a1a01030305160c0e0109020403020906011418061b010c11010908090402090d0b0405010b0f010305090a030503 81
    0x1444018098855043c08096102c0d48040c411880d1003418039108401504065001d81468140c40c0c00610003000181c005044038140d035054148031842620b15900309000d00f40240b08440985002806441080b1080352180c0550407070381011a104d03911000e0032a600d008540014000104450b91013011900070300f20400c4030000582901d600c1c464000200749030520558042c80720b60300c0f46a00c8420301c0503035a514480d41d008001c000415500d1034500421901445208202d88046420702100b01702c0402c1c105002003c4800b002c1c005584e443c8800c0000f90000d10080e809880440f0000e03600d98456101d5424030b0052854041c06c1a01c40c0d56080740d103000c80a00a5081082000640d0f0305140d405c0000210050031000491a03042e00c0100410a0303e100043c40e919a0505244a0015000c0300940f8030000c42640d0041e1988501d5002988100c1f5842019103420002000e110500c80190001030000c1c0c1c081da001610702400000450845004442061040d00318045040010748a1801150 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 393716285 1250 393715035 393715037
    0x30105013e0c18100830250209010e0f04060e010612050c0103060503060907030b1b07050106080d050708090409030201020f131a0f0a0f02010e120706050c070f080703 73
    0x81c6400107040810b904142e260700010b2040c0c02d1008000045404469140141101c0c80c0604006d20150007030303e040d00c214106545001001c2241080d08522000c01e84920180d080000c84c0c2d204071f491211340c9507030b504010a90040101d503002207004e141d40c84085014400c40ca85c4543e4035551364990000030500310201090954a8910004400c2c5648030b00e03151080c01071f030103803459140c01c0001504542c01e55000fa80642c01602c100008401c0100341c0404403500f0410075191175441e51070b40c1e0080381e00e400c02070502d00c50200b81c010038003405520100039110040100c5412040e9140143c502e402034074001040d6100800c410003042c1015084460658800e000160401402da58045583c1d004400c210954441840b01000110a0111502c0700010240f4010741b03480c0403490b02903000e204500c1120b050181c01f130481b0400d98400d501088814461100b41c4400c0ba0310714000c05090340c000b0205451071410030700815200c900b107034111100c0070380c0b00002c849010400d40d04c03141580c0148400760 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 393717535 1250 393716285 393716293
    0x2100b030f0304060e03010f05010302100309050109020d0302011506080c04050609040f050c071505061c020f030610090615021c050d02030103030804020301140f1b0c030f030105013e 80
    0x2821004200043c2c00900669155440c04462035400c0c0341c00c44180c400f601c0111420b1400400150702c980381400300080d00c07450040342d450010b040c118050480c04100a4100c002c0e801c840e0705050341940540828400e00c650600070607038606080300ca070b41c030507100d00c480480d081208104500d4803c00802c802035003d0004110640002000c4049403000c45140041500000e00c0d2000c01205008a9481c803010301010022410584046000c0e00340c0e0040482c204842c0c204294250b50301d84541d038541a03c010b003241c8451034402030b8210100028402c02200750f00b816804510310084012040d44401254000c1c24101079101800c00c00101c0ba000c80c2c000d001d02080036004c0c1200b00d00045010314001e07110003000b0f061134418142140c503601009000ca41500c02440744c80912249600c0d0007420240403114034080721600708400c1c1c42260103460701440b0000307034090031480000c003660489000362a11a0381b000c0d0f17070140a1991030401000c244500b039050111510113003040050009003100b108031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 393718785 1250 393717535 393717553
    0x1c0302060604062d0e0c0a090605040e16030b100e04060f050622150c021302030f0103081803240f0403051213060e011515020319110a0b040510050702100b03 69
    0x502c40400c1d0a1b03420600c400e800042c0c4030180da800034107540c014442131800519151414401513011722000e00940240081e0601c401c620912070b41140c5d40305100100661083c0d5500400540021100303048140107030306042002520000e500b84400480e0350252a4a1078645c4040c01e00408030766011141c11003107040200400d1151401c10841854070300390729401c00040e140d004000c10b0041c215900d4201c0c40c010410490168424840941140d80c03000c030310b5448030030748103d1020b02250007109582520490301e1a500c1c282000c0440c0e4801e05043d002c1082d50b4032043d9284000440803100900405d20800c280107820060300c2c051640581c004007000104400c80d80c0b010140e8151606000311a9184c8501600310500405540003c00e00000300c0d8540300314418010b91a0302540d20442e00303248035000740e04112402800101a03000c0c1d072a081c0d42d1b4840a5140c2500b0848040e101550144584070002e0002c40484c402c00303000c0c4241b034008203440102564018042c082c51a400d44d003500580402c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 393720035 1250 393718785 393718799
    0x60d0b12060f010e01050616030c06021e03190513031b080c160b04150503041e051c020309011b03090e160e0405040206271c0302060604062d 62
    0x2542c010540d00801844552500000108103030040c0c020900c02c9404202c4040c8039181d44c00740d0040107034181445d001d0b541480c100324009005044040b081d111102203240f1450403010001e5110b2600b540c000514001940d00d80d80c00c42e481202c0c2c1520314601203070031002003400341001c42c50f500c80803540c1e168420003996132060150000190020b80e94007100c000e98040e201c0001e81d4010f40078030b82c1a90709003031070300c00341c84903c0c4440c0704401c084c03010001c0401c1c20711404c03042d42b611031900400c40c42402d420a141096543d5502c142d40304410b03c031703203001404441c4040308503401404141d40c3e2100e0402c0c281003024145d021b4040c210144800903200142c00c08028048e50302c2420841a4204503221514010303025898022149210700d140c03500300702c01a44da06041e50800500d00310381c19007080b118000440c842103040441680190541c0300c9454103414004c00a1545e03201e542598400e861f440188400c2d9801ca01501200c4074215600da0f040f596501010070300403590340000e4501ca552000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 393721285 1250 393720035 393720043
    0xf05060c190b0f071809150b0a0e13140402090601020c092511031207090306020c100e0307030e10120e060603010e0714040216020405130c0602010605060d0b12 70
    0x10048490102d6802001035031120190019484030b4941054003030705c440c2c1c03807442e200c590160280e140c603666034030b0603c0f802c0920340140c400070b00f416410311503440d043c1082c0904440c95000305144180c1031801ea1100300b480310f010724190400d501300240d2940d240e03039003040342c900002040107045104500c8014040d9030303500300003030152141d00c0842403d4058030104108500b840700f01d6000f84960359103400d41024000046803060380c0c0c80e908607040c68444d00c408880080079580080c1031940049258401c11001054502c2d140c410070305c040104d4055414000d84a00a140b070140103d80c00c161166903606044100908407241b40c900001c1e240c107020000c078105c1d00da0740400c005540c80799080001c81c0c24240710309910808110001d0440030b24000c2c14100b1201d6140345207015680106440f4010104442043c501c264014002d100d03500d414050012550a01c00040d907441d80b4941000880c1c3d070041c49a08150382c0e003c0e24640c9000794025045001c0d110380e842c01c41e08050180700115030480244 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 393722535 1250 393721285 393721333
    0x1203090b0f0a0f150e0411060406020303090c010914150d1a120c09070f020a140102070515160804080d06030f0515010b040e0a060b1b01150f05060c 65
    0x100340c0d695080145040084032010b40c02c880c0158540001e1409046905130b504c07089605000b04084180c1c2c40b441c1201e04d07800d0400c2d54a401090102e00800d02c5900071011310702c80c50b881c40807200301024141c011503003583c2904c07820000e1110000d0a500600340700f54545050108484410b1a044500c9081812507143e07040c070007003615401e6803000040c41e00c0f95150001200c0900100703051074814000494080016100c1401d01850b0482d1000560003800214225600000550f130f40900c5050102c1c080c1d0700098084449000c0c040c92411221061203c6038080d5080c020307460b00340000008103941e9810054001e0319170400134048080000920700030031010b50f00c1240c0742d0f02240c40d0743c83c200e41703041800441c60b00a075018000500c01140e01318259030464205100d030180c9a151252090f0003080f203900b004042c20380020311446403030504401c030054120a1002001311000801480d10445c056010703969485c8569482081036242400142c04285140001d40e00040c1c0d0080512113880008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 393723785 1250 393722535 393722551
    0x201140106050f220b0c1e0d080a0f06120b1b03010b070503040302060f040e090f0c0d060212181b100507140703060605090a051603020d060b0d0f0b1c1203090b 70
    0x2c040029420600400b000106400785100c0c1c00041003480984230581000340d44208060180028035100443d00101401380032007504204441e11a81c0d40b000080702c403401601c0444c0090003042d064007509403440a94030400f5080b03402e60b420544a1509544515800d507098030ac18407010000d60b0740c00000f04140030100031160ba90b41d180040040254800506501c516004000160070300710300451a207000c860120740d071118080c0703585030100007030281452403201c95400004000700d00c511070704200d5506040d08102c1e40840e404100c0f0300b01103110b4841d8607802041890844001e035000303002821950b8450343c2c118031071840000009140c04042d600c10780d060350b01c6034420000f605103600c01d1900150010014001417820800c421481a100c291040030543e00040c1e2084c003652662050003d4180020016a2441e101503060047c0c10303130281100c02c50785004086102460207481c00702600000155040c0c8200807521040c0d03d80f10101d106206040c0c44140340800520480d81c0705125640e5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 393725035 1250 393723785 393723787
    0x160b130c0b0a0201110408060106030c0908010903030b01081f05062808060f04020903060f0903190503060307120c03030815090c0703020610061706061e0304030201140106050f220b 79
    0x20b5600000e09460886400c1016000104070500c84600d010070400d041d0340c80b5050204014008090854141c4038981c0f1610007035181c40040c100f010380c59048590603410176039500c05691901040e040c444595526010400043c1510400580c01c1000107000c1e19581104401074110160004d1601c032400004464005080401000414640341118161403d0207580442c2800d11030004a56158409402e49910099100c001406050200301302d5610b42d4000b8900c0103040050704016003640c100395500c1e07120340540d13800403071ba900480c0f585101241d081290b070f200c0a403554a00b500d00e808050518a030440848070408055220f0348242805903250b0002640c1c1d5800500b002810403030090105186181040c0081041c0c5a008001c10301ca078600d20b00c2191261581400107441d0322514076110b006403c8144803a092002c040302035032085000e50000e0000703500101402001090034040ca0020034420311040c050120f08101804c1280c42d40340039030f0401c03504650f0f4441801030342c0d44440b0443c04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 393726285 1250 393725035 393725047
    0x90a0f11030a1a090a1a190f0b0a081b100e040c05030f37091a1008061e181c02010c0302131e0314010c080705160b130c0b 54
    0x607078100f015805050035001c0c02c900705460765644c4a0820396500c26961a840b080880c0300700008928414640011035020068003a049041101a1402d216524801e5540c103000191006d00400d4003564010034116209046204004110724103e0350150301c001c109000046c01c1c0c494645100e81c1c045d0030125102c03180c0b07034900000155030480b001003c8002e428001070f42840109a0701244100f020042d4490f0145811288a041c0003400c0781c4201600d0003201c0110505400c01882015002d1060780303d0030040d00d500c03034a2080c2e81e180c00f907030a140d60042e04590054900e952400b669000401c01c588441ea4a00c156840d5240c40029072a546441140c881500c880e26024801e03d440c04246080640c142401480c0c2000054140d00c80d600d020000442141e109040c1c40041ea0051a8081483c05003810f501983c54004c040011540b8003052100010660242c0100f0075105076004802129014030b10a40d6011005c410181984c500061182d0b10b0000103600351001d00c001e00340c99040b26440322 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 393727535 1250 393726285 393726323
    0x3061814012a0e01110313121704030305030a0b061b1005010501140d0c1103040f14090f1f080a080903010c0903050a03081306060603090201080f090a0f11030a 70
    0x50024440260007403088603840038058105608100f603580908208604007018244203080d0311418240ca6100586c0c100d020035140d200c00f000341d400e1030069400d000d683c1c20703901c0c4240580c030a602015010800500000b0b040a58640045254a0740600300606058951200c0580b01114101058281c0c02400c02400e08544503c2080d00400d0240303017a455031804030810310800c1c81403e0707800d08000c0d1a01c034040d901501400c060a83c0c4200a001c881d62070382e6440c2c54508500c0e95001c0c82c40380702c5012315124200e1528008060280300d840703084170702070b484050b5514030441e500d20540100c0302c4045000260301e8030500c05d980e002c5000d00f020f540e884500100301030841d040440c105040c001800d5003440420000204440056410b00300381d44d0702e48640c0c03001d036000781490a000740003509140011521503415000666094030030b8130340302080d40ba040644480c400040300c80019603803200e142040441c49015007040014002c0c82140310107904d94000c281001d82d5003200b5103201c0e41c1c2c04a041444 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 393728785 1250 393727535 393727571
    0x207050924060306150706060e040302072301050409020922021c05040b0c0c0f03160b070903120e01090f03060b03061e130219080105070f180306181401 67
    0x414007220b0091440c50114006041c1c1e940c0b420400340244008100c1c00b0030814158800f074060a640c401c035403054613041c603009640300c6490082c45016921550f519600ba91002166648200e050b1581e500706814040078034000e400c105c003410380c01038003441d40748201c1480c0403401c525440e81b1040035070355a04140d80e40110301ea4445610122a06d44000c0202040a81e11031542091100d061681d0b2080451101e9107040031070059420303070340070001d22940c09001402611035898030610030307203840740d40c4c44600743c603c600144006072400c0010030552914910070b0400c100c903d42e05041801411b5140d00d81900c0444070342c1c1007280c84561392004110185010000071f98058142124090100314880d601c03080c41001034405400c07204169048021581d0701041d240500c43c1e08140411000e6039880d81602030401036440c1ea001c20160031552110303521171800c1070240440e10204143c550724594601004104240c80e415008491b1031440e00007800300c80072074032524001400821203502044400482c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 393730035 1250 393728785 393728851
    0x7050406090e0c030a05062b0b070201050403020a02010809100204091a1e0906060418050a0c0903030c140102130303021510051003200c160501030507050d0c02070509 73
    0x201c2c801c0e0b0812075590440422030340e0040000c00081b580c1d884050200381601c2d00264403d50010a01200380b0540355500141d0a40ca80142c010313aa0036101d00400364221081030310050b0050b002072580344059406401290b4100400800301c03500b451000401004907040754200b440c1c0c2c10b86421414074003440459511201600440b5502c0842d10840c0c10405010b001c2d0000e140100280e1001a5136990b41800740c400070090310141001e4240d0072040b4034003c0c0310440380307909800c2c544100b2180ea40c0c4260910001c0c0c5c1e505807a51075101159465400090b844000380b21515034003000302a04c0d04100c02001c0740113522a03001400d40900213040f1441c500f070000e000403400289030340708000965807840540521203682c2400504420103500800d04040755048414680d500002c0c0c04500c524001988007001c041d0458282045417640c00440c1518010740702040002d100b400440c0315904140d0000907425103a0040b51001d640c1c4c1c00118041200484910200150304041d03503403018116404489 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 393731285 1250 393730035 393730049
    0x4090515150616020a030b04080702030d0306181805030703110c061606230c090103051302010206180a051218030109210c1b05011b0b041104090b0705040609 69
    0x24030900200c01082d0715010b010402190761041c1d0801c001507455100d030079405141c10020b0307107c05140c64248130b8040d621a8104038002d100341020510064880e229400c140c1300b0031000750039144c5010714110007034078540c1758220380e2080b8201c1307200015108000030301409219481d1445100605407040d41825440c1c1c680500456003000300600f030700109450604d00a43c0200c0000e0118260110310001550b040182100311180d181400600f45c0701001401c040c0109907418070040d03540400406c1070403116103000303001da03000002040d0030503040380458481c2c1045030100d855004490322494540213000180c040954400101c2c0d4495450104207aa05e0b86d105034000c0c810055160740341c04610304010007120300c0c0c01713007807640317900ea03a109210148890b0b4210440c245084500700300c1c2c807c05240c03071180c01d001c2604d0000070394042102411003003082d0b4004600b040250342c0c5454000c260106103614541c090750f5480070000064084410034010600343d45c855445500700803000c2c0c074034005034014107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 393732535 1250 393731285 393731311
    0xc03190e090a09030e0d140703030509100507022b060504030302090405010b0a08040305130b070501060e1b0703050711090411030709110301140105090d0503030709090903020c100e04090515 83
    0x3098021040c00c802c25030954824110101b50f040c0f800d000b46003860150308500401c2d0002040c103a00c50051b20781b8000484107158003050441003900d40d4030600d50000c3d001820702580390700c0e94030340611101d64048074000020000b000b03903880b20304684040313400700d000c40c0d40801d81c80c95608280c400c150140450000e10b0f0b203040350b040c00103480310000820040404c140000c1c1401d0001d41c5c2c11590004250780284141c4866403450081d01914803409039080c440c81e800006442c0b0040c1007902842d9a16071400b192400000340c0b0101c0e8603900c440710a83e848810340360265031984550070018440d0740184200d4001c9c41d0711204041c00c0480c00d6000c1058581000c10b10780c0195141401c481c11219603103030b011881e44480006907528020b040322180d000c03138003a15401c10300101000852203011590744042460f51160303080d00c1180c00102c006001a841400c4500300d40c240403008010742c0201e03041215030080000c00280a45491001c00c0301c00750048000d411804c5801c104103038104030640307200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 393733785 1250 393732535 393732551
    0xa0510050904081c0b0a030c181112060102030912060403020c100909090512070b0907050d030c020402070201090b030108010b030f1c0f1101050c210106140c03190e090a 74
    0x940c0038011130805003010318008410144c4114954054400c1180150a900d1100d5881c01c0c0071044104038418103c07a007103005162003000060b80300e19001c0d00100084642007818404849491000003400c15055120401450140d5507481c100d402e600d4103404004d012500d82490005d081807200388515014030250914407080903003216901d070903912003a10015007101e660a007180342542c140e03c4510400000200441070045040d07031144203140c054221103189507070788107015050801000141c000385070103610800520302600103000d004d005240c10082c0a894001d0003186134002e81c48500e6682d5110601c814a0038103018011404552401030156800c281c58117580e0307442c0344003a100401c02200222106035018108944a104c407050081007186048a8101c0d00c0364440b0a0300452002d14010710b2200a40c02c01c2c40c03d060316215924003030102400310f04000039411111100d00b640c001800b086001c0d802e424080e0304185c1690780d9258030b499550003882400385003d071107000120b08020003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 393735035 1250 393733785 393733793
    0x1a0301201801020a0204051509010b030730060807140d0203060105040c020f0a120905090411010302030c040509040515091b0d0f051509070914040f080708030a0510050904 75
    0x3680e8801d00c0c00180d114900684400403828200d2041001758030030300e800c0600041ca83c2c2d070b80e642d0303105c108213840d0b0005a98885441c5d014a0000715000000580034049000160350f941401c01d80c007022076094901424803001084003510070300c0d041104a03501c101c1041000b43c4090540c4c1a180300b06507031030481c007051600840d803106014002c0a018540311141001400c1c420007146940b031001c070090f5400803255140c604410751240840d40d0002e0300c80308021274185403000119000d281c1c03000100014944250044d40a900020104d45140c00d082c48001074644444440c544940e00c21009002c200d5041c003020700d03040d613001d002c4644c030b98040c032070744510900d00c854018201a0101c4540c400c038441440c01480030206002c0041207030068500342d0b254810350380130781402203500d1020b9440603a00d40c03000008507070398103040c14480800c50b40860042150181c2041016016212280c0f5003035003a100c54859034020340f81022081d549008000c0d92103c65003120b005000c003100e0301c0c243d40c10715881d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 393736285 1250 393735035 393735037
    0x807140a0c0605070c0f060606080708093d05180a02061e040b0703050a08090c0109030b0c070b09030417010501060504050609040914030706050a1b051b011a030120 72
    0x501e003076901e0020484c0036018945601d034103a800203a0b00345a44061411b10054041c80c41140081440c110206070010300aa481c80d21a0380410300030400c40c1e00011714032040d5039115480a02070342c41c80050502c03140c02c100070200d070008541d0002c5401c4c1005051415a080350890351142900100211001651403070b0865114401109448102d01c1d60800d00031100d00c81c0703920180c402c0703500040c61010150040c0c09480d4450941d00d8030402035441511446c0c64948000c0000d0000d00405828400103106407206d0b5003240d079445510703040c001c081e40d4501d006182560300c05a82d900c085410010050204604154030304c0c1c007002848030354900300c2d000e040d83c040d03130040354807901c00440c4a40c80e03902d0355446046129000a01900350190703680d4034a44a600c4280705803030150030180081c4058503640580d100241c00005520951f0490a100726000c1d0018000201302103034038081c2d480302440900444541040e020107000030301022004142c21288061020201c540c04800c500f064104900 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 393737535 1250 393736285 393736307
    0xc0b0d060815040305043605010810090b0105010f030902060304030908121201060c0602210601030b031b040203181c120c09090e070b040b031617340807140a 69
    0x2200c0b103400d030030007c0d021210304a8170300502ca00440c941c94a49203010a20b4010a040743d6078902035070345142c13840781030308156051000040c0c150090880100310700d51040186400360b041601d4001131420080d40003400f2907005640039400507800c03800a0200c200d00313101500d1800c2c5007902c09072800d042020020030642c1d0522466062003001d00c41c0c042407051a404031142c06003804503058244014002e4880c12150940e411030000b03250100c0c3c959507040004103440040341d11004400d11440560400000c1d500061502c5140794440e266807004083c00c005a04010301e4140c280c402011003c1802068020307401c0d0100c41040c20281070724280c607003102c604000c0d11010100855800401e5660515080099202c3c0055140000e000a03c03541010301544c09881600c2100c50342d191000e008550244442440c003503040b114102040d91302a85040315a280e8202507171440c0501c0c01c0c480a840e5031329685000c2000b15007840200a10640c2c091208400584c002c0d0082d400c0000300d13100180111188 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 393738785 1250 393737535 393737549
    0x608100504091502131809020306041101030b060706090308100e04020d060e0f0303040510060509011806050405191413061a0a0f0f0515090d0c0b0d06081504030504 72
    0x1d0402c04040c030804910381035501c819080103650703800100741182841040344c07040c02d800304034018110480c01e100707000e01d0501c10740040050140d80c5071601e0b40a004001c91242074141551a000d00b01c603030325a00082d01c61705004030b4001236400f07850b0802038201c040013025400c103541d180340c040c410302c80c14001240d00320b501991900032000c500e16141c0000d041d0b004041c402441000c20400412034004011441180300380e050310a0140c0c90310301a41650b64a0151661040c030020041c080800d5000000d8a105c04611020495658540114045034000c0d2580d2401200108601c15907070064018081c603881307201038001040c5084030000304207c00c3c1150007000d0710f0311070703481c1c030842d03c1c0d603036044605140000d0020f811903507078039850540f0703400c20312886840f00340c0d01c080080c0c5407030400c1c002e5001e00e150b90b81a0385092140000c001c4401030030340701110103205021001c074441c000d600150200031900c12000403140e092400d018507085010106100350756900003004006588041580c04862603 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 393740035 1250 393738785 393738791
    0x304020a0e040f052a0901150c030e1903060e0a05030313110405010806090d02120a35092b0e0a120b180c0f0609030a150501050a0608100504 62
    0x2180b9101803c401c0c40d2401900501c034002e9888200540b01810403204500e000800c4544003861060004e10682445408181000114410309550164403581c4040c0e11a250200b0007501d030350005044448c150740507000150034000c0078001c000c06440340044e21140940140307821449070303403020f41e28480186000d1b21207100512100420004d45455102e0348801001030000d5a1110740d07113991020100c494410f903106441c41c03907242c1c60004c00c98118000d00280140e242091850041d03e1451404001810a00500119070f0100c0300000761410390401e195020662814408117052402c000c0e591030b0300307060281040c4040c850071500c410b0480d0900f941044802d180703845000aa0441d4550b01c802c85030f061900e0910100300c00403100510034100e210b204024110180652950382544624440c3c020740082e8181c182e501d0108003810715010f00604640c801c801c190342d80c40391840280c0a0041c82c5803658018407044c0742024504010301040d190000f0709145c507085c0707074070741c040b03030713101c1c084c00746603 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 393741285 1250 393740035 393740041
    0x209101202091c05191e150c081005030312060d0501060806041101020d0813030c081306020f070602010b060d020306030703120806040c05190e0f0a0e0403090b0304020a0e 75
    0x215030140e641c249001805401000c49600405100e4a0b08500840b8207004140324039502d00041450400b1040e00b02d803684400903080c081b4801c001107010410f84031048400448900c2c40b40c240a0382c0c0040455039291072090a01030445000c090f2140c10041c440c0c0c005204429035002c03c03140312a403000b41214100c2c4000014180940141001e4100120303d0156a08000a11040050040c0304080a03400c880241d207592404139100c80c420f036240e0040401948025011a2040c1d003d0000c660013509000d103014455214090151000da100601580010010b8080000d003809004014056400244103195a000c0026254424083c1d6244182c1e40031004c600d4648042210382c1c00366600203044000c2520b100000780c92a4822a003052140e42800300c0d08090510401c160f81e460b14030784140c401c00d0091071606545d800042032080c0d4011000c9202d0903250341d00c120340100100120540030100307080ca1b00b0300505541c019048911941c000300103020060329214501e00440340b0b11104104113813 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 393742535 1250 393741285 393741317
    0x1a090c0910050301140604060e04090303240503060a020414221103060306090705060927040602190c0c0b0a05120906061e030a140709060e0703050703020910 69
    0x4021a8800340e000000d18845100ca039402c42c00640c143c41c5449040169048403408200e620301c101c0c011000042c20840104055080a070011651580f0a0402040c21080610000c44907003180411032414400d0714400c101c030382000d00c64103401c1a402c160035443c1030300b000d0020304400c0c03a0352084c1d40524411441c0001d5820f0603102c41c0312141340c24070107000c80b040003210b50302d8540080e5600f9101e4020348004c20840540012107208941010300400e0910700504204000c0c041d502031a40c492100105d941c2c0040074842e03884a100d103108400c01610340e200c011986c51400804d1682e1810300c9041208a400b0808985000c400c94070a40e01e1150342703690300c1074121602d015001e04010003000020a101e9480c0b030105050744031b12803d80d001c514502c4c0c103504d146910300607044466019041000c0f0200403c1c00d030020205d4030341c8040b00302d651082e0b070740d80306400f110015072085600b080c1c407005202206a040c05540d40002c0b8a04c0e0650402c007400340040c00c00c01c100c1d4080000d1040d4041040821 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 393743785 1250 393742535 393742537
    0x40f05060901170c04060e1c150902030304031208010806040c03080315120f0105070903210c050a0302030901140301030201171515131a1b0109080a020a0507091a090c 73
    0x100c0c3c0a1110f1114100081d0081a030b4015005090120301041c41340010b508107000601b590040a0082c2042c5140d942ca83d110800c032603900d020030568551003004050f0f01c04000078002036105402c1c1000500031144000e14268068011400940200040c88003149210300d0403401d803500000b4140d92500c4100d51200400041c444aa4100c0c00320f452100341c02b607000c143d0740c4071541e24200a01c80c039a666041200e0952140c00300500032a01c0040186500d00e1031304528620320b481d130400b0640802151103a901c2c1c00c01008007240180c0c400540c0342d50659000240c40d500b800880d000174103550440d40040d18241912441c4200c101e50b54000800174440045040c8003014041d10b00000c8400e040c00300d0601c0c1d404900003180c082d4180000094400032903400d0444084115110f43c2481e400c010004a00d0003403c09204a541d24bc4802c82c000c80c1c440c0b00207285907481c54000b8845062946000c40c18225183d11035980c0701d1802c4182c2460350100500500303c200102e4502030195039011881d145 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 393745035 1250 393743785 393743807
    0x2010b0405040f120206071d0a05031f0c08250201090b0717090304030507050910180f0e010c12090c150e24070b0c3903040f05060901 59
    0x200604100c24402030040c20528040d07540d014a060000300081340c0000c1c1c1e66200151f56840010790650802011f5180d0000040002c2c0e0000340f403c003010f5642e400080c0f400704407427000d054083e0810031030740420540703204514590311641070170442450f0038813907003500c10780e0480244203008101c0d02a094140c400e41c040f118803580700741e0941e0581015080104130358410b4164032283d50110021a42c0100000140d90403a9030100080c180c3c5030030101400740324840075148102c5a068490040385001e40b42c040f00300440b800010004403000800181d0068940810805100b030b4508035049101d01e0340100b90800d41141305a01160010f0b02e41303018805000d06502007170091140340201001242d11000c0034081d148101c41c07441c00f9014440489901e14403000f245002ca1200700160000140042941030740b0104c1005014100b050485500c03142d41000da894000c1082d146e0541101e5200c518452080704103104000c500b481d0512145000c000d505000d0644245000300d8088601d1303108000d4008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 393746285 1250 393745035 393745039
    0xb151e01020a060e0102120a020306030c041a010c2f090703181103101b090b0a050403030e01262208040e061507260309031c0f1503110d05030f0a02010b 67
    0x2107494031700e407208c0094206440071403107802500741c0620f00e80b401e0300400384900180c1810701381c040708036001551180255003044034503031108000075981c0c00c1c8000101c80a441c2c4496846480c070b070000c0401c59104402400765040c1440c010074940440c00d243c18445e40340364003c0d6240701c1d04011030002031070f000c1004c0701a450981061704900310400750000d40b0001c1c2c400c0f911034044282d01c40a55540030700038164040001202440100042441480c0f0740c0444101810320000ba01242180500e004c10382003c0c02c042c40030203a0910406802900010403203180a5103c600340c4101680c40303e89a21807481812024440480817517200d98070303060489440b2010200060765401d09181400d003c580d442018010741052208044260124500b140e00c1a00e0f514042e41c070b044882d140720b40215110b44500701c00d1542d01c00700000280c4491090914084150400740d0b0350134654540900c17114a841c90031401444010580c6002640000a4880400460075038681380c1044020880c014005201625 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 393747535 1250 393746285 393746317
    0xa0b012916021306120204110702031023040b04300e0402130e04110409020f0123040609050a0f0303020312130b071706030a02100e06070b151e01020a060e0102 70
    0x5101011021711005061003914140010701760740340108124010581c0c060f405402038040044941c200f5401004008a142e175003442d440c02c000400111803000b2101241c0c0350040c0d20a0100b4051a002d040050700c1d036102085003081c082204c00030340b210880110320248441c0c182255060b82d6241c040d2810079085c19600400143d5424003d401500255800e44480e1f8801c41d01212605140c01140440c0c1d402901c03040c4100c1240c0011511034204c24110011015040b02031500d070030300e0f03c3c002d100401e01a42c608031468280001c02c1708512407030340320b2070540070101d0f02000025008015202d12843e0b140e0903810f04d40d501c540490101c40d101d200201a0410442040030b496009000028221200c0010a4966441000381a85c0c1c81d000c5901a42c800d4441418412184c41448600400c900c094403590400c2c41c00d42d100e902c001020740700b100700c038440d200c41c180c100d04101601e4102d15014001d8612282a1540041d4070303070b203041001030480c07500da4002c0c41d0b54020940440d0002030310402c40d9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 393748785 1250 393747535 393747539
    0x509060706061a130e07080402121908040918020306270d02032a06011505090603041a070c150902010504031e03110705010912060e0a0b012916021306 66
    0x40361a590290761000c101c05000d92011480c0d204045c09644518a0342e181c410503034a50f07400700807001801940300c5240f4800c242a02c0d88048491000310400d030f100f01d820395215420862400c082e100c0308841c0100b1a01c0c0742d449c681c096a4001540740e081722503544030f4004003c0b6000f00c084880148042c080d454440d684000701055800801400c60441c071042010800031580317102003d0010514401000c0d030311071401481000001c1200400c00006410411f25003001000442c1c55600115820380d401c03040c242c10075400010b40b201843d4070003070616010b410030507160b542e0300030b0040e400d03451100540d40d100075000b1640100708907006941c01000211010800c80e101c1069130304403400c00c90000c5d00780701c940d640c0030038001540002e035070b0142c590003001d03414079018602c1d094081606482c3e00791501905c1300c51001c10b018040501d40104204115581042c0c000790030315040447c0e030421048801c0b00034040049030070035a02c03101343c100148c1004a62900016401d43c540300d41610641e8580500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 393750035 1250 393748785 393748829
    0x1c050307020601051e01120f0f1a1507110604050402030103051006061b0b0a06030c060921020a0510120f0f060e0603070506030c0d11030402031b01050906070606 71
    0x24500c6201254200c8100b6a220401c4c008101481c9010002d50720605810b1a5150701079842180541008803000030200e80c084c286000f0381c0d5400380c078103551a135680c0303c4000c100110300308108903800685212040741841c0c09903070203c0c8507180c40a00340c00740c0540068100c0d680c01040320000e0100a0007907480b56102d05210751510500303148060110300e04040002e15a000d0045900303c4260300e030001104442c0c5458000c40300c01c0091600c400160344560200001d40c503024071101608079036a62010075400c0c88a03528481200e01082182941180000300069031002c1c882c0c0d0903150291151103a01106000513200002045200d501150501c0c208400751032041e03000c0002c01d0861401408800e640d29100480300101342c0d54560140c11035001401107081c0b210003942c000807804010f07850110500201c0d41140c2d180381070503000050000902c000d62404110a4000c030980302ca04420741044a00080c1c10380c49900492405620f0200e400801e0001a41c0848000c0c010b0082d040c80e22560088 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 393751285 1250 393750035 393750037
    0xf01030b0a0b06031e1b0f092205060306010608040c03140309040509010b1804120e03120f1309020a21022217070b070f080c24060f030a06050402031c05 67
    0x940b9540d0360039143c0004406d2400105109414210f03c603415140001030f001c0354905a00400440f030b0040322002e49136150403a41d40740182001c181c1030300040c69091070410182400d2069010100b08a640c078148008100d0388811101100c2c1e012026020303040242580170700314001d906090ba44946000100f03c000344064001c020801e030102d40c50f001101625901408046055401070480080c0400800000c1e005240040300030b071004003160090031050303d0584c12503008940c43c111300c44001c18248501d401211788003000c1c00714090706605040604000030494006007213140c1c190981684150b41020f642d6040340c8140c0380c4c480c5410b100040c50340c442c0212600030310a41c04102c4c00480c500712410030205446e070560b1620b1003c0d919121a6464507682200001015951400100000c2d80400010002183d80f2040c1101200350f006030107402240300d07400102070500841480c0c1031404540d901003102a06290b01c2800020680c07250700100745081d000302e000b10b442c1482c03030f00c1d500e132402c0d0860 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 393752535 1250 393751285 393751321
    0x2122a060402010e0102030c0303061504030c0b090405060d0b0f0402130908040311040216031112030112060e030a020712170f0d20030703021b19030210050f01030b0a0b0603 76
    0x80c131000c14808101c801240c2d80d2044041c516201d0b002413011420324642003040e0300580e02c58440907401d06440c2d40342c442006226070300400c507140f400a903036140d90400d0300030540d11a4040324460032000650316541c40005001300481382c0c0303841c468005000c564a905505012044030242044405003e1509407511b40c000d000981d50700005040e510240d25260003203980710212040c4180e50448555020b1380e03080003410b020fa0381d030301519600380e14043c031b1100554000d002d030f6061001941410304007001200e54020403100720380c0082044050a079000070301c02d01142c2c52181d0304d0380d242d0900d013840203103500c0c8004455228400080d841c0c40c45800c2c0d1000e4501340a0300a42003003418a001c401c2410781c1580300b00c10280303407810f05c005641107020380d015110070f200200b5401030400e01d0303903041c60a00d0b007103204543d005e0500e0f00c200e40c02d0550400c41c41c4140000c0003410000c0d400c00ba0941c400c10241480700602e0440c100300050054070171500084d8000320003808054030b03410101900c4800340100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 393753785 1250 393752535 393752537
    0x7030c181401080c0f120417030a1406100228060606020604021e0d0312090f0c08010c051303060209010207270f0507080f070207330503040302122a06040201 69
    0x25001c2040030240c3c00c1250b1951105e540210f282c205c88800c1500e04210082003515a00303040c0b039840a901c1c003203800540c1315075080715000075030107080b424030350800102400b218040c10441e007060000a40000d0520040701c01111001c058070150300401c210161800c8005000f1414142c0004405800240d894007583c401c0381c421089102e80c514005e100322108096030b511421515136800031030300901a641d1070014445020400700703490b4070740f000d985c90021400c0311100084003003048045401e201d841c080c00550314105103810b40c828000c8115400c1ca01010f40070650004078001643c3c001c019000c001d1a0076943d0a48601c07031800810b0a00a8291810746100d0031b0410401c0e2a00851182c1c81c46100b02d600d903005030f912541c9440c6602c07400246004150f00c00d8210104003d41c184c0c45503030301c0002a14032000384164440d1a04a141484600e01c0e091040500901c00003d4000c0b41716458400c0d1400c0e043c0e1660150026001021002019140d40b01c4200f1410400c140c404506113106e40d0007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 393755035 1250 393753785 393753797
    0x1d040608010c020c180406090602160309080f01090507141914010201060f1d0603240a06080c03060c1e030403050a0215060607080906071a010807051807030c181401 72
    0x84e020f0201d0071a4003003007a040d0182201c0000c0004450b42d1003c40c80358001c840050420400076440d40040c1c2031000d003a00800c4020004000400c07003007110100304042c0100a11009001d40d8801e5690f0209009050980c003014110030155104c1402c185c5801040c8608903258980d2443c40c0c0e100740e0000c0c82e4440c015400c2c0280410885003401480b41201c0b502540f455004800c03038904c640124000d0802c65040c001c400030280c00e15840036030303280041c0f03419103400684e080c5458680111055a808081c054014025007501542e021590503800104010030fa070b41c0e088000da003007101d07444240c01200c07020404020300c424142e000010341100120740e021104d20342002091000100c400303c1c0c040d50b0000040000c40006105040903145020003e8a11424080d280c4c0d5034245128004603102d80c8010860010007030540104a003500030403041c2c54999203c0c1c00841e458046d039200406c00c500380350300c880448411320b22406c4c203e11016000002101d40d0364960351038000b171141295415000900b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 393756285 1250 393755035 393755053
    0x5210123012903060a270e06040201021e0c04180201030e07081f020c2e05060609010507030e130e011a060a0c0503070b04050102030a050a02070b01061d040608010c02 73
    0xc10840d40d9911054100110300401e07664440e00b5256a0000305031340c1c1c02280d14040007484128600400d50f00301d034001480268004207000500403548003048501d4140c2c0004d0912016036004581007000401c800342c0d03060300e41a00754400d4680420040b000360082d180000340328400500f025203840740b0381300f40e8051064000d8400e0603a0759010030700071507115030400101c0200d040f034501c0e40f10300d145400003009400e001100010314104802844101da14030007a07850b43c5440149103081096010074480c00b0080c905002c0c01203a0680243c40310036040c00300010320700c01418091007100c10710441c000c0942c0700462000c042440a065003003c0002a50b090543c80e02d284400c00b15114072101001e4034160600103001c0007290003c114103810349107400208842408280504015403141d07004400240c1d4a0400c03044d14421200010101c280c41c0344140203420000c1d0709009168111041851f00201c0c4131200da0040070381c1410140c09580c0145420400246608107400404038581d0b01c0e02918841f003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 393757535 1250 393756285 393756299
    0x40f0303031a040c0906050a020a151a0312070b0c07080a020a0c1517100e0a020711090f0a0902010e0301091a06010905010c120306091419020f040521012301 69
    0x444803260391011540c89a4240000c0784610702401b101c48d428412501411404d44807050703008440684841c1968545051059008801459490211040d801022001c03001c101540845c043e6401c010952401300c4080b40b48a2042401d80f4003507074101e04059079441c038940000e90717500b0580f0000c80354002c04a6000889d55102c64036005051401d031a00d4262410309100080d4504008210070704c2d0a56215001c503611f0755415903544101d1049400507500c07403041c188029010f91220314680b00c2c0944004020100c20659102e0742c001c000150302050406c807030720060307620ba100f02544603003640ca040d080700d00380004112060806903c0790b6400e0306035140c5a00444452025002c0c1c2070118480019002c0001c80306d81e04a8042c0c40240b030000b500301e480e0b0101c0020745000030404840ea0f0404414094071000c0da403e010b070510b6140c0c0d400c51510302e400e01d121850b030103688070303040c03013504581904003a401060340c48003655840c0c20020404050100d4515820b2640414410f0b980990000041505 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 393758785 1250 393757535 393757541
    0x60a1a120f0115031806050403020a1502041214010e0607180e040f0312090206070303050f0907051e03120c0604210806040e10050f06010e0a0e041106040f0303031a04 73
    0x1c0d85901c140020f001240c81801e6010f070500000200751400000030141c0410714a21416018900c250302900c0d02030800d05207260b0110340c04040050441c0704000402c0411612008040e030254800740f00101001d9004030b4500402091a20303241d24024070341001240c0d0340c000500d80c503500c0b0201c00510680c7d21110540c40b682c80c120b03001001c0c4820b41d103850f000f0030f0040d40368501d4900b03410300108088001d41d01080040c0c000031000c80c0403986540510040613603140000754428040710050000c0340c5080c00283e170295040c100f6100d42003075100e25800648041c44010f00426004ad4000d40d55006941040e965201c119016030303e14030b58080400042c0d443d4003031300b200c51220303550b40e6509072544002c00c8002e10140b05010705a2248403070200300107800d03018861280c11003103800c09840c40c1060002d0a603408402d51144685d545c160140300c014040d601a642141e00401ea0150700d00412022401030320654102c4034181c006068000105941a00605040401102440c500341d03407103002c0c8801d0f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 393760035 1250 393758785 393758789
    0x120f07020106060c0503030403180305071e0e0609190f0203100602071a030a020f0705060702060420130c0203070213050105011d100e0118080a05060106091805060a1a120f01 76
    0x2c80c6c10400100c1c010900c14101092180056a015071200b0b5680d90394a1a00e0913541c072010680c1540389221102800c0300040c080100324103480e0501602d8105c1c0001c0000c0001006c1800c40107180d03020400b4110664440352000d4500c0104565074240030b16000b401b4041d038460780c0018400c0749000f051aa00c2c48652a072000c4d030300c0daa61800c5840f45285074019400c45064400030300400e00001e03022601c200079180c0541101e4010300003600301401c144007507c582e402000304182c01d82c03912024039200c4150341840c035414042c00160400c22107078202c0c00c500c65040043c0d413161018900d44400c06075507000324100c400c04d0f00d41803040210f80035400b01803080b9542c07160744203c1c2c1d1440300c490b039401a0b480d880445414500300e82c00017042e00350300c41610b41c4d50f085011507030f2007202181c081003010015a800b500c8075082007512145085a1024043e8840c000d0541d415102c1001c80e40584508045001814489803503400c036031802410007881c0d4010b00380720701c2d100e42000302085990300d00e0740c40c0c1d0381 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 393761285 1250 393760035 393760043
    0x705090106030f02090a0b120123010c1a160e0a140f0d060221010506090904120c060606051801090609150e0409051f0501230303120f07020106060c 65
    0x14960386091819001802001d0001d00c20075001c014640701a41c0d580c180304043c0ca2080080c58503500c17252004150340d407058110021080d403046042c40030007080d11072030340a001d003480d04001c02c000610785a00d4102c80810f80d0032081c000c10092240e1400411510000c2d82455a1084480300f07a5208000203500c40c1d1068440603c010a492001400d002c1c049044480001c1d01c584a822000c1d504d26040742d00003005c800d2141020307050742e101800e01c24205d60040030129203140c104425800002e038a03000c0544001c0c0002c01d000150240039014030907220031260000c0701003005038dd85003000b80a550040055508440342404024515800744c0340321b00035100c0302d50315849120300340300340c0341881d40c4042d919030148800200c00110980d194022905114411401340140108510424a040c04441d0603c2e44180c1040c00600c4004003e101d03130120f16204c9540340042d0359102011038214402d51114089181140040040048003819800e00404d09070f4002c110040d9110401c440102114400138 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 393762535 1250 393761285 393761299
    0x20606010c02210a0804051e090f130506070e090106110604060b0a05130605010f300902040f0606020609010c020c060d110c07030b2508090c030d02060108010e0705 72
    0x80150400040c901c2c83e6960300c04580c0141d121062840d85400002c03c03084600301e000043c2400941000e11603418600720011111100301d04010002d00001c030010001940c200c07004d80001c003031088213010364000540103402c0c0c0f01c00f8140020020001c003640100e01c1c0c0104049400021807621070f00601e18040c030f4810252002c0d80782c0c0d0303072450003802400440b241d00c01694140032406613551342082940c0808450005407003890540050519031658001c0c00a005011510035041e0f801c4004502d003070f500c04030705940380d0441244003000400d401d042c0070f5007207403610820381e08540540c0c3c44181035469903000c80d80a5501c04450900340d032550000100160840407a413040c6043c040054070b40c82035483c0f00494500e10281989280d500200075828541e4480313a400c05c14000a070300955000050002d080420482600b035409155003480140000c1004410014101c0301c0180300010003001d0080036694003428166009540716003c2c00341403160b500e4001c034240ca140707000486100301d600c040c0c220 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 393763785 1250 393762535 393762557
    0x50d0206031503070b0d0203160804080f25050606030f032706040905040b100b040308030708070e1c0302010509010c140319022a0706120e0102090a08010c080702060601 74
    0x36004188401000c0f50580300d5a0b0000c905405a2030181109014400e00140c0341c0c0360001c200c00c0d04010301da101d182801105014000031600c180102e4841e003020b803561a94aa4581c4010500c03d144184212494007030b944500081180124410703000b84412400c0300d180b594a09a410703128412103e10505038405840600e41501d007510003c580307980000c008a0400313030789082ca601135a40840701120400406410401c6020304100c210f03001e44811101c450a05080d9038403800544400f40070359090281b0540054a42c92141a51002c85080034000520080d40c9991080c041c1440d0042100903500f89000500c008005200b202c0003d01c40346d03540e214840c0e4054032150164400383c400d141e5210181c1c81d0f8607222800340010203440c40ca51401d040c0e000035a03a101d200c0148200d482a4007034100440800c44103034030808011031b5038040200010b0003440b0080c11402440340225094100c84c4900d0006503103841940a09c500300f1180d25200031541d21440c040303846420444603240420614808 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 393765035 1250 393763785 393763801
    0x4230609060a360203010602150f0703020904090501090c08010c110a030c0201053f10090e010b0411030106090518281515030e07030602090303040e071107050d020603 73
    0x244044101841451aa02c2d24030035008444060703d030f00c000302d00e990004010400c0c541c1c100710801d003841e21000c0032905c0d8280045803000344071024100008258003c0342c0030394541d075550301c008040341d4004001c0025020340d280c070303c025004070312030b00840307510b450a241c6c521402100c80900c10b1030084050a4040c1041d0b2342902c8a48041c9420b0341000020300c2440700400820801d104e455255075030003110b1382d07181142c501d10340068281e102200007490301401200083d103c41107080d502c250401160303050b40014400e004108600030310b5442410070902c8a82e1001d460f000310f0503951b0f150365200c0d81c40d40700d00602c10040c41642a07024010032040004050103c0b18a018881102c90510700140b04440c22110066800140002e2000d4a12030810404d010b400c0b2a03407662500745007000d00c00500030985150700d0f500c25101c05401580c0001d0345d2a030569061003110082e01040c1c1c007010f81401c00c004000e00c0100b00c0b0350250128498036002003540e2420042c03c0452a500900003460350340c41d115 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 393766285 1250 393765035 393765059
    0xb010507051e010204050604090501140423090f12090a05151c020403061a0f09010614090307030812100801050c220305030d0b030615010e0108090c04230609060a 71
    0xd40c0b42d5824003000c40c00e60b64101c0100020901c500e004505941450585801c0380304502421b445580303044140001c00383c0760800c65004648002000703c0c40d42c3c40e886030340c1c10020301440701002070080500c40d00e81c02900070040d1080030819100300c5d03402c81d102c4091241d451000e0803402c0c2110710030b0180e0101c0c0305c020000104550000c5c4400b506060740c0e903860724282c4200c00d1034000c01c42c50300d50b07561201d810924040c03d034000781250003603401d52400001902c0c506e12a10b1203d2080e030001046103007030300c04202e40c100071503100700e1082d650b0410394000204c0f1202503401c50580900c24a0000341c061050003002c1c001d165031f1207158a84503400d4034070783c0c4009203000c0e04c8030302454030782000000c124144040c004282801398085003c400c03410415040030740050a10b40001541c24032803000740da004500884080007070a14102c151a00c050b180c1c501581016542d0f4000d003030110f03440044020011040203c84854005c8030716440c0c2c0810000c01c1c1d00100c03403461700030010080c10400c0401c220 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 393767535 1250 393766285 393766333
    0x50d24020403060207030509031b13090314030414060a020f03010b03060d05070311010e0a0b0708090616030c030f02060603101e021605070608013b1303030b01050705 73
    0x5040107141a075030f035036a5000d9801000c03059000c0340c0040b0303071000d0508041c0f2440c005c18081e501c40310f4028580c440016241604030400748020760766504483c0030140a00801d0303074403800e881c509684038900fa14103000c03489024100f210f0030f40201004540005294000c0d6031042d1404c800c25411a800c007481e0303900c260801041540e0098000d4102c0c0701150f018020b920195001c0e00d010a4841d00c0b440000d400c0c120001d00305406108401d5081154450200a54400980c0f24a00c81e42c0c074104030000450501031140d0310221800c0c000c4030740c000c05030401001540e00f84a9281e42c07455400701030040c3e883d10411504180c141d0084c0c80c0b1280002f0032035004204041d0110082d8611450412401e0100d0b0050030050045a280c08000c0040c07000400c41350307004040740c1c80c1c2110190b0401100510a038a20781c580c2140341030748103103030301503820205059074107241f289071103203046c80e07c918000805012104260003080c5000c605808551007102148c04103034102000340700340b2640020741c4040c00c0600b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 393768785 1250 393767535 393767603
    0x30f0206070f181502060108010c0f0804020d0f050d080402190509041202121803010e03190c050a020904060b0112060b12040507050a06020f060c1305100201110f070c050d 75
    0x103440f01040d1588141015010b098640d070040c81150305003100282110600280f10083c000c003485200c1d861507001c4c4845501a0341514441030a041c5d514104140e2480301000403c18012003072070348500740d80001d079248224000c4400070740742e4900703070b130a0804440c581c0103268001d9000b40020b0003141c0001c403414401d04580c4125003450300554918401600044000a152202100f060b070281c6800d000741000288048042d40c50003050001d40e800c80201004400280304041c8041428040705009013150b00b40c002d46801118546072800c2c0b001450701c882e1450201c0c2da0150280e00d5001c940c80303484280c0e02003010240c908220b030b4015080e4180004e00407111807040da140841c00d6181c800f6564001c000c940c0042c20b620030041a0f0a040c0381c401003070445c088a00380170f950304031590172030110119070003555011a030000c5098101d0242815801e42c960b4035500240e008104459036004000c0030b40205070911800d42c0313034010080710044458003c1e081d003280399041001c003991110103ca004002e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 393770035 1250 393768785 393768827
    0x10050f041e052a0a152102281701080c0f031905060906070503090319022a03120f03040803060109170105010e010605130b030a021c09030f0206070f 65
    0x8000c10a02c10f4100341052202a070f182e80c1d484103540d08040c20414042d0078444400c4841900a400c010b16400c41541c08550500d82c60040080001c0e180d81120218020a41904400040904007008021814064800040710aa040c5580c2c0c039103040014140d42c07040001d41076000c407040400a043c28820003159141c0603203401c0e41e2020701d00c50303044402e49101d007000d411645400d086481c1464401400241840800c02c10040500404001c4880f0090216404503400081c0e1904918050410095101d044540708001c21910901007039a6a80c407001c408a503920041030200c1c0c540c0d0702410441340400c05d0107101103000500a000616400b0006141c03100c4030584d40d203840030100405442c2c0392401e035507400062000920340400700e400f4000c2c1e4241f80d45020350005203485850044d1050580e4800f001c40422000b2060750101d503000154105040c40d001c5910355960001c104a4000700c0c08520100c2882d00c0250012503210b101e2001605d80001e5041e0000040e18a0214a14400015a5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 393771285 1250 393770035 393770053
    0x120b0601210216052512140105072a0b010308030c0f04030602120106170402011d1518010305130b0705070b04050318031c030e03130810050f041e05 65
    0xc8035101038140c0120080141c0c001c07082d142005400c01e544001c40c440083c4141125075000403e003440f203800c51b900440c0c4d4886000d00c60800b00f425802031030381c00860794240018000388a0344660b0958069081300c00d1007895100840c245002d0b5072000750001e040d550310b000108081011100a1688101c0b2070f18843d103045080c103449040d0394000c1d041180c4040e800700d060072504500c803090390b015201900704180410081410700c0c0034014000c000904116544030ba10701c009200903040405c4140140504100c0142c030950555280c1120f940c5c46c0c04014091f083d541998480e0103245d00490903281507403401242501da214180c40e00400c1c0740180842000014001108a0b48461043c1d0180c0043d5448000040c0300e42282c1e004100034034402d92180d0802c100f01d51283c07006000c040b0490400180503031100d01c855043d40103001000304000c0c200c040000700340348007180022648078039140c00c00c0940d030303880c4001803019010b0714090800120420028450544031013510b0310903000e803046845400b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 393772535 1250 393771285 393771347
    0x9060c1905160606030f060506041e0c020106090c11010e06070e1314010b0301030b0f07080a09020a0312020717030301030c06030903020312090706020c060306100c23030a09120b0601 80
    0x7404c2ea4821100d10310b000081c103061020b107100c1c0701e4000904441c1486810900080119070308140c40d20741c04502e40c4e40d5a42c9000360700035403000c002040c4000d4240b09140e03442c2000b60000c0b00c03018101003107500382903a40c90041030101d82540304800d1f98480134131800610041c0114224034010310070740f0759aa043c906103a4880c0c0304249000700340e1520003594943c11458222140b0b94081d14045092460805102a940d005601940d011101141c002100c0040d400000c4c540c102e940c3c40500546103d016942007940d021403e13400b990003440c544000042510003840d40c9120910019250032442c034801e200a5200382c0001100c240244100e0f403e00300c203060f03185821f0b4029904119180d120510070448075030140945082820200ca006041d860404040303001e0b818030492003010006210b8200e400c110500508d007030385d0300302a005284540040312031150349512841815010412444002810044819810070b10359440b480c4030f00305464090040d14001040c61100b4015031058030200c0f842 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 393773785 1250 393772535 393772541
    0x12140d0203010f1802030411090a0603080d0f050106080709090c09090c020a03020c0105070209010e0403050708120a153203100906060b0903031c14070809060c19051606 74
    0x604800850300505a10340908804140380c8900b04e0548680188100008191507078a0003403070f00802d840d001c10a0f034910300132800400c1e00e5040289420f00102d410302c0c00503140e500016a884441d4020441e51740c80f10400d80388910210ba40c1800100d01c5c0105010204140d0800c201d6a001c0c0d0401c08411900c9140e06002d484c80a0070300001640140288428075504206000d228003080c20024500300c0140c0110394002c005002e0814440684004501010f215a00312a8003603040364040761121b0800042081d030300c4042e207030688038500741400a08002496605d01040b5a80e07a040510018110862403403039070000382c0c040040030340c1e52038140700688003481080024407250340000380743c0e090762070300c41d04480d580d80265803081000d00c6a011703140c40002c1191519204c0b0480d0000700740b40034009402510550a28899080c00d250500c400c423600102000c0c090302044083e10b401d50fa0f083d59420484c01440d1060074100f030aa451802590b0044000700078800524080c8000c1212030b40b601010703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 393775035 1250 393773785 393773789
    0x702040f0911150f040303180306061d0f010e0601080a0e1e070e010501050403031d130501050418030905240711010f020a0203070b031e0a0b0f04060312140d020301 72
    0x10542841c060341e814940381d03001c44500c03004126540e04100d03050741301d4682d5010710300000301404400c41200c5c41004e54407800c5030045502040c1800404c1d10344107850226a0107c020080906c014000b013418010701c0300039541624500290072007556112001103401d060094801401aa540d00e801200c100d4107004d2100c0001c131184410b004401810340e03080c500751080d8403100b6040603100051050345ea012084038100d0380c0501c0c00c040d0420f03031001500c0080220001895020444071002805101036403c968100d4404580400440000041d0744420852200c402800902c0721a020300507440c00348000900e8454264176400e9281141020038031503801031000350f640b0b03500040707813400300d61f480ba48102d038060b039900c0604091603003580807030381d2401e03903000e0f24540c00e00c0480084c001c507100e000e408640c01d420340c070610258208020f00c5801003c07007642e01405140142c0d5116958141801600120780c4c0c05a00c8008421f90b507441100c00006e220090341410700f0411070340e40d00391100d00240d40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 393776285 1250 393775035 393775043
    0x80c0906090a1401110a0b011e08010501030303090303050105010201020a09170309031e060c130306021b01090c030b0112080412030c0c060201051f08060601030b0307090e01050a0b060c10020702040f09 88
    0x240143d101000500480074988101d100e0780e01002603c800101995121030454105111a10401403000c54020401c1703841d070000c6080d0b610b094000001e165050f000900c225000341c90820240c0d88a130012800d0344a6618141e000c01d120500404c1301d401b810428000140761101500c0c20000203500090a00480009000110584a400c4001078606001a80d00100b0a103907483c0f800e1718102035075070744031039a100c00b0302081e81c00320b0004e070014043d90f503400100404400800022026141100c00c0140c540030507140d802c101000454514581c03c1c0c04074207550000801030a042c54050040700b40b01000400710b00700328a00c0c4010780003a00d042e44210190285400104840c81c110040074440002c10705a00c4103110103090401c001640840c5690b04070030203182c08506848294082403500b030aa03030049036a14500102d102d040030703040d4000d070700a01c00210280682d0a4110800a40380103034900b60400d600305402c401d50801c900e03030090202610150020481c03061110440e402c84d81d100509071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 393777535 1250 393776285 393776309
    0x15150a0e030d02010c020d0513120b0406050a051b03040f21081308031f03051002130911160c0e04030305090c0d0c1208070b090a021807080c0906090a 66
    0x526181c01d020120784002584020002d41c040104020340c4d0380150320b840014400e00183e21116815401030100c00b40105400150010440e844d1220340c0f1034040b2000d8800780d00d44004110500402e009603401030440c1c07840586441000c1c00340d98540d038405001110310300b103816000b200181c02c480203c02c03039000c550820510010800c8002c0c0500130300501d164a56084508200001000030058a030050740c030b12039014003c06042d0482030440602e40000e0003500c0b680030034030907800c040d030010109000c1900b03440b100700b030740e0308001d2098541c0600c1c602d186490a001440c15001c44003c900c0c0b1050040c02078500480d50391000d01c5040300c0640d803c0d4002a1214100240c0303881c204805c00c2010b4043e2458440302c20f0036114510140303a00d000e8800c0c80c950a0600c0300c00d000c44103040e00c4069070440590100e6040461a03280d4510703c1642c200c2c0200d007100c0240100e06440313030100e44101d51644a95410b82c1e2a60035404455010304c6000d94005824016007043d0340720136690101811145d1404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 393778785 1250 393777535 393777557
    0x801020a0f030216080304050c1f0f0e0d060b15070c0f051206010614360109030b0604020702040f050a0f0509010b01050f0d0605090906040204050f070815150a 70
    0x105045030506048003814010444d004496516005401040740c00c4000c0d80e4a0303885030304d012410300b540c03c0280c0d03600c200d001c0100441b01c0c0020050f91460300250706c520b0104c1140010079a454507400040580c84101324034128003040c4150400061400c0061000d40c0744504259068001d03044001d0640c0e0004031380b2004e011141908008038041d100807107000304101ea038828a150395540500900c030070840e8009260858070300000686002c1c21820311781c0c2002400c00500132030240c8031403624407840d416000241800d54051090a4152500050465641c1e074030082800b0181d03001c140304a80141c3c3c1d4403c120401c1b4114800c00d4081c0c0c90058011402c14a078004910984030302410003103240c2d24040400c101030780c11104542c00c1501c5010300070345410303030402658005c090340e0b48000d030031101c030300208042100081886841148200d608025684441c0c681034000740c4200c0c0c4020200c0e60917008101104901c4104a024907401080c6400c030a0519140d0359003500f080307107203d012075401550 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 393780035 1250 393778785 393778787
    0x6120818030307150606050f07030e0307050a03060b030c1903060e150106030c080c0c071a0d020c1011090d0312090501020c0106080106052b0f02100509011701060509190f0801020a 79
    0x1240b00406c0b01c0c0c9071440c00c0c581180000c15991080ea00024140302d0107030920030350f81d10f080c0b01c504010500282000107540d602e083c0352020b481c224003654031034002e0407059030191030200b095a0b5004811102c134001c0b2815035680c0d170024019047d200c3c00c0c902c6800320a0420169001c007041c0640880d580120301c19070140000340c0b0b2004007404460b1803450911042381010780004000c001c48159100b404400000c01102c5401707031003101500e90140b0300000700c0143e161400100e018000c9800b6170200076035103a80c0c448c04114020010034642c041081c003440030209224244821000310306410002d40c90409030758043c220b07840460780032181d9444150030000c1003801e10454009200948170040c0c12511a16600d412080c41e40040d10140300384000031050101c01181414400d81c040c02a034001d83c0d8450000e0b250340c01c00000140002c100d012400d40b0403880703070303025412980c003500e07040d04007900d0700100100b820030801264000d4001020002d000d0b8010f084e400002d02c1207200050780d8103c0c1c07501c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 393781285 1250 393780035 393780041
    0x2040b070b13050d2a021f4d03030105210706080610081e100306051306060b070507060311120f100b040b0405040c1b0309090b040612081803030715 65
    0x41310000e0444480051000b58a480342d91912034600c00180f0740b841552007d054400e04044004c242c141955088000c82c40707040c0c003400f440c0380b000c03e080440c580c1103c04450740040581030400b101780e401c03d0004104c241000c480d070505043d461903116a9803440c0d20529441d00025600c10400181c094003401560b040180c550449601c06141099843c42c048940c2c008001081015611000038800005c41d80b01d100a1000041c41e4484428000da041000061301c0f0703061245010380350146050000103010f44030200700c58a1550002c09070141e189007650070f60041904d03002408010130200b088011200c8084072407803052282440115203403c21350302d12607008006403c03c4000704410441840364a2009064804851049502142c0c01681c0708088404801c103030030307480e00c440d07001e03908070100344d00001d900c1d0039a002c14004009039000700b410001a2a032034400e1201c0c0340c00c8418410081707008100103144400e5003c016101000380b9002080c42c55001d0304090f941403c25034001010f042042c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 393782535 1250 393781285 393781337
    0x1a01080115090515090d080306040f02090108061516030302030405190b010e190609020a0e0102190204091b170d082520010e0105090102040b070b13050d 67
    0x80c440740c4490003903107000d40719004a00506100d41101c41e0702d103200344060011254a03450181030b04161140500e02910f0b21340068030954403903424105c1403080d0f180c440c0b00303448259505940b10340c0140c554030140040001e079418501070301102000080701d01d00d500031a030b034005440303683c0041e40c0346820300b0301c03600304081d42e44030035905000380c4258004070365041030071030554642d405105801d4540010406800c91201000c01c8102d05143c00024280c80c290b010705500034164030f40d182042d10070001240c90f0038101c055070700c0100c0c8401e9000094240703544407544952280e80452303440076a00150400c0c428442e400851211600004a0906001403002c2e44a164650804000364103142046908040501d40c0200c0c10144102984c1e4035544a154802141c808428503864081e00080105018240c40c20100c0302641c200008901034030014401c5504448400c44414100843da40d01c5422644001e0121801b00101c3e10154002c50720030f02c00c0b19459940c0352901503d000285012b5072050b03807d2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 393783785 1250 393782535 393782549
    0xb0a1e03290402010f0201020d0510170609060703020919031113050606040e0603031315090b090619120c0816020309010806101b081b071203080411041a010801 70
    0x90281c00d00640181110381d421036030900701200d8102180718200d0080c01058003040409041c00c05000b0080ba0b462401001d03250400c40f01c075601c0250030714913640da00082c2c0d00f06280b540400c002a01142c841d50180c09140c0000f0b01d81000c144d20340c200e40300d010286802c143c58051400300c0d001c04d2071821651054080b80c0400b01408145402c60000309a03000d1072007040490b100c200d00180156905000326403103134401009102c811a00c0381340589c594446c1c00c584c40b020034101d42d0003080600c0400c05849175030074010866490702d1040400c5854600080628000b407001c400c41c071982c10305260082c1000d601c030660b218034282c94042a96a88445040d0400f021342d041006140c1c44c590388059915444402070b114280408007200b411203031040505000d0040c243d0182820003005401002410700c1080d002c801d01e2650312801261b80c94016a12900702680c0001c0d14000000307024407071569006020b0038a001904900c840410192008001040c55030074503980f41010a603009001e580c0500b1503 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 393785035 1250 393783785 393783833
    0x206030a0510080d02190309030b04030f021e0a0f030903170c1506010e011107090903051803280303060512010b040c03061406070203070504180506010503030a120b0a1e03 75
    0x121490207504c1d4008104060031040351b03280031106060041090100456104403800750b203280c0b60800030b0000c030710480c018005010f12405448414046842514101e40d41009420314201c00e0b940c0d018040488003003142840314015000000c42c07025010888001d1480035103607540c0d0008108031f402d003202c524030388403001c0540090103d00c0c0d0f4015409008860300303080001402c1e00040d90315181050f035600c1040d0460410304074004040e80500604150070383c095031280c240c2c81c084101900c9040d9415900c2d130b0342441d8000446100b51000c54151034a000307040014104d600c440c049480d00308181700002c002da455151280e6a030030244203c0c05e03841003500e0108110b508182e1083d47c1540070500c1d0a21481001c40e4000039541c1c1801100d0062100a0003000070070780b9525032144030001d0420681c2c85004030340002401d42404011a1003001141d42d69030114014461610014005a06030310340080043d41c01040035128000c5540402c4000b4841c0002c1e14174600d8900808502120700c2c03901d144e0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 393786285 1250 393785035 393785053
    0x7030c05060a17100f120b0f010308121504151502010e10020f09180103210e010f020f0a061b09031131060311060a0c030311070206030a051008 63
    0x190100d03210700062040f140d4224261a4420b200243e840b050300402290240791600080001e81e040000c0c01e8548100f1850100d81d842c403001d089070040910024004c000c1c2000100651161150304a0b44942844044002c1c007083c00041002c4511203103034410401e40a074410f20482881c95a501030000c2e840c402480b64040019074642c640034280c8103148450b40110384200720358800b0080c0d5041c10000b0340501c002d00c05548040302c100305c084c442585c0c0e10b41c45040d8031104101504ca2025524069143c00c40740d425041d004642d104240c0c00070324110300800d2140440c4030014441c0c500c0d03d601910300416079909283c842e6420b00c0340d501c509003d01a401c40100700143c01180742c000890012030b502e681201c0005e04420032201503104080d1101c090003450302c42883c0c20742c0b11000752030281c0c010040c2701c8110024030289105180c4800302041104281c1c0740068031903049481200c00c850049810107805134041541070704165080e450b2207440b01e01304401010031625880c010315501002f003030615 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 393787535 1250 393786285 393786287
    0xc03010e060402070c031b031b0501090f030b01050d020d0807060c08060103140a05070302040e04120906140306090c09031225080717040f14030111031005010e1305040507030c05060a 80
    0x540c581b00c020003208102001060312403c24002c10011500440c06000034195540701212100c0796008907808140c0000b00490485401d09295080c1c951113542c00c103081c2d0800e07080188481444104980c000002d450322400188444054a0850f200e800c011511030403110010341300d01002462181054070b400e014070440d020190034190031019806002409072900081100a07209075041094203440c00780501040000c50310000e40c22a801daa14034020a0b11140c0489681020b42c0c0064880c00c810b01c0410018a0003503c0d15801451108180d07152841180101b400c20221040040580070007003090214444180c80000c250a8620519110b00c00166038142141c0911100500204800740f60000440080000c4602805905040d15070a43e0340d80d50070024a411444454000d508000b01c50782d095500034252402154903082d00d4401c01c1c1001c0044441e40d840387c1c003031a4031002c580e4203401240c07018803813030b03010f980590041d202013800c40c18003c00c150301710b40c059405043c0c01c0014075103203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 393788785 1250 393787535 393787553
    0x4080c1810090b040b180709060912140f0105150406090507080c0d2c0c0a0510180302180402100e1309030c140c0a080c03030702270c03010e06040207 66
    0x2440b84518000303590492000800e009142107420960805244015404943c0b10544101e1043c056581d032640119122102150041650310601039800364001d111000203507031401c807540398075801d002c581144410300c12490039280c003a18040c22900310042604060b00f80340c05000003030405400103000c1130a1500c4010036082c1d0051024942c0030000caa0742c41401c205d40c002c030390100080b1b18030310980c0036203000190b28400040422a854801e100400029003000140c00e0203d8100803c1c05842002e21b503800d07161121803001809280c90b440a0100060391280021513881c80c50052410540c50144140070003d600e202c80c100502205040040f082d98503145452a20150388a010491031554901038488501003d0010b0101886000044143c10002244007148500721007004090b80d65150040d15030b00c03001d40558054000b003080c0809402c002018081d001d594800480348112182e81020400b070b01035502002c000d1000004000b80c0029180040c1c111a085608511f01005940c030a0b02c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 393790035 1250 393788785 393788789
    0xb030601151b05030309030a030b0301200c1608030403060c0c0f11060403050d0e040c050a140f070804060801140604080c01080603010219080906010807180905030f04080c1810 77
    0x300411801c4444100c0401d1000725402c650010032240c480c10008450380e100d030042d410001c0064640040410b441c64140500102146c8400e1580c4004084042c0342c07486500c102020007a5100e003074042c0c2103061545200b00300405241000d90380303407802c6242c00819100b82c80c1c10306d020050114080d502041d281d2840380107442c1d00441c4a2054021080070603400c0c0030f40c2c0c0c0040c0c201e0060101c400c4096030000760040007040e04840420004544480680f8240506181480041c00d2506682c4a440e0f481009081c402c0f00d05100a052103142d82d2100c21990003500920006911180100881d10018081c04240c1e0800c49009003840c0c20302c0c000030390b54043c5105540c100071190b0f02050baa500c3c203504503445540a211064818040702c00090405031040d115510f80e0700c60311000003001d403804904903044c0c0390302c943c0b86030017840184281005401d00e0001922140010040d82c0503a00100740104003e100703410240c0118558202002103420078a1488443c10008008000380b1003034400360241 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 393791285 1250 393790035 393790037
    0xa110703080601030e1b2e052d1206010201060b09091017030703030f0b0d030c020a0e1611030906070b100e070e04180507060c08090904060902130902010c03050f0c0607030203010501030b03060115 86
    0x51910041b0035a47c01810603500c07000f0354841e01c448040c83c1c032949040103202d000d9600c0c5d070450441d20340bc4012402c1700e81503c9108400001400800807a02c1c0c10f003440d581040303010305d1862032a9100c0321450520007131030720302c00015440002d2060400d5010f014041702c42290040401c070704540f03a000b00c0c1402e15850b00040810030f2110f400003c5540f011080f40250100c00d10007243c516210070200d022451404420020500c5100c0c148010040003003201c03200c4001404081c100909542c445201e020050000724007035613046d0021130841e50f2201e219200d80410790300cae010021600821700c404c88080d1803158280c0f40868420f00d0209500040343c43c00c41c0c03034a150600c0b80802c5803c04074054000c4030f18040c5d2001c0b00f078083c00240302e031720b400200689008569003140f006070341401004a40445030020b0104050b0701a44000ca4007910241c554001c4100d6003c1c40d0102440441c0e00340300301280d81c4008039a0100042c0202d5070b140c4140313944450181c005120650401e42410044101201c81c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 393792535 1250 393791285 393791287
    0xf0306031e051507020718020304021f1b05070608010e270c150a020d1701030b04080d0c0921050c100201111206090a110703080601030e1b2e05 63
    0x3420000200071010f40b0302c4031030200445504001c0c500a48400c0588115451501003407484824107002d44222401190b000740624803011606403981050075140300e2210602030682d559140340212040742d00d0300188640c02501c462410480003500c201c1c010b802600c0110340d500101304004520002c50074034000c80035080380030010f103500c00900e481601c1c400c003a0000c820b07401c000e211020003070150091a010781c0a481890119040881d90700c8961241078007807044120040010a02c802c1405403c01d00030620316246c0796405141405031200c0345564000a11032a03000c1240400e16a4100c40d04c0d80000c50301c4a0310540c54848690320400b074078040d8418400c130750440300c0c40d80c000d602003418a00800151602c6100b411055022248215081802a080100020742000c00381c451403090400d0001443d003444200c1c1ca080b40c5e186c1004011030306040d03541d000c08801c80310802210281c600c658040c0c2070405800024451055282c10042c0b0582e01d01d0000d4034440100180c1314401144c89103009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 393793785 1250 393792535 393792593
    0x90b0f013807030201060311030d0f0f020c04021b01060803090a09270507080105061815010908060c072001080105190f120302010b0f01090b1303080d0c0f030603 71
    0xc000c00707002801d4801d015034000a40142016010340018040300c2c040c03e104e64281615105142c3c85540e4910b1010024106000c0608414003608801c1d003407005a104807544040aa0301103000c030f03405111683c442c040d509858078201c200c00d005a13005888640b01450400d090040490b001c40d010380120308500e902c4480d103803158001d0011101c200c00d1242c00d0301b001900542404c94807582c0754010381d9415400c0000081c0182013041d585542e03c42c07409c09a0b4642e036545a00d8030711400c81c030400541000700d10000010102d10801c01540114515201c042c1c3c3e447c0a03290070900c0d40646000c991401c007120441c2c0c1130780da0304403590030304490003620301141c0071280070020700b24000960488801d1b203100210200e8030002114101c2511407082c0c00030884400060204085500c03950780c4107001a01c00c0030240040c60014000d0200d070480ca039541d003040c1351280e44a80d05500f007134100d1840c0554850306d002c40c81c4e9019500b8044035800303007001c00841e41180c6a4040b14018090925645441904c031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 393795035 1250 393793785 393793859
    0xb06090607150f090b0114060a12021b0106140904080301050f0607050a051f090c05010f030e070305010c140c100c0e180a0e031c0e0a02090109090b0f01 67
    0x102c8010404104200014945001000d000b022100c0c0305442011500340046000c0941207401000d460004142c1d40c10b01c070100100300c1e080340600c805001c89a800b8085020003400e1380c0c407011a41c10360000045030f01c0c0c1c28841c8200448a105090740c0c801c0442c2014030011515540c2164190340d415a00c9a008543c0340011641900c42d1820080192048541680612802140b43c02400805102c80c0346420043c00030348003a2492640c0c050101048aa02049950b005110388460311105040100d6004400c04140d41800c21540c8161416511200d085120907808403070794016000969240f4148401965099a0381c2c540a00f41a0103170341e40c9819141e05806910f43c40c00154004003d44400c021510248000c06010754006260070709213500107224200200a03101d60f1506801100c44141c03480500344081c2407450980e1613580502258503015844030110303140a0f1a508001052700041450007903000603009001c0020303550703241d0040c00184017201c2e01c1c0c0811200d080000030f1000700445 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 393796285 1250 393795035 393795053
    0x5060406030c0e01080705090708060f0102070906030804050301050601050703120b010e040c050a021b010c02010c020a09020a020622080412140303180f0f03040b0d0f02042402010b06090607 83
    0xc0603111040301140001c0c01410000044d0580d9808402e03600700551f00c00170301079914000c4c0c4084020031034100006d580740c03e10700b0102103030303103c1441211481c998406094086410079081a03d8000c80000c0500c0141802d000d4160414000c0c81d1062801da1540c030001d14111400c02d00c40c00e20381e2644250509a031003440041080b00005104002420012001811a9006140d01d00250254241c2010184074491141d1090003042e114a4041072030707640110740848520004076030140c04c540700401c4404440c8040c003c900196001002c079800e14000c07100520401929120043c01411208030010b4854025902110304080654030011682c0c544401c05028000c00c003046072101200300105c0c4102c0c520781201e00c2924034140d1f680548114841c03501c0e00030f102c034040c0896000f0002000303400110401048801421000011618124900e4400341d82c81940484c051b21010101d9080c213007120490030781c2a828034002040650021004185a80034000c5030034800c01010801d5030074007005074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 393797535 1250 393796285 393796289
    0x612090c091a04050613020c030f1b121c021c0509060703061e140303041a030103170c0a03050c0a170c011503080304021c0f1a070311070605060406 65
    0x1a0500310025128a03140300242820b281800d505440d50900d4503803400c00744542401003070060041c03984600d4601241c0040c2d40b01100085036807000b000301c0010002c0c114090004801c42c0c4e0300e00d55070000c0080b282860301107a00c20600c88848108115069099410000390f6403e180400140c1c40e420a00100c12056460755003502046040ca800c00042400104c0e03074a100741d150762810000c041d124910030981d54031405040400e0040c8003824030400c10102031107901c1c2d40b0700504891074503480c1c100030030041982d032814019810001c401841040440504c3d5648610444d030002c0c02d10140d1f010035640c4502d01c0380083c050080c0080e2072038911509008581c1e560f41c1001d0275000361001000c0c101420740c400c81d0000015440c1100c140a9070903001001d000302d98100401d54116240d5400b00320f1184402515005010700048100001400d840082c070704542c041c100d110384200c0926603441d44154010280020985000d000c11b0300040c1c2e0b107007542c0c04260040c0300019940c2d6603801180c0180348607 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 393798785 1250 393797535 393797543
    0x7051507050a1407060e06010e09011a0609060c030c0c010e0d0308060f03011104060c0606080a0b071d1804050c0307080a140708031309140105010804080a020a1e0215070b01061209 79
    0x446c0340003d8800045040c1218005003102c80c495444101c103500303d54040e516501214000d00c0750b05a1403610601030810910001c023440e04e80415800e80c0d61a65005030010032094000034210b030031542e003050010441d411706450416002d540307580c0082c111640142658803400c1000c06c1c01e60551000d50021240d040c01c0d100d039958960310780d00302074444410400304540040c1007050100310400081500050950f100e69110095220035038207580b01c1c0450f01e14054195090102072110342d0321018000703e011440c0c05203400c00c0c00c2504149082142e25404280607034801c910401840d40c00280c4000415008400c40e54490182c09a00d03040c042d9580c003c01c924440464070390701421941c810602110b0010400304a050300031f50481030081c40912032140803030000070002e008141c2003c004c0030301131124415204005035651310007400b400fa1041e0b05080100f013826010460409811021a81503510510703810030081366070b4600c1c1c080c0c0501a440800103503440300301d40c150003074010400490340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 393800035 1250 393798785 393798791
    0x90a0b090a0b0307050d170c120406031a041e0c02011b090503060f0c03010902090f0915030d020109080304030f0c0c091505011d060307091a07051507050a140706 71
    0x100711140301501150380341603c00c0c0103500d070004062504651024036564400070551000c5040c00300502d49402082c013090050090440c01a100660540140094001900c1c005444d1950540c00403180c1d10350a0002d0046143c500025085c0c0c03551181b044180c0c01100b808198078524120132805020703c0b0368501c07441003c110080240310b802075421419a40190200c80c043e07514680f210070812416a004c04035003800300f0042c04400c0e03032a0001c0c440c605010b04a140401980c9001c40c580310004c581c0800d8000020a00620500d001e105842207500320784003c7c001c21243d40c4445100d48001740c001400c0c13114000703503a40c0700750003240104021a0095a01c60b821550b07001e0840203491258104040b008004c2404500740d03005031032620340342e000090341d05803059100003400300d90f178000f070710000078041c40620005941c07070603114058500f001104641e4480c505450160316068101404034110702c447e50070824055401400d0701c0364048249040800c896201d149585184100d030406011281 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 393801285 1250 393800035 393800041
    0x408030c010f0b06191202070510050a1113050f1212031501091203211109031b06030c030406110a05070302060106091a032707060f0c11090a0b09 64
    0x1406500100040d0b42e001401d00082e0f0203041004a203124040b5401113400341c0a255095903841040564091600c80d24014600701280d22018507255490b440500c00310b44038010800450303001e0281c0e00351340840070351030b50030024003030042c0c07041c005907008070380c0941c82c1c0d040d40210640c1c2d030500542c854004041601c600d5501c803601d00010341d008550200300b45240e644002c409500c12071003801250203211910a80340c40940d41220410451402540799581c60104404140d91034801d8011000705841c0460352410408285401e0510404a910b403207841c0d034503240000e84402088070307032001c6a100659a29031310740c900140102102c103040d552001010407154a0143c02000904815000307400712006a17a84030340880b8102010700501c03442c000542c503605a4001d0b90405180c0149010f00406000c0f031007002c003218096200b2030601d1a56021840c1000b5854102c01645080007181c03a14150155807515036101c18419400341e40e00441a510002d02c00842d99880380c08010700040c0703502520300b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 393802535 1250 393801285 393801307
    0x140411040305070911040510031d06070e01120c0f0c060908070c0311040905031603140a0503010303110703050c01110309120d090603020c190201050c0102041e060f020703080f040803 80
    0x10084e008081440307180c01c051020b103404d01d0050350201c610045c401c072040500076900f18041c142041100360020001c1d000c007440600c080c031000f4860740b0155900e02d4400c0c00d04000400396000350880140140c03074800c2000d0141d0340b002c02401da0540e43d080c1780020307085500c0d01e400108445000913018035004140b682c1004580c42a8408407801a280320702740d02244010001150683c8000400e540e008000c8254044418000703003005074081c2c20b2200c2c0136000c0b4108600103070b000b01595400039800000500405410540640c84c1051600003002c08504603030f1095551002a442d01781800007a00c140007150348100220b454a04010f0000c0b1484bc035010342c0981c1e60050416458045a240c00010520520030310950302d4960382003004015000723112080d110318602030786040c0d0400408111441c0c00c44004d00052000f008094085c0c56801000e03815585400d003075400c00702c100446c801c00040003c3e4009040415650480e034042c2d0b40f610940e5403044e2034401c0742d008505c24040400d501001c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 393803785 1250 393802535 393802543
    0x6040201030b0609030a060b03070e0412020118030806010305220c030507320d0506180d0509011d0a0513020c12070c12050a0204020c060925140411040305 68
    0x554400c0c0c80c203002e810320100810400d4040c0ca0702c0203401d41c3c401890840400c1c42c41d04003080e501006010745040c40e403100c849012040044034141e9100032910119040903038244110b06908109000d40c0c0351612031981d0041595202426030350403d52144041200d95103200d64507a0301880d020808602d0158510302440d0440a0b44015034203030150003030010300031020040c40100c104100c600c05075a4a5890010602d030035a0f924065002101d0204050016104100080c0104038003c0500507000c0e9986c2511729010070b0322107450420400b448400c3c8642d80000c5903021214407504622422504040821450105a805154410000885c100e0b244455500401c114440c03903054171510703041042d01c84880c4c419040002e140d40c02c03454042109080782d1203600140c82c4520300f916814406500064140c0e0000c0e4174020301d6406c0301050200502c81000050f580340c6001c0e600c28000d400e200b600d00081000e40c82041824403141e41501e41a98551780704500d588503040200f520745840381000ea076a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 393805035 1250 393803785 393803791
    0x100c0501140106020a060207050102162f09070e041e0606020127080a050409020310081e0c0f01181514070f03030911030d08151903080f041706 63
    0x95518104105001c1c402829003541640c68030b400130018070100d03545240083d4010002610b545d5801d004c403c1800a0804424041078020611180480ea4000e41c000b0107011161005000d4a00d0307103100c1c0b5a6443d4214950340c4140c075420b007036511070908000314014060074804804003082c80500100c4200c001c3d4400e5050382c49c540c1c000c200c00f1198030342078290200c5030250072000601c441c82c00c400080790b10b4014100c81d8103500c1c019003020354500c55482a078000b62a802d1a5450f911000d0055480030000d404404110404401c075442109600d56110580c40704914051407116404200ca0390142d44100a055142170300b02994a87d1a10b9a03c0700d480d81f01c40300400500e420312400700d4025078006680b01c1b103411100d640c041c114903a07425030041440d5138048580d0019140034200b19a004c1c054284900e04a03240c0100e41c0c506103003c030307049540307076a00d06102d488401a240722850075940c583d01070700d41c4610040e07903480b40314003080001d0080e640100031080d1413030a03001d0420300100b00380340 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 393806285 1250 393805035 393805043
    0x1101182301200a090e040c03060e060609012303060f01090615050a0e0d1a0a05100b0313053904050403050a2115030b06090c04060507020a05100c 64
    0x108204020680340d00761000951440030301c408001c960240d41403250000d1860312064244112a0f03aa00c0c142e0601c0401e08403010780358800521010001e2121038080c500e8a000d5080c041c258500e00500080c07240c2da0180560520041885029500349100850f941c0b0390f0702005040390701c40d187c9000d9140b07598809009e12650581010400a04100303041c2c0c01405500140d166241418210030040b6020400754001c1a8080b40000d404408a1f0601e10460741915003802c0c11982450030440950075541d002e00140001030b46110b0401c1065032180541ea08058403250b600e040050504000340b030840038644440341600c0e1804e07241c28104d528280d1885401c03556030b100166010380703010401120300869000e0080707030040184010061050408409040d030f0918009800114035801404aa80882c3e0203154800c200b00c060080c0070600c03140c20340c0b0180c115418510707031500c82c0c04807400313000300e22130704042c8440800c01c1001c6588a03148200039143c040c0c903040c440303188190000c001e16040c0e80300352 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 393807535 1250 393806285 393806333
    0xc09090914011803020a060203060d381605070809040e0a0b070302070305090f011808010e0f010605010f05030c0f030c030402100e030c060d0e1605010906030905060601110118 77
    0x1e515001e100c401c050300d858240c0c02500749141c01d521f411020750700003010194000d48a01c2c401d0006200d24a00701e41420302e44030040c901c881c0c0d802d0910601c3c2e030500c41064400c002e08041202d00340c0184d134504500110b500d4081d0319074030309280040301e90140b0700783c1035881420b01070000e1000e14005400303039182e40603580004140d25003040580883c4111000600058010000748800d810100120626402c0614100c51900240c3d444030891712059004500140d440307170202007142d0401c00071884490350300c4000300085c82c0f91100180c004011101480140715000c07001440c0038a2a030165601508400c6485690740703041007000d08a41e01c100e400b00d21403000003100c1c0203880e128980c2c13515038040180080c0605203200e000c118064110381c83c40c15a4684401000503503030700038010205402c0d00c225000c421242840005062001309030008010180340400c4040400e1000442a80200c020309104001c10342d1407000501500790724281603000d103201840c1b0130400a00d206071800782d080d1180302c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 393808785 1250 393807535 393807551
    0x503074119120605040201020a021201151403032d040f05090a050402030c0402031f140a0806090c0402130803071b0f03050715180608010518070c060c0909091401 71
    0x25215160040c404020003000081000803d950301498200f40140129a041c2c1540d500040581000c940226460b944030340700c110054400c4182c50014148078540210055120320210b40c1d07074001d62400001c06000622242100211107120302d280a100c41403841d603890b140d084403d620465840f0302ca01400c1c030003001a07810035281c400d141c001c581c01005090080782140800000c2d402c0507080c030042d100503c0783d9100d80c504e60111031000f0820181c3c8000d003010f116040040325080c0ea0b0200b803158211b1020010744850104400ba02c91504032030040e02c0d09034001146000c0c8090b6080940c00b0711000035103200f80001d01342101401034a851101250988034542050500c8180c032000300030340e212000c10321484d410300010302a030451601c0d02c84070100d03a03e01d01c40d11a50140c0d01c0140851880300c01807200d8202002211065240103424026a0804010007404c1360032540c000707001c00d5500d00400080901c030340030800040032203d030b0074003005000c0c0c144507105006030700049000c2d61900e100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 393810035 1250 393808785 393808819
    0x70c060f0503090a0b10090e161d1617090105090c0102030a0203041a09030d091403011815150f1706010f05061b0102030a0207051605030741 62
    0x3160f00c1500c405001e090440e0b03031551a0b541001001c0c1696006201c080c10100392041c1c1807090304440081a002050300c4000310030841084201c0e81c00000040100286d10404182c4d034041c2ca035001801011f15a9102c40d981d2000c842196642a1210451504409000030250150010380c0600355203029107010013880001640c4d03e2040f86010303c0580c0050004200031140f00344000050360700c16401d68501080500000d09100c4031620303100110f032002c10280885020fa00030210b0342c200a8000b0001203a845803400400e0000c040300609203845a13201c82000103407500004842c95000d0000741140d030311019a144c0c900f00c0c2d03014180c00841503086116a200700000c41038126140c2c0868000c9041c10300040c0040d5610031125031640c041d00780d488003110030092004610a6001c00001070305c0b100d007498440d0520340201380ca110107140c503510910256802003a100b040314600f4500d044c42d80014080102d20f141034140c9240280b9521840a036002607405500f8030540088500c50025065844 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 393811285 1250 393810035 393810037
    0x301050414161422031b081c0203120103030f021002131e0b0703020106050a0506090f060d0f090f12020d020c010e0607060203131104110f07030311070c060f05 70
    0xe44482112600030034401180d0150000700030140002c90f074949081500b400c0a07180074074030301c0d40428469500000308180444200d00710054040340000784020341c5403030320742591072501214060141c02343c4882d00b00311a0081040b16141c139500c0d20012001e41c1e4a04010300595540b904440144c051101a01440c1d03c0c0c910031a2072a098043c1ca4280480c103003100d80b16503004d60b0b0302c3c0411a032100840454151401005403501601c030340e0004ca50241010184404040c455105501501d014040c503040c0b0340c0c8403069241400001e0390281e454515007043c1d003016040c52014110340364900303001002480314150450190340d004451450400e1142d403000ca90b02d413908003080d40181c00504891020b1b620400e0801000cac940100300e07506000341c90311a80f040740c1c42921031000d811000c0d00c015040020311101c41c120220112010090001e0030840c1d520350f071041c5243c00e400e60318000749103004c00d030280d03101c0c10751500b07014561500c1d429149800140c841c0c1d40d0243c070020903280102986a0740c8100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 393812535 1250 393811285 393811291
    0x60c080d0b0607170a021207080712031811040506060c0d0807050403150b0f0907020a0813030b0705030a050f010308040909170c15090d0903020616170301050414 71
    0x1104440c80c114424110000800c8046a196030000d01005248045692411840e14a0024940381e6654660903400646010709504c03104d1034002050111401190326041590f654981100c801e1021000d002c504070300400d01e000c906007405056201003810301c081c80d03589c207a203024261000c1040361241403c2080602a926107190b0582c0314000114107203208812085d001394903401c0c045d043c107440b90303201c1c04031401e1600480724240d602d2000d146030b0301e0103c40000144405460a4080707040c145002510b4480c0510003a1541d000081c5103201821440344100046401840c00c0c03009080041000b0020750064404075025810310010811551100e04240c0c1283e81c0804020301d802c5c42c100f2403c014141c4004160b42d03086816400e551001c0701070b00140300c04212130024041440b28074840d0040044050719040705944441c4680030955000150902665011203407244ca07070049001c688602010b00c0001460407500182c40d06448004070044e6040e01c10894081c0540c512a11021202440407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 393813785 1250 393812535 393812543
    0x709051e0615070f060507080f040503090105090109150e0a0902180913020a03050c030f010b090601031e060e1005010503070e01050901020c03030f0301033518040510060801060c 78
    0x109022038031500c0c106400030b0301111044000b90030819551512030100c000c01006484681d10784c0c0420030b41c1c41d0b21907a4281c1c00f507003030240710013036052079120302d556070084204d502c2c14000001010f0035560b004909142c02070101c010003a10400036400700a14034555850344a0140115030008945019903000f07440030400e00100320600c88000038104039030041e0152103100a18082c01502000d82c070390700300d001d0166005038000c2071181c0e010310a01d80780a03086141080c03aa49000c10450040e0341d402d6026421900034600800c1c4c8001e1404020102c03004981d42000240c41c0100000300300900b041e003644507030200040180c2d00c0d83c0e140015541c600c000c607800b4000a114200e0385c4041d60140c8060600340c003043c4111181400703482d011034075540c0082c55800907000c02000400c20400092140301c24501c03c034010030803814200c07919418480d901d10a00d40c402002040c80035071210591032280214030010000d210504014100c2041185180540310020f0303510000400c500d07000305543c0449941c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 393815035 1250 393813785 393813841
    0xe0304170325060f0c030b010210090201090302090601020f03220605030f0f150d0302032d03190f06120204050901021606020d02070f050304170613060509070902040602070905 77
    0x989401c030710b80a00548030460b002a540e0018502d1005240301c0d040310310050761000074050180c80d0000e440c01c007900381d001060340c3c00c0941c4240142d900005141c00c03654180d4101091f6180c400060b03003014110708030300708680b10214003070310304100c40b01c582503200066a114452450300e420046810344022034290403000d0401c0041860081c3c1d42c90941d9106034540d504410952805001980c481c00d00541640140c0c40071540c102140d40d40c0010071201c01011040c1d00b81c1140300981040d81c1c0c0130042c681c4601031108103414001440d103400500000f4401c0c00d08010150300d6904041c3e20850030301d01a8001ca20345000110070810510844250300e01581100720b00310512341e1411301a500c00d260080c40143c0a006107030009086c0b4545c200218869800340d620340381441c0b0000d5000e038980f11035850980c486420312108ac60900031085100307801c41808103881eaa004142c1c0d142200981c849682280f001500040059010694000351035403020180019120000d000d101039003218220300c0e074110303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 393816285 1250 393815035 393815077
    0x90b160905011701180921170106020a020d03030212160f0e130c090503030406050c120901081305160f0f0611070b07030c06060e07081f05041109040e03041703 70
    0x2581508000992031100440c14540981e242082c0ca14460343c2407c0c04400c0000c2c20140a070412142c5490b0842100320714015031404000940d503c28080c2e02a0040c4c3d4045100f00a2602ca501100e07030804002610310100e090005108204012180700c1200080c46420103a000303900c50403040ca413403003000b0450450300c3c000000c014000d000c42c81075a03082c081d032800300144a4600348060001000070b511101c0c0c07070700c3c0c01783c4001d414101c43c1d100f001c1e08850308011081050b80c00074003454202030000422031940c1c00f01d01d8205d180100004514031100582800010659400400241a039002c0d1955405055840d5020b46465880b80041a1689c224a206005407111040900403041c024940702b00b40071403030b49841003124070b2500300b001406001410003182d2a0800041d80c1c0113060f0802010880e64800b980c80080c84c81401042d20540c0c64810800d1400039a01c103403010703981d000b0820090340324004452a680d51144c49060750000741000f1002d5001804002d80b0303003000c0b2403145140d5104c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 393817535 1250 393816285 393816299
    0x6040c080c0a0903060e0a020406150f14040308190210140f04030219050f010515010c06150503030a090f0e0108030a0302280206060102011103130201050d090b160905011701 76
    0x2d00b0515500e020001c6207030000000c501a801a200e190100390301411258841d070043c0820381c1d078180c0101003c00103e030540b0955542c2700c84204170132001460291007840038960200c40380e100e0356001410380b5030b02240c40391000071410201d845400041d000c4650340c508840310103003941d880444a0390380c48252070000300f600c120b0340300301e81d4414401d105a030f644004255001101c030350501001e407140d6205034081c030b14910302441101d030402140c0d041c6520081c64400001e091080c100801446540c07038004006c0e060720fa0300b55200141c18010256030305e40301c903001c008041803128071403681c0381a0b4a503030028040c1c030751a41c0079040c0d40d030100242d4179100c500a019000f0358030402e4601d944c07141848540210b80da026030707442480b24260740034000d0f605100c4002800e5800e5034103400da1164040083c040440500001a441d0302d80c2800c000303480f021110714000c014130620001404c1c5a51840421040c071802040c4815136004c50344a4400c07182c0c0700d800440c1d40460400a030401102904018041c80d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 393818785 1250 393817535 393817537
    0xf0f0618090903050309061f060309060b22140f0708041b06170912090d23070302030f01050412110a0c0803090a06030902030d1b0606060905010806040c080c 69
    0x12496a11a0003280d41d0381c04040c1200c004141c01c0d00010804424821400824020706400c2000604101c24010b100380c8898031070502817140105050f5106444400c110042c0c0040715119002440c00c518410044283e610000055840d1100a85405600502c605101c08203900803640e10f0008003140c2d41d541130555070b0520242041d01d10182c06800481415124192100034100e1a52403010000d51300c425a440300c43d0143c848100ca4000301c855800e051001010380d110020211050081006e040c00c0405807000d01a00a0140c00040b020780b00e0071f858001040006c40344260121035102c02a22602401ca030300540e0010450450311424042d41c510464003122280b2045042c0c07803840713040743c1c0c2d1440005c55540c00b44003a900007085031103262400c0120b03a4001c0c01c00341000d10031250f290380000c0e11480251845820320090804103140d030000000b149510350740c050410085603407900400741140209c0d202c0e960000340320364002141c81c02c00c3c0c061200b20b203902d40c40d03101207511100d44003a06 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 393820035 1250 393818785 393818807
    0x30906060609180c0d0f1407050a05040503011b110d0e041a040906151a0d0213030c03060f0f06180b01030b130614060a0807260f100f0f06 61
    0x80407062503d69625440c000300c80c0380c09100404103081c2c0d20b0010b620108140e0f0507488017007803400c0c0781c01c19028954210400e03a40c0d1000c2e484c6013287d42c9402814054415024036045150190b2038002034a040c0910502e89101c00d009989541748225001c843c045c1d40c840001071030400203203030710580c2c00e543d080541181255610f6024910364295131680490229900d20109840700c94440b8120007440025011507400f8003445014a000340004548400c4248104c44240710b40caa800220000b044041d9180740c00035691184403010166540e080010140480703107010020b49107043c1c4049036420b40782c41040b0407200e0200c004007008603141c16020007080044034660525842c0c45800e82240d0341c041c8810101101103100191140c280304030b1124080c8a00d001c01c0c0150010081071045940158102d90320560394600b0042d40049000d5000145442c42590f209600c018400e02102458500c54580315511820042d080c4903921148004000034601c40c1c29610312031080140306d010301c02c0c100c40d40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 393821285 1250 393820035 393820039
    0x602071401140d090b2a030618010b0301030c0608130605060409081c062c090a06020a030516030b06030c09060705060f180a05280c0b0408010c020102030906060609 72
    0x401c5555000b00c02d000c3d5102d65a00c03240c040d65141500c08200303119144035041140381070300a000039881c0d08000c01c0e0101d2107a4070700134481c0120004400765514115100d4580c5d80e403026468a580d1482c0c4501c607900300b0b0104643c0c501000170702151039442840d9171840b9502c4200c850031021100c2c0c0320400107200181646820644131400c1c6404101c0c10001001d88094280b00e640c0c2d0418005031010032610039400816a1245e41c20140ba18920350451042404000203010038003621500c441c540b40070803560004100c0c0e03001181100880c0d800d940038034441c01c024a8605581c0170404c0c0308500715001c0025582c1d1201092020132080100c0102801c00848003801c804d203448619100c0d64074042040700e03400303c400580c000f04900f580150310b0ac408000c141030002e062404c5942d64042c1c0301d110904c0d003488556506800356904010004541150a4229080310180b0b51078000c0313906154001d00880742150f0030a41d078044042c1c4148201c0348140200320203405507442d903004118481d07002d1240c1c25 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 393822535 1250 393821285 393821297
    0x6180114070905040b09100e180a06050117060402030a0803070c050a0b0406150e070509151b070515120601020c0a090f0f050103261902030304060e070602071401 71
    0x80c001500010030303405044540c942c80c0d442803401d4100010307a25002109809010100c00780038031201108401419241d03a03807842003081d0b41e1a4165502c00440075038800152243ca00b0042c180300040d40241e058032207030824850711001d00038400f5076179039094400035019030020b04001c1c003040e04400a9a00040945044030071103596407102031801000c008141d40c0c0155010a01c0308006e8544514114488091041085545885110140080001c09039424450009080c51080e5511460301c0c05094040c604643c41c0d0341e081c1d0007148010550b41030441c0c244904907000c2428034004201041e85016043d04501e07003485240e07444146480030740000d06510403642b00300210340c1d03007200d103002030940706d58002100c0b00101400010f80d641c446920b040709107044010f01c042047c812885540d4a45800100400e000b4507549100740d204000344085030b0280c2100100e20140d000c4000c5d40181d000360028800311842240b00382d140e0103244101c00240c0c3c49030408100703884071382c40c24400c1c2d440141824 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 393823785 1250 393822535 393822551
    0xf091807020d1112210105090c0d09030e090c03060103060b0f0a0c020d142a0d0318091a0126060d151b1d1005070203010902060403050f07080a0302061801 68
    0xc84c0541d00000101894100d04001d90f81198a4074550140140401c0365003204c1402e0584101c02d2134400d481c20501219110b042c1541803600840380b03210b2025000e0691581ca181000c0b1441372900160356040c006030920100064030051881540c0d0020b1152504a241412401c41902d020841c01c0041781c0055401042c84049084004030722510310901000c3e02d44c88082800758120000204914103810802c44c0150a075030f200d403140303803c1156150274552902100b001c6100e91699843d03000034070190030080300c1348441d0410304403015001030a807a101007000c110071451000c1e207101a0102d95400d000400a45245060b89981100da03014400c1650b9100c1f91281000548a01b06c03041c4a40280d08010101c42550140d080050104180401c00c00c80c0c051400041d01c0b421100b0b000d008010020071548159682075105441155008041542e50741c0d403450042d440300e000307d001c01400d005140c0d002501900204641a0300e0340c0c143d02a01060f03495442d030284c4100c220b00304100c159a14100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 393825035 1250 393823785 393823813
    0x1903020607090b030c0c0a080c0a2d14031603030b0a0501031406040203040312020a0e0f100819112d040b030c0310030203011e0c03020406230c030f091807020d11 71
    0x402703c0404c00740140869400e981000004441c1c0e000c100c600003841415295204108500004501c030703440b000c01c210900350888020300c1c0d40a0032050100211103440c0050405405034000c000710a010340d00c90341500d6031070005608030f4461007031103010000c3c402c0015860345416801180d01c07903c2410300c04110f458081c4900c5c120307080a062040402c8505049404600e00509485032100e001c81e0500651440f92a0041c00c03072a001d040792951008201c4032001c0210707140c100c0060022219589a11003c00750740303070f000202e00c0c20b013400301c4400c08000040c8030708018000c075000d031001411028a1612240240407150344001d1120200c620124404401030ba0300780100c2d883c211002050740c8003411100940304c00c4504d2442004103241c4100010808a60448080000100c0450721040e41d400f0700d50342c0b400c0500c600c025502440c0400108000100c1040c80544444441511086801114070469204281d420350b0300c04050b030304c1001250303030152240302c02010f03031001c0134191041c040001c61 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 393826285 1250 393825035 393825037
    0x105030c01021e1603050a060614030a060c0912150f0204081b0a0513050412020f0c120313060504060207051014030a09020406140301050a1109010f0e031903020607090b030c0c0a08 79
    0x7186d07a03400c611810020b2244500540015180d4410100207180c02800000d07521042240b0007800070707840303240e0400d146000e00c0c81d401c002c007907450380005040074501d09500c0514812802c5004646008035405800341580300796001c0d907000000600c1180d60b410b20562042d0740b600c800c1580071034449400306031a11504c021001c00c0725100400300f02400d0514221404000d110841e00455002000000b604440001d100d01c4000c0305075038000c03604803200c1826040d80700301d921041d80c4a0380c5130341c00034003960b1010040084a6071503080c0e801042d29a4104454070095500c40000540c1c500b542e1008024500001c58020301c0280001820300d64542c0400c0a55005030b100d541000040c141610b5641020f005142e4041310300d000401105e60452818507882c000c10038083c0c10007000b0340c4094043c80c09185c80704030300c080050403076114600000b6903008400c02032a00310014003500d4003241450740540c0002c0d0503244042a01c0c0e003107582e04241c401d03075a00100801c0b8403c0c418020b07804045036501e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 393827535 1250 393826285 393826289
    0x6010317040f090912171b093d140c160b180406030c060302090d050f060711010506090414030d0207080c060903030c030a02090d080a0c0b0105030c01021e16 69
    0x40c101150740ca14030304103c118010b1990307030501030018014016401e4001040c650340c1c0038444002113030f201040a07603500004d0088050782d503081a1a10520410265a410100c803d0121819101c80005020f40183c10000903510b150020580500ae010510f10381100686418000030084030a1400c034000b420001014907444171001090014400c80410071800703480c20078181c151403d2024030314590314504440c029104482c10141e0100c0d0f4000ea5a8440d424010031031f4014007102c0820040488040e00c1d80c070240d0b840404213003980071340313181a901805400c0c4201001008180240e4a075200e080d2079528500890a55010400c82c0741e188010318400f901c10300340141030341e9407608801604e03240781602c042c0c80c0b543c140d401030080219900c1c40c003080345d0b07010360900f401684400d181404200c2c1c00e807030080c00912585000c40d002450725803044181303030b145000314411102a607a032028503440708104400c15005810820052501d01038245d080e101a03501c00c41100c02d03a202c01d0500324070030580c2d6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 393828785 1250 393827535 393827549
    0x10c02090f0105010f020304050105160609080d02030f071b02091008151e061c0501060504090501020c01050114030a0605041a01180501060e0108220605070f080c03070206010317040f 80
    0x1006010f5541d2003030400d0700c80800c0340011454181040000382c103900909010310704520f0130a00318000c1040a80144c088554003005050300c075084641c90301c020350422071b01115580d6120700043c600c1031080b644c0d0340c10714076002c020800764403650b004e000d0f10180040502302d00300380c410350014a8000800040301078183c80d50840d681c5040403c54100713002d13007511030603100f4400c601c14001560340304000c82d0051a85120482013001c541c2c03921601404041d0300c419405803910701c4010170310006400034030038a040d850080002d0b03a00c5805040b1040303200c2045a81542c000c00101000070f9071684140d0b04075004c0c481030b1401e0507900c080d180030b01c45d0903004040c03080c00300000800007058500030140034040381d040c110402518000000c1c20210020640035180407000d0a9214041080c5482982107810a000b40068508104040c002c0204800200f0000304840d0001d4881c598078419a80101d031143d01a008603461502c810000204046080b1451502003100080400304540c03160024000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 393830035 1250 393828785 393828811
    0x90406140106020a0b100f12060b091e06030d0f0309061404110a060201023f0a20040302031b120a051f0c09090e1914012003040f02010c0209 62
    0x280c0d16003031185c0788004d0640901281c02100c140401c42541c0a26001d88421200185482c3c9150502d030014001c442c1c8030581140b80b5905001240600450482001e1412040d89245840d80070504d039480b020a1441c8002510017068000e02c1d500c29004901424000d00010450710880c92300680c08031015101110700c0d00c4200c5144001e03040001d20040100f1041c00210300f00420403502240080056041001c0140e042c5001c070000b00d50081410800020002018040c2c9006240320004007c040d4403540c42402d60040c00d0300c2049400211030540b50301a0242000310072003070300c101055401c4100e080d4044002d841c21b0006000401c0f003d8036490048004040034100740d1542550060203c0714540850f04102d864500d060b085404d040c100d030056607001980d14803620a40307080030080150324a00310741500000c0107101d1000c812006a40c64040204a80c1007950032069200b010b4a103100c06840c006d1000074049100e03101407032009070041c1800c0768000c1d2150f0010f96000000c460300071420301 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 393831285 1250 393830035 393830053
    0x140a290f031b030103320316050714360705031e01050f09040303060812070b0105040507141309020a0201020c0c03071206050c0d0207030c12080c03040209040614010602 74
    0xb46000022485085014003149503504580391800410000318820301c92880002480801803483c035032280c402404401078a403074110f4994107a9204000c550300761168400c910001ca00c44981c0100040d19900c02895401c007214021a020303105400249101c4108101c488014111208200703c0c501c641415a600d9907030307103003003076070b500c01007403c080903014071100c500040c08107448950340088407400480700d001c040c1d0350b145801c401500c082e400800a500a1100503141c02d0b200e0b030081c1c0f02c11f5200340410140c1d40e1b04c41003400b00304c0703c084903400f000900d00c101421100d10300c50300800c4420601030640b59090740342c901000913648a40032180051307600241900f9a0f10052040b010340079401c40281003140d2624580344c440700c80548020303005c40c1da030f03001241e030040114084540c04918001c0540d00c0310001e0402a02e050700c500e205540814035412480c0000e803003090500c0c4103460142c00d06080d922a90248006a030005000b107580561700c9044902030101500c0590003029540c1c02802c6843d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 393832535 1250 393831285 393831301
    0x3050d110307090b0715060b0d1109030a1e020a0303050c011503050c12010e1c021c230d05010e09070e04080a0309080d05091501140a290f03 62
    0x408103015020240c105105028034260300012a5084950100300b442c0c840380b05003000d0808203402e0268a170045e183c07460014007050004082c10411840b02c004000e4040a804160068840c500d4071070f605404c442006070004903900401c0c0d40510140205d01d0b000c4000d680070500c0d0304255001500803900200fa040e041e250b0901806520990701c403aa88a05032440c0d9441d66200c942c0c600e41d501ca01171509110805050940c049408000303024100e8180110003000c14a400d01c1d190751900040c021207401a41040c40301c0600100c00c5115600e1301d005030800100c0d416051409591990009410466842c8151081c000d4502800f10301060060070f00701081d800d481c01ca01e560118404065220411000c110240c0554004c5a01824041811000da103082034240c40b546104039881482c02c02841000c80340000d80910028000180030100c1c0d0702d4642e86141040380107040d56000300d260343c040c441040410b2a4047d540b003c1e8a60b03001c940c0c040e2111121303680018101c07181403900401040342c40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 393833785 1250 393832535 393832541
    0x40b070932030109050c04021e040b0901020c01020609031c0e1b0915011e1403040b0a05070e1e010323040606120b1302030c06071b080d050412060e0a03050d 69
    0x590101c0080000200a503202c0340c0306c100703403400b440c81282e008c10382d04405404401c0303032460164951040c50b83d940d2a0582e6031219000403e40c80e006205282d0090f10315400001e07010f01410240b0010f50078a80090341c0c5511410003a09044042c549880e0350502c414002c00412040741d00c146e030704100ca0360301c5905100198030000e0000c01c118134065900210742e41c010380980a424496480e401d41c0e446004019030f03074060560503c0c200c40c0000020401400b5880440a0003010300c43e00901c070a40381c580b41120154090600e05901100403000b4001891340040760a03584c94060601203680c2c030130310319640218480f003204c180581c2d00c0d180800c01000401c0c4100c1d006017016031034000703552699841c0c02001d110000c0c540c0c8002003007043c000003513507000c02010000381402490310b03507100c17101d1800050111444142a50480c6441c40104803007c0110707080c4008040c1c0d40d1000d05182c41d00789030414214540c038050300c480e5a9020a141d100b40c0034000c80e80954045c0d1a4655500700b1340440b4411 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 393835035 1250 393833785 393833879
    0x220f03091d06120102090a0b130305070e0a060905040305090d0218100f0803040b09010c080706020304080703020105060906060d0b010507050102030a0b011101020f09130209031f1112040b0709 84
    0x60f40c2d2041200744029601e03001080151034404417040d40358045228201e08031240d5410280041c8206140080c1d92005983e001e84280461241030000543d14458802501e07070a950003008107109020304007050500140244c096400204001c4a61451008202c0600015650b41420101204003030055080e140020001801004011072074145003108840141c081c40402d241000000c00004084c0031455007a5048181c11000c21541d030f092500d4080c10590000360b04a000d5402c110028106151030040c1c241b04e00d03c040d14582ca0451030311600002404400728040c14400103000d10380104200344080d5100700f00041002809240f4140007400141c0001c09100c11a07004210100c000200c080030313941c00400a484804c0c100903414501801380c0a004020368042c45441803c102d005000e050004021100c050704012820380303244c2c00c040d58070410740300c1c14100b0b00b481d012600090120840552200080c60038140e80381e01c80e003204200343c10301d050541a0101280c4540f1000403000c0807411 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 393836285 1250 393835035 393835069
    0x60f0d08090d0302030f04080304090b0103151a07050111041a0708070b190c020c0f0409110f060c03130509010e0712090c0506041d220f03091d06 64
    0x618005540c9090203842001849800380030780320071840400d8000c000340d44902820700e1820b51210340341c1c900141da03030304203104802c0d0385418110000f250394041e02c0750700341c107080400c41a202d00d070500d4070100006801c2c03003440c4640001000b051002c110203200d400b06141014440b96500ca20302002e020750703114915201c0401c01410003a00c00000c549000b00d407075041d882904912141d594130100501e504000c00300301c0000d410084150f134083d90200f88200f138801c00b22241d0000701504e6061004585070044000d050107a20301d400c10b114034200907083c54602000700518941340101d400c01e421074000094101050900714000e004500c1d0020505025003894800070b45d03d4031303043c1c000030030055110a4054903650340da07403240184003842d030407a4007400c1d0140c030340d55489617600d928401032584404a01d65150341500441c113440944081d613540011024841c00c50324000c1d4960b1503112011160407414003200c03900000f09131000d16885034910050504845803440c00e001444500b51994030707804 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 393837535 1250 393836285 393836299
    0xc0801060621110f031006020c060706050907050604030f05010e01050c03010e061504061218080301031502070c030b19050603071e0801050a0516090609120218040308060f 75
    0x10000caa442010a03002c0700d541c140075064041514282c10003004a03002c641004900040e6084070300001340e00642c0110726007004110401d5136428104c0c0c503040e1800d0000e50144041004402040d103980009800c41c3d0f0040682d0303502c543d1000010f0761035005038000c481c40f4880c03007107040c24004284100c00079030442c074000303003e01d1403c074402c500c2c40d12050180c401172001d0400030139002d0700c42440c0d4028044a0b0085181d549403100300141403010302c500071130951424007440c01140040480c481e10520361100007142581d00315501c0114150b056051000140d50030b1200d800420303448070381580154000c601c0d6882508142c8480440019450303e03404581e410542440030716180000c0003011600e84401d00e55001c05c4041d00052490819403101780d03e5805c1405000c041d0a266001501640d80c0a50b0300d030400561010a44d1240a1403007a600807805d203038401c00c81c5140000640410b244000c0c5049a0840010071102003014141c505a000451a00410002d8142142e200c0e0842c4003c840705 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 393838785 1250 393837535 393837539
    0xf0b070905060d050717040b061507050304030809030a0507090b0901050d050c04050c0c0703050610060c050c060a0e062106030f1b0402131806151d0a0b0d090c080106 73
    0x814143e01c201d064209400d036442d000605140d11910755615610601d598101143c10103007070850012200b990b100703108011908104412806210464aa032648036000c0c0d0300b07040c6580c135461501c4d00401e2070300ea018040c1020031000160184903403405019442000076800c180078041c03020402d01600154025224166460040783c000541d4070131800085902140741d9490940c81075981c000c0c16030148891181d0300c0c020003044070104e007082c40f40441012030a1081d5944034116542c07010582e0213005c503008010b00c2141410904004c0c0600f0800d814110036044002c408150390303070b100c51141c8280440c10200d0761411440e40228a4000304c040300140302c100e2891020540f2850128601c038222161110324141c40c1c1c071150140d95000000e030001c43c500ca6a82d00c1c0705103843e284c1071410300060f440d1050205400070240c00e6006600d01d41e03520440c00c5000c03aa100104400390f1003c41c1e42c4038013510380c0080d8a20120380200380c502240c44003c901c190040c034200340300903c690008c40842e4103022003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 393840035 1250 393838785 393838789
    0x2120c04060c1101050f040f08191e0f140105060307050301021c021809040b0106020111071205030a06090606030b01021b010804150603050703120806010221070516030f0b070905 78
    0x2a00807070741002c10485a52840d10045e51117118040000b0650784012a000410141b44d600d60790486100c03001b502d40c0041c00c0c4006081c01d0701c1401c4014038040d000011351889003080444458410702c03424100b44004039503150030b0780c03140d501e8410308100e81d140c40030401203084c244840c40040000390700a5040001481c204034205d10031155085d031142d4046405001d0120403500e50f400b4060240c0306600c1818181841e01d200c1000f4060b4101540c200780c0c1c0303648203206035000c50301000c1d0840d15040403c20310a0b41141e1a601c06009155941c4d11218003003178100c05445410014a0980c0f00054035014050003e0f0420003109420000c074540f0341d010388911b076040006c50b42d100354003c508050080e181d6007504011301e0355030000b41492090716400300401060101e40ca440013016214821182c3d40c4c01d0049039508104044104038006c1b01c1c54000664081c400500001446502075560810312680340d0220750110381c1c415509c0d641154544000d210003044a50337084545481c003022102d0030040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 393841285 1250 393840035 393840047
    0x11100804150b04090204020a0f1710030b070201020702030f071509080c010e0a030b0a02040303090b1c050a1d0604030f050309060c09010909020307080402030c0a0315050402010212040902120c0406 86
    0x1d615141035140c0c040340d80c00340e86552040200d290b0007401151160110305000b4030b8200d50001c40b101084909001507461070100c031485210b10b0350180d10307901d003506541d1616120341c8040c0c82d01c020342d0340a101080059405108010701e84541c4001030144e00e1405004c041140b10f02c410442c140100b844050000d1140880d10000c004401e00345000c1504105020a08034406a44082c25180982c01849000195500140220390007a5100d40d071550312810140c10521901c084022180b00345421107104d907440303402c482d501015030140018000f41040141c41c0f40c00220401885982010b4104000c054001103000c0a00e40b0f2850224114a0104500760303840d000a8540200b4900c04200c184140c0e00c42c1e04c1c031001800c4182415920390400c014050405035090390100d1080c00b4411810100d4245410381408403070300b0a10801c1c40e074141862040c0117240241090741103014400c071019004445500a00040594001c0183d481d010340e60002e440b0100501401124034003040b04201c003d50041d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 393842535 1250 393841285 393841313
    0x50d1e05070b04020a08070f050405060402040608130212071415030f18340501050f0906030c090a0602030a0905030a02132c0f010b0402070b040b0c0403050a11100804 73
    0x20502c003850388490000964000b80d650040d0490b100e000b0380491460380f5880380380c0403030b142510148800e4856008000980c011070040c5000550600c0000d4102e030802000e0300711140c0090006110f0300ca8110b411410b19285070070035201c441d09090203048608020000754081020058928110b040000d1880383c03180b0040d040303150195a10412401c007190030702c0124001c0c20024890212416040d00603100d01d107859016080050382c43d000000c40f5400b8000f1240742d505859001e524107030545c1e04100751a00040c001020361003041c03000c4042d6131030b000c940d640949001d070000c54036110641c81c020090b06c010380080b402500004090401a1208404461050b030200780200d0201040d440c80d40c054199461502610524504d080d20b18010202e00c07000300c603402000a02c031105602c1c0900090b48034940000f0804131a0000040c0440c03400c0458982250074032000358a080e9883e01c9483c0303020f050740f90540d4612442c000c10310311031500c541600d106019a051a03240380c94140c40b0030280140038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 393843785 1250 393842535 393842543
    0x1a03012103050903030d0902030c09160c03030b03032a0102070809060d0f06141017010621050f0a0f09032118080d060501090b09040c1407050d1e0507 66
    0x40e2609020540a6025206000c2e40a421640c40300030301c00c0000061319801c1d406a02a016080d440300482c01c01c240c4081c8101511148800640b00741c200c102c0300c05521600580030142d94990300c962035074040c0300414200500340d008444141d61070310940c55605003001507a41583c8100b0180000821000544174440c0c1c00b1030318582c0742d000014507500600030911031b401c4402c1c40d24902181d0340c0365440c02e1142c1418107441c600709824286909a0b0070008495030f03501c00103a04401000080d108203c003010b0b4840031380a06141c2c09450720340b00d082e20300c1520000f1510b90b0440802c84880e8003440b640740c1100003500144031581b62924043c000c06241e0000008081c000000c0011104490304024050a801c2c40c8001da05105ca092020440d000309640c060b6080c10924005080c0d8441c9854506a0310f544054500d420b49010410004103a1002480140010409119520100440900203590051000d13110540c0c3c90a001400c00660b031281080c00c000e4041c103c071100d0b6000e400c1e1800382c0d501c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 393845035 1250 393843785 393843839
    0x30c052d0f04020409090f03110c03060105120313090504030e100503180c1c050105060a030209070309051903020d03060f0f210f050706080906060d120c0503040605041a0301 76
    0x150000c1406132103950040c664072410041c02c00200240b09918502241c02170341c41c8094000d03180c180030348a4040c203a01c02da041c0e0050005108514146403100b1106810034100c1c2e26183c280a800300085100e0ba01c840c03099603565080205040d0029074000002d541200d8100c1d28941c01c0e100900b1501020307103c0c5d6402c04440d0030a500c441010803402c100000014800c4085160300d5034030848040d0307050f104503802d50034070001c644982400c0300e21a040e242c0c000e01125030350f51005001c600410460b4016100b600c40e0301c2d0a021076500c14800981001c1c003c0e406810510b440c80c902800b81d070150b078030002e11041c1c403120802c07140000c1c5814500341c4503420104440d550510310303041104e007032804000c1c014004d405154030401600043c004111455a01c840f5481d41e1400700c0d16171070302400c64001e600700481e6000e0100044900c00d105e0301380442803d0050001c0025151a440e54000b50484d0002c1240000c0c1804804403440c0060000d00d031805445155606180c1900b10814400b80c543d620310607 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 393846285 1250 393845035 393845059
    0x902120f0f0d09180f06080106051207050a0303050a0c1e06050709050a090209031c03060512010b090606160c0b03090f010203040507150c08030f01091415091b0301030c052d 76
    0x1d9a049840b071780741ca044040c414581c51758103081c02408188a254400e005a89040020f41c0012910200300c41c0000d00c0c00900c02c0c40c40d28241d520742e0020fa03d182c100034060402c03500150170080040d01d0340700942c0d41c2008050300da26101c030890780041c00c038009119200c0b404001035550402c0f00d034241c400c035507000345e1240101408240b0304520240e04c6045468013450541e0143d90607485a01220030132210440f1410100c1c103a94200c0d07000034482c2d50415554000160181000401032030780520300001e00004211a80726204492100c1e00110038010b400000d204074850200058032070440c03542d000314510300305070352801d07541c2810b44120711000b515021380c0c90826008030b03001d02e00590020f4101d9600e207400c4105090205090142ca0100d62501003260f100031030a0007000d101d0020281da040307183c01110b040100d18540100329008c0c2e00a5040e048005402d444d02441c000c510a406512a00342000104411340c19021b1600c0418000506c8000c0300c407850410a02d43c000054aa40c81000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 393847535 1250 393846285 393846329
    0x50d050903100f020c1c0203220b0c0c041d0a150216060f050a020a05090f0319030e040501050612010e071e02030702010f030e030f09040902120f0f0d09 67
    0x35602d50110b001e03141c50090510070415468000301003c090752070540300686410035620722110402c550000050340701b40981c003851456140c1600902000c1c00e968800150b548003c03c0170380e481140c9908441d001074031512960f0030540111040c0c420411150700c190060401c2099861001c40c4014081984940d2040d09481d0b0035030454200d9000089244840c0040381001c0c0e01401c00000c46490302860580003035281d00d1a0700c244c034842681c2e9580c06103040030980801085900350501a0b81c1402101174411029807040e001080003403090f2202d0500c000a103080204942059011034010b03041001030a0b4414aa0060302c0e0548004d003001000c1e645848000711a503410002000341c4100c81442c017050040e40000c0a041c2d028801d980d108040144860100d0984422407814500ca900900032030752807401c610064035500e980500300042140c0d03160000f482c410b03000d080070019a00000e04c6120180002d02160000740ca0110045c41d24241e94207000b00004510300c82c0c0900705040b58441a410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 393848785 1250 393847535 393847543
    0x12070c03020306090304030c15050906070201020c03010f1a04020c03160c0b0a1116081018151b05031311010e030106030c061805030303011e120309030303050a09050d050903 76
    0x1558002d4225643c40c0380080e08142c0d42e0303219000603240260304100008507000b03160000191503556540d41420080d442042c80016000941d0485c154015045144103170385091080001d061040c0d100492196661607405042100b001d10690003680100104410300384000b04680418004019100c485c04160070140e0760039030550004c07034440500142038034900313500c08000202c0d0341e1441d00303444500708810240d4180c101940302c0d808840e007024420180c00d42c520350040105101c4000c29000031074044e41c1c1d1441c0161910002118190313a42c6004804c0c501fa18101801180c850408514604000c031480031011070325100105044441440c5c4802c40e4840c0074000320005c0d010300280f000da61607140c024045843c1d80640c0002980e0711400c4e8403011641c00c0e20300300b00d580180c05140b0710303402c1208091084100300c01e001c4070900c6041c1300068402005105a01007400790b600d5001c41c50542c6001000e980f0050a0040b1250a042003440444d9002c2036400441e503007414425a102e030070700040b03420 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 393850035 1250 393848785 393848789
    0xb191a1204150612050a030809100f02120105010c08090907091e032603041203061d09070e15010e01030b0604081506060a02060a0207020613080a030905060c12070c 72
    0x110035aa0024032080081c01c42d030390307070040142d20381c203010294480308003401d00041c045010304194800d040c540f000c83d006a0300603070481183c0f001e5840150b414040d44042d038003a15000e2001710750001d00c28001c90300015501d03016081c00d02e800c0c08134050b180c681c02c1c035600070003400501c035100070700200c0c28090080380440000c02c504a28100c484581198034943d041151206840340b14a8050071440e1080150b0340703610500c401c540d518196115621000c0c00c4580c0a2203040a06541d40d42c046a00c0c40e0300c41c05081d241c00010304013059413800802ca5403c1480300e40c00600000a181c0501c10f035000c030260005512002843d020180d01817a1004801074062640b2042e0007480c0041c000c00c40d0320010411060324010310000f06403075140d60301801014400c01c0700c04401600b00201203102c04040e41c004081060004103054105441c00700107121801d015072008100f0b6005280110401d41c1200e1030384010700040f1846418403242c400c0352611030540782d24000001c40000f5180040042c1480701d040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 393851285 1250 393850035 393850057
    0x110109031e1a07020a060b04090506010f090606020d050a0c02012a0204060b0702010906110c031b03160e0105010507060f020f0918090c0904051f06090b191a 69
    0x20001d04030000008104040200c00e0300c50000328403601000381e94800c03003180030b40c085a0080c64100400e0f110070f002081c001d0031056001780c490f071039000420010007000d400303400c0c4002007002044c17a105050003100e101c0d910080540d0010040c0140168020094070010b281d24245404510003c0c40121141d220041e041007144103994208404c044030b868288002520076074040010725151401c5140e24043d00b10000d0010f0144d000034055940b045040c5c2d5240c201c0c00e1700b02c138030010255001034202007000c04900ca0f1403600c00607149e510300c0e00b0405400f00001100020303101310300b0000040c69102050041c2814030000040c001d00b08140d581c440174500c40405021525584400c1c00c10b4295800042000c1c4240c101c00341c0140d060001c0000f103030056014000400c00301c00c0103002d1145443c8028001c0e44c080c002c0088001180580c0b5121103a60000103400180b02820320581310700320b82019a80c240100800c0080b1003d907001d0707480b4942500e80602140e040107c1c07240d9250312612600d9208a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 393852535 1250 393851285 393851303
    0x51609050d12230a12140a0c0c14100506012d050c010906140601090e01140402071203200c1905030705030708124606030503040e0115050711010903 65
    0x1000420040040c0101010b5a69081c181c0007001c1882401d44030311b00311316204040c1034804038850004c680c0c001c0710804c44c2424200030890707064580c00100e190703001c0c0b090410340102220000464840c0b01c0c25034404001d090111140c50003c82c059518400c4000041081c00d00c6042c03d180c03540601d09075007540001200030f0140711f030241f4043c0f000d0440c410013010f000c581080400c3e013039805900074400b6a044812403900e903031320f001501089031942c007082c240c01641c05c020b030b84041140390207400d440050b1610085400b045a2141580c2444000d4080448100a01144040c1c4034040381004200420901039041c8100d1810054298070690705c00501034170000410101b000203200c044c1840900b02e01c590102640d908031041c080100007100302c14010f00840d07504070404032683c04d01060681c0c2c0240b110b90550344460f080c044030a07607001034420b503001040c10080e0741c045901c2140034041c28180c40890bc0d240110160407030041420080002516201140c002d910480c418001142c0003401c0c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 393853785 1250 393852535 393852587
    0x40b0307080619060302220b07060b0a030204050405011b110a111807090f060f0e010305150a080703020f0f0108070807021c0525020f120a05010f051609050d12 70
    0x11780254081102549005100d140b4680403007280c1d22540300b218107407455249405400e5668a005100074008240c0c400342800001c00540c4840c0b207428410b41c4964000901c0c0c0702c0078140c0030540c06500000e0410054035421002c1c801c200440c0c203c10640c0c0c4078a00c9100c46000d407000033f07148503144500740b541c0b402510422895550000c0000b089601032180001d200d9142d20701142ca43c2d05012035100480d032404c00700481035200707510050b4004071340d000c2d0740b03000004040010300c69042070b4000013441e80140e0043c400c1d461f242c41007030b21041d012a074401022000c000040d15044000707140c1024842c080000070302c40e600a021b4100c814040c1c0c900400c14100503080030344140c001c01d003c40d03468101c0d03180ca0300038040d00030944809190002d200000c4c0f0380c883c0041001403900c10946007080c3c0101c4000c080000c034240a141d00c0c2e65120100840e061a00d0403800d80b6841c0f61031200010050b60f80820080d41d11880320022100e500300a50500d21600c20b4001d8406001600107503101441d01c07170745 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 393855035 1250 393853785 393853787
    0x170408160c03051b0a0803120c0d090c03151112010303030507020a05030703031b08100b0d11040f140303070b01061d09100905150a05041a10030905070b040b030708061906 75
    0x10480c2e81000305c610b15425078a40c0e00700ba0b5a40511020f805c1074104c1d16001c2203c07642c541c006000c01441201d004035811740389a03140c005400c55648112007006080c1c0c032002c11604540100025148008403082c104504000710640784e030f1042c400a024540d958000c6221b140c802c0c4100e00d102e942200451380c0d560881c2c503004008001610a462090030741c0050584042d1140640c0c2c1d00802200101a1415060408010550340314a2228400c0740c6e441140315144044034018200038000d045540c1800c505d41503407000d64215554401d4461741007001140d00107040d842c4110f0568525290014196140f0024030200c0313400c02e4015984482e0101c204154060305100d0002601c0e900981030110b40c885401090208407008041648920010400e0045080a5120492140b500048041010060000b240d110710180440600003a00c5d1034903042440780400900000b0400f0f0320b1568642454070b5a42c4500780400380c8074004110603070b000704100d41c0e5a40c03030160901080c00c882c6801c643d50303410 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 393856285 1250 393855035 393855073
    0x60327140a08160b07050f031f09062301030606140d060e0f06042a0c05030d050115110a0309050f040b030303010909030305160207030b0414060a0c170408160c0305 72
    0x401215211504c83c00204014460b0041d1038020300480c00700e50443d243c030210080764207c5a01d1450304802d440100003022030081c054040100b04000380c045040810311315120701d1607007240300103050500300002002450f5200003841e400c2141080c0080d11980548202405000ca0764007a010700c2400d2021b01c409103417042c0702103009800440d81044083c00705000d4185200041c640c2609400c0401004245680106100082c8620402c240d03403400010104c440220b41c3c00380c012050024658844402d0140c10840c0f0560f10300c134000c0180ba4440140da8000c04aa90781c1c05858007580c0007026208094440d40c2045032000070080030750f9100c2da140c09100c8004d103407004e016800a07080c040481d03c03030840540d40318001c000d141e016081240c25625160307441c0c0c0d0050700444d01c840001a1220703850200b440300600550044130f0201c3e58080383c1000400c42c0c822240c2d40c90301030f2684401d10000562a030100c90264042461460506401e4281102c030b0002c2d0350f00140860144140c0846001c410340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 393857535 1250 393856285 393856327
    0xc04020d0609450b0109091502180f030a06090b0718150509012003030709060e030c040b06040509010b0301030215041208070c050d050601060327140a08 67
    0x1601004040e09041940700f8015192400d00801810191003414000b082c81088089011828403200402c10558900e01c80e410241d1081c441540d6a0200f80200500d1200c1c044612010300c000790f04001214021010543c028400c407482041d0a1042004a0302c05200345021250049400c20070305ca202d017003080b0260011140000060481e00c00c651403149002c0203141a030301c2022280c2400703140c500c230581c2d803a4010141141072004041c214140c654a50341000c80c0388103407002564480c1071401d0054002113040c0c010b40c1c280020b240c45244a510001340c4102032880859012583ca01c0c4800481e129200325000660091102c60001c6030040c885001141203a200352540700e0000b00c401c01803480d0340940c0c060140c20982556801d40071a00b21b801070000310340220a050710403547d50307000500300010400b0481d0310350800c0f00100411078040c45580c1010b280030b180c4400048080540360451801440001c00e2544049010300d074036201000403a0303410341e00c450307116540e42c2c040381c0380302d0103680d11 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 393858785 1250 393857535 393857549
    0x106032a0206060f06040b03150402040503120c0c100f390c0503030306030a0605041e0609110f03070302040905031209070801150e0606030403030f0c1214040201051b0c04020d06 78
    0x1381e0f0b0b40342800d00f0545c04940031180a110b240c0e04503203036403038041a5000e19101c119071183e000e010100341030303a080c0221303038000d40070310941a40c1d09041c1c11024100940c010020b44503164200c420401d20b03400241c0d1007441801c6c1e1418090fa1192030140482035a0601c0301d121808004481c281d2800d914449820341040c0524101d813010b41d9288101039a03413000302e51464041c0c1081d8006030000e602500f1060300903105200c00c103401c841d00030441c100040d650005403075054a841034401405a240884c80740c151041e2140d0480b1111540070927074514051000070300850b6074040d9501840390500540300c90b003c1488001da0103003403607030701565140c005001d02591035207803004a1160000180c00352044030f255000d14111941c40c0f10803c07045410060056081c1521110707850185a82441481081a2992214800300312443d28034022580700f080035000140304901404050b0380c000341035070a8000201416800c400f0318440070f070b090016445401d030304940003040349a0f010182e078001c142600c1c10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 393860035 1250 393858785 393858799
    0x10308030103080c1f0c110303040507060c030e0607230d08160c05010c021e06090c040e241005040207020d0816050307150f0b010e120a0b0903120117060106032a020606 74
    0x30004074503441e448140e40c002c0036330344200420807a050043d00c6404001d03000703084c100003d03001c0c03d0100380d181e404880c00b00c4d064010350f0b0710010b070005100d00b00c0f0040c0c1d008100400420019880180603204054020081002c0e1090701000c0380d440340039501409a4004000d210a448104019541e004115005d002c1c26002020509031181d0000c1d0b4103200c2e58041c00104030100b804001d1000400c0c42040800041c06164260140c509111241450f2000c80b0784002501d450310b496800341c00700c0310f034019500c120b004004000150ba10302c0248603186410440060341c071060001c0d00c0d204200c0c002e038010194000411003500b4010603001e2011012141d60046c40228110341c0c00108840d030710f8000070f000c50038640039080a8108070300300740000c1c442101101d41641842c6c90340c058001d808c035003645440d400040c1c0c0740c4d11603a81c10442401090801156008040310440140d195581401140e080590301d0000d003a030010054161134010b0220551200107075403052009444030001ca031a203026105d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 393861285 1250 393860035 393860057
    0x51e061206030c030319050f0f0a0207031506030507050418020a031a06090103020306130c0b041e06030c05040b030a201207090807090e1c02160905010308030103080c1f0c 75
    0x18048219814a928200030381b0003040070550a644581003425903200c032000c00c9c495401003940c0c4800410765076502e50000d100142c47d5207050314002c032541321000c42260801c8000c00001e980010404c040d14021140414800d40b551030640086001c3d400203036003d03d000c0320000230b00641941e01c50741040e50421441603a41d4200a1085821003844003d40661000000560b000034580c600d60350716100741d5102000729911b0081d2001904150020182421039003102020402c003185d040b8010302d01800c0502603003a0401001d1f04c117004620401d42d800c0781c00400a050b45a00340c2c41f100300c65120721001c4846c42828002442c081d00041c050001c0394a081010a075010f014101032001c40303950740d000f050307804d00302800307600030b4079175500d4400c45803003115400e54183c60305402c0d1821490140d8010050003040a08105e0380703070380035030041500360b00d401c00504c045100d42c0112819640c0022341c0c0d60340c41c20220348031441c000e50041c030b144043c120810100b8201c02c16802045403450a40e40e00700307141d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 393862535 1250 393861285 393861289
    0x918140c120a112217030c0106092c030d020a09050f010201060b03070c0f12080702101b0e062101082109010806012309011103070507051e061206030c 66
    0x3d0504080100f000e10280f000b82011501031200c00c07010360112102c10b000300d6aa403804411007921018400c103035000030800d9064648248156002803840203014070881000f00d80010703c52a07507640d002d803400c61090120051010030811a0101d1a19010856071a8003000d0700420300317074171801024803030408441114079540c07050242c18240c64503d41101e2131903c8015090b52201c618103001c4462143c000080b00c04604001c003008050346440d02c502500c4e103440b803c02420311140000e5982c0e21880c00950841d005004800c141010139142000401200d0000010b42c00e4050341c8000d41c641066506020255001c1c400818126100c0e5021104c061103040ca503192510248408207511002c00d01039400c103903114081e0b45030070080605090002000c01e01800c0140c181020100c1c0c900c45000503548072650b44031500d84075910915025600b0203c25956140e00d6103160b100751445150b03089248405802048850380c0041001460740b80d403080780b10744e1483c0d000e00c2214242e100340522400300f4154 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 393863785 1250 393862535 393862541
    0x120d0204091b17100308040305100608070807290c0109110402070807080f0c0f0304030201170f1f0b0c0609070b0712030e0a06050a0504020f030d0918140c120a 70
    0x44042c0d44490100103044a03030f006001c440280441c1c40000f40c0c0c0400404107a600c1c0082c40614050f0000d080040200004401640e000742c1c04008203601c000e20801405401088081c2641c48036407491205c08000358410003415a9080c84c285400000a500c498000c0154868064548980b812647c0c98006008102c100e0050b50006848114108800400101140c004040200021a889062010b040c00407894600d0340c0780c00366a1a880090140190342c0c11803042d400241542c00f88008030724102d10300700b19104010b85052000070070711a41c0c1d003071840c08c00e8080c0c003c0c042d40c628075600c03141100304050b41c5010a80e0382e03900c24003035048041030031808032040761031850f000316a004440700181e01c12002031002c445411841d002e6148180001040c50040d180903040d0200c020495082500400040100080b100b600c2a40940c0140070059040200002103903581c507803070354007044496107200241a00002c07681d05000081c04000300d120300c80c0c001d0040c41d04138178824003032076560300034200c22 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 393865035 1250 393863785 393863831
    0x70203030907181103040312050c0403080706050402030a050316060e07151d0d0c0602010b01080403020c150f0a080f0703060f3506090f011404080c120d020409 70
    0x750000344052241500f9158440600030032903500003140001a101001d86400544088000035103081100503007910600034160030644007002e040c079052459550b00701d1840f60b0351004007038544500c0020b00307550301800550302d06a001020340741c0e0f95101a80000340344641e45421a1668a8124200c40488000443c20306a41e0469580d503086014900c0c00e40b10922034101c001c1d401802d00a074154251070f902403da000030b1241c103600c00d1003800c1c407402030300b0b46510001f49810440c80c1c404200200c0d900241c2c0d010814420744e070003400d10041c1105c0700103c1c41500601402044002106883c5661151515216102c4080c2c1c20810b5110310404400741c035664441c603502101e6144040c080c0041000366400144240030345200b18152030b0040e84000e84244c010b000c25600500c00f0410104800c1c040c05012080d03580007008540346220442e1181c00c8086d0001e0a216404591781000100400c982d61420250f500901e8035075081c24807620296209005072a80c40c0e0400c4a14078001001c8030856007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 393866285 1250 393865035 393865051
    0x1f060b0304242a050909011a04030807140105090601030503040e0709051e090601030b030a140a0b040c0311010f0f0e0406180b0a050d0203031e04090513060507020303 73
    0x85540c80316103828003011140ba010340014070070b00700726041d0a00c0510414000d49402c00c0401c455541e84a24400107224a00b0781405003c0304125914050f9100180f80c0e05550076003000c191031098490001c94140a59040108099000103e1000b407040c1a0503182c022030102009111030703038501c803100d41c413141c080c4401000c0f64003c0c03000b8001c0c0d0340504000e070f501204a103403800c9119541c0c00041c5404080d04490b0303c1250030208050002c1c1448840b4562112080c2001e0007103401c3c003070109940c0c0340d090340050208018003208121842c018400c031045280c00c4940c444650800d81407004140c80b20384000c8610800d5025280d1180d40a140d091b03a842e112070319044641c60401c502640c0d01117800c00d010764001c5d540c07400441c032441c40500c84009000c41450009404c2c21078818004618055005103114500400070580142d800004a644441c104480e04004007202224903180b0701654000c08031140c00c1408002041415884508415028150078050f94880d681c0c01c2e41c40744029940c0c1d80d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 393867535 1250 393866285 393866287
    0x204230904060b01180605121b070f0c0b0c03030f0708060105190c020a090b01180302030c150c0d0309051501030308010506070f06020a08010612050105090f040f05010e1f060b 77
    0x41d01040d02584442d58049041c100480d00c1d800d40301c1d140050b5180d0341c02000104901013411140381e4031044925521011562a0003500c1c800b02d44260902d02030900000e001c503051001030000c000c4807101010007400d01031621a21a034660204640340c0d0021a40c40c1c4802e0b88107000181418403400483c0e00500d01070b111180b03011050038660340342c0c62051060000b80401c0040100044e118000c02d000102004000001e0b050000e03400185181c1422800120501250721b0074000740e039010494903d0241c088984052342013051000c0e84072405501044070080c0510165070140c141c141e0490b000c1d0324840c070142d408140e0700400314020100207010180010b0408401480b150074090f00400340180507403102480b0382100d035220016a807040e4100f4000071503243c010819160010703045401041c8001050080b5030516000c01d0011600810882d80c05103001c000c601072004820007100c840e90060000d09c00f41041003092a500c2400314180040d55005411000101c0c5a510494013030b291100811 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 393868785 1250 393867535 393867541
    0x312041706010303170405010b030a030206060f22020c0a050111070303060504201605010204171509100510090905072303070317040e100302090c0415030c1101090602042309 76
    0x241c2d0045d0001d0003200e0540da95411410b041d41e003000010342c49132080d070061015150080c00d0000d9070400d404070602482c0600f5590045030103034140c803070401c00346060040e241d0915400b114a0b060440e080a4903075403824903003500221443c401003040d076001c0d8400b0700c01070b81c0e90340601084565204004048111003070641c0c80c00da64440041c04001c800d0786030111401040d48686089a100e030340202841104039945060002050101c034403801e50131461b20015107422800c040d16101e8107184035411503a40c00000310482e94000544014181500040061180c9840c0141d5106828010f402210341507100000c00700020402d8041780714800b0700544161403650307440c407000240484c00084800780c10b0101003140c1c0c5074007104501c10754031a41d80c01004d03455801846035410001c0e00041c1e45050401081c0400011001c1c12800380310103180000700090601d404942400ca038140015980d400c0c04240707018403009130085c0090f03800c015101c1c400840e101100301ca401070aa11100d801495201c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 393870035 1250 393868785 393868817
    0x5030d081f090203160503060619020304091b0305090712030c080412080a0e030318010507060f0c030914010527070b0d0912021513110312041706010303 67
    0x10068206800d1072240c01c01c0070340d62441d2144602070381c200035102c40d404402c0142610000c1107a80102500e401c01903d0343c2800c0000c12500c0c4a00100d00445000f1600b0155002e031080085400501c1c00034002c03c2900c0442c0803540c007120074600d0500010b13041c0b2022482c12900851480120b134604958050301c540c1c640e0741503602403510403050300d0381401884009008807000c2490b000c201d01c0303078841507a00c10801c0c50103480c9814021425009074005d02c00201403d4400e2844842c4035002d00704192a80740d54640b50020b0403610700b0313162506040541c505103071703a01600204000d0744540200c0d0004809030030150b00722501200e41002d0328040e28020b04021074400390702003e402d80103051740c0a00c2d48441c4821520381c4001c0d0400c942d26a190051014050307000680c104c1c0d2030040c4003604540d100d030001108030340800b40c4007580148000b2010301c10060503020306a038034600901604c0e070307400c100040d102c1190028403c0d002215407903855010f941c000840c10a050301c1e41901c40072003080c0d203080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 393871285 1250 393870035 393870047
    0x70e030d180906090e0607080903030408160203100519020f040902070f060903020606090c07020f0609010e1512070809030f1303020319020a1d0a18080c0d090f05030d 73
    0x3140a040e401c440000c101d44649004800c05024444401700b90500d24000441c03601500524000800018006200c04c0207404011a50003a811140040e12070007212400c105100c16040020341c940b00348400708803040015000a441101520980101d040040b0340b440180d2090840c11404c0752820003080c42407864603400781140d1400b54401d148900411f070740e00e070300f1a00140c80980160b88200c04001252a00c442c644e548800d021b0405428403031150b020030402e2501d01c00ca148500d401140314819644506200a8541c200600c204d84001c41081388d80380541c41440d02e000c2c5084024002400c031401418094040e004a00003503261021a01e01ca904540125020f5a08034042c1800000565410044000840c0c0703d085448d4181c5007078810001c1002d803c6d400034013504501a1050700000b0603400043d40410740100c0030881035002801c00c83c07480425000140a480080382c02091440d00168140e603504290300c0303c40c05151180d10301c00382001c16100d02503040d80880420202c5a100380 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 393872535 1250 393871285 393871307
    0xf010c05090904030c0203031321050c010c1401060b0c0c06090915041b030c030b0a0f03060902040603170a0201180b01060315090f23152214010e070e030d 68
    0x8681111401031503130000b0300b580c9c00340d81404980e0624540900a0700140c0500041c0c400241c004000201641c0da5290b45650302c00a14a040c00000d1003848184003d2314108020484540c000b0007541340c0700d54030b030915034121602c860603c1c4500807041080341041e00884d040d83e07000800c501c503640d40ea4060740600040821006401645558031340810389104416041160280e1305e0108808010303ca000382196202000386101c0c14464100300312940761040d500342525040f8101241240140c000f080240400d40d00003040074809515000c0d040112002405501c00180c7c000d0190001009092000051041d00a00790f6815480104042c034040da00040100440c1105803038100c1d55400301108546508406000075911281300d6000f04440c03070550303003160404420f094124101a429901e15843c0c00c00c0300d41c0141c801c0d1904454a030080c0c0e224083c140e92298060180429001206c81e00c02d10a215042806022402103140c2d54001c08134801080e0003e0001c0150a0070000101c40e1041d2803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 393873785 1250 393872535 393872537
    0x10031421250623011809150c0e0d0c171606050d0b031204080d0801140f0d0b1003060c08040b04080a0e0901080a050d050f0403030503070e12010e0f010c0509090403 72
    0x80d401c886449007001104090003074007003c249880e600d000300d599060686160440c03160f40c60300c1d20060005954440c5012240340c4100700045560580405941031140c20507416800070039000000100050104540e00307071241030801c10200c0c900500410f50700d1b1240305110718411006c90041c081148030342c010b03110000d802070b0049040f420500204e03081846004031400e2030607001406200c0d8420801c020b11700c2c6155442c081180d036240007000d035158008044028400d160a9a01c01603d82d01e134001c00c5411a00500c0c440d07524101000307001c90000d4075100445040341400c210703615440c01041c00038400c1d60046480700159444e80d58060742d69112007498001d010844150341e2503615800a694040c0200e40006c101c00100303403d0862801c82d0035a059000c0010070029070517031904280a8904803a03050412130345070703110060191810145154103e41114490701040300c580c0c0305422054200111009076606201c1310712810b800d0b03640d58400203020560400202009080803203070103030f00a010b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 393875035 1250 393873785 393873791
    0x20d02100b0406030204090605090d050903060c0d0608060903181806090c1c020c07170304090f110f090a0b030c1206040e030a080a0b01170f100314212506 68
    0x140d500040c210b64047d502035038095510410854031721420094544241c1c001d0a100e410704009100007980d4100c0140700c810906804038034940210943d401101c007405910081d6003607468007091159603500b01c6840d0002c605100e111541d8036040c5418142150000094100070b5a5030762800e000c0f40b490081e09102060b0010845018031a117950200907402402441c09a610500d0380851032401002d50404800080005818002010300208440450b1100030002c150310b80c850b01540d00805041c0020155460000b503004015000074004002c83c04046910300089a11040070f00b2450104031110400140104999948101400d03000d5501036070081c408201c001201d00060704680045c0300e82408914810203210a00380c16002d11440c0032820711305800708441d0f0f0355813084582000f52501121019020100b8038120103001070304095608019501642c0512800072580c80ca4900e14060301480701d110708500401a500899140b801c0b80c503900d9010b0791201038000009140002c0484245030b0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 393876285 1250 393875035 393875039
    0x5060f010c0f0807260f0313020d050f070501030b040c050306190801060b0d0e010c090603090203120403060b03150601081816030305130509100519170307170304151112090319020d02100b0406 84
    0x4810482c0907140ba088338003400602d4500000075040d540740502c2d080c425801d0a8100d1942ca43c030038241c9600600440301e0301502440344103200031044d01d07030b00854030b01c0d420044007188000921000703180c1c4100600e001c210f004420013980c0e080302c0764074142c000007c80c4281c0c00c0040900c00e030030191130300d0700007420340d80e09440c0c8480e04500c0b98443e6004a94dc180c460380b1603c0e0f90700d010300c1811949403081754001118902080000c2407030308000c1c80031203801c40d6007060607200b41c070804c4201c2c0040ca4a0140c14051a101c1c04c000d000c540001403030018000071240c020685040802d00d49020709841d04419031020300344000c018005100080c060488620846c0024074052956484035041d02424003669441d00503040800a149650300e0003e03003c0c0003003050000080291400550300312a0f000e00040c020701403000b07000c039481081d16115900d040c5a06005e40080040000c100649040354802d400801c1f0400c281d882d800c500840700e0241c0c1244a00034651032080d000b80d060340c840284000381880d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 393877535 1250 393876285 393876293
    0x10c020108040b0a021c0c11070b04120816050f06010f03021809030909011401140708030414030408030c1606020d050703140d0f050a0b010305060f010c0f0807260f0313020d 76
    0x40e088500b10815850f10311042000381c002c450323520000f2240c00038145007070910201c901c3c0d0303216601ca10340e400c25002442c1e4041c801c440d07098402891001071502001c10103400d105031b441e0101e004240090148100025090084512405c1281e45c0500642e41e80c0c800d07001306421848008000c41c6840c00100014106c41e41c42441450190180e0703024003140159420004003000003040c0c2c84001100c040081c1008148050f003038950069203e0503a2a0310b21403401024218050380c1c1c04000c01c1d101c042000c0200032008168820f20310032039400c801c0e419503a4001242c3d10020a415140031420030841a00820701c24402c00c0c022000d030000182c40c0c002c003070b0340c01001ca50341d03a006030302c040c0e0343c8100b0b02884501c070b0300070094040380c2480d080c4180c1c20040c00140c60036003c3c65160f03050103407001c0450204803080684d480d985c0d4000d1001c41d00d40e83c0508000100720a0516001d42c80b0114101c11918129091f0644820b200c0c0254910700b10399500803000341c1d800c0800d10580c0c0c040b08001c00c010000d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 393878785 1250 393877535 393877567
    0x3060f09021e0a140c1e031c0c0813020d021003020408060603010207032001180c0311030a151808030406020702090f0405070608090c090702070819050a02010810031e11010c020108040b0a02 83
    0x981614011907036542c0032620f9403409800884054010b5040c03070040989d043d070044101d60021450a1000026074a0b4800621075000c0c000d4000d4010222001d080100c5070103a01500031a50713620f00741e9243e6034501041600b02d1142100090200f00c0700038003141c034407000054402c01240782c2400000d0100d030311103d07000345c02c0d05200112080030340d8440510801c80c002004204981090b4001c0145d04c90f00c4d41c80040c4d1440140f003190089541e089009540c0d0041d8182c1e065841d00220110343d03904090600c04080d50000c28160f001d1040103011490b2074042030709042c49550040c0207000540c0c14900100d68401000c1c00c400c40b1407240c040e15101940da0003003800e0142059400904415281040741400c003100003d0b0107008503258584200450004548040c0f0264240b0b00441180d0b00c0304d02c0301c69411101d410250001000b4841c07500c155070007500c00070325076002d02d0b1410f030310700148401180d000d01f072148000e00048a080c003280c005800b06040d0754103c01061005410700d44002c40f42d580f0b0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 393880035 1250 393878785 393878833
    0x2403030d020c1e0c0d032601030c030203060106080f010b031503010519150f26030d050109060e190515060d0617071a03040303060f09021e0a140c 64
    0x2c150840c5003100321648401d0724480380a01c010000e851810020400501558510040070b010b120752010310002d103c80880303242d840132101c1c2c011422070396101d060030701c25075009020490280c4944070010a056018548080c442c0080140a0a580c0c2c2050140d0f038441c0c201906403038180c070600400d00943d80e82030090a10980307005114400384402030400006070703a040c19415245600c0c0c2c0b10103015400505240360161500c150001e500d4200800724641d000034415480c507558000401c89071207020403600725038100ca007894414840c01d92190000254484281c0d000b1f0380c0c001c2c0c0b1819102c1c50994030b400c80384c4d11055500740c540080580c0c001160450303001254000d0140e0341c4840c1413002c00202400800c0c05034090008240c440d0906078001c0754012041400300080c88040002400c151103a085100078003548001d8904240e032301c114401c040d41103107480e010483c1662a0910810380c2100507160700003196510045c00419001d1045c21643c40b0b0b079814030b070600440b030b02304014140701240030030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 393881285 1250 393880035 393880057
    0xc020a050a03140105061c020f0f19140906180415061203031b05070215130306021801031416031d060103120914090601120c08060a08062403030d02 65
    0x29003d00280c0740e850071190002c3c14548030364240e620340240249240301d461140369064540400b0301c5000c4002548407020b10700c01c103074003510440031401201440e00803141241c891102c00e64032410042c0801116a804860003900405201040c1280061410956411901800302c030104000411180c0c1d090305c1e202d0300601c0c1305c2c25112455004256040c4600d81e000302d030b030061074144540d0080006101d44104171029200b4020b2002403042d0b00400d504403000034440c000c00a03072190f41c0385003000c0a50003a200345224200100c200006550090081d11001d0380103c201030025903c0340a0790441040140050b03041607039800e5001894010110f004403680950001040d07290701d10f140100b02c540b01e801036501048031909040080344400c180b00310160404980c6003889a40d0000121600149170700e030000c0c620304004414a2035508414211701131082902d05c151900d854541d11039444006070750858a1460407450401c214082084000c4100001429240380a10041c0e902e42a43c2015103c50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 393882535 1250 393881285 393881303
    0x60a050a1209030e19180b06040e102301020601030605150a120204050c0f040504020d091e02010801080f060c030603011b05030604051003051b06130806090106060503010f060c020a050a03 82
    0x144c013a01c1d11800d031703882142c014144503502c0350802c10f4016001c0c00c00144003249589540701d0002030340c1e6280136940509004200c000151034000c2c5600510714552150f403424010702004c1140140b290100401a1038041e0020001039103181e891a0050000815130020000e0304081c0368816030b148681c8a005000b41400301d10450300f180104811034001030b001403207c00d803c110100c14a1800000c1d68219030007182c005880300d070f141031b0040184c400c50030001c005002204003c450003805909180842d4000c0c1e0711402030381c1e00c880710789540e554102e03c00070320781e8071080005642882d00001564030240140011454103542440300ca00084da40c92208089140441000003e044c14411b5540c092411000341c80518030750344400d51903035844103c8194040c1d03951030540b101e40b6040222452269110030054403a551503041c152030302004d6070b00520350750a10500040c0749115070140c9050301c5280409070580d80c83c00006903031000388103000b240c00108040c4009940d65441c241d5078000e500615000d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 393883785 1250 393882535 393882557
    0x605150c0f03070f030e01020312011e0801152904080715170106030c090b0310051801030201170403030f06141f1407060b030f030703081005060a050a120903 69
    0x5050204000140c1075690052104001043c3c180b90707039066090301414118844041c10004174150300c900000c3c0720180d90400000142c08501c08203d81c0118036131054580226200e4410a0a0750418207507250f10300c0c80150280001c1c0f500542e0000e4074038012801d82c0d071501030ba641c0c030300d44d07900581d000700ca1070381200008000b0101c0040c000343c2000201d01e4129880485907441403140c92041c0203003420107598070241502203000b103012201404d1403140700c603103a140000124034003031401e008243c00f5000a4030020214400c121000341603941c1611041c680c020045481003503844002e00035000c0644458000028044a01c1150041c00903070032050300d240c2e1003a007401150440c19000000e22070003c900089055030002040c0880c4005c00700c415a24201400c02c0c001901803000a1035150161444110400c04000b0040402c0c81c0701c4d032900003455850b440d84c503c00b803140d81f0480e038100004101741c400051098000f404803e1150410140c1040d00304070280c20be070604c03201180030078005080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 393884892 1107 393883785 393883807
    0x206010b03060f18070f05040e0f04080d0c031b110706050a03090512070c0f0b03040201182301080c04121205040312030510090204030209061003060515 67
    0x40d1690700c4c072039010b40001190041e0380081c081203803051070b2000140550182c408684040324004c01e5035030307603103510748011800034002c4500c1c0c1c5040040c14030b100d0b03c1d0300c2102c403120710039680000c44402882d041d15641c140e91954900348080000541d00144000a0b00d005540c06031520380d44a4111440030b6000d0003000340000d0030340c004d8420451641c0e0001000d030106502440c003c4400956800350300c00d5000c098080c6040c2c20904000190255001d800751980181a006e40424000d80d04d002d030301252a0704a003071118081d40c01042c2c04403982c0c4030000c107410282d44007003d46840c0c03906000600050901100614104541d51144136050086060b00c004582100b180c414181080c0c60050051008503001003c03105018408a0390a1180c404d50b8140e032b50113001112a03442d01e5003042107a9109014100405464910104035a100d0306100415032103141c905a44550210312 = true := by decide +kernel

theorem cover : BRFrame.Cov 393705035 393884892 := by
  have h0 := BRFrame.cov_init 393705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 393705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 393705035 ≤ n) (h2 : n < 393884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
