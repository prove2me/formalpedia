-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2746
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:37:36.179025+00:00
-- url     : https://prove2.me/submissions/b58e58b3-5129-4431-93d0-4fa6f46d5bcc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 493705035 ≤ n < 493884892 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 493706285 1250 493705035 493705073
    0x207060f0315150801030b0622020c01140907030606051503060d081303060b091f03030804020d121706010503060315040c030c080318061905070c0b0c100b15090904 72
    0x51a01581c03c002000c0b0402408111194002000400d0040c07030080c0784038500c044684101d0306040c000d080308001940140440751201d648071004021011000f402407071280e50242c0082007000c0c0345041c000161030407903000c0c1d4091007204002c0e51415940f0412246d200c1d2055481116011192070607415622421660640c60640d00c80040100440d035040710740e01d0b050032120941e0940350722801034440b940c8414481c038002c0f03881d441000068090440e803a8404d0000b012008200d07000e80b102208950512000000035056540302d5480c4d1410000090b000102841d14509514002e0040b0f81d880708400070701c40c5010b00c201e000404012143c500355001d168804207408016903691081c40c3d49030007185001c500840307000300060b200c1c1001c1050300c01d90f80030f210b0030100341542c43c40d0566060b0711841c0c003566070f20904480807032648030010051001c0c6000c2001401c03402c0489803014215949034284500c1000d0303591526100c1030042055a0405d01c0c2203503589929111450a02001614036007010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 493707535 1250 493706285 493706309
    0x6060310091a01030501050f0102032b02040e1e161b02040f0902120123150a06020c1c050a030305190c0903120509090109020924190207060f0315 64
    0x220707909002c40380400c2d01007007a03c3c14045a41c0710342c10481c0041410b1744460069000b84401d5040e16804120105004800d1031103500050035100064140d03032141d08007482e01301c0c1c1842802000600c0c905c41801880000c400502d5600700541950440c0c1001c040e0f032000c00c41064401850302c100441400100b55004008000d070f00b4901400c01b01804800400740c2c030984100d548044082018003d0b1441c503403200740881c800d00070f011841100081d020304150440d0002c0300110701e0907199020100301030304251700244ac0f1011340100f0803d0501d440c14000c200c0b1802800e412002440c001f5002c1c1540783d26040c045090f5035800010800c44400038441c0408505003080c0300d42180d0000b103041d058074054050003840340035624080c2d03024801c080c042600540240010041e0682c0c9901030950440003c0010f07403000118060048083e00225101441c2c0030009180c201c01540a9503d002c0c01005002420303c4514002e000fa0000741a681003070103260716040840c410f000c42c80341c200c0140000081e50 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 493708785 1250 493707535 493707551
    0x19050f090a0e04060518030a1409030604060b090705070c210b0c041d0f040314190513061107180f0204091407080903040611070b030103120905180606031009 69
    0x20b0103a11400340e0701502c2040c40c00c80401d029032840200c40d07030341d81031880003580ba141d0090310031180f54501c44584c02102c0c00a122405140d5020300c030103406140200b0340800c0721581078081021001e0084d1261090003410800314000a20030007100c011a400345000307403182c4a40c01d512024048102d84001c004504510800c0014000c041c040d105880841c281c024060b032004503580c08021301a41d01c000c1da0050038000900007031040781501d541e0520400200d0406203142c6e40c4c103c1c46101d1208110108074080340701c0420b1440680d00384010310082c0384c01e26044400e04c184a80b5503199000ba00b01c1b900d5034a140d03403c0314078982c2260078030300c807040d40455455030340d0300e40000203005201442c4445c00c001000324101d58030880c0c2290084030580d01440c6032030b1818500340d500101c1d80364244114007418000240c10500080a907000714000c2c104480807040e180002030401030190800ca2082c01441708101c0415040346142c3c0e07001c8029210755640351607000013482840c0d22980000b00044c107040e10 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 493710035 1250 493708785 493708799
    0x100b0a09061502120403020d0b070c050706030606120c090b070305040f09060315060f091503050a081b0303070905010e010318320316030903080c0303010f08010219050f090a 76
    0x240e82d0124155500380c601c4140307404040c4940348038a1002960150094110754089000800801e80140940c02e2040801b100759640314117001007a880390000c2580d444080007a1604640400c0c00141c0139201000403035a60a00545010300500620000c044040351140405000da01110060420740c10b003c032071580d0b0383c94144007908032400b044400b81d0f028000d9841004c0507015038025a958403003e55085400c10001d41c0080c9042c2c40c05c6030403001006030000119109021582c51140180c800c81c1c0d40c1d0001540d01c11a003403017140b000c0c52503441002000076250b40442d0035030a5030424649a9030741106540102d019246050240603034190000300b035401c0200b241007421031000c01c580042c109408268100c0c008403080c890302c56081e001003010350b4020b4a00484040d10501c2800c20038040da071285c03030302031b10b6411a10b641003080e0300002c01880b000c030a4001178001040c40c1c500031f501c0c000c20015035103a040c0603510315005103d4081800030710013507664150303881c201014010b0380405a0320b801c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 493711285 1250 493710035 493710059
    0xb0c060106090918030f090306020319150f0501120212070e040b0303070c0308030c19081e040213090311010903020c13150e09071805060f0a08100b0a0906 68
    0x1c584404201c26510000310020140240700104581101541a011417600c0550300038101d031002204100b2600740220020f216440914050300c10a02e030701d0054003103114108103d0300d105c0013850083d00302c000300308030203d01c1c0807000050300c00070328003003d2401c0c05a55500c00f038000c200c0c6c1088011018000c000d05a03174040c17801c0320b071107104450a00c1542c2c6400141504c0e403041c410301410f4007a012105101140c2448000c68016440c0103400345818075131140b1103480c80071080d034840040c2001080c0814040b540210403c02c0e00044030342c3c041c5040582c00101d0303a80c1c154164010080d1200740c1a02410301648040d004a0340c5c0c100244544041d61600a44a940486195105a030042c5480c00d00061610070481041560911009800c1c02c2c1030b14000d210b02c2c02800d070040d9214401e00410b409203407220143d21080c660324081841d05064040181141005824601403001718204100c204800a04409020918000054842c0c01c00c40410860341180c1c00c01104107040040c0010281c41e524 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 493712535 1250 493711285 493711289
    0x602010b032a041a040c020a0b160e090618090a03120c050a11010f0f0207061a0105091009030b04030203030405071715060d06060807090f0b1c0c0b0c0601 68
    0x18165510b54030520403000070302141d84414407040300406428419410070340d02445200c6096091982c2e130742080000103041c0c50411060b640160421040801003182d10403040c0d81028091400400300e01c030314080106050704190740144111112004105035880d03184080c1a4080c00003c3c0140074940003122641d40c0348004d00440018000b0400c128200b0750b41c0c0305141010b1601d0359200c0c640b00104000700c40c080f40509140030705550764a07200b034141000784184441c92216440158898801d41400800c40b9402061600d001d58800712440344c40e82e0200842c1c000c8041111440076200c8520000c441080b0182c00040810801400b88003c1c11340000203075100b144160b04881c011901ca803184240c0c0d80411186e41b1480d070000c0b51401c1c0c8030241441140d4000350103025400c40152a4440200750355040e132180300f480c1c22054080c080d0404502401e00810242c2d0401c5c01380c00fa00c2c90101c1c4200c0c00c55001c0c030703c0000043c6100720030004804050002404019410f549a0f0700704d41c075040d101c0700e080c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 493713785 1250 493712535 493712539
    0xa03051b01050f0f061504150e0103020c06011e0e0c07020901080d0c030c060f023408030406050601030605030f010209100f022a030a1a01172a04060602010b 69
    0x1261108050345814016203200e01070080b98841591070300d40b8401c4d5680c9002d00115445442c01078241c44c00c55900f809040144010203c1c08018182c00e0000f6061600c105801c40c1094010040c1212803100004c00034112401202721003032004021440f0700b51054075400030180e5101000038031441e08402400f40052900881344042682d0781e0341d8a0b9941e80310701602601c049001700205001181c080c0c40380001b41401001c000c11440c440c40d006004030b030b002841c40d4000751074454142121504c4003003640b100802a11030411403c80d0b0780c45401d400c6c000140010086600c410000300301d42d02c2504031400510010b030859071840309420b5028040d402c00c1002078010030504865a80062040204100c4034400d5006000c07800c549404140c4000c04c101e0311081683c8480340803901c0358800700f0107224814042c440715140b074039541c4081c0220b50701c107034044d203419005040b0001003e0b1000c500001c0740b00c0300325500c5400c01c40140b0281c00045e00781b41300c0e5a01a00c3d042000030503a030103400040484c281 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 493715035 1250 493713785 493713817
    0x30f020406170a061515020d02060c09130209040e060403050c01050609130f170f0a110616110a020d08030f130b01060c0c03080a090f09060b0d05060d050a0305 70
    0x1241c4044441244199290798070340d03c140a2940403c8150f800700c0100444a802c0c0400c464440141408841240110400590080813000078066050054503044910742d003d07075141c1241c01c000140d0100d61415000d0983d54005070080c115541d95000d10035400c00d00301071712882e2606080c060b110f6007040c10110313551350820000407803501e0311200a5100d07403006414072040c098281c0300c140c0900d8103030404480d8008481403d240d6a0101c40c05000e035100c5031a03041c6c1e95070101c004000e00c640b02c81701c0c0e100380f1036102d40305002080c0710f201050341d07891180e440c02c4000f50548244152802ca540c480c040d401c444810703440d10034800b010380114498111003c602c0c041b6121032500c070078900c4200d8405800c00c2d51940050049a200d107401c0e0100f1401038290742401c54494031114400c0c0c1c0000000404203880c1501040303829000c00340c410090004a404204051034001103291510550700d00086051f80c401c00240e0642d00daa41c045090394120048a9000701240340281a0b0b0b40a1408106a452 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 493716285 1250 493715035 493715039
    0xf180f060a08150a110903010e010c031d190302120a0903020a12170f040b0f0415051608090607140109060b1509100512040b0717090c011215030f020406 67
    0x280c00142c40001140b01400e0314a540e8910013824002e142c3c020000c0c202810420850255903000d000b40441e14050000005000c4030405c40a811110404d404400f01003c40201404424010403001c1d81072422000004401c4114a0100e00307041300c01400550389080480c00d03c9032261b0065030402924821f8510088103a101d246000c094400140001e00282100c07440808010005d4081e050490f50030200341e082c07640700c81d240380307058000080c3c0c01c00d0008007140030031858041040ca04002c2c3c02038206145007245080d00141c1401c0c5c40c2002078404840060400c0c05501c1e4001200d4481d900076a1040740d00b010444034901a0400d81015690305061100d040d08614041070b03440f000902025035545050b841c801440110505107900d6002c0c8003061000340401d80a074046c07648142d00c2100013811a1030306090191211811400482000c0c10038020031410f803c0003c0c2814102d182400c00016144e030884488015020104001d00c8010f08500c00204108240b090180102d01c221000c0c05943d03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 493717535 1250 493716285 493716299
    0x403030822240603141002040e2d16031b0c0204051e09060f0108010c1b0f0204020d0e060a090809060d02090d0308330f180f060a 57
    0x46150401c68040c0205900d00010550500ba41c0d1540e145801850b0300300c1c00c40e0784001140e0380c90b4815101100184640c4072001e00506c52038003030028805085003024208240106144401402d00c1c1884001d010351041d26410407407400c800d0758a04010801d00e107001656260990032040c03101020908107405d00b650010b86014100000c2c0b082c0d611581c1e000c06540800c8050003002e404010941d0780761220180181421510511401d100d1000b843c00341032a048043c500d2030b050740703c805564540310080380090b500810501b4a1f07031020f5140f010100983c10898070050b600d1a0080d0b0042c070019042c0103800050b040520f5800051050342c1641d601c0c44494415a4107050005005d0304c1c040000c2081c0e494188040d000c450130341030700141001d4584005c901440c005440540104183d00100402c1c200c41440c03011155203002c0c0c000c0411b00030003989484008001c2c0710f040c4039001050348011244c44604000b03000311141081044c0c2c0d414141d480324290710017541c8280c007030220a42c02103604 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 493718785 1250 493717535 493717561
    0x10507110c060a11010903020f15130b0703020c0604030e03071703120712020f04030c0501180302060c1614030d0809070b0307030b1228020d020415051504030308 71
    0x2030034020018141040c0c604080140ca40e200d0702c000c80600411040c1c46680c040c0911908100c98801d4009000c1014210a542e1030104598000c0200b0079030f1100f00070200300740c8040001400e44c045914045611391000603400390048022469081c81520200420b0607480328001c40d85000aa0036104003503212081c120314400b4245500c002ea5208000c44000c0803007202c0d005901c903083c0c1c43e000d004a845400c42c1307801d0ba80001e9046451680208007401030114540e01c40300146000d0801102c1c0041001c0f1140184c0717036500c4046c1c400e90780410000e503060b50500c00c000d6021108100f6030002a00da0010740380607850340d1070f454000d11441c8084018035001e00f000500641103500144549490004440c102d07500082102c420561900032805182c0c58030404070011402c1395019140c0303040c1c00b17014600e0700e07a050814009200000003225025803900a07614500d01e405840100d003e0490b10040c110b0300e10280c2c031198102141c5260314400e00c0c0c0c108064402c0d00e00ca542d1341c3c80313075071281340401c0300e1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 493720035 1250 493718785 493718807
    0x40f150603020906181c0807030314040f060c1808012007020a0e0403021203070e01020c0406060f03150302060f03160503040309060f170907080118030918020d091202010507 76
    0x1c000201301009466011003005c84008a00034002c440c0400040d01d00c3c0100d01010400311012800400c50004240d050b0040c4aa883d011020401145c038090b2540c6051154104002d024255921071064016109400304401c1c9500c00521001c240e5039480c00070700805000075503819007141c4044008105002e0021245000c0c0c00808102c400c81c102080700f58180d0001d441101544a1241e032040e1505414018610624954030b490141d400d0110029040401090220340305d00d15054040c403070380b40c000e06c00c1c016a00390780c50000f80344402c14481d10600c0b4081c0d040654448004125140c009042400541c4a4000b079106200350704042401500c0034041070720010003184036113005001d0a8403443c1c5805402e40e103442c00804814224039403402e50403095440d0722403604410028000030009010310584140010520240041241c600410b59902e82c051040e40f00f0721403a982d14440741503010b890089a45242c20403031416140391200344001d00c00d0341070001d94200000110518010311203440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 493721285 1250 493720035 493720039
    0x709030507050a05010503010b0a0327030f021f02090f03010e0703032303180307060e010615140301150c050607020105040317060d02011809050103050c181b0d0209040f1506030209 79
    0x2c03c59007451100307101d582180ea221420960341314010010003342c025442002d00c09403080c0296120345080051021203203800c92019580000280c006482c2c0309959194030140f00180141c8544410000861400600c04096170560908144a1040380c000c6010f8040340e110707032110301e41c0c030300c0214011401c541c01003200001c4000030710000e40c2110010140e0030320642540107480c501441a030702d0320b0840d8080c14031a001d40c0c2d90b03203c4c1480141c0d9003c80094000c40e00e8100070040b4440364204843c50702c0140170301c0c501122851120382c01c1c1030080072000d00866000b4140c03140340c036051a00900800d01264181c000900101d01c00303a0070001c01b41e07004c0c0240303009007524007007520756001510948400c40840e040160f900c040003403194454071030507029510a101070400c1c40c1181d030802624101401340fa02d000d520800600c14142c11803092903c1507644003581c20b032038518004110000703001e100382158110b03003000c158106000507540643c0762200041414441540c40700f0088049000309102d0a0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 493722535 1250 493721285 493721287
    0x7030e120405040507030b1e010905120a02120f030706020a02070911031b250210020d021903021f05091005130201030203180a0b07270905041a0709030507050a050105 73
    0x8000c608144d00302d0703a0301420908000c26100c000d1000b0605a80c0401c814110200c1c8103036505803207607031001102008000450b07006450801404d00c0c182c0718008240000e1042d920750150001181050044070705108062094a485a6090801101a601811040700103018604002c1080445031094048440e00d0840710340c115030312280e1508c00d004100300500d074400030510410402e1140f0640c616841709130011800c140703d1181c81031000340c0c0400c00d031000940d041540d0140100d0345c00980e00c407124140244440045141c0c0c02c040c2d04124070203032800c030740d52044006000b4050080d00a9030003500c401003142c03150410040a0b0003159810b13142e1406038030362100040701561003500038640001e80000c40354400c2440008883c504655030388220781c003c0c034039410002c1d030343d40001c1180f01c800c4031000160740c8810b00c000600340c01d0301c50703000d0b0065060f42c60740400c040c4151060741004000300d4030202d000900300050050324000d50791008542c1e6200ba0030000c00c5a050000010040b5401a1959 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 493723785 1250 493722535 493722539
    0x30103030c1b08030f0d05010e0124030b27090706080a02070201091706040c0b07050c010c0602390102041202060a050d0f05010905090c090604020a030e060f07030e1204 74
    0x2034500055203007041c102150b403039030302090b00002480104940310040304982c0e6909030045111b01600c5059100d0090b11448000403c80c145001c8102503003250032811001a51101c43c200354010110103c03000d4109406007400d502600000d444192425540d0b44000195540d038001c460752903420307002e10030000ea410004668000c07495005011604c3c81414180c00d0307640c581000d100d4600030300010540d05e5204900f400140030b42152080b019100065010345054140e071141665036013500c1c6400c1c1040100384000c000d20044e541030341c0d0b034000d400d480c107900d0340003d50703910001070300010359444404c5181c0c80e90b260b8000140700700c5c1c1c12140c8a00d9041c15103070007a001c20403034cd0807412035101031190402100000365882c0c800d1511ba0865020001480c1d4180710000049542c001c1151041d9400307011030722240d540b121042940318900329005a950701e100c881c02ca001c0e14480c05085140d10805060000340032104080601c81c2c9500c0d50104801d2800701c041d01d40e605025122004406410082 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 493725035 1250 493723785 493723793
    0x310020715141510120905011d1603030c230d020c060a02071205071701200a27051518041e0f201305102010050403080417030103030c 59
    0x940090307080345061030010180755402d517100740c8001000454403a59940d0282440480202407092400d0140d40200203503d802c3c440070b00000860302003e01403100c0d0391051001c0098480548400c0424030929061078505100341968403132103065044007601803050107207220b050590591301d46030842d5004203109450004d07500900b8104034025075060141c04400703c1e110306c7c403140780e0305905500e00002405071110303035600d0103d0f4240f041000001504010401c242e560115200c4c01131280303000032803182d09885840c1190a200c9e036000c40c0d00509401407580032640303d2006040046400c2a03545460f00440081208641c2a417003d4502d2141d2580303c184007070300c00d80c070484070001c40c841c2c00a03c040691880050f01c80c10310240c4504000c0020b8235080035106640c81600030001130721401c02d90900c5070000307001d140443e0000c1000c4258208034056151042107010b01c1141e5440c0e082219080a04000b000b041c03013124296a0b8600e044000c041041900e01164100c80c0c05507030701d00c07820704541c0e9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 493726285 1250 493725035 493725049
    0x4030201051804150807050a0303120c090e070203090a120b160203040305011b030c020606031911090f040c0815040602030603160e071202091e03100207151415 70
    0x12060100281203880c80d15507100320510304c200c59114840e681d00e013100c028038040058202e24000c8603504020000030307420a000c840500548100810382d0b0080c120101c51200d03040d4406048071188109204107035401000502c03600405840103000300382c845e00c080085103001c0600414403000e54002801c0c0300c2816405480f401d05a1050307034502039503a01c03650b00b9946843e15031900340d5060007161443d103405104048055099001034007131132130400d000a840b03d04070b4220704007081911000608000901b190007001423401841c611650400030700c842c4100a0880d02140d600e03010000115200d400002c000000029000a00440d65110f07075800c400380d00301070240c43e014803400103680c0c407201840e14103d0241c5101f028454041c5003180e0020700e046020803441c034140d4410040305c3c15035200c841442100480007501c20280b03480405c0420b1410600c41104006284003043c880e0402008007095034642e1030106043c003094003141c0c1e80384004ae90980b40c5814a055030504030404d420000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 493727535 1250 493726285 493726297
    0x190e19120320100204050916140c160803040501030e0712081303020405040501090204060f0b1e040b0301080109150203070e10020c06160b07050307080c090f0d05100b0909030403020105 81
    0x601d0020645909036500d001c0c0e003d0340482000e41c010500740424100464000d41c030818005e403902241584501c00380a204541d041140d6009001400c0310001504002415011f1355150038600c0187e40ca1031080d883c2c1e08039001c0e041c0000d041c00241d40d904580003e010003511100b05515000005e665901070722580100d41c800c010b503412240010159865210b41407256000d100080345d010250f01c1040f01f15122500040c080c0100b1941c01e0014841c10001d640400e1100030f4503041c5404288001a894000c40d88051001d000000011944400c10b4100d03a404620410844440159141801099020840303210000035201d412104040c54415510001586540181d0f50300e182e8403004103116511030b070b20b410300400b80a00c101040084400e503696202e409441c025082d0f0816140051039040003801010700b003c03010031000f0880c1e44400d4140f60340703030b0300904101c098030241c6000e5032a40d40c503a000450301403600800c1045800c0c6400701c1c51048105802942c68a41983d0054071550090 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 493728785 1250 493727535 493727567
    0x406060b19080907080c010c020301020705060108030a02011a15070201031e02120c07050a03050c160906060305090708033f06120115050411190e191203 67
    0x1459000920035400802485604032522454034641c0c04020050722000b00070b4100502d90b40035500400c01c080002c1180e41d03c45000f440c1100702d15500c0d000080c0a4000c1d9400035107640103013400014001800002405d444006400903c880d1000340c03200b401142c9000031071a0007290b0344203032402018014004010561050500048078600d0b192103500624010203445c089560014107240a103060380e640691021014100b14503200c03079035031816142c48446030028140900480c110500c220103122a4410540d101102c0034040d0380c600c3d694010381440d2060740042403414000c9151450003142950685603048021032912043e40030355014107001e0b07041010000301c0e0654100190f08040705c00c50140d64206940d0706142080c604009800704650030401040e8944852940710003460740c08001243e60850f4005400c640c0344044100e10b125481000301061031001c3c001c101ca40d04240116140c010030765065202143c42e41340c0800c001c0d5180581000b0000c00c10300b402c00280703e588408403035800e03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 493730035 1250 493728785 493728791
    0x90b040209060103291201050615090607151d01090f150204080a060608010b0d0b040f0807080c0d0315050102060a0e010b030a05010504020301140c09010f030219030b0901060801030c0e0406 83
    0x76100c0c4039043d11700905911038816031851103400c50b482c1c2100038118050060000b000031303080a400144c801003004130480c00042c00411b1381480b503900d103025179100301c0e00300907001002030005840c080281b01c22041c280034422844120b0312100300c14801c448099030b1100007141c80c1010394076580c0c2400b81c040e40064942d5020440450b05c510240281d0750b84a100d50008243d407800c06400a00356100440e4160003001000c0c091390124091030032864000d9045148601407060508101c1902e10410700041e040c003800080c00c001c14540000c410349541400d690802c04000350303214a0344040024440c00d8016488180230074041d20741980460640d600c100e000245d050681c1c2c01203400c00384c401d44c080d03680b81d5684080005505080c0111800300012003810911880c004607003150602a61940b1410480f8020480e020b860082e41210001c825030380842552450946004024103180000079000d40e42000000030341500410030b80341a01d80c800d0038101201d0030a00303401a44900144280c41c0662 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 493731285 1250 493730035 493730051
    0x15041401061823010f030201031839120c091b0e032112010f060c020402091804030f08070c080a0c17041712030408071e0210030606030c17070f030902030f03040503060703090b040209060103 83
    0x302f100b0000c001050726082c0070248581c0c60921603681001036010b00324039030406605500800e01c000c1c0d0454004e10600b8a40510540000032a250204101d0f041c2d1561800480c5112100c0e5104d01410078003a00c1d050049a581e00c2d030700202659041403207000301088201c00d070440145410340244c4450341c0084c201416207100d840c29039400301405d59090380410060295009400e034031080441c0d01444e1030a2036400401c89607182c044c40c0c0b080705c0900041203601b09209040021721503040841020762004a83c850f5110155006003c1c08103100b031940740310314580541d1805a01e4162031080f82c108440d18100304a1b41c488403060000c9041d1140d082c045d01441100580d9020541c2c28600820b5030b00250480c01c10b00007600711100540124103104264180a0340d0012050003c3d601c039002e450882610b444c03a06c8160054404420025494040c16040510034000080a0030403108114211680c1d40c481c250140d0441d1100d58000d8508040c110008000d4100308030308a400c81e8040c500080c40750 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 493732535 1250 493731285 493731383
    0x20102101a0a141c0305040504020f1911160e0609180d0302040906120b04110321070323040302011b0515041401061823010f0302010318 60
    0x4040c9801011040f041c2048200071410309210203404d058000300800382c4c1002d1510003603d20300452040607c51500091040c13500310404c000d0b102000c80342280051940640300300075120f05d981d80d14000c51071082903111a1251b0b10600010101d40b00d204c5d0140b030b161600c905000420800520140d0a84078800c2040e50310701c004c002403214071000e07035001611503003001c0c25035041c2c40c0a0f5120410700e4400c8000340b000f040c1030310002900198408081003c105411001c41d040000903070620102c40b580ca00c41c0e9403000410002031060074131a40d24600301d6071203402a00c2d1a03034100c44840c0c0c1800e106000034030055000b0b00d000140411800ca4001010b030380c1c2d941d030515100c0f01400c0302785200003003030912040000c0c4030b54032002442c03000c0003400145c0c14540c44a20490702a82d04951054494a4500c0800583c540d140300b0141c0d0b007840301506684079188848a048607100c01c900180c40e02c100413120080e000340d440b1101d5807144c03220301600e9001643e810f40300c0304030f611244190203400c0c001c801c2d5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 493733785 1250 493732535 493732549
    0x40605160602074d0d050c0316150309050307080c210a091403031e1e0c06071806030515060406020f0f01020310150306030804240c020102101a 63
    0x1803419103120302c0c1a1110080103210415030510818a01d0040e064540130100b407410b600341c101c00c41a22040441d01d442d09106190604070041650180554400c030110202e8941e446815118800705090228901c100201d08540b40d039000504980c20601c006000910700300e00402610344542c00321040c82500d0343c400d058494825000c460484c50019a0708051038010f1480c2d001801500c0d0020300c00407261000c40c1d141d11440a8480c80c40d4800c1c10546100741080c0d0030b0300e1940c1000404500e07103404d441145500c40d0702071000c030011846002c1c00101110b2040003300c0d251048041e00e92180e034603100e816009814007421240d4420b03c07403500b692407a140c060141c001016641c3c000c140d00715805401c182041d802503015003469004100700500840411100c4040792164000c081e18620310301811030080c8078039000142524030000d03000480b403005c1c0d0444032039050702c504103299640302070000756030305000218004d0158000d040300500343c09a0764405503030f95050301012012019848001110 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 493735035 1250 493733785 493733813
    0x30405030f0f04080d02010b061b0109060203090d1b02060406080606070215031f05030601170a050105040b07110d0e010f090302040f020304061d0c060a0512071e0504060516060207 79
    0x4014003080404c0320040030010b0030107401c400c0c002000742200410120340b19114100400e614140d101d0b500600040c07003540300512058005400715103e0810117038841d2180074141e0200d00054900000010321005039422035030070340e401050140703014038100042d81c08410050045601c0841072281d100584c070b0740321600c0b4041c0e1034400d229940e40b034240340318141c24544640e403900100c000300c0c01340b105e62400100326054443c00078030788801501c6441c13018640750300c42c48010195402c2806000800018a41c81d0340158129100d43c0540624a0700085c0d407008800b41410002d030203941810030355402800700c0a880b422600d1f281e03410755280d80100302500c071181075042813194008100801e00645105035200207009030300c0b040fa2840f0b01441c841c0e880207421801d41c416000064010320003030040c021208006810f601c4011140350049010701480707404800d0b04ca9580c0341030185401c040c443c100310740c151240ca846040c2032101a00302e66003054003400080718416030810141020131400300c1c2c0e60030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 493736285 1250 493735035 493735057
    0x7200d020708100902030307020906030106050d2d050a060903050d0e0c04050114030a06020f07020d080a0e0f0d08070c08150411010305150f031c1d03070f0308030405030f 75
    0x4900c0c07600b942146800341800a110311607103800700e0000140c0c0c01004603a5034640488001ea52600c5020001740140041e0b4080c039070000010b40f80c2d000300f0511581408600d20042081c1e4488030740050788503058440e4600041103508018080d01c00103000c0d5000301c400c00e001e86041424000c410303811a0464400ca020002c0e0356200850340e4138685024001d80b400f501070804ca03a17503012901070102c0d99030580d14400521180d000b00d01c0300801034500003507558894005001c1d54410300c0a0524002d503500860807000043c0d8650703140d202d42d040141c070302c00c1c060380c0c040d00303000c0340c202c6a49503001c0e25041007034101c03580c5040520018000c0c0c02006500752075482e042c46444035082c10b24005025242c50050981490f0418080001030320b00300c0002800700005407200c00001901c000064107045040c0d18031042c0d84400c0541c2000d140e07100f038040d0403440d0399180766100e0f03c3c2d01400f019542da92500c034083c012841c9481c10300c0040c0e240b10295801c5442402181d041017181c0c02200159002008000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 493737535 1250 493736285 493736293
    0x10506031902030a09170703020d080718151b02030c040b12070e01060f02010e0d0f27090e070b0301051504030f0b16030218060c03070b01121a01060807200d02 70
    0x188842480c00005191b0140764a40c41e0440c0c176980a920f0b0303440140c0281c03e000c54000060600c0b8080d4000c290824845800703019a90740301e41c0704000c20320b0403000d0440090340708504441c03001e40b03403005180840d070000c008180e850800c03001c10019200c5180c10980121501640d0144404100046c1c0d024101d1701e1301d003101035030520300e0080ca6068811191002c580c100341026400780030106854002c0c0c80036242c540c8254100c00c00c1950b03601c0c040d21664112140038084003031525907010099064800840060180d90a690516a5102e12074029203100c0d10040004120340e107010600c0401840c0b680c084036003440d0303030ba8542e8004d81140c900b040e00c0e402039000030030440d459031054055484450303042c03c5003041d40340c4105110b10080e5000490050100281c00c10f00d0103010016980c1ca190300c09040d421941c0c58a1a280b40320780300c0c0402302c0f8540310040301c2c01810302e00746242070306954203a5102461551407420454508844c5040c1010800c02c0d00781402e003003003081c80146e0914582e0340040c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 493738785 1250 493737535 493737551
    0x20c0d06061403060415050606040b03040c090b06040e1504090b01030605011d13150e01020a02030711010804051002071505010b0c07060f02150907050402190f0f08010506031902030a 80
    0x40a042e01c00800c0c51007900030400f003000190b003030000440e1580c90712070001001d0303544d000460005c0c80346821900350070401004010421400060040546400d29414810080081e0600205005600030515040003900000c0c0711030882c900105600b03400107202040488290329003000003013003a00309a404980310310040c012003000a103151a00000c10050481030710f80401880100091120001c045100002c046480e4200503040700441c1e403040b03802156100f8100c0e134040e50300c0d03102d110100c0c0d003c241d0f007003030147c158040c00d50f03e8450360f04000600480310003d444c00340294400007040307594107008089102c5000c00d901c1014080c2074a140160364550740079820b240b5000c0c840c0c0c001d00401060280c50700c1d10715808a00c2d01c00e440d50010341c0450307a07180c4400381410185103400080d00580301050320440300700c81100c00e004580b00c0b074803000808140c3c80320444584008503000750104060740c004200c0c500300000103603030014800000c0b1400c205034144400981e4010b560070b010041e182d001d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 493740035 1250 493738785 493738799
    0x110a0206060f0913050a0b0109091e0314031b04030f03031a1309050c0312070b16021b0301090b010605090a0b18060a09080d050706060603020310030210020c0d0606 72
    0x2040303421103001c0300e1510b034140d15080001d04020300209241040390801001804125040003107405e5150300494207001c540e115080d10008119840d425100da09440d00c00c111050410281480001c1e00360f030f22426481c001c80c0700002107030b00280112000301141c4d0700035200496103401500245220b0038545001e4086400d0040503110028955528a9030b003a4400b8450360394001600040400d091003c200d5228070f013001030805051168081e094001c02400a1056159000501c0610b202d01d0b4030504c1038031001401c0340c0403001e1180c0d08016920800240c484e4808030003222904c41401000458203c450b5138610b9403044003a070202010880c040f03032402a0b0318182502c107001e07100503a0918102801c0c00411400143d034689903a014103400201c02107000c1c03084070300002501009080310398100b1000e000601941c0082d40070b480e401d03c4c01d507010034024424001c41c1c0c00f40280441d008100ca04580802410200c249040c40070f43c812088801d9645c1c0307681840c820b03264000c400003c2c40d603141281c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 493741285 1250 493740035 493740043
    0x20106141819090b0709080118110a0e011503181106030a0e0d1112070803040609170301180507030605030618030d0e160501030c0c0b0601050441210709110a02 70
    0xd404a48d0602000420b010502d460270001190007001c1100c5e041000d60224440f145281c101c20302020250001058003000c0a4149105403c9a60308001140715040a824030078a030030300090458024101521040c60294083d54000c11008000510000008203d62510045c940b030700300072408043c2001c0e03800105021002482d502802c04038a0100140e580004611000380001d02d80c40d0f641c4072510a1015100705801d011022030305050f034950312813411014000d146034a0903240b40c189800100024828040c4504684000c3c008104948600c501d058002c0d801040030a034500c01800200c404481d14002c2180700414000034044030302d24141c0302e0711009401d411403814141480740303500080758002e001700180d84e00080302d040c1030b40707900c801200c191140e94041e480348031090040c56482032014440340c11401440c1c0141502d0f00760740c1071407045c001c00810400c0e48000c0141c103a0300a0b072a0111012018030201064608140c3c441044c1700881f8907000c00010310b10408513444207140c1e0104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 493742535 1250 493741285 493741289
    0x1504170f0607230903010c0929040b0d0b15070606090b030705062104081c05040201021b0d050d020f06010b190c06180b07020106141819090b0709 64
    0x1010700300d07901e010000940641c9001c650400207405080c10650001c01e00e40c02d40304070600040c001d00101c00b041c0700c004d0150030709000d5a4500035540c44a5403e01c92010400450308401561441c00c5c6807503c81261102c3d00154882003210b074032484090302030340e120320f48450100307070321400243c40320350b00e00b400021141d0b140c10049605203441d5407041d5a64000a48200710740701180d045966080c038911400e411500c42c01e8400c01491542e0600c0308103c0c420002c0c10080003400c0c4942c81d020080b803e91025144141c4020340960004035a10382a4226404c40c12007562025000c030190703c12540d601e42c5840300e4408000c0041c0c10595001200c19018000280100300c5081c055041400c0c1d48200780207108aa000c00f0306101c5240090f00c01c00c2502e400031202241c0340d203001d801c405e4a40c20300060005e4103d40700c6005510f440d0700400c1d19a07980541200c103a001900c03208910998115000135900701034490070314124807103003454000c41c1364003c1e11015840780e104136046041504001e481c8001503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 493743785 1250 493742535 493742563
    0x4030c1a092e0c023708030901111609110918070807020d02030a0f0e04090303060503010e071a031806040c0302040b090601020a060c140c01090209100e15150417 71
    0x104410f4001d680c07000c100c0e041c0800720041400302c82610003410005040c10751425545d40d100c407040040d4508020004d04455002a00c07200009c0b0305150142d5107428200080065515000c0e60070300c0760b545982d0120036222010a40e0610b44501d2000085c5414007102607560000844000c0002180e8000c1d0410b030009030354002000300e03007c0400082e489001c0c01c05001c3c02c1185480ca06410f0301d105406401501b031010b4010030041c81a810014040c6c00315008131402503082c08091460640c0000e892400c44004d00c01c1007009408020049055a0018103811003604841032030300c65810341400345901451080721840d15039803440c4103001c165503400c81014490696002008820b036008550641d105a000000081c416005803003601e003485001041004810081281c00600c2c50551010030450f0003140c400d002c03036680381e0090084140354014004810303c2080404c410620000141441603402005290141905800851690420350183c10380d07982c0d802500500b2101030015006410355 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 493745035 1250 493743785 493743797
    0x518010c050403080d090b04030507061409120d060b03010e01080705150a03051008060c0d060801050402060a14071a070e010305041e0215030109020415030204030c1a092e 75
    0x48044081c005019510000d0000800001c0011010519500081c030581d84034440c04101e003084e0074010090b800c403400c2101c8043ca030a041203090124030301c02c90701c0307404220003c000b00000851000c02c20741040c0544031000b912503001040c140c1500c80a1400b805d00000b80c1712007580342106061411314180d01850098003004140e450715031480c400c03283c000e00281004103558883c084201d00045140d07120b02d071039019200034013a00100c44002880d0f81201c045045c8072198444005500320781c000d0f100250b1103d42004480d00c0f40e405503105121034540245440d082940c030380c40d0b810301316088003400c146800304030081112a9400035892142d0f0502031a082007546010340d2128041c08040d1003110036141c00510321011551210100c403a100c004001c1c02d5201e50395402c60701c0181d0413600812010100105a050b08035201c0d2003034804481e00824000c04191906c440b0120750b0034410400558148100072140c00c90f1070343c44881c42c0d855440c8152400c2c40c00394007160b50710103481d04d5061080140d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 493746285 1250 493745035 493745051
    0x1803120a0e160e180f01110309010c08010e06012d121406010c020f0301090609050106051c0c0e22030807080a06290909100e060406081902030304050a0801051801 71
    0x1980f821554015081d1062111000c11a1900303480e0400100c8804035560070100c1310641d0840180c045d50223410361200078043c0441e18003003501c9004090040c60314801d5203000041040d072040b8800ca948000389481400c1085040704450007504000c0a5500421080111980350400c1c92040f451410030700840d204480c02c1c00c0000130903040308480007a100f100c014030300401c80c0c1e50a500c102155a808441001030301a289030560103006a80302d40351103143c2c0b9040c407204071020b0b09226002a0343c0320b0790310203000381440810f00c08800302502d04010800c456584c40c0c2001131100c040501d540c0a40c59884040c0b5010600604040005081881ca0b6042c20010090784901c01000c6000f103071001c0100c107100310f0529000030302d4000c003048c07194080440c0c014016079000f081501c100b95140a0708000700e41c0d40e40010b00c000e6aa06100e052201d6000540d01c0c0c0d02c0019007500c81c00e0b198070090641c0d24041d641d400084442d07003e40c00044071a591fa01c140071500980c50b1402900090b024020b000c490 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 493747535 1250 493746285 493746299
    0x70b0c04030314040e07140d0c0309060b0f100c1109070309110301020f04030b0a24030c0501022a01020c09180c030d0e01140408070312030b0d0b1803120a0e16 70
    0x500286c4940140010b12510000d442100c070181c40341404060f00030070108100c0c110043c00b810b1003013419503240d071070100c03290300074180520080d02c02600a4060303101c545120f001100c004030780203801e03104d00b5072000c242c00300b5503101c003d941e02581c0323165404621000c050809402e0700449214a5200382c0c4100b290341c40001848080e035003100c0e0008a14092a41d55561403400f81007a00f0b00b00a066042491003031a4883c034004a005886c064200001056111001a82d58208124000c0341544078164200089221024602042c0006205813041c80e420b24021803400d09041c3c2e41c3c11a1450003240b203081c2850104000001d5603070490052400c418800030103031604210010355810003102842c1284440c441204640c001c01804007101d0034a03540c0d0910410081c003201001c4006824002d000e40700d8034207800c10249040d00513281b5590f41d11a0304801014590980d00c0d04024081444441521450380c06554485c244210300803e00742c0404a415040c403160341041900001c0c013600c203101c40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 493748785 1250 493747535 493747559
    0x70804050601051e0604090e100908090d02030129010f09180b011803030903230d080a09050304140f09010617132111010603020306040215070b0c0403031404 69
    0x444099600d1854060705640d00c4e00c0c003080c1881155001440050000341d80501e07a441405582040d00031342d603171400710b8200700d403d898600070054000ca105004210f03007850b0075a422604540300070000601d00090b00d82c155140440250b50303824040b4103182c0b000075540c1094250380c0d415001c5c50014480c1d800d001c07903210a844c0907121860341c2955150980c109034040c2114800104030307108032000b6940d50b4540142000740c5c50000300c4105440c110b01d0400702101140302e81c441c10604000d4015030519040456a05500038000f0210640b1211600081807040c00284003400700c111029031185120001e000140c3c002d20380751402502c00d90700400840b58001209403140800d490082501d854400300b1090b03454080348040d02d0b0040034107444002c0384403503c540a4080e8140c8070a4500000380c0b1030b140c2251628031021713400d90401400600145070000030140000c4039007510609240c6c2c42d0b185e41d00c2101d01103a02050f002030000e030900138950407401d41d4208524080804d46000d040c00100804 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 493750035 1250 493748785 493748789
    0x36031e021309021207030c140907170a29030f0d08010312050405100509040b0301060b0d11040b04030b0906060604060915031b02070302120f06010605030a0603050105010e060405070804050601 84
    0x42290340c2d00c6000c007155580c80c000c41040d0404130449060640b607050101500e90540300c2c10310804845070010800f07092800420340f041038170383c80307000214010303006041041c040102030141f40c0755504e00258191508940c44446029004d1a4222680001061600d0712159500243c4258080c041800303425912050241c15203a00c82d040d1010110711110039900760040b0340005074015088284141f1456200d0080d00003003401316030034840000c201d8107042c200c5142c2d0003111034289040000120074403854000b800d50724048100d0910f01651101659501e422176003048400301540000d00030f241000300102e581000d0205c4401c0d240c2441c184014144048030312411b0804500454032004a601a601030315042e00d091003450101c0005820094481d000c40c001207114007000401401d20000000b401aa95024030008014990800d5000d545035003000f003a989080c0d849100100028130203000d000d0082c40d070380c8002403460419030200710507102c0052031075082100c1c540030040030580c0002e940381 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 493751285 1250 493750035 493750069
    0xd080316050405090a0c030b090c0414030307050f0f2802040c0302090306101a04080706180314100e03030412050306011112040618060f36031e02 64
    0x400e0140300081e1280d00607940f10641c4040340c8400c124446155821100482150341c0c0c00b0002801c20100300400300505940803113021100340024030090309211203904090100800b142e04140985e625070785030002c0341141070140d401180c0340c420110700410a4400f1807158100000c1e420700320036150440c030841c2038030291082d525054020501400390b41241d108280240030b956041c030f003125180c00028640c0c4160340030900b0034880300b01040310803001d03070302511001c0014040c143c1c900707038044a0160603041c46105440f8140030000000d0fa214a16010b904040300141040301084282002118002300d0b0201080c0c10800410002505041d9001c10804090074080d44079101c100040b62040390090407200e02e441482c3c81d8200320bd0f0200094401c41c1c0e80341e0350f4131052001d051b1400340c094030684100b4000c114030300795002c0498050700d405000c8900c104225403a135564081820000108050018220591500103205000c1c0c2d49001e0a121100c0802c10040180e503980071407502590110904 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 493752535 1250 493751285 493751311
    0x80d02030901260a1e0b010c0f051204030b060907030b0f01081005060d0212090c011b17030703020702100306051c0501020c030a020d0f090e04021207180b09060d0803 73
    0x2041d040c5003690050f41600c429004280c0500e001c01c41c11009003405010300c03001100d00124005010840d020301c1920310810303911201101c440d9030300c0000300421400115018020340303810610f60462600030307000441c0035481c1075119050800605c03281910281201d410141415a00341044d2500c14000c44c150b03901b0300e04124107598034003d0082c503d40720b40115a101c040000c10010030402768001d40140ca102491050060310b506071180c1d5281e03120540b0a0109040207100e09170b588181381072492003070003038070502c4800900c0c00c40300c0c0d030a0740125109004680c0c00b00d02d000641c1080115030f8a01a640d00342000702905000000b08001548201c10100302449100042000b10039010b13900c1c6950114110380c0c988021183c0a034585800b20544000a944000603840c0d852003450100704948200440541985480e003d05c03001c200c2e0051090000c4c0b041c524002104440a0b4035401e00c51855100000c42d81d1800c0200f0065100c041d041c14452504002c549000c101c49004036a0004008100c0e1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 493753785 1250 493752535 493752557
    0x71a1506042601061a0901030b0603060906060705120a11100908160302071206140f040c03030f0203090d030f0323063c0a090e0d050307020a08030406090c080d02030901 74
    0x2d01e014100315084514420419681201d9036405640030b4410440240c85c2408062a144140001c40c0401c680480c1e0101781c00e0041059405e1140050000c240941d050b195604041c001d52a4290302c00d000782400034111404601001505020058060030b03003c9040c020721105880365083e40c040c0d80c102a4960080e94204000c140c0200700307580c020059096060204100c40c10008000c1c001846c68500021855000480c600d0706102e01328420340c1c0c4400da1010850131520201c4031910348609140951004110400803070b034071403041018503031003640d0744d240c0710b4040b4800500356190304860523240c030303803084800000c0c1003e13160090b07001400f5200010045509000801c110050340905d10311039101407103102d03000456880400000100f45d440302074456580e1841e01c204d41c0100395502d042c0d0824010802840d206100030740c0c04c07a260348121900081551600301d000c1d0300a5030304031006a075944202c0204010781d0002002003039800060502d040440401135202c1c031641000c0b0341040082485 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 493755035 1250 493753785 493753859
    0xa06060b120903210c0705150a111c0b0f120109120302090108161403250815210709090c060e0a030305070c150c0201090506030c041a071a150604 64
    0x140c07840943c0103400c461180381c111110a158000580f40c201c2107a0500c40c6c40301650f050602110244610500032841511224bc00c5100529040d861194061210824010325a980c840030620075400c4900020f030180700e40c545892600c10302c81a450600d8018405407050303a8009600c242e00c0b140480c4c40d80304040402008446401001384c410040100102c18403212034240c04014143c0c69407003805240d68043c0d80001d8916003c200da00d1420300c288280c2c5002181003810703124100d40c5002e0344c10306120300b64401d09414207a01e50040940c950b6106200310900000d114000010700041c180f410420300391001150459841d408040d040c00000078501c4104001060349200410904158038101203030361200600c25005840b05074002682c03540301180728940340e006c481c01402420a42c0749454a40104165854407810500e944040e0500c148030100c0c8a40e1800d80f00918440070f003a0440c9403071410115105502200369008036411300c02032040b5070504e981711041c42600c962104444508040c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 493756285 1250 493755035 493755037
    0x20d0207060203091e0106030b06130e0d0203120c090108070c1a040b190501140d03110d0c02031e0c060d150f060905040b10030504050a06060b120903210c 68
    0x100041c4010710020030000501c42c0454a1400400f80381001540d00310441215405e80d68103000c050706c40010000468001d15080300700c51004003103200d0120b80410b095000d5402c020840310301c04050b800000b05040900160812603500c80c00d90f03040741d810065600b00090121100a006009008174600110240441000c402d280c3d4040c0c1981180d03d0303d4103141004100c42e069550007100b8002c9245003110f1580c50190781e040e10300340c20300c10036441d0a0708104040350906180603000d11440354013412032001c007400341040c040c07074a4a403640a00c103684141031404005485101110000c80c01c01b01034240003280340541d03000100c60b1252100340100c0b00300003d200309a03140c00302c40240000000d203001030b103035168201c80c05d50f16082c034126500c1041c44180c40002d0819a840a02e4103610482d1a020b43d20003074109000304100c076200c01056a4003400c450030303a048803a00e0740000ca6000c1040c003564050b1079220b20114051410403140c43c42d070075640c1d20030064030000992400c6c001a88030356440 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 493757535 1250 493756285 493756297
    0x408040806070c030e04020a021c0908070e060a050303030f0c1b060406140108011509090309120f0611070b0a0504020f030148030b040b0a0b0306040507031e020d02 72
    0x5041d5866030400d4080540302248455044002c104204060702c2c8501d003c1c429140100110f40242118000301c00003480b07205141543c4000388040c0d0300000c031302d8040822084000c0d111004070750045082000c100402101d041e40903501c2171b8010030400104c0700791101c0c040d820415200a144c0c0ba104000405d0703190b4107000209106500c1a84100410300c49150043c1d20300c100c0c8044944407507602c4841080c2038404005030104110008042041464020303440900c4e818001d24094211a0b210187c0c2ca420a101071000c2c0c0f5801c016045c504180081d51142c0502000c030380111503e003140030b9403000e481e01c1008107003a100a0341d410000e8103546541d078509941c40e00050080250003d800700001d44140e0303601c0d0320383d500c6daa1002c1840701c06105914030304421505000c4140a0182501e040700035108425000f900035448a80020b659100c415108000d0028204c10a0701c0c1d1a04000340700481d20000d100f00101400c241c0e1920740c180301d02c2281c624180382d83c5405a070790245141c900c006440b03a8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 493758785 1250 493757535 493757549
    0x1e01061802030c1b0a03110c01052506050f010e010b0a1d03012d060506090303071407050d0f0516030c090f0914030a0207060f050421140c0f0d050706030203040804 72
    0x1c900f040c2c580300805c07100c002c0c0f0300c03a4456015141c3d0703149415076283c2c0c40e4608a8003042040244802d9101c0c00703a00c08055600e00e41c0b9040510500d0303a0b403001038450984440c00c2107191440103102490308400058050080080b1035803d103481d501008040c4445042d400b00c05607104860345c0c44544085d084420107804000d003d0051040140c07400c0c4401c0d007034010007180c1310f00e0202c0100700c501e0001e0840b03001d007400030015824092191542d4201011440e0f100000384221040010326464640c3c40304205c074000c90b44186440b40c242042810101c040344410303004080e00800b400064220032005041d2007201600162034550302070140000e022200000d07102c61003290031292194030010043c2200c503455801d80351880e03500c00d82503a480c41711907400000300344140803e20801030b00150341588580c110311030742c0c41c582190300c40403807103000300345c13040020740082c0340d8603050717041c803401005030160151410000c21403642c80d115240d0043d40680002c140e0004007140601c141c04081d00d000d407150b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 493760035 1250 493758785 493758817
    0x30d0c210509010e0406051e031c0c020f01080f0403141b010b040b01081b0a0e190501030c020a0803042a090207060b1503062b051e01061802030c 64
    0x18003002401c1900807008681c0043c80c40c0c1c1d403007480c50030580581801c0341c0d00905000c48485000c2c40c10380d0049054400560103125043c20aa540301c5010091094031110740c54000c003408840c018400ea51860032075082c107000446050011500c0d503030b580700f07034050380524040c01500c401030b4111003244503001808000740c1c20141100c001d40e4066200c00403017078007150100721542c40000151075604040b90203d10749142d0101d0f00c620440b080c0c0083c0320000d034600e010040b081c107240000300e6141c1100e043c040c041c24121014810317541c05101c2d4540708031860000389a01c108540d1007124901c0001d0005081e582c01c401c030940d40d45c0e0f051884a034112807921a610700305403660341c100b00a4210903400e580c400e0404107103c40c64103141e41c1c5240441013200000703240d90754070400c1c000702d806d00d036801c811010701005011203207a040e600d0031101d0911460140101905410311100c07164244904681141d01d4044200120b4242051a21510650b0b03d8056261b40e242412280d16000f1000000100301e8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 493761285 1250 493760035 493760093
    0xb01091502060f1e0c070503040504021b0c01030e1b0f0907020a12081e060d020a090b0103052511030409060902031f0f05010c140d030504140606030d0c 67
    0x340114482d4410b044070104102c0300d668031241d51a845198501c203102c906086000300300948200402026440d001d10120303480d041e590004101203900088510003c41c803074000a6420000500c080700b04002c00b4030741481203074548071040d52648140f03900b41d05141c1c040790b100380c1143c8840250003d55240140100c07070700d00d8420f9019468031200030085807110ba02c00c441200c00c80c051911213018080044640c00320040540c000001084082c0c00308c0d0340100e00440880040c0c3e154005900075120602c00400e4200c4500000b4007074420240c094010120310f002c02120404424a08042181d00c51900003a41c8808441817410b41c42a03410041005042800108074090550010740c0502c501c035146c0c00b00f20f0445400b41d02000028080c60b507814100b080300300469803017030070407102c51b40c0104031280c00011030700001c07032170245040c2e41000400d4031401008240111000902013240e0b000c0003074030031442c1410001c0c0d241c203d08500c110900c2905403104050000300c1203007003d03001540b142045468 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 493762535 1250 493761285 493761287
    0x302033a020304140f060c0a021006030c140105040b03130c0b1305011706010f0f03061e090507050309030405041a040f1d0a0b0604050702010b0a090207020a090516030b010915 77
    0x1500441d8165820401004907442132000003601d104040f4000001d0308464460780300c91015a440280882e00b1445800950351140480c0c2c81410700451040110b100d9003407408241480309034150001d1410f00106103c1017115464102c12203500c01001814a815440c8900e0907101c040007540000342505070129004103d00c400c02100d106540b001d80710108414081181030f401440e040314201d0010b074804036038541a602405505901041d40c2c00c0c0402d0058a4100e800d002560b103484201011504410401c8841d5039845120340104403850046e02c4c601e0564011a031301d11641c450f16000d241c2d265a651119252007603100355010005000b48200241042c0b4400500b881a100702c1103035026103400c425a07030700000d1000d00c070750b0f100e50f4507a41962103800304002414024504021365403075036403120304c40c0d864bc2c2902d0085d0403051030058442c0710700d0060280ac8200b64202101d494944030074044040108820640207110524001c03448042c07940040794042c110351b21041c1c0071044015007034141 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 493763785 1250 493762535 493762537
    0x160603050109050c0903150405011d0a060c09080706080604060b1206030c010809190f060203040b0f01060c0f08090d0b09030909251b0c0e040510090302033a02 70
    0xa0b61401d800340882e031510038400240307104e10059640c0c1540035400780a440e060780c20400d03038814003c1d03000191270381826504c02030711003001611315801c0c0c00c60002c40c4100001c42c49103500b4900d076890f21108171400d110030b49030b0b00c0e40c2c507014a600380001c460000d8240c1e81c40d50401000341c01e40c4410030f601c030b402005100d80171000036100700c0c1c424000c00f805414035520403140503115803420001409803001010f603105811158640940c1c000030085140c20104851340011401148200643c44480ca84809001104081a04000c0802540d072070040e011601c25001d0035030894000030749a984040350000142c1c45908004010814946003040042c0803078044040c1c4040e000540d4401d62550b01c1d000340c8a0075000301c1c008002100000c08064a03080c0c0b1608003403280c02d40900852114510a031510144a07602e0b9010b840200c0d80d060400081203000c2c00500c0150f02d6455050185803419900651280203210f0140030704c075501c4811500d40c6a019070004d140075904406480010040801c030406 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 493765035 1250 493763785 493763789
    0x50d0f051f020712181806030525080309010f0305060111010f0c120e030d0b03030c070806060a1e1401050715091103030703050405040504150c0e01030c140301050f01021606030501 79
    0x40c5030070003810388403e50082c0944038500800b20300c02580541030030b0301c02803180e0543c440c40b9842c1d80d843c100400027500822081c1c14a20034090340b0146170481c13180d800034a00040d040300401d41c106014400040c0d030802148400342d2660f080c040f5481d03440c040102c910f600d031001c40c01c0181d801c00225840740480b55000102c20421369130303410200d82c000f0034140d081d82c42071034607000c8580c002c021041080d20707958031401c8001402000c4e249003280300112507292600941040a01c0d0701b041c0184074507403a102402030010f00359400741240307040d489c5240028058461084c0d040f411040d1400c1c2c1c0c6d540e84510201c071504c982c4107400900c010b148080c54801010660030868000c01c001101100784e00d000420369411507403681c3c44c5460720341080144006020080e00c01c552040c03c56400d40440f03c414000c0b0f99200889681d4003080310115000141035654012582050209211001d0007440d201300c01c032415540c060340c0750f2001881c0c90300102d1821005108219a4090500c0046401603041d00b00d0342c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 493766285 1250 493765035 493765043
    0x206030708090f01060f0b0a0c02130506030705040c02031b0f03070c15020109021e0f0a080d030b01050a0e0d0c1a07060605041e09150509010905060f01050d0f051f0207 74
    0x101c2d0107039200f040c50072100382d405410404281035604100b00c04260000b018115070780c0c90400c0300d204440d40416000d0f4400110107443c40d0b01d40d000c0041c141820080e40000303220454051040010400c800f0b9102d2052426044010380ca0480c5013080310010408503074184c1d0301000b00c9a80c3d09841c14881504010b5001d6a0100303d03d0000105403903105014031810203400912205c0c803a0391860001180030b86e0350341c005400007103014034040075030b4840c106d0100130084100541014000701000030308039541a002d03641400424040c1c101004da0001204040a105507503840481d152030904941303501c9580e000c03c0d02c10000f0b02d541011141c141c005820a14840d00040c4042038840b0200416664840030601c3d006603d90b01040c02d41c8426003003001c519010740c40079110407461aa4040603104200e8941c2c2c07260b9140c049100401204000641d8014400000785941d5410040081c82243c60054003505420b50102480144181031141d02622214100003418951542c000c103406500007483c2030b1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 493767535 1250 493766285 493766293
    0x50d0c09082a0612160c150603110d0809040207170a0e10020304140603070314010e15150a21061202040c051612090305060a050a0e03040e0403050d09020603070809 72
    0xc102c3c01d115080c1e07016100300d10042c20b80c655030340340d0356103080031150307500f50410031461340407404240c03114406072076030580c0100420201e08505250f01200b0300305072000d00a004140d841c2c0f010815040907211840d90484000d41e5501d06402c040201d0808003080000341c0b1800150901c8458006442500141c0181c5111440c4110900281d842e40a1445038000c24510007400c0b20040c94040b0041d42d00501030f042c001200000ea850005011400342c002a000404035018451300c20074113a0f01c074180f0340702100c4403207411213004411815402103542617800d00060340400c1041500b100b1088042422440081121590303803007070744a04240d0404240d000c0e924000c10554094450b008440014464000004180315155104280300040351f400d03034104019042c001c400079070306010072401102400800314040c03d02c6400481160010a0300301e40681c0200420408004401401a8400e0305414819110618412140040d0814200c02507100c06d00008101d06260000441070160384014215 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 493768785 1250 493767535 493767613
    0x60d15060203030408030604050709090e0705032118010e130c030b18040201080903040b0d0515090402010c0b04080f0304051e06101a0d05010b0409110406050d0c0908 73
    0x690302d910040d100035184000400000311181429003119812090628014003074a65514481c0d0482d658080d01d0708094012103005c1100f494100440c2c0e4002502060351060507006c80300d0004d0364070503500005070710045000c03094020382c05401519004640038042d0320b41c62040030380c800010030300765141e2000700b17140051341c525a04103840c0e08103101207001a02000d54980d034005660084000b0043c40710784c0700420001c00c102c600c0c0d80c00780004051402c0e0100d0070b0f0408200340b40e004d8507803020f01809001081c0400c80985e82c000304c1780102c0703a003002e10203000707482c1e5040c103c0365803140340c030786101c081301c00414041001070009009030b21207e09207861358090b41c2030a00070b0321104143c58540c201112000103020341100c40325060316155845c2c525918000c4a41288816990243c0c850401944089000c0066100b1400341080a0f0700c820b00040c506400d224000d07249024803c41c0c00000c6642c0d0307500d000f1003800380940202802480e130454010088104111102c0340c040090b03486c81c41d441c00f142c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 493770035 1250 493768785 493768787
    0x170708030a0801081902090f04020d1e0b1e06130603060c0906030e01050103020f060c031608070203100e0a120c0605100906080a150c1806120513110108100302060d1506 74
    0x40008190b1b40100f10030020b407101801082010005030090740d1110396000001c0010b6400080700b0100020420550302460850501e0803080304020080110038030201e02148101c00c1c09568554851021110050100ba0707881c015801000e01d904004c00c0c1c1850810b44a06464120ba44c50040350050ba409216594110009600740d403002e1100035040703178281402c800c0d1454020081d000940c5401e046a0030003a070700d19507080c604186901507820600015500381941003d20900b15404410901486840c2c074040d0540e595034a0000c0c0903003551810400b1040c03851164060718a40e41d0409001d02c442e003080e0b0030284c1c0004440c4192080030b072404100040140c00800da5071001a0001900c1c0200810306d1100f80103066803020741000c0060303051340d5015550b008a13410014001603900c112886041c90f401c0d80440350040c0040c3c4601501c19000c0380010038001210310343c82d83c01e1030020040d8440500150303041201e038200030350140700842c030b80b4000d00310303541b03c0c4201190941010a0f01580d9902c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 493771285 1250 493770035 493770073
    0x111507092c0708070302130b03070315080a0f022706040f0c02070e06060405060d0506030105060a180e01020c010c0215011505070807030516030309200a170708030a080108 75
    0x41c0755400d00c00000030342094000c2c00d034207500c511541005407030512030908042c030403115500009042500481484001681032203091070100100880c2039100381812601e56032003035103c40003044c01d000d0101030303000c40d00c035034080309014010701c100940b0303002165000d41c886500482d09180a1441e0448910410056002c0c83c04044240c2d00035140c0356007001001c960040c00104102d410075407c11000a207612a03074024625600901c02c00031340380c06c1010405007500c0380600054401d00351141c05100c4d6990381001c81822592080740068103048001449029004408107403005501c0c0016a0740035680101d000d0240c40101c0c04106e00e56030f02c030141071b00048a020602d1000a005004070000104444c0c02410301601904000e0704100024206011003440441d00700c3c0000d45691205042104111440014400300034036000301100d11804107461303800714880d810fa078a000301c0380181c01000c1404814040c1130380605a03565082c500801a04000c0280b00e01080c0f031080101203084528142 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 493772535 1250 493771285 493771349
    0x5011214120405040b06120f040312090210050c101d070b030106050a140f0a031a030a030f0f030b0a030c03150504080906180a0905160c0507030311150709 68
    0x10a01d41c1c101424001840010684e50102a42100c010003502e01e4515a40601c1449003580c22520390113440c00d407400402d003905103460240110309295240e00160b545070516141036016290454032081640c0545150003a400040c014880c50318030005001c211b8407990414503a000340440710903642d50526100745100034032030b03040020800d1054680e040c0c42008050b0110303650a1001c0c2c00c0881d0401e0803500b079440810b182e8003007560b130007200e00c04840380c406040c0c40c004214041c00007201d40b9240600464420b030011820040a030701c030f06603040d0133580322400626018164007600e640364604101004950301041d10b0900088022042e030401074001c05108941c841d54a070304020007a0284202504240382074049911018900001c0741c032440d103600024041c002000c6a0f90a0403444a0258085411183d0402c030b40f004101010800002d5180212685450481e14020360702054900304400d40208030b07101c02900c0103120b0300b10703444080318060b60b1144004d1200a00c4050f80c00d0281107205c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 493773785 1250 493772535 493772563
    0x3030a110403051203090f030d051006020a0506040b090a060609020702030105131502030c09060c0a110303040608060d0309080d080702060705271c0c032a141305011214 74
    0xc0b0103000a13144d001464000440c20201d0380e007143d40060641c11758000c19003481c00d2075a603008101000c8507940b0340400504642c00500404007564172466181c0310010009086403400e2008240003840400c8242c085a41050040100a45685a83d001781d88400000e9100f503003000301041310a048460040812940600701e001c006829035900d60180d0001064841241c40170300200d62079464000080204c03009090240640e03e016282a0030b80d0400d209510b4020360007408140801034000c07034030940000c0c00326405880d040691a04542154481d0440b0b0b442c4c0c060041d481d41d4084d00022502e008644079001d807456170b5181103044031a806030591a58401040c50380d82c2254400381c00c0c051224000c0a8400f9401001c10199406400c3c42a00126550501c0712020020312010504000c487c00300c4103003071038a2100e55202249242c0c0d460049000406c041c240c5500c0a54030107801a000032440c4c00c4c14045507940384095080c8640503901030f0307840301440000c0e60040c0380114040001c0304038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 493775035 1250 493773785 493773793
    0xb011a040e011208091503101a04050103020f0408011401090c0305070c0809030c09010803070b151008130609080a0e010311030a0b0d150203090d093b010803030a11040305 75
    0x42c041e2610070b03c0c80341240c04d9501c00020001041a074641040102c02080c400c6e03c456a00e007005101500d548205070f000280c1d51000095002c0d081500e04203c8044810034a800741c4c07210168010b441c0603204d01d07407000750a0740c40c1130000503601c0510600d070350403944850410054000110000d4080c0c52080381c032040025103e2016500190f1500007034290050003070102c485080303402c8040313820414203030450740c0035070b00c08140002003010488011b688901a40c41da00e800340c807548003044040341d0b110760075001c1c0190840051809a0b4003503d81c01800d4101d1030600070303082c0f0340c10700981c141e10240c0060b0018801031200320655000b401000f08800040c1032907480c42d6941e100c0c01008203074090364690b120082c40045400b1a2000d148038000c2262aa40140d5a00b440180c440c60440a42540018072400501c200999014499074040900c003943e01e49500400c0001210059802ca800c034915180071140080352506001010314032400ba00d00c001c12030b01c003a110f02403145005030303c0020a6540 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 493776285 1250 493775035 493775039
    0x40c05011d04060602300403030818030708070c0b03040c0e1302060c15100e0c031003020d05060a0b061303021014030106170f0717070e04090b011a040e01 68
    0x120a0041e001d040e1040041c1034041c0300c481d00040e0075100d5540c40306006034400d84110440001c82c401c00c101c01d034103003503482d0032918a4041c00b100c980540d200190130700c0742c1c4500088035040e80141010340003001c0c50581e660307940300e46007940d01074210480580320000845c0d0081780349400302003107034010b40c1c1000e035406e240c0303140000b0050282e2004000051294089640c42c0c0141c403894050250711216402800d090100703030810081403080202200c6122107095810071184640d50001508520310030132041d541c0e543d00f04103590084180d03000a4000b0362010841080c0100840e02c50300401e100744050100300904000c00019000344010044042c0100303c0400042c0740c0007000c1080b8042d00e0420201102c62552900c2441e0070903031042011444103064840507a0301550a1540f0001e41003100e078140c10106002008503090f4541d05480100030004100118018100031022440c0200144600702d017501d064032880400f84a142d044604031a089503201c100d2406443c10345003505c1100c10fa03030f8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 493777535 1250 493776285 493776287
    0x2060d15080f1005014b1e0302091f030213020a090b0406051c11300f0103122705120a0506060d0c0e0c0c0f010c0e010e01170f0412030203040c0501 65
    0x404404000d4242c507181c3e4900b1240b841006d02e1446c400380150383c0141281c2d1030300c2802060003070540301e2079091025105c0c0610040c0e40311040d0580120740100c4180c0c800c12030100c81a0241307060b41029600402c080101545803400f40c00403e004429075403883e000554401d00c000c1140102c1c0a0340010030030522001580701500021000030504803a8040358000d141c02d404071465100c001014000641505080c5a40032006100315560b440e00c1c0c162185c1d85440e1600d500a880c06020040c0300c035286008a9048a2241d0340300094254008024091501410074140a045c03091040c10300401541c6524400e1032404902c075000036802c0405031600b691120204844406000402c84050382c000710003151038465000040c1c450b03007651410307590380c01c60303640744510342a0074408095003a810300030380c103000c45e5202d940c060380c0d05020f00b803115410543c680181c41d4003041d01ca010141014007404c00c80c4100750650a81d000c1d501030130111154401603901101644000c940240005154690411140d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 493778785 1250 493777535 493777589
    0xc0304180f0e120c0705040903032301060e0d032706090803071211070f0306050601090b031311010e0904290106090515280306080a050a02060d15080f100501 69
    0x4c94944041d119002e07140d000050407144001c0c005e400096440354100c42d000074512004c4001c102d0410f1230300840d03140c440b0081002111062f10350181104403190003c041c0201c000030344001c0c8046d000400341c2c001c000c850303c298916101d00c40024120182c0042c03c2000807080740d08603604500c51a07034241d011181503500c0318420300801010720440c40d00080c0b0f030b03442e80c445e04045c2d48981e00204040c1000c0000410114542e003104001031010002d000b08406040007025000750700240c000a00060000103940058240d450507400640810401040014002c0d540d01194102d02c000b0055101c40d4445c00e1501200740107450205103040390900a901e0f1480c03160307400784a9a44c5903884d10303031000c2924565030709071410f42071390406021500d0380d002e8150150354050540c1d48000c02d1480040c0d250646d8a05075904003034001c5000140814403942c00303801040103504146008081c1541c1d03040310554030b41c080007107100207010f10340881e4040d840c02d010b10b9040356024050a03d25201c4d45c0e12050f46 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 493780035 1250 493778785 493778797
    0x11a030c090a050909010903090e0606071511040e10150504170c10020c210a06090804051203040e060901121e0c060306050a1205031c020c0304180f0e12 67
    0xb1018652000081c66039a5041c03d0b40300702440d10010071080700c07a14019020f040240c01c03091440c54100100301407038546100b07403900c26030080c0c580010045a00c082c60001e06c000d241c1c00da1259000140824900b420100e410300880b0004140c1294030b42da01ca450000507170803a010700004000b00010495443c1035541d04540b240054284c3d126110301c8000a03c1c408142942003015810ae0300c0d09030f1091402c03050743d81c1c828203540181901544a510070b141c680c41d602000600c00d070f698101c518140145030301654090075020b012811801114050651740b60030a00c294401d030241072000070f20034104130107003904840c41c04202c000f1107a260782c0c1e08032484007600c50400019205030720b024049200446241c1c02803042d902c0001c0c1d614101000d115820f0102d400c11620149070099203030000d03500000703c41c1c00d0041409101c0e59482c0700214280070748030703c1308003100c648030110703012459030343c2100881e4103400c000031b081204043d070303004a0040c2d03000401054a69007000200c02d02c03030f01c031035402081c0d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 493781285 1250 493780035 493780039
    0x90c032028020f0102130e060f03030a0f050c0a0f05060703020705060703050601030b03010617101118010215040501050a0b0d021807031401080a030f1409130f0504110306011a030c09 80
    0xc562040b5059089070040141e05446e841c2000080103041d40a00c001500860113454820040045d070000c00e98038801c84038000c00b04814510f4160001d4419030603248002c80f04816240d200780a41850000c1c81500d240944190107000046414a8001c2c800c880420b54050090700b56540d84110035001418010011411b040d1031390320317443c2e050380c00703210b5500580691002e040e0628001c08219282c20786010300d61945a00d014000c0d00311040d90790640b0199809a190072004400820040782021243e42c041c0d0182003018092000701700c8107401481c8241e81040d0b0411a41c001d4604010902a000310040c0d003007154444280c84020740099902c2d8040100d0501250498034244245440c4400341c0c00000b140d000310f41c2040c10194440d40c0c1e0182c010380c0b0300d408043d45044441164540c030400107082c2c400c56007071600701c6218145402c0818403c0313482000b00950b190034101031039803008841210741302e8001d001c00803d41c1401c181c09040b03114480305005003035941e860b8840b0364640c082c0802ca5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 493782535 1250 493781285 493781293
    0x50d181802220602010c0e0a031211030d020306031b0f0d170a2109170304050a1e05010b01030501060215090a05010606021c030506100315090c03202802 67
    0x400100550390b1511200401052810086250000c000d00b141d800d20784a03010801c807040740719030550b5400030b03141c1620b400020000504d0041c19040d100306c42c041502c00007500010038580d1600b010365020b503211b400103906840c031260034010685181011081000c0e80400040c5048800e030414200c0c011840d4400c10610300300030485042501990848004100041c07071104103d0127420400d980404001c03828030f024821820706941d1030113115101500c2503079117200400094244141044042500c6411800f2045840766044c081d01241d0480c50040e103540d0300709000c07100e29522a02c42d41d81260490341c06818040801080d440c000038000d4000c3d0f80314401d03000303146d011420070b100e040010502a00142000403017908900c803822051030f500c00a2500d00800c00c0b01c41d13122040750f080c100c20180340004031050701c06911410180180c001d00300c01c42ca090442c2550f41d4166000b18203800380c0c8520b940e1103100341d14503c400c601c03448a02146900942e00301080038500c202c8071020020707450042c0e03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 493783785 1250 493782535 493782547
    0xa0605030f371808070308090a021c02270a0b0102030409020a020d080a1b080703020d050c1b031e130b0f190e2808030c060103050d181802 61
    0x145281000400351080e405404582007040c00802d40314120070042e0841d00d080819201d9265a80280524a00a02400030a03000543d06e01018018080c2a079402024448003010200b0305071010030750760000b24015203140c00701c01d0407019200011528817034440f00b040e0540d030b0703003400d924007604005924505511040c0800b0804440e01c1c00640011040e5600038054200b01c0e5400408401016100030301039440d00105802804a801c2d00d413515210070304060415071507103a0101d0091084202d0075915920301028020660aa04010002c891b400411a000c6161040041d512485800c044061500c0a803080c2d44168038184c0182003000d1465464200301982c030308292643d07504c074226841c90300c5400500c1076041e283d402c05480300c4019610700b50082203000004a10214640c0c50105901c4a07440e04403181130030900a0040a01803007000e5a855514411403d5901c400030300048a00d8080d405908500511421510801043d906070600020b444c10460686001c07181e20304c0c1c8807107a001c0040c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 493785035 1250 493783785 493783831
    0x11100204030515010b0c060604051003060e0604022b0b0a060b0d021c020a1b02040b12010b030d020c0d0825050c01020d0206100509130501150609050a0605030f 70
    0x40c00045008402401600030501e00c03040d41e0302c40580010100410500007204a00e07000900103501c18001d4400044a8031041028040391070705600040241c0d05103a0304011281c8045801e500951080d100b009028841d05d80501d2200e500c009806aa41341c200e040d64046407112411581081d403403080042c0c155121003042003a64030150007041403580004558160000400c540058002c1c190400c504049c0941d10040c0521a541c102d408211040303441c00b000c1d580c440c0d200c1d05015000402c1000d881c400418a1030207016800070f001c1c805c0c059462040191800450030040ba0030000b8a1001404a0b81d1740d111030315000384440c216030700c6e070780d09102080c100e004240c0d1038460701a1000744080350a02c00020300d4890748980500440d004041408a05c1d1a0fa041071303030030786200300c81c3d206050f5178a2001b6110869541c5c0040c007958200b403561404110b415100074140d59a42c0e5070f070f1420070b4a5800380585030105118500c0000e004000003500041504090f40c0c001030b40500c100341d0586d90b0300e4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 493786285 1250 493785035 493785037
    0x5040b0d0f09020307380306060306030f010510060305010e0709030305361215061e0a0303081e04020904020d03031b081008060412034d130303111002 66
    0x2a03410302c0c0e1081c40d400d2400c0e10715084418041d06d00040d51a03000482d102012840c040135040500034180800441c01c1a034062201c24401c2e11010020000c0b1300d00700c0300c18140c2c1405d51141c1c0012030724103800811140d00e80d02d0a2481152980c85031204a461070b03804440680c00a810390300700b0f0103280c624441c220143c0c00c0d01e2143d00e401107180202d41103402c2c1000203803050340c4c1c0000000d80c0036143e1600c4460003100040d510020480d141c2e030b80c03201218800441200da15410560100d540300300801019003190200b0b0117090545010380c0485103000d9185071003801078502039032200342000020300500d880d42240100c03a21a14000c2405440160107103101e8203840c40d0203021034800302c2000090000708082c01c004102d22001030409017040c0d00d0f101a0900461030403410561942c01c201061410381f50307640c5003188030081c0e41c0122502e010445002050710350101140703030101d20003114681d410500361068920060003400c9000d01d590f5060702c10b440c1000038058180030b00e0511020182580c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 493787535 1250 493786285 493786289
    0x2060a0c050d050a2d080a24060306050a030503070602070606320a03030e060a030e100e06072d120c08150306040c171c020102070302070605040b0d0f09020307 70
    0x926204d40710136242c01c000c0c1c07941c2031181102114800046220309240c0346891030320ba4902860801c4071a81d25006006000b07051032500381c40800c900c0d656514000c01c030000810040310450341e410071995440d041001000e0405200c080d00507482804200042040e80e0b00038034440b803050000083d20742c1d440c00c41c00603003035445801c4105d0704c0040c0c40303151070120504130314140d895044810301519030031070b0340140c880c401d000b0101c3c2c041c0c0b01c082865101c45000c0d0b072010422512038001c61f00342504c0105103001403c0300720100c6809006500c00f0961a030300071a5425074003800400c15804421090010b45640325025013000e080092210110007036080078452040d040c1c03240d0395200e000349881c4044a40c1c07402281c0146000368003100400000c6660b151481c2c0c16034504098190010a4031515145400c0c004511400784440c003009105107140c0550050882c40e1098090310085a07981170103440d54006c51180000e2103204224211100815521111a1900300200040d40412640100c0e00c0d0030200d03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 493788785 1250 493787535 493787537
    0x1d180f060415050312030408070209191a0f120a060513050708060112020603090f1005011e03081804140a02090117060a05010f0c02090903090109050d020d02060a0c050d 74
    0x480103221650600740a400750300d0412a000040803442c080110f5954000f0329401181c0b15030100102d4208107911044400081e001028103103c0e081c180820713900300c100e010344041d08a180c9245402f8040350313584540e0336207000030054441f602d80941848020449046020424015564480001007040c071074180291030a80c261071003001a0703c0c00da841c040302500003081c660311200041040707818a0071004c840690655481d500d0391140e206003480c02c04a00c01e900114083d5074000d109c50004c03607210074100c40a810076a420307400c00d420040b01d618520300010303003201010888880c0d1481c06042e0440e01c0500500009800307410b034601c296980c1010b03541c0100258002508103003542e4003944149a0113140c141101d02c6081000c001850811240b00710350511948031081459540601c0e0000b541c3c0c3d801400d810300078901400003e4503940403c00140c0070030301004000c621420701080c0003803c3d0f84d002c1c0901c08080215020040643c00c900141c0c0d040240d4000b503c00000c3c0b092240c1c203600d0b141 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 493790035 1250 493788785 493788811
    0xc04170609280b0a0609060e0c1b0a0b010e15330c03070624120b0705040518040204110c2a1203090102060105060304200f0303040f0f05040207031d18 66
    0x41684031015641c10342c7c404002904004203002100540200310b030010080c8061002b40c0d46520038980e424142006409071258030150000107007003040c10b44540c0b2500b9040401c0e00400c0f005000c10811030228000ca40a10426440c1e0620345d0b020a4110103034040306203005420040410141c44c6183c0c800c00088030142d8940d0710080b20610b802801c030703190440b070850301403d40d400c02c9200c509010341c00c1e001070300c0c042605001c44c59050040c0200d070040c1c18003401c40580c3d910301d48040c1c40c0c1d40c0ca084e14200d000398a00b6070000c00003c41d101c240c4842d4084070b805820b90500240b4038800c07000300e002d000c0700c401600160814103550b46102c2c0210f54030800010b1a01c9020701d10001e4200f0394141d0180d03000305001c008010000303100448a081c010b00c540d41d40d03285c80e08181c0c0440c1804030502c070b800740c00d484000b0b03001c6004003944900608561010590720740c0c0c030f5100c40a00c01030f070083e00700080100d5881d884035088100e08826003d40094081c0c1107410148510a01b82c0070010169412418081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 493791285 1250 493790035 493790039
    0x3030623031506010804060f0912031d0601260114070917121c0b09010909060e030a200c04020d061e060e010e0a0b030c04170609280b0a06 61
    0x5040c4801900d03524000c036802e400340f51040000c3c0c104040140018281035403201641040c2d0110350126001681100481407400200c0c0b0028008080752000010b00c0d284d443c0002d01586000100385051316162114910802c1d241c00030240503405000e8021071654135030610b0f2a9200074010740f00c0c4101b1240c0d1300c40f200103242544914030610303940b07114041f0380c1041d1801035064070b40701c080340c10050340c0c00d2545286640a12000c0c0042a194a07002e5100c1c907880d00000c2c0307206803508298426801101c1c100814400ca06566550f4400c0c940100003003000c03520200000306c050700c0301e1010414018240c495041e00000050126031050082c043c00c2560b81500b4040304102258040403401c03a2002001c043c1d05111010f400d010744541c201d81081034120380034405445021002d402484220801901da0800c01c4801c08030742c1060065424403603202c60b404a84400025846019540b140064914000d080300b02c4000a00c00040c4c050a40910124090001e034a524125100d020810780000e42c00e4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 493792535 1250 493791285 493791289
    0x30f020409020f070201080a0c0504230301091110020106050f040908120c04150f081f090207060905150114040c1b0303061a0a080c0307020a15060509010e040b1303030623 75
    0x782d00501021301c01072800748542708040d0800201d07026665941d0b40d1882900700d10a02a03410034031001030f05d0301235080040c02010030035007000d0442490030864030a0358518000c40c080b800c03142184159903100103191503810183c14141d0041d4902ca010305807680c42d00d565100780e1001688262420302e61410000b40402004200011598040c807903441c0c0a40743d089040c0b0300400144c000b030495171090b205e400b0001c0422444602c544028031003144207544840607810014000c1041d400240c401d405a1190811303000100c1001c1c5050304c4114503040020389a64007484010303c403403d034100c2880015550700f11988000701c076014140d0301c0380e070300810b030301d42800c1d5912443da41400320401034003c140401c2c0160ba82000755240c0c021040540036440e070b174580b81c0403842c04c0c00014003e4600e800150803c3e4030f100ca130f0341221003614070540312324100b0b9a0385c0c8112032061030111400741940758150040350188042c81185444a030080c5408920161903050907400b1a491034076003e0207000810350700ca0b4034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 493793785 1250 493792535 493792547
    0x902090a091d150a2007110f12031306030c09060c05070f030b1006030e0316020609090c0a1806050901030b0109050306090c030f06090a031b061d1c050a030f020409020f070201 77
    0xc00c00c041d401e80c500d92500ca00d800168003400300010884403030f0149801d0123444052150503030040080101100302c200d2100745460794805d00c03000255101040000c62564060300542c203406000350b0301d0b400140c2c0342030000c44e016244200212043d0080b00300018060700b08209d1440610b00404e03c0c405c0a0410000401010402c0e60103001854180a801281c01201005a0b1307031441c004a20710006021a1000500034465404541c0d4016480410301c0001e05980001c1d00119041e40c4030980744800740c0d000710700032000920440b00002c10070031606d9160351080c2c2206848403018107090150310340354030000e814901e044800742c2496100c03c04212892800300b1201080111030f101808003404c0910005484d030500c9400a000d000d000410510304100f01e020242200f80c211208004140c40d04114003084a44030000e20303000e100320b009242510360001514413910000e5290785143c900d0007003059000e0003650a032540c14650a000000350380280b400100014000040343ca90b17182c41500c000b42030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 493795035 1250 493793785 493793801
    0x50309130b010f03111603120203090a050706090f140d120f030b010905060409020a021006060f1e17091203090c280902070f120206070201060902090a091d150a 70
    0xc0604025805400e45003c07400c841a040006c90200095601d6050644804056100343c6000500c0042048505103021401c840700034030500a0ba01201e81c4d0343e00880d5424000d0181501010030183d0802075028180102d04002001616610300101c0a1b250184041824070014000c1003424684c0c11810354584034035984c000d0242454030805040501190f0345001c0c6000c3d0032241c1d0ba00049224849000f0400e1072000001080c0501107a078440c50006d000c00c460131700c40400700b0700c42080038a0b40c40724034940303034440c40303066036600070030244201c40c50701e078580141c08600207016440075910780c0c405810003948a03500750300003810020034900070720101c5a91003400ca2001c1c0c12840510840550240115003180c501c4800561a03601c4d0382064428002481c10040038a4174100001c9801a008203280c5d1240d0015002045603da4804401080e4441c072200568002d0080320244406a0300b0b034003005850710f2001d6402064050101e200d490b1107112041800307008810b1007000320025447c01070801d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 493796285 1250 493795035 493795037
    0x130b07230f090d021c060e0705040212040201080c16030905030d02030f0a210603120f05090a0302010809031e03090c0f0603040605060d020901120209010914060904050309130b010f 79
    0x440e207410140350600340c0c05030782100c62003810190000c07001d664580501034240360a0341d0710304d04803200d585485001000b41d4215065140600031000400740342070b00c01c3d076184401130000808299241c0d401150603c0740104080b0b80c000d0180301001848800d550502256031081d140c5640041c10b2408251511200301081c000315401002072800300341c01041900c10541b9107050000041d00c281c07048100310505400a1803140d4070340100001403001c0c41405d068a08102d4540344549624850201d8441c416052000d40040154a040005502c1032000b181e01014940559060032003c0000300074402c4644102d031000702e00070062008010b820f0103000c00340c40c82160b0740c2d11200034003004038081d40802400513048540d80c00010303000d600c2d0340b10754503060303540141000d0180d03844040c40d0345822a001800c0e4040c846100000c58040e40358801c00b401c41480c1c0d05222400c1e86c0301020050b490750000c01c100d84a00090102c10040c0d1960b40300d02e370500c03c0068001ca81680d886000410741404102544 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 493797535 1250 493796285 493796287
    0xf060e01150f0e040c08150d0203030a0507080f0304050a0c0b0316050702030102130801050106090506070b01030f1505190e0d090303030b0312031f06020f060609130b0723 75
    0x1005150300c004001d0304809042220514404000903038462200189642d041400c003507030401419030002c0c0046c490302c00001003018a1103020144003c011030380070001d400d43d00400000e00218041c50203024035a00c2800c01c64907200007070300031036280e40084d10105e0b09a13010307130800703000c010018400001410052514a0540c540b103032070409203101010154060040010754241591400e404480250442000c1107c5040d503400100703000345000d2080341c001444881000c2060f14002c0c04580c9101c0c0c0288102e03005900350b8a0740c4cd940080c40408982e200f0b13010203190352855650145a00c40c25440524000100c1c0c550841c40a440e241a00882c054028410207005a0380000d0f820040c2d03505858006032001c0d00c1004245005000d54010000d00d201000b04010840820072002e04401120755040202c4c2e03803800305a0341e41052803c80310040c0c00c20000034407103080c600c0407664400c2003800c20380004d541544900c2c2c11020141c50001c00554030307450101d400d040e29403094041e600709120305 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 493798785 1250 493797535 493797539
    0x50907050313030e0d020409050601150f0806061b100f11070b130c0b0c0a060c0201060503031605071508060117060607080c070b0316080903030103020f041d0f010f060e01 75
    0x6032051902c000c0c0080c10301c14540c031481c1840c2c8403505000e100c01d40c054000c211510042c1440c40e0368001c244a40202c0c0b022404c1c1c04030815100d84000d00c8039032169100d0051030f80301ca0080000b41e80026155200c2c8074400310810400e00002c002e48c1807c00610180009d1820001042000380d0b010b4810005142108000c441c00107041041241d505c518114500c1d01c4100036460141445a2250b000003c40724000c00c09224503980460740340340300d51050f082000789141c0d0301000d0f0700340c50319071180c5a03164005200c801103840c03182c2c0f01c24410610590584803120740340c0002840c0c400b491940c480019a0000c104101543c12803185003890510f424201424a06400084c0081c8110000241751880114004007050702c10403640002e0061707220580d480e480d1200c03034058450100001c13600007a8010b07010811030407020040301c0c1a02d4020f40703c12510000310080c80054400040c009422a54410315981060030a00c6000c804d50304400002c145e60b61064504419682543c04c8512034003915801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 493800035 1250 493798785 493798801
    0xc01080f15120304150801053111070605010303080f09060601030c021603030f1205160c02031501061d1c060b010c1e0b181b04020403020a0905010509070503 69
    0x2194400003442500c01c0c04280040030800c90005980b1003965840081804aa490300d1107001d200300d82c0c000e41d40c10b015a07a03160104105001c10031620449041b02031550b400724020000c1982c01c5045041010400102c1d20340807820541c441c070010380b262540c940043c01003603801443c0c1e40c0c20260481041c041401d2240401c0c2d10f030b80340541000c0c1407543d00c05e03199080c50f0007405050301200b008000c44142c42d81c7e03410068281c0100700c4000000a980c3c4082c40200b10707403032007501e01800b00304e2200220000d18a030103540d410b1940c54142da041c4940f0b186641c3c580b542015890180c02c290703440e0306010040c1c2c41c00200b9618011003043c0306040c0000881046540e2800e8084459080040400c0d80030f02200183d5a002001c04047d00c182e403641d41c0d00400d0101c00c10140816440f1383c61120142d40c8461142c0c042801400000d281c030b8001d00c004005072806d01c0d0061400000c000d10042c80e160340c0760300013050014a80d000501e426180c80040065142c1003210030303400811414034030302d0361801e215 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 493801285 1250 493800035 493800061
    0x20102071401090f120302011b02061303110d03060f090b060306040f09020d1101020607210c0504120f060605030a0221010603020d3903030302091c080a020c0108 71
    0x406808001030300340072115030b12030b80d02c030310080264404120b051a212031800d1401c080c6803c044d0003541c00d002002e40500d640c1c80b885000d4104a80c050446034403250300e5039013204401401501005900300c1400f011000c1400000240340c0c043d02c0010b501da2508841d8a9481140d0b40010005e07481c000d05699161500d100312035101c02d089800049114000c6132a07030050a003000040d4001286105500400c12900a00c2440080c00d808540e001d0790b521104a50901f02c0000c49000c040c50f00b001c1a03442800354002425103580c42c10014141a112210319240410121094800144045010f003d1103070b0b034407a500240409401030056400c00303030041885480c62140b03d000c071454400c100c290001d000e51000c0c1c091039004007500a80f05032810010300b0328407104010f54101c0c1440000f040020b603c01c0d8103035914420020020740172455501d0580c000d401001c1e03815003007028514101105403401603442800c5101d16052900e03844c0b80200245030051101c0414140500301c4244452488452 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 493802535 1250 493801285 493801289
    0x7080304180f0509160e010501050406030c0905091914010f030201050d090629040501050306190e070e0912070305040905130c080d0e01020a1a0903040f0306140a0902010207 76
    0x40204211501d541c02510700520150200c004864030f00000e20849110101d4501200b10b0001130710300380070392100300074128201c007071064030b001c030b0001c01041006030302942010041d00c3c0076080c210366069582000c40e82c1405c003118601400414214905000c081500c40c03601e5114900c1c414a94035810644c10101441841c0006818008081002e22242c409074002e80303480303507000b0b00034800c076406140d002c0740c8060b40c500034021385551152030000c5401d00c0d00c18181200c00c010000c0465469050f081000380300703000c0c1c0480c4105c1d2152462a5012400c004000081140d490310041c07518040003003504040c0d114180e0402450200207082c003207070740882917609561100314002411307250140d000d480c8080c1140010a0300c1141c20002405800103d810865030585458003104806004012030301d40c001c41c1d00040c0a6030300780c8001c103d407040d2181510780c0408880b0480740f6280c0c03140c50181c00200d065100715600e58403032804140d40ca260200441d000b84501c041400880c20319800070b92503079068 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 493803785 1250 493802535 493802549
    0x20418032a1211030f0a050405040b0316030206030c0c0f0303040b060a030c0302100e03010e010b03010b010207181128020c010f0503150f0d0309051c0c0905060102150a050906060307080304 83
    0xc1010b01c5108101348112403203000b007000c005681c0c00800c3c1010349150010711850380301d2403070301d29135480d03604011136203003001a9803001030025507003140c1c02c0040b180c202910080708402c050000d13900d80f410810080301800500300c011526072400c0d113041e240041c40200900d0148401c0c100420002e00441e00c1ca5094076811100e0a42107480518110b0b28099010701031a4158242500518020411342c00a020307404254000c0c040c42c08104010780c1c1e02c403105e1144007202d448011130b250505010b40d1002d0f2407500803c5007103281610b44004001449022100150484041ca0b44007030b5454040203074402042003030030004c401030100d1001810500004005c1910090580e4609000740d6039001111014400144090f844840a0400810003c10b901400e4091414140c0d00590358481e0f07949140c3e110341c4011004c6207141002040400780c680600b40e2410b600c41c040c50342d1440007100c411284078425004002400c0d03d4042803003440d10074051b2007a8040e0f00054002c1c030030580040101c81c191039032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 493805035 1250 493803785 493803797
    0xa030312020a0302090a0e100603020910120b040c17090c0d02090402040e0f01020a030608010b21031314090f071d010c1a0f090102160609020418032a12 67
    0x4502c040c2c01138403484042582c0a07503440300205841d148400454010130442c0d5024100726140c100c254128032820341804ea01c04030354500c0d051494401c190318030303084802c0d010100e0322211590200e0103895081c101c01d40410035800309000480c0c14814415480803070380c03004103190740e01980400c1da0f0b010000340c0a4001c182800c009029901c6541205405804034021103281071130b455890341c000e401200420000034144200010104d07414000c00340c070f180d0000d000c070041c105030a10920450001c00280b00c001d0005010081a80d519041020018900c00304e1407509000310004004401c00000c080a899010500502400039407000f40c108050b9441c8480f0036200410340016030790000031450007001442d1406036040078219901409000d483c10030000241e41d1038001440b8241c0c015010300040301450b1210040c0800c115400011005002400000d18459840c4000d9442d8616600035000302da41018015400008100901005245035451040d680c00655a04040c881112030039010848 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 493806285 1250 493805035 493805047
    0xb031807150e0d050d03020a090e0105060d091a0c070204060605070b04080c120304050c010207080a21030e0d080601120e100b01410703050a0809030c010c0207050f0a03031202 77
    0x4031084001c05080c4c0207800c850442c100c030701c40140a5441522100b000a60059002408501c5000c201e41620401032180d410f0440130981c66006066003401a1094203106d05280c1d128402c80c030006020b00100c1e8600d958542c503a00503c000d80740250b224404201e010085000490b0f140f14101d0f4202d030b44240c40560f19100e10406907d0a0703410314000c0300d00040041440700300440000d480a0010302038003a03d145580d64100c0c980c840050000292680101e00d542c06080e8238002d8903481d2920607410000744041d1169025481d0070001402c10011507004001e000c21076030400040c010032002e461051103410f640280d4591554000203141150076210340d402010b81c3c2c00b80c40303591003101110a1405c0c424451400e1700344082c1500303402c41401880b22202c244484440c00403552510740507210396107400901503003103d10300c000034050780f5503003c24010f54000000038040c0c40c50101e0951f000b40308072810030f000c12402c00412070310700348030300300141c0c0410020780c014a0102000c54501801030b2100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 493807535 1250 493806285 493806289
    0x11103040b0d05090f06090a062d0e0106081f09020319051501092c0c040606091a0406090e0c12010f09050f0403081f0b040b031807150e 60
    0x1024641080894120101d0108608002c81e0f0185108841010032a010b07483d04080f51901c0b040141c0d10280740743c002d6004c03000480c4198021409800e0004144201c0410841d180e030410031004140316680c0e92039110343d482d0300000740180c2000d440240e01038855691400f040100c4291030300804c3c49010380b281ca0180c10f56409100720a1290340104003a40f60440314602a51500c12840d0045400e1a0300000803030001c22130310a49082103044401c007201c01c0c507803101c07212400c0d001d04020300d040d1203003034007a03281c03900e80e401003c00802e519190380444908003d0780d207040e072a0320701900c0800c4400380000c0004c968451003910440311081d507c90040e46403e07224140c00d00c00c10108070342d200000c0340005002e01d0604d03440b0381254107100d020410390b140e441492080001c159405000561140c1c0071a410840144e01c208600c0900c6684021482d610744024240e03810503845652000c0d004402c02944000c0302d441e485130118420060200141001042800c1e40400381c03140007045840d5680640c19 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 493808785 1250 493807535 493807537
    0xb03060118060e10080d0207060e060d0209030a050303061c05030f0c03040f0806240d0b1518040b010605070c060804060b030303150a05150d0b0402160b04210c02011103 74
    0x502802e80400255140c403100c4d04c0c3d400c99183c8170302081340c4100c1e400c01170710600c0419031509440b41584d55284801d00c400811034150800741350f120540b80d00300030000d03555408000c9000042c1c0310300083c58132454248108140c52140d100c20500400e0b0000e95140051408811102582c0300b01921503100e41d9501c401c6441c60107240c01004885801d444c0c00704900400140052090100701500d80c04100b24880401640710842e00c01500b1031604004540010300e4502c8181d48004030460301d0307003d103840c840003c5d1040103042c9100807000b446002d1005000c03401100e0ba01409140c03c000340381101030380d51550420002c1c8203035010882a40041030400000c1d40026944480080842e900c03810101c1c40340b1400a9800490380c4108003030704002615060030fa805003110b50254100505001e400305851000c1c15020b000190700c59401c00200e62406800d68001c0c1308580184000704281c07800d46000c41c6940380314010092402c21059100c59520fa0110b202c81e9015828030b804940a11920241869 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 493810035 1250 493808785 493808789
    0x51206091003020d060504050706050a0e10140412110103110412020d0c06050c01050a0b0307060305061203070804090e01090b071b06050127020901020c0d080d020307080405010f0b0306011806 84
    0x805110000040d040c8603158021b00d008901070016100495604c507416500382c0b04642c4054045000701114042070314112040920403c06070034180c076040c00008000210b039015070444202284000040300601207003000440078681c00382803c0256902c1e05c40350b000140607d00c509404801100304510454441c1116101c030700c0d0b4011700000380552502c80c0600b9a070021080c001c941d42c030300f80c0011013442e03075400b030b0400c8060083c1c0500744070b60030604110040d100c01444150413402c40b05244002803010401460388a028014050725035090281c46410385030500400d03c0720ba810010b688020460030400710b40c210009003884411f12074a060420040e500954000e0b1403149440000900c00404482c581c031101e08080100000d043c141c2c12440c00ca014076a80d43d801640410f180d0241c1d41021514102598000c4100a061140320880c03001681d0040310403900194202c414081008024010b1000032406414144403030344812010a03591181441818010010782c0b0341c0840000c140c0d03100c040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 493811285 1250 493810035 493810039
    0x6071b03050d0f0206070206280b06070803100e040804051201140a06080f1b0405071101050a090b0a09020d030e0a0503011404290103030e0a050409030306140105120609100302 77
    0x10029102c0001800004112207180050702803400042c50143c808038240f44134110442c081c080000082c185540e03c41103091801940e52b80e100811035281d50b40c407001e483c0007841075004940e00d00e405000780d44214880e9004280f00e0741e620b000d01c800520104155015500260b480c004901d403400c2050740503180100d040003401000f802409840f01181d0445426075908504848024803510103160355035030855440ca060100014201c10a4075040d0842d03504802e40b8130f003031010303072401403c1c0d182111010b84181e15800d41e03583c0d603041003008d50008140d0003048a0350070083d002c0c070740d004a140c09401904c02410881200c5120b0701c541c0d203007a614405000c000c1c0003040610181014101c0c285801d660643d000805121040c0907440c00140000303482d041e00000c0c1d151a446c66070b083c2c92031803812140550101c1c5008012800e52203070702c241001e16000782e0b008900e00340303000c00012048200920441c1003101c200000c8200940c20440a500040c0688a0055070750303960311a10f08241058100039 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 493812535 1250 493811285 493811293
    0xb160f0b0a0b010e03030f030f15030718060f03030807030c091d040b0604180809180a0903030b01021b09041401050c220509040f170d061701060506071b0305 69
    0x4500e100c1c0c941d0082108031400e0b29100c82076070202c01016500d0181b0b00c420000c205003040001c1e884030258031090303001480685040e103144204400a401c100f800d4101c044400c01c15000c18120549a0044400401080c00e6001890f400c50f20b00034103403000102500181a01d880807401124403852180c4000c16140c142031400403d1099810b201c07405c1524141c0c5d02c2880003010030340a182134803d000c144507407080c00750341d01c135207a9547c2c4000350040d04026901c00c2950301c05090040039000c4252080100c8c05001500c020980f40c0901241c030300b0000d40d41150300c09100055040c3c030554201407003030012100c0b130015507144d15280d00c240c00030f4490740905508240a00000500d600050188182000800308026154061514102005224150b406114203000ca4041404003003c441c2441c041e0003030400564001000300f049500074007444240e00d56613041041506200d0f140507801110f848002d0010b43d02e00000034419006101001d484400a81809c00301442c1502500f8000c40d1b000307090b5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 493813785 1250 493812535 493812541
    0x20307020f010e0309040f0e0304030f0807020d03090e0a0c0e150c03040605030609130b010902070f050601081609060f050609060d050a050a0c080402030a110a050a03080d150b160f0b 80
    0x80f82e101c2c0c001010140c010f07030a01450703039040c0d0581d0052440c0101e1000041d410249903869107516211161400e0b14240e60410964000d030b200d151140000500039221164264034144000024000c01400040c0d003500c0c0c00a517825550f40445030384030700042202c40d9811404400214440c0317100302214002180b1001a0000c0d006070001c02442c0300ea102190200c0040c0c1e5080c03843c07030030801c0c0060300914200c03a14005008207103182e8080d048940c05842c43c500c03410b40d00e5985500e0200282c10415050b8070001c000c40d00088030240b030350301400131580d060026915004c4100a048a14001c10344101408501441503459400c241d41c4e01d060949414482c03418061a10070040206a83c440c40705030800441075a12401400171502956014004001807005c0b526190001c5105c070034150b5002c00c12100018207907072800c4006000e5401020f890360703030300307c04001c0c0c000300c1d0040c03400c2d05050000c00070100203941d9441c05455010700c1c0604004140242e07440c0100c01c0d00d030030050080540c0012414 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 493815035 1250 493813785 493813811
    0x30b13020c0c030f0f06041707050a06050a050a020903120906070516140402030c0702040b03161806060c0b0712270201110615040f180b0a0b010f080109020307020f01 73
    0x10360401102d003642921030701d40c5961842c80d29070800c140c10322820b50181700880d0008038942200f4051528008019007041219922541030205d0310780c09581c482d8030b6009200c0403010b14800e0a8000004050843c0b030010714401094031a500c160400640182c0410388036002e813200302c2102c010aa02105440d90710140342c602d0011100c00d4000d980c01e021558060a0035801e00d842124060181011050b0610010340d08010203010901c00464140c000c0c0047c900e003c20600710f9900c00f0740301c0002030418482c081302484049524039030090080003214180c210205100543d80d40d0061a07900d007580440140340780c40009811048242000705041c0d1801d881c841c01841001c140381c0303100f40e0361074003a800343c2c10945daa180d209480c09501c804d041d400000039481c081d8404d40c4080c502c10b8000c50b4240320a21504100b8500d00c200313a45680340e4404015501d0380c41d01c079407a80d890003400c0c07181100421041c01040c0b10740c14050642c4843d0f000010420041c001c000a1804851000c001c3c440107040400e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 493816285 1250 493815035 493815043
    0x10806040e0a0f0302060a02040b091905040203011203110d0e0d06020919050301140106120e010e060124020105010b03060621010f0807050301050c0d0507090306050c1908040210030b13020c 83
    0x540046c0600c1c00461158150760088900303d42119011a0410340280200304a034540c18403842c0340c0d501c0922000503ea1202c0c0041d500808000e64080c030500d2050602070600d402411485149030090f2510604042e04034034040e1502c50107070359500084ca81c03441d04000a100d81c0040d65404082592800240720368081d1540a03203c0940c024061001100d071055002070080c02803202041520b0f41d081c1803106a544480f400242d16000415000344c034900b1a420f04a00b031b041400c01208000c0c1783c07407a15001d410000545007061001708815071611040c1e802500000e40160300c41c007000106070b01c0d2070000740f60700c801241005c1481d042d1940c0d50b8402c1e4888060920400105000744140080c85180c10b00c201b612404005940500e8041c2e02e694a5005103001045402403042c5190084003142c0107105462180903804085030380e6102c042c1461000b40c84426505003005004410000180c58108800b28560f42038100071403c0d06201000035241180c4000e451203082c0701064900300190005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 493817535 1250 493816285 493816313
    0x130803070c090f0c0c030f09030b270703080d020915120906090f0307021302120403020708060f04110f0a08100f050f0408041e050d06021323010806040e0a 68
    0x40803c0107803203006a906402e0f51410401d110210b8401c500290129010305080c500d128024948020f0207070b12a5510711641c0b02c01c5c1c0e01c501a054045020906035040c4090106c00050300e10024165546903542c0c0018078411842081111a00860042b03002e85036400f0403007201d507030210071319140d12804048106047d0100e514405501c14640801d9410401043c80f204034004200035510b0200541c080c040c0c44612260b201d0740e002d81c00c0202d044422404403000b40124800d03400781100d18a0170000f54500700d8090800d1303036040034801c18040041d00100580c0030000c1c00b641c014204c9001a0300045410055074424a40350007210046a12658581c0c40054000640402003005848400301e00c526000c044600030302c0301d0070400051000103544091306001001e4500f020b0030b450307101c4004c210803401c0c04404032006a0040789404401900e40045000340040c04c031070181c6c0c10952040c0c04241e600d00d40205050000e0070010951948454010b00070107213014084458211a901e001d1800c0c2e046a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 493818785 1250 493817535 493817549
    0xa0e010c1502030a1a06120606190f030e0607080103062003100305010515060909040f020d0b090c030105060a06110106170604020315150f120d08010501090b040b0708130803070c 78
    0x1d40048001e606409482007219805041e09047c60800c0e441c0b0b04c103400000c0c081542c03258003482402548015131040d0a0f60303007140e503160030034500700000140c1926400304142c44c4540100b03040040140e1301228650440c1e070420004070781042142d612500002c103821020b0048140001001010589c08c4c641d802142d2158008000c2c5035200d01e59040c81caa01b400560383e000320b00b00502141403034121003a07500207026081e82400c140e0350f82c0c005681ca4455920454901008004003da84441400150101e00007034009109a26103d0006640c20086024120500101c42c0311610301050950220001e05624480c9070080e103100e8680503039400080f50b00f05c2c4031380b0401c214400c0705a4403280160080c014000159002400942000b12040c1c040c0703140c7d034225503281f802040ca0b040c1001005115041070b12050220750400c4001040520540c10840211314200400c0202034400c000310380729541c200c3c1a29403100540b040902c2d00d10501d0740725801a1002091901c01c1c01aa1401c800844145c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 493820035 1250 493818785 493818791
    0x9020c070902031b07050f0604030c020406060e0a03170903010e01150501140409020f0903030313110f091b040810061415030a0b0303130e040b0609010305030a0e010c1502030a 77
    0xa01d0741840203078801201c0703d0070016000a820141403500c0e6005e440b0a43c811801d42d0401103115041519058084500350f0000d20b483c00d914055050034400c84000e00040e250002c5981e103d2408100c40c10340e40e100080001e00310f2039241c0b9031515010b0644090f182c008000f446816103210065002c2c01e540c502028820690107400a2558001c120403004020781c10901e0741040e1404031403000035003201884004a6100300320034004c4d9901440118454030748640041044551030401e4a142c001c0c50740c280340500445d00c40300b040390f41d44080072503209820061680e0728000c1030b00c400c0d09900460380011402c0c4240544030410017001c1e0001c0080d1290803a480216000c21010415941c02503109420302d800100b001c01c850707495030380110142800241c2200d01d40710f2130300c90400ca094034950002c49a6180d4905000c108030303944100c02c3c0c00040031200b802d003950461f100d03151284150080002400540224800d00741d00501400c000290000d20f4100c40c21000441f0348044e5008991401260745 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 493821285 1250 493820035 493820039
    0x806011d0a181b0c0624030813090204230a080607020601060212070c12111302040315090c061b0f0c060e010207150c03050d05090307050d05181302120109020c07 71
    0x20f4004901d591a110b59660031401203880e88500c1c000780f415090110f070880d26403c0c4496900c1007102004000c502c2040d0f142d548042001ca02041c21010f6000240c2c2d07103004210402c04004100310101203280d051004103900c0c1d00120000700c42c4044d44d400050720f8003c102c01c0215498002c1080c1e07048410503001e8440c442d207510000100b41c440d480300200230411898042c07000c0200ea09080007044d2040124002024040c03001a03504001c021000c5c1c4150740000e402d1080121425804e242c0f0540003400b0300429005075141d802c0c58100b03020b142c0411010350001004802d10005000b401030701702c45541100c0c1d42500303002c0c64841c8940500c4021589002620005500c001210720032501ca46040b0800d00030415011250051840c40542c10000144018188900303030703110b954001d401d240000c0d1f6542907180b810034200700f0403000480070301400744050340ca2000300e040315400b0150216200009607a491000038001c2c0a801002c09121902100201c1c0c10121580141256a04c02d81142c015035 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 493822535 1250 493821285 493821311
    0x30f0f0c0c231c030e0109050d0e01022a030a0b040303152918030f060402092805040f060c0903020f190b0306060c1b04060f05010806011d0a18 63
    0x240c00038a40b05803644418840204064166141d041c0c0e21403d103000b05404205054513130a5803140481070307546401c02c0e014082819003140c4003464001e002e0010b08002481054000c114100a5900c6040b6605005442c200395500740580b204041e032040c3c035980c00c0d0501d814003d0050600000261060320006000b01d00c42002842000741040074451803000081c0d10100c030382040e0050040142200328800d44140c2c00d50b800e22690144d041d6040042c19149010f004201d0310140c0641980641803209101790411030790394182d0469200c040101080c5a15140f9000c00c01c0d070340d00c50014000d9032074902061041035000c540d0000f06d0740201d43d0050914422000c02031021075052880314044410390003000002c0004008e1580220001c1800e81010003800740340c0e003854054820303a490030301c100c00766107120b180512810001d0150710704501005030401c0c0018040030006001c00e23050007514520240e20041940c02101c11400103024525100e903a01c45100c581100003051409007400d00100786005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 493823785 1250 493822535 493822583
    0xc191a0405030c040204050d030f0201110406122a0f0e06030412301a060a05250b1911040f0305060a02120402010c081e030105120604020102030a030f0f0c0c 69
    0x181d00c0040c284a0341c0c41230780d03130f00b03551003c600050141035540761034407208070042c40302c00340c002041242c80da04071845c001d00041c0c00b201c0f8902040c888683c880711203542130690007800c94402609030b08100d6401c07070b079064040e0340c0070a4040b0080c2d030003080002007000b000841c0301c0041c01b94140751510554140c0e000e00c3e6611030143c44e00088040008994680190055500518410300511700325000041110b40400c1060f0702c54044034002c601c3c000303024440c6141507801c0d0a40707005804c0b90480401c5103950b81d200f00c414050440102c001d804a901c410600b840d03070050052466080c0401c0d0f5855039022040318200051105441502a07140080c04841d0a40202c81c4080322081c503e0503260f580f81e006440000d000602902c8100b000e101c10140115004662402c10381715010b40d0f41c0320b40c50300d0100120280544445a070301e230840d80c00d010060743c00205a900707203952800c001c100c3c4d400700b002900080a03210300c103401c07050030051840c141c1a04002440511800764043c0d49455039501c81c90055 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 493825035 1250 493823785 493823789
    0x6071205090c1c02060f0a02070303110604151a030703060606390503210610020d1d030a0b1303090506130b090d060c1116080c191a0405030c040204 65
    0x6030580d0070702e82c1c20669070303030f5400441403006140d41c0c24000c0911080d041c5400c034190540c00750781701d00030600500d50406459090380780850010010b03890296903100c14041090b034101c1c5011b0310b03206840300151100c24500f03501c01c0080e04440c0050340e24140000502918803440e8041070441152000000319030003045100300c511500108803219a06030201100d140300c00075107841c0418030940c00400c001c0464034104102c20072030300e4154140780702006080c0c0c8048802000750740c03050b50500411a0800b00350340106001540c400201c264000110341060b614a82c010b01c6001c00504200d140760070341000e21405030095645402041d1500d003400018401c00c1a8040c180200303800421464409600410621002038012a003501017540d881040c2d034210000ca00200d408106d4005034000200403045c1600210040124107a2610000f10b481d2003021142c5401098010341c5440220760001c040002014902c48161903801c3c150850489030b001030050910a000341d48410407203103058020780342 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 493826285 1250 493825035 493825039
    0xb07141c0b062b0902060f07050705010e03060a050414030a030f0506010302070803010e040312021b1b180c0c0d080a060806040b060906150d09061407140f04050306071205090c 77
    0x65900c0d240c4141204188120030080e14203131514200300044c0c6441c1c0c0645a16411501495100d01051030220f040c21500d4105904110010b00f004805d81e80004041d40c0200b65194009110707129800c1000107002014520751184c40000b441503034003039056100c0000c0c001d01d0481080240c481d40011001d901c11480c01411a02c41480107015040006007101d4120388203013003866801c00441285400c1e600400c03031428911380080c50742f000c1c030602070103000e400042441d039200400c5c0420001400c0001d100344060146001031000902505180046070f03101c00d07000044032000c0041080043c800c480454070720351160305100380021041000600d80340229408451000d4035900c0d1000e20445642c020f160941c030452404100700e0306607d18000b08480300d161100032441914504200040c4e842021380c41c1c542914a2081100044d40500020140c1c800042050356403403200218546502442d0403190749802080c00340148640c01081140c041241c0190901c80c50741d8180095441e040f080000075 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 493827535 1250 493826285 493826317
    0x351602010e0a0f0e0a020913050405010b120d0c03051309050124051c1401140f0d0b0105090c0c0f1c02010e0705120102071a0103060e0303090a0b07141c0b06 69
    0x302130100c507000032990007690503c0060626003060005819103096015040000c1c1e80c560034002846401c2c042d12020b10819980503091740b010f82000359641d2114502441044282140c1404040c4a001158524804086005101034840c415140100000c0c400c0da80c2030b01030031245408044040403411316522040e07c50074105900035841e00b015240c6e83c01c003000507a03550b1a019810b00c0090315194007a01d04420024209041030060090300784030a81d50390b22492803880d0710400a860382845030705559050300c2040144d101d40c0100449402a45400328442c010740410003800100014000d4a084100103140302221500c0c000ba42200c440504040d40c030340000c2028006410070303049446a45084100051900c503d94840030380c0340c1010902e070b449004850740108207003c07041c05440c483c0703010031015500c0c60600700d118941e291040b000042c1014121400910302500405d45132002d20440040c3e0381d0b80303034100d0100350044100c4a0703420851a162002c03213000c034280b40c8162004002400c90803 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 493828785 1250 493827535 493827539
    0xf0c1208060114030a0e010c17040204020a03020c15040b0a020a17090f010c0e040e070f0e040807020909010207050607022d0319050c0706020307351602010e0a0f 71
    0x4950811005010314103000c508081e00f040b10032010001c51041c0d0070000e000440b9010541001c0c20f581001ca074003000c000500400d2040c024507a200542c006504480040c0d035204100300039401b9008024400050707024031404c141349161041005841039104000304400d9542c1d603c481e2049000d5040480c0010b096008200c8842c080d20700d00ca9001030001c0c003160f08000c10b0804003400d4450080d050700010b840c07484c040c525410203004281028032201c0140c80d41c03d00301408410801c040b842080042841c1e980401c092110200c00c90712525005801c40420b4540010200d000c1e5000b54402c90b023622441000070002440410004030104102d2024a034810150300000b826084a941c400d1003400304110040301031594446a082252040d180c0949480f82003060b40d0911135a41e1128040d500100000360000d810300a04000443c8000d03855070a04282d040c29940407000010848003407040020742400710744a0300c1660001b103100345d80d50303180150404240100c2d08081c0c800c10202d070a0404003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 493830035 1250 493828785 493828787
    0xe0601050c0f01180c050901080303072003130314060405100f0e16181406060a031407031e0b1c020d080403031d0d0201091a130b0a0f0c12 61
    0x18002a186642214800101c2c00541800c441603840b050302d5082039a20035000700f1a00c0c110040003402c044603489403540c034001c02c3e00d440e8400203010b9030410200001401c2100440b96000291220a90840307071580210310707500701c4c1495a03000c15500342420303030f100a05010300050003d1045030711170003070175a007003880c0031400150841d138040c0c0d41007580302c401c00c924502d0308015800c01d584803828420344072841c000e04010300311030141410400d60f05210031440b00580c6507000c59040701094418980c1d500c001d94040b0001d00d904a019150525603205200e40580d040d08050b0540d2140e08c003103030000041e010070500316030014071540d420400a8011003021100c0c0300340081d80500180070010941c0c076594445129034400c3d00220003007481910410200d5540000034005a641650b00311a60441c580002e000041380741b00f000e5543d01c0e0703400c1d070b00d0038003500c07206a4040d0508a14422802500e0310301e90b590f607412000020002541c06038400c148c1c07902c90300580704426040040c0754501010458 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 493831285 1250 493830035 493830037
    0x40801060e0109180620030c031e090a0b060103111602030c010c030804020d1b08060a5103060b09060a050105041404060b0a02030712080601020d050c10020a090303030b09010e060105 80
    0x20f43d01c3c6c28822054042c41c0000c200d00002e52040c08803076a4207a90b0300c2c0071101000c0030142c07080000d507144498401c0009018000441506890704490f464030300d5035075000120081c00c0d04042c1101446000700e4500c0f403160031a03504049052084050b00c090361803d800440d81c00c041240042c000a498401040140c1001c01d00d502c0d4490103a450304048400b0361946408481c0550f11035040343e4445401c0001c030031781c14800c0d00e01ca410114208404110b0b030784000b20300000d242c1c1100a0041f9407140c501d0030310900c075904044205402550004c0181d4a05000d00200f03020040c5074040c91080002682503d003403404001030b00c005841c1d941c100350800a03900c10032640c0c0941240c106079942070110380003406c00e025180b0880c5a074000e56450b01d00340740964985040903481014844401e00b07200072030ba00483c4800302020380740b8206450b14100c504203880c12640f80140120305200003920314415034415411003e0340d0094a050003d0740030701c0d051154480091003184021290800840d21940c4104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 493832535 1250 493831285 493831301
    0x61c151703090108040507030206041503240603020307120c051e03060a0b0c0a0c03080c0f07030209070302070f0f030f02070f03080901030c020a020a09050118020702061e040b040801060e01091806 86
    0x40100c1f140c0c25100c0e804100140c0c06908422480d0102084002d001681402581084800c1f00180050304483d40469100020140190018140c020000a000900c181d41988200342800000e02030a40c01c40c5001d891a0b00110315400642048031001c2c1e034081c1da08040701d000b000c0261607004214130b801c20a5801e43c00440c840b002e240207015a410109030078080900282d4029030319541d5812020b181c2c1031403c80c40c3c000d10650780e001801e080003d640c2d00188140e101c83c07681000b69850905143c00001c5444800c401041da11504130550281a4081d840c408550100e8003102d944a80718254149403240ca44802440e020040201c1a450b505c03c0e044000f14080600480c0c1c4181e944d030b40090310f075440b550804442c2d1b690350f0004000d03551400c88202d02c40d2120007411032a089580d00464264401c8000114240202d0070b0748810185025049400070203461003450344860319800c0e0640a444c0610454078200300d403000104044100c7d1003444d0115101041e04004140c2d1941c4000240c1106 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 493833785 1250 493832535 493832543
    0xa02030705030a0504060e031902090c070609051e07080d0f11030d0c030f060506030f0402061b10060e090a120e1c0210050f03040f02061c15170309010804 68
    0xe00a200001d00c0c200302422a0361050344403580c5441c103020000340003c800f040550711984c010a012114501c642a0170041250140e540407201e40d12507145e56918410800c004200c00d140000d0b200034800045005880402c08108501030903015071103d507a201c803103001c0d02d40c0d1a00191410140c8901803840000614158200500800340b48143e16040d5049906e10300c0d1415100e088100310705504d032254448051400400b00001c41c03c00c80842c91a0000500031402c150f42040420190342d0380105035101c51030600c038191061b0342c82800294451111409070b545040c10050049007100d0070340f81c407078030603040c20009299094a6442d00f00c2620035035070650080c000c17441e80200060710b50900140e0f00284100a00090049510500041c0141105a001044002d000c9020140c22190031650020f4014000d000f400100d0300003d8607610510000d2513100c564100d10a0808100790400c0c0d0310b4034038200606224540d615a800d0600c040092180d50030b07041041400915802040c040b0340146c01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 493835035 1250 493833785 493833787
    0x1110050a18120503120702030a09060e0301181a130f0201121b0201061406030403020c09090c060d051806060604210f031806050a02070308090103140a060911040f0b0a0203 75
    0x80d80418401c400c82d11841901c65800c00a900c540c2100300704201900180f42e0b1009501d4994503507001040080280206400c011040c80d4210841d50309400440f10307035900004002d94440646014044071a02017050381e00c00f400c01d00000c5031603070240b044120241d0469007102111354150f00452364034500180b001c00c1d041d5990065280c003409008403440300d0711250000110a41800c4d14078401440518071144034003010001c000000f9404604040400d40603910200144c40301c1282e10f0a003041109440c2e0420ba010079a0188404243c020740e010b000881400301050702001086501c60104584850300000100420001c544144001041c4455441d40c2c11900541d16501e084039543d440c1d000340c1c0081d09450421600024161030440204260304000c2d01e4120038110294441d49948800380c100840400c1d4204075074040c0c2c002001030b55400303510101c9031074920140c030b00500407030252500c0c1a103406c0d040c1041e201014120f90507181000b50030241e8a292040c02044d0760301c808044030031400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 493836285 1250 493835035 493835039
    0x4090902061b0f0c0306100902130e160e0607170904020d1509060602070608070305060609030f101a061204060b180708070c11010c080c0706020a1110050a18 69
    0x71005140c501140b800c2e0140100082c2003000c0d51030b14204100c00d5200e6002a801e106807003602d00708500c200c5005200140c0c81d003603403591120922802d68058062a400c400400442c070300b8041c2100c000703009644a94030f4421200c020703c070b0140110180282a03408500c222030300002d10101038422541e0080003d858029450a95001d0fa01d0400342040d8140b5048000d00880307940c0e000b903001402c1c1c00d10003800744c14604600209040000b42c1f044090517900d102255641c4c54410032524116800340c04c9034041d90a4000f0342d9074620000040381902482c2411075900c0b10104e201d01d010741d100040109080c40800145045030902c058401c407413290780c3e0607582c0d0440e111140f5280c0800c83c001c8100445151000001d0404240240304004001150488a000030746e0040500d004071820329001684c20030354501040203101e807140690385442540c01c0016100d50004003009060b20446560314a0124102803042c200c40000d200004a0790502210360340700e00ca50301e0704405441003529090030719 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 493837535 1250 493836285 493836307
    0x6060f030b190c02100218093301021e0a0f1b080c0a120201231305120327040207121106091207030504030506091c0201110409090206 59
    0x505550310844900302004100300614448640646441441c41c00c00d0051940a4000a403911200800d0102c030300d5020031a02091400c45191154500c4080c050142070705140042603090f07088032400800ba07401000341550740045541c502400d810060300280008a010380ea0000100c6c6880b0083d401e43c4107404941021943e040480c0e48074902680422920101d0400050350744030f03003600a60010b500c003200d581543d8860380c43c101e04488a40f40c11180880d07191004892101c5241c64040410821020307843d507a85100f40142030001d8141401101981c1c0c0741d0601000c04140003181465401c00c0c0200c9d090114014090241013000e10011090581c52034005800c980002e030094a2000c0345118210841c0d822400303401102c10240000c000034504a240d003540d90b601c3c1c920305030788404045001e40402d4056400e50300134503440b609545052510b5070b14103175294403240d58140b1080004d030b8507408050040c8142a04507a00c2d401a40c41c050500300410042c200ca00402ca0308030300200301059860b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 493838785 1250 493837535 493837559
    0x309060f0c0d1106100609051201180b0108160506040e0c0717070b010e060306150f0a0821040602060c0307090305030c10060b040b030f041e0809100801210606 70
    0x555900d0b101d603c1c010751001419480c0c00d01c005c180e440c079001030260500005403c9103070b5001b00c450031909203100d032000100440c050011200e41d2540103d602010808010144e4900c4d41a150360b5003c0701c29000c0040000003c148580c46100d070440c00c00c00c800d0240b0505003492907840100c0440107071500c420b90b0749804035140e401c01c91700d90b58070010400004000d40d84000500400701d00c403043c0c02d00d0501e0000030340c883c10080d041595080a0780e00c0c4d10351a441d28038184808400c0240010225581d5004450725038040307806000a540795411070003610303060401500d054841640c02040c099503130701007d44440d4409804c50040c0203400c0000400114108001d144041ca040060f00b0340e101c5240805054942e150405c45114106000502500b16084292503009915580301c401c7d90710f803800d218100d040b091050b20726403074902e0300d1007052210910083c505400c1c16646a40f420300a0781040328401028000d1071681494901c194100242083c443c01036140200e10029626540d03142d0f01d00c0da = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 493840035 1250 493838785 493838803
    0x120f06090312060108060102030a111207110f010302030c0d0b0102031215040b011119060212010f06080c13060f1101020310050102010f09082215081501020a050309060f0c 75
    0xd5440001d000c8404003803070390380c00c1e04000b00f82400c0070f5030308207080043c0d200c0c090801c030041046000c021010454108025a00c884101040c0056072290f403400c0801a801c21000b400b401080e03507040c0100554400c8c401c030391256600100d01800c00e04040e2040007e0580022010304511042c0400c50100b010700c041e040c0034180800000d4004c502d08000d200641c2c007402c42c09418441c1c00c140110b1400d00c0441c89a0030840070f40441d465504c050300d00040203000b682c5106075000700207000415000300c590198070a44903952036045095458601c488410300ca00000020402c00205040080500802506844140d14100b0300644041b0b00500d0f42240c200301d820807400361042204005c2541c084c8540800c892080d81b09001c03150194880005910459821000c50b0a0404011803140b9011303007040003a0200d494107040c6424903c4c0f0041030080c050762003410100803c81c0310011980009610030318180c2c46800b46051100070810040a50030002e054584440d0421520f00b44241c14800c0e220 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 493841285 1250 493840035 493840051
    0x21050c060d021207020606010909020a0507080c0a0c0e0411012109120f05071713120605011701020c0703080904090c0f0314030c03190e04092103061202120f06 70
    0x42c5420101d800051807643c003410000c1550012414064240da00140c220162002000d0240e95401c4841e011034903407103a0140030705901808204614201d0317010401d03099042c05041d2821302c0f00d803140c0400441a100351030040c09103610807940a0654000ca6003000303080150465400d100885c800c0c918281d900ca0501115080c42d050640c0c0f006a402540405040c9068504142098211303500e488000c0f030312000001001c040480d450844482110b40c10015007103001079483d00f03809516111000d00300a0003450920402c40215107400c520520a45008800210041c80b1461554035441c180f40e000100044e007054a400712000072462454042004112401850010919509166208580311300000d6129042080325850030780c030000036242420950f000240c3c0785119004145c888000c920903894001d41810600000d20421000700d041c000100300d100201030444881c11811900c0078007441e052002c012112102505204d4000484d490044c01280d400c914810021840c08800303c030040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 493842535 1250 493841285 493841287
    0x6062b06170c01080a090503070f020d02030d03020c1207021804060605060406050c0d050a170603010915050412140f210118061202090c03071e050c06090721050c060d02 74
    0x50361a50b444102c0b20751040c410303942000b01b0a200c4d5a890345031b00c02c0d440090b188000c4000e81c0d50075950740000c0d8620090b4010100c0e0b400b0303001c1e810045c003e50000e104601d824001c4000c250f160108080c212021143e005081e0180392132007008201340000b0140c000d03a080345c2d40d0140402c0940310312000340301820841c9c507603940321110705401c0d625001d01140d09404018062141c02c0400780c000400c008119550802103201d6500c000c0441c0c010840210301408007035454070441040c45540e44858040c0707014100c900b010080c1120113680400e580514144482c00c1006080f03806582c080240206102944298031000c0170a09103084118080c2c102c11a24170302550401540c10003407240c0c40041000c0a03603030240d02c80503000616003c900400080c0d03800300020014096a21903030f2700d080c01d40c5025090007448000142d000300250460b5281c4003d61080f0350128103000b10008014044070600c0522400110058241c4440d1103000380040301d80c0d10607103000c1c0003243e0301e80014101c4010303014001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 493843785 1250 493842535 493842553
    0x6070206070303150302100e131104030f06270213050106080712021c0c0813150c020a0b0c0309010f0b030c042f12061f110c0616050606062b0617 64
    0x39a01407270110804d41107103002003020b6004645026102103d800060440c120b244034140031000d8402805010090b01d4004070008034200f801002000090003910201e04001401c000d03c0100d40017802100080783c0c0f00d8000030122031080c0421041c1014072a00581484013200302c4c03006051808460038130158a9190342c072480e50748220104d034800e8131214101c46542098813644c40d0616205080ba40450301e84410511041c000c00c41824001d501035001940ba1900c1c1c0031100c0035030030178be07068016542400f140b002841803902a040c2c80c46001805020741e407101e42c040000402c0c001c040c100410582012110b02a14030500b03922031240000061503440c84413440224a1a20007480c00307101c1d142d00b080c030b000b4038021140c6494014107a41002d10034180082c4440f407a02c8001645c90f94000800260050591081c2c086c07a42098410700442d0300c6600d6a00c108111030240304002c2035803280c02c00042039036400c282101038400b2a2030b48000703038040d200c0c05080c081c00c1341c0c40c11428035a4054408 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 493845035 1250 493843785 493843789
    0x6230a1d0703030503190e1504150207020114091807050307022e11090a180605040b1003020f040e01080a02100905060403020d0501110313030e06070206070303150302100e 75
    0xd00d80a20894000d4910607081d6900500180009000034500f5640016200707480f036000da1001100d07040010440c0d04105044520608440c412141141c0c130031588032000c0321004107030081d1030010350705850300081e42100c00c46044090b00f01080c0e09a004100c0c0c41c040d4007100d480c0340c1700c40c0113076040d0b40c5481d940c2c98003840280ca4400c1150170001d02005c2031030051440c41500f08203901c101d407840008200d4084d42c1804070a00d0145c410140c1d800007a502c0c000400c80d48100c02c0030b07103040511006210346ca070355004000803141c004060f1754111311071140540bc45c900c280d004040e1030315050949820551110100d54031200242c011410076404514003005518240f02242c1440f5018a0804041070821f00850b006002d90710000303024055030341c129000c10201f074006048075400c007480740b40c032890205150748100354002000c0d004601200924445402d00404071400c0300d8018001c9071421101d9a401c0b4001d11803110741c4a00040d54034804001a40c0e025102d160340340d1541d8850394000c8240003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 493846285 1250 493845035 493845071
    0xa031214091b0a0b0a0c030c020a0602030a0324060c1e24060b0a0c0609330204050114030619080303010f05030a0c06050c0703060501031511030f0406230a 68
    0x10b4414403880365034004003e01043c94003254004041c1d0300c0c0202e80350741c00345010784102c10013160081d0700100303044010907155400009049038111507a402e00a0408030503207540c8000c80b4400304401c200105034213000315401404806940e61040c105a02d00e051510360080c4500d611540450b0f4150490040c085c0340d07070703444d6403041c01c040032035100b080b000c0e1a14000180a00c1340c44d03202000d200d006040e01e001d200b884d90100400d2900202440035405c0c425560030003066030b60030610100404030320003102031803c5200b96002d03168180c540f00d42040c400c505584003a000280206d0348407070302070701c946003001c40300c803207400200440700c000c6880f54180500342d281b5107840c1d00078900a50040200c8804200c08a08138001c864a504115640e1080c0f00051400c103941a00050411800c0c0800001081894409444500152601080002150b02d403120b9184400c0d1483c03890f500704540483d001c6511603024000142200c0f44049987d4407501441c445188220f0f14003201c01e40d2040359140c1c10440c44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 493847535 1250 493846285 493846333
    0x3110304090c14090307150302040305100b0a0602160b07060603081602120c01050f031b0406020c04060902030c0316031e020306040e03090a0e0a0f1d0d050c0a03121409 74
    0x343c025070800e8214000300399034481d20311690405103c12840010042d0281d07044601941e044802d0f9210640d6030300ea0783c0c02610440c00c0e5180110850a40000d2082c40451068200a600c4d107485800c3c40c40d228048260b074202d0001a140b9550310b080000000301d05400400c0004038170241e00784003043d14010424086030050300000c142d00801080700d00303a030f84101216042906025019102d0302c1d02c400c81c190f007405166554240d984001004144c0ca500068a0b50442104071400e018103500c524269090740010f541e82c2000410078400718141508029074400da000c5280b41c0043e2403203414002d00d100c00580031442100680c00028010300b4101802015207400c1d41c1130046107003101d107901168084d4014032a20340400b08403404200785031650381020803c0a81510306000000010b5140410a4040e00c2140424442c0944c11074400d0b000d030f0140d600c00d00510000c0d01040900d078505541d18480d0303800e071501d065600d240b40986e207000d00d00d00ea801540d000e40101119144031401c400824216 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 493848785 1250 493847535 493847567
    0x2060f060f01050901080c04030c0b0c060703150512100218090612190c1220010f09060324080303011a0c0a11061b0c010e040204081903110304090c 65
    0x181c00d1044039980050849408071020f00e13003180c5590b01d122281500c2e000d160001008440643c0000903030001a101500d0f24000d40c0d4242c51107511031140a5007142c001d81000c0301c0001c1010380420841c0b406c06010a074a0b006201580e129100f11440c0342c0880c0d04c20541512001c01d110b20350754950416000599220714140e6131050750410010200703994020000c41e0035902c0d000e503c20302003007100e001001c1c2d0050482008507440c1080c0707458008240146220b0615202d00c1c0c100c5284ac4c1584141d00d61019081d541d210b0010f680d0410030214050b01c021501700c8003407122071a8a00500443c21fa851005240035400380d0703240c0d410301c02c129120100740d00e000070000c8014800d080d40040c02040b0029290351115007000140d0b503002c04a2020b002d40002c0c1703507201481c00c0b40400c01c0301300031400a00800e0266a4581405555401c000803800b480c06014810760112800e400e0100c0c1803c0b800e2000b600908020403000300703801e01986150302581010800d1a1500c0c00c4075605038201120303099504c50b07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 493850035 1250 493848785 493848799
    0xa180806040b04051c17060d020a0504050702210a0306050105030c03010b07030c060f0b0108070203070c0306111c0f0b010903150b120a050601031b03080301121a0702060f06 76
    0xa4440250398030100034001800009164001c03404104042207141c0400c14101000003104404a0000c3e02040e15030290140c600c0309100095250b1429254108891342d0050031031140c54248400c2c0320003413400a0061042d48200342100346c1035014151111640801170000c01d85c0c8503070007d001416113030702d5480941449010300c103000020401104bc1d07819a6000702281e502e8a105042c100d540441500000d48070b9843d002140803902000e4001544c8585c00780c82c2c180c2d003905c3d0000226aa4418084040c05604588109000290164000d00c4080c060250164104402c01c6481402030340c00c0c030f032038031a126034500c43c03804c00c42c51901441a00039024200802ca040c03441e00c410081e65540700c81d81440700d075100c103100c65940d030b400c030402480401c8808417000b0802e9450f0070381d5160b50a00059072002240e11080c0c4000116802d100142d0b5400050f00c1c0c1540d2829914409003882e400040f1170340b10180511100000916800a10610490340100407070700f41085013400b20b02c000340c105401442 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 493851285 1250 493850035 493850039
    0x3090d0516140a1203090b0a1e08010803071401060b0a020d02060912040302010806011206090e0f120406080912070b012c0c0901030f11030403021b0d0b0a1509020a18 73
    0x92045041c0b011a40305255058038208580f401b2640340d002d039000002817004c0422241070b11680240d00c125504000900c909070315161613420740320302800b4491000c95600c20002c14000a01c494240f002c0d842c0f642c00040b580079180c418018103a0000c090a80040e0300c8000e0000002e07504122064014070b15201070324100c2954840c0840c40e1180d40800790600c101d59010075441e91284061040d22000300c00304000042d02c43c039081000c0e108413a0881c0b00742c8034546d481400144003280c1e1201c80588410790a01c0e2500d40841a46e815000800e114502d00ac0c1810401c4503031082401080402c1c860b095071a659030411140d048000720300a114042a140c45090032a846880e27550180c010441c801002d0f2078500c8440102c01404102e00038900543c200b141c26600d030422a13008d0760003248079400390303070310501d100d9012240300e4078201815502040502031200415451090380390003042c040b00110f00343d045044d01d210f80d008035902030300495900207505140503a0280305c5012104980314a40f8400d8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 493852535 1250 493851285 493851289
    0xe0405120307020309040504050c0f30070e0702010f060e04120509030a14010212010515030c07060b09100f050a1811160302070603060905040206071403090d051614 72
    0xc40550a45011850010100b00d11600030003c1c2c0340301c410300501c20f000314078003440c24503207620341c40b00b90328000c2078121380341c054610307000300141c030007105800c2400e4010352480042c020480210ba0150840d000f0f04802207080422045013500c00ca60079000404c0c0444410124401c607200f41c0d204102d4000d1800c03d10000464209400c46402c41c01d16100d40c44008010010f030820000810050407002862031400c010501034000d0b00ea00d10342c3d4400498a40c2c1d84006000900401c0544004002c80400025212203800406069070302d004e1000050f00d0300c02c034004500740c2c1c0825036082c3d0010003d000c0820840c4072601c1c030b100150030305807940c008031450203621030b000c501c08004070308440d41c88507404041c0340944801d403030741d0f901c4441c101c0d8244030b4a428003a40341e0707919004038400079041c61004140244103004460080794013034440e03454060300d500d811001400100c110100c030300041188040d41c2d5501440811520301500107032290b03028601c0004c06c80c00c20341d031041d036054440c04035090b040c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 493853785 1250 493852535 493852543
    0x1502040803090405180a1a0114030709090303020904090b090c0f180402062b0e1903030203040311011b03140402030c150d020409020702010e0f06030606090a08030403050c01090e0405 80
    0x40d050946000c40e540e185d420030020101d481344a0a0060302c607000000c02801007844d2a05148070072241159031a03601c030181460b1540900b500c01c4d405601c80c4c2c03810006000f4a40c0100c0c0b2041c080d20b07005041c4102a0000713001e440210400b40c540b07550746814000c00410611030a0400541210310419000c60840410380a1820820901f2400b0007100010107540780d400c03c582c0c3c2025401001401071203641e10320090396034003141407050b0300d19050421401c0180090f903040045080c0100d104140c0a50b54110003135400100304904001c0c15200c2451100804d00842192800400c25103140300703100342c002012540320300c070201e1001901c041070001580f00419604c1650b1020ba80c18031614a61910444942c451803c00c0701c0054800100050100080d0f406498814401da03070715208501541c04012444140c18001d40c1d02c540c040012403500c0c5031540041031012000307030945642a0b0f803983d680b0b084d0340060344180c07560380001d4121461581d00060800c0640203400e550040c500f007a4940b1555 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 493855035 1250 493853785 493853797
    0x6040b0906120a14060115090305120c01020c071710020304020f0f0114070506010509060102010e0615030f0604050a030e060a09060503040201050919030303110f090f121006031502040803 82
    0x15468842028001c01414403d500340560070864a030248084c2c10b50f06903403000c0034450703088540c03604043e420755135100d40c104a01300e982100c002d01501200c40c07003070107003a404100700302d070299420801544009000d005040090640060a00c1c02ca9481c560003401d0a40b09030009190610400401005039204110072030141b600703071064103003600301c040141d81d45152030a241d0700245000c03541c481001000510300c5d05a0b04c003520100d05584402c0016400c1e00d100d801c40384460b401ca0740000e02c0400c801002c684510380024100d421095003100150705180c405c0d40e060300c8580065580e01d0a041c0c001040d02c3c282d007403d8820714a05481c0d000d0040961b900703401a0410410000085025a80310f20306880090308020040342d00f541c01c0454084554906120440c0481d0816055401030203a100036180c1d004000e280403807410740d1420820100801d00d1b0302c01ca600401100420712a43c0f0200b119120a035801c2e0310004405095092883e0b8211940903003030ba19900420051020352000700c03d40d40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 493856285 1250 493855035 493855039
    0x1110020304090b0a2412140601030e101a0a060c08030c0d060f060509031216020909010f020f18040504080f1303021f1d090c031506160b06040b0906 65
    0x7948a281400107107204030268081c00c01825414001c4c075643c0000131211031000021b807108200c46a50703401807411398030081d4152186c0c0300054000f6110354000d0b004070403000c00d00d00a844e5484600501d10084030900c01e1110403a00c0c241403c2c04150401081c404041c1c1010b08040343c0040807561445610300c00200701c0019000045441c4a6014a03604481c0c06400b880d43e14184068440500402d20b401681903503200340724464007a500d07412290201c070102e84402c20041c43c148919000e11180d124050401c41140d076803190282e44100740c0d40b01038410a84c6105846556450120380d00030341c01d2048940c1d5118914101c240800216080e0403200100c401803c0d003612200c031059040e291112030b60010390010700c002c0c1e0790143d4075200c20308280703040c201e5121000e071180070041c0d01c2d454440482c21140c012005601281c4d81461502c00f031a4060301c01d10000403c800e5000c00f040c801c2d00b242c28611018195042c4c56410425001110340d07101c40d081e80c0820805c082d0070700084500501824041c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 493857535 1250 493856285 493856291
    0x506010b0c100204090b03060a0b0f12030f030403090501020d090807060c080702040504030f12020f160507090c0804060608060f0a180501091a090d0c110a030b0a09111002030409 78
    0x30000d81d0082c03058851065076003504544880c3d94044e0280505051251240f10b0300030a00003a503100240c0c8501c9809078000340009007124107250034001601c169488451440c441031011300145880c4100540c4124031950380d184905141400180c1303080005440b960034090030000901506c2ca0000301d0104071041d6107800d2200400c00d0034008418030450704040d42041c00d0508000078503070000d61942e54054190740f4402c0200c0c01000d607004900805c10140c50500c0208140c64659114a44201c0c141c1c0c050b00583d22841e6880c002e030741c11100d00808000108000d0030070401448140e100d400028880030000d0b00f014641201c900c3d0400400034081001142c2e58240b41040700d0420900000c0c150b032290003040840747c3c9040c103001a018081d03c0c2074606004c2c00010f01e0b8030f000406d00104003180d0b61503041c04000f55588a80e000d440e14680107410030400360340040422000c1003400d000305090100007a01e600300e41819001603580401c25400b0303607604603c3c0d0528a90000840b000c64801401c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 493858785 1250 493857535 493857547
    0xc020a080306100e210c01020f0c04110c10091205042603040b0a03020316050708071103031603030902040b0f030d12060e0711010f150902360405060d0506010b 70
    0xf0f40b9002041d8504c079412100d024402a2121051a01032a0764007280c0111b401070300b517200049948640f90004446a40c020100c254078606142c2c00855050032090411802c043d21640c0031464915602a841c0700140c03920255421301044030700e07140380c0c120b882c0352103845c15043c0040d40c506408003010011030540f0042003400d08807000d0041d83e0140c501082c15075030301d103030100004001c1e42066514442e4010001030b0341c540c41c1d0140d0304494460780d000f06454200019034075200070445c84102581d415000800441f1011441c00907489201d42c400c0c0c03000079100f00035006100484500343d59090092442654030700315950009064902e0750154a00204441c4800141e03c2c09044107900007800390311020217001c074494224038415101443d817002080364014103003420040e5428141e11202c00424800c0038086041140c0041000c1c101c0e0801c0c222011000c0c43c0e40c07103420744080304404810145404440c00130300c0c150007942d82048046444800e69200c07030700d4268503a60706210f16801801c0002e44 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 493860035 1250 493858785 493858787
    0x150108040f15090204060801060608010801060303020c061b0a06331502030c1501052b08071e061b080402100e0102070e0903120f070e090705040306020c0706030c020a08030610 77
    0x4075803c2a80500306008495a951420b40a4501c90094a001c1942072002144402d014440c280c2240d415900401800d0804418401349a1220342145001036944809600a1a081103d0340d41d06101d4500010500c1c0440146400115500300400340b130008000a04601285c001c65407080d2030a403080341c00f02c650700c41d8084e481e40c0b00f854a070603282d00405000d80380700411074080d01d040f200306441c24002d40810071190071b15943c5140600007044e084560b8540070440383c1016003600c51050021000c0c1c03013200071056085036900201102c4150b224003a080203202c2c07032184610742c16000e007003c1c12542010750009010256450754801003245030321000001da0310801c0450010302c94070714684014241030001d1526a8040314000102e03103c0c640110302e400350807804842c429075442c1d44d8206502e501204010b64010b002d003183d41000301c24040800130554901c010b0040300c0c11000100076642c07819802a050340d150760301040544d0001981c60340030803c40b40032240e000390221945140d622010344 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 493861285 1250 493860035 493860041
    0x1020f06010627030b0105090702150708060a091406030c0625020f15073c031e050d0632150f03060a0f06140f09100206150108040f15 59
    0x104030207680d0301483c0000c24401c8079064981658429034607824a9034805d2001e903a1100804141004d0f141c003000002c04482c42010a10b810681c018441000c680e500c402e41400e50b01d48019046440741c529003030000d1850108141400b80405944860400741b40040c200910f079a00071181001415100d401001c42d0350b2411460300102004200c4000003440c8031800100f03803c50341040b03410040c035a10b034910541c00102681e2101a40c8400c6c0f041a034224846020140034040045060000d0801d00a2582401c01c654099214441d03980310b4803031051001000c16030f020795114030510366040881003c031100e0701c4112144c40760800e050805810039200400e03005450480801e1104034081140480c07650582c0c01180038100c21100318078820703140d090f620814000d91240e0070201d0501814207a200741d1510140540003040d07503009007045111030208200d107412004203801070b0800d03010801054503500c4050b0b240003003841d110010b0710f025912200a982c0b09280504590b100350a440c8034400340b90 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 493862535 1250 493861285 493861337
    0xf17010e15330d0e06070e0a03020901060f03060f1e0b040b0a14130f050f0405151c1b1e05010516151a0f04020708040e0601050408010e070e0601020f060106 69
    0x303d010050703002140b4100c1d0b22200240c2e003100000e006400172041e18501241d00000780c9400403c109201d03440c4c074a003641d0081414889106141c0c03100000250492020250801030490f460426408540585550003820060304400881001440284040149602956032102550811009140d21042090780034000c6603420a42503000000105458a60b80212021a074051b00d03c8080850588100020395600300c0340e1801c9102c00d50200000ca03d0a205101e503e400401604107200f6419200d81c111450108603c41c610a00403004200408218409052910b21680c44203105420540000c3c9948203803028140541011071049091180740749410010304400c2e0410081e5242003854464000d800c0301c13100b4443d0a03c1010b802690420340203c1d0321287c1c1c08202c2d2440c05083c04079400e02444003a0000b810003c09000c041204e0b10248142c4a507070601c20001e250aa00c2d10210f82c0d9a00b00c01049141190440780310080709110004155064071118180500b8001d400d008a040208141e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 493863785 1250 493862535 493862557
    0x70317070804230f0301050f0a0f1e050709060906020a080f040b070309060e030118060f0207140109050c2d0310090b01051309080301060f17010e1533 66
    0x10301c0320815020103400507071500142c10380d131030701c01040c0300420182250822224200084450f20004100b650716a0110703030000400140003d600f211400c440d010a54020f40d95000d0ad695841031050190300840404018034103450070842682c2020030003516240d4404008081d50004a22000031007803400650707000d001ca10410036150041c42c103000f031181a142c8116404200b14803040d080508040c042c4c140c510381c0442c4501c0e0f10021654482d4006e000b610100211541d0911800d40026a25a201140ca50000001040030803050518506089403620418410444000011202041d80204c05800111107107601440c51130702c0046400e01c0001c1e40310b005014035010314001088040388d40c1506840c0c0aa07044880142850030990441c3c6012a0180c02a2014001004680d119002c00ea2817103c05290201890000105900e501202a04007551b00107100301049502800c40f03442010b000b000305ca030f0601d04203840c20642c036580c0403443e000009075401112040d03a125080101c450210207 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 493865035 1250 493863785 493863809
    0x613120c03060912110616050912030301030c030605010e06180a090b0c0c0f06071b060f1107020906031c0c050a05060903120c0a0519030b100206010501020f070317070804 75
    0x840c5031034413001c120900800c001c02d101520880d4240310019044e48603c4000040039085800000b013138501e43c01a540056102c01c82c1d0358500e4100d00188084c50086110320204a0982d085180c40390984805810070180e421011080103107a41d501c400040d15010980340c04030458503910f04e0030020342140f95020303010880036000d10582c034205200038084407100d03600f40c40d14080b044071007640320301c000da4007203000824a80e0450000e0f480004007441841c802c40c0f001a03080302400d08601030b96414911000c034040080b03603080950500a041a03030122080380a000109080303145030399181c031305c0b04403141000407400c9004200b01040040a09060700b142c100c4d189860030a003c00e0366075024100c4a2000912100403c0c00f1820010640f0300311000b6448090a000403503080c0c07410411004c1c001300030580c84400e001210748034004400c2e40540d555000d80001d605100000e86044041c41940c28558400801040420440c4100c01c000d80910000d040e640e1300c807810580028040c40d0001d40c90101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 493866285 1250 493865035 493865051
    0x10806280b0a020c010c02030606060f0c0706031e020a1719090b070318050303040303050a09140601030201080606090a03060c050906130f0f080c0904060216060204050f0613120c0306 80
    0x4801c00c0030342408070031070b400c465004180d14011600c031710320600c1c001d400d0390118011a07c6460705002420b5512011008581490a520812071400e181c941c0684d001c6036841011703c42c1c920004815241c50310401209500c0d042c8054030081014a104004044181c054004111880054469000c10308143c1f103050020502e241030412100c0700507600d80c00070034034005501540c3c82c543c04001203000d8125028600b10b82d00e076103095028040c01400004c0c9140e80c1d031003c03800201268120a869482ca00040c45158103510014000210160a00c1d2007490b0030312104645030f03240c4020f802629480308010601a0308200c0c1994680503800c5402c0c0d22003800b02d00175052504142d0f01108665415880040550340c80700754030b00502041c003900703490f90820f840100c0141001d80d441e035005845044014940407007111803540301d2036607210403180a0340000e070803c4503180c042095488100300302d5040d407902640000802d0017590600c45c9842000f4500700740e0040c03140c100080300042d904040240140ca0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 493867535 1250 493866285 493866299
    0xf030a03080f06010306030b0412200d030c03060b0901110c04181e0213051b2209112209050106030b130504030f0e0d0c060e1e01080628 60
    0x3070803551048a0142040050219886406424116034101d00c2c950501e07246c0c4d856619804062144004c20f214008003400d00900350303a0304c1400102d01e404050111035884840045c00d030348640b5010001c00d801d01070103201c100340b808211880b808090a00a0b03140000d00615030400c082c54400303980c45490308482c43d0040c950301000540042c400e0710203032201000c02002211070a18854003a410446040382000390a0141d844240c200c2c54070440715a001c0300c0f200c484c0001d540890b5105c001451081c00c081d0444589110302409400300940500c0320814900700c40342c890181d02218030034030b46445641d110741c1e0b51101281000e4151114248590b60b10340da0042c003d4020700c1c8800740155040782e068982000d06200e20790040d030345680c1c5d141c000b0b04024012a1812988001c0c00c2d80688014064800912444000002003c4503200e00d403e11140100308445070000c101c1c12110b0b200c0850526040380c1e44207014039400b030401c03122800f4400c01c1404080341c0e080841140c040c4103c0481d404200300e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 493868785 1250 493867535 493867547
    0x102070c050a0608040c03151409100606170408130b04090501052106060f03030c0a0f050f062214030a08180d080a0f270605160e010e0f030a03 63
    0x5074806680c0c15100c540e0b555400c0301d51040c203c0b0060302a50003d03030140002440d032580c840030749114040c08501d541d1f00000c0500d52940135100042d0641c05541701204c00203c2e0f0190b0002070056080007500742d07084501c22682064010802400310100181d07000c60b103204803002c01d000d044c0340003030240c030f60381c8840c5a031000301002e0203410b124039240d221441c0c204070804400305110400201070140e03602c40109102c0c0e14800080c165906000501241d2500c000403c1070b07a001a000c0c0780300e1800c1c80880d00740541003840b44078512440c1d420403c20440035112080f0080c0b40e4182c2418000d40c00c82c00350a0035094031503c4e1001c001603000005c0c40032115540401c042d40107103651304040d0010480d00014030b580d07801480b100000701c2d0380c840002e10303008803946c0182040c0ca801403003c2006469540c0f0180305114545103807910404c408001002c2c01600c0c410b00c0c1d84680c0e88c6203c0300c250040e50401416071105010b0391030404c225046c04003140d40702d0400d6041c20007405001c070345041005190240c11 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 493870035 1250 493868785 493868789
    0x71b0503040f151b06060909061e0e060f04020a03080406050309100606171b070804061202090d0b0702280314070b07050c12030a0e010b0405090309100306080102070c 73
    0x9400814011030f800208100da019460341a4640300e1074640c0c020b83e038101c1c204480d1002e8070f000b80c1d2035400144402143c018060700a1080c040041c1c08803440c004006840d2a8012031000540f40041c1c1d82182480082d1458003e00c0060800d07205030390354070011340d0754000c0d03800c010310032040420001247e540220203580180c1d6040b00781d0700010000840e100c100c800f64810600055214400f00390a46000d0844030340064404a201e10121611310004120354002d2208a03001c80c40014104021940a10b0825265150100c00c4d8580b000d004009440903810303000203003040210102007041c690081044440b0301840d003860555144103604c02800745110500154007003501000e114107003503180022102c0044c0e0051040040740ca500f42d084519412003000c00103548200f410400d940c00541002c0c52182800041c0440d600c0441c0000c41c0c250752510701454043c4e4101000d00c10910004001c3c0c4042040aa512401c08407c010084024103003a0b801308295510008451302807000c10448802 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 493871285 1250 493870035 493870049
    0x3010e0c03042d051b0a1701020c1605010909050c0a0f0c0b0405061602060c22030b090a1e0f03050a03020d1404020306071407020607080d180b15031005071b050304 72
    0x8403003400c2179195046907980702070250f2002c0851400c0c000b4603a80a04825a441d80304001404c04580c82c02076846c24248148408030488501c80070096981d00881c210b016100f02c4100b40b005080c001d5040b82140240d44180d414030003000c100604991140001804d010f8002da2680751a08260034000c0c0c80c0d000545100e040340e00070340c10101116000041d0a4080e210503d0550700e084041c40c4d815001c00e200b0002222080c3c003c0500101044010684a0141001c1720117000d80070401d1502c00e52010b981140182da81202c2085140401c0440b070420104503014140b195a401120008a000384140341c03803050030614010b02c0c0c0d0a4425500c070388500c258800d80468106491ba05001d82d2079190038507a00401d00010804da000505244014107142c070712a42d009800c1c41c2901c50074506440400f9403200818090b02c590600b840b000d01003240d08840500401078201012001003030320f03250502d800b84482a12500400d124911031410348510b82c0f0300c131090044c1b1140f1440d00e503889a0103449420 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 493872535 1250 493871285 493871293
    0x609180a051b04030605040c030813180b13050a0b0d2001021504030c17030106211506110304030204020a1e020115091d030301260303010e0c03042d05 66
    0x400560000b1202184610108981414a0f1859132214040d000c014011280c40c02034400000001e0341c454054034000c8002c080000c20281070100344180a10541011550182004070b00e080e0381c2c44005203008a103180e290003055680e0741000410240c0f0360b0301c1c030454100b0700c2c0c000c01134180400c0c4500b01c10304003440c0c040f868880744188012a43d80700e4908418904444803004100024080c9525980e41031285038010f04141003d01c80c0203690300240c0c8040d0126201010120440c4030054000107031600d441010132251507034088220409845019100a003c01000000c5200400f0400d40c0d00555004200355941e12880000070000d071142ca8002902d4030000c60004030240c0103000718410258030409110b4034030301c0c111a84001d48020403080e089400039802120700ba40c81440190701030310640c2aa0890002c401c0c51800020800410907402134200f0302c011703c01c5030000d6003a29000b06080da01a900e9460314140a4060407039524a600320011811480440660311511010164003c900761 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 493873785 1250 493872535 493872541
    0xa030c030603080d1a040b0f27040b0f1627050a03050c120703050a020d1401060609060908070803030705070302030c06070e120c01020d050a200a060c02030c0703110609180a05 77
    0x800140d40c062100240d118030114401100c9040503480c2a03008010705404050042c271103000080c21240580e01a07601c80d681d03070304018803a0b00c403141950700115600007000059201c40401021b002070880e05006101c40840d041c000c0303901c00a501c4014200003421062140d0b174902d000c80da0341c41c1c4284a107005003400c160306011004041482f02c1100d0b0054054005803025500b04107032100c1004003114850200c41a03410041800d214400c042c210640312681480c0c10105c0281200e07406520104496000090600c40c403003012003079036085002da042260300c4802c645030a904500601380c007840343d4410041080030707031644102014904803054800c20303021540c0c10b8000f5100c00b03442c07180c6030141c0c0c007010b181043e80d80b10700b0003042059081d07d0700107002c4030100e0701084141d0440001e0745041c0c0c000f10840b07041c480c9078490030119582c0c60004501e0180100401a101c18880c44080d150840e040c6c03a08442e03464900c00c1781c6071300c0402025a80660008140802e4000050b41d040c0022440d180c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 493875035 1250 493873785 493873789
    0x60f050306061e010c03050d1a04050a020424140a05360906060c010e01050a0509010b03070b0715050c0711010203130506030a0204030816030f020c01050a030c030603080d1a 76
    0x84507181c0070241c4072500043da0700750040d1500c80e85400c0403400c20804001e080c0c005a0903104a80309005a903200100d00c0c04001c04110a944000d0072502d00e05104000030485010b96000b1941c0d036480e03c8800c94505410342d0790a03a4820b8105034403000300d0000240d44000d55920074010050788492180c5550402d810004d90090781705000c411920004001c0800e60b558504440d250307522250050820740350030240a842425101181d40b02d03030742c50b0744603030070300054030014040d140d400740e05080200034a900100000f41e07540c00c44c5c800d40d413844400141d2038091040140b2200c4000c65010002c2c8254200f1070780420460707210604c1680e1483c01e88203030780c09540c4044115101007008000100c24070381003104014042d07001a0031010003e60030040000012920000f801000b000702c07050f80e05011071414060718080d081e490001c115006103c0780b143e540e800105aa00c06000c1d4500000c407101100e03019001040c3e180c0018009060118040b01807090035040206982ca40c4080c0c010000c4c2d044003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 493876285 1250 493875035 493875049
    0xc1603150218060706150b130b160b0408072918060c0c0a0501061d1e07030b030f06040507150305090d03020f1204060506010306051e01110c04060f05030606 69
    0x3841d101e900c04610071000803898008041c0c011940602000140c0c07901c400986004c4510b540d0101c5001080031403040e001e1010082c0010050801c41c9d1550300c0d01c0c102c0c5c440348006100f4003200030901c011030800300e0244a03a1b20181c1c1d01c0b01d64011008090503222000b0343c1002c040100d000d611146001000846199400141c06030405549000740955120b45181403c03503003090030071161901c961249540450001d002e05001801d1440034642a0108040c44041d244002050000801081c0c6450451881741001d90f9070b002c400c91500084010311303c4000707400c02e10000c000003514441e030f006000500030013141c035134121080b02d00305403450180301c03006400fa13950840301000c144e040102c0c00011540681c0003007040342c610000951030004051401c407a488403d8906407020f99559007041800c0d60117200e940e02910088903502a02c8140c19a1505906c940f1306070641040303400000110780f900c04000d96900f0b14401401849150744820740441a02c102e032080034401d10a91011940a0601c29 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 493877535 1250 493876285 493876297
    0x1e050909010b150d110f0309010b0904030206010302040504080403021e041b1403041e03020c01020105150d0f020a09090f06060510050a0305100b190314060f150c16031502 75
    0x3600881c0e584040c009035003080d81004c0c55240d81c0b035448406882804000600814003c04804841500c0741003100a407821185c00c05069402a9078035410720010a800048507811241d04a0700440c255845162541903800303181e0000390044800134404001c24503503210007103030000954041042100d1508101c000503c0c0103808000b00f4003203150154031284241c001e42d803141c052000c0c80c03080d00402c2c01000c9040181041039005800c4264001d98a43c1c0c2800380b80d0b04001e400c5040300d1902d644400003141e051031540d0040081c01e100c8104400c6440d00c1c083d840007014040740c1000401101e0030114100a14005e0450382036103030440200b140e181c90b038000f03020b50340da507500d25040c1001c00c64180c0c010107029040144048615a001869014180091640d400c1e09084482c0c03036809007070003034261010351000f0041c80c51003008101080d10390381130030101c5d100222122100a03407240c0d007d80342c1c2c1c421080d44662500600100720000090400690101c0b0b01c00c0d0001e101c11010703404117108a010f14 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 493878785 1250 493877535 493877539
    0x2070b060a15050d020c120408070e060f060a020c06030703060e0901110a050a14040b0c060f04081e09040e0303070f050f040905150405040606050102071211191e050909010b 76
    0x10000902c40c00e44a20081d002e6191855070052804003240d10395450018041308000c084040050b0501070781c1c0050011400628025006a02c90b0500b0000258960090215035010f148046002c140790751080203089848400944099503a00b40050300030302400d014062034101220702c1000c1000c0b07103414442c0c00c144204024072181005a94001110140d020100302c404000c60004e042d103242140300300510007888500b8449035100061281c00b410214000d2002e0300c520700e81001c02c404242c0100031140d100c03102c84580e241154814070074140c41e00a10400542040c40c04410305520800000258002c4c1d1245d103d443d107481100404a030a40308080040c500c04100340420010311510340c00c41130300003100d00b500f6086144580d0200c0c040714001ca0782503a00a40719601040b980d40c06110b288080c010b0102d5510101d0b481d80c4944111008440300180155444002040b1040b0260001400741015000300060712091480d155140407060182611a55001c004201520320500c9600c1607800c0c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 493880035 1250 493878785 493878809
    0x8030315060c030409181401091112010f05010b070605010e070509131803030614060906042310050901030b0108190504170a171305100f060e040602070b060a 69
    0x904014400d55801c490004190740c4024130001c198480799000b60241c0407070070b103410700c0b8140380c030300f428100841540c24a8009914016900d0042a03088000042c1c0060640d54296821040481240105124510005102e140c0800407803180f00302002828814002c8906000326600c0e03240c60650400d054804801280003000800d2640c2030100c1d500e5409030203078030b0000d03001100ea0070804440340038000450010390395500622255002412a1050540a03600e050500c4445c5011540a200d00e000304d50a80d603486070090b00301580001000e1074114068906a158003050700c0140c2a90000110030b8042401c1c54010002544100101c602c140b4400d2a4000b00d00140542000100f2000d03009403468282850380843c096036a0340104071226143d81d90f00d01042520300940101e480c040c01c0c90b01503030380741042c035404107000103100c404d2001b0401c4002900502d01e00c14000030501c50740290480401c4404000520800ea40501501d42c0110102c40440d80d4002c104010200d90340907046601744 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 493881285 1250 493880035 493880071
    0x9030e040c0905030714010c060c0e0a0602010e1e190b0405210a030b0a0e010b09041a060a21060b09040f060b0d180c240201060819060f0c02060709080303 68
    0x16400c1c1021407601d606040c06070261123180c0351007007607038064040580490300e9031496480900300020107000505032880200525020310301441e40344d1011240c05011a030000ca034000182c0028481c920001c41c0602540f01d41c4046440c3c0059a001d080724191818017600000c3d880d00b0803183e5040d4080f01c410807115107458000141980141994139003180c100e203050201260348a003d2801e2400f80442000c010f03111086401000141c5c0d04880080341d090340c11903618031082c0c4505094400c826000c1c18810300c004c8a030784080119840b8040d044074164104000061503100030310003400c81c05000d580c240a1900180c200ba010758105110301090542c08024a034a1003400303522103a00d4182c000c103c5140704086484400f6094100d80200209003a44007120b034410080075440990303030100780000d2140c207180002443e1144500601e01d005944100c0484041101c139074082607881c2c002c4c40c030400c41c4d5050544025952a4200c0d010004140c07280000304481800005403449141c5000c45104605 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 493882535 1250 493881285 493881299
    0xb0109090507050d0c2a020d06050403111203010f0e091b0607060207080409061a040303030b040e0a030305150a08030313080705062806080a0b06031009030e040c09050307 75
    0x881d000b44000d0400c6000d00400c0b00d010054040c0c4d80000000f03950b840c078040c1da22280b0090700385902a1011030164124410380050b202c0100300100990021000102561281416640040701344c000e104240103044000005c2030041c030146058a03050014251400d850380741c101d21202c811341d15003049038040305080c1800c02a689400303c0103c000f42486082402541d5240f06a17080704500300e40003140403505000b40c45451280b9401003000c3c0d84c62a45041071a46100010b104a000150030181c039204640600d4a0b01c5d040541002c010404580640000e400c005009060a80c1c0e281d1450132045110406450454030200036120130780c01071071664071680603504062003551400c54040c5428031601011030400d1280b50f00c100b201160645040c20000090400e162803100604500e903e004024482032900058481c0310039071052003000c544c0c4610300020f1600c4680c00d0807001150070810204e0400d0f500501146030300300b041d101844041d0215105886c8900d840c002c45415600c09001042a1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 493883785 1250 493882535 493882541
    0xa050405011d030c0d0503280b060408030a080a0b131d0f0601210c03030c020f03030a0203090102150f130807080301090b0f0108070f11030405090f190b010909 70
    0x100340300d0400002c00c1c6004541d07100d080d070319003210380c5281d41021840e07003485403060100c0f880760981850010702c1e621b403009524035801c8440040890840d003468100030200c076140e002002106005244a86a82d0342d080c1303056490740010b51040014000b40041052183c0600443c2d0050174010101c490b1900c00c1410300000317040c89410040500002003000e01d00c6007090241c0390800b0398007405040c1702e60510005000050500f05a03007400303203024545d00003059580c1341d804266581460308415200d000e00000303804001c601062a8140400161b010065800000a040c10f030420307000d0b15401d0902c1c001d00d1142d20b0381210404c01100310040040d184210b69010000a103128050007800c1c0340841d1182c0005e504260030a55406030780b0804016946401c43d0440409002460100d0322803904da80c0c014103500101f0740e88010712021401c0c00e41c14000610075a40600341c098141c14451401c00e0380780d462100162202c40da00807818502d240c0418050254008031401130f11581c01d8585049650070003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 493884892 1107 493883785 493883791
    0x90905100216140c150a02010222051003090203060a090201050c03040f030c0e09120306060408160e160219020d020405151e010e0d020103020c15040c050603040b0a05 73
    0x50b6a0f00e10040d01c040c48542e840176621071031040c1082e40a80105529100c1311811780060030740c1c611000008204941c0c0c115058840300040d07520a1b4203c0e42d55440c06505500994005108145c094004c0002648103160039854004070320304d45401c40d0072680012600c000c0c0240204180f160840994014003800260443c260030000a115503c00c407030081c1880b480070100c0014415030b40c450540e80241b181106850480300042c18950f1012041d0044070018070b10312012030a900f10081c1508010b01964008000095440303c41040e40884040b04070383c07007000c0ea4552030040e11140595070041410500703c1c90345000b840c0801103604032440004260705403140700f616090386d00060b40e11742c1c030800359900c903441c00042c00120080e10a01074070079480d10031a1101c5004000646015220380d010b2008500c545880b0410042244016500a803c6840c1c050100300000925402250 = true := by decide +kernel

theorem cover : BRFrame.Cov 493705035 493884892 := by
  have h0 := BRFrame.cov_init 493705035
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493705035 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 493705035 ≤ n) (h2 : n < 493884892) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
