-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2297
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:17:04.935244+00:00
-- url     : https://prove2.me/submissions/21e5ed75-d854-4e23-b794-b609741204c3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 412949640 ≤ n < 413129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 412950890 1250 412949640 412949723
    0x181202070b0d0203060303070f030f0e1503060411090a031b09060f2309040807140309031905120c0f06010b16021c06060b070b0609090d0c0f0b04 64
    0xc00720000580c2d440410030b41c0d00580302d40d2818007003402e41c8511500103100452003035034071081680000e108c0740c1d016850307510540111017407800c1c480b03401d000004203806100c00340001401894a50031066900745554091800d14039010b001c00e0549070340c0d40085484017116404002d0203180b00d0808001411020001e00859150031241d541d400d00c0c07409115808808440848440240a0684808903001a000600c02d180c5070610313a00d01c0d000240102c43c1603c100d528a0b06c5603200000b40e440d050b0008014020050782080601410803055101b12840c1c002c1e00e9403807102c0c070002d0001c1c1002d8801e881c00341070396200700e901c6103081c203905800c44d01448000b4415504229038544018004940c1a95001d504a12040c001c0010200068006045c14102070011801c800c409000d40007a5101d00003128840c1c5454003080ba080c40126503c03541d913481440a5801284207400b80c03c4038a000e55034134103c0002e282c8038103081540c21070b42918034881c000c008550401030003014000160b0200d400141 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 412952140 1250 412950890 412950899
    0x30608150c0a0c120f030b031b060d020705030a050901110601030201050307110c031b0108010909231e0c0114030408190903080c1c0206060a030308070201020d1a030d0c0c1a0d18120207 81
    0x301d44849000c49c070301918000c941d0701030b4a0740640c100d98107160004d08494523002d007020010a0f5034888042c8a0010b88000c64030180302c0030028250741a01c0c1e050712454150703920100304642064100318900c01c03522900720316100f607031020303c103550848030f1810300c00910001c0f4200240a070441a4408181d0034603200625001c10715031003040d80054401080c0005450790010a01c1c035002e85264404101c8016038243d14100c240000c03031400b180800e898180c0e50f07140ba03044061003408200d81c041c010a00800199420700310052080403a43c0c2942840b09015440307495489554100c000c081105d94007004455940010014000920741c0700c510007170289140901c0803030010700c42c81c0700041c1408101800306821038000c4d01500c54440e581e42c020003a00c0950310402c207051401300200c0380640540710070180301034415079403680019007042200013410329282c180d04420511400c5145041014817400315100900c0c00b650010101000d41002d02d400c4900742194100301c1c4815aa0656001240411 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 412953390 1250 412952140 412952173
    0x190e060a03050706211b120b030c13060b040b03150a05100f0207320301150e060103110c06040b0105041b1110020a020d030608150c0a0c120f030b03 65
    0xf000d07240e151a1000401001256100160040100d1506690305002c160040c5405100190380c00301d00c0c903a01c41c90b560510700308400442e0744c0c0c44040303034240c0c000703c890011600301240395000ca4060b03010001031055640140c50303420340041d08890341c00c450001c00e121549800c1d120038569a4012502040601e2400c0000b54607040da400c1400c040c8001150141800c07030080c01032100401d000040040704034040603206e601c8190026005e150501c801030540700350b0a0502c00d5100b245103940400b83e0050030706500609503a001410303141015158514030424034940c070060403a5044032001089682418070304014000310580046000d0f601e403031071018880040c1c0c4501c110007285814480302041c02d01c0340c203500f40f00340000c4540c0d20600001b00011000d60004000c00e103d20a1740d420401251100203264480400d850005007210031000460340500c24080144902c403e1420b11100044a42d0f883d4040303110030351400390106000d0741690303022a825005100351480220050700404c0124481d24 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 412954640 1250 412953390 412953403
    0x20709020f1c06150507031106062d0307090b040c0201052703070506130b07050f070b06030c100e011719021c050a060f15080c0a030209190e060a0305 66
    0x1060701da031052004400c80b10950f88000040c001220218110424249000d0600d50011000314009180d640c09914060350128005000b41d9005005881d0705d10308d6504501d00d0340300030581e560003a030010381d120800d80d001c0005000a01c001c460101c0d400c07003403400300400c86440c03001c0d03501564100b80030403a0039090081d030000b101b00d0085c805580c0c00780016440345507000720b005c01032452040c00c0c20f02441201082e0310303054a0b403156061190659440c0380c116681c0c0100303035030201040c0782804070900182404502552281d03010f022144602c107880005000340407070b00001000301b40304140c000e80559000240c00301600076003080d1011170401d1140c080c107880020a650120980c04030705500d5404a06208044840a0780030511140c00c014000400404e250b20a104070800444000102ea081164608c04111402c0d101c0300780580d01c1540101841d400030f0000410540c0c01c128a0b0740d199100b201c10a040e8003183c0855110301c0c141500c1d213603191000380c111881040b001d101000081d0b00002c65 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 412955890 1250 412954640 412954657
    0xf0e0708090d11070503060c030f060d0302030910031b0315080a0302030f160c030c08070e1e0411030a05030405040c050f0a0e062b05060105091c080408010e070303020709020f 77
    0xd16066483c003010181401d00940003140e2502800041c010310b50341100c080c0d4020030a4a40142c4161203d03030030445060389104000300543c01c184802d50b40b034640802020040c503000d00340480c4103009049850f000010300342d18100401d42d10043c400950b404601c011f8040d0038000b0082400448a031000381d681d009252940f600f03240c0c00100c00841c42d44660603820a0b039800b41e100d40d10b4540724940029070b6003150040d601c052148040005541e90741c041c031a0f0240f820701035185038044208540f21016900203206445858940701d0108503a01e040292040c818022009551207900340000c100940d22070105030b60800406102c108403c00502089031000c1140c3d0802d280c0c41142400814024000e4403102280080105200d4644c441e0314200c0071400c41c00d05034100700305d81e034010040d1a1030241e60200364010811070900040001d2000f03480e40110f000e42c900c80d0406588407201420344d41102c0050060b82c100180800c2010340420000014140c072200641c1000c20004001c4014040c0004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 412957140 1250 412955890 412955897
    0x20304050f010c05040e06030613020409051c020c01020c03240907050d031106060406080706030b030a120c03110706120209060c0a030306050f0f130b0105130f0e0708090d 75
    0x4601041010456069514403500007400042652503028101c3e8006110740700000443c480007030108d240c00300c2c08510840050b012000c041c44542c0900c00280f050440403107003449031000700003068440510341e000c102405e60083c80005426070009040005d00d5640500a9011500610303c6229a081140c50101d880750b8814070f55071000f2003945440a2540a01c1d0805055000346090661094501d9242c004100445000b40c9402c0f05200c212412481104000d4220610500c20340b480b0790440b0840030801411203003c103085031100c101c1c0c0c040b050308030800b0600582540c810035810118251000346034101074310b54a403030100050301034060060300303403451540001c180d200c0340d80b00d506484554265000301d40d02c00c807180c50058001d1140e030060314482d00c0c6007404c0110300d20703040184c070164000c0500301c1d00051190800840140100203000740c1484010300096001d080b040e0303c4e20300202a04482d0186213460241c880c6407001c8042d18040400101804101c01c0210004031044105028607 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 412958390 1250 412957140 412957147
    0x5041211180403080a0501050105090d030f030b120d02070e2406070b090c03070503010b0d120c0b0c04181811011e1806090503070b0313060905010e1513020402 70
    0x1e400c2140c0c0401d071181180804090000f45a809489280301c1c2101600402c240e90325000150341e540034030712030b45074401c842d43c208000103482600707554400059818041051900000003646d1500054081e82ca9503120f502f541c118154104803690041903a0886c112241c1404511000c0103c0c4104607406c44114200800d00c01d174868100f1640c00641000c0404001d0400444d070715140e40c81c4000191107849041c0b40030440d4034040c4980740e083e04d4000c041030382800407665440040340c0300280c45014040c0111020380401c0150340c0c084d1064100c841032030383c4d86080a004010320005800e00180b0391745050b401241c07455030742c28215031480d003000c448106400860012108140300d01c64030745402150904103c182070f001140182c1c00408136400b898207549485045031940035030302c140d55040d44101f43c10000128040001c2d0703008080404001c3c4000c100f521500d003981d04912084039141c0d0b5514148101107020703c020b600c01c1403e04400011b174103004031507d1522448180183c4030f141e001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 412959640 1250 412958390 412958423
    0x324110d0908040b0d0203060901060f020a0b0a06030c030f03030c09030209010302060d0e100b030717030f030c0706060608190606120b030f06130c0618030f0f02220c050412 76
    0x710161001881c0000c54145d4a03280a02c462010f50001d40d0950301072080d000020600b1350040300115000c84207039000308135401d02505d507442c224101030542d900459441c040800400c1c8481e10710800345002d0302e10600200384a1500034101c3c0d055200120070800a600b003800127a84000815045030f4045507925202ca402c0b03001d40e8000c203003100c0903041c00d10485002904004007500500740b4200200e003034460396581c4801800709002000000c1c407850f0400c0140503d003031065405160010300018409041525a946201c07c460341134114401003003515040280403071518900f02c0305101c011005008880c94050050300b1f406075441e50b000a03d03140c6020080c242c030108a010011844a1f040b90444e007802d003101c0c0e0303085844403002d42e40101161804031382540190b207011009002d94540102d41032071030b250f00106507484282281e01c0002c4110143c050b079958000080800c03c5840d200d0b60043d00645000111508540950203000091000b0021280d0307841c2c1c080e0705136802c1200d02c5806c4070f01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 412960890 1250 412959640 412959653
    0xa0b03181912030f0e0606180c04062102070521070b040b0c0c011802181b0d0912080a0c0903050604023c100e0d03030e0304050a0324110d09 62
    0x1e00b04e800814078a440c0541109000001d1800d000321403c1d1200d0203c0105078856038002c480403148007185000400007045014801c4403007031030404c0502c1c0030003c581e030440100b07001d80e40f00f404195960790106107131b90101c01d45d000403034290440000d1a2450440c2c15a1485041d2000400c003400c940c58030030005a0b204800c4003181d00c0c0d0344030100200710858000400b47c40e4003003098400d81c010b10070080100510182c0041e40d0f4080d840c0034404400c440201c440020040d03020034030200c2800d8803041c20000150105801000c010640c0d296000340745006046001242c91941001301004010702040020031000f04640ea003041d01a0b0b042060307203103504085000d1081f400c140414190f031440e0f110a05080740709807600b182c4400c541803400c03000d41c220115014404a85034542c052944206000041c2c081d42c40346403070140d01400c3d40c0c1071031741e20742c0018030800183d031054800c0300700201101000b05501710101071030040d42e40c0400040c4440d0100000c64001c400c80c019075183d4612445090048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 412962140 1250 412960890 412960901
    0x20d1202190801031e021f0e12010e0c01080c0906090402090907020a1502030f0c0702030f1e060c0c1c03060b04032904030f0309110a0b0318191203 65
    0x5861a9007101040c140d0008148840904c419200604c088452410b540c43e12807040b00d02c40d40050412a088407001c1c608046041d10354074001c02c0c40a0718200c00c40988a403141d08211120b80400000d001540a505a0601c011556614100642d000400c5000d21044056481c8a072040c0d0b102502c0c0c039800008134000384038480070a42c5c403d0b50001000203081d80000d880c1c0d900c0b132280d070340ba10400400c0300c46101a40015160b08925040500014800034210320240520b1800201100d00f071810043c400ca0820180c6030b49160700204001c00c0c0d030034501d0100642600119a07a840318a883c0c3d101d00b91b15100c2c000700323030030708010100c422071140f07201c0c400e40011025152008040703a0b601e65a00d090302c07424003241c444065041c41d0f641813039000f00a514009220740d030152102c0c0c460824545048000300408203044404c0f0000c0440c1d07200a44034241554042d100c0101c40590b41e050001103080780c0400c02207041c14030b33032182c80c2d8004428800303105141041e0b4080c1100d800014032a0b42a0040e25 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 412963390 1250 412962140 412962157
    0xe100f0c0c1e0f08030301050105030703020d0603080301170c030705011803140a0312020a0e15040e04050105071e0215041106181203040b090d24150b0a020d1202 71
    0x40810710041404004a000c070b0004490b42150114015607400e0000c19520152042c04816001400100030765401080116070102940ca40180b801c69100301003811961203400c00da0b03202e000840140f00391003d120031085802d65003070041c1074101480000981d100418082c407070401481c60509078001400704441005160f01c1403044004030088000307140d0740c07055a401640001d42c03140002d1510941803080f500c00a426686403000300d9051001c1c0169540c10b04001001d42c1c1c8100300004a10904082c1c5601803840341d8004113840c20140740090555403003408118810b141d04141c80c800c41c0c0c00055803400c4e902048800013180e40d43d41400c0034a40501c00e80c01c1c0c2c01c0356001600d82c0c03009191130842c45100c1d404403104010000030010720740d50390180b4002c0000d200e104000040192070400288510144214040c02060500241034031301700030030103c23990155072600d840321141c0b030f4081c0000c1c010b0b0800d100303110f0904190a40c029941c40340e9001071401e00c141e40b80007030402410743d0111769400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 412964640 1250 412963390 412963403
    0x20f0604030201090c050904050d11160b0d061a0409050c090a0303080f100f060518030703030503010815040f06090c0509090307050106050301091110170a0903020c010e100f0c 77
    0x9250904020f030181c64001011942d041d61040003103a24940001002d000d00d400c034004140740742c420b07442600c0285e051701c22541e041c0321f15a0503940b4100c91010000c090419508415200d500001c600403d070380c050381080a1ba080b21928100101e1842c0c0c0c1914101c480040d40460103407a11280c01c40148500741180e074001e0499007001c000e1540001e51b2074000d140303074203009130582d0307450801006850b01806807440000c1445d4040010707a12030000380191030405010114003c1c84200040e14001c1140d000710089400880100102c0b2414408801c00307807030b015000c0e00700e4a05a5a0a21040490349000381003999801016044c040c06404030806410068407c40c5c26003094110641c3d25004114120b0380d0390309069001c5440e0030180140766107103500110103080e0082c5041000002000c3d61042402c1107002d00c180c4069503410009107000304880c920004000c40750b410001e00b0042150051170502c011404591b0458a410300440100f0720141b40c090b2540c003c98004541c076050900015001c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 412965890 1250 412964640 412964653
    0x1b051b1e10050a031e0c120c1b0201090b03090105100603110a1b1502030910060503120c0f0304060c060509161814040b1e040f03201b0a050f0303090f01020f 69
    0x4400c50340d000ca03086d040359888041043e2050400301098601e206144800650b002e10740fa00b4051901e540d190095105041c9000c00039210fa0301149070740c10895540400d1381d102d07424003000c90b0001010348040d180614042c0079944044181c00302a1040000c000c0811a12021402c5221408160084d07040c0e400b41010000900704032112003e500240e5603071907075002d0f11203c81c0500000b40700d400100c0c1d1000d4044d02411010303121200c50340d040840c003100240211100c02c0380503c014401040034148549591028054509165088520060040c0300c0340c0c4c4040d14044030707182034601010884d00c0c450001202150f030062980094400380c1180325181d070001007400308210080860704e01c10562100d440807825965492071885030002da8000d0075400481c003056020178443d50307101c0a0100e4003542c4020b036000d01e8810901e00100030524401002912645220700e00e021000e0900070300003280d1504030998644002074691183c4001c41c0d1244041500a11140c2d0007441081e400301c0281050360319 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 412967140 1250 412965890 412965941
    0x230d050906040c17070b09030a0b2806061b06020c07061e08010317090a05060a03022101230d0206120a0b010503040305030105011b051b1e10050a03 65
    0x391800c0030399040383c05107024070002c076000e510b400d1503140450404004006441c50038542918980c080445140c050140440c0342c1e0200d1046c40303040b40128100500800d0451180c45010b0003005000d0f0070b000160b0610350f08004059006980c004280801c82040c454102d162805000034410202d07a001680502d0f00002502034014400c05980410010102d90301c03581c8560480da04113090000401c00d0501208161002d5103800250080c80006452654030f0303a00c03a0300080f503035000120000006900012203540302a01d0b01c0c1d8180009000c81c144104950500b505090b80c80070040b10a9802e0001c443d01c2c2ca0700d90b0b5144000d018264014140550343c0d0b030600c240360402da01c100c401c4c000c841d045c5800380c101944120112403041ea0540d58460551742050011116a002503209800c03e110340d1841002145007404003400450b104220f0202800c03600c8240240216814690714004090511800c01c6403a42111404000024502681e88461202003a001071090150444030007808918205 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 412968390 1250 412967140 412967143
    0x212180a12050403060b0402130e15040207111207060e041e0204140a08190f08190206010f21061e0c020102071e050d05090414040c050a15230d0509 65
    0x84c0d9000b042e040c808607112805200580c45684460451999588010081c0c440c441d10740c0d80c2c01407d8803400303000a07000140024180d070007058058840072050700645c0b540d4036003414600070b030b0000e05d0042c0c14404e11f020b501615542103614114029510791a00c0c911603050313045001d2101541c8030f811501c40741c840d4003081000305100c0e0052b000781030400001c5035103d400200c088981200380d41841d02030850343e507054200c1c2d02a03402101e001c1d10610101503521888030382804400d0865006110b04c0d0300d8085030481082180d8401401c03401400c84003000310150043d00e0782900c2d08000301180c41e02c03041c044540e148094607030044600e85400c904c0c1d0f07442581034004003500350284c00704507500b89286003a484000c41503400141198440b41050a030f1501800241c140c1d004010000500301c001d80b8011101050304882c11610144030000503c0315203130128050010340880708000318041c0ba030030000341c5005811038052804a18448031400c80f5403480044400e0455054000c1c00a41000750109 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 412969640 1250 412968390 412968397
    0x160e060102060121080a0c0b1f05010c05031b0c0303130303080c0c03070212010618020d0c020f07030f020d020d050c010306090e03071e0b04240212180a1205 69
    0x203006015010000500c960b160070503c000060580d085140000681d0303480e11280e01c1900c50000b070080b9150104042890389410350710507082e5031240b000d602004120fa00111003140c00280c14042d54815100c0464000030a40343c0d0b40b85803010b000c0c1c40c2c040707241c0c5084c545201d0f010782580c14480007400100031450900b14008591084d1107104160302c80c0400425a0701500141c581250b10a02011300580f42a02c1d00c04440c035042c5000254280d00d540c040024498100c2c00003100e07540010f0001d080020328460a0b00c40300c0c26101900250032180011034840c0c0e2188005413121540c00c90b4030044d07580c1d204010191503030041c11460000c0c0240b500d1502c800614441c82e01003480c1c1800043d041c0c0c80c9014604142e42510007451401c80a555074000c006142e980e84d941080b91284900000303200d81032100d004034010b4620100d0101d41c499520303a00014400c050025034018802030154001c039241503904200d01c1025020300003040d1000c1403509a844401606005000070004030300c1c0d8020008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 412970890 1250 412969640 412969651
    0x9060702040501081501050a03030c080307120513020a050405010303141c0c03060311150d0f0f02040e060a0f0e19090c032102030c10020f040e0f060406050405090c01030c02160e 78
    0x7010340706ea82c1e820411141585900c405000304900d02c2d8402c00166461006562004035410102c00c100b20f910140300890f0411901215140c7c000c4003c4810b610b046403403e4010801142c0500a5605566009010401e41400305005940208050801d20100c1056100c03130703801c40c07800704400c98440400a01800c2d4501c0191344071840229941d00500b400c100b244031400c29405024074145840010200030071b0310a05a900b4035590307465680c20f0b00320a000400040090300060000f82c00c2045c2000b482514982c020440100805000c11041b21002c0c0c3c120b511410101c1c101401442e6642c81c04041c000c1220002d15140b04a00d004c002c100041c1c038880b094072400078071a002007580701d03016650f034410492403089aa0008000d20426072154000302007440c0320000d420b0a141e43e500703c1c041d1001003510a10b8011a10b482002480d08051044030020310f070454083c03095040005010303845180d80c0100a04250301d500600e46498001c0040c070f019042044202050f00da0340700801e40816070140d0380b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 412972140 1250 412970890 412970923
    0x3060e0a20090c090108060906010e03060f0a0c050403051009081204060606020f03070f0215090a0f0e220609060b0307030605220c0e0603100e010504050d0f090b0906070204050108 79
    0xca40c4101c024801d0b04c10010068644a0790b80c0c80768420400e4a46004210904001ba91442502c0c01d440600820340a2100c1d042c15150030b0600355000c2c0e0650740782e152020304101c5c0a1008001103040020018600b58205100040c4ca54880c1081045442118416212026180e06000410606900c184100c940c40d5094440ca0341602180d9074076445003060290124121030100000f40c40e08000c03522640c10030b943d0862604ac0800301040744e61566a0100100030741841041003607254504400d90b0003c0200031000300541c44401c0302c00042c14901004c0c00300c03540c50240d18104000780e40b01001c0800010704032611b007a62490054050f01040300c2420345524420008001650072080b00a18254001c005035106802e001c0b416034000401421140c0c5071144108506841301607204008404011a001141a181c5801c04500d0004c1e0030b03810364204510321210700c020300d070722180900a50780718030320b000e44d40e04404001a150380030b42c41c0040d5000d807900c000050b500c040041c51f16004400d030107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 412973390 1250 412972140 412972159
    0x80f070915050d14060604170309090f3112030603082724160602030a0e240105100e09093009011b0b04120201060f0f03060e0a20 57
    0x611000840000c3c0c440301c1e00800c6c1800305018000c0400c001041d204241c9041b40d04000c420000039000d1103096070401280207600062041c4c9400103c494001e491400000510b400c420b110b10701c03040e1202e910080e00064960021195262190b007008000395000301c00140c82d2895214040ea080e14008124180502490305038400da04001ca01800180007403400c1c02030003550058012030a50080c0d03d01c5c001000b40120303003800100c407440a9409242076400c001800360010a11b2440c00b00060662140a01c10b00031001d03040f107809070ba180c1500c42c15551000710b02100c0c0e00590fa0340c40c81c868050390011242040140001d40056504200c0015058034203000d04d2808580a560b501c2541d2414400300400000e2a694061500c1640b0058044507010308201d441d121030000c518155000c50ba140504c590300300300c4507824043c0801070201e0350003081c1e046140402d520015449071100500b030584a1152696180b010b01000c1100c0f5005085c0704000031680f104000e402c44c03140c40a0380316001b00c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 412974640 1250 412973390 412973411
    0x1030b1801060f030807080d05040f111e011407050f0d0e010c031e0903050a150b0a050f0f180a020306011209020105070311011b030e0609060403080f070915050d 71
    0x501410342120f403107801c014000c1d41183c4a80388140e0141400780c0b02d81000b049440c0345007030a407281a2043c1d00581709105544064035050100110f0400f9113442403080310b10303200b0003000492601c0c54807a0300b400c2c400151000310206903082c0c010040b01421900603491074048000c030102c2c071500c40d61501d94442180070b508400650b00d6092800703000d80028035841011084c0d40785501e4007444800c9a003402039003a0fa072666001d10f000d071490b604131000e1540041054800d10503006d03405030100304644103005141001c02148503c0708058100e0b01c2a20410341880403901e807940140843c9240d020000028a454040700002c0d5006540303440c0080c071400701e008199441c922610b02e0159059481740c0c5007004645049a801000e802040c001c0c0d540c61007040c066200840070390717560104c40d44010440b00040002c1c0d50a060005280c144980c000e602044002503020314196800300c8070000148842e12403200403a0318412941001c00006481010303000c44a0700203002d40303250601314409000b1107100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 412975890 1250 412974640 412974643
    0x624050a051005040312090b0a0f09240509180f100515040915080102030a0b0a0f0302090c03040303020c0118060516080c0c160909020a0603020708070f02010c0b01030b18 75
    0x700078800b00020310504c01030002070301c0c40c2030107045142a49002081c0d90344030160000143c1c48541410301162803100b17880c0140740c010504c10002e0980030320400c4030745540c0b1110340905002e409958200400081c56106a40c1c43c0801401e4001022300c0000e0701d440c08026402d4080d0701519056152041100c00150900c1d042c41840b800030424000c0a080c607242c14803800181c01007101e41d40306010408000b0071403100901c040c42c49048001008628045501c0500c0301302030b0190095000310305410828030160301d03104035542d005103002c820240c3e01e03652400d00f01c0c001d010b40c0300102c5107542000540002080581d80352072032503006102c2008640c50350041c1c40380c850301c0c0d500c400c00407850850008004c0003640740034040042d002016503420190b41105643c0401d000d400554461b0798030340040f015810b0046c0300101800060a04503d0100642c80352101ca0007030310001040c00c6030500810085911482c0c0c001d1030a5801007100c2d206503140c0c42c002040d0346044a182c043d00030400d4179055100030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 412977140 1250 412975890 412975909
    0x60b071103151009090f05101a0d0206040e0712060803071202010209010818010e010509010204061707020307022e020a051603020a031403090607031d06030f130624050a05 75
    0x9100d42c0700d5000d24604807034440900b28115050b80c51b070710403103240008610180a890401c3d01d40c0720001403411040202e848040c1c0b11840c1d124080c03240008600c3c01070725100b0444041d036480000101080d51001800c0710040101e40104401a00b805000580c0503c00005002c00c1d40c8140f10180c40c1c2039000804a00303e01518055500098020020500300c440c580207482d440c251141c0040380c0203070711070882c84c29030743c0542c0c4d8405582c1d40081e08202d8164004400c21181e4a016a84000d90501d10002907882c095080040d04c01c8030700045240e003074003441a02e4402d8034007020344500350140e00346000e5107481510703106480c607004044644048290410401040d240e0040c03103000c40d507040d522803640303031442c404441c07040340320400101d446030744c6040180c11101c1c881e540c4c0300203c03a42080402d0025021b00301d00c40c003407501481405001d0714110400c0e40c0c44494030709410302c0c812040c00e04a0207000000304024106000d80700e00103106000ae0380c500142e6000b658000e5920384c0d21418041c0c2440b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 412978390 1250 412977140 412977151
    0xf010c05060703110c0706080103151401061101150e040b010f08030406080604200a09140f010e0f040f02070203071203020d0f17070504150e0307060f03060b07110315 73
    0x1c11540c00141d025010342d0044550100e0324030780301c4c1020030b04680c80d131a004c16500300300007140706d41d001003041010000c1c49036204007c241c1e0a2040b0b04090078485000201801405c0a000d52500b0f4400103083c00d5201d01c00c2e41c05124901340f43d00760740d0104003100c040300b5981990303014001d600102c2c04224085144c004c80300100021840d1518203407044039170b50b0011301096800742d00d8000007a1844031505181a08043c0b4941c4e082d40d450740024060300c80d8219a01c1100e400314801c0400700e85507284000c18445100a003403d441075542070300056a103201d18121198800d2520f54501d40301541d9038003038026103100358103c2c2c0d8210707190044605003102c400c07802401070b40003006003030259200c2d016001c030b50031440c02c000b200803030045240460b0850072608580000d00100d000c00c40c120a0325070035910b058850a2507042da20807040401d454400c00d008160500ca201d1010b4026280320b903000c070000380388028100c0d48851582c0781c0844004400207505120344215415100f0325000141e440c4c1c00350 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 412979640 1250 412978390 412978393
    0x3010515031903110102130512010b0d29150307090203040f020103110409020304080a080123061305030609010f06150e040c050d05090a020306010f29070c080307020f010c05 76
    0x35800c0e940c51074022240200071010042c412425080d130100c240041e1086050700090000081d00344814400042c40e07083c0d081c0700c1c581c10b207900c0c3c60654031201846070281e07422803600c03041005090807080412004268602c003000e500380c108040d03076000c5483c01c0d140749800c50942c0c0c0d44079034445000d81070340000d44028003140305040d280c80040d070082e8416000c02d50203240742424130380c2e038820500032078104440170b0340c00140004801038625440003695001d042c0c141250b1050300a40765220051140031580300b40100c0c800500310903025109600e882c004e280060486195142c0108260301034a805500070007414100076021036416203a02c001c04048011303a607281041e0809008100161810107085800d0007002c020034101803071203004a505c2284114020081044a0720501d454114164494142e44150110502401c8103e4036540300c1c00d801522094043c03001100840080d100740d0700c008004000d00d180001d80609c010015010582c000c076003681848000c0001504ca1001c0081e004015 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 412980890 1250 412979640 412979653
    0x6011a040b13030803010b03100b0414040c092d0e07051912020a231e1308160e0702010b150c0a0c0b181009030f05030d09110301051503 60
    0x150421000340c502e22860000e80001d203035072522401c0207035100380c1024144100000400408142c401c43c01c1000f17001c500c0354186001d01d001d14541d1210000701c181c0344201e4071200505410b41c89607400a01405008280c0c4480000002051458504d20041645c00101da5900003c4a40e41400039034803410280d1207081c0b80c80400058806a403000b40d0031581800308195044200c00780758400750108100c252944046140340241ca810411100f0203c0781101c24200281d20112103005004451400103007400350f21013640c415005100c41c0303130f9007101c0801e01c44c1100e8951001d19080c48030b02280c1202c41805001d8540b004120300b40d800366052a5001088907650700030100c05031008040c894a04415280200206d903200c0c0d1201003154412203c494000c41d0400c81d41d0001101d062600408070b50000548501c00005000d08005200282401c3c40c4d8100d001b00b0300c44203104403074141d0054602003081003c2441c0c444060035403280342d64002d602c2c00d400548280d0940305000903215006004120 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 412982140 1250 412980890 412980899
    0xe031603081b030a0c1401090503180609040f0c17070c0b0c1c0b01030b040923070b0309150f040c03060b0a0801021602240a08070c050d030e06011a04 66
    0x74942e10050500c15201d032508035401d822142400a040c1400d0720b80e66400e10300207541408550b41c502c8481c114803d900d46012200000c0b000802c03100410031080126060320344610005000c3d008001685400c503090049007283d04001c1d600c01848220380c0c1d00d0355001000c0c0c0848094801c0c2c41103640f040458101e4003240f000c6070340100c6080d4010308031a82d0919007445811b092015081c01844000301c0ca0302c0d00c540a140d50780601039034820070303030960b01082840c006482e00c41d5480466050120101e0481c2e81c580c2c540071080c01200003030103115034015076a05050041030b54880c0507031410b800081d185404035480b0f03803510011074080d64100748009641c0b400e5460307000003400390120075684000880c0001600c880c084c0068062402141c40012481e0746d10300601c1040041d000104103140c0c01c0c4a09801600b08007400c0c4d52044045240c00e031410341d1498002e0f00c9000401c1000342951050824036401c00b98184c102c1c0400500350826109266640c1440c80150b0261011912a4080903c000e01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 412983390 1250 412982140 412982153
    0x5041202040905150a0e190206090109050910050405070e100305073014160f02030409060b0304050f0607021b13020c15130b0a090303090615060e031603 67
    0x181080d0009100240d01802541e83c507107001a02c0803140d6291045104100f040d844ca8070075070b005a485503000d48804142d0304840030b001c1c142003000900c1800c000c40c0700d1134140d02c1840080060301d000341101c6e805003040d083d451803400c40c0c0e2107014490780c00c002c0011100e512400d0402c61241c0080e000c1d0400d41c00050b4141c0103400000c0101007080f88400044140302c03510240c0b107886550791008810a003042009030000d45003108400651100800c05201b80a50030505684000c0140d1030414400d2000c0c900482c11440b4507881075406505010021074240d610f80d00071405648030708120f424154181d1102521044200c440d0301c0940c11450800c4485030100002e00d01e469401040e20403008500e80803c401c030380200c0151a20780d4010048103030240c0d485901b040d0415582a4504159551503a40c00c40c032510051990b0101510b035010001094002e4210410856002c041800207468204150745007200c00c1c070815001401140c0824450b050201c0d02c00d88010308200841d16031030071034035400b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 412984640 1250 412983390 412983419
    0x10b011d010c050c130e06150603041407080105160e0102010606090504021305061b12030103050706031a150a0e09090a0308040206070807060501061103030f01050f0a05040510240504 80
    0x1540c0f98058601154a140d840c1c00d035180407504289000500c0d44844500e0a1904a00900740e1042d1414448000c003240d80da50192684035500c90144c2c4c0f00080c110725603e04009155101c2a0300b50300303000c240b041c0300c0b00d0301d07603c00740340c81170340c0d8505005900070b100483c20390303040340315100100b54a504107000c14101034006060030000e003c1c2038524a81d580c80070400582c022185014060280030141715076aa09004400941e1002d0b0891800c55044d030320303020346820482c031420040c940d41e05400c1c040b18880b0111211010002410302030700c0c92503c4c011240e16070254441400281c41084488068500108280d001c0d482d40350081c00380009a9a040e0386400000e08242d0341b00c1c4d418404c0c200090901402405080d110b08000f142c5035240110180074610f01e50410001d1b50428001c00020005c0480c0981c1102c2d81295559441c49000020030300c1c00c04660031142d0068185000c1011020080c106401120122452014030994403024001c440c5840d00c2190300089040000300110304940048 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 412985890 1250 412984640 412984643
    0x12270201120e0312060f090f16031d07030b07051612020c0a09020c0606121b0a050d111302040b031603020d0906050420010e01260117010b011d010c 65
    0x40d031081d60320041e49103400003804449844c628908210903030a00100c030850188082d1707484115800d00c42c43c00d080c1080010103203034540040a4848400ca4401d80080030b4a000d5a0084070b4204083d43c00b0546510040c0401e6904000c00c2011a803407c1c8200d00300c0782031030420f44485294a64035518000007468000c1e240c4d0462040004000ca030780d0b19038501c54014044428010303a0364800c2c28400b4140b000c02440988541d0803107200c4030580ea07002c904140840d01c49800d14103c2240740c4001036010b141900700e1500311020f10fa01400f0011413514120b500c10040b0b68120f02a490403014030f0503840b075402500040202440802c00100c4541c2e15603215070381d0ba0901605001c18100b8520440c1c208680540d01c1d10349920510040c0131a86200b10248001101544080b075103039070018100b20501c0d464076040156004102203e0b440b0111450562142c0c05c40041c00345d42e44034990a03c01292114060340e07546001c00c5003510358000c0101b0740c1c0706005690001c642d50100340041d00d940d01c00180 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 412987140 1250 412985890 412985927
    0xa080f070603110d1b0806010e0a1203020a050d030212010506071a07030f110423030615150408070e0a02030702190609020301050403030f14010f030210020f070612270201 75
    0xc0130302d1821460041c06a260384c014141c80044280c003400400c02c000141c00c3c00c8c1800181c040340d0356551203541007541502c90030030048192640c20b140892400a403114080c0980c027078034500540b081c1e4150000d007800c220420b600b01880e40c90307108006242c840c0150040000c00107103171501c800714101003403d92000e028180000d402c0b02140e1141d042d00c8504d04042100300001509000c00501044c4001c81c0c00760640c01c180d9404c0d412804280e07101400303409403c4104642d40d06586a40e20161613007000026000782ea61201c2d503a41c400c41d41c40c81c1c03030b02805001300e05040004010040300d1080c0e81c4114907030780c01400d0310318500b112040c0000d215482074598036110342c01c00016071024044d142c0154802c0d074000400d00303940503400c02120722540b83e0700c0c007000d0f0210040000c1c85c500c28100c816250111000d00c03c040400d00300b40c1c507040003500b81407100e000f0001c00140030313600245101d003404101d0105001c2e091581d41800071007219607500080355000540d4010155110303c08802c0780402100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 412988390 1250 412987140 412987147
    0x406120f0c030b040302150a150b0f07021206060a0b03070f0c0213050411100c08040b0919060203040305010f0203091f06170c030d050a1202090d020406030b060a080f07060311 77
    0x4942c003c0307580e42150150302603480040502e4550008a840d20341c401c048010070020328440c402402840d0800b4850203407003c0000c5824444852008116500d4030b50013040d403c610901d165031107894500c1210030600c60490a0000640d010181d01180d110301410394500d503058861040c141c880d5000008141e0b00401184281d180329000c902c983c070300a50088007050141b8103003508200ea680304c41c0c00c03042c003005803c007800300000720071906403010b0f6413442c0c0415031912400700105000b00c80f07006109038141c408c4076000540c260080020800e81e402900203001b841600209035059102c1601e01c445c4960040580000c48810482c403c5e0341e02520010205c0e00503039460a07400400a40502c1d00301980201c4c880440601d0308201010002d40d01d41881400c01015500261040c00f6080d01c540f40e5640000ba6621582d540803201100c250b0700401c00c201558507418009207002d4111000c40c01110100030204030004002411004858444020a840c0741064021400b5040ca145c010100d4a001e1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 412989640 1250 412988390 412988393
    0x1020c0d06021c0903020307020306010803040f03080d11070b01030b01120804060806010e060d140a090305040e15090109060306150e1305012009030706030213050423040c080c0406120f0c03 83
    0x84c01000078140c000c0c1c0c02075450b2801801010300300302c0c040c2c2c172041465100308000c00812034083da0b4801100e41000c9000d031296002d01c0d010029149a0403802030f0003100044034000c1206d40003075035050b0fa00545806106a0702c0d60a28811740280e031501501150081c0300801420344a6100035a2140c03041c9801442540500c022a0322038000d0390603a00c030a911500e042c1c1d824405114407680c804c5060f0750511503c5445d0320040d00c144513501460180c00354000008602204141c0906240d80028040084a682d11807540008011500048508a081410550040c1001034140b001c1c0c4810310551190391311071001841d04120400e8040b26a07540782c002030050a10f0412040348038140d0114000e0341d400c0d401e8100350400c2441e410900038107105210044581d40d00c03010003001e4440c1550300003034002c0c1064894a0505002030709d0000149800104000c00882d4141d10084800480403281221500700400041ea0018000d54900307140c038207841400305403096400d582da1030050030045032050700d9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 412990890 1250 412989640 412989697
    0x11205090309040e01290102070305150f06060a020624040f0608150f1506120901060501110c090a150b0a0806130506100f030b03030406120b01020c0d0602 68
    0x12184200260000b0900c00e0007400d00d0301514100800c104003c000c078104c0840911804606200d80910751500051042090390080090030b001c0c5070001e086505011401c0e4800034034030310844a907000320082c03d01080540c04d014003518014030b00c6401078040b81c0d03220700c0d1440881a05415085d0481c1c0111308400080d2558400d0360000d02c4413a00103d00642051112031a20413400040c041c040000810084800e03066980c02d038103c1e1001080042003000800029500d01403842c01d030808056000c28440780c106e055201310201c1c1c1003030f294620f4940140d5030450b101d88111042e6074100491900042840d00b86521513000c444c0000300d00403e40d91281d03088017aa0300410051008102c0139000c1c48030a250800e10b24100c4231100c08107004c24644040802d008810032850141404101183c2003041e07030094003c581540000b800302c94607540d54220040c4280d80081d55260300600e4402da001d11544042203070501d010001d0481e04649500390744550080d404031f405000141c2c06241e022159075036 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 412992140 1250 412990890 412990901
    0x70b091015050603360304050f010c0b010303110307080a17060604060f2d020303071e0c12121b200c0607060207020405070504030618050c0d030903050a0c0303080709180203060112 79
    0x417100020360b1203c0c104400d03c81c400404000b40c60600110019000000320b600480c503055036498603081503080c5076012854654051010700030304407400469400c1141d0362140080a0242034050070400b00d03124113050058900c134501a400000d02c0d20710950710030310701445880b00c25596003000403510000402811094003883d544840050300000140600a82c1c404080c80c428100b0038012049000171038400f400d01040c8960080c010300219100d0300016004d004c51005094150b0020b101c81100c8030b030045403441400c0d0a560129040c0b0100726108400d04108080300303000c0d50700912a0007072600c2004000d0b000408200c034816000c00140300161a107000b0300b4026080354891640726421882c084058035281a20144401c0d84045c40b41c010030f030001001d681c4000180c9110304006100e040c03c07240010706801c050103501c206505a0b0400c06885142001c8034007a64400c1c005458108003201c00b644144282000300d15480f0403172042c54015070081d9002441410310307008442d02c00400c24103a40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 412993390 1250 412992140 412992241
    0x9040908031006050a120b0105190f020114040203070e2809030e030a0c0b0c0709090506100f08060103020402250501090327120503070b091015050603 66
    0x4602109110a84102400380b00140c802070074100d04060405100802250b0540300140f880c5403180c04039422640a1b01c216112407080000e05504142d00d100050008000e000c03108006600c4c180d00c0c2800d5030315803049240a654000e02034004ea83c42e008074801140720151505ca0b0105001a6208010500744c041100d075107103800e00414550078504018002d024040c408034043d03004614000002200c821001e030646507085106511b070306079a5001850401c1640020385034500d840c1c0e03502c00303111000414a101d01c1403145250f43c526217032400c03056815410b108000703041c0d204100600c01480c182c0c001c1c3c4400343c1c0d100e204086c80c0b002504c9042c0c012243c1841a43d82c1e0b5501d02980e800d16a0000038003d940306903078802001a120301e004078004140d5031041000461000c0003140420105204690b00c080c5c00010403080b6017014003209480e1100070310384030754203031402420100395661045144210380c0700034000e500315900c10038403400300e4024038180ca450300d41595030090980c400340c0d80a4442c0d0b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 412994640 1250 412993390 412993403
    0x9270a03090f0905090607080a11070606051c021c030c02040c121b200a12090f05150703080709170d02060603072601020f030a0903020c09040c1208090409 68
    0x2d00d048810003800b00b850b0480312030300381404100200e90000240c8150000d0007440d00d02100c0d40c9401d648801072000d0f08034000d0b41140003405c42d05200d0680c100206481044404249101042c020798103030280c840c100940185580c0d110f040d15558034494450404e00a0804056140c480e50004088170282040440030803d449002c00d41c0301e10314403c282d2100f01e401d0500c9521144000c0c05408440d141c3c0702044000d0904ca00310f09003610500840030655404030040d840ea0040e000041d1440c4001c2c0240c110011286400084a02d000301c118a00718000c041d00300c0c500300050f28111030b50301c4024154014000880300008201143ea11442603070611940a414240c00c0004002c1c1805009401144650311100c0d040c800c6182100104909000301d900e401e5103890308411440c0a17014050603803030300c02400310420445003615040810314038031075070a03558035403400c01c10808201401e84000c0d010212020b001e02180c2007540210451030300030f0004c01c3c142041000003805549252038110b409 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 412995890 1250 412994640 412994657
    0x61d040207030801091d0717071502061e010302010c0303020c0f0a0506060307120507060302070c08030a03020a1403041a1504021605010507050a1205060607200a0504060509270a03 79
    0x5d01c40d43c8a164901c560304000441c903442a641c526940b1455405120001003e5160214010008102520003051134074400d070420400e80001944034242111101c541c42c1c4a4681c02e0252400350002c141a240d058654400c3e220460f01c00718001c2d0410100322810388140d44100c05503a1080143e480c983d840341e0020041890300c1d83c1818102080755201c40c4c010079031505030b0400100042942000d5440a28005807100203034100650b0a241c103078048102c42c040012130104c042e40c9900140f945501640380e024105078034080c1c0390454031003150003030072400d50011011101c04000c4c4515802040900c01410711050000000f812a400410054098010006401c04010080c00360541c4000541400c0e41000d07050307035010780701162500040303030700b144d0b0740c00003810556900c1c0680d00301d182c001c14980300c5c01d01e4038030240d12340c4e04112140354410142e80b140000c4c0c61a00b800307480e081d03c501504820756502c454110302000240c440203048103007404541e203210301da010407090301c2c1c2074020303502c9025 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 412997140 1250 412995890 412995899
    0x1507050619020901050f090a0302090f0f011a071b0503070e040606080d080a09050a1202030a12060605040e0603031e0a090801020a050909071e050d05060a0e01061d040207030801 78
    0x8440500684074000c19005110010f80c80ea000802d0342c0003007a400072030076034542201e00000c0742e2250175000254444910b405010103050448400340c4a40640c1e40c940090742d0b00c5142e0b1140140e1041d04000691314108040400102e10047c4000300b051008044c610242e11280000d003041c030b00303410640441c6400410042400b506010f400000c00d660350240035045150301009100907001000044101d8442c442003007008402c008039507103242c2140c001480c0440300c3c90300035200c0e0b012003181000608500d000114182a602c40c050407140580c440310314003440d100d60f01d600408010f100682c14041488410161880e10011080294060754440d5441ca030812001e00041103603000307204039a00c14000144c1040d0464212420014125144002a660301008458003e0000c0c600030032a0b5802c5826001c8641100181a00080b000700600069a809051042c074540d14030034043c500043c070300108081409002c00a4690181c03010880d0341d00300003800314050f41c1c0041400c40c0010082d100410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 412998390 1250 412997140 412997161
    0x110d080a022b080601080405160e0402190819110604150909050114060702040f1e06060206090a1202120f18061305090915011205070e010f0902030615070506 69
    0x759281580e079040c101e0040c002d00c00038015000184828140482400030409002040150074081d151070100e030f00d1015110003900c04810300542d0220b0283d640c16180030030752543c480310501520102d00c000d12540400148444070090181030650f45880803464007a4581c0750300000784080c200d4040c030341e02030700704042d0020174205882c0c0c08040032628240c018002000ca0580d01d01d09890100c0d030b0036844503018000100180182100381c18107608d4050b01154154040728000c0100088034800c02010303990305400e9803550800c555075211a009400c0220000b651000181000c48461045829070580103400c400b05034022551040400c40200e41c418850300c00c1e5228400c0341e4400d95425044c0315560b10700d078124401e14041d4a00c40e030f400e000028100002044843d41c3e008200e04e1488155039035600c1c000c2c01c5200161305540501a81d0b102080e03006103107151a048500003100f4400075403820300e503800250006050594441f81c04d01240d440d80050a02070803145004001408990a00240d004c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 412999640 1250 412998390 412998433
    0x120506090303010f0504020702060d1a0f03010209150a09030c060c0b0a090818130f05060405071107090b0315191b0e090a0609050c07120306050d110d080a02 69
    0x20695000b0001440003206800e00d4404450007a1005a1110792500c00211280284400042207520740010031240d10545c0030140714100d000c0e160644c00740c82d00404e05090348225508240c12443c0da0008000c21400c500007003114170040e19103103110079200d40e40c00c526801c00b90701020000d00680034801c140210280000e800c016000c004000c009030564402901d8050b02c82820705007c0c510300c2c50b82e1035480d0701021005001119404100c10740018554030000c0c101610300790300840c5801c00048000d4052101d00706503902c10750051004900e0400080041c002008985401d8002ca410407810551100719207400741ca0814000000345074100c43c003100300c880c040424203680d0810f002c2940f46030b4001d021441404421f40e021441c1d0b9440f41290405021607521100351240b41c0001c1002c4a10803401030081144246102c0928640a05080f4192142c83c021a5031000200070924006070320341120782c2c0b040300c0c05081e5101003c25074981d00b03401d0700416030701c2d40582c1250840c003100c0035004103170 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 413000890 1250 412999640 412999651
    0x3010507020a110f1f1e020d02010605310e0a0b0a0515060d020f0408160816031a0a09020a0303030605030708210304030c0602040f0501030506030303160315030c120506 74
    0x2caa001135020000030f074202c20b021984042c617203615041401d11407003040138981850f40040c0c0d402d00c029105500070350350703084030208030300551802c0c1d0040b03140d00c1c0c1098280300d4208908800510b205a0b0304507000c0700d10302d560036a079041e503171425185284000bc0c001840303128090560b8004510340303c0000c03420344900814200903400089010f41a59503924191240480030040c0182c40d03d440907808111407245401c41e2655101c2e2030044110030756040a4102603e2051083c0c0304c50300e440308490324058401d400000c00442c8403c0304090100c403601d029a50240308508081040112030b004a400100c0341d8105a0010340c88000602282c1800c1010000030481100103008066219240d8040407030700c46040d076a2a40300001007800d140c03050240e0921aa00074070219501d550b1000f03003118040b2580f080f036000c282881c0c0012810714000c4103582c8550039141c2032100e00c030f40d81c403811801080e500e42c9101c46800c42c44404404981120180005001205640c054903960303810000e00d4084000c0c00d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 413002140 1250 413000890 413000899
    0x220c1809090302060f181005010602120705070b070c030624140603040219051503251d04060b130306050a02040f140d060c0c0303150f06050c0102040503010507020a11 73
    0x72158002580020034541c0300202c0041240d150303c40c940e614030083c54080707080c8143c1c4541d1110b60301e620855030140e0304a4119800321150f110003401071223194020100041c020b5040642c0c00c02450580708010b01410f0b01c0342e401d212900f600d0b60344a8085540707039040043d014010089011042122080c844040d00440c80d03000d40e804000d0300090b00074440100000e0184000b003411230040780040c42200080c2c1342c02851902601c4062003140e0040d04121114020744891082c0d070508001600c880781d41580e620340d078140b00c1a0110300d140003644042241190030a43e510400900945030380d01a040250091601040c0303e403030350600380142c4030041c01c043d1840744104400c1225101c019806e10886210b43e5840d402844408001400c44100e1180a0f007164202144190915841298469600c0c820749042004c03064032060b1540800c5c890007214070142c0110018880310f8040d40140c0706070b0f450072002615054480d0042425901c0c151a081c0c0940d005080070b42c200704014030302185a0300b00f941c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 413003390 1250 413002140 413002151
    0xb0705032704201e120c1e07020603010b16060612050120030609072f10110306040e10020403030207030b0c190302030a0209041506020f030306030705220c1809 70
    0x1c0c0943c0705031181d00007003d140c006800d6043d03600302440003601c010000d45d0401980620340710100320300d0395000e1a00d40c6140740650b0141c1c4959100b48094400980e0050035103801c60782408040849a4440b18100303c040301006d25110018080b40103600182c40c43c00010301914115180c91401d541080e108201d420070740b545814003011101060701da008004545440e0652102c0b0ba058031003040904000a05031250f80f021042036201880e10400f5801c180201c407480c00c620060b007000c4036030749003000c1c035001010008284640b60607000031045014400a450007409403560090480e03126500460160700491001c0051000c20044607500103840b4990b2454440498140b40c00401c2e08034a180c141940840807420034a140c1d41602ca80701c002074410030040b04c0c4c2400000d00300ca00ba1284100503c0362260710b0b58151030210581c2e01030100174000305000d60070001048001c68110545444100c8694140340c035540c80d0703001d203000c0380030541c880c01491a4425a101041a4140c024003d0070b400c02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 413004640 1250 413003390 413003441
    0x20d0c090b010918150b030c0405101806081e010807170f0307022e0e0306071d0904060e070605030a060b1213021f080604180308010b0705032704 64
    0xa410130f29a500d0388190000b00d1010040d25a41020a560000c1d06100d4000c4208242e000340c0c94003e000740da0741255440c24a41c0362000c1124247d8401c8255406030b5411035042001a00606450b0340007142d1071030a96a2825101e0b001c86140800d85c0a000d00b58442401000f0407880c00c2c0415000550001c0a050b0aa0090a0f0a5038911070104024082c3c050500000317200b442c51800c00ba4580005000d01022040000c1d005008800018429109000d0040803d03100c500a076109924420705260148107980000304115807000000c02c20b0700c200d03483d0810176008881c203100b1500641030030786030180c032410503403032503002c0340c04036080014811001c014551400382a000400d50042c4413014500d00020700d440807441d548080c0d03529805007101da400344198a07402c0611f051003034200b5a4104000420302c0003601e0150740c803c0c8040c000c1205d0b0b40042c440e6a00e080d0080608501403022246030203401ca69030724080b440040f0009840607541040c104520f01401504400c0f40003d4905110341d400c4d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 413005890 1250 413004640 413004659
    0x20306040b1005040c020d0801090501050d060b15190e0102070e06130f02040f09050c0301060c0201050307020304030f1a0f060604090e0f0d0c0b0106051c0e0a020d0c090b0109 77
    0x103840541081c0c01d00303000645440c2e91031194030103070801030710510501803035000c041d549980c040030050206505400229880c03074248070391070494000501c00140396032982c03a1071004101782101c20790040c6400908000d050301400c02440e009888011041082c1c60580005001d00803401015045420403041041604034102205030012411907074000440a04000e1000034010f1720301e407130011400403900181103641780712404e00b1520440e5003801580c1c0d40d05003000640c0303c04d029100c08a0600768411015502c26406076a1026080c01283d00d410f842e52039400e412790744800f0850f28408222214070695031140705054000440d0655003e07a41840320008415000303074043d5210340303561940258288041040151703880107541c001d07100700d01c0040304020300c981d0b404841510146000b60000a80710710801c12a51080300c0c41c640791806100c0a0300d46006000003006a03d141d00c81c0101601c09039640261100010344284025202e280c6000d904c071003030311117544840f414071419240070004000c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 413007140 1250 413005890 413005903
    0x1050a0e030a05100e07050d05061611070e07030b1f0e06070b0f01060e0102120901030203191a01020c0406080616031103090a060f05130b0702030913020d060609030203 74
    0x680381854000d14905a01181c41c0ca00010400351042c424035200082000d0b070380d403002c102800d010b000e0f50301d00c60312001440306503203803010010110b0f03000600048402c800311030444403405030f91604040071510104d80a1034100560029102c13090110305129200740c05114074600e0500680d4071040d1501052540300c0c20402c07440c111414080d810000d281959609800c40326103a900c200c1641c00e604250340144c02c00781c02401904045800300e404a900740d800042c80104d1000c2903d866490a2a8500110080c0d040034104916590b400701e16201201032034003a0700c801c0100d01c08020090010030f03000900d401508030040340658944501440030b0322021802c10707402109014071491403288490114003c00700000d00c06100c0102005000031a00041001551640030b000d0a000c02c0960035101d8080b200d069502006002c0818051000101004410f80e40400d003801980c0c01d1074810340120f13074960424001c64900c0ca41c001104ea4007551144200c0016266900e0300c2c1d0aa0390460717003c282d0340c05 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 413008390 1250 413007140 413007157
    0xc07021002010216030905030609030c10020f040f080d0e04061a031509130303060614041202010e03010c031512050307020112060f0b040806060d020f040b040917040e13020105 77
    0x15500c103480d00040c000d40440320b0040140d01010003000d2681002098040f040c05803d210340122404551030250020a4070800c02031000075200380044186080c000b50300c16840f0000c240c10a01c00058421022001c0c2d200800d4071001400301100c2032071000386480c2c05034880368030031454140107001c01c0700741c1240b405a020f282501140d481d1540d5000e44a0030056113105039203c0303001d0082003c192480450640b40078400e80701405055201e1034103540c12100e44510b410382c000e0600c000c001910000c000300c480d007401030504048a0410704080b17803d444541a40301d02013510381030070205529882400c040100b4440c0d0701051a8401640c50948038459148042c1c10001d55a4010b4001d040035403000c0d00034020509666a0ba0740d0303551206580340c029109485880c05020000350040c240144a400b1741d03a4000c0008d285800c2d040e003008000d0061035049600281e071280d40f90002400000e400006400c0321401540301d1f403406a0b8031006a5009040084d01c2e0483c208680050f40c100007503402e0728 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 413009640 1250 413008390 413008399
    0x12060a0e06011809020307260417031e0106020303100503010207020d0803060a080a03020606040b0102010e0c060a050c060c130f060e040504020402090405160f0e0a1403010b060c010c080109050c0702 87
    0x141e020f01c104280c418040d400c120500c500c00403d1011041d044044910303d0150034511100e610725070580c580d120b20040f58040c1c00f41a28a03411a1258044001954003108040300076075000c03030207011458000b600340c002a01681c070010902c81c41d808054031000091008400a5103400c06541c08181441c0b500e04004200034001700110b08a540c40d20075410240c03007090201e4200134a2070400030740d51081910150f008500e060110701e459481800303600c4100440310020007503031801c039060200c5548121895004c021703044c4408842008213008050040c0500d443ca15105d0300d604c0360a40200c003a950004112081001003006800c0d0842c5441100c4841110002481d03074842c000328000e481040801503029280404118030004e5a410b401c402c1e004a940d00044071810035026141d550b01030000340d901c0040100d042241d640c50500011070300001600215044940301d010a40e2034100c0c00c145040e994441c110034a01541c400000d60040c524200248140e060280b58010a441800d0029024 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 413010890 1250 413009640 413009657
    0xc0b04180504030c0506040308040614250207050d141c0206150a12061a0108150405062b060b04021e031003080301090b090109090203030301120f0203060c12060a0e0601 74
    0x14103000d4404004002d1704802075800610f06450000c042d0b440494007213501600c3e000302d44010802c00d41c0d4540c4500c1c24244541d50300040042c8080c010500802c2440c01c522481e440401c690b10b070b203644542401d1280c1340070f42c11504400000d5007000c40c2000b07094903014400c658044000e0b070000f5010b4000c80c2d6188140c1e841261100891442710703064220400f14101c0d80000020405e442e400100c900d1803007a8100003080c0c00e0001147c0303860042c4e443d408080c02030f000365042e910f025844180c100300f008000c4800f40130580100440034034807480780f0380f4014050011800b0700046000c0c54549000488007107113040d94520240e61040c5650507482558036000c000a030500000129801c043c40d0404200c81d01ca680d110700440203000c111000034010054000001842d842d1401544000d42d4000c0155046070708040008007039545042c4280ca05489942d45c035030260300c1c00d004c414000c0b240440b24660311918148032910a500207030101d405408210420003901104071880c0d03400600910f030540303e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 413012140 1250 413010890 413010893
    0x130c1512141b070c2601050405060106031d0a030f0f03050129120a020c070b0f03010b0f0f0c0109140d0c11011416020427020409151401030c0b04180504 67
    0x2002e0040c407000a14075140c007130300443c0b1504e0300194104a07143c0705640e007402c3c180c4400203900782c1f18107a070001c2c102d50000b401844118042e070008240e0071044500c401e2000c8222416610f0208101e0060300410014402441c24590016804503560401e040501130340d49000214604880a40d0391768480410b6854400101da00c083d04a803004100c0d201c01d183c080c200001448000d502c9401180c540f8404d4000c005403500044050ba0000c051082c80e01b81140c0c680b880584030b941c000385042020250800c82e1444050f02c0b18068655440239000000d2041d455140942000004019906095115172075894450b5070010030681d40c1d590062450212413050070040e6900400802428071041c03000c81c507040e050384c040c140380701403d000300ca0900c01031050280040c22541600b1f15081204284900382000d410b10340c000046552044c070505010381c843e040210112400b00e0309030b614105500c0010028400340d421103a0140020b0ba0440d85443d240482900000c21021001c0101c5600e40c0000340 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 413013390 1250 413012140 413012191
    0x30403050909071718030414030c030d08060310020f070f021504060513120206070b062d01020106142d0414010f06030902010512130c151214 62
    0x403001d4901400400b401e0038580c0010303040000003202c081d4101c0712040065000c0000e40812103592260300043c51a20303003040d20304c0c42a00c02d080c0c1100d4040c0308020000e10140c41c104030ae80c2c610b840c1d41c0d031004214107042e0205414141c00408131942280144140c01c2d5903039420044906240e80300d041220507000a03c00300ba450401c00c014210000703004640042c0c0981c00c039005025007100301c0342d00514540c488c425851042c21200303010b9080841070144800140340c018046400c004020f11060005100c46040740010510b440005a1854005003c40031541c09004040c0603003d800321030038170310081c0800b08000b480800f0f03244c4111070918030718421400941c584c119083c103011b0000c0c4940310107aa40c0c0c0c0c501007000c0c850003e140105020014070075209100d00780200e030703050750b03043d152075031008200c804440050700380c0796a030071407461110000b80424030000041c44003038696412000c2081000c0c20030392100c0016500d1600b0304181c1a013070043c400b001544450050b20032a4903503641807069 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 413014640 1250 413013390 413013397
    0x7140612100503010e010b0118030b06010503041103031602011d06181c06021308030f040303032a0905100e090703020c100c0c0c06030e1e01090c0909021906050403030503040305 78
    0x3505546010305c0100d1008040d0451034120000380c071062102c03900c0c00c0d01c00814041911010303241c80081000301c0c29135849900110b4000d03000c0c80d0740607030301c200550001c0d08650102c01214241c20b001d1881c1b00842d6000717400e1442d55000451490328040c00280131800311300c1400c00410844050385d20803000ba43ea02c407a608039800040c40756000d00c0c54030349020802544071517003c6044043c10880050442d40c0081280d0110070007000c894101032560f07034242c0141645040d41113411844180301c40c0c103c0209080d100b0642d03029510b801805103000b06100080d00303901d04060800110b11840d800c65102d01048941104442c0f80042ea00c0f402041e51605001d980c2c81ca1801171400c05040840c15a032101c04d40b1041c600503501d00000a55401040d011100d40304500340303084e0401d681d8050007803125104800355480d284004070b1446820350b20010a800143c000074606981d5940080950030150010090103501e070191a101c0b031b080c02d04c0541180140d100040805c500000000e040610480a8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 413015890 1250 413014640 413014649
    0xa03030b031204090203150d150903091508010e01050a050d021306050607060c02010f090f0b06011806030e0d020111030408130513090201020606011806111c050c0714061210 76
    0xb042d4481d616510038001952080c0c55501e022920040c0300c0c059490114604c0c00c40300d600c11414500c0010b50380c840c00c080c10140350140c043c02349801000a0104540d0810101212141d5580d2450341c14101d8002c001001078000501541031880284a55220100c1c0078040c1c90f0101d480141d0250b06019007000741c80c8603000190042c4020400742e003009442d030007580303078901150000d01810900c10402801c90700d440f000a00032090300c84112000c03c0018040311342110040c94051990141c94014004804080e4002c000280d80c42015160400007400640d548007110300c001d000e00b45504074400d216000140c4040e03c0c03001c0008094480c00b2804004500a20000d8000410402d0386540c5000800712064164054040d43d80010a15032040c040c003032156044600ba17451a6042010440b0f8400c00030b0640002b510a60b400240703100d2041542810f42c001664820f903882c0610208a0b00323229141e4090540444941c0881c0a581c1d180400c0e80d0207542d03150b48100c2c40b6921010b02c0030010368036900 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 413017140 1250 413015890 413015923
    0x703080309160609081c0509130941030a08280f0c03050f13030e061204030f051201140d12020723090c0a02101104050909010c020a03030b03 62
    0x10000300e503074001e0403d104540e100003d03903002801b402c444000780d4030aa500b003000924200440000d504e828084e82243d2006910700041c1c18110341e56442e240008648801050079804d03134011500e0384c01040b094400c1c41c40d013034140c0d890100000b445a0720300a002048003402001320000305601aa5000c42e40510218807121040c0c00c2508410380081c1064030f00950900c2c00c1a2030408082c0c0070740203c601840b800350403000300355140c440d01520a142e01e4000c0301000f21018059005a0790900030b0300d140745528200101a0505160290041488083c4202804002e02411030b080c415802c2d56811903103000c8511420b04254000102a00d00c5002c1c000e092901142c400642c0ca940026540c00b5200e01030702d0701c031008000c0032400800f81c020803a40e03a40603400b100024440303c00000a8850081c1d41d0044410209a130b49003102914a07030100b5440c487da02080c1082a40350003d051a04401d405008000304884110000c0d124900508060709240d21100e0192850301e0030010b0300ea81044285 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 413018390 1250 413017140 413017183
    0x909061c05060a1512050c150d050a0b2d01081806041505060406030b060d0c0810020304020f01090303020c311e110412021801031406180703080309 65
    0x30300d04001009010700e07540c2210085135020600c100445844461290890018050318200108000c55095598213140000d101403150410300f00c254003420740103c0c0312050200b400d08419061001000908450580c0d1088415102190381d401c1e4221515102d401e107896501030f5100740f03d035106000d5250b4504481d106580c10002804100c400c941c413101d01c1e9038014017181c0c0b280f40400050701c165000c040c0411501001042051600c88a02d2041171701c03880d00008034a0b031314030703815080901c1096000720303568001040108501d01582503502c491000d0810032041415903d001b55074100704502c140c01603d286d91483c8d2445107050f0031001000b9020440c00040c2c0c1a1743c074007009800305c0031410f01a03006009203003000440c640100a4010300c882c0d00c9c60f051920700404680c681c500340344281d0b0005060404440c8003840da10201e80614007401140e452008201d60b05450080000e021201001030092403c0a040000c00c5440c1107d400200083d12501c641440f54208110070074000342954049 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 413019640 1250 413018390 413018401
    0x90b030903130b030603100b1c050a0c0509040809010f0e03060117100501030b06100504030f060c0e0d02030304060f020c0d1b06050307080a020f07020d0b1501050909061c0506 77
    0xa0900c801500340340c0d600b080e60741e195604140001c0d20384540c10f03081042d059415a406a1280b00004001014000c40e59200c0035400a9030f824104107580039000001c41c202800b21107000840142801e0b641c98001c0d05d8561180911303805070040460402c02e040180a171003a00c40d00d031459400300000c4c1914065656002c00c42d10040d07a00040c0407403070044031024841c2e9a201e03c1554100e9411200711529980c130743d410046540c00b07890800c018088103100c040081100441c86080c100e02c19413001035440e004490240c401140c410050703100d0f4011821131801610040296012035295007401a003617080c00c0c1069051038625008950004248c0c0035160500594a0012588006040c085001c807a1541003c8444d40300c1200c030000840e000343d0100341448115402006241030010240c0d0030000c03560b0000e07a0f10490220140c40003039449092190540b800f456406154100b400c103030b40380c0300807200801c5521500612140c03081e198050204030b219082c9159100c401c0d03100085e1140f51405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 413020890 1250 413019640 413019643
    0x1b0706021213030b06060d1a0a150c111c0c051011070506030c0403050f0706030c0203040e0118060f03140616170c0f1602100203040b030109050403090b0309 69
    0x118452880188a84802801d280705a10111404000940c0e01070103410f00310744400c442a0303005488103070400c104001c200c10018291103043d6800d0f420402c1410541045400c0140440c07a03500030401114551520040064010f903800621580c00b0741e0000c104810390300000c691000d111803255940d98505150020040300e60051010340b9000c031011140000c2d0518100d034104019043d03046580d04c1000144001d141c07120103544d00002003100e480c942602c80d42d0b45818a181319941b40c940b5030017010f090001d907406006501040260b0720045050510340403204013420b0040c0f2070101860341070b40ca144c900d690aa0442e0026242c41200d1400300d95603464180d03018140340800e04464000c01d00814500304403009100008011540e0781e00010981d5a000581110090420b011901d402c000b01c1e40783c041c000c405800c0c20816540a2410101140103001c54251010b44501c00c41d00200002c0c00344417011000e49040d20300da5200040d0650312858162903500807500011080d10340442044100e600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 413022140 1250 413020890 413020903
    0xc111e0c0d21050c07170c0607030c020f06130b18060309061005091e0a090c120501110307080118060b070f050d020f1e280b0f07091a1b 60
    0xc030303840000308003000b92002c0f24240a0361124281c2da070018030303040214003841548080101c80500585444181c55000130b140c1d40d0003003804030040b80a5040c80c000358130b030045000c41504025680b1914240844d02014400021405036071507440c0301241d03600d100b4880d04810210450081e010903560706115446513038640080310740400c0034052100c081402d06040c08100d0085820244680e0841c2420850480c0390304005c0c00c0ea040c1555170754010000c26902c2c4411002800802d0090400a103d804c0c85800e450040d500f0303001310f40b0100140900310354030050003411174052001481c110000c0314000400f4151070b6100251000c0041600400d00041180b200800da01c100100d42103003d03008020b0362190702200460380a900100c1400b074400c81142d803100d8042d04d000040d80c2480440701305440c031200940c2c8100183c8040b40c940e50041103280d060041e00980414101240f5180a010041c0000c00502600010729040c1075150038900640068890394100c914805d1075420402c40803e40c1c3d4013 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 413023390 1250 413022140 413022173
    0x13030b09070602010b01050409050711070e16030b0907080903120a0218040b01091404060509010e0702060702070f0303030c0504080321060d021c110d050f010c111e0c0d 74
    0x140001c0021160b00510400042103010b031501030900c0e1400c05580001c0c079000746860203102544075a411054418000c810183c04500070303114140c01e00400c2040400d1540941c48281490900b19461607a43c140a1030f90000980c03400c20b640ea81e0301070110381140182d00b500a520090241400381e031140717540103010b180c03c00e41d159840b5202076404000175070700034007502408680081c034144009080d10305260440000500301003400c0340e42d080070843c0506c00341d0120711451414000e0040044d41881010f070010100d1000700001410703c4c000700480911440000c0c1810303a160704208501d40110305032002091640c0a0300c0d101c070080c0411401c5076803910358404a24400f900041c01c1841d01100222030303141c016080100144010000920003846003000380d407030700c0030415055016503811840e01f100074030840240580070144c065181c00e5507d41e0343c1c000306005c0c4c64010300c0303030340c0394005614200c04400d44152030007500800c200c6410402d038038100700d07000340304040807800f40301c1c0300e0a1415090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 413024640 1250 413023390 413023393
    0x803040909240507140a170901110a120501050d05060708100f080d0f09140d1106040f08070608040b15510a0f020c040212070206060d2613030b09 64
    0xc280c05d030f5800e28148114110704001c14501e00b0a2424802101e00e101c1c0d20013070a5000050011a03132094840741d403c00100d40d00050703840300240400711002e000d1580140000c1d507012085c0c980d1903507444d8035904000c000138104000c0034006104601d524074110020401e07140400c1c00562201c1c1c0c00c0c1e880d00301d00c04480012614001410301c0051041c0e42c000e0865903000401d0000340c006100b040142450041d00750740401600d0300710350b2070740e0300c01c001000200110344400e050701e441c20449a0500c05158462030601c1a502c00700700105452200b02c07548020040040805030300c2d01d8001951a820340a00d043c0784c000c032180f60780441c1620244030389900103030302c10003141c42e4042c40c00f41400700802d401c448800d03034040c41320405040c042c0c00c201c20900554015070f0031020516001c9801c980003202550f003c0141c101c1400400c5805018030b41c0c0006c17090302d4200c1100c02c0c60b203030303041481c1e10400d41e9203081102c52912001e55809905540d000b6840c0200600340a5480c10010049402910310705080d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 413025890 1250 413024640 413024657
    0x31b0a030b0f0108013c0603060305071a0f0309160308180d05120307020721060c020604030c172106031203040b010303050f0903010c030608160803040909240507 71
    0x1079800b8108aa0407694030040b00000d0003800700c0903030421102144159003000c86d08000030342046403203203c8000780401d0381e0009060792550605528020250384000700c050048207007090000e0342402100c9c00b000c5180d02d01d554a403145a07015107005c00c00340301d075140e03407440410120420556030002c061a0b41c54041c000d070700c0c0980204001408840b0079004002da03101c4210b16007000d07004005980d0140349401911521559003001c04145400d200010300c5921052041c4010400c0504c511030450360144014190b83c90300c0c3d58003409591042e8009454400c0034400c082080304500100c402180c0480c42e03024074210b560030020b00e2090159079031442070140e83d00611802400744140c03417003503410209440050b4a1a107090f00d140d8801003c40504110400101c186031720309008100140c681e81c3d40c002204c03450154803600300342c901800814480300400040000c00350000580f810348000040010706400d00d0f241040c008000381d42c52001d83d82d0994041c12140309540d0015102c0d02e806c3d202d02c000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 413027140 1250 413025890 413025919
    0x4050108030f04140f1903020a23010c05030d060b0304021206061c030201060f0305060f0105010806060403060b04021e12070c0305030720060c040f1406040506031b0a030b 75
    0x1102d01a0640040000800f84400c10001d00781e25141c0741c4841e0050f22240990b0a550b000c1001d241c803a58a41802100c408410000c40c10725002c500000c01c101c040c00007880b0803a4500013440b65904d1003240c10040700041800a21030107104803505503200c801c08018040e500c0c00d03611419001243c082e449217000b04022544001d02182c0140f003030000400e0142c40085485070b100e81f80c0303ea03400030340440d942c642005c1095004141d198011354025001000945010501100e08250507000f960400801e20300348155600c81d6801d0b05c060ba5404000030401e4500c0c0c2c07001c01c0c02400343c410140b58005e1102d030414290110702d40146000004e807900480c0308c1e0340d0007505844007070702d00c2030003000603c0c201300013407440d0310600107401501c641c020074440344019038a010f49054401d0302c1000e036202001904201036041180b10400400c0714110000c2024644000180d040c061703031040a0043c0000400140342502d0603900002c144035010b4401d80747d52241c40000c00801103c00400d010703032024041004c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 413028390 1250 413027140 413027143
    0x204060e010b03070c05032a0c040903021207060f09030e01021002090a03060c020a0501112124060c010c0302070c0b0c0606040b040b041b08011d0609070c2004050108 73
    0x181640c0301642103e2031500d5000084500b40d03071800d011390395808144101e05590183d500d0350010041e01045960558441c05403903401d24025030401c0744205c3c9850000343c00242c01048090030b0903942d074907098513080c680c00c0143c0541500821050b616107060320300420941c0182920300d44200c20380c212400886401c01c1d9004a11a02d8843c543c08010302c4070030000111550060200c40c034180c41034540f028525034078542503400d03000040984a0b00860150000c01c46400145108914801003850600b05403c0002d09541448074071108680101442d0143d40c98120864072414243c000030440104520350013030094021210869103e0000c5e01c00007090629030341550181d0f1081006000c0c180c41c1c480070071000707010840200b1b41180e224000004160380c0c902c83c5800030410f49420034000072100718010003140c0140c0066061090004055285091002c0c42542c000d0781620036403840d80310680103485440520344d00400980e0b050306158011801c1d04410000c4800517902032006076250303210726 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 413029640 1250 413028390 413028419
    0x114101703180609040c0c0215040620010603140a060b0f010e09070e0613080f061009050402030709111305031f020d15030f0314090a03030e0a0b0c0703020406 70
    0x1029a00a01a8100c903254414039919100c2c0e0042000d4505440300d004202922444807080f000304000c900c5c4482541040800d400301d075040c072201c803403402e410305c10040e06981d00813483d440546081d03551402481403d50200c80656080740300152076090a801e056a644000c90080b42c5a07818901d004043e82400c0051040d9100140c540340704600303000080c000c0b501002404041001008912003004c0e4a8802c02401d80401e00700a040b01d450070214041d142c1100413030f0151040c2d11050070003005141c00c184640a4401c0c9030800305964039070303000103071520500ba00300c0246907107048100d403031034440140281802d0003010440c02110740e8460805880303d00014a011844418900000c10b00c40303140e005041049030b5a00025215012000e10000c003a204d0704112506002d40085902307054100100440c4600b40715440d502d081840d1020800d18100f9210082c103200820300c50900554030041601d002d03001e000c0b0843e032541c5581d114903981e101103100581c040c620380600446c1c00764105048 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 413030890 1250 413029640 413029679
    0xf101802010e09070207090c03020a09050a03030816050706141f3c030302030705060a0501080a020409060e0a0c0f050a03080f0a021f1401050f09060405060d0203011410 74
    0x1551040a10b0606100e8680707801400c0c8021805031500214021155100319074402c038150f54010f86440c0c4190024042c0f400540100e441203c40e83d20400c0040d03880807000da449204200254500204200140c9a03402002c134020710b6070b801c0c2590384d400c044284240318861001c101580501000100f00d038222a1414010b00295240041c51326800d680155004410280d0300c0c181c1803030324a95000742c8a15140650030840044c1c0001440c40d09000041126a400508141c410070141d4901620b26a4504031180c4c002d0103181c840884401344011544590001c030340a07800e45d0b03003088503440d2050010f01d01f4002c041140001e0709020489040056011082c0c85e40403000500e00011000c4034405600320001400851050788000c3c5c5d04003000080801c03481000c1c1070b01103619846403035030420316a4160070440c003840201130000c52581e00d184d06e040e00080150b800058540712600810742c560b840860294040d800e10b070402148034406c0660328482c0040f000c1c0c111055031a6202c0b25210b4440045 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 413032140 1250 413030890 413030897
    0xc0c0b120402060a023a090807030b0402270415090c0e09191101120c0807120e16082b080a061a0309010f0203090a0609020f030f10180201 61
    0x203001803e02d40000d0041c940b19004907403800062040041c6010704070382c01040b040d91168422a9400007002d42070031420050704002c0300183c1090074680c2d42e10240e03c405498480050042419501d03800d88400080c6081e000491142c031138400d458524442c261012a00c0c0c1061545180d01d02010348607019401b81c0c403c40c420021480c05d400e004640300302508a850500078a121254003c032a102400055803081400001111010001401d0103852126100b50a404d207051070410507070000d04541d111115040c0003d054085161040085c0301c0e040c0c00c0800c0344a68101d0010a5090601e6501107511440890795604900900f02d0441100c5900c1b2031584001010369980250061001c25804241604002003050382d036980a4910071801c0c240b901d10746030000600406003002e00403100c064004100a40c40c60401340c0000b69110460500034000d9aa00c83d040300c11541d4417161b000728680c0003000c46a0f1021400001c6480342c00104d0030105079840d124025286420040c0c0346101e06030144c5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 413033390 1250 413032140 413032177
    0x190801081914010b030d080405010b01020a21020708010c110c0f0d0b0c090a030b041e03080a1a131e15061218080406020d110d0509130204060c0c0b 65
    0x281c030145001e03818a0b020085548070441100f203500c00300203034007014003107030b5810713003a030405041090840e800554002d0442d04180c8203080441d5a840e10403a21682410010f04041e03546001282005015001031409500b0500b85d00c9100d036005004950f2140800c0580301410095810044d0441d41207035901c0e0010b120440072070104810f008015805040003410381d00c0e080711003000900e00d14071034000f240c02c400500140710502010fa014146142415601c13180c450215480161280c44001e02a002a80d214480110551401d50b09130804050103040b10700c1b19202d800b000340c05007907005840c451032650300c3c1400c60001c50038050020711050f06c201d20f00d00942404000c50310001280d52000c021500d407210754440609a0003521445405642559240d6041070300c000e04113009080c0c1d0404210011903074005000002c221880603201c10b0803c0e980d501c10181c08201c00b040c0c0e892140001c5440403a0001e16150842c142100d104d00c160fa0240a8603141e10440f1041d000e00c00440b4807105008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 413034640 1250 413033390 413033393
    0x801030f0605090a0b010f15030920030a060509010c1b0b131e0605150105040e060909161203020114091902042706060503060c0a21021908010819 64
    0x5034802c83c0c00208400c240c131085015600c44002401003a0f0000b0301d040040001000307500702e68000701014071032a180a0190304919200c01c40003d02c4084440040c1280022071400c540e020008405d881c3d500071014001460080b40701c600805080840601082d580a02c0058030115099541c02d0b240e80004a18290346401501203c00440075204907049442d0100c40d48014131507504520a40b40314501c0440d05180c1842c400d10001429489a410301c4010711007800741e400c21810465008005840c0c03000c0b41e540d1034020780d180040404420803085807101010074680100d500408049019400034001c0c1118000c0707059020074215000c0c0c40e40d4221042488060804c1141c00d90100d000400100d07a2103c0304145440903500ba005038000d00d0804c84280c01001241c1c011400100300440161246140c0905c20300c03100d2043c00324200401209011b050303003440d00c0c40a411100c03030030b940046443d801481d14100182004030a1031000c100c1c41000040c001d8400540100c00820320850401604640d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 413035890 1250 413034640 413034653
    0x70807060809030d06120215030c0d02071502040608091908031f21031103030f070819110301170f070501030b0a120f0b0a0903050306012a0516060801030f 68
    0x3500600d0a80802c22403080115013500420b00504810300c0e8428401c6524410001244500d100343c070111801402004488030721842034828107941c1c540c01503510000b603d848658080d80803003c0400510124010600f40d80c856995841a00e03c80101e844074056541c403080307400b050007001045c0d42010000100765080038022070110980d00014803008076118a500d07000e52108465203401100a604a0710074568800f0340c034000d0b50000d001071495420000b169150b42640100410140301060700407900402000c002007940208010b0204030000c081c02d81d29020b5442845010030a44901100320500000407402c0000401010001e0151514140040d0b01400c4000310b401d0740b149500d41d00180000000800c02d4201c0d01c5254580c829402c00c2c41c15103040c840c00741010310010702d0701c2051400260020101c0740c0110007400c05401038180325110340400c1580344401c60045c0541c62100081000014400c288903070710582440c803a0b0f03190b20342141c03800c0342440050300ea0141642c810010801 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 413037140 1250 413035890 413035907
    0x411031b07021f110607020d030b01030b0307050d1e03021e0312011403100203011e15050f18120d08070e0901030b0903160305090405060409030c02040b13140f010807080706 76
    0xa0f07600304034503103050704022141440c0084488401680000d010840007a50606c00d0f08072400c0c0900301007007158030b410007207603542001c0d00485004c1d0340d2001d900002d21004401c55aa45800401030b900105641e107402500c80714040d80110721005162008c0e810050003100381e5001c5002c0c02c2001c00c55a292000103400843e0a02040b609070160842082c0d40d902c8030700042d0f01900c01220540c074481120891400100c1d0750750321020100c4078400c0080c0c3c0e261361000407500e84a03050300d204e603144c18141010760244500da164035a480b007051022900143e4021500c1c000030350042d2601151030b624202e00b40e42d014031105ca540c0c0d000c880440184001014100c1282d00855090116800c2075150305072100e60280030102580802c1011401401c2e40c40c041c05401d620078029601030001d0740b42c03603602034075440801c40000d2040ea218044546542c4440c080c105000359144020300210b0403010140d08040c50668190300501a048004518914001a85001c4885403002010000d103051030031541c80c42c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 413038390 1250 413037140 413037199
    0x9020f0906150d0b1c150f0b040f051905132a0803031807050604030204020a0311041e080f030a0f090509040b01090b0a062a020411031b0702 62
    0x40380354450b066003400031009030407807219032000098035804820030001ca5540b1440c4030300002503580041c0000912051400c800c0d040f10180c041340720010380042c1c00c0039102d03440245400929107800d00c1081c15040e0407076802801c0f1600728444070200141c0c00d4003038500403240d9050b091011503103107000480031111070201b401800c282001388490655070f6002041703290301400c85a0300100c18080045500c84e2403901510041c0000d0008902d480040f030501d000c2c511000e44510350201b41200c1003402600f20740101401501040c0d07846813100300d801010400c50000b40c181901c17840020a80e0740000490501702001240254103080940c45c0443e180781a80f8411010000c140e040010241c0342c400100b4006c902c02e054120096041039070b000c0490340c40080136480b50590400800c10789401400540000500c0480c10895030644003a42400041d0200001e402c00d2501e4031414500c210340d07019500980603c0c0703060246156035031007441240590305001c1d511621200780c421702040307008443c00000c0d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 413039640 1250 413038390 413038399
    0x22051e153604060207051209011d06120702070911070b01090b0613081f05040312022505070e10180510170f1207080403060e03040f0303020102090901050409020f0906 73
    0x121004000c2100c0544140c0c1e0031283c0700d4000c01c5400401806102c1c00c0515160b20420034181f20f0b8400009140b841d2103601a4403001a41c1d20b95843e548501c01101c6140440f031088000605040500a566011511807001b255181410305107400340b90004031002c55400c012458616404c050f8000d0060014441055115504001c280104204416100010140d420160400810b002e0319100c0030000e00751802c1c0340618080402000a80049901041010103000181c5400c0165006c21074100015000b0840e82e110030b9811041200004440381a900300c3c02c000061510b0b82d05000c6202010b60080301410810401c03402441c1c010b981c04030340c1c0402d110450707281e611381d82d14044150b040014070032031064205441c0c03800e032010100180d204c0025517407000b514040c09070316030340c0c00d41c051400000c0c07205480b003007952007400040059902071308049403c0700e0465942d03c0c004e4000c1d48107980e014045c00d00540001803600d4a4414260a990080c00c2618540e01c220100407400e0300060819078070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 413040890 1250 413039640 413039719
    0xc05031503030c0609011401051815121516030606080a0f060302060304080d0506150702010c05070807060512060102070f09020304020409081c1a0102070522051e15 72
    0x504404c100c0c0e203010340c800c100005894100e40d0703c018048030058020354010b21140032001e5aa0300800d803019804180e80c43d041d446041500d001031010343c0c1c90b66030403d891046140440d41c1218500388d180c010052046045510200c140050f416241c1a12542c00821000381c00500c03140103076084071241c3c4841600000700d254480e1300003942138000b501d0550300d1340c2c80814500d46405d0f03d41f040923000031007150300300300518030f0040b00640d07807099100003410800c94103c0d0700b007085410010b41020340b2505094500058549000170002d4201002c0c2c041440c0c081000f00c0c010b54008560301c426280c142141191a505110b9110041d600140c13007260460341d180c0007840030400d5107001d400d480c0701ca98030000080791400c00b03140603141c244c01010f0010051b40c00d00304190fa00021890216442514003150035100d40e0124604001c0450302d41d0304103400d00302000007444002401c04e420b920580894681c070340b5001c120121581c000e50900d50061145c020300072254180880e50700a1805104c001c0d800b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 413042140 1250 413040890 413040907
    0xf021203070b07030218010207050604210203060702010203040c0609150f020309220c1b12020723280e0a02071b0311060705070605250506190c0503150303 68
    0x402e00c03011a0a000003070303070102e401c1500c404282c1c1d0703100100200348020500b840c00d1200242103403080b03200d0409038401402c83ca105161800002c0343c40c964004050314000c1c075006801034080e6001b200c080f10302468210004ca4458007a820300025a40c070f545104c00580d40280055079008648660302c819888240100030103a50f4547e1007400510403109100780b1411080d10a070241c0b0402c80d006401e001801c042e40ea010800e420540c0e0507030b60840144002500c45180c142d0508005c0e070040c2d40126501e43d00311036404002d2814081002080e101f007100c94900380200307032002c1c1071079442035020034000504012402443c0a1103411101d591001464110740390713290102c49000c0c1c6212062480301010800c240f10004040c60552101030386c0c45841c22101d6654151111058010071003401004a0161003840389203508000d15010401078100460f40745c141070740d40c1c050894410580309010340ca48040c00c40d00303020fa0507480c000782c0c441608503120b0400d03000300000741d4542079400d88001e014689 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 413043390 1250 413042140 413042153
    0x7080f0d06080d1106013809150408070608190504050f0a0b0a0b040204060906050708091c060b03161403100501060527060d0f1103010605090102060901090f02120307 73
    0x80c801070041d11003000a0480c0c40401d802c20350141d100c14003480d0207040070360702c0c1c00704403101f104600d48071183c105403a00e840710022a40d000700d02d415a0444902d5001a07564130f980760042c401d480f844411990360316a00c180c12141103404070382d400c00d901d5501d400025040110b42103560807074450f0058a00980707400e14024a8070801c000d0580300101500140816400144101084131105035820343c60a42411006030440034107104480403c0340c00120602404041ca00381c038803c2074020b00e100c121041c2080306110845070040240c035078615080071020f0f1440c0000da0428100460800030040320314080050002081200203103405025000c1c2c20f000310349051055038040c01440d110142c5403811000c040c140f03c1d1603052007860b800241d80d5541041d40c0d4a90a803070070790104103004540150314540311805020480c41e00c0c811903002000104006411030082d01340100f00707908483c096521200400d00303036001c40c10003420202e03c40b042c3c1d1003d8200170074920301c0300080d4812285002480d950b884c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 413044640 1250 413043390 413043403
    0x1210605100c02130507020606090702121305090708010501080c0a0c170705060708270307050d050408010c03050103020a05010e0607050706030b10030e100b0d0c030501060905090307080f0d0608 85
    0x1003002902c0c60a00e941103240841d8554103015119104100a107451040070307540d001e01506e141d1150b40c1d180d000504042c802c001c0c0d60024142404016140c1482d8007414411075404d00943c1d210751405000514090303c5100094100c840580d41c0d4011501d5007036030310045a0001300e28070101300211000d000403d12499080010b0f1401541c0c1d0b0b40c0d9041582046414840060107400400140a0502c1242c01e6807110140a41220078841410f450600c0c509078074603c41c0703880c028414001ca40d1a1110160001c000d070007183d605a00a102401d8501c0d000c80171242c0900000350b01034908802440700394854110035001c0b00380038112518061141e01c03000e103041d04c00d50216000940f25481c00d0410705088034955032602c51400c082c0840070342c0802090300c4115901913030041c03560303070b0602c8409075840e802c41c0380c0321682020480d20819181c0c1055400f0b4034181c0191484c450a04020034222940081191a140d0300200921704150f410180800e860740321b441403a18042d03c0e0100410401d0051154 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 413045890 1250 413044640 413044669
    0x3020d08040915030803162001091101030c050d02090102031b010e01110a1d010905040f0e06010b0403020a14010e0406090c110304061b0204060b040e01030611070201210605 76
    0x41c0e01c4500d401c80c0d18060718010f82c00141c03105803e110400003c1d4004040c1e80d082004d404c88500e079251a1007046075610003100d2418142c000242d07400031012010340c0820f45040c041c00324485904013803030040d8160f900c03983d030100014a040120441c02c000640c0901014403052040ea49089a203044041030f0500030300352401d0300e075500d401d8018405400d204105c000d102114401e8140105280701420100c0d00760000342c41c92440c40054021603118110718805094004c2040140461495400004004680c003100c46413240300c001164a180130010786003180d60060118401505022000403905003005405040c041e10a01020499441e4090580680755034003001030441110280207043d9600c900404034035030400c11043c45060ba02aa00d02030540d100200910220040c3c404a802400b188d0702c8244030b40e80104010612000b200c10041c100d0b8050b540034018038041070103402c80340c420180c000740030034596030034000041f0103201c00741c808880325800001c01c20b50f20000b2034803c4091941 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 413047140 1250 413045890 413045903
    0x150e0a0516301a0c04050405010b0408120d0605100c110d0b060607110a030c080708060f130206131e090212010e04152d0b0a03020103110403020d 64
    0x30044464031401d030810000c103070381e1000b005140000400301e004290300e4004078000391542d06444061184292901c1c5036003895440d0000076240c490f0300300c00103400c0307401140c0c4110304010000640c4030b030000540d420703503500d400a4415110440901c1c0a1644400105039400b1b1300c0d01000175255031040b614405000d41521030421240030b51a09111250694016500c240450501074010984201e901c86e0321080130b60342c0950750045800c1648051000c4402c0950107200c00702d0100030480040c01500454460030111651151251507041e02c62108413000784403c0031a10010303000f28903056400c10140c0c00940f840745842070540307105010400d6504140d810004101a0b188a0401104c0d00c0c3c00500041c0c6c8110305010303580541d4a000401071190041d41841880400d0500c00315180302d84001d005090104040c94081c100c61071589480d661180c0c919a480c2201404a4218041c0c07000c1614000c006e1603899086900540081c91003000c19440198207000220051709d81040385d0321518082c16 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 413048390 1250 413047140 413047153
    0x1e0315180a03081504050411010311070c18110c0303040605060a03050f010b12070f0b0708040b040f030b0606160f0c090c050403170c03040303030e12031e09010513150e0a05 76
    0x4040c02d0144c4000c1107842d026a00c1c1004000114038100c01c21040d5003800d203030100e200000306a0685150040d6800074140b20031000c0005001d2600042c2410980c41c09031040c09003102422002d80c0c54040e042e10071103030b90008c00000d00040d40320742c0401d9000000601d401c40a51312500c0e42403a050011050000c070b695913243d4103c8a190102c5210401817040c4014101981031528001c5102c50030700c0f41000c4500302040b46001c11200d9015280a00104624583c8440c2c1d200c0c05604200030521080c1ca04c045000080340080c2011400c032004881c2c000a641c800341004d03610038007480c040010580e141d41041c080890808414020520400d50340d079150342d00d0710f055040020544102e03026806042c0820040300300d410001005907811244c05040014150303a4500c5500c1c1410400300030381210000020800505015941d074a42c000c1c41c0d45004180e2995903603400c035007201e100303139402041900424010b10000320035065405c880b80e03414a010407110b924184092034a0b40c4828121007075080352 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 413049640 1250 413048390 413048401
    0x15020336060f0c0703120f090c181506050901020115270501030507060f030209030139051801050904090506090d0503060a060e1f0302091e0315180a0308 67
    0x10018140c01442800b07040c070079800c102e01c0e5692030388a1014014140300800720b0030245d681069100701c00c800c010441c00c0c0700c4000d07140b80c030079104034042c09035030442c00c0400408401030881e44100d1a400e910b500340d2141241c2880420307a80f507005403e00768115921222800c400e094280c004100416010040d80c1c408000000048060444050761001803880d04004001042001400204039891410820300b1031480c0c0c0301c218040d125240b0041c1e01034ac2058a1005400351100325a00c0b110049030900d01301204035940387d08010702410850001420901102d9002240c0f1543c5818078030050402030302e4103130007001190580e25840c000751a1a0400002c1180d06141400400c1d9913030558940545103140c03003000106009400e000320743c20002411a107503120b440300b02e16582e05400c80200b184148524110040280d4041041c46002d0340c0710f4140700d41040301812081030b19210040207050030317040f140b4101c01c2c00c1d01c00034502540050f410364180c40e090414024290700758003e50794000d240c5040c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 413050890 1250 413049640 413049643
    0x602010b03030906031618080c01260a0c0908070e040b07050403031b1401150305070f030c030f2d020f1f0804031107080307060c02070315020336 64
    0x21444a020b50001c000890543e40d030902140d502c5036900907903c541420060080310000140242c100418007a0540810b540707200081c14611980d00366111403240050b850081035401d005c182c0400b10700203a2000c14001041d0f41c204102900007860300c0007185d550358100c14034240e201c0d84a50001d020400c00e12081c4400001180c0d8008200d081440ca014550350b00285019040c00d1449516500800600100b114002e10307074801d4801c0320000d10500090300c040015481e59403004440b103201c0c0c8200000c4600c651907502c0200c0e90800500c1d9250b070710b1603d50901c0b801c040103040b9603160300212044540200d0024080c01c00c3c903c07803503280c89946184140800b440c556480d02e403160381400aa090a41d42c2c110302480f6454641c50943c013070b500c0d2440d040e10410040010700c101805407400200740c428000028004450103420280485010428180e032250030038000a8010078510442c15807084940d00119003144144000c44c8411078941c08012080741c15190840d00d0411030801c98245560 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 413052140 1250 413050890 413050901
    0x7030503060a0512070306050c0d0f05090c240f090901030803100902090d080a020a24050a050106021905100c0801080606010206061c24061706041a04110415060201 72
    0x2500c002d482d0580580c22603035200c805c1c1c44018075003034031440040c50202e28213080e906201c442d00d80030300c442c01c200700340c00d03014040482d1003180a1241c4025803045142c0b03503240309070708d55012404005c40010382d00c0b0111640c0c0441800368180c8000c00401600c0d03214594010b000718011400f95403241040030000c807480101d94420080940144485604e654490b00b0510143c0c1d84000c0c0580d8a03d0015810f03803c043c1c034650003815040070045007803c21003610740160b00e24240b1900c01c00182c2d64190300340088510070300500c0010382c4154200255803800c41481d5071842d00610446100c604008454415980c242c00840300166203000104191700e0200301c41c1d90055003d002515243c60004040b981d815985284104070780b884910340014041c03151004100084c0f5046030980e0116000c20450160940b1300c40c0e19422000c0c0306060043c00c001051392400346600c2450303464010340407411803c42c540c3c0604180c80310341c1c3e41241340419603200e105c0e001d084440b0103910325500d4070f001000781c219003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 413053390 1250 413052140 413052149
    0x1c0309081b06010612060b090f0d0203060a1b09080706050c0a0c09060311010c051b0402070b01030b0411010903050c01030c0504080313091116020613080321010605041d071407030503060a 82
    0x24180320052055007c4102510400c000544120750100102800610f100000090180d0140503100601540201c20780010101103070074212162403000c00c60040f20341d02564411644650801881030113003910400051043d02508821211815520340718903800306102c1c1c0c4401c046642d01d100400800400a141800c9500c0034280030051a25585800b0340301d4030074500555001c0f0b03d40a0032880366030307107606070b6185a030880381c150159030b1245810485240c05860981d90794050485540456200e000c00b00150fa500c80c0281107126400030066010b081a09500340031721406001c04074201c030b0100080e040ca5020f2070b1040c1080c40c940711411040701c03610010f1020b00c150803c29480400000c0d00300e5002c45030b06680003950b85802e07d407800c80402045d081541940800035220500b11042c021040e61b0040420002d0f141e42da85007001c2d126407055214944011034040c40381d07014034003022f04050f0701564070700300501d00490134528621141d0000d0380c124003280c400f100340034203800c26481200c00390 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 413054640 1250 413053390 413053427
    0x17090d02101e0c14161127130b070f09140616050a0605130c05030109150218060307030c0206060603010f0b0c12040914091c0309081b060106 62
    0x101202d00d003020081d05885005041c2c40d4982184040151003840c16120301240401d19075140e844429080349100c01810b41901d40b82c5c3d01d0080e02e1110300c3c0c01140e080b03980f00400480c0001009010410100102c0100b100344c81110040240c000724100300c407402e01c00c1c0150b84c6e81402000d00341034040c05141c01501300c3c2e0214030b200f041e14041074403800115007112446ca0103401010078185841854450322400081455003408103110250040c03817014403009100740f580c4084151541c0c1030500f03d40491070003504015003400043c1d03110070558014800c4010383c182c1040118603020204a065000b9036800d40025035a8052070060303581403280c42e8000100b16086891945001c841003000820750045410141c400240380f00341100800102d40780505001200b40c8860f07903122176200600c03441c10892030380c4110100040e440b04001c0b8684424542c000321250351080404030850040032600d1048802903803c01040710118070480c0b49000d0151020001e080a60402e41700078888a540b01d180c00e441d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 413055890 1250 413054640 413054651
    0xf02040906022701020c010c02031c05031b0304050303040f020d0204060b0a02011401030b0a0c02030c0a1505070314040605060f03030304050c12070803030c0d0209211603020303031617090d0210 85
    0x10303a070104034801d06c140c007480e00d54545800ca000003030502101c2d02c0c40590022645190440d540e81080c003842c41910b030810902c1b00e11414000781c0c07603680b0048034014080d0f00b04000140c009020030840d40d00460018000364010044daa000c58200c1d903c681081031044c402152581c0c1d40d0341e090180c00c01a2100303a0880c4c000b075146540316506100301501505520f13465000702c1980c58808c000355840101c54400701c2c0d8034011039040c80c510f1216a5101c1800e55420803001414441c001d01448900141305643d48840c1d96075611414000c0c807014002d1540024001d20900e0b0740e42d800c02c055405180940d02400c00c030720121040050b48600ca010308c1c582504004400c05c440780b404000d90368031a00310308001c0d40d100160b42034074009116801e0740c0b50b80004c540c810109c0326250104c2c40034140100d1422507808400d150b845000c0c1a1403440001e505038010400209104049030800810800ca4100034001e0300c0b00d200034410051007110f07a4405030b80310024405001d03604001c4071301e10285089007040f1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 413057140 1250 413055890 413055967
    0x50604180f02130b0d0f06050c19030c090906090203091b060f13030b07030f0e03042d09090b041109040c060c03090801020310050f0612040f0f0204090602 68
    0x1d01000c1c018019110f14190010600748a4958100c0c2d0104030000b00440758000c0140303070240300d100d10508292902864000010500c1c85448101d074004210080c0d2812842c51080045001d8010824440c080114080d000a070101d01e40c010707a0054405000f0168407454120015444e0503d02c46880c404121404814007298a03900c0c02c80d081d0130b00942855a4807011610000d40b000070591000b402a912642081000ba900d984840c40391175078140180840502d4425040e580c0c001c60064820755441c040c00d1042c00f10226401131a080f001400104500340d0307510a05017119007108003a50f2425121040008116203500585040c890444182e82c103400d09840b01200c0034054020103050003800e81c1c0060606000324809401024207000035560b0b4a800c442426000750f0a201c2d50707009411320680300301036207040e0050341c902c81c440d240207181981c3c4585442704c0d4001000f1082c2e40c1034940da0300e0400580c455002d01e1008602802c000342c1e071000e44600585401d0b007843c203846a8203020b10080c48 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 413058390 1250 413057140 413057153
    0x1b06020d14090919020403080f09010f0305010803162a0f09200a020118140c090903071e05011103010e0f0603100e100905070509130b0c030414010f05060418 69
    0xb50007000e4031070130350f040710080b40d0290000e10031600054582040420130560315015a07004003407121003a42c80140740101e2010035002c0da14207024a8120750424848007510707001c0e0b01d4001c517460f40181d0f851001580c81c071020b05110050308100c0741d0300d045800c5040c0103822288605500800024030200413540d0003520300440001100203101004400044c01d0214500c01d400001f001400350000c4001d5040e1481c0c082182072140e103844c0014000c41000040714500325155610a000c0c51004d14609180d03591080030240512a0351100882004a81004907000744134482841e0300070b40742950384e0750401c00e0b981c0c2640e0008104441003607910040001a03180826041655604031002140d00048000c40b44e0070303d40da00b501210214a810f2084013070000008112040310000c1d110381c0d003940c0703600c0c5c060500c1e44180315019041c210000003044213200c40700300039580f090080e10360542c1da42e401c1d8102401c0d521901b0220481c191a0700501242d4034081c410604448281d80d01208400b100c2e54802 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 413059640 1250 413058390 413058409
    0x2e051906020303160e04021308010513020d1103010e03040618121a04020a170604060608010c020303072307081207020d0f0c02060405120a11030307020a121b06020d1409 74
    0x3c512030910f13a583c0601c16405014080e4804030000e100759205c01e41c45480f070790a24594403510344076600300303008a00340d44060a01444225000380c203a80306030a030f94649500d00750707d195045805650b24007030700d40015018409400680704d42d82d51200c0700c1c0501842e80711030b80883d800c2406216410303121680002d80c021600070b205500742e42001402c0c0c1d00ca00001d400b4001c940c1c40040c0c40709402603540003149000c24058882d5102d00001c001c281e4841c401503080352480e0486c2c2000d6030040001c181d0007070164400528022401c02030803039010715402400020f400072242160051804201c20b241c0c2c07140040b0181d4041c3d0188010945404100344c01440d0111340e0654070244002129100e0543d221b000403200031b014007514805403e0441c2910940e00e01848006a4000ba50750180c0f078118a0701104070380c01141c000f0040b0351a82d013007134481070299659020894000c040c0f0403030100042d242d1314192000300403d8000d02440340e40382801419030802c3c202c441c1c11000042061100307c0d40c074002031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 413060890 1250 413059640 413059651
    0x10060903030c150f060e151809100c3203180f010c081f12080c010f050106180812030a1d03340203070e2e051906020303 53
    0x44910600c0c1c5041811100e1039a4495010f242d0800701602540401a040041210800601c8481c0daa540c42030a4410148502ca256404000041145c00001030f014140d50454264429214501e034a24000e104443d00380c860100070450340c1212402c0c6d00703081341c201e40c03003444002e510802441601e1012900d40c40000c00c002101c2140a00c001003199080140c00450b0312044003c21110455000241102d102244e000b96100d00c45801030200104113101207040f514101160103114a581e900c1c914540c1103880d080362550745e54000f0105800140c06207500905440c0c69983d01800120300c030022111050b0000402c0381d100c09204100c0b09107420460383e0020302d080300051102d00c4204010881d18000242603140d100104480c40b11044c0c41aa1a4604441081d1242c80301064072203840550600c1a01079496008100b04001e0704002c20846507029002c03464081d040d403024202e0340d118403243c0f000c88250a05511003440702e4203080c0d0041140c0d10745809086680340c40c000000b50b50f48801001c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 413062140 1250 413060890 413060897
    0x60c020c0d061a0303040801021213050a06091a040b0f010506090a031205040e01080714040e0619060510030f0b030a05060415090602030a15090612110f03150f1006090303 75
    0x91403220b083c0b0b1040c0400c3e00d20090030f03aa950355403040014041e405c81d040001c40d8518000c00300c0d000d104510043d0340300301d51040191900c4585512100e0040c440030b241994101c5001000990301a81050340d0b501c124810890700c0482c1c00c0500440000850503001f4500580040011000d02e0342d48540200c200c81d8010500030300c014580c0401c580b240600d034007108000c2c080d1400420091004641d403000c2c1d40f0b2108a0594224020042000742c8030000390f00e030100d40042020609801034154101901c8404003004203080c0d07034810210b0402c84510403d48000303a502c1c02c45840c1507010740204405403c00300c0c020504001c0d107403213181d100c0c0005080180140080b120340381c02c01f82c460700949001d980004045407031f4500045400c0160940b4010000c01d041c540d000844e84004500c201300c180c415402c0c005200d40c070306d6526031071458181c154499100c20030319400e040a64041045182c4c1500f4403c04450b03c0c1084090481c00c01805003c3d40703681c0645200c14022182c0c0021a441102d80500e0b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 413063390 1250 413062140 413062151
    0x150a1d01271104020705030c0d05071703060a0807090c12140105011101230f0603010e12090d0b330913230304170105010b1e1c09060c020c0d06 63
    0x501200b070342c0051518281c000f40045150024030a020000c0e1415010f44c6080e50416818644101d0b903d2060490040403280c0c2400c00383c1c44660890080c5501040140045400c02e4460344c1203481c0a1080d40103880c000d85030414080040c0d40080010f5440301a00c000f030001407590603420214503c140111410004a61101954040c00b50020140c0648104444100d280740d003008401c4540304540300c03010345d40e044c40415064241440352044001440010302011307041071088000319031101c0e00c4643d000c02d1094003c0f0100e030b1307441c010718001e4403003107040e0102e400881d840c500605134a02411340d000d0400003800500791180304469500103800342180080c1802460003480c503040310000300300000850b2000d800c50000010050082c0c0f41c1c0c80038920640400c04c123690f420384000340030351020301c90140b0078440c800356208802c00a0603102003a00303080c0b59508402188100352414580e0641d5210101030082c0411446213000c0842c880c0302500c410204000400c018505900000b00003d031b40d103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 413064640 1250 413063390 413063393
    0xf0708040f03150606080f0103030813050105100501021207080909070306080307030c030318032307120203030a0b09060108060d0507090204030602070507050d030807030e150a1d0127 80
    0x41150050701950242020940e164104482c821480607071600005180020103c0c216001d02180340c403522071088025916030035550115001036014200d00100303040e120105000820031b001d007030300c9035000f00c003812402460b2000091500c50140c072484d09042c01042a07c000c50342050496840801c01c1da00301c0b003207032103c41d41100200820392004e001030101154420070180d00c50406914903010b9074043c420900031583c0b00c80c001e207240c1c00082c0401e000c5040301c0b060b580a00b4102e1613803040c0a59040c01c0c00360544500400f1042c8001071801a0000406c0004505880c452100e1041c401c4d036489003149000c00002c0c2103000e011340054400c0e50703504c60000401c1010020740c40a0924500c0954440d039880c94118041d411402044816000b51440407070300303003002e100003803c5907050741c0d5040b0300d0385a94000390020060000150f000c1d00400d001c5140c5088010701c501d00a41d040403001030052480c480300c58045071a05005a06a4101600030360003590f0002d5209001c000d40c901c009600350903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 413065890 1250 413064640 413064653
    0x5030402150a09120501020d0b06040803040303031e0e0a15050103031b020f1c0b0f3c070c021807200c0a030c1502010209091512070b0a030612080f07 66
    0x56126440a84c024018441040819006802034006110040c0a4516200104081801180103242c007a0780180401c1004c03038071a4000d8485203c4003d0741209900700c00200304152030f0007003024000d41d88260307455070801a0804241c1c40340440603804124550450341d008022000201041083c1d05480340410f00703640c0c1c2c1c20f51355078018a000305032030b582503070840300d179008001c49003c01d030781440b040c1d0000303120880040745244c40360006442c0702544900b61381007500c0e07a40c802c5105442204000d040c82c4460440542410f0044034203403541491703010988100040c1041d50312030091900c0d010010300c1407043e00400718205c6c0406031101580489001500c0c18600513110303c030305500c5115040e0002c1405120040f040079607020443c0d0080111083c0c1007070b070a0b841401c0b0010f41256501c0009444011201c681c850701c100020001d000382c010340942507140c81e00c1074120350070301d41001400200064051060600030101c1d441400a41c1401e52244601c5003c1c8202c0c503440608000303a10000c2045 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 413067140 1250 413065890 413065907
    0x2009010507020130050106090609050a1203050d02070f061802090f0a0e0616020708070b03040308041712090706090605040315060e1303020c040b0f04110c0d0e09010605030402150a 79
    0x400c590010316425400f130a5601a00083c0720307010100c2c07034000380424142c3c03091041c070065400142003502c1c1e0300c3c43c00a50020f086003180c5c080c1c0c100300081c411a103418200b4001405800c0c020b1a80d00305d140680d092110882e41461516480200013000120041e04c0d500441c80c3d00c01490300311845141d0316030030100d025000c40c42441d240b41c00341c18108810a1044c41032940010320719402c0300d41c11a12405040d54a0718540504030040200f80000b400003885152541d50191285d01180d0210560181a030003a81007000c510300b10765030038420400103000c10400040280450720380404a1031802401500c113229074003002c1d2040c060202c50440650700d1745c0042000303180c040f0044075149405d500001070003600324070880c014000c800e08201146003d0040313410000000b4507000031000c00004000007000600510030ba800e8003404442002d140512250200601076140c2d200070300078a80401c800c80c101600850180f0100740148405611411103d01c800d09049050a980d080341c00000e880f002d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 413068390 1250 413067140 413067197
    0x1306090303110a0c1101050f18061204030522050a050d050a0507181b121a1302040f0f060c030518030604030504090e010b0f01051e07050120090105070201 68
    0x10005500f000e00340e008440c10036a40c0078881401e00c06079101c00450b114070a4860f5001410301c20300c02007449001c01119090705003401003c542c50050628403684034404202c9099003c106d000c41c0421207a621061071500c002d038000c4a03100d10a0030a00007134003d42103400764038015110611203100b042010000208815040011030701c10300e0751680307a10362090b00100031924050a208241c040298428102c6100050944600d03d4054a1220142c010600d446d0034640c254581086042107454408120070030210007800540c0c2d403420a0b0f6040c3c01c266041d4030103a00d011110200700007485d03022540190705680341c07904640e20094145903140e800d01c6110b204c0c4d40345c0910410b0102b00340e00000244200c0b61800300500c29034000c003840310308844201042a800900c40480d1101030b40c400e00c014007480013a800484d5000c241400c5000c4507410044003200c1d1a95142840c001820840203c40710085180b0202132074100e048000a12030300484c0c000905000100c2d0509418069051a894446 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 413069640 1250 413068390 413068421
    0x16030908041401110d0e0d0303090605010905011508010b070201051308010f0504110d150c020708010e010f0e03070c030605060f041b030b030f030301140607021804020f04051306090303 81
    0x7640c992804405941020302218045403210080c40d104041c00b1071601c001100585404a1001800083c003076000e00c0c008084040540d070301024800a002c900c10a0701a0810341070015040d8141429003501414001d035540c248130300d03880100000d010300c404860000d40d084c1713801c54070342000300580031901030030f17402a004075424000000300100640d0300052040b03004100110b46281410180f14841d8200000a41140a03004038115605804c2d0020b25012265104a40d030503503541190b80e08407010030382c5544160b51504000302500d207207030147c05254004880030f076241449941c0d070316000106510000b44030949030400143c0c0c82d9a10403040b17181ea90060400c1c01008940d08621000550309000400803034038003010081541000203260072006056002146964280000c4403c0810404e100c00d50290302009404010f0700c42c810004211051400f04000c1818144100001102082e42e01400344d46040301700b140c9490101c820f00c0d01140c02c1000000c0d580d61740c0c20704402502170009400d802 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 413070890 1250 413069640 413069647
    0xc07021c06090c09090201020606010311130e041a101505040b071110080112020d050703021207060809031303200a080a02041839060302030118090b16030908 69
    0x207001c1e00b908145282da108040301070342c0c96280c04100d0700700d41c00c2c114040e00681c000000941594040d5000c3d504000010040c6130800208083d241400e48039904012140c061450a210030062007036330010481188411120084c90450600d192014091185000c42240681600002401030003241d01800c284081c00399601c00d50b05080d0713903180c45a40400e000b003c151080c40d80443c41600854141c03120010802a4600240c0812030b1182c103240043e20203009503240080103a032003120703900c640060312000d40001e40c649500a0305080d030040250078641c00401c4540e850800038603601d1706480e0f02141e0121400c880b002d500b82c90705101d16086810003402200800c00b40d00004072044060f01c00c0f034042c4003020070b00005000207044100001c0c000801c10418031901414085108540355040c1c00c8003102360841c00c24050504c00710380c80800841d50020041c040c90440c0c02050401150491050000c500182e80d103201c00c000003480a44045040c21030b0a0740148030b6007100020a80001c0078984 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 413072140 1250 413070890 413070893
    0x110a1e09030813170109030e0d060204080d0f0815010e0904030203130320010903020a0905041410060e1f1412100506010305011208090f0f0301050a090b070201060e0c07021c 76
    0xc501d5024000c032000e201c80045070b00078132081401450041079041e541c40855043c91410712202c050f4018007251166001c3c400030030b0b007030800c019000c0d4035100c44e901e005206910b4a0060207580d00644814982000006004903a9800400508201d201a14070303041d80ea0756420100c1c15401041d585401c039022010001080c0030190416a1100718074811075035148144000540d85c0380d14621000b03410040c0b0030000c002000d001ea004036400341c06600769000c0003c601c0c85440c10803604c0c110780c01c0342ca1b945071020b05c101c3c284020f40903441012030250b000b10840210070510101050300c1903049207508200c1c4014039881d21801d0380000d46410003211481c5003500c0841d030150008483d0783d40001c2c5420000180031040340b00341095150003003947c2d072400031090305001e0710240f0014031542211041d510000c407a2802d200d030900c01c0402c070078001842400e91400c1030140f000501484116030403c2003c1c0029081009a40d030414027030203680ea6680306902c04510307034002140101c0c0700f0750fa65121120 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 413073390 1250 413072140 413072167
    0x13260403060c11010f0c08061002030909010e09011103040302150a0b0d0b0411090c0a0c0c0e19200909040f02040207031e0203120705031801050705040603110a1e090308 74
    0x41607981e0f064000e000c8840000c500d50101d5a41204590004902030041205420013a92403c1220510b2050380e140030b4801010501035802a400810007444150400c05401820320030306440600c004001441d504058034002d50369400c240d42c1c90718500d81c04005c1181402a544501c4620794040e100c60445105800d101a2000342124241d981550728401d501a5180194900b1711400e00c5c034610703074105441e080e02264086100402100e1740016a4001f26440300b0300010300d0b1280210110403480e101c01a40d1500c192488822100d403801c0c41c5407140301c0e0303403101c0d0300a60b01469400d9031a21215601c504025102ca0702122003c0d420030701c0000e15006266212191000c103190404295004408240040344d484c8240240d80305400d56050102e65103610800007940c10000c6252606500c10301140402c0c00c40b0070945040e0045100001c0070411207405028402d01854402e0b0362a08181000c60040d0940018541240b1072041001b40e1164060240202001868012040c65207801c18151a81c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 413074640 1250 413073390 413073407
    0x60a0f230a03030801030f05031c0603031b030828020316081503100c03090204150f0f050d0201080c1201080c0109240f02010f0e060f13260403060c 65
    0x440c1a1540c01000300000d041c102000c00c1240c0d49540d840009a203941c035000c2d6402c0c0c60810444150104124120b40443e02c40d00601518120300c6000420614500d00034001c4100c0b08003580c00b028402403081c0100381c021903415448550b1090b900c0c910700d00180c40c01d0382d01d01d0262440764581d1000c000d014142c601090f4801460100b03480c2e422098485894000818207210300160b8158002c0301550040b40c80d43d0060446502c07141070214541000c0d0380000c0130740e2032440c54141450f1440004000b007a01c02008032000784042c0d54110180d50605000c07420049102c40080c0c184803021003c00d8114001300b00311000c440d4402001c03070107940c540f07112f07036101c81a04800341d001441b101c9010403c220030350a0307000b40c002d1105084d4001d240d581c0c01983c00040380d4441e0001e6540e5a04145040300140c00340726880d501404c00350030140750504880808080240507400951b060040603800101814080c0c2c40150001c07484600300c2d02c8080071040729100726080200341c1b5040c03180d032016498000240c3d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 413075890 1250 413074640 413074679
    0xf090e070503030408060a09060e0a03080f16090314150f0103050709110d1d030a02010509010c050703080f06061b0a021e0109030f0f050304080a060606090609050108060a0f 76
    0x35645055551410141d49000d00c0c05028225003000010605441c515030280345c3c0c01d44602c0f804a1500800c1c1c00190038000b208400341c02088034841041408400440e1056000901c0c080c4408041107d0303070003d12070049400000c3c075403071891241500e20707003080020f860340c0d1070302400d22001c0303141503000d4145911003884101c0b03161181e00c50200e4400c11500603040305e4034100720001e0511000c0b144590282082d00007648500e24000ca06031544103050005140a95180d00082018144542032900311036040e901c240400106000320b1000981c45200290400041d1000184680311940003842c14811442c1b0400801c1d080c0d030742c400c0080d001280c4500f42c280202c0d50300c41000d1080c200999032000c10320071580010603010052000404031030148495501544038043c00305c40d681d907a41e280d940940c21040482d0b0000c600078040200034001c22014240320f1078200e8043d4070f03190001e080469036005585c14401a00c0000e01c0c1c5444060092000f44507090380d0002a50703681c0300c9041d905100303001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 413077140 1250 413075890 413075893
    0x2b090f05010e0601030201050d051306290d0309230d0b160c1106160203070321030213060509011e031e0e0606040b0307090c0917010b0f060a02070f090e 67
    0x41d2005560300810f65504076601030311041d2500200680180c02000001c1c941703c0803407100b82000d400b06900d8030402510303000e0007110714070b44100008180200c3d8200c850b41c51081f208920121700203a40000d80b03100b116201000005100c42050640200441d404002c940002c52100500b003800f0140c00c5440c00b550940c800c030800c12244990454410400341d07005052402d0414422945040c1003005040410003c85401c0d640303103860740001c0c144122a8011303109601400281c81e5150b0341c90703082c4000203c6c10300382145000e4030400c40c611180300510981040c072801007185001a40030701c100d483c1e5010481d141281c42c85000c0d40141c02804030304041a10082801c50b0f0480b160150310400e0362443d54040180140d44d03a90b01000090081e13002800e4040c001c01e80d000500c1d806600810001048a031a5400401c0c1410550301002050700c031800d0044c0c1c180200419182c0300c0300c090060226050f200c2d5075645220b210140d14203861544454901100310340001081444c0d980200040f0383d0f0b410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 413078390 1250 413077140 413077151
    0x110a0b070e09090a02010e0f040908040602010e06090c04110d09121103041a0f040305060709030218240301150608150406031212060308031521032b090f0501 69
    0xd00b4818051000c07100c034502070307000c015030f0409503024618500132060010001064081203c0216064401d0044201e0f0030a401103400e0240980a004204c1080c1c04d9800809552800f030315941c0e60b6060a501c40c9000d55a83c4802651080e40101203c0000451307020900c421040752400765504144104084001840041422407818022044804984810740c81c003001402c1408424904d60101c0c0402003072000800c0000300040307081c402144151050745a54401500e5070040c0640c0c1c0d0b40d5105c502180700c1e440b80c108007104040c0e0711f914818081180e100300b4044081c00109004102011401c60f02521000e070015042d80e010031103034801c00b007006010741400d0624041c0400d840c06804000c0031203000640007012203204100c03071030120b01c48a0020070419920f46500400d0743c0240d800790302211403003403010320504011504000841d000680d4028000c0c0c000c4810742c4900641400003d8a8601000c00c080c2407000c155240000c8407440c020030000c0e0261800c48100341070540c08840550809 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 413079640 1250 413078390 413078417
    0x4200c071a0708030c070f080d06051c080703030e030412021309030f050304210f08091b04110904050c03060a15020d050f0d060314100b060f0901110a0b07 68
    0x21050200c60068280340e0360308041050f0b40310101600020f1404203400010f00440300401c00c0c403005010443e0059000079641e140c0201b01030280d074101e07044907001d0078811054400c29201c103520080d5030b07a04044541c0c0c6422003450100d000c0c3c016052114601d02c8003040218a0400070000564824030840700020b4680c511010f040039030b041c0c4140940030601f501c0003070301072501030b0000b994840d100702d050480780d0840d140f908410984142400001a011405400340b1030340bc9545130703400c0040700e4014184034890b6078915046110595406004036103034404964901d0b0074005036480c0804c000c100344080e1420400499041d0012600b2601c1101c060100003140c1400301c1c0701c031860100303540c09024034282e0440700355001e50080e542c95200040800442c0002d04651007140050b40c81040d121140c4507109881615242a1942020120340740280c10313605031f500c0108540f070440507541c243c1d4031840e0000c01668280602c0e100f042c4580100302d08401007140c000c42030b910403141c5450b501c0404245 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 413080890 1250 413079640 413079659
    0x1b02060903030601080405070b0706050a2403020f0406050a09020702041b0806092509060e010e060d0b03160b0a0807081315020408030c070e130c09050604200c07 71
    0x1580c6a00e0a50000c0001c201c0c80d522030080385a0003401b0b4021103418aa4551201900e80e200e2041922079a0340d0300c0500001c80c045010354214050300c1e265600041102a14044c000303001840700900c110f86800812a02d625141c21000c000c01e001401c5003801540d030105003003c0d601c443d030101c0c0320741d1825500c1c600e14840c07114072441540043e034640c2081c1d40c0d2401841070091014020801035a202c0350941d40c1042040d0120b0803c0c24690b0301d42c0007803483d04102604c0b00f8110707100c4606010024049042c4c940315402660200d12121401003640220040441d040100d160f0316128040b824080204000368040f0040c1b001c0b00599442e2100c5a132030f590202d0301c02c81e0030750ba08440c11014400840210300e80302c801c450505104140149855581e0445a10f903070304c03940c150505900315400c20401e01e102c0c11003065119041485170030296110303549492104810b070143c1c501c41d07551034002c41d00300c0d212a44032140e890400205000000900e00ca05030315508030010603102c074410600c020070355114 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 413082140 1250 413080890 413080903
    0xc170301030f11190617060109141e1203120901090c0501080a14090f010608011803052209091101030912052203060504050d03090503090108060409151b02 68
    0x4002c03080c61202e46003903a0f0090982a41088141e0200c10720143d414a02a000407083c01002c140d241d01c81e07594004204500000c0004100ca41032060b079000c104024480300c3ca6017000490106c40e240c094030480821151800c20071200303e5004038840080700140345000005184910307811a68007401c0c0c2d980d480460036103c20580051003541c07040000c10245d402180c195400ca80c0650b07000c1030400c82074000894082040700c0c5034180350311404410740503a80a00c500000b07042ca0310001e10191180b000140e11502d4440001000c12000188142c1c0c801070190464807458074104030f446603036545840480285c101d561041d0b540001c001c0500410750301034441d9a0807540d001081c2d40c80c41004040a40d815045190030212150045841d0143c10132100002c0340a9441600009428142820000e14185d0320f4030881e401c0c1450070701c5c03200203c0d03400815580c45902c02d02e0f21841a988060104000d4944441c3c010500000c480410030340317121030381140da00e0601c640141024082072450403642c880 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 413083390 1250 413082140 413082143
    0x504090b01091e0e010b0f0d09060b03060408040611160b0a09030b090102070312021309020f1308010e0d020a0b0c03041a070e040b0f010e0603060604050d0c03030e090405100b03010b040603030c17030103 89
    0x2003140c48c024040341d41120a4140c0a502c00180400020b40400c0c01c1c5401120212413002000506118254202111541e4406044000c144611110320501c81c004258007400c881c000c400b2425080452040005602031980178010010906141d4040c40c040c0d084090100c01040c0354006020414040d8826210041098400c070b114251800814800039030121035118103902081000c02010001d249170000141522000040e040c100300c00c85900b000103980c000c2d011074002200d4000440c400c40071094221040f02c0358560349446074034041c80140004480d06940198400810000a405c049400c1c4d52102c1554140f01840100c4100006540310082c1c00c0d010070f81d2040c81d10240d080010203140e201c0740181c0400e00d415191030020b07601091002c4110746018401d002401050351000081051030400d0341c04112a0901d0b0780d860b0f0b104e005003441d403c10b0b20f1381c0b60800f0807260360035080170b5880f140203001006115140c7c01c008200c50000c007802d0303a0b91881e401e6944e001c035030040101c034102c0c0d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 413084640 1250 413083390 413083417
    0x804051c120b060c0d0207090e0304050105070b071205190f061208070c091118010203040b0d0903020c0a080709050c03060d02010804080f1204150c0504090b01091e0e010b 75
    0x1d011000c0e400001d1405000054000d0014003045407240d008000b0080c0c4800550010070a2a04d0080110203480c0741440340c400faa002131004100a036042425202d255500181481b1595194181100e03100700161030140d183d4281401d112a14075048040f1345803105165040c40400081803820050d00e010740300304aa55065610a10003255688002c0c00c0842d11440c0050812a0341d00941001c2d03070600d4641d690060301c001010050f0024030383d210305805100380003450809103420100801d034040d5146219080d9140d0b104401014400c0c4180343c0a804020400102241c451044507682c03c102d0003042d54403458040400d1040750044241c074841c000c014810710510405c0e40c0110390080300a0412914150306010174004d190407007010f0103a9401043d01e848062030f01e401e0001c03410040c444210740b81ea00d0100c8055480780c1c00340131201034a07014074020940c4802e040c01240c900c03805030311020f40588c00c0100b01c040740c52038090303c0301110388001d10240c29989405c0740841c00c2c8508078281551 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 413085890 1250 413084640 413084657
    0x903030a09060339020a140c0a09060b0d020705011b031b02060408090625060c080c030f010e1308030c0405123415020a151107060e1207030804051c 65
    0x5138a01800400721a44c41541c9a0b203240c0c0d84d03400400c11007404407101d203421203005a1a642410703ea010024240c2500521107180713002400c2c030740c5c0e2080e1604000e99070340025481c030501000b50801c0130311001001c4900000081d5900040061900c003e148903000c0d80c60201d2038400c0d10000c1c1d01c030b0181d6007220400d4604802002005529403020400003130b806880780c10705071102084020b003488103000303250124500502c004003d00c000c45c01058490040e10034001c1c01a24585140c84a041d148810305a00464403070500c4624a5078404000a000307510000c10001d0600c0c500000d00103d130000e80300f01d0b03c1d02c0142c1e500c50384c441107107400041101003c1c1036042032074100080450340101c80c40182018058583e030040c10300b80101c481c2c0c0405a4000c00b030381020015040044511206070761020019022942c500e099544601000030300740315215101c1610392a014849a0b06001004004175907030002803034050040502140d0660349406003003c132919507080e0f050100f2500105039504c564 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 413087140 1250 413085890 413085971
    0x10303120b09132105040305070f06020303130203030409020d061e18050403090509010b0a140301120303020705010212040c030b01050102280516060302090f0301021312080903030a090603 82
    0x35902c00c109401d4501c6000c040884280481c0b005004000c0010341d903030751b6aa0380c20350501d03d203070582503400048c6000141c441084501d50200a0740c1d002040d0110524610b01d460002910714012600042c00c02440000c41041030540c50b4072040448000d11220300307980c6e1403d10501c88002c00c03889815061002d4488280e0a2112544515805407003410300d401502c0d145c4e001300b410344c4400d822540701000001101c00e00350703070450200c0c64805600e1203894590341c10048403c0a8088854004043c140c01140b9001041001c1d01503c0d103c50300307a00c6844240c9860b003800c0c5500c1d40030388420382c0e090307140d5000822a03500c0480d68502580e84103925800c80804040c0341c3d01c48862082095580c0c0c0038200c1440f400c210100501c038000c0203541d40241e120380c20001001208410b15074404d101ea031042200c594030b03154804a40c4100c0b40e01010340200200b20b400c11540c248500745034141d250000003841071001d5003244400c8180c803002c3c0c0d8100080d0b8002840c0c0a100a000120303a91960200401d842 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 413088390 1250 413087140 413087161
    0x10e0618070503151f0801180209060409050c061e03070215010803070b15030f0a060e0d08010317130306060909031d0a0905090f0708060411030307030518060c15010303120b09 77
    0x41c0c0c000718510140c242c01d0b580c211b4030b03017114002e00740f881c5840841d40c50503065103401d00d141c0c3e0700200200d4082010b1000e95456940d078a20a104040c0034580205205850b03540d14003954a00704030b0340e0003590340c0c2e1500d568000d440b50040001c28510268950010840410000685280940c40030480b080c41d00c86207ca40040510382030b5040c0d1501c500501c5040381c0c1010301000c8003907441401d011803003101c0707228030b107080c0100c40b400c8004020840c2c0c0100003090140701074559400c03069002070b80da654508101e04200b003d5800151409051410014080c0083d5000d440814001d5841060030100048c0c81055104403056455015405840034410048640c1c0b10a030007614000172030327052f415450462400d014041e4013030f020310740107001080113104880d0000980c00d44224080c502d005010390b0042e080c0d000d101944503c030702000b18191142c0d2a028104e070081c034103001c102d40c1e10308c00000f806030b4106003d000403000114402050b0700155035038021804c03a6680180981d807660b590541a0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 413089640 1250 413088390 413088421
    0x61b040513060506120a0c0c0201020a0b1e0f040302010501090207030e012703060b0f010503070f0e01050d1e0c0e030a060b040f050c0703021c090314010e061807050315 74
    0xc0c400242e41d14000112a81c1d420010001d82e00400710400052504046a50440f2080705600003030002020003100180e9003c6203060813680d10400c120942c0e20b542819400c500409d005a482100c218014007a01660041440384258460b5000380056070b20384424100740c0c021500018042400d040344c072001036019411002488121680058000342c2c401c40442100507031b68000e4401c00da0300c1090f070126040846001176007200a0030b001e46141400346004008603082e080e010100608440c69103461b07880f4000f00c0350030900c9100280f207801c07442c81801400c0405203140e841154030f000700b001655400b802064495a0300100580041c4041d602c500024180c01d00c0840d611550300d0301005c185400d980b203010300407080301d03000548504070b515010b440d10700c5012103d4200103c001c0070091803a800010f00003560b60050401540407421500d840c00340003280520100b500441e410000d680c1502d0306400b11001c9043c0407550310981d611309050b11500807180c03071030b41c00502d000012240303060207010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 413090890 1250 413089640 413089669
    0x61514010f0e0402161b030b1303050408060705180d03390b0106020d030522050109140f2e050421021b030f0d0f030b031509061b0405 59
    0x5480e240c2ca100300080480e8016564160807103508403403c001c2c004901078042e01d1010b24610742c2000f03070a41e2682103400300028060761aa00d040c007844806c040c41841610000d004400031903086007080c0c032000c0e000381c101c5140d0b402c880b0100304131700841c1e18160480c080d04503011313103405045841c20079490b0017088144052607034420f02500e2098004070001403020500d40154000314040d410240001c0c142420b00d040314007014100814094101506070000d0802c601e50f00a842d001882c1d4945a400340c058107002402c0f01c500200c1c0c405400001291204807080910140c80c00354151194030076408000c20301240001e00c1b42d0200b0921500203074813071900540501c0612000504000380c58101c492200804001a0881c6486040b2400100c5195000d804220b02a1a440d80b0340d40003180e681c54691040d000f00841d8000142d0700c103020364014555a5405016120488e20000c0c1f03100c9114015070f0783c64030700d204180000d00100000c0c00c107450142c0048040c140b4003850041009080e00f4461170 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 413092140 1250 413090890 413090897
    0x915120c0a03090819020f060702100b01090b22050103090507030b101203031509060b030f15030f0a02030c0402070203190303060f08010902030d0201020f040e1909050a061514010f 79
    0x107000701040001c80504440062510a210784a980d424007d040926241c140400c43c1e20030300a00c00d881d6000b0030314540127801440b00003100c02080d00100c5003012241d0155091403400140140c40c0040b801d51031448100e20407504540d580c0c1c400045003241d60805018045820a29041c4001007000003a181c0121105450340d40c41a294406d68024548904048020070f40e68013040341c13035803141581c00d030080c41004800c004086c5809504d120500c401011340050840c2540020120000c1513041c1701031940290464104030320080c5140c1d038865141809a21a10440300c90340e560345410b008450101e64058007030440310f038070b10542032084181010304030141901c501c40402c145003403400c124028440540041180b6405005060030310040440c03020442e40104081d109000980d022078049803840c200c03840c0c070741e9211a108240c140400100e40344e80740c01c000340e240600c40c0001e82100202d000307200420410080503010028440244100c0313040d48034002c0500da5643c01000309840031400c03801c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 413093390 1250 413092140 413092151
    0x50d17091c062726270d0c06050901140d0f050609011a0a0c0203010504030314130b061201020d0608150c0703020607050702121c021e0a02191206020915120c0a03 71
    0x216484c07920340001054011038070110005441020303616095072040d03282550000d60034440340d118001420744501429040c00400600001c01c2d910801011100d142ca1690182c0c0321541488500041c004200e9007543c0700b41000d021581c207180804166048481c202c2000100c4622018580c10030b4005000c02014003046840c203c2c0540c50078010b03144035501c60f0750700281c485a01c241e03400905001902689410004484030300c001010100d0143e00070348100e5264551400c1104400e01a1244803c00e81d0914105400041d240f10000b0b0210610455488210340c1550f5030031a602d42070040d51000744c011703440000403a542d64099030041c40c07514005401d00e02ca03001d509084034034003440300f480c04414014000500756810b80c1409a09040196640030090682c0e0079008255174070801c0714068401c00120010340f490201242d240c42c01004880c03001c009041c840c3c1000c8009421195409019005000d160400c20240e0421034071030a1503100c01a8640d10f40c60305600003a00813a8845040c1651034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 413094640 1250 413093390 413093453
    0x60b09120a0614070809060f07030b0a03062f0a230f0a02070620060103110d0b0f0114040207021804110d11030d09050d17091c0627 58
    0x180183c00a5102022840303030641005500104440c80c010299855600a10305208900e4503841240c0d403c020103142c0890b800d82d01e60005200d443c0d05a200138100340ca4020075030100300400300c0f0207100404a0705802c0801031200d0440c2440d1103140034000c0060031082c3c007120400401d801e084080300411501c0c608182c4c4030124003140364090075a00c40903a002050410200341e02124500704504282c14509806100e03051255903640306002c0100503440040d400c480640711543d840c030300c941e041504083c40e0f00b010034241c0d000160070f020b419801400704450303580fa401c0900840d582c266000d0318490001d480360310750306a2568090402c07a00c81c580c01120b028103980300b080703040505015914170194000303142e041501d000001c1915005209103000d04100300d030b0303031150f9100019822400e8400180c4003030034a00c1884c0b280c6040c81d64055504000f0000c991040c2d045004910b115031000c00c0010081c0c43c000c145646800f02e4401c2c400c42c510340c40000210b60007280c14001c0c0000e03005121400d01c1c1e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 413095890 1250 413094640 413094653
    0xd020a090e1c050d15080a0204050606070f120f03090b01120f0203010606050d051014010f0509030105010e0126030405010e0f0d06270f02040207030c020a1e0603060b09120a 76
    0x101c000b00050408581510300005510964111011100801035800e16001c1640c5d02c44d000c081c0301031303c166551000160584c07548400c079002194441e0101c0100c1701035150030f01800022212000010305d050001c000c01e18001d2180340c1281d0707084521160305a180403404012910041400c40381c0c4000c1d0080c04005071002d00030342001c2d000507141d01da140c440b01000e031400c403200101210155201c80400300070900064220322490b0f042840d010030f100c00000e405845511880c034143d074042d844c3c84000188800802c001ca41680c000d0700056403d191926040c14000c201c10307071000c410740c0007040100095070107030a07a000d000300060020011081d28000203805400b03815020b41d00c09445445c80319800541d051410003207242d80704000041d05180e00e034000c6120100000074056075000500906040c090b5085001040e402481d600056842e0b5003060344550b03d030081c0e01c22900041c000803440320302901840c42550000a031081c00c04080c0410061070b0a40301030751408600940e900702d0046400e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 413097140 1250 413095890 413095933
    0x31c2003040f0918230d0201050613020f1806070812150102030c0c010509011815140a020d0806120604060b0f0411070b0a180f03170f1305071e080c0d020a090e 70
    0x40b20707000052603140500c280410120501c08000b8818410400d001e162003d0100340c843c4140e119008173b508240d0200420107030301c105030010348102804140c0d204191070742070b07005116025401d2280041003000c801a2303030f2030181000700d0b04590046582000030b54803400c0607040c10340303051401110005140045c403141851a030841880082d10f00a03170b020090f0840796012078071640016591401118510003034590026408450401040d0004100380e0ba403030104802c2c10172140400d442090a240c90854028041445200c0c020006204030b04820326051243c4511482c41c40c010514200c1c040c0d90740300c1c1c0380b1001048030b90125501c08801d04810645e100b0101050300c5484030080b941075905001d018042d0030050b004c041000030080104a04001040541081e0070560380c664a0300c0905c1c20a003003440f1900035000c1c0ca81035a01400e41d02c04100031160441305440e05564120843d1428800d01098103100a0b400c104207041c00c0020750503991180e4114500c0c5000e58115043e0844003981140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 413098390 1250 413097140 413097163
    0x2031522150314070b0a050d0f061e0f180908070b09060117031306030903030b06030703021803010513140109020612011503060302031c2003040f091823 67
    0x1d1450144100403814480403048180c031001402130a00c0c0a1500169214104d20801002408a8000702000054025018107010780c01c061100940341c84030300050001c40281c0e0444990010700c009003451104d4203003402d80701c1c11400541101450400f000c0903140064048400013810000c1002140956103c64080d40c1c00c440030700007030351408232018070072640f5000c000709940003007000e0940206403022490071a505801c0219a22140e810150010318400701c00c0c0d41c11000020030000404d0349940248075680314040d0401020401209160132030308111081d01c07400842c40d14034000308104610b0b441907010b0507400803608421550102d00242c00804280f6803443c801001800311540107014121004c0c2d091030204407041c615000030750388081c3c000c2c0d80d140ea84150f00301d100300e1510170b000284000010180b80d629200d6a000940d03621b51180c800c83d50003e51880340030924914602661748498200c0a603004105900c0e26100d0311140c490003140881014895015034200007481190a1300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 413099640 1250 413098390 413098421
    0x1050f0a0e0c091002070608280e0105070917100213080f030a0f0807081b0906041418011d070e030f07050406060e0303030114010c02030a0602190302031522 69
    0x41140d042131249400c4070603028010342d0040d1509109242e03200310025403000020f03a407400004c21042440f1400c18211120203829401d000390904940c0741504954040c0f80c142e43c408600d580da40c0b08281007807070a0401944190000954004284074680240203078a4a40c203002119655560311545004001a90314034590804070340c040d24142c1043c00300c2c0c884415130511500900d40a0401810040c3c02400881040c401031030344007005094200b07503005407202505007550f6035200c80d202080030030320103007407486803095904500c54209144007940c1240c50681440b50802e565184511020350020480803c11002d4080c01041e0340c0c04010607980c1c810618040c0c41c08070300300003c1c00240c403119080b840034000e80b4141c0c0e5945803800401c603070440c1c540010b984103000e45280100d500030500c00d0040d6051080100c80c40c140911a80140081c0f0722511f00c10b5110321709050190160b0200321124415078000303008650240c28120195054080d2024100409547c0550420b003140e00400031400c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 413100890 1250 413099640 413099647
    0xe01081b040204050108071d030f060405071e1703070b0a09020f0303030c070b1b07050303090106050a1d070324170307020d0f050307061b1e0801050f0a0e0c 69
    0x85002a2403800e14090050310305525040c100300020b80440d0014207120300704090381c030094924041541081060300401000d03240841602d0b01c45a0380c80e94256010386840c0a0784c800042c03040b0080e41d0110b01071101d02900e408152800202d00d980b00c200380118003aa00042106c400018010702c001032003000700c03200000c0d00182500501c40b900c805207104500075807081050254042c1c08100b40e0b10102e90105c1400d40b07580c2c8281d10382912180d800441d8000000114007030301000000b0001d54820b203a0800204151551001080300c03032040d500c1880c064259031b042041c0c00803098145154410154200460716900050603003501c01d002500308006c4440581051180300402c4201304100b0b08010001c42c2002400d030005040101000e81c0100001c0352101d0304010007006205485181b80c1012081200c00c0500d0f410206150000c103544002950107280034612107030342c000ca02c4a80940b940c030080544e09240a021084030120042944008001400280c50340b54030440c038400c5090021040c0c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 413102140 1250 413100890 413100913
    0x507060c0207080c0d060e0307061b03050103020a05130209030a081308030301030b0c03040c0e0f04020f032d0a060f0c080601171902120a0b0306010b040f140a0e0108 73
    0x4440c8500240400c641101008101107000060541d82c241c1c811140d4020b400d0491800b00c0040900d144608003a000100303801084c404140e001d8003040540720074444203d82001021400c50f402400020352043d00302409101c03504040b10800112510f40200520f00381c1c2c03060000c1d19120a00703000321101c3c000001c4022440b01c4c2e4041a000a1040500450455040d03642d00c08050100502c1e41900030300110000701401080900c0c840108509031b0703200b4241c285555450411041110164080c0c0b1031590306142070b0500045410081049000d20000007480082c100b549a408800d000402e20400584002040c541d114450079049040e40005419107030030000360104031b00800352414042001e00d04883c100c00384d98070307030f5001200701075082c201504903205070000e000d07030b075000c00030b1214260402407480f4940c5d10254180d50201d00300c80310760380c0c4c400c800e01551049005035450044003080401002008030320b5035541003070003000d162015480d1401c000c1440c0091740201c800e503000b6940c000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 413103390 1250 413102140 413102153
    0x6070f151d07030219180603020f0607030806040f0b061209012703110109061407020c19050d08070b07210204030201080c070615060f110f07050105030a1401060507 72
    0x41980500203007580c440c004810110703403a4603152101030b018400440d800c80200510004840c0504032503440009014100d0003c42d0080c02240402c80c003d200c030030400d8213a882e144056900b41a415a03e11150fa91540180005060140c3c801c00402c3e448020269895440c1c801800c0b01004c90150810b20745804120b46007594003246c08030180b544044000500c0e0112075020803141c80c2c150800302e180d00481420a80100705800010b06030510b00151865000340c120001d83c01506280e0845030710710100000c00c101520405011289860060820426400d020101c801d4590040c0d420a04005454480f07a002603411501c0d4000251200c3e8840f0441102610100c00ca0140348021400c2500710b81c0040d103084c1c800b90800008110100e045010448941c02250400c80c030410305c0820903a80d848088c1800c4149407240012900c4800201c50440c0001011601440a0001084014940350040d034580c4d00c0a4102502c15880b1075440504d580c04280c00c038000e010300d0b6101c07035840c3d50505201 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 413104640 1250 413103390 413103401
    0xc051f020706150b0403020121060b09100305060916030b120c0a2c06120a0308010807140d060b2806110f0601090c171006030506030a080307050906070f15 68
    0x410369860354607000d0240088280a54081d0f1f0750a080c508991124003400044261000c450441c40c02d041510101d03912148074060120104166030b0000e00b03030080442501500c2e4100c1e61143c1250709000020540c1d01d200c0c0b5000c5400485003400103950140300080745184003001c00f002050780c0204980026401e1041c0f043d00140130010079020020034171840314000b00201c801d040100c94030880819182da650401ca0561740b62103404880300041d007072a000d00413078024400e201042c090b24100040d1040900b8108621b404000c00300340121036203685d1540181900310318103800545607940094214003844024460701451034040101501e064802041032410758454401e64000c9011050075880016115054070b42e02000420035610645080340c00e40d020320b200c600b00d0a101018407040c15141103440c400c1d18039540c0c00f401180d4500050554510b85007400a03c140000c000103a1103d20800161140c0100240602c0c5040c4498031044001203184500b558501d403031148910480b0101d1007030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 413105890 1250 413104640 413104661
    0x70311072a0f06020c09041e03020f0c06210a090206040b040503100b060a0c0312150e090f0a11060909010b180108090a031b08030106021b0f0906010c051f020706 71
    0x241c0b2000c0d41414002900c40803079000e0035005142c0c4c03101043c10040f524a0030300400f48806481d03001d0f48d4090400030341c0c40c82d01e54044001c40c010b00600389000d040590450709183d045192415491128404000e140000201600300b1070f9600d58000740180d46040003000245440380c01140c50340c4c184000c2604140035001d0019420b40f502082c0d01031500c40006458141c034543c20440c280f82e00314101502c1465080840300002407900c0c0a4480d802c0003240c040054680c01d40f60680c8a42da28400f260f6104001030701454240d100c28504000101d062596012040015144a06000b0b5107c0490452002a003007000417000c085400c8400340d00d1b40e010000c9898003440c0070419400c1804003140ca48001003405010421508038800d40540c04543d2404069403080e01c0613525a542c1c00001c1d194101c1d030186044c000c1000c8110a007504d0038040c00111501c000f4101c145544603d00159003103080355008940c42d00403480c074507a0000010942c0e884ca843d036144050780c0e0348614585241110414680b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 413107140 1250 413105890 413105909
    0x1d030f03040617070e04050a0e01150801110c060408032a0403032c062209050601020613030f120f050405010203070e03010501030807030309020a0f0b071712070311072a 74
    0x30040140d6001c0d44210030000290750010311303600c03444010f0300540841275200c400e560801c5000b13502c000304008020101e803804002001018010701c04402c1c14824584000f1490b440103002c0780100d9456401550070400d441e0b120500304800c0c8883c00d500c041850203102032030f000400c0400505400901201502201039481e0340a02c50680040c1010180120000d0041343c000c202281e5400191020784180000036181070b840c141d0320703c1c40300f000d07280c1182e820b801401540c000c5010046071030341c10640d10790325031203c00410101403411140380300203408420000b038035501c204a0182c440d109c0d1500441c0200005a528909044098000b051003100140242e141100400100f00c0e45010758003842da1610b404078401c800c9000280000d00c0c5078002403442d4103848030000f9022aa00006e1442c10302c030b4440041d500000c460103a8090003070040803002052803400059502c0c0c0720354401c43c0e86101111314a8145242070315941300a0241d071240c550722401078202c43e0b09890b00c001e80c0600502d603002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 413108390 1250 413107140 413107187
    0xc090a020901110d03150b190e0406031e05010b0d050a0f03120e0d031a010804080703030603020a080c010e100f12020409060609030212060603030f1804021c0515010e011d030f030406 80
    0x54023200550740100502082102c407586281e180d644981003a00110303007154000c44901c81048001401d0800c00004843d02d41c40c003840a91030781401ea50940c00302e6001400380116217201c1e11074200b44024141d04804000c41e403803605c040000144a544001512003000b80100382200c0c0001d004c58101c0241a00b00b80740c0b080e900786c03981e0b030300580103a4029806803149071502c850b85070940281509400083d484056244049208000015001080282641e484000c000284144074891000c07146240005150301840000c2d940510b903641c1005c02103000051030a603a49003010100c42441d0824800110516000c10551403e81c000307115603040c5c50098002c038104200001c4c0e49100d49000c05241450200d40d407040307907144031843d0032500e4028200707540e5180074010b40003000c5102d9104a00700c40c50100800c0090071a0394901c40821010384414030614402d40041d0313050002c03c1c24007003140000d140080d00c0f40d1018007054074031800040056440e83d0901e075014201074122160f5207607144046 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 413109640 1250 413108390 413108407
    0x1804020907050f071103030415081006090302150304030c060e0a02010905100e100507020307090b120a0302071a040801150303080702010c050307030b010c06091506080c090a020901110d03150b 84
    0x40498407296408448117400c03004941c0400c0c2075000d603a20911000340400d500c01e002d10303040095144510b542844603120543c4401d4203a401c0540b9006c040e4010b00310186039003d0070102d00040d50024040d0030240c01e00c116696903c026212540000a00c60300425961421543c0001c2c0800c0034010469101440311543ca900a041c540744076031851284110014000710680140c1c2110b41a60f0045c05075201c050302d410904000d0310350303c820b0502401c4580340503141440040340d0000702982c164080c00106107071507001c10710211407556060405004000c005010b01c2d01740b00d1255034402800104212910b0340c103004d4401c90b0b0081409096904048038601c40903445021650f02101c0ca08001404000c50f40040f91015a0900300610562070b2441030414032440048041e46510034100034407216441d800016141e41c0e0310700700e048d005414980819095402500603055030b0106140c1499a00b680000f01443c00c9024550100466943c7d4040040b18090503d207002800300b0a241a2a04912 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 413110890 1250 413109640 413109667
    0x22701170f061c05061e060409031d01051c0f05061801030308130b2e030312050c070b19050703060602030715020f0a0e1009050a03060e0705180402090705 68
    0x1070006203c0d40101881001140400d6540240c080e0803404840c01890700d4004a43d840d212a43e46001041c0820001209454940504150a9450780d0790840c0504011074841c4c610008140190500c10103124140240840001264514540140114583d441c1503a40c008031003010b0442401030b040e90350040100b03a0f480f402c1a04580d41890810100c0c3d5508000c5030655441780c0c0001d00e01460300050106a60400c003010305080b480c403c02c60b0203020820310b08141d000c0342d803100401280040010842c0c2034007940c401c2c1ea100d64540e03007007840c0a000303a68880c6e000070111241200c203100f101444081503558800c0503071106180c14100400c5080072000ba640340a07140d402001c10b801d803000c80400044d60303019640c0c002090a07805880f8001d281002d4205d10588805500400f0444103404215104201410480380c2c040c007007040507421602d4610180034043c0f543e800c540300ba15000281900c03804084280d50340103280002d4207050610400c0380305140a0244000c1000070b000d86000c1e01031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 413112140 1250 413110890 413110921
    0x530160f120c03141e1f05010f050d260301060905060301140904062004030501110901050406050717130305010e120a0c0c1e03120305040812040602270117 68
    0x304100c03100e40b00301131300d2510b605d444044020500c84c15440c2c2c8000384041000101e60103445007207691115042140030500f011603109100d00051039400b0001045030741440031940c95600d006003008429640420201200c507031580c160071020a0b0000300403c407070b0368001d890b20003030b02c421100d01d4610f500d00b003856030142c03c1c8404464030800d410f5022404010303059001e1410400c03003a0b074403014a1011030300c103405900310344030594503542000d21a00b5410302e2442217030040c2c0c41c161207040c205420404112032a8015102c119940030b009109606010b441c1c0000c1c100b640c041c1a0f00d448441d040d40707052400e4840c0ca0510307a00d20341c07005140d5007080e007100382600c00c9035407030386011001c8181c40d0074400302c505610b0b44102c88001501e00071102441c240c2003c00c095900480540001601000c0c1c101c0c21180c040310013514a01091020503000a103002c4540e40040c0100009030a18420078103481c3c01c20f940300d5854480380d458120290440d60003003444000c162005440360760340c0c94400b5001847e80c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 413113390 1250 413112140 413112143
    0x10c0e032e0b010c0b0703020c0c0a12030e0111030f0d060b03150123030f09060f011a0d0f0203090d14040e0a020a050f161b0530160f120c03 62
    0x1612020381c00903d134841e0701c2d10300c81560403030000c4a80741889031010b0002d500034190320390740d805107040c0c40040781403625044044400900c0c241c6420041500d00f00c40389801920138034100000e0451240b03114908102406c04111510340056440481040c4001107030015405041121000e0080044403004001c0c0031100c0c10081c2803401c461402d0819080c03164034580703814100907401105100c190001204030711b100c0c94061080b1400b5485404820b071569009105406803500c3d881042050785c82500040c040601030910003041002c6941b120f401a60811904680701c3d5202d03040c40001180d01c84401c203103d48403400594075140c100240400d4840d401080b40845c59000918240b00f14810030032604103a400603c4161036008244000a110700841070070340d03203512280701070102455281050000c403000104025100c007031141030360342d09414030f9a10213100d038580c1c060510f4440c030a00c804800e844041c20f0140400c1e04100c02c189592600ea006050f480c01ca10722500000340c0014100800c0d039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 413114640 1250 413113390 413113483
    0xb060f0d0503180a0911030604050f0f070f0e0a080307202103040302152206200f07080703060e0304050105090108093a18060e060705010c0e03 63
    0x3400d01c0b80421444c0c08180c3c484400305142c80b00d00f80b00410718001950140204890074855034840e44542c00e0070074001d50342c4179040e261b08008241c2c0f071401403041a48107907076030401080c103140000004a0702c08003540314000c103810004102041050020000c0c4c090000c40d4000307403085602a02180000c01490b0506040710800c0f03c030740f01900c00400540c1c1c01150700812602861000c400e403548503801006e0b00ba81a4031803c25520f40f004c540307206041c181c94840e511010154011605402c01c5200354103031526500403034010041c041e20911200000e0404040100b02d042c0c690700d0000c0c200c4280350072040c450f80060000380a6a0792050071561400424038010b03045454140409040507401c11000d100d00281680f01048481412402010380218000000155100350400d49480000ea541e08030841c0d20610207200340c034041d43c074049080b0805004242070400a44d40e440c00c540d0f00c3c201c10b401240802d2154000e6150822200c0c4500301d01d05144c048a485040800381248504000f41044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 413115890 1250 413114640 413114677
    0xd08040b0c0c0a1401060f1202010e061810080919020a06081801020a0f030522060f060810090209071e0311070516030b0c0906031803070206070b060f0d0503 69
    0x1000300801002c400990002c1c011134041d01025502402000c0510401508003e8408002884c0e10010544020300f501038541701c00c0e1003900c6040020540c00106980f41060200c030000e0301c1ca40300d4600d000f80d501003548858540b414507102c0c1901d801900003080180c502903648103001610342d00f99000484445050100c2e440d1a031141c0401c421180400c1c00320789620200742e101019502c03441121a10382c541d2800c000c0c5031684200f8080645200b000350f03249545010400000500d04d5000546112441100040c1551140798060034895041940c2d00a07d4032001a0810751a00810054000400d0304254400c00c4000140350b1044080020700014165a00c00100d2125039013803c0350b049640c80400e40e101c01d00f102c405081a1140c42c0170a0b12240200800603600c070b5100030403140390340f0004048070300f140e40d2004646500746036008444a0b5000a1040300e0041c2c880c0d801070036240b48600c80c4071030701e40740241c01d025620303105012092240801c14984c0000c40c0d00401141d14034450f10340110700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 413117140 1250 413115890 413115907
    0x40303140f0c06070c02100305090307110102010f0906060e0a0203010806042a0305060a0e03040605220506030103051e030310030f0f0210031a0402040303050906030403030906050c03090d08040b0c 86
    0x30b8000c07460000721a01a080c20002e090b82c0c000c4170f4542140c800c5820000d000d00c41c4a04804a9074200e9806100798001c012000115140e403440044010f0305100100702456501b058100303480703202000b01d903501d0702e030321040c092009849081603104c503c0c181c08600715803401c007243d6980c40018001520b040b5181d039203a000c200300455034110782c608140c0c0c4090019601c1c90019500c1904640d03605403503181c105400e60040380071048402325107060792403605111844c40f510140d0030710050007601c0d681d4070ba840083c40e030701c900d00550b0085015101074a101311080c46000b50381020011942c046400c100100184603400034140000d4940048075031200d0016454400790402ea05c403406940702009411071215954180c20034130481c205403460308409460034060100b80e000e640801404902c5c00d2105150314104200a558003501916000c20502c01544688084400641e040c0c0300700c520000410803040c0d4200181d0300c0100c81c91820140900c0c060725030342d0b00d4150203803110600e5070300020901c2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 413118390 1250 413117140 413117167
    0x120b03060103030f0807033b010609020a110c0a0e27071703070b1803040b0c070e1312080718080a050613030e0409020607150603061104030314 63
    0x100040005000c80d82156100d00f0064003a464800071070380054081c1000074032841c4a40510000e00b14406404000329040d4464040d4028400003035414400030180c6400c10b40100b409603400502c8070110050307039400030380e4009180740903c200e1407030709603c59178000c00320342c80d0302541e9022917100c4090055aa00d901c02000c5064600101c0b200245d10300f90016500d14201080b4407084500480ca042c00c0401d009450755224050070601811000d04100019a19030991030741d00840e1040406503450702d03840b102c20391115080b4010380e00d529448003001348024500f008110750006000788072a9554082956884040011070078500104240395010682843c000c00408502d040a1001c8005954030345940365a00c45c1c4d0b07082c00f92070b41d21411020844114500c0148124250540d07150a5254074000620015101030f2000b240c02901c1001240003041103060b170031200c401c2404021400519604062054844140e0000e160010820003080025000300691210000145c0403d80340e4548110300d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 413119640 1250 413118390 413118401
    0x40207030302090402120105030601080d08040f020114040f06080114130e010605040608031306050c030301090c0c060e0f070b0f0405011202040806090f060a060608071b0c06110c06030c030712 84
    0x83d5002400070402150000402456505840095084681c0c82e83d0b40c001859903126845404004644114081004030340a1403003070320854010304060285648080f182916548154004403810300c442c2c90038080d0742d502190890052452200401c140306800340000c802c1e051405c0c0300d403140780e5205030801100d202034100800814005104100e440da0b81c07503070940c03294804d80390300c80042d04260010036102d0050043d11400404000258210fa00f040045401040c10900e04803c1c0142900c032640003440b2400351440341028607001e17008003d07031070350a0340c83c1514030f4001d02103480003400110b141c0c1c00c40c241540d0880d442481c05501e00d00503410904000d1085410a9146004076020881600030004113070001d00200d0003210016513411400004881140c05608005500d80f00401c003244d10a5001c5814036009155000c0c84108944d03a40720090312540c041c10201c2c0c00625a0300358020240401c14405038151181803552400c00714500d018440100a04240440361140120120003907000b03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 413120890 1250 413119640 413119657
    0xb0f01050901030e2d0f0d05031b04030821100b0f0d090f0501020c160f05042a180e040b060907090f0b07060b0d0f0b0604090f080a110d0e040207030302 67
    0xd440040351886a00d0180c542c0b007605c2c0c0c6a25121b0385040b40c04a8100060302c1d0b8032486299101411610740050300120340c1c850484450720b03441e0a000c0800416500c0e0014995418500e8450401d010381044e0008404d50080c50382001a0315900b003004900c0168003102c17071030b00f4800040da039101c0d2612118401000940c50141c4409860381501003000015401001d86401090850304040c1e402005405803d080d40a0745001c0341017642d040040e070030b042e0801100340d030b24588000140c0c16003258488030008003070407400c002081c1c9511a032008a800340a8000760540c14504415481c00740c1b115404102c002d400706000d10081400902014452000480506260942840c8032a5a140c09075411b401402e0107a0310079203082c816022a1400c00e001003002d40d0300c021840c1c2910016110815020ba00503c00c5801a07180d0021318001000f46e031501903024418070b4400c0d154545002c005040f00524410320b14140e1100c10184101504000303506281d60f0100c0b00076980319200d00d0118080e0082101 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 413122140 1250 413120890 413120923
    0x9040320030c1e060403120c05120a091104020c030415140c0c0405060105040302130504060f020a17090c0d081c020d051506270a1a0d0b0f01050901030e 67
    0x74001a00d07600441e001d1104000d00b0183d0044404000300c0c140c94850541d001800704100020300140c021280d00810280074141c146a410403106a0080a00345130498041082c00e40d87d800c2002000342080c40580c0c0c00c2000d480440c01c05900b600409d56034482c5014182014070981414440e1600c501c05050009030b400d1101600d500359010f10300d80c2d55102d403456900ca14103103c00103001e54454426501200d400803e240005400001504020000a041a6001501c0e101c038a0039104080c001441500d915580b11490003016030020488544050103500e03954100481040c4a59541d20913100550742104001f95130f643c480b10001200d01e020300403010f00e20700100d81660500b265901c02803103824030f810310901c0210604104503141c800c9800041e42020440d041c40b5a02802c4030390a00d00b400c4c09415008180e4849208031900c07104a03040d5501904001900010a0058002c005c0001402c1c1c80400d070191082002900318040c03a149075042590b41c0c1d4803003580b09410480303041c90300070015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 413123390 1250 413122140 413122147
    0x13090212030f0d05060d060c02031b0d2f011a1302030903031909051b091e1302030102040305070e071e020c0f0d0f08030a061a0f0f0d020301090605100e0904032003 72
    0x48c000303900d80e003002079444444945d2080a0b010b50801007145205000c0550b20221560520360781c3e14082c20030000a0709036040700d1105443d09600c240329507c0d13036414003c1421040c0240c0d0007000309001e030151701900c00b1401482031100582c000820b0341e42004108100000c4017482c0300c604401840321080245c0b0900c030300303c00755502a2604034010504c40066419100542d45d041500c00b2034100622101412103420001440026a011000b2a03c0340b000300050f15143d0b0b20340b50720b440e082039a0403515828260500f8000e40707540040606000401d107441000016161080103034130348440c0462103000340050b003a8034426a40700c1d0102c1010942c0407425001510232802c220426030000c031b503000f1100d0300d00300b004a4842892044d0100c0b185d117203400b251410a0240c03c081c4e803a009009220300401003070040d0910303030f58180091406403518180c0000c0d2140b4080800c1039200d050003a0405100031070340a92131548840002030381c03054040c01c2c42c040b461200003001c05281251b00040d5414040813 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 413124640 1250 413123390 413123411
    0x20303071704060e030303090c01081504090b01050a0609180f11211e0103020d1412130e010524090d05030c010f06050307061d13090212030f0d05060d06 67
    0x1d102600545146a80d000d800030b4801041c140e0341d2100b0b881c0d041f0076611024001501d07610072400d0a9200c0c1c804401d041003c074034507010600fa5040864111048041040144654100041040b00900d100d00d07019642a09d000340840112545148a03102c03a5140d40001a640c80d080d00805501c041d080784460f5205141005501c151000b802005642c0d01003901050303003000c0000b40126910074800030301042d42d00e5542048618400301a041702d0f009003101c0101c0814000340249124038038240c1c04140e44803c0d507844098208080e0300222601030070400140825111240c0c030f0041c810032340030b001c0381d1005000d0389484a030043d224210f81c090107403903100080000101c00307003084408040c000c1c0941f28548503414240c0d81c660085d0354142d88038220030400342d44107a5828001c0f0407002d0440c3c0015081d04080340324509081c03a43c08015407a440304400f18180601c0d12112604c60034003650070310310302011501c0c0600c524582003040e00e4031000071558a68a899000d452542c1c03110040103160a02c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 413125890 1250 413124640 413124683
    0x30a0f0b1e010801090219080901180f0302060702150c09040b06030705070309050301180f08130609081e120711031917041208161a01090c110a0f02030307 68
    0x90081c6030004100d007000150104450091b600803401103140c103a0340304404001251400d40c02868007415640f40d900401c4000c4280036051903050185900708000101400c01070f00d401000750503981190321900b103030901101044100f40d003001c001010107980d60f980b04000741c00f03881607013041540b20700d0000a1010b0399801c40c00400010b4400e03120002002c0c1d070b030b8041508075914480082009a0030340c090000080c08042201c007000d120340c1d40039080c819000348100000031036801c21000704026050074450395404012605a00c00390511480070813040261068640145a048003000304c0c02095000c00c0007600f4044c03000e011030190860741c03001001c415654200c07c080409540c01c8059610241c21500d0b020226015a0644015201010026070ba86007055200e003040040e03010701100b04100051240f00340003000320000c10032040c40d5040c505c11204603111403903554213001d04208242c1d1003200c0440c10f00301503500840d00b018400a980082400d6200d120401444461080058003562a0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 413127140 1250 413125890 413125939
    0xf0a111014060a0506070512030601050409090303090611030402181e0903030a0c020f0d05071a04120e01021b0402130f08010204030b070e01051602030304171b090408030a0f0b 77
    0x108035581080e00f5034034000d0001906c101303a00944940c02c032500840e82c48140d40c0c001c5400940604d80f02d03142c02d030744103059401c0381c4520000702e00283c0c84210a000344826401890052080800e03800d1450030940d000a11200080407240340c1000c2c070ba00096100043d007225010b09010350b0455182500d0010002521382c0d00032148035800a182109442c0740750310005410300180301c10340040c00354a61400c4144d5a075001001c00300c81030b00501d40c0b0100c102c5542c078070003400f851040c45601c0c0250943c160140062071880000c50456000020042103504480303440284e2290a66005030344000745c156a8680c107205400c50f1110b0441c41c080011803803c15030040c021640200d004000c40e8031040801c4500365011096280040c90074401001e400d1907203080c0e110014801000c072450281c1c3c91806007816814240c2c2c591042d008885808226074044c800721041c0380e0304803244a02e44c603103503849500710b0001600704108290340d11441c0c008550654412400d07410002e005c14000300054428105000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 413128390 1250 413127140 413127151
    0x31002040608010810060e0a0203040f020d03020604021509030c060306031e070807090213140103060f06110f1504080a030b191409040302280b090105090708030f0a111014 75
    0x11039203441781c094180d9031040c0c1050350703040d031080002a1204201d0340c002c0e4001a00540f001c9008406440051b42e51340e804d07801d42c51094001e0109460b00d40100a407075151610141800102002004910390f0007103100748d034040c41180c0c490b0b126140c4501191510300c885011450b41e0f6542c000c00c1c54030340000207581c0103c5440c1e4080b13424640d2111200e1069016680c20f1002e17280d01008280041c86d80101d1800394018107143c0010a00d60381e60040100400300d900001c0403505040d0b0141180318140031480d2040101341c001d24011060b0244ad6a0a890050020309036103c00f2030b201a0641c82500001d001000052400240b054100d400405440e02c5100f1008151800580e4900c0b60034030360340b03041c4101c2d0550081d0044c003403541030385000c6125401d80d00c8040540c1c105420000b0f104802c006000c0d0840b00000105171501180191600000d900100c0706680b090211800c001e0b2040b0071148044040c0c5000001181020049440c068550500340032060800072035400d100c5070b03066072904c0380 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 413129496 1106 413128390 413128393
    0x1020a050d0306090b01080c0d0e030f0418050610020706110c0301060306060503014b090f110f03060103060c0c080d020301030b060a050913020310020406080108 71
    0x840c81440000210360364000904c144c40c0380c1e10503200d4500c0d00782407006807800c280e00c001541d801580315150010342c50300500c035611082801a603203400030801e08180c03030326129020320780800760240340c0502e09840d1000080082c542a400c41c105005260040c00d5941d05083e005c035080145000355058a1107006120034407070728240300c2c1c0c0d0700850007080001081414103003050b00f5582c85500140074408503c21810400d01030a002030b00800400725032456080f10702c1c0c0c0004129203000d501e052580d280c0400d6509010304481c054405c10b1041461641017a002820000c080c1804069560982d0000c0014000a81e10303070f100300c1403c106810b11900101c41591540f10607801121952881d90700800100100203580421a4214100721400c18205003007101256200c28002d2030000c0e03d40c161912041903403010301030914030100700d01080d0764031901c1c1d000141c0481070038030921819 = true := by decide +kernel

theorem cover : BRFrame.Cov 412949640 413129496 := by
  have h0 := BRFrame.cov_init 412949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 412949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 412949640 ≤ n) (h2 : n < 413129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
