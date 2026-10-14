-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1590
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:44:38.454729+00:00
-- url     : https://prove2.me/submissions/f9b9f046-83b3-4174-962b-490e54e64aa4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 285791366 ≤ n < 285971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 285792616 1250 285791366 285791377
    0x31a28020d0b03060c040f080706020c060a0306030f0308090d020102162a1206110301050609012106270902060304030f12061509050303040f091805030f03160905010807110f03 77
    0x800f940e5140e0900900c00507507d039592040c8407680c40480b00b0301901d070700170a1541e000e0700c017510416219801007004030080c1c8119071003d400390068406071070501d0781c080303a010320a034545811920340c2030301e84034100d08034414407962505101da017058803030004001948403603400c00b820250385540c5144e80e00c1d0090b0301c0300030ba0003503509020029800303003040202e004110307507070100300d8440c4e0139503241c200800c3c018802d075041d007810020300a00c003000810501d48490407403485c116080040035107031b001d91170030149803039407251311503410170f003001d040c0c3d000c5000c1c031003160703602600c50750031515070795030503242415552401c8050040c008100c81088040380f04110081c0061030402200300900d441c080c0c60181c16412083c000d402c00c010a00c20b00011412440c115010040000781129545c0800b5000c880c02200c01005804001401c404426031240514020826142c500b9004014080c2c01c0d140d103020f81c8100ca020075600c1002901050280c10300001e108100c2c4140d400c2007901854131811039104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 285793866 1250 285792616 285792631
    0x5040f05041a091303080603070501050f0d0608010608151003030c02100e030607050306011e0207210602210109090b06010305060d05060403350f04031701031a28020d0b0306 76
    0x41004d54014142c1c0501381540090054002e8aa16400c100009080e0300c145410800070f000e00044c800540c2c403c1c1d84c002c5004050b104002c11880303407260b10745c1ba110203a441c141202c84a294011840e40d112101250048070341c103441e0032441481030b81c2400410082c5540345824003110341d21501e240e0303d050103003901c038500990b5001c0c2d9a2074014005440000d00d0080f880388142a41003c40481780c001440d1401e41d1611101d03600c42c0b080e2200c42e0340045e1580800140258008100e060210182080c42c0440c061455100b91a40e0f8030f82150760300b180d255580240c502c05404010500550090740050782060000c0d241d400b01802c541c07901450450252002c5002600405101480b202d003000d910400074807003054440304203408440050381900140c074078031200c1c05007404101003501801451108a01c400128801580d40f4148000048910002854119100b500040c0421307842911044110300104c0303002c180050300500c41000350023200140351942c1ea6040750355041c0c1e40411046116656 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 285795116 1250 285793866 285793891
    0x1030c0c0501050106120614010c110f0607140c01020303100e040314160302060601020d0504140303070506041b090b0d1104060b07060902040c0810120819020303070f05040f05041a09 80
    0x2c0c030846c0c1c04c5c11100181d00c1880003290064140805a0f4004d90400d0480c1d0440c400941e10f10b64200000c050084002182d40d11401c0000e10104100e01c1e10070f01b543c01100740050320103010190005988901c41200c460208046481d82403040407800300c5400d8000d030103890030815058481000d824664401c41e4019a40c080d510546801c2590400510344c4c0403100b0320203010701d94000310001d0b01600075070242c4100328990460034906920f0030001c0c3c640068010040703840c1c60409007410400191920205482200b0340100420982114001d01d06d0a60010300417540804150f11003a00c0249091504c41c0d00c240c03581c0002400042d01005401c0c264000c0c040040d0144092041108543c154540801844141000c0140c404001c1c42140d080740d02440b1410a201e038549020407040c8901c401901280000e03c10f00c42e11aa40040030f58460a55a11240b009081c06042940d03e8002d0703220f5962800c6d280817007401607040680000040099100c00741800809000015014031000c5506101469 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 285796366 1250 285795116 285795137
    0x50304060f110a0320040b0405060c0c0603192a11010f020c010c021506060403200913110a031101050708040e0133140702030a050105040b1009140601030c0c0501050106 74
    0x1860107162144c0174069600e051130315103050031240803030159120b240d01c20311006c1601c84001c00180f103000e940c1d000040c10381e40c1d24901050384210503101e101c8a8140c262410001d503041180000e4820380c40f00281c04540d181e400c04c100203c98207103681d0035202d020354851120140c422034038009400e80c40c100c2000071554032045040289800325101c144d1418441281c20301000b61141c5048409880c0c01070fa0400c1d100303140c044191580c0703d80710412500403500d40c040054050410000b0290303248644080d2105107510420014000007601026042484034080c42c001580202c2c000c1c54540e10411006041030754540079054184000d901c042d41c10120202d00d082c0c4800056a010780d0796584000c201c1d5100140e410040a0000703008070041030540028001c02075640412162a03980e40c0030009008900d0a854518140c01080d164200311039821540401c80034454005d070382c01002c40011a641c2c1d590382100440103812130344170f00d805204c00014500041354003802500c1c043c2c40141c803500900d8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 285797616 1250 285796366 285796391
    0x306010e09190f020103020c03120c090f0d12360503010e1b0d1523060420030c0f0a02010207020f060702061209120c010b030601090c050304060f110a03 67
    0xc61a01801081e070b030a0384646000280b403d003c0e9005039602840c005032038940064400b49907109071307a140981d44c10b51004010808186d0310040c038002d0002e030b50811014100d40b0902556030414400100b250842603c2c5103c5640300f554200b40c0c1030221300c0503a4412400031000300302100b207021342c25512202c814051016083c04d000d41000d0031500c500611000040311441002102c400310320521544540114105101c2042031101d40d00d42c1e2024100300d05d10088010b10895080d0340d651102d003c50100004040c1c0c600340c4250704545403810410b420340810307403081600541c0014072903078101409001c0c03004500e13102400f070300083e0400d0f000140d540c0b280c0d004004002742039146440c454801000494010303103070728040c0d030701072110400000040e45a1a10a50070b1074600640d011035020041850309141d9815000300301c54000590558003143d032540c0c0c1c450260740c0351105480c0420000c001180c0010410703842080741c10f50454000403004600b8086240942c0301080d00e0001035100d1004c1c5c4100c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 285798866 1250 285797616 285797623
    0x2011b080d05061c080d0906020a050c010c090803070f020d061503030905032b020705040c030b01030b0312070b04030c0b01060e030607020105190e0c03060a060f06092102030c0306010e09 82
    0x2035411144440e80703d51002c400102d035042c0c1c134001401a840170441c2802c0d5021600250b180c41c1c1d00070340c00d43d2601010742c03000344103420801209841c4c0d0f080c000000307082c9002d4440b51040d602c9a0014510301481510340c0240b0301c1d150704040782c0242d00e5560110100d8501c0c402c20142c1540c5103e10f0207064514103005041e0304280e04003910a400c41c0d40b500840020702c207040f62400158070310305400342c00017030300907410141c6c1540455086410000144c40c020340c1540a40247c841c00d0301d040091115a4090590b41c0c206526040c408540c03c112280126402d944002d85c464483e26200342e421380940d85861a2105c01c1c0d04c40b001060849141034821324007446101d42c4203500344002c10040c03030002c0340d41030060740f400319514010380c4e28512903421007014040ca080078800078080f928981010f18003000104a5880b070350043c0d0140c03d03c0480e0003441060745500300c48481a180980c1c0c1c0e950104451103c0801000320380c1407181c40a992980c0d00d061040358020905101150314502c0c4c020b900505 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 285800116 1250 285798866 285798871
    0x3040b0f0304140c03030423040c02010f0c1103030106031d07030503030a0c020d0801140111030f0309010b090f01230915030d03060e011502031b0f070e010e0f0402011b080d05 77
    0x10a500406a28076403a240002620108c420350004100c2c010004043c2110380d0618400081c1c000c1d01f0540c94040d01074054010340f00510310140308110b0032012a00440d509864220304608a40082004102452098204407042213403082003030340100f0300c062200d00d0200c281c0d01c2110340c0c0c0c201000704001403200c2d20400240031640d0000c2d01c4c00d40d001c11402000a0014040c00742101900b4480703004991154003076075081481e0008072a5030b07038500800111710707400c22580355900e50309100318400f0780d00b0100600d50040f15181c40911725a4241601558610b80c0ba07040c62034074106407401005150b5a03c0000e501415208424903456213005060604152400b241003050600701003040121150441c0c18604541c808100184200b4207000100d046100e00003002d145103042d5510140440c4001c20713081521011a01140c40740d903a1a00d100400520074841c20040e0380c94040040e0f005c0003000340d0540d1042c4145010400306600900081080d80c01d42010f95030320384080703801e0405168a1003600d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 285801366 1250 285800116 285800153
    0x9060705040b09090c0c0a0f050d0f0f030f0209040f090c0e010f0e1015051b12030402040b03070317120906010b07140114040b091603030e0f0303040b0f0304 69
    0x10300c0e042c02c0c00200407003449810300c02c9000f00a40e100041c466540707007080d42d10135450007007910160340c00ca050550341c010140344140c40c24054200c150102134054100c080055155440700039000105c0c3c201640241040c108841546808101e1003819036124825003028601408000810b9600385c201030368a507409402089907200700c01c005001150b05200c0001c110341c9800c04c0310500756201012414204001c1d4400c1e20480c0e0114860440503800c00044c20300186115000040a100282e6085c0d55011045c21958041c400300f020030b015003003c0d04440080a806402c8400c0c2581c0c0b81d441c00004500c2c1140200742d00030200d0143e108580f41e204080e0008081c2c0010300055042c071300c9030071181c441d42c44000c0c40205004001c03409480301b03421091072900604440d100318580760400f400740d503008881d44180e81c01002c0004001c0b04c0b0328035200303040d0b83e01585c8a5031846030340c6003800f000d011092042c581c0340c4018040060290b00c850020020b445401107010703140e04062824400a001c0c0c5106e44 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 285802616 1250 285801366 285801377
    0x50a0303080108190b1b04030c030b04170702010f0c020301021b2109030304060c0c0b07210201180303020c0312040c05011124130b13110d020105121803040e090607 72
    0x41c00800d01032003181b50010001d00000140200d540340080b0f00e8030882d4070080003118505400030a202c8d4002401e032140740103039507403e1506e04c51051031380d551240d000021301181000010000803440740c3c0b41d00c507600c5d1010b0001803511010041c110040d02c44486920840d621120151801c000301c1d02c0211750440400480508095650300000d03100c1c060381c0141f074108204e01c51440207102c080c841a034001c007042c5000780c0ea1488242400c900741c41c103184040c0b0308000301c0e40903400c0c2244148100c2e204e4042004036004003036140c0e68124043e500200c0040042d220501c0405074802c0c132420a40c2c000c80c4100710504401c0e2800c0000341094284410100190700420521001c00c0c3d4804c42d28601d61080d200002a15a100713000e1040e4010300b10340280400e0421820042003094180340c00c203006024074240c040d030000d00c20402103480c020800080c0060f8040c0502d0001c131040c000c059810178211422151071168800401d45507411950011002011010502003440b2090002c1c642011051801 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 285803866 1250 285802616 285802663
    0x50a1d0106170d170604151229060d0303150609031a0105011d010207092d1116020d080f030f070516080703140d0b120c0a0519050a0303080108 63
    0x1904140303803100041c41403030013a000246286d03500c5c0c1c0080c040d203190103903404a060703c8210884000b00b00481c21a50a414002c0203e2640e00007040100142200d0461072070076035881080c0100801040340c01c50030f040c0c861a00080c007440248071440a012140e541003030300c0346142000c07126621400d40300b0320707130720701580040c003199902104483c0d0703240400303150107800010800100e06d003840f00c0d846000a1444d180075298807103015aa61807000b44083e00c1d1b142000c00c617030303c0501242c0c4511512808114204060100182c2d01c8035000d1000340010300c4c1c030204080c0c503120000580d01900040c2000c8000000300081c010140001c0c5402c11103500d406400c0c070760b565904a04031074045034060030520020600404042c42400d2107003c94810f0a0019180d02000e441c00b00030b0300422250a2041503a082c07040003111002809004004005107050040c91515052103800c000740a0079005032450b84102103031a0300c9019402e00103501c1380d81e51108562514100364142082c0e000c3c483c602240a040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 285805116 1250 285803866 285803893
    0x6121a0102070e1e01151d010f0309110d050c010810030f060509011b21180f0804090c080a11130317040504060308041e080a0303050a1d010617 63
    0x40c1d620960303024418156032134459004d00d80c000005460742d18544c03020a030001c00d078107100101c107280c119010f80311000b0a6000c02d800c422181140c4ca005400151041da04881c03092003904402c0c40c143c0a03070786041c8440d541101007816000110f005403142d61240b41000050b507804059964440a18403103e0181c50855480040700c00b001e9070041d0010340c07150003150600c542940440f44100113140c1c89050010043c0000c0c0141d0030011040b094440440348081d0000a1070140f2004203404800c0e10b1140384559440a030744601d10750094444940034800401c001c8405d20030758881011949424504d440c02c10b64000a42c2e0f0075581041c10118180003241914450020800659a00c91650140d5082881e03600305140113a0b40680c2d030250030001d0000600c2a200010300554510560f004803015400d000c2900c1c90b000361141050301d40c000c14000000c82d109510482d0003900060002c641034000b1000205180700c4100200180e075502c100c100002e07a10905000c6801e0610805415035411503071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 285806366 1250 285805116 285805123
    0xf090c0e121009030302090d1104062102040c0908070b090a0f030b07030902030c0310020408010f0207030f031109040509010b1003050c04120f080c1b01030204052803020a06121a0102 80
    0xb46118259101e1410800305400398040d100d642c00083d0843c03600400b54145038810b03003400090b0a0056140c01004100c80d255100006200d00660f1100b03a0422003960900c03008281d404808002c2059903c07009c01d20b10400e01113030300209a020049a00c403420803042000003003841c1e01c58204003000d200100300183d050014180d10814504000031030b034115001080c100611040802e034540602c1405c00c0a1088680c043c00c20f5425090080007000d800c80c0001c8100e100319040600032910610700520304c507101c0d40010311882034250050f42400d404030045000d4403800d07544000541d468015280150801105820b032801c0c05180c2808107040c030200c1d801c6a03201d14020000d55940810359001800f0070300740014031295224900d16070302d1041901958860003007150080c24038003245580078940d071090094500b03442c002400c1c04001a09500211000e200c04414601450102d039800405650380300007180040041d51208040c1030f500801107000c4481000f08010340d41c00489803c03e650341e000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 285807616 1250 285806366 285806383
    0x80715080103021516120309110a060c0213270308071d101b050606180106021c0c0614070f0503010f1401020a05010204030f0b090d02250f090c0e12 65
    0x141c00190f503420442c20f003040e00490808046e0210b44104e10b40c0c0d0b01a54187d000030302e0107008003a01c4082120303130400c000c01d80d4441c1c400c00d00055200040312001d072800e804000900b407030312040050003110a02407090300c44000d94202d50b04151644800003856042800940d001c0c1862401400c3d00411001817881c104a400006018241045c0c0c40c450190085040358003c1003102080c00f80801035141c115039401044402d5400ba40e1085400c1c0d01c500c402c2d5180c541600c030560050319503c40042803e528a030b4a0040c41c4003040f250b03922080100d0101e11039045225941511224580b0701180302401c2c030a100701d40e40041200030401000b01d582842840070035120040401ca0680ca0351000407841c3c000d00c0714024049510008000081180c59808007621a1094100e00110707543d22410350f4403040c1c40400740e0050303001102c0d0780403840d0500f00040f0029403840802c1d0b00040d1030b2645201801d440d90010f0450585d50030aa81181d0740101c9030840b8208100c401402510360317410382c61b8664450 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 285808866 1250 285807616 285807649
    0x2a0d0507110a140102070f0606051c050a062a0306030606050d15090515010b030103030801061d150d020f040e010506070c030303020d06030807030c031106070e15070c08071508010302 80
    0x541e4403c282c842c290121a1840e401807800b064406050070000014a842e11500d84101140c40703022200003101c4181750f444070b41080181984201030340f946400b0300f40c07154019601458601d8030140b48c00e0304011440f400c42c0715a40000d002425803504208030760007a00b10a1144550078039400005140c928110b1540d13a03203110220b000416460110300e04090880c2403034110044100106d144544140518100ca010340d0750914503076652101a01c42e58001060454050041c110100c11070821000c11f142200180320a0b510308070040482c0022a04004210344805000080c100724000015811a0140c0401c4520629058030340c1c5c0c43c0c00700c03500584002020706801003503000685c4d80d01d9120b000111b420200985d542c512900e0010010010341000b1408112205038404040d03a00140303651007640d050300c84508000020042000450900441d4903402c00c040001e500012542e03031002009040070001041240e00700f00c1110800415070f5200410015508010005607585da0883d04203860b1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 285810116 1250 285808866 285808883
    0x1d0607081e04080a03090e041104090317130201021b100807030f06090b1003090b0601030e030706150807230d080c0a0309050f030f030a082a0d0507110a 67
    0x3144004201c0200355503503890641c40460005480e4201061001c48540320b9607800c9103080d200d4a07050308140b403e4401032300c40d096180420001e07040942c000700e80c1a0013400c0c00d0052864200e66800d18090458200101e1003d5814800865804100d004082d41c0094616525240940c012401b040200c0b641182001075260200b00094000e6003d0302c0740480c035880c2480b289884411000260940c0003819028000c200d40790035903284030b807140074241c0f64008038009442c0c0302c480c0110040c0882400c6408a80030421072100010184d1003040103600f918141c00070b442d49041110303414406a41d0112503c030300c0311940b400380c5070f0b20381501d0380c40d002d011079158984076010308040100340503d030b118110a21464002205054110381d8003001c44804803103204030000c40009054488400305600b20841c0d2043c000030024034080c1703407829400360003c041924022810b4010303100030b05003120901c1002c440050034185c0c41d55a8003d559120354281002050041481003982d41c0c0c4003150710107031000a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 285811366 1250 285810116 285810127
    0x603060e0c03070b22080a0812060f0d0312021201122d0b13050a0606170c011707140d02030405190f0b060102030409020d233706030b071d060708 64
    0x17540a000180038088140071900d03900c00314a000003990b130001d0f036550a000c42c040c0c00107402c0d00d4044030441550704041c100001d00c96a0340e40075a102540101100d801c0341c1c0070702400110601c0041c5050080c81200460740c0c070403a5604080b4617020016104641e006100341001c0304802030000340303004003a8041590070710b40c0c0e14620388050f08864850014a68000d40c0140f9007800202d030404000d403050b0720480003140d44d99440781c50b80c4030503800c0c0213404a007020306022503081e500c0c024150b110240e4180142d00c2400c48046032038907802110380c0d012940e80030040c4000d0042c1042903184000c45003004042441140c1c0f0307a15585aa000b800810503024100001c218be407007801510002c1c01020410b42d00d0344100716405001e81301071000e16182035080048500b00c020300e4440980038071412034451403042078010318402c5005078901c1c00192045020218030401480d481400001c601500b01050181000c1200420b0403402c140c65560500700400d40d888241d4078801190401ca40c032042070f9598a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 285812616 1250 285811366 285811417
    0x20102040b03040803100b03180c0a0602150907120c0305011107080f0a020a0213060503060907061e02070e0717061e06070201020c040c080f1608010306020c0a05010603060e0c03070b 80
    0x1c060940040007c1075001c0b051103041500d415010004444643c282c4400114803000c0c46001c0304644a1080168420f41103420265034400500303810400d04400d4a071180e031540d0a02104003200c1c00100c9604540c0d00341042800002c0c42440d140026018180780f070250144ca4440139409213203c031040c12a000100480060b0080000c009500c1e806084000c8030740c40b85650f10000d0000d4820301c2c1c0070380a107100040c0e040402180d16000e0f83c00030380300c4591062030004109081c6000240403c154443d0001c003140d40961440080d10818a82d600d890181480200d22641c0030070160101d0700038880364820b00203070f4140703610481e098001607581e03d880b0b42071400100d140010600300950014580a0500001903000c4026882500340c41107100881c2c407050080111010101c403400006a0ba00005000207480c5030014020454103600315441c854191300d480342140c090368400c403515a651381d451760f01355000740100c80b035421048000e0401140341840003c15441821340010300080c0c4a0050703481c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 285813866 1250 285812616 285812641
    0xe01021914010c05070c140a080601090f06061716050f120601170708040f0807061b03180201050706110705030c030a0905041a0907020705060706020415020102040b03040803 76
    0x100401440a0484080c5410000c0c404441c948090304507500b0a26500e01e068042c0f02110b21140d80201c000001d140b4101100c0c04c5503940c001c000398800e04038000010385101c10058680a020024000100080b00c02c12100c11501c00c0c3c0c1c005800d100d0344c0340c00d5900070107000c41401d41c0440e036000e018603124960a01107801d40307c0d882c00980024004166000580f003181184c174840d110a032130720b080c0190400c80c0d09480741021a116030004044000240004045c40d680e055002d114080a03400e144142e940c220a4480b101081c0f0f80320807143c1c5071038001607414004c1051890f0584e8370741082c0f0074039400084c414030171940041c1c1900e85804170b90740200c0320b1030200c1c0c00c159040020307251900d0070012001d13100d5001d800d071400000c190f0b0b0008109881c0c14400c08801c040f02c4a01d07141c21016180034000030b18002170a8000b076019681d03000480351a140300500d085485040010713a22410301095408503010020104216841804144100307002042226000380e00150010386981d03840428119 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 285815116 1250 285813866 285813883
    0xd050601050d0c05040311190b0c03071202011a01080106091406040b0307081f0f0915030506160206090c010203090d05070902040f030b0711030901050702040905030309071d011202010e0102 83
    0xb0a4039040001c2c01d90707135221014200707403481640d00120a03120541002159a01502015846130300c0305070801000031081d00801c04600c4039002e484c10003c1a8a800d40c011200100303100140c2d4440740028043d0800004560a0507402d0900a440e9418a44001e10311140b50095401d14002070107400075030340d81c0409580c000c00c5561000350392803428803030081002d0002d54070101801c4420b07400e5001d072411890300b2800d13515500e22141c40d01d03181502c130300082c02d40c91074060507550200134048041001030040622551090200d8180c025490400900d041c0300142800c11540040c0080e00081e03901004540001c4000c80d18111001d03210704000b4100805070303000031141403001400160b03540f5125132650480e03009031551106980c4000003030341e001560b04001c1e1642d8004009510705c80d03000340050989a40081d01c0000c441d095580d0300e40c9950b10640e040c141c25400618100100c414400d56015400190f10128485d94982210b448007034600b414000d05100b03000149042a9208016124 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 285816366 1250 285815116 285815137
    0x6070203161a070e09010602030f0f0a0c0b0705192d020f061501030b060703080402011d06030f180f030702010c2a0302010e240306010309170a02010501050f060d05060105 75
    0x20030303d00340000040d000c0d4a02482042c007030b40c0c1c850000640640044251041c0024a0002614105410344651880e90140c082901404151007445002c01c20940842c0e12804164940350b80e9808060420041c10b10300f440f03003504110b002900b2090741c1800d00760213180d00320300416000c440c0c0d601d80e07026414054032442110181c8980e40030480c3c0540140016103105500380c80400c0110030700010f202c0d15205050025011400c008046001948201405180030010325651103607510300400082c141da00a407100e107401e000130020b105040c0601c1d441d510603084082c00800818030210003050f244d005200f0080d060041c41c01a4000348416030b40c06021303404582c8203012000303240d0528003080311b00900003a4001801c01821607002d0508032074212180d50207200701441e0301403a80c000b0440781d1004108904041c0c5407a804d0000034040d0001c4403125084040f081c0e02c444c01c400c0c000f401c458050f03100504c50944c0310700e55082610b6040443d9601d030355071301d03002c00e40f60384900058034a44070310030000c07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 285817616 1250 285816366 285816413
    0xc0909030c1b090a1b0e011101140f0109061d06131121072015040821040b0c132706080c06160c031509050f0607020316 53
    0x141401c803542d500a80b00c080840c2e4a1480d40c98030080710301101c04002810365400da50080054056000f00d48205904805241580000c03040c55001801c0d901122043e446c000402818894201035103e032407070240500c41d5003000b00b81e1505e0000c00b00c2121040c3c0d80c0128114013004200d294440004a0f24582040b1806004c59010b515603844181d00c50600841c4100c030403029070380c0c08070300301441c540a28a9944c0761020403802001060502003c840c0c611058072079280d4044181403640e8550340b0803030141030078a4a50402c1c1c1c0ca59000c255000c1030040600c00ca00c41040b00081440328103076042865140c503180c030b98141e41924080032000ba00700c071101d000c0341c0d50214541d44004400001c60381c51a0002d10a42c1d42d103446040c4d4542e40d4000d110b6000f80d09208240c102030828400401d10b0780100400703400c407a80d03a216080f0812500300c000a90b5900c99404c2c50038080104a850244a80400201300c50704d40312100035243d00600d03440e00894000040d035030003802100342c5044842c4901d642c40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 285818866 1250 285817616 285817633
    0x1507060b0d12120c090b090301061a040302011209080d02030402120708010f140108330a09060605030a1703060604170109020a1212050d090503120a1503050c0909030c 73
    0x41582c216001c0002c4001464031208030304200454020404020314a481c0c11351003a04004050070240c22080301660190b60360b20b40041e1b510344540d0802e081610031a400c03551507085000046c054003c107108108007608010f0742d90005025041182e81e42e8482040040c0c0382c0d103031440098107440710610458a10710941c07101107040007040d80001c4a41640020400102d184030190382c40c0310700240704243c03013500081c100d003607010307001042d0034480e0484502c11a649100070748070700036110064032400b050982e41c0c104103003041214414040903203011001840288050b58507140840b0b4000740c0f07407040900c0400802c3c1140c94880507039010301070299903140c082d83c0040805000b8054000140d10070200b2180010320001001c0340051955005140010380d00d00d50481600d03240c1c00856900354403955180d1103400710b1824809414940707400c078501070281c10082510410b82e07000310010100c9981d20b003407c00000d400050300c00400003042d00d0310042551580b840d07605600420a0480440c041d5810 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 285820116 1250 285818866 285818873
    0x203072d06050a0501090e1b09091c080603060f09030307140f0423010504261f0e010e061501031509110316080402012f030c0706090803091507060b0d 66
    0x2034103890006d14104100c2d103142021a0f5108049155102d1201701c0341c01d10403079403d05181c055441018803048445144404030018521946a0f9085001031541814441f81d440c080c01000d07040380c580d204c0c40c800c50400b800300c01d0b00c0380b00192030041480f08201808074074142c5002601c6201c41e1242516448075958080051520002c10202e02061810348100c80340798040c409440c15600000360860b14100110080041c012000a01c60114803800c403030762100d101c40b87d00000c44001c0401010500c07106c80406182500e05c2078100041039040141040f6448460048010400c4030900e800b00f02c071882d040044041c80410740081c000b01d810a00701c0a040020000218012206001036028094803d44102c800050a0724020300040c1c01c00c4405076800390031351010401c50521008400401c030460f0030303189158021b10300250290044941084001d801c02000001040000b002c1c0d441c03c2c0e411000240310740420301a0324181403010a80800388110303039011558200001d06445580d074142d08 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 285821366 1250 285820116 285820121
    0x301090c0906140a120f06060e07050c010f0501060509011211280c0f021e030a03020c1002030715021e0f0301150c1205090103020f03010e04020a060203072d06050a 72
    0x15590701035071000c50a54440c24161000d404465482292403170290069951b101c851103180d1060742c00e1522074501040941150518a02a690a8403400da4a90001600e5420b680d0301c601b03003600361440d080040100035005070440e40181da0902e801e9040258083d0000000d0030b41e03010b01e401c4040040703002100d032611801000740d00703034075601c84030a05841d5020440d100303014a040100012403070503c0c1303001428100350207500900c1c103078900c001040060002c280342142450082c0d006030b04c080140c002508090307950b0950660184040d41c50038115072a50003031200d07a11701c1c0803115680000e0580120802402c070303180034542c503080c250b0b48201c030002e81c03000d40c1c000307010f48040750740f0308a040f582981c0035101f03001d5170030380c00501078901c1220341c0c2050700c05401c581102414940c0030488442000e540794000d41c0a001c18220300189400c0c140140061100d440c0c00030410756004010071808a80038059080e981200d120009111112140c60a00b03204001600100600e05203414001c40c0b000e02d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 285822616 1250 285821366 285821369
    0x1090c0e1f150201060e01151b33090b06130b0a03030302030a110c0a1b12082d0315030307020402030a0f0b0102010b0a05040209120604030c0302060906040209010b090301090c0906 79
    0x181e0017485100c0e200d42c40ca80c132040d000e205049902400301d41ca2801d0070300858450000c1d528103254180c1202140d1103414010780c1c41c1007054026505080e400c04603401300000c0d009021101d0408200406050360b440d810300c90050081403081005a1540c0c1500c51940c002006018001e071141800e1381e030300e00d00038020b50401e0b00d1120105041c8070107092000c440700d0584a0f00703171b82c020044c043c03912982c0725900c04a40c000c080c4401108001da000c600800d4400c07403180c01c0741c42140c44581d184019015441c0003150001d4912624609030480c6650142c0c101c10b4035041000c2100d05130402043c0800a4514451514000d4116001100704601c6000c268000f9400c24a0401c00f03001e0804043d00490032034035040502d40e40400000700a00c424209a805807807101c85c003404401144c88550030845c03400c0c504a0b011000141091416005c0590500407680c101d512440206600e04180c0d0000d0703007881050141e8094000046280c8000c0c0d0340035000500c41c983c01215442846898480103005803c65 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 285823866 1250 285822616 285822659
    0x10e060411010212070f15020c150906060d02100c050d030203040221060c0d060305390306010e04020102160806150d080d020702030703120807090801090c0e1f 70
    0x8020700010725400802c0c9000503a00c4012254500203180d40d80c182c45609003202aa04011806d1807640041040d1000700344640c01003000385072209001c40318010089000300001402c0d081036082c03003982e4446060380c05016504545044489001c04001c03921034801800c050542e20a00300b201c00d406405a0085005034001d80b01d6220301c098200311015498200b800070903c45d4015400680076020603009001c9465941502141c1181d69885092420500c044c000310302400820b0428030074041641085400f98000322842c054508020000b80c07211b005208200c3c01c1c0099000017011684280b04079104c55202c9503540c00c4103078846224035502c000454201142c4100110b0b60105850702c02d150341d000f554800c016501d000c10f100d6080020f90000700307040340c2501c1000c6000c400210440c0c9034403c0043c2658520940b45030a000080c03481c0d0b996807120346e09902d44512100455590042c54007651440340158505444000001010081c0c0c0034075203010450701600416080e000ba40e0344941007a0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 285825116 1250 285823866 285823883
    0x616030518090411010e01030b0310020409060f180c0512040b100618120309080d020c090a0e0a0609030e0406060201020702100f021e100507020309031204060c14030903010e0604 78
    0x140000c0c0b004600701a14042d11000552440404070340c0700b43c000800082c410f240c003090880c84000403911301031183c140c840000d50041001c4c080342c4014811a07000f03044031903007000ba4070714003125401b2400c6021009103007a9210002404040d01550440304110070310407610040d0700d0107017800c2038203060550b100e0001420601c3c1c0003810034454100e0360141c0d40e2601c034001c1d10f680b5118081000949040d802c4045c031a08a0b00041c00303000900210409031800c1d0040d0589420480400095a40c01888102c241d8600221000c0340f0000280600f456a400300300050110585e040998018a800c03070010b80c000d0810b88003113019541074015181c02e81c402c3d40c8000340049100f00586408100d101ca41005074002c00e002c11401c0740c001d50790784a08051100303849112485524050680f501112000701691001514640604007003140901074480452a58181424118014022040610701601000d920080320900c2c1200340203c0c0d00c13520740200200403807030040c1c00d003a44400c421181a00d01c03e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 285826366 1250 285825116 285825157
    0x33040303120f0203070e04091119080f06131e080a021023041e0203030706050906060114030a020a020c130c12020301050f012f160803161106160305 65
    0xc0b41802a00d005070003945400040e07820042c00c3c08001c0c4400034060380c0b10401032560118070744400b03841690310303028204011080c80c2403402c00783c1341c44e144041001d0143e1104c000c200b00605c610710a0200340b540802c4000465640c8250010002c0c0025006800d01c0800188040721a070001820088181004018030221125250b0b06010521b009449242405400c00050000c0d143c0d43c070003454402d00f4441c0350305148072a004a455900038490855a5968900c184420f000040251941c001402d01e489110615aa200c4100500000d00090010754005c100180b81e00c2c020300c070309a06250090601ca554283c1a101d400c0908552030458000c250082100340544180c0c0c001c4034169240646485200510301c0c00440ea80340b41d0380380307040c40700b0300401c00301060a5007440b00707500a40c0000018008403000f20301044001032541e112440c66442044803401b02c1d041e0329008080c041c1c0207188051781d442a000070a106100f0200c104d0078071510401c7e00700c20180c10402074040c00703013141d088900c0c00f07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 285827616 1250 285826366 285826391
    0xa0c260a0b0609030a080307090306050405030310050306060d1b0b0c0706030b0109081903030f140403080a060812030603030408070603020a030f02031317090607030c061a3304030312 80
    0xb44505003c890301900700721800b8020680c4c0c1c4000350340041d1541f1703000585030380c0c94481c0303002c5a1050360200c030580c100109110820141c031241070081c01c0c084002d45003506002c000500d0704450345100810352409201d0b42c80c168844452020010702c90280855900e00c000608192034013003030300503003011900d441c45124403940320b901450241c0e241c02340100200c1c01c4040c0e6440b030070007480f0421420075454140c134100c81d03501c5001e582807201221000c81d03400d080610b006441e14800070103000342c080c5091000c2010f501c2c002001003030100c000c0300066907521880042810744c0700d250400a140c0c4100d0a0000e25142d265004290b2a10165002c0ac80001321008000582c8403c0d41c01d45030001906031110042040003840b100900400707080e5a14040c1c040c00420310a07080044280d0201d880c000007041841458060350140c11070480444202ca103400f8002000c802c021500745407100c220b5002d031078104c072100c0324070200da0500c04000d6844030742da890028200c0300b40c0090317104441d09120021030788 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 285828866 1250 285827616 285827629
    0x190b0402100f020d11030f040306050601171303050c01020f2715030c0a18060f03060b0705060112030c0b0103141c09050402090411070308040215070302060a0c260a0b 73
    0x240d18194003501801580844c200d407541c40e402c0016003103010403c01800d102003142e0003000214401c00004c0740d80d01e001700026044000030142040c800c0321441c104105c5111101e001034200d94103050842e124103148005030b009001d0000d0311010354400107898242458400c0d48071845140d8958a02501031307400d02401880308400708001400003050022a1241c82108081c002650940c80d00440b0307540d0b0100742c4203124106a10441c0820321600700d1101070b580c94020314004d41289001141340920f265503966994205105410001c0341608140d010035104801144ad115005000041c03035584908105011542111810002c1d1280700c4000050315180c0c07140c43d0109a207610b9031103072586002e00b803101940c0000c411a03402a45d42520011503400303407014012850080e40c51440d20b140c1841405010f014410122240c00014880c0f040020303800103044d03902060303c8501181a0100010035142c006440320b61200c0c00b502907407400b42c0c8090807098a40b04441c042400c0c03003a04030070002d0100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 285830116 1250 285828866 285828887
    0x70f02031015030209070e04050f06130605060a2f0304060f11070501050901050d1d0c0a03260f07030201090b0a060806041b080f0312070905091305190b040210 70
    0x40040020b9400c00141c81c02d00d1509074000c2041c103051184d103403202c00060440718212000d503c0707004948107020340f90610131443c8504074240d40c010440d04d402c0c2000a507043c01000843c10812080ca604c00414034030008440d00310300c5002204503140c00140d2290358880e0414003802d000612085807070408140b1490200841c0d1401b400a00911410800112425400041c2840c107105c0100000481e0040c0341c0700d248468201c4100796234407000503441e03240c1091642541544145d2400500388041800700718840140c1c5101ca40c10407440c07107148800a820301481c0030094145001041480c2819019000320314064440c2490314965625a032400048070468066450340f50711140009000650788070885044403107410180d8104c990b14800f09e80340c8042c7d0a09100b40c0c0d00041500c03800c510300760012540144290900c007010320b09240202d03c21050042c1224684609840e0360400d20805028501041d82c01c42d46d000c925245074141541c484005403000c0b40100005150a03000600c01e205142 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 285831366 1250 285830116 285830141
    0xa030c051b063f0f250c02031626010501080c19080f03120a140a0f0902100302090f030c03060c1e0403060e011b0f110c06070f020310 59
    0x3030519564207104816418500c441d80d808282005005880c04081140f034000007210f00600c1e80c0302d15141100c860b0607080a8008414804110f070600c811001c80e1441106501180c50030030260842e0f800001d140c804c0c021070711803803030000c46000f0134101c0803074000c3c903180200c50040c050383c1141c0065141c00c0700c5c1c0c01d202d4000941c0281821000c60303d065030746859052816000014442d445496180c1040900580c070440ca03440003e4121480454a1400b90b01036040c01041008072080006000101390091a091609075684e40b594000410f0b40d00c0003106075000381090403081c45041c0041c000b94030000085100b220303008040c20b024a80020900034022002d40a80b4240e00c41c82e0828030380c0d400210240e181101e8020302015507007180d0020b48001c500680d80450001030041d200b90840340303a40e050601b4052201071b054603050b0040c41e8070410203a2441e02d500d4080000d107115041c080c5540c6200c0c0d01c4480058000f040c00390020500c4d461600841c10303107106c2c11980c2503c0c1d08032001c0b4075810 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 285832616 1250 285831366 285831379
    0x206060a1802090406050402030f010e15090c0a0c0c09050709090513020603100e040503030a1a01140307022b020613030801031e020d060903020606030c090a1104080a030c051b 77
    0x440c90810980c0141a880d1809080802c036170b0b840303000041c182e030001c03501103030041c000200402289104400380e6400c403d082810028040d1444046642800000c00c10002a0b40c001544000039100308016103080d5040703500c050120b525418100c000d041c0544100c0002001d021001c01c038041140304aa0050308002c0750980088016400d04c140c5400c000c1554801ca011030f003000459030608440b06200e1071185019603035a2400c01c0024048500c9a00d1241450304042c07000368032a6048040302d0311701403107107910b1a120340c0c802e02c0403460a204030300c651203001500c5a041c00d180c00c8040200344160b00640954400d40c0c0d50007100c02c0c2c14450f00d00060b0011325200c00400c0862501c54440300120030b440403404e1a1103064000c141c0089400000300c581c3c0b40d48050207070926506000b0150031200447c09840c0501e01e980009840c61005040e0300f1910340d030303a0903080c001c807041401c480050038403d0a41d05001510b05000d041030303492000a54550194040c1501845d5045030f00010f00e00d07009200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 285833866 1250 285832616 285832649
    0x50c030a0918151a090d0b040213020f0904050612150402030601060203090a0603020c0c04091a160c0803090a050d020a0317010605040905060d0816020a050306220507051305070206060a 81
    0x9019a484000152811040802040c82203031030300c3ca0706d6110a80034680c0a41a42080e1041c03048000c0440243e480e10741c030520250044020035001c85901210445003c1840d456600c001100810710100380511071181010011400c01c0704550948039500032000c4c1c442603a84e42109a88030301c00c110b00e059010811207014003200f40658050000380843c50225001c4d400c075000414121000108145c41c2946400140c004480c46034080381d50066030704075130355501c05402d4400340651041040040100002200081100c1c000300208128507400100b02d035580c00031a50044d4403a81c0195044e0005120820480d030038240d071010b15030480302560399540c038041c41e000000e80240b030080c2c4032aa208012111520100d0303c00b4000d08103064591039006a10030080c810801e020041d54409070003070f0004401c100a1501c22508c81494085641340c0441d0030407545800e40c100f00c646d40003a5070150702c002c11100040996801248108900d0f022500c041c0c80d03ca040044055940c410400c0a44007440d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 285835116 1250 285833866 285833879
    0x3090c04180b1308040806070806040b040e0304050607150911030d08130308090c040906020a030b031504141005070c030314040203100c02190503190c0503120403050c030a091815 78
    0x610501e114056414241030544074000641400c03800c1d08c41c580020030b210244900b614192043d580794403411181000004824071044d901c90141380700d194400da40100c3d00c0c40911000303002c805041d0700541010032487c2400e240600d0024003540d03c4901034481c06080300c1203203010b064640d001d4240b4540900840003240e07011140303824010a11303505030140d40340c005101d40f2075004004e4a01e10501d40503880380014072005080b100720f40c50301c6210b644103004140d22220f2428000e038015412040e16001035501035991460082c07a0802c20100714501010000c5c1254041842c501403031096400344068070800d00703031050861060324042e5042d00035801a04107103160354419940141c0364016211a151803a42d0300c10f0b550440201a1483e410000b0010b4414010384450440a211420040400d05903030300c643d556400350104140914a2080c00304061502880070b03108520b1440084a56030801100e0007000f081d00c0e40305441e520030071001c40c284d4862003400b9100c02e0024034600840014130f4242c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 285836366 1250 285835116 285835141
    0x203030a0216061508060a0606080c0c0a0206030c0c12040b0a030c0201110403030c0b0f0106020703061802090415050c031614041203020706110d09030809040e0303090c04180b 77
    0x2d9015030320803402c402400c002401400b8680500c4251104000f045140c000c0c0e245c100171000341010003c0d032034018140300e8a508650780301d07001307000155055110302155460310328100d042140690311800c08010000c200305180000d0030350341407280a650740f841da0900310143d140200c0c0a0320488590902c09103c1e0148260b0140481c9882d41c800850039103010001080d036940980c00c160b0000c3c000460f40c0c02030221114185801880900d000e03107241d8034095009458103044d002c028030b0b20307840b82030303901e40d50301e40c40160b101150300102504194207007882d09014100014444903189414800001c02c40c0c0100700c113030781c807401a01407004a07100700420100c80915105141203400d94080c40003184101c40031051040b0b9620a40061040606181001d000d00b0602070302811107910400f0304001241d882404082100c1d88062590386661010002401801c918070301c158061001200700302001d000000c0b0300c00341d15815202003180b19268030018400e40d5510b40081c25200c0c0300e0b00801d07101486075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 285837616 1250 285836366 285836377
    0x3060607020a03060c11070509070801060f0306051c02100804020a1703041e06080906010510030b2103090a0b09090c16050312041a15011211040801060906050a060203030a02 76
    0x9041041d0b440d202da40302d0044070b2401c0c40c1031001400000410305180c02c10003200300038042c2161412403914140b54002d1088005000d014208501c410101e11f916009801c80c40240c00004c021400745083c2860413401311071004001da21a00e0001103180803640203540d4180180d0b0054410024079082114070700e4030481303c211194091000b040001100e81d44e00807400000000c040491740c1716460024001c180a40140c02c1d050700e50000c0004110507503820126a60f546400c0c00c0214014002c980040c034814044190340302d9014040b600c0c200c1420000c4020203155a0494180d04030544441e015003080c040d0b0407885401840d00400700301144040383c0908001802e21441c04600d0895581e0f141c25600441601155150b02c00c060008000710007000c03a2081814007483d01e00c52918000014140140303112003818400d6900c1002c8140c10150015000014410140c555039503031011624024801744c403890300494a404000b00351442c0c11460002128003580c0110f0840d152880d80d0300095002b0b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 285838866 1250 285837616 285837619
    0x306150e1c021e150c060f07110a0c0918030921080f070611180f0105040f14091501051c020d05010b07050d030e1509030d021201031101020307080306060702 69
    0x41c200784034016038508800d0001840c1c1104050900414201481091940b4510091a008041c094480d150200280c2e491b03010780450f00419403034403071200c00ea40011120071381c1c503124011169000c05000368100b1000c1216000601001680a19a00200d620040403001000580c10040030042c8168500c502d00004680d204480205042e9548081031030b406018060160b65000c183d68042c0071861189895488140c440756142c490300d6104503202c98462000240308200c070f4000110164800c00a442c00361464404d0402c0c4c654440503a501e9400008030803e00c00c0c0c6141d800101c941e00040030302c49032883c045c0c4525081040c14041040e28101303c641d501d032450350a00c620600340f006030150324000c2001c00702440d41c0e00b000e410200d082440c80c2c5010002e05003000003590b4265030005801c80e00c40d102010071803403500c0f80d00c1c403681144504926504024000701d139407160841c0000907503040f031b40328040029000103554010790300c90007103c00c040c00c4900d00340001062414032000402c6070070310 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 285840116 1250 285838866 285838909
    0x30215090a121104050c04150c120c050105090c0607300302030f0601110304060e04020d0e07061e1b0201030b04090503090f0f06090f030f0714010306150e 68
    0x654020a500030081e80c00388080c0385400c40300e54244003d21280c1030000000381d03000c0c0b18034a40340398000c016100e5485440110001015100c2001d0701c43c0e030707000100c1d6505c004540d030008820400100402000b80098075103510b0030000c64400180056135501b00c81d03018001504044050310741030902401c110300c00c0f000e0101d2908065807184c41e00c044840300b25441c0c800503202c2c02e007042d00c03107503003d001030076541070101c1c1480500794440d00006580c03c0721440c1c0350441d012480100401d010780520b0b03100c25482402c21082480100011840009641d559900c1c541e0003084100d41032910074248907042d0202d0000b00f146040c021000e440061500d00604010696400b03010100d07044401458080d583d640000c600045103103400b8001351450f90b0202c401d4082d051044000408501c0351410451180300f4032202c01e00903440138440c0846140c011000d0394109581d4800003111040c0d004e0003140001e10b00040400e481c0321400149a1275426580d0300362001524000380091640081c24003400ca49 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 285841366 1250 285840116 285840127
    0x130f050703120f0801050105180f0f04020c0304030201020c060f040614070f0b0f01120c1e030b010f0504050604090f0201140408030a1e0e0d030305040204020d06060c0302071e030215 80
    0x40c0c4000e00d0b59a0404190795000030700d5020100280780c1501078010780d04226040150380c3c00340070207040401c40b00c02c0c100d07000041c2420301e800050b007000380c0c000900d42060000c07075a401d0a960200150048034001c0c0c0a031165410b8601c10043c40340304000c0b010001c901c0900c010300050340702c1c41155060508401400789414420346480b0f03510500000304032102e4601c2001c20100e0350160540900408440120080d110850307610100c01000c280201c0b60003039040c2c103040070b9403410282034000454005285401d696100c2e501c01555a001d03000f00c9004030304200114046062030b104103070489402c500e40c2065484903a00444140010741c1b0008000c4034140004121400180001d0860600c0c1d41c0704c55800c0300f0009845084017030000311110074001400c0c2d1048068a0751440b400ea55036044c81c0020b2159a00e00c0041e0080c082c0c3c0c0207200380e1520740000810501e4004500808040c080d408540e1440c0e52001c03c6109003036481c2c0c039018003004a90041006042c01000a00d015803002945070420 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 285842616 1250 285841366 285841373
    0x12070f0f0e0a0216150e070b090102030403030513090e150c040b070f1b060309170703020c13020c0105070906120903230c1203060118081b1201062903130f050703 71
    0x4174031802c4070b850b20f59482c06c180c84d40110410813003001b4118001e80c14240a40000003075201c1c01284030140074050700103021113000c1c0242403540003926200104011540004a003203594260303503541d1341c4403810340c03c0214800512013010340e012100d010103194907140455550301c80aa1410f401206c0e854100d80d800b680c00c03413011441c5c0c00a0300f10707a640000c80381032030b0408440d82c1080045800050700100b2030000420b034003050310b104002c0242c619188840340c91405100900c0b1f001100005d6500e400180400c0582c0001403070101ca0f115a560120302d48072000c8201109c1080c000100451254000112000340e011008481c1c640c884071075600f4042c0000c2d03601d09000312205d04001111000041011540c0c20000b03040300110b8010403001c5a81c01d100489076203c00c40002d40555041140d95030754640e039084d51005800790100001e00880d503950200500195940d03201000e0242c0030f8100d922143e01c5401a00c0c81080e50790010703480840d20344c8800c011600e440e00c081e00d003800742401c0072012 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 285843866 1250 285842616 285842633
    0x6090f160605210103060e10142205072301021606140d062c010f0b07020a0b0c010501030203011a06070204020c0f15070905010e01082412070f0f0e0a0216 68
    0x710700030000860140e0218496908251690800443d96480e1541c9c1250403400c0c0c0341c1440d4400000c1010030714801c0212090618011280c0d00280070b40301c0d2400214599024502001030151410400749000f540f02005a86551802d41001081c66021504000701442411207200030312022007990719010488412005a85550f04400010015150500d00c840003140148100d1100006090520b506044200d003088516201c5c40034041004031b030303079015550b85d680304070000c141404045546044110301c00303010b80000d10050b4400d5280500005400100c5404420b400b00c0003042c0c00d150110a900700002500400701c951f06c1c0348107140c0901c4152604220740d81107100c1c0b0f003405141d41e28207050001c140c1ca1a5402450412414081d050250303608140c1c8141c000143d0360f11003403145009444072000302082e0003032a40c088043c5420035912100031405505135881d2550750340382d01d9140c0154004180b43c500c14001d81c201080d0000701c01075030542c06407174070b4051080d0907980c003001a1141c428 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 285845116 1250 285843866 285843869
    0x300c1502090319120503160309060f0e011406060c03040b071a0103034a0f030607090306290d08090415080c011e0f0318030206090f1606052101 63
    0x10000151501c03406118004d420a040c14215141c95440e40c688452588550081a80c143c424540c4904440c0308010540e0401c1041c4c40c02c2d00002c0000710b02c000740380e501808445561100d007225000101310340303040030384c00c076051000b441c0002d41c5031074035120389420580c3c8120010748e40750f00b003400d214080010f81c140003070095002ea80d40401d180c0e01c101e055828a100c4200320190514000e681d000881d861201002e2404800c4210740e40308298400400c0d801401095480c0d814000e1008010030f80d50018810401d490294400700081d11014240340300860144a03070040c01f10200c0d5803042c8600c0e02c1940f0510f050700c2084e009003804000e00c00300d0240c4901922885251140100a22088508002e880600542480c0500e4800d01810441d4a43c4200100c0c07101013104c6d88000c682ca241c000d0700a100402002c44020400701d0341070800035241c400590f880201409020034981c1143c1c0d00148180000c2c0503076014204e1640f92113400e42d110b500000000896070811a0070008511804a4050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 285846366 1250 285845116 285845143
    0x30411011209052d070b031f080c04020904140c1c1a06070c03080331030c081b0a05010902030c0a080303130c090e1e07060e04020304110904300c15020903 68
    0x80c0c907070908d01caa41c0708103e01d01c1c48a104014a055041200840002e040d03020010140d80c01030b41c81d000400420058481d1254803503d00f034040301444000281c420040103e44c170050301c1e02e001c402c1c0340c0103c1c4080ea500c060b500603000c0108201d03002c0514040c8010001d50f03204000c0072404555a50b5502d43c6034100b1240f81e0844500034140d252405021610605040e84040088800c140b2613903016040b85111540a4419800841c0390a13210000014102d4500c0f000c0003241e0b2011810b1401602821040c5822800303030180c450360003c0c030b080c03807a240c0055850307010245003076540c0d0340826007440030781d903009880300c0d00b45820002d80000a0311070b0181050303051020b400400c0c0d000e09500a14208d038404c0c0d0000d41d2000100304096a8402c076901c1005900f118056941e80b5070382080c807840080200100e51041402061100f0000294400c1840301c81d01940000e805004000016002c6100b070414004a14012446000038404401d060784010b6082d0f401400c101c2c400010030310780300c075211042 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 285847616 1250 285846366 285846389
    0x302090a0306150b21060301020c0a2004020a0804030819240b0309030901051b0607170f060f09060a1a25020d14010908030411011209052d07 62
    0x50350391501d80f03030000180103456183d92a0600c0682c11481c0d01101c41c2e0b828500217400804180d0070359080d0120303103592840b00100c64a03542caa003071200c4805402c200690f00c881500e1541102030402e4001d8800350655034031141c80c50343d501d45040e10440c00007401d040c41d0000d44200f5521012051240070101d0000000e001c100c0076008a40841c2012280c1001000740d50500030030042140010880389400302c2031904070707140d1220101b48114104204a80403a502406003080f0b03206a1010140030781c1c801c0c1c0001000f99032101a48622009030540d06950004011005203169003052640d0a4000300301030510040186d0300c8840d04c0c0f544058411001d99034078005040303401e022550111420b078920310032a0584c00700c03880d07001a62080c1345a10080c080c00c145284640580f00030750040c188a0b8015404903640e286c075140491503110744807841e0740494001e0040c1c920b0050303240700d082d40141d0b1110040c8440c2d5140d00038024451400448140c030fa51241c9901c0030805414000ba4005040e1403003003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 285848866 1250 285847616 285847631
    0xc0303110d06140102010603051f1103090609070b1606090203150a0b131109100203040f0602011b180b0309010209030f0a06180302030708090406050d0308070f1103070b070302090a0306 81
    0x2c0c0040700c10035643c182c11681050414800300c1c0c40400c00703074413100300c03080c0351040c0d540c1c0d101e07c5c0c3e40a4085802a450381d6080841003125101d804a40d15104080103802e48458585440b0304030017074003440712480d00040081d0000400a02c0651100341c15600017801c50f0b691007002d410040c40c4d41d2040340c0301c0c2c1c91140c6404d0300350500d060495071901c1c10044000107108a42d072503003540b4081d000780c071041ca209000305038135a4001070082c400c480140c0700701c1e031429100b10344540001e40641040004002595120554802c10394411101d0f0031010701411805840b09141594082c901d820142041215540c20854203429a408014001000540394090408120039081000031a0b004240d241100c40005104000190340813044a12203a03009007060345411450003c90010f08464000d1500300005080790824160032002c054032503100d90791035180c80f0b000c00c00c00301c850140c00c2646510b00c2e401400301c040040e441d20811540800c80d46801400c1c01e00450008403841c0d281c2d0300564415590704070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 285850116 1250 285848866 285848879
    0xa080d09063f09050601030302060402030709050c0304060c4a010215100302130236040b0f04060b03240109061805101101060f03030f0c0303110d06 65
    0xc6141041006041555801002801002c0c0410b035481c01c11281c80354034402d84041a90750042e120203811200701c1d0786941c1c4901c1e000e59a50401d44003a4841e104014000031070801c18007441d44a00c0742822858115200e941c1e901c8068402d481d07240c0140404c88445042415107184a240c0c150788149a6445096241010220118101aa907800d40e800c04a0005183e41c0000361800300c900d2030111100d181d0380c0d00002c00da00c058145c2000f5400100c0705250007029034150040c2c03014001500380e0002130a141c42440c0e1000284d100b9800a650f26512240e01e145865485803054000140007403126000c18000142101e0094003c1001c1c0000072050100c0c40f2109100040c2000820360058005030642c40060041180761040108001115000310140c0b002c44403403200900e00075103d11586a03550034090103105c1100c0f0012581d600c0c1030b9000500700720951401b0112509500c668403140d00450003100d424241d000d00f6800d0503100c1030b40b0f00074200450001c00c0503980c00d00c40000c00ca8106074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 285851366 1250 285850116 285850127
    0x3210c0905120d05180d120e0108010302030c040e010e07120b0c040b120603190b0603010e03120a020c0a0f0309051305061302160c12050606100207090b0a080d0906 72
    0x20071841c0112596407010707011950000d16034814103420700f001c03034031024480d48000a000c4000317100c40e0001010722481d81004100f001e030500821054840412914400004403a4181c0c01d01c0041c0d850f5120986c10002414954004203004030f07403030000b081c0c41002549003454400580e04c542011441202d42c5001d000c0c20044080d08512005506403800340750034900c0c0300f00d0080001541c842041100411030075502000b0140c607200d0145202c00364031200f404c242440c2002110024042d508148602d200c02c0c8001c070481d0034090a0458056807902e91509000c000d400c02151240c41d480703030200b00030214600b0038411422074801d27507602070300d1401c28060000c02e00c40d00000f022103505000501c0741c596030b081c1e041e440356088a0340040c0c8414007002c88880b090540070000c0c01c0740c0245a0f0114003420344c1c07a9000c100034068000c440483c1c5801003400f040c030700080c61100c0140c20142090101e60103503000070440050040c004840140c443c1130140c20680707220101408107c0310302e4100180d54000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 285852616 1250 285851366 285851369
    0x603050106020601120201050d02040e1306060501030603080d020a0207180e010b0105031501140904020708090a17030403320f010e0c0102120306270f0c070210080403210c09 76
    0x140b02901041d4034080311100c29444041d00281440004204500310b08003541c10f4078010080c14140840320300b891203e0f2800e02620719000d0390140e0800c0404038041d4040c0c064003080b00d40c090f80151a192500415200940110101c041140507181c8000b80321405c80d01d100700000c6140707900061034003428120508403209030440d14103200e014010440400380303420004915800030300300030084100d50181000e0a119100a1543c801d1000c61404144000da0000c4d03d01110301303480082c0703401d0b00d074030b084130000c03a032a401c4003807130341c01007009000086180d940c200020000303401c403800e405828525032001c40100d42c00040150701113900e000f160700302401124a8000e01c00007a207103502d80f18000035103594a402d41c40d42d44810001c040f880c16101d42c842d10942042624207030150005203201a014180180d81c480d10300011603002c41c1b44141804110780e055907004181005030b107100e49003070324900c10080c004d6003440041c0c200c0c007020414a10340c0c400c2c0700c0881c21001403d002c0e031130000380140701607 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 285853866 1250 285852616 285852629
    0x100c020a0b0105040507090e0c04031b0b16080d090818010801050109140604030203120306030d030204080a0f02030f07080c10050c06012904090507090905040213150812030106030501 80
    0x51031003000716a042190506551064501145940c0d074141c094428044942c00354120040788000c00c421030140002070000e0781d1081400f00b48407100c442c0d04452000c2e035800340c0c01e10448208405000350020b0785003030782554801c2d40c242c0d081c0b100340820603003200e0f840750007134900b4000000c002420301810340c1d4481d4070383d009080081c42c07541001d0000700075103440d0066280344220707201000c885586003000d5030f008590090407a40820b010312b03103030155030300f058401c2c030301174415600c01d00801030003070095505442554005000ca01203644440490264954042ea0540203400e44a21102001c4c4050800740c4181001015080200c2e0b050100201201d41c10b5000c1103004d0140d0742e50301102040f520304441c0c0301c1e02121007400792081040402102024481c3d8501e0b4002800640d0012507000240301d07941c2a201e680c20700369140700e04426140e08032002513115807030070364903540e0411540c4100042c10040900d840c0e8946c6502c0c4c3c851a22a0006082203254800300040003056070500500b4054107a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 285855116 1250 285853866 285853873
    0x9070309030206150103200a112e110d0b0307080a0f020d050f060f010503010b0d0305030f2a07060b04090b070e01121b1101150306020304020a0f08100c02 68
    0x1140c0c03002915124003400042c02d80401900c002d050f03030b210340c11190b5050702d00c101003014030010351f003070310b1080d488405c540d80841c2008240d000903080108480c7c0780f008580741c0900250300c1c0310341045452620248087c1c68907607030716074884529110724090140512540c000188040b0300504162070203034198400046c0c4d5225147c0400081c04240b09170b001644d05407481040d030380080c540310341000140d141c082c400e441400c0c100103140c000d0302d000c1412941c0640c000c00141140b8424880351014520700a00820303410004200030880e4510300f16130021400480760f0580d50854211004084200d21603c0e6849010070784800780050b92050043e118000c440801c04e95460b9502c041c2c8240000701100c00717210242038000d440c0d0f401105583c9100d69000410011080a1a04800c907080880040d1001404130552000c2078601441240c1132504030808480d4218610344e11080a035000a10884e005465101d0000e046007564003005c000d801c0305400b030501d142000d03240c1d20886418002003c210360 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 285856366 1250 285855116 285855131
    0xb1c0c05090301420b070b010905010f060c0b1008010e0307060f1a01050d0b030303010608090c0306010e011401050d050903070b0f01120b04050c0a0b041706160c050f0d0806090703 79
    0x5110300180d02c0c0c0745504103100540034000795144c80b400005130b12803072a4000003e00d80c4200145400c10318141c41d01584c003040542d80b0f6901c90341c1004070b1401a131010400310b4219030042008080b03c03990003401c8040d4980789940b207501c00303825202c07a804606103a900c0450aa020411103000c0d00d0882e001a000810051803075a2242c507601c00f03080090b40c10300100041c44429881640c00c900e24400c40682100d03901e5030b5952000b402c07a6404c44642d8a180161100340c0e9141c503020034a24100c481d80740504546908229001090020000e155418030004008903c1c5401c00341c000c00c0c0c4aa40b6400266403a41e44505101095460042c0708801403800c060041c41105650541c00c0101600084000c0c400e0303441d8900a4074081c1250716160b8025070001000695070300b1440207006440d812082e00c0c1c2c48802450105544034016600300b450075110414020f0210b02c505010b0042e50b004608541580904021250510811100840005070b03410b0401021707003401c0045c00c0c4c102c03219103000c00028 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 285857616 1250 285856366 285856421
    0x20a0c0e0903040f0b030709061805010e0303120a0203070810080607140c010e010f11040302180403051b06070f080c0901201002071a010f0b1c0c05090301 68
    0x8502400360802105460340881d454000800907240a807880400c0340005940328401240240c108079840400242d00e1240410458400d0a840510030444081c141f01c150a0800664501c0403070703940c258261000384184007001e0080e014560090204070801662401d00703140042103440001c0058580b001840c1c400c0101510002e4040c4e03118445142c4003401c10300301000800c9034440c401e16091691308000c2424a80c0d10194040c00c0100e0800d9000c120b0003058801403c5540268030010b0361211010b028403442516805445038014403030301d040c51400540300b080010500607030462000c1070f4020300c01c000b330310346c0c1140c0b0361521407045040000701d03807030903844003400e5201d010f22130390400007150030300194000d20105456040942400b030703911002106001400a401404041d10707615a10318407480181c0038010614140c520905012503400d0a107150070078950f01090888071018141808000c005000b03101c1d082c03407100c0c07554803076584021903010507003525800c211407031707407080159080c840c0b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 285858866 1250 285857616 285857633
    0x40b031914010204030c0602060a0515100e0402071a090d02210a0e0915011d01080106050a020c0306042405070e040b0a0f060810090e06040803040f020315070f020a 72
    0x41544505081c44501070091018003901503984000c100e0706403940086100c980224282d481032a100900300040c1d510b94498080045103c80250742020300900035403603440c40b40c044400c04d21400340015142c40e801d40d03a8a192042c03c00141200400c2800511011078805e0204440e86503440c4002c1008241048803030003e40848104013840100000320681e07510300a04820440d440d000746407081c00c0c0340c6040c0a140d01c0103c500040d000440d41c0c00c0c0d209046078280c1c0303d1401600107a54907044c0d41c0c00d106d01a030301c65000c00c09450a5102e03040b00001d85603000c2001c284101e21500b8884200c0b00034680c129454004e480418208500300002c00421a81c062800c42446a00f2140410780c042200003150a0742200d8000c880c59502607131012071501d4214800600803d10308482110700d503601c000b00003c80f0205c940703900a47c0c00c15000704000c0340c012409190410300980e401000c130122a40060700d0658401644c3c10b01c00c4086003000b00d09900300c0c00020078147c3d41d0000d030a00070015600d0250 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 285860116 1250 285858866 285858913
    0x17060705070302030927070513080109120f0504170c011704022b060203010b040f0501050408060402241b01290405040507170106140402040308033d05040b03 69
    0x950403000600e40016520341b004405440d4405415040b401d081c0c000030f00c643e210a5030403025200852000400c0241482041a201c3e081182041040c0e51088222041c801c070242060030050f0034400815026801080c1109843c10000206111030b86900098070784056609400803003840c800401000d616011f61039840700003400502411184488140c07060310b00320a07809041c0c00e10210021560304003400080055606812040b040039580d6001115288168003d5030b1042d017001001c9401400c0041c1e0407090505605e800a18507650b90780c8040c45500011004408138031002c0c0701c81290030342032249243c0c1c100045030800c3d440c0da03628110300c400148044854011980d0b0000101884070500101d00a061280b559040c00090502d041e4043c0205010b006802550020f908086113464404c8400700ca07488030f44182181c0d03903151401c4440058580e4a18110307186c0c0300d20548009110304404d54187c031907070070400392820401440b04448002c00407034081c1d80100701180d00445290203952 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 285861366 1250 285860116 285860119
    0x80106090b162102010b030613030207060302030a0f33050d0308091014180d0c1e05031b0106090e06040206030405070e070f121b0e010201090c170607050703020309 72
    0x142d540a0301e1904401c0e0b08200f884034884000d01042c00021103606402100d40d00004030112016601c40181410400240160003405a4000703a010030619000c1c0e006144d01114190000455440ac40a0282540e03c00002000d0805440c42032005802e14960391450034840418010b080504041c00b1271444002c0f14406414824144002061010300b00000101c1142812003071048400000310100c0311074094800200d0410001d1482316010000580303503000d0840d903aa0b442ca42c510584070700d0713400c51a81e902203401d2200080d000c0003041d01000280448040110301030342000800802c50700312600303030b005948004c2c145036a0b02c103036002c000744c0f0540068040351400c0c1d40e1b4503145170840c50501d07141c1c000c4c5c111128840810080c0c3c0e07040205d404000119031180d0340c0c070001400b2131004664200440880600c0049020340840348240f8504007000818000080d40ca40c60740c40320100c00e507043d404041981901403442c0c24500003403224a81142d46814071500307003441130758043d48034015150000d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 285862616 1250 285861366 285861397
    0x16080c040908090a03030e030d0e010c03080601050c070e1504050603070303051b1c1d130203100f170d02070608010311040914070f0f030c1809021f080106090b 70
    0x41d0030311030104121074a01e040103281049260340c9150240c030b02100d80c268144603004404402034a00c0c05110052090007050f9120480a503445e43c056030f040c800900218108a01441170141c1a5001c10100024221503600b24119103803554602c643c031100a00101c0c040c41c24038091002c10340740001c0140659134141012500d4a030307180c034564030703140310b00704107000d0b522a000104026188010360f2560072142079682c13000c0818018444030442440c10360039900802403c1c02010041d600e40e0182d034103d000c0c00300a050683d5240f803c00b0324031042d0b80084000d01d00d0009a95492101000911043d14041c0041c0c400070b4607110028100f800d0521018280c84148825494141c3d502d074003400d0041da0007058280c7c030040346a00f1a0350b900e800d00400701c5244c850800482d2081c03020203100d08481c0c1c010203000b1682d0504a1060344040840d8084801544811a06005075104003852544881c440682c54031500da480d07005188107410303030205042c846480000c3c4410300903402140d0020b200c03000203 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 285863866 1250 285862616 285862631
    0x5071208010f092c010e0316060b09150d0201110f0304090e122212081b0609120912030f03041a0103080f070f0602040f0810050f01120c120308070216080c04 69
    0x500c1c0034200b0343c0e4880c0c0706c3d07001c002403c188202003090716900c500e025200400012450b80140a64000c007500c2c011011404105188128030344030b000e443c2054810f02d0100c4a9030619600d46140c06aa00b1121220b50004181840500c031b15108510142846200400c40f00b907408040300658860303464810041403c4210a000d070825151034400200406422507002c00c4290602045640040520f0008060392820700c20308464005409401401550050414481e1b000000c00885c0c1c00410441e0f004107500f0910032745810140043c5c401030348020503040ea28a041d2411007012212102c6008641201d0401400840c0000060701e070b01448131003803950350b600c1074100004170390f03400000103180e14000500811b41e4040e00101c0000c840c1315400311907800c003403045103030301b5590300b01d488440100d0048010400520a80d52000000e4059000aaa070944807908586015160003065010542d0b010500810340da041007014880b0054004420350681850003180d10f0340050b4094911482c0c480e4076 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 285865116 1250 285863866 285863951
    0x131d100b0f0403171b060405030306120f2b030603030504060c1a01090e0f150f0c0d0507020d0e120d03020a0207090906060801050705040b160305071208010f09 70
    0x44801568104400a0131101380740300c10600c0d98014081282c1c0c0f020f8400507598440c0b03000030300f14041d50b405000395065139a03c800380030315004840c121118500c50b031007260742d0000040c03004c1c0e0881070343d019500c41d0380021030b1f6560007603c0c959000e000802d86010810030101e540300d41a541540c0080c50041d00c000c00d00d08082c0c03034801d030074480240b0308030085000045245143d8000070ba801d090106440005280082d16078940c01007a008641c10b800b0f02c0d00041031b601c5048081c65001000e6010709040001540c0c00d901200c1d011205500540d1007101c8803a0b4054000808140d003080444020190b404400010358a07256009200e00505401049400045009100000107085500c501b04183d101d0360401201400710b5200703c55a035440c040100e90018030550495054074015020b0780e16180d15400c03601c245c0307858070805504201d02840140e002640c412540100f00c00c003940e841150354101004040d8030506a841001d005103001c0b0306841741c000003061032000c043c103001610494045800c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 285866366 1250 285865116 285865147
    0x504030f0f0605070e0102100e0709020702040e0a0326240a08160f0806060a0308090a0f0e060a0603020a0e0d0206090301050718050a030c090209040b0303131d100b 72
    0x1c80108400c0c189000c0000040e8412001c89108100340c0c00c0b01c0f104442e0507181c0d8115210580c000d18a030f001981c0602004481c5e400034844244040d100182d01d54400500d1070404000c55402c0740058011481068540c4150300000004807500a2044483c2044426050f110341955a00340e1110b2210300c00c0382c51a0344800040700140f034540c041d40d50501c44040c7c3c40c2140a0940a0800d110701d0808000c00d9a4a0000b829881544040c0c022800c981c03c42c0c031034800e950040380c0d13865403002da0a41e000c00c14000360307442c0c20010117070b0070b80c0c001880c10802c0400090f0707000c6802c03000816106001c1d0724052503102c410481001000d03100720240c490700340089043d500c1503120b00d5815600b03140034440510342c44038066540c0c6180100c6c4400594640e020081404800c0c8009801c030400500180601c0056500911650000900000c0c14100c100301190551300461042c020341d5088003020010341015802c2c0c0e446662a201294002e46440d0340303180d91103a80e501602c000e000d0082519002031800d02c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 285867616 1250 285866366 285866393
    0x15060e0a151a0a020105150603041b05041a1002150a02070c2612070c150c0f0506010f0b040305150c211603050f07120204031713150504030f 62
    0x40c0c2d000c80d0401c442d80450030351030b800000714030010340c40c0ca800607044d02c4140c5090020040010450307407070741e101c540710a0b003601348400700d4002d86282c2117400100e0303a40720b1141416000c0000c5603101440149010002c41516074038114055400200c0c04c801d502401811107680102c48078030040e15000c003401d010705080792580200344900c1c01040c1f41d4041c450b1030381d02c0c6205001a1400c0710851000c100743c01ca49806180c10051840001020a03c0303501c8007452070415440591414414454580c1c550541d000701ca40c10640e901d4200d40010301035202000400b001900203000c100d8a0035141d036485940c0c2e207208044c4950000132690104040c505407608950348401c14100031f401c8160b040841d0316040200303898103020313403e500c40048052400307402134a00c20001c90001c20034503958001c0a45a41442c1c800400350994208000f10001c0c0c0c240380b5210a07000c007104c126440e04c89034403450110500d5600400342507140280d042c1c85580d403020496046e20392000c11240622050316141019140c42e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 285868866 1250 285867616 285867629
    0xb090306240904060902040e190201050706270c09020c19081308010c0f030c0206060108150a0b03010f05030a0803070f0c08070305190e011719051315060e0a15 70
    0x502c020b02003880074036004131100300c4c001c9804001050341c400f00c1c05d40d0344445604030807200702441c1d003120241d8024005813480d140200300102e24a0f80107220071114401d00086082d68001030001907051250207002c6602409264804518210020500039600c5a4004d40c18403a0300b12028500308203c006400e445869900403e0140d0f81610f03554294043c14540e540c0b070300012601c01c289500030340309015820740240c158000d491141c54050045910301c2d001001041890100f1345443e03482d89034100100d0050046c00b1b4601d0b01c0f54100014030051405c0f680c4400e2295001c400c0610100d031107a011030390092890b01f01180621a000010746046004034005000c1d0f600c08500c17070040c1030300328000b8800000716100c00c00d11103040d4101035424418484419001417103422607039458465100d4581d420814a02650300141940785e20306094460031502d01600001c0c5100030410031554003800d004a14540c0070a000c403c0c20300111840188004040d00e5080780c413419103a6a42c1240602c2c01c01070040d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 285870116 1250 285868866 285868879
    0x504020d1515021209010503060d0303060503060702101103040c150201090503040909030e0a0f0630090309060201140a0b0d02030601030b01050f0405040c0501051b01050112020a0b09030624 83
    0x5541004007904242024090058040e005110005840340d00031601c5c00203050b11101c0c10368a924091042d81d902c04038007142419907491011070a668200a0103110300459401000e03140c81c0d880442c0291921020720603502907040c01440002f40000107a5010341c1d5018080034030006000300124058185080042c000340070000740030440e4400c54012079003090203030f11000c04111f00e400078010408110302c950f1452400240c8144070652203001d031150026080c00400040c6100d40500d105c2001e00c2c540030b03094003540c460400042641281c0f2010062689000820040e0194980f40c0fe01c2d0313000804c5083c09036943c00c9641c0040d555204441e140ba50040c00325441c035030f124034241003614420b004545c80703290f04441d0700c0350780d150600440c1e104640c8141c01c8401d00e49031034010760703550b000000c1d440c410700c05140003001005030901c40c40c2e00802c0321119a800081c0c83e401030222159840c0c03c60741560904201d845542c0d2400615150851201110300c5034401d11071122007078005c880110303075500c003c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 285871366 1250 285870116 285870119
    0x915090c09090a0f210503280605280b03040b13150e1f0204050307030204090204020705030d0c0e04060302010206161206062705090406020304020307090609090b090c03070504020d15 80
    0x10ba01c117050300e911501c44000e4451121003c0c3c1603c15010486548800030950711101c0c40c4615a20b10030b19a42a4208000c21202c3d25440050380d010011620307074440440c80003854900040014000c0000c0800070349076032860800d610b5502c1c81000050080500380355815514040100000c0401c1407090741460030009000051019603c03240166402002141606d17110079107d902c1d8400c071401c0360402001020154503580c01d22001c1c0c41e00c41e6041e6031150f82400144003103001800103120088120301c0003d00000150b4014050345092902140564500030007800140d80000301d06400c0f607058890300511505002003254400c00c5021103e50a07401c02d84c00040b03440d0818000308070300d500c0c24044d010041c4482440d58005a80d8441e50345d11071048404140071500c2a40115005400030f02541c0d803003502c840c0042c0640b4210307031201390b50a07030700d900c548284515914440e030002c0612010308003100e20070300000d5a505aa0040602c107950005820010103a958421004130308881415080f05 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 285872616 1250 285871366 285871373
    0x120702121210050306010f06080603030910090e10051804020316090c0905060708040605070c05040c0801140406030507090218041b020d050c21120c030915090c09090a0f 74
    0x204003036603400c4404110b404041090b29002c43c50324180c0b0031406000d981c40349494002c40f074001c0060106501030108100221054640d42d6071160304900b6511015101450014517007225800108107180f411000242404555269042900e004001040390798158845000103400d00130b026006034181001c4030b40018190700c090700103009010454481e1540d0513503410a125451041ca4402050054108014403501e40101d010f13203841802810040350150300ca0000c02d084806401440c00411701da0b500402000001074800c15032070710103407001e00c01c0c6c070725558403540e80d84014003c0041854000ca1062911440c5031600c0a20040041041c403240e0301c003c401c03500c050146541d90006001d18840c1c6120140550100d604084401c4000c020f007201042e006240d00c1d46111a0740c0600004205035441c20401d20a00b501408105042e1aa2400d080c50450f00e000308520401c1d030540c0703040b0104072203644003140d54200100b00b41e030690040d030303289001c036400c2c5840040010500c404080507941071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 285873866 1250 285872616 285872647
    0x13090b01051005090901050d030c06050a0f05010603090c05040b01050904050f070e031c0c060e030c16050411071b030209041101080f04050c01030903143c12070212 72
    0x101c84042d40c800c2c949001e214411151449503042ea243c0015044004004e1420601e42d0032100501a103007840c02c0c80d2842e511300c0169103050f244001e40e03646803c040c013000c04003481502e00404035420708102c00441541c551441c54078a1080a220325682c0c09a00043d03409401100c1f44840300910030001c600c1c201741641f481881c140c030b02c640080c0d0707200032148203410700140c00744070124820303610380d138011280704101c850304110102283d01c82d80307410014401c21001c1003c0c00440b661240540102045540e03401405074030355014912950901c658030900b03e0a02048881c10b9810981c0020710060070401440c0790303079580d0700081d00050900100407d001e11305040642c1c140d0240c2c0c2e4440d50742c80d034010314404110162030141c0f09411241c801c2c19558001e905c1070311858400e05184c0c552103586044290240c04c00c41c106220511414104190588050070b002152801a208408403a4082c0c00445090191641508070094040d01003120b0500801200400a20b800101952810b40a1440e90b8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 285875116 1250 285873866 285873869
    0xb1206181f1505090c2b02040303110607031a06030907030807050601180203070f05070501092312160813090c0905040f1a131b18060507030e010c0213090b01 69
    0x50030362940b1002c5880d180070a0464041c15801030600d0403c840010342c00384001c5e103e4012051000e040606450580c0c40d8006800207501135142d110303828000b1004541020402040c400401d031900061841300800300e04107a01120086c6e50f01a100e07540c02500030302d0514182c00261410901007488010008000f0710a0305a07040720310080340a200c0080c0e00c0c401c0e0300003a92102c021415a02d00209110320400141c0f16141c0510300200d6a034801d91038141036160200e5160305030303582c202244458040104981d007039140805c11071903e02001d1100060040d03100700700081c812100011859146004c03402c0d008043d04405104004410300c01101410b160914400d20340994101041c0d10405c054602c902d00ca03a03c46110039010000e190420000da44c00c040360100e11150f80c0c0c0440080c98250b410000007980341940310750841c0504015a031450301056404a070403c50200804030000b039103c030210700c4403c401e00700582c1c203203500c1c40000c560040f406940000c5074640042d60091101c1005450b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 285876366 1250 285875116 285875141
    0xc02180a0506011b080d0b011707050a0e180f04020111030309010501170316020906030a050a05010c03050f0c07080a050405130603031112072603090706030b1206181f 73
    0x4d480fa6029800000c1541c0008040c00d9045e040c06940c0405040380c04c40381410105242c00b5614400040d40d4000010040d1160380020703002040e280f10064000582c049054011500300d8050640582402c11a140041111019296440c00700f402c6901a0001c411403487c201c00303890300e0303191115109008200900c24140c0414408240c2d0200060100454400e003559500b0103001e20515024440c2050014050a805115110b4846c011a01c10300001000074450343c00030072650781120004040d640c01915011582d880c5a090044582408003200c0b982030f4000307500ca48940400c0130645160050381d10054003c2c103e45d103001d055200c550f02030703c00c2d00d2081d1105100b074a403202c01d075035a904981c41c60201c03036202085600d01040c0703201d00e0703201030f07075802003800545504421a6140541090302c02da0040d80c003040061001036054010f68607502803d0701c0c5440009042c3e00007940d42c6e680a403072000c8031210b100200d074100d031041c030500d0030f000d40c00c00503a1500c114141c900e500811020000a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 285877616 1250 285876366 285876377
    0x50a0201090609180c0203130905040b06180103030e01031b0c050d110309040f09081605010f02031302120a050304060c03081006020d080721090302011d06070c02180a050601 76
    0x42401d902941c0c4080548940d0640d00904c500d100b078040b0010000c998500b025444140004800210501024006041003100c0070907581000d00d40703031441560182401d449011180042c5140c88010081681100d4061800d02207210019005900520034510010050300f89401000102c60700080c84081d054860340c2291039000001404039207240751080c4205040d0010440354403d1310f0250000c0d00440c0c040c001c000380012251ba6909101da00841540c5908a204c0003141c0170300c2000e12490610600c0c2600035813840ca08448140c00499541c100280300b040021046100314004110f0207007490790200c212503030303540c41c0c607400f92800213280c0c000c070001440040090b075020702c061f08290031a450b036001804507c0e02644d0a6075142d40041c040310802258006a0540e034800e003490a001c000e8440000840040070308000f0b081d9421406900880780d40110b40c0d12818000180b083d502102620b825034494200780700244d00010042d0312102d070000901d080c4030010000d903008a0180c0c0c4240c070396 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 285878866 1250 285877616 285877619
    0x50103030c0510090c180e0709060f08070e0415020d1a0301200301060503073f020909010519230306060312031603020d090b060102012409020c0f0604050a020109 71
    0x20700709a6026150040004500020400003554500790b01086c041e0120b4001c680c25660041180c54041c0a42c0b080c070186442d200204418004621100b028004140c054240075051008085038014091300040406c0c802070f01e01c02407101d065068850348039400c1c1040c80000c5007408040910b900342c80e420b91003940790080c45c8001503900b032082c600d88265a00c0300c0b81540e01c3e006045d030340780e0002031008044c010b03800003a1007100c0320840f1140c211110101c003503400c140545c00b543c01284021000d1044c90b48104000e40d525135075800c0460440b1011039070040310700f48101c41501c46203001da02031f0740c4008280c030403440c403208141500540c4600a0301100c3d040d5481c0d2040540d80e039110621810a150100003049203801e4550224000c00940d0901610f070101c244c121000300d03100c604003600e1410040302840102e40c2e080c05000c01c1819140c28603d00220b004002611070a1a0310070802000c1c0d000070b1201b00c5001c00d100210b000c805202c199a001c0c9890b00308a0707100c0e000c240d0100e0009444000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 285880116 1250 285878866 285878893
    0x7050f0a030b011115041202160308040e15060d11040902070b060411030402010c121b0308150a0b091c0215070302010c08070507020f030a05011505010212070203210409050103030c05 80
    0x21680305e24170b59040c2d02caa40d51038a8840c040805000c00e42c4200314024804001c1c171640d40c12084e140110b20441059507120300d0141c2e007020210300178003460740c0a007005206904503070310a0192003803000900e400060b5848000c01e8405188140d0380155440c0780085030b4002807003040c1c007060340310365416501030041010654001000340300c01c50f030007800309061240e01c42c00702d041c030000241240c08070305110499048003800c02c0c64072030168400714002a405d90412803143c00c0c541740c2802c1c203182541c103141d03072500b89400811240210f0030590f000340c807441100310149076003c40203e0401e8015003100d000898040c1c648900354480003055002d0340c04e198200c00003d100d54a014890307242c903510141007002c00d0f42003110300e4101580042c4d161151044000100c0e80a11514502024812803000868500400642400b03101d107000d0781c403403e0501001d00540c4010a003104201c2c03540c003e00404142d20060a02c250003650084240c152500002004140c5c000600c0c1030500c0c05441140c1c803c2c0c10390360 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 285881366 1250 285880116 285880123
    0x7050904030917070b040b031501020a030f0311160503040518060d120225210b0f13080a08010306050a05160509040905010221010f06080c0307050f0a030b0111 70
    0x1103000700024510321040100300c0700e0344085070700c2c801c500d0282c0f9503165903004003000c0c98110307400c0110180c00000520400c02c0d0803d1070284910700a0000d066a03003c0707a1405007003407030081c013071000f45500c0394101564170810308121602812040840c040d800c0003410550703a2a00301c0d00038a0b0080c40d001c08401e080f42d0700d0303802040c0f09641c000c1c00d400200700507079240580e42c045181e54000b07500c2040164041940070b00044001036440061000446192444803019641241841c010525001440c1c1d0041201d00110586c4038442c00a580407c1d20b0b848164003484166081c05031041102044071b0280540c07014019049a00a207014030140e120800994100c1d24207860800f40c40d0302083c54039a4460058000c1c1040400080c800903100096485550036607104041c0c402c011022100d82d0454031a00e112064007419001c3c2084038242d080150141c421807015004000440010000803100342c400e200b15820325030408071044d200c502940c0d0140c05401410400c5010030a4002246000403000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 285882616 1250 285881366 285881371
    0x5070b03070f051c09080f0706050f1b180120150610020d0c0303022a100c0f0c170a020d231204020f06040e07031b141303061a03070509 60
    0x20081c482000a01c1d05001c0c00800c0c1005d0111200c0d01c00380070f070402110b07140014203035280c000c4001044914219a0780f2264090043c02c0740c0f0b400080d41c2e00e0182d510b41000603078403185120f240c014446104ca00040c1c84690040d0001c048100401c09020000040410500c916408208408520303455032420045003280c00e014200041c0c0c81000c41c690050312034090401e8035402801c00502c1c00402d48001c000b0101c1101c0c820f0221140d400350303004403030001c21400d030760254001c0003040802e9540c50000e044010620ba8039003006444000c12050001d201ca80301c0501050b040500d075120a9500069150241c0055150210700d0441180ea450090340b104c19003540c1000c2081d6241c002d05141c5259040720161080c2d0304241c43c801c0c2c1c00c00a0b12140300030800703081907040c03003d124a000c103001801d83c0d041d04a5004902c40b091140d050b11601700342d80300034004541521035200c440e25811001c60810980c405060941044510010243d48800740400300100342c00340c2d49003d8075803061000c0e401d000d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 285883866 1250 285882616 285882637
    0x708010b010f0539100203060a05060309070b070f0501050f04121d06070305070203071d07050705010902041505010e0402070b060d03020307052a030d090b0309070305070b03070f05 79
    0x25008000700180f1031801010690b0310b800d5103001003074901c10b4804c9030f42c14007141c02c02042c0c3d804500280d110801c0140700003203208400d042d031851a245010402007249407045a01519010001c03d81e804400d0050070040d000020105840308118204820f044118190540340b1b54a450003151500710f000c01c4503842207400c0b80310b141d18200c800c7c004464a4089815145454104070302e40501541c0b0b00b0001d003401c9020343d4519440304a20b00416040040340d138030088414600600040c07111b00750144060f800f0009007085512460941401800b409665070006c0d44540380c9008104410710703000410056405c00e81c0c0d503c45100320041800100d01c00c418021b81442c03229070008803d0b180c40802e0f04552842441500d00300300c401c0d6030b0700e807500796903207404ca0614040c2c14894082c08080c551070780c00110304500511010850890107801d5400b81c6c091130501c0030000001412800003040a14021644207045034501680e40c03480340301c3d94100b6150342d000526610702e04031480c0e1154060f960781c1d402c13 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 285885116 1250 285883866 285883877
    0xa0825080f0c0f1903051011040609060f121e050a02070203061303140301080706030b0604050f01030c09170105150109030203330a090302070803030108070e060a050901170708010b01 80
    0x70802003003004106000b03419070040411030200031180303410750342500441c4200001c1070708201c801aa081555410f1001d002c0c8004244004c0084ac1d034400c038454201e81040c1814100d51941010450b0340b801c0d140009902103061030380c92903040021074180c1d51911000b0808000c903466009140003a44034000c00030303605034802408160052a12141700702d00d14800c0c04c2841120119203400300207134000b6400840300740c21510040040719018008c11400e00421070700d0929060505000078000d100d0300010504159440100c80c414901508104014201c0000048503118a010f034035406408111480c109240d0300e0206031049501170b080d98802d42e1740c000d01400900c0e01c05000a0546818a500b141e00b0103c000c81e95072908140e80c90490003020104008955078541c0c0c02c0181c40c020a076031202105034020401003111840c049400c10039101d2400c0b010400382c0b90308000a40f480000c5e00501d0303004440034000100300c01c103c110000045480300c141c40780e169503065840e00f00c81ca4501158003055 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 285886366 1250 285885116 285885133
    0x1707051606050c04030f030207080f0a0b01031104061e030203240103023601050306100b0d09030e04060b120109020702010e04020d02071709040e21090a0825080f 71
    0x15000c1c2c00c02640480e00007001400c06a0304d032a074030941a500d05095002d40c10a503802c1c0315031301003031182c0500c42906800030102c0800701d0b510746241400520015101c003030003a00c40207450b9070380d4200c50020802001c0c95802e2141d01150b00c1403080c2248800c0344244583c07030704900180300020118101d1070304100c0760305450b840d6400f803065003c1203400700880100e41243e0307400507116080c2d440080040b801102d00c1c0d10340c1440281440c010000d8560350b4a540c03644010411f20840380105c0c1c0c1700613020302e400700710b9203a240307810ba40068901804691145c2000720218280c000c05024100d14a00c06c502c8a601f647e990703000b0400c92013030440c041e0000340c10704190111070400f60020110601c24103001880c2c0240c60b1160210714032101080030107181e0029a180e0b4500c1c0c40d000d0340c04070144642c06403a20b210f0340c0000d10b05918090110b00c2c600c101c049090117913507035408046c10060078070509540104200c0ba00d40c41d229076883c40d4a0f00c0300400a080890110710015030315185510f118018a800d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 285887616 1250 285886366 285886373
    0x6020702060f07050102040303030c020f061b0405090114030705100e0d0227010501020606040209010207030b090114100515040501020a0b04110a0314060a050609040b0705090a030317070516 83
    0x2988400010303a00420104228601d010a11005040c00d60041e400147c51741d00310b00c0d008003034035044064941154441e03400e07401035040c0403d240d60031020403150382c0600554850a45001c1c000c0c4d61100340d1100c85c40000290b1500240c0180320f0fa84011010358107002d80752010402e04c00702e441c01400000c5d502598844403418403031010800707140000d0541d02d640e80000e80c90722901e00d01100c0a034036060010010801540c040043c50f8002038110b8082d41082d030003800007550f81034284005080700300301c0c80205104200a5110a4410358401500b40c0c003807074480c0600002501c0da1003032a00604000c5101400c1c468118107841c00d0b07883c164054200e0303c6007502e074180202000b801c140d400034080440a032071991170003800d10003144a0341c0702084000300d0f0f1400714141000108403040d200e040008002c955520034881a61059020035440303100d4484050480e12030062400325500f01c60544008030525400c003000d0207000348011103100341540c449104032030034064035000c052400390b4a050705002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 285888866 1250 285887616 285887621
    0x15050703110c040e0102220b120c0f070c0315060b030c07060e0d0c0311010506030c09151531121b0b030f09010606050901080915160e0114040306 64
    0x11005102140c418042d5000082c040700d40c0b200d00c0b24000c5c0c0d4005202080e402804480200c09503440403400c0c60030780707494885441071242e03001582c0c000d0b54000024118030344210544410b0301c0130415168503030b1480e140c07118444200b0700041d1100d240901076056051300c0780c002c4005a81c00101000d0440e00c1d443c03450700d215007090740c2c00c5446984482c41d561910504004200004a40d6a64141100081d0501030200b100ea07018680c6984d0424080cc1540d80700003401c2c0313202d500182d036056481e0303944400c1311b0412041a1412a4810030310b80c003d080c0c0e0f0309404017800300c001e40d04000085607140d00114980c224052100d50b00c1c90030a901041100404101a4124041c050280c0c00c400444480d0200d0440030990400103005e24084180151405580d44040d4451030f8071008010700b0f82815030280c40c81c02644006410440310900003a0040d6043c441c4003510902c000c910341060801c0081009190b600c000d0b00c1c40029002c804580503503105443c191030400c0e00a84951520b4259182c4001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 285890116 1250 285888866 285888887
    0x12060c04060f1b050303190e060f06010903150507031113140303120a0603060c05040602030405060d021902010504050f07182d06031101080105220b030a110a15050703 73
    0x107000c1c02c2184402ca143d9040b103107100403441100515030740d18219020f0a189140504003801041c035140038000303008400a0229001444180d0011499517014012101181c064200600101d032800c510300f10440130703030002030040c80e481e10b0500a60189030002c6a5502840305c04a190710481c1c4800c018050700200b1300c06c3c0e8a400030301681e2800c0190781d4012013040082e0b880160843e941c410070001e2054a1040c0380c290350030380c030b005132030a890003a00a40d240983d002c1c05104010003d00b03820001c5955048901e0865036500783c1601c1407410702c021340208011201600c541c0240412510400800724105068034100c9001001e424a80b6059000030b000862130b280300500e402c00d40c0121004100e414034900700e00e000d00807890070300350b142101004440381310007814040c0c210010f110541c2c4130a00340c2d0801c1d1f0203104480b0034101c00c28000d405031041c42d5002d60140110095581880009107201c445158160740f803202240c0d6030300300e24030a0f004a0316084001401400b01c54002440f5225054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 285891366 1250 285890116 285890147
    0x120503040b190b031603021503011508090a0609060f05100f030f0c08160914190e01091502220303020d081e0c03180703020a060c02060708030a050612060c0406 70
    0x1002070680d008a8070780111201405c2c44c00b11041d40c10011860a640c0c0e80300120219901c06065514010160a04480e002c01d52024020030600141c00c05d0740800c016096503070412000e200ca00290300340031000b0600041034420311420301001408080c0388018000c112100b0110614032145151141d14103842d410300300701d400c0c4400700400207854104000300c41c460303d080403a08001e145490400c208a41120405801d40200351040110011000c5043d014803480080d0121799000d001ca40306004084161008000d401c80808403001500541d01030304c4d0004614015541c000410f095113107968070303144401001680218141d0350b880e0b10404880d40c011880b140360240010441c4101e410041c0d0440f0200302d125130210400c00c80301c005001d084030710040400034090050454003c10790091042c0074000c2845104400b02c000c40d1a543c049851181e0018420307903ca050072205180504400e07902d00f4811a5060208108040c000c10800e02807183c4940c1246801e150000c10383e002441c00a008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 285892616 1250 285891366 285891371
    0x101a241602060f1b0c030a020d1a010b09040c0908191b06020d090504330503030705150c16020f06040e041110050c0a080c1612120503040b19 62
    0x4010b80392000074141d024000e4103440d450380c40e92240126118148850311082d035212680316001c0b501c011810300035660701601e8500ca8084c1900f000c1c0148005000c2e07030802a031009000080034400c080c00350900310b01c125014040c2c9940000104d40054182c052201550001040b0622071601203110140041c860020401e40298038000d450341100035500100c0560841030319900900e82c0502c00502a140845040007000403c50140200c2c08054980c032148111259506c2404441c0599800081c0401004c880c6c0d40c81072894201d403203240c0e00206440c544903040c007265140c10100b042d070345950701003241c000b130403e03141d02005001c40c1c54081c20703070704120200804911030a0104c000ea201d0b501814041c200440500c0c18022070852024440c0100041400031080d100c002040703501d50f040d04000c840d501c0b0712500b0203060074014000340c1c01004541e00c10740043d01c0b12101c0070309034116000e2141d01c1c130751520710007050f1814401210001d241c0845a40003a0940c0c880c50300c000080807150200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 285893866 1250 285892616 285892657
    0x5060f1e010902030a060e0103030f0309060204091112010b0a140f040905040b0f09060c0a1817070e0105030102090a03060513080309031216020303010302120a05101a24 74
    0xa0342821202a04200c94482d00007041100800c06401074100402c031403490350790b8035850b64500521808091005800705905c8280c1326061000340c0e019107001d011030714801c10440f03503043d9503205150700c6081d0401c529083c80c03000144501d110000e039140d400540e00c0b0702e4081c900030b032400c4105038081c000552250000744008961032200b80b00782d0f8803552060b1112100d80c1007441f5040c900081c010004100d940c0404200000c200d00700381a45d289901a00300112080540050110500003581109000d46134048807800c810000050f030f0f104071034a4026401042c0d80321003d0500381d11030105955000b4140070f20400000c2d40c1580407582c05100141c003400011080e079589070a55000b9a400c440da0b900100701c07102060906120725801691128480b030b407a070200382c0080d40300e00052101034030030031611054414981061081c842030aa01c00c1c19640c03049040e19020005018004d0746c0807400043c018058500d05000400200e012100e01c1001d02020300d001c11986240d00c00d0002007001c8644000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 285895116 1250 285893866 285893911
    0x10906021603021606050a0e0406150c030906090e0105060c0c04060611010e03120a0c0918051503030a08402f0f120f011b020a05060f 59
    0x24040e88054041c07069107030400741c10000e25000c1e0382c080040c4662000c4100300725007600203044954a10319030610740084000040020010241d592290b110002c104402c1100250300a81040900c8e119844220301980c66590071075070380c0c0304e138041c80c0018904a80113118500d04000a000140da03050215013210180501103025603840d50b02140206065840c6410345420a0041e10f015070702550046040c4a4a150801c1c040c000c00f4000c0c0c0c1800d541d400180480d6031003201d124000c1e001c03021a0000745c00d1b210000c0c0c8018402240c505a03555070103540c2c40045d00c0d0210854001003c079035070f505815142ca6001400c00908100c102c0003060408913045800c50030258690b0451160340c1006c5000801e9040081848604110800d170045040d212910000021042034000c22401d40300200b6045403c80444c107200c5110007810400d1085200d800340348031054000341112045100d145d190240f80c3c620030382c0d481641c03220003401500040009503400d408002e4165010f07181d254007003da00800320 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 285896366 1250 285895116 285895121
    0xf061509031b092802160b100e010608010b030402191205010e100902031506012006091209010f081e040302030d060602030f07080a12021c0b18010303050c010906 71
    0x20902c6102082c000d6410005180400c1880c3e4032140300344441d0700d58982c4840300c00040d014851200030303e40d800716929500107210000341c0e42083d40103d07690707610b0601044840030340d0114800d107800202000004a50303144504181e034100c8a403140b00a046407129030070410700014440f94802d1030000d110000400701e005181c01602c540c021000080c00780b10074001e00d814080e00e000c90b154003904000c129001a1000030f5810003114542440d021203844200040b1101c00054109018030741d45002d1031003500502281c50f80c0074000c80b100302e405005d40740316022124000d1101803408600c00507440b992503401142119841010207500d120000f140c01c3d030601c0c10900588007030700180d20210b84000300114a10403038001d000c40740025800c1c04c1c07c00452020520507000010900e41001c100d0b5141c145c0665459803041d420304000307544901000400d0044032405591860800d03080143e20b0b001e41c100303007003189000e150004900582c1c1e030960b2819201c9600c0751060802d190740c4c0d040d8100100c1c4203032 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 285897616 1250 285896366 285896383
    0x306040b130c110a051c02210904150302060906070302010207120c0c21031d041b030b060405060307080903130303020a0213020a08060910030f08130e0f06150903 71
    0x20703000021500b0480000400076010355040c8543e60b4006048580070660004a0b905080c03103040703480a400c00c0450b0200e0400c0c0500100340c0d01d01c0607021507041003100c00800f07002d400300255401c125908114030040e48200182c8800323034000004104007040c9052980081075400c9c0240000b500e8503442e03507500b40c0d0b843c144c5000350001402d40c4081c1001c005030003030010300402c254115440c4001c01030820104403110000010148200260140c5804521400b242e504120043c010411400500e65482c9010110184200060715144005035a407a001d001d9505490f0003801160441c1d503019802e40b040c0358003800c00d6280b40300902191b0844404083c030340e000740d0703c00d03400f401003080d491042c031041c402902c000380c14490051011041050b07004060540c4560220b414001544034030f031507020301314078580015212195201c822418415a000208000174420091034809a078400d2100c00107141910300c100014805804540c40b072401941c4804240e0f0381c50219480e103180309000a02c0c0c191407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 285898866 1250 285897616 285897649
    0x6030b100f05060c030904020d110c07060905121c090e130b010909050624062a150c0703091d06090c090d032d11010c090506040501050306040b 63
    0x300601440466904900c024042660341e5410001c07061202a1207000b4905503038041c0b5408585205d07810754980081c0c0d01200301e02522669080071000c143c0e05c5400701d01405000ca04902c0001806007030101d0540d40c03c5151002500310840800c001c2c030010071015280308100041c810300820740a030a405c0711405280e6000001006645c6d600e400c44d01064141e000d607a44130b00e41a10400881c1001c030b41181e0000c586515030025440c40e401c840b1180c03040c0d020603908003202140304132445128a0f0104d05c11800c014000381880c2205c818143d0b0b81c078440e8440c0b443c4a03009404a82542d61328070207842490b1082c1800b010303240e265800060803051a9855036402e4807460203200d25070411005041e0003900e600200c5e0702e01001c100224000b0b44102d04000d0810141c2e50290038800455152080115010180f0421890a081d0010405002c9046c00002940782c010090440760080e030882c0c040310000b8150ba0704091401e0300545560300005c00c00c0c0e42040c0c0301c10041c0d400d40e5884110140840c003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 285900116 1250 285898866 285898891
    0xa0212070504030506060a0b04050603060a03050f070f050604030f031808032118030307050901020c0301020703020f0708060405100b01031b0917073b0c030105180f04031206030b 78
    0x3e181095807818002825950045880070000c4c40140301100484003a42d5044d2111503881d201c0300081004481c2d1503001800d42d001d2240da10205140c0802e1010484402e8543c0c00660f60316034040080c240314034400201509003201c0c0c2d6400083c040c0750305c221908100e080e00346203240d550510f40e0440c0d10070546003040318020351445001113682030110360403a404e480440540d010b8103650b50303a03920000e032203601400b0740407c0d524610380c030030009231b5440e4074064000c4d501c2d10000e00d8065500e00b42100482e03d1801205000300315110f000500034030a60700b10740104084104004079000600c2d914035000c0c105a141d40110042400243d421680c1c8901b642d140a02c140c03030900c1d8000c1445a180c05090300350030144003004041c5240c225400488950200da60b09010709008a50400320b103010303154002600c3c83d04000d2400d010340082d5048035030a90307120890785550300c3c550030340003421580c517491034041c1c50218005c0303441b444410351b20422a0301c0c0050041d80f65155402401c0c1d080b104581a070341c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 285901366 1250 285900116 285900119
    0xc060f040c18050f07020d0c03030213090f0c0915020a0618020607050d08010b070c2102030d08070311040608040f03111002040503012409020c0c060d0534080a0212070504 75
    0x343c4013000d0b40d81c000342920250103103024409000f04000c52194001e41015000300b4800c2079010b10f184d00030b0090848240130000407141034181009045481540340228040c21400900785005250305401d20f0016809066103901d5552040b0080c000718508118040082030400016240c0c3300080c101c490003600103258903239540300c1c0105003100580000c8026403082c00f403a40014410300008040c2c1c0d1111101d20030060302045031204039000000042d605129402000c482d048e00980d420303015944a42e0103010289442800b20349074800ca12030840040e68920000e00490b07140c040ca0700c1d409129180200a1540c8200301c5460042e25402c480c5085500180810140ca0f09105034010066000e103108841c0e101040c0c10030092000b0710070400c0454000460416120081c0020201b40100074200780d2a584458155401010b08a03280000d02214465401c18178600040d0039184014203c070442e441e050506041303444480c05007480314040c0d000c0c421040d4504040b84906d205a41c144c0d562500c0c4d6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 285902616 1250 285901366 285901381
    0x105031f092a02070815220b1f0f060f11010501080d020601050406032307080111040302041802060301210b090a0209070807020706050f070c030c05030709020c060f040c1805 76
    0xd00001c0a148155071044c8020450420080b80e040c82c0b80220350f03c0b90919513940c00d401c030424071300403130100e01c412203000000d03040003007180c0341d1400380083d500b1607042d02d501380040041c0110340380122080d81920304000c0103614841e14641c1c250003114682071180328040704500d401e480080e0040710700c0d034201c944128002c550420200d030042000301c9052041c03600d1516011488100c0005401414a683c0c4500b1042c020400c1103000800c507580081103c9500000001016005400100c0c810307800e1451b514034000b0f2a0400e20400f9030002c20491869191512020381d02d00d8481d1141c2d190b107802d410280211b080382c00b1661180000c0800f4000420049c41000440000208828180480c107414000c2281d4006600c00641781641800c641e10082c41d0b0b0029401d02500e20018458010300001204001c4062008802c941003501143c030990b86540900e4164040c1000d5204188d1200001403020000410300c1d5401a00544142c5500c586490030b06040f4a480c0307c0c8550096140c03400d20807078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 285903866 1250 285902616 285902681
    0x120108030c0c0f0d060e07030807031d010c0b01061d120601081903080c0d0f05070306150521040614070201020a080105010903151d0109030c1707020105031f09 70
    0x820400c545403c6111055000200304602c0304001522169450300d20009010003000044091a041065035071034551501d801407030a0440c40300030340c3c2c405a42c1d054888950040c81d101c100d040d402151901560700b44042141c0304083c90000c00e9548028280358040c5485a40d0b440c140240759802801a0b98140790501c1c1ca05440302080c038002e10609134011000c258080c2a1039007106002c4840c3d9034135170800300c1500c080e2103074400b810b030340c5460503040c0020b03150160f1054048681d24541416046152542071f15103010310380049200000b44c0414114941004449079072140c07160340c0024200100440403190000111000741c0982c0d800150f08104680040351980144000d1801040107400c656600c0350700d140040c0e0b0f44016035250660003001502124003854040b442d140200408461810000c09410315078400303071014044207a11041d10300c0741c0c000b10741000703406131107181c591740341c400a01d0701c803105400080d140800c40180115442026024541c8940300b600c44985d1502004ca01c05940c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 285905116 1250 285903866 285903883
    0x30f130e010b0309030703110309101e0212120a0e01060e04030905090103030c120309141015050616050327030c01020604150b1809010c1209031407050102120108030c 73
    0x30b10100500070040c41980000440d901c655242c545488111419440306146010b0911450307800903610420000301036000b440c0d00907102080010040c2103000d14400da0f1504907100044c903d800d81000303441ea401d0120042217800c01c824810002d0710f000d1007840d080c00c54120740c000e0040c00b03e15000340814194007d90b41e002500c000c55800b041949140e40180146030780c182c0c0140201c10400d062040356002c0d511a0070b005d40c0000c10b074558640c01610f01a1610040c10025101d645401c01e10b15400484800c041c0c01d5a1000e000580307040c004210303620303024402e0700080300d541c4000c0210f40500c1512106090f4400901102c40340138580d000101403c1034100340f640e42c1198400d00810020560540040036075032300038440014106420808030700d40c96010460420076059050900805580540c400c000f80c0c0c0d020f66130108180040e801d81405d40d480401302800140340c12480c50000900103004180d15480313040018134121380c4141e00200041c00740d01c80c680c66080850f039290b400d00207114006 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 285906366 1250 285905116 285905129
    0x91201020a0f080712050403020d020f0a1211120c1605030303070801050f060d05090a050708070f0e15041b080a020f03130c230f0f01120b03030f130e01 67
    0x10706120910900600031658007850303008010742d40d80412a10342c01004004201d0b0300c0e0460510982c40c00d800d0282d507a0781d02241020046c440c01c050440da001e4003061034a402644005440d5034007101d6138040305d402c10480030005040c0140c0c0806e0491802d210700401007102000d0207011606100390001d0129041580721500a820410401c00500c7d813006029042d90000c940c1d8905015418002c11a01e00412201c0d03e102481c14052100d25040060603800c000d100b00e08070b80d100c58940c000903444000038403540a121960200900000c0c8028240b00e5000d415504d50314603581c48180040c05032600a1408040d002c1d0161100c00c3d8168400c11865010b072061fa025447d1085a0f00c028041d0b00c0000c0504801003010b510110800c248084210001c1c1103040007202c003e40354110302d113540f410224a0b140b0031030804508007058140742c0c01c0703820000c0381619008030709440345048801410005100780d0340b5001c100a406906409000582504401007150661517420403148034001c0d0410382105 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 285907616 1250 285906366 285906371
    0x1030302061008060601140d060602060f0603030406020a0b060103180807031206050a0306020d110703080a0506041806020307020f1e070801020f1c061a09130c020c0d0c051302091201 80
    0x10f000c2508001801a0010001e10b0070030755650f070640440e00140200d50241c22014201400000c03510f6001030b20f036015078442e14070b02102d610381008040d0b036841240b01329405604583c1190010600c0004540d41c00a810f06010400403416504001000764840c42101d00c00b602164240c14182d0088446507001d1042900b040094101000611014603600c00200081e4001901160300000c6411a25440d002000034a490310094580513110035400c40324074150b1480c0c000000e025107068020407088480081981d40d241080d40c1764a4069400149030409511030441041c0300b0103810440080d699a450364401c0c0040302040a203030400980f5807064015a0051004c0a140083d8004440c007946664003241b00f0548030701c65443c050034135544071641c00d80d81a45280501d90074040284201a01101c6120940f80210715a104803000c0042da14016400f03001111050704020100c040510f0042a051103001c0d0740320005101010507040c604800c5030080340c01401030605940c54001c100d441c0000703 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 285908866 1250 285907616 285907619
    0x406020a110c1c0609051006051017040b15030715020c040603020a0b03041b0f050f090723090607050a05070f060807050f070f030905151305090915040308010303020610 74
    0x41c1c0c3d1030b00c0c000c905103c80fa20b885036030700800400d0350040000d90352100644050000401012005007030a106846c000d0b00c3e00b40a4240e4180704407591182201c480c41d01c01c0700ca4a45496994080750010000941461350a8072040142d0701040a003000300078040400d0304156a103c0002d00303101d400d1020601403030900b10103200503a5002a48420b54030240559616941d880c02c0620903066041410071344003401d00300124542c820410382c0d10035a00240da814401c10540000d0010720481114004009114803107210142000916204c41c0494242102810074285200160040e8451581201c50307901c040d0303d0204200e030a100035401010380d00c40b0360004524100d4082c0072104024824001c1040000308100000100825501449e401803544d4418200b580f902900e1b10a050243d0b52054090007012036808010304222000d001c0e0026000e503505181205103c0704000152086000380108482408903000c44181c02d4481c60080e59418a80e51560602034185040500b0411070150382480 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 285910116 1250 285908866 285908869
    0x8010b0102100b0103330b0f0306101103040e0906070804030f0e0102070f0306020a0801050a1809081e0d06120309030b040309090e010209091503210d050406020a110c 73
    0x4041e41e0001240b07102145203a0900e004070010034020301c01000e0803c0119a40340d079202030002c010328171600c91100c808400d03207401049000c0e000d900c0c2412205801000080c4481c104542102000089410241d1031840d030004440d0564005400641820f0030003000c201c90b940040080e140c001d030050034120480d05044e18001c004211901098092100120540e4026403007040440d0080201040c401c0f02e190b1607240140c0654441c2003c0700003d140030001055520b0300081d42d5084840c00d04000d168044460080409860048415a10500180711b2000b42c0500d403000003503400c0e0401d50256580c46421b5052040714040d070000000b40c602803005400190f0407818042c2500d820281090265490345004c6982d0110340d0080c4034000c0c04c10b452000000c8054024000f41c05048600e640039580d0002d80a6103120310300b41c016419031015100b150900c0118100307a0907880d094a1031450400c0a070b808405460068800703c605903070000e406180d0030391054829141c50007402c00341102941010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 285911366 1250 285910116 285910123
    0x11070f0209040f0c030f060c03060b0306040f140702012406120e03271804020612091011090f04090b0406050a0b0405012402030a08010b03070c0b091608010b0102 71
    0x1000a00034841c4102040a12030750f0060043c600e60300c070013091005a103d10b802405414070100469020782000d17803e411b82c034024020a0243e4030101d180c5820350742c0300d0b810070015001100f034443d0520707910b0840c01903074048a00003a01c1140e20350000f280c424160b00d6410072400903881c806801c07540c141001d1001940c400c00d4030700080841c81000c244d1001c20f0b8202421481800c1d5141d0070354800c20085003504504050403c0c1a0600315480d40d0900c410005440e00d4510850b0000e511a504102040301e0b08071444069800040c07071411212814001c45600080385c003103039101100107401260040481c0f07410098121490016074061207803480715503c0e07004060002c0c000800f41500d036400613500b0b1203031b54005c203941140140144401d50395065040140d64140c040d00c12844108a00000c48a0001048039038840107035079007900356031900b02485201e400145ca0031080040c20b01122010806c1e114669005015000c0a071094903030360100801882c2040c0e004c0c13810b99041403c5200141e8010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 285912616 1250 285911366 285911393
    0x2070f053a050a05040e0406060305010b030c060d0203070314012310050901030b01180b0910020a030c14160603020306100f0207140d06020304050d0206060409170a09030c1502011107 80
    0x2410300a49850f04070394140c0c2c0354010303a00b000e01c00241d140c08000c1400010342201c4110b81c001c01c000c2040500388001e140c1c1360041c8054031600040c1c00c010300e541400c61980110341c030001d07d19000420080c100142000e40000b80d100c0801c0c0c50b4000074088a418004642c4000c031401281d00320325002c1284030281042c00350f003c40c1414550780b041822543e034081e11014086401c1c03201c40001d210344131140c40000d03070040703000c0501400150944442180c00000c603540100c3c1c05071910710f54080395130f548914060940b1150044c1e800b42080450420700c40364840b4020384440c8d00e0258891a290042c03110074145244420100640341400003407031500864002c0669802c03000d4404131187c0d030b8003c100300c110b018100802c0139100004000c2400008209482c00c0069903007540d00e141c072440204420b48041d564060030141d10a0305000d4200304040040045940c03504103040265034a1b11401910321503903200c881d6141c2100c0d00850940d50a00c6203050744654103080f5030611440c2d840780e04110151 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 285913866 1250 285912616 285912733
    0x2030403020f07060206060108190f050c0a0801090203010509010312050408030d0606020f0c1003020a030b120c1005040e0604051306090501063f021912060b1806040b0402070f05 78
    0x20b41d0f100142b070036210340080e505402c141005000c02c4c10940c4503d0001c1e4491207074100002c03c4007002250000881c001c403412208002c00640169003140c40b0300309030044034400f000500504110025040b0418809842c1e8032038040400602c0e00d02e00340002e070900041e0284042c2c1d541204895241d950364030401091010b045260050f01c0f8103194074143c00920088014a6100c0c3e0410b0310340080382000030384c40444e0381d410b4441100c024513500d4159140c0c0985e02440003403007492000650141001c0e40b08550100815188420a001c5a01c503c01100c3c0202029219039440e45005d101ca0304107980030b040919511920034010448034142d0081e45601c154880e0701e0141c00581d4442956121140c03240701c81240c00307003400f04a603240300c040c05000018408541541c148046040766207805510681108610813954255070340d036200300402001d0f010b6001e58802d50a1010030080760044001c030048c01d11980080010881c00781c503207400c004182b50012500d001c0329404940c20b9041319540c6040448 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 285915116 1250 285913866 285913891
    0x9060e010c1e0e12030705010c0c212705040506010e0307092a020c0109050409020d0b0703060902180906090105031b06040e0a1a0901060f11070902030403020f07060206060108 77
    0x340000201d9400d041c0d180c3d42980030a040302e180307030224000310080219030301c1103000304110000d07414140c0e0880400c20011b003010f80004103001d6802100071003d0030602451900c050f5000c88440030709610310351020001450045940c00b4007c5040c10301c40d2a1300300000742000c205034404000001c0c3e4840b00780c0600750ba00c0b515000c01d1260000c02c40c081e2001207821044640a03160440b8009664032011040c2900080d40c82000040c0790506104020200c0c1c0c000c2d1070011500c0813501d50614100d40504110109a615000000c08202e14030190942c0045040528400d80014041000e4800302034a0a440340ca001401042190360018142001c11140003084070a0300c8218009940c9009542c08903e05208400c2001241c60f1190300c400a43c040c0f0034403503030616403e801400386600b400d0060301c02282030034203500c20311070003104107400812607141102d06094941180703400707907002a9001c501503409860740d59518201440400081e0500f44014051403410800080c000400a81607207218003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 285916366 1250 285915116 285915167
    0xd08090c0a121a18011404080f03070e060a020d0306050406080607120e030a0917060408040b090a0503100b01140a0509130209030a03080907082a030a0501060909060e010c 75
    0x1600140350405400c944000c002c451800c40e40300c50510500310f4081405520b020311b402a003440c1101c210307001c0c50b0424070040c03d10010b506411101ea002600000510141c202c000b81182d5034140104000c41c410b501918602070044406000e42e04290800ca120380e041807000e100019002034000c0c4d02c000c41e0310f0301ca100d40a940040c140149284c2c0e071a0b89040c040018608101c075003100c0114125200f455480d09500d00b03d80203c1e44911058400a06440701008108880c3c0c159002403c10080000d1440d0611582c8000180c031303041d0141e0b15801c03c03c0d1210100000b9603000100007018241405015250048510b4020000d01c61070f020b4921601100c0e9604540d1140c541c155094000040c0458541240341c0c20040d01c0030004943d40c0c5840d10601002090b403080100e81080389507140c041d040c1c42c130113115007a8100034000980c2c07103401d03120381511030b070115209016960041c001810001244946401d24009840c008000d800c0d01c0d070f0500c1d6030813080c940c0c01030003040c902016000ea4180b10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 285917616 1250 285916366 285916373
    0x20d060b061c05011502010b031b0a0906151e05030c0d0204080a03081501020102040e0606030901090506011806140f04092612010801090c06030e0106170d08090c0a12 73
    0x380903055184501541d80c001a04241c080390344150b06036000c0000000b8945d003c000c04a090714904910650950000108d88d090408c00c1d030101c94a2000051070740301d10039201c0d2a0503085500c3e03503104054208200c0611143c1b41d0304241110200c6444413492030011084501c09000c40c0302c082c1c801d2030340000016442c00f00780240c1d816038001d080319a0907581075410508006040a0041c0c460b04a00443d1030031341c21007503005100700c4049443d9019015a0796840400704901a00000d208004554a445000c00066000d00906010b0f0028200c1101c4120800c1180d00c1164520340000c103a0110a44214000765680200c6491148040390086040d45c91494405940c41c10700c683c81740700c00102c00301d40784980c883d400540640705454281d01ea05170398031441e0900b070301c00c100c10150810703800003801d011961081d04040d0414075440d002151003a41c4a8481c40407410120310104c0c19000700704003900407640100e0f1150030100400003042413030142c4000440209051003441c4450040355248400c2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 285918866 1250 285917616 285917629
    0x10030b06061e030402040b040203011404020904020c0f060906060a03031b020f04060f03060f051e090a02100806190503060c1e040b070c0909050c0d0201030b0a090f18020d060b 77
    0x50801c5000c0400454a45003542d229001560124810307820f1406660150420384207880c12508079028140d0148030600c14070009604c0150b5040d00650200560800c4c04070800c54a4030449501000700428034101045505040300600400c4c1300340a504e40400100342d01498110b210002da00024481190230b10001c0c0d185084cd0a4203034005080c40c2000075495846100c160840c0e02813001800090001c140702401c1700c50440300880240e040a04501090074000b52081d07020945008642500843e0740000f0000c103a000660700c000b4054208000b040d00b054012809400c03600105200c4d641c1c14280000d8451400510000000802040080b40d82c8014510640800c1c2031130140790b625074540202c0c16495000704401d480782100d812001900175894402c0040440d080030144c102454900200045000c03042d000703904240c0c0380c030031504450b0b0701c0c01c1101d0002d080000d03002801070320303c40001041e01c02d040c0c030903090280790020580242c4c982d8040c10001c0c80c2d004c0340000b014030140700000e00c07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 285920116 1250 285918866 285918877
    0x6031b01052b18080a0e0a0b03040803040212030c120d090804120201021212070c02040204150c0507060f050d020a020f1905010f020a0e1011190c0501050310030b0606 73
    0x882e032041c041103500c400b01d880680b0340090102c1105000300c1c003088a000751040c14151008000141c204011160741d4403a000510f890680200307402811582c44031007201760b130000d036025035040c8400014082146080110200b54072107181c041c41c1040710701038086484150003c01208823640000d40e00c903850b40036600c80070700303d544000d015031241c1c0c41c0d035a40a81482030b504201d02621031030b456076002c1040300007a42c3c1041204035000d03400381c1c4d51100884054201c400201d0b000741e02403001048012840c00515584c90f500d1340d480341410b100d4106140b0300b0880ea40a1810300c482c001d1407045e4070741d00c001201c41c2450490400f41c0e0321030b8614412480d1110641c551100350044c103000c1c6024080405004440350702640082c420b072014800840100e11030300d00c0000201ea10881000e6407414544280704640c0d402c3d043c5080021106c103242420404111284018021020f4a400400107501a41e8000e00000c0c41e003c2d0030345c940008118640001800090300603c50540064a1951f07880304465 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 285921366 1250 285920116 285920137
    0x50102031f152d030e1915110f030703020a1812021c05010603050d0314070801050d0f02060d06050a0801020915160c0e0108060603010e0c0402070f02090f0105011706031b0105 77
    0x743c2c00d0603e0008006048240f4036a00c1c602030242d807001aa0000041e11846941242c294094200e01081d03690080070410341c44c402c412028800d550303004d41000086c2d4800c58441d20050307602c0710641b1004002100c010850300c40d62403a004107002c0744d522514014522075055900310f40e40584400b9050258022650041c001d43c00c108000c81000b20126403401c2c04d02c0c00380c409100c04001e60000700c5c4001401c0725120f0015840c1401004a45024080059003a0141619984645254001c5030b0350381d002c15035101d000d58072120200068140340541000a0028900840c20028084001928001c1107106000c0544004c111031000480b0b10f11038802d85039001010b5440e05640303c0d1540e031081c10034400c00c4c00038050040040c409003018095030000101a00151100e1405036040000941040344140e8201c02c450712400010380721008031601500b2880d2003842d440d85450001011540140004d8200c04045001d0182c9924000303900c1000c0011045500205440d440040307401d8060003d041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 285922616 1250 285921366 285921437
    0xc180b060403060615021506010e1215070212030402150c100903170f0f0117072303010e031204020d15050a0902010201050106020a0203100c090f03050102031f15 71
    0x400c003e0141d00c031204503000416003078012945090140d0312403d090094250002100380010100d40c454914209486070003001441841d0880d0035851824800d20407019402481d03009000740150100507d10f00c3c20f1000701840d00d9032826070f01140f00001d80ca0410782190502240c04000740c2030502c420080c0d22010402041018400d080042c802c9c014001307104214100400410440c814042d500340c41011040c040c06800d0340380000384410034034419a00011030280e80404034008002440b100303082d1000381d040342c0000056074101404c5410380d084900c0e040d40100203481e031b14a03004501d26807140d011104061007a01d6801d20309540c880c986450031200b80b521007080300a200980c02218801e000380d008009903a02d641050743c4d1662400e5001c0c1d0302d5803060404504500d46070f08401c402a0b0075180942c5120703038401c040b030f5202c0000e410440e4241d40120802c100c008050001445041545000440541c64401c06031407075060303100701d0703030401020000107404054030084074580010018001c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 285923866 1250 285922616 285922619
    0x70305090d0204021c051504091101110f0d1116050a03201503150f130207060908040b07030201110901091701091b0302010201050109110a08090f0102030f0609090a0c180b0604 77
    0x40c0303008080442c3c87c0d290203d440c00d00207004e13050a10980101036440900c890407400300c64010343c0c2030450b6102412291282d01944440c403003007407200f064540c00d02c0d2522402800c1094019051000002d4121303004403600c1420031140c0d40d0000450100d07034012404200905d03030901102d84880194064a401445010821801d41c59000c01140b01c1c4480e61800844200700d0b41c1000b07481c0321051070b03c030f1748030700300310440d80341c1c182c0503402000c000e8420500080d16201c0c640c1c070303a40c0541103640700500f014408100c402c18150203000b03005030b4001c0813000b14074281c1c1101c0007070000b00c064002e9045c094809500800810400d50210810756080380f803030340100320041900742c1c02c2400703400201d0042d400c040000500b22a5030013114150601c01a1150907e840a4011a41c0c000d00900b2251184190705005031404000c0c8001c0d07010301d661b603401d0107081c0780100030711a04000281c4000101d03800340c810304010132120012030080d207512010880340188500c40b1040908017030101d070359115000190 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 285925116 1250 285923866 285923917
    0x30503030114100c0201120f1e02090310050907030b0405010e0106080304170c0a0e07020a15020a03061205120d11040b210103080a081e041214070305090d020402 71
    0x4001102c80407a0503a4500c40300d00000c8403c070202c1c003c02404924007a1098201480680042c1081541c000000400b04190286491844890140d454a041e8005000c1c80c0f241018003164411038240c0c0824000c83c2801542e40e643d0348500d01c00a088170010a0200701044001c0d04100d00345d201d0103009000654442100355201e50051250039080c00e1002c9502a140401051100c0b21540090562000c680740092280c0903510003090207045016060b1000c0008400e01c00011654188000c01601c400155202400f01d80245d001690880c44000d544000a00006204034480104803002c0340c460f80084061b001030401c54a055288800200e03000c18211142000b0f416284006d170203001130088000f8074001c80110a00010303111100c200001015103020700c003695000b0501d51104100980201942c0c410b44400303480441d5201010101401202d92083d42c520950410710b5000d450082c540d98090120b200b49040f0902600c44070071540d081d0340d40e070783c1900e01001c1d5035504500004030700c58 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 285926366 1250 285925116 285925139
    0x509030d0917210f0c07060809160e06010c02030c100804061a0d1205070f140f03030c07030c0c0812121005010e190314010e0c0301150308130305030301 67
    0x5607015038203a21040b4480701c00000d02d07200320312045010024400002849060994840b103c140b000890412060644400030441c50009080c50b40d11f070011070401801c030608007400e1408101030055100c03003d01007501120100341e004002400e0a0460500d5840440d007008103c5010542c4240203214190390150800400b52240f0710840302000a80044455450b2903403020024642003503003004510300150145d14962a403080d1070910504040d1140d65042c103c0481a10444000391381d00b800c690710480410482200004c854041c50441c0342c02c01c11814039008803040a02040010664002803000808514000d0310318142919090b6049055030091a40b080030b20105040c08a800585d20070407007a0928280e410503501c4000ca00070510400403440481c14081050f080300020010005109408001c4a41c0e4044000700d6403070041050300d41070104440c0070301e00030390400066001305080c4264041c141d990100040f603c032920031840300004c04654000521600c40000003180c90003606 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 285927616 1250 285926366 285926369
    0x9120d0203181522171b1c12050c0601151106010b1912020d1d0c01050301090b130e160e061c0f08130e011508011403031606140105030a0c150509030d09 67
    0x50601c0d420050340c000a00c503040d21140c00c417208141480c01503000068001c0c2c403548caa032115141080c148507444211a061070402c0e803100c032458209554a080840d045804540c0e0302d10b42d0710107004258500300c0c044207a03104a07600d100e20060500c40002c12140a00c0d1901003202d003205003152640c0c040c644007401481c400409148149442c1d060110541000480e8a08584181d440d00c3c250792170180d003480a0f041d0880c030303d43d00031128110416400a50f02c1071840361a49000100404880040c010180c90050340004084100c44010407156031600c44000c9005c0320032540700c43c0e500000e030a11600891108030010f01c00d07000010342140c2031281001030070544500c059000101c0c0d9030740c0944174140640c0f42e5001c1c0420092001000700d154104211010042c028043c1c1e840c22800b401c11071590003403010115003803075a46810a10040000c00760364003401c02507000785007442103a20b500a4107080b5100e01103080d9501d40400071454440c10564400040150885660701503c4034080c01e44030b035070b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 285928866 1250 285927616 285927643
    0x3050d06120c08120403111003090f03080106090906140d080708030108060a0c0c020906150408100609050106030c020613030e1c02040506030102040f03020609120d020318152217 78
    0x74440b906000c400c046003105c0459034803c15241705940b5000074400720301410388492003416960000700f404030765002c1e91601c44500c80da4803400c840d8100040900b10301317000d41148000501e45503040c010172201001d1080c05180898400c11144407919001c0254442c0e034000418801c00072000041c00c0c0e41c002030850160500c0101400701150710301040f104140e450764042c0d03019101c0c1c00864032a0400301c00c1240c003040b80318102c034946519580d415117401c4142c07901592040d0b59443c10040d483c41e034803c00e13014000318941030140c440103100c000c0d80d0700006041040703100100980c607010940607520b044940b01000d4600702c40c20500320000c03201c8140351003041c0c2c0200d042c02d0018016203410f2088030152110802c0c1102080c2c10350b0240f284d542c005200b0310360484043d200d03454425000704144c180008043e13005582d502402c0000c80c0c120600700c20014090081481052203060a98098800ba804c61142450300001d00030301100040764942d1100d03508500701119401c99010115040b000c5821 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 285930116 1250 285928866 285928873
    0xd121107053a121b0c09021b0111070201140a0c0318081906050f22030311340c05060d0f0c0f0e031b0405060a21030f020f0a03050d06120c08 62
    0x20800e8183e80016104d40010f200a00294050015600c264090440c1c204007140c0340305a03070415685142100e0136032015440d00c00006c11004219a0300840540c14151002102c6091903400840a401f100b14404000d060010600700c044c01604151849001402c02c01e04848400c0e0b000e110308116842c01440a8410a05203000100c441c16912000c5000300c2c0c21000d00010025200e005003401d08a0500071002c2607220104d030900609440c02504140a0001000d121410548600034900d034444d120362100a45411891022a4517000c1502c2100d0317040d00c0c00e0750743e060801076110080401d244044034141c81e04803000606076101c6880000d0300e5807912849402c0c1c0818042694691084500c451000505505c400c02c0d0308141d0001074004401401040c542038039054050204442d00303440240c0e00c0603000080741810340c0454141900c0d803050000e014100f00294809880310340754000a070600100103040c00001642e91300103001803d40852040f00000345240200c0c0b182000d1040051510 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 285931366 1250 285930116 285930137
    0x303090309080607141c1109030d082509030807060606090f1202040b060f03010b1909031a0612010e010510050108010e0f0606090d121107053a12 64
    0x10ba8030780210b807951076482101e203400607800107580c044d29040c12401c0c2c40201401c40361b402070140484950b06000560b4540c4060001e0600d094844280141009217082c103010300c0403036040589109a082141c29690651406000d60300c800300c2e5880149400d00005107041800244e038005000c0c2c0d040c9581e140c070000d80d949e5090310070305503501075102c090b5010014100140b030030364010800644080c00060809541c6d02118140d0707003090f070100f0656031002808002c82e0070004101c0540c8852030900d2844141036072507002c0340206040c5100e041114480109645039520030100760710920b00d00013803120910104515010b01402d90390440c007030fa01c8002c00718071036020700b0b0141c1c16504400390014103540c074941c0004a45001610350350b0003010403c0343c01e2950702d40807412000240911038050f1582c0700f549004003a9031804007030844035003006205214503558510340007440701c0d480c0500072410581c44900c42e50351040c1c011800d448205107108070108105620079030030910742501c40b28181d5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 285932616 1250 285931366 285931379
    0x5090414060a060809011d100c180501030e10020a0908060901091a0709030f11210303131509051e0f0330011403010b0105040506031302010c0c030303090309 69
    0x103080541e103855102c0d0640e801488218401c680d038590000e1044004038903000c0d90a5200c5d0ba205131160716039629044040d0702d07004d0f01c281e4041c0710280403083c0792104081019181801c0386d0380c0300c3d0090504060702c0c1c1e01c60903031142c03081008c1480c2d1062590110341d0b8060104000d0403c2c8410320a81c1081c0c091500010301700350f03041c8681190341340c1080c800700f95800c0400b074013200781c42d000b01400c00384000640080f0210340c80700d14902c0d50902c1100304c2c0000c00c5500c401c0111850070000a0b0403110b000040c0c078080c0c41d8000c02038903000140180308116010b51450b10422005080361804d40042c58080b102c0140100050840100032079407006442c052072114116440381121801d10745558800c00c201440145190440d000d07241640815503c0c442d1101c490401c1004282d1080c1c6064044000e0f90403d4038080c455094520742c2401d116181c185848080f40303150000604035070303500000d0700ca01419a4000c3c04c007001c149501002d200101601c0c3e2801034000c2000d210140c000880078000031134803 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 285933866 1250 285932616 285932651
    0x13090302100f0c021b0603040b04021207080c090a1e02030714120103170c0705010807031409210a0c02040e0a0f050a05060f07230c07030f15140109052203050904 71
    0x8445c01400691540e030b00c40c3c42d00f550034180904102d030000002080400720300418030548019100b040e010300182e0740d1100c2040641030000e084c510030640ba0110500e52151800b81e151082d003600b81025031070ba80da8030f00a0b01e0049102080b0b4001ca100007940d07600d0054082c00a9042c0d80c440c0740c125a10704001c0405030941e01500080e1000d0768008141030041e58050000e25522241e14540400d07a070300d04044442d4681001c1d58071200c55440f1055030b10801d091004012040124000034a04242d604240103002005195001c0d00541c0d5038000071042200a0110340c00c520341004503203c07102410300c0e020759030783e002180598142c020315012034103400000c007025000310f0050f0380345e8101304001c02e0342210011586e035604140c04d0b401c00078a80701060a0003220019130081c04c0c1d0700e01c4100a07017041c0c800000c8918000202e0f9140004a122407a14030070000d065901c481c4002a41c1d0313507880302c2031452800303610700c144859650b403213603c04050b8441300034110340360203850a0100c40c2011001501 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 285935116 1250 285933866 285933913
    0x82e0b091905090c16060f0902010f08190e0a0605010605030117010908070b060111120405010311030709121703010e0103060c02010501080d030903020703080706151413090302100f0c02 81
    0x140800c83d200844c20aa4a2101030100000201080014204d80e55904000c554560250b00d400a0311008098103540e0080942a41d034001130514284510345448401140c00b07403102d920040691310325009408545c100060003c0c503a20820800182d41c441902030003d4000f4816401d8a000581d40c4245100301070045424a69000700305509104080e6149030003500010701c0075040200f12504400340820412a111942412000075580d490401d0b0004040c3e607240c0d251084041410014000403a501846800403651199200d0019171924030b480900451f800401c403c07190300c00b200105041d416200d200781200d10400041180a01103d426401e0740c50074410380ca030700c0e00485c00c041c910a009801110b40f240c824810342d80b0f1113840381c0d24540c20390084e120a4805941d24109144541c4d0310500003c050304140d01401500121000001c000520228500742450744581c4500101350080090001190315000d0074055091b188000f40001d0078441c01060044c41003510040045500d82d01140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 285936366 1250 285935116 285935119
    0x70804290a0c0206120703020408100605031203100905010608010504060501020f0604110307030609060504050601080703120f120504200402040308030a020c030c030d020409060b0a082e0b091905 85
    0x1420210350000c02c2c0c0d02c0c1d810259040e42c02c013804012101400306100e140601c140c0d0385450041e1901e00b0441011f05c1d0050080d01b11031200e04d065000e000c0c036034002512100c00071300d071172040760340740e450380c0481b180c46c186603004000280c24080086095a00040103034183d903070a80b400c01905688000487e5510062070303403408590407502c0400c01007080145200c503211009022100210b81d00d558004c211010902c090310310641e0742044c0001c0080500c4140e0040c910480203002003411920707004ca200f02490040030500c02c04000320f842d82801071441ca989990020300401c800d2600c0d04000c10600342800d010b02445a422482c60464607140c801d44080c2c94100a42c541550f0b41c0c1260103000f584240f2960040d4417050080240c0d01004000a02c041c0404003009a00c0741d183c58922420b59500f80c20001402c80c050182c50003041e440841c050307002d20b08609184614011800ca41c400b44190b003a001c80526403140085043c652000007002d008c5800c0e9464050300a04c83c00e050401d001501405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 285937616 1250 285936366 285936449
    0x414060c1801120b060d020904050903130b0313020a030b0a0c02120d0902040908130e0a0c0c20060a020d0813050705090702030d090b24090711030f070804 68
    0x1219441800400031100070310b200011303044200307030000e100d941080d040305c0444c13900040d45060500f054000d080e0000420300046040a079481c400081d25607042c000c1300c95122001c40042c000300703500311180d890150040c0c1001e800544904101c01649422188001c8080c20b10038900709191001403e1078406a92031022410880000301450140800603803da9001e41c55554000200b05080001d0107801c460360040001c2e030389040305035101d001c8000c068080da0b9203010112101c043d00b1a070f002100701c1d84003034251146403000143c40c00c031070116648940c0194011807240d420356000283c158100c3c005440c1da5800c3c0e9225058108041e14509000302180c201036420852070a0000b100c0d500102c007801500d01305001c100c446803c8400d41e400984010b011502881011160814180b18100c9856124055034146902088481c14040d10103820048072000d02250400240b003520201108001e5281e603400043c10702c040c46402c1030003086400442ea510780d103004034059840725000248034102 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 285938866 1250 285937616 285937657
    0x6080105100509160903050105090309031009020603041104020c1209040b0d11040914030a120501060507030c120e060f0a0810290c0f0a11010e0604050d03030b03060414060c 76
    0x40d19001030405280500c28885c0001c000240300303006007481142c41d00002c54492070b11030708051070550004000b15005142102c0500943c035004100d82c1d0158001d10740b0b80400400c4008140241b0615014103860b000d00d2203035016010342c0c4070080020100c00c803420701120ba000b0b03041004000508100400c0d000400c003182030941425080520341034050721142c0c2e030b85240e04042e5811544200c0d0000c000651600c941026203109100307442c090309040c40c0240c02c0450f944e502405c2d40c15080c2020300484c05429110010038895200181c01403c041c014584230744a110b581090b5070000c625000200e0000c00c0001d440d240c1340b000c91411500e1817070540442c140d042c0e2114400208007024402151020460405191810041787c0c0d50f018400307000f00302c443c8081c20083e505d00742c0fa12003d41041b180d0340c00c0c0c20003699042c0c141d50a44008440300700340c4142307528054008041201c01240c05004050030001030194020000c1054910307802500c61680d90120550968441c1c0c43c600040d41c42103100d0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 285940116 1250 285938866 285938881
    0x20c0c0a0812070b040606050a03030e2103090d020f1302090f01030e031803240405010c020d0e010806060d050123010c0b010e06030c041a0406090204060503010302130b04020d06080105100509 84
    0xc84c9504207014580001d681600c96001c03801444954006501003a10319600c0c200605000d07000e01c007003100ca05070031040140b850704540d80b240b0400003a18420180b1450003c00d5580e20300275078040f00c01c0100f0380c64291000d0400c41e4065003054407101d200e06986101d4110550080c007403124180640070103035251103902c50014100e246040e50130380d0984580c81c00341c041029038619184500c0e1740a8044050b500d4540390040c00c0d02c010296180854000f42415900341e80c0019501d481901c00b4280081950b440d500403c1c6240681d43d55036500c5410040001280c180d142041004100074010907148804907000548802c000c0b00001007006c0d0b8004010040710000d071520703d801c13540007001d55001036042c00000341983d401c054a00382d070880e05400c001041c07030f041c800c0100510742c4020a50030640303006400381440c081440041d020b00800c00355420f0815040e8407040004800520854442400029801c0288001e02031040150f10f000041035001040c48020f00071502c0080c00704010b41e54812 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 285941366 1250 285940116 285940133
    0x20708040e360105060d12031a040c170901021204060b0f10030605030705011803031407050a06061d16050a17090d0e011106070302090105070204020c0c0a081207 71
    0x109071140d06910031188882500e66400b5290404202c4684100e00d5140110481c0c2121806031080384034070807003a0103900243d0a5000b4002c0c101c810309001444a42c00d200200e9001d03074060b00c00b0ba2040c54544c98010301c6070044100060181100c0364407210382d44401c5900d00701e2168107680140c001d1200005000034056820511905202400100e02c8105000201e041c0342500e90321403001ca600c5020a0000b4201089024000c0c4403d29082c012042c030300b5003c070002c6240380000f40400280e007d0140304214814203c4a41603440801c44540008608100d40107050b0360003a084000c00924401e42400030f000c10250241c504652500c42002c42c000081c1c909600184001044c8011039000440c104184400c65100f031891034050000988090f10080030040160051410f1101c0f60188500c1c00070001400c03135001e941400d0043c2da614001c0f0060f1a50b00801c840203500900000784045001c40c041020703010154240c404000d41c54032000c6244e15138001c030b5452801c3c1c610a00442c6c01140d20071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 285942616 1250 285941366 285941371
    0xc04020a05091003050f0a0c08040b060d0b010b1206010504030201051611060c0a05010e01111b10090809030c060c15040c081903120c08070c0309090f09050c04020708040e 75
    0x7410038030314281c1c2d4940802c10102c000950a40440d40d100304210049a10300403080d401544030b8000c201510320820003600d0740c0c00242002e4540030b10f04001407100c0d111440b00050081c1c00c6410201d696030745000d4007141e6802100c10340e01034440c6802140d1194012010341c0c1c2aa9030507107500381400703100b421440381c05c2c100350420b5030003401380c0032401c80c0c2d07032606001403007145880b0001c0c04800000c0c0c1841821b440c144030031b406107030b07150400e1400c0015441082d070b080c403200141c1d00040082600704407840c000f06440401021407600c40c803034040219040041403224800c0d41039800d0190300c4003c00800d80100110786007550010821034024181c82100d55600c1741c410342d00c2207030854542d07400504e0100c4c40e6142070150320b14885000d040c982c2101080180800564050050381003203000142081c10150954003482941c41c1c0c0c41003003602404084024124201e800c100300c030031007254034001c0d0148079415521402008043c1c481e40c2414000c507840e064201074410b203420f1512a100c0c2c0c000000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 285943866 1250 285942616 285942637
    0x4032601120611041404050c181903060f090302010e0d120c051c05010e1503151e0702010510050414161b0807030815030703030e120f03030f0f07020c0402 68
    0x22a02c0b582524003090010300081e10903075401c44a545085d405000c1110400ba010907610201840081c1103030f42c22000410040809580c540040c20740c0f0b503d0082c0201554100804690500282c10342031003d551000c2085402603009010900111111544446501c02041c000a020481e050f0864890750000021030b03659107403003440c100c0c040480a441e4142034004600f1107440303400401c5025001070741260084910710449001c20060380019545260164078001d03007010007000100700006c001100035441d500d40c1280050b034580040001e000b01411654241d4120f982100030525041521a9040c2100610000742554480c505c0e004018000507000e00d04020860441c0817010080c00354040103035100b8010389480320b209103005400c0b0000200005c948545051200419680004800040f01d805041c4085030206034008039800c10307401d10080c2958480e001d03080044580020045110b06e80d0b103200c00300c0c5a1601c0d444802c03400b10661345440181d215444401c450f140980c0204180c954 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 285945116 1250 285943866 285943871
    0x91a100c1401050403110316030c061806060806012304050c07050d0906090b0f030a050403030b0a12020f1f0509011e050a0306050a12142103040326011206 68
    0x940d5074400740311000c074924400741d44480034041019040100010030340c841d80e02450511200810010354032030140409001c1000c0e1070300110510045520501a1201f511000480400c65082c008040c000798410412148545400011000b610307419507400f54403c48090240d5000c1c030340030080034040241694a0184c02000030f1000500704110303070300e001101612001165840c01c0d40140c8400d240350300904c40000c0c10400040e80d011901c0440c0d6220341c10f1180050143c035203080490040910291141d000381c0380c104041343e00388601d40340c003100034400c070742c00d0342c2c4e44000406001040c820040c42c4075442541400d204003090090020b000c00c41c0c410316250401141101e000341d200002c0c56030000114000184000589903d4055100505003e491b542c884501d00105025640503550020301117002c0c0c141310703001c901802d020001250030301e00540950a840798203018103540c42614210041551402040284981040b220348105d1030310000b4102d5038640807441c46e2000400c10100c40b95075 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 285946366 1250 285945116 285945137
    0x402031902070b01080c0d0c09150302120f070b1e07110d060504021c0503030105060706020f030f01050117060105030c070609051204050a090e060703020702030307060f0f06091a10 79
    0x40da540301501066000341504803c41d41360404d620705107194941228003981c1005101000709000c0354419045488000300002e440c0c1f25044040661072550704000d41c001130011042e0310391309000801c1e040d1368991350180c0317124039610f890064040c4500c001c010140d41185c40d46081120509000c0c1861600a08010000e4401c2400050100c941e10400702c03482c984c1c1d50184000c3d400c107807504102d2590214665565000d0940f1041d69a000503c1410711602c000502c1e03208000464060381c018840002c001622414125152405031109018250004070312900d0300000e003801121180c01100b060f1110303031550725400d420640f13a6206440c10340300c00341c9401e41c40002500c01c01031a1100824030403090386450402040100040e202c1d80b08070b02c1c0b80d0501c04402200c560210700da64001200b4100180d480b249440400d05602460034080d107451715206c05225100320325000490300d084051410001182c0310b010b407a044510001659590417440c00b40381da240e040004180d440303a0914242190b124 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 285947616 1250 285946366 285946411
    0x101509020409060e0c030402130c1704380c030c04051009050102102c0f120901021002041203080903270a090c02103b0c040b0a05040203 60
    0x240e201d54807100d412566494100111080d2401e010f812040d0440100e1450400b40c002803200d181d040b000881d21691038100d005064042e09034206002d1103c640b6151a16040c200120342d2020700c140c80380d0070a14071401000e82e02e03c14907401c2300c2110b241e510f50b1003511668000080c1e904010815031004104101c0800c0302c0e030b10f203031480b00345148a50f50001e00030f00300800203041c010b0f24103800005a00341160001c0e00c210344405013010b0b240b00c001507042d03089100043c6241c50440d10f0b0200071405440c0d100356000741d8000041c000d20743c0a80840740c0b0819404180012446103104030000b01441550040000c0d114110450300a0b44002c2268117000b40a1704000e96041440300801210005460012250411029504c0204560001001076001c0f070794000e9261200049085661030740c501d201c0ca1080030103441c0c2c2d01c150000c030424892030100f0291510000510450700481c0f4032403500803034918942030103590100100540100c000600d4041408081c0d00080c02c2e81c0c005c5982c4040b200d840 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 285948866 1250 285947616 285947621
    0x20d0b12030904060906050604051c02090907030b010f0b040603050901140c0d06050901031106030703060801060f0330050a14120f07050304030206040f020d02090c031605030603101509 81
    0x103103011406035540d010b2200402c0100d80c00c69001d90000c40c2009810030050380d40409440484205964800c1d0300142207a900301c56403480700303001394000c420100303018161000294600503280f1880500341c160b600e03404103004110141c840c00e80d80440802c41449024440e8101a4001d80e440c400462051449a10540c848504a0789464803440c041030310b0600c0091401180700520003a50114915415a15696250400180507500031000000822403080c441d500c010000c1c40f42d1402080300a84541412a01c1d040360300c0150f500180010300c460059455040c5001d0011070511405243e100c1c5000c147c413107402c01c0503820140010141c1d00c844140c100c3c0000d1420a01480541d011864401745103003903210003510381d43c101320b030500c10400001d40014000741c10540060000e0003200c0603200003580d40c08040d400039082440c41d828030003d900c0c8600918081c041a40810820841c104c5003150a030204541031607059200352010704d03403820300e948115410b0b0068010911207a8444149105 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 285950116 1250 285948866 285948889
    0x3040c170a050a1e061b18030b070302071e0b160315030213020c031803070b0f160c0503030714070510050d050a06270b01080106080612010e010c020604050d0e13020d0b 74
    0x403080800074a9900d05540301f0001c1c4044106103200d100000d046440d204400f54004019a0600d540000d6103410b005082010801903440d41e180c401c41c030b1015281010200200340c0c0d402008007200c844411403d40240282c15000d014100b11034200c13443d5030204140e091803060008800c503800c000c01e8442207010f100805207a210071914180704051842030514140540c1d2103580c040d0b40510100a104100d2401c80ea50b000c82012002802c0c0b005040068040300c07240e000c01d81c10b00c0300103907150802070074104520a08100d0b00680720690b548600f440b00241e20043c0610000e1010030800b0b000284591100d500110910000101c0b039460b01079405040140e04e50300911059104403485035440d0901030103007000402c0c80d040805526024010f00007880c0a40058824012908a04106002580701c6032561140c08000c0c007500a000318069200d039000c0c1c0d000e580d07500409255210103401070740007900c0c0d0341c0c020b02981032040420041400a4010420303250038030762160307400b00940e40d41191011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 285951366 1250 285950116 285950141
    0xf0e0a060c3c020d09090c1b030c020103060f080d120e1213090612020409030c080a120e03040608060603103b0907140a0b03040c170a050a1e06 63
    0x10100c42d04401e041040070084038000442d4411600c0004156200300e034081211101d034000300b0a10602d030004c1d65a800d60124000c2d41182c441d070751600385603000010b82d0000c0d00030380381005040d4682403906d24a400038001d03030041e6440701d0444141944507459908071003030300c058001050450125240d0070140034200c403016507000441c54058400d0100c00314001400301c6001002003e2501c1c40303407140c1101401010740304660700c4e00700c24107140c0104003440c8071991141890b60348104a2001400741904169140901031038540c009503130100c00012202a203000d5158294503954050811050b640000d2010b03c21440244001030f00b200e42c060401038a02283d40b8148030800190400447c0030302201c0d400640c0c050060a1158918022401c0c2054130407032388514642100c90404110000d041c0c0d4011014a54004100418880c1d401100300580307114695039594034100c0c0c1d09482d42c40300d003c00c000e499030300040307240e100141c984c1504074180403040401c0c410300d10058588408450454200343c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 285952616 1250 285951366 285951437
    0x1505010f030e010504050c100e09040201050304060213080d090506130306150306060902180904020f10093209040c0519231002030a0203040b160c1202040f0e0a060c 72
    0x9007c0740f400303601007025541c0e2072420420300d0550000044803000058406410700400101080602040b0780441e402c20704041804803102c0d41e50401c2c280c0c0c483c408130210002035000c40003c43d0354507200c402c0b268a0780c1d24144103000a815502c5910050606041c2c8004450050301d0020018000c4d000c1d500040c40800c80c01030b2a101c00f00c04100c00b40c0d20011110f44103000007020080141d40720803008411581c2a5116001039080300400d84c2e44000980242e003401910810244e50300084400d11040c074490080ca071340c14030030b0302028020490000d95005009010b122400e0101c0c3c1001b52054411840744a9030300343c0990b03141e000c104142c0349203001c1c0e43c0b801070070344455509081030000e00000030040d00c000c61400406090003900c2c4c4c02103000340d15070480700203030650707100a03403c14110105820480c000300300c50b0755189029a000d45003504074000c50510070000700307106080c42101b81c0442c10fa800381424040300e0362440000e058400c240024003101c05203110702100c4140818410018a40d241d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 285953866 1250 285952616 285952633
    0x30402010318020108040320011814061303030b01020102070b0c0702030607050c0c0d02030703140d02060903040f0302190306050109020703021015030222020f19031505010f030e01050405 82
    0x605450215400c00c1c1103920191001d80145d074890119503205401d840c0c0a0080c01e40f0b40b000c08810301480c400c1608640c00d011290844003024101012035900c2401c031002c03000c807a100143d44030380c0c080b1040301140340240c04100c003082c000e80012024000510006191401b25603444404000544031500840004038803c0110309007081516040a540d080050804403180101517407040c10581c0300d4029007107a125141151400c00080c00519400700c08450039607080b010f0142c0e144082c1c1c07903410061281101142140c5030102c1203600741d4801e8001e100181c0e003940c003488000c0c81a180c0100500410440010104d801e81c03280034042d00020b000035230b4034401424020300d0301074407041e00d0410900e48500c4980d40d510715000001101e40c1030300c011030301052110002403140300601c0e1008400d8000a4501900d01d0100024443c064100c5c0641d0200407100e0b20803402c6030000610902002c40d02d41083c40f0560180d44071800100e0b940c9800b240480c840c009003425950180d408840c1c641c0504c04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 285955116 1250 285953866 285953869
    0x50c030d1a04050c040605090f090a09020102060f04080d05092b0e06030f180a06020a050d2a0e0411040b0408070506070506152b050f030a08060f06091005030402 71
    0x10340305030841d012601070186040035013102e42d4900c03642c8901418807000040d04034490703d401c5109110701c03c3c014903000307075440c06016202c0031340709a40040340140628800100d0304a40c55442500443e00500c0f440d00300020303445000001c010103407800e4030a2207503000c001d407082d00b000e03007480b0808820f201d1810300c0c11049101900f1600382c080c1c200d210b81420300810076281620045a6800340001c01d0721501030f815900007900340281c0c440c001d4a0b0382e00001c3e10180c0d0341d80003402850400050f0600300b00d00d1000c01221781d0036a0b903d034012101c00080d82183c0910503c180d8a02c1c1c1200c000130b100090f13864400350801e0b0071f030380140c0c0b0060802c00045810003d10300d092011500514094602d00e1404040f940c40540742d18000b0103515412118100c0a1095102c4401c03806040c01c1040050840158121084102c8034151604442d54070034515196105000030040e1208070226031541d03100c1e0f0703c402e8204a000042d90242d503030886000d20040b082952800403641204030346440c2d0980d0790900c0e00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 285956366 1250 285955116 285955151
    0x90d0f02030f0705060910030608150609100303120f270b0a2a14030a02070501050606090f0f0f060720010c020a0b07060905010c02030a11060f010e0403050c030d 71
    0x101e40042e40c2121004225035103d084c125514050b007110b004660016442c0180d004260070f800180300b520800d07244d0a03420201201040c040c003000c82d5444030725907501e6444003a29006020040024071213440012900c80742e50072400b5a443c141c007021030b0f0104410b07026103400002c0e40c400e003031016031301c0b501780c0900285514a5421814621080c07040800828481195a044902030409184102c21211066200e084000c1c050401540019a64100200044041d401071482607429500c0c20001c1420b510700201210280301010301802c01e40002c181c10011814003101d851604451828000300242e90703008014000c8500c11088002c0110020504420340b425181b050390620880b00c07203c0700035a41d0403642c84c00700e542000150340d031079901c0c0c54200042c02c05900300410940c240301c3c4a107030441c2c02101500214110741d03a1842c00c90b0b160140030f0ba0b600c6003601d040e03109201c020018041c0301184010154854042c0c1000e80c503150b40d4040c041d1869001e0410381d4030150ba074000c141a55012103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 285957616 1250 285956366 285956383
    0x30d0c03110705060913140c070605090a020a1809050a052803050712020c0307092304080702040917030405070612020a021507030b03030711011704051c05090d0f0203 73
    0x340052842c1410000850424803035840c6482c49420324690242e80008140c000e2007449a00051982540c1050300101ca070a400017101220386505000000e01e01102c0014004445500101440601460030180e100403082d556114103455886125040106800300407060015100b5002080071003089201c4041114030342c0241068000c54103121004603a010f02034038107254111141c80d041c8140c0301c405919080c0b10500080d098040c0c0c01001602d40d40340c1d0710002680381c500c0215400d081d0120b010075105072040701e0007002c008061000901508103907102e440d205100700407000b88081c0380180b031880d640085070201ca00c1d074400e100c14003d0a40c444a10f010340c001500c010350600302510b002940b50000002005009114600002e040302c3c480c0d04102440280601680d0b81e0b160349080c14021040e00900e001d02103041411201100310040c16024421a00300c07014080c90180250f2007503401d110300d030828040007020b0010071125942c071a04600343c0c500c140244050010701c2d01c1414100000c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 285958866 1250 285957616 285957647
    0x1060f230415090e2d04120914011b06091505071205060d060b150f040503010606020a0308040303110913020d0510060f0c081b030c1203040804050d0f02030d0c03 71
    0x1242080081c0c4c0c015040c09034101c1c900302160217019140c00c1000c20460b01049a03000c0010324a401d020501070001c80d9440881c0040d501d44400750748844c01e8001d4041e020384118006070b20003e81244004960800c409034922820010450548588a11281f643c05034035020115995a051002041e00084c3c2165050080c0700240b2981c9881070010300d403c11403071005090203840b40c102090543d40c2d900166480440303403982c561144990503564025820500039a0301943c0307400c1c07020403c240001104503c46a0540c1c54400d103039aa43d4044000d0f08105050600c80174040c40300d8101c07565546004051000303443d80040e2a0702020402d0303025a003025015259460300c5440a104680e84403020103844031403810311101f02807040c42c054000d445900300326603011001c0d8403030b00d01d440000300080c0031680741c0c10111103200214042e03030081d0f48003c0d18005c02c003032030800c02003140b4100000030311015401100e0350501144141c000c40d007400c1034210030030002081c00c4d84c02d07410590403100d1400440704 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 285960116 1250 285958866 285958877
    0x3091c020c090c0d06030605150414270c031905010f05010320011202040312170702030d0b0f030d0909060b0c06010303030e0708010c02030301060f030b0901060f230415 74
    0x5600c0003144640038050490004607030002005000b40d00c0541244000f103130312500400051a0278180ba0644662680200344510f0501c3c205081003080b8812072405822508eaa0b9503510440403244854640f1426003801c0d9400381c402d0215240c0d506205c96000039210040080c1051506e03d809401c41c0d81e040c5c0e00c03014203861b10005002044201303056032000f05148162220072000000142c862900108440203010b00008004c401c002c4114240c4c0ba60401d2030300c89494042500259004039501100c240300181c0c4107110704a07408070141c020036110000900302141d44010400071900f0680001402da01103411078504100c2145148103c10003080304005441c05c0c8003035019a15203840061202a0416444446160801c00c05000c5400203120781ca000b0020705d0000d410180d1a600f0901c141400300d490750300704940c0c4900901503c00040d6000741058030580c01d200e402e0340d06186480281b030410610501c4483d103254038200c2030a1004469207015119458800319484484210070f62804005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 285961366 1250 285960116 285960133
    0x10602031c0203070e120102091008160c0206090619020706020109050a1104020f03010f051003090506040f061b0e04060609031e0f0c06030b1002010506031f0b030303091c02 76
    0x4044244112228000d10740540c2c1c98840400c02c40e00350b011040b44581c481e001da003040e200a074055000303002500080c1d40035800120301001c180c0d1440320449006120400058500800718440c0351140100c0784000c1c42e041c100a1034002103007503500000c9035441d49c02565a0340050880c0c04225440060442d403009101c001c90b180d4906071901c004841c000c1c10490000c00709041540d8a030196064007105146041d16036956a400201c045203910815001c3c080703100100c5001c2e486030107056070003904040180200c2c1c03266a6103001c01030807140c003560243e070703515021100006003101014002e00b80f9540c000300030407884100004c0b506107500030b13001d020620340100005540034807032a018920302c43d40d401e440c0010382010f00b545100ca00000307110035111880403035090303010341c011004c840094619200c0c1c500080c909034200c81c4152451507141e03111107003072040c180c810000c107a040e440f220000f003644900080800d1443d0001c2d25071002d681c016234400c1e14210703100c1c0d0504d9a019a988020b01640 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 285962616 1250 285961366 285961387
    0x90f0603070b0c0c1f080705031006081f12023f0c03030a05030403030b03010605150c01020408010603050303010314030a1b02120d050301081006140402030402121504060501060203 79
    0x1e00d240c0c4980c07821200e010840c83c84044003401042075002015000000d51803145d1540520b030030314800402d0100c0c41c1280482c00003482441607a1244904400106a55081060680712603038000c02511910085103c07038841340809022181c0144403101c0e045920354014810441c2d014051082d181b00042d03540100d0258442c010404405040b56027045005109a10103107410304448540a0b40c05105c00a19039007a194002c004502c04d5000e65410065034022034205030030781d061813250580c0006c000c2c035220148100c1400801b201d5040000040c5020341e241c4019081d1501580f00366100e801c044010030500203803103038440140b4645c001551400c07001c0880904404a030894860060011050310750071512095140f0110303810007000c446c0c1722014100001c100e60b02c24041c0c04010700406400c0140104c85000301e41c1500d00b07000b0089500b51009041c4002504000d005a84c02442100740001034013041c4201c1c41c00d042d03a0407074084c00e89840c0c00d003801601c0040c0d10980c1113604c01c0000c0140c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 285963866 1250 285962616 285962623
    0x513050405031204051504032102070c03061107050106080601172b03060b16030306050d0201080c03040503040f14010917060a1a030d02011a0103050103021e0109170c090f0603 77
    0x2c208502c012184240c0304c81c00c11501d050f404075481100f400d04141444141604003002110600030b071245083c08028040c0150240c0c042d110008101c030f4203402007800040c2598002581068103508683e08141c0f40b91289401e40d1341c280d1100d07540c1e42108005005100d044040b1540e0003135000024900c55840b41a0245548003400d880c00f40000c01d0384804904900c02d40013240100780c0031110f1521580030316060303100c1d0f52641004501080ca411000a6203090003036941e030b803ea40584030900e159841080f030114980c4010011945130208110118004080080d03210243c0507480455400c4810702e40054198420354200000d2036200c01182401200000307205544000e000501061451440c02c0c0030b4403150982a4603503041c0201c822003604661705500c82824610700c00030301c0302c0c0d1a0780300e00103604507002800f010390092072251108441e4803500c00092640031040c0752201c40b07560b0b940100754488440000311462030304410512010b5240040345190814644e80c40d88440e400c024000994 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 285965116 1250 285963866 285963877
    0x60f0609040b06010c0206180109091109010311090907020307060f110304030309210203070c090c0203030c210a0b03060714190e0604080303040c060815011125051305040503 76
    0x80b4140e650028140781d1180c0c60b8203603155400703000340b91120b08143d400d2406130580442c1500065200200103031081e002e000e48100240c0181c156450303d2090001100038043c031100303850040b41c00300b141520356120a0704842c860411940a540c4448043c9024016070f0740c080d00009038282441030b01c41d29001c40d201180d400c20f5150800040e44aa54070744815410303010140480c20b01c845001840c40a0b40100003409810f105046000034240c81d095180202c40e0700050320300c0140e01c14030028001090a00050a02c9940350b010702c6820140d0204401d14800104e80d2021042d448020100c0c960401b00541504407445040510801c60340100c14019405003041c001300001c10001d4031460070f0b0003080ca9107a081c0010340f0041d0741e20744813945596640e10a0342c04449100340740700c0004601c1c2c42006114010700c14800ea41500340130704401100d4800e0301c10782242c401d000d600c0700707081c9a0b00d918050003448052180b49403a0545007504010380e0031181c01c1c1501e40b45043c0800c01001440100484a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 285966366 1250 285965116 285965123
    0x1060f050901120c030f0903051b010608070308070503040905010605070c05240904060b030103050a03020705180402150c031305120a02150c0309180a0516120f020910080405060f060904 81
    0x501e0b05150441140a00f41246e9460081841d0040810034183c2c00b034002d041510a20902000030002000b01c5400c8412901c030790700f0a900802c0091001078100e100808459008800b1242080d0300c840f107800848100b81d004401050001901c1400c101d8003410b00b1004140880d62030000c0345010060312581800c0c801d0308500c42000103242c804990790782d44803070050700c44041e00c1900e940c0c40307240071a42e40a000d01e0950152083d070200250b00d00e80300c410b00300515498034000101c1c1c0c55681c03c1c401c040704800704001c0d003150140120b2000720030070000b034800800e290b40c2410100d45454140100001c02c0400382c040d81e0844040c005c090f031101c0d03c91464080068141c10707034805045000e20700314058518200d0348030018040200c502842564402e0058600000800c459100c204c2d610122500781c02200d40810b0542d2001198900395500180c0002c1509601616183c410f20000300c2d4462501130300d81c00f0070020b005210a00c0300810a055210380c003101e4890942c14400000b4074003000080004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 285967616 1250 285966366 285966371
    0x160302031e09100f051e010b0a0c02030a02100c170a210905060f0901140105090c1b060c0706060504090206070f08120c0904140601080610050702120601060f05090112 73
    0xb002904200300340c660a42c2c1010040002d104900c0c3c000026107002c1d90b0345070142c042d544900c508004e00001450485041c41000761070b10746c11010540f800e0b400c003032041c0c2c4e05000300200100542c4a44140140c4e0400310350b11200503d075140381107800c50056995118881d201441800e05450708051501d024042c000c0396101122008840750300075002c281c0700140300d801600140480d070354140318080e0240401034020b100c01526002060f440003802d220709a80b1041060104000e000390030010030f040344580232081414240100400d00c1c2031400d0311280f001d580c00043e6001030103201e01c01c14016080403201072180703500c4c2d600060620301461a010b011803401c20804010071103003904882d14103840d05800e1101340340c1080e060382c0d08d401c500c0c0d000b405503041c455441450000644014451541611496001c0c0c64100a0004840b051401c00b424020301700440c4000da81c60a01c0440c51111101c000c0540b9810703c440140344050b440e1120090000074050802141e8000d110214640c1c50203400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 285968866 1250 285967616 285967621
    0x1508070e010c050319030b03100c0f110313032111030304081b06040507060e0102010b09011e0504020d0f0e19110103090f030c05280803040f1208160302031e 69
    0x24198031a01c5c0d0010308020040c810b8494071034040c1c010781a002412800d44d9101d0512020100079101440350000000b0034400300119202d000d045e090403413500940c1100c1c103040b409120440a00415041070350aa01c0011406100181070054200c8051291500d4402c414406001980d40d000180c4014000710001c10181060311450030005482c00040c81100c001c0e088c03a0030311684654450107490009010344565803600d5005015160303092001078200249a0720340003110500308040031800c2c10161328284000b0702659035001071b00c0411807954001594001701040007080b00c8007841100c6007500044901c102d44180c00d016100a160000482c041c002e58200c0101c00902c01114020059040b0140c0e07101030603800480003141741e100304200ca40d031008500a045040d2014002e00ea00c0b42c2001f0035000c00160241c0103142c210b07114014040d140507003981c410b240103007000548070010750040d04110285404e49030070038010301c2c0c038202145182003590110041c090b014035001404a01c5002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 285970116 1250 285968866 285968873
    0xc03041403160f1802040602061302030102190306150c050316060b0904050f0d0318080d0207140607080c19181a1c110a14160c1508070e010c 62
    0xc42001482c22040940c0c010f80c8851180380190054001c14000c0c11071483c0305000321095108a0303080d540035030010f01c1c942c0e0b9041c1c080d10740031645c01c0049815540900851800050b0090349440c403000719100030441e2410400c511a09154034803003e420001903840403004201d0100c12500d42a458154003144060b041c20401e010700b54019203290400c40c20300800040c800b01041c52030b008400102520381144a40724210b00b0390b0080d0200081c040000c1d40302c40001604000102641c40320080e025080008546802d2003200c0b01c07005500e1542c01801c01c00c0040741d401905194007040303c0c00d1460501d990380510407045110f06041e6000d002051040c40c0350661414007000007003030303510340394002c0580020131300b2540c0d08041104c10045c0c3c500c6040d0704203212107000f8003569a8901a03180e01b0219200350490314240d480f030031412401410004032009942c00700101080c64050b0307403202d01061034440724510300c588880406041218003001e00030a10361002520305060000d182c0490000d00905 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 285971223 1107 285970116 285970123
    0x120503120705121b04060c03140417070603020f09090612010507030b1e03060411120109030518040e060a0e01181110211a030619060503030c03041403 66
    0x111007401080c0c03180172140c04548c040d2504c0c003845000300e01c503903c035030b4040d4003c0841188074101501c4150300c10080d0000906c0f491804520300302c01c81e4940700c158043e134241d80b032050408502050031561a050320724415810800200098181481e0103001881002c1d44207005d030107a03032007040ca858585800445200310107400751100d50f03201d17941d0850000210002e0f0341d021414580c0b40161820074802d910400307111341c69080c2d8502c40c034441940300c2038120305810701c500e04088840c44256000329000e070f0820014000881c00c032030a88103150150917183d903440391403440500c80d030062010f03118242c1c65040b002d0714002e00381c0303040270400c65200801c00013143c0c12201410005d9000788407984461250304442021000e0f1844500c0003d08141041c0e44081060050742c406880c043e085120b280010502100218980140100c5490300c1c0c0c0124400e094528503400d0030910952000c0c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 285791366 285971223 := by
  have h0 := BRFrame.cov_init 285791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 285791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 285791366 ≤ n) (h2 : n < 285971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
