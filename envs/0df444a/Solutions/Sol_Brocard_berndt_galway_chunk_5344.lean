-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5344
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:33:33.525173+00:00
-- url     : https://prove2.me/submissions/7624210e-bbb3-4901-8fef-0bb15f800dd9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 960971223 ≤ n < 961151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 960972473 1250 960971223 960971239
    0x30212070f050d05181e0a26030f15010201020a2c09071809090c1502010b0303041d0601030b0f0607030c02062113020d0618141c08060604050906 64
    0x80c200b10400d4500c15240d20000302c05d16400902c0c03c3c0001d005804400e481081d0708445080c51615650f150100d041d0040e00240304419401804807151041819107981208055501d181c14104807080540c03e948402c080351982c008207883e540148210b440ca12510384400c400c00c892040118000300580c400d5222000c40707000380744c0032038481c01440da0040441d91544100c1c0705200f040e6860718505944090310060514005001080002c034601098800b01c81000f2828002d10030280c1c0540f03107804500d07406100c001400905280c9801881d0090108144080700c65102c180045041d80c0405a60070351040c0510441402494118002d0681c980f01c0d04203100700640540004805410410603021451003103140d0451070038181000d13079030195044648030035241103500030848400c0100c900801d502d903602030008204c50038400220b43d066004d592030b200c884103250490b496640c980130031995080f0214201d130805000f00300e0b2602c1440003516541c2803614140410007548000381c40d440d00704c050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 960973723 1250 960972473 960972487
    0xe0307020307082812030e0313080a14060709062a0606080c0105030403140304061b02070f1710051f08030909010e16030518151006030212070f05 64
    0x801c0c89100001c2004002500d6801075002c0d130b00070807882c100b400c01040824200700800060144071a0420301c113151500043d421a01040940345105048542e0154640c440c2e0004003400c00194068419110b0780b100c620394240540742c203540c0c0505803004d001040d4081824011144111922100c0c00300ca070640ea09503072112456030005011210064070a1510390342d040c00301c0704080004042a9800b864143e01d1403500b52001402190507620710380b00d024002001c030303040c8907150300160803107008582c1807030403050010350207580c0d84480d2151041034046060b000503841e114410703500450f410711026100d100c011420b11001410018006c20300e02c184101b07140b5600c4030140f0b00f80003600c0420015540c0e101d94100300017256134160f00c03040c1c0c08140d8134108070300f84090408010034002c03503090110341ca4030b504454403a04035444c104404984240c3c580d061001045a11181c081c500072940c11010382e4850208806a100702d1146095850b03e160210301c4852003401c081e000368045150103030034005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 960974973 1250 960973723 960973729
    0x6100306090c02060907060507020105071104060302120d27030807060609050c130e220c2102090c070b19021312060f0509070b070303110706060303110f100e030702 72
    0x803101840d500503442134080100c020b1003040340d10080c115604009080141940c0001e2281c8503a000007020f090100040f08801d407a6a04800701940d40200b01c92200d6503c608866070b940b510250f04000103103000d0000c03a41100f1011910120600f00c140c003606541151181e4410350701815045907166518040002c90450314403921740a000b41402d81c5540300146c811030500c24045400c44c1018102000c00e002a805510380c180e8004042220603031b41494060a20b603030050717113640c015001d0f080c40012030703901c03259919980c048803032085480f42c990340c03900c0d94901c0b80c0e0701500ca0010815081207003c1034083c01c3c092a800320303500c0c0351400540f4000450000540c2911150f001c805800a12900b00c001c201650061940c8000365030300030865840e005440c10741d134840c0b512841481c8000055400c0902d4400e4111055000048030000c0d511001c5150040c02444c0714481603001403810001910f00ea8001310f8400003035000702c40146800f40003a100340d0000e0401c103000c104e40d0b210800c041b0005072 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 960976223 1250 960974973 960974981
    0xf1509030a12081914070c0302010e0109030305090f0a120e12150f0901092604030605040b0108010b0d110915040c120605030c180601030b0d05010207110a0e0610030609 74
    0xe8120340c0c07282c01d01e040240b048240b290018a40391300c41c508002d4950b002c0440240b4441e8001c2c00c07807421580f01a06824184d00521601101c0211942410041d01c145a019001240514a2002103ca00f40c56505140d606c840120000030501d650100b01e081e900c43c407480d003110070003600414102249011a1800c0c1c90000302034141d0392014140c10130040000401c5508a42c4451018000e01c5404001d948002c035198500004032246a104000a0752a16075072040d2009161f000f14104405d007482d0400c071040100074440e80342a503080905201da00d041001a440c0940e074440d0842501200070020850340040c002c26010014000c0341090045176520b004080c0f00c801f044e1208600307010850183c07000c0d11402d0300024000c0e40181c0c0315014603100c1d0910200490048202c00c43c41d52a1070300100d010300714071030f091940003400b0006401404419801000c00324494203010072000c0080003400740b042218484c048402c2c0643c0c00040b00303420103018594101072149000902192074900503400c803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 960977473 1250 960976223 960976253
    0x405130e070609060806120313030f200105032802071401050601140406080603030c2406010e0d0201052206020109020a0906032d080f09010e0f1509030a 67
    0x251505003440c15500148600d402070501c1c0e24000785944d00303041c1c001d00050005080e040c080e0710b201644055030803042c401d44040710750740703040e403074956a980c14a01e045040c6618240c075900004179042150019100700c0b01c03074043c03044c0c40d40340c210f80d0740c00c207406149a46007100380c041c80e01e0001d80c03280600d818402402628072402410300010501c18595003181d40c01081e07a818840300412041400c1110b1040c2d801300d070742910701414150785240c042070842c0100700c02c0110511072060704a600c0200d903e01c000e141c8030501244412551b44100449032181f2442d42d40e40c0207000b17903200c500994070410080c08680c1c600700c0350f03845060003a400030380b69000a901c1480140d55600a807400c519000c103401d401426900001d205140c02e5841d0310400b00c043c130b2032031140c0300c07540c1005002118007050310303403c90340d0049451342d01ea500b44051142a5800000300d01e001880401d5030f05a14548403102a10395a4050001c96084104d031044210943c46079440c65458030a04600034000384143d841c5500c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 960978723 1250 960977473 960977509
    0x919030212120a0b0406034701033309020d140708011409030a0c030207240f1701061404080316060c021b010c0206040b030f06010f0c02180402060405 66
    0x10503e001091403044504001d8064840c40c280b80d410404030340c0d040700d80185c00548010403d5908420300d8a00c410212880c0f8031942e80800ca103280c000da11800400c14103c9001d90045480601400c546c6484440c3d450840400122102c4c2005c01080700c41c1c0c45441001e101404000305600c036070319001c1c01030f000f03c0176065095100d59000d22100340b0030f0082018403546081c02300001d040440282d616070213040190804c0201010ba03c10915208201c2c480041c031003449904001480c1c0108030b40c0090300c0141d144013007012010f4460059110301c16201582c140300d403080d42140d0910300111110740003c81c404001101c18040030424080500c010050742e082c00e03244407404829450804151042c298804c42513400503800d115100b28450415441180e007441c003402501614400200640180d80240d441c403140401000703007030384540f640140140c000b41c80b80b9070425503641081f900c80c00c5c1450000e410800d080d86a840c803600004807641c200784014005d606083e210310100c2c4e2a01028811420 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 960979973 1250 960978723 960978757
    0x10020a0f03080a2c07080a08040512070e1e0c03010b030403030b0a09060b0426060f13121815050d02090d050105070207060306120309050919060f06170919030212 71
    0x245044c0802503c00140004006401407411980f07030604940114420315015007559400c81030000e0090002c040603284441e04501c06003810203502d41c0c3c000d110314200b203c40842c0c402090700e45071041c05030f0f8103e9900300381003403440d9100e40d422409030002085040d00040105030100754100180512400b4001b140b6080d40c40e14a4504001224101454540744060803031000e0001584c000c01c0c815404420381c413032001c85840b010781d0b1861035100c0140c09403a00e020314141c6089194000015101d85a010160246450322400e5003240858958004070100340100803e440c100d0440e005040c4411001b0043c02041c20661561400e40d10304035440c40040e00001000d107d15034040c49014080e00412443c5180300c03c09550103800c800321801014032820400001030003050880141003080150f2000c00e0254a40d942c804070b0101c04030740240d0002c1080100400c400d20a1004c1c150b100320383c00e80080034444805070440d26912035001c1e00303a046009500001200b000369000400c0b03a1800701d6a020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 960981223 1250 960979973 960980051
    0x2130b16030801090504110105130509150f0118090903050903030f0307140a050a050708130305010203090d1e0c02060d0509030a1e140906090411070210020a0f03080a 73
    0x1c0c50382c1c80c1604101c444a261800b48804601911203407c5030210030300b001991003a980040d41407200b919800300c1d03408401c0c0010080c051031241c12079180420190380810560b03620310015144e40040141f07007042d00074001e50802c407541705134000201007400390030003d10301000100442d0840d84480e44800d14002e00000b44901c4a6002e00040341c0040c00380040d0f030404035404401403052240c80e0301607040040c0802d4403400c0c40440c900f02d4008212680000c103289641e4505240030313400071a540e4015010f04c0c5006000503004450304415104840c91030b00b4003e0340c1401c2550040b01c07080c41645c0204061118081500413441a28003031250030004503100c0c80100c40040103109107019440c11144100e5098005c0d64000c400450200341c07030141c00b510303030320904007180381d074043c00203450303402070420351b50481c00030b0042c004002c0d00380281c510850500500d0703002e03031351407040510041c01c43c0d10000600c00401d200c3c10310b00303411240300b0801240308001c1100381e215170400d074030036012841c102a03451 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 960982473 1250 960981223 960981227
    0xc050109050306070804080f0f21100503030f1e0307031b03110d0f0e0a030909050f0610030509011419061719020307050a032102010218010302130b1603 67
    0x180300401040303000380070034604000b00070420440988001c0031440c0c00f24400b4031803610003058481c1820f00c2c5c0032290300d03410a40071a44a408080340c0360103020601c0c002041d211050141c14000343c1d240540250326261102a42c4805940706129203ca07041906c2c1812404040076002036006129541e00820042c41d4130000d030303443d45030b015081e006262500408082c100300c1202a180c00d00d12000300003c072420f02000781e201134040150444144d000d4401e6002c00c02d608200381a094030890300003005680e6900c072003000b00190980d0215801680c40304424070251207600007030ba0250581c400410f456120a01300380311400c058800d01b05180c3c92000014443c4060701c15100104030048ad00040b500c030f441001a02c51140c005161b0400c100c441010040d92001c00869000300750250601403599036a0406801c80616070041c000e2142c404480d0115a80c8140296001035010b414502c0f101360010006400a6202c50003101114030142c0e00015011019400707013814804032150b0800c0b51000f4640 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 960983723 1250 960982473 960982487
    0x30f1b011802090105010e0d06050a1401080a080906072a0519050916030e0d0201020c1b090114041508030c0f0105010f05060a050c1204090f09150f09050a0c0501 71
    0x40c80e440507500e4004000350f91019641070450b8020700f4041004010341000c1142174280c61800b42c072160420003800b0f1100d01660091888030b0025a126030a0303626081503641300e28030250042c0114070244144d081a1030004000c28409214407000c401040d107103650044c00e40c5040482c9446070003010b0f001c0040c0c0c1000c1100309040050030342e940d0384103420600040d51042000d08400c0402480750101d01e0818042d5100c090404e5822003200c500c8241e00c00001d000c2c2d440181c0c48401c0307010304403031103400300d00c0c1405440e0007800041070b003100c50f0300342550f4585440d04680850b03805602d6035038034200051600c0b001000f0300b558602560351000101b4107145800e41d51f0210004613854500104101c3c0256019941519800c64546075a145030340d50403540d81c014001003030680d00492500d0300c1070340e00c0c60008008844002000780b10101c000c8039200c0846511030b1015189101e84004088260403a502100d0586032065000803220302c0e588425240c900c48034000c4914160181e0140300e01d40e00012 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 960984973 1250 960983723 960983741
    0x703030309020103050a0e15180a060b1011120d11030702010c090f03150203040503070b0f040c0f0501052d160203010b03030301031a070c0b090303041112070b0c030f1b01 75
    0x81400100c0349403111503900d421042030708120159a10104d4275095010750000c400c0d414079411111001c0b5141045801030070380b012024881c076502903204020320b0068004910b0205c1503005000150161744400b9580d0380807103e0040721956485200c00004070040155006800c95800001c1000c49040050f100c000f2035002840d02c85443d5004000041c031401d22800c081910260158590311031b854014914050b072070b0000c200001c5002000031001610464500c00c6008107800f0711010b5558040ca4213041003030107000d0020304204202c0d214040801842d0645420200e0b40210340e4003241c0d0441219000829490f8148058201000541c9802d01072241c108100710055440c4d545590f036031181c0c1003107070181c1e15004145c003400288001d003d005940f468a07042000071000340307001e201d61602c0784d1007240c003101d658070200324030303030311410a20150469644080c00900f07449090810101d021b0300440903141081c4410441000c519040801902c4d00c180b1151840c0403144291340c81e03d0966000329 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 960986223 1250 960984973 960984991
    0x403061a1905130f11030403020d0e2707120f061e0f181509020c01050a060b0912030d1b120908030606070f020d0309050f0a0807140a0305070303030902010305 70
    0x1c0018006540d60010001854409210000f40f9940692100c00034180c402110050100c2c08070410051540100ea07880c8a01d4203607656203c45001c0d07d00708092981c5040300070803410320081d0701e218200240d1504940045c2c00341025021401c2c10904041510800c2071420320950301c0d01400c01c514444100301c0d00d00181c01441c2d50700760500b8074802d0024100e00d40300e000501c06018075a1008030340c0c1e50b40030411600e51b44948d40c121581741e0060034007075801352070305064542c030b030000040040c06c4030b00c1800f042d00c600c0f801c1640380041e5941001072012080c0130901d000d000420210081e09040d01c0f690140000d80d0f441c005401c2c00250b4050b043c030000100316100d00e41012610700c00620004112640500100c070032035103400c0c0c1030408200d41c0100c18002908503404802c4102455046030b0840204d030390468420f10036540380414000c60010901c07600c140f81e48482410300c01e8195040e84c4c92402070016054095103552600c0b01460f10a0b260b205502003a500c9450078190350f818007810758844000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 960987473 1250 960986223 960986269
    0x3020a0b040606361e0207060603020a052709101404121e1206150e030709060302180a1107060213090c020a030e0f1314070309021807050403061a 64
    0x20070f184043c224903c1002d2040036503c00c004c017807002d2039070307000440301000d2a000c54a401803440c3c0080108020700040c0d11581410303070b0010f12807400a90a20580c0b000820355114038650142c01d004204001d810300006002d220014020780e5082e104c2d4041c5069003070b106400906180c2001c4130110043c0700800c00700401c40c40d140c0a0100801c442621140c120b140044000007001280e1004040903005499070342001104000740c0c2e40e00030242d000404048081c0c5040c25594800382040724040d202c0203412001200b2a4070b80c5589021a540d03000c40314820120b00300bea8040c41c42c0142c0c0c03000300126540d56000c2241c210b03008000c0620000b074100d060b41086400c010042c040d5542c24039060040030084801c4003c0c080c2c0d00e542c440c091303003280c024206951140f001107864015000058030741c040e034050b0030000350700e1511a01a40f450704e034024140200c51117010010010030100104401c05121080000000090680c4071300c034041c1000820b41001c00c0500ba00304408841f080718202c00c03040355 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 960988723 1250 960987473 960987539
    0x21e0d0f0b0a0b15070318060804141c080a11030c0706050a05010b0d1a0604080109060b06030f0c0d1b090305190c060e0a120b19060e040204020703020a0b040606 71
    0x28010b038080754101001e504c02e031079029520341100d041c03207c0383c0540e080c02c4030300d90f0004103241c2000b00d2501851089852079084402742284a50f0351440800742a403a202c45c01d0b00c0e0f200e69001b4400311780c1188401c08041607244100107508410390040d01c0003c04408000713a080d09014082c440c1c143c01101e6030f0f82c140a00d501d0822900501d014034080d460b48035542d0000400d20030320741018000c1001002c0c1c40d2944450780c4441050003842d400b80262285402d2a000c4400707490160122486070710864901d502c40e854075251203c0c1a044031503500b2a00c0e940340340c40140da044072101610104003540d1900304060851508904100b50034070070810200d0750705e050745c0018050350050004d440c113074501280d180f80d82200050200031190b20104859062181c043c0500c130441032290320915565a42d4407000280344902c0c400c40301035208402880148102286c01407500350006e14500b8000d01c12601c1b0504261104200807030155011108140d1f1100e00300402c41d03280301d81998402c8544c01c2900c00c40c0d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 960989973 1250 960988723 960988729
    0x3050618030304020a031203020c1e010e03130b07152901170c1815070c0602070f032405090106180c02071202030f0604030f140f07021e0d0f0b0a0b 65
    0x40b45000c000e0501e20104a1f102940d4481d41c141c60990300d4000446251000e9801c650041d004c0001a10395030f5420000b000031807640000448801281070046c503540180380505104031500b14900480f12410031020301d88550149004002c0da100043c5280c0c1d4040700c240e0000003072100c115640394140030085100750030101c2c0d00c120306d6a01080040f4215a00e03c844041c081980c0b41490225a201072640b401701c010003850b1024080180c030a0460700d502d180c50320340607039a901041c814010161441c40003807002a40107a01408110a01c0030703003440356080084030300c003a6034088071006c8583c0c2d0b480348100403a4254000016102552090400941d6207800d00203441f440301d40581000c00c3da0a02490045440401482c0d030440090010340b40d803828a45001001030114201c27400004581450704800d0320120400c071010800c0c1103003160300c0d0001a90074070074411f14003e910807503241891143e8019868189001810500ca65404003a50845161100c4003000250050b1540c5107021550403142d2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 960991223 1250 960989973 960989989
    0x3160906050327010c02060a0525030f0f0204080d020105070e01090302040e031608041d060a060809010f0609060f0f05030a03050705031c06050310091e060b0603010305061803030402 80
    0x881e00802c4840c51292101036590030301203d000c0f40d205629040f0803548060f0f011800034081e41d110384050045486840c034040c4030141c00d40c902440e2085000500340b81600135400012140082640440d04509102541e4202d80081c2e0041743e103038006143c1c2000655084c891140c4c4000c4500f065940998080d00090062500c0e00009000da583c0d4003001d1021001002031702c00c01c4e00000026820140540360a510030381082c440d614244c03500c0c503401800c940001900340e210700c002410901b016032400c0d0040710000e5018003080e40c6550790302d6035840f041c41140190000380c6018040410054504440001c45074003c0d4480380340d00c4410b800c18401e650b40442d0000505415180c82522540d80f400c2443c02d40c03281c089210038052111406d03006d0941c0a030061070485200310252901031607098505015180001001068646c0703070b812080000507040004c03281140511000601c100704280070940039070007030300709903000e078404000c0055145007940d59003090824440035600b5030070158003180d060 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 960992473 1250 960991223 960991231
    0x11706010f0512030f220f060c030e18040b010f0503060c121f0e1b07031707141305041b140a1101090312180317040c0f0605031609060503 61
    0x80d0f200016920503d981001910142001001030a030b503841d60102c2c0540d1844401c46202404d6500b0500040ca80746000188048409980700c1c250030b07051039902201d204e984403a15660210b00e000104c08150030300340071188100d1095002420950400810102ca000a9400303540700c2d603c0300041101407100c4406079900700c001888013200da600c8113400c8600c8035445089148540c01daa000018900c5100340d0341c075001e007030f021a102c154190350010a40e114414441c015011802d4020303401012013000010980c4040b1300d14000701d900b910001e0201c49a0b011198968404144030340c14400340c40d082c441c00045807402d14090304260038140c00a000120100c2345034505020115000110b00c0c007800d82e107512180700390001c0141540c6072601030402c4120f060041d010601c0e2a42461a003600904445881303601038590f5074820007101d5134903006000040040310080f90003000040c0d1100c2205900d0080c00058a80d10b8992a02c62404800258405143c03420004001804c00080307800c4001c480d00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 960993723 1250 960992473 960992479
    0x141006080304180e03071a06010509011d01030615121b120c03060b0a0216050906030c0f2107240801141207090f060b18011805031203011706010f05 65
    0x507580328860784009118400c04e0350044d000004000c0204050100103c901d5071008000056585911004417110301609568601207400c5085988080c0f400e402c6c44a0b00360014903003ca41c40c2e4075070a030614501d804078602e002080300035103840c00006042c040d160b40c1c0d6500d0031106851038000300c8000d00480d014181102051f82e10341680088510940080001d04420500a5078410b42e204000b03554140b10441008254121400440d09240c0039941c0c0f401958001c006021a48540b810000746407041c0b04815840310201c0015100c4040d1030319069407124142e000b41c0501131a004251003c102d41500014400d41810307150501103805c100080c1c196803c0380f004100c0300a035000416800c000c1d80c1c070314900314420a0000140740c1c0c2140c001c01d1060010345000e000307283e41c81c4c40d07200d080d020360001c1d9682d103a071410004c2a0b95118210109558000a92004c41d081d50744010a01300380110960807194200040180450b844010b440b511120b0400c000b80400d61602444c1e1030480350a006080c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 960994973 1250 960993723 960993749
    0x11041119020106030507030c061e09210213060e0c031608091009060605031618180812040b060306070c261b070509040b010302060f0f07141006080304 66
    0x600314800d5102e64095640407080b24a46900c03410813200341c1c000e5104400c0054403080d8214262001100307202d844000070740f607600d035490814007111406800c8503101070982040072000d20141e80e0f00030391808070f054032800c0003454508040c2c1c98030b003000c5e0090401840c001e04100303110302403904070180055401c00303213010001600e680410a0400802003110500c15040071740540601c94103902c0102100c200f103049031140400c0401343c860840302d0340304040c40741c11300d4058000791024a410445100a03105000f8001c4952980d58001035049908140740146c0b241c000c0004101c64a045250020b000320001c0c0402d1800d200020801070508400500781102c00c0f076004080c0c03141070814001200c41188054a03419482071b1041380e40c1030420400801d10070480001810b040070740c0a10301071600440b2020b03182c0e0a540a00503a0b81c00390030440350110b000c025000e00c88090001602d9224401c8100c0c5502462180c01c5038505203000100205043c540f40040011440000c111030803140b100e80569 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 960996223 1250 960994973 960995017
    0x18060405191a0109050111030f09040e19110a15110c03030408010b181603020c0a0c06050d06081902120721050d170403030e2107110411 60
    0x91050916528500d01442c10b10420a48071003080c64658005002030382c0704100195624011902220b855402e4400e45c2c10800c03090a01c206030000070203041d03001400206100c14201c149034509411740c00ca40203005c080202140402c240018500001141101c22140b658142844a08805441d010b29010310503968201c0220707081c20711a070340d8215002820342c1d494a07a140540c82c040d15500d0319803442001800e814116030084103002c54010140105c040c40120494181a0000d500c072042e081e03c0c1d40308504c1320400065400d14440064241583c0d040d03150304156808605480840e001016550030241000d085032100c8030903200700d260100c54114402018100090400ad5a0f0b0000200c8040410201c00392201031116028290711400807281034030402601200e05c00b00e040c00e10500310289c2030106c1c001c00c0c429003003040b0516202054604070b400c0101c500411700c0b031b01d003402c080c4a1030101c0c401051244c6484403502c8840c0c103a07014401204100c0750140c0c54401c05449104d10301590481c070b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 960997473 1250 960996223 960996241
    0x91b12060e0a0c090b03040b1609030f0311060a0b22020c060114030d0f170c0c06091b010302070503030606070c0b041d1f05010f0212040f090b18060405 67
    0xc2916254400040c00d02d00020006000f402c00010085203941800041038549401228071032600f0010919440d2108071280c04000b6417030310b01c1c80800c6859000071000c100503d019482c1280319482e13034804102e020320032034205007000306928100b504d440143c07000d40e00c80c0808100448070b22405992100440c8440d507009008100010322988600000031455082d402c030a691082021011521070191841b0b04648481004c68404001560b81860078040410742c1c4180c0d400c010000d0482e420400420026468001d080300c00d000b0b16030207041c4d662860308100d45500ca080d0401c2c03800f540f9201075512056509c0c48007926140c06043d0008410702404070b040364100103400e01803036142c0e581e5641c2d00b502001000c0080000500c40540340032540b00c0503c50000711640d58101ea80c0d07100c4501d0300c00103680ea01c04200002c002c0d400780c07441010500820f0750045c8040c11015a001e03041500b05200c200465603910811030082c030020011044160400e6032840d880341f400c550201c3c1d240d40f00700072 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 960998723 1250 960997473 960997481
    0x30903080a1206081605240f0702040f0516110316020a08060705090411040509061e0a0e040b070f0203071101031104060c140607050a0806030f03030c040807091b12 72
    0x19881c0a185050000b0420f104c010803180c550b03c52181400c1e5140340c0b5401000103100488581c07102455010502901c151031181c05010540103c48616003013005039004142511071118102d4450795541081000c2d02d0900c240b5549642410301d00180c40150024105a89120300c0705c07420444200070007908215036481c007075400500485e10030b46401e8107089801800903000521482d01c0360b41010100130b940704d501c106550232035500030042e07280c83c1c0b1500148540c0002c0744010365064004c044210a0986441480c0c03130042000c4e4503440800c1c82c09050596061201400000820208802c0020603a90000550340c001c1c0d080043c01c141c0b4043d150041c0e0041140e50a1514091000b0800040c1140c202d0350000140b4000c0d142e0300c00c210880f00703040c1d40300d00e0b085a02c031000c140700b40408a00284911041039100c48042c0440e100d0361443d54034145103400444070310640e500002001d00c2000070901421700201000c44e400e11084000d00340e1091030040003807072541048030041c0001540b01030303508 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 960999973 1250 960998723 960998747
    0x20a0c030e1201020a0815041e1806020a0921050705010f020102041505071b0b0d11040305103204020d260414060f040e0403020f12090a060804030903080a 68
    0x13156222440000034004100440d0b0250a0f0303030f80d4410b0524181000d00514100c07a85403100032011400e0b0f40085001000d035118181600b039002e40c0e00c0c8000403503500c010900340d005600c03407000f554a0048100d114281d00d075414640005420b4030f290001d4070020742441904c809080005000145140c100e009010f00e600810100319540400f545958100c0000c0c40c407035001c0e41c22850031840b600d00405000030b551141d0400d180f0308006206a154040d40005114074850030741505c0d1a5807600c8091600002101c150703205646c40d0300d0010440c9002a02e040e040c0c407a07140b0a801d9000c44440c91240d1a8001c0029000b06211a244820044210300d101d41c100078015400b109841c00d10288081c0343c006000c0c1c4104481500e603540c11a00e44201615407048020300c2e11807910382854070316919032001030012401c0d0301c10070000e1a60420144282c0510b40c109070075154950604100708081d6020950081d014400d911040c0008603a001e542c40040d00c0c2c00094203a901c000401e011240582c00070 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 961001223 1250 960999973 961000009
    0x60f0607120801030b180718020f0d0b1c0b060d0221100c020106050f060f0c0d0c0614060315070908030a110c03060c0a0e03030d0203010b09040c03020a0c030e 70
    0x1800d072040032a080040a41a41d000e45000d0300c0740c0d030b1400b0203644015600d48020749690f0003541c0412202c00c944400383c2185a004501505044401c0380703035441c0b900b140d80c002182d1902d90174142c141d814407100100389521441889a4905015151407401d040c000e01040d0040905040d888159103542ca081c4030801c1010a04202400034003858940f82c001034102003400034102510520b155105026003130a48900900390780c4840b148004008081d44896940c2c030107601c080c0700c2da01c1c480c03074144095469070206e07480d402144c000307602d0001c04a411400d40010020b1520044c40082c1e00c0007e000c0c6c8010341c545414060b2a180d00f60150b03403480060344031403007521000540a160607400758280041030954400c842c0340c1d00d2441d04142d103840046070304030019001440303c49020ba10031000303c0d5420300e001d0140c134a40705502d0300c240140d91098100901c044400036142d11207060601c20706260410624003181001c3c0b030000300801403001702030058200035600c0644501c84c1d079030480d0386400056075 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 961002473 1250 961001223 961001243
    0x180a14040605070305060604052b050102030c03041110080a0209040b04020d0207030219080a0f0516060e0f0106030b1803160c03030212120c030a15140307050414060f0607 75
    0x5840c007200942400c5075902c0020313061501040150030a0801e80d030554070000c000700c15134440000d4080314041020140003a03150708038440004103200f8401517001c3c051400380c590792480c250034820380001c49081c1250180c81c0c1906003400c0300d83d101400f82d400049010b80035a0301d001080000c0c1c054025400302d41d40c49440000c81c0d10031071b07645500801c1c0e098402c4e000d481e80c90710043c0d8240e43d01040040045d1804600300300040c07000e48282d98203004d866071801d10310b0500030443d01c000a180000c0a04681c83c517640d0030300c0c0c844442d0810035000c03c4003c88000307008050442c0d0f204160800040d0000480e520320360518001c3c95414015503080c04036620010801d000d803030420345624205480190301500032180907545400000b0b046580020078031081083d10345400003801503039031006003881701c01551070300e58005800d808114440200024203207900410022000c05041c40050750101344141d203000d104140c400841c400070765101c5011210f58015044810101d04140710b0140010410500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 961003723 1250 961002473 961002481
    0xa08120f03070c0c090606110307020a0b0f0c070b04090509030a020a11040204031a04060b0307230a15020d080c04050a09092901060f08133305150105040302180a14 72
    0x45d6600031004c8030516038801c440034004440d540d0f103a10500700040d400c24000c035020322116210b00002c103510503004a8483c035194100003240e0038698140c000800c91140014104062011030044d10340094044010354580311140d180a90b4400d11540000e20030800c011220156517035a034107440c011504800c8501040723444915001c0280c0c800c5800312113180c90708461540c50b0074002540000d40d10180b4090b01c0d040d682803000c1900c00d10b240b40803980f10344211310104103c03001106426482c0b800e41c0080c42c202000f0640a404001e0085c9012008201030108001c0da1751000d8071182141d1120741c0001c0d0300030307050608110914400b004101c00494408103080d103800c80c0043d0604030742490f41d03611340c00510302200300c030f0701a0b0507608095402088644000070940e442c15204410020001003c0103900d80900309608000c100701c4511010350b03400412116024010540303820b04000d02c2e16525040c155030005060026400141c040c010101c1c0001d05c41d010303690700c950800480c8400315116850 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 961004973 1250 961003723 961003739
    0x140d0617070f030b010306090602131d0a051005010c050f0f1005010803040317090102010902041802010806120a080d020702040f0203091006030b0106050c0a1b050a08120f03070c0c 79
    0x48040d8169664800c11000080100c001d800719020307a544141525403903440c2d40c81c1c02002c0c25420794103481d40d607800c000d1084030101d541001c40c01484012541c00440d101d0010703d000c007100003043c141c10380b401c020400601000404da000151b5200f4202422403030007904051b841e001000059012031710401c041000c001500081d851100b030303a2581e0074400c5a0301c2d0140035449019502c00103180d02089500c80014410300740181900c1d0b0b030103200000303858040e03070001015142d4601c0c0c050b0028040c20700c21411355a000705e84550000003521650380c2003000c1c0720300c90781d551241c03100901420300114a800c254a4540c04030b039000c40d0002c10601c100000102010001e6009591042991062820b105803221480c003504044a410a0300510b032a880e03e20262215809000840b03100d0107414003580000e900b07440321400285000e10085845420f00d418400e0001464000c0113840c1d0107112884000c501000407507090039403004055442c5d0300c0c1c100007507660b40c0c60a84000e1a4501e80600402c0c0c1003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 961006223 1250 961004973 961004999
    0x105030a020f0403023c011407021c031805010c0f0201050702120a05060a050f060f060a2d021e1009020d060f0e12131a07021c290601140d06 62
    0x10886800703c1c8180c0c00040a40d5945002e801b844a0205035180301e40c1101d60741c494050680750b8005446006010305162442d182458054811000f05e906004a040711004100c040400f4140a0804103025029616410341401c1c901c6c0009040000c00500b0504640380c044210300c2c0300c15007a080369500e080f40d03d0401d45802d01103843c0d2044c00c0c17425001a42861002d050700e070160760050141074001182c0414485a61700038007000e41804070ba80441040c03080a100b8128a00741181f4801104c40c2001800a05003000c200100254a80b404000b4100181c0480d0010000c0102c010024901c0010301c040313080d00f08400d00c003811851900c0d02c52004060181c0140f84140e060006031101001002c4c0b864040b40203c0718114202045400144403400006c0c80404420300400d840c0741c1061802d50005141040c2740c102c1c10481c0104014020402600035408030842090361130b02815610b9601480a054030010700450403c103008664030740083d40c1104448070b5000003401031041d15103ea98040c511 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 961007473 1250 961006223 961006279
    0x60913110f073e09040302011d010603020f0316090b031e0d022122170703120504180f090804170c06030f1605090604150e09060105030a020f040302 65
    0x640035943d07000e400740030b040d55040040702c0104480b410707841c0c0c140c1c14410f5000c40180304800b13545d41d4580c005000c0c62540c0d030024218098000101d40141103205004608c00806132950299018059000d1036408030500507081e00c00c030f210005000948003001a1030a4004025004140d51200c400135540d00045002220585250201c81441021039203501d04090148c12401807610140610f000200c0040c1c181e001000b41c03407000d0004c4588441607081c40c0551100050050751001400f001000004815484410043d080841c01d0606e00a960102c241102c003134007944580d0380050f403403d444154131a1000f9504003040780c3d144c0791624004251161428071185952080100a29040c5017036012644500000c003419105a21280c0303181000e01e0300484000c2c10b0000500c0742d9015605c0329005480285409074603540c048110034400307448840a007407080c1c0031300c0003101002142d90f00041280d4001300350803c01aa80c1745c5820001c10b5500030350308003d41c00541424860b000c01c41030151000a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 961008723 1250 961007473 961007513
    0xf0f060f091b030209160c0b010e010f0806040c030b0415050a0b0a121505040c17030d0608010e1c0e030f0105060f09131b08030d0c020c060913110f07 66
    0x2012a0b28402c401420082c0d1000079480142d160000d9005140041c03840442d07116802d00c83e000000301c0e55441e007000c0e003d0300900400501e09004200945070080e21000400116000c0c1415040a44490081d4019800060078020700000450200040c2898080c09880011001c03c0035050074000000a02800710381c440c840c0c090008045080101054440b0003940d00101a0761030800c001d07440009044010019122403240d510005204500700d000300d0108500100038540d24520715070490300700c1e2000e402442050b890010181041480001c401000740e20a075046010884100707001c561a458204107650140601000d1009001c0150059401640101d520728100c950030400c2c1301301e20004071200080703607804d00c5204000c83e03403018440025030b0301c0a0b040040c1d651980e018502e0340d80700c0c3e4200700d451507070ba003800c915283d41480103041100c0d013121003e1038107410784001850444076126901c101c50781c420601003030308046812a54440e60381200251503103c0f0741801a0300c0d0800c2059155 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 961009973 1250 961008723 961008743
    0xd02060108010c1205040602070f030309020103050c1c0506030304050312040305010b0f030601060302030c0d051e0f240619180e190e070306052a0c0303040f0f060f09 73
    0x240703100c0c10b00840241010540c2c52030020074000c09810013902000d003043d102154200801c2c4040350402c030712861428081d0300c000c200032417588001001c46000038002c070170b00c41041c0403501c03d0789442c003400744050f40054000b141507103c50f80068103600c12644a503070f161140b040d00d106501d2401d4060011240142d00801030001c402c8148031105031107401665054118200510841e8041d501454210b0303003210341c0c0ca041c142c20300714103021290191003003c0f4002419141014145092604c190302001c0c051441e40c050078403a00c12242c0c800140100e4444181d441400709a0340c0f500003c1d9200e0300c1181a00705044401e180002d000440b544428410f030103040103002c201350700c04016260003a203030306505081055003506141300400c0810f40c1e034192401030442c0000802da10740a0680100004c500c80740d0121880c0041e0000007040101c20007040c0303424801d902810390044150391303109401c550300c03602d018034600d407601c51042c0803040209810703e06203281c41a10200d9002c0040640f0030580d0b42 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 961011223 1250 961009973 961009979
    0x8011505100e060703030b060310080d030b01020d4b020109020109031205070c0f090e01050412111f09030f020610090e1515180709060c03050415020d020601 69
    0x10600350500c1c221020a003500c0035036a081c24590300901d00c1c0d078000c2c540000d0010310769000031140e034404e450340c015a01d41420300384440c4800307100f440440301240c201046a0410040003030744607030035105500c0900121100341c45039030303650f01c122a40d8032640b5680c038441e48206655418907030070408000303000c1000a4002804150051207000f040c00e405860b030340c0e04e16145036a20410040d2a130036620401405000035000111440710a81c00381ca256144082114281610f4500300c07a01304500c009142e0400c0184004100244032810305044140f502020051001d21102d2400000640030502c1c12110401101106015444107442d18842d07914034808820070142280e036060240c03001429007250002c100302e041c2c80d5510040007040f00074207a8842c00b2046414204101d0101d0300000700c888440c0300c000092629050b9103607901d00202c10601b0034100300f503000b8940d411602402e0184401c0703a00500c18507009038181d500170a80d100d102420110f850030300030f480d0016005100090300c036120001c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 961012473 1250 961011223 961011229
    0xa0c020f0a080309301e0d06030b060d17160b0709030203100c0e0f040f06060909150803040603050604090209091e01050c07020f1201050403050c060705040e0406051005060408011505 80
    0x100175010801031412460811a1221200750b41c45540c0d2a120242c2002c038641c0f102d102c82c0054552403600b884001800f51442c00c1c0502003810040205201e1100c00c1803d800040d403441e505000c5c403140c0c1562036101c003e16054203180b60002940901000700b0901049502ca074000d50b0502501c2c400c2d0152080f00c811000c4140590f4a003400950205555001d00b0400d401c1000c01c10792501c030010404244180410300d41d108484a0f40c02c490f000030781c1e102d401d110302c070705c58001c0c441103504155440450902c0d290308691030340298007a0b0420581c07a80c0204450f40d440ea041401d889400400d040f2803810107900d1680c1c1e03030905041d00844400c081d0b05003054000b040c45641d2148441602907440e0000b00c2c3d003000701041030045200c4d4010380801c06005030400c2403150622507413080d00c915075a180d00404252908000038110300402204020901800030b503016020380040d03000320085050307111100c0500264407150072850304078402040000c0c10000541200109910700d10440126035191418 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 961013723 1250 961012473 961012513
    0xa0e101a1e0307120b01092301020120030c031009050112060e0607090501052808010602250509040206070203120d060f0b03010627080a17120a0c020f0a080309 70
    0x2038003000c1384120240c180d021929400004e0300810516040c9079180d1070300d03c10141221240158801011404600010b0b542c092045480d030700844050030410100100501485120040000059000201c0800e10b070241000704c21010380041903042c08550384440c1d0b0b01000000404060307621a080080c031010071140407415a0103190541e0314104154200401903800d84d0140d048040c0701564043e90a582c03000811168070620015a141d0b111540344c408001d1828241c01c40f1005204050400c000c0307210044100882110001d80b00c0c60000da82d1400010f1040c00342c0100650503000e0043c00034400c3d84003500410300b11150120030400070380c580c01000c112060f180111101c4007001c2005106050140400c0c040c1003022583c08040041150522110002e4a034480d2040e0f03803001c44401d00700492006014501525462281e045c1203d40e40d183c094240b0140c0842034107070f07803110070750200c0b071082c024555224044000c03200d1341116031805c0f035420f6004450082c1d131070040d03019000104004040e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 961014973 1250 961013723 961013731
    0xa0809010e01080421050c062410080f13062c0a05060408030a0905070f050112020c030a0e060c03040623040303020d031a120a050c01030b0a0e101a1e03 67
    0x159100341c0c5d042c0303500c0071051940f004222106012040c4500351241c2c004015542c0316a0101e14a81580302aa90400d00c1618100369024800c0c107060b04c0740c2c45e00c140c5c060709059010401d140f444040c1d40b9607100c411076403610510080d00460906002d125480d081c075980a9114483c00b800700a0812072080817a112041c1113030003006a003258004c00c004c0707031200000d15000b40894200040908440c0d030b49500d42800c550003c2615550f8000800041d88c0013110324400c044586400c1d840e184414920640b203204500f000020321176001545040e98880c481510580c14264080b65078450712030501421802c012000b252441c10742c805000865060741007a10700f1a54541c00501141c51081019400b820b208018000c045900044417202d90b0b42e03070030010740c07002180005410000394604140d414009500301d101e042c941080202001c0781c0b41d8801700b8040350901864030645803100004072250700d851764003030071103403001d4401e1000500041c401000c2e94203d41c6203400300286041c003400c100d804111 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 961016223 1250 961014973 961014983
    0x10020c0607080d1401080d0207030c211e1b06050405010809011401090b010807030b030304090c111e160302010503040b0405010b0909030c014a0a0809010e010804 71
    0x15050069905190001e0210315124515090515140800c040100c420a10362149180c00902c01040700d142c06000c070f548282c0c1c00f44060030046080d0b0711005c02044d4980324004e1406e5481072001c415922202c80d0b40c201c1c40d80f241c0d04844100401841c00b1131010001000c0d202ca110004203528a8440d0070102402c482c59074039118101442e03d030041d2020040144024115500c4079403d5906c00c1c402443e00e806444c0c09000040d414081800040500000604c220141341c9492030082c203039503002050b50100d5540c00b42c04903103c07038044400c135079650b600000c10f8001e00c203011a40c1070880441c05084031070040f500864007145081094201c034030f0b206110180c00b00c0c00030000714001c07034249010036074130a003e6000412200c034a00c0100b44084801c4580c0d8403c0c2d0004130b0040240c000a01034800344c2180d00e5482c58280700301c01600026801000710b000c0341e491103502401d030101d2110301078a103101404001d403041c0101c1400c0440e110352042c41e02900161402800d012103601650f41d0b5801a9046 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 961017473 1250 961016223 961016233
    0x702121e2d0f010c021e0610140604031a090d051204031409030a111003020f0d0e010b0604081c09081005070e0d0c030b0c0906030f06060d110c0c1002 66
    0xc07955034101441e55451441400b884482d203840e20024014403003900342d154000c2940c205203410310781c0f80b4221035000b0111a040340d400d000703408504090840c00c2c0c500e20140c4030303442c01c4814000b41c41031003142d00040003008130b500300210341d106040f981445404a101a180c4504516804403228070a00a00060780039615010a021070721a203601102c41403160010b0389441c505100103403504141310301c11910200401d49200d142d051001034819070038100d040541c10321075a1916800e00380556200c0c80f48150b5520522111100250004d06131454042d04003542c1d03544400406440d504d18030480d00034218082501640740b4411404d0340c1c02c03108582c0c080c0c400f100300141c0f000040c10340a81454101b000c070081244446e5a0910011840303881900b44095651841c0383c03207004c00000401c0304602d90380521111b00d080c0c450038226079000704c012445900c60794840e00050b1003406515a100891780c82c000b4407480c1c22540c5401400e0010400b02120200000401040342903000a400800143c00c9 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 961018723 1250 961017473 961017523
    0x91805060c07021536030a17040911030403030e070303171504020c0c01031b05091909050c03010905090c0a1a0408010f050403080f0c0316050702121e 66
    0x1003030701808070148000e060405014030340e024441180c118110f802000340740d0128800c0f0650300310104608041d55404958882c0d1180c90020391144020b4201411103042c041040ba91b1103018401c07500a00180b010030012062202d004080c282c02c02c0300c08801080c42cac0303a80b4061820380059084100c96059482d2507510b095419202c4c4c80b0080504008500e43d20907050360316994603400940400f2030130b81300522000003072000049c1541c2002100940d00c0d40b040c40b00c89403a9038000121000503d0555410003507130000410485a42419030007107202520b801e0a11908203610300041d0704a03030140710f080c46551103003035826449014142c019a80003400341000c1041c402c00385104031209c1c2d90315101c5404d10740d980d840e035030940311461030400545544070104401c05410101c0d080e0445548522504180f80055810005100140c0808100219081e1211040d84518221a140c03603000d04844462550030000c655503001e4001c514011040c848400740140314005111117214414030740d00039100c64 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 961019973 1250 961018723 961018741
    0x91514130212011113090501230d05010501120605060105121f0b0301030503070b0907080a11131514030c010c20191802071203050c04080a0b0109180506 67
    0x2004200e07009030200c0d002e00c0150400780f00b00e00042c0b141042c003d81c2c548914030810100002c4c5e82156920902d080010302680549420a00911814091a8021b044000b001030800e042d805030050941d070034000040f80d001014800078141d20300c500c0d0144070503151500191030a000301c10000aa90343c1c3c050024012940e07828011010304118602c07881c501c0c0c0ca5250140046c0d10036001592181e10024a02c800c1207990003001d54850800406040303c9801e2107412911064491000781101c541001011803982da80101600c1480f081d0204010031555109a0413001100b0300c109000300941e803007240c8441c1404038a00f007010605a4845010300e4996580400c1100b20034843c1d16914140d00c1e14051a44403003001032030040107006c466118910740170340300c03801110440f0550502c0b40140402c0b40024007036181032614000a06001ca8583c0d1010000d026a003d81d1b40301024511030001a01c0c01d0100e0800d80384d058517040b040c2806002c16955042242e0081c03080000c0290b44800005080b00b4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 961021223 1250 961019973 961020001
    0xc0308060402090d0506090f060c030c1315030e010e0303101a3c09060706050702120a030603050c04050c0a0f110102030a0506030610082112040501091514 68
    0xa000500f058221404070713803181028141100d8070703804082441081c1e40100200341050041000a1400c1d103464044c034002400060000c0c428503201081900888903002d40c0344011f05a08944090b040d11b8058005028001705508070419519000941114074404030440748a14101119605070a242000d2229031484041500064640130b201c0740c80800641c0d602c0c200300c1d40c8100c10460405550188041000c00d100600c3c004504041003c1d607155143c41e019920b9084c0c010200180a0707582c454264184080f40794400c0940340001422505550164095410f49000e2003c4a901400e0b40341440102d900a1f1a0b9490542c004c0c0020703118a88150003180c004405481d1800284020300c842c80c0c00da0b041922032440d000d864a007044124102001410b900c003200160603c6602d00c0c0000071501c802001d85a4400b0006201e01c1c002d090054804881000e000008034070320518182c24503c2c020481301d0781c100c41d1500c0c0c6544100280300a8010580b140410003809003042d110404110415 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 961022473 1250 961021223 961021231
    0xc030c0204060e16020d0c08091206282717040b07060f0b011e0908070e01080f0a030f030c030608030d0911030313420e0405070c0308 59
    0x10144900900040e2500e0041000508441040000d00d040035040d0700d41d105120094902158010801c070480107034015500f208094129200a40d5224104042101e0355210100007045204120078803120403010301e1059400c080308000350300311903c510b0340d860940c0c40700c410107030400100c8000074040484444003d000740e4403a0007409000d4014003500801c503081765020881c8010b01149590502c8014050180c5805995504010001c1e207200064421a04d42c094850030503411401c1d019000e000b8003030140600303190411904000c0c3d6410b514031a04000f4091018203001d860020084014001028040c0343e43c144c0740c1c0c81646100e40c000724000c101c1515034000300742d00d82c6d0b00042e0126080c801409070200ba1600490300312018105000c00100c4041414025070040000c640454480c852440659045503146410405a051450080c0b120800c818417082d562594124902c0e00781d680d0a01a00e807140c88134558000c608040000319101140d280020403421281c07071001a10680800741c0c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 961023723 1250 961022473 961022477
    0x20c120115080d021b01050712030b0414090f16060f0c02150a0f05091806041b09030c15051b010e0d0203070b01050a08120703021908120708010f060c03 67
    0x301819841c4120018040c0c1c00106282c02144681d90569418810f1130710007104100c0c1c06003400322010008040d440b602a0181011400003600a103044c0f094020074400c1000500901042c40c1201040700003910542c4c00541038401d941c0042d50f8240d010070201000381225030003000003403070410b090301c5803c0120070040401064149a00c010383d01c1700855255031401a00c41c07a110392000b00c0c0035003260780703041c4001e0034448103014441d495602c944840c54100403a48a566007a2a801c0109002d00242c00a02c0c0b001c0380a595105003140d4031904c80e02c1102d01900c0c540c5411a50f80000300d4581c03458450800c001641000145e00116603146100741c286501400091140350384001e4a050404003a101c80060300001030240a100120306c426001d0402110851220380c60490035686d00d030300f55041f41d81040404680d104c141402071184644400d40345000480300100f910b4100007941c0681d00c8510000110f0303000c01c2500307220781d1041d41030303802c58103040240504010003503d0000020904400b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 961024973 1250 961023723 961023731
    0x30109021c1106040f030605070e0a06030c0c0b0a0c09090213090e0c0d230f071a07080a02060402040f0513020f04060f0923091f0e0a0b0a1506020c1201 67
    0xb1660700d45000400003003c014100d05202429850402c0070746801400100401000103038003907040d81c400b1481700445507641000103480780206e6066500a090b03010182c0322422440800010300842c0d0085c030006200c50717039801c0b000e84d00c40c0140d01c104e000c0c844400a0b540441c04051000440365803241d44000b044500b1a554031040c0000a9900b203941c820448180c136003041c0140031b0808045058041c50300403006850f403c4061401c455071141d80b841140c1810700340c413185025101000d01160142c6412080c915034900f41c414002c3c5d51101c017914224095883c0101d582e902c0c0540d8800e0500840d903482c0d03c040540402d40070088190740740c2e0906a0311079943c54000038888600c43c41000140034001e000b0038216a12202a0803d048030b100b940b84450342d42c0304000300554081010303117115100c4544014661444030085008040b0104686a24800e9a00311400c2c400040c00251003550300c524184100d0f20000d03000944074001e480b660740960700101442c14146082e01d8182c009107000b200000f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 961026223 1250 961024973 961025003
    0xf0231062f0f010902031c1e1e0305060a06112d030a030b0a06080c0d020d090807060b120106050604051c0b0708040b1e0c091504140f030109021c 64
    0x107082585880001c1c00d20fa5449246100310f0030144a0026280c81e030b000e4060004800c44809001c0800700310314105807440e440c110f6030605002d108000700c440d0b41d1410480e054040c40b41c01070f00908055480911480b9100b40001301a031184000740581401070740a0045004041124036844444009802d40c0c04204444640181410006056120340c25a004202c86007103000388808200c01390400d8041107210810002e5200003001201c16600000c440140d81e001441c04550080c80c1d100001440e000b00092100140209500602100201182c072440c48080420009080340e049104141d0020381c1440208458a864800c03403101c4001d102204484040c25030302c1d002d2104003102c0d07440104090b0000c4c04280102d08200c41d5100f881d4a001c0c40c40b00c1740000b048070300c1000040486940e400005400341c0c1caa21009034050001d00c61080032520b45846003030041e504513803040075500501c01c910421440b85014051080070341c1c0c01804003510358903085010400b206d0700c090180d0b81030b030060000c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 961027473 1250 961026223 961026317
    0x302070c17010f0e0f062404110903010f1b05090f060c1f0c02060f04290106030b030a08030408070c150806010f020d02070504020d0f023106 62
    0x1c165040100301c00012a41d50211035901260340c05214a038265000036010185007000040c00e0782c015007a42c6a000300c8291044040c8403005080c5c450300d0b006030800c8602d80680e40e030350018009540e0102c009100501d0001496801c50f070607020710207558481c0c2240804124010002880a000007401d0301c5801a41c400208a041e80b00b0701d01c115080e80714440d40307288001d0040c81d80200c070f222600144480186100c000f540c2e5880500300030504140b90002c1410003e2540c2d5580707004200f014681c1c09503030000281007080800b40300d042d0100c5d040c1000794580e450040340e2000c212394440540341c1140c80baa150b0041580004d0030494003c81021401700c2c9210404601c9074410880fa610076401e842e00b04001000740e505001d042003950b100c2c2c901d00407010b40201c0c090095aa00756001030310742a04840c0d01001d00103444552417554070010340c070011120011488110000040314003080c000c10184802d50414803403107070800240006011294103504171801641000c40f091030001080c40324510303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 961028723 1250 961027473 961027499
    0x1e020301091104050f04050d1d101809151202030c130f0614031504031b03020a1403131202010207180506041a030d0e040e03040e0106020c04050105100302070c 70
    0x1060320b1010707052007180e07020300e00360180652100345014184484e0809540e21a95240144c840c1414071403458682003e12039550800030707060790002e20040080c2308041000c2c001c034565400c80c1880e4482c0c0c00d00403c01a020b070080b40d80402c200300c10a02c40c41d190800740b42892140320710803a4035015400c002d030540ea0710b901482040003c0404001044081d010f100030803120035502000c0b60700041200f100b8160303408a80002000026150102c8030394072458212505411a035607c0d0380590b840c0e40400a1503400280f20b0100c078400c2000d00c81040410984550703074040e5640e04880b0510882051052185505000ba43d00e481030044a103250744444002c03650303080500000880541d01c0c420010ba629060058242c42c0c1c0400c5150500b01c0041804642c50300486012241880701107000c00f8a907480b2741d4408483c600710801903c3c0ca0325100c80c01c8481303000081c464900144141001000e0340d18041c403465040b51310017019154030007003003002035010303402078242500e18441c514000502c0742c10303403d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 961029973 1250 961028723 961028741
    0xe0a1b0b030c1b01090f0b060d020303041d0f01030f02011b150203061c023015090607080105060409091110110d020102091516060207032303131e020301 67
    0x1a52034503000f0210900100030b82040c81c401c4a80c0c103098902000c14010f981d2060296042417403a0203550340c000c0868066080703540c0094140c400050000ba01c00360110014401801c421023100150700c44201100c2000c0d003c2c0005888a010340c000c130300056010740000300c040000d6070306d04150780d401d0f916040e44007803c58200c010440e40000c20401c6500d4440d41c420a000c0b601e0b00c601c3c80f124a82e8001c10310b400d004a1608060280280c140101800003035030800410540100704c038400700d0081c48090480c80103440c00b1381030780300304000300d03002d14041c441050580e030001c0d107201d080c2841e1038081c1010340f4001c00141c5000c5180c9a0f0101203807a0019a02e05400c40ca80b40c01c0030209100d00c0540c03500c040300c042c00301164410300c02956182d0b10680b13a08400c0340481599903c600c01403031114582c20124100400c018030020b03208003055040401d19900032070440440c1c40440403d007000942d4401103880a4419551501820024011850405c030b8508800d400c001c4080d0720390301090844046c85 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 961031223 1250 961029973 961029991
    0x2306060405042403300e04020c10050c07031418040f0f0c0906080c18060f040b0d060e07081e15030a08030f072a0213061e0503010e0a1b0b03 62
    0x1004070f030702100c09101035190b0701751002040c2042400c0d00c0103059502c0151214070880d00000d50300703400c1ca42000b03c00c05000c4880da0410213400c0601e009001c2d6030044c002140800d1440c03900b22444410101a60344980e81070b005800b00c5150f04080000801418141343c0e2840e944100100d64408140b041c854a0f400503107a4040182c10040702600c000d00050810031030307460412041c0d40d1041110301d4010380a0007034503026104e05000310f60040c1070143d41c00c120307001e02011600b280039181ca07402600840c0d048042c410650b41341c00b041154455004c0310f06900e2030070a5003500946201c4131103030a81c400799007556130f031a06a450307000074284801c3c4001920608408000d0110001000307a5080c3c11080b1420701c8154100d10000d65000b030724885042410b10000c1042810035512440045401c403088440f08100e0107464540c40c1841c141c101c4d00348110640e440c900841c15003014822507140741740036070080c042a1503c1d17840160780b1407600d010350081344481d040090018090001b843c0214421 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 961032473 1250 961031223 961031243
    0x181e0f060301050a061406031003060e1b152d0d090b01081b10110a060204031202011e020a0c1e05060c03010f180e070602012306060405042403 63
    0x120070107003900d0014121144840c82d1a4040100311460a082c4140c1d10041d6060b5031295200300010303500044507403018140c1d40c10003120003c0c2c008042490201c1c1d00d48010f503050f42000030f03400e00215919500843d05012000c102c0b201c1104240440300c0740000011000840700c1d40410303404035154001c58071480c5425140d40403181000f06c081c503910702401002c002071412082d4103195040e00352403160b40030b01a5401007481380c2828414200803c2c40c0901000301ca58107090391038940b0081d0b2280c44255900c030080403041039a180b0601400c4400740e00400d00044074801c0500c103030b009510407440d241c240805c14070700d100041c1d00c1c52446000501c0c6c0c181c0709040b400720380c03c10600303040000b400022404401c00040c0104445140400c4c166000c40c0490350601c086c80002000500a41a011000348a065000103425030305401885400c000e5400da1403100e030701074610720340c1801c080c1c0d600c51b40310905000c280602e0a080e4404a8011982009410340342103550b00f0030b520040641095440e1419 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 961033723 1250 961032473 961032481
    0x3031b1b070f08010902030604060203061c0c061d0a050415030204142d1504060506030a0606021207051905011d0a0606050d050312041704060306050a060905181e0f 72
    0x2c00d203850003480070500038072103040c8550006c4d031501c0e0024002040c2580c00320104426817070300181002601e03409204498410450b01340310003158110310810740050051580400820500c40601c0c00002000d01085030240c00c04d010030014001000c220010030384603940000160b0b0f00c41c0180340c101681023019403214105110301501d0004200c4400c100204982c01068a1101100f840c41c0d12a809440c005500741031040000d01908003980030b643e1002c00031042c0040200d480e440003086034503603000c40300703a4200b169020030b00380200c01c0003406075001020707161140080b2620f21040f0a00c1403000048008828040c3d41c0d0300c0700b03151211001940440074841c200b001921074500030f080111206c0c0d000c001c1950b14203540e840380000f10004003c000021030b040140c540000d100c018030240c0003035200c0e0b80300c000007001400c55100f02c40c03245a0040c1d0000702c1d50300443c80101510800780c0802540030110b9011003c10070701810500508030790043e48045816840981405134140440c000c0e65810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 961034973 1250 961033723 961033739
    0x80c0a0617181e010b0909030403141219090f08150406020f04241b110f030616090f050a17030d0f0209010e0a140f0105130806071e0203031b1b07 64
    0x1411720714a0117102000f052084040000003030701e0450364400800d00a0404c40711541d414800d41140b0b903c2c0c0400c000c070b52140307010291030040c0034003421540d40b5a500b6a540340340c14070810305442910081e41140440780000b100032404a503000340112000b6181100b03c2e01ca84490f50b2240c1d101c0100410640300304030300c0604800b0101d0751008249080100c54400400b500c0201c900310f40028a4070030044003400d12034481c0708071a0703484a4010290f414600d01540c2000e0000c40e1407014000085000d0004101070f08065540e031700f914005841e80e2070940c01c0810034104003040c07402504851105010708582080d882c060350840e8000c1d43c04c090f845040c1000050005880c800340d145c801c807a012410301076415000281242450100d075246030103c0308000580e068400c0c2034600300000b192103030200320307000d00107840c600516180e51050038042403001800d82d01c0700c0450000e0010b8008002141e00501014004000e0100d0030040c907160811400c004641c000d00f41c1301142c2c1540241104001c218 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 961036223 1250 961034973 961034981
    0x8061003050d03140c0a020c090c0c07050d0809010c0203070305060a090606270c090b0c01051e1005010806011103120916030203060406020703110f07080c0a0617181e01 74
    0x29604062006010414056656030802803100d08405c0c8041a40d030046842000604807070480038100c2401420f01414010a503808a25041018814254005154200409114540342d003001215061621480045031900403031401a07034035101d000c8000c004200284045030088074981070000d4034107814039181e010b6841d60782c8605000712051440c008907440c291403400c004410607400140c0c140c500c0c2d10a54024816400446010030046114036099105601083c0078000007211300c8c0041c0002e005200f500b50f0112288460f401d50720000700869401201000c1d049801418080000c2810f120414999003003115032003c144074147c14080c2c45d075000d1184400301503103904101901421500801c4c0d403088050801040642d0004051085c1842001070f024100910740a60705050f20174000c0b00e1b0f845101c1e00400e15a400b44122303d050600d003100012003269960740f18810010140789062440c3c80c1c00510010704491541043c81828030107004640142041c0d10700d030003d5803c8040300c1d500b10703 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 961037473 1250 961036223 961036243
    0x806010b09010210111b1e0a0b09031e09030316050d1806021e0a02040c020708120711011d0a062601030302190f1e062d02130806100305 60
    0x20340b80500406036170042808599085001140c5000700d2000c0c00314092505112004214424009800030f241900c4082200c44480f400707000b8150b21030301e03030280171500d03446070308081d1178158100b07448100d5074102c0502030403003c10000c05403410842039010008014210550444058101e40b101c070404642001c0a01060001d11a940003220b060030000396491000c44242c281c148020004251181c0e001c02000080a5001d402440007441d00b40010f580d584450003401090700a040194041e51009403e4840292300040b801040c0d10161005456250254000b6440c1031007035440c088450312003084240c000c1001c1e40c1d40901801e0026060352000310341d0a0f45542050001c401040070a40c001212030045030900c140030794100940c80c01844200d141341d4010036211a00690103402c90700030750310540e29030044505021591a00901e020b440c030501e0041d8248e000c00d20302c00d110386001ca6010381161850840090080341c1c942c0b62080c0b070300c4801c440300700c08003540b980305004001c000d002520030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 961038723 1250 961037473 961037503
    0xc030203010e210706090206070303140108011803050a0302073002061312050408060c0a090b1201090f0e060a0609110a0f0804030c1220030406020c0411040806010b090102 75
    0x401c03840d0319000030400c00c00c43c81a090011000c40c42409002d0f03554046a600380d40106a135076120340710300c0c01070050084583e0554440c5020030001030100300c18058916000792034a000850400a5a0240c4c1c481d0040a03032001015030030701000c40000d144803150042100340031510640e00341010303181d01d4544078001c0c9074000c42d00104140400c1401070385210460a50044003240742d90341488048031140580d030b100d001284103400500450381d005400030040e4601c950348088401d600e03050503648502c0350741541f00300404032500401143c102e076808008120040713a000718004045401161906505030391001c0901d564507010080f069042c4035000d11071600c3c03a1460708100349840d02030400114103245500740814100018101403140c800d80c040180d009941d92030f40040403074020300310040e500c0c101048150585001d90441000004d5a007200c50300ea0003032000350603240c01d00019001c0408500415501440007080c04242400311034041c1040104107921110340e400024034108080c50441c030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 961039973 1250 961038723 961038733
    0x1406010311070206070201110a061a090403050a0f0207050607200103050f0a0207082104030f08100501050705010f0c0c06061a040e0702070e0903090901170d27030c030203010e 77
    0x19007208150140c4200d5601201d030076840c1c4605000694509082c3c45a004290007170501c00c40802002d94001c1a20b40c01a101e91000d0220f10028841c08460940d406008154103101d11134401d4842e40b049411640c441c03041d103141650340e00108032260400c00c82101e980c04101240e0790400e400310440b103000d0809180600903801e1240440310b080e1400741ca82840150001905000d00442c41d08451040c201000c004640e1441c0309820140c5490540d0100c000580903041f903403032544034111550090500c1100605054901001950b80341d2005030b040755113540301c2034654000000c134810680156001e0300c513083d110074245440750442e10350b80c2101500320480450031200340307690310540d419208085103007109034941074400e92401c0410340c011403000c81e00c0810807100600100203460880070980e007080540e6284d0280c10104a80b450b1410010b51015280d4030f12644100c640550205c030720701c01041401c58070400c0440040c0b10b41c1064481e0038a0120070400c609091058511400380c60010305 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 961041223 1250 961039973 961039991
    0x709020a030e1212040309030f080a0206090114061909020a0e010f0c0b1603020d06141815151209011a010e0904081c0f0f0510080d05131814060103 65
    0x48002e0060142c081102d0b9907030800181050300400707e0074040c58100081c0c100c4010145000309803076211401040c014090340b03001c0b8062000c14010b01c0150721085908100a5840c00140821101c9400ba10420742c0b03160034000500743e0315840103200d011110303501c9407140d007502ca00141c454034031442d540041211b200d040380d020404101149402804140e0f0140101c2151202207020740910700120f401d03035103491400942444001850341c1100001d0740c000000c13030b900803840400b0b01e0040392401000310030070f41c9506c0507181c4141d03801c1c4403031000745100741491000b500410700b1040442e0036009a17035448080280040168070180180b580c00d10f4a50011a2890040390103000d02400c0144060070218821445001e010040015070b100c40b401082070982c42c02c1c2d0280589921056050030a01c0d003c0403400403902172440e541a90a8400140a80100031004481d44e510802002203952625100810101e0b6020021484038000400109d05546541001c68800a019060768181440c0800007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 961042473 1250 961041223 961041253
    0x4110a090f0f06030209040e03160b010603060503030d0209030a08210606071113020405040f060e01050d02011b031803120f0f0c03050705011103040b040b0c0906090f0a05030709020a030e 82
    0xb5106454040c600035840e186100c010602038240300740d07451000d0001144520351907500043d0102c6041c000c06200043d030b44d035080160110350b91341c002d47e80c15400402032447c1510594000f0a0b001030050100c031403000d2103031074800b015008030036400c82002e80a4000039603155410017a68000c01c08403141454008165100040c02000c0503140d801641e554101d06480b95103070b41030354010000540b00340700c5280144c504c18010400c40c0243c2125013203035000840d0b182030000b505e40c0725942c1a120404180c1c07030144242e00c010101181201080300d041c0403030017810034000c001401940b0a5880c4d400e02c6c000d03801d0103081d16070050460b0007003203070550100e4600f42c1c3c80010288041e4150802c01d5581240c2e0806a014080c6020805542603001040c8003c000b003403181948120300450100f0b4040d00c480380485000d100d06190705501031000e0080d1000d0b4580421845a40c07080107185031078841e40c030404641419041c2c2d214840455020910b01410354140c02142150b0f4002006031a03011112080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 961043723 1250 961042473 961042499
    0x807050618030a050711010e130f05090a03080c070c0b070605012112050d0f0c1e08090606090a0905011109040b0111060c0c031e0403150207110f04020904110a090f 72
    0x10107081c1d05407281460000d030340202c844045010700982758074002d924021125015005001e80c00c8040ca2400e40050960b180c0031440a1203180d050380c441c0e54603240c0c1c2844030360f903030080041540c090b8000ca00000314001ea900003800603d10070b02011641e503140c41c40300151313000c2204600b6800b81f01403105400245221030346c0b1440402d035052064a8090402d42080200400c403010700406e8507260140030819004250b4806007006280019800001d103c011100203d0554401980d40e01900110345140781c10006650f10601c505000500351945849071402d40340c00c0c4030744103015070b800203214400742080c1c010617078441e00a00307002030315817400e103c2241d6820004160300402c08002c9402c280755481172049036008047d40f105007c00c0c004805421186920a10040314224501060109044107a00a0340c080300c2c1c2224a0000c981a00790038801060f241c4040c103607200f41d0030801c0d602c2c5541c0b14410080d040d04040986501c5064640001d0400703035661f082401160030035507040260074100302e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 961044973 1250 961043723 961043737
    0x1a040912050c10091a01060908030d0504020f04140609060a060c0b040507030f050c0915030a0201030c052203020f0d020303190201060b0304050f01060e0c040509130807050618030a05 80
    0x50900d54501c2d180820354244070007071403080c0340c890400220784240590703030038619036110329244205050b90707951105481041c914400c0e03a07410380061041120300003095003c1c0d5031040c000b50008448031004400501140c1130342c400520903000707070303414440703c2d0a00000c10782e480318080c0d40c620300e014280040640006c0031a14002e0424075800001810044d09201c4c2c04000c50380702035040071440b210700d8215218141c2990040c02614a81c0c00582e030001064505202c2d400b003e03000d0b1009001030b0f00114003500c41464103600340320003042040404a0041500b041c0000c03100202181a0b0541c8100100b0241c0c0001182c4250044600c2e407025a2b4044116800c4144d640704100301884818000da024000710362000210440c00700803c0181318020408420010040d4020492251120a440341f80001940d05c900f20103001c2c4000e001c40d00703081072880c0d08801421018401000503640b8241c031036004100448254000c00d0600880700d084c60301e100c08025546c006103007400c1c04250020041d008400c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 961046223 1250 961044973 961044977
    0xf0402031f15022e050702030c060a05060a0b0a111002040303030605040e0d0c0c0509010e0921091e1c0201090f051c06020c0d02160608040b040803070203130303031a040912 76
    0x5444418140613201000400b0700110703c28003043ca069003010b0348035040140d0f001e90900440f0300007000185184100391040a00820241a440c02c1805201c9650803e86040c8203114018036600700b41c0c081000b0b07002c1d500e107801501503620780c02c502e0003d00f620200e5008a008a00b0030303428072800c050100d4980118041e62500f50490f800031f0401c11920a41940515080101507001113000840505c810b48100305940072078002100d246088041c1c8404844840816042840607012a1810440c500200258198088102940e410000b681003a201c400c4000303c0d02010f000508658011040d40003d00903000488040713480c04000c1a6039560440034645a8181100c20300104016079060346c200b04d840340b0849110904d80c03c3d02a58a564020020f1440320409200254207441244618803441e80059400b00300d4450b0707582c49244e9000581a01d0540c0024011a2003600900510310002c50123998040380c0444101450450766a030500e00d10300943c1408444004a050003008030b0310701c041d40c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 961047473 1250 961046223 961046263
    0x20071e0206040f030b010f080604020307030b2d040c060809030d02091c141606021c02190302060f010b0f120402010e0604081e0307200f0402031f1502 66
    0x944009451840345820000c030720301d18900d000c400d00034038003030842c103840030704000507041a12106503070354404048030b000754154016801800018803071941d60742c00c01032806040040072941204e032080b030f1100e4a25401c2c502e5011041105002e01d4140020082c141401c0c10901070804140081c0c41388100f6912110094001541004580f500d480d254409842c0c1415a0906031061400543d11030300b403d65403201d48902c0f8540403e0540c495032623005ca48090b00108001400c0307602d4240c1680b00c0c0c0e814001075000d461421600c1119005404140741d100b50701918403441e01c550f84d0b083c0c00f401070b08041e12003201032143d9402c1c410b0000072100a401c98181400c0680ea40c0e20040340c2007400200038541165021a00160340100001c1c01d00b401c1d80856100901c0100e808242c076603a0081c001b0140c4a014070410038210900210b00301032040340050704c40c1c210302d034024000c50140ea000b500c8090110075004412200d031750355490040050428800120110030184900954400341c1140c1d1000411003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 961048723 1250 961047473 961047533
    0x80307051204031208192904110403140a080f0309011815020309101a13050c07020603040602121602010e0708071413060605040f09091208090109060501092007 70
    0x300c1c650040706c646035503800313002c40c203411802141d0404900c080410485650110310000f4580343c0140d50192001c090340398207081c69603d038984910766030b000c40e00282c01120001d00110300c02d0b8004090440b81912090340d02c2c14040301003400c40d802c0312601c140340e03103114100e81c00045200044030185400d04102580301d403903040c200d50600c885d07000c56203100740c03902e83c03031f524081030340300a83c02410811100014048150304842c000e031541219010b0b1440300030400040145480c001450304940038900050032f040d10000151014101a203a14500c05192011859115424001c501007038070360001078248a481d0500e401d6840d0300e035020f800c420b4a64030100c940075885000c8444504030450a060024540e02c10303002d032841c1c1c000e001c0c0440d20311090502042940c06405002d400c1c41d0300034012841c0ea80e0344241120802c00140c2010015500d03141030344007044107405468007800c50014006400e214005416070f12110034501c0c9042d404050007003d021981d0201e6003030451045040000384450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 961049973 1250 961048723 961048741
    0xb0103020c0f0f0d021204120c0e0432060744011502101107020d1208091501050f010e0a14010f050c0a020f0402090a080307051204031208 61
    0x2007800d02080c621031030300600030800c000200410f042880304241c69100c601180e013240c4079444480900e161000800c801c22500c9005a50b01462501491102103481e44841c110418048240c0d400d440d0040442035980485455848040181c503004682039074040c1c818503000d40310a002040c02040c031031090009510116040c0314035a12074151035180c0c00389120039501428a08200d22030700c041000c4403001107007844100001070b18040458005000e0070201803640b074060a0320b042a41e224000902110b0016110000e42c1d4080c40e00c2080582c064102c00e200c003d12034400100303890010340c044003118004100c84e10841c0c3c1901c2050f6882c0c4481c004400040e94035800081c3d8040c2c208800d00e00000b0f80e52504406215502ca003662102d038007020f80e0718211558028641603030b810750445214140145003805020b04680300c00b4101500381160358002401da2101d81e0b00c400461303040010b045003004024040e940648001140e040d05050031a2a41c4511800c0002e0b80d40030b00407001c002c182644 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 961051223 1250 961049973 961049977
    0x2011706040b060406020f1e060f0910020304050309090709050a03320307050d052b0605030d02010f240b07050a0204020313020f010207061407020a0b1206131b030b010302 75
    0x1480c041c00f100d565a540c0e207802503031004c480010a0090044100341c001c905280303207140104410700c038000d01264030b4030040c110541d0f9000d0000c09a40c0b1030070351111490000d41c0041c5208034000e60182d625100402c06000e12908010445c00c00c110001c1020312160b41c07034032010720549404c110601a109054407240001004101181c188503038000c0c3c5110350440c0000003080041d200d80181d80003100a40c0042c1c41e136002d0410070f04400c1d10300d411090008a040041041c20011211021842c02d0360307000828108400d003c502d8006035140e14000e07a00d20060301441ea040c0700328564805220b03960b00701449001c1448d0044407081c800014911050000c104440f403d650340040c021950382c00c1000d01c0d82d00c00420044100c0c0034100c820344800c2c00398000304891048401540366003404001c0c0307400f900700550101000b242d10610146000c0b9011303003103c0c007801300040c00c08420802402c0c06402c0110320030545c0c01c000380340713414540705090003ca6a95000781d12441400c01140340780d030f2600140e01074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 961052473 1250 961051223 961051241
    0x906120c05090d0809190305120306032b090f05060a141e0414030313030b060102030d050123060715020f0d0c0306090e0c010915051209060103050c09040201170604 72
    0x410200300c070f110103002e12075001307158484040320081800500400240e0180c04d03a0722020785250031001964441442a0703000310381c000c030010f0075100c648695050f1780800c00c40825401841000c0b80003960b21054010200c0d00c050700c541000481000d20f0030700007441d00e1241000203c1000811065000754550b1001900c0782c00c0056100c01c0d42003400107120a0f10744d04680300741c3c0200d040032500110141008030841e005548103a01581140d8195280c10480240103000d503811072104124024482109120f014041c210940c4140d84910544281110400e1800f441c00d01c92181080f1100010303070108015040881e98803005a111582c0310f41d0000180514514805081c5c10040c100320000d0349a8080380c2512002907082202803089410b03141d071582050645404203842000500942d68a4145200e01d42c0e5145021843c02100b41c02c1400c1320340c030039200c4542543c80a0018000c21805106801d4440700075200e49104d0700d01034000a0003801c60444510300034454202158480d180c0343c21130350103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 961053723 1250 961052473 961052479
    0x130309093b1f060b030402130b030705060d0f05150a0603110915090102010f060f0302011209230f121206030a1407050a050402190f0210110702100906120c0509 70
    0x348980e11075095140106400c0402d0381140381c820049100715620060301c1c012500a094954410300801041009100340c0b20b4040c1e040c8034141d4001a41d54450f0020141100400300114040384451b0002d41907a1015040e82480b040c2c903500000c542d204e00da60748044407403074075000c140d80070451058059407080000d0250040e0039480e01422242c4a00010241d0800a80c02084840c002c0005241169061700800039880b4158000f0005903102c2d1140310101118801c0000740d41c011940c8190101c44c2c0c601d030111506c1e0003e440d400c544181800f0f030301d9407407040e00301800004080203140d0040e803040d188000301d0b8400074001705140342c40030403078030000b1035015030880010080381d101c4031780c0d64146101c0c55101c0c103003410f004203841c28280280c5201c00c030300c680200099030465006a0b4507486203600c1808502c5a2640e207a602da03028010310700d441c440d2302e80c19581d072200c40c01071100c0109201c40803414825004070421266512085003803004295520014002e00742d010105c807280709101000d68 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 961054973 1250 961053723 961053733
    0x1d0c270403050a0815150c030d060305060402030d210e0c0a0306051b043606091d03090d121808030c0c09010623040806130309093b 58
    0x104050700180209060a016151101e281e41c616a071241c44010300400146c01018805646000b248103101a00b400d03440c1d601602d06120a00d00301320200c2e845907100b42c40d00c0d80301a092000754102800003d06c00c100501e40003981500243d17070b24084101025071140748a035211840b200602c0103100d070b400c114030000e2240d04281d0317403410f1aa0107810300340c40d41204110070900c40c040c0240078408a4046428501009429007512001b4400041b08000101c06483d80e501c0c1d0562030380114072400300605110800000e044002000602e05680c9130034001c401d43c0d04c10001c0003004d81e142000b0345440b60340841c40300e006403141001100c3c40086440840060405034a011400c0c901c080003401c07910702c0210848140990480c201300000400b88101d0700881c0c42c00800078000e40d02c0c4110f0000380e003461380b40c061030295140c0090786046022502c4802c001c0200032010b0404d58010b007003000600e0301840602c441d140c524880050301007442c0798291102421143c0710748554040350704101032030b0040103480c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 961056223 1250 961054973 961054981
    0x1202060f0f100b0a0305101512020f220305010c050304050a0213110d0504050c030706120f0b0d050c09250302180a0303020a0303050702030a050a0309051f020705011d0c27 75
    0x50060102603c4600c00300544030b4001c120b00401e0a10940c0ba0601c643e1000c4820b01d500010314020350007800303040d00be61010403164075030f00407020812090000072080c0340c00c46880c0d41405421a00e400d2012820014208184030100d10700140d9043c0e115011520300070640450903489008021010040c1030301d020203d00c00410038001c1c2c0c800b500c5240144165030b14980743c0b008060f00c0340000e001d19030103e40311302c034604401342e29036000d0021215685d80002e01da07109080002e900042d2594102c07226400b14202606030b0078401209500309044540304250300f0541454500d182100400c1e030003c2580c085100748a6004144580404200103400e400742140c0303c0c20025200c9403424070a602090405000c218054400811104c180146603940c2d410819100b10172009000396100540c0c85100340f4134181c10440c3ea09100800b075040c007640050b586d03020b070310304a404d65003055103002029840c1c3e1944000c101002c110b48006a40840d0107040e00c014180b0a5409007040c40c4503148142c110400304 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 961057473 1250 961056223 961056227
    0x31a1c060f0207020334180c1403010504020a030f020c010204030b0c090f2e0f090f0b090f0d050106140109050301050712361202060f0f100b0a 63
    0x82400902510051011840800860040e40f040540094255100420700420304003180410101c940080060041c4103e008189503140e01c40354119800300b4054040c1d5050381c500701d1048003902c00d920300303000550503903d01100c2d2141c001481040c2c00750750009903000000744650301040c14007000701c02c1152202c1e0000d990324000e4202d03000c01c444149400d00802c480f003080000343c3e00d0980c001001c2d4201c0c2c105000070311200c0c1260313001e40300c103280c800c41c04000c03030b11010768050400e0345641d44e400d211004060401440006180c0c004000c4601d0501c0601c00b10f01d0580c2222101c00f416611202c01000e80d0000c50912010404090b0055180503804688070f2424a2070380800c000990310f00041079110070070907080310010340d844404100c0c441a100c42e08245030f00428144000b01101c0b000000c029907414a40340032409404c880409074099450030086002e8a80780c04000500c01403491340341c61030911540100c06440b06c07a1003860180041c0f203940d4072a441c0c802900340340c2e00301c1e5142c2e0400000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 961058723 1250 961057473 961057519
    0x7030816050c1e1003020d09050d09051e06090d15060f09110a08101d010e0c09090408090a0f061e050a140d0b060309160b09010e01031a 60
    0x800c0761940500e0928100901d40010005800740b0384807403448421480000b0000450a00c049403024503400b801900300380c000500c40c504016001e04043e04405411602c0140340d01420303081584510351300840d85038036030741c08842c409034405d00b566019685d103400d000043c408400c1d00b1008205001c80a0000c8070050b480c0c111a0484d070045403c11140c54680d000481034440c00c1c11301c806455030034468400c05500c154100c9400006814030601020f131211101c00f1240d200012000428110400420503540c00d034000c1c88d1302100e5480030300e00f4a080440060088400135102901000000c50343c006183d90b8a88050000d1080c1201c04002d19a1890040c000c00b80300d141d00300045000352441d07040305016100b11900c8074060350750198848102c1460080130b80003800c1241c0c25513a43c68000020b616420000c0d030055030000c0080c01401e8030b0707000140f080e2109411603101260284a030751500e0341c002c04014280d034824240403a141c09072900e03154910008a046503480800385a401c0908500010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 961059973 1250 961058723 961058767
    0x1e070906090501020d05090105030a06050303040b04032003120d02040e0126281104020a03022205060307031a0d030320180405100e0a061409040c17070308 68
    0xd4074140c896071a0016600c410b2401406004908200311400c1d981d032050300215403040d0b08002c001002501c03540070034615002500061400180002c050090044076001003240c0c1200c913810b48271440c1100046600d41c81d40b0f0745882c0d011480400c030410800c0c00c580686002e404c10001042c0250b95803400185406d48200b010542c2e0441451031094000c0c0105041d0003c01991200f0000b80002031880c5c0e454180140303040d10742c510401407580079640c1c1c40c001488400866500941c903a10302120424081029400009040b0842c40003006551903100c1903d41c0240d6500380050400000c609103c400380c00b905007180c4c40400e84d4038030f03001c058140c0d011003841041c001745035041106598100b115449854503d12101103809291138191806810140d800f0031003001c1101e03850f90360480e02c005200290b908007d066110b10781803042101080305c658074070100300d401c1b410b141016102d5030010b4100d8040c0e10130b40e500f0083c0c07988c1a1041040380000540e4480c070001d40c2e641c04080e59215201c0017074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 961061223 1250 961059973 961059977
    0x130e06060c15192d020c0102040b0a080907080c0904020a03060e0a0605010b04050904060b06091504090f020307121526010b0f03030d0207050a0c0902191b06051e070906 74
    0x42c58443d2082d5849070042441116500f0403071940c0d070b0114603220a03040714564203055001c000400b0b81000070f0015000070315031403032165182c054402028003425002803152989502080301041040400201541800310940b2413400710380799400403c41d45c190b01e41010f07110364100807c840c41c0100004a0807800d0703000d0ba004200c00c0c0d89607001c0584620452103140d0f4000c0c610b1000c00c0104003194460003a00c600100381524000d040130100301400c0c42c0e01e1003002800c001080400c400381403401040008060468110701d186170004000d0900c5203660955155590ba82104031030054500d015000035000102c0001c0741c2085441500c0e07000054281d525240b542084000010b07400d0610902107940402000f40d41003047c4416000000e4103c10400d40d032038802c0300240d001240b111506080908122400583d48038061209a0381c40103901400c41c0420010a141488400042426201c800d40c030040c0400e4030b494003480c11191110808221040529960038000c109400c038181c042202d60039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 961062473 1250 961061223 961061251
    0x709031a0703051006091806031704090c21180501020d0b010e0411091201022b180260070b010e0a09051f11130e06060c15 54
    0x18103a1a03640a04c144102c00205030810400c1c800785c0c00c4013040119441c42c50301d00081456032a10380400c1d191000c0000100b21304001001c1c4410b40e0706008a05402543c3e04280e80804094114440750346100440007001a50321118402c41c4034076a10b0715880141c100d8000e41d105d512080703030100148000150103000c9003034601c034901103062502a0020300001440802d0410040d5402d205e944c60403500080300c555800c1181070f03038030403240c2070647c6000108180d110320300d0039010f08501124160503031120181e04880d9100c005a482c4032030040c8003165405a011060040d0306a1200e10070180d0140c0e42130100c1c201d203441203440300b80302914810b280700d0340d0860441074641560076038860711101900c02008071005000d078080c40440345401005c88a000038001601e07495950a02600d403070098042000c00c8840020744146000d080c1252200c041100d1410b40c00103d1008420384c60b2140300d0103d40c882000503c1a40c502083d1490584a003054441604069480b0501e01d04221108800710301c0c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 961063723 1250 961062473 961062481
    0x209040b0906060406080603070f0303080a0e062401020a02062101050d0f0f031b05060106110f0c0904030c0f0b04031b0803060f0a0b130e07030905070e0709031a070305 74
    0x711000040c0034800c040c1805180130705019048a102d1002001c068144c402c03260006400391902000c080190302a0783c507010f00b810981c50080903240317403a0701da140540c40181030249085500b207101c410980350860070b01c0c10002d031000503802c0440444d0069445036010403000501c81803d44540115540403850001030381c0c031002040319005885001801c042001d0706403400103100da400f0802d1560007410030105180c1a2104403080403003043c1c0c1181c03d41c1028004104894104110740c50300c14615020380301c0c4203403490119650f001c110b00b107a481200b000011509250003903501d94001a0003483c400719000325030900d5105180259011000140500f070100c40b030128081c2044000e5900c030700021314580b1900300700200304401141c8198000420480060540340110041990040c00888920b5145c81c5c854103025282c0700600c4003092505000d41000010000301315002a1040b0b80b240c0312580d12000f03000c90340741c05d0710341009110f0804416a403008907089080548600306c165024852591 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 961064973 1250 961063723 961063729
    0xf111f0905071208070b04060902090901020703030b010201110d1a0d0c0609090902060304060914060a1505061207050a050403021504030b0a091e080904090308060a0b071703070c0b04060209040b 85
    0x10051005000131505004000005d07005008440c0c20500030400464001050780014611100c280d40c0c81e88981e500250342c10406426006200d8012000d0008100c401c00c900040c41071485840d0900f18815564105d0f0240da90b641a42d2401e03550303014201c454250714601d480714810005010700c0000c110307141c0300060410740c00e000740b40500f07034080e00030707802c588884c3d55240151440d5a000c6602140d200358426036030780c0410820388500683c00021510303459a4110410450003030700a54040c2e0000c0060070282d690004150f5044455072400c00c3da240c02840044985010300d4100035800712007a43c18034844070b518030241050b04c0c0a140c0c09040d58544004d0101120b0800c8030041161007e0701d0403031040048980103500c801d0141050500e0002c030303600002e0454840d0002200450f103140c050003d00c0c1028041a0003411304140640e02c1c3c210280c0340c48804203010034411041c04000400078050911031811017007403541c41403820360b0030304051034900041c0d040884030a00661a040040e4070600d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 961066223 1250 961064973 961064999
    0x7031b0f060c1106162303030c03040305130e01080a0c0920090a1a030f01120b01050d0201110f071401090e0a0506040b12010b030615010f111f090507 66
    0x581c850310780e003103010007560b5010380b08084242d403254800701c103000009001131038001542c616445406203030029042c01d04030000d110003160728214160b2050080000c543d0310941260f40154150034601d0704c03000c984103040102241c5800046008541e4000010b01d1240001d100d1140c52042060500302a1921078002c01c43d10840001c11108802820b000c155001134001044224809010080074503103d02460034034400598400213400c200008100701504902c0c0100d01600c10341c0032036074542800391902c1c0d04824040c0a02c0e0320820b105003041342160b0042e007020300100760b5001900c0028610700005510b480c0c81d88100407200c85030524110300c2e903108812007010345c2d4003c003400d95682c6641c11304000410700205002e070410794451402085a4400741c010342c2d445c090800104846007468207060401101820380901f100000080d0140c60782c1149403402000124600030400702070800780c0340e10301034140c030080c9501a0301e4241c500c86006140c20100890b4042c2044510440c2e0761010220a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 961067473 1250 961066223 961066229
    0x302010c210c05040504020417070605030c031609270605010509010c0303050603120714070f050a05060c160f03170a080c0a050702130501060e04050105130f090507031b0f 75
    0x7000121100800d0003040e0340318071100140da140280c00c050300d072800b040803640650040080f035002d0060031005407500b0800e8002800c400e1619500310f0600c904001d5044c040500814200c0b460081100b036280d101c0c12040005015100e1030a0321f13101081c4003a240c8400008402c2c400c60f08215000c10036500580495002813410395402c2e4110140ea18114020103018080d207038075000d0104806c4019080001a041e660300902c00d030315511100640d81842d00d0b005500146140e0140c0c0010440c50b99840030100440f1170541b00f0300d0b13440c10301c40080d41c2805801c0842c040d414950398000b003128140e0034040e100390b038030a4094601d10308002c038815213a802800903100c000760030100002d194540d01070141058107800d04106060a1043d400a1502c08004c07403c680301e180e0b01e00040001c0c55011110003242241624100403a506100105040100c900007029036a40c40c0c02c0b924410000561000001c2070b080b04c01d6503c502c0c0c40c0e14028080b2208440801c010389a120000709000e592540b0850403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 961068723 1250 961067473 961067507
    0x71406151804022d0a030605180c0109092d061412070909080c030309031801030b150a05070b0a0902040b09090c100309050f16080a020307031106190c0302010c 70
    0x2e00042240322401c65031080114004400c165211446517203c0117480300207188100c5000c00c2c00d00e04004c100f244c285800d4000003007a40210b03074000d00c2d43d07048848101071307641200001c01c6000c03a000c090390300792144401d40c600c48984100b940600300c00a03403019083e00d00003a0b00040004a840c200036a801078a52030581d9500320750400c0102d510b4950040124074403c41e4528140300f103112030207055802c2102c030003445810014102ca0201c0050501001008003420100080300106000c50183c21013001d0f043c0080c100054070141d010f01402c01d031000b0507800b020020351444c0a034448409005d002c1d204900480c104485103e8616010711132510402058008080b1910808200120b48400d41210410302d40d59001103000304d00300f0b0203606041c070280c80c01000001454808009140070651040105801c9009072000596000c542c081c2180e8011000c402c44010300c1002440b988038045110448002016081c03c0c200e40041c091282180690000c02000c034200100b070782e07030300d80190500303070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 961069973 1250 961068723 961068739
    0x40c090f202b02031e0712050c0c0d030b1504383108210d09050d1707050304030f120e0a05070b040b03010b07140615180402 55
    0x284081e00d079015008400116401c0c075119a4428640003030129111214403500b6000003c001418000e005810315540020031403000c685081c0400401c9100e40100d11506075440d10003144070030708104152150908803009075000d4100440018000b8040002110b000c1c0751017800081302c0464400595044980c1000071602c608403141d03c3e80e8100800c1c400c8803142c1358030b00b81d110704462124005882d42c114481401500303102101140216505014803200103c00c940205005a01d40804c1c01c2000c209803942d45108645e417202190158094004001285443c0c4504441888000901060b842c491620340010b01080c640c00500909821180c850100c1c80420124001a110303081901c0b01c0240d41c40c103005401d540320488010f50301810709801841c1d0110505c1003d100c8140724034001043c03001034442c80e062915170301c4985800144036200c2c6001c00400da160501c298120003080c80201c000c180d907040e00c1c00c020420090541d15807820b01079601c3c04210710101000b9030005008a4000342082 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 961071223 1250 961069973 961070021
    0xb0c0a120306030f2003340317042402030703050a03140114180f011203210203190203040c0308030c09030307080306090f011229040c090f 61
    0x40c0c90a0812004040d03851600002203081ea14490b102c0b03d20880d0036090002004001e481c44a10401c00f0511036000800c3d0360100b2941e803071003003c2c82400c904690020900c03004e030907005901c080d031000c0d094001d100d480e60a001d9840c0000d1050b101d150310054400c6090102011001e0948240b10015a00820039140070078000e40192035062840d1401094640050300d002550600a078401c9540c40b0704c080c3c010b0540e1404c08004136000c1c206000246062400c1000001c0082c01031107000a46131000c2000400c0c10700c29070f98441011a600720f10010310010701c5003000294021180171038005c0c10801111550404c074000c50b03014030342082a80708060305680390203289070f0010f40f4408803014100450f030101d031020700c007800320140522052610f92420300180b101420f401800c800346a44504018094140c00316a1054402e8010040d04007480f5600d01e649511485e006051300b602c0080303c100810018250101c40650b4001c2c0c03818006880e8804018040d0b5a00c4802890b0241e4029048 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 961072473 1250 961071223 961071233
    0x102090a0e0f07031d1005090d1b020d1419050d0f0e040b0103150906090f200f1605030c011104060f05181804060e0606010c02040e010605061309060b0c0a 68
    0x103000481c024224080e00e0740d0f100e040c16454142038490441e038103910350381003090006c4184030102010709281440e060882b003c00c0848030382400e41000900c15030780a0016400e0014590310401c00c2c4105a0803100e0a0b12a0b0000b00302c14a2211070450301c07445022520290303144103210600e95a905515080440d00c1404204005008521651030406540f034030005242c036507010902c002401078400c0001c00ea400d0003486401d48002241e00e03a9240d061200c0c031a13444c00300c0600b103120400b100d01c905485801c4040d9441d0309200d10000003620807100713000c0d8800d120b4044000d1441404181c020060700540070500da01da40600c1c030502d808280b8500c00008114015401019080d610354075070501c040f81d9200162108640a034245144400481003200300f020750301c91149218604030040c5403030302c1c00c0c00c002000095107200090045484901d02a4400800d4010ba8040c040062031583c03a06a10301e00b10100c1c0c0030b03912440ca562401c0400001d0710010080c00c4076400390702c40000c0c10000760b8039164 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 961073723 1250 961072473 961072481
    0x230303070b0403300c0206090c0108132405010602061311060901021f0c02120304020904020d060207060c081f0803070204110c030f070309080d0c1403090405090102090a0e0f0703 78
    0x28a058104004c0b185040c00f00c071401007040c03000102040003c00c40380e002c0c0003d24050005280c1c1e1740b6540160900c02c9140c0c0c01101450740400141e03940040740b041031034004094001e807903021410450708107000300b01e484076810072410b0300c1e8190308035005e66a44503800c1010f20b04041015062003041041c0c02103038200100200a501d0043c0101c0300c440940001c05603d8140884810a4444e62048001840c40d03041c854514200101d4103c9821414950001540610050002031148140010100401c001e940544d54840d40103582007203031011100000e807501504807000c030101c5603020b1100710180c2d50441e094081d036420800450170300c1e605500b803000a0226404000308400300303102c83e400d036100420091004014809849823100d00500c2c000e440703443c0e150000a220f812540c114459164403039600b0b01c0d1550000700000049190040c01801c5101d06094140c105090901f040f18a540540090100400a4680740246503640c2e586440b42141582c510655100ca80c0119003e0b92003030308 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 961074973 1250 961073723 961073747
    0x151401060509280e1003050d0305130f120806060408061504181a0705123c09060601030e0d030c09120b04150c090627230303070b0403 59
    0x40f51010011455010f41998501d80181908040d800c40d41406040d000311a040d42103078010b4400c8081c141160b035a00d494045070058030042540d1600010913142008a16108140d0000d01c0c0f85898001420300e1200c00c0481070f90300000c50080404185641002e00c2202c048805020290110740c40e0365020750303c14200c9282b0781d0752203034503440b80c3d4400345035081c8032040080c0714500558210124618543c00160f0080980051042c03d00143e54101550801070b540b0000d1070700781c01010719501400e500c816060100e010803940342a00c050040d02452130711035000c0c803100360031a11030307a0b1040c0045094501da04940d0405070001030405406c24020b07040013000c2c1d6003c2c1094000d0395120520032040e21440c2805650b14542c03c001d10041c461443d108281101d043c010502280030100700c0036214650074810202084020540103865105030400c01c80703900d103800c106840c415501c45100c0745003400022114070007001413454a401d40703000000c07650190351050103006561780c0c0b030328290b40400301c00d2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 961076223 1250 961074973 961074979
    0xc0e03070f1208070b07080a0b0418030503060a03060e070812070c050904050c131e150b0f0d0204090608120717280f020705030307051203060a1809151401060509 71
    0x40031a00002c0c17400300819210700c64507a07910005142860b4a07005403108600c0107030099142518210300740c400c01035100803454041c01c051f992910303108081039454107103030300141030540303045040751007020301240103812200c091044440c101c42d0070b90344040c5071141041c02850403014a130b0400042c00c00002207035005002e00d0554100921680c04103811260f95130011030204c0da6940141581c4000c41c103407240003144500c003040000f2a40301c003130b4210009802612805030000c00d2a84560f9180c10444082c050318010540d2620340c0c0703042d110b02034989400303069002c1c0a000710856480c40c43c04140c0303a89940150094501ea004c0504001d43c0e0740c401c1c924008a80502c806c005180852499003000242c0541d03100c441d581e51204009050004680010b48070350000c0001c0340100d0360001d016005180c1ea048aa90740c1e843d94000030700440c0c44ea5000f0107511124912007845892142c1c0001c41850164500041c1724000106800803120038441110341d20a00c0001417001d00d10440c01b03071500d44400303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 961077473 1250 961076223 961076227
    0x504050612060c0301050a1e05090604090204090807060e150112020a091401030b0603010204081005091606031b09030f2409050303011a070b0a0c0c0c08010c0e03070f1208 75
    0x1400c4418200301048554041e010303c0000100400c3c140303011988014010000c40a0520907a05032081480e2054400c6512401001e40410f480b5500e5a00040100307500410030481d04142e45448803050300010420b8642c41e00c6c00210f6000204003140c507a12030985000180304076820a910588901c030800410b0340c1014440fa408a4500124881c45001010603000070199600d1403519201c240801407500d402a401484208000301000514403403040b4044c01c0440d1903560001c503645481c2c18000030001011038514000750b00c5805070700000c10241220007003040000883c0080c1d51006051100a081461000c81500890138840c005400800c0000400040d1000d40e0307191429101404030070b44440d0000801008400351051a5200c84042c1c07421560608499480c1d001c6991001891440027603111110700d00b02d00d1160307001c0d91f60b10f0344c0301212040d05616030b03542c0c600900c0c034207610101082006120601b10300d0001100310031101c8806104c206d950500b91000b80d440c0904030229103200c03003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 961078723 1250 961077473 961077499
    0x31202040b2803200f09223b100507050405031005060607080a02120f0405120c03030d020c0f2e0908041202060712030e0f06010f05040506 61
    0x8a1801058404480c248110741c1030702c460b10b0021030a1549021a06241ca05808940900000c0407003a2140c071034000e805448014804145525120b008041d90740030644c4081c0c4c00c9082c0c282d0005880980005038100100c01500340c039100d240800404c400b101c07035400d00700007041c058100e006907400d40060060350300c15400c01d0440400e50b10b081d1070072800700b0404201481141800c1221004a91202c0020701c4181030890200e84540300f1100042c0c40c0000c001030b8207007054020080c4815400f0300141c0e039552091413000419140d0000c1c09039602c507508184280d014000000303052245050010061413521008248100c000d501c0b44400e01074502440c0441280c1800500004244030b02c0740d858400c5449a4070440355910384282e180b524101c0c0344c1802503003c6800c2c0020b580613542c41070542e156082250000803000d01034040d0082146101c400800b54455250300481180010003044902c451200803515407104024010315072030a203506010096840d20780c001e203400100144c2201c281c850 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 961079973 1250 961078723 961078739
    0x60509040209031c021c080c04050f190b07060f0c020c04020306010e0d05010501081c020c01050703140c150114030c190509010e061f050a0f090b21060103051303120204 74
    0x1607070700d20000d40c0180480d10003605e10340300301aa10344103a28201f10240761055142c80b00e40a64025540101695410500641c035410901490b4082c4100b200142d00c0d1307940c444a40980c0f00d004100c0e07080d41002c0140d580c05030540581d81c42800c1e0380d0080d0a5850a00c02800000d40005080f81c1c1002030348202600341d0344459007034000c85d40c02140082850b42c1000c03541d910740144411401c40c2035080c95807000c10240d000c07a0f201c076465001d1806560381d42a604048030680401c036080205188000303059440030303c0c0042d00101c0c0c44800120280c0a0789c0e03400c0c0a001c5040300a40076a01900018000c2e0003601d000e4810540500b941e02c0500c2044e52590041103521100b60401100500d10405000c0a480c044080f40c0c03000b01003000c2100405105a001015070246480420a00440c001c2c201082405030045c2c00241c144030722801e0700c9140d42529003c13426050441c811400c0c040b1000700c2c403254032a0140314451441e248149149150945c0c08491503c1c0c0707449000f1030749509200c0490456 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 961081223 1250 961079973 961080013
    0xc120e040f0c121802060409020a03060506030109140c0319050c12070c110316091d19030e0a0f05091302130b030c010c0c170a02040c0f1806050904020903 68
    0x8000c5981d8a0f03078100070030614508854840100300001c0d040102c1a80c01a0380c0c00d801c031019034800290160302c55088480a40251480b41c025a40c014004000031034480c406c0d600141e106490440c14200c99111101201020710050390121201c0f84000f504103c00025904056000008a41810320740990310700c4200c40c801017941e99100164600c41010244005201d0400b8064401c034081d02c00700002c8540300140113524400c040c00c0c039844509403400e0948600155030801d4490303060358008020142c0101c141182680c046010030340381100782049041030380344c1e28140c402048000c030380c0c1414a400c00481200062070303c881d0010281a001c01070f21003080f10b00c0e00496450020400b00c031004101402c269220314001d0411400c0180200811407411001c0c0803165090f032041b8420052a19450900860a0002c0e4205082840e4002410790100e03a440805640303945000d0703000b0720300810400b20350640c821040000e0702888040c00b145051340c005c100c00a0000e04031040428131500082c1c0c0c032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 961082473 1250 961081223 961081241
    0x2010c031401091107080a0504180203070f0f0e090c0417010e0307030c170c03130506270a05030a0b060a0501020a0f020108100312020d020d260705040b130303030c0c120e040f 77
    0x49009c5000c02201c00360700c14155000c030b1004015411f602c1c04c0e410092078104495410b808000007941e50081050281d2503140701800c01810251191a207164180300c3c41e4440e1048207034228031a00802a80701042c45240794510084001e18030300720b800d480444003e14074680c00c1c0c804078100c070000a12040000c000b0509003085001941d182c180d01c0e443c81480d140d441e072015000b24401c0201082d05184540e4030b590201c02c4000361068031110b1404629034072180e4000680601c01c0900600a000780403650501c00e0b80200c0c3d080c02026190401241c85698286c03004188124801500b0015030041e001030b5800380c4aa600c015040340c0c0d0341c86501c40c0c041040c0550b005030300721040d21801180e050121002c03c4405d410511402c40030114440074412035000e05000c051035200228607024411012180140002d0b040140c030703420050402c20b074913002c5210440101e40740a4108a40d540280381c0c1080987c3c100c00038440c196080d82068803007179000065564010360341c025043ca042000d21a04c089 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 961083723 1250 961082473 961082477
    0xa0506031020030a270203011802180a0e010903031b020f0a031103070c06080901050f0c040501050d0231060f140318190204051e040210120606080702010c031401091107080a 76
    0x40303861705006250848184071540401c600c1003842c140302680314103000000c1010440001d2820380c4d1040081d0b0020114414004038070350030004010306055140e086100494488002d0400714240448140e946010700303040c2c2c1503180c00001c000e1020900882030a2209404442682c2c508056507460200d900c40903045040810344d071400f8494042000d1203000c1e80b202c07012706172004504001090f40c2a901543c41824100140014650040e201d15010340e42c1a102130f56043d00441c0040c811803a40c152850380070ba8002001450020f51103116070799035464155980c0702e5568070a8004d2041c601540300510340310501d000030f4400029584100801c0b10b15401c5000d15480c0300100788100010345030058940d2803002806144c0030004850f500106410540c1100e07034102d215102c1d50182d402e07401200001c0003140c50004d0005420b41c2040602e440b60240b039008010b040c003c144258120f4035080713020400003a21400501442807154428100c5440d0001e42600b030000701da40c1d01b41164441070791440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 961084973 1250 961083723 961083791
    0xf08041b060c11030a0c0b0f070b0408040501020d0e1c081207080114011d09250e0f0402030f0105060f070c15020f0d0c0b0606120a0506031020030a 65
    0x107028030004500f05201044001c0d008255158417116102c0080d0301555104510001d071b009980d100c945c04858090341d000c02c2c00b441c0d03894603043c1034026401c01d20605002d4040d00c5c1c0300310091881000c80ea00c0c0540b0003820412812525061030000d045454030440740c0060401c424034000403000500c520803a000e0ba6030003400d40c10241420013601d04405400e041c081070005070303421802851214840c08409803050019a40c900701045403100c0082c0407001c0030104050880d031150340c402502041d25000781c544104085900c410300c0102e200445602d910b44460100500203450100028040c2c040110300c101c0c1001c80607120403c0001b503541c13124425001c000f14414002d6014810215954003410203440380665056010f8001e08100d0390080c11100164001041c2d651905d055a04980c0400503896141c58507469070300092400307403100c4d4801c5c0b04012802c02c3c1007603d4014007440f0082a901050482032988a00c90309800203850ba8010545409440c114101220440d1040a1101c00104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 961086223 1250 961084973 961084997
    0x20c01020d060f0503070b120c0f040e040c1a070609080c010609140f0403020303070302090a090c0f140a0c0221010e061602072301111b0316060f08041b06 68
    0xc600d80f03030503500480c041e030004941000302c92412030540b50070390100282d1600c140d907006000034940c03180405805070001d01050119082c0e02009001e40300f248100049061a9121102100c2000303005800c0c0042d0300003000840000781039034103c028150b01c01d0700c4075818610355106035070a407007894000c0c06409a503802c80f44082d000071204503400010f066013440c03090a043d10000c1d1a40b1008000005151300001e03100c0381600d6600e095001800d0888081115600c2c408000703041d41c00e5100b1010009482051525805c500c900482e1010030041d26a251344690316800d03c0f4000030110030030320402044a00010f288103003070150011840d00701e40038200c00e241101030790a50010107a00441158000c003018007580c03c0c45150b1042c60300c080c9444070150241031004075824801182003032010f000741800134404c096018855042035a04409440e005411a002008008a54402c11002641100842412034014421284c102d40142d4016880d007001140400709a085a446480011442c80c194 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 961087473 1250 961086223 961086239
    0x150201054609061a0108010e041110030c11070e01062604060506130e060106051b010c090810020906040b090d06060608061e0901030803070207050301060312030e0d0c0b0a020c01020d06 81
    0x9005407003a100e811103011444c2900081900c4414014030102d14000d07404a401e11418194036050405d000b0840001c04011144c0240070381500d51016000c00c40c80c9444070141180490f04405542030800703038000582c0380810444000c4404492803440a030f8000c10120318910040216101e180550720110343d5092240c1445807040f85050080c4e98a46002c5c4941102140032030f50504490072480e00075120121204113000e40d201d610400c898039868010104105034002080c2002c0750208000d991583c400c0c0344c020026807061581c810380c07094003040103125000743e40c0060700683d400540341e0417140301c00c1d81e5041c0456001c0d800ca075001c1406c000401c50750b840c00300910000c00501c5056441824603d00119503c0314040c000101000d10102c00121064400c00046000300341c010024841c3d55524142100e4031900d4072a0350002034146051005100790000d8072200001a95403030400d00c0e03170710351140320420304050308441d0003e0b003c0002e60b1f0007840900103086500411403000500741d10300118 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 961088723 1250 961087473 961087481
    0x81512010c0e0a08030313030e0d050c01080a0e070b0705030f071b210201110322150905091909060507080a0608071505030a06030c06020715020105460906 68
    0xca81c424143d4810501c1420f1002c800c1d40c0c0c0110201050f024050703d81c0c40e081d1542500800016005040c84010000b40000002c46950083e001c1e03c0750750194403440684000e5500c032011a030525404100704101c0155507070001c10f000c80c02281540d0801d03140c03454011403503108442c16201400c0219070001c80e00c440c20072150046c05030800302086095050380540c860031a840020b810321900706082049100c1c1402150705400100c00600c1e140348540c0031084d40c42c030581c0141640340e400802803403210741c0100d030580d003542c5004000c413100c1c1e41c4200b280034802035400410740399240c42c2e01210000955500400c4c0c0102010703100c0c0381c158600516074000311917083c0e00200c6d180e030041d601040086611000072814000d00d24000d55a603982c20844030180c80281d0004050301070328000090000d50100b00c01c820f0711400e80513016102a0540308078280e07102610030114407244010480b0800340e10f21341400c400007405110b9440540c9000c1200b0700040799140354141076444281d54020410303039107e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 961089973 1250 961088723 961088747
    0xa080708010b04050a2d0602010c1d28080105010f1707350303010902071203060b0f0c011b020d03060816031202100903170702030910081512010c 64
    0x20642003915080c0001e040034100c0c854403101b070814802c0d2030100995a40070794451b2050030084502c84e1780d10f400081c000d007400200980041c2071400b1841801c00072115004404600a0803000e0882060242c00764804034102d004c04000310400001aa1100a0042034001c1111140455010b131a281458444942c000c49940701500010002e10150003081c0c14078a402c0c61000d04d49000816580c0303c1d1940c0c60600702e246e6118803000c000000d05015640041c0107686c4103a942c0366207100c00c07480582c241c0f03819004446028070140007090351035040c00301a1981c000088004603041e4041e80c0007100750b1a603000b0040c010380001f044d08001e079805005a200030b204034070050a164075034130207410414640c0d001c010800302d80390081c034903914400c104032259070000c44070400044445180c00360410425495400501e00060006103400d40048107503846088003500c0c501c640d080810341100c0411008049121442c000021400b0380d032240001c084910707580170000501d40e0300841010b440b2181c064 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 961091223 1250 961089973 961089989
    0xd0f0b0f1f0e06031501080d11030408060403050310030204051806280e07080d052106060d090215040f08100507090306050606040b1218160e09120a08070801 69
    0x510070080748606405040100d03810000c800400340c4418000a050802d00e61401980004100000c9104030020880300714140942c0c480f02c0d0003180c01c40d4180c0c3ca0380206d10030640c464007c5000100030a018030b0086a02400d2001c94100881d125030000d011a03030169400079461518114080d0481c2c5c0c100501d0b074110070541c121002080d6403400b560004660302401034206610344540e00003400d402c1040d80c01400d0098142c6040314102000180b41c5d402140d4611014400700d0800703002c14001d00c03840f80c0240c0d4041c2846113070105000410000c0c0803d03410890f0048403038080d60180d81c00c0078020380302900c00c032030f0008003003032400201d04d1800200c264a60300303c501c1c0c402401115a0071400330380840750321140c081030030355840c030000307050b8003c95110f1001c28070300242c40c0f6861403240103074502c51003100030907015545150614907969401c48940702a26041c040e000e01c143d004000c201644060504116102a44014601c0310983c0040c81d620001c10b0303120b010301801640004032035000d050340e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 961092473 1250 961091223 961091251
    0x90a1a060a061103040b03090307030e2b0c150c030806091e19050703020706050f15120c041505120d0207062f0c040b090f010605090d0f0b0f 62
    0x3000048902145210724000d006401c0b00008280d5401d10a80b0002c0c03000701c440c1622031a1030984e0340d89a500404080f00068200030710300c101880d00d0f0362005c01310728029110070410304503211480c80050b00075000307860700103011000058a0004a481e0b0520040950740c081c442c07141880c000e01502c4000d40141d10a24403c0c00308052a4402000002d01600c42244602161110360800290303d0030b0383d60351103046d401c0c0020054100c1e01031700180f1441e80b140008010715601c10f1006841c542c0155000d060003140e9054203070319840d14203801410941d080d82070f50240212140080d08460390201042c04074294400c04214900d8401c1ca43d5801c100c80300e01408010004000003925070300301d0300070b840a002000240d501c00ca1030100062441c4020102812032540c00d800c00140c0c1c031600c01e0006c901c40c504280d215019400c0c50241503000d20f0104543ca1445d03420400d0603105a0008825070f900500c40300d604c040450107451504101e00d0089070200a1130400174040c40321740ba40245401d0607805070b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 961093723 1250 961092473 961092481
    0x605150702030c06030403090905070f110c03060105100e28060903080a18051c0c06020304060e1014070602070c050d050a02212d0c0303070b041a090a1a 67
    0x709400f05550001c5501d507035281d45515041d10400c3c402e400801c4010310741070401800b07035084118020a09584e031100305500701d01c08607044c0d556040860140d00b40d00040c004004078240001d00c003541402c02d0411038400d114003004a8580120089644084601c048031003c1e8000340340c5018000e005d00e03241c000255410340e01c03010860310a03403190303904001e4200a00003e5114000700000585001004032142b54081c52805200f040e20f0401581d10314443c180c0003e030709000008807400c40300ca50b103c0007100c0030807000b00a5030034480301007102482100880741000005440080a2580c4607150042e2590250f0408009101807508007500481041c0000c0c004254001070880c0500e038100c0f50302090f100804070342c010195182c40898890b100c0c0c00c540a40c030300702e0814000b070500040f4003840584c2860601882e5a1071110800b80d03050b420410050340030407481840d8036070241c003902c1050305003c00704950304011142103407002e2482c1c120380110700030003000807025075600d000d4016880782824 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 961094973 1250 961093723 961093729
    0x40f060e010b09030a15050a0506040c02191e0309062304181d01060602060903040e0c0c01061e032003030d0c0e030102040303030917030702060105130f0509010605150702 75
    0x4018011407005010110701c0300c3c407541e0104480441103a204000c08414501007801001800042e144054840d013854006041800c103440381600c00035040e030040400c2001411800d0080c0d040300f10a86050300078000c045e040000140102d00c00700e200b980c403103540c9071419030001d00e10540128401e0200d004500320030226100d42c0c0c10b13503080d580302114030512885140c0144000309085d0091444130300c10441d000004080660042c011110503400b500d503181d5400c1c031541d0b2244682d0050f803001c0e41c1b010340810503000c0d40c0005014522500d40c00000c03010340361003051405491f0402c1e50394043e0080030380ad00800c0b0038a4542a80e00150258004042400302c001a0316401004071b05207001c0d07035802005c11154418824036501d004060003c55403035441c4e0500601a043c90071007541d229544003920f59000c82e809040f2482402580e01802269082004002c2c18820103401c1054040c0c0300d49854158103294840c0c64000c1c0c88040000030302904e00002d10280d511440c10180c1d120f6410300801000d61 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 961096223 1250 961094973 961094999
    0x60f0a020c070510020309090a24080a060c2001020a0e010f14090f0d050c0a0501020d0207140d05100605030d0906020c0d08040b030a0c030b0904031e030e100902040f06 74
    0xb8800c680b031303420031080756074128610b00511092070342c80b0701d2102c1400b01280b01a40070404035560703400701c9204550010180700380d19040e40300d06420340e406258800c1c046145640400d42240d07440c5040342840081e0038182004000c11a00500282d600088482195030419010381986100382060301c4605148030002c0d019a291007032200000f00700140c1c18a03540d41d00a071241705050300610241030082141026581c9444501056000c0d58002c24003003000c1d800041da1011500c0240d0040c426a810541403103400c2481c0442d03035400104103915080004c07414008881901d80724900061128030309020075140040a03199a01031008941c1c043c041260701041a00307045205a6400d0f1b0401480d00e0044440e00c140d41c4846d40f81c072004402c0c000e41460f41e400c94142002145c1c0c090100d40e254900708228224282c13002000b2030500c000c01c91604110780e03050078018041d03090025071506d0402400e81440300310130740e040305a55140103070740c110300c1c041c07003141c007401e44c480710400000d414460303044242 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 961097473 1250 961096223 961096229
    0x11070311071d18101d07060302070803190906090b0901050105010807321b1002091305190204120b0f150d050f0307080306180c04050d0501021b060f0a020c07 69
    0x2549a0840c0070800841000204000c843c104002c0020404844403a0303c40c0d2580c00c5c024000d0f015522001a17a94400d00036a0501a0010310003455038940540d105887ea0441da40741c074595803910b001d5008103486201d0000c600f8022810500c3c1032614100b05421144140c2120b414070440400344204a540501182040e050744840203041e98507906854054861505540349080000240440c154080c058410001c05075103040366803410400e5664802d90041140e00c603005001a10310416400403a00400d403c00310040c00d0322541c81c0403401044c2030b40d00030381200d41001400c0274040304102940041590004000d24180d14a0400000003000004108001407160104034510801c1c000c044c42101c0103016604100d943e2541140340a09080e001190300c5032154400c5107034159128a01e00b1011302c19240d01d4441da107041d050504101c1603140c1c050080d129507509000841b120615061a51a4020070300002c0881d85002c0c0c400212601004044000086c018800303074a040340d00245150507 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 961098723 1250 961097473 961097491
    0x62b05040506181c1b03050a1b170a0c14010b0f030a0c0510091814070c12081f1205011514010e060c03030a0615030c0206150411070311071d 62
    0x10401d144d02c0c101e0303401494242c2d9001310448401d24004260300320000341404d54690301d80c0e10360320a0901030202e250303c12081c00742111b060b4141402c5203104060040048030140e0800c4510708019407510f10061804000b07406e1141e560b44a1407081c0c0c80d044020510f02d000c1200100319420f0203550b523803a2500b05219050081c0c1c0c4104114103071a0080039014003810200c80c1c1041d00e107038150ba804014028400780d030700301e0341c0096003c40c4a03d0b2060710403120320b5411469406828330707810800c031a4468000c001a5020010021005041c005404004001c049212003c600c1c1911810206d00311001919090700e662003000c0d04014510a00190030410482401c01084444400010130581e20400340c040e08107000c00030401c88803508661051042e291202030418160180313074000c1c1c0454100404e00c001591155000580f01e1200c0400c882c0c1d50301c1c0240012503a4640100520b602d50030031001100482c0080c41d000030004010000c0f04d00078218140e08a1003204803200b03440f1050405010591 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 961099973 1250 961098723 961098763
    0x902011e0c020607110907050406030b090f0f0c090312070b0109061d061504060309050606010f1205040f0b010807140907050a050306420c0c062b0504050618 69
    0x90246001d03c178250f01c074010b00b04131058600280700a0559000d4059080800e11300240003120703090220f14248902003110044030162150580002811801001c46408400070070040300c15440c284078000c8601c2244d541140c4400c070901e040048080140c21280056140180400bc5076842100000c0c03a911006100182078888501188501da120491a170301140c00003400a80c1c154180d001c0c0c000107008030280e81c41929a8401101d80c09040b40803040051030b00795540b409485c0d282c0c0120f03000380c810180303248490f106542c0c105009000340e003d20031541180000300000595503040d20441744d07044910a81c1d519010001400c1c90080c030f1301040030420044002195515001d601503c2d0404080c244e02d120301a0300402000c03507a6460420340031350090021044059007842c19991801c00000182040e80005414070034217800c000c0c031101003009252509102074a40b1403890022404116011500346441e0400500c0c00c00050a10401e0b0b00380701940080c0d850002c5903d02504500804d444 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 961101223 1250 961099973 961099987
    0x160b040e0603210f1201140f10050316020309280f21110301050103050d120603051c2d09080a0203100f20090103060503070e060108040303020409020309010902011e0c0206 75
    0x4a0f4010700d40305c0c010800d01c09001180300f05071164040d144200c115000380c0701c0380c0e0140034404012103840705000800c0085c00441c01104100a450881c00300c148102c1341062000c800107000386a2083c1d40e13090140701a90701c8010920511a050060120030005034240e41c80c0a058015610404401da40070048000c100c10401c0310319207107002d100b14000e0003404156120b0501f540c81c4e95104200c078011445102440c034043c2ca640c001d140881e0380002c05055803506e00c0e01d181d07079480c0c10780100350208030703001100700150a5407049154070700e190384140c2481ea081c010005019128250001075807a403240340c540c0016600001c06c03031050b00e9403c4010580900c051501805048030600b0382288a00031b0348200002e1903100040c00034008240c1e07042c0500d079a240d0516840d895503000c0d94901070343d500001100fa50064604540061003854014070b01580e031200380040707820950303031f21215944a03003081d4159a800f82c10050042c6c07908200c180c2d0031100d000003030710308030102c5002805940049611 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 961102473 1250 961101223 961101247
    0x120405150106050415090b0c100501140a23090a0e10060312140405060c280807030f0216080d141303150f1d070603060605030402060c160b040e060321 66
    0x1c7c44000b140d907460b404080d004940750714030b91000c4100107141c07800018540da84812040c1403000080d1080c04d401c1d050040c82c102019682031a2443c098583d60786070b60f070342c8031030315520f1255003110300006011054541403410910303070780094501d103400d14600784082114100c03d003910741d6403418000d0701030b800100500c0352030080e070340061307803040000c2a07001b200600440d40d0306da104011222203101200c0140041c078803002807000617003001d00a11500d00080d00a01103d030344000103004a0f440c94100d00c61b08040141580c0160b5104c1d008040c84016407030f0810091402204825455404c207050445601c2d00180385110250003c0656003140404410365800b03400c3c0b54504d9601400b52100c4000d040740102c0f0390180e90240e83c8101640000c2881c0710303110f00801d82d1079555403a403654a82d6002c01a945c0c0103c42803088600403400c0e000d42030070950403c840140440c9038807036240e502d8121011102c00004090340e020703800c050300801500715000011200d840d90b414103661104605644 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 961103723 1250 961102473 961102487
    0x9121b0605091b030f0a1e050102131401080601210e0d0f1803080405013b01110606061207140c010902090109020a1d030102070503120405150106050415 67
    0x15100da494282403246460001ca0700107000c2108201503007005294100f410740e2810107540c0410b182d0030000f60a400100c40303071039402c000c00e0000c49012840c02c2c551512801c90703001044814042c110400104448111306041000542090903d4015850308100107000d0465400e8014141c07110340d0004180301ca1194884c0501c0e6282a040700d0071b02c0302c600030107070404170400c01c50360200d05c40c0990410251860607401081e286c0c0701081d94180382c07510300103507284454420904481d00514160070003c02c2e541e400076100034454807281d41000403440024017007002c003c0c030590b8035803c00f0040002544491044038241c50100045224580c1c1c1c050088608a00ea02c0850034900300002d01920045015001194918000c0f1600100c0382d0361602000102c0c4106841040440c2011071021242107094080890718031018001601c1e103a9655180341c1154803144c100c4460a41c110244010700404000c0d040c292580ca0130f070b9105d5541080000317030142c041e5100c1c503011000070364848001b80d803040e5a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 961104973 1250 961103723 961103777
    0x1803080d0e0102070605010e011505090d140a05070306241406120c0316031a0d0c08240601140f130b0a020f0d02060c091201091707050609010912 64
    0x40215142c0c1e505207001d1011b003900303116a00b0b135020303500004140f54040780d103483c4442c051520307500e107048000018406a80c00180381900c00e4076a80c410484101010700a00e001f00b44a00b020700052401c515004007250740c03c20000010000051029000142c2c2c00140740a450f08156020041e50071034000800c0c034822130b68a00c40b6030340f8000500902c1c1071904040e5010740c1d80100d070400c040e40b8800d0b0860896051505100540c607040d10200d0b040e0070503285000c5007034080c220368000542c40b420428907240305c00d1000200c01904800c002000859000d20517002082441c040440345490810f910541c09025105012048000340c0801d4004188040d540141001c00c0c1884d1503004000e4007a403200e06988a10500f40100b41d40c0c000c40500c04a041446500b01515580c100b410a0090115006424102010700e6590b07009000c0411480c0e402c01d4041c2441058040d40e409552400e641801e10242120782d060707060103104c0c000a051100805041380440c90b203100c82010f031000b00030000c0b282d0780d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 961106223 1250 961104973 961105001
    0x20405030a0f0308090604020a060503060a0f0b041706010e01030201120b10030b040b1f14090a0305161d06120c0d05010f0b1801091e0c0e0a05011803080d 68
    0x100d40784041000c018507400c02d10b0302a444200c070701d9640c0c1d0841520b401c01114000d50000c04104140a0f030750241c8041c582100c00600610905602c6075280c2041100030341003140e00701d01c00700b401c100300e5400040300b22039480000054161949807840b45a00c0290600009051002d2840010342089403580302c400716500040c0480c003401c82810000c0e0091403043c11580c0100e05045174a0300c03509120000740140795005042a641034040382c0d046a003045000c40006090004008040d199550216154051030045020b0410007000101660b02d92940c2d0340100c42103401d403c0c042c40416000b00c00542d02030300139918800e0403000c0003841401c2c203080c4e0941550002c40104a04140041540135400c0802d604108000c03400101c401c0045c41d464007507200e202c10856078014803110510b41c1060540303801c08070514212504c00140703041a132b02c4a18202c2c00140030441e82064500e440480034004001c203080040342c82c0524040c15580d0001c0f40009011028001561540010325034003400300d4145d26 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 961107473 1250 961106223 961106233
    0x70f082418060708060f03030901020606040e0a02090405071d19090f0615080c010e060319060e0702060a050f1e040512071104050612031605030f0a0e010306140102070905060402040503 81
    0x560000360460078185d0781039005404040304140282400001ca40c161201600142016940c8104001c00f0304114508044140250412880142ca030b1070042d6004500c2103000c0c080706820803a943d07841c40011011924500004010311034030881c0143c0d400c4500d640e0910104010045080900c480381d0050401401240703442510880e220300103546606851401080c0c8a80780070380e400454242c0c0418941952009041010907c10000c12004481500110b0004a856075442c080746805030411a00d00300542c003e0300402c40c00d07030858400c281c1c2c00f0801c985201c009090150700349451804000700d8207426800b0b000424184403040086140e14051448241c0c4d555a42e8a86051841c043c1c0072103034015801c2c100842c0e41440c1410684542d0921040150700f041112184002c400181040560b55400300b00300d40b16441c0d0500004054a801c0780e140c604441c480d106c0010100c5405621208403088000e2036020240e07404100c400456840002c045040c1d11035000013030003482181e000b16410b1240c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 961108723 1250 961107473 961107481
    0x8040f0f08041e05040c0f080603011104151b0309030209090114090f011109060f0a0918020a3f11160201090e010305070b0a050904060602070f08241806 67
    0x101440302d10f20450840f101c488402c0c1e0303403410f2205480b6800b5104010500c002944d218841c411481c0591000008001046044482c025071040740e200750401d0003098000e20340000c1c403036048894580ba030380401141c58101038403600d0040100c1e50a0000070702c01c60b5210041620220250480e200f480c0d09840c1c0441d0f282000b103031484d900c022440d607000e0781e9402c1280843c03400c40b801040d6151035034098091854815500c903d2861b03540030050280c00e000500c0760214003074602c240d9494808504080040e9103061591000c2c00a248004c4442c001da6058011854001da00006400d01c2d200002900d2a456000c540b146024010101c00c1e040c9a041c04110321011440944040802c0c0c0c1c003c0c0c80e000142c90325503020103501842404050507a0b40107420410059005000809803040d69103051400e120300040050152007c90b48a8001680110b90a0007030f0b01a0707040020003007002c80c00070095080a500344100c81c0540040c412601400040000c3c03007540c4514040384c250503d5425122903144c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 961109973 1250 961108723 961108739
    0x7050912070f0810020c0606012012040e060d0203100b04060515030703060608011215230708240918070b0a1206060507170408010c02070e0901050103020108040f0f0804 74
    0x20b07040c8140d8a0520501d064116050030364400ca07840044941d010380380719501c40006403880b40e00400203500040b40300c00f00c0c240314003061080c501f4448400001da59142d150000960182c036000e81264030401100d0003013001650300040800700b989403040c010039034840880015000788880d81c4000d4001c000302c884d8818804e5130000652042a075500d00704480c7c2d1301d0300c4085032440000d00451010109201c0c0c42c0b00400d04010608408800826020401403558054402008503445138401c2111140090048007604203804a03400102c00c6403075450328002c0c0d4106451a42d60301a56400b0300240c1011615680c80c0c101341c0700c00b52400c40c2c22a9011503445100000c1c9601c0f0114880018005022000151480340505000c40306603a8826041c50303001d446a5024409425017686024070401c0f0018140d4001e0240581421032a0007410b115450188a1143c0c8540100920038591400d001400140e0b08085010b421507003010464104004a180000b150303494200d000d0202c40e000310700024484 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 961111223 1250 961109973 961109999
    0x60b18130c05042a0c0302030f030c040b071101090806071b06060b03040c060e060702010f0f09090c0c060605303d05150d0204020904240f0e0705091207 67
    0x1300e1668028400000000049030015001040200160003c1240243c1c20090b880515000702c1c400310064982580c9251035001513012000890380d0300c414822860f240c1da00139049070002e203240409030620b460300c580005c084c0c035103e004000d114902e845104003805a030b41d00c0b10010341082041e4942c0c07403c003804c207601500c1051142c1f2000945410101850303050550075584c0840e4180c41d9001c070810030b6001900c68a1064000c21700b00b191007400012000000c4c09220602e42a070b0b1180c2c09008600d00741002a0751107030b0442d40c05800f40074030804140783d082c681a8138550000000d050220442e032111800c0c81d11f00e04044420b21603c12500b44009402e070034802c030800c403010011007000041e02440302902d8040b58030982141681d00611100d0071f00c442d500314070520080c03005103040e6400002a048804071405203070081075a03a0301c000c800d08a004e1403c040e2640c01d440c1210b10b07107030484000202c0001407115040220105604005072104145440d81440b0b217004e0b42c10440c1c41d01440ca94007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 961112473 1250 961111223 961111271
    0x1a0117103b0414071a0d1407030516053c190f030b09070305090c04021209010506060c0d0e0d06020c01050f07050a0905101403070804060b18130c0504 66
    0x74020032581483d614000f0745441102c21040c02c840300e000e403016441c80710b07130001c680b044c00050b01c40f075440038246400d0113203503c2002207460000d60b43c181350140680c000115584041400400c101081e10806056040341051880d580710f8802060690700c6032100d504040e05c2e10651a90210780c6950011414501e0751000305113a44413800681030040c110300740c9214044883c1c01401c00c8002c01d0344244240c01080d071202911040318030807202c41c4049070881e070203c080b200090b000c04080c040348580a0040d41d821010880e5400d007410306915441f03481d200c01350280d03c01d00c8400c08400c0c1c096181c45a0721600c0a03013160085403244004180a0f01910084500341c642114050004200c4e5001e8010358110390419980d44080d02d044ca0188400f940c0c2200c4c22000b40018850480c030141c2e4030740000c510919090740c0d204218201071402c503054410704a100b901c1481440300c80e030048140203461036402005101c51804082c594180020601c40540141d80c0050824030311201590115940c0850 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 961113723 1250 961112473 961112483
    0x60705191715040b1c0c0b0909010b0a0c0204090f060c031104060503090f0106031209121101080402010311030a0b0108090a0803040b15041a0117103b04 67
    0x400850603000312600071550342008100d140c11404110040c0b11050140920840070708002000d10240b4000b400e1580700d4a00c9201100f140b521100400c5010641c07070000f8005074040300d040942c9800001c0501c0b10500441d02c4481002c030b650208a441141440c50b01c039005003080048840a04041c5064a030b054000e4500900f452440400c05100e0320980415854243c001420305040ca40d0448180e0b1001d0001c038030718810030168118880c001e11400c00114403905000043c00b15040c40a4151001c03607100c0d20400011500706070105401c0b4141d00385079502460b01c0360145d81c9920059004080203c8039071310768080841000b4850031158004200b00b0000d8807502100d640e05820f403541ca0b01017050040c40e010061004c1400121380720b609940020040300d011861228041c04202116050106490300d583c605048a170556003200c41100c20980340408800ca45c500030703221102004080c8940b03000072040c0c5191042c5114200c0c0e512050344035403582b01c0d810410407824500008410b80341955 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 961114973 1250 961113723 961113757
    0x190b040e042a050d0611280806130e030d05100602100603050c04090206160503310b0a210509010c020a1203090f02060304031d0a0b09060c070503060705 67
    0x2541e1894015074070b0045201e68031078002d1074107103010700040361006041203584035118141c00c50081e10304409031104d109407500c040c030010404544603031001400c45000d4240a246401d000903030300d50040c411010340b4403800c049011070b9140c84a528620a5009104c4143c8c40c0005020a01c942c9003250011651664215041c446083c0c4020044440500c00289150b004000303455160a080d00701c19840c5c0d000a05442c01c0800442c0120007150035103c00700d0f125000080d09a02c1940303219405044045c0b024080c0c2c1030780c1c500c100c0045242c025802405c400b0000461240542e51090843c00c4000f540305214580105032402e24002401040e95404655420007280180711071000980350300141c1c1108540f181e100c00300704160010001803209590704103801c40d5401c00360301c07620020740c00303544030f0350300c00f40c42341c0403010041c08140c0a00803081c03041540c10420400d54007140142c2d441801c1c04c407241c0755150281c0d07511600d08245a440103401d03008000c10000010b4100000e001c0049610305994 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 961116223 1250 961114973 961115003
    0xd050c030610081011041a040501020615031902370803070c0e0907030b01060203071a070c08090d140a0b070503071e030b0303300601080402190b040e04 67
    0xc0b000d50b42c082c11225074410100d11041801e2a0091840e00422420161406403265180d48000301e0207007000054040c005020801560f041003503070740c4003e40501800b90b1208160010751030740b0b401c0807040c070b41c0ea0b40d00b030011003550303a25030800040c0c01d44005d032005403044428150b8103040f0180c41901c0f04411080740040d0340701d004000c0f54074555000c01c0d110300141c108483e25410010241041c1c001d842082c101200190340d548150380138080940046480700c0303140ca032400700d0403008032007a00301082910904c05125042107140315000d0f8007945150310380509801240d00915401c030302810040340e944051900070030204044000a0041c800b6540e10b03070b5009420344440c4015141b80300010310381401085002074042075070300e07290090b14022406010400c0024510b402c820741c0c62a803102114401c00004002041245142d585140500d0046c902400041d10030300d00240061301500c0384082050202105a050300d01500d006049a078445460300c1031410080400c45084071010500d41d044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 961117473 1250 961116223 961116241
    0x519060801090503030417040306110c011a1e120d0c0311031303030509010309061b0e011e08090304080703050c0a0509060f041d07090f05060a030c0b0f07020d050c0306 74
    0x8655060340283c002e5103583c60f90303076445076415034644120031000300a000200000d00c0b00d0023a110142a805c580715190b81c1d08001a900b1a8000940c020f2a070312901c01000d0192111031600c10710314500c0c0c080030000c2001001040d00541e42562903210741c000d610918014642240d210303005035002c0e50740c007880d141248890558030b02c500140d0b050410899201000028400e100502510382c0615010844002d1980c03409d0554031402c3c1e003110300c2e1100e21a604461a48000c410044a40910300105100e251152200c01024000c0c007100c00c00600c00005203580d4400c0044400400b0f104d01203c0b401581e9040051701d030700241c82d03040d02c134081000001400b89014050310b80a94801844e100d000d08062007040002c2c00c9280b8848060092151050b44081e0240450300c001c02e038202011a42100c40c608250442d1401001c2610070440c4c61700902c040b84040300c60b04d003a1500403400a5071620483c0c2c880740780d801004002035000542103421400c00c800070441680c03c04041e411511161514102 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 961118723 1250 961117473 961117481
    0x80408070f0812092706030d05040b0405040203130c090c12060501171f03080408070603110a18050603010909060b0f1e211c020c01050423040519060801 67
    0x240d842c807a400780100c2c1000e4078803c0c00034840340744020b080f000d003c007074004a610355882c01c04803a840003100d03034200b00b83c504003801400001285890003d26080c1003500030912402540215800b035a404400520000050550b10040d117401c01710010074541c0d2500700d14080c0100e070100500007007a0b54183c030100052400b030181525016120400c071100300415894840100614903c2000182d0100303841991035862210080c5025140441d82c9605045015281200e5603214408142c43c104440080e01200c8042c0d5042c2c090919140d0303061242044401001c400310307004150b008034000700005041c0c220ba400b4800a910581e400d0182403020310411084c2d001001e07055411001c04410300b00b44111520a03600d10b44402007224038400c03d52015000704940c414282941c1c0c4e403000d549407842c1c0000c0c1c03020b0b080d240e000740b00401355003148100083c1603001c2d030304c03a16094081110f014002e150701281c0940001c8005001003101e13140c4048180030b0b240310b00da18032014030314186000c2005403040c05 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 961119973 1250 961118723 961118729
    0x60c2710050d0b0a0b0403050f0f0a0210050d0c050309190809060c010207150c08090d0c06021c0c05180904021e1201090312060510080718090207080408070f 69
    0x840d8290302802003054406038032500d44100318554924645049503540c0125501900c04068800c1d20741c0d044d4544549400f0080e0000e01082c0c0c4030b00d02c02968004000b4a04418540c1920030043c0c40c03610841c15a454000c807902d0202d60780c01c2002c1d00e90060790000203507210b12041812a103103019a5400168400d0035548003a1480c07104000400090808000405030090040001440c103100c2d61038100c401803174803002c0140355460f032038055030980c1d0118032180c00608840c081c0900d0b11440300302500300c4865180c000c10081d00130030590703103100c8940c2c0e5865016a005c0018001ca062400300104103501003004150001407154044546003007040d0051702c0307180c0c0904181c00582c0e09507050090b0314003940c42c250b4843c500b201e07003504041c3c003070190800b41d5110351221858052035198603015a00d068001601892100040840191740140c08a4100015060114011001105450880501b80c001120b45400007410804011030360004004441c1e07984107a810fa02c3d250400d5507031092980c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 961121223 1250 961119973 961119979
    0x318060501090c2028020306090c0423010e15031c12151832070e010e120118150b0301020c0d030c051c02030709170d031d060c27 57
    0x244417400801c1e10488101c41e124074644001c03405905640080c4c40d1020403075001180d030300501241401400c16004007080120b29a4803203101100b4181860702c0c1c0a014410541d961342498042200709000d46110070200e4009002d64a070300e0b1044243c5c0c400d05400d10003541c0095640c03103000c144c0102c0340c4102c0b0700c0070780050071004042d40340c1013003507004580c61029054555a00c1c00c0648000b4282c600351000c1280a00034075501c1c3c8a207906d41c0481e1500108044240521250602d110384e03400424040c1c0c1d1a011a020000d180c2824220b034018142c00000402540d401d103000010301ca0040c410101c029000e50703003484a0303040340c0c040c1802e034080d5030905d03045540702a0002100c40d0080d000f070b400740013a034a405410b02c06040d54007c0b90804003240b081c81c03180e0000600038182c3d0f200d294100038181d00c0c06400601c80303000c2c80156480404a421904141d0349503100740f03820340700421813190b4440c00707001c6900904040307546041c141e104e8100502d410075248040702c0c0d248005030760031313520b05802 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 961122473 1250 961121223 961121233
    0x2030919050102070b0d0f0e060106090e041718060318010617031e16060b012601090908040801150e0f0c12060f180106170402100318060501090c20 65
    0x40302c02c680c41600304010148545496802e481c03030045547c400c1c25641d0703084000070278681d490020041d1400000e42c112221300000f14041001040c0d20000c0382c0c2d40040c3c403188050381d45420390801d6840414181029901c41000428007001101d01070100c83c08142c404001c21207640d59070034408042c000e80c205442160024000301016901e142c0c60b401c52054414111454000809042e00f28008091801c03901c841d5590080c80a0f542e008540800c42180c00c05516072041c00c500743c1040c9000144680d40110b500d031145001005814421f86d170090002350001e020003841040700040007040303070050080c44001e40000030007001c0c0c8200302c03c0c0200d88001c10b4034030380315080c0f02c40d084c15000109640e800103440d500454450303c507804014068a8001602011541420001000b0240303100001c0502c80c403500c14000540e4502c1d600a4122805003000900d0f0207848611920242884c1c902034451481d15000107444902038010100543c8181c1d80c8000b81031010151882e0b440980e00741903042d9001c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 961123723 1250 961122473 961122479
    0x30d061e0e0403020a1b030c0b0a09051c022e0c170304210807031a03030409150e0103060203060f04020c030922240f05100305070903080a0203091905010207 69
    0x10181150081d000c0c1c41a00c0741741ca6151a0603100c0316143c9103942c601c1c1200c100400c03d02900d11001c0025050f503c1000d4a03201d6200401000d044035805103600c1749140406250200721044141520158050800700020232405007221003100040481d00501d1540041c03504010300c84c401c4c0e5061640d112142910780620642c0d016803c1e040103004880c1c0980b4481003140c6e03109044000c600c04211517803000407a18100500400740d40100c1040c029181001e03441d42d1046c0d80210a4a007964000c120008030401c009600318442d0741241d1040119851307400000c018008660001e6110728001d403540c00138030307480c0401c1c40b08034403c02c1e0100000d50000c1c04003040d1f078504500f43c00c4175101403d101c0328042d0300042d004412903c0b0100120301d0200c540d00321f000c040015107010001007520383c90006246180c0808150851140300c503900403d6a160000780c0302502903086c1c54060754001c2407130340d201e683d600d20103035603075100701503075441406211100040101010121019688181c0c050005540307 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 961124973 1250 961123723 961123739
    0xf0f0b0a14191518080a02040e070e0928080d1d1902120c0d1b0b130302240f070314030a06060816051b0102090405010602030d061e 58
    0x41c200405644200401c0242c00e00940280880014241030320001054542198014260740e010f890060f007020303625681042076807004214009a560191008110781d40810b12050400e0b00503000700e440b0100704004c0c4601c034030340003e00e00340242c01c032404d899010b07880521021142140e0308005048400802c400d44440645e908168004d1130071040c4842c80c6441080300306d0401c0c0741074900740f00840c0324000243c1545482400c60608603985c2c0301170000c0010820118040c2aa0b110001e000c1c01100c1c8a044460307484d5a02c031a004101c00c0d00280c1d00c85c0c481800301c0e580180030380310076031088089144488042c0310541000e94200d078124002032804d00002020441500442015000d0056441e10303100c0c164205401144039000c0140700180d43c9080000160190f040500100090303600d8520021800b50010120307a003046815510100030031086160034007a120b848017050b0801d007441c00000302c45400001400301036101200070300ce010703110b032408010404465035a10340100102c00c1008450 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 961126223 1250 961124973 961124999
    0x103060216050106090b3f15010603201918170c010f0203130905150d03030b12010b01080a0c0309020d050309010f1d30010f0f0b0a 58
    0x290461016924091901c0d0142100e1159011004081d1210910307009454259140e80c2160041481070f120000791488101507400c000c21852403050380500f8004004004202105480008c000381d6207243d070b1500c0d0b00074050254501c03100404110880c0d030305a50710781d4405603403070460065480a070091040400710340c1d280c80084e030070303a400300c10007400300310144814400ea500ca84140300400d0300030b81040c00141503148076808201150420b01c54038407481c0c032021b040c0c0100c3c0c030070500102e400d845042101081c40315500c84035074412400ca018204040e0981c00101950100300e42d0484803c0ca141481e500b0380d030555422500003a441720000d00d400101e5402209010b03100d150001d0179048943c042401c034204070800f501d503036002040309240b56034040d80440b2107010916000710074200280c560042420a04c41d0544621007402c2c1c0e0785500f0900f10002200000c1e152090500300c906003c90314000e042425060108034103052036888a02054003d116131407402410b8080340c0d51410700c02a00d10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 961127473 1250 961126223 961126237
    0x130f0b0d030c06331409040f06090809090f0403020105010503030f3408071101260727060810080d0513090c0e0f030a051209010504170601080d02010605030601030602 73
    0xd65954a59201c40f2940d14040444001d005040781e40d80608011007400380b180c0601c05c851046050b0406c01c40001c1030003c040742d585901401c007241d001117600d00380c00d560013450301d140d8214066204003c0804081002030b8091030294000300402d91700c0d401415182d102e01030700388515079400c01040d14170703152407070110705409072407200d078a1856a10f0200c000c13180701c0a001901d943c0d0f000700f2810140050711360290f03005503003400e08004c540c518140a214100c4206826485600b0500001e50058003840c3d15940c958400010140a0780500c601c0c5840d03110213010303d5000414000c0010350003480306140c6000c0d500c102c0020540c03008401d6045910380c0c00f0f020010110211a2070014100d080380c0100e1140071881d4407001d0686c144001809042c0380c0d03102a0070b00c07030f62040d01004081100070400e207a0078140c904116a6039214480142c540780f266500c01201c01d000c0d581d800368445c0c40401c9140c141c40440d0155024510b00c0c0708102c0c281d80c0203020351645900510010400907d06034010500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 961128723 1250 961127473 961127501
    0x5010206060f1503010b120c092d09010f0906080c091b120406140c070b1b0906040b0c0d111b0103110a0905030c0d110d06020405130f0b0d030c06 64
    0xb2590b60f07100c24014603082071384001d0308a80046200d450348450030f48040d0b03001c5813443c42c060a0414213400140d80c1c0115111031541d000c1002e0f140392172120301115440074400090440c0301a565103490301c80700d40700035100d6851214a040301c08a02240d0210752114502401004411543c66040010141c181c1440e211403500304208820307009240c2400303050f48624000e510001d100100c6008079490502e000303210742141c2e0720400100000a0b0010502c54002214803410441050442d103c20601e01c60060b0460b40154042000540c1c4600e03000200713468503446090b40d550290b0040d06403a4441407042c50340c010b800076100b100b41007594032040720103e4814900492444203180286901754000352003980001d501c500c00f44110705040002c0130740c0d134000396011080c054032911800710700721340150035502c100d05c0420144107100050b0151006484002e000c0354203001c401d20580000c00c058030201640504010401c2d2a5240c10100002000d4050701c0c3c14219541590b2000d004000950a0402c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 961129973 1250 961128723 961128739
    0x90c09061707020a050a050f19050a060c030b0406121104050f010e04080d020a030b191a07020406080f0604140106180c0903060614040f020301050604120501090503030403170f0105010206060f 84
    0xc10001c20038140d00d14054409424020100208c060a0411488801400c2c5d1145c900700380c0041c0d8005188070416402200004500c0310084084000c2e100d030301d900070392090404101003192103503081c0d01c031105481507000008042911090006840d0200c1e0300382180840207004010b00b91074003860b1030b0f20921903c00c083c9402050101e113012600a01c4900740000e50b60399030741e813040c1000382d828005100310100c1c6c0108140780081e44070040e5041c4040c200110f00c0400d802c070446d103440d0003400c0609182000d80b000044139a1036181d4501d002c4400f55455024613110110040c01803041e10700b41e44122210108014030584004003420f01d1409941c00c006500714000003143c080c0c402c140150042c04046d10355003e034081004155003405d168411074620402c010402580d41008507012100d202040c82001442801d22078010490404081d19038000041080101984a25424100c0c1d40d01d0111609580303800084060142007409940d000d6444540464003074640780080b48269400286190 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 961131223 1250 961129973 961129993
    0x10c030c020a0f030302060f1012050705040507020616050c0604020409020f030a050309040b06090906010f02031b0715031a060f0d11090f270c040915090c0906170702 73
    0x2a090000d00c0c3c0c0705000c100c045034002d0080590601c4516040110000f09414a06182060f85100c3c02c5a109060402c0c01620300c8004020050042c907004203001401088103151a110182d1500000c8a11091480720050340c0450b42c0c1c02641030f0b0f000b40300303800300030401c0f03a9895090000401d4450301c1a0f130310026103030714000035540400c0385c0a4000e02ca48007450311007400ca001e100079254010385c003510070300e0140600d00d0076881e0600354503441202480c0400030703803d851009030309602c150540050840484141c03419203910000b41d20b021181c80388450441001174080c00c0b01240c0e900380c07030b144915102d1045c9a500b80307410f802034002c0c003030310001403498805002540c40840b0f8903030b0020a01480301080c224042c2c60018020002c0440c140c3700c0700c1e01d0b0441c4824404a0210b920803e64050300303488089001e011541c429074000c0e1010040802603070305c0d04440b240e241d48141c030401074013604004c20408031601c6000150300700e500903111914407849040f03814201030001024101188680c1c4042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 961132473 1250 961131223 961131229
    0x31a03030a0c0204051e0a18021f081b090d031202120103140a0807061e0c0c0606061b030509040209091036050603010b09072c010e010c030c02 63
    0x740541000d989a40d15031044a2041c08103980c40281841901d01c0241c081c007045c0c00d035503400c1c1980040ca20000090b840e4070f01050303203d108206e00e0042c1d0002c41c128620200303045040d00188903000e594803002c2a40d940d1f02c0c4c1245520420702c0d0108095007081c00140564101035804403041486800c1c64010050080340000480e003001094105207000034004209000e4102045845c400090000e82200041912101003a00c216400280070355a5400140c8042060340c4e06075000c0100d82105201000305483c00070310f8807020302c0b0251481c0349401d10004400340140390180d01c0000180410040c840c060300c060b40e480c0c01c65080c0940098007004107188547c0da41520070320451000c40c0307141e41c2d83c0c00e00520021196000003440c100341d04000f1141d42280000c11844403801d04da4001013050358640d03000c64050f040c51815290010400400e00449541246038410200e220700148228500c2c801a22000600280c2c000342c049105480c00b2042d652141e0840c200305400303400c18a0201484d9404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 961133723 1250 961132473 961132477
    0x3140a1d0a090e100e0109051f0905031201061d011d030114090303011e080c21060406020306012d0f0215040f02011205151e040e0a03030c0c030906031a0303 69
    0x10a0815400221304002000b00d184119800f40300c80d00020403000700f80d0380c0c80b141c0d1402d10359018014050b08000c14044800e0682100c0c0314190710506403610740f5106c0c2a14040d410080c000c810201d1a00c000c6903800860010b01e20709000e40503550b1454114541d010f640d012108800c00a4155481b114406100d5010300c640c1405003500c038004613500d6160400040d49030004080c241600c0045100c200908040024a190300800468458401301440c203180e4003035441880200c210344c040e01c0104020301001e503001e107200c1c60003030b2030b04554558040a80000c4003100302c900300386031668400c0d0100300da00c501e4221036600e5580c0112940019420408a0050811181110070745101002070045581c44104039203070100810040c042401c00100080c80518000340c591f0041e02c0001c3d03034803101c9885001070103151170060b008221b820a6007071b110303031159007800054004c2420f2140300c10b21180701e100f0807001d451701540e41d0980141050b2007100600300d0b40c0c203890001c080410b02c4171107641d01440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 961134973 1250 961133723 961133741
    0xc05070c0f0302102610030f030906030b0f010c080705010e07030c05011707080a0f02160812090a03140c07051507120318080f070f0b0403140a1d0a09 66
    0x144440c0c281c0d1961042100ea441600e180c1020041840304040310030300d44c42c94a4501945100c0700c07003003503540e0300060b8000700f915074009462101100f0341e0506254200c3c2c40d11064444a030380500024401809002d0350410744c090450004190410405c0410082c001510000740325038004102c214540c031980b4985441d980050300c1d0b03910b07401c2003006107603001070f1482440c00c2005140c03180352800400c06400351100070466003201e519075035181000003a9504071200e01510215409607180b10f41800382d0f203500807800103404260070754082520501c0019142840640c143d44084007085180c181000715000b00c1c000c1542489030704004181d0741d131a01c85083c949002c981c0402e4440c0c0060805034900d05448804034181480c00158102c42c4a40d06516a80a500010010790b120302000f842e1007540715000018040e052428190810019112405030255000c2da4644090180c4048180980d1068144c0c1d0804241a0841702e519107403400c1c521079040303400a05003403496544064900948080c90 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 961136223 1250 961134973 961134989
    0x4050c090a0b0f0c1501210b0712290406080a0f022b0f0b0a0e070614040b030c13080c060d05070c0506040b060102011515081009020a05040303032d0c05070c 69
    0x60018011810480c0c0f50b0400010391aa04c7c2c034203a00c032900d071071104c150301901440800c90601e4540c1d41200704e58001000a20031940c10411551200303000050911001d01c00c244101d0410f03a0006200303c0c0082e00e9607110342c0021209000790415820058568001c0d0b0301d40414440071003001c041d031f424540c1034140482c0078550100100200d0702c2c01c20400500100407009040c1351403104c80c1030010000d01c14040e0740c00c0b400c1020b031410398003c0160140c0aa0b900580c2603080000421440c0702c010400713000d06044074826102607603190629180c50b14114000d182d0400300030300030009060703201c1d04031503007060b42414000040c50710368130740b5420050100d03020303284e43c8410350170b00c01107590900c06c0c03034801d43c0c10a65801060f400c0483c2d070141c08a641c202d000402c07401c200490001c1d614404120000c00e01e484045543d803560100c003a101c1e410600c03050700804d1810191000402a10a812700d5004c0980d40c01100f010b000c1e443c05004207a06000801008030502c404c20000b41011031001c0508001d07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 961137473 1250 961136223 961136263
    0x5061801120213051003020103021305150c06010f0e0c0a030f050f0f0105010c110d1a09060915061c05120c0f01051806070804150507030b04050c090a0b0f0c 69
    0x390061003c0f4240002a03032049900d08020000215403a10001040d00d03030919026035181541000a5126070445e084650321001c90203107100054080402058a01000001d5410030313a40e071b58810728050110b210b5030b1541741106002480030301c11200145681d44a908001a5105e01042c2801c21200c00322130039252090443c040c84541d24560040702c0c01820b0910b8030040d60b598503580c11116002c540c50050090030590926820459440c03540b18400d41400c880801d80d18007000c50607601c0c1401c0e0741ea40106d001d4000c0d103409441440a10354032030140601004440b44079400d200e01041140c61040c0e80ca402941403110440301030a0060020400c181c000702503a1500141782c508480000d403500e0318480401307100700005400403d0341503101410303092580c259030315401c186580440c010b0076400c01901d0181004500c9030103500c641c00c030840c1a1020441a50f0782c2140c121341d40706590003558025111802001007490020013002c0982d40100f610b42000e007200307003540c1b4001d540c42d4102105003c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 961138723 1250 961137473 961137509
    0x4060b1b010b0418030c1e03180503060c2a010f0b03120a0e060c01060e04200306070228050f0c01021006030b010504020f190306050f09040503090405061801 69
    0x401d002d004022403088404128446a800d0101c284c240382120003401e008076130003464140f015080c12522030304c02c2070b0000d4a500c0b645240c003c0070a13101054610b10002d40c44408207081c00d0000f4420303c2900c5035413540d403600c1c090068242000780640700c5840c2040580010034072094081c0a0013030740740c050510202e0040602010141480b0a101002c0f651810600c1040030039503101240700e480b14010359020f5aa8580d0b0801c99014000d180c0100d0b695400340404d000c101f0010300c4401810043c0f40031820901d0500c1000c041c1c81c0c0380b040e9140001070780640780c103041c408015420004410303401912450080c01598500c0e04064011941c030240d0b400043c13020249580600c48820602982c1e4010420035046548100c0444018029207004560208440c4203001d010801c9a210700da00000341060b80c0a640b000070007421441c0680c1d03008400503501c00c0c41a0401c12022070050303034003601440c2070207203d4003480010a00144201c0d170240b055400303040d4580403010000c0c040c043c0e10b20002c001210b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 961139973 1250 961138723 961138777
    0x30706180e0f0606090109030c0b072906011b02090c04140904120e010c06050a0c140705030414150301080102030f0c0415120e030d0914010203090d05030604060b 71
    0x3119840382808402190400072401491000503034040400c850ba940c5501e4036000403a1010103981005205486000c0003062000230741000e00300180c4210110f80400b400b00d405228407150380a11302845540032400b1654940c010084940e076401d08030040d04059000740c00244d4402010b40314001e0502c4002400d105a14030100380543e1103500303030786500f1182407580d80d070750751b00e0f0348410b66104104c180a10314501e03a110b000c3d0fa145064000e14107024500f82001d8020040002100c0c44004c25502c0c81110700d00b503100d40c00d03104031035006030145042924154800b907008041c1c1f501c00d544a40070509644860004038041d5000c1d000c2030b400141c49144c24540740a05500241000541550a00c000c00444100f2410400c1b03100c1c10b0700e00000e5402040304807802038415548c00507803901010604c1400840954000303001d280c01100352403040c0a591520703900302d01c01541c0e81000c40d0802d51403ca011400b90f4011a0004000b50001844a80c2c410444a43d07801482440e042c844103212180c81c3c1003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 961141223 1250 961139973 961140017
    0x90d05032514070b2209110c0c0301050606042c09071403070506030c0d0905030c010c090e010b03010e0c0909010603090b0708070f0f090b130501081e061e030706 71
    0x9401000a211560078640009801e000d04520b0505c100100100070020302a0702a03860010800c246050102140c443c3c3c21801c1d40d041004040c6041c840e28880e845249014001d1a000d0400034001500d440e04184a020b00030101e4260600b40351255203500c0c0c2030107100d0001ca4803407241107006d44030441c00c1248280000e10950302c0d0902c20340c407061044c0425550390080382e8021b0b001e01d40c800d5880c07038490f0b101400303403031019405030083c000821416100c10b4103411840041c00107940f0007410640310b100324405141f0038003851a1103d81800107200d1406410713000c60300018814072240c180b03044040000c485c801c09821081c0000c1d10307101c1d90303000c22443ca210950010400e0170940c425242200e001030018549108020400c241d1541c41181e02c0c3c0600a2480607048030352000c1e0351448801d000103000d0b41c3c148541c0b070001d03a02500044605d140102203101e08061091407103101e0b02c3d00c5040000d0700d640c42050101c03090610b402c541c00e03541c00f046418006d05094646c004400c10070304075100a0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 961142473 1250 961141223 961141253
    0x9061002150f220809040507200313080106080d080405030f0412020a05100f210f0c020c1504060e0111030d060602060c09150d200904060b0a05090d050325 68
    0xf00f030100c0c0a110010380e620741558605d000907580050140e40d6035208a0390490489000001c00e0341d45030900c004d81d100403000f04810302e211184c4000550307a800580342250130900c075500468001000d0304401601c1340b00c0b038641141c02641145d08080701810036072016845035210701d00317004c004503840045060200089006000481d0011015144c1c0034025229002034400c81c4200301c02014540c2c0580e060340400d41242d8040c400810405403180b840900500300d03400110054411814440d1003842d020814a0728000598202d50815190610950786a1582404541131005603034554044503420405071042c07810003030000c585180b8055010341050005030081000d08400c00000d000d603141c42d0401107500781c451541e80d030740381e884c000c040000304000480001c81120900000b001241c101011f00f0040b0702c1200c040250315074901e03008059108001c0314401154061182400d0b502d40260600e42c02c83c090b10a482c50055081402c2021358000403a20380500312800140081c00b035185800c4000f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 961143723 1250 961142473 961142521
    0x40911131407171504180303090203010510180f06050d030e0117010b0a0507051e1507052b0e030309100b06130510022503030f090509061002150f 64
    0x20f0220040c904002d210001060803210307450100c01d410303140e11250b00c50081000103141050041000c1c2c03070010003816503d5020303031082d030800c0081030344050342056100446220490100003282140f11410141200c1512507802690720360740025507450b02ea11488415210750394402d1402c9000002400c84100f1011414503100640700500c2007020800c2191a411958181940c40f4840d901e4000d16100440c8003144181c100041aa29502c01c0040c62546416040c504c0c1821a91507140803500d50082c8079101d82d4441490420301c0ba030315500508081c020702d41540109050b01205032561170750748207070b404003071503809100c008080320f02500c20985140c104440851a01c101216601d29254aa004d01c500c0381c0d210b80303041c0501a008100440000c1d8400c1d851803000c031183d80850906903428401540816002c150703008040388a40007078401d9130b000500c02003031500d501c0280301040c521124004194407414011603050340c809911240315200d40b010a50b5185171601c90050554050503045e09 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 961144973 1250 961143723 961143737
    0x270703020609060c10020408010e0709020a021506120715530f011a0a090605030a1e0b0f0114070803041118040c0f060c02040911131407 60
    0x100680c1c0d09001c03201c01d0201250059142d801d0715965600b41702d014030ba418816880000e00007110314041d08100051980340c825500c07203e5650040409910803420001d006800010711182d0552810048640010019041c60360308450b030001c0301c1c50700d01c40b81c03c10881c05942400e145181036210080c181c41c03805054140404002e003e001c04000700d0642070603a070102c2202603099100301c0d080c88070030719400750309c3d400c85040c20a1401c54000d41020300842c0d41025400d500e0110841001b4211280200195101c41003240f42c40002c0344e2070340001d4201b09080d034903408041c2101407000811040c1440d503050010710070064004028032141c000c48524140180052041c04a01d450400e40350020f4100e09040d0392035485140c001855895800d240d60301c038401c024220100c2410210b621b00c22131046a49110031501c500c0310850525080c0314000000302003108880060030f00c1c0c4c01c075510052180000400b00180c120025420321a4084003841060f560002c1d0140d01001c0840d05400c0402424041c07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 961146223 1250 961144973 961144979
    0x910110102120f100e0f150d08030f070521090f160e011d010b13050a030501050f01140607300807170c190e03070f080f1b12152707 58
    0x17694500e80202030888901c41d01c80041c0b49003107038140840a00c0c5008001c0444500c05151401d0745400555641980740340c40c00000c0c0d0601c0c000d5040f2024003ca02c0d00c0305080e5000700003034481c1408001c264803411f018104250b08428400c1065070f0f0303c0425040c0e505683c80c141454040410f03c140d101e0700115100c40c55141c80440910307090342c15912401c0c01e05540703a18440c0b485d031049201c0e0380101e40013041020f00009100c2d0660159020303c20900c1c481d17000b40d9841182d00f09a912005083c0c0d40100100f202d280080d81c0080b0b411513060001800504025191030003041001010200c100480d8019003000708aa501c43c4042024480445800441d0b05000c2482103890103110340244240b2030720802513144502039070101c0c408082c000c0c1103c01650719504c1c0d48001000d00d1040140510030032103030900a4034081100c40e00300c0410036240410200715020054000908003c40d80140107a481e006820f5100da11010311a141c008201e8802007440d1400c0c9014440d091b0040f00c07217402c00c032000c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 961147473 1250 961146223 961146239
    0x114041424070201081e040308010501020d0e010f05130302040e0319090812091807050405130b09070309140114190c020d030c0201020c0f0a060509120910110102120f10 74
    0x502d20054082c600b0004603a0344040030001038050003070145504100e001000205136104404038140c2e03000303900383d03000c0000d03003a02a113454a5614031103010030202c0c1000032010307126034090075020040d5007410b043e050f80c81e000304040714414100c0c1d07209608001480805600381854610035040c4c0c514000f540180741c05101c80e200d012241100910130f00c0060244402d65070f04410b5140382100c00194446400c1048000c0c0507a481882150b002d520441030014060718240708550812401500352900d0780d80e041011001051200d004841e852045000c5c00c0c1119824410b02d4424126800c0303c0320181007445102040700c001941910303010341001078041040380c1c042895a0000c1e114140461014075020040e4003a0140c0a66100213200720041506c1900d0002622182107000e01b00402c515200c440c102622541606000141c01e0403c204140081c1800151420b40c152249800394510528030b808500b680d200c080807001004000040c0138640f104a41140e40004500446c0c1c40d0440c40c000342 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 961148723 1250 961147473 961147477
    0x3050610050604150e0f0405160e041e090609080c03030103030e0604030807171605100e03040515090d0c0902030414010b010c020603060d080301030c0816030c0302060304020114041424 81
    0x1340380100048400c00394070a45519000b00e2000c00c004100740107600d0f241c410701c03d405a200307500c0c90000310100d10140160819104805248080e118049070452050a18401411412104481e01d81d5101392107000324507000007515505001c0c82c0903541d2545941001040d09180c4d4405601c0742e40204010000108000d0480e5000c550003082c14290300107801d4421424010a0016915100050b841004000780442c000524840700c05e400c01c0429811036210750b60b0b004601469421003d0800340c80d10f1465000040d040d031000c0204400301c3e2761915540c1800b490f0301980040081d6402000303010400404229a02d000301d0342100800c0510340000c0002e1020300200400380c020303a800000304019444021b1825000d44e0000b054a9a95a40740750402c107010b135510a28260380618504400c1c2e482c02110300004580e00705140d490740380e0468080048591015000300c0c1480000e0500118203030100c4042c000404950001a005440034010f002680c001c012000120f84541c1c10980603800041003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 961149973 1250 961148723 961148759
    0x1020f041e0b03041e0203010c0f080a0501080c0d08191d030f07050409020f03071707080607080c03220501061401020a020a0905100e0f041103060714030604021303050610050604 78
    0x456a017006050340c10307480000004180c082e416500302807010309600d4000700401001d0402d41d0f1495030541d00c850504c2c044a1003805905115007102150300d0709840c003041c1030113000c0d025182c4645003003a00c0c440758400c810f0045807003000c203010003044100c0e40e00300c00f44101d1008007a4060310350344415010f15521560140505480f4566400300c1e1030070b64449085180c0300306000b40c215540d06451345034075549545005000e0986214441000ca038440c0d002c1007490040ba130a407107040c13150325810310f84019500010b040c0c0201100000c3c10840600354040f0840305180280b000043d02820103038003503240400f180125055501880c02480140c6501c20b01c402181ca50f40d200141c0c541b100c04080681d10003e502030340c09040750600784900d400d20111034038007451041c480d02050204a0040c19200c407400c6a003040803929006800c46000d200c60015903010100800041c541003d8450071010b10b40303160819a09a8003100c00c2000c02da10400d0f842c405440b04844107410980703419080403248607603031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 961151079 1106 961149973 961149983
    0x30602040e0c1206010f17070e0102070b13121707031106010906050105090d020406080703050307050d02070b0f0a0306120516091a090405070801020f041e0b0304 71
    0x20854802044800501c5060303138a400066401c6070000c0803076414400300010314129201040300662050280b616001d0303411550900091504080383c10032101601e0030482c0b000e04425101c1480c0841d038108c10a00c000800038940360082042c644821460f441c008a00c040c100354200910322152180c0ca011228240e07610907901040d20094030031140030680802560711241071105803109928006040490825581d40c0103070304d004020392058500741c2020541c201004800c2c800b0102482c5c0c1c1d0b00c01041024200036a002d01c900c64074064903050301000500d52526406038004000901d4071440c903070f100c00e42c1030500765150144c405200030410040403000c20b20a02d18800c0300b800d03a002c060840894941c0c8005d101400b04054015a20b80c410700c41e00240594090000b03000707512402124946481c500303440400d44130805003580e40042000711050080942610941394030a400c6 = true := by decide +kernel

theorem cover : BRFrame.Cov 960971223 961151079 := by
  have h0 := BRFrame.cov_init 960971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 960971223 ≤ n) (h2 : n < 961151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
