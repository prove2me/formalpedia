-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0195
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:23:18.07599+00:00
-- url     : https://prove2.me/submissions/2b251cfa-cdfb-4ef3-9866-8f394b8e4056

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 34892091 ≤ n < 35071947 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 34893341 1250 34892091 34892101
    0x190605010e04020310030b0403080405060609010308030c070606081b040e070b0909071103030a090b06010c080f0a110102040f08120403020a06120b030d0e1908060f07020f010f090b010905 82
    0x403000e41c00c50416401941d01000007020b01c076280c200c0800454011107041003d0406003002022040100e4054449100d0380700494114100020304904894001c4005411621583c0207151254003001056030308503114030b00404c180c1c2040c00760010780c00b45d00c0c01d400b0311111711100340810b546020f004181c850308550300130001d00c0ca05170100c070600d10b01100c030909540d85104041c0c90501041056a0403880040100410054070742d21040620307000d82a541455a2484011110090b42c440010300b0003005004010210b80e00c10050541400300b42410014502848419422a04943d011010f00c0780b8003501049945018080211944845002c840c41c103400c580106040001038800c60f02004480301c41440c00c120307180e12030300f00c0360002400c1c0c0300b200d04a100c005140d00d03840840244200080c0702402c5034500041c41d8441120b02c2c0c1005841a40e4440301c81e0804450700038203260070750241c003c0e24590b0480a109154055040c238200203280b074014101100240016000304044602d840c0c2804 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 34894591 1250 34893341 34893347
    0xc09210c0d020a120303021e09010c02130b03030304080301031a1506090d02190e060d030804020f01020a050706030c080703061428030503041a0702090106050a0201020712020619060501 81
    0x4608000e0a980740e5070145510310208000030305681c4000c403420000a86a030815a041e00240150301098108440c1c5a904405100062242401050120b800c1681c0c080060034240390050400d41e4101e000540c8880400110303040d03030f1089900b1141818000010720801413402000e2800320b0034000c1074002e52034800480541d1a8600348010305c26500800d8020032540c0780340320b00c220640d018148006000780640c43d0300703480c00a4003a1000c648056000641e8a042100300da02c05c140d01a07681544944a94003031040002075910344a0450081c0d80d034200208a007002a20018251968002148403032104000c00100026107494101410120100b00312981401c58003900582140d82441c0da0040c40028040041c285204e202c10180803c0c0002c24007a0101c013070801c40703400719000940090700704030b040c0d000d00c00c403203000758040002401484454440c8024120b000c0c89400010300c0c21216803103010002e040c103041da5005900403c01c202c080e9030101c001c11000040480284050741c204000a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 34895841 1250 34894591 34894603
    0x50d0f081f05040204030602120601020c0a0909060608010c0801060201180201200a060f0605010801090b0a120302030c060411011e0210020d0b060a0801031406060f0f0310050c0921 79
    0x10998035000710101c903022150303a0000300001d2800900440d9900e0307503850004060b41200714440014001200012425400400c941c020070310000c003000701d0141018a40d0004014404003500c2d4140d40381e07800316030b9420901c56480203440540326480150325010000b070955417088070a6400c08903104110340140d0f001407440595204070307040c190720b00541504062900500c0900906000c0c00c00380082c18110441e4090001c0c3c4600f030343ca407d070903a01c400c40c0c54207441c03102e41c0030b503000f1241040421200030401840c00c002c03880b81c4103992030a050301607500c0c504541941c058400f000d04191185545d0b03000018061051990502980d0302941c1500194a500c0128000300d86030390001009415031405621285640000610f01a2100c10f00b02c00200909000d000490310f501c100c500c001c2100d140011010b00c00c2c800204844070b030b04001024440210401820030f90548180d42d460f854600060042500c207c107070075034154480b211070080120403c02d0109141089074521141c1c3c4401c04003043c0c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 34897091 1250 34895841 34895851
    0x90617030703050910030e10051e0907060305091f1406091014012001020409060b0408070501050d09050303090609011104080c100c080a02030405030c011103030f0a0609020a020307050d0f08 83
    0x142105c01081c4d00800d40240420035441c224a015a201651080c420740e48024020401043c11201d02d840602c0d003401016030a0364003501a0340203003410013215103e43c00c0310b0350101099080d600e0074200e10100804201c9068402103401e134031440051000044170740f00c40c0d4030441c200c642d4030702424080101e16442d400d074083e142c00b0242c103000d210101d9004151440301f68000b840c0010000d00720485540c000d40084c021a00500d00700b060018003005030205503003d4606082c0074016107480e05005548545c414504a00095141e0942002164082c40610701c81e8088038050101407503c00040740c00c45848030f10481c1000c000b880b0521400300300086003401030000340d649080790710072000e0658080741c0c50038000b40b04040029034503c050364084041c100f180d0041d4111808903000da4019140050290f045002d90b41c030a100041d136180c0d94200c0c458100c0d500e140d0000382c541c1c5130913140007684c2c050b808000141c0d000290f40010030804101c0010511500c4c50310042c03500c600a0014003000003d04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 34898341 1250 34897091 34897099
    0x5010b010e0906012f0a061a06030108070e06030718020901030b06041d04150203091605030304030b0c03100b0408010903120203010e01060f2703050d0906080c0d0b09010906170307030509 82
    0x3a000d83c682c1c0c0d17002012a1113401c0310300b10b468007a1a494a1406094945c0d407001c00e5800425040c030942c10101c00f079034180c81e440c0c13018002003400c108030150114402085294148100c1c0d00024015081c00d210240414484a0169864100c00c001500740d51643c81c007140a604200801c01c040441b1402d0f01c901e40c1c520010600c440c0d221410440b002c0481403400403d0180700006000001800041d40010349000485000d07165a48604158490180380f0005d402d030b50394400010070725540385004640c8460411368040e1269100d45d0040441d03002500400100e039503404554080c59000340d8076050105003101c0a5140d0340c108040c19066041c103105c1d0f201444403200400c00b0440c09580584408040781046241c4074980001c1740303d9241040c4425240c500030401840704441c440d40c0e0702021f80341c264071445c0d1241c450401c000325070b52110020301e502d181c6d41c4c52540c0c91a610200c10f10300810546001003119418454840e980c0b624141c003502142d4020030507500000e40000071303140100001c403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 34899591 1250 34898341 34898387
    0xc06120b011805100302092812050a0303050613050c0301050114070206090d030522090b010309030804110a08010213030c0b0301030f02130204030203030705100507020706090b030403180305010b010e090601 90
    0xc250044c3c011a0344031f0358040081d1182c20140c0307108078240d9070310240c0540141c50040d0b5a410041c0c0490785400c0c060015080383d01e822011178046c0d0040da4110300f01034560f0310340301e15126148003114000e5813100c801c0440000104015039101030000303203080601169524000d8940e0000b4a280b29500c00b0302c0c02485039009103418140100182d80344041a0700c0310708c5038401d8444081a0b003404034000c03a001c0d50701e0401707100c685503c68421110081d0341512000c40c251225150007404d0b120ba120001e900047c0d520300030618a000380040e001301e20143c2c80e42c102017819864030204000e140d42100c2c00340c100034401040456086008410000e0b01520b82a50080c2c0c090ba0100c040d200720780010b90988000945c80040143c00969a0060b070b8917103004011b80d03100c8000807615850280328020020f051504103100c3c0d2540740004540081c4241005140c01c0102d09881d4030600c043d5005842b5655601500c4505503000b000c00040000300702d03100e80781840c0c0140043c250708581c40c04544c80c40c005d8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 34900841 1250 34899591 34899619
    0x609070e18061c030c02090a0603050a020f15040602010510060f0207060e030a02060715150506091e0301110a0f0509100c020307081f060e04051c09030c06120b011805 73
    0x140c081414000c50080215001e4503d0381800307000104000c0049000703959403c00134200218078841c15054940c44006000100615001c028009080308012513001c031040f032800d40d1801184000740000c18103a00081800e2030400d120310001101c0364001d0003400169030070501015400304110081d5015814a0021a01c0c1038002c40e107407801c410002500701c14002201020b0048907440701036418403c42092000900c1c4c13000310381d03020b0458443c40e03400c0082440700030241c0c54021424481c0c8141807000440c0704411a00103400e40c2d400c00900000c01800003108034075540d21031900c14030507403d0b06140d49813010400205841550004c015410080c0c20340c49a01156800d0043e840281075410440303020003e03003142a04a041503100840401c0d04e082d0001454040381c8480500c9180c0004c0505124138640441807504114a40d0400801072412000b01c001605c03100000040e2000395101280e00791050500000c584140344403906210500400720001800040e80b5400c2d1181515103002c84210 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 34902091 1250 34900841 34900849
    0x915120807050604030e041a0f1e06070f150c2313080d020115030b0406090807060609020703090e06090c0a021f09020a05010503012301090302040906050609070e1806 73
    0x30740032004265006035800d10091590080c206032448904403410485084401e0101d100c20320b03840e4015070042d2040200e4001e41c500060754841003101c00c5a0b014026084000003082a442031404a035400f1081d0600d40074400391080c0c2c450900d407d104200b21810320307004007505003881080c0ca203001c1d214584081c41c16042510607640000341040f2004038a40d00d611180f5100e841840c029401503290805213101c01e815400003604407600080b00c8030b40354031180c03690409880c1690040d50324850400c40040065100d00c01d4100510b224180140c41c0d400c580b500802032840c035440140c03d404a1014829140c3d5032010154010003507014240c0c2d1a05407260a038208804520b010780c000d2421410582e800341c941d08801c04003032003101c40011841d11580155480c1c0402c1c06060503440d10920208444d100c0841031188403541410420301d0241e0b01d03400036003503810f60b100880c0d2007a00c0301700748603803404c161607100c1c1c114070300d03041c00290b000006003c00d4108210840c03990402074100d020a5081e11 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 34903341 1250 34902091 34902097
    0x507020301150812070c0510030605030616031a03030a0c0201031805060f0901020f0f070201020106050603130c05030706021009140a0b0f0105030102030103020609010503040c0f0f03030909151208 86
    0x58090001c1c08024101007100d80d160040d0b105200e4603000f42c115110305901100110780b0020340c440e14000c8006e0400c41408505403464680405040e40c4030400300f4942d4040000074451007605501d40c01c20321425030000c0c181c40382d450703184407180c0d40c80855040341d0303074044140c60715241c4914204801c0d01c0103000403000b402800786600d20721480003182c030302403050208115105160071442d005a984030b10078282d00702d1040c0707050044400d006118603003850b242e060080c01b8090052002185203621900002c0c0c1d203034010348801221282815601c010000e0390807401c030082008502070400189000000b9403038280d50300150b490242d954115404000300455a807442c11810001c43e45c08401c2c0303141806500704240c1d0360381140f41d814400020f00b8501402203178181c9901030892405c010b04140192003036003001c0c10880d90480042408600c0000302d10460008201420b400f03000c5514504015040030465005840b8041c14020a406400300403100d01d4119a800850f6101c1c0034074a08206580740 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 34904591 1250 34903341 34903343
    0x150109150510030e0c0f030a030507060603081b0d0306060504260a05030703170103030905121903020c0a0501051303020d210816020a0215030a0b041d011104030b0a09030507 76
    0xb04060302e207200032503059011014040e189021125254003500c20020015104903045074150702a0350f9140000e48584040d142c00d80c800c40c40454010385a039a4203045030000c600c1102900b0150365026000081080345c40c0c40800503050400c185810708600038a0361140c0e0040259440390b25405d02000580d40402d10861005802a504c050801d441c020783c40e5849203e00b5000a000a01e44170740104090040c2c5040b80d03890b454400c21207280c4001e2102d0b0301e10084000200707010f8001000011a1780320468149540300364003800300c12261000704016417a564000904102040c480907030380c603001c4103110003603e40480c0c1c2154408050715044484410003034203200301c21440780d40d00e030006d6000b031181400742c042070031405080d0508003000c0381c0e10303040120082c0d842201c8400b2400c0c01c3e40c0c1c7c100210b4000450a0000c00c4e00c0544102240c19544078031424107200504030f1004807940b01c00c3c400c1c0c45d074007800040c01600d41890b5480e80700300c0340009402c01d0300d842da5032800d060030503009200f19a041 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 34905841 1250 34904591 34904599
    0x1a0108070e041b08060a2103030219090e07020f060a0b030319091d150f010306051c0c0501050c070314010b04050f0402030c1c060506210706030c021501091505 70
    0x88000d0a40307220600c1c0c0000c3c40c0001042403180450003601c1c0603080c070360549000e07440c00d91402081c081c1a42c42121581e0003035013415400c202c48a4400b54034400300c4c51504183c2c4410301001e15061240002e568000c3c611811074000d002d4030041d1960204040740c10990601c1c01280b4501d5060000381144910700d400250720249002d6114030382e80020204085403c030000055840b80d02980011007846c2c02ca41214450000900c400710790301c0c046c15580b94081e0103140c000380003500d51002c01c1d40200505100010607481c003100100b041698100764014160030319165041400c07004c02d055588105001c02046002c011000f069500c1c1c0035400307000c002c1c1e00140240114142421802c01c1401e054a00380e001c1e0042800d61041030800350301d0a00404c0302e5441c80e207030349911900d03900d00400020309103a9112441000c5031240f240304502c50803094543c50b015001c568600340003d011900355402f81c4003590818403094000b10854000c2c541100c00c401c00114a044061802c0080103d45401c69640 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 34907091 1250 34905841 34905851
    0x80c060705120a020a0302010b010503060105071b0902030106031508010905060705030702010e07030807030e180c0c07031a07090e0c030c0c0a05010e1c030207020604060311160f02090a1a0108070e04 87
    0x104d031300044484299003c0d400030041758101c00011541417104032a00e0307001c0703001089001d000031198844103004000c2c0702000b141031500e0354142003d0342d00030390107000060380311501e615560030050b010344000c2c030300003008002098855440589404004010b0414040084009142c05000703400a41c0301e038403a0800c0c0c502854a83c5450079035a04101010307800141440001c40351400c06000c0d0300c4a001c07001002404139941e0030705440b142d40c04282e00000038010640000700080c1e03486481031084196003101c041a10f0810401800c015060303201107072500b588014010b074140c014003107a80201c001e0300416503602400100524008400c01c1c01001ca61822880e06401000070880103d01d550007103403541c1b03442c0b059404909038040c2003070107036000e1001c1004100c020300030750125102a0214000c07509169041504581c0d000d00c0000507520703200e440030720303804510300500c04581c81901c29804006101c510105018040c00c1c48032400d045c0044c45d80802c05040c01a0320002006400070000c0c01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 34908341 1250 34907091 34907107
    0x13020d0f120906030f050f0105040e0a1a0f0c030c030c090a0b03070c0302071413050601020106031401020c0d08040b06010f02030c01090303020c07050a0308030c031009090308060910080c06070512 86
    0x10768950b0f00c0b8640009181c050354642121040c003a8a0141440b1003030188180d080004210003411441c40c1c3e0b21803442402e54080006008505400b1840b220340c40344071f503500c0c19a046e1940441e0003411103291075810410006c91445150541303401842c9100125126014180804c410034081e4010501e5980040204194607900810700b03403180f80701e5425107070919981d418152520101c0710380c0641c00420b14140360442e80c0154400341d40b0580503c004164141c0c0c98239440d00740c0702c41288803403143c0d400181e07000c030704101004596100107146c0b078203030500c0c5400d44680c008800041d1007030307040003210807941400e28030801c00d40f03085500d120001c00100805d4034000e00254420f42004129028999000139a4130300780c9103441c100c0344c014982c64550360f142088090554002080340d15850b0103400c3c0469804080d1146c1c0004c0c5200350ec6032641c1d41011001c000070308100420b00001e628038200f05001d8000040b0f607100d00900c1c02d03202d26445503c10b140003030078020b108802000942010030554 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 34909591 1250 34908341 34908347
    0x10b1507060e06011401080a140c0703020c0307050108131a0a0c020c030d17070302070501090602030a05062220030403030902180708010b03040203010905010507030f06080613020d0f12 81
    0x100340c641c030401c010801241d07840d2881d40c03103007030910a00c090b11080344a40c5803554014013202e980000388080000e140804a4500341c0c480e2010754500311103200120b0308004141d01000000324884003200284480d81c80c0c440000c02d0004010000c211100101c48806c0420412010700049206440c80c10240c03841c04050080050a8084070040184030311041c3c0800ca0a0100f8030001507007559480c150f4001b01551001e110102c041c02d003408041e420000e00010600a105e6051502d04c103007000750b62405c00301f0081043c1c0f00d002c3d00484c41054074031030300910601e40d0700854a980320407440200e19103100b44019010f00b58201d80c5480321820000c10081015070547c48072100520880e58600c41c0284112b016600010072103401000c2f4a070240140150041a8041c40d1701c00d2000300040b0392a90956a500d0940d0015901800840e880307814501020000e07000f107201409081008000c3c515200a00d12184811140c3c0a0700a891005621050020100380e10824075040f6400c408032640000c001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 34910841 1250 34909591 34909597
    0x30209130b100806060304020d0c0e16030506031f0506010905040e01020c0d020312070c0f0203030705060105011b080306090a020f03010b07060b01030e0c0f010302190302030103060e0f0d0809010b15 87
    0x3911654100ca040d401441c0903e2105000f403c020304030606560352a0309002205003011001c0e651a40d80420005510722030101140c8524201c000c4890f007806440300180540d00094503082c0300350410301e0a541410648451042c00d840f100402190740e45a000060b940d040b01604501d801c0381c02c0806504448070150010004101981e04492000d1081c81c01280c40307000d0030420a0345086590003280c085803144218240440c0a1084000c071090160b001034910f900400c17040b00c6541098004105540c0c02c100c05146240c20811880114095942c03540c0b1203110042c05148202d16220200740444615410b551910300b09103c20b42d6213584411003181c00340c06c00007044625078100201c5e19040e5220703016000d164144c0c2001004000407010410011b650691182c1d0304055003446901c40e10100d40d403040348090542e840060382e03541181018030503a007000c09610050b5201c9103070320080c41400a03651681c00d0f01da2400710080d40750400040e0240c00c92240741d0742d00aa402c2c3c03480720a03013808801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 34912091 1250 34910841 34910861
    0xf03110c0c0315060a03080a052106010206070906050403060519140a0b041b21060609050118030503030f1009020706060608100302060d09020f030d02060f0f1504090303020913 77
    0x4641003d00d8030036030041d00782412541d40d6080510840c081000441d0740002d468100c9072410b040d402e010040c1c0c40c0721032002c1900120302c04c07070000c802031208a58050046030340007421071800d83c150300e0801c440640360788594440145030075030b103600083d80c076480340020650302a040c1d6000d02650422401c0710b1420401a1090b192480c6800740014940c641446040842d6070010070840868a000d407040e100c0c2d8800703c103540800510840160100041032080c00058030a948030520803d0030a00010b040849080c10080c1845030000180040b03140001540d500c03494030750310700300c846e6199080e0501c1c0c43d0702035000054082c0042039160030000c85401c40415505241d9900c0e1151303079139003441c5d07401402a200203500301000b001050480301c515041400c1a6002500d14420144100041307854480140043c50050700000148000461300e5103142c2d420003502c42e0041081c4c02d14582400c0a04118031110b4400c0395103454100401d8000d8060347c60404004010f03007a081c12541e402c0d070190000c508 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 34913341 1250 34912091 34912093
    0x6120a0b0a140d02190801140a0e0d03050408070f0c08010c050705070302091f06090509090c2206120b040215070506060904020a080313030c12030504090e070503060a02090102070e13030f03110c0c03 87
    0x10009603805c80d9881014581101cae80002c0000440a90702540181405007054400c040c041101e8000b180b8003041c01d0100612403140176010034500001c660840314243c61050400108100310400f0810025120060341d40444604010762652081c513240c6104100855404032940100028050b800c50324920448070290740000c01551880d291945a103543c09560f544101c0c0c1e660220030300650091041d0b0085110301c4000b5102c2d0325003c1018042ca40048219502d0403410100000c5082200e034600280c5101d819460409403150b581f56140c4000812301c9006041e154001404d5542d0411024000c085002c1a240d903594041310248401c0c46900003940d09820140307000480d80c0000410007022a0150766031401c0504201c01207010b0411641c01007401c0c40f4558001c0b5140d981809113500407001103500517910350713024001a00b0069a6849000a03501d0002006440120700f50f400051560602e002071301c0b200070504c241c00405c9664041080032002007040040c0d00c40000341000005001c44c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 34914591 1250 34913341 34913381
    0x1c0f020306010b0a0815010e041d0d09030206030c0309010b0a03050a03020d0908070b0904090501050c0d11071e050f06011d0109020307020c0114040506120a0b0a140d02190801 77
    0x4030307101d814440d80c403000002411103030000d0700706c0f00c140c08885000507051402c6a106029200060159911518207070707000c00b05c04040102c401001c20003e0b400450074140780601515580003d002400011700e0000c42480000000700b10003070a41c80408080c0307001302403991003601d030b007041583d0340800f03001200503104e0090b580c06620700035404a8203c43d40034006003829410b00c602c20405811110040741c100f6111920310001031001c1c069117101d941d4085020b0b03201c090513180e00040d074404140c50100c1e19030401c096408106c0e00000c00c034500280200d04841c50113a80360441c504482649505060700900f0004118040d00408c01842c84c959980215450398035a00b001089100603108000964861101c3d40100e50042d03070003130f0403030444c070039282c0c10645d4620102c0c0e80c55001c14070901901024208218800950303205115003480700355146800030b4105080c0350540729450380024402e031040b03003400c811903880b26802d4014200040d10440c206980d854002d002c1c1155030441803c000c00d035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 34915841 1250 34914591 34914599
    0x61d06120606030c040b0d060c050c06010b04050901061b02030a060e0f2b050c01051003140c010804030e040204230f030a030c02010305072a0203070f050d0803061c0f02030601 77
    0xaa07480c01988014050103805003450100402031180b1031600b40c001e102c81c1c04480c0400d44900c03900310210b843d5120310b65150b40e100003582c00c1100503080f600c8030034024003050005171500510300d415203d0f103007441143c03003200a089600144210600950500c42c2401c194104402504a094030302c1c101c0c3c00b161341104154054a440d6280c47e06c4540c400301e00900105010004030b8080c1910a0340d50404624145820398640d094803811107105034170111148007041000070105800c0e000540c0d01c0c2c003402c900c88180740028089900600301404006480d69520403d42d5280e045030300405940301e0305101d0483c1c810301c02c00007400400b0414855240000b0703800e0142004582c1600c2d85a140c0d0390f55031019502e07401034004140140c40081000701c5440c102400c0640c28180041c0f040000e4044c50b030000c0070344105880d241d280d421610340d0b1300c01c1040820694452040140846510100168590307035050b01007041c03031409129451080130340412400901480c0044084241d00035420b40e1070503a22 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 34917091 1250 34915841 34915843
    0x12060109121a2a1e040e041b030809040507031806060905090f0d03020a0302070c120501110f071509050a030809010b010e090a0c02150c0d0b090103030509010f0201061d0612 76
    0x940407200f1000101040710055161616000300700d1100c440e040d800d0a1030b40d001134140c154009400403219400088203102c00d2251017850b00b81c0d50100f1801c04404c3c90b00b0744e03640c5952402401c60f2280241d40350004074081901036044500d2880010b403241902201c82c0c20103102800c050f21400c00c415180401050300b0007030126800240c10b034180020f000030180304000314020761048141104161b030034000e60b400a4000400761004000400103c2200c903203d080407400c44039040180c2d00da05100304208807020482d5000c6d580c8568019503802135a00700200300401800580000030410b001d0401c4110403d0342203002140903110281c000c200030143c180040da00151840c22256100041000040900d24503400100440040c0d01c142d50b1190f40c1d1440303c1c1d49054059071040422032000c511000510201e201e0580380c80e1044138a04083d5141d524058840d00c500b02600d81042103140c1003028041c000d4001c00001e20030b00e02003c40042c840018400100415a181407080c9039012491100c500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 34918341 1250 34917091 34917121
    0x1110f06160801151b03030207060501030602041404050601020601060e040e01020c160f0305030304020f0d0c0608160201090f02240c032511090a0b040212010602060702070b12060109121a 82
    0x84284c80e042640c000343c00703400c5d0320030095031011820180c0810200c80000d50601440c0d0086109580c003607110790902d803c0d2403000310000072440c0150720781810410203a0303000503a94112a42401c280580307000500c0801c0141500061021702c540c00012842c02040000500102403000021010703c5551110004505040c0b1448060801e41c001d00c003040c05441e11044005d201e5000821a16540b066592004010011382d0305c50404110a01d04002007001900c0142240d02c0c0301d071008100401e81941c0c0c5000f4610a40e80c06030043d441c940070612201c00d03901024500803150700e0401c2c0c95100b554141d60f52680021240a840b008121a0208240004c6621401144e000d120340a9014442c42441b420301d00c010b03c0702c045152225a52681605c444c0300400308240710300d10398000c40d0304142020340745c031a000e8800300855210030001c100078000007013a00c035040d203030a20910749034030717950b00407200940c864220134900951401100c041202c902d0f05a40f40e108101821455940d0b5100902c50800c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 34919591 1250 34918341 34918379
    0x60807050307120507111005010e060a08100504020303070506010b0c1002031312030605040c0509040b09090a031d120a03080a0b030a030302070203030d05091b0f0f01110f06160801 79
    0xf44104030b00c9001070311580099038850ba5500c0c000c07415882c0020f2003482d02c444030720444c1c0100d5480c0e0040c410555410f00c003e510a0058aa0b49507680ca07003c2c100b0f03601d090051400e0b080303c2c1d440010030115941030044484d8a46c01008440030783d6112100d00100d0380c4010011441c51007281c6845c0041111130003901c0c40307812844250050310f219616403005110fa44110b1008050f07942001040c1542e50b071048464020b6165251500e504e103110038842100d40c17a41038a8410340140382049980940081e030402d4541d490b1420722002131007050000d03019180500d2150744840c3c410358480591800040c40c1e080540031b540c1c1e000282d190380310b0007002c80e2850480190135030044441440402d000703800401180b44080c0490b8a4080a5031049044960548101149410900004600300410f107010a0030fa80704a0b103038402d80c0740365400103140d004480a41818070103020100d8440441c00c0c07000c40c29041d028400d580462505003600441d5181c14881000410001000403c996540f4155400c1c20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 34920841 1250 34919591 34919597
    0x504030c080a020f010203090c0411070c030f05011407030c0201180b011205070e0405010c1101050c0409091e060b04060b04121403040f0e06040501050405040b06090702030c010204030c060807050307 87
    0x442039211400542e02c0024188154030400300c03080b101a00910095200d40700110260072104102010070003a60f56110225526030400e0114802080003c0d002e20100c0f5801098002c0400203464514003501041844500700f111302d80800c5101a017640264a030f207001307035000704100180700c0d114041104903c0005042e20761400010b000c0160400c5401d280070b4002c40480b80c4107a0345418403000d005040b6002c5405035180c00d0700c00b00c101c1d0000381c0300d6400840d0030300034002880c0a481040a81c0030328414800c8040d11000e28409024000158200c041e9100b12105000340050034540c016000c2081d0282c0180d151030000505451030354181c40c141c50072020400449039094403210940051003a140000d4001080005001c4004580395801401400350b803040c545806010031084a07030581c000b074000c50038901040300080e80b030740d0003541c0060100d41e08007a40c4c1b00c031a02280b541c020320000325219840003d010041c00090011402114a00d503a00f08095482180807a41804195160004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 34922091 1250 34920841 34920857
    0x901020c0601031103010906060f060908120a0c150510030b07030b03060a02030403030e0601080601081204050f091005041107020916020a0618020a06050901020111041d0c070b07091503050403 84
    0x204c1c00d82c6501d5000384002e0000c038020420b921070500300d8070035034004e1080c0324807990200109504002c80400400611010302a80c0140301910302c49441303825030110820a4070543c400403c69030b001c0044016400a008011518002c0007007404550103000941e0420150000611514828050982070050140242c6803d41310750044078042d4001800440038141c49101c00300200c02e080110328020012000103003001d500d0460398605106e4080d19860320351030100000e00c6581c513042c810310a14402500c825880d651480c11702020890250841680642003096400c01040300c1005849520b0080383c1e886d00d2602d0b150312411800da0308031218030150300007040480200c0c5465114a00703182c80140050a0240039600203010382d40c49404c44404a600440c0310141940e092107107180e00715104403840e1826051011490500f1004440c40340001301d03240008034010500360036205115804807043d1900d080054001c1e280d203120307000f41d40034905046000707100d16100340605800765405489400d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 34923341 1250 34922091 34922093
    0xc010207060c0203031608031807050a05010c060f05090304030b1e04020603040809030105180105090601030305030a0c110703050307020306071403070e180106031b02030316050309120406090e0901020c060103 91
    0x380c40900d02c0d010390780341c002840351a0a00c66001950030011384141d624a54900e00010008003401c4941150092030f84010000e00054640d441c403a010b5a0090810800c41c1d2001d1030b152014050b908a00e0346800e00f04414031041c400000090415a1b20070304081140303660b2010380543c0c441ea005000035101c49104049009402c06400654015010704015407030b021155001c81d0940d882034070b00c0ca0200704401c25046400400384138081e0000c203904040c0015514507140204140400f0300110340840e62030540426880c005c283d6100d01040d2642034032080390740c80c04c01a890790030a0400b41e00034098580050f520900c42c80d0301c40300d1400c18440030740c1035880381502200c0c140001d1040d5508059034030480d08801000b084071500814403590007040420b040454401c00000c0c0b80001001c0d984144140802078030100010719400c065480e1040d10790369601080c40c540003000300d144000745c40000d0007046850380721a0300c10a442405030020207949844a400d4200e1140141005044d004500148 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 34924591 1250 34923341 34923347
    0x1009090c1d010f1403040c14060702010212130314060a0c0504210309050402190201060605090105030406090302031e03090c0a0302060d05060406080f0c09060307060804030e010302070b07110f0c01020706 89
    0x35215002d41c50110291880501204200d174401d41e01500c810300130010801554500582988030400251082401c03c01c40e940040d607120300c02e1b0400a001c42002c42d00031072803a9030030102c0c070003545c000c3d11600c1d020424560b440e4841d50159003203e100b40c189117083c0711b0f032400385003118210781e4015949819940c81a200310341c0540012030840401c10400340000c1d041d41c035400500402c072070b8007082c46001c40e10f03140b000e821034149a1188041c05411b00c20801c5030781e041015241e01a4002c0c5000c81c140d9124034080342584933608254400e0384940b081d0b108007881c080080c601c9890150200c1f10090a0b4a041102040b69031100a40c00442008000c200c0640b40c1c01994100030060b0000c07682648034813140d814482e001c5151519940400da14160303e281001e407007600524160044d00c00d540c1001d50041440c4030003440a030900440029001050b40720394100c501c00c5800822515aa04100a00404610904030520401c0c890143c9d0301e01203840118040703048450580007080c0d403c0c40c00e0816 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 34925841 1250 34924591 34924607
    0x9040b0403080405120304081206040b0f130207050a03080403090e0f01140409020604090902031e0d0807050906030720010c0503060118050303040308030613050105010203180d021009090c1d01 84
    0x454280c00391103031783c4482194100146009920a00c0380c3c07522600b0303822a4150f13140c00288500d20503403c1c4000303400341c0c3c1c0300c540c03a06001d11000d45180c0d222a140b5840d05003c0e20a48900411398806c46410009040e4014600390080b486561220b640070343d500420345000400303566040303514550500410031440d070251038500d00c50000e480482c0c440c80703507000100d40740c01c070f0b070300188a0b00d031a140c0107021407809100c401e0508040f0201e061840d081c0501da6640c80360071454000c00d000d20f074030200d03600d28080c01c1034486406008186540c0c0e880e0145000307140340051284a4003100c01c08091800099041c041c4150030343e0590340b140d08654a040045030007000207514814110828070010825440c24030040c0003540c0108590381d520b04240d000d1190118402620644c807500c1d01e00180301d03581e408400c980b0701044103814040001403140005d2a0714040c0c2c00000d41c44095008010107494101e0550800c540d404282048030b0468840182c600c0e0381480100d1046442000050140d0340c0034400c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 34927091 1250 34925841 34925843
    0x10e070c02031c09060909020c120f0f04090902040c0f021b060d0207050313050a0e0c0d020903010504051005060d020a030b040302030c1b0321030402010818010f0902040b09040b04030804 82
    0xf203480010503065075410701c100c4500d4840000b2141c040034003841c0e0f08100c4400c01409110713011490720106441031307a16400d146004100e01000020403041e4088040f06031442c110105906940d204c0d9610118402014141c0e0101d01990520780c031180340700e006a60408541c40150003038544090110b00e40321040351034059450b40200140645451a0343c0741c809448440d106000a40d9143c8a12481e00c03c0e1000d00d500a0f88104500381040c46800c0d8140001c503002400c0d00e03255516083c000d180d0b94080c0c0600c01e9581d0b01986440104000d21000103480c3c20300c580f200404010a481d21810f0003200da400c1a0041d4001c2c0007142c2c1000011410342c003541d0f00c1030007841680c0c203103914440c500b410004040c400030800105044203803000c0c581070024040e0004003080b00c04144070b8503800940640001003004c0d060180f00070000751503152042501008a4024000f00144070a40542c3c000030098040d0a0340a01d20b003810100b0241401a101401283c000402100030380c0c969408484050000348 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 34928341 1250 34927091 34927093
    0xb0105040801180c0806070203040902030703110a05130b0405030a020d02060708160b06030607091401020708070906060801080708061306090b0c07020909010501050a170708030703030b030708010203010e070c0203 93
    0x40058052402c3c4a1031030b600b0900780300d100618a441c14811413a80c61034001c060603801080c1802442c40d000002c64084032191400507071070382d8901405900800401c100c1c22403089001500c56003031540100240224114030b54081c107100c2c1c48000960700d5000b68051a070705036000e440303540f02520b0920035079100070f803009145918120a558032642d40d9001501c0e86442c0054280100081184a042c0740760700081c164000d0170b461425640003085180f00c0d21645040d6002d15601e140030307901c2400f82201418441003100c0c040784e60b6240510040116108150010700c4504c000304003000086002c108a445803001400c01d0f0322440840002c1c400c4d40c25084500c0e0350340340001c200007111000410700c641e56601000c0d445401c80c0c01480010b036001001e0070342c1e692506c001841030350b03660415007007640c200c107050343c00e121481051070b0701d0081c441c1c000420a200c0420305108050740754100071210081a803c1d10303019a0344041c040d00380d0100380110081c80505e100011803a62048170355a0415000030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 34929591 1250 34928341 34928347
    0x5090d141e030f0906060603061e040c050301080708120304020108070909151d040b150307090f020304020a1e0302040506130f0b01030c0f02061314070902070c060c020d060b0105 78
    0x49202203194196078603108440310007004105001d26120002030b40030202c040600400c0c075003400001c0c010300c001820280318034450001c08481d0501180b80904114010703000300420001110050041d0700244070303201d0140304506010459110100c0d21103d10040888480c0c00d5484940c01912221001081e14080240c2c458002800851500a41203003400c190b00a0700100e00b4444045140b600843c40002000c2e1042c06001c000b61260b411700707510444100032002c4003030035280004d0030410280d102010b01400c00d0030311400500264015030041d4400c50b4648005035840b448446805090090300080e203000a40070009410560407482c2d008600502c226003102410043c0700880f52000894000d0903681c20b5600401e50b0180b098580c03020035800d01a4800000c148000c0d07072008010032000210200d031f00b812082062560401522801721420385188540b605c0c54000290020074003940c100201d42400500c0900908280300760710303000713085035181e50b15030b8940d030002c2d200f1807058a040103010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 34930841 1250 34929591 34929607
    0xc02030c0a0809060f0a0f2607270905101205030d02130302040f090605010803130501110f06070503040317240f04110c160b03040311010e0d05040306050a05090d14 72
    0xd1004120701d102d40c3d29401e100c1002d400004021402020445499230058900c1810008043c50034a0303004103c0d01c0e0404034120704400702804000000c0c5184e1403600802e174003103102000340d00080d110b400b00f2482c400d20703a940c0e0490103100180f80d00010b44103400c104401c820450468006150305100d2040031740006940ba03010804442141c0300d04840c0560f10520501008054080e00e80140803140095060107081a6240305000203841041d05120703005403000b045480c1886400007802102003179036154500b002d0007500651084a041300000d480c03251044801e41c1c9030744003034001c400101200d8140e55200d2010098a0a81500e6a501642c841d80310190703541d07140294a101c05c0442d91a80c0c4454018510618114000c841e20480c0d010000c4103000c520031030000c0d81e501c2905490140b070703516103094030070340100034840694160f4021944040301607a00f000080089a110b05820402d0340d840c164010110764003640c283c8085e070000000701e03102d148544c0c10b03031001050481c91a4580740003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 34932091 1250 34930841 34930867
    0x50303041101020c0109210c03050625030204141519050a030c03020306030d05130306050103230d0c1709090108010c030501080601060c02190b0c010b040c02030c0a080906 75
    0x1003210200d60441d2000703465001540d0501c895110310b002030800d0f440c0719042040c2412540e003d0003c1c00360b6810005490010b0100b041c2e040002550441c040c1c3d110303810640c030f003e000898459182e04044141403d48518184039108490803103181d120300421f8240c03030404019005e4480349103000d4002c81406041a600390418182da1840d4207074403403a80d2140000380241c19a40040007201c141881801009000d4a01080c5041c02c60803c1c60040c0c0d503803031000c0d0356458000440e0800713008503107014004402c1041b195540c44c01c545181d0041420440010000356582000d60090000121341040010000300d002c0100304001006480c8107041200b10740200b002e00d1026480282240c1d120000503c00d10781600c5070714054002000580703540d40c1071403406042c440c100107009010b49070340d805880c12080d4aa0715400600360202c00680c1e11090b84440d40d0280411184c114810341c0b40c120300019030b030b000008840200e01600e015040208964880c1c0c040b541011403820f420807010090300c208501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 34933341 1250 34932091 34932097
    0x904020f0c0601051207180e1c030f1d030702120304090c020c0a06030605031f02130909051e0d081b0304140c0109030312050a090b09030c2a09070c0503 67
    0x840d60380140b4403985404200642c01d0a0150030341c00e103030030880c014460013035841140c2c550007145000100740903c1c1c800c0d106141903d080300c0d0b80c5ca0503007046c0703d842402c0d515412090350858200001d1140400303400101c0481c49124040c1141d40d4000c10101c00103040a202d0781089030030034402c0d0303410640da900c10f44082c0d41d1420011070058011040b054110b151903415000070300080d00d000c000650030500840da6440009200f40801640c0180d55000301e91301d03404076000780c5092780d0100080c5a80701c070800050400000112460300481120f002c4c214950902e88980d581440c00034242070358074203002c1d02c80c2c03000502450b030310f0261040d0b6816810050002580a00d10840040c41d0600790000c0044c10700a00703484441c100840a007041010035070018660418100c0110000354036140d0f00440e40c002c051806005184198040400c000c1d400c1c0800540500c8001c80c040d6240154a0300300052110111180c1c40100071000c410240cac18141022000ea2014040c200000240310300e449892841d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 34934591 1250 34933341 34933357
    0x60902010309060e010b0103110403021005030a09050106090b0f04050c031504060302031903120b030706030e010b040603060c0207050a21031101050a0b01111c050a0302160c030c050d0f06020904020f 87
    0x181d1961090a09548d01d48210040444074207009404c150a55000464800100180e0300401c40301002003086d400441c0d010302c000c1588100208072140d550690301c005050551180c621684a49140703001da81020300506120b407403021402460740e40c4074000c2c1640c01038001304164000c1c0e655140030005031803c101c0c2c20044070b01b81225402c107500300e2800415000812071009402401c203070721403440e600d002619205560040c01c000ca141d0110521960042070051032041d84581402c1c03001082c80166482181585d007943d007582d00c8103032140b041c003640c00042d101e00300800c03981c20401c10030160441095144141300c0d162803000c40581c44021825034006441c0c403d0115642d0000c00b03025a004610802e086503200c0150900307041602c201c0d80c0b8900030902c96400c0c0b20002411750741c0984a40e040720400c01c10908480350070a0035052141c80040030780802c030f4900001180c041f071a8903020510103816640050716940c002840d41c2c0c3c2c60080c0d00148502500103400780054aa00b190903c054070f607403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 34935841 1250 34934591 34934593
    0x5060a05090f07032d0812040201110a1b0902040f1203050c03030103061a01080105100309050f030c0a060e071212140403060209040501090b01050405041107021f0216060804060902010309060e 84
    0x9083c48182c086002000c0c004194800300b081703c0170400207007100084e902e1250541288034015501c07400142d8005803814000b401500441d541a020000190340d10000030b5100307444101c5140e1145c591380200e00c0349019000340300713007a914200400d4124901c1c40d4215803207860110b00700007200500310701c0c58000ba0001c1310600c2d16100014007003040b01e14641040c45092030040c44551401d40842da05c081ca4464180801da260700107007080c08420003429840d860b4880480b59140900700c0b046803038058070740048629500b0710000c12031036680080d10201f0380d4110280003c80404a55407101403060002001090260f40c101c440c24100c58800070f0300c02503008060169403a050747e400c2100702d4805800240b00185803900d07086450364403205850035a4800e80e000a000716481418a0150103600d0340254070010b101504c2040107045a141961a030464007211000c08045a9808030703100d440c058280020000300000c0c001c04c20540003054000e0043c100061090015110a41618580c80b001012 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 34937091 1250 34935841 34935863
    0xb07080a0b041503020904110a0b0711040c020d0503090c0d060b0319111306050904061b0c0f03030203070c0609050f0705040e060a02090111100504110d05060a05090f0703 75
    0xc0c4805070081d15140a070484003008060b500b203075114003101050101071300072224403001400708081241000c0301c02000412024045940e00c02d80c2c94690311408080780d81c1c030103841d1107140714105030181401c00d802940190900c44801d00c021a01900010210815842074816080081c0c4403c1d060343c011030300454000c14202c02407001d0606d0310403490300004181010b1442c2002040d40d9020144c0800411500c420700e030240686464090b000a8004c5039004c20360000740801c00040350b00110040c0600c940b205001005030304142d9051800010142040841011510000707200342c0c011540700810b400d00600b82e0120f03031100f0080384e561840840700799010805800605104014440040208440a026005443c035404c0d846941c098800e00c5410780205120b10240e000b0130200c41c074040320408030344c03099081c8488003014000644003611000f100300d084950506081209a603110f40003401081d290311001d498030000c1c2002071400c0a0382c0106900c140f2220018403441005501035110044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 34938341 1250 34937091 34937101
    0x5070206070327030f030e06130b0112050a0b13050a03030e010f1118210106030201030c050906120903040807090608010522060203060121020703020c0a141c0b0708 72
    0x44401101e05542c0f4090780031140c640006100c01e480381e0a660501e0181c4004070540e606802a14010304559807e000d11410080c150303d01c180e8408a5500402030000c590341e944880c008010801e0001a1064200e510b0050105200079010386d080b9001c40c2d0764001e085800d4a4007400c02c40b020780b0441c0000d80b90100d12005400034040c1c4201841c261034200503103884c008181ea46881200743ca8449081d2046060308166203039a0b01030003d61415013414031091500e002c5600901050100300e002c0380c80c1032507110f011846081a200180c0c40a4407140c41c09812403c0303c00d00c9200181408581d1008000200390381005100e214024203c0b00d0303011403510704041c2411b0940700000c01c0041500c1744064092880c1d9426442c0a00395900080016500c0d181c0c500102c079000618001c801464000d02c80d400b200040300d0340148000d0780690700391801c1c02c809008000001f05540318208130b1038140c04180302c107468000c400b2865000c60325403110b0301d0301c11a03131042100501160f16030702103180001000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 34939591 1250 34938341 34938347
    0x30604061403070611030408031b070b070308010e09121b070b0705030304080a0e100f0f0305090705060d1d0f0d051c110c07030804051201020708031503030403060507020607 76
    0x80d000e0a07850640ca180d01100902095556070306114010411141c1881ca080d100414401c44000d007001d032040d05d03a52110f0702000c440c03407403114142e03040314031860790b00043c405512000e540010303a00d41d540a600b80d1a100d044208880080e083c0b88580c0100c10900c03003c1103904008001c0a0000d0f14032000d09008010801d08000480e031007521510010407a000028402100322070303000d64007480c2c0f01e0720351044920440d160a1011031458000050060300f081464102d42d0f24204104103540b00c8800d50003003103086007510800d0780d509000398008039081c801868820f020340071540b4001e00004071568a9640b030b000207040000c000700c43d0f420800000340540800c0c0881403041d8000d0030010702d8055007802c403500120256501030a51581d49001150521710701d01126403400c04502183c0b01140c480c101005994060300c249442214a014104c03100641030080d20604c0e13400039141c50940c0e80f100320100c602030141c03120710740c1404100f102000250840c420035004040300d5004100b03d242140b009 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 34940841 1250 34939591 34939601
    0xd0b19080d09050f040203130c060206010e090a0c090c020a020a030f05060105010203030c030f06011e090501020d030b010503060609040b150703080c0403050d0e030f010e0c10030606120515040e03030604 89
    0x41010b156018041504c9600c2140d081c000180d40042c0d0b65624035444420045082000425119180c807000940540c0021031034166480d41821070800d45400200c140d4802c620700000b040c000c60000c0421004040741d1007405041d807a401502c50070200343d8001604909e160b002250f20f12211981303d000c1c010100449400350100380010f501d1414500521170442c007000b000b40c5c16a8120000003420b03644641a000c00300441c06140d82842c6940c504060180d182d580a01d0340140706641082610034400d009403c411700741a1205850b544404003070040c03035800b03c514150407607264490040582c80741035521018500802a0b107072a020185401854120050818001128240b0007400802c03004210490f01c000b1a060444216140c1c4022905021000c411100c09503c5c0c6003200e14129004100c1040d090800c482000b0011000c00050301101d0513070095400203044812111161181c5900042d004182c4808600003802500d00113030075200c10700403e10f1540c00110038130441d030400f8090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 34942091 1250 34940841 34940863
    0x60306090c050409080403060e0309040c0c11060307051b0c120d09050109051f020109080313050601092013080615040f0b0f01050715060b0405010207080106080307080d0b1908 77
    0xf06111807143c0d5120800c039406140409480303c2d0f650300c20a500b100e000c00032140c000d130001d8001d00a0580d81030b8040c094100d04a425103c0040d0000260885d1600c842100e02c80c0c0015180e2505114111b402e2000410194800d0b41082c881c4186512711641c1c2d20a000c010210305600412904100210090501d5800e81c042c81c18066251380034001660394541c261401c6108044c01102d154201404034050310310150040d0441c40000144030301c00c0c0d100200301041034094400c48109998800a400c1224081c00d152a0925402d012040c00210b03000001e1600300e4103007034a00c1c0d0300348c2c8072102d460510b0300681e41a04c40704078400c0d4011841c00c01d070081e040442521a8100002d000c00c2d00420281810700464504000b00001c0b40c404228007500c0009202030606410844507403924540240c60b80280520350140c81403400005a90300705014100c181c541e0ba0001d14100140c1c0d5a50b2701d259001032816590703541d100c511308080c985600003a558128030150300041c143c2e19001041d410710318a202 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 34943341 1250 34942091 34942099
    0xf180b0f0a120c020a03050c0312040b1509040209010302010309050f0102040b0307080702010b030705060319020d0c020f030c12070305071b1a040e0613200306100903030e0d031101060306090c05 85
    0x3c00c1415907500440e000c0402c9415040c2103540311119101e507402c6104050f8013080350f8503080e0911003803240090b41d10307200d00c0c0300b4211940005928070411041a404407002544001c4080c01800154465084000c40d103100c1e9080300d01001c100b010030380c2645c0047d000002c1661010042100451303000001d641c0100c0c460008010f250031140109842e26190301841d400303040004089010880b803a0401c8111500c03504c000c5407034290401e041409031421f02420801031042d065002001e960220480380000c640000401c40502070115120450300303c01401d5050140500059010464404a000114600707808100a15042c0104030314881403284040481c2d0381d06000520440c1b6070142a00e07040f03007046405800781038039130345008003421135071b40101040d1404905116000f0100805540180c4084034081001640e038001100c500c1c0080c4000b500040c0d42d881600c44904250320a803c003d80030f0320b80345400306a41106242501d5059004480b4245e491907040e0920002c1e010030790290000300c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 34944591 1250 34943341 34943351
    0xe0604030309030f080421050903010c020322081e010902040e0c12011a01050313060c0801060311070c031128030201110606030304030206181504080c040605010f180b0f0a12 76
    0x1e19158442840c1f200020030030608404081e010030700070000e43d502114000d001340452040341500031748a4000c480c8260f940354204c00c0b180c021076112078010050351140c3c0001d03d142c40f0141c5000e0259040340300e1082c825580c40c3c60200250f103e81c0a12016208980c0003440d09400784010300170500c01ca2045086503914210308ce4002014400e0381034900202460140d40341d8035490380003007d04407403083c010810b510749910140801e400810941c1224916102040210788000b42c0000b24420490300804010403080c003440065403c1c400100350b07020207007030008440f071160040d082c007030040340303400d100303a46c20107010070031503901282000ca4007070001d001e0206410b1040200313959010b1800001c4c0318110104040e81c42c00c9041440f17250303100008001c00e112640d4106a81d1243d0f01501410074240a02c07031a90800d400d0600400f021504180c2d10314140038415101107540158040200100d0b4100500000364102c441c0003400c4011160040103035540c1d40302001030500c807292108125204c3c245 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 34945841 1250 34944591 34944593
    0x8090a0203060a0b01050c03210108030702011211070507080304150903050705090712020d0204140d02090a020d1503141c020d0c03031413020907020c150a02010e0604030309030f0804 80
    0x4102d29402225581000c07905150504c01070311076002d444001d0b44c561001040c0c080951010340c1603103562100d41c484092450345c0311903c280e22881801800303400b044900c2a560117044840d4001d0741c1d1003000b69101c6082c1080c0350359041c101000d990000140780d00204040c407800b03580403403820f20074140c0d0902402003855907941d261034a54074800c443c420000f4400152005003d6070f130320300c0350200d4a03904656031414000180000d4100307018004580c55114000942c42c1445252148120380050601d81140c1c0d8074960040a0b50021110044141d00d6104120303041a44001c00400f451041380c0c05035407440300051391480c2c10070709130380d85c0303022001c0b092800c190f1f503004191207100100c24030f458803a030310f690b060940151400400c0704407154450000c1111a0b00201d6011000350310032181500541c42d00c801c103e0307881c04100f4503181e20003091400100000d0fa4607005011114490002281524103140b045040a604580030b07000702303440d00403e008140e4015100c0841c9103160030007515505107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 34947091 1250 34945841 34945843
    0xc031803050618012a0f080405030d0504031407060504061401030209070e030102120f0a0c021b0105090a0f06110c01020105130b0a09021003151a0906031009050112020108090a0203 79
    0x2010704440c1050206007103903000d03800f00390000017000404080c90059040b14680403c0264150000c1c440010303481451000f0b51489074501ca070103503811400450410026462450007404083d03c06c41c203000703ca00340f0403050f00c107a00103003070418050003001806203054145a000e640c03000f520b85c059105881c00520041c0e6a600c8010342242c11440d1916500030701e5000b00f402480b440e0000144010a0b804209140e005007840600c6855010000d03ca9407050300000d995564102403109080c000c150000c4c0e050b94420b0300039050742c410040c0114120383e6612900c1200f90120707044a40000c01145001d00c5800040250002004081c03000700180d180c5039070303001c4003880c094500600c0c40306039401240e0140000d40013451040d8004154a404d400016805030081100700401c800f4510724010003d000a1b11255001500700b12910907813500c86071070100f09503684000c0031001c00e40314207000801e455403640f040301e000e0716034004a900141b859000141c80707000000c0004070250320015040d801610 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 34948341 1250 34947091 34947103
    0x10602150612070b031801050f150109060f0f12020f070c0b210c1e030a06050405060d02040903050c011506090503031c05060f090f06120706080708060f100c03180305 73
    0x4d01c4d00c0b105516034445154a1500080440242c0915820b201c00c2c443c0a0452108150090b51240d1903018030f4041c03040150344501c41440b4074008241d4283c4080c1c0024040c0400882820003440d00d50545540a082941260042041910f490720041002c00411070130905101c0030f008001c3d0039a0900010558000d1521a282c0614a0001035a80851031341842c03a4252040420b24807104525091045124582c030740040317905c250075605181000403642000d1048900031780000e0040b2020380b05540900000d05000e00303084003088000c1014100c261001e00c43d00808140c1094481d8905180600c014100d00c1c5039000184a500100011041c2c8010300c0494400e0654482c4003080c45d595400009a06514420103540c00901d014100016010503054141c80340c441221006000c0c1a11040940c0c2d0301801d000c1c4a0210711480042a034281c000d0001075403200d4014040007d081c02c100120b8a9001078000533070126036a004000e04158000001c0e030070f0680e03072110801c0000d1440c0c0b28143d503a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 34949591 1250 34948341 34948349
    0x60402192d051c02010e04062405090901120209010603140a11040b040603020d05010603050c120604060b0a08040c0506181309020406030507170118060e070302030601060215061207 79
    0x503405582454803060740d10070000241070050a240184441c80000c68a0449080c82280000c084038905051880c07d440342ca400d58000148081c44416488825101c82040440c00c6043c0f210504c5541400e0703903480c02c480d000e0266000c2c102405551f034410300c0910f14068020000703160501054400602c00c590225a0180381c0041c0403540c400c1c2d05029210a102e9a041003400c6400000c010844d660140c0061a020002442c00c0009a907a030300c0031012501e050302c4030b403641e4108110004c1c1c0107289101c13454020f00c0041000418a035292070350308050f4002001e031404101c403201040140100312014000408080d5801481d06040031151111005507001c05071080181e482040240203059114010701913002d48104000c03500c2c0d042050b81c9100394481c0512004042070782c070300b5070a4103000d140e070205441c1ca1110100801903442c40040c1c020302803000540c0c4108840080540c0e420420039000741244e801401b0701c50022544120304910003040140214200101c0854503100024550111 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 34950841 1250 34949591 34949639
    0x5070b04080d06030c080c1203070201080103020108090f01050a1b0f020303060103020c030904060308070203190309050f01210e0f030403020306010e09100e0d030501140a231206040219 81
    0x41c0b248680ca510040400e5000608210704141001c114100c0c0004d0041a010044805117031085000e0207103980da1068003002800200b42e00d00401c015401900c505412009800503519008180040242120421200c951015440e805980c0101c4141012040c01c3c40807803500350303100894100082e40e6403002030072560405a00040f24401c1800134001e460085100034800e014090b600d003000f070303615007005030103a10070702415075858551012029640b4030581e00d80c5900c031721700c1e00c3e200400000c1c1c401d451500c4d060219001034515070b16a043c44010303400301d182000040d02c1482c2e9903007510380140400d10924a910412003440540d40004525044490040711824203a603009400c2d82030107000f0f40080d06c43d50405c248042101d0000c950041010b0803580c040049a0f80c41d171005810500ea58139139500b1102d01c05092103102030001c03580e14200301d0113042500318404440400d15007029a400c0c2403468021a052004514006903018024104c2070100340c20641410045003943c80c60407066001e03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 34952091 1250 34950841 34950847
    0x5040c090e06030109140601030201081f0501050f040803120109060b04060c08070204060b0406120c0504030f0201110c0d080301050f0d1e02010c061b09080d0507031425030f05070b0408 81
    0x42d0b81d825000070b6012030f8442162020301c070702944410340e1107000b80400c902250030740c4009030f00c441c6a0381a442da0400d18194081c3c00038900b1006481940c0098920400040104000310318464100001c1c04c00050030143e8003550341c5001241000c550f000c1d00031078050001004100f104541c401c00c0150100d80000001d40c1d078440c184006801040c01e507020814940d404103000a0380780c2c1008918140c008500b000741f0074021130400c2102da070f12850000a00c0481000c02400242d40705091120f450791924044a110001c104000307001800205002c89680390000300600850906460800034200281c480280780901e554400c000c0e42c9211421441952004e40102c042d0381c410a4404c1405821540821406085241c1d9000c01c1904074504000b003803c007680014003074000141c2d034101f0320f0156100d40c20401150b5044a40c115110031880700d01c401803088104080c09102d101400038441c0c20b0000d8031190b40d1030003400c002c0c0790064802c248141441000302190f100000c40380d000d81e2091b28995 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 34953341 1250 34952091 34952101
    0x605160816030f1d1e090106020d02010606021c03020a02121c0e010903050306100e0402070602071a101a07080a0201090b0705030c030103020f04021c061d1905070203070605040501020405040605040c090e 89
    0x12005c82c064040d4410a40400091003030340100300c081000b4000d50003404140d40341e5034280e0340c5140c2c2840d4a243c1c050699416071003907103e0340c00703494850901c0c0f042c5d907070100046201c0215500115400b400031300c4940d441c20b00c000142d1203a09400084240284850051910302030711a001c001c0500e0301034002100043e80c1c4500c541c411401c2c0e00002841152525041e0800d40c000750407080307040b80c0d900c0380610750500c40707009010000c0c46548000c050b80c40031403c000350ba5050314031381104034030f0315407080c001000082d2121001d40050306856000150303c90130343c10002c000703503405058501882000c00a0041d00c03500842203e040d40d405517007642010103003c0110700207210700d8085440b007900803c2900c00741021030300302c042290350343c1c6413080b68041031541c03e1210160680315a02c0c80c2039814000d03501c000c070541040c0c3e400107080c0141e07401d060705500c400e41070700c03003c5604031042e1758001414002d62070b20303100b0300000d06000e03141040400412440900142d03000d005000104101e400021 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 34954591 1250 34953341 34953379
    0x106080105011206021b0613020f04140604150f03050303090606010903030f030213030807060c020f0111070605040c03050703060b04060f0605030f040809030106030602030f0903130605160816030f1d 87
    0x240d013903040002c0f503180323280000c5000c58409440720100c0c402c150b034280648007440c1034041c5441030045101070207141e8aa1a00f00300080c8019000c681e00746484450024402d00e44943c62401180204c1c00303141c0c0c134500075441c1428000c00902550610203da081400807a42c402690001e10b49241001691915010003035040d200ca00e900091494900141300000c00c84150051312a0014540071101d01061001115090b03e542c0c3c00500210001803001c0000300341e050f08055005030154451459a503180c0c1c59507420241c458005954094907040380f4804c2d81050b200c0c0c0d80c000d08402a604102234200704d8010b00743e100190003014820540340114003840441000c030303000840e00400822104e60789140c410040d410440701d040c400d510540002d00440c5c404070440e0341c901020101946803609024050380d06030003c1040150224540411030005210003009140002015164034600c040c0b51800518039020031420300d0401c00984145442580604400895004210b8801380d45624048480b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 34955841 1250 34954591 34954627
    0xd0c0503040f0303020d02010b01030506060d0209040b1011251e150306091d0d0c140706030501030209090a0b060d110301020a0302070b0c0901090302010f03020c15010503010608010501120602 84
    0x1c40301c0c0b400218000001c140c4c00141c0340144107860b800074018132581130011340c11520f080b109a42c01660403c5242c11200031540200129400100001100303001c69011401d011515000100861007000821818000c00c009c84a01c1401244060a030a150b03030104044203039241c0710f42c500c1103811051120003582084491380203411141d011106100c544100200030700f0092188500c2c0318908611000c02881d104034020003e0001e100030015200700035002c80e010306a90000303691540703800e404404502802d004210040085a80204d01035055004200020902401841142c2d0198454800050003e0000c95001074211900c400c1e816003801d0040342d03003550300c50166140d48006102d505031a00340c5d001d41059400f0f00900c1d0215900d218820b2400d100d0802c03864003184100c81c08200542c031603050704041040503c0e026051107000d5002070b14044c18200c43d00c040389045e40c0140114202442000002c01e040402808030754940034010a1070400e0358005080107400042e4203940102c00108 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 34957091 1250 34955841 34955849
    0x90a0b091614070503040e041506030b060f04092303040302040504050d0e0102030703050f030c04050402030f0406110406080103111801090204080c0f090a0509010612050102030f0105120d0c050304 86
    0x60000c60701e86003824210060344184090003240510680481200165003503034621540640118070f03003410440d4a100c0100000d00465502c101e41510460724003480c01040700841c4501100b10050600b00c0801450788140b0120500443c6030003039410101c0c804c00700c1c0400c2c401003107498054008a5140e001d080d44a01d800203504103080c84140020054002420855601c072079544400034170b55400120307242d100c1d031080500059814010050721080410003150040c00f140400c0f86826614001b040a076041140e01c450354041941c200404e20060f0702850b0754003880211031a00e0319040c8003010b441ca030418000036190555046100900703403604000c0f1308072803050440312041c0e903030354500d01c5010b50301c9805521745c18013030700c400190035092440003c607501c00000e0481d00345541c0ca003e50340041100130424120b0750348a02002071103c959141100b50140034000169a0b803a242d1071440081c4810b03401640100c0f00d1511540e003400740494034a1420349940707050441c1e0501400c10718554000c070b802c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 34958341 1250 34957091 34957099
    0xa09140111130b03041203022208030901080604020405220209040501230613060305060112060807051206010602030a0f090e0705030610080c0d0902060c070905010e01140d02090a0b 79
    0x640380716003000040107404044050000882d8181d201c00b501007090109580003040c1800d822089500b050107034000d0710443c002060f4924144c0319001903441e114882d90300011558000081c02103041d40c3c014802f0703074411000c4d1810340c502403411000c60b440030b00961340038034240c824030380c7e400e0b90076842d404448070b0200c02441030016585035200400803000203050380648588203030710706003c0d082000a03a2220a0300d450200700751490b1100a50182c00010b0006040242c241e10240b824045482844040c0c07100000500c40c4604100034000c0180d00851000d855033311040c01000004c0c0c2c000100d40810015160822840d00e41050940d031014040d041901c0409040d000c004e017040d8002c0c0510302c41e40c400c44c2c0c00713407044d038200d003003a50005070540390f10a80701d404102e400c0e69a011604400c05040c4007a002c20300e0100f00300c540c10700703108450b00010005a201d034010802c210b00b00c8440f80c0903240c1e40030740515110010780081d0018501d010001d004004803000502402c0d02c0d0384c464005540c000d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 34959591 1250 34958341 34958351
    0x321020721080a1a09040206090306010603020d0e0102040f06030b0d0804030b0403030b060702030c01051308031225020c010309020402040909152714010209060d06030308010b0906030a091401 84
    0x842100d980d5070444509000181088000b9a60405070f0080a40e03605003070030340c0c290358108031043c065031540c000e200340c6c0c01c40c60130031030100c147e2820400d40380202020f41e07006850306482d0070350318180c8400b0b000900c1c190703006010900080314280f124004131011400c0000d84074a40e1000300791801c0301c002000c0c04490020500100344042c1038500352042344250750070409000c4980030403005001c1c020303001e501a03100015009680d405075000b401c2e801c401031a1201001d648107500c031325692000c40c140d10001c1306403042c05442d4000c51003200c3c000c0100480382003941c01c0841d000b5991918100364604040d1141074140c2591501e9040300d002e44000c4d101840594854207210f03441451400741c0b11401440d049105400054204a1841ca003c546080c884200302c0c03910313084030b4064039009004c11958200181c2155665140040240f09000034000c1060351071400c0161401740f0581c0002c002c1d14080002da00386070f456004a0380e0110300c01000061140d428100340488100c00e1409502941c681 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 34960841 1250 34959591 34959623
    0x9010903050f0f012a0f03110a1d04051b070206040302040c03020a0e0a0f0b220e01030c0e01050105030a0e0709020313021309030503071b0b0c03070e0102070303210207 74
    0x2c6103250400015030028001c62040c10902034024808100c20718440d5050814400090b00c141c82166580e0505d15010900c230b0400102c00c072240c0d000080f1100400e80f80044205a441d03604400c109080c2c2c211010051854540c0c03083c520701c41d80d015090300c15040000da807000c640c0c0f044141c90246402400030002449082c202500079401400380754045284aa8031841c0c80c0303032401c8800c060303941d840020040c00345007454000054001c3da00b0030002854030207118600d8a6054104001001780c1c2200c3c032101c0d45036003000385040585030449078021007048014441640c000c821240c00a07a450800600800c02c0f241c0c650030300229422a526050001061001c050003003042c070440b0360700845941c460000c00300401001c64a81c90b00040102e00d003400015500343c012100d00c2d0324a001c240ca000c5c6150602d640d00e4520b4403080340c580103102404010700103942c0e0f11640341289a03a00707000400c01c5508585000e85801d0440d2031800d101c0302001c080911108940c2c0503603d44a03407004043da400d80711 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 34962091 1250 34960841 34960843
    0x1404030305030f060a053001020703050405010807051303030819050a0c030c03150302060304050a0b07080f01080f0c06030a020408100c080601081b0904090206071103072909010903050f 81
    0x2503480082000702c00000c0b0710741780740014181044401c01401c03445510300140d41c80300054442c9121503501c1d100c070703400300c24107080c20b00042c041c0381e20a9840941e60340c2003038005010b0800280c58001003140a00c04c1d45407005003007540c00d09032901814902a0b564030f00030181c0f684412080c0290100341040b05101c402c07101a008803029039020b0700d080c40b80400500c1d0842c2124080780d5141d0b1400e9051500b0405810168003c40d049800740044d55140100e680b80c0c0b490070141602c0e024005007440e810020b802d100760501c2d41c0540312071006031a2071030200c800c10340e40e0700c0a50042c070704ca60000008546603801c1c0e981298000d1250006440d103860741d00000710700a180d9941da20010403106000507481d98402c0c0e005502c02c1d403059050401010b2301c425820800d030080703401c59420594804428015980e00c00140c00c507548141c00001f0048400418035080c90040da000d0710400000f014a01c1c8047c81044440154181210b14079889219100040b1651305443d400540b05000b03100140300c40f81c3d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 34963341 1250 34962091 34962097
    0xd020d1407020f151506070302060114040509031905090a0b04030210080f040f020d02061b0f03090102100b0f090408030a0c090501170402130501150801050d020109151404030305 78
    0x20480c0321114241c1d07164002641c66603c0f4481146403600300184041d0107510141d82d40b0740107503945d20f01c20260089034000c1a025130080d2402da0142e4420001000448088140520000015a028442ea00b0082c544039540d008034009510031010099880c58928410300655100c2d040040120b560700c0c0e50381418110303a0b40140810b0340500c00c1650b080a4041c00f601d041802113158505842550b6a02d40b10700d010480c1415003260310170072185840001d03070b0340d01c005492004044001c001c0c2000c1d100041515264609106407496042440304040681e0080354060170710f401242e000c00d0702100000021a01e0702c011450703590216610301440288201ca00c00b9621440144030704002941049038259884040b520455000449228052340c9802c54025040d41080c0b001d80403604440c1c030800050180c038026000b541d41902400c10840740c0c00d5003c40994014507080e50304800c82403154000030070320003050040f403100b03000c20b0007030751041c038800e441c810a58034251a0054417035840f071030700910b194 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 34964591 1250 34963341 34963361
    0x8031519030b0c0702100809030c0106060906020f0703050717010f050705090307060305090c0402180904060b0102012004150504270c0503070c0b0705070212101824020d020d 76
    0x100070300000c070b5001e4000f046420b0940c00400004103542009000c648030304008240320050f000521032024590800d0051030040c1420b81c03201160315040410003490181c68103200e81ea99840240208007140011400d03a0640d450340252001d00c031611250719002d448414a0700112529000802507819484809401581030440c269440c45e5600c0b0811002c0c0d038020383d080c40291f000320304036649900d05139000384a4038414070707e02c00039800d550000503d4031008685c180c42c15600d0303030000c400545e030a10400d9400c4480300c1d41184000c4070701d00881e1280c060360050350300c82244032078440d1040340076109403002020020301e0611210350103003644981c10540c03e0245403060a111914920301d02070800c0d00e11501d256035542103990040c3d1079440c2040310191184007401000c01106015848440601494081c0350000344000c40e1440c00f0802213034401c443c40c0420b1000285036100141003400780c132540d0803810350b45d0303540500c01ca2a80c0c0024400c20410b200c03810302c0000d84440c00801ea8124a0010f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 34965841 1250 34964591 34964603
    0x304030209010b13050f0d1e020103050c1219020f0f0904050a0203010803030609070e120312060108070c0803190e010504060b01110d110f01060b0c0c0103090f0803151903 75
    0x990741c8980314410750050394075090075096003020900850522544c001a84480100140b8007c1c0050701c81000318401540d240e6829610782910070150350301030042e260888034100915240c00d8912072117464170803001d40100441034001140c40f1041c0d6a5070141c0303070200000c034030340d41c0c4d6011440310990785a4440075215000c0d81c00c0a0000c2c495950b20720a80741202e81e0038014510751341d505c41c01c1204400004192405102004034881103544070a00d0800800003010011503a030107104400000403d0001c1038681001044010400701b207a004064040569001028a44030b880d101881d981411105c1240c000c124503240e043e2082050540099004500411013040706c280c05100440b614103526030302d100b20b0b50040c071440c40310601c0b42d10403110031104401502c0c5e2550707603020007038256010303030740041400e1034080782c42080684140110102d12109003020002a8000d541c0c030b4031000704501e4058880c0001000143c0880494030096185040060608081300d000302a80070403011035000903201 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 34967091 1250 34965841 34965859
    0x703060b030102030403050703030f1104170705040b0a0501180503120913090b060d06020702060309010212010b1216030b030d021b011b020f1507110111011b0e0f09010803040302 78
    0x3480c1818030850703010700d40559030146042d24548082c0c001d0301c00e02040d01a92592408032505d082c8105d00900b02518924505072507410070510254500b40681d00700714851454031344400c806699071458441110000c1c01d007501a000070100030400c081c1d1a80c403564050180201a40c069002c9200404d00c2c00000c88e501c450b4109899070300310460384500300c01008003070f04d0720100b240d610b0540b0aa9041d00d11443c8003500d001000d41c0030404d1500300b6a00f46059a4001c01c10018a6900c0000306016000746010349090101804851b031090b0400340818040c0c0700d4440d48a44540d208e5040700302110b50180856140540000f4002c1d030b15072810a07074011028080314440b00b1581302e4041c0103100700c00b820380d02c03454907000d408111102110320300d410741c404240e5441c0700d040c5484001402105000303000501200c5140800580403081c0310400c1011079240c409a208001481407003001001c046141100c221a14100883c062105542445920801d1000001001d940000091056a10907540044 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 34968341 1250 34967091 34967111
    0x70b01030b01030b0106020f0705060f04270c0f020309011805030a150c0905030a0213060f1202100c020d0f0c0803130906050102070f060c0c0905010b030601020d020606010f11120408070306 83
    0x20b102c2341c82003090240b44c0c1081004002500d4008050310040c00c9143c07400340352a035500c0c40c1400c20212581d625240d10740100b1a1004407115115a900c1070581d0b0a140c002040455030080d140d1150a0100303040c85000b91060341c10650000f1583c0c0544005030880701211300341d00702030301d40901c1d442c0150035050402c060381d031b00603101d901c000e0b04a07080540248072074601795080042c2c42030b40c1d001013035913180d990038000784040341980c44000620b40072036101d0b500c2c4d6150040c4583e40c0d07040910002400847c03407075440141c68102051074a25001440c0c103034032075450301e001010503240740e01c40700b49440301007902e01499030701000c1c000440d0441181081803598940040e45c031402c09214075056103445007000c00a141c0070783d108a0905100e4068003445036150f4090394100c400a070403180080801000704005560104060040b078800307800100b14070300d00701000a02c8040c04510701001c200262070038860190007005040c0a10521210140e1595201c4443c650b40d40040d100c2501e6440c2401603d403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 34969591 1250 34968341 34968343
    0x20d050c09040b0a12020103020f0c0601032001020c0d08090301091209060305010f05091b0f0a0c03020d11060105061606090302012f04050402030c07020a0e0a0f02040e07030b010203070b01030b01030b010602 91
    0x11381161a03640500b1030f400e0081c2c00550083d00044440030752603100300500c000282d000d01410b4065842010501111040500b00129413021051402d06561000c07040a42070790304c41582d60303100c40d440640725540715021400310b80500303d6000020448034001420a88140d00960f4140030754031181d4003000180c0c0d0300c4032000c005269a04c6070b07a420400c5003011907420780e00c01d654401c0c0e91030390200b25442d1a1082444101913071000c02c020307000940001031078040541c10f0250b6210b00009140043c0c2c3d003215000816180d0006102e440d00c02c42c0002040103106441100e60601c440c1c00c5a0108106489424003901904003003d40c2c1c0d000304510b1004044103040c070401180c9501407103d5940c140790034001440700940c0702424150b83c0c81c609001210041c4c0c1da11510401a10f4400c00000081c2071864160043e5860081260340d6075005010505c9a5001c020360319078130000354a001302e00d1040001c0140d0662203000f0700601480c4441c400402404000401c0f039040740d20543d07081010360385e81d000403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 34970841 1250 34969591 34969609
    0x30a030e15160605060d050708060106080f070e12010f02030109020a030501060203070506010e04030c050607020d0f0c110613030206030106030b27040f0615090605040c050901020709050901020d050c09040b 90
    0x44288800b8044a0200f003003640030342d0784204068928684d141544d110149440d406030322240c050762044ac01401010713400b5090380d4020014000e9844241059400585041000d182c01360090810900e185100300d070035040110b040301d003c801190340f561a0341300f50001e988005544404a800c0400001e80b2510000446007030301d4121000e403403541d09120024004d50f034068002d41c00c01280c101e0300d03030128005110300c90281526400404c4520480304003c1c03d0140c0d0100d114060001c086220f45c042105081c0c1769040301e900716a003036921800403904131340e14429508042c1d0020710101c008207810790560700c00b980003181200c2500b0380748071038440d10f50f00d80ac3d00344000c403c208480012400282091180200d9588280c07804600d2400048900300070100540c4000c00301511081c0801c8981498400c4c45080c10140c0751080c41c1404603c0040d40d81e0a80d4419030700156503940028044840c294192103000c1c040e15410b225034203040088261980040e04541e101c1da20380a007840711807501c6244 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 34972091 1250 34970841 34970857
    0x11041e150b04170a0605070c0b01140604140301060b211b070b090f030d060e010801051608040c0914040b06030c01080a180506090a0302070b04050109050d03030b030a030e15 76
    0x2030940303400e05020000b0302c111000d00390320241c1e1040d01e07040310005e151405102e2149010341d03900b010203200b500b088114094183d105900c1c40510a50045498541030226400d079118012140e1a920841000c01d004081a41c0402d5400300d0100700501e01c200e00c0c00100782c00062000c0d1030502c9071a850ba00d00c0140050301000300c14103100300726003800540104481603115400b08256102d08441482d143e045600c07111808861607640e420074081c149040303a8035805050000020042d9152042580040c04010300301e641c24403246400040030400e0b03840015018140c01141840b011310000c1384940200d8064504840505c03000c1d00080740d506001800c40700034541692034080a444407094040188100d50019404090014100c40421410403031607010b0720041001b00201019810024108a0550030000c401d131001c009c10030090383d1040c2d0310b00544104940c0e00030b0801c0b071454103030004d04005030f10942601900301080c0505400440d02c902c403031001e03107040c071204c012031202030443d03c00c0d400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 34973341 1250 34972091 34972109
    0x50708090f0705010309050a150c021009020f0409150c030b0f060705070501050d14010305070305062a09011e020607180e0103060e0f060103050303070e090c0d0911041e15 75
    0x4042155603c81d4000c000d4440c005c200356000c0623080d41741c001070380c0c070080000aa001e8540b1700d100d0320340b40e0410090030f0300c03010040104000b61585d80040c21540510b03101510842d03c54001e8000e00000480c2004a1540211300b040002c00241e4054003401e1350f90000ac0c803d51001004c9003180c2403c001721184140d202e000b030181241010010742d0303140c0044176a80105075680418003003d11600e00118080c50040c0000c01e4110301c1d40c0f8107146000e00081c594158201890240c45a411340e070010b901651101140081d111592480102e07000c03800d0010078401c050b00000154186074004c55468060003250f5035840308105a10a0044044a603204080074140c9000040001c1502c0d940b00a080031210801d80f4050300d000500700e480c0c03070000e81066034960800414040307020340285962200500941d00c00400e0b14000b02076000d64000c0074449181c81703480345500c02c10080d0210003107a524200410802c1042c3c2110744000071403080042c184045413500b8001d101c82140c2c410042e003180c900711 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 34974591 1250 34973341 34973353
    0x30216050105221a0c01050a0b060316120513020a090225050a060c0206010e061c0615080607020d0809121902010e060c0712080105090c07050a02060409050708090f 72
    0x2112000402c20a0008030b54056865030206202c4d050301d80c002d0070344044100180d11810628185400c40e44080c1c84000340718680500503429484000980703901650308900044040e07488401581e1607640d940e084034a161600c010040700d0460000b08000c03641c007e50780c00e0300c61625201c0400c1244951080d114080c02d0030700500a0006108a007103003d14400c2007511000d91140d903e040688244140400c00740e0400401400160107034102940d0181c0c045400100f845500e200c0703940005d03500400500500e81303428800040d8030403019004000e1507800100c4043d864580c4000b511141a00b00031400901c500010507001c000000351003084200d1000c0c1d180c9030161659401c182c4429034400b46041d9507c44600c039014400c140a914450000b1003041582d801091030182110084010160148110301d4018040b584038410800d03030000b10f0b41c035119562001410094540f0804c460001e41c00500042c1c04281d01c0d891b40c00c500d000c3c40f13031519040c42c0c68598a16040d103440c0b0110414145078489 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 34975841 1250 34974591 34974607
    0x21070504140a030b040b090d030b012f0a03090501020c0f090105011b0b01090504060605010305100b031005030102070515090604050a03051b03071b081603060c0302090d0302010603030216050105 85
    0xa107110700702a0400402c0c103121950383e0b075503402900404840541c0c00800300c0b0b040140581d000d008040c0c010029240c1041000d0105c0c0000e4403142d140605070448404103959090f0001c105a191886202c0c448119444401c46280081040109000307031401400b0380420034046081c2000d013210140f500030b14000c038a80c03c0800460b8803480154260030313440c448600b10000f140b1881c5d4064043c00e05003402044910b00b6041800c143c4490303901c054101407a000c1044081001c100807032054130051103940da600c2d101c40504043c040c1c0300b030700807583c90751002074410104130001480c1c001c15188140b0140712030750f0b206003040d1502c80c1210003a1050b0452205000024030850007460301002d500100c82c5248004852146190000c0d202102d11039016800004030000886400c0c0042941c1001400b00451400a1440c007560b24800140151340340e6484c4602a4047d4065610405000d05900d03103044081c207000b8064a45072100b94054069076aa490501c98201a513006030369060312171616004107 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 34977091 1250 34975841 34975859
    0x515030f070212070f020a060807051c020c0118060b03030901020703060c0216080a02120601051003020f0d090b250c0206030a0908040603060602010608160b0a0c02040f0221070504 79
    0x4001c020744110b010f0710082114010f103000103441c22902617008000070000c244140300305810b90790045020300c000c0c1001c0003805030344502106c031140d1084000500352905c141c00d8070064040c40340142295401e00355003c150600002040300c045000d01014403140c481a81815100d10507503600e07500503040004140085880ba400240540c0d110384125042e66010f900d1001d081102c6412500d05a0400e00881082d8034000340c8440c51000e602002c2c1a00b03514100c0092010305201e42c8003020705402051000d2100302ca14180e071601240350000344040d055503e88102b01607412510311202c100041a00c030210701400e41181540490340d113507805240a160208401e41e04010114106682c6a041c290005004031015200034072180c2c8001c1645414420060300351403440d08001c040b07078400b02140c0d0b00c968803854114111078001301120354814130708000702c8400d0301404001c1c0d005820046803ca484c40164014480019542c99580e000c00011a000d04501025504500020014403040c002606 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 34978341 1250 34977091 34977121
    0x1080610090305010515030d08060f12011b051309060605180d0f061d0606061e0c010509030414010305040c0510020106031703010306060501090810050601030f1a0a051503 75
    0x2030141400a040e55a942d200ca013960400c0300c03001054140d0544d04030b11801c0404c1501e40c01f20392420164032515201c0e0200c3c410402e01c0c07002e079202d040c0039075560f036603a03100303602c46009445441a0b8008411460001a10b6a03003c10100f1403481440c4000040c3c1040300c3c0304603025103100f0b40e1418030f00390181c072070307205032a031032426055000c0084078140000549100c4400c015030b1040b030000c40d440e80c2118444103800d80034205280c035900080204202965008204d07600359800c801606481e10003080180420300030041411901d6180c5006d1181c0400004085c100711240c0721a0000d6425440004409866040d1001425010b03440707000c1c4014a40b0791300380e017042c1c0f98920000907095542c0c0c4916414500d9040c181030480e40002c014000c0c4030040c09188058242806d040031001d207042001980d80c080d080e402d4904a07a00e00c08074103262705c2130300004401240e4080500231050508507000311200c411812a10503540e2050014190130102c0a115000da0345942c12815940c5084408510348 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 34979591 1250 34978341 34978369
    0x1403040804090b1c0317090c010909020d14040c03200907030b0102100c050304020a05030a0209070302070302011404080d050105040c02030f030c040e09030c21030103030f020a0204020c030901031505010806 90
    0x81004c14054000a0444801080600070307500c2c5006600c20100c0c000d0081c201a05811681d0405980c4080990700006800c00f01c40110600590303d0b00d0381d45158000781180d24401d20700c94480028003080c04800491441649d0242c4080b00c0c160407000c1c1200420f81c00b42080707c1c0c100145000180485019601000159006005642120814a603400e048030a80c2c034200300030a8000c020b000a40c205104040007070001074008240e030f035a845e00000c1c0c840100030310041c00c040d0001003010404d8401c0d00160742ca181081e41c0220241840d00e40044903412014080c003c0c985000d00002e050302e0280900c41e002d412507006145041140224060f49a1004100b40d405075002c1100040314101401c015108050320006180c0758140606964288074011112a4042451144065000c940001200e04403581405d0000342c92030325201c1a41400c02846019501c1440400c0c1d003602801d01000401d0880001d980c01c00c00700900400f5400d844225005160010b01c40c90700003000c5080c1a42c5d400300007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 34980841 1250 34979591 34979599
    0x120209070207030606080106080c040203060102150c16030e0916051614030a050705070f0b090402090102010e010f06060314250c0501020a03150e0609060402032d06011403040804090b 80
    0x3a46030b80310300c4c1c15115143c0c8806a80d079502d0b0010403d004042c0a50034600500310f5081d440c5082c01c0c00000d43e9100c01003042c0d141c41c0303202404905454902001c5070612401c102ca800468141800e01a040506612640d4001c92041c000030b4000003a400b1503002001040d100d0500303107a1400428448142c01c0c0d28101d070390b180148907c1c41a08000c2000d4090094248e503100e40c0d4400604d030141c24000700c0d9101140850761140c040c4000100d40b02911010041079800584600720480101d01400d40c007552075070b0551030507270050490714940d00007000b03584a9032801c0c0102016811000c8a44908a503840746203980011019001b4004030f440c07682a00c0345142c8803041e0091a210744d822030f400311510202103544c0c1c440380610401540601c070020400c00c010000720307203400d502065074510700130400d61003143d00000003250058203024104400400010702e48620b0080c5940364450303041649c065020a00680e14000503c8c015400c691040ba40214080d00305480c00000c0d6024104102400d680 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 34982091 1250 34980841 34980853
    0x170901020705041109010f050c0303010504150504051305120702090f0405010b12061006080103050c011101021c0b0f060c251710050a06120209060a091103040b060a1202090702 77
    0xd03a442d80140c49082c0c8130150056903901c0f4260001d070803102050003c02c2404001d101e9040507020200030349044480548021540740044207a080c24482c16400c640c4d400b0349080140b048820b801049602c1076441001240d0b480c0b00e522150311700c1402130f120020740c040100000586040700c0002705641051140c4e00110350200e0740c2c0300140b9810120300c07009130254005010015068021603440000305002d0400c00019411502ea00ea154030040c9155414008050b50280d0114001d50450f03010300001140c403038210148501003c094940b50320300c07070f00c9001400103510551030b221007162805800c0384014480f04008091680c6000030064000450000d800000500100407007801e010080400c80580080d0f070b11404502e0031168041d008404540c40c044042c024448900820848540c048a05d608180e503800c00160341c03411141c01c01c45aa5040101c18148030780303034a024600441c454802500d2550b1260203008a0740000e01c20f10000d080b0f840010800350805130b120b03d0b0004850320588134 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 34983341 1250 34982091 34982099
    0x61211040e030f0307180b0f0c070509070c021201060b0301051921030206090f100b04021c021201060c02060a050a05132403060b09010509010c05060411011b1709010207 74
    0x100b1600680c054030300401c000400c0009245c3e010a0b0280503c800a0803446503030704003002440680540e00d00c040c0d142e4170005d03811046aa08000700001088018820341861401c1c1d50001e14036030203402c0490240d4515008440c801206001d41401e5860048586056030302e0501000305510304000f0905480340a1600490b8541402521101500c070980c110407003240a13180c0240380c0100100400c020b078202ca200352810082c0441c04c88001c10072144086100da40d458001802886101c5000b003260034540603a1003140d109070041c00140398002119001680e03200000d80c2c0588455800a500100800c90b00211900440241000c0034042c038045042400e02052803200d640d140d00b11702d8008a1461040554800d100d43c40440c0d0142803400340003661a0010329038045c012400c01906204003c940740b94180d205440380701415030044120f50550426090907600500c0d08600c0310700103a5403440c480c081c03224000d104d035900e55100e031900d2440310f12014100c0311070b00282100d5045014040e0002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 34984591 1250 34983341 34983343
    0x110a0201031e0c030504140303060906090a060f030501090605010e01120b07030204050d0c17010c0509090403020c030604060e0106271113060e030c0d030c0803090a0c0602030c0709061211040e 84
    0x40d0f1a45800d45001803141028140031031002c2e0360004141003039004104100a603102c82100701d401c104240e403400b0003030321b901c2d200c803020304110b804c00400c0c0c3c540d00a0002c248001504120015401802c0401c0241d0300d41e000010b80542c00d019404070130305242e42035130014903150240c43d0b0124462500506144e2110006001d10903030801c242c0c0c000041e0b40044c851038014144021499816900800100d60401e0000d8000d01428004030701c2499108002000c1c907000307201e10103c001008042e140390386054502000286074401c4100207561034640c021541c800c40c0214103103a4143d01d90179100038490840d6840c0a00f00700c2c0c8503c0c020100c2400940307400d045000c0200c01400d503e03290030702084030480525240c50955500d0b244140c60301804080425045441003d42ca030704031032413036036036500c500c1c0700d03450400a41802440320030a80c10000d0403d5000c0301500c0c0c1031460030300380c5200d61340c3e840300e0005403500c0b40902400c0c0100c00e107260340020951910032809290207000403502005100b209 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 34985841 1250 34984591 34984601
    0xc011415010809013b15070e0108010302060d0f0b0a062102180111030c0723090103050c060711090405070515040e0105060d020c06090319110a0201031e 67
    0x5808a2500903038440340750b8000820360792214490000b0030a890301e0070001c504041c07407030300d000c401c00c10180303254a51205210101200544ca6100320b941d100342d900020707080003070300302e44210019a03241c611600c158403070000c8030b0480c4c1e0000c080030f0820000c0802840100ba0950701c0780d141d07990b5554410b086031217a0121100401701a1240114014280c80c00580000300c00f100c0038030f5910400c050548285058002d900404084ca0807480d048604030016103103100b80c07900705116120340c1c1c9000031800120142004a4111030500703102450410080c0003007010207000c01401900700e01f0350428541001e0020341080707030060384081860f81118021501c022415a015a039136000502e00740001d092054882c0a07110061444500e00f40c5404010241040d0601410b4402d900c0003609441100e06034041e103002040c8035069034210b040c05030100340c0c2c2c3d40c4070f480c261502c420f0905818460a004400b403c0d299140c1c8006000603440d00d40c011001041c0205900003400f485000200c1c800f62a8424 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 34987091 1250 34985841 34985851
    0x11d01110d02010c0315051c0213090602030103022701030201030c05120a05070f020a051002070609080309060106020f030903120a02010912020607021612060b0a0b0d09120e01050406050c0114 84
    0x1480d840031300300017016503804402e0b40d6481800140100b00e6612100317110b4002009407094040c00444503c00103041007180b401001419061812020a11046500543c1202d01c21583d132136002c44000b82111021288440f00710402035000010805075000e03030091102d100c124980b0600d81a0303e030345100b1040d03809440450100b0780e80e41c1041003040e0441d100032140081f50005103501d4090b50340c0c140d03803010324000364842c054002c038014041002c2a041004082d41c0410880d85914000200c940c0d944401d10840e0018482c1599120050300c02004452050f140038000c1c1c1095030840c1c86050003a440f40082000b159a10000d9001045103105240e55582103980a01014242400000c0c0f800070109400d8001c8200074a04104c0050343c48a42560071307070702075408180f40c07410a0010b900c1c0c3e02d039030b80103111a00000898000703490299000040d01c0b0b03c100e007001d03074003004041c080b0390007680030440c90302240e004c110501107940200c014081c881c2441f8004143c07014403084025a00e1000d8503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 34988341 1250 34987091 34987093
    0xe060405060f10150e040f051005040513060209030a0204020a0c031806050a1b0507180f0b030604171303030f020d2a05010b0a26060105011d01110d02 66
    0x1051004204060140c0394010780c1c1c48a01040904008402005140e0030b4801c810b2072409081d21241180e00940e038000115000038801c21040ca0107101c6040542001c650540790300c40003078004129860309101d51030080880b0809600311500c543d582030001d501682c81140c2c184100c1c1ca1080044e600c50000b40040c85d00303039071810824175151a01034a0035001255400b80c0d051001021301201e5840010344a5400051400ca00021001100807400f40704e905400381c02800b81401c0400c1541040601ca9a484a0341d1800c011b403616110001e0105c031403544106916400080c04500412868503504541c4d40700e00741d010389042c1003d10407800011903940700b00c02183c0340f600d801d10b030160148031441540c1a20b041c0221a503070303041d0b081304448036810301102c05407904001038000d00c10258002140c0b4807002e0001041e031a112201501100c07001155848060a402e03801e000d03102d0302083e440d0403100706850700c4142003912030030070020b00ca4980a0504000700020341c0c3c4c6104c1000c101c02804918690 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 34989591 1250 34988341 34988353
    0x9060b0406080718020702010804023c1c0203030a0c020a090f1d010515060f04030b01080304030516030c0b07060e0a0f02040b0a0501021005090309090412030c030605060313060204090e 81
    0x1c20013000c004403002005964500c18006d950250760800070003a803241d4112080010300c841d9810007600e55944900004055407039440400404031407249101d40b107201152004000200c1429803056440320b0071000350150800d1244100c50743c040d56001540d14030042240260320b407035605200440725030030640005c25803a40c1c0d150079805954090314035410f449030028007852401c16811408115490300640c0208800510344040060340d1056801669122200c0c2d402544d440d100700b030340c94000c1d00081d04c0d640200c01000340c40342480c0c81000d080300d030711244100841c0e2404600c03040c0c5800110007a00d20940f44c4140c00c1c992641406194030191040c0c4030440c0c10b407602d006101c00c403103800460901030130702c205090225a13000104006a103407028000308180d918220500e0071070190103617250b04071008030306020400c8507150074040c0c207800e41c1c0e50801c441103000b9021820388140f4414244c000104101085190460b070140016041c02404054905540c2c0c0d03508004607040d11142d505950004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 34990841 1250 34989591 34989599
    0xe030c03030a060e04051c180303090e010e0717040303060513020a03050105060a050412050a020307030302030a1707091e0e1e01120b180106080307080703170709050409060b04060807 80
    0xc1c0c82101d0140038032044c419014640b07541e4060740e86182d40450f0007041c0032101c6004040c3c2c4528040c00c04400c3d83c0546000c503d645c0e01e40a0104652030140c82e4400c280c03600003050b0040d008a8171446418503035900c101801042c1900c0090710000b902c142c04040e19000c002c1102c0e26603813204042c20440500060307545d084084c00404490068100912400c0f0802c10109950707842400e46050b5241d800e0500d010010a15000303292442c4403030020f406026495000090640101c0a1300e0741c0440307900e1300c642d9406400402c40e10024212000c8001c518881c8081c00010000c10340040c00901580c4801c00303080d02e030040b2409000c0304a648006800900301421a060301c229007250041c24803450748074855055564280355040020021040c0e42041d140c5820b0889007504182e005040e00010303203030b8440b500e040c0100140d010300780680101d181010492980034100b0451031142e0a5603403a20415801c0c9002c22002d040c62900540300161030300b03254200303991280301c0c4400415280000b414050b00d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 34992091 1250 34990841 34990861
    0xc05010e01020c0303090609010e03060f010321020619020c011b03060b04080601270204150905090603070315020c03030a0b010e06070b0f06060408030a0c02030601051002030409020d0e030c0303 85
    0x124500d1a045400000071000360b40c4000094500200007103035407545035080940101c9401280064542d45485000b0a01913003503401207509050b40e006401c6d200c0c100c02400d400180c0c0c200d842034100010b030700140000e104010b1703541d480c1007208130107003026140a642050443c25501d0a0501810440a031b8094640698043c0324000042c0a1000d016092502e4100c280d03132501c0052140000c409202400c403403196003500c52156202003020700840d280e640b50654005041076a00081003c9900c40401055901d08003811520440000f0000e00440e0300f03541e6a07084007181104140e21081c0c0900008800c07e106001640c81003d290000085512481d8001032508189100031400707103000304990340220b040610400e510148840b0062401d0721408007250103442150f00641e4580004a6050000c0394011a101185d5000b14100d50259888008100b0010f5103d404c150140e442000100400e00c03e98000d01030f030b5148010000b0b50010018001401d44e8444894480b6035017002041182d0084 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 34993341 1250 34992091 34992107
    0xc0d170105011701050d08310914071202040909050c04060608010605030106180906060309020a091e0f11030f0103051605062d1303050606030604050a120207050d0c0501 74
    0x40e09281080841507500d040f25500324040c0209809550125424818004d4480c101c841c449842d070300102140403a40d6107542c0c00001d4104044031070942000c001a640d1075801040702c03c050800c00c1d03416030b403640c14050b0364416241019001c026002c0c480003e25030304c0c500c00c60b11198012030240010008002c01c000846070355070804000c1c040f81c41c00610405a006050702d040d5040380c10148110b810041e032001d46a212944407810080c1080c0000c60741c1681034000640c220f00c2920610b0b2495100d40240081d01d0842441c0c100740103031040c0070b40840410740c0100c80000d40e641c3e0700184c0c003100100d13443c64552044034000514180031004204005040082c40128250107150a080d2410980080c0040c880c1c58400003144011800c00701585041d000d1852603004920246995851600c81c50b0b014030310540720035035903030007564005421810081501c9110310742c0103001d0700350040d1683d074110700c018007440300d1400c5100764580403615480d99201c1c645040d006408090301c4602e0180010013041c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 34994591 1250 34993341 34993349
    0x709181e091101050a12020d060938060c010507030203060306010f0f06050307030b1011070506070f0f0c08060901090204050603030702031b04020f0708092e03020307050c0d1701 78
    0x1072074200c814002c00ea01c0e50404550002c2468642d554030f100d42402c55180101000ba40c200620014030441d0b201c2c0198010811201c0c440818001c04042c140b01e051074909440c054940c030f840100d242c08034556401d541460401c402401c59040a040070000360843c0c1c1c0c00c03100840826400003e03c000b505e000c1100c1401005080c0320810824141940c650201b41188107400c24400d01101080e1814000c0c2c03c000b01072640603055481650b14110000c0458012101d9034045004240c8082250704180d012244603940100d8195010820341d9184a02414580702c10b44400300a1000881c17400f0003444010f000d6800b0900100340c0810600401c1b044950240c4810320961040083c0c900584010520300b0350b108a513544100c040464401040103881103003145610725000046030000c1109500207000f640c0000ea40f006218100e2441851410b1406d040e02081002c04d0003050221920a800641d40b0850510b807950801291021641ca42865120800c022800c2c010301c0344041d0072140169170040c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 34995841 1250 34994591 34994651
    0x50705041d03070201050307091212080115140c0a0510020408071203080612071508011502031e0f13080109030806040b10031a0a081b03030f0301050405070918 70
    0x4030364844074641c1c0c0744074011000f4144240800080c40850040d410000144510540c102d003c0406181c103072581e0303d00e400094046a80310300042170041800906402c044010785031342800b200c0c41c481190090304a0010001643b240594003000502d0078041d11340c0400003c08096115030800f48101c1c2030100c40c4c0c00c03c01103907200c1070f400c802095014088541102d03054680f021286c541e1b04559003070040b160044940040300012899000b03502910150485440d644001f80c010081102283c8074411040e564040c411502c0503e0212510b0030010883c06e025000b0700c2e031503c102d04c038414800d913140b64031441059540b481c004040c140c000b01e045512550494080141c9001f040020b085246a614801c0c205660f51200d1402d40f40c00c0200b5500b58500104601680703a0f03a55047d60b40c50444074207a11860f4041900e0288506002050314442e03006190841d0442c2c0c200001e20000300130050503081040000c000005002038009210030b440400c0d9076007c40e403030390380c000400f40a6424201c14000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 34997091 1250 34995841 34995881
    0x807082404020103050603100204080d020c0a080c060c0309090703090203010b042a20010c1403040b041e060c0302180105070b0406050402010c060203010801090c0902030925080a05070504 82
    0xa0898003030306640d4041c0d424200003070192922000300386020040c448490b0136920000700400e4400000a5600070580607a0803504590340d8801401081c5059218030f406036840682d000c00785282c89400381c440603039410200d03800c1807110350018a40ca0015514400400c3d0f85003a4901982020700075a00501c0381038405200d294240390385e8009500021202d030181c140c0d48140070010b1486240c3c0c00c80ca10034070780e51202c458903d018085d4000c100c20020100401c1c0503c04201074042d1032000e41340310341c1d0400d1904055a540e6100c0c0c0c0c200d0407110301d03140c2c0442142c0513440001581e5105440b0f00480650700140c40782c0000c0c184880d4000e90410941c14000c00b0b02801000130325001199500c0303903110101081607200e0303200690b141c107524100105038500100c0041000b00f015072101c0c460601a081c141c0210740d88034031a400707c1c80305a8164090360480341c100d080c46810106030108100c0c000c045032440e50b0b5229020390500d90f00c00c0089820b900000703c10000b501c6e150082103e030582d43c40300c1e041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 34998341 1250 34997091 34997143
    0x30f02010c120f0e0105010e0a0506010c11010507060e0303070c1403090a03020d08090603090115090507120905031b06010e0115270e070507050d0305090a030503040c03060204080708 80
    0x811500080d15020240c9a0040000503100fa800602004c55644024455561141000e00c41400308484c845000c42c81c101c005111980305440c014401c0e500183d5850461440800440da10740c402001690140c0e21410892900d0000700001d41c0300d45482d641c2e60072240000d14003128807102902000030681c1c410310960b48039a07644036802c3c2c2100d904555a0008206910b0a10240c0c09a04003059021300c000c0104486401d06400548000c042c40e141000004d844158002c103d4a00351224000140c0401141c0e0a01e080c59009003c02070103041181c1c200500712000b4000b50b41444c454800c6034204000402c1140c0314510240d01602c541c46010f00c4040101d50000d00115421603080b4409048042d010800394000c9504030280c8003400194817245040000a40f5550021340112540e10a02007a0010760b4807074410b0f103002d108001c0145c006071140da14222403036000548299103148030000000005a0b1074401400180003000103080070900d841e24441c109180c10b455480001b80302075800d0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 34999591 1250 34998341 34998347
    0xa09050306011d040c0b070503040f080303010608060d0c03051c0806100f0f0903020a0e0106080a1104151101090c050a060201090b0109091e030201150801020408060a0b0625030f02010c 81
    0x11100a40c10800804135500c0781460302d03e038041d941c00803810440000e82c00062190110040c0191000700e440e4501103581c41006541c0ca110034440c4900050645012400b60700d040403464000354040e107400000c450300c2e901e0b1203082c0302010354032000030f01d03240001d000029044001a07600420440c1c504400c5c090b01c12000c0c250400c082d0400c0104090f0340a20742546015220400c080c42d005000c0004268940043d44015002030052101007000400000c807045001d00400d2071001c0c2d030f00c881c1ca04062800c16480d40710f095603c8a10b0611032003204105059009200c0d48019601845050001d6460310050141144c1282c00020869041513861008101c0a200f072a0448a4045001a44012500f8007805401d4401e250202c21030345e082d100710074107905400450201010340702241c4025521103c1a01300d2103907102d01c011a41042c000140103240e141e00841008401412252500301030000c1004981ca261040007600c41100e80c02600340740d4031514803034154405000800c8030003001c4c1c40107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 35000841 1250 34999591 34999619
    0x303040803180a030b0a050f0108010b0d030f091805061c0302060f060105070b0a0e07050111061504060b07080408150f150102070801020a02010b040c18030b04060207080307050a0905030601 83
    0xc5412403150000719070b00c0e101c43c200d10000b50b402813544001c605214401d0009410150b5a0500055020300003003404441803241e0520b4040050401055074825038080d100a201d807201202440b100d1980002c0e8040d80b045e01044009940e1000591407a0180400a0b410704180000e1b0031961440d03031180c0000d8001415035081801c91440760815540e000c012500da100e0058001e10400f0b102c014408080c105030440a01d644d99141650b808036200d00044a4003080c2d42d10449440c0d010f1804901d0000300301603506132051028101144403500d0b000c40500a03403001408403021103001408004c054028050040c2000b05601c003000c46040201c0ca2258106000d001c40d00e8203c452142070b10581e00811140004100f079800940d110490b002019008112803001940164100807200302d41610503030440c3c2030f0006d0207617a00c48290440c1c03200001448010000c5440640c04c000a00224070380c5406980305d6515aa43d841d901e00c0c400400034211001544080c2c040d501000050002901d083c000c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 35002091 1250 35000841 35000857
    0xc0a09030b09010605060d0e0f030c0a08090f060a090303020105010915031202100c020d090b1e2212060b18060d03050d06080d02160b18030c040507030b030c0303040803 74
    0x12040b80c8820465a005202683c041caa00010000700494095026040981c0d80a1141c09448000040b80200c6489100341050090701360004405a000a00028007900300a88054a0441e08209210105500da446041c0d4400880d00300d880030000c240c2e09002d444e014010400341403068004964110b0b10700c0c00c1c1404000c00030b04e803052034000658070811444824180108080c4880c01c400000a5114030b81c200081c000284070382000b1600124583c1291021710a0550b003109620a214078032065030404c031080700048048003c103003011000316584401400000040456031051850003008071242c0780d20a50103192a40c045004003c80c6400295000030151450140030060b890f0480780352103448901c0903c14a480c9010500184c0060130362554181d036021564401151504c0466944807845034403014a4108030020b065400314040c00305008005e4103c070b2200b81d0703040c0002d060751012a480d0000a603240d000054500e410480c600d82c005090340030303600c0d0170304180d0341d42e1f01e82c496014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 35003341 1250 35002091 35002103
    0x20705100b040f090803061003020304080d050709150801210201020606060904020c06040b0105181501050d020f03070c05010c0512040209090a0503070515071e08070e03100e060c0a0903 81
    0x1c041d84242d103564105030020351440004000100306803400c204181c005840090081e06030f2001420307054064800c403030155400100700c03070528440004103400740c08005c00c0d0200b0000801c00019100d2a51010389a94919a45800c0065810003114203040740f040a80700d01e056060209a80240c2d0300031030320030341091060b141c8641c0c80d295100810040e1150303080c0504144169820002031020004034503058500484a184040701c614014030104202510540144d03042800c10782c0d030f41c3d0b008000074000c4c02c42086015003080800003884a0982044400b200400c0130031400b0b0041140078840c104009500c0d00741503080c0307a0240c1403181c246d080184002d0244203d0b80104052440c2007081d4100280c0c0302c0120b0ba510320b00ea02c0c01c0c40e01d90300c8245c0d4001145800c200800c0d822405188045403003d41e220380511014030101d0f0440d0381c141d0242904051080d01403d20302181c600340300b1111801d006200102d144800e60741440d18102d8020300c05090310900303010400c04140d100303401c1c40032260440 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 35004591 1250 35003341 35003351
    0x140a08060a05131406010302070c060302030901091202150123060d060b0712090906060503060409020406090e071a0301080c010f0302130303121803051b01150603140a02070510 77
    0x10021420440198108541c0f00e07602c030700040202c042d940c01c0180141484840508070381c039140c0040d0181d01071124000c141e961403000901c0710b079100781e0155038841c0fa000004554030f070b02d6032521a4a45119a46000141c00884080c40541040c40c0c80c540184580010402615041c84201c0150404031070781d14801c102c0050120b50f03140c0e45030011805005d03226100396580c089481c2168841040c44181c00c04122023180000f000e8009100d0030080f01c059403509469a5114001c00009106d001383c220ba0007507880ca400715010406200c1c0001c0440311034020325410341007201400e176948004d5560b030640d042c02c02c01807101000210304c2c54600c0100303081410380094011000d801030b0158402d0030400131100da100006241c1c1c0b0000641000075100010410303800442a07a00000d0700e0008042c0c08180c0400920468050502040d0218200e26000044401c18100c0503071611030309138403c0b000240c56100103400718500c09011038010782807601c114038050042e5661501c1f1a07402c1c03e0b403d4125074070307 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 35005841 1250 35004591 35004601
    0xb010518091e0a08030a0c090f0806041514040606050f0603131b030510020310060203070c0501120209030609030702040b010906020c04420f0b040308030405010608030703030219140a08 81
    0xf04070010902d680001c0d9192680f030b0250f480d900920201a01070000742d41400005294500c0307000003416169000c0103070125a503680c96916031407240c82c0c00b04001943d21100704ea007100c0300e038280c41e01a62048038046102c514010801c074680403503840f03040c49a6410400c4c0500300d42c42a4540c1300c256400340743d40740010107c81185d0724200c0b02e644068418023412000315500300196005600c00c02061070490345480c0c41e000200d07034038002c1d040000d00c000f24078503044c000c2c0d60140c002800400808000545061080c1c4082414608141d850b03090503840810301d10708500c0c050048075100702c000c1ca07186c11042e1078188000d654228401070b544c080da9030748010355002c40360002001d0340000007818420340410304040e040c2d50038901e61140c104e071103813800c008100d070a01c000b10070085444280006040c40d003140c560360303070650000e04100d130b1940d86e4590000e00e080b42840a0202103009840058498403454083c1c0c1c1d041d48080c2c0c10004001d40e039083c03401b26100d400d081d00c100d001c2c0d030b1915034419519 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 35007091 1250 35005841 35005843
    0xf0507180803040e15030304080a02180906061915020106090b0409031b0f0b040503030403080901020901051e07320706080a0e070e091b030a021c060b09040b010518091e 74
    0x1010b46499051f0000003000f1800300304c0010010f040340e00c02d554000c00316010314070741d0704451000d5821050300d8001c00c01094070752a000700c505680c05480046800415079414441c03210000c941ca80d0000340c0d468200400480090303209031070140c0c0050b2014420000c103590020b050301000108070240f005508501e8003405039011910b40c5082d400040401c190419050140e40c94008a60850000d19a100010b40c07a21040c02514500b00061310f4560424004078044200714140750640c0c29282c00910031032001c20480891080384c00c28501c40940042c005101c600321091000c100300020b54000c03901081031b580d2004603280d100d4040700d40000c041da0100c82070740c1410ba165200784000364901003400800c500c00300d008203082c15070841d0240903540203001d00d44c40fa083d40002940c000c00511a600c2403800183e1132003940c1d07108103000149086940002403101c1000d46055680444140041c019418081e601443c400342c1805190585d14000342100e83c2c4410480c080f45e00030000d07602e2881e0f0703254 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 35008341 1250 35007091 35007121
    0xc04050a030b0108010c09030302060601050a0513060504030311030418020d0b0414060f0f030303070809190f0308010509060f0f04110f030a0b010f091412010f0507180803040e 77
    0x1006000100d003a81d28100080450300038000c004039546440ca4800c02c80c3d016a402c01c007204e40c5034014007a00e5540c00c0054a854101c4020700061140812080744810340151020002e00200d4a40030340b41c81c19400c1c0103100181100440c1a2580100028440b0158201000c10207041a9a002d40c0d40c000c2131140b4000b030144074030501c0d086400c00403007100c241d4032411894401c00b820345609507040052420020030401c400586c0380c03d81c2080001c51966803041440390703400000f180c101c2d01c2c10f00212030350803100440d098042e1455201501d504042540c440c00c400d0040000300d0740310510341444c900013003d4502d450026031003120240ea40e03155503101d9821111800500a01043c1c0f030300703100011980b20b503204403429150140b802d40d800007550b0141800a13a41c076456582c400c105420b01c5685802588072031205d5074407015108603054131a20074003031040c240c045610b0110f0b103410907050180c004124107500412190f00203a00f03010303603000003065400b00c9540100c80f0303140362100c08015503211 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 35009591 1250 35008341 35008349
    0x61b0904090320070f031509020a120210050903031602010e060a0c05010506030a05030703030203070c15020705010b0301020301060c030509040204050604030507141009090e100e07050f04020702090606030c04 91
    0x3824415000103058001c02c400700c0d02d05840028643c4050724601d001d4440415000b2061001c140120600106a0720807030f4850300980210000350481d07050300094628004c542c880d07450000d078183c10008500b032142024005032110f0411504248054000940341e0040007d0100c0b880c04050600d0156031154220a8520030007400c46650b8004c03030b4000400c1e01243e800c0580d015030a000204510382400101000b100ba08a000703181001080c0c1e60440184d8030181039070040000b003d4019000c2801d044071412032036135070100181d0741d03225490002e080d42e051822480c0700341d205000401640b50428528010b1541c10b03c2d10b1a541e1804500007002406107801250f04000e01250110401c24006064025107004401c14552011940d00f0008105490044e403400520b040c5410440c4100039045a52004142c4080d685150402d6902d502210490724180680781d0104408001c1400d01020361848c0e45c50a0b83c00390324150950300411801c40000d840107005010010000348500c00e084240e0b0701030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 35010841 1250 35009591 35009599
    0x80402060a1701060f030e06070c08070f080a080906160509150f040b0903070807052d03060f0601030606080c0307081801110405010e060309070b0d020d150602070605070302061b09 79
    0x10f541c41c0d1400a040313044901d18032021a1030300c1c0003140410f8001a44610a40c190340d038081104080342c0ea59500e54210607400c0396403031300c0c440d1030038006040706024181c49015692008954076040e0b10301441c000c409440e40c00408405d900800300740e0352220440b5030000d0161a004080d4041d50001c07000b07413180d540000154803000c680441c4908a900c010407948204402301d82c40c090701c0c4c08540340c40340c9480c840c883c2c2c007030100844036008120382c10050748011462403004200c110f1000c086428a40100d810030a001540c1d01040a0396805221b02006003076586494509032528244901151001401e403005000c40600004c0d42c04080310b441c520000d441000034810050f592003500c945810038014180464082d00c110300190800f003065910441d0050010f001e21860115000c903268060310000e50000e40030030503402c002c20180503807400030440d0000d00e43c0041c84c080d4000d00b4400d02e50403040c1001001c00801000c2a400580e139078212050968141c40b50955458242103489086030aa400c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 35012091 1250 35010841 35010887
    0x15040905061f060f0c0c12030e0301050a09080714240405010b01030b0d060905030f1c050105010203120f0c070b150a0f1a070c08010207080c1204030201080402060a 72
    0x10414040303612401880e007440d031485080000380c0000301d0b0b0000307401040005119500c4441d00b1038420544030392190300810500101303648500440500b400b0781a8141c0102d00305810b240c07080d09091062550003030406034100f081d0400395540700c0a03072080000292201d00344903013130030480c0300a20a44503000c3c406000041228160141c00744000d81c219015107840d4a400c4000205500078010440c2001c00103204051010842c1d89100c000e0802c89400c0d1542d110030b10a060105102c8401081010231044810040c508041d01e56819640140c00590454100344000400c0d00c5640500c0e0b0f8200c0d0204900b04403e944034294041c0d030b80280c10018145d41c40880a00403002c00c00340d4a81120142035860b010f0054562988031065034a0b40320350320784494104c8150f640303d0f40c160058a841e43c445c0c0b494030043c0356104a51403d81e08500f0703081d2251880002c107a10320f42c0c010002812548441c0d810a420b040c950b4001810205000300f02134025040064039141d818450b40d101a12aa812400421 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 35013341 1250 35012091 35012093
    0x9120309181008060105061902010b120a02040b040b0913030203091c0614070203040b0901090b0a020f1005040510020306010e03010c1e0819020906040b0d050a1a01020c0108150409 79
    0x2080341c1d055941c01d01680d04403101083d40700000c079180b8142d80000d04030b1b52500e00401e41d00c0e40600d8491005074115542c07400a01d4040d91340112070701c0308c0c110880062010422900400c022160100403640c40380d2f1134a0209416620340e00072813640704922440f01d4090807820b090590440c450400c2566000880d500442050400b402120310414025a410030820411a91400ea40b150a84146015a1040c40104481e078500170003044102818035184c20b525554507040041908540035072009600400e090641301e4104101c1c0860701400d000c0c007070043d4107041d04c5058807043e900314030119080d00040000c1403039008429a012406001e4002c0000903903500c0001d104050255800c01c2d4103108400980c0c2c0d40d44102c0c1c103d40100b40040402d84010004c603a600b000b94002c4035040d4100300c0a01c030000b443e030030400c094005480291408201468a04c0281048619408074448804c040e2110f500159130300140032150380ba001e007014045078481c144503000c48030107480c00c10351190800740901c2c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 35014591 1250 35013341 35013379
    0x1e03090d17061c0503070308010e07051804051003020a09020c16031a10051309051011120402010915031b0c030f0c0c0f06091403030301081902010302070b090c0a05010203040b09120309 81
    0x24100d45128210110320744561800b00c2e40d506c2420300359680c9208403700d03440315141c0b0b94011500102c80c914540c00441d500e90128101402a07841025644c1d404511210104000e1001e080700c04d0004c40c0c40c0644600f19600c24080709088440903040d0711501c0e0008030000032070814500540700c0103206c40c03d115040c0d00001c0c05003c5000e802c403101e0140c00b810017031002c010b0194003140701c040c1c09030303c0c2819404404a00c400ca8001c10584c1001020b21001810a064855009140349103503800b01e50b000194002680800c4520441410841106d0303e880200342d00c44020701c0036400b946840440800300303042c600d0100781c15411504401c03040007400610a0f4100d8030613412104003491001d8035410a00426031603000034450f0a4803908080a124104001c3d8020403107110300c141401414148140c0710003040c1c8000f116890110351200c0176404d00313807400360035100060000348021071405040001ca1011400341c02c0a040c02031075428a81956030320148240e61484001408451101240e02d40403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 35015841 1250 35014591 35014607
    0xb060c010f0b011b02060d020f120703060819080306010903080f0c060a0204030b0c070f0506041a1623040314060f010b1206060903031e03090d17061c05030703 70
    0x2210780c052411010b080c45502506810081d80c4404030392048520041d000e00034990300a02c10002880e41c20041c00392a8011400500640c0c0207a40f0b80b0190340c5045200074040f5030030381d0031109030b07075020301030150b1080360101d8000106944410b0450b00da40300ca600688611070140c200030300d121000715030740c401c41d51150b014002c105500802c4030710f5511521490380482c444c5000191040c2e105100007904600403000900b080d81c440e904544d000b103035607150740b410080c040d41e0481d40041d194101400d6560032840698008155000c83d03040d0000440001d8150900480804c2c1c42040e140714840c0e601041000341c50013960402c5220b160040503000082d102e040c1203032a4401000110008035001c0318035425601030001d0a121a801c1e9201c080c00c01910350442c0b05c003540d0600c410000401c00052403400c0c105403aa602180680303a04081810030f08015001c0b05100810840a00c0380c4140191041d2540d0000401e07101c40c40101d905450a500d5141c2a180c0a071683c80002021001c0591003809 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 35017091 1250 35015841 35015861
    0x231309051f02180a03020303090609010203040f0b040306060602010507020c091306051806090712020103150312020703020405070e0109030b04020114030f0a0b0d05031206030705030706050706060e06060d050a0b060c01 95
    0x41c03102e41070301c200315413038070140400ba41580c000d21543c0642d04080c0000c288041d41401240e040540e42e1030014441d502581220f03400c02c0001c50100f04000300c03801100013404540c00280040e240c038500095484100d001164416031691020aa144040c200283d45032034218600b485546419070740741c00060008040b4400612a800010f000c0103004544402030355451282d07800200c80503001100680107100d084824002e0250000000980b100321107507411006030098148180703940104170031214001c24140c140214a403044142c0e0380c0c011040b0040d40d911000006c1c0b01c0d125400101c07450918002e018492510000c14080550310040c01d8510400e00170800b4000b05a00c41c0038030001120688004000c4d03401403204a440354401080d250707100c0300203021a0305150f611400a40341c0fa1585e441000800c10000c0c0d59014442207004072401381c6071100c1e50058904204d800b08070036100c0d1054050075280c1d11070104002180d940c01900c0518801840c943d266551202102d00920f55500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 35018341 1250 35017091 35017117
    0x100203090d09050307140103020d090b090c010305010f0605180406170f01090b0105011b0c0b12010504050903091003020909010b030a0c03060b030106030e030702060f04231309051f02 80
    0x41901d03aa103224052440680b480a4041c12186182040209080110b002d040e814180c09010f10000c95200384030314500c8502900514020b030401409075428040c1140320300b410036091100500040c1c0c0c9214105c400c8604500c2c00550350300e2421201c0740480d140010413944503060280004041c0b101148046600b0b201509541640344a03040c52802c955110038020000d400b15001013040b0343c003400b0700d44545803a2030700c0201c21440e9035807400b5440529030400e554000000c90b0b22060107070840291809881c094904000509000c100e181c3e90307000b0316080ba441040c01c07040403042ca9210383c050300c1900c000502020750b256140c00d02010b403500100c0703e08088910300b5048000140c442e0141e00100d40c0400c40440c5103900b4180304402800c1c080d10b003040244820012100107032074120040c08801a2000c08036104c0e801c051408420510741d010545480d042400c02c85503d40c1c03940c01005080066010004081d40a1301c0c0450401c42d140d03151524424902d41d44034440308040c2c004000d4400204 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 35019591 1250 35018341 35018353
    0x606210c0905040c120201110106060801060207060e03060f04030c050a08040303030b090403081f030c0905010f050307061407151404061b08130602090d050729030402091810020309 79
    0x246140102c0c0d0301101c0240c908401144104900107443e10b00c9001c050044c58101e010208083c01d0700c1c2580c1c0260722107c000b43d6803200406c0010f41c14003c4501030800c41c50400310f044250340029543c4c580c00350a001c0030001081c080703003c00d1f029850003480c40d40d004050b54a045141e041a00c2950854030007500424100113440a1504d4003001141c4240d6140d2140141505c0c3c42a40c41400d92410080d9002c01c4040f09000c40440c3c240040c800003044d00c690301080c190f0402a1042c806203155102a00030307030084100784a03464105140d807070580410500d9988411040c01c0811070300c101c114070569100c3c907040e00d82c00302145084d0700b035100c0c50007a081031114a402030074458018103d40c0401e00010000000300c2c010508080c0c1d18484140150340141c01c01031440005071600902e00c4007280c6503071061804001d8281d10300822654014104003140306101c5d040d01203482c038400200001d200c0c00c0100001810003520301c40100321801c0900464a40c1d0010b419544000d41c402d8810322028801d01c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 35020841 1250 35019591 35019599
    0x4080601050604031e060b060c01053909010207090219140405010207140402190504060801080319030b01141c0e03030c0a050d0603020303340503040b070606210c 71
    0xb25040700c0403139501c83c0312203d196064000c21001d9100d1107108848458443e2882011541c07044040c003005144440000f51074240400510b2511010100d030400c4c40100512002c44c8100e805542c90401ca080340b4684e640d081200c0040b800c0c2001c03504009081c510200e00e040c0c822017030030142001002e030303912240e0744010300702041c83e41801a481001c5c01603010180a203d1541d55550079031100c030000d0000b44c10101c640c9141d0200424407a001340000c1c2c2d021604100c620f0b40b2460301401000203402035881c080740118100d100707014001410302070545590134100d02c0c0c0d01c05c0307110613036100321112540d032901781201c0302d0507400030348002e020201d0f03084c126445099000131040f60b0055200064140c0b40125640d020390711a0080c0c0006d000079655540c00201584090008160780c01c3c1c441d050100d140410b020b010fa251001440b80030b60070380c0466007100091400401c40e02540c0b903d0011036203498482c6849130140c04580c101444501d6404002400c5218603042590214490352407409500e031a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 35022091 1250 35020841 35020849
    0x3010c03090803060105090a03051b090a0507020d0c050f0601080705030706170609090f0106030b07090e06090103030815060c0d020d0216030b06010c061a03010e0a05030d020d0b0a0b0408060105 85
    0x1107038030251076900c0820200d502580240c0c001e0060000141086190607a41c0d1140c1d07040520244c1013404540d55441302c0500e0b4030304200190340c0131014120070042e500b00342c00001c0d51482d40c0380c0a4010321014040610a0040c01c00c000041207075290222407656855098060b114140ea02c00c0a01900c0b882c2c2012807118014080034440084000540c882070792101e0400c81d01c82000f42c014000c9004401801d06424028001c40c1d01441c05041c0b06212410840310091881949510a1500b440c80005004003a80c1e01100641140d40620f031170040c0b03440704d01c0c041800a01c04600c16912080000d4140c00544003c103034811010100d40a8507641e140604080c0d8a600442d0a00241244502801c0c000501c1d100b9200c4e81004062412822404081c2d5a80048400e0002d0748880d44803041010205480d0034090806510105405054600082e6440301d680740503100341001320300e40100720803513040d40940c004c008415006160402199807102c500c032aa84c07003802002d0700d500071580041010300b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 35023341 1250 35022091 35022101
    0xb070507050a1a070c1703060105040b07030518040203010815180d020f01060b0c19050c0904030c060f020a050a030b0418030f030c021b0f010215010b120618060114090a0e0603010c03 80
    0x2e000100034506c40d403502c801d8106680b005121070b05100381407001040c10b00900f07024058191107034803080da4601c0302c0808000048848000c035841303a401000184040c070804900e000400903070300c1511800361100d041e0304403150184414100a403081070841c869071070380011000301107100d00d0000c0111a4a03004078080c688102c0e12000d0143e40b0909807064049080071801e07103014090030a480165401c90005188040180c40070b40000d408403402c3d00030b0000c144102742c0f140740d10a104502e013103441100035100e4041d1080342d0090550f1240f000c555600c690b0400c001c10f136240002541651001d280180501b80b64041660010b07280104180d005800015070a0718424168002e80c041030095040140045001c052076045006820443c0f20103c0315440b0380d4040c0c00300b20b00c016152189141e0b0000540002000b9a104a0001402c01d07002d5036403030707406c1c1d401101c00e1811489a100b4100c03410340c103120350180c2d907030041c500e180009076900e6416050b9000d802c2c128000d005002046404a0a440d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 35024591 1250 35023341 35023343
    0x9050313090e01060f060819020313021816030906090f050105100e010602030304080a02031b100f0203010b030a0510150201020702011b05072607030503090108011e030b070507050a1a070c 82
    0x10035084801c0c006d1034010540594418142c00440d080004401c1e402d0013a0f820550740e000e08084090218411458090002e4070010303088000c0050910340200c00459002171070840c24103144d42e404a030400d021301500441000f507041210f61f45910390501e8028000e0038111040c40b000a8030110200c0c0418490302c2042c1261420307802107046880301d80300d0400543c002100d08080d4801001208400304200b840c0000d000640d0018241128050b100403040d60f1800c80c0b6466241e204100510944000b841a00e41012603078100060303c3e501c0509100300c0100035008002c0f414480d514588200f9815001405018801c0e60303040b11002c00d041c44102d0500d42840c0080ca9034101041c1480790500c5c6004640351a10f0321101179030346000351490182444469001556540c00c000f4a030348203960068143d81c01043c5550f40940080c6ea50002102c0d406c0550200070045601100030400c028400d5056802407070300001611040015883c108000c2030380b000d4050b208161039000241440d005405001000e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 35025841 1250 35024591 35024609
    0x30106031a091605090606160f02120106180b03010e070b030103020f04050106020a06050702011d03130e0402100e0103021c021b0c010c021c0b07170a090309120609050313090e0106 79
    0x160781001c2c100900c2110043c1042c1e0000000c2c0200c41d18000e007120030707400035802740020035514081401031001c42001d101010036141e0401008010600603000700f80d0311000c01800008143c02d81c000001e000d0120320300e02c07091510802401260701221140118100c9108981c8482c500301d0100910060318024031078440507030844041ca2000c603805400c02c40c0e001c0224800001c041030100845201000ca8600200e82640041403034850303140c0900410004d03050030700d00b5102c9031800342d00044251200301c0c141400c2020068000d40c10340d020b034040e40c0d54080040d1159450891030401400207400145000440c507180b090500e02c4001c001c2010b0b1104801079490100242c000d400b80019815001c00461006103000f920601140c00d007120315000d40310035500c0c0a03100d40300707150f410180c3d0f401500b200046458008494002608181550b0488049100141c0c1c07a482c00d050800003020010b401400300c4c0400a0104001c21230312044206440c03004404014200040321128221a0280501011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 35027091 1250 35025841 35025883
    0x40b10050702030a021e04050f06031f020408120a080a05191509020304060203060a0602030a020703060506060903010e01020901022b0305190c08100909030909020a0c02030106031a09 80
    0x1005100d0001007402600140c100c03450340c04681d02180714603120781080590090484092400c52802c1c0c01000d0700070843d48164006401d15000113500c501108001c241c09125841e51100142ca198041e40d0041c00142c0544a038492026102d021551200c1e240a00091036240010107228061090b24054103456501110021003100080010300245800c18030100100c040041c0c040c0c0c0170300046100301d214240158690802e50244060b440c207507081801075400920026150560005810040781d1308400041940c1c1c07140004203446104050485402d5400d00141d039050314015001801701d64000c1c9c0c22140e0109501e001010b0450740010b4000805810b4802d40c2490b6129030403181d084440d00c2d520f00b00d03200500300f81c502164002301c80400030510440c208242d01c03c0b0340d202e540007030100100600040840b41e07801000182280260341d0100c0e03010542a03501882182c0e802000c0343c0c090003c001e07070f80d140c0c20000f81030034a03000b46c18648030034a030002e24400c80c04503920b21105100d03034404003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 35028341 1250 35027091 35027119
    0x70305070e0f090d081504060302040203270a03080f07090803070507060207080d02190303061d040b0a05070e040903090f0b040801060504020906030f06060f0712030c0503100b03090111040609060e040b 88
    0x50500e03105506d00c0d403003034030b921000c0b0140e61240300460040f80610f03081c46007101072510701c08a181100c1c3c1e103030601d9040407040001094000785400d40c03141c20482d100d4001d0341c07004000d0710080f41c1034114521078440070034010100314001a80000780d99030394088a0394550b581c0030807952010103242040050300b11042c02c1d001c81d000c82c0000034000d4424100455601d1715501e002d02240f080c120000405e540d88824401404000d1042035003085a4050030700061420400203884800c40281050056990701c2000303062520444040340904190302190460552b1090890000e803c140201c0302d45519107000010a1b180a00c21a000020050802d6066035110703101c001c0b054000a202c5134011508001c0c001514402c2ca000b000c46d28400c0080034045645d141009046480c25020754040c071070100700340045240c12611000440310818030043c0c1d01da07151a506070141c604072150001046010a0104200360403000100580b80c02d9a1000341800744c04040106403400107501c00d8004151190202d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 35029591 1250 35028341 35028361
    0x605030d0903060905100c0906030506060a171b03100303020115030b04080d110f03010312030b09060607081c0605090a05010b1b0114090c04060801061a0309070305070e0f090d08 78
    0x625894060702c250b400082400d40c90300b00355840d042480e000920004020b00c4012b070540301e16904054251140c9007420000080500140e8002d148d55122246c000f001520b0107021a44c1c03403600380c3c01000b000d034982c00d02c00c054040c80009030000b01c0265081843d00060030030380190701d03401c807a000304030103a0549841e100d80d07920354013406022980d980c40d4030148882c900341000420b620710182268992b40e6245007001202c048001028800b05820410034400301d036039441e48550091030440310990b6512607464800713220b12548100b02c076002e00181079180040d849a000200315441500c5000851341c0b424440d81c100c8009010782c110f100000e00a0304601c02d8003840303140c81c1c00541c03800001da005200302d410f818284106e805518075844044440250704050041c0001004000d000b8407026052400c00300180c100114501e05a540c01f100007a1108020480701b0001c40d08501992320782c3d500c0c1c02960940400c12100403400b44000740100b8444400020147c0b840340344c564a000640c1c071804800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 35030841 1250 35029591 35029601
    0x31b0705120403030207090f05060a1401030b090405060402030708030c06010614070501050a0c0914010207140a050a030609061103012114030c03180a0605070308060a0b07050309040605030d090306 86
    0x16580c500c20701d03103085454800e86005102540c0070740c008045d0b15140035410300c161940702910035001e9007041c05125954035440800d1003a55201207404800300c1c101401200103080c0e9480e030680c00b80c0f0400510080c04000700301320340554000e40035600201d032140d410b6503503481400402d508550020004000c4503214621801c2c95409000603e46828115207400e400d445090340d0f182c1a4560f0780d03009101480e00500c44000800e16035091134500039203000040e40760340c2c00b40304843d0094072214002d8040c1d07032781303841c01009000c00404d50313240c40c2e403a0b08150009008405045480c1481d00701d03035414221012040d01e04950701c0a0442c56050b03000301e07034184984d180c1c4004580f851152188441d04110600c0030300169511030004540f01e104411110601c08030010445c0d003d10304e842818440345501c0022a846940c041c20015400c0e1500780108464807040d40c0414500d80300030906100b00701c1d01000400500c0401c6405110182d00d4204150b240c6000c2610f4501050701244100700048080e041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 35032091 1250 35030841 35030843
    0xc0d0203040608160e120615010f0207031b08030c030301080c190504091a070c050c0409030806100c17041d0f1b0408011404050706020c010c03200d050408010e03031b07 74
    0x20707001d40c174180c00481c0360340e0039015029602c2e8020408000040f600e061244e40404c4092800e00b13001003040e0b001035214545070002401758440e142e01005c545a044203454000d0680400700c941e5110451302e140e849810038000c100c6a4000c000c01c0c45064a4013101046c03042c0d054940b510310781c9182c4020007000f49002c81080355480414000240200e51110940388034450a1700c0740d059241c01468400e0905500302c15041c4160310b01101c4070042980001155840308060b50340441400030500701351070762664040c00a0400c44080c0080b42ea416000c4050000c45040d014902035018a8070b040d400c5030361045400c81c6801d4001000a00151011203e607182079144d2000546001e803100c02c0b081c00e50f4440204840656191400e00c010405d0400c41c44000740050700c090010710403002c000a00030b2400002c003808006100704190007140c0030140d280510040d1804540d8822060603001d8440d80052046281a5181c24080d40c50a14040102c901c1030a642e000728221428000d40c424543d082650 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 35033341 1250 35032091 35032097
    0x41e080d0f0b0a0e060f040911010309020d060e0c120f0d120914010203070f09030b0f06060c030c06090708010603080403080c0313060e0907090602060a0c030b06040603020c0d020304060816 83
    0x71250308542c41d181c1c8001c0c003425442003445400d2604505000001c046c407003409000e10f107042c00d450302207210302550704283c00303007483d0124010006000055441c4071110000d45668501401c04944880c00104c0040e03888042d90400c01000c418140c0c43e031104d00c0500151030315000011401480c0d031241c0c5413100110400800004c0c0c45009032540142c0200c01405106180e5002052000c0c1d01d400207024091554245000021a4215561101d18003401b5149003022030076140440c9603640c52030700b5a044000360108480e2224102c002c1c06aa509051fa81d038030050147c1c80340810200010301401007620f402c600010f107018616039841c0100d03400110003d000d80000d003d40c0740c943d2500c445140c0100516501d91800c56182d00030844621000342c4400305004e00b40c0400c20040350040b03001c940c001091039001a03802803008054002d0b012840055504c410001804101560198003403c0a4aa00300407a0074000c9400816a600c4c07190f4003030701c4081902800001c2c502070101c92070304c2c000c410038a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 35034591 1250 35033341 35033351
    0xc06010515070303050c161104050c04120305070618050c0a090606170402120607120609090b01050409060e0d05040303080a0501060905060d020d110c01050f0f061e0303030708041e080d0f 82
    0x5c00c04081e420416800b00c81c0740c8c0e02100d0b505014513003402866001012030010a140919200208070602602100201404000714044080c402e031075000d400d0f8107280300b0303603040c8102c12807900d640c8501050314000d00c1940045404244444144100300544030151101000b0dc00000e40e039000c2c4000041040707902c00f03000100408107440610480d805007800d03440c1e408a444003031707141c44156080c5800103121390745818402c801040705030340c0306c034110f41d800e8a001803100c1250a0801c00b40081846000152044544450245611000410450b030003592120442d448035412042640c0d020710890b0001480398009108078504040201034203406604014600288500001d068490500c40c07001c582e080480c0080c2c1c00d02c001e000d07032130b07114000280c8650245410021060110009003402e0700a44d170ba610300010754446070752049841c0030018201e0380c6901d0445401440b01704112402c40d42c0c88040444114641d800b21401c030401c0347e100f40441d00b00481a185103004000c0c420841c0b0085e504d0b4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 35035841 1250 35034591 35034607
    0xe0409021203070302010e0d030207020303190c0b010e06041508060103020603072c15070203060a0e01090f110f01020f030d0504080904020d06050405090706050d0903031b050c06010515070303050c 86
    0x300700070043d4902c65000802c84a10010a0701c0c280b1903001c000b001410b004200b42c0c0010b03038001c0101d44241202d41c1d280703488072640d29012108280300800c001e00c039464210020526214100d0341d9845942c1c22141407280d92155800d0001e244280d01c00c500d0564045401440140f030604091503000442d490400d0404442d02108590002c12511a00344075001c01c0c150021410050024540d03104594230240c5006844d6001c43c0e40d80100800d400403142e45c034144413a80b0a0290000c0c001a070300111400c1a200660401c1043c0190403548503114407843c80404215500204070202e501ca000f1010350305211034503846070050300b4000c00c2100c0c04541001200c0c0d86070342d14030181c20100c980d240c00144880c02c1c50306101c101c600142c003044059001c10401c02a4581c80360456203821464070b0080360089403450150042d00800132808641ca0030f401481258a5218010344408a5030302c08886407079a07146c0034040c0c3c0e01c005074200c42e0309120801c020008070f8040c1e00034580000841c60403501d40303521 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 35037091 1250 35035841 35035843
    0x40606111902060f0406170604060303050a0305040201200318030115150c020904110301110c0703060216061d010f0b090402060a0903170c060603061003030804050709021b0d0305070e04090212 84
    0xa0f0000c0c0045450340b17103040900724030007d01075813004098800b003203458251b45025107d07002390100c0900301a101c0000508592050018400382041056250200700700344007041c0d03ca802c02c0a0707001082c10002100e40c09403405001d0414101941c3c8604005641800407180c84044103d1940c0c1c140122501d5100040c1c4420345241e1095024501c20260ba5091074101402c0d00c00401440158030700500400e45210347c0490000d0849912440c010f070744040c44080f0302204400c07030320003a00a901d00900600d03460740c0380052203810360300c2c2402008081480c0700a1021207c94612054000003601c000900508140000b0072080c03400c1d00381000749581c4c0340d4031001130302e803006843e0803881130208028807681020031104c4e401000440190045152100420f0791414151201408000c0e00f07401040c1403110a101d0000540600001590b0320364076250246035600b401d12903032655104400c3c035280118484d11403280a031515642c0e175100d0b5040842004040c19090710140c7e0b00201c0c1000d030300d000c0c101c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 35038341 1250 35037091 35037097
    0x7081303080d06080c190510021c02010b01090e240f03060406320a0908190903021302070c031104020903061302040b03120a080c2502040606111902060f 67
    0x9410304003c5070990a1482250401001490441c0510b0403250031120319480300762050140d07601904c0c4001704140e8114124600f1203101010307031800088070070840c40c056041d00846010300080e2a40d610040d92591143c1c1804000c81d40c80c60a488424116818043c2c001003039180e0000007000c107202c450100001034103002040da4210360a41c0e541000030210524000d510031030510000400802d58180c181850701144001c001100c42aa47c214420402c0b000078103450f00c202c03584d000200e801c00f505001501c0700d1903a020691060303101d81c200401c0081d183c02111110360f4001d080b0b0115600c0c40d61004042c01c80b43d03041c90b80c0b26400780025013050b20204035203846210700c032008c0c04d03014030300740103010488421030003950280d003090641003014804c0400301c0e907054482d4900350a040c1d580c0000150300d0302600b41c840020106001c14500480007030007000307000794001c490410681d55500b07070540342081030300f281c09080d40204413148a20b807504801440f0380c5001602c4185400300c01101c856441d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 35039591 1250 35038341 35038357
    0xa030e0d0c0c140102100b01021c020601050405010e0112121e030b0901050306070512060a0b0a0c11030c01090b0d021605030406030c020309090619082d010606050708130308 76
    0x1948420540050000009a10b0000d002080d1124480d02503100000e4441c034a881e482c3c80120344480c0320100c541d20030031070001c0005008100c403010348000b903002900c852003032040d140b0481c10200041000071502500c5812140142034541d4070b0110b40d56200104000c0d1150a400d020002e1001c90069200d04004c58040c00d1680e0001446a043d608112140a041e00814040e034030000402c94025089422284d15070400304401041c2c0d9908000a010201c035034020340b00014000c14550400d94010000c0d0315807130f1080800c10f80700d42c0a0800d040da200d00281001e80054502d0038104500c03a2170700020141090181405803030b002d80d6190000c1400668134040f81e007039100003400c100d8940c1c11321803600c04c444103101940c60324130320200149106074003402040c030a00d40c04c481050b4020f404540c4400918007481550107a0504203480c00080034500c9109240340f100c90b0604001090600c100d200f501c5d07003500c0342070404a0b183c4815070313513401c0201900c200042e00039001c80414000c8010302048 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 35040841 1250 35039591 35039597
    0x60f0902070303060e160c11060d0b0405060409081b010b03010606020f0609060705030105060315091603110702060f0f070f0b0a0b180105040203070c0b040f0b011203140a030e0d 78
    0x24107910301d40141110110b074002c040c0703800203900780000e0a00001291101c19071500d402c094508050801443c80c8c5001d01a61f1350180000070b41c05200f240d1500000b0210504a80c2040356645103410b00c0140e810803840142589010003400c0030030355119005c4465551940300000380408480046421140c1540110707000d0791001d9420041d1a2040140542c0304100704003802c1107040480024000d404103003d01c030310841c404070000d50281f091403034038854424001c3c404a182c1c1020b003104480e20044030252000213003400d800810307403000c2c007044450103640035107042c1c03401c0100340c030f17840b800d030098101200a00410840c1d880031803c203464a01925020b602403440504100c03412804440400c030180e400b4a1a021060a00e0603619000324119032081d0750250303403a0765095040761505503461004004e140510309110510171140d15112036107103d582500d030303143d889500c1b01e02c1c100d910120040c0050060701000035140e0540c00901180d107900e00700401c400701c01941c1c042c24071035104803007400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 35042091 1250 35040841 35040847
    0x10609060e0a061508010902070f05030a0816020d0206060906030705060d0e06070806330403061d010209030601090e030f030f06010807210203150a1508150d0b0703060f0902 76
    0x7002d410b43c414400140000144684e614035181c82c050309080051081960713032a404070304c1c070050004115000540a6200c01900c0ea503810034076010b4000790701591105460070440074504020342c000291580d40708001d070001e2040b80e54a100f0401c940e84002c100c0c0b90136000d04800015036489080c06407500300711240020644405004a240c034000b0300900110400140005210160311403c101c48594413000008003283c1c1d005902c1007102c4804504030000c507001c0043e0000500485034092000c00ca0a008442c203480131804c941c0c0c1c00d174081e4900141d4560040341c0100050702140c0e201d0309802614000381c034200341c0c00c0c210442d101e40080711a05400c0d0106800c011003580e2140b132869103c1c241d404e01d4401e0b6006e401711130310140800d02a11442c10b074000007140c0d410103520134174515a64010018041d40b61944c12202c04065414a0b40c030215048a010072705540306400e040200040180107045480b030103071201808000003500c42010f041d650000400d03102e01200c00d241c090a000c92000d80d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 35043341 1250 35042091 35042101
    0x603100f06170618010e1506040b04080712170c071509050301150e071206080a140d140706050402060c0607020606030f0328140301030b0609060f0310050702010609060e 74
    0x110884014800751042c84d1841d40c40241100c1020a5410344490071342100440d07864503500d4004c59160008958080720100d000174100c00c58070010015100010140c2d080c031665001e035080c4a100f02c0c8030041c0814008807000d0f00c4005c0da82c001d0a10039400008880c884da03070310314500c000c0142c00030030000040c0c1400c0f801d001900b000d0060035480700070440341c0300e61149049080c041048019010208224042030b0080078015a90007800c041e1003400162500594145401040c040c0703100380c80b41050040501500d4040c0c0070b00d981c80032a074050075000b0b20f070903030b039541e80d00c0100341c0200200c3c0c3c00034050001030003030720b0b04000c05442000c1507001000c0c02c1c145030301014641300100d420203801e58402c0081c01c44a03000810314101500001100b2818142070302c0081d41c1e6501e05000800054402100010500c03404440c2d041c00758030140e07201c68094a41c3c009220400c4488405580c0651120035403103003c0240e5072056074001c0b0140300000c1c4064445c51140284ca140303501c09040e804103201801 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 35044591 1250 35043341 35043377
    0x912070302031c06050f0303070201020a021e12070303030c0207080a02040c20010501030c08190b070504051206100501050a0503070825050c0105070302040305211201080a030908030a0c020603100f06 87
    0x243c01b040045006500b0b120040c1d0000b5a144039280000f405043c04000d04600c882001009800c07201005220400044101900c81c1c0c0d80c04042c070040d0f001070308042d40c2440007400420031109955040b4090851803400303409100c05405c81e160940c0800010b48014000d014606125448107a0810300209465140d42860b291b2040c01e43c001500540291150243c100807600d8021152a07002c402c00c641545d50620544d0079000e198492034203d4481c10805888040200d50b0380d00c01c0351500d142c8520b10342c4420044900380260701e0224003081041000c42e0740303580a03280003584030000301700c065042c000080c440041d25003115004801710303c020845440d0ba40003800b801e644019540343c01c50170545103488070381c1c0e6207170413082e2a9600250a0300c1c0f1100112540704841c80d46a104001d5900b03569510350039a07940c1404801580011081e03200490b809501200f154410501561006481070340c0e0b4081000650001d440c01c500c02044e14400154000d406510300c00a180c581c0f2824901000c6050301 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 35045841 1250 35044591 35044609
    0xc060604020a0c0b060a08010e03041a0405093d030b0a11030402010c081215100212090411040510021f060e041502120405070602150912070302031c0605 67
    0x1548030300c1c0140645202c1c140d00c003641e500501c0d0044818041c5071074003070101718480641d8001d0b10855007030080d20390000d40004000c0c800c0b1128401c403000603c02208072080c0318007841c09002c0c1d1014405002c98044c4803a0391505111100b514441d4580358544201c1c000303601c002c81000407a01d01c80720000c10600c210703111610341c000110401480594045040a006e071712008100905001071a003016060101680c29920400c180210b40d9174641040c0b11034042c11540404200c1c80ba00c502c030348000c0d0523403000c10715076608410781d400300c0c0c100b45401c41048003a2030347e00c18600309440c0034000000c15964649a0160113546034014250080e08001510584e1149888025096040c6541000055012a0307410380c4550004d02d502104805d00322268041e10401e4113100f8041c884006000601201285000459800ba001c0341c0040c0349243d524900c401040381d1003040394101000b080c0e1094071260007030000621901c1502d2610710190f1503039064207201c03c001000c42e0365a8006200078280381c118 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 35047091 1250 35045841 35045851
    0xc1009060e030c060d021606020301090203061c03020706030c0e0901030606090b150403080d090203030a2708060c0702030a0507080102030702010f0e061b0903010f090203011a09010605070302030904020309030c06 93
    0xe800b1114010000c1140c0b4403c0303010317018540350b00180721080c50f00c0c60500f194280d54012415507a82d42c0d070b401030703001030740007039a12034401d0444250360896007040e00d4940542c2c50f0b240e0013901896107010010350082c8168400700c410b00032503c0180c46c8581d00c014019028511980303000800c00d050030b404404644c44552000e0282036801095a048508c800940381140e6200904e141c0d41c0a080040901508210400941500c00401c2d21640300f03811010050403c110449a1020100100e203800e00c0c11455210b913005540120f00401d02e5000700340020100c050000e000c1314014805a6075032480c3c24000d030320424071a540032081c403140d6035083c041c44498001c56101482001c03500400240c0790480607001480000700ca40100804800f034600340c2c0c2403c90024003c010902804150b6809022400d2040384254a00b04040d030844149000031020b00c0c1e0050040c5c103d84e801c0250569295200107400c0e41588000e020704011503441d0f000035441000ca04015580303400380c8040c990310f011000340c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 35048341 1250 35047091 35047093
    0x203030402130507030b040606030c0e01080c0a03020d020c03070506090d17011401030902060c031c020708070803071206030804170f0c060906130e061807080402040209030c1009060e03 81
    0x600c00540e4035802c411040800100300041c2e5912402d40507001041c1010503950454200000003075001c1d019481a40407482e07644880040319138040044801c00011601e031079100340709100075151184aa030240035a036100000042c580345462119031b2031a0042c68007103420f82c0c011410800141b10a00051185440505150055841c1a0651107440005010b12008040d00201400c8540e110350803110f102da402504403942c40c0310500b000c5071a03600501d0500c1c800103400c0c142e8401c90803540b08484060307800c00a03403401d106c0d0990703d0718001d500190801c4104443c800c075650014120344114001544103125040d5900d143ca07100c2d0b01c420300008035000b05a00418002503051601141035030103c1c1d011a00070f980c480c032a0000843d11300038421505d50300301d1107140100b00031011550150040354100c9041c01401e000c1458038081a5007181d075600081c079820045001420290060f00069030000c080d00c8801c982200460a44c405501e851000601150707003c026568100c0301060344003134160 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 35049591 1250 35048341 35048347
    0x201020c030405040903020a0f030509040c110606060a0507050f0d080903070f110310020c010204080f07030305090405060d02090f07090501030e0a1401020f030109060e0106030b1e030c12010504120203 88
    0x99801e407a802684105406180c590580c401054424082c8220465000c492010a0a2a030034018000e4001c8035200d40500d14014614082500440c1e0300b1009a25540082025580303101c1407150a13000080c07003009004040c030042000440030701141c908107444200070185042118401020340002801020840d0020004400421a6a04013000964104520f0401e400310100482c0c0390000c0c61091222003840401d584400c1c80303041d0002c2c41101c01c440c00b20780a40303105044050b00c0d44643d00c0001c0100f88204625152030515803c0184d01c010020180303508a0b005401080100c8011540c5140d2004194104a106508034814802a0100707180400104288084455884a04c1034000d007080592000a41070741c0400d4045641418402e01c110f82c41e0359603042e40340040c018900030803800c103182800110f801403003403250000000300141395a050004240103a8040c11110340069018007a80340c60240580765402c04d104607580302000024503103454213050000340d007003480c000b0454200b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 35050841 1250 35049591 35049607
    0x9060f020f07020409020f04150302120d08160302041508071707090303080603011d151e0c07020d02280b03010e0403121401060c0519031202071e05070312020102 71
    0x58420340c2d40c1c066054600040700300c0d09000080c4152500c02400b58402c0c24640c140e000c0140d1418440212482600d0b5446042410103034661201d030007099640002c2d07e9840040e10004440c100c00c490b01d0344509005103410340300c20194041c81080b80c503500100d00c29009007d5003e5100b100300c0210280650301d40070700d0400520003044000e92f03100103000c02150b00003048041e034003948080e1401c10341c041c1d500c0341d0041860301c41e85c540004c40700004504070741c50001140314403440200400042038900c0c20703002d03030b680e86088002038110b280300b6070b04641c1c0201141c005807a05105998074805e8603000c0e0b48110045484180c5002a640240018580500041110004410605801ca5818140705801c4000000e880e4000c0880200c403814040e0703060000181381f5080480300080034000d00c155000344401c04001e200c0c2c0000644010006551420b2480100c0c405130f01800a140c0310f51100d04c8100e040c0c89190001080d03034041940c042e004004100100040e1507131410000709540000d50502e052 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 35052091 1250 35050841 35050867
    0x60e010e090a020708040509040b0412080709061101140c0c01060501030605062b0504030f08090d020c060c0c03030c0705030f070f0905190c0c0209072f0703050a050109060f02 77
    0x40508000d440b6600458a00d040241a1065601904014142216500d0b00d810544240d09058606403542c112104155803058410f59045100e044903442e080b607410702c4c1c09000c13a45918100c510f03e4880d542c5500f447c8568a46802c0c9500401400071402e4981181c00843c0e0300710707011680158103152402c8001c2220b0b84901c01034420005054040d502d511349005620f20080b003a402c1c07500348540c41e2008100c101508560102d042e98800c0e42c0d0f4840700c4d6200042c1503a0740c614044500003507489000420043c0c41c090008190048100c010348000810800c003003403031500300c02c281c68604c3d00044405e00c51800c0400041c400d048000000344480e40ca00090300d64410821700841306469101c1000074100c0041c0000001302c1c210340d00003000310696802c801084100c002d50220300c11254000800c40745c40c070071900b89582d400740d803083d07201241d0f14407200030f5030341c0a40410340d5460207150000004030b8028031003c0d00b241e01030030001c18002c106103090800c80d019030070b40c007641078814400c600603c81 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 35053341 1250 35052091 35052109
    0x10b0406090e0a0603021002010c0e06071e15060f0510020607050f0a02031c0203040605010e0106020d0e031203070c0b0604050c0406080a091b0905060f091311060a09060e010e 77
    0x9901c03000001c1c0d5483d0701d40300703002a00442d000a50860b00c1145100da5941d4150300001210391079a450040130502041040040d20810502070804800c4c40041100e03c0181c805c1c90030124490381540032801e41c1c0b60070076070030780e003d9034407004190100410400041c2410030400503000c9051000e407405180c0400041c3c000c4c003c900400c0b1046c0d1000c211aa405802042201d544a240e5010500796a4085031190b019510171034040b10558202000000c80c0e2180c0c1303001505944030360300600b45154192408803400d0b00e20644180d40361241ca5150048401c6031001140106081e545100c0d040b0b00e141001100c031a40039001e18011464070040103e580005001d40301036514519244801da01d4000300c0b80f010f0060068040c15901d84001c2892a081c11481590200d5090315014800c60b0b96007020084140b80e010001c1ba004a05040040d9181200b00b49000102d40b01e40040f111008070003011403a5900400c050801244111509020045c1c002102d100134800928115070311940000214003004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 35054591 1250 35053341 35053349
    0x3120403080c0d0f050403021902060901120209060301140102070807080705090a0e010501091d0c0d06050702030c0d02030405091303090605130308070c09180b01050907140703080f010b040609 84
    0x41203800101e000300c40944102d43e50703856998002d002490119000300010f200680d4204c01511880f25440b13400340c1c0e40c900012920390020007050510001400658071124259180901c6580c2000f5000da5581d47c003001d14041e2100c4c2a0701c45140c1991400640740c80030300d07000000c00c0d6000c0642000342c06d03000100401558410341c4d521410740c0740d0440c10320252814003901c003503c1d402c5c4800440d40482c00e9000200300351041440040080d524004907440f40380328414242c01103e42c2861034041042070704265080046441104d140c1003041d50110709144c0d2480c1c42c0e50040e08002001c0100740b811646141e04641d0040880e03030142c1d0295405000100180300c0c080c00d01a02061040c4c01d50f07940e80d1808000d6421441c0c40342d0380d04e01882e00301380160041c083d88903003a14000441c10100c45516004845650068030780c0d6069090104010480c00000c14540820000b00344000848001070050443c0612a0b100e8000c0e03400c001c0400d140001f07058100c15403c03001400104096540034103510112 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 35055841 1250 35054591 35054597
    0x20f031e090a03031e050403020a0203070f05062a07062102030c0909220305030f0a0b0a0603050907090207060b0a21060902060705011b120902370f0302090903120403 73
    0x360b1503140c4a5458055014001c51715245080c0812040c15008145800654800c400b9100e0554803a01c40103a03c00c0c0c2d9024032504124107200e004000140100400302220f18a503174020012001c00c0701c1803804000e6040321001a01440c2801000040c202580018401c0c6600c154194a000034040107140510b00b8041d225035000d00100d003810b290a8070070098003015000c419001c04e514140500640e100f902c41482c41d42224000480c5603400d0710550340c00c42c0009004c6030b5494a4048200d002c1c00004d01036803081c2c010300c0000210280c01388020040e0900c07840c0040350b40003a0200b0024004130503840703040701d40d1400217040001c0b405100d00403251940041e00050260160021403058041d4101c014003035840e00390114244465119801c200c001150f480d454114140c2c041d0340296070072058002d41000c545050760b6498a0a0352180c11500c1c036100380000f003d04d80d80d806240d0f644142d0301001000c4942e40040c02035040040c0d1031030f446807100c2c005629100081d02032a5800400034000740070 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 35057091 1250 35055841 35055851
    0x80304030503060f030304091d0703031418100306060f0c03210905010c08180703051b03010e0106090c030c140a11030c07060201060e07020d020606040e0709020f031e090a0303 77
    0x2030f03990f900316021a42c0b80054101c0c0d817640e03200d0362600001c19000311305202d5500313000504a100007000036124150781d81955104100741d41e41c10030000542107243c03451303e104801d00700c04006890b07003521910b009080e940c0c04a54180f6144000d480c0007285800e203c00c21020380380541c00b0075080002d13010009118107000c08a000d01e40714000080c6404800140351303508141c1c42c2070741c90364481400307405280290803c0019111100b070440e984c0030750f0b100081c5075800c62104003600c210101000501d055000e400030400d200000c10040c01c460032500714094483d62503800300e01d0964503119510a1080e54205422009486064003105000b4032001d04200300111200341484202402a10b110441d40c0c2c00310b42c1d0007034a40102074064201c0740500d059450300c000020fa500d038400121000840615006001e494607028180000b4000d01c2488907114131034240001040d440c81d2000301141c50301a8840c5441e4207048504001381c0100030041940c50300c0441c02d011704240082401c5402075414200050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 35058341 1250 35057091 35057101
    0x70905010e060c0304030c030611040612050618090f0d0e1509040b060c0601032607112202130609030503180d080705101508070314030705030f04150309080304030503 73
    0x314841c950740f1078a540004580001003201c0d603408078095910540080c802004000c2e440ca50a00543c860800095614080303521302003200e9000a4105601400c0c0040144500098001500c8251602d01643e84040d0014a011005004c070700c2e0b00002a1404c2442060500001440c80d000ca107623943c0d2500c00065140b995682d6607101201c040c3e4041d180e035464403410322603180c481e94244820740d440c414141c0484141c803102039580fa2201801c52546041102070f03200c00152040b0055025003041070940081c0341191300b25008030000c1c81a08002da0b4071214020016010059030740590184140400c0900000d10044203860754a258880e454012400680010702c81c40f54540c4003505551001079040c060002c00303d0b94503401c9070512400e01c200e0000500d11004200c2c01c1c0301e0041c640c2c0188005100082c1e0158107002d0300b0608200716410071541d40c03030307203410755220b144004041c110001d003c02020103075680792030000806040400501c0b00540322154240f0000f07100504200300003000031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 35059591 1250 35058341 35058349
    0x302040f0609050c04150206100306020a0e040e030a030e060709060f02031312110108040b070c0807020a090914030301060906050702030f0d0203090a24030902060705010c080a0f05070905010e 84
    0x6000301031000b001d011608110a544d00f066009000d190107110b11444100c80041c00050305500030340ba0b14801c80743c120318540f1040025045500c08404211b18544540c41030350356401480c092a03100e201031a40d80d001c088020381104c14020300110550486820042d03403540041c0010102c0e030741420181311046056004a00750310a80c28220042c6407034840100d080c540e05000108200d00c1510400070306104200150344070401150000c01c80c00358200041c2c40315110f04e900c0341c400352103100c216042021a500080d800e16080d04500c4410780e0703640420050100b00d0030041c0d081441600614919418020700406242d210700403c4240700c5c000403c5411510104500c0007021280c405443c0d41d980300380c0000b52694000c0c803045200d20746801c0f022030700072806c1480307030250f511501014100551890060f07000d00a4204217991014080c4a0040400e4080c040d000101ca5683e5a0400303900d04006c50030220313410044810f1045d45407604221010380c02c00c400e0801e60701c003402c1c1940c038440300da4001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 35060841 1250 35059591 35059601
    0x3080f0918010303020105010e0a020c0a02061c0e0c03070e0907091d0f011a01050c061b070f052112060108040503040902120412030509030a0c020d0231060b040302040f 74
    0x603801801c0080000141603042d801103043c0c0e800b030700c0305095030748038aa5201c09038010b070800b00f0b00c141c0140760031100518240008010030b041d00802c81c085481c0b1080d2510481d200ea410009598100741c1c0030481500d010b110110241940701820f00d600d0900015259076020f0500494013840c0d0383d000d4010b41d034007000f0a0b28841d400303804100c450400008400501805050070540004801c20341c0c207050960044089e6407482c2100002015607aa480c0e041d45038a0b16004403860360204100602c40120310140013582c2d005024100820f0100034035002d024151014803908800303450140491b4003480603200703116810000910344890a42c40e241000ca05622940d4040c003244ea1000480729580c40102c00030b1449240505030407606145c072400d0650603100c0031164941a1741081140e105e409000b2000d00080b2400981480411003407503021500520741c00c1d018001d000481110b064240d00c018034685c2c0e10081c20381c402d20406103000303150502e074000da010081c400c079100c54200c3d0b80400c03e9400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 35062091 1250 35060841 35060869
    0x3150112050a02040e0307020108091f05060f0301020408150105010302120429070905011b03050319020708041202040b030106060503070f050705070f0501081503031b010e150105040c0903080f09 85
    0xb0055402d902d05c400350790342d01c2103208a0100701c1c07040000390780312008244203d1159031070040701c1503c01c1044118005000052000d580715641e808091980e860900c060800f4181c0b40d8000d11580810100701e00c1c41560580c000d604050040001e0b4084001007801950010b9200d00420b142d03022884100ba206213000069202ea05440400c0000c641d52040401c4104c8200b030329500f400034681034000c03083e007a48020207004100b00b000894500000b444113014290070600340141080203540d6040b40c0b03640700e5400381d40d4040c900350150b0150b107880c4c401c610010400b10000c11079281740c13400142c917600004018030140444404002d25581c001e1040f6038078207130302c80250b42800d034440412101820031801520300040f900800160341040d000d000c0c1e401c0302001801517041000d00c1c0c0350802500c1030100b80340400d540380e0800600c0d80000300078842c0750701c420b6070f0f41c292690305040074402164115007140301000410b603400c1000c00d43e680104c4010704d40c5005619666960352010070031b20302a1540c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 35063341 1250 35062091 35062099
    0x4063b040f110a1b0b06090402180a060e13020307030303050c04180e0f032503051b01050105040c0201090803040803060d1203020304020a0f0302010509130e0a1505010503150112050a02 81
    0x180054604600c0041c1154403890702c84c1d07100c907103110383c84020304400c0c441c0050100100402044440c58102c05059003c0c0c40107000340445d402e2040444010402502d000c45581e4a460044c445000b100941c0b50380040000403605401d50f041c0c000036901c244a20015050541d620080b8100c0095201100c0141c42c0d01d04415840d001108002802482e165000c2d245602809141200380540401103e101030503032002e926822010441401d03100141d50000c0307041c01000c010650010f030a01d81109001000c0074000a00d030341c9404188426158440c03448011a403400707030340b5000160b942003620307040b58100030400d807245d030340c1d4003c40d407034009019003d07000d4640004124844e0390300d90001e5118510035070342c102d4130395030f604404682c075030203404000d01040083c00303044018180803000b040c800750f3f070441c0030503083c80300c0d01e000c0d080140c410f00c1540c03a00c60b91241d00800060601035640100303000d0b401440c01e001c051301440c0403580706000b2112440501c05c45902400410000071034a0ba800030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 35064591 1250 35063341 35063351
    0xf0807051b03030402090f061e01030207060509010509060a050106020d1d09010b0307090e04020a0e0a090c060903050111040506041503110f0306090f06030c040222030804063b040f 79
    0x11034010780e42d403c04c480407441070f180f407800124400306c3e0074403203030103680b0181c1204081c0c0d8810741030210f40510b460300b507410150300740141c0c2c0114080340500d90254240ca400055039041c0181200c2c00d141000b4102004181810010001c9990025010070401480d14010524050140ea03100f507074001c2c0c9829941c000020000850800007a02c005d600a0429440743c0320159510040e00d5000d01c0c084030302a51103105400c04000c51001c0710030b8a5401103105038000341c40a06076840921030f510b00d420140006821181c00e10412000b40305c0c0c0c6218031307a50742000342003034501000201d4a00c2180116810081d0f104441d5003003502035000a6000c1e00f03d07001107034907420440d12120b49900304503407542c4502e0342c1d0004107040212842040c1c1c050a03002c1c003d00259510307501480044c2d030190321501800380e80021081c1011901c1034003100514440c000c80c03540d0750300e44280100322030080143d03507800c01e1410f0011401615142c54040301002c50b41c1092403a4002d40300001e000307150006100040a00344 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 35065841 1250 35064591 35064637
    0x1030c050c12040609060e030709020306120703050d030b0303090904031b061109010f0c05120c15040b1e1006230c0d11070b0909060a03080c010203060307150f080705 73
    0x2c44054001d032416940c90460481d62100e0031200203101e0402160581c104401c24171004110b034000b141d00440c0907002c0d0f0020740c28554903924200007540160340c030350045400c81c0c030b0b290f92500542c030400f001100214100f003c03c500050350080003400c020184120440145204121150740b40c100a030080f00401155081600b0110181c2c044480e8500040846049040c0c0c00e00442200c64220707040001000c022030b8840308600c0c0f641c400190f00c4418402c18907100a45201c05004902c1503119201190346814031074801c258103c0c101e445855100360b43c90400032aa0311101d021011242d4901d044043c004034101090040c0050f4079a40071403040c00075205901000001317501c40220300035031b070716640c0707507000105240c9404584c0500c0841c4c0c5d004000140407464101d14440d04454001e0100b080180d50313554100d85513010b029a01c1d550794020040103142d10303044c0080802085808111242c030a401400103000286070504c00007031045020100744024498415a0850315241403200780305014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 35067091 1250 35065841 35065873
    0x30c02060d06060f0302030c0a11070807080109150b01020d120212040503030f0a18080d0b04020406090f080c0612070207030206160b0105030f0309060a0c0b010914060f060901030c050c 81
    0x2e8050103010071108500c0c40c0c0301601c01c0c07003164032445801540b80d00b0454506021118080c0181d16000144100b15010903183d0040c00048001c0c2107050001480881e18503011290762900070000b140980341802c42c10060b6004508100b82056514098100f410284a0303107001380504260341010440030406c0000708240080298082c009141c0700e01e10a6131080c03101401c0d103004401c0d20071152000048800020f03410300207040e11544c0c2c0800815034074000c1000c0b600300d800a610003000100c05510401c8006080c4d55602e002d80f8400b405000d41c42058000701e510703407058040c10403c01c1048000202e00520074001c00020b15802424a0b6440728202d0350303d000c41a4500d02644d590301d00000020390380c9000601031660f840143d02450410524404015254001c0100082032080509105c40040c0700c150081d13018000e84140007400183c4015a400901c800500481c09030542c034001250a640d00310541d00c086d2400d19000c0303240700f91110102e400d8040c4203002145ca2007000d07820220380d00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 35068341 1250 35067091 35067101
    0xc06070c02091003030207151112030412050a0503180f0a03030c03060608090601060c0309080d121a13020f07050a0507080c0901030b0a0507200d0212040305060a09030c02060d 77
    0x2000720b5041d0620344612000394981c07100c620005025034020001000100240302d07000c0c42000c07503420b0407007201c07100800d50343c1003507a0750740202ca1401d400800c100400c4000c0350030800f040060318000d4185064410040d00d180b001074050900b98450102180020030108541030b410004c50081e26202d240f280b80140c00703054020044800f0900700140411191311901c0514402c051010041c40346034a000429980c00c0c032090401e034100003c0020100c0c0d0941c04000c80c1c43c50725800e581e20301c0351040c013803040002c941150b010300307040f000c3c580011207550b96040c088508201500c000141d840540c500031151034454010010903a002d055881e6043c000045500801c42d2030420560745d800000780100b01c025002400010710500c4241c010403514441036100f250b00200600308582009001007148074420300c05141c00c55282e00103900462082c0e414000c001d10480b0b10947c0c10300300390550307039030540b0343d1030060499444c00c2e603a0140308103040c4241c100300da4440c1c010740055642c65a296100f80a02 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 35069591 1250 35068341 35068343
    0xc03090b06030d0903020f1809030a08010b090906040e03090d06020904050c042402070b0d090c0e07020a06020f090d050307050105060d080304030804020d0209010f0905010f0303020c06030c0c06070c 87
    0x90422000490301c0c100465050b104228030364031604140c0c21542002001040303440b019070880c0514846000c20096107a51500482279003000b50340366038450b0001825400141c121586041052001d031036651a01c0c004250400300484022445441ca000320034070310300400031000d500800d030f03e103c81d003482150750040c07441d003005803400d2249a880c4d4118880920440c810524820103030404040c40d08000c80e03040280b9891341c8103451801e6540d982020040d0414544d02e60400e0f95105100200310440701c40d60014a4814442861880c0ca000081e4941503c034402901c11900041e001d10340200d100b007101c41045000f400c00300c68001034148103507070b40c11011080350258a0800401e000340b40081500e40003e80c0500306525541c0d0b1540c0444600801410803070b040f13405600040c00582c0c0e081c407040c5c0030745090444010030b94230740885c410079a5010390021500444420f424404668080388003d10818241c880990b01d44401007503541910a804441f681070143c3c03400d000078181d2000d1800119 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 35070841 1250 35069591 35069603
    0x2040b07050c030703020108060d080d05010b0a270501032301080d02060705070c1503180809040b0a03050318010909090f110616060b030102070b04060c080f0c0a0e040f0c0309 77
    0x42e406a909160707584c003003030002a0210340302d00300250482c6040c01d041c0c801075116040140c02d0601c2100c1c41e400f80c0301c00b83c105221401001c0b800c3c899a13940807001c280c00000745900744401c60000c50322200e280005019180c10103480d15141c0e140c090100c11884808074514200d1085076944110003511094107802c640010f00544010401c014402c0083d01c3d2441d40000700180c403540b8001028070781a00506829050544500d8851449946540c1020040340143c01850b620302c4007800300811030b034011076464807460391000c00b40701203240001913500041c9240a4212221003c070016a45800c0992001240d10309100003081007021908458501a1044039058a1035220108103c3d00d4060840c1c00308800e2005800640400c807190808030f12020064001440e00c420390700c504d1060b15003150181c1e0f00c5901e0b40900c0340225800320100740c0c0401682c601c0300303160824080d05a00c510942c4440020413001d43c0d0b00100d2136949134021812138400c8002040390b2991250f000e00904403496081d500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 35071947 1106 35070841 35070853
    0x501050a140a0306030203100c3203100e010603051326040e01081c020703140709020a021b040b22020702030303250e0a0b03041502040b0705 62
    0x190710b100355000b04140c5c0c298014103107810012001d8242030740c5002d488000c0642d10109a8004840780c01400d40c240d40f0707007a8016060300314990b1100c020030300002408511121f420b0182c048440b00004103105070b03603481081d0201d400840c1d0a4216031425003201c4006200742e4003210301074250342028050000750704281c4c8810b40040e0481c501d42d0b88000014010841c0c2005040910801d11070300750a031240b030000080d03c40c09607204c000c0c82171084c0d0310b50303c00c810307018400e01015104d020021500d03000c0261001b550740611080c5000303007034502d52055245080c14003400703082d10400ba010901907818113061120000c0300e80d05944665070b0030b00c0640010f94040c001107000301031490050640d401294110b40c0001072001c18101400b1038a40040056111082140e080f0384441855a03101d07075503400c01e0000200c3e24040c1ca03034402e01c0080c010410440c10009002c02c1c50180080342c075 = true := by decide +kernel

theorem cover : BRFrame.Cov 34892091 35071947 := by
  have h0 := BRFrame.cov_init 34892091
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34892091 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 34892091 ≤ n) (h2 : n < 35071947) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
