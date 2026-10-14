-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1248
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:58:28.667376+00:00
-- url     : https://prove2.me/submissions/4967697b-fe8c-481f-a0cf-7e9f7d529bef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 224280575 ≤ n < 224460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 224281825 1250 224280575 224280599
    0x41508070f020c090402061b0109021306050616170a030e06150603060139021c032c0d0605060109080708070902030901060807060801030b062d0f03102004 68
    0x1d08420784001c103085d1103a2000804500401810700d25a030320614625029030015005491307034a0094400400c040001f07170a0500f610120301032690003100401c0f103040002c258200110166000303596100000707150f60fa0b445034580c480150b0340c0c0001d0b150181e18000300020300616401624000d00140c04400407400305116000c01840c1c0c0b4184401c9400d40862040d00404018646d80c2070480700700011464440655444843c4038280e000b02030450741e0302c0611a081c8410807203190141ca83c40c0305074602954002c548840316088111441054041d07071002d8554030940ca081920499002c41d4900d464000103050071030941c004605544242002c00440802140103025903010f000b0240e0b880c0d640103a040d0240696030300415041c41000400a0f92517404180d079030507a0721400c0c021165032075080070817a054985594a078200d12101d810840b02c4000c4140c0380d5150240030b84450f040c24001e000203405c05401080d03c2d0f559507121001c1046281d03181000c5107a14684a52541c1030506000f0386d100b030707 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 224283075 1250 224281825 224281843
    0x20c03040f061b170309070e010611010518061902071a06040b0a06051602010216031202120f0a08090c1905040c1404030308060307030606180f0902010806040203060411041508070f02 80
    0x18011001020030006c84060140740054051490300b085a542c1d1004000c10390034296214040070351030017010400e000d1810f10040c4100e4100c50050040b0340701c1002c6030380d004d2444207032804d13426420486007002a000c000c0c0d48400c08181e400841c02490f119080c00241c81c1d02ca15520710900c0652820b1025075008000c0d0b80780f040b80c10382c800a200d200ca1005070320304540751900100f048c0b01e404001013040f84156000180c00b085030f00351004200b4000110815011300c84126000e450706010280006105090407580441e18100b103452207005000483c840220f02c40200b0820304280600303200e10b042500400101113801c3c685141c402c03054030141c040c1c600550000134100540800414000e80d03040083c0d001464002808000d070f0342c2d881440007035a12086002c110a5414409180201c191030f1003428215a0182c540001550701c00c0c082100a40c40200440c1e800b580e151302d9000340c1d18150000d4000340401940911011a10b1079010349a03050051140c0100300c24082c040c0d0740b4546c00714a1410f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 224284325 1250 224283075 224283113
    0x61409010210020f0904020304123c2708071d01050405040614150307050a12062007060e070e010f120812090a020117070e0d020301020c03040f061b 65
    0x2131521021242040d00e03100303410700b0300d5110f400032043c4014048104c0b074840b408282c07501e07100b043c3c01d080354000c1200071000f0031510f103100d880c209080700302030341100100500d04a8600340074200411590310018004a0806811504048a0922040d002080440040d004040e02160f10350000303074142018100c1400741d18062038840d00410100328058004402d1024840898007a43c50900c54004148484148482c8244905200052107081a2940320281c554400c494602c410031a26410b0140c107005400c21843c464401c5500600039400005e443c0f903500c14800070814107441e201c4285000c91030341114824104080040001c007411a9a0408a03005d21003284080181400d0071880c900075409921440501e0004000042c0e9021850b000c90b14400d03261101c1d00426040e100b0340d500c80859110f804a44075070b90030040d5203411003401c40328920007400075140907038502c202415600960703c10745c400400500c05205a5401c0b032210350141d49403000d03407103e1140c0c1c2d4550040303034186240140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 224285575 1250 224284325 224284327
    0x103020903010905011812080705030411190b0c07050901080304050d0312061d07020a1232090312070206190e04050c030a0b1e062a0706140901021002 66
    0x660952003c0d0040c5032a5600800208410299035550020640d10110103c40c0c14414414241d0003c4c06115814003a1009940d81410359036941e075202d010203c21400c0b1b540c000080c60650250130500d58805003d004490801130b00c1e00a00503500f031501001c2d4100743d2003440c1110040c40301e420004290703411140e045903550062101e40c202511083c0c072041c0303100c1002d0306010021483c41c2c0c03000c0301c40070309541186031080c0507590786030100c3c2c645801e140700804100c013a980301c2502c27030b11803114140500000d400000101e40121310300c01c0704800c0d40c02a690b003800049840412032a0600ca820a10410150712a1600d45c0c190300142c221b128611807020507030305000b82035503010f00c030b42075001c4001c030301410802c506e042c809045ca989401c1260250400c034201441c104090504882504002ca850604004d04100319410000c1d2504007079080401032844100040700740502c520140c07400079010307028010303941c100000100300c0d030302c01c4d01c20b906644410081c50040d81d900140c0d9021540c5103003001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 224286825 1250 224285575 224285587
    0x307080a05120c040302010e0103180b072c04060f03030f05030a0f020703090f120f0204050c0705150601020c0405041a0601120e10321905010e060a06020705060702010302 75
    0x790303068041c060300120721035000e0040001d09441c840c01401964003d0702c0c0d9004981104004406030b0b134901c50746881d180000c42d134003000501c0040c0c0d4950002d00f00d0500030f076070182c0d40c250b1072043d42403a4a902107051102008c800d960030a0f2040c40c019000e44420700c4181411a100680601e001c40019005c100c00000025908100ea03440589648030b4080305654900305424000e08250310340c050000785601e590000101b0418a00040e03050380d40c001056001030f1a69001c100092070010703c10b9076203e40401942002880c00d0003215000d0445c036401400f14100300b4002480c00300b06019103030003141744c2010300c4003298040e0000c108d55203840300d09017a2980d034480100c42940c2c203803440400c06810100341a00c02e0601080000c54000144000c001144000e00c2e0b08921041640b03075203180c030b1802601007122412101c10340b03622180e240140385e41d810306580c1035012590240e00c42250350f0072002c02e116036460031036440c1c1c000340300313078402003500c2402c01d00041d44a100d40080281416800604 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 224288075 1250 224286825 224286827
    0xa0c0509061b1e0303040b01080705030c010e0a170607030c0810031b08010c03140603070302012a0b1509090601151b05070f0302010f050415081302030f010b031902030307080a 77
    0x4901c40a040d40c3c801d00001007600c20b00d01d5417600203513022229140b42000204040400107001700889500400503c1041e12a100546440003c3d02079180c209a03c1ca0340498690f4100c130354003241000600003407a0380d29010800400702c1d9035100d07404e41000b04503418840d035a00c0300d100e00d03001d0b00c0c1c03c2951412442107494a4003010451039010355223950902411004003034140d804040140d134540f150108036910b00c01010b8a03120107010080c0801c080c40042015a149440454001c03020182655041801c0d51245840e04800315a1000d01041410520f5424108076600c0754020b0407a40c014281c03541000d0b40301c014407083c207030000200500c070295100750380030745254103414642040617120344a0300c03100d04d8042780703441d40000e9020071039100c0030002051044017214103c4100e149110010100c01364100c3e0881005401d111015540003982d00141e07400340051018444410300009601c0500c00615040203e801c0c3c0d0015611002da0100c805038030044203d98030142c0c810000341c0c0c1d4101001c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 224289325 1250 224288075 224288083
    0x1503021014031b19020d0318050303040b0c0f042408130b0703020d140411010512011a0403060f050604060b0a02030301050f010314010608040201030516230408010c0302030a0c0509061b 81
    0x21032125107030764692108040e58000c159822021a10750b02231044074030001003880310024501d0014020751041001a0115014080c034076000000c07448014907100e0300007400b000c16002600b0058031603452161124a10101d0401605905242d0400503854507240c3c0c482c2e80c01252120028205494000015000720302c40e5040380d640c03001e9103904101c500d40300081100441c20803503044581022000300d2003001e600900503907251500c2d00c4d200d0300c02a801e10300110318030500e4024492107240180300c00700006e9824050b40080305010440018140340c01d40411065130581c3d80503441700301080107510340580d03011081380d05455081d05c03008030342809500124010615038600010030001c4a0000c1141036000ba5024050381c003da03014001d54032250f040043c0c1d00c4560b00c421000c9040c8404240f00c10280e0001025001603003000c1c503003041d50303c040035401d40c1c90b40c0340d8102c0000d074000301f00a0912424856005444441e01c0c0a50402e40c4003000315445201b189010000b00c00c0b540415500040100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 224290575 1250 224289325 224289337
    0xa14010617060411030a050604030e030c13020c070906060e091905010806010e070806100f0c14030a021908040b0f0c0102040b03090c012a050705041503021014031b 72
    0x150594050700080d0603664554109540803a15003401c0c1625500c1c5282c0080e0b1903503595002806010141c0b40c0c0d0340c0549182c9101c01c04181c0500074686c1e80343c104c1e61901c003000104004d8007405a607419845158a0030503810380c0000060928200d0305002c00d070703840084040c7c800303826122072009484018034a0740041100384103028407030070b0174000720b00617a0104078541250342d40045440d69449400003540e88075000c0384c1c450781200f084042d40c0905c9108105140e03025889040104ca48151034881510400403460758000301d500001d01e1000569040209107031103484105083d004030107650fa40716440c82244140d000104000c42c1c1031140c8008081100c3c10101108000c654540e581c00640061383c1080300c102146004104120095501030400700d0313110264032402045408807a00c0b0b0b212241206070050b5500e00c246980485c02d03440710320400c0a1240d50000190016145104105810720000403003c10002207190700c6141e10f05d190305598000f81040700380c4411489011180465000f18 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 224291825 1250 224290575 224290589
    0x210f090f161404020d110703090b04030210050a0c060e0f0706020a050d18081009060f0c0807030c02160803030a061509090c11030715150302090a02030901061e080c040507020a140106 80
    0x10611b2040b61002c50090082500c070b0f8544a02041da00c451555460040780700281d04a480b02e030000740700a100b8401070a4100a03410480841e110a0712110129001808003840c11751110010b900306041c00c11400c1c004100910040c100304401c1e80e01c00791144c00c8501034005202c0b4030401800040c400f080c040010b403900b0301c00c50710a403083c1c3c5001d0b03019040820b41554002d1401144c0c0b001d04a5900904045500b00d48521484c1d84030f03c181100104000f085120071400b40307840c03a0452803a034034117003001400c800c0001c41e16030622200700412070f030240e0f02c600003820001400002e1300d07802030500c408550385c4043c0040e121600b03040030703a80cac251489241415404000b440740200811544890040403010808105135010508000140b20b498040658444540800514000310039001164440e41410003c5540d03541c541080b400c07001c00c80c5956800d441041014800040304110545480348211070a2003a4100004041d40315040148060302c8000659040074408209412200044c400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 224293075 1250 224291825 224291831
    0x5120a0f03020102090f060c0604030c06061805010e0c1612021006060c1b050307051203120405150f0f01031b0b13061403010317210f090f161404020d 66
    0x440c81d00070700035400440701c684200101400814103050203000c6d075001d003248200600064940d61030a0b141c1101c412411203807a9299000400c4900b00100c500d05440c0101ca80460554101180d1403000e0300001c010480610062200030b94241821503083c0040d50042c0c040e804118030180200d0900340f410f04106805810301d41c0000b182940949040042d078056100401d10050364141d03140181c42e0380c8112a031551100200740614a000390003076902d1030000040700c0c540420803481c0001106c048030191a1b541119000b411520b0100c200e00d0740c410003444400341d9521b404015040036044c18007025203180000d04019103010842c1000002801008484c5a100d030f001403034441c4151000e000b50000103616561010b140c3c1c050906803410b1700d80c0b00c3c181c82100006aa10000d864120f03e484610049400151342105114501c1e0030f4020100310201d00355924250304036a107405405503000c02c02e41d0080c4501c0d2106030207600040305a0740035074000e03080754150f00c2c0024042d0054000c605c028910b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 224294325 1250 224293075 224293103
    0x50129011112131502010606200712030905011101020c07060e0103090605180d02070506092803030e04140708060136090b060f12040816050a0506011e05120a 69
    0x4100e140d402100c0c540004e01c0c1d8281d5407588120f0070303652144070b00008140f40003c00e200350450307200640c01c540304180884201b01d41d40c0c9140b1400c2d41d041d24054000c03582e008014815543d01041c10445017201400941c50840c06d042c4c0d40340c1d951200c1c403445081000d07040c8503490585c820f400c0400740c0c0703811080c14041424456040400d22000145400d001d01c520b85440442e1400810b1050845a004122a0804400805000b031000236100d8441c483e42c018501d14480401c1c00e6081c00c0914002d60312494009100014801211226262286884010420007861560100415a0104081c40c1c28005c9032075101d07842605006c00105e0541d40c0e043e07540b160385250b03050801601240d40411041c404400c846090010520554440d000041010444200c0000442c41c110350820303c2815214a484481c43c10555950440d060460b2a50002c64041040c01010061103004d04070044004113a0034482c1515007007210248a80350094403d445201240c020070320010740e640d40c01c132254140c021 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 224295575 1250 224294325 224294347
    0x150e030304030e01020d0c020906090c040e010f090c05030402030303180313031b060c1a15060c0d03050a05010f09110403050d120632040f021303050129011112 70
    0x3e20f030035044a0051042c0d001e08500e0324402c0d0121103550760050410001600d5400030700c040755500410310709288600700320001e080001204c2550080500030481d43d021403c0500034800e0754a01301c8401c003004428001d20025035400300480f074100c800120004008100e6808450842c0a014a0401c40503170302c05000082c4034a2602c00d00c4270030000c0982140356034503104150340381e801c0d0001c0a00021000c0c00c0700c0210034440343c8026001004484450320090401e40041c40310380c40b0115041c416000104241d0159415009940d040305401d03000344000d6041a0303c5410490040c031543c0030303041e00c585100a4000c022402c84000c0c40d04101901c1d100208034201504030150b01c4901c181c540e107001c40020b1030144645456002500c60705030405100203010360100e500c010101d880354091342e24980b41b0208040f51008010709110550020781c42031843c24800e007150f02100310060a403402003007070030300b00d840462840c19038402402c241020700444286286040540a116814803d0020b010000c44d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 224296825 1250 224295575 224295587
    0x3071503090b0105040603030503040b100e010f0303030f05070e33120c09010e10031b0305160804152301030602030406060b0a0801150e03060a050601020607020a0c03150e03030403 79
    0x1e00d00a040000709079a84400b800221a40c603c405000078100b80085000030f0010204e29802c0108462505902038498080b40c4800d05d084e80640440ca285a00801c10107400d1300031070f400a00c48650800c05450002000380c44c16400c101f80910840314071101120928444440c841000c170754256280e90381c05840b190705520f504c5002c90040d40c2c55004002502e40b528002240c0d10201c040c0e61b843c1c5078401c0c0809100742e101f80212520b007450b0700d45e03208500740000716402c0e4070080c1e4a42c1e408201e0b41080a141000101c1c010b4040d0b0400a464007048042159060300c40031003082d6000000d06216801656a42d42c4160b80c9171071840700c0b140c03000005100154000d0340c00b69000d548100103007035035040070300ca5a00c5445e002c039022a100c0d0700108641c070003041d44082550101d090502450114000003801c19004451f2000700ca55903209010103940e04102a59202c0d0142c0002c0c491028203450724900090240700040107480d40d55207080c801c040780e400580320b151001040783e403a41030615000d003139 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 224298075 1250 224296825 224296841
    0x21201090b03071503090809030307061407141603020708030d0c03060626060a0518091b0612060a170606010201110405181f06260403090b0903071503 66
    0x40c890074901c0c02440c9140220355030303007180c8800550406001c0c0441080e070141551050030f8a98010130300c14070b10303246c40610041c040c2c10b106450003d090705000300d0483d40782a024040c04100644500c0c040380300c101040854201c0b61548245240300020303454101e24044082c0c100035136600002c900303032500c645145c000402c0e11406407405e2289030b4580a0846100c001040a404005401038250756071600b4511856004140544505800d60325000405c0d1000e0b42250406440b41c4040c041102d1088284200b40c3d2030081c01ca5800649504080001d0980c0111815410b0038280c880108407581d4403500315000610380100101c1c401d1130138980442d01d82d00300300ca81d24050b500f0030481c840c1c1a90014200c5d0b0644800070490300100a40445500b000a0010004100c003c000440e180c1c2030000100e4070300c001c0a035603a5030241810700f00d110403800d401000113922200a80f005200000390040710100a949200444580325150300000034030309261940b1145040a81d03610a032211039042e000082 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 224299325 1250 224298075 224298089
    0x607050d0f020d1404170a0c0b071e11060a09050a030f140f0d03090303020f030f0412170a0c0c0b0c0a0e060c03040501050a140c010207170a020a0311010f021201 71
    0x44042c1040f01c1518104010307244490401c0d4200700c18802c21007071680a0100000110840c0c01501705a628100c0f078040d5a040344031581c1c03002c00c800c020840c6220000c080081001105c1c13410001542c0d816810182e4055079074410740c008039041c07806601ca1524540180001402d020700c1c160b0f41c0c00c000c03440d400b4681c0b05840300000e0b1040d220030041d0010384841580ca07400010000719201d00c4040b001402024800c0301090707020000d4005460744075000d140a5110110f4001310f90501e8602031940c85107220210045c02016852103041d100c411003416444030150201003214140f100003210414a850001880300c1c19880510814410280103031a0154040c1c0341c0031000702c0c0b0301c4100500d27805680e04180303559000b0401404a54498000750501c21074a041c05401c02c1440c003102c040c50340022000e540345030360100b0902c05001300c66042c0440c20b90390300340c05450881040002521000700c498050b00784030b20076560100d001e80c00d6012901a13200802c0440d168140e03848008c4e0005420310500c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 224300575 1250 224299325 224299333
    0x50f010f0c08160909150b040914070c080d020a050403060f0501030302010e031e09040213031a07030b0609011103130806151005030114060909130b0109020c0d08060607050d0f02 78
    0xd0401e10441c0010440c43c08143c071080b00a501d042c1182d00605a4081650803501e02c103071303000580aa042d0050704c050401230b030300416968080103c440081c3c1000304008200301d400d13030703881c2d001c210302c04101d4591900303649000d42d403242c10300c0c0240c50740d1081c2d0344020201480e210021120520662119050b203210394000d201240d103118195540703000d4010700c0c0c2c0304509512101180150070800400030550007800140c102074202000030203058496105881c090070000c042c105101c40403a001c2c2e403010650404210306000140030070745038060510014103002015a0004600c2000c0090354802020010302a04a58940028580395001900d0440f03014440c803001c40d8aa1614101868040c9080d944542c1035038a4480c1c55100d2007500100c643d041102004001c201ea103d1900c000e1041d400300400034074000052070700c40400c441c140e220700b04040c0305000220050a0101d0101103200071031400101684035900007520510580c4e0005085125582064000c5500005000d0008031544c0030f403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 224301825 1250 224300575 224300581
    0x509071d0306061008180604030210060806010f03020607060603060e0a02030c2b030c0f03080702101a040c030b04090308060108090102030105030d080910060605091203070c0b0304050f010f0c08 85
    0x126684200c10341c3ca50b90b1090081400641c594490010305a001d4000d00300c16900d090080a41420200107840940050f00318181c10407a1074040c1c00780c1c0e802807203401c00814440d0b15110641d40b4040782800002c0c402c00d4005040340a22190703402c20405581c010804100901c0c0e20700c0c00350fa40f080800c000724001d000b1541009554940418501d00d20500030030b54000148201250941c000d42100b411002d00c0350701c61041740803600b058a0010050b11a45070380b8030301d0401071006850a9220035200d5421428a0700d003000142402c3e640d41718030a001d8a000c240103c07502d48c2500a001e001e406c6940140c030b4a801001816404000280558401c1c4c0322100d1945414501c1030030f1348401d0003010340651060301d881c80314070b100e2a619940b042c04141603500c14414102c10800f50740141e401600054400301d078000c11071400415001c2500c3ea818004c0d2701d000003a0b91040030b9540c00d03105620300c0d0b071008030006060010030721038050002c074084001c02c0010394032410310700184055014200090070305000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 224303075 1250 224301825 224301829
    0x1b120b06030402130207170c0705042a05090102120c06330f0f040213180608060f0703020c0f2404081206360a0209100c0c0509071d 58
    0x48a00840c0c0241007400754944c2100254080e50007558204d400501401d10b4144403a403075000381003011036110141100c507280400308002e4070007901401e205046000c416030800c05030000001e46400090a18648640b482001070342021f6104000c00c0389030b54005040d0314003a9002c11241e114544030900c0003c01c5504103159401c01202c081c3c9200002071040c000e41c00e42ca0034081c0d02101e02d00c024040110b548800f80403030280d821145039081070740c43c001801d01c03d04900c11345064000b40c506204100312403800c142107503286000b402c1001071841c14400305800e10b00c250112081101918200c03450300c400c0900030380d9940701c864500c10b00b04402181884c80c0301850707000d65000e01d810102003814000c0700d591440c01180b029080d940d114034829884084c40c140b240d01c0030b28403014014004002c040507803c034030b510140180390380c0501c0d20410001c0080c1da1034a0140182c5501441c04a2000703a55207802c40802d001600403039405010101044007890f0721039a42d01595240c0d4080020350900801 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 224304325 1250 224303075 224303077
    0x70305060108070803160308190e01020319051302010e030c04061e0609030809040203070c050727050f0f04050102120f010302030f0106030c051903060905150708040203030901121b120b06 82
    0x20b400c0c40001d1b14400c000c00f09114144154205260807480ba4045038600c1304002110300d0482c42c1c1103d65008403c00c071481b42d8001a140082c0f26102c3e060002c3d1031320130b00700041c5110000c0e00030305120408002d5041c6403010446158201030113041002072545501702c2c1201c00079181841040542095004179010f0b00c955005011240d0003ca1281441ca80d4002c02c8040d41000b4604001c0044030790340c220104a00708051801040c00400e101900b0342d68002404d0440001419070100c9401c0c00e041c48100c001e000d1540ba030102c610112008562503525010340640304801019803440c6007402031000c40080d0000340e50403284203d0454101503001c40704c42d406c0c0e5600384006030540f01d1524080060741094a03401e40c24070410304403008865207030f82d2504110303403039810107861f07507401800030100100032144003e810286d0340c18181e01328034065001170f50741d1060840442c100302c0c0040c00108200a41d41002c1c41d0343c2c2e00f41030038402c0a11801c00040c039003c0c0c03460000003080c0c00c3c01c3d141451402c02d40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 224305575 1250 224304325 224304337
    0x30406080c0c0c10030c02190203060109050403050f0a1805090405100f020904090c140604080a030507020d02031b1f23040509010f080106050f131d070305060108070803 74
    0x144403408241e80710300001c00150403015245125000f00e19111580d41e4603100c00341d01400540d100045e00b030b42038560007850050400c2141c106c0c9801030500b94090303980001c03101e044400590010503d035860b441c0494036401001c440141040000c2100c844c8507401100010f01d0364905a450081c0a60751803c0000b42c0f201994090000d400c800801002045190000c00004407500005882c0844003c0400c080316484541600d00c3c00100d10b0500042c2c10b40c00011501d40713000c40e8407a0800d401c050740e0544404074548010300b840310000e182c5045403180d0b00145055600201a22481802c501e200b505c107030344078100c80d4400d02c1e20200e0640c111034041100001c044456446c2c03d80c20f84507101c080e10f00c4484c9900f00010310020b00002030660344003000c45000c0c00c100282007844602d007015503405c1d29400e4109034840e808550042030540c558420140141c0002440403440c407904d160b5480e58051000e21154039401038010102c14014009085070490703140600721a40195600b410986a00070743c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 224306825 1250 224305575 224305577
    0x31b04080c0310180201030b120d02030909100303120b0f06030f0601020105160c1b08030417010606090605091e031e150702071203020c0307150807020705060d110c060c03010512030406 81
    0x100d41c1350b4016501c40e50081d0f48005000c0c0c001411040f2103102d85140070203400e40c0300010b0b40005992089401e00c10440c07600a81c0e052050255141140d402811079038054403c108010b5a9044000080ea181725046050260150203e5600e0505200e409003511044440b140590b0030300b008500e640f142d80c00544d2912049070754407507034003120342e81d14015189140c080310b80d15007840710301150700c0341d080c00284000c01200100586800e61704940b90701b5112503070700517005e024070b90000f0400a5003140c100c82869a084449206000c1010750b007510100300344840361303003600c6407a510400050084030141d0112007000102c2d1405003500703443c008003001c100c40420040e0451030003044048050a458036546119005803005041c064020900c2c2c01040c1d8009104a202a0382402c4255006415103030000c0240c405854444e0070720001c90120700c0340609152010f80d864060001c00084001a182854200c40595030f07203040580740389043c0c0c1c2007801040d201c1d00c2100400791056a00004443c1211a2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 224308075 1250 224306825 224306861
    0x3060503010510031203091104020316180f090513060903080a0609050c0f09280e0f0906070e030a060f20030f04020915060310060806030d050d02031b04080c0310 71
    0x1045048000e0401c60304100d803080351510604005132780760f002640c840c410190b044e101709810301344010001035204c00e0315040c0500509040c001140d00c501c00f50155008034101081c19212824030080c00307542840013070429803418401804055101d9000b074080c410410b81480100c1d203405402044910a64151200c004204090750140307090502401581900501c09120309040310034141407500703109203448181009840500110804002d090313000403055406020b50301e441c0300c2d182d54800d0041c141c50b043c0207800e6000340c0c0c0d995080224003207444d40304c5410b0002a00b50004140940842001e20726041303030440d5621440b0b00603506803441045005289500e50300c4580901c0a400f0000d02041090792503109041c9158607020001c46c0202600450100394910307105e001040820068205441b9400106d410010b0782d42c82402d96040710f41c850303401680cbe900c40c44a64940f01211080e142002900840d0028034844d02007904909550182d003942e00960302c1254140c01c8031040e04100201d041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 224309325 1250 224308075 224308103
    0x90b0105030a0c03060e010b0706050f0f1503070b0c06100504150e0a0b1008060f010305090709021c09053d090212061801110307020303040b0c0f07030306050301051003 74
    0x200781d070403042603415103090003c5c04a40f90300d54010111400d0b0842c00c0c014400240c210100714040c814907600103c88003402d80c09003010318504110800141c000c1c02107a406000c00008c55030244000002072080200700d5684807080d1822a484040c00c43d80c0000e009806c0070001210b081c64003440b201e01d801e0176603152105042074032102500501070704140046581e03e0b0540e01d1a200c0072040100c06029440d235110526101040052413081d03400c2c0141054140b2003808400100000d0920940d041080c0250700d07500619064921348985180d54031410f420b0070041d0041c0440841c040010030012030446d480c038915503001d558050f50040380400d8401402092940004859220000e2580b0050510106612551039507152900684280c51000118141c0c1548e40c0000d1044145214506401d5803c516000d28080d40768080144040d0410052600058000e090241150400e10012985035140c00c800e040080042005004050196282001140801405441d9101140e0b8000007500b4402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 224310575 1250 224309325 224309341
    0x3050307050f07060c050714070b1c0e060103030c05060f160f020313030b060310140708060307170a0b010b03100312090e09061e15010f1407110406090b010503 70
    0x544920b80403244610144031078400075070580035202d04417515a8840f0384428403800c000b0300c1d0b540003c000c04c600d84d201c807008100034040c40c0242c0304480781842049040e031383c000300c00c3c41c09007402c1001040d00e4003c00d40040105600400c54111550082d000c0340c80e25542c4850400507a9410703203245034454024070340d44541a10882c0b8082e071400c0c0034415242083c45440102e0842125500704503400182e030000c20907141070402c4440001d038401d4005200001c0400c4150140481c064868010003105000041d503544082080c0c0b4000c050030030003e0010a00c200303165032200080760f0101c0791540c2610002410904107800d880c050b500d0750000301e10b03651865480c0c949010420700070f4424042c070303080c001856508842c0d440c0e12034059240980f5243c6040c411a80c6240000d400d0b54091342844420702094840c4c0401c030b500003810a091034a2541c0d520202516240804030804294200c00260102004506041c1007103862081e1801e001030350702c0790310260550740c0d03a1009600144090002030f42c04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 224311825 1250 224310575 224310577
    0x604080d08330103020c0d03240315050402041b050306010207060801080c091909060e07080102070c140301090204020d09120206091218030a0302061617010306051b0301081609090305030705 83
    0xc414100149000004190f0b1800d203880001c1c0d034004240d45001409280e58019140ba043e08500103184c142241165140005451446c80580d00140d33104e000034215100c0740e004084007410484150406143c070103009099034000c5600600500601000007481c03406581030314141c2d0300000151800d0004003042c89001040103011203011001000104540d407820f00c550481c003801000c020500810425800d45040001d90000d203d0380e1040009001103030040c82100181c946003444040b104512000003405400310f880c1c080d601510010b02e0380a12069540301c0c0e10014815210300c500c0c019404c50070b80c3c031004110307003185c2590001260003007154010002060502c0301802c2040c140108503002c2460103001c2201200503038018418052006042c4070034400b03609061404c00d10b07117061840400494217041c0310041c102620380d404900c0c59051401507000c0194150101d6480c3d683d80d218075039503074001c050180d2245120342404100041180200c2100a406840f99461515400812512 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 224313075 1250 224311825 224311921
    0x910090f060e0120061b071e060507020c030303221a01030308010801021c091a04050607030c03020c06060d08040b0703020d0807020d02100b010507020604080d08 71
    0x1040588140490030008505403a00507180c20758424241420035000502102512513000100b2800786901e12110312000604a6010390ba900103100c4944e0b5010040109000f55880108480300001e06800ca00302d01c0440601120300401081c82151119201681c81c0c8901c4800d254168004100003070f110000d101c144031141d204018014520314030340d11014a83d003684031196590459100040050540c00b21802c0d025180101c000c42c0307040d012400071002400d868910706407840d11503580c42c051000117403902c0402c0340c41e01080c031070500d0107240540c1c46150886148001c2480c1480000500b032203842a112480d07079030b000800d05030b11504104030303821003c280100c1d10f4100420010480f4403c0401130007003e84a50000d041c3d07107a0a203030181441c10001c042004641c040030741600c09590016582e0388490121000080082d40d03440102c806208825010307410030800240041e00d40f000240c4c0da040d03a481d5075907015040e11092981d00030b034042c4a030100310813070700700c5088890200d01030a4245 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 224314325 1250 224313075 224313077
    0xe01110c22020d0b040501050307080a170c06070e090901090c03060b0d0f06020c010612051c180f050a060302030c040e0a0f09050607020d03020309190c030f0c090f0203010501050910 80
    0xc01007540c2041002a80c1c86000100b1182c0e403144002c40b024100b40c025980076000443c00341c40e01ca402d00c5621980c44120740c102500ca10b4201c0c5468000700f6811007158018000e02d0141c5505181c40710700907000d40c03e00300282e80681c0395180090036580c010710410600e16403009108480c00d01e19103c0c00044c0c070206002542c40510b803045100000c0501d0404015940716520160300e031340008921038211049644a001c9184c03201700c00f10000f58000c107149024915002080720b1145181c0380071601c80065850804c180800c28401046000e8885520780403034004603940380c501d0b91a4a004c5090b40020340c3ca41080d000c00f13100600c4100c0e4a00c1c1e205034003500c0e103d00024000000e40750302c0141d034540b1109842a82101c401c0c030594a5041c042821400d0719801c0c25880c60030074a514584d20500701c11400700781d05600368480c04001141401e000110342144600342100f0f043d0400448009142c0b0403490003e242002303112100d80c06000f0b403412620140c40f058207100c004828400082c4840070100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 224315575 1250 224314325 224314369
    0x13060e04061d04050606040b010e011209050706090305070b04060e0d0302120d0209041d0601150e030f1f0b06030705090622080f0a110d030903060501060804030e01110c 74
    0x2058550820580c07511440c070802d00c41c1e009040a04109007015405017080d40900d0803d020042980d800c1510520b82d00400e107403803410f4038801c124601c004c1c4000300c8002e015000300500004c501e940100e04400362400341c1e040d41c400503070f51005c400140c46684911404a00e0021019005150030005030401c1406401543d001c2d5103c1310074050158451856088215800300e5424842d003898815200c40c0c000f41440d0044c2d80c91003e002d20f5031030005100ba1078004c00380712903804d221031040f1a00c132005013020301241d000c400ca00300e1641d100c01484980c401580300c0302d0784903004000c0301d0081c00030403030300034041070b280da1280d240850f02035100305844c0760040c41c100107044051105500e0300200c0c2101411500c100390074074262600740050407040c0c2c40c1d10b41c082c0908401050a00742c120040c0c840484180c1d40d002007500e01584c071682950f0000d02401e1504000040d01038101c0c5220b8482c0c0c1c071a0b6104071008030030350019200044680c4920351964000d11112050b07080c280c44054580c024a1081 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 224316825 1250 224315575 224315579
    0xf0411040905040609150b010915050c160503010506030d050f0904020f18010801061418041b0306062d0e01022a130b0310090201030609050c0c0d0513060e0406 70
    0x10700707580003a10304480711580c50a09500b0300442d4291032141e10b50b068824401d410546000a14821342c6000b8820040c003c1141601c01c01c1c0510704581c00301d11160141c8001d0740d20788800d01c540d04030034401e0340d000b0350034540069014900441ca030303440c0e40416114642090254141c880e402c1e00714448407a0015400c11151000392120009000e0f0107030110501d41d0001d000e500010120303407069018006010703d2000310a0605109016285e008040050107240030402c00f00280251100e483d0000c81074a144101c400311943c03682004040d5480c0ba00c0703c411032030360801c400c3d034404031112103851042c0c2c019100d1101e16120f040072124122051044544612031a10b50900b4002000091401c0718103006080a0f141005c0f0540c880714015208208000d07141e003c0030944507907401443c80001503469402108580c00703503109030060700500714108010328060300490300d55449050b40362010b100d0440d02e6a4014825011500b400034402d1521007105c0c03406009454801030b00c00071642c040c6c0c40d6240 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 224318075 1250 224316825 224316839
    0x1150302090a051c121103040605070f020604080d0e1008180a05030c0106080c0a060f080711060f010e16090b09060d050903090a150e0d050a020301240e060f041104 72
    0x32600310388918022441c102090343c0f510b4450721703a00085240c103001503114040e8003540007109540450f4034074200580c4d2000701e1300d07002650101c1c2000080d4054404174000c030f00d04c200010700741c50600b03c075281e04000407003080801580c3c400816207400041c000794009400c094001e0b82414130b1410788004c0340d0109809990703080c1075820000c825009607540f100c0030807c1300c50070003c0d0b1302008000e4809121080c02e28070001c1c80b03850070325480014000b00401098100303109040e1350094102c6d80003551982d09020700c0250b42d03000f080c425114026000e5000c5040c40c6422072000c0c0c541c00c8262280304881d403424154407200d410040c0d8160b4050001d204410b41c0d140c060144070310070001d0310701550b501c0302600200001024542c208000303000341c02c110000100e42214032a00500c2c011602c0800b8459980703000f0703140c4075080707400070b406500300a0b65651111010300444d80382081c69045030380c01520b0303482c02946500101c4150342d110580d030141c22142d04003540104c542100c04910320340b0346522401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 224319325 1250 224318075 224318089
    0x10f0203090913150e0102090406050f0303120702190b04020a14090a05131e03020706020a0503121005030d0903060b032103040f0b01080303010e010f121106090406060801081501150302090a05 84
    0x251117001d40d40004500d001d6113018800c01010702f00440e00c64803140b5016000c0b0341e4078003a007a520182e4140b000c020480490003000a0609202c85801080c03054281d0301d400d080e522420b940807401780500300070100b00c01e8201e100f00b24030400c020b001580b0a60f41c01c1ca1303c00240002030700302c0d44000a00c000303000c041100c0c04110264050112041240401c003403900038a0300140c3c0d81b040c0c0464010400341c0c1c00088012048800c0c01600300c200607501c1d00c0c0d03100c0800c11030712141d0015501d841802d446e8551290000c110304d04036405400b04200d072625540c281a111440c4454059101020000c03000c41e41280101545d0000d02810800320280d0842d42c0d0722070f400b00c0a13040b010700c40e4404001002014100701c0d03500d000d015102811028145001a010015148800000c000650464616646440307030020b82da100d100050062044a81d42c3d1000b90007404203001c0e442d4140980000c5c0c14070200c0ca484a24121928034020498159034440220025000000f040c1e50001c030100c070014056030340305 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 224320575 1250 224319325 224319341
    0x10f08030a0c11300a03050403060b010905040f0c09141c0f02092707050f0112090618020a08030c120c07050406061d0103060b0910210209010f020309091315 69
    0x103c101300065400d40c000c4810064100303441c20954003246110f40041d501070280d030200c1e90b01c440007003030040713900700183d0b075031215500010382007490807140380300040c1a604644060446900d500c1e40682d10f07241da101010510346a56908a061080f081d8403c0886100c4266480d00900200c0f071541f595071f0000d41c0f039020940f540002c25500d50388441c8000440052a203442c1445802003082c2031a100110340c543c814805080c0c1071007004070420004070801c2c1c00503a040c1d80e0098042042118004080d0780c0841190304c10390007400454808502000000101d444e079029810040121304101c040090305640711039001500782c0600500003500c1e403501c0c00380001601254030340c0e146483d03003c907808907910a114103a030304040c10b0180401ca0408100200d45161030240e0303044641d00c05601d81038070098165085120343c80f440070f203042c1800104e507021b083c250310247e071001132003040780034100d959020710300a140c1c0c031545c02c201150b5a43d1481216006843c418108010486250300039182110301e02 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 224321825 1250 224320575 224320609
    0x60409050f0f100302040e0307050a060e0c010503220218100e13020a061202041d040b090d050f09010c12090905010603020a020a0b13050a03050c06010f08030a0c11 72
    0xd000780154041001240d540c070084842c040241e40c50b2401c0104003c403001d11001e4051713642c900081c0828030050084404142e000300c100c500c40c164610f02540100100381c1708440074025020881481c0d0720500c12240921030000080740000f465007002d50500c00d64030012130784404031041d079800c0070490101e01c521802900307560481d100d04d03040b4912401c260042411100c0792403400d559006079212000c602c00d03642c007464180401c1244a09400c0284101e401200d4440d191408500f100e00110030740174891813203040032051540740e1b009000d542d485071001410110300c090101c11080c44080000c1d0600d48014503010020341031a4079030303500407119600d0711301c0016800b400c02d0043c0b6045014940c010213861030b0451a201c82101d0094503640b200e900100b40350b0f15200411082c1c1e21000c00300741c07107641000c144c0706100003928015060740d000034030016840c02580000110300000c1c9000000b00e68030301c400355280c1480040101e40006240100301c80400006110398559250b01c480c0785815081 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 224323075 1250 224321825 224321831
    0x10215090607180b2d0d020c0c010e090c0c0a120f020d0e060a050708120705030f060301050103030509011215060507110613030b0a1404290f01170705060409 69
    0x16003001441201c1c4450320071082c49034003801300603413800041220401043d0300114000c00c0c17440410980b00203d141c2c40001c1065000c103800c0b2403074409078001d01c0c200900c0c40446408580500064a000701c141da03550385c0c4101c80c40c0004440c003040c54018000c2d1102c20056544d8030209644502090441d040c030540041e003c02039480c00399404001018404010f41072100311000b11100065440c444d46100904000000c2008800c100d075030340c1541d001004102c840040e514040a00800580048030003440c07a01407040402c64a04041c0704032410789800d40e950610f00094800151a01d102d500f000600381652108402072511010304520301926403030340c40c55604c42c01414241d840496070000180700d481c1c100804241c47c3c0003c10b2010490b5404444002036558804079640100808141c205114040d10100410844d18501526081420070b0b06608410107051800744405401c0ba0004080c90450380107222817441b071039001e803071118070504444009031280081003841e08140d11807058152 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 224324325 1250 224323075 224323081
    0x1512140703031e0c05030f091207090225020a030605150d0b061203131a0c12190c020f040e0a080c0703110306070c020d0c091b0807020114150102150906 67
    0x110901603079941c2d100d140313488046407a0b55120603480c1d100e60004060212000036845800b9102d01c4040310540195405603410aa901d0f607200d8040e40c000c1c5c2840840369080101c01c0480b403002c01c102008590080c0030040c485003590342d0311008100280003482c1c00490b01645100d1a5500c4070501c8c1e00d54450146400582040c009010358100c0045004989800600c0001454032203400b181c0c04071010f000c0348500201c032299803149284202404d006580c00f4060781d00c854584498000c041d0103600c002003505001d44520700b180d86010086000b0340c01031a9201c59100761519400c20328900302980c06a0ba4000955030300d0b0005681704c0043c030311054005e2038081003408012184036000f01000d9020b0081c501c1c001600030100d80050340024404e400502141080c084000f10b000003070300c0840020008100503c4000c8100150840003500089001c000540000c1c81030142c010303250707111030a00c156601d546041d10046101c0300e000b50304610032000308002302d00383c2800c400d00031107042001e00758600b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 224325575 1250 224324325 224324357
    0x315100207034209170715091a04050f010c0806030d02070305060a020d0612031706010216030215070503070f0c06140301090203090a060e0c03060a151214070303 71
    0x1410801c02c01011100d500c00003a4a600341c4002900200c0355100c075a80300f4080004010005071001820004d0b0020018954026140040004501444c81c004a411941e50a001603a01401d00102020400620809150044840c10f50040e208505075002c0c0c18614007450308442c2d076503c14000194444d01402200d0070b05100700318262903c0c0c400b41a8003800e540b1460b9481d00c01030110b4120310b60000d02c43e40381d0744242d4049409032801c00812007000219003001011106044030080140e8040800308801d9070002800d00c207a450701c0e80b04104010300e540c081000894002c6032a42820804214143c00620305000804400307200d03030b8182c205000e990414600300c003203a412a00a01011070b419510b00d1008105a904403200814050b0341c0e5aa51030710f0f2410000c3c0a10010096402c220240c94200008265002c0b111000e07800c0300d445569495504d410703501c040884602c802e494a00038000c004425003440c01d203c0c0074148d00040040c03042069460f0052070707030003034001503494140701d6001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 224326825 1250 224325575 224325593
    0x20a12020124050901030f03030605030105070804150605090a020a0905091305060901140c03150307060207150206040804090509031606050115110706030c120905070f0b0a14031510020703 82
    0x1000e80414400b44090520011503691501800007405000e48090000c04140c0f080c1c000d14003502000c3c0080c40f0601300408042e00d110400d41c3d0858002c0c03007000c1d000d8038000c0345224500465100a003126030710f40300e42401d0002544100310300410030007011001303c0d403503c0c0c031000c4130b024040c044000c8500d9480c600700641400d20140c50100c250341000303c0340012110321601d00d60420a1841190350380d845800314030158440d145006c0c0c2c1c00d40a00000010000e8003c5642c1341200c250145404030702c010190100d80320358049800904d040c00501080c014256a41e00903a440102c25084925202d00502d0111004000c4a4220f4074151075000504c103144e4488110300740a071082c180a4043c44401c101140c5414030390013098101136a8600700d9003107501c180014560042481804c0117041940d050864480c40e03a80503a8180c10411240080c0c0354802608491840c901e0360789603c011200008200b10340d50001c0c10f01c120000c2e035440c05c4142c690b0380300020444005141c0017000e0301440c1d03203070050701 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 224328075 1250 224326825 224326871
    0xf0a0f1d120c0c0f04140a0c09060207030203070b07142b03141f1a040807050f090712021b2103090a0212011113030c080604030509040c020a120201 65
    0x803040500588440c050002190b0b002180101d42c1e04602c81d0044d40071800a103035038a01d560144a00c1418045c8106e07965100c17001d8400b01d07a66060a850b107450003170781d84003114800290154414541007007103044110143c14198400c0c1080f02c2d9810f0700180f903074506269082040301c10480000b6040c2002030b1031004000445003400c1c14065445510980884044020310b100c6c00700900c4140000e00381809003450004d0014490300054080403180070701d0700e64005024054852064200c0031a09241c0b0312004e519290005003035441907582e01904448004501c003026507402e400b404142c101d4849049114203220203039004003038001000c40340210003400311a20754200e0004005001c580310010650301c90315034058404c11103920130300061a004220341c00303010708006004102180e5030540410540b0031070b07001e0104001d129850fa038440341c50b07440c1070b500103001c20000c004861050405401a402580880c01a40c20107086038407001110082031001e04c005035511010011410b0002031442c4c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 224329325 1250 224328075 224328103
    0x3080f010e13020609040e01020310080601050a0317070f020d030f031401180c090f030803060117070203030403030e1905070612092013020414090603150f0a0f1d 71
    0x107101e00300a240704070580405000640200c50010f64441e0035200c42c2c210040d00040c0070021075503486d004204200d090128080e00e0104c5c014640001020f18000d0001010303a41c200c00c0902c41e601100b80007160030b500802c03049641c540003980440150f5544440d0600d054000c2e182c0465010032510010200e52030300c0b10180c05600e0081c01070242c03000040c0052000f180e0200000380b030000e03a5400707036203000c1030b517225490082101b4404010003070200c010354001c4000780c8030f00c5609110546070710f8102c141183e0000040e4010b00004010030710940151400380e86071800c1d255103007410003985c41c5004a103c2c01b500c4561140008220007580000d5500340420b00c0502000b140180c6da487c002c805a640c2c0321315081507440d1584e4241d035038805042600e51807500004660383c0303903070b01c54460b131594002160701e100c0d0306060001a0a4240480d810703041420070b211817a01d540e9007600000841030007800300b1521701c2c0d40702455802d0703025a208000418408901a00c004003080c190a4649410214401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 224330575 1250 224329325 224329349
    0x3030c0305090d030f1d0703060e07030f170403060903030e0c01020f1b0301020c030408010605011713140c1305091e03030121020603130201141306030e10050403080f01 74
    0xb40e030011640403031164103803070f0104641c4107040000003e00303400c4498540005c1500384825031400c00040380b500307c81c42120240710201b108822207450b03903850320026142c12904174100001a000042d05c0c502c1d40829404181400d8032a22001c003103844018048000c03e136120054442c40004000243c81200b01340b00070107416460841040d226400c580790a50795518040a085007943d0a405139070418070304c101203907141c4d90741da0030440c0a40703c2031013080e01252664020360317800700310000c0c46440f0300241442c020518200b035580f00c080c5040003035518038a0003044580305141da81c1c10401d1900b0045580003044a080c612003450401c000d01d41c1c0c1e501d2005004d20269400100030042d241100c002c0c4901002c1d00d10718110001c82c0045890000f5440320001042101c0c804d0071114070680740b4000c1ea0b5810f2000071460050b510ba228410108107009004002000000d00c65002807103486040c5054602003e840c856020075a40140d8044003c01c160600308040d6401e101440e500600d00070350b0003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 224331825 1250 224330575 224330581
    0x91a0d230610021911090408030f06010e0f13060f080706080901050f062101090303020a0e030a02010801150e09010906031a040c1703070c0608061305090303060603040f060608030703030c0305 84
    0x2070764803441a0050803104035004841c0c024440c070b420b81717401c4148010b000e060b114545403801d040158400c44a20088601120108816500c1784101c1400c400c0060480c000a60400e401c01000a9440d204110002e031100700214034584420360090081c00500006c205940c203001009c0c00580300241049a560300d0402000f09600c03030000c0c596001001940c3c0c0344114000b204c1c071640624404905061650300305004d0004141c0d155004004039a000d6649011180c880c03020140c49100880c0064001034117280103124050044244003070346591402c00306901840a0041840200d00368003069010380e0b03c42040041c01000103610038100f490400c46184c03881d1903602d50001101034080d43c1074604850b860201c0e084810022500d00da41c00c50600c441c015901c0381c0040602c10300b1075501d03000e11000c1000c80c40c1d03043e507802102d00071800540958155981c082c20b200706a000140286d82441941c0211008a112442000061308098014541eaa00705003400740540e840080003404243c84c000030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 224333075 1250 224331825 224331827
    0xd0639020105060d0b07021e0c04050105060c0709050a090204060e0703050c040b030703020702060708070501050105031002040f2c010e06090f040b0403080408041a04090c0201060501091a0d230610 86
    0x1041413076074400b100150035280c032201245045000700b080855442200c1890403d0400004d902034075440444007401160380f101c1c00d002e01c0e8001e4080c8210294803a10040c42150f0036034005a078085580340700052041910f80000301a2042c5030720241e1030501c440103108001e83d250044030380c000c000d92445c0c3e20f8240303800e044000520006040404040c2d010501500319650340c0102ca99441c3c000b608941c52ba060b81c240740b0f0080c5000e10860348a4850000140810003d40c0243c40842d1000843c2c15070144c90600e03071002400f14055002a550003100f036810b4844621030780c583c040d0000186506640c648001404029940500320321840003c41007044000344103000324662083d411314048005448078944240980600d801134454044406000301d594103807480a042162042a414068a500d1100c2a0300300c41d1079019076070000e656075000b4440204460b00b60b103a040025803909140c80c1443c01140c00f2200d080b0b844004050303840490345004a20444510341043d011600ca1140580c0420 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 224334325 1250 224333075 224333089
    0x9080f0109030c1403070b0f10090c02070504110c0f0d020c01030b0d020d0609022d0603100b0a02120a05071407062c0303030405010b0a06030e0c0d063902010506 71
    0xf8008040d00d0a8407081034940e5401d2094545131903000044071594284405030125103441250004e4442d10000c1c000148140c107030098106810280c2c0207810794030308140901002d09028943c2000500e010890a81c521204020700c0d03400204403005004600d41c0c0c0c800090810181c1440d9504145c2400b402c25002d65440c0703400c50300c0e2907040b100105080d10b50314015024064851010790701861b03401003803500c243c0c4160700c255062a0046556907012400040052a01055410305c810429201c400d02040d00d0f801c009202c1400070f4011207260580d289242ea1030341d807101000c00c001030320200d00b200401820a01d00f2140d03025800240a031035003001c1e402010510b0441586d40b012241ca592828802c000a42198400f613010381075990364a0941022070203850700c001c801e4000d8800c081e002070414031a202d030000d02502140900003440d02c1da001c00c071311404002401e581280c0d986e0900602500b4a50a180c4884810400458034500c03402d5105241d40c0403000b100156410002002016030703880c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 224335575 1250 224334325 224334347
    0x90901143303011803020706020d09080d03020f0d05040f11040207030e13090206030405030406080c0a0c0312140906041203060503060c0d060305030a09090617030d24030309080f010903 81
    0x40c0c450280440441c0c0000d0141c5414091a9000031000519200740340d0b003c54080c0668825400311103c0e00906c41d81104e2041f4a03200300d099540103c259061014403a8008120a04403807880703905086051541d03008942c0c0583d8100d9240c0c4040c0444c004028182000c100d000004803400c50800c070103500c014100c54101881503111b044041120041d1424a51000516a4001d8801a00c80ca89454200c2c1e91b58020b0207004042045203000410605a24080b20805919a034850300071199554080d20460300c21507004030700c59194040740b905061840314480c410707070160b00200003600340340c200000c0120048009408042c101034003403005440c0014415006590300d058903590f0761341594040020051600020018080041d41c0c0007030690101c00d170801d40346189020015030b0343d254a50400d00b06299004880da0b0414082c918080302e856102c0d0003d2b86000c54142e019041400b04041003035003d420407000705007441018480382d0402c00c00615200c04d1500204000203a0342c0b8050403024410b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 224336825 1250 224335575 224335651
    0xb161b181a2e05130e010e0108010c0f030209011716031a01020a02010509030f010203010f03050c100c08090f130c1106090601170c0a030606081c09090e0a0209090114 73
    0x1c214000b0360315204504448180800705907492505403079681d0300b02000028420705411000d99000490515010b1040501c030000e03903214031044019400098000c0d40004641a040c803107081196800b21540e1560b0510500c00d010040f10001c120000180864100f40c0240e500484610520740550341c000405103041071702400d1070303615041c40d00006441c040d10310955118550000c0000507160b51900b0f10038050343e1042c822380f42c14400790301c00d20400344040d1488030005038003e00c101001c034088500400445030701804861012801c00089400f60a1200440c1d0480741e07500400b0810660110582034110b804001414480c1001d03d891a44c403801806000300d140e1600c50001c00030b1104210900200001806602d0740b5a03032410410000c0195104004640c062000c0b600180c031780b10750002c40e410360140c80350f014a03401c00490000414421940340c603188904450f00c0003580d22010440d1040c18150000b0400768203038000c04058810140040d04600c125040c804a0042d0078650b9071400084 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 224338075 1250 224336825 224336899
    0x90305151609082a040912120e0303060d0303020918101707030206220f0306060815011e0b03040813051c02010503040609120f08010b161b181a 63
    0x41072495844c1041078200469200745407a108030200a00001b8590083e03504d5100e01080d01e901c5078800b4240c4680c0d54226030580c00420001d0380744e00d00343c00743c000868002d10b030050501c0c814001186034000c28031145840742c4000e80070401000f40d000c02e000040c0801c1078100d81c03043c0304c102c8401c1e920405400004c0c0b003a280407486496030a80240b101c4121070580d20031000c0203685007080d4650030602d01083d5a05414030501080103280000c0003c01d5218204030240140c4c41d1850400c0303c0e061508422100b1144000d0006040060b400a14041d50160000c2a40c0d82c400f50300c1e0f6914008254000c901400c0c18040c1c091480c03800d900d9609015030207090807507403681c0c0c03031410000418102800801000e81c1140c2001c1b2507500000f01e0140d040a500d484550743d803110130107107980c081c610990079104d101070801d00c0060f00d00d0450b8540d44a2000d5280c41807a00d42c894110200503400340101025038507444003c04c40020b81d10769140b00025030300b00d10640c2d494070050029580343c28041d000201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 224339325 1250 224338075 224338123
    0xc0e060d151203020d030b0f0f04020c01020d1a030a0b070311041a0306090a0b030309010507080f0406050c010f0902090c09030a0b07030c1404060203040e0709030515160908 76
    0x1080e005181030540d810400100780382c50b4011520841005076040d001407040544080d8042c0c040d214243c14110000e0158043c4c07549001046100c2e9022846150000d8082c00154a180400d00103403c040d5550f000114445180e41441c1d0b8414041d000268401d030b024080000114600d105030507000004c87c42d0214280e02a83c40841d4244165844003440307910b201002c0211035480c0010718003400e401c41e121245c6440d0f0342c03c1703913064424510f20030354942c10400c544107080d801a0010450079101c3c0808904281c510704110000c1e401c103a10501c045100062040d041d43ca0a1141449503000e08ca020441204944c0104a15010040020440039400a2550b4055408000b581c00e1140c1c80a590046e034582158024003800c0c2034240003020412503500c80111540207426035040d0780301c0b0fa00550601d450140031940181d0050003e01c1400400c050201c00b08109110140008120161410190900380307000765444920710b281500f0051440420b02c81c01101048034070307820501e001404404d85c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 224340575 1250 224339325 224339347
    0x4060504120c0807060e010809120405010309020a05031209091609120816031e0806130507111006030309080c0f0f01021603050a0b0601080403080106080403050c1b0906040c0e06 78
    0x10341d40d43c000e18036134840c65400144482e40040040c03038a020a070303214034003a01c0300d01401c5e80d900f5004a2940f40100180000d00040d407003a401203250900040940700307025540c03004070703081c580404001c080c0180005440b10352810035510b0580c00503c3c01450454108000000501110b41030090a40300150144c441043c0720030303501500c2c107096080706002515075491401808480c032000f0a0389800d0603c480e490541c901031520103101d004080c0010703035071000c110f01c50001094018044010702244112034410a0410080710764851141040040c0003821420b01a180c400154020541a480140c06a07940c0d240c202c04403848040039174040c0f000010403c0180e04020f101d0346004184201c485000080c000002400c464107401041c40314a680c5074003004440003001220b000d0042001c003401000300611031700d103440e0710a000e807a10a040401d1100c4007410034481c95004440d0b40014070120307101d858140c504036008081200c007080300091658014140c0019104140c2c460407001c0b0b6442108 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 224341825 1250 224340575 224340593
    0xb010203071a1b03090105160212033402030702011d10081918060c05040302210319050d050f07021b03010b060a09080d0305010311060d0905031812030406050412 71
    0x442c03e407401940701c3c503114050758002c0c00116045c409000c500c445135040f99002140e940d45400b000390f8200d11355542c0381c40b018081d12025001880b040c136044807400509003000104000b03200340d54003440e5500f450340001400311a40544940072981d4400318405140d03903054090042d0211410410415a0703030b034607041e100d12264004644a0f0341450b2101c04501c00147c40c034045544603190070051800b452700c0c101c41d1030145000094200c074014a1a0a1010740720309040c0b903022883d022a441c000d0594410222590390324030040101e0000b04255a8182c0381f401245c4c0e000709402c40e2120145040c01d4029580e1180b03140b01c1640300921810540640c40a41009000c0c403809004243e9802e100c00c00184042003900c02d60740d45010715825002007a1203402024107e035040400c2d510120507200c20041e10764406020110000d540d010b50000103130b414800307450344407699020580601d080c50f09103d400032810504a10311f4008100a2000c51f4000f8180d8061b0b42e11072100303561503140c2d031400c0c1c191 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 224343075 1250 224341825 224341861
    0xa060b0a122301180212060603032218050a05071d0112110301260d020c060f090a091b03050c12070c0804180c020a03020706051806030405010f0b010203071a 69
    0x30f0f5003400510801c00051100d0300c0b030120b100f5a44801c03150700a00c2040d0b01c441c015645583d140c1c002f04030320381e01c8611a10281a09102c080c0c508a840c940d18107415041008407008204005e44400401c034580c20a40300380765000c071040c10440c1e1103800307120308817140c054003909132030510500005003814948075074001324103c520072404030b0740c0b56128984000440f668254544a09102c03543c0c1c6e080d004000700c0c582d070394034003d50014101001200e0400025400685d95014801c805115400090380c403134108d00000d2100b1180002c1035901d0104454810580c08128018141481d0074011046040012684007418600120a0365142c0c1041124cd00114000c0901410008070700070132030180715505461303450400c490030480030704845c0081c1e840d5446104050050780164008100d42d900804c02003814020001c165865210b52900040f010b070420384054a00f80c0d541c1036002d13200c0c1803034403442034014000d00040d41002420703518070395482c081104003a4541484004518003440303110000349 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 224344325 1250 224343075 224343143
    0x6050d081306021615051c0c0906020c0a03020d02220e0c0a05031e030c0111030a050105060304022d0406060f02100c050a050c0c030a050a060b0a12 65
    0x250104290500c0c0c40290410410803003030801d140320004949000085130040102c226034200e005510f809041e651800c50b9208207000e0080c1005500205400100c0c1b01000080310440000e41d01200070000b403600400e600401c0c1503520843c9481801c0c1e503440c68900403254126800f034030040051000c10041c0071404241161340711221040e071003650b100d41045112800310303821164020340b50350400040140c0c0780b04841c0c064206240465000c030000c0c415400f0842418100c070f14000c408a4151300b110500d0b1902801d40d0350100911085000500070140109001c0301c810b0304608050700058400641140300124001d9145c00308044400c4909007900e01c220b0040040008550f0baa0000e0003224818440c0c0d0014000c2c840c41c000d03400f48511880c0088445a561030b030412000d035806a81951101c0010030740c500c00c00340c290791240e40400640c80810b10502c007a000754540c42c9800d40603034444428051051003d610300b030100191070f00c1c50001046d000003103941c1c1c4400c810804404503d01c240c242c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 224345575 1250 224344325 224344339
    0x5040506070c0905040b0a0c020102040e0a023a0b040902030304051c0c1205190308060d030e151213030e1018090501060e060301030b16050408010c02100e03090307090e010605 77
    0x1100b4002e4941b880c52091a0184041c8034842d0468001c03405c03841140110b0300d2283d40000414160021607014000070380380f101c03445080000c03400401724a0000101080d070442d07901d414844448007240030b0a1a6840195414064000f0903400a0b483e0300550094038002e100d040f40c0d041e100c6242706020312001d80c10040e510345481d00c441d400921440080419074480c81075000503079620a0f910200c0312038035003540d00d07802c90351551010009100740100c03042d01044092659680c6070345d83c1c0e10b0301503000fa1400a006da680c8180d000d4060350305100818145841c0c801003a030401107900b00c0c5181c91228021515031001c001c1d06901554454040711007648250a600b901241c00b40c0c0070303800302c4c0c1610007a4440294040014040005620003408000c14510505c0045000e0700036012111603d00180d04140d400e05454a45650031130340082c1c03c807401a13101c100c003507402907032902c105940d20b130703100015500d02512030010a075a076055108400b04140d445480d07000b001401e510041c040d0400030440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 224346825 1250 224345575 224345581
    0x2b051905031305031603020405090307150c1b0b0c0d090f060c080a02040807030b06030f06072a120f030204090c08010e1312080901061203020607110d05040506070c0905 74
    0x85680c9421100481c420710302c600002190601e0300052400144819805650302da600715802e100103440c015040105500c8140442ea000405006001e140300911840018144105810003040f00c840c48800681c0c3d2514683d110001c01c510250080c3d2101c1b2840c0c1c0d255550740101c880304014100c806002e45441c448a411030108030142c2c02101020b841a81d42c0003998444000044c01c0b80309030300c9a20080d5001d2041000094000d0210550084005080d55400b004081d22142841c204031640400200319a070000d05c00c070310303200d0010b0100000d000032140041f81381d030789c80d40f250092420107014441402d5481d5002c130700ca60101c901a15005100b070049000040d000f82c003428003130040482841001c0005107030124894400040190051800b21a0708030811041d103c44901900140c0c4654079410003282c0250200c002c0311800c2e200350700404051408040090800403400381a0410b43c0043c3ca4140305103902030140e509950084a4895030b030022032402c604401d405030f00420340310b4140020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 224348075 1250 224346825 224346833
    0x7030e0a03180512012013050d0804270c031401061b120f09050315060607080405030303070e011706151b010c051b0604030903111306031b052b0519 65
    0x8005484542c6d0f0420841050580760322000600030303c42c2900104119400030092031400c001514044c5005502e12442e258480300e602c65903a484089010000c14003007110035102e6414817400d0014405440d042001032501844a07180c120f041c826001040305420b5207090009084000c545031039448001c00c01d402e407220b0380141615100d0040d410200701c12003400105801d020940349040325510b51142d0705559034104000050b001100140c460420900000c501500c041004500070b08075500d4040901804000041c21491000c48a40d1802c07248010b025558a4107280304030801c003400c00c8242c90740291001031aa098005120208a40c2010080f01615030010700815400c01000c8071030200c6041c3c005816a918410354000300003440e4281c041000c80c41100d44141130b1f41c0c000700088074080618a200e811740d40d05400946000c0f01100f2038010302c0e840c00740450014007065986904170300c00322404118541c0303889400d05a18007a0301464013003040900c0b8071031440c00b4003100404285480c0c24 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 224349325 1250 224348075 224348081
    0xd06020a02010b0d150c0801050d032003041d150a03060b0112060f0f0f080c01030c030b030313170a030c0611070b04080904060f12020411130b030a0507030e0a0318051201 75
    0x34010b10031480e02d013000d006c59104140050503941c0141c07011031035401c5603400300c624031514100b0080c4450700503640e54008205100510040c000c4c4803c00c440c0440c2c0300b06600d000c0b003014000d01071a84611506113a01c0c2c403109060000c494000c1c500046003080400161030f8901101240c0c591030b841c0100100d80954001c10003403e5034001ea800090003900c8402c80e100d603000c18010b05000e944105510301c10f543c40794000c9254802d081c940407030302c00b032201c01281c91500141c01050790304000c0c820030301090607001c404801c0503010f0001000714540341d44010700310345103618000c0c00c0142c40d0700200b1582085402194200c2d544510112014a4a800c0c800410781190a055200d00d0411070300244840c81e440404040d16902480b181e8501d066500304401801c0950315a81c1d410018001a440f04800070603040040c19001d201c2a944d191090101c011240000d20103400d0515000d41c1d022000c000044403500142d0504120503d000d028026001c02c40c0142d0005510500e0803100028207034040d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 224350575 1250 224349325 224349353
    0xf02030a0501050301050403050304060b01050423040b01050f09090630010c0519082502070303180e06090c0c060c070b1501050307030c050405150c16050d06020a02010b0d 75
    0x401c8543d88500c1050f09a80003920046d0001d8070500100b404a0880c3c0d1107043c1006050410b54905aa1042188101c41180d940034801e0100d8940e404c0700c0b402d1901580502070400d117000c0389003541d88074210003e4010505d00c0380c081c01402c00021611784030b00c68800c9070001c8464502e8010307004c000c154a524104240e0811140d400c000c0c20708103ca00540030b45501300703517000981c283c100c040d00040310b000000409445400000d02446d0ba001c3e20300c007208880041040d80604011070850a000d810700328982600e034000c1500403400c01c207502c4181d0180d60820402c44044416844030b101c0c0241c28040c031030041c10540600c1003403020100d440c07001004c441c0d2065682c101907503940c00820710114140c042d011f002c142c0800015194038400d9005248244950501c5402c4c942c13142d0100b00322000d140318282ca05a800076081c4400c0d0010030008218445010b51202a0790901d0b002c980b0007855250b00900e015004500380007154001e40051004410140ca060780815107414180e02c1107036070f0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 224351825 1250 224350575 224350591
    0xb0a0c150c140c0303060103050621010b2e03020a091a040314150f06030115080a0b0133120906051b040b070b041109010e01090510030f03031e0f0203 66
    0x212040d4107140c40342c0c10988460480c41c5010350b0650f44c07010700550107030a0040009911410040720440350507aa07001162007500d20100000b881c002039014080016925200000e28050019990050180004204480a04501d00903032201506001607801d5201c8c0d0f080400d0403009140d1003043d03104401b0161017202d0143d070740c0e403900c8a070105a8903281c1c2c2007120508007480b0344100180b4040d86580a8a410820190000454101502443c1c1480c0c055030461f080507000141c6102c1845400706819015040760614501c030075103548a000b1040d000542042d00300e01c20024170062850050302072600701120104207104200c914501140280011180701000c022262103e802d914504019182070700c11040d455071800005448030701e41084020f008403602403000821040c6510f9401140b0f00900450800c09060350600d0b0210050721001088008101498601000230503c1c0d448414295034050070b00140205400c80008502203603a13900c950100d090401c0b40720041d01680c0150310032500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 224353075 1250 224351825 224351837
    0x70e0a11040e0a050c04170106051003150e0402010c060f0510060305100306110f04080604031205060906010c05010f0e0307020102010513211211120702070503070b0a0c150c 76
    0x58600d034501140503a0042032215000c03a00018a00c09603644415044401804054285a44d94007040e54071800380700d000303400da51200f00800a50078035280c1021041460f003004c0c05445186d1301d420b8148142480340640e8601508041415039014184825015030082c84c1880b0003218442080003400045d14188031074400c2d10030028509100b4841c042c014100c500c400f4910740d00c1d5880740800b03400c00c1520a0128281001801d0040d0556001403000b4550b150150201d0b29081c10045e05d101500710f0345001740e41c1404200034941ea00c01041940c000c00908105c0801c0c0518103149004002101d040661185031840e20001050b00001501616100b60700034401980e0f109500001d03070542c10001003540050201a20032002108046c158041692616520040070481e2070825901148d007891140c03000011245801d0190a0085900c0403250005044551501020030340d80c20711032217042d0840f04041000041d40f03200c1c0d0752400c01207400040103004000144c40000080507054071801c040781e5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 224354325 1250 224353075 224353091
    0x70f120801030302061302040e03040f03150504022416030905101103041a070b0f0f0601020316030e15030910061e0e0a0914010c09050118090e0f070e0a 67
    0x803140c0d110605881e03043d4050b00043d15203001c101c145416580040364800d0302c1d000119184501000640001d00c440c100c607015440c55170510614003803401c002411050304250411000d40c8502022400c6c00020301c9045044c0040c88580c020035010f1194040301c03903564a5030302014540e10038030000070341e46c0490348076400203c805420340b8003030341c080030490301038009210401c210f456111088a41c045586065441e00c480ea690707a442041c0300326816004070310a03406125000c0100c400050b4081d07420300080d4a440203202c2e820070040c04125004080100c242003803c0d150320740000b151510544038440d20780300d003040c1482a03207540783c04070010802840d28000040c40f00c0b4040c40c403c03001140380005005242004540021204001d2088001c261100c0c0c03100300003441c01c47e825119a074101c1c00021429080d60340101440e07500e17803000381000001031420f6540000314030081d00f19543c460780040c1d14046290820b0528443d00c03410a19030258443c000f40d80601076411030f04c03421141d002040320070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 224355575 1250 224354325 224354327
    0x3060f05040b0606090f0d0c180203070905060c03070605090705030a0f110312030412230a110606211203090a1719031a040204061d0a030203150c0f070f12 68
    0x10140c5444582d100084144020300c508200c000c2c0182e0601a81403100b10a4907a0260b90788190302027900c0e80503c0d03002040084861380410380750040c110459403c0d01d48500700e4010707a96070090300f10180c82d03da1b40b02c01041c070044c01009a00c0007450003500f40c0315180e0080c1001320603c0e100000558807980e414198000a107030100d400c2e074421102480c82400c545480d160710035089043d03801c010a01c88220590003094080c039a0000c0303400f0702c403588140d803090b09031030060546804041110080c0d010700e013031190b241d58031441c407400c0904036240d200314041c18249051a20248200e4031910b240d0000c103000d4043d10102d40702a1243c05024022a1442c00c030f102004988512a0144c1000c852240700c020b07924480c0d00720b0064240c030100010340c0d41c00c40c44000340881e8010751016011840d90900d104c4d0600c11003190480e1564100d40501080340307590046a2140d40c10001e0240d80e003000400541e03107140a60a83d04402014800c4944403001c6140c11080c03483c0c4000141c0b42000b15540666a007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 224356825 1250 224355575 224355577
    0xf070503030a0525060f14130210050c0102070512030123090115050f030a020c1207030e0d1b170c04090503040510140403060b01030f1a0103180501110306040c020d022503060f05040b0606 82
    0x11070380c042c01c0307000010ac00000c103e4541e00f1107204070b11595004c0200e013000c500d007001035034222802c80b500315503a940f6000c12100072039000e450000780841d449042c0c0c9074554602190a0442d1070109000c104024440001c9486109604555114030404010700500120740e90251000041d100102c9100060f101c0c412440c0d030141810060010b400400d02c0c2045080999041200c24880c104480f03100c8560303500b007820784402d03804c4541100003c018a818a607010080e19a2419080c0d900f0807003030426407911500c0340329502600c1c0c02003038101802014103108085480380c101c601c201c50785d1211786a18115010b40760784020580064207010f80c0207408211441000c3c030301080f000500d01084200303001940504070b60503083c865204242071550102d842802601711110105044590340d00d0400d0400c41140c05000811003103520131491000b41640018440c0581381240e5070000ca000780300010441c4501c85078100074080e40c10302aa64114520a80299009910808889072590b07600e030b003030050b1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 224358075 1250 224356825 224356861
    0x510050628090209120303040614130c0905090c0d08070501150b090f01020f030f0304061104080304061b23010c050f0706050406020d0501080f070503030a0525060f14 73
    0xd03142001e041001a403074954000c15681c0b01c050082c00014019144440c15900200d0701076481c030f5122402911044000300703003685e000d8100805141002c021740c039000e0300c20001b8056003030340e190b540b0081400c0d1042041848441c01004145405903003091411104507080b56a00b107425608100c0c15617400130000d44400103845155640742e013820401010460000011654141540541d02e01d4231074081040c401010900c030a6000c455580c1400d140c0b04040700c1c1c2480d548904c4c40014001031000400c040101c2e0b003210400d2510030a00c00c1d1031121041c0030440c0034001041403441204106010a05601d4040580381c0003008001070f2007981029980d0f803144030f9040c81807880800241000911561006400c103004880050404c81b0541c400700889000f030b0010a0f56511804c100400c6200030858680544006e07030186042106c480805003040c0190140c461241140c0503d0b00759850543c16180b201c1a0410410b11000e040d07010008006c1401070029a4038802800008295414035018010 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 224359325 1250 224358075 224358139
    0x607021915060305030f04030b0f040206070311010b090a140a0504020f040911060d1b05190804080d060b0405010306080f0607051e07050615040c0206060609060705100506 75
    0xc0d94155581e40e4072407111551104000c1959184008400b0580802c09040c01e4802919a00d99076815810301c3c0c903c5120041c8000d1907a04448100b10050300c40c1000e0b105402d5240c2000d60706840c020740c5071405410811a059000340d039000410442c0403250304117003103201e41206591026200e11340391342e066490488010703400031b07541d0101104500701503000c0c020b101e00811404c1200343c071400010348580e00c440c03500c8241c2510760b400305214204032040d482620400d0b040c5503190202079214072122102000301a428807452000080900a0702000c940c180e0480100c200040e588881204289070090300545001030700e402004038181c08005280b0307009803505402010569234910342101c0c540d0088038020008006242c1c503c907500d5028002c1d01855201c0c10141226180c01848600b50035454510a0b1040d41041480003000c0e4010420981242040d200180da680c0e1804c0452007521603450001d205101d0301c8400410006e60794040c1e801094101c1d0f11507812000300310707087c6864a80000c01c2d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 224360575 1250 224359325 224359363
    0xb160b130201170c04081204061e120207022101090c0614030f0c0903070303020d02010c05070f1101021204090b090105030d02150403030b090c030714180103051012080a02060702 78
    0x5180c0c2c0820345081e81d0300100c4c4810701d900e080c3d1034a080a05180c0c500e00e650018440c04a4140003083e0042c802100201c00c60480790203e020f00107005142502500c5210b50865000500e030095440301404100c0301340b008c50710a01d0a80b41c40100c2c80c001e0251039026103110444810100b0101e1003050144c03161020b60411350300303513154000344480031400a4001c514084d006c0200310199182445082d0066000e80c025014555014038082c0c25100c0c0126090100042041a04006103107480201109a000b6070b4036030400d504140181d1801c8501109038244200c0410300142141241e00844503c110a840f204082e990b202c060640d070390401e140c0d00c4096008003c00f0a445079a068642c0d90060003890086240000e41000c2407c08c40c0984060000c0d03440001000a86500804a01c22070306c016035038030b4a0321040585042095140300d50050406807920041045003414521590113065200520a0980c0301464076105650001c040103025018040c00651100d001094814690030700144c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 224361825 1250 224360575 224360597
    0x203090915090c270105160501060b03090304050f031501061110050a0c021c0e0d210c0302100204080613080d060905150306040203100504020a0b160b130201 69
    0xc411150010003681c0684280700c40c0318181d5403080480760181484003015070366942d5205940c40f11840000500034010740010000640707913440811500d4800900001ca40040840e00e8614058070b204d41c0a0212a02c02100740840f6003004001081142d000300e5403202d515400c5800e0680340c201c4074603004042008480104001c40c040c40c1c18a18440010007960f841c03140c0010034408445c1c0640351050401e50f680e040580480d01080401c4645000c0820211300303e40c0c9010007042c0c00c0401c403105006040c03642102d0104110074a04400c0c2080950350705090007100e070002000f07180004001d60051141501a001c1e84081d40f08540a0300c0240c1c0150451790342d800711004940c03009400449011208206040350148148540c90140c0061a40450181401051601c031080701c042850303c01e801c1682030000607a40054554004414424041021783d66800000e0180720558400c034280c1d03400041548081295200c1402d000303206441041c8982c45218103001c3c40000c1010080c04243c1c4a44c074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 224363075 1250 224361825 224361829
    0x8160308121e090604061103060d060213030f1109010e040804060c030e04020309071e18050a02070227010f080a0308090304050406080c0a0e0c0406050a17070e09070e01020309 77
    0x8541c0c84540742c984140d0701040000b41c14207060341115010140c1c1c0205003400200003482c0182c0c0d2a126500300c0d000e0075820003100203800702d0000100104110790004401018941016080740190b422000c00004120701d410080e506090407040188030384088400400d60500c0c16100301c1c061a0440340c49400d050404009681e40001d0510503010301803d00c4c088081a07807280002d512031000c140c041c21142e8507140c522140e0300c5481c03401380300b402010101072080701d030340301d81820800081c2500803983c0d469880e0b000c07000b4170800101130341006004000c4a849900350035140110312242d0040c0c040c40c2c0c2d07103207200b03044802140594450383d0011003140004c0781c865011a5086518141a00d141554130800282210380316030020301260002c00900180346030140c540d00081124181c3d6009034a884070b85042540300c2c2e40605c074140036000c03403404401445443c00d51424002c00d0040d0140f800e0240300a0520000804540d1091004000203017030700d4030070f2203d4801d99406070000c6041c0088081 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 224364325 1250 224363075 224363107
    0x7080414030106050a09020703020c03010c0f0e0a030c0312080709030c0302040b0f03011e1d060c13030c0e0603010c02070311010c0609050607030c1106040309050603042a08160308 79
    0xca54590b40318080440e00c1d80d0b60b0134040000300f20102d40181c1d180d50618003c1e0601c4520910345200740d1410411042180d0407050981e6400600d00d0045140c140701c0e00000c11124140d0006000d4002000001c8200244440850801040c540b0f40110030fa855000c21a0f400c1d1281c00000e09a4140e441c00b000141029000000882c40c01041c4c07036840040100800c1c00c5a8044d00c0400a80c444400d41c0d0301145580e1047c00c101c1c0ca00882440d1180810910055070f800c0c000d0910450f220000440a8003502c01c544814051640b1142840030349640d80c406c0b01e240c1c40c0503904940b00e5460080f0144841e40006a6002220391013101300000340d018070015101d80001750410795920381c8841e0340070002042801001d10840c01038400040b200800c200c01407007084010460740c9140e0218090101190b0860b81d00344c1190300865485590f6690f5141900d00c141e2600b8244101e030300c030100c2d90b0900042e403074030403420b84040b075003141c0844254400190903601c5511024003084000c020a44643c02000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 224365575 1250 224364325 224364359
    0x1006031109031606030b09090705060a020f010218090c03190b01020709090b07030b03030307080f0c0c0f0d110c13111309091505010e070c0c0f08060406050903070804 73
    0xc0406810024031601090a00401c00740c41100315100110a018580e0103110b00010290291f5080b40c0d10b182403d41c5580e654594041e030fa200c0e1401080440750300b8420000c410340030420000035512000d550b00e17504105400b810070b80740b050701c000c0009100603001a0a03031b8070800807200080301647d5103c000d00018088582d00504500406e80045400701d1907010b44440944a40d0012440d0701d0f058800030100c0c1c615480280c400d80040003400404c0781e12044441e04183c02030b03154002a121800b40103071a12400e6440310f014000c0503000b80c80c1e10800303c0c58000c0340c01c007034554036002040d07490380540b10b07811a51300c0703640908203441161143d002540072000b04844504400d02d401d802402200c031141c02988200f010036200e5258404201141d0740d400c0f03807040d1100c418401035040c0804209400002420b240400c814a000e41c028010307003050349001080c0500084041503120341d8940d484003421101519000d01b0200400c0180e0b00c004112600190800c4115081034145074140c21403110103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 224366825 1250 224365575 224365601
    0x30501020a0e040b011b080c030403030e190302060a0f0306320301180b04050a0b09060106110604120c021305090a06060e060f120708030307090302041811040902062503090b03100603 80
    0xa10600030000809c100601c0518003a89030240110038003010806da0030f0380382c0b0703203409071080866007000161109030075900001a1414108200e1640d0b020072402440540d0040c02840042091400c000c120104403001001210803005001001038040c1804d8a105010f8203101070b1a4015450114115041d4660090300c141c090b07508034005a01c2d000e00040050781c0f440f20711b420440040002a0b0006002c41450002e41d0141400d40f501c0c0d1100502450100b2400c000e00480c1801c5408650700e0703090000c070700011a07008002ca420318103d000c2d40d8001009046540502d0240d0100d12107114070500b0744541f400a05641d0719520001c18002e114003640d45180d0140f00791600840e641c038050016500c62440c82d501d0501d1540303140100310139161720b5000c0e8141041e43c114803101040029481408203002681c02140341d00941c804621980f003000c00403c030201034920494440d250140c074104c4817a020750386a80d40d1a807902402d0256120584840100c2c01501e60104036450098002c1c011090341 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 224368075 1250 224366825 224366827
    0x90c0d050607031a270703050103030906052d03060f0a0b030a02160b010b0909010636030203010911091e0a05101512051803090d0f020604030501020a0e040b011b08 72
    0x5081e000c2010010303c0c002e40c1041010040c1c400134500c0c0f5a10000383e01c07042500d010708c91949551400782582d0700c03d02500c81002400a240c0a10b40458282c10b084450341100c1703030455002c03c0885892039007050750454862031040100340090716141a404083e2034442001314a55100d020407000203521910f5864101c09010381b07100c020039992f84040d4028010b13035904a590f80401401c000c0c440105820800c14020480f0001e001484034849000c120b084184241c03e21082d05001c440c0c000741c16500083d03040d820490058100811004d10405403002070ba200c0b6801e40f078000300488a544030848030a050140c0030001040070000f070b0492608544004040801d44e906c4641000903005594150750118800610042500d1003603c28103900214840c284003d03903c1c2c00c2d00a5460b8407038542001d209158000701001030111120000000039030041c041584d0320b9603850028044c0d000b2224400100d207850036250b0b042d05250040c00c89501c3d05079a03100c0303900306410203030110704610102626001c0c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 224369325 1250 224368075 224368121
    0x41a07020111101407030c0804110a170c0f040e0307060b0d0c0608070f020c010c06020d0605030a030c060e03070201120c020c060a0c020a0b0712120b0607030503090c0d05060703 78
    0x1010b02030a995a61080c00120b011344090344a84900036000c4e00c1d20013007500d0880a07845559108411031380080d8480191181a1540320000c0c00d99a0381c0c5e004600c203040160304414480000207800c15100a09035001d1070408652020041100ca1066841d080d40e00104280000a00ca5030722612201c10010101e02e40c10005407a40c05100e500d82d0442d2000c1108681400219a0400f51620070f08105100070581c0c010003000081000070202c2c0c00500032070b004140410381c40f41c3d9410803c00f4100140032654a101c29060050194108290940c0d00c18070b000d000c01c04070b0001108484a41c4d80685818058603078000242e001070086c14950400c5000307031900c141c21540e0b090014016000305a55501c0c13034852900401100180a0b03104440e1080100000c0300007a40010240c2c0b1825007905040b01200741100c02d031000b50004541040d400040059460101034103c0301560060060108880c2c1e8880401c0c06d0040465083d400507140e98030480c00900c00900c2908140e042424a1114414903c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 224370575 1250 224369325 224369357
    0x10507060e030d05040605060d02030c1012090c031a0c090105180a0605031501050405030a1202160905040b07022109060f040b03010329011202010e0d0c0503070b041a070201 76
    0x1802503043e00302d540c2e03200e00502c02800b2013409025009801210070090141440e0f0019030754800c612403060051504004240c0020300825100300c8400500038241b0150200b07240a0700100310501003228214019035040045603401c00740144a01c00c01e0300e42f07a2800340080f00550300c98001880c1840051034480c0c540105844401110f0014040781d11419101d0800500074107814446803c020f040084c1800b0811843e0340000300404140d030440c4103949142d040320400c0742454404408580500494480080da9403800d50040e03108a000f0903007622182c40307503c002c0740c4898594440600307641c980e000c0200c1002600001780740784103000788040d2600c402c51940c02c3c1da03500a9442140000e401200404c20320401c11340352011004000b00c011203c200c00c900e038881e8244107004504000d049190060f08590003071001c00c0c036410000b032200c03200a01c1e5240c0b83c405608180a610f0003401020400a0038440d4442610b05442e108100104c4031000d041c40116035400c5a83d059040205030648801e4131 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 224371825 1250 224370575 224370577
    0x1081306021612050703050f09060c0607081e0402010f081009110c0f0d2015040821010f0303031a040e06010f0501051903020304030333080318010507060e03 69
    0x100c400e420b0a82c1c840c000d0070120b2084809404a034103001040000e0800aa480000c0710840710b076852185480e1514840443c88a00890900d504940310b0b0314284000c150300030250510a15500607500c0d030005c0b840424010b02a415200240400c14081d21802100c0c01054030303a6000f00e00e00d0440c80d800e81d540310340c00196561080c41c10b040010000f951403841c0d8050281d4004044104010b15420b41c16000c000c0c030007400c110351025801069641e01102e0a4207221003034042121500d04030040c24642441482903014482000c040407011000b0200c615804002c036048a1580344407100013455030300c042d07010b0b00040c02c001d08031101c0e800380c7c0001d0381c0d070718460623000c500c00300003c0c0299130511549200c500000c0c0c00043c1400401e04c400d000c0603039a070f00c2083c900c1d45180303809a12a240d6240540c00380c02d1200442404240e0300103e2641c81c1d0354252899081510300080300b01c46030b5201c92007512849000440c86660844210038011540500000c00c01c452040e040090048e080810316829 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 224373075 1250 224371825 224371837
    0x120c0b070c0203060c0405062205030706260105010f121103010306050103170903100b03031c02030709092702060408030f0904060503030901090303030b040e030301082413020108130602 81
    0x8281c1080500301981000c1000d19400f1101030b07141c5103041c1c184000034202d03000d9120110320424440d08155600060706030044010704001d011180c1c21a260f00b0054030462500b07030f54424895604192000618006129a0403604180c50b007076100760184a081ba4840c2d1a8030401c06555285c4500c000319081340c200031f5000703600807540003803654114541560743c1568000402c131100ba007440402030541c1c01060400380d005c44101c1c0000c980c00700784007181c21809100c404c5040c65900100d8814000b40d660011417241c600e81e030324a2001364440030f580f01250416111006422070009400c1449800280d9800390741c4e000510081c01c0c50360f01c0c1c40640c5160304c102d10350010740714081204160740c1400e00408024180c21005582001e0311503000a15006142c4400340070036031211015429921648c1c4400c09001c5004141c1c1c0d525030311001c000e0394480900002070781c020b03819080203440040100c002400740015405440c0000015001141e1410018100d120350010100714040003030103070b20007044 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 224374325 1250 224373075 224373077
    0xc01140a0b010215010b030609100801020a02010e1c0e1c0b151f080a0507030e030f0711010806130203060609060304060506131505131b080a05060a0b0403120c0b07 72
    0x326441040002400c11510b02da02941322401d10006000b04d40100b8140d07a4800c2003030314803c209607558104000380c40220f134004100c83d440000e02200e05a41900302289a000e0042145c0c0700d40d8100e0003824100000c9604040001e0044e43e0742c01452811262010060929504819800362a902d80480100081d20301c00c4182c085d0f0001030180341400e000301c0b40d641020101c0b100071200300c0e0501406050000f00750f04841643e034800174100c28000c1c1d10152524204100311303038803021004a071440c2c5e64020102a101e0000c8000030300d25540c40740825a1040740c016126091488480c80104040d4001405482d440042807201c0502c03515000045d51049000c0d0b5800b16540c20a00c042c00f07201e10024000042c3c0340d00b80708440f1602240c06a401044030825609943d440c0c116841c03450003010903802150703800001403100084035900002803406410010400c0000da101c0c02e0400c10003900f140f18081c2000b03030511041000c9020715018510300921402d040000303020303580c0c440e030a20108a800d64 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 224375575 1250 224374325 224374331
    0xd09210c060507140312040b09010e0d0302040609081c0503040c120c030b090105040c060c020607060f060509070f0c2d06020408100501050904170d0507030b0f0913080c01140a 77
    0x10521514003880f0141c4c100150165141404800301242160700c0100064a8030690002140960101f50b001c101c1c0b0a1126050304c0601216284c0203000c0c1d0300a100e4100015100c0102003107400c4086004c544aa00c400340a0300c456a00c010261800e40005009443c030580d022000101c0221484e500c02140307100d0600020380c20f0235890503017808540a40020004d84c544000c200016160790f0703a25055449c00d0520b040d00340399a02c000b405900c5500d800801c1c581c104038440ba504811a040030b015aa03045403080c04c1541d400a048440e55074002200c0c00160f03469a410001c105170341c6c20219071901000c480a10700400c102661001c0803110700841e17a83c0d41c0041d0030000d40740c05011107203003540009000d0029516181c0003a04a04000e44041d1080c4005559041c0c00b90000e0111068945081070a000a05e00ba01019009110004045002c4e0107107103080b9132240760440ca0580b003001100301c80c00c224801078983c44d800e03070008084800301e0340d40c41c0300300d002d8176000321521489860505008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 224376825 1250 224375575 224375587
    0xf05070803130f120c18020d090c0e0108030309060c0a090803070f050c0a05030a140f0f0607140703120510180204030c08012901020c1507020a06020d09210c0605 71
    0x41030703014895408055050300003003501000500022650040f83c0e120710340303507070340f9207614000c1b2000b48078210444000928018481d410010700d40301510446104a65080003603071b9407003589849104c01c40d011002a04188002040c803040b4001138035030311280d4504825040d4035603001c0d81c5550302c800d005580031511121080708000d001c00035409000030580b48a2861443c21010a644280c041401890f280658000c4010f02004010404003c02e501d01102d413452030540300151a10301c00d9408000050014040e00f2400c100b0300215003140c2d034103a5403400d645802c0c84081c0c00802c0c001c0c11a90580d80c81900004060208000005140080c9600184e031140740d464028007140499106526903410b180c2103910b2400d07844a1000c0c9402c41d2410340c0420945000100e003080d0b68400f440764410703980c0c0440340c00413008101804c21584292001d4860684034002a0780d5441400404000115690300030300011056030340c24241552002d801c007060f4200742d030750074000516039041080050030100302 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 224378075 1250 224376825 224376839
    0xf020a020909030c061005222a08070f0f08070c0b070f020c0a0608011806030b13060c0314130c0314030c07090c1211120903190306120f0507080313 65
    0x1030302d4100186c02c0301000c2d45450600071032000c0000044c0c415035807904440c2e0120011440d0030200280d0341c1d5900c1c01400c80543c00c204044000000000c000298211002907171440c050071301c0106a00054881040c0b0b2055007030101c4000c01c004003400104050200b03904001045000312500400c140e451b80e001c5500d141e0002803911040c06103141c4100c6050381e0402400381c00585007419910001d00d2110001c8005550704050422684014095002c46081100e800c00c130140303200e11a48141414406065029406c42c259480039000040d0b12601c00c012410443c4c02250030380406224101030010b096494582910103403184021124a800c00600fa80d00f092080c410800900034411f0b0810000c0900100103241c0b5094240300a9040d9442041c809070024040540300c20007a104c40c0e00405244c881100c2e9202c2d04110f2040c00108240800c90b41442d0007402208141c8001c0c00d0203014201013a2180c00020b610003405030346c00c0c0105034010801c0d44060005041d040c0c13040001078505490011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 224379325 1250 224378075 224378083
    0xc06070203090f01210b120304031a4503130e160503010e041a1501110a020f0402070c0510020a03090f08030a030e1c0c050c03010c0c030f020a020909030c 68
    0x40314030304106466101c5c052000002504442d0407001c000c002908442d842c0c04980b003c61303104181c11291001046c00010000e1954404407015400b000ca40d0058130f41d280340242d071401c003810345039456041c6242507440c0521000c40141c41401038000e0082045280480c1d8156840b5901c60312095080450034000a09002c05054010002c024036045076440c00c00d0080250106005190a0f010303c04046014840306010240c480d00c51600c10b440342d41000c0c0700000c00450002c40e000c1c04034911014188203000041100b26240b42c0140c900c4501088080400009611800c2e08a81e0321070401e1001c1401d4443d51111202211540c0007024501c0c01420090f01c158995030010300c1040e40c0f13400030701c1803c40c0441610b20b0b040c2c8030700300030460f401c6c0034890324101038041040056169026550b000120350141a5551290081003a03458601000342410b0030782d42d890b42e810b0007103900e02c5980800a845088000780920003841a1641c3c0245a80010b85601e010703141c01c011540f0218151418060070303c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 224380575 1250 224379325 224379349
    0xc061204061406010503011a07020622050402040510120e030304050d020f0a020d0807030306031203091b08031218030d140a090b1b0c060c07030801090606050702090c0c0607020309 79
    0x42d203100407450710800007849803005000d80322540c80351802400d0407040c1d14050340c0e80d5a5009041380e0301ca03203410503003106808078100424150640c0210001c0c80e41001d00c02c503019613034050b1030203c07921040300701900d2a01c0041c0f045449507030b503120f07941e444040034000341d400f03288038201502c403030601080002d1900054105040082e040420603c0040e0307a2000e038440d82c0366000c207000d51111103c0c1000e400a18a6a00c060119100c5000740000240d0540c00300fa2141d100302509800081440c102e9065035600b03000f521102c3c2c0c0200040e080400300c080c840390340070b00e2071554000d4a072a0b80c0740803402c540044803104c000c6502da4075040c40d1048011295503009403501d004204181c02a12648849c0320090441341e02c0f818400d400d04011a9030320308441c00b00f00c1580840d0503034200b1700d2880320154800d00d07003580096051000422003101c140642c800722403890b62401e040014a40030071403030f11000b50182e00c1c0480208880848d0b40414422507101d030b4a6034000d10744410843c030034070401031851 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 224381825 1250 224380575 224380601
    0x10c080c01050916050a090e010209100201150f030803060603091e010c09090c091e0e09030a0915080a0c03020427150305060c0307030e0f060a0f0911010804050c06120406 75
    0x10141c03e0010b612009031030021600f07c6100800c0110003900418020700c104a51150416040790481d010700e601500800a41c0d980e51b00e0940e420341c1d464003072000350307402804002d214440400118a141c545035002d16080030301401641c20744036010710580500300c4030f20381034103040e51544001c822181e04458814010a48103900340301404031420300a00c8800c040c040d011880d41c180d00700314607490098403454040d03e0320003580801800e01d8071409507240c2001800d10001024550041a1031041e4203402c5038100302030b10741106a07124001030001420302d0b441913004056081c8000680780040c4000400f14200641221141c0340c1440c1c1e03074106407502a4540c1c0d9801200d003c0801c00200001a1550302200c0300d901c440d202d40f40e92030120302070161032601c080c080c4a19a4030340e4501c400400e059024204207a01004070b0501d0050440c1955000c820181041c0c40c0209034a04075405400c41590140c45071041d01d140c1c01902001030f0b0507030402c2c001c040350303c541c1a04000070041a071080004512003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 224383075 1250 224381825 224381863
    0x5090105040b0607060507030f0f1d0304050a03120203120705030a0b0603010b040b07080706110a0806090f0a0905100e0a0201080f0121050102090409141c020d0509010c080c010509 79
    0x1140400d48503c00c026001708180d1303951002036440c0e886540015906948030105102e4020a2042000600101404640705070050128039950b008000101d0f021500050300c0d0098591460b1110194503064201510035030008002c003c91140c04182213500c02da10b9900c8003070326400c0524841013201c84c9080304c1c034000c0d0360400050003175001d16002d607412196084089070b03442d0040d141550f02030003a04401000342e818900041211152140030300b118116980d0341d810540d845204005035150b054460050341e00d8000c0129411a165801812000d402182200d0180d58407007038603004c941c512525201d250f04405088402c40d0b070b2148005400c05810811910254103210700c54060341a204040854906440000000c011087d0180c8400c2c01f03000300100494038207030a20585007505488200c3c21801024885025401d00801d0348003560381d160b000f42118543c3c00380550f51a40801b040340c0c10700014003101400104e007580240000e240d042c0002c1054185054850700e040c0014504410b0350740 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 224384325 1250 224383075 224383091
    0x60c050f0304030c08150f060f0a08060a0617010902090601030b01030e0601081614060301050d0c080316060b0303071502090a030f060c030c021c031802090a0509060108030c03070615050a0303090509010504 90
    0x28140b00d400e401c544d00312034240418000e00008ad811a4480d0711201c550700a5808005a600b0307103a0056040b1703206e0200034003034000e070280000d080750340e1401c000350300085000209819500c40e1b4040f127801001030500182080602c2c0351f081c0b0b0040264032080d00707079000d85440070300384081480101c0241050341c0301108031258207002801e503001c140520b50240d2900114982405454000710b001000f510054a5540788200180012041140419924141031141102c00e500340041118070554010810300c0c551848441610043c0d40078590550303125410210200200740d075074101c094203c0c411030000500c14138200000c0c01b40c4004401002c190b401601c40c48204920b00ba101080c0c041e01894005042c03240c0c0040c14800d81b00f20320020b90001c40080c104008071405501146c0034840030400c59900b83e0340c49034900c2d600d100301000048940c01c1802420f000520319000301c3d51103500c0902c5030840039201e501007260210307958402e40001c3c000400c00c10150810b0344006025110039101400205 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 224385575 1250 224384325 224384341
    0x803160f09050306040212120d0902030706080702101a0411030402040c08010305070312030f0203160909060b090d0f05030f03070f0509010c0b1306021305010201060905010e01060c050f0304030c0815 87
    0x140060011f402080d48105800c00c0b1f5100307104c1454600c001070911a141c085007800c22000f0142032100b2806449200740c00304400e03008850f0310384240c19560041c0442040c51185a0161400c1241c14401c0000f040c462050740d80e41e0b0107115100000d030f45015480f4901401003006541c01000d008082c03003040401400810303800310b0050181d0b0380000191007012403281048000344800704042031000c1c4003005100903540b000b060140f108050380d0310b50403d140c540d00948110351030f611407580e1300a020005440c031360911135403611103e4001c0006a042080369102c0909543c052401c014a1410010401c0000d5801c18a004000111031a00c80c4c00d01002c400043c0505150200203045c0444400c0020b001842c0c0c24a9000c0c002c0e4840015900d40d9886107820400e815580200e601550130705402142c0c040403403080a040310700c0044542c4483c0d18041d030940b604040010107603071134000c0c00e60391140b07900104001d000440c41403221102591070444081c2c100310b9000c021002c070385c2192051140b05 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 224386825 1250 224385575 224385583
    0x6090106080c0424110111180a090501061824050706200309010b060f07030c0807080412020a05120c010305070e03060108070509090f0d14070803160f090503 69
    0x5956242040e460540750b503000c202e810b01855000b08104070120074151511640500c9107101e40c03000740c41e02881e8440d0140c0e00c1e800d036600480d410075070070014000100103140e00060041040c00140c50291700d252100704460079650260484804a2036100b8000c010013070441000f0000c011078002c02e03c6c0d9101004580d56150b402c40808030820001240345801d1228980c8420046d039400f42161200741e45941d012107054000f1210611103500e0208079485d1418160704035007443e209009042c0c600a81039070182c074880140581540c101d00188103d0340001c0002c0f0040c030103001c8001a00c20811a14410030039a5201600722a014213207848110b2803140300020003252a003001d08000c00c0e41c2d55224011640307a2031040010b6850711031a000000c02c80400b140542c00d840007901c0056559580c070860658801820644a016601444500078128410010310003028540403056180042d2915001c550f2340055901050810105600001340754003e003c0620120540c1401d0782c1a5151900003615 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 224388075 1250 224386825 224386829
    0x91605060a020d050d0b120c0a08010605031005150a0f0509130b0615190c0506010602030708030a05070504050d080c0c090c042106020c0d02101103151f020a060f0203060901 76
    0x203005000c45c45540055407038201c00454040a44000d4003030900c0e00f8480e070b440040c0c200c114040c108405001c40c6018040c0030300c00c29034034040c004024005181000310002c10004020b140203002e140c4283c05c0a5407925a504c009128580c034482a440c00c3c1001c00c518400003030422907001c00a200310100050b401a171969202000b21743c0c20420f4086c1c082c40c4107580c0b141104004181c0311054910221359040b010710402c2070301a40480d141c40c0e0f01c55405a81e00d1240c0310001d40b001c1c4041c00004d1100c0c4494001075409070103464114201951500030810441d1402c02c00c17603001d10046098585004100188840d18004030b8400072a1306108a4070380300ca01c55401400c611071036a0090b00c1450060b5a140d8002e95442802199588a140181382d180d42011145030010300070300800d180304000c10700500c181154000075082c80c49d00d0720138285901e515607481842d0400c01c501030700040705a500100604401198010307054624503450709604503122440c100c070341d0354814014802651a09420141 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 224389325 1250 224388075 224388077
    0xc010c02010c0606090c0302130f030206030f130807080c100510050607051906050906010e0402130515130b040c030204031220060103030309032c060d0212091605060a020d 75
    0x103042c14060500b04064080c9070032000c40c2604180c445005940c5c164001c21b180d50310249541200794440c480c882c1b4401c3e05100c040c0d4071030b0042c80071494081002000c0c6422501048006012051a42d55820b26401c540700070340f03090501240001202d401406a1200a400500c1c100b100740390000b1032201000807401240d014400c003007051001c1000030005000999003901040c00020030520300303400908000c80314604c0c2030091000025010704c1d444400c0c1c0c051607004000d6180780e0206494000241303001000c1c43e00208143c40c103409643c90b400c1d5a0300ca2003150110102d441c0c8161030500003942d508100312410903104102c100302007204c040d0741c3c2080080d41e107826941d0000c864000300c10300062280d090f00e94010200008105501a03105001c0948282c460340070407090082c01411201240b100c01c3c007902da090340fa442007880c00400826003401c00200042c1081d40030112103441b41000c030b84941c29640701d0150300548100e5156014028001190301ca40382c10161a0025101c1d005921084 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 224390575 1250 224389325 224389337
    0x7030e060a0c2c0102190b06040b01050904140108010605030706090e060301020405120715050c1b012601031b0b0d02030604180807061d0d200106030302031b0c010c0201 74
    0x44a280d100d566540f4040324103c1419002100f9003421003014444404154094880d41c00918141241e41404c00d035113680040d41032210307a58500510015140c11845141003050030000d001c803d40c0c40380b00344e40450b01c0380c001c010030790b6040c244000e085412a411481c400e40c4048010814203521424031005c0d20244844001642c0301c60b404a03003e4061a0495a0301c43d803040840000c40b0800950034044071102d180b0301c20520005001500c3c5842017044241c1076410451482407040c065002e50810240185010315001080c00310401c1075140840c02084c501c06c41e8001002484200300c80404000600c502c01d81410b490b20061180ca44144541103200030b801000040c216500c07030780008082c40d00456488402d01e081d18080c569070b842508100c42240c940305c01002c42440400c8a0399100c14002d00500009203507000580e0340c0681b0a10500707004401c03040e115001130080c0604070041d4481c7c1c0085440c0c0c1045103a10000405100144c00598840c41c9410216070344010720b41c042030740a0810b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 224391825 1250 224390575 224390591
    0x60605031b4b2107021515011101050c0702010f0e030a0b070f020c031009060219030e15060904032627030403050c0105131208090907030e060a 63
    0x10080d0b02445528098508940607a9000c80105040611040c600b402c258045000c0729002141e03000d01580f9520700f0f0b801d02d02c8058401c2d00781845440b0340c1100d4140100e070810510741d0f400d034980d88011a40c0003510705c0a0205a0b00950700002c80f0444048140020311442c9400200f610740ca0041020290400c18030348000c0303280c0d42c0620851001d01c42c0240a0384e0840e001810402c058000c245c8500e00010038440301c100c0d6851002c00d2080e0400d0000380909451490b4501400181c624940b084d90f52a6081150b00003014003503242d00e1903404107031030104050301c0c080d104504010a18a20003142d40d641e2040104070707030360a801142c0c8a41d0504140010704129400b440d500f41c001c40e80050502640418000940340380e81c801c95400406c10141d0101203100d00d20a030b1603000d103101c020300d1030780145800d075031541c01400900503c0d000c40b0b50620100e5520201a00b00c00081e92042d2404040000c54072010304203c05910703400603046c101400203035400c805081e0350b410300400220708c0c543d9070588 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 224393075 1250 224391825 224391847
    0x140f0a09020d0614010302180603071406040902130906061b021003141806100b03010e090a080708040e10060507020409020f030708061915061206090f0b04060605031b 73
    0x2550300b46600035a04200307022845604480e101030130f000503031041d5043c03802d425000d400000c071a0310070341020380a89401c41c070f0946c6042c41c0c820100d00c241d60182c02400302040c040607920142c01ca140b81010605500b0749401103034000c450498209900304140c1a030450100c1c0c5020369104583c50341900c040210000c0c80d00200d00401c8544900c0c681040403000344010000025030081c1440c02e031805907406a02c400000403544565842850010320b030500041050b950800d503515030101410043da20002c0644c0d5411005610408086a600d5008241880502d101840042d4000c8112010701c0205007800d401070901d000e075550091085445a04110440d100d2001c0400e074100040e01700ca20854440c0c0c002c030345030103003210708801c03442c014409089081c5050280d540305248050340c0203000d5040c25000c8a4410400360f549883d180c49000004648442c2c0c0b140386036498030300f079001550800607000c0105071045c0d5805402040014014014103210648020b46400542c0c1840c598404900c02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 224394325 1250 224393075 224393089
    0x106020a0215090406050a080c090f071d0f06120f01050102030a0903080307180f170105040f0b040501022a010b01080f011206410708040303050a0e0111040504140f0a0902 75
    0x480c542000c4086c1d000106000006104c0c209d16030103c0f03000d803c0b9541d10202c4400c298048030076070f00052101e02d4000342c81c8a41880f1200e01a005401c48410329810004220990701001107504070094010801281580e40f22032240075000034405503180c100020310050821080303010140070b1010020100c0c1c16103019050051846440120181d64103680307682000f2000454440c0d402c01090440741030342d40c0d20041c851035104652280e040005c59041d03884100461000400440c5e071343d9802c0100400c170b00750b00200d4451181c840c20028140341d00d1202d0442c25901c03008041d030b0600100c5c00500940d00101e0245505580f00110104d00c10f51303280c2001005400142840000c82d01000d075810850404c0b14070740c80d40c19061216106602c6100721041c034409208542c602c00149214000ca0f00280c031940206820841c03644010031030090b4007219508444091a201000540014003041030b41414058003603101c80e513500c2c260722464128030000c410807009010ba485d00d42e491100300c0865590349 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 224395575 1250 224394325 224394329
    0xf0601020c030a08130f0b0d110705010e06070e010c0c170c090907050117190504022e03050703020901090302100306031203020c1209030a0308040323040e0106020a0215090406 77
    0x2c0c22076646203442d04042c400d5038440e640b10102c00e903a014011070790024511441d02210f0381120b485243c0f40425440800605a80207002d0f0b11010411982c80824424000c400d43c007240b0300054019810300caa806045c08c00e96440d0380d8144011110428085a64403443c44200d0708a420394a4440656000103410240244043c0c1e91040201c024420441e00c005003000c1075540a032aa411900700700c0065240d1500210382a03554541904140119858581c00543d000b0f88090403d840e05c0080081e013200d950a04045514030341030390000c081140358540641500030005042c2103103000060f100007040c030700d5240006401085038090b103401440c82a0b100c40d00860300035520403205132071a400100039600445a0000c54800e1400309003014402c1e5007102e2800500500408004d091603070b06841030b44005005900f8400c010b034200c1a01003241001003410080462141e640c0e0b41022507503428514180c01403800c5511070b000310310040e01d840b07903242a007641581a030350b00c8880c000001000340a1039 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 224396825 1250 224395575 224395579
    0x40b04110a09050901060f0e01150c020d060207050606040e0a031103040f1205070f060e220c0c02030601141c06150b07051b0f060904020d05090d02070b040b030f0601020c 75
    0x10700004044481d0b80c410750003850604001d1184641c0c5140b58840140540100b00c003030300302000108818441d040b03074160045801d081c00100941e960300080c0810360400010b550864000807031008101c818003406604c41d000300c408000c85065001038580d04c000100f4010240310013000c5000e400301040003076600a150342514005125242c4182c0c0f451080c000d1401c6520f4400d144001c03540546070007001040d42c42079aa4040c2052201c4100546210145a1401d81a40e11920181d807049240190004c40c0b005442c1c1c80c10b0f10340d55105051402d10160b120060000500c14800095610b100d94080c4106410282c01c3c0055880d0401c1c03001480c8a00f80260603145a01002030138040308000391000a00401c1654840c41000c1c0220403881c0d00302d81c0030b66000c201c0c01a43c03040c0e85410805400e1260b8080d0005007014103d803010303030494506407510310382a0700025241f003400382c1c1013001402401200703503124101482c10305014007d02001d0035020340540518000350a9034420003042c1814000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 224398075 1250 224396825 224396839
    0xf1116080f0d15080615090c070c03060b3102071a04150c020f0d050a0201060801060e06030d09081209040b06070b0403030c091a090102030f040b0405040605040b0603040b0411 77
    0x1510303000d00081500b03e034043c803442122040094400008513820344100a16003200d40507101001c2080782d109802480c0709a00c107030078001c0c00c010a907032524920107903110740c070001094030008040220707006600c209140c0c11070315091003003607080e1565400107054a50300740142e2150894a07040161035407020080082101c04d01c01c00c4148200340d900342101c91000300c0d08001c03501c00b0040c200d88508511000e03c45c5036003c0c0c40107400c420f1040300188021f01c618800042e5070350711901c50700e0035522290700003881c1842603010321000e032406101003149d640c85400e000110030b150404c003a071204400440e40c070490b0000f1442200948070f542180030181c500911141d5126039624111024070300036241900041c1c90000c20014440c0146515810f644010040c0c03c0c01041a400708215588003080380c504600041c04034041c01d22040d0301810207801002140f5440d107051a06000850301c4c150b01c0980b10f5803c000c00c2d10203039142c2d80100d0f5049500051181c0351a9624280070070000003000d822500b00741 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 224399325 1250 224398075 224398087
    0x201140a05040803030406061a04150e0a080f030705010c03020301030b0a0f14010905070909050106021e1c020d080f040f021009080303090106030309171e01060504140403030f1116080f 81
    0xe200e505c2380c020766050a424589070100b14071203000354061401407401c00903130308160644550169161120b00c0350b0003421404403079212162141030a11030140b001c825400802c4050070000e0a0003400045e0b00303503242c1182590f145403501c07458900b000e0042c00c24a81d403001c0000d10b62480d5007041d104040c0c000001c8034156501c0540000404080394180001500142c010914841074007446040350960350040000040c003a200210700300303100070a030980317200d039280307150020144010f0843c40d2140c6401901c0a103030f21400140018800070165489040729104020008072000700f1481010f40644508007540000202521002070a8021002d5488084200b01d040d000540015080e64441e5541c06405030b03445402c0202c102d1000020812030b004910320800402c988600e1604e4000303600700100304517a40303501113000c44d8060440c150803400d40c40108001d25400d406400c0703450b81d03080da0401540b0206100b0321914000c43c3d042052000d00b12500d01d050103101c2c419209001c03120700407250340380e0b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 224400575 1250 224399325 224399333
    0x5040305071110080a0c021e031c0e0303010b071515080111191b0b01180501170c0108060303040f120c1a030703091e030809070906030201140a050408030304 69
    0x1d04511000c842c0b0b6000616005514108415140801d0007603454140041c0c5031003180002070b103140094201103201c0e046600900c131414190305903c903124400078583d20101c04104003868005420030800326410007030b01035810072000003200c3c1100e44d41d008040d211102c171318161542c12200751086080c2414240c100b0444442c0201a100b1606503600800c110f035007041c80c2d15110302a00d080d40711401501f00f4241c00e410301a0300b00e04a00540701154000c0c82e242591160b01600080c2c000141c01c501003c80300242d048507100e05400741c888980c000e040c210600000994030750341c40381240d04100c43d003070100d501c94408109070303000303090141024503005880f25244080031a030048240c035000070080b40001d032a0800c000c101c440040090990745199145030098014009a4008540708003a04804a01c40e6100c540c000d240d16210741c0d0342c4d0001c0d041206401c1e05d0840a44c00a003422403801030304100607030300103105460300001c000c59107841d98a001c605030ba031402144d016947c6030100108120403c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 224401825 1250 224400575 224400577
    0x50607020f0118240207080d02070c0e0603030901030e0106120609020a0e060a12290714031603050603030f04060504150309020a0b07020f030304140102060c0a08060d1505040305 78
    0x8454420001c00001c4010012003420110304980034111010324602a20314000354005509084c50b5040301600d0181c6565a81d5003035817151540005e034a9000c9407000c01c1000301d229104c0200303466003108a0508000002035100d1180000c0079051507541d040c0f0803002c0100b0f400640040201d03224010313444600d402c0c0300002e0321012008a2060721a59004510784500110850003a040900300c5a0b0f200d003040e8480c01c00015200040d40c05d0b0a6010042030405500e403445414080070708600c03081400c026030040c00c9965001c82d610300350700b001d000b0401c0b0000d09903e44e0071800300c00d16005c2032075202e8101203815480f4038400010b680100050200b00f5940020003001180d06d8038103014001c41e1400002c40031108200d00c02580024a0482004007164000c0a80856400100421040368507480081e14551056004111302c1d14000c2c0003286560f01484800da11416201840b450300d00e039581b004101040040049108543e080369000070700c400e200264480c28090030301007000741086c0c24080c02ca = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 224403075 1250 224401825 224401843
    0x50907121104120212010e03073e1009051005070b01080307020303040b0703030f1406040c081501030507090e070e0f0409033f0204030b060607030c021c05060702 71
    0x6a400c103066440001c0d074100848045484083d00c00c840d5100325070801101081009242d03003107648402c03a00015420520041c9407640c420200c0d1901100b07444030703100300481d107c81600d04030703200c000c500070f500d000c81c0e8040d50100c603040b10102c00b40a9048030984803a011900b003240c00200322018294020f81200082000a00809955106a0f60342ca02d6a07980c0c800c01400a425030801d002c00c010f1408410043c010f4a40301e81004941c0c4581103400b00229285110000d1a580028047c000302d800d0034450300c41e404e4118034042c0c12618008a0405401c14441d159504055071140000d401728031071705400020348003102002400f41400e640060201c0440402540b00301210924100e140c50103114085046604d52143d05058a401083c2408005000c81b041c89140c0c00281514024002158642d5551154100180c480d0705506000d040082d00800b958041e01c010010310f404070760015070202003158101d4281c407084914410f1620404009040101a4400c920501a04c00c1d000b054001c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 224404325 1250 224403075 224403107
    0x603070317280305090703030c080a03021b01060603240506070809060706060306050f01060c062c061f0f09050402040209180906060a180510080303010815090a020117040c050907 78
    0x1316403900c1e03040c0354403141944401004142485140b000094603c0c0c047d0131598414100181090702c0550808440c0790840b2141e02c540e5941d000c18070420350184180035101d0782615003509207001c0d11010280a0300607024141c49030350701051407000c01444d04103e5203041b0010304460345a45251900c080a00068041168828101000a013030303441040c04e558100d8080d940c034000d40b404191140d000515000440340c088405030603d83c0640c1400b4503c00342c120452000510192a08654551007220b01502801e65548448400c01c41041b12502100c00e8402070340c80004c45444910008001b44a580e003841c0c0c011001e4200c940601c613110800920803420641580c0c5240d4503030080000c3c1c142c8074064229080e420241c01d000d0b107005644210b600c0300d16503080301200354403040d2103455500264001180b9903c0341e070740500d5900103603440641041c2c8040c02414440705c981e0002e4503100400e0100c43c40b40b6202c1d80080c01b80090a04030900603c40600310f1045400c01c01c5009281c43c4001c4c113000703 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 224405575 1250 224404325 224404331
    0x7110402040f09111903200a020d030b04150611151003110108090319020708031305150c0a0b04110a0e060117060d0b041a011401090e06030703172803 66
    0x10280e06801110383c01903091262242c603403036030001031300100942d41300e6002031f000d410080310001350310400802d4103039681d40080110079050b4100030b0075500150380c43c0c3c0c082d9007041c8529405c074031504096410344500b402c0200b00f0070301700c0030b025180510448d404004001d0300380070302c00c0c034404125212056034062581c29000040f00f40042d07421100130390750794200d07500420400411201600554800d8400c52050702c5e8000d566074400c9103550085c0e045580390149118041100d0b1900e2282400a0501c1d070251500300050740e06000c4d22148400d002070120345c5d00c2c2c0001410410600c03010b4961075402000001020380702d5100b00c5007600304a07141c9020603540c911011003420310359203e6225a01c001c1c41310a101c82c455580740d1282c280504221824441c0480e0060241c0100c1c03600b501174a00440c2c030015002c0c1c500001811105e80345d220a40c403d44004c00d018040c0c0f000304842081c1ca4100c02c410003103200311120608a0b10032481013a420380781208001c40704444200e900791411503030755414 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 224406825 1250 224405575 224405591
    0x20150a1136190302040f140901020408010605090c0703080a06170609070f1428080c010e01082a1902030403060b0609010504090f060909140f0706021207110402040f09 73
    0x4041c8407400030360480442d00c1c8840d030810040c0341076040f000141c0d6020a001c248500d0306050300c507031003d003a21008207694002c80c007402600c000b4441c1e00001c04e806c031001e441b54204003400c1c51451007a41c802078100021840010301c07251080c0c02c51030003000c100300406841d2042d0b04040b906c40740e007038414038114010b00303c0000303c1110342a8101c0075510000c00c040003040c0080304101f0568541c0003500003102d0111202040c1e20380c540520b03030042c2480409407514904800004000d98240b0140d02d051042c90014800004400c81085000d071030000c0e009081c405c40c8003007000c158041c1200c1d500820003004c0c03040400b158082302a000716407080b94244030107a062810007199000380026507000800600c001c00c451800f580000c4909080d0034800a0304640b140708800542e00b42c1e102c181d03000403000601801c003540410a501030b03544a00040c206641c20040025141c40345d004c0341000001c070100b00d0001703111100807252136110008000b103507190369400c1016030300441c0d0300c620744049281c0001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 224408075 1250 224406825 224406829
    0x813031803060218060c0c0603060f0909070603050c1206010318080310050103060906050f090a02091309140105071b050f0712021212040b1c050720150a1136 69
    0x1a0b54a00b01b51802424040b900282801030302d400091500e5803013001d0789282c4030107447d01c10282d030140301c2c0781d80500710044c01c2c03010160680b034002e8841e1207540001c20810388038906010041d40c220311f0918010440d01903050121041001010b8042e00780d4400005102c0c05c05c0c1580c0070b60003114020b80782482919540d90300d2404440c036030310400d030300104100c052180d0340c03400d0300c05568017014841e4014205404d400104a601d0310342d00c031120700103656910502c103011900d850340c00b101c0d00c9031000340860300c1c2c81d400081030101c0c03140764190451900640d58080040610010041000350300407103d4255503107000f0052050b885000f0f03402000a0982441d00e01d1004c01d22940e8009111103076854585803030300c4005954080001d20b0305c0c03445a00716000c08030105002d845d001f8401d80d910b820f8074041081d102c15036100c001a400030107a0003148900c1600140100c1d40398080c0c4c65030030008020310314131940d02044c410190340e004004c034121154100c0840c0d02c68114540c04078111a0800300c00c0404c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 224409325 1250 224408075 224408077
    0xd0515041d030a08060307230a21060f09060e0a03090f0b120a06170106050109050303070b011707050d08040602101415150423090403081303180306021806 68
    0x9060001a0810491684124003030300c2c0c5a40c0003030002d001c13240a00e03648e41588000c64062000a84160b9404449038070307514003030442a001d04a000075401c2140a0702c1c0d000181940d5400c0b00a29080d110424600c0d1400300b0743c00b816000c0d8010809200040740194001e46038000d00070124046a09840042081c000b591403840640350f031140c07558500b00c10404c400a004500030114084162a010045602c40300041a1031403e0b60700c0001044490130b110014140c524142c00047c003d90080c0154000b02c1d00244500d41102c043c0f0080c21000031140003503608008113900321681040c001c9a00038200a0580700400882d003295080d15455107400c0c41303503415121401004ea440c94210000b19284031030b4843c10f40409413004040070082000b40c40d2812040d08141c1c44010003219000d10030050f2015900030000c01070044520401600e405c0d034024048200290a80da0503c10403c001002c141c022480c2c0d0460741e00507030b40d43c00e2880e902d01d414006076201c00b02280302401cbc0c1510313100d000d0500034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 224410575 1250 224409325 224409371
    0x5100c02030c0706081f09050f090c03120702150408060103060c051306110a0b0106030204181112090f06041211120d020d0605060f0a0f050301180c0201020d051504 72
    0x10080d190680c42c4c108201d50144000c0c00080309102c12401005010b030b405040ca0000702100d8801140900d000c050303240322900d0003821610660040e8014048903035012808006018094685540fa131545001140044100340303035544040d0350004010514210002d1154101d80c0303d80c2c0103020701c40f940d91007120640281041c442814400d141e06103e81170003a61050250003007882260a044c2081c1c0703c410103408203070711000220b0360020b001d101c0405200300d4941000c680306801e0000c2801c819250b203042c482d03c021107905801200204100110601032441c54a051800301ea90078101401c1809000201120882c08a04000480540c101c0c01040d900b00c0300d0074207844141400d0414418102030741c0000085595035541d24800b0030b16a8544c40a00341032148050703210303103441800c8000b414001d8030203c080107000c000e2004100858003c44500d0a041c00c030744010803804070aa00c1a40a8000c2c0d100c6540c8071340c00e180070400c2007002c5452103100748404503010b005c1949054005c0e552050381e9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 224411825 1250 224410575 224410597
    0x9070c050d0c08070f11030c0303041d0c0d090318120c0510030f0e03090127180207061e0605010f1715100201020315040516141605100c0203 62
    0x41081c101c030080c00303540c0660b2443d01518490303190682680c5e40070707440d601d010022160380012200c400d400c0c1c102003102414440c0c05600444c03515050041c599401020303140e5000c8076204690000e2400d00d0040c080e590812281e9000b4030000c100c5250182c00d179001c400d00320210702e00c500400588100039111005c0e003560007503c50302010303090005000c00c11404810020030f05440f020846880e01d1720740b040108144152020f55103c81020000400e201d41d031031150012540c840081c0c4010100100c19102154403604042000341d42e01000c0801900a03940090461484d0194500300614043d1500704002c01e51201000826210740054510410302c1d24080c00080050b0809601c070740310648603d4100300e25a004070040403a01d000645000b250713070700b0340005035004800e01800120304020010550411501030146151101c1ea04080e041c652819000300502c00c00041031a5186404131015090200e11004213440a4145240e941c49050398541038145441c13013050880e0b2011098800035101c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 224413075 1250 224411825 224411833
    0xe0c040219180b1b0d0201020901080c0c010f11090a05030325050a0519140d050d051035011404121205070e0f01020c013c090509070c05 60
    0x840c0c1d00000702e080c02070090812100810062140c0e400741203482014000c002c0c05101c0e0f111032604140110034804156801885000c00d03586c1c00c40011a400f030a000c8210307031035480703109805004d0010010b01c0c0130464a003840385140405690000c1242000650380041101d80d284c0c149550f03440b8000d541c050050b0950080005c007102e01100c500200d02a0044460244e40d81e2926402c10b0031807001194010201e004500401c01c1c0d0039500320800070400c0140000b101851405003040c400c0fa00060f400981c0d4400207000f8441c03c101d00341c0034011038000380313914410141d503840340e04510b0b042c41c806407101d0f48000012294140101c80c0000d10000e81e00c07076192130316940c9460416207150b0120501500ba4050b81310b064052081c940704401c2ca685590792540c2c900700b8015510b24122059045412221b0501d00700c0c2d070403008020b41c1104002d070f10404062500543c8032200700a0074000302c094407880004d001d4139400120712003601d1301180d0310303403030341d126000107841540f11700d48000c060380c02c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 224414325 1250 224413075 224413117
    0x5090f010812090312030a051b040609140409060509031c0b060901050a120528051314120706150803040f0e10091e0c020d02060a09020a0e04060e0c0402 67
    0x2041d000600f0711004090b0844607a0420104210440d0f0000c1b50b190405c81e079940f0402041640d243c004a0001c00451040d62030039003444030003403010419005071065114800042115a200c41d13203e00c00c0d25400100c1001982404200305840750f10035458946409030041c1410343c41100b40c803074030190b0700d0002c201c00e217802c44038001920300e03801010211080c490f5400b0116400301c01c90148620508103074248c2c3c0746440b072440d042610800c2031585054180d2030b000401c18800080d42d10041d400e600071a0361200d160190590500e002c0040d80d80f10180c2002040700e00800545420900304100c5601c0d80e1819662038600241c5d072030140740700320300704000c20000c20070211240250b21500301c0e03503904c0417144590326555044151800c1c08048200d5900711040ea8090a1552080d20314520840c80904030a1200c80d07030081d544c140190003900c180d60354a800d14115511102038000130509a880c0c0c0c2e24620b01030030000c0c000e00503485a00754a004030501a00d01d0b103060300c00c070b403503945413034607195400a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 224415575 1250 224414325 224414353
    0xd20070e060109150f030f29040b100314060f0321042402151e060f040903020307030305061c08131a0403170304050a0b040302160f05090f0108 63
    0x180c030240c50141408040f0700041140080900031131240545a200d0410305071483c8001030803114a51f0400a002e4900160360b030301c0313004512280c80e645084040b0a0b00d03e410410000e07004000c81c1d03100f81c0d0f0096507209030802c43e50309500040c078040f0080450300c0c03a031b44d60030090202c03001c1136110842c1e054102c1e00304211035648c6554034244050054041505103034031420102140e0000c011841004541c0d02d05d8054102c0d230401240e003d040185c03040e0411350910528540e081c0c00c0118404038003100c0040000e200d41c40f09242e40c00c04190007402484041949e041c007a4503580141800d40010781401c0002e230181c1801001d041901000086014400b0102d4031160025000615411120340e4105000541500b000f1500c500485034128069a920f196250844000c83d0800344180344840500801010031030101d607030030035180c00c1404c07a10141ea031880e0032820884082d10380210301c640d43c24040703000041905e40c4410350340c00340e4541b401d5032a0401801c0042c0030174411201950b210a480000d19 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 224416825 1250 224415575 224415599
    0x607020d1704080a0b090d031a040e01020702150712020d050a0309030c0c08010501060e090c0a0f1701090614060702090610050403060f050906010b18061305030604050d2007 76
    0x100d404032030301c0d00303240c0c4908603503081851441c0155501280c01040c0440a030f8107011812880174141000c105024514010089062910000324441c1e560f500300c6410310202901100e264075401424030403552056105280c042d0003410058a101080c003610300c2c0c15600000b848a00c20710b203922074605001010008402400c9401c0e800c070704112030440e00b140099209030040c0017501402c0008246503050400040001c00d801e001c040c2304440e403006200c110506802280d60f03154613031070041000c40440c9c1082d142140030030402c03036061180c03500000e10240a40e204800f503442040c455401c140c0e1107020800340e4010548003a6010403c000030070340c40c1c6045003107000e14000a080107400e0550300d8075000d00701c815604598030480d865100b04008214180180c0d8090b1144078021401c01d4000340a81c00d020105090040c01000e000402e94250407400b40d0781001400010211142440d05d89466a01c03819411004000b0814544442d05104d189a0040304070380140001802c0711071401c1c1c80700b226 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 224418075 1250 224416825 224416853
    0x40b0906090306040b0a051501090e0c0f0d0624050d0e190c0816060518030102041802070218060607020108041406040c1a03070504051003062c01050607020d 69
    0x1100c0010480c0340c619490500c04548240d014081800507480c0c40d5004800f85c90004080544d58545040c801880341e0304880444191040100d0550311960f40020843c0d40e4440d440c2000000c0c0004200c260440b5556000700040e96011050602070f428491440074403415091174a1002c203900f07004d01c000340342c1c295200c6514100250704544224250541c00ca81d203034034241c0180d4028008140910841004000303410b204004030344101307038461400f50300034503901a03504149151166151000300c240e909406071409440c0b0038510715050384d084040c040c000e602c045004c900800d10b01c408103594892810341c0910414025100b00e28081a80e4011a41e112005100701d40041050180f880c51100c01c0107400e1049120305114070003241019040641c1c0802c0705400380340040100100320b04507900c030054904803041610f088081514500040d80600026002810020345811082003403010140592031200c01d03250710311501e641c8610900c0040e2184440207508029150030305030008040c403402c000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 224419325 1250 224418075 224418079
    0x9070803040f050402072402040e010b0306060f07060b0319031e0f030b01022505091b0702012006070909060807080c0f19060507020922020609041515090b0a05040b09 73
    0x401201074541b040000881f00d040310a071641c0840c1c10b10a26020041c42c6014186041c01c0900794034090300005e0701c510440c120003041a0020801310104245a002943e80303090060a03280311150001200c030912103015010f40004100c0314600c0c0c012210a096441b04110a654031146004840d400381c02070111b00b841a8114840d190750300980e109401c03d0040107214150101000320300d00f0080000c0c2c00780c0a05047c21100700390b58540041d010070700444403816030a00342680760388040010a20a101c030044202070601074102000425580002c0c0c441c00d40c2c90190041000300d84809a00307030350310841d0041e6080e55002036050318151822100c00d5030301c031500800b02c1d4520302d081000b140700d0014641c018004200042001d81c21840c01610702507101007018281c4482c1000b09101c1c401d40c0828140c040e00440c0000380103c0d140c0c480b5003040c108a040d08522000803641c420b100d4082005214511002910040c40407a500c2c0c1c0d018101d032058910b0380c0e0780c83e0a107820101c0c07410303c031780c02894115 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 224420575 1250 224419325 224419343
    0xc0d0318050601151803120801060f051206010c02041508011a0105030a020f09030d0903020306010b03061c110406082506081503030d11030f160512150d080309070803040f05040207 79
    0x1140d034114036002001940c03048200d47c1c020040c01d0702c007400411040e00f000052000e0800030540a50f07104040e244010041c41a000310380e1100c0c03005032400c5000060185d007143c18001080030303070382c59a4003400440d016100200a1800071b61400c00307007041140d1749a07001600030400320f14010f040d07801078a0003d00e035417003561270312528000292600d90313451001c00210300301c070b4400c1040d46000d004540c01488120507407440d502d0700000040f0f94041c040ca12000d4482c2c44030030700d03003489084c9640b8141c801d0b0180c0200840d5894840c580e566103000b402844c0d8001b80c122002d50b5a203190354840f0100c503070640f2545141d89608040d140000c1644a105070903210901c0009030b1040c81d402406a02c1100c00c440b1980d904024031469840d02c4020410189410f40b005030b60704095101c0704903180d4920801c642d5640d078642d0030300031000508501e50903602900c1c1d26000c02c1030000200080d40581e05c1c0e40d0407248900d0340c0314a06903c038001e5110394118901e190354104402e052a40007071152078881c00c110 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 224421825 1250 224420575 224420597
    0x50603060d0204150510111203040c0608071218052107020111120a0807031a0f060d0908030c041509030b070509120607020714180a0e03040305030c0d031805060115 72
    0x1041101d05c92a07810300002e0380c40d120600720880123218006244d0380302e03c1d099156103042c3c6c482c01060411403080804202180c40080c1100d8450007803403c00d1140094144980400607048030269518008155110b0040f0441003007c803400c0444400c1c0d1100c0d0301501070828265400540f034403416200d84040b20301070a40340c00c8511840c8002003511001645590729181443c0400504960400c04820425244402d526055a484800740c0b03019031800c54246558030700806481024190321a001031030281c0100601441c40c1401020300300303417810040038100d0600d0b10382c01100c60b00090f11004e42700c28050008904a140f00e1401070003894030103440846004100400145410380c11901c0e1001604a02c0c3c080c880c0705e10b02c0208040b0780384100c0b00c205004407896940022508040c24030503e06685601c0d50000300810f100343d900450b040030559441d105060281034490441c0c400d0040020325040f03040700e01d40d05281c0501c69041e084002408181c2c248620424480102560307501408005052 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 224423075 1250 224421825 224421829
    0x40f1502030a0c0801060c0f060e0a02030a060902010311040e010e0406020c061e0606071e060e030d0902090f160305041104060303090807080601240c0b010b03060a050603060d02041505 81
    0x11402150800400500d03c0c0840340001c00d2414107030001d404204651006c00301090302100049061030704010300166690511603614a0200c86080003505800b42c252504140081a1b2119040318000e880c1806036048042040c1954030540c061a1492101d00005100000007401101d60040c8a954010325110402c00c4152400302c04a8040d9801c4960a690340a040344600b1801d41003101503c1d1542403c095589200354007004c65901ca145541075002d0300b0911455030040040051010140e0740d480c0b60005541003e4200b00c981a030003240d1940106e0b41092010031810310440151048107941c406940049020707040c054420344003545001040c107041c0d9542e1243c84015882500c4100c2070343d182024890821101e9401685980c00c890010804a21048440400c1d002851141035440450b49819150303003508140c040e1500303a21800104909a81e1002035000300011680b200782e4075515810041c041c0310031180702e41c100001a000d8401030400350407401032030f0070000700340680c40d403a000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 224424325 1250 224423075 224423077
    0x9051204090c1205090304050118320f0904080703030f020406050a02100504020a0e07020304091a010210090302030d0e0102040e04061b020a030c0f03050c0f0715090e040f1502 77
    0x310801ca10b0307994003034080b0319070060036050306035030007480078000740c5083c2210549a00442c403d030340c18450711815201804841c0803002c800750004c04141c03122807111402080c10017a0701c10800d682e6100c051000110340c94424260380b5641c00080404040e5550b59440c00c0c0389401500003103040c541c403a41c0854880e12280003420107000d10341e03100c503159001c00c18028640300d07200442da03408515040600000d40ca620302000265481312015103c40d4450300e104070320358461a8007141000d841c000108a40c05900480c00760312070301c26422103036040c55441c1c01000312200c2100040160b4010010040701d15150b812105032401e0050006040070b036a896400e102d0310003210211046a50303504060081001064000c840e20703420301c01400001c2ca1954050070707120b000d075400350142c0345900960041503c00c504564402c01c0050035540c1c7d401110003e030741d44810b9801041032880e803104811810500c1103003400c0495000303a0024429031625100c0d0b200f007012036941500d2030140808040003d00d1940 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 224425575 1250 224424325 224424329
    0xf0403050d0f1407021902060403020609120f060412021507030b01110111071a0403050307031e0c0e040606020f030d0c022a19080a02010e0102010b100801080d03051909051204 77
    0x462900c0303d80342c601402803c044000081c4259000354201a0001d45c8420051301d00340ca83c1030740d007242d907124004000742100c00c03d003d000c0001d11921000156400011803014003440c824178000094030444041030b030b00c503511409541031034000362001543c024881c0d0000c01601006061003034030105103900442c00e5800c41401410580f800040841c01c114845003070514610079050f03494000d0074182e07002440781c48040d01d52420540c468403091001c0e80300e90301c10210600081c1d001c000743c1c0d01200c0040c01d1410800c10043c411850610000b500034004220070b41242480c10286241c401214440702c02054524850021441001c004610950015500d20111001141c4200c0c1802d05c00b0104451316041444050034640500801c2090b182c0000742540302c5582428208581245900100e00424000080961015004c0b0a004546400c10503030741c10303a4002e00a8a801d610905016800e88031b00ba2014401c05a10941000000400b036011300d10303240c031580c1a260101040c20288a40d41c2181d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 224426825 1250 224425575 224425601
    0xe011b02130606090f05030313030f06020f0c0a020301150807060809010608120711041404140c1e1807020a02061312060e010c0309020105041401020309040507090e07080f0403050d0f 80
    0x200ba0074801c2d11305e0000910010201180114500f907000c299001d0002040e200c0104100303003070300e4510708100c556010388221070b0801d00110386410348091b44c030b40e98848618040e03000b5440e00f004505030180c40603030041910800c034003c142c86403801800315560380d0020b14030001c0b950303501c0e400708a07070505002040300051600101d60b110784c8a410118010f5800341241407251f07103040300602c1d0f01d85580c4903da600c5a000003078041003080b07a014890030210f086040e41c2d400603840328842e02c40c0d18403070491003c3c0582230386c0307032800f91100c640140740d01c5100395808000350b84244080001460f0050080009443c15141050031656a4107103003111144a40201c40c00d0f5150989003c00e5a0700344541c914012040c40d0038000020a6000a043ca00c100c0c044d61001c5209101522001e9008208542e041035024004004c2441c24100050001103680194401c0702c0b1040c000c23411040c45030501e0307401410b010b500c524071911035581c2034480354040c80503000e083c0d03109c002041d40b18409105500c8201c000d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 224428075 1250 224426825 224426837
    0x1b040e0a030903152906090301050c0a12090c0e071b0b0a0e0d1409061e0306041401060503060402070f02030a0c030b06060a1403060d0206030109090309060e011b02130606 75
    0x294503020402800703202c8510b00c40c910300400000040c008250b012160410b071117017a840d500c52203000c90003e1103001040f940560031300040c0045204600300500301c650389540d4280d4403c41e4000b0380c5040e10000c000c058040518410305200c5946400c0e1032a030051550308000210101d0302c1003d80301c14460640999142d040c120401511044900841444440420180012094440005e0803411443d03202401040e030215a40b0034980300e0008440c074010300d031080341c04150050489105d51381e2085591600550070002a1300c4c0410019103814140c0e0299111039041d030743c94400b4080250450030040d11101250b8140e900581c4052018076480c90081c040e01010728154144188001400b40200d80115404c00128851581c841150039043e0161102d00359070f91500c400086002c440c010780607601900c00000042e000e0610b50190f61982d02c6901c600b0580d90f902d02c8144c0d1140604074000b408202000d01489804001880a100c094070040c00000720501c40da003d0700403220300360000c0c408103034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 224429325 1250 224428075 224428079
    0x3030201060812091804170c01050405070b12040f0501151401020d090b04170304090e15070306060804110312030a0b0109080703020607032d08060f040e1b040e0a0309 73
    0x302c02d0000600103401110a68507001140340450304855407400e400701e0000b41c080c0440c0800c4a4044a400c0c1030aa0740260741d10361803940200ca0003407405a8040710715100344280040e854000009075042101844a00025a40c640c0c44559203c0c20b900d8040350f00d03550f02c0d40b428600713004068482c0d0150040c20044141e002d030580029141c40301c020041d0007030003100038042100006460813241680d560780ea00d03030502c00c04680d0043c5140103640100b041d080c10640035490300c900001d00481000301c502c50511080d107411500360b003196120302650000400600008000c02c2c1030702c80e0740007090390103401c0b03415040030101d50350f01a8005403a62984581c039030b0f5001c07030f207580e116404102803e1118080c01c0041c2c5194000b548505c51980000c0070b00c00340d1584920502144800400e24000301003902258510303458005080c004211001403041c4c2480e60703110041d0410f8031902020740b40c6140241182032000301c40b4540303040d5400030a54415111318501a21550070322000010750700c66118404054 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 224430575 1250 224429325 224429339
    0x4606020729090109080d020f0706320105030307020d020d02040f06050a050a0803090d031701030606090f020306010c030305060406050a030b0603060c070b0708040f0b0f01080712050307080a05040f0303020106 91
    0x440040c0011410781e04180301140424441c5e821562451004180103943c2c0100c2c0221081e07d015800d0050071541c40c050048400c0780252505612039090340000c0078500d800e40d00c0403031002c0c0e403e0080326050781c400d101c41f10050a00314801107049000a24051400c01c282d40002c054401044204c00031503115030f0100802e04081250340040c0408541c3c0021180c10440e80b9a968040c818980703205000d401c1c500b405140c0a114429954480300881003020b60b102e0038401c3c080c2201e440743c1d0407100d00e41600700f00124030503c280d901480050351100c0c10070704280c80c21405410040c180030391241c1d44403000580e40e501c504001e8000c501c101c2c4406030515040c3c08141c2445001422440c160204019000c000ba041382421548000305003071030462902c5a0034910030000d2654801481034602c0c2060040c03030103040d01628101c42c042001c550b003643d00c0781c0240306000401c0100500302d92090010a000807104000303000c4480c02c52615506007075480c801184025056070040d00540d6641030144120 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 224431825 1250 224430575 224430653
    0x617070f06020703111c081b1006050f010807030e0109150606030908040e0a09060e010203040c0611100b0409020d030504091103060f040e0c0301060846060207 70
    0x10705031400500b91092440d2104c880084600710403c0c4611603a0750ba42c55001c9050600014054204100303980b90a4040000c84103000c47c020a00d1492140303800000c113010140c0500020b8603070150110b03c0710b174280401915441c5000d8031147c02d05480e418a86038140c001d02c5092401405215031002907400303103143d50b08a0302c1d1a0850030030141400b59010110381c1c840111800c4603c1004007074410f030f54407590300c4000e20160500803c440e040200341083d110054003d14055400b40b000f17296140d07038509040c3d40c525919081d040c801c3e00001100c007254280c65001c00c4d07803000d02a02c007048982c0d181e40080c1c583c00d8642c200300e0118a0118062125001c148241d0140e114a01c0b01d0510303600344034000401c0e102d58084218483c50300d81030a492031107410b0002000320280a00244440e5458180c1c42d901d82040c0b030a505000203a240e03210100c81000e420920071151800c07680c40030403451403d440f40e6010310580a41d8010f400b0010000001c00841c621400e82d84800e0500c000d040010072030300c0301 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 224433075 1250 224431825 224431829
    0xd020301091e062712050d0603030801030b060d030210090f050a0308010e0a0c1b0501091725080a200703032c030d18051905010e01022b030617070f 65
    0xa00a0090458a0410f03000c034281c80c0000e401c030700d05c40505555844119035500c16036800c118070f0b03401c00364004101070700b0a182c94103881c40740786011202e03500c18007802602c4018030300250041e40030400c3c0c026420391a510034500c20b8001c071184142c11496840302c078580060900c04a002480103801004070700d520703940054002041400c10f214000303003010002c0c54619001d010782c00030403221a04104100d001d50080d0704490341b0075603c58120b040c2203440b2465401901482d4a0024580d2100c2c41001c000c0240f1000e280d44001802c0c20910034660403200451300d550108000001401c814200503000c019107030007584603607204010145002c0d8140410214603000030020039004007034200c0c0c0e035030200b002d0340078140502d80380e0360030f0a0440300c40c414504141d0001d6004004003032094007481c1030f1911030003521000e0b215450104207804c012039440420008840710610004071b800031241c200510342c20a628285000326109490726240400742070f4046150303005a202d0441008099010451080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 224434325 1250 224433075 224433101
    0x60e1806040503030f1e131b0b0f070201030b030f030d0c2d0306090905010506090f010e1618090911010207150e0301060803031f0803090a050d020301091e06 69
    0x203954201942c5180e9a03000140c80c0804100070840012540002c80d6800c120469010f10401c1050030668050302004205c081e00f03031005d07501003d10b40e80072030700c0c2c1c14a4070481c0e0ba8040000c0c038000e1441c00c01d0130550046202281055211580c614095804110500300441c9803006165130f448a144c00000325042542e041d030601542001c20b00c84050039020719503010641c0415000340c0e8803103410840052145030030410642d80303042529010f00405600a500c01d400a036100300e001d40fa40044120401c1d82481610500c0c107401000031000d5855031181003010000b400c1411008180070740000ea0201c40d500007a0403140c2c2c907500da03001d10120702444101c0748820300103451752a0500d1103424042440e5519002031002000710034500351401d51100f402490b50388141ea03124105000020942c0508030070ba00307460000024003040c2450084216140c882d8024446200a8640420702100d45071184045c0d9040d503840d5154004a80c4101c16103855820a461824100034180b0b403510485038090380c194 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 224435575 1250 224434325 224434333
    0x30304030f1401180b061201320f1b0d270506070305090309210609010e0706020c010512070e03012c0a050a0b28050105100819021309060e18 62
    0x8049449088006d0b005241a607080c0071100180660301d025110b01080140390a000d8034240c00c40b040c1c40110900c1c04401c5884071070706a00d4800c1c2c10350508405441c00003001109100e1030711004100b00c000c00140000c0c05002c00c81c000d1040280c0c030315000381401d011007042c04d21404c0e0108102445070f02e03800181c5050400203030a203500709940ea40100e6010314054841c03910301001c4500a600d0300281d4444210031030b0241e14000d00072501900702c1341034082d450300c118580400d074070f03001047e000602001130391214288009d4000c2008800c0c0068410301c207000360441004602e403400e0058130192400c404013100e10f0414682c14501c1c503185109902c4107070b042510042c0000701d021481c8404560000605682611841010b01300b500b140d40158146070300aa211310010b03a000d401c0701c1e040345c808840101c1035045501c03041e50502c00c1286e0501154240d070100c50003030b9140340e010308060042424030281441d11002c00303a040b03424039000281c1741031240c4100405070001504c2031940c10b4030a4050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 224436825 1250 224435575 224435621
    0x70b0a09051206070903080904290103050108030a0f052b15050609090a050402010e030d110705060406120c05040906030b19020a020d1b0606180c020d020318030304030f1401 76
    0x20018285c0c1c0c04014030260000403640e1459560740c100881c1062000c0504010710500b01c41c02c81c40701500c9000602090030700c000016140d202106030303900c000c0c0e161107000b9003100d0f01a00f1a1154050701c285405c07500f80449540c502000041c4000c03280b140340b03c001841110460203e1404445940030034441c1c80700f049500c03000d8031810b0500341c00840f0f0b000c020903507445900c01a16520030401e203080e0503125250f0040c1d403090340b000c0180310410303120341a120741d99200e200344001d0b842680100ca022039114144104041c0d0303603078804400726500c1d103412030605071540b0344c00058a180343d0041c0c503502b00b4082481100042194040d6207180380c41c02c11803420803410b03406901c52440c0700c01c02003405040380c0e440c03401c048400e4103180c0140c0d02130002c2000701d403240800e003c45440301081d0040303545040b11040500d40000303461140d00c00560011401c0403454004080c600001c0810590140814400040014108200d00407024400d1030940d010380b40b20748015003141d03100040960051405004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 224438075 1250 224436825 224436827
    0x140c16050402042601020904051f05030105040f031d0301020328090302060c2209021210050a140406170d0f02010b060703052107112103010611070b0a0905120607 71
    0x11390800030714200d0071040442d902540c290080c01a4000c0d190840e042c8402c00030661407401050740a403403415900300703080d5121002d0500300c1d00102d4008103903200d1880080c010030700504000303104201d11000040300c0700c200004682660000e55140a01003610008248128440700300444e035030141240c10001904142c5000390f555101420112410343c0003e03010109105070410342c07400344642c60400f5489640e074100c0f0700080d40000300445000308128003040800048542c500204e0700018030401940f810112290032500602c9190b56000781c0e1004001035220351040250b400c20035800c0604110007000c9405020b40a80981c070384216403400c000780c2c3c01552002d060710701e0345406182041e00c0f95002e201070890760101d1216000c000b075210302008189580309200c45803141484d4244c1e6807071100b510740f0300c20300300800b42603000c0d0325000c0c0010701809108280006da003031042c4040385e0110f03640359070070541580b201c50ba0358001401c200c01407045082c030032031140242c0e50368401400345141202d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 224439325 1250 224438075 224438099
    0x30f012901050f0d20040608150409020307030201110102131401110d020601061d0301020313020f04021206040504030203041703040602160e06190803040902091002010b010507080703140c1605040204 87
    0x92000b8144c1e0f1412039085090200005d420040050b0701041c0d43d90b030b26a400a03199417011546500c02108113004540c45040c41d005d00c00030b10323038040c005110040c195401501c1c0011150070b07002042d136082c01a03400014255600c607000300760750808400018041c1000500c004440d012001c10342d40414030300000941e000441c1411030300d540c80c0c6820252048055904240300014000394158008014010303008020f188003981140308590340c80700030170318409001c107a015001e0004140c0e9403500000705281055002664051b2003441500c1c5441d4a6170394101103c17110509949065001180a11900f501006400051503207085107100040c0b40140d018004c8500420040c014180c05c0000c00d500040d207240ca001502025041e2038a0359200c0c11124020340104401602c41c0040005142080d8018411041c0083c010b030b441c0c40c5404d1040e03c0d503e8083c1d001d4001182041420140c0f1406a01c0c40c801074100500380c0409090141071714814481c04040b9504100d105a00c104410841216400307 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 224440575 1250 224439325 224439337
    0x609040b132003010b01030c0210180b07050706050f1b0705390603090c06031510030c120c0806011206080f03040302090703061d06030f012901050f 65
    0x11410189a03694000080310346420301030080500b80900038400d902c2010091880003020181c0003080900500c5004506540c851b0f404007000da044680422680c4c030042e0040740d1503a0350001b81c070494004a54400751360400407036290000800101e24031003044814000c41e07808c41c2c6a4034007120307a400d104017241d045115641410541150019000c01040320078442d080ca4840d444041101c145558030884100700c0c424074001b80c88207104454143e983c80c000d0b00750b030700030b80c89a00140710b904042d00a02c0000d5101802454075613201902411040c2e503060302503400c02c000b50740c01042031811004e026101007020100840102c2c1410380b50010940d012000981c0b103002441d25004074080c030ba80704002030142d81c200e051103028183c03e1a0740250000010401c4a209488290180ea5200811000c80700c50380a10b10a0400300d02140791019004900a604080000c060b1241c0c4201c051810b400c40c0d006105003540103841c0c0c0810a510a40004140c440d40400c2c2002031802c0280000da0b0940d02ca00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 224441825 1250 224440575 224440583
    0xc03061f0c0b07081603052217040303020a0c0806040b0c03130204050c03060a1d070c0309090c0305010816031505102606100b0714010b0604030606080f0303060904 72
    0xd92181444a10801c14544015003254501c61682055080144090030854111310121007410300c10030401d00c00e05c01c1d40d200d03070307800c15600300c6440c00f49500281c4200b0348041680c0c40a0002c960300290040200144010f501c203400405082d2858501400c4030455580000b0300d0350007007003c20001c91001d4502030307030140300291000d5880d56101c448882c103000c601c03800783d0880d10f0001001076200c0440001c500414044552900e8a507580600c445510b1303005111000d10f40070180440c5880380070300d40540c45d1600c6400c10701c4120f0b4586003d00c044807442418907000039282c5004009610080c4200321f407651281d01a02c45c25411500c510302d4402405494140300ca64490018501d010400100005081c000800c4501100c801100d10642c14448041010a000e090301184189850890030000c03100507000440c00d02c081e64541c0b140c442c0018114036059500c445004446643d840014009144252400901e85003066034462034280d0940011100b40c0c4100180300d550764500308a580d00030341c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 224443075 1250 224441825 224441869
    0x1a09190f06050c04091514030105090a110607080313030e01051306110a21020705010216030303020c0705030d030213050a0b160609020402030c0307110604080415020a17120c0306 78
    0xf4410800343c20700c9240c0c40b420030300d0b2514100810840742031101404940369100e00b0310030b181e0380030201070807680180c4414425a000d1070321000043c3c8102201109420001c3c4800c2c241002500c40c2082507008442c01994145141c1d4240c08042d0050701c240c100714004c0c45c0143c140110301d4841ca19018450081c4802c1c41042080300d4a1484100803040e0040d40c407500c0c480d00100942240100d80d10600140e034003500030100d000ca074a5200042469284112000521045145d501d05400a52026039269028001c01c100030850361010005040c2200c40e968005035110030381154501c064109400c441d11a42d014482004400902c1054525400c80d40b02154002081031070800000c00d4042002508a4000b1080119441c82c3e14042c6209000c10f88130745001e00c41d1243c203180c03910b104403401030030000c00744810300407400d007100000f01950031030040f00c40d400d01c1501c640b1610300c82d40d42007080c00d60300000d144450243c00c040440e004094030011a0450600c040000d810701c5a41d02220003200ca = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 224444325 1250 224443075 224443081
    0x90b01051c1203090f0213140f0c0a030c020c0d0c15050906030402060f070b01030f120201090f031101060503031306020d02160b0f0904090f03080903070305030a0c0c1a09190f0605 79
    0x8445c03a915242d65402010304581441c40d9010b07074017400303011b0001c0030f101c008080000d80646c3c00b11a100e100703807a0312181501e0520300000a070010300a8610701800c6204041080c0c070700d80c440038841405503008010080b403007490a881442400701d440550300070400280805609500c1c0d080560340c0266040312081c1c0c588152082d6034116001d00303400039284001010000091000060400c1c035054003502818103460348030603050782a120150f500916425159582c42e000c80c2c810000680c0e002408000400c9940d87d45000030f03e107400035105100b0b80c40030315400b00300e004c0d010001c2d01130242c42c600150840018030ba078003260708605440b400480100008030218004000070440380d40f80d90013403040000b040316090150035101c040700c00300d000c5079610001c102821000401d40f0481d80d41559500d2441d95140d927100040d101d90301010040c401c14010b1103001400c404007480303625100300100c210600c0c015603064030301110751a0340790300303243d2060408000c00c4411030010000f9400c5440450180c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 224445575 1250 224444325 224444333
    0x306040b090a080307050705120708031302040605040603080c0c100203040902130b030442020706090f0f060b2d010e03120d051e010522090b01051c120309 68
    0xb07a20380300a018100002c2001121a001409014082d00910449a80410000034044241f0603001d018080326024000500d854200301e44903407c4900c060804240c080e61403003c01d00395450354000704d0301501d002c110b8200ca02003c00030051940da0480f4500d00f820100400691684201e001d030880740d58000840382000014203002400801030303021710715603d1901c2c1c140040040e11100070852101d40c9a000b404002c01e5031101500e606100b00d00043e960000700521200035400742000304c480c15101c50488020405040e060301c0060f00600509a2001c150302c1c2c204100c882001c40b82d48143c0c112070402300e40070360110039188444001131030346a1202a07035005892004100401c15818459000391840c141b4030000a46005408004c040c401502d42c0f10351040180707070300c1c0b40d11000720b6005401082030b880d120b143c000b2100c01000041c80c0c680c402594007410741390780c06c0090341c1c0140c00b50010000e0707003000c0180412a1826080030000380c5074940d200340500412044120400d602c5038107910500c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 224446825 1250 224445575 224445583
    0x909090a050d0806011101050c0d020a091806030b130b04080d1b110706091212200a021206040c0509070504051e0f0109030f230f01140c07020306040b09 67
    0x3640d0000200e800000550070003c00d150002c070340044c0000c41c0001280a140014001c440c06001c1c00c240782418403441c2611900290480c4900c0303410040c041c0800030b03094030078255004003140002d6021030b83d1811801c010380f109401520f2000020209100d0030003066400c0380540c1c02641c40a0f805039a0003039103510001800ba200d52002844403800350207800250400324034254588800199205296110030a9801d61014850811008003c1c0750301c10024101c0411804000e4040c14021032200c0c80b50400043c6d180315581d4203181c1d0744408052019460900d10300040c0000f50700003049030f0b00c1c09035131304a2032120900c207042c01794900d200450030705070103942518007030800070b0050085580000b0302c04401c16400e1441d54000d03c0f180d001142d0b41d51048047d0402d80e50400c101c0010780519590305800b203640509070150700341c2003102c8840344000038442405c0d0000c0980003c40d007281c0903100f00d0780201c4007030300a000e4103d080159900685000c00c00640c0160008403020f881c0da240c503032060030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 224448075 1250 224446825 224446843
    0x10305010e03030412211d06070c0503121803031815061c02151804060501050a140a020c0a06030e010b09130206070809090403080924060d110a080c0f03030906090909 73
    0x15540c24506c0287c0c070282050501104000044100d44840d22101400e50328003e803100068402d401c200180034030701c0b02e0004226041030441e500c869010503240340c00ca085400c181d540222114400200c81801c40f030400000d0580d502d449444503290411000055080c508085c0d90303400312080102e1001035680f001802e100d00c511210f00665902d0341c1ca00d00c40074603109807185510440c940903002c109035100368147c89401c50b10b03444402c1c00a440c4103070050281c01c152826011845003452509054481c2074298000303010948011601840f828919800c0d5001c614015004903140f90400002000c409485c010045d01a10103907580c034250b0521000f6072007802c1034260049907040a11040540c000c0ba13043c403881c2c01e1001d41c0e40007441c503028030510402c1e1425180f106d01108010841525043d104941c1c6075202d00104220b07000100041240e140441d44454500e402c940d421460300e0a0046290060308401c0b07010718500000c500002c0c100380a044202c42c000c032035800010348000001c22030103038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 224449325 1250 224448075 224448137
    0xb0d0203060c0c01110915030907080a08030a18051009080d02040b19020303070525020406061d0a05090708060109030c0905060f100c290a0203010305010e03030412 72
    0x20103150034002c1000951028411014070340c6031034002980100e02c0c82c140d079418038000f01003000e2003c40c244900d103a40c2006d04090040d0088403400542000104403d8220030705c03a00c4d0203626494402580400c0b24501000080d030b100c030442e50a000a40c0110324002510022940040c0d03407035440c01c5c40c0c8018011200c11109103880000c000c2034121900010303040c9850782d81c0501800404d201d000320b85a000591714200410000d0004a030700f0104900c45200030300c07502864a01418090300010161880c0394000c0010950f55014008280000b5840c0406010305481960a4924240100f4000b9200401c4031040050400104e21268481c0081e1401150040e4807066401d84486940c8000c0900b501d52620030842580b80c44120300340004404a41d51150316580c84025040c1c840b400c04048a8504580c03c5070714071100d198000d00c85424501980d50003100685960451804500710b41702d07104100480c0e0b00030300400c0001051514462032b074440b01d00e00921100a601c810b219511031543d0052 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 224450575 1250 224449325 224449333
    0x3060412110304090905070f0308090609061c0c031506021506010915030501060f14070f0602090d0b040b070c050d031113140117010f0308030c0403020a18230a0b0d0203 74
    0x3402940c65041070240340d001b002940d11481c1d4441c450b60301c0c02c000b848024080312041c0510441440c04c0d00180c034110801400c018035080c080780182c01190004201c010715566204070400340a80c0c10322500140d0030007005035441440c104a80a03680f42030524105400c02d80c4c1c2c0300002c1c41a44030701c20200080c044006030314041c02c030722000900a0302003400741d0740c00070f005043d00f4002d192241a44040070501d000c8000c0c500241c50f21042460920300106485850302000121100d03100c04044d074100034042c00c450b00c00c6040500d03000844450280c0a03104015009103444d011070b00c080b82401321014203080c002000c091400c80c80d14107020350780700e0800700d540c00040043c410041c1203004101c80b1090381c4490380301c51022480034802c00d00380118000b1650b104414000503511500554003c0c2c2585013150034907949900003aa5a0020b4120514504d500304400650988a006003403002c000e0200d41c0900041c010850040048000e001078000c64590400180a031552064000030a8014003a2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 224451825 1250 224450575 224450579
    0x1407060e03040b120901110a0c020a0b0f0d050105030312072703061a042013050603090c090702030a0804020d020d0c1403070e010b07031103190807030e0c03060412110304 75
    0x10f1826004220150010103e88002981101c03040c407851103192403140e586810720341340a04c110350f04078a00b2000c0703812210881d804610082e004c40544080c80e002100d480c0d4a44a0b0034080c010740380107034030050003a070050000707108005061106a074040c190346000c6e040b45030b6040e4070a00488220310000030600c003028003c414007000e41c03c265006030150100500000111061108a91041c940c903960b118090012000c84140c04006000ca214040040c504081d1100c00180c071f00d07441503403842d0581e40210356007082d904120111503071107491400a5400c0407100d020280009800600092080006940800455507105a040d01150b003000c8400146622205840d0075241030802d903e01c24412840300142c089495902c007416101c070f00d400e49040540b299000c1d0344440c50000003201c030740824003804600d0080140a803084904950310360f4490700b403064010341205c003001c400258581268100c06078640b00062025001035106849420700ca441d03503400c86e0b0f0001e5400e104442030000044c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 224453075 1250 224451825 224451839
    0x4030b10090e06150d030f12090c080c0108010609080a110d15050702060a0c090b07020402040b07060504064a011103060915010c080a03060e0109140702010c1407060e0304 75
    0x10740c80c4512010031004080401520804c01442c83c05e01d0010002500202018040351240d01c105045402c5848003250080e203da486504041147d0000170300b980c05101225030540e4056981d40c010459418220081c1d07081000180d2105038250000d021140441e10380300d155110b00440c0031031b09400000001c5c40361400c102d084040e1906940201c01440f40802240081c0030034440d141c2c03890101e17107038a80d038580f90008200b1190000c072420303640301d5400c0c440000c4007180c20008011051054400080c9450326261410032203001150407019014149803000f560803491524140c09041004610300455107030103d10611602500e82141035400d00c042403a04a0b07800c000b5502a510440e00441c503a5144007030440d0b1084804072290009980342e47c003d020603140402802d5074500c42c58040b880315110844070415070001e0307014418607551080d40e0900032010360880c50700010b90f44000d201011400034014401d0013484c070700d607180d14000190b02d01008041d0303001d803108001038001c1d00e0311541c0c0d9480e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 224454325 1250 224453075 224453083
    0xe060403020f0613030e0f090103050304080f0a0b0f10150207050310091205310602100902010509012f01050921040603050a020d06080c0112060b04030b10090e 70
    0x40490142c8142510445100d0000c24210702c5408000d0140500c800561803c4814011005c1069009621801e4070041b688850100c1c038040e60064005540e030340d00d01644145081110750701d40c07036075030059100c0d0000510056600342d0043e018910003d05900c43c1c40f41304607400c0c0740d0362003200c42d00603a02581e000c0036000f195100403950300b10295041082040d6000c0c00f9a2040c5e0b00051116210800c0c808401d8000c1d0b000e070620a41130040f503107003a46669034018008100070070207040c4440c4a0010401d01754100311003907000800f1076080c407e84030254006030580c0a1141301506001a0f607c0c003070079040c40720b0101c0d108100390034020100b621140b0109402050199075101c1c03030713004100845003400a940300d01c48a1420f22140c0500d05840c03d2412401000040c0c00741d000300350204898900c428150043e140580203510103001201034240001d00000068480d480f00e0500b050400c010f130a45c000141c404070381e00840207486035030300c80b2065525801580c0101c001c140c0f4160b61103801c503c00107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 224455575 1250 224454325 224454331
    0xf07050a120e1f140a1d10151e0608070c020d0c030c05031204060c1104150e100b0d0902010203070b040f110d0203101a03190c0608040c03060207020a05040e06 70
    0x43d03042941488500c001041c2c800308012484404954004100540030560191200042e18030b10703000e00039506d08409040c043c04411000311641c8a0085002160403070485100070403c000380032500407100711000842000d0761244106010440c00001c4105e4000e01e144d4800355030080072203011400354030341402c5500300c6000c1920200d1012a021410741400104018000080300025040c42d1829004480513150310301d04035554054902c02c00100d4903240a403010a148241d0005c03239050402c0360714440168001c1c402003454200010401c0751016501c00c403090a080740c1c00c007180001d21400141c1c594815401c0040c040000341b801c010502c40c0b01c8442c003490030b1040c8080000648098200001c1c01100d94002e54190841d4400c10b1038442e190b801601d10714010004001180719840000e41404040d5203000c1b854007036400100200206100990090092810800110b0420b40c4480c03203000c0290100504d410740c0011481c042d55280c4019100404c0010002c2c00316007128a902c0b80c40d09170503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 224456825 1250 224455575 224455603
    0x1020708040e09150a0507030219020f010b010815120307171902030702011706030c09011502061b041a040905040f05190201140f04080a050d11060f07050a120e 70
    0x10b00c0403481441010442c1600c0402d82a103034121a26500c0301d11006060103000b0005041e820490314000080c1040c400d0150259a00070f810b503600002100c5003522a1705030079604100c250030400401100c981000e800d280c0050381e16100c6007080214180c03940c4210390000d48034044414034155030f50610710041900035901d03202c445203180d4207231060303a47c0e02501c24004d0101f01a41c0d041c00704284c0003c0103c1e4456801000c8807040c50f80704010078400002030f000030002c4403c04c0c0d80006519010080607070020240280c9100314980c101d0400d0140c000c42c080d800c244100d20714140e40005800781650b001e844280c13003c00c050b082c185810041d000440e1011901030140c145040c8c4180603104520040c1ca8041e103554048844480b0380351501c0d40000070540b003001c81840301040300001007182002241c4550002d00032100c4400014104070050041100d4560180013004100c03041c1b0595a41c0000c510708040e41c48820440702070701c1c000b030083d2800c02038030f1604503d1100c544000031240401205 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 224458075 1250 224456825 224456849
    0x3020a0801060f150512090303010f0b0304020d0809131401052d040f020f220503120f07020d0b07020607030c03150b2a0a020a06030b0d060b0102030c0102070804 71
    0x1580250900382c60180c400c059030016048010400d800d88000c070b030489805980b41c0640390071101c0401c001c0000741540c0c0f00c80107501c040010f206002008000501410f0341040c01030662800b40c0c0000c0d0f0044550000030000040840c80c8442500c07580c00c82801d5110381c52080c010319040c000c032451401d0f024816144211003450080741c0d500f481c0440c1d1031100d00000903c0c03c143d1050004d210140030924031500c5110b908014074040d0041000160810b10868501c040200302000d1219070f403a0b0107504490311075000b0040740440e11120104451801ca41240d555856070b0407400050205250312502900081002c420402d1540e408140300d44545559181041440503411040b4101d8a03050700d8120b007000e241c40144013200c28000070740001d8494017402800950304a00702c05962888002a80309a802442d125046103404603081c0003421140c41d0800110800c1e20000d80504011400030704550b0341c9860308001d59100740f040311000301d03007800250b69805031031904910903402840f0710030780403003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 224459325 1250 224458075 224458079
    0x7120c12030e180609071404090e01020304020f0103020a1b02060d0c030f0c030510030201030504210504060f030b090c03070201090b090c0f0a0509040308090a0c150f030504150f020708070b0103020a 87
    0x3071100b0000f8000c0d800502038050943d06d0345015104102602c0c40140e00b04824040010f401eaa6400382020181c130090016032603041920500030000400c40016050500511040d00c0050b401002c5401035220402e217201d42486c2c500104140d845201c12100000d414010403071601501904004d807840000340c000c04c01c460380c01c3d0040b0b0885405507105495120100000c001641c40394100d990810300644041c1c0380c42181d44080c14189408120700c2d00802d0307020074100002900302540d55268501c1c1e003011f1140e0382ca0503000a044a20003000795000d13090100c0450071240c803d41c0003620340d075803040b11442207044c220b0b001031303441910004aa11403003042110b0074082c1413071003400e07003203c401410a1000341c070f80360380513514401d0042c00790b6081d11910003502c0204035000c90340401031203490f200b42d0b0701fa203070400024103503407030120507505160920041c0300000d44500c0355480300c400040e00004083c900141f01002a21528501500042d40440d049041c80300030711100b03040f28801c5400d664855 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 224460431 1106 224459325 224459359
    0x1409060421140f06010b071b0902031009020c0604030e18040303051e13020603071709060a060e090a0b15121608010e07120c12030e 58
    0x1801140d045028007444200700c07299540b401000d0300c0342c42000200d072903442c08103104280c14071a00041c004180b02c541d0484844000158068507261a605d40703556020350010b4542c118035100c1c00c1d80014561090b407080324800c42c0d060016144039511600d0640740d24101e01140d41d048951011072800c81401c2d1604288158400c1d180001e076070408014800c0d1010031041002c12004036442445442c2c8501d50701409500e9045564541c2c0e951000801c540700401c0d2007000b4021503070402031140420022801c1442140c81e10000c21026503115807007440c07000280e8402055410242c0e5850200398081b1429501c984011404842c0a1180d404505407941444201046401642600d4580f0f141c6584403c01041c5100090003d03000c24402a901c400d064454494041200c480070400c02c0342106080c2c1c000c0141c0c00c0100301242003403c0280c022071594682e14400d05000074011144 = true := by decide +kernel

theorem cover : BRFrame.Cov 224280575 224460431 := by
  have h0 := BRFrame.cov_init 224280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 224280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 224280575 ≤ n) (h2 : n < 224460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
