-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3264
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:08:53.999589+00:00
-- url     : https://prove2.me/submissions/b5d1185f-0ae9-4daa-8286-c03fcc39b1a6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 586870503 ≤ n < 587050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 586871753 1250 586870503 586870511
    0x20a030204080f2410050d0f020d0318141f090b180a0b07020a060e0d0b0915070c08032a1201030b0c0403020603010b030a0e0f03220602030d0906 64
    0x1050407a05103404070006250365000362013910040c203c1d41c20b528800c502d81da0b51503d0742c2c0c10400300f0706010301d0309842868000c60710519804140700071001c4401001e900034001a40b22980e600d80200030300c4c200d41034500200304c84940410f0340100c40c4200e00c82c00b03c0250103003201c1c44031440d0392000d0411150b01c50080011510700804e03e54188800340c4141c040d02c00040d102c0302c1d02c07203041180c4040d10350451009000c0c18000d90b00540c1c1e030f580300701e001c0f18038a051540160582d04041200da083c0c8180c00f510b00c0c00c02e44144080300c000004c030f02c0840c0071070024164098031031480840305000c681c0c20161180d001800800c000507d0201d13034220131103c0860421f40e221280480c8200da03049000300b020041c0201c40100305000303081000582c401030f000708051406043d0b0b4005081d80c0410300035002c4c40b450200000d1070328103c0e5400803c3c28810321084800040c1a9602166250310032442c8100484000980da03509500781c0d04171070180c1d031641c0c0145042a0000503070000038a03040b8401da41452311 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 586873003 1250 586871753 586871759
    0x50c0904021f0c05120c030703123c0207050601090c0233090f10090f02030307050304211e03020a060501090e2b051804020f091201060315020a030204 66
    0x200404142c218065880b05040e1030011300340242032084818005032220010010b500a1150120803286c50700ea02d400d0617201c000701c102c244d000400070f1010b05002c146200b0380c0701e0a1031132a090000c41c4500b414803080400d00290000e070042c0c4c0200000141241d0003c401800021429000f02200507660f00c1220342030500300042d02842d41c0c0c500b07658030701c0b0600d00b54203620700c003481000c081c0d2110031807009099091140100a5941d090048802242c0380c0c0c828002c0100481c0c4203008010940050890303490300c5c03090406548a502a110f0040d4035511407a25200da8005092840507141c3c001c0c20881280e5501080b20088409224089007180100352800780011018854a4040c4ca0010000100c0c4044841c01926001d0720b0b11182e01c2a8101002900c942c444401c0e408806444504c0c020b07032940b000e8000ca4001d5500c010800c3e6005001107600c80c1e444005e0009001600811140b84540300115035616080b07035482c1c000500380003601b41100703c0350a800d4000f00b607244810701d001498159 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 586874253 1250 586873003 586873039
    0x3020d030c02060d090210140406030b040902031b1309021008040501021c060519080d0c0212030f030f01140f0405071106010e0403020f06190b010e0301090627050c090402 75
    0x4001c0402e100d1341c07642c41450400b035081c4020b002c5140034140c11304894000351420103602c140298130540c2c0406448142040180e255034104034000c80d400380841d014071603840d1174070301581500401ca500601140e406881180f0150296043c929009400c5090010016100312250310b4000e01c1610340d50340800c105903066088507071b4041c0101c0040800030b070003824441040078441021002c0329205920300d00a1007154404038030326400e140c036401c018042c14001c0c400b0034048601070210b004030780000301d000a2544020f1009500c9450503280500d000da881c3c0078808030074000362060340e80100080c4040405810070b0343c05a078001850b0301780f0141401c01c4401e5546040400d820081d80b41074400309103c00c160301001407034001408100a400585026003407407001c000006400d100300354980212440d26401104030365103206029009125640032401d103030703000d84405216058200304110845945040d040340318020a68021301820203c03007840208007008c4009401680d01488000f900c0c4400c1c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 586875503 1250 586874253 586874257
    0x30507031d130c0305090c030606040510050a090213090903020606220e031c020a0807082d1501020712020618032407090e0103060e12030a0b2803020d030c0206 70
    0x810442c0114a5210f1020f0080a0f6240984902c4440e4066070000700556000b16045a1110701910002280e07a20800d21051001d40b0398001c641119000344d0208a4580c507400070151040150030b40424540e84400800480f01104000340c0160454000718179070b403400e6000d1908a90600c011505200d03140351040d003c40b03d80d00740c01490380e0300c005180c450714100a07048a07a200d100f03040440c1811134070b074005050054000e200c40d0070001c0143c0010044045104686141d107035402e000d40800d08164240d21001c94140c5008a550402040ba4403044d07200140e55420780750314201001c1880300036400e000f550307001441108402c00850100321083d0300c0403c525046a4590301260804140d020403249481c0c2c8003815800400c02d1143d0b0900c54843c41030001d9044a40c8030000085512501000c507007030104040e110000c90100106225100405802030309517101c0c00c840f0090121280301c00b01884410643d2100f64400c0c48203410030240c1b411102a6901d203000b8204040b80081680c000f030b6040d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 586876753 1250 586875503 586875529
    0x203011a010909050108030703080408120429090c0415090905010506010801120f03050c030c060408040510180614190c0c090b03060402043c0c0507030507031d 70
    0x114800c10940041503a00c41d0441c00140b03241c00c0700708119414400700e030b0385900c40c000c009800c0c07045900103d0200b04080f4102c624004084190600c0b9051030b190480b0102c444041c0040c8000304200e03405411b904007003c036401202910b00078400b00c0c1070142444003600b804024414203901350100090184420301a00c40704c68400e000005103481d1400006d040410103800c584201004031002200003803421094031119609401e00c9600d03101c1d2418071030300e18410803014640034000c980502c0200304120b400761068030402c40c0c040b5811000d10340704640c07807070054496006800110320b041020b0350244004c0b000005140300d08a02d032042a5101c0c4c0300211100e525440003422400614080c04881455007000d1b00c11400180031b06004000004e60b1140c003c0d101a12842c0e552000f07020292144c402c8040f0b201c0608d400810100d00541c1d900c1030352081e450620999410115003544191103001200c8456603d5203030182051015141103603500b803448403d18607800e0318850042c0903521350100c4648 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 586878003 1250 586876753 586876781
    0x40b13140105040608070e04060203341103120c0c1c110c01030203040503222102101b060504030905120109050708030a140309100c05031e010b0f0307020109020301 72
    0x107549020305000403a1540c0d404a40990441c0c24203100740f02d103841400e07400c0382d081303e405a02c070b48542e58104050b40c1c051501ea900030480f6205040c122041110016250034a5124411020b41c880311107600d911030030f0890101c1141100000d1007c41480c0058014442100101c51004070b24020490350f2900d550100d102182c01101901a200c008003c00304800c0700a1070f06500754280365455079541d01484040546101c22410341c20048107030f40c5000e01c010b0811000200c0020140c0d22041c100000303800040c6e005400e4004401c00d071030301070302104294000f4210310842412103a180c6000406000c0e00440410003110000030302592049107086005441d01c0c00080c42110781d03e4020b20748172007540425041e03003080c48143c0c2c5494000041c0600d500340108420380d01d55400d580d41e4101120042050301e4617160241061013194040084c6104000110003a104265010300e0724240703e009104485102c10100540140409030801858120501d40004580d0b51190341c00282519603e0b141050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 586879253 1250 586878003 586878041
    0xe120705030d0207051e1501050d02012c1509060f030705040302040c0f120c0e01030e0c1507022103030a240b0a03141306090302031309020703080106020102031302040b13 75
    0x6c0d46500191111013010346110081000900803068400c40702e80512925111f944d0480c0e0560659000341c0c00c0d4891301320320000e520640340c2d00075405590350700c00c18485405032a180800072880c07514803044a0600b01c00034a00d60901552200e000129840100030303034100903050100000603201c900400449480a40310b103003800d05500da00420001d51050058101400c040d8a5880c0c1c5410010581901a0030700e00410001211001303549058290300d20344d60040020001d083c91007181101078a00c00d0302c200e9400452140e80b241e1200888000b01c0d1010158004101281c410b082c0d0781d00001c200c1810010943d001100d04100d16080201c0e40d00c003e400740000180700315056410b07ca07010480c40280121230300e0b82440005441f681c0c080d81360003440c10341c0d94440e030300a040c003c0084d108080951090714a8280c1c4620004001c0d42080034110040740c2d9220000c12414010300035079100e4042c3d2f40c42e802e11a0309940812000c1c2ca11a101c40342c001d811092124410106401810080c50010110807 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 586880503 1250 586879253 586879273
    0x20a0504020a2619050708010308030604020408070f05030f0a03021b0a05040f2f040b210112032307021302041503060302030c0306040b0a020d06050a06020a150e120705030d020705 79
    0xb20b1184c0f41c2148408010b0310b03100800281c070b41c0003010141035271f80124001c0e442e0b03620140860020300c240d030440c230141d100d060300014200c861140c0b031500f03489058041c1c1c0c64480e82000a241c4d648100744000300982c000020050720075032405c8440421100080032a50030300d50715800300701112080503403000d0494860302c00c01c2d02100980d0f03e01c0010358090142d598001800c1c0880c140e0741c0114050400003a03000200700700d15010100501030030324440d012507052075035696085103230b506c10700e242140412102c51005a0714402220908103d00e1440e180c03170710700700c01c9600300115202d0b90110006119070271b10000c611095103070040103000303400d034400150307682c1180101458519002c060600c254418030070400010038294207c1c2d0061603044025171104104c100a201600e032039080710b5000321840c3c50000300503a0001300c060319603014400390b0210b00010a0640140c80d103140c50360040d0b5006200c40e0084152a0300202180b41c02a000d60341440c8a0501c450140d90002900b036880e648014605 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 586881753 1250 586880503 586880521
    0xf020910120e030f07140a0b280501050a09150e0a0e16050607080711030a031d01140a05070c0302060d05100603020307090608070e220b0d020a0504020a26 68
    0x3148841510300841c04c000480c0503421903407041a00040c80c0206403400300740904070410402049540c810800e11403072074611040170f100f030310340f00d00c4100140304410301184650641c4182816104090000080320b81041c803036074098031a102d031130208091103240000d00f05581e02ea42500031040c2e540040340515200f00146c1c40c014890384003a00442d10100b0410907a44d84d5005c0316561684008210b46582d024245207808000492103603805014044500c000c151744425504400e14030418070032035005403c0e004442c075851040788208900001c000355905a40200090400c003032254026414507522540410100c3d000314110f404030b95283d40900000300b801c441400003608091504600750700d440c000c02008601a403080ca414030814002284c18103114101c1482c070100003405410f040000000000c00c40c0650800d041415880c2c00c0051840e860003a48804040750002c140603c040d04107810040250f22028a000c20b1101143d64442c44e01980c84a070783d001b90600c09070480c82d1505c4660 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 586883003 1250 586881753 586881761
    0x2d030b0a14130519020307170906060102070506030901060f0b07020f030a0803060405132001030b060403080415020a0c06120c05040b0a0807030b030f01090c08070303120f02091012 79
    0x403030700180c0030070314a8940c207844140d019808050711203400302e00360300c0d2600c2c0300e10f00d014105000100b0500000c20407002e142c01c03150120300558840480040307540c0c0d20780f40301d4480405a80d83d9006800841e0100403928001c40038581000380b038000024101d5484503900c0c480052070b0301030400c04501242d280e0542c500940f01030340a650603405010100042e54901c2d00601c0000e0401c1d01c59541d500101e90007030540844152000e87c406040c0004042141d0303c804107030b0040800d1800a4244284214182001c2040e14220b170752010540d401d090802240c540c00317000050580c4110702c034140c180c0000c5041002898010001034440c8256a50b0201e0700505030707540700e0307a810300b4864208810080452001c1c00c03580c84003810324140b1850740b9a807508030040e109415109902d171144c600025000d2074194043e16886110b1150b081c5826a01e03900c20b619410644805008101030305603480e091b103d02e030803100082000020062130201c06100140003010540340440020704502d42c0c1c51328030f5100788a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 586884253 1250 586883003 586883009
    0x317010b1602040c0e211c0c0609150906050a0e0705060f091f0c0605010506040303090605090102160f2922121110170712180b0415060e072d030b0a 65
    0x1140f400070300500d42c8042c01515074800d0040c403250392816010248060244072f81e41d010407441c0140301450320f6041250141c0000e0b50000706c09444c00c401d003002c4480000d071040071940007a00c501e0134144c00104031000d5800511800b50000c2c000e41000000f00540c0b88e03400204003240d11200303007408103410f221080f910140c00943c0590f5003000203201007900a05224125403c0e0320304a99104401c0004034100300d542e01e4004c04c0e0301c4140c50b0105220038a0104603094940d0510902607007a01c8200c105504030200c1e9040010303400c100910b40745189020000d8031a0b80c030551500032403550f1801818101d802c0f80a0503520307096522580304491034070601c20a0f40b040f40345403410010606042c041503145010f82110280002203142c1c80c642c0c00d01d03030440892a900140c0581c00354005040405601c14119000c0b1141031443c00407540c01c2200b0720620054030b5024004025030b0780d03041c0080d07511954620502c0181d0741380008616071040091440c0d202010903940104075103a48805002851482e50 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 586885503 1250 586884253 586884283
    0x60d05160309030c150209031614030604020d1211060c030412080603060f07090308270a081506010c0f0507050120030d0f0e0304030317010b1602040c0e21 68
    0x5a12000c244e0059040c0704c0541c0141401c035413450b4020200d03009110350a41c80d0740502548504010306c1c2074410800c3c0031180c1146040a0000d001e204141c1c4407481218000d40c051440100d000104003501c0e10780e4210301c80c0d0700701561a4444019940e03d040b00446805080c250004204801c00401c92078107030451001e810b01c814541003000002e5210300005000c50603c640c0c040000701801e10800001009503040008203650f02040800725030032401d80300082003030741038111940c00c090a00c209104101d0304803001030100200c60041d400341c90702005c1d00d000c5c1007180038885130021600c506a0840c4041c031a0307000b482c03003900c2c007400900f0f10012101100c030b00c5c0c20405024480000c02104491800c2345100002a444494599010052684049503022440040390200805400c0f10001a100202112003d01c580c2c1e1036819280602c0703100a203400c52142070070f9110040c2015041010034070030904012a60303900d01400309000960260206500118191483e115501d0600440c4c01350b10381f103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 586886753 1250 586885503 586885511
    0x1140a0603090209060f031207080c070b0408071203020a170a11010b0307061b0507061d03070b0405100e120d200c12120417010e06090607140405060d051603 69
    0x10f500000c40390380f03000304000d004056095602540780e60a02150b800d0910101c082515054241003404a54100344104400b61090000108031400c0e003600340c4046500c0e4000509006007800315907450b13141d484030218150310403c600280000c04140c40301d610f030311051708840d456072806100103200e01405900b40a441e40b40080f5072109413030129201c07081c1c40490404901c00300398880c0418418144040c054018002d00e800030030360035888441d9440c00410003600c40c941401080815403941c4041c4952511820200301c100414140f107880650941141d0411407290710f6004080f03408041e14003d0b40c0c841313402ca1981205282d0308031100c081c1080e44900090140ea5100c00380030741d107207820202607103c0c1d11603a601140d4148100091403900b001c403105180c450356038000340c00d004104403030030400b40d5092800410b0340000015038580b140912000620441d110900180c03400090382c0c101a0704000b04010201d11074032001c005000414590000190a15280d80c5481018046d080039030105410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 586888003 1250 586886753 586886771
    0x190e0103140c0409021309051023030634030e010f0b0a050402070f05030c010c120212070311090418030e06072a122105091f1701140a0603 61
    0x114403e071016100042030042c1c0d620004400000d07856071990020006a04010030003681703c035042c490700202c495400303161400c0980c900155882d1802203102507015030103040002d490203500c181408102c0d2840040c41443c0c0180c100342700301130f00c0701d00e10030740420788900030030200746400d01ca140740d06200c807401040404801c00028001086a00c135552041d600070603008140304042240044d02c03580001125502c00d186034055000c2d007052515480890300c0d0207400c4003520000c0c02114940055044c1d8a42103503a4000298010402c08100c0b4000700010b1021030400c0d1141d20030002608403010024030490144e290080840c905000114002c0704144403480005105145100501e20321004115030000010005580c00e6501d901170300c40303103038103815076801d0203066820f814145100c0300840160009810f0256000e100703141e401d903008103610115100050291104074201c155074a489903294000c00b0442e240001c1c20307005403050b5000c0d02c0c3c4200803840c0c105481d000501843c00c0500410f24 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 586889253 1250 586888003 586888021
    0x302040b090904080417060f4c06110d1407030c02040b0904060c0807030203010f0303050f0c06100906080d211b030b0319020a0302060c03190e010314 66
    0x41c007401a0302808448001c1801c10540200b590003a080700c907104c0c022003c0070200e280c0e98007c203850200800d8144c60106995290328039980407102040000c445c6441600705440080031031540c182103044c2c01840304404a1100000038800034415603665240c540050b09126080c021207072510310610010728000c50448480c201038500503a05820310040c1e080850004c5806001400f01466103c4400c03005c0004200c2154042641c003806941c0b034503055956030740140c00302d200c00c0c003404c1c0c40074035038001c03c00000744070388003c9c2014102d040710182040c48844a9902d010342c20f640c0c04014600300304040c00300c2c441d81e2040348002d1104c00c00801540d60060005815510f82402e08642140c464940c0c0c08c1003001030300400030a50300c3d1100c1c0e4100e40d8090b10000e0040401006e224880c1c0160801042031420111444c50103c2c0c004040c40c450609c0c56003007107110b60100501a210780803d20004159003001c031502d80c1d42c05650b4075154100e680d1400011300701c8014110100d002c0c03180c0410700c02e00701 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 586890503 1250 586889253 586889257
    0xb04030201080412031b1e211a0a0905010812030c09060c0c131509060311062a0606010f02060709031b09050a02040f0509070210020d0b03030c07030506070302040b 72
    0x76800984030352400c88010341c103c02606000030300088080b181c42d0041d42c410361100406d8540401f402d1900b204001e2030b0740c01c6030603e080c000588101408640c2d0135000703058643c801c41d11580d060700b000303401640c900040780c14800d0304d030b00400b101a55800108040c4600b4042060b40c58050f030b5481e86503241008000e0418080e40342e15500034200880c901c26400300c10032544c5003051008105207914681140901c0c0500b80d08810003400180b5500001800c3e0124002c000c00d49600c846185032005440301882580e81200d924090440c0c04402040303c400da040d109101a80c282344040c1c4024070788240054408183c0261400c03c660209080240032584580d101056a0380020404000684210307490032184603608006212480e000502140003065401807084900c6568200300840d5a00704102e480c0104440d07280c05070300724182e020103c4440d9401070580061240b80064042958030100f45035404c00d6544070b1342588071000a20074401c0402c0742c0c983c0b000003890158035103820420030501b80c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 586891753 1250 586890503 586890511
    0x706080609160f2609071403070b07030e0909010b01140306100f200a05010f0b01050307030b06070c08030a0809011a120c09250f0e09060a0b030c130b0403020108 71
    0x100c005003c100c514070402c518034401446445200804004014032404d80c5030568001170184500007001030301e02203c000d250791b0003074018090901d2510703180d4203884a40c840c4030120f04002410050785900e80d600712116000b00c910800026034200c2000006d040c15002e07080f07a0316644028030411041e135440320301500c044001440c25440381d60b1203120a6940d45111b4030005241020031848006004000540e001c005001d800248060b00c07800c40b02c04115100440120300042c03040000920450180e089607668640c0641101c0c580030351380d01da035490004141c02244050b0000581403242c01c1d8000c04640d04516000c008000c0048125601d220007100454200c0c040c10703c0c1d180b5107000c80400e200c4188840000f6242161034541400581d81c21520320284605001d60000c614110901c61004a14024480e4030340d07102039101c1008208906000038103465221598260114090410a0285014030030300360200c1d071108050700716540e078140d00382c1082403c19014031003080035030b0b4082410707a00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 586893003 1250 586891753 586891757
    0xf150c0e09063d020c0603221509060506011706061902011d0d0f0302040609031104020c01110c0f0c09161701180b031c08091905070608060916 63
    0xc0303900b14640c424036842c5032200806010302c84114603080c0d0f180c1070584110412090b42619054901c041c10440e0714042520400105014542e01410344001c1c1c60f15400b9880c051407001100d030381b582c6014400d54500c098111041900c40d01485800c1d60030140083d01c1c6080369036045d5003450f0841c08108030307000d18580d4006021250f50791121140c005e42c8030040c062421000204e500362540c1b18599600340c0c9814800020b4040481c07030701d10320302c01e2082e1000d0b1140c66488502c1c80c0d1442d110f200503408401010fa502030b0382001012040882489060800602c0c1c0c940c8a4842a2800c080c9081c5400c0d56040c0c400b5801c1000140e009a031104205548080a4800c080d0f9041d0080b80850310014423030141c0601c0e4052400120b040c4202c401030039494440c101c014080c1e0691f28003856143c1c0d103000100b0280035843d40200d01141e00400c0e950b81d101032100112000a5041505000c101c483c2000c29542d40d00072190501096a001440300c0d4842c406846203038942c106600b9a4280880c4e00100c501 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 586894253 1250 586893003 586893019
    0xc06120e062a1206191203231206010e040e03161a090a150e06060d170d0209130204050d0803090705060a0e1e0a0b090402070f150c0e0906 61
    0x80c902d0070582016820800006289482e018030b81200c078000901661068400c402c00c2985003039000e41c1c1c02c820002c1c0d03904020076030200402d079502510301c800014610704840280a4403503007800ea290b40134041220455060300100c0c1402c000140160442000c214000c0b400d100040c0282c0c04000102c6983c1490054201c400e031003141400d40c1c0c041520000304100348101000e00502c0000042c80e150000c0c0950154101c14121520200c100d8810100c544455009403000079072514290444000803809185e84180810103100c460900d6806611688a0b003a8045081141414214250250b10303615807401c40c5490b081800140380e040c010b242c020684080000040c041c0001401000001c00010384865141c9000c1c2e2000352500860b040394034016443c1d02d045002c0e01c0d8218024003480c0001401e0014000d040c0f200560040d07004951154200e038081006000181d545070360809400c0c01140507000d40c920707004605056414018400042101c81c4110b80816610f00f54801d40040d01280e90701 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 586895503 1250 586894253 586894291
    0x804020604030503160b0906250e312c0313061205150108070f110a08030103050f1b09130c0b04050f03060903031803070501090c06120e06 61
    0xe00501c1241c000400d40d0201081e2180981032558481d841130b8481e6800b18141c4d50f8000714103580780f00845040100c6c0c8900c00e4001c000d201003101c1100060040d162540052083d04085440800d04c40c0288252100450100007920141c2e1310226090014210900c020000140e848540b030a44043c506c00303540900c03020340500702d800c101b194504022010f1003000c00750745410280501c0010b80d04000480d0514000800081c8840d140e808268016142c0040a0312031650440e00800848044424403c0012480304103e4040004071001c0c1d200d05c2500f40c4d29819854024140641e491001c8550740c03005824500b111080840c0d5005008203503400700d000e13601c3d2607035283da42000200181c9030490241d40812030304580c000804c107960f425a00030411704201e40c140b607640ca01c1142c01c02c4591f00240049002d00c0c1c14040608031034101181121b0600340c29403207250071680d210030104d501d02c0440a04200064011041c020001e482c0c040800403c0c20b441006500c03000014440c20f510034141d107240c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 586896753 1250 586895503 586895509
    0xe010f050408061f1703030a0f05040c0918080f03100f0605120703060b180a0602030a0e040e0f0610030501050114180601111f0f050105030706030f110d09020f03030c0d080402 77
    0x71300020020450301d201503401c00503455849500642c1c100a40380e0502c001000700c14514080c0d11b0295502c404a81c0c2d1252510281c840200f14100c00002c00c42d0b080e42030b41d8042500351002d03040c6c068003051120380d03034208824001c00d81000c590000f180c41c01c000b1010031000f40c201c0180c0d0110003c04c54104000d64944030114000c1585802904a540012600d000364240314071000180180079561041d601342c5941c820390b60b90043d0543d40000401803403016401c4c3c20300b03130040b1420361111021216000320204886052080845211400c00d0000c0344c01c01c140070090044500506d510322111001c0c005800218450080c04040b2900c09540740c00802e040b64840d558880c0b001300054249d8012200454a42c04a42d0f884c4e51080c462030304164141080e81c036180318903812500020014181c0324a450001c1d00900f8480da02280c885540707503a0b441e84401032000500440548440000700e08100748104076840103c00a1203010707038028445a1607844001914400010050801000300c2c0d86500c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 586898003 1250 586896753 586896811
    0x4090b0307031e03020d23130b07031701050402271801060302070506010f06020715030609060e0402030d18140307150201020307090b12070e01030b100e010f05040806 73
    0x90180303220324449140f49000358403410280d48294262044a41c000700102e800241c00c0c10010318003614a0b18100103001d41e0401070011005610310543d4140e07540c85403607a503030019401a00449c1062a1550340000003100550140c03004031021400c0460180b1383c01000300b01d02c000c8203481410801114955a100380b00c80b803605082c1c28900c1d01030368444070b004001c0e4010f031400704c0d81441f444002103200f0790060b80c0d00301960031030750081101c17034600030020081d010700d00c0c0c41c8002d2650745e04012030741c0049801585c014021130350350f4200b1070809106141c03400034507225038803c01542c281c2d0401c4203e551484101201e40c0c07000000c0003a00e900c0c00007410b10b07180b82d020490311240400e4a10404e601034025621401184d11106042c99aa05610125101e2401200c01c10303075000c00000c0c0035030b0103860919440c0e10180350009001c091030340403615891a010003407010036480d03208441c0395039101e0302064441c5485c0c40d0517130070b0074500419280d4480015164440201d042210b03e08000c1003080 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 586899253 1250 586898003 586898009
    0x60d0b04050406240509070c1406070f0807020309010905090a020f0d1a030d0203120a021c09020f0d02031f020f070605190c0e01030504030212120f0906090304090b0307 74
    0x31003080035040c949009001440e1901d080006000540540d0180701c0050300808129170001e08110410b81d101d650803101002c01150894440710081208602c035601000154800e1442d0344031100410180f0350b0103081c5c610010821400c5600801c07505000d41da10135200380460340706031103d003d04e4035000c0440000e07001f0490f5150316010080354907442c808080d004040420040018940c214082c0e00c14151a4452000d000000d40d00401c0800e001c4801c0319a80c642c00901c4150050510458001c01000e4a0182c200166210388491110741549003800a06802ca002284d200700c8518096001c40d456904482c030540b20341c4000c4459805150554046400040310a104151b541c00c861420b0001082c0503208689800e1001c00b003070710000003d2103030104000c455201d071212081c12000440c00307000b000700124114000e40340038144910714000035100111a20000c501c540c13a02c140d01c1003800000820404560b4000010b000000c1c0002c4104c6080c0c6606500c0410803004420205e407821005c0e41c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 586900503 1250 586899253 586899259
    0x6061e09080a031e080702060c030a0605060f1b010c09061b020a030c080d020c01171902040b0a0e04020f03071202090307090203180a1e0201110607020604120504030503030105060d0b 80
    0x401c02c040580c48a481a50035042d0b5001925003240d4038011524244111644000b40e8854404180740303100440145500059604000ca5403980702ea000c2903954010004d0040100c10100714100c00e000c1305818511600d9100d0001c0014007d0108000c013100c2040c4100c006200000319000030440c6081c05414020340c028001c840b00d40c1d40da181c01e4070840c40a100c0d403400c0e4018900030009192012440d4440000b05960b0010703817040d03106d0500000c4101420081c020500c060030f461002138180082c10003001c0300310045460f0201050080e250700c1d008408940b1651040040c0c411030400c04054980140c0589081000e01c00c12901480091148001196051040b0400001c080d09285c0080d441070004180c2c0b800d00c11084038405590342c2d4140c200400c00414000794100000c00d03001c05140907801450000100c03903070041c1e1141000b1042e030318000160440f0040200f03201c1c500c0001c0200240501d0304a00e41460b544902da102e000601540c0d00c03981000501c0c40249056803c11080c2d05401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 586901753 1250 586900503 586900513
    0x90111010902100c0516080a05160303050f030601110a050606102105062e031118060906070b091507020619020703050903190c14031207060e0f0303060103050a06061e0908 75
    0x19210417580ea40d148c1104840c03501c03908500e9030140e0708100c540000c80f58140c032000d0403e0314803100800960801000d80341080b1071000c1c0d4150a2401b0080d88a0043c0268098080360501c0c4081c003500640c0664040140b00c5040014030280101d890b03050300d01c58600301c000803541c0b00c21000034020134405851541c00404505030700c120014400c00b8803c26802c5032410030140c035040310040e04a0181065843c0045801c0c100c0034224245040208101d030030040c60a443c20b0f802d640c400e20f40071015103a65402d81d00001c0c1c0000d00031500c1c660a900132609000a00c00c03498144400c1194402c080c0c0340040003a0003141c29020107004a0aa17001254002c094841d000b840741c0003d1020000d00c00c007554200c90319003001841402009035400520009406000301003480c0c074010902e6809030b041210702c5940c030909605a07903030901884001840400203190b030780c100b840c001001d40d400504242031181ca440e074200070b0180c1000d20000104000b0316201c840030304140d015609042030f07520000c03260042c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 586903003 1250 586901753 586901759
    0xd05031c0e120d0c140a0e040204091d070501030b030303040f02030313030318090b0a140609310204060c0b18030c0106081504020a210215090111010902100c0516 71
    0x340902900d003590545104101c0100c200034104c0b141400d2030240c10071781c102000082c0d50f50380b00e00c5200c0710000003c6c101602c2d2683da409210308036446190040c001c81100d00303050100c43c1d81409201c0c014003003460103111116102c00000c0c1c0ba440080e05c004c00c9045900034103800c54405005039102c0c02e0010b81c0c6604560b41e2820050803606050084680c1e200e58100b0105d0b5031181403054664a56025042c500c000e42001c42072404020040c8095a1040d82403000401c07507500c88104014001c2403c07107440d1210312a000c0d502d50400b80d0800c0030840f900500042c4101c03603204d1424200160003400c0d4010540b1820000c001c01c4200841d090014000000e445c810020150003e0341100c2c5020115003184190144031021540c3c05e8500941c0520409020044180504c12007400015040c0c20b0002242a42c1d00041c24401012000d40c0d100c00c011600791403942c0c00246452105051000074046034500f98005078420030722010b1071042c0202c5031840c00610030304102114007008000000504c85803 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 586904253 1250 586903003 586903033
    0x1b03110a0308061002060106270503030f2101051c02010513060f090504090b0c220f060305090a02010816030209090c030105041508060403030c030e031204060b0d05031c0e 75
    0x7150b40a02501d001ca44c1031080d18030000e00d141c101ca0590b503d00c115482d844511510411540300400a10400d1100109071030b9001d000420110f2440703607460b9624001c07040d100441c40742a00c14401d000501e40d004104a03103442807203111018141c007001001000d54801179a081c0100044034018960740000818407580102d0002107540d0941c582d214129903a0341000265400324000601640d50301c404524032030444005041e01842540301c0320036102e284404124412130f29840644106d800c80810458145c2501c211600800380710044d00404000c1d030006801c0c01c401608480d2494a2141b2003880284603a050b5040030800400c03504e0541001c58851020303410a0013158400c9192400361401c0d0300c2e18040c060704640f0800040c0c90996202e88083d4002c0015103032840c22704d0b886150910020205100070511245524030b55080e0b8105820150219020310000d140990800246100440c8000054030111400914a0115466101c0c8109c0207404400b250351054440d004d60b40803200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 586905503 1250 586904253 586904267
    0x8120306060706050f060406080a02010903061d0d0e01030f02040305190206040812120609010302030a080903030d0c050c01111303061d0d050c0c0d0804090504141605040b040c1b03110a03 82
    0x80000c687c10f1100540f0764002588508030914000d0200b12603000400c00240d198205401401e481072031640307032508008215007007641c0d1040345000035034034102d100e06640e05441040c07003d004401c400c50a00e030540d5511a5600742c006118409145002840e404640d1400200c0d000307400100140e0300d43da1002800c9a403160041d004800e110480c000004030075060031080c2d40d0490745c000300202000c46c0251100c01c500e038425208079070540410007500c244491603001c0c100702041c031991802c3d80c4950140320f1070b003141d07405201140081c000b0480a102003030710217074100c1500e82002001034003041a10b0f8241e40b07079603036400b40001401812440d41c4001d40040142c10001007503000d8800728036102041003c0900c0d001401800c040003030205004641007170380075680c4244215502ca80c213104040ba00c41ca0641900c0a07070f04040384081040c00345052500614801c44000d43e01400030782c00018014240c2003601405000611003242c0701401c1c14801d00d4410380d14000003064a10290316070800030102 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 586906753 1250 586905503 586905511
    0x1b0314010c02060f041e470114130f2414090c03091501140a17070b091f050414031b040e150a0204060306050a08120306060706050f 58
    0x260140030005000c45648040051003542d00c000c0e4040c0c80b014010386501084e40001c8195051748120b41000d640088191040a60b02c008440080b039081640c048641a507202c00c00b141f5041e00d1440c01040f100d07800491080c030340d600031240c004010000c14002001448058551a10a41400407000a42501600030b1000f042112400c40100762121180294580e40031982a004130b0b0f08800070700b540c0d1642c8055900405a007054802c521504610303071503140341c2a041080c410034400c00d003580343d25007020050014003000140d2001201c00c12360b800d880d00c189216500d005100020131030302680d10740350384941c00d01045003030f007602c25024480146a90094045c0000711b0b188811159560300c1c000844410312100c204129520502900c14000684101e000c440090700c10000049540c051424103e845901d1140005032258541075004064950030b1b400320340a0002c01d102404603040102da0410510313000292160780741c540d90003003030480c03050383c1016000c540360034240107818030030110305402 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 586908003 1250 586906753 586906757
    0x40306050906011203020d030b13090302010c08090d1409150d09060b0108042a0b0d05060307090506091303050f041401020d02010209211504050d03061a071b0314010c 73
    0x81aa00c6813000d41c40c0e15010b20740a40942d104030400301109110b40c11541c0040e1000e02035031114141620342078250790304003100318003507512101d0300b034201c0c0e40c0284543d0f0312680c084020081281c44900282c00366403c00090704507084001072500c100e48031110400382d000d41d070b1004641d4404615400340010f149400c3c0403a2114103200c072032060b40d03100d1150325004030b8001c0d991503036001c00050070074000b081c480d0724034020001455001400d0180d10025040c10060804041041d103031603810503052000d04d0b00202c0c0c3c507915000030b1004036200c012045a12401b00c427540032003584d440c10162444d00514500900204000502084840352500d14800ea03400c00c0e022285842104075003a800d0340104410240c004564002420a1400366280390501c20315000549480500141c4007142c4440b007110196500c0d4800c4198055082e45031280030300a04a14988000840809103105558481c210340507103500500340452001d10b141c0c0b00c1f000f004580c400d50000201d9401c01c4004e000c0c00180c40c1c1d10300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 586909253 1250 586908003 586908013
    0xa03121b0b06060a0e0901180b06120402060304060603020a03030c060c021f0b1201050a06081002180d1b080d1103070503092404090501050f01020a0c140d080403060509 74
    0x8000e861040300400305034000307a94021652014144030158200711190020050b00e80104190303902e034050001d0181031074444440c500c1952400070420b4407180380b82c4c0c60040c0301c01c11095007030184034854a9085079040310116565200d5080c0f02c0c010b0f2042d604080c0d80890481000410180c0100740740c028584162014400041d04039000d0ba1070b410300046691050b00e4070988a107104c212944200c0e40070a0080160078541840d00c81942103c03400ca50310011241c2e034510512078103104114a84503544a040305500c2c0c19041d24511000e1003071404098001c2d01003411210410180040c141040c248290444201c4c0340e45041180c0d0302c0440b0b10015010070b901d000e000c0c1008901004581600e604407001318500b070400030030700000341c00159040480b4084042d6a401681c0c0103070080004000c0250b0200d410b5060104020080920308412815544400550070004400c4184201180d0001d0300c00054002c0f440302040302e0004100008002560010703022040001d10750010f03008002100c2103031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 586910503 1250 586909253 586909277
    0x50108070e0612060714310e07050904051314010504021309020916050415092c04060b220e010501080d08010b030a0213031a060916050c0c0a0312 64
    0x40100b54240c0c1d43d548542d0010400a25480e00030324002501c0c400080b0f14a1600d488014420692901c07000344020502c54510744070685c8a038000020064190120800d1050804400240c000c1c490705502c98021a141d50010740c0540302d004507040d8140e0400c42c0812a0b03d110301116000b8401160100e100c1c0700030006240b0110780c40d118403049594042c1c4240c11927100c40c680d503010380c01501107130005c00004000203d003a036142040442450f54585407401c15900744803604c0c0150401107001d840c00354031460b00000c28440c441803587c21a802c80360004030040c4045c080380d40451400100c4440e03166500710500d054105038070007288440c40e0002080303180d80710b00c0d1082d02e0303240402880c40002d0f500b40052104020034001540c0005882e500113141c100c403112071755500e00301503000f516480740b141108510542e420a02607803107003080341d50414600e80401a412a400702030080030402102203100b582200d4100300e8650341c4030000b4503200100ea0341e498550f0066804a80741c3c00000d540c000700c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 586911753 1250 586910503 586910509
    0x30213090507180b03040b15030a170c010c181a0304081c1a090c0f07080309070509040b15030c060d02250b1b030708070c03020c120f0d0207050d030c021201050108070e06 75
    0x3144608e10049c0980144601510340c003128601410000c0c640020030044107100010910a02e00c1c2c03c4d8050f15041e208640030400700320301544550058402820841410080031501811660b101e50300842094950856541c45010f014440360b000d142580340c0640441c17040754500708030080c21012607244025566100400a15000d0262801580711003804401e0010301c9080241d90b100c115001102c02244d500c0c0001022003a0a170b5050b203034441c04d84140036120861400c00c00c10345506074002c08070221500d02143c0148190a0301c0400ca640c04111b0340b85046642590308001c400c145a2000380c0a59400c2800c20900c041c2c4207541c45690003442180e0f0f080f803000940c0d20540c46130b20b4810041e1f4820340c056401c103805820031421401180103030b1501c2e60b00c00e81c2040030018104010030b82303c802c0d1403102d45400400000d180035580900c0c07003040f0700d030741c0c951004459962619216401200c984081600f50304216048690380d400d045c00410715020000d000000c0383e45c09103203410030351a06004c0c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 586913003 1250 586911753 586911781
    0x51515031c30052d010303110f010504082503080f07051909080f0a0b0a0e2a030d0c020d02011d21060106030213090507180b03040b 58
    0x9a81e0100d0400c1c0026400c00340610340024414400d842c1103814001140c25495500001000248805649100348000c0300c032440c110b0714410f4820b500ba0701c544060386405002d41d2505100c010308100711440c228070312a4080c000b114510031160b000340a2402c251402c503905400012005180001036240311410402c49000703c0c14944d0141c0355840c071074890503c5180c00c00c0c0010000c07014060200942c02c02701d8400c40791402c6504042c1d8902d00e0392400c204113281080d034201d40e01c0045910580040c40450100714000d0340146082d480004c0c4105c00c05141824000414041044010300014000c5081c0c074101904090100171000c1d1190240300d00b4050302c42c1d00c42017001a41060b40d0511000040d400388400401e04000303603642c014561420740000f11014004074903482c801020300c101c900400e4080108601414290401b5400c0281c14080350308441014810044601d48840204103401d024110bc03042c14413801c03040490340c940320b10744088243e000341c41c01c5644003d0803000499070814030350 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 586914253 1250 586913003 586913023
    0xb07030606050f0a020a02150702040c02030319021305030d091d130f0f02060f0414030a11010f09030602030106050c1b1003240f08060a020910120905151503 69
    0xc5443c00c00144582d14046900700351030781c100394402d0301d41e401d015a840302101c25042814030080c5544500798414007080d10b8890004100350760090081c4408113031720800c03e03a01003074058801601e0715610020b480c48035056034800754140c014040c04849155000d10964251541c200c5404410b0300401260804100c0440f000c3d007100c1c18980100f030000c1e4200c1d024414103030103014190841c0b0410340018100c1e030300c92071500c0c9001d900010100300008440b40c1500c600102180540400c244907261001140584440241040801c84000c1c680e02e01940c01100a99000203045490750384500c4081c001364400000c08150384222044060340c48207000300080030751005401c4861035030400200741c005c0c2040304d41c166009900700e8245582452044403840003800f0000a40601d0b91070094002e04080d000350031214018010040078040e1b8440484041007501680341c0b071004100039042c403c005052040c0c0050190151641c0081034680400130345006144031544041c80b500410304040e52040140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 586915503 1250 586914253 586914257
    0xc1c0201090b2b06150306030206030c0f0f0f04050418051c05040305010905100c05030f190e0307030c1b0609090902060c0604081c0204051f02030c12070b07030606 72
    0x910140035928031a80a000c01c2e140700b0f0400100c1c0140c03481d080c082c1d040b07035a903600e40c12aa00c250801c40c96002210650641c0102d041c100403050868021480a02c00200070005035a000034200b40791070381c134008a40300d0644508219490707403204a59108613510900c141c1d40320390f0401100101001d080016802c40c141d0000050601c1c0f0981c80d420303c0c8036542950b00b2020b00100b0312001011500038050301c452540300790054483c0929600d4940b01701d408200a1000b000018400c2244206207807051642005408060740d2000328001c100001400030820002003900000c07075588200f41d041110300c24410310464481c07190a00300010b180c070030091841680b00084491108110b801802d5002c14000b5001515061400300541001c0b0b141000c107940c11140e803074000402c00442204180c402410104943c429490640f8040015400180b000700108649162264461f01c041c020400c55000c02040700070364000d279000e015a540160001c890595045c1c3d2a00002051544a03203c0d03402542c0e015 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 586916753 1250 586915503 586915517
    0x70b0304030e0f04231b160c090c0c03050d020f180f061c0b0f04020c0d020c0423180106060f0806040507020616091d060f220e010b040207050c1c0201 66
    0x117064150034540150070f0320124007020290307449a8001100074402c60381912143c141002c020b1600c0481c0c48415803084100c94504220070151650210b0855100c580618040e80c583c0c0013003d00000074800d48181580c0d011001a5400380b22035020304507602c00030215000d880340e42c000300034010903115600c0004208091100c806940700359940c402c02c0280c00143c10141c4e00703030003400801c04a074403259240300d251b4001c208002c055a8100715884c040c00d03090b00c0501c03090300c2001310084c1a183c0c1415800780e00d8220b4000508101241c3c442002107801704000307102603592008050060084e0307020745000070b00c001d0002191424103004040c01000c403039004100780c0d075800c2c0c040c240e00c2030001016000c0211030f0800058200d0400c455020111002d002c84400e41801c008218018100c8681c5c18000e0b0400d014042040022030036508044103000c40100700e200d191b4140c0c1d0700400e001c0d00c0080d8010f10118140090100014881c40041410354a207031200c050580101d20526141c05c2c028009800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 586918003 1250 586916753 586916801
    0xa1b061710052e030b0a2105190b01060c031d06070f0605060118140d020d08030702060117010e0d080907030f060506041128050d0903170114090c0c070b0304030e0f04 73
    0x28161002c01d483c19405200d01c04070b50203030b0390744c1e017801994400450b27040c20042d00b00c1e060001c407210850050055062495529003140d80213002240c1c00d80c1c81800801c0c1e000c940c3c01c41c40d1a19022140d40e690300c42c44000803600d10345401d40041006443e0140054000c12148280d0364101880c84103861081203010242c030045010065103442d8203600320b030080481042d200000e07200300b02135406402e4a80217070140f903040c070b0500d14403c1c1010060b05480e03811302030341c806c0203400070031210307402030302494100c00c190386104401d0301d0003a07180c0c00103000c0840700c40c41c07200b44111503108600a00d400c4030705020403c80d10f8080702c070340c0c040c502007203062000d07090100711030ba424400300081200e1141481400c002c50b002002003260f4214805a010039042e210f0b0140b5460440c0c240f60242441001007940c0c1401680400d1080c01c0c002c01128013040d00045000c00d0007401c010701401003000138200743e944d14040c40c000305005180c1d45a9401046003191020a40c5040e010707030000c44804005175000d00748 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 586919253 1250 586918003 586918019
    0x304030204090f0f080901020c0d320f0610080a15020a0e04050705030f06060a020a02121507090602070b070b190b03060106020a1b061710052e030b0a 66
    0x4241c280444090103c45000c1c000100e505210404c0d182c0140596900d4a081c140003a0a0017512150b003031141800b80241d00008080703405484941f04200600221250701d011200104441c09901e50b86610230070045101114000910350700ca03036070311307141c1c0020316603500550b070754640a203c4010075004500740c2d450800e2501e0750103804030915034a01100c04a03450404101100c0f000c0d5500c0c8006040001000310034804804071f243c12200030f4030000d2808800d8500291982c1d003002d0000d00c10120800d030300d031502c00c080014001120801c41e804540342003a45c006000302a042c1708a401601074007000140442081040d035a205070000c0d80c503583d070303918808218010342c850390140322003503660300e004103007130f24100107071400b0744000d07001883d41c100c580c2884c2c00d1003131146801e00b0100e0729404062150036030200c260305a042d80010660116214108040c030b1400c0950080380d00b04e10078507003004201e010101d000310700c0a0303048840c40c0040c804603001c0b001d60b0041c80804d034000b11907142c1040805 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 586920503 1250 586919253 586919261
    0x301020d090c0e0606040b0a031506080403020613081e0f310f0501082a03100803130308031e04050a0b0a14070e0103150b070215160809013c0201020c0304030204 71
    0x9003e034a00010b00c2c07032a00c00c3e6002c10035000e800c100001070cd9241044200b680401211760800408503000070341020b80da1300c890703003481220032808008502031038111007400160182c40c04048078003201a150b502980d0303c800b0302005003180c0589003c140c0404c260010f4000c2d51041528030000445000c64248001500c0e0074502800b1034805c4440d00c8191108078031402c0c0c04a00e10b0262521055480c2040c820056011909402545031034004006001d02601780803004000c13664400c85403503d942c2d410025403c0c19210105c4549103412501c104010000080307007040000748034260030082a00e901d0046421164840d5040c0e441c80040390124248a0046c1000c5504840514002c0303046900300c081100d2481d05540036581150010404804500c0d05406128810380315000003424a920f40344c483c50454100c02c0f011304082000915100785074070803d110310501c0b00b91001018920b5501c030f4850b809003640444140304501c1e200c4c180700e0103403041c02100c2039443c6502c021402c05085400b040018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 586921753 1250 586920503 586920517
    0x904031e05040b0a0206060a0f0602061b040803070b0405150105030d0e1318120201020f1602030a0804060c06050609010609030b0a0f0e03040807092a0309020301020d090c0e0606040b 80
    0x1c403000707210014603558058001c1c070303000130507602402c16030034450184004e070010b039000304015010416042c00b025500281c40c03540110400c462200d01c80b008041c41445100d04d4100003168000000c0d20010710001810481c000d138843d008489884107034104d0011b1b181028022154160480304a0160300b510a9030080c1950f04001d201e502242c41000e08a801c0780c244007403c00d01c0c42c1000c1c0000007840041d141d642d0701e12240d400258500000c04201d462144220349458440034070050b038081c02e648040220748100355000032090342da0f42d1902d5001d81210b00d01d06040340c1d8030303060200082290500381c03055412211a5221300c0080c908580c0d50301d1104500030420307000913594003200101643c150064040b90205400515591810207006600700000c80e0460000641011030102001011010001400c1d510030204181c0c454440c408501400062802942c150f001169920340c003a02944038429440c8100c0b0210452503807070302e0980c200c2804945907580613001f40300c100181c2d00a0303001000c00c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 586923003 1250 586921753 586921757
    0x31a0c0f0a0c1103100b0f030703170304050705061201170114011715100501090915300602030a0c0c0b0703020a1701351b0301060506040b070606050904031e 69
    0x10f9007a4070200e450201c24024110800391110020455820141d1641c0d101031020703005021032a0a540392909001980103a0303088141d000000034040c804207200800142000030880c590b64070a0314605a81001c013801402e030001146804840d8010b0140315180c07038464111010304507a80307000c951061300c0c41c03e00c840c0d0b242c90150240720102e1012180303115216102c4a00100070140c2020001403410354a0f170000490907190001c85044910300c1440402214001030600e07c4842045803e401c1001e00e0141505071200302040070401c202150300030758070958110104011090b07040d041101d41030030302080504401e681c4400314080f00c0c46900241290400ca0403e4000d5a0610908081e1071100343d000c42d407040003c2240d0054146d100303122540b25454105403aa10142c82004d685c1c5811255003450305200f40300384200e005480c00e401c03450040100504246c0c50781c0c1c2d203007a000440e40c00880200d450a1820801091901d0000d000380c0c00780d17400d07a940c400420f11502040d20280c0ba60406202 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 586924253 1250 586923003 586923023
    0x160801150522110a0e2b08040b1303030e18040803101206020c0606040c0509010f09080102041d010806040f0f0201050d0c0e010809030f0d180804031a0c0f0a0c 70
    0x21541c00b58040c640c40d1400c0540200d80e00e413031400004004800d10201c0f03601c103038403280080307a140700d031000c840446002480d442c164421040c605120325210766071280840700c1c800b180d00301b600211802040122030094650805450300301040012080300309004805d880081004140440c242c0707005981e000c1d5180d00c449445a841c2c8e00f00b156480c5094000b1107445400080420030008103104603604040c09480c140f08400e21043d0141c114040e6280041c100204180003d40e0607100f070003000014013400000310766032520b6071400c0b21600440469090264105000006c010000080151099400c00d00d9032100c2a215946c0103000d22804a05a0402c01d05000d0102c2c0c0c19414400c65145030201d03194440d920380044001362103400300402a58840c2c00a01c450118010070b03d040754a030191641000480c24481480400300400c1c44002901ca0b8001003400301c10440c1910001242ea011283c0c01519581c4928545606104102c8400c1000c101803000c2c5126600800d40c017039009203d150310103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 586925503 1250 586924253 586924309
    0xc030601171b0d06050103080d0b090628050a060c140d0206130606150c05190803070e010c05030d1e0203090c010e03010b120d03060902131a070b091608011505 70
    0x82c09031744003a082964049800a210f8003241d072140b29946102c4000e4860802d40d04d40031000401215034a490303903038080001043c80f02044007040c8003030040e050080032941c000e911030000402d400704003032040312002c60f03c0644050004000420041012070f540c002e005981d03604600c240c000d03a020008580c107948075003010070041c1d4260180100c0c5e2910741d460131504080c908015141c030b680f0b003001c040d44054454088000c2082d40044039448403090034100c00fa10340d49001240c4140c0f00706009405800042910703040e44d2015040000d80c0381c0c094100700a0b40340544111800c030300c4250744036466a4054001d1000d1540110000024140c0040001070707000420000300388048140d11009003e908940b08084007180c05114810140500343d808600f058240c1c200c411042c3e03041e015a0130a20410f00c0d00c2030690000c141140d41e810360001d46501c0c0f605008005070380d11180031025031070074a9001070110b8402c03814401d082e11a00c15030944850103240405211280800d00400d00303402c901d01c0d40c16 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 586926753 1250 586925503 586925513
    0x2010f20061e1302010e03070504110d05060118051e040218010311070209010302041d0307030206090607110a111504120c060c05030d0b01020102070606080c030601171b0d 75
    0x40d85540e03401000340405281070140c00b0681d8200624036000d0140c4881480142c0001d20f0b1200081c42d4213080c40c4195030351706400645481010b03800f00394854189054402c40c8040e5038007914500c3e078041c40a024a459020040d603030251494180000c1e019481810090391030109040d4440c103814051f90a0141e04140105040e640000340034003803014000e0a00009580c944103898aa080000c00740e420416240e0001d4500001071001a10990b12040c1c00f1070000900c81202d90307003100740800c4980d41d01c494603010352a080c0c1141d1019040c094400007400981c029500229407221a00c05000000e20541d10542c408050040480d000784008038420402c140c031800402c050b010004404450070070303c0c075042c02100c0903600f01038104000c0070281e07000110004166490000304000110350000d00c0c3d00101e00a000e0102c0c00317048070341042d40019081d000828145042001541655040c1c0e0300c55030a108284001d44100070168803160255840ca040c41d90101c034600b400070180f117403100d134036112 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 586928003 1250 586926753 586926797
    0xc03210f0a0b0f15030f010b04080d2321060603011203050d1d1e030915030705120f010305011d0c0f0a0810060e070207050109060305070e0d060b0f0901030c0302010f 73
    0x9540310032030002045c40460702c00c1c981987d004100030141140b803e0b08098000340c03510f41101e840c4d410700c14401040d010034909007240c24005d5400c4030a00e611400207145080c084074500d03104962540c003034030200314982406000c4034103949020b1441c043d9200b0795a001c945a5000c0d4103242a4142e40e10340c100c00700c0180c01c0340741003000308440092846508031310b0214903108410034240303e5a44100300003a80390311040c61f00746007101040c102c0707038403541c841074240c4131840fa0b40c200c0d526909401042160304035280a00a051728050340c000c014202c850354a02000e480d100e400050160300c070240303140003031412440314081d0100250004020991704c204582c0b0707100d891001140c01e95120a02030009018a510702d44d88105107100401ca6540342800103400303254a4000d20b0101519600000d04940c0602245440c58001038034803160b1f8031903810036200030500e902c00d40d44156a500480b0300c1c1841c010085078140c80e00107650290051440c1e00540b04040c2a510b44018440c0c0c030b805001e814265280 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 586929253 1250 586928003 586928029
    0x207020114032d06030d020f1510080a050d031404210912080c0c090705040e1302060a090501030b0f0310090f05030301031b0501030903081810020c03210f0a0b0f 71
    0x40380100e4200b42c0105406c102074040fa040031588902900d000000002403030183e02d00c0600c00d2512561900c0c5400c00d02070301250401d03465807007081d25031000c001c8002416820345145a078204140940c891410701c603400c0540300604440750b0f100341135402c6a4030000755102003219081ca480c8180e550418034809464409007036603120310128407145800014000301d1400c0c42c044030851014a480035000d000c9010f40c0c09035000202c141e000269482c05518000c0310010f400130401e542300c2c40160781c0106486614041c01d80068100074030384005091840d080803500c20001c01600c1c0d19044040f010004090080060750381340c07126a20740010035414002940610f004101d40b00b05101c00c00143c601c100d0443d0b000c64101444c3c40b0a80300401e5020103901c1e00010001048030004c1412140c003232415000840078039080c0d20020f40144104400001000d0030308840068680040503500c1c030803490a41101c288402c000c0d20030004865602e243e1003c680f444004100901e81c000500201d401034402d04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 586930503 1250 586929253 586929331
    0xf080a200406090f0605040b0d0b0601020a080c0a06060812090103150e04050307030206090606060d2d02090a050307050607030f030f0f06080f07081b010c08220603020702011403 78
    0x5040c44c4491445005880c0a00400c1d64207001201d00100402c108840031403001d03041100302004104168409e0107007102c41c0703400c0341c0c41e15140c14030350018a0f12680320800440d042498110300244040b030205001c00101c0054001c00e05000b038042c0150068503003c15124024000d600010464140c264270981c0070380d001b40c3c007d41c0c90356003e29020b403070004c001e8070700d400c2544614100104e0390340d11002c03075881040b0304001140000301e404421403508642d0065010880d01e940d203141002c11168050030070004100c40c00340c0143d03503030701c1490348600e02401903542140007003100e100424040c607140c14802d801441e0005d900e48041e0b006408481040149012160b01c4a00400c9220740412003608100c103104050106107180c01000e42d51450b019040000c0c0c901440c14240300383c0e000e05440d08035031350040101c56841d10040d04854268030010b0000c411a21840e40c0818100e11030300c261001a40e06031501c61903100310381c004517400c3d000188030b4845500e40c2081070124080e15624011200c80355 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 586931753 1250 586930503 586930511
    0xc06010b04080f0a020d060c031803050c1b03070b03070c2108010e10090c0e0303030a060501140a050d0203040c151218020d06110412030206010f0f080a20040609 71
    0x40c5040d0402c0420000f0b41603d512205007480542d072002000d40d0f00c00c0e0b000710002004064444140c01400c0f80803c4500b40a0703d058103c0d0a140c1c21400601c818441602541c07401480e80c401c0e06020003d416072190550b118490901c01c03c090240196004000b606080050104a58902484800700100041d40820784024006107035002080d03a80503021002d40000c0c01e107060300c040300044410744034005d034803600c5100300408a8060100304400b004050700b076a03521f02c0e2810f200801f8081c03920440f0700251207540e40202039080801601e5224000740da94a151145800d066406508007400540d00ea41c0d02820000c1c038666050058020701016440389000391501c0c007840300032685002810320144400b07100352001a641c1091003890168800c1000070407070142041c1030014007403030f00030044403031084003c14241900020054100d400d0403014600325520b80388106241c2d8a20300c15001c5541c0441030050006105005860034507600711601c070f11003810700002400707540e040d83c05411190341c0c07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 586933003 1250 586931753 586931759
    0x61103040c0e0112030e0904110d050303010f080105070801030b07021c080906280f0e030a020307060b0d0c0e070c12050904140f07050304080904290d080409020c030c06010b04 77
    0xb001e0b0301039004000b0724540e9881d030301c82520050700003548a5540392060000c00b0000d400c10400303a8044a4400001d0030000c125111490131559a9000b8043d00c0f000c805500c02c001a01d51050040078441c466a44d0b400c1d0b0540d1943e1340c1c0e1308404c0b81c05003000d0294001c2681007405000c4031602e000c80034000f543d810b541802c1c401001030402d50060514442c9000183e00c4070821281000e458101e6000c443c000640664441c5801c00104500c541042c0305010014802641c00d03400030240c05614000c4604000f070f024003c08000d152900030900a003003443d0380780108848801c0ca00c0183e400822401c0490503a031599440070104649549490003094010450001c50f08061041d0450a1040354001c1d140303041695081001c140010500010450008001420000c130701c0d05958144002800502c0709807840a40b102d9800f1070303032990182e0100403d034110750501d8107041c02030505400a03032407450582010740c100c002c2d40c0820791a4003c0c1c4402c0200c5000e241c41001094002d20ba000921501c0300c1c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 586934253 1250 586933003 586933019
    0x30a0b070f1818090f0303020a080a0203160e120d0207181e020334080609040308010b09030102071a04120906020d0e0d0f0303051f0803030f04061103040c 68
    0x1494100400420010400d103001641400c2c500c0010b07101d15505000400200e89103010250060490040446110390340c04000c054145d00a0301c003560564461002030b1742c400007020200d000c200c4128199116001841d07080300d0040e58420344020001c3c04040441a002c00028a050401c04480300184e009907410043c0010f507803983c0716800071480381030001010004100301110b840c404401c2070070340d0000105610300720941940d02150862910100c0408042548100011101c10110045004400003554515119400c14856a85604c41102c1c0340d0a00e030180c1059085000b44581645d8200036460200c2d00501b4000c009045003611021941303454905540200051080d10060054600c4280016500494056003505041c90b10450318004000000e2003460505009004604903051040c00d25034543c0140740b1404800e510f01e041410903441103c1c145805100303036040d41c2c10500218031544480414190440d001d08802f00c0e43c030903015500a110b0b402036a0450300d12800c1202001900 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 586935503 1250 586934253 586934267
    0x60f2205041b0e2107060f02010f1803080a060b0c0c040c110717010204090f2901210e070602060f01060206040213023109060806010f05120309030a0b07 67
    0xa00351200541212500b0401a0803888103070314551040d5441c03454100ca81940d005440480e528010407690850703610703403016041e10b1064076048015401c1540d41c508810450203120b0142c000845907160520039510102c0c0c40301d5000c0c004e00801c644900c00081e5200300e14000c0c1c048000108080c2540c0810002040120303500d05025400b0f118049040c003c0400c4040740d42002c48050f00e4070065000c41c4515203d0081c4515002005020320386002906e40c600251b108108001d203480180240c43c0e8100713441c0b0442241482c140d80003654038010781200f0000b40c03910100e02001000046103148400580d507041070718540040c030050b4020b4040041480a010360340d801041c1900181103039060540215001500c407800f80f0042c2600041c0c40d9182d052a50165889814240c0311580d415019064008040b1300382d1044926803810128007040026012841d24105c03075010000c882c2984c940018804242c100140b0300000f0b00041c08042d00c42c0d14240301c0400c1d40c85c4262441516850a04c402038208 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 586936753 1250 586935503 586935521
    0x6081b0f0414040f030219060b0306100e06060c01020f030403180e010b040e070e030a05060628091104080102030415060605070b0a2f0301030302060906070509060f220504 75
    0x20380c100b107103260361a000400700da60400c0c0c0000d071603070724413101e41805c1c0d2801d050b60201d505400b09a8001e00c0c00d03c01c8903813220310101300440c1500c036142c03070f007900c01c0d001101680125051005040c02040b990325148004015007081140054203008220340741250300d0b00122800d60100300d01040e22402e410014818a0140c4420a2401c0840d414005c03080f1310b5009501a45c801100c5840101c0c0205000d41941d20072000000c2c1150030408051800c80c3e100c041c1520149e001e01d8051402061803a40056800b28076440f80b001d40860b139181401f282c011340f00c0c008520f4ada03000c080001042c0d03a0000e0009503c203038040c0350812200c1c0c1420f0f030841c0403103c588c1d1140c0c08118044c4440d20006141202c100e420100b00780010540c0401d517064080c1400080401c81903058419420024000d0101c2c059030489002c0d800313a402c02d544e00003826468110440d204000a80c04226942c030524181015088d0140b14040213410034060710040103800c80b98448102034200410f104000503c0c06020700500707 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 586938003 1250 586936753 586936759
    0x8100b0406050a08031c0f0c17060f0d1104110d0903090b030112140102040f08010e01060501021204090507090909051e0c012a080304150605030c0904060b010306081b0f 74
    0x50b01e480c001310b40e41c890060384c00020311034083d1401c50121408580013221100d84d4a541002100c0c0207520107440e8070f448084c556494a0704d00c0004171b00b80b03020314904d0542d0360050842e00d42151155244030301078080b10401c5512603a00d504071b4416040c05405048900742e0805d0000d4114003509000c2c108010715803210091403010030040c42480850180202100d0f48014255114190034a216000e40125000824070700c0c044600055800815008583c4410480008002158031a4012629911084500c1a81d410108030400c100000760780415440385480c9412109140c4070410401641e981e9441a21b40358068a01296003100900401c40c07981c0d981c1c1c004000410980d0006410480b10b80c0c0b0b2500004a2201d43c1480440141551314089030310401240c0d903860685400d120307480402380314040c910710700180440c0c2401d001402080481004082e01d01958459490318081e2250261031410103803110302c0011030100c10004002649900b402c00c0c5000c1104400f801220507000701c1d140c0c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 586939253 1250 586938003 586938019
    0xd021b15010311040506010201060b0c070f09090c0b0708040e131415010614040e100314060609130f0c15021513111914040509030913051008100b040605 67
    0x10008122121108040f80140d0303000c1510754035440140c0c01080c096205513009070b40002c03980b143c500c01150308425140030803103c0c0b2540d80c4503440503044410080c030040035042082070034000140c844020781595881070490718649500c60418403d8503100b0b544101004030101d00503820003282c811400c2c61160280018824041c00ca412030390110018031401c6c050014108216150f494000112406026520340700d680f1401c10000500c200039003440b096a507000c1100c51710050620100d55240a14001001d4101d01c3d100c500000180420960040390001d4207028032800141d036259150300100030b00c00b1500c80c0688808000b0b400c00c2c0b00d48103040c000b00400d0041000404007130804d48030345078120381580391110300c0304042079022a68105c0c02940780740c4200001a0044848403e0b101404103507424010364699085040d542c2c00350745042684440c0391640781101101c66480698410170094070508a190746205007428180382001c194011902e40303070360521600749406020b000381006d41d5448 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 586940503 1250 586939253 586939259
    0x403140c0c010f02010e1b0a080a1136150103090308191811030111030402010c0f030912200f030a11040f0f0b0310051e0406020d021b1501 61
    0x5444080c0710302141d0600c20b00d581ea52103058400d5100d8001c03001494112000340e22454140c1400d400c801c02105d00c0f5600340c1d14081148400450004216680074840600d036181140410102c075030b221040545881c0c40203101d40340c10741405900d00b4440e900740a100314500f000c0090030202d0f108481554103160400c5242c41c0000e50081c0c03e2030380300000030310b81a54480c0300f660100c040c2c0708a81c0c0210010440c0c8102405100d000344140300d2840337007100200301f25010000da10a29000445029000c191aa0200004182480d48940c003142c820f29002c00d40684640f40c01c040d0100b40751059a01d9a6141e0003800300508070f16010105000846207420b0f01081d89000946d113030740d91070f8002c2101115644220f00b985494100300c1c6074186226062200181c001070000c0140102c0300d88a2007841405848007903a2040d00c00e40b40035804602e4038540711120b0745d001a11503840508226040c075400c104414681c0c040e403018054586000c001d00141d00c0c030310481d0514040c001c010380811808008010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 586941753 1250 586940503 586940527
    0x503011803030b0315011706010918140f010c09030b101a0a020f060a0f1529040519030320030a080702030702030703110411130902070f150203040314 66
    0x11a40e019031600d0301051100c2682c010905120005036240d0507030f900e040002c1041981d0550b500305002d0f482e411203c40e03aa075500c90205559110700403620b5200b600e43c01da8042819410f10406205a80d811030310700d2440c0300d07001d0b400c54a46807da6000208080c10074000c00c140030130010707001b941d02101e82250314184a81e002150788032003004070700300c5400550880d0840c020700c44102069203074000e07101d43c3d00d04110311702d000d081008012102c8511f002ea80e4100c034400040003109880145240382e112262100100c011416903c44540100405000c0040d180c0e59020002c3d0b1070032605002c1d004410300c0c5282c084c216020640d070303203051901500100800d2010010644070610350314503080c030035902c41440070b034150b118a80020350140543d83d0084140b14101d4a00c4854200070750b0100f002100000181e1050700903456072414445684404024925258000d041c0c50790284048040d400350b559941001c1540e09101404807030380220420040c950403040e988044000108000d00d000c02d00a26 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 586943003 1250 586941753 586941791
    0x2090a0605071511130801050411040e1513020f03070e0c0708070b090106061107050901090507020102090618042d0e0115142e1407120c020901050301 66
    0x306410054040754000c28414254842c03500700f02e40301030400c62004040c50401040d80500707040c21183c40322900000f284401403040d14803a07500202d83c000d00e00d50042c00c1001425480b84608031034800e00f1003446101995203103442c02190341500d01660303c00c562050024507081c120700f5a02c241c2000200b001031403940d00c031079a8402c0603002a20b50390304162601d103136a8025480c001d006c90040004100ca4020154048000d0755a50f44810200e1241a10a1039030b0360010b01550b9003105030300c001005400300c65088150060402d00000d17060200c01004030380241c101900c04102c180e106184015036003403a118001280c10405c0340b00c1f1b03a055880030b0058030300e0000c1d0001d0007100d640f4011021940c10a5000170000c00140f006407102e00c1e9100310050f10003481c1c240d07840c402c02d0314444912500c0170b1581521551115000c0034440c8180148064800350b5039524a030355114810491800051881002103541d49165128103c0a00386030050251007403050700107034003d80c0f40000c803c0d401401713440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 586944253 1250 586943003 586943009
    0x80a2001050417030d110c1c0f0e041b05040e0702060601051207021203010f050a090c020606010f050d0507080924060607020d050102040e04051506011b03031d0309040605030102090a 80
    0x140c4100d800806200b000c1c0745203c0c09803d694417501d020310300601e4054000c01800c204019100f1a45c107c10381c0804401d0103c0c0710600000400c008855041030540a643e9140c03600500800c00a402d001000c0420300d62001421000c1c000b450020303041c02001100b0a401d5001950342c401032050340f61010010b0041c1c40f9250a40260039005070000345613038801c015807070004940d403803510b40300d581d01c040c402c4172041d090140710300c551140100440c0801c081e104100c0d00d035049600030011600d03000c005603400d070840d0b03280c1400c20008126505190b28a401400c1c016142d43e03990301600d24007407081c581010341080c0300c0d0340c54400c003a102c00000c0c10b501c50340c0394001808549030350b920001440050000c060b0890000c0040d4008240000c40d81c540f4040640324900a80603107010790300d114182c04010608444090105100084e8401e00400d441090400e8a00c203040c0042c0c02c2054040003408154114804031032640001408102070415025040050005800a5040c0000301c1300180c90707940540 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 586945503 1250 586944253 586944269
    0x6070c0f110307031b080a11040b0114130311061e090102010609110c060106080907060309080d02030a0504140d080c03062407030e0d030c0201030b0118080a20010504 73
    0x4880920042510404081d100103044034070950343d92906807040100c203542c502e619400400300050224012480e800d00942c06042e40c1c01805440c402c12004208110441c3c0c10060761003a2414561000002003102d0031110070702d8035116207186408100300b5a4088030a0041509010046103461108880f260307600100302c0c215190449180101d0050110780c2c00012201e0801303c8083d0030011001c02130001b502840180c442030780e00c0d5081038038565130503600c05015a022440801c00188250312980c5554402c0e0440da00d08900058240240e030425941c00241c00d076a58280401c0004035842140441c5032100500709058004c0030207402520000e124944405001002481d59514072040314128030007a0700c440c004041c088480a606c0e045148220042101403030100000e01c0c120a640501603415030318200e682d03006600440c06818180030043c1444400035100b2805102002080041c2c11f2101c0105500c0d00e039800e0164030f000841c8d00c4801211461601100f480e42d004040358281c40580c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 586946753 1250 586945503 586945523
    0x6050711091b040e160906050d1505040504050f010b03120a0c1104020c060703240312030608030c0d170105030c10090e0f07020d02010506031e1c02150906070c 70
    0x2118502441c00011448488a07040004001c40c5944d111038116029109100d402451a0544242035900001500a62000c1070040c0131100905a6036000b00e1000c0c0d05601461400300e03900d00210701520000d135011911504511942c0301611000d200340c408508041f0000d0020411105c0b11000d544115480d8204000030b6030750100a005200001d258007010180c070440d41c40512000d9240c40307103003d070798400c002403c1c110001d008100389a07a1521002c02d0741804079000e8903643d900180c4084600e000300c145520345000007004c0c0414806400c80c80e1101d80640b803041001070005141e070400a1124030101c2c003040c018410394030005102c180f2107405654840403004940401d650b01d201035844102c000086600700300640304400700007405180703a40c0032603041d4802c45174180c0c261882100c20580560010400402c40d42d4248110b010340a0341c103041c2c1d41c00495011041c148030400301408000741c1d00000048110003007081501d5400b00100020700744900b4020300003001c140c0c000101411040740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 586948003 1250 586946753 586946761
    0x150b07050f060408030f1602030a030b03191b1a181c03020a020901051f1b0606080601052103040b030408121806070306050102072112080609010605071109 68
    0x8010039080881c9560885109140610f4a502a54011942d9685100b0b80b0070110307150906100e4581c0300b05216401843c1040000001100140540c603052503041c424280021103000c4113008001c0803078050340340b45205c489190300020b4080125400840540e60100c01e4443c050340201c1582d9426103020215503071140d82c50005024046446540c040c4229048071102c10541c002405c42003552003035882038a0b580e41c580802c080c1d003041200116616440b0321401c00c4030f40c4205000491a242282250220001c60300c580044800c1900440e40c10780c40600103000914201c01c80306481609881048401c040d031040d030300c2d124015845500100f03200800801d00300031016060b1240385030302841c2c1003843d10308105221001680f02074190010302889000c81c400d54464002c84d0155001a0000c0c4111403800d0411003482018240b0001440b568251010005084904102000038290360b1160320341416020400d1520040c2d100201f4070104000c0f4100241848008041d020070031500304c02d031561 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 586949253 1250 586948003 586948013
    0x108030913051308041502010b04051909020111100f0b0f0303070f030302040b03041214270301110f03071413030311100507050a080f13021002070b1c0b0301150b07 72
    0x40c0f10714000d040301030101d400700301d0302030300920b40c91600e41c15030080c8400304d010414041140c0096601c0d2200c0d4030780c06d000d03840030f032815000000011b20601d420b2103d02640f8183c141064a50f04541d04010703103e00320281030844a0103101d903c600202c3e203044243d14408002550380c400c01100070018407944628000785402907054034020a41080e01e05d940b0314017840c01e2400da00c03203030450f940440d10340c14010042e00b68685c103460140903043e01c050a19420101110489000c0c1000700d60b1542d00c0e4118080002c1151000c0c2020780c08484810362607003006c40e80a400c2040e9101506061001030106e07025004c0004507110840e90542070514018081034801ca0800508000f00d890481c2044244541745034000001e210711342c40c59840c0c0e00c1caa107440c000500503940560b055039000070007464400252800816600c602c80726070044440c4240da03103501c12015040f01c140320301c01c10003801c00e0a00c44400e60044240c83c4c2e074214002c0014002851120b06141c2d030600640322044004104401040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 586950503 1250 586949253 586949281
    0x5091b04031b21030315050901210c030302010b0a090903080a0509031207090f3302030d05100906060206161803170c0c0901030f0b060d08031e010803091305 69
    0x40c80c0d55262203c203181d00003001400e14800840001e0302e13101141c0604921104100203541000f00141c207681d1801c0ea50380701003142c0d901c2050030252030782c580c5070001e40700e500d201000718401d40007c561080e81c1001c1048840d070a62080800038104091301c80041e0f805074006601580b81080041c19072241604103145000d036500d40500f606541080c401c061760400c4e01d00044a8030407000c404a1a2580d1522140c0e14084a6054640c034260f04c00310411480c400d01c1868500080c41180c0c02c0c002408108000e45005852040707902165100500001107640501c0002d4006800140918100341c26001010a0000ca503981041440c508249a0780e030f001140400951f00b244410790600e003600c01030340c070035481000d01c81d10a1207410f003902e20300d09010307031414102c0c1d410800c44190b0010340e0700c075020b003079000402040c0d0219043d200f10000410343e402030750089125600002c240e54050300c80c0b080b40b001c1a00454950f5005119050455a030503503c204040050fa034041016122011030311805 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 586951753 1250 586950503 586950509
    0x32c06090a081210260c03010606080a110c0d0f08070305041e21051b0a120e03070e011205070807180915050903070c05090606030f040c05100905091b04031b 69
    0xb9411440445c82c100b0f03000310403281075402d1030003030b94446400107042501300da81c603108071b102203059140001d049074200c0e0f010070078204c03a6040b11407070442c0c250039180c200000403d1310400300b04c0c0d0020200c4083e903c101c10650144590404110030305098561495102000c0c5040c102611500c010300704000419205800c84200940c01c0c01c1054410507020300107821245d084c2c070461802c0c00e820b480d9100d00040d110b0085030000c205040c2000840c00c122000a2004003a6426110744000020318114104826008105080c17400c5041152443d00700d0410446500c01c03042c80c0d0103010148030f08022454940c15821240700c00041e98040e601d001980c04d07140d4001c0000e224a08010020115404001020106d01c140300c64034040c0c0e11a020090a084199201500580c0500004082c6003440522682150280c01c0394500913a070f40300024107a001d20b498070400200b98001c20001030502d02540ea800042e0800c0d08131903124408910411030140b0301c006001103507420010084000031042100107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 586953003 1250 586951753 586951769
    0x1404021f02150901061e030c0e091f0209270a090609050a030806180c0318150c0d0c0539030403030203030115050306010c080a032c06090a081210 64
    0x71072a043e040b075402002e00c1d110742a000d409019960500c3d2044403070070750981e9405801101c40508042540100d41e10050940710f0b54814074140c50040740c41c000940f440001c6224001d80e480191100f400b46a082064800c02c940c0c0d003c0400818000121402540c401170307140000466900c0342c20140050701c49504080d006010309a452028143c3c07024045109803801e0b10900a00c0f050074000c0c905905040f84c1040d041360003072002c90803c02c181030356402d210101c08115590501120101e540c1c03404c040d44c2c400d425110000302a0a500020300a42e1050f141b2070030958207214003402c0000590181d0408a02c900003011141c12100e1720f81000c803e0000103c0f0700712925642c8914029649502c00c3c040c2c0301e00311000004003440b66100d0030031641b090006945142040503a992601226002990b0b440d0074035403600442d0351042140d0100650761980d4038540aa00900701c8051404c0c444050000c0310a40c112106080108050740202c840820b41050314040c20303075648080e10b040c12843c0e003048030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 586954253 1250 586953003 586953043
    0x10504110f071a090d0e062821090203070e0c0403080d090606050a05061903270b06010201021612030902090901050a1b02120d061502101404021f02 65
    0x348801c8800a000c0700303c010f5200103140e103490300115a290280350752035000410392003440009042103005001c01d9420f4030004110340a83d042c803028908189550500060710160341a41504c0790340700c0c14661f005003184108a012000d8000c00c1c0c60342503900611b00c01d03106504c042060b496160003118002c581080c020380d241da80d0840c0304000340441460542e80c25080000c04641442c00c01055822500001d18071864030080282803110101c0f07800f407100c14999036441105688029901d1403034241103079203009401c43c03554a00b000781140d0281480d41168410700c2050308081582429411480e045501e035413030441d0904003200074041048000350031502e081e0a0100d41c00d01508010f00815481c0c0091141508007007103400000c281d40070240050344068214915201041c1c002d0009616882000c52150780328100030301104928890200180d110700301c01920100d80384200003d06646211010860030540c000a0b4055191030508054004082c5c407407400e00d008000404d120102c8110440b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 586955503 1250 586954253 586954267
    0x9110f070302030d110306010f030f1d070f0f0b0702010c1104090b060337050c09010e2509030b090a06150f0501080f01090905030409090503040f140108010504110f 72
    0x30f4490b00800d00115005080049481c0b22610b00c0007a03e00c1464103940f49903012a2120044000d495048010380034a60b442c00701c05892003010120100d4a0a46170040a10700e00d0400160742052035507010303024070f151000090000e006000125402550246030055088580d41003218403501e41c004e9180e03100f40307055600d0b010001c7c031040e81c502c1220201c0039200780041450000d094007800c0740040c1514640f01510140c8507200c80c0256400601440440300880800c00225984c12020b80000d120000e90344100a02c0707020003100c0c2c0c101700700c2507402d0320328000d01c000018050607142d0000804201c19180080d4420324200050390449802c20002d200703480340c445840f50300b80c00502600180345030300800454954010210700340145080084210280c0c40e2035001002006258403c503401c0c081044000303100a220300442048074001e07005165200c2c5050108400c42000d82d0040300040300b81c500818283e0b800c0100141103420a90f804038000c0302c040c03401d40c0310740700e018108440360704081100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 586956753 1250 586955503 586955507
    0x14030411062b06090c021903080901060306050c09030705010c050a0204050a181406100e0f0606190801061e020a0b0702011104060302130905061c022d010206160909110f0703 76
    0x44001c44280480402500c0c4e180d00c2d040ba00d8003408000280341f006003e03c850006441111a103074480201e80000520541341e03510782007074035015513089078400404100401c680c03500340442d41c001e000074200022640c04035900c075601c4020568020788102d64a500107a80143ca80d040312001844a84507290f0413601c91909a04441440c28200882d100d224001f40c030b0241c448500c08180c500d4401080e1199881000114103403400801882c0c00800902069161041c02c00081018079100d855501c86503040c0704000b801e0501c040c81200c0c0810150740400c65a40e00400c45e80c203c550801400c1c1c10681d60b00344143d0240c0032582000900360b60008000552681c56800340c80b514080c080c0c1c0c0140181e5603921748040e035005903030712a17002d008110000a000c802c1c2c030300c40c80d01ca880a81000e41e44690301300c42071100402c102805500400c1000f07580055a03050025a0f0301030700c4803480b0305001c0c0740c3c040014840b03485400b40b009080e941e040c1c101004852603055412040c4000c03403c990303524031742c580 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 586958003 1250 586956753 586956761
    0xa060f0b03040605070e0a050609030c0a0e0f13020603130f0c1e0503031813140a021b01051522051008100c0503041502130305010203010614030411062b 67
    0x1003541c2c3c041c070381000f180320706200e25262400300d84003e03c000e074150b003045c00f0000c0a03400565a280d040c46214540340c1191900840403000f001030700d0708803a851030450707401c8185d0507000341000d80c84402119080c0040c0d4601e020340c2e400c035103100008180c5001c03610300281c00340c042c8040035050b400040c00005140c600d14a40301c6c40442004180380806a0303890a00d5980d0140d15002c0c5c5860240c0c541c1c900c0c080c00d2455601c1d019100b1a83c002c255108100313100d036030740d0380241c40c0c00711a643c00044000440c09a03440110003401c0f513800070012840c242c414541e004c1d242c03d11442c803c030710249400c0483c140625062801c02144003082000e0305110402c0051044036110314411401490501e200d50b84442c030500c0142a916100d4500c0c5a45a40e50030340110102a4103403010f41d804c1c009602210f490390b42c450003643c805c42c0010394a504000000e0320750190a5040908040704008000014045480d00e02e10500143c500981b1143c450100031000c06039240d02d548007030040302170001030740c0081d08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 586959253 1250 586958003 586958011
    0x10608030a020d0801080601090903180b0d050108150c18180402030c03030304030504140604030f26070c170a02060706090b06040e0606010818070308130909021005030a060f0b03 78
    0x22103400d01d095410640740c2c0c480034402d02416801c41f1004019a2916400404940344a841d0003006001da001050070b001009400036000048046000420b50655100e0a40900103070700081c10b0030140d40c00c0910070300400900414564a002c100380b10500c44131035071944100e00041a880012501a00040c240c41c41214240c0c807911407044210400e081c048216405582c150350740f1441e2074207100020f00c21880c1c450070560409010400003000c204122624002c03148502c5400e1a040040001040c2c070316030b040340c141c0800200708990400500b09800c00740484015240c40c414807648680a2400d1001100000c0c2d002000020001300300443c50b440509218404c070070302c10072522004107003c200c41301d0103860b100e142c1c0041c0c003003015980a40030050307001e00d6030140452641240d284003030811000fa401101d00d82008651540f150500848100103444120b50400403d134054000800b064180c40081007030003c008040740c03050b4643d800c801c1c06001d00c207242414890b602d00c01001c855004a03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 586960503 1250 586959253 586959257
    0x5040908070c0b0a02030a0c1a1e06030705010e1201022a0d021b010e1207140405160c0b041406270c1026010e010513050408041a0c010608030a 63
    0x140c0081455480b00041c1c1d801c2c4c4c6216401141010344c003420544205c000340c2019214441c0020403c1c80900f00c010f2078502c90b02c1c00f081c066450403400e01d452070400c14054013140c070940001c0e10034040ba07640302001c0b148210040f039070f10b000c9074100b0500d01c0c0203101e445a01c44210b0b9a0f68110f914441180a4160300170111f041242c0700c60314410b00c00ca81312040c401240c51510000300504240e03601c101e0f080201128020003a00c040003045c07900d94074140072580244d05a0f42480d100d00450b2400b44151ba034843c2e0707459400c00d1104003101c2c004080303080d018801400408818041401d1040c02c80000d8072284050044900310f08003d0b11491143c0d0b9480705d1803c280005040640c4401004100303101000405080d9480481c2401020385080c103c03200e1000c0050b02c1c00000d40c6001c901a0b00080c000c01c400701c1100340650408007440906140340b4086d080765801c00b420b0100060758201150215401a8070161014885001e8150f043c441c1c00c0743c0301080d41c00d02d10301040a031000300040490074055 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 586961753 1250 586960503 586960523
    0x2040f0906030b1014040b041404050c0316030c030305160f030905090718150e041a100810050913050105040b10080d020303130c1d09070603060b07020d06060504090807 74
    0x1381e4400b03400c03d00580160f61694242c000c101e503190410390800075090b8402000030078003503e14148440301041c111400e40751640102e43c9003402d03081c14001d04908054003c8080c4c5620304584446192503020301c03000b81001000070f00520506400c18810900701d6100200600701e0400d418020502d440c54061140300728a00740100706424022809030101d04a807188004002d4500010b58003040410020741060002402040c15a42d40c0d5200d0b45550b6002e030801d00c00c0f0b014000c0c090000198082e031450082c0103003403040c4842d5451000402c5c4c00c03184100d601c000156101c4400113100c1c22240001452036007400141300400a0a0020314407612484c0d01c00c034503441d038500005646412811050f00580c10800204820320148445600e50341c0c09102010b822a43c2c90f05501e030024203000c0d190111000c23581c28481e5001c02440081c0042c00c50b850207004207030920841104d28071035024000d2080e182201060f003045010703003040c0c0003460020f00400c0f0708903a90034050590703801000101c440d800c0d6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 586963003 1250 586961753 586961761
    0x807050c0a050f040c0933050306011b0320010b15041215090804080708060603010501030b060d050a0c1514030c04180207120309030201050603070302031f02040f0906030b 75
    0x80550000e04956000f803162100520318420301004040c0003098004115082d9004201c64031941c0410312200c0000c1602c510380504100301e08100c8540d9980c03442001000c00c2404031680e1300c251040b801100260580d40300c03c0c0903180564540908078480b40217012040711141c0784013819880350b01c0b410402d8804010300c00080c06010520b11641c080c40d00c00e40c4100003030308003040054110342190541c40000007000d000940303402006400643c0030200d544c0c00302c08107010020050010540010080c0d000b40025415551079018170300d801000240507016400707006d030074071008101612596400441d030401c83c03621030f1048002c2260612042c4d021500040d4a20030207020703042104c1c800c100030030000c0c0c00d080c1484031003806900b22114001d401c9401303018040c007081111844150305e070400c0d04d00060040203494080c4c20346500500e001c0c481c1c0c1048070204056100494075603184841c0140d05141c610850680742c000340110381000550350030084c0046520f000990002c0d003524001d029045140d07403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 586964253 1250 586963003 586963009
    0x2d12080702041505150901021603080a200601050103020d0b0907180501020f030a0c150e01020405090606070b0a0b03010e01180308160f0507031403040f060501141c17070807050c 78
    0x3840e00c00d00ba088428200d503441c82c641941c015066540c41441564194102141e04004503549e60f001910b80307180010342007440c0c58000303c412208020440d94507500c00b010080340381c0c9400d014440c0e00d040c0358001405802814803540401000c00c2c0c0284100401d09203520024160202c0041141203600c02003000300301580001510981c180c03038207005519103401800201c4881c1003034901200c01c02110084001031039420f010b0626100c030401c00041e181d80c900070800800c0039026041c54000c0d0020082500415450401151b0156800030081840710358240400d0040275469410b2056510b8001100e8500310231440c0710205ea0f00968600c0043d848441449089500d07114059011910b105042d80b1221700400c0034048450013814040020000041d81c1020b507030048808907200402c418050080215031321a41e40542010801d00c6144456000800c414401d4401585446508105010200400d91011464071501d48091580700c1096152002507500500021541809004150403441c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 586965503 1250 586964253 586964291
    0x70213090515061c1403120f09060106030e100b0a05131b030e0d080901140109020a090b091008040609050f0604060f151e3b012d1208070204 62
    0xe03132080321628410b501c0d960301c1c030f01110f0800b480134850100b800b5100100d495101d14521031895441010311600d88800b049040a034160403e0044c186031011200100f84002004540c16101c043c0000e8200000340c00650308804035400315a1080c0d40b41100c0e018003000350000383d020030986803d030700c80440036007040c2c0640e004040301842c030b50322108801261901c40c543c41900310400c074000013403411111600c40300a1009030040718049400040c040c085a502454200040c00800c4082d400c0c005203c0004800398040b084200410400340007182c00e0000381d0380070881295005040392601600d01040d99150081100d040d00c62524040000c60380c003415000d50301e5501c0b44141c3e070480c06404c0a040045428110488280c048001440450318a06090f003080b071800d1002d00340c03348140c5d82442c001210b81054040081e0000f09001008140c64540100c407254500392040100141000300d0381404038126440402c0101c03080304008144103000e001007902713b00903101402050440070786900c1e33407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 586966753 1250 586965503 586965529
    0x1e09020313020904170403240c020c04021c09030c020909030403050c0d14010504050309040e01020f07060917040306090b06030a0f02100c0c0f1401210207021309051506 74
    0x401000c407010001441d08052495115100310780c030724040704c0043c241c581c50360041d410856402400b005c1c440d01039400e031601c21451101c00241407000b03449d0200c000b9250550700035014025a00031840d04221340300000020110303562004100503c4480307082c010200b007402c80e000d90180c01d00b0300c003040800101000b00c0d000c0c0e94110008182044508042c0003180d02000c8003986d07002840d400e1114070300000c6c00707554001c0b8013a0f0300a50300c0d05400b00821086620740c040d001003d81c41000035160030f0410a054841c4d0710380200b40000d4040395030500144c40000600b40c43d01d182c10003c0e0210402c80558051210a401144103400780e43da40018103554000c001006003000d40b41000c00f0005181804840d2804009464600d004813038554918100c00c0d00b60f04281410200b2840600140d1110150800540e03400d20305444280f100385010344140b04100c007101c1e2403540005588080d9252804103003c0468105c0c01089000407a00b011030305d0300c0c0c0003607040c5401c031100745c0400e529141a030302e81107c0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 586968003 1250 586966753 586966771
    0xc050103063305070b04030801090b0102010209011d060705031c0f050601080406091b06080f06010e1c030512070e0a0b03010b0409021b0a05070f05031c081f1e090203 73
    0x110703480e0403915042040b5440340610070048104001e2000610000c0c006000d0b82c407a0f11069010f5040400490949407982146411a0700c144640c0000ea03134801c1440b9221a2070340030050490340c2080100b00300b881000000b400900c4002440c5101102106da0340260740100202040005003040b006010b0704c2d81501c40ca8001201c00000c80c0c04614154080c3c0311841c03243c2e40d01480c00488030b50700618940c656004e100400d60700d1080102c004405110103500101c01d00e050403182c0040300c0000c2c664401e070380c8203106042d40050308800f0580103000b1221241c2d80c0c0c0060f00700d1032810030002400c21403c401d00a010b114040c0c00001c1a0b485182543d050ba1100031886091508021500d4000d4006001c003001e02c0c16000e00e07691070f00300184032060f1040d008078050a25903042043d50300800c103007980800d01950283da00c1188032400804086005400b0b4035040a0781d131500f0410110b003d4800c10070b1401c0c01000400040e102d144d118055100d2200c0d260020f9805136240a014100d010848032103030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 586969253 1250 586968003 586968059
    0x804150509070815161805040e0a030e040b010503040b09070906030b090d02060105060a0f180906241218050607020f07061107051002070f080a1509050c2101090c05010306 75
    0x117040380140000400190844411100c040d40d4000003000d4075104014080f40ea00500001d005041e480f105803800c80005031006c2c04200c4078200000c09030300c0001c2c00a401c10581d0408108680024030861006000c03082040c0881500c0303081120300481c094a00da01d8034401d00c0c103200a00d500100741c1c2c6040365002840c0c503042500340c15040e00c0c4040068004000c1001c0540f22071002039086103000041c20031a9800035002d17041c000d20043c68000003001d550303945004203017590b00560204202441c43c54661012441e60141c641c11110701000c841c0c000c0850195000300f01940c0d83c005a0784004118010444004a55400054404400784280b420b01500160800e0215081120404400c1e0741548111601940c0d1400040901100b54004c41d507103401c00389208042c08030038207201006082030074040082105a44c1c86960703403008501980d0089162001c584207441c0a80c64561951301c0440092002e80300a02c3c0540843c1980d02400c0d01280c03600740082801d92040468450000010050300 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 586970503 1250 586969253 586969291
    0x606010207060503100b1c111204150e0123010f0f0312051e04030c0b1c0903121a0909340b121e160804150509070815 52
    0x8483d0f42c80104a0708407000c00c05030000c6c0300ca42e080014400d01030604107451012004001010603620758035034615818070227100904400e040807060f19000f42d403200d90803680c511182e008001030000d1100314440d65190003403420983d614000c2c44501803010580300035040e81ca544140e0303642d466074015401003e81c1040240b0004010300480708120016040540c10800b0000c5030503e09d901100d0ba15001e50400b14040040144098219001c2c000008005041500c003800c0c10154600c05168481043c2e00c42d0401010325009281c5607185250700041801042c11904007198844000781c2424014002580002d818060225020403580750303880c554003080400040400914010701e0f10161014802c900024403858128004e000c05100c60080c03180a02e4000034008949034a80280054044090100055900800320b411044020380c141000c49407540d041801e00007607410f03030301c00046140005110504400151502c200c03800030b0102c0d04901e001481c6034501c0fa40c142c1d5030b480d09400c02030f214 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 586971753 1250 586970503 586970507
    0xe041509122304120206090901182d092d0b0105040e0c060a03060503150103140d0e060d0b06030901140a020c07060f0527150f1912090501021209060601020706 70
    0x44da40c6280001d007541e050140440018440150aa010540c8100f241c030011002074a940180d030140400f40344015019261400c50007030300302c4102030745e802c4260b0302d140d2034040003d144140c003c00702100038103a5044065661015550041544c20344a8070001000003580e03140901451140015030ba004d0010f410010703061003520380103c1c182d0000e241d00c4040214658a08019150b0501880c0c0214800d40d4514200100d8441c01605210865000702d04504002d50304480702210301601900d6899030351410050050040650301201644036100009100070743c001500055440e000074452210152617114102d4101c0c0f01d0a441e105060b0403255081103500d008007080426982c4604160345014550390960b086141174194145444c6102d091801d91814206443c0b14407044040340140350850384070781d07001c15002c1c291940d01c03800b000c800c800d903c591080c2001c842070f108000061003003070f1080c0350460103500008038140c1d02d0040c04000a2542200007902402441c042e000341c03c220382002e4007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 586973003 1250 586971753 586971779
    0x70612270305090310050a1407020a0203070302130209191a040f0e070c06050717010501180b0f131805070311031303021c031b08010f0e041509122304 66
    0x43c240c1d06000340c564075000d24010b8001c2910983c0d01060004488103408000540c10030042e023503000319801410b504005850006002065079011030b0080d0700607060088800c042d1040098441e0400340f4a8013852250340712030100000c2c1d48101c041600c0441d203110426089000c2d40c03091001350140003008005041060f15040d81098062802201c0c5042640720301081e541e09075407034400900c81c10f48088040c052025118090802480c14441c10400d44120070400c0300513000d0b20203d040f0020322400950b0900d41240d24501a082101d20555590000301c03c400c00b0900040160310304040005e40c005120f8031030702d180c0c1c155210b156819515500303d010105030150340c04405610401e036102000056207640001c8240013581d0200e4103224401e4440115062b03940c5440620078100700510070003040c0180d0009035800700402a00ea80e895043c81300c0c0700c01e40b128000c0412442c0845000a104100700080c01c1200703e601c13000c6011091094220600ea10311080c082040c2c410b000a020001000034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 586974253 1250 586973003 586973017
    0x50f0c0d0902042d0506060a050a031a030d02060f150d060207020d0c0b271f05040905010303050405121506100e120f1c0c0809060c070612270305 64
    0x10015032031580440c064140000402800907203080e904c0d403480b0103c92402030303079404141518500d04152400d84050705038010902c264084c103440d8910a2a900000001003140d0500181150489404003801039214042582c01e0004001070318002000c01542c0140040f54400140510440d600640c032808000e400102c0200d85c000140a04032012030300c07190901010701803400407a5514054407110300c85070300201ca02c0d5841303540c0026036110f00c0e5507646a2022400303100c18ac5030400c0a584881140c0074803640e004581002e280000200600d03034000090010760f64240c40f100b0344004250700c0ca90307403030001700e082d00e80c00c0542100241e01428025215400c08415007481d906080707150000680000e13240e009054240c0c05a04900c0c0e81c084200541c000da07075044920b5440d400780c84c010081c00d0041d0403c02800c0c0100016462420762203010841e203005a0003c10740d0800341d1105401802c481039801041c50142c14000540e00080000101d10b54800d800c000c50760551915581c2980c0c4c0f600098 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 586975503 1250 586974253 586974259
    0x806070e06070510060314190209040b0402120f100c020a050d18210b01050612070518030a0f020a0f260703050607051c09200a090c0c0501050f0c0d0902 67
    0x1084d00d4520382850281c80c0142d4071480007881d40e080509115031a14603c840e084c0b00b903076200030041c00940c842d4986560020707080349160f5029900c50002c2140c10041464465062084600b00100c8001c08640f03030b0030322512048107028592800d1030481c0e5034108400064000d8004c103100440350ba000d1407000380b201c9040702440041c1551803a0380002c070000200c0860b4980c19540c0341d64104085220f07000d000d090115480781c10000090070f412480d480080a00041c0000020400040348095075105941c140007002c82c0e800e80e0399807400b01c0904040303030f504900441c8800070105040c0c80340b05004080e5886541c1007202c3d291000b082c56660941001000c21301d028096010020030743c1400741511581c0d25844071582d4411103031910006031005800030a649207032091002c00101071144480c0000c15030b00c000c818150f40721001818190290340301d000070304d01d003080340c64500750800d020040b0240918020003507640c5880040e00c0000c000c0f510009803d0b02000084800011540801c035454005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 586976753 1250 586975503 586975513
    0x905120d020301080f0102041214190f0201030f020f070204180602270f0a0b03071418130e060f0a11040e011433070501020a080702070806070e060705 66
    0x19940410540d004a18020035150008010300c2451350421a807030104002c80002c51401e0300e40180310030301d0f240010004000c44007181402c818414100300c0742da040c05c0c240210110070304103803070107000551002030100d0129051241d00d00c0000d08070310a0781d1407522280e0f0744510b0704500350b0802004040c9034000280c880419400b06021503030074030140895103642e9200142c0a014584180c942e01480070b1207501c2008105500d00c1140c50b002c0307406c001c48840c114020384a4a50702010b4400c01844404103400c068086081c4200c6088950f160409050a440080d00303d12544242000d0301d2461307040c20066070004020034003400f85008650343c0928183e400040440420980381e8043e4800d5200c0c074803820403040144400e001102500318a60401c41302c0d02d01d00b420300130300b685080c20307524030030107180321036039004032504180f40c0851313020315803110086507582158007000d0b061f4081601d10200621030000c0216803e00000f030749070f018a540c1d0300c41c4d842c0d021038442080800d922015080f160703401a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 586978003 1250 586976753 586976773
    0x81801060305061006200a0803070e030d2f0d110a21082a0c0f0a0b011a070c030204051510120e070f050409030309020603041b0e0601080a0905 63
    0x6101090040d00f00c2c01c3c5001041d0724201000303000802d10300019102c0082c406504613148000103ca09940c0e5220752510742781c0e80c507500285c80c000181e071185078140c000da904222500d035104414410a0001d5814603540c51201c0c542900c071081011807004183d4090700c0003203a0030b8098480c00d40c1d0960b030300045440e88a21503440c038980c00880684400403510960300060900d8024181a910480011200c2c1500040104100000d00c0c400b101c12043c010000707155a00b000c061122040c4249060104e030560802841d0050000f00300744205620b1100400c11280041035800031a408140c000140c09081820342e02044014030700507122898504189a4408590b10b54140c1d010030001191940c1405207907090104050b60311503c44036034a504074040c103011710400d00d42000141c503002d840001d1010300ca45402e5001b464501c802035403000010040004025440b240000201c1d5150a82c034403845d615001c482101c3c2e800d88503030740412080000a040076516611018543d4000c0d402c55641400b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 586979253 1250 586978003 586978013
    0x80304020d08040807150c0308040308070e041d070f1a0d021e0319020307320325030c080601050d0b0406080a0204050f010f060f020f032b09030818010603 68
    0x84141c0c020050b0750403445e01000716009883d03100d0140b0742242815038002860b50350040c10b800c40200002c0c00c0c803c00f24049001644148026400003001400411440c82c1480c24141c030070406489a424038442c458003c01e03606095242e400844624061961041d88040551a042d4200c00c50b20200f00d41c0c03d21104c0000c0c222440707074102982004050365642d040084100150307a020160000f90380d80100184154613502007030321801440ca1142c001c03c41e128110007012040310b4100c1c0c1c4004820040180002505681000e84c420b03c5c118550f0182c51070461301c1601030320300c10507420001c21801c03000a02c2c9540910300900d2280d291460000304440e4460010701141e80c01c0d000b44002e0350102d01d10008504062103040c0e004441e010302900203600d40b43e40c0b0024680c4501440f810050102c4806c510b00b40200003030710068040c1400c0d20344030049000101501074501058841c44ca0798032045100d24020303480f900d6200b0340c0581e03845000d07548403806018004900215403016661740ca4000010503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 586980503 1250 586979253 586979257
    0x203240f09010b210118020f2206060905030f011a100c02030109150e01050426040f0b09130c1416080414030c100507060f0b03030304141903020703080304020d08 71
    0x140c02000030080d07000c2003c4c1a0340c00c4030001040d41c812161600741402c0942d45860780c4084256044a440158804461002d1104c00c0d12043c42c0154030b00f81000030641382d404c000460180c94054045900b00311700c5c1c164150981c2d4034a0703c55504414035070001c7d40316042414501944c0c66807804d00105804195002c64210350296a05071030103500391034021070700c0c0d5141c0605040c1480e018001c0c0150700b07003525901c46540000034880500a2801800008440f120080c0c8000b01000c0d000f90f0145565600307a9001075014020a40c49600168160038898005104800450350159100140c20061400a41c12640500c2043c0d41c0921512008000600c82c00f00030070140200500c04060401030800389460000e5484c52140305403031003082131a001d0f90081c00e8801140d0800e0b008503c0280700c040b41d000034880f1148440e0035000010400c07091082081c080340c00b100410301212003140303000c8aa16080901038000030010382180204001098000b0050742d00030740014415001070b003c0e035a0340c140c3e40d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 586981753 1250 586980503 586980529
    0x51515190915020124050919110708040602011401031109062404090f021e090a03120309030f0e06070b040c0503062a07030c020909010618090203240f09010b 69
    0x40c1c1d1105d0320210780d0060070440f075014070040c216128820f8108000610003000081981d0640d803041c0c503404202c12619000f2450038121000740582d1041c0c541403400d020380c044c0c01984095030800440c0340410107030317020316130489802c040c0d0b01d04c0001e80d41c1f00b00a00f90f00090422076104926003000b02c0c0b00d042d81680c080c0340501e0801880d503a54034003a019000d170b0340040394592050b0700c14030000c0203440081d4030201141c280a88560f581d9400140055110360300307030300b0150180f450302000b41c21998255014282203406030702d44030296110407500f00e49410301c078039a26400101c02d0000c03030000b58411076560307041032141c0c210414940e2120042841c2c040c0c200c40c4a109000044054145900300e400700041c2d81040c44d6a0520f403e0064402526400035580000d024281c00f4001942800e401e5002c28041d00c4803a0765040d6549407030103080082d11a40400ba03109004515001c40302d2401c407068211405070101c1404911760310340e108240b41020003401520103548484c1142980d640c3c0010008039 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 586983003 1250 586981753 586981757
    0xf020f030409090b0c1305060c0f0a0303021b2d0c040e03281b080d0609291f020f060702070e010509040510020310050a09051515190915 60
    0xc0f51064200407144070800380c100200030004000f101d900421100c000c50507100107840003903540f040e002c095454400c210380e010802c0c3c000d00609408060340358005124044034071042000300c1c01c1e0f4000c001c6e00c0d010318280095001d1194600000c4071103651014a040150170800d442100e2807001c0402d003500c140860440690308001703200d02d12115030103100103075a080c40c03900d0088098488409080d03580d1041248080d5058114170300304000d01103046894080c086030043c8503050307039801e0580190252500f1180410324415802680714100c4100c040038160003804001844c190140010341050f2001e0400c086010b40c007108030841c1c804000440c007441403a0f00900009180014101204006070001c900c10100c03c02444085000003030b1102c07004414000059072034690500c420442c0200e03501036600041c03910400030702071455034030803031144c40c0d80300039510560701c0d820800c0102a004142c004800f0414440c02d40000c00b0b0703004a90303c944180c00c00c1c0300a291070751440b801907800c125035100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 586984253 1250 586983003 586983011
    0x4021824040e0708090f061321030e0106051e06030a110f07050d211505030109030903150c09090f06050d050c011d0607031b08131e0b03070f020f030409 67
    0x343ca65004481036400a142c9014000d0030303464104640c0c440300c0c050440c0300000303c2c601a4406121443d80c01c089102c00038454107412000880c8041c02609590480305117039481d0801c0095036040150208607180389060070b410500d0110000c001c2ea036080600700c080e5244d075032500485408801c10040019a8100583c030f0303260085480e12134600410381103043c0801c0400ca104000c1e2041c6a0000320a08084d0781001c1141000380b0050f5a1160450713014591541c00d14041506050b007000c21201900c0c0030b1003155044541c85403e00301560320403102c0300c0005200c1c10b401c00040880345e03c151811a882c0c80c011035100d07501c40000389200e030303480b20070303100c5400242c80c2040c15a00300c03801c62000700d90b508450b0305e4203120b00e002860030b01030310314094244400800405019484145c0a26215500506483c2c441c1c040240c0c040052030349009601c1c410007222030185600e580b012001049641000c1e2980c5541d5a04c00f0403540b40b241c0c00300f103806511600d0742060782c034142400a0806042c034010001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 586985503 1250 586984253 586984261
    0x1f02030c0702120717030a090302100c1b08010e010b060406210c11010b0a080d0c1b150914060409020c150115090b090901051c050a06060e0604021824040e 68
    0x9102c543e0741c0c4401c501c070381c3c42048040c07d01074000704480c0403660105c40001c0032990740b51080d2254a07a20400a0810103d0081c040285450340c0d660001d40e500e15000b00040014412864221154210b00716440841031004001940c481d941003082030614220802020415202110079038000000410200da407160303808a82c81c9092003500c4112100b150846a400d2070b040c11180c80c0c0624282640800062010000521490089545160f04c8a80c050344006a80d102000c4000941c10380350f0001074420000007444400e8000013000e143d40060400749400e00c1c000c484002540001440d00c80c6000b40c08403551001c1c1b0400015000305684074400b00340781c07040c440040c1000080c0d0040d4444050500c461800c035200d040007241525410780301c0420354440300102c12500c2c9001e4030010b080c3e100304141c07a420049243c0000c1c040340c581d840d0401c5141c030344800300000d9000b0303071402000d8035815061100030743c60300c0c940503140d00725100079035501800e509514081680c13190300604040302c8090180 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 586986753 1250 586985503 586985519
    0x1060803032e03060f0212010b03060307050109082a1207050901062f0c130903031a03100507030b0604060305091002070b0c1c0e0c121f02030c07021207 67
    0x150300701141124203030000218000b020750340840c940805400b05584002d691a81c03680c5604407070903010b1000c00050350f9039441c01c1c400103c1e80105c403032030b01a02600300000707070070f5000f1410700d42500c000750003500f0501080300942e13400c040c417000d80d122000c42c020010740160f180c0004100f1440320031005003c41c0ca0914080c407503003650684c0301008102c1030401811000c60b912040c20f66266555421084105100070340c2c1e45456500c5007803c0d4000c0d201a6038950080041c0e0240244a01c603403014080c4540b200241c00500300d148400c10b401d81c01400d032f4110ba00c0c0042d4000d0782e002007141000220303000350602007410b82d04290402c9011a54074018801c100200b041080543c02e0003100640c64207845548100e49a0409000450284c8020500240b0310740d5500811a085d400003004001042c000200b0319510305100d90064001c40790411149420540403441440e09000c020002e1000c006d0b0504a0300254001004c03a00c0a420074040c440050b40c031103900c0101c4400410080c010700c0d04180b05 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 586988003 1250 586986753 586986781
    0x90c050c0601060503070f0c020301061d040b090a0f0809150c010c0924211802010305130c1a070f030302120717040b041a040b07030c021b060306120106080303 70
    0x40324080c804d00f070003008690303688108040e840030158908034080003010700c0820b000d0400c6030003c0081c3c03040003e810000c51034482c0114485c0740185150146030701d41c071300590b40b2003801540c0500a00c0405903c1c401058060b07000b440c40350000380450044c0526488030965982048440c0c08450f51600c0d25003240e0381c0e100b07541d100602800c0101c10000d0f46208510384854081d0a962400c0c0320300115403400d8001200940e18541a84c550700707214405e80441400840030000c8000c81c0401d00d0000400c0c032015400f904142000c0d405210b0445444c24400002e5080e14a08401d04003200e08200c0c0b0400100e030386152444603482901c016841d250503280c5201002c000070681c40400116210b0b1540c00980700c0c1150b40c115400900e80310140d1658200403c0341284450001c6c40203072500203200030403909010081c03107080159802c201803041004100d0b00c41c00c0c001071003060420300d11500d1a451806000450304407030002e05540c8410b5010a100d03003902c0c407540c4a006103400100810031080c640c01c1e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 586989253 1250 586988003 586988009
    0x31101060f0825080601180e0318060d0f0e010912171f210c23040c03180302161a0307030c0306080f100605030a0203030304140304090c050c0601 64
    0x1e81d40c0c0000d081a4000e40d5469015445900360890070010010b03854001ca00350000c1c00100095401a68580d00c001003220340c01014105114985601d94241c0d510100a42d0341016001301c52100c965016030401111341c000a400111a5548800c00841800b0742d10580c1482136110001003201591070410b041910143c2c02d80320140021008080904071a40c01882c0c5d1020059081031107040701300c5844481e9031059081a0b005001094405600c460200105115688100540300032a5210f414011500d8009082801d900038400000216440c06800400c0185058070340018000000b0a020805d83c0c0f150005401503008580c404024003000c5100b0302c043c103441c0601d011522480e201031001c503c0010158420940e84e606010070251003030b004640104880c00840b40d4950f005503d194071007010383c0008034072501d0803c0000742420017044c1c61406c2c640080203181076594544424a4a072420660804240010040496507124503c2003800c010103d076201505d401c4519041840c1c107806030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 586990503 1250 586989253 586989269
    0x60f1d06060d2d151401050a050f040b06130e0406060b030705030604180804080312090a05070b030a0605062110051f17070e1005131a0c01060303110106 67
    0x10442c00100b100034a00400c545150302007610320102c4000c8088010030722040051044000a05812a0030076540011140510344c8500039480d90741d900030031889075030b02d10071160001c810354600d88880c03900b940001411a80039012a103420200200d40c004400c1d903410100e007420140c3c0c14041448894841c40b40030b4555060641c1c0b440c1084074000d80a404004e020610568882c480741d50000150a0300031023507a44075511603100c9442e1540d040c0c594100b41101e030343c0760407800001043c08000040700b4405641203000b03441607a050106103e0540c1c001801555401c4d02c910000030075840c1c200050211841140c0d00321040b80380e01040c0340100c038024110300f900300034001c42401282d5a508548001351007200138800201007040080c4c0d10f48400088018a000c0b40700100f092a503046102072030720340c2c0f084803004000300701c0200c01c0d0b8203401040a11864074183d080f092010b15000041017013542c1d50f9403581c0742404a543d06840c25911a60412000a21001e0b8540c03040042401068040c1080c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 586991753 1250 586990503 586990519
    0x30207031b060e21030f09030903011a01030e03040302130c210f0b191503090f060902090921070305040b071101030605030a11041d0703030807021605010f0c060f1d0606 74
    0x84d2504918500029144041c00d0358a000400c00d407003000c200303e840082e4041c001b0b1162240304d0080161001480c502c25000c0b80c1403540c48074003036002008032010f9aa00500c0840840020652800140000b00000e01408419152440c9a80c07441d01003000d1040c2109000ca802580004071000741e40c2e41116040c0500c51203100c51542107030314401c2c0416907603c20350351000c08000841c110041c0941c0c80015114038003658040782400203036080b081c0e415000751240405600d80307801c00740c0d4403003550b00569140c915444c00d5200022880d0010501035010307190890925441d03000f600000d038446401203941084444081e150307543c06010b980010401100501040c144603106c60304624043d4001c01d100d581c1d5282021001680c07124102d1481804108840c1e2481e102c0c43c015124607410780b400005846034500144c00f00c0c03555006102903400c11303900c6505189894500b070b1490380d138031842241c61580b5510301e001048004d20410400d1001014040303024003400641131300300035001e40940d020f0014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 586993003 1250 586991753 586991803
    0xc061b090112051f03080c120a0507030c05031c020d0c030b010e011214070c061104062010050705090a08010203010b0403080d0e0d0f0e03060115030207031b060e 71
    0x41c0035060220018103010401d80d80c2c291408400c4c1d44403045991030380486030008028410582d0140441d107013088100c6e003078980341d00000c0d0814000c0111603c0003500822200000921518807082d02c14410400c680c208100c1e078030705000d901301071309204480960110305054885001d004120700e000a074102045002c1200000824070000404103e0511180c148c0f14810710a03680e005400084a040c0200c0450900c004024007901403140195041c600300a1140d510035088c9048500700d45050f2140740720390980f001065180924408200300c85d01500092140b820545d01400d8841d500665603a503440ea0720b81c0c100030a01800d6080803200c1c1e8030510040c403000f410f0f08101c0d001d50342c00c21882904c4021803036040c4080e11454004601a00514400609031508480b615030b8503600c90700d509180500c0d6200385507441c402481180b142c6040d41c1c610550190007503004089141c001d1500d02244500950002c03009100044e0031030b800e90f41e80e40c0b92586498103100140b07d144441100a5010030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 586994253 1250 586993003 586993007
    0x306070509030c011403150d02060706020405010f05040b0405151b0c0a0617010e100f090207020418030f080901321b04051c0f030e030601050301020f0f090103110c061b0901 76
    0x140300700c140d1091140311100c66550980101c01e61527004000301c2d900c100034036018010390403e00c940c0380402e100410a81d06e090003001614140e1b440c614070340f0300b41854030080000d42d0411404c9070355031000c02c0103500b8006210171030900303141e55507400500c500082201800070f4400541e00035420003140f51010140d4442001d90769046480c1454044001e448200702a09040410f40c80705040289035440090100d203150064945603008507000c0006080c0206550030303072003041e00003c2c009401c406481d50035900402200303420070105400051096100c0700b4111100c0c3c00c41d04402c18154010301e0215003c2d18a150940e8007001c0310640c00c240103001828481e460040340101413040415036801304440e202c0e80c49100c2803d42111903600c20307940d2070902400d42a0081e407654000d0158500101c3e190a0500071a541c0c4a046071a080c58031410102e0094550422414a41096101c0c000303016102e100002602ca4491480701070711150416120080504030710200c00b035601030061045080300c6e0f03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 586995503 1250 586994253 586994257
    0x106030201120b0321090303031005030c01030e060703050a0605041401050424060c02040f1a0f01110c01210c11010b04060303080711011e09031b0807200306070509030c0114 76
    0x7007031200350302088601c030951030445d070b014400d039068040c8401b10820498610408040701220802d500340c0c3d10010890b00110162081c6a810b420103500001c0410040c43c8242c2c06140d03c2000c07000c0000b45980c503000000c040d03444440141942c84029001403145142a00c07801811031905030410751194100e03002800b00910611440040c429000041019501d80f1342250a400340801003c0003075042e61180405150143d001d9140075032441c500b00038665001da0005c454101c0b0301c400038010103190900450340d500a5500714840d101c14540c568500040c28056a10400d4960310355541103c0c1c00000c041c00c49070381c901058800d5090000030404260030011064004240307240400654041cdc00750030f03000d4101103407003d1400072800e400001405043c1e000036425442a62605140d800c10515148030046140c006443e4080400141d0300080212480408a50892074107140c50000c0c080000c0c10034400301d5203000810400079a03880c0f289014848144102c030300342060800e01310281d50301d49580c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 586996753 1250 586995503 586995523
    0xb130c0216050a230a030c03110102061009020705070e04030e091612050619080309040f0203220311010609050a0c0305070c12020c0306101508041208060a030803090106030201120b03 80
    0x8038114284c0e001081180446000c04c0c074080c0c080302140f50f603850541e00703220452105645071492080e0180c055840419058007500780541c000d48100e0a01311013800a51003400b00300d80c0d46c480d001000500c071080c40e00b520f1281c2c2c040d446440e45418000c0c1480b58600005100300f101c0c840356031900301c0d4580c100200c440c0710b85401c14005415502c000c04100fa0300c5d01c803664101c1d21060030400183c086000002016481000d842c18404006c00e0301d00344040c0d0000307031980c030b11354030001050411455002d01c05605143c060318141c56003107410001d0f2800c5071404d0b003007101c03540c1e110001c00c6002035041c05511501d6110f403400304040e00c3c1140f401005284108030040c15088040e1081c0c1000f442000074460142e8003c056903110b0501040740301c03004200744150402d26407540c02051580b401081101d1240742c210035503903407454821008940c0601d004146c164050b840850100101d901c10700603512840789030780001801e5095000140c46000290440600c0d60b003820743c0e100650314081011414 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 586998003 1250 586996753 586996769
    0x5130f1b0b070c061805030f0706110309090c03270c04150608040b190e0a1203090b070507081207030e12040b1e04120309061103120c0c010b130c0216050a 68
    0x50040075198030f480c840c2d0346502c0203615201d5190f0300e41d440c0d6230205020044a041e6180e5030848048405902e4481c0038848034182c0c42030f50100001c00c40c0b0146802590f00c001c0f04104010840041802c000080b220f070101d900c00d41e400082c5085c2541001d200341d02000d9150200b22003007a180c480e0041188000403c010400112500400d950081e410135048050b40c1c86481485400400d080580c2e80d818080c2042d24002d1810b007103031507400d000707104055a69070007044002c1c0c25551204141c2d0540d0007050104c071015010000c1c8011182c2d43d1032642c2c001d6460f0360b008a40320500e004182d1038100070845406012604000030008003041c801181e19a2050381c160401101d04141821750500656200350542441980900c081561110f1003500341c034441d480e00c403411480070011130390343c1c0100c4089036200ea05400c0490388410060000d0020070204200108079254180007003420503800b082001c6040762515503150109805104544800303002140414900b40341000140070041240b0544003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 586999253 1250 586998003 586998017
    0x12042604060e010e030706030b0901140306180703051b0907030c080a0b01090e0114090702071401030e0c030f1c1806050f1e1213021305130f1b0b070c06 67
    0x10f640600f500c10f502c032000a06a400c003580d40c1c1d6002e40a402c8100c2c075284966038241c000300e00300040900000e08c40c50050020b007101c0d03490600c140c030f0668582c0740c076091500c2664000070000d58100801c03000d003440c043c483c0c1c00d01d80101302809503005002d40108245404c0001500346158043c52071907014000c0200030501c08407101c01a42c60301560b0300881448060a000410400c880150b40d02028031306031205d440d04c0d580c01e00202d84618040c051f0300c005054245c0030600943c840d402242c0c0000801c41581c448004c480b00107032070b01040c0200c11300346400034401021818800c40c000c41c0c090a550508070f040d50b09030302c00c041c0c0c1c0101c00c1c0034000c1404030104240580f014540261071007005602d003926074032420001803401ca134120079040102030941d00002603280c42e04191036440c165019101e4001031422815910103864010041903044496003a40e0012450042c00a18081d015414207801800c43c41c0c0b040050084a402c04121200d0402110002441c1c00c2c034018121005854040c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 587000503 1250 586999253 586999277
    0x40803100e09010b03161d06060d18020a05031203010510050c071e120f23100204030c1202030607030c091a0d0b0405062101020d021204260406 63
    0x5150040d880e04400c540c51600c1040000d1100154081100402c08400321828080e501c03c00700d41200740ca000b015525251000d1420035504c0c84402240c003c40c0007490b00d82070540d00b02c1100122801610102310018520410350f0560070310701201009010254060191a500320021814901c4103100d40c0340140550968880754911600c21b591075068000195248503980c3c49140c903a4a02d070f8402d1004100c0d0103040080c000e032000c13104d50030903548242500035207051394035a0050000300b420841d900041c4a00c4040042000b803299214403c00a880140c545003142441c0050f00c00c940c101c81410702d22a820034002d40d40001c4c0c00e41e441640e81c81e0200300701c5041c29084900c015a680315024060038581e8080080c2c0c0750300054030540040308020012190010104400d50390280e0310a50000000301001490705030004140300104103840000d0710b0a080899400200c0e1f019009100c0c081c1d2218040c0010003940e4003c0f0b5400e204c089080f051901d20700700303418845200720700c5885c051101c441070712 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 587001753 1250 587000503 587000521
    0x11107140309120307060f0c080604231e0c0a020c190506031015030b06040504020d09140105042f09071229060c07091107050102070c2309040803 64
    0x12a11100083c0c09501041c070042d103c982d0307a40240d141121090b0400d14810850300e090320442c5a0040e0a554070480d944960701440700920a40241041f034449a060107206229210700b84d40c0640159a9984aa503511300c0055150400c00707050b18440c40000c1044045241d400254040c01e8003048a585031803120b0105500041c98180c0c2c80b40d42c001e5004410454241c280c00d6040040304c043c2d201d0031034851081030381103003243c44c50911568042004d00c000d0003a4241940901179800311100c1c009958102d5849a0f03150340c00314a804252a03444804010422122a011008224039212883e0700412002c043c5008200c00500c0a40241c880d90002034001e03104480d502d00310000707044100f01e040300d42440844d52100b40f006030241c00c0c00a901c803085500389241252061907046001d484e08038101503000340a0201080c03c01c0241c4828049000030480070302c024021607211303014a01440303140030362592211040643e4114007035128404a4040d8880342d01a9501030751050380950b40f41c0c0c0d54540e07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 587003003 1250 587001753 587001757
    0x4030e030a15052205060a05090309090a0f0c05030f0a050c070b070306030203060106020a0b2a040b0405010206150f090a021303050615030d14030408070b0405010b01030b030111071403 81
    0x7038416522075110320300020843c1c1c8194020614551810260f961058041c2e049041c5180d0040c5140c1c003040005100c0c100d01d50205400c442054281c0349454548000140d00f00c00030359008518581d103003c0d24505401c1840380180040782420490f080d8a4501010a88460000d0a00d680c10b5240c0d800516a00300b200c003281c42055002c000d0b01404d00301401e00034024001404102d0282c030886002140403400080c1190340d80764130400d0540707590b50300e4508160340c00e11102d4146264003250340f907050f07624283d0041d0028200a00181d46c071203140074002480c1c01c50241400d510038481100303022041c1c0340c01c11402c10004043d030340701300d10382c42d80c2c041100280310306c84420351208400c0401000b0403070b002c501c0b03501540a01ca2600c00c0345203024105030f1901104a804004aa5095021000000c00317030301841d4068091648107080013195103442920031001c070340032038180e5034550703c0f04455a014803e5400200c2c003a4020040c0380709003101d100652048000162000c42c1410300c8411040c01002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 587004253 1250 587003003 587003023
    0x7080712080906093c070602030c12070c0b090f1c1103030c2a21190b0613060f03060501170307020a050d150e03031909020904030e03 59
    0x802048808086500030500700342030b80e03100e41c00e0003184007050050704002140302510390400496501c01110103404103041d124030000080c1814800075000c0300c00b1090085c132000742134a4000d03641e10381c0c191a0040c24241003c1d00300c40820b13000d01c1b6140c0403501c12010a401c0c0c0b10f101d140d0075a44c46104c1d0000796185803030303a400c0381d00420500b44075602e15048440c0310718161040f00450a017519030740c2015102c0c012242c4035480da900100206031035148103083c00403007064000000c22004040d40c045400c2540400c00254100c95036400e0704030b51003040100c1040500400024000c0b50000d5030742042b101c502a090500c181c40722070009091203042d900010003441c03400e0070703114140d68a181000141c042482440c4840c0301c0801203084000d03000c0111f039241c40d4000c180e07254071800c007002c002010601c804c0a171403445000510f002a10f80500c200200150a1070055860f0300e04401900004464004405181803c000b0f002e00161180501580c00a0303244c10400300780781c2c1d0680402c0c60246145 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 587005503 1250 587004253 587004263
    0xf0f0d080a0b0a0b040503010e061308131703070212030a0c0b06010509030714090609010e0103030516080a0206090d0c0312020d090506010b0901091502030a120e12120f0702060408070807 82
    0xf040040d800c1c0502d4000c10842c0c00035402441a250b0b2010620b440c3d440440300c68400342003c10300701e0002201030000304240c03081c500c03140140588807020000c001108520110143d07000184807011340c40c000c0880700c40005120015403030031400306030080100d15200f40c0100100b101101040307042e07001c0c009a51030000d01500300d0700190b40e0340581c0c8130300102c5404028050b80d4040003049684c01c05080c49410390348142c101030032607440e542d01244d1640c441c1e02c1d60290242140c0c100310000b1003403002405218241d60080003582040310b0600d00384000103001d0300520046200220000e5082460b1041e007642c803a40050700c0c1c04100001c1000740441c48401002c501402c0004250f9001110261103121002ea850042e0140c540c0d0f0045a01d40011543e100960300c10306c1010714030b078401e040b80610401204004100013044a01082c039141000320903a41c0c100021070500500d105910000b0342c45029400407411a0800590117501d0703420250015003140f10018810062048000031108016400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 587006753 1250 587005503 587005519
    0xb0406051201090b07020a0c230603041a151008041b0303050c01060b04061e140307020d08060402210432010c0201050c091e03030406110f0f0d080a0b 66
    0x101081d4024695a001140c0c15190322002c50718262000400b010116400b4007040d0129041c500320880ba00c0b032261122001205c001c052680d25112712010314059441030b50600a40e000159510709030213002440440329031810b4031216025603c0700084945120142040c40581e00c443c101081d40d40104251450b05013000c080000c00c15038050002d00e0850342c508001c011541d103034120500d0f0392040c0e1007804001100c03040b41c81a41551034000400701c504074140080340e42040c82d080200c68104840c4130001d608141900403005401c01c0701e199000c84210780441c504151010001c0818140700721007420b60540d00005070400c0000701600340010050250103042400069010341d041c04001d00034403003075003002d5100380480d005014440c0940381114a15052907005000d003ca03078268207440c041c840c804000c941000751401d00050029044c50b580d9504900e101026071840c11416105002d1241d0041c071032071075071460106600712082c589103402c400c42c0c2c03510580d8202600405001d1075101c120 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 587008003 1250 587006753 587006779
    0x507020402130f0e070801060503130f150c03060302150903120711120a03020c10052203060e030c070504020d0905011401050405010b09150d0e03030f04020a120809040b040605 77
    0x85074076400301c81da064034034403030f60b500c8181100031a041a60b00724041600600140121401440a958050701c00400406002e010391107200d015030550000391940103030000300c2e4035698254007901440c1089030030701f0b20280c0e180d54041004600e4a0010740600d000115200200d682c0501c1601d00c00340e880025162510102d0030600000f111952040c0d21030300715030f140c1e45a80c0b000851040c0010b9010380142048590010900281e07240311342e500410400304102200405000e0b003150b080040300d890030900300c542035143c18000c41e0783c512961031a59105000d07145466000056a009407402a00c0240e1518009403e010183c90001001030040d401d10791801038413940003d40c2c03412500110b80500099a845441c901ca1f480b17110a100c1c0c10801040c100051040038030700402c101001520001000b100016000341160401d503200085043c11200f48000d502d00310310b0003030103444806418030404407541c0d02c4000c50311955903054000c0744c9413500034802c2d6840354040402800007405456607203079 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 587009253 1250 587008003 587008027
    0xf0c03041d090c1c030e12030a080a0506030712030c1e03020a120f090605070203070f0608150406060e130f1d060a0b06121f060908251202010507020402 67
    0x5040742c40c2d031014401c4104007070803490900c0d4000c8200741c034481139038102200ca4034111a080d0130014420340003518a06c40c1d80f062541040146102da146c2d55903014181454540310082e110041c080c288690300080081c801c10081090704402e0700d030316040091441c184e601d4002007000310000000360341b50701e01d040c4109140d00404d129000b5449454102860441114169105402d503084480014103942052019501400041a101d0300003002c030b90280e640d5180310f0002c074070760307401c194001140f2805128808901c0101c8501038a02254180405810640c00030020010160464400c103440246184081102e50245c006400001006d1141400560640809050f1010341145501c20000062580c580d50711901d0602c0c40c0060040d441c01541c43c580c0100244080d2111142440b05401c07a1401c940350030340310700106015100d0300c008a00d040c0d0945e0400c0360055290124041c10103a490141018400c0481500c08041c41c3d5160030040e400100c40c03c0c0a1030100a4205200281e5092190 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 587010503 1250 587009253 587009309
    0x180907090603110f0117060f04110d060e0c0304120c14060901020406090503060405070302010507031106162a03050a0306031a09010b01021c0c0618060e060112080f0c0304 75
    0x50800c4c0d0364222440050720044a02e441c0b0100a00a40401c0c800410710324600707112010850344000b8004030744c95440403520015688040c604960340340d41e0320010040381c12544c0c01c0550051a0107101030a610303094540c00607842d00c0800220030001460202010481181c2e0310075200752151084449510f40440c443d4003c1d8018080c102c003150b60303e000000c1d9403400155052245501c140940f1039185903030700541c1c8035041003c040301402043c4880040c508000c1148920907242c80d1034500032583d02000241a5000e802c1e81c0402d400292a0403d020140b0030b00300076a42a45841d02503903801d00c4440440041c182600018108032588103480110b410b195180c2d401615440002c224050f240c100682c0c0c0e03503819040014810b002e82c0b4040e0304103402560b140504600030708010a4101c64040340d100040030085003265999907581418803603000c20411603002d800501c1c5804000078581d194108540142102210203400010304104101414002e840041c42c1107076210101703d0000c01555221 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 587011753 1250 587010503 587010533
    0x621150c0f22120804030605040222050103061b081503011b020601051206040209010e060d0c032a0605120c120c0406021b090609090f06090d0201051005180907090603 73
    0x4080b80c00300420070a4803141002d01142d07000038060b01d0289160795480243c60000d00581c4e220114841803500403111030341c00401400e4428000540e581145010021100344c3c120000d21100b03840d08112146800404140d0803100360040e10192920b0000041d01403c6012910ba248155040c500103000d600080c80f14140c0c1c2048619024188854120f5542d5441c1117401a5122844000400c203078140c4420541e0400f8014100b441484040e88a64407d100c0c1c40e481141d03444540892092000751040600807003059000600c48401e19102000b4054040d034060101300190b131f2004070700b004412500715035060300c606a00000c41d04c1c2100c0000740da03402500c120030140c00b481092141a20401d21031a0b07035050004c1911a5507145c41e42485a512001021014a44114603051512980c100070503441507a00e00000e00c01c0070f820f40d200a0035240050a10561011001d000b03203d990340744e041031403010424401c044d0b0780340e89105607070745030a060341d000c0c078030180c50800040240710421b0f090400f1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 587013003 1250 587011753 587011807
    0x30c1e0504180618030e042f0d0207032c090106030b18010e010609092c0a1505010801060611030a030c0c14061503060601140904060317030621150c0f 66
    0x544242c1d000780820780f01c2186001d810740020030188801080881158103080e84640c0c80780d410100400c112740d003260b01a080541c08a0420801340040c0b5182407143d0b502030710b035041d140c00b084440601184128206008040030700d0740301c0d416041c454854180c2c40447c00c030f0071b0a026040b541d603600e854911907402c2c0182400500e0103171020503540440d0003010300c403401e40341500d40846582c5a0f4605120004e91195240340984c04070304010070007003444c144407524030142c0013490394540f0b00001e0844045030711404c280854805120a00d44e03001c0292541400103040200d00303251030040c115140d41d20407500800040c817480d55100031079030000b0480e202e409074030803611a02d01c0340420190380e03150868803180040d04181c0c00310540300c05000640303403c1c1005440440d40d103444e950343c0712050303060f14418084908003008224a0b0302e010404a4003818a5241c030340c1510480f00d03106170712200200c40c001d01400039040800d40c2a481141214000030000c2c041365192403499410f0781d2891040201499 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 587014253 1250 587013003 587013017
    0x120011503021c1110030207080c071502011104120c0b0c0d0909060b0a030f0608010f09020a0603090b13030909050a02090a172503020a0609030c1e050418061803 71
    0x2210300c110b040078459542d081040d20b01a6030513242040000e5510000741c0c01003640038041800010500c4010b41141103d80f03000d801030506041c40005c0020326030301c903030045a0501c441951001c0c610004c45065401410060239101c607181000c12800c10340e544110040f010014580c03024500108048001900d03956031241e0165a0b12aa182555402e00804020135810445540124001e43c0a0400c054121801007070142c0c4d01c1c0f1641d401c5400c403425008046072124888003c41c130301070031484050102810200020801915801c4d84000020001820005e030707568180241070040180c4030003804103d40030b024070b190144008001c1d41003040c01030b001e00d00007880411007410860b601c040020b0b998004040041d0485a287d80d40443c8401d9400012a041404405030b203d444900010b0440c0d030301c510a08910354506000a014981e100c0800f40001070b0342d92180c84402c14100044490459021400703ca950360914454891140700070420707443c240f04104080d40390144019142d0007074481407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 587015503 1250 587014253 587014279
    0x60910020601171501090e1510052403041502070203010914010c0c050303190b060c0607020607020c010207062106090b120111030a1112090105101d06012001150302 72
    0x6a07204400070f5a45514a88400140306440c2168050035107484030740120b511102c1041c080440c3c00d5400e55914405032009c2c4014003460500139110840051940842040b503103514085101902010700b0007041c1283c2d00942c0c0c0c00c08040c0d43c060780d5101e40c00034000c11006180c0e01e400302040c06100111a680d500f407882010405000381000d0440710b4204001e5440c550350301c50f200d2203900108605c114542d075980354154050310340401501c0e400068000810950030074034400307440d118004142108651001c00340d03002c0399a0100304a4212180307410040e0440001a0b43c076404060344185017440245406030028043da856003111418120a481098041940051560036195280280040110100040350450b0b019500030f41800e43c502c00850b042c091890181c90703401800b07490004050b9121406e00160710041a0000001d080303000904003403424040b80c1148842c4020152410300c02d41601110304000c000003040d61606080340204000315603080e0407020722120b03010903401440c1e91341d026 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 587016753 1250 587015503 587015549
    0xf0c06030c031b0e0105030604020c060109051e0c041e23010810060c080306010309051204050108010b040612050601090513020d0c0503010e0c16021c150606091202060910020601 78
    0x142000b40350f1380d42c0c0315141c03895400545059001a1003160015403c0040000586050102c2ca0103400c2410010a0b5410f206015003010304c40c03070600482c100301040900030031f00003a41c100c3e021240180c4841400080c046100c10007544298400500040eaa80000e01000203c2c0465140c4d00e0098890312105d8542c0c2d04040204030071405011701180750b1216200102e041c440c09964040c005240101e0000034a540b00b030300b4202425480c0700c280300b000c00d0a201640e0441101c0303016202002c0c0c03150a061610500920311a1781411740e40b0403541c2c41004c51602e901c134070409005440c4c0036181c01625030720205020001d41c00310080c800294604400d02c0341d850700ca40e0407241201c041180310b44103511303491441d404170f80c8525004801040d00d1402e0301c00503183c4412424034126a40e96640c60791285082c02070450601503094480c1c02d140440074014140c100c0c2c0704009840c440034141c0d25900880c4040307421751045a4046610902416006248644c0091058141e94510031404002c0c2440044 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 587018003 1250 587016753 587016791
    0x6040c0203041a0f0c070b0309060702060c070209090106080f03040e0f15060d0b19060809161203090305060907170313030803070e04050a0f0c090812070f0c06030c03 73
    0x52070407002c3c2d450400e120300c01c80c120040c103080110507910b07519285d004491140740010a51200381d0607900801080315403003080c01003592222050010388036900d80207004030518818460300078480e00c00a008a080808254000400341c69500c0885038103881030810240d0f280c04c184110f1800c80c3c503450001c6d0100c0b08641d01c3d01e0040340380c40c0e800c060b2071080c001080340c640c100d08032000c1c407643d07200c0007061156940e1100042d60000d04000d190520b0901400602c4040000c0000c6801c3e8840500f8200880ca032041102c00c0318078082600010310780030302d006c0710000340b035038000340c0ba0388502c4c028482030520204000c0125050074958640760078080008039107900401d6400f010344032282e802000886c5202d0003d5500c800345140840303c040b0390350300040403544240e07091141c286d80d0342d0050000e868140f1903404000389501741224180e140c502c1c0e035907403803804403c14214080041248820003c03500b020540c015440f42c4034000035a2103500090007803151510210009082044800d108001c1400e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 587019253 1250 587018003 587018009
    0x130609240e242d0709030c3305070609051e0715050a1b150f020702060d020a0309020909010e070933050d0501140a05010e131e0b06040c020304 63
    0xe8080e6502c4410f442c1c003c40094202215000b1283c140c807542480800c0300611401154541c501640c0c25401c080048184c0c54110f154005100030f02c20501248100320324521078048401136044080c20b200403605806880c800801c0b980c2044440c0e020800d000c52840241c140b9419409494107400c035111390b4030481071140d45840103410004d807181600c500010704138140c1d542170480708003109070203880c01d51301c000005586030000c200d60f004079414180200e012440300c8440650500c1c82c99000110141315200140092960019521062901a400848600e81c00400c1070005203000300d03525020b4103034005034040c02e000b00074000c1501843c5200301c030828412401c00c200c41e0304805141d04500c12032402001e01842c0c600c040007410390355612222215911070000403600b15000203030045403072000381003004880d0400c00103028884114800741e6200942100c080740004081c1402c40b40d0704481510340c6040c0717000c441c14000340007900400600584095908000c0b07052084030480c2c4a0140740 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 587020503 1250 587019253 587019313
    0x60302030c0406150f09150c0b0c0c0c010c0204090c0f060e01030507090e0403020f1f0e0a0b13060b03030403030306050f040c090605090604080304270203130609240e 73
    0x80391084035032003201c117890702d840700d03050070440340da20f0382120f680743c868803002400001d400c0d00380744040015030050990403400b2000f00d141444200047c4940b91040500320a041003202c40c1e1540540d9201c4c0c02c959220364006002101054440320301c1003450400340165130100e894101c03506119403103071183c40d1190305181d640850250520f1681e1180c848054400d40440c42584421100400148141e2640380c03e100340d40201c00c00c1c900c03030500556040f08034002c200e0700310716281c2000c01d220000e4554400c2010340000f14885a81c9000001421400f0210341c02d403102060110070590558405415503400300c50441c070841d42d01040005598101a0410008110010402009014002506480c1d8000700310905040c0c5415065145410035400f0591018602140422003819080280310303982d071030801903140d450207186444a1402039480284121355072079445e014000d48151240e000c581c042000702007440c00d2a100340c0600300f047e116482c1c030300450920620100105010409902d221 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 587021753 1250 587020503 587020529
    0x8060417030720010c09050a0b0a0f050409060305030a0e040228030221060a05120330070c0b0a0903020c04050402010c17032a0d0905100f060302030c0406 68
    0x5409444090741000d00001d0610410745886003038440c84000c61291010050300001e004002e81070002d00309102640481d000b014408801e0000ba00c096013203403400d80c2541440c04401c00010b000300c0d070520880d40218403081c6044401702c20004044002d002d0b840c401d80d11a0900460501003008a1040841d08000703450998441101190030011002c031030700c002d060060500301d00e428013007100040741c00d051910040306001c02000d490f08084010140005460110100800030440d540d07070304c2180d590710360501e0f003000e602101d031340c0914201e000c00b124040c00d81014103001e4000b0b02400181141150100b82010005000c00d045100b1030300701350307003550041045030b69100511009040140041c1d04000f00042c107040460038807020300e1008200070708007030f07aa458400c8c0c59000410b0b04034015040c500c1101380903c41d400f026404e0342c507101620722000a00e010b0301e190203441c00c0c080415003010719040c040c400b503087d21540d1141084030300036801d50392401b20400800c802c6502a010f4801c540c1e0346 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 587023003 1250 587021753 587021783
    0x2120109230307030c030e0d15110a0219151a0102010f1a0906060c0601030803040b22080c010905010606030f060b0403120c0f0609062703050901050c16080d0207080604 74
    0x301c5d0304000760450080c2400c9102c80f02c02c0c2d0100d405445003550543c1c24502d000301840741020644503200d0072603559003504e42000c0349020020344664260880d00358601c3c030316a82d1014040200414040801801d000300100e10200c1e1188a03da00301c5102c140c0554648256030640f0b013a01d01546003058001e00036006a000e4540421001034005008140c0110052160341c0070040d0400c44540a1402446910344070300c3c0624000052680040040c02009062031110f80914102d5000070082e03984a1100350f00c031002c204d450390041c03091440c00b614540c00d10400042d50394140d404078480041524050017116114840611603129503c4014903452694407400c80541c0700700c0200000a1054070344001c150b0042d122581500d0718260141c519607600c145c1400324121510482c1003028081000440419042d2000ba00b90b0161020031410700c4030019416203c468180b11880700410f01402400ea056210710400740d40d18151030000d40548280140400d4803200054007034883d03035009003e4503c0e844 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 587024253 1250 587023003 587023007
    0xb0d03080105010f0804020918030d060f26060103080c0102090307090b1201020c10020f13030c0e0906070f0f26090633060906030f0f1b030c13030212010923030703 72
    0x50049c01e038450501003405088036860071801540c0007400141c10b10408141440c10400181711040703211702004001200422005d82c01140c0181120f0f01705c04100c0c0c1720320440413110701910070300c400903074036020f0b6001c0410114580d07803040300c03212415500c2c00c83c618021240e41c1e0813413280558024696002c000c0d814110000f64000b03014041d8040415410803000140181c015805900122008403d100092200c8803007942c1c6554031920b0000201980e00300854060a4000359001d41c008000002d110001868001c06002014958803031510705001e00220741d01803410015204803a0500410020134480c0e0f12421411407806041c2c2a4846401a850f54404d080c0729503080c0c140d00403105120010a40d6104809107100d0352031410584403503d00f0500096030080d00900e84c4581e8074a2507500440e0034980004d032507222070840c2c56590f40380c0311a0340364118895070b944000c0d80901c10041d0009006010341003084080c2c4508000c038841218850403005c0008a0402d50380c996100b4042800405c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 587025503 1250 587024253 587024281
    0x30c020f15070303020d0c0504031a070e060a020601031a161112030906040323071e0b0103081206030a0b04080a0311030a0e072c0a0b0d03080105010f08040209 70
    0x2100c014004a00c0d034102140340400341e00411025400f10f0340c04210a00610102e000d5240c074040e541c54054078042c00c40d5038140941c2810f84441c01c074488100d00160b01035020b00c007d0b840c10040200020349413030700f16000942d0358009001c11580100500d0003030b10034048501c1700502604094400111040200804550180203c17030310340c031140725121031440450301500085001c0c8030201c003c0c02d0549040e0501400141030a0b04000c2000e0101000722410480d40041d12080d9901550459108030921441e036070010b040c2d600a41055a03440000081040620040c400100c0102601e403c03555030341d0800d900c0b20741d00d401c043e06641c450000900080c2c0e1040040254120500300015076040c1401080b513030390022980342481d10355031201010504802c000d800002c0070708d007070415040c80c90310305441518180c0790a248030252410303011422403401c43d048258105005050080404420f0074004e01d142000c0c424a400302d40b402c023041d0465403140080512564010f441d03e201510341c8000640d0803 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 587026753 1250 587025503 587025529
    0x6060b21040510470d080702040c0203030712090f0b06030118080a0207080118020f060705190b0106020f0a0201050c0a0b0f0a0c08100b09060405210106060c030c02 72
    0x58055400409140c2c00c0038461300c04007414003841d100880b00b03c00c418140203c03ea2000d1a00074007250340b4140100c4030143c0745400c164083e80e0200d0210300700d242200050141f003100a40c403e00b482c000c0340500c3c2d4000040e501c51000e6554880b07450500d804140e046404075900a040030705990300200200b801200c6840c0c100c0f40203000050040e00c050080200c0c240007010417219640000f400d48800ca41c1000103101901d0210001c109200c070b100d0501101c4c12410000074003540c405c9080080d541c0d10b40301034441c1103070040144c440601c8101031828502400080442c0d00807101c400100d20700e8130001e46049069800310007012800120b8005540d250404007800c001441000d104c1da00041030030400d64003501d140158403065052490041c0141d80120401004101c02001000f00141d10844100304440c04202c1055a410040c0d010500c20b11840d04026003003e070a40c0e0010032001000203010301d8040c06402080656101ca40884200e240180050000b50003403540c1009441c10001444a03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 587028003 1250 587026753 587026763
    0xb03150109090c090603230115090b03010f030c0b1c050903090a06170a110f071a04080c0105091f1e0504120306060c150506010216090906060b2104 65
    0xc0c69642c0c0c1d03802064825010158001400c0c0340801c009498150084400d9103650303004000ca1a03c00c14044051008140304502d440c440c0041d20315100341c0510103150141002043c8166a5030b1103048161154a59200440b400910150002071114269060b51204d1014201c4ca89840700504003140240801401201813030204208030b0340580d440d0504500200030365141c0000d00910700c0d85200d0080d00c001e1400100c0b03800c244404011580751f00440d00c10f080304c0701d06151940014100319450b0401d040030704000a802006010500c2103000182107480b144000a1100740d99504c0700b01e8a0340b50250365192620f98040f01a0400c9105030400b0b81180709252820881c200048182000e564040c0c070b05032080340420301500c03000d80d40341c0580005040d9504000103200300680c0da200f81c100f0000001d0403543e03611004600c4036031090103050034107050341210007401a2910307240d9000307003e6810f040b80c0c40d070b10b02400025000c03912070030b46107003000030240e0030701d184104603c10503d190000c1c802c6176 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 587029253 1250 587028003 587028017
    0x20a0801050106020705040f02040b09010807020109062d060b1c02070203060c190503010503190f0c030308071205190504020310020f04090b0f1f0c080f0c0c06040b031501 75
    0x5a18282440303428000c0c0515801002042d06e0502400b04480c02920400140750040005001c02c500b6841180d21144003860301806c160356020049004000540b802000c4600380001401c0e1560790f2a5460606421329041603406807520000c40c1c201d443c24070401c86070500c18007802600c182084042610045415405894460550b001074103108003240c00c04556000440c00c0012000200d40d80120500310741040c41c510f50401d000282c0e5030030070003031017501e0348800e02d405801c00420102010060350311200000240d51a4600500b4081c4122407101c002400e54007100c885190b075020b42801419034080719080b09400400280240c040100203070b82511604038881d5a40d03580b4401003c030102c482c01c4d1141c0341c42c00c040000c410f42d150782d92a10310807080542242a241c2d50108215900d070900144941c0d24103181d04140c5040001d454081d10001c0d0114401000b20402c1c0c0007400040441401e4454071507169040040e43e005500803000d003900e061000030030303c002890350f20b1194041414103a03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 587030503 1250 587029253 587029259
    0x2061518041e050106080f070803030408030103020411041221020d08010512030c07080c1507031b0c120b15010203040b0406050319110703020c09010810050a0209040518120304030f0c020a 82
    0x5130035504190320043d01c582c854881c0024a501c10b014207005845264059071940c20603880b010f51310f01043c04003034800c80c1e41d04010325001044000321001050a0126011a02c3c2c250401c601b0500403542d0f11000e0200000b042da41c100d10102e14804c0424903600c1e802c40e903074209004c1c00030781c401000008170a0f200402c6011650601004801d00511540d0000d19400e0300440a00400301c003111851140410244140000a078100a01c00c2250006949030042d18040c1e041000382c440c042e612901b2a800d02031500707c144015a040e0034030480005200c5202c1d08020001284e4900c00e5219400c60409c0600c0203001042c840d400071600007a0f1001680846015026500300b07d031800c60400b9481980000d04004064050105a0b40f40c40126440002c40d80343c21032242c6c64030480441000310300d55075000120189065810f0711003160780503104100c58a0b010180802105c440c506801c0c00e4801c92151056201c3d280d4120b81c070856069581c001744420286064032003024241c000c0384d202059038404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 587031753 1250 587030503 587030513
    0x602070c0e040302010e010c05031f051e040e0a11060c0c220b040506060d09060204170d090e0403120b130f0606030b03030c12070212070602061518041e 67
    0x41030291a00da801258a07041c0303031901a084801c0f80520601590400216242050300441a03079030109113218461055001c8042d240b141c1d58150700242d61090003404031041003c21010304900040701500e04100e0f05066111056842c072061500a00d003400e80c0c807401c4c10354100800900078600c03c403800c41d02040309440c0018103401c83d201041d0101038055001508401d803d0090114090f400d540030442410320901185252040c5140a810551a0b041e054100003050f4100c4006201d06150140708490941c8620b480f540a8040074000641748480400d2420850310305c54011541a1a03000682450340c00150240c0107411a982d407040d10741d556125550000c0c005c0504c040c00000c070004566003000d0303026003143c2410065500951007803100145076100050f540f07000c00b40b21040c00751100304610026501003c02c40502445010b0301000007201500050514000ca200d04c1e80041500041000e2141c200004d241010b8200240e602190100b800e0303000240d00e180c01055141e19000e419202c2d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 587033003 1250 587031753 587031773
    0x3140c0a0b04020f1e101206080f010c2a06060315050406110c100506040603050a030e031504051c180602071e03150b130608010209040f02190309060207 67
    0x65612003190301c1008114a00490400e810980403034881000415000d402001c900c20360303441500030480c0b88070101ca4940202413000c25074891420522415440b05400b0f91908031500d4914815820400780749090b0340a08920340c0d0969460050341200c9420007040c08821141d00000d03a44a5034442c40800412000c096041c0141d0701120b000c541ca041c503280c007400311288040401000c1c1e10500c28001d06240104002501c40d0105c08042515251000040d00410707240c0d00042107842900070f40700c100b5401031703145000c01c2030032403da6241c40400307445e00c580e941d01110020000d4100d01c0760310080710340c0e440c1e580500d041c7e54a0304c00c00070f00c2c1030b403a4011802c441e45c100310056401110104400d140036034400414030b40e482c500030905450740c0d0b10751b04a0103a071604018a01d8846800b0002515035030100d02000043d901e040c0103003507030746030854004d502c282c1400e40982e040c00241d40040101d4000c44905000002411404415403c4220010300a01d13000700c036203540801c0f452000c518a008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 587034253 1250 587033003 587033023
    0xa03120b0904111806010f030b031501030c1806141e0a090605040e030c07030f030e03060c090405070f0806131805030a1b0302340b03060a0614040303140c 68
    0x700c000100f0500c004219049001e0000030700c20321240020410541d0b03010352240a1441c00b0304000c588440320314002801c000e050852003045070300074400013050041a11020003103800c4a40c01300303600040611080103480940c001d9156641d01200500300a043c942d4101103a00c0d5007155040702d0241d400d0001c0d0a6440b65840304e01c21035125402170000f454544514072040d80d2b181d0007540390800d0802d0b05520344043e840f02400d1880000002c80134140195107850110714000d003500c1e190701d401c0c01041c07000c0c4c0001561501032031400d0005103a113401140071001a62042c2c44c2d604e42603441c0c5007000000c0703031050b51034101c946e00c032001268000c140c0d00c0c018000500c43c10185031550103108004010a0b03041c040110000c00c503000c40c10200390049145403460301400250042c00102c111042e6a0940806503142c240744403102c0041c07080b0407000558081c0d58111198042c01340d440d0421245042c100e4041e1408603810001040064050008404960003042040d07040c1703948074404508000420b0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 587035503 1250 587034253 587034263
    0x4080d050c0904060b04030b010b0f120f01030c0e060d15181511040b030403050906091f020f0d050414010e0a091a1518011101060605190e030a03120b0904 68
    0x302e51401c1c81c1c94240100390250150700ca00a04007403a5450301c0183e090180300b49142d10380c2c0000d0f8021078109150484001ea040c0c8110000e203800d01c20070310552014240f2040ea202c1c00c480030007144a8046050039801900b0060540c08141e8480d102c06652140001d500740901c0ea407049000c00d8030590340460040b982c0520305c01c001c051503808096055036030340389004414070410002400800d103107105032a0440d801d480d0441d2600341c9a4086401e0f44075442c4000c0e031200468400c2210b152900a1074408241c044d070070b480140d0a22900266075109240d40440480c03c140420700a1510900c2c0e21020100140b509411200701c03000030900490003504401409031306c4a00309070040031194409440640155540030010881c039a4410813800303680d1410340340c15403021141a40d81e1103001da070400b95001d42d008101e21a6501c40140180d482a0506001c1d120038500c60b10381140150003d140049002e03016105245003a901103807281900c0c0c12902c0c031555105440301d856106d003d8000c1c4114494 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 587036753 1250 587035503 587035507
    0xf110f060a2010290a0603050406020708040e24010c110f0d141207031b0606090c170a020301350114090f070f061b1208100e060102030a0804080d050c 66
    0x100c0160200b0510540400401c4803401440340841d224034401c81708980040c9400142602c603450001c1c00307880346443c0034041d204c2c003040c0401d100511501041c010754004410034802d584000090b04100e9481c0c800a021450100c0010080f801c072107c95091240005c00014040c010702c0006000759500f11000c0d5481c841d20010f920110340100326154985004490362810207509a030300801c1300c401e403002402e00103800300d82c00003000080c0d000740c0c01030242d60100f131110341d5080708000c281c602020008464500c220340131400301d00d91803017124107a0b45002c0f0713484400900d030700c0c0c07513110700513108200c000d445015007001c03411413428030900c585070701c44584130030081c2004c4040310b01d4000d901d01c4440d12a04480d4007004100000c4d903a0b8000c0384ca09d414285842026459032684d50031503007001400d010f40c511074103440503a001c1c080a1084040d1300c00d030004a900d481201c9101042121054050380c003c110b550300b505c1c06880c0c81e5922038482c1e03030400d01d0300300c00741d59182c1038034005c0d26040080000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 587038003 1250 587036753 587036771
    0x307060c09082d1c020d03060b0c060c0f07080406260708070e15070b0708100317131e1503020a0207031506030804030f110f060a2010 59
    0x48410039000909405009191480007404001044440102d6149030325005948000700810140001030003d6805401401130049540000e912445c1e000780001c0004c3c80c254010070519142c03420f581400c00350304010540d039651401841c010754040c0d00c1e0141070500500000d8001032003800104094030469488842e1040400a03246c1440000802c141003100c9080030060815480056650703c2803044c600131b1141405540401d00b8070782580030789130031203000045010521941f843d034107000c1c02d81a40c88c0b409565840140c014104031902008050400c3c1085c076540082d200346c0076207a1481c40c0d040080174190b98130f011384176041d80c8210700300d81c0da002d02c84d04102183c40f14000008400b880e0409504d028030b980783c021340f618000d01000f0305038040c4c103002003021051684454041c45d40701c01c0d099a00c0d070300ea0030100d0900d405000d0480b01003001030001085814215404100c5640c09080a8200314005000741c4000c5906144541e00c010403025030b4500c510200300031041074107030350000941304103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 587039253 1250 587038003 587038007
    0x7050102010b040c05090d020609030a2102010209030a08090103060e01090905010e0d231902100b0604030f1112030a050702010e04052802190e090906151201020c0307060c 75
    0xc0444001c5100314a0100030018007500a821907101440c00c41b505540700247d84002020390007011f10f01350301841041c0113002002036203c902070494451780c03807010301c01d1034540d0100d00340e2261555040e0150400079039040099035080c00740400c80d005043c0401d0349074030f03561100c0019500740e11100700e1580b070380c0d509000e001c0f081c4554000080e040016010a84011501070300207000d400c20b001840b0044908100000742d9036003074621122511030b0301e6004c80c68070440295102c80c4454200c40341031421060841c01c1c0b505808540840307034850010080c0076403030781743c5000300700046d404182c10034010140002104010302c002d003000c2c07440d9103c181d00c5c1d4941e4000100300700b55243c8441c0c01a4504030601100c2d050200541000e10f105048607010540e00e04040001ba00a24070281003041030740c0200b116050b00b0000308880a101541e42c9049030340c0e54012103940e144162070503c144404068002d10a0070110030a00d501c0a2031400980341200d8150b100345950301400703040c3e40306552509510049a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 587040503 1250 587039253 587039261
    0x1f0b0415061d0a05010f020114070908190b0106030c02250f0504050405031210170c2704021905060d0203091c080f270d0306080304210318080705010201 67
    0x2401c412503181260154801150340f0030481d0186905014019001d09a658400d401411650306081c0420009090058014000030000d0041080038010b41024613000340d4100030440c400c0350489000b909907403910400354004d000d0502401c0c1113009100c4141e134a00f800074a4103007540702d14001c240c4071615007503241d92058050f07000f40e1304c07a07410034080c031010590001c1a555011403a488004403600c8040300000c4cd09100d92104403d42d40b9032039845024000840e080e0080c0a050711240c504180c0404624200381111a00c0c803445d601e00000300d005410301c0400a1100c030000545a050a81c940c0300003445608022280140705800100300068140b00740205016280c0c61001e0040c468048071003d81004e00090441c003051098000040b0b614400c403000302170141d090152120b0040d115410345485007080c1c602d150201e410300a00054510001007164220350300e100c90161884440c00c004110b240c5500b400344c0c104000d42900340150004041c0d503030010101c000003840c0051400001900b91 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 587041753 1250 587040503 587040527
    0x806160806030a0503030c0922050103060f062612160501060f032006090d0609060b09010501141315170606040605030c070c030501050c07051204030201021f0b041506 73
    0x70781058040c90b0001341d00209403a0028201c0d204191107071461008200003650014074a50f60221840b0042e60100159100c60b0617a07003e414103002c0e1001812018058960a2007110b051050b105c0418250003c1d40a0b03003500d1a87d0390042d00e01d004002545290b064004420b81400c03092030a440f41700b000004d1250100402201040c6a00c5d50b145856100380c0b0204442c10000c103000c1d8a803140655a180000c44280040c000c00c0d0000b134450303600f4038200405201c6c5003210a986030030004001e6181c54030440b070403a5416914411000008842401d803a002034103511050502d654011a4044441648010b42d4000307642d640d1071401710141c08800c01d140a030003140107100400c814840194040100e1341d000070090955952a2540c4c503203100700c44120361010740701d54a0b210a00c4840d00380c010040c00ca15009404440312520f00d001c400000b4451440004c2c0540d008402c0c0c884400303d203191a40048200100c0003a01d1500e40c40400c054031542d000d040c0d00000400018030505030407554103800 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 587043003 1250 587041753 587041759
    0x9080109030e06030a0b0405040c1e081b0f03071508010603021e090f090a02130807050f0f03150702070e01090203091b03100603060b040507110304031b0806160806 72
    0x115922689002d4022104520181e00070b402c000f0004102c44155000154040303c0600708010301d25090401c1d82a40b05540603210100c50700c0001c0464503104510040c00b907072014409018000250b100c00c850240c1c2c0310441326000764003010340c3c3c0420384d81030141000130305180018104506550740014401c0700d058001e83d040c54418007414000781c03030030000000307040b4100a11598a01e210700000380c500c804103152903030140740300c1c0c20031002e4100c64000c5c021201342c0c8101044110b071500da8042e140c10060091981000c509460090300d40342040f6a0b008284015041e28518605607182109103c0d00311952000341e840480200005562142c05070300610200031b0450031810801030058440820407600e521800a012001c1a90394090086504940382c0765001c012407590307840c011010340480298240300d54500340000b0381c003034041c080c8043c480c1c038041c0203146014110381e10155942c50b50b2158007900b84120308082602034040000c0c034000d0302c0a08c035640300060f203500000c2c800f4100410303043c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 587044253 1250 587043003 587043011
    0x150b09040b0c070804170a02030705030106060e04050a020f04270c020c24071103010f02131a070611130f26010b06040308030708070513150e1f090801 66
    0x1040c2500300701c0c0e4028015280855660801c0e0a01100390f004580216649a407241c9194003118800540c420001d4801c1c1c060700c208130303666001c0508031600d03071151a0100c0d0b1500f00c1d40326203103003d6120a51041100b50010b00700300044000325002d402c02c1d00310007401442c01042c0703441080e94450348000420030301030234440c0c0c030034041000352528100c2095038094010080c64002000f40c0c4142401c004801824060b220b50b240d0a05141c04855101c0c050700a510380030810380b880b4140d008a03a00a4440b0402040d41d03403900d001ca652411444c0541d0300c550005005a8001555500a042c2001e000400175900c512140114a40307080195200031160f51014000f0409500144030102440c1011064240034003c2100c08a014082c0303600b40b182d110500007404000c220701c03000a54020b00c1655600c101c0b036650008d091751284501e164048504503e100c0412290f0300e005500c0300e00b403000d46020203804100a001c110b50502d50341c0b01107066003e0f081501c2d80c03d82e0180e4203c00801002000f40 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 587045503 1250 587044253 587044261
    0x4080318030106120326070e04110a0912080c07060806191412150a0608060f07090b16020406080303071d0604060e010507120f031b02120a0e030a150b09 67
    0xb030f41219403000800384042d507046e0418451b000040c00c9940b042c0c070361503400c0e40c1c604210020b24500203071074941d11491a1101d8812510b0840d01590800703182d50302c5074840142081c05004034098a8803040391307081c0d81000a242186c0e000c2c403825008003604c2d290300d020760408504100f42c0b05019152a602c119001c941004400c0b01040c55007000d031015140b900441640110f40f505101c456030089006290710b00c00d02c0710b00f41d03650748420300b219070340c40070340e14161142d01c0da110460b1810350380e850001d060044184014094003000302002c10880740400707804081d5501190544141d580003001130b030004000c0222841d04489860b1002407466040020100c40000080300d5024501521003080010741103010583d02071801c40c0e0a064210f07810080650b15039000400390315840484d8000681402c40c0d110212a2419000480c00303410703000340952905540301e00d03003d13030414080c100c2000010341ca00f42154805024a02d115809208000009804c002c40031040d036100004140c01501507900704 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 587046753 1250 587045503 587045519
    0x4090b0109090b090a1e140a060e0705030c18030109032304181a03190210080106360e010306050c030906040b091228030509071403030c0304080318030106 68
    0x200f41d024440d4100080c5085508a4198143c51550300d8004841d1402c2c5509140605440d1f40b035120381e0141c0800e00007036840c1c10a011150000365541c2000c62001c0c0042110942c034a40a040214101c2d0140b40c0c10003814400a400d64007403503800d40100d080701243c69042410300d50b81a011820000f00a85003d1074000d00540841202da0303107804680e50303540350b501074650520b01210518001002c4814040d1625000782c4100444c580807813195090340f00303400340c2c6030143d03500c60b0403550b1035155000540c5509440d5840b440c5007518458882d151040007035034110215034090003614541c5440e4007030350305504d01f5404490300544480040d1000f4400c204480c07600041080e1320591140760080e550b100c406100d480c5c0007040681000e00d0b0360221341e9440c52042c1102c810002d5444041c0c1c9407500d140850700b5400c0f80c80039184040c140d0401c00f41030190004138003202c4c040001c098100c91903c7e69103141c2a065801c103820071015a0800a40703250003d01080c0905000d00048000300a614544628 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 587048003 1250 587046753 587046769
    0x30a051b09040218031501090b03060f04080903011512110402070f1704030821150105090f0102160308130b090d02040b040219020304170102041421010204090b0109090b 74
    0x726108a80001d61035034580004012010071240140880e0103540680c100ea403200d00c3e00b40181c000c40c0b0728040c0c0c80e464034030b40014290b0083d9940700c4600f506444940b1006001d82c07056401503099074948004d0300c80c1045e00c210460051070f4982100c0c10510315072508040c070a8004024900c1103005101c20008103040c08242d0711001d43c0302a280000c5425000100900d016903880a0700414000c2180210516900c5080007441d520708a00e07189a604c05c004112551000c4810500041083c02207100909284c1482c414001c014012140d620365154041e81d01d0040d03075041150000e4003c1500d259074103000100b1301c007421a442400b414400000b003c80d0405140c0d80c4040c1c41a600c0d41c01000568a03075a0459a401801406181003425100c0010391b0341d620600c2012030b44a200101d600701b180040c82544c080d60003180342e802d80102940c04005509030102c05080700145d016003140a4031409100030401807100c03110114440c1040b90026010700d140740d102420b10f90401c4440d081695aa0003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 587049253 1250 587048003 587048017
    0x1005030a0812100e0a0f0633030608030304060606080702060708190605030d0305090d05041409221b0b0c0c130b04020d060e0c090a030311160308030a051b 68
    0x140002c2c141c3d82c02058220586841c0e0280c104440c2c00c43c184200b903286500005500c1c000e80200b0701c080da50798640d21038105100030f0b685800f00241d6982c0c2803552030025600d00f08118616020807020749131a0700e0340c1198011b60302103034900c0d0350706010070a450300310058aa10a4850001c0d040601e44004040c2000f440100781810304000706542d4016051103900c50009084050212144c8001000c009001001d081c4d4007a091442050b00b1105403a2080c0300700d60a032402d14000344110110325003800002c0201810f100d0095400046000015034501d91002e6243d0042c0e03260751800c0d04010b140b03d09204540c025601c80c0b0020003c40d403030007100160201c6410800d1310034039000d1002c17880440041010700d021b1644a0300004111009508a8003c0d0f0b041c1d508494403c6803503205c5d0a88071030b40340328609103207411155030041017000c00c0c05240c0d1542c060024a0985201c49405002c91584008a400c02c1b030f80f141000c028040d05044e148100e6a0210181480d00d80c40811900040d5660107604 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 587050359 1106 587049253 587049277
    0xa0302030f0c0405010e0d1109161b0804060c050c090108030901031a0904030c0303090803010e0f0612060115020708060907150f0c1401091a1005030a08 67
    0x40300b2182200c0d4161103003011082c0c104c060161003c1f084800ba42c0ca001300d045228001d446090419100724600e160300b1218001150303000e8041159081e541040c0c4c421010800d0008950b00200d8055031158107080e9a040c8461410078944044820001c2e00020750100009650380000058103544074262404c2c8010040342c5007a0300c40503207001c0e903e580003204502180c0424040c0202c00302c0b0b513020745008150003155850745c4100da0700aa0010003801149400c0010404079881c5c03064000e1030441d03c00300114002c5d40c4243e0b5448040c0191850807240b007001d8603001c1d0003000402d00030501c9809a8545180c148c0f03c0c1503c032020361080c00c0404110f0180404038038422661248516180e48855100b00da03240c50391105030004030010700c900c0d981c800450300820600c0344220705000180c0e5203440b0754a403050000302110020340c4180e000c4d40c80304501c140080d8890b800d54686031111 = true := by decide +kernel

theorem cover : BRFrame.Cov 586870503 587050359 := by
  have h0 := BRFrame.cov_init 586870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 586870503 ≤ n) (h2 : n < 587050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
