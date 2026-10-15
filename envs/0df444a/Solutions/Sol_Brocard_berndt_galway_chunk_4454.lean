-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4454
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:40:12.661844+00:00
-- url     : https://prove2.me/submissions/d73e7755-1dcc-4f4c-b8e3-90a122d7a85b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 800899280 ≤ n < 801079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 800900530 1250 800899280 800899283
    0xa1403100c030e150c0301270903110d1706130204080a0803010f080316060b0f031b040c1704021507050601060c0614091c0207120b0708061507121218 66
    0x2504d4481c2640b192404000d50140d0700d40c41c06040500042c03140b0a42d824600d01040354140408807034106c0c0045d80f00542d00e40d50000c0300003409049071041032030700801030401d5082c0d0b44e00340710482442c60304015901903001444e00e8895100c40b021141141025130480c0c01408900c0d007524200111418480f116078403e11506109243ca00300010fa81c90003c0191003a004244403200030b011141d0304c8842c080d01c1030080c619404940c0004c010001e680c20411500c83d85440c0000c0380b581080001008215100ba441080900000309104003151040c0350345c0c43c2e44181d048640040030f19410b59a48014062808001d10340d10a0000104c0c0254019030259203144c400c8009004103401650000180481914084426800741c4028500c0703007945e803100e44224a151040303440456070b503104044524040e070001c0d94688004414048110351084032150b01076000d803807040d40b2403824000c4142ca0321440102500514250301030200c001e105c2d400e000107513810f02c03005201040740843e0340604007911580 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 800901780 1250 800900530 800900533
    0x6040f05030606120d0305060a1e062618070b0a050405190e0f06131d0c01021c0f020c0a1404050a0c090e0606120f0703050112020a1403100c030e 64
    0x14a00f45004c0b102c07041141c0044000d02034400380c90400743c01501c40502000e0380480865000320b980c001d4950000b1104600003080f1418514110028090340311650b405a000e18030040c0134002c800e4000205a003054002c02c2c0a00340040b5455010b00b0240c540d002507041800014078041050341c40300240068410031501081c401e11124891120f51100d4407401c007203160b80800051311004221440c0d80e0002016012040c80c503401c0e0501350031030707607915694850b605e002a4504070300a4108518840b08000b030004004400605075171800c42d080c0300c0c0f22002006104c1407001c21242c82403042680b90ba602800e040d13102d60f120400380b10740b0588070020300d0146152200103182c1d05014050749000116680b1101051428440c1c05616000010026604040100310034240000c5403110948903042c04116080281040d50300102a00d00690145022600c0f007070103c80540c2d9085c0c1100110749400010341c7d00780f018000841c0c144002029070b9507100e4074007011003001e1078040c2c00100c03424a0800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 800903030 1250 800901780 800901793
    0x106020609030712050307030914160506040e0c0a09080604030c26091003060f06050c070602030c03120411031606031118010c0218160806030109030c02010311040506040f0503 77
    0x7038203030380d41e0090340c40140041c040100c8513501180114020f6411007664a00800e010510792140600b14816200c0c05010341d004015001d59190f048200f500a04401c0301c849140074a440030741c00145a0260008101d0070000507400c0c45203000724100e5000b4a0042d081c0e420034a030504014080070709600f0240c3d2f00e4501c01c07032824070204989245000d0f9200c1007030001e040c050300d0814840251042800402459940e2401040500b640580740004002a9032426500da234183c80403400c060090b4402010b640c001d12006422030800302c1600c040940c40aa101c443d0b5035141400044136401c6121140c0502800341d000e007006011489a4080d241952000c0c0315544021602c81c40d01d20030010700c40003945060f104010550722401310203000034001044140601410360402e58404010303100c1524004405032030000254001c4030180d448442140200440c0521f40c50180840c015088001e04041d0b9982136000400005010345001d044041d15031a2100d440302d552511003d80350040d94442d11959 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 800904280 1250 800903030 800903041
    0xb030604062c010c03053d08011410060f0801090b04021c0b03010b10020606060c0f030f0910050703080f0403020f12090f0a0f090c140a03020307030f02090a03110d0503070b01060206 80
    0x76180318510000c1c262040801d030450052440c003c1c0350320080d000000b858041c0002c92040c00d004020f0740028ad0b480007040c908148582003021500c5900c4041801403102c44181d00c0341d01301007001e0449a05840105e041c5920f076000400900c5214400f00d240c1000d09109403400c04103900108404600350000c005002c0035a04202255100810840050b81720030300182081c1820340103002a13031403400485040004030074415041d44c001d40c007050544000840d8a40243c5800031f40202d0825035410158a454650b440040c50300700000c0c004040040d044020504062007040060308000d001d20650300c20620402651106902807004a80f04441403084035840c4e107415481c290071294041105010315251400d214040d0040b00900c40600c02d035031403e0008903181900a00050103a079500681e05e2401c103001404407001929203190b118818460480d41d03840c1e640404043da5048064aa021241c1000050910302c8048004045000c0031038804100302c10000403905846213a002d4400d07507510f8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 800905530 1250 800904280 800904301
    0x15090317060d060207151107060609050c0403020d0f050d0c14010b060a1d090103140f07032402160605010e010e040209180a02030714040c030b030604062c010c0305 72
    0xc0e1010703507004214044100001c2c4081e4001c18200d4498865150184607100e4814102c810402880008040c0002e1340301c01c008651061030068a02100204614101554040868029030000901036038031140d0702d905101d940036a41041d19844811035908500204005002c20080c410407110344811403c001d800d61010f000d900010080505041c3c100011030200300e98405482e04000f170000e840342120420758540c181c8950296014845c101c2c030281000d129145840422481c00100343c0044100340001600d00041d0a04525401101100d00b520421a20024400e8040d07445000d90035628410130800ca5400950490309450501c0045aa9820f41002e450004450003075101141000040c5c070000c01e045018003d10b60601101c1140c149540070a107014006d81164800384c1d0400541d24092900f40141d01c2c0c4019240380500203451140d002c280d4071440584003c1c41c554640507280e0815651501810b81140b4040d101b00e150441d19659034002e00101c00d1400c002402c000c00540240f03103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 800906780 1250 800905530 800905577
    0x4030e0118230a14010c1a07050304031b020f01051c090c1a1c09060b03030309010b0405130f0b07030b06040b09010f0806030c090c0f040807140d0b0a0513150903 71
    0x40c5010100384c042e070048011150b04006070000c130741940d11292103034014101c1c645251320401d425128a42c0c0e900300360801400604541e181c04408405900058005844520904100940070b080254803800355903042c1e07254400d0148100c0900d0300d052035440c103000b0994441c0707040f11100000d000508020303616a96041c810f4a50510340465401d4a0008141e05603000800640c003c600020307040c0d04110000b81158025540c080baaa0f448520880d1903117440c2c42815004420141594102e1804d603031051020020a24080c01c00c2e9030318800140d01c07600039008000000002080305a683e6114805880d55401544445002801e000e815080c00c0e40981900b43c051030009009020580c02001045160000288080b00400040c40311792501500305d809030002e030101e540502622800c2140300c1c00e10b0380d0480c3c003151007030790149201c5001c90022180c594000c6400c01010905030345082c154120b00605440040c0803802010105511456550058074103034400c0c0e0781c41a80e44680307805810b42e00d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 800908030 1250 800906780 800906789
    0x5060f0a020f031f090903180e0106020c09090a020901180e01060b19200d02241b04080601060801081b010e10270303120603050604030e0118230a 64
    0xe40c10004a010900c502000960b070811010f00d4801d042d803505c000c00103a0350304003c120b000c2003004210881c04051811002c0240c154401e0f00c40003036241080c0255565480020305000e403440201290305008107200b140c241d41d401400303440141d43d680c9184e00302c805000c0140c0035560329002c060451300c00c060040d0404c540407604498140b00d11a4923001d000300130542c40c8000d000e204c0c40796000b41e9161601c0c1d180702c20045409006e011064200190070840182005c04c01c0d581800c13407a8907001d0b40b042815810100082a0042c0440c9015480d0003500c201d4000003031a100d8000002412035104102c1e60603555948140c41502451602c00f0b84480710703100c001808140700d80b1901c4254104007000100307043c45403610880190155406190000d4100e40030f0800b41070f0341100b0310130b164124000b40c030410943d5004100c2c0601d10707182c1c1501c0310000740005040140391858000140c0c4510f40501d60b0106054068030700c1d5030364190401020081d8401840351070178510f807402c800c0c40e03c0c030081d20440703 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 800909280 1250 800908030 800908057
    0x3020c0a0e16080702030d0c0504080c0301180b060a1e03030f170103030f0504090f050a0b0a080a330504020a09110306121203070206070e090603030a0e041805060f0a02 74
    0x11602002e09440703800c0c00402820840c80705104041200031980a0145851040d48406580b10b09181c1454101240390000d503010707038101a800d0b000740792a5060200c0e0035070441041a0036407070ba0b50010b06941c140d50701c070003030b54500403d024600c0450301c1d009800b100d100341c40b0700680e60504c41c415500b0042c10120703265074082000c01000402d02507203107452407a0141c584a40f4040e2134014120846030100c1c0c0020341c0940c0c0c2d4041111044a038403882c030140c04100d940104503480e102e00d096030340d00000c10061491103214004c004010710005001280201010740d41130580c1543c0001000b404220f80236407050501440000e90f13081c4038842e01014240141a071455641c8000601c900d01441040d00c1c50035101d00722441b0107190030500518001c13521980542035509040d10700078000c0b180040e1a80c8204003038014403200d80c4d400401c60343c08207511f00740a40b4038140a00054003e01d20940c40d0594017140401c1e00c0b0801601203080d45c41032600c4000d010443d2070300000003080b8000c0c00f0300c00d00d60 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 800910530 1250 800909280 800909311
    0x1c0f200901060e10091d0f09120409230414120316031e0e030409060605191d030f0a02040f0504050c060c01020c070e0403030e0a02010e010509040f050403020c0a0e 72
    0x80b802c002c0d588552148045c20710201c150390700c2d60780160b920610413100307400703060039400d00220729600c51950350000002001000d9500009600210912030743c40b41d420036980d0f404600c440c0902150100540b4003026061800e0741c40e143c02c1000c0c00010084802c15a400b807005246000f10305582070360f0180b19a01d40c00c03c002c403110381d0198001d04404029551011205250401d030424500078600304c9580c88001d5502c540c0381a0681040e03a4550b00000e06006081c405400d81000700d00c0c1c820b0820b01300b89400b4501c41080e01030510085c0780196402e4040c024240c1040c00f4400014462025500c01d4604208407001010b9220444a060360003c1554001c48440c0b169407a0110180c114485444001450b003071100e18498600504c41d804003441c043c07180b00304028141c051254801c20809000500410242a40001c2805109001450522102050303c05190300c0d60b5101c1140c4211000b4108290b081074280070350f840c000e00400c24800d0422110208640040e180b00d60300580701c3c01d00310b602 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 800911780 1250 800910530 800910557
    0xf01060b36040b040902041a18060315060d050a03020102040f0e0907050f1201050420100e0910030503120103020418111e03060f010e0c040608061c0f20090106 70
    0x7803c0e20700d030326540c0640c545045102580e598420f03504900c00044034010300501300030034082080200103604e000041e8034410080d15850101706000d0368440400c001909a0320079000401c1d9a80d5000b0240c51446104141c004054055004005580d50030f00e142001550715116520300c0d0004030b07625186600203100c204950305100d05e0344120464001c100c540008803e268040c01c5038002c5500359031401e00610420210300049098440005041c0d80150340c9214050740074220340042103065006450240026a810240d040c003c0c01640e03000007940d607510780f510a18078458000380400d030300c1740d89455020304064400701c5090a010b0b5002d20b0841280c19418108032112408802c074000158184a0701c101a907401d026461080c0000c01d180b010075414a4414180400c0c010021203900d50300b04000e100c4190030241a41d407005080380d090218889080340701c0052a401000100071440703400c80c00b0304000c607102d0040d50b172810402412030150950020041510380a12802c000318410007034650 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 800913030 1250 800911780 800911789
    0x906051e0103020417010912081608090f0a0303140c0901090b0d0f0207060e0c06160813030b0c0a020c0d0201080402010e030703080408300316020f01060b36 69
    0x10400c00c81410b00500300b6680d07100512a013800401030601c140d640d040100104804411003240c410280d280030070311480e0155881d104100742c445000c042c4003d040014910403402c00c03007281c54104580070342d00944000d1401034040d100f1383c00300c1d9003d140d040380020b054003411390980da614201690380300c0c0d60500e4008045556803105c58a00c5400307481e10700503004203140c0d00003061014481d110001d441420341c00072a003031403449621188540c02c100320350020004103148500750690810b104c16030b80d481e200604081884c06500c014005403c5004001000346c00501804102c03030507400703035400880d0702c1c0100159030003034810082c08151864042000340d44100b96806045034090100c03030302f10b0744079104c81c1c416030065440300c0c03284d600c00070004451480c1d21051035500c48109401240c00c1030b01515503070083c0030050080c1c2140c0c00c5207403010b411074400c0091440e01d006900c000c02c1110f85903244141c0943c0410f82e0215400f100306c1c0380440104030b040065051205003a0300e000340c549544100f0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 800914280 1250 800913030 800913079
    0xa0512030c090301020708220302100311120115080f07080a05090a0b1501032f0304020d06060f05091e0a0b0f0901141809030f0d0e0307061401090605 66
    0x351940c0c10b200c8260300ea20244010034451307005042d015100d9210100751190703941c0d01c1c186604041d80300e2100b040161100501c0c40c003461518140412041024250503a0301d0162040c1081030b0001c00b000000ea445901072440852207455071108c405680e40d000c03031440403100b44c40b5040040c80c3d1a00092948c6840e500203904200300005980001000c0e0b111400e0015054800708a40716045008440d60340c0c051240076284002c007102c0644041c1c07625181d001c0003008004a041084000001804550b1107404c2000c074558082c0d070400a042d2981048840c4c00b50501070325000e86403801c04034008001248285030300e4141c0c0b000400312a0745014486000d000420040c641120000d192005581c2d22581c105004e082c1282d0242500b00c03a4504205c0c5040101c5c1940d50080180014444001030120466608003812138081d960b41e2220301c07100d0020b10380301d41000340d01c1c04003042c0c0400f0001c0c40d42002d190284840c202841990700c80030000c0840b000c03849226031040d00421508000e841c04030b0714 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 800915530 1250 800914280 800914291
    0x50303120417040305030304060c1b0c140103061703030603150603060610110f060a150302030304030813030606090b030c0a0518100e04030c06061211092a040608090a051203 76
    0x800e083ca13640e40d40b007502c1c6800544084911984450b840f013030310b40c2d00c508002070204290450b007036281515141c50b02c036290540502805411009030030b40380c0307900039041500100024103403900b03540da0000390191a90400d071013440c400e0143c1082c3e0500c9080d0b03c00701342d0007000024041c00f21500d49038100044480780b6401ca0087c01612080010b051406003d00e8041d602c0c4c90019000600d4070b240b00f4011544c41000340c46c5d400140301800e00240e2400802c1e01c00f030700d500210065840024409010b074422140d40014205406c3c07040c003042c054660741040c0e42156084d0100c076014070b69001004801103660083d603821074401d40700d6403440e00c084907410760230201c05d054800d14240c0f1403c4003000c50a046030160f000c04c0300c0c12060410410180f01707a40040020500b80039500c092940c911003940703003c0300d1440c07181080d900070403000468440511184041d920714210b4034081f02046030f46603002403143c480031503168400984051000f04031001281d5110010b4014401c29070300701040d80d00082c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 800916780 1250 800915530 800915573
    0x51b060306060901300e15070905010f022b030e0c0907030c030902030d230301060e0d02011125060203160b07020a1b170c030c09060f1314010503031204 67
    0x94a800101403d085045103c1403d840442c1b00111550154600200f40e5051041400e0800070001c1440d802104002996024030348400380d460607040403413410f4012032450303181940307101c1c0444c5036a505802d01c0109603959101403110203c00c41c0511346a00c95180216006242400040c40c8240f29610032000c0c01002d040c00903541c40341e500401c1c80d01003010302e40c00102d080951085410381d0210880000c0d00c443c801c3c04d80c0342d076050140c0100b20382c50b0052a42e00501c0741e80300070021a8029101107240c680c9040480c0d4a401140e12003100740402030003071001e80c1e030381054007040b41407011044504004d407024400d0200070b01c680e2020089003005000000318000c0035000c0000640301c000c1d0440c50313800c118000c00d0749800c0011200e02800b0030359505440707a000348090505a100420101c0782e00404645480c82590344401041c0490b0311898a075600550120016142a0306907020403004c201d1104010f11380e03030705d0b2424907075030f8420b0444004100005800207000100352100c0444804942030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 800918030 1250 800916780 800916827
    0x7150e0a1520101404171605030d05150a080a14010e1005091005090a0f03020705150417150f090c130e0111030c07030e1c051b060306060901 62
    0x410140e031201e400350100050f00180740710400140c80e0b000340300b45102d8814000d00e503030406580d00c0b0008010310100c25002200403413207040740034000c2e10550003d60080142e80d0384030241014070f001440c003184c02400200780408200e203039040401c40d040503100543d000b041c500403651116070415a003035104d0116903480c1d4808142000e0140420300001001e8000403606091204020303041c00f240d0341d058000c0303030702e00800c000409074009603461405400941e20600d01296003000c909112103500160382200c40800d02e1044060010000c204658003000c9000440302604007280c0c51b01c00003d128007004840c807010803003000040c038a49400c0b0307174208122000e040c8801c001c82c0c1889507164440c40941d96400b003210300c4c103034203028001e4504c058690325851803030996401d0541d8001c600300a000c0220703082c010f46690b1a15201010078a1594110201010003494241e40da1a0741ca05042e04180c1c1ca482c800c05e41c2c0c2130260a07240265030081c603107400c203480700c8011118080540b00b0304010801e8032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 800919280 1250 800918030 800918057
    0x80912090105220f06030f0903050a05090109030b09030a1e02060c0c1f090203060604290f0a03050d0909020f161b0329090606040504081b07150e0a15 66
    0x140104024006207400c044c40c02d00e40140541150061b80b0251121070604c5030b504002a404002c03035440f072105051468941440d000125040f40040d007004160101c124284480c40100002412850782699a456143c2048207005040702c0001020304015a1110b00401e0b07036015480f02a020502d070050890f058981e4000020650302d00c600090441103942d0901c01c0d083d0f09003444401c3e401041503909000104201508030564110b5080d8040140003280c911780041d6150141c0507442400202088401601c070b0070001d444014540700480440c4520708005004181030081d130b40c990f800910700714282503ca00c9048440c043e140d604031129820a500704101c200103c943e03030b000e103014a005c18824405125810301394141c0c0d0400941081c0c0030410400701c00750019038254000010b403004146910744e8681000c941c082d0092200d0181d203503804400d400240000d5200c210713400b602c0c48006845100300240c2d00401040380305a040004000207100203040941a00d0401619190000340384111 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 800920530 1250 800919280 800919337
    0x70e0c03040822050a0e130303180b0408030708160f030203042d03080c0702090a021605031902060606070b2715010f050603010803070f30080912090105 67
    0x10f000001041c001d41c80501040c00c002c862880a0044410680c146051038032003281640311036407004003010380307800040b550364000302801300486038020f40b51400c07800c040c913013400c090b0411660040015412400a1000d0040301c01c80d8400304402c5d2a015070242c1021401c034040d51000b0070a4820400c1c7d1182d00b141c1c12503426021030b601c4941c003000c8001c2d0405250040c14410081c0c4482c001c0c83c402e00a040150f55000000740d00400c00d86001a039a40403009031a1007018070a1014000380000715406640b0151f88030000c0359201640e0a0b201940c0d9403008001c501c1c044c402024000d17a5000d00000c030032809032140441821004001d01d0b809614440c0c0c0145088000a5010f5184408030010400c0d4503517030100501505040b18610b04541c1012285039407801810000351088000c5041c103414485120480002ea200f0100f8000603650001c004000000000c12032200151030000084c0340c02c0e401007013120303074035203007040491404c4042c01c01100c40390044c04911241d820701550f882c1d0003810 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 800921780 1250 800920530 800920567
    0x1804060b0a0806071107080c040f060506270312071104110408240103080a181d041103010b0f0f06090405040506090d0e0a1a0d06030320070e0c030408 66
    0xc6410040041340352041c0300901100320014109030340e500c000340c240200100864411382011081d94005210458000498090441c43d4441030b002040010010690070300e41003240b914003100b211014100b004003081c581d9805d00710300210190b0005110783d0000900c084480058284024000b08220ba420107000090380d00c160702c60b01c00c2c1d50002c031204070000310008605850412004880c3c50642c916180d0b10658419550120f0400c0341412810050302c00324010007001e40814203040b1016103c10290f68510481910140d5010b00ca96140312150303c0c0502400242050251554405080c0c80e42803241900303892900c0c560114044c04a0405903c580c8203840c4264040c030002d207102c4c1001d21506003440340340e441c110100580c0f9003000d5903030703100c4004001c102e4a0600d4045001500e002480c0000e006500049180320304000000090652007081e1070003c805d140d040d10030f44100e00c0380da035035184140e100b41c1da00c45884031300203014006c510b40515481801900c0c410703e0b0003038410081a81c0203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 800923030 1250 800921780 800921789
    0x6010906021204030f1a25030b0a0302121204230f0f0f030a0b090102070209071b120c060c020601380702040b0907020f1501260f030708070b060904021804060b0a 71
    0x50540d1108540c0200000d07c020441b42075003000c000608a607000300752040183e0002138000d603406c1000241d203503801c024200342e8000342c920554441e03407620280410f405070081c41120381010a01c00307051a280000a441e00b40c2001071010064150480a00010b800d003010900e40c236000c0e0b0000b0380f010075208040d035807041740d01c40d0006984111506c1048280340000c0e0140c4200810410520303000030340c00c60b9504c04a60803900142c0030b104c8814040b50305005405e0300501060401140c0c25a068000840d1416a05500c40c40000e21328507054440c6403403880403105611130070703c1140c013000320421f00061010a001800124845080780c01086a00100740c6802d801640180d619400640017030280c104141c4200080740c3c00e9514000d40d1064403441c0d604003044040c4100102d100d0403004000051054081d4816a600d808103801d0114081c0c010f0030059070600861800102c40c3d150000140e48141c0d80145040b9410016201403290400001d104459150307a4101c10b00859440c0c405003c01030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 800924280 1250 800923030 800923051
    0x30d0e121902090115020607050d11121821030c0906121503010506010c23010c09051507031e0e0d080304020f040c0e010509060d06080606010906021204030f1a 70
    0xc1c6a8414000d040c80d0507400100c50200010080580640c04610a40c110201d407510586400900c10980010711520800102008000640100815940b4101c1e440fa403000c564100e40d895185582c192518404806d61040f105038681c0e8403e070b448424051900084e9502030b081c1031243c002d010505583c41070343d41101c16030302c22040140c20f142c0c2403c0200c8506c0150024000c605215002a09004c51150000c1a03403903069512014800e104a1090380080c1d481300138000c4142040014200c5a40341c0a40c9000b0300b0184006884440c41c03208454803aa40760743d52003281c405450100d19182e4849103484204243c0945032000380d529111621310890003401c0316a40d0307003410710401850806c6040e016019904002c520f620413500b1180320303401c5040a09005a0b24502030000406a1050b94945803e0b1407400c3e0300440c3c0042d0000b4410702c561420380780d202006444800030b0740d030788020320440d40c0701070340402090000404e240c100440c00b521179017400000702460001c0c940300c80c41c100c603040c015 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 800925530 1250 800924280 800924323
    0x30d0809060106231614010c1d010e1e03010605010c08120709080a0818010806150313050a1a06010c050303160306050414101e090b01020c10020a03021605030d0e12 72
    0x500c05031b000a416420300c0b00008100c290310240c800b41c0440389408103400d910010244219150340907131440011100001c0112842502101c144403c0803107942095000f0361070028003150359409041c4115100350003403002d03030400f404012a03d200340d000900c100f0030095045000185482c3c100040e8450314403440219803142d980101445c07040e51034000050400507600140506901d8100b2044602030120043caaa2940c0300201400c2000302e24400401e948a41d580b84800d1040038a21041d0290014403e8003503903c1c0c00004480d206c4a00d00050102c1d002003001c01c00b00d0a01d108680600141030a010580d01d035110000f508640300f01e881811405042c0301041280764092031040e01030000203600c8040e1403100c200204468619000e0401c0240c0c4d161032080741603000700103038210440004c298000038100044000c0d11440d00800490240c400d44880341d01034801c1400303e8058540c0034009090104020104840758600c0411036034015851441d10448242c0c00e00c09030001b407400e450320048 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 800926780 1250 800925530 800925533
    0xb04170f0706051018052d040b07030209090a090f0609060c0e0301060602030a1809290307050f010819060902041a070308271b030d08090601062316 65
    0x1d50300018404003100080c0c1d0018412040c51244802180c0c0174400c1c0000c407595030b0600d501d015421828410140b00020f4001f029840440120511840c80b1b500e590050380c84400041e026400390040165000d00c41800040c0f0101c070307603445022107a019801821010140ea1181800c642d64001d003a10001c0e16450482201030300b100340c40081c6102036000b04000c41c0b40400094507070044e801b80390b00300104070504280601803400848003429051804201e030a401e000007200c4080183c0d1406000d40c0403004480e8903180204405e41240c002400e845000380164004680c5107100408010718883c05900a1012500074400d030713009480d420304c0040e80c0700e00b4140c98011108038000401c981ca13408010381c10000c0d511400300c0c0c2c2c0085002960b1100d008900440000200303900d000c00c5100c2c840c00c016048010000304500f95685816020381d0b0041d407030306504442c50b05040b0381e4024950711034001001a144a035902420500d101c0c119080400c03e07011602c0f641d6801409140140a010b144910 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 800928030 1250 800926780 800926793
    0x212121b0f060f01090b01050415051e03060a03030507020409120e030c06130b0313050109060f050108011b050a020c0d0807020307080d020c0402091210150902160b04170f07 76
    0x222000081c1d80102064640880c410f0300c0782c1c00500402d500d10b51200002c3c0103c4e401001034401524207070541301c4811000741c500410942090002d218a40781d0207244407881c800d418120b900820002d010854100e01710b40b401c3d6070b00d9100e504104e0b04295075000400114002805103403444c980b0ba9a005002d0300e42c07400f003624088080c1d038900d1207440100b0002c8101c0d0031302100c2404503210410415220b5132000002d201c07020303550340080d01c0c42d400d000d20302040001d150f02081b40c5407004d81c0b0810059884016190807206d180318030181c1000b80c8440e400c0a94025400381c1420041841190100c1c400c0c500070640700c044028007104c84040c04140c0504510b804e01c103400181c41c1d0360009000c106030300032000f5502c903807203051076004950000e036000040c0c9910100700860125482252407400c00070000c0f0703009160580402d0380c1c01c20b00311004a0480c0040c001c5540b80540810398a81e6000c2613141c242c8030400241c000c554154086071300201030241c0d4400303004141140c000880e11aa03140c2000c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 800929280 1250 800928030 800928043
    0xd05040f3203211e090f06011703090f060408010f09060c1106070c0609230c010203031501080606040e011212090e0a0c090e0a0c020c0613030212121b 66
    0x20340e641c10034099290390703c01208414805514514800e25a0344860a0600d2200f1842c4c80403d00e00001500304166840e0000f46201c11880043c122038450380d0f507110244484c05080d040c840d294104200c9049940303401406205a540b0041446107003540d0f07003001c0750845425004c0030748110386651148041c00001d2068025500442c1007807c004510349010a4a64000511010501602c10f81c604140b0890350b10041c45c40390700203032030f084520f001002c01c40300c0700aa07594400c251040c0c4940880341e520201c107482c00355440f41d81d0703000d180355040c0c0192240c00340100080c2e0084c0042c000000c181102a1030607000308010700510700691028102509000030001500701441040c583c20052502d880c0c0a0075402982560300281e00a100141107501e101c1c0307075003d01d000840482c280907400040d980099880300352070b001c44030b032901c044052158a0003110b07882c2d62120a1807000304094208080400d203c00340d040240c441c83d00126901031b0040c2c124040c40446603030146401002150300b045003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 800930530 1250 800929280 800929373
    0x1170c041805151e070302090a03320303060f060715141006080106030b03010f06032406050f04021b1221060d060e0a0c09051e010b0d05040f 62
    0x103891900d008056200c01c10344502c80c204e000f041310b00015001c00c1c841d60681d8000540103101a06e0203569041610b942100c0e42040c1400e20a1050114451606424000b0b101e07246800514215900d4104000c0d20082d42c5400c6c94000c4010802c5100003042e000f80c042c220300c4c1e2840002031040c3e06414075041c040000f068050442c08240c030900a0359040721000c1d04441c41e503e0003007a20410280130030301401c18070f0350901d100d47c00c2c0756001c010000e00c090710800d0a001085c441d600b00040784419401e8030160300c910358009401030000e219605080d0020040c020100391280c200c800d00f00c001c40d240c80c50b803051003030404a000c034920100c41d0044801540703441c80450850039500784031001904910312004000d190030742d1481d1540101405002203980e041d0411400c0452a0781d5000120240c94100c9460089449000d0f80030058258613651505881c0f00b03041140c00e00c088600d0440c014a00508180e500350115408600011b03000c044046241c00f81107003121210307440b00007200c0503000c041c14 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 800931780 1250 800930530 800930563
    0xc1605060c0a0209063f031e0a0903051902180105010219020f060a1e020a0b0424050a0b030706020c060f0304060b030f06010305060c09010801170c041805 68
    0x1e1584404800242c42945540444d0049140e4442d080000c4076003840d10881d048040c290114210780e00c0d02c0d114500e50341e0340a080744020700b00c0c0d25004aa105d1258481c0008894607010403aa101001b040240a0640160400581e4a5207030b858031841c00c00c420041038415110010041c0442c28114842029006682c11503186035041070000f0f900c03007804034403440c9242c07003103201001036548d0041c200311100e0010f00071590b00d00c1083c000801414440e0b034101092072164402c0c41c00740c0d1000601400300f07a04004d401a41341c4465031b85400c011210408010082e01006c0c15600564141c4210388c0540b4002c0000100300b50340300281807c1c40d01d03581c41142507402c0030003498410340741c201c100ca05203802c0c51a015a40e5a4514114004000d05829650184205460604820070004020307040ea80501d0403104195200b0104402c82e05ca000c41071400500c83c0f0004100960114071421040361100c0c042e6041a9660408201210032110703084880e010605000000e2040c1800584440b511504 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 800933030 1250 800931780 800931787
    0x706290904030905010f020a0c060e01080c120105060a1707081608061e0406080312040c0f150503130b09031804061415070606030804090f02030609160c080c160506 72
    0x2c4000d0440d956511416041c0b01c0704001e44c601d02d600c2403000e45080d0b5030000c85850f084c0d496101c010f1040c0783c96840f51b804a07004602051a041c450019101000c241c0c0c007454070700760300304070a0158582020446030148001e1503404600002240c01040c03040302640d0320210b652400110540610010f060400103124040d03060041540714459081e60444003208000c07440c82108000c20001d15041c1c0c003640c564040441c5840040132030300c2e22a0702441c06002c84c4c641d42038032504411140d541c41e10641140074400e466514815000e503014690150300c14006503146c4845031604000458222103185290f01b0000d202c0c9490300305880f00c0803102d20161420000316042c0100945105958002c041c4030320703000e00b110003c050740e43c011500080e50104041c440329543e8500004584c20a02680900700e04000d0110407030072592080c3e038807441d0010220800703919030b000f14818840540b07020504200d450046032010419242c002c0002d40314003002400041c21100410320300ca0000e401c90391007240c040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 800934280 1250 800933030 800933033
    0xc1106070e010f0f3203010803040f0515040306090807050a03030506010f11062e1215180f080405151315120b031e0f07091b050f0706290904 62
    0x8485c5074032503203415103000001441c2411081680c0b07444d148030421641d00000102c0c0780c5401101800850310040741d50340302c20391900c0420020501c0700c51000300c1000184410400715205800080c20280910003080c0341c85059210349045c01050038058000c252030b0004e00c0070559004008801240303880ca0001d4505098890080c1c4900002d0400080c0740e52901000000454040815000400c091041d01d01c890340d07000e803803045a40e0160f003581c1e04401131204045040c00c601803040c076124003e6a403200742e03455654034034010364000416140c03c1002d0001080c60b854290542e03a4543d204a10701d034440e5209071604000340010340110024110301c07140c4a000b95044450202c0752602c0d0080440e8001152000c00d00e400480c031902805600c22001c00700141c1e0011841200c030108000a03140c00d035842c0c020b020244c1f07886c4a02d040d048144010310807100d0307100e00b0107810301304490300215150005a448020a4419075401800c0302c942307100c04086c1844482e90700722001c44085d41c41c0300492826 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 800935530 1250 800934280 800934287
    0x60f130b01080c0a090909050705031c08311713080106080a081c090821071128020d0c0e090f21090306070509031009150c1106070e010f0f 61
    0x340c03040c06076687d110303c14801048418454100500005421154004180e00e000c180c40c0c140305000d840807402140119666100307040f101c2e005905013288011403900c250818410707140200200b5039a10f42e1002290300c5d504500e000901603015804540c41c11103041070340b80c0c0e0071540c01c0e0f40022419800410303c0400145100c0c00c0d990107000301360406c414100310b2030b141c8000d40f034103c0d801000d14000003690400103120403c1c40024005010148045944141043d615544e000795115aa03a002d40c0790101050210100d000c0040703038020054500c07070140d9022442843c0c00c2c00c0100c0307450329000014012144584400e59110700803000074040c0c1c3d210b1603801ca46402c40040c41c0320103102060b04903041c1d00441c00c201c07401c04601508031a001d10305040010502e41045c4e0a0b03610074003c0d0101d10944110600550f080b554002e0f60303d410080380902080020510325054500744000c00e46000c08107541444094402c91250711081d00340315210700010710140c1c040801c001401100352003040031951 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 800936780 1250 800935530 800935547
    0x117060a06140c0102040e0a18030c24090804081203100e04140303160206011203120c090f2403060803030f040501020c070303020c0a0803040305060708060f130b01080c0a 75
    0xd1401c1110315081d0b4811210301620685450001a60002a0016004aa03044041d00c1068030340740801030303412124400c51014104400c0034001903104e48111000c1984a0076840316084210040e441c016025a0401d090b10001d850607030b044e8001090401c03c020090100c0c00310800c80000442c9586054504034a5200c028040c0003900031586000804000300a180042200640d0088984030314040340c3c0107910032400c01980005000d0309000144230700d5003070300001c280c96050b110112594801b23402c0e0b20041c6000f07201c1e1000c000c40c807500092007010010740075014025500140107014490501d402c0d8405040c02c8c0c250405141110401030000080140c9400100700907a449043d103c604146019014480c0740d5a000d0142c82070010415400050f1110a0641582d07001035085d0740d46d0340d154aa001d01d21010300300380c04c001c000403c003901c100240d96100c00000d046c0300c00260050080b51011401c0c07648038808540d20030405c0d07015a004480d0036403000f510f240e1a07240ca07003660390050a000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 800938030 1250 800936780 800936789
    0x60302090a030f02031f05061002060613020313240b06030103020d02191e05040f0504030507030c1b15110a08220302090c070209101d070309120e0117060a 68
    0x4245203140401c555050000307030701040c00c00244080e40ba00201c0500c00406048e60007912454a88440000c07842c000b1540310700c10719000b456121030307450000010004c2c0d80010300382001c19079500600000524014143d00b80741480069000c03150f021389200c60100d8088044c0503100c2c1c1c4040c401080143c2e2040640c011207541030b10495034050707945d00c0c1c14042140c1600000e82d4006030b500c0119040c0405000c0d0011104212400d102d15506810150f0488006032409800a1010400c0c1d10202e4080d40c01141a548106000194044518980e0135504041d0700401c2c1e0f1011b0301300d030362005154010300c04200c0d051510040c08004659541c0c148840c418070a00c00c840c016040c0320340d052085c020100340011500500f030a40e1074540799144114581c0000003c81c81221500045182c050464810f0016100442c07032244e00d60714242c0060703548950080002c0c04154a40f200341000035030444003c40c000c007103030700d500c50040c1001c03002406403014038100040d120300c00750421506546e020b01c0341d0201c6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 800939280 1250 800938030 800938043
    0xa080c03030f0705010f3608070f080f03101a0c10050901090609050303060102010606090e0f06061b010c14120a020a020c060c0a0c050d080a141e1201060302090a03 72
    0x322070a00e8454098960075020000c00c919113074014480d000324100c8007e81c01c0380580341d480c0c00c1440001c080c100d42c03a900e502410714001400854002101521503009150090185034102890322242c0b03285a80200c980303a0012151050070030001e4280130000c05608100045103060000031060556600e50030b40f070600f8100c0d150800b295001d04203501c54805941c02c00000e20156845040c0155603520540701c242c01076180c0307480010002c2c46011901c01396480207004400e1901d070b071142118400005030110354844000c2010008085010810221200c8014000714159040180281c00340b4004014501e8003041040700b080d074070f04001c0200ba404021944011303113403103a4410407842d020302c0504207070304003000240c000340d02000021400c034032a1241d103610f2080c648840500c60301c1d4030420f00040c00da210034000c143c2c189000d00080d071910b00407210043c2c14140810655000784d00320481145103d240000d900c0c043e00c4980d904507026104909040d850b1080540108900901c203103c080d000c0e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 800940530 1250 800939280 800939287
    0x190b0f071103040603020415030e0a060902150c1605011b02090c070b0c0409050a02040506040509060d05010c0f020c030c03060f10090c09051e01050f070f0501020a020c0a080c03030f 80
    0x20038050710506184041c00e4040301e8440b51200405402503105010b030855800d00c405405c41403030300c20300440c007003e1142c0300500242c0c061a9514005071182d0302049070301009103180c6500b002801d2002d80002c84504000708503501c1d0610700315800c01d42c5c41d04110704001001c00304604c2661a0380441e01c1d07499059500c030240380d41c1c801e00042d080c0207021000703105410f08018031002410080240054490400c070411192b103603c6180002c920a0340b040d5500400240010821460001c10707950b40140081c0c0202c0c00000d0719a9181c0c00c58224044040c003160300750500c290055410810000319200c180c0060a00034007040000f551a0002054507040c007e1031800105d081c000441100010022240c0a1040c1090804048c05c050b40c5402000e0141154520780d4040320910700088054143c1078488a2619a044070003884540c0501015200b143c01941500c0004070244000c0124001075030107014103107100410025004020380c000302581d030041e98003203074076940170080f80e0b1012280000c80d541d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 800941780 1250 800940530 800940541
    0x2100327030c12051e1e0d0f1e150e0406090326010303080f101502010612050a02090603120901200f0c01140c07031b120c0305190b0f 59
    0x95502c1040e4006180503800d000c001c20003900a0041c00002448041c10094040c51620084c030500400382e0001c14040399451072510a0318200084c44902c1c08004045815825909424151010054415070301c0c400d040b60010646401c0c032414005681c00f04003c4403c1785000002c403111600608060015607603442040d042600440c0230a4031408030010403050702d00a4501c2c03812040c002d00c070540c00318000c600000e8011103092001446200c180c90280706d400e040644000b184100d034140c00b01590340e52000071801c080c50f01d0b202003145104000070302070b6001510521011180c040c014a02030351140c240c51403001c2400e015101880800e10f07003000103001d00400840401c400b8060110740f4014001c0c0c0003005440465200b8020710700307072502c0c0c0d034041c7d56940359002c601c580e0b0860001508851002d1001a5258050508442c030b0302019031161a00d0355101c1d900105660350494813941c8881c820000c1001c1809520000c0003145000d4244072041d0303c0d0307481403980c010250345030f00c0e102c04001213 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 800943030 1250 800941780 800941787
    0x3020c12180a0f06170c0a030e070503150a1d1f0204090501232d0a0b0307080405100b0d03051308030301080c0102060108010b1c081606090210032703 66
    0x340d4070003000c10366010750310001040500100d024100c0051104100c2080d803400d81d10415019407145480d452404030070f204200c0040c9104a12101d16004100000809035010003506a0740380c0810400b00c01c83c14040c0c80101143c001d65420919441019800c2600120206814203c2e0844850740ba803e03000c1402040000c0c0700d0b5070032035109140713880004031784c10604004d4070001d900e02035070005603014444104170302144e0b02484540904520ba802c441030030b042d101414168400513102ca0040354452844114a400031200c840004910b41c04003c180182080b07400181c4003075490800844184002042c5098619240034091020015100c0440c40020401c1030041040030300750394507941c445103840c2c0c49060041c0c6190061107900000f1030211410700c145061004028130381c04203040c0004007001c0c2103410580507140200c0510008954010301d00c6c1003201640701d02c030002420011403040000005240c0c006d04101450080034200c0100c0400019070b45101078519442c20f00341e00d20703088 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 800944280 1250 800943030 800943067
    0x1406030d18030818040b0f0a210c06020a0201200c040b030a0c0303020303150901050f010f0c0c0608060414060d11240702150c1f0b030a0f030f03020c12 67
    0x1001442d0008506401c04601e0138035031540c06040f903050051602c070504000c4080d4950760f503680e018100c80410003914942030400001050052080d1010078400d07110074074100b4103a07100e800541c1002e004a011581e01c40c0084180140f00d40c1d1580b0340112850025030350700240d51040b40110340c2c50307407417400542d001c000b0b0060071a800303492850810340b00d01d002910307500700340c4441400c05842c40c0c180b1000d1510041c0306058440103011808205c42003401118896089035a420600142001100101d10005011006840207448036101c0b07052520074001220355080000106030424814440c059484c10412681c181d00000940143c0e403000d80010a00c04110f40b242003600c0c9600b02d040c00e40111040900209030080741c1d14002c00c8041d42089540c1c1c40341042500503500603c0c890400042840d82540c1c0c4001000800100350341600042850000d05000554400303001c4240c01e0308045e440620258140e11918040d03040c80810750300903598441e580420070200b2004966450115040b0002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 800945530 1250 800944280 800944283
    0x402010512091b01030c020c0d08040b4e270606040606080103050d1413090b04240504020318010c050703020609030423010903061109041406030d1803 66
    0x111806042c42580305070395818200400404500c00032040025602a10440700d10020300d070054a030000420003040014041c034007080354919000c0c00045440b105142c050464110850406603d2000c00c2580c0c492604003603c0c9a1000c0d41001000200040504480320040411020701801d580381c2a0800c95901154201181c0d0035100003918801540006542c2d0301415040d642041400c1d210041110300107001d00001e03040d83d01c038003400c00c000c500c1042d01c44ea901c011210420304102c203911007204842e885500003d03071a5126040c945591805214032444481c808800100b10340704454900d01d205074a00c50148039581c044009500080c0d020b003500c500a6025008001640d00402c01420f10f80003500b041d00180700f24000680c3c5031600001311421b8482d4038070f198281c00104801140711040c0011070504000c1d507440008001071720750003007110301d480b2102a2900c070a52001030108480f440081001800301d050107000103920003160390603e01c800361500c2000064007460300c10b03044109134030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 800946780 1250 800945530 800945557
    0x2c09060409150b1203070503090907020307020a5f09010807030b1e01090b1807050c1011180d0512070c05030c13021305060315100206100e04020105 65
    0x200100000c41d51159080ca03c00303d4401000c108002c1c00e0942e03a025007480145160710401c070025091510480c080d86c480e10620449252581660119952070456800102261249640304960000070204648d000d400c0c80c03c44003400c500d1440a0111201c9000713410f01202a0040340c113044400c65941c0d0014001c0076100c081e5659403000680d80d100300c0c1d0300c42650311090400110740c40940703d040845d000c0c030301c288181046d40d007454120402060440c005540c0a01100c403103040e280c00d0b02c46064070851a039160562070702e06a501c02410002000d2058516900d09000d244883d20b110054032410300010388502030024900011034800124048041c10b244a1265035109240700b40000f08615445107108070080c40d0f96600b0325517160403590042e580b008224030901d81080466001e054121001d500401920340e4480102d030407580166842000040348410410300781c184a002c404031400d09100403e09441c19040d1941c1d00b4103180144107940314654045001e6a21840c00d80d102c12900c541d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 800948030 1250 800946780 800946803
    0xa020a05070b13140d090e0a0603060e0d020f0718020d02041d070207150f0c030e04060b070512040605160606260d0f0906230403030f2c09060409 64
    0x480f4040480c04030035046400d1880d80c60a81c0c44510081403c02c03195065440742c0c0e031010700302800e6420340384d402000c84094a84c0c905d000404101c46014800701501c10001420b852040b0071402030403c460343d116403e40e40c0c00507104000490041d110540301d19204000103031110a41c440950291050394452004c1c000056141c003080d040c212103c50248420740c003142c1c0f10f5940c42d800c201c0f80c84141011000401c0610381d88298060241f05506c9540703200346017580c0c4100490f4002000c0f24069040283d1419001c904503041110401a01d040805040200b17401d05d8604200184140700d2200c0700000c2c1c41e0b80616400400005130005406401d41801020102941d103200710103240c00320b8890300c01c6100b60204952280d02541102c0e109002541d80e03c03403460b06206040c0d03601440021070700025048400c24844400c2100c000c0d0001d10310036514510a121002801425203417650700d001040b01b00c0c101d07425180f0340700803142d90b1289011b0741c01c508075075140d10001d8014441c004c5c02501e43c0c41c405 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 800949280 1250 800948030 800948041
    0x3011401030c06030609060b0a05071103160504050a0e03070201201005150103060311060c190b01080d0513030b09010f091202010608120a0305090a1a07080a02120a020a05070b 77
    0x4400000380c0c2c3d5156400c001941c2d65880c090161a044d00ca003c5c01070f9070401c040c2d51560310400003040001d001307264a03403011401401007407418000d803042c503a07090506c00d418010380c50300e0300816400c07152902040c401d01400102c2a502c922800d030009062205840e14030940050b000c4000d40360320b005105407045480080c0904c4040d00c011100300d032010104a1b0500199070280c815a010350b908495066080c10b240000e100295200100840b014407921800208221444480d1604603104040300c44c600e5140c035110a20306224100c0c0d10051010903c008600005201003078812281c04c040c2004031501c1d0380c0b4180d401017285032020302c42e0505041c050801c1c022401c409464413100c40d4000c20449a48100a54803841c0c01c1c100d412508038100140803041c0d110350070540c9c01c46000404e90744e444a03a540ca0095410f00303048401c0c44c80302d0550822050607003000295a01880050080d850201d201080d01c1c0c0b4203000614a801e034a030b010426650307841c85070050b12500b0303034040b45580031428407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 800950530 1250 800949280 800949293
    0xa0e0115090501020102031b160c032d032708030307020a03091406030f0901020c030c06150f062205100c0c060c1a0a02070812151e010e0301140103 65
    0x300c6545034045aa0035000007140d51051003120f20400010900708072020200d0a003c40942c8034000d181d1101040b282c00340b000c14840c000310750041d8402c07545075500301209281e07ea08481c0c2c00300c2903141c4c81078035840c10004ca9007000e0b800480948a042c1078414101c500c0c212842e2615035002401248804002c108803250001400b0035500d02035200d800d02c055940400914246205003d1900180d081c0007161a8104200c2120341028000c000917041c480400c0506140d50400b14411a0580c0510240010b00d42010705c00006402d09036004449550703000d01198007482200c80011494804c03200e224505890111b264024000051800c180c056001c000281001000035013a180c1385115540026000d00400750800e0803548500d01d082503c2c050a103400c00450000c111150760f503000c05c03492000600f11401000c608800141c506110b051505001107044105942c4030301400c00101c040c030400b0302510035200d00308400d2800c002d040b914240440d014001400041a00700030200010040001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 800951780 1250 800950530 800950559
    0x1e061c0302060f011e0506090d02040c0c061b27050a0807030b060d0c05060f040905011d070c052508010603030e190e01050105030406140f0a11070b13020a0e01 70
    0x1035000d4103c40e90390b25010030303440c504980304a602c3c504819000401c80c40c00c0202c09408a200700411180343e0083c242c011505039407403036070030000090440d140081000f14078070030500000c80c0b045524003041070004014005410448219180c2d5510312584101003444a41c1540030f004042c01c124005991281107a44d0740740380d03010484045500c207000030007606102800c1019150001c059151041ca00303014000550b01c101d011060b0903408100c0880d1000c06405828000e002e2a241300c62100c1c0c00c44d030411070410016050030308020f0f60094271004103000181800c0700202141403840c800e0800303c03c3c0074106245a100e90042d5007003860000605401041c86a000881035a1240e520380d506106a84140c00600500c10801c1c80ca400500c1907510070030107950702ca031041c480003a0b0191004103045403e18100c0c0e2280100400341d080205a2940c1e004034640c03180e800645e2410214550785100c0d80c1d40d00240f88140c4241008072a805669030240814001c068070b1710b510007156110506802a0344 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 800953030 1250 800951780 800951791
    0x903020f010b12030d02030907080f1509011401090507021e01151a04030305160516080723040c0e10030e1203090c0103050a020d230604051e061c030206 67
    0x140390a03042442400c183c008181035110781c5010314500860040036400941007c0c203a0f410f248510003020540359004c00100c03e1103500e24004181c05440c2d0807030150052402015241241d04003c1040070b540c421403000c60540307101d80070105066541c1c0d0001c034a40303c00c0340035503000144900384007600f10320103500c6032100801c04500a800c0301d40310f522000042d190002070040c02e410412040011034428006809480300803200e86810340f581d91036061915511000740c02d07000350100010000c83c1420405140141658000203a004a01040104228046403945400b03151078109806490b0300c10b10f03800081c3c1ca0000d2550b00004840d0100400801054040302000c2c800c0e0388091074680e4945083e40e104900400051158120032001100030707041c0603040541082c3c082c48262030842290050f034116900350f22400b203600c480000c81c1c405102005d00098000c43c9044140f0140e51109000d040401480c040000320a03281c500200c0c0010003140008008040341140560801da4049105400703003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 800954280 1250 800953030 800953033
    0xb07060b0102190c17010b01051b1c11070e0106020a1e0218011419061116080c030105150d0f03050f0301090506011205150f03210406021006150c0609060903020f 71
    0x400805e00001c1c2260320702d03d005400b180f41403081c00401002e00c40c0c0903210350040c2c030580d510700940d1502e100c40300e130048078801d02140f00c0e42c6a1031140366080007004000c0048010f1583c20f5458000082e48806c3c0802c80503226001000c01661400f40395030314425101d90180402003c5079100c81c511508640a000d83d88071109a8407004075180f40c031005048401140c504c06603400da00d844425602003448030059103d80c040c0c3c101d10030111140b440260b0040c03605102604255000508041c02c482006140f2a01e0300198103400d16a622280190b1a00e00e600c0038203500007600c40e060a5505003e060001a001c2c0400000826894802d800240c0120800e0702d4030042c80000c1c184201c1542c10883d1100e0280e01c4510201d1014a4205500c20903090080c050f902001481860b901c0300c54480112803d01d0000080d003042020740c1085229103800c1404010880103062442180001c417200300d540b010404011030307440c207000f07240d4814268a940b204c070803c1005410b1401a45428010040d480c0c0c9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 800955530 1250 800954280 800954309
    0x2041a041a07110d0b10080f102d0b1005090310180209040609020306011e05040506060408031908060a03020f1003060f0605070b100b07060b0102190c 66
    0x1900555019101a91240180000d000c0c000459080e281d4001000c281c40400c196911402e0684941d0204200c40e0b014540c0d44106141642c1d600300014802c0c0d0143c0e80e42d42c002e20003d1302001010078a200b03075501680002c1246040e00b000d110150140120582210080d02c0c2801c08103140741e03000c2880d00806460b1209802c08942050f203150140c400b05640640201407a65400b81c029130103002d2003410b6055081c0d40c8ec0b0300f500800c26030101150100c403407076516a103240075440c0c100710440c014680494500551403c030078006403103024510405005645800c0032800960300c0f03106983c05894020200c03238440300e85082d1140d05500540c4a100464490404202a82010040034050300d8000e0011181c0c01103000600400702c50080c101070825994860205125510054001c0204803c2d6134254544105060034490408094202d07a414005100d042180d070040c1010717610099040070700002c6059220300141c3c00c00007524041031060142001c28820420041c07848000c3d145c120b04050702 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 800956780 1250 800955530 800955569
    0x10504060c05090d03080702030d140108010e0328051606021306020304050a210b040c091a0904240c050a02010b030a030e0d1104021b190210030c0509060304060204 72
    0x102c03403051548090300b007482c0c0d400360001300303001e401507540042d011b104491070480840528070481c0d488119a015000c0c1c40344c0100640c0c1ea090003082d00e29140c10000d0761508041000a01d494500c10001441c0e040e4030420740184a4014001d4901e1800140ca1104e8501510321f09540250300c0040040da00f01c0f2990b01c04a540717880001035400703a95000c0c00e054045800d110003c1e10503644104001e61203000000504005880010a0350113244504102e04290307007881203410503294079460001c0340d0f161003200c0d140c0d2a42d8801c1d80d03030740080c5c00c5190514017168034045205501c4c0e02e800d1940040d030610103044103581e4001d00405074460168000c005408010041540b0341c4250807000d1b000519031490359290b0f1401d190f404900d45c3c803444200342c41d03400c06030208050740c2240e0080344550305050304008400b0428405550101d1810140f480300b102690300080d0039202090a14081555414403072600078040c4c41100c1c0c40010040c02d50f510303440c0500e00782021394003a01440300400484401c2c4030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 800958030 1250 800956780 800956787
    0xb132301020d0e0f0a15090909050606010c0614090609101401050f0a0905010f0f0e0915101a0301050406080712150f020d0b1509033309010504060c 65
    0x45000503800340c0346042e10400c0844840380410703d46640500c24078071070381c007541e204004e9000410081708121034690b8015005060910aa40600c0586007403420710f200080001c1412030b8401000d0820602e041d095086c280c0c02000d84904113080040c00c80f05000c0c100b030307002514038841c0244000b11018244124844030640e901000d008040107610b000620107072803c14515650520042c21144400303a071104a001030700e20a0380f045c58000900c18044c02900074414411012302140c000400e2076080c00140036544000400241c0c00d403407800c8010070742000090f0a0070b030041000c00003a01401e81ea410481c65036600030300c030f090300c01c91070100300007101030010410004072200309601481c004211784400e003164560a111480303141d030b5400c4403850070420340b016000034500d03030b03c001801a500b4000e02080780c14058804094402c14403600086039000502d030040790500c1520a0504c5481b030a09010001031003070f410360442d00300010407100c008154081e40c499401544180714510700b00200340c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 800959280 1250 800958030 800958089
    0x1509030a090504090314071208060609090718120303050105040e1903051c05090a02101e0c110406030302030706050703110a05130e07031e0c17100b13 66
    0xc00461880d4008118900d0141e01000340c2c180030b030a04141c0e41946d0340c0103981507804080c0844107261640c000e0115280e104426552006054480c0c9160400750000074203141c00041800d001c01a10858501c8003400808405c001090283c003850180c3d50f50740341c0540504024010640501e292101c2c00c1080000000d00c14505840064810041d419540380bc132150b50011602150740350103014200071911941c4205885046004d0207061420b466204114510008020020401030345514168081d4441402c03c0e03000f1040d07003000502a1458039000d00d00300a00b2180590152514000005154011000380310480c4618410051076a8040d015021602e0740170708014a0385003446240e003401e000300003d20590f000076805459041d075444102d0040403007110201e0000b9158008000c0300300c048405180c4400000e81c00307000450b60780720010442020b0466003900021850301290341c0313a40d0300468401600800401550b071f9244c48140040b5030f005031041c080100c0001d80d059000a0065004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 800960530 1250 800959280 800959297
    0xb0a17010e06010f14190e0102150a0c0201060b0c030301051903080403060902010528020d031118010c0c0e16030209031c090803070f060e03041a0327150903 69
    0x1060664903100011500b000103010844c05100110005a0306410154042c0081080301144407482044405004062282400d9403d0542d0301060032005e40c03a190300f440550160400c03a00292600b5441e0049026100a5100703607040d040006006080c0040400114143c07081501e00380004011510401d610201e0340c80301402d284401c0c0700520003d94103030040d5070b0150052500780d060410031004014016500304402c010300740c5100e0079096081d01072164204000c002e007801c200880120080611503c1760025005060701e46010b512030385d80c011407000050581103500c0e070302115112080c0c00050714081d1116080725019034150031180d0702c00c0c000c540c0b0403d000350151038030624200c1c0181c2e80901913220b62007130162160340030912200401c05031186501030040004000f810f402c00004550301402d544001c0e41041005209031035443c10b904540111a0b50041c5d641d82c4c0d0000c50b950301302c202401d10032007104503000b1031034003450006034420038006400c044c00264407005022945c81c8074901c40c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 800961780 1250 800960530 800960549
    0xa0e240d0203070915020c100507140a02131404080c03040e0703060503070909030f111e03031905040804032406091a0a0513020c0f01090b071803030512060d05070b0a1701 75
    0x154a087c1d061442d060003001c071080c2405030070400300d980c94192100102c2030a00542e0320103d50781c01949007000301500400c2200704104003642944e03810001c00d10004001074801d080002e40503000030410000c59000f000c00ca2000d070001e05164000034060403142c441d8a1007446880e0010a0340c540c1845000b00080d456240d2140000d03015805031460315598003040c42ca070180064200d000700c1ca010382060f100e03c2e40c1c1c015650703915207000c101904112500504100924100401c000103811404a41c2541d40082004070f40550078030182d07603d1a030306540000d205003000000a142c100c6900700780d502440000d059982c0070901c900b801000c50795445826480f600001c00d20400d039075643c0c0280780c1c461508066510b0058202405805d50b450404201c45081010082100880c2e0040042c00d80c518881030340818646940c60080c01401240d100000c4030207003002240156a400348600e1407582d00c48191800c040d81c44007405182c2e003140c02020702281c585880070002c0c0d4000012141130710044203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 800963030 1250 800961780 800961793
    0x206010b0307090e0a200703200d0c05010b0d121d060307050a050c12092d09091923010509030a03150306020d0902010f050a0e240d020307091502 64
    0x89080503060000e490a60070651b250700099a51344071004504104500208550f40d1f0002854010410005041032015011601448503c6400c003c103003d480d000032844c00c241155010700707105004102c1c100e001a4000e0002c1c0c400c904214028003d9010800503451f00e04040e00c0241f000d07a10741c1000303110310ba400141003002990142c0102e0140070845501d15285041c0700400401ca40b80039041d42804144100c0425141c001d4645440410503003506085200c06c01c108203584c9420108107881000c0c0300d008100001542d01108002602c00c2c464030210511709498542020b00b2841c0181a01c02c0d0342103c040c01443c1145070501070b40340506181c100035440d001c20104124010140501b001d052444600e00000200304280003902d50122500d1380000c0c0c0f10f840e440050000714070002c590060200038040d0045040e040960405621820b464000d600004141c000d10850705107980c1050f000701c042200650090103502851065405807901500151660422203c803040d01d95600016400314 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 800964280 1250 800963030 800963039
    0x1030c050a08041226010f120803220501230105120705130e030708090102070608040213050c0c0109060b0f06130b180a1d06150d1a041401060206010b030709 69
    0x8032641000c070410340380c452a9032a40d04620f40d1780f1245150481a00061302e00180914540010036100425640580c90340311003a41c2e40741140c80c040204010a141003c4003919200307641820144103103a40701e002000b010300d002003041c80040d082c107841a00030717003035100200340703810141c5403a4003c3e49100d00801041d4600f10802c0361170304002c00c583c4106504d40b80b20980b600010005003441078820b5080e15254012403000920b0600b07558407400410801c00248030168a440740d201081d2405100080380036607138a050083c0f540300d15414020f01e5807038001c008052001c5503200b00a002c01c01c46081c18280c10301001c0040c540117060809244440a450800c01010302000504154103140d4504104a0191000805031003150b072011108052380c030311503000503100204c1079a0107031088410802c010280da6006440d409040b0480c100c8660319084000c540c1d58001a24804140050091220034910020094a14020f114083c0580b08603070001c5204001001074a10031440d0341d485a5085140 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 800965530 1250 800964280 800964293
    0x1701140d060f0e0106081507030c0e0409050120130b04080303070c05010608030a030e0f07060e13060f08240c03040f0f0b0109020c1603020a05040504030504080f0a0201030c050a0804 80
    0x2d5410b42c02c1c60703540e410442003420a010344002004840c000c5c1c40d20000704a0500c080c04001020042010b143c102a00d4010b9004030108610001c01d49000031030204905d0200d0050a0510034061060016a40e4207200400180102031001c00407a0700068655142e08041040c09a401202d4260304180f00043d03495102d4511342c0c0500b400340e0004250155241581030070343e1f12a09100c1c0020791a2419441071080030840c401e20180d410300100042840c044004104900c20500b40c1d12403003400c00d403154601c01c0c80d0000d001402c1e940f5040c121440d918428280e550601180301c0401c0c5203504409140c1010a0f24032a200300c0000050f6403440d61103a03103851a170841940c040f62000340c0c2d610418041840800d01c0ea028003a00d540050703079000310000c1c05192040c525124081e40015803010700068965011400c2191416030300414075480350300d0203039014090b54001c80901e1003580191444904006100d0351b401e4001e0b00e007048100c28080b0102c1c0c035449030348902400715080364003040001786c9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 800966780 1250 800965530 800965541
    0x1d090714040f091b0216062007090209040623041d0303070305010f140d14030c100902150f0901202d0f0d050c0c0a03031701140d06 58
    0x11420316503250540720b600c50304008009401c4204496a0344d00412001c40015039040d8000640c1e000403e4550b05c501860700704075a43d030242404104d4110242d18803020079901100307011403010181d4074480d0f15014031100030342110f22aa44600d040c14400520280c10169800c04070200e03082c100654440da100341702c06010407508204400d174803c00100b81c041c0061003c1c600a100c03541e40403510f540740012440812100c0d0f042102c0100a40214080da60307034625445044e1548280c0c42607466030089921800c41c02203806c040814010075414504040e40303a840340d40e803a407088800300c0201c9405544180c09000d0041c13003511040f010082002e40c3e40c05184c800040740103c101504001580c8066a030a0102d100c4221040e0b00080343c180030f44005420300d40081409240080c00071401d00d0450340d50b00c8405c0b090341001d20000080e00e41c00b48105020100302d808028100d0302c031955503072400400d6050342c000388919518150001040c141e0f0300710b80d0090300c2040100804003445051b140c4800916 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 800968030 1250 800966780 800966807
    0x1e111002070c0902040605070b15060d09060902030307080a08010605340206040902070b0f0423071d0f0a0905030307030b061b0a1a0702060c070f0b090d1d0907 70
    0xc100c00c2c0014500d206000030300c0900183d568080d1941d4803403030215103c401c09800780c0d807210900105480039440e03d50035a4014024141702007583c0c03600d401c0c042c00402c4100d001035014040001c107902403140c5400203280008850740d40b0f18480c1e0382c542d41101e032401000603104100c44089000e4000d5403483c042565042c00c14050510030340016030024183e5881a40408100c41e00420f00205128008070310941c130003481c0030b02d0003451420ba5180203078400c2d141c0080203420709402c190f14900c0010040c01e0003800c1c4028504451400480b103110354404116174000d41c25469600003001c0f81d03854080c030152a40e02400a604640b555001900500b410302c0066400400612211011000000c84a110040e020010b80392480b0541858140c1040c100394078904003010000340948654000f461603405400e800c5400e40740c05d0b440c5041c1c16800d034502e002034032040f0342e0700501c4a940c0010400d0407503c40191503088246200c2e0f4038034a411510f5070035060707011642ca0001551113000705060000036 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 800969280 1250 800968030 800968043
    0x6090a05010e07210c0e010207060302131703040305010207060902102f0f0709050109050601090b0403020405150415060906020a03051818010303020303040c09020301050325090c1e11100207 83
    0x8884c0c00c01403404031070980b0b85484c0024200c00201d101d550f01800014040c04482c6800e52809032201c2050800f681144036584904841891071400b400c01402664061603110009560318a02c40c01e069015007041807059201d400b0141d88135940c030703000d016180c9034420480e02d120085000617203c0400032440c400c00b503855002d24411141c14407014405007000c4d00618134005010f50410344a8011a88000d003100d043c002501c02c00d2165207616416103084076411076000c5a503985450f00400c2c0c04a80d803400c103400a003844040c8500e103007250556000c1c0e0b1a42e0b910810300d286d982c5000c84e51022030082c00b9001c02c1c0c082000c1d04465040d401d080181c0b510280192600305400d00d884480003d09070f1003600140c0010040c4010020051320b004018204420300307508550400000a444010034140c00c10202c0e980348009420030b0020b0421401802207650030001c10700d4021002e48058150031101c2c59421403140f0704d154035402403004200410040c0014980160286010402548100303801c0e5200d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 800970530 1250 800969280 800969327
    0x10807080405011e05090705030d091a0f12040311031903090507050d0813080c0f0409020d050f07031b060e090718180c020a0b0c071a0f06090a05010e07 67
    0x7000843c45540ca00315135400b40000b11441d00000c403a003484801d0b0803080c0700381c110318988070406600c540d041040d40c02c040200c2c01e14400e4412072101ca445181d5460944038000f08000039420002444140b0441c069103c040845001c0e0102e00c3e100c3c402e002018921078200c000040d010b82c8227a100d0316805103d8021174007540c1d00e40b000030b501e182c103da0b8102d4205400142244c0580c0080316a4030003415035030f004040a43e511000190340450302e58800c0e004980d40c500a8055680d0451040040c1d60010141c428803072942021544032807540c0000d90700440c24001044101249030f5050040311000d036110a03400840204003d19590701038050800c014010580950b1385481c000303185e0040c142e54049440c1090604249000c0e5031300400c1c10403e5401c0010359901041c05004d01507400200761601c60303941c41c000e04e0400610a2009544803c20031044104170180011001c031500415003201d411465540e070904c1a01510b070f00f40200b8403080c820ba000315004074081c4d44802c1d0783d1522101280c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 800971780 1250 800970530 800970551
    0x1419020903120a1403190c12060f0807060503010b0a110a060216030e1002070605090310021309051b12040f02030d0e010305090f030906070f0503030a020403061a01080708040501 78
    0x584616810b401a001034002203e040c11034008034103d56443d2003928450840c83e19001001c24100c0c00754035413251a80f42c6034400c40b02c5104021036199146d01080030407842e91120000a03181c07525024140c43c2c0c0c401c0020100e001801395040d00c1c100c480300e040340d5141155211044400c8003241084c1d803280d1098416203070024101c1e0002c0c0010358400c580e010703690030560800500100d80b504100c0c1c007a044006040a4142d40491500c050381e0b00c40c00d145035075110b00300100e80b40c001240307280d4a65610100b10303c420341c512050307044c0807244030041c10f011689421550440c002d8002030f8628040c041000480100000ca0409952040c02030030034a684c02e046030042410980500c0840c40003034881d1710030041960305840f4030340e0840c1c180c200034000d410600152941c3c0384918601760f8440c40d4040350f0681040741c41c05803000c1039a809015a0389a040421380c0d0000303504203001c112286030a00f84228a0001e03064000c101a2205946e61070141e100c440301541e00b01ca008d0001c3d949035480d0010351a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 800973030 1250 800971780 800971783
    0x30209011202040b01030c0c03080c0d020406020105090f03120f0a14090a12090501020c01080406060b04420c0c030209070e0a0f0b0712030f11090103050a1419020903 73
    0xd0090110703061080340c100051042004450790900ea05050624005078101010750112280648540c50305040d005611001848601070140f410096046400000c020070b4013503041d0010b600076001c81d0112801840c0c40c0310240d440703002d40728803202320144031710000303030207011051456400003542c0c200000c015180040c40c0402e030004845860307040d030060400c0000c10031158006003c08aa503c0c0c007054550409000139180c8110072100f60401051310702003000d100441d0300010013001e5111a8550321550380c120450ba6100360700700b8481a626005c008200a0003e03040310441d03890060701420060700d05001a0b030325400f64a41a0b480c3e4000000100c01615241c04440c0070303a0090707c0d4094120707403400810181c12900d8110b960070445582c0208144902a82919012582700382c501c4081c190316401100106001c420310040181032000c0c0d010190032030001031918800a9070103100300d80d90026000259001c0c240ca024540e88240002503c11610581038104251011009450400c41c540040d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 800974280 1250 800973030 800973049
    0x70f0309020a1d0a0b130e1c090807060c0b0601081503071e0f0302060d111e030402100809060c0f0708030f01094d0a110609011505060c03040302 64
    0x1e001c1c00283e4500145440d07040c50801c0e849550200240158508003004c0744c9968924810305150f42d032200d00c81602c0c134400348210007092024081c0b4580d0070680f0440204007807058490100d0314018400040f4982c0c0c895a0004012a0400e404801c2c4da2900001111038810041c0040015001e00360074824603a018002d0300300800041a490729240565189001100c0e026800b20603010781c600410401622400700f5280c2030b00c0c4054000820115914007803080b8428111425031641070301d941c01c0d03500c501c040041c6008500a80e0705400c05210440e050390b00402c15a481b2296600031400681260ba6640042c040310518072138407030400076299202e00c01908140c8480e10711001d02c100501c500c1c86503115401c1b40f030076060010301304004183e40403808146001c1c00c204030441c0c2c41c0c16400001031004070090b00c0d071002c04600c03607440d40d040301c2c0280805070030600181c50b402080003040050314140107130750f00c00c0d104802e1101c0c03591400d420042e1035803002c5816413850105100000269a400300034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 800975530 1250 800974280 800974289
    0xa030804021518030f0f07120809090a0e01110301050120071d04051c0f081e0a05070f020615010c051510080f0d0504050405040c210b010b090603070f0309020a 70
    0x6002c203c502010581030241450110040340d02507040d0030707a640c50025480044560800d000c1c80000c0060600060364420881c4e41ca80020064081c0038200c0c1140c2d0000305402c010300003c1150305003215980c0010701c801e00c2442d000071f200c503030514015203a4041046610280300120f48209980380b50864804880440d00b40d10881400c0c100b00c180401880b034100324a01980342a00d885403140c10203040c09104114007010403000340c0c0000c940c0b07403040701c420200e401d0b0104051103e15207020044054031084880034001107090340c002500314000101580142c4d030584144180720402001100d544c01c85003000e5a40c0c1c400c1c1c200d400407500e07015602d5801442d0b0038030b0145d9101d00f031513000c501d80242c0e0340d582c040b030f980001c200345034056005003560203449040341d01083c240c5940c14510003881480d0405c140d0200f110016140d00560740000d50180d40c03241c000d0740e020781c0e661109204240603256506d900003000b00000340800307204480310808401c981c200010001c003507802150110403c0d400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 800976780 1250 800975530 800975557
    0xb0a1401200c0f03030a0801060804080702030105010b031e06030721140a0228140d151506111506030a05060906011a0901020c040b01030f02120105010305090f0a0308040215 76
    0x340300002c1c3c1042c50042114490a40007940b800b82040780c001c0807007005100f001c4c10400704902080400100c9030440c2c1500350010700034070142d61a12500841070b4415591640d980080313138044507138920103e01c0e00740310303140007005040d19600d0803c051003141a003c101d40c801019034003203d000035001c009405042442c0d03000501c0c032180a0b1041c4000c100684489400c03001881d4a840340000c2c42c800520306507110304154002036000100032585805554000600080c1280d81d03080305503440303178018024810030b040c80031540c2c4c3d07070f03408151035045180c10b059640d0317000490600c2614081c00e0071150840b2002c0c0071100c0300340307882d2240c03810a031050b20302d0704450b04210b004010602800090448015401705000e19144080d40080c1d44c40c40349850341800303a6210301c1c001c01039a009034440042c0e40c0800300107642d6900691041003900d4024003606010914010100d80040c50000d42c410340c00d240c4a0080c610803d250f2400ea40101000b4412079011071185100d031180c840840242100d13044600 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 800978030 1250 800976780 800976793
    0x3d0e070806100f050d140d0210060b0a02250b0a020c040c0e130504060b0a0b1201062c060d09031707230d090c0b040807090b0a140120 59
    0xd406504001001d00704002c08610b80400344007403500a650709044540403104600d03182110f01c1e0001d0300880c0100842824081d07143d0300d01c0056004035040c0825404048c08100e941d03110f020844603401415180c0780140e001410043d040308800c8440101034411940700d204856451401c00490fa2000041c880181c104070701280160505004803000480c4500742100000304c640045416803030185a91a041c54440b00400c043c05041c0d8400d542c0da2101500082505803034030180030169118245d080a04120003000285e005e00c100b042d17119601441c0d05039403031607914034203d908401c9811900c03544401c0c20444041441c5c00740c414980110320075220200006100c001c200c41040009045405004034012000086028030b400030030340410000046458810034a0b8010080655000c020035081c1c00010200300381d40c3c54009070081f104942c08030354056444240344d1056500d003845064100080c0340c800d2204d503281c180c1c00500d011041c5000320b0076104190740c070910655600031450a03900a030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 800979280 1250 800978030 800978039
    0x30c050d090507031212380117070e090a050615070804090c031e060302030303240d08042102010e040c0e0a0306020306120303060604030201030c1e02010606090501023d0e07 76
    0x10b0180c7c8484d03001d071001203080c09400103000c5051000d850034002500c2841d420505060b070240d80a80200000c5800c1d0212034600480040c000c001d0381c0c24002c0c420288540000c041c201d050062511400c00940b018040921054054082e6000088110713082c5800f0710000c0b03810b21140c4160390521300559800b09a024104400340083e081c02a00351040d241846c10a00250f280041240d801c0030741409403440c819403c004001c000640140034036804001c01a050b01481150406003007074441c20342c40d891542d00070b21580301810705440d030b00074003083e0324545200440c9000d5200b0b6002c13149a0522100070184000010800041034004075516903012080c000700d414084012807101e030100c0c0066246041040000d1140d001c2c07807000078105030b1100c0c0110a071511446440b110f83d070500440c01900d04040d400a4082c283c2c5014283c0010b00d454000941c039031000840d064425018842c0711074540740c1020301c030105410b900f9582c41049061500f4020900640700d2425606a580041c09549041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 800980530 1250 800979280 800979317
    0x1608191a07030c1e0819020d0e03030628090510081c0201150308030a0908040b03130209100b2a0f030309060a0603150c120c03150501030c050d0905070312 68
    0x4011a0150001c40115119205400c030421580080c0751321b0801c40091303010700110010f441021000d0501c3e90911003051003000300040914080c58080b11041006075401c0c4051000f03e02041c0740c481080e001c01c904102503c410b030b1125810040484d002517030a503d8a13803241c40c0c8011b44050f8802100c2040283d180a5030a10840d03045d85181817583e0b04952440d101c0b04603a0101401d6804481e645010590810105400f02c90080014082240d02c0345070566500300f0344d00100400380d015442c040006008044650004825901000e20391414101280d11606a2200381040c00c0a1111650411075070007808024050403902c0c580001c40e40c03850b1000c1038506088001e04108070b01802c201051002a1410700103403851300b800c1c200068108449002115502010803445480c1c0c1d00d000d9241b090640c6c542c004055854210140888950707a4030011800c48640303001000026809000c115007540c40f54020f4043d0038051411034001035107980701e214000c1240304240003c218902d4060101081c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 800981780 1250 800980530 800980547
    0xb0621071404050105070213060519030c05040504171b0303010b0c0c040b10080a0207020a03060905010b01140a20010203010b0408120406020304060503280c021608191a07030c 77
    0x80701c0115505052501d40080e160340507008000f0320508a0550f0071000d601c15500800040800030803407980000440200c5880c20f50074001503459600b800c90105140c102801200c1c01581c4c400c28079000c9030142660500107410003040c810b001003400b00c18102d03001c000c001440c060141843c03880e81d100801c0c8556403824043c0311001d8002e604007043c00055903110101401e100505080c241607d030b03908501c01d0020321441e03c000b0740c010075295003c01441400c0d408003a409101e03070000c0120b010700800650710001c901f664608074920421011203030920a404c0d6140354a0810103407002113400c083d82c0d60a9070000d07000102e6002000c24104030500007007195130a0207440d00c0241c0e241c01c0c10320400035203d02c141c0c0216402d204000022a1184015020140c1800d80b085451443c091040c0011030141c0400c2400c100140704181080035090b0031024020111a8401c2c000c2c040403a422201444000c100002662402d0208801d41d062203007040200f4030400c230503540000e04080222020f41801e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 800983030 1250 800981780 800981807
    0x3307030203161b0204050403120f020a03230118060302040e030703180f09272a050616050f0a030f0206070503070f1817011d010213090b062107 63
    0x1a0810228403100f03d41203c0300c0203990155804210303130b40c80303003020789412410746400c0382e4441c80c01904201d000c0c5c050780603043c85041070b5001d01c1600d4201454000354141031519409900140b4010000e1800d8056401c1585144000c04948a0b5880d000201126102510450140c10028440080580c0415000c1d40039048100d6054079900b0264030a0309103040340910080f00b981c54221000301403070b44408c0c80c0c09940301c1c0003803107281000d49404c01540100002400940e610100c852049600240851054580140580e4180909062851341c0a9800c007010b80715030207015040309404400388400074013103000b074943c4030001e54011070007450302000a140b01c0c01c016050080c0304481e640054201da400301d284c0b07483d0320400cac1203600c00c007450881640488100c04c103103c040c001104040d00a4034940d0003100500b001003010f106e400c0d09038851240504030824980100b8068400749620101001c600a000c490418811b00000a0010303c00c04c2e250b41c9003080c3c0c008120500350b112507003001e000e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 800984280 1250 800983030 800983037
    0x260718270e2506081e0601030b0d06090309210303020d060f03210c0c090c210c020105130201140706110301030804030b07020f0601060e010c0501060605091f02330703020316 76
    0x9281480c110395411100d402d4085c8203e41e20008102d03e40e2203604101451800203084031409209441d080b0b0091201da1000c9011407500000001d108014011810050b00c654200c00ca106100703a4003180258001e550202a5942e1074401080100700359426102440c404d06c80d000501814184105c80c06910743c5c1a94200f02c210f03031a000000c0c1d4031f0400d41045849000010441c1d0008082c20b5840000014240a440c0c498401d02c10924043c0c2e04680d4241c0c4070b540080080b0b1b122001180000405004080d003c41d04240704102d14280d40c6005000c82c0b801900d0000b01e0f190302c00301c113420310380c0280e00c151260240070a0900610a810b040c9a0304458140018140503003154500f42c3c42d1101441450144000c01c4400d56090f40503942d0550610344c413000800443e0388409018205d5003101071107078081c82c51001c11080c030403030120b00ca21281c11150001c0901803c80070604039459186200944a1381c031450300d8a0b40380c1c0d10705034554081e81040d100940c8910f000984111310402c060080d4040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 800985530 1250 800984280 800984297
    0x41508060a0b1815060706090210050a090e091b010212070506010527060112090c03140d0207081c1106040b07030f0c0816260718270e2506 61
    0x3040480148041a001552021b840d0642ca0404000070310030114060340107035410b0305400c0c5050b8000001d00241540d078070350b4000306881d039030340000e43c04d001c8400c0f1070194807210250600d42c0914020305801c1d04144111b6480da54000c6820040d81c1104800b22001c0d40107100502c00b62404050b5402500402d405d0550010301580c0195509203018244506108042c0c0050b060712560f0340240442c0f58011482613081d80d5240307032101d00400c9040c440079260042c800701022007031002c20280c04850810b00184041800b0180c3e8001040409640703605200b040b0300080300d20081030150b940325500410441c2c44030300d0442c6018094440d1200310148452071700a001080c5a0000380503600850035010003003840001510640d869103000308403c014100e030021010007904003000303441c424211503803802645140025030108002c0d16014903940440c2e020506040000c040030510329015600c04040f80340320008001504200b54651880c400070a120800380c08400d0300c180707001c000d15130f84c68103000b0b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 800986780 1250 800985530 800985541
    0xc0608060607170d02040b0d1a1e030a170a0212040b0a08040f0b010e04051605090f130b07031d060f130f0204020a05071103010b0f041508060a0b18 65
    0x110321807290000c3c203004402000e2249985254103844000919440465599880342c10400e495000300c4e84d892072150425689401c0145000c4008c1084600500300c80342507489000b0010f510042c1c0c1c22087c1d05071180300c12000c00b080d5004c40b4012601c0b9452280c940d50000e0640080c1002c024002c00000003801b004200b01500411040b10a00d14151901c41850f407079510304040310103c0c1110181c104120040045254006280064040d0740700d54200c900d003590703102d0f1002e625801407140540c04810540003400036499080e46a80c410144c0105804003a080d50340c0441c0b0203403e6410500080c0d0b1514000c46903841d4808200685005c0e500400041c940070800214911008000e1009146081c00c04020081207a054041c0e65038010320642d04c3d2601800010590b030031000342503034841000c0321450903600b010700c50341c4014030000e023082104852010501c0040d11280d41640c105013070161002940360000e02030079002d200741c903201240c00800c1500700490b062203808541c801e010010140301 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 800988030 1250 800986780 800986789
    0x120304060e010302190801061d03120304030c02041a011236080f0703030501151202030c04092f0c0a110423160215040b06120703080301030c060806 65
    0x804403422403800485907041d00c00101c0181c058000c25807141d0490300902403107150041011410783d100e503940e0040ca080031001e494441c1a1f84901c803034241d00400f951000f030110070317001103031721034001d051210301000d66901040844401070441649010813482011196074403079048100103402a03024001156403551a800800300c3c240309040f04441d000201d10203609640011880b950003d03501030700d4103a43c01e5a000f455004800440010703103003c1c008a001407990302403207542c0313840d941c918111462a07201c400c000d60018108001c0f2003024032000607140d0305401070480c085461000a043c10788140c0c18008604828002d03000821410300600d80e80c1000001c410810b01d0f0401c14030800c0d0024500407038001d0a507540340a003500401050040020120500c1d68003400c0d40403111448800484002c136204c4a1082124004500142c0491301081500300400e402034002401d00c801007081110b0503140c045180c3c0125051034000c4010000e005424452900a00c650b0400d2441880c1190004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 800989280 1250 800988030 800988037
    0x702061b0c1e091005060301151e083402070e0f160f0504090e0c190f03030c1403040602100e210309120c0c130c090302220f020304020f1203 62
    0x54003658001c0c0001c3c00d0130040f0000440108000382060390349507115140c1d01c10070903850703090307070003090a01550a400c03903210401050900b94a0355180490780720f0101401100890b44018400070140e0845820300c14030005e007644041240f80c0060180510b80b02080c0220403008083c55000558070040044003040c50217031455a403950315002000702615402a10140680c0e0030454503a0300e0310440425074240010214075428044444250a283d50f00c240303000c1074414064101c80181d000b004000003170046440b40e109911900c074030501061000c02651552f0000e6120800680c4000d84001d840a66446400c2c914003212003d4070900c0c1802001d081c1e04100056070124445000000076080f01050118500c604c0105126640d906030074030703005513036200032001c10b4424089a0558085d40902d88107442d0300d06045e032641c4c442c4c1460f54013004520112821000421888540300000c0301200e441843c14404c1a4500140c40b400c080c0103010381c0000d200509405210150307404460404c5c004240d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 800990530 1250 800989280 800989339
    0x6021c2019020a060f091a04080d110702060c01090209010b03070503010512100501030c051512040f03110a1a060301142406030924040c0e0703020702061b0c 69
    0x714140c1250420803860080000301c060b00c41c40c03811850890340130207034018441c0c0d40d0203800f09003a00070450b4800401d60b042a600100007680420101d0070251080d001406080100080320341455056008200c89520000404ea40d90355120060401c5280c00900e07240500340c5400e4081c214503040d0406803051106004682c41140701803200c0290800402800c026685811400d01007542d4a00c0d0141c050300060040c1440361005c401528040c1440d00140d5846107008503140000d43c07215103c84400d207420140a600f000280c111180d4200d80410a030540c0600c0b03504801c219a041040f801d00402c13000d031515100303074100030000390240c1c46081c0321030b0807845000c1004800001713002c03012001c4d94920300303441d00060b010041191807680030515450302c10030788000750116580708080309160301e030440d801480c00030412000c0c0a94042603450340e41c481e0b503a0034014078042d103923000202d65403c80d803148042440705015040303021000340904002c0c6041501c0c0f605403044030358140d60b0084800a603 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 800991780 1250 800990530 800990557
    0x901081f09020409021009050907030e070302120f06070806030c0901082a030f03031906050108070522080f0c060f180a091401031214030c030a0906021c20 68
    0x1441d0706659a0360711450b00c0690080c0024241c20325068007800c03c0c5128401c80c1d20410003000040e1010b4046d0091480744804d10f80500a02411a0b0800000c0800042c40101d280b1580c818203441c414100480b0b80501c0d000d48640c41c040c9080010185444041164280280521386c0108900c41000400c00d4911010030007030303091080340ca441c1c17400754403c0380000c60f4507100364001c00d803000034084000c43c091081100800c2c40108003200c00d00641d0064418180018a440d0010351407604c5000a0b0221424900b12003000024180050014504a82180b001c5400007101141c02d48802c010700740d1a0901910094246291700c800580c1d5402020100d00ca4036910141e803400e9552141c0c030b040081c1210560030800341c1c04043c80265054402d0108940d500300c00d450b000c50842c0660010b20f550f42c411030304185560340e07181c00300030785402c0a0700044409440d514110300194180c00a800d100202c4488802c400000501c5002507072a28010040201c1c91401314640101192044500c11201080d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 800993030 1250 800991780 800991791
    0x30818011a0d050c06031314030703020a120201020408011b110c09060609150d05180f0318010c02090703020d06050411070201030c170405030a030f0203240a0f0f050901081f 76
    0x1802e0781400040f0480b1688031800108104d070a80f031f18451101c1c0c40d07004580102480094400d142d60364803c00e01c1c00b07405680400e6021000401d40007800312660083c2c4005420990303180b00d103a0a460078008440c62494100b00c1c0c50303808a1b40b011014201e6404100108860030703020300812030522000c0c0000d030080c0340000d0b0485c41d40e00e4400c003806140c54040702c6d880e920a05a11400b000704401d81d41c480401a0b042140c0030400c1000924241500c070700b0001c0c1d49080b08070a2003820b9a810545c440b0305200c807201c1031401580d100c80b0340d5440360b40d4903200540da0314983c403e0f10080301c20542180e0300c0345143c0341c64044106003e0b01a50111a030a00700058140510001501d03944071044281c00c80c1190b03030041104003c40070002e400c000800d45c030b0034441c149002030900142c2c04121140082c14185102c1240c400940041840500c140640103040361600ca0190000364009508003210304004200c0400640c140071800d14010a00100503200c107030307944840c0c03e055503103c4015030341c0fa9803070702c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 800994280 1250 800993030 800993033
    0x3030a080615040314010501240509040513150c020705040638030703090606050a0b031311100503060a06020303010e010b0307030b120a060b0a05220b0607030818011a0d 74
    0x1c1100c018542040301c40c220160300ca0541030203440c00740030b2440240c10b480c409c5140d400002c070740746038000c03c5c40d11894100031241050000600d001060842c45684450140c8041075065182e400c05140203e0301188141000071f000c0d14080081c3e01160055250040400060a0184c1c4010b00c0d02e400c0a03120b5030719007401904821304c40f0389c0a00034620b40300000620081503016804070034954880c0c00e0501c044c564510400c451202c80c2c1c41503080c960000c00010702000b00c201c50700ca01c000cac0708002500c04031001201062540da179624000e40480d4000003442018034101c141140207000710b2004510315811b02c1040e0501c04410b1242d1021303103002101007810f142c0170b03030042d9100d0710f4058100010950320b410707165030b510441e64050301d00701e10308003807800c013402d200030401c058520140145d0080521a0960ba6040c1c9100010000044e41c0d070b81d4000c0725540b00301c020300c01940a5035410341141840124028141c660691142031a0303d450410b4140002c0c200c4210f1070403000b1600043c003030449 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 800995530 1250 800994280 800994319
    0x80705010207030b09240406050a0c0f0e030a35040303020c0d05011b03060303031406010f0509010e0a090b0102060a0515100c05070e012105060a0908041701051503030a0806 76
    0x1000454240040c2d0851031900001d003000301b0780d00c564000c40041c032244d04d40801d001e04485135036404400082821140300034071401205450b010107009401c44074001d9031515802e20700001071010100b070901c2c00f810424001d0440840c0c0850340481e008031031034a481d6035000b80d603c0ca40954054041c00c1c80b411314206001080d0b1008101000052100c58429940100200101003034003045010a241c031683c40041d45900704e4680c498041a1144110ba0a00c01006d6403d900540103107410488000001c6000b40c4071444e05070000c01d506140412a2a0030100190501c2002814844064500380c1044a0201c0b14410700c0412070301580d00788800007142c00300300d9030070f4070300c031000f50091140490000307004040c4120f803812560500d4054510725411400f000d0a04907011001d0300c03560181011683c40c41d015413042079075a1007001c1c864500b43e541c2818104440c1440c0250300d59954400801008101c450321513400d07003008401851500490403005084e002c0e02402160180c521407800042c0090f4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 800996780 1250 800995530 800995543
    0x80f1b060c0304030b06040c08070f2f0312010b070f060216050a0c05100906021c031b0503010e01060804050a0308180307050a150e0319021f15080705010207030b09 72
    0x10081943da4440e100e040450840c00c055a2550050786070031000c9401c24445c1c1c4155000301060f50b9400b4100c05500002c441c058030700d5240080c02034258981c1003000b5900801180003028030005541c40300e602d509151840d6105901111040700200048800070b10320b4106411501d40c420310042e00d03130105540030b0801d1803060800414910403220b0704010701400c40960000c40d5030850b080b40c1c141c1e00c0f841041310300701b0140c8100c1340542d0009100c400344001a1000b40721800f254540042c440e030302c0c2006440c41c9000c54080d50040344000006000103400f820303156015000314200303000c88ac18155140ca0b600c0882d000041c04020503000420040d00382503956001710003504088a440c0c68460401c4c0307441740b5500303100700c8034238403201d00104541206015030500c0148000103107042610003000c0910142c400383c141e030300711f000300e9a90f100004c442a0302c0e075a2512361500c0014140888040010902060303030080d62003540f10384020086a0f078005690b03130540390f1000041801e600c400b00d81515081 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 800998030 1250 800996780 800996797
    0xb0a1b020d030302090f010f020c361501020c1521090312090f0a0b1305010618050a0908090d110604030b0702060703090c150216140307080f1b06 64
    0x101ca1220a05041d410340103003480360b508441508a02203038000550700c040096035035102580010040c00b01c6450f0000c2580b00ca1084c04100103c0701680d506400c880b03070100720b961034000f5104800d122200c450390035170040340e91007070000344047c142d0f07a00001d81c1034407088500d03440000005a0303000103603000340d01301200450305501c0c060303603040200840317460f6084040080ca0001c001c600141d03803a03000041c9000c1701c3e00d0030409000d0100c2c503030b2600c1078403650084c00e8104514910a60f10b000030b000740700c0c00c1e009044e4129028403c4010969030819284041d01881065003410040c002159a080c05c403210600100e6226401000e00c0c0707840b907220341400d07080d1a8405008540042800740041205205034010350035213a40303a4501c50705030112803071b0b100301a00b1540c3c0540c080c8014500c01c5400260004140101c41c0f0300104099495050312042c2c20600c07041401c13451541c62030504100800c0901403280261840d0100701103c0c5e65260940d141030760054841103545036454031008110345100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 800999280 1250 800998030 800998039
    0x1080c0d17091002011d030f030114150307090e090f06011401111f110c0a022215150f0e042304050c130b0619020c120c18010b0a1b02 59
    0x2264400001c1d001b0b1901c409109034140441c07202410392070010040740ca03a13021440c0b2003030650742402c041c5624400160010380e0040640300b4140004091030014500c500090707601c200d001800c3c0003078900e140b00c0160a030000350f44500074400c40c03090301080d1581501d881e2083c2c5c00051406100480b0103404000b0345c2c4805004124a00c900040c0204d000030aa482003281488103840002069800b4400e413080c06590380c101c4079171500140341c01c0300e6100712503002c1000707050103801c0040b011048408011008444842000e410422240c0d040316002124440307041200c1104414003002d80090015180103200c1c1e541c8884100080012520ac507240c40300e508030b403c11500d05490019910302c40304040c11311402d01000d0803001d02c051801784d03009054000d440c04e8100b014981d000c1010800d920580d00a600130200032680c10b442c2c0100340d809040c00e01004000d003003e580c0900154100d80c00c140310818401c140140326a010107802c0310400e941c5840c100108040804122007810303003116009500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 801000530 1250 800999280 800999299
    0x21030306150810080601050102100f060b160302010c05030c0d0e10050415060b040b190c061a1c0f02190b04061d01031506120b030316030801080c0d1709 67
    0x49070b61000406110b0b40d45110312411507612100c00b2a6100e80034810f203030042c1d0040c0107442c251b0005400802e065020468003040c401e44924440c01507400c418000715102c00389414240505909001c0c490962020b030408038550300340711402b904184a48410012100d842c0e10309594144410440101d140039030030403c010b83d003001d141450f1102c0741d007071500c0d18050a08001141c454440c004071021a0103001072280b5215140c0c010410402140b84030790284001907905d0400309046029403000311507000c1484120040320000c015407980c214a00c5100041c190244800061080710342880243d01150f544183c10403070342c02e01e081042ca540150720382c2b03000868001450340c1c2007952007005149414121200070707044e200440031607801402501e110000c03001c0800c451401840c0f050301c2d041031203401054410014011914503440002d0302c0f00c3d600400c40e2030314141039108043e107024005100c007400000404200248022004c424058540350b0181500c1852aa0610484030210300107020ba250 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 801001780 1250 801000530 801000569
    0x40b15030f190b011a190203070510061e0b030106050c100e152a0f1204050c01080f0106021c2703021e01020a120509090f06041521030306 61
    0x40c00810404200c458440301d90011038280100e4440000c4d10b61101300c0c0c86d040030040c120b21050001940d1115040d40030400603180400c005102c0c41c014081d4802000c13511501d882c12038003031004110650f0004018881e02480020700b00c5081380d04407921441c049440d0108110303107034103090924400c802c03100c1c40c29404804104010a503640d03d415070901c0291142c1c5c2c0e0125072000e100d0100d24140d014041c1020500810514401400544006503101400c00c9007484400b149501c0598056034241d00c0030440ca00c0c55a80800c2542c1e10414800c5030744050b51401502a58980d01c1c840364000c08405000c1d140300c0c00e48210350f81d41c20b113002e01100007007010180d60754400c03299050000b60b01a40c5040030206142d404054044900041030780180402c2d03c1e035485034049000c1c03103490350041110402002c0e0465603540003090180424945a078580e050101c00c000898540070340c558041c2d8561103080000315040c815401d0012810750321a0300c0f8840a180441c020034136500a008100020b007007080307 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 801003030 1250 801001780 801001813
    0xf0703060b0a0b130e060411030406050c04080102040605040e011d0103060f0b0a03120e190b030604090515071d0609040f06180c02060f01030b01170c10031e05040b15030f 75
    0x4c08545e100300c1d814100b52509414070056442450758144100c808001050001e0566842640c0c04500f40024500b05600c03054843c0c260380c0709900c1840010004201405100c030010307030050040c4828500c0340d144950f04410080f951405100c00b50100d651200640b40210a542014681400050075040019240c0c982081e25840f441b51000c00900d860319002e166007010341003c07078100b5903c0c83d41414103203440c0c4481d83c00d600003010990050340710005000055820005503070542d03100703104544c151901c99030040c102c0403001600400520344002311103040e258039040711389040040d40c000c51681c505041d40d0b405441c4e294010421440115160400004154000c4400d18101d07401c0c0d804540b640180941036131000c0c000601100501401004a13216a028484452000809850f082428280005d1420303280540c08000700e030719018031110242040704811071b8241800401c00a07810107464603181c0f110000d101034240369a2130340340030240c1d40c100103c01183d40c00800702d4510650b18034568 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 801004280 1250 801003030 801003067
    0x703050406120b030c0607060e0a050a02031203010b030a021b060709060e0607020a050d05070f030308010e0705120c16051f0b01053c0c060103050601080f0703060b0a0b 74
    0x2070010754807a140700002d000500518a4412008000f03242040a45040050031350210f01e089036640d80c1d07808900304070001407000503d074900030400b6082c480064010702d4207064020003900ca481c0001c00060244440403030580340c21031245000161148189800005180c07444007441240e441074400b00039445500c10007810a81d4010b81c0d03030350f0301d003074075401072001902038090029400460103400340100e01700030015140650080c000c030f03890303590744140244881029400680c00180e00c4d20041c40780c0d0301001e04840d0004c0b0b65240c810300d0400c020240400549014155103010708000641d903214090b0200e100312003e80000a0310001007180ae00307020450070b0940ca26008900703054076080d07290700450545218011104a12429143e1107410107030304428400c0c0d03400c007699040300b407080300700c1042c010b8240f8040c8440182511350560510320b2034224144e10103d00b90348820150821172501042410031a0382c080404a8940303a402c0000344005015040440c0031000418019289580606103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 801005530 1250 801004280 801004289
    0xc080304112701030602071113020a17090a02100203251101181403010f0906141005030c0603090102043501091e050c03030a02030c150112170403050307030504 70
    0x100015950b0124518100c0c41c00080d005200e000c1240040010034000d80090500c03d106924041d5085a4070000030074481c2903001e203000340f41c0e021510304040b03500300c40c02030411a00c0384120001403614088155695030382c4c28009004011030b40c40400d00d00e000300306036450007901d85a003c07030031100c540c0c11920b1a00400400d45411520344d540700c1030755000d0071104500d08014010440702a041c0403180c4c41400c050400103800d5940e03041101e0001000340b25499070380d40303e800041080703500070400d0562034401802c2c03817045004910042200d0382e00008d1640b0f04000c240e8800e5283d075100f0445500902070340c2c0c800c02469184408101c190160400404085240300d0001c4482403071440c00c19080340c1344c03100c00400080208845112010f8510f83da40c1c2210b00c140300b1038008245d00d00100f41180c2080020700050790000c03500c8114030340140031502144050040d44072856240440c0c0c0358102d031071050064401c40503580300b0400c030505542210041e642003400c4940c2ca025528000f4100e80c1300303118 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 801006780 1250 801005530 801005539
    0x31305070b0c03040630020d0b03071809020103060e04030e1302040e1915060e0a05040203040203030306010e0a1e090501050102030702130f15120b0c1201090c0c08030411 75
    0x800c041c1c6a480640c1d20484465006608041c10000155403204004845444040000e1481440308040c8200c0b045802e4030904090f840d0455605500180d50005003400d00c20f4000030340078843d2010780903551611005440780030070f0801c00350005900404143e0408010540340308100418180c018082420582c016a0a103120601880c850001c0340924040d06040d032983c000450501c107030b003900b443c98de00320b80e0100103942030810b0395030000000c43d40e2120380800d1540c6150708003440d00011500040c0340c141d50952031071038198002900c0c4d102c0204103d042c40151402c200c0380792600742c903540c060321246080c0700e5030350041c009002c0c10101038030a403036920342004004511940b0201c291084940d01821400c035002a602d45e1401401c61440c0e4400b01c143c3c0d80e0103040200f201010781600a0121603d9240048464201030000000081114155600030480890b100007002c1c071690441d086d5590001d4405074076501216081c2a40740054040d000110a00c4180012422204043d510454 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 801008030 1250 801006780 801006793
    0x10e12010603021906020d050333041505011b051603060f0c09080a170f310501390305090102010e0c031e1e1c081005010e15031305 58
    0x2c148904c525418002c0c100141c1150000d2140f85004602558018141101d4003111212400d580806400c03144140c5c40c04404122001400341418418a07410100944007480a1070a080000c6c0100c0810295102d450511450540030b00101344180956210401001581c150b503d0604901a00d00300184c402c50a1406804060f400d020381641d10880304110042c000740b01241e01d40e44482413002507040219401008030340032801e0040000c0c410080c04011a440744150860038660345894412215003803e04200709108507030704004070f142103005800354114000000e6640d090305180d03690086a501c1101c1c42039204058010015003031507102a40208000200d4492590f03540410144058268201d244001c42076040107210310018542002140c092000010103114800701c90580840c0a0300a50103091443c0396001d441141c40c52140b50140d000e091601d80d0003225000c3e84141d506000b09d80b03042942c01d80340c190400440c808014041030f05d9250440f0f49041042e031220b070440742d900929 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 801009280 1250 801008030 801008059
    0x20d110705010e0108060112110a020f03040b070f0807050312010510020d0e27070903051213180917030a180b15180405070513200306010e1201060302 66
    0x39000c044540503900c1d05007859800e40159112030340944441e0421040c50b05950f42c5403118050940001281040c850752107141c0c1e0700c0282018401248035241e038004100410064008100743c0d0810b030b030081c2c080207441a140c6460741c07840c0310364200100303240400310b8550740c000e01300010380d4101da506640131040041d150800f2611101c40c402c0b41c01c041000c031034072031226003040b81c0038900400703034806009030b0b001800700c0d010300d40721048440340001841d0000038810070805005003d600603007a030220f400d00345020004d00300c40003140290900c1d28001c81810b141320a860700712a4040750815080400348810340c540000036442215454040c508001c1c15083c17001070055090300f5a40c110000ca95640c0303e48000c1c4650412800f003950748008038100e210300f11107401140c01d00841c41007000f03000309490001440003800c058000d1102d02c03031401608448400328100e0340e994075501413141c01d5a80c0e4642c801a250041900b40180e04408100c1c400c19222005500c96415a40215212071140041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 801010530 1250 801009280 801009283
    0x912020109050d0513030b0c030a06150804032105070e120a020f040506060f0c0a11011b1203020f040e0f0c0310090e1218130e0c010e06040503030406020d11 69
    0x1040401807180e80f0107040c01040601c100b0103050314400a40840810b01c2d920303141c0c3d19121205540740b43d10180d000003840f203c504203104100c004c0c01052840b85a052600d43d0103881c0450082000d01070259200e0002c0c003034608544040d881c2d0826003400c20650800750b00003040e940440d94000d00032200d071400b45c5c01d45400010300030321050b0b004180140d00000311062002801000e000035400890502c080c4000d01c02d0180503000741c100220040c42021020305054001d4031140c04141d050206c600d48030b545104281c00900e82c40c0d03810100b443d20380c18464008030000e12840040c022503800c042408901c3c03940c055038540c040c000104040070035442c1c084581c4010f00c4240d581e1003880c041c4117400c03c56040b29810451310a01c40c00140c4000700690690710040e64011419404803a4102c40302c0c0700c1c5072600d60b51125401724a0a000c0040310352003102280c3c0d41070021001410310080c8149952142c0e2410100c50240c04068156904c1c0d03980c1d07000107541d60b9045105078020a01e41c49106081510 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 801011780 1250 801010530 801010541
    0x3090307061b020d02030a060c1101060b040e060f0a15030204080106090203010501093b0402030f0a03020c04090213020c010e070b0f03130305090339031203091006080109120201 78
    0xe0b950380b01c400100c0c1d942e08200c07000801c2d8404980500491660707801207a52440b412100f82c80544030344590201001001c1d00310380540e048424203031002c1c807042c84004094040f41da0320900a4a010180c0b89050380020f940c0c882580c80343c10040540d440d01241c544e8550007400849007030400910034640c84d69a280143c0c0002d010340c80c002400150300300101100700190a132180c075411800b0000169050154004a0701c019039540c1c034022140500c82181800c1041d001500c840c0401f0380524041903600949400c0d81c0c110451055443d01400c0c0155510b01c04181070764543c0440855480054880322406480c81000c1214a8002c00d100000c41c48043c00848400c10071101c02c0618659414428440b924041d410a0b41044010b1113200c141d51010000940f00d0404450751628210b003062410004511034441100c0d041c064200f034203503d03140080d003411a940401125078890b0b42e028140d03031812242c1d49103581880c2c03d15000149064040d03000121030350240110714030318845910306900361172 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 801013030 1250 801011780 801011807
    0x9051f020a020106171507110a06021b0c010903140316121404030b0a111c1a01090b0301030b04050f15062403180c0402070602090a17071802070605090309030706 71
    0x4001c0c1104c0c942031b5101c00381040c1d0003070b814105203012100c1c0e41a1607190400c042d0044a440d540020004c10707031000b03007030142d0a204442c4002c2408958900008102022034480100802c02568501c50303050000d1041e98024540400201e2840c0040d04152150440c028030000103c0c64511050500100710303000c94050380d40100e0b81c841140c40d0311040d070000307100908824050000c04d1088154541c03050142d03020070002e6010100d0101c20391902e80a2600600303014a041c860f02000c20040700d40304a0544c2c2c1140c5d08100994026a142c1c24800e0805511082c3d0720a1405003004d58a844030040c59128050882500c2d11341a0540c220070808103e014042018080c44003400010702c40f8a0900380d604590045000b504c00c10f010005c00f1800366000350340c00312403452300424400080d040040b0741d10000c0c0315100444003940640300c00705072501054064105072807050a201e515445490701120301c4580d0002c07082209142281c0082c0d01c0e80c0161048170f201e400380300000140300c0d10a541480904 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 801014280 1250 801013030 801013033
    0x31008010b01051c0917030f010609060c030309020301060b0424080f0f0601120c05041a0708031603090503160b310501110a0f020d03180609051f020a02010617 70
    0x3180700618030113000c6042c0ca42c048a40e01c40003480d000038035684440d00e4101d50320081e10380320700f0507180780794070014144c100d83c3c10404088070411005a12003104c101280d00741c24009100d10050010030301509654200841c11034000800040800e00070001d03c1080d002e104600150a441c3d81d821541c100301034440b001d09403003000205007121414680c003074016030141081150f00050103101c1082c0c5111144100205d00080b43c10031100e411485c101ca40386600009141c9000515558008240000b80c2034140c0100c84030005020140250310040b0415000b000701d0b07881d20103140b00103d1603150010100c4000c03072140d010485546000100005a19200d625100483c8101d603000508101c00d50042c1d03541d6403510980141c030f10303001c1c00400301c0190030350b80d28075210041e1202034a0074500c1040241054a4140c174003030170b802c00d0031807d00c3c1c04e948258085039610003820300c140b0b40410710740d0040d00c4903110180262441c0300e0b58010407000c13050740c00a20103540c0ea01075040306011400c4d10072406 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 801015530 1250 801014280 801014287
    0x250e010b09150306030118031805030a080a03020c030403050102043510110f0c0d2d08040309090c0804020a090902010c020f06070c0f2306091e15031008010b0105 71
    0x490b08000245a03c0714016000103030f008000e085403200c0da4440364080d00440d091210ba400201000c41510b40030b00b0040d0300414894402c1d44c0c4285862290b88030107010940e01103024840300c20240b08907401541c02000940d215601d9070460182c008280103884518550b128118103070300e01e04003a00d403078030410300302812031156082b0550029200302015840a11030030460715200c03103100805004012121001001642c404942c0501660009011480d400d0400c1c2d8138202e11080140c80b8840c4100b0720328082801d0780b56031400703440c117540d940c11014510382417005a0000035803008100d84158000c0b0340444040340c1d244080e0702101c040200290002d1070112800d00541004904403050400c0500000e00d00031302910b81009107003664000c807008c840d21000801880300d030081d06a00ba0b51224040d0303020303070506900140ca20300c1521241ca010f640c021440b81c985084151590a0403c00944200620005803074140307070030f520440d94064220f006040c0820321000c148075081d0f0414041e100d0628 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 801016780 1250 801015530 801015559
    0x108011a0906060912030405040204230108090a060c0504180f0b190506030411040c0f031b081512031b1e070b0f1303030c020f04050702060a0e250e010b09 68
    0x3102c80c0c0000c0407540b1b4072040000140c03988407032004bc8000e016222032142207030000810710a0380300c640e2070340504101c0540280031101401144600306a5807200000038000c4e1401d100781d03030382c2c0610342c0555044180004a01c400004e00c0d0401c20688036004010040c2107041420005041c0c00f00614007104841050103001a042c072400440e00a4080d204c03900401001800041c02d880f010b696120000342488011968990140034141d0103145200802c14041072010300280032440c001c03c01d410741e083c079040d00d1806490301d8a0388203c010302d00342600c2d0349102d42c00040c4c0410f040411140c3c018414059054040348401403d03422034100140501034581c074204403c455500000c454210381c04081080300c02c4002080da0700301c000c503c41d464a250910b4180100130807140002d0b1114040c908101c200124140c1c0403c0055008180d290b000a00000c14407003185000b090181d45a100400d45000c0d0400392a0200c800e401c66030b1032900c8009a1317881d503070101000d000316110310380c00c026121510361 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 801018030 1250 801016780 801016789
    0x1211b091d19020d09020307030f170c0a030c15050421170109150f060c0c170601090e030c1b030d020f0604080918190b01030e060c07050c090108011a09060609 70
    0x213002034622101090030340094000a08100281d401103802070701141140b002c21003a496007800d0071500025060410500415131501c82030040c07002410404200e90440c1008002541303a040342d080540c04000c285010719022120350b20072107054401d180c10f41d0120741c40d80d20a41888007a102d450180c0c0605900e00804440070304071000100c0c502140c221404568114401c07441d0005089070b607100540c50100c0e041068040f281600505450055507041860410300000d04c035044540c03034440001c483d042086014150302491000007000e0203803c130602e60311000580b4030725078058104c045d241c510005150507603031b8032042440080503800c0400010045078041d03001c4c020080c0c01804080301e103012865101300d400400c5440140b00740c23451042c4001c030003083c89002e0b001182070800b00900310901c00000e548041c001c1a680150740c0004881e010020103100081445a02803ca0100e550315140600d000c0c01610852010000444c1031040ba00e2428000650040350040c0440d4a0000301c00c0500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 801019280 1250 801018030 801018037
    0x121b051b03030910210c051801050f12010e090a050d0f030207060507080a0f06050f0409080c0f0607030c020c1c230d0314040201211b091d1902 63
    0x35034980814800601c45440384103415080d8000760f6070712840074030054104070074015080f696541e42e0745042490f0455941103002c4400801101d141c0e60310ba903003000c00494091180a0212546032000b10305400201090700c402d605813030003a80c203e403070745d80c4800d80e1954601d00d1001c060182c2d40b000e1109542580074180c1404a00d80c2031801500e0b00080343c40c1e1500b51361090324001c0005114900708000d4940702e1181038209602c885040c0003440c5000005104030305106100c074411580e40d00d0038420040d454048685921505083e10341a03418641c1240d241c840480307601020904001d08880103500c08030304200c0c42c803001004200c020303c2540700c40e0308101c0d49510071a5401001c180220101000240181d0401c0c601801003808581084004041d500100701c002c900c541840c0c21b000050782c0003003217241120b16500c503d010030b40001c04640b000e44804480c500300034508107403224000c2d070300152886c291000c07151600090360014240700d0f01b00c40203c9004120b007087d03001501200d01980c005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 801020530 1250 801019280 801019333
    0x3150901021201261b06160c0303052710050a020c0909030c150f01061b06232802032a03010801060e010f05010c0816121b05 55
    0x1810490701c1019415411001c0c3c00401008121650390707507581085051100440c041d244c0078107103084000004174001907501c81c110744142c0001c500303071480c111404103800401d90801c0c40b81e07200564070b0070050800c2d400400000f80c4c4031403260b50010100b40071440041e0441d00030780702d0788500360f541d581194143c104840c02011400340075280b454958032105500d000d041c00e00091560755225101d118039101189204d4400703c52084104501545140300e554110340c954104042141181e09640742d0849544c0c2c8000c18540c5850051000c00e01040c107503000b211b40403001d540c1c032a104c20300e6060b840d02c4985c1c110035041001c00081e5a5101580c0c0140d0b810803600e100186a490b400710300030344140f005200e0b8443d10923020004009010b002d006920041944061400c0607505081c4e8904107440d46d40515418065224105000c2208401c22680d00960165019464940c1407030490100340429500d00b00080c18001c60b84e02d19400701c02031402043d80701009003010125241d074000e050302103000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 801021780 1250 801020530 801020533
    0x70806190f02072103270f0c08070f090203090a03030e0708010f090c0609061220040603020711060a051e07020d0812010e0105060d0203090721051b031509 68
    0xe601900304981c00548080c501c18030035901c9516800f90a494800c804c0c5080d581054107042814141030b040f200e00d80540768040310b50103944010390901459210250f200103103408214000040c0a800100d81031043c0c48800741c40d000116902e00441050b8041569501e4903a00080445e100090095001c0440200708030241c40ca001c0e03a540c0802d0854400034401460240c941000342c0c108040c1e07456240c0903003102e041a54009041c11340040c000900c00c0200e2900507610103c1d0380d1008200340f0040000b1880b80d003c242d8454941c44d00030003079008203000b11281103224006100303030315150096424001c0a40c0c1c9050900440c1c0c0f0210743c194600340c48526184000300044c1c03015880300c2d222400110702400005903070311103203100d1034030b81501680030107000e0701008010300260b600c80701141c81000c4d04450240c0c8945454950504100c0d40d80d0000f040e40741001520021190750502c00d001060041d003e444c8a00b601024485809140c00617a40e4940c0119000e141421740402e640c41d0030451050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 801023030 1250 801021780 801021791
    0x10204210201020c030714010e040c0c0b0a1803090504051024030e03040b070b01090605061206040b0901030311010c0e0f04200408011e0c0f1110061e0807080619 71
    0x2000b090500a290704994502c0002547c040b4180d60030030b180085a40007079804001d0048407030740081003c842003100030402200c2c07001203901c00c142ca4100a8440e2a4000414008455403034090880491881503502507424074000400d02000c500016086680c45c1071050214200c0120080c40f12407500c0d150020b041d40c81544807128003003040030304041d10342006003680d01d24680c10b01d000325010513071180c02400c0c00d2032414441c54441c034041d41c23106000e14010781035507110300000030040d10a041000d500454a08000030516500007a801c0014003150001c000140c1003040450349501c2d081c6110782c00c00340070204c03003169007407640c001c00c54210081c0751001d00342400b920001c850361041d480402241e4517940000b001d10028509032002450111003000038a0720408090500032500c50f00400b84154102200c026220034401c4449901191a003080900c0d00c6444101c2540b08581c0f00d0b1480711440d05011030088400600c48d030658103404002c058958440e0346143d41d005410158024454461 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 801024280 1250 801023030 801023053
    0x1020102040902030c090109050306090a1e02030f010912030b06073513090b130b060f0c0609010c0207320a0e1b0405060f2a0a0506060301020421020102 67
    0x80c07010350b00030007540c106255031b22185030004103c3c030119000580729402213400d0040440c40080d081e112554045e082285d440c6990300c40f01c0d594904150041d4140c0134919064078000c1040d40700c460024404c850884410308002c408404980344c280c3c038036803c5001040050f01040c1013070f5448402c003c03c0030600110206804604058042d83d01c8003085804010030b941c0c03224500e860440c4040c00c04040c04202102112000230009030200c840c8032000c03580c440030040242c40d41e1040350300c16502da99019948016000c0d0306980c1e080208c80d542080d501c5c2c495030311040e91010030b0500032a642c0b140d80120040c50001c1c00c40420108429208010580100b00c4016441d010780c88001002600c0b80d1800905d458120071a203c40040d581126025041101340300550300c5909035400c0e4503c10014079141c050105000052000004610f070481e01d1003040859134490008910388424441c0b01074401d0794030740d071007031500340d005500a21100915a54440005070030004092206900503c11180d010145 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 801025530 1250 801024280 801024299
    0xa081015050304110a0b071401051003060209040b0411180a03080306190e07090e060301091e031404030506061005030601020d0f0509040e0106083a050f030a09140c030c09060102010204 81
    0x645d00840c0346c1240483c180040c000c000340800c1d064808400203100c2881c09010304102501c031404010001640811081020345072540f08140b80c00700940200403941d40d104042d007558001001502965208010002030384c00c00c0020b03807088a500241443c250f0f02da810030004910b00000968200e481210400101e05190701945806048292541e8460608099005020400042055000341e041c01105070020f91008922a49000c0c501c15403015041c640c5411998402c000380c06404005c000324001c820b1010108003140a00411240041c03014081d0304280c1c1d0030700040340c203507015030000344403042418000c0000e14810301e410714105140c603020100060880b801f025010110340c0d52100c1c2405a44010009e051700702285411072002840418901c9603540140d01b0b8815a00b0b80a6850102d103501450a651008034295611a286c3c40e2400010005100343c640945281e141d40c13a02220304039020400b02c1500b14050041d000300160b40c0705002c581c000180c0103504542d420080000d10070300c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 801026780 1250 801025530 801025549
    0x50304170f12130b0406020315090406020a0305061509061606140405010e070506040312021c0305070206010609080604031d032b03020408071701020910050a08101505030411 76
    0x2a203901007038031142d4004041d020020024a0303000c841902e00a80b40219404c0b008207035105501410161362665402c8201c806d034240c0d500d50540000d200800c0c40100901900907043c03c601c541c1c2d040116507582c1d401c00c07415000350030320030503101010007810109007004c0c0024a20503880030f010303501110440d0b070350713400b11050201d214140791158814401044420300034030326082d40c400e0090150906000020740c80e0b2003944001824040500041e4104070300138070510740040c61a054000302070020030406009804112040320042c0920300010503114001d07000e0034242d81c103001c000e00903541e60303030790554801c90354403112244440f000c0e81d070841d01c5e0b4040210603010b03080880000030440b2009152991034060900000c1410f0041c00180403660700040c0500c111200180258840c1200700b410600a1040c00030481d081603d10300c003601c50641000040400c80100c0e1380b41803440c0d580c0304004050036500c5c001c00040c2d452604000456500c00c5001d5a001070180080d20030340340240000540d0801d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 801028030 1250 801026780 801026797
    0x70506120f070503091209042409050703021e0a022508122d0c101d0f0d0f11030304050c1c212105061302180105030417 53
    0x5000010403410740190080240c2000840c24010b0460800d4082c42d130b200c80b020341e5040701400f03010904c0e03039540da243c2d00180c21507006001140d4002d910100300507400340550007071450003401c101c00300e0f0035588030b84200c900c00700c181103004181104031000001c181d84400d40d450214816000c3c80c1b0b401d000048001645030380d02c00d84a010442c0380000742411303c49039140e400785d91f00f400d1103621550103150306a0b00b403900c451500c0c0200c80b00c1420b52009940a00003000d101885060007800d0309081943c0601e075543d481d83ea4040ca50b410250500303176100000c06040400343c2040d030b40350034101c1c010303018010540018144210f00ca41080095031039a042100c00b40c40943c08024540e500d03017071402454401001500019a0010881c0c0340c0500200148122040101031030700120001e80c8640070b40165103004851001c030b124203000c5408064030b8280e403903031300ca541040c000c9041c80d007561082700c640b0f4407a01c503d105100301100064566400003001941c080070001221503884040200401c03400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 801029280 1250 801028030 801028057
    0x1306030606030e06130809010c0f050c04050f130803060a030f0804030c060c12080c0702060721091a0702041107050a0606051002100c0302040f0b0d0c08060603011403070506 76
    0x11031070000010190b801c1500b40c46030542007501880049220807168095440c3c220b25260750704c1d405900103c442003480240078120300b60340b4204004014001c14043d442d0042201e040c080d07900e0b00c10031007500341e0702030f501100c01c0000d140d5910700003642c050280d984071900034201c400c42907491b121b03440b03803110700541202c04180c001028410082d030030f000000605900c2c0740c0f4203000f21040d514030740188030140c0f441c0148003255000964075078509003155440e41d805440551103045502d011248400c5000c48030459803841341c41051424484c426100455074100f8900c43c900410b5480e000c80c69111240a0360016103801294150b016210f0003041d0381441000140414420345c00d004c000c940407a00000d00c180912061584495800991405486440030380050b020400c50b1050780244680c0e40300c0b0481ca0300e480c900247c04840d80c030203001c603810641800d020742c644d24041110110302c103d03191079010a06000500030402c891480d8030000714060f003104c2380f032911003000840681100c00c090001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 801030530 1250 801029280 801029291
    0x51917070513170d03050a0e03210c042105010b040e010203060901050303030c12150306010305030a1b0b0c180a12050c040b102601090617060405060112080f030c07020328060e0102130603 82
    0x490403050009030b400100840742f00d040c2801c201550070207202619042c0b001c0c0c0e200490480a00070298044005000028410401300780261081ca01030341045030340d50312401d11341c2c000151609000c01140e00c10307607200746042e2912804208c10b650101000e805514075100b002601519a201000032501850080000359200c02c1e01c1100240041d0440c0c03607401c0c201c00b99480d0344000034030510030036400005040030300d510349061190b0282d0505c55070610301c0c2d224441d02c00019000d200301001415641c0580240c2d842d0740d801d041800251145c0c604d003180c000c00c0c02c1903104d141c41d1241652103120142078179896588942c040420329440d0081e0812200755941d20030400084040072440700000344c1c0b06001d030115141584900751500414414800c26055400660b810443c00608552440200c0740c0300c5134480c00e14a6145d111b42d00000c4007203019114501c0d400710001400d1500d00241002e0750040300f01c3e40718039910000a06440340b9031004540d001d2007900700c441000d280f900041d0840340c0e0000b44 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 801031780 1250 801030530 801030577
    0x29040b0313140a0206030f07050705010f0c030c0809060402010e010c120f0e01030c17060d0b09010f0b09160e1c11090a0c051917070513170d03050a0e03 67
    0x40181502400c28540c1d003c4424900180c5841040c0c90740f2010040d240e04865640903001e4034180318244006000d54a4043c903802c00da0015805441010455034081041e0651480b080c0e0740580b055481e040c140d404080040c005600c6041704034000101850440c4480c0c146544035207507911001d04000214070b0800340400d503150700266440c950002480c09101c1603940d07150181583c00c88281004c42c0d40f41840000f4800c0d112098880c0307009030700007450701c0180340c02100b040c000c2807440c41090080d420012415000e1402ca448e8600034001804414a4141c80303400c02d0300c00002c280841604540080c14000c4401caa10400621482c0541440c2c0c0c0d91103001010060113401c0289018020f9141ca0060301b2429881360a0f1000341c403040c521401107040d01107043d645207050079404c4098003c0f410402174071a0740440907000c106215081c49107840e8407111980c1c1641c00003118103007694032040821405901c00e4200340c0d001140b0700c0c40000c4401403081e006065038003212424194a0b0914103885 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 801033030 1250 801031780 801031793
    0x207021302030705090d030e030a060621020a0605130b1b1c09030b1305011d0f030f090d14030f0702120c060304030c050c041503061529040b0313 64
    0x203048101514045103545045032000d4000d024408003079024904505c3e03020105806080340d081e40c8200102222030042082c500b110107000e66004a0040c0d9400305026081e0400c3c01041c06030b42540204540307002400e004044510380c00c00c8034600f252000071000041c02c10084002002c030124011503d100001000e05032903e040081410110300756094030003505820b034010304003c1507a80c003400071465901c1da222400f50700e400003400a00503510709101c01c110043c0700703000d55500d00d030783c3d5055130781e580ba40091060301c0f4040c4200005505a04001d05c4010b843e00821000c005480b8111582141c0302c0c2040c09403458200001d4912107503800103489081d441e0801c0c149600860b4040100303030140d11100880c80c0d90002400080500c41c0140003482008001e0149200307000d80500100109000c4c041107896540c01c80c4800d8070100d14240711300750201400081e21099845400e40b0b102c10400b0a01c00542c0b1f407c0c0c05482074010003050001148440b005070003035011f10f024003107440e10006142003d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 801034280 1250 801033030 801033049
    0x303201c1706180a0b060c030408070503160e07200a0804050a0e04050304030f030215100e0a0e0c011407020d0f050601050618040b0103140f0106020d09080c0d170c01020702 76
    0x103103d20411076a06224003034407048107601c5101102c0204403001d259000c10710314007803803000348071b140000300c1c0114140c04001000300840302308034111460550106501c0c0b10281a5000714401d09190800248407940200301c48014450391010000d125504011181d041030070110040b12503180001d804c100d1860180c85010242c661140380c1e82007400c02d07070b54031662845a0f100042c10001d4074a1001d05040c02846520b2483c0803221040030f03d4540b010b0481009802805004c0c0c0072a1000007180b0301c1183c03072041c40103082842c4000c006903043d80c001907070502120740d96003075028400c000c01d01c0161a00603c01281038400c0c100300d8401455458403e06140b0140c0003e40a10428400d58180d80305078a510001484192000250700e40710f500128080c00d180b954141580895600f41b00b40190745500343c904890300c2d542aa1410603c100342283c40f580188100c118079804031803a14818545404441c00c0107104001c1c7e00c80c40e038184400303140b25403c045000e0301540d501160407029428941c01c40c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 801035530 1250 801034280 801034291
    0x90717040305041d01150513030204091b060807020610050907080603030f0c01020301051c05122206020a030201060e06032d07030f120201020702090a0e250303090f0303201c17 77
    0x124200102811948e4545280e03210192089445182040c10b01c06101034004040d0403840c00a11034503101c1c070000c1e00741c200030b96031a80144038500010380100c5010451005840300140040b15a8030343c003d0071501d446014040a5160008222002101c20148000c3c6548000d100015840f07600d060104100e442d000842003000398810310001c40080c10121703035003201018000b41203488022405542034140c1c010b4005032158282c4500c04910b00ba0002076210006109034000c0c8a00303915844043c001c401d01340c442d650507500c000c600010410311100d114000c181400307512aa1101181820740c50240c0740ea02c180c444003601c0c0f140b0824082ca03000303400c581007140d00003986428400d0b40407900441c40107100d174809980d100841c1c0021402072000a00082c00c0b040f403000c8003503510b80200e500500611048021544071080083d50440d1901d446080f00c2d0140c5070785549041049903c0081c074242caa1480941c06481b00600b500300010425a2541c001c90743ca8000400c8500c24096040304003034003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 801036780 1250 801035530 801035537
    0x131e0b030f2b030e03070c090f0e0c010507021903030f1805060f0c01090204090b090d03060b070605071b03021b0402071518060e0a02030c090717040305041d0115 71
    0xe40340440c9585903058859614082d002191903945072000314010040e800b00c6651a0000007000c20030300048640302c200380e6a028100300040c100c61119801100e03c04441002c0b281c001d0b4005080c1580680040e01c1020b0001d000c00b400804040c071191803540554004901203525002041000f541c80314001c0484400e94205440540c1800c0000b14107020b0490703104910f56000982c0700704044290007107001580e000d0720503c8010010300d04001100320440344129148101c036401c003100782c4240a50307401ca420066069103446030644814000c0c10004241c0c1040c003a04004a01650b0320200c044124140664040c11030600c4000c0380b0040b07003001d0544d4510450041c00303480c01140d4011750030700c03541c2d9141d600001d0340c20b4220000078043d134072090b01909051038007001074160031000c940000401e100300c040c0c47c1104c0e01c0204114a146c000c1c1d42e96800030301507901c0582d40b0040852051781060003410001d040990750007200c8000100c0d5907180354008400e500400080000d880ca85104042509 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 801038030 1250 801036780 801036793
    0x40b090f1203042109060e030c012109080703020a06050615090d03090f17071d010902161707050615100302090f04090515060618131e0b030f 62
    0x10032180d51550701815100c80c40c00d00201240802c00810110b07840720625030b200d8032003030500e04c20103841c000c220b11504010825031200c00d01c1500d4045407650700c0d010144c5a807072554030800300e210130240543c00401d0400369900740c008049000d41c005031480ba42329034000c0900d25403a240c0030301030750b101030b010601038540c601c1d0a604c0d410162058030000380e0290342c50b00381d45015040499000406501c1688880c50b9070101240c0680d04400411049404004075184523540d43c0b0301c40706c0d091402840d80c4c81c07000c6070f50043c40b14801640042c000b0003d40b45a480b010b04c0191903108482540350008519424001694810003500b482459400011501c074007859a105c54085061640c3c40760031171b000c156002800011550700d03501402c502c0427001e00708201030140c9107071042e51a40200000d00c034001d2414001483d51a0120071121003d00c40c01081402425490601114807420703540e814003951540724444c60341d44908a2034045a441c800c010414000030814942801c0c15545544113640080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 801039280 1250 801038030 801038053
    0xa0218150301051e151504030209010b03010501050708130503060a0501090f11030a0b120d031e180303020901020a0215180303121314060403030c030b03030711090606041d040b09 78
    0x1003d020310031382030031143c082e680d070310307020320280c01c4481d88150b9006e140c03038403401078081a420141c001d032813003500c1c5c5800b1039072295030095060109106043c0051010803014000030403460140880c40c1e07280d90b42d400e91a4036000040e09007201142c1a040c42d0780e46038010025442d290286841c0a580c50408100d8464a1642d60b1298031008041442250725400070104075110281490b2070f89040e0025036655000e1250014080d2000e200040030070296649249114502d038492044100810036031000c0d052020760302035020390803810049041d40074644141e8007584912200d0252280d02c4510207658250320300e86040661104540d09010786c1c02488142c100d21840c8400c01d0f0044c2803c0300f08411641545454000012541140c0c1440d000b01c0f0103110406070503030000c441080642c0c80038000c8032108018190360740903c60010340804601c4440c00110f05108600e039401c1100038100d146000c0c1c84404840000300c541c07400e81d01c00350055040000344002c80d100c80d80c22030102c002500c0c120b07094 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 801040530 1250 801039280 801039301
    0x402040c0509010e091b03041a06010807020606040906020c100905100c120b030f0f1c0c0f030e0a0803070b0a0c09030b010b030a090606170d0807020d08090a021815030105 75
    0x130000d103a0103000144040746406600074110709507003000441440c3e981c41d191603e0384c8800c00348403410755500b408402203400c540c096005070b44104c80f20360003842c003986c5880c00c110107840c00101c1035881d20760230403400ca0001000e204841441100e041301140750421880c0c51407038a00b415444030b40c9245030091b5580c98a6118040c03074024442d030100441c409100c100040c0c241940c50241d00b21512400d6032030304000d0310201b0501e00f03500d95100382e1662480503281c188d0320328000b164014440324a11024000007030203002030481c0c1410141840c1c45441d00c030f90b011881c42c2c1c0312030710540d41418460100f000046c56030003685044401407505d0030100345944c1e140200035034180070309a128440070001030b80c02f0b0f01da44d001200242c3c02900034007919644481c1000c801001981104050280d2403201031070354090002c0b02c0c01b0717a507a43e000b0100100c20800c111403900000d001c80f569805080041000f580d02d01d0f05405415910143c080720074100341010700072142004201d94001d90601003008800d40e034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 801041780 1250 801040530 801040547
    0x30c072d0b0c0c0d0c05030c06040318061b0f05011e0f0b0307120201140702060d0b01021902011e0203090621070c0506060f12150121023d080402040c050901 69
    0x10b045c05810803d8601c0e020b420341c01506401c4110b445010104001c1c0f41e407040307002e0100d035003c07039040d14016129101200c15400030702ca140c2070324108a40010000304210342c001100c41c0544000200451080c600c450580c00740020350000e0343e203401062145161074411f24146030022001002824580024020110301c1844003a05000000d007681d0b500a82d040200c604096009000c41d5031425400700850042415881c05130052050600d02d6145240c590400c0018036016100d41c542e0071002c90075050071001c09612142180414070400043e511024064106942c2c02c0b6082d800c408604901028212402407200c010420302d45240d6001c42d5001c910345030044410f44185490540700c02c041244100c2c00a4030441511401401c0100141e01c55103040c1038824501102d05a0180850500404415510f0103540120000b2030307501c0f80c86080d82030741c4840007aa4241200301d1140e002c0305510040c046c20400100310054100807c600c0c2610030032440c09660b00b0054105030410000038034204 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 801043030 1250 801041780 801041803
    0xb0a0909111909020a0504150c0b190e0303090c1c030c0323130e28051305060412090608010b1209010609180212030f030c072d0b0c0c 59
    0x4204402c4007002442103508107001d40281da0056544100c0d850006013958000c1c400d034242140407603031070030041b48640001c0402c0c0341c010003d400d450301e828000c0c940300c1c4a10250207102c01e03514429000c0214051006d140700e029001d02500502c007440c0140007178854010003400600e500e0412810001c3d400c02507103080550145001843c044020344841c6480210740c0c03080180900100d007070101d10003403e03840380a503030707000b0041d0f011a00c41003000070200198145450642e260051800c042c3c2101350300c041e5000302044d604030b1814909072501d85c10104261002d480802c1c07442d00008049800408420041030180b40c500b0700c40d803401c44002c1007402020903184008100354040f0b95086425046800504609041007218440e40c0e4800c550104261001302e0154089424100045070301100b03540424045026036413a45e50b601721242040d40c06240b0482c0c0500c2c62004001d01e00c1ca092200d1070808a00e031415581041c3d041c03c05001d41100140107084c0e000082012460390074020900c6131080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 801044280 1250 801043030 801043039
    0xe0613030e04110f1903020c0c24030907030308010e040807060b03120301270204030302030301151e08060102100c1407060905030a030b0109090b030a170912010b0a090911 75
    0x1404030700090042c2c102100740308081c0d2008214455010815402070070708000f128054520a00d000c2e106030181e0113650303481c01703082c3c0040300d002c0082c0c1030445190701c28400c01c02810f0940e140f04010a030ba59041035070b102202da0b22a00040c8101504a400c460241109001820040c6001e0b520b50440e4419400002c062039151100d420803034030108001400080030071105a2a9a11545076030f608403034609c0d5155440c2425500302c0f00340d0721107200f100d0549405501541c1780d60300b00103c00040d0700f48150070804200c00340d5034000313388103645510900d94102c0d6596104c40e040240009290a4400e17240c00079092130070f444160095040030802d124071200c12140c5460b207903141085401401852005001e902001591100240c0e1680c482c080700c802c00d80703802c0040c94a4000c02000c4440107150145c160307100300d8001000c02d010703140340c0c0025031403807000e189403a140390040307401000c440b46001c50030f079160191980c246c0360501880c0044c0206c01c204101c2161740e500c4144481b0748000003180034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 801045530 1250 801044280 801044297
    0x3012907050d030c021207050d030e0f0706170708060f131d01060503060f1b0708160b01030c0503010c0509102a02040c080906061e030a0c08010e061303 67
    0x6804941058456103504281500d518034803240010b80a020400c0c1c40c00018001c0741030001d440d42c14041940ca680790403e0003012188480d00096000300049291030001c0d100c0c2200c984800d10040000c040500b030140e84448902d000b2004500816601400000601081c6410424261140c175000e40d14a1000c849148001c03180580308001003c0340b0115114001d20001503000107041500608202c807410b0b011104c40e940c1e03030304401001c001d082c1c50b0002d2400940b080140b0b21101040a00490b60041130040d280110801c03021139016291401240e02e107041034010014031141d000707264000e21007517000b8009039030007500040a510490007540d00c1106484c40e8516001d02c00d000c190141000d0b00400f1003442140840320030102c8104908038071503030506046030380e41c0e4403800201e030080304038100401e82916010700f0010b044511001c0350b840f4200700b0301020010340d81003101d40e00507030180b00c1c0d44c1c1e40c1504082029003982c10790300e03410301d46610180a000c0301445003d540b15006825140c02e451 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 801046780 1250 801045530 801045599
    0x50a020c09100902070f0c080c09162d0207060e03101503060501030b0a0c03060609170a170a140f160804090c050c06070e030601090f0b06041d0106050301 68
    0x98980c1203403c0701d01c2441c80420000d042203c09801080c43e04e01848114000c166103002d003a5940c403031240502d4000c407010000c50802e8075490b03000f5a0303205950400340c2c611904100003048409410418003110703414039240481464050119001415091411102000d4044d01203aa1240c0c0e4070300d80007415544c0d00b0054214503240ea000005503900a0007800306582d40d04015280302c80948100c002c0510389081e1108050003031103000101d91050f26034268040c6020301ca82a06c002201c41e18025000d402032000009011036840619149140082921107448080c000c003070071200f074210250a80d0401070190841002010b550500d40d5400b0620000c140510705168140207562006c0c40503424040401601074200300581100750401086400c039039508507049800344600700f03405403d90400c038014403110226800101000c0e140c2d01d004a141c8c08080301003502c0740c0c1700b6030210038103080b58000e04c08241d88915116004040310b1074807174190750511810f160100f014001550140420f000c0014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 801048030 1250 801046780 801046801
    0x16022e110f010906020c10052a071b060f0914060306030a080a0518040506010c021011060f060405070513090b010c08072a0e0402121f0f050601050a020c09 68
    0x692510004000f805038100d83e01d000c00180d0800081c203540c50240950107000707050030f8030a89104810341380084050301c04506030781440d00c2c0d80032415000d000003045200081040d03080c042e48001c001c1c038400c2c891a032800000500d4840c2c2c43d0010420407002060400107080b102e520340d21b0041044460070303a0390f1180700010b80b0f06211944010144400822204503294115000e010300d4102e180004221400c80c50400080321401c0311038034040748508600401508240985e0f0b10a114141440c07804d1801000d951450400102c5210100545580401400e400c06001d4180c01461a0407c039003420304008801004001501401a145558a0ba1010160301c211142c410b00703600a42290381e15000340c20601410140411040072006007010260644a82c0c16140c0d01152003425804c1941c4d00c599081101c40c402c0e6101201645c81100c000c00c0000d910790200390120b80c6a140e000840c248440600000c1c0d0380000c00030b50502c03d0a200c000c0c001c0745c0126240c480d180045606242681d544403554 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 801049280 1250 801048030 801048043
    0x909100b0d0503070b270312060f0919020f0d0e10020703080f1003081204050c0a0f050108091c0c060b0306040c03030f20070602070f0302011b0309090216022e11 71
    0x1140d0809601101ba4141800480181262800800e01d03580c00e54403c814840717419103a008041d0400a404001611403668441400031109020b0025280540e5482c94991980141e51068422680e0b4015400314a0080242020a0f50048815820a00d02e500e0142070b60100a046c0090800d6010015045182c0c00c4055000345a00848150310b90100f2030703001c013100c50201c4049846200316041c5540714603050907900201e807503407041d024040e4107110044400110141814503148074141d641c858000b0315519401380f083c20f554900345002c0c101d041403030030340304414650307400380d0010024040410062038041050380d4050070092504000200d00b2a803120446808c444146051074a14500c0240482d206080316072607800c541c42a07440c2c0111200400c0c440c8802400305114403040c41c00009218a2290703110300074148850a07658030200c00c801d9a120388a443c4c91410412030b05070031854600c0f0290102e0100c0d10407901030344034501c4201610302100d00c16100b40142c02d01210800441000700c03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 801050530 1250 801049280 801049321
    0x1812030906140601180e191503050307020a0b07030f080717010b0927040609020d06090812070c03020a14010e07081b03030304030f03050c090909100b0d0503070b 71
    0x100b007155600850590754001c00c0e5076840c0000e10100c035691901d0400326a82e0203440740141520055124007000032007a080d003203244507003c0c0d107071880c900000d4020040440198080c0f805555103601910400054180642026103252000c1c840800401e51112394480081120300700f003130094482038000c5d0340800010304100c050416010005c0360115404001e0004d00c00f040d540350b102c0c01001c8103604044000d0510350141c124a1100250103d201c5802542200d0700140a00c21107603100c4e03c0c0c80064030f5100d0030584561400003403540240801300b079120760143c4d80d0b1402c00840b6900355002500d44e850040041c0641c0c0346010f28025548003035200c80c0c150103075901100d1100740d0b0340001d40d490704111003098410351014045034010b8100401241e100f2a0305541d00d07075901c142e04805400a250182c07113802c8508040c0b08004031506c90100c000c1c0070301660002008100c401c5610a002c2d104a41c0c61117010f8864000d520700040c2c00042a00e00705540007881000c641d40701202500c07042d465152 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 801051780 1250 801050530 801050543
    0x1090c030912020a03020613031403060a0f0807050f040902220b060d051819032a051615090b0d020c01020307080108011109010f0305100510020106081018120309 71
    0x41c2c101c2030075000220a40014442c2e000d640e1141d940c2c11582400304250000940400c21910184076024540801980c1c00100200185201c80c3c9404000704003001e136070072030021580700c040c05001d1490420010040080300700d4080c0701c412060350201d000c1c00c90303000100040d10031740e03581d01d404207a43d40c000c0c03e03004038043d20a58a0352103a00d030f4440070f1310083e221144020074240450500000120300c1038101e468440b00c9100703c1045603000c0700d100701c1c03451203c010003421696245400040e09407003600180140000e00000141d943c2d00d070000c4506501070307003003140c0011481d41110780000e0110215544c00d040a6110240000313144040d01c120000b03000954400420040c4440c0c0182c40c00c1e0684021000030050030f03c0c3d001180540d8400c03641690f002c0780c3c619540f0030985200b0707049a9401034440c820f5500d520782d41e071b001c1066a41a84868005030f51211000c0c0404001080f500000621031101444900d41d003101e44200145840000380c1440f1026035175882c90380c06070300000e003050341c40300 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 801053030 1250 801051780 801051803
    0x10503010c05190201320109060f05120304080106031104050a0608070605090f0901030b01081005071b062c0f0304050d020f0114041e0e060a0509071b061a150301090c0309 75
    0x14146e03458030240d101100340c0c94200c0400483d41048031311410040c2c41d9a15000000982400d0800480c2c07040720303007240f181d44030402c4080340304103003800340400551148009581c0e036070501c800c000907a030008180c040d0070303458030078204034000001401004032455411706554440b010004583c68407030b1040e000360420500400001006100a0072038100c0d401c01c0140c40624007000d841d0010340d5000d90310340001500e4410b1200100c00b840003180e0085212b024000345102110320f148500840c1015035000881000c80c68051141091041e41900c1e54000b029510305401c09001808403410014081c1c05084080c1c2d5000459018149000c00540094142a01d03655943d03881408072005560070541552040701c0000d000703aa010845001e034000520084c03034a400c01c42400110f100081181d03042091008110864001c0d001c00d1040040c0507100114060004030111000c59032000d041501070503030b5140b1204088207500669054400380310300410000c45241044016000000d409840340c5180c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 801054280 1250 801053030 801053081
    0x20d060e180316020f0d050a0506070905010f0203070615050d0f150915050a022205040b03030909390d0c080606070f080d061d010503010c05190201 65
    0x105140703100d180041c00072000300c0624a081d540300d00426000540042200b03603035100500c1c0c040c5071000c030301c1e80207400c20801c0311035a2075852030220041d0044c2c1b0305810003428490101d038069009000340c1000c0c2030031a841c6032030000095407441044001b50200781c1d03442c022030101010290070001820300801005e440705050401030050151220201d070310f0300000ea0840d8444c401030290981d0315401c100440021a655840d4030003414004040340113130b42d82040000154841001c6000c0319108100000e9615406c20007032008540900044d64804d9109110551081c0e40316480c0303e40c07110707480041c1c13191180321000d440d04c02c1200c42240847c50202c15842018a03040c480503218100580e2070034049440400d0b01a2005c42d8143c48051300180c04201c5280800c1d004040c0124880c070914030b90340381c950040c1a000484006400c030b240c2c885198101400180f01c20030496014080c201c00030806503120b008044e0041c071880c881c440c116583c500009400a000b0760010300452401d03203803002e40301d401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 801055530 1250 801054280 801054299
    0x903040501210239012a0c05070f050a1d182d150408041a090406030c050907030e030a0f0c0f0b07020d212c030904051522020d06 57
    0x850070513121002c0c0c40c11034007101d00050248102ca0055641d04003000320030f42c0584600440c440c0443c1040c000500c600500044080181d0390040940c420700c00d404c01d01702420010b00c0b9105501101900e04070703627080d03d074040b00c0c00b48103074015545015a044139100341003039030300703040030050441e03109050400c10000e41281c0403018004590040c066428502203150308070b102c620b0a58024041c14407d10007403080c1500001d032400c108050214003800c2201c000005019500280c008a450b00a07600317042100d810b1403c511a0000c1c1141020320001d400d80580c1d81d03807030180352190f204008656110200c01c600035015031072000c1c0c00001a51809006040c294447c03a410355101c0014421180d055848a1240c0401400008502c0718000500010343d12600640700d14000c058202045106240803503c4181c205040c04949902454030307800c40e00104070489d07400400004803a8080f400d800050340d211500720703100001d186103211104c0300000320754009018600032261064907041000c140d01d40b8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 801056780 1250 801055530 801055597
    0x1902030a080a030914060907050907120e0a030f020304031106161415010f0e010e06042c0c06120609312102120307051201030b0f09030405012102 64
    0x38100c03c15000b059005c00580d0760004488051103038100910500980c0303020f81259400c40900c1c50035225108000e5904402c03078103032071010b83d0386a1101d2a031008150b0060b0301680300cac20382d6001070360901d403541c0ca5003a0368100c1c516a00784148000640b40070810304551803600c01076040720801050800e11940969101c52900ca200f011005000000840444804500c81030742c1c281d200e0302c07016903c0d0a0010244140c09808243d000c0e4560b0750015400500c07414440484000c08241c01c54030302004240c5080905214040d40100300800c00c3c0c0c4084001d00050360340007502503600c241c9a41d0f9240301c0c11203031891a00e0060b04000032003a800c1c00384d6801c1c02d0426040e801002c100c54142242c00000b0b002c200180202c0015802c2503031070101514445001d117a00225505015241c4014016194122803007604112205142c035014410f090a8852000d90b011403d00e000b94039041c01d00c070010b0507003412942c9001c02c2c4030000903000840c1d00d040d0103844604940060003c2240e15a4400000010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 801058030 1250 801056780 801056783
    0x9020a09240509070f0302030a0b09070f030c0801140111100513021e0102060112030507050a060501060f02010603240b0a08030403050d090e060f03011e05060406171902030a080a0309 80
    0x14001c0c4000728141c54a00c052a00645154413000c504200c5100154040d4000425000483c1c0c0d03a0b81c682145500d880e09100d1003501999518920750250381070241c221802c1c401c40310304020250006100d40b411901580d49100c8090030b08081e015103003000306140c0526000c00c844058240000d214402c41c881c00100b0304980300b1564003076044140d8505424145202007428016804140100000c440d034000000780c5038000e15203603180c004580c840a2600880c440b045a91075a180c0041004035800901d4a540e036940d4402404941c0c5503445030b0207540200e03407403521401c000007035002a061080d4020150400094420010a41d0740d011042d100d03041751005548a001c4d00c01c49011742031280c2400e800380c1d42120320580c0d66484030024804241601d080c0c1c15090f640e0b840580c80041c40729032154080408559000c0756a01c5c0a100b0700098a200d903204403a00c910405901c0350414000c00c07408085050001700c20040006400028a001c0f80ca98010342138060000f001001d83e9811b070061114107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 801059280 1250 801058030 801058091
    0x19110103060501020c0a0b030903070f0b0a0501080606090118060504060b03010627061b1b030201022a040e010b180709050604031203050702030c070605031906051309020a09 76
    0x242d958001a6180c0e5842c007013480d40003042c0ba10900101d4044405581c22201c1403048070300741800e070ba030b81014040e402401507034150130110411003c10064029a405090120042c100605000b80410503903070040c010784c2c000244804513500510000d03486480200801841400f1003036407603031f5014042e8400c3c020a03000034001154103003c5000100d0302d8084e51940d85141c55040c0c038000c1e0840d5a5282861000c04000d54249040049000101c150464002d410400310717025181d440003902d440900c00c07040745045042c040e010408003035030100101c014415140864105030310350780e80f801040203021442d071144a04406140c00902d000d80c0c0762103003026840d40103890340c130741c000c11506020303500c4001c081c0164501015074503072003a00281d410a440b401103034186980c0e150701078101645608038000050010007000b40704032151184403c84440c41300c00308a040d0805001c1a403100381416038284c5580c60711404821074840c0c5101200401009808005c80d0129241850700085200c480b0b8214 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 801060530 1250 801059280 801059291
    0x2092809060f020c030a0c030c021807020f0c0f120c040e030a140f030c09010e040c05091f1403070203040e01172e0905120406082418040519110103 65
    0x1182c2c42c501c21900c04070114401507051032000101200c5541014004400700200620481c005848105110745440424890420603280040300245002032030990302c08142d000d20005002d645032601c103941d01c40302c00d8134560803000742c3c1c107001131401d6034000b80d46800600d000c04060a034074010010b400c515065a503005011280c00710f842c0010700502d51410080201000400c1a00a11000420340d032507040c10441148101000002c0c12114030f01c1c412004a500011080302c10b2070058490f91000790018680700203000d900b20002d00310300d259108120445000000701d802c0c503000b0429907000b002110758070f070403130742e101c82c48181003c00c2c481101c4110310940301c205902c00802aa03626400521491420000030000308078406881d405000352040e0140c13448000c0d042d0303051001080600380c50b0300d59002a00f0000b03614601012640d0b4441c2d528155554031042c03540e103080d44a503807214084500c40b01a2030f14108030b41084d1064000d240303003c2041140808200d0008091741c1e40b00001d0702c04000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 801061780 1250 801060530 801060551
    0x151802220f080a2d06090b0105190308030a110c0d020d110303160f030e030f180a060203160218090619062402010207120801030510180209280906 64
    0x50f40c0b1a451801000b54410360700030000300d240880c510309405507610062180d1020790710313a034044401801081c1c2c1c995400c04014440307070030505000010f50342030041d000070f114515240d1212a000c05800141e4942d00e03584658100c240807410354040c1881d8000381d0b00c900241c0103000e5583c110003065100401c4603121510131001011080d1f81c42204003030b421044150500c00f040b10503e00c05484d0106160391040b5001d0328030002c0020b4142c951148217050303910801584810449021501c001d44078800e10141441210b9020003600c001059024070708055660a2000074050390b50030f44030140310794004041007911030700000c3c030600480504400302c002c103d20014040a4031007502a80c40c80c5005036691140401e01400c00c071804148510005007001e21650360040c0e0000d540500c0d100151043e401030084c444280034103200840310400420842c1050744014a505c66190f8001e4405c040703210020740348030b50a61000741065808105010011f607840008001882d4840c010307603620386062280c80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 801063030 1250 801061780 801061783
    0x2102030c0906240f0c0c0a121502090f040207030302070204050f2404020f040f080106050d1a04210c03031404082706031005030c0301151802220f08 65
    0xd00407100505500c1c100004040564200c00c620510181c0b07000c02000100e0202900102a14141500c1409095240c0c101b0040102081d5240c001c1580704014240100c00031791400e04005c15900191005a115060040094ad60125150700c258000b40000380070380801da4150300400780d840c0f08660030005515402c042e20300c40881291403a00155000e9240240c08028903401034000c0001400549400c171903080881281d0003035401031614426091003801440000c0c0100e0707015190030f54070303180ca44034075407034003407003490512810400c0c4070030f5101040610180a1091080001c046802c1100e21000c0c0002030054040f9901500000c1c5002e45903180e9841c01d00c01c00e40515004580d20781400410945540c55a000183d028010505801c1c0041e2644566024500c14001140c2c00a20703035242100341400c0100d600c081a1090b450a1f550101041e0484103000544207403407089984001aa42458020b1099040c3e14405c0040e8000069012404005103010348800013100c100ca1a66035a00c0c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 801064280 1250 801063030 801063049
    0x40e070c0206090d1712190c09140f030d021f02040803090f060d0903120e011415060d15080f061933031707080d0504020a2102030c 58
    0x2075110008000c0407846180c04c00d0350540c01401030300307000d18003400b8560320716255101b010700c40700c5540e104040092404400c0903041081850f4034007803110110784070006006007494000c210034900c081c8e0b0449007035282d400c440b83c045a000780440700d14080402000c0c0d40c840307148014032184c1904070112080c0d00030364002d40b411242d2031750065040c190000c0800c00b082030410178640e00001c00b0b2292820014540c003400e81124060340300c002403c0c01659440e0192021074644080a03814503a251201050414100d9400114001c6008011105800040b1303540706105255010714208801231045c1b41c0d940224078126843c0030304441144007410406a11000215a41c0d000c1501c0842e142c00c9034402c5030072070812040d0b40d2003600340750800c00003c00c803400b16071307400004015207840b42801040039254103100074041048003141411519a2003010750b101d804014070020303440340302103000c5413070f09116200075184045a13403944805008258547d400703c148268800d03c200604c0010508106800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 801065530 1250 801064280 801064283
    0x141f06030c0e07032003070f08060d0311010e070b030a0b0d0b0a050c090406030303021b06150112060b03090f0705010302180f0f03062e0e010e0907050d08040e070c 72
    0x8a040741440d00c1c40700490ba0000900700001e00d9110f41034140341c220843c4583c000e407030011290307503141c3c2000600104030000310081c0301e040c021440180401540c0d030b4800c00c90710716890314050318903c911445060150581403607a100714890031801183d07003007050000d50701c603100c0c1c100c04000034890341c401c2060311540304001501603242d010104198004642210307901c04000c0020514091804001c50100c1d0000c0d4415070003e54086101c200c0d550b84952039400303e80e9618018607203801d21403903004001d088a60740764180507022000003281c130f4981d003111005002c041101c64403464055512503d901445554001c00e009008001c1100d6002c1c0c4240c9070f1181e0241e6244001082034800d00c4029011411000c0d84182100d080155a0342c041000c07621580c0011340c049604078003880740210079007250403140c809918030340040c45180c0158600b141150204154000a034481003002810118240c1155400c03142e840c1c082c01c248001d01000b00100d80c4440d0458101e5030b20b10790104c4031111313032000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 801066780 1250 801065530 801065543
    0x10f41030606241e04031104050a05060f04020901020c03011a09090706020706050d1e021c14040204051b070602190201020a0e09191e23070c0f141f0603 67
    0xd15102e111200070140c004c1d03420004283d00e001d141000505100d400a0b0310446044064108038455170501d03015164110700c0c03a41080c40b2504003100003445180c4210085070003a0780c0810b1202d0940e2007008031211014000e0001c21440d100d42d182c4011502c46070700142e009080c510003207150304400013002e100f1510140d018001080c20824100d8682e403208640c449040d480702e412600c00c40c007442d100c0004240310000140c1d15a0303000c541d202200c45403662031101b64070300b00b0080904200420a40d074001d60442d4000750756980c8480700e405255080c0e407580a0040c02141800070060158010030035041c540000c40507810701210201d003070b03100302410070300000c0350328540c03500f40d0815244035134101828800220001d4103000105044039920a0340207508480b0306d140c41903000d10752041450300e4010802005000650b0041c1390b02c45100540b42008201e6a00444420710850b089084d110355845010150443c5d641140c0030756030030344200c00001040319611900b070510030500c914002c0700c2e031041 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 801068030 1250 801066780 801066829
    0x140702070537081b0108042a0e060405060f1c11041104090605030106050a030b0903040b0d0507030c180e130501151a03010f41030606 59
    0xa041c4a100e00759110060b114107018255405044200c241145541e5520600c594070a45001100c510f003074a07104020b0100010141102c41e0b50341d1080c0030603409504a803c01c12903403404411580c200d90490036103800d030040b250300030036040d034294050360003000d080710240040c1e10740400700b0000c00c1100c140300da400b01910071117810468026541d40e24490007100078170040403e04000c00c060342d03034103034a107060104005801e0102507111300c01c441c051701054000700116801c0501282e038a800a0202a0a91052500286e1950400c00440340506a400c0f0001d0300c600401240c0e80141906445080109040c2070b194040c1c94032900d000510700800000900801d8171f49035411044010242c41c2c0e1501c0c0c5400e84000700815024007900c08000080f080c0c032503480f46030924200d5011900b20104411140400c0104003003007100350040d054880540c4017024031100d540f001c1c1c9900c942c84620380c3c454603150340c006201580341c1900f00940b08040e4156440b50381d4440403c00c0d50b0703850b0f00e5105882c00491 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 801069280 1250 801068030 801068039
    0x1b351204031d09010f06030e0708120d02070c12020f090411060711090f040b070f0c1502070b0a0b27011e0305010e100b030a03080115200a020414070207 67
    0x9005400c08110307540b4103455151080c4000ca801d1540981065100101c4198100841030749482036104040c02c0c24040e190090401c8407207512182c99070741c072926511000c0b450700804402a4125104180c5c0310094200603562001c3d800400b680c201c406921800c0704048903403503424800112071159500141110a151106042103544e401052055400c044415036a112913103d11100c4e038050000400022503d24285c1b90440b26807a004001a0401c8450300070018a0340e000340d5003115003648547d04a00c04900b100c0c04400074040e4010140010107030b40103002401b07445038001c5800200c16152007074090126000d1484004803014601c1a010102c1d0040200c0d4290b0742c513060401a850440010b156a6902c600d425a01c810b0108482c68207c411741c09a072101603c145021605c0a0340030300f482d65040c0d1005480c6880502c604112045412001c031192031040150395000b0790119840039103802c0c5450008c0d9503411f4008103c0c0100d00d0194141d080d18039000714070340316000311f50042c107442c0d007030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 801070530 1250 801069280 801069287
    0x914061809010b09040b06041b0f03020a03021204060f0c1404030b1803030c0a020c100f080916060903151b0e010c08070b041704151b35120403 63
    0x1440795806540e1070700c0c41d0a0f603075510504180118080c090707000e91707402d026003003008507240707141d0030060200b5403601409515044403030554500b40c0c0303003401a143d0035280400e601034420840b00303500f0014000c00b088100710240e40003140c10b80240104000c0e105440350103a07030343c100008059200c0c1d14180401c10000d00c00e5895550320000c0103400c00c111141880c00913146400070f85454419200214015800d0fa50401041d890400103c03010803882c40001c00182c20302000359007a20820515400082c6240c0e0200103510301400c00c008c0540c503180d981c1c00010200c402da030200722031107503140c45200b9100c4401d01030840001070240c540c94001a205606480c070961401e0868103111229031002e0205200c403015100d15405480c0009543c82c0c9031500302c0007281e42031903001d02d108040c0000e01101079581c0180000401501348400654000307039403140c506101840080070b0140b0188100c9944a6920700307450000c10030580c55015280c0030b0b091a07100d0040601d52030380006104005000b02c0e10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 801071780 1250 801070530 801070579
    0x405070b1804020f0d060b0301081504170a02010b100f02101a01110a0f06020315010309030503070c140607050a140c03190e040507020106080c030102070c030f15020310091406 77
    0x40000403600e403000c03917102c0c0020741d5107a07845480b0743c41b408801001b159030113000f403030f01447c1c41d00f1280002c0e280941d5801c66401210b5048000c0c200040f5081005038000d5205078103064004240001117032054200401842d2890044401030040b01c0f1100c603a0102c03402500d19481c110100c481103e4040d03c0119240c0420410541c894401d82043c207000c502450742c500b120346d00a4030096030303c0c80c00301c92080a40c80d03076000c5241014608841c41c00860b40c01015603400000780d141400c0b050744142441500e6400510540a0740e02840d020700040310341040c010034111101ea103e074400010103120303039400c0340079014158505400c01c1010240c051300810302800344c400c0070f044c17242c020b0307021401044c103c0e80e0450385035015130f560b14414000300204200d007051005049000758509003861350b0301d504030b181900c80204140203480c0394104201d2074036044061158216401c41d16403070003884a840c049654801c41c2e001a142c41c00c601107016594141c070340700b014081c00310100d030201c20060b24924175 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 801073030 1250 801071780 801071797
    0x2408030304080f1608120609040b0103080c010204031401050603060c0415030b011407110316050a14060f07300e090402060d1518060503060c09270405070b180402 71
    0x1d9007001989450b5130800c0e80a1030281c002c3c4c4080781c940364000c02008002202520180c0b0940d5040104030008031607250603819641d1040d1956264004018591f02900031034100504100803c002c4610340d0b0815802035104060131800c45165440c0e02e0100325440c8558041c4046419002c4021807145c0d0081e0000c546003c410b25080440c00008814004030350451401141c08060401c44281c080c5070403c103003540f03500b8940d04040480c0c5801c00003003074403801784640200700c04240709000c131660b00c0d1402d82c1c0d0300d011400c014540e1100d080c41c2c001804a107014114421089000c80010280503030150034201d03510035151032451850400c00c00604540c005c0007268005c1040142c08000a8280a010703842500100e00e101c0450130300b805650303220009001941418a0107208000942d00061120f400030400d0b00826504c801720004070b0341c0c1e0040301000046503503e0000440c211001100010302c668003603015110000c0d02c03803d00c80a640701d050414080448082d201003030515042d4000c0002c603 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 801074280 1250 801073030 801073057
    0xc0f0b030a180c06030f060b04050a14040216050a050601060c0305180f0a0b0a4109100e010e01020a0201020d11011b020601061205040f140a021201240803030408 71
    0x800680d0f0703500f8031003003980140001a495040318a9a2078050203004003514001071543e0506040402041110165100e01c0c0301202c0303801c02c104a161110340c1212640459186034206211080c20180d0351034a0300c0324121030511600f4000900e091160f5100940c1d680c1c03594513146020341401d0945840d202041100e6405181440c89107031641d209072801c0010907850104c292505003800c400703042804074a0001440545102c07400450844500e408001c2142c85040405005909413840103a8002c012015404c0301e4801c0d8151101500007500c100140400d03654401c40c947c00384012030715200c3d03409000303001da4017024005402d07034010a000b9050b480c044000080016000c600018807c40c03045a0b80d0268104100601a6691200000c180e200c040300c1c0500040c1060358501070b19066202c0050040d07140d0181605d11028280300c0e2600e119001409012610807080ba418000e000418001000f201c0301145042c8a03440f02400030220f500348030185043da901e80d10780d961941e03c098100a0f12 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 801075530 1250 801074280 801074321
    0x1501060c110f13150b0903070b03180102070309050a050103020913110c0115170d02030901050a03110309012906031302011806050309070911030412030e15040c0f0b030a 74
    0x783d460f001c1001803d01040c290100301071403206400241a401034000400c03c40040104d036096843c0014080200c5000e40036455881c3d4a07403d6403255501c04580380440365000064100c241680074401e9401d6420464459040c1a59070005408038402c0022842d005400300d00b150040902a030300c0f01c06c140c0c4580105501c2d284018140c035003110f20700c26042c1d42401110106000940307901302c1d13980c10390221100400958400c540c01079900d01880c0c40c468104040007038440b007241e01c242c003d035500e0580d02e041c0035100d0605c0190140a041e03165010318440504411a0108004080e00e01c04240005081c1074a1a150880c0c24400c8000820003641400800c0e0501442030804031f001500510740c9560f8180c1742d041c440300050506855030b204401107803d101e040384c10444050105e039003065018002d007009020460042d00035000041f04242540641c2c0c8203450003650001d00c41c1d200742c0c807411022300050384601da80f201a00c1d00b801045482641030002505544640c1e0000100460f0100020742 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 801076780 1250 801075530 801075559
    0xe1302010c150603080706050603010510330e03120f0d0908190c050d05070c0e06040e06010f140312030408070c1214010b010903030e041d030a0e031501060c11 70
    0x29107030f0302d500898910000203801c0b4107004080c1309168204104900920250809a031200c1414030030303000d0045031180300c0074071a0f062a0049003900102843c00b0741800c0d54091090701520603180a00020f0084c0180b41078010198582d50480d8001d501701000b15040841c8982c0210082000038403c8400c1142004140c0c0c8003843c41241200a000c25076501110f980d040c9451418240c1e0301107942c060003018814400041d55006140059aa0b01c1480c4541c594601002401600318035134600500e01900001150200305600920146c600100042e50200079130700c00d15a42c2e1a0420344444c003940300740301140c00124080001c1c00310a00800300100f0081c0c075242d84c020034000c0c041003215446040c07034003d400c0400c00c0c0180c1160343c0d02402d00d1052170707143d0345020f00b018030070015442c8540d0784d078601000712103070b6171001c0202c200c0070310200ea0300c403106940050582030f83c43d0880f510074442c1003031140f0074002084425058695503a624501c00300d180d82c4019424a0700100554480200e110505 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 801078030 1250 801076780 801076823
    0x20030c0f06041a0108060c0f161217101208130e0708010e060d0311010e1204030323071b0503061302040501080f0c1201090206030906100e1302010c 65
    0x5040900320006489507042901d00080320b00740424401c094102002e0041100107030104501c0e0384250440c00d0503640381d6800c681c2d40c000c0c0c811484501810030701078414109203d01c510002e40805400d4491407100c14550503800c0d80c0800494000100c21405c40d01844602d0314504001165881907401504240100203000a80e410700d400a140740b41519040090707140d4400d0300240140461a4140305c142050404904124201c01018041c02107030603014034040f0003540140c2e1400c04c500166000f110714911010443c6e4014481079000035550a410300841041c81a9841e859000070105490705032545d446420b80f9000d68554110340d08282c01c00a126201401010710407120000700182d07801c0c1c03502c1000100c0d40180c202d002650301c62461400448400205003140b0b034801c8907400b10030841050079074050708804000a400034404820f015491000050550088070038603110031500780ca80050300c000d40f00495020080703411007030342040036501481084d4502030080007400001c404141110 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 801079136 1106 801078030 801078043
    0x2071401020604030e0f120618030301080712031418130b01050f1b0a030f021b011e110111130b04030c1e030203060a0e060f040320030c 60
    0x4809944806d0040b101442c0101261a01d03180d00c070144c0d8580f0010b84488200f1221051072604120300441580d05803104540102411440d101410909044250041c1d0070321844842847d8907010100041c40b2180e00700090403445192003081c001031100e80c44111451604c0c05940f1921a0b80c00400ca03001d4807030b24000e80e600c809220740307080c6811030404a5105a44038000d00003080540001c1c2d10201201d603038095030f0400921141003060140700e030710760170f0001e101419020342580e69580310f50f0000c009460418008140d480000d403c4a440517040b1841c80070215103070300b00040308203d02004d40302c1c21040506051860ba19025201c015000b680d82046522034080e0303111044501410040d87c0050458025080002002e00204a80b03030000f07074940140301c00102c100701e1103410a4059541643e8104250f05114001d2410104041d00c82249001c1080740c030702480b5040050 = true := by decide +kernel

theorem cover : BRFrame.Cov 800899280 801079136 := by
  have h0 := BRFrame.cov_init 800899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 800899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 800899280 ≤ n) (h2 : n < 801079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
