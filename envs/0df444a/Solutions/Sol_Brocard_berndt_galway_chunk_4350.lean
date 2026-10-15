-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4350
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:20:25.145218+00:00
-- url     : https://prove2.me/submissions/a334ba4d-58e8-4b74-baf7-4cb91d676f58

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 782194244 ≤ n < 782374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 782195494 1250 782194244 782194271
    0x21b10030e0102030916050102150a0506120a1a1f0317190e040c0302031e0705090409031713021503191415010e0604060302091507141009080904 64
    0x245400500082d510000c14040e503080c000030b05610a400d440c10f03030768800f40d80380016a12221503018110102c1c03004000070303500410590003540e0180004151800881c4244e421a01e80903840004481417801003903c0304c00115111740d1603900009003e081f50241414820010a04c1a9480300901890310a121203034280310750380580303c1c0760450340e1404480462031000108030079104025103004900c2c10300001612032003802124443c0000b001000c007904650565254840380042052003005028000c1804940d514010382c00c16600a65601d4000e88c1202449191020041d10002510011422440060b1181c81c032001d08401401d0324151640da9220700390001580000309841100d140040250b285d04011110701e0081c42d035400080f401b03180d03407001512016a804040f0340d101300280070800840340f00360010b2020100181550090454015070b0240c1038101610481b001400c1c030840d60460344041101d4450388c02445818003027100c0d0750300d03117810a02c18085454000d5848285c40341050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 782196744 1250 782195494 782195501
    0x5060607030c080c0a2616030e040f0213091a01021e070b0a200f07140604031506031401020f12090a0c06030506210d0f2601031101021b1003 62
    0x242804005c2c1d0712011840e1070040c540d11101035066403c8014403608501c40e50041d400d03607040e0415154220447d00c05a2400c0c1c480a0b450650554003a4551000b40100340d01400901544881324804201035400d201400c000cbc4da44e100310301c40390086c0c40c245c902d00076130340007682c04c42e1045080b911000400240d50541c0c10502990810b61400c0030015462008940c42a41503040c60803000c2c59503144100414000e49804a088030b5010310341c880d00d4148a0340f003050b8a0742c00c041000a00c03480c5029902e41e40d01e104901e80551400c42a42c1e07a80b01001807182031b4a590b1728101c9044001c5141010540c0c600c040c5000b5580c004021958080c005a4100070402c44403808641011101c40001c0d6112001030280c4801c40303490303024008aa921040c0000302840c00d44a03007020320080c0c0181c80042c44211520008555004200000d50001c495400d130300303050311010150001c4d0300310004e41c15800c10f541001c03c484909411980000295603080300314160080c404c2c2c00c111848141107000d52000c4015 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 782197994 1250 782196744 782196757
    0x30c03150106210501080c0a09050405120d020c07080a02102c0a0302031b041a090f10050604030b0403170112060f0b03010c02010603020f0907050a0f0203070b04030203031005030105060607030c08 86
    0xf0a842c1400104590000140c000d0f903600c000c6071900c500b04c1d1504101001c1d2441641d00800c03d41c0300e0244000c080d10000043c01d10300300518001400d100c07400210790718292541c2c1c0a800d95400080d04e160641c1054807000313441c48101c2c100040d481e103400d07a100495055a441d5081d1000325610000300a03504d141c042d0000710340090440c0e286101d84006100b00c8800c0c2d80049100398680840544422521201040d5070800140800740a42d541d8500d00754510303000f046075046505101010400f41d680d030002c2c1c001b40d03004407840e40d071601c2c0903d405030030003280c1e08030550480301c054010090324100c40c0d50100c0090307000364003203001c15041c105038000d40100800994076500304428601a55815806102140e00880c0c03901c880d101c44205000c01428142c41d500c001560130400d40f80c026004101c000d0807034085104803482c104403500c5024850710240e408030300503040001401004011540b40c40b01a000440081150707040c002c0000e640781c4155030009040c48180c0a5250500c200301c0f0a4520 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 782199244 1250 782197994 782198057
    0xd090c030b040305090f1507060506031504050a171c021c060b0a080a022503020a0c06050c160821090307081f060e04020d2906030c03150106 62
    0x1803504103850702030308a40141760110b000e400500003624031840d0550035488026880c100c0c0601e07285240c0c071150003810006040c0d54140c81100e582640c1421600c1d02c40344624040e4001c1c00515040c1d14000001c1100800100400042400704c040c280300484031040801050160041c0ea03461440e9882c0351144182c250012850300d04440061141142d20042059030501e65a01e080c0e41d4405000604034024002d48000711064690040c074020640883c400c043c80c040c1c012505d401031aa5910135440b00c00e030f04903d0000d04041900e92481000b00b0401c0d145030b042c0c28400c0d007200d08181619640d031070011403581141c0443c1d56108000b0050030225a05014068190345070240c548074116503e51001c0500340182c1002e41d02011103004511409050f41d12102202045032956000c01c00c0c0000220b070250360310301000d5081c00c2e030044d24501b01d8002c0c0550345445c03034445c601601050b003807088100c50103029400c40720380503011240c4982c4090550b1840c0c28245240c480409500989400034859402d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 782200494 1250 782199244 782199263
    0xe070e12030406030606020a0b0c070c09051017030313031d190317070c030605181005070f09141306030803040503071b06050a080403030b030d18090e030d090c03 71
    0x200e003044040000c00640b6041d85044c00441e60316030080346c0d561b180c0c4001410304205400840c0350044540004c20156011b00e2001d00346c25154042d80c0d0484905071070082d08020710400822016842c02c80740b64904240390051801c3d40f40150f08165070503e9143c000341040341c06031901d0702030184503154418100c13020345006005054400421601c480030f010030740d1551407040360220303861342c0c2404662400350b015001c040341502d1583d844010b841c01900780040d20b1003840c0702545500c01004243c110990200c8049280e0070061005024802654400d41c200180041d0034800440340c07160405805801f03660050840c40c0ca6214800241055000148a10400000e12080c81400005021850f002e03041d990118803850103810500e0619108a1002c90414408050260300a0600315401406400c0204d5554509000281000961001c4e90082268000402c3c40d41443d46055800350042440403c0490f400c00c041d0f950f6402040301d9080c1d83c0d134507210400b080201c906011301c0219404030411 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 782201744 1250 782200494 782200519
    0x304020f041d15060604300b1e010509060f012a030512010b070308010e06040b03070603060608130308060d030309050d0e01120c090b0d09020303070302010c02100908040e070e 77
    0x543d120f01244001c03807a150040400f1480a1903d401140c0032102080810640b50009040c00700c00391508000c410140c03440075804002007510b643c034082c400e4202981e200d4104259071881d2410701c206800075406458610204480d0341c0b600c4110074550003090a0000c3c80c1c0c089144030085c1204590070440e450f00c27040200c58101a00840900350510310031314010507586e00d403581070300c042c003070030380b02400060180004010f680c2030460590b0300600b02030000320f03156a400c4003003440d01c81c541d4401d04c0020f030b40d200c0c10055281e0005003250001c542d6800402d04e1941510028080c142c0900310510400c8103010070b00815000e40c2c012034402e0b52003825a0490100f007500034001e017680f41032450104080d02440740b0008442d2058420300b050a40f580003080c0c0c00e01e4500002130304810010b891490342c441551700075a0302000908a0700b4826030001c40ca001166400a082583c00705104408a00f000700500c0051000340a5a050f500c0d07002c18504156076a41046442c0c661004030160405a001840c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 782202994 1250 782201744 782201801
    0x72a082203120804020102070e0c0706140603070b03060d03261303110307171b01020301031101301e14090d0512040f14070605091509060304020f04 65
    0x100304a901401454503022824402600c1d82141150001c1c0107800c0300300180216014001002d822021303140c040c9041c170700181d840408441150880489292015080010500e8200324174809000401c08003411402d0490101d111080030a03001024086055214240040d401071800314903150b000c1c0942c090b080540c80c01c117041c0c0d507007441038000851309906404500b90000407208582d6001240c4122192410301201440d0005292078048210441014000c403100340051800b85000e802018003d4020800160404075403280b1a800e103334a101c900c0b88001d02d0401021241d0321074000104d5030100e0502e00c0d0151110300080d80c1c03002884c125000010700110041c131881543c0c00001c80d00e02d040a0341003510700b40903952a00408082d0700d00001c00003007041d10f40d03a40d0300f072081c100966440c05d8040840d0030030110350000070018a01003036100c01c07031a081c000340340100024140245001c14600c007240c51071100520181c00b40c88510101c0710b951b02c4030b5111041294280151503c0400710285 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 782204244 1250 782202994 782203057
    0x6040e0105030c01050a050921070b040e090c030d180506040815070e370e04050d0c0b360d030b040b03030723010504031205072a08 58
    0xa07040c00392203601001034540d4064021640c80710640e48586040c151a1800c11480d00441b070448032011404401044c66200c00700001405405480c1d0709a48840c02d2050402c0c9d516002800c03241c1d030b40d00603091a40e40351404103000c28802005d01d000155451520401d2101088070350243d6040400010006080140171601800c0161071455034510743d01c8220044440300b480310b09580d40039810070041c08903485940940d44480c1010320b10358240072283d164030b90490000390311115107002c44400700010000c0510941074510032a0900503030030002c944610462450040411011070003c40211020801031802c1109090400c0000c0c840501000b000d1500c0e40d0411940c00d011038106403614810b460039000300f15401c2805002907081c0307070722515180d2024586c00c0d0005044641c021540c003c1550078001c3c240f140f40240c449010310300940452504860b03008285004011840d0802d0302010a071040501c0070443c088890014501d075400c0c0b21607e407003003041404204420640c80c200001c540031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 782205494 1250 782204244 782204249
    0x1302030708060405150402071502030a051f0608010e091c02160801060b0d0c05070b01060503160815010f1b06050105101407030c0f0b0901050a0e0a0f0b04060b06040e01 74
    0x1920810340382c50350350501c002d482c0f0540d2030941c2080038226544041c201907020348a03060140b25201c01c03811041c4c0c0558100e074811346d06c4000e100e40b03490030800000f024610368101d4400704051040300500d4018001c24100c0107004400c9241c290034080344080390100f14094004141010b9045500790910020750f84030614164600d0491040c0300010b409001840781000702c803089482103107040b550200170001454202d5040040c000d0500503000840c0e0640c5105001e000c00351603075556802c00140f960800303c096103500c0204281c01080010780d80001d810500401c0c020300b0003100e4404d6001c0150f5903450300c4050100840b41c20320828046c01a01d80050f81225001e40b1844412113054500311410b01c00f09542c08101e01d000c00200340080c0c41290084101030040550081d0000072317564100051001740d444640c08d039140c806001d855030081c443c581501c046d250052080c0300c083c0d592510191a000406840c105400d00041c041c45480c3d000702c2c050920003083d15965940b034000d40c458080723003070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 782206744 1250 782205494 782205497
    0x15120e0d110d0c0f03050f0304111305131b08010c09091a061b010b04020c030304060b19091d031c150e010e04030c06021803010b27100513020307 64
    0xc181070642840100b0b00703044080c410b40d14000c4a01c22030b1a1041c0482d107460b030440c2003060400c81c080c0c213081880302450042c2d11419094400c000310400308040480c0e01c0e0351040e0306910b03120038003000c518000501c048140e400308a01c0e44044441a101000350010342c0280d84a5007131a003118100c81d0322400700300c00d44800390030410000040a40281d0001c40e01c7e41111380044042010000e07d0ba0510440a220132a0300b001103907554813000420143d80180c01c12420300c0d031002c030610040081d64000d02030400425a400b8601e40442803107a185800c0d10300c11035030b0142e599182801440d040c44010b4030b003009000200ca50300c1ca90250611102c0b00b445030000051480c0a081c0b801d05588542e10004481c40c0e0481d6490076400d0007544030307150b100a0803c4003030000c201c0f000d4000032001d0028005059160088001d440c0707a070000d00d82514490205a032040387c4000315540c8035100f050011403440c41102c0142026503500750300d01d406a0281d0005640300301a080151152031040e0002c52090707103503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 782207994 1250 782206744 782206757
    0x5160f02011b030e07170c1e06040e1816170705040e0a0b01060809031902031303150605030303010e0c07300e0f0d060c0c0b0c030703060e0f0115120e0d 67
    0xa6405014944031221002c00c2d061f0484840d2400c6031420078103001d40c01c95041840041040c03d44002441a03000c0c1d030140404440180420441110000390341800740c80311307800f51010421410a50921518a0080001c86410050303000e0900f503080000001510010340100030013030510448035951104600c0480f00b040310300001084c6036114858060041c0ca10000450428800c1e00324844201d03240f50742c0404503c014409610003010805041d8000c600402c4401401081c880311041640c1d050380003140640d00400040113034566502c4495801000c0030021900c03440c5a280203503007084aa002c0c3c0400883d4804a032020611880c0d43d4402440300351031301d201e0070780c1ca60107101d618444070b00519070220b0300202c0c000204606070028080110946044941d0700502e50390040741082c2907441c00c103102804410044002d40511480c000f42c81c20f5180b80e9a9403a0001105201d94014012044030000c4496081071003401190404a01c00c0301c02e20034082c00e420036880039510004820a003000514 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 782209244 1250 782207994 782207999
    0x40906050f01050a170c07051b030d0c0807021507080301090b0a1a0307080a240302031603020a030f0c0509090f0105011517100306140108060a05160f02011b030e07 72
    0x140b04a551305400d45d00c84140710805100554001d04000b0260703840d94404010b007000007074023404040d0108a08490400800302100103061800c8581c040e420b06005e2440c4101c401b00e14114142c0d80501e904941c0c0540c4000040044540c9006048009120031000300012402c0e41003500110742e094070590300012610b03520b03014030012002404950b0260760f01040421000c40c4519003d9600c551074070b6002c20341803041400003813a044c002070b141d4100d02c010305082c011860b00b403040e07854024010503103241c07050840c0c00183c85400c035484018100c000f946100e40c104890304101c81c1c01450010404481443d05403800c50300e4803400919920b140d4030700000891040c104d0040c520028886540c1e41200024007220b4048034500503000d080c51a410380d0b00000050040e00a048240303012240d102019490302c40d1003464004050711348a5041c4c200010003032000c2e0960400ca100103002d01c1c004041c900c84503001d83c010000705c1080522290040010b0b21025019044450008054402c4030050b55 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 782210494 1250 782209244 782209247
    0x1504031205040f110d200a0b030f1602010b0a0314061311040902040b31090f03030209190b09030d110705090c0c071806090b0108190e03040906050f01 66
    0x100200c8000b803d28110144000202d813400b080c480800c24050801800c54900d034032503014800541b50b94440c81c10440918200d6806d0104078000204150b018207800e50400d081c00c510f810800034410081d210b250196045010300c00d4200001da044003400300c0e074545481c0e05040e02d203240110082920b41c405e02c008107038100d038000d0b0704244c1c0d07540002e80c0b40c03080741400040001800d54001c2c1a648662075070320140990740d8014251002e442417035071104c00b0700e1842686500c0c0c02d00780b20034010a10701d48264100821581c1e440441072130350520b00141e5401041000032000700d142d1117071000c024080344001c80c5c2e0750703090070003040982000c4049819800254404450840d1200c080c42640d801071001044039051695204d42c0160f400480b035030a220200c130074140390014035800314804011a81c0500e020300c0a0748100c034040c0000c2c4d41e0038010030b01c0b500006010014064451030108101d00f400d00003405d1107600c071412020460054a644550b50b014400c00744c4581c1c00303040d00c9400002150342030341d07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 782211744 1250 782210494 782210501
    0x40e0a03080f15060f071b06080109051008100b01030f02041419030b1005010e0a0510080a06080a150c0504030f06020d1b03380906060c15040312 64
    0x100e9040c0d41d00e200641e9030a04004580d80702404184510b081c00c00040d915603075800c040c0c41c1090004500640740e500a040005100c0302c02c4405071940b41c0301d040141300702688801442d066134911103001c0340d582c6690380c041c1a80c818540c0220300314000c4a2180c900010300e600000c0050100b6079041c003c1e41c400318a07160403403086115091441014000d2036040e03042001d881c4015007141c010109002d0754a884080a1038000c482030034848000e00014000d1b9a0001c0c01547c4500003a0350007a03885040070013142c0c4001e101030003042800100400100c82d2601c6410490141c01000281c9440d40410b14200c00f1000d408503030420200d0510300f0300e2140521071005c2c1c0701265044940308100d50000d86400c802548607010143c1d0705902d901012900500d4211699254400c44d030303000800c002a961081c1542c0d102400e00b690900001e040f0000700c1810781400c0b07074174100880d01c1d690ac82d100c050000382540309216030840346008040d0b4550010342102c0748070b440b41c0d0198641c411085034081180c1c044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 782212994 1250 782211744 782211763
    0xf0f1e04212d120f09080a05030f0a09170313140304080f0f0c01050d06051f110c03030306100909050709060f1e080c1605010203150f1819020a030506040e 68
    0x1443e482c8000c07180c6032042d006504006039402e03001440d14815101c0f10400c1d0b201e00a0000030601c00002c0c0401410101600fa900c00300d80002000420035540d07a1017a840b81c025500e07081c1800200200e6840a0410301d501d50960f400000400c7c000341112009489070040d00ca20308250003400c0312481901008a0600da6000d02500904010070f100001941d254004004c0760031400d940da8008a90b03510b0700e40c003484d0105c5544c40d502c01d10340c0c114140180f410700304144501c0c0c0c0d500141640f41c1305440010551ba00120308845c0e46400c000900e000b00c030540e0349580b1081c5118141b1080c0080740750070080030015502699240c0244206051043d50a480c00021202000304140148503141d8030559445070000442c0c03103250724004043c0340c404500e2041c40c006441d0350758000240805050940910380d079a14054400c3c0c00c2e00400074000442001d500c44000350710543c09400204641401c0000900c8544400400c41d182c16625a0080040c0402c03903015004503d040d15a15240c01e000920510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 782214244 1250 782212994 782212997
    0x40f0c030e19022b060209042904020a350108030307080106031a060c07060206070e0303030f0703021903271511090d06050f0f1e04212d 60
    0x1014015500b84a200014032510100300842040107400b50226803804c0f4400718040c80c40562503035904d4041008803000d8820b1034107588030206000211040c003240e51545108121750058444265400940d0030650803101c2c0060354924103100032003125100c070424003007900c2c405100f11700d80c1c07242b512690f03e100507210000807401c08801000007a00c2a0888194000440e0040c94030129801c0420b13040d422651242c1c0141e080a5410320a40d0380c10011507034031800c1490709a854525500100ea141e101c09031029482c1c0103128001200c160103601110700100107a666007140590810006004043c03500e00f01080041500c0c1c840001c40c07880032440a9203400803124249c000105001000900980201000404091000c01e23150342e103980c40c004d082400380710041640c1c0303003200d40c09862403802000c84464590f24030501208406803051090307000c083c8000c1e12001d403220b04000941510b04a1580140c403100384000017060352140300d40c021021030f0920354070181c0b0050140c20080118148600 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 782215494 1250 782214244 782214283
    0x30d1d0d15020901142b06051e0a2105120f04050d1506080304050114040308031603060801061503050906060f0d030302120a0606090f0b07031d040f0c030e 68
    0x42118102d90060995a60505110400c501c40c2c01d001c500a41140824150282d034109041808113600708500d90103811101007003103024200310005000c0c0c0e00c5540045860940c201d142c415940ba8480c210015000e0340081c0034480006850011007030707000c3d03003040302e15005017054201c03411860b1054800c10540c000c03507582014142000d0040c08206410300352084409420266800300701885004050503100c0007641d511030515001400c10345441c407856060340c40c100300030804100d4500540780c00032007040030407003000c1e0300701822006000c1540100d5565480c2040014000700d90850003031070088240c03014400c5503950586030f92107440031140302d03810050844c051000b601d0f0160141030164800e0400604007100c0c8550701c91049000c407130b08008607a41e00c4080c04101d4000070312000074048607000201d05428012000c00c1d600400e8401014000381100d1810310300e0000d0176030f0740d080e440070f00200200c00f2000380400141c4555942200464a07000d04c50301c000e80040303000200c50880c215100d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 782216744 1250 782215494 782215523
    0x302010c0b07020c100206150603011206020c030c03160b0106170a020f0d0f0c140f040b0f1c051005040207020f0603180601120b0f01060c02010c02040b030d1d0d 71
    0x14035440700c024060400c501481c05881c41c0340d44d83c0102e4140c2c1c1012640200003510b40344440610407910356092510804003400104110072404c40c0d0510b15030361042c00540c81d074801140b400d25502580d8501c0019000100d502c5004110961040400318010829101e8599071450252986035450700e84103540c02c2c1032400192140c03001d800900440000d444070502d04450345d038501040351000b0501d90442d07901d5110070454a984090403100046c4284c40503440c0c558401164102845140704c2c210510320080f808880a2403800b0a07901c030b18540d906000c1c1043c5a48000e0303130050500701c400000501c0380c0a00811070b82041c1c4282c0b0400c99000d041c003036410002804001c41900300034283e00241140c140160b21214050081c80d0090100c896001e018541604c0d08103211400213080c66002c0507180d0040220700d5016254010003a020b08003e0b14601150000c1005000510700301303030702340c418074222000150340803128a104100039600c21203540c05001c02c00c4042c2001c80c1d03000c0e1111032100d080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 782217994 1250 782216744 782216753
    0xa030311160f1121070b0a1205070207030204090b0702101a0105030c070c061d0301050f13060e030c0703140606010f08090c040c0507030305090607050a0f02010f020c031908010302010c 81
    0x3042002c81c042c450242c103c01c40700c0700061030342944281d6161900c0b000c6039a010706600400101c406000c0ca0700045080c002e408100809590043e132020204984a001042c85180240400da018580140c000e001540c80d50500c170b003500e601655100c00510030b20007a090328421a01c01d5240c0301c0305c1c03010020100e500c030360011107081d08081e08a14510070f0404c4408001980744c2202c4008220a45807050750310310082c10b500c0310144100c401402a4104010400886222a00607a000950001c030065800a40c1440b100801c021203c0c12003d1000040000525600250001c100c034412004a560000c44410603515000241c0d120f50108500f03000240455000300d00e032503030104d20102100c108010f0300c000034007664044000c1100ac80e600040720824158103004040e8800c0b2214020302450900a400a0071840340b124083c0800907600745510752140701790010001622464800e64070750b84a1030b282030b20f81e88204400c443c42c020100321f4000c01e900840d41c0504880e0161100c1180076242c0d102d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 782219244 1250 782217994 782218013
    0xa1404080304030e1002252105100501080304060503070c1211070b040e0606070f050d0e04060503031201090b0109030615150f020304060c0816030c05160305100e0c120a03031116 78
    0x42c007c03030107120101186080031111192032030007409044004a948d64107000341083d01d0400c4a541083c2004014080030000104440403100c16241243c1c0d666101c900c11140043c21880040c1304041511583c5101d5a0150180070740034511016615000d07a05c3d502241c9500c114404c5103444280c00300022468078100002d41881400b072000e50590407050b41d911410306400300c4217080458440e060b5070165007080d11030b040190a05400441c6000494076001c050842c05105800384a500d400c084049a4410b040160055500660030301000c020300d041044052054050781c0c503850b001c0c2000c8403006100c0c030a0201c0703085068018615060400d101202d03211440b00041c3c905110811603607038507004a00c00d0759200b138025a1303080710845a61a120f82000f09108090408080400051011903030203d030300d8000c00120513002640d0303403002045a040c2100010400d502800030000381c80c00030000f15011200e0ba11a44d1b08020080111000740114056400e44401080011240d030300040c44200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 782220494 1250 782219244 782219293
    0x909050c0f0316170606220507030b0d0507140604030b180304260c010206070e041a18390d140901020c0f07050114030a1404080304030e1002 62
    0x6094803038094007036040b0030f842d034500e52100409104401c02d44012000501505411040071103169511185110401607040c840c00500c0c41c0305540c0d0408180c0c042c2c002c4e07200500c1c003a000741141c0d00201d50340c105551204030521502458401c610f11402140c90500200d80a481c0c1c0b000071701c990758481022605d00f101c111100c1180354401040041010a40c6110300891044840068a50142e1002c002810082c44041c8181954032074010710264a8001034640c0c100103040c0d600061241c018020103603207400c03496100b500101400c000024110101480e1445044452072070340311078400c2070070f9840c000200102c090200401c1c038421540301c8800001858070f07010720200858150b881c6d01040c0c0102c0010349281240307a5002844a40803031042c030003a01291811130141a200e0328000018088002a070000700c09000c0020000fa0036445036800741140e842003800c1005185003925002840394010748080d004500c8032403505000d4a0b0041d284601e09200f0745c081c22204200341688000d00031201c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 782221744 1250 782220494 782220499
    0x8040303021c09120207061e050739060807120905010c02060115031a271e01051017180f070f150203040e04111f090909050c0f 56
    0xc011501c40c280782e49034418070203510341d03500048118280c90044c6403d4a0800c1660a541214904025494010303207a403180d08000000c0350240303800300c503040354948281000104201a04504942c0c51009400e401203142d05091400c843e960f050343d4106e0315207075648221300014020343e00040e0128452113501071000d800010100d80101142d4440f03096070000c0d4060340c0140e00c01e0004220044080c2c0781c0024805407410b04020030640c2c45082d20006052829250064210004001411803a40070055141e100c01d4840e6945051401d0102030415050030b03001c4ac1407080c10700202d282d01e4400d03406010801c00b501ca01001c82a0004040301c0380c48000e003840143d008030075000071540b8040c0702c5200c0c202c0b0740d40094034445081c10340200c03002100e034108a64000820307500003149a0000b0845007642c0841040942c0c9941c0c92800d03d0f80090005140c9401143c4072200c0054010054014410900f0645900c100ca03503c07048414101c8000c400003500c4c5a001d0180b140c52402c0800ba84a03600070702 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 782222994 1250 782221744 782221747
    0x3040915030501020304200a060905090903130609090b04050108151801112701173411030a1b06140c04061e0801090c12060f0302031b100804030302 65
    0x7203480b1582207800072a01501e0314a1841c0e0a01441c2441c0003614201e4041251450099405c01ca8020050b5030f5034000c26008419090120344600010026036860079501c4101d4030401e034072050001c25a0215104100b02d242c2030400032005458503000b0541a644994003d2a6018000001c404240e07009040000c4d41c1c0c40241607040040c4d002e009441000006880040c0d840250f00c200d43c944c5041c0c4003d86d0300000010801481c1c683c4c0c40304040100c5240d0240e034111035140d0074a00640700c41541900c580f144402000490070b6880c00031000d440c0c6031503072141041c44918042e425100d00c01c078418500021001c0b82d4000b2070b50402d00001100da801400e00084100b01444a42403044040c0c9900308061400318042101da5404103065080b02e00049072202440d4000c04040c2980308180649840c00c1c0e103c0d00d00880f80b034070410300c1c841e550b0564402801010307501d1492100b4166540000c0c1d0003401011481040c1e4029411200b601c0c1102030a01c21a40e10007003030031945a03102a1049040540 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 782224244 1250 782222994 782222999
    0x15080f130c0b040909021207030f0201050706020c060708040501151401050a020a050a060519060e04110f1005040f080303150907180e011d1608090a0b09061501090803040915 76
    0xc0e82400350000d0000070304d00044040f01401044500c0f00d04400060403640052002d00028080c54201848281e0a08106480c1c000a2603c0c501a000d500004e427030501c00e040c02c0150180cbc0c4074a00c00d0145010b04001c000160386032078000c028001500883c41f15000303031408a069540b1401c020a83c0c14250310549000340341030303500c050410007405403e0f10265158028428101a06440d42160040c0c60b4010032005180c4041118550401007001d0400ca060600d01d40c02903d0b00740c5036a85840c4001e000d200d401d1a03190380070702940c11a0203403958a40c0c42c031401250440c000030460f8014448281400c0240e0310076002c200e11024010000c10403c900c041c45c020b03d60303100192134000307404a84541000da6051181c00c0700c0154091035165000280350307090043c0c108040d11780d021030018a18180c503981c0d032040c0f605450203625000c002c00c3c564034402000928600030911901840103030a0080d64541c2c1e02004480400080c0604111500308110803c03003c0603951003d01d1209400440034141d5a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 782225494 1250 782224244 782224259
    0x80c0409140403140324040e0a0f030917071802040e012306031306050403021e0307110102060412111c02010903020124171203090715080f130c 63
    0x2080352295548400010042c80109904494902e080d0302d11046003034114500580c0000300000b07031805a5401d182006000380c52501e941c0c00c41015249070a084070710f8849903242591501c01c603c0c1083d1700152400d840804c1030301d60b40c00d8960001c0c840701c0040600c282003c1420103c50303190000c680c51154208000a0746004031071000d070003051a021040d000760400b241c4480d491244640e080d03c2a0780801c20464216200042040c0c3c1d207420090025540c0d0390380c40c05030314088100d8803942c0031140500b4407485002c400001842c010344076941120380c2c452107000681e40c411050b10011300ba4510200002182c500c0340004442240100342101c2c403042c2d8031540110340c0c180d0b1002d60300050351035000400038580c090080141180c140b0181d01145540103850040c1c0307120501840120b01104071554660f210100140e000c07400303540600c00d9990411a440c50780d540d5152091080b013285158040140f2800790750814072500e00702589510554500644082071403d0901c03c480009040d0b00109007103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 782226744 1250 782225494 782225501
    0x10030605060f040903050d0c0e010c11010306030629040506060f0a0903020a030b010311100905010c0602120a060e07110d08060d050d030f0e030c121c0504050717030a0906080c0409 79
    0x24040d4640071f039900400b8404000b504c400c0341031103003480244a40b14002ea64004410b444003030700242103080c110b41000040300904040c0e88041c104038200020055030041720f00600d481c201505802418041d00e6a080c0000d440c8101c0da916170240091200c034901c1203040000300f45d140f40e186070040006403288c2c0018004600c0360000e640072016a401801000b0200c1c004182400c1d0466002d0305281070420024012195805614104101004c0020401200d83c050760000d0714a04500d0000d454070300c140f00001d24061285500801d0740d107005c280f502d405101500070101182c005000644040c01c8150346200000c0c1c00d20750405010725071903020850500204c842c0700310950340803035131207440401e41003a60f54078040b11905400c1003141003120100000c1d100c80c1034070010f14040c0c07100d03264903020318420001c122214030745052004004c10024041b40e004191001064034400201d0110f603000d90724040c44008102050b23802d40248001781c040c0d426142d20014120510b4605030b1602c5156055 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 782227994 1250 782226744 782226761
    0x83c060906061c050a03110705040f0e01052d18010e0f06070516060f09020d0804061403010b07060b0f0303180f0d0c140604091418010510030605060f04 67
    0x5800c07120a00125141c000b954011001c10565101c006035469203c0c01c1e1901c0c0004001801e0051072400c034183c0d0343c0240144802040b0080007008411503c45c040405021000d03c0c408907035190000054076003420080b031455589801002c00d8001c0716800c0d41c00c01ca404058610b0700c0c01e185d6501d507444030b86024001c5007c6125200c0c00781940c41c150348081846c7c00382c080c0c0803205101050080c4252036601646040324641c01080108201103c0da1320100104244600a900904842d00d0740080c401c08078000c0c403c9070f000e0350300c41080f250407600300303031450100380a070300403d1701d080064002203121a0000c40070448024040303890b0b100314000113850340d4410310501318110a00c2d82040c0c07a80c50592000307081000c1c1503603504450b01c0300e0350b184803086026000f00b111080a9043c25071068891005441c0078000702d01003040305800c00b0541c078070301810858034102c04c8426030f43d0000400d501030007024002c1d0b207074003031891600d410360f42c9070000341c600204a01e8020f19900401d000070fa0f101d0180f81603 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 782229244 1250 782227994 782228011
    0x271104092a0306060f050714190c05010305010b090108070201110d0b04140c1b0a08040b0d0e12031311210d0816050a020102190315083c06 61
    0x3109803031000300c032266084001070301c1494600030701040301c00c0c0c00240c400035500062030802d035161110302d01402c6500c0158220100d034031400901103500600751b850000340501540d44050001c0daa1001102955401d0040c50991a0f0510819a00d54021039007590402c2032400007041001c3e4500660b01103402c0083d400c03110a440e00c3c0e0724903030340c05d061040d510300310948034011880d49031061100c40c092040c94408a1140c81040400d4500a02400100b11032544140b28559856466020039240e803c104d00c2301d200e25140590b20790b200c40b0009020f842020011003e0341c1140e4940481d0300504000c044180c507581284242d80302660b80701142070590104800c034940f040c044201410b890b002d140d40c0d000060040788030600c00c500a04040e0f001c60b5003424a001603443d00c010f01c0482c003a000f5034042030b1003038190789031844171650141c100130103800180e40007d0002d661001d65540d42e05d130350b0401901021440609028084880c9914039844130001900c04d54140c0049035649008401ca40034203 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 782230494 1250 782229244 782229281
    0x609070905100314152d010b030c070f150b09060f0a0303180914041e050a02040b010302071b080607050708030a0b01020c0d0803010609171903031b0c0c27110409 71
    0x46c40e005507504464600c400e0a0285000e6040c00d4070703500e5074403018200e0f1101c65404181c08080000100042c460964840401d42041d01c401c11408098195886101e00c144841030004806041907020040c0704c203401081c4035011407464030f06407686629082124038060f10480d0208413009107000f6845001c40600414105142900b41240d08001c083c29894204004001800200340001082c0c000a501200c00050741c00381600117070002c0c071400310000c004039009207001515030808000d000860703000005841d40c0740d40b901000c9605102d084c5000f41007040c1803020070700703030001a031040c21980410700450b03070402c0e14200051000c5428080850f041d0200000500580f42d00a00040c001d01c240ca04241200e0010609551a0308034215654508410104100c0c1030510a1300041240d00c800c601095192140c0040104500740a50307040d518000410703000640360404165203070606000d0490071102d400e10300c0d8100080c2c9240624480205e81c01c0c4004900e1403294404c3d0354203020501d05a1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 782231744 1250 782230494 782230531
    0xe03010e030412060e03030108030d020307020c09090607081f030609080c0604080a030609060501211407050a02010b0d050712170a080415060303050f090a090608060907090510031415 80
    0x5500340d40100704145c3d019001800100301c0e4000010030703580884500400561644d40d441012032030030394958125540300c8680014014400000718000b4040c9906540340d00c03036035a480c191007010142d1419100d85888000c5030401c046007565020360303107003486011b000380b0b40035289001c01d25042c0b0a032420344010038002410304c030f2142c161007500d000f00b28500b0280810340c503020000c1d003541603030654100c04880400e04a802c066080c0d02200c250101d1041505040c01d001000a14940141220301d015610307061040215151032030a0220056011008002060a0124445001014503012282004020310180ca0b40e00c261020349a0300307041c1d641d6054545000c0c2482070307032101c1d09a208041d19103015000c1c000700b036220045a061b2106401c0300303661440c4141c003140000ca115402a14a01d2420002084001001c04c840f802101c019003154880c030786600c42c3c070046900641d074110101c03034800d00400000b15555003249030903c003201581c0c0c0001340b0300001e0b035210500300d07502100250308070181e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 782232994 1250 782231744 782231753
    0xc142d0a0206070c0b24030114160c150c0c0515040c050402070b061e1206010302010905030f0c0d020f1207180c020c120f10200f07030e03010e030412 66
    0x3802d9101400e4a003c040b01c150030b8071817010b215005410a1185864204961201d250f07103545a483e042d0058020440e859040349001031018080e6020a03282002001e115451846031040c4440300340c121251020301090300301503a0042041704400020b0000001c1484046041404490000351201900d5421403805150003440f10403075800551060380b041c0461400b080760030b60046e600000903a680301046d80c000b101101509490003200d580300180c004900740010b40400c1850403030380300ba290b104466840c1c004164031840d60b1b854080059001c070355501482e10300180140c0c24240058820f414101200c00819400304c0481030342440c960001204024142031401d80f1226204903410802c40d404d46002d009456000071030003a8422480c0340ca8000004800380501640754090000300c8010a10f80807140003c4d000d80d800c024400c0f0301000c0547d41d070708005400c840d1a440024419441d0150584d000d0f101600d042c40e8054041d0741e58581c5c0c03213a1340c1c010001000500719100794940c440c49603150 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 782234244 1250 782232994 782233003
    0x518151215042702011e090806060d03020d08060406030f030302030415020c1e0f070e0114010e060d0513200307050d030804171909180c142d0a02 64
    0x180d5001e54500181020b50202c41185112042c103c4034041003076403598001218010665000d2031000c002081c0d52442c1c054010840c0400c454120f415201c15590703644c00c01540007042d500c0900540c01246086040718842d40b50f15500680050001909a489884000d0502407001088021903800014002441641800382c9580840007405500d801040840a500d036088610b082c1072400c031818502004c0002417052802211400c1c080b81c06103959900ea00301018820302c10000321070801116007840303503c51141c03c6226000508100e20b0100d04122070001840004d0612a445000d40703001d00010306186500080c031b80c0c6c1c00303001c80100312101d010141800001e50125100700b40c0d00541600298001070502da02a8100d00d003040007100310b02d0508468460b140a003000d500c3c0000d10380382e4140e00030318403009890940d6105501c150290122908680002c80c0340d802044900070310407009104000106030b52100030000d00d4820540184548030020003a40071119001d010480c0040d0707660410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 782235494 1250 782234244 782234281
    0x525030614070315050a0513020705010207030c021503090d1b0f1203060905160c0c080a1b1e05150c10020c0129061803030a08040b0a0c05181512 64
    0x3c40d07801070a1702d0640020b100058502c41e281c010f010894031100910800e03815502401d8202c4025540d0718903a250083c0310100d40c040c00c0f440740480486003001d440903142aa84035030802401030032111006241902d0200704940c13501c0007103680411030750004203e4100c11000d03a01c40c075a8440240d500d820003130240d1344107801446100d8580000c001090b00d1994030120107000da41000385083d1000d05000e598070ba0782e070300005c0141c8605a00d5404000803102000000340891b00b4490740107403a80440c44115940c280070074600d003229007080c403540ca0207168144062005c440c803d0b01d400c000d210101e0400401003080700340c1c079501049a209200c805c0c01401180c1340070400000303102e9404c00700070040420b424002c2e405090003050745000501142080030443e900101202c0d260002e4041c020040c0e04116000ca908204990108100c6d0a25010b0612108815207a80e0300340304848815050a1800020b0203900c020b0300c401e109085e443c1e000050507030800d0700030081400d03e0000078140c490410304 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 782236744 1250 782235494 782235521
    0x1b020d05240a0209010503040b15122d15100f08070311030c031e190f030906031b050d200d0606080c0f0901022b020609060405250306140703 62
    0x10404c3c0c4030540e9008013242c2c1e2290740b04400020030345a21852404014442100c25040b00050403c0080c40c5030000304070202440c2d104455401c120780494103d400c0700055500526a03100d020b09422400d68802e0060f48000683e28034003006540b110f60382c0d0250707816408a00390350011081481400200c9034903004180c0c1c181c00030204111350301c0103e5941c2c81c13681c00b001d685c4d01b40420080c0c0410028020041c4010f1341940040c2616035900707107200b52000160045010502480c8000b500a0007401082c501080b01410b90b41000f0140c6070179295503011541d0b030b0314800c1e504e02120440191214225130790101c490304480d00c03a0406072800f000ca82154000f40213002050080060141b03441048401000c1c03d1446141c0702c50401c0d0040c1c4c50641d2020a9600d01c01e45103c407a40000d409800c003e4000c0c6980e401c60302c2a40752100040c0d00c0d540113450141503a00b040da6100b201c0440b4064450440e480e80340744904480e540c2c0c0380d520840c2c4101e52045c0002080c4421f20003043e525004419000484 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 782237994 1250 782236744 782236747
    0x5011704030f0c0f0804260609030d0c020304030204061d0702070509070c1118150a03080307180305070906180509070501081302041505100f1b020d05240a02 69
    0xc1d03180540041d5001c000c0b01c04201a425954041006940d503660095902c010215100c60700c44003181803015000820305558002c1c0106444440700c005003035406402d0220145d0700c6e150f0103080c40400b0384500c2d600c110540c0700070080000180c40b40e100700c0c0b00a11100e80f641d03103480c20302c41c400403181c00058460390440d40000c105008036a9607160040c0c0141c0c2a04055100c83c84030718105120a50350225a58801c43c05a80559048004034180d07109203058135030000c6581000c0200b102c58052404040c000c03040c24070000345158041e403040030202e40540620b00d04281c0c0e035511285010030b80e412403444103803035900801884000d42034a081015040d1400d20039440d115003c00d03541c40385ca00c600360402400b00049074445c001d0040780c2034210f4018100f0301c0141c48000144e40201c210f485014042c011500d00a442a803061300045954001c0d9a2100d600115050075000a0034040e50b0503640705480c0c00b124000260108109910092312840c1001d42e0300308400c07882441007004003500c110070700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 782239244 1250 782237994 782238001
    0x703140a08060d1a10061407050a0f0204020f0a120507030b090a09240605090106020a03140915070b090c0604050a1a0c070605030916030b1602011410050117 69
    0x8206050541c0036400b40c8403034100c09554107000018800d8104044c2c0703402c1110302800b00e5641c00142210954209072030300024500c8030317041c60307155102c0c03083d001e480d50300580900000144210811210280024030150401c110409603030295031100c0e241d00c01245003440301e00480002402041d07070041761800c00304000400b15011940e002c000400c0c000c030341980c2d1b85518040007000606540b15004182d00b8600550520038a180209814007035540305200e035000006000c1c5c40001c1034040c403585a5580e01142001608010b100c0d0080e95034154440c0b0000c03004000010482e000c0c0000e075002e046020501e081c0700c140716050542555515000307403005c01084c48142c482484604c1241c070414503210720011031004c40e007014000c810032121213025501001030f501c0c0e40f00c0007442c019003542c0240e400a002890202411926030702c402080c0c50f01640000381824001080c003110520180008240103200507003c8100640440c0c04002c2210204010321195a00207800010308400c444c001c446801c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 782240494 1250 782239244 782239247
    0x61504020f071202070f0b04050a09200705190b0a050609010803160204060e01080f07120c09020a0201180c18020c0c09180a060204140d0c031b0e0c0703140a 69
    0x202e0548040c20040f100f0940c009807520130003e00c2c0040c400c1542c03800d81284c07200c50a100c15409446500d03c50241c0e00e030702150224641c0300d9240d0908401c040001130300c618116940140e08045015240d50003001c180c8070100c02c0b0b40182d01c400a02c107048240d5142f810201c90400c41d40090041405003c0100050140400c000100c6540c1d0f1095580030540e45941d20001d40034110607040b4243e03190a440c0001a55075000494040d2441d4202c00e8403003254032450980030036008903030b01410709010b551007000b507460b941d401003a42c00c10358170010600d0f2803552a040d103071003200b070b0b0b049540d0946000304100045003590012900070b101c100641c9409440310a0507555050407030168861417001010410741c030050030459524050501c190358200340e1600700035000750484d100740c0400300d01c40d560191891814100c440304141d0302980f03072041a4107607100c0c10031400d041029403980701e40c40c54006c14042c2c50132007160305c50356036241000e60390700da02c3c54010491149040344002000c3c050000d01f800c60b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 782241744 1250 782240494 782240497
    0xc020105120a02031e130212010e011803081605030a051918050f01061a09120604030e0906010c0305030a24030c0906061b060f09080c01090b090f12030c070203030a02061504020f 78
    0x580492340d0002d88074440400c140145000d00c1d81e01401e40c42c002402c50656404003200704d5440c081c0d01d0300c203660fa9a03114640001410000080005042040016040c41081e40103d800440d0f0070600c1c9c2a1040404100c02160007000031041c501c200c5081c90420880204041c1100d0041030009000c02842c0c10b0303a4644500600c142801c1c4030401240c01300d40d81c0c6444a0001c001d581240031075455003060b0801a25006288418030f00501c1060009100b65010303010000c02d140d0b03d69101851681c400350600c0041c98508250f000445a20315404400380c2a400d03604051801501d842c1010f52500131200c046504680c400002c0c4000946900303c80b0040ca4800a881500118007190081580307500f10010824010010054013010032a01c0b200d0f41e0551001448034401c002c1c074103480c0c5038044107a50380c280e5812080700700d0348103615480c034490240d405960800e00c0d02c01458140302e403650009082d85c016100035401a4401ba0400c01a0751000b244802000c1094804516040a200002d00c16 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 782242994 1250 782241744 782241781
    0x1b04050a0306020c032511040c0503040f030e10050c06091902011409060d020406080a0509190203070b180307120305030105060702060d110a030c1e0c020105120a02031e 74
    0x806034007042280e10b40b282401280e10501d04a4004400380840355020303404100c0da21b0b0280e400c00407020004800d410a44070320f007800389098480504507030303036655205950500c901c42241006103010351030225890f08444061419900d403542d54a0f9000d080560b85041c038000c00b0b50420f40c0c006001d11078040b031180401c4146540a182040502c030f40383c00c2551507881080d015641000d000140c14a50300da241e4050401d40741c440d03642814684624200c00161003090b20310b14100d03044045816125403282100c1000b0301d10250a40f160550b0f204000c2d00310703400c5155043c400b052030583d003850925040c814a40542450b814082400c00d5944004000c3c0c001406054054800000d0a00039541c4038019298940c0d284141400070f0113020f255544590440c2e605c0d24040782c1894a0142c40600070348513404841200d50503903a80d420310b400110f444102444d8280c0c14454108010ba520b104d6201d092480391071b012030056982d082c80000510456680756620b501001c0d80c030140900c08a00201c0c61a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 782244244 1250 782242994 782243003
    0x10612020d05070b0c010605130212150f040e010b0306070f1722120201150321030b03030c06150d08031314010207031814100c03030b12061b04050a03 66
    0xc507400a28145203000810341050340d0442003c24914508941500510282c0f401500c00c500100140740014042c1d010b00039800c8004181880000c4080002e80c040b000c07032070710082000d0440a440d0700840c0840f90410b8829030217075143c2c080d5082da41000c015207030b0412002e00d84583c06140105005001e8001c0c03d805209058004000ca0715100301c424885c0c0c1c40520420366400811407502d8114000300c60712881c000594248a000c0b40c83c5e102c455000000c4a80024202d055031461421354420003451103c60014999103103090000740d101040500328410003240100b50b241886100e01c28003107009011030307200d07804950040340060500819a41c0044404000403102c0c41c0c2860302d00b00030820b80d0080c0c0c4580d84049107000a0651010518080c1200c43c0d40328210a0b84540490032030001140c503582d044264880e000441912035001900c100e0301a00d4001141010080011000c40c803a454411050340030009100c40d104071200d0700c40c048095144500e150500d020003042950031907220191 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 782245494 1250 782244244 782244259
    0x5040602150405150c0714030a0e01230c150f0c0a18090e010609050c12071413030f1a070e0105070c0f060305042d02060306040f2a0201061202 63
    0xc0800404000b400c0311910700c4e0403404c00c249041c008000103078005200585c0c83c12101c6203910150040441260a03c0d0f060307640d4a42007005031001074400170039201002012042d458840404c0005e00409425840e00200207001000440c02d00503240400107480c800b402101032040c01000100b00c0100c1d62030211034180140c045203c0020342d10380b0030181c0d0003c500741d81403001402c41e8400640c819010741c1e6180b1020082d83d00e90304c0142c0101e000f45040c403a00040c0000100700a0350146002c5104034100c000d1080c80e002041241c0031208642e81c1c0125011030901d030b0308a0812101003108550300c17a10310300d403149914044130700903d0140c041c0c1c1d49605200c4d002583c0414030144840000240108000021a080d500c6000030000d00045405640702c035602d00134060510151401c04a00400780c1c0d0089012107525000c00400c0e40c0080e08050f8003950f124004180d40e82c81d401680c040512200c0d0108070400141551440e0950104072102107915047d406c0c4900c2040707d45c41c0314910340545014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 782246744 1250 782245494 782245501
    0xa060203030106053405030307030606020c0a06030e07180f0501140a060e01020a1a07021203010308030105040c09052d031501150314090706030f1407030b031f020304020f010504060215 81
    0xc14458105e0403e40c1c01d00000a4486130078050000300071802220b56580070060650340d040e08903190315181403483e03480f1410724010440c4a1194007e0620100b020090b902c03800d0ba06d92501c2e82c020071a51800e4010754a421907621149000d02c84c1600402c1200344c0b0004085404002554800d402c0c050801800010940354505074420051503008030392044908084410a0801b10310440d03088540c0c200520034802100480902002502d04072036001c0e000c5800c5909080c2000b000c0e040207229031040040d45440000d4035602c00d01c120034511b402d4510b51141c8002508078440c0300e054019490b0181d800040070301d0303400f0324140700b080c1120203118080c901c0b40e80d801e004401600c8145401440703100d454043c4180311a02040080c01c070343c01620100f00d2045643c0301001a80d840b5002840d4070240348000901040c001d801c009040c100040680304900d842107560383d290b01108541810030b5501008200031400c204032110711500090804900302403400b00000c1d03072800030701e81d20b01c5800c031b10a021 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 782247994 1250 782246744 782246797
    0x1303050909071218050705011b1e06061403060601030e12030a181a09070f1202040e0d120b12030f0d09020607030c060c03050f0c0f0c0313050a06020303010605 70
    0x404000400554140f1a0000807089604c1010459009413154041c030f503030000d0035602468800c1801c84c0d030f1550208810181e46c0324a5921011041203588100541c0f444100203091403044802506100c58841041d01900701031501d4844010459414549090a01c013660140010f80084102580506680e02d0b41c9100c0300707074041d084060308442c03441d4403c20f50404101c1406105404038001c0c141c15281c0d580c4e0511303072035901c091520500940c0d0a0201d818404c0c0081d216035407502c40d001520119101c0c036050040c501d050407048030080001c0c0420800f42c01d105142c012041c140b08101d031101340c442c6004440c80c0e101d100745510f0305100b0704001512040c0c1111500311014054006004544445042c2406040b902840c6400c585061800c06152040c900901c0b5040c002c61201e40f000302c0b60b40e904003500289510040c125101070b43d0911113074140403010001030003400450342210100c107280c00e081c010f00d03120941000007950070a000510142e5800070031786020260100303012500f807145001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 782249244 1250 782247994 782248007
    0x3050906071716020a3503060a05012604030e0114030906130519030905040f050f0601140403051629070807020a05090f0f0604060b0f09040b0a09060e130305090907 72
    0x40840861200e141203410301d05003d402c00203018020800034a22800c1b10000703a00c01203a146a1200d03919030140000e510550401c04010107203001e0203c200703014049000b119070f045070200c0000b05100c1c0000800d580c06520034180c0501013202c10b0450514446c1c040d29040c00030569a6000c0c9880741400c103004c42000b1350050281020040d101c1100c0d2410014030911540c0501c60045d03040c4000d1a00e9140396100d040d11981803a0b042c0903141c2c85100044440c0d41c000703148030b2500c644c144800b02c0880c80a010f4940e5036241410301c3c1103220b16203a00030180c1d80e0105540303803006000c000d0400c2454000c2d403c07604859070050300740da6650458030025110841c6900031740d402905400403c07101c000c01d0300c8018000e44200403480c0d09a944c0000f08410381e0440d01035030301e1240f000c0c003480d074140090700041e01100000600100da8074070418041001080380c0d0740032441c002d4603240b0030010115083c15280d041441e82c03d2002d0715840325107010304144a02c80f01e990103244414001410710344a40c8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 782250494 1250 782249244 782249263
    0xd032703080310080105011203080703090309080f0109060b0409021c061b2303060d110402042705070305010e010b0706060509130b09070509130602040e04030305090607171602 77
    0x40151241001200d500f480c4540340100c03560b035860400041403000a220f659a10a9895610501b055503143c20440203844410011001d1040300c0c1d00104004c07405028003110200c84400000303409410341081401e4602030b141d0f00d8002d52811340c0305800f60706c030850201010509003460b41138408240c5804001030280c000310342100042e030041c2d80074607031784400028000548603890451345210031940c41c1c00340c44161007684d8040d00c041e41b854001468a0000b11000b070005100500301a134035490080c90f2524088259a0740c0c001000c86c121043c141d01c42d403034004a2510341000658104880d5120110060185a5003004041070b0301d020490107030000c401404010b0704144640c1005441d1180b0450921400c88030340c0303241000108441c130300003440c01c21104001c2001825842d01e180e019001d402d00c02003507807a103408000110b1404148034100340600d10075940060241340414101d814414007420300420824002d2281640c00c50402c1042e0f0816a000340e0140a5450600c0c240d18121408 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 782251744 1250 782250494 782250503
    0x2060702060c0321010302100906020606010f02031201080a03180b180f0312030610050f0405010c0515070905130515060d090507030812060102280204060506190207050d032703 77
    0x8003c15013142039100001c0d41203038426916100d502002d0082942d06031510301426005038000c000103201584144030003170250b40f141c01a41d2074a002c04454a0b0211002d0300240ca0643c01041640100350b446070b01e059806103011008260030741000006030003071140a51518103800300d480104802e9071195580015880c00a040b80e20544c42c5d07020b001800d0f00216100c51042c4018940c500c0d000780031300125907110788803010181c5420308041c019201c00034242c405942501c164210341595410300710380d0f00e006811b10b49440300d502d80307880c1c1004824500b244038064814203000a000d540c0a150210148042e400c8555544030007001c080400100203642003d0210701c03403035000205224524000b0680c00c03040e4104403100d070365038200583c0c0c0c40300000400013000200202c1080c9405041200032440d6200400100d2a20764641c00a03065410444039408000740400c0c01c01c503480d80402100000308019208200811103e0310007800d00d055240035a13422150a00381440c1e00510340021b017001d103900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 782252994 1250 782251744 782251777
    0xc0c1203110c0d03020705090405160927030e0d0503161a18070b0c010b060f0c061b16050703020d030c03090e040b1807090608012702060702060c03 65
    0x508005084080707000d0500000d005054946070281010519010801d4050b00140304584c5454140070842c80c00520950b03050142e0b5600540c0010200c5c942c42c010070003200080b5a41600581855403411241e0348006513030381e06009400007a81041c1c4801c0004d000321491072904200303061240c150b1003401025402d0442c4c0035580c00030860309610070001e0f01d00c000b032001100d0355003071080d94914080d4000095540d01101d02041098001e0009141d2600a90008101000c0e21004034100703401c080c0740140800070100310403550a1b810895654000540281480c90040c1d0030f4002c24280f00360b1002c07920030302c5030f0507150007840010040784006550140555050f1162414018841c2e01403403000c80004008000015101c00c442001c1402039410402c0c642c3c01d611030b03c941031040071129a41030080d0066600005408940d4032034640240394000010408501c0300400e00c0e40c03a031100883d006034038880704840d009030b03d81800340c0d140307a94165902036807150294201d600d9809490ba520b86c0e02901e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 782254244 1250 782252994 782253029
    0x110d0b0c091f0c14030403021518090103080304020108090c2b151b030203270c0306240a0305030d0506010507060f0212010806040b0f0c07021201021209030c0304060c0c 74
    0x611003d0f1080c00b50091003070041c0d4684020805031207100e5031101942c80481103a001d1105042a001071890b0552002115074900e8035002055083c1026481581c0b544000f20401040d075030040881c5600100c018094000e08a050001405c0301e0070240c0d626130503030b42221fa4492003003840c0201315401600280d40441e22031500c20028098000309041000f07450741184114403180c040d00030749014511030340c1c9200300403510429007154441d5201440f80c0f01d10900201d1000740c0c40c00e000d0720707004002120b805840301a54008034003841c802010400e00a080418081020480210035210311110b1040d01049a8640c0b42c012111401100800340c0140e142144100c2d48034880e034004c02d4000c0c2070103d2000581c7e6a034800e95240c070300445010704034001c0300b000140301300049100c49603c0800f12456030b00f000c2c03064002c554610001080d04150360344c00030394070180c00041e89403540e114610703038000c40c5409114070116480307014510a403010b02050081410030800c0c14100701000e04000701c1d10341039140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 782255494 1250 782254244 782254247
    0x131103101506030b010804080904020f0f070609030f1103030105061e1b16030f0f031209050a0c0530070909060b040c05130b031b030112110d0b0c091f 66
    0x708144504800b0a01e014031001d03640d4014400644901d80244180d03040051030001c0c08040e501100c0100902c5400700031844000c1c0000c0007804045009190006410303582c0d2802400541d015040582480406420342c024013000000301c0741503c40513201c1a4456491031883c65496445101c411a08a800f1880510103030280044100f81d4030f0340384c2101c502c41840c0d15041409151400040d094205c40d00030040840c3c5009000558144246495148561445540c0c01101c85814080300c0c5604003030203003410302c5924011440504000c464030030303100744404610710003000141ca241d01114021071024141300c0c010b000c2c0600416071000d06000c41081c6281070f000405584032000d1140c2c0c98020070303000082c400d800380c0c0c1c42c004510341a91903407418800303114240e03000200340342181c4000106070380100901c20040c600034544c12101e510248000d103441109a00ca85084074024003141f24444041002003800710f070005a0700c4501c035a55454040406e901502d015070703049000d04940510420b0300d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 782256744 1250 782255494 782255531
    0x1118120a050327010c06020703020a150e0708060c030f10030b010609060f0206012303120705030705060c07030c0209190608030301081006050a091e09030c0b0603030313110310 77
    0x84981400081c8840480054801d140b1020704440e1300140329500910b002031826401000818083e004a41c0d080180343c0d00c50341d00c860b03072000138411070762950492505900100500c3c0045c000401c0038161514021100100314080180300c01060080000418150170b80148004080c6802141c8509d07590313100c040140004015118440004458081220b0a14804208141a0b5143e660005400224400b100507011820000c0c142e140c0a81c54400e600956014024200244103002641c0c43d5085030414600b401801420700000e00ca0404c19100000c7d4000c8084104c2c0d6030403922040a070b103c124a00d0202c000d0100d25001840c03070400c1c08a44440d000002e10704840c114002c5440d40d20030003c80d075050b201e0b2031041681002c00d84d074080c8421003854100000148088003041a141001500da2040e148041026400306c0c100500381400d00c1500c0000c5c9a000c1010340080d861410100060707030a091202d0400b07448490f079103003601c00940c3c083c4201d0000c9015400c00b40b0240c1c0701d0b00003003105d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 782257994 1250 782256744 782256757
    0x110f0a0807120309080a020d1205040f0312030e06010609091e0525050a080c0c010902181614090f040e15150a03260904091b091118120a0503 62
    0x800c0d03004c000041d28110010b0b00c028426030107882e003041e40381696207040c441c14220807003005001060101181425050304554001d50141903001d4414820300406411200050002c40e020341042c030041c400d040e00b051501c022120300950020b52030348407070200d02d1610004d843c40d20240d4140341c288000c04419071a00036160300c800c102840020f010f294156041c1c0f1840e40c0300340114a613840059a1a030013070018140304281d920002c90f5092190b0b0000344c00025a60421108400141c11b220740800300d50518800071045041c001d4019041c4803e002c034134083d4030103070f500c1030290900f40c4680791920340007010026a807200701c8944e551800c20300c42c1070100c22180d10340340707810310440d4850b94601502c240342160740154025042100c42c0f600c81e442c0180300703c500031100108116010315610b9a00c5011982070041180c0c840140600c25119200702065101c0350703d45040021718034140034518101c1c0d12020003040d161296680e07403400304000b04596404201c2d2805258461424401c001c4000d105 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 782259244 1250 782257994 782257997
    0x303030506100306080c120a0212030d0c090513150f08030d0b060a0804022b120f02280312140402100302070320030d0510080f060103110f0a08071203 66
    0x101030320394840c1103007290a248035035806039012036640700043c203000141070487c10290060302d03120121034010840240481080885a50002030064140b80f00e5101d010324948141c40c111189503e032000203403c11081145071081d090750780a0b100e13100d01f809c0c6001d00007040e6151004054a603146070b4107440341c01081640070002c3c24040151118608141154844003003503d55806503203454080c012088a130341130495202e40c1c698108080050010208011148907049102800402e01401818002540c80900940d03102c0300c0c0701c0c000c542e42401c3c4168414413000b40c003c6079200c2402c003150840700301403144810500c0d004408541c004d03408804c41c481c034001d80b103200d120354541804030f0881c4514100a80018030540a40a800f40750811003446070300440e044a04207400f6480d900d080320b030203071000716200c40c0c0d100742003041400038460115142c002c039000c0c3c92290f00d551610302d4403140c1c0300038403441020661100ba0030740d624010440003802d1000200c58416480c2d400740d08000142400940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 782260494 1250 782259244 782259259
    0x4050d0201060501170f04020d050322060f020a060218060d06060201060e0c03061507120806090901061d10120b070314060d0b180d080a240b0904060308040303030506 73
    0xf125401030395081100c00380c1206820040d5640c40100c4840000034000700d900a410900f00b4010450403c0501540341c0b865000309100409408230010318034003030344298103001c50f8085000c1960740104881c0b0004c4c1d00104003598580003285901c0044030707554049640181c2c08592401800741079400b40d0290303000c40e00201b11031911648181910242100e0b440070102c1d0410020358181490041150600310902815082203059517032550340c1d24110405a000404281c00c2000a1a0075690a03420000c003030b00030010346041100202d90000c00000f900c00260042011034414844068042c0042484000445c0d40c500c8c01c0c58001c160220645000c00044e081100144016500f50802030080a008180c3c1680415580c1c581403024001400c640300080101500c0442010500c035000150245075074500c4030f0302c0c1850740c890840e00640607080590440242c0b81011400040700c81081c0c2d4036112109442e524068002030290115400003004e200c004900001007540540005003d400b08940d0300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 782261744 1250 782260494 782260499
    0x6050108070f121b1205060f010b0f091c060507121b0f0c0f06051003020913051207060f020f212710020a0c1b03020102030306151204050d020106 64
    0x50122505000c0c6030320800030f408000c0005140b01c600f0210300e00e641da412580c441c3d80c1d510210b20300c4044543c203460a401400030441c4150005001501605400e4200f07424801c55010442d21030148201e01806604941d110500260300d241c5002c60b1242e100720140190f16082c1001080e00d42c92a90305c0c00c840e810700c449600e40a47d07480c111007203a01c9c19507030a04010340da08400c6503d00c2d940c0d02c080c2e41e0800130303040080200d02c4500a607480341218055141c0041e240d8414408082c0e40144401458088a08084d00241e404680c40c00801d12280e261500c40b01036050610050a43d210031608103440007035101c81d010405d9024018001200307441402c000302800e0103092071403003140e00040c0300700c40a94500b010f50304402150340a01502084600d80d41043c2c1d8848101d9000120102c0802c40100c600c800301300640700b144527122031405000c070f0700364a1540044d6070380c04040c002c04e21489483c900040c07622001c0040d41c0741c4841c04c3c0e00701381b5a1300345400d1054480c82c006404600550801c84013 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 782262994 1250 782261744 782261759
    0xb04021306021209090c030a09140c030706090f1502160603060e0901050f010603151a03010302190605030c09010c1209180c12020c0304150504151704030c0606050a030605010807 78
    0x255440344070080c01140c000c6c1d44240110308036510081c030030b000d81580c1c0c50401003c203205038501c107105140c407001007542c800d0100405142070358941c4034504014807220b06004a030f40a540070006c43d05625000542c0000b418400d0782401d03085519101034034040000010b015506801820880b41a803884644940f20300503410300340c5400300c40c103c04c0301c0591401001824400e5201c60f810214070500400b0031601d0388250b036000c01c400061010f10b804007000510035882c0080d40c1414200075440c05813200f52900c1030107402d6000040084030b14000102e01982d00741d00840c00050320715804405d5140103d1005400341c000d02d01ba0003411400d0b80c56084071604081603100c0c4640a14940d01c8080b1280ca052071800c0181d40428003102541c0800d02000901d40310340c1e040b04540c010607032251500c0750300b00610b41451108000f1100c04100c409900c00c0300c41503000010580007078044c58003400c0c050b46800c0c400060304480e0f1080c1e8020400800c00028840154032541c141c6900c142604c0415507036914 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 782264244 1250 782262994 782262997
    0x40b0d021809091e030405120114070912030f0c06050403020109050606040e21071a04050c0306040b01060e03010b0a090c1107060e0d1a0a0c0e01170109020d0b040213060212 76
    0x82c0482c003644a0406155a0410341101c99070a00c82002207a10300360f141d47c04510054000c10b05014580c0d1100c0b080581000f04903000d551000c81440c00246407464403070400ba40380407051029040c041c503280320a14507032003403003101c60807a000b0340c3c1840642841d2400a00034a41c07032a0030746140c0108400310709649020300841003885801c0700105640b14030089101c1c18040307503078101c030106101040524002559104031180c20403070900071542c58542401e00758109042284140e00c681c0110081100003a00c040300d06040d0b13110b91500036000c0c030f50a000b2a0040c00710143c401d601040350349001600d8ad1454000110100c299070780c04400240903055187e4a0825014a002090419804e080e6a04010f150389003254002c505540341800702c03021a409a82007a82d601001d00e0302c500c0816201c2e900411114045d500030710382981c601c003840e40d100c44c29403c1030003200060f50b000208610009035a4100c2c4040e02c071300038801c65640d8183c0402c0e6070b41d4041803003040c0c054003a11b01c00d6000140d0420 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 782265494 1250 782264244 782264251
    0x4050306180c01030c05070b01030605160212310b031005040902130b0d1e02150901090510020a0204060b090f1e210f0a0b060f061e040b0d021809 64
    0x1005281c501c0b5908015009401441c40120400105200050218401c1c0e508580218058000000c80c0d04000040c0300340c1244603400b110955210000780000c02e0721020460790b02800c800d0505240c064243c0d4108051024000d140301800600d0346c001c0b42c1041058019405240c20003940c4001550b201309000640300f0021001e076101da03000d9480c03000f010154001c030700d29000040440035600340315030310151a9075100f09460f07442c030400780510701181042c1c4d44982104666a8606042051107000200140354034042c2600030316480040c210118000c005884103254014004d02c0104d40721000c41025400121100707214801581003030007103003000b82c900c40604031011003400864400e0000d001d9002030390404101095140c01020b01002d00034855176404d00b40b420042c0c0200c0b240780c1068105404050811031142c600291483c55075503c80c0c086038001802c180082408a40d81017040d0241d0103164003200950320000b80001c4c1c0948240c1c01045040740000802c45810507500038041051400c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 782266744 1250 782265494 782265541
    0x20c010207050d050a110d0c080f0c0409021e1528110304030f0c0e0408030a1b12151e06030501061b02210d020f0f06060a03031b050106030804050306 66
    0x4081070012884d42c407148130000101404450102103190340c8d040072100103500c03449003500b158070034a509180501542c40e040801311014000b10b401500010321500c007540103000410440c0c0500450f94541559030346140076024810703a00c540600002c1c0406044403e100c2000d004c0071000518000e0045a1101c1000395600c01582010306645e1440306268079a003041d0346c7c004014900160780d060074100d80d44120f00c20f03201e058984c240306c1542c0d0141d94040006040d032000a111050071035500441c8200e10b911000408203441124100301d004050240c2c1000d06500300e8030030010100303910b0508010845215903020072403aa030750401160090141c59640140c06246034105000d442d00c0200c42c420070391250b240203100c188070000c8500d442c83c1403440b2000340e046034490490554062001e80182000c0b400a80000d150680c009034103c140c1c0e020040a001807140410204810052150700b82c03075001000300b110b16108e003040006a0094483e00c0e200b407060b0703000070b108070703040b40d20804555010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 782267994 1250 782266744 782266753
    0xa140d081b030112030c02030d090e0a3b0a12080c1206040e010b092427070c050322060e010c02011d09040c080c010804050a30020c010207050d05 64
    0x2c1c4000044c2c0c1812001d001d6041102c1d440d800720141c2e6042c08040100c1004d9114500458944011030010600090040c40c103140740803a41c4000050000c0c408940142c42241840001103503070b6a9480c210041d01e0906851091010300410042da01c013000807120519251001503a0320508408060720038041b400004119040100356542025001a90380b01c686200100c0c00d110010041820200101c0e40395140344101c03540c1102460361100c000044500c02e80f1000c08888510003040101d49040d1800580c40c5181030010302201e200d242900c05035a807000c252030303641504419001102d100c840d14254023490207080014028045d200c64025244103071201c0040000c2500103542c05c00b0301290741003e00d41700a1031075400da031b544018103105922540d0698005d0781005030051a080003840141c0c1405840410312010420000780c1804040d4044816241c8244100408181c41b03051150404403030041c0701e00541c01c60b008119000e01c580c0031b0303084541041d907031000c00c0f0190003103180103802e5030131 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 782269244 1250 782267994 782267999
    0x1060c03080406110a180b0405010512060f0618010206070903050a0b071e02010f0c0504030308010b070c3203032b020c120c0106091a0607050a140d081b0301 69
    0xc000082e402030061100085071803c25025820340d5109040410001d581d00350000701d030b1051120349802804402d000329003054244000a8124400c41441c100b05000110008081c0e6a842440c43c0400c903020b032082d5250451031018065140c00250300c1d034054003503400007911360b80c4034119000441c5e40000c01007105e00d4541d00c031a142c041d40602510100044400b606004084594045d03c403001603600004026644a1210007141e11a0142d01e00f04081001b00f0030100b540700e10918155600715404554440c6d181ca891070b2048a1a4000f00c0c1c60110746a1202c000b080030300904c212691126400a08190b10000705030302d900c15000c948602c062105250400c0c030041d0f038010316040384011001443c5c0714980202e5072404091044010400c03000007a8001c810740d0a0082da0004d00170868103020031001c005454070020b8250020502455001c9a0341c4140f0008001c4d81000c241c00c000c440c9116940c541600340c450000c1500600800e1044011030701504001c0050108018600941401d590 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 782270494 1250 782269244 782269247
    0x140d030f0309060e01051f0b03010501090b300a14010b030a0c0e12030301030521190e040f0606230a1107090e0c04180302060a0c11070b0909060901060c03 68
    0x40e003a80160386850765a441505138510900c00c850045c440e1880034400b5200000102005c081917402c440c0043d00141b004004170703600301c8501c030700341c901c0320044070b46a04240061201a281d0791a00d941e2503007412039070b51504498800c01c18024502440188455000c8010f0409400420310412412203810000103c02c1440d5500000c40c82c5010314200e03090008441c00601720000071141d20040d600000300400c10080e0802c021094200e144c241c0200e010307002c40c0f002c0c500f030007484410000100d000056410f9203200d212402c46c9803030b0091082111840701d842d554010071880c0110b10200721581344c41030004842c188207004500301034880524000c2c94640480d80c2c140542c000254600c65100f003c501410503000307180b0440d030300b5401840480c200318200015109010080100110b5480051000c40c1d03010039080d07480488203001140d50030841e00304441d544050f542d009014041c2200101d403000b009002404c0e040c10440d0760215a4442104100c2242c0081c41050080740c00c80d0314420019 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 782271744 1250 782270494 782270501
    0x2041d0c040e03090306010e0708100e0604020d0209030303130b090c1c0501090b070503060a0b12150f040f020c07090212070c0201030221070207060f021b06090316140d030f03 77
    0x40404800752400c1542c00307000702e0b103400e00230380141110842e0341c82009040703984000c1c2240c4c0040c1c0c0014289880c1e01d8218600122040500914044c7c3d400007084245040e40d50111507000b00301608580da41e140c801400542100c1c00c1070200d070b000c140b2801103401100009030440b103100c0000c00c50509250b50404e0844100a2503070300315250354032480100041030380c10381854840c18080d15256a6450414100145005d064008a62035081446110042140d0100381d5520024007080d00c03420462120002e80c81c01d620010255000d410300001140e4503859401a2101c01e080da0102c4014035220210001039000356400b881d0014500400610701c51301c203038800c6078114018140185402d007480100c24425501d04000d82600b5007010034488081c4d030400c01e090040c246442c0c5802101d50054000f0345800840201040c0c0c07400c040001c000f141e0700c84040b036040510042c01c8031007004040c2280025071810307208141903001d400c1e43c400301506283c50000141c0758503580d680d44d9407642000641c001c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 782272994 1250 782271744 782271761
    0x5100315090c051c060b030f040f0b0a0f0b0a05150a0302070c090b0108130804150207051305090f0706140706140117010c02011a01140d02041202041d0c04 68
    0x4503100d00d00300040c1c00c24188505a001d8907903942c0c4a5030303040a290900001e5001004441406180c80d4040100412000903240c0040203400b0000030368885003021281e164251300b02070011400384040c00481800c40e803001d06500401d240c28070119166104000d00c2e41310510a290f082052a44040483e5a455009284082c1c07a03040040c1840940e4070703038180158040c1c101451803903980600e08113560b0050551640310f070420314280c010104907a140182e0740620710801c03909800d521030103503c260080c40490003820001c1c003250381e141001c41d01c6402410040d81d10f40e410303000741407a240030800040f9012007a00d171070b40c440640c00c1c40f61401c0e188455000c807500303640713955440950542c5c01e811901c000b0f0003000d1105020303845100b8a00d2050840e0480d0781d107241035a00d004200e442096100901036250f0070300742022800e1201d80004090030744904400d007440d0520001b0003007102d00042455410090003605c0070895090743d0041d03003e0030140c642c5855603540c010403c0c5481454980c1002c000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 782274244 1250 782272994 782273021
    0x40203480a2d03030c02010905040c1d040b12010906050609040b070807050c030715050a0b0d020904020d1a0114120c0907110703150f06031212152706051003 69
    0x10803181c440d11002d03640c0007a420071000241c030b5092003002c1d50ba120712400301401d0110b50030171084888103000f030000608081580038100d1100660700503541c8a0703000c0c80c0340d204080c00c0319010f01c61407442140280300d00c2e1800c03a66240f60101081003803c0c85101584260761044a40d80527455540c0b0545001600400400030441e042010740c00c4441c00380090300e19207204132040040341d108080d10170107441c07004140c02e0b006443c1908070005c95890002040340e1540580e8000342c241c80d2800464041301c00c1c14000380081a034101c0350034400c0102014681213811660601c1004c01c40c110400840c1441e055800300d0301c0c0d00540c1504420702e040001990480c0240c240751605d40800c0403102e00f0302800380d20980700c40d8a54595042c9044c024000c3c8040d1207100c2c00c3c01c2010600f143d4440420b198030b041c5c40410000d420240d01401e007001d6102c1403181004001d003052096a801c10407181060925240c19079510303607614601c00400e54081c0700107543c40103000720341d0001300800440040c00c00d91014074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 782275494 1250 782274244 782274299
    0x21009060b0607030f08250302070c05041503030f080c090f0a09051608100b120403110105151003090c0b090a17010c020d0f0207030803040203480a 65
    0x2078290ba4400c003d020052107078407040f20b0441100405003d100000300a4515840d4440c1042200841c200d416a07802c4a54100142c90320305a080098485500741c09c042d0700540382c070902c070514050410300340f41128070aa9070301042d101c8482c030480c4c2810082d2402c82c02c81005000250003442c2c405000701e800d19026180c2900d035941c82584605644042c2c45400d403856248287c520000da000e403000b80d20003034212201c0b2500c2c0c500381024a0031710406010125141c110404035041510903401081c0a1070070704024171080c00c020000b440c03103000191300d141c0f0070b044019410121502078003600702643d412810b02048c036490508043c031990b00103001540e002c161380c10f000c940001d0442c80c03002d85810b05800000c001e00d40c4040640307010b0340e80a1315824007d01ea04069589540080c010b0300741c076801511103840740c40d2440864a0404482e1810101840e01040318182141405610000c550501404c442c0c00003000e121002400d07113444900d4011410303820910001186a2444082540b019641c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 782276744 1250 782275494 782275511
    0x50409020d061a0f0a0308120705040317030f0a150303050307021f091b03050d0e0103060e1618080a022803030810152c0d0c081203010602100906 64
    0x1c004035a0040c06503203c40800e6034900103030f070038039088240c820300782982d032042c5d1141140c642071254042d08100c40d11107854030780001d000511600688000315404015451100b14400c0300507140c1e0012105200014001c20000d0260759181c01500500e5030b21659020300c003401c0d900e0480311903000500000540c0300340800b018000d44510803101c481d0030710010008940c071841c500211103981e02190074255058080040c00824000304240900160b075043c01040009400010b070050321103903029a07a20b200400412041001500c0103904001142c3c2c0d405404e80003446a10740010310034020828154400105074005050812900e02c403560805100094041d400b103400c0f44207403494104600181e100f50501072101014105103000e401041c59600c00e641040c071005110103660b4075203d5103000c4454000d00b0f03511107040c6a060700000030709001c40b485182c0c10081d0740307084a449080f42a1141c030311440c0c1e10003988802d4030f068401640c090030b0841c8482c924407020b00b0030408162034096030351702403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 782277994 1250 782276744 782276753
    0x4021c09060b0a090b03010b040209131a0a06050a030606110c0f040b030616031109090601301a0a03030504060c081606050f06180a0e100609290a050409020d 69
    0x10070004150204021a482805c070b000e05080d07a007140e5010b0300480c01485040304659901c0340b8103a80705841c840c0051030030202c04100c11901203060340039420860340c040108080d54407500402c6c02000e5914148041c82e40c0340000c45464405229517181900000c40390285460601034620a608000b00003086c06504e0307100082c20100b050380c00103030802280030084201501405003034a8041041042400c0c421030002045016400030680350411140d03402c0c09950030079081c955400d03812043c1d46040c10450100059000705204000017800541000c5120814030b403104011056a134156100303420302c1c0c41c00038192001c07074100d4400c0320145da0a01034070300c40c00b2280180d2a2064010a00410303241013002e4240340440c0050503050289a0091540342d04070501f00c0c07501e41014040800040c051201002c3e0f83c20510742c6443d40e0b100c1d608040c130000344500303550004c8007002c00f14810280b0341d913400c0045181c403001000c0001e80104610708204098a000d134040321a0a0000c5c1203840e0300782d0321769074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 782279244 1250 782277994 782278009
    0x204060302041d010806180a1b0612020c030906070507030501021809060d0f08161b0807081606200303180c04090b040b0402010c080d060602060604021c09060b 70
    0x411800690301207001c0100c031050216101d01d400b984040302c212541032141103526100014001c1c4113001d107003001d1101340d04080200c1d80e0300f550800203e85201540c851f201c02111072604c11100022415801400010024400c032012070038030000a628021800003404025080300d003090b41c450180e0100080420400c2c0010101e5280c1206205a0398001030100041c054010305054001c000030710b510800505000034241651303030411a42a107964039180c529139a0904010300400300c03520307854040f2980300ca03c507015042d81d0580c02540c000c95140d00f042a60703503070038006610003981200f0003000000d010301e04880180c40030000c01c02c07104104494442c6103038800d0381c1000008021001141844205002100c00d00328100c80510080009440f401c24500300903201900111022010800b1603008207a007410159004e40b2058680c2d1540b4940c030000c180c10720401015004a41c0050360502d481d100b05c1d03d000400d41a403c0e800e503d20b003401c400a0182203422240c007652148002d103c0d969118 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 782280494 1250 782279244 782279249
    0xf040312050c070f1505070506040201120f0e030d052a03060103020f0307050318070f0632030901060e0403140a0e0405090f01150506031602012705010c020d08011401120204 76
    0x1003070300b008030b0f1524038017451050783c10400804103d018484400001c3c0042080c9800680902c1c0410841c5c0201c0700000060500503601e5060034540040c400c81514044041e160034070110f6030400c0a81d80d6603011102c6191545803c4010b40356207810b520020b91204c01071500108180b50050800e100f000b0841e000394400c0d100000030810200400440300039184098640107807540240170b9241c90041d250180c581c0902034507050000301e810381070b40f4201890310b038880070140b03070004980100841613080d0640e1095a440a940d402c3c601e012416030328002a2601903641540c64081910101d132146203280c0210b1044401c00c802d1081c00f0380c070b0356628059a07004505200190030101d031034030310941c211291442e00e80082c01c50284200042e0741c0e401c0030b4a030300004c0b1001c07486100604090482c0107110b0320700000d0800b5500d404a115103188419144081403003000200710364070302c1c6402031340c1d100d00007040100000c07680d10040c0503251310340515000c4038130181001d410031000d000c2c420059800c40d4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 782281744 1250 782280494 782280509
    0x4060f06121202011b260a090b0c0903030a212a1407030315080d05030402090f060f1c020603011814010303090501030504030c02040e0c090109020f040312050c07 71
    0x241c140d0001d10920405a2409450900007040f410700032150a0282c0b10f81200018280803684840d8109424071392210003200c0d030015202450b40c68a4021500101414001078800000c0301c000202c42030440c1c008c1f200320000c020001e50601c40008000c035011039011030703420821501440c06000c0075046014000105145113007013a460040c0e0300c111045e405600c6552010802c41c500d46c034080316480802c0302c2209030149800305a000700130f404c1511841d103d9104a0041c4204144011a107500c01c010314089c2d842103420010b26140c40340c202181610a55a8036030002510448038030320b00d0900d000d42e0300110344c01c880e0040c0e00415000a20150001d80c020308551b411409440c800760024442c1c85042c900082120282d9411074500070010706c0c0c2405280d0605130f494010905050059103035199031030380100107000c60000c40e04402d4a55064222090144501c113001044c0c2980c1e50003074600c049a104074040c00c0510f0b646400384c60703001d0b014914080c0101001440c400403002d010400150a90 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 782282994 1250 782281744 782281769
    0x50907020105071206031e21050307091a09120c0301110c010c02060106201203041a0106020d12021c020a18050303040303090303030e120a0215061e060304060f06 71
    0x22501030100102d0b006100319403485c1481c14400100d82d08061424007146200a200b0b4602d58a4200307800080c3d100030750480310b50702c2d00d10340c0d106502900444c401e04940e6a1249580e80e030349400701d0b000000501000406005010010f55810507081c0d038011500781e42d044070301a050300c2020a0858401e849201918603002a82103d180c10900800040e2000c0e4401894150303d043c1e401403160b006098210780300b000b030900c3c07007001da0400c1002e5900038a4042209a880c10180350040108806401104000000000000b074140c000b280c407071115005516150321310340001c20280001e500040c11104034161140c0444507600f0030344054428030030b1948031004140fa50f51503c2c0c010380c2c0180e200c1440ba500c2000140300081e4403c50510841e0340c1400c2c04a0a0b1380c514442c1d0381419011103800110a00210703c00084070303400116a4901c003104d1020642d50340700c000a1001030086002c2520155047c01001011810148002c43d8043e00500000076145203d02051080e41c105a100c5032a0421 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 782284244 1250 782282994 782283001
    0xf0f0e010b092401050f1908040308090708031b150c1b0714131b020105150102060c040512190b16050304050c010318020603100923041b050907020105 66
    0x1c1c02e4600c16000011440f1015010030354860b039504000b40411010b0401502103101003044010300292004001850029003410042030001000355904840540018480d540803444641c408549101600c26400c00b940c50000748a404142100101038031195612275181d0190801d2000c00100b4002c00703500d900c01c2c0d035803828800101014254100c03c1c0300145c0090000308814049100441c0c82d421007690014101d041c046400c4000f0008400152111500e80b405507030380e50b906501c00c0d403180019070b00c200c1d0b103002c450303004a030b07124001c545d60950b00d40100428011864134510109110000070211411031280980d000704089010004850052006e0700303001202d0113486100c4034002e010b2419908502d401d41703074a41e60b12072211145062564070b0810000061100c0445800150003902c000e64a080030107401d00f04800301c2c41003103403e910702141c4a02c4410042403429400320b0401881000313440d152590340540340d454500c8600c0d181000e0b40015980c880020003449505140c00005080c40e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 782285494 1250 782284244 782284249
    0x1204020a06021b0f04020702130e010c18030615080304081b0405070503180304090915050108070605040608090118080d050709120f0515040b04171c0f0f0e010b 70
    0x1030454218000b5500100e048451007107000a0a61842d4022942e0751480752078000864024411503a000e500301d80141029504043c10390800420700ca5080002c00c2000340d074003021030390301c4a58406800d211601d10717804c0000c80c04542181a1041050054a03c580e41d00d000043c519401984800055045001021440103078180b02c9a28400305480a200700d24199000402c184001401c0b0f041a1a684060003407400c802c00c00e850143c8902d4504000a4402d0f0604030f10b01407410385034029141c20400040380001e030116240044402c00c0e150304e0f081904201c0d05442d8050010141c0c5d84541d0b0b54180b80e180c200028130100301c20703406408100d6542515840700030a803900100170f2024402010401c11029151404c03000e030f419080301c100d003410340c1c5130301e4214244000040c0ea0103050400d4402c3c001070141020750380c0c1c000e80c49002000045540030710008000e0242007607a03440304d07045260181c039005458000003140e40131040b0004420a00b601c148003260038910800700d0b241c1d520212580baa0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 782286744 1250 782285494 782285509
    0x21100f08160b09060313030e1011010609020901021906240602010b01030b06040b070812010308090909010c020d200106030501020405041a13020906040806090109171303020f0a0803120402 82
    0x1050440c4542e4505510140402c61510018041010241c5030340c1206041c1072042e04242c42c00d1400601040441ca001003004045440c056645807055290640025041d841413003101d1400c0b1042e00500070b010300131001c026445450440694029441d801e02c80c0a008407030341001d407402c40368031400000328141440207003100c100d44295418585000da00c400155200402e540c222500c400754036560381402e29004106018846000001504100000c0100011000074140201c400d03a520006503440c1d003540c1c3d090b02d1600c514400960081e03050174041c9441001040400c01d04591b0401800204008180c00c41c4c0c2030350f000b50b0300d5940c0400c4c18407291406001e01200b6144002c1000409200b100000da20903007940740112025500185055040c0c40d641c083d5002403030300000b610a940743c0400e840d8068620341074126511604008080307040800002501c1401c07046841e00d0b00c03680d04507401d025000b140e5420303082c7d101d00070b0480001c10010400040c16003d00410403460681001e206226a4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 782287994 1250 782286744 782286749
    0x15040f030e0306071e030b150904140106050436050402030d05070308010e10031407030506180303070f03110a020a12110d050315041406090c21100f0816 67
    0xb500030b9070501c513415a02c00540741018840d4120300c00c160104c0d040c260010709442168a400408102004240c0c04160000c0d0810360000d031070034881c0701e181003540f54030030809000351380114009200501031042c138030614250b08406040000390208504d11044815a640c820389603030903442d1002c01c41141001d11a100079680c04c0d062103428041d445c0e4002c1e0004005008901e07012030340c000000d500d0810352540500964111045003c0e1028048040d500e590b118081500d8a02c01ea80c0070400e6030004000120712080e01c04003450454581450032078121100816000800d074684038000808800c0c08001c1c40c01c1c8125400030b210803010f5244c0348000f41250032460082c000d12aa5060700c0c1351000c58000002e003041e250490f03495441108841c00500000b407204e400c1b514200b02d150301200300300d0056014220455980300180d41c0c0c910054164480d02c41d91010929011203400d1080040304003e580041d4a00c050402d00d6498420051142c2c0301030380850071300c0d8001c005101486400a404001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 782289244 1250 782287994 782287999
    0x613120c1401050913110324090610080402031005090330040b0c0c07060f1d01050a03022803060e07080618190608071403060108060601030e15040f030e 67
    0x10071515400107040c6000e0960590300411012003042c2c0f003000349920650b5040800300e1156181c3c10079800c14012030800d202c561180c4881043e140146241c00d80206100e6800100002c203d6403102c17004561410014204980503c18a480300c100035509016491003201e0740c10065861340c2d903075480c0d40403110702d00c01003045c00d0b0050660303654034120f102d107010352080d00200d1031003858a602c0f0140c40c051080c3d080182403406050400704605502c203008001c00200c2d60341b0501c032070b13403003101d0700740e420b25031aa501740410801c1084540d10307030203038024060042d9003e9403403054210201500c0580050b004480c800a035032880c0c28403403214440b1103650041410b107405855403900d0004203070013650b814034a12080c1c1300f500000b8045000c940e2171200300507206109000340383e5140030450f0346054030b000741004004c055070600101d05000551604807403005009100070f859000040d0001d00d400d03190b821690042041c900283d08001d0011070060b4172410005110b0055403d0084c080b00200802d40d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 782290494 1250 782289244 782289269
    0x409050c040c030e100519090302030705101401080c031c021f0f111c1109060d05060f01020a111e03070e2205150a06090e0303061302040506180613120c 67
    0x184030045010b44a8200440c8000050310601c20b089c02d03880c1d80540c100050240c0700310311303c0003403d11080d00040a2003130315014884082c0d03240d2500548503044c03082180c0e05a400288204101d02c0c00419401186803540141d41c041c01d0002e6000501c25482c1c41d0700100203840d02c0b414130314030300d1a208810361680d42c21180c8e0705010300d80301403141441c140300f20b056500e92100d4040040300142c1c4110340750118010010355481d0020322800d00940804c8031503911030b012016203400107500215491201d036a000700403036240300c0046e00304030788035041400d01d000c60089070618984a44081210380003400704460604600d144c002d041c0d50440a00364003030321102c04401c41000008000003600c00d0b181d544110200c0841c0d840f05001002490b65a002642c400d007000c41e4500e80050100003180900012345a284241e0300e1000b04005901c03441c411180c0083c020041c800c4810100300c99407417100402403103103251440c070522009002e880d940018845400401d00d500c200125862810000e0007484c0040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 782291744 1250 782290494 782290501
    0xe190201020d0807180801051803090a060c15090b09120f091e0a14031b01090608040609150c120605010203030c1c020f03042307050409050c040c030e1005 68
    0x1e440b5524040103a092162034008a1000f034090743d8541c409820030458041050b544506803400f0341800c0d82d1900c040910701c1070f5561b92840c08400c880c5c1c0103802030502d22045140c841c0c1100c0740707480001c0a50307041c418003a0305200b480d107501400000f54060304181c020b0b410050394942c1014083c0b02c0ca0300740c2140403c92007280713000030000d0f82c203014000c40b034004a400d010b908210030b050302124901d601c15006a400b00340d00043c40461900100c06608982c4500700403400b10f00001c070480f400034007103515400b040201c07a2041001580c044d104000200d5869015a01d050001c14407a14a03154241ca802d008200b0552181e180701c58402d6000301440000c0c90040040d45034800031f0710b854200d00c0c0004908148004600400345800b4411030115030380d00b00410307540c1054005607812150402c0f00903941e00001c091821020b0301100c400042c0c80380d240351004010061000314011078850140410000d0701ea03541e442058241d80450710b01090220302519101e00304070804400a010a10b80f4003403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 782292994 1250 782291744 782291747
    0x15060d02121e13060f20041a0403050316050f0604030903030f031b03020d060302030a051006170303013506010612111b0102070209011d060402031e040201140d0e190201 74
    0x81d030000507000b52000034000c0c000c182010103807406e0329192015802410310807189000d240003c101310380358000903205018144007982010303c1030340b0028101d039109001208215405500c490001c52080e41181c2c100202c150314141001c4080782d0580120b841c0c0c000410a054101c2100415001d06107800c1150046040d8046290f040c1000e0b008209a404130320b014441c0815807049016580040440f520310410340360669980f1110506c41c0121402c1c0f004c00910000f0038800c50700102c44c0d19000d142107030b003090010080c41120445c880a010400948420340740c0c80540c00b221801840c0000d0444c9604150700a000c1400324000b83c9481c901d00040440070040715401d85440f142102c0170111603a86040542c0e01901410b40081d42c0003829a0000844d040310b240c0e683d000368034150600b00107964180821040740070448941d401c00d04032589540c0a401600451a0302904c1410200c40b8071029a0b401c6040e5001030300c41c407200c0d90361400305040880341044040c41c201e44207000c0342c42c8840141e00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 782294244 1250 782292994 782293021
    0x210304020102100c02060714130e01050a051f050708040b0409020901030e0303150904060e0105090d020f0c010c02040902120f0d0914030c0105030405070e070c061b0815060d02121e 79
    0x1280081003100c0010001c403d05400440752800704000d00d00c08402d0300c1e2b0000c41404403081c41424400e80f800c2000084070b042404009041d10a8034444500c40c0268102c19078107503010350310442e0305020801000c81e6080f107030f50152000e0325802e6030058441c9000c2d0009012540119580c0005034414020003800c12150b2290401000007921368843c0d036119840c1c1500588001c80303900c80b86508210400500c00d000090b0280c41001c15401c54440510300d16109460314100307040c040c0040c44030882d54001d03007803a810502d1000e101801a600005032408080c1c2062820704500906070000101c3d004038940c0602030f0400b500080c20345441e1200890006076492841d61101814000040002800e0020500c001002401507120055084c03030048002000c0d4089030000b10b41c0e040c40c203401ca41070044522a1a06070402588075500700c0d882d003034040130f6004201c40300c96602c00002c101f500e001d032a05001038440d43c0c0403503125a08038101048003008212400e0103e0502c1043d907020000e990300c0914 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 782295494 1250 782294244 782294251
    0xe09090c040b12070e040c062d050d0e03041403030306090f191407082203050903160b19050f090420070c060206090d0e0909210304020102100c0206 65
    0x1240007030b0450750400464101e04000076940458090080300041031042c05017614851489901c08052490b00c07090155280c1100481c20008000d420620b08005d907182d00c500d2051500754108103042520143c60b5000f81c580e00c000a4000d44c0000c01c0801c1089001c100c55081c2c640300714051401c40c50304070b003c160520320042107441c42040800101b01c0b5407030504017940d20b08103203450a00100039a00013085540f81c05507070241c0004e424400180c3c0740304182d0500260803166110640104804c2c0c1c038210307815007202188070340c0b5020342c0182d000880b14414044006108c08040c860300c844c1801c03440c4030200c07580b01000c410301208105442c4141142401c03a081840200c0f000128000d0010082e083c1c2da109829544100d0000034010f000c0c4054600ca150482e4016403c4034403966424042e0b58640600030114030100c1ca140302c1031103041c58414281c907848009401101c4031540316243c02c06c2140c03001402c0302c0d0b91400010074401036580c10300414407101180c85c0140410f5801e41c4000b0740c0c844004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 782296744 1250 782295494 782295499
    0x91509061209020d020306010e0103120807233c0909040b0a1409010902030c030c0d0f05011506090303022514010c050d120605090601020d051e07030c030e09090c 71
    0x40600c0c0b42107581d030300980344038907030081c045601961b19011022241d07503082c04180c901e0021142d07400070302d500c140f10191045080f5503444200d0505401d00048451141ca942ca405150502c85c201c4400884607115081d4030301000d61080140210000c030ba030b019803c43c3c080d10621002c0140a03116261601e130140c02582c0810b200c0030503a101d5480d02d0040221040c44c0e90100000c0b81400200201504a080460f008505481006010604040c6c0c3c40c02c0760f921968012045801e0900800c600841c03605001d40180c00108046142011070200c41040340c02250105881c881d06109250f810081071003505004141c0400102c4800c41501c42c64025200300d90004210202c1c0307400c01e9201e00014103920742e01030704440d0341617150f030f1002d8151404250100b40300d0745084030004039458a40c40c0d081c0103400607000340510302c443d01c50803100b580c810044040c441440fa07850440c210f00c0c1c0b10060003480c1c003e9841c0d0f00c801c9902c0c81c004100c00c92103902d561141c0c2d0b040050000200002c1b03400000070504 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 782297994 1250 782296744 782296751
    0x50901051308100501061704050714010504080a03080915330a0306020910020a17070302190305130905190b041d01050403091a0901031107020301020a0915090612 71
    0x3500081c01268401e0307008031603940035000803000c50080c50341000b8160707061a1100369286e0b030741d400204030505007101e0142c0250b029040030030001409525032000d201c410b2616034500303900d568100c2c2c545030b24194214009031031141002100c04080c403c40e5403d01951031024120300f0000d180c01e172894041c0c0b402010010a401e1611a061107000d4041c001e60f40140071044410b82e2420a00000e401111500e03001e507007840500307150544007040c0714058070340c00100300304024802244429580c00c4003804409521860582d00d0880c031341c401e0203166040c400c0c2d9480c1c3c0e5414442d8680c180c0900f0034ae20540e21f06090006101550074045101c061006c500b160004080901000080140a083e03843d080c501d200c1c034251900b400e0301900818402c03406901c0c4c000302281c1d070302c0042d00d00700c10100c044550440d00303201c241c000b50311a800c03020600e4444151076080c100d454000a0881c0c8c04586018080b070b02103603080000d26413604003072a8258460600100c171a280c108081c01007045500308014040c0d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 782299244 1250 782297994 782298007
    0x31305060a17070c060e030a092912090d0c260f0c03070c080703030c150204030213200a020709050c07060c111b15071505100e1605090105 61
    0x81100a4401d540c18401084001c0c209500c01401e1038100e84402e0380c040c3c6c20003a0707a0010210010886000c03d0742a03544107001d601d4418102c12041c24600b01c9031001300d1503580e10104d182c003403015248200200740c4e041228100200c03028a0403400300e011009100c240c000a4010031410420000e0705418803030101e449101e1540e09800c248210705c0e40c09202080400e000e0311250001001d030140e0761140b82e0b04480144c40b40041a5036030b1107440000d000072030039411800018100e02c0e45100303500010001509098580c2e0004000170602084a00c0c4150365000d03206020319400d840b0f507001d11000103114500450044029101d1020340513140101e03480b02d020964900c040c000b251006034101d0300801c080380e902500100320b60420303140c0d90150301c0750304450020010321040741d40030031000404084201500d28221002500504400c0d10300d149011266408400c141c06401d00c0380d450840440c50382414506c1c15142d40b98091308804144444680100103141c10004591100701c0c00d0034883d40722030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 782300494 1250 782299244 782299247
    0x7060603050d0203120a0b0f011b08030114091311040902030c0a090501060909020a020318220b180405030409050c0f0a0905090919031b050a0f06050702031305060a 72
    0x10903440200301d841403864100500758040081d1041c04086041c1d030341180c503810360079001d4443c80c0010603840400b540204402e580204ca043d0040000100c414800040988905845030002d92002054080850001106250020348aa4040200801040c0d0340a60340c03181411040c1c140005401150b4401c1c0e0f40c41955801c201a4482c0000106000d03072303a689906490380074190038812000414160000842c440c1e60600a0340e041c90001d40c015820701c3d6050707000c4c501d25040120032a1308010030310300c6000c0b0560480c012842444801d0380105050503840c050180355101c002c1000000710f100f409010004001208940c01c4a02440e8045120b0300c820107014410302c41d1030f602504135040050b0180032182c02082081c12148121140d0403181c1d181003680d0f48424101500080f04103d466440e40003034016103011001c4c0c0e01000c2c8840d90203000d80d441c6840c01e00154402c0e40e20f2810040700004211060107903642c00401440a075084c00590320700a0b44620301c03406001e206550214000c034146 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 782301744 1250 782300494 782300501
    0x17160b060a0e010b0d06170d0f03020f0c0c011b0309051002010b09040f020a120210030c0e030a080c070605040f0e1e130b010b04180f02120108101b050f0706 69
    0x24070000e01e86041550307441c4d005108a0f880412035403401820180d0000b020b40410004010f0310040c900a8503201082d100c0441e882031041d0300000074141d09000c1c18118454403805821004503000040080e0714021001400f1004a080200144102c014003800000d0740072881500f103d0301943c0703c04801081c82c1c401da0251161044071504450100700f04018400d040700d08000b480e0007078404514054903000c42c0c510036989404080e421200d00102110482d03c00d62110f840544940b8100281080b01c6000900b4881d0050040c1c0e0105000704008005402c14070212000700f20031708099141615101118540074890300c9580132821503400081c020808a01001c0d080c061150348051080c5440c51046a030180300d04403d550701d01c440030001c1030411400c811281a90a2030780719069a001112742c40000c0d210310700c2408003540d003d108100d404103e040405018114413006803070088030302807c000c102e07a190600c03070b9800200003040ea01181d030890f04035807908070248030341c47e55920b0508220014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 782302994 1250 782301744 782301749
    0x519060b1e1b0a2405040809010c03021213090b0406080a080a09090207080d05070e090a18060908090909010b0a0311060c0a0605011806261608030717160b060a 70
    0x4038041d000d000c00400201c0408510104c0e4503c13a03881e41c110a4646110841704100e134024800705040000e54295030081c0340510400d44a403045a20034065035010500300c1d040346500444049940b0303000d01454156000f43c8114040a85082141078504154560b03598500803010700562000142c0701c036900d208244080191a05c1d40042d5903c8081e4686001c40c0e9001b10403c0040501c0c0c003004c19859885403e2a03200b0b8000100300380d40b59156011211f004148030460054000404660080001c13600c0c05201140d901804141d40c823401b84000344030100f5802050980c2c80d03458000c13488030503611105014166074110a409111260755000b040040c0700e0004c440b103440c031030351610404204007900b00758103985020b411002010004905c003001e4403004e0044149041c400d00111020b1107100012100004181d0200d41c0d404800c7d0480103060b8000781c100da586900006590010305c001640d41002490b406040c0360318058280d545440d5040d80c283c4001d000c8042c0002107403680d580c00d8102c402 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 782304244 1250 782302994 782303047
    0x170408060c1305010206072a0f0503030a0b03070e0721020705101113140315010e072d080702010e1204230612060604090519060b1e 58
    0x164140300821507101d03004107040d80d00081d03421801044551010070b82070300903e40340c0c4600c201c280d1405903d00720003074010b00f000e8510340320b101d1000201e40401000d4203504d008401440d03483c20510344800a0701c140c403a0403402607001000400c511035150720001d61003142c80c0b030a14101c0703e42808003d5050790b42110b80c1c030014000303d441420b001c401b1942441070070704400e04000080c546080070040d4060050400c4508907103040401002d0311002c00f008007400001e0a50754502c00500f0030b40f007420002e070040000480c5481c1046000d03a080003207005180c3c1d0782d8069000c01c1e44518944000c003103400f8180e85c00c010f00c080108039120700035006580f00c28003c0007903d90440641036142aa50418403401201d880c02c1d140d032819010402c50083d0f02e1503400b4010915056403040017180e64480a02003941244007044001a405c1980c410103005113001a00215044c031039500d0706c03003030f615503400211461604000c016108489908401c0e0313000e02c41001c264a8404200700459030f508052215503 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 782305494 1250 782304244 782304253
    0x30c080306010e09181b1302030a0b04110706050603010218040e0f0304090c0206060f030601230d0c09050a0b22022205120106031205030406090c0e0601031a030a170408 74
    0xca034480801d6417951140002c846000c2c11501c0c455606110b8000080c0d000780308180c1d40c6099498540007158000b40c804004221b0001e59804102144c504d510044c03580c102c00b04407001044284e018807a00b200c0200c00a500302045001c00d000a00040c1010500c035682e070b401c0300450840c0a22104014a00d51000c1e661900da8920070100034001d00241c00d4018024000068110700e0802840c02c1681c4c4027400800c00c60b82040b04030140709400e14030948412020b612207510741d6032000c01d802407540c03043c0c0c0f200864a01c1c00580350b05498001e860058440d0601c01d202043d41c86802401000d002440403054051800300340e031700000d100e00e1104404807d05000302c0d00310700542d06e801c4401c0b0785007581c42190985044d403006081740c007540401400460844481c41ea030510440145030014040c0c10005041002941c62001e000129030021780401c2c0c40808014040da003610850074a07142c1c1c204100c1600203048002521107000c070f440200322007042d8810003103480d0f0350f034140c1d000303451b0f00011207 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 782306744 1250 782305494 782305501
    0x60913090305090a060206090a060b12030703030f0507051801080a0216110307080a0305040b07080408010509070303031118040e010e0a0b01050a270b0f0a0603050f13030c080306010e09 81
    0xc1965010b180c820740910600e41c070000b10703141b000403102d21031500500039000c601c80503034900c40034001c0c11a01ea40e0101500003208940141800100001c6100c3e880025000212a0740b00341561802440041403150500074001e2000040102a001160900c1c200c01c1583e01c803400707100207001e864400040a450310318014100001a0301c06a244081102202c041a82e00d05105a8404d500b0100a0004505110405c045032040020b4080f5a110b400ca090902f5220035907207003150000c880950310303079010410402c03d0581612501030545c2e03c5900e1030349040c58505102100d10385007050340e030085607606c20306c4c040c2100a52000340703401200e40c142c8005a006041000810701c00303025003803182e1840c03107001441c003140385602201e80001e695911001510850304000422652056a0b0000e0510321014426900e105004000d00b5150f00d0005242c02c16024034074181200130080c0d250040401c0c109004039030000851301303050340e02402c0d00d0364076501c040c01246c0c541c0d0385008c0c00d5046507850062 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 782307994 1250 782306744 782306747
    0x20714030c1003150e190c17040f0204020c030912120406050d092f1c02060d150f09060b130302060c0109050106060c05010c09060f1107080607020a260301050609130903 74
    0x506000d0744c4030404503101a5011541c0d0780846074084541f0700424401c8924210320041c0351b12155009000b40c00700c2d02485119000305050b03901800c0b01c0b034507580000560f00c030503180198014a0b0114110014520040350481c040e0f010312a074000d040070300c08041108910381d13041e900803543d034a900c03000d500b0103900d1900381c80d1840d00300443c0324150b06c1c5600c1d102c00c14906210361080790301c8500c12014000d0496580074000d46602201d200c14525407101001d503485103906501d9401007070003480c4103c1e05460100c00d0411140140c20012001404000c11098600741c50220001d07207070100c4015580d00f001646090040202c001e00810650a0041c0083c426400115591019000d00020301c920409075001b100c518034213003c1e45001c01c0041408c41201886a01040f84600f04842211a06515990fa080c5000022603103500180d004102840070030000383c0300720f110950710444480701100c456a28150a020500405014600100c3d4150f00e640c0c0711414000846a030748000c005000981c00c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 782309244 1250 782307994 782308019
    0x909110c12030708130b0a05060f120601051008040c090506061e0409051f090506240306120f03160807080318011505030a06050a09080409020a020714030c100315 71
    0x1a410085413800c00020750088a03c4001c0f181151310510725541c1da9185407004d0028400507285030b400402c03041284080b6282d01c21244100e001e030800400300c0303600d02010840140c2d030082403181007010780380a01c00055020410300041e500b80010214442c0c0d65800481d4150155910826104400d003101010f15003841004000340d40600b4001c2c405d0343c0d114258003154100c2c0103019814404550000c008480c00c81e0300c0f15400445c01081054044c90400c5030381c1c240946034003080c09103040001404942d00d0840e04a28000751000e000c1d0980c0e101c5004c907681c40f03000791200d6503888145033508504001d14001207a10066010000584a042c01d408100b40c4000c03a00b4141565843c00451420092a0030151022200010000c0c81c030200180d03240c03400707030030b000c0d02d01d4201d1034440f00e00c2400a084000070b80b020f4400c00000503254020721038000d14010840d40009101c40e0703110351803000c40d00c0104014001d91030544002581c145183d001314014180043d40109080340b44c000407030302021605 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 782310494 1250 782309244 782309251
    0x30d0507090f05130504020a0510031b08011d0601090b16030909020306060405060903010b030102040608160c1a1906060306050405010815040b0a0e0a060507021c0909110c1203 77
    0x41c0c9807040e0a480710b08a02c40422107004907030780409111011903c481c81508025031051001d0b151407a5540e03103202140e9110007200c845c101080d240d90301303c0f802604561004071005002c0c0b801141a51602c201100750054040d0310074072410400c00050b03a0b5901501e881c00080c5212407060f50f5a010322990581039a000f2002200054669400050398280a00a0340d0003010010851072800d4a440200a06540302020068141d501d0380d101c0d21403039600b0701c045c100505241c0c642080e04d1405403000c03c002c40300c25040c80244030f0340c00d1141c808a0010000f40b404258808400c2c0100d0b141c5140103c24024229200c001c00750404901051141d8140c12600450310143d4090000740d880d1082d1944039840b20514801c00e00c00d60f4002000304444e410020f400513130b80080054904000785425003000c01e829000d44819880ba410700020079030400407000c80010102a0720f101700003035903000300411502c1c1702d00340400d52628420280e0000301c00c01c481c0713454250001c0f220011009404c0300c5564008a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 782311744 1250 782310494 782310497
    0x50a05041121030d0b120d050405060a1202030108010903080c0708041a090406181d0c04110433080702060f0a0e191109130230211206040c11030d0507 66
    0x6c01d0000952500001c4c0c4460848081d01c1d00c0e8109070901d001c0c070816800441012042004810780031300e825500c0d10045020f018a4000420300007080e040240c41000058146240c00004200c25004500410261000d546601603501c0304040c184540b03290394007030032121542c014600180060b820440e507945c2401100190310500c600380519002d05080d803220300e200001a0018000c0c03183c1c0789015407040030410065215581001c0d00c49c900059001c0741000048014807511080010390714840780d5050380c0807601d00d44524641b401c80002911150080c200600000c8140e012650840d65504280546607403182104d6404002480030540f040c01050180c40040c0b054074000210f00b07003031501c1d0b44120080c14010000442d40da0034804e4941c01c40400e0700080028a20503410484860f00c000021940400103249018207400c03a4544040090b001e0381d00144d00b0800d010720401c0701c1030394581c4450107c0300000d404910030b00542d0112a040c501d06200d010008401c046040c10303500540c090b2840b03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 782312994 1250 782311744 782311759
    0x30c02010e04150816030201090506030903130807050a050d08070f020f030a0506160201050403171506040b090108070302160b2a03070f0c51050a05041121030d0b 71
    0x285418200d17030303400d80d000190000e450103200b070141d420108011a0800c403203104580c5081e01d0402a1281c0c450746820842c0690841941006280307040d25054010f40f10403149800c400385c4554860702e0038811040010001c0010000f80c00641d0b4a080d00e003c02c0b8030001d0b0944200d07078801d182c62600c0700c0341180c806a04074402040070f0700d118814400c0c00c0c45290300d600c4450444c0c00082c070b414a2110010902c0f030b82e070f9011045c039142c43e07180c3c10007a00c0100200040d0988980d4a80009002c0f410010040000c06106200c004101b0700e05007108141070b50414080e00c0244c482c2100c000f400a00150005900700c45403407540c1882d404d040045108843c1c03aa0f0700c02c00c01c042228122901081954090b1401d0b40218404c0807200710494201a01440b1440c58081030840c2c143c64005a42400c070000c101e807001070b80c03034508134403070340075065000317150940c00c01c003a182960b990300c882200d00c0041c9008070b8010035120002c8107440b65590800e441d400c2181d0700c03101088080800b40c214a070025000700d54 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 782314244 1250 782312994 782313013
    0x40e0f0903071707050a030507021e0f0d0218012c07021b1801080d0914030a03050a0c15020307030e01154a061804030c02010e041508 59
    0x425415500910040e4090341c0b40030345903101d805591160314024261003804001d4040092410081d0104061280d199152181264010840070407000303400d81003954001c00d4001c3e0241e07110580b84040c92011110f0000c040124004190b004560200700e0a84e0b40c0440004a43c44960710030301508080c12580c1190740303650602c911542c0720015a003907800f682c080206201c180b0b20045a18108800c081c1000d503404440c51a07560312101c0a0740101ca10340c10101c0809130f4203520414040281c02e031580c8210b001c950800c0030955451800c2400381c100320002c00c80450052040e13180f8102145c02c1061048605070140542d002544241c90110100b4a00340075444021018090380020030f04200c9030f02e444e40d10703103000070440014034040b440c0c440c200c001040410600003013406a00d4800001110450451414400030000e8080e046920458020303529007291440390401982c0698580b40c1040001c103d4801030741e0b1421030050781d41d0701600380740c624644010004c0a40c01220b1420301210503550 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 782315494 1250 782314244 782314261
    0xe04050c060f0306060313120f020f0a03020c06030702010e0318040f050f150a120b0a060608190c090b0705060708100503030706020c0307020604081c0305071d03070f060302040e 78
    0x300d02c4849010400080c000505075181c15005503510403100451609440e0842e5220406500c140200c82c0204030100c040307030070003941042014001507c203c01813020515640340656101b41c0040c00034842c1030b0010003da0360301d01c00e41094482e600240201e80d2a2810080344030120092400002d02940c5400b5210f84881081e0040300d0003001c00780055411515090012044951b4000c416a00221010000203000441c0000450014094030784286107080c40d9800c2016955290f100c0310400c00c1c01424007047c44000100e0b034003003006004000075829800c807010b0b9a00c260035480f01101040100d4440e06025022034950320854880d660f5400f103a5072500c1c851000d1403240210b40e0507910074401c0d20300080860380140391b0711040d042281d0800b807030741e80095081e501a07045030f4003c1e007128000e0780c280585060100a04050350405003d40d140ca180e000f818804004841611410300f800b06203c2610240110b4014101e600400f0b050b090300c94502601951041c4960701881c084030000807075a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 782316744 1250 782315494 782315497
    0xf031e0304060201570306031e170a02011e060e1312030b060d0e0726060615070b040b1005030a0f030513150206010e0612120c07030b010e04050c06 65
    0x40304a00402240e0241e942c945c0c000d240f04030881c00d400e0001401c0340507804a40c00004800800780c2d000700d00f180c21450407107035009000038500c04c00a0420032910015102020740b8000300d4040a070715072103050f0400300b00d007d00341d00608034a00350120f0030f1070b013040d00254000c0e1041e01c1c4881c001d0076194407840e40c403000c4000d4860000d40181d4488001d0034000d8407a4101407862207008008a003006040071105d030440c0c3c5000c24104e400c3c0d000090401062850b030700703100c1e5000c010740f0240e6560041042c00d02d0726103400400070340c840c0c030412014280a4040105942141d600601c3d650030514042c5480035002c10242c07103500310300340040c0000801745400a401b4690560204c18008501400e540640c0c564100b0400302d04c1001711080046003001e44401210011640781c2c0c001c14195161071410036516901034201406450710540c15400c0c150005860680c90650003409a1b42e0220803103e5030414910790002050700e03c022000240c18110141024022030185050b9920500c4440400005 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 782317994 1250 782316744 782316791
    0x90414240f1f180b030316030e011b121103030702101503171803031305090a061508062706120a030906080601050702040207030f1218020f031e0304060201 68
    0x40614814103101c414140c00b0f010050849518010400d8807900d80002d003103801540e00c2d00c1d60f0300703150b291040071b140d07000340e14042c08202804c102d804a076040205400451845070087c00904c08100d0304090740344107081d200c403030711040307429a620380c24090b1000b9190046801001c140340c8c200000401420a8072421008803513004420300c060181c900e0038101940c0241c00303c03208070a03410081c810f0a89052000300025140385e96202c01040c1400100404080041d0405402501d03003402440700003003405000503c4c85890806042507a030744800510290203220707010544450841d11401d00c03034041a1a14011081203401c0c110088035000e500c0e80d552484078026001907020003040049901903118a0341100c81854640d00e0914103401103020390344041000ca0010705080c110055140d80059201d5800c0182c00040c03240d88001d904c10300d450403000d400039210b0718001c100303004155030400c504023002c06540d0296807134509018060303869400c10b10594003d9400e041042d465031044004c05c001c1c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 782319244 1250 782317994 782318041
    0x4050c01081519080a03080103061b05040302120c060c0309011713020d030c0c0308181503190b030f0106060f0c02210a061424090414240f 61
    0x2d20704040401403102c1000301e00b6180746441a60104424405105c800a501c1c02074650003059451480c20408075868240c0c8107504204418003d4403142c3d05c1000c032001c507601258ad088a101c044070740b0034182109180381c0350340003400040c02068440702001030000c03180c090300c03040c00a6840c01450b4850134000c450080022446518402c014036000321100c00d801d0291805092181c829070f04c068120701c051700261a00a0081224181c259140ca48150607440586030564001c8808e00110003602002e84031072100c01a641d5000340018044e40038580e108c1005003200c8205075400c000a0007000e05020b008001420403d110640d1802480130f44441607014000f407400d0414100c0b01c002a080203c0c0d00100e0f030181d0082034020404c1c501501155005066048a0314100350881010940d0316000030050040f508618000d41d68441401540c0140c100b001c203000540b16542c1d00703080507011401042090046400101c10050f8200154456411204006105d0301c4da030b0202c40c1c41101c0c0014800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 782320494 1250 782319244 782319271
    0x9041511030c1b1504050106210b040303050603010207021f03150b03151c050705030c03010e03030105100e030607030b09180c1905040c02100f0b09040602210c0304050c0108 76
    0xc1c2c08410010354000540000103441a141c035507000c8a5503510b051750305898503034503400b050080391000c2c0e4019420821160030829840666510325402a5008001406040d600da00040c11a00c00390102c8503007550044c0064010012000761880d980c1040920500107850041444004a413104003182a2008220900d095542e444400881442c3e24034049400118210314181c00030105e01c4424412403180001e804600d091409041c90700c42d031403490610a13070410b043c0041c120740100459065480c1a1001c112a0a22000c180d802c3e9010650190f00761007170100700900540e0641c002103501408540004960722981c480302e9540c940303415120110b41018034040ca15150070140d4550208200c166111016500c0001030105c4000711019805604410030f0300b44261035500c1140030780c1d20f142004010141e0814040743d2004030040c4000d081c60760000b4444642c200e6243c80e00c0d60a000d4412104d11444c00c0b88881089410035281190a40704281c0526900e60066004a119a03604490365 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 782321744 1250 782320494 782320507
    0x30510060509041e0c03020d0f1505160c050a0507080607111609050a0b15090102010e0102030f070c05070b0f040303020d03111804090807110102060a0c050403020d03030b09041511030c 81
    0x9107001e00103040451702c01c08076080020040c0c80e0307444440880360290317410344d80b404a03034240134031080f00c2030a030581914940b0741000040c0c20320284400090810b0f16007400b004450380b0b4400e1030201d09000140003803040f0070000801c0240018014840d40345641c44102e140c10110724541e0b03403100410b044d400000c1c40396040c00302c645198090f507840355084101141c3c0742c2002011131f410400600d041c400c42000010307901c500b5602406a4038440030008002c52861402c07000b200c05140001c0d150741300f008800d12141092040c00c02c030007030280c020160800e070b5414000010707000f01d41c09484200c0c0940034170284120940c2c040c1c030400038200c3c2c0640400d8a072000c41e0203d01070160b80018419071003580e40e220b60000c942d20001401c00305120b0301c13100c44124103078000649070500080c0250318460415070105091503101e0140e604483d07068698410030491460190040e00b003102210785c1040e1000108401d101a802c4050030f88191102d0800c0000d039400b003011180c0c40106d03a00c0c4051030081098 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 782322994 1250 782321744 782321783
    0x7060e28060e011b0908070f03080307030209011101050702061902030405060a0203090102130801050a0608030301120b1005031f0e01181e02220b0a21031803051006050904 75
    0x11401110902000250b4584500c658442c0a010007580d200010300c521070a1121030740402007c1d002e02251003040f4402845c1d95034460705031100400410825070045030090499000e40c11403802da0110fa0024019494002402950b0314070489003042000d03100341500301c040c0400d100700e0380550b803c08050041079440105070000b03544042c0019115642c2080504840c076901d010b4a00502100b03400442c0300e003890503628080d202c02d0b4000c07000c1500100010800049040400700c94203600510181441d9600400c2d0990078003ea4001d540500070007856000a0000c00c203030000e039038015102000700700c200ba50010300b00d4610048904102c0122241b18010490505030131800341c00c459001c0d82407420036400b02c0c0041d00340c0c800c03002c02c801d00d83c1030b600c0c00c4821500542003800001c1d41c2030101e140c0b600702c40815075420510940c414168541148040c50300c25045d5007001d140508503242d08503a40e10740103981c0c811031480c1c0006d66141c00d0b4041454500066024001ca0f0024046030114581415 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 782324244 1250 782322994 782323001
    0x6060d05070e040c050309010b040606050a030c032903010c110c121c11070b091e0a05040e0c0f030a050a170409230601020a0201050d021c0207060e2806 67
    0xc0304080c440071401e82855a0f6841c0941034500c0b0855070b4545c5c4034100121051f007035400d5440240d1040c2d08040301800060707405815105d441155280100704007080301010350040c079003007140d42c10f040c00038800101e80c003009982e0f2448841d000d038000c001000600750300311600040d5054071206070b0003828419070f1034584114041140d640c59000d0300d19150b40c40303041840000300c0780000008210801c5000c4040e840c01e0280200405880802c1d920b0a5150f900203200c0980c0541e6125195044203c040c003540c070340c038420300050701c03021303108000715030481051076078440100015a1180c07945c1c0c181e050040c2004034144500300d42c0900140350f4a5040ea462a400000b56200140c01020074400082c08910b04c1c050840c822411182030401e1129002d540b1086c40d0004190b41c0c199030262030904010703680038003103030303170380c556203100140c4179221004c0310f2110031034075405000c400340089156020300190307902c40c42c600c0d441081190100ca10321019030b150201244c01701203001c8446003c94011480640 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 782325494 1250 782324244 782324251
    0x210090806011802130f05030706051c0c05070f08130503010204050a06270e01030c0e070c1b080102032412060a0c110a2a05210102090d260306060d05 66
    0xd8000d0700b404c5c40c09070b9030103284020303901c502d4004440c00ca042045d81400d000690141c00300e4030b030483c43c01c10b200400009810500b03141001da5940c4510f1020014464800e55003603c2d0700419a8003407070060f080022458100741b82540b5001c140c0307a8009003514052080394200d41c1d01820380320780e81d07282c181c0554040c0182141d140300c034007244d00e070040070b00c88070721086010f01400480e6040550460401d0703009444542c2112141018110901c4030f210780050600c00141e40c4094038050480a03c0c1000c400b56006074841c908a43c008001e01c164240441e4101c803180c2c1010300800100b00810b810003030b00c102d21240c480201c0c1c002102282d50018540c0050003401610309204c608000030802003803800700141d0059030000078022a04008107a940590124500481e051000d014105400200c0203501c81840410521202159440d2800c081d016954056002091106114030500f0a1160f0341740c0f00c0724856442e600184a0b619005665064034001c6001801d800d00708240c3d0442c0200400c4041d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 782326744 1250 782325494 782325539
    0x60d020d0813030302120711090628140f09010b0d090807080909010e060307091a030105042306010b0910120509010b030606330403020616021009080601 67
    0x203003101001c035046030001d2002c01c420b1050315404514508009040100806c45480440f00070400034001c40c0c10546003039000b140c00c82d100440c684034a00003900d4045000d80071011081940300540c62000800010011140c0800c59621021486000c100040150041c840c0c0e2007d07500c0014059840008003410302c5000d0190002034804540d20f0b013100c16001307103504460004000840c198141800c00f282030041516051000442c01c19100080c3c80310014044d0405642d0780304040701d401d0070124002008014003070020041ca00f407508003002c10b01822411440f150b00b601e076030b41000e41c10000e1040d0490344400315080c103001c0c008003041400001011040c0070400750440421001c4101e129060103642001c000284880c4040f0030b06007440030080416220300c21f0107641e034005440502c4401078a03200402c548000c5050b003100d0608600480d00040d40020011030b601003900414044e00c20018002c4030000c510394480801102d039405030380130f041c410b900b1203001000440900c006860024110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 782327994 1250 782326744 782326759
    0x18010608180a2f1206010b07030c0c0e0928060c030209130e0d0203040302300d03050a05060316092708030103060b06160b271005060402040608060d02 66
    0x591221041c4043c00c03201d040d00c4405a9034a11200c252484421140b49800e03544981c1051030a0000c40d140c07a41445584403010300003075a802014840c21908606a51050b00683e419480d80801b0a00c0ea00032030307101b4200e10800c0c12001d498002e4100414011002030000e550710045a500c8101401403040f211007415002c3c424003010340d03a044031140d2070001c06000010743d04064902140350040d4241f1180542d007042100f030000d600c540b1850f08a1008000181000a21240c01ca40a000c00402006107901520380d6070000a0f49c19008180908588101403041d034680c1c00816889000d0400c281c0f10350f8900140c00c100c0c07580145c0040c0500c081001b410b030000c2207512600798180c3d011202c11200c0f104000010f0041044074490004081c009852140c1031a48a02005c01c02d0040351002810003285180000c42c4c20400d480f00802d018140c2400d40c2d0043e294011141c5d5668600104c40002800c280c0064441d04040c401d603021900c3c80d5542d0341443d2268030a200380b00403c2d402c10b0760402c40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 782329244 1250 782327994 782328013
    0xd020607050f010b031c05030a18020a030302030304020f01090e0403080c041a3a111903021305092a070f050a050c0a05060d0b01030e010c0306051801060818 69
    0x81805050082d050340301c0045014000c040c01c050a100000a2108291156000f8220340c6903200c019a0381c001c1025400050454046045c01008508004000c4d440350102c4808401c255001c0081c42c0a14800d40d52903c03120007940c010b494070b045034091505210242d00004c0c0219100b40300301500621a010264034003510b8000210019404a040c207818040006110221600043c3c01204180c0f80300346960500380002d41070714040400c4188100303060f403621030070790030410803000f11508982240062043d4080c441d1000e0060741046042e1030740d030810321800040505042c0300c605d05c0b070720b6041c203006c01e0700303003203880c26924216645100000210305020f4100002c02d001c19815865004200510b50300c0524949240b0b401c034883c10341c0d4060030352481d0401442d203c0205880c4100c0440d00d0204025140d0700c0100d00401e00d605401000b50b0078040b40d00c040a40590107041510380a80c1c0c48600d6202200c140303c0c00140a102c0d110014426000003160706a80425880d0f41c4603034041915032085 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 782330494 1250 782329244 782329253
    0x14060d0f0c08031b0613030c0c051c050d030c021e120d0633030b010210050406150b0304050c010e06040308070804152336100203180d020607 62
    0xa0071600700d0710b031550000400b0000d9640100b5022a100511382c020021407500741c00307801d040c0c04100d4005090000c060b0441d02040016580302010380b0b40900385a5601c045002100d110040d120b00a0740c803030169880c4240213500c28003070b1500d0501682c008203460407100011800c010003600d0181d2440c080d44602448150410005004c6501681b1010410350300b44254440451024803003c10444c10010030030740b03080504003696403505564140000e890300e0200040c0d04061461004000e0f0902d00001c01040018540c8484580a003480405894036126890441184010b903009861944203112003080c9620488042230940c10252895051503a0b0303640e0551590001e550407202494080b4040c400c03906c3c0580c120f07220940c280390500e606050000254021048061410b02d076050004030a4014100110b2050f01031002004c42c201000d81c1c070109a40c1d6008a5407150b1103140c1703424885518610002c140c0e40248000814024186143c204022111400c900c0482e04001c1c00c0c0209070104 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 782331744 1250 782330494 782330513
    0x201050d0f0204080a0b0610020a060c03020f03250c08040909061806052505070b09190507051008010503100b030c040e0d120c05040905090a05070b0a080a14060d0f 72
    0xa040a60007008003c42d82d1400c0a0310820080126004007206c205232030f01990b0028060400c1600041c0009640031a5030044000c0d1140c40700c3c144144400005111780649040078011044440e00c058003910b802840d000c4070b0390010b01c04080c0141e50301780000d008000e00345c5d100c2d4110500c1441d000030b0002110440c004900a0010f00340c03052a0341d0740400c100c107042c01110f0194007011610744074841c02c1c059005000d9009544015280e46000c0c030000b203046008001d0a21014010b401900446c4228a08156562a140102e80c010308054144039103050003400c2a81c180c0301e000b0003034000c000908091900810030411070a03418071031020390341d015407180d1041041c1c8803010000742c00402c8010788050101b140701007111490034500b55000d0f880710307800030586007520040d440c00318158942c4c80b040c0c3d05e803064100d405030450203401d00024022040d00002d000380201c42c3c132458202c0d83c40e40800c00072a000d00c0c0200700300a40240000301e07646011124112600e20034041807810640988414400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 782332994 1250 782331744 782331749
    0x609120105010e101415070c051201021803030309150408121302010314041e051e01050f0709030b0c07260406030e0604020f0f061c06031703040c030201050d0f0204 72
    0x9040000d401c4c4050440c4000303114014008240181c507203028000041032050031413402c04080d030710002c14410300b0002c03124008002414000e20b082455180d410405000358400c04220b00742130f840c200385440c241404002d0b02d1051800e040940340d00034a002001c02510b00051088468100802032000100240541c01e80100300f126054000e02c49180f00160440d07245c111001ca402c8000000c120001d48480c0008521440820000121a0142c6007192901004401c00342c10381000d401182c404640c1580004e120741c22003032009400c0c1e110510181e403d010703030f40005040500754100091003500803c00411000d032282c001c0804414888107442d2440070034481c1c40e0750682e0002810030000e40e150190209014041000d041e09080070742c0040c0124202111140c0100821001d003103140da0b40030b058482508118018901091480c107113840100740c0341c0812110101804610080500b410041d00e210b16880480d41040600319001581d013a0092084040342c1a2a00407071100800d03140084c100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 782334244 1250 782332994 782333009
    0x70306060f0e04200112050903210103050d21020a0c050601060e0927100c09120305030a05040c0b04090603170a0206150307031205031902030c09060912010501 70
    0x46641c108440348107010141d520030000010120140004103003102c20700d22005281441140400b000c01c001640d03901c3d041754400364030b90f151800304424898048001c046600c03440400c1011440742c9861001c05d000300780401b800701d44c0300011f41c2103014090782c0007010002c020070b55218003500611200d1300b682e100400c4240020144040c0004101c0300300500b501404d114100024441c4121012401400c4000c5c5072031510440d41041401922080d905600100d4440c01175030a03025007004501701a100c0c4130a40000118000c40c0010403070f01c11810383c001c40e540741d13440d83e1550303d8001ca143c01403c4054820788040309041000076400c01e40200034002001449800b0404d02d1641c00c3c81c2c5003c44ea50301c0c814214400401c04140c2c003650100c0c1c4141c0c020046e0072840051a1540c0209140c0300c415000240760942e122801c0340748640000155105d40780800091902201491000050307010984074007003130305001d004610140c609980070b0403c1c000b001c0d00c451203000300d0307825003400e5070002c0c0e100f0700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 782335494 1250 782334244 782334251
    0xe130303050f060609060702060f0313030807140d0b0f0909010f0f020a09030305071406130506060a06021902060c06010b031b160b04080903010e010b030705181f08070306 75
    0x1010940c05024040d03100b20650740c041e88501c1e0030000b083c490b2007020001449030600040c07000866880c182a07802c0d030080c10720784039100d152a122403000074a0401064010600080c0090300702882002580c0c00441d0000b68941004010211500605030010352290b1041101d050b01031a41c1740c1c1d40c401032050f05410004500946414081000c8501040c8004030507801000002d0301140c2040b04441102c1e410b00c0d00c07075611402c504100701001004242c0e01141d0080d030342131001c0058021000b8030705502480c00d40f1520f0302d40c0c02c10001c01c00e18901c035030005600010043c010202482244c0000c150014004078640000a0402130a2132000d8000707030190b1601000307110b00e1803c0070401c0405080c500c21013610342154008142c0070380c0700038100240310501480c00181007001090a641c000700001c0e0081c2b09051a28a840d03010381007000e2010700034850040d0005441c03400400848001141c1c0c881044662145840e259042c0003606104000100014000803000c400700a0f4100a60003141d001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 782336744 1250 782335494 782335531
    0xf01050a2c07090f080601451b05130902030714030901090c060908030405090403030b1c030305060301061a030402270403090609141306051801090e1903030b0a0e 71
    0x40311014084d030000017440d4040001400780c00701807016804010b500d40300031050300b001c041030b0303114200c8401c0e200105010003114442c82091150020441840204802c02d01185016030403100d0f8001c50030f61400c1003c50303072020040b41c403480e402503810910034946504200aa03aa01c00a56403095031a524103a540707101034020301c400094a07a01030880ca141c8000100e18184c880349d40c03405540125842903903030034041030805002c0e41c40000381c00805440b8280340f003046403901c11500e181c2e007010b402081c209000100c4030b140c107102c0d0905940143d08081c2c10070811040060a90300010000ca800080741864800600304c86807a00601e0103030001103142928207864010000c10160344040140504110180810710442101e905038090a40300643c03403035a54074403980038290b00da000d15040b01040440e807001c0d04985407203a060f61326619013032021a400c59a0039507607009032a005605006031004403800607100b5000b0300f80c40c040080c01c00d1400f03600c0d850040c8010740d00740c40201a40d01c015800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 782337994 1250 782336744 782336759
    0x1c0e1002071a0108061317090d260a0f0c110301090b040312060e040807020d060e01020a0216060e091003050601060e12121905040b04090e060f01050a2c0709 69
    0x6250140c0b113000c01501e040c1c102003454810382100034100130031511040c083e0816078504402605d4500707000615880c0115000d003401c3c0002184481c0c200b2400c1148111650408040d404a8000221a55440320341c0c1c1100c0c1812200d090540d102118904015020301490765000d000742c1444031b00441c80181541040d103400340860155000a52282c2d0420b60b00304443c011a0240581c03154101e442140e564200d403002440c1000000c400615180c60110201000c110550240c500e640b0540c0842d00d41e21940c002445080c0510302c10f0400103071020040074810304040f110103801615540c50a9261a100d50f545810108240c10a100140c241d20351003010345008054a10303944058000391072030030b10706c110202c02d134460415030040124a4940040555208100715001000e0304040552140d44481208002d0060040361492500c22480418a490004901e242c100c602c010518001c8514000c0b00c0540310036800704c4032803801e10320320503008110b03404054644150701d40d0707960000c4507042420 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 782339244 1250 782337994 782338043
    0xc0f080d080c07060507020a120809070801060f171c1d0603101a070c030b0105092809020a0519050913150207060e0a060606141c0e100207 61
    0x2144000c0000003414410280140000c60310002e400080120341c5d0b80e03484005a00d04610150000d0940444155040c603440d404425680a18a100c050312072a95130341e540d2138203842c140d000301190003104e50303c1001280da603008038108400b0003500341d07a007030041100b02180104c01d509451001c1180d07222124030340c3c0e1001c0442c5108502c12a560f0b411402e10390100a41c030140c6000b00b1040408000c140134540440d402580c900b164408140035807180c413441c02801051080c8074040c02a0400030100d28072111900c03482046603500c2610f0300440e50104919001780800d81d505a82051100700c0c0400c3d20780300d00203000205d0300d5a034545011305151500b031000d40d6900401140d01c225403101034100040e0007000704c40e10006207030009621641207051280040915244d41c0005100b00e260120800103641c1010003180c502d900c2da00014040200c098266104140810500700c00c0d400a6500c0b00c2500d0340240840822101100c0b50180310301c070300c102242e00c5100c0c1074501d4411202c16820646e00600d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 782340494 1250 782339244 782339263
    0xb01050a061d01180f0311030d02071a0d0f0c030506180c1215060a0804060b0a0b0f07110411180418230a060902010807020a030503071b0c0f08 63
    0x24008000000e122840351004180450b15030400c442d14000c0040381c1d034420b02400c0a0b110510141010554038a00114801c8440d1130b814028015504d600139aa0b0011038a9412101c071180580340c4000201e0044809500045000c0880b40e5141c034122501c2c0c142c0d10031520340c1046a140040c1c2c1c0e05006040080404803407890400c026180010006801e40304800d480c40c134110f5002200c0f49403034005007014500138106421340c0081000c540a4039003a030284082e802603020351810000c0d00412024882c903120580031740c40800305d0410558801c4d41040c00104501802000300480150007940040d0540c3d441c448207008030071003c030745051010059508020440c03001c40c1d0030010aa400c041084403403140c4032000c0c248944280cc20001a40101b2850f503201065000740c8295075a140b81410062000c2c0b202a400204041e000401d014000904ca5030b5090f019281c450035541c8080c802c40c1c00c00e522006141e400880b80c0343c00c0b00044e00e0070354014050900d03400700002c09410041c04900e021b202c903 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 782341744 1250 782340494 782340497
    0x70905090f040c0603090f050303090a0b010f03080702010f050c120d0e0f06010501030b01090306050c07110f220605060408010e0c0604060504030b0c0f0d0b120c0319050a0b040b01050a06 82
    0x1d0306000014070301c54041400c55602d400c0118400c0000e00b4500345000200c0809040740c00000200024114082103176080340e403080180701c800b6600c515840140700030300e000092020a040080c0300140d8001c00205883d0513203407404d00d140491010109003048821040412100700c00310341c0d07000142050040400c00588240100440c86204107203650b43c0070113209403818180d0b916444605a407003410000f0185070000400c0c00941420141d100340c60703104020944990ba401030015406107401c0d407104001d80002014580b8407a1a21540e40d00c0c85c882e580c0180b462991154005859121a005030004060070700000030040b51404040c0d0419004020291113044100028402c2d80e800005540039242c10600460480c1c3d01c40d1070000d4284180b8a9038040c0e003102141148110166801220070444151071031812294825407003503484000d0102c03036a040e045510950380040640007c030170081e0081049407920340c81512583c21f1144255819280c8004640043c0400d00f800e2407003c0080109 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 782342994 1250 782341744 782341771
    0x1d0c0411130302121203090303041101030204050f040e01022a011d0712060f09080a0306272a080109060602060c070303051b0d020901020c190611030c010507090509 72
    0x860700c940e4403007038003404028842e080c141c0440d032401e4010842e00c40d880c81c403400040d03a02c0c1050034095030769070421101110303202f0b4203440c0c0042951003030090f60121440500150f843c12032070810003002d8507951a22000c590340c203104800c40d003c40d10300c84502c1094900206980b036981050802c0c00d4407003404100c00d074189440d811441ca640c00041e44405c0380d00b05201c00105400300d00c0d0000283c641e4450410185003015075400501c03462400078003001c0f50980742001407666a90604903400282e6030360254000705840f07468004031041e040f400350b062244100b0410300346402d000c070450580401e100f0300040e10204c014070800d0024806d40d00600303411b00050a40e89440c5030310340d60707a116603100101015294000b0445900b0507503280301c8070300c3c20308a0840d01c820140d0740080c001d4004640c402c3c010301c158144420141418034003401101c4218100c290b510b418440c0c02d4586c5544041c03610864402003100c0c114400d0300303201e0342c0d01030407545d80c0f0b04452501e04010000e820801400181c440c01c40f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 782344244 1250 782342994 782343007
    0x4090b1e0f06030c0c0d080118050601050a0c030e040c0504080609010603050a15090c0b03270a0b1b03090109140d0e04180212060106020f19030e041d0c0411 69
    0x8072188109075aa4045540950300e03900c032000e500700c2d030041c00160056441a052030074003641e08140000d05039850818400e08107501c03080a0307000e4500c15203103e8081502000040881403140f01c0140819000e410319000c0c201282000c83c048603500301200001440203d41031049003030510113a03800c065494002d21009040d600ca090b2600c1c45854001d0468101d0090a0384075441604003440d08ca4205500c1940030755500c14000003036104641e52010445100020608104402ca00106014804004044c01c10141d602c07170002075805011001103000b071a150f4090381d02d445004611850b040400400d07040401c0c0717411201d001060181c80c103181c000f403080240e40360b13120341d480c0e0300c81e1030460300441d59015010181c2d240403107480c07000c1d42103141c2c50001c1c107080030001211070480310550300321a003604616070b07203a445c1c0d62070300184481e400f803800340c0c1008a482481f60101d440c00060002179516a0303c5283e13422075800ba150380030b40d82c101c01074040300d51034144203051250818401c035524048 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 782345494 1250 782344244 782344249
    0xe0103031b030905210114150a06080a0228180b040509040b0705041a04030b0708191a0a06021b04061202040e01021204030801030c080a111c050304090b1e 68
    0xb826806600c3c090303520f0b04808204501c0c410a885c86030b0044000800c04050006401c58800d107085450340c8d0030080d55141c0c44440e040000c112011140540c0d01c2c50119141c6070400b0340a036106c0040e03c010240d00c47c940400303e030001d054400700c40b41c440c0c85415640b0445c0c0e04000302850654088080f81400b40700030015a21695010707a070040c0e00c1318000c0c204c0ea03035000781a01c1901464102050066081301d0162180010200400a4902580c5003041549e41d49034102e40c0110201d5401401c004104808030030320b2440e822003c000a00100310140c412202c0e004110240195131121006a00c0135501c40e946d001000f14806040e00c082d1000e0140e5410159004490703404040000e005036901c41103201403290a5068812200910600c5012400c0504000b08061828001034500e400640c2001904c03000002c4c0700c030b601940c0920051100c415a40421504d0344088400400044150009100040e0240010405016401d0700040e1059204042c00717040c1e00784c0d0500c40b50701d4800c840e420055a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 782346744 1250 782345494 782345507
    0xa0f020405090a090f05060c071a0103031407030924080f0103230307020636102a080a122f0c07080d1103120708060a08070e0103031b03 60
    0x100035440c0031540d00300031700d4000c00e1007100100c00303046409200188811451810000c092260180d83d031400034691501109404c1c41c800c1c480140400c4103803020001044a441c041c0c00b50318001c0c1840300e009952500e5181d000030b221180f00102901d1107611410103604155220f0300034441c2c00350901c0035811942c81204200610701400c1036248060480086201c04108503030361203038054112500c0b0b90310490840c1d00c1c50b05290121413828010000c80036807511034007010711075810051074401078108001c0143e4280c00c00c0d020100c21406401100481d20448a85650100340700d14031721a45c0b00312007003008004c071400038925510542001c100103c1c00d4101c0d01e990500143e03981c1c0b030700185031003500b2a07089440b80d0b0120b80001d018540700001c260f40040b94030f1400d004180c68503a852142e0700700840e1a880b6204401c00c03c40d5894000c510720074800c400f8146d000202400040540d5141e030b052620700704c002da005031880120b6a0060081550040c0c80b0348a00011030514480398980c0d907006400d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 782347994 1250 782346744 782346751
    0x801080d20071206141b160f0506071101060506071a25020f010c030203060d14100e0115050907090b18090103080901090f060504060818010e060a0f02040509 69
    0x4861400d1074041c1031042440260000e005060125000c02654905140030780402c0350142480780816002507048040c00411040c02c0c00001c40551a0801d40d2801851000e0086030a440744c040c4800f50318000752040000500640c46500c0c2c0c00070200c02d022446082d0366254000c2c2d40207417810b00032880010442034442580790380928500020f50748404960f8807403001258540c040c9404c0405040201d80c020035003e1561208900a02545940a90690a07403100741e502c3c03a0031050f42e040200c08039103498080f810044881050b0381c0180c807000f01540c2030350490900d29809035990b83c0401520b007003400302c1d140241000d440d0060b0500c1c00b40b102a1000d10b45200f002c0654400041c1c154101c180200854005c940080020b500342d42c50741451170180c0c0000c402540428120140801c031480d002000108031110396580515117420042c00305c4203242d018141983d80008002580369080003800740015001c0b4400003461103180c43c1c121030044e41c0b41c50080429051040100340910344a8041c055407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 782349244 1250 782347994 782348027
    0xb01020d05090402090d0f0f051002030c0a03150b0d140f04020a12140601150201050a14070c0201030f020d140a0e061b0c0d080a0f06080d18030b01150801080d 70
    0xc48844600119028150b003100040c2200d05c60001d5404008c1300c080c4c041142400f6100f102d144601040c0e85404a120903500001c2a04c01800940d03c4280700341c02c0070742e501501a00d44000c0300c1c1d136401c080006410040ba080e0055485442a0f0000700d80c03c000f16500005c0120121014102500400d1400540d8000d10450004696010040c071030104549a500b0340301c00129402c640c1c1d592440c010007002902c001006509140200fa6811124000c1407085402c019902d030f50794603004421358052101041c01c0703040c95200d038501303d00e00c051407014091503e01c030b020100307058440000c0c2d052842401040500094034040c81448807000000f012640041640082907164501e035105420500900c00088417500c55006040c9006a1040005001d401005c90611649644903003401c280c64150203007541d640d00c52101400e9107441080083e5810751105c12454006417251030714200442e09800c00e0741d100c42c2c110312441925504c2080a030040507000090022a40310351001081c00788407410000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 782350494 1250 782349244 782349247
    0x9230c0f07050d0e100f08070810050a0905100b07050307080a0c05011503051c0206061003060509100f050603090c0411090a12060f020f0703050a021203190b01020d05090402 76
    0x1041080d01021505200e801504a400c50f035010b00c0d00900c0d005416803041c1c000c051054149036a07500400c081d40705128076031152075003651841000c4818040040c8880030000e4403c4002640b07884144842e0054040c814000c60b0b1403510b00d22405400c0d80c1c03035100501ca50800c00be800017041000c01074032541c9502c9806182e544070005e10840d01644802000741c9554a01554004da94078805042406c0f00d120381c054410058080341101044203160800c48050307000880092001d1810150004103401e02d42030010b0400d03105c3c0301154146000302d500407105501c911082c448081140a144c00402d021103115183d03180131001d40c0c0c1c440c0700000d45030b40110b45a9208114030b451140c00d560320b485001d0400d484e0f103035403402c42e40d036102410301041d9022031420300c08940900d294022601d07144100d840e210f01d0f080844e074007204d203a40314000f4031085004440c059900306040c4001140648002140320980398013040f518070844683d0081705040d5032042c1d00030758140da081819503044110072107006 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 782351744 1250 782350494 782350507
    0xc2c06040306050108030702040615050d180f0c060810120204090f080307170c0a14030705040b0301060801150e1c020d17070b01060809060109020703171009230c 71
    0x20028051600010721403401e110010500120000280141e03078000c036000e0000c15a02c000441030302130701c007406000058080104c510b104819400210034125a04802290403189455105500d00c40074411203c4031102442003010710790003100c00390030052100e034120000346000342c0c2c40200096050028003850300c90a07010b0038000b007803107140852500000303132f1507407442e02440040c05100c2c0000e4400403403801902050f0500552000d1300c3c10301046440300c140011014503d0086604001d000c6010014200004108a4502405903000b00040d484541265041030806000715004101c002c081203100354050b601a900c543e2600086000d11410b21461641e900100314181c556050250061603c03440c07091550f031501d4018030f6580c0c042c043d00b55450340c8070b000c1198101ca040e00c1c11940c0780e00410041c41084110341c020b244140c860b04150401c2c0d503890314181505c01080303c510b00005101c0b00100010203150090070b840250000c42c0101034000040c4046d00c1d600050070f43d0811601c0820013 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 782352994 1250 782351744 782351749
    0x9011a07060b0105190206060117130b06130c090f0605070507140102100501080a020f030a0b0106080a18121d09011203020a0218060406050405010608040308091f0e010c2c 75
    0x210785003885c0c00041c142818001045c043d40e506c10548a160009550b4010404400100e801e4180100c06a44a402112800c0d449641060710040c00460388400c010110940450862027400f04c40045034071603040ca02d10309081820610703c42d9000006001007001201c0009130042102c4054540c0d0240c1c00503600300200040f89081030805a90030a285808008600c10f5000140403900754421520b1548a402d0482815211802e6003802800d5800803401400404d0080c03078000d41c4103401120000f44c0c425150240024521408415034081c1100000403d08540c098165041c007814408840d207050039103408940c16801c1481b540300d0107019460080101407003440a031a615400030f1007100c12410203a40d6070b0b882401903900078030031403510400044605203405598100c500544840030380356610345058900e1440100980304a00400021002030240f40c001c210183c4082c1e0390019500741e08104050850303003c4010442030000d6288a80942d5420400e4451100440034000011000d400b02 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 782354244 1250 782352994 782352997
    0x10c0b0411180901110a1713060204140f061617360d0c0303030902042c070e0f040210090911090306070e09010915090f0b09011a07060b0105 62
    0x11610b9001aa681c054040105041a407600801ca6032000700f0202d8100144507216129070440040030030300401c1309540f010310600c050359001404a680d6001d00b11240d64500c00c982c4260002680040040800c0449c1e0902d0541d0a41000040c0c0d007440c502448680581c03249402100002c000503c0d6840f003070007010b2a42c00fa2040b81420724520f45000d40135142c2101403070740340910042081641c3c00848000c1c80d100d0003612903c0e4012007460046411074a045024000b065400d9800603122510b1480c02c0b4101c004106e1441e20b070505003000301038140d8806090204d6036028141140031501405036900307548009540183e81151154a002001c0006030707280001c5078031400405140426412409007502c00078840400100c3c1654260f07640c2c500d00b82e9010b03200c0301b522600180210010300050910f54090002d500c98008200302440d56401c1aa095640b0341c148510466141d051b02e4610b400c00540440c0507110280401000c1c0c1c0710440140f2083c004d00d10003074030031915560080000d034010340 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 782355494 1250 782354244 782354273
    0x1290d021b0a121103030106050d050411090702032d030a0c020a0b0103050c01090806190218090c0d150b07030f030e06040b091204030201090e060102120c0c0109090b010c0b04 77
    0x307907681078609060203086000091840000b203a0b0348184080d0301c413408002c03a03068038100d8580c141024040704400c4c004001c010002c8802b801c554021580b1903a40800303040c41041d11341e0041d65592440c50024088445203010031500400400d000c09007620408140c0b98440c070903c0c000901e00d103910404070701d0f100e4500400741815801c140040248980801c0c0b01c4807032902030300c07108040c0750383d90a41599100b0490740302000300e003041d9041d0b1103080c06800800c42e001e10b000c8524100d9141c8000140184800c2d21501310700240001c44450ae01c00c10f01441c540917203800a0103150600d0090071121502c1815402010000e00040c4c0c9095140680e0024421740e2a543c22682580b80c03515061550807004d03903440b0658400c100070b011401401e0001c54091741c1d41079685070001072620801c5081110003801d95030640c01680000e42280c100341c0c001d84243c92804000706007090001001401044558220600d61401c0c800c016441d41d81110b188185c465010f08a19002c1e80c0d1418241003140400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 782356744 1250 782355494 782355547
    0x503060f0c070b04030203091509030d121514040c030c050429030c07050f011505060d0b040c051209281104020c030703080c030f010b0310080106090501290d02 70
    0x4030030700c01170680c0080540108070080d140e4a000315a61005d080d83c1d03016040129501d948036142240090780b00d00712801641c6d040b16008256809182100c110b864034541001210300d2901d9204812032504c0c1c012201e2007101400c04100204050038003c00e644103d00030441e003a242e9600c10100d02030801030410442030340165264032802c02645482180d800721800340d85520440c40c1d507580208040c03181081400085a2410483c0e01d07150134080d80303800440c604401c0b0341d901c20b1800c0e8561030b58001d1880c0d28071242d0f52581d0724007d108642d101d48201034040e0140c0e41c40b010400e00314020798502c006000c0403100c04800945402d140003c0e0b07100c020502c540d00240041119248614000050900f20344280c403803443c165a0400014a6400210b0303003100b604060800402030782102d4801941c1144526407078141107511061410300b5288254052000580d5484c01040540351107805040a030540703402c035001c010a4182d0004403030242c1100c1070015035000034103034030b0f400c4201d20f0b03885540c030366 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 782357994 1250 782356744 782356763
    0xf100e0403120c05281b060e12030405070b030606040528030305040f09090812070903050601180c021605010e0607060f0f0e0a081210030609060605190503060f0c07 72
    0x29400041a607004401c010300481e5943c850000705d4a5008407048400c01e0998a81003542900e045410b11340d490101d041c0c45450351104040100d0406106502100700c116a40660b80e05003841c0040c40e042c045e500c4861905020b00a100d0b02d90380e01b00c211801c56504441c1e070003003d480c40d141030700303015010301c000e03a942d0440c0c180000406400c40d026100721440d10320100010380e65415243c0c00d071500b180004101e02d1042040c000703400e0040080d2508405035240c1b585a0300e07142e540d901d10b4050300384c0012400d0b8a50b503208520705041070084440c40d50003440600740d0480141126480003023070f40203090502c0144050488151070701015a60b0054010900f448650342d03c0d03030031600414000382c1c1c80341944e05020070a4601980040c1c071160040d808642103281200c407880c100c0c85440050802007003142e44400000210342c03240207000d0301d14002d400025007a031600c0c040060b5200d660100f6030121402075000c110595011500b20750217851000101c80c29551301e41d0300c0c02c0b544034030440107081642 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 782359244 1250 782357994 782358011
    0x130605070204020408010f0f0b180121050601061d04110d09062403120f080412050403080315010e240c07121506090b1f1404060e090f100e040312 64
    0x300d8105004040c0341240420036a8510412700010300070070512150301440c1240100a03c101400e0000648041900f2800703030b5a0cc1039480a041c040281d00c81000079007901e41e4403c400c602a0100149080200d904101a58000c540301c0c000307010760181c442849a84410f640305005161b009140313498040c6013070ba07001070002800039003c09014042070310301c00000800d034003040703008bc08242d11416854031485120369441c0c0c1c807450000360101a4004006060000000007441b41c07015500072459601e92842440404d80010034050302c0703181440c0b0424008005070b40d000c8503400c01580580f400e0359883d50728498008030303034a400001d521400c584103003a101d000a00c98190b2a04801b050360305001e001d0703260759800d84000e1303402691a0326400368141d4450b860020100170810078000c0315003000c803511012459000e407281c215521410100e4115159001c070703850441d074000e9004038100c11124560511001740304c139444150042a400d0007841011805140c0901d201c9680710344d5500041c000c001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 782360494 1250 782359244 782359271
    0x80109030e130b37050f06070c0302060403060e0c030606281e030b07020109050c040e0a1713120804060e131a100c1101050306040b030609010606021213060507020402040801 76
    0x460a451041300305041c50384909291001c1941042120360090040400c1c0c0e0b84082000900d9102000845003d041e9100c00401a00c1304006880210301444000401080b064030507800c144044820380d2094003c0c00401078240c0d903102480d8000b80450340070041c2031134407007042d1150745000c3c0c210f11b01070700643c100d1240c450400c14540060381c3c822920360303c641d01c3e640c10581c00e88220380c01c0202290031400311035050f401c01c0e42c408601c1001e004c1c01c50b00e2120700c84d01c52011141c0070303c1c64034510120000e0641c0c66040c02c6e4800301c0040c1420b104000009483d5218009039008500500d800c000c100c4d04012010764a02c035030518800d41e140800c200b90405038942a0107140e002e80124020f60300d14241d1150300d80100054040365400245121206102c503004543c0c60348010700203913015039120380210560f1400c201c810310070740701400001170321b50174120040e01e0103c40d2039090b61504000c00190a805450005a900303c1d01e443c10200c0d110481880080e01030300440c2c20885696190800007000e02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 782361744 1250 782360494 782360539
    0x905010f0e060705091e0405071206120f0204020304030c05160501031b1e0201061716120f0305030411091509090d200f0102130f080109030e130b 64
    0x5019468003080007101d081c1105458900c221400004244103000080440c10940e03a906130045840d003c451540c0c001d400090f04032002602c1140c00107044c880800e000b1101441803001400c0007209443c0d0030a226a250a42400c64110090085401001080c10103004000d4005100c1c1c0c03000a8450a0750346c01810b44071a5214401c0c0ba00290400c60a50140b20054009266808440c1e9459500702c0014902d400b04c400030411800843d96103010014007020b82e00f858040803c100c0c40501070704101040d0a60325181d464208090450a603400000083c00c035403502e107406985030401903103d68640c14042e804001c01d145484c2c00510160404c218101180200d412003001292803282540703844102e03654890000060101088060701c0084c41c0c4d24482071600c140c00c3c44c40048642c6088400742e03d07800d90b00100700015403801c001c05d061108000407010b0900dd480104000c010440300398400401490a0030061801045801a501010300050308032109402002e400742c04071b00c0c40c040c656000f9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 782362994 1250 782361744 782361761
    0x30905030918190605011e020a14012013170a060510030212010b09060f0307051305070807020a031d06070501060f14012606190e150d0506011a04050301090501 70
    0xc03c001c400b03040450000e11600098803070603034400325414501419000103c5942450034154401d2800d442d00041007142030140c00004000081a08030b02014a0540c1415070303650070005007402e01524500f82d2010941c80100c031580442000da40309124441410403203401c10240c403581c104410410303640c80040480b41124821754180c0c41511641100d42e0807030300b000701c00e0fa0b403000368440410094500083c060203c042c2c0203054a00b5182d035038001030003600071441140100b5480c0c500308024260002400c645c446042c0c00a03110004040c2c1e8014101d050709038140508444004075072540d80c81d1070064484165201008000c0c40d5201d0410849155141c403404242501d0800c84c0345903944a1030f0501080540780143c09100c40c2c0c80141ca02184034010708258100b000c1c9203591483c2d078003a00d0900c00803c00d00c0001005405c0000c005488403d000020394040c0c1040040c10000483c0040e000d130444009098200301803106100800c900d11455105c103a0660174040d00b03030103001c010b511043c3d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 782364244 1250 782362994 782363011
    0x3270b0406080a05040b010905092b08010611101104030f03030f05060a23010c05030301030b16030c1e02010f060303030b0915010c0303020903190302030a03110301080a03030905030918 81
    0x24507641c8503e40030a90310304540042417032007204010000060344d500056044018202aa041200c0c4181c0300d49144022107810f0301c0c0b45095246801003160480f0b00039002d00664a40282e02100b0700c202a07903101048100044d81c95640e0000c0b203003402c400010345025640c070030055820200c56040081c0907011401c100b40c0154904030208049182c042008811200200e034512072100004129540c0b1a50f0300c0c45542c140f16801c0c0c020340c009142403004502031445081500410b041071001c510300f02c038144080905140c0b42c22100c900700358009400481e010100e40d80c02e200c100b0313401022405000c030a0381980740241400c2c404810140c054201045040c41a6080d0101d55140280c2c00b00544040807441d0215445041d284003081c0720303800400c1d4500c40582150252800f4400140128003140b9054005030070126000741000d03071600814100a425801250030343d410068096103a0605803c000d0a1603901c01e080380401005101b03035410103000802510202c19510103003101080e04503038042 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 782365494 1250 782364244 782364257
    0xc0b0c010c0503100603050a06050d0c06030e2407020705030105070215090c090105150705030a0503191533180815071103070b090313090b0d03270b0406 67
    0x41c001803051098a204014500603610450b141c00400c3d40100000340c4040c108544504003c5500c0e2502d0348908001381c4a54031481000e80361100c020100c9140603514003c03600050204e0018868850200c0c01d058007980c10011941ca41e8801a454103071603621068143d4200420490519004a0b5402400c45182160240350342c0f020b404646a641d00358169038000c0c543d000610441c1081e00c3d6407050004000e0300710b440d0004580b500e925507001325503c1c100040002041200000d003100850141c031040d00410b0041001d0480303040802259805a4401c40c0f00b1515a09000c0c00b8800c204404c54a4041000460202c1e20300001d0079411205090000062007410005480400040000070340150050103081030302c07071b100103d5009040c0300394120248005d201d00d81c0400c94460b51680a0007008000716030f0340303100d08010050401d495000c030300c0161034807403412a9920f5981d99100d0745645407514058008030070805c480f460041110688400250420200c0c66102000c020015104d00d500c880 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 782366744 1250 782365494 782365511
    0xf04230604150810020307050f0705030301140409021e1306031103060603030c06060d0201050d14041103030f07080325090302401b090f090e030708160c0b0c01 70
    0x42c10a85294031a01d120f0f9844040d003c8803042c481e0340078540202c041d24044d071030001d55a80c040d281e500011800d0318503802c00001000380401100e00c4914800c2d05440a1040001c1c41e00050030320341d1115007020b01c219913a055401e6a5564064205128002440400505849044c044170500400921f80c0c06446001c0c04101c89241c0001911b40180904004000e50b0351200c051242007031030410120705029007800000c910400e940075220584003000060104c510309821302c000c10506c0c40369a80e0290700100b15240031280c50070104c0d200550000209544ea4890a0682e001e030920100040ea0b0a900c0c2d19006c01c0703041e40459864101c90003143c103291140b610200c028509000b403003100311024050204624036400c0800a05040303503000800103070000b10002110060742c4441821030002e10044024460f0180323101080001e0103001404201c40602e1407000c60b901c0c424804050450400810b1144080c10314280031400d032644160203d18540c0c0e41d01c508551908a446000002d5003491b462 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 782367994 1250 782366744 782366771
    0xf070806031e07030b0108010509060105191e0e040b0a0c05090f1215010602010605180c070b0903160f031b0b0c0f0d33050f0f04230604 60
    0x40038000e400041c0580b21015007111500d11250100440c0c107294040c01c4000804520101441402401c0007000429217292a0100b01d051580503003007541b10340c040a011a8084032070b1b1002d40196518110f5201920001d2a0403022881807940700104207400c12040004000c2d8855405000b03403580e600500c50a00404015200ca001d00070160b50001c14068110000e85001062441c0f40c050b40011b0701d03001c00b8411251104d08000360440030150307454210030400390a00d00480d4601c0c0c0181c0703a01d1080380c28000111440c612466002500021003a004180004002e20403540201500000083c001d1514508086d02c12032107001076004c11515070a60070803030f48611900d4011540840590520740d200c42c10350a640d00074034000b02000340300f80000a4080982c1c400c2c40d0804408502c04000004501c0040252100f140c00800e007940c600201006151500710100c0340c441d204a64200c1c0316038003080428000d11400e20f840719605004003001a008600c1c4a9030307800b80a094800744044583d0360300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 782369244 1250 782367994 782368007
    0xa060302031009061404050c240d0c090806070206060108090c090f1e0112120212090d031205070903020f06070201021207060b0307060906080a06080a020405091002120f07 75
    0xa5010b400079145807040c000960b0048520b503120354800500c220500d140ca038021001290204c3c0ca5501104c50340d141454040200e44000c806540b00281200b00034096000038007400780001601138503074510420321401046180c02800c1c2c000121405840c1480c002951010180e9289000c00c4150006c66100c80300824074900e4184013405802c01074079050520560807000a1501d03141c4a81803080070085042c4da50594000d02019410301c2d444004d60900107880380000c0310003825903200e607801e00d41c2410003000340d8024110880c0c09071a05c401c0d80c241a02c0c4214648880c007402450f0208204919400495001c00d490094a50480c424004c0092118501c602407003e40981c2c4490010140c1004100c0240b21071841980c001c51001c8015010a00d0b20303001d5007111010406059051000c0c503440090194054501c83c0305200d410b2520b5a09504c683e1320f54000b0b4061a21394002a07101e50041003102d02c084c21807041156140c20305070800f44403080a581240a21000d5400704034144e10942 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 782370494 1250 782369244 782369249
    0x10b0406150519050f22093b07080606120309011e020109080406030e2503060902030309120f0c1e2806030c12090c05060313060f0b041d0d0e0307120804050102060a06 73
    0x552580002801100362803108c19140c0c0c203441c4072009820364403440005002800c0248035080081c592030034801d0812085001c004c0e100e1110394002d0000503040c1e0390003512408801102d241552402805400480c05820302080240a201d0000303070002d85554107a102503c50300381d1400740d944030241201d40c80341710942d4640c030f40200e805d01c107428800314104c3c1e48903800941c401800c50703241014100104100c0458001c081041d60018183c6240e03900081c00300c655000780440e400d00b0010469601010501444904540030314107044401084d00c151510310502c034a1000c1c21841d0590341d0b680020081d0000301c3c88400001c0480440c0440c40501e80190804681c1c08001d07119224240820301031a0b07040100750500390003002181c80e0100c0da461141d0401038032103040100d000c82c550000c2c0300c241c070075880868102848010b40e003c0c003003801103240c608003105071070704601c0300b84804e0019240640f99000800806c09044c03000d410070403104020012544280c0903901603503079030b01c0e00c0c208a51062 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 782371744 1250 782370494 782370521
    0x30114070e04020715140f01061d06070c0f081b1e012715050c0d110a08030c040305010b0907120f09080705010b0406150519050f2209 59
    0x9010850460044080c85a19807000d440103041c50303440d0300c030a0500f41c1040711100c107565968902c650b0260041c2c800341d902c42c1e44010241c100707500d4050000c2c40346188081900b1610344011405645549440072500071503044050b0001103511a400d6003c000281e2154018034031a804466164500c0803100e089584002092444444900a40400f1031582c0c1130b001410481c1d030040c1030400d5446a580076814149280c00b5031031046c10184103008202e5607624105c188041401032035041080007038141d90781e110515189068056000c03042c0d00c0c0c08000d8038000d040c5079000c0108481e059410016200710790140001380070500c1400d00b406540441602c07808000341421407010031800c0c10380c102d54042c003001400003c02c0304071502c0c0c4170f01517041500c0032030f0680d444504000162411b40125001b4020501203201d0990389881701403d14480e2860707942c400403681008844503070159060383d5031a11034910307181d5076911003101c146001c100201e14090400088201050b0f80348107126101e01d40891 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 782372994 1250 782371744 782371781
    0xb091015030210091701060f05010c02091305030904020a120609110409091704061806020321100512160609030b0f060d020303040f0503070504050412051c0c1d0301 72
    0xc5400f0300071201c08a02040c41440350002000070012001148900d810041c072000191690901d00140480021681b04030704000e0400d1088000da95071060780c0350480e1450744c24400043d010700d041030a6000c0c10510982c0a8400b060303072615107811210311401080e80130020420561544030040445880b0716004102c14802c0c030043c40f41943e180c0c80200307000d000301c00300c0d049124240a00007084c1e2161300b02034000343d44990b41014040d281c0c140c480217400d007030001d1070420b60034220b148aa4080031890344c00009406000c65076584c500c45401c8060180030349060b1000c803000800c40e40d03e600c121104820a00380907000039140c3e204080d04d0080d031303a1250711102c607030312508100c00c1410805410340340d01c43c6515040b400107035410001840141290041440010301e0441018100801a404a030040381010f0401c80018032021060035284064140103445100710000401e00300c10900003051f44501d84014450b046402c004100000b041005044030b1668403801131500707842e651180c2c560b55944 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 782374100 1106 782372994 782372999
    0x7050a0912141507051e0d0603142b03020c0f070f1d04020f041512050601090608010c1205071106040b0714041505070804120b091015 59
    0x2403d0320440424944000050030a10900c0300304c8a805809808494000900d0810b88040090f0b2030802c000d80d58407491f00c040240c48801043c0002c1c1302d022980100070070809840d0b008103080c50501642e5907413507402507003c3d41141c0007981c9180070b00441684000c03c208242c6000344842103551900c1171902c400d0300d00b01d046188a1400220b4040304010150701d85031000c0b4100941510002404400c1d1326480007001c169402900d007903501c138400c5a0a1107000924070b41a9040030341c040144550300c001c3d1508803424149024041121000310070300016481d0f0005074042c0540c249580100c1302c50707540758106441150203c64081a40e018000c1040c1d110003031020700c80c00480418079007405c2c20120324410307800d82a00f00812030002558001c110103003060354000d0118038001044491149001040690120751428261003464030329004400e10f4001da44030012070f031038540100c50 = true := by decide +kernel

theorem cover : BRFrame.Cov 782194244 782374100 := by
  have h0 := BRFrame.cov_init 782194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 782194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 782194244 ≤ n) (h2 : n < 782374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
