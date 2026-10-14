-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3126
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:44:42.853835+00:00
-- url     : https://prove2.me/submissions/af88ce41-d513-4ccd-8818-143c5f1151bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 562050359 ≤ n < 562230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 562051609 1250 562050359 562050373
    0x201021e070902181302090609010e03030910050d0b1905012d0e011d01080106050a03091709040f06140f1306030506181506090a022701030c1b020f0a08 67
    0x101d541c80e1080b41200021200410410070701710120040e8421000d180d07921203070400848100d98002d00040d0201704004e001c881c02c2000f210045603e00002c601160089080400c282d034141c1254007400840481c1601c540803450400a017462308945a8080c250510003902c06100b074000c3c030300f4551000801008107011800035880009485000c40c4020140050740c00240d013040300024a80d43c840c44070040e07482e04c4041c3e1800380111800e03040034050000700b58813044840040340b116124014031400f0540702e183d0b41c82c2d01204210031a02e070004611082800c082c81080100e14020b102c62801d2000c6d1000000039042c0360028104d41d83ca8424850814a8040e0200c248000050082c1c0b2846102c80c00705020040b904034160740340350002c2c90201c3c042083c000a2291300f00805065005101e54070302600304240f03d800c6442a240440d52088011007044c0d050b906581c4c14040d4080c4a0510b0402c8916034420441250010b400d038400607010307004205190200d5150303440003000500c0882c00755003071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 562052859 1250 562051609 562051627
    0x130f15030c050a060302070b0403080705121f0801051005150c0f0303100806010e0106030f060e0f070206010f0b030a0e0307151406010f0527030a030809010f090201021e070902 77
    0x88603890042a008415050f40410024068402c9039255500a641d200c2d83e40c2d02d0f680d0440703402c9801800c4c201001000d0129240706500c062800c4d0003001d804291000d0124000104101000b180d40f0069542e8100401d011401170582824016500280c0d1130303000807820141050300c20711031190001a00c0c400c411030a145040040059402104100c0c85500310950341c4d41129602c85080c00341030740103200c4200410040f4002c0d80807886581c3c840c1c501103002503a8400000701c00c074003120712510402c0a941005195903050010a0241001030441c5e00414101070240d00f05000040074022081da89141c4003640c03c00800031b6481c0759500c4040c19030390100000d10700029161100e04001c03617806410218880d0340c05100e842c81c05d4007140c0d03100c505041020307140b484205400c0c894900190540b41078241c45440910840081e540213450301802402c2446060b800c4540802d5410440340c41c110b1060b00603070740411040700c05032001d0800103044066200007030034114954400040b89100080c80c0d04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 562054109 1250 562052859 562052873
    0x150a0b0a0e0406050604050102030406121d01020702011106090a0b0a060f082503020112021308010203010902090a090c080123031b0405090703031b0314030709031e02130f1503 77
    0x40c2c5062010356650802d0180c280201c2c0038140c00368101b0f01007441040c1c4070319209841e8400c140300100f0b031186c1101c0c2c010503841c03500c2d0b4072130440d94002900f0b005650b003000d2248100c03a51800108110716101003d2521518900342c0101181c2c140030101e45046515048540507100801015411039900c0d40c24540d070300200700308542011561189241e000f01d5420f8403104032072301078580030401002d00303085000a40c401c07184102081b81035240810620824401b440c0070704018900145e840104404118400c42a50b210f2002035041c50249428142e00401d200d04440c2c1c002c0c0300902e903041e04005420f440d6941c0b403000360140315040c02000c0300401c24106060561054500b000191900708407207480320301d54007019010420100c80c01d00c0c0a6840225040014041d28043d8040f8081110000f100d0340151100c40000d02204d206100303100d0309561a41303055032620b514165941403a8082258001e440351007903200c0390380701244120182c8c503030810b02e80b082c000e1418100c0503441e0300e0181 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 562055359 1250 562054109 562054127
    0x180902040e0d17090604030e0409020d150b0a090e10150909050a06061403061611011103040204050f0f040209040c08030d0c080105010504210203032a010c17150a0b0a 73
    0x503c06401408207090401c040741d220b01440d00744d0313a0810b080b215502888080c207031401040783c20a014040d09000314841091351424500240004102c110b5900308000403281250040204140340901030088003030005060350703094041d44004500038503c84031401c20785505900c10602c10b41080201d204000e00800c0d0300905502c900c104104464607654180c00315030740c851460b90940d000070702140d0103440381c54030603203c1d040c2c910304400c0740821052518291001c20314246030b4440044180811480c0c40d0082940c480d05414507485546040c1c030f00c01900c4500504042c3c020b003000c60102e02400020684540900712510440f907445140f103940000502c030b9034103548000740d4150008550b66200318200c80c101c070b848103440d000040300c5a940c2c004000400c00201d03071511042100c0707076a824001c1c2602c05c1c54148403101c041e821402c201c4007401e460416403004200031580c0c10585410229051143c0c000780701ea00425a00c48450300420740194042d00040300300310f0085002c114035a4483c03000c2c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 562056609 1250 562055359 562055387
    0x50c0f0105160f082a0c062202030d0c020301061a0706050f0712020c0c0a15020d08040803010311010c05031b0c03060402030a0b10030f060902041401180902040e0d 72
    0x18040034202c80700480322282c400d594880001c8810000c90080c0b400100402c131400f8481450070300c401c2000f4942001039010305031017180e0340c010780d08000c1504a1249441030400c0c4050300e1344100c0b4882c0d40001e1310f40c0180b00c280e205100d0b0200c41502952000d502c42400b410302601e10280296040304280c0c059002264125255401d00000980f4218180d2119000c0c814585075255901c0140e200c841c040c2d04110f8821026104464400856a8500c3d002c90000c00103070303051091844092400a0400910061010612202c10280800619070704112411207400860384400c44070b41600403514070407030341c0020300584408501d044420b0041c92801005040440881b5460340410080c992a1501100c0c044e526401c800103c4000c03c030f4200685601c0102828105800783d100e544079040448240010795480c0e50b580c9503841142003d00c1114010021070307030907100641c0740802c0519000d101d11300048100d501c0d6041c0d50115101c58010743e005080300001e56a40d800c03401002400c8085024403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 562057859 1250 562056609 562056631
    0x60f15100210091a01030b010602070f050105030106051c050114030d0903080d150807030302030304060b0f10050a021501030b060a1a04030b04140604110406081605040b01050c0f0105 80
    0x8012051924a21410308284540c025200745081c1d1a0041c000741444002540e010541e082c4c030702480074544603090701030b5108488046c00f55041400092030281c05402c41180d05000950900c40c580c0c101040da8111661468910ba1b589032030300d200400e8007111503005d400c2e9400c040c004240040100710b02d26148030b0503000c8450f84a00c40e001107400816621020b070107038070300300154482410f031a04000c103050030082e29034104503036031040d41d86007944940c41034006804c04418841008014094030b8003c41c3c046903503181b1015440001400039264100e050b05200380001c401400b24000e1001103450740c00051486925a9682498001c05404540c894841c0d144407802003441001d1000c44201d2041403240c00341002d0859440303003a05200584180d030001203c9051615010f0100315107031089114400d00c0c0e11a80c0e2200900c0251202c03078014100a07004005003c000b9000050940212002110302190f59200301d001a44c0c20f110b1420324a4546c081c1d00e4600c51000c1054010601901010075 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 562059109 1250 562057859 562057891
    0xf020d0b010f02011104030f1e060f14090312040303111b07050102060415020d060504020d0b03010509071203031d030417061b030a0c0e0423010b0c030a0f050c060f 72
    0x742207080f210849242d05c14842d05020034001f0507075203944c11341c07420300c54201100008a50b180c581c40340381c48400d04903807443c0c940c0b54014030b00b0180e0183c501c21075408180341c015402c0405140b0703103900400d64078a21003c0301030f0000b01407600c290080e0303404016000c01c3c60703610078040d41046d0034401d43e4214000c16201c0e90000040a51001885070700c80c5070005200b20706031944640541c00b035402107280110340d46d1103420104841c0d94a100a0480d150380c1040001c01c002003405242c25120010418450392b08004420404103064020300b0792007d600d0704d4001491300100c00450602e11f001070302c1c1c100354840400c012070302c0740c170407100840850040c504850003079550f03003404002d02c0f24491403041c01035028001310b01c016400f500308441d0312803982010055805004049401c845034449000006004560b40124540d8286182405000c81303401040c81e04a600c00102e55074170a4981d10300c00c2100042d01001da0a100f00c0c1030b1900076440009550031404d010f0701005e5116005d42d02800b0306a0000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 562060359 1250 562059109 562059137
    0x405210705060f15060a03061d06030c03010b090601050a031805030408060901020408120304080915031902070c03021c08030708010612021603030f0902030604080c060f040b0c030a0f020d0b01 84
    0x50b5400e031280c4080c1e001c4e65280070001082c045150842c001c80b00c141030719030340007181c107030b10394140e80101010f06015200140303092000c16160148104000d40030780d251902c00c902ca900c0e01c0888560014080c201079a603181091030440040a000c04c011a20b8078010425000700000480100102d451394401c0f0752190310b5610441e400c03440f40e4469180c865210040b040a108c0404000e16401382c0120880c40c10112400085045980c00c0200d100e079100000082080b002e2074030a91807642000f810342141004400d03135594003004440c0c00064172400801443c954420318007100240007aa0000480e03449050a48000c1e044103020702558020850700a01c00c00e1940052003503680038104a0400e007510741e441c0c0c500f07600a1132040781b1040e00b10345402102c4003584041018a005511030644683e49a000d100101d0500710003611400d90224001c0522001c80c1007a20601d4000084101d016926201c1d03080a40c001d102814003411802d001283c0c0c9041100254420aa00c2e402a219049112603034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 562061609 1250 562060359 562060381
    0xb120706050306192408070c020105180301092a06050702010c0311011d0a020306060118030303020903011b17070329040b09040507061701050109050108040521070506 73
    0x25006200010740c040c00007405914205442460060981c84100e01c903580f1040f102d412012400342e0041c6000740c0160104032154400c80d240c2d030044152600010420050780020540c0c4542c040030707100f0002c0300d43e0b402d440755003e500440c075042d0b1141da05284818103020341d81c1131111764030300d43d4032441d10200001010b5000b007007210300c02c83c0d05940381c201125a5550035202070071900485026503603100d00990b8040740010752091405c4244c0020a0841c560703204151600000914481c1000300c00040b01c40d6070640b44401400707490345800c003d03071234445050201e0b00400f010a54144450515a54100c6154005003140e11001d560b1441321070a9664100079410f903140b104031a8a0124045003039003c507000144480ca122038010300209a684070b07403000420407501030303074203072110b804c011010070842d0f800c0320350110202c0d03c1d500f82d048158544400030b050719101d8030a56050002d008000b604210051254001d5400c03202c450340d950303070240d0030465041d411514040740c8a00c244004180d41800c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 562062859 1250 562061609 562061623
    0x90611100b03010b09130b06040209150a18060917030a140a020313090506040b040b09130809060f04050319020d03050714010c20060f0c0a050f0c0d0909090b070e060904060305010b12 80
    0x500600213300c205407220403140d110402d08001c120080054011520f0302c240c1401c003e01c00f96480004603418521860700e94968842d0041040e8010051031034590340000c88043c81d100501901d5840e110b000c02c040e13042d44108a00648845101040030a541040ea40070340e01421059504010f40800c000511040740d54080310903030b010b501c010010701411520003154074801e00c03c0345440d041081c52000705010307402140c1c0070340800002080c24001d0303080c2005400c00e40301d441d90010340c40e10140d402041d140310603181e0150401034001441e00034450042003958136807841034020006690413400040085201c5101c3d948000036000c0300448101e0002815405074000030000d038a50b8640b4420710240f40d101c1c06c2030b00c050000502c41541000480b10242c4020204500034200300507035224000c03c102c40c180c01a50559240111400104080140a642c00b0409080503200c2d2240d01002500e140118042242d008d03080c400084200314042d0001c81c01440d003940c2c0b4403042190701c44400c0e21400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 562064109 1250 562062859 562062877
    0x801081504020909100218030c1815010504030816121d090a090c0e06030d0908100b030304051c060b120d03020a20060403090611100b03010b09130b060402 68
    0x142080105000d031400181c3c2c10341019051048502e080011242c0405a8010f420502000140c0c00d00d54140c0d820144110000d441040380c4c001160450707000d40406800c0081c16a200140c0504e100c1d41459016038212000b0b90342008445071142d08108203071a042c54040c4e800c440a00005002d104c1c02c40c0a6641c004002100305c401c1c02c0708055110600ca40c6243c002c01090f030668442c001c0c0e6000c03426140c17441000c0c01049480c45200d14221041c1481d020201b511202004513080c1c00b004031000103e00c5140b020a0b250010811101140000340b0b140a1030b0000c6500416900c012412142d01c0100d4281580c071440302400700031505030400600c0601c100c2d40c0309540c1c0128070f985200740d11960040c402c03d9043d0518210754075520900d420003003d52a18200203a010200340810315400080c2400101700500d4400641d00100c0f0b0622b841d8202d03141207204e40b98542c241500c03607940c290002c070001c000203090b0308114541106040340c0c0c1c0c0d0040d24103903014141070020034820b06050089502e0b040d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 562065359 1250 562064109 562064143
    0x801060609060806060d090506070201060501021c030b0a0503011505090901020a0e0d1e0c0e09010902210a06152d0b03040f0f05010b030706030e120f0c010203010f06080108 76
    0x516002040d40d02e000d005140941c840c0d0100146c40280c0010320130401e44a00a40c0104150715003040007034211030543d0401c60546d4010451403044450200072000c603030b5028500440c010701000041b9001c61200d41140c3e41c154201201280b00c0b01da032101031022240103c4d02c6603c0d0b601d5a03a0300d2403c03845070185880c0051014404202c06042890001641620a1403039103420182008a002c0b10713840e00104451060783c1500410070244500d0102c1e41040b9000d0080001c0c540396400a00e0b00b42c10603004804203254a000320a5403d010300610443c40c5d04403806000b0f90050301c2002c00203000703e0143c4035521b0205840384e810707481d01907110004ca410005440410600340024440c0d140c000a0040740c1d407207041d4030741200003104100c408620703610960010031200e9000d0b040608100458114500b09450031b002c4c0706008500181060400030045d80b0319a442a440304110b80300e228042c0c10b41959800000005105500065890308880fa80d070740e05d005690300c0389022515018a032000b4410340c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 562066609 1250 562065359 562065377
    0x12615090114241309080d0f0e0601061202070203010203013c12170712080105040921051608040f060e030c010f26010504061409180c09090d030608010606 68
    0xc3c400440050b042030080c005410346080d07500d41030a50301c0a500450703060030007140284400c00c6601170321701c524a08260900c500c8180840d116a00c4030705101c0e140c2004102540b0340014905641151034113030300900299503030740c0c64064407202908907824250002414420160320903141000304020701802042d98940c01c5d180c4502450100c810b072805441811602c4000422201c0400c020241c4610442e042406096400d00250800e03005034003032130080382002400400669071554124480040005044410240d80c6003100c07035014908031407408000556540040c000c0b014094811503034040400300440e503c071401124010307002003030b494040e8032200d0040c50f2903004040e03170200340242c0d240c140c440c02c1e0041c28283c0b1120080107210310005040b0014000740c05c040c0500000b07440304d05101d03a5800c994202150707400c03200401c4645d40c03240200c01d0400042c02404100792101000700250190700301011082e858034200494036003c680b52020006540006018240403500b81d41c47c1c450003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 562067859 1250 562066609 562066651
    0x60804080a110304090e01140901020a270b03012301021b09040204140c0a0306140603130510020f180a051302130b0f070b0c03040803012615090114 65
    0x21140740c0c900801c149003c24030002c04c010000e445490b0320044d180b00003240075a0101021186101d016004901c0e9900400c680000c294100c0a1100b010090740c80271001c0001072200c4490108081d046240801c0001000107059611300001c1c204600b0402c1ca40500b401404005a90b14070341c400510a0b203112100d03521140e071400942d11907003d4000341022907002003206003501d2510044481c199403000c00704186856a926200b401c0c084c240c6e4100b201103070200300300021080c1c00300a080c030240b80d614845a01c1048400e1003848140400f140d410b640b00d00c1031002e10f8420b90001c0840c0e009400c0d8109840e0880d2503c21710400880d540903045a42111003c0e02810196101d008561030315125a000051613240b48001000705044110100ba10f5501030314225114400103048280b10980c18828000130a801074205c03030440d002442d1000000381e2000c80e542c1c4001240b00c5419890050741e811554003989031407441d00c52040310008000d0400711581e15402940203461f0a004003140f45600302c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 562069109 1250 562067859 562067867
    0x2031e1603110f0601080706020c0312030f061c0c140402070b271207171c090c0510090e010b04080c1306170d1b030f030b1c08070b01060804080a 64
    0x40076040e50302551042c0f007140485510341082039010005540c0034580401042e41d05100c1c0000804089010b01081c8040100c040d915020282001000015050209080da0340724049041c0718000d400340b10240581c5820b020104007418031800d03034000420a02141c141c40c0c41d10072107a103c0e43c0480d810540e6210a032510f0050041e95080f4584207400c003030300c49a214400c000b544640b485083d440c59891082c0e00d842c5041d4200042c42c001e11001c1848180e0300c00d6043c54a0387d080406409001031a500f0a08011040a040d5405960886140e541c02c019581e40402e851054800b00000a0ba443c0da0301d080040091259102d03140c0c0341e403c080a2a041460300c11002c150240312002d001c40c107152540b1000c851641c041005d00f00660010f01e0862036560800c100c0c2050880107503030345480c0d15032031304c01605454100150b4420581d03038542c00c09140d91840e10380c040000c419410591540c20380e00c0e082c0c0d12a80100000d0b030705d41250900000d400380c411009148035581c045000e900340003800400392 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 562070359 1250 562069109 562069127
    0x51b010306180515010305060d170d0c0e0102120309030f13080d110c01080f010e10081c110606061b1510090509070807060e0103061502031e1603 64
    0x904064460310000745040c0c20001c040c542c948000700c0060a410007101c0c40d1001c148950015052604000800a01d86c2d5a4010b0812080d08201c0c0c3c1100e0000d9020801c0061050f84082040b41d89084866001150702c140320b0b184186082e001c680740904400040c03920350108481054207a0320800510b00c00c0e0510728098405500b0500324540c10039195425142880321503107513400064104000c840c5504000c002e0b8840300942820840d45c1401c110f060800000c00501801201ea10118081094454004000001881004103590300722580c400300b82c0b03200040c107150714001400c40d1001900b04c0c2000c695140076541c010006407620701c010400f01d80b2406d1682d5603c0072401140c5a00c8402c4a181003094882e804140c283c028a0707091610810032664041c0c01c140301540009018131404000088200948000f0b0420780e40901424004070081c14079500071200800b100c0c984400312030b4000018013280c903410b4440441002e21380c1e172581018010340c160505071100114450000c41e020700660307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 562071609 1250 562070359 562070413
    0xf03190e060a0e090c03010302030604021507051507170c0a0f0215010e061f0228242a0309080d150305070501030207020102030d0b0109080f030306100c05 68
    0x881403100d00248140d0011140d903404a1511408a1040e1422000195001d85901c3d107607410b6505503008256601ca00400090080010a0f408a105451002551040e0381e1040071501038807850895195000810f54440000c2481d0799021605240780451041c8150301d07034410181800c088910441d60407514034201c40c254050280103140040301c24101c0c601800b00211030303490900740813091180c0100703000d418080194820601a1a03a03078089110a081d50303040751400c52084060203401010741c5c5491005100302e24140f02c00d04a40c204a4240d0100143d0103c10405c1090000480d40400c0301c4420f0f000007411214021489113009501025000d40113001c03e6040280180c82c81007180c2c4007401c0e002c40445020340400c1040001c0041d100501002c2c81c1c05d5040010b82d50000c1d640b40518085e0402e116100d81c01885c4591180c2000c2000340040400c4680207202080410346036402174980502400b00b03410310084541c02030441000d0560301800803c0d0f40040c00c034031000c03c0c6540400c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 562072859 1250 562071609 562071617
    0x1021b040e0613020102070506070b0708060f030a0501050a06080d0504060f030b150c07061d060f0c1e060f0c1206040609060807050120070302130e2d0f0319 69
    0x8448080c5404010b864400c00c40040342d6903140186000180c80c09400e076010b64400c880804c211800135410245442c0c204c8030341c0c240307040c582d150350000030810401ca010454161003607007420f8051090541003035006144086042154075102c400103510f90342d01a403035101185082000300500d500c90ac0c6a01b035001d045e4500002c040c04024009001c54010b08a40c51142601044411070964240480c0c80101050704240702c408080482c1ca00150324011000e610421012038002860001c150898400400c25001d4803182c2e60707220107440b0340c0401c15a4800c01c610404c03001400340c0c2104803070540148c2d111406d240c1056000d20700700403a00320042c600707600640c4035140011842e0f864064000540f100c000980303407082c03c02c03000601545904140e00c040803000000102d4141021030040c041c2c1e6010b40710000d40030049010b16001e400b0320a60081c4610489518048504030404c0e90341410040942140c1e100c0e44892040d6903807007104100140b42c0e0010003611015440104014510304a1418 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 562074109 1250 562072859 562072871
    0x203010303080f10090923010501080c1504090203071716050304150b09070f12180204050603030403080c010609060b271903050d081f0b09062a06060102070501021b04 73
    0x5112419250904811a04c0c054940700c0d040544040880147d00700c64141d0080180b0744c03400400c2d59803401150a5907002d020391040c0841c1d001d0061040300d001e0001c1f10010742d80c90a11441c018200140d03010000258100c64011881000c007801440c0309600040d41c42c541140c0321515074203003800214082c071411903541c01c40c2d00010b4641c030808910a61103030325000ca02c006400405058425142c1d803901c2007c1c81c04204000700c0d0002c01e0041d4149805580002c2c00c2e07030f14400400d00d188150340001c3c00f200804981809038002c1508900309441a501c420301c0480c0d0385100c00b19050084e01a10031078003840f100e410048080d564004032030420002d00f0040560251260381c0110f00c015003040d503854005500720ba01058001300c13816040510500d4003250341d0040c9408020b014014062105e40c01d4001134520040e640391003e507000820702c42d2003200810b280c0754006030005007030101c65004d40910800102958004a084411640706030083c1094403601e500c0a1451401006500e03031055842d1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 562075359 1250 562074109 562074119
    0x50d0918020d0e0604050a11150d020c0f060c09040c0504061b0303200909010e060d12030603060c1d0405060a090902150a080702070933051c0b0105040203010303080f10 74
    0xc411340c000c0d80140c024060351542403e182640b40c0480040c503004440c15031040e410612440c003140d062646001006840349144000c590030000560b0184c02e01d40704140c20b1180048001d00140703035a00c4c080f1402c210242e40d0140644d0386021310b2082a0106140c00c9444c101080424543e60b2000d100389800030340e4503500c000e12803418905a00d02d6003030301ca0100e1120701d181480c500341405030810356001005071a01c03200290040c1c032461401440302c60400b0001462a01940082014643c09a0240324100e5603400050600480c03480300e000c0c01c52120904440c07804c01d48207060140c04058400092035003456400c60141100500c200c0e0480141d10500c4010316001300034106100196031103809908001400a00e00f00464004218443c81c1c00100800340c892401844056107588625031700343d410002401003009216808541c211160b125041e84a0006804015410740700b4220807409907280c0e0144000c0340024003001300400e0a80001c0f900b0741d038900c3c2c0f406a201c644a10f01140c1240c0314 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 562076609 1250 562075359 562075363
    0x20307050706050903070807020d050c0d080a02060709180b01050f040b070b0906070e0405040f0c06020c030f010e0a0f020a09150302120c010917030f030112050d0918020d0e 76
    0x44981400050020660400b00200c90203400d0f00320600c1002503051800c00d0721017043e21305c0380c030000038441c4034081c2030402000b00612603a400c0050040450403c00700713504101c1c0a030f51002c2c100c00011f000f5040080d60580c05030040c01c0aa46044480b0340000040050420090804914042c1804401d010009490380c034000108003909500c4d100b10f03190005807800300f407000406070444480350040400c200e503050b13001d0181d42c43c0003c01c460200e15500c4509107045001030001d80a041c42d40300d002c5c08210590001280704820405030200d84001c614524268201c4a100f4002d85880e0022040348022401c50920046140c4c00180343c0c2004541c0d640d41c02c8122000030f000c0300a280990351041040d1703d0880100344485600388041e012491100740000e000024074000c08032100c0c4142011014bc1c282001a07846809813202030603134a5840302c50990450410708406c960b130b44900340e200d030803944c03140c81490121481d60801c0d104020b5600b4200700a5007001a00103409544e40c5804600d950701 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 562077859 1250 562076609 562076611
    0x501050d0b030604080d111c020d14091606020a03050304080c010e0f010606020115031e030e0d0506061002071d13170a090506040503030406360608011a090111010905010203 76
    0x5c540d0480d40c0d01e41c1c1c402d10380c009940c0f4040302c2c001041810302c4a8001960040c0c807200304100d030f52130016954406d10100500804032405010b0410110000300300f03500e08000303892103043d40388032603920282e65541001c80e681c0f010003078010f000400038404500002c0d01c1c840681002040007001148910001c1c1c001450326a2500c2d0442c2184c2d152070301080219020f100318909800a004003a91813821500c44c51010000001100b0102044943e61010305104221020304004010119020a0303014103140d07940c0c2d00c06075095031241c440c54601082c0c2600028104044030b51805900a00c11881d215840308050010140901c416003800341e0340005038011110502040c00a00c46900e51030b52020003811030741c50b0f40195009800c204400c1c17250390b40c008281c9003200c8080ca405001200300382941c98002148088902c00c4480030b035009403100d41d17140340c9034042c2d031400d5680349035680c1e0300d141c10f4940030b8409054102d215070401459009505c110080d2060305030344000403c443d00c5c0ea58a0303a089900c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 562079109 1250 562077859 562077863
    0x1203020d09060201020a09030206160b0a2304030f08091005010e010e0a060e010504020a11100c080a0504120807021f0e0c0607080f0702121f0e0d090501050d0b030604 73
    0x100d5034824620741001c818400351100f03100840c1070a444410144c440856808040d01c102c50218a0414001d04c90404902680d802034003400326041024004000c0d220030025060995291004092101c0c614802c0610507034155407000c4150300030281c00d4603403c60107000d0000ba405841c2140c948140f483c002c1a00070201c111a9442540c5031103101c0e10410f101400b014400c0d41407450800c0a452880c205c5410342c2c0c030441e00140e03500b03107d80090710020845205016503008408a0701d100c80481d9000341642c00943d1500744030f650b940303c9a2400c44204960003042d110050710060303451846035680c07503071081c02d5004480a1000800b40c00c184a680d141a6008690711884440ca0860003070150000c100310075604141851443c0d6292031580c014903890084140c00801e50100b59511000440b00900c00714041e10b0285c840e9003010350400a03540380b10244581000340c80040c03102c7c001707941d000541050707950040b000c0c00c003030046441c3e9004005400c6600d03103030400ca171b0180d42c050040501883c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 562080359 1250 562079109 562079113
    0x1713140d0807030b06071205030603010b1905101b0b06010302090d050a120c0b0118021209030304021503010302282303060f0112030e0604090606051815070f020406120302 75
    0x49442c54004040d500f08280143c000c0c50140481300c0000c0a81da2840c1c2c101545040c07040c0c032691040d000c640101000a24950b1104041c00d122034203000040b410385c03c1e604203462030414100792034010340b00c920745141c100e0700c48948001ea10011400c4040410b8000700145809442c0103000c2d4001481818032403c15240c0380c01c5044114100179558072140d8a15105042000c4001800c2d115603d00c50b4051045110100f4501e100b840d0300ea600e80d049030420b85603103000079a00d08020b1281079403500116812802111000c0b0304030011030382c0c0703010389040f81c0e8002d12070289901c281024100e00501c20908201e820101d190100382290581d428203c288800400e58200841c0d4001305403400d1406003401404580c21401400b1103078107074081c03018080d05400c201081d010300c5404a0800d103d0365100005240c6000d00104515500600403d03806482a405c00600d503600030403c2505070808404c001c1610080140c100014403102d1000b801e98001040042c0709903517041c400390100600e8108800503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 562081609 1250 562080359 562080361
    0x50a090605040605071227080405090c040608090c06091e151c06031e0c0801021306021e0714030f030c0a0203070f03020907030f1506020304151713140d08 68
    0x415071102082480e117445500500c844446003119803080840c440902c1408a40c1c40001f1090044d0481200c0040c10050402c05a078540343e841104980c1241c0510130024004901007401e00900042c802480700000f4407071482c00030090300304000058a0400440c800c20000b851b14150342d21380c4520721102040c03460039550740345c2420540000b00e46a441d9000d10324600171050001c2141d510001420900d4070340705a0340704c9690304200540c0700d0241d21012aa40c00096200c4201c5003160250f01215035540071111280002c1d40b003c200b880c900021180c050b4015902084070741500000c00500240280660700c02524014040703055034854803c080b203581c441402a401c5041c1000124020a403400c40704600c9400c56001070b5200c40e01900f101d0406465000e40c04014041d507201403410940b901e0400c40480d510301e0082c0d00c03600305201d680700c19504c041d4000d47c4540036100240d15244412081c07803e5640d1802004100750b406613080d9001024002c5a03494440c08000e100b1001041d038550380c4039 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 562082859 1250 562081609 562081621
    0xa120f05150405090307030302030402031002191b051c03060315051e01150509120a2a0b04091515090f0f1211040b10120f020a0c06050a090605040605 66
    0x180079428041c1d80e000e14548410403a1030000030007903503040d5905203409a030369221400040c0c1342001c40e9040b500f459100043c500c03146100a5406000c803445500c480c4200200040002410441d801c0003600c1500120719182d070b0700340701d402c1c51480b1015509000900545948445000b00406016661001d5550090041051410301c08001c0e0010401c0511095030401030042d4103c003812100c7c005002020644a03c1942c0d0021002100c038000c80484500c03004d242091501d0010002080c84041464501c1d0342c4441e4842c0128012385000d00030f0307140307010726003812880144400c031030034407081840880203e8528588880005440281d0b591801c0f80c9080c010510780402440e40286085052004d042001c1111540c003d65203d410903010700081d829240440c1c081d240e03011035180d00c03401c2d14001924282d00718140c0b1011001d0568200407611810607040c1c12441041c0190010544a0008400150040c0c0095038090300c1c0d520b000c2000307042540c41c00c09946054a049458585400070040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 562084109 1250 562082859 562082881
    0x30c011d0601140d0314090603040f02090a020c0a08070204140c0d060b0702010903030806040f0f09060b090702060c0f0903070f060e03210c030906071b1a030c0a120f05 74
    0x1001d4a1683d154140c080c015000003201e003148824001c003030140f899030b44000102040e007542e03031035100504603070b03a245428507240d000742c480b181c4d00328842c03240440440d0300c0041d039100303130342c4942d40302c10040c00c031003146407500724040c0c220b404100c0e4820f850340c410703040141222000d2030044084882081d168250fa11286059980681018000e4a0180b2201d80035030382c8a10507900b12034040c20a40344c13644404010801501914401e41446428a8058441c1181903809554180d006982c200a41d524160821414030019180100180d001e0310100301d00d5040e0900a00480594143d0385140c5901900800c0c1032034010b038000000020078610801043c0d411060082c81414101e002d800c2140f031055514103141032404100152103001b003040c1e0082d00c0200210f03520017100900ca25103e040320b14190940d12880725401403180881d940015800150017220000030211005403401c0d80d0340c9900d05481500910b950b081080084a45018010b58a208055518403000700c046000d1a000c0c402007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 562085359 1250 562084109 562084111
    0x7121203020c10180512031014090f0709030b100509180a030e03010608010504260c03071e1e2006070b090a02090c090103050606070f0201030e030c011d06 68
    0x50600d4010045803020040100702c800e07001d0703599100054011a001c0c10202c520000403001807291040c1e0b8941990007840f00065886070060f214003812240d1642040c0e5001040c0d49a11500311540d00b0100716011188280150b001031189064440340b580e076210000128800d03182103080c1504001c0510003814a1555241e01c401b541c0340703136007102c0e0b4410140b41e5544210000542001a624050041c9a90a401c054028100d4000a001c103091070b0801011100b40d40d0800103074040381289074950150603c1c250703900140401c0242d81814896150040c00081110101c0701c2c28241c114000005000c51190034040507203000e62070b070300e40c1c200c1c80d017629450750346c80a1240801207100245019901e240c1103600040c0d20440e01c40b032030784411406070b24008405070000e50106100c001c200303800b014580681420791090b0303400c0c8074984030001401001d108240b400f501c0f021a8001c1500907502a0b00280301010328071003120b00d021034851405007101c88071040caa05c201c1c038903050018486810420a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 562086609 1250 562085359 562085393
    0x12090f0103050114101e02030408010b0102010c021011070b0708040b09120706021b060408130f060518012a20010807141314090a090c05061b0712 64
    0xb0007455060031002c0c1d062007404149103208407240c24001d60320700c0c801c040c4110032402c50b182d024551103420401940f00c0d00a806000020742c40e01030640c1042d0303c140505040c00c4415009011000f40000104000c3e0000e101741030901c0d042080407100103468450400c3c800d1040395200390603410035240000002c0c13405041e1021503807042c50b094845000c4e078012a80926130080c401130303803690300500030a0850401403504034140110010042408007101c0203011019411034801d211545481540003401218041c480004005101502c43d031601c490220410600504100703914440b10099403520321188212610405070401c0140c003000b401d00c4058025001311100e0384188032182c00002c20268000740340743e003005007003206111010030400850b5543c1c024440c031140b003951500c0078403c0f001d20300929203020760000400100e0010140c885e00140c10341c851000c0c4401d03440d1008021054110224100c0c2e68a0080d00c00a1089410408000241406d0090352000744241c10000181c000704406 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 562087859 1250 562086609 562086611
    0x170c3a02090a05060108060405040804060c0c030605010609080601060311071211060a06090c020303090a0f020a03120302180607050c060d0b060417010c0206090601030609150f05090118020f1005070512090f0103 92
    0x14040011480e904cc2c40070f40d4240d1610009503840c03410902207450300d80d40003131700035460301c8000703d485136200402c101665082c0044400700d9aa8a008500f240c11000c0309418440007031001800003441841c01911844080c82d02d00ea0051359806640d04040c0140c4080407001d64901c02040041035600441441c0640ca0005e9400c44c50a08285a02c0350a1540000e084412200700703901190b684002d0100a150460a421500451848090000d502c41c4040701d44034012444980224901042150910781c5d000b000303170000d9448502845002e81200302d01c0200661185400d4580c4d444200281c40100800c4200c068442960003100d0f08544002030301508640180c03040007002003001030b045045961085c00000d5004150412084010f2556040d0480f142804140040b4003a00d404c141e003c2c0718914000c114202031184006d406844850009401210300d15800142e45485000d88010201c1c0741007192400780039039242810401c5601110603003480c042020710706401d06210f65030407000c003824 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 562089109 1250 562087859 562087861
    0xb011a37021b0603180d02060403090f060c17090d060b041125050a021807030b01110d051b03160606050603010e04060c1206170c3a02090a05060108060405 68
    0x303100c80d0752100460a806800000302141817401000c2445050303a840b5415241140035041d8025101e20003a5800d400243c40c076203001c0b40f03007205600340c10304881940c0c451200c5a0b001c0c1d0713a1310451140001450300419418080800180c44084194002a200b0b6800081030000c0c4410071017120b419030100202e0340c10521440c0c50b00030031048418914049501b500c60214030b2890801d141587c0010003d40101d00c1c051041c820f0002c0c034001c940900001d440c14405100400011500b2119815104409520081c5985c203150300800040411003c440c81400b14240c031056494510b90004d4a00b10011520103440d07001e1180c140300e580040c1104460807071840d458000d240440c060040c3c00039105580e00c18403500c900f805000700192134000040148550b685c1c0712030140f50b101440c004000c603070140141030b140074038214031090340c54400440d4030340030040d0180b06900000504030f100d40041416441e6680503a84d0340d80d40600c105902480414103103456000107100300304c0034044c24003490401d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 562090359 1250 562089109 562089133
    0x509010801050610050c0a0c030303050103060c031103070e120d080405100501051005210103050303070f031404170d0f0b0109080f070b0d060f0e04061104030b011a3702 74
    0x102d502e0144644c81c60a540c669041c0541c0600303040c1822002405442652000410160180c0280341201c0c025117040003500322100341641954a2401b10054210341000020140340c090722001c41044005810033311500c801194180c0350480315807081010407043d6040104010041142c6550000b4401d010b0160b545400c0110f02540c02807041c0c2e00c103025020501c4031841c200c6140c40b5448480421141c803495030740c1e0078040c4d101c0e40160350900024205c0744000e0921400390207200c4c0c0d441102c000480d655035446d21070840c185031144426038030700400c0119420000b124028069042c15103100020001106000900000000e1303001202d65001030b0075024a01201162502c01c4a840b042c2595544030702001e441c00808440d0010001c0c0c00c180b85020a01c2c00100001c41e1280b44581d034100401d0003203000f084450b00a0b03103c01404146218014441c1150141072100707100c034643c10303036400c0010040803101800c00344403203844003d140c000d1100f089a01190050351104007030000d044100092 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 562091609 1250 562090359 562090369
    0xc0f09100627090212130305091e030a030309020906040b0f040c030b0d05070e01050a08030a200a0b01031109060d0f03020c090703150e011802130e010803030a050c030f061002012405090108010506 86
    0x10303000031442b403484200240c0d070102c8400b00170089030b0790090030303a40b00840d00d01c0c0150050001c0c4034240d0180f611540001e00700c0c1480d125020542c4002041c40410844101c00c001c040d00c00d1040c6441050b40342e01c402c17480c0b80c41e18004d40035041e12034070190000c1402c11651496030003050340907901c500c1581034100088e60000c0112248c9418034540704840c5804158012903180e01d418181520780f0603040020140604200324070706a0b4851045009448601020010f15800c142e0b800d5a0003403108101d900014103a040705555039200b401036402d4010344e60b0009103540012140c80e80481d03141e240c407458040c02c90702220050428600204502c0d4108040110304d140c1ea2220703039a250f40d002400e50344030380705940148001c0c018880308146968481029a44070341081d47c0b9801c109041c0303400300d42c46403459030503288104e40000400406903200b10401000203010703804c070000d655a41c01c0c41420000010303184104242c100c039816807502d00d01428810070a1050380104400d900d002d0520404c1d50321 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 562092859 1250 562091609 562091617
    0xb040312030902130b0a0503060907090f0516080a11030109050a0c0f0203250c03050f0d020114130602130b043f05120c0c0f09100627090212130305 65
    0x60a0000500003005c5000b0400c400d940d90082641131041404201030400c000070034405443d0400400c0c8580c030b4202c87c040c01500c1c1e00b503d5800111030000c3c40f00107110b105511840d40690308010105980d0180340302030740f440c0d0080e0050341e89941c8a070104503110617a40642542c0010514041811442c0301c01c009440f07008801d044400810fa040c9907419000b030041202070620341082d00c60010690f00d290a5076540c507901c860243c217016480641c80a1401172180d2440c3c42003080700410903584410f500034200121004c1100d1099090000355880f240d02c600340d82c05047d8042090382d1741e50810108002001000f511140e01507040c44140da80b4029054900030100403400003004035500074a85142441401185060591804038040031200340018113004152400d0341c680c405501c0345014083c8400c8100c0e61580510360321881000030901c242000c04848021000114204942c554008022102c1d42c0c0500034140d004a403140e46680d0342a5915041801040d440c10307c070b20b1941c0c015106000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 562094109 1250 562092859 562092889
    0x301090207030e0306073516080c07030903170d0c03050103050606150708030c1603080f07140a14090a12110a0812030901060e0403020609060108060615070204020d05010b040312030902 81
    0x25040080c0d991242d40c006e42d203424a82c034088294080c1c5000d40d01c064071108880d08c10000122101d01007a00a6441c204a81c851601503458081d05820340d10f03081c803a1040505400003000d01082039090001c0117205104401400d5a000300e00d03940b450408919104001d081103128050609100e1142c0c45c0c9401160300e03544d0305c00304840e165603031210100114080d410580c180c1c003070b581403008100f540c0100c1c2280b0406042202040544440400300c405244050085034951410001c41405c2c90041003200c3c2001003080e220b625000f00c1a000c40c6204c180d40c1d100b0384480e5450901c2c00200458030310444191f860664441c0122880e0440e071569641c1220070030704080d8000804079020721070a40040c03018102d6801c6000440c1010f241c025500c1c401100c004803d80601000450688004155140100b0006001218008815000b00c941d42c0c007540c0e0483c0c1c456820440320f01022014010760303008040b0b142c1015200d5103581041c00949908400403801c140c48c00c2201c00050b6656460090340074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 562095359 1250 562094109 562094147
    0x20a030c050709020f030a060e0f0f10090c03020d06050f06121803030414010c03201303141c030c02070909150609020903010b090126030f0301090207030e030607 71
    0x10031810401c0c00c004141d00554202c6000203002072641030460000c5000f101500002c0010607a11044180740140507540860b0b0720141802080000d50841081500440f003601c801c02d5a031b50714000001111905a40783c40030075008a245086640213104001c000d1030142c078414401613800d07000034000c0c8178280848190130103400104030380c0200340c5070b02c642205044080b42c0d5a4105070a00c2401b100c006e481c9002c02d0b43c00c0c000d47c0b5074618440d0180213180d007400742014a940224144000c00c50b0460301722030442c1d81c42084000041480c01c1d0607494440c248101410781d4588035410402c556402c0b08100d410705052407020b03c24039900045050481d031001c0030025001080d4944845610000713444039001e94100300d004205a0381a82c0185020038040b0020000c081110041c804594000d02c14034081100c0505c8a100300da0300748001c6040d1200900a4a207007425000c2c1d80c00c101d400a0700b0180c821a804101242015004599624128002c800410a0703151044000b058800b0801e100502c0d6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 562096609 1250 562095359 562095377
    0x120503030a18060e072315210103060c090e090303010e060d02030319080105490516091b0f050c03180a0504020327070302060c06160e01020a03 63
    0xd0182c04031185005074008402c0c0304200c0c1d0f989009035202814000d49064240310242c900310300000320702507400b03040f01401800b06200102d0311089180c00000f80380b0300c20200080344001c0c800903098014042c0d44601400a85030402c030720010840200c0390030524402202e242480202c040000c16241145c03603040002d491951031502082040400b420700940511000c150003200840320441818881d06035a40c02e0010b0fa61002000506001e41a030b110051a0014020084090103010780b40d00ca80c4c2545080141010b24607802008031140a0684064101022171043c1040c02048100107054042c801c2c452160408510200342411041c0b007414444202e010740001405503040c1d030300320356540c41929101e101030710a482c450b08101000c5849a4071101d008601481c0520950340200842c59640107000404011510b00c1d800a441011080c07146080c0040141e440b00e0080c004000103202600207410480e00011000000d02c3e207400c140841c1006c1c880280e40c0c0020300c0402a609840c00041c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 562097859 1250 562096609 562096631
    0xc0403060b1908010c031b0c021e0607050a050f061b070f20040f020406050306010c14011e0b03070b0a03150f03050703020a1512020903030d15050307120503030a 71
    0x10310014890142e60240307440a000800d41810b44c0203c3d0403462686060184944643c09819a80031014140d00800c0c0c032088120b000d4245401240da08030389044441e07001e5411400043c00d940c00020040700c8951140720883c00300318050043d078400c1000c81c001071038541071988840841c9205040c0310900c03000d010402905114065a0a0840c03135000340408800405c00c5410101840c0d002141038025400c0c41a00704c2d800c1c220788201c40c11200340b5a0342030f0660b101e5000468079494646801d48480c0c00412002152040c01e00c50703240440d00040c01c00b40300d54a00030100f0103460000d1407081c825000b4000401003c10316000300d4185201602c1c000030081400c4851034500182d541117003e028400d1180401000300004400c0141e074001c80d00304003025a5000303e00d54640040901c42e00049403e29105000c400940140c110464018207032410264600400703011110020641206a0324440e410001d40c03c1c24031260010703000007515030481b02da95403240c980e06d01c009401509080e0340c414407040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 562099109 1250 562097859 562097869
    0xa0804030c0b1204020438270703180803090307060506040902090402011202040915090e070b190c061e270809040e030a08010608071b0b04110d08041d0c0403060b 71
    0x20403c41038014121002002e07040c200b1541f082c42200300e005c0d0b1248000c49540324a900380204100f400c1882080865441820032405000c2282ca0507507102c4182a140b40042d03407080182d442101000025030b2a218282000426290050b1541d4007982ca841c0349140940c4907a41d0b4170354070940a0a06104480c0c080a00074024822079002607807240c071300440c0514022500c05001c0484800c000b05201400d81c10400300e80714403080c841ca180ca2042000030004040710800002d85418007814107012261403911180b054402500401c100000f56189003d100d4196104000124141031000d6421911420303180030359243c4220082c14900000c252004250340701d41040840f2100d2405490702c0f07200c6410043c10520081c0592004903110400285103180f1440402c004c2013846a50301c00351101030b8403107840b141c60140065541803424042459242c4404c8060002c40307102e18042030b40c0b14908040c1400e0741400050340300085d01c3c140c0a000780040007a095401340c94114400103038a6200b040054 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 562100359 1250 562099109 562099151
    0xc03060b092b03030911090603150c0d050708042102031605010b180708010e070804080c010b09090a0b060405010623040909060e010b01020c061c020c0a0804030c0b12040204 76
    0x2c0310056400704140100341e4541c101074806841a08821072030f80820f010064900c2d42142c502c2d070594000308014808140c0c40d40c070186c103d12030b10b940d2850440190328203025a5400c03100c40c1c02246d031003802d100030000896100c203440f0030404015a03540c0f0210000946a110300d102428051140581050901c0421350000c1d45c40840145000110b8014000c020075802080382e416009c40da045000041e900b1981040d40e00c60b04082c0d0f075a001d1940c0d150384e8444160040c03c068042c2d5944c90026803610b4031a00c503443e00079103a00c3e00030450898289401409003800512242c00b1310705084c010081142c02c14400c65122441d094000c10311850640c52400c1406254800e9025a00307103000f00080c01079550000400100310002801140d01d01d000580c2d486452400040c0c0000040100818002001d070500d100030f454410050f1600d0003401ea26407401c2c05118050f80c80403000507041003040300381d8010303800501d620880c80703003000c200f404440800840208041e00880c0c4480d204111030000d11008 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 562101609 1250 562100359 562100419
    0x801020a0806010801080a12110c0a03081b1516050c0604060902040f0b09041515090515030d020c0105030408090d050c010e060f0306041821030c03060b09 68
    0x840d2103003451035008145080a60307a00340854119000070031000c001052006101da049110a103810000300803c03138890514001c42c4140740200201700e01d495035500500350003103000c0c0d45005e13200c0c07032012007040b154442d18003031052643c890215009402c0aa00002d5804038418060000d0024000020345851088900440e030b2400380e0b8081104000c1158400441c01d8020b07102008013a40d07582d0010104ea00200b0415400500900060001900480202804084588003040c0003000c40d21815960703520b9008940e03000d40300d20800440780e01c07400c000700c980742e0700320004c2045500c3c0c602d0194070380f0a2551424100003002000405011314801150b10404000e041c542c0c00f904181001912a003413121128006500003283c5032940c07a05400781e4502e180042c600b10b03e941c8940c001c100081903e034220500b80085094808085004440039610958901d13060325004a0030003001003c503164000d02c02c0030308d80740504c14443d1200007c1900c0f0f0703e00c4140d8240c2013400900d5032402c042c0502c5901 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 562102859 1250 562101609 562101611
    0x150609170109080c24010506030f06030327090f0402063115020106080705010e09060d080a05120f040c0311190923010806070c03030e0a12230d09020a0801 68
    0x70b8640d03c8200140100d100c43c45c8503a0306194807520b4804489440080c4115031b400481400440d05503d500e8035001c0d00071500808a030310700030f1100d00c0b03500104600b1030010300b40560030f400c00c0820b0400465aa503c0810580c0c09540b518059000509038024113404031070103503402c2407000820b0000102040035031b0b1440070700941d80342e603030440300c20459100507a0801542481070001e000000010400d081e034005031100181024094188140654020700756032340049c0035059103000c40e110000424440c60789a4070103649110041445440c12000742c4481c800c410348108003c04200301d50700207000d0300c0d072060328550708c0c40e0786500003447e010300e801380003210000ba014001003119059102401c0b403030b4020060800d00b466032960415a40c004d104100b40c1e60401400645035600c00c1c103280800034841d09002400c01c42c00e0544501d895484c040032104440c04c3c8030054803158002d0f00c9006254108801a1a050303445000c4107210302a40d42e800c0039054480c07521200310b594410385035014144840c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 562104109 1250 562102859 562102867
    0x18090a170a0f0f08060103020d0f020301032a03030e010507030e0a0b03090d0306030206040303050928061209030903020108060102070308030c031032010309050d0e0415060917010908 80
    0x154603403280d44040300e81800309403600d10a0b80d000d030080e1071801ca1000141c59040b01d60b03540800540180d0300064408400e140d41d0400384d1400300a83c40070f940610b01841d100d0100e00d0000e481c100c42004c0c82e4180700444044100108000b0740e00c0804036201840a1800b00d8441081c3d1800780d0350480d0708991a588003501c400085100390390303800550320481080f01103420f489001c06081d0101d5000e40006500300b44200000e20103c2d0054000f4890100060581c80c09402505410f8000b400229162041c0b0603048400704030060344181e4694600c80584420411000c8594014010364880c1c48001d0600c82c1c8000000c100c1e07802881406d00541e001009285e403032900c040304000c198011141101c0c0200208000b1480d41114200c10020000c101c21400b00b00001e6484210380c001c00e410740b14105611100c5540005100740001c1c5082207140d110ba1004000000802c82036403105101e5042c1c081c0328440800040361700510020407a0011002134050780180b880781405003d076030748090300301c0200003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 562105359 1250 562104109 562104143
    0x120f0f01060b120a020717031e060d0c121a15030c040507120504210203031f03030918090c080a26090f06130e070f03050f06041d0706022103010518090a 67
    0x40c0d450a0700107006602d4007127981d40c0e4010084046d15a03c1c01400c1078116500a001924640000e82c010501441c415520106498280340100804641541540e01e03400080c4446040400c035509001c101168140308030f1030400e1005105101e03e00601a4140d1074001207001c1c0800005010184401d44501741c0140350f003890007947c0ea90042d141aa4503074203a800c1100d8a8010144407800d5a9241e514000118941444102034880001440d40015a6a40000300190030038201c0c1e070003054648007904210b50581400104100d1485192030450441c6110300041c5000c0422504044411601100c13003980340d07000728186008440e0031441080c150000804c644003006442e0380300310300580e1001340c940036a20040b400e451054950382d40030002c41010a06c03618064000c030300c5070300034010300c8081100040c01c030516203201030b44203201507084174081c032410102111100e842d820001e5034407495540b400e070204082c89419001a07111407120801709203550011311008031040c0c1c104180d0141e20381d0702 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 562106609 1250 562105359 562105381
    0x13020a090204170708060103030e090a0e030712020d09061e020106050904060615050901021e03130603023103020f061902060f090c030615120f0f01060b120a02071703 73
    0x107440f030315451048150009440b840001e0283c140c9500d41d036100884c120030000d00440714000741a100c103003601c0301d004000b87c2104001a0211a00540e00303c0390482e41c64001030704284001410400704140b0f40c4081c0000340d01301403a40c010700404820020b441602100c124010a0f09400043d44020460700b400306210b0f00350004030075038501070421500300002740b805451074402c60040030b0140c0c001904a0961070b6628100c100800c42c00c0c010303249008825503172540b2190301c503044040480d42c0462040010310038a000d61400c109504d59201005400700c1c0740c0d052115141c80b000780700d244501403c291076140d0308140c1c0e90f4a00140c0144031000485200039441d503400f01e4001480218180000e808481c00292403840b03010090301030101c684401d4812070462000102c41c64200b0104690490323a6038003041007982440d50000501220914601380780c1c00d456480c1c1c8240b006600074001820785003090b40382280c010540242c01a0b44000918009410081c05251603c0e8480e0100030000b2000359 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 562107859 1250 562106609 562106639
    0xc0909191103011b14070602040b0706050a0509070b040b03060109120302070302030c04050613050a020f13030b010b070302060c030403020a14060714040f0b1b0f03070b070905060313020a090204 85
    0x1084000740083d5158003107403101c451441440b80000f6417903943c08081c00410741c1c02000c14502070701002d49043e4943c01011034075440480d08695099980c000c1140032100c0e4442c5e01d405c004513101600415161007880300a5000324001d50020034070000218015a01038400340b00103150040f803c0ba400102070a000c0e4950600340b00603806405a0700c170001d280e140900c5500d1140000900000000100005d410000c1c83c00400c0360407050b60130082c0682c0003180401508858942300c0860355624107629102c0b0f500c2e041a070280c0c00c07401061105c940025004107149030300c140058100b9480e82d6880c2012464140c0410001c1c01c562880c4680044901b40400c1c420710074580c54403414020071013100110b200740b0841c480c550300c078480c105090001100b583c0085c06000c08071080e0181510120425904010700b80d00102240d034030004482080100305c21225a006a0340d08085d03000c00d1800000c00c0440c880289040d90b1070412680e0402199101e403150750107400c40000071501c0340d885503036880c8010a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 562109109 1250 562107859 562107893
    0x31b0c0907180b0f0d0504020409020a08010603050c120304050d050313090c020105090703032f1204051801030b0c0304080c06090601080708060618090a08280807020c090919 76
    0x2072000402c090782d540c404c9031001250400305600d0090748030b0206000b1705001d841280e03c5901c44d8200c2d80941e50700c0782043e026008900c00060040d29500e00a46130852101000b405480c40346c14072100f60002006440807100c1c259461009581c051070310b2400c5228030782d012079800b00ea0040120301c002c4580d10a840c103404940080003251141c0d03000507a01d101500c0024001400c101c5140c1581e03448041c03042c8421800c550702c00080e0800d080301420060f5440d1421450400883c0400c07040c9000698240004054005500316505580f940b1420742001800510082d03000000315041280c0282213440e1110706206448990626800310b540300e450078450300600d0b1140e82e0012a140901140c0c460141c040200095040e8402d0205051301100040c180040b0740030740002d90380803451520042c0302c0f0907000511810011000d9072010140d02c4421150000c12031035a0400a40c00d070000790024101c802100c0380c108503561101407a00e403030f002045401c10060318014400820000d034012081d030074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 562110359 1250 562109109 562109147
    0x31209030806040e0a052d01021603090e0f0a020a0e0607050601081e1c0918050105131e11040911031b030712090c0306021605010e0c03031b0c0907 65
    0x1390144800e982e5030303851800003900c250085000c041d240701115084104513402e25111401ea110682c56050898015075040d0420f01442c1c08180205a031085448000e0f010580c0f0140386030416915400384d8910080c01c242040c0e600290010345a4003c1c0481d0701c0752000141220b9540c21245040c03030700c0302001c0c843c41200d40701c7c06000c0341c0340c2c9040b282003070740c01405030f002062910060700c6109060a01c10021130188140e6440c0415110f150b80c404030911441048041000e514000034000301c6421b5038200e4407031a1170700795007030385c3c2c82040e40150103030703509c04080070543c0e5141d000041c00510859002c5c0c0400c52034440e561a041d1000c8014500c29881d403103003102065960030842009110032180500001e1410200035080c0d0541d91044400a000c2d0402c1d6403401e8883d510740d0201c0c1e003c0440c545030207825a02620400909009200c3da880b0310b00060001c0900c4080401d90760300134100c1000c054010418070090b080d000700316088408100402c1040d080c1000a00038210040e070300c464008907 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 562111609 1250 562110359 562110371
    0x7060e060a0c020c041d0f1c0e01050a050d150f1a0c07030b0703020d110702100e0105030c0705010b030303070c0b0a05130605070201020c341a030403120903080604 72
    0x903020720321900e00342c01542d0700030706801501c02003040018a100d1400f0300d00ca61200c0c01508a500e820003007203030b0a240341e10060100c2d0741000c6030790782818070345014641040034529900595907030110650341c08501604042c0c0c2c580014260328009031200f0340c00e41200d2403001500180c0c1c2d01d040744403076040342c2c4010807440350242c1c5820004003612503400100c0196005090820010340110781c03d030380c000741c0ca1a00505001502c02c4810985040c20f0040144090101c2c0c1349044d171422258036040c2100340e0030640c2401c164100040c166000080820940643c04691581400401e4004401640005007a00e41e070b845d162402500410740380c5019166209140c0000340b840c681440790f01d002d50700d00107091800c00000c1d41c079400903000003845c400031550203100940d51702d6010001d007090120031080207042c13800c103600c042589600c10b281c0f20011141c0c43d13004000008400c0804c4001c5006080c40700d41d2551907080139a40c003903801410104e45480d00b02140d06140c2e10143ca1409407070115414404 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 562112859 1250 562111609 562111621
    0x1c030605030303010b0306060d0504110a051017070309050616030e060c030f04031710180b0a12050102040803030703020304050d0f1e031107030c060506151e0f07060e06 74
    0x88420501549401d40e10410062040041e8a4040c40e80181d0003404280b9040341c3c88000c0c002d890065604450454802100304036070703d40028408040c0a040c0e40b507100711010300380b004000d40042704440044941c4a03000c00d9400c2e06c01e400c000c510035080340032240103041080f5240c400910080740000002d1822440741021000461405c3c080c0380241c4042c1d0070764032441000041400098011030078452511000c08070011152a2148908180074420030305030301d00301010000300f41c50310040d004145454032128460b40c2e505141800d0300d18000300100303984000d2130701e0350080c4920380040d110f80c80084104201f440d07050700254030991140e4141c9410600c5000141c41d10f8001000680106070401070750000c040d00c0c0516507002d00320340d1402240d4002043e041c41e10603402010150005103900c00d1001c00c0c050203028040c1c0104060341c602d40c0144031007203d004030740250740324400c00351030140751480200c0d40402994100380e07120314640d40c0e03200c061522400410082c840c490703040c0102800100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 562114109 1250 562112859 562112861
    0x110f011a15090d110f040504150e0105100308070c0902040e090f0a0803012312030c0f0c060a0f03110d090b060f0f10091805040302070f0b0417030d0c021c03 69
    0x1103900b0018103002c8401100e5602c590301000d540c40020340010116070500c41079600c0f4082c00c3c1c007a50040c2c2c181e042030210914100c00b512072585008095a050230203202e0030320740440002d42101e410403c1192644428644190140e05503406608100d00209003c03c05004210b920303030040d01d0403402c44013450303102151203450304030009c000380889200b4030041105941b031403012400394100e40c5258201c0000c840000d00f03040b274039140f0407400d64008102d40c1c01c161401c2040088043c10b0f0401003208a04201c0014194071600410004012841c0c5508010a0081d00003280e0902c03140c014603281e5001881b80401040b00080954140b0880fa020506074105800101d85180e4043d1200701035100a0084c08a9500c040311020708000017000009000c002c0c000628082c01e0b11248007241038201801c00074600030542c1c0012500c14900d1000308050384690040303034112500c01c205031100d0340c01d1091541c1140903110f081607400b0308000a00c1180c1c7d82c0070810740c0000c3c1103140380b0305503e129100c0482c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 562115359 1250 562114109 562114117
    0x41d010c09050111070e0109020f07050106090f0b121c050c06011202041103072c0d060b0f060a05031f150906080106090602191b030606050a090e0607110f011a15 71
    0x40301b201013040041c0400c1d005034000b400604d00d0b903811b081c03800180daa240343c00c465456000d03001ca01d40c1c035691542ca40100d402080c0100e0341c11184030030078142803091951902207655007001c10340d1001c4081000d2034003880c25a071240510388103582c020b40c3c0d103552001000e1075902e4100e200301d02e044244091824082c0907640224499901e0407d4004000d0030004201040803035004142c06054100c00160784a80b003040c8000e2043d40013181181e00760040c0098102210f4855219041c14802c022010340d01205491384000140783c0d1006805550324182c406040640000c004840700d490b280501580260f0550101e90311540c030b001c06682c0c1d440d011150700c0d40c02d0040f000142c10420b0715422291403400b1307126031280515403800c10880610315007110744000740c0c4110388594031000208490720740300c0003c100a040c01401445582d81c01c182d11381d10341800802c204148681c10382211038502c400c00649020000c040001c1007050714500c02400701d00c00c540d840c1403040c180c02c3c6030034644040040c1030b5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 562116609 1250 562115359 562115369
    0x10b131a1c0513021003110a02010218030304031505151203090a0501020106050a0b033601060e06150a2313120807030f03020903120304060515030c041d010c0905011107 74
    0x56210f04030035420400c0c81817090750243c0405440d40c0040860a002100401c00550b55400041c0c7da004203070b0010b01001e03030700d000d01c0340319030070500c81000810380218401c54035030407590000685560700da251100e40d4000009840c0c00213081440c0061500000009080b40d03d001c6451424681e9600c00490a0354002d00a4580048880400300012441d1a02071b5400c445a044d0301803608944c5124122580307120707001a540a0707020f00440c0401c070b00c203221380f00251613191000005840c0c81004911082d0704100d94011400001405151043c0b02e01450038115180b5440000c2c203001003100110f0b40e401c5680782c156803840b0710500003840b00e85180d8180300d650384841c1d214204a010f03181600d0b42d081181800d424544c00f006420026501444030310810f0a00e8030415491f82418140351085400003400802d082450400c512401d41c1d000400c00b4000e44122008660904490070040d6081f038a00200a0300c1c0d0300389203240a249400800d042c1c25100c0c280d0719030116a10f0294103d1b13a0b5a158491 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 562117859 1250 562116609 562116631
    0x8150408070b0a05192d0b1002031b0c030714130515040c1b020d0f050703051b030307050705060a0909230708041e03050405030a0b01210b010b131a1c05 67
    0x1119600ca801001b140b20f2901480e0008401180401003040d03c5103054201c00160400103039440c0030421850321045000119000706010b04414010035641e4080340038841d411081c9900500b2942e4400f00311680919031b49405119500300010f900604802c2070008510840c00c040c00100a9480307500b09004912038100400302c1080c56030240984c410444105071420b18000e1412004a40f080140d60015403040d4000c020030b81c514030030a0001c1030a00845842600b003040b10101003000080c03600e081c0c4000729821552074890b0001541c0b80c11690380700080d40d90030603010203160b00d4200c500801d003000b842c948030200d91303901e4011111140c080340d000f4010101c01203d45002030f001034151400a20a0401910f400e45a80001e0316040d10303c00110b1300e07103100c00014429000844180b44510003410b00044000910307607a000c60300407050141c2180e107130010072001ca90400c06204c80001b2b02c035414003806c49071100e01c200c0a131a0711081c00c1c8401d101e54010300387d4054405209062040e061542 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 562119109 1250 562117859 562117901
    0x3010f064505030c2101020f031612450606091104030305030a0504020307030f140d0e01120f020708040f060f09030210200318120708150408070b0a0519 67
    0x2c0c090b807011406252210340c6d90f003800280c2e0218643c034003d42c0242171985101c02100c90b9144014190f10305400b0560f21141045041c0301001c000d543c0754500c404d821070004004241425590032104a900d042d43d0030320601c2d191001c18800b1560140040d1a85c01406001601e4010901c51541c8a54400240004c0e407c00000e040100c5552006030071520003000c0d9100140c1c2c03030f2580c00d031401c251781090f18118141e0481d140308001c104641000506c6c4c44c1410150401203000181142c0d402e11400482107889070520450500b4a5048038001540051065102c41d02ca400800da049640c0c001e01d800f048011102504150003407184104a07a0b00405001e640851360301d0840c2d034060bd51600d10184901020005580742d401d001510003882d050340b110030701c46071100030481d03503598031000b9400b26081f0391014401c042021951004020000700100740301e0300c4503c1d00f60282c0c4195a000b92202d0210018800501d440e90405402000040340200e9010b181a503800202c0300303600840e0741200c070514 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 562120359 1250 562119109 562119139
    0x3050c040501023f03150102010e190204060305120403050f070515070203011404120207060816180b0307090e060301150e0c070206030f04060c0503010f064505030c 72
    0xf13500c00038112900c03c000c4480c24880b00e5512040a503c0c0a030441ca800120400c980c12017030106200614600f4802401030500000c2c8460b22618100080c50b8011900e10100042d52940e4211000440c2c1c8602250b10b07804919105280c190000e00080f0381500030b80e084540d0386100000e0900941d440100020001130803070114004592000000326019500c81c0540d11400c86040303683c6210382d0140380190025441c050000741440044d030445010b20507040c092140e4045116070a0020068070b04180c6401035400e0b41b5411203004a40c081210303107000201b003101c1c099008140d60300311004050860043c0d2100820182a924003451031080c5107590b000030881000800180c6412070b0151002502d000d0b1150003140003076008a90116001c0750030000c1c0403c000c6a44030f03075240361002e4130700789045504020800d80e0300c4107c0d101c3c420800149000c0140410380c40354501c2c52000040741000e00c44903242d041c2d50a20315010958901e10045240006464100421491608000108240c640303080d11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 562121609 1250 562120359 562120393
    0xa0803010603020d0608030a020f12070c0927050102040801051e0f10051002030711090c1204110603040f02010e0102030408030f0f070219090f02090d1e020a0b04050103050c04050102 80
    0x685003180300e161a2039000900301e1060000300600070341c2c9c1d0302500d00c545100c01c0320340c540400b18940480b240410000000401c2c04103044000ba070782003035808210701c104103011000180300d034800034011840e8001d00c2003c021056004104860040f0000d0209558441c191446040b45146482d56080d600c00002d00749102d0f81c245903400036820074043d00c02c91300c607804102c0d0300c4d81045555000da440000c258043c0444000380103014481103580300c2003441d007079400c040c0e81e02078001051050300007007001c50200005e9854046007094040e050a4a0b07140c9070803c2034803006954000d07404107080000fa02840d51000c0101c5081c0c40c2c20038019031801c12103c914000d02c3e840350f003551f034451405010510050342c0e0341b588000780c2c80006201108660411708440101c0b0943d41c001d1103941e00c108214415506c40002192425801c010503400e03014411200c180f035921403940095006c4650080800c000420101070000e41d00c0c281d900b004940e079150307500380241c8102c1c0500d074050780c0803c0ba0400d2502003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 562122859 1250 562121609 562121617
    0x60c0f0e040203280f0b0604030201140304060212040c0e0f22030203040504230901060f0909030516140f0c1804081c050a4a10020306030f0a080301060302 68
    0x203072200f04c1145a415401aa0820f01c050515106842c0d40280b0082c120501036400c2e0340714200c81141c83d180ca1a40017070607800c1d00110540d0807040210004051007040e60555145201015040c401880c1500d0100c3c0600c3d0107008442204000c60040f88142d13041d030843c60311420b104a2038030300c0030441b00281d4003803401c0000118118401000041119190750061801ca00341c0c601801d018030803041c29103918004010818944d0380e260200403c0101c0303200c210394045401d076520000e104a03090404544900c20301c40301710001d0041070183e20070006000c1d0380380110700355101500d60340407001b02c9050b120b04d007200c9041e40c810121800111011000c0010070342151160300090319104c4952284101111103200d103140c8140e407602004003484860103a100c401c1d184441c03003414004113218078042a1030b4040900d40740321284c241500a040c0030100c01d910310383e08408590000e006090050042e40c42103450324042e0055406117242c290340043c0084500360320900081c10743c0e0801c0d0b403c40003500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 562124109 1250 562122859 562122871
    0x4020405101806030308070c05030f090f060a09291b0309100c050625030e07080f0c1201060807092301030515280e0307050d0c060c0f0e040203 63
    0x101c00203002c989580240c940080c80d07410108846295017005421140010183c0c010300000c00c0e2050f001500210403904000c01841da81521444c14001180d03116410b2441c15802035000914959413a42081507401120480010715143c41c5240c1c540e00d005208412181d045202e0910200c40c440c04610b00c0f000c03c0c601103a00b16418400c0350760002e0603140100c0000340200f83c00034900818400180f0450740d110400700c09001c142c14203003c141c1d04520080d0300315400c15640d42141104640705000709401090f90408842090890030200750b22000115085403160740d60000d4907840e94010300a140c1140d000c40003a2601d20301c0c20300c05030054000aa00c5070800c1024035070180260030070010381806540100010710300400448440100c0d2540a01100c50f0007200420381c0c10800180b4006d20100c000c4c1d0342020583c044d25200461442c0035080b00100140545181e403e2182d40c0000401c100d0782c007551051051000610080d10905030850440780050942d210803c451309081d0000c42e04a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 562125359 1250 562124109 562124131
    0x60403030516170307080601021f0b0307030605090f1b09040209130506010f0e090a020a271b1e02030d0b12010f0b1003060f05120f060c040306061d04020405 69
    0x1a0380c0d0f0340c8244035000c04200400c02907020080c00710043d44895070643c801801c3c002403445180d0025035036041451082803001c5a601c802e51138a40b03480a0020f2b2008560040bc288528201650540d0710f510300c00301e08020b681b180148003100d14540d8081403100d2100a0b10202241d01d03a502031100c04a001844405410b035286d4031a400503e040006600a0442c400c2840ca02402c003042e00307103000405040705615500115001c000f5a584123148801c031a10312088600e401421400000030340703207aa03d4960b14602e03003421b4900384000d82412100f9000650b440b000c13403050408480042d42c00071000c810059205105c00c0c051071a00341d10020055100425100c0d41c64004081242500c0d440c800c1404407503207030703040100c0905100744407914100d03203400c040c0500741c2800141c0c2c08107804c6226051052040200b5030040705002d0008883e0740350201c090700c2c11454201c803808910343c440e2104a40c4c55107801c0b40000e1005403210b80d41000207501345118036540300c0ba000c00003e00380c0503064048070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 562126609 1250 562125359 562125397
    0xf0a03060c0c05030f0405043c0b040e010e150f0105090414060a0902011404031a060f180403080a020c2121060f12060a0f0621060c0e0604030305 64
    0x1203041040501524842003017504c3e940c9050a0074403055030548203120085503400716881c00040d130f85c0c40c0c112800c00d000e80081c6070b65004460500c8050032094442c0d40e042880e0000c0c04510a1040d000341195060120403a0003007100940010314420088036030b03888401c0780310014000351800c95904c2d40c1080c0210541c080c2241c2e00d04580c0d080000036600d1080d03480d0740b06501811940c001c200ca80c030b00b800e9000c0441c01c091860b180d1103102c40c005020041c01000e9500080c0c1217030741d4480002e55071400940050140100c0d0b4642d60384800003610305401240c0283d0006207074003014001c82d001e0003070400c00f4009021b0101d0141e440c1a408400c0d030301c0b91210610010118043e00708501940311681c816502003410a54203205280c1c0404110501503e0640c0f040d40c2010b000080e15074005184000006d0b41c1c0011907900310003030400c1e8004403c1c1e442003444206401c00d4090070b01e5400c0b4052070040007014208101170b034440c850540075a170008401c1c042000424007070400780205900c3c2050361307046 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 562127859 1250 562126609 562126613
    0x60c0a1e123507030b030304121e0b010e011706060f0f01090806090106031b030308070809030705030a0507060b12060c0f120a0606022806050a0b0904050105070e0f0a03060c0c 77
    0xc980700310144203100328800300300580e0303a6050040c5c03282c000303041e00130b1480c2c1401c1890a580f51205500301505915004640505090300030342d65005c0342e078200020300d5155850710300030742c02d0740c03403c5c130940301ca2001040c801808110042002800791400805500505128006201400c0c6032a14000c3c1803082d41030000550490030300a0f2071094420384000030702c503421894450054040c0620100140401321024400242c00c500c0351600080d95081030344456403031081c2c00745940714104d0010024000030130f054080c80d41040240c100d40344180030900100b940b0100307104c0e015018040e5000540d1001c00450149504c01b0000e00011b0104950740b0320b40b071440b050080d52414280c41440b07103166030381e10070880503034188042c08500c0050005040c3c2d40a10251841d001183e11001400c4070f961071010401d010102e40c0701c00040c050203484540c0c50301d4107003051402000308450ba032010a0405c14802214074048188010003030300180210902e038119101e04004194440e203072428020784030700200c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 562129109 1250 562127859 562127927
    0x1060c060f05040311122a16030606030b0105030a0209070810050301090c09060b0408060613090f110a0f061e02010e0a0b0406060e04020f0d0201030209060c0a1e12 72
    0x2100f140282c8030107504c50056000700e450a2144c1000f011420000e00c012503030894049040d4480400240a518013031b0414220039040c540c41024000310700441600010070400c49800910445e800303800c114045aa1f140c040c035031590745c0f50708025407004540707000900740c0c2c1c0134009403a04070f000801400c1724562690082401c44e405090140c0d4a6601c0303140400c1102c8aa01400c0054294228043d040c2454804501c2e0395402c05411188900d035030317490007040381203903500000d1080d0700304d8001d20816180d41440314560281080240c002c2400d46d07004114603800b910203d044030310a5603851441c3c8545100200c4c1d5030309041d008400c40d500c034411403807102d03010801ca00e41c2d6070094041d01403901b000d01c2c0020481c2c0481d440040182203040401c00565183c4079584c401d1101541e56041070f030400d2004070001e2080d0002d03242d2000000c56000354542001484c58191803141140e081c945d82c0941522480800d40c0304000c108410100b0007400c1c151084078000621800e41445604031480410706075 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 562130359 1250 562129109 562129111
    0x10822120e0307090515010c02030618032502010e0102010615031e0615020105060d0b01171e030904050a02070b010b0a030b030a03030c031d10020c030403020312070b150901060c060f05 81
    0x81c00e41c644403003e1204168030400200580203007400c223208002c04590200340c42e00c100624441400da05c5400c82c0b502c03680e0510495000003030642c2c481d003414810800b6201038070500c04080e8009200000e4500d01d650052141d041514640c408100f07001110400450140ca00c00401d500052000c0341000c4507002e0340d000d000d000e41102035080c10111030300c2d003009084030030041102c2c5c070a0394401042408110707582c0701035045d00c000501a1108008810440c0d160864003802e80240e000c540b00d00c5803103100701001810540e40e04440034099501e8401e042020307030150311800740040400100400040440d00001c22400360319040c01320720101007400290a00658501c243d000c45e403034000101c40c540e8180b18a0b5100c085d0f034500316120100f160904c5603994002101c07036032842e50005840026840400c1a00d0080d54010216040c98111074070081c0550400c05040720096141c4011444480c0e100a28250040003c0d01c1401268680f1000311205042c5480c2a41d0b0190303603034074424000200340981 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 562131609 1250 562130359 562130369
    0x1d0d0c08060720030702060406080c0c1c0f09080303060d020a180204090c02031801031a030303010b040303090b030702100c030f09060603120e0906090403090e15010822120e0307 78
    0xd4980b600ba8000c80c83d940c1101c0403001d40c02da0800c100d01c50060780c170002a1416140c9a140c81441903555062403c901d10494554281c18030400403036490005403400d0351880032249035110f040750480b84c0401e0391095a03501400d40c1d584c00600000314103040103500e48007014002040d1100c01a640c400b0103826109605802c0d8032950000342c00c0c89601d0a90007240e90121040c401545441d920018088840c03812180e814105611403602c0700310500b00c41c050030605000142540c3e582d5942c1c000481103036000f488104d01207000707142c1c0050000440001d8030300c2807841d80c024103410b04070b03c0c441000502c0301c0d0701018141580d07600c2d810001c81c00c0b0722580f101345200700d1002500340e0950400e41140e0400404007002c101c100800721000b904c071000842e401a006a440361501e13121468203a402e40401d40044014105800401901c6018001c60040e0000c083c1c9a820303607a12002140c0000c44131068401110b14540400200024480076112960303e03a58680380003003290b01c00c002810801b8039449 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 562132859 1250 562131609 562131617
    0x7030605150313170f0a2a05030403242409200706090512070c1a040303110109080d15090902090402011b150e0d1d0d0c080607 56
    0x140301a08090a152a048154800e05030451805180c080066000c450009206000220429aa00c4414416500400542000f250703d0340c40000000f00000d01d000c00421002504004104485410384100040940c02001543c03a060460311075040300115107481001450802d114020142802c2c41400000b06418880030340d400c1000041c1e01d1440380907007003410185e2801280404011120f16070079200e001e01c4510b03c0d202d00300d60522000078000c100c0050b2541c0101c510700307154852a580200704052145240714510754881e803010305a1314442d805a5400b040401080c40841e0003262410810601c00c0c00118a03500c09a803000400e400c001b40081800e525000e401e541c04032000010030141032014170400084040c0e0b000120001006807019040c04030130300313006800d4208400d13080c0c60b058022410400110480302503e000b0890240c10301a10b01546684991b6a803186902a10f00d40180a0414040c42d4005c01c10880002000003280c6080184100040036201803100d00c0c801c4010341ca0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 562134109 1250 562132859 562132871
    0x306141807091203090312020c03060a0903050715050603190312090516031214090d0201030504030504120b10080f06062709070e0915070c030c150b03010b010504140f0303120703 78
    0x71f0101c15802241000005542000d0f121203660344000036556402009503c012942d580503040c103a8040c82010b9010348004a243c4c40c090381000541c01585c0162420f608445401800c01092217414003050700040004000300010007400300240c00600842c0c0c020401d0310108040340300c180d801c2010b558411201c44030700310b4002c00d4258110722010252100742610034508a105400502000a4070100034180369480300814280740c460001c1d41e001e0071094000841789903035414600901d50b0704640300713410074103030700408112620b000c0f5401f20080030803070041c8281d482d241c08000348070580690510100c4030343c081d0602c0704250202c24602036011800544100c41c10b1050300d1032006c0e0300602c1100304d50701442c100180500c03500c4255622041c40c0c41c00c80494141403401b00e0f10261142c00140068a032003500c1c507101c1796540c0c88220b046030101e00821034400c0070401922140518401d0150282030b15070b5000c441d0620f010b005220440080580380b8020030304041c8500d0985c03d95031440001d80d02c2c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 562135359 1250 562134109 562134113
    0xf29070b070305100e0a0f02040506030c07050c0a0303120f022b0e0f0a060c020c06190e0a050607031b120f080f0c04090b0a0503031903061418070912030903 69
    0x112420381c0011184208007107140c00e00301300705d002c0070300034207112102c1c0e6980a8402180d11603605450141030010015030f680d00340508444e0854000034015583e40c060240b040c0c1062034403000c120200d0b80c0c903440e609404c5650414000040c000c501c0d1410001e07408000014500c81c01c4403034210108803040c101c44000009200c140300f2980100d2001c6880e0740007044d4119201e0f00010b440c1c031425446400232410b50011541242407a260f41076031904028085200e0940b206210b81c10200c4540594a1b0503854030603d0030444514440c3c4201600308004011040100303110b40c480205181d0030b0002d8a4810043e6038454143c200300d042c40c5000141c030490740c0303103a0642c40620550030424a6840100b5810310018001d2984164850884056a80c0820811540702c522840c402000f0050550f07031501c1d4002d003402c021040c00901e25001a1608002050700e541485000400140140420080155081d410600e00c48041d10700014030a40391400254a01700702d900c0354036644260303601c0610038518 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 562136609 1250 562135359 562135361
    0x50408150121051903170604060b0f0c0304030209010806010e07020c030627100213091b030b0a09090606140402270d06050a0209190f29070b0703 64
    0x9499085503060400d001000030182c114105500c01d50a08407180801140e8601180b41c01160703080361190340e040702807003c24035400900503040b000b103c8240c4038095945004000032100140240080340b0b00502c040c08088200001406642102c04201d030310745a00e036000500f0300f02c000d9004400c41c2e0721110040c41480c08944210b03400c060076000800802c174480002036142c402c020080600c1d00c0801501c03501c0c4920350480b403d01c0014141c2900d004000d41103010000c1d61024804c440c00a01b54040011160f1072803281d0421969891892012010f40d1071089014026500d0202d078845070100c8046641c081c244200400ca5204840c005685450011171094550600015510552052003000510408060520104c0040824404500f801c6500146400212038405406141b411040101107042c1c0e500400781039500302c1d07400391030b81000180c1401103009401001d01c0704402000070080c202203a403180102603c80045415111002c03c001c207040d0f0080c41e030a4600103103001c10b0008080d01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 562137859 1250 562136609 562136623
    0xe0d0f020301061e030f0303140a0605010f020f0327060a020609011820121005010512120d1505090c070201140307140c0312010f08060a02040e041b05040606050408 72
    0x1015030042c840c4e040341c072543c0c200c030500c03403002030003644a52180350101442980041a4030182d401002064200369500000800003405418085910351505221007400080c0c14108400c101c002186000c0d8002390f164003c500855075004008411000e02c4010341d40e20003d01020a82c9500031300705490310103620780c2503401c00c602c0046000c000c2419400495a41c100c0400101e0032107500070082c030b2604c00070405044c29500c1ca1015070081c007400038031481c019004281254021590003907000d54031013409454034144000110040420003864403480719617040b0b442100000303c0b003d80950342d00c2d0f001c60b01000f41240c29412004d00090403000b1980c00c5654140d000800c10b02c00d505610f8050000b520101c002800900315034000304002841b6407042044889038040440c6044c1556034440c0340144a01c524042c600130b07405500c0025240041c01d100795007c984070340103460000d0301c460725115400c1d07451941c6180f01128202d404241c40d203803800b5080092031141d490541d224030b000d50980c04c03c2c030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 562139109 1250 562137859 562137869
    0x1b1903031214011505090a030c080a0512162301110d1b02070603020d020c0a030e031207021e06270103060902180105160b130b07020105070c0b070e0d0f02030106 71
    0x26400040c00444101d00c0085492001030805c0d07941e8000c100d0000b1150040c41c0d2000f0140c142004010038941008a20307500300c41c2c814412070300d0540c0c2d200d12500c00c03406044070014814034a00144ca0201d50010022245c0214142e014221203001c10301407820359010384421040c00c8800100c00030070304203e01c9402001c1c284654418990450030354001e40700d840d10f2203010209900840d16004902e4542d046030f0f55042081c0c1101c40e400e100340340c05441c5181000400d842402401c00a620009614003140c040c291300034000000003425404040d4840e45030032440d600400140000700b612110346460940c09107144101901c480c086000040640e4025040a46c541d4014008940c500305015400d503010b079400d0070400d4641c200c0841141c031340780d0700020103030626103480144442d8500c801c1142c01820b008440400c0c150751406426801d1b10b4094821a0000d140540501c0210f020a01944e800180c80d14000d07125140074000280030703078034400c02500c420710306845040c1145424032540b40200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 562140359 1250 562139109 562139141
    0x90a0806060d06020c030c070f090b01080906010b18040c1d0301140a020c160308041e0b09090a180507080f121b070302060d051e06031b19030312 64
    0x1203031503000300b2001c10324040c004200a07001306001c4100202801036408005001040310400743e2348400000700c80f0210b1117911403403450180390b1481e95100d4400684501031510007091540d28200e80b0b1455540120b110107100c40c8840b4156038140e0300e41c054110490030a51300e195240c183c10103c00303603603500354a0091181c0e140000c0c0740d540c02408008584c0c003645516005858000c04503c0d1414041c0704101241076440d00007000c010008180003400c15107112125100442442e10404182e55241d4091800e40e00010700148425241c0710b003600e88d120700c4406001c0b40b2402400300402013000c0151044855422941090142d4101000001400788011000301101e44249071402c92078803a46191658038025403d071300080800c104410402903030701404896a40c0015101100248019100060b54850b02c6282c0000406c929405601800004025242e008645007588080091000c0c109400c60b406495000100c9000050040158029103c0307840e83d2142e825140200c40714420445000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 562141609 1250 562140359 562140361
    0x1020303060a0306052a030108190c0e07090302040204150e10140c0102040f180f0c08130212070e04020118290c16060e01081527090102090a0806 64
    0x1c0d80d60b030340850b41102d401c4000021241c030b6001c590610041615060720300d44070b03801c0d500d07410b503030007072000394100d9214505440344a618010f400100c07042d0945d015106804503c000c1c044001275042c5540c002a49040c11007985a0384d90115090307030031a500c142c801081441011001607044540d1000c030b4601110f0740300c006400404060300381d14041c1c4107110080c0d40420b042c401c2c20b8096040798050a4103140d00b089150703a60804500700c95040e500681503606103591007075188001d000310501c41b181500c48101c2a52540141602038521110684c0e0020b4002c102120480080c81740d20040c1034460001003640c5041d00000d0705040300c07541c200f184035500d85810405c4407403e40c074140c0c032001c102c0065003000c81c158000004a0084556080443c054420100102e0101041d0602110b01e0740c0c9a42701b42c807139140300544540d1004c6500c1c4c4050894207543c0a418078140582c0161441e400c8284c0c01d545c945001c0c0c0100e1040200c42140d841d039030014940d002807a20310354000c01130110340001c00003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 562142859 1250 562141609 562141621
    0x60a05011e0f020a0501090c060f031a010e031e0303071719020304030c02120c01031a0a050d060204030b011404050c041503050414030f0717190e010210021c0b01020303 74
    0x1c8000d14000120400034460000300c9050302c00d20507080da86401000a00c49000b0b541002100c50040380f1400c1d01140c21098103c41c000d00034000d079201d5600400c9a01161404800151429018111140d526016510003850301041080c0c8461030301c0170000c01942c0301e00d031050303018000015054140200045d65800c00501035103601c030742e1002c41214500907031a0b4696141c25100751740d15910081d800545101c0750b91800c200001c40340c401040990b000e0094498118810320401000140c10740c105130040003d0002c0d04084800310205803042d9001032800e59240c454016202080e000154100081800101e4910340b500a05030012042c41c00e852909140030b60f8005400d48400f109000d00d919100000c0034040c910858401440c0c2c2101900c0d9035125144908401e075000c40d03403c6800004400f03842c0d140302001400d80b4040001c504012001c2240c9001c1500c1070809001c0342e0741180314080f418214980c0a000ac0c065020600303a111002c0303041c070703003c04d4103498a24182904650061040280b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 562144109 1250 562142859 562142897
    0x1706010816080a080d02070b0a09050c04061202092505030702010606021614030a0204231003230102040b0a0f030c0c030518060d0c050415090f09052706060a0501 71
    0xa4103039401340d6560f6441c01000500341c046e00034654080d0044400000f00a40007a65030020b0746e12a10130030503108140700e03c904200484407075003d6080c6a284204509005050420010f40c000922070904c01000c5225400401041c5450382d5640000f80044140401241c0900a00016000600241102c004403d5000d09081c89612078500e000698002c80c0c0301a8805000ac1c3d01c10503000750003404120004144110403030762401507281030050010000c0e281c0c054440d00901641c1c5e20035030034040c6030303101c41c00709180e030103400d00401082d5420000041c0403001c45008124107401c50b198116a003c1503440038044541528103141480072031244940001c1e4020b04488017080c0700416481c0504404002c2002c5004046c420240d6070700d480345c45032200d60050068411501600e003091016002c54104a80c070805070705c02e140c51118080814409800141c101c150f02c0301d01c000f900211203045504035110030b40034900007100c0d500700c030080c86081d00f080002c20020348400e09111154198104d48a8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 562145359 1250 562144109 562144123
    0x609031101051c1b1101140a05040c090515011116051306030c030609260313021f090905070201020f04050d020f0d0b011d0405030712020304170601081608 68
    0x18100407000a81c669041c019a2000d260100040303000c00021008400a807040a001442c1304081014041074902484050140c2002010080078002950300c91a01d184007900018104568070600240c000c44d01054038400c1034818003060302c0c42c41003a00c0000000d005a00680210400d54200d51542d40c0c48104080c0c1000884030700b074555401780c5c031550442200402c069040102040c0c04e0303d07000000d00606402c12540c850054035540321601c4030046031580040c0c034500c114030900302400090b0350307041d8441c2c0000c0d4903800a41104c1e075401c650342503401c04040d104200030220740d902d0300601c900565845465417020241c0000c62074906c52410000d00ba003e2441054420b01c03040c6180c0d803c6441d1004450b0001e0400f404024103140d90b4504030503100750900410707001c41c803c0813181040c0e210304a441801142c20030082c0d4035011050303c9050365400d00f4480401584410880004c269511120a64911820303d010740120b504080341d041c2407040c2500e4180d00a4400b850903c01540045128 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 562146609 1250 562145359 562145393
    0x3050f06012606040608070e0901061502071e0b0a0201020a1205012d09020a050a02010c0801210c031401020c01060b030408030106050c0f0a080306030118080f070602070209090a0c060903 82
    0x106043d0f600c2400040140c56160070061481c090408009001c400e150241c07402000144000c3c03100f00d032140401c0790a4680e200d00b080040c0d100003820010503904003481c0d045003c401c0440600262500076070081c40c0d0281da20303600147c1d0b0008411060941c445010844240204070a01840d403424220000b016184003500b40040e0801c2c01da4a0a003008c119500010170012009544540240202802c1f58002c00d000c2c90155080c240002d044030721071210315058455100e480c41608844001161010513103080445900040b99004008074008400641c8924804000076a403104900e200c42e0a58206500c08071080f1000c1c014080001c0c1c40c50103a82c1075a0301c9103030103500e5550182031103142000c1d000c40c0ca21503000741c3d01da0109000d000c00085104100a40c001c1c4100540c03176042401010071941c01501c0c5040901480801c05010402481c0d0103000f980c000d800c0442940024180d08402c0d1280c101d6584082034280400130b071144100c00600440c108071101070300c1e6440c0c070790160b1149804 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 562147859 1250 562146609 562146677
    0x30e0a060c20060a0e18010311030d091203050a11010510140402030c0d05070207180c4104030b010e04050c0306130b100e0702070501200c10110d03050f0601 69
    0x100351417548038003822603850101201e003c1225652401c0ca14450480d0300d0345d85002c3d01072502800d2040c4d0181c0c8240003294201001030346460040d0b08c3c02c8801d90450701c009020000803010280f42400c0c01d008440c0101c1d0104c6800038620300d44191380c1404c01c00c0700b540d82e0040d03005004105014510700d041e01e480310704480340425147d507182c81c100d080c0065504440900c402c0d0034000c04180d80315074030034604038109444000300044d00001c216030a0400e0648000a0201d410100c014880031360b040342d405540c900c82103428242c69540c3c030f4002c80001d03009446503404090400c01406800c004100200e001a8085c2c907c41c14a02c03010300c1e084400042c041d126074203c17000304400d400325204246c000d10021216803d10b06000d00000c0d2160054803a960006492035068113114103009600b08074140c4003401054180003490600c00141462034118040c0588034250070020301051150649070007203a6000034032860b141d20711080c0302d51301a05181c10090040814102000d502c840c2d1040d680200f20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 562149109 1250 562147859 562147877
    0x50a0317070f0c0803030403080618190b2e030b0d0b0907090c0c1a0115030513051f05070e060301180e030d06060809030c19030e0a060c20060a 63
    0x4041c24a034851610041039540f03020070000d960480072020714003862196881003c1629080104080411400802c989402e01080400c981004100c040c800340000710902142401000d400100da03c5642e40c0d0207414264091040c18640044600d40ca040042d241010000d0340c000300d000c40e040c49401c45004002000030004a0101c80c000c0040c3c500030b1044030800e100d13603141c0c2032009015503282d0404603540d00280036001410480001954140c0340402c8040c5050b12103c4400ca02410000d000440d02100a8020340e004ca00c0a11244c4107808800400c0194419046101800c80340009c01c01c0080102a08a0115071303030b910400c803411245500c8440d81608403010007000201014120115107100000d01070b0070582003034124004650282e00c1e1404985da40d002c055840e44211184a0195000150080714420365042845140c501a24100040d8a140808600f402046400c03450104480358500010800d401075000135501c0320341101940814108041802409801160001c0c0300c0252 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 562150359 1250 562149109 562149113
    0x9060c050403170412021009150e030d0201140c07110901030803010f0e06030a080c150f010603180c060f09081506150705060609070309051c0f0203031e100825050a031707 75
    0x108d0080c040c01120007025586c60811501400c400035079041d06010707000d4000d80d080c0e001e0042c840d140c03920b1081603505106588402c0b03041215070207600300300c1c0c3c0310300e1600c1e4500b02034032801a5203000e548610101652541019001c41e1414803551014409500800410400e034601044070344000b58029036141e120030709a001141484045000480c44080342020041d50111403550319040b00d03015107080200a4001e0440202c00548200c040c0c004011841d040002901c0740c0c010000c1d4444506c2d00c0100503440b200d09604000000c40300300e00c0c81000300709003c0e03180740000001000f10201c51400c0c3c40c0a4203a918a51250401002c80b807048582e0000201d50301e0181d044020407d0b0720209449940109035900c48403040c40103080000184540300714401e040c00001100d01868980f840c000070590001c43c2c035408510003e00f02c6802203402180010702900401100c40008009115540d482132075454103402200c680d03012502ca02c1c00040e04102041840141c10400e01200c03a5080e90b070f00e114 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 562151609 1250 562150359 562150367
    0x1080f0a1514130c080309150c12130303030b010e090f0603032208150103020a030b0415020a020c12160e131704060e10200109060c0504031704120210 66
    0x1801001c840901120100070070102c8042c003c8907264410031011220f80d440384034065503405a02407180e00000131410980622100074060301c0d03520801400c82c4c00d9207412501d084480d810540303489146805100d000d100f010303018080d90140079828070b005a200036440002801405000c1c0600c4188503000c408140a600c00744116645410300e081c0c9282e420181c4e101404014915100c0d503001d60040b06402c484411108090a04a17500280806030071802d64582c101e811300042e000f02c482496000b03503904003100500183c042c081040d006012401c800c58144036150101c0392001040d13400079442c040140d0929803113181924800759914806941d41c05516200c211292000b9103810140c03081d040c14030030300100400c140c441ea643c6502054560f80f09009070340590010403800b241c801002c801c0e451009203050f140d0050108008079881c83e180d01c800045842005043c000241c00040510502082e000c00c0190a4180018549024501241c02e190005a064020300c18019042ca81490500c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 562152859 1250 562151609 562151621
    0x4061802092235030403050901050d06180b0111060402010207090b010e09160f0903030804171603020102030105040e060103171b0f030405040605011b1e1e0b01080f0a15 74
    0x1005400c0d8880c0215000c501014000d03c07524851200c60b44101c900c9100c4085054a0003198103803503840c20302e41240c00550b0540c024610640559940703800c0040c0c680e1002119010b43c00381d031040040d4060301e02c2c000500181701c071045090700307510070414840141da00107401002c490f03030761400103206910314004a0b0704070002184c0ba50720a005038140074494103480018822180c182d121003a90004030035003603450f02c242d2310015010803c541c00080225960003c00503000d818100000d140942c6c01481070f070300c1d03a03120740309400503940400140710b18103003480b0302e4880050200080c0020761442c0e41308640c10001d10f0484080000204180d00b270105440143d542003401d050a5030f035004a04401d2541e01d80040c400c0394031450030144002003550140c008085181c140244510314400561030300310249900c411407000078102c0d03081d24400306192400038040b4000300d82c0c0c142c5510046040c0f03260b008c00d042c0c01444032500912011034100708001111200c2c242d2103000d90420381c624503400e01c001c2031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 562154109 1250 562152859 562152863
    0x30206120105090106020d140f0d0e01050103020108100f051002030f041d1b03060108270102030a06080601061e090509090313060207050f1507051203040618020922 72
    0x140454008000600c090000381690b40559401140e0381c1c2e14002241c1d20101c0c000f1403c003048074003e044a0304802d10000b891402c481d640140d10307001c40501d0550840c0d138981069002d9035520401841150383c0284620f82000c04100c091818500304000000d03424010700c525441102d2141030441c1c031030f00074800c1d0307480380c22a01440c648a540e140101010013241c0740000c9190518440020b0203011014544170f031704c02d00e141000381503039641c10055a01100160500140c41c444000c06080300d001c4c09409000440c3c080c00140c0c0304e040c40445207040e01c0c0c260f00116841c2e00940014031000d54001032054105c1c070008c1212a510840d24000c0e55101d400790441500101d1660400050100010040510040c8d00700d03446a040d940d858126102c03000d0f4010135034071402c0380505c41968603000b1049190702d07034440140c925005081d555149800301c0c140501c0c1d0003d401208001c00d101c030b18400c100c00524501c4c05c0c0f50b003400c2035500140242000400400c419035010788590f001d04107040170101016 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 562155359 1250 562154109 562154119
    0xc0f081506032503030e030102070305030a18050d030606030b120309090403030f020a05041707050f060d0e01020a09030203190201050307122003220503030103020904140a03050a03050f040b010b090402040302 91
    0x442544444010100c2c0000d45c04a8035980e48456641014821039080c40c0d055038805003941c5608030b20307202804403510111000403040c486000451420300040c1a0b289845d00c00140c15481c0c4017000d81581c400b1440329114000d80042000d40c1031010044a80ca828101c4980000d03540710714081d001806449486c1207824070100b101c012041c0c00000030000d466580c42001c01890b604001c2d41e0f518800d900030b003900851250400200c130f003000005080010158400451601d400d1100c95003203070010091000001c03c040020425818140030840740301550070664211400780d40c0010303129201c050159170811a10b070b56182c1380c000850f03000c91110042d00c2407540d0045080e400c000c000340c00c181c61504000c840400203c0e000b003001c542c14038500342d2005c041c5080d83e180d6002c000e94860014020741e040ca860920b0010541401e01c000496a88a51078250b200c103200d1800138101c460003040c9010440d401c00c103000208107049c2e288c60465440c030041a5036191030001080190040c2e0b48000c1d008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 562156609 1250 562155359 562155403
    0x12003070611070501021804061715180105090a02090105030a050d052a0709050a140610020703051e1e06131511190201110a08041b060c0c0f08150603 66
    0x8030391360f05040043c1f244115000e201668a80201408420035010510800c0d0b12404030074034000400b03440280d10500c603840f8a045c601101c084e5a0030f488045400c00201e80064901c042103103000b000702030261078150000d1940001943d01c980d551a00c50f0808400d00101041d52182c40300203040e155045400200344442d07449011480c9031341d920480c000d45480c181000300085142c2c0c81e034400d60312440e0604034a031010744c407800140310140d00410080070031400346007004000704008000700000303088421800d04bc007212a00b12941041c01250380c07144d24521140780c0e03012204002484942145490000300c5d0701299070700e0260a4210240c0c00c00480d0b9080c000c1c1c0d031001007513840103030007203c2c20b66011645060311040101d08075a0700912080074400305104d50002184940041c50713006100301c1603029243c1d060100030000603003d07400400028035200103603040210001c0c40c0401403290580b0405060304050003252a40c88000b81081c0d41d92a440005941d65810040c244564000d0302026041e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 562157859 1250 562156609 562156627
    0x40f060903031a120318060d02040810051509041509061a0a090b030a1b090f0b041a060f0d140115080108030a210912020c01200307061107050102 64
    0x103400d505034411100c640c80440c18040e4200101e50701300c00c903c0c07400510300c0d0111031240700c0c644103043c030806600200c040c031007050390340c19510080c00504000d6000b80105600b4950308015508020314000310350050840d00419900c81c04405500560310075102005411000110001000c0361000a040b103030501141c541b007031203120440b06641d401513070f107034800c0c40d02c4510403815102c0e0800c5480c1c00d035005807080e401149a003128125409400208807250603592140e90f01540c802110440c0d0342c582d20350003040035140c49d00c40c50b090115003d05514405000a0000b2428040c207901c04107038090010703000401140d01d0780900542900c080708151300e940c4890340d10364071310310501492001c03902100022031403000000603180682d466540c2d81400c00381e01060101035200c0ca41c3c2d5044030036110800d14000402841403240c504000e680104191003940c0c000514608241e80400e80c0b0468100036070720002c030b020007100c1c41583c0203000803e9107131101e403510015106084014000e54408940004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 562159109 1250 562157859 562157861
    0xc03020a0b100618081b0a0305030316110d0c0803090c040908030103030f050310090902060d0203070e0a12020d02060a0e0a0801061e050d060902030c040f020c0f0604080d05040f06090303 82
    0x400e50f14a5640d52442014410780e0902d6084e0034014200070703503c00324007082040d43c1820180000c5901500d060b034801e039240c0c0c84a1440d041680c441c10a02c074241100b002455016040c0c419051401e4020400d04040040182c003601d950600a411000008000ba100340020002c10b0b405210250003000f44070701909141c40950802c5c0400c600040b0a45c0c0c40d80d80c49032140090307d02807031a680065030094500b502c600002e202c039201c1280c0040003441201c455088603c00340d881080d06032030b0b80080e410304000300815407c81c2c1e08a249400c00d540c0036400540c40e0034212140d03031541078940583c2c54039609401c4c1e400f94030409100d03a00111080003c20071000641010046034a0b0500b0000200080b048000b00001103010b0a9000030500551101113400380d00044086800502511030807040c1034003240070364140d84411202c1c560000307902880720100300400860403400802030495070806a850345514030825034030004d81900e940105040c4540c8014000e101d039409001040020700520f0b02030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 562160359 1250 562159109 562159141
    0x181212090f0a06080c03100e0108060a141b07060209041b12050402090406050411040510060e0406120807060b032d06062404030f0c081e0d0c03020a0b 66
    0x3a0241020781a03400c1c1c141802031907103065540c25110010245c2c0d8400f041e0045401c01000200340d5150301d1400240c0481c0e4200c0b20303000e00040c0c07000c0c00c0d052074008000c40644000c000c01040001e040c00421510315040300303125082015030b2303500580d25100ea003400300c064014141d035107500c90303d03207030180e69502c807000310303003941d082942e181e0003030510084604000300c400480d4080d40080781a000507002800590041c0d034080e12660b16203880980341800308080301e40c00c8940c40c1c80d070700c0722000c05d000c3c0d05d401107500c0b80a160100c0d0300380700250401d00031400c1c42000c968010041e05000c5a001c0400640d41c100800015015040b82e90079968043c1c28480c51501d013030003e0644036075250041c0c2080010071864842d55000c1c00141c03c00685070a039400700840188402e025020070312002c400a4071051654141d60f0180c102283e139a8200810b01d41840748003a9850700200c02e1072000d00e08900f0210b0810404440303818450040c18460400342d06204500e0401003c0d03202240802c00b005503140804 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 562161609 1250 562160359 562160377
    0xb0703020c03071215050c030604091a040804090f0501051507082b0b03030c0c010e030a0f0803041101021902040f02090d0528020901170f060a02120a060b181212 71
    0x1958403954601701c08001c0350019030703440800c1da008000007521401c042d0400c88210f03100b00001c0d50380c16400300d6503074000c42041d5021122100c000808002883e042c2c010b4031200c980460041046515040008285d0102c4030403501266401207a00d030f080c44960b00a41c0c20103501e8490401c2000c0da40e03000c0d0b4619031241c0e6090100d141c0f8086074220305050000503192084a80d81c01454240d003071b4001902ca6681041c2126410f110314000301000854142180382c801b48240c411944be82058134200d9992007a0b010311a04650100c804c4217944000910340c0c40d8031a806a8000074101104c9181a010344520954542c2081ca82e0b41194204100003609484207005d11544d04240045c500f114a814001ca5002a51000c000801441081850300030580100c43c1e490413101d0415561000c141004003c50321100040c0d800704190107078000948040e548090010b504003e01e40c18104428128015400220920802311074800c1440c2c0310341500000103210701c2c0898138140b50342c445900090303200f512a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 562162859 1250 562161609 562161623
    0x207090609050c0d05060301060b0a05071101030506100c061103090c0f01052b0612080c010e07050d0303050a060f15090b040e04120516110f030d090b0703020c030712 73
    0x12001103501c0b9650203900c18501003807a1804101a03c00501805032501d40d00d5507880c80c00094805404000740380408103602c406448914608009240149002180d8180350902c002c20600780d0350300c106400110202e003414040c440c00e40c00c204000380100750950715400000000d01c000b15100043d00f00e10050101e9441a5a1651a00466075400b828a107010b400250710940700c0021386d03040a0f2482d18490190015005940d81011559030180b600181c94101d00080c40e081d44c0c1c81c082c086d1030100c03c0c16a0080c601540380c14046a040000200040c04255503000030803030322030407900a00700030b05d088888031120341d46a00c005010182181da03c03001103030300048000340112a20081c0c5048461400c0402507560715a107450014419425071a010040c0030400b101c014281036407602e0105000d00110400103c6280030b100b24841e11a0a5920a912045001c90881da204540c0000d45000c2c0c100b8940310324544c03406901d406480d0301110303814045c5007004100c0c0030660303520741c01031402520 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 562164109 1250 562162859 562162871
    0xe07081807123206071d10081008010507020307150b0901180c080903090d0f0605150a05030a12030b031006031a0c07080301090902060f0a031a030c01021b0102070b0a020709 76
    0x11220100443c0c02d0004049404c0240064492400b409401c00309a5041d046044502d281c80b00042848003102e0802012681c150180706080b0070341070082c0e000e4020351008001c1421300e48400ba40d68054064014251017203200004c001c80a25006084410340141c100300b4156103908080110503ea0000582c1c0f462034000c000d90402d100f00c281c180a195040040c6180c43c1c40d6030700707010300d13045940c0e026120541540340c1407000076410320506100e9401c145485401009032420040c0c5042c603a0712143c441e91201041c9c1300030505010b89801c8554a60030000f4134428030002003800c00500c00c0f60280d01c0c42c82c212001050000c080b0421800c0c0f403440002c1c07003103980d4046d015610f602034101c0191400c0d400f880148150301c510f41c040c0d11100d0000309590b052140c0fa1461010b80d60010714240c000a0b103401c0c0010b142001c2000d0f0f80e4a84008802134441d04032003400003581d0710f100010f580030045500825404c42c2c2d00070702c110805404100c04041e80c0d0110040c000c0d40e00c40d9148160a00546044 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 562165359 1250 562164109 562164173
    0x9060714012406052d16060f0c0806221805062d060f0a15020d110a0308060414091c0c0c050907030b030102160c0e0708180712 56
    0x40c89250642e01191a0309082c8003038414051505d02948071042d0644a211180c0301c100d0300c4500160401075a003449101005480c1e25140b03081d5480024071584440c1845144503c0903005010140c1c0440f00755a030070621251910710312910800c60082d030b803080b480c2036040d038850010742e18604541c41c06881224443c0d100d60700050404600c2405c81c04000328041c021814403408180515007000c0c005007000d40e001503c0c0002100b114031584500410840b840d960031030720b40c041c0080182d450050a09030048640c1000c80c5840342c00c40b01004040043d10b200040c040d0303456030310140d050600c20180503410b03d04403900940d1000c00140c0c52a400014445c0c01303111030320501072001050ba005602000840c80c10003408001702e0090500c0041c5522403603c00c506803005d202402c0c401c00d44400541d044003075820714014080c1640c00c141c203000420350402c1007079600030203880e421103a110400303a54401503c1210381409650707001280605c480c11403000c180200c0c003901c500c0038a40700450346603100c121 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 562166609 1250 562165359 562165421
    0xa24060f05010503130512030f1801050c0d09020103020417010b180907090c0c02130b040e01020c07030f08120408270109031118160908031305060906071401 69
    0x81c4142800601e0400018280c0c3c1d042c0f490307044500c0d1081048030020303660303103040c17046580045840003110043e01c0d0800030300114000b24216001d030204020009403c1c020515001e07440f4168200141c0d5460b464041d0031079200b5411a401003201d41d9001e01003411500c41035020303000345135115101d40d014041200383c280700f0901c040d02840030343c4000d03d885450485180c02400050900105000d903446182000d42c171b80828581e0a46c901c0c400000760103007400200310072200d0125090520381c4c4140081c00742d440780010740d0380550340c01000011303041c85586006480c2c1e1040a52222188680c50203010800440e40e010b04000d5130202000ba00103007202c045102c282c400f418111b07001407588801000416003085c102800c410303000d00004030f03201c8040c440c440e0610055800f040039148407251600c1d03d41e4000a418003400d1280d01131450100000103065035110507001d2240b0aa40000340d5039072959800045404281e0b20418442005054140f8240200824110a4051010b112481032882c0355 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 562167859 1250 562166609 562166639
    0x17010815060a140405040807060c0e040612031d300105070518040f020d0c0c11030d02060c130302090702030703030b0303092803020d0b04060c0f0509040209030a2406 73
    0x20440b036030701a085000f01004090725000e041a43c0b2032a08010060204100c0c0c000c040b040009611042d156180305801d0004541c40c03a4031140102d064140340c2000607911441113015030714280c484801c001c4c40301001811a2041c5d020b444042e444105c01a0182034000080000a01406000300301603a502c100c01c1d502c40c8601c60207850800240604503506150a0780000c0103900482c0006007000540311500b81100c41200c0186c000c2443c40c64a0010480155040d0b03410100582c081c00000d0404480030396104d40c058030b18401c8050100d044003901076001c003800c00464000300b5609040c103111f90060b40343d80c803580781500020704140d8004210b0a000040722501c0c4000740040c0510b6074101114030001c190344180890083d01000700001603a03889000e2296503001c1c03c164042070030245010f00032564814124401c0c0150000815042a040010b541000006903005641d40e0b041400107800e01801d01d10041c010000f02d5080c0b50821022440031201903030f038960822410791649501052004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 562169109 1250 562167859 562167869
    0x105060a0f060c2609040605042a0c050312072304050105071112010e0f0601030c14180703020406031a060901201504030e0d05120a17010815060a 64
    0x206200c0d0410426100c0d440c0401c180c0d00400340d189134461003125222071200c0b4000401c0040c0008125504c2d10710741445074200a107001c9a08012100d0810f90a00c0c000c403008c48800070000e4080c550140550140e440e101003181d00000390fa41d02d0490b000900142c000a440b080c0010f02c0103000401b828040c601d540522003501c02206003864070301001112290300c21002151940200c034107015403619010301e60075030504c8032000403407180027a18407645803803801d484030300d40d0740c0c40a0010000310302080c0121040d103600c0c001e04e42c1e02400a40105040e030050341d180720b010214000800c504654554080c206075400390b503045c000030b01c0d24000b1140b060110110103910040800401c00700d980620302c0e01c51f51040255005180c00031034010141411031440301c2da5910b00450b8208030806034403e1701080010011a9480c0b180e4030152540359846203101c080072001c0350001844d41009005004084c442e4102a0505d0301641e15244000d03222009105a0880151000c0104415103000e104c0038083c1c038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 562170359 1250 562169109 562169129
    0x80f0d091401020615030f16090c0503040f0201080c0f03040b271e12030702030a030f18060f0e070311040606050c060a09030509041805060f09030a082d07020105060a 73
    0x5101c2002200a86400004486e4148200f00c4042c00d02003091215910f5508980030600f0140c0c0342080c1441910140404401002070410400c000124030354007603441990203181c111541c1d55881001c0b00c13140324005070050140c0d004030421080048842c0058810422101c0460113080300700500c44032162a02d01c240115002141c0d01054041e418080c1054101c014045400d0501840301491182d030003a181d440c016000028140d01d5141c00d40221051142401d20800600040001c0744809052486000f840142c0710447e984080030980c21483c0c0d003c01a500f520705d101c0d640d1400f8111b0010003150280107504064000030003501131000c2e0340345965048054a0180d03180305000c0010405c00100710107001090180100e1030b203403441840c8034003101c00d1407001810305c00e0403c4d1f441c2840c01406151100c00401c100010380c100030045c0c86001d801c0b401c0444985d250030424646c0424242e590140352200b020808207214811280b690280f035940c0c000704000e0302d9450500c0b2001c1d03501d00900f5941 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 562171609 1250 562170359 562170361
    0x203041a100e09031b0601080607050405010c1104060b0406090810020310060807090b0412030e15041e030f060c090f0f0506030919080c1002090f0405040c080f0d0914010206 76
    0x30021521000c3c0d4000c04420950b4a803405000c8484642c000d1444040d200c3c1c0d01107070060040100821603290461440c0c140f01c1e00300b03403501000070010f144000e0002c0144064000404c15900c5641044003d405011509900d95894010041503003800f031140904902c6450201c0000490a00c201c80c0600004034003000702c9c0b414045c00f550750076405868501000a56140082d101d0200d50180029100d140c000440044544c10010403410910148612031180081200745800d03030f45007140c2c01c889008001641013202c0b45808841700340154000780840e80e501540200b0070805034019140707051162500302080f600c0e0070883c00c0004190056003660f980700f440c20720a0389010030242d030780300202c4c030121000d10b01c1c101c0c0118440414100e00315415100402c045290701030910000c060b402c4405001c605001403040010380148007810040d005640d6600490103200c04076140c04060700b0b03030200306c40d21400c900301e42995818001c8002c500040c020380000c115031404002003e5001d80584c020409 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 562172859 1250 562171609 562171619
    0x1f030b040b0d0f03110321010b1206011b0b0108070512060c040504090807141e01020c0604080a0c02030706080a0b010905030607113412051002030a18060203041a10 72
    0x2910348601e0003134040c031560443d2071012050400c0141110b40e00798007000c40100c00000302c0101c1030010b1b08030104e101e5050102d002900001141c2030742c001c6013480d011881150822809803640c010340c00c090a180e10050010480c410000f42c0b902c00c446083d1041d80c3c0303600441c43d51a071541c1c801d0710110b005c114104400c0280d498103800c10440c0364010250b242c030301103c55807403810282c43c4000c00c1040b50000c03c4002c400e06030501c918420b4130040d40003585030620b5406200c0d2910030040000b00713000d001150580300380b4422924140d000340d015003201c45641e1601c0000c1c0c200c80c01104e811904608061640e00c4651107450381d54200c40d406002000303a515044000e031850304c00405107900910aa455003400c071440481c80219003404010307065620140541e1404000525401c848a03102c0c0310003401d0000f8100041e1428042035400713005890f03454244505000d4201b01e2101002c02003250221004d00010741d0065000e00e2281107202043d045210003420744010840303000902801048003001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 562174109 1250 562172859 562172873
    0xd020a021e04020904060306090b070f0f210204180b0307050604050d0212030d0b0102070801110f0d02120408041502070501200724021902060414010507021f030b040b0d 74
    0x203000d10020400f50500c0d9000000c90201c50b0158020303500d894543d040c40051160042c070a5030460441d103080034580351400406415084030540c03510400011000300b10447c1d002030801d60040f40710020541d92150744441003281c00d100c0001ca146c00c03e28020300100186000074025003201c101405840c1024500020040032400034482a0703000f181070407101c1c280b000700f0f000920010000e0000000e410050703000091800c501c3d500b0288980c0e00d4000c0070400c41e030140c0c0956103d24010030382c0a50b200c032602d20910207400350607620100340340d4400a20081107280005030081e18044030b5850080c45000400300c1e941c0c509072080c01e003c41d107410003100c80c034210040704000c0041e40100700c1e407407641c0c2c80a142c090110062001e032004003075101039002080e414481003c9540d0101000d058030303201c0d034000400c0c6110318031600509080c600700b040321070790040341543c1005030020101c0341103030346007511280c6c040e4110180c5400249080c03904080c0349070078850030210700d070082d00054075101d00d41d03180d075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 562175359 1250 562174109 562174159
    0x6010f180c11062d01031a04030c0c0315050708190e0106260d021b09100509040b15010306061b06110f04062312040c050307030c05030d020a02 63
    0x60030002d98070040340011508200c501d024100001804030704400b51142000e10300c0000c20211881c001c903138010408103c100e402540e500602d140c0b04061901c3c0c0303203415203034100404030042000007080000814441e90f00300480e07446407009003c2c007241e07460603800c84074094111602c130b40ca80c001c84000c08402d4910760102c44103a070340380700000d10b194444e4104080340d01140c0150048070f05c2c803e61b0140b90101030003423401c628224001043c0000c00030f019455010000d0303004500626410b0009100360521000500052001419414560400b1b05102e018010101c2e1480345064484035100350552007445018102c45903651818007a101082a400e18012028810b0354502c1e01c4207240c410350000d0800800c01540d0f04240d07184d44030702e0001c01030820384580c101641c1000e015103544070811402c0e000c8030b034000240c0043c20078995440c035010500b40c895401c560b42512850502000f04203419002600780c450480c1200d20880d40640c04a035112816100250419540b40781031401c00d44202c450 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 562176609 1250 562175359 562175381
    0xe0301020d0f0e0f01020301063e010b01080f01080a020d061b05040911040b09060a0c12020a020901080a080a1d19030303050a09050304050622030b060306010f18 71
    0x35281c806140000c0041c2d80103001501c0c511a61106042c2020100b04483c00040041d64000e50039903250a102074000140d002c400c1c0c007014001892004d502468500b411001e8084043c514010250303283d40c01e00810304d4180301808159a24041100c55074404800381c100c40381a40203040d00016982888100500e00138220ba00a840d400386aa00701016030a505405e00b0994480d500d0b10315013201c403402d0310101d5400b40d184500130081400380000c544100c55a19005940042d174030b2082c101c0482d14962030f042c010340704030340544800400580c0403e01444460080341c1038030342e0741d8a6580302605d030b060690001304120401c2010504950040d0b010b4006082504c030800e000086001c0850f0071071820011400c0401040f150600805825114841d04a211182c040206800700e135a404e0ba02e10450164034407400e8081404464242071300c1d10b0a02d01c6906546032407017a9640c2c503241d41d00c007106503603091180c0500c000100b55000b00000c810221401c2801e41d543d00108041c00318001c103401c01407 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 562177859 1250 562176609 562176611
    0xa08070b07031728060605030721050406020405122a0d08121008010e0703060e070b0c0a26030106180e1504060b090d1704051003050613050403020d0e0301 68
    0x6242c140d260f84502911a4101c0482002503030000302107090180d0b9107070003150400d440c084c0d0a108296004040c2c03a84194181003d00300d030ac00c01070600326900542c001c0165210700b480108020030100741c003e0011960b098070700b440c01d811140c60b859100d0806120041642c4007111910032300e004801000c2d001e059010b4401140030302640c0356a03034580d00084101c07003000d003007500780100c4a0381965810024003950008000898030041000d40b200e03920310000c1c02c11621640c0302d2915010a00c4808020142c168030b20350340e080b0704800310303446070000c82080e2089080c13240784481d0151300141402c00c0003144000742e0329580c01c014040e2803003070100312034218010300351134085107924034010a180070b200c100001d00717440c1d0b10800410044d00c806401040702c2e00f01c1070041c14015125408104904e9501800c0c0740c0f007a04020010098074000c1d030748019440340e000321690140d030b50580d210702d015100c140e85e165200c02e21101e240054503810398000300141d2080c1100ea54051294941100c1400c0c0100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 562179109 1250 562177859 562177877
    0x11030f100f02071509051905060718171b0a0e010b0d09060e060f070e0a06211d06010608061c031107060e01020c040510051306030203060f070e0a08070b0703 69
    0xc8120807070f600b000c0c03d5000d10780c1d44c1800305d0511404024101042000710040070895181d0fa403940c0e115907002d08541c091000c0916504051f080e44103482c400303000c68151b401c0b03400d00d20300000c95a4107142c03020505038441c010345114150906400395001d03155018940d22641c0d10342045070003207602820524000b07075528204080081d2050181c0c01800c43c2a200502d41814400079540c02d00c1c6001d00918180140c14120100c03e8a580803c0d50846542e03040c1640c1164241480007240400400601049032400100c1202d10a0040a100b500f8a40d07504460030343e80c0310042a90482c00035103e80da4088030300d280301c1e2a25030b91400b005400e144a1301d407801810191680d00d41c5841e60b00d400c030502103001d18454510550381080150050305049400744024108072610b44a02009030041c0350140c0040481c1a0f40c410382a04030800440e80601121410b140005204600d44001c0d5003050000f0303807c2c2850041450241640000d4418110113090782514204041040e0b510442045050015400c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 562180359 1250 562179109 562179113
    0x902040b03010314010b09130210020c0f01030906110a110d030216080c0102130807080138010c0c06050405011214191808090f01081308130806070c11030f100f0207 72
    0x47e0600b402200e5154200780414120f10400082d450800282000c540c800342c80c104456558039441c07041c0d40000c2c02c0010310100c2c2402d058010b000c8050380044181d60000c2c1094982e41d00c8080c8050001611041d218540703100364044080e071041030f9042080d01d0100d00c0c3d1402003040f010081c6407a02c0c50b0000180b80c41d6600c2d0035105a107940744d2108459800c111410001645e083c06100c00203118070b84d11017010f0076040704100001d00e014000b07041c0396a940b54a1041030740100d0b80f1101c8250041e403600e4085586083c0141070303521501400d4001401450f081e1070240706400b0340740401d4014000101c0540d180d12000c042000c0e26a20303010320a460300300c2c092906908960b0450f299000f10800c2d60b9840c01d0b0b50502030140c4c501e01e445070410401c03404008003040c444102d001d0307950744a500641c1e0340d004021190890031090300852040c1c024001441080c07a042220340c03500301d205859054000d5130120170192122000394004011707400999030f070342c9400305035800301c030314080094801030a002c00340d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 562181609 1250 562180359 562180369
    0x1a010602100f1803021b010c02013908070201300b03010b0a0902040e060f0a091e0c020109030908032a0f010c261501080603071707030308010902040b03010314010b 72
    0x3c2c01e4250003603001440080108440c201541015a9007800c0c121056031241e80001c0146038010130b6191250b2118203001d02c0030306407014075100720312480d602c26403942d0181003550351580046e2041303020491000e8000301c1c0d00801c1841c045074001c00e88003240040c410404d100701070240180d98541c503559481d54040b207640c400c20b04401a000241c0c0050701c1e1800c0c00c0341036080c1310b0041c0a840c4100021001401155185501c0d8806d0ba00710300c0012540560207100f040c13640c0d11f80c4800008480c100300004107166030552058031194000e40d40d04290a640d9050a07440c1e10840072100c40c1c0b01003140414003605400d41510f000c412030682210020888188140e08542048101c2d400240745602c85501c0070038107078806a002580b82c00c0c8004607007415100c81030074921000d00141030220748000944282e5003800018000d1560751406203440d60400706154542813240070481c0810380007800415590030074030a039000c3d690440c1000d0b1860742151903981c03404030703d55003000c02503490b100c1c0c5c9011a02d40c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 562182859 1250 562181609 562181651
    0x3050906090f1f11030c25050d0605060f121c02070b03040c230f04180609290f18030d0c050d06150206040b1504020301030503071a010602100f 63
    0x1c035032858121000b078003c010400c1403148281034003030740140040700c03010300d020490b8802100c0140320918400603000018454140c1980803681c000402c1d814a024028150000e0f403040340300300c0d002101030748558204418500c20902d014100d5010384040320060301e044260383c90b00303405401103a4000c1d40d590508080f6610803030701100c02c1580c24400f0088802000242c84400203a001c1320b00c202c9101d0008125001c2009a020340300e182c480c00b440c1c1305810b114000202e007507005001404003845c0742c01c021000306405050725405031049480b40224191501d0228098410a514180f068032080d801810580504469110a0108200e10b030603003007da1044212541844c2c540c0d58460141c070000f2001c940c100d507c5003401c80304095030220159400b180b200d6015134072541c41c036280d8031400142c0d80352801202a0f6038106200000200c1801800000342c090b40d0310504408588015003400910400e9080c494100540c1c00259044200ea00b01c0c4c01000d240c5d2268800003505685c612950300030b00c84 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 562184109 1250 562182859 562182889
    0x1706091b0315030d14120a0b031501230f04020a1704030305010f06050a2304091104030219081c05161a0f0c04090e101113080a03050906090f 62
    0x300160045080c03c051000403540422401c3c02c2c40403c00340c860102d032034425000301c5030680110b80d00007030410090ba03102950005000e401c035610081103070360f0100900000c2c02420352035000da961081841032020012013603041301600d40e002004a05041c400a504445004003d10280d542480e0040034058210307845540266004502c0d940741240340c1603114081d40245040100c208040c04105800048080b070246110b400d0484003210310400d0009806240c02c1000010b00f451103091000700c0300703409042036030b0080781c508a08480202200020b90000c6c4501c1b4401d80001c10491150410000d5180c2c0407012400c0040c5408031000781040c05078040b80e011991100d99801182115014000c05540a00021000305071400d0200206203180103922800c070905448192204c0d00000030300c10260403d007a0201400144680000700c0300c540c1252140034000c2c03070340f4040010780c10000505440d086030141c403400d2404e00c2400600c109607000046003030304000320f18801c0c0d9064542d80d0380da4203490 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 562185359 1250 562184109 562184131
    0x50c19080a061a071716020906180a0c09050f010816031b0503040303050a0606080c0c010608121902010c0806120102070b330f0111120d0204060f1706091b03 69
    0x8084c034076208121400c2c445000f88200000d00002c07801c110358105a4103030300e4040381c1c1190346545102c00584114811b4403081078440307112060040e0f115603500310300c1104006440e4091110744440a00c44650351088075507000440381c3c00400c408114401215444c6a000c4c03a011864440407030041d505090003c6032000015000000c1000380b5505200d0280c002022940a1080707503c0c1000080480201408002e44118001030703100310319100b540814010440031040d02c1040707210f18107ca400ba001801c0c482c8030003a00540c0d0380e00d40c510607c10700785c100700c1d50f441d40250b64490f2010f20001110042d0b44440300e65003000302001080d50303d04c4d4541714081602e402580861280480a4441500c2c11840c280c2c801c20f95491441da0754104d5902c050781c1f428a480901025414600c81c501181e001e0a00100ca80c0000c0108581c01d00780c00800079034602e91101e8580c020104022944681c101d500030301a02120b8010550500c0c14080d000d030014005440c0040c0f030040b09800340792540c0300f81e81071440300c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 562186609 1250 562185359 562185367
    0x4060f140f1306031407050c0312100305150c0f031009022712060109020c010216030503060a240c14150108060a06051c1707030f03050c19080a061a 65
    0x24100c0e0b009101c06410320786070500c01c00035400305a24175004094254030600c480403c2c0108084420002d807812202e204500004c01d00300413000203454111404141c50342c1c0180602d03201c171440c181002d03034040c002004445243c010340081080c074981000d0102c801c460000f4000103040d980500240003041000e02d0310a0b0741c4501c003009a240c00342d00640c094000c180030030081d841e12001060650442d00c0c000c1c0050390312085d500c0200d00901c00c41143c40c0cbc0d1082c600d0256418558080d01030340c4111429a40c00d110f0b140c88508507920550903114206a2907400c0f80101500d43c403844244041c58881c418907507805840c1c0c1180f50816a00501e903040c001010f45c0108a01242048501c0e000007040804011507806c000104046208030300c070007946546c40c40300c1c610801c1440100341c0040400700b803040381c50703441d1032034000e0a800141c00710b000060706100c08610445030050032a8031005080610200c000b2598000782c03180600200384068885c0e8840340040c04e20b40302450303001440d8101424a40d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 562187859 1250 562186609 562186627
    0x5070c02270a180b04020406031704031a010e072006070210060905040203070b1c09060b04051819050106081002130f18020304060209040f0c02070509060604060f140f 73
    0xd4600000c0c40c901050342008040f100658143c0049a03c5a81051003241c441d915400450068100d95200a02c00d040510701d9908020b540e0000c0d00030380b0b11607131540ca4900421030490304c07143d0f000e004041d40c1d6012200400e440340d0180703480b20a50400050b0300d000140759141e0160404100300c03040c81c05078200d61048540c00406100c0d0b540a4200d03014200054106900420384d1940305004a440f400000200078a56819041d0f10480010340658240041a002d1410401412013800041c1c001c44c1010081034124040a070140030140310880208046040c4060300c3e0b8010719104c0341600c5035560790601052421050110f15455000104096900c03142c0b1001060404034660210394021b40d40c2d4024001c1c504600490750441b0301b180005603c1ea100c5050002c000d1040307480c1c40758020700d04000388108000c07a400414030701d1455001d688906542e44203000d410301e01140c0039079200301e04001c05d03c08203001d0085200c01041920b4418900b104e211002070041d8414100d00c900078070003040c5001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 562189109 1250 562187859 562187929
    0x708070f0605040e012d08010b010e03031602150403050a11100f020327060a17060a030b0a050a110d09060b100e0d06022104060507051201030605070c02 67
    0x20040590340707003843c58149080840b407003d80e4180140e821003480140c5608405400440d04040001d0800c6000045a52400014004c0007055201030100d1291501255985008000d8a00e01c00c6215401008040c0c20390030041403c0c0e0b132080e01d010501040c007010000c5842080718080b618450880e101030240728108201c28200c0c50400c0c4401c00864582e140741c900d50100580d8100200a4062001020034100c1a000030703807025a0540c00040120705c1009041d4071010107100e099582c0d6100c1115150740c0c0c140081e10103503010251001044c500030610f1006a41d1040d035200751a0600050700043c071200042195001e00000c0c07081e692150a804103012251250300800e83c01100d60002401100d20302400c0c0c5070071091400e202e102030a5142091042d150100d4020040c614418540000d030705007844c00b41171041d942a180c443c03624000404550003141200c20f090041034a80f4800d0b07186a803103502034800201000100b01e42000c00c2d83c01030716034441800d0b40c0d00c7c1d400a48801c0d84140300310704e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 562190359 1250 562189109 562189139
    0x1020a020c040e0c0a1502030d020f130b0c0a1e0501092003010c080a051009020d060305060a0b060f0a02210a02190201052508070c050a0605030f01090b01020a0203070807 75
    0x1900fa40c1041140f1200780d43d5622a1200321440e44038020714603122540b05074118014141c119174541e00000b0281484403c24006051070704e0180d00c0303ea84c2644802e10401e0601428000700800c0d801a003644c008920b0340300049604051851450502d10f4495403110700f562160141118080395018840b24003500c010300d01040c15000390001c01800301c4954004000100181580c4021959100490000003002040c2c2000d06002541550364031101c100d088c1c01005544820b840900820010402050b07017800354a0780e05400404040c20071200002c13a4a0503400b00303803003d05621a0000c622824106100c01400e4607590000d020344401d0740401c01f906080d10f001161030780300d25800b035110050f81c01000340c44040c80e041050015580c408003080001a0030040c010342101c001244e114100100704448606558068402d11422a0b40302d0082d80c00e0b000607104141c0000120703005000d003000365030080401c00343c1441181d800c0c0b007880c0c01090401e062600405150303004200e09000c41141c403100e039 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 562191609 1250 562190359 562190381
    0xf090203070915091502010f0504050303011d0c0f0c160609030210210f09020a0f090b0d050c0108060406180603020102010b10020c0d0228050f0f092701020a020c04 72
    0x100c3d201c038110420081c86401107005942c118050f105030060100e200750b00031105110413040c200310b6400e01d402d000341e480d0001d00c198003d144116040304840c3c4881e14074203015022510784581032400780501310340190800f07030301c030425441110782c80607180d0881c0c410b15000b040c45486440b079140c191700501c1115912204054103004500c001d04030303a18581e5007101c2482c00d801000291900c040981c41c40500040d800195100400704d40100d01c0032140140d20040301d24481d4104081c00004050111280d92020054800d4200265043c2c00c0d5004514007039104000030710003e612611010340355801c04a40c554041004e90766034050086580901c1103407110388003190b01074841004020000e40d210003103d480c9008a0300c000303c6070115121484800030044124520750205221807182e0074400c0d500307101c0c851047c104128280d074641800d0113900c010318000380000c669a5618040f80f4012032661016950f41d521101d45103c1c8500c082c80a40100d250650260251030750440401090340c01c90b00030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 562192859 1250 562191609 562191629
    0x5060703050a1b0c022404080f0d09080a030503091c0e0a050303040b070f080702062d0406050a030c2309010e04050603030909071809241a090a0f0902030709 69
    0x43c0c445959000780c00109025412207480c402e040c4801413425881d01c407404100400500820f010400d504042014001c0340b81a804450703076000c01c54021607040280781329068464010524003400300380f28000459010000c041100ca60b582011209050b042c6203d070002d00107080809441301071320b82008030030000d2070114015800c0a080a8400005105282004150030007412014040100405c00d07981b2007a0000e100c0d58480c8503255090b60640d09104030385005028525080d00342501e4201558250382150b96140c0c00c042c4038030400d80041a52020344070a020107040c0024034141c2c0384880032880292014080e0301c03400f01c1c1002409a0351041092071090307040ca001c220306074400106807014010b0843d2050034548031014191a0380c542044c40140b111401350021a00941a4100100340891000c0b81608201007108002c0100e101e400341c2c0714450f072042d94400310340400310090111b400c4018001514559100e4010071040b038183d014038142a000300400002541006100300203184090b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 562194109 1250 562192859 562192901
    0x80708071107050d03110a0606030519080f09190f140d080a05070305120a0212151008100906030b070305070f080109020d02070605100527010b090d05060703050a 71
    0x103094450200f405094001e40c004510141494810f0103050f07503000c00e10094551006c60740c1856000307015507000a80d40761151280c035118500c0d180005000c201c1e04404100d04000c10a40300d640b86902506080740d01525807110416503401c494004002800e400103401c08403032910030150200c0401c480c0380c0d44903080c40b070782c0c88020a210f001140c3c1e082c0414600250384420528054546015042c05e0105000d0800100005042c00780c2c000e140701d003e11040303401c155403003d000428030080d070bd403801d40056084548120090003000400c0d0440030620b07100c020070751078032001c904a444680c0140c0b041c010744428001195050f21032141c010446142200402c135900d0300251600d441885015006580014202e10700c00d2140c0c16520719030b0380140280540d0604c020b00c2c0160240b18081d10b0310590001600d43c1103085211124440d01c568400c1e00342c41e80e031801c04e4080041d04200340031030f0080904c003620400a181407080d02c1c1310f492a910001a642803c0c50560112180c9148c0e050700201c0e140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 562195359 1250 562194109 562194137
    0x20402092d031207120201110c0a0312091e030905030a0305040e0c040b0301060809010f0204080a05010605190b09030a0f0308071403040b0f0604060918021219080714070608070807 79
    0x190490b41c80540102d85d4290105041c1c504034014100340b104c0755441301c00811040300c903840100d13070404418001da807020041655640301104942d151301c070060040300f4092040000400181d041d5819502130b041c010070055845010a0408408010850000708001014400e04000d03000a031340144d5000a06800c10f42405c800302824070040c01010705000b591000250b04103001d40001019a2541d5004c0d92200d80d103034243c50707468065410440d800e5081880118041c10072483c403002240c2502c2401c4007003854000c2d03404507603201001807909801011050004a1001c00b08020328030b109583e030890500e4070316002407400c803d0040d41845c42e2010018080455408501250072841d118592801c686821000900600c2e0a60090030b8150400d41140032004152924441150080e16401000e080000b24152a20503001510050300014449040455110b001074517450344100c0c80b4a038a4071006444c1440c2c102d459204a0001d02d003002000030a5501a0106412111504001040071454 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 562196609 1250 562195359 562195393
    0x9020307091b230f07060507030e100902030c0d112e08090f100e0d0302070c03080f0c030c0d1b11062a0322060c0b04020402092d03 58
    0xc501c240d003040030808031503000700052020150388440720603181ea42d134000d405900d48117400051066a843d407030000091480c0740a80154031408a2840240c050b12020b04815001003103a05c80690b0580b0529003243e41d2500e84001848125002d040496401800e40d002c200d030a500146101020514003c00742e160400040c0045100303025030b003494003c0d0b0f6100c4003042c2c681540b0385103900c1c4510440b00300300500c0345035078407a504882035041135684c3c00403c020300394203034866850010101d4141a00410200300400064420036440c01e120b40c1c039010340b15807440d01d190081e60320f4001e66040300a4481303440360403a410108040311484408031928054980c661580440d050644c016000051038004101d201022000c3d111494103100c901c52695544490f913036000102203180107003440c90209802c0c4450b00048007201c000ba034450000d140c190350750280f03c10740500202d03002a0288601c1c030103a13664002440c4070a0308440a02c500300e4505000c0d010159440c1c4149019030410f0f100301ca100c40d0301e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 562197859 1250 562196609 562196651
    0x121a0601050f160201050d02120105040605030f0619180303050106030f050c09090c1b0a020307080624010e090103060b1f090504090206070204140403080903091e01020f01020301090902030709 84
    0x103038560340110101c00e1300040c0c0b07551280c5030800e001540f0029038800122900750515050350700a8804104254685003407540d00d50030103040749110382c449800148030b01110008200c15119550010802c540602c0520000d03504845045000c02d40310700051181702d030701d44144881c40b1000d0b0024484ca00b84081c2000c01c91160701941d41c01500c013000019007100c2c80c1c030100c680c14a41850074071110721080300b0940c2c840c501520124400d0080e10000a1640c00c00142c207405001c145214a03918108002070141c41001103035920f040c010302646901803035440324001c0340214010600403550f4001142003010048803a1352803450884008203140c1e5280c0d00c420b080040d640d0542d0001100162400041d010740a4072900a40c01802e00483e42c29000390301c45660f008500c07a80710500603840785c242d200e4982c09800002500080c06a41c40b00d902c0041d501d4800c03c400c4180150f454003406e0000b4182a644260012400c19458141410440c10104802c900800c440602042400f240d03400e03ca407086a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 562199109 1250 562197859 562197877
    0x40c35181606050f2101090603140303060319050a08040b04090f0e0705240a0504030201180e070804081306110c030c1503060307150201050a050906060d020613121a0601050f 76
    0x40080340318942d17040d034103161042d2840b000100d6419580d65010000c050212804101c941c407541c8400c486240100105803405918024080c0a4454103c582640100850752041d60b440c0702d40c4907180d011800e00c80040015004451242d170b962070601308102c054840c000001c004141c50120000303481c090124414094620854a03c07070207006143c003011081500d0032079032103e01c0000800900700e64001c07008000701c074402e891b00300e082c8040c442421450701c454484d40c0d4101601600054000b80304044141d4064860003050381440800c12503041000160b800904c04100740309a05480707030320104440700b1017000132001042003c3c20300c4d01040292010140d800304c4800003002082c982e40c0c040c080e80f000b600401e804485400c482d03c200a01921064460031101403402c00030401f4520003081c0cc0e40708480241c440130307501469a081c404e00c0ea009034002c014030702c00b80c07034041a1403c442d00b5146010707020355a000c40a9110381c40e6015988000b80c215030511000b00102d000000112064541c400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 562200359 1250 562199109 562199137
    0xc060c050a14030f0f09180108070905070c1401090215040807050d03090512011e060b1603030605281e21080714010605040c3518160605 60
    0x1c80240c840c91440c02003180c1480c0035030000c5a05c40010390707180007600c1035070011200000d5810030107403c0704c1e020740700b2701441503240c0100300c050044a4007604029001009460300076400e80300d5032905401c04002041d581b00d241d449078142d00030740c688001c40e01c0c0000d030240700d403d24252074031642c25561091885214007544402c80c1d5902071501034420500148405031001406d00100201e0500a00c0051010000440706085132085003455120314802e0b5101095514a8445d00d83c02c642da22100d894402ca04050304c1d86000703c4d42e52102201040303d68844510740440311a00441e81803a6911070300b166942c0c81d80f9003801c0202841044600003203401040ea080c142c1d4030305820500f00b00c0080320b40940f812800052040400000c0031000d8290210340c40204100d0307480d602008140e620742c9082c1030004058031002c50580c80c0c80c4035142400303105c103100031100c11540300d40600e84810880324a46000c2c2803e0410302201d07c00e0020312094402a40800340083c10910701500c64040d40d9007442402d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 562201609 1250 562200359 562200383
    0x80105060301050619060309022707020f01110909041401060906050411161727010201180b1b0d0908090901060c08040308030415090c081203101202030304150201090c060c050a 77
    0x340d02c03141003241a114081c1d01020b0ac01c1900704102041e454140c95000040c40303161a0183d200c83c041c42510078410f03014001d1490f1421040400118a40c0580182c80100c03510b96013003480b0509110348002401c030414046102c524010401044807070700001071030590710801a0008004113000c039242140e0f8801035003014071200072030344800b40c022810010499404410415803040b21003505403807140c2c00368024820f1050700d078004041210203800c02044050b0003c08650340c103800801c0650307075000c01d582c503e04100c01841d0315801d0f50002c00080c0d800800000d6072400f581014410f144c0540010b0414070f40500c015075941e00103201c1c070710020b404aa0003001023020040408202c1c0000c076138607031f020700c8668154142403200d554540302d034203c203129a0341e00715002130003034007035a00c118440c5c0d1194004500c0c0c5841483c1c564180e81c0200c0c0d04d8003040001080c0e44074000001c6c0001c000030360002403010320f02d04d407034980faa00b0b9800850034005840a00d50004800140100c10360b64403140860301c1c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 562202859 1250 562201609 562201613
    0x5010c03021e0610081c0509040f02030f07140301030b07050a030f152c0a1116031e1704060b03011b0c060606050406050a0e010513080105060301050619060309 70
    0x40c0394000101e4a10801d100b0748040000c04006000c40c040c03090030041038400c0d55124070f130994074803403201d00c40c0d06c07184000719090405003ea40034000b0150003a102081418125a89004980c8103d85071102000e002081c090282c0e0700400c040c070307031880c0e00700c80302c0c50f5505640f6484c2c4982c42c000c00300400c00c040042c0303c2c041a440382d0010340e211013041000703214020254003040740c0c40c400d1340038501c11480c04480400d0140321620340c141c640c00340c0e43c80400e0740d616041c1400d4080d014108143d42000030811125043c080c0d20707450494054001e0780c5241480d401042c1300381c1c8405415803a8820454501c2122511100310710700766810643c442d00c0085c10f0700c41080441e0240c0741e400d5082410204061401000c00e410059007032020784548000c00078145c86450580d03a601540c000c0741c00049042c4003400035140070351520078801005041680c10034804582000c00840f0503001024142d45402c2070003081d00302406030384e40060040300c0082c030400c480c0f607240154038000e1103808100b5444035035000c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 562204109 1250 562202859 562202863
    0x8030411060307030c032418020705062409010b12091204080307020405180c010c060204050d082511060915070501050f07050306030304270e0f010c0c02030705010c0302 74
    0x1444035000d00040d07164030b801078014008103c90b0198a01081c10404010300d6251a004603107804400c881f03240300300c1401c1c0705010300d148100c0003144100c00d90801a0b02d000c81d01c00c0011794030070321030000d881070b000542d03600c900c000d40c2c09990b0f414000d41c42c01d0014070500c44001e082c0c403c081646110021140c1d1419425031415509004990921100203404501c0c840080020000e1a000352170903c230700c1d00c1d415090303140c0c0c001002c200c40280d08a2042c400351036104011000100c1d002d07110150030a03441e280007502c4800784100817035424600041c00081c103610540c0d8801044010034100c0544c410395103405021141030b499031485500300007030750191a96601901c14130012156005d586a5060f0f00d001802081c0541c0e070941c140300c01c00001102c00b84104c0449100300f4016000e141403620b00203d1040c3c14030403054041005080200b0012400a60710442031400000c10062031115000d0712418211005c00c49400c04028052001ea005610001040c4003114428a0240b9061100d41000c0b4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 562205359 1250 562204109 562204133
    0x6170129010c3e0d031103070605190e0d090b0a2a05070e040f060207110907020601170307030c021302070819090b0a022a0a06020615010c03020a080304 67
    0x2002c00015012a8030708404110b010700c25401107494607481e40c1001d466240000021070740c025403000c2000c20300b1300080c1c45a480c220720740c0da40380104c0703007420000e03a82d0005441d800c68180d40801c0d40b000b1400c8140e00d0a0007a00070100500014010114017020010001c80c0c0074001c41d141c1e01c400045294019204000101910300200310013004003007a14815001d0443c584400e0b112803168035004104003802e01403541c021a84044220041621035aa80001e5008a403094441601c2c03508800703000c0e111542c1042c881c4003640d000d055030b5810441036a0300c0d8450f400e1809003990003404288000781d0004821203545404440e2824150310849021010b445080c4000b0312126021440600000900e451040b445500340c032805481501c401d02460b043c09002041401039101c003e40d800c0d002c1c0d00d8040107078002c0803240da203a00d82582d40046821011594410401a448101088031417018412113805032042468840029138807503c0081d942c844e4010041c05030f07840007000c201005550340b100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 562206609 1250 562205359 562205363
    0xa080f0601091d0a06171005040c090c111b130504081b1f0b0112090f02280b03040b0403140715050f1506030705070201020c040203090106170129010c 66
    0x30103c211041d54800c02c0ca15803c0d10655062800d080c00440c401c08068420f2a9102c81180100000803400715040040c000c0680300b550507000d440c0000c140e5400901500160b4030458440d01e140f0406000003070325091102c00d01020300520201101015900d41404040c0a2464030003c60f00392601d04000200d446419903400b401915080f20040000012500017018084d5004654039080685021801c0c1d17000c4200d001d0000c4e01042d10b0b109010b0959016807031180c014030f0018544035680d130100705407001e600049403143c51030b0004124400d2583e9038040140100448050660030140d0320313460140c0d0050002001c0c00304040204415428000641e00b4864103d0510140d200c1600c00b02c100401060b0b606402400b100400140b0b00c01801031902c04c483e4000d03004901c3c50355011021246c0d034008110880c1140100c0303d00c0241ca99890001c0d5020700615000020560b00d00035141c0da81c1400401c041ca40d5034140b10183e041c0d901c0d6004804c030840740401803404015a40c00c0100c40141040380c1c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 562207859 1250 562206609 562206629
    0x80613030909051302010221070312090209040606050a0f0e0f0714040b070b01060e03150a0b09010e220302060f04170a080f090c03190c0b0703050706110a080f060109 73
    0x42294101c407132080b04a04034000c0e0290f43d45448018540d8541440e00d4a0030112508100881c0c00000e20852040c00400c48600f00000c0500c80356000400030318045e1025150303191903403000d00540c9080c1d9810317401048050640e20f00c035482d000010b505160010903005001d488000020411801036860965a50000706490760f0b0750b44808040c2029084481f0507a0486000c0001050a501860a12200300e800a0041164240081080d0602c5400511041d40c2548074030310304004d5180d12180c02d01820400345940c0e141c3c503109507501000440c0000484a0580f8001b85a020039004104150020080c2c102e10026640d00e080884e581200419000070143d400282066859031281d035040c01403050161003c1c2c6500d8500c4603640d20001c0900e41649500011402040381603801400780e0780502c50420f082000d0f17035070340110300141c01810b01034000c00d0001980d0780800096125080000c6c41d620402403c149410170010910240184180d4001a450b404110142e01072aa900024103825903 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 562209109 1250 562207859 562207861
    0x2402070c0305012901120c0203040512010b100509062d030f0411090709060e0316080d0206011e120201030e030412030e03010507050906031005060723060108061303090905 75
    0x1400900801c101035000c43c100d40f9005060f01012080d03041c028444405035038141c0714041b4a407442c001451281061425844200310010b05030300e94102d941c50b0304000400018000603004248407100b8805204101005000c002c000c4265a0701030030340e03500c0140c0c0c035240f131800c5128001a50581d40d0003e940340121001004100c0c0e00e10301003882c20322643c4a0500c080d0703110089018401e0380b46003a20040003040442c0070900c0010710a108001016100408861510030110f900f425a190190803107030351500010001400190100b10182c0144012031941c00c1310b4079a01071400e8114518010500720700115420002907a10030b81050311107110b05800e0307955540c1c1d10040462694070f25a02180400c4090050114614040c407806105032040d8407450b2408010a00b0008568802081003200b9181b526000c0340710344401c0054860144103464203134400d03164249002c02c6841c4023f103040705601020060140c40c0c0c000c0340761500211130060b612149441c514041d122610250090340d00245440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 562210359 1250 562209109 562209113
    0x9090204061e11122101033909150803090a090207030329100201020c060f0408120f2212050a030b09100603050601020a21030603080c07060f0c2402070c03 68
    0x2400600042502211700c44034000c031003840a58641d400d100107065071020b401c1d801c05d0699001001904205541070720401e4102c0d2141881c8060540d80000d8420756446140b2030940441403054005004014000e43c14100501c0000d41000c0542c041c000e2132580102d812020103000e13404c41c100145901c444001904a4080203841c08000c10281d80d100e800d01c41440e0350240d00601c212104050741e9401b0f00456903520344c00c0044890094000c4540450070000316160481141441c2d00030030342031984940a06004000c01031551101d40050404c802c20840c07000042c9203418001010078160038050f813a801509001d8000344006d030351880e00880c29008200c07180d90f0403d180702c10355000c2d41b0104407075180c000049940f06072851008000382d0b51446034596250300240300f034420503910301d800300b034017510781c0d45007681e9410141081d46940d201880c180052a000300c0d40c045801f8462070180700124007511038500d4419100304044c6280320004030100348007408e17011101318942150160721000d56038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 562211609 1250 562210359 562210393
    0xf13082701090504060303050403080f04052d01090506070b060f0d060e060a110f0c010f14100e09070b030a0204080106030302070306110f220302150a09090204061e11 73
    0xc803641600003080740300045280e00c0c0500c5001300707407a011b42d9010700b01415a13890f800c00380d000c101c44d403c00003024000040c0998910285000c01e0b9000c5024200c111502240905041e030420803060600c00c030b0840c14000d6450b84019111502e40013035138001d85440c4ca4001c035440034003601720182c100040552100500c22103800a003807418109007101c076640d495004030790888078101001c2c400040b00304601440c40304600084c05005c400200006408a94404410b0131102d84550040c030f000701100030450801401044680288011b00710980c4a1500d5090143c4929550240340a80361000c40856180915136050742c0190554200801c030013922814040e684202c20303c021550281442d140c0100d6214800598016242040c1c10a04140074080080d6070031408800e0341ca4605584040007026030b0381c2070b07150348070000d121003200e9230352003299002400340c0a941c2140d01d5007401000100290303540200300c0d889005405042c1d80c40030711042c200725402c144841c1c07000030074403c01e0221980c9502c9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 562212859 1250 562211609 562211677
    0x3062e050a08090a020a2306030112050609061618030c08010b03190b06090601110a03050a030c030b0307060f1e02070501090503210d090204020c0a1a0f1308 69
    0x2c1d1a02d146590b152840d0a41e42e10500704020b4000f03d580408206420150074071045941c1408010341c1e0326140c071070114000703410981c008541041600c925200b8400180034907a0421880b5005d890700340b80c0701342c0c000b0101405d0b4014408010078001010504c0d00c0ba101440d0107598013540a000140d5074010290181104a0030148240501c2c0d400107800034086e04411480380d800f03400c5410550b42e5200f00003089a0042c5150f041c0540400c240040c02824010001034600c40d448664070780081003401412241161180b200380b6140c1200c006080d40e0004103141110b59074030703045400c1e1111719011100f4010f510780d61041c0300c28640c41d80d00419004034071034080d58008c1c1d079910b030366036500c03010550f46515121240208514400c403002d421300007035000300b804400c1e842d00898428116800300c9c04a82c0152007000b01d0b9003149580300b040003815009650301c0c051074007907078005041c00388041c40c00490190007000103502100400c0c080061040c140c80c014102035489405602250b84181c8401203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 562214109 1250 562212859 562212877
    0x90807050303091c020a03080a0b04020a0c290406090201110d02010b0f0d0809040e030c070e0a050a02251b030b1e1306090212070f03051006060503062e05 68
    0x41c4900382030360700000004c02500111a03500800705076040da1410f40d003500300642220040c0c0d443c1c01034102c040c1c6581c0001c025584040d500d4a081e204103080003281c0aa03590103800c224090001c03001014101b80418581058200c0e41c0014220301030f20068070318107419059500c0c0d60007000c1c0305410041e010b500002e40d803001521132014040b1b90804010600d40d0000f0010200b40050140405905256010400041030380081320300e40025000303064039007031a035480003000b80300b408100034514130b19002e0950001d04a00c029414030025049420681d18208a40d072103042205045001f84500703007800e46458045030761480442c42d10790400070b0340e0b910200c0f1460b244005c0c0d844448910300588010364450004426013410b01125540c40501810802e00f00342da01c0a1810340c4820281d13424480c60700142340410f0110742c2c941c07540c505503040c100103900006605290440421020340c008040302d501402c116002c03002c08200f0380c1250f8403000c410101180c8040c81150f4689042c0d00200200f480603 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 562215359 1250 562214109 562214113
    0x90209010e041e151e021c1104080c092e140906010f0e03071508040203100b011d031c0e0310060305030406030e0f030f041a0901080103080d09080705030309 69
    0x3003c0741000111100c00180100220400807a202541e1360941c0125456482004448220f80103503280d503041c2e82000c4040801c12490000b00c04a40c1958418100403413544a042410030349001301d03003916101d4803100140510003120000b005280071050825401481018045072140d030603640e184102e407140180307500c0c000340d40300e800000e24040381e41500c50f5034165281003141c045610102d079656021200356801d4490700710b0100700800c01410710b948180882d0707560a010316160040500d02041100c588580c3c500e450864481030340e104020b00001140703102c00c100403500100101c0c0c6030500d05d80f02c0c400705007181181100055804103c0415401c0708504440c0400d48044c074080466103a8440200346500030882082414001e0304031400f454459010784d01071540b8116501d05640c009800003e5442c000a01403101e9010640c100e01c04404c003080d0241003002840c00a410301906001c042c015060106017040c20401c80d810201c01258813080d4251070765018601559070750800d9034289000c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 562216609 1250 562215359 562215383
    0x1f090f0c0801060518130902120c0315010f2c04060f0b03010608070e0c0c06011710020c10090501060503030f031501020105070f050a02011404050303040b091b060d090209010e04 78
    0x400c2c0316000343d038889840340c0c2104003456004003c02544040746c681c40c80b082034a400c0e150015966006400710064900c0e4050401c1c26000c40405080c10884440380e84c48004140c0180040c5130b410007100207451001c51a078010754404807044030004c3c50854540101c8034a00c0c00c00041040c2a044804540d0101d0420300c00003180004150a891441c041d2a80c2d541c42218200151030b48041060b400c1086140c0040c41c040d2180011814a14245c00142ea0400c0b82c042008291804002e40501d00341280000c5003002d0003e080c10751a001c00300c0d81c1402487d1240810002c2c0300003035100b4802844001c044a64542e640d141132100703504111015580da05a230206141554010302400d40710307449a07580d03082c030340070104000c2c0d526401225540045642c3d032110100d903840880da1a5006500443c010342d10ba20b0a03182030a02c4200050460486400c10041d41c45001310341c0030b51030a807802c220340860319040c6550800008280c0782c0ca01a51000f01070000196403803400b212580154000d00d0001c01d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 562217859 1250 562216609 562216619
    0x30e090105040e2d011d0f0109020f120f06071107120308010b0d0e100f0f060b0306010c1a130b0a09020603130302030c06040b06010e01090e1f090f0c0801 68
    0xc0703814406030f10071181c00c01c0d140882891310000400b0380c0c20038030720016803104e011880b80508507600c000ca001d130704205a00344500c05200400c844446007a00d60000c3c0910892540400d028040700600c603405100083c1d10202100e8081c40a000d41084040c110390103880e00050062500c8441030035018103000d501f038085002144c624000100d01e070991101c1400b0b07481c01003035405641c09181029003d0740d85a14220202070b05015444540745801c130041600503c5078030308030464964014000d0007501c1c1000401c44041c1040a03264001801d08259074448500c0c10304d900c83e603241c403148049c0c0c0c11185081101c84484060307000c40c3d0354020100b4a030640c1d50301c5a400d0880e00c1c0c035403029521207420b00006825080c160a520704051013407041c1da041001c800c43c06441c0c071409550480e00f600c855420005156442141c00301c5030fa009183c084106440c00215996441c40030304218860a0300443d84665125443c000e5001400c00b403804221300c0411034000f000600d40d440869000912076000010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 562219109 1250 562217859 562217861
    0x10c0e010e06070c060f0c0501020c01050403030501050306060d200301150821090f400207020f063403030507090503030d0c120f14160c030e01050f030103030e09010504 74
    0x42c5181c0c1c882540980c4d6400c1603c180c1385000e41d5103040013007100c00309030314000560a001511103203241100103c0d090a0501e00901582d00c16000a030003544000c00b0001c1c1740d9505030944030b04940100d02200203042504a003501c522102c0a080c0c0c140d800c03c9103042008a4006030941190a5041561409049000c503884108003030591192211002d002542092800c01c0c0300c0b1014100040c201500d20200801040c4005003407403401100340c189804580c1c00c1c80581d20389106448010500b1450f0140c181e002850412280001a02078031000c20f034849448900d910500703c0c0703004a80c00145280e80980510794085a46400b01c5c002400c2c00f01144141e802419908191000240a1410036421404105c020910f500210003001044035030b500b8041c07118810521000d220090124944440c0d80c1601c12400c000351000d0250345030000120a03442d8801c4110b14403e0381480c0100041007003070300407181801502d540400c0290004000010507411103140300d0020303000e4840b01e40d203070f81c1d400c1004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 562220359 1250 562219109 562219117
    0x4170a0b18061b1b0624100815030a1211070312030c021507030c0206060901060c120302040e10030308250f2a05100b06121503010c0e010e06 62
    0x303540c0780d2004011600814168003003d5401032102e109600300b03d030803501c01800412071080601940c124006028094a250080013610f0b48106006210440703440085010504410300401c2008011740c046842c501c00c00da80028284001000c0f14000c00150400101041d100f80c0450081954044180b08401011030b4480c1140d4210072100641000707000c040e070150501784400811805400401c00d0128020032602d4040e42c400ea40000700c1640340d440203840d04038041d04c01441089441c0040000541c00303010040f50541c41003400e08180c05041041d0041d025a4000d0351200c4001030070401500403003141c09040341d009585a070000d88490140c10a49564000c40e61042150b581d0841c00c0140118070703060a04034540b81080d428402281381d0086100500c0007410102d5901d03001d28144601042500750b0540c0759401040000b14650004d0510311034045200d80c1c61403c0400920301c10040d4045c001109400b030002d000740303074100030f005080b29500c0701e809000c218012036401c1030381041c1041e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 562221609 1250 562220359 562220401
    0x2070501150914010603020a0e0907020c1005030f0112170706050a050a05041709010908060f071103340b16030e0c0117040c050d08040f0510080f06040204170a0b 71
    0x140c03503a6401d2500c12800b0398408c411080c28001c2000c0004919100c240c2090b10510309940909824a00082000810902100c2001c1084030900c10310504001d190720060450b89002c40c2070880c0c1c401880c2c260301e43c0c810340100343d07106500810804180611a0061480780a60000404c07117682c4001003041250806c2d03a001e0020702d020144540c41b144000014007040c601410481c104640d210a11480d1036822580300414000e00c2c004c0c005456041242e00d07100189407005141006080c030f407085240c54a45240c22a8140303040d40710070043c0c43c40400701d03c000341c000500c0300b254601300d60700380030000d4a1f440c6200001e26040d0021110386011450005800741650f45015052544d5101086c4140180c03056807048121b04000405503103000360740350614800e194054980b4070300064610820b0255010034065640e0003400c812281c8d020800c0b0f42d100c03254036000341468484601040c024015600700403c900105030189034103013000155191842c4c8207100310b104940d2400c50440030030100c0044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 562222859 1250 562221609 562221641
    0x5040f061b02040e012c0c030c1305070e04090809130c05070209062b12050307050d020a110706050909061804140a06020703080403121104090b0d06020705011509 71
    0x1c2005151941141040b83c001c1d1002040d0401d102c0382014140c04100f0340764071180c03103225074044100300500c821200341c0e404030702400e00402c04074041004030b04083c0d0700090320b039503c40000300024020a1b18403c400030103001005079140510b800316281d4441c440c4588030b0003035811103414010490094207400c20654bd6081e003031520503405d00c85404405021280c0c40700c01280d151130000801d10446405103030300340701641c0e029010304004400c142002c0e0800100038081042288140c3c0240403203407600304103880107944003440c83e8204d4001d420700203d12802e00030301d1000544258020007070301c803220040700e030403805495101c01c0141040d10034070541c44420174080003d01140103940305032802c8030740c682901d18801c1c503652884200e82c440b000403400304500b103050005055000705070010350801300008001c880005c0d503070564180149e200356071540d030f1900200c1d101501c070744849890a170746c032031025522204146040d90282c881f550b612100c05400200010303041e2441e0180c220000901d6034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 562224109 1250 562222859 562222907
    0x80906010b091509031617010504050615031501060306080d033303080c03041508151c0609110907090b04140f120d110102072109031205040f06 63
    0x70500070328943c022055041c407031090000b280365031401c1c0302ea4401c414840049055103418000142888044400514400c0c2c1c5810104000500d00248044d040039403200c80d01c0701007010f03a0000b40380c8040f265182640d0301803d030000410301c3d01034001d2003e8a0901d8203660030f203181d9810071801c0381c00c40012520000c0c203400d080140600007403d640040401c0110519140d0380326200d003101684a9030308003000360f00008080010b901d104500e65510691890a0f00d05820494040c1110000c0c00290390b12412066846c40001100883c0c00d0b80c42c140e0141040c09402c03110300300015000000c0b02d034140149800c000040c811485141040156461483d1590500e401e110031600069000c0294a401c40ca41c00a0440d5030f45e140c003040c94a000405000345003074054100004e084d141034102c040c015078010b2281c440001c205a014a9000d644200d80d11102d6040a00c01c4401102ca41c1c4040d00c82507552030a80c1c24154080b0040c41030b82d80350740c280300c1c01e95501c0800b200c075509514019089030007100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 562225359 1250 562224109 562224127
    0x1c020405130209270316030801090b09040b1005040f020d0b150f09030102070c03051f18030806030a08031e010b0f0412020d060203090a23032505070b030403080906010b 74
    0xb003124142044803400b0312000c0213000c2c0000349598404008415603c01d8088003108156116684170b014010180080c85440140720110782d2a03500500000c1400200000082c058a0030340e02840007801c3c000c0c401c3c84803901c003250210003980711044000d4042d00b04002840c513802e1015141581c0000920768518041c034181000d0f059030481d00752268076540802c503170408140200740c0c280166004201412032000178040006071040d856070300000060a1203401d00d0074a0f4803094030010749405050800c100e540e5800000d0604512540042900c03402006101003400d410518407250b40d622140d502041c0d132103040c07084460049010440c0051010001030104e01414108444598030250141c60780c0704540c3c0c1d852050760011100940140d00100d400c1d41400003144151907440390781880503864151121559071288241e04240e400b110340242c3c81202d45010317482032821a6080415030b260036032192141592940191000d40010744424081007045001254a0303040f00c401001841c6080422 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 562226609 1250 562225359 562225381
    0x4060e0618040507030803040303020c0d0e030706030b180f010819050a24060b181c030c03210b09070810060e0109031a09190b04030c111c020405130209 67
    0x2c1c001c44060240a00000c00180040c003d035005510070f850150700d8054110385a45001d080414040401624600c0581d541e00c0204058003554498580490a1070030007004c41c1201d10b1160b0070713181416154042140e00412200c00300d050780c0140f015107a00d04219052400d5919400d00003801070b40021400b480060081c01c00041c0030f58540194440381039404034403a00329506903100c0d2005120005000c003c41c110240c14455201301280c400011000b04a2041c4201e102014001c0a10152a8201003854010483c51070b200100c0b1800a170310505d894000b41c0980405040c250003644c0074004554218019130181e072080c01109414851f0510f4408221008510306551a06002c031140c000f101154003003d0130380351168100302c03080b0381e4180000d80a10740391915040c4204030001c46a014000b0f0303000d401d030541098043c074007490a846241044002c99080401865103c4191802c08076034512400510003140d000700d404000c03e99600903002c00d4000c03032000007540240c3e00d00015040c0750340c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 562227859 1250 562226609 562226611
    0xe12040b0d0b060a09030b070908150702030f0706020a0e0103020c0607200114010315060807150201110a02010b040e010513030302070609060606020a0605070203040e0403200d0e04060e0618 83
    0x5040c00100b610314408012860513401030203042c002411009045c0141f00755445925000282c2e868802001c0340f50a8029455007856581040d0f03003101e0b0404507411902c20030035142100d10400c80240e84940d41e00d4508000c0d445071190b2004546004c5110003158007074403d880c10708461b00c010b8607a554804d03400f2074007030140880b40550b98107240c0d4603c2c0b00740002d2003012040242e00804012a50650404200d0b0300e018040c0303801403130f042c072800f03003c407032030200e00d1000f180c1d44130f0501c280c64911050b0030303809050b503484907a002a2000c034280710103503070542204c001e200c0f050310100030240c461403100b400e940048503142401802d18000600103842607004104081c020240080c07070600710741d034110903901150f1204006921914140c003d1104c51b10030584c014400d0300003146000d24202c903003c07a141000f4000f809000740c3e0b48404941c5103031036140c7c100d046054401d82c1c4e82c0300f4048401030403160307214950501403881c3c410040b41280c06070340428003584000b090350031342d240a00c1402ea80850 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 562229109 1250 562227859 562227877
    0x70809011214090a0209160e09090a0605040308071107030309150c080c030c060c09012307240f060e060918030a03091202160504020a090f08100e12040b 67
    0x141c0c6542c0000c1c8640e41c1c120850142c0811001340c540c80d81d0714010015010780c060941c07202c841e0020f8400300d03034a40042c0103c03034040003524443c20035075032044003038203140d03000c040940078604280400080540c0301d40101e1050f441922010b00e000603103565541e80381c203140401804150304410621000b880c003412417460f1521803912190801c840d40d0b4441c050382002c036040b889c3d0342c000b05000c1c0c0b0b02c44060001d143c0c0200310310646400c100808000915a400b900c2d402c00c0141c0400100c864284013490888403515000b80c0c1440c1c400d44866210081394110717604002c10980360005205200180d401182c0855841c80c810a019032210001c01c27000311009059410000e0f0402d0484030b0601040c406050038000b01e40300040c4200c90760800c031a003509031014074421900080d480e0403180c0340010101d0151001960f005848142042c0d094500c2c0f0b0075a0000e9503400319820000031100b1000581000e03244042070706010740911400b0150351501c40944600d460b070b000340310602c0b01d0078492000d050000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 562230215 1106 562229109 562229111
    0x50c0408240f090c240724060303170901180b0f010b040503100903020c03010e03092e030b0a05130902030606011d09100e0106020703170708090112 65
    0xf01c2e60f0400b40c412528002c2da00e414170807140b1483e5003501000c044503543d41c9903045c9480c0aa150204843c120f01c280005c0c000602c00f03d000300400c90f54961118003020010841300995400d004080038442e40d82c0c0d501a41c0040700c641c0000c12002e00540c0d141e091030070908403201d00c07220142c126650305401040104856200000c1d4284d20729826400001c81900f030380741c01c80c1082c0e04550303450342c558281f031003010f954080840201400c4404a607001d440740c0305e4805038807201d050b041d0045407800b016403a0307468803402500711804000c001440f1280280c0c451000503042403202c88160200c41ea59aa404c0460500b0031515400040900f04941121110503110f00200700521006001d444190301062031120301c16041c602070910410050090740c1c485070000e5440351b6512040d50302d000d442c4003030855203200da804c4407401a00301c00850f15003840503005452030312089500e55412 = true := by decide +kernel

theorem cover : BRFrame.Cov 562050359 562230215 := by
  have h0 := BRFrame.cov_init 562050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 562050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 562050359 ≤ n) (h2 : n < 562230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
