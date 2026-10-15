-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4483
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:46:04.818026+00:00
-- url     : https://prove2.me/submissions/a3c4c874-c461-4e84-ad31-17824f366de4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 806115107 ≤ n < 806294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 806116357 1250 806115107 806115113
    0x20a1706030a02311416020613080c070303080615130509071e0e01110a02091f080303090d0e0d02010c080d09080409021306020708030909190203071110020915070c03 73
    0x101c02030303403407050049804d42198941a9038804c0042c40382d4040944948001651680408d5882c0c2c4440e684002d84103a00320f60034603070040c8c00754052042442c400d284022080c0741c6c00203e0310b48144404c540c0c12503000d4030104640b00c00d016841c00102c84019040050010f4548201c103d41d100030a840c0002d64000b03041c05c074042021b2081422004600000502c8140e540e004100405080980000700134008141c1d021840001001700620070210042805106030303540c070003101000b0031421007142d071a814800030311a19242c4080c40400840e41d203600d00d0301c050030905000000030790142c5401400d041c4030f850704400380d4400c085603180700d07542d0060b41c0f0000c2c0020010304054400b0b070340c0058540b20700c040408101210b5400400a541c40a5010480c020000040b50004030301900c500f801c07a01c03104080000742e0300d9103141c8001d5a001108020300641d001c10850000c1c0315130400c6403030140e00822401c0803485103094007604208010354a081c503003040001450400e101d24094585656261 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 806117607 1250 806116357 806116429
    0x1120c0e0c0910080703050106091a0c0c0d200d030806130b060d0906150e04061e0c050304032a06181e05070902030f070f0c0c0603020a1706030a02 65
    0x51a0304020903040c070180940d1740e078548142030252503a0b05050700341e2414440704031001c0841c01d55a076403c0000048240480740280003206a40030042e10302101006079240c046052410901c817404d10400e0f261949a0525102250300c0308142c05407500785807901c5002c240003201d452003a48041c40ca80314401750710503858217002081c1906400b40c0000d207a0784039180c9682a03810b00c10180101e100f014405004800005405d181c0207540b1100000300d4801081c0d44404007840f040310345070414900350302560443c0d000340003548128442e5845d01c2001c10501d1850001c240c000314002e0220340380b03e0310341c000504154090300341803020064040300141c0700d035101d8608003190702283c603c0751502400350302080010030658002d80041031040d800d501c2d00001031961f118004255804101303040300d502c5609802005100c400a8021080701d040d42d4407100082c2c06544104009400202c2c51f40700c0c0b50310142060f03011401828000e0240806200c03680820007240303041900701e40c0c080c452547c0011144100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 806118857 1250 806117607 806117629
    0x7061d0d1407060e0724030513051c09150309060e010501063f0902120303040807030e0f0301110306030f1219110303040507090507080f0c0f0f1204050601120c0e0c09 73
    0xc12031440c6d19400b0f000082c103440020306440f040d07221607e048400914003062200c41001254950320721100711203001c841030b000070f5014030109800710002d03901e80359140e00001e0744540142014009002d80c07204450803900d00344103000005400e20061100030404050b00036101e1308030560890040e8004218400000c03541400c400c11981d030700044e80031420180810400030445d0300c040c1d401d529158036444464030814400408104000040c0841c546c0c40d03514005c002c3c84060000c108106000603c60b609a1058a05074468410041d601c14035203030004110700240d8040c0800c504010740e090302d903082d520100d00b5810903c41d110100b020410010001b66110b02c0c002c9004100b51032412104a044501c060040005c1001c5001004403d0381300ca03400e560498900c5080941da5450000e42012900914030b484e51040400503480411040503a18540201c0c050740030f039000d81c4d07a00d9102280020440704010000b01c80300204000a08501c1c08440e4000810340e04149859191800101c0490342c0e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 806120107 1250 806118857 806118899
    0x100809070501053907080f03120703092f030307080403020d060905060c030a060b03091e011107030c0c0501032009010e1503040309092c010207061d0d1407060e07 71
    0x559090b04e6a40400b004008001c1c1900000f0700075050070b2804290312407081c1c40d004100814101d0102d0907141c880da01c85c0054581000342008070202c0c035001801100001d0003a06100600741d8001900c0b441c020003101c1900f60f02c444464a0300b071456081c02200500400d09071201903440854402240003840740034441c0c42c480300d503280d0305e1401044030b204036141d941041d018601b0a20420240303900000388035400440848008242c45111501b01d8050322640c018400401c002144080405401819081c4030b18860880c0d0402c0b66202c41c0118210303890705034010001c1003018404481440080f005100310807040c94000c0070381d00741c54049200b11840ca181c4100d0000e00004000606a22a010740c0151080c02c10a102034601020140d19010380d0412501410460b114400e07540034007581166005684100c00f0700401308024003021020300404590350403070280001d40d524942c483e080041e10f8085020405041c040340303442c0c0c07400503c1054000b00d158840c1480c0891790100e0070650880d2088 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 806121357 1250 806120107 806120197
    0x905031f1d011b121512020409051903021009080a0c05101a010305090106060806060f09090705040e0709120b0c0c011407090503071d0910020406030204030210080907050105 76
    0x180f00400113105030107504422480c10320b0041200321071078076400340c04101c0e40305001d03186040c5050f000060040054000c010500c0c441c00314901e441c080179404e0442018001d40980380c00220b42241682564203446004060100c100400e02600e80210705503080c0034091000c035148003202e4040101118508034100c104681c6890311650f456a147c01040e0340024120001d00c106480c0c00c00c040c1400c0c01c0545010711508010501d440510b1a0134140e841c13503040248002c0f02c505040c1c901134115400343c0141d803d22507841c03000521440c0164145002c8416102c2c02081d26030310754880b904860400b40100866100801031b0f6044007030240038880c00950401c0915285041c940800380088186501c1a0301036005114108110043c210003c0300d500040000680c44d03a07940598a0300700400100c0c0342201610210300130a110341d143e4050010350307100361040d4412455100c6c00751524442191169540d80c001c0d90180401d5114401400f44411041c0d0030a44005d00c0301103a00c0c040041c64160b03420341c2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 806122607 1250 806121357 806121401
    0xd050c071509032109140d020d12090806010e0403051b1b030c01030e15040201091502100c2f0115090509010515010f0c0519050303070905031f1d01 65
    0x400d100345041840d12504071044101e031302100281035a4100c0c464041c0340c0c100340811100e0380e25464100a83c20703034002d0209500d1091843c006d50005004007040c00010b66620b40464510b81c00260749069511010320300c20595a5070b80c0444880e80000307001d855040000c1d41404040d00c00704018140c0c1452501420030300308444003450715000604050604050501409204651000ca94200c1030b00ca014a500e01d00d54950006940c52036a03507200c5000c8410b00f00c11b070300c0c06560200d1000f0b11042c0c5018203200b00d0608140449662101c00e0360301c007450600c0e0b807000e44c4407909000d03143d150004510000c9203111800b54607061007445907008a80d9962200c040200d810b000b031280650041400d0300f4a507148804100082801801c03030300e80005d0048080041040c86001c2190151660035088040c0203180217182072070304c82c5c1095800401181034000003060624011035046000140c80a030704040380e071402601c001030603080c0c1000c0e452011810300512865404c7c01140448880c000e1031000c07803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 806123857 1250 806122607 806122613
    0x70f0602011a040b0604060804170c0607030c0c0c0b07060e0709020c010e1b130e010c030608011407020303071b14031306140f090424060e010306080d050c07150903 72
    0x140b803500d9411481a850610907a40541c0c2e007006030b80544070703d49002d000e00d03603a92070132801210603100146011000480d102140100000e1054440d24031580c00b40300508902c4016a00e040c1c0100c0b00529025241c4014014a40d2020282c0b541902404c400300b1090501854107007402d1803500001d0b1829000a601c100c840000d000d02c034808840b11000300840411868a4000c0071050b020951280d0b080400041c01905580c02c8003402d1070201c4020132001041c4040500100307154465451954288003540c12442c040340c081901c51041900994075540d181e03030040718101c8084880d1260041c4a464001c01301d209c0002c41a420340c00c0310015660784566a030304041403002036000004200d03c111000d001681c00c94152a855a04004495103a0707503400000380107001c20884422008124070280c201803c50000240304443c0c0e00d48420000c2248a00110290f554900982130241c1c4503044180f0702c0e912610082a0108000c13041d20340280c2c0b9000612611342016560340009a40000c0078824 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 806125107 1250 806123857 806123891
    0x1506060e0a06080906011412010606030504150c0c02060d15030b09010605030a050d0813021305010611010c0804021207051009050108010906030f021005041a12150d1103070f060201 79
    0x42c011030b040c1001c02d468414125682c031034050103000304401150440160b2612025041e140024140000344182d42d15200020300901c400c680642c1c00715440c2c0049101c0407580d01c600e5144060b81d9461a10b114115002e1081319032012038102c0006549001c000049854015644050f511482c01503186040484555003511015040548260000012540010030000f0401855035541c207085035140d072802c03080036500484520207900840c0030103540c0503014171035121605071349075501c485a43c01035105089088071441d00c100d03400300354088046400f40ca050350368251079108a2040340c2c0d05030703110400310b0420007803817811002064091805210075078222f414107001d802c40103000c0001a00c0c0d130b00c0d40701e03225405240103401451140280d2403400e06c81d0b8100c1e8080c100080e8541d060944100700d0300d40c80e07482060501880b1480c0008186190031095590206920051018101c00365685460b00441d034011142ca603d0301c01e80d40c0014070b041c810400c41006000c17503000000c59291001340190 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 806126357 1250 806125107 806125109
    0x6021e1006030f020f0a050307030f08040b041206062705040c1a12010e13031b2001020106090b0a06050a05070c0e180a03090b071406270102090f06071506060e0a 71
    0xf10842c2d120401f440701d41c0f0000703054000c803508526242c50800081c2045c100030311840e0000340d40460300050206101d5644080c1c02c044c01d100b00e0040001c41d940d000f2081480320b80350141500c0c002071615441b00e103a86600035036041802808102c1d8003659070405150315000101008210210115140e50080340200b0b08a0041c80801c40309080c900d41444a40c012241c41e0a000b4240108441c107170314170003c208004441d0a074410b680002400b4094455528010101045070041d0b092550200760010980980090303a100506a1621103042440a840a40004102c4e004014041c4840c0022400c02b00f0044004c2c03049104003600e5040a05400d00070042e05601000c0701ea110140c03100c002039100f41c0f08000c40b0741c0410401d4a400662a2640c14004030300380d0100c0d0740c8640c605000040b1803803e00051009000104030345154400c0300d100d4240d004081c505940050302080b8425542001001040910b1045050004845210888200703c680c550012030000b01070201400c41070408a4100d4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 806127607 1250 806126357 806126359
    0xe07060905090a05090c10021f060803070f020315151c210c05010204030b090c03070308030402060a120207031e0e03071206060e0112020f010906021e1006030f020f 72
    0x20602030070000800c28140b400340c682001c02c0e80c1c2c3d00c00104640424400e000703240c1c1000b00310640a12070807000960350008c45401804405518020351044ca81c0742c400e0804859016028504242017500d40c07001c6403550b141d02381d81500030b4001082a035580603034110f208001c90000c41c0f0700f0800796000d021a206100d020030442c80d100c45500c40104920f402c12425000860304559074a12030514104d828000d8814020950340c004207011041110881c03019108070010002c803144071206908140d80d4820300e1001918915040000ca07016040c40c000501e2460701070704050b840016070b07001c00b0040364880384095002400900c01c000c05041031031040d82000e4480d1402d49014181d040c0040d89035481d40c400c02039401080100c2604100150300311000920140c40452010340e03598108007048110703060300701d00c11010404407008a600403540c070001d450803940100700c21180c404c00d100701d188034040c000d06144121206111000450700440c0003552160100c245185d400b403040c407500d442804000e03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 806128857 1250 806127607 806127617
    0xc0307030f082827030203030610021c0e06210403080604051e040f1202070e010e01060e011b021905130c0c082110060810051011011e0e0706 62
    0x641d0400e80b49115074500070324410000350583d48510a0001c1c400d1200d98244c10100c80790188107140c0c000c0041e40c4640b0080c1c544402d410040301302243c5480300c003c1d01c80048120028400311030f502c5144c614148040260100c3d1601f141280c030280d22194056000e250f01420104100426030301801403a0814004d44090107035041c20f006402d00e800603400000ca0030b8050400003401d00511554140350b07507030800015480ea140440380251120100c4c080c210704420702000000f440003040c0314560403182150356468001c42c01000455100c24441c511841140550690bc009666500c07040031100b403030b124000f240d003840c15007800700654103d50402e103410701d07041c120345040d038028616250580d40441d200d90b4a011415002007052124079407905490141420030100039408142c12003076030000e40b25801540e60340400c103c03640e001da01400303030051560800106100e00401c480e203104110b000c00411800315100c0b110703040c0c50000c41211241d940342c50341e07c1481441400322402800c280e1500e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 806130107 1250 806128857 806128891
    0x90803070c080f060c0904110d05010e100e07050702010c02011206080d0e01050418052205060f0c071a06060d1119050f0a18080609011a03010c120c050c0307030f08 72
    0xd4800381c0c05685202e90145031079442c141d1602c0c2c1c8c1d680850b18207501c0d1501c200b2403540c59030305004580c40d084807402d03031040c551140070594610910002e481b031811395880a1a02501c0d900450320b851b1603103002c905109000c10858409899409010040d000701c0e401000f0a02103120010a00311411020905001c407c000602000a984d6940c2000000302d100204098499080009206000c0c9801c40807030000200e51008000c0003040f40c034019654807030303101c07850745445407000001d11982c0c000410795410301a5101001040031030343e9a01c1a001025a4106142001004240e40d2400403105170041d0001d1044000108102a0b09051005151041c1070040d01c2240c80840c0c82804c0c10041030040d03581d15506a00307a40f40d58040580309041c160380b0a030401b02c0396580a810514520300e820140c442507140a0b040510038240a4522079807003a42c00c00400319803e00400605516004005041240c04451801007009200141c4256205034001880001c002c018110140ca41e41003210150030b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 806131357 1250 806130107 806130121
    0x11120a050115050a030602090d080c0f15060607061d070806100e010b0409022a01020307031b0e060306030109020405130b010807061d0a2117040b03070f090803070c080f06 75
    0x90f462080c1c1b64013040050f56800c1210015a2100e1681c100410b20000000c3c449c05041e00450602d07004420102158516414005000d001c840d0480d201500301c1c801b40503002c08a0b0240e001440070b80c000500306e2440c4020300507241d003070400d00e401c001c805a1040041c80404046c51303500a0051040401c914515410504e0790443c3c0e1041e4404e0108094009c24116074499800501e13a0500000c40703100140410f42200140c040e40084400001103444c02c03c7d010b400d030300e54200000c1c1004542d500d624a0020ba00c080004075000a4101c42d00356507903a0350540180c40d2032140e41e006140d28480c7c180b8407807440c5058910000140c0251010b41c00c101003c0000d2130700000032060706440b200902d40c100c10800041003c4844a502803004103c2c0d40703040480131030101c1c002c0111140940644840d00011032002c030f071540302d00c3c400d102e481c48003000040c6e00d807481682c0783c038054040d0349400004179903543c01961440d0820b04081d295141e030400e040040309802c118001119440002a03c86458090 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 806132607 1250 806131357 806131369
    0x212030903090909030d1a120c010e0103021c0e0a02091e060f0d0b070801051203030402210f0a030e0117070f08070e030a0c06030b06070c05040911120a05011505 71
    0x740424003030f90048000c0341d9180420300c20b075110312524484c2017046c01c150002c18010344410364101401401000d4503143c0c41d00c408a11000400c01c1a10740120280540004500a6000314400d8244202010103417030305010034011005820209030090072070480b180100045d40401400c00342010300410071000c50140e00c0070242d40d1154040303514104907a0340502046014203203140007440070011004002e050303a0403000e00e5050b540203540350140d41800c0b59040da0baa10090350040d510560108209540da04004150745c0d505000382e09450708a002003082a01c0c0540f91042280411034007412000d02c0e507400300201c9c80780c1c00d1400b41c0c0005400c103048003604580344441641c04028202000640050041a20992001020f01124181d4030f9074201500741c5241e900402d400a03051140c00c43c0d46141030010340e2020b81d000014001001c3c601400c2100a00901c0001c80d40d814601412001913611a4110102004250003510380074800349080c40c210b070401e114196010500c41024051601c0711 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 806133857 1250 806132607 806132617
    0x3181115120c18090412022109090408070c03121805060304020d0201111219020d120b030a08030717011a090108041e083f04170414010212030903 64
    0x1101c0b456910701c4018110703210012110101508110709030705000402075114030041500755182d080d21154029200b003450807087c005005103840c2d0041c844400140f0f40002001c0d08907105804181c40c10340305603281013072602e55a1060b220b030b0003010000c0c9107064102140d00d40380805803155045003400c010000d1044e000290019000c0c0c40b40120480840e400b50810300036146a40e41103403080d10201c550003645903c9011409645469690407454030380c000940c0307684006447c3c0b50711038080350106060004294080c026541407140c50000e4001c900302c40003d501a5500b0754800e8402002180a640180c2060b0300403006503801a031024039008100c025550581d0382481c020107a5202c6080200021a00c944400011051084a1401c108520004005000c2018520b020314606c00000c0c440c407420003010140d04410b140d040085d8107985a1002e54451712a40010080c401701141d04440c44d00150005075103101c0e11405541650b030100700501d940320500001c1b91451400c540c13156101c0c041c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 806135107 1250 806133857 806133871
    0x411120a11030c0406020c0301060e3405030601021618111908041b08030d0c120c05040501180b041e120f030f0c0c0b0a0318111512 58
    0x500408a06101819000791405845408881d0b45a00740300c00c00b81190341c00351141c07201601c65001410001c0c103042c0a114110780c0c0080b110070fa81c1d643c8a4090540ac0d892440c40510f031144d2443d540c01c448041800c11003010102d960760303504c0b45080341c00a480c08000c13500041c02c404034214100500b001040c00003a020350b0a840c00b00d00806005c1031030110303001e54800c4020400a400300303c000f2981c42904140300e14090800801d100e002c3c2a2030015010381402512179982007000940302c4088a40c2001100d403119103881c2400c1034800f0301040071130b5600c1000c900016000107042080d50b910100260110241d034810f60500d0340f030000020110f108501c0341c0310001c001009000010140b1208680041140589550002d0440c1c0340034100024020070403000300c1c0001c1e034590718080c411026001429841044c08540e00e090000d41290360700240700807410503884210072040f00c09c00300c0c40303a012188203006202c0c0c444800410840928908021a68145406d03c100062200d09404490300144 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 806136357 1250 806135107 806135137
    0x1005152707030209010302250c0e07050906071109070c020325051026010815090d03050405011e1401051c0803060307260f24092e0b0411 60
    0x284c0c413001a0301030f00801c0c176104040142c4078642c0e12510300c03c1e04041e0006203c1da0404d034065803522220181b810303085d910840015810303c03500050703042810007040450b0007651122211000e0100103644200111440d1001902d44004c40045040812003014400018410503100e0400003024500ea01681d01c100c0348902100c8a01c0180640942a50380c8404003001c444001c5214008080700160402c2c400c201c55440b0318035914800c8115068120f00840c48200500460964402c0031405003c0181083d51195661045030007400000320260420f07804d0014049101407500300d07201c0e140358059008900484a07100171250564110400c15006035100164075100e4603a41c0201c0c0c501481a000080600b0390801114020841e009a0748182007600d8204c888114404800c2600c501200c0500e41c031032100c0d02d01c410440038419100c281d0001b0080c08a40f929095481580c119100e000d201132132161400d82000c11080560180600d00802074800b40804040d0032031101161254486100ca500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 806137607 1250 806136357 806136367
    0x30415050a0e0f032b023708070801170c090112030206130201020606011112070c0e090a211403070f090f05090a0f09020d1203180b040204050910051527070302 70
    0x1100e6060701c5610040848240c55400d461780701e1021000000c1c1001c80000c10600300e4605288203107106840327076240c2d66521080382d10f00150544080505c83d5412114055056a208291610810503008107002e140600408403030f4180603080445c06009450011f420f411518050b0b600060140e030060420700e000c4114482140e4118181010303075007030744400e02c00000c81009200c1d11101d0781c400d954554800c3d042c0354882090040c5c3ea48003100000b011043c0140040300046217003208200391041d10b08041911140d04d040c102460340c03045544a0108498050000c403280d0b20002a2000d80140185c0ca0949814280040d00c038440040a0043e6241c6904494a14076101d410044501c0d5000e80039115140c040e14000c0c4407107044003000c1000902d405420b040468a0003543c00410780c00c01405655500ca03078080c400981801094415140300714248440ca000032031203040d1095001c1a000c0c80081c81c6417041200310b2030111a881170391450304c0100101292001c124070b40041039030800503522 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 806138857 1250 806137607 806137687
    0x30b0702031e030105010f0206060d060b041104240504061e091715130c0b0c010b1804060c0c02060a0e130c0e0301230c030415050a0e0f03 61
    0x140c03250919010000c01c422141001040325400030311305850003600d4050246003000301c22a40c1d00e5003201d6050f48400424901008a00705034827800380c10740081c0c03000ca40030304c525040300c403581e115034018610410340e8101012050070f450452036001485240c0701e0710305454400c0081c00e548010071041c080c80c105031100301d5003500840404009180440b04d1f1440f148580072503d4461980c5c000c50035910084100050ba00b1118900340716403154006885684241090120341c0c554026250327a01040d9a2014181403960b1a41100d21044210b05100340706880c0615002080d64660120182400404141c4200590320355007600c1c1b550001d8a081ca100c0400b4000040018800102e80600545041005800c8940c0311490140f400010342c024400303502e1175891920b954003103102036a20402d172600030620742c00003030f0011900a40607250201118007d00d80d10000c9480c00e40326684000e5551180d000000c0040c4034101c401c000070f4015608101030501a094209201c0c55031900b1080301251050b00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 806140107 1250 806138857 806138863
    0x7030b0a1b020c090a1104031b260c03031c0c02070b1b0106050a24180603051f050306011401140309150f01060f0c290a0608030301030c030b0702 64
    0x1640c038084030300c01e040a030320200a512000d8101c282e034040d51010f000120a214240182854001010f0341e42d0b1811f40b440d21902d44110038800812401006a8000075241500e00038000c4803200504000c410007801424203480d111004541d140079800500071121095002c1403601b03156a0080d501003403009202d2022418140660411144420042070903149030036040440b2032204481d9008000c1d160302e5100701f00301d00130b5900c81d207414141c90340d518500707a4158854040302c1381140d040c2411145021035040d0210712954200b0700009a480c0c0411190741d074103411180c00c01d81c1d0032090421090900011984840f01400386a50744074203a07001102c564802c03021126113086440100d51a41440d043e415241c200704658200001900000b007140c04c2c102c10010b034101c5210b43c440f4034668540080c10303150500c40c510143c070104e25060780ea5039400400407595640003641401c0b04000d142c40d803510340c100c480310380101d070165205100600004000e54010400e40350010340954160391040d0302245 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 806141357 1250 806140107 806140121
    0x105010e131d07050607050a08160804032009090d08090a0c0e100503030a02061b04081b011101060b03010b07170a080a0b2d04021902030301080c011107030b0a 70
    0x2441c54a05020b4004030324040c000c0480d51440c1d20103480d1003640d41c034100411806002c0d0064410380110268100241060f4020502c0c8503210f1788070403031522252a034109035081a8400d9950111903030710040060340c0314105402e910800c4032034506078200360703c905585400f1517001e04280414940492110441044200c03c0540c0c45003c1045041d01e5001d010080442901e05030b544102e5a0b001081070b1030b0103c141d03440080140d005210a5491010300e0154a1049000003039000b01003101082c9c0040034814800d42220041003486a905000001800e002c02808104802e0749400814401c11807080101c030304403003100c000d90341c0346d030b106040c654100a00d00d001e81c2004000083c00c1c461168020006500c2403101540c1084030303000002c140020282a21084142e03c07610701c480940c402d0120072003900041018000605000c244403010f2010604511000d001d03910220042215110400602d00f1504003840c00b06c6482c0c0c49090121b55620481c04020642640c076000079105032000c2d40460 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 806142607 1250 806141357 806141389
    0x801150e01031a0a060e0307050d0b0a0902060702090c0723031b07260106060e0d3306030c0f1a0703110a0f061503020306060f0a050d0317090d080105010e 68
    0x20304226502e19010746101c1c4071b100058064000c9600018181c47d000380c070f100708207402c001c0e03c0074195546040c8600400c10048101c0e44020f0501048000d61107031600c0c0da03c10107210410594500e114203100c0481100d590010140c80b0140721681895007010054881e032403020200011803080416680d410000203800c000301c0600d20f01c0f49a60f03854000303002a841004980300030040142c99000440c0d01004101d8101c2e00700700c0d4664400c6c00640380c0c3c0141800e0541c0700418405017031030b01c81c0c49000080c3d0041e10800c61910f8507420700502c100d05291100034007031603c081f08400c2c50841c45031420306214513120788800740894840281401040303030011a00040050311607a00c454a08500f40150602c1c0c00d03034459191100040542062113200000d4a80060081c03916a0b65501002084035644440541240c0c0308080016281c881c48050740070640701c0e481f201d410610040013041401e41c0241668925404024102801c503000040241074a0702803901041440043c0080b0b1801c090841640e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 806143857 1250 806142607 806142619
    0x1b0203030a08010e0703020313120c020a08010c0207050303160b040f141b060a1d010c0204110c060f041124030f060a0609061d030c0a080c010801150e01031a 69
    0x11041d50354041042416600d552544141d117880700d00c4220104d010031103800581c141d289612901090890035071141d440c0c400e151032030006199501103601c58010b50b100c01c400369101d40000325050740510001010b8035080d00110709280300007004d8a0306010500000d0700c0031100e840820184110000404c07a01c0350004400c000d010054106990345180b0020501030408001e41d1040c95882c0220483c0c91511007640d8842c1d012000200762003019417480c0c801030602c45070429080c0141c44034042c5070181b4032035152744c9488008503d04607040040050050200044030380030040001d1911022101c2c04038203980201030314843d107029820360b1846c0206101c400402104001c0c0341c118080c0c0907442500141c3c0c43d4a2100d0f0385e40030a40e804400782c0200c070007045500c08103108442800b2034603050392100804640b000080003022400424068100e542c03103420204c4000c8903960803018060050003840083e5400f03820424004188078000c01180781010748a0742c0010340880b481d14440f000110003400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 806145107 1250 806143857 806143867
    0x90d0602030907120804090c080403021e0f0109060f050703020f0304060504111c11030714040203090c10090905090604110118034d150708030a0f0b0f060a1b020303 72
    0x71704881c0d00603104a036682e5040c80300c9001d5052203403010328021076054000702015000516002160042403100d003155202d02d1070244117201007402040c000341e00030540010b064210044490070345000414410500d030040200101070000799080b40d91080c0c0103c3d001407941c4030380c90480300c0b118090035034950003904030f818540400415406014640d2048900f94080752104040c5512403105c0e205030844001100264001414075400944e03106000c04191500d1640c06000141c054100d0003040300041c9001c1c0341881000103511440d50032400d15002000d00e89425601d000c1004050003d2031704201c6d02c10245640c9030342410a010145078840007000e990440c01c20030491483c0304044644c045110140c5840384a804000851310343c0c44404040c1780c1800c070280500c402100011044c069501d410841d41000c502c0b400061405400e42c4070b4046015110040c503102500c5480101c1842100049001d040a5540000301d0f014813090381003540c0500b0709010160303000105c01401031b4044c0000a4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 806146357 1250 806145107 806145113
    0x1c060b13233715080114150f010905030703050d020f0a0506070507021f0816110601050d0804030611030106030e03180405060a1205030306030609070308040506030a182402090d060203090712 83
    0x252401582d0403031008101c40c00d0101920b112018040c7e450421000040c04180c00c24180741c3e131300c0c400580041c1000844156500d002c2490b0682580c015121504051140170021b0340c107101e034181c0c0d41c5041c0024090100b540e110641c803000301401d8081030043c0007900c0d030119140c0d081071810100c810b20314020010801c0c0390207040400201e90801005000c0001c2e002054040d6080000300e030035550042103203a080000707000d03041c1c03454103043d20001c0c014400000094100c0c01002d69402a07042c406440b540740c5600a425503400f1485581250810b000803540a980415011220318040320045401d444240c0414035802031034002c40c07402c0c1c6004106505005001000314000d8005a04940b4107644446135540c83d09010f000041c456070b010041040740d480c3c40f401658011030081c00c005050342984111a07103005908200f2a217911b1031046809480d268501c1c0c0f2001e1450400c015441d01e01b01d9000107149101183c0020038076580400840e4182800704002c1c00036101890b00f4400400140c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 806147607 1250 806146357 806146391
    0x90209040b060c06010e06060c07090504060b120c0112050c091318050a02190605070803100e04030c02010807021216060603050307240207021c060b132337 68
    0x100402c6202101513003c06c0b1a82448d40407103030907847c40300c0580b2200c4e08080c040405000090001c0d10029240c03503038842c080e500d58518a0310340340000000c0c04914010400503200340f0f1070056580d81103180c43c0030424038500c2d08040b25400341080b104880b06528242a000051060020030058000c01c10a0348007040340000b4400b860340d00131280825601410201e000c0b0700b13126805107000044003400348c43e0000d440320f00070b59005400c0640f2100d185880c0c41030403200030341c129000d800140c1108001c00555070055000d41d0420000e03c06030240070040614401c00340b248203d0b50005c41c011450031020f110466000744050369212003500c2d41c6c1c03e190b082c14a041c0150365501920302c2000c040c05014cd03a450b10850380d80607400740c84055074420060351818082c0d41072000740e440d41d07100c1c1b064500c242e95505210b412600a45800070700d421140a409812484404601c0c007031104001c14081c055240315415802002240030305c08146507440c010746d01c3c44031a0114601c440c0d05111010f83c0c0d09042d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 806148857 1250 806147607 806147609
    0x121e08070b060d0c0f2303030a0807030905060708070f091a0703020a06050a09150c1d130c080709050108040b06060a0210020403080405040e010c0c080c0a0f06050f0c070c090209040b060c0601 84
    0x4a0b046d08070309a01d0030410200a804007803004c1d031690003000140107581c02400481d61151290030005401c0003182c42d81c606000049500038002403401c000c000c4c51580094841c426001c1514000c1d01060038081010024200811011920791010030170f4820148200104a0341a1b8010024032290a251003650017400b8001c00484d10b5119009002800481e00c0c400c2c20300c100e2040c0c0d42c1c030f000503c0c02035175040d407140380f84010394014140300e03020f580d10541400744d400c180e400c0d6640c4c541a4600558020100c00389500068100861031003132001288680744ca0f0fa0300b20600b1650190b036041c003801c09030310380009912000c415900110b000001c8c842040c005d44101c1c0c270182c80522103944242451400c0342e012066140104452015850104807204007414114000d0002c4030b403601629122080085003604045500c035886d42c003000b801c0018514015085543c840b107032070921415941c2c01031116903d005080e07403cdd40c00f0812805994840e00301c0022084c1c0030344000c0c0e4071086002060b4890500b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 806150107 1250 806148857 806148869
    0xb030a0305090f04020c01050612160b0d0f022a010c0e040b01051b033a0c05040f030f0203010b0f09040b040501061d04140f100519020301121e08070b060d0c0f 70
    0x2d01400c008040c2c0041380001250038bc09a180c0c0d43d0a007007039a03140040d0012030804080725528106d1040e004003a200070130030a0b414007214500c4101104c072090b400030340f0500f80303041341e4104a21388e0402d907080001008001d00c01c40b000300b03078510187c0041300d86000fa4181a84a59060701a210b100a00071005090300346200c0c40b51034080340b030740b007000354041c0800f014000892160001d66904070655400404254114986a80392175501c5052a410002139001540c988140395046070451800344904410b01805550340d45240282c00001040c111000f04050000d60388035000804109003944640081d0960803045280300405090280748144112011a05141074001c6503a04030b20009204041e00c05050040c2070602d01c600c03403900900300181c110014007408002c00ca494444074000b45001e011060071040980029040443c11005950a5584101c2e48030500320041880e080441d500c0a80011840070541c841c400440c0e40c041c0d029001400501c0f01d9140441d01c8000d100c0d1500807610303 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 806151357 1250 806150107 806150119
    0x40905010203160f0905010912020111012d0e060103170d0c0c02120105100519050307062321090a0b15010e09060604060806120a0809010801090b030a0305090f04020c010506 76
    0x7a1310358054400400d03502684d40403500c030240400401a20032441e003aa58818034201c441c0c4000d141c18182940c1800594960280702c110304031081c603450080c1504d68842d20301c42800701c1d41c00c0c0d01c2ca8984a03581030001a0a104164030b68040b014140c00880d80410624a4100401c22100c0030081440340ca0300803c03441200c040200d04442501401401e001c1c0c505144289000f074a070508220150700080b503400c2201030340c4840090f8a6a0500808000342001d481d520510001d402517000c1003010020200c50030314041c001c00f06404000a030141203030300d00e050440c81b40e881e0643c1c1c081c982100d80390014030070071981c81001039482c5034881d11888a038082e2100ba064910a404000c80028111102900043c00b03000821605201c0c0940d1900844007038050706042d04150406400c20600f418180d034200380000b000d10b441d51780404c0e85401002002c208210141440f00065190395102c500942044004100707544955108108040c0104008100315641c0c4059110036010b07280450f001c45c4555 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 806152607 1250 806151357 806151377
    0x16080c0c091302091609080111090307060923151c060801020403050c190302090109051504110706201201080c03011401090e030706021b070b180f04090501020316 71
    0x40d14900d2038086903500804840c07031561440c1000104144a00d030080c100075241c6c000190f001400e22a5201c000d03504c045082d0341c3e01e00e44090500d0005e42e603002c4030401000840400803e0444481e0070001c0001c1003601c60a852a82c0018005218104003d85030800010301040300a1581d402c03510703420400b2105000321503480b0b24070382c01c034001d40c4005400c40e0000c80c44e4440528006040c040c00001d2440f52010098481c1c01003991980700744c0080b4900c556400501915486a006100c007415080740c00b400340000b0b0701c40d07040782c501402c0c0c0020429601d40704420804840c0080e65003a40503456481a00c4001d41d54040041007000c0c0708281c03440c083c03242030500c0c60406024074504208249600b4910f6480e01da0040014448009a80450b00090246400080c01da0000701101040c03001038482890414003a03c0c18030405502a0000ca44200107038011a05503c1d84202400e0341240c00000d4030811001040240400100080c2194400002c00003040d40a0801482c0000e480c1c0d103420b500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 806153857 1250 806152607 806152621
    0x9120a2d0915020d1110050c0315030d0e010f110f030703090b030c0306090a0b0607060204030227070e06090d0507081b030604020f060d060609063216080c0c09 70
    0xc00002e81c06280160000200115200d000e54034250b5410711032002c42d802c00c400c2d202c44800326034040d0f4440384402c0c000400d10803088108111524075150440140c0000310500f03201a2261104001d41d40c14010703428a1a44118001d040013050345056500395141c0400e4142a6a241d900000080340840c641040210b843d01000c825a031085900e200480d03d076440e81c80400800200040c01f8900c0c50351500080032030341d2140c801804003503216180c05a102d42c210301c1080794007240c8600e0801c1010b2583c884050014480c1406900400d481c105004801c80e2b904c023107082c41c0720b0741c544540c01000040e010300400100150500c00c58810005444041e503c000500341039040c0d0050721075240e840784001c117003d454051811038404c18020303c42d0740390802c288048016a10168083c00c0841c07801d400420500ba04102c0c0307400d00085001c40c0c840301085d49180c281030701c0d68500d00c019480402154581d1000200d108803402150018142034660341d084409076a1140c4c0c000402c0d0190300084082100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 806155107 1250 806153857 806153879
    0x20d0302040e07050f0408070b12060108060904060c020120040609080303240109030609060507021b1c0c0b0304050c03010b150a0f09180506120609120a2d09 69
    0xb61140505111240e0702d40c008101c85075080b02030950681d107000c03c800070704d0481c10040c11000f400300520003612000c503400e841d01e515100030440d0703042c0010002000703015644d02d0041d55000f0760100000541c8080854224014a00d8580100280d09415080101541c1d500c001d0000c8540d942c2d182a6505d448600094481c0401da65900513000d0004003041440c1c1001c1c10b8080b80441854080c45555403502c481090380c20a400c1030b80c00c01d56400902407a168140100340042d550304d00014244051000410b07081da850005c01404d90303191000d40e00c00c100158001c4002042c1ea050596103034100f90401d10749422000103c0c501c00d610b0480405014105580300c0f40c030303001083c42414241003680c0d20540ea214040040c40b02044000030021480000041100c00c041041200006440c5065002d00403206002080780840383c0c0000304010b0745207000101c0030304161401d8040d41d1036403803041d000c0d2202003d400410902010075060120440111410300c04030401e1a03480781c0c40e036580c90048980c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 806156357 1250 806155107 806155109
    0x213090912030c170a02120a0e0606042f0405040203040b0a060509040c090c030b31020403020906120f0303040f3e0a0302030d030c120b030706120e01050702030a020d030204 76
    0x408a941e200c44102c0080b65404c0132540322400000c09482c240d10114410040402250310030030f81d41d502c8014886401d4100700855108a0940302003200142c5032076102c1c52800c540e480440000044071140c144402c44606071782c0106406007055460303041510b0b00109140c41190b8003002d091426500245600d88144080c3c016600907001c0182981080e0105010301074001503001819148d00007074040e510303034800c0362051082d030110740710391f14529403443da00500001002401e810300500c002d10143c2e0b03c030440160132690445007041c0d4604882030090500f111210090203a000105c100001c4c04907013118996030703c2c45034502d9200281101003102d40720020b40e030582400c0d8200510528032540400f918011000c0007843c0100b601e54036400030745480c03c074a4a95000a45030500400850340100703c2c1c0300c4031919010306118000302c100c08255035650030702c1040104528060801c41d544296400040d0a8100c00000c1c0b104d4604a180659683d2003540460010301c2035100c2c80c201140b1134400e030341c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 806157607 1250 806156357 806156381
    0xd0e0d051801050d1e0e0f0106050a05010f180f050a1502060a11120a06090e190201030f09050307061b0c050a0f0302160602010623060306040906021309091203 70
    0xa00c40c20040300440302500042984e03407500ba0342e035100395030610103011040d041e03101c5d00760041804241c900d04142424040185d00ca06a03050000c148100d070748044110055030300030701c0e1031004443c0002045419027800050744803241c04412021540b07012122500741601c80c15503210403207c0e52407105020380c00410301a800180c0211011611111444d0403040200c0d0801f0203441c00d00b5005941d0745100c0c40e09482d802c00c0c00f40e483d40c04200c6030006000e0300d0b43c1d41d41d98001a1000d2881d884051541c0140414001d0405079240940d0384805003a9000320401500041108c1d2220803a24020005100300035490591115141d201340358284114034002c0180c0c0d000c03001d001d60900640c1ea203005442d10382401c405500071498204c0c04485101d0303060b0f0041c6050381c00480d60620f850400070500d00c8210040c0148409044911581e80303400c1c04072038000d902918002a8549981001d40080c01050240b4901070800080080e426140d07400183d80d160295074281e18031200540c1c16000c88805100d50 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 806158857 1250 806157607 806157637
    0x3060f0b071a190f060b0a110708060108150a0204033305060d03030207020607020612010f080601060801051012050a0c0909020c0604080307030e07060c0b0906010602061b0f0d0e0d05 80
    0x20001c030f2121500800035000c1d6841012401588840741d8000541100c0106400030f040f842d040c0ea58070310204881c02c01401c001000e040b9a50401d01c079540c80d42e210030250100b56015101141400c0540d034115402103070050429095003500490407014540240040b0684001000485041341c4c44d600c10300d0301920000306000a0740007150340c10340182d000100142c2c0e001109101110140e2240e0f002410081a0701c650181c8070742c100702c102d0312110044c0d003003151507501920060000b1a045501039054810886035025800c0740b2480456104407190030365102d03a41001c00740302052690307401c1070842e068282c039507003100e68850b200d01c400c038080d190010300e66510900100c2c001c03820103401160440071618002c10301302d200c24956881c0800769448280000c1c4015000f0041c401d030b5920158101c16280f02130202c07545481c1d4000d56905014043c940d007080003603444142002030ba0201c960b10b102d400da11685a01f00c248002c0000e0905501c030128030701030038a00c0a00c5510400440340a08164808 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 806160107 1250 806158857 806158891
    0x8030a1b0e1e06031f150c03030b031009030e10180b16080c1011120402060309101e0c021203010e0a0f240501030902060d090303060f0b071a 62
    0x100155107400030740c9650b440000700c5080788261105401148070b1084550b550480e040b0f00c1404156922aa500100509014800c03105025500c4102481216058a0003055421500700000d007460003e03086c220f001b03071134000501c081680080d050703107820708202e80e0024440d0a0420503280300840d405036230403d1240d468240006520ba0002d4015040045952501c0888958a62105070f000c1548002150701584901140940c40c2c0549254102000002400c10306c2d404201090071501031b2000348a030b00d002c80003a4103d02c00300050042c5c0c40c8100000c0c000300380ca10800d03812000800c0c0e005100141021100500c2034000221124088504588140303140e10b8608150340c0c840340030b0201044291100503450240b03032039018165110000c503c400c00d100001d40003006880c000d55000b14141402c1c4080c040141c6d0f14041941c82c80b01a44401003030180b010b01c1c0440090032242c00c070401040c034440d400b0840e0b0003542d002d0800d20b4423036841e280d0181085401810380300802c407142c0c8442801c0f02c00c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 806161357 1250 806160107 806160109
    0x1506090e070201060b2d0909040b09120a090311030105071b051906052e050d0503090a0305030c070f0f03061505102622031b08030a1b0e 60
    0x266004080b44000505191643c000d5142c80d8001c04003100b034130082c3d60b42c00b451181d2088030880c3c04404030280911b850541000b003020031100920280441900c030b00050f481040a02c01c0c8104c8441e1282000e0b540c0214035005010345887d0302003900c4980d04e030070581c001c030f0034144a51790055a1740c0c1c991011103c0c8030320300c0305c00c03c0783c040d401182c440c0520344202d541900c16041c030041e028428600407680f4901110003600001c514214601c2011300c0c50404200f07400070340c003140306455044e6242d02880300c080c180545148610843d42d90410a00e210010a100001c030181001c20700403000d80e104580d803241c0000403501fa500510414602d00401003001130b2081c0d2081103d0300f01860310400003982d40d800951001c4010b094400880c4070340454440070203501946000f10f4a00c00904015030620040300a0400d120082160740744400e100c4010030300d4000c4000d80344980c1c0c0c107600314414000350701c0c1001c0e81d83c2054405c0e000d0641081441410303081c00340d1548100b140350760b444018162140d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 806162607 1250 806161357 806161379
    0x2060408160e131709060730050a0302070c1e0602060a020903060601050a20030a1b0c0501031d06012408042111031303030912150911120d0201150609 66
    0x1003c0c060804e4810403c010305030712641c01900400c2c0c01500c8003102c269482c1c40001c030003600c07225510341f080e002c010030300398168101040e10703032514941c6030040c3c440100d450000024241c50300b08080140803001911044c8007410025400d0717850741d9081d01c1d00c0b600c94407035410070ba01960441582c160040070019009510441c054040365085252064542c0300c19100c1031003c0b9400c0710003085a0f0400a001e1400640298512039060303c80f000c801260401c0740c9500450301d241d40034450400d5143e404007402201310748101e4901c0c0500d83c0503648996965183c0101c0c000e00300c4d4100c100c000220800d40341d4180202c4185114035001500c8407201c0080440118076030400aa0b904280030420003d50001003080019203048668940c0d44100e541c01c500703024083c22155441a03101c4c00132507080c83d0029180028084a07904c44040c0455002040c0c034018180840c015885500106504085903100000103600d001c103c03159002004140b0170f1408080d81c240b124051440403c18502040000b4101d51b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 806163857 1250 806162607 806162633
    0x90b1806090d06140c070515101809110f0f0108100819051005090a1506090c0305040c090606020c0105130b0a050a1205010f0e09070302060408160e13 66
    0x4046901e80142a070005024450480040d10351694035440c0004060b1813441644e000a0320304005400c04640f941c55070743d03a40d080c01d40340c00058003903400b188200c15003801e0400a882054000c1e4a01e5105401038801010b4200003a9101c44c200001505541068000141c010102811101303c808050005555001010b882d4000e101404070001807840c90500401000c4c4440001c0d0000c50a61824118549101810345075542490401806003c180004e075010495170300c148648489031030500b40000615480e0310124401d8108910180740740ea050303000790b226612400e6601c3c18252100441400c40c0c01c41c1c005e800150b8412690f80600358000d10281001e50710740c20030141401e45650050f180c41d0000307004000401c1c2d002ca01078640e10740217032100071801d8003501c04006962403c0b02902c40f00300b044c400e4a000d00c1d88880414094442071001c9400b668024020690b50380e61004015078071a00e0140c082005500d50b00007040d85030141380221302401c0f01c1800a08000d42c0c1e80c0721042c000500f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 806165107 1250 806163857 806163859
    0xc07050d02060405040926041a041223030301090518010e06011a04080328020f070504020705160807170a02240d050f01141f050a090902071110090b18 66
    0x1c07050080313a084104407880040001507c00c840d00c0b00d1a06d0041c1c100c1540558412035100000c1c03105004510a20104104060700701035007180c0708504070803840b00010718980a041d03501000002060406954000364001e02c44401902ca25081801041d4200d0360000180e440982064004100d91804a02c0d20030b44400b1040c0110301c2d1030341c0c600b040e9256511a01d18000382c0d0b00e46100c03030000c80500c4070b07807000010700701d0014041c925800304120745c071502a070041034800da6000c40d0070001d00c0401c2092105205a002614004d903440d006140c1c0d80355082c0c8648500a0798070101e003a012070000c02c004e002c140e806401d1b0500c0c1004c81d5841e20327800f0900e020341100c00d1002d025001c0d14440310f010f8107000b8403034a161890b4550421140d1008010344211031030103081005100c404010218444841040080c68442e4890b111014100d0f80102940d02100038503001080c480140010344003508401041151050750f14504424190342c071142902c144010248180705a122540c030f010030740d9228040c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 806166357 1250 806165107 806165123
    0x8211801020705060711161514070309180f0504050606150a0909020a0e031207210c060f0b1201150906050109090b061308030d05010b030c070314040e07050c07050d020604050409 78
    0x1440103811100b104654032011580c0000703a1090585030b004072143c981c180d41e99200528005050724033402c190441d22443c140d4200022220f441001d096001c000c0c51642c40c1800d005030b040500b0842d43c0e654098586038031074000d0004040743c8031801011603040d02c02c6621140000b9241200a01c02500110300c40c200740000f505148800c0ea0342800703403504403c000d800d50703500c41500d801c0400d003a54194030794031003081e11102c00140c40c64016507040d801c40d50110011035404201012140039010503140e0319005465141c0c1c82c0e00b000b42c1034110b201550302d0340c4c040501441d0b03610b030a61300307072229846130902240701e15800f0300944005410088a811001c3c24191401c0c2d00c002400c80488904d40c884440f50b0000b196000d2100198010180101b4002590900314140040980d0451041d000001d081c480d02c0b0414040001c108000da070000c04072443e03d00700d40d1500703c0c800340099000b51081100f0f4001c0340c00104862921203800044c030303a0090002400e150070001840024a003031181500c04003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 806167607 1250 806166357 806166373
    0xa060f052e091103040606080607050409021b011109030c0f06070803090c0d140c0a050a1502011803050c06010819140f0a0819030501050310050408211801020705060711 74
    0xb41580c0229203c0f00418028255680b902d400e200b0300f15841c5030070010407600703c0410300407100c0e8401c0554058403c9441c0041c0d4991020718040c1c110411106e00241135401c01010301203140004024202521007601a140c05507007010812420360b045aa9841d40710405120040101301840f010750380c031244d0380d07003100d0300300680500150469004000c221900004140034101078042031184095405050307074400c400e1810300c80003e0a020b681d02441300360304511218414164800d4000941c0e0754100c4100d862950f07960b0500034002e6200f180140d6451241c5000000d0781038000803420100d00b842450b907100074007190b5949050410b030302c1060119110f2682080030f010800d1001110240c4a107900300d9a0341c0f01ca030201c1e10424440742f0101c2c00d0502c4c08004109945011501d410000f00c18800001c4655542c545171070103008201213010100f101e0300c4090715181c0018003003409190f070007903461603402003018020f090703100d50040200f051b004800071884080c000c01c04034201010b4202524200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 806168857 1250 806167607 806167619
    0x50d09061112070b072706030f050f01180605060403060f0e061905040f1b0603050a110f0a0903080d020304021c0f031d0d030203040f0519030b0a1103090a060f052e 72
    0xd1b880310301c00c608100d0001d4074100003c0350184608603416003018801d001e030789040c0395400d40310401485030818a10007081d18103490300c2c950b400440901001030a098440b520b07400c00034000c246000b0b5488904c2d10b410031141d0611000240d070380c810101c000d00c00d20800e190340c25a001404014000720b8400c10541e1740e46c07000441c1c00c5500b1030300d40a500304040030032f407400740b0040c1550f9014101400c400d19004114064118841c11070300c485088044583e5110b02c10710003203901c43c1940d800900b82500105400045084603001107000358021181790500c0480401d071605201c4010500401541c0c00040d8400000c0c0038403030b03034002c024500c500e05205a03206008903540070782c56003044005030000241800741d0200c040427103018001c16030350b0440a01c01494010302c00709007230101038212108100010b40f51420341d00480c40f10000c4995081c1c03a418020189940c5092000085600390b0500c540c89400b0a128410bd034421030440c0354082c44030300e00d1509000c0c00081d01003d81c0c9812540ca0000c209 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 806170107 1250 806168857 806168897
    0x1502071a010305030a121820060403030203070510020406120b01030e01050a0b03070b0c0d110705031b10030515060a0219051e071406090d050d09061112070b07 70
    0xb140500003540d500c01140a00a01800c1c080d170301307a624185403070001d80380c2c240e44500c03695105074440d454100e40188015290142080840c81e6988200006000300030194007202620f1041d00c22012101c2c5100d00403102d805a01a41c0580000501003640e4014501142d80054148010604002071506000c05903d0b0a6410449000301516159100040582010400a0000d01a0006180c01c0030321440341c2c3d50322354429254500400c1140322484084100074401c0400800d002011210520200c00701c491b02c540c641c8031010701c1429040301c00c0c088580a80140d0b0322030800d562145100e03007400c0080040a4003d40060002c51150f488460300c0d20f98502d4410810078010300090a4000c0c880d082001d03440100e158045181e00300c41c00070441c0300c0042c661400e98400c02c8400c540c07543e1351003003c211918813100024000303204002140480c9a04050710301d0940b42c0b5591140645030840c040d26544400158039185070010411106000c00d0083e054640c0054181c54080410203110307100703c1c9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 806171357 1250 806170107 806170109
    0x16060f0b04060905060307051e01032a020105070305010b0a0c0602031905090c100c1136010f05010c0c1e0305030a030501060e0906241902010f1401031502071a01 71
    0x24034540c4d4400b44611071031300300b042c180249800c0380c1d034a0803000a4244100c212055254540c1031540b10108072070f00d03607014507094541007401c0c1c000d40001e100751030000340a805c00351440804a0f203000000b20743c030507028088610854003500c0301d80f000c43c200c1da1a81d001790b1000b8080b031241641307040980c54444260103034a014004ca2030042c0f0f41004540200402d01145000704424012600790200004210031330101d000d14003111110340311501c1504000107605420300c080c0045401041100409107c0f16101d4103940819042912a03600e520064524804e4400090701c042200541003040070380c0c8110048c071414103c00c01c4c0d8811030b900d50f80c661443c0c010500b05400720f51101c006000082d070104c01202c282c4021030740c0c0710180c01c020010400c5900c40c3c09980e0342002c44a0203403944850004208c1c0c8070002600c2c2003002440084600a0080030380c1003805e42c540303007060108020f15a26074817140c1a41c2e000f51800061000806a21000794421541126040b001c1c0d001561004181c8020174 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 806172607 1250 806171357 806171369
    0x50603070c082a010501090915090204020d021603021b130b1f020d0201140c0a0e030f03040906031a07050f0a03090c0e07110706050a120b030106030f120516060f0b0406 74
    0x3400c030642c04503c1609548050300b00103e45440c0c105070340c0210740c5800d21940c01902c09140041c45c50080c0c000b04020703100c1c00099643c198000a420301c19481c0300706010b80524040c0d801d0343c0442c2030f01c2080707030814142e10000d180c0c044d040841c4c008079402ca5520086101c14024070b155045418415004035542c031a00b823a80c0075030041c0c0c1e40c0104481d0280140c00c0f4442a05e002c2c101540350001d000c0e4030030701814803180d0400600200c00d402c2c40e02e04002c03800d81030245c0c004894903241d0744d802ca00007070840e50000725411040c041281d01020321200e2224029032440d1600d50130501c4680c3c41c02e140b5003144220b48101902e456a901c041007001d22540c02411a4810302440362400c21806840303400501c1198001d588901c5003044855402400e0311310309510751a1004c508510101c0d884017500d04000310980c103520700a0004200a028035044c000036220361360b0b005e4000b200d03034000d030340c0c1e07019680c291100403642c552104d001488503446100c0030103180c14000b42031040580840d040f948590000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 806173857 1250 806172607 806172667
    0x1a1002070807120206070b071214190b03070530060604231506120a050103030e0d050607140c1c021009081c0e030712090f050603070c08 60
    0x344056002880342d100580100c40300101c480e000b40e0701140c950700c11311202800b0401d00c81c000c039104d035203c7c966104448404a02c14032111545940c4540b0116040d1500c01102d5890720641d00456494012440b490b0f070000c01614070700e45000180200000c4e0321a604004402e07c0d0194142e47d0040b0218107036a404400040502c0d00e42030003408101c0f4410104050a4080706425a5520041c1d90440f5413000c901410084140520004a01140556102c14000006038800c01c40719a0155206a040301e0180d40d401c010300e030a113000c1c8030b90840114005010b9400150000f401c4500420240d0010f20620f81e407075180031500841d036400e00109070000c900c000850054520143c2d4108407043c645200444208100c0020356501c1f403039845419410070303d4420040203181c0d166a04da00100c80a2190340a5950720017441c901205c00b04003040e0410041404048081084a00c07401002c0a8034009800940303551201c4009941c54000c06500b121409010040628000055807030302c04401c140c4458 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 806175107 1250 806173857 806173859
    0x617060312030a1434120c0804150506090408071704084812011b1e08071809060f091109030a12022401030b0f07020606041a100207 58
    0x14038a5100050311005d07121910481e5a00c2c001070240d03c4036030b40545102d450a03083c0541809807a9030080c07a040c29006490440004e507c16040041c2d1032240382705035211040c80e03010000c10811242c0c01d48411390045403034000140001c86c0400106115801281050181c2d401201103003619072094210795920b80000707210002181d80070030b00c84061700071040001d050824804c5080a07613260b0b4022500b840c030141c00d01c540d550301c507a40461401910f820080c03110000540c0744074580301c584030392480042d040396041c400804521216a000308030540c0c42c60095200c1101c06c48440c400402c0001020081040c001100380d5035114180c0140100706401c80010302c7c0082060440f034154140d130b0b138644820086030004c0c3d6000701d00070305101d41c00121564200c0700f07800103d14000c24036400000381100c4100702132200603c030f404130707040300d10a18a940e05996003503000b020308041030f00c3c94005640310344003068403440e0582012070602c2200d011a034440c05c0040010b500804411b01c4a40544c003c200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 806176357 1250 806175107 806175131
    0xb2107020703081614151f03060c03140106050406080103030807030b040f240302030c09101e23130b0f0616050105180304121e060b01180617060312030a 67
    0x85d6943c0024030100c054040041000315008a43c0c0000380551f140c081a06200501941d80c41484405103400400030403100517840c50280081a00800308003850480400020308948900211816103641380c0c1d1700507a030f910f940d03829150090090840002d054551600d4003442e00e8070b200311850f4540b40c107404a00c4040020a400c0d07500380c80c0700b0310741c5d03e1600703140180050717140023a0305200c0107016690006540d5865520101d444003079004003502030403401c2040440d0801c01000d5060312580e401d801b625041d07111003504881502050740b508041c400241c0219608a5442200180d50113001007030100d0f0300b030001030403a83c00b020012181c54150070055080c09401d1241c0c1e0b600c0b640d0b05600d01018140c445410780c1d24026440744410180d140310180d000c04c000a14154201c20001048036804c00b42464120040d041566080c0d0001b40300e008004072189140a415007114140d8541c0403103240400c240414240008203981d07017511a0000c95420155540c004501c942166200051a40e00900d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 806177607 1250 806176357 806176373
    0x318100c0801090608070b030702010e0604050120070b1f0906030302011d0102090d0f020406030c060203120a020301060c0f02041131031208070c0b1003030206010b21070207030816 79
    0x3c0c00101485142607400d100304a000111001507c840540c1981c807079580340d004a000d8000e516800f0b0050290b5000d1208218054019a5020094140c0f6175110040c10500150718010003601030800c80004002c52520404400c0743c101120100004064080d1108070100903a5084d1b8001c60040c1c0d503070340445a1040c10403a1501c1c040000d84000d51800390071070002078601c1c01c900809080450000d01d440b00315561541b0801c0110340c021425210666a104069102d41004070782420172018500010300d00d070090301c2128107072003064681020807a207e072140c1002680c800002c07070304035175584000c1003031100c010090203019030b03078030400000d140700d1140800c0d81421101c2c103902c03111784c120070038030000fa009108003c1954591800100550b190881154290142c1d07a01034089031700d56040c480a030f0644403d0005880c002c0d002c42c0e0b9243d988002103121803103655141c3c8040744800b980f0721000c2d514030307004907085182d0b441141c000c03a4032516a8002c0ba4084651540000c1e1440c4400007008000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 806178857 1250 806177607 806177609
    0x20a0801090b0a0b1c0e0a08040513180b0609103614180109030f08041b0e0a0605090906010618150509131a0f061209010c0212040810020318100c0801 66
    0x3070b81c060400c1000350340d1011500d01131400381c140b0030342e107000bc1001e80b4580da500881c20810700301c440d0303039004665062200c01d100c015550903005211960018070484030030340422084407480d18511444181440180980c1d04603000043c0c01d8442d80309158200600b58041e03050251120780004800d8144060b022901250407218503649904001e801004260080f0101e00e4200320381c14816000d03925883c2c02c20f41e458040203034000b026100314003c903808403640e182d02c3c17081c0c0803240c003080075688070001c0207180403048880c1c800540c000341c018090588120b43c0c0901607241451100f5034039450340c2010520a240a001500251000c81c41281c546440084070300c50b03000b454000c102070300b01080300314074000868034020301032401d18942032499242e030380c102c031050340001c1c81200441c2001c1014034064500460000c00502c1020200180410200d04680803100c1c4a80201041014101c0d000d001e5080180301c00c0030b06545698036010000709014a00100c0303040d107000140c010b1200300c050b00c00941 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 806180107 1250 806178857 806178881
    0xd09080729090c060a090e0906040b220212010608151b0a2708100510170d08060a0314011b050301081e07030807050d0909020a0801090b0a0b1c 63
    0x40c0040c010302038808100c0080c1d4480c1600c4807941c1c4c0d0400c2c10282e4400d0816403187c0c01c2200c541341082590007002c101c0c01d00031841480701d5400c030381b41d1120459518500c04e065444686800c25160014500400a02e03803a81c80c00c0008902c003659070882c542065689d0481d40755a501030010004c541d6006840d2600009002d00c0240c04c05c6022003004140d680c01c544803580c1b0030351010700454070700c03003800001000f4891102201c89540303015045002904c0151009000030780b0716440420200c221985182442c911880142414110500211441c140c043d182a07086500c20b07a01201141142c168020402100c0c4004107a60710703150384442c0c2010404030414100b04091005101c03101020070300e20f0641480c1c6c8402c440102c9191001400c0c6601680002e01015001880004100000c034010034000c08540350760301c105075505100c0080e13110b0140e54000140400c8014803403607280d680502040c00020740154455501c800c1454010350104e03080701c030800ba280d4040310305c0900f14020900a024 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 806181357 1250 806180107 806180183
    0x12130b131a19050a21060807081b0d12051606020409020c0606040c0210090302010b030d0f18031a090c0d0501020903070b0f03010e06060c1204050a050405040203120d090807 76
    0x68010801051a4003403010107500c4150722482c00b1611761981c05c0540030f440f0307100035500815904c42c040c41d61542e4924074841c4120641038030062510304512045d0f0b2494100d0002000344440081c125980d80c0b100b69020723412030240f00300307901183d060301c007400c081e20511900596500c0d0001000f46081401003410344240d05000c1108125980468401003003030725044003144804181c50103902601000c1c6900c0d40621580380201611a40800e4020702000c0545030400131a40ca10040c040d8144203000c0a802c1444802c091540b5030406070060754171600310000e413080403a400c000a03541c1040c9841c01c3c0d40c40e80d000700b80750303005107014400c60780140b0307042100714985a07011420b141c0701d0005200380c2c00041d208000145031925071204031882c5129240584180c52002c4a000740d260b005406664061210b00e540411039042520030707103000d81d0b00200200a0084030718040c03040c0354408440b281c0300075191011800001c007610050460103100380310030025034404e4a15204891085c00108280300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 806182607 1250 806181357 806181367
    0x61a1908072d08070908120a050405040f05090c0303070b04080901140301091422240608070302030d02030f04060e01020a0b010b0c12130b131a1905 65
    0x1190040052652145041031403040e0394595040d146003031910420400c40c601000e0840c07211040d000040100205500c03a180b2549030341d04101c940d000d80b4050704100d90f011001c1c610145241303001401e010403103494400c1c60161034102050030f507000c52810a001589540c01c0c0030014400f031207510300d45ea005a00450500c811030b110784040700e00c0944060680722001403c44034591181c904404003141c50012599656912441c0800501070522285845418480800c0a0695140c2411003460030760440031150080d84e10740141d066a803c1529481888907061212140401d0041400600e420030107000800d10b940107250070001098810821900100828000348070b001096806440181c40c100398880f1507070380184c0c90040645809015449248000590b12203840f0046c410204d005080d684000d01c180c40340c2c8550301500c43c80c2417608400400a11142140201410080c44005c2182003403d9950440f44030304119071255807100303000040d10080389417040500c100c40c3c400700d160461800c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 806183857 1250 806182607 806182627
    0x307020309150c07120605130201050f0d0b0406090c1710210203060a0f1a01050a030f09021203030907120503070204020a030e16050a08070f090c020f030a03061a 71
    0x40e1061110303061059540c0002c002c10310340000240c4003040d0301803003180c000d2619031070403c122030b440c2030044a405003032000103810f80c5484244140c00d6541a150141070050740400e84c007854203d04841206207036540031041d0036540728000d00c00201800000040c0c00c040d8458000d06070700c5101507000320646050207100c04072a0350401c1004407115a515205c620105101407002c007010300c080654148104001e01c12070310032561000f084a048804100600450513030340c810300a0020080c24040342c01480030109150003608040d011031460000010500030503800140301c048005907102d0664004010440b000e0003c001c00c80140c412030040810041c2540c1d90559a0f109206009000d82d4022a903d02024066005014031001440c20f4407015054200c14100c42c444038429240700e00c101c5e503000140040003141c401c00740c1e100003080c40c0c0031900300090100901601021b50085118100801034503903000d10180240001e251b83c0071070300720314003030711030b120a036180c0020120501e080000001c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 806185107 1250 806183857 806183863
    0xf092107080708070b04110a2301080a1d0303011508101a0405130905060114060702121606050c010614010e010f09050a03050a0611040608040816060606020c120102030702 75
    0x1940c045501a40d600561034060399500660358000d1112102c07030f05000410200d0303910300d01f407154250b80031010240d84802e661102a548070b051a10310b4403651002c140340d4411003025512030071102c00851a03080c800c000c641c000503400145010740d0170100060001c0e010074020b480b0b04001c146401409400c100c04800561b20040c4500448000d02c0c0c07844008800000058500411340104410380310004461100c000e0800c210b800c40d40b40c0612800030503611840c40b03818001800291070f01d81000c400781c0c00c1c8810260300750f144e281c55105440c0441040c900190912014200d036954880d1203d089108141c20765429800c1407041480ca00d29464060740c1c4280980c200c4d120920703080344840b41a030340a81c1d000072070350003468028040f10400310900200051280c1441d02c9004100902c017803021900600380950b0003501c000910450104010034100740145c00600c2d0100244c2c030182140d543c524003101d40c2c2d60700c2840960480202d007207544c9040000d14100084c960000e506d545070028000303403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 806186357 1250 806185107 806185117
    0x1101020f06070c051203090a030e03010c1407050106081e060601083303030a02160b03010f06050c0c06130806060406060e0111010f06060e0a090908030f1306050f0921 73
    0x41080f214080400610004000c03010001000c80c0d042c0b0350303e0070407111440c0c0740c1c206031a080d000300d60f40100000c0c1c0b60405214481c2e18007416598105d5aa80a03801e00303035140d114003410b94107903407070307400100d2060b0060002c014280d4004909001c2d46e10120a50303820301030010300b514148020303042000b1003c202d80341095441ca000c0340c000a4105000355203030031140424400340380c240c400403400a19581d00003604400c1c500d450020700c6642641c0f0b010112151109015030000c003c5080e0003005081e0182000d000d101c0c07140c505032101030b42c1d0345000c512503410001c04984241d1400e00c04101e504820b20089400440554050220380d0401c0720107401c444007400014100210b0070881d02188000303501c03074910728000100070310071130b6507548009080380440d81c07095124078a02e050000d000341c00c07407164a00503a88038285a0869903540207144824100400c107070001d83d4401594400141207101e120b1041d0310402107840c103030030550392040c6802040c882c20740d1245c0c5420403100c1a0b103448026a5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 806187607 1250 806186357 806186371
    0x50d0509060909180a050313290a050409140a0f0209010c110109030b0c04090c090806071808030c061f0e04151d010203160903110f0f030a08071101020f06 68
    0x200700761119000c28104520000002c080f0303005510280040050110042c0081d170500346050380b109480d14003041e200810b150029100405402782501081d2000c4003528200c903003414400e0034a03607101e4041c001d8400115041c134284110342d0810074198038a12603240a01982182141842c600701c001070200c40800b40c0c007400039844088030340b0007a0b10a2082c1405554400c0b614900c6d41060203030000306401c0b81c0241003040d81060420b1454a105241800840d50010010002c540300c0300400c3d144202c08440c00d801d010000100810810000c00050071000b500100030510b030f1500312543c210f009040f8502001d41400c001003000908060801c0642240e04001c59104824189100307a0081109000e400d0341540c2d03142c00030220100641c040c510401c01020300310440603a01d9401c4500d8045800010128200c002c00001541040031003140d03504800f501c170030383c80c42521300024034080b403c0f1000c65205000046040c108004007420122284003030004140f0070103140300854590b00014160 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 806188857 1250 806187607 806187619
    0x60b1018060903031b290103060b01050f03010608091903080609181513060c08010305070e0c0f030a060b041e0506070302060c030403030209040c120c11120c1018050d05090609 77
    0x1760040c054000030315554200303408602288601c52a190f40c40d0000c00f4032050b60a6464031075848c240303501850444086028250406295a003032000a403418040030305103100f144a008013401301c40700700b11a11143d00340030382c40b4000c0500d8070804226162400400503900320740c1c1e040c03049013100350004180381c0600000d0550603c0d80d03204980d5582e1102c1c2e201000c4c00285c00c041540c5091341d0404d0f5194183da00070341c26151032a0f103e621840c2040d4007903915031030262003000140850f02100c005103810174200f010101d0080d075505101c20300f80e00550850407200e41c042104283d50001d0544040c01840c054420a0806a180d00d000e510303a80e004010340030700c840000024041601c26410ed480c3c94000620420560741d860b00010502044e0f2045030183c28549912410389c0c500404280c201040540018104036034819421402c681203124160000d100b40001c081402c40700303004091442c25451243d082c041d01c1030510a00e4020b0b4000300c075061103010440080c483c1c45542c101c0314070400946074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 806190107 1250 806188857 806188907
    0x20a0b040f05101b211b0f1e0804020105090a090c02012012041407090b0405071e0f17011814191802040e151609050d060b101806090303 60
    0x800c0c0014122043c3c5090031a1901c0c484065080040c20607035a2400f0039502da18500020702015074041a01e141030708c1e068010101000150b911807491280d209106141240c20904184017240818400d5000101300036101e81c0042e00d80c03a424400c08268480740d505030081720901600201d801d2180784042003550785580000b80c18480d085041941006074101101e02c41c60b0b403901014004c10700114058030442c10100030480c0c00344030750641003980c00c0071880950399061070b21003a2807103101c43d06860240b11002845075210300c503100c1020b0080c411a11900103641c002d104041c1291a041c2c1040c1003440048184150071101742c11201424010810001d604911020000b003c6400104000c1d40706080141c01c07018240081044013015514246190070f644601c4486280d030804600880c0c0042c040d107104011a10b401f51903901c4540c01050009186581000825007680088840101003136100001c2c0b4180120903110500411051400010650442d07500911208444000209615030421 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 806191357 1250 806190107 806190137
    0x1a09220603050a030e0109050603010b19030e0f01090203161512020f0c160509060121060302190608011415070c090c4b020a0b040f05101b 61
    0x1002401450b04102100c4007140940340c018824203041044078005490910006200d04100d01a43e041c0e0f281d640d0f1990518000c520700c40394403c00c1d07000300c80403d40c03074103000d00a00c50f09100e61032003c011710001040101c12801890700d404406a0300282c081502d91017017000f14040f4846616000c2c01d4502304e1503008036103603054041d01840c04040201140040c98400b8140b000400d8040ca42009040c00c5500760748604000c12072408030344650204803c5032801d480c501c28410030f41c6640020b0320b000941c5a480383c011961204020075182008024600180182c94010071094014003140c202c000054031001c02003480001c9130080c54644007070104d600d40c20040000c4418000d00000c4100b0031841c4074101c801042c4602ca034506034568001410741c3c42d100984628520761004560300e1003100001600c001c540158105070842003140100d109080c001004d0b1104e42e0b001d01c0c007030150604489500e0130b060342081d500b000c0c200d011629040c51001c600108070640202010b503824101c544445401d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 806192607 1250 806191357 806191361
    0x2090f0c0405150c0d030912050906130b0406020610031e1a150103060f0e041e0b0406090b060102060603070501030c02030904023c0d02090a0308030f011a0922 70
    0x18000c0c592002e640301c04626031160180280c00d0341d2030100111441c4400750301c400c2e41160300c01d607c0503003601c805040e5190504d000d080100b4003d1005000580f07040091581c3d00c9403201d2a40149040c000c000501b081071660410107540c12204451228801a14564501100f8038414814003000d20500101505001c40ca095251451401445d00090780c50604501c40408080d8104076011a141c241c012485c0c049007811001985d80480c1e400344280c0719071702d0380410011181c224181c1c0582e14006400011b05030707c1c0007401036100351800319000700f1600d4000342d5400000d10443c11580480d08119980e500041c17018225070003807c00140300d5091800490552103240c1d04140c00c2800010500c00264000060021041080400c032000340245c191303400c0b92060b440034086a0f140d05001d204035203201c0c4e60040182500040c05280419a00d507200000e64100721041004500c004004000c1e0326001102c5000004038684064038280094000584161482080d81c1d48100101e040400f840c10603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 806193857 1250 806192607 806192609
    0x4090201140a030501030311010603050c06070519050109110414070e040b1c060e030a051b0102070618050c03060105060708070611042319140d080c070f0503030702090f0c04 76
    0x150404a54409030000b02a000e003800784002c50019a18000c0074094003c18032516084e00e910401600c81c1110240400400f6005000282c0342c034024100c4c0c0199400b00351407207112440c030038070000c10880c0090610700c0d2070b8281c201d9683d01036030500c540401d01540004100b603100e201ca0420032548050000468010300c0070102c03540e005000014801c0f14103c04103201c0400a100d94002d02102242900007074480c099140d9103004154203100e00050f03c0b0002003000f200c14070a400050500d405c3c1c1e1106001e0ba05c00650060b580c00e20159410306100040c001d048030b042050f0000c1032194500804214a03100f00007019046034804200c4408001c07240d0421140070311898406502d0350348070b00200c80d440f6946d01204655180b151a203620700d06013500c00e24414803080c2951070300c262400705000e40f00c104c81c4000075130008442c0141e20001e4442c102924003c07644100030210282004424000d10b071181c2c0056201c0e07070007481200c00607030b10740d4220399016849540900c807544804032009054001c0b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 806195107 1250 806193857 806193887
    0xa12060b0603070504051504050901030b0702430609122603060102161503050901020909240306130807050f0307060b010305011d04060b0109180c09061103040504090201 74
    0x1000041c00f442d15800000391082d036104841e03100040c15803071140303219485544a101e4121030303101d0040020030018059076911000ca0700544d20b5120709981141088101901c051007181c0448920b1030740503281d2400450720503031102a44034118280740010704030004174412001030400c008822400c10805030000011041000f00c003e0a40e4810481a003181c0c1044924a0040c41505850040d1800003840300045800c04d125030214419200310407000342000a1008902d990200442190342e254444035610410a8003000701c1c3c5c1c941001c0c502c20a8030a1035030280d1103584180240000088800515540640c1c02130550b070351401036140441c20301042040090301400f0202da50400d110b00c41d007100d0543c0c18240d0741008181c3c1c071002c50805221628614128004002000800141c0181c1c00308124541c14100790400640d60f48101c80c203000c600c180940da0170381700c0c00c1d80440240c0000c01c02c809848903081040c01c0b005100141943c9015038459a0701c26622418980e0643e40101400042002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 806196357 1250 806195107 806195119
    0x402031306050f0f06030601060e0103090c03021f110d0206060d030c0b07050702040f1803120b120a06050a060b071101090e0c0c150c04091d0a0b010807140a12060b 72
    0x43c02a049007030040080700d04031242c4481c84000b898500d408a01103042e9441a103034036221840840044000704000d402c1100c0c407491022021000d40c0c0d807412122519000d02040b40d1708840313131081c010010071440c0c0218509602c5580c2500606401184480d4041c000341c90002501c005801d0403a8040844000a480781c980c00080c0042c0992040c02040400e00940c3c003802450a030301500d400b220801100d41c1200c7c0c2c120300316200020311681c6030304000c40b101140424420f12031000143c0b2410584103000003644601440c00800815008851380400b01110130051246441000900c511130740b8802095520580a40783d050380c09504094060800b40b100d41c50185407950881034140e0041c481041a4410015020b00328000780305000e2003030200c800d100703060138038144040e00604180c1d0720807034140400a5444064000810a4003561409403460400c0382d4503000e050360400d21190450080780211200d400382588840a103d021103545c0402c0b85002800ca0805d00014a00810150f901c80b03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 806197607 1250 806196357 806196361
    0x2061314010f050c0406030b01090303050909060d171c0501031101120608010213030b0906010639060c140304030203030f06130f050604060e22031b0b0106141305040203130605 77
    0xb44c0814041d000765240d907181040280880c1006556800c5c143c0b0001700050302c10071503816181459007501d500007401404020350070082d591804180d060712202412201004500c00c05285044140f8012074211440104110750542c2c4031201140e850250340d82c1445210300c1007000d45400b0354050300c01400640000c5407903074000106401d03030341b41512090f120500d0100214022150204005040384d655403106015055410f1403000480003007400e00700255070300304d1030310801d08103405c204007024070170480050520b0a10a02070314801c0000100551200c052080200090700001240c0d0441204680e0140da59034450014001046075810444d60303d06210460043c01500d4104500641d011102400181c3e15006881440c01e4200c40b036640d03210503014001a8000e10b680c110201700e0103840d04088100c04009280980d0700700007400c850103400c8100402c08160711181c44080007003649840c620380100071580c403003440f106003d400e00c20b640c0000860340301200c08105088140c4d05c030748144154 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 806198857 1250 806197607 806197621
    0x405041703060a08240f07021f0207021302090307173007060c0905040207050a060b150c07030309051806100203161406070201020c150a06030209042102061314010f05 73
    0x400b0005c410f1001c60b000c42c001003030b0700c801e991541c03621600c01d507401000d24120100804503124800c0020781c40d01a0308010420141e00c2e00c1881c0c100a402241c80075a80c3c0c1e0141040c1841c01140e40d0081c8801141a502000280310100d00c541c100e040c804c00d54440c4001d4007440804019100d903c40c8061180003d07501e04018098018010904541e150310503403d43e00c8003031200740d20814000070704c4e90f0461900750b0005910744d404001010340181c203501c03641001d24010003440d0b1140c000c001050340410010001c0650003240038010f4001922001c9030f4520150508c0c90214010386020310440c83e000a002c130aa1080098821086e56010303004a01e00d0141400110f51507802d0b043c0501c0e00904000500d000d0050080740c2d0004580b40040103001410f48040d001801c000d010220b566444580c00000f603a40e8144040c00385001d5101444c640341c07a01000a2862000c0300f81344251740212080100321240290701c041c1240d007007901c07c001d0003400c05259005000010400c1c03512440c01051181c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 806200107 1250 806198857 806198893
    0x7030c0501150609050618030a030c060b0307060c02040203090111180f0a06021c090521010b331903060519080d110f0f0102180405041703060a08 64
    0x4a900a000800071010401025901000e0030701070311000c6140d5000401090801c80018203800701e070f4100a403141c1442da000a0b081005000044e00083c40101c401010706c0410300ca034610060045000300711136442c1c010058010a66014080d210301da0102c000350035403030f081d00701c510484000c0710480d5658110401c0070503402055100c15000308000b04246416043c00c030300e80015502c0580040044451300c90070709400c604042031000030021000400602900c840c0000019400c3c802c015528200842242c50b084443c21107640784a100c01c4041c0c8a6241114208643e8691151010482c541c0005401c00b503d4400c00342004945003c101c041003109926a00000030303240c0803144640784401c21008a4049034440c000c1d034505030008411101c0d280e0007009119443e044c0c0c0c1d0240c1c0c07041c82012002c0e40c10005000c10310b041903500090b521044006040207074500768822241040315080035200c2110305801303040c03181500c01002022444503a140400740700144041021904414000020458 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 806201357 1250 806200107 806200127
    0xf111f051803040b0d0b15030a020a110d0c0605130b0a0f05010b13151e090f08030f030a09080906030115020c010e030606090c0d020a0e0321220504020703 68
    0x201d280039880c00325a000000c012a0215448036081034107103040b02c460413009240007071495030300844513401d805080c40f00e00c0195100d020040c60068a944440d00050300300350008860507415001b0302c00101041d41c12a03111090076810045c001555550310000341e594a05016014010000c19020040b0700c1c4500d80100030b541c910002c080c45607903666410240640101410758041760403000003807000c0380003120106144016898250061100030701014850b0712000d1030500000c101d280244460104111000300500b42100114940700304080001020f000c050040300310640c8880070f035030500440105499030076900400e03169032541e640c034200030040d13400c510f00d1001d0b008e40d04c01c0c41446d602509000c0380410000e80a40703600d03603410003001040d6074010008500300c1420b0008640d00d540a20141481442ca510307060711400c901401c00d0b29264000712218075204400301006410000303203081e80e400c840042e40d000c0084045c01031030105101c003900040e070004c2c80840c2d240145039100c00408 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 806202607 1250 806201357 806201371
    0x3080405030d0c0b0c09010203070818090709082107050136082d04301a100915090e01060503060105060a090e010e01050a0b04060f111f05 61
    0x382e4161030b82d107001e444110028101404040b040b100240c00000164000c103042001403040d01d207032401e01d0341c1d400169040941404034850540300c02801e10305098442075000341c09070500c840c0c85840d05101035a6511141081008a000c0300a01401070040b84107a50499900100078401600345808080010303131150107151450704241a403002a51120720911202c5400280042c9020107207501c03503100344100c520300340c03c039203043c01c40c0782041d03072088040c00c09096103100140160102000c10707495001c0345511a800c0f55001d04980700016616441c4054012851040640f2942c0302039081550a005a201c40280c0b403d011420615440044018040d91030b601810050107602c08142c0b4226280c90040741c1d00b6138410030041c0701c6490701d00003074100d000d041c2c0f410110300b40e1101c0103090300c0c0788207a0005225403005070050005141080145010f0100c1c0d0b941c0c0c41c1271524295006000100560030907040c404624490140c00c00103011404000c8000c05131f18802104065604d0010242201c0f00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 806203857 1250 806202607 806202613
    0x210a021906090c1202060f090f04050103060501050411031003060507020a080409020a1103070f020f0f0301060e070201141506391606081915062d020619150308040503 73
    0x80b13500300c0d200c034039000c07403d4000d44203a08040c0c0f048035408440c1c2c00307441c44562042000040020640d00c1f4082c1a018500c600004510740d45400d0620040d0ba44480d1415000c03581801000550300510701c1c403004480e000352000c1155214404140e0801203041e0f005028110b0000c4c1c00303d20b2030001d40040520f4655692a02801c200390584036859016030f400003003100f64250103003005450114580300703407107900a000d54006540c140000c0c2c00c5460302c0d4840080e40fa44001080803564080c45221000d01085031403d07114640318414401000400d940244034107400b0891080c1c8000600c0708210700518101c40700b60807043c40007180100385c00ca40c1000b4080c8a091403486d05513000d0000141107420320b44030110152591a90303840000009541a8000ba50314a80740d403000080755940c6d00185103a032929624a0030510f804000001d100c4004c06c01000c07030f102009203c0703600084240e404a02d107000c6230154040921140060310008240c46803440001e600030040c89108070041007118030841c11 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 806205107 1250 806203857 806203859
    0x10905090c030a051b0c070306050106050306030d032309011401061812050f06100311030304050f010e010908010c0509010206150d1403210f0603210a021906090c 71
    0x400540c0e500480305859910700034400315501000a4002d00e0b00608201940040c00104412641560700500d07260010f035407244000700244240e40c07061501400c0186006460362401c0c00c0401e645000342c1d140d400c1015079404c5084100c1d0442840c190784030032102d40300d1100b4204111120f01a2012140000b031002407980001180741c025481c3c5001103d0200304208924a002c80b028104a00c0e1801510140110388433502d00384001e00c421486203644a000b004454114280410b2a91100d18050302941c01008184510f503200c1c1086852104246401780c3c1c0c60302c880c03004903541a9143e208104c1503003406420b5410b40e03088005441c1c49402a4221031480d592915a0084503200124464008000240850100b01c0d040c2c1e400000c0b04a034030817a843e000c02600100001200b0f10842d0480f107440e0710904c02c002d1b88005402d038011004030003c4c8445048022061051081c0d40103440000400141e80b1600d90b00070310580d201164150460141c004285c2412005040036103c00c403900035290750 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 806206357 1250 806205107 806205109
    0x20c011d0714011202030901060e09011119180f0510080f04020f180901021b03130513060806011205010c140f1b01090302010c0905151c0603140c010905 67
    0x40000800100900100001032510540100d41d01d040b911281c104040140344803103010035400190702401580c000044c00502d40301d003861320024094810709169041c01d443e8440d1010359802c0d05c660010a5200c0082c0401810064540c00e66404441c10765010001c4001008503001208904442e000d5503c0315001c00402c0084a02c01004c403030003408041400080703009400c00c1244038041e248050849035082c80f00003140525910100e03130650a503034001441e40e20201c0001044540032411400030b500f400c07070b01714401002c488540503203402213032500c0d00003e00c0d18482d00320740010080740054510700d50f1039607496400001551820f540c1503082c9500c2c03800562180c020800760310b0300004c029040031010001c441d000d90041c4482807040030030400c04001b4060a216800b2001c0c46500001090b60710310b4005000c19a46900452040c408412072480f40f0460008484003080207031034851049240d001c414005159036000500900f0000030700c40001351002a0207442c0c26002d80f91000c919650324 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 806207607 1250 806206357 806206391
    0x303030b0a08100f18051509010b03070e16052104050102220f050307060903060b010224250c0213021908040c0503071a0318100f050a0b010e060c0c060d020c01 70
    0x44000b0f0165011040f11f07c001e150b801096504150504c5c000b045e0b09505200091400805400032034250300c1c1030060240e07561041c9103c031040741603824500d08050283d1006030020140081d62080484014001810031600f9411120282568880840d00310700100b03000d002c480d62030081c507240c150643e4002c00c09140c00500101110002d81c0d56894550955882c20041c1c0a5004901d040d4803841107120983c045950152540030049091000d43d03203401810000665050b41c488010642c541120318906907006031281c3c0501e405840000e5040444055940240303d02a20407400741c00c101000c11000d607224240c0d0313004031701810024440907203c2040544800f900e00c44e660f030314a20300f803400c4112014080a540d10650040f00c522043d10400880c9080559003021b004215aa42005203141c4a90f80304e8150480d66000c0d08002008005c0c001801f2088a0240c55104450100e11800c00002c1084020743c1502e01511480d254440c20f40f0407800394102d42e580300c2440d402c2c010005203016401c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 806208857 1250 806207607 806207651
    0x102040e01121104050112061a10050a111b1206010b0901030f020d0c0305090d030504080a0c051207060f240314030403060e0c040608060903040303030b0a08100f 71
    0x1000540c0d156441c002042030400c0380610100c4032840f412515003c0c580d0382d841103e0017803407100e2141d0410745142c070706002182c05560720700c8210341c101c400080c0c5a85443c080140d0703d101e02e00b800b50fa03400c1e8052054440007207155816425100b00001032140310030403100c2c00c1c60200b082e10301c080f05900c3e240001d40c0340d480034024612401418008400d19620940014400744803000006242080c042500000e036800c00f580040860b442d0007e120741020300f04074030380d02c0351110b00d000c104a00345541c442d4118442d0031022003c104668035100d091240c1031010b006680403942c0060740d551854035040e00905000300004610301d18100040d002c40b0312280041c010030903a80b1540702031504555401103100409220044c480c0700600c80880041e803103110b503400305c04100740181560400e0400b0002903030038a401c40800d9030048014030034803842c000700b41c0d01960340c07505010071201c1d080c0e0041540c04079250302001d2188103000341d03100520011340c0200c400340c0340400c080c400b0110009103808a490380c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 806210107 1250 806208857 806208869
    0x3010e010c110a350a0c02090105060c2d06010f1805090c040903090b0f18040c0516020d0b040602030f01080601060c0f260a090602010b0a05041a0a08030405040b03010204 75
    0x1c441003820000d0b060118000c1d454210100744811310340d450f1961900402809004500400d0071002585842c81d4001e004220498800b443e01c514850495241c020800702400d14078840c0240b000c40c060226412030f4218480001ca0721703e5a582c80c03000c0b4011080c0d2003540345140c503902d00c4001e0390829004d0144603103a990001c001445040341444020003200781c0075010810104000b1032510303c024001d02032005003551003034807078000d10001130081e001c1480720761107507103446082c103803c0c0d400800351044c582c00c100c0038021610050003c03400006411000505102d18101041304100c65503000d54024441410b981d80e06a0700e50180e9036071001c003030040e40003142c030300c022000c0003c2500718204042031049049000c4240c054080100001c0081407010504c040820b5240b074656020100c500201074a1000744194003c24000c5882068036004084c000e507202c031252980b0540c80304070345100000103002c2400a42d503400005440340c00501403a44038070b06000010402d03240500070b8900f6030398 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 806211357 1250 806210107 806210123
    0x1090c0e06180705160813030201031a0a051201090f14060f010506161e03020f06090c0916030b10050a480807030c0b070804050d0e0f03010e010c110a 66
    0x30707586011364040d0020081024031004070780c41e280000e080c40c0c01512524102c1072211101d282548009800e45d10313121001080366908607103880d0f195603000c032080304071942650001c2142d584a4072450140013405805440164120201c0041101800010300c40b295094203448298441e007851004080081c403a40c1c1c0d00040c14400c0c03144550000b14032005040c481c20386074500b280e41407041c42041c410920280d0258001070a4040b00090502890f030b800090803000d0300c01203031584006000c40d10081d107a41c0b00d001c8511b00800d0700a000342c0c031448441d43e0041451110307140c82c69000381280d1100c803440000035000040d07d02c1c100702410305a00400f200c000d100800204180c0c44503165a000e1654141c07c842928240700481e10850080c40c01300c1c0659140e01d120100790070004122040a03211030100301240003000301084010401921030003083c0782010b15041c13200001200d0002080403617602d94640000120b491505502501e07180240307480d5004c0b1900301e130055588407042d01a024090350 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 806212607 1250 806211357 806211361
    0xf0b030f120301210614041a250905180702120c0601090c03020403020303180a08070806040f0318090204060f2a0219090608071a0a180b03040b06030609070503070e04080c01090c0e0618 81
    0x24031040303645c0300909d00c0340c98080e80b210354483c00a07030105141105900d246501c401408401541805007000040c02015254034091044081c5591038405101d1154019515511030031094442e8046800542d00102241c0c2c44501145011a17551000c409181c0300ba00042800203840002040c64000c03030741c1c41c00c042c00c0207541e2a10740c0b48000c08000421810005040c1e51000c0858401c04204060080c1d88c10040e144c0b400d0840141c402a5407440c0901032003071001c2e44a1001422510784052085410b00150100c1300742e10100e10485018142c6040d0704200d06000f090781035559000c1c00454500074211207d8554070403030452408104840c050320013100b0000103015501030b0706e000c0c0080364038007a9a084242d58a041d2080e035002524100d441180b002c0600201c2d10301005426000407070074000c0d0251a240c400080da4540091107030100e100007a800040034003a5540507180409107080c020321004041e4680710004100d030f401002a44034508000c1006400c02d800c0382c12104c246103000d20219 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 806213857 1250 806212607 806212651
    0x50702070909110a0803120a060b04030f05120c03131505190215040b250f14040801020a02060103020a0f0b040e0604020d0f0b030f120301210614041a 66
    0x40c140004080d9144040f00c01c015407152079010141c4010000000075640b202d07001c88a14101e14030181c080c00c032050601e8000e020803101c210807101200ea1080c40e800d0030f084107150036810321500c2e00220000e020041b031001d844101c080010083c1c1c80c0040d4060148540b2140a4444c0c0e02e1081c00580c0023500038044500d07290042c03019800e00c50124012141408452010075907182802c50b03044071841060414042d002101c00075054444840c044003000d07042c5801c400520202c90079004400b08001c4403c58226504050120380c0075003d10781c02503540d05c0740d0745000380d6501c2080c481203006281c41c000003d02c00d540c0c9850301c8150707185c0e40c412a26140c0b0300241f0112403440a010035500c180d00301f000103069504c9216100842c0d200050110700e00d1034070000c03d414408048040c800541022480fa032411070008222815104980d10813030030022220003090300150303a0b45000f00031518140321000203450081005105900c521203000c0341009007100e0701c0f100e0351b00f07417920345150600344901005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 806215107 1250 806213857 806213861
    0x60a060306140f1201021c0c05030603060f060d0f0507030b060603090c1521060a17190813090b030d050c0d0f210b090901140408090415060509040605040507020709 72
    0xf003c2d40043c82c9500e4111640d46250032a4402460703002081c6000c40c0120444056006200041203e802c1040c00c600c2c1c141c001c0b0351542801450840c09000344000101d440e40e854074450204c07a040411002c2c490128544031355204030354001035400200c08000541c40d40781400890b44134a903944041c0c158070007640180b24000c0d0b00381e089440c0d540710500c0b6001c004004081030a03031440090520301298280341d401d000d81090141c100c0080307201c03425210004407100095904000700c440d80d4030680c6a02070b0520744880c0c007a4051802042100c2800082c215145030032018441d170046080d2007900708410000e0b03030385115400b01d81800380c011000380c044030340c0200c1246440c596a0f0a02850f010b0141003200c08604071000d04001c05503850050202d81d04210415652020406008001126000e8043d08408000903c01048064001034902254032240c02c0013a4031446c0b540404117a580b1841c016050303070440c00d1035a0080303150075000580f914042c01614040c96190300030700003043c102121600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 806216357 1250 806215107 806215129
    0x70302070b031906080706210605043201061e090b0a050c15011d15030a060c08060d0b01050d02010302040f09060303090b07031e0e18060a06030614 65
    0x419806141000a03054070014002d600c03030f4600740c1c82e00001d51014030402044031615080460142d10081050000c2070300541090000004000c8521042c043c20100402030700b100d401a0f50000d0900e07218154044010300d4403041080c0940b460083c000140c65425006442445040d00041c51115a804846131001c04114444014070b081171644d40c40361329001c82e6620840b03460001800020302e4120705c4000340801400c00c016403624481e01e501d8a0400c181c0961801d41103041c1d40c01020204100c91458804c40b00300140c060252400c06406052000090000c01045000329410800041082c904035590b11340c141d0f405000d07038240f0307420101444101441c000c022814103600b0000801c0002247d0740c20342c01031095600208401d4214900184048070540c00311860315418040a00000e401004d001c1e403c07079101800300d50003540c858084600c0d80c0000f41658104030840a03212240616002581c400e00050f80c03108112641c075030044045489034406c1110011100301d42031954600b10315500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 806217607 1250 806216357 806216363
    0xc050a0e01021e16060c110907091d061318031407080c0105100b1c050a1b0c020f0d2003010908040b0405040c0905010c06240e061c0804060507 63
    0x210f41c880030480c900140a0030300f42124490380804528010701c109403012401070301981c5000d01800c802c40e5a545d91600510580d50300c680056400111079900c01c0c0b076410b00401036000302c8803072842d005000303140e5844150741e601c0c0540080b0614004440183c02684003503604412038400455254608541003040701e81c03403c1072101e080081c47c000c5100c040142113005065400010350b030030a001c004500b002141d04c0099020400e00c82140580d820910f0141e22031243c1c4404501540d4078914030b4003d100c80e00d646025034550004420090b0340c800d102000c00e51003900c00c0305500f07107040100724500041c1040205810110008100c0c4818808500300d014180035002043c1226a6030b138090243e04203400103c1d801801080401891409010700d080504007401e280d010141081c0000381451015a0041e240584034088001c622503241d183c0b14180c1000205010700545550880e20207200580d0307558483c014000300481c1c0c16039007400d48041251b00407032031403400e450a18143e5541d00320400607 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 806218857 1250 806217607 806217613
    0x70210050409090804080105090c03031207180305011a040204080714030a05030a08041115030f0415060b0703120605010e0d0309080115230306070509060904060b03010512010c050a0e0102 82
    0x1580c0380c0b15001e1070300c0f941e10a100c4240c0355810030010a08507480140201440c1d44026030a072400e440c088221070109a20703150f1010380d5620888190713500c80034104500c0c11a010b41200005102065000c4040c000400c0d180200d01002c0500b00002d9004a0260051716044a0010072400200c440207c00c40407019090342c034144220f458090a58000700c07034803c04610004200002c0111041a4440d10b40e401c80d0321020a6051058940310303400010b25030300aa081e8000883e00340b010305a0b0400700580c1101003441026142c3c004080503410804003240400c0c038100000407407030f130103000b203c0c291481a0744a2003a84122007c02110820007042502800417640010400300c000713008030201c9880680404095525256a8041c0358850030480300d01025020a60942130b500420101e03000645850402d07101e003540400079210b481591165944207103032590000324075002c40e01842c101c0301c00301c505031389108035519058241c0e5880c25000d0006081040000d4455004400001503144180b0407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 806220107 1250 806218857 806218859
    0x702030a0b010902091c03020c27010303020f0c04110d110c010603030306170607020606060a02251e030314030c0f180a06110309241c05010e0c0702100504 68
    0x141e200c0303001081e00851102a00003400e0000e03420450500c2d0003100301c0030045489080203407002500d4800c0c481034544122240d640205c0300340e440f0f034a003020b071000c1444894507035690780ca006585d6034140341c4681c40a008811040e07000d446c00c0d200b10500041e10540306482c0440c0001d4401c000d00c41c01c0c004209088050241e00b000341024400c02d40610b109480004226040000c4007400007141d21400d11294460403c100842c0c3d40851000c0d0030040588620303486645030001a403d001c0007020040c40e80c0d04400060880d00b89400c44031045031541c40220105081140c0040200915030002070041240220b003281c07031a048000035607210118a2884c0d050030707842070411b06991702040c3d10100c003250326800081c0925014400000504050420140e2840c151031400e40700d014100d1518400c550032040c0c018418030307505880e1740000750010550f580311400601d441640b6112040c0c10300591030600003103003941040300d07040d0241010015890030400507600f000799102554011108200703003400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 806221357 1250 806220107 806220113
    0xf0d120e031b06041a190902010203090301140411030d2c040912030e0313050d02030c040618060807060503061003090534030f0803150a1d1005010f03020702030a 71
    0x9100340e01c0b081001d011030303091a06004c0801880a0703028806269207105202401000c10b4090303030041e510035404100c0080303c0c00180c2c04d41c01a840031503090350074108091a0030348600341c003d02c5248502403462500710100145036441d20441c0307400000c03c00c2d129920300e140003d110b90110030030820b00d401c1d042c0003031207010800740d410600013204c1e000301450010400d560940203541a54212100440c00c0581380201100008407501c101400f41c441101100301355141403012803c075840260044c003038181c0d580503821500701d80c1d00403a1001c3e8540358000c07030b000c030003c41c0a80465406558590950b1035900420031490440f0078000d0038141e07608002400103e040c010318035070740c0c0311f80111058030000030411010b202208032400c07920f51406c0c8050001500ba03000401d242c0e07411062940c1c503640c03410f071010b044015241c440b40d400400500700080c26148948c2c0d4010024221200842c1521945000061000b05004117808100300180d4030000c00d12aa0182c914613000800321406524291 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 806222607 1250 806221357 806221387
    0x70309030f0f02060a0914040e0d030b01030b060f0c12040e0c030903121005040e0705030a03050f0408030c0604060608010905060103060c1404031101020607050403110415091506020f0d120e03 84
    0x203000ca00100e910310b00204040040301c7c204005000b801c0d81c0510165201c1200720b525900710308805d1040c1507840000045591083d23010f041f4040018000d690f60b4114258010499044509608440e01c80d40c405010980803400a840c11114204003540d010717250603207a20306030340004211527001d10050140131903400b480e54480b40a01b00d0400454225420302d030510007a148089940402070f449035104002076100000d5030400f890701490070b9a102e0a641d00c0c074000c01e01c580d5002503428400800c8001c0a900041902401244100404c101c001d03500c24009003070310ba10500203041c580040c0010400700d40940c003c0d818106017441c02d65144514481501001d0b04107030016551074400c00e002e1803565804001654008059003091030416165039900520440009903050007283c41c0c13a0421300041205a14801606144400307000c2900c0303500c295a500139152050000600c903040843e414943c0c0481c801c8a621840d90351f00701c4414000500d01d02a0031840b941032804c4c4010850b078035a0076041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 806223857 1250 806222607 806222617
    0xe0606090f030610030b06040204030320070b0307020c04150803072d0305030f09030f04031506091a040c03060602120711101706010302030601050702011229090903070309030f0f0206 80
    0x2c064241da1350f80c2582410003610038020b100c00d024070300c100028004030350003050203240490304000300001c002c410703054130f800d004aa602c030f40e1301840088281302031190040b0b600803000c9020750b005c0000d07115419200001075894443e100554004005000205d145032811000d4034113a822072113040b0581104180030f0f95020241500050b9000c0280301c035441050340080c0d0048503204c02141031921198503a100c40c41940b100401011603d60300c086101290b412040081000d40010060000c0451010741c00900348001d913841145070102c2c0c181324a02900c00c1405075070b05a801845000300c900380307201c0907a00212041d03e02240791190410540c0e1581111062502e8035039428517201c4825660851005000d01034170705042c014810070090b643c1c01029510340f00e40918010f81d0003940c1c4114400103090104032500291644400492045645520017170f131b060083da05240303503944071489140c4a0048200c01000140b80a0f0308001048003280c013404030b107019400000b02c010b09680041d61036406 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 806225107 1250 806223857 806223871
    0x6072102011a0a080d0c0501110409060501171005131d01140907060c0f11031615020a08030109021c15030308070c02091609030609080310050a0e0606090f0306 70
    0x1502c10251440d190402c4480e01e014054642541680c10030343e4082e15902c0c405145e20400c051066400203100007508031105070703951207811503900c3d40c99180c00c5000d40b20f03500810380400c09030410030640200d215422481041d0a0f00c00106007401c5c031080180204500c0300d160354082d281c17608070880c0c244000c0420a4400440f0001502d14012804250310701c00c001c2480d68241c0001c041084640d410100ea00b0525034000568501550140b40981c3e003900418000303030301071140803400c000c1e1081d40300042060b601c40e814030100110010790100da440c02c07610401040c1d2101070004001c0c050440d009000419061003041c0c100030421a001003c499054182c0d910801030000304106054220b0b10954200c402840c0c000903242954001c02e0f2070840141a500d08248542508e03110035200d17040703140c043e5611040510500e001420601400e40040d21408548142c804002409240c411500021140e078044400910303a03629040144d01d40084180ca50400d0b00c0554820155906203e824403d0034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 806226357 1250 806225107 806225111
    0x10e03040f090b030f030a03022107081801020a1e09050603280b0306150a0b21070e283201020f25030609140d030b010e0607210201 58
    0x7180144100580d440b4190301c5020790445e85e01c2d00041100401203880058a5040c09a602d10445691450a000e01e00000190a03508024400c107954000c52440c0201c4c00c45009032008081e842c1454200d100c0d0030704a00c0825010020121040c80d10344000031b480300303d42480281a40e8410124400b941b040b00c014000c986c0d0784500d1689a030f8444500840081c18202c20040c80d4450808665941005081c272038427810000041c85003a0b40c1d407144031014111642d80c00d40c880320002c1c0040d17503858030366903240c0c001380901b0006143e25100b0700202050b11070081000c4030192440c1800541000c0001544501c3d081c008804038040d50341140510021001c0441341c861406901c075103c0c2d011583e078510a04641000d100d10100c14000100010181c0d284140c00418901e60000302a840c006940000c1125041480341c83c04d015040c101c1c00b02c02c951440942d0351401002134120300b1240443c80003404500290b0340e000882c180040a40429442074030388880f0101c107205121403000c4c60a800d03c0050b9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 806227607 1250 806226357 806226359
    0x509090a081b0d0c0803040f051c03020c07170a02090903040503010c0e0315070504051215130210180b0a36050603010f0b0703020a2a0e040b070809010e03040f 70
    0x204100203000d80242145445104602030fa03440300114840980043d088c40e5882c8030800a220061103031200c188101107040c5081c240c5407078058040c3d0850241c00240e805050340c009803012410b0030030180481c4032805403441e40d040e41d00b00003030001d019298148501c0140004190740d01d0900c18082c000c07840703485929603042c54204061901c0003082244980e4082c94050080d925000400c0d0b40a6520407588410300310145040c0f0f5282c659610040d512181e080740c144134145990402d80c0319964000e031030380031680640d55020344e000c0c22807030148410681440744c108555903501028086100192030088400701003c07107100000307824980c0e05506032100501949154000c6441440100010f8600c035017107601d000e100c00700c14900c0c0e1045590040b40001d82904151090140042d03599000d00d0120840800f0754200c0c00d0f411041428011603180010040741e50100380580038403070b079400102c1d203601d03903034a040880c1d080780081e25024080d92100764510b100340d003d0000c0d0002d4404003803401202 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 806228857 1250 806227607 806227657
    0x7260703241a04050702011812050d060b0702150304050616030b030f01050f130f1202010207020613060206130f120504050409081213200a0506040303081803130509090a08 75
    0x144c501400201c15a85800c80401c007a2060000035000d450b04074100c03603d00200700205803000c3c85004602d6400c2450a000030400c0c44441008d03011460090310626850b4443c174407900700610007501c0250032a03001c800010448551030102104650307003840d0200c4c0903014400032034605001c500320a00181d464034104440e000ca591b6a207035008055003a0641d00350a19210000141d002140141c80e04400d80b25000045000350100c60a00d613004d17056030340c0c80c502000c20000040150003110018080d40002c190040d90031602c00e4600d507040002003d01c402141e90709000200c520180205100062200003a20742c0d035031060034141030054260665540310700d4000074040310024051f080190b1010291000b0840341c42040f80045901002c0103d030201000001f188500580d018070b038031140014010040542c0001442d005810200302c2c82212000c1580864403130003058041550060828810030403850310b8034055802c41c8441e000d41c0d00c120301caa2203d1005601122003034502c02e1140c811a048 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 806230107 1250 806228857 806228861
    0xe10050106020f0115051c05010e0304080a120201020f19030e030a021501080703030c0b0c0403241503020915120f0109050d0305070504230a060207260703241a04 71
    0x10185074145c3c0e0076082410000013840004400b0007282008010011540c10000c0950042c2c95801d44102120381350b5613150364180c0d44e40d4071600c04660584400b896070381c2c007a00500a45520040d001186030500c0e05c1020030450090361414100205620f0724500402414180000d002209056024046d4000020304211031400180c1c4442c00d0340d44100c204101095114228401c6c143e031107030300c14030340707071501e414031400c030b000d1030308044c001c00c1007580504500c0000700740d0070014441044060040c9900740c809030f0303010001d500c000380d0864201710000320384850042e2192141d110081c00340617242c0300c540b0900c1c5880b00c1200f0060f000d0b9075800c205018407004200303203a0510068601407042d0324001c5c0005000f40200e10441c0303003040000f00c402803090951610070303c40440c040c03c0513810300c0e514400203580350400d114102c4020071005562007045458803200d00c2c99078080b402010b040780395541d0040d400b051580c2c201c845801c00726141d100032449000d40c940c8440c4ca00100240035000408005c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 806231357 1250 806230107 806230121
    0x606032d050a030806030a140604110306060a06180b07050109020f06160209060a0321031a06030c0304030c050304080c090f091c11032a010b06030a0e10050106020f01 73
    0x454040303000c00c400007440002d0440d0700c07507418901403081e81c8613603012a1602448640080c00f0b01c1c5001014071070050006010352007207008046506280036030304107241d00e1301d0068440e19040b01008034240030309401640c61740300e52400b11401d04406a03031565811004c0e00a15400c844503511202400306501d460f0348102c0003060100d032800c2c41c02c491480c240d200450b60b00c1c03000b40103054481c0064420f5598850070340095810600b42c8110f81c10081840c03008802d03c4e40601c001c40e00d030052483d10712040043c2aa01e0210140105180d52a0310321042c1c0380741c01c003c1c401c0341080030590301140058003d0010b4001007000000910001030320800304109040c00804589041007810704101624000040d026a40800c03029110012103414408841880c44a0340d02c818038440058411424118225a003000440420860690041440a0a0a07103040381c1d82507501607801d1002c00c50800440d80001d03c40e9100c1011540003043e01455581a540c1c00d900c4240981c00003115190105001e0080320 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 806232607 1250 806231357 806231423
    0xc120c09280602030a0c0b07030216060207020102010509160303031104170a050c0f1008070c12110c0a03080a051803011406040e0609030a11030405031c110d0507030e030a060603 78
    0x903041c0100088024130200c0c402c00090001241f10012800d49402070707044594084081c000c540d15019941010300295000c114102d00562a0500144003040045006002e642c8c5007010340c0c01d624a1030f20100d0240000d81a80c0080e0301d41040001607480d0a0440840042645000780c61b10413135a081550801c120300354842e0040e651480200043c0d0703240385c0c1c0329200c18818200b0301b409880304901150743c1602d9400003007103c80c540100140942d04100e1284254004901300d50411030500c0a000e070104881c4802071004c0d0050083c165a18010b1307016040c0940301d15010030454107250002801d60f0b4504040403604400342c1c05000300790805005550345a14850b0050600742002c0034220b40d0b904c00c001000c000c0062418070000608414000c950082c40c000302100c0c039040035800a410426452404800030811000d54007a80d0640446c0780106e82c4002c0e2101400e102e05030320300303a5032030a003441c18941c10300841e800600000c41620613100658080c42811054113140c3d481c0110302c190a03a844 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 806233857 1250 806232607 806232613
    0x124020109210c061a2409010c05030d0204090510170607300f15120f0f1e020109050d0f260a11010606080c120c09280602 54
    0x1400120300122564620a2042c41046008400701c2000311500d22001c00c2c0108403a0a000443d100da03562a1014170254004071481b440301404080d20a04070155481100740b03000080c0050000c3d58010481500b841b4050803e5a00e00740d0b140d8055012030748035800c0035189070741d110288801c4146030f03000d07600a800000200b40030703040b220b0145995088010320310810042c8a40505842c0020366081e0512544030b64102844c0c079481481c00c5000d0403a0701154601e9a141444500078020304240042c2140d804100043da0201251294400c078181588250b4201d0054040400040c0c603908100e101c418544940003006500c520006110b902c903980714510a0354000c401300007044c03007915a01d503180c1d0b014a42c4a0313880820014403a80c0080c503c0c602446c071001140b010f05c2c5980006003d0b4000d000e050003085069240c4105448540056606000800c42803002d08120000101059040007c645801c0c0c2844400d800050006c0310b0704c20040c0281800859150f602540012505c4c042d025600203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 806235107 1250 806233857 806233871
    0xc0603070507060f0b060c010e0c0604151419080f07030c02030f0c0f0109030909150e012d0b0a17010b160c03060908030f13033501240201 61
    0x10042050207002c0c0c028200c159034402c04101d9130041d0707104403004c05014103130586401285a90700c2c0244200301d01c202c0e81d8024030903c42680d1800304200e50640f040b0117000004002503c1c0200c0e00c040506040348a516010040320000c500c4d80b00c06d6103c3c22800350745443c1300d4a401074100c0784120f070182104050605207003451104503004021741e0304001c0d002c040c071a05c42c5485103480d813814112040900701e65103032965010602d9480401901070b1001540180420381502d4502c810b01c40d49803044040c1c1000d10320041c45185400c02510301510030700d41c1c19107040090103142035484c2c3d0305903115965130840091070740d1806030031030809070885500d2040c0c10030310b600d003080c00318852013815000e03003601140d9030a401c100000d06080354041c541284080080031414030f007018040e8000d84002c00b9015890380020012499840a420150350543e545112000b58031420700e18408081804d0700e0b41c2c2d4582e5145071501c0c080c503907814000d20703007100c00c1d89510110780c10710301ca4918840b00d030100310790501c05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 806236357 1250 806235107 806235121
    0x90f0405090601090e0319030e07080d0c08090f040510050112090c0b09060f0a08061f020d0e04020c030706090b0609130b0406021902100507090e0f0907050d0b04050c0603 75
    0x20b000d0381111418100030414101c2d5024880c214401c00300c00d0a0b000140200d4140f40c650b03d98000c11028a07a0030803110000d849510050b40c80900000742800505002d5515001910313134400b4000742c8002411401c1707201d51460014064071811100036034a0404003008008941c0d010207480401100b1020030010305001e610750095482041c060140c054000040007541500d607401100d0440d07030005a195190002d145004000b001c1c01d448461060004040c1c0074080c8604c031034142e291440607001004c000b82040c40c180d0303c0500e0590220b0740140d00307101c000402007041c0024880d83c0e210b811300049001c3d40c0c0c508082062000b1f001907000f91064410085240c0c0751220200c074007900011040000e039218540751020b4400c0d86030b0b80708604d01c050f00c0c20400b260002459507041c2c84078503041c840e0350b980d510b0407915400248203030b000000002c400705000780200e00c080e40d040101202550348003a19000403a9140075201c0781120b00000c544100014030206106010381d007841241d00782c1c55414910 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 806237607 1250 806236357 806236363
    0x10050405090408160209091f0c020d080c090a06080a050c091311041a121f090f0b1c211d010e030d02070e06060301050d2a0b090f040509 60
    0x20002080350f00002a040d03013865186210703807441e030f034003e1405425180031042c1d9902c5e10800c40c0300c00c1c0c82c2405501070010340301c001d014840035030b8900d43c02032040340580b42e8100c480100c090400070f00715008011020701c64490400107806400103454100e42c81c02c19103140c1d0b0807160014031413001030f4000d000c0b10136070f80d031041424094900f40d1000414010140c4600d8041d0b0310450303110300741c5501030b03040824034058000d002c0c2c10f40185482e2070108a50b81c0c00105c8002c0d0000c03000b552040028500144001000b503400036000341c1d103520b00003501c111501c000c10b4502c1d0003044014022008205000c0800541d100022503070304482c1c40b40203006c3c03c1c1c0b1030054070304490702d0401900700106c20071010250744510380e9840940f500a04546591110b40346c069100c40c40d901606049411040020383d4905040d001c0303a040300d10140507600c00140c1511484081c11922003900c1034600080780005800b13013020f4564028100302d6907400d0396090300004001440711640c01c401d010714101b07000c2000240d004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 806238857 1250 806237607 806237611
    0xd0b0109090c180906212d02090a0608071710150807060504060c0221060a05150306040b0f070512010f051c0b04110612041b0b070c140a08010c0e1005040509 69
    0x32400c1c41042c0c1c03400d441c070300203d84190b0341c01c7c0c1c02d042c80c940c0b0389021604040b408580203071181c8285480d48140e510030740e03246c0d004164071a884030104008038402c0802c40300c00503000034103440c00d000081c03000d070381034504d451134a46000911800030f01614500b80701a1000b0409420450700e41441c1010160814612800184c41141200400c00e014110314442580d04c0c882c00c02030342e42c60319101154400502c000d0b52103240010f9600860451070900041883c0a43d411810f81c202641e224040c206103081c000340400308020341800080742080300030084501a244006500c200c060404092002181000104079004043d40061034080350045213080d4009821540400c0c40281050120b405032286101020110703c3c460100420700404a01c1d0711070102c464001d410b06143e6580c8038142900031468054245400032004001c4103111880c0e484200001914007242a03036a0840079084800d05510100410344940c00c80d12145416109101004424200715007042c0c100001b00c0c40c68030700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 806240107 1250 806238857 806238899
    0xc03060f06010f050706022704142d010f09050c0306010509040b0a08100e0114041505040c0b07030f11031908041a0405030a110606060d0b0109090c180906 68
    0x40b0f90300c014040740c071038412510001d8010030300755a0340c0406030a0303c002c2e09030031401c038011030342c20700311200c82d85403d0180300e010442244064491362610410304200180c0365824000040003642c441180c48412150940204840886192020328102085080e00d00040091003285803c008020860b0703048815510500d105580001c2d23000b00c140c01054406a035034000c50f03a0b038886c00445005030705503500700640600e0640024031039915030080d003207121803055034020304100030749040311400c2445500503940980500540451300e03545610350b0800380d00c807500540c0043e04074054803c0050b00018247c1c00800300d600114a819800c07102a030070860b10040d10420810200042424040c01ca56607041043c3c1c100c0009506041906e4100c0d507960006051001107501c101c026159003001245d518442e04005d04400d1400b003405003820010b160103015a4180241203802040540c02380c81400ea0300030ba191544c00e04814060294100c0c150300da40688090b03410090103005e450904a241408600 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 806241357 1250 806240107 806240117
    0x30801140406210201020c0411030402060d14010b0307020c01172a040f080d05071a0604020c060406051e04020307090213031719030e0a030806010e03011b020c03060f0601 75
    0x584140000c010b00540d910040c240034403405101590402d8902140c4624401d800700c0c0c002041190900041c1d0f28001100c40032004240001005801c1c0000100801500e000000800c520105603c0500c606e0030307000000079200200170004480e404012520401d0000d003081001c6044180f84c21040c09001803410703999030403030070100d40344240318015400c450400c000c8090302c0b2500c41000c000140d409100700d4565204582500108600500c1140c61241c0c000100895088801d601c03c085840084c01581d0041d40c00c0014407041081401418021441440c2c040790504140700810400300e0600001c01400040e8018040140d800060040444440030000358075502e030a000e028021006910103460700320740101c03098100704120010b040c954445401c2e400c200224200440c11118801c40c0315860b40d0202640602003401035001c60b41c807560514201458084460109094900301c01601d00510074076540000764503010312101d10608415030051540b841d015416020622000d400181800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 806242607 1250 806241357 806241389
    0x1150801080c090406020c0307020d080d0c081909140607090e1005032a0619030f020403020105090f0312180f030c01050a080705090901080c150a05043804150c030801 73
    0x903a0234800d42d00e007150000d103160703854025070804452950081e201c00c401c503407400034600c9040d40500e030018044c0300c0c0400400e00c1810403040a400402d00d82200f41c036150b80560209030310a2040000d82d21a603469600c400c0114542042c071002c07040f002d409032408010081c001d201640f40022682400d1044100c0000130b1440d480c0c440c1d00c040801141d213134002038000b42d13188034030b440203040320316618043e5001c103c1c0040e640c1d1100103c0c021408020b000030405c03c04000c81d45098400e0726250b1000805681c03580c4c1070070700c824400c0d50000d102501d03103546510045215142c005021303803241c01d0580c0688801c01840000170111f00c01d9800140c148501100801c516600c0745041e2890740c02c025094803440e507100c0404a1307540c545504481d100d04540d25120310000d10f00d406840040040e80c0751176080038100008401a104480c03c2c402050108004142040c0c2e43c1d811100e80e0b444807640016603c5e805d110740c1c407002c02c04001c414002d1150000c04200003a51084103141100c0b201d4030448244 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 806243857 1250 806242607 806242627
    0xa0f050a1d06040302210d0c0f020402030a0e06130b2a070309050603100305010b011419030e03071b0f15030203150d050c03071d0117120301150801080c09040602 71
    0x3c1c01070b5080650010740482600b41c00a116980010326100540308644005a944800b01c0301c00c002c0d088018550b400000070000103003040c1d0003458010605110109205603218403141c43e050302100c1d0942202116510982401900b15803075802105503c6061840c0c918440200401e80400c480b9036001100040c00d0010326200b04186006008002c00790b0303642e410098100d030051081c034001540c2075480c105070714081b58013440c0340200c07018518281e0b50510201c694807000111101000b4400d064449450421009003070005081c0c40d842a240303c0c14880000b81313152100c0c5080d4000302003002c24007000744580310418114880c10000381c035025a0725a036507582c0b11031100d4250000c5070840081410b40040103004600440040da082e401c03194040d035518454404101c0720b00800c2c401800e4000180915500f410305181c039544030350304480c10203038400f0302110740d07031f000342d1022000c40c14005881404030790000c050b5004000350401486401d50803000101001c10150000306410350025414405c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 806245107 1250 806243857 806243869
    0x8010e040809130501030303021c20181f030b0d0f02040b01140310090f0c12180209010e0f0a0e03030f070908030c0109020909010603240912050a0f050a1d 68
    0x140680f90018409542e41745000780c041e41100c901c90305060103400e40c0740c002000c2849183e41100c1c84038035000118060700030314a12540240444641584061040075550704c4502d01070202d0b5101040d044101c04541c200142150329a144075403056000c194400085001101c0c1e196109130121400501003081c5c0c00142c4040170034000c26040c7c1140807081111941130301e04100211340c0140010300032402902c00b1001211748005102c00810f99000750100c00030a01e5011300210441700002d040c03421066000034144810980c0b0800c2440d04842c2048800341c11828002c1c0c125408020a0020101b035103d481d8807800300502c40403254140c00d0000d000c0b58480d4203c0d400610040d01901d0b034412501600e5406800070b544140c1c010402c24004c40c507114814400d2b40200c94000c4043d043c08640e0849410031b203002000b054140540b540d243d00302103210060a0144540240c5415550b07a140080103085001c14400d10b4040c80014002181d041d13401400c40359044000050540700314110710300080d9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 806246357 1250 806245107 806245129
    0x903030c080f0d1d061513050402060708160507080d080a02090a090e0102071703040b04020d150204060309020310060b030105122a131a010c03021504030206061008010e040809 77
    0x2c0f0706040040290981c20250035062102180c181500c596640da59403501003c0786c0d00e00d0141c0c02500461300381034120120fa00480d049440100f000e0300d00141c94640b5030084e0007038107031151b071420008008803c2001c00c022100c003c3c4008400b5003511a18110701420044005145200ea950005400040c0b5031b280c4c80e0b001d0203840348803030422000e01d040d04441d00075000701900302c45001203802210f803030301c0300401564804d1f0f0344455403000d6a034840d0301f80080c80c0f1008030308072851440c0c2070028803011b01e1400501701400c5030781c3e0001410781450041502d0680945034400b44146005424025110b0660860741034580984480d18581d540c110603a2030000e46000741780c2c0350003000240b4003110301c051582d40002c40080b1160002140070b800c8080840f06080740e650a81c0010b003100c064594001c000c01c0703000d640240140c46115600c51100940c020003180d003200140c00420811590b45400a11040c1d94965443c1c968001d60505207044100f5102400c05000100c022070010050703511110109 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 806247607 1250 806246357 806246377
    0x60a0602010b030c2106010f150201060b090118090e01020315010503160f0207051e150423010309140a02130b0a0506090402250515070509041d01060b0309010c0903030c080f 76
    0x880305c7d07030b40d4a15081e048082d80580e01600030100800703001070344140110002d56481c10361103440d10962000565401452124100e1080038020000885180130320500034103002131400036a0340d281900b64036402c6802541164188241841400101007094000ca400010141414400c0100760705d000d174584050b0354019980044002004c803485415100c050b0aa03d03402d880d00343c0c2c5607042858600d098019070083e03c0022003100543c80c09103400411900d400d10040c100010032003859150800070091888000745550701542d602004c604002000180030f01c41103038200020400707480000d00301c40e0a8420b01e84690408603100352143e0703842d070448099403c11040080101c1c091405041d003548154811b480c94000c1c0f1050030391004030320106034481c80d51070307481a250244450801c001060340d03c03c0c00011447c419450384d007141c130034851070024040c51280903840c0d01d4070902107403c0d18096185d032003c00c160b0140410000390400c00c0d0211450348a0a95a11001300c00d0b008280c0d4060581c2d08 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 806248857 1250 806247607 806247613
    0x100c0b0406061502070503121207080c070609240b030c06210103051b0301111c090c080318030a0302120d0219080f100e071107030b0f060a0602010b030c21 68
    0x80b51507070009440402c1ba80144c041d161880300c0540c40000d540980921181515041130014042502c13030b17280b1540c42210380136034908000c0319444500403a40000d01c120350500c0f02151038030038800850f8503845d986840d00e0040c080548160f001c0381c0c950041d40807040c010302d0045020300409481c611164100c02d462801c5000c9981d43c1d040c41591207421041506800312610b406a90034101030180c83c15281d02d40700d10300d2400e11a000119001546090481c0402c0d6913003200070000b601e076501d503800520440006545692044021030000c9005601840c03190f80415901c00000e030300030a5050341e031240244040d4440c01904d41d0040640300b203a50007000da54820400074003850f0040a0070307004140540807031340c41e035a5001940a0126003409407a11a6a40100040e4540c0c8603074020601c0b4400c81040d5140550b4990b1128641c11042d284c0002c0c20130004204001070800141c4040104441d200074007509404e0b002080d250f02940d180705000703100c01c01404005803107400750052841010411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 806250107 1250 806248857 806248889
    0x90109170901170c2a071406090315340810091b080c1e09010c0b0a0e0f03070c330e1e150a03060b03070c020f100c0b040606 55
    0xc0c9001a030214580c005c100c0c03140c85103000c4d40746031081c0c180781c0780b844100181905814003544c145584000240a07501030340030803014441d034805000020050001c0c0302d40d440c00d4101160741828a0310701c000d500f40e084030640c0361040b515207036250b0000a10a00d0824044d96180c001100380000300c0380c1c00c1520b10703d040101842c0201443c1c403a000521255075035418660b02ca45d401c5c1452441074201c03107100300c440102c543c65000e804100905400030141050b5480394010765510b4509a81102c2e07442d40c8a5840704025842441030104410041003000550310f4038101c2c2c0c3d1102510001401401c80b51240e00c14418011200e5440484581e200184248011003009100800030320314a0aa2401055500034902022800c1e400c3c1320180e50b001000c3d14055400c19504444036044800144101a21900000b038481c0c5118015401543d6550341d030040d0001e00d006025020b0101d8051600032000b80c0058a0308a6001c03404514040d0b10801c01c64aa03103032400c01c07001030130b03d0b46c00100050010030341d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 806251357 1250 806250107 806250121
    0x3010b06280e18070306060504030b0a0b0f1801080d2f101b09140d0f15050412020114010e0c09010908331e04060908030c0403050609010917090117 65
    0x300d41d11508055509010b1b103602c5e0f00f002c450074081e80c400207181142401c0400d50b0031095400803602e0407000b03402c1e803003030804503000142d0a001c0d05101c24203400d0740c2e00060111030020700c08103d0a014074101950030342d80400314035290711002414502c04004040c010441c0c08428003501000000c1e50909018500c2c0c0d0310000c0c80d019016048280200e1516000001d49072002540c500c1c00c00c500410107030b00c030550342c0c403848840c03640303c101110702108004181413040300c00c0c4501740c040c0780034040d080c90140185101900f1145588000365848100c900100100000840c1181c0c3c0180d100000ca0b0302e46000340c005861318500c98010303030564000c46d0600c0d1034402c11449803071407145c010303100082c400804c01c0c0e00300310000c0152180c4403081440f8181d4100003d450400d150032a11a01c00095070710b803182c880d00a036400544002c043c0c0000001d0410500034100601a08a8400300080180300c006503280b44046103c00220804c03c000440c10035456800740c4c460b0030007410141611a200c0c60425 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 806252607 1250 806251357 806251399
    0x60f08100911012307230c0f04021b0a030509150306030c011407050105010e060126070c0c030c12061b081b09040e01061508041a0a060801020a0c0203010b06280e 71
    0x2078182d903c00c2c140f801b07080001c880010010380303224001d02046201445c5c1c43c18000070f035100d214003800910410a142070b00080400001c0c8040340240e0b034664890030b1000402092009145d00002405014801d00c0219503010803810300d034080c2400c102c9802c00b07280c01c0b02c043c21300564101504551900740005290ba602c040c3d841c0c410f04090b40d0701802c076031250500c2c480c01005071240025001c10700c4005000c8900a1280003842401250341030700c1555a03644042e4603580c2d0750401700039107802001c00400c000440c0960390002c4403c965203c15100c5104004002420003005040a20500782450000030140c004071030303040d01c0c050800c2c4407148482c02c109010303041c541300e540d9042070008401c0c80d007140f055119601455100092540506a2140c04029414054000c006541d680d14000440350024030041c44040005d80300c00c651518140105400c40f001984140e00540c010080381030030000070104062032001c07208a500341404044012035940d0f00c062551138010801201c0301074208142c1c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 806253857 1250 806252607 806252633
    0x50d061b0c0308131e0602091009060311040e0f15040908040305071a1b0309040614121f022d041e0609060819060f08100911012307 58
    0x30f40b1070720345680350050308502d60001e0040150810152059011812125030001c81440b806044050700f00840d090014008424826040e8003040303400c2000c2042d43d0b098001c804034141448d44460919240c200784103920140102152818005040007409061703003023080314041800603000308009051407408004a070300501040e102d038407418000203460030803282101c079212105660305082c400404407124158000100d445014001440364014a80b03580c4101c50007051055000300000202c2d0045c4080f201c104480c1444581001c0103a5660320100002400c01664420005958070010041c05540e800e14000e60f03614420009003d18030300f56684040d0099803030b37012115803c081e480b15515400070452107001c01040f8581000c2082038007900200d640010381c0c0064242840780171520f00c0407a025034124142c82e41c01e85800340802d0001300000d49900309404410480b944042e2a4510301c800602003441c10031203075418826200c0ca0302e80e451f869070f001d01e681494441900b85441d41c102c40c0e031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 806255107 1250 806253857 806253863
    0x7033906200705030c06160510230c091c1e03020f0f0c0d140d0201060f091a0d020112050a090201111c03020a0507020604080705091f050d061b0c 64
    0x9140c1801c005101003607520464500034001d1540316071880034441607030480900b41c0046a0109030b410082001400080c000140c3c2c6640010100120300040814860400303001300d00300406820090300c50003003022150382100850341d412031384d10080083d040221728000010b0400314801214400c084040c841c0c54100f510940a0700c0c0c02100c2410340c265983c4c0c240c641a00150b00c1b9404071802400d10b00c034441c0c04107000d10440d400c4e028a02d4112843d00200d04880401070b995900108440607180040348080d004080d0140919500d000200c2035016420251511540b5480c80201c11603020300d9100103001d05288092189140010710b003c018002c1500503408110640b003c2c1d96a2030010402c1d800c48041c14104081541092600b10002d40043c0088001d0210400180c00036a40303000c0a48000c0c80d1704c000812105003840280300c0882d030041c0000c00540c02400c2d8882940654102c00c6040c0c50007921562184400c3e0304000016024500150840300c488841c010000c540c405203d42917140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 806256357 1250 806255107 806255147
    0x1002031f031109090f0607030507050d0515090a061410020322090c030504200a05030a152f180a1d060f0d06051807061d0307033906 58
    0xe44e420340c4544503c031900d413060054000f50005211036000c4c2e0700903900410246402030811104856175000c8a5040e5604001e55040700e4180d0864903140a103650300548018090000b02e20f85915101d40e401800c01040c482d8140402d41c104551081040c0c404071060040b0b017440113031070040980300ca5800350058050300350900140c3d040e4680640242ca001ea80e00540c114042c01c1d0749040340107111021440282d0040b4081c0c8005207590b401c1111011850181240b01030300400c054040c400c9500094000c0c0ea002501c802e80300011b03507403c03036030702800110096581da2403025211954180340d00d401501c4c0c1c0b042c020000850a0a0480020203803546848c400d0b00f0903440315010016030007a0b5010315036022048400345000200c181d00025041040541d022625040c0440500e081440c0fa0b0440000a000401e00f407414140170302c44a003054074150b0160007400d04544602120460084103050f210030007581180b520014483d100c03080c01080013602011030388034000144900202a40b41440d19 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 806257607 1250 806256357 806256361
    0x2d08090f0607080105060304060609051503011506020d081e07030b03010b09250210050705130b030f0c0c0a0212030a020c011803020904050f0105090703170a021002031f031109 77
    0x100041c1040c09507880d9142c0200d141c2c6480104034071540000c1c0f00300c03400ca4851100081440350781c00390320f000300303021300c01454204588018182140c03140c014165040d1160718082040710340128400e0b0020080e40b4120040355500340b4518001c003110051482c5840e1207200304031000d6403661240c4035a00c0210021301041d6411402c02001110549540c5c180b0390724103002402e0a184d4020480c2503e80d640141c0d251420200c0441c0100c03001154884d003c80d00c00920348007041c540720001e1008e80388402c1900c0c113504020101d41d111840080100400c0c41c80001c20421069041102001903a4020202c06203582070207a45505c0b90005201e040240c4118000b01c80e9640c020301c88e480ca034a1202080d100c4940ca19020001e51840282041d0343e103000e28011a02480800c6c01060311602a15008040081c0b561403d03221504a8a00700fa228600510540c8070040c1c0c08502e1040500201e10090384030b0301c684510240a08820031803c840e0f2010250010410040078112842c0c0300f81111040003075 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 806258857 1250 806257607 806257633
    0x1f0504030c060509210709090c03140706051603030929010f080a1709091312170a0b0f0409061512150c0e0402070501020d0e010b102d0809 61
    0x3074000d1500361a8081604c0114621014401e414114003100500889040c1607447c2c990404944104100743c4106141100a0084c8040904110764031358010009184041c6000382c010007500404c183c1c801c5031901000050181446500320041da40c1d00265a81d103000b00d41c04401554034048180d0707465550001000242050310004020100c84810014051040040e135624451a507002c04d41c44400d034051115000d291950807525100c1c510708000418035295600b019001142051000010000f5811010211800d11503003aa00105410000700356811100006004007081c4107401e0f4010703291404c40002d0102d41d402c0018800c07103410019000f10f40b030b9142c0c00755100c614000941180c0c2e00d4130610002c084290f1203410412014030b4420184113460000609a0388084025109690080f40098041d8214483c41c0c5012400400810408250310041b6a01d5071000002714240700c2c920a5014543e00b8481a1240c07020420018080741a50705c00c0c080d10f017610994500c031080c41004658100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 806260107 1250 806258857 806258867
    0x6030606100e270c07030915210603120c1b0501020d0f0323010905060d02130b18100602070e07080105060912120a0e0f060f091f0504030c06 62
    0x7000019035140d10115a5400910555002c2214840c10521100c00021440d50741100202d024202154081783d464080b07040080031521190800030903e5021000e884050350842e035000000451005c66003403c54a01005800a140f650b00c0913242e540b007803030642d038056840340030103a44a00c80c1250580c425a001104995400e0358082d480c05a440002070704105030007a01041500d2050703140200360b21904070002d1221005440c071448040d1000c0d0018040800b0a01034154402020ba48000000b0b40f02e4001813080c805640c25400d4032503a4000c022040d0302c171440070300b241d20a00d8000c52014140301080c10500300d0a07100303200050003030480206000c0200c40e0054096021951703011404c1c2d0074030040001507440032028980c000b20072070f1803180500c0b040c420300b00c4aa022011143c0c4440c040c101c0a810401ca0405d030760300c2003012002d03801c140d030382d88400c0d42e04111154000a40343e81c0c80c60081038a10504d0580e01d19000320140d511104551b0040050081d41c1c400d02021000700d94a44007034034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 806261357 1250 806260107 806260129
    0x120f161715180a050a0609030905010e011d0d08030f010608010b03090c01080c0904050a0c0e0a03030c12030e030d0207150614010c051609020706140c0d0209030309090109020306030606 81
    0x1401c0ca6510085000100784a080c0c911034031810058408a2825554191501c1907141c0f0403200251244901018035403c0341042e4000c2c4020300f051030071b49000300e00003002a01e00c032040e081214580581c07102c0301c1e10750010b020030f641e5010a140350740c0c2c14007210114403e9001d100d0a000110260004169580c1320401d0300e01a088080041000300c6141c0700554211a00814031501071034207120900351582c41d03001e00e5020b55a150350002c0c0c1c007420780b0f4000700b00342c80740c20303032140500c462410030400a5408010303001a01c1d00020180d9020042281c01c80284c100003800d41c1644c8404906a001c40b5040d030300801e14213200c4d50200010950465003881030300d65a100f88030310f8014000f07100700c0c90b501410701d1802441c400c03000e40d20051203d90040742ca2008a401c58105981c1c049402001c00c000c5125484c0d80c0184048504003d00e030080034050755100384907102d4502c540220314000c450710b080007525143c4000800b80155581c549240310025002101d01901c288141c4000c55864200000602 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 806262607 1250 806261357 806261383
    0x10020f190b130222020f0712021c2f0307030504060314310b090c0f040504050303012c0a140f0c0405010c15090305220b040302120f1617 60
    0x2a203000d0b403488502d00c801503400348121045400300081b0410690705801081824030400180101c0410454000d2078004040440361500c11105829a1070907084940009440c0c0860102d0102c040001c41c02e0044105106d8050303032603c40411a1004c1540050103802520040d64042203078011199082351420420b40c0c4140b502d50301780210010004a58644214082c003d64100e902050542e0301c03001a081d0441d000b02ea02d0b013000e80940e000b440c00d41d95507524901d08030740030702140c2460b88800d40c0b644030620582170345203211055242c0f42c800d81400ca4000000252160326989083c4085202070004082210003122500000402d0707102072010441c082c40350b0350303045030500d400c14005590324500c142c070559410010910302c6490a8280c010341c01128400c0d038a00f900c03071100254440d2900c1c4280e0b00e100c070041e0000303803d009900500044e101225011216100c560030b404010350304244c5540031080f5140a590764500d4070140401022044a0b8003054031400c2030359135900640c0324504cc89480e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 806263857 1250 806262607 806262619
    0x109031e05070b0606090d060609110306031e070b030a1418060109020a030f02161b080d0516060213081006050904020420070326040b0610020f190b1302 67
    0xc01c000c2a070f603601071580301102429071131405800c0b200045903042c1110003111159190a414004141d150048001c5008200fa03128110708040000948540c80301e440781c040b41c042002c081c4c02180301000700400401242600369920704049240c80054000d468030100c0f03e10418010804287d886414800d410000340b0281400340d08150010340690304c041c3c1d184007096210f41c002403000004c0e200802d04122001c120442403a0380380380c40b0784190315503847e00d806080d0103403081003402c5001c5401c520440c50340ca030550b0b41c2c0d0342460580340b00030f016001c0580303094404628080d90000b51a000e00544d00c40031300b141c040320700e4401d08405403100e90040741d4000c1c1d031920210300142041e8121501c40f4800800142440700b40d202c1c4441e10380c000000a5002440d10590080c4540400c003010400720400c0f01c00091500d000d4691105500000c0c2c046400340b0760344020031101c58428440d81580801d0b01096440d0507000f411500c5200400c01d40070754185d03041c0d20100c0c404009060406030044d40c09042 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 806265107 1250 806263857 806263867
    0x601140a0e0114040801150b030609040803090102070b01030317240f12011e0f020a091e05091302270118020904060b03011d33120109031e05 62
    0x211038103602454424144201c1c43c0e682100d60250300083c00c050410040001014140d8042003882410640d004442c601410020b1000c0c6458180c400c0354000c0d003220310301c3c0e40e94480b00020b42c024402e8690140540041a001104141d844032245801084e0030302c84040985804444d00720b00340240c401400e80517200801c820b07480c207000500049903600205201080030707030501341e81e0039512011059455080b15000504081c5000e11881180380a000070840c10301240c920042e19961540c0240e6032141d04100c00b502c88a403800400b0b4026001c0500500141d0910f100c52060360406d01004030b10030059280c5000c10809024a24081c50f071416820940310727441c0c9800038880d80e0312010004c001603002c00103c1c5094aaa02a0000400c218052240e403985043c1e8850108880302d042080043703441e40c280600904c1004802005040b050030034542a900d4211ba407411900c52006241c00c0400904d02100032001940240e0070300340651500302d01c0e00115585d4440010311030340602d0202d1400d0003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 806266357 1250 806265107 806265127
    0xf080c25140f04051503070611060417070212100b0306060a170f010204140103180b0c130503060a090c171c030f1b0f030c1205040606030b0403080906060114 69
    0x5001014002d06010101d2988002240075100d0840d001d544509044c0c849141c14181000030744014000c6181000841034103203803068568402810203024001444601001c13a69000200d5a01603801000d12000d40300072102c054443c160300c0385041a6031711f40001030b5183d0a002c1511031003001c0044c200e45149013044500c190b0005c2050400b00303184540020040082c0f0244004c0000d4103503540c040d80311902500005050748c0c40a140500c802d41030b201a00d00003400b03000746540001c800c0c4046600d5000031790001030900003a43c041a80361041d00227228081e500350b4000349829000701c00003c3c0741c6031038407144800b4441806107240c156228500404104100342404401e01499141c0400d000311058110800e0f00c0903d81c0455000b03280d802c03803010490308030103041d00d5900c1905061000444d00318006e407007a0b88102268032459201c1c400203040200c00d40c01200034503400081c240740c40c02d040c1002014100c1c200c075400518404d200205d007a660103035900401e0380100e000910303c1c00e00424 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 806267607 1250 806266357 806266379
    0x70b070212040806150117160e10030504060b030c01140706090b04110a08011b05340506070e0f040b010309050607110105010e0705040e130f080c25 65
    0x9248100310300800c41d00e4580461030300c004000900701d120041c41941400c80c1c103250340c0b05c01d5003919810300066120700d00e00718102240362036000f507190800e0380842036500300694440001d541d13165031006c40307c1c001e003070320b0b90705a40814002c90162108000e03002600d0301b4150b40b461154405c60105840400620408003c2401008004d206400214418003944e803100c4203000c1c16030f03040320300080f130400c0e00320035081a60b80e100040101c0781c000d00051401d01c034084095107620741b5080c1004800112000700c050240510005540007902d1a0604444481951103066810700300b02c3d40ba00504010501d0070740721780420100800010140d030b100d80c2201003040010080d00c0121418141c4489841000c82d00c2801054803c440f00c2d26885105019010510f0031144141c1000320a0a00501404080f950120a54090390b5070703c100a4555241d5454480509a110200030140d9033000034181c01c0020300304c0074001c1101c0d0f84c02241c1603140c06814103075000d030700716010700011840480100800415a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 806268857 1250 806267607 806267611
    0x70201081b04030f0c0905070929120703061d010501050d020d2904060915090e0708160302040c0e01120b042903070b03070f12020904090501090b0c0f070b 68
    0x1050070a8079050f900e40c1c0300054000d04480c00e44550341c140780e08200506490083c81e60025162420714030705420b000001298811030910840400a804011002083c441003212b4588002d406c06c41558900380030014003a0189004a000c18040703401e1440c100c509051025050314016103070107007800c6c00071160800a410055000124a81321064006208004503030786c000300000c20301900e00700107250248001d0350b015074010100c0038074000d06981d06a8072890fa6605a8050100c0450707041101d9042c82e15001d01ca80060006018a00d08004060300c08095a02140d1003075600740081c450516060300c0c80203032440c4003800300d4021a25032240d040306910a4119043c000c00005000d9680f00c213600d186003401d40e201c65a24048807280d00c5628003002250004c0c003014119034507514002c403004001e01c83e9070014509001d00c2845201e680d40e56070701918031003500604100300606c041c0c10a24040d00706140141c0b02c0041403804035800302c1a4904455090260141ca645056010303951308041441c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 806270107 1250 806268857 806268901
    0xb092b05030601270905090c03060402063a06090e0a0609060e01090c1707081002030a3207020f03120c1b03070309090911041a0306100f08010207020108 67
    0x6004010b901c00300703100a800f6005001c50041c0500241442652022160040d110212540c800c20239245e803650f0004000b84c2c40790381669041d40740c0d5201456400c2a25468281d1030404d0909100c108105200ca80c0e07a4000c410459024841c00e59101d2403501241c100c01c02d00c11150b04400901c0b80400c0d00340e044813610ba4130641c00043c4401449600c20308581e079900d81110803400c800010481c80c001c164100100312024000390031a18a4002201d548403a0882c11094283d00440010303211401648080d080200401701019808144242c0200d2003440e800035005000000000c03400b807a100091400881054034001c41c54080c2c02c1c080c00c0d02000e0001c01d9100c081d10b041000c003204214505180c00300d04040b0700110b0b2118043d00d4007030702001040d0022907980b40741218200c0492030303180c944100100e0540d400070703010702d0400c40000000d20f048240c0c0d030075101c0d400c1400b4140c611125407004940390034500c03540303484c1c80700d00541c00d0744100d0202178009600072000c02c00d185040c1090301c110040d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 806271357 1250 806270107 806270117
    0x5030403021e07060e091017010905010212041a0705040519080a061416080c070203210901090518010e060604091a010e04090c06050c0115030b092b05030601 69
    0x102c081800c0801000901024800390041e0f0f02c100126078000c440b403072449030100e4480c04c42d882c04080e60078502129100c0c1102c2d0302c82101c41c0383c409400a5111403825078114000359510a0308140d01e10b0001030070380307044500c0c22400d001c0c1403080002241c414003c20282e543c480c40d040c07806007001203c0c4542c0c1c828900400d2800c00004d4101c804000e02002c0d10312542001c64415185021031007014001400100c90a22a1a96482040c0d1014407164006400110300c0e480b04800e001207071800084075800ca00c0d40140b0000d0703202000210000d4030508500341d0b902e48076a1307106c00a212000341c02c5440507680c500d2000040c44010741300d2000d00d0780120080e00140c20f003039130b0b202e0000c29140c150103400504c000040c0c400519503440079900004690541c0c1c1030014050315a545c00f4a079030351b4130842c41000404183c25200d88d5082d000300e500100c016100259454490400d80031044003540c510625114038503118a013a600c5032074a440841100c400780050081e000c0040d6040d600040c07240e41004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 806272607 1250 806271357 806271373
    0x21c0203102601050f0403140c03070f080903031309050601020c0d020d050c060f0a0905010327060b1e0f1f0e01170a02030901050105010e10050d021204050f19020a05010503040302 79
    0xc0b1007442660b11a01100105281030b040604020b010221408841c410740041000100b0b00b00800104072009035900c6060b5026007030041c00d001038039020b6034824507454003001410f42144d141742c50340c44064400701a030800190301c824005a0b5074000322030301c6c21380107840000d07288c01600d0302c030406420f080e01841c10f40d01102016000110654010301d102c0c2e15210002c038120162590241c51403001d001c0a08003004500182e00420b001104403c060f0442800341040b4941008240d403c40d412201005d483d00c8d9001508802e00882c2c0403103c544180216200b024005041c41c1181000c181e540d41703043d2840410b02c41c0101240c03645099032009050102003505081c07070050101280b0310034801c0e1400181c5a080105c8000c0c250703401a8010350402c120601003c0e22a60361a00d000c07801c45950070101d50326641d0440300006805603038082d64443c000c110400c000d02201048440380c1e40da0050542d070300309102c104601d0480910700c0cbc0294120707480c0711050080794060303002507401034020700403680d8034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 806273857 1250 806272607 806272679
    0xc050111040303080a0c0c0206120a060506030106051e0717030411060f2706041e0f030303020304120c120807020a050a11030f01202b021c020310 64
    0x554070651085001038080e00070400481d100e88141120111107150280c20444980c0000c0e400380501e11403900140c0e003000200340510709039401603000300005000961230750380d200d070041c0150300035201000c9103803403215061540c4611441101c1d2000da210300c12011914103112032220a40006004441c3c0e0501e01d0729161084e515030b03000d026030034440c0026940d903100719840980c01e19000142080c0d444120516103046940c1c200c142c40941d044c04215452001d000d42e60008a155180d00c80c207000c4541c80703c00700a041d0b054009610075030180303814020703000b0449801c03a400016400050032680f820740e04040c1d2144a01101c0d60402c4051040340e160b082140c0382d0f281800c58041e4201d401c0542c0036412006424248000c515a1074079600070841c4600820042806a414615050150500050410180c4001103110380040000c904c8501c020000c071824070020340c0325141c032542c2e0000300c8200003015212402280e02c150301c900e042224080c0742c54101c4c103050307050403200c000a5011460780070038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 806275107 1250 806273857 806273891
    0x114030c0403290604180b090d08011a0409050703110c0c150a080a0b01051605030903010b061c15091103041202010209010f052a0d110d0c030c0501 65
    0x451038905280d80e1075107140b80031040b6603021402c01c2542c0c1c104480007410760300c040e0522035120314250f0300481c00c54000360000e10411499507005185490360f40a00105220001e004d2a070030031140c8801090b070f6292000d04140c61800178110010355820001482202d103076800c0343e60080300790308003c01c520000034070141058001e240400d08560020a0055442c5020702015410501c806507861403c0e91441c4000e0246500038100040e82d900c0764043c2d2140d074403800880300d0b40d48521008845940c0c0d00e00c0c0607a100d81c000f9610394400e46c00c040c0300030301c4d40c90300404403280c040c2a440308000862524001d000500603d1102d119040049100055440024000d002a564042d001c1907502d1034213280c58240000141c032000c0440e8410b1140c010140d07000b258510100805007031480d1128841100350088810500c1075010fa0054a00c100ea5a1500019440700754211038075801d09807851543d80a90740c0d900c2650300030002d44105074440110b801040100a6a07000e040089869901e5040b4012 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 806276357 1250 806275107 806275111
    0x5070501110315011d0f04110c2b020c060315010e10090303090b040b070b0a1107060902031e100f021b150c0304030c031d03060106180b03090a0f02011403 68
    0x583d0381030841800f103290f0b031008100c94025019840450075850207404507090008060380130b4003490351a5822405280c0540c140c40c01c01e02c001c0700f15101c41b13002412118004080346166010449602c0c403400a050010034181c43c1100c01400c41070030b40c1d0740c400e01d10f4a146c8210312210306021801400000303e403113581c3d104410b903081341c80790341c0325601c0c501c0c0040030041d003540f10200d10b44040c4014460110408200e030742c44ea4100640c04500d44805440c03000a015410560210880000c0d01e0420000160400408203000324140d17081096540c1e0400e480400305081c1c000d294104203000d4070b0000845c0d0102c141407002020060408810413600c1c20301442001141e12180e12108140c90801d038132281c0300d0b50240103594a6429400c0a680c064000e02c10f070b0000400b4403140c1c2c0a0801c0312810124150f1550400404070f4540303503951f10020f802c2c035062070500210342580c4072000c250400031004a03030080c00c2400040202007182d499500c2c0e1142200c000324100030100c0a0008080a8180614 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 806277607 1250 806276357 806276371
    0xc080303090d02010509072709050709110c06010e1e0405010e070f030c361a06071a040c03050f0705101103031305010b0a060509180f07050705011103 66
    0x10303580d051144285107011004001041103a04060800c424000086203c40c110b0304412460600003818a1145403018900d40c890410b00349884541d0003801340014050341115502d080800280d140302000843c00d10a0b400300e00f02c9640090b00400c68a021391001c242e00071150184107401402020f0644210302c4241d400340c070780780e450300e2050340f4001c02400301da0010002c0300c00e0800018a1540d610a001c8901c0c898201800d56400d400e50341e14032007560046461912400001110080a0b000401828507101501042241a6150713a0310304004040390340881e00140d0001036041049000502c06900420499088100107000070000300e040000d2180d165640015000c002d0030002802401280e40d03500100b0012500d141141d0341074048216a00110f00400001c1100310a0a2090141c43c0c1e0380c442e1a0084011100010419400005400604002c840d550b0b4107110507880044060016200d54001000b080d02142105000b4401040d81ca1300c1a0001700b900403200c0c0400040e0f8004540d41 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 806278857 1250 806277607 806277613
    0x1715161d0141120c09010c030807021c080403020c010e0d0b06131401140306150609041116020a05030111030c1606061502010518031c0b042409020a080606090d0c08 72
    0x10640003c0101c1d03203a800156000c00034142054040024030118140340007500740f03c10303040803801040c400c2c401041d020030009001c03c00c0300810000101040800c07902900103015a1003141d1066200312184205040010300e2104040072903100c01c5819200a03044035030210000d044001c00c6c2d800c500540071441c0d1690b500224175071500c5903081039a084996140d01c00d41000c01000600380300c0521850045070103481d5540c49a00c40008107004000e5a84200a1340601196802c1240e0064a413641d08138030039610310700800d0781c801c28075080e81d1654020010004051001884061186020700114058080041540d8540c0c0c3c94500807102c0e1b0781c00143d12148001001710501c0d809018564108084030030707060803544014281501c034065081c50010510304156410003510740394006079640e00005008210001034808200c0d1450046503140b0741082c2e24140009151216200740c4507c4041030300c44408a56843d41004150741c0804001c5503c03543c0680030320003060003218000041c214800c01 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 806280107 1250 806278857 806278867
    0xc170114130b1e0f041109010f0f080307050a03180f0b0d0b010c11300a1403120402060904060b0307030c030b191715161d0141 56
    0x400510010010042c030311851100b2008881510010f045603031104d441610b49032540c80fa0b10f0103904000c07440c0c03251a03008042000200f40c454542074054110b4028401c80140183d642e800251680256400549160884805600800e028021801040600220701200300380c80e4030300ca034100700050700a8a0200000705011004003164801c072031081d0400d007030242103002c0540d0799803040040d000025000700012402d0300340038141c8045108145062103206d0039419980c041044c2d03510640c140c10780342c0141030702d0900039a0b1008000c0300c50307000f00364124060ba55210307000d000351030380031020315034004e595901d000418003020f401560007940340c0e41e400308803a1201100203041e00e000c0e00b1154410070362150980c1d5925401c0360744c40200e60f041d051000600903084000c0c0d0500d8503a110b034401e6405001c1c100001c0d18207980032a504500f80d51100c3e400c050a0103410600701c908400c1c2c05001c904a02c01c24500d19a0b800418048403550303200c114901442107040764207664001c84034500c10040410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 806281357 1250 806280107 806280113
    0x1406041e03060c050702030c040b04022703060601080115050705070f031a0105060c0a06150302031f050c030f07120b2706040b03060c03070912120e0109030c17011413 73
    0x80b040010651314025082801031b800180d25030a20036a41846144d6a03180f40e00c660710b40703406803840c9100c41003400c40403189080c44100ca44c04070041980c400e00481d00003a00560290940b54143d80c1160803003020041c841005403115404171005603090300c1030203400a9420030642080300514407401d180c0705e40c0d05001c01d14908090040c4c01c0184500e005106044008000180502004d034100e40007041c80350640550035050a0603800294240c0241c68003e100038801c0d1402c0074854410890410181d41e0340441900d4901040c0c031644020395040010400e002d01c40c1c01610031304541a600001e0300159a000140400c7c40c1e140c210140c40d10301d4590703084291803059002d0b4042c006071014020300c40485c0009440e854018440f80c0141c1c80480410f90b407070301c00e1041002a12044048281220701810046050581c00649000107041905000a00d500c220301110450358041c1807080d29600342941c03c10301c9018080700003025940c45059007030070a14400c08070f015030f0149103c0c1c1c1403010f44c1e007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 806282607 1250 806281357 806281361
    0x1218030f04030c052d22111b07030507060c03031b09080f060910020c0a0f03031a030a030923040f020417030a08040b070c1203060e07181406041e0306 66
    0x9615422442d184205c5010700030080d84281d060031084801407006502414142000c4580d0b20300c0942c1e043c50044803905240790140100012801c00d0300400785400601009035480146010080190300300b1103042209900568244011074400d0602095008030300420381504a001d01d021000078030305a03010004200f050003000100301400002d403900d46081315030241c0e5031014441d111180c0d42e001035000c0e00702c1c00a000404409901c0382c10012910600d0900030054058807110481a40341109410810301d0002101d0504c80e03410780300e24010070301d400d460385204c105030410b940c00f6429904640e2072940d1584604002c04010100050301c1d5030801c0414001e12014503c0d054407540100301d10028141c11031003896010380e01180c180c409584001089910490446008060344c4440c0e624109050705074000ca801e840f43c420003140c1035901c0142c00c4a54080d1200c1200004c1006881030224551018035500144401742ca010b24160350384407001c1c415080402508041c141c82d0405004009242c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 806283857 1250 806282607 806282629
    0x7050a0603020a0e1212030123091303140c01060e0a050703060b070809040b040c120b01050307050d0e0703050303040c03051528060e0c0a141218030f04030c05 70
    0x5241c01c60421888034000b13070695a42c0340c0164412508028500c020f001c0821a03154402d52100c401603d80d40d640603c05000c41024412400d00c0d0b00b103030301c040e02904102e80204d21682c5410b58031040c1d10305684007902d07141003c0421422141c001c00004000b000c0900900000740801c1042c403416141202020044400180c205802c040c10309030104466503045c1c0546403415044401e10350b42e103c0040c0006c0c004c0c0054682d0941190a10240c440e9043d0081001c1c01c03040d07034442062141c980c041004580911044a00340702041d001d1200304002152603220900e00d0744510101c505443e160340b00c0394955041150202e0740203941c501c050080102c01d00150000241c031390780d10001820030042c2c900401098413800945030755150031070602c1813645e4000000800f010040042c02c0d04141c45a500c2039071040400388045025a070342800d1405400c0c0440d07141803103003040d882c0a9201c41c9000d40c1c00103100550324040b8401404294000c40f20a80100004c41c46a8910402c0d64075100902c0009510 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 806285107 1250 806283857 806283869
    0xd020913051314060f01170723010f170a1112090d110607051e1308010f14010506030f0408120a150e06030a030e0a27051003080d020a03020f070507050a 67
    0x441401c2c05500175030908880e064610309414443d8130402d44048600d4441c0320ba1001d08900707010503082d0403510040b94186101c240c2a61740241516480e003003035500c460a82301107440c00101d03100184040140358003c44061101d00b103103910b8008091907400d05070400f0f82d580c80981d00900c0b1401102a000264418503400640c0600481c1c5001c1d4005030082c000e4890008000b10080b060440d510605400c40c1d0140c0c28865031100802c0c0c0322010180203002003c0040c05681c81e060880320664400300d0342c14100d07200104020b00d0f65850b207400c5001c0c0000544221881602405905820414148450f1055078030050000d08408510011000318980e0342c17200c501b031145c18007800825103000c01d1031021180c241c20310b402c0790700b0444003103080104664054a01140302c401042c008104142e00100308884600c014042c64840c040c5120742442e05203c01010108200803814917031000d030b00900542d400c0350800605010035103c804e1407075071003000122046d80285006001c64600246620b0203468 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 806286357 1250 806285107 806285113
    0x22d03070e0a09030e190e0106050c03040308070c030c03030503040c0b0414040c021f1415010906080402040914010524011b0c050607350d020913051314 67
    0x101d420071000c4024030240403105440d40342c4101c20181406404003007080400500684201d0030302c2c094020180303c050003a458103101000000030142d10804c156489801d11501841c5004e16594503410341b9408550300311070350302d10b2960020120300c03c0d0303048600960007a10303840c0d968540b170300e041d404121a0f50010007601c80c0900090007040100640405460026200003c035000c014106920b020343d603429850000034004409204aa469001080111955605607665803101e80d030030f0300d80c440c1030b140301c6000400101c0d042240512803070b00c681e085400a1720006580100d600d6100d00700308000c5054a180c1c0d10361003800201c07440300f00c001415828212651084480c40700008200980791400191907082c45200f0324144400d45041e0070080000804941e99907416207803c881c0c981500079a0b00d403481406034071a40c6540e14501340b00c0403680000d01e084c945590900c80e08000d411208840b50800e40040010108110500c6018000d070058039400035090b82610345080c03030000d00a070440320380d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 806287607 1250 806286357 806286359
    0x102060c0429042c090c1e06070c060e09010605030a0f27030908030c0604231e010b0f0901090902030a0605040b010510020105101a0403022d0307 64
    0x10922000781d4042e40c041c00041800003400942c0b2906124504502c02c0400d03100003000100b0b8021284480043c04c40713a40700d00501c80c401c60481c1c0b150181280c4040e01d0360008140141d00d03140c58500c1d400c15a8400c0d464100c40d1084401007407440d00403503011100442c07980c03800c0c84100d400140003000050119807200700d56062500051103400054200b007045901d81d08000c00c1e54049422074010290000014482041a0b0001c1158588198419030204809031404682d50001204480302074810400401180d26280da5070505a2902e401424203034a850040414441d414400c1800c001c0410f40000400d9919241480c2105c072040901031181b00546000c50481d161a0388807411507034107200c0007a40e400c490003c2820310600620041c5810b10b800204410802040f008505030381e41070350b40c2a11702819000990032a141661a0ba200b082c4c840010410246955011100c81c0641d01d030460030980d9070750100c1c61180e1004071911000d0140d8203184412400d0500d80c030b916041c1100144511 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 806288857 1250 806287607 806287621
    0x109240e070317162102030301030f0b06180a0c080108030903120a0318060603050601061b02102309040f06050d0605070e060c010e06100f050d06111b010b010206 71
    0x1000c1510000304070300035040f1103001e019001d0058600d03840d4495400c00d5401100d15103c410385684000c0340075032a1203010200c044a20000590f4166030340b126000f10380d500b594980c0205103900802c00c43d40110412003100403581c4079074420740603d01a007004034503000210006043d5003c141c212000f01c1c0e0060005ca44595400641101014007220b142c540e00d12201c00220054800b580c11805518045041e110402255501c0901224008c00030b55580340d8071020100c44140c03280d00d4085840c400b08076281d0151800751200842c00f852814440756102002044035005101d410b801354070204081079980140c10a8005c180c18690300390020018541003c00089040d00d44402c06004c583c1c1c0c0b0700024164901070400303004100030080070240c480e07100034043e0380600484421050140280c1c00030900a5010201780e4094800100407210a0b03420101809400d002044e0159181a220340c9001000c05404005041c0c4041c0c9400031508a461440602d0949401c60b40041c1107500c414104190 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 806290107 1250 806288857 806288863
    0x504051b03090712080403050c040209151315020703060b0f01140f0c0109080c01180c0512030904050f070206010f030308071413060e040f0207020f060f04080109240e 73
    0x20038a14281020348946581e90400d02e400325581010800360841d4104006212117800030f001200e2280080f80c0c1529003404c02e10090303005106c90590050b92400907680c50901a5003c0c1808400945810142c60b984100d1000c0d20200f0f09801c8002d44c000400500c148403050042d50265007081c0c03909149840200e000070555072450102c1d80f40c840c408520451407240c85c108540e201c5103804003d001138051820a9001c0d5031188030340500320343c038120484036000f42241a0a030405d41085103c11268070700401e0010038a8050490303030440c0000c000074003880c0e5640c41040e008110300c40751600e1626054101078607148040e0000b0f046c00322220300410000c1d500072081c1d40c0c01013640c46c100c45001140c9003103040f68040c03890f1003c180212448082452940018868058482100c1c140650f030188404038049200d040e00c080e41281c1103500c900b1035410050010170b203054928410300e10742640c5045460071945138207400c5542c84442d00800c90164103120803540d0082035440c4c200701c2200c0403000f00d40d0b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 806291357 1250 806290107 806290141
    0x609070e010c121707081302090a11030901060305070515030115140c06091b0d02190e0903090907080f2a0c060a140403020a03030b15070f0309050405 66
    0x1004a0240c1101240e48500c481c4100745901c03089990241c101207101030000c0400e01d1400d4010140d901c00207001c00d00c900d21150041c02110035100810045400340403021750001c00d078a80d20354a0315a1a0350361801c10000314403a40384000001911400c510348282001d4096024a201e4260482d60040b0865003c00720303030440d6008030065403100d0340000c00340c6001c0324074990034000ea0350115110210f42c80210b00d16200c2c0c1060303019180320300340700b80c1d644080694840c03885803c1058041d0600042c204568400706d0f01802840b50898541e4900c00585446012035149159804c04942c020150821500d013542010260070403101c0380c40e042d0807605800341c0080050b2090144008181c8050700c01c0204601000001141103907600c0301aa003140e0b0b1140d080d00d414074910301d00010405100020701c8054000e43d4583d01178014140c031030310100c2c090281c50061683c0402c5821000400a42c03100040101c0b511a20300c1c1d200004080c1406040301c92254007060180c2e00b01020003220404a0600740 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 806292607 1250 806291357 806291371
    0x111e04090b0d02060315031e1b03061308031f080d18050603040f02040f05070e1c0b0c03090709050f041b06080c13080105040803040203061803040302040b0d0203100f0c080609 77
    0x480c6c0b1059000c0024030b02020350f01504403550380882260000e10010400c00403520180030750a030611a0201450f90f990012565078955000d00c503002800111008011030300110100108880c1e0802101003000c3c0e041c6541c40080b95911900400c615103800481d591641e409940303c2c40651850302c0d0215501d48030041000308003451121a00c000c542d1250b001200b090010401008980385c1b224000d011b01e240001c4c0540301d805004200301180c03851407500c9001d50351003201c448150311038101803625a0400380800b5020700034010045590401480398601c82c1036901c3c42002c0c07600749810000d2400c500f06034041700305207c418003404000c1c2c1000d01c0d0f5410803c10042c450f91000c1e207098105600e801504036074250b5003060240414062010042c0d07000d6402101502c0c00c9881e001100f01180200c40b00122564101344002c10141c5015800901b40140180154408030000c0e40001d081215801120118559800c4050384090052007250140306150a12004a08008000813441075000b0400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 806293857 1250 806292607 806292631
    0x200d02160b1c111e040f2c06010507080c01020910030b01020a11040e07080c030c06070506010b0a03020c060a0c020708011e0b040605031504051b0d06111e04090b0d020603 75
    0xf4400c5210000841c2c0d0400100034140740b01030041d6040a403913078440c0c41503201300c0d401d00401041c150040440c08201d14a102180b0345450304200781090070080081025040c0001400a40003150800e40100600000b04000581ea038810710200580c011110a94104140c945400110a80d0300082c1d0401e0301504103414030102c0489000080c0580202015a0914080d00d4000540d1002c0015048007242c8124159441d200e90341d018080a80110700c03010f0030742c1c2e00c80801040781c80404402010b80062925015103014100e81c007540c94450f090b26840c50140c0c0d01c44c00207851960500c0010003400340030000380400c00c811451a015004c0343c0310040015942e13088501e4441d41c403640904000c0c040a000d65812544004503030310380500807034081d10b141c0105c902d101060180e40880103141c01d00208040081092500c6900c010910810b0480ba44007041262055110301c03401601c0b0b40d2401514901c0d41c2d031341064200c905451030a13441c01e014540d100030743c00060380c610090303942c008414042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 806294964 1107 806293857 806293871
    0x11d01021903020f18010c0812040c091a040f140f0717190207110a0f08070e160c030207090f050114030703080a200d02160b1c 56
    0x1000d9071200410002c40864085e031101401404006140c041d41082c0c0d19a111002603000d8100c80103c1c01c4000204400c01c80c504c0c8000d8040e000075201849503804d2400116840390740017110500c143e894903455034010700941e001d00140c0c5240c891840803810200f420140020040d0351700c80000e2030045c003443c120b2441c105024021100d41c10040000c0400f120300034025080802d0031240246c5244d0086015502e09001c04040c0642c03d0005407503600c0c121215203061000e83c00040b2201d1041d0400802000c8881144592101800c20031010302c00c5141c00c90a140482d002520028034081d1409850461988454142c9694101e0711040d200c070b0000b016500d4000e8840240072150400c02030801c03a00c1811002141c02c4124080307003078203440c8080c95041500c09010341006a000d111b64500203e407240020b0000c280440003680351a21a9140b1645403149040d80741440d511000 = true := by decide +kernel

theorem cover : BRFrame.Cov 806115107 806294964 := by
  have h0 := BRFrame.cov_init 806115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 806115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 806115107 ≤ n) (h2 : n < 806294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
