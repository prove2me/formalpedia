-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4509
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:51:11.669643+00:00
-- url     : https://prove2.me/submissions/fd60bf53-b481-4d49-822c-011340cd47c7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 810791366 ≤ n < 810971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 810792616 1250 810791366 810791381
    0x100b010e0d1502130e090102041215021e09040b0405070f051e1c0f020a0806040b120d050a0305090a020a0303111f1b0201110f0c0f150103120f02150a0f 67
    0x80c139500a110f8200b000310480100c0250100049a0050200f8042200c5101e0200005a80240c1c1c502d9440c5080314900080d000e07000b011030101950351051b034241d0000500800c07021108440401401040c0001c004c12104240c0d800c40010b551002500c0b030450180c4001d00c1c070b070341c86040c0c04403c0128041c411030075540500440c0d40b000c45003030320031700c4040302174019078000519090055041c016256002401801d00034040c502c00d544030002074000e03481e41c07a055060500042c00350fa14128070300201401c10391045451000091601d0000342c0b0072280420300c180f00d603500401c00840503103151400c5031030b1100c141500f6241e010f5100c0e070340c55805030150809814005840f01144483c045404e484038050100041800d42e410031210400050708502160701d41413854046e40e45030f004d90034040d4940821614540710310300c0b401d5214020720800a000d18101c030320401050b400505001011940c00000340000800341e4003268130130f454203038046851a4001160740d000a2030040301c4080d02c05071000c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 810793866 1250 810792616 810792637
    0xf090a15020616081501110d0302030712091505062b06050c090916020a020406030b0f0117032706070b04031206080a02090417031602100b010e0d1502 66
    0x158004240d030503014095241e2010110a01d6015080c84503000b400d03000005100c00380000458070540042ea0142440050500350a030848520762501440a4000d42c0305a440b180445c0c91202d1500c40608240904074465601059034100340610380030f4100603260103401d182e4010103a22012000030382486405013000b480411030a440d40460038818101c0358042d03d0a520000c007008400c03c05c1d12503842c0c0540148007000e41206a2240c40320480c2080c203011802503105062547c00001d00c0a8000c00b2800790340d03880134505103644d903150141703060100c501c44041036400a01006205211a0380c403040b0100031a080184152000c10000c2c41d55808060100c54100c2078a09100c02d00d544840825001c42d1010010441c045c180400c4070703580c0344145030003846010000002010054151243c100b842420340e41151a8101030760041c5041115004010051280c00c080318441081130080c06480c1340185c46da40c0010245c44140000c00e90250801d4551103030742045180d030504944002c0051000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 810795116 1250 810793866 810793889
    0x31b05160612151202123307020d0c0203030f120405010b04020306010914190e04030306170705040207050114090a061a0109050d0c0302061b0f06011505160519021009030b0106050f090a 81
    0xb5050790904005c408a040140c0c03507810042100680c0c000503402b520030641c0c1800559855144000380c41d6114040d61805c0760304012801500c00d2401e400d05030700841c8200001d01c1302002e00800c1c0012400304441c0140000c0e81c952041001c030f442c0201440080c10b010309004450344040c1c9280110304000d40c06291208a03038003c01007031640c0b520407000031302036286528068100036020700c0c1d6181c2c418024107109541c00a01041001001d50103012070804484461b513092809184080d11020020360541d145418121585e030b034207040e1014154800740c1611924401400d243c288200602020360844192645910120160380c44c2d0015103009031454101c1151030350b842c2003541c2422580500300d01c06500080c010b01003104000c3e41840e0000c1c07a0f1800c1c54981541c90305032660804400c1001d80300d409511343e04041c80c0450811080c145000b51400d02e85545812800c603141d004500c0003801a9004800501c0078612500060120110101b2036038105842d070350015031500c6103170707004040810 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 810796366 1250 810795116 810795163
    0x12032802040f170d021e0304030203011404030f09180207081e040906081c110a1505100626060102011d07031a13031b0516061215120212 60
    0xa4a01c0c1c0d01907000008040d02c48114140c0f00030f503a81c20381c0440346052500150380c0015262041059038009c0d50014001d00c015139040f4104200e01009440503000122603100b2512194082d52040e0b04407010040c000440d070704030000302e50003504107031401c4035000c03004c204e103100383d0a2040c500e0041840ca04029941d503840e00240700100c40341548442c186402110450b281004000c030202c1c0c0e602c805c3d081c12101003010300c41c86030604a4400c001440034103840c100000700020750744041d20545080d800505020380f10030382a24151091240035010b000000b0040310088070741c00000d5001503040c0008184c0b003076081401d422080728110303400c00b6940a2542002400350080d5075031100c0000c005043c030310382400034001d04030b24422400601840700200303006400c5070048680d0004950840152a00003e010707071481c0c0302050f18806c180008a10030144c1c0b013101098410b0041500b40110035402e190b282c0070b00b0398985030031070b00181c1e448002c003007240c080c1d4079052200010208156503c140c021 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 810797616 1250 810796366 810796379
    0xc0301030c3c060f090f09020304110a030305091c020607060c031104120c050d08040306020a1e1d06030c07111201021207030c0804080307110c042c12032802040f 71
    0x180358500c4c3c0c242c20440481010851882c210f80f104040d0340141201685da50f54500303003034903282c0c074010020b500298140d000106040c0e1213005070030392001c110303941d0103041900d8143c04c07179000f0901d0300658021020001100050130710345c49083c0c0100c1c58240403800807030408d0b500580e9000350303100382c92030001140304504000c0740300d005c24042d00307089414100b1390380181c50301c0d0614000c03408014151580011080041405680141000c1c040395845415603072030f10300700600781900000246c010712940303c5030700c00c0351821130242c034400c0c2e10259809040c03e905440341000030f44180300c56900301c0c080350141101d1000a0000f41102039840110340c1c01c0782414000101164001d01c010b40820403400d00344000103846a084a80202c102d181012403862604000c50800020412450340b0500d40405a005402c90307002c5030700c150507142049200c030f0803441001030301c0c0c40200070310030031094003080081c1d0220721280c014400e28a02d01400c2c121040998004000c81c1d01981000d0702600c0f080704200000e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 810798866 1250 810797616 810797627
    0xf040507091701180f0314040f0e0f04110d0c0f030605070801060216031212060e090d02031903050405031210050a05180105040203060d020a030803040501050c0301030c3c06 76
    0x30030382c1c02c0000c00921060701c0400800700c1c00d500e4003c020340740b6141c0100c103052050090181002100d400682c1d01c0d07a9600c02c0b070401940f1072181c810805004400075060607450a450f5100c1d0303030031171150f420040da502e00300040340180500c00c0324075401c6400c02041080b8030303000034005144110300004175828014000780200c0c03030591103003045501a01d00c040d0031083c4061101e0851b40c0c401c80100550b884944103843c0182e80c03014a8800515148002030500c154800071406024041c040d9202c0b140c402c00100d859201e6031221203c2980005a0720315528443c1d840746070310034011002c0e40e0525080018005d008042542e4100e0405000710f820b000701d10707114005c1c00c0202405c0b140603043c8500031800030009041485818442d40d404000103030700e0385030205400c0030319900401c00002203889142c050416007090f10306846640c6048002080e034a4500e044a050740c0d0802e0404e504186404800003d03281c110140c40c08483d020b0800c1e403c0c0070081003074141d0710340701e00c84600c402c203050481c010f01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 810800116 1250 810798866 810798899
    0x170a0516080304030b0403050c0f0a060b032d0a02120c013b0109050d1a010f0806011802130608070e06040b120405030705030c030a030f02180603060f04050709 70
    0x4250405180c2000201c40000c00c03a01101d911050041c00c9a841e81001d40315800f4102042c102800354510840c80268080361820000348a580100500030790103041c141d985028440e81c22402c80c4003529008503480c8000700044600080e81201c1c0114010340c00301e24190038a01c0c100c190703039102c03845041c1c696070000407418000d1000203041c2c609080b07046240404080c0400c4002d1803800030b4184801c6a4070501c0a90040c0402400044a0685074540808180500c800c285030f03800c58500003040004400c1c1c100d1084030020f5009110903403d021241030700d00c422100035070b0348176400c205e03001c1e155440520400c001d091a84a0311074030b1030b0042c800390039015400710716845200b0030041480840491400d81e811016004155807041d900c0745015840c6110750031018041e88800f1410641561000000b407801070340d640c0d418892882285402c80c16402100019202c0d002c5a03c0103e10500704800511b5010900614039200c54040001203800c0b200300b0742c0c22800003400c18005120b1643c0420b018070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 810801366 1250 810800116 810800143
    0x1021e040305071d061c17120a050105010903031101140109020c0618100e0703080d020307021603120302070f0b010e01210507060e060d02031510021c08060406170a05 73
    0x207120185080103031309a00c00081036a8420344024042900015159101d03540840d803110041008002e00b00910b80113070001e500e849030b00041c00d800110181c65900403d07040301d034182c41d0b03109014110b0b0f801741c1d600c800300103103812159a5100900003901c01c083da82c60080c07011071b400582d5401030030406402c0c000020440300d003100350740310304642c2c040f400034140300410142080080d00c09111441c0b40e0800d00617500c054031841000c200103406003000d90085006154580032503000750040101c56851342e0007403002074030305550310f4803034a90b0340d00a400400303103240300d030759605004810b640c1c0364080060280c0040251004540052000e40c1a01e9290401c1800c1e000101030f502c400c03a80c80b06d6a40046010b54420031408803640311140d2070b00b41c01e589100502d84401c0d5102d00e0002d000f541a445070100051040c0c0c00c50201030b01c4180045400c0d105080914030125520790307099403c1c0e0303503c0006042c05802c140d8502c000039000744d041105409503860341d40a401c0040e16410003e02d000301c14034009 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 810802616 1250 810801366 810801389
    0x61508180a03120e0c09010b0a09080a0c0e010e0702060103080d02040b0c07030510140c09040e030d0509100207080a111c170903190c020303280909110d090501021e04030507 76
    0x40802c1c6c0e2030005141c112542d0340b6800390341303075202c450864981d19254810541845440141810040e40001d00400e0307507525106005241ea949940502e4100152242000340e00500010300c04107080c030008000102c03508801501d050740d9000d0132034040d40181078005507a04032110034010003009202c01030080165090900c04148021585145500040c0c4400c028407800900588540c0342c075001711210b407905400b6682c95444121010700078003400c43e81a95140240380250382301103c1d610030b0760f030402e801c42a030608080e09104103540c00c1485500a009611852031103000703034820801c0342181c0c5056a0394441c0901c584070b00440030b20001800401c010780052041400c00c400911005411801500c1c0c50b10b801001d03800400e00718824406501d040d0500c00c1c1c60070f402c658110181a074400381960700c2600003a5510300c004101c070900f50920400314010000a0900c41540d0403607150603010340001440c0011180d070b02600d6820500041d04103000c085003c106200040c001d020007009942c400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 810803866 1250 810802616 810802633
    0x15020114060a05060706060b030103080a020f150103020d03090e0a0204053a08040807031101020607170c1b15070f030c020c01050d0b030d120609061508180a03120e 72
    0xb625032a050107081e0040102041c00b00500003150414801010f880f4401607482d41c4a0500b40c08075400014288090b00c0b038038101c46100c42c800a0f403c42401c804100d507a8940c1d00316401c0020750f0b0302d01181641088250000071171034003d4044014082d010318500180e90f5803614051005612a511007150000001325807160051100703101555070081141c0140014007542c5001c203603034040da4001121622400c1404001c1001140603074004520903006c41e451a03a401204851f11440c1c0740303003d6070b050a5030010442d1030341c0103000342103110003c0b00450080c280c038941c858036100890040003da050140107009130103070070034110b5480d103000d03140600842d40f400e240650341c0c055403000241040b0001803c0412030703070f140d40903080744807008040d103904e090300600041407082c20b110040840c51402c0320004d0305100c18800c18084802c0076421f030b840c1c0d01e00d003d02580d04610040c01100c944094010041c01d14805200c0304c41d1480c440e84030f1003d500a0b12011030102c030030103102244243d211069 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 810805116 1250 810803866 810803869
    0x6080601030c03140a080a0c0308010512071502100510050f030a081e070602180126061005041a0c06150d1227030b06010801030f0803040f0209011502011406 69
    0x2520410f40750011040940c100b0050219885c100d602c00c0003400c4041d01040ca0f10000c0d5100d84807156941c0641e131a0001d80e41c03140d040010000e040c50780c0c2615540921000c02501da109504014002e542d40181e4000c1d00750180c0e10802e542044034032218a1000350014092890803902907105980107070018580c10b50241d40d144514820050b1460319038120000800f418501c03501200c8000b584050103640310308641d031a0011150700071002d180418410308080b0802a88040c078061740d25000b20350b404070341d22203c00307100b2589280406075040100811011542d000c10600100a07040f140035020741d0798a9615041e0700306080903085011a5540880c1c00c14242c0c1c4207030940c107002e5003100800842c400024000c1da80000540d80c510304417000190b956000003c4512404210ba00506840c0e003656140c400464088409001c0140200501d070b15100110720540043d40c6d0207841802e25040c40c0760941c001442c2e1810990002008014030000025007650a0040c0780d280d6a9000d0710202a040000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 810806366 1250 810805116 810805133
    0xc030903020a061a100e10020c0a0302280b04030b0a0209211501081e0105060d0b1308040e04151b0c060f05040c05100509091801020d1b030608060103 66
    0x28050107407611608800703131a0840090301c00d1070030001003140c0c4800546810103001d00259a189030303c1501c410898013100d0740003040500703800382c0c01028411014159420844c400c00c0100700f40d8104120b001c5a00804c2d0800c01d101c0f400791240c0311400340c48500d90300d04804403c40c010032803000240144481342441d241d0840580e900c4c04844480300a41500f440070924107141000d130664401c44540001a42440106100b825081b880300e082c0150b038882113020707007610400d07104990007141c1d80d100a4040340e2164030f511f03000740982d0b8550415103210b03143c911107a0400d40085256200c20b805000030052520600140c82040040602100c0400403c2220050182901c07606001c1350300c045108001c219845111380d1001c600b8108024101802c00e0b10ba00321103805114003642500c0140000c00b4010300a480c10060000c0480245035902c8960030380342100e440c401041903400b80030001c0404010300030012102c128000e65a0340310000d5100a041c0c520580c403142d417035040403005001246041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 810807616 1250 810806366 810806383
    0xa02031b0d0f150f0b030d050708030c0a0903080c150906060102070315151404140f0a1107020d03080402190518060f030303091b0a080307121206090603060c03090302 73
    0x1002c00c0005482c1c201401c05040504691000a01e80314001110003501d5011840c0c1da0016000c4812010303400e50207640b544111030340541200f01c10300018210340c0c40d8400030092214280b90141c8404da40380c2e1001011b4005034910010f07030300100d02500f00d036001d80d89190341c400541c2004203442c2c182100040e440e10b0305804098022410316169181401e4207420076002c8034907441822600303a0351001036408440318000002d00c01d604107602400c50103442041140101c214082d4100c0b1525045601801400201c00b4207444540c140117030405a512130035007100c0c1d00c0c0240c98030038042c40c00c1e1040151407145000c41c4a0700c42040b4509020304d840712140d42a0440000943c04c1c00c0e911103800245480c40c601d0207590b89484000304010501c3e0300401c102101c00361590f00c0c00700f001c1c003440030007507070001501655009620034000341010545800d14502d00d12421f080c11103025041c40c03400000d484143d000408265140c000400800c042d5208054212800d0b10b001c002500c080d0340d00035250b030307400c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 810808866 1250 810807616 810807623
    0xc06061e100e0a0b040311100f120617010f0c0305090d3f14130b100b160506090109080405060309030f0703030606180803270a03050a02031b0d 63
    0x1406a1408901d00440012196560042143c1880c0307036a00d00c002c01e250300c0b5000c00c903503011040240408505120403414000180380d1600d42c0120038002040b10340042c2001800034040d1101c0707001070040011080c00301c4030150600042074aa0f200d48900703050360110f00301c10080510b0070040101004020503060020710b00c5260040080e410200d945406484c000c102000d1194524105004502605480c000c00100d01c1c0f03061121f2816660902d0301b00c001241d090240024401110000448189201d5485902c070715000440d145c64421400c070641107660500c040c5c1310701410030001c3c0042044155489103a0000a1140a070302da1303207440c0e440c041d41c45024001c080200200380a0003080c8240c035920700b1054141500c1d20313018100100034103918440c10000c200141805a520840084074805484081c0000c42c41e05030000810b4a40c2010841403a20580710104004241c1da20300360844001c600400042481da045d5004140c284601440f2140c0c0c3c007600001c20a082d6165201c4042080b82c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 810810116 1250 810808866 810808879
    0x30203091c020303030f071107061b02060c0a12090816120f08030408120a05091b03070b031314240c0f030f04030306090b130e030c03070303020c06061e 67
    0x100c0102071011035000d0000950500000c0200f01c045030609814601c9040b00e0303507596212010103a4850303100c0d1214042c44000401c0c071409aa40c0851030034201101c00d00c00f8111300c0c541500707205020300700200c0391000c075206c0892072010b004180c3d03c044d058010b010402c002d41003e010320045881240d82e14403c401410540d00061001e000140640d03401c01c94000002617900c2c5440d191550280d4001d00b07807951079900d8800402c44180c4107100e840c0c411100d0340c00500e510134044080c4076000181009455144c401c3e079a0218100030b0f500d000d0b600501444100112109040c42c101346c142060010142d1140e0000c1e03409101d42282011141c40c1c0700a0804541046d111040040da0134801c088100c40086000800e04c0b0005d40140611442980269070400045485120302401d9440201e50541d00204540c0205c04082e09540152094921482201e282203c030080785030458102540c2900440e81c00300d200034001806010480d8000307030840301410700e9502e81141e11000030b20055414001c15 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 810811366 1250 810810116 810810139
    0xe100c17070b0c030402151804050a0b030d12050901140708100e07050a03110319020f0c12030a1407051b0c03120a0909020f0f0304080d180201170403020309 69
    0x644181101d01c0d890b00040000c0712840c0c42e5241c5410f56009850483c01182c107200c1e001540c09246060360a40f50030005c40e5503558010300c003000301510b800783c03490f10803d590320324000e11990300700007880311080585c0f1414043c2200c2c40e01c11044031401031500706140d042c4444171900c81c03a110703c00d550010071030030300080a441d00b81030306042c0240c5d034000402c0c0c8149141800754040d00f10303000e441e005181d6501844050501c00c80c5008a004c180c510422158030060401c0d600309064014065040c20007031181d04204842d000e40d45860710300810300405540000502c40d0a801c1405042c010303802d2101ca44002c0e08105c0c41c000e00510038032225404010340c0c02d1082a41c0c0209000c0c000008400504407031038194040d440c0c40c036545c40719928501103040d24800040403603842c000d54034060360501e5a14100300114400c20f00540c40184102c0b10101c040240c14a4402d261107000030000c0c004203011101c030600e20000d00040170f009107205015600008000010f91b00200b03e03480114181c07030000703141 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 810812616 1250 810811366 810811403
    0x5150c03040905040b040b07020d0801150c0503120402090c03070c02040c02011b030e190f08131a0307030e0c090105330921100c09150206070e100c 65
    0x18000c1e40c006102060819080c0070070b001e02e003607903d13004500a0a45002da900d030040107a0340c0d82d50312440c000108600c44010050300380b03014dc1c403d8070103003a42030284800d404c0f42d9500b8295070220346c0f9051708103540e07011f000035824013520460b40590b48402003451414468000752510240d508028401c684807100318a455100b0b40050300703d503002c4101c0d04048000c810b000380252002c2c583d045490f01c41e244450304d244010b04030031a50039800600c500351160741a151820281d000c00d01e17908410040b11030010303e0000d1031030303d9040007045120680c0c403401c007498014265000c003203954140364030680072303a81680c1d100342070b050440d00300b152044c1a80404e4120114442d59484ca0000380300300c20000740c3c90b03804407003000701504a030445106a202008101c021742c028604d40c0141d84a41c0101207142c01c600c80d80d8444000c0d200c050816125450341d0707110b0420580341340340ba8400160403220501c0003240e0000c140d8260000708440317618501904600060014a00c00303000b412099070300c1d42c00040c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 810813866 1250 810812616 810812623
    0xc0f012d0213091e1a01052a0d0302120604050606270d11040e070f031104020d060b07020a0902041208071b1d01080307082208190c08060105150c 64
    0x10070f2040c00c00d00131400c50031480001075901c0542150130030300f00581da208400540300c2c001c460b034505840c2d45040840c058200c480310817000c000d403004c2c0c2c0381244007101c0c101010001449451500e55000d42e9610404041a880031000340003103001300d007450248060351f59031100b6101d820401000c40c0b1110b64130300e0400e41a90804140d442c1d001544000b04206003d1022f06100c3c0703181c0280e40c24000c2c2204015015034030155403181b45040210204180f00060610984200c4141e0042002d41086000c012110403150b031036100c401c01040c00680d000850070300403403080082c060400b00310300381407504121095000170060002d000400c005045010020310601242c100341251b130010540799111013400458090321109010042c451900004445c0000021500041c1d070004d801c90900400700b5084000e04a113600b82607424900702d001254a00e0108881c0181d0005d5561081e290010340c2000b01440505420401a0383c005000500c01a02c40b6500c2500c0c8040901603680e40304d01e41d4082509 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 810815116 1250 810813866 810813869
    0x609060904090c061d0306070807050c0a1b03110d022809050c031e092e05070e04060512030301050607020109030b0406060303120506101101060b0c0f012d0213 70
    0x80f070b030b00c1280086401580708010902ca02081780c1020b0789252544100740c0e460344200c03200d0700010464400202450701c54409850382440320070450380c20320625a64014009201e400b51340203201c10450402c1840041d11600600300b1003514485d01d000e0198000c541345140070000c90a00302e003400c080150543c9910b221500512480104004608080714014110744c02540c4003071001d04034005c910070310307541d84d00c600d4020341490b4020310414000c4076031010a41d10f034074820034443d42c043c240607202075441c0c061030740b2130f514035075440d494a0000010082120807940105000720f1013414040241e12000084a05503031084802070744804072440122200c03111500001d002d40c048405101c00c22003507030440c0064a1280e11059096284841d6807000c80780100c800303541c050120703400e0786000da00401c50100d07d080040000310b01552a4192110503a01151054a441c0c1c00500003020085003846003c40140781e0600846807641569201c4a0324140010303e017030601c0c1d00080410182400204100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 810816366 1250 810815116 810815123
    0x409050703170d020d0209090603030a120c11010203041a1003020108040809210102031b030c070204110d0c0c02030d02070b04141c030203070219050a0306090f0b090a0c0f05060906090409 82
    0x1980c64070f0000c00c480c042d40000347d856014402c940d0118205107400700c29104c078030580e036491070a0711040121a0002d070000c0841102484040d9060141c0c6000038002140b18501038900400104200555641c0c038110003401e101c640c0c0d0703840382c041c80143c2e070012015401070b07000903c00e83c03103500c92000140c8501180991001038401400041300405040d0040c5125428642240c0c9081408418401031071200f100c5128200c2000c01907000146025402420401c4282102c2d40c20700d60240e4029040b581c9280d003540c00318115607051011403034100415841c03285180301405066140802c0343c0990300960207481414402d10410303400c2c40d200c0e4412010b00007143c0000785c52810960401944a501c6040203074000c40c00c22504c0703141c8400c8454a6400c9840c06800281003a143d511510300428141004030b0320b0310381603542003000c91134276075001d4040c20400b030251044031101e1401c2c110515003580400d00e541501d280410884e40c46030b0603640f1800054070f0740361381d694140000500070308503000001d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 810817616 1250 810816366 810816371
    0xa050c0c270604050114060705070306050c0d0e0c0d02120c09160e0a05100f05090d05060115090f0611030705101a030606030307080702030a0b0109050609060409050703170d 76
    0x11908001c055920051121804808040d100c0000740815650240100c56268880c60000d54881c00c01c40005c1c50114041c5050710800b40e226582c00c0107882094071195192800410210640c845e14400c052110310380100070300f08203403800d004c92804e0308518406481040c6000c40d00000714003d05c80b8112a40c0000c003001194a0b08442080c21103030b421078070b140051a60400301d0017501700030010030103590340100464a480041034007182e0907601060350008020341480403100d036448100c03811031000d205801400496040c900d0421510804d44030860401604990410541c100b840c0b02d0801d1300d0f400d00c0e000c0130b02220070262a14510841d40b00400621a40d5440f4a00e000c0980c48111410019051288550100d0040541d80c81c02910500c0d8103800410840d000a00340340000d103100340c8060b0075035460000b25110446607843c01da02900710207071620f04104aa01d01b90003042e9010714215010003a40800e519481c2e55071020b800300400c1e40f5440b151000101d81c0300310503a1071103074408205 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 810818866 1250 810817616 810817639
    0x7090906060303091e0308090a09020714160b0301091d0d170106050a090509130813050406091b0c030e1203070209072c01050904060902031503030f0a050c0c 69
    0x1400003052903110507000510725800200300c4044080d1034441e404182034003056038908544886215a000502a5504c42a9909d000030000034034005400158080c2d110b02c1c107440c00708140c01d401e09985600b03d5195040315241402041c1c3d0003000d89040d00c480907000200c02009a000c2c085103095a25100054410343c40d400350169400445a00c1002550030104a2a640d880041e2400d001e00007262000c40c004640600c00c40c01c00b422035587c0241807004140140e40d84c3c0e210310515034880030402490411041003804582000d00500009202f0035004000d05010445001a81890010840304001c4000c20310004c4c0340c801c003090005034a004007081401004400507540e25400900100d005680c00740c006071000d80150b15480c110b001c0c070204c8020361020030104e442c503c10720840c50b906221040c00b42c800030b40c64030311407080a8880d24000607500c1c24040c2c4494650a980e07501c1074802c2c0c1c0104540002d4001c1c91003650000c42e640d0420319155202c0440090429070380d10b030350b2a0010f06003540d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 810820116 1250 810818866 810818873
    0x60d08040326030c07061e090b090607050415030504021206090307050f060115050703030e1204030213050403090506090a08030a05031609030309030b09161401140310090e070909 78
    0x18800740d44540b80d224401480c0c01d150750012a0004032a881500e0b0024049100818000c2d002400704980060a0203942e0304050340c200c04171030a081e0181d58600742c0b08200700b010b410401a2642008036800c0550270a031905c0a01c2406803050307081c3c2002c141e107640100d0300719114600b03511250740000041d41c0140c0313095a0001c0d900d2300205000d83c0c071845680b51200301e0040c00b0078042d05a41c440e4083c000d02040000c0c007130340c040c2c1c0214812001c15a8848039a10135a200707000e0300d601a0100c403040d645c0d451941c01041280400c4410081c0c170315160130180b00001e5001240310044403c251125a16890410300040d41c5405541c00955140000120199400e900ca401944038203551000003d001c0407104088420341c00358000103000c00c1078450180045004a1107041e0702c4403040b0704031004400c80d2034070a070f2210042d1340030030b0514143d024014120740e003126420f1501b4220210f030300e04500d0403800c08550784070544500340a0565840c1442c0a640c0f09011302e0300903000341d18040c00044064034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 810821366 1250 810820116 810820133
    0x23060702100224040b010e1e07020705361005030703080405090f09060408090d0218010306050717180a08030c070605060925021c02100501050f030d0503060d080403 72
    0x42024980c0501d2404050749122041c8020700a54000c080c05e1207581c00d1050301c010409014109008418183d10708039040d01c0b020406910516941d80035010703591525042c80084040d1a50024040304040700300c030050102c201841040b11540c44a51407645c5404100100317140c0160061901741c0200c20022092013807000041044610030b440701202651086000401040151500300c940d4000b8000700380480c0d80c05c2e000d41900000140700e03d803481140e90015155001c2010020b54061381d0078010000d118861142c036074410340904000900312800240203411810042060900b1108400d01d100703064130030032010147c90340c0500d900750303179061803000300085402032201100c0311402e2200049a42c00c14078207007801410310122124202d005004a05513440070720419200b1031040c05e0b803540021040070700300d2007403104c00d80250914440103002c00040d504142c01150083c4070f012307000400c07918000750100010f00c1e14948103480c0e0b114a000581541e684081c081c02c10301c0c02140100500c804403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 810822616 1250 810821366 810821383
    0x40b100f0e150d020904030c0206090a030f300813080f04181503081b190203061602060f070318030302190306032001020c030109030e03060f01230607021002 69
    0x1c0d0b080341c2180407040704018000190302802500000d0b4000441e0000f8001c140960b9140d00c002c00c494240800d882c0030030800d030f045500c1540c95a904011550a00134410072054001c50b46500d280040d010b40207413000641c01d98010201080040070024070317040c5404404503030362644103201603947c1c40d080343ea00459400c6401548100d80ea0040801c1020b07240380f06801c2c420b00101c00c3e50400c5440d5845240c90707900148009001e92002101e54050f02c0d000b401075840100b995254001120042d005042c41e00900500c0960b26030811f82c001c0c0754280c0c0002d035860717001c2039100008085a54542c0c013100502100e410501e014101002c01c1b604054041d0050840e034201130280c0701c840804104120252040341c400035148007212000c8420780b284100c1c56940300300c0103004891101d800c0c24040b0b42158006e440a0b8005081d940c07000550380741c02d012094204143e0709101840d035042240550520b0f81c04240b030b04030455017403405100794684809869005d81c0003440c41400402002c0007a442d032a40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 810823866 1250 810822616 810822631
    0x3071202011107060f201b01030b03101d1f1e0c08160518040e01020c071d0c0408150423010608010e070f0b030c0f07060b030709020f03040b100f0e 65
    0x741300200e490714200b6010080d401c421b0400400b002500d072100b0f409807080403919a41055100c3c42c1e044003a171000c00000c9540001140000f8103559a05444200803a01c58155462600b00442e2645245941698410403500351500000c05a88124640d440c1d14542c80b04007910b0307801c0481c02c840b12500041044c0c070400d000c8040c1d02c810b2203060740c111114803d0400e0350503a214040240944c60401d0b40c4110310b0b10a560000501d084450317090685003c1c0f03164401c0134076928003003500000070101c0300341070f401c071a0350301d0000e0405042a1020303454a4240c1d800061541d2a04005410b0204c0c24619102c89042d040c0502c0c24a120742603a14041e095a00510700c2d10760030034401e401c0e541000640c4074104c484062041d62114203064042c00b856001401410f040b120500004600700c0c000c10040c00d203035104100000f40d81c1151410300d410700c0c40d1a0700110380307148103104002520020030103d0345e00c00d50202c0c4500381d40c2e8401d070b018220700030560415600310300c4240c1c0c003140e0042004901c0b07020f0700701e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 810825116 1250 810823866 810823877
    0x703050616050702031c09180608070b0715020c01110f0702040506090c07170f1309050109051b07030c06050c0705120405030312090a0f06090614040203071202011107060f 75
    0x29207181074405104180c0d00a4055003d10300c0c80502c2e40b81485210300130545032900150722940c2c0c480d00c4030b210600701d40e1041c01569910341007041c2c0382c0401a9000502c000480a0305103a520384132500542c0c04009039501840d000960101c5816003035108040c3c8200036803405856020480c1041410742180808a002d603140c04007094542c0351032403006202d0140107120510309031643d5036200c01810f41108008c202c0c2d006100e844090121a800b030405950428a980007a0749001c5d59881500c50613032120f0301d01e5103407805101160680c500101042c04400c07440315500d000605c3d084900751951080a0401c0b440c2c50140003003010840020202c00b4019401c80700b09041515100c24140300f00e21a099065000700b1001c61501003103140d00340c3c81a050001d0f075003880c10545980000e26007450089640f070b69a4140030f0104882d91055010f09002500204064600307640802e649011038001c035400c5082c19140d4104680c4200160201c00d40d5010070b03100050755907140078110646c0400e4050102d01c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 810826366 1250 810825116 810825151
    0x71710031e1103011b200d0e2422080c0d02060d050c09030115050609190f030501091a1e0603070902070503131707140f09041a0a0e0a0b0a09020307030506 68
    0x104641401c1c4002803494024008a240c4441e040c0c41035010104496003050300d100004272924070302d0004c01c102c0710344100741680e40c100034a5a4580303007d011400e000c41e0780d10386006214034a40002c001c50f2508058441d00b581e08880d0002400c40d001d500ca0b9621014109810482700c548050050508a0810f40090041142d425400c00441c0c0341401546c2d044001072261401c586444c2c0d06244c030080208400f985125201e402245090102e500b080d9800d07912020076404002d00340580500d04038441c1010030450034181001580c050009040513400f018940116205560a02a00008201c007010841d80c0306014507040f80c0300e030802002400c0350a218100060388010210b4803021030b988080c00f07001c141d424003185402220000c920540c10004000074103c0d6078603003495050280d1b028048a6001c002910303407903e0602001000211154284003041840e41e40004204094590040d8020820342d1021140e400600c110b04002e58544905070002050000c082000c3d4050300c3c02c81400010b18 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 810827616 1250 810826366 810826397
    0xc210d0e03100e030d09170a020a030e090705120c16051e030304080d050403050d020a03020c060105030c0d03050903010e0a080a0905010c02090103110d0605071710031e1103011b 78
    0x301c0e5241c2d00402940c204005d0010710300d080e40d000d013924620a24007243c40400108210216801032203140d000359111084041c180758100403264400030301225152001d1800c100003d005024000e003050039188480080740314102c0c200c2c1500c4c09404410703d0118000020700381030341d48100c2180110008080030004903040040481202d115642010846280101241583c0010310b0018000d80800800380026a5003680500041c0780000c3c41d56809604c2d0104a4006402c010307040e0b100c1442940038240c035403e25120a4101810b032070300340c00d055856040343c1011034050718404114103520300441408a0030862000701500c0c40091681e2003000032030322807005407060309003e0806035121014800400008030070340400240404080c00b1000100400c0e40d42ca802c0d55403e90307000d004690302c041d030301c0b40000e80907201c0c1d940030240805211884e481d544604101d80d170007118401c1c0c0308010305da0308400c6c4400c0c172808405d044e00c003030020810018082d03610b5901803a01c07145000022880208104103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 810828866 1250 810827616 810827621
    0x1806071214010b091002100609020903010b040b22110406050a12050c040e07020313141305040f060b0a030804150e010f140a0e030f0102070b070903050c210d0e0310 72
    0x5840c0c00800084c0b03400740000800090320081d05502e1700314402d60880440012040c02250021710212502580710003154041500b0344004004890045240003040e034169070341c0c0307081c19001441312004a41041040c201d140c02500031701c20a502118000038000030b00a500c040203205a140755607495150303055080054080d01c034180d5654400d0345080c0014401c1c07040b24031509070080440d0040780c0c80c200d25604003250304921640304e02c178400100300c008030541c108400d03044134154404d0b004001d1843e10765034026160ba400c0c5005094079668800c41c01c0b0030307110922800f0185410a280ca501d883d070720070718002c113130a800240301c000035440c00c03c1701c1c00e80d405900d030200340880c903890380903210b21648041d4105410121102082010b00c48418107242c60900200ca2400740880c00941d81c1d030020705001c0500f5901030300b03140400c0302c0403100300042440421b079146401c004507549030079a0315003440012070401014148586000d10300c03d840e4101e13000042c60000c16015816075242c1420140c90108 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 810830116 1250 810828866 810828869
    0x90515060a0807030b061306050d060c090911041a040513020307180b030703050901020d18020a21060506060f0c010b120610060c151806180f0209180607121401 70
    0x1102210380440c08515180c0c814800c80c1f078071418001101340c1e40301c00050003d200454260303881c0790f0324500c0c40c0030710742d01c10400e201401e690b40d400e1100c2800e2442195051252303206070342c016410442d1091180303542d00100d50003030200419210018181785990b0f40250300039212800400c040c4140003403a4095512110201c5581c4000281159208081500034003001801141555401c0003a40c080c01c61354403c0600b500c8004d03401240180c03092041c003440e07803465000312000d4040700e0103008581c90f40d01a91440740e58084000300f1561100d5021641900844170076131080d540118245840300415030000c145034004994a007681c5184103503150319080c046e14030740b414211504040c484075016201c5000310900c648000215141c00c0400d0b80c0480b24504042c4240045010036001030148500454039000c01d41011025440380b1540d07084018040000000c3c0580060720025003030000f00c0c15020ba4a542d40d00c00c0c4c604a02c1c003484010040328003012000c1030545840d8140e000c81d205c1928160 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 810831366 1250 810830116 810830123
    0xa0b0a090e1348140409050a02120c0a140306061906110c0d0605011823060609100306050111010203010f0b1b070b07060608031615090515060a080703 66
    0x50558a00c54843c8040350356000700034612441401950320601c0c00c0d000030342c00703c0c005904480005414048003280021000c2d68480c4034a0034038068001141002c00e016050950499100c3c2c0c0d8220506416800c1041400c1c5180c0c0c8422401800103c100000040803000101101500e886a0380c2404101d000d8800f1645040052084101070010354019034100407a03054020459803404902c00006c3c4000340b4100085801c181c031140108461480003010740184080200b050001c01600d406103041704141d0032072002c100b1000c030040b5000382c0b13522086950700b41c03010781114510840d40d08083c0c05044035204e07640c0060294041250001c106100740c030b0594810780c0181c82da807450100c03102d61507040303049448a40c000c10f16070403510040402c10355000f8160702401680b1650b81d810544201d503515800720009030003c000309106c05c87c2d00c1c0e5000409036030022074444500e0704905100001d00300850b000701030f0700c075240846204406c894180751107140215002015141c540d00c0c1d90383c9407601840b009 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 810832616 1250 810831366 810831383
    0x270302100e033604020307024e0f0a090b0a02010b030d03110706020f1b0627030a030504050106080708070e1302090a02160c0b0901030c18060309020a0b0a090e13 71
    0x1d20f01c3d8a4284c005580048507403044450515150744514010100303800103103034030000801d00c52402d2900c41000c011001510f0003024420209042c448040d201d15000480040c01c00201502d4081c09801120090002d100d4125140c00c05140040e000b4241c100076a8480c2c4101c1c106c541c900c1d4070a0003054503e40c40c0d0701c0290b08015003940c6550103900851418407150809104401c5009005584020140d6098009016504105104200c0d4000044000009480315843c072104150300101710b07101e41100d41780000d403070f5503107042282c01004650041e850a0003501000144048000b4202080d181c1178400d50099172100910003400000c10030303009401105c9040050075100c034a03030203070541070304a40b10001141d48a981d2008042011342001d0f030b032201d0200705160156071512550300e0004203400d115584100b109404c0b030549015100f40c4041507140c441e648119180d843c242001008281001a105d910022010301030815038062000c06101d0740000801040400c3c0300c50318003e8001110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 810833866 1250 810832616 810832717
    0x10e0105180d110109021807090e06060a08090a050706021b0415030201081509011805060a0f050f0d060609020318150103230a08090a050301270302100e03 68
    0x7503419114140030180306550b9080c0c184056261101d0301c0031f02603082c5004096500e00200050f01c141c100390000c030001030400c400c100325501c8600484240501c3c07800e08106580d19100a246006011880100f90b402000d00001d030080c0c00185040d102c0c3c990307140032a5000341172814801240d444510f00e0408048c444820000365018400054102c003c2139101e0051810600100340c04c0706007070780219078004055100074404425840343c02d42101086034414580c9140c8121f800000c401c41c0501480758200010116031680c0c0c801111610a074000c40c14000d042c1d44d038405034000d4000300c811283c01c180c0f91205410008010406c500d04500f035025900999081d52148560710144020901020440745405d9403806020444144e8043c400d248103665581ca100510041a003541d10141c02a03041c110300c207001400340407900c80e560680c050041c00304070072402c040340f400200c200401c000a24140440b0100c010100c02400600d40601e2103440c80c82c5d1a5619040f09a2441000c0303d0880300c4901 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 810835116 1250 810833866 810833893
    0xa060e2d1c020a12050a030f0902100e0303090d0f0302071d070305060f0d0f110f01081b041509090507111906020c030d090b0108030a0512040501140405010e010518 72
    0x1d010304600d1188120341c03240c45580e6a2220403441c50401001184010880c8803070180e15020300601a10205070a00000c0c800342d000c150752407420b425000c00c1c00f40240410a054408005541080c00c0c01420130180410380d00302015050b260078010b030014001c40a010451000b11480c0c2c0e0419201a0500f0407107985020045004000207003125a121000030301d4800c0c25903406c14100c04060156101d0050000700703160450000d40c840640074003800306185036510750f0707810180450b800401c0454800200c5440c43c040c1200c0e01c225041148003452148000401715400900c280c25200c02d040c04020b1a1101c3c481a622184501302220107603100c00c0d01000b8542d00e0f1421110f40600c10140581040714004010741150030441102030083e031b6611001044c00b00500440c1d0042111102441c600307035200f40010000d00c2040d80f0b41c0500c0c40001e02080030813109502000c21a803000300c85550900301450014080c1182039280900740d82880c020907500394a56290b4000b0407648030040c14804070148 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 810836366 1250 810835116 810835153
    0x9070608090a0c0303050d150f05090606040305070e010801050a06030215090301090b0106050a030b060a0e090c07080a0305070215010b03280507090f06050414060c0a060e2d 76
    0x1480c0071918015904100001110050404060761203601c4d0305031280b0360560207904940303060800c521441000c04040040752400e0883c00d0036140b041e44c03030044d0f0b60359260200704188a6030344010942e2007081400611043c11080b0281038401c210001e00541d21850450400d4803400c2c04080e520801c1c885441c0d00303a1070904001c00c05d103400500007250620313030350722030100c004000da0020001c900001440c00605606100d9180c480034200d032402d080900580c070083c14424100e0380c46008d21403d07000b29128680840544044550051200d5a1010707078100c001c0c0500300c1951001c01503c075508403107042e032102c111002d06885668004c039003559940362229150303202a0100480d4032501040c210501c2d070150051501c41c170015292048030a05d41713101903000307101d194459401c00005000c00e108075401043e08041429040740d110f0349a2146500290601407009402400c0340d18108641170300207808680070a079002d81d5070075201801d0004000400800b00030310309040c0b0b50071204120050031000e2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 810837616 1250 810836366 810836371
    0xa0b070c09020c150403020705030f061e060607140a02010306090c0e01030b0d0512030402011e12020711130f0c03140a180209100e01052205060102030d09060e0c030609070608 77
    0x40013240d1300c2d0030788003032048141002a103086c0e0050700b013981c085c8510b042c1045550201e20f401c400900c501e203000121114010180072030401c1024103240480c002d030351054180e40b8000d07041401740c0742c0005007000300e550360b00f80d801040740428200701000580342158840c0000c04202901d031a202e0103207a00044000b8800e001c58564008421100307400440e030100b01050b46128100c0300150b40b4202800050300380c03418000380c1c0170b0008100365210b50f899400300c21004500f0f0341d20b0b409078441c0001d20b0480c946500c00744249800c00b0b40141c0046034074285403c910041d030090315082007410040f900841c182c13402c2054103482031803044081b5540d46c0e4541c0c080d04a4004404a40c41720716410390000e11148006d641c0540b83c50303101c04051004242c0d030480d060041804480040710107220101100c006513004000c1d48550743d82e400050382c00d900034011121480040b001c204041141c40c501000105011034000845124072109c100031410001455405090400c0007005018074000701111041d400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 810838866 1250 810837616 810837637
    0x80f070c03020c0118120c090f09051b15030901090c0812040315060e07180806060f010c151b030e060709030b0c04050d2001020d050a14040f12020a0b070c0902 70
    0x8000700020390081508408540c1b5128030305010169280805810550b02802500568103140000610000b100000d00014011a44200040344600d510000d200d070358000191210307491f0f0000801c1486030303040d0b01c489a40352040c006412040d450341495981d40140415034008c0f0310041205101140e007802a003030405080c07000200300c841c0ca44103e10b03501c130400c2d20700c100480c0b05e00c0c4682d06100304000c0e070070001e0100100181098580b02000844400c800c810050600c41a0003001040c4030729480c56000480c00100c040c404400086954074010341c00c07850410000e403400349618281c0e100890402d000341815502c203841181107444560580c0c901400020300900200400100c9031200110031390514003a0202d51295482d114001903c011505a058111741140030903c650640207826140402e406251400d0181d404c0c1d1074544180c41190006088242c14600014018280b1402d001d8000e10a4030080072041c0e07a241210a14011440d00418486030b00300b0901c89010b95a0180569806 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 810840116 1250 810838866 810838907
    0xb040603050a050106030201110a03050f210c1917010306020a020f1501090c08070228020d051c050a09140a031a101a1621080f070c03020c01 62
    0x550380e40d05807030280030b9403089400b0303519103008000b95a0800801c83d0083d140d000507103506e005590b0002c00318840c0d14007200b420b4001085084404501c80081081005141101d03205400c0c600d1210b000d540140c166020900405613542201074403440003600466030344404100700381d01b1540d4032000780d04a0140b040031881540380c51505413104100110361400318800a051550401003141d0a440000004034203002c41041841801030380010030900c018400ca00e0b241d00301c0b141030000344100081ca50b020703501c0351a051b822024060003159004594140c03c01148060190700010741311406852004008119110020010b040d03031074101c440e2854009107910320b407d490381d6031404101301d03050b050300819000c6e40801080c90001481031015104010700003000044040d241c0c1c42030320800165003410503000d01c0d84e400300003850416200034080280c81025104503a60010145441120007003101c11312071002c41d071818041c42c05e00403900c2c0c01d580648210121800107407915001e0185e00040845c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 810841366 1250 810840116 810840119
    0x7050109080a0504030c06050304080a30052203020a03030905030910050706380301060503030a050c07120b0f09071e1d1003170708030a0b10210b0406 66
    0x65207100141400034268540c641c40d0342c1103040001766640c00742c20510501000704188400700701ca01068413051603961600085003401584802d140380c2002c0d4000741c10258944100501411641080c2d205c0c40094207943c2c40d01002405190481d03131555005009a00b100c403580022a210350000c846050090040324074103001c03803021a110043c084c0e0b1080004e00042202010000103000d0060a5084640003198410b108084402e07101001040ca1040ca502c0d803503107003103c0e1020f4129400604006040d179445d03c403038070b60141041e448030004a00b14000c2c810b01266110703a008869802907080140023101c2c0e910b01c000e8a503101c9020b412000c0b28400c8100004400e00d009600880003005801800349051410000c1260302a43d8044614400b0080040080010758441000d04580d000150361000300814403540700c0e9441028405032040c4070010410100c0103181d00512b1007003409881100200708151030440d00d200c0341040c03003400041e0410b402c4500c1000c540003000040402000021200d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 810842616 1250 810841366 810841373
    0xe030a230c0d0903230d050d0b0a0b030f01080624010e090907090e0613060b0d06050a150801141803040905180c0a0608070f0e030a03091703130b07050109 68
    0x3400c4850840000d11060091040001c160745e00041000d80c1c0007010f0030480d0300b202a03038403507030520b91400070000089020850300e41141c10881000354064858a0950707140c088100007030f882211320560380ca091400004000c2000180d00d48500300101002d8910a40c407103805800340102000241041030485c9030501030381d603450103240250b00c440005c00300300346843c916600b5640d000c0b610443c1500540e003000f00c2500681040400b041d0b0141c40000e88411102c00111200902031024002c00d18040c2008100b003550303071111054800000c5111541075407040aa030076280142c1406c2003882c0d4100108100800098042d4500c54015003501c0c02c060300c40d030b00142120b1003250340a0400b082d05001c0310a41c01c0a000c8000d035440281c41c01a1000e0825201400360b0b40041c0089003003104500d00c441d02d0700e204420700d132401c1030f0042c244c81c42c2c440782e418001c145482d103010703a07210042d04083c80d0400000010803140310343e0282c00050100c3c9e1505803010700c19089001c1c2034545540340c80d40035000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 810843866 1250 810842616 810842623
    0x305060d0b0906070f0905030a231204031a010501210b0301020f03040605070509090f0601090b041415160b0406180b181f0c09030605010b07060e030a230c 68
    0xb07000a000520700ba1412070001024400004542c90034015209810300c4141c5010030202c00054104160300340195902e110380748880c00300464030350503029070b03141c0d50040e491260003042140e0284058034019028a9060400c1a4081c4034240c08683c20080045004103010001c4188645c0c4000c001400e01ca52404039017a039001542a8181c03020000030030041060300d204d0340350082d240d031034518203240710000400d03842c1602410300300c0f004104000092450b845458480090300f00c0810381a01c503039490b10030752142c600d0070302031038401c103031201c80c86a2030f400c5242942d84080202112403050781c19511414842c0802610541d103094452040840441800c0300091456210358458032080c580106d40b500c21a03844440c5441a030090b00040c0c000c5007240050918043c40450000341c1e0078414041520956603660004204909000002031002c0480001d0601e140c0258014041c403802d00290644a1160a45180129400c8049581c0340c01c1d00d000300703203880101462001d01c1c1a10003c502d904c1c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 810845116 1250 810843866 810843871
    0x6140f03012115090b090a030e0108100b0a1101140c09040b030325050609060f04110607061a01030b06190f11010608012013060f0215091b060a0e010305060d0b 70
    0x1030003919035440d41c0410405c21040307940b00306000c002c1d000008450f40d0081c600d1440388000b9041017041804920316514501110004010070040b07107275902c54403800135050200240440c030300c652925017210140c1b000110458402e4180c944540d00d001b4604003048010844948901d0701480180320011040c200712048041c035140c050116844125603141070742c07416400401c083c6842e080001480303039450750500902e40003070380300e50748040c0741030440701141c99401450009071425090010310344050780c0041700c0c0ca40c1204282d0f020b220460800042c00746501c500b90403911190003003001e4649061145002000a000314030388070f00c030310300e81000250a44130190001601c2c1d0f5503030301e030411410b18182d400310442e013144444c03142801a4481445600015480741006000714081c125040d94420b11002d210b59051800714040c50030140e4805d55a40a200d170821503811500c5044849481c0030b9050300d6808071656a103410f210a08401107000d09000f030203080d082100003511100180c510103000b403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 810846366 1250 810845116 810845153
    0x115050c01050421050f1204290603011518050a1d0312060103090203030901030f1d1501080105041214071502031b04080c0405100e010f06140f030121 66
    0x13015901ca000d140c00700310390500c07825414880304000d0046d42808820039101c0030000074541400d980c2d10303810100340e840c03401103458140014034640c100c1800000c0070150300130704041e0000c00c6945665030003051042c13290301901034020072606c01005a200e40341c01103a070000050b40081411192924400030007402e881840d45550008601500705840a096a9030310120074602804101e00761340219490f841a6000141019202d800c01644400389030080107240000d602c1d011454454420a141c4035101c042107180311501301340001803400014010780c0d001d59004180206044040740040e901d404d005a40294400c0007800b10501150182d00585a290f070700e62005070b40c07440d00880b014100c0c0d80340710070020114000d0100344003010700020601c104c0c407005d41c1c00042503110350b0050701c0644c000394407584545013814000304804c900c8500c224200d44c070035142c04c070540d0602c0f00c049030b071805002550b61150b40300707100400c03541552290201d074044061621a01d04040c0e40c880518100c0a043e800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 810847616 1250 810846366 810846383
    0x1b110306012301090b07140a0215090a050409111002120414031c0504050f0402070204020a0e130b0102190201121a030d030e06040807020310092405040b0115050c010504 74
    0x50801c08040c2d55401c4000c1c00d10b00840070a09095074104540104400505603440c40152142840c508000b291400c0350010108059005480141e02c454ad01201166000742140000028181068040c0e041c02641c45180c00c0607909443c000c0c005e401c40301268040451081402507030003403d049004002074400c148440840c00d1003e003d042c58444400030560303680c0f5413007500240c1d03183d00809a40039100100d4000c4403120b4010002000b901802d600650f00bd480041c40c0801070350040741441c8056020344804601b508200640c074202c0e03003034002c01d85c09a00040620800401482e01207140e00c0d10505007042a0409814503600725007035200c1351515a001c0c0c25043c0c11074601004505560041d0f807500f031004201a0f40042d8403148054070081c00848040742c034404550341844400c14071051a40308020030712090a001c00f80055040c00c1907202603001030009040b030780b240251807041c1d4120040f88904c0e480c00c6500741c0f0703501190f054041085400c1c44843d00c41030080c0642e078051800b4250740d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 810848866 1250 810847616 810847649
    0xf0702280c0501020c1305090f100c08060d050604020603042109030309121106070c0b030907031a01060c030827060613050708070513050414040507060801061b11030601 74
    0xc807407205041e000710341135510050900030103640b4a02d10318000024407001080c0e075110000450314141400880030158014101d207617900262a41c4070100b29600c664424149884200034000d440d40c0084010300a604034500007805401c0c050300954226109a100c901410000c0c03050041440310048200001000d4800810505078000c4034200500b0507903801d914544400c1d902c900040041c100302d18080e090200d08a070030302061003000c400a05400840c05c4e40c1c2e14003c000c0984031450ba0000301c51800b0349800c0744503110005505503040e50710300d44444100101301d88055410440041401c0c100c83c889441008003150f80c8114828111001c900400250601900304040c00614064850500b842c3c03904106080b03a101701e01d650041250304009a4030302c0c0d500d20409100c1c403507411054006040c1416668506c1045e00b000d40715074000e1003034501031601c0d00b0302100e0703540302031050100003201c041c41c088842114040f8a09145d107d000418513046200000c80c0c01c140e001d9210904140211b501e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 810850116 1250 810848866 810848873
    0x61805060109050601120b0d0506090708072c10090c1706330436050705040902090a091107050f07030b0420041e0c080f0f070228 57
    0x450142ca2105014480b81c80c24600082484041035000a202c9031550031246498842035041034566405c1402d079107880c5840c01c2d200da0380b455035110b50f103041c0c4900da00c001a8840340d640c141020a8100303400c00c00410b68916a440014000740024040301c00398400000d030454184144410f60010f130701c5450700448a1201070885207002000940111640f825000e039500c1181c03c0e130b001d035042c001c680d07104042c1405e07440191802181c201e00461000c00c01340740841d030505032864034140d10b555020050b00c05000f6014090340c1d41968024082201400140803502ca550082e02c00b901028141180c0a66030781210400d0b41d5210782e403070810b407000103004000d10005000c0c018541d01c541009102c0d1910b9a51091050003006102900741c8204000455000c035011204201c07181c0c0003082403280d00301015040d0711003038641c680d0264240c609001102d00e90301907204544600410004080316580b001030b0400c0000009100c01c0c00c500501e492003111400f400c101c1042200140d0040003810140d2a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 810851366 1250 810850116 810850123
    0x3010e0c040b061303172512030e1b0301020d0222050a0305070501051c091b1703031f08060a020301030515160c020a0f06020102030901061401020312070c061805 71
    0x6a01034000d080c00c22800e0040485041300d4821290b2040c040c250100394440000d003140038a40c0f44c85e8184104843d070400040b40d984140d40390500544c3c0300700f00c0085d880002e8080f00c600030248203440d086030340c10510750703a005ca8241e040a000540050301c2c1152070510b0500b2a88103000b4005400c2c807010000410612000b0003030301070b00c4180d038840d100781e046864841d59464103108460400400040c0ea00f4924078010260150700501d5030148111020f91400c0d06c0342c01e10380c00044558158410000034103e81908040554161f442c1c040c41c40c6442d4010382c80108002154020003464001074002240310080184520030403594100680700d506519103641444544004103120b4240307403003400f050000110344240004070608285c040703100d807440441c81c50b5503140d01031540b00e40c2d101e00015181d9010f4005502c0352801074002c00c107a98840403c4c88140507504040d50040e4018400f5188401c400c0d610340e0741028190428000c0483c81b50746220135240202c05410030b00000000c900c08000081 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 810852616 1250 810851366 810851381
    0xc0114010807060c0503070615031211010506060a17040609050303010f030611030601141606050a0b0102010513170a0e0d030302040e090d0e130e0303070f090b122403010e0c04 77
    0x134500031540e11020f48540da640c0c0542c1002400c4079540d030241c15000034843c0b929200550b80b0004e0500c03c800c0100e405030040c000d130701d803076030303040d4200750004580d85044403c4035040c02d010340790000039203e200248151580c0003001212840da0701e00000000c600c0800185008008100062030302500314a000400d880413030754442c81d50081401071210703583e0089030020038240b0b000c0f070003620303150825515404012100c0014108030310306403d000c00240aa0040c84005d0700a800900094403110b000b100086490300c406445c007540300821580c0408204000d050f0100c40e4904881d04005010010b0044560303600c08a0210764000344c1000218407038020658000302d9400600100044060701601c203041d00018a4458070004040d844028a5a4403e203000c00905080302c1d1a860483e02c050f158450702ca0400c00803800c1903000040701031560088881c40c000d83d41410701c092312014004540100c881058016480701e02030003000c4c2741c41c2482440140b1003414002c1c0149405e0034248000c03140311 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 810853866 1250 810852616 810852629
    0x41401080706020d08130302010f0606020c0f060412021512070903021e0906060f0c010518010e060405150411030613030813080714070f1805130b0403140c0114010807 73
    0x44084404c003a9004400c0641c803d20a81101e01c8418441c90124010703d0440c082c250124a041d02c0441d4003940082c031800c5030711081d0303480012284400200700f2180500d00c00e100d450b035203101850006083c41d08240c8201d20b07420141e41c0c02c22450404150b90248112000000105159401c100b50715180e0f10501140400c1c40010307000300700d000042183c81c103009200e24040d0303200284202e104d45400d4220b40380d1070040300c000c0040e8104075081c03906028480c103180007198200740031260150000310304140659408002040980204c4190341c1140c4030050080d161011009800003080c1c606005440c807504003000f1080c40030390585000303442404c0c05410220b40d1076100c00040c0026424104442c0ca190304081c840a008000384140c1d450400141c0040f0940c0b030760494006044080d9404580500d40064824403590f610341c00b0124500c01c000402800b102d0300180440d02107800f81000880118003a50540d2030812600d2006084d030351464104140403e00d003004108481c818040c40303015212 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 810855116 1250 810853866 810853873
    0x9014a011701140f060d05100c0504051002061608060d0213140a060b0d020c070504150305010b0303120129160203070509060607150605030a0b0609070804020603070302070f0204140108070602 84
    0x821281c4c104250702c0050856008404260041d424004100100300d6440f607203d0050083c40e41408006200390407906c41d99025080c1448081850fa00204240784201410082110401e0007407804441e03001d03028041b01d40280d040d011110250b1100282e481c80c0004250000c15140e071340c0c0c0400002e0210042401b050349140c9402031210075150000c44440030031144015858070941c00080742803440c10b0740036517401464030700f4551300c040c111703106032040b203000340001c000d01c01c4044141601c0c0d1080c5100020210116001800820001014824014000070b00c000c610380340305e11044841d40c4521014102000362488600440c9001c0202a010f04000c0d504181141045030118a01d1301400800600d24403002060340c01c1105d441e40203c3c028a0300070200e4500000c2030401c0780d01d200054811a01a80316100040c191500844035140a2603000c0d2140c1c0ca141d468000031402034110203c02c50b41201c50410718009030350b40740074403a0b0115610080010b2075151a00c4549020070b9580040d09540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 810856366 1250 810855116 810855121
    0xc0507110415060c06020918010e01410415091d0607030c1724010e0310020306032505040b09191a03010e0c09014a01170114 55
    0x2035001c2c02c0b9240d0342420f001c5000c2e140f4058010340154410306801a2008406011400c0c6e8042007904a412002040c0d11603600c450703044107804140e400311443d51030346400350821030200d80c8460101c441e1995075032140701d800000141c1541d9204526203002e600050050220024501c0ba82d0354890752503d00e0341003101100f0a007500c3d084014141030a05aa80240c090010f020302030021141100d00e1490845240054481c4a0041e00510114580010b1695407070340e54000c41900034407040040040c5170444410790010041d41c402004150503004101610544d024504082000048058013400e5030034200001c1c0800c03034449801091041b80e01c0018400c60310b0892410710158041c4c0d807408594851906020b0810129040f10650990303c1c01003910b2200d040403404d40020201200c000001da640d607000480e40701e0a04030030700c2046c00c2d01d4910200500142c1d140e0a40d4a5002028103512507481103050b414483c240e00c9101100310f10000b891a0060a229400f801f0308004000035060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 810857616 1250 810856366 810856391
    0x50313120c05240c0304050312010806070917190c0f170c030105011d07050f0307020303071e090e0a0605061c0605010912030f031103011d010801060b160c0302040c05071104 76
    0x10f01a00184c048a4000045024081d0910844080c0c00c0245020b011650351000e907030f9a1418202c0321800040d0355404013140c1d20844e146d80490164400d8010100b070351607a080c040281400321411503500038030b200c00043c84458000d040d00140100b01c401002411454511820004510580c92082e40b40c5801442100a07105200300b96050a40740c01c0403950f1682402c1c2e40a10600c0e05c90381009030040704003c5a143c0c000020352040a44d59502c4088a0018095204400083c820440410352101c014020003a5202d5000d80c4a80150b0340411016075900c041100740e40a03403402049214540c1d090b0410000501508008200c20704e0900c204071701c0d0940485001d940500010104650310302006191031203500201d84c00384004200d10b0752540e641ca260030162922044000c05c440703018000150700d0006210300c500301d0b03010241c160325200c071289015220b81402d40b030403a007010743d400012001d602c83d481913801c14081900e45680d00c40013410007240c541c0c44803402ca80b0580c109486c11059 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 810858866 1250 810857616 810857683
    0x60a180b13083007020a03060207110409080d18080a081b0307022109090903030105044506050a050a0e0c01171008031630050313120c05 60
    0x5080c40665180400e407401d00f00780c01c0368825000302940c060507002010050110542c02002102d2080008030540b074050b2060000341c800d20a00a400684140001c001403000e5800501c1c14a41103181e0100684082d6611102c1d41c1110f0640c0c0002a44031040208030000088580300c80344060010904514008500079540d00b19a030040000c0d00c0d007911881050010030040d82d00240c001081002c0c00d24020903104d540f03400c02d01c00e040c821802c0521106410043d180078102d091440041000091001c9108403c90000b40300b44001d1810440c1402c004980d07988156802074541000103c0e4500b0050098015250342d405454555081007094a1250783c101e4a2668410b483c02c0f40e001c4c3c0356850a0010351090b603550310203e0755006c00550030840024001c140d0080d20300c6102d5507480080f5001c1c1d6080b0f16048141e0711310b09400c5010100036024000c40185034030119613404455110040d40c2d82c6000e0003448000035020406020076981040b409102044148105c400c030080c149203181442003c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 810860116 1250 810858866 810858913
    0x923060d15021b0105131203060f170703050d0305010603060e0c07170d0e0c0a0911040303030f0b180f0c031b09060706110d06081605060a180b1308 65
    0x3000d0b0350000b8020441801910703000a024001002049240b4001480e090301c991180307000c80b20701c4055040962984e00a201d44003e0300c806003c0716100d035090400b46040c840d0100c105050070b10810b180040024820810150341da51613a4022400d949031410140507295981c003c080c20708036807410041c0710404007042c5c07507010340c101400103030310101e01040740403500c100380101c20030718106032803407030352803400510b1051070f06007550020000303540d5036400340444070380b0340c2c0030340e0804020081000464401d0300600080d0007080c030300180c488034103800500d00c01540a41d5503002d03900c034810000c40000e4410181c0d805044030303c0ca20700d1171130715000d04800800440940c8000c143c0100e06003885071240002c2e0351100d54080c104000581c101451a0502d401c000141521142800b40200300c0700d10106408442031181c4048860460500c2c0c104001900403419030700c1080814118000c280d041c0b03400940042000214469481c40b0103c0300d0401d000603070304900f5162b401044500c3c2c110155a801c0364 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 810861366 1250 810860116 810860153
    0x518030a02010e01080a06030c060c0c0f151413092909012c152107030210030902040614120f0d180b0307050409180506040308100923060d 61
    0x85c402e44d20107042800810003604040c00a0030302a00100d812900012035040031070085051003080307591044140314000030b80c0550b460007014018200f0b4101d004e2010134115a03452700040c0d0078140c42810644507a5119842200301a454886031140350b042d004092a528898808984582805402191381c200b0103100c1c6003800846541c2800050392b0700c0d1110b204030300070f1824004043c107200301c03030000c001c196011191203000350742e034414200c0344289000c1c0744212402e000360a000d0314503020032814038156400c00088c10389030350903100107a48a100d0301d4060482d09480705030750b14203101805107840c056450106641c0c0080c8280c002001c00080c5a4204a9646002d401844061071071003029080f0342c0c0070100c018004000d215030329410202610594007820300030041e4115103001c3c041d84d060000b40107003082e0840c0c8007150100344600000c13a8414003000c1c01405480d910186e0b0800c440341c80304200c10b500d1f81091000c0d045a031720316150f600205e040710100301d0780305c140d26240c00740c003003070342151 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 810862616 1250 810861366 810861377
    0x1908072003090d11030f0712030f030b0d031d0f1f030e151f0e07080402061b0c130207020a140d02041a102c12010207030518030a02010e01 61
    0x140e40e401002121038410010300a09500b803203601c2d00d0880b400c4840c1882c0c2c424050700311101036030300b00040c2a4080b103102c1c003c4e50b02c9011303c584081d64502503c40558040544074080980c494450390026803070b46102c1d41d00d00b04030b85c0041c0d070030414404240b40e141d48500b0607990085c035640c0c0e441a0404000c030b81d08030960001c030000a000c0d801040314010341456400350110000400340d0305120184100c1c512201c1910b841c000307410394548141130b4042c40c83e500f80c1907404207038103030b20030200d86911920280440d4039069509880311130341007040d11046070701d03440310401b05080d003001004404c1c0c010941c10258180f12030be50010b446803943d40140f10030903005524050b9075644006013001000d401074000c1101c403005520004084142440e00b6014090145000860622132585204421030b00c40d6408840840c8049043d44e88803507840c4564040ca24040c8402d43c198203100034005c0c648682c0b07480ea0b50b00e00100e6140c0315031380c1d1000c1c91072007500107440742d04c00751740c214410250350706003444c16 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 810863866 1250 810862616 810862667
    0x4080c120106050a030812130309060e0a0b030903040602010f1b0f09270b010915050a02120c07051e130e01020c070303022a0d0b2802190807 62
    0xe18014581030f80020381c071040d03419000082c00300d0301c40107055040ca1862404001d66504107075446458a40304010005490700800300965807241c030302440e481200401c121074080d034845000449402c2a100000941c00005041158540912541d00540c5c40c041040c02520b4031a5101e03840c160758003141105102c1b02c55000240b4622074030180c1d000c2c04084c0006850348540b44804500e6040624020694910340070480c0318642c01400d1080c100c1e0a0300700605580005450120b8058029400c0f090940c803803520b4500d8003030794102c0a04640b944441c000d01c0694034000030007401c41d0081c0c00c40d20404159642420303081d02e50300032004003a0903c244c003054106c07240c02814024458140103403054090b9210110030503901080e00700c0c140001d40d1022003010b10410440c40e607000c11400c40342d44181c1c0a91000000b40c15a440700b0741c002d10a0744204101c400803040054800314a264400400350b00080304203a880c09004200004841b07864100d540d40707021080a404012055540709950880299 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 810865116 1250 810863866 810863899
    0x611030a0f180803040609060809060109020a0c050601030b0402031905060f07090810060608100605030411040b0a031110110c0d0204060f060801090f200c1219030c0504080c 76
    0x440c122420b8111858032903540d40d990390940c0780c1d0414090300001650003400010380c2c0d0b00c2079007210300400081014000903483c000d0203800a5002c00c0302c0d4010f002030030030848007040003404181d001f1400b6074034407060f40c60988101030501c801020203820803040d400400000c100c0018815611450dc4411110b0f6525946030a9816140340e44c80190144154491540508800d401c00022900c84c0e4850f01a561a0740e010300507524014040d04000072400d100050108885174403426501a01400000301540c071800800c7c1002c40346d8005813007140207112103840304d00300044010050100c915040d210401c04000c5545c443c01000006441590031500c0b000c150b543c0d0b0307800383c40148104074414800ca5076984016041c410244500d440c414502030007000c110509000f1048400b1074030b010135154a10700e4041d10342c10740008680b001c0c144660a40352f4005200640104524400f50500b00c41007000200d00070282e403540c81e503c404000701400100200c038000514414000e0084905044240b100382 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 810866366 1250 810865116 810865127
    0x50a0f03021203010603020909091902010c0c050405040507171507080a0f0e010b15040b1605031620150f0f1e04050102060a140f04060b0d0501020a090611030a0f 71
    0x90b0507036601d000000000b10160036a0003060a42c10903980148107036600140903417209070400380f0f240e02c0c11080b0f501c68015885540c68500082c800c2d080c595010b6210000704084030380490382100ca680c480c400c10311401000c20309146ca40c80c59900182403140814644e1403229501809020500c0780900102d6031030982c4d50400c0d007910b898690100908610244600c6c060041a55118007039541030740f071110f0008101d4110f17416914036074101890080260b0001c4904035000c0030589180c001880080c1d030340b402d00c6811441290087e07685400500d40b143c80341d1100001c135071019108000d20018a82036522510548903054002048642c6440382020500360740d00c94a145c030400c01052110a2200c0452500035005941d400c1c0e0840b07400d5956000c01200322200210821803e07082170b80041c1003c4074484643d40c0c841d1140c1310110348420108045904240207a00c100d496035004940341501550200382030005208a240054503020b8803074405440b4803401025608100304121405003590042 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 810867616 1250 810866366 810866383
    0x70609450e0d0e12030f133218010302010e0103200c070812030103060b0f061305090903070f06020d1509020c0d030507020d0c110a0906050301050f04050a0f0302 71
    0xc60a212200301040c84940b81c1644044042c0070400080c01100e013402d04984c1d0304111800e8500440c6041c5251141b00c4041e00001c3c8908603034603202030702040e14581c7c05080707005600080c056034034180e82c0d00704c11403075000501e20f2035015880644a103040070302c010710003504481c0c0a007002682e00c42c0e41c04c0120003424034640c0c6070329030140f034094840070080341c1c400a04101d59660706580300d454413181255160b000c180c5a46604407030903c014400f1030103540c8422002c00004044070103a46040010400c0c6410040900f0030311220000308004a04001d5004ca601074021400b852a00750300d60340f6070b03400c18a140c2020304165070108000b41080c00d03035030081124201d0142d501c2c00301a0394403c00f0001e035000e074010302024014020440000c80c0280201400745590390040e064100350304404443d80d1070107182c2510705c6211800e08002030f072101d20144024084c6001c0204205050905060030340c1e4014200344c0080c0c40d110100004988081918007806600c80b1802e90307400c0e1542012440d14540 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 810868866 1250 810867616 810867749
    0x1080c090a03030507060f0e060c090102070e0f10080f0a1403090909160501090b0901080907090e03120f0114210303070305090f2a040f0e070609 64
    0x5041c02005154200014080d001e01c43c040502000c000c0750084c00070b403402005070020310b9000c2008903505001358005401807000c184101c4400f15030740c00780100c00c01401e80b403080a01c1a8403003404502d986544966001d841031000605c2c034072160070703840790b51080b480a001d803068115400d0411412001d104035040303075000406007102c40c02e05842c982d44400203100c41c0c01d2542b1000f5000203455006000b1001183c07069503000d42808001d0006450000009180c2ca9150260100209201945108488443c0081c800031512000b466124084440c0e018107003482c501c0440b0010031542d13115800b48850000b05803440c900200031541400b40c0c05109560303c1207640030120420030415415445244182044400c45009890102d10306448810b04030350030245100e01480940042790f40390821034000c0c0d000e840083c4504a19061004590010003a0700c0d16400511082150310752012101002d07001c151010b000441850300c1300301445464455030560100790340d034441c1481511905080d40640d9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 810870116 1250 810868866 810868879
    0x305040302062b09020306010e06030c030732060405010f090f0311091311060901110a0605040b1014010e060f130303020105130f0b06030a020a060207090b01050c060601080c09 77
    0x92101002851214280d2a02241c0c1c001001030903d818940a40c07041c094001d4040c1400e80d013401c8c3e02c401480c000070800c54040c0705040e0b0303c50f42502c0801400000348a00d0024088041c0031100c58984030280d50680d600110450f5001001540c0351400c135000c50304242803500c14100300707000c2584c0100250b0700a454403009a200041400318040c201010450110744007601a50340b0400b05101000b1300801401c000e2031050003909505200700140401ea00504154000c5109000042e00d04002441d0440d041519101070108000d40203e142c0c1c0c1041030809c1e01824141451084d80700100301d144040c0c10812401082400c548900040380c216105c1070200655814030381202d0690b01c0038a1004400540c07800001424400c004990140c4403035011741d404482034070503202e0041c2080b000d408103a050042c043c958006980e040382074001000ea6402a240b8149064105030803598484e8106046c003400300701c45031205d1008150950301c00c4003400c2602d82a121110703000128090301c0405600b004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 810871366 1250 810870116 810870127
    0x7030608030d0c120c0e0d060204090c0c020f01021f021c0603060b100306050d0f2d05010c080f010e090a0501020a050d0b0a0f030807060e01060314060906091207030504030206 77
    0xa850fa0040c100c50380c0b0381d880e00c00122201203003500c1203e00c08141c1c400014590649903013140381c644010070701180546009070515444c3d01d5090100c42542542c800440c8040c84600c085007032842030b40400140900241101d04502d00001e8840422200740c05c4c0d08580c00076050820340c00c002c0400c0c1c000c0890500030084242c8030702e000c1004100903680e0718171038981c10581c0142903220380119416204003030641c0c0c07608122a80d5405c82d41c12001012a402030412034903c44040704209807144a0104100c0605104010304100e400c403071025580900f000b6003101002100038040c020103044500c01080740d4000d9490110580c00c1200d02c4c5801807195000003403c0c7c205070361140103441d0281c6111020483c1070582c10030807800303886602c07507400d000da04d2107010408503900d50043d00d072090081501250303200725a03602d60300f180c0325a0812a01300aa04143d1039181c42c082040d9035101400d1002000c0c1418807000d51a1b40b180180f030010480c40001451740e0030544200b06840041d68081c040c20b4880 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 810872616 1250 810871366 810871387
    0xf0e0717070504030303050f0c1c020d0203040602040515070f0201050c0a1502030108070503010b0d020625051b060a1d01090306020403210c111e0d030e01021b030606090703060803 79
    0x2039100384070607000a030404c4082a202001c1c0d2074450300404134070422a00d0f2014049240ae03544140a4005540541c24000903007220382c60b000551055108940059503507090408221840b8064402803a8015083c009240082e01a20030b1301080c2d0340900300192a01101a40e00745403030000c40000b880803101e840754070889002c5801542c10380d503e078002c0c0d85025072224249400c840110810580c8145500e90340c1d0058205080144294a9400d0140d5005201d221410500d6000b24004490540c4410400010003e104c040303800080001c9805a1400044540050107000c000f01002d003020301010f02500c0aa00801414005540c445d1081d51500d9a03420203c12503803610303003007a4548510f0700d00c01d03d41e42d01c9503880c260055403011803511031070920b106104140c82e03d411041086d0501000081540d501e10301286d0b034540c400d80d2404140c0c0c40840009007052503240640d400c1009840c1480801c0e500411410f51048098403110350039601c0400403006000c1d07652040c0f00d540400600e0f44280c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 810873866 1250 810872616 810872627
    0x3040605061c11091f12050c0d050a050c090402010e1504080d030e061303020a14010b1302070c0e19050c07080703171303170a09052409070f0e071707 66
    0x200c0400c840d10b80300d90b641d803c5a071022a400d4807501440300174080c0d05000140b0664281d44d1644c0c0603404546c02c1000302d20105a0500c014141510540d01c4200ca040421000300050110341009403030112040c241980080d0140b9040c0039560301c50040c4407003003180c4009801c16140104014000c4481701d601c840400780c003d040700300c819031050080c24005a8090700d03442c0c1d52001c043d03040c1c0c014401120301d46c07100707980c43e0200e41d4104c07899500c60309141a5651082101020202c6030b1900513a10302c180d10b840c0414244c03035441410309080d54010450031600810420710010600b00300800c4c150341d40607412449114580e070041890078080b4203074051650010200c40c280e0080e4090244035200d1244800e101c1126000090011740c00c4202d00b0a1300c1c06112215401074583d102c003240c60304241d620142400447c0c048102c14a6900b0206911026403401554200d8691005000c010382011a00c206e044600d009140300f000b0107801040900b8843c00307042c0f0481140641b001c24030305281c2c02c000e00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 810875116 1250 810873866 810873893
    0x60f0606121503020d0b1008030f030702011401031e03050f07120f030504151a030f01150506040302060901050714010e0102041a03130b0a0f14010303170103050303040605061c 77
    0x120145491090340c2c40d803a00580031403d0301e4004208940b40314582e5a400b0302c2071002001400ca13280a0040041e02042c20009040046c0a9100003600c9152a86000342180d007081e0b500d11280000800400101e200d1031134110600710786a101050758102c90a06580911070143c00382540c0c880041c4240c00d21985012100c141c1c0703040d50340c0c282c00380c07905141242503a40035100075010841840d1402c40e0021280c1c840e020490f4082d4072591000030f10000a0b0a04070303429488030944e51a880080c0807440c3c1c440056000d000f0403502c0a051500355000b10f0094051490101d06020b00090050140318207110800030503c0000000c1c400080d9100340386010390071510030165640312542c070316011010781409036441010303450508405100c071a2103040e00c05170050061814596281c3e983c6101146074010000c54a03680140003185500d18a0000c100f0240713459203500c04014940144001751001c4100c94115411040c04101d07a21030341c0000f0f0401000d4007601c030704003c00c02c69500420035101c03040c25 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 810876366 1250 810875116 810875147
    0x418061e03030504140a0e07080f06010c03090e0c160c08100905100b06190315081f0906140a0f06051c0305071e0515070f08040807060f0606 62
    0x18480510036600109240060000401140050000740304800c140381c0d50641c0f00000510103414242c0e96a0600908101a01d0000001c1c02403020003601c6443c03104241d0b0020f0003840c046021041a0310b00030b140f00c40d18041c5030400072280000c41d407812502000d840d008001c035502c2411000d550310301080035280520605400d4051a50036201851062003800c0746260000007601c100303001c000442004080c40b1203200ea0102080c00f15009241e88072080a000c4515034034005461b84112074140380c01803a03036001c11136586c00200802c04006110865107183c004048001c40c40c0c50300d9240000c003520040126010b003903101010880740b0318180d00404520b5100c00300c00c0181e143c8801c14086000465000c40e49902c00707179800c0030300003480f07030303006000706801030401081c8807106031318141c088560484160b0351980b00340750001000c100400d116801c86c0d03c034108001800300c095005441108014005000320030301044e0941441030700d41102c070000140907010419140c480790090401c181e00508007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 810877616 1250 810876366 810876389
    0x70605060604120206130902030a0e1c0c0f05070b180906040b030d0c110d0305030708070201050105150f2206030e06061503091203090a1e170f041806 66
    0x40da0324100441110199075203000100244800d0b074017804a182e00080d09084d00070041d5a0009500d00710788041c600501c0c0c108004250001d917075030480d1501808400c100c02c141036048a0440540c1c012840101060f80500d005c81d481d465410014108405903000c08070703051000a400d41c41c20994540c0d80e001b80c10440c3c4242464031850305010407111422003030342d05903014000d0700c02103a006207402c00c0d00600c11036403840800f100b0800700d010980000070031000320707002100f482070300398100441d550301440620082049614020000e4010140369200c3c0c440c2031800611101220411350844021500c21404a00d0034144a452003802042522403070b40040c3c80c0c166400c0f076106000c12802d005d418004d000c0c111044039001a90400d90000e071541d12140f06450382d0900d00d80c006809548a4000c540280c401e00c0d003681450103a80e14003d0240c0200e407480184903001600b00c0500310304a0220041c078648841d0b400813801c2803442540c20138100c0201240400c0072401c0c194009509540d06030b01203 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 810878866 1250 810877616 810877621
    0x21030d0c0e01030c0e01022d03120405012d09080c011508100212240907020d031109370e0115020613080a02030d0f020d050912120406061703070605 65
    0x455205d41500007590060301f1421444005c00400b903c20b6502640091130303404041101c03681c40d03241d58030a5003904519001c05041200303100003803281268041c000da178101710303214a541c528100f400c001032803645c101d6903c81c014010f1040701820b0b82e028404071130080004504041d90300840c8519441444198810300c00140640600350080d81d00b410094010361861ba101c1c80c10f00352212411100420300504025488403040d940c400181c1e00480d005d0b0082d18900e140076030000c041c1c60800840d4600040c0401c1070400545848014201c0081c4040310145009040b00885220300e8804800c2d11140c6541080880c4d820116844c0318121203144000c102c2502d6451802d0b6201c04003103d90710b0fa031220146504c004201c9690007800005503a2064919010030818007108550303400711240b034500d40c0898040c80802d602e105054010255000a14818100e41025542c40c810100003c01c0081c0840102d030420440742c00a80160a00f4402d01c55030410181e000c3d5942c2d0081501500c0e2107003004003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 810880116 1250 810878866 810878891
    0xc0f0f070602120c121b1c0504031403070206120702160b040302011d03061e0603060403090b1303060203241f2102030f041203060602060105012d020f01140621030d0c0e0103 76
    0x401f03803101e1050b202c1c0b07030a061458459200c4c41e408000c10701134070f000810851005036903000090280c030640c001407008500b27003c080203241065820309002c0c10301e03504c0c0c41031106050344c0c000d031000c4030303824a4454104158036082e40380110228511039014481c200512084900355103203c8841003c581d02014199a9001050707a203a00598007e8041084404140243c510010007000c51178903180030602060307500e5440030102c2c1e0007103441c64051003040107180703080074a400700380c143c00404403200d0640c084a025010903589409200c0c0c2c0501c482d0340005042003d2a8004032440006250115280c0c60002240c04a0020442c0d00300ca020b024040e10744401e5010b44500c9050340c0d066030003000d141c0c1c01d01005540a03d603405000c2904010042c5c100c2c1445d000c2940b0302d0442505034007070484400c0b421501400e43e100c048450401c0c41e450000c1261a80b42c0f50301c2624281d00142e81c502d11101408692401c0d4800e48404201c0d8500f02000303400c01e1504a12071010100c020380c1c0c00c10a2281c0100d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 810881366 1250 810880116 810880153
    0x901030e011d0c22110f070c0f05041b0f030e070f05010e061606090606030506090a06051e040f030e031203010815010b0a030507140c0f0f070602120c121b 68
    0x4800c21210804034005480060391a031020b01101d0108804500d8042c0d40c0141b920700703821920f021119076524030003d000038115400c0700741c01043e050f00e00f4407100e55020500026801580402d00030010304e4040034040394820b400102584044205941c0c201d0348416180c1d29081c61401890701198104400c40540d05058040701c030ac4d08143c038101031103085076030b40300390141c80038506c10394000780c84140120104205000b114002c070f80c2c449c0105280003c0c1c2c036050301507540041000d07044041008131121004204a9603c0e07009510600c070704000703d5240b170162503640081c0e400c145c0612403503c0b40301d0003aa60600a605036004001154611000d61105540c0d0071024000e03161481d805101010b11240030b070300515000406420407002e05a070640c003600301500010304802c2c55500c482d014800140c4140b11820505601c4000740020a0400354040e6949420100440b01c018000400550764401400708180d140190054155200c2d602c0e020f8105626402c44200420700805010590403910071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 810882616 1250 810881366 810881389
    0x1109090c090109090c09050603012705012304061a070311030901050405040518010c03020702040e1203060108041509120e03010b3006090a121704080901030e011d0c 72
    0x5079100c0c043c16040100001c050840a903501d01440358200e400706803985e695001d90301a00b0702c000c440000001280b00001c003004203100a5a54501e010014403c0703054580381c0b00c0e16501e0440c9050709000a040103d40204440e038031458081d104005c0f003c07805c040480003017001500035940c502102c031079a00f0710342d228401c2d0243c1ea800304101300010003440c03c141e003001d507000c04041c80e134009031401c090f5a42d00f0740e48a03030110700000380c0c0041d803a011490705200e070380c41e481e5048005241074150038401b99041d10001d0245810302c02e00c003000908112002c101442001c10005040c00070303188920300300c1100c110201420001c16506004107865050502c950800d5980040114150441e0300e40a802e00c1040b045948101a10680076180c0c131400c00c02c4010701500401c4002c140c6288141810b003800318a0410320070400000004408854509500c2a900290091a201d542d81c42a000680051140f002d10000e154200101c24107941c3d4001d0245a600c1c17803920031348507050642c0f03003040f024400c4c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 810883866 1250 810882616 810882619
    0x807082406040e1c02030417070b0409020708071403031009021c0c020c18040b0c07050a062a1d19090e03041205030306010f030b0d030e131109090c09 66
    0x44030000309a441c003600204040e00740d08050b1005a00d0001400414000044841015900000e000c203c020f60412011021640180141480a04080c1d11900d1031090344a258142600410f509061082c14411a01c01541c40720071280e00600004e03095840741c0084842180707400b541440018250024000c440c16404013000210706102c4055000c0c3c010125180014110301c103400300c0c08071a40300c0000c1d030000d144134841c141d42c03146000e251407248104000c00303105411409200b00c2001a41c0000d280b0881c40c0d01c039001161820149905184001c180d140291401c0c01038440030100c180c00818040808426000700c2404001840501240900944c2c0200d0409090305d41040340000b00d43c003805ca040010000d40707140550307a003180b401007440c074078003511282c000006101c959a0010402d400740500750900340001e55000000075210002c0c1c00010701841000301c0f28403030542c0d8070308138070480b1208450200407018440221103483e400400c541405048840041034001c1c94401c144c4091400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 810885116 1250 810883866 810883933
    0x405060607110d03030e16090e010204080604030c1e080703030e011b2706050a120b091501020a1202010c0323041707061a100c0804140f040204080708 66
    0x102c15003440034200d03492109400b019562802c107001d640003400849840f10055000b01c0b1041e040c404041c084031480358030308055030b1040108001042020508a80c881e4150078400209030050900c10868010300d5815000d842c1482561401c024500d030240000c41e000b0756040280c0c081c00f040d5542200d4503e003180c495500c1107010841101c0c42041d2000f010214507800300e4241d004a0032031600d04803240c10600c04035001003000010f090b480810301702c400d1021507051042200b402c0c0400c80d00030700509000c007688941851003220703034020000c200000364000d409201c29000c0040080c02081240481800a0f081441d258071103a040c0c54410092005180ba88147c1e4071150b50f008003100e014210301043d80800d0107004040fa0b12445034002480c1003000c0315040b103201d10108070031036004802581c20700c04d400882030046200d100075141981c42401d007421401d02880b0000390001280d410b02a4000e000040100b80b80c2000309180c1d00703d070704200403640c15001204c070303404c3d80f80c1034100261544403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 810886366 1250 810885116 810885143
    0x402031002070302010605180f0a0c050301260a0804080d140a0c03090f090507080105120c0603072a021c12080c07081b0c0a120825110405060607 64
    0x5030160300511440e48a030000090345a940e002060001d46a00700c500040d01c1244100010320740b00b4020180e22419130790301008800c80c0d0000240c5240810702412803110f680e0b0203650103150a11840c40c100300003600840f07040c3d1101d2300c0c00c00b8480e0f000d800380d008203028104040031071314020100440c60581e8141d81a003800300c0d01100311580411500c0070b80030403190120000d8041d45c0c01400a0180410080228403840e0512000d018034006a0200707000e084840f1580c0c101400c08100c1408002c41101d80315680d4540c00c0707088608010420305450074001221492f40c0100d000540012980d09c00c0c0c642c94000b4111060a41e86218000c1740a0405a20800c07500c2c4140d22a22046501121083c4424181000b54440740706a030400300e4890000598094901044502001001c103a40380071960f904146041954039111140107200040000c00c011650201140f105078a0030761010310444041500c05482c1440200011130240d00da02680c80c0001180c0d450825004540001c0d4008000150b02c9 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 810887616 1250 810886366 810886393
    0x602010e0c03100203040813060e041506021e0c040f0204030501050604020306090a1e0e0a021f020a1b031703071701030b010302090615030a06140607030f0f27061205040203 76
    0x4c5d44010012617282000300421240881c80f040d40c2c0c40901640d98510540c55080b50903c021030f040001a0707528042500400c0028540c0062000102d010010580380c000681003442c2d460032502c894450ba1141c24010100304450380c55003d0400c50703000d9802400181c884100384000c0f8803051701c0840d0440e109100040c0d18030110303004141c0309911100700f80a1507a140010000302d40000000c1075a9030003001400c000d5241103003240811083c004180d07101e1400d20341020356a51544000141009440304c52114100341e10b803851002036030801e100000104080701104950b500407a4254085440d030031440000703a0340343c11100c0c107881d48100100c5059086408100c003502004002c5548510030240283c10990794002650007101d8051001c02e01c1414505158036000d46074181e180140c4080c006000460b6000e240b1461000141c140220446418181180c1c0d841ca54900300d0222200410303400070031900c850401c0100c4495550340c05051000383c41078401c0d6401641d001e940740e0b010480c03040700d9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 810888866 1250 810887616 810887621
    0x30610230d060b121b070f0c0306050f06210106030219150f020d080402040216060b0109050d1a060307091e0f0c170a02070b09060108060f07140f0d0f060602010e0c0310 74
    0x405451422960811b030240d900c0d00e2041003044011201c44a00540420800080340601504111b01c0e461088031842d181020400c0d0304000241d0855108020b42c604204140a40c03204018640140c04800310143c507007030003880c030750302482200000320051072040d06240c411511211034688a601401d00040c4d10181100c0846015000340e81c8a0703403c2000c580745420100100700301511407007000c562100d8241c009401060030b40c1c0154007403200200e082000a0103010000d200381131071000c0b400c07640c4407080442e141010582000000901c0d01e601c0c0540c4126a41143c5100141488240240003100300500250b540d000181d00208903012110b0104004c03000c101da030700c141409030060504025480b04c00144071f06860b80c3e0400d1300003000500c1031610500540b0b510041105602490b818500b80040054804a50042d22540c020400071707420900c200890361301e200d1400d000e00403420f8035000303000103102c1c512034140550b103402c807403810070500400d10154481c80103021381285c0d10050000e401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 810890116 1250 810888866 810888901
    0x30e030a030806060d1811030f010b060304060c02070305030304050a0203060105151819031103071212050702040b0904060c020c100e09130f0c03030905060708030610230d060b12 78
    0x9000742c44400415980d5031501c49065090300070b950b44030383c0c20103290032301d03003042c04408034901c80340d0510440303607806d8a07410101c1e50816440308000500a0012204034100f500c00c0d00014114003000050006100000807401e200c10b000302c0507249140d030b0b80d1082051840480305a000114424050807005010410144e181001301030581c0b070b51556403043c00c6940341c150303800460f01c40300c0880e040c00013402c0401003100a006642c5400c0c0701d01074282c4401901ca141c0003024000c04c43c00152040864865401c881001074018080c0040c03070074030b85040c40c01740010150f844010b12807a4051207192a06040d6402000b84035220015440c07205000c0c4030184200416a00c1003d0b041c000b0100014400300c0d4460405004400f8400e44034110b01d002002c00c4030541c4140d200b08020301054001c1424003040b41d40008044880c201da0403007100c0190340310300c1c1c00813401549205100c501e0014204080c0100007258880204000b900d4407002e903d030040c003e425801c107105001e0400206807205105070100c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 810891366 1250 810890116 810890137
    0x15040914030d02130e060a0e0a02160803040218040c09270503091c1a0723042c13080d0f0c110607020a021e0402070f030e030a03080606 60
    0x4aa48040c0200038515401061030307510141c1d000481440c101d0694202801801c3c1000c1148440c4c200312000542080c060700904500894034170201e108540e00b42e044504803000204802110142410200150740007100c05a00840c405950391440e415481c1c4900c1c80b13944d10031600e03508541000c4c1004014020101d0760445001c480084410721505032614141d100d1140d0000c0d0ba803103003c00d051050000800380b507904051440001c00300044c04518401e1420120b0100509059880c000c00f29840c01c03400d8821444000241e51000d101300c107080040040c0d85808511410002e0322010810b211042e0381394403a9440c1d2410049040710790328503044503101e40540710311410100c46e66285400c40d5082e44120310525036a032802010283c11041030361540e42e030103000c0c11141c90011406915001c107a20000e00c15140080e010504005049807000312803070180c003c54840d5980d01c1d107030b40213003c40c500c113601203240414a0f003200c0c5000a01c03003070003584c1a075410f4087c1e119002804401e030090031440 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 810892616 1250 810891366 810891383
    0x1115010e0a09051207230a0b06060906070609020f120a1401090203070f0305070510020c0405091c26010302030d0507061803120e060c0f0d060b030708011409150409 72
    0x2e4085407040101d508040341d008262580c84500c0e107010103406103811307483c02c0501700302c100c0c6212180c1c0100304181c082d03404c0400c0301c405031b80e611b001504d07510601c0303410399001f4004a649400d002050b84140010752003990342d9004d030005502084442e15030b801104079958810150100007400352800341459150280010a00d0006580001d0419000b504080ba40410080c030030420f0040400048004100540d048600e61860300d000075114003020803018020344d111030102c3c0140f141040540d5100c85110030740c11240d014458010480e801c031180c40c580c184034a01d0907904e4080c42646950403650300030010450250581c030300ba952070704017010a0b43c2840d940d041d0342c01ca941d08034a401000900c26035400b2090100b600f035160440d243d62100c03040b564400c80402c070070190740342c0407100d035181ca1a00554a0729407000ca813002404071030300110705510002c02407100264228401605913100c2407200c5941742104403d016083e0000c45805540c45198410000c4e9428143d1010700414001c5518 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 810893866 1250 810892616 810892631
    0xd020903100905030c0601090b1e01090905010b0903070914041203140c120f1005060d060915050a090b0d020d050a050d080601090905090c191e03031115010e0a 70
    0x2140111401064255035903000005c00c1014682e0074002d007805010300c0001048000c1580700403c10307801c5040202d4900c28112881c9070000d83c06122550300070008c140d07050000e580c40b41d41c1e005007600075149560003171082c0034011914111600440003a08810150364207207582e1501c40141611001034404181a5511803a042c210940c09030716120300b082c20440c81e507882a44465030800d42c4020301e030031016100501441003e10f4405684070884030100c0d0b900381c540000b4403000d00140f24541c4505c051a25160401c0c20351106a880781045400840e1700100c800e6a40d403266081c0c0c2d820203c4c01d035020107070307146803001880c045007542c5905000d0400c07a00c0914007903075840d01d00028504081c0210740008100000d660707110205102030301c03a069091020b0b00702158a01c1d03980d0250107401d8490a904203900004c03003a002050720090902102131080c1804950540001d59904d000035400101004441d1000d14000609156548000300c0a8800e0b03a01e07088003040c480c1c4011f0040c1e20703000c6d110702c02d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 810895116 1250 810893866 810893893
    0xb0109031a0114061204060209060904231006020d0804080c0313030c15090306020a1e050a121803140c01090c0e010608040506070c0f120503090f120d020903 69
    0x307880c440302416004025079418007016180c614180c0d030b21148949003c020380c140c081450904a9001b41c0c0c40300340541c40c0c40894000480501400340801e4000c0e24200503101010b296840b030348914003051000703d4603a12a1400c0d43e54400083c010070b0302590220282d80340081c4580141e0354018041c04c0e0f068140915081c0c0982540d00090791050184001e10092051042076007140b0010023903940c121401a800b802e01400708981d0388170140600e940800e08000e1640280d2901c0c1d103090002c0e800d006416000780020381190402c1035028000384a40100f80e4020a1034800c8190268170f503a40b11014003d15078088030b1200f0490080540500d0501030034124120074010b000003a445130415005140c10300d14010400c540c142d00c00410041e948090001180011804981001080c60840041c00d091700384603100208842d0300415422601c040316188079400800380d8042c0b0f0303660301038900000311045075903035801c86822035002034042008100300181d8107074018130729a04050207681c8062101c02 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 810896366 1250 810895116 810895133
    0x509150c0d050a0c020d030c170a11040b0d15031a1009020301080a03030b0301020723010b0907050c0c010f050306210a0303020712020114150f0d0804050a050603010e0a0b010903 78
    0xc1c0c203480001c1d200c940350b20041742c041c0302c855807900562070300b00610700744450000c00c0e074840200701104000d0807401240c5000a0341d00608014246040580c0d03030b0f16504e00801c2c0040d409a4403000700d03149050b5400b484c1900c0c4001c0102101d800c405a03451504003e01c04202030310016050180b02c114245002a07420800d001860082545102401c4200c0c010305002c3d050702c03c0380c1a01071082c1d01c1000703060006003c01d04d003000c0b544030a9081d0411488a4503100340140491244140d20050050401c10226030002c000e2104440d01c80941e03070702040d8440103655400035502041d011400a00004080781000c0ca4641d0180b5901c91701000c4d400300480c60300e410044190010b80001e80c00140322420b0003040c600320000640d251008000c604119514180c01400c060403245402291900e00260380d6240104245c2030040101b10110001031450102101c3e0b206114050140100c440002014a032800a0700e04aa60108691b089a070320007441100824464014034140000e404010000c90080d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 810897616 1250 810896366 810896371
    0x160c091a030718020c0307150c140715020f070b04050a030f0207080303040201030f0207080d05060406050f060f0a0306030f030f0201050c0903031903290a06030509150c0d05 76
    0x800085950188120200403844515103078000d41c0040020031840088035412030510050240060300ca8803600a018114031070358102070002d410101180c90700200540c4000c80c8480d0644858050142000803e00303180510380c00506404940804040b40d0f5040d50003e00c1e1141d00c41c040d10345002c14541e280045d170f4009585c1680c544d441076541104140d042500750300d04a034180020404070b49442c98550f0340b0b1100400003410152103101c0103030b1403c1e050301070b00c41866200ca44035488a0a80204100818045480c20300c5141030050005a03401c00100d941e08821001d0704042c03602e1240c0c0300c04083c40e80034211440c10165104c00010115195041d14802540f09a07105c00310144580300090039108081c04114803070700100403400c0c856034000215600312415901c0000c00d202d40c08d000f6070060a228402c0050420a88005409080c6050800025070400c640300b40314141c5407281101240c9003100c040320607a01010890044c0d40c0c05812080e84050f8440d50a8070307140498400e4019110207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 810898866 1250 810897616 810897629
    0x1509040e030c0d0302040f030809040207201e13090203030d020406050711040c0f0f1206060c020307120c03020913021005030703180c06030f112d040305030906160c 72
    0x4140007007403074000c1c0301030003c4074042e01d0700f1340c03c0c83e041c101c051200101e248001008101c0c000382c002c1c2152180e4054922450f042a0310b40d440e140800300d5050008000d400b403900c105840c1100c440341d10607100d1403084c403801c054070102d05055840e00d0000100301c210003c0c1c0c1d041c4802d00c408a100805070008201905043e2740b100d0b2907440903d0143c00305240000d03203034441c60800100380e480642c005954000c140051a10007080c8204010a8641d003543d0500090240d0424401107003031a080082440134502c2501201c00c0c0320b0391414003a9000392031020007010003242ca8000c002500d0141c10440e0401d401882d4103460f00943e50014015451980802c1e010640200c100003a503501403241041c81c2c1e1541e005182a42d101c0e03901c0e803180924038082c0206040c2c1d10b40311000700304625848030506400d4120001c0c2e5070030748110207200c00728035544000d441080d0792070b04168500c1d181c1c05071021250300c13a004505003640a41040f006402410f044182507540444034408655040c0040340200741 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 810900116 1250 810898866 810898873
    0x7120303020702120d0203180d0c15200c0d050708060f1b0a0819140901060312021c050913140a060504020f0d0b0a0e040305030a050a11091509040e 65
    0x2c6441480034041076200c01c010b05030884055495415004412210507a501c15010030f60b186884000402c0089020005418107005d200301185016202003c41d40490a0b40c6855040442d0304601c1da1040c1c1c5c1ca994800031a0300720b46141c0b1801e0a003240116000752049d01a039070040d8540d010545412021101d21286c203400c40180040082d155030864080c2e8002c040951620720809805031054030041d0014842d401c01c48035030030241c01aa44804807403910340f0707000a040d00701840b055001c1c000d02d02003581e803503042c2c24904502c2800010304505501d9048851040021803c00079240c54004812160300070644190b82e42410000703200d1078001c2d500301024096903040c40c0d00c1d1002202d5840e001715020700d20411041003c6c140c21000d80e000c0080c0c1980104510000c13401045002980e688501e00c10380307000c401d2200f0140c015015604c5545051410440f0340d5a20208000307a426001c2000c041040402c0b401440c0e040400107c00c110580e000b0321840c0400d420b02180803202032013583c2903d0f81 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 810901366 1250 810900116 810900127
    0x20f09040201020f250b0708070f0c0918020916020601030f051e0d031118060f16080a02060f04080f0307020703020a12110a05060306010503041106040e01081006060e10020712030302 80
    0x2005d416588050005561910300f80700303441d5580d025a02c250980a01700805500b00082005403c8101c00081d180e01c1030144407000c0d81c0700390800100c60545d030803031181d200c00c00000e000400300000c9881421240d40244503a074659222500d40003c071100682d018019110180d5019000243c08040701c69080014000781c1c00000c0d000b021501851154050311508120091415055220448090354100e6107940d84000f0355000c01000c0c49014003500e070040b40080c0c40400d01103568042c01090f00541c00341c444542d5254251a445141190024070004041c4100d601a001100146038000c025004585883ea1a03400242902005602012400f011074100e0810892104000c00c0000c2c01035800072090350801000030458040208160704004011000a0601c1240a5000010131010b04007941d120740794400074a010009000e051340d00d2080103205a2040e65030b100d880103c1d0303d43d0b9580581c0b84259420801000034128034034086100b20f44000c0b5038606401e8510b120b5502c20784005035104e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 810902616 1250 810901366 810901423
    0x21002010612150e07081e030903060a0902190501051c0b0d0b070e0904050c01030207030c0804120309060e0d1b080304090b041b0e22050403030c030f0603020f09040201020f 76
    0x1c0b0380c80f90344d15000f6000f451081204250018840300c0000740d15602c00e0b01c03c514908150f00e035018142003641e0621030242071203002c03100c50b0b02c4411401c1c000d0310007200409401d004a05100c21a1090714001107003045010f4414a41403a40d08884598200224070001000c000035000c0301000c0003550503803034103400c0c0b0058a40040900c02480303400d9400051502d4103490ba6034841c804103690b14103042d00018100101480358a030345064590250445482c1c90701d03070482100400e100038044011030f4000d9000700b00b16009410660760782800400d0a6070700d0210b0f50f200000300340640b0384860043c1c40081c022986030720900150028014400300082c03650606402c003c1520380c01c41000c031082c503011414038041d561018848031094000c2e0341c0b10760700003200660507c1401141154443c294a02424002090742c960081070b0100119070301440010408660760044509ca40300095008030301d203495115a04000145651140c0140107444100c040c03056803605003520100b0a130304a802d01649000707407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 810903866 1250 810902616 810902621
    0x403031b02070602070b07140303010b12010e040f11010e03011a03150705030c0a1e11010c0306140112090605010e010611120f0c070b191707020a02100201061215 71
    0x2140801d00c020002c0c586012000b07500c07880c1a000780d4a41585c005100c405100441307050000a41c280400c0b29603030b40c0c0d01c05400301203030441c0380d40145081c0b01100000354032000c2820b582c002e98108002c0d000ca510195100d14189503401c44540c144280340d8020315081ea000e00c074080f4041700092881540e0030744941010b081030b000241c00e404810b40b0405201d403060b44401601e900c5405814026610000b041c010741d0700020681810403041c01c6519000d0010740d0205111204c03041200c000d100c2204000c505030180c44160040d044070100c4050960303550b40c490600c0e84c02c1f4001581c8009507000c21500d6050a54030f00341c0102003e842d203100104a6642d015482410200c13000300502007402c01903035804190710450910403052100413681000c400300621603580202120074074a50b03110720000d40102ca000042044c02c0100741041e48604a40400c0507285204011507030203402d0307040c01982084034016060400004544d030381e070f801203804040614003c1030180a0300502c0d5601920b44d03106010b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 810905116 1250 810903866 810903911
    0x1060611060c030f071b0c09140708070e151b060603060c03060310092907031a060d0507090f06030b2107180e0102030a02070c06050c0a1514040303 65
    0x201c014100304200c01e10300d8500d2041c1d000150b071b107040424590760340506142c91131050009003100101c0c000000711b45680da0b00c1091625060404c8094a940360007003070b10051320031039008001c101080020515490f01c0300f5191a5200050251400c0c48900c48048030002d2400d1008000d80d4020380a1100c01c1c07030100000341d80701c80740151803448c510b00030300403a480304000050f44000e01d4492b5120410444c4c81444250900704001c0da502e11003001e10b071480d5100c181541c403200400d141c00001891301c07000034a050310b1220b024204500e0148a0002900240001408002000246000401d0500b070719075065005004940e80864115069402c00048840018140e40c0c0c45081e03110b0110700c40c3c0b0126074082146e250700d0500d413800c80100c0c41036000c9e005002c7c4086155100008010329a01180d0103400024000c0ba42131103a50340f14003059a90784140102010350354000d00e10140017030496450041c601c03600313450105440746960300b2118849020b40c0d0444c0401d4550208400070700d0602005030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 810906366 1250 810905116 810905131
    0x6033022080d09090b01030b060a0801050406170615060c1006260d08040212150405070b0f031f030210030207060b06090d0201081509010329070807120e0106061106 72
    0x12903049072001c050010185403041364403054503052540201da01943c040a060312014000c1541c0c2c00240d00020724a14090007282d00c202e241103408100d00f41c00141c16281c0c040390368028001c039104d0021140840c44c655044540c804010000c1b000300c00001c0c0300081301078681c20400300314030342000c4444020448400e24401e40201c40302e0340040a07a0700040c0b841c014806e6003080b5402e03445600100d001c0d18002c5903407022602c2840828166a192000e41600c9a0f00030025210150345422000c0c0c0e0038800c035000d0504104c01800440c00103032000d98541d00300c44440c0001e518196480d4082405020402601000301c0c0d408143c000500100303014005841e0b10444006103080550300000b82c0310903400001a04004241c030003e24800c0a01202d82c40506000f8050141581c2d00d1900d44500074210f0050340a07034038200c0318001c081d0806120789004d0a070548448003103580720742d411284442d03100501076400352900b0740a10084401c1c4583ca001d40300c3c903a900303003055803100c05c1a4a07017940540b020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 810907616 1250 810906366 810906373
    0x90a0210180e07051912050c040f140a051c050a11040b04060506042108070b1603060323160b030901060e06300303011202090603060603302208 63
    0x301211342d0002c00c0781d002101410120380b2202c41d601040798415502142d01d26954602424026400000301c0600100c440010b450349010b0340740c03180d1403031100b0300101c0315410a01d440c1c0c0910042c60220759440c1100c00803000c0016550072a1a020318100244001350b644403030040006c0442d08080c001c1692400e000d84042c0030140c50080451560b20681c03065400560b042c003c1c50b580b0207150b0380c001500ca8ac01c14a0340382c482c901410f05100d4800c040d541c0e40c000c0701001d990340c04d4050103070180c0000c49400400c0e418050800b083e541403101c9540e6054889030266280140540d084240b0b1038020b0640b03514401d4682c40d01706841401c41e055030704280d1001002008000683c0e81b0034084400240b03403100c6801151641700741503005000d5440188000d4000800003050440b040a400000f03240212615a103544900c0c3c281030703c03140c05503826074043c0c000303469107066441c0c8000408100240048a01c01315559106540000e421460a01503d0500e4503250400030410072588005402410b015 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 810908866 1250 810907616 810907621
    0x6010c02010f1202161415010e0a0f02070618110123090102070f0626160c15230903040510031104030f031e02010605010c0b090a0210180e 61
    0x103802e84003201e2001c000c00c0310f0b800741d0340001100e680588045100c079030549280342d00c541ca822080304040c12941c0744984900c0c4080c4801703620905000b8104c50078000c820750180c9420390024041d003001036003140d0041d0200001400211184142000409146900d2a8420892410000e09080300704000d0400070340c40a00c00c115041100c0290312500380c1d101d01c51760b03000c81c000141d007002201e0b1300c030324010948290001403a40c0c02190080a080c0c0c00b0000b41940c2461071002100894240c0e6003c001300840340c00301040700d000b4000141c4581c01a80300b075102e0710039040404285c4a0280707050320116825043c180d5403210351400ea6070403d01e550050b50a060034007011402081202a580c8201600c4907151503002c3e0684085034080d640082c124150000c0904015208440800c050980c42442402c0c0180592041c424503081d90340c145d40d1801441300031b4441c2001e001c4003611581c0c0a00800a030000165510300ea03400c0340c1d0001da1101c11b80c1d1182d020035055028803641c828121400356004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 810910116 1250 810908866 810908869
    0x20a05030d1209021f02070807060215040f030e030f0703110604140d081207030c1e080a0e0f0a05060712090827130e19020a0311270f06010c02 63
    0x2014000e081d401c42c00000d8400050000440004106080031281000346000852244d40030520505403411442101d10030760b40c8100032039488403540d000a101d441d1200c041030002d400c0c0610b0010550180c03421401c02d01c00c8400180c00c011500c0c003010015480081c040040210b0420040700e0810110341403401d0500d01010760b0a91400d150340d05200e1010248080c00708003429050b144d88082c1c810307801003a0710708414090010064a011480400c404440f040c41d802d200b0389000c69440004e070344d90201501c90721807041c06001c5038494040c103030003002c000f6203c03a0010091015628050401400c0c1c82c01e01080c040d01d00d107420f4200c0c1c1841820920400c0104440d4401c0700c17849210311200070450000f445c0603140a010f05a9019400303010115041502c21581d0040b4000781d1090040c1d8a400340e200481c04113031802c10000a40280c002e0f04200041864100c0d810811b440c064003294401141c5107010240744012a00f580a1412000500c545c4ca0702c82181241d04c070b6021700300b40603021903d40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 810911366 1250 810910116 810910127
    0xa06081815010f0e1b07031101020a09180c0e0103050a020d150e090a081c09020d0b0703050108030a02070b09060c3306090f220f15050c2d1204020a05030d 68
    0x850810301c600300012506d04040c0708400d00c83e03140b80050008c54441c121014000d020b162b0510031200c81184001c507064001c88144102000040503469003404001c4010054000d444010004601d0590901c0701d03604104080c066040207451085a012909042c01140c0103c1c00014084a2942c0d00a018140004040c07008482504440101c0b11801d204c6d1110200c000c0e00413044000d40248141d0500002c0205190303480f8007821142c2c600348540d81c0c850405035564004c000700100181c3c4112410000303e00701e140140070b010009044c5c18902541c1020350b515001f4009040d50615100380301c65611902c030002c286448500d605000d102c0317030030b0400c009010100080c02c1740f8241c0d8006000320300782e0f0700500c688400806098445040b5081d290900c10208100d6510550383d072810381041c50400307646807003030031301c10408030281c5810810506592600d044880b0642e4480b920642d000c4460300c40d203003000d07040610704c00c03800301124500f502c103010010041d540024000d83c17003c00052a07254006 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 810912616 1250 810911366 810911401
    0x7020c0d08072d030215071b1a070503070905180105060d0f1a090a2013080a1202010c17060f040f0f060e13020a06081815010f0e 57
    0x7944658440c0d11070704000704088414152540d0492480c9601c07040e044088a4040b40799003c1d400f52000382802c800280c4030b0780401c42d244070001d200501c4041107502481018104030b80100341d984111160324560700e500210070380d03c0c800403e4010003007281160f0f111500034080c1009456103000c1c80300c1f088140000d0f03401801550304c640004582c1995200b0f80f60321101e481c020140040c84000c0556101c451007039101d1280901070164400000d6001c07143d0700031420316103440300541444480d40840078800e13400040600340502c140d50030008031a1010000c2d1142c15000321148035206545420107400c40c0c000306104824840d1200ea0b94502210b11860103500800a582588104481c50005002003802c1144040302d54a800c1c0c541d01c071441c440c0d12504c156002c42c82240303015103880844545400d92684001d40c04000c0001c01d01c5190310410b50960003550408101c0c1e03400010211050500304d2120b02800641c071400010130000000f1021400200100030350740300c032410020490142c15451 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 810913866 1250 810912616 810912623
    0x81614031302030f060f10050406051c050304031a240906040b061606020c07050604120201030b0d02030a0f0615080318030307140d0e041e150f030308060907020c0d 72
    0x68401c00030554505000c500d00505082e819189a0b2030034003e6051542c000317481310b0007036003e030480206050a05204400a403180100542022940f2069a1000020451007110230380402d000c0040001c14200c000c034004041d20030440e02030703d1f0039044040c03440703038010702c0500310580b02401d10101d80781c0c0e041f01500b00400380e42c086541d902e00404030340319100b40c400c1e503e03000d40c5131a03104c4180449070703020340100d458a005540c80c40c0d41d00d404015480c02039028080c240114201c0503c01036000754064a42c610010300a10349540c0f00f030700060b040002c03211003943c00c00b044114980412500e48201c02c150003904001005180c104070034a9502d0081d0010240c80b0b0800392110401d940c0d08000307803070515900511100031885400015511440103103640c1011a1001f40c89072005c1c9400e0048040e40d001c1c0e5440b03020341c030310010002d9003c0d001c0300c41c1e10141c407401240d01144204101900201550080d02c4140990501c041440440301c001048401150081c0c02c840d040b40d9600c080c0c964038181c2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 810915116 1250 810913866 810913891
    0xf020703170601110f061f080318150f090a05090907030803040804050301060303090806010801050c0304111f05090109080303091f0605060a0305061806060301060f030f02040608161403 81
    0x40b1400140c81c0a100910366070141d01c101000802d50710000503085115012201a68441d10040d0200e808520218080c1656070303002840351008008910701c3c00e680e0160010454030002c03583c2400101c5a50103d022089100c4002420380d0303040c2031031000200100303020b0b41c0104a51401d6000f06484803600c0c00000c01c0c1041c00000f03d400c0c040120b080d60041c4c4402030007000015624034015081d1140c41c86611001d014950001840b81d1041c410244900401480c0c140f6680d92946d451008403041c0c1c002030383c4240d024142084ca040c10b000d104203000c9481d2141d965034482c40002424181c02540607022641c4208208402401c002c180f0755070031100030b2410594075400b0111480540080c0e00402e030005000704054503403941c185c100c6c50040100b545d43c19142c500c0ca8910246080c1c04075181500681c0800040110902c9108d08020103611458001450b4101015100c20b9078099400a0700250170502400325100d409841c0f410420018140207009150810204216010040003600f2008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 810916366 1250 810915116 810915121
    0xb060a031d06240a0f0b0702280b0901030e06010303030f0605061612022e0f0c1e0c08040b0403110303070506070305040f020d12030c02070b0d02250501050106030f02070317 76
    0x2c50321003007130001d808002001c0090039102c401c010055000f40700243e200d090b090130007042c5240c4035404415041c5240c039241d800300e414070507604919807021640504250f030740c0344120311442c000d00026002e0740c440e03680451411080600ba40c1510f016400203031013040b08015200d40762550103590581c1ca50301c1954203000c0d041e00c3c1d10903401c1107905800b4402d00b0f604003d00c0e82143e00d1504e0a042e80c481030380340c10854140340d1020202100c00007800f803004a40c00b4800500403d400e00062028209185898445401565241c6031541c000f41d00c04098110003140600410401e151a41c01c0034500794011130401400313072a00b55135810090402c40c10306540f040030405110000c083c0b600da5035000f4100c0d0b88018210b01e80501009401004500020300c4d004000c02103038400300d15407040340c1380074298608140e14214201c00035813219003150300d082e11f00e01d0346141003940d11101030700260060000060540c5400702c003800796298641c4100045204201003400203800c003000f0041d030380042c0108085513 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 810917616 1250 810916366 810916369
    0x90c0918060e090f0721140304120501090c06030b1c15050c0c0f06100e0c0c0a1a0703090c15170a2c0712060b060a031d0624 55
    0x41110340c02695400c6444810012980c3e07000034000040051001210021581e07668050340c20040110b216040004d520301603404640700030b03000c0c0c241480300c105072464039139654045000c3c440010030454581c0d4440b10f04909002074111800300421103420300780448000d01c0c00183c10b0903880c0c28182d101ca00103e1000c400c1c0102c44242040c00c0031048410000c5040181c3c0c131817000e401007075420310903203c1c02d07030007066048010400600403200400c1c1e1940260928150f00f0710680010f20313010083c4c500303200401010200b080880e100307a01482d00440c0a90030111843e2143d40c004280354245402c201191002410100741074080f5404c0c00996070f07000e120f00700200e03410011400082c03950012141849920983c5510650151100e0044c954441c003c40250401c2d8103001c03440c0700400c2c2c00107a8100044107203101c80c054118802c66001862088010004860b5001940d9502c006652281c00141c0840c81c20345451500d0841c13001400d81c0e04c0d00075080f03c1482102ca00c243c0c0b80c0c12004840e48401d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 810918866 1250 810917616 810917621
    0x16200601170309060a051b0f0607030e120307050c060a2c030d0501080c0406090b030a020409020a080607050d0c020a1713080a050c09070f0c320610090c0918 69
    0x9000000300035035915840c00170000c1035034200c03040710f25440e24000600c441e00c8070002902c0200380a440090700aa0f90ba01134141d0041000400a4140340175040c15155844014002544a20394a443e580d0703d0b20420744070716180c9240140800c82c2140f60140001d40f0511841c0303c00c00d44088264203200c81824004040e0950055900c030390001d509003030010590100c049019040341c00107403801c110b41690b4140362015a03c00100c10707501500508000d9004d1b0501d60060054240090001880181d40700d18041ca080c0c4216480000100c010580b00c0345490303e40608a02c40d000b030f10081074401055101d02c025075403050a01007640c5030006810840051080100000742490700544501c01e60b40d0504c203840302188200b483c0f082c80f990000880c0e1502854000a00c16010750b034071030404205540e01d030810003131000d50b00780101c000e500190b81d40e0a04446130700070b1079503a00580710b5820041c034140c0c2004195017103100744500309540c203440d0551204044c4111902c0301c83c000d40380a08003560400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 810920116 1250 810918866 810918877
    0xb130503100f0f09080708091804060b0103050601050408100b010e1003060f050604081e12070f0c0b031618030501020c06040b100b2a06162006011703 66
    0x301801840d00c11034200c5141d61003040c02d800314001c02d1041549500910701140ea0142c4000d01940c81442007002040403117028110201e00600a030f00c4a038170b07210001c41d403820110b0302202c0d044d8403805a5001540e05014650700305100382003903401c081c207083c1071540f940c24074214154800e45c9c0385090103031070303128070160034203094060300502d20807010150080240205004421888640400014540c1007484c11141103400407005130040c40c200c0d6000440303440e0304070b401241511a414104900390072200040203264400c95036115042c086250080032540550700007036280c03400780304000c1c5035101700f80003100e214482e182c041c007001c201d240101c5540b8048c1d000035213298408540b50042c00c80005d4054041c030300640800010f5070f58030440310201d42e0180526400050141303c9008040d01409041108510410004403030151035680300785042000c0321406406a85483c05010040d00302001d0765a101200d070024580c940c0b0f140a490340c0301c006214180d2409185000389601520138029a01c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 810921366 1250 810920116 810920119
    0xa09080a180803040302012a0b1602060601020a081801020a141e01060308070807140d03061a07120f170702010606090801180303180804080312060117010b1305 70
    0x5803030382036090380204884466070080801d003a0400020400d4080003080d14112541603403605490200120704207504062003c41c4030000740d50360703d0740000581540301d41d0700c104140010544520420300b0001d141c401c1c00742c203d5042d50041c1e40071802040401301100c019030031400500d0228003500740101c0c646169030a001d0900841c000201040c8000804c0088400d03c011a21004e12608402d40720b088400e184801403414004000344000500d404000d0030341d007070089030340c00c0701c0303804020300c0d181081c4545c400c0000080c1e0300d4005002d1040710400600040722a0b90406081580071f9407114600601ca00600e014042c5040c03019010078450b8482407071115600b441a00700e030900900c0640600008d020303070400710b450210080780440c4c05105d1100c545d03000134510301d00207030039443c25002081c11180b006007094a4981003408a50a88020801480d0000045564840441244c0d440d0300300a003030300741000280034210014050034000f09042d1109101c1c416039810350201100207800490388442d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 810922616 1250 810921366 810921383
    0x9010509210d0801080601061d040f0506190b07081b0717060601030e0c040b0f040612020405010f031502031f080d081506180a0801180c05010801030b040602030a09 72
    0x201a8003015a03070040c0107007100700b02c4040b01d841c008281c2e103000090044180603030101d001000180d00c1664403400751603d44001d1a1404c00c440041010742c1c07110704007088000d45600c00c0c0091400c1404400110b0407086400160650400543c51024031a103240035024042c04602c0841d10812011841021580d040c00c5502c03080d0b440d4240400c03041c0c03c6010440a00814001a07004e50081c00b910005e000920040c0502c5024802000010055112440e0b0401c1c2d00a6411001783c0303a912800010300300e0b5400e0b8600d0761815104100580300141c0003601c03540303d49541000042c1d9101c45030b00c4011100b10015880c2c1d60b80c005540300100200300c1d80c0c07501c4003440d13000140032040482c0405421714241d80c3e03000140c1c0d8502c000b079940c00f21454802c0d0044000c0248031000184544101c10085005002c00c10f4503640760301071801c0d140c40c0703114190051000c001d01010084201050f0004007400c0c00c0c403248070340c596250b80000d07d100410151049030000000b40000e151a8008103d00303a021000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 810923866 1250 810922616 810922639
    0x809070b19030b010e0d032d110606120d140c030d230727152c090103020607081303050c0112050408160816031205060414040809010509 60
    0x100d65181c0da00381c4080401d107003041c0a2441d520468035900e22800142022410140c1664205c8905241080d00207903600301c00b420382d113141461105074501e484150b89100b150310790400c02c68180400900400c1c41943c03002c54142502c0004108070004040e242400c0349d2301541144000018860244680c015000015032612403046a501c61990f505142d801e20a04200d400d240b10410790382943d086000c59a00150542e644032642d0000142c00070a0f00d40c048016910011080703d5551002010007003200348008030841c42142d4003042c24260343c0d0b60700500c80300343c5c036012941f01d03401030001a0191030001104824070a41c1400c40c3d45501381901170448541d80d034104141c0750104014206d00192500b01d0340d00301c8401340e0194601541c0c01800c00d03481c0100e0840081c1e04c800f64084221150007083c0300d9151800c07500700000310514041d0312060189030320b0020031801c407040200124856449c0400c24481c0d080d00c002a550f00c180e015042654408036800107803540d004202c02c003580240c50350b09 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 810925116 1250 810923866 810923887
    0x33c04090f0c0c2f0a03050705120303041104020f07020d0f02010e030c09060d05010b1c030305070f0503070c020406150504030b160f0f090e13150b0a0302010809070b 73
    0x121441407403a40c00c040101c0007801204403403e0030305690190543c01356020035189109411011100001003810700e070010b121802c00f2844d40d480951084c0e030321350400e0404001e6801d0040c000741c080c00b0030303402951a51410782d035040495044542010302132070b408640c1c8036000841b98110740045030014080d0800000c40c0c5403110301001084030490000d51400b00c0740340300c3c0c28001401c2080c80001440d03400b0076903545042c0400700040c080d040d0b07a40c0d902c42c00104402c0d26a07460f0009a24030b40fa821041a07555810090305503030b00130b8414420030400e000e41c4a00d0b0340d403080650f42c029095103007400e0308210900004010388020340080710340d0003184943d613030307150b81000003401101e200e694101c1e981c0d0f50b6580c10b140c10300c08c9915404046402d4000d5807040034401c07459480079008909081d50100c0e1960345403440c402c2d08a07444005443c0381d000744070901821003403d4130396401c441814003218031090701140c80c0c1c400701d2000034180000324020800f40d59050107010040c01242a01c66101c001d04130303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 810926366 1250 810925116 810925121
    0x70305040f080427021c09020a050904030f111902010c170a0f0216060512090f060a0506010809070305030d09050f0a06091a271e0705030f033c0409 65
    0x70032141307020f0f102c006507401d4400078001e4440303d2060000055101c1e1161070140d01918103210201d07070000f241000070034269200050680914001d0342e40744000305000c24050060341c60076469407126400000640780c101041c00c1569900f075820300e0b200d580796415281c001811412500105e880e28008180c040c800340c3d1020248040c00031a81c00c03503c403803181c0006554506564012500015003c1015503c0c5120700d40034070340c001d0700d400101c80740110506440350500d070301a1111042a62141c040c02103541e40014001d82000d04880600240c62456a815560f03100d9280c1e4441d07a15160105c450078000244280c1405100803005e55036841102c0c41d25000600b08c1c0c10044410790304c81034509000d820000b5a842c40b85500034010f031000300c001e07140481c803050760301580b02ca02d00c0341c030300c0c10101130010140c511502c4940038020a04581081d04050502c0c2d0002c019603000d07807050020222418103419041616230800ba041c00780504030045860000140030504810514001030004044e8200d0307 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 810927616 1250 810926366 810926399
    0xd0c2c040b03100c0f180806011a0d0e1609020910031505120705151e0904060b070f0507091107110f060705240105010f120b150306030c18070305040f0804 68
    0x280d681031403040132500d2503ea24403580c09100c1c1d440d42310344010710074048406001c10b0501030207540d05046c806c0300c05000082d071b140e281d1007000c070381c2007216101100ca0080b11100040d1644a60540c01c1104200110f0904240b8406840c00c158503001d49038000506105103101902003d0700100c1c2c041e0303412004980e00c1d003252146501610f80398000306043d040300070a5800000042101d00c2e030305076268003072012a41281c0403140d8800d039160341c000390b0b0b1b1103114014000107106118411081466040440c107040d00b9034808600c031801d022403144000d1441040302c0d171166200c03407074000d054582804680d487e0360206106410003000900c00c01401b03000510451400520b22103540060081030380e0907000d07072083c85024046041b80803801585801213681e84444c5017810030001d08054140c0c0000c10140a803031011045110010030311184c1d04040c460385a014078203850460080e00f903202114a00701c8024000d0b41059540c4010404124144a030000c04582180c00c1a49a5469102d2803048400070b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 810928866 1250 810927616 810927647
    0x20d031101090614070804030206181f0b1305130b13050102030f1501090b0901030c0e04060b070b09070e2d0a02120601020a02030d03020d110d0c2c040b03100c 70
    0x70a000528664411b9030340e284210785c140d0152070592140d1000102103180844030100e680201001d011003808900003d100411000801040001440041c01209030b6000d000c210b8150800d000c0000811000c0801d0560036130112080056940b003d08900c0e040c185284001d22550000051203441e458041965009032100c080032400f803003204c401515080580c1c0702c2c0c112004003d1250040c60f6006ea8004030322011941040d440404400c40000c040310001d80000f070303044070086103007014400035403412640060448020a440c0303081a108540d0361200905015062449900750b008a5480f56500001141f60003a00000c6044c40112000a5001101c10403548031080c80020850740c40010401020364014029224407010b41c0e90440180d40001e490140032601c40e40b1b5080d001800d54020310410310791080c00980300003400070040901001c03122842010021000200402c0480e40c2c44455000342194000317810000d03503001c01d081141c0407411402461a1071000c3da000e58002124031341c400c16 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 810930116 1250 810928866 810928901
    0x8070b1c0c0c021804020a05041d010e0d0f03060f031e052d030901120b030c09040f0b091b132307020607030c05070b100b0711030106060903020607020d0311010906 72
    0x100701e1841c076410111170186d0301088a8404200c1c2d801d10764050550b820151048440d400014503615003074644144044c1030b10340c4182050030aa59115171031164042551500340101450040914141180d40c080030700413400032070415417046030401846814540c800d094078800c070070524110104100d0141602000258100101a84540441103031095801610303040c1c11800d41c600040020917461030a96014861404510450394440902c140316030f1142940c00004155850310303104180025100b280d255005515001080d0700070030408682100548601c040c0100708451384024114550000c0340005401c0184100418620b07100c038070503103150302141e01c01d80350890118103d441d00141c0100054082c041900000c050711120380c1c0141d00514420080c0d904e52805214a6000301c1e42201c40c00c4609111458500303081c09001c0040c00075003802c0c19803070700e541c001c0f51441c0f1510f43c009200709044420141050700440c403030010881ea403c001c108410700740c54503d00a104e290340d034105490 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 810931366 1250 810930116 810930139
    0xf0e090c0f061605010618020910030516140415180602071a070c08030a090f0605210604090503040b0408070e04051c0509030a1a060a08070b1c0c0c02 66
    0x242400006201080036182c10700c0c1542034800541081e4888030210b541d035403100ba0016004011107044105a00700030710050f540c0c9806020081c09030004440c2009260070710342080404047c240103608940082d086c0880d554546c2c11808025110715041000e00b600303d61140f0140a5000001d803440b90000c0b00c01004680d11044240c1e91051640b00b00b12080301f86400507941c40107070501421a091103030450382c0a4a4640345000d00316000b0004403400940420390401c68078024854120051003541006845c03c85001c904804060f1220b03506403040d101c00c0c0100d002c5441d9640725500c4241c108059941f12521564100304590003441258014421003002040c55039121003103d00a641c0540245280210809444004040c00c194401801400c0c172084007161410303c070714490039103e03d6001d4000031100d0360322443d840d000303031201d4040c0c02024014041003500080f2a015a1410702c0b034251161600c14400c0018160600380740b0a147c20880b85040854004142605240c421034a04101c1c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 810932616 1250 810931366 810931369
    0x15090607031b152301050d0809100e030d0f080c03091606050a0e0301022502270105120115170c0402041d160e060d02040b16030315050108010b0901020102040f0e090c 73
    0x103180c0250704c200841c032120300401485c500714460050540c4070350703901402d00d082400042c0304400d4259410b0081050100b255200307103030a00c0302c02150552170921006465032503400401406008180441d40a00003010685010040090741e50340c0f044150341c084010b490b48030051003a081709001c2c1d808a0202504038820f1700d411b00981e090910710035141c00400008244256044501c008140e030000c0303807400c1c841c0306e00145111030300404602d85082a40e41d454901401070b0142001da41c008540d14000202100e1048407258100316104070905040840d600c15207a0304040c00b003404240d2081c40001c001940c0c0600c207010030022a05a80740c003d00d0b503594580598441052101800003650050040c5120700e0300d50041c050401d00d80c080141055222100014541d025200300d070000b2081803000c00805505004d04c4c1c2d61104240200c1d40c281c0c0c94100007824128040c0500494001e001c50500b10341d92003541501c00410703480010101d11540c0d030310160b65a01041c4e400d01c00c103000e0301c1f42d2200c07103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 810933866 1250 810932616 810932651
    0x904110d1407020712021302091509090c04030305030a0f020c0d0c06200f0c072c07031109040b0409060504210203040b0d0c03140702071415090607031b15 68
    0x81740d01200c020b000c1c0f01810740c00c110400381059090f2031007076801e00c6010174940700d0141c42950240f82c4c0c0449652034109000f000303001c0800500c0030f80e002c001000203000090744001a29048546603801244030360708100d0140c06070040051414103842102000140198810300440a56001c1c040821010301c20700d0344800c0003c01440c403000101d000300101c1d550a00040c00a01c007102c009001e941071151144052022500200d140c400f0103041c0c0403a90108480840d041c60700720b074880c00d080000d1003507414014814080c484405100e50754070040c40180791503075000041400d074000350411113840e00e03280c00d0f10241456400030760990180c13032072040c03080c1c000021142034400301d441d55810801342c04a044c0240c080f0a00b0041050785070b0448080e85642e602c103080c0680c40b2500603000d0306052111800031002c0400d40c10744103c08a1900c8500d80390180111f404008050b00d4a0f41c3d41d040030305098901c10030340310a015444000304c84a9003070281c29000d072404c004188600b1302103641d0030092883c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 810935116 1250 810933866 810933869
    0x31b1a0403050a0305070501150611010b0f011209080d0e010e060108030c1b01021005191104150806060f040f030b092e060e0114032b050904110d14070207 68
    0x1541c420009507012900980c082d040e100d12900010078909049c451244c90011142d210a0105040020342d41005500380524881c4030410703104613441104c8007000800702e401c5a02e144c48100d40d41d102e41010b01410200b283e0b4080d00c81c2c0d0342840000388c0c07207030814000e02144451001c240138074400032500110120840704c80143c080c6c000d02004c8408401c03810545505c0600f01d040d031148814150001e491801080d1040044007114450f00c5040c100107816551171081562013070000b0002406112403039001a42d181541307240910407960382d10003040683c442c0c41c000800d86240428001034813070000c1143c006480c404d01d08402c69807910f841b5165501c0d40301301e0740c150300101c0062000ba0052030382046503c00181d502c01251103644c0b121484c402060070303046501c0c540c410074642440c0d81006c0040c1a10b90003078603a03020520505445030046d640c02008000100000011202d450b990b0316044001244d030844071103a5103d6000c1300f0200149903076407a11101c200e2107000284031b207002086800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 810936366 1250 810935116 810935123
    0x1403071d060609010504030605040c03060501060507051203060102010902190f0e0c191e08090c0a0e0f0705070b0a200921070905010f06090e01120f0309031b1a0403 72
    0x2086501c644040044a0708021050740c1049024440003012030003502890380210301070001e4011480c1103080c41000e60b04160400c0c018040700b00000e200240000981c10600e405040400361a44c460100403130140c8002076000e54440581422001505082a00306046a4003402d02011040e07690041116807a000c4a981001810a12441da40081c030585c0c00100c04085103003050010f8074040c213240d40200000c4408000078001c03070420840040400c0100603000003100c440c0005c5140480c1d15042580003854810481c1c44400801d0b0140e00070341c1076580690f881000344030304d40342000019000b0308041c48155000380c0001050850400b00b2401c454240b60050208501c10f018501c035001c1c0104c1790f0355120070512400380e0001e000032940c441c18bc040c00c0e00c29450310701149014002400859544c201c80710410070840108041da03091604025019809030f0030b407001200c507003003d940c03500a41d8009040090f9000c0d0707034440b913044a054034003500e0440342065056013802c082c400e43e0f03001da0300004 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 810937616 1250 810936366 810936419
    0x100806010522020903010b040501140f0316030f031205150910030c05010c020613060f1101180f02031005090c040e120f0f0f070302030306040b1903081b07140307 71
    0x800c242c810640050840c0e0300003500100c1c0992803003021400f200c0c42684000b01007108002c0920300b62a10340c921520860084004050580c4142812240300741c10780b02c0142408003801c8203a08040c016042d08001071003910f0104841e01c0c1000404800c2070028010790301c29401c03200060044554103410b5001c2d0380d00609c100d0459810440152002452403d05903407001c424060175003000004082c402c0502400d503255260701043d0300002c0c2a0352030031440c03c0400d0741032649613805503224580d40c540207901f020b498415050280086820415940000c510903414403080000e03082c1d000502406604040c1c900f080509200c00201380c5802900307100f95000d0724200000700c0e2942c500c001801d42d42c43d00c0392040d0316060080326080720541c0495000c50260300084200304a51400340304440c0030f41c100b6a9841c403016150101c0501441c41804003c024807004076140c2005807400d41c2390211581c06100311602180c5418030408000307130b05080c0511910034203030b0100e18181038402c81c81020310142480c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 810938866 1250 810937616 810937669
    0xe06070b040b070e0a0807050a06050313060908070218040510020406090e0702030405030f100b12030a270303090302030123040305070f02060315150a0c15141008060105 74
    0x82c034048aa0140007401007082600d40d1034401c1d03541000e58001400303e04020560741d0325190034042160416801340050103014410048208081d2a01100c0d140d800140000c1301029480c215803130f4000e01c9000794100803428518002c1d0105004840d00072806031048541c841c0c140d582d13400592065000d00740000f12450802c001700400b0b28003460300207805005907400e060311040440d1400d10850f040722550340c41005449114030701c038400c0c1c1e000f00c1400c4d103d000c00941c1a46103180d0364441d10f0703405410440c0c5000040b904cac01240f6154050107501e840304070803e03580c07801c0c000d00540d02c90005a02c42d5103081010446208001e501e40340d0402c0060580c1865612910280c0d01da0300131040a94000000d088a5401680c0b0301c40254402d03102d90010249a00b000d000b07100241c04203040041111031704101c1881300f40d8120140258903540700c03446002d9201d609040d04042c2400f00f420001454181c1e09000c2c10051004a040a030b480340803c642081e070740c0340c041050f1040b80ca0383d07110403e1240c40c034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 810940116 1250 810938866 810938873
    0x50403021c171b0a1d03070515090a091e05060909191407181d06130c05090412120b010804022710080c0402030c03131a0f070e06070b04 60
    0x2592040c40060081d800c0c1e850070003c214540d11100300d16001584004c000a80c8400001c2c0014840d082a802083c03814180000f103811000d03111850095400041460794250340e803403c2c0b000142c044000c1c24411030011014240d8100710010203d12030360b0904000418500b4540d0a04d0f21812a4900405140f00c0103403c00d40114400041079516100e8048000300d940300c200500710080060000b00f0848044a0308890200e0f014414003010720a0210040e0b0001c040000e000c41d04801e88a1034000c4140580c034019012007000c0d8030a80d0408411000c01041c8550010103d415407401d4171984009040556080c04072820482c0d041d0111341c400e004a005814484410010034810b10804603201285000c400c141d02c0c01110f600751402440e220510512a0a210342a00d80d04151815070850411020b000d52900000b00341050040c0707503080740028403c0031041042140d4102005d1002c50800480c580a681710884549001c02c180421880050030028200d0f00c1044e040900c1c00900d4540c0da4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 810941366 1250 810940116 810940157
    0x250614160302030f071b06020d020c091909081809040b07120e1506120c0604051c0f080d0606080405030901080402032112060307030305071502040e0a050403021c 71
    0xc00c141e04610080c08040710300183d80008241042c012110030541507407041103c107014016810002c11900460079800c076890300000d81d901506811511280b040c0d0b10600120641d210384100f0401280c10701d1600c1c0d09010b000d1008080c1d07005008807455101122034180100c0c84000d44004240c501d820001586007441b4084404925014503404224041c010ba807491504c041c4514486580103500184085454116a4252200480e1014007034149041c00011000d0046208840c0210320800c90b280ea0b0905856421800503032100010000c0307001400e0400d166080038050b02c04462600380081200c60080c01090f01c80c5602400071481c100d0408011142d21401900803070300f5210b01001c1c2a00d1000a1082e6003a10f034030146501d03124140d1084030b900f02c0034060040350181d08490424008280e0100c1219a1543c11659805080c50b00c1c00c4110300030f1249510014030030841e08103100d14011a50807850013203000b68200c520f992041544503a00d16094030031080400d40400b0303240300901000703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 810942616 1250 810941366 810941407
    0x306190b04020304031d0102010b030d1407080c031c110d0b0a0e1602190305070b15060712080a1e0c05091903050f0309130b03010b03250614 62
    0x41408105800048085010b036001582c007100800c0d40040b1015824030100060300101e00c0c01d10080c001e00b240b40c00400c0c0c642c10107142a60401a010001120340390717138403085a5011750b0001e55156500701d624002307904c80d0480e031100d031000c000646201907080428051103d0f0300e81004102c40c40c0c149101103c030f0040c41c100c0400c40c2c002071803c1000541d25000b1080a10500e613241d00c0018080031a1002404e001c0d0007002424280484c103528000310340d01500f910000d5078402c804060540710406002680e81d0500a0254440d10010301c0c13208104841d0b13000e55014082c0d0303c80304030130344134034650f007080d80c2510540c002200708080d4038002c0001703142c014005110990030714034a8441000c1c040b50119030a2005c40064240020b020010072030104415080e61603c0c2001d0740c140340440000841891000103146a1140c0301d001499050307500303500c203c0420100904652400c401041c000024a21010304861035010b20100060454003c4804141d000c42c40c0c8149860300e110200c02c0c2e0340388000c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 810943866 1250 810942616 810942661
    0xc0712051510181509061a041508070909050702070e090c010e01030f0207020406090603210509060a140304030f0f03090f0b100b0c15070507050c0d0224090f06090306 73
    0x20352400380c03440070b184d85040000d0407a070305020903518208120003110b140740c4881079842c0300701008104043c507001140410700800c1440d154a05031590302e0101e41422860300001d00310b515220600ca01103800140c44812610100c148030038070380e01c03c40569120b031000180c150106400002002d910340c46984914000020f05c00010308200181d000700d81250019086050582c0e0780344024024005114001c1008031000d200140d00400c08443c010240d00612003a0783c000c80000c15028441d5000d2034001018501c1400801d0f01d0340340a007402444c0840004c19180460003070029541044c1c440c0c050103120b940c11140300643c0042d541e0341d000440d41d0007810404013040400c1d010890404440050512045d60002410080b5085003102c120034400b8210509100d01041241d000500200c1c034070103075800c0ac89582c1d20420131400800c0c000d03c0036000100390042107140b25407000070800d000d851141c1d8103076403c200180888040c044944074450525605600060000700e010b005801220b101c0c003c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 810945116 1250 810943866 810943871
    0x1020d0e031e0109140109020105040e0408120f040303050a0e0307140c030303090f01151202090403230a0e030c18090102070204020d021917070e0102030c071205151018 74
    0x4070000807150a002c1d8900c403000036511202d00d4014021100f400980c04000503008001c0000c0a50018107144514030034406202040b5000505010b141415503544070310851007500d05142107114620005003c036000c901003460100801d0039a1154070403140c5010b4814021442c0032800e8580300100c440425201190b4441c0c0f5500c032034191000c2c806580207046550092200703c6458403014259003561819441d6068003450420002c00c5003101c41e6041c0790140c40115890b100d40c18215450a9000d4000c41c80c6a5400302a0001d202d4800003028021f4242e40c824402d110218105900c40400001c102e510440e07007545058114115000b454010111800052908070740c0d43c04101a604904c171035441d040d07804a1459001c0f04030015150f008450b62514074508001d1401c107520282c4c003e8002c0c0c0800000320040780e00350740200300b11032482140e00b08807a04c80741d0f6045155010305100d031044541e1301403408445460b43d0040079007405044040688200c031418a102c4000b403e003211040c00300e454 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 810946366 1250 810945116 810945133
    0x130507121a0708131506060f110c03060604090302100504030504050a06030506030c042f0a09090c0903060213091e18150b06071401050f0606090604090203041103060901060501170601020d0e03 84
    0x82c04d482104000c020310348506d0002c183c400708c05462003d01854000b403a801c4284000015580401c080f5440001114001544205800c00301d00d04007d2070070822009252909000034190040041c204961080700c03044101034680f2003c800361034040d02c9890300341c6d00c80501a480ca1500d0381004e100c4003c4c01c200d582c0c02003000c48560f00c81d10303000e40803000217060020300c400c41c0070781c403500d1a0064401c0c01002d200d81c9800f40c1d401441aa51440054a035680c0414180a4111506001c0303000342000f50301440356440c4000c04a00b89180c0c00c0e414000e481c030707050420140601d0440324424203904280640d0000c1001a010406482c8100425070701510800c40a1f0010300c07500308560410480c98000103d61500d10111074800c50040c20844c45084103001030782440d0303144000c0340c058401800001d601e83e1034038544090001c0032000c21a9142c000d610400c1841c41055101c0000c07281c09030380302865020040028103044000f51401d0740140c000241343e41c02c540c0942a09450a140642143c0041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 810947616 1250 810946366 810946403
    0x30c0d15050402030c1804051501181a0409061b0e0604090b130c0f080124110304030c06021005060603060f040b030a060f15170d08130507121a070813 66
    0x8512409a40c1403600418082030010170800403272004d6460200000c154104000d40140e80c07800010a0111030301d0b81c030b800030000c4800c1c052108041010300180024181f0740b60400c0504496880c070900140c980c00c0b4030382080c0c40f85000c0320001101a00403031802c0e00b002c0c0c0c204044e108078011303150081160300c0083c3e94610075200300240700c40203582c1c01810501000c001400c090041e0b000e1641c01a04500710710306080701301141d4120545904005254038204000c45086006030b600280003905008000180b294010404c2011100380e0701c0c082280d60b0b919070400203980401c7e02e04a412040c5041c60810b5800c10750700007003003000b00034203c0b64411600e41d01c0900f030310100450b00c6c22503511952104003000314481040042d2800b1000750700880c1668190965400c0101c1039041082940c41c08510b08100c4100c0c0f41c05547d405c4016603021603201c05003c5401d036201c40c8120b80e140350f400c0d402d0541e510811201402440340b0341e20424103481d03950a101c5a001000700c10749112030500021182c6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 810948866 1250 810947616 810947629
    0xa0f020a1704051002011b0c14070e180303040c050103020d0b04150501030c110d0e0118030605010f08030c1b010e030303010f031e030c0210050403060c02010902030c0d15050402030c 80
    0x294001c1040c080c0d0321800c000c14040c1d9508510a6201903a040080b103103d02c95504092282030304607480d004110408a080031401840c8007c5405400d015000b001701304032144401c41e6200341c028400103130a02e903000c00352540d284001c82d009803659008900601080d88690000c1170750f003a5284c004540c2a401e84005400c442010380042d05001030808100b24650b014000d000c942034982c100340460685c1d61141c240c8500b0085c012100704221044880344a80c01481d420302c07102e07020720f21001c0312601c80c540900206801e0180c54000040c40400045c0e1210000071101c0003800100a00003c210350785002407440c0410b01e40301d040c00a511446841500c08201860080841c101e500d00d8240c40c50070500a407240d6004181a01c588400c001008250030005078881154180d03a032075a016104401110036000c1c60300010711440c200f1200c13800d015815040603543d40d0007203055840d000354135810005402e88540b0010329501c140e1028203071214059001130b074841d0010701654049012100001e10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 810950116 1250 810948866 810948893
    0x1050115020706050a09053109031d0103020412050d140f0d0e213c090103291807091403010608070803030403080c040303050d0b0a24081005060a0f020a 67
    0x90490024451040a0235484e91070011140d009034104046040e6440c0100358940d01455122400034520b1810764591107581110024100031390711200c1c290103032030305170f481d05200511900003c0038a80103061541020080700e42280c60349007114074142820103450040c010509107114140030302c218046d440415203010301c00f0420815070240e540c0b42003403041e02104000740941c030740d141410f00c61444000485403082418807422840c050700d8052120040f40503042400c0354210180ba008042c5a031040740707074032030b210024003200d442c007000b1034803003440d000c1c0c0d40c04489180024404c41030401003800c503244100703c440c1014001090300c50b04c0304038a0749040c04035400900aa4400000c0006159200030902d41000c1044081d03071400e884d5441c000c08600401c0050307600c03142d031a001e11146944005026000700000110010720080d09008c2411940d280c0040c40041050500019005200c2c40240c0c803d032200203000c0c60030585070b51030403550701661708110025403054070407645c045501340c1280e11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 810951366 1250 810950116 810950149
    0xd06060503030a050c070f0f0e10090f090b0a0902310504140601080102090f130e0d031d0a0b0f0714030c0d0c0e0306010b03060d080304080c01050115020706050a0905 73
    0x10350311601c0d482d0046c903200180d4402c0d200804010310070f01002c1c2c0c0312441c600407180e41d0803404043d525010084040082e05d64001d00e540380c94118241042151034010840d090b0207a00a9520341e03844003030100aa600a45000b54000d001410782c60b04d05d00c190510b1103003c0c0c120420721201000781148801101c60a079001e58818207160075222104004000305400360107100c1c025810080e0741004610a603142c1d4540b10f01c604010036480740c58201d2580702070458600081102d0200c0c4418102800400444442c100400101c44038124a2140000d0141d0f600b41e020944039aa0b680b1400c4c0312114400240042041156111144010300c0c030220155004000c1c051134079030788907101d1400c034084070f40e01141d5100340280507000000a503030200ba0319044036401595190341e036503110300084101c00320701e01c01059024080180404d00c043d0601800a45040c40001c0001e6602c03034941400c0e110a101c030800050b0b100340400c2c040140b0543c0030300320782901e43c20301030f481d1522040003d019400c0300c040c2d039 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 810952616 1250 810951366 810951377
    0x181b0306060b040312120f020a0903030206010611190809100f08010e0403020d0f030204091815110d02280c0501110a09030816061d010506100804020d06060503030a 72
    0x1402400480d10850303008165442402d480c041c40d41e07032040c0c400b5070b1669400c5c050003030844240e800b2504c90f400c000ca4180d45403008540d504150b40001e440d2040c40e00058005210f00c03000454103500030310390b0710145100c0c40001c2c00040a082100f0804640c0500e0480b041039003170110030300c1901c0d201c5d40050a40601c0e00c40300785000303881d1802061114140c0c860310416101506000120340c02140440e2032031954a0801c0c02084d071b2000640291089503c5442001d01e454105000e80c185034080d04505407043d9002003e02203141e4000d003d407414400550310b0000100b000c001000200e5008241d00e188140c007a20015000c200c040000c0e128001c060b4000c04c40e031a09001c00c108080c480d80340181070b511045400c00c0c9403680001c02480103404000e1000c0400500601044800d110407092258442401d00c0251401200201640e004d10500da0440d0309201c04202e0b5440c04040760400d1165039512032074156070b103070200001103440d8030090300c0030350351003502042a0310140300502514000b9201e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 810953866 1250 810952616 810952619
    0xa0204051e010b0a110c0d0210110f0313080102040302280f03080703020f010504170c030d020c0313060f02031c0e1209010909090c090c120e07030606060807080604181b 74
    0x30f00b60180008001040c1d8102c0c0006603a20387d64561404107494041d100d5141d0828010019a0200e10f460b400301032038403d0f00c5864201c090700100424442e030303c0840b107030801562103000381e00345d0280e400000d52141255092207400c19108086091229101c0c004561455450000030f111400e250010f648d50000000c125060540401207003100b8031440c4000c010034503041e26180c0001842d11144483c8040c00640404616010030599880d0883c0d0881103560740c00c0700704900d90304c0d4407142d00a4041400301000003204ca004009152011405802851600085501d040c8422030130700e180075034480c3d80d03d6030a0486c00080200e40d0318403880500380c035550703941c5000142c00c081007507018003a070a04000e41c010000721075500b05011501e00f40e501062031720482500740c50b007481c401c5c40324054074903109803200f682e500040c50404480c024281000910786506045403100000c03140400826005400f0a8050802d6406104440c0e0104c2008410000b40da441c007200c600300c20f15035100540c18410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 810955116 1250 810953866 810953887
    0xd0f061505060316050a0513140a1502030d090201201513030c020603060619170a060501051801090b0a0503091b01140901030b180420030a0204051e010b 67
    0x9500000e070500300c80301c0303041d454007030640d01c1c2040b00120418204070020820b400d000c6e0089081d61039014611103c1c040094076a08000044111142d4140c452040e180d4000f800071400e0708401e6104101d680a5464441c3d40030100000e030111780300403030402c5500752800c0390fc00c2020380d810351031a5070700d4003074010084c4400003c501d05a014100462003200c0c0c1c7d10f1080025000440c049040303606903038098a0742d650000181c0e150103408501c8a94420002c00310704c07000e50020003007407405a144038918441e02ca00421000b150503500036540440c10800200210901c0888000b80c08513051414401e10381c0c035440110500c1e0000010036001c61408400d11418140a0081c0441803409040e6244420072500c0020082d26509854010031080040c142885034803c1e001955410700143c1189004000742260b15074a00e81103506648001c15040503840c2e003000c1c1d0f6000a49400000c0003050352200d03940800c4020000507018982050540821041d41c64188001600030700301c00140c0c64441c3c80082 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 810956366 1250 810955116 810955151
    0xc08030c010608011a2421070c2a03051006050a090506030a08030903040f060c030e030f07090221010306091b061b02040b1206011d1308090d0f06 64
    0x403c40001e41e4100702c0c000c182c078100c0501d410034080d401c0781d072164039140c903001c2408000034011000e842564009550060100c000034583e100300110b10030b020322543e070f21004a13400b5400c80b10040020020541080304001c0e52050310b61120044120003840c0c55482d95810314001b0002030640005403500e07130403c1949422686030b0010f00e903408050056243c40c0000907150701204600800c9508c022011448005c82001640c2c080c1035442c1c101c0043c50303101c95025040c60190501140003800c000f890341100c0c2800b0612000184100009110040c103050040703002c0d40191802500c58075000c07030399124600e1b1442080d402940150300c001032420503030400c2c0d0f09505024910750100c0c070310518100641507112174215906d001115144404140324400034020f0710314641c109074010000070034820020008600700d812240240c2c4d1070191034100001004103607908031043d08400c030908100d1004161783c14014280900300600c04a43c1a000da03880550181c8109070964070590389804c019a183e0045 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 810957616 1250 810956366 810956369
    0x518010f0501080c01181a0712050d0e0102180609040e06040f0b010e1003020f0604092a020a111003140c130f080d1206121a01140607060c0203070c08030c0106 70
    0xc0c0380c00b030440781000c0840c03100b1b240e081c401c280007151040030400500001c40242c5590540c420002c500110035214010b14503084030000442607842d05a90311065007051089074107100c90b02001014455000701040250380028042d690031580f00c07042d281c2000d400388a01880b45114036a00300912103641020780102d0016005502e4528056041c8124031003a8100c40084a03411100d80c003c810800000ca16140160382c007034240b6504202c1701a02d40400302810f25210006900b08000030070445800300e903101100c0030701820303051f20b0220303569260070090300032503640d46241008540c0f6075103039044110750241240da54020034008100c0c40c0600c44001c01c54401001101c158107117440c01c0c4400d03540c888440c0c41003a07007444048200e1065161710364001c3c40041032440780d40c180c40040d40c10110800c012490392548145508000400c810000c8000d844280c1c2020344030781e0030403246903160401087c03021603840a41c0710170320000d00041d88402000c1c01915240014588030722085940034251501d6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 810958866 1250 810957616 810957619
    0x70c052e030b0420030411120a0f0501090804080f0c061801030e010615050307020609060106171e010602030d050630070510030e0105061807051b0102070c030203060a0e0706030518010f0501080c 85
    0x3064213410800c1030000d08014225002807000508ac4100d01d0701030f004150070b4500800d1103c01007400503429201180c2102a640d507001600c00b034881300c07810402c807817140c0b100010500e0b00300c512150740c3e940310341e0000001e040228000a5240d0300d4107a44280c0030300214240c0005640002003100840d03042c8212504882c0500040c1030a5040000180c9804598241c2102c2e108856000641204a01607070142444500b080b0100c20358584038000e45940c01a5110002e46040c907003c20807070b08100b404661a1803600d2000ca1410303246940c085640c1020580c1902d1038412a580401e80703654040c04001141d00d280c50005048000400850070f40d070008044500c10044507000e0f00e8402500101280e00090034a0300d00e80c5c0e03003103044405401c84c1c0003244842c000e41c03001c1000410884540c04d4481502c0c001c07412511203698140d01c00081e100305851904590700f01100c1000350501035004182c1200e00c105045151440c680316243c21144410501030b00c1e50b4440004011480b0280a80f8054040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 810960116 1250 810958866 810958879
    0x20918090303040c1212050d0b0a170d05030105060403111302030a1d0a0b0a020904060807080709050c1c050705040e0405010506121207110f06070c052e030b0420030411 74
    0x1800c1c0c41b21141c04040c0b010b800c0c14080d0001d401e5468040c2c940c0a100c0c1c900d4002c0c400000d494481600515903400e444007034680e4854611341004007406034055034121000202640d15003800c5680c0c204000004192503604420b29038802d03245100c050014502c960040d00300029450754030054560395140c41c041003252500540d01100100313a5901e0001d502101214015a4600320030000ca001400c85500881d042c5c080c0850114102401103001800c07030385111400d000301d40f0742c200810360510a00c00441d260410084109103080041d4100c3c603408005410030781c1c1480c0d038600207418280c00842c2c044503140d641e2800c0000514005441881412040c03004101c00311085a10048900c070705c0c1c40203468012840c1100303129a40e070000502c8003a1000d000e0a403210001d14286031b04940034000c0500c250f480c0d00712110001c04942c0d615454241140c60100229101c640a400400403880c000c1e822070745403000c2c41070429540c00d441001445e03440c5a541d4915203800d01c0e01c4048100340341c0ca0710981 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 810961366 1250 810960116 810960149
    0x5060c07020f150915090d0501020c16052101020d0504081902010209010e130914031806070b010e1506040f0303020c040605031c0e180106260a020918090303040c 71
    0x1c0c222019903407010800d45645a29400c81040c0360075078040e210281f03521568100c504810004190003070200b07061500d0895000389a0500d43c4c98010003280611504440c600c8040075284d89520055240c034003142000605d080044907400d0140c0e80112007e542a076400580105805030304450900c1d10805031001b1800e16074140002840021002845403041c40705000c0419207442c0c1c0c2d488180126801010310a521210043c0030751a60482101d211004020083d00c20b42ca0400030b040340e11465104e0126101c2c1e070f00f84090250360b25400b911100701400d100c0e09190503529407100904c058203c0c00083c1d01c8035451864001d2030500a11112400740b41091000c200c140c4000900c000742c100e121501e2040751102250850308290790b2101154050001c03444034881d004500c440c01e0607030300ea9540700c1c0b5201d0901e151140351000d072410800407064103400000c01504940c1d0142420706402881422018000304030110801016103510707449030000030a200412540d0700b0001c00a1048808800161 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 810962616 1250 810961366 810961399
    0x206070609051b1e13020a110a06050405070f0501080c0307020a05060406021b03091e062718250c060609050702011805030f070807020414150f210a05060c07020f 71
    0x121500301035410341d401080c7d03e60845d02443d40000d1091075030381103072044101d41c201040545070030f44040c0c1d450300941c60040f4140c01c0d099280805e8410603100d04660340c540c14611515030740001d08600c21401006016030010740140900c900071070090f40d0140c2c94886203060502c2c0d08042c2280c48580e5441000841141e44900d4243d009043d403104503d00c03102c5042010500c14461103a0040d0044054403624602c10b01c1484441c501801c141c64180c10f5403c3c1c0302c10380f0780d2035005481d21040d010902c80c04000150311204100c00c07007641840e0210080f901c40d9180c409988081e003202184c9a00c0f80100f00c020380c2c0c248107003600c84c1d140290b410340781c000ba9190b440c0c80e0711a83d010b940c64103c001900b6420300158108a8800a501030320401c9032480c0d44440a1188100b510702d2001415203040c0c0364050710305402d0070041c6503c014500000c2041d4610a010240e00c003c00e105641e010784010707413011a03402d12155100310541c001c01a5142c1e410b01c100b00e00700358041521442035019200041c1c10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 810963866 1250 810962616 810962629
    0xd06181103190f0602030a06050603040c0614070809130b0310051503150f09121c1508120d09140706022512030207030803150406090203060105070206070609051b1e 72
    0x402d07804c0b030350050b40ca84030351034003601610b00c030b4001d40d80204000007404100054214103004035891a41c4004200b440d149001c1d01324424504003805800042c0501820303403900c086d40e20341c1c0307003a070107800600d81c2e00c80c40210742000792860034225075a0ba80e10821850701000d801c41c01801000714044c000240040310a2000c00740050300c02d003a0314807080002450b004042050000c8071000e244001d8540e002054011644100244031110306424a004030303040c821040c0440f8181c4d101b8001815100c5d12070070040c0441c0c0c010340010f851080e10f9040c0d85011816040300c16050881c1400503041305400e140c0c003e481c00f00314905034510641281c071562508900035000406461001205403071400450a081345820610380001c0c19a0f4000001e0000300f00340e20f00d00d240240c4050f101400050381d10356001c001c81c00100d072098003052003000260018600100100606845400300055005554443ea85442c0c074408042d00c02c64202c05176101c1d98644081c07610a007206244031a001507000d000031442 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 810965116 1250 810963866 810963893
    0xa0b071a0a060b04030807030e0a03020a050d02030c0a030503121e040f080702090c0301150311092205092d12131d01060e0603070e0d0618110319 64
    0x961212000c0400c1c0d03191100c1e00000010103441410a40b034688030b090170129a8420f0000310081101648640308506006842800f16500200102400c901e80030502901e040c0710340080368180988010f280d825035440c1c904e000954002c07401907071210b100075040c0349140000307451800400e0441040c041c00341440d840389540b007684040003110321245450900d8440c001c7c09402580036086008002114801501441c12038041041e80b04400384c1030902a002c07205188854140103100304103c084606000c0c952041c0a000d00c003503400240c4080070701c041103032016654064950071507000c5941c40420480003c0042c0c231300703c20514840002104c00b40d40c038449104407002c01580401d848200e198002d40b00002003040500c00841038120ba412403504030001d000b110085071820724403031440d007880000e407813003158161075080c0000320003400c20030381c242680c90880d03004c1d44030140c0070815625224050b140e0303032103060381c94000e00f12001010709004a8081c2e45500352000c204403008030702d40c02d00b10034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 810966366 1250 810965116 810965153
    0x1505070813081308030a0f030b06040524040803040e060301060e0f16050d02070b0414060f071101021b0307032c040905070f06110f010b06040306020d06051e0a0b07 72
    0x6654500c602c0d42181883e506501158082c000840c02e116455007203880100fa201240d0380401c84085404100701407805140152600b01c2000241c8a440418060403004240c40f01d0a9507130829541c1c018441c038540c0182c000c50b01495a00342441510304003405070b1005420012005d00180c5405486240701c0c03100140242d07a440325100d0312040040c096022207203480300000303065603640c0c001e04094a405c4816602102e440184a8030240004804250680503980d20003d074007003900c8a5108441507104100d1164065500b0001c1d14184a810b040e42c0406000c00c4000d1500e13089541000741a00c2e120408402100c86400c50102c3c03000f01c180152644484211070014840307000c2d043c21454692582c0010700c10040da90400f0030856008a103c2008560785011141c00d040d013a1070a40c20303034405200c1507070041c0b828402400020000d402601c464000110f0024440f656000000c42441000c0b032011000310b02510340741d02c1d5041220031100a4240360700c0741450140c1e42c2d511140707035224038080310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 810967616 1250 810966366 810966383
    0x20f0c0307032f0a0b12090a02030316051203190c020111090409210302070b070e100c052a0a0803090312090d050d050d0501060e01080a0c0201020f04031505070813 72
    0x500c0c400080b10a20803c0c42c01c050440c001c440d07141e80d062a41584041725003450945900f00207103402c08001041c40030564003401440c10501035424201410303584945c01c030b80f58001c1e12030100c000c50f410405544140030b02c0314840369070b110179502d220132185902001000c42e41004d03280c414521000c000c4440124040e00c00003080e2801c3e08040f0304140500c00c040b04d0400304120005031f02d5030b040c2c020300162801003003001c001f511000710a0360144402c442c181d0b00410441d48880942c4d000f25800f10340c00d806042990000d216000501031820303c1e410301d800440030300345e6031100d00c3e08007001c1d03403000381c4011002986024034010009581c0c1c900d4191400940d14006241290f54440d86070441d8800d50110484030405000c08002d000c540010240c113403000d1800000283d202e01c260b05c81c1c0d0350410b0607103501d40d0b152507000b01c03076000d400803041540035903408000c4c084403032244400038001140518030000c1100d043e50b0403030b0255540035040d0003c01a134902402209090113001103499070388031090 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 810968866 1250 810967616 810967673
    0x308010311040902060f091c0c050108070c1b06080105041515020c0a060504090b09010302060702090402041508030c1e030f1c050f0a0b01050f0904020d09080406020f0c030703 77
    0x10040c1610190007500500c5c042614503a440139a0040c0c10703030410490f20b4020310414005560840501c0d10300107010b100c0100e41c1003102d940a542031580192103841c11681070100c907212801080c84140008580400010042018a40c0304044502500b012a420300400e035104000094821043c0a01c0507400f0047d141400040d008103c82401444086e041c850740e19034410000d072075504248604803406060200c030000b03e2904054440c1682e07401003181d0b0421066409100d48a00c0041007203800c00d40c0c9621361b54100807450351100060990300019603442d04040f10f59410501640020007200d0641d003201d283c030305400b2080d5200d031000300024a4031240607a6034000c036000c1101c0100e038202d1a08090100200401c4122445070704220000e01c601500c8000442e2144a043c00f80954030342c00340300b40b400700c0c5050f400401405041803400b0629074840c0d160f610041d1700c15400400580e00c164030701d00c15041d00b80710700340b280c4000724090a442d80c51a140c0d003814280c08c11007100789218000d403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 810970116 1250 810968866 810968869
    0xc0301241e05030628090201050304030309030309080f0904110903070e0705040e16020d020d09090f02131d010e1b03071206080c031501260f0a030504051503040308010311 75
    0x5200282001000c403102ea0525580e40f20b1528650fa5400e03070f00554219080c40c0760180d42c044c6c204e1203030b410b80d9018a0356941e510120700801460318100c0400d502c4903051030101d10614054946410500c03802a99000c0c0c6208101c1150303c00180503400b25018002c0032215a00818030301d0480d65100c00c84c9230a551b8981c3c08035914811504140705440043e42885112003100119102d81e2505400b100c00454107400c0981c0d4030313000715000c1000501003107002e1042e000541c11090141541c3c04001d804c0c83c1079159811301801d0940c21000c00c120034216031340c581d885c840400074010050b108841c0020306005141d45a00c9843c0d40802e08944400004030380c065208080c6da5111015030b840803c1741c1d9851710807194403003603c0f0784114403905c14060740d28000d0314a0661181212085032805803148016514405401d10360406c0c4c1405015001c4070201b107020a101910721035110b55181030b69941400c0410508450303008004000700400d004000c00642c0000c01141542d03080f40b14916803046540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 810971223 1107 810970116 810970169
    0xc0503160501030e1e0a0b0c04030b04020103021c09050c121501091d0d0504080d050a0e1e030a0311010f0e03070803090312090c030124 60
    0x3108008079802640501005080301050702d0041840355000000501c0c0a2a01c50319030300321a140d8010040b442c1c8900354084e9402008506150540c0c48103042c40000800003810705038001003150760050034030024409202c44040c1480071407050303d011600d074080004103a0150b803811500100410b404218030449884c009d1240710036a1030510000c0c0074040b1820300c600308804407441402800710a0140c80c0c400307446501c031240da0304d20b4240c00901d015500300b245410803100788010444581d222240c140c2c03100c030485120100240543e0a12080798414008940c0341c8940c800c080100341c0c1100311001016007550082184050009176403040d24213201480109400401245c000038588801031900960314400312800c0244009600c030080c01d003a01c41c1c1c031143c0e01251100c0d179540f41c24061440c003c144600d980800d002c40d42d0b00703e5100031182c042e01011200405c2949060385042 = true := by decide +kernel

theorem cover : BRFrame.Cov 810791366 810971223 := by
  have h0 := BRFrame.cov_init 810791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 810791366 ≤ n) (h2 : n < 810971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
