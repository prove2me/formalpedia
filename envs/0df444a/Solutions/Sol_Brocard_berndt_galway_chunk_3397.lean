-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3397
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:33:24.494689+00:00
-- url     : https://prove2.me/submissions/0e1eaa6f-00d2-477e-ae7a-c1e1d14b0b2a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 610791366 ≤ n < 610971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 610792616 1250 610791366 610791413
    0x902041d07020d0905060c1015090e0102030610082802090306010801060f0e0c0436050c0405130209060a02010212150904030e060c0703110a092304 65
    0x4220091242400505442144003201038492060aa0303a403500106050085030039a0010082407420360040c0c0000d00540e02903c115200c0794503407104032000001c99810000b001582801003c0d20f078414015180800710003103241d0b04120000650145d21580c415040100c240d001640200380b0b00c4407501c0941380c034140207d0313104006005c0d0002c0e410041c00240a440382000011300c03450305028000c1120302084840420f0307418007211007242a4000c280b08070341e0400300400203c0011182100b840602c1d48800d23202d03080080100e40d441100180b14144944d418a0f00703000382d40f0860b034200e03022034400b11014035900e0001d110780b41c00b03405a044120b5014001094240d034030b036011740050060102e00f4404504a544406181c0402d900c907406054100303001c0300c001400203001e9007041100031001001d840c205090946414a40269a041222816500d848203000340c240011000c0c064054014188048214a013010300000c250b07201002070600208041818884800020903c020080c082c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 610793866 1250 610792616 610792619
    0x3130b0903090f06030f150604031b0e09011b030b0409050109140d2307110d03030c0e030c1806040603080d0c020d03050f040605070207181b0c020a09090309090204 72
    0x8560712500180d030b16901984200d4080c0d081c500e8283c086901c10124600c89610070303114801224640600c1c4404580c00102c10800400425200c0c2c04403403210310103c0c1e0001c195800c01c0002c219058008e40040590380c10301140c2c606070000c6c0c4529001118040c64002410b014410000f400b5101c801000781c519407070710141006201e6001500a548640310044400b00f6060504c200c8a0803550100c5101c10420080490f90b0080b0f0b440003400d6540c080c07192400303c007180c0d800080000382414801c40c04223540c5c000d00c60103a50090030401d91031300c0c1100030b030090b1a10031000c00e81c00b0000241440041581030300190b80344e5030b2a0f0100c4007a5400c104907545441e0390381d41140082c506210840c0141c13041582001c443c900c40e0081c680b00f09040c4082c41c126840f10750301c407070240c4800b03000c9400798002c20001242c40e04c218011000c04c0c5414910100d86c02c1c500c503a07aa01451821003400080141c10448180584c076205107090440d00d901d900003514902d00e0404030703150391064002c04802800000d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 610795116 1250 610793866 610793881
    0x150a1a0304020a0503070308040e0a060e010e04050c040c020a060e010f050c1309021314040e01050c0a031b050403080f1603050a030c0c150e01270b01080105150603130b 74
    0x6035124520a40c1c40c200e02903296010107940e0042840002c0402c1e108003c1449400c080001da590081119540450025110004110701c0d030802d030015541702210204100c01c0c41420021040c0800e01914200164100014000c0d180e124201d0f01078081521041081e0140e031096210304502000340c41c4c10803160404110b40f1030640c1c419480c7c0c100d40d044010001c503c044241c4201d5121514034101d0015441c5010410b88142c1c802507055030340030340e03904808980740c40e081c01203d10a901d031605c4107603a45401240542260031f40700045000c00f108042007800e107900300e811141680d402c40b1206840303800924240840c0c1c0300307100c80b4041801048900104158114000d06407483c0161000c2c01401030f0a042110041e554440c064003488078180110030562007607016468111000d000824191140380c44035180101508018036000007244c12a428030000180c1d0a000d030211400920003400e0a003441c0000380d8141c40440d02c242c0000011403034949080c0b21081050740e010580051600c1c0102 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 610796366 1250 610795116 610795169
    0x11e082707060512150d020d1406150406080f060a020c0a0c0906240c12020106120c0603110705030403202110110708030a2927150a 58
    0x1c1000c0046580d07102043d2004000c000440040ca00a0f040d0101c4806d95003c01180001c882c00985117a240001d4402082c2c0c018045184989500711042545800410a001c1100c280754400a8280c0101c605840015008240207070070054009001d40c5030660300b140f150602e04005801040e9800b42c00c0700244800094100b4030450b410541d00c5080b08243c40303a07110b81d00b441c1940810018050484850004252f5149103c40f0b542610002504c940c40e90380030f00d00c10b800010203803801401d400c2c0c00c02150381d050080041210a1811081c1040c03000e54400c0c0d6a40294080100084c03203a1505641c40703210a031005c108403d0041c4500c0595900001d1080c2c03202c40c80d5140f105c83d0250707041c9520484520700409000401c0329140728070b4503445032920489908064141d401681d00c030500607104190b5512040c80e03400400d1b42064180b031202e401c01072241c42038818a40c8080300a9501ca03030100074250b00700c3c0c1c80b014070040c0d06061941c200014102003143c4d0001e1080381c10580d809086890081e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 610797616 1250 610796366 610796377
    0x180605030d1101150b1e0c16170d120e1c08040c051005120c0f0c061e010f090e25030b060a08071203020307051902011e0827070605 58
    0x800802024111040302001d0b079031360b0300441d440a50100700910f03017004415480030001c40710041c010304081c0b14628990404080000e040b07900d1840701e005000e4560450780c41020140310380024000c5444400c40a010950f8440703c3d11000d90707a420125507103c60500c5402810000702c1030310f030185076a2200c0503001900c00c1e00c007a0b07444501980c1c003041a08007001e140c0406c080382c1c1c40b41811302d00203403240210b40c5c1d4010950302030704400b4401c0954004031803000d0307c01104258050040c610b4808600080d94070103041c107030b00c4418103000422460350101340d014140c44281e4804905146810b1a1900d00f01e80020070048201004010030b8880d402c1100345419244540407000f00c0c0c1d00c03a4010002124000d00600305c0c0c907000b404040001190302c00480d0451446401624200340f4039456650030404800f841030304030004180c4031003c541c0e200c98444040c40c00c5000c0e5604e07141a01e480201008001032440e201c0701e00c50710041190035012030070341030041c00410031901901e803294001400385d0000d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 610798866 1250 610797616 610797647
    0x3306060c07050a1d090a02090c2d0418060b04030210020a140102090a090b03060115021c030b010305130f0201050a0e13091209030f021903060c0807090504090507180605030d 76
    0x4e110124011071030100d038088040da00140300c1c107199240c0d000c129a595102e0030206041504518250088006c0000d2507450500500440360312a4502601c17100c60511405140c4100c0b45000403e010040f01441a41c040c0d940581d44242150300032603080c0d01c1c0031552032018105e520364100c500e40d100760540040c011003c040d107541d48007942d01c03c0e00b0700c1070783c08070600d85074942c1000e00148a240c00140301d060408003a44101c40da21788120014601c5420140341207000280c442202c00415601030040c03907000a200b074204d01c00e8840f1625804402480100021b041200010324510f0072840b4000240410200034051543c101581d000c0000402c40d03103038121801d1545401640c60309000d25800c000f120b82243c0c0880c645803840c0d08200d414020b440c1003101c402c42a80020010885601c40c40300034032840d1301c48607074505244001919001c51035020310322484c1840002d5000580204210041390345c0d1200c400051140c4a6402e00602065000560103100310f0020701079495100d010100115407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 610800116 1250 610798866 610798919
    0x80a0b03031b071a1b0705090406090203060c03040201020a12020c1003060f14150901050d020c060915101205030d0207151817031302030706023306060c07050a 70
    0x159806420404c0310402c42069180342c0500a41400c40b102c092554150b0308520180c4075015190800180034801c2620150391040c0e86070110800c40c03c00f000722139008031009a0740c1d4198a002d0380000c0daa6140741c0340082440c1035040c0c076049000d00030401c140e80240000c04c910020f20900000400600300c40c030039100140204a40058170742040c020513248a50007410202c0d003140f00111a0341558041e0581d1070401c1020000109150600d1010f0300d4110703d180060034690410743d4505260030074072059440440e81c1d050a201400600424001c2110351030507440c404e0710700714181a4118000c00102e0000280001900d41c1080502d2070f9070781c0b0b00d40c00660100001d00300e502114200440318400100741c0315500710300c07401d00207004029590107901001e80200e840500e50104e42800c580e640302340003591001080140120006089840100600031141d902020720b910050b00100060300041c010706002407000c04991051040c0e0000e4480941000c602c07583d50410b4030030300d01c4001500e245d504d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 610801366 1250 610800116 610800119
    0xd170a03140a0f0f060f0605130504090c03050606090705160503070c03110a060f3c051905030f0708040201020a0503030c0306011205280f091406070206010f06080a0b03031b07 77
    0x104c910422003030f915030070084030440e4141a001d4602e0b500070b4000d5008100c891a0019041c0e0f190701490310070340d2068240d0140c40d403441ca0514036041c0d028002e60300c9180741b00100403550340d10005503036000c040181c060900b00310301e0801ca411031058082c084c20850140340c010050060318403858500600235210300d4038865684070111440e03564002c0c0407000410300c540c903002d14528080c4140c00e42d6010307850b500041c25032484442c048000c3c00e07d03c10118801050601c6403112480a124440c0c2080c20302528504e49419a49549a0020500418009000b0100f419640300b0000362480c01c0d405401c580e900c1c10304d241c820807107803c11140ca50000d4060740c140043c4942d60700400f03005500c946044c1910640c004c508540d07680c040380f1070701f83c4a541c3d01d084148050f41c034040c2201c041d000b10092030382a5900358101741070070302c0100307010309651049004008050400610100b242c3e41351030300308110b4032030718002d8026041102080b23516210108403040341300452442442c60b41d29950498051302d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 610802616 1250 610801366 610801391
    0x70302120403031d041b020114070509030a02150f070c0e0109060819060f02040f0509221212051510030501140d06060503030304030810050d170a03140a0f 68
    0x14420341c04001c00180740351005154035160b204c400a4101802040441e034140c14080d0f00c150014150260300050391601080d400792030300040f6094005815180a0b4548030703404c408266540e08010000340540c1c1c0d0443d0080c15482584159501e2520451102e540c0d44140e0034070000d03151050180c0e0a102c8403810001030310b40d074248112821a511a80a001168908610398602c0058241e080d00e075280c4410500404502510040c4040e018070501e07031804a04000a01c4504032000301646003a203d100d030130307a100b10781015590f1095a03008007a016094100c00c1d0403541c262a98540d030070610700300828410809084140404c500c801030f507020b118000c1d9904110203a031002e11986c00c2d506840f2101c101c1c203042c00301d113603844a0702500010030303510303551000b02c0c1c40d56000321010b400241010017846031500340c5c03c160301d00810040312000110308007525403449810104401c0652400b0001d6031801c0c0d24002d030400c3d03501c7e02c44000580d100e80351000c0d5240107020011700c6a0002498401e003400d42 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 610803866 1250 610802616 610802653
    0x206040504051006030e3c0d11011107020607020d060609050c090112050610120e15090708030415080603010b1002031b070b0d05040804081c0f1d06030c0405030a050102070302 77
    0x3080c00c1f0316040920320503d40300030024100038029101488000740108540c00c10208036074034006005a8030300c480c030101c3c1c075040703401c5030800c01f00f02c01d0a07142040800096030b18142501e40403a01102c11044640c03561400c4001080264003040115082c0400c020305c0031034100c0508a40d41c02030326150f14100c1100951011158112055039118540e0385503850b00c01c3c410700c0240b0380d12460781000110b810314894120725204010141c803601e015041700b04144440188180340003455140000d60405050840c2c80c60706200500d800d1003044808030008100e5a003d4000c038030087d002401581e008100c01c0e0000391294002605041d400564400070368074540700254040c12104115041800c2080e100c5400024100140055030004018440411040c00504c01c41b02d440c13041c00200d1b40d8182c4206809422a040c0902542c18031211078040c0340d189a22012035400640200c843c2652651404000c91841c015a00311345d4140c840c201c2d01a041240550080071854001d40841d040c0420481d520b689 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 610805116 1250 610803866 610803883
    0x6010c0f060c0c020a0f0303020705060a0f0503130210080f010f0e0408071b080309040c051602040c02010f0c05040906050d02031902010e100f0e041b08040206040504051006030e 78
    0x95041081900c8021640c41e0340241180e000c0c602e0025911922500055078401241e0045c0903514851201041015010403c4500404003511080d04240c1da450004d0b000c6207910501b401488400000658440e0000c0c180000c0c15500508945510641e80002011740000701c4064110b10941c00003c10201003405295049071107040405966983c2d96842c60b00607002054200d03080c80c2007500303043c80f480042542002514140004549030661082000240c071480c402070010f20004000b21101101092411105180c054a0200720846401400c074014039581c401d80080d54036001704c0d00c0f40540d110004100303c80740100107102ca0342d1908204940c0a40e0100000e41c158001c408980c01c1203001410244501c1c01410000001c1460030007203207000b11040c0d004000980c4d288203140d07030b054202e429074140042c1542d0820940052142c2155030300594072983c024800e0343e1000408640d40c41e01200e000d070602510500050414000d01c600c1030589008641c0482d00b03101d06a000210000744040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 610806366 1250 610805116 610805123
    0x51f062d051321080f07050f0d35060a172b0e090a020d0501060507021c12050715020d060305070b031003061a180105011b050a11010c05070605030f06010c 68
    0x1400240c0f590f4486805610188000c6001c80051040301e01251050108100c000e69103000b61a402c8103444004103018080d542e04600c0c03080380c24803205034001d09540301e68515403a441c1110640c503040b0005403032282d11707880902400c0c81141d0445000c1000718100303010f200b00c0c0600b240d000c100e1b81203400c03801c0d83c11103034140043d00342c9440e0f030024909100015002a80d41000616042c0c490607284181c5100340c21030700228800007030010450910902e844130628500d40c440f140c40d240795541520310501c10f03210000700400850110107210f9404481c007190005004115558031102001030007402d440c0c8400c0d5000c2c0509100007451401a00444c2d00ca810030755084082581996186002096540c030185255070b00e000c0f4107000b984400c4914400c040c5045180046503250600040c0b0b100c0090403075210394444902c1900004178009190307800300d5030140e50702e100c6546190048850445a140160036840343c040d0000344c59400000440c0110640d0001c14207d5582d8030054601c1ca01401b00213 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 610807616 1250 610806366 610806419
    0x30c0d03320f1f03030c0c0801020a02120f090a031a071805010c080c06040b04020405010b070f08070302010e070e0417030717060f12070504051f062d0513 68
    0xe0807080c0d460780c1075901888150302d8000c0c503c3d0f0250700c064501c00b203400450204840884150078451019030501c01030040c075000b58a025040d2000a44030f001d00340c0007080110000c0381c440a00000c0d5010345081400c00341501e5102ca5580c01c1c94003100710307626090120b5054402c0851442d5200e0728001407207144415008042a24005c011550301c4031803d016a41c0000a0009e204102021701990340224011007215090b07007000d004210443e101a440641070500402002d00052200d80700001e00f84d801081d103a44036052800d081e4090a98400741c1d0f021400b4680010031600071954055014030300582000c415003200e001100c200c1d10042d078444000c922030548003403608814004075503000d030006e8005410240c0400214141000c3d0424480258100b03803001d21007800d180c4940c84e486105c0d03100302d1300c01281105800c0c02c0d00c410340c0101802c10111060150020140f0000f1982c5440780010101d80b0301402040148150460398038824080f101400014030380d418400e21030589484003a02 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 610808866 1250 610807616 610807621
    0x72d030311010912030c18081f1103011e1a270a0f060e0301052205032217060105010807030b010e0a060309031701030804090905030c0d0332 62
    0x5940c0c660180040681c0d540d2507400420008605150260400c1115100814800400ea901408000000c80c440d202024000c4040000250014000b098042c1d907000c140e950703401400d41803000e0292217050307090881002000040c1100034018040d1740c0c2500034004620701e03860f1130400c00100301210356040340c190305020490000c04403815007002180e41416000341401484c01180c10091641c9c880030641401d0321007000101e0b00448208000b0b002100200070038a8040030090403110340080080211941c0b640c600100070003042100d081c0d08041e5129481c8007a40e8418004a00c02400b03440701c40540c0c40104515004001a500d05032081615251110307604c0f66011001003000341d12981c1000b4465034101e08944900c000b0703001410941d42c0108030a206130602902486d100e210b00c0c4a012880030040012030b03050710580b000d40381505000701c2c68450904145265000b0b260000616024081000540320b0701680a200c040000d0003a85818607500003580b191000404001e122400c4400d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 610810116 1250 610808866 610808873
    0x703080a0218040222080309130615030c0c0c0b040510050712260a0518030f0703050f07081201030506091501030b0403090b0304080c011116020d08040504020c072d03 73
    0x252071a0003c500d54000c0007002c117100341c1403490b0305074080111a0000113030b2694a041c0039902039000300340804140441c2c0d00d410300c91115101d1010481e4101540e0342c061503009881401603840b00d64000c001242141c3d02e07540e07a00c01e030b64400d10510b0320600e45165003094441c0602c00f5580415003100c000144080034400944040c0c1241ca07031030880e028128403072803001d1140c100082c01403005410014042c90001c05200d100d40a040c404403d541c400d001d80f001d090920b4003210040365140c984140c64000500302500b2500030307010001e00c44a00410460003440349000824103d0f4050700441ea21034541c1c1248a4903076005000001c101042c000040c00031441891800e40c10910034601220315990329180c1907000d42099404581c4c02800084070b01d813080090290300422140f151045280c44481d03801d03080303480c3c0c980c0d40090041e02c5102500d0240052041500c1c003c1c070000d80199034030301c81e58489a845200c140162000441c10302468100480f0b111034588520301c4203040c94900c03501703546 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 610811366 1250 610810116 610810121
    0x1a03190b010203030403141605011b020c0307150201180f06150f0308070f050a030c0b07020313060e030f071d0c03010323011b0c020108070815010f0507020a06050703080a021804 78
    0x20702458509204004196291807203941d0007031a24004c1d07000294031004080400d010840101401045511640c1e80dc46160380c04203203101215100c3d07001a60080a40e2820f07805020703400e4005a4a40c190300301d403004d0003075000031800c465104003410400010025004100d0301c00700d028807030350b0b030a1b040c40074400654040c00401030980a0641950541e100e03a403102d2030000c03403541c1100018007040e607640410403142d40d040d410034581d0000e1420709081315029011403c42c0e03c40c2c901001000011a80c00c0e403024410802d0410740c49064071000c949400300c1c4400080846c0100070707020704c1c550014a010002d40b0590b4141d0354000200a5080d0b090758103107000c0b81800400030001d5581e800c0e0455803070803c7d01c40303003002d261700d07183d000702ea291a000150048000411600034016400f0410043c509a0f08112426a00c00d00348543c280384140c070200c8640c02850b0b8000e400880c030800c041f82c4183c101028018840c4a0b07642d0c20401c2d95643c480d1826405001000c0c00d0070400480d00c00c07424503064 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 610812616 1250 610811366 610811387
    0x206010b0a09080303270706050304111207091a03061b0901120f0b0a0b120a050709050d0812250309030e030307060c1e09050d0303061a03190b010203030403 69
    0x1482c115a205440702030703035802c5600944131040100c0c0c01e004a80800d405000f95072405000900c00360007100d15007040541288401480280180310b40c2e041d80015540c1d030300100c480000d05070b04a40700d0984508500c00209404103141c442d003015450b01000c1c1e0314000a00d240300e10140f00f1407800741e91800406c0c4207550043d104a5041c07003021415039100b000c2d00c2c45580b014520034500802e0302160030091000c00d8031160010358001e2020080102040018501c55410000303513000081d59075942c001c22110240c01e03410455102001c1400a801e00c0450360140800801e60801da400544541e52580024810b11300603038901003c810050710390500a51080d000f49010303040c61240f0403101030000741550302c8200220340303503551858860b00265220036541c1150001e0000c5001105815070007070010641d900c281481101d0114008003018403941144000b080030321071541890b00a0020542c090704121600100f0080c2103045000d5400c550143c41c0c41104181c01451039501e490701c0455039940344 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 610813866 1250 610812616 610812637
    0x3020d0209280209010e0d23010e1614010504080a03080c04030f030309060c140414040906020c0a11030d05040603180b01090b12060601020705094308070206010b 71
    0x2c5000d00340100140000756141e060210000694903200c1c41c00251180200300b01c1075000d4400e601c601400217030441124005441c0c04d032144401c2c02d00841545024155000000106008044030288861402c4058506036002c50740b02444840382e04004554900686c850400307668001c9043c040442e00030703511541c100381108030b03081c0b4058072500d4032110380c0507203001200042d41e039500e9841480040d20801c00907015928180d0224656201c14076100d01603800344566841405403181d60907a180d134070540c03541d580311078255103401c01c1050540d21409800301c00c1c0c0c3d01712a1145845035918000c40d01c2c0d20a0107464070384074103282c108076044004140d8490748050aa40c0d07101d040d0042180480100e000740110341e400f06200304542d007842a07502102054003501c3d4001004d00c030340b503138010801505503402500d10350b4080d030780d076804081c0042041800950500400c10192045d10840c1021000000101028940c0d09541300045883e0a000c9a014006812a030014440b150300000100f424250 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 610815116 1250 610813866 610813891
    0x150901050a0309020913030e03060106120c090306050901020901080109092d0203060c0d200409051b03010e060909030c06011701140a050901061e0308132408060a03020d0209 76
    0x34203034080b0355404d405450a00c941b05003191280c0070198014881012a18150b02078445545800c1d000303090104e801e00001052030322054030f061117070303c50880b400c011500b040050146c0c0c104204818003c0d40103054541c00142c0e08000412040c20714020328120560000314884100b40076026045003500b900c07100100c1402404c0b43c440903035010040c00d4001c00b800c82e07069580e60111140c4070112041341031404e1900706511000751050035060240d4003110310f24070000c0b880c0e6940c0508a9580c10803500621490340000c80082110403070418500d01ca140c041d11405c81035180d1803501c56590051a1194460b42d0140e00140040f0b541c800c4440c01c080c00d06030002c100541c0042c0f041c3c50b0311500b22074072803d00d0340d280100400d4440074002d060003031510601e641d07125582038044800c141411300010704010702c0001c0050b002c4058180200c003c0c94004122490800d01c0314829103035210140743d100005070f5507008a203541c40d1881620040741c0e401403400e800003021703034240304800d0350040c1514a00c44 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 610816366 1250 610815116 610815131
    0x150102061b160f201e0904060f020f040e01050a0f2418031a1305190305040b1204151a01120608010e06070f050f0304020d0c030602041e05150901050a03 67
    0x11140303902c04612051030508105107070b041c4428010180300d513000d0624143d17a104120009034480303480d10798002d50846030109240007401103000107441100d59560907108005800a0012036200301c060682c0d00446040340c2440e41e802c1280c0050100d401358486075803001e4142d06840c407003188050705401e150b0070045038051030b00f1301040110f4540d6006807003075417880d00c2c142d00030002c00840e140d000d1740c4c811211001404540b243c07980c1b01c4441c0020131801d0280c2840c031090500480039900245001c141c03803550742c5403442070f0b942d0307041e4107403411a100d6203c20341c40d4000a0450040c40308198100b00c0c079040d0b114820004450018070244a096803d035110340200d80d8580a004030040c27100700100800c0c0b5401c0c4401c0c000e1080104000100c100401440b81c43d10103620b039811281c100b0b8040300c1032041c44815044c1000c141505500040c541480040c0015041d900f4902e040346072072611070980340c2295140144000c08144c0583c0d1501600c1c108490301c0d50703600450203013982c0d00e502d140009145 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 610817616 1250 610816366 610816373
    0x504030e0f0a050402161119030201110309060a030f05060f0f010c020406030f050604120912020d051f0501080f0708071e091e0b010c03080106050f0f03150102061b160f 74
    0x280e0002c40420600b5400c10386103424400c4100c031240c1014015988e0601e80c200780d80c030440350560342c0d00000f41001021643c0d9070b0242c07001c009891250380c00500311703079460011040240041101e0071070030802c60704090000b0b6052074104007001d650a07010301160010480d48004494000007950b04030383c450740d00c400100114000f207990f558010700c510b00402c05414541007040c0031803038000b0124200128a60184445862204131444c12641a19440303401c000929015003008200c05d0505604030300054805040c1c90300d504418100c0d02c816040d29107500381c00c500c4a8881000d8010182542d000060070403002d02e800300303880e500d003542d4071404c1240c0d03484040040c02c2c1d40480302002c01c61142503254034440d030791900c1050100e4a09083c0010000c40640d006440920140f0032207042c0500071901c141e1207010b0340101e80ca141114201c0c0c2e90b030380c681554407100c004441045240107100c0d035000036a141d5040032400e000c46000700c02043c1407640c1e402c401e010713500440c0d60407101351000f8903290000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 610818866 1250 610817616 610817621
    0x608010e030322050c0409060905060a06180c21020906070b01090f060302030c010c061b05220b0714280506070e0d110f0d0c0303020d030504030e0f0a0504 68
    0x358800145503281420b144000401c80a0030b2032182e824101c04041c0300080d40060010304100d002d41e000f2408001c6800e10f480148110100a042c2d4041c0904101400003298480004c3d140d01400661141800f81f44110403501c20001400c041030805102060aa070170084100c006080c0240240c0780141c440c010130582d421105048501c1d040680c01403100c4a15401400798034184028200120792950300002d0740c0d240110411418070030702200c071805104040e0003650039a401200152080c00310014010b245511120b0111031540525080c01c001c4181003100004441350304408506100113510350340d400c035402035000030492280b40280000325103561803580501001e401c40301c802c070105003800350403c2002040401009601a251985556403c054171085504000815804521040401c0c2251031404045074030005a4401d50308200702a0300210503a4030941c25506140e05521064064a006990003030114075060b504090a00307042c00d1140b40280b0081c84a11030a9588002c03404 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 610820116 1250 610818866 610818881
    0x140705010603081b0a03051909090509030d0f1a060d2405130b01270e01090905070e040203100218040603080901030b03031e16241a090406050604060801 67
    0x4940f43c0225501d0361103402e070040f40a8980d02d21001c1c00c0310340300d650b800504600c81c40003501862608090650034145c07066502d10042c2465800403c42420007070400e65503500021078562200f8142501e2004066590152054008050140194240480c0104130340f83c2c02510317214a810395101c10291100800a64625080c9070340b009000c801810300c0d050107252640e08485081e21414000078a6690341d0010440454414081d000e80e6450141400c0401c903101d103a00140c2c41d54070301d00000c50210403d501451071a885007049802103581d0f03d11b5558140c80c101c40c040d501d81c2001411000305c00c00c940084c00104e10342608031451908600c00a0201c41c0706403c1502d410724080f4905405580501c42d80790b046804030002c50600c0910b00c0800290340081c44801c06050b170100711543ca03484100c103481803842d84142c4560740030721301e00071361b20707589041407580c41c103072420000343e42813006001e0703100001d07501c0152000f0603035036172501c42a02603d405040315402680d10540051a40c100f84150807 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 610821366 1250 610820116 610820123
    0x3130605160f0201151517160905030a0b0103240c0c022d0f12030d05090601090203010b120402300c04020412170f04170618070501140705010603 64
    0x480c1c1c010444000300707114480c82181c4150f80c9006240c0c0040c5100c000c2d16800c461040e1482600d2038505030040361820182c1c84440340c5144070f6018018480c404900344492600e1070707a0780c281c1e410b07692001c01d56035944580018152a600c070006001243d0268440c0940420202c5004c541c6541c0e441c0c100200d0b1442c014500000304050411800c40ca042c02d99405510705612140b10200c03c8401c1055804528000b2070388030715491030303000030750b51a040f42c42c40004c0c0314202a00d48501018240c030000e00340891f40c2021600a010002c10a103000d0300c26681070314002d050141c18000703000c03078012400e040603105aa0013095066040c0c204084031142d030340b144c00c003036420103003036504640b91914142d81628074910443c010f00c0140806e0901d08000d1206a8101001c4580764500d5191501795125281070054030110000b4081049400d205803a0782011000c0d0031030740566607904881000051250304401e06402c426000c008941c400c0003c422040303034154003189007a816603100e60842e4181c0e031045 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 610822616 1250 610821366 610821391
    0xc07080a05070b0c04060e09041a0c0310080a0803040f06060509070513080705061c021207050c0d08011404020901050d053628020d050f1b0a050603130605 68
    0x402c200302c41d4050880d0014030030b0303e01c40d0815050640260880600d1107001e4003a9416400040501c4130007100c00c4c00d0300c0319103003500600b03040c6440304d41d03c180c1c0216110007480282c05070004510600240314240240c01003081410760302d403039440b10129420250b059940700d403200030201d880d5a40d41c107040d003c3e14181c1c4030306585000b10310403252510b900381d0020308550407589080161b5102c2c002202c10602d802281d4000e001d042c03145e800000d004485014815184000810001942040c000c01c2101e40810441e0800041c0007400c48035131500340a8501105203070b42c8103e006080c03980141c96000c80c1410b049080800302d00301e03481112000ca0311280c0140c40f141c00c3d59540c0d505004848102d9941c81030b0028003549400055907180711440390000602031950882c001c00e006003050f42c00b2154001e082010b401a6030500a9030791450f03c01c0f02e40b050148441c40e4210151003489040c100d031000c3d141499017440c010411000340c00060403c7c968101e1918424005002c601c21203100e5694200c66 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 610823866 1250 610822616 610822627
    0xa0221090601060908070f090228050403142e0207020d0b061f05070803060414040c09051003051906060e0a1a0103050c090d080f0d0203060f0a05090f0c07080a05 71
    0x44c82000c80354000c0401340c000700810302040b401c0c94044019141040c4c40503948052a400d942d42d0104403502c486400518601d140c00f089620000400c01c40b40203d4078241481456841282c5440411100351001518129610b8480c0c404160004000e010104014284031142d00424075016030300c2c00c100c030018240b0302000864a004021060209880861110505100c07040908603204030003028017400c2c404000a45c0d0350b41c4940000000d044111000c2445040600d0083e0747c421440c01401c07007003810f00001442d0220008881e000700d940100051041c941e811888948480742c43c0408d4039096201c42010174801405d01c0d4090094400c0344000800020400400342c820326030495a50425040c01c007032115004000080d6072012008450446184004d4600244541f05607007034544824000f16110515465070f1703010b980718550680c0c260505800000c01c02c42030425078083c203603104034050040340031840c8940312990310585820056180003800d40703401c80310340c0008a003000000c000155 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 610825116 1250 610823866 610823879
    0xf070f0b090d08090f0a0b0309010c110a030c05120310080606010509010804140a1b090b09041a0a090c030b090c0409050601060f021c03050106140406080a0221090601 73
    0x124010116910668103204a60300000c80860307000380b016107010b00c0440d0b01041c6544190503140f9610000b004064203581d1003012047e940c108558a00d681e518019240c2c8616004880788400054a2000340201ca0300350380d01512400702019082d01d4074401c1030b29100a6205560045000c0c010487e00d42d41d0700351500b04001d1800c1d4005003482d04010040c8100c4880e660400402e0381c0007907021454040c4181e442018070701d8400408405411718001ea02c030805070010540080e4150b4000e118248072104482003400801c0f00141d80061641c0030340307080520707410726050116400202941c00401c803800d983e00c40320514007550f0400d5403080d84880610031100000c00201907100010348040c0f008804a40790542c40318014428102813000301614014007520070f0002d0803500c1e00c0580301c01e0303910b100d04c00d004004080c240175600218040307207403048000c2c40c0d00007507a0490305d042da200b0300e031580e0f203400d100b010350080d505030002045103002426400d0307000b260710f82c45100340000030701c1507614002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 610826366 1250 610825116 610825139
    0x20a0c06020304180f090215041415070308040c03050709050109050601110d0e01030914030d0b010c200a0503060f090d0c200a030b0a06060314060306270f07 69
    0x3401901998010042040610410190141c085460740c600080c8072110301c80700006094500320080d48802088950081c00a516004d4015149000c64140074090004284803800c54405041e400c0c1071801e00235103000034030541e4401e610921541c0d002c06856942d42c0c402d0300d041160740020f2009901c481c0180191801d0f03200702780c5d1001007441c04d4003160101c9000d0548034501c20b400ba03802c111802c41ca18400364047d400034148954049c441d170103e11455030009840c0d42101c190301305081d0811035205007541c4111206420950005524820f130080c403610203802542c0c4c1c021260300141e512100103000e0380c0034010180b190613910303200a42c80c13508001117070a01409000c0c2c00c051110507a18200810242840341c602103031348600108041c8110000245a00219817009003a0303032568003001341002654000344101c441d141c80502c00030000403011882c0300d20440309a81c15500420000d000c00503135481c5901483c1402c800144440c0841c8810342c10001070f4482210140d101d0103003080040c1c42d25 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 610827616 1250 610826366 610826369
    0x41203050f040f0b040c050d03050c010c0311030f1b0c010c08010f0f0608060a0801090f0501050a0b0d030c170307030606020f0303040b2a0712031a06030a0c0c050a03020a0c 76
    0x12900031442d20b480d80d6282d28a508505000c3c2010210f031001030100007060070400c0241200612036502021140760090455010840321140b55003030181201130341d80207000d040b0000050312059407c607941c3c1002000080340c02010821070307000004003002003610f00300c020148018004004511a1240b0b407003d400c0c200306074403070107580840120030080500c5190403013064590324940400310b52203000c0011304c4403003190061003003940313404108402c110344400c100e52102d210340b000307024035915100799008603155802d0003504400c1c541003e0740040d2040c2078140400380303d2400c1000740d80c0e031070040340c2036030b0821107400b030100e0740e905801e201060301000f051045ca079440c03004525601e80391f0b550008601001c0c2160a90305c105204d1041d0083d80481d042c1c1c403d00b03034600c10310388400e072904240da8840000344100c80400e1030320003a107240e00c4c41400520143e80740030342142e203141c881c41a844006c10022600d0b401b0010034800b0103000440600021841500943c000e0140c4c40181c1024484501c55 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 610828866 1250 610827616 610827631
    0x406030b040c0809030a1d1002010e07060305040201020c27010f0612020c07090b0111030f04050109080c0a0303050d02090924180403050325020604060b06070b0a0b03031204120305 79
    0x203e04025000718008101c1d02900c405140540c0001c4000c00c210704902142080c0a07031114500030261146a8150f0210882154400c21601c0107682c07603100751b0468005541c040c0c0140c0041344d80034004d041c2411003114206408500e1034940d000314840700c02d81c03d42a0000c1c1c03040c24504e401007000c0c0d41e0100e440544c1d01e0140004620700320508110310f07a56003061103545a0540c030f44140140c142e0041c841c00c00d0144d808000e0340d41e15110700703d100d00c06500c41c2c007895010607a2a00b0100c0c00002c0021030303020b013800180118051500710740302a2a20f400104c2000212a0200710440c16074a03407d42c1030b40954100c191803107241c0030303100c801e07200c0314086100c840c010040c0102c40301c000c03403d48400c241c0042e01814069503d4880804079105180ea00c140450f440b004164200d06007035000a46500c114003c820421070b070041c803000c00000c1c1c41040e10150240c0200702c003049032103407554404046454000c1c102d0346803182100742104001402c4030305039040300d5559003035640f003501400b5056100ba00d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 610830116 1250 610828866 610828877
    0x15180e070309030f260a2705070e270c1801080709050408030705030601030b040921020d0207230a1d0f01180b130e03040f0816170309060406030b040c 66
    0x300c04003141d5904090140700c00c602c0c12803002103411586c5582c040441d8611010480381400c01110302220030f4407190b00200d51a02c201c1c200001c584001c0340c8a90300458040000d002c046402e03c0c80c1000384401c0d00140c410714000d07031592070116500d04001d10400d03011031001b200f096242084440c2003600f203521103110b07242804d0170800012a00350840f80d1121032410616180c4c0c43d00e0004070014210030106540191034985a04203104050b04621000080181e0500c051300415800300c0e01d41c0c4603038182e00007580c041c680070b10102075100e820201c0342c2c284035450a40c2ca84e01e0740001e0700c0b140c0745a014820700003154000081c2440901112544512410a6650154500070452440f54602409803146aa40f000c142c0320954441024851000c510f40b002d10440d81300c2c0305000d4490780302d4862004040d6030000005984200812280403102c4c0d6000c1c00390015207080d8a60f1010310800c3c0c540b5082d40800c0203807000903650100904050840355600042074106c07401444202e54405003100305014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 610831366 1250 610830116 610830137
    0x303060b0d1d060408070813031a180a0201020706030e0a02270c040b040b28021c090e06150c0106080c04060506070b06010e030f01060306150e0115180e070309030f 72
    0x60303d4008688072140c0c001f8080383c0d12490141c2c1d0001c0a60640c00c010000c00089440314809407040540c24081c150161b00c03005440191260545c0c0c903c00400000d0240e00280070800120f8060345c09012002c8135002030b550304a040394009840c41ca01240d200b221900e0700c031440e44201c0e00d16a15260302608800304685458102406622030340a50f100b0352509001c001144154101c618000c07a140000725040c81d00c006039038110181d140e10b804031951400c030754a9182110898031441600003100d5034071032401d40c01d4a8050512508101c5900084299401042960b0006009100c0c04008110307201c080c4c000007003a641000240c41c050703030100f032054209001c505c0c0030440107003441f50443c0090070000c070300c00c5000000c00d05001c408000341155501e40740000080c46070360707000202c00b1038800a00354003141e1500c040300c0c06600c1c00c0c002c0d00c01400c0c12250003203010b8090b12603410f103d0415003002800541d908846c079403113280ac8a136680080e03180d103c0300d81010342248510242010b2800d14030b0034003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 610832616 1250 610831366 610831373
    0xb070503190f061203120b06040b040909020114131d1501230a2a03020a110102070e0c09041a10030b060d05130b010b07030e010c0303060b0d1d0604 65
    0x207040950062040035070310303500210008407903400b86004007681e440400f140d0a150402a1a03100d8901c403008009081c00c20303620b80703441c00000325025942001d19250405003848a1780004003200d0a040341800f9192403980080e0650a000d4400b4040b002c050070315560600185541490300d010318002c0c0e442d20101800700400680c85110060760303081c641403182e40c24507a400b02e00203440c0b1920031403034900041c5000c5a180c3c842540000c000031401d925151348200341002e07005958441c0f016005070270a00700200001d841429901c40740e0014030444884a40390503104580e4401aa0781c14030040c0005031404490915004440780d104020030183c00108480c004203000915504d50442010795030354100d0250341c0c410b000c0e2546941480e20801152401f003105000314908801e0940c0d024500300c0002480d01180740031550f00d980c0c564ae5245180c0091001595140f130f0500046080c9a2141404201088840040e14480b80c1e081c07400303c0c10a4580440114541e184400c2480c44d4201104105c0070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 610833866 1250 610832616 610832641
    0x10f05070e010e1914090117070509040c09020f192f010e01020c07050111010903020a02120a020909030a0e1e240f0409060501020105361501030b070503 67
    0x300000e0802482045083c80080d502e40d4181400100c010682e0401141c00d4aa40c20300400c0307000195140d180603600d42d001d10a24941821030203606a100041c107110605100b11001e800c14862408689101d032203022800590300314081c1d0300c45062003c10501c0001580503100b83c1702c2c07842e42c10208400000382008449000e011020b40402c170000c0802c43d00c019000b584803000c14862080215102d40041809a45981c0c10780b0555001506640190179402e00600c0b072001005c5d0305030010800494560700b802740c51400c0e85051125406500094400750f1620881c8511803000c11002d5a50f41400003030150980c240804018040c0070a0f8600709a109000813201c204624200c030f02036903000c018040000d15107100000320000110116410494401039800381c81501d0b007041040c800e890316000124202c2358215811050542c10004400e8030345006031725405106201180d424040400d0703011a03240c031183d2805100002400c0e0010814006e130a07003016003000092800e1351450405c00c548128 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 610835116 1250 610833866 610833887
    0xc1b112706040506010c060609090302070503060705030a0507110d03091403342306011a09040b040f06030c260a120c020d05100f020c0714060405120f010f0507 70
    0x501d543d14041515680902d0f900f07050f1643c002405c0c8402a203451800e030240c0380d0080110058030992101054500d40455642d10896580da04d00d4215958803908070003070913015261000f4040002642c0031413160a00c200d50b80309483e510b000c06c2039296890050b2040081e600d0410741a0824044170440c1300d444881404405c00c1a603c0d20707400f141d852410594500100300080071881802c060320031745940c001d0701c5403400b90103506031019a039840c2200b000f04100c02205403010320741040070250615059100c0c070751040001c0c1001450007402070454046030355542050b264802074050400a0f400306c062250804c88029070314508080d0702050304d40d920018008014100f0071044103100f5668410080c060041e50014048441c441d103e0510a8580c3c1d0341c5642d40c2207030385c2804048181035049000300e400d40e10641004005031482e1a010a85440d201601035a214404000008040c0d8038010305210780a2200050122000701d6003619084032101c1c4e00d02070713030780d41480100b005e1250061f03031200303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 610836366 1250 610835116 610835119
    0x124020708031c0b03012a08100611122b020c030703051b0607120b030a0302031c0209060409150e04030912230607020d02071203030c1b112706 63
    0xa08110565803024060003142103810f070103620700341e200340169030200c040215090901f4040c009980c841c540071103840200319000b41c042032070071130100052071203040c00c1c0001c0c191000030f8454070950541045a65402031a00c02c00305032180c84441096101d114042c800e015001b5811480d084184c3c02a0b0740303038004d058016050080100c0c0c041094503030700001611380c4056406031503c2e841e020101034940b511014410742072a180c5100c0f4800fa00780041d000c0f68990301a0025820420f001c10301b00c110100115043c24084e80074000451203489010142c00901145940030409640344030800031120340b01c0c1d1151006800520601001c03035040200308041e02e0300c007090b400180b1003500300701c0e8456940c4414a149036510300701c3c5c0c4c042c220300070850345d0240712280e0031340c0c220380401c060480e5600741c07038000c40324074090b058010000a4081e03072210100b06090b05100c1203400c0c2214559040d420507401c02d4802c11241803040305289024100d0a009050754000070706005140d0302c1000340e4190081c11103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 610837616 1250 610836366 610836397
    0x2503050907150909090b010f0905100510031413051218100905031e01150302010503240306010b0d0c140d0c140f071a06031b0d0803012402070803 64
    0x485034030303c0f807408100940341030001400340aa8a02d80544900000d1240ca840d13040e18a0001c40c0401d0240100da0090300004149103030325007450b00700103000380c503000c6880c1070568a00e20170340380c3c001059515109421481500502040c1810002d0801060b80034051740440100700c0d0080d885000f080c0940709090903030f010064619a0b010685102a00b908402d0741071091002000481484000c0c004003841040300074440c91000c955540b206160071300000340814001c0c00010801b40034180300c4076580c4440008003840c2c40500011900f030150a82064098a40001d80024090300c1ca0040088064551a00a5070404118401c02d514090091074172821600d46c008e410311584181503000d8650000000f403665842800711045166000c118101c1e0810043da541c08400510045114807480000e000f90490b2240030a2881c0c00c12101100c2c2039209452001c100c3c04a030321040a14003810343d2075a01c0240030742204000040c01a0701c0d504008551101106002da006c02000761540d4040300807a1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 610838866 1250 610837616 610837649
    0x118021e10050705030d142e09020309010216031709071202040c12060801090b0a020306060412050304180b1c05030a030b2101051f14090405010b092503050907 70
    0x20b1400c61103800c400c0c01d000d031f00703190050455599094905004484d418009070100410b101d01a04060b86400410303d1f402410101300419241c9800840d841025240014038005501403100310500600c1000d03000241c2a03441003140306d40884100e6003264500e0014842680707042c81c030b82d03082030507554001c3c004ea80314000e801c541070007140300070503041c001c039400d0244540340c1c41e44900034102c881d411703100b84040307401042c910300c4640b003200e001d500c000d401d144c58142000c041c20120091035a00b2903161004220000e400041d42c48845600602618081014000d100030070030394150a8244a1004008000c40310010f5000011a0640a903904001c80d41c2240d00002a030910042c0b0002d1000300010f95882c80e13502e07810b61001c0e1103944080740305084403981c070f20405030b0400640101d400030b803100c1120702024600a03460b643e00034840c0001052556042022408000c829614041c140b0111109600264410002c0700e1403082035280c01c21040c0f07000180c1603540d0700103104500019101d40711 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 610840116 1250 610838866 610838873
    0x60103020d03050d1b0f09050603070c0311030706060302040e010e0c10140c01021914070f081c1401060302091804021c08030a0b100e0f120118021e100507 68
    0x2510089214041c081004402c0481740c60062405160328030b002850a10260454500500c058029281c001c0c04403821562801030564201503860025414001e00038021050051b041005000b840c2c800c0e000841e080f80b861041c401610014040c032041641407051041800d00002585400b0703620407540c14441e40414041940d01c10b0420000b164003110000b60804015415001048030340f81c0304c80e8505101110960407602001c0b0407451b610000d804200b40c1000c80d0a6030500701000d40501c1d85685003c3c004203154008000e49015100f5070380d1205003013100138051000490041841d800d00391f107000402c00c00a1646903208044500d00020300300802e040d5102c00305016010000b0801c0110142001e04290f54039410441e4100413180c2043c29005690900700303000c1d5164075068491211200e07800b02001809204041d0f041e4008400c01440b4000c002d09000302c030800401c2c4144605521900e0040c0900d40c004030f004001c004103101945046a00da101021400904a1805646410f894038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 610841366 1250 610840116 610840127
    0x70b3006180612030c06150d03050a0c080909071e08070507350c010b0f09010306020d0f0c0e130506032d030a0e0102151b090a0306090b010e18060103020d03 69
    0x1644910358440858000000500010301c0d90040c07100409140040e00c440040188414100d18000d00281082c400c12005500cc0c2000d0803007184286011803c258035070002c100881e101310741c48000039400004204204210040c143e1980942c4e18003108240f0788580050100c0c8280e030390082104400010240d0740584900d51841a00c1c0b10342d01340f40083e0030345c1c41450301e184c103d4200c801d0203500e880325101c2c06182070f410404507810050614022070303107540c0381d0400940020141074049901c440004100c0c1e4200c4c8a001038201c5a51203101294103940d05102c003083c44990f07151702e401d1070042400b940e598002010440143c0710703684120040d19655202501d04080140d5425511010400ea10001d402074128800c0600030b0342240d0b240300b007000c0d2032900780d00c0503201a1802d1007005400d40c0b000f098880280421800a403540c2c120310380e00e03503401c411152503040a0702c80944802c018045041801c40c42038001180125042c860201d0100071a29a071041c40700a20498901e01c180c4105070259 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 610842616 1250 610841366 610841389
    0x50909070f0f110f0d031b020d0f0309140d03060617270a150c0f03050f0103020f0a0e1503060603070602060703091106070507090e0304080c12070b30061806 69
    0x1c041d40d21203240c118024000e0a14200c00800002c00300c9461801f561000070aa5260400c50f075401103241c40000054004000b51441a074002c044020440441e007805c22945850032101e0340d000a4180c81c1200007003021094007003050114260310240030300c0c0107101e0b05001105812400084100b2503021542c0e14243c000d4000800d4006044010300302400b9550100582500d181c4a4030041740590204604880c012031700210081c034500018405414800c0120b156442d0142c03404d9400f580304c580d0b10018440444444a000d0f000c00c1c01a24036040502c04182c0294090b0002e02032141480e10103500c032113008218108069503840c803d01480340310200400c04001c082d2000c1da4400441c1890344d201e14141c040e07044000c0c108108001554000001c403800c0781d2001000e016064950b90410441c000e100a2020f07140c4540f45000c24030700c00703102c01064581d9015094412001c89030141100e0001c1c20021682c0503502e5404104080c0c0311007409a000f06030142d0411174698980000a504203a003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 610843866 1250 610842616 610842643
    0x20d06020c070e1f0902040e1f1a0310060203072a03150203090607050910030e030f0c150703020f0a030b031606030903031118130e0607050909070f0f11 67
    0x70000b13100032001c1d040e040010001e261307020341094a448a43d4801a849180f24800c034400d00100003405110a140ca01d440d680c4108400d113a0070f175aa040c40101d410586001c6086039400082844503400b08043d00000414560014609008154450000828400c594601002510a0307003082c5010100103c502a45c0d0112180201011458100e0002c0d0401c82d02103450b88103081c04120f9280c000c1080c0c03a55040c00600803210080c2c000c40c2140601100c0300300d1080c40c841440320840d03040058000e08100b1207401c1c01080d880d0305445122000c0803010f41600103241c070401c5544003024011080719007e0b100c50a020070719280c4440800e10b000d5807050003134000f03465100c010444603456044080805d00903035042c44044e1403884200311621035281e07103c1c4080c0280c01d14410a04051942ca03078842d5551500017148008422a5030a01c2070845445d400100c000485242915001c444290802c40a00e40b03424076030016080a01040c940c90344480a2003000078280201030420030100034130090 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 610845116 1250 610843866 610843889
    0x7080a030e0304120302190503040b0903070302042d050c07060519050703050a0609020c15070c06020708030612030a1d0604260f0a050c041104051c020406060c020d06020c07 76
    0x1d944c4001c524400f01034070104c0050085540b19505003800101c089403085e0080051403801e4640141860154030040322a50940a4a00000050f9999100c0c0100c02454120a00040117006112403600c8400c1c000c9807400500c0c100900001b07070300500c151810b2a07800a03002951f0f03203a820304031803d515122040f03045a42400c040104a640c16003145015000300c1000740801912030240c04268001c4c0c0d1171089203030f40110b0107841031405d40740d81030f40c01a00340e003022260364101d07480d0703001030740d000c1a01070390320300c0001007480305070305045407480c40c00c958040c00740d820030360100350042c11013807800c5104d6a0f580c84542402050f90718001154000c11022802031a003c4a002030078040200c0c24001801e42d0151421680781150003081341c1d080c4c00d500101034500380c907542041200510b0b540500d46080081884040384548540c00b0641ea140f003001c1300340d400317031032140304101c2652580c2d000f00042101e000110001138640b89490001c451f4041d401584960724402a14074001003940b001c004801d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 610846366 1250 610845116 610845119
    0x41e020306071706010f12050c21090c010e032d07060206180106060807050307090f0b13051e1507050619050a020301150e03100204140f040c0507080a030e0304 70
    0x6411407188405501c0168414002e9904d01e001582c080000100070004500f40c1540808108810351103a544030f1102c00005003041c01019031456004843d240e03000001040c1e009015000908215025507480b003440c201409415071404070f6140c003849240c80884c03818101c94215a42a0301800e070b0111540c1e00101e0301050381d1094020b42c0e8001c1981d8148044c0324840c210a10030106020700d00030307601ca0f43c035156115207585404460a42c00140580100000300c14045009003130f489520000b03158400015442e80c9200b0011010b50a1a40c00703240f0520102600001010b58074141e0603080a04036514500c0019054036400c99105a480040040c06140c00300325806145c0d400302c50040c90300356400c00c499510418698121711080c007039a6083c8080158110405101e0064009400b1000d820303929462a440c501320140d0b00720307412108034802510340c0c021a905090b2951030700c1c1901140c0038004501424000350a42c4645071000e0300f42d24000a41d07000690082c2c0210810861b85022265074a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 610847616 1250 610846366 610846381
    0x10630020f09010e030309030312070c05060a0203012607053106080d020f070e0406020d1d1603080901030b060c07091515140d0b030303011701110a08041e020306 71
    0x60b48800e599501058005200807560300300002600c00c00e04000d4002c51a101c03003601000703000100180484104400c1f5251a00041d0040c01840c0c01903418100140c1c8075410000d00c403a610f4505081031080801f11610320324400c4c0300040032411034005507080110324258101241c0d480c0010b01d208500101140100f4540d04a5a8062001c8903841c00030751741181c500c11400c0b81c94002281d074030312440e801494280205850190115009031181100629120005106105031000c01301007295040802446560080060002803028050798200501d02030550741c56030114025154004e04059031560448003640700c107802c980c00b0140c0303a01151074059440d071042c1e010b010340107c03e40d560340e80301500142c2200b50717105071856a00161601030407410346507560b90b0580c024030700500e001d1340c40302e0403c03066031420710046010341045201d0503040d100401d1403509540d00303141213640b40001000341c070422035444074071603820a6100200312000b1280100c215901b403000c83c0082e40c1f44c0074800c140f040c1c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 610848866 1250 610847616 610847647
    0x80a02030106050111100f0e1005010602060703062102030f03300c07020f060915030907141c02011e03020d110901141605030c1f0501063002 62
    0x184210001e019550b200c0004446500313840c04421107550010342100345088a640181c40d05100440d4000b034840c02e441c0d1113a00d044036050821280b16501d02c0144121031303042c05241c1c2d1180182c1030034802140b92050003602030000c0c2c14031140301a50240400210358050060511510740d00302120780320300d1464216030003080d4401803000752885080200d0a8091800d4810380319040581006080040917002e000e8455a00d111b00c80e0300c05410040d03011955160b0344c4018258080d00e4040741c0380d240000080340303072aa840d0401089840000c410b584070741c1e52040703038101da103009503030302c0c03202c0d01142c4016940c85814000c02510702125007503c62269500d035015000b01d440401051242c501c000e03820391103070b00c2000000340c00a170003024030310030b5001880018140550645602405010b1a07141c15095404c0b00c0d00c5400c264100303444900381c100c0d41d1001c02c3c4c080c102c49841045994540100134203461000c442040e171401903c044071300100d941c03e800070304850790ba21040d540c6152804501c40d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 610850116 1250 610848866 610848883
    0xd0b0408090607150507030b0d020904020a090606030e011521050102041503050403030c17070c110603071115160f020c040606210203010f031103031c020a111c0513030c08 75
    0x185445c00e0006408188240180241c600001c0c0c441c500e107c2c007603000d001c10040300030300998020b640a40001000c4c402803044c1c2c0d0050419540c0020f0104c643e0030350b50b003542d411184c51041c0740007641c0240440c02014504c4580001000780d0704400f038132546482c902a015543c802c804c810100c2581202d019010f4101c2d40c4294440d503402c10100484800980d4814040c81c11030940048003400582da01c1c2c094008001085d01450b0b919201021410014030b03103034411910301000981c4091540c0c1588020400840400201072010b01036103496034440c0302211000c1d0180b401c100254155400140c000d20541c008098040c00500000351205000b410025050045580f6100c00c4503101c130300031f0814802c0d241a600c201c401054280e2541d00c40b02400c80c0f503444140c0c0d05010400480d4840b402070b044550704a01a13903009a117030b1a1000f80034285454641e03e1800c107800030450100c0c07285040032500100106401c3c89038480303101008010b084900ca8000802011400c3c10109806134005032150 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 610851366 1250 610850116 610850153
    0x2010c0f030305040c24140903030301081617120304022d130b0603180f060a050f0a0e0d11010e0f0318010207080d12180f02010e030c0d0b0408090607 66
    0x300c281c0d5851550403d4400f00740e400b140f00c003280031b403501c0c0a44a4900750020303e05100c0c0480c280182d55002a0442d80280d004680035480b034901d402c40104110100002420441742c2c400d101c0840c3c1003402d4841300103a84c071201640000000500719030720411000d40c1d014400c020242c0c10350200b42e10034100c040100c121442002810b001d85009001400383d0801c40b00050070706821512032400c22251a0004c0100c24098042e01000745801d0108005962103050180300107c3c617802c0549041c0c0030b1400280481000c036041c1009508031500029004400003414900740e0355144910100c40d00515000c1c05481c0c0900804100d41032010000010384102145074034182c43e8480743c50010b9981d04034600c81c9042580010080c2213105002d44125440c00d004400041000941448104008071080c07604682841c0c4021148081d540d02c1100070342000c0041e00205480b10034040026955401d4142c001c08c0b9011510004040120390000d803034800c0c1018000d03a449400323a144c1084030680752100e81 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 610852616 1250 610851366 610851383
    0xa180b07080601170601140d1103071e030b0f090612030c0d2d140d050403090801140105011d0f090903030609100b07030f0e0d150c11150402010c0f03030504 69
    0x104c40c02c82c03401e91042c01242d05840f01c0c48100c500d0042400c598010f9041a5000d903510a00c070b8803c8402100154400c5000d030742d0300400c07401000c849104800340034103044101454609004090385038190b0110900c502100d042402c1e545160004051010803188903c242c08003203803516840800080701d20030421503443d00283c25034103511101d840f820300c05030f041b060107002840d083c030180134101188500012201291601344010703500e5003074450594040380000c1e04400108850082841180c0750b032264500b15224030351501000070b09405e900f0482d03403c410412024590300e6545c0d8558150349610181100e0b00d2032500049282d240e030402c0715064091070303001300003440e80d030014200c06040c2c030020030141d4149002c03520106c4282007040004024044800c0d04031541e55103484070121028071070651b01c86c44c1c034264031114066034010b2048006200c0105a4003150384400719102c84030b41c2022500d00f0303d40da51800100ca81480d955005800482d4000754074007815416000244030354020700d1203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 610853866 1250 610852616 610852637
    0xe04060503011e0e071706070915020a02010e1c0c170a152c0109120c020307051e060c01020d0506090609071d030727140a180b07080601 60
    0x141400c0e2041d00822207203203508006904007004403a48041c014131041000c859402c1c2d140e034110134010310071080150041e8800301c10031404591022460b80505403c40041d48940e42d0584042d5442d02d116100905211010b0050340da42e4842481d54405c03000700c0001042c5640b041c2c24161011013560085819052503200082005a80003a489500f194400400003440d1804003900000700700c200101080505444080c0c001d141a201c00350b0b540141a01c0000313201040c43c6400d00c021000c4802d04014410510f40f403001584e40466084100c900507207401940b40c50b5030f00204180c008441d8010761180021841c00d204100c150301801c070009402e48108074a403255000c00111480c11070380c69510081c0100010981c512440690301f014280103101000780c101140020f003006810b8116421120040711900700120754a50f40003c01805500304105003482d0902c801c80141e401000d0b1741c00a52600a80b4040d0341c00ca10728600490f0700001001c81a0810500007816424144c4015002400c00301c0d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 610855116 1250 610853866 610853869
    0x20f010f021b030f1e04050a080309031501051804110406030c06170c090f0a2102090105062802030c01061d1b030105131404050a0c0b040b030604020705010e0d0e040605 74
    0xb2600c81c807800341d10b84c0c2d0030702c02508290340794510340c1c0c0c01c0e210f080314060200107016160241400068003c9001842d1101d200c0c20505140c60071112040e022400a04010445a200d010701c0071180c2d1038020359440d407641c1e01c0c14200c03040d40b4008100c507041840c049000062001a11541068801c15940c01c440d400141002c0d111f825002c1e28824903150040042c143c1c0c0d0718184000c807c2401c0c0203005e484050342d4036170501d2441c6d00841e8448002b40704c8172a10804510f0085680d41c05848200c0300c070b5040031044072120351010135840b13280312141c0200104e408080e0082050b12507aa0400f4000c0c42a5511404040d01c503003245105004085c1e050804505196000c480c041e00505000c00094116071915003081510a1107010000000340d94528080105403002039a80c416801080100103100303183c80d00041c0400c0070b0744050980308081c802440075908000842e0740201003150050384603041c030309000d8010315043c1c14014852080080703041c1241e405c4113555441100031601080203070381e201d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 610856366 1250 610855116 610855123
    0x3030906010f210219090f11161e0b07050a08070203072109092309060709060c150f0509100209011e0e060a111b030d0f020f010f021b 59
    0x301c1100325080180104401980f60000c14000e000030441904c9030315880746407501c190641c00c41040d00e500c500401091141d607000718882108075035140c41c600760680d0315a2a10030903030350000305000000003540f503001c100c0d01c07440c11a0a402900c285503500f401d14015189a21181d0b00d000443c003880c5c005080fa900100945041a400c81c210803000040c00100d89c131039101002e820f20520201000214082c5c28a224481407103400e207202100c4522510880b01042c68010002501f076400201080f00381548013907072101301e64940c14250b41500d1107151030030055102c84441d05c622440e00040c00c02c1d400c810342016000c0d0042d80d044d240c0d020b0103030031020207138464460100e0102e00a501d0940c06046001920454801c1a1a00c60010041003000403401d902c135200d0354000a20b894110340703150105000f4001c0c166a1807003c25001c0081c0c0c00800d4581200c1d031091024070070150280c08205000b40801008604007900030059462440b42c0b0704001d40002000244000082c24055207000000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 610857616 1250 610856366 610856369
    0x190321170c0a08070201060f090b040b040b01050d05093f0a2007030501110406020705011b06020307020f0708010c140a0e0d050f060a140a060b0906070f120203030906010f 75
    0xc041c480c6440c000100c19150328030041d214000310341d41e5131800514080c2084062010b00010880400c5e40d841e0705040000361461070000c64801c030310308401402c003603804c01c2c2120380da240b0585001c10150f0310070103681d04041c00144035001c0300203038104caa04c48802c02c0704c0e01860030303450b8040082c2480c1c44204142050241d08051804100d220a81c000040ea10a4800301d5a01c0c03c0c80850300071b80e482c1d5032070303c1c29507a800d1010312031008042803d01400b9010300005000d041d0030f00c0d020a2040c0e4584106c50384031954403002d48250341c00008a41224805e010591072840c40b1011200d1166650618070300070554241b182000502c0c880b22400c140c0100b0382100c006801c1559071010f01c2105508020703640c0c150507804c80e402e1056040c048a024402e02c8114481c0c12003200005a0031441103004851450081c001d1034540e1410b401408000200e00a40c0d6003520203849003500c48403a40350a0b00c02c413018000150400d07414a040608403640040154803031002107050710602e9070380c2c240c18240004903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 610858866 1250 610857616 610857631
    0x120a0b0703141e070c0606080703030206040506090102070305120a0b0d050f07050108041a09100504080301060e060c0d0513030206070f03030c08091c140a120e0c0f19032117 76
    0xc000403984482c45400c60b40704d05da000d0000010300640d84c0c54500d10b81980303580200c0241c0c2240040109224040c4502a408202880203503d000c0070765400500c58899100c425811b9020a400328075400060781c8a810000006809245501460709100381d03503d8040446e24624410420f01040c0c41d489000f4140c0600d40c441d500301450030320010380f009074050003060901e40b44950483c0000000240c010f05010300e0203040c0803940d070750610703c00401411b2050301e03103070203040e00f0801c907000342400050000c04080b103403601d2034076401c0305411301d1806145644003951140d0007244400610508481048410b4400d031401c008043e01000281e03540842203450300401c1d0002c4c105401116045c501015580c0181d20708204034a141c82c080401641040492100203005200700311918416803260254164420000b045c0780002c81d00000d4050308101b88150007000e8000e5480341566011800c07801035503003c03401d14108000b046910121454840c0c140000800000c1030750465140940c2103400f602c071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 610860116 1250 610858866 610858921
    0xd090905160c06020702040e030d0504020307060903050a1119080105090105060a0302100e37271e020406050a080a051b090d02040e300405120a0b070314 67
    0x30707283c981e00300030340000034213903001600c0303c11408042030140000d096407003060000243c03600b068014549000d22030f40025050004012050001c41d4000404005169102c21841356808040c0d000c102d0a100300345d52600742c001c0405004c100d103081900308038444c8182c0c1c402080156110000c10526036500d200194001c103000c1c5900d020306224040c075040b000302c05094441004440c0044108201c05000134030500070010412041141c000e204207402400385124095000f0980d0784c00300035100108680d00c15080c0d407106054010303400200c8800c1c1d40c4071803c0f411034445581c0c16006c0c00365880440c941002542000c0000c00030800c07442218001d2034000302d20940c0c05075041620381154059454143c0c044191200c20006a03164020144041c0b41500944102c0441e02c10403880f1a410305652001081c4400110080c910b4007400e5600303c6501f2502d200d8450005250b6904082080300d003c0c001c103000c00200a8a260035400c030050244e40040b01c01c01c155070705034400c0300d2610800c1c2c40c00d08041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 610861366 1250 610860116 610860137
    0x903200607021e09280b0325030209010906080f030c1009060209120106081023070c1205030105100e180919050604020a061b02130e0d09090516 63
    0x40510f50310a0f0315402c50806112541c1500000314010822501c02c181109420507540c65200c10503004400483c5d03202c400e02004c0b41e04000a030711007000d806203809591a0180030b141d8804c55140320801560040c003040c4055846900440280181d03020304107640c03142580825009100000300c8000484400150446501c1e04407520041c000301d88042c1c50f042c4d002c0c88000c041d03582c0c2d9104810400564000050201e1030641960309098029040055035460140e07419880300101e095505448401800c40d81c03981d44444059039200402100900221a0100d03c01001500207000b0740c10786100300d4403400d451840403000c407905809240400d41101a80a00704c1d08a00e81d003a0b100e8100e5990b0003510496a01181110321007030641c10140c0d0980c1c4105c00b80010340c14080102c0000d00524a4080003005180021440e10140000c0081c007546640c0c00381602c8021079070180101004040070b0f26620b403c4040010901c041c82e024003002940307490f004c02c1d0312948020b421035062000d511069440c0307 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 610862616 1250 610861366 610861369
    0xf060305060a09020d0b091b07020904020d050f06101502030d05041e030503180604081e040509151206060112091b1805010504200a0c080406090320060702 68
    0x8000c050052074218211400200d41010703140040d0a0340c1034007181c0090b001c1043e200300400f400c0040c080d05000b0031040344110302c4080c1101121015038041d41c0180240c0c0342d520110300a603090000180107070040303140440e002280460050b0003025000e40304110709866040e40284031010000140c0580c1c4204003055009495400c0264490b00506200901c0a0020f090f0120110200e0084001400000401c40500310600c9803107542c14000004243c3d920303203a0b44d01003451092031040340f08021502c1c0c424942440300d504650140001074140300060074140840341500b1a01040b1070b00c908541300540340105000a440b40c820b2005a40c2c0c400300740380ba68030140052070984002c4c0c445a441c59a0700024845161517100103246200107480500c0c542003004040710010b0b005907110740e00703041d510300340c0d165140070f04020f002424416a0381d6480a01080d502d0b1907502c0c6006100d090041070000d01d09030406a49000c0741d011f15070900c0e802234a03c5405000f81004a80150300090500074640035 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 610863866 1250 610862616 610862621
    0x105090d03030911060d2909010b1813090b06100f05070f14061b0406020c01081504060b0901031802030319021603060213090b0a302603010f0603 64
    0x15540500c4240103100b0395040400c036140d01c2031544281d803944a1540047e440645007100300b0070800e070140014150314a50001e29214010701c1101e11140340441d1100b203907264502d08a481d0440201854a0102920300c0c00c2c02402c60070742c099901c034491708005100740c00c200440c0902c2400035521032000e4950303550250745d9500809020795225150078120fa00044901010401c0d0903081001803000d031515103a01499000340d20042c03042c00405003c100401500020000c0320880c090a041d40a56a80c280511404031185409175000c1d04014000800c5100a00103001900d0300380d030107011000038180c2401003c807055000942541c01000b40050310404001078a880c401c45206071140c01d0b0300352800090344141f07030b001910180e0740051070080031680213244000030a1403080901141c900000000c075031100c0c134402c0000501c404078140b40d40d8500344030b52400290440305641052101802d0000d60403000d821005c0480901c0010242d20000880c2524103c44d4140a40b90049080c40c03800c41c003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 610865116 1250 610863866 610863881
    0x30b0906040e0a0204052e060519050706090303090320060103080c07051005040603060f290f070309050f01052803090206071401060f05010905061e1b0c0105090d0303 73
    0x40f4090100d10800694031801007a004500346645011204804044a0084244c0c4100101c40441c0841d040020756009001c1e16043c21034000c4940c0032401102080d54144030340c0c0001800c40c1c0c94040c81d442010303050b90020020341d000f036844801a51400b546001ca0700c145101c0800c90780d014000400010301500000c0802c482d1034410303544603944d160302181090700030554540c00306501280c2400a190704d07205600050410b041c0389004945002e2070715600c07401c81d100e041d503000e41c0700e480301881c64415004c075000300d082e0703040d00c0e07590794180d060040904009008180c802d248600c5403004a62141040c2d030b401010040d141c400e5803600c0f4003600c1c0d1200d0800400002e02d6101c0c3c0d0702c1c0d400f5070ba075880644002402030290f594038150041140f03003103450907007210b407101000e00024840c2da6440844102038410989a060b56084480c0361000440591800b08000b00d0001882608080803030100c81003581000c2d00f21008800180c1c0107490318041c00d00e000760001e83ea1000c0201180c4690040759 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 610866366 1250 610865116 610865141
    0xf05041a0904050f0f0604020a0801060f021c0306081902030d0c05010f0f02071a0408030604020a09090606090f0902041a070f0501290108060607260412020907030b090604 75
    0x62610050101150079240c0413260a001d01c9040c10030081d030940681151544500c1c1140c1c2149030003c41803002d4104d18040c0911000c00c4404c4200121940c000c1001c0400042d480e004492510a0100b005000c0c000034000c3d00a240180c1d10205005416000603814180c0d00802404000404103000c440e01d8002d01d0040c1c84542d202c0354032008080321803090061030514a40050303518441c6050202002603c5003010b0303c03c01d150fa00700008682100d0a80340c000404980240c3e6840350440e04071442070464100071042842c2000004d82c0719081100c120489030912406010301e030361507201d03000b01d02685c0b2820014001d04bc0781c0034003e0038640010945503200300203140040b00c1702d481e424210ba1004a081ca0129a100c00308031400c640600781c241040001d00c0c1c4601c041c0351170f2021a00c2c034090990003c2c041415a00721031001d1100700d0800042601884105072125919107001d040c948212006a000d40e04d82000f245045100c1c0c0289080c42a0240000c401902e444052100403c5402c2152 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 610867616 1250 610866366 610866419
    0x120906040e0f04200f0f010e04050f040308160801051c06090b090f0d05120402120a08031b040620210304052e270503190f0504 56
    0x10030a186000e41d842d015042e100c502c02458646441c00707003014440303402d110450250880d900d0301c00384d90300c1c148141200700076100c0d0054018444016280c0310380d00c0c3c0c40740b54000d06101c20085600002d0040741d02c2240295070300012038441c0e111000410002846d40b03c00503114030700600c1a424071001c0c0582c12075070502e0309010040103450ba00122a00304030f04480080c2c80b50f091045092040041d49011002c070006003113030400e400006091441850b85601c4c00980d0840001c0942da5038492a8500c004110141c07600d140b0240ba2184940c1d200301c030442021043e20004181c1b000071101034805a0b41c40b80c60300c040c80e80081e04c0c2d26a001540308041d580500ca03000581c014000001400801400d090110f19280d05241c076004d41404010010703030745042980c90a4030f003282604000580c0c2100c0500e00044e03020042c1001201d00115445465000c40401c0007020030801300000800f4042c08040e4011224200888100e444c8050030901d4400543d003403009124100f242074148081d5140124031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 610868866 1250 610867616 610867619
    0xa061709030d2a03050601050d0902030a02030f06070f09030b010603050912130306050a0207022409100e0f0f01080a020f0c070608040b0f06130902030f060a0b010e040e12090604 78
    0x202d82034401c001d25514205142c0c040709030b2a032003d011181d644840c0d038101885036140c281d0008005004560b054500c0c103495041c0282551000d108200d042500501600c220301043c4411994801d01541d0100c0040c40020181c40f0141c031541145040c0c0e58410000b0170281d10b040422005028086c000711210700454002071a88814600241140c09034041c0c40c0404900d1b600b000011114001d0003404010700412248005030758021851800a84952989030f1070001108103582500503c07080980101c140c201c140031161b00407071034041202d01210110180042e180a00105200810b00b460115281902260304606150050312248030080c0c0440e00700507480c840685802050b91103080803444180600c024000020003199006d42c046000c10380b20700344140805c3c000c4601d0304084400c3c50b552071902e021568113000304c00005440c0d0003144e202c0e041080c21840184400d026090104070303051069407241c181400381a803101199000b4004c050090071001606074054007820703034010000c020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 610870116 1250 610868866 610868887
    0xc1002250512070e0109020c030f0310030b0610020604080d1404060c0201060b040807030f020d06090b160c03090504110c070303031b0c0b06040c05040f170c0a06170903 74
    0x100c480c00540031152025540c6044180480b08846005032050b940182809219290102c0d0751241100c410060040c1c1c0d07000d400080c4c5085018202c1e030001d90090010074880a0300d41001c0c100196400b0708556080c0d1748980c0c040102c81c1e60307982004009a00401c0c0003030f0205030514090051040000d101140c451324651008903503080c00c80d0201d07680c0c1d80e180e248891450b4244100000745c455425031744c1c03806003040d001c40d549a0f42031000411500c404901c0a01b1502c50640030030310103a010105021528403483d0081c41544202c0b51241034000034002d25000c1841803804481494141d04c1b0004c2c01810902404050a82e40d0070300d4007200020040600e8904003081300b4802103000e680d0000c0c07000c3d2004e0850b8446a1070007421010090302d80d502101090132280c103190003d104640009211440080664050069900248a0340300c868070019040d5001441600c501d030f150030aa417114000d140810640c13112901406c00050440c0c1c0141c6402e500401500f5000142c1504a90038901c4018 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 610871366 1250 610870116 610870153
    0x20f0906040e031c0507080c04090e0304050a030f03020f0c0a260f06040614011511010b0613082104060c05031c0b0f0904080d1812020105070810080c1002 68
    0x1142004c0100d507900208048044501c59a43c00040a1a00841906011007800658080c500460a0441c0c0c0c588208a1022007042100c000b040060100c0301c007556a8205015408036629050f0058050242e8442c441140400e024880030001090702d5405d905059081c0c860b8541040070494444042002c9107403c102005590000c50624000b04210303e00340c9040f20507580c2c803090903880c03038002100510a4040d02c000b10350100400c0d2910103202103041d04014050318811001ca030b000840010164071420200715814150b07070804088170710802010702c04c9800c8400c1c10f19201034191b8180018000c482c8504200021280900e003168108150f00d00e038107400b01255910700700150780d540b071030781c0380303400d01e02c025201c0710a040328a96003928254896070814410014401c4505940d0740004c2c40000d040060503c0c05900085e210701020402400031f4000c0609a0b51030012601c03003030008400c1464810700c00c040d00e020348050b0442c1e03100781081c007524540c5c140d402e100354042c0e00070138400e00c4c4206 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 610872616 1250 610871366 610871377
    0x9010605071106072105040302090c0904140907140303070f1113020c071a0310060e0307031b0f0506040f0e040c05092a04081903020106081902040b060304020f0906040e03 75
    0x201c1c0c0040170f6002080300540b0880c3c64586010034040244020030140c1d41d051070007a800070042003125940e050740310015004140c41c40c5030404205c0548240029040c0c00202401952400380c00d03804811501c1080581e039009103200148000280007032540002c0c0c542c20200305650010301a45400104c03881510144d802c0088440c585910002e000c00600e0345424813020f03030001744902c062071414050980801c419042c020038091101d501c4880c542c54500300b0400c401107401800c852100c1d050000220300c000d503280714044051003d00c5010406d440c3c103500f16422540d90311810039039280740c0040003aa80100402c150b403007180c10480002c04d619034030364182c858445091000c00041000e0002c0000000000006101050500051154520004100b014050a50500800c0080a1801f24050005a00305040f54024082c11201e102c042410200794a8404c030341c14400411032106100d03050104982c00307136002140710f0780071074103081a280d02e540200e000341001ca05007000740602841c6070701c40d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 610873866 1250 610872616 610872623
    0x90a0f110c0109060534051e03040b0106080702060f09010f090302010e060708100317161202060702012901030b040e0a060608030705070e0a06030c141e0901060507110607 75
    0x46250540070012184241c0381c6c000c08886043c40605013911035030024110403150040c40c44c00f00c0c120f0311403543c010780582d50f1003652015800b00504c0700d459404240d0300156402c0700d40040701000410f401c0e01451019108000c2e560091989540340e0504002d40e1f407000c0d04200d080d560318185080c12803e02e014800001d03000340c0000c0b615903000c0c034903c0d00c1c028000b000e86c410401904144001042c801c0e48040880760080c0b4000300c207142c1a440c9500610610100c0c180510301800c0c0c00041101000646070710800795001c0d117616586d8030009070309071210103030640d030100480e841d109c0a040c0010301c49104640c040c500021b032800e10401081c01c461803101c11004039800008580100030090103001c010b005044003031401d0200542c0d800340d171400c850080b12020b010340b50010740900c41c2c80d4442030095411005081429988254419100c05d41e4000e182c014440554075000361080c039890281c1004010304943d046a18003035040341c1d20341040c0411500326141069007007242d960b400113892300600 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 610875116 1250 610873866 610873871
    0x6040b1e160e0312040605070305040f12050613120c0311010e030c0d0216030b0402190f2102090f060607170405010306080f030f070f0f151a090a0f110c01 68
    0x400c00b034000400e500348a840ba5000e4030303d24040c5294007081d541207503250f040c51516040745280913039080c01070341c0012103132460000c3c002800030704840e031070601780707014009480c0b2940300c0381c82908107240402406040503024464422400d44242d20909980d0302a10b401c441440d0110b210900f2f5900580f00c0e200c2c00d50003c0f803458851502888400c0303202e0101d000800b04100f80c0d40c1d00e1542d510b05480042c04107104600000d081d07486a21191218035126480b00302c0b002d85803001c444403090a4060440c3d84550304074182d01d543c2084080088554004000d04000c2e40c44018a140269000380550b400440610030240003865490000d030611188112450301c5a081600050032254641d00145107680702e0029032200a0340401101c00410444901e195030301c0d00350404980120340e020780108410469064002801148891407644443d01c1205004907054507a06081804a1030080f90b8810141c60104404561590100ca01079060f900041000234801345c1c81c0b03a80380c01c403408006c0c2a94 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 610876366 1250 610875116 610875151
    0x14090717091605030d02071a04050a180609060e160212070b1506130b0903031c020703030e070b0a031d011418060c04090216050607030209030114070206040b1e 70
    0x1e211030614005403c05030700914824034110402555a5818070481c95001004550107910b00c000340c0c2140c000c0e090107840b0380c40b2940c3d5200c01c407444510b054100e000003407401c00d0200301c40380c4130b000d4002107441d190748a07102c0361611104c5c2401c2003100710540302588035040004d0054400381d4054540c0794002c00180b0702da131401c58031141140c0b468400c02031080c0c108101035000d0b88201040101601c52000c11140c8805200d80401c0c40c3d0b1180300450b112101840011518450094000b00b849034845d55090100c2503c0c103040660740c80650003072619505c024811140424860f60140104201400001282c001946096421100b0321119001246451002c00146000d0b440d80c9105004610008000c40d24002c01020101c3c050742c003070000c0b4583c000804207003154401c0c0f000d0104540140070780f803a50401d407001900035844247c0d014025400c2c245102c003908070001c945481034841d500030f0902a0b55a03038030300039945002000c6055035101c007400300f1003081801c1340b154840c1d100c510180c00710a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 610877616 1250 610876366 610876393
    0x60215090706121a090c04060210020a092c0a061e06050904020906070b0403021c020a030801150c0501060603051509011a09030a0b07030209130c020a021306050909010c03060b041409071709 83
    0x181e50302280010050040040010356607000e008442280c10101c800b11902c0070800f02c0b40ed00000a040c51035081d8480c0040c40300c030314411341c0000c003100c40000c03011004401080079031030000424418480800d000384049100e82c140342e0000d00c2584e00082c405071500c1200d07503811980003800d40d010b400503405040c41c00c00c5005484410318a001042c0018803505184c2e50300141412414010140045004c5803003540050044201800c8150b21038000d100341a103c40d4020010b0000301e822040481c1c5041c50404107052075041a81a51110007002400c9900f451640c6000e5000c940d2a0341c252090704600b0000c54040c82c035442c0512100e80e009692381060384100700c141001042c054030034a03d414943c0b414240c00290b4440d440e541070b5144180070061148850040c44035500c00c0750000c000408120100c030b4194408035000000d618108100c80c6c80312502540ea019078003034880400c11030145000e503450700c0103015900c0340c5586480610030340c2880b44a6800e14054031605100c0d03000520003442e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 610878866 1250 610877616 610877623
    0x210703020601051813081b0610090c02030d020705070b0f1c020306030a02130e070b0403020a0e09060138090f030c0609010e030a0507060215090706121a090c040602 72
    0x1403c007144e92451103000b10681092803400a0300111440e03400c8038014080042603000c0c1d0f1000340120681a40d1011492040c0361149002c4440017024000000701007182801d1b40700303c01031071550760b0080d81421101d481440080d4820034003611244620400015064800802402c04180b4007840c543c407000c030382d110f41e4001d0544418200041b4010310800c012910700217607484695030102d82c02e070398441c0a0382182c0300070107040c005c000c0b9601031110b010408110200080003120301c00d81d107911040359110f01c0307011642c1061f5108a1544c00c203e004115003007903000c0c044007804a55084007400005046582440e1020521811100c500404c90395010718104c0c011034076014082c1c01170502c00c4090300000e041840343d01a140c0c184201012018103a440030081d51001c03503070220869900b5a10f481003e56070709000403055482c924040d0008084100c0412800c1c2240c1e5640c40d540780c084c0003102c006c80640984002e4000314070800301100207590700c0c130f201107000e03116a41e80941c0d52400c015000b0309 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 610880116 1250 610878866 610878869
    0x4111201080a020d200411220303020d230307080105040f0912050c0304120b040c17030406030f0b0a2c01120b07090b0310050901080a020918210703020601 68
    0x859030040420200561507804941c20150750100081030280c841d074400c000d0a0440c03c00701c1b500145840c00c6c0c4244c44c0c10240090290b84010343c4444d01c811000c0c407154101010b507000042c01a000210b25419290181e401d031910340c64000a40ca540194100070b44002e500200c2d0800d0000c6d02050040095040900c50140510b9000c201804110304030746400c42006d5003030807240c0c200040004c3c0003a0042c018070699026001c15244d4403403515035820f01c19203211080e5419034050b23090020000307140b40c4241980717140d010501c0240d42007915218065005280c4002045440783d11042e25201682d038030441c50015080889103100200e1000800f00000400e50b1180400000342c0001842011003000240c2e03145039002c8403101a030360700c217101141c0d0f5070415480002c0d01400031007800480250000450103032a000e44101503581c1ea1340c03100c9517580083c03500103500b01c030102c0c0114280e0300710b40800342440690401100d81140950120f540840c0c0011140750803810082072490030164140289030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 610881366 1250 610880116 610880129
    0xd0519170c2e06080705010e09011404150314060106020d09080709020f040e070302030103051506063c1c0b060a0503041a09060a0f1a09090c04111201 66
    0x5051503030304244942d80e90101502038090b00c0e041807030ba500c440b0022006402d141e05a00e07040c84081d585950070340e40c81c6902d0040d540415181d440034000c5050500c0880d04858441c500c0300306042030181440003c3c040c0c0755039850b0682e20741c40d0210204082da2450b411880d61031000b03004c82d61428400074102082034044a0401c50380e041e003080909000600700c5d05444950303d0060780e03805c0e080010881403040d23034010b40e02000c0d9102001495070b0541d000d18100ca00440c04e9401500a095080c074100404079806540b010040c4217202545c0c1044034241d86191401e04900421045400c0390103c1202407c05008071040004400d411841e0f107985c04204144024424050b030440f00c3c000030454003e500450301086000b00000302400f00311851414060180c4031524039a00f82014555141d00c2d080380c00f41d8016081c010110152f458620401d01c081c80c41c51468a8200c14040800c415100d006e071490325244102c0303a000c0c1050b9100e01c2801480c403840a5010f41c2c80d0080c0300c801410b840142e1005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 610882616 1250 610881366 610881413
    0x60d06050c03042d02011202040305010501120303110a05040e0901090c121a04050a031419051801180b0c010e01051302031b090a05061906050309011514010e0d0519 72
    0x58034802c80303c0c60340084d0710340c242004c041c1c02c0000e0400300700a00642d8000341266007864000200e90580740c080300841c4e17019507414400100021031540561094002000026104020801205d400c0080303164200c0c1c600c0001007080081c541f11548207041c90b4006c2815401ca1440c03060420224184848904c000055000784914258030f40e151a4000043c0240c284021109204040038002e411070301d544000c2d400909940d050b01030f004080741c002c02d9100ca500419041034000307a41c0101c100ea4000304584280b8a561406d14011a240743c01141d042400c541d201e40100074184000c1c01558414000405520381400441c010985411046801c82c0700003071002c060f0780c40580765051100c1d41300e281c140010425481d20381c00b0525410a04540e415000d05440020030301c1e560140046002c0da0900d0000c4c001481078500880b9404914428480c0d0450811200c415550150000d89440b950081003910b040701c02d41c45007410904844942d0880d040004107890401c8218807080600100d0a45030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 610883866 1250 610882616 610882673
    0x60f12040b1e040804062f06060103241404110d020904110a020d08131407061d0d0f230328231c0f05060f090f060d06050c0304 56
    0xc81a40d440389005034810001d01c10880e65800041f41b0002030300345519100c55124041c1c80380c1007611184291003484c006414503250400c4403001c44e140714a01540110358202183c0340c052105000280900d955800039150581000440c0f080c4015051281d0550405651405041c040000700e0700c07800d401d41c0c4400f00c2403002030f8445600142c8030700700303c4040c00c155416881c0d450101d442000c0c0290000d04e248588065041201404034040040791550749a41100000c049801180c4032003901400c3d800c40704034103500e00801c0e00c07000d090752030b01c0c09402d42d0b5505080060030a500101106400092903000040b0103414444541141070740d140d40603140c00c46251006d1001301411542a2100211904120802154840030085907030120146a0258020300c0743d00300400600050300c403c00c1e13110300e0140000c0103414101b0b15030400250060081012790345200322a5001c9002601623034000106200e00d400242c841e2107020301501e1401d642d140c903480e003403074a000980700e03400c1c00315040c0020805 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 610885116 1250 610883866 610883873
    0x61311010e04110c062d010e04080d0603060e0d08010b0d111b0304170714041a0402030702010b010306050a050a15030e0106060e190e01090b03100c030b2706060f12040b1e04 76
    0x20047c150b6510600d0580261514200342c840c5020368003480050030300d4800b00104001c010f600c440c00b0300c0d4844003503601e0300ca03400c44241c030701000c244540240d07810304012030840300c04160322200740345010170f03059801c1041d0b510f4903800122017030b08000c44a600001d81400840c1d845031001075a40c0884c4018160700c0d0130004000050b40c481c81016003d00d49032110b00030b031180207500c11019410094000c649038503003c0c4c0020b0281aa03000d030342c1d0200307140600101d0749040010048054440140002c0c140d140b50013224a6640d101c07404d4401059910082107600000030b008000c002c118030f541d08143c000d0b000c0108000b00401c4031a80d040c0004a031010840b1039404018181100c0140304001008010140031034180341005040c2400c06c0c0c42d1469152545405600c2405c1410b000e45203003030283d00114076401c20b0701d580c601c0e8600042c00000090214034280c40141800381707130546020300740b04075491290007024042d1001c4a0703004018003001001c822915040040548051034206107040c20f84 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 610886366 1250 610885116 610885201
    0x100e1f0e160206100b0d0b030f0a11042304080703020f0d0302120a0e1b0a0e0906070806150702101b060f0e03070f080306010e060a050c061311010e04110c06 69
    0x1200c0f140151107450383d4aa07641c0520580600a89c00e800b518010119032034981c4112800c4c581040c802c91030048246550244400e510140789604940c01c0300940302d40e01c9860a81e00403602c1102188a00440722134605000c0c807001c0803449542e10301503114a0702c0301c1021000d040040c60020a50711700440140c44020020300340b902c400102006d075111002010119450404981110184070000c80078495141c2002a42503c80c1e041030355031240c00c0c0c03125800c0007031002c4030390180082c18030188110000752504158440b1040e940303003000180d1700c42d071400205052782c01d45004d4842c2e642d9851032140044a034000d0f1801d640601c03010b58600651070f503d52800c0700750b442e0080c04601c00400042c1559004200c00d41e45c60300d00500b49601d400180030010290b6024142030290342c050100401c4510042c003c210f00140c1d404003034100001c0070600110790b54a035940c038076036001d5250140454041500001000d8030700000000d4401032a00051a01400207658640705406180c05642a0801410f4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 610887616 1250 610886366 610886377
    0x5010504050705030601110709020406090e0708072106171606020c15030a090203120c010b0f100c0f12020a0302150121050106050621100e1f0e160206100b 68
    0x3400c0001f00c074151000d040d45031807165040290714501c00100850f009400c020900101c4200003081c0d8036594585004841140090f1415804a08014450088401c1d90b060343c070a43c20022800055a40ea030380c3d901c042807034042600301e4070750700f0034403480c41411002c82c0a48090405800240402d00c0554041459185803601503c00c101000c0007040c1c9030303105c03500f003402842d800404903900c00600c81e0304a0001c2d44198a55040366107020f00500450611900c000d11001000340040001c01c901c8a060b00d03a004040c001310b480d0f6001c0103081000a0300540160750072443c6500900c091b501e140740203803401721005079200b48007542000411100020f074aa084051070100c1030b0084203812443d0440c050005500015801140887c41420810360140b0902c1070460402c0908015107a50340f40000640103030140c007186421103000500025015106c0c032244c0c40e1500800343c002551204a80303005030058903020a443d424100110803203074100403654201ea000002600b60900e440c40030803040c81803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 610888866 1250 610887616 610887619
    0x151501030b010309050a0c08100b0604061125080d050c0d0c150c1e0e03070b220b0306041113060f0507210906090302090a020c0a020a090f050105040507050306 70
    0x40301c641200592081d0001030005900030111034070a0501d15120710542410300403004240302d17800400e00d80c0051400b82c1d0100c10400f8007400d10b4942812021260001c0c075954102083c481c200d04c9440080f090807241c040008aa0384000c900c6003400006400d044040f0f08010400c075060200038640d180c0400c0119400345541860910f002407407818a034103243c4a80300402d5a4074000f01a05842c2e0031111112800302008035580f0302800300310054906000034200140c142d4040203061101403030300f000401c03207803585449900c0403070703e2300d01c203414105220341000e11410404020712403541001c0c029130402c04140b20445003420a030301040384c1c20095a101d14070800800d001e50355900f50080c4111440203400c507401c481200b01c2001c410780d01110103440480051624034000030f03054402c05443c410b49900410030005500c411001d00080c0d00007a50501303c601881c150000146d0710381c1c541c1001049800e0f4081014014140c441c01120130591000d4050f500b884104000d82d9408422203521a40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 610890116 1250 610888866 610888871
    0x7090b040909030c021003061a120a05060103020d0e010b181b031302041d0709020f180a0503191a072c031b090a0e0d0c14010c050c15150103 62
    0x6070f4201118034071002403020b0b41008001448907802c2c1e0703240d00400240c4a5680100144403a011a540309602c5614030b008600c0a410000c1100c000707141d0080758010505140150410150342d0300801200c48051807451503a540e075240340c0b4a0b05100200188003042480c0f80026440c0c00e180003480c0308143c84c1c0c0700d4801e501c0000005c40070600308844000003500079104000000440400c481d031207107295000801032095040004181d910b50080f181b40b401c80058407070070440c2c0001020703590b07a070b0a5a60340d4030407030100012910351010054808a100506041400000c3c90308000d80e544100c0c5c100d0851810149042180744c45e08005003080d8464080c1c1d41000401c170401c090b030102040c2806441c1d05016000d070240c0042800c2c040500c0d0b1140440d080021621140f07000c408403030f40901802c6030b40d00300900000c040c60241b00e0010205001d80c074451728010004008a003180e480301070003004900e001c100c031240400700b00040105140c08000e04280d5091072070848035840101d9115504264 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 610891366 1250 610890116 610890131
    0x80906030703090605010b030f0f0402010509100e03030f03060909010b150711090109232e0b03070c17030709050616060603080904050601021216060b120a03030507090b0409 76
    0x10b20940c010301c000f541285042006503150081486558002e0742d240203110580d9010890340c40598000d10302031581615554900002c01d400c1c480a241d081e0034000038415102d6040c4825101800206003200102c9421540e82c0b501600300a1202c1000e0400000c80c1e1401a4a000644416001060013588143d620341c0790401481c02491440005143c143c1150280e0000500c01c1020380028007091034101c03603100140c00200140324000000c031081500b115411040001412444100c0d10b0086806081907000356190300c051100342e40151048800203008055000900c05e4036040e9400003050000414035509110350010000e51580c00b940744103d00006070300c0c2d15040038428800c1d0040d8801c0040c00314690741d04140c021600501c200a001e64241400240c2a41c408130341c0000400c0f008400741d0400a800002c0c040c002c2c4504070031100c0607551020f05d00c2c1542d80640070a940d4a5040040115204c9850300070140d410241a900503c01e4000090001c1d0803010182c4069030210000050040e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 610892616 1250 610891366 610891381
    0x30303050a0605030d03050a051305060c0f070503180a320102031603030b041b0909020c100501030f060c0e01020322030602120108010e030712033314030a08090603 72
    0x8002c264001903040c403901116200d02c94068001503c00c010280d8100050307075400190303130240880c2010081c01e80d040840004c003400701c1c01000e04011059010868200b2483e90303151072039503000014240b08020703c1c121000311850704030580e8014000507425060361495401a508095184401341039200700c0c0c03000300e1005039100b0030642e060340081c1522084400190b04000d001003114050145c002ca080521801141e10381c21905031407441250b503211944d42c40c0404a2009420103d0140c0302806103001e0720303d12a400340291406507000c0c1c29a04c1c40c562207440d280b01100d242e442c095080c0309003000c03a400170740c0e00401561090102250000038000421f4410392041d81a50030080201c0e10205d500f500212078800998103a5010900800a0040c1207040c59601e025901004002041d20b1400b1000c8030f102c0d4200702c00e82d0304005140e42528a656114144226102c0940d1034032000d15002008a1414900102d124100c10b038090070080c00b01c3d844400b540d1081c2859140600000400308218 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 610893866 1250 610892616 610892621
    0x3130f0b15010e06090108041536030c0f0314040b0a08240f040e010f05090f0115050609030109020406090c021506060403030c031b0c0e070206060a17031606050709060f020304030303050a 82
    0x54007038010412480ac030301c000b2000955448203400c00303040c001d030f800c9500d40504126040f41c40e0140c480544402455a400e8030005072004102d04005008040f91207098030a00500081e205002c8044d841d81d0910000074484c0400a0030f80703800c801e1a02c0000041e0700300c580329821051054030300c1c80c040c8040c440400c0190805840f15982c0b503181c41c039601031700e599580c420f0380110710030310a44054104500400f400c1c0d80500a0802030040800300401c000c1c90680001e10064001900206502120350005021240d940c1d0140134802e45400c0340340171250b414070055040c03180503081c20b144ca040a00200340b5038011404020280b141c407610b01000d060080b460030746007104d600c4128070781407058544131002c28444d20418030141485004502650300102e4014890070000e0301c8004c06d00d242513654104560681c00300800f0380403c0200c60300b08a42004940429805480d0100c0c2c80d040c0340800902c03404090340514204803a41c00c0016080758080110340840b034241ca0040380c00d84681380700400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 610895116 1250 610893866 610893893
    0xa1d090f1b030a060608130c0e06180405010b15120105060a0203070b07020c0a1505220b181206092a0a030303050a11040b09010503130f0b15010e0609010804 69
    0x10382401000700000f000c4950400400c1c0c031020b0392249903030b07120800c1c4151003441c0320000502441c0079032804c0c041d003410340220030f50140000b40308070b0071002000c10041c005981903505545994481c2e40c68005800c281403010401d440441720310749444d80da81c0220008001c1805510310131807000400c03007102403003001a1031030145c01480d060340074101400c002c1c2d84c0e4512074503010b02a010b041000194910381954003407200d01d8544803185070810000c041400d04001d400741360400d20000788045400940703070b405009100c81d201480c5400e000c051007001440081440d007121a40d200400b004800c000205400b0314403102c002c05008901c40b40307900015020070005000340c001d0007a100c00801e041e0300d0340006004a9100008002c0c099400001040c60b00c42c900078444c409004205248455200d000110380c080c680140200c2542c0c00c030343e2001605e44880d503080d549512020300f401728458044074031514002c400d00b4100f58140ca0040803d2203030040d200018180a240c0c0001000d001081c500d110 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 610896366 1250 610895116 610895161
    0x30a0f0606050307030516090b03070315080c0411031b030901090203030a120b181308130807211104111608030108010e0f06150a030f05030a1d090f 65
    0x1000a84800000b020b40d001280c2c00e81c002800c00021400720100c9060342c4640b00c90b659203d4000605010340107045500203016141015560409030a0b0025414850400744c860440680309060b484401c000541e8020410030b0540d0340200207101a4061054883c2e45140651350944c0d12961110080da005141241c00603403d400300143d40b5040e070b41d00c400e0400b400e0034400310400c0909054802e001c0702e41d5000042d40c04400e0400d010500e4030b0031038650404581e1149466500d0b10241c003a00720110b145a41c0040f10652103200c0500158004100380700b901004070b0404a100c1400f91901c0c0b603840d804107600b81c020f9644602350070b440740c0c40b10100c030005d41164407810b07408175051414081c164800d202c1c140c07241d40303401c145604241020a10603c40401000240050303160415804840d240681d241980a030324044d002000030709031619890b500e0301480c0503540310307880000b015100480300d0a012403120444000b980c1c4580d518144550070030041124688640e80d400004038002e8076075071004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 610897616 1250 610896366 610896371
    0x91c0b010b0406030f1b140c0a0506010e010e07090519081e28110103180c09180206070321091506060813060b0307031505070206060f010e06030a0f 65
    0x440c000241c240104111440b0740e43c2044100c00c01003614044480b0f542105c1c2110006480c4003006a10480031440713900c0b01d04925902d4504141c008924107400050200d030701e500070308010448030781e02c4100c07940146043d03070034002d26240950004142040b00e01985104160b0400452005141321003140c0190004408175101c4501c0150b54941d41001800b010700948100a41c403810000308410720040c00d07185003104514007946550f0401078481410403603040690303804213802000d114039080440c2c50b001304501c2d0107440c2403143e40340a0390045080260145102e8010f9001600c2d1001154122501850100303101c03400c90440c20140c5902c80300981c0741c5424400143e09001e282112541c460100420400c192942c424099400c880202c841036181460040c14801180580d01b15111100c40103042d20b90031922070b51040c1600c0300ca0301c5c2c0f00e61440ea9850421104036010019075410080881c0d11009010311031000a00820a010348a400360002101060008916410580c09501c000006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 610898866 1250 610897616 610897619
    0x60102070635010e041719210203040f030f020a080307084b040f12170f01051e09071808190c06050708030a0c0e0307170f12091c0b01 59
    0xc03c18440c609445c1510034010f030a84082c0d00c00d83d8038040301e183c07619a052640f0031840118050390340740194904440c00314140109201001c039984010b40c4103a01c208502c269560143c01c0090103007091140300d400350360060074400c011465071800d60b0f601c54840d1810030120382d11140383ca8081135100724290441c84ca200d0b480e2406c462108668509514480da40b501d04041040016582100685020f840e40d40c200407003001040c511124080101840d00705807894840490046620600c2110145d402180f140d006020501d030040c10022400103403000d400d0308019001c0003454408000d052007040c01030704c80c80c100d0006c0004400200070000801a1a81c0c0340f52b5101582c801c4030300707010840d0035045074600400c8803806042900e02c82604541a13600b55a541c044210080c81d003225050103100c0e8802c2414015901000480d003d0144500051000004100118900742d074840b03c09466800505565044111440036680490b10403540c0445488440282c0f0070607040081d0003074000d0308007100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 610900116 1250 610898866 610898879
    0x60c110a0b0a0e1b10050705070306020d05010b1e0c0c0a1205060112033f0603050c06180409030e15030f0c0f0d0c050d1d0606010207063501 62
    0x200c031481000400020320041c080b00302e003c0d4480c5194600c00c041c0300790100c018911800c04203102d010204040c00c01601d045166140c5515060069001f240c0980d00001d45540d600c805024107401803241104da2814918995080101d0481c20001c10012881c0420440310492080001c00c0c07050038050302c4004160788034041c16024100300c14064a043c410f0714000200000559403001c50a500341d0b84640c80b14000d014404c480d085040c4900540d01070031807d14020404500302c5a100c081001c4000402919615149040200d1000c45030310440d01401000300c103504c90300900002e01011200020721080351b241c180c803a424000c1c030303083c0c012411201c03003041e0b07044e0080118040c1c010103100080d541d407012074056a610424000260008080c03250103e4442c041c0c00100d6807080c035060403400e180b02510113404940d03500350326151007031a00015500303031007060001c130b60056000c1c80a80007050900c00d010307040c2404c800110b41500049080e0101078006031000da0100e1441c0f80a242d2556034559 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 610901366 1250 610900116 610900133
    0x80d0f050402040e0c0a0b1305041a01021614040207020301060305010e061008030f0a050a020c1306030c0e010506042309130302161a0c030705060c0a09170307060c110a 74
    0x12002ca000d0707031070a04e0050340440700082c01242114020b0050b88882d060400350000741d002015590311740781c000d41d03004c039036a03503a801480100024100000c100074100000203240685045045e4001c0003140000e016881d0306920f1040c06520030369003d1781d80d40c500d201280c0140030aa001601035460606900c0c5034800101f50356008000d80000c602003140c8072a0070644910443c1e86030444140200720b20350080c5d008202500c0c01280a0059030301e04090140800d45014a00d001030115550303c05050080005180c400d101030010f0380710415071076060034085405d40c4150b0007811020b40c400f400018210f440c0e007072228201100904402024285050000079400401c2011809401110030328020082c120f41080c08030b6200e5489940c56a0702e40f21414816407010400000318002005014081107080100d0741c050013451054568070004030200802080c07440d041865070300200316a000c0800c0c400816a04c5454200000207104001c00000343c44076140c444286c4080d01942c031a8000b84160308 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 610902616 1250 610901366 610901371
    0xd0c05090a0b01050306011b020d031e0e0a03110613030b0103110d0f060e030906030907090507090311010305070e040c0306091d0a0803070201090b13021503040f0f080d0f05 76
    0xd6665100d1074440324400c10a8549101c101c0b4006070b024000903082d50310910222600c0c803842419110100300b541c0100b0151a00d85d00240d000c5500c00e0250320300400c0f124440d103120444d9180105084d031013000000d555841030321000d800394110701d00c0403581d0b0341c4241c1210707111010f90304406112070b92403806401c116024802515040060340780750020741400500054440d0b4015540c4004c0c000b1980c61000a265030f940d01802440140301c0c0c06410380b0340e08015405200003d0052000714504a10070003a520000c229408000303d840781040003906078411200120350034240442c0b25902c0e0f5404031585035400e01c410703600604014001103420f4140c0c0c0400d0503180007ca084c81a0100f80e40ac0d504482e030003941803551548030202c0000031948060245401c41c07540e100126070503105482c0c080500c80242c2d416640c95021052000840ca0f081c048218194820740c4c3c21811454141c640458034080700384082e11b14600424440c003004110300480b5005020311504001090f07a001c0e0103002801304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 610903866 1250 610902616 610902619
    0x9110d0c0f050406050603040b090f030c010b04110703120b0102010b0a0605070b0109180605041506030311062d09010908040909031404050901120503090312030702010c03151707050d0c05 82
    0x400d01c02140c0b03420140207100903202c002d1b081c0792458549039174000b00960010300d2032125004108a80584d41c905000403e00014103400118000e1900303810002100c00071042c1d440b4800007003010070006030b003020800000d2099482d002880c03100240060740901100f01c5030942c440320300d04010a1031500f00e4094001a40070b0405a14036a032210181d20403142c0078100c100c0300c0f192202d20720001966981119074414030928100307600035030900011066640329003048000c181c01d04203c02c0300000400841c1e5010440d10702c40740040400c4000c10b031440c0e410303035001104038201d407000800041e02504070050881d40034080c1c0f59155915011000140170340c8038100e000410100090fa40c0d04140810303141030362402001024980d18040303000c4c88103202103404580900051080130155030b420b010105d4400740c00d05420340d5034649214000e00312481c01c0440030502d8681030340d0f078110f400301a8072a015243c18552111400004002c56403900b00158801540002e542e0804410000e0028190084800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 610905116 1250 610903866 610903889
    0x60a0f050603070b0d0c03090b161106060f2106010f090c03110307030203060a0308161515050609040905070b070c052b020a050d0b06011803020a050409110d0c 70
    0x26241e04141d2206402c1c0f00718150128280048051081c1950184103400c400d810000340b10f48150340c0d03103229900c084841c100b19161880c82d80f0741f990b8001d9004c4480d10b08003805003000d03162580c00500c0341581440d41030300540011070000240d070032460a04110b203da801c00c684183d0703558905044202d02d5400313070070303201401c2a24294609029000320316420b68000305141c00c5540740c00c4110f0003500014840e642c1300851090010210f02d40000410a0b12513140d40303606081e00f2400c010400c03c21505130809480e2504c0f890401c658502000881074810445034150742e6480c8030b00040c01391064420103485400740520010b0045084002408110701c140c11414003190344200300300340748400c5044085000514241900404203000204103168402402c030f42c040c0d0785403400704204082c2d420303089441d00d901d0760601071250b8020a119070b141c04102d0311a60001c3c01e40c0e0101d00d00d1342092081c0380c0a103454004034010095a400184440c0f000548110030900081c28526402000e40c03165090009 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 610906366 1250 610905116 610905121
    0x1302130e0c0a0305100b0d0c08010903140c190516120b010b0403050601062321090d020c0f04060909030c17040b0703051303053c0c060c0106030203060a0f05 69
    0x81010741d8034100e9804c200a04409142c00c44000080c0c0024022158004e90b04002e10380045c0400580c4006000170700e00010342d01d40c00d460043c04855404038020307842d290500058800f200005000200f030f0f00c510220402c5650180383c40e41c50661a05114110b805091902250060441c403000341c3e801c2c003400205a0b40d076603a01c400c0c0b84c680300398080501240c002c0d400620134680103600105c0c0c3d28540c0541070b400443c003041003a10a8000b10320200680c0110800e03100c0000e1110300b0503070010106000740c64147e41400010303540d80c5072034440a0203441518079481e0309903207941c0402c004248205081c40308111500e802044031852103012100c0f65900707040a50504113170415202501d04d0071103032074030f869080d407010b41e02034100f4a580032514500f0703407021000950074000b100d00060070054807803c1121005002100301e0068500c45610080c441e001d01064400080d2150012030581c0c1d0a0b5850f03c030f00c0b0300d55016210a80002e9010700c104024482001c110b0f6003d00b0003880100c504000e1034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 610907616 1250 610906366 610906369
    0xf0302150a0221040f02151207030608060a0b010207091d07080606090a1401060c08270102010b030c0a060302090612041101030b09250e090c07141f051302130e0c 71
    0xf0311090b100545920a08aa0200103040695844421902100b500c81c01d1100a041d121b101003011660340000030f4542c8402c0101001c100300d40c0d84c000d10402c1003804408010030000f540e4003040d120308048036440300c1e40b1801203002d080d606081008140103031000b8503150200705903102d00c140c0b030850040100c8030000d9076044052040246404101100140c164a0981d08680148400c50300b03541c1444200058078501c803140c0c402c40d0546a13121420591901c00100180c01c44000e525854002d40100c0d20b10400f954512240000b61132803402c0058680d240700c00072428602904521609a84d0b40d44140001d10051079280c0c440030702c00340d80502c0603075050014041c02030010344020081ca44040824100340c6041600c00d200300e00b0a00c0d00300e42405101000450014040d00d610815100c002183d109004c0d6003000c09501c0b10b220401420149150340c28074600c141403e081c00d030f41f2035403500440c0e10302071040340c020701031a00102007250b074050381109000244040c51010070395100e55840001103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 610908866 1250 610907616 610907677
    0x5011a0c1504020111030a080412020d02070b07170307032c030a0c150c08010801050703061802090301060b0d050f0907060e120a02150406090e010f030f0302150a02 72
    0x4000d02409007081c180007200c400c0107180c0260049061200f90310070074004560400250646140700d580381035031410300c1c0c18001c1288810222403400c5400100700b0b00c00607900041c107403044034040492030b80e40e03841c0e80c201260701800380d00c481c42d0481c200009218030107905d43c01c010b0031480f04143c03000c0c4001075000e000303e80c40540c034155826030300305000d170b00310f090300a02c1a5001c06010307501401c1c07600e100c45d002c0302c2100c09078840680810440c0c00103100b44c1e0024800e15030f100905040030040ca900303017142000c001248680c8012610340001e00e4801d103490a4204500520680040c0e42d12440c1c003c5109000c0c100031a020002c8038140800540706000004001c422030380681c4548040040010502440414420245a0300e100709101100141ca4422021070803000e00c100e560b84650400070020040444d41e800007032040c2142c40180134003030554400000700c9601003036640c008078880c0b8080c2e040000c0f0780e80140750300348010104502492690014000b9540110018100f0700890040185 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 610910116 1250 610908866 610908877
    0x5121c090b04081b07090c0806040509120c07030b0a06031209030308070e1f0806030f120405130e0105070905280308031b070521070f0b06190905011a 66
    0x1007080701c401007004580c05100a040c2c0e20038522006400001030300510380307071501640c456460f69030741303000454085a1202d11240c201c4012901440981040700c2c90590303561031810100c0303103080000760100e00d90b20104842802141d00650101c11454881d641500070318007884281c66000c241208100114891122b003c00d0301d0741134440040e00e0300d410b51704480500310328140d00d0f0003000403820074003c0c41c0b172000d0500e901400d650394808a441c02c0c005041c100a210016140a98015818220100030600c1175400303644045c0c555911800f140c14001c009080f40b802110115407814050054090b03101e40c3d0001991001da40400c030101012187c1c8058020104000b58241e24076402400025046001560007103240b800b039802080031116215969404070700101d45590207801c01c0c04004181007441d6000b036800b840b21500b09082500d47c10703040c0d04110402808540c40c080007480301e5403540403a10183c0300170319140b25459218031019005250a00404035041c0075040c0c1a0a0038041004880 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 610911366 1250 610910116 610910123
    0xe06220509013c0c1211041e0305060705030408040e04150e071a0f04030b150406140f0111160308040e0a021e0c0309060705010c0306060f0906140705121c09 69
    0xf0070043c1c1c202881c00051060295042c10009611000d11180070036010700340e09100c1955110303503114600751440300d10444030008039501501c0302008201054000c81d00e154080d8050074015943d40d5146000256446550006854a0141030a101c18001d404944c05180c40c00140104003002104400c0b41d6110202e10a0f0768400b41c503c14010542c1d2010b00c0944024003410349180d04050310707662041d019031012030700d814010000300003026031440d050042e08014900942c2d5000040f820340003045e00c41c00f44082440c1802546007442500d0710f4200843e0070f80340304400400034905d031a40342000b40742e171040c4600000c4401c940c002c42c2c07020b1464401ca1341c0e4054118140d60390100c000b580c42059800a2390b03440300c0b501051104c20115201c040040037810310640001540082c0084050101c400341d4100c0b130100303c2c4200901c1d0046400c1300b001300c25508181000e507001071421041e0780f024402d09500500c0e600644907030b010004501e00280a04802801c004480100144031407001c03242000b0014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 610912616 1250 610911366 610911461
    0x20d08092e05070c0b030705190c020904140f0d020c03010e010608060105090a0608030f0a110d090b130302041b0207060c02150313060e0d0306090203010e0622050901 73
    0x1d41140c0604003c10325144140490404c141c1e0b05d0744115095001100d49a020a40001d4034100a192101d451851030005003400e201003c03203900482c030440e400800041c16400711120341d00041004010026414803c40202d444551000500a4807070b045000902e01a6080800520101d00c3c1801040181c40c4148000c0c83c1aa1902003001541e55001d04003a84403030382c8a001040c071140910040c0b802400040517036a4802e001034000b0300c48114004c41c10341d290071034241e10954030380c0120a40100d0300d842550b40e40360b084101c04c2d07603c141c100340d20083d030007864010740100344000741804001c0310506400391205d55544035015a0408a4140002d60142d05d620302c013070329440343c0000345800c00f400c903c3d064010f500e90341c0e400341114050110f4204c694494611540c40c1c1c1e905000b61405048498004e605552506115040c260b00c00f4141c10b210f02d85a0f1866a588424100c0c070101400da000418405800d00300c0d07010780207007104000700b05085030060042d040100c0d07070010f8460507061410351 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 610913866 1250 610912616 610912699
    0xf050114031e0c0c0d084c0b070f020f03060705070f1a0403120e03180f2d040b10080f09100e15090c09040b0601030207020d0809 57
    0x42e040c4110005000c6003c03550305209644d01050100300117514040503480d4082241848080171340c400b220b480718130301d11403040301c2c0d050031400030b103002030107101242042c1d240162648503010300c2e5031440380c108001040020400009000080c404044920300a031141040080c1e51800e240e1900c004494810208104210400000307100180c540f09940c0110024141100e50000c02e0003001c80a950940c00101c5900c039440301948036209075407440b03801400540c0340400ba8101210354042d1707603000501c50409c540c00d400305511032203800070703400c040d01541a0410420308100e0030249120804a80240c0c94071541020500702042c11940300c0c08070f920355a0041c0da5106440c0c024000007000e0510a0060655034814007840b03000300c0200d00400000b80820318a054080000250002d01070207583e484038030150312a484501c0c0d40c98100b0341200145605a4403400181c02034440c0050003500082142c0d204000d01110f0006801d00010451310907016040e013001c070948a400c124603291522000d000e1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 610915116 1250 610913866 610913911
    0x80115030c15090b0903010b0913050f070609050d0809120d0201050601090e13060f0c05070308090601260106080d090e0a050c0301090c0c020402030109050610020708030405090405010e06010f05011403 88
    0x107841d91010046c0049411440600031480c20082a80d41d000070038100c604410800100744100300000200c8030060040300c0c0f400304002d01d030f660507102d03103401803100040c1ca10901030402c0854a511201614822404079a061150380e2210144070a40040d440c0c000482c1c040e610460654080b9942030030300420310340300c0f0050441c001240c80c40481d501a56004140d0524015008e0f80e07420700e07060b85070a51280d2040c2800f03000041e00408065040e0030040061107004115603a03403a6050b20301500b5460105d28448050050600d90400046440394845030200d083c3d0183c65041600c0a81407001c4007a11800c1501090b00c9042d03c1c5080e10800a000500c82c50900d03030320074003600000c1d20749201003000031380110301241d00a070090b4014a86684c01c201040c1070511140c0100015403006103130711480e040354180c40340180c0c0641d504c203a03c20340c081410701030250400030541e400542950003950350b44021401c1d8003d01d102d028085160f5401c881907111501d010349102c0c44111450302c0d11903c1418 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 610916366 1250 610915116 610915139
    0x7090e010f3003091401080c071e1a01090c0c0507150201150e102c0403090801050a0b03010605060403021f09120f051504120f0504080115030c1509 65
    0x1020b45494000040c40d001400d501501ca51440300d010381c5620414508241e103080035840d0740b51441c0d0502000c03005010307081405a080380c001e543c00c2005081042031510013103403c1e0008000c042e060900000800925030120b00205040f2104040104042002c41805488040c1c60480c0540325800c82c1c6020084101080d28000111034548000203e0302852020645d8071615074100101841141080169103800641c4501c06081c80000d4505806851017a40080070b012904090009105901180030540602599805800820000d1010f0b1628210100040400c1d4106911035801c10000080c02e00342a0226400c0c0d03600a4031300b50204c0010f80b02200c10302c1d0000551010040400c1001900148400e03080446600c0b41010890f56501b900b001d61400c1e28951180300720702d1400d02070000042c401000250885243d00f010070410b2812181680d00c1d02595004c0906542011812515a81200c10110a4134455441c001103503449648610380e0001010050300400d006120500142e00d102d07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 610917616 1250 610916366 610916399
    0x10504050606070311010f020406020102040306110403170915030c030603010b1504170319020706081b0405010c0f020a06020726070513090609060204030221031803070e04080307090e010f 82
    0xa07000070520a01f02d4610408903071040e80300b6001070358003040600c20020703a40200d042c441503114107642070a0464075000760b0001005101040b41900040050158482c0101084884d41c40e4860701d45a184c4601c140d1501da004035083e40c440c0d40303400aa420a0325040600140113a80c49109a05140c1000d5000c0c5002c2100b40b4016540d1009021440044100040051a03500c0302d41c09813402a10305440640380b0385019060700c0140c5500d00c1d005110358400c4080e5011141d00340f030b000b10b50001508040c801001651000f94008203102800f2410f2600014010211042c040d408500718001101581e04070780415031030b00b840e801c400320820562a080c040c0c24080c40f803810307001641c60000d9840c04221303120351104454a0fa0089820019880d1845d143e20788a024004c044100603c105072a80c3c07170744609090034034064898540d40f1029142002080083c0c48001c8000c1c2803801c0c00c0c00d080607940c00c00c0703d10600107424a200440c600442070036841c1203580715440c00801c4c1e401c10b801501c0c1c0d0f8461 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 610918866 1250 610917616 610917647
    0xa0506061e12010c090806010311012f0115060203070c06080603150915070309120f1103030103201c030818060a09061d12091503010b0c060105040506060703 69
    0x711001400701c0d0b07075440d207000c008007000000284660f8000405844078000b40d0101400d504888010000b15020212400c1350210074688080b05048110741c2480064000e40a0400641040d800c0340f00d03c4415800b291840c2031000340341c003c1e1030340e62800f00e0b41d92180c01e4004044038001c840410a0764007070284103402503001000c1d079010404004100805070b00444030f108032507014041d1003030086c0981c103000b40c00010354070f0709116081940e250704030442d0039020781340200440300c40001c450754445c0441e98900318410307040d2642d0396503a003810816440c3d0f02c8a5070f000030f00c000c4041c000c039181c259140090380450203141c400d040320507102a120398138010040c2e8540d21091501700c40d01c0c0c805200b040d00c13580c01d5400000755404039080c5201210380a0159131032095400031051513186002560b0b40c8090042900b1a5a482d85200400c0c401740b1486e161400241c00440003007030500411010380310a180c0c450413a011070b85d89204010a8520a43d000d40c1c00c880f00f008081c0c0428818400840501103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 610920116 1250 610918866 610918909
    0x702061b0a050102040617010806070e01030e120c010b0a0806040308071205090105071403100b0702030c15030a050c090916030b09070918050108030406050d0e031803010c020a050606 80
    0x9140000742442051107086a85940c00501071040580048065900c400340c002411401e42c1401034035a0394590152141050049020f0030300250fa02c41c1c0c10a02148050200780da0080c1088040c003a55500701d04808001942020768003c406e00f01039807480d00f26000c1c1c400620590300d0320f4a0654a0704400303444282082820760011810f0202805420f014108000000520303103000700004007a80700846100102c89810020301035000401c0c0d00340010341d052113810b0f03581c0c0c14103480028607040c2e4014a5a801c040c2c1444261070303c555038005144620743c4140d00340240c2d43d52048116141c4680020a64480e0341c082c085a0840354100c4240e044c03580ca070400048001803000000c07900c0d142211000001184054213000c0f07d07016a000700d001032103c01d01480076505220583c0d84a01480c0140e5041000c00f01d42a0701c0c00400360046002811401c2c10350f0382da1003a002c800d0103070f50100707820140258284ae0800101c0e5100203481c10b070304d941150241005448805c204900300d81c0b0814405100b14 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 610921366 1250 610920116 610920157
    0x50c120726040b070305090d1404090c0305011502030703080115030216140f0c0a031101021006080604141b0418060f090b06100210050a140720030a05070206 69
    0x8021421190768200d800c050721440c609454003207407000004000c00c00300350510040c481c00c00000502610300c0c0e445400c0102105003c00c01c0b81b03007240542da002032009070810318800ea507180c142c0d1005c1c3c141c59104a450a0510604206a949206101004002a0041c1b004220700485c404221411101514025181404160162404074030038031080d1440e1500f9403994921400030807000c072140c14000b028102602001c40028450300c014030010302452241a4152190380c030034403d5034400c0c1401c000410015488440b85a6036030f408481c05c44492622108041c1841c030000b40810b04500901200300071040107005001c09081003c0c00c5800e00c0c680000c0e17480000b58075004101003640c01d02400034144819041c2a0a490800b4121502541800d25042b02182c0e0209198403d0828100082110303145d0540800040070b5a4202d400c8800246050000d0264400052411080c0b04020140d0205550044d96220304c1b88528040c003041040140000500740035000e031040c0c2c950070540c43d810300c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 610922616 1250 610921366 610921397
    0x7050a050c01140708062209050a0209010f0e0604020325020c0a08060a05060405070903060510030f0506061008161805040c0504081006060c03030f110a170a050c1207 73
    0x49020f1062100340180c04803c102c0d686900c03034101c13984541c049400200000c811801000c1c8402c0044400e07960540f6080044e041c4582089a400e1080c0d020344040006e6030741d0714a01d0180c01c1c045c0143c000316103040010681030301d818000c1c0c0780248426024001343e0302100c0300c0084402c800c04215000d50046d01190101a511307489440c00070304800c406042c240c03501d003180d141143c00c0100035910940c40c1c10180306603a5071007040030302600c1d070159001842c3d884a05081e00102c1e101d80c4000c0182004401c240c0410a01140c4036001e0201900e0b59401003410300c50540c0e0713204e011900390035030f0100c80507001c03280f41c8500c107070b4400c41e203280203240440e03900c650100342501d03003100a803404943d0014003040b11070000c01000b00d2918252008005090405000034120340b807050014080640700d003d4403003084503a510031100d100340041020b6541e62a084068900c0c650b0300e0300c002c00c0d55000000100b0340310046c01130a1080c00c4001c071280c60841d08411500d5809406030100303040051945411000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 610923866 1250 610922616 610922621
    0xc0e1305040f08040f0503070801060605071218030809010e0f0f060702040f0203010b04030c09050f15120a030807120501030c1716090f1a01090e0c070b160207080a0b07050a050c01 79
    0xd40b03a00031210000034201001d0620300b508c0c982c4250904e030b02d402400c10510b644001074a203201c2d8045400e8280f03034821201203814003210030103800b00301502c41c030000400c0350041c010942000700382c80d00101c00741c40b4401c20113614400b00c603440d041281c519008805160401c0100045840240000ba00140141320380c0200d0700300b60800040720340000b50510500402d80b80c450020244081c0920891505081e04090f2503000b030501908060b44000180c0a41e440c02c2098981403500d5048a143c0c08142c04c008203200d034251032841c0401c0c03c40301000c420b0184e5004803410b8a40102011031028038200d4400c2880c04400307054409401071285812403618143c500300001c10346044085180c1600c540d080e8201c2e820a031044c80d00461456100307400381d80000c1c042c0c0881d80c0041c0c80c50516604c032500000c0300c1c422441c000f00311070f106d0340801c640b4145030324000c0e02c0180181c3c2111255600e6011941d40e0b40318001c0e01030f2803000607800140d00300c1e101c0d0004140054035460414108094124024207 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 610925116 1250 610923866 610923869
    0x1020f10060503120c030406050708041206151205031207030b10080106031a09060d050c030a14010501090c1205041b06020d0314010f05060310031b08010c0e1305040f0804 75
    0xc1920780100304000c3c60200300304454044070542c0f0928061000b209256a0310840c8a800248100800c0241c14005800300780c50041682c44982d240c000050f2511400030505512440c0150f1080000800e40000e6946854400e030f0b4064015407a01454035640030310760714028424410076846041554054452028140007407805407518501d55040c094007900b5070b0040c07844040102170380da1008915a94521392a034102800f41e41100138040a418518241080e03400c0b401c0c1c251040d010705804008000710740c20414061a802006103980b0b51180005651950418a000885690f08083d03080490380c0100c2d0004e1041003980006078009000904d403017603070360010000da00104101b50700c051b00b502407800741c2c0ca2030950a41e0a076051441d00d03c004030b61401002e0164030f0200000380c1808002d004000910341007024460071000002d0305054408560040411a50920154100c500d004202c5400803050040004c1f181d146030424030390003004000c00640340c400aa506c0c84002c00c0c3c52400400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 610926366 1250 610925116 610925143
    0x40605040c09090b010f1e12020310050f09010b070308101a090405090715050d140a0e100903080406090312050a020306010201390203270a0b0c07031101020f 69
    0xc0780c40d03c0d0004501c00c44400803a0300b07041c80001c51030380308055800a00b1103504001d81580d5010109400800c540c24444050050641403002042c0005051190220303c12164100d030030440d001c008405224108070700b8030600c0300158050001d04000ba0103000302641c0310042c9548540c00b17070341c2d8016440525215000c1900d41440005108910b4103060141c1544030700b900009020151520b01c4400e10000143d94110403c41c000c0303003851640ba0150041100ba9100144d03103446420500c100c1d200802000038a03440d5449020300055010901d400307001c240743d40607164034000c0d6485403078550180c007490004a0030411040941280013500e0310070140a18003031740c00141c03280303041800607086405500110240c035030240700708501c2e560a600341c10340341000c4014000c01c012110300d0a0b8518003482c002c1640400c502023120003031860490780d4207240d40307049516005203a600c07101c1c0100d52240308600a000e400414003071020407400140d0480106041c411903000346c81c034910083c10407081840c204c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 610927616 1250 610926366 610926377
    0xb06070f200f010f0e04060e160f020f07090b041b030b0a090902150a020c03030d0e07120831030501020d050106020c060a0c11040903050306091006020c040209040605040c 75
    0x5603206000307901c1c440d01810042c1d41c5041424854800603080021201c00c0da4104902c000080c1030340d8999030040070042200031808030a906100c00e01d2102894411181000503aa192803c01000c1c40054071980c0d031840c060241c0141c908105501c0c01512051040540250b107614400c4c048040c081d0308901c0d0b10200765000902c51980804000c00380070298401298181440c60900144c0e44440e0341440f82d15184094590b514030301e020681c01c0c0313410050026414000410081c0c00c02c070440e084200728420613002d680d1005c0d26001c00300048130802c84007800c0b40d1014001180d41e0980510b141d02c5601c0703060046600c0415200b1081d4000c0c40c0742c1c1046403281d40204501e002d10045000d100e0140010340003500741c00304540041a03440c09000034200810100b11160740038803200e4070071412140070151007031050407018240036143e80d00907140e450081c5550300000d862a400d08002206076a4a503015183e18020102040060341001c0310499006548100000f9103983c0c521840303000500e142c0342d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 610928866 1250 610927616 610927643
    0x15090b0d0e0c01020c03100e1e0f07061b060207050724031503030c0b07090b0f071b180c050c01060e06010207090b100318150e0d030608030406030b06070f 68
    0x1c1505220b00c03400c80d00d06541c0b0202c003100707950364081030703c00341400000800070789090b1951500380307031081c50106410446100d940041e0b007440080b502540c4040381c04101c4030b005944110880304c407442030460714265100004050001586030b0001c008090082080390002610b0b02801c517000d42044410b0200d000791000e0b1880c1007909401410000481c59500c3c6940901d5914040d00001002c64000c25815504001612882c0502024405880c1341c84660351100c3c251501c26003154013450064814141075542c1305041d4892885040943e0380c9114040442d032800046940039014003880300b4207000b018080c00d003110409102d4a801400504201ca4403410030000290801d8995040340c81d205003001082151a262010303607040d20200c918002515004c20110310350b0440004000038051824080c0d140e0554030b0f550451a000c180500a541c0d4206c050300d0180c00702c418900c114245500244020070000e406540070b4081c03800060700e0b10b0700c0c2c000141d0740c000e4140130500302101e070071810003130 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 610930116 1250 610928866 610928891
    0x6060e10090506060f070f050d2309131505090f04030f1b020d060b1c020120071a130e0a0501170307060f0608030703110c180115090b0d 60
    0x10303403000400164034200800c0c108140491058403680c4804a038116000031210304000b040105072021ba80c0280594580e2502d000c0010210641c50429141100080c1c03d0924569040c20848408034001011820b118480208090290101b03d807845030301100725034001041d40326440b025101702c40401000d0341c83c1c5030a01d805081404c41c1d031150010030105034166891040b40c142104802601141c00c4009281c1c14500f2001408601c40d01c0e6801c20084420004044020100f2291042c403d0701da03035814510450030141c08c02200e4466a620398040c10003041894010040000e00c40052550107291aa000d241501410300c164407226446d041e070070401000c500184902e078054903202d061110740070800d142c5590741c2c1c040c011000c1c160071780d2042045094000c030352007a80100050800d80307488018034200505540c0f001981189180225606542e2500e402c01c1c00e5945980c5819007551964200200020311140c1c640d5080f051024550300410040c2c2c1c9c900144c00a4800c2ca88041440b048550 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 610931366 1250 610930116 610930141
    0x30703050913181b090615140f070f080d1b08090a080d151a0a0801050d0209010303050a02151315090503040501030b0a0308041401180501051204050a06060e 69
    0x9904002e900d05651034a80c1030f5405a805105600005450481c441d09480003055030b42d0355001050243c03402000064401081540c40d4011281e40c071404440c1d900740c40d054845108030a081c048080d0304000e400000b5074001c80501e2141d0041c00207900301503500520100700c503442601841040740c40c08440c602c0c1c607401448035500c22150703006442401195904c60283d401203050008440303440b2200c5100e9040b02d0407482d002441040e40802c40001c0d401d055540c3c540c0a504540c000500c1e0f0b500214445c185162502840340d4040d120003024ac0c6580c40c1140d10350031120445085010b068640c180110000c04034038000c2520007800c607640c03480f903d050f000080012115104585c10507942e11301059001c0103407403c440d02800d0208041507184c0000d8035980840c0c00080041f0000f103000b103034203002070300c2c1024600400e803120703110940081c42140010790207104003400030700f0130032500e0203036400704514940051040044500b90030440e541c020556400d60031040ca0208941c0c100320a200015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 610932616 1250 610931366 610931389
    0x6060f040c121515050c0604030804020301090210230301180b0d0813210201020c0907111e0105010f150c080c0118020f100c0b07140c010606090b0a0c020103090203010e0307030509 79
    0x17400d20a1510010946998441c0750080000d42031142d00000102552029044a0b045590003401c820703d20342603003006800002a003801072004c9510b0204082d102030340e0750441e4141c44682290309a84401440400b000d08600c20003680c2140c00c00344900b0009281074041c0c424482089108c28043e402c01885200d40e0807002018035851044005020150b60045110716604000b039036601455903400c002038644010302e1413841d9851281165410624102c0601d41a005100d034000f1f0110f030341c3c1d58603160084540b82c0140d010303165041801c192418000c80ea6511100e105807801420804021461421903c0400001440800340c40c04d201c11490001c00e5a01c81c940215100c00c1507400c0100c3c024526150654000c003402003840c0032811650150900201c005081a4659505c0c124408502d0103010766103d0303000403480c000340109569804000b0381e07034030303a04603612031060f824180c0046002e0070302400143e07055542e4208095042030140020150700d8001e0326250390382d40700d8000740030740c40410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 610933866 1250 610932616 610932659
    0x30c0708010e1908090f0123120105030a1a0a0f0f0506041416050c0312010f1404050114100e1c021c03050702010507051006170d0206060f040c1215 65
    0x800070f06030015480c04151111103006981c0c80400420460060b500c4a1022800403a50310b0080c00300442c81492100508200044080c60421a607031141410b0340c611800d0300040c406041504484019401c0d100d06560060304010089401d1000403000c404403541c2c02800c050061b00e40b000c00201d13040c40d0080f90441000f143c2c0b10380389490240c44517401e00000384c50040c1000f50000c0c00c0c6017048810070a689014290f80091b02c80c959441c004044060102c1c881c1456001e001500c8062600e024031600741241c4084c55500c2030010460b007000b080c0c40c040b00042c000c0c04604800007001d6200c1414070850304001c0c28110540035220f0040100801008448240742082d41c8203500000790322038152111a682801c1c16500d9101d03074030306030342441c2840382c000c1c3c42c8900e0200001041c01420490000c0f00c2070303060644e6070060070040d080341c4414044402e05d4100c0300045075a4040d0800c1ea01c01e0b10040103500c3e214030075104102008046d81c07058501071503660880b290034441e8901c1141c0d00e036021102c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 610935116 1250 610933866 610933903
    0x60b0a260c10050c120c0105060306010b13150c0f05030307030b060403020f040908070807030c02130b01080705033112022e0e01020a03050a0c0903030806090702030c0708010e 77
    0x1402001800b600c041c0c41a0408001001c41d01d80c0c104502003000c1a091140226015118a25008403500901086500d20311a201700000043e680541c00d0446808140c0541c0b40c030407041c1400c50002044203c0c2110804115034186010040b0300201915034902d03105801855807400c1c06040107050352159002c2a114a1003000104010b0707684001031801500280c3e40402c4003e09802c01a050f8000e200c80500318010000304941015406501404080c1c42103400500310754003403201d28202c404004005020492030408114401d0180e80038541c130508814988500009014420100810384400040ca54015250140420840c100c0788038100203a0310090a000c002c41210010240d50503200700341c06030288111041d00102504191060b170a031100075595030300c0f6040020300921089400d400640cbc0383c0104556001d00c60104502165050f542e100790a840300403c1008152010f44071906510042002080482080c4a100c1c02098a0000018040d40f8043d1840c03c100b100d4100014102 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 610936366 1250 610935116 610935133
    0x911011809050c070f080d05010605070206120c0c0106140901060f020d03020702190e0601030e010e030703050c10180b0a1803030e01060f0f0f12031407060b0a26 71
    0xc400c40000303044507644200440e00c0e4542102d425210b2107044805000129120a240103020300040101081c00141200300034a070398801084549010f2000000d42c401c008002500c41010582c40e280d0300080107003000c40c6009640000d1034219584d0b540f1040c0340c4407400c0121841c0c2d242100d80240101024203024921494400c00291114200341800c42495400714591042d5141d00c4203c8022116200070002040d4580b41824241e8104940580c0024144405216146010700820016070002c03001036041c012140c0d0305440b075130024040c1c20200e22440c00d20040407501800752442581801c0c0010480610a00381484a80d10091042111905100504621004894009014541526000640b1881c80c20b6141c09003880c0c2d40180b02403800038101040001e101c844072002c50321291041d105072903661480111070180310364040c01082c08184281d000140030001800c88504c030b0319000801c0014100094601e180ea500880d110541208929914041c01c2420380146c041410050038006c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 610937616 1250 610936366 610936397
    0x1050105090c030f070e040504080c1011180d02030304090516030504200d060c08090d08060a050118080106240206040b0615091309110a1410120e01091101 68
    0xd10000e00440a841c13014400656107521642841480020080080c0302170704060a004507550004261002e031400344507040503100b2014800e5807a007003031400409007000e607020748242d2500303907502a59800074841c1382a040180c1c2c00f403006201401f01c480001841c2d05003400581d80e503030440103440c0300303051a0500b448041904481d041c80c003040c40d03444102084240302e01052542590801c02031a0301d050a0582800c05d42004150b44a540340000721030101b80c81030300c200c42c82c40054a0180d041042d00b4014080c41d48241c0031170092895207540d03143c1040e50382d070800c1d003142c1466110740303034446c40340031240b030400401c0c410910108002c0c4001e0815007001d840f1140720420150103030b4402e64100e041c100903003907110203840303042e071780100130826003a5080169005040280d800316001000c55000d200185024406581615007402c9088207402110042c0004282007510000500024030444103120120340940d650300118100013190134003c030319040380e0704100d210050381031012042401c0c1c2072 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 610938866 1250 610937616 610937641
    0x60c0809101a190f0f0f0513090f030305060909010207170903010902120606190602100e0c0d050a1b060c0f08120109091101020102041d0a0905030c030307181a0304061118030105010509 81
    0x94800c108c800c055a0100c5445a0b0010040b02d88010b004414201d003450030300d501548220b00c00d05003900c40150550b0303000c690500301e00c03c40e00300800c1848601d2000000c050301c1d4019056051014000180c420aa50001060501d01a142c12700c2c50f8481810070665040c0343d10000c64940410201801090500401035210811101d01c0d80106960f480041d442c0d103001c00098401038005000580fa10501d03080c100d8682003903d80554100007101e20a0540c0000e00e80f0040031580d841e518680c004105a45507111a481075000b510340d40f10074000c2c0501070600c400c0c07035402003443d2032000405412034a0300d1107101070450740032819640305000070881e07904141001c202c502c000044069203aa1500d441c0030080200e00782c0600b880c4000314600003001400401540100e4850301c40b40b80d5010414040e403040d0059010300480c42c580f48101200b00400c410143d1303042841000003282c200c1940d070410308030f80c0004c45800380720085000d030020030b41000c5c814035005d08001d81d807003a07061a1001e18120b8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 610940116 1250 610938866 610938869
    0x70605042d110d21021014070801030b091203160e0108160e0d0f050d090806060a030303020703050c0a05010b0a06050f0906030613090f060c0809101a190f0f0f 70
    0x40c041e14200f00041008041c008807000d42007141c0d60035440307480c0000035924901d48003e5540c040ca403088620712146800305040c0b090850b0754502c5001da08640d110140c5c0b8802421006240c400c0039205912540c022014510400c8d41281401c8a0166140e00500c8101c1c49440c86042c804800240440d40d080c40480358800ca0690414840403003208000c0342c10042170800150603101c42150f5802009000710b03455142811903912040e02d2074850300302030b4035040e007035a101d580031400c0c01040000900a40280000501130308140e410400c103482c8890a10030414800c80d441d0f55283c0002e2040c0c988031500341d02610b4246000346c10180c034444088224031034280c10502c035441c0840000c02d50364844106541c0e003030b078540091190401516200345115014002141c401782401070483c0494416010280325507001c100a00c540031074100d80600602142c0c4441400d440f0702d4040c15210b40328911740a44c80515035280721901ea19050381d0b1b4070f4000d45604501590202d4000801c29000344002960 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 610941366 1250 610940116 610940119
    0x40905040201090e150f1c0b010e1803190521190c0503011e05030a0f0605060105030f15012303160f02460c170307030e06070605042d11 60
    0x6081e003200c40b002800f402c409a50903211040c8401f010720800501445407070403500c03110b4003100c80ea00c48214506848185144040955005101105d40180c0101e148030254905041145c500565001c920306040740e080141600101064144000e0054030815003100c442010010004080308081c010320620040c425000124a81d841120600034a02c000c180200070080844154038200d00d400108040041c005540003443c10b0000b8480c0c0d409241124030901250104800d15a05c9030204003c40800710f900d40c0c10070a00c0f1058100201880318000c2c569503200801c40c0d100e02d040603070780c0004455600910201b200380f020b11028240c0005003840b502d103d00303034081142c034940505018544a00c1c0ca00311712035024040c0b50721004038005c0790900c000f401034490030003090316403420701d2001402d503c2d1003010341e00c00c01c14500400d1040e80000c1a0090042c450381ca000c0643d1514000c1d624155800d40c0d40044901e0a445956032248910048100281d100c4a042080e600e034002c03000d6a50944070b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 610942616 1250 610941366 610941379
    0x915041a0c07090203010f2c010b0c0a05010203190e07050904020d170d0c03050912160305070b090d08130510020c01020d0f0506100306080a021212040905040201090e15 74
    0x10381640700500140c00a020b83d200215101c0d80d44260700a040c600500c41e000b600c02d510a4100c00c1442c507080c0d0381c03000800308180d1881692909441203201d50010b01c0100c01c0e40655155200050004e000031405843c9500c20703914190340180d8000211020307150f1000c120380c0580d000700010b4a2b0400b4007a40319070100c440d01083c0c8150b040c0900180005007605d2030800380001c101c3e0414105030702c4805c0d02c0c112607508100c45d0351100724841d603540440b003070400c4003241408141001e186080d0381803011442864031a003020000d07a41d641d1805425208004581c00c2000c2c0e00d04082d5203e49501e501c842101c003146502101c0780c460a45815103402a00803440d000100b0740c2201c2000d4046507903501c08040c08015400513400640c006140c241d480310b02c00d441928000d07908620034007074441500d008901074585007078203500f000760b03165070164040c000d4012803403220342198044010b000101081d60010444c2c0c500f40c8001410a41c00da08112038404041062003204012000c1031440030f4800e0b60348 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 610943866 1250 610942616 610942627
    0x32a0302070f0b010b0a031a01020a060b180a0e1c0c060b18040309150201020702032a09010f03060c03110a110f070807140d02090c0d0204090606050915041a 69
    0x88007030b00744608050700b01030b0301100001d501d00a540c010098010305980400988801c20301c0c0000080309044100d005a00c20404000403400e00c0e400700c1504000100038a600b4517601c003011102000403550f425029940e02c3c44030f012010b06000d4850100c00c060050401080400750207005c050404d01c000e48110b80d145000000394039495486036003c4000b140ba0461841d151800800c040d8a6000d2851003c104007040e02d5694014001c0d101581d50060190006500c1007440501d000081e102803000204400059007880d1035481c0c10781d0103880d8400300300407024150708050084d20300e00c4858108061810746510502e074080d1054a260802e00c0c5803031540d10f40f440160b82e180001c641c400c11000e0041d25070014120000244082c00c5440e0744602403a0201c14904100442041301406504a2040d00c009140f290f0344a0043c28525840c200041c1040e8031804a40222000364100320042031000072040100d01e0b008030120800091051040e01d09414010295180c01c0d0b041541700d00c4080200d0f1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 610945116 1250 610943866 610943873
    0x7080a0c03111503160f08060616050106050d03120b01140324040c02030c070803030c03010e2203031e0b0307120303090b090a021003090804150302130602030a032a030207 75
    0x1052003110054600c02c1d41ca07410000c1c5807808180001041740c02258010380c9a001040c010503950784203c0380104418202880c0c600d00021001c1410740403145035503034102c01b00c4c181d074600701c90400c418002d64468076102e054142c40e00468820508150510102141c0d500088100d41c080702e51003105180c8035440300b0305401e003040348004600082a0b129003000020070301554000702514008008200310782d6041e41d81e5540e103840c0e20041d603184c0d0458034100b006204501d0096050354020350f94000d01c0d0000418100c00c0145501c070360741c01700c00294468000b081c201d0440c111b0b084108000441c100541101c240001c0c1e6a40326500c11007440e0541d0030400d00031305020758030404200d41c011041c03120620705840d0103500d5803010700e81244035130001d00b0000e18042c840c3c490982c0241d444902140b90900300105026009084100c030410982c00704920080e046c403d11307001d001410f0300d030002c540b07600d201e40c800380036034000c02c034106000d03203e01c00c050090346000034200503070350028100140d640f9560b04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 610946366 1250 610945116 610945129
    0x90b030307060504061a0a0b0904320103120e01120e03130e010f0e040b150f12010e0d0f02101505090103050607020c0402071208101d040507080a0c0311 67
    0x41e000340599103041e040001303005094201d000f448414103801c00074107000c50100305400e203550061002c251b0041c0030003080c038142503101c0701144440d14420301210007035469800da42d07500a0b200c180d001104030010020084040e5914041403510304004071100e2000000070500c070024042c2e115240d8440c50310360480281801168012014491114109600c0e18044c02a420082c42074280314580c0400010345024458030850080342e0004010b0300b6501c540010750007030125134030140c0e885061a405008a56102000000ba103204a0008616600c2021034941403480182d0310a0500c4495030340c005407140d0101e0a5209003c04000004030403004002690081c3d00c0398104a400184000021003440f4000501e14843c0d800d50b03003150240150001408240c0c024003c000306600c05505014800b680140049688804117008828815a864140200c001c50040b000e01070307c3d5810f014002405414002c060117481141c008210291503541c5101046c10203102c05812005c1c1d45021418658602 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 610947616 1250 610946366 610946377
    0x608070f0e12030702090105040501030b24040905060a0506240f0c030a09031e110d02040902090a0902092a0a050403020a03031d0427020105070218070f03050c04090b0303 75
    0x341403402c0b46182c51545907501c1c3e101c54410f030320406503040005407031b20b0079000d81810380303901c45104042a2103000602c0209400c402c480348401c01e003401b4484542d2550302c01c49241e41d000310014481804c06a401c8003c031071000c2d040d503002e02008900b802c5090151980c40440800b50340281e0b5503a0403045c03480c2c1040c0900030025600d0701001130b18203000c650203c000c6003900c1c0030318440c94403400140c4442c0055007054400911818181c00383c1030703107484c0c90501c00042c44d00103000410700d0110343d130009150300340449011030340aa0322284441981400342640d40d03c640541c00f4611134585600c207006d4524901213a0a03800b01d00024014826032064090314000c55014102c800d02640f00d00d8050b0811501143c030f40410303161000064454a41402070f4032006c85001047d00820540b020320264030031a081041c2c3c18003000704074a80058071601c500b5003034000403403035820715800c00c0d45d03000308003411410003003040505101c140401031040c10308880843da01400006000150100807900f1401107 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 610948866 1250 610947616 610947619
    0xb0f09040605121501060f121e09060e0f010b06030109050702100207260a08011802120c0c0d08010e060906040615021b060a0c0605061203070303020a020c0a0608070f0e 74
    0x2a9000c1e10f40d03c0380000c1d003c0d40b0070102003003c40c1141c1c1c0740d540c215007402050000c1c900141c60409440540d019544c00314031140b110302e00d400d0040300396200780c0090740d41031381b011107404c2d581e80b901e985c41c0a418400c0d04805a01e001c0280500b0070030304000b440600042c001e10400035642c5012130b82040c002c01c1405e40c1504000c0d01951581002d080255450140c01e0150424145c1340e00380c103600c02410011910b4000c0d07140c42c0d200450342812204070350302850001000040368200940764001e400b160029100304440704070103a1300d810b802d1149040c03281580102e070078022144011f2164019005a0719401001698440915558200080c0c0580f08030360115403c089041401c400c42580490f080c840c043c3d40c004403d0a0450720024020b4071300c41c82035480001810b012650000602c55000355401c840c001300b0304080300007a51072160956110400441c04203500082500981e03406100d4942d500c142146ca0140480c54900041d00102c1e0091508040090030107881c81e085014030141101c1480 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 610950116 1250 610948866 610948879
    0x90901090c051909050a15080f0a0204050d08030108012d0e4315050d0b0405070909060902030408030103152009040f1109120a0210090e060103060b0f09040605 70
    0x3e440041d148103664002e1901400c0c1040300880d110040d031004842c0501c0680d126401307603494210100c07100002605200c0e007203408201c0000c1c0c540e1040042410307280500c031507a680e949000003082c00c4851143c03441c20b8078240006a40b640000855100418504880010032a1501851000d04192110741c010401b070341c12401100010303040300d40d208094076210b0743c078154904005404400841030380c4500c4040389445000840050303c60806480243c0117450080740c1d103030314071000400340c07041203030a00002443d903103003000285c4a501038900213002d4044214a90b05140d241c01c1103500c0140006015407580c841e007030032100099800a408581907103003440c05c11000304070481040e401851581c0c0710341d0504084000b050010302c508014841500314084c6000400002d00056210900310042140111084000541c48008079500c001d036403036850766855800d20010501a82e00909454101850140e051040c42070f9481110b094160340403d4076102c01100b0300040280045421441d041754 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 610951366 1250 610950116 610950157
    0x10050d060605061b010e0109110d0c0b071119140103020f0c010f1a01052a0703050d020a060e01050f06090a0f0908130515070227041b0b090901090c05 66
    0xe04d0f0028035010508140000d1140e003840320812400d0f85e0700c80f88044c00309030b10800040d1003842d02d200c266211034401d1034504c00c5503a803040c4115482e00300c968140c2d41d00c20380100303210482c5041c2c1e8004a0141400b10310021a50805a6584034840082401418141c1c00260078111440d054291461485500d0080c0f0480340c4003003125025049584d00025881c12120300a0034079030103076040d28201c0e0800d6072444030708141c0d0048501d40354203184a198542c0110000480480c0c0c05000031240041c4039002403481104601e4413000702e502e160b074840c185034540410721035010790942c0c40d650840401c450301c45290701c400415000401103101014501442c00c2c004038100110f58015002291104903501d4101d543c4000344a0304250600490f40f0940381040b00100518080502880d07085008202007128001c007004d02180d030506175400d0320740c0311491161030a1050550002e0010303180c074104d120304010a03000854030192042c040c12072102d403a61011441588514207481c4401d243e960010250b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 610952616 1250 610951366 610951387
    0x305010e100f0b030c1c081225080f0a0e0d0e090a0c0c0609050a0c0b090a090b010e0d08071703010f0902091509030c03030301090f06080610050d06060506 68
    0x2500c1c00181100c0003418804400300005141c070440405100280c0917110303d000d804104206820620114840d03e20900256004644154080c103844c080c4400c3c0310041d03041c110011000703020070310f11122054440d60102982c4942c0b080c11150018004600118151903080640d4007401a0b50341c0fa084606c07a0301c28400c0340f15072041270301d40300c3c42050303665407115141c003401402036488000b200740209103114030300c1002408981c454190107010b003046d5030075880d095a60f8220320032558410700c0180c0000c1641d000c1d503e4411007172001001520420082c0d40d0070707500040d000d10300e141c00e07541c803d082e000600c40a02c1040e10803210503550140394000081c2c000c041403046600b007801040010046510041480d180501c00c0358060070340249070442d82d214035034000900b940314031155501800340c851a81031907201000039501804c0b4201c3c000c1600360340d02a840c4121602c07940003907507660000c000d100501c0010284582610416101d0700300c1d442c0c0340c3c02c19070040c1031141c0c040e580050b00010503543c007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 610953866 1250 610952616 610952623
    0x90a020909160f0f0308070c150804060c0c1106090414131202030403030e060d1814010b01080412030c140408152d090106030501020f04090b0904150b0a0305010e 71
    0x41c0d41032000c03400c41600c803c200552080140588503402800b100c0030710100b0400030150081e0380c07194001841c401c2d00c0302d1005001000c1a4440300c08a000001400104a50343c010788400800314031380402e1006554607400c1c160900000c40b94010040015a2021030320b0b03035001745005c220840318101031410002c841d10308000103500241c9100c1c88680c49501482e2002c0112811203426654004010b10f1138803c009a0fa40410701803044944d440380340c145040146000c410300c0364000c0890308400d11449502a095511801e10390303040150000403c000540002188200005180b500040703151416000360b403581c0e44050303000080e076004100003c030b0b10f60000e4200d9410901c4620100c86458882440400d0083c80c0d07903c3c004492203040410041e040d540c0401e602c00550000450000d030b880d00d13a0b50880c3d109411640a0080000301485030306180d001d0303620409806c1d1010390740307480d15850301d42c140c2414550541d03156407078501040090f40c80d4207016000e150010001c06c9180158240580e5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 610955116 1250 610953866 610953883
    0x40e0601020f1203010e0a02070204091b090b01081f05030a050327061b030f04121b030201021b0a031e0507150905040b030a060e100e0a0c060305090a020909 69
    0x52094500050b000c80380880c0f00070f94500002c0b03480b0304503400d00364400150b0800500300ca50a031f034244603002c0941d849025407000203000301020444c0320306001031042025119007000d0b00c0c040c00c0c01410b18460b6480600142d1104032241c60f0884404018036240c0c040d00d440d8003903585407003290314241c10300c42e000c0003d009110040c0d6203010003549504440c0c0a01d1143c9580030751041e0148100308903419003c14031080c030b1828009507494004056a01c4226400035000102032040060100d07040140e01e40184103004603001144140c07a14650002f50385070b4403142801d419101403510b8020300d889041072600915071140c19090698400e0600c1e168003904880241c40074420620001500a0000d54031408660141c0d24408054204014000a0b10003a08000e82500c6940c0401020541d10b1023800c1c1d42800e000c01926514000981d69406c2d40d0b1004000c64880e0002180715000a05c0f901c1032504881c030905000c46d040c1d40e0090400e0404900c404080c0d00407042400700030380350314003013001d04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 610956366 1250 610955116 610955119
    0x80411030a030207060f080f0105010807200304090e010203011a0f0d1103070f0e09011703271002070b0403060504020d05161e121103030d0228051305210102040e06 72
    0x9140501b0f040304481560064807099540034403000144019442452810760007550b41c1400d003841c0c2c1281c015211800c041281038603c070340021030203018503101d5000340021400c0e0b43e0025419035041070350018144418241481941e6000107440740f2a0480d441514004a0726201c20444a100104e6000c01c45d4000c6652030001110b290f90301514500982c1c8012020314041c001100c0303682041a081c4006d4503081d81d10100d031106108a90b1804042e008101c00c22141c00c02c580403500d12201400b007d103400b50180170654025550a000d1402c8a40a07201240c3d048107000c113542d162400400c1781d070780710010064070314081c014250b8116500740da6400b0403282403440c0d04204211000740711aa0080b28080e080000d00c0310f01420000c11880c244240250b49c00070305503854907a5085000c01260700805403203041a0802c0500d111040210840d15000305840c10b14900e0034490340c415034810003450103290b128541d120301d920301d440c81c1700d0090700d410744842e4021550b954845441100c005c2c0200d8405 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 610957616 1250 610956366 610956377
    0x40b030f1c110604150222120204061d0c180d060603020a120201170a1107030c0b0c030c091009090e03040e01150f0c08130b0c0c030c0604030201080411030a03020706 73
    0x1d94010014281d8410782c2c006080d4042000c0c01d03901034020358803501d800c010300c807e03110f04d00f407581d96644101c10081001d070b113102541c2d030424414801951815404282d1a0546014011408219404042d88a07844001c2c1c4c3c2e5440c5008810004194a1034811a8201142c40c04580c00c0202c158440d00a0340e008482e0090302030381e22b0b070401d100100c418100074000707007a07020f04003c903101184855400682518012821070b0500e681d03a80c598016410031340c001107154018a0034448280e600603007010303040085c00d1075071078000d280c840c052003441c2c01c40d8041c03280c00040080700c92140c2c8034036016003410102448040e445402c82c607680c1d042402000c0040e21144000541c20b03403990218094000c05445040410010170010f650803052414151440002041040c01c240c00085451010340f030880f01a40d2a00c8400083d580f4044000180602991290041c07541590301e0105650489a0901e08103241d66201c0c9469002c07080901007064140c8501d80c44001016004145a41074a404c0c0e51038 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 610958866 1250 610957616 610957637
    0x80d1a0109090e1b1309051c0f0c02130b0402030a0914060402011b0c1203050c060612031b10060308030403080a110301210525120809040b030f1c 64
    0x4211143d04018083e0b641c05000c41d80d81c0f444020250309000e41c8000d2600c41250700241346801500c0c00800120b076940c0001c01d05001800c601d0100d4402d100840c601408016800b00c07000d8001090218007030f100d0104203000c054a048540c004e24000000500155168201641d1110141004080888469840d0b080c01c220047d40050701070301c501d405075141c884800d00181203007030b40c1000f6002a60500116880802e41910b132821240e0101c4c801d03a1019a40c800c0b01d43d585d0705010000d08580e12402030b0750084602010b000040e0b450071a40520208000e02c3c0ca004000e01c1c5c06d001e890b44c10303c903d0400b5000010301c0f181c5000345110740d02079110400d2541d0f640d80e102c0201c816003501040c0044060006110403c10040d04000501c200c044961031351708640c441e04d1800d0240c918000b0244444c50780350419180352941c90f4000e201141d00c62043e5662545d54004078040c0015450089945141000607607808221074a0546d247d4810390702c41000c10074084840074414448000492075002c00c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 610960116 1250 610958866 610958879
    0x2710021b120c122a07090c0503010504050604090506060906010c05150a1506170c040e09060615310f1d0112150b0f15091c02030d0804080d1a0109 64
    0x489501c010b05107040200c5040b010710480030b010130310f80c4c103501a00c50080c000c184403446109480300780c11141c44481e00c82d0700d03040410041e01c00c01484240240c0c2030810202c0026400902c068022a085490443c195101d10040740c0c10541441c0180c80d512030b90715000000380c951500785014005141d02803020404582091b40360781150b201d04000501e011001200c0000d4104400350000e000c2541c03685003a0341d44013080740942080d5650020b9811050500050340707404140d51900b0b80701000c2141c00c140030141659014080081c4811160110328110400038225020b00409440c54010f079480f0750362181c021a005010041081402254500001c51243c01700000070040e19440311031000007446501d0844040c00c08c09951a4010501c94000ae20f00d503154094006038440c1e00f0041a02c9590410410903001140c1900c1200c0120b0482d01e10090f88002c14600000311190601100303d48032460b1514441c891003801c1000c1900d811800c03a91003511810000010100b40e807087c1c072140d103030032 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 610961366 1250 610960116 610960153
    0x501050d0803010e0901021b010b04050a050c0706050a09120c111c0303021605031b0714030705010f271e0f09090302070812032710021b120c 62
    0x11024009a40a20041160003c01050300d548901010005801d00e4072466010740c1c0c0803418103208088c2d94544010440d5410684502a40001a9803091000b402c03c003c58501e58400d80340c02800064171140010628007054001c1c0381030992042e45d58040f490743c43c4000340114062601256410401001803015240198880d860035207164a4103100108640d01a4025407102c00c00250800c10780d040c1802141050001c0c00b4000c510318105440b090500c003659040401d1904040980d00003181041c0540e2000141030040d540300b0700f80400400f00d9913509403450703248042160101c181c2e682280f45080181c8003200c003150b0107989c40c0c4d01c0850a04296480c50780c07440c0200c41c01e1103003144040084001c0c0e03030000005c1501a00655044549034800716040002c01c51450769055400420b0007a0350242d11600c00c040c805001070441180c16585d500c035200c03880b030f81301841c3d9240c011034030440c001c0c1a03c0c04100c408140340222154100c0d0350050242c2ca800c0740315440c07030901501420301c01040c0c450 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 610962616 1250 610961366 610961389
    0x3030c052a09150a03030201060617130321020304080a030614030616170c042103082d0702070501020d020f0c1005251211030313081912050105 63
    0x14034058a0740d49528040c4109554028000080b042c500030005003584c46403031404001d54041c0d40081686414203c1c0a4050300b00b20230b82103020001d03c4104015078070300f540a00c540a0340f40ca0034010725030050b04a40051140ac0b80a049054400401d0104205c0c03117200621008640340c50503c002c039a10030309a0784400d454000c494050704020300042c403403440c00d01c0c0389002201a00301b658170381101d004101031584049503061220314000400f0f0020a580031046000310b01c407050304280303421003030740c0c0200340d41409807017a100c04c0f051003210900c401c00c805040001c601c9550107c4542d181c6482c00039645c0409219640c058020451010385042c80460144c0b480307031603040209a031441e58002d00a030090705003010410484140080c00f5040140181501e440010108044003180241483c003a8185800d40080070b10441e040c03000d224040c003009503a0701440407100800608251f0821268611485000510549940d4200348440703400249a400d04c01c03034180104000d0ba200c0c018407482508a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 610963866 1250 610962616 610962673
    0x110304031d1302120f2508070507060219031d0316020f04090c030515040c050904020d0b07020312130b010e07110105011202010f0e09060d1b03030c05 66
    0x38912900d03503109a0310440d490301000500200484414803010300c1c12a003141c000408807120010900c0828024240c1160300600004006d107452100341c821401c1e0600406540b109008200f0b00203010a8051401d1356801600110299a551104040f00c0c550103040c0400e000401d1418080c00502a1150f42200380d0441f450000d40c508040d00f40a0221803240110407039020059550009580e1901c0c0101c4c0f00852250213144040340c1189010750a1200716130310540f079110980100004548100140e00813a03405613180351031600c50780081a109a908800a8800c0041d81c09120b1203650010081c00117208291070401582ca903039a013441c2000002d000544206e06200050007202001801e041e0080080c9c1881c00300505d5480051b42580c200b640b05441d00180b41c041e090542d40c201c83c004082820034079000c01800903e100140b9409005403225000c0c4581c503082904000c4d85110200700d20300700d013040c001400e0b41c030f14000b030251141c020300711900c1c002c05400e004100c4407664044031440340e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 610965116 1250 610963866 610963877
    0x615020c030c130b060c0f1902030c120a120f1b080301030813030605040c0510050c1c21091a04080a0c150513020109050307120212120c070911030403 66
    0x18a07208010307801456610041d95144d0316240b407a601e98440e4001e084003001c210242184080e550314460818100041d011180c1041070034140050f900421440303540a404c03205120101c0210510fa4902848400020078000742a5070380c102041d041480b02c1001e00c4250389100c0c0700425058581c1c4800d200f210b0091001d0000c1c8011320000301f184005e418000c440780000356040343e99880700b0041d14002e860964015a0307a61090205042000e40d40321144030381d023015072504d001e141d6460b83c0d41d1031209010444880c2030407d944804e11a0115846803030000041c0300001c055852010300400d81400e0444000318002e640c00c03109050004031074882d0350090601410241802d5003a039080d8103414040740c6980150840f102c0342b220503c84e15004503500f000b0a000607075148000b42500849130400c0744030350300281080002810071021400350f01e1381900d03255410464045280e150800060010410400128180d060500c00040010803241400800c0c481d800038288140e03800e02c02620050300041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 610966366 1250 610965116 610965133
    0x1203010e1012060e0c01141b011b050d0b04060308121801060603061d16080709050a0b03100506040f0b0711100c032607030e1513060e030a0c030c03020109020d060615020c03 76
    0x4c03448540c4000c070248023000460401146510000c810610810a802142000c42d03070700940c00080c40340d2110044107407009c202460442d12030310101c0c0201d06c904101c2e20255400154244c0f48000103045c10580301d0b00a02000c2d442c0c50014015100c14040d81101208103143c140036041200b07840340c0591551305061460080345101200e035000c0c002c4c001804e01507420f0300050252603a400603002030150f000165140d040c1020f145c4400145544102e21546040c0020700100458490307050031116070341081543c0749420328015000940354030959a1040340c058026094503000702088c46068480d07502c4001c200b00800c064810140f007038400b5242d01810070001b0320594066030107400e0b00c00c0c0c030408980240518128502221504460100400c0710b92280a0f003000000d008165666010101441c10701c4032030744c8002c0c050140c045c1d010302004809025001458001e51201c0e1320f141e000b8141361000710041c1003510141c01136205011010f003048030f4000003d4804140070780c50940040c0a41400c9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 610967616 1250 610966366 610966387
    0x1a0306090607050a2607030605040e0f06060607140706020a0203121321050f0d2303150604210b07210e0709061e06021203010e1012060e0c0114 63
    0xf024402c0049034002002100b0b00e172030001c443d04c224403c2800d650003140d01030400084c4000c3c1c5402e601c0c528650352020f608820306440c081400c0c0d501c0f01080d2090f544038030340c0f4141442c3e440e1a0f02980c1d90355018070a004603041e540880c2d4034a030540241d045980e030910701c10300c014851145040c40505890281401d10150320030781484150204502548650721619440b05414451805400c00017580f00030300480007543c2084103000f00010002e8185690620303224602c1481c030006210410700040070801e0f0307095640364025100a8034811040c200a041c0d0400803c0d240b1944e0301c004e8803104103400024003658071681c691000c1c84000084030275003403c521002e1001d03040390398400180e4002c000c000b0917150628401c4a005000c4128030019030068907000e1004680d0a8000c030f0110b401034842400c1907416203045904580903104805038561b542203080704802e1080e000841102c2c6400c19040a104081d000006401b00701e02c2074030200c4449000558044c5903642140880c1d071403e100e040200b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 610968866 1250 610967616 610967627
    0x8010b0a030b04020702040e0a0308011d0c090103020c0607080103060605041a04050402010323010f0e010e040f06320906130b04172a010c0905060a030f1a0306090607050a 75
    0x2c41002901c0541452104d0340000c0956140c0c00c42c1e048141d0081a01c01c6c285680811074900400b407000c00301d070341401c2c404d40ca40f1000300014003203103100b40d00007071429035a44a80e0458115005404c281c4015003094000102440000e03c0151402d44c24040040b407140f800e8071481031092056081c001c0d00070141c500f400040c20000340168107243e91031000c0030030410f4044441070541541400600103606200c142c505a0000da041079044862007030043c003001d40c4000384c043d040341d009400039031100590b24040001c1d149608440191140c01c03200307644003c40318118020280072000ca04039687d540c103806d081da900d008503904c221350300c0b40e14403102c040303415540040d03041402188801413117800b0480c03808040d840540c5a0350200070000e20a0f148040c0d1303c1440100e01c94290086c0620803a80c58000c1a442c0b0303500aa83c0f08000015141104501992010724000e21104060100000ca0a00150351030441c40035203020340182000102c1c0c1e034802281d014890341041d100d550070700e03240d072008685 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 610970116 1250 610968866 610968881
    0x21912020a080f130b0c0417010902090f09120a0302030108013602040f060b2101060507080307120912020c0d0b1b0f0d020301050a050d030f030c020102070c14010f08010b0a03 77
    0x400d0700400d0000020517050588107100305905c14419a03100c1c507104900d00344003000440107031aa41352084040060340c58059258020300d5520300c549061302d07407090140c24000e410740302c0150150005041091560141c0140d812134801c07400070011440b0200000884008690480c1284110f4100009911400b54528400c65002401c00200b0300c0c030038040c10003241c8041c0c2001464002c0407941e2200c0c810b00002049808001d00010641549001000780c894010460020039418010000820080c8900507450151008a9040c0312000d401e05140050034000c0111030014000c912001c0441d01f09801401c0d807d651281c1c1200d036070303900c281100c0c1d9010701540700c7c0c038010740c4108041200b545d40c02015242009150301c0c0103035207501d42801c1200009681d0300483c0980e80d00c0d03440c500425048004051140014103020600d40c0d03000000300d0080c03085400041500c7c1c14607001143d54220845407541c041000e80b075404040786080c0c010798202c40240328816068800300580b4505500c42c0d00a0038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 610971223 1107 610970116 610970131
    0x90904320a0206090112090f0303050c0a020c1e0d1406060a0b0d0e0106171005010504051b0903070509040b1504050c040e040503040504021912020a080f 67
    0x1c0d100e62481c40068840d803404106103031141d001703140c91114040da8020401850f4000c1c6000c01c404190000c003500020700c7e26000070700b480100f50031a2507400780c540092200c5241c0200f080b01c250b401c0c00754070b45603813600080c0c04400e03100c600300c01c078640703200d415620314810034030043c5882d00740010f0084c1d200d056805020494501e0040031250a007103061000b040480c1c5003210a030143c51190301007520340324040600d0200810118a80310340400701d0b601404640d03a201c0420080e100300391010300c9130301e42d00e00d59000e401150700c0c000c1c0f91248001d0142c45149076034000199442030200c0b8151100320038402085100707411030350248056401128108442c0c10301801030a814003584c000c1c42d20300c2003101e01107400d008040041c1c2d001400010001e6696611941002107070040c80c03d00d01c00440c03000440801403407602e00039100100d5055071074509942e603003070000040b08005008034 = true := by decide +kernel

theorem cover : BRFrame.Cov 610791366 610971223 := by
  have h0 := BRFrame.cov_init 610791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 610791366 ≤ n) (h2 : n < 610971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
