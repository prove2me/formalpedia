-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4328
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:16:04.248528+00:00
-- url     : https://prove2.me/submissions/f8b4ccac-2d4a-416b-9fd8-e9356af94731

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 778237410 ≤ n < 778417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 778238660 1250 778237410 778237433
    0x12041521020a051b07050a0e040b06190f0927050303070e0f100816031103060607080c060a020403020a0603230709050d0b0a050901051308031012060510050609010516 73
    0x40ca41590285803424421043d00c0700c04500820b1f0095200b881c000070411500003485024a802a04110300380d166007050125911980740c0204e0032a06080740024003402482c2e0400c01080102e900003503460b40d5203240e0945100c0050703c15035900c0e81c0b544510100303801004580c3c00038084e0030312401c448020b40c085034484440c1510180d000c181c04e140c0007501600200d030343d4811565081e01c10000203410034180c040b0350700400016204101440004c5c05410004028175a00340606030342c600f002030302d81d0b001e03181c0039007110400781007500454200110b0070450b02140c05010f59003030a019050440e642c610b10102001d562040e058144004120901e010380a030030050030024200300740d8a0414144030b40c0046064910b03814540c0303014000f8401030700c1032168600035200c45169013202043d0351642003950300003074180006c070503080310006401c18940040d03440c0c092040038046064500391030400d22840c801d034045c500481cbd04100001040c0e030710000312b035003020628601d0b054211071810803409148 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 778239910 1250 778238660 778238677
    0x605030c0102070e150a06230a1b02040e03160c0807051324091e0c08011e0f120b090705280302060a020f120a05032712041521020a05 59
    0x4010502290f0f07154408c01010105696001102c0d0403545105804a04c0c85a05040b5000842c002c600b402d40903000300700018240d00040011408041c13006c4050708552000c14100c0c094a0191802c0041107042d200d02e0340188503a0300038001030792500d0041400c05aa900240c1d040c0f40d611f0519800c2000c49282044012100890f0010320f0354880ea4004000e04041e00b00480c0401c5000c0580c0c0c20036194002d400180f142541c641005034a8801d07252980f81c1081c0724185005400d440224440f50342c0618440246110060003014030f140c1d080415424070040d0500309280c028220500030764580c002c90702c2020b03081000c0250600440604015403150540000b9840f043c0000e402c60303000e900251201508800005944400c644031140b00725510030f044103c00800c0c001d0002400314030411490300c0d100b40d02503001c640c182c40361004481c24104041d810b01c132115001b0405104038040c001c04251201154101700b05400242e201090401601c1201c640c2c1180d00029100d0060f4458810750b10201c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 778241160 1250 778239910 778239919
    0xc0501050c13050a050307060c02010c12050d060602061512030904091a060108011802070f05100c0206010b0f18030a020a03052107020d02102609010605030c0102070e15 74
    0x1800c00d8070342180503070721400c42d1800c2902d650801140a1a265981c841202c1c2c0040c002c00c066481c041064942412681c2c080e4140300d41401c440b008144070b01c401010541c416528107623034100200d00d20040f82d000741c02840031544040200710290f2003500d218920300604403a4038030b20f04020b04250f869807084030440c58020341411040d9080142c6803a083c1035011100580c81c0495844400461b40030b00c09100b014030f02c540d08400301d541c1070040d900408545014411600030790342aa1900c900e00340c0c1d41c1c0d0388540b8495a403100c0056059043c0032090240540180fa05d2804440030321480b454054034146003034202030142c01940a03a03081000303040380c560240030300c002641e590070a15160f03d501c2c00c01107681c5088254018486a118048031481c0d03a000f41031030040e10740c170b03001e000246c1108401d100500080c40c0d45d500d0b00741031158800e40710114591755020b8071300e003014502d400d44416600950007640414027800c280d80e004511101901c1c000007005800c0d0340d030030110250f240443e03c00360341c21 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 778242410 1250 778241160 778241171
    0x209280b04090209120a0f0807050712110916051b070503061015091214070e090a0501180201050f03070507080a08010914091009050114070801030c24030c0c0501 71
    0x419120350041c08584004407480c80680d14085d0915894079075890000b0844c40000124400040c03095003e8811980103008492409484200710b00041141400a4031024031a030121886440c00088a59104601c0c2d05002542a20f0304806040c5c0d01601d1103036594a031105a800e0b01c807040c1001040018140202101c44908107044001c10404032401000250f4189414881c80e450084081404032080d80d105046452816200c40010340c01c040307075000d0719000f11080090310003c02d040d0f03203000e03002e404080e011240c220b01d440303803c5502448810300d016103082d4604000d030303070410103841c0c0540203882d0300d07590f96403601c2c070031110b42c0304002303000b80100001b00340000f41541c4401200c0c1070782c1c100001000040383d07200445030070368401c40c4d80040c20340c05404160b00b000d065410040e002807260b4000708074600389102c102e00012007181c0810000c2d031100300410a104000081030000c001c0c1c8038a9041e07a1415040c0655207166440f1840e0603d5210390501502ca4071503000800c40d02d400038005c006d03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 778243660 1250 778242410 778242419
    0xc050c1203010302120c010e060a0e030723010207033c0302060433181707020103050f0403090e060f1002011d010e030d090c03021002070503100209280b04 68
    0x65070002e000c00c0e801200300700c180707130b4401800203800810680141c588500d04030041c0d0800006a12030051481000115001711046840400c249405841c84400b40300c920b22804102007104010a10400d0455102000030408640d448100803450100130013040380340c0030850380c40e01c242c840c054841c090381c942c12600740003030680c00b0420b00d0050b4844c00081c0441c104070313812070184002c0c241404041c90000e034401c0391f2004442d88003005000c030640b801e140c0426552030304a01c042003640200da03500740006030001150391600c40c0581c4203c1a10307119401d4100750728010100e02d010700620b0b0b600e000300c1003c44d40c0e40d900c0c2c81e990010300200410060440d000000d0082c040c0602151600c400c0141310399500300008103010703509509081400440c241a07060400708007504075074506a1301181d4808021000d61260b140d91105003200d90024401140f9020034140f034000341c5003040030200d1060100c90708a64070360020f10041a20045103241514a9071602c0703046c44442c0c1d10901301c4c500005000503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 778244910 1250 778243660 778243693
    0x5030703081905040201020c210109060605120136060c1d092e1715010504020f030402010c03030f0203010f08060c03160f141303061a0303030a0c050c 66
    0xe20805560701101c0302c0104105040c401d4500540d402070250304512644407103410aa6640b07540d8024000c8003448484400d8169804c40300c0086040e540503880700020311480c10007a2030710100080030b6008010004d11000011810303a40c07170002069240100c115030025091f404402d48c3d810350003103820070040304044809090384002071811a40440c102842822510f02182e15074850540c0c00d528030346c1c02d40c1140c5043c1c0800600c01201c01c3d103846840010551a240c400fa42187c001900020b15440080c10480b01079060168440ca210f41e004202204100200074141c0b9001503081c200242212110f15054014244800100303c803180301200001d44002400d0a1100705c444420030349420391210354032a265444125044218401850001003109104044085032440d85240c0320300d500c0c0315508650300c954090b040d00240031081c51401d00501c00341d0701c18004100004104d5060704488080420744074000182840051507940d5082c20f000c0d1300401c101c40510300c5074000c0e152007085921100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 778246160 1250 778244910 778244927
    0x10c1a070509240a0f020109050a060510080109080a0e13052427130c0303090609060c050c0f01110105090307140d0e0d0c1e0302130606120f020705030703 68
    0x1944968106a900c4520052003000c908500120700403c502e080300d6004252912440010031604565079401c0d29804150140705c1c00c02118400c00022541c0d05103080c07100c45a000c25001040e80f0392400046100041c80c803030440703540c100103003010407c0408150004500f8080f145404811070300301400c00c914200c120a50585074a44110b0108205807250309005c021410b0080241400303044203000d02845c1c041c100c00c154001606c19200f80c8086550f9550550385095a0044001c02c11100040c03066941100000c6c0141084c2d01c0d00c4540c4400c90b0301c6496071416921102401558840c3e50a441a4480c0d170321402c1c0a4000070007070009050125066680794031401058500861040500d44199008103024002c80c840d03540e00ca01c0440c0007010800e000958000444070051206c000040c00500801c1c80e50000400390302d44036003036295006011041d120352061140441c60300c141440142e4101c080107034004590040000c0800450103880004e1056403030141182c0300104000c810145e000701030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 778247410 1250 778246160 778246177
    0x90a020a08160e0408041a070201140a0c0b091204120204060e01050a03031103070f0f0b060402251b08060106170f0705030702100507020307022b02010c1a0705 70
    0x11461516618420740d600c07082400b459190440c00354200700301d80d01c40103903a035802034000c0302c109240c01d0ba14500c40103441c890583d1041c1403080403503084195030f0406840080b010030380064074034086059038010a0b1410b80c88008003140004c80203e0f6031200204810a030700b40c004034496580c0d07070300ca0361011207960791041c040f4444e40c10000c000c5441d20050302401c0c100e52010304840001401c6503400d980450030302002c10b1041c401484200c0110750056504000d85000d90a000d4007003400b41801003100030001c00c0f081c0641c0c0108000110310050107180104407074410388e516401e45003403170001c0e400151010003100640c4035010104064001059940c12980c6540f91503507100d4a4401e5001e031000102d5900c0c00104c050b00000c0c0040340500001d6a10155070310541e1544160f2002d00c0d400c4910903946a80160b00204102c02141070000d10b4541c1100130700c2420010b04807161140846080c0705900074101700f0004100c5040003d07541100404c2c181452480c0307c80d20f000c0e0b80040c02c03070300100c1f003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 778248660 1250 778247410 778247419
    0x1407080f010b0334172e09140601080102090a09060e013309090c0302070b062103121b1306110c04110901030b01140a0c060e06090a02 59
    0x25510410441482040c0e40b20001038050000207010090820075003070840729850801150035007003142800036001420203040c4082100304030101d444c1a461800d5100107041c400c18800400305040c20074090b04030000044226804500b00d00c031450142c08500d6030a010f106503110f540004641c094064014214507042a91102d803815078494504050359054455501e150b100c00b070050012421000405905034180d408010351101c0440b07851581c44990105000012500d60302409404060300510100c10030074a0150b0600c0080d0700c525552000103040705120701003001c10400b043d000c403422100c6013411102039076162602454140e504900490305103000c03013440c03036121401c040144240c8500000c021440c525403420003005071848041d084010129104a00024089554601441d00310090744003486440c1d400c2840050140d03415452610f05111105400c0c615412010003990b40702441881c140d400c1002c0b0b428a00b0003040e0a85079104240113001c10003103003180000e94000b01920965 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 778249910 1250 778248660 778248673
    0xf010501090c02190b0c071b0e07050c0705120f0f1c090608180c03010c0e0a0906080a1b0510080f0a0b03030703111002031e0604020f0306091003140708 67
    0x100498644c2e00e00b045061840500d0110030012071500385003c1d600c01c452800241c030304a41500d07095034900c402105038001240304042440024042c00600740c200125040c01820900403282aa40f03a0ba081c1c09014002c14010002510b241402c00054850310202005d031a0841030400b0401e0b1a61000030910b055000d03114010b4084500c1034494030115406030342d840303402d40c41b40d0040300844820111811303a644503241000350b45950030f00c80e150491025460b88032047d2880020f000005a450340260002071504408000741100461901c620030342c8006034000c10500c40140c140c0c04427542d00510341000c5d08200110762141c10100b51406484c0d104040b00e1700c0e6aa4603001d10980c2c80307600260342c1641082c00403400180c0a040c119019060b403800782d03401c6400030901d0000300e8000702c40b200840300c0c2d1544c2d44001c00c8608600b554100710107580c04c2d490007035002c145110b14031000e808103000f0a0b40800154558848017841c0b40550b030701130070314008070380c412071030f02e507903004034015681640540c4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 778251160 1250 778249910 778249931
    0xc07060801052205100e07030c0905062107050f030c0703030e070303020c0111030f28080f070c0f1703402612072c0f030f01050109 58
    0x404400710741403055600200c140b03d0000700c068980580542c080c81402c1c880460340d200c801c8007151252044d59000240d90340713402c00040c2044200e41c8194002e02080241c0c582001000064220810341003910030f45e6515002d6086a040c800c00303080c9035003c02c0c08010f001114600000500c07106000c3d07a0117100d080445c40c1400c1d12005140b00c010b003d40d0102d20035100e15406110310640c0705840000307803818000907100c07055481c0c0c032601440c1003407960703900002148103d0700c490075840c50040c80c0c9031101c2d1800340d070f03021207104c00a05083d05118500312503504208944486100c00c1d0340c0484408000c1d488a80300c103203c1d4106441c021040001c610020890300c1d402c610200c7c84001e00b544404401e81c4030700080c08098441481600d20403043c1c24400d0311285030780ca101e815a403520b81559980c4d41000d5501c00c00c0300b0701800d00401c01a00d0a09440d000c0c10720314050200c0d0f1815071140042000da9000102250214a8100c1e05405144a0318070080010342c04141242c21851041c0b080341d10a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 778252410 1250 778251160 778251169
    0x6010b1c020d05151c0b0c0d0f061e0303050a0c2f0a050301020c0a1104060509090d18180c18180b03010c0503070e030c1c05010f18030c0203070302060c0706080105 72
    0x42028110000c001580c45d03034007059020342c0c11500000c0d070190440c0742c040c0400580d415181c0d8940300510007500c840007046059140c1d02c909089012104843d1544d504540c0c00a229102e81c4409004102e20107010400707018000c42d1020804401480b4141072100b1040c110046604001e0494464281e140d00060642010300840c0c8110700000054803101c1a1580e81d140b0040301e0400594005640e4400415540c8520b030307900f0b000c3c0740600000c20344036891480003090222010b0b15000c0c0d500707002c03104005407681140e036842c0c206150a40401c0c805019802110080c50085960821501d607510020b1100d4003031901c40040401c1d031078140020075082003410f00340c402d2078804200282c030401c0082c981d60b11032000f00c51a01d9000b010303a04244103d10006d00b5110b641221302c5540750740c401c440b00c1002400d11501010f06150681407001c40280029805500c400ea00060107108519070381604642d018401c0070040c55006068503203e2201d03c0b4442c1e50b03030500d4040e400100e9414000814a03180 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 778253660 1250 778252410 778252429
    0xf19120903083301030203100305060f0108011113060e0d0b0c0711030714010503100b12090c011806030903020f070609050315060d021201020705011a04110c06010b1c020d0515 77
    0x103c5203605403050030010300450080d03000a01d420b80e0010400004000200e003440100e0094991103488a4154105000b084c211030031003080641d1000c040040c050007004843d4920308480060402d1100c00d88000b010600581c1031540c021304550b00041000840d55240c009402c50318001c922031001e08030070105041c0c0e55907050041210010b540c4526060541c420070044d030703003c080311101081c03155644d140107902d6003250041000c5980004104080800e081042c01d030381c0e050900c0d14019081040d1040c01d042002401503104140c1c641d81040f09040c0200080540c8020400494417281d6582d18010309541c290300880d8840e00408032031092010f0411082400340c8401082342c0322805159003000135071400c14030080d5840d5001d100501c00704000780320f40d4028044d914140c10707100d02098100000c949081b40c010290b8002409280e0545100040e000d055a007604019940c0d282081802d0036440030081c51a042c8500005461003500f44503000940240c00d06045006002e00c90f1040020107003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 778254910 1250 778253660 778253731
    0x4f05060604110c1204050108060f0a061202040e01031202071707120c1d0907230d02041e090302010b0109060c02090604180b1009020f1912090308 64
    0x280844046599890a0341c8244454500c0341c41c114602221050f96904210740d5014484ea0303141c1c042020401541c01120180d4411400c5441c08000040500040c00c10b6800340a811b0410602c03895100d030401169045501034a642c0c00032192540e980d2520f00403111070030003040018000c01000040c442c40300d0a00380c85580025010744010f03414229a00044c0240c10740586001030210340000b941ea04c000400440c0708050020800359103000002285000015804000024940c42d8044d400302c2c691a16a803881c2c4088401816258640c00060040c02c0c54540301500440c0c0b980c4034507009803d0b58400d0901030b120790000d025405400006444a1200d8490000440c0880183c04d0041c0740c100c02ea80d45c001c0d8001e10016441c00012903410b032104004d4011a02c4003091800d1040f0503081e010010000d00c0302003019494490642005000340c01491403a01000003090071a03415070b80500d1401500911a000030407200c11a41001024000d01351a00f21030308040d01840c810342c20500860b2250031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 778256160 1250 778254910 778254913
    0x10b01020601290c0c010f080c0d090204090206120a061e09020304032a02090c07020f09090a0506040614100303080c0a0207080f06100f0f06084f05 65
    0x140e1030700c400781005060408a1080501c0201c0280d801140f60b000900407104141c0c00078560b41d40c0010000d8008024865900207006040c0d0810024014040480e204445841d102150700181840450050140310000030341c03050780424140f0341e60b40d01d112000c0c0300d2004000705010715031313a0340c400b40d04001800f001084044c0e9803003401d20403d1802d40003950090301c03030f1400614042080c946440c101803882661602581180c1e22141545468100703660450100c08506143c000d440e800250100141c400b00c90180c5a4100082c10404043c001414130507006002c0d20700600e000e2800c00020005030810030301100c54500481d408040003071b0001c040c2c9034140c468402d1525610040750441d001003290004601c200e50f80402c540f0400c0c800d060010410400503c1c0c0360400405804d40c400d610f41003111002d20110040002050705e035082c400310707015070400c96900d032100000a00c0f040024081c6050038030000c82c1400a50020740014407810440d4501c2e001302108030664034003072042840c0f014145 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 778257410 1250 778256160 778256173
    0x70521090906041d0a0c41011e051e09010e0402301b0c0a0605063d020a02030715020a0b07051309090b07080601091208030a0e010b0102 60
    0x2d905055010000c2001d04242c90380024650301001d0b403400c0900b0804843d200c042407010000d06a14903220000c0280641141c007010319011a54442c41480700c890052100b084e0848070403a901400d00501c40c4154405044c2c0700004021000e8010342c840030030b908481004800144103000340c0c009403080480140d50b180c080b08049000c2002030340003200038410700000341e140e40708480d03105440801002c000e40b40c1903039a458203031402c400758841004210400380c42001000d088842c0403401d11032a603030040300050580c0312040407960045600c0d010801c1c400d6051520000004050202d681a04904105085c03101290034100e031180301c1c11000940541c045a01846104030203d01d0100c030608501c111103c403c0c3c1031312446506a000da48040c089280010a042d03c503600403480700141144c030105008100c0d19070303111481c2140080c864420804a8800b00d5220381c400d145c040c1c003d01e410408401403a1040c181201103601c203844401225240420a2055a0045c040e501c0780c840142c014142 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 778258660 1250 778257410 778257421
    0x121805010302090d0b151e040f05041218090f021c0b01051204021c1506050d030c0b3c0f10051002030c010501030f0201080612100209150705210909 65
    0x120880141c0304840280b00821540340e15120f240b0444404041415004045082d000038441210100003027028094144801c100211703280300c00210b07000d1290301d05000c141c218607000007061009604240505401d1400e4003a00400035000390101110084c00203d62103078500680040314081c5a909020900500c5000581130070f510304103a1060001d1b21100c046015112003a058400200b0121059900507090858501c643d225840280405039000002c1034510344002c1d1105185a1004000c2020076000a610b035402082c3c00d121081c0e071000da4107040f00780d881c03009150314070740c00d460b0881000d41c00040c0c12008820a564002e82c800c48409032224100400d1140d01520186440250f200c20010000300001c24411380340214000c80c2c44900d03680305880010000c5c2c0001d0003640c031410b0b020140200980000c113101028190140005030f840071f802000c02d0a1042030000c11400100114001c018840e020805e03070315040352800c0b01c051240c203004072008103028460700d00340c202c10fa240c0043c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 778259910 1250 778258660 778258673
    0x1208070f0c1a0703060812030132030a060203090f1216081216030b1f030507020723030705031f021b0307060606030b040204240309121805010302090d 66
    0x2405405038500000d501a9566650303904070041d250300f000265500d00c20018080207000c410004451103e1007445d552410a80c02e00242d20fa854a0403603500440c0003031020303e0000801c440c0c801c03010741910801c022030304222000390811101e8913058015100100036010021811000204200030352500700001c00c41070446542c0d4403901207400800811918000c0e14100310220b22400c44c3c1c0f01130289000d28280300900307645004540310b0003684014030034444001d00003807030000c210451030001151341d64401d040385441010382c04104154030315840303840910320003189038581c85c8080c0c040301c0040396140305040d5110504011626545194191001e0003101a0010003008074110140f5000c0b0715100800390960b44007580c219811680e03071400f00040390301401070304000d25044070f085003004d00e0a0384445500410a080112042899402180c4107000e98041102107410510004420904400281c02c90011000742074100d8040000082d01d58807900803140b00090150024401d81e0140e039444 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 778261160 1250 778259910 778259927
    0xe010906091820030901090c0b0a1d01051b03041412030706020315130209041401300f030f020f0a082a010203240d0302030301060f020106090510031208070f 69
    0x8003600b2034090403624000302c40c0006180140c03445e8000040c04400c0b403408603691801075100c000d00301803c0c09503401064001983d0010001006a49485861807000403690351140000b0000441074411112803074200000180c4141c961100160b00054520010800319494488811a0552080100f00001a4107801454025020b0700721000390342d03a0300c0300160114200c05241c880055000c00d40640d40d02d001d00540101c08940c6a12201c19414001c280860088031b003081d203080e1030039100310b210681883c2262a91550003150035003100c11304d8a4010003400025528000520500c1c1c0042d46134900400d981c2c1c8510b51001e4021718002e200e5102100c0800343c0366510b50880c00382128240d2141081c00207622458401c00001d84100441c0325015074902801001406070b410080d240c0f0010350008112810b5400d2414420640c48040c0003c901606958000074182c07070408040c400344031061301040c41545d00c122000c501034a800b24040740c810004540400008a1280d6055803813805111b00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 778262410 1250 778261160 778261181
    0x10507060b03060a0509010c1d040c09230312180906010203130602030913112a0708010507080f070c14030c07170d020708120f040806070e0109060918 66
    0x10400c0041c21002a080220445100900300d8441c000c01809407828801c610317005206003041d41c032905001011400c80002d445c0e440d40035503030340c40d01101400d01880c3c4000040c001c1e540c00a80ca0b504054400c040e940d45141c00c14041e21032840c00a44807032149095449804a08030380300882184402006114000541994150b001c1000100c80401090354464043e0106400465841400c2d0040c80820508003812803c89450107116200401007401254003145060a40e04107003003440720001c0050300d5148045200303120310000012a500103400241c030460701c90f114149559540c841981611600316005400079220114032000210982e151014014640044030f040c5034042e90f40328035001c0c982d084401c40e050100078001d003c07001046080301542ea5407000d00b01040c1b4007984142e58420b800751561030b00c030000c01c5400c4840c8410301640c0052182d0021141c07a0b0030720303040c0901200c0d41442400d000408103a40801c40601841495040701d071013100c01c20b0051203888086000744400500d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 778263660 1250 778262410 778262423
    0xa090201050c0307061514090c030703020c0a0506160503061c060f060303031a03030c120f0706020720091e150d03080a060608060d12020106030219051302030114010507 74
    0x101c2e141001e000c00140501e58481c4000049110011800303101200c0240c0c0445d049401c3c03c081c41c095500d645694039040100c0d044d225031030303031038049041d00a8041c400900c10a881405801e40510200251050003543d024661103c04c00c4e8111086516200490700e0039049280380c01200011112081d007104001c1c0228030005d144030000082c0c0c0705440f0b15600a400103910799000510001c10304070300a00c4520120011460003d41e0f2100b1921080f03020302d00035003428080b918800c02005072044401607640300d00115503600840c1380405055004040403032411242d400c921710306007003640010340940100903c0d0003072862490700324104010014808142213412101c0040503458a14414008602c6a110311405141c0400c4103001c0340c105900c1102000f820074140807031511510810b880040d040f001c81000203000d1035003070307000d4240303648000d41040358640c400e51141900842d00f001c0d075208941565180046d0640c0c1c409071300081c001c07071107084000ca041206e9503001c2c0e40100b044910446 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 778264910 1250 778263660 778263667
    0x60c0f050414010311190e091005090702160e0703051f1404060b0d140a061d1e01060e01110a02060405040b1912120c050d0302030703200901080115080a09020105 71
    0x110b281d64204503019820010f002c0b8071b4520660b000707001409100026242104145030044020340445440d00c00c1900034101034001c43d224620034000e00688803a00000c0b0040d0607a0b448500010000c21909000000d00d401d0100301e40c03003130031402c00141208801c079911865052a000b1032111182503841347d030242e51598005810543c20000d0104919603240c0090b83c1160800d0170324503007400414203520035141c4801441450b107202803031154250b403070284040315a03400e03505041d403400c5444505410807901000103940c0354880c0061000d4003080e038403000401e58034480b0301c0d510002030f070700294420300501080c0710609096101e103e98141c0244401c030b0802c80315400c0795584401d40c0180003041c5480b0211018404801202c50007905030b031078103008081c410b407100c1d5114030134210804100b54001001c6100c103846500130311a541c8910b90a0303100345a4408020750a076011b4045240421140c2000203004500009a01c01c2c040b2662200b030701541d2640c0e03c0b2401414403d4040381444001e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 778266160 1250 778264910 778264931
    0xe091902090109051909062108160204020c0717030723190501141803070311010b10021501081603030f170a090512090d0f050c0d080304060c0f0504140103 68
    0x485a80005017000c5210784403481c00d000c905420f81300c440d00907012981d03084032801c81182d03400c489603d206800a21481d11040100300072000d000003254065405800811200000600460214100d88418041c00107600c070700c4d4542a1203000f603c00c09800d100000300742d030014501200031480f040c400c2005030f8007400d0b00f10445008103182c1060684261303550f265030b60352031803498842030f030481d000d1041e4108000007a90910b0766031007003440090401c1500ba0f540d01004509421010781d100000301946211007900000940c0c3c1d4200041d5940481c4017640000b0300710001049042c0d050404c0107440c03128a05540781581d500c00c07540b0030001080507400d1004090295051454026200e00314085242801401c142c2d19185e4204034504440c0c90400c01c3c488140c2d0b030a503c08507019808295896a0250760800d942030012001c02550845035003213125040186030760046200b04e2142e942080316440c426011034601050745001d00101e40200400d020b90743c010781010713107511814900811060a82e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 778267410 1250 778266160 778266169
    0x9011407060e030a0806010201140412031b050702151305090c130b210907060e0d06050108030306090f0c070b0a020c070f050102103c0e0d0e09190209010905 69
    0x2150742c1000c560408540707080d590f03a00180305a0025001d1009101202d092480f248240340003802c000d100010015400b14054026000803032600082c0d00c01d0603081c148034401400a1f400150100d1043c500310340b1665820107100141c990943c480442d811686040c2414421440c02c040c180041d0741034248081c04901032184907e80c060880e489416440704030595014070003041034220b00010aa1480410000303a000140d61000c545061410b940d40c003124101150440c20440340203042241884004170308900004000e42c01002c094030001d08581e55a0f22101c889034080d18034400940c1c1c06c00c41e131808038803200d5807507401014421005150444260710681b408819038803c50741e0b5454072904220340d68040c40076201d2800117030402e0004011100c0c0200c0c126204d002c0300b10341d441c007000104550306042d4090300d81001d10600104550740a02c0306e21542c4a0303141480e40002803010455109908141500e1405541e8a5440b010007010410101c80607421580b020303070402409003400141913a070f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 778268660 1250 778267410 778267421
    0x50f03030d06060f17190506060909040b010e0115120911040510060201060902090f120313030803060a1706131e0c170c030d081005060708030603010506030f030901140706 75
    0xe951101d00403544c40d101c018103416540d440403014032003800c0800218500d14152144030441c4848001210340d100d0002500f2409241d45c0d19070029030301020082082580c081c8603040c0c1d1560141070186a80e9070301108483d440b204000800200f4241c01d8511040c259003203481008d20030841042080720a41c0401d0455800721055080844800010400f85d502845681d000c0d0880610540c03401c1c0d60400850482600750000340c1c040c100b55480060720300c100780240d514a026084000607915034a04040c0c0c4950000c0c0c42161184503d00c0d40001c0304405d58848241c018618405860107603030704244074480300040641500c030788a82007408840f81c0003c45205c858a8840d228514a4500b0b0494000181c0c80507103108480d40d0181c011060140c1c1c0000360300b850040030703150000d896605c1403c1109007101d02da00241c0c22802c08500d02003000b41e0b40010310321030706003a80200403e660380810560b58800d9441e01540c107070004c002d0b02419511030340340d00728003000c81d0081c0c920340035083d42c0300411240c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 778269910 1250 778268660 778268669
    0x15050a1b080a0503040b09030901210f060f06030f0504120c06110c030d05060f030309091e25090b0d0f0902060d200301080303072f0d0e06070b01050f03030d06 70
    0x1030700041000200001e4050f44c1f508038090600860a18095100107131110f0109600580e000c05500140100384075160807440701e80310928410f105403aa18825494448207074096100401d05105011342c21940900c1030340e1180343c00c140c2c0c0401000a1a07001e42c2d0850f10000c059901c541c4615050004003140302c01440d011003030b00d00466589070641c4d1803a088030405098070f4419800702c00505030903500001601c01c0e0b2801110700c01c016844a40300700d10403698640b0b00e41800c00c03405040000d6100c54010303c00c913851203210318080020210314212000d0003c0e0090080d5100d041c08010540030380c960000e074960461080001c1c200d1a00e4002803c09e80000c0c2c0e41100301902d4a922401c40c03440380c900000c0a0003c05091811541013000d0725803a808020440e03020404089202060f0510023851000c1000c291156070800312483c2c100c0d2521441e00c00030b110701181c80c03a4507205007810900c084554051f080300005c01ca5908000800031004403284400d41e040c8003d0126003600079840c803c00b0000d2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 778271160 1250 778269910 778269917
    0x1060c1b0f1e03050618030c0105090c0a060f0f120902030303010b0918070c0206070c03020607060f1d07122415060c050303060d020613081615050a1b080a 68
    0x240382c19240750b141d034208010000d0040d1544070070000504002032054200303a0200380103140c0c460800c86185140189881d0b020503600305000c2c881801404100c90b802d04c030040c1c854000a0fa1a0901500c001c4e51200300030780020b170180c000c9546a03205120030f0b4109512000c011074500503580020345075030001e0300700c0000301400091001051800e0318031800d80c10107003141300c000c528005401806075030b44800064042e40001a98000b002990030701c510265134000d0806480d01814209a0000c124040c42034142514144031032941549401c1c0d0f44840941c01b070014480c0a040c62103a0147c441e50303110440f1002203050084100d00d29500407a0300440440c0c40000d4032034004a000c1900481580c8148144000000e1602c085100030084980c011800d81e0406922802440406c3c0c80703110325402c001100c0d00c00700307001c2100c04020419022054a0008404166460f5100307000f08601c0840342d600440c0042040b40c42d990300402001403104658210030160220b40e840d482001d502a86016000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 778272410 1250 778271160 778271189
    0x1e11100506030c101b020604030c03320a0f0606050402041514130302060715050709050a0b0909041b0302061b1603050d2d08160c0b01060c1b 62
    0xd030b0908121440d1102012640b4900c0c1d44043d02d000750407607102d0090501650030400700341c802e54032000f04440046500c8040808034968a00700312a050182d070244a0007034100b0603c440d40030b40803140c0c0b02030f0307841b0b1a07000e40304040c202c1e42c1da030042080c290002c4400c031303031204800903083c1c1c2d403132000d80010040c0666001495031062002080c0306024000d000d000403081c08511076420001039001c0c242c80e41a1001959420342d41048240d0b400c0c00303841000040e0501003009071055122600d502143c000352410007405480d09200d62160040004484e04007405070009004241e404840301c900c1032002c022401140d840390049600c0ea8410302807400c14800c1c00300d851b5051141000604514036034a080d070341c0001d045036200b9031200c0c441a0720388104468520300038024110091800450b40302c411503001d550401c0ca20203441e0f0b0701c1c01c9070701d040c42e24400c4180700c03812400b548182000381d0340600a416680c2c2046001d03100a11008400e442d40f0214a02c01c2c1440601d81441c0c50141049100c031112 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 778273660 1250 778272410 778272421
    0x10302030f030f0f07081324051c090f05101505030616120b040e060717071e05161a0903130e1f031a0a0b011e111005 52
    0x1400c40e60441180280d4410042411290b4070003090b10301c84251203043c4d80d030b12000ca04012265010b800300e41c40503028030130030009107504d840c400340510303030301d0703001141210011410b081e01c60303000c0e0004a000e0a5007820400000401a40c06601d407640b05009180c0040c40a03100c0501d0480000902c204546da900a649a404c524150020040900301d0052880e442d0a80c43c40922001c07004d22041071010380300340c6c10840ba04035004a0003081d8050010002001d07004295507032003000340e4820002c90024030320700020301c42e490002d51240c80035803030b46101fa28a0407400440000860400c40c01c200081c0102c4501000c20400f84020a00440400480038000d281511003008085e2940300707a907004004c041403450044620318115101e22503941e480303507651400344440404510304405240e0302c0300b00110801044040603485061002280340c82a0b444083c820225685a1186408101400d402c1100410341101100342000c540c6040b40d4500d801c0f480d82450b10740d8000901e1101d0b91a00b04008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 778274910 1250 778273660 778273663
    0xa170c090a0c020c09090102160c050a05190b031b07080a180f0e090f010c020601030510060e06060304060906060f05011404060f0c03030608070905040b4204090b01030203 75
    0x740c2103640010304020811280340d01030350b29480101c201e8040c1001c40d0024100c2c0c10300390f05441c40e01d450240c2c5842049898545080501140d0090911402030540d01041d64100002070b981d00d0440030440e841c1180c100f900001c40b0b80c0009041000c84620040746d030455100d0b880152030b2032803190303908030345a100441d0b02520108c0c00c01c01e0142c9400c001c1d00308200051039003103400111102448200915201c2c0000d544c02c000080441d01159828420503580031640002c141d8102e0740504151811800d00c082a40c0640e0791130b20810380c01125010200c0d4032032402200958210348240c50004d80209a5034032801540e005a11410a000e888281007069580106407801d420076000301280c035080c280400509400d0b281c141c034504128032412500101806903104401400d030074401c0350081c0c2d9aa0300203402602044904550003d4a0004104808241d12800ca85a01c1741c40b107800140a8884544020040901806240b0441174184600d542c88038440c2042543c003503440300740190b06500502d07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 778276160 1250 778274910 778274929
    0x90a14041b0203160303180b04051009030509010e0d0c03080901020708010506130518030c03090f1206060108071209200d1a06120f0c01020c04180605060a170c 70
    0x740c03040c5603241c402010259000c0f045841600e5143e81c010a83e104c941411001450800340041451490709a0081407101d0215881c1c4902d214004460202c038040d8940c000307450000a0040c0481e00c28044004a0740c010039a9084010000d01003500614003078031401400b12650380140d507124000034040849590501105018160b030034000c1c001c81c280760000c542d07190918913280c0071480e0748802041d0340c400d441d5040144403460360102c0c0c2e101d015030b09140340c070ba5000125042c0708020400b07144442c2d0500040004002010f00050300aa503241001900c4402008140b04200709a8020f01c584500980c07044200150040c080300c5015044240781c4e1541c100d82e02001d0f0700c11404c1c004007100045082c185c02e54118800002c06150382c941da40803a10810b0464000391031030182c03420000d48284000341410030524241d080b11a20703400801848121807040c0744c0f0510303680d608901800851403d820103a04401c02600c001000c50380e950106801e0401c0134210001d9412411a460481c604843d04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 778277410 1250 778276160 778276181
    0xa030c0b0c090a0e04030c020612060a17100c1e0207050405011d0c0c1207050c18091009020a03170d0f0c08010e0a290a0806220503090a1404 62
    0x458900100c0800058541c1d085200300d103000020700c0c00250070135102d140114155540a054261260884881c0b5400ac01d02210060300070341241000040342c000c80006154401100400fa05034803505001d4140a030030b01c0c07043c41c414020a685640b0302c906106081800010090303010b42700e00fa00308810802a0b40741a8043c1003c0c030b03101400d840c03c102007510741c0f60300842c201340c51030382e21f280d08007081d400c00c1182d28660059080200c0c250781801400302d0ba412804030100c0300c190484c00c062048031f0143d80180c0d20391600c1c0d0702030044503030a56400e9008940f124002044802030307503902d07170b100116020840f00c504280f0501043c80ea84240e10740c0a070304040c02281c8002c0c0035420580380024900d29051180312003042440c0f000c01c1c1200015070111034a009070403a4510101c0790b0a040796881d54262240a0280302e4000d0001184000460400c1c0559a040003d1200340a040654000e182e8150010b441a010800043509990f543d45140c800401c01500d200441c01e903a0302c1080102c6141040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 778278660 1250 778277410 778277431
    0x70b0a030b040507020309061602090f010305010b192306130501080106020a02031c1206140f1206180f010507030516050a0f0305100e15090711030f0d0e0a030c0b 71
    0x28040c5685e00402560111007003500c0302629800800c0010100400c0048003175000048030043c45640782403c00e805040ea400f800081c481c0c0c1c1d0b1814240321248045443d5000c01c006236440c14045041108039440070410000260700d4480840000202030794042100c10030300401103c02003205581141c003003401024540040c0486d41d489402290721140300340c45d42480d0b140c0d00c1d24428010b600501d0002085038610741c00700302058503032681c6520251080811441004690719829081c070f0101d107588107014030180608905c0d111701c1103c0b00c1801c144c2030360300340c0c0b409480d400c00d41020f0b007449060720034020341c0d501149504011100b4112114041560010880100801c2e4019a00442035660103001e5240004040c2d540359400c100031129600003803100d8181c82c0c02c2c0700310f02d05074034561207800d10116504410758039016400d540100c2003040c1880d182c0c00c103104c154141d00050700500413a840042020459800e4000580c1c104003078800c04402060b152405103083c04586104c07950300240c8100d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 778279910 1250 778278660 778278671
    0xe06030a05030301090507120c0201091b0b1603030e0f070302270f0c0904061d060a030c172805070806060a0902090612010605180f06120403020f070b0a030b04 70
    0x40328942c480c4014051080c1e026181ca0200d83c6282c0f14103500080c044980c241006805003c0800034080c0401000507605000158219030381011546204c60440340207590749898034002c0b107844002c24080741802d6041c165a2007004610203414859990300881501c05064024210f1041001c0100706100b40c03c0718030500c20006600c07000052145800103640d41e0480c0e160380e40c0848041241c800c1140b1140c0080c10b00c3c0001071b1a25500d04644c0340000149101040780c0d4494040c01102c641e00d02c005407007030000f284100141070381c021004000090200603600d0750311004400c01890440c000c0800450304507000c040080c49014010000030307100c004c015000b80d0400b4030009005c05021b0250b2146103074002010034056450904441244028106003130066940c0d21019055400200540c2d400c1480800003130b6092400e00140c4d07030000401005e032420081703840076182284100400880540c482e80b41344500164080010170f00500060442e599290301e408001001e6801100c1010300841c14407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 778281160 1250 778279910 778279913
    0xd20070b070323040209091e010c0201050a090c031707050307030f1107061e020f16080712030f0c020402120a15060201050402130c12060603020d05010b03060a17150906010e06030a 79
    0x1040560b070021707011503070f00fa0385031940703842c150420140c1500d080100030382000e114500041900f0440300b0080d1070f0002c0185503180c0852409030b44246000400e01c484902c020300015000355003d1540041e010001402d204c69541c50a10f50382c0180010740c0802d4110344000f000550140c440d99611081501074000249821809003006001c0f203a0744085012011003c020103108000d86008801d03170200721a81c000b11070007c0019400305000b40101c0f40140c02000c40d4243e07102620000c8960b0540c1da0032440e201c0264100c841d1007803254104d80c080d40800406107070310f280817041809401005030000d2807110700c2c0343d000e00f803500c0d0358820390075641428100070143c1c0d5101003050005100d1040071900c0403848800300c0e80510f0711480b60310201d261200100b04d04c2c7d81540a800040500441000586d0701e6180c02c40047c0000c80d01542d0240319903c0911140c90b000c560300c0c561140050807900350032400e50240011a07401c4648401541c001401001011003d03540b00b50010001d401820750b40760103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 778282410 1250 778281160 778281221
    0x209150f060c030d0f0c080f0408030a0207020d12121b0203220e040b0f10050d11120d0c210210020903120c060a0605090105060d20070b0703 62
    0x144501a204100c04501961001410f00454031008940c81040107000c00781200600184075004551000600400008110410b448040d070300458100081b1402c5503036060300003010303500162007281c000301000301074000140c486100042100d41030b124100380310062044a82101c48151144024103040c0340701e0a0125008411160650309444114081c000281f00b0200041402e0744001c48808400003040300f4001d02015090041601c01203120860301c0b82d07501240c0c80701450161640c0400081d5002c0300107000c0c01084401044040c180351806a44601c0c428108000c2500d0140442c560600c182c0401683d240070402c482c12505224481082020380203644006081e02003483e55030000f0300c0999a5001c020390300141e0601020140c0d10030701c00f01c016840781425110305503094100540030610780390207442141655009003059040210181a4001400140200d000740c003441c01c0d501018a1402e000a240030303030142026400d9410010302c0102181d44600d440d0304000074640410102b400c2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 778283660 1250 778282410 778282429
    0x15020f0105070f1b020f030f030403031407020913051005070309170f032d01170f0d080a110904110a020d020601030305340320060402030703081e040e04020915 70
    0x41301d241000c0f840500c0c4003042d01c5c1c0c01a00503880d03151080200c2040c40280000090080c1d034481c0d9203044210340700d0440181d15010b45040254040920000680d02c2c0f44540f007510136190281085030f1090302c03400640b01c11140140d5034100007a486002d00400d204000030f8040608415404243c40c02070702c05802c05643c08090a504142900254009002d4401104c11011004160081542540d560341100d403d80403400d5280241c0c010f80502034103c0d0400306004a401e50799440e607400e1540c0f011000c00040091240052005000303000c4804a40c40e00c3c03050911840110803140e0751100c0304500030345822015000707042198040c100600019503c4810783e010b049031840c41004004001008d980b05401707410030682900740990542003410340c041d614980d6521131036481075415504a4089072100800c88010790140c0c042c05c8100005410071005102a000320b1000c41029400c015594205030300c981d104100030004501884103502e0403281080d040038842407281c01c00041d1070045584000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 778284910 1250 778283660 778283687
    0x5070206090c0619110a08030126030a02060411040e0a08030711030c0a02100e040f0f0c03060509160905120d03060906080d030f06051507170702011e050415020f0105070f 75
    0x135002d400740d000d1101c101b040040031a44940724580300d603100d500d04180002d020800440303000701d000303060522110100881701501d031136601505050307a07162944220780070192070554000d50389452400e4170b403005100f841c046501c1050283d42d6801d00d080c1c000c00c070903038410304802c1ca50810801c0e0505403200090002d5000d9056034400d2205801e107006441c07190b01503114907002810000100d40320415540002c4944015613002c000e000001c180840c01c5905a01406411216220100304010f01a0380d81040c1c0b4070701490320104c0b1503191404500f2000380402c001001c1e501080602e100035405000d0440a044290020800c03680f409402603600d43d414584c82c1e0a0580d103042c42c0400c103045800c404060200a0210700000b030f1291031500b0154028002946c0608030900389401d0007280d007088130045a0140d5480317002c205000e18801d65500000090400d0004c10840010826240014042802902d4010380b80301c2c103000c00c01c1030a4480040640c81000f004400c3e614049030080b01141162 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 778286160 1250 778284910 778284917
    0xc021e15040b091507050a0908030f0f0706151701060915090213240e0a0e04080c01020d050a020d0b0307030201020619090f060204080d03110301030b060d020405070206090c0619 78
    0x1511000303d1a8144005030300d00034210608a800c0124203500030300140350300141d40e5507080c41182e84202d100c3d224043e2502070a134030901005607000f8101c080001c0c00030203005880020710b0703280d1071130f0491410910394030002d840c4190040454040d1028480e000081480a1080c050f04040c030102003040e0409000d81c18107545d0204030007450082d211500c030050807802e01c038070a502507103e07508100032004041d018005801100000d4003820f0012000d000c682c01030b2000c8000740c9584d5941c501c560090004036203550341c24801d001800c55280516401074054100c0103a65412440c0f0507000e481600542a000c4d0380414401c00040c2da000442d240d000503055640c0140007020802c9402900782c04202410440d804607007a07003030110b60f0f0300910440c0e40310300483c1c054425580c010b9060f50111014002011000c2c40108007246001e4807803980000b004001d240b0801c000e50014040305d5064446a0040c0d04c200100135200c00208a0495242403c039481414245442082a00c00d440403043c1402c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 778287410 1250 778286160 778286183
    0xd18030c15052109010f02040b450f040509100b12030f040807050118030b060114030a0506010306060e09040f031b060506030706031107020409020f040c021e1504 71
    0x6461142c01a40c811084501031080301c00c01d00d030060a25110140c442d0300032540303000c200c0d203d5451b480c0308603030854845040060905481c42942480c2e040045442050b01c0c55900068446805c0d160720004110b0601d200340344000003060900c40740c4000681400d006605d00b009000044200048503130780312100c241e000c10261541c4000c83c202c590010b045d00c1d400d10012a02104841b03c400c0500305640b14141100d00c00d0380d45030011104a1040454460031400503041800031985200000c0e90200301814034032045a003501c001442944105c9948401941e141d0070b122156902d1301580340200310078031302001ca912a55000030310110028000030b0030b0740b03c50800380c0e08140c01405003001500f4158002e203e0345a00e824028040d00003210024464002c000c004034019010b4441c5640d5a060404d1650512005a0903c00140001d01040e03900c18a00300005c10f507a0381d24058859003103900ea0203490340c51840c011f18094407004c076510480703d410800c08402c0070320988501651003034002c42c035002c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 778288660 1250 778287410 778287449
    0x1503070b040603050a050703090c0b0c0c0a150807090501141c0207050d0201050f10140103060b0c010e0c04051b0304080c03070f0201021006151805120d18030c 70
    0x151064a50000384909004140094400e426922a03486846010404e1055541d580d030700300e040b5884203e00400d444440300c0103200780151000946009200f02d0700312501001150700081c1d500c40103500016841d145004103040203503008a0068200f24182070000c8807908120002e0003881080840141058002c18814441035540386100450900090700310b6541010b801c0c01904e501451816030050b60800c000326a070a0a0700d60500e104400f00015201141d0401c0140c88800b000b918000b410107131102c4d00480c401705031000034042010320000000d03d500745510200e0401500c204158401c0380340400b004183c0c0c2a041d0030300000741d544800b0070350325511441c18501500485510100b14400400d00741c3c104076100b0020410035001341c003144e19203090201000151a0715006807000804031200050205000700000c0b04040242440c06808649481c013042814942d54000d560b42e511115551080d10342220a9416041d42d8104002801c1c1c21038980000b469100d214021001c2850f050f15017 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 778289910 1250 778288660 778288663
    0x141c09060e0303191707020d0c060509010912080915060604090504020a12151103070c020f06070501050903031b25020d06050405010c020105130c0b1e161a040305031503 74
    0x11101c00c8030084c01c0218904001c8010032072515083c254010f9003085001c544507a00004104010382405d41c1c0c0d00d45071120350303514600131305000340c0907242030742d201c06001000490512005a103941207550388070765484c0c8150a280b4000700a501913208001501c00c4c4407058403084203c0b8156032003106c02080035246c2c1d10124480c0300613a0b114414240d400c040d02c20400c02003c1d60940c1900c0300b900c01784003062950300030801c41e01c019110a00818001755241c0c0040c10030301201da8200000620241c10722240362a41c03425540120b8800360583c10000410081403111911103000d460b2b080303a00390a2140b001d11303101141c3c0c407100400d0181c5401801800c211350318410420102940322000340242d08040c0740440c081d02d0b5440702c2a000d54280320000d09454400201e032015590881804520344c0e15140e404c03410340c1e01c01011a00c403c01c0c240794540c1101250401812420004901c039050703150b640c2821802e010a01c0350000c2401c1104062101203a4007005413501720b1001a1000401254031002a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 778291160 1250 778289910 778289917
    0x4030807170c1e0c150f01061d0f040f14010f0b0a12020d020c2409100e15100612110f0306041d07030b0603121c02090d141c09060e0303 60
    0x60361081c800103142034044c3d0002c65000100c4c03903050a43c1600f80c8030140d00b402010070034011040001e0107031264020700c0401003010850060040e041c86003214002d0b000c9410b8400d90a103c803081602c4007614064078107410100c0d80104030b00c0003010300007801e048040c1c11718031a4a480a0030462404100401c00041e0fa041350f26608421800f1076a4a600030010b5031038036000008240f812001020080b0304030f07151a130061003804140041c10619082200340001030000070f920480318401c0c0001e011124040494580c0117030751440c5501d407410b26080c030042c410103448141c04880b0b4104685003103100107400c01e03549031903201d070b8100d5260350b41c10002c100181444c0d000500c400101c0802010280000f1a4020640e8000c504000c615039403003040c1503549104c88214800d10300c041010416644608550707000070420001c025180c80d81c1d140000e038030500c1e001010303a07640311400c0030f40c00310040400005540720350642c02370245090f4175a0181042100f40700300c2042c0614a42c1c41e0b101582c0600c1113 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 778292410 1250 778291160 778291207
    0x8060f0a0608070609031101020706050d0213050603090703021c050c010e031c0e120a08070206030403140301180509010b010206010e1305100f060f150c0609020d0b04030807170c 78
    0x122190700344d861400a040244074070081e52845440111010305510208a18064130380e5034480301d14103520484114000d41c40000e0400c030368a18150045095030700d8600031406060404008e200e65400c40c0100180c80d141854000130300542202911300294010a00c01c0c80900c003400c00701c22a1441201282c01c00041101490034410f81e5211803e80d1604103402404042082d251020452040c40b40c01359150480200902811400d00203040185080070095501c9482864446014844d003a842c80194100380c0044009010f0100baa0f550301c211407160681c404102070003070200842100c0040d4440c0018015032048120410025618150030030200300713050392000403120301c5850b0140745002012410840024142400300010311389403040303404000c0d10040b500c0d222140c20b54120a840240e4014011a900d81c0caa020020140e0740d014400a0040d004498900c000d14291400400d0a04001e00101c144030032640020000d007182020560702036080140c0f6560382d90b001c2c1e1407803040c1c0b001c0380d071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 778293660 1250 778292410 778292413
    0x616060b010c0501151403120f0c0106171507091202010c320c0604060807030e0106050d111302041202061b06041505070302040b3c1305040608060f0a0608 68
    0x80c0044800c441c00340b4001215000b00c0d001042283c208105034680d20b540d018041008024000a1107200c81100282b050003281400010490f0340d03009102c03055050600141c1c1150003203c05072001040c2038400ca98070a000d40342001c030090403c1d0345086d80301e600c2c0b040a4100450010401c003040070303c1c141c104130340075403c41c40c90640203522403038840b0303965600c001d5030a40955006003080b420040162401e450703031500c541800b60344000084004100312880001e035903481e00000159511012001c10229000701c000418584c1c000007801003840380c00301e0884019104000030002d803c20603007419a0198102d0310165286280c009542c2600621003040100d8000c650030b2100f00b100080c0e2424200302421400c0c4816600c0035001d0741280514414040701c0740d001c1041e0b80382c10b00144494141030140d081120340000d5030b01e2140541c60860401c0c0101070f40000f03040401400950040c0c0024001140c05000023824050242c5d10fa40c4080c00f2172414000d101c01141d440301c2c550b005070300038100000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 778294910 1250 778293660 778293671
    0x30206040b1c061707050306040506070f1809060e0601020a02030601090f06030b07090612141324060f080105060f0d0215070303020901030608240c09030a0f0b01050616060b010c0501 80
    0x6004e8100b0325201480039180c40340f09400201401c001ca400d074801e54215014040f00e90368030405a5004241d49424010810300a287d481300d4820344800e5005403103041000540d03103080900368200980064222415584201c011500503580040d00ea07040d20003200001c0303069040780b04c4100151a4170b0b080180b107880018200b01000350b01a101d4011655203513691815403054203103c0c800c6401e0310001000c80c1e0030502c001004107959181030000c4910600d00f41d000340c0701010305207c071540d680d000041d14540700c0c0010041c1b480c80303100960180100200070440ca09188001841c6c400104802d24081e8003070440107030555840c010015181d03541c181d0a95500c115503c7c000340207500c01000c00307022078903040c804a64481c0000b0400b110b4031815408079a03128103985c030400c1c0343c08010f2040076860303001c0200100c3d0740c0303082c009001e003144900e202c0d2605608914000584410582205000306800d106040c01c00c0549140c0b0760540b81c02090024914031084012078170a0801c140c050007960806 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 778296160 1250 778294910 778294919
    0x50c070f0611040f09020d15030803070e13050708040302060105040c1b0305070203060a020405210d030902190b030105030f0f030316030906060611010e03090114090d05060f011502010204030206040b1c06 89
    0x940081947d0441503508209660700c00204110540d800d00000e0803007541813000a1489014904c04211101c005189208032000d0708032038010380348120345c8400010350f0300c0140410140c040102d580500740481d014800412118401002e9007020b480c1c000d0891040c0401d4018175010300c0c02c8603405070300903040e100b05142540c1c00c08065070061207a0b03070242805001400a040c010f000000b050940403003d882180d0121a08602420700310400760f034848500220020044112000c5100520080c50b105840f589030200709820a98030070b0040f80e058200020781c2ca40d0280110840f940300c0a80007004d0300c00c03460070350100c000700b00c075040082a80d482c0442c0400d00d40e81101c20311072030075480c1c40203020088000d2200c1e500d0307003d00300c629404105101c80d0248019240806403002000140c0b480300da01d00a03465040c03522900b9076504070414080700040c03000c08482d051500080250380000d6140c9403460b03020403028400c521a4420948002c101280c490008105a06001040b45401c0c4202c0f0b445 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 778297410 1250 778296160 778296179
    0xd0e0a0e0915071b030c110a060c020111010219080a0f1505040b0a0503070506090301020c06070c1505040f0b07050d091b060201090c0509060109030f1203050c070f0611040f 76
    0x100281210b40c92241002070085481060881d241c0d007010324851440c41000d0350151020400090119411000701c0050b00c8aa190000148010304480ea501701d003c4d10280000741555002180d000313500e03401040304012811030040c542c0411212490014481e0396800001e400909003100d00e1080c081c1090410580f0051070190388054860440d0200306680e0700d03108100c010041485001c2d01078124030400c0147d840c4c12405840b1501e030140003d03103000b03010811a8145603044801d0004254840454024000d14031120355140c0844442003242d400c4c61b4484940103e88014000c2041600344c001650380d9200b0410f50761801d01044003405400240c1c541002c0c15281c0b0b01485000203030340709000030002e205004a28150340c10030303403000600381080180908070000800c541c1c10301410f0580000050070000d0b000e4000760180840b121200c00001c0c004081d034501800303285909405201d08004201a411f1003500760313901c0b48000943d40d01c00d10700580a80569880000d40e103010000000342d2091 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 778298660 1250 778297410 778297423
    0x151503011e050405040302100509030906070516080718020a0c0209090601091b05030402060702151617031509040501110f04080c040e0d0509030a080403110909030c0d0e0a0e09 77
    0x441d50790780320290b46032010300040b10780840e40a0010b03030003803055141080840d8050341c0c00603000029a4904244500803495661040b0021121039101c0000005607180000c40d0001415105010b000d21078500850300c806107100303a102c80d04803503001074000b800c00d0144900910709a8043d001544524000701200d48505092180c402c1250400300d050441001400c01c50740742d0513842d02c0302d60941d25560248181d41c1c0010000700c2c5c000c4038100e070204020101002500c01c410a040d440008000e06280c0100d0788014818100c542400a00600c8003038085440440d1a0b0b0a0a036a85050b941d141e0504a0242a000d8801c0c01c120000142d0100301d1542ca00040c801d0740c10000482e800360031410240800c035414401601080e420140b1a012014800c0c1300074903688000404840d2002e450b902c8034a40d55000750310440340b02d4000c000c42a2503040c051030295211407100055400c01071032842c10340d1a00080e0b800d0404000701100c25580320b65075020114040c2030449006002d904d08003128958418 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 778299910 1250 778298660 778298699
    0x13080307050607260426040614070b070315180b090907031a07090801050a0902030607030501050918030c060a0b190501090b030a0f0e0102090a060503040b15150301 72
    0x6a180020710a40c05000819070304410781207805000a001c1c13401c00e0800401520803219140709142d0701c41940d1404204408041188510320b0340c49240c010064020480c0d0f690710078018509000d14070200340b03051203491703120360340f400d01181c1207074a00d1280071000c0c81500007020f50b40448500c01f0700c01c0380c1607006050102c0d0590b000c0c01d03240c40d8071411568405a0388401404c84681000c94903103001e0410a9540145080c24040802500da004150035908100ca001c424255aa60b02100303620701000202c1d0020f1107404c04102950402d030104140c01c4004000308030040d02d4004469040004008403100d444000007585c020b070510000010151514252007481202d0140d040c40e00450030f201c02d1022100161188080710b46801000903a40d0030092404505a41c0c44040740751b401810300540d0000c00c070300400180d039074013010208a0300f00156000380003000020303c02c100c001110040c0e072982040740c0703218070001c8a4442d40099070410f040e0b40b0400560001100018064000c0701c00315500c40f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 778301160 1250 778299910 778299913
    0x70b16020d031d030c1003181424070e1203070816060c02030408031614030d05070f0c03021905240901063c0f03030503010806010f060206011a1308030705 68
    0x40b465a000c15540e01000b0541c01d80c0001d2207a0700c43c24460180c0c0c84402e1350140d1082e20b03c008e00154840d06004c0d600c1c10384032541c5800540c181c01c00305440c3d00a440c41c040002c0c80c5400e050801d8400204070b10348040100d405080718035503c3c0b07403462040060342c44441d400318440c0da880403040d42500400d90000c00444089080409207031545002009071020781d03a1807002942450600e801441c0031501300c4200352005482809201048041030005000000c090700c0045224186580020501d503050210781d01000003100a03900001c2c0c0c0403e00005850b09100d03003a806105608119003003807040e080c081510600d51321500164820151581c0c42078440800130042c07a81e4070014121001482c002c2000400c010131964114461040a803440d04404203c40c200c00540343d0311f081044500e0398005402244008c0b0041040503030400105014001c0302c514481a14a080741c040d68a02041c0101680030320403140803035880303ca00c01511810200d8104840c402951034500f90346a40c04a2406d4406 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 778302410 1250 778301160 778301207
    0xe180702153612070203060a0906110a0302190908030f070809120a0506070504030308040b1005040e0106090e1207140c0301060f03030f03050c25060c030e0f0f070b16020d03 76
    0x4484818041d0fa11141d0050094000f950b00d650604c001000c9c129000c03182c42e6550000d00208600c0c001c040d200041030b64034010780e83c0689940850345945420004001c00040c01e01c1444080804400d030b030946420300d0405a125a1245814443c60040005d255000346210302400300c00040046c24500242c0100c2c240c45460702c80002c1261540708a000150101e12084040780024007446040c2d0b034454403002e403480640d0307150b40004e8103071029004401c2060703445000134080004940b04464503401b80200803d1500b01c1ca0240d14001d000c0d444001d0603284481c5401d03690b40078144104945410000c00803c40241c4444000800036075130f01051313000602c204200005140a8070400b070091362040078007030130072520f8801d904110006070f407140c1c04107100c00c000c4000140c0074010424080101c0c0c40204400411007103003840d10ba02100f005106074000e4038040c03007080000c50084144c0b061075a00e00d90382c11058040010402d0b1100c80290442020b003e80018181c2c4500c01d03e5003c3d030f803400c0740e071003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 778303660 1250 778302410 778302433
    0x20307170f0a140c01060308030a0c170f040f12030f1802010c0b0601020a0b090f06160504051512090f19020102030904200a0e1807021536 61
    0x340d0180098006030000304114111200c0e004103020544050035401d01454038400400c41070944626a00807951000c002c004d0000709a0540500042d0007540e00e0b0580c1c00c0c07210315501c840c680c540540340c00c1c030003966403001c90180440342401c12034841c0c0040c030040d02c4a0003c03000500900040050160f03c170318118011401000e94091080340fa42c050390751132441c00b2151030320003210a0281c4002e0551140c00b0407030000610b0003290500ca00340d0380d400740c10004207001700a818140000c0011581d840c08080b292030b515004010344040d5001601c5400916546017a80310840c481c0c003802c83d0101000a041001c03401d4000baa000700c850b0804291a25110140c58404400c804248000d000d030300280500307881c50030281c0c40625003c44c845180718a5445105403458141e00510000c3c001514450750341d00c407402d2030f62848120210340d103854505850b00d40d2000f9260307503040d010103201030301d81c50101d80a005550708200802441a2807504006280380d0452501c5101342c03401043d0b030062001485 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 778304910 1250 778303660 778303703
    0x1090203150718080a020907020f0109030909060f050603040f1e110a0803030712050603071a071208060d03080916062006070905221406011d0604062a03020307 70
    0x4007144e8010005003841410b13982046080301008140004511500c090401444002d01412004501980743d182045003414906025643e090b0003d541c0d9400040e420881c513100c0e60f085036070143d08140182d03010215442c09110041c4a10750b08404804100c0d0000140040701c10b607004481005c484c0010100c2d82e0b055150f80f03a010403182140464285424401070b001a900038540c000310040039540d0040c0c44040c45a18900c000c6580804810003044010402c03901c00480c7d8440303681d070705064115242000004084000e400d800030108a000408609030700310411110804100d40380320311200c25204d500c002c182e940b10701c0301d00844129802a81611840c0860303000d004032441d650b01d05240742041c080c040d0002c1010b013404070a07c080400b9140c49403041c0b146500000e0381d0580ca4111b0304005c00010182d400c01611780c901c503400d00c480f10f001590f03544101d408403600c90801c05902d0f000340000d000c8002c0018011181550365900190405038040000c4c108a48039002c481401519a001c40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 778306160 1250 778304910 778304957
    0xf07080108120a0c022110020403050a121b0b0a1d0d110304030602040f06110c280902121e01151803050d200d120e010902031507 57
    0x1c04803604280c0c050107221040c64010482c40c5051305003041c043e242e41c1d02007540c107030780b9800e28400c0c062500000c0004c2c0c5c409115400d03085160040660400e81035884064603004001001881c50003003140b1171200318045c80c0751120010742016900240c06060500900c0144220750380d588980c5007080314500311440d40c1c007880c03645000000a08907250540010b03181c0360401c20340d01119202c1884000005225800204090135407140c0c403202c401e183c00d07000340c0f03240d12a86c0b031901c464218401d50784443c2c6802514050701622030301003020b0000382403c10500c4c07003503540002203601d00010300140880401c0002c2c030b001d00ea02c000d4400c1500030384200407000c011301b8041c0c440c154084489118041d4460750301506622038000364a85607503503d503151887c00a0502d80c10022500030f01510402c50030310b0000401c0b00303007043d010746003880c040701005111031114003260441603030765204454000d80075405000d03065809001c44079500004a000402c04030304071000000980410700c03d1581f107003003501d103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 778307410 1250 778306160 778306169
    0x6020715080606030414190218041a060a15020318010c02030d0c06110309010c0f0302040803041802070506012304060e01050907170c1e0f03160504080102120f070801 73
    0x200c0701c1c161501c40400106600262003641c8041d45204035106089042c00110f42c000c0742d0b0f000c0d00404002a106124500c15040490341e850042402040081400141c45c08080690510a40c500760386881c00900c610000b07801010340c8110301114001c03001c0c0c0000080030303406102d10070851440d00c0c50004507000220303010b00031b41503007103aa19403c10324050001401170602c01c08020400c001c0240d01c240742500200d8600c40547e44400348003090503000181b950324440b05141c194505410011100e0340c903c110b200e504440340505188a80c50641541500c41d03081d030000c280c45280d40c1da0740480031000c50307190030032000a03070210301d408a80c40c0c40d200d6101202c00380302a501e0ba40c0e00c0c0c84100881c00c070004041105004180d80503040742c0f045410344912589641c1c0031107864024030040e5440f4040c50320390551f200c9008100c500388a1030300400b034903031240080d00e50340395400b0a14000c0791640a80d9216038895030010a00304a025010309032648940d921125035009561000c0003203034244021b108 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 778308660 1250 778307410 778307417
    0x80c030703081606090f080a030c021b150405130608100c02120906192a0b040f1a010e01090c0f0f0311090303040b03041223211006020715 61
    0x4003103012905807844508240200d1001441a00f142c0f580c00100411006c11200c08100055241030103403d8401c910750362a140c802840006e500d1055030074100c3d02c01e030001380b103105400034900010081004440c080e200107000d8400d80c6d145012400050040c0780195142030061500d009052006807142400681560b8000c00300138006052500180e4098071225401c510200001c901c2034143c0c10740308041c280c043ea511520844d84d810340c0c5100c508050780100b80703c10305901c20001324a80d01c090a07041900a01c10f408588001e16064088050500c1988041040d04000244440030744424031704172070702e4040501428164290880e51388180003041000305448483c000396891190348019890441d103d03540745884200d00010780307940c1007a480142d15900000c01c0108012000b1100d203074041103400e000ca505085884041440020054441c0d807d440c0414241400a41030201840321910711640711030301c0c103001d4a0060103048900400002d8401c91400080a888a40110024440030b54 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 778309910 1250 778308660 778308667
    0x170d0507050a140d24090f0207020a03020609030109021c051509031603030204080106090203010f0506120a050a060e011701060611030a050d0b04141b072a0f0f080c03070308 76
    0x400c48560f081800d0704d407130003a500c503401c080b000030290920b6a042c012a00102c005803804160314240c9000355064000140148100001030f00c03001107481c283c4c0d90440780243c98181a00129005060480000c0c0d4003039920260a10080418050340a049000703405640408800406207601b031082039654245c06d40c0304001c2c070800e10304c01402c6000390502c2450050714050351a40800c0c2503403043d40003028400d5001004001681407844144001c01d41030341c42d6070904a89041e1001f4510006190702501600c1d40c0000d091305146500007400b411a0030901012561600d80055407007150410a90866103040c1000c980300e4024030381e41400c640d040d4005e510701a09814200c2d040d03000280c12301007481e01c0d85503480140d03513940155001e00502c921540d02e0f0749082c26003842078580c000c00c02c1c14480c00800c154004104c5010b61001d50f85200088200100050f141007102d0008550007040060000680440e9030002c40ba0110b00301e4080c40121041d005004d01015203c580c02e00c0010404035081 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 778311160 1250 778309910 778309937
    0xc030309050c0613062303010e0a1e020405120106030b1611070602060601170402010503070521070e01020106230103110c0d020c1c110f040603170d0507050a 69
    0xd8000c500114810740c15142c000b201c21011890300d03041042d5100700a0b8a91005002c201c0d48044441581e8505072440b0b85041c12000301801580b1040c0101d00d0440c49401c00581c00340650340161a680000e81c440441041102d00d2160094000e4028288142c036000109a50300c0414080c00040e29040400100750342c961150310201494488a0310017441240d039580d0350001d409101070802000c182e0060801031600000040c0210444d030b85001e441c5401005010150368481c05a9038080e2550411a6581ca04100e0440e910120508015440c0d9081020840e070107a10421034a002c1c203003078009109a0f81c94019a00c420281c1c5c0d4941185002e83c0315030f0204542c42500124108030302140d0b620720b4148402c0c003c2c1c0c18031010550040159011009034420fa007442010070786203811844444100103625a1400c203850941403400340b00d03403840c00c0c0030b50300d030740d0303694420310046504c1001d5824a2048400842061300f03c4100710981504e004d0024001c0c500501c221201c100352550340742d1400c01e56 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 778312410 1250 778311160 778311167
    0x906051201180b062a07151d1903020405060d051f1b020706020d03050601080a0b310c170c03150a090f1109010e01080c0d1107210c03 59
    0x40800c0c0c0100b00e0380b01e1908005544481d40100140481410b2001c01014840320030011660650440007050f4003040e010804490b108100d00c9800c1c880b464080d8107610200c0201c10300351a010307c06a40000020340c1d444901e80c02c81c070300004581c4241c4080c082030790740c2070401c90840d10075000170b481da030448084d52040c040104158484802903800c0050844c0c1c40d44c50310410a600c5881030380c09648900ba050200380c1d01003150b141112420700d814049458000d000030407045010300a484801d854072440c000d144e0307400b5600c81a001103202e1a080140b0690100355692644444840041d0301c0c201240c14080e00ca00701d11200500391100100e03a50300c6414411410382e0006040820441c2c90001d5039130a61341c0d4485a1340244901c00340860601e41156030f200031601180881c180e060307010000d5031780c0c1e031741c12200c0b50700c0c400c1d800d080008070740c0d0341c401c10b0010324854000c442e2051881d15040540001094010f061954050040040d204031038409000e047d241c0c40c0e00c4c0d280402d03c01401100000e10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 778313660 1250 778312410 778312439
    0x190f0302130e03120f150127090507030c111b0603041b14030d0e1f030608060a061503050103020f04090609050109081902070315021b120306010906051201 68
    0x4049000480b80c0e07010600a0564112040040e8090918424010000c1070040e003513411070101c000940e1502c1c209000030340540c0010524210340c2d070328241100d8111040b51058802862810001d01082c034007600010000d01307805a100300840d61417103400d985c0c29400a4801d00c440b50100311411980403070400c00c10142c00c0208222503442010321040c81405080783e0580080c0f4410141c00038141800003010f05040040d0721040400040720a41030055a03180d50b0001c0e41204424032085e10469910700303d016100540000c6254420041031003000070142d030252046940000c10211860007143c0220203660342032101030f5019504809080d01132506901c0030901c0b510602001481e900b450752040d0940700c080205603080000480e07108078084207204010f81c0132110380f014003409415a5110b601c0d80e224000c00f0b6040c240c1c046550041240d50007401e0400d508554200e030040b841d17620910141d40e00403101680020300d642d00004110380601c1c10307202c000f44401c0fa2503005038240414104c1018 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 778314910 1250 778313660 778313689
    0x50a0909080f0c1009030905091302030c120321010512060f040210210501030203070b0c060f06010903020a090507031a1008090705060d0203090f151f0f0b0306190f0302 74
    0x10203400c1c5045004a105d02d074600e900c00d4036086016454042000780c030b0744008140303038840c13410131043c440140c0e40415940c405a004a84034016480c0c0c0307042551850281c29000a0500040c4040701001407038000014101d500440d030620405594040c500e864000640300745002c50544008140185842c124841d00c1c0051490840150300a0b4090020b00c407003010380e0325200729502c00050080d030034184041c102078480180b51900d080e00200000b95241c400500c03030705801c0b9850005c283d6036807162000c40010342d002000341a14980714a5040d00400003a5040c20100e40b44c800300c0000b104141c0309441e210301d0000c10908001041200c01d0329503080041144456000340c0c4c02c04a507039070b0341102038074000e00709080040e03c030f10b4000505880e18441c1407071840b46a00510600c000311408125095024210090220800c8940410103415a041c0c0d00440d050201703200d4003040e1000700b0000b641c8108400c0352051603801c0c490103080003000e01c9000d201d00d0a04c4403182032002d401c01c2001d10051700b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 778316160 1250 778314910 778314913
    0x90e0403050a02210d11090604180f0204080f060601020a0c05091e070203130e01032a08010207140c10080106030b0316080606030d0513030605040f0f060501050a0909080f0c 76
    0x1511101c0422110040b010460740650011031200c0ca50102881000489140c80d4a810301e041896400685540600d100c1c85100c22901c0ae180c0c00304800f240c1101d200b44030f1000307007552100d07100c290142c2c640303121035800b000c02d01c40c040016403698800900304100030b070441d499580721420310041c01100b0000030031510a41354648421b95080e03c1501826206d101d407075020b19211140f2402d44413290f40d00360f00942c14502803100510105424000b10030352000c045288000003205180a403018002c0c0e50f1001006500c08101c10060005c00c40f1405040c81c038107016545c03a510924100001701c0410b48218000501e140014011280030351701c0384517911030090450f21443c0d0000800e80c0980c410741c004003400e801c540140702903803d04010940000d80705040c1581891140c0e600200900d00501c0090403203074503039002c60306100004682044007030300621803840950361400d04d030015080038400c583c02010030481c0052a5203203480360341c0794198000c00380b17880d0036010135003404103070403206814400303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 778317410 1250 778316160 778316173
    0xa1112071803050f2b050c0709050f1006030c0e240705070801060b0412112e09301e03080105030c01050c0c0d0c0f0f05030607090e0403050a02 63
    0x2481d010400011407007000101400c004000390a41030000340c2c41c1082c0101d403040780c00b0364005804a0010700484041ca0b103d174860281a607002d10b014a254842560f880c542400d125203408001c440e40e10489585081091007561000c00b10304541c050304c4c1280c00100d01981d14030862400960181c0d40341e107241c24030800c3c07103007d030f448208540c0035030f10440e020b0b446410700300b00e000780078061400203203480c1c00e00e58101442c028808094898191009144821070200c481142d991001820718030791042260000d0b000d005210344118205160a0a000c940000d10005a13003400d5084441c100b000c543d61044200e104034010041480c030b00ca0b04503a4103000c010740000585000c0f851800c86070182d0b039a42c20755450502858241041c0c0f80b900d0f41004030410201c1000600010940c25142069031010744058081c2092103004140b0340000460145007070b0b0000310104072a00440503140c04038103640e0180c4418000b902d0700701a83c0316801805a0313000004010a0181000d041100400c1c01034940 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 778318660 1250 778317410 778317437
    0x150e011104090b0f10091e120f02090609191109030609030d060f0303080c0307021e0102040311040e0606010f02100920030105072106170106030b0a111207 68
    0x5550415005100c0c050f03a18554240a0315040c1d2014401d90029140d40c0a6044450002001000c260103981080008916080d50a4034039400100060841d91028507130720301c0501d0401040d44805509174400c0810f003011404a00c0d220403468051240c603413146803001c50300c0700d0310782c0500900c103a881164042440500001e890620000e441850400c016641e1a211342c80540c040341c40075000a0b030040040e030401e100094100201e1504a0643d02d5035945940d90b18904a18260344c60303000c42d01c202c0c4411420460071340150045c1c81541e20801440b4142c107115030a00049035003156000075691b01a9000ca45554010705079000308002c03a2055600d44100050a282941c400c040d00b1100000d140044190f03280900d07a005d868031004600070311050401400c010000e900c0541c0308201c0d1303130003038840584901c06030b030100004104d0006110507440c4d00040301402410744e40300a981c1d11480c03400051400c17986115100c0710b5000600c4040c00c01c0009501000c1d0150000c1c03401081c880400380060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 778319910 1250 778318660 778318691
    0x5010e0f10150911070c1217090d05122109030912030d021612053a050a0b01020d020a08250209091e0118080304020a03150b010e0904150e01 62
    0x450040390044582da280c08038505038002c608161f1010141014001c10032000800c4180b400415031510703100c503a2141411400141c4c9840c0c51400104103100340c10303001c0e19003204031000d05000c640d84050800076002696440180040488606082e600f080040c0ca1041c0751181096a2040c020303003c990030000810124000c0b40c1c80400c20041c001c00910003801004004034400c40342480742d203802410102c44480c2c0f2403401d94000301780c801e0310b00b00811440031100406050341c26200b080c00301f0f00c05400d0140300321005100b0506224018001c3e69058003da07800002c0040b0241c1c1d00c20a0b8518021401c6d0100c9840d04401ea282c1c0ea001c001315030300101595460034514003440c0302074080d0105031803000c0e410000e1448180c1790800b69051030701a010035650460044a12a0400d840940d640d5503440010f40700300e41030b00000c0c800c000600c0e90108000c10342c3e204000c040700a80b0358041000900c0100040c42c0300c1242c004140401c400403003201c00c941030300600d00c561003280003c00d403200e1100808 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 778321160 1250 778319910 778319921
    0x31207020304031502120a0b01111905060f0603150a060306020a0215100b090d0f080a0215010b040e06010f030b041e1d030f221205010e0f101509 64
    0x8001640045000e10a20a21810000f156140400300f1031401c038040d095142068001000781100b15590780071800541d0242100b85448800382e400c1e81c00f51450070f045086901e51b150820382daa40b103143c00164426000c0300100d07002d00401401400e80d4006400001d055400040250510039115100000014624005801c1094454010789840307a110072880d1580c003802000c1400c2c0801c6035a040110a0020003114412001910041100c18075810185403488058034000e040c81400100c224003180e02140c0700302c0060a00030541080d90380c452000361580101d0003106000d652036404a0340d158003a0340141e0500c0c451f0b00b004070b400345100000404481e007100f1100301700c3d00750980d020001c000034866001c0040e402c09851001032031a010340c1d80c0c1c2c0c0c022100219113004000030031484144510861131a844002c080101d17071251034820b002421144440d003128550f09110031051070131008181d85255011010007460060001c1003010f015081c0c100002c0c84100c41d000e0040b600e40d43c94010b1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 778322410 1250 778321160 778321171
    0xc07030209010f081009120f05070813170f030904091109010807050316150c0201050705010c05040e060301051b090d1b03020f060a140315031c030510060c0807050312 73
    0x1c1000c00c07844c001205040408040044061500d840191400940880151220705071030786407100d41c2241e030342e41c1955140b013000005007490700e02240c4d04a1081c0401c3c1c4040681c0e040c08408180c11400309a0329688921920070003500390400d00c4200554109a4040300c2d11501a1801d602d242e000c03580402c1740b50a003a044800c030f941090200b480b05007410800c2c004c0503505850400507080c034110b031500740c190b40801c542c0b0400840c4c1d680907065a20840176a00c5254100303000704140800c1941c0608507074401e00c2132141c641a2480052028a0306104140c40b50a01c500b07180e944c2e0a0342705402d0134660100880c240d20140c079006020105600040604070043c02c2403101c1500360850041088040c042450544990810401d841200743e200c000c061428001102c035030340705e848048051120102c1880034a0305441240340d003090714039540c440101000e030580c4040084d5251041400042c0c1707000c0c014000401d000111104c0041c22000007800118050002d40b41402c568290222058600765030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 778323660 1250 778322410 778322429
    0x506150c0c01020d0c2d05031206092d0403110f011401081c120209040c03020703140306030706080a0204080a0c0e0c0313140f10090c0e0705030c0c0703020901 70
    0x41c0500c0d60100b004249520003401c1c202d2803a42c480c0d40c1c94102ca924940e0041c83c1c0181c1d000c1400e52040c3d22044410703616800740a49448a83c40c4549480c07002c002c503a06841058131501240110385194000102c0c800140e4212441c200c62140408445101500c00c0302001a2203a0740200d0002c20b111154081d02c014001103401d0501da04416049581038214000c01e8100300c90b2040964100740c01000140003508050314590081d0b08198000d0240d51503007a0040c1c207150000750090380c542e0041008600ca0303128800300307d640c4140581640000ca42c490342641c000542408601d000703412165020005140c0036103440e40380c1c5011800c24805071011900c19003000d100b48841d01d1440541c40d40309900600c100c0c10341ca0032031f588185084030324801801500c40744080c2c807101c0c03d09100389a1005c040c50100c07030015000042c410001c01c0080f1040e600c0808060011608080c940403607801410950345071821a11039048041c86544140744107000382c80b81000010060302c522070b509008081599 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 778324910 1250 778323660 778323673
    0xc040302040506042c031608091018091d0115061713030509060c0d0810050103020c100b0a0906060201020a03051303021f1e0e121206040506150c 64
    0x8103010030341d00040d0886104030b040500415100c00e89214006288002160a42450100c605031768158400d1880421816081d0f81080381441040d4008088182054810304910b814010342107440c034840c042c020005040282c02000704601641100420f511052120341c0c039010505411401c4030b0f60f540d100c80c3d500c014844104200c6400230390a0314581085c042040340c1d803420f50440c810035106490000d0610001103003172a26500c0303810507a42106105812100918043d00001c0e2203044201c5081403402421100414694400d0003a5104400620000c01907100e151510070094200340840c103800c49205c01c00000c4d001c0722809a100105945d40005036908201e540007403c2d0340b401000c00c94039450310213900300000d034005031320720303101c0308100c008200445107000703020280105007d4441005041025500484020b80c0a900c0d001242d1003190841c03500402c1240483c010b148071480b05403103000014981c0e0070b058001c9640044024172901c08068180d03000862a007029520040552008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 778326160 1250 778324910 778324913
    0xa1103040f0501230d020307140a031401080a0b0105060903030c06100e0c0306030c090619060e040c0e0114161703040c08060c0a0318082d0310030303150e0c0403 71
    0x804d000750540f000c84050109001e050075114403840766640070260540c0c00000030350b0b924800c54401c840380b2400110781c3c0d03072410342480050103010044010101500700c480000b880440c0060100e002c1d6074040851602c980c83e01080219940001200d503815010030406070700d1703032041804294821000001034025003070030030a60307202c1c20400603c2e05020a80030414000c1e603690025000e03003000c1d0221603103140d5070b43e400c010032100844100782d020085200d100c007180440d005000364007009000d407001c0040030012181103070603160340240c807804607000481c0c1410354000d110040034250704244146042030541c1da503246c0e10040201c4116a05200802803104001a0300410402004018004c0c00c060400040c100131038402c4072542c0342410344c1c9280c94122103034094014800150003150290311501850965040c415841a0145a00c03007400314100c9030321000c03002d9901603408110302c0401d450642d07405070002e04006c00402c00c004565140010040e4950308190b20541c4070058507070b125480c1d0f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 778327410 1250 778326160 778326167
    0x3060e06070815060415111903021002040501090e0a090b012409080c010c0c0306050411120616111615030609052a07050312070806030f0a080a1103040f0501 69
    0x191584403000000e000940c90b030366030013081d80c040c0c8507401c040400501d044d031820b8840011a625000c8580940c40c5240f800e80604040284080e00079001d840981c070488100340128480d6000342404140d01c0c0c00c3c00d01c1103582c0c03c0080c692120040000003481086921031445d010000d80c0000c04007069504009484d8404080d001c1d603400c22800c2101c6c4075030400d000c0b1074a9586a00c45a410005d5409002081c1700c6100101d034011608038600300054106414514038030303181080f00300c2c082d843d0080b402000080006801c3d120f6065040c09038002003440f242100c08200d0510b440307030b003445404507900c218021854040024828060310040385561580080c09a50b5907a00c2450424907100400c92404400a0041000c50301458000d07071a61001030f440c1050b000e01c100c0035082e40300105078004407403e00c01d1034500864842d00c03075a6190352000101175444544032070050303d41d0041800800041c09890140800c688241400c0d80404c440c1c0a10f1481c641041e841146e940704041ea0070802943c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 778328660 1250 778327410 778327427
    0xf051006080c0a0815011e1205030301090b090f010e040606030218010302040c02010b0d141207060e0733020106050d03080f0c0304020d0b041505280e0d1803060e0607 73
    0xc4c0840680070700f0161960b80130000300305124182e68680d443c0342c42c0070711f18410b035504400340810130141b20500d402418103d940350424001c0841c100e20300344140b0b40500d040c041c0c0a01c0b9410f82a95419540e09041c0308043c55500a4400c65800703455040100050303841450750003403440000700c0b04181d5171550040101340c5494401321420340e4988040c4074459154094513010180d04001801c05d0000500203031498001d0550441220030744c049540020030445400c0100f040c40910201e45045445071a9030700b0148004110f40740740e005650141600614005407058003040c10700002450f155900089420709c118590100d0005028004101d0680c0e003c0101301e400c41100703c8840d0640c0307041d60200b03c5100b101c1c0009081e8601fa1400907003004542a641030341003044100a0000f400c004588d551030100c2144130410410aa40041e094011940720710b1854406000c001c0803101c20101d002d69003c1d40314480c6100e141500c3c100400820080d0152014142440300140080d00e08540014107459 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 778329910 1250 778328660 778328669
    0x309090c041406030414060709080c0301061511070806011d1b03040803100f090207050d230f19050a02070e09060c09030c0d080a0306090204030209040f051006080c0a 73
    0x800a0006106025010390602d15111055076844c2c1c0e40d4503035092603584007900d45469400c0d40700f100d0801c2952903001c0030710000c0350b000008440140e9200010142681c985021b00c4405100d0740080556051141c01800301300300c1d0b06020b403800e6079280c1585500f000426088048a00c011024000986e20405c2e4000d42c001c45403c400c803c80d080000307000426200141001c0c20030140030020500c0108109513603002048015118014a5a03494915020350001d15060300c50b402100c00c1d0b0003550b409a0b0a44083c00300000300300212054418030401190410800e800c2003440a20140e150000707800b03070b070145540c20f5855194032428900710003071400401d40c0000c4005160702d0b05001d0710380000545039030004c981c40001d41e1559540c41c0424600543c3c06103640d03200c001062000c0901034503100078540c1c2c1305142d6042c40310726103410301c210580c8550320000790001c0c8500d000401241150040b4580c940c03281c004c4e00c000b200c80c04908000e859403504a681c0b40d4000c007003604134610700010200000e1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 778331160 1250 778329910 778329931
    0x70b0c09190b03040209040515042102030a0e041a040204030c030221031c090803070c03080115020c0d0305160b100504051302120f01110d050a1806110f03040302030909 74
    0x1203091210344100b50202a000070302a401c0d22001c01c0400405000e0114060400312200d003491415040c81c0551051541510301490210444d540245101104032441040e0a413030b89815030020300c007404001c0100c4800c030300d40c200918000707881583c0c0b64001480210f000312030710f46149040d401001044100307040d40388132218180001c2e0916031404400c0e500c0c68081414140410b900c2080000302400800400810002c0004100800c0c02d40000700d265115000386d803a1441a0b0302c0707000041d040e000307006031940960300c641d4510309546022520200c00612a10b00700b0700780541e0120703019440c0488041201d0190b9040100160010713640701030001010200e800b41b20a00b005e8018448d810301444001e030258100f0000500002420070991106010440003008040b08a154201d01900036913180209a8209004a0b5a039501ea00400d00c10400034207000950407401c0d511003000749020400e160380f00c0824004840640004409184a140660061596041360b0001c100c007083e001084101923 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 778332410 1250 778331160 778331209
    0x100e01021b0c0a090f1b05130e0c0409090c0f06110c0604050901050f150a0e010224010b1303060f02030402010215040c140d02090901150f18020906070b0c09 69
    0x15540d00640902111201440019981241c00c9410054021501c40b43d0301c61b400c441007402050340c0440104001d940700071441500a460f1803040354115400d480040c00300071300340400d101850310390703201e40e4955101d144505a601c1c0d82e240c000941d003065074404000315008081c6180d440000f4400c0060707042e4111f5040745010b041c03000044034082c060040314080d41486814440c2900e80b0b038880c941701000314620b2900e0316803502000301a00002040d80740140241416521400c0d1040c01207540b885140f6030450b0f59a003800100700c42034005006407103a80319116000404070390240b14410706102d0080c000f503568039080c0000791404410a140420758000e150800c0081900500000251225880c000c8501d4000c6000030302040d500b008044d51021076402403041e408015486034000051105054900f0341d07580c0398801240d2940d100c2c04010064114131003c010510754001c02107620300910f0035050840f582c0701c2c0070001800311108031108400040310502c51500000c055944080c02c507000030f0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 778333660 1250 778332410 778332433
    0x60c0b0907080a03030c02101d011a06030601030903090e09011a011107031e150c02070e090d18090903030e010b0609030a02092a0414010c1a09100e01021b 68
    0xa0302c3c40c40d040d0140c01c150380d03480300c0f6984520a002d190704000e6060024000001641d040c8001d14928000404841d8642007000300064100b0009408001d0000c1c0000d085039200c4006402511508108030208448540c0c0800d500e1047d44c1118062190440001010180404c1d0400600d04051005060001e5011654599100004c101007507a81c480c409103280e1260008519130301496a8004103c841e080b021480c500c1403a5200228011141c1d0072940300b650344900740d074503c00c010745141e920307600100700050b010b50040000c0c190044951b000e0915040e522031100b002c48031101c0c0100c0c00a0b8490f507840360031103000d00500c0c007815001c85102d807a020b15100029991640a90000d00600c03010002071100d0004440c070307000c3d5007911001d01ca24002a0360041d0300316401800f890341c080d1008400c0c014103501c551000002760b0ba1044068511580007a1040c151440040c50175420788180258290614840d008840c8070895030000507849020344024416801c031060f050520039031140c0e11641 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 778334910 1250 778333660 778333663
    0x16080c070605090907080c03072a050114010605090105040e060f0d05030304020f01050418110f13031a0606041809320d080c07030c020a030c0e06040c091a0405030106060c0b090708 79
    0x80e000009c60615408448102d20424400c99080400340c150a81801c941028400d040d08842002d284100e0f0050750392ba00c4a6050310280101c4540f00c3c00602c0c00d0105011a0140241c21900000002c160b0551515614005105160301c010200d0311900302009010071801c14461a48406000f420101d00b1302d420228560308d55440442400301043d104c41e150701a0610001c00c40b000344400d1184540d0390401d01d210701d2501c9a042c4400ca901c2d031444a620050000a24499401201d00a00107442d051401c1899403180c40325541e282c140c1030765aa22100090f0750f4200044080000094644613518468004440c403809104c1505894200040b95402e2543c85202182d03c5a12080b00d00d03203556442c24105c800c0081104020b40001c0600340102c1403002c03104030300d0126030015010003070642d110b5080c04141ea516001400c04590f440300240044499800502e002d0144424500d040c03e03a21000242034601951101022030240e480c0712080c00040103515a1014124004007205443c14403078a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 778336160 1250 778334910 778334917
    0xd030f0e0f09040309210f030518040e0c100305040503090d08070c14091e040204021c050f01170706090b090621060a0501021216080c070605090907080c 67
    0x20810400a440088055038900c11600e15161001e0004800b924181c94040e0014400e80101c02242400305a0102e0380c6024a01004415500000c1d150311603a250f0340c140c5d07254100c6101e048100d40004c030350b9601500c0f81e1281e032502c03094400c001c0850304500c0d001c0c07010b010112510a0105030508040101068001049039854007041e9440d07014254982803010141c0100c1800030300118051100144043c00c05944400d0b81d40b04171104403041d15512031015492202c411b400700700c111480002005468a035014020141102007060829000c201a0b601101c82c1150801802c0580200502c000c10070745035504655031108000300005070500c54041c086080740e200d8441d2000000031b40c02540d031115010f0b02c44001d18002503440c409800309400e000b11504494840c0101c00301b010010b180e62000458000076947d070420f59180001c20004083e0740020a45e050301e054504208600400c0400c009890050404c0c0c1d49043d100e203040d00030042e00c0b4002609050070408854144081c1520740c9046 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 778337410 1250 778336160 778336187
    0x30c030b0d0f0201050705060718050906210309061b010f020301051503040204090602270603072001060b04032f1c03022b0206160906050706020c0d120b0d03 69
    0x1103141000b002d00c0122120b01c02c40800500354003848091003d21038010414100d0b8105034210f41d083d464498090208080040318210780c010303412225a514a20301040c454081d00c0e410040c1c03441c01000741c0102c1c0199000940035a10a0b2924400b04900c010070f1281c00109020b54006604e1949040000307000b551520a00780880c0078000702007011503545a1111803840d911020654903501310b090350b842e082c4a844240f891041503070080701d40da403800c0ca0449104008949071440300d00300d00010110211403544410b5070566136100e0100e42c0e005404054402944200f1142840b86020504100d0740078581c002030030702640307041500307810780d581034015002c80b140d04144d000c5c0c001d441d083c101d00c4c10340310050f003e5850210b66150902580b04602010780010300c0c1e001c0f11980c3c0c8503100c05607046900340618100090302c1c0f4000b4040c0300c0c41200204030b11030152030007504104605100a08000703118110102042186040d80c0340304600c0c0c003c0100c4004200c41c5102540010b071030241400302071490 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 778338660 1250 778337410 778337423
    0x60105030c0d14030904090609120c02061b03070b090d0207090204030b15180c0c0f0a0215070f1b150815011808010204080a140d020307020108071407050c01030c030b0d 74
    0x4020f400c0d1420000e07615040c90042c0306001450310303030412400400007540c082d00c2240c8402848041c150045000200141d03020304441d140111802d41e40e20100c8800e0580507a85c0420001100400c03114032403d80128201030141c108504030f000d0117450001c5980c412010903005200410100d15103070117042e0710034081c0307442e5030413a01207100040561030080241e04504450704140f0a000d650031000e0652142d40004460a13404004116581c41041c0403000790300280044003100d584050801802d1414840d00344070f083c803000d03540c0303070318000408006201d0703109500c1000b0404112051800c4952059600340403034513042c00501009280e41780c8640c903041c442400c03c1c6543d0720038441a60002050440d000310b440c0c503140d861154907509000420350744002258503603a114400030030200365094007500114603080e519801501c900c0801130003981888140c003000c40440c3c0c4030380b005181d2940301e40050010450301c4000034080b592550007520425240a2000c8850303202c0c0000040a10340201 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 778339910 1250 778338660 778338683
    0x4030203041e08030d0504031d1c03030908041d0f1e0403020309060d0603020f04020a09062d0c0b070207061d0a030c060c38090106080618060105030c0d 67
    0x2214200907581c0b56102c0d0400d031000185002d1070b03155540c0b0250050384241d842c0c0381c404480316030701c481c4011070745aa0356200d0440d810024819001c40102c0b07880714840d0030080340c142c1c007a0303d5203030941c0c0240d800a200303903503020071075038651030041c9009078061540c600d00c001c0750038801416028120845043e061074032500f23000c02c0504d80208183da02903440101003550381e500c54440703000a81a18481280610820070303142c01d00740b41078025990031342003d55a04900a02d0030400701c410050700d940410b4030800000c0f0118008a0200c2c030700c41c00c003119440300540c00420349400c0c1810b200060092085401442080c0301d45a030050301a14100e5010700000c013031b018001c0c0020400340c1d10340d0004004841a0b0340c0000c0c1c068002002500f1140102c0301d03c10751541e404030f5020611003140c0031995070410344d01c0034a9900410940035070000655000001c40e6034407242d216281c0141941d00e0030003070220320a0340303085010810507a805002d041c2e01400d01c1c102d10344081414403040300300050400c04c924 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 778341160 1250 778339910 778339949
    0x10b03190903020f0111130902090d021c050d0302250c120510050f1e272d0f24090319030606030b0d0213020c070801140a0b03060403020304 62
    0x2000040f0390784404e00000c110380040304113600040d52001106003640b1031051400901e0107c14401e4914500c8042d0602054907425820800c040000c1c08980044108641800300441d404202c1c10706518030380c0d100180c1d80c0010b40c2e00e5015000700c0c03a220001c2c0c4460f8189903400141308034111030440c1c0c107030000c03e50102101d00d065800c0030a00c803521b0b44410f02c1c08040120382c2e514403004c28025a0265a40c11000f0825003803840d40641c1121094032120501500203640402c004803c5090202da070252925030b4050140c2c075103500180d01461031200e00c541e032005d51701041408452429500c1d900105204601d049180c00100c84003140070542649000c0020203641c414012544038290540c2ca410755900f0066010700246078500030500001e240c8000528903080c2951940b14141d002040241c0112001041c800a540800e1070000c2c0e50051800c0000c4c008401d00601d02080002641c41503a0720b403003003649046448100c442c600c00ea10103810710011980100c111000e64429207132020000d0041c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 778342410 1250 778341160 778341163
    0x216030e040234080c060f0601020f0303070f090302130b091503150901060f080304242016060503090f12121509191b0516060f0608070e010b0319090302 67
    0x40f0080076001050014a500c1d800d0341c0400c01e00d10980150078024a292a0300004a035209000080465242e1003040407982c4680140411382074001245480340307609440342e001c42c0f40704420820000185883c2d452451151520380c246551008142d401c4042000d25800020340d681d600d0000b40000840040118540300c000790024409054400040c800312503440c1c0e40c1d265284d2162160b548001e010311044070601001d41d03410880c04190380c2e10000720400c00d00c5c0025510310140c0c2182b21500c19254040c802554200003000103045c0c85d15555140e00c1c000545078101400326800c0d0032540c00c2028501464a0204287e43e445120080d202c8500c2d56807031a07607c4410446445564010420420002001d10011130210400c2d040c0b281480950010480e01020740845a85c01c4041030061020011800e8940e543d2110740b0b010b05004141841c03104414400c468090700040c165402c5054107000c020303c0c01080d00c0c01844a0b640c0280741d441d00c01c211481c1501c540c1546480d80d40c03900b1030102490320 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 778343660 1250 778342410 778342507
    0x10212090906122d010510030b071715190503070b162001020f0a03210f020d020702030d170c0702030f1002091002191103030d0216030e0402 62
    0x203c0d0700071038800b0300c04000442084001c20b2109152141c005411100008040c090140103c08000d088003c483c01c41e0341d44004048020142002c015040840189a058100545010748948440354005440070000d10a0340060441106240000c1c10701c20811514001208011144088501d54a03030401d180e100c0ca4080c910396025051074001042201c109400c1c40414109a8090302140c203401c4150320519100d880408003c1c010810300e48681d130410100c4410440ea40350001400076400d545000c0701c1040342c00ca01755003811540c0c0400c1340707002c40c1010400340000c20b01501780302100000c046039000c0f404030300400410021034041925011074030100459403108200310b054aa030244031886060080d0082c0314603901c903034050126a04600e0011a15195005400b8911000c0507042d4855141d9211000d0249400d444104041203400c2c5241c40509000380e078240007101c440b0203506008100364091141540300301d10402c218240c008100486480c40d4150111600d100b65a4059545c40c0c1038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 778344910 1250 778343660 778343689
    0x30409090f0b0705120a0b15090102010608190204060f0e010b0f04151106060406030308040b0601021f090b15030307060b060f0403050f0717061f0510031a010212090906 74
    0x1d030070402c3c000d0258105010f8088442d803503e09450903511a1403800644540d00b10044e0000c070b40c410109400d5010038010b1981040c103000101d5150340e900b1049191010703100403203400e8000d040851086103454000e1000605000d03c0c400305980c200740e00c1e10784803034042c4211900c0720340002c1c20a56440380b0360107650003483e44000c401c402248a110190242507400780c40c544a0103044001020751402e8403885003902c1c0c2564801200366203d070340700201490080d04080c15441005c40600625540c048001f141040598020420b9080e5141001c2090750103029400160b146940027045520008240c035051a00700c1c901080c54000ca002290403840383c060704a03032013040014040148500010307666403041c0d02100302da650325983c0d00d505070740c100900400d540c1e581208010409110724003009a510541d0051ba480c040c80d5680e000507180c4144042e001c02098440d11148421820303a400400301000a0022b0143d180d00e89072036250354884c03040428440d04014011819903240d102c2c007240280b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 778346160 1250 778344910 778344923
    0x6081b03060114210a0c05010201060612050c040306050412120908071b0f0816050406051f0201022107030c020a0528020406090509070605040803030f1e1006020d11030409090f 77
    0x404aa0103a03205c159040c0c0a49003503c01075400210703948144614002c48003240e80e200e400303074605030000002c2d02c1c0250102d05607880a00000c40420000d12a02e80030b648181c85d210496084a50043e141400540c6500c0f180c07032500b00408041000d0804403002c80364040350300c0c0b4000280c42030140c5440713100e4002e0006500140320114030800000364440c4142c105e030046000c01a0b5502c104001da801601810350028000603014401d00164944a5070006d414000541800c0a0041300b4180c2c84c4c1e411901520f03d12200c080c007154540600c1602c10300b010602c05041c03010002e0301e03116521400c000d034000101040e034116202000305d092a03000346c1c0e0f44c02007052204039960601040900819036500b1800e005090000030340a00803000c440888a03640051800c6696480042d403501c08000d045160020303500c0000d900a00038142640e10861403071001c20030351070810000030f01d0311043c84114014401d50b94085031a0b40c02c0041910b0480d450301202007116140e0b89801100c0c0304400c94000c002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 778347410 1250 778346160 778346209
    0x10f0b0d0e010e15060a1e050f030a0512070209010902070f020603070e120d080c07050c041a121e280201021c0f0305061e0103091b0906081b03060114 66
    0x100d8004e80007040c004d103c111802540980c944501c100720b01c0544c210098400e14140040185080c4952004c040e01da0007015201c8641c1d543d1965418041b040354911105440041e00800f1881c0003002d82c1c0c0034000c595800c40c18441655508540300d0000f101c040c0c07040e4400300004a0702ea20400c00103180e07813400340800402a50748185c00c2c0c0d41e811a00d802c0ca000c00e450f231001881214110040d554520f03081001000d030000d030700d82884001c01d407444c520506030302d50408445031503d0b022481682c171343e8018024016089282110218a8000d4041000e0303900040c40b040030f6205514101018001030140150f100d00c150300c0140c0c40d140f0500c2509000c40c85c070344143c00318180c0000c0d8100310149152003d101555400702081f542e05503803012b40701c00d0340a2251301065940301c0e0307101400d07280c842c0310341d0520301d246122203c9000c15542d01800c100c6440712410b00c082103041c03102002c0c40d4a084804140c0044c654006a19400c05000d4001662203c06038a04590365801c803540780118200b899004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 778348660 1250 778347410 778347433
    0xe010c020a020f0f01022e09050d1e1211070b0f1803070807060b0f060c0a0c0504020304050703020d0614040b040b07020a0809010f031104080102070b010f0b0d0e010e 73
    0x1200da0708100142c1c4200e50349a0810004d00f4066221068080b050b4060100100707030407141c3c0c5140b43d90b001d8241c0104d009840780840d4070203922401440d940250010814003594090042c01c040c060f00d07940441c15101d28004130300300d401120064110307809c09004207031030040c0e404880d841d01403140c001d0303d8051407100f400030740451092031501840345100c0d26180003415922190f40c03840f5880e401880b50608005910206480d42c6c028000760038000c0100c83d4030341803080000c5203a04884005455608584030070400c0121102420008040548040d4118507240d155540c039410644000f82c040d480002c010030400103030364400540054081c51141541c10942040d80c50b42c0310846080396148503150225400500020300e10128a602c15030703003458588890011501120414a200e01307140e10b4251345000604510302500180c120940010384401e100d05192a01801c10b07407005c04520307100034003408010511801c589003904078410104503800c20704049801484a0441c60310701d0f00034400c5029 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 778349910 1250 778348660 778348663
    0x12061506050d0c0e090708011a030103083f1915030303020a0504170a030e030c0d02010e0a180e010b0109031a040f02030d021c17150a0305030d02030403090e0f190e010c02 75
    0x2816541271141d0251111801545440144001c0c000030700360382c80c02c1c00b0f07400300f561800301d110540c003040243c6000b407031801c045204203080031070140c1d1161009440c101701c28541c1742c402d10741380009664014000251040340c01001180d4901001d0101a000035004410038024001c903001800c61051044034060f00303107071103a140d20b800c2c2000c0b00098540c5400301060b00d00024400c11100707000300b07002850a025401902c908419200d001e41042e000040000c00600c2c10071000d0302d1146c01c030800706414030321410450846d10040d0404e414030901c500d00313001280900b002d00101541d5104441c2e490389032411302d00140324950900950600c1050720001a0641c04038000b07561007000c0c02c0600548802e12410340d414041c002c0304503605181a030000714411840754585030a28030280070a030149850b80c40f4241540d0043e144084c4494001003488105940644030b000103200908040300b4905102c04009007505014029600c90301c18490080d130000e00541c001c001e10700110000700888020010b01a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 778351160 1250 778349910 778349927
    0x5090a020a021b300a0b1e0c07060e03090d12082401270305160b0307080a20040f06090b0405150c0a0c12061506050d0c0e0907 56
    0x41c4014003071541480f40034412550300440c1d5041c01003100c81c00020101d00d07100e403095500d072004003012411040c009440018041421030360b0080744031900c1460114256003010134080c2c281c007007082040d000c004c6610124402e94007250391000c800309400020070000e501d036000b86a41d0f5680076540c02075500411840900444906019840345000c0b50340d1090a25841401e0b072013461894030580458020a600c1a031780c0510400030a1f040c01d040c90300700040121004102c0e0011a40e551103008a030390050070920891004100c8118054610703e00000010034000018002d04211a1100d10440c850240c50600c0e0741409225040c1036191546c40781e9849842401d0f01c107d00218003200404182403032034200700c40507200b0180ca41001865030f460ba0079503682c08402110718600580580c0d00000d84040e40a071f0007482114800341e506040c5040c1041110906200a0310744c11003050100702c100d030803070f082e142040081800010007031001c5c00e00341c5a400000955079802a010420041d00c40e0b003003080b5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 778352410 1250 778351160 778351177
    0xe060f16031b030e01050a1e0b0a0909260a050421060912030608010e030a0e0a081203060f060309071e0e0906010609080a2d151b0e060913020405090a02 67
    0x2440070b519111f810302c040b19030740e00340d40c0d5007601c2d83c0c0c01d488100d0205401c00080c1520150501204036503a05100c0c01f02d84481c001200e0041c680307504100c1480000300d1701511030312050491494140118800350452040b41314a4000c040e070172000d041c9505050400240f00380d000301c024003e1076000d00d0041c007029407481580c1301207841e1413000309403188144550b4a445098030f004519105843c0e074180c841368040c80b0403a60180040c20042846407050110716105480d6665442c4ca07401c1490820180c1180202181d014850501c1080420200001c0b500216810211b080d146c00304100284000340071250009007914034950240241e0540014105c1e04a0b4890b0344d80400700d6403036911598564145010103048072a000c00b0105020500300d0b00e8150800c5903032288808008280c1d104824021028000e0700c2c900c0d91030501c01d108c10740d01245000103101e03501c2d01c6200d60136034a00180c0c081c0241c4003081d000e50000080c0b0780700610154110f901810006060380d58501d8000581c0019600c1820b4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 778353660 1250 778352410 778352413
    0x10e011d03040803180f12061b191202090a06091502030a210f060b131e030b130501050f01080706031a01050702150a120e060f16031b030e 61
    0x1018580000300a403400d85120f00c0185180648240801141000c22031043e03a100804526240107942c50620070300d1a009180041c1c0054640281041c1a0ba26148040e070303450f100811254129004400c4107001544440c20030340c0600c2101c0c18242d00a02440c410160040c00d418400700c1c0301038001110400301c40f40c682d40e8034003c8800d540c04070703200c2c0140c80806006c500301584201000c03012604645040700c1c682c200051024080c004901990140da0200e40c41605c00600085004007200211001d800c4510f9421000d005410002500d90000c1c07002a042c081028003140b4110b00d10700741c178016260001c0c0240480e040c900c50203210a0401e110320041d0340b14440d0005110b9000f03018480e039181440700d030500300340d0300350300113681c90740c00400101da1109580f094484d8041c0040d010303001c0100707260359040c2806200402c01e801c58140560340365255006104008415000d072a09a40c03109004184082503402040b0540203400c0d460bc4030090441d41840c800c400d10b52680c06110b94419010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 778354910 1250 778353660 778353701
    0x4031e020106031e1502070b0105090910020307050910030c051e070209011d18071a0c0607030606021501080c0f030f01140402040b1804030320030901020705070b0a051210030203010e01 81
    0x844035400c81c410741100030940c1c1c8c11200104440e00e0900c26169000205d2400d80d480f58440d40307200c5c000c903841141d005001c21004540340c8428103040300d040c82803200f00d05040246007050100075003280110005030801208400b04405020782e8501078560705940540f25203840e58480005140d01c40300c85d02c02d0000c0400b00000070301d0404001c407181d40640f401c00082c2c801c0c0c0b4100101d45100484002258044620030046004280c8040020501c20440e69800042c42c9040400c004d08050315001c00c01034179805200140540c0e0700200c1c404241c94411100e007010340c60740d8030110f8103096400d4501c480d075500e40a102d03140da02420b406248594400c40c1d0410250b010765007001120400720703400e00400680c80c000200064000e83c00548405c442484420303007642c01c0e0b24120585d078401c0301c0364010769401248250030083c00301310180141581c4440c0300c2c01c0c55071040d0018610300405100c1c0c44003900d0040850243c510000c00c1502460300500240180070080c00c016028200e040040c5904d800001d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 778356160 1250 778354910 778354943
    0x5070e0a050f160c031b060905060610090b09180405010207230309010c0602090a120b0c25020a09050c0310080c0609040902040605100c0b060904031e020106031e 71
    0x54044600c952895004900b2003000c0c0c45080342e20040b410411020f00c0f200040746c40c4580c503e9003040a820744135800118404001d841c0ca2810040c002d001140940610300102c03807040e030405000000e0790183e41c112600d0b6002076000691504100d00c07411240d021580c1884180501074006012190096114100c9404030300c0d030404118000303903240300854105211218842d031107280440c4031240607800140c140703500207000406258003984085240f480c0401072100700159507050340d51002c0c0075089182011060203100d41c2c201603581e80681c0c290101d40d001001c55a803d401d4801034045a5020401481c014549101c80d600580d03522100722040d8400040294002131058014200900603a0805403c01d09000c0a03000e2407800700da02070b0f00c50030042a941c41d0203940c00d100f408280d0302d840601e10541401441124050400d0340a18405000c000110350003880340881002409150b03000000a21000c900404680c0c100030031504441c05202c448800401c04058181d005001e600f41e4003508 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 778357410 1250 778356160 778356181
    0x90405161b0305030105010516140d110f0715050d1103072d030b0a03080f09090a1a1201020d0606020304060e090402090406020304020a030f03090e0106080601020a060209030a05070e0a05 82
    0x281100100043c00c100010302581d4030607405000107100903800b200c420005d996850603882e001c140e10540d1548440d10094030340d9400340b120480d030030703910000d0200980050115900c400140c094190742d803090010484240d44103404452542c4040030007040f070703d401c1003080801c0c1e500640b407010024441218464401c03105405090708402c0d008030302c0e40e2442e2009000e0300600026041264400003000c0000003041c2014002e2216850f00a00a50366601400400210000c040d011242080c078000d10605607420203d200c941c0c2d244200c4a80343c03c114100241030280c85a00c00001e181400d003071000a000d60008007801c01d445a07615403001220200307051080080c012180658844400d202080c040340081e40110b40290000d03000341d4100e6140e0b120146903072140c2e8804c900007880303406c0801417181c02c064482d01601c03452034220418140100000e644100c0040080c000780e0b800514800c542c2d400704000070f0426806010b8500c9103070ba600740580030750802c407080d500c3d0505020000300400d84 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 778358660 1250 778357410 778357457
    0x360106020d020c09180105040c1a03161d0d1a091906090311160807050906010507030e300706020303010b1207050d021216050c07030b06030309040516 66
    0x242d40185855100d40040000900000e005045040b2840d1050f15109000b03014a6120300d01502c0e120f11040d1404c05207200d00c12802060851000c2c0c00d0052003880c08240e05540718006140c905407015010039250035192100c03124500307034440d200590540802c00224001c02d4a203124401c0a003190b6a180c1d090f43c2ca500d40c074202d107030424090b50003040026a80d40d05c54241203000785010500000c0c2804641e16211201000c0c00301c8001400301084140c60400411000e410203413660140c030700742980040d1850003950b00040274465540008500c94492a9101e03105260302510208140d10318850441c040303054903034a1849024071400440d18900000881e0304a408032100549040303100ba18003400c070903001e01500204901080000e401e58110f00107016407080a103c246100d0030040fa501e00b04100050021090000600610041d16030214030282225000640942c3c1544c490001900354841c20b1501d40d407044c5402e003400302c04494042c000e408003030b498448501d072003100c2c150b00d8202e00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 778359910 1250 778358660 778358683
    0x108012016081c140a4d0318160303020307121112090f0f06160f20030d020307171b072904030b040305070236010602 52
    0x34485401800064824001042d81d00f040314407111111040120b42c5060326021295401452511024003070300802903c10f40c0f8644128601c1c110740c07a90b10035800d50740541c5403182c29a28181e072007800d180300412403150002040180c4691540d903c2c0000728104440703410107a0b50207504c2003810210518007400703400000d0301d405070000e608015150751350042c900b08064252003080f60f40f00d00303020310840170011410080c1c440400d681c0c40f0035144c010b01c07125150003010684200340200070780f440b5440c0c1c1c070111002d103d10345007008110f0b034031420106402010802c00034015803020645200c60000703081c031002601c03002c905441445001200803030380c4c0d024100c0e01510b0801d2007040441200701c068020005116600d42c0f07902c1d207403c4084408d051842581c80003901d01004041e83e08200380300c2c2e9a400b03100c0380d2181114206421b648134501c1001c4024801824000002045c10941d0703561030703025402200d06080b600894030b141c04003802c280000c0e5441c465a01004001007603640c00454849840c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 778361160 1250 778359910 778359937
    0x8030d0e060f0c1b06090304030311190212010b0303070b06030607080405100506280e06060703020c04110405190503060c07020102060628062a0503040320060301080120 74
    0x280c0303540c0c0c3c071410298401000042d20610041920001c2e91003484510b1180c0840d001454441303140d0305014103030300612031000003103811a030060b54180c242c4200700614260160780254000d102c6005060050283c0301c0050741c5803102140000c2040b40d80e0140e0b40c42090103900341c0d180394860000c195441c03c02640d0081440d000142c407100c00306c00a82c0b0250341b0840040003015440f136903840004c050100201c641d1140000f0392000c0c460321051496032504403c082c1d912502d84000d42c0c600075203030205420054442e40d100c100c003021046d00d0f1800d940140c10000e0000340503950410342105018064071859019004200000307140721810340581c0d07200b81c0c040c0c003d04510366a040401004811142c0707289000c40000926015199034820030ba40602000d0700c9454020800d441400803006115401d030014250242e90000080c1010080c1c40072294840303050060840c2c0c8100c1c84202243e210042c1e600100040000100c02c03005410003464000342c44034281400b104800c1d030b05075601c10400c0c0000d42 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 778362410 1250 778361160 778361191
    0x210050a021e01111b0601051203070b101521050103020d11030106090e07061824091e14041b0509120607030e0d0305041502070204021308030d0e06 65
    0x22601440040841850300302c0000130301c1c000124140e030b02a00015503040a0050103403c48201c1e000801200d400b6000484018030601034111145035079110301d040c000d0070702034004d02144459850300343c1400a0405030b00d80006003c0d01c801300610582201525030a1200a0824400490a184141c0b4140c0b42c0142c400000c0d4105a2203004880041c3c0a84607010f43d03032420001446030640c80740c101d5000518015280081c50aa40100355004038680e60049403a40c940803c40f20800803038000c03400e00d02800210818002000c141c03a043c0260344403040d0b10f000e503100f1001e140d041c0f084003415903c21506c0d89200d01002420311040b1120f005c501c466010958001030307a080d000c2c1d0064014070301c0041000e5020290b45046c9401d0900558145010984640740c0441d0074000303100e1b84c985411186001c015070300d42516030b102c84a00d001d203c00007040e4002103110540d12590104e8503098000d1010346500c0780ea6240ca5540caa0007251240000e0703152030a030501444000c1041405044003070040c607034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 778363660 1250 778362410 778362433
    0x7061b03030207080c060a0e010c050412140712151a0a05060c0c040e0a02030111070803060904170c1e01141f030c03050a02031b030d14250210050a02 66
    0xf035100002c00c1c1c0b00e15000348800c080719402040021b10541840c01c6c0403510040780c110707160a641c0380350200c0b02801010f02090201c0c3c00c540c40100c032000e811103803ea901c201c041221038200b031100c0c0c02600008204c0249032050007682401801110f080b900100301401c03c804461110a032036002d017a6010580580030481840e01c50094140c1840400540b0a510f00050001d030840c0c1c2c2d11081c01030349421034060001945070070704ca41400b02c5e00260426140c0305440c0d58400080c4002401648203810960218041c0900c1100c40306542d5915004a6030b10040d03009000e907264a003400d4501c1c480d90945c2c4040c10740f081805090604440000e07119090344801b0711205521502d040b104000c0d0400c81000800718000201030307c011801840030b817404490718014503060187d01c01400c401c0f04206190402103031000601c03888025480e1030b201900c101c044040c58007038800c01d1080c2c10404d00b00c910701032804028040c140a1180b00310b4910118151046003030350940101e41e480000340e0401b102c0b015 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 778364910 1250 778363660 778363667
    0x50112060519020d0b03150403120203130f1103010e031606051815090709090c0501050711091006082d090c0409030e09100315020f0d1a0307061b03 65
    0x10780007005550b050003035081c0305200300126004a04280702c01c80c0c850910346140d0809008405205060004170f951901d4242c0300a030101102002c0100007917030000c0003c248110743c015035102d80d50300c0034601c480300c00203007441d0003404264a00144203500e07012000060317080000071980030904284407101000200d440d160001c0800404010301510380d24003440395494244850036100510040d207019900307001c1507140c54105a9000140c0382841c01681c98007007143c00b00c0e490115502442c09580c1d40c0103038540310f2001e02400e0345460300800b86405010521850411071000d544071540d440c91146d46401c3d254154500e60150b030042401070340c5800e0420750402c04440d84c0454260100c0e142550346001050880740424400d800050300714803445d5007881e2080065801486003804040c606003140c4903500c0b20305415403400440c81e07001411420f11003186040d01c0800c29800c0701000384050014420551500354110300348280611900480e81901030003034454114411201070425264541d82903 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 778366160 1250 778364910 778364921
    0xc0a050f01180314060f07020105060607080a020a15050a240e0601140a120501240f200c0f06131404091506061d0303090d0609020904031d0405011206 66
    0x540715140d400300203c00700d240c0b0040b1100480c080d500401103031802d550324004e00c003005010f4030216410b01041c445595500010349809a4210310400d959409044090f85860340d101e400900714600c0f103461545001040c1e01c00b42c46007140d19000d202090b004e407590030b80015078a0b0700509806c100d20041c40300304000601150f00050604040b90074001c8820000b030383d9008003030004001036904c5504a0040c41074002c450050540c8403d16054800310302b80010010480341c514803c2203c1c2c0d05c2c02207a040d201d085629a5410640c000305103214503410000e48443c0c0b011800c40c055100d141c1e000c0480d00b0700c50111803d000512641c1d0021030304080c00820745007140241154482d441d140c4840c0820b5034000005040304103e080050740b00d240c00c0d00640b08115450342100b240c0c00c1d030801d0240c0e640b008411100100411104410104481e142c0400140144407002e5001140c0b0700c1040f042641106001584059099100e1490000c0e03104120965009015990304000e407064400005461500302 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 778367410 1250 778366160 778366187
    0x1517070c05030706020403050d1e030f180b06090705030105090a0e0c0a08061e090c09090f0303010602160e070905040b0d022206170319030b061b0c0a050f01 69
    0x10354a40d0081d0326001c1c034642100c50283c1c3d034503600180420400804002c4034119240d80d081a10410702c0d10700440c020844480c90031014151200d99840000b803441d444072902d5007088189000c1d130000340c2060040c083d42100c2c128010800d24010905180c01001900e0485100602944407542c607101440007400841144186600c5265503101995603a1340101c40031700003140080616151980e0303890340e02500c410720300401071091000e00100900114114016400589041da00b07900c80b03001c1d052510300c2440c8411040c1c0004000440e030940e001c03561801d00b071603801e00032140585510315540f1003001500c1d01004101c03212010045828550414040e4440040050200d0452900070848120300c840c0b003d81d11002b62500fa01c0e04412501c01c59000d000800b41c0d42034403600590919950707100307800d41c2d012500000180d41c188244240c016116584c2c000e0101e40e1221040401e0281c4500311102e10340f964001c030b071030301d40480c18103e00d01c0084540080040000c252403100558010100081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 778368660 1250 778367410 778367417
    0x50105070c0f0b09010201050708090714150a02060603060c1303032105010303030c2703030c05070b040902070303060504140109020f1b0307140604030503010302040203270c0406151707 81
    0x100140c2031441c00d111400030324400f940030341d540b801007000900b1584014151002d015680007401503021000410009803001e220890003011121030000755011842a502c83c000c080009524401503070200d481401401d0907001c403882629550740603809030081c0c007400a04108214400c20210340300c1c004401115030f60458081020045c683e0724015036100343c00c254003003a115422008000d500104400c08c01040645052800d440712011000340031086c4406420071a0b460a000184242404000300402400c07c0c03240d84e860341c8480f80da01030f402103803050700464034001f00007a1030300301400b4060150071b0901801c0c0460303003040c480b040290080300c0e040b440c0c080305000c1c0415646142510301c01200740c1c8002182c80306818038000002c1001c0f4951841c25411803000e02c17001a0304401520705607a07044601580700e64400c102051000742d54191084200600c042030071103510003149440440c0c10507242030101d40d03103030806e1100c40c1200005d1040000ca40c0c9451300070700381609100035009650b40c82e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 778369910 1250 778368660 778368683
    0x151e090608210d090f0f020109091415060f070c0e061f0f03150801050415020906070308071e2c0604140a03081c0605010915050304060608060702070e01090e0705010507 74
    0x319825021030803900304851b1411403008103419503030041c28140040c0b100040900407880425480580c403080a401d2090803000704102c0b90b0039540d24400d98803420264107910b601c0700402c0c100481070118500c2040038803102e0902061407410074500001090032840c21a80a2000e811803c03503441018001500805079111140002d03542e000b5000c0004001d22000420f8a080a0900791612282100146080c601c100654030340c0e031702c6180666114681505140701d442c1c9d10001c095804000c2c0000e458424194000c11540d841d070061491618001c88003000d89000da000307440318580000d8210040c1d03010708280020012280d8050203412241d602500380001d46960350f6401d030342504840758034521240442403040c0c0000007480303000020102483c203070a01601d4101d03205180c0c910309074420200b10000000800b440801d030804130081c4089006c9a80504e040c02000351601e846000c3e03000516240300002404c4d90307280c01081c5a81c1c00c0c80010340303070407803601006403400c0c3d005900031121224040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 778371160 1250 778369910 778369913
    0x180b131104052707030309330305040b06090603070515071e1e0803220c030803060406091112100b0a170105031906151e090608210d09 59
    0x24042d06000d907980d055038251448001000c1d1645942c02104090325900445003003021960002040040f6070500000130425500c558100400000b18640d065401d0105282c81414942c140d00940c844c600601d410f01c19515040c0402c4820300b030a4902c80d0703169120394018085d0b4540051104a00e00b0030300d6041d4035018080c0e6410203034010913600c10302c4425401c001d40e0144002030034502030b8000b049200b0301d004401c45e515030200b03000180024a02e85040f0036808803024071511044100c0e5000901c0724442540e80c03402d010180e1044580a0156040801c0009c50388403902407010281203290600f4281002d00240741d0706050020218084514090000503030420200028891100301d5071318440c59003074515a002c0e10540683c0454000c2e84402c0400c80364112990a00305402d501c5800841e03460f0016150b03c1e5001007640151000d482a4043d0f92100301c0c080c100d0808884032040240445543c4104240d1502d0203102c01c1e61420004620034010100305800600409008020000c0c02c58001e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 778372410 1250 778371160 778371169
    0x10503270c0d061407020a050607030903090b1201061206030c0b030405150f07090f060e100203091306091b12090204060f0608040302010e0105090c09090703020d0c0603180b1311 78
    0x451006980b02c50395a410f80d444c20b800e600e5100d42c0301e44140000c00701c2c010795070344056440740020440d804165945e034600041500c980312420041040d000140e4940403088130b0801d00190a12400001c12a030001c0c51a1001ca14040e84044a400c41c0d468015240f901c0008101544000d104507543e000d031110207203060356403c1015000f0b00c1d00480d500d04602e00220060f10a46040d0410304e64044008020444194000700c1d402d220070003034440c0c8040d6558010240d01c0c50060075000b603401b1000c2c0340c2013980044a40d20400441c1c02c421024811400c20080d4420440192500c1100060040e02d41e030504240d40c0d08038003010361025000080d100ea88140710980302034140c1200d00003800c0340c824441415424050032481078001c6c40204103030f0034100c680036620100e13800b80703c1c010200303540000e0b10700c0c0081c1b0601008580140a104071014945840002801d840c003c5401207880c102d840f11700c4e4040444001790356640003103445000d841e25141c907111030f0b2010300100c42c0c0000303115072007415445 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 778373660 1250 778372410 778372429
    0x1606020904020a110d1d100c0b07020d02100905031b03040302063708180319020a030909050c042102040c110d0507050601060e060706091a06010503270c 67
    0x8240e03498680004c0400b04060170841503d61140400a410f82d00642800c03240308030b604404e000700c8106008807031024040d281c0748a45080585003c486808000a4580215828039402d00f01c5d8250b810102040030148100c0d100b8001c0641283d0007444140c6500451090811480600b00708607400c0590700d600241050384140c8036450010042d02e5000c0d06001d400d05841c400702c811840c220490f0020203c01000341c00001c2c0f0100c40d03010b02a070740c1d4a000009004490221406550384070005d0455100a5a902d98090003140007072201a40001c0c0020244a01d9010304043b50245161601e0140c00c0c0c018411140d017048090501d1404d044010f940704c0c0300c1c904a40c403160711a0a01f03910100007050030084405151014040100240000928041240da0540e0103d00b483c0091030818004500d140c0600c0100616040c50300c0070700300501ca29062a0008141200d0a018050340c94800454083c0400e030384040029041d40303a0b00507104861003085a00003600e50880340b10301c42c3d803c001404851b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 778374910 1250 778373660 778373677
    0x12021305190f090c0e060702010e2701030c03030f1107032603071e0f140714030a0c0b070914010e01053708040f0b04030e10020d08010911160602090402 67
    0x103a0300d40c910a4070704c1d040b40c0461740107642220340d5030511141e600040e0115600090142c400c805920000c0c1c880500496100310099240d91580d941d5a100d2806111000b81c900041e404941c0c4440400e806620485505403455145000b070041d15246650340032807110b0340c6500006d11019400401c0c035132a002005144101d46542c0c44955548500e44c00b04010100d62801c1d50030841855400301045030090610910b4031240741801d42c0d00c60250414500ca68006500d01030039000010b03d22418030360040c400041640519420304054403142e105484c090858480c440b032481003030400003c0e56000d80b036240704100c0d06040241c600940c010380203640140b10514142a00c4500c08041c501c4200d800f9900e0a440f034500b04101c1e00d04283c0c440400032081a100200f101da01c160005080620400c901852504081c240c040003034030070a0065242e402240c4858005010200009071560860003190448038500907100d241c180e400c50382814900c41d82c3d9064800940800c0b065142e034541e84024880d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 778376160 1250 778374910 778374929
    0x70312090e0a1a03031303030c0c03020d122a081e0a2d05091512070c03020114010312050d111204020a30050a05010903020d12021305190f 61
    0x1c3c41c4195039602d5000d0405200c3d030180d0b00034050004402448034500040d2505424081f1485210b4038000001e2070450704002d40040d1f1004c044803c01009400080e42070000303442e100140380928003000022103038151541600710b8010424000f281c0400c4c000c00ca41143d600481400b111b644459030700c560303c142e00d10030000b0301045920200c1d0306903408210034203503508031031411203c0c002130040903401610103240c46071558604614603490108211101818403690580103854108400b0f068140c0c1064113070059401c0101c403c0c070228000e0b0403141600e911047d9001e054820000c11101900407064501c00d01c0d13139505050819061240107403281260381e2800550918213441803140e840401c1d402019080d40c0c0d0300031002d002106544200100d060204161075200007800e109103407510342a4045c00c954a8070391780400b07066001c6078a000050403a16440c0b840c07044022076404034801d10010a10050210100b4400c40c582013070810900041c1444101f001c0da00d07600040066465540045040c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 778377410 1250 778376160 778376171
    0x1c050405121803010c020c1801050a14120d08042907051305060f070302010605030304230f04020c070302040b0d0506040f0f0b010f0f0f180b1c0501060e06090603070312090e0a 77
    0x52a008201d17407803640040c4500b08c0d555140038003041000455006081e01c2d1b110000348440c01d6103499450842e0300c410320046035107031551494054550041980c0c143c0d14030705d20f0180070320003142e510071962414070716841d600c4140e03403921021190741d04804c0500510001d40301002850b0b54510000e402da0440d9110f00550740d40d818500607003102c0c135903130041d40260400d12040140614000d60704c0c106000e910000c0c03070300384150800a01c1141c10301c080c0d60f0b407251010075070001c030b002c1c00109641071b68426101007005058041c20004d0a28500700c0040042e844040050000340c1001c101e40840c2340f040481d0001c0004694415021607001d0b04001c0303e1802411080042404000842006104140a8422503410240303482c41c8004250086400c5a44414081c002070b21404015420380e00d070907000008020540ca4814064201c0d4461030b458000c40d000030400f107192941c070b014064840100202003891865961500c00019001c02c2c200740440c2c02c2c0c0c001481078812840740d20403221500002007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 778378660 1250 778377410 778377433
    0x20f010605010305040b07032301140f03070f0513060b030c0c071d07110f07080a0b0123130b06030a060815040309051c020301111c050405121803010c02 67
    0x211a0303558001810581001c09110100e226107860b650828402c3c6004101041c0541c40b8080400300b040c80c0380d80540d4001e0001655948049540100138411076010321100d454804065480c8514000c2d03410348076100c6410405841d000041500c00c45040601084140c2d86c0c813a6118103400031a03604004010000f203c041025040c0600406072a98542040c03460b06520008945c0f404018407010a014426a0f40410003d04121401d2800309000c116515a912a65601d8595035084021070b0511110b20009c9030800d04455008507200904041031807038550300d020000c0843e155503c00029079901c03404c02c00c190b126240110700c540c10700a0089a024a0010b03003500c0c0c01922140d005021404000388070000707600c60a143c0c1220340c111614460283d03c458245008a0500c800a40c59841d1030058485070303c204000d440b9000d803d80c04650f1901c081c0e6421800e4070800c6800030055003222400c80d00d06542c190203070180007903860406a0b0252070001081c211121001c41788003503400302c01c0c0c012 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 778379910 1250 778378660 778378663
    0xf0a0e0a05060f100f0305030928062001110a050f040b07050601030c120201020d21060311040513150f02120403020c030c01090f030803070215180709090b070809030415020f 76
    0xc00303c17155950078251554507102d844e4044d034400248544a051075030b441c1100c1200b2080c080d00440c0301c1c1c0311071060380d03900702919188090f030704a990740d05c100c5c416096021041c402e9a0000b10411085032800032928021940c7c3d81c00b0000110042d82c040c0310100300ca0710101c02500c90513215100622f030399411030500141c203020b84d03032000042101035560031006036404140c1c6d042c04d50950410017118040d0408880109610b2881300c8002407074030000005110100c60712007440e120564040000380c0703888420071050540103c0280140e8030141d42240784400310b5200c10054009698018100240c0000c041070202055400350010381c0181442221490144191840c6c02024203005800c280342c200d859141919500c00901052310110025100d01e0092006000c000c0070b144401c40c440c0303095030b031000e0030440e6040c040c50356224031580810500610b100c0c0c4550390380c02c00001c04840d0b5810f58100c80003079004082000351b005c18040015003c84100710a8031b1901140c02800b0038403909411503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 778381160 1250 778379910 778379941
    0x103030201020c1b0105220503030a050d1d0a1e080f0d060f1d040f0c170c0a060806041d100b0108060406060e13020c060c0705010c080f0a0e0a05060f 66
    0x5078813406180c0729000c3c9680c0000c2250410190020030006008180013102000c00040e48800d400d030000007680309000741e014004180c01310385c00404100000462148044620759094540003507803020f280caa01042140f14070501c000b00c0d5484401c0810426606d4144980002c0c000c080e8513440490000c0e400181400b66001a00c0448500303410030b850405940b50028140032079807600b003d00000705090108500024041d241c000c520514040c0c0d4a050003e004402d00c000c0c03411900a00501029924000c51100212000755480140b00d440e0311003040010100e020800ca400410340010010080051000c03045400c001e250018100007818000342c50701d0001417015219a1030300c1c00c144002c1e608a507003580060700503114850034160041c41e000c0203110f86030038250035201740d10070441e14a0700900200301081c403031002400600e243c450300303a4402005952401c2c41e210b0341000555251182c2d401002290140d00c2150710003107294079000c0c100b1100b40c0343c078082c4e18044801c0040414545258 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 778382410 1250 778381160 778381183
    0xc0603020301170a0206160c0b04030803010501020d0206040f031103120c1801110a08090a0905040b06010e03150105060c030706050c04030c051509011407150e0616020705090a0e060103030201020c 86
    0x4d0004540d6940c001074a41c42801c590703005004095070044280301010f000000034200e0401d405944645a04068645800c00d21450b40140b1810f00d12054403032002c21024000d5134002c0344040180842d903000d1301d0b000007042d0040e540d403005001044c4030181101d2010b0040705100c1c680d954414483c50300e451030860528001e130601403104c0c01c45911000001e0040d5078681c2190160b500c804204e00007410f441065400034484909100510040c08240719119000e45401d0700c80065803031644061684814a8601d01d4010204000040149003080c1c0000c103242d070fa82e00d096911341101c2d82d80740001c840c4180c900d6040da0101080c10b0003002a0080e0b264094201140c040c0038007541045469003500c0f4800c000b504000c1d4030840d540701084501c0a0b030b007040d503001e0b01040e52008200300c00f00007041d02c41c0d42c203a000c0c8940f01c086032100c08a00c000c0c200c54080303980030702070003401c003400e00144e508003900ba00e40d0140c0c4c80e502944030403010b005e03080c0a940319600140e5503d009801807854580781500c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 778383660 1250 778382410 778382413
    0x7050702030601030605060a08030d060504180206070f080d060f05120106080706050a0e1201050703060504051302060924120a0507050702010e1207091d0c010c0b0a090c060302030117 80
    0x481000350340d00040c45411680d01400201c6c083d070360720b4003051a20103180d1241310984004581107402c646281c10074800d0360b10650b0f04001c070703010920f08649a00d8180802a4200504108000108007170130040002c0b240038402d01407404181900071004c64030107900c030200c110900c0340103000c0c900d40b114440501d2010f00303009110141c2010307a12030315a00300c0e201c0e0700c081c41000100007128500910301c000201e40d00420048515946d0002180a0a41200c41000003464074070082000c3c0b600f840b409010f000b01030b00500410070b0321b0742880190350003072508550144400c110054002c00324110b07440d1040d504030070b8030f03124608080c0446000402605400c05181480100841c965001d01a10081364092030012040792a0700c0209103541d4240e841d80e032f218041e07020042010000c42c0c01070494031980001c01424907109100f0140c51390070301170003540040c101103080000300700c0180c92950032080724280005c050605a90312480404640d00c40b20102e078011004000380b07030150700d4400a1008520 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 778384910 1250 778383660 778383667
    0x140307050111180907020a06020a0503160c17070201121b0f052503030f0f05070207050910090e0f06250e01080f07020304090501090212100e04082b0c080705 69
    0xb0103d190796490104403a00a0044400040c0348a100b00601001250021011551141070080042c0650302c215101c44510841c0320030480c0d02840390004050a0340c2040c17284400fa2000c0040d40110b9000c004280d04000000b0b203020398504140c803400002d1008240040036401c80460084d14418181c0d500c0c0003804400e12103d588002200504000000307410f55040e4244101e1a007075006007504040c82403018131f0004802d440312000e42c0224050301300354003210115580d07001001990a0101c948030011443c1d244104203040d0950042d45180c0e03642800d031003841100c4401caa103030070000c540040c40c1400700c2c0c2c902090310103015604010050345284c449018100c0400182400c20090441c0342c0080ca02d200207607009200780150707006052001da007800b09507500d0307207004040e402140018881903200c0300031495080142c84003074111013080000d0310f1641d84036110303084180c0010b0980914507001d044103c81030800700350a90201d90100c100000c6002e4209001400040300071310303800c2404405c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 778386160 1250 778384910 778384927
    0x180108010311060f070519020f150f07050a08120403030f061d180109030e041413200a03200102070503150a0e0d1d2202070f140307050111 61
    0xb40500003005040d200c031640c850401c000c4902c0c03403280d440090164058601e03281c3c1001568002d242071030340208c58036407640c0040d10400495600882a400345400d0400075a11802c11010103001c85501601c19949a51503580fa0404617038001074a518040800e2404c1204040d0944240c8500b0000d51380100005800c240c3c03403594040940c3d5190070b1200c168800224852841c100740480042e20000034011403244c0d240103419007541c510780c540f2560510403129100002c8044c520700c1101001804103050307400d5200c04288541510041c001c40c83d410000d00c8598036202c80e804000e51040e6541040c000c0114110b45e9030340600c0c5180d5046410144080089540c00119109400d214449004140e29a00c59200050a01c20403011480c001c54800601460b088400300c940c0c460310307041c50540880306100300310080301103c000c9d80200903000185000281d450340039000759440340310034429003000303501c5003845200d81900c120080c2d88000b49040c10844213004411030002500b81c501c0c14030300c54 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 778387410 1250 778386160 778386173
    0x50c0403080405010320040801020c0c0d021f09030605270616110a23280f051f291e03120a09030b07020a03090911041701021801080103 60
    0x360f1103070394105a116280300d100511103194555031800002c03120356641f80d40e5000580030790041c1c09803003414011200e80d0042424000281c40d0655402030a160180c0314130441100542d007020350746000c010301c0c03139000700c0014400e20036180107032100990000b1620004070600d4451112014039000f42d007181d014051a200400020010390301c16040446520701001c007180d14104010030060400020800030b5034030519800f011070042640031066405040103014284034114905040e0254003003401c1000d0003088010380300c05e0700e1038401c5c0d064079540c80880e05460229512039601401c1190740340506e44066020740c00caa0f2490b041e8150540348641d074400040ca184001c201c4040304100f041c50940001d41c0d00f03000b0110300303010141c4e0080c0c840c3c61407a4001c0c01c5494900084030100915008200894000200290016490b075a26600c00d810a5100009058001e907000f101020901003c6138810421030075040302e580e82800180c480d0540b400c808020b2910b601060b060200c4c003401400407176030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 778388660 1250 778387410 778387417
    0x11b1e0e0103020f12040204110406020a06020d2406021c080c3010060503060303270a03060906180305160302030d0617010c021c180909050d03050c040308 68
    0x456040c100505901480141c000e4403480c1c840310390350301e4000b5881c03a406954200141c0a14000d44041010500c00e00384440507105500410340968469400e06c0300049450f0001d043e261609800840c2d82a5485c2e204004a07542c80c1e019203080748900424011107604100d11040c10b180b50140452000340154041c0c100e000182580c0c1a103040010a014a907925154608405031255070045008030703800d10303140c40500103032068480308a8202000840c24450380543c1e015520003400346141003040b90a400b0301d41d01160180d1a2040c004040161540d0380403111401140901c6022800c0101131a1a4088074a68004051100c050003a0100400d5101041c0d0b81461a0140c2c698082c01d5036050a0340b95014040c68101003a0034070402048405190741c0ca50542521280240900341c0080d42c2079850700f4a00210780c12115100c0c030b411a12501c500c80e4841500c048084440255032500c051600343e400707a01003a5601e500440c0c0b02e0002a5142c4107582c1d2200d0003811050810f800c603a6514007610 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 778389910 1250 778388660 778388717
    0x2a020c0f0108091e0703050c100e060306030c0604060c141209061e1b06060108011809030e04050c04030b250302030a0f0912200a0308180d02011b 64
    0x1800000f6038291020002100005004800f5400071003480d00780300da440d03109000443d41c0303000d8a40900c0c1241000724403980415402d40351141040b86007424401035410092010b6414425208581c00c0d40d160200203102401107039485000d445e030241030010484180d507100041030f600c030b2a400661048d413030082c1c5030020307411500396503640445504c229614050b81404541d5000000e40101843c1c10322020148505111040c1d0b180b0b0b6441c02c0c01941c00d00d009100d190a54245200c44101a00d11603210b401c425100b410400b01140c996008176080340c2046a070800340000014050052101881400307510035800c1c8001d4010601c4031001040680459820340285034000c00410803030316558108444c4c00005100030806000d4a003001801014800140008982c1d0002040c1c201c0a0f00200b0840b000806002881500d040303940894111000900400b111000030080c80d240050610210b8041c48613680003003071049102062080201c909a410002d008414400000101e0041d00710417006 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 778391160 1250 778389910 778389917
    0xa031a0f0603040813080d110c090627011d090706051602040615120c110a0b0a140a140a05071205090c030312160c0203030f0703030209042a020c0f01 66
    0x252030b1850020b00d1350242403440b0a0700303035264401055480e00094030701c0f0211000d65508111920444500751503801c0780d00c00715084001080014010b00308108003c0c081d102c0803000e00e001c80024440103031080400c0c1c001010f0041100340c442035001442c107195030400800e9000d448581d25091001e40a03110340c981550100d0741030525003040d960345a020070002d04074211100d035507611400005080481f840e19180d8a80d10300711941003880d228164994000451700c004004101c1e071500c03071410b10304000300700309491a01c03806914600903080000358080c01070410042a80070480c58406120a00144004246458441001469540b000c4001440d4486c060009699214001d005042a0320182a50340500c0300150701d1041c152040101d03841103601030307103030b00c88004022401c4824042e20903010350306600c244528100a480c0100504445100341001860106000081000c1d2102c0c2800718100d0403010071001d41000c552038000103203403200c1c40034148006545001800200f000741110b0b040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 778392410 1250 778391160 778391167
    0x31608100e0106090219020607021902011101110703120614010c0803100b0f130b040602030316030615050a080f090601090b0f1309050d090303020607080405010f09080a031a0f06 78
    0x101200f94495000b510300e415056559148002215200382c4c54940e49100600c10480081c1c5603030301c049a105411a01e040b03103d00c40010580044030200d40c4120400c0d82550384412a00070204a6001007840c82d01c41c0e208c1100e01c950b1810302000b00c0780d243d80808038080c0c5001030702040d42e920403142b010036039019440e503499444c2d0082c100c1040704a6044855003420010350b01348480710f180090180c68441e81c03607403e20f0355207451a943c4140164030910025a2003440802d4001010340503d1513881107602d0b0004450741c1d5000c41a898880112015010420000c5d03103280c4558444c00c900d81c41041141c406540341030450146a8074030051161400d2107942d1716010b162565072a499501d203000c000d00d01c004500811040400030103440300b00321503900c62140c4058032140a0801c3c0c01c2100e0300768000d80b070030340d44400041d6901c1800601c100e80035542d840482041c09a24420b91045501801c03100d034480c0e10701d01c00030b01220000b003004c1d050b00420016010117503031045040782031184144e4132540c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 778393660 1250 778392410 778392431
    0xe0604020d08070b15030d0203040b18030f031c0e16090b010509060304080c01051e0a110f070311160b09062113120801060215040203031b0c03160810 66
    0x2c81d030054440091442c03140340240a02d060701000c0b80c10110904500b501c1c4030a40a100590380d9220343d1041b024410807c0c0721844032020b050205044204000c2c0130342e800106d4070058142540c0c04038401c02c01c000103074844828a14150311031044884c00c090300030460b108103142c060280410500c900441c403525800d544215134444d0007504c0450310081c1070607840342410720b4401183d400914000316598a0040000c000c404414001c550704ca9100c0c59000c030548440d80440701401da0030022000c445000c03c09403851040703603001051010b000b0350b542c0001c2c1c4180302c246810111040c900303c2204c0f058440c01d1004840400403501103000484000c0d540350aa10080310040d11200c8820203504445030400646004c0319804980e101c1c4255107500380210f00c100141c80d080028052040143d016901c040600c129001c21150458001011030b814241407462825080340c6259620701141c001d041a002c960034200401c840140b0841c400c2c41445042414440e560310035500c41500c1a070300ca2401d401c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 778394910 1250 778393660 778393673
    0x142802040906300f0f0602120c0a0306053a0503040b0310060c1518140106081002030c030708130507062d2312040b0103020907030e0604020d 62
    0x400030110000d040c030005a81d02e1502410b94507000343c400031400039201860402e03480306150071031141e120780b008080b540750352116400d0f6140c0c000e085804640c01c204960003440300c0d07124070b407184e0164141075603a220040402020b889065020381d008400790295140c56030010010b0b20100e8402c0d039401e00c1c01c1159a042021308052250025069000004010404042d00781c011889a1401000204111340d265421541900c0444020704501070b07403110400340100c1034008150014143e254450001000d855102d0149402c0c1480d8040760764030345042203805001c2c0b242118180480d2411410340c0b034004010942132100901c440c0401180c031000840303100c070024042d024207400400b00c5114640300c02c0d010700f81e6175480f0000304a00c9040752002800300403150f604024005c07981c1c0e9a9000c1048448030702c140841e4900d10014068043c0071803403611041040380762040e401562020801c4d4035600510080300d10140c046c1c006c26081007032107071b4404e40024403190840c2e415551001004010b04042 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 778396160 1250 778394910 778394917
    0x4061412010b150d11040605130b09011e0507060f020a0e091005012001020703021522170403060e010b090907060206010302190305010f050703060b07020306151f03090501142802 78
    0x80017080400306000c40c0d480e43c0300c000f629140c031149030380d0843d00e900ca490400450080d08110360009032010700400c2800340420380805105035074145a401c2c20b2980c0d50748015911740000d12001c060340881c140700420361003244217007404801e6540d501241000c011aa086030090300802e4184080300c0001488040c585030704180f04001580210f44404041c50002e48a61001c12000c071865440c102050300f0309290011805c02c04142c40d4040c05040e40c540d1000d61841100301d4461940005020002c0441c6280c02079031134448c90310b0000103100c0c105004102e00346101905540d29503001e11005d1184030340005070702e03040d00e030112019034035042c00c4240c05101d10b0950700300416950a00b1550020406290011409101143c405100c3d0355210310180100740100c64002e589a84601c000c80c2e5840040d00844569960150030f40501c0310f6000f40d40050098000c5202d40007035075401441c024000288140f081c8841c01c5503980c41d40e420a0b0444618403c1500b000b0340601c04c014811240b0400c15074102c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 778397410 1250 778396160 778396181
    0xb1005030d0903290a05090709060f0e0c031b030a0213030b040c0b2b1d03030411040504020109090b040e010c02030a112b050904061412010b150d 64
    0x1216604081c014006010525a100c11644505515004655442000403544c4010303400c902d226044c4c1c0c0c58003e0000034200c042d1600486005207040850380407400d000b01005040303c00880f219851a000c10b442e0f49080007086400e80d844e0034404c0c0890618003443c1540c20500805071151640c0350303581100024800c072680d8802c441120b550000400c4400001e841c41036000b01c0c004410141d036038880650070700c9a03560408c0341400307504044150310f0f40c0b10200346e01071103030f01d10024415691a51941700c040b4544502006540040204001c1000307940c6e0710180d082041d030b0103126605040e80043c02c800b2290283c004665191800349020b502c039079001c002d1113080c0340000d0104600c0002c000e9240c1e80010000340004019076891440c00100049080b10103031858420210f07003c56042106004400b40208010010200840d03c1540d075540509006040c0c4182c44402a000c60410004502c80f8200c0b00c00302641003441080559540d014032035402c4000c000202c3d60b0326640785c921402440c0107080c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 778398660 1250 778397410 778397413
    0x12030a0b0a0906180c02030a110a020402120609071b06090305070506010b19021c0513030c0e011809050c1903021816080c030105100302040803030915060109120b100503 74
    0x20001919007a40d081001112400c00c520003404e4070445213041521030005001015900030044070a03100d204d5083ca85072000410700340c50561f076242e030025007a03034407828280c2100102901800224905102e6803500400b0b1424850007440854542c041003462007030b00a1700c025500e801c46000c0c917000c2c50403140c000d603014040d2a010f42e11480130441079000290200c40c2e9850f1405501589800054100054000c1c02100d845c16003940030111001c3c2c0c401b914a5200c010808000000181d6500d9440013906c02c49103048502d6040c00b210081c6071181015007041141001c90000100780c020500c1e80054405440545d807000c1c1e0030144e4103010850703900c02500f10f001212084038070711b046001c15001b4050f0401d0407a9040f901c00c001c403240c41050301e080b49811001c0004000030300d00b110307030800f8032a00d07030402605143d0394503006030441d0411210009d482d003142c0030a00c01d0b09200c051142c0d01000c00d09000388030504011807184e074181002c030000d00180c1c40350081a1001c50444815009000050 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 778399910 1250 778398660 778398679
    0x604121209140c060708070206070618050c012d140f120f01080c09010b0705150405061b0a020c01030207050f070611070902040b07020906120f01020a020c030309010212030a0b 77
    0x50200d01c0a20300d111048694040c0c50f1a608144c07804804540c03d050300480082e040691540811689500088044030700590751185100751507201d0680741c40e582e0044000d007451019190000d0640421001d415030640180018603020460220038062184198034140306408013500703540f5038522845400005042006c100c80684c0039054411358414421480d00583c181d99900310315583c2c0d084005581e6003c0041130061200c8064640601380c01f5018008403020007072112640320b0320f850107a6041e11590000340c1046000d09203103a11080d030b4445400d20303903d020b42c1a08025201c204150718203042640011715502480b10401034418051480801d98000c02d070b8070700026149c44d0700c80d03049a003903000e528400075400000e482910116100c40224501e02401d6030708001c1d40300f4000b400ba80e1b100417801004c00b0b52001c10003030042806501c1000584d42c0c103400385c01a14141010100724800d502c00c20040c0034a0342d0128208041008001d009505c90f00c485107040c0180c520317540180e40010801 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 778401160 1250 778399910 778399913
    0x201090c120f0212070f150206070f0c020d030801060e0102060609011806180e100c0c0f081204030807091e0506030c0c1204050a0902090f150708070b01060e010c050604121209 77
    0x110300202252140d4421040f1b9940d9950010700e0200c1e2003d0040c090380094000a0902e8003d0080e4140d1402c00c1c40c0205024031030b503000074000d51450209900144c07a09006000d240e030069400c1d04010401d0008000c00d284c29000140c60150501400741109124000464503035110380041020344510800300c602000802ea1907402005259120350803480383c40110040300c02c1c00e03c0307580c422180a076149060340d841c540302c40e141018000340803903a640c0d08010a01d40103111102d0240124030079681e914290a0200c80108550100e80001c110b40484a060740080045900408200c5c1c5054941c03075142da035905a5941c0d2030041c070030014051b000340180c004030491458014416a04100d58410380d16440c1c400100403401070022a0b90011400b19034170f0704034548000b800b001240030310f43c424500b403540c0ea130320422034100c00011101c030f02200d8014007000d078004c105007005040a01e8603400c00b406940b101035403034502500180030445804103040d4250702c81c0d042e80c107403190141c009000f105810b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 778402410 1250 778401160 778401163
    0x606182903010f02190906080c03060d110d03020d0908030913050901200403031d010f031e0f1a10050708090301061d090715050d1e1e05070201090c120f0212 69
    0x140324000c1c0010381b0142020a03002d01a242c4940201401c940150460362000144801500e12120a0321110b806058005480d0b84922034084540d2280d8080c1500f6280c0e40340181100350203410401690f041408184a15250030007e111f00e441e02c000c01040d50748078038404900400d43d51620091186030600b03d040200c20407001003046912a540b0380500c003c5c103090b10b0001482180c1803900041100400841d054400d4000703005490300700707070b084201401c040078080489140d4048007513070f5034481c52000f4407000303502c0101c9088002510350840c180b10f4041c00511510648400a0415030301094402c0251801d6104034094904200e0f101411014074014440320382c0301f00c0d5180603921810a000c5102c1502c0c64041d1002001e940b41e0a0601000400c00009000c400041c040041c020541c603848034030b20390090810902d40c5000c01d50700f10318010501d600340c3d08010403070015603040c0040b200000b80c0020524007210b82e807502180c0f4013103032403508490310034202d48042d5000721804068100c0400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 778403660 1250 778402410 778402447
    0xd020625051c02030a0f0c140f1f11090603090a06020f030f1303020d20070603021b07031505060136050a030206070b0c160606182903010f02 62
    0x50402c0e03140d00318007410003ca0360b038880c2e50422000521801041e0705124007070a10700115611403501540c010b056481f802d07107082c1249860102550054005229116683c0403034590050545024044a40001641c04107446244245e9006100000001d662190103000d00800ca40c0e12840540da96105400800c0c0b864005030350701d09d10b6030b00c1c08002c078480b0100540980481a80b5802400c510003035804161a08a40c1e410100ca40003030340302c514603035128140078240242c19691401078860018106004031030700e40a07010911b503130100c1000c0c000304130040c0345092600310b07110f03000c130305036031107600490b144246450182e429030f4100b2140085e100c00d180d42e0301a4218200c000b05030259403601080100706451101035007010b000c00c0001d001c1480440751356807041b443c50a061404a42d0300451020704c0c0e002c072007a1040c42e51018180100b05030580311000310203014005108140f80f02840a20100c66a0703505200482d002031400307000e0700d0039000074800f6620351504646036122082000100034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 778404910 1250 778403660 778403683
    0x9060403110c0901030204020a0c050f10150f03060b0406150804060c0c02090f0601110307080d0b01030219080415150e010512150c090a0303050d05060f0d02062505 72
    0x1211580380c08003480c0009041c2c090a0300040030200103910356000d00000f580711207160010061100b064101081080007507076490748681d401048030400750070900e0300701c0303c0406000390110340c84a4200116040111720500350780d04010002140f001c43d8002400070034295100c110007804136100e004d40c054102c1005071007103000d043d051044010880d801c032200e80342c06000951080744000410b9031140e0b241150b035444801130528090081006108614581100200b160400000154103681c00040d002d4800702640c20709003076040400c030382106402e07040d803203a5100c2040100c40015051100d00c0014280c035011072001000011505400003015807014060b80f01c198121200000342401c1034042402d212066001a0681045545030003031b00500c0034190004810341403001e081381d40d82d01e04070311004520988034a60341e601082841c0c0300780c1c1c000030f0030303188100d00c050305810490306e8120000a07000c0d4101c0e6890340d01c81e02c2850300b00004807181c094400031049800b4547c03c11000142104240 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 778406160 1250 778404910 778404917
    0x1e020f010c080105030d1d0406080d030f05010311090411090c07020103151a0a03020702030303180f0d021b0105130834030303020f0d0510150c081905040e09060403 72
    0x41d1618141650582001e00c078540d01648203403452084d191180c84040302041010025502c00102400000c040d0b03051500f100d4402e400031882014255003500c0340078106414810248551361541c3c0f5000e040e484058100f80c007450b2541c1c0040e041100c005001c000d80f0344024190989030500794144013450308000740490110703180c03550340304594041d607483c082182c2c2000c0e0070403010140c80b0110810740d01304803190428076800303028010040e5410b002851040815075062110584542c880714548403900f4000304441c0c0090401d00a03a41c0c0c082411744001030b0315121800324102d0303440100d130184903801300d80211101840c8089107040e130102d82c10140d284954035200a01c8560343c649103080035150366408d0801034107401040020301a40142c940a07241880050a10100c103e8490548030f00711182034040c01107940c01d0000070f884004000120017280703442020780341c566540b900a4401c160b803800032510520312020a051049048a010340000b082400580c204000515070350321042c6c4044010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 778407410 1250 778406160 778406171
    0x181003081b0f060a0f060e0402010c020613140a170d050a17040807050f03041202090a060b12010e090f0a0624060e030c0414070305071412010338071e020f01 69
    0x44030542d0140d541654801017007c64140c48907401515013085140c0c00300d0f085081444100300d442600141c000080c48100b41c0403a101101904100c4001456005805c41c01d19040075080c1c41d801c0080d00200004d02c508016580b560301e900103079440c07a00000d0426141d070700d00d0104820040d80c0c001a00600340302d0803c0b82c0f450866800c0b003540300c0c0140c1c0200000c006041100001500e41130481d140c1140104c20b0020310191554580d141c150701c0140f6001c40b402d12079004001c5440316201043d40400604003400390628280c0c2e105850364900ca5005e009552a03a42c0305128130321a00745e031303542e807080d401c00444040c0e0b89102c007030110402c02002500c01d020b564001801410107024031a034000d00310fa1b40b104a0fa442000a030001c084c040c002c10708008802055608081201c0020040348071004c8242c0031540c0340d803618880441c00c0170040c1d80f4042005008490902081e112241d0346041040618603030f580344881110301c0d074074400340700c00721421040c0081c0b101a0042001c2d440e862411009012 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 778408660 1250 778407410 778407431
    0x90f120f0a0c0f031e0317090d0801060201061a09030c10021b0604060f050c070305030d060317120103240603060b0909120405130f050103030905181003081b0f060a 72
    0x75030f003d24480548401d05650205c2020b60107542c2c00072000740710303050101e5200e00d20700031000340800c1100e001600d45d22500c8031500c03154001e95000e00600c0c0d184000c0c0702c0d45050011981d50381c40c0045845021490101d070364803441d0380501042c4114203000d01115918840540000d42d030340d12090440f8401100c1901c1ca6445041c000101c2d0f081c3d0f062034035100f0580f400c1a00032920781e40408002c0c540d6000369440400010400d10007882c01c50095000403401d181075040c80e02500040700f0440c0a0900e0410000004940c415100c0781126000100d01e110000260907001015a218860032446481d195021040056951041e10000b505491a40781e1781d4031081015a0750404400300c1800da08180f2041250386000610801c609c07410742c402103410b0582d281c1d00c1c000e64038280c000f10017040704468288190305000516000c070107019802040036090560b045203c0206034000505080341c00100110300302c00300304698007822074a40c11200c051001114480e04c40a042e46c005240f1342c2005581e10 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 778409910 1250 778408660 778408679
    0x302070b071106150d0c0b03090d0221070314030103080d0c030203100e13020405040506011e0303051e07020d0b010303030b0102071406030603011509050406150b090f120f0a0c 77
    0x21181d40c40b10003010329031190720141800940000b49564821200401000004c4040c0c03600801405040100c58403820090443c50510304c5420310401154041c58152100062510300f01ca007401450111994503040c0e0700381100c0c0040c2001403000200c40000002082012070b50042120442c2050f0801c0240401c14084069101c192003c00382075111603000d0005d5008594171076001011900349080d02002c03903011505440048605841030340080300100100711900d82c240804403601100041c032213040d90f501a1990051656141e031240c8000040e02070700100d5011125490b0700202035070f502d400c10b40b601980d1a0400d0004a0004c0d040010021301540005481020750395200396400c4c0d0741e8040c20034402e0b01d81005002a60544d2500d04401ca943c4141c0041c01c090480c024003c00c06283c141008000d0300c2d000019840704d031254440c100302d440c05927400d455110204441110300c00d4882000144080e801c5a0500da890260182c2c100d00c8c2c081c00206011340324850400c1d00783e11a5200c030f00341e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 778411160 1250 778409910 778409927
    0x90c040e070c031d03010e010f051503070e0c0a05040302120a03020d110c060c0c12250308030609060d12030609110c03090621160216080304090911100302070b07 71
    0x100420000254001c42c10526482004c01420240c0001083d041009046080d5210001c1d854000765440c003e004001200030f40c00e02e1ba003a0140c004100c117030301d040c0f1402d8410b80001d203140e03061240410210040c0d8400c0c401c81c0c00a5800512030403042c80580c0c0310b01e40321180a039040300035110702107100c01c0843c01514030000410b02e50020300041810701050049c55840446507140358012800c20140036504c41d003904d6450200c19008102d420710110382100304481e00c18540c2c0a60402c00010000035000c58100c0e039024400b511292480d48800300411206045500028040481c04c03910a41d8554954072160480700c071200c0a002032900c05c612010b103403150090105142c5c00030418600c0d68108400109001130303001f28600c80c00f9960f0b0a841900200665140658615800c1508140c2e40c1c1080201c851020205401c100d56141038038141c0e4178401c5204803029252990311031000c0c011506c02c030740d0400c1c4000e402d0982e240130045000740250b02c4101e04072040c51400b40810945441102117 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 778412410 1250 778411160 778411163
    0x50a1413091b02120703141201151815022a010f030204030807170c030a030204051f0c1103030c06010e060102011b0207180b04092409022d090c040e070c 67
    0x5004c14082d00b50380c81145500c00c40040d01800600000349501d4810200140380c1101ca401d03170400d107541041c44503160040c0c120284c804001840240ca500705190b885c01000f117450b400c441d581440e610840603410300c00c07140d1007600d000c0440c0c032074600c002c5e4030b41148040f01c28099030b90500b50388012100317500300c0c0a68007014003407c00c240310907400a0780e01c0050610f402650704103e8204100312580310b255034050b404980000e40c010400b084103044c188060800301045442c104008040100024404010784a000c0d0180000c001800d0480d20b0a00841f50802c0b000e6083e01c0c00f645e164501c0b00c0525509440c29401903280c06c540c0f139401040f0300301641d07181004d5405440c40a103807203101003040c0c0d2a6101310000b01e640303c05c1407041d55114810402d5951040c4907508052a00b0200c0722003038440f052003100c089080c240c180d00140c5c0c40c0344094850920740d0f09003c0b403400c0c40c00143d440306842c081d0810b07009203c00c02801070040b2620040d000f03e84824021034134640d10418100d99141c2401d80 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 778413660 1250 778412410 778412413
    0x10f080c0309070f060509031501030f1104110a031e11030c070c0e040b04260403060518070b0715060f090e25080c09060d03050a1413091b02 62
    0x41180c0c10220402942c028410381d00300c5214035201c0300c141c1c2d1460481c0c2d000e030300072940005c3d044050303040a004c4056448100264440103626585514030099801d960040066421400080d00c95403642e00c10005039514401a036259026400702400915002e40c0f04598480006a00280091507000f50198080521100d07415921410340b140400e030040d890844034516070400205400e1401d10300c0603c21070203481c49245504103414011003107006042e01b400b03085000e1402c07110300c903809000c60b07040702d9001500148039914100d00404592845500712054042c40c1400210800c5113409031180314010b80090a1706100c000c04c2c0c00444c0c0507449002640c1d5103034032080080304103035801281070040000a5070101100a250581c1c480701203034034a014820301c1c4009100601c000c0102109820003940d5003161030420b94002040e201c59170300001e00300180000d841900d04d20650451461840c00001035440302402002e814041805000d030300c00251800c4004a4400080c00c68000e200340d1580 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 778414910 1250 778413660 778413677
    0xf06070c0209100b070605071b200f04022a0106030209010311010320041701020705070306052503090213200c150114090108120d0b0112021611010f 65
    0x1402d004815100802c1021140d90800e80000c3d141c4500d001420001e00c2800d002482e850b21030300103403d0744803000c84500041c07804144900000d0180c4500680d80039440307a0385000701d00c0c020010b985c07005509a6580c000e030011501450840b00401000c15271000310201c0320311b071804a60350b5422241c0c50b200195001e03404c1d0004001240079410060554a0185800704401060311940c411b425170281009016810001d0704103d01484d00b100440440e00d000001c1d817918100d506d400b50307904881d0101500381c5a9440102c0c2e000300c45402403806070091f541740003c04003411040500100110281603015042c20b44250450212034820303485090090740c21400072004080c81a001070700028490441403068881c40c4480c1e03201d02d00c079940208088401c00040d8000701007884250503046e807010031070394401c41e0000b1600d101802500e6502040140006802284a0040703450b52240121005603070b10004141c4c44003140101c0d170a803418001c0002e26528030b85070740119101d603442005200051480c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 778416160 1250 778414910 778414913
    0x108061317090103020c0a0b18121e19050a0305010f080d0309022106060a0b09030d1209080403080d050f070507260c150a02071a191802030f06070c 65
    0x140584000034040c075005050050480c4034a141c800d0485082d23036001885000c01c40007000482d14103e0a90019001d040e080701720a07081d50f0507002d410780c14606510003030210b040025059040d201041810307020070744503003c2c02d01d010342554048152000042d080030700100300034031304001d81011105900d00070105420001ca04170014004210b049a004c1c405007401a245000070b001d1540840c03040c006802182042c0c0b0400900401552020030740400a01100d40281c0d0040f80ca2800800c1c10304010120140c003011048c0107003556180100385160110b40801801680400b501d40f9003401c44081040381c81d81d0040d94048602101c60400251081000c2c1e000210a041108100b4501d40d0540c407e410764002e03158026040801500c0d41a40401c50215014159891558200303108000440c9021241d071110494001c0b4105251248589000402c481d00300001c50442e06419155007001885a554580e10303582507602800e904c01d105042d0404c030364503400700b48180541030640b00d00c4c040002c0ca = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 778417266 1106 778416160 778416203
    0x31b060a0b150c0106090507110d090b0405040207020303120411011e17220332190c0f0302060a0c050306010207090e0f070e01080613 59
    0x2001d100a0721622080282440c0250000b101c580e1250034080b0300e03000d003130141c0c40303403828a2a0200300256603078400641c105200040080d038031010803000c9c08840c805043e000313441008408100c2045640b41550051030020310203000d0741d0900218041d00e86242900711403e440d402401c501c00d072015a80410301c2031040d05010010650f520441400506003050540b980365074030b40e041c0200e2800680030322514260006000103030030841581ca40200780030301c1caa80c140c2000d40701440e401c00090340802980c010703243c0b50050605020003c080c80918000c00c2000d007083c0441503016102140c031280000e083c0c40c0c040d4004085504015030040100c03400706101d030040100c18014404e00d40c1c0c0c00314184017201c00743c1c10b0214691800700403150405000d82c0020b0b540d0b00c00d002c4002001c0c00c607290141e048464032001d450440d40c0302003203203250700c801000050080d0340394141c0e00c03202c542 = true := by decide +kernel

theorem cover : BRFrame.Cov 778237410 778417266 := by
  have h0 := BRFrame.cov_init 778237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 778237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 778237410 ≤ n) (h2 : n < 778417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
