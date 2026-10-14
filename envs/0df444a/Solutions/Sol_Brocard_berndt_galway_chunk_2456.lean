-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2456
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:46:26.118853+00:00
-- url     : https://prove2.me/submissions/341e8872-3e7d-41f7-8c62-0d721b81e86a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 441546762 ≤ n < 441726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 441548012 1250 441546762 441546769
    0x131707060509030f01060303050307140f030f06040e06130c1e0b0d02070204051315090b070c061404050307020a0e0709031401090b010b0c16150810181407110c 70
    0x1058400c583c0c58000c02014089040c02441103e0056102c1e49943c1e8892401440280000140c40a50469608200f144c010f034501c1c02c0084a92103401f400d080e01841c0c0b40c040c0414020031626075044d4032881001c00340200e6100915040304401e1060028054046d124640c0e01161a0354071221290100c50399002c0c051a0748400c003030180e481ca0143c00500b07040c5c05c1d8001078182d40d000d40c5d44101c1a044140c1901c10700c5400400078500d481d4040052001e00101e82e242076a6850050529040000300d00c8602c0130045240c001103c0f440340d042a0b0040c0d810b16003441e640380d0340001000ca02c120024180001c3e5204402c22140c40344107551648040c0c6860341e10340c01c1002e112002c084201d0355a609030030000900030801c06010381b0040f0303c019101c2d6401d420441c5820704100101ea20341500340401c000c0030140c40d500c0c01c1c2041d2585800d84003074580f40800d4030ba03200e00383c20000c105214040300d942100d040358040c4805e05e10405e00141c154880c9241030300c1660821100004a811104010540b4107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 441549262 1250 441548012 441548017
    0x7150515220e151503030d060f0f0510020c1908010f140f0f1504090602030f0109060b04120212070b040608090c0d0201170405070b0d0204050316060527151317070605 73
    0x1405800d51f0f291554145e49001100c1c01c54000d0820180e6010084c0300380c8080d440000054503094510510101c04520003a650307040c071031010352155446d50100c241e882c0101a04200400e428802806422018280c0c900076040080c00c12002c0e900b810009030568038880e0680307000302d10346210041c807629500044490303602c0c0444010b411580f42c40084000070081d1004522901c07004c0340c100321a504001581050740c3d030540c00680c20900030b01050082e10149454400d1441d812540c00c080700003d100c2a03802c20f01141c0c41380020078004200021f0443e0042142881002c10205480800400c0004c1061000103240045e0024419224031001d2100d8080344540042c040e80446080c142c0e00d110041007940200d05090a840c0c000c00c0800640c14200009070a280324030f610031480c0c40c140300004096024903842240d10802c07211501001d20600703080900c4080c005400c0505030010328100300043e074031030f040c111001403544800190351600d201518410300030403400f400e800c070b1600404075082e8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 441550512 1250 441549262 441549301
    0x4140d120c0618030f0f02071401082e030311010612030507060b100e0429060708070204020f040521102408070e07020307150515220e15 60
    0x681c2d4141000002c8541652158840c1c82a500d0507150025405c0040241d085800514195404042c0600640990f820300c200e40820a10301100c040d910b1500c0703103020781a10003612411114140c00da04007100100c006c007054902949454061a4102e01040d080751700324824a203d83d0034990304800000d100d5002404080c1c0104004640c1c0103400000542c1d09403480d0210020480031444e01d283ca051070b00460001d4014003600e55802c0c1810183d07031922440038502d40744145c100080444c01c0003200b00030f841589802410031510f80302d444004048690050180074440c4525004204001e1146840051829203180140c003894056010301e030090607a4840002603402d04542d0911070120134002c1c2d40041c00d01e400100f004501d09412403594140103041ca81c1103400400051011550507414003400e280900800212a0380ba0105240c201c01da851045a00000e41c0030785604c49014136030540401a05214100408000c641409a85500341c00130010b0001004c000100d00301c0851858030b107507 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 441551762 1250 441550512 441550523
    0x607060506040902030d0203030714090a030803190203090109110d050c040506062110060c030e13110a09060f1d060d0e0f0d08060a180b040f020d0204140d120c 70
    0x30143d09500090905030050801c00050344040204610142e00c400800010341c00c0a98072490601503001040011001d0301016001150004c08600c1c1d99460f408020300f41803405101f191a42000d086c3c5034042c183c1c0e2078058aa110041147e5400751800080c2c0400d4194498010f00d80e4800300e10a210180030020030070359002c1000c1c00200b0440b500100c25552650720042c9003e40c0d8900590007503505a41900400200300301319a8040020740c0000d8180c00c0190225613441d02c15006030541005040440c012604604020528000c280d81100304201566060b841d1035040900e8980101e8002080c0b038003801014841200c22219420910300071328a00606150203e81c881800100031f1514414101d00741441c1c0c0a5110a00a1039120300305640045044800801141c0303000c0c00301c1000e0442c402c180344190f5507103200d0a1642d80b1070340096070a401e115401d640704d50768410624002d405c684550700403907030114010381031454410441000c0927406802054940d80c6e0540448443c0c540d001c0c210b80 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 441553012 1250 441551762 441551771
    0x170a02100b03011112060a120201052b09211b1106040503010903170f04020d06020c150a0903080c190f020709020304060605120111090f150c0c100e060706050604 71
    0x1003004c610003e01c100000c082d28a406401d149060003840c0820707078003003600c02e6405035a03500140e038050b0441d0040d16500d5014040743c0b15201240d170228400303640a001780c901d0b1a00000c00c10941142d010300c041d001074a414590004c0000a542014190984855810309001d241e80010310300e6103e825916000b401c0c0c2820503031501701107402c40b84c0d107090a07804103000c080c0c0080100324441c01c2561144565004214a0810342d0100c0e4942140c01c200515498005c074603081c681c2c900700001e910343c9441c40c1410b0401c0c203000010200074403d60310240c000070b02d45030026290032a202c4c21590b000c3c0100602d6200d01c0b40359a000c54004801120990840c09100c10001303072a141d50000d1030040380142400684585080308100b80400c001004460503418201c44413665041d403800e0b80c001e81c00541d0419542008000084d803a0310604c10519032000b00401d4412150078005074010580400ba1404490300690040c192030b0122100c40103580301404002440005002e80c2003542c110001500205 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 441554262 1250 441553012 441553031
    0x9010e0c0c070e010e012108120402031f020a020708060c1e0c101401090513060c0309020d12020c031c0f1b03080a06061d06030414030304050a170a02100b0301 70
    0xc4000c0b42a0301c290309803024500140650310300580300071305405c850070520b81c900701d1f9651680d03110702a10a120360510001c40c0010195102405201c4200d0160307000781c84031900c160b02010094100f04000c000500c45d0000109001e600092402c0c0074040c4508040d0500400d0040c001d010380140070240c0c1004028402502c00007010480c2022090150b8808180b6580000388040300d00300580c04442444c1c248410700403c201e139070014010b1150000b1001c603e0100040c0f056001c2d0910301402500841140401014407040d40742c107a584d000c0540c2a901805590020190f13200d5040903140e500c040b0811441c080c81d400340b070025a19070031606140d4400100e003441001c00090008003900455183c0e420444003401700c1c450a4080e107100d042420850b1041c1055107034040030790414900030740b07000000c10113124020003d00580c480c144100c9a0780d140520388a9105c80014004407030710010804d121036020812016140c00d820f007503000b0311101980c0c0c5003110190400d5500076806540c2c031450031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 441555512 1250 441554262 441554279
    0x2030406060302120319030b060d091412130e0403050a05070f080313050f010608030702061303060216050f030a121d061e06031c200712020f09010e0c0c07 68
    0xc005a44c0481e000d56198403c11592055031280045407200301031a000103004640e1340c03070050300c03004401120f001400e8005450b04040001900441030051300c50100d20504110b1001c0042841d0740d0405020854076603120031002d50440180d40003000301d00309205405400d84103e000e011168010407012140c62081e48801142d54815680b0800100c03800d07204005100d000c000551070040204002c01c5542d180401c000d86a0080c210300a1080740001081c10307044001181c3e9001554020303404541c0c0c4e0901a811075000c0e02c0e8a10100d0321405101101c01c04940c0101c2500e809410607103071a901c5061a00c0c25500800c0394800b07240b4200c1e00303d96111a031110802820744140020310309084c0d0440d0300e13005110710700d4008003d58800e81c0081c20005051001610616502855040241d224192044204142c607030343c03080000309100381000003860b14402045012103900035641c00320207129150900414210902a1410080d40b00c008103802e100d18100500c081d5040d40f0582d045a6203d0101 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 441556762 1250 441555512 441555529
    0x507060f06180b181623090a0b040303120c020307050d0e041503200a080a0b010e0a291c060605121c050d0e01091209080d1202030406060302 62
    0x180d18a58540b81140340c4001c0c1030310854050b9a011107000340e00040e04c40d03041c103000718001c0c140c0c4403000102c401c902c1200c1c05511000110030b006404542e076844405014581e940050b4022849002d2030800000c0e80c40012080303030180ca4256580502c4001034410200140c103005d0030500031440200b280707801003101441107400c05402581c1d100320701e002e0300c010401034a59000d088248020300c10010000105000c2580408000e0b034a000c5a44660b417000044c01040a030b48403c03814066840410200f0074003414250594030700c440d001c202503d40c0b044040131900c15400025011a085051000c001042450b0030208a8001c0010300c05104408640c2c0100d00b13020000c9a9107601c60178240103030b10b450b050310300c02903071418004c0040084051842501e4110101c10f00103110001030036200700226a044000d6244481000344070814103450320360212441041032400041e240d050210b40d503600030617241410302c05a80c4030101103000c85500c000952000c5c204849040d540c0e00c0001c0141c568030701 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 441558012 1250 441556762 441556769
    0x406090c05130f0501230f01030b0a181503110112230108011d100504030c081b01050601050408030406080a0e06040c090b06090d0f1410060f050a060905010507060f06 73
    0x1c5481e03c880100241640c41c10780000d200c0060102c5002c1691030034a1462007840c0048520b00405090140143d00504107458990f40014002e80081200101c00c145074180b22400d960411004500b03d10200480781540401088030010303040c04e038095031285610101c1c070485103134001181c84641b43c240c0300500c002080c0c2c030000400704004100c3c444080c80380e0524060181044801451032010036034841d0342d8003c506251940da00c003c1360505205001c8000010b038011322541da103072964900041000c6d00c0c4408200650b0034500003600e1948558140c500f100c4c01000150304140c10201c00381d039240d5000345111141540c86200d480091802c1203020301460048441c04440e034106900c000030f039003010b082c2e81e00511040100d110961101e5201500594020030383d002804103030b20384294020640303040d0814a1165088035241d40b0b145601c0791048541b071100300700303da81e44c0b20180314502d2107500c51302001c124402400c1005501a0004120681c41403400049031110600c100e0102d0b540d641 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 441559262 1250 441558012 441558049
    0x8091006080d1e051209030d050f01150c020102100b1c0c05010f030e0c0f010c060504061508120412031107090506150715150801110d0518060406090c05 67
    0x10160000581c1040030005840440c0d810443d080c040148003130040c0c4943d0080e100e24071052000982182c4052050303c1001881d071f48184042d08100e040d094501400b80030300d42c3d81d583e800c41a0b50388103000e01c0c01c2414980c1e046e0040c00c44044a8010900105031000685402151710078140c0400d02543c1d8035070941600c40c4041071500c0c0d0910000400320710802d1f9013203003450314214110205600001d80051401000c0741c0715118180b003440100d800701d40c406001440b02c1d06000902081280503084842903003211580794401c00d5884000b580d071804c2c0a07a10514101d4104004d001c0302d2100e10114544500030b0400d2846803410001441c50082ca0b0b0f07004481c05550313441448481e180c010ba28803c0d06440c01ca095080140948416031b142800c000074420259440c41609040b103001c80c02d060040040c0002081000d01e25102e03550250f000369515032982d03207400000b50303c0744981d9003184001d060f050018003041c0e031603540700c20003082c504c2c8090b200b89080d00c0c2e000035140d841140712032403800d005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 441560512 1250 441559262 441559273
    0x14130812120702190204050604141504050915240d03020303100f03030e0d02190305030301090b0418121709031b0d020a1106040b04170607030606050a0809100608 71
    0x5000007507030020301820620854100051240001d2100100f0b206080c1c3c0407540000c0716214100080c00608100b545500d81e0465941000400c080e04944c1094085003a60244010398030340e46000e40f0350f80045005200b0544a40c01700d9034580343c079000ca04003400300048401c401403840780021048200e0050031401a40001f00300b00400c01044445002003182668106501c9e040d40c1e805000d2a01c6114664001c2e88000141c1d411741d03603092010542150002e000b07209041d04da080203516a402401800d44480c10100900142e051503c20743c1d82840f548080b06189a0559445c0d940e44070800c2b110400b0071490b10354a1580700708410341940152000f00003582d9500c1000824443c58a4229120800390001450b200c00160081105129030360b01c002d16110700704000300012030382d020b40d4105e030030204404a8007040031078028000340b414503020400c4817201d0341c45503412801d0302c002d030040b1000200107025665441d4000c607840c58000c0348201c10f54981c0308032800d5440885003140c0c000c44203540032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 441561762 1250 441560512 441560527
    0x2061308070b04030f060507020106051e09060a050904020d030c02060426060c0301120201021515011205011406030601030f09051006240c0203121201090b0603040314130812 76
    0x4005501c0140162600b441c1428a50707150200322030501c00b0302602d00754039580001c2a0620030343c40040a844000e05507411301c07081d9a00030264076465005140107100b014086081860440c04060071201d00170b082952580c0e60ba406e00c03004030300300c2d50100d0500108038160340c010382e031b41e0001d0400350404a030204100c01410258040c118205400030286800140900603a0110307901164159940c0301c40004940001d407004074035040b0048036021034240600188a90b40d41010380b0503100c01c6007681d03012100542c50282d0811114284a0403102c542502c540c1011802c006000d507511174014140000c0c0c003040400c0160a4442e4440c040300d65802862894100c4500c5100d40000750120189000203c2c00c1d804c801b00f0840848603005060080862120045690401980c0d81040803058002d450700f075089036203200d00740c1c207000d0480503c0c01c001d000d8056040c81310035284110b40503529140d8111218501004550000b00341200802c08010042044181044031581807081220519550001e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 441563012 1250 441561762 441561779
    0x140303060109150c02210601150806030f0a170702090901051b0a0e0918030d0501062c130e0706020f0c100206280c0c021302031b030c07020613 63
    0x940c0c00500d0309082d1480f070601030a5000c4250042c0a40c180d510914011100b070b490120383c24041841c3e200f40c0b184c6800807443d118042c2089808038040e03150404680c030b84070101354a4210988100340950701c5501441d000c540d00c0c581d032054100032110f03038924220158011405410040f103045143d0380d140c02c00d000b00700c0b05024503d00c03172614030900c0d281003580301100104100c06040780144500740040228500060320100500c521140d08202c0340c1e00c0d40e41040c080b001d0f040074444d080210b48640a0303040c2c41766241600c140103468980e003604450281100300088030b030039441e0300410165900303440c00011400b000a0340140071240c0007080305610b05000c05240a2190301c80781e003d000d0005410340f00325000034442d500070041c0c00c5100d0400d4408404004204c44088054403803070f05050700d00808903000724403004018004c0d95070310034005019030503c050348010340c0c40d003407201c007090310b5040e100380c2040c080c5030095540101a8508032041c0c0004101d604030420320190326012a00c01c100410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 441564262 1250 441563012 441563027
    0x61303120f0513090209030f031306020f03131205010f0204080c0901080307030206011208090406030b09240109020a05040801140129030705030612060403110c1e1c1403030601 77
    0x440e00d14000c2d00e050328031034036114201d0161050790034150300494046e06968082c40050041c1c440d0701c1c00c59441c1e405080c110b0081031100c0c8035420250048000e817802801001c812100c00e0100e054118a11031b140c42d003082c054840c840c00c00e48155586030150200682039000600c01070100300700a0100c0b0071158200000b40606a100c8241a4010015040002c1e004200b4504580004c0c80030703841d400003814060301510494500c0383d03202c0d1400b640030003003140c45500380d40a041d018048807102ca50408103140c800b9020302d2080c418803100303030040040d01c15517002802c54003514a0040d04240d41c8036050760035291550101070184003100d0051010110440030750801e990103020514941194080c55143d03480042c1c21001080800000200280c40f004821340c0c07602112022520940b615080040555041841861090013800310b020308905c1d2130b02d90b6850303494060142c501580402810410010303150b4a403540480704150002c03000c18001c0c000b2030040c066110140d0358900e0450001810207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 441565512 1250 441564262 441564287
    0x60c0106030c05011d09010b0a120212010312050703020a0b0601030908031303180e0712110c060a0c0f05040909031b03050a020c06040308030a0f0f150f0b1608030606130312 76
    0x242c84448101c0204ea4443c0c2c06c4504484c0300c404042d41c0e80d0209070701114501e440041d520800c0340001650007802c003607c81c855048a0107200f098104204a41040300c031441034160150040e407280d405840800e202d0791440d80c02001c1410300007246402650f0f40c25031038100b100c40c0c00c0c0c558040070000c8141a04404800100c4120f400b01c0386800303003004100d100355000504a0307010400300d10014410181030313620140c0030314012a1303200e850f0311000410581e10300040301c0c8a09150b0a01d2082e240d018050000120004030948565040904007020b000007010741c01d40680c2000303504107070a540880010b040480450103035440d00d980e05440000a458100b03584102c6000e0b16040004001080c61403081e07980000d420000411200c42c1c0a1080003e844070780f03a0b00c80300c9890640b141c034420203020419811521004010007a41d503070b4001d442c249005a1042c440d840590300201c0001840d0031b00215840032006000703505210b144d00e004600c200f0a500211111051003c4002e80107070040394000d002c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 441566762 1250 441565512 441565547
    0x90506060301021306030506031009050a060b031902011b0c080610061d190b040f0504140c0a08071b060e100e07141c240207030e0906060c0106030c0501 67
    0x14130740034400c0c4a40103026441040b0415565002058480e40d040c008034040d2600008184001807103411f04c192140d030100411908030f807030a44490040d00700480c4d1440a5050000d4400440c821340d0015940307800b20707042d1042d8100205448000003155861028041c1c00b407103004040500d0069003410705400320f5040340087c003031404819001c1121b5007500b440075810a0340c1e0041403040345031250802604d81d802101c100040818040743c3c0094054054040b9031003184c0034450703070384d1614140344210019541500c804ca000c11043c414180141442500848140b0300101c2d00e0b154050802e04c0f1110701c00c1c0c00c6583e59100d000c80300745101c0c01c0041c0703142411f04440810052102044403a0703a07603000e00c00c03c0d078080308008202025507980c021004201502421408000d04640750405410303842c43c95024942c8a0303002040100c00d49842a03400341585601e07101925442402085004080140400e0b44510204100b81010600303010b0803009601ca01113003071150341803100152044001855a007072 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 441568012 1250 441566762 441566767
    0x3030207180b1f020f07060201051012020303340f06051f090c02150108030d05072a0809040f09110d03090308030705070c0e040210110a0209062209050606030102 71
    0x1041c0d40e0f07034a04a403003590500034422000e0f0712a08240d08007404200e00944a0140c41400117070f464064004901c6030482128100501da04c0c0c00a403031111401082c040d4059200740030403411201c03401030480b540c000156016500c080c902d01c90380c0c40c00f29241d6080320000644860041005401d0081903000ba4030f44d0340031070789a10541d403200d030111018800c840610380c540550046e070758000d00c01406100c507503100c00c2e0301c15038440200c0d90341c0e40e005800560000d46010006a00d05100d055441c5c1e402e04611013400d0b451200d070803910414042c0301401d89800f1010000c1821700c4d502c03403041d0913205544030320205d000340290400110604040751498042c0a00c20840d400195200b01d2500a50303a00140e100c3d22920b4945040b034503802a40801000c1004c40c14000ca2500e141c940c55074480c0d0700c01ca4415048050b20a02120f011610001c20710140c0e0001071190300500e08032000341c0d40b02201600030054840c0380c400424081c0c40c0c0400d2102280d6940c03040e9014482d0500a66038403540a030300035403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 441569262 1250 441568012 441568031
    0x30b060903031c020d060303081603020909240d0f021306080a151805060117010204140d030201091b0f080f07030f050309060a0e01020115030b011a040b040303020718 73
    0xe8491248400c40030f00700c007903601440c1c0c5810700c80c1d0650b88801c1d103603502000180d80781e1030003808044080e555000c0d0408103c0c0850411440b9000b101c40e900000b810355149a1078040c220382c007503034540c050005002c0501d1039045003900c5070010305101c20b0240030442940ae0450050124403605c2480a00003581010010b0080e140d0011f0102200c2c1e511512222082e80d81002d0103008028440c04200712619004424051202c000303501c3e8140c41101d968115400800502c0500700d00c5941b090610301107105060310440d08d0a050320040d058028000810707410403540d1682e6416001d0440e0316084207a441d000c0c004180320702540c1024000400c010314080462040d15030b9a16164880103084650030103283e01044801d000352a149075018000c0c903104d143c511405030885c58006103660040d031900e01c482003890202c120742400c80313030131059505169003490a101d00e0b100d0850901848200c00304000a4400e06010080c0011030281e0f0192a1081c2010700b8000518061160040c005041200c02d5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 441570512 1250 441569262 441569269
    0xc0215010605071b03030e0909010504050705040509011b030204150309020906060901210c0807230c0124080c0a030c09020d1b030b030613030e060a03150602010903030b0609 76
    0x1505444840c1001034075242503203404c02205464030004115641c00d0480042003640207610b00c6540348088426034141d070f4038402d071103007200d104036400b4050380e0245008104a082aa1109801040b410000300d10003203a4145071190180345898103002903030020b0200403108041401035a0200545418822142c00d500060a00754010700340601c01c40380041e20048603070060007202c410741200140741640740c0001c008a8000c1400708052408900741400291109101e208007140c540b14a0b50113483c079128038070b102002600100b401e01520740d0788441100d00e0392071000c296640e0b001d00744500d481480c10312002c2c81c00c002c942080240190382c0c0344414000926507064160680310001c50040e140ca884055140141000d071511a100d00d4038030b1800101c140e450303086820702440c1070f011035240d612048031b90204025000d81c05030003d040c008540f1010320300391004041d82d80d0b051401181c07180b142024803500321107950000015039903910f1000100b40d014061034051390000c44660b400c22407024080b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 441571762 1250 441570512 441570553
    0x8010e061506041511150708040b0a1814010c030207030909020a05040f0902031b09060d090c0b030c031602030406090905041a2a16171c0c030c02 64
    0x102022404071203401c05a89800058030b00902c49000010450034805001804d2408140d110507a03e0198081320914a00070501d0280201116513854042d684d5a0f16a00c0b9500c001904c4005902e46401100c1c84400b810250b0848260161030460903030041b2014850860b80714181c0c6000b454010b110b00d20103c3e802150000807134288010240c1d4400401404075840c0c4160b400c22004010904408a640c1013070703501440c810034102c910003461110b001110b1684d40182000164020002c025144007148540c22002c4010320403024049010303101c5804002903001140c80211015010080101101d2110240c021041190001e545043c0c1490002015441180240011107072174601103070411101e400c03801803081514540c2407240c141a248034004800302d0502c1b0410000640020020009910031a4100612810f11481d110800c2c0e82d480024600b82c4030300c440c68942444042405c0c08081c00d10b00b0380506840700040e243c600c4e26030140c21511142480d030115804040710040041d4501070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 441573012 1250 441571762 441571771
    0xe1b0a140315070908100905060f0c040b0d0204080105090607020d08091005090c0a06091a0c19080c16060801060206040314160c0914010b03070206040f0309150804020a08010e06 78
    0x2a507074281d40c4251044c0c4100c0b000b54007503040d510450108007180001580544002c40c40351050f12100d889114031070b030031010142d55000714500200f2003082418011401413100d214020009801c00d541c0c0c2d00c5090849508135440000d613003010f41013040c234540c14080101c04000d00c1c2009581d07800c003103060a40d41d292030601614816a41d00110303807024820131402014100091424200e141c4845004009103002d104807010030184811210041496006440107034800344020900603032400d043c9007010040c442e003601d40311010004100c01e403070140701406001004440c0c05460a00e003102c01041c181c1e05900050464000c03606020000b50300c260244042c840380d141d11a200d45000f10210340c200070103e40100b0101c103a040c0001c4411460f00107110307a210030003192046a0ba0741041c00410710003240d103803006030040800a40005c0c2881c0c03102d0700750743c00b914180794015111010f030480d052102c03000d80c1c04074940d90104001c516200074544040c00c01c4800902921020b0b4030242e6640310080c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 441574262 1250 441573012 441573043
    0x603030322061d0a23033c071e030c0212031605160b040b071e0f050a0b0a180803060d06050c04230609040b03010e1b0a1403 55
    0x1a1605000e01508000101c6035070360540150001103409183c3ea600c13900e581111140e46420f044c00030b0250003e8490b0700461760b0300246240031003c50f400d514007aa001c001e141031001450313002e0403038044000c0840c4100f400e4404940d40e82c0d4030b4100b00c1c24000d0320081c0c2c00d82511210700e502d000642d1042141c580e165060302c21012588844441d18118000e0005407203000c010104081e0500000099500400c440407036400c5004d500c81da05400e82c0e03c01d90203070b1a040f2600b005908002510095500a120712054020100e01110341d9a0454180c0c1600c095406a01040c5d03450705101d00044110707007141000b481000808030136107800140007a0740f44050303d100004170000d441ca80716007000c81d520036440321007009185004851400036400a00510381c0440304259040181e1003020300c103d441450082003141400c06c4101040301a00d95003107059050b54031510120790540c000c02ca01d000c281c0d110012000c4412a180520a6815290380601d00c5034440c5003445000343c9021480d61504580c0a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 441575512 1250 441574262 441574321
    0xc020d050c0306090703020f151921020d0b1f0c0611040303090602060f0705040e1f0f090e16171e03210609010b0d0e070e040b06030303 60
    0x60400500300704030810526014002c031820005030348008074440050324402c994001c000e880c1c05081c00b245600700c94500d10043d07402c01c001c4920104440c41d10903d60858074200c0d01c805128051010000c5505038540c01140d00411804400d81803402041740c2c201c0709440c00940306001d00424880070700c0c0c2e030110006001d90b212a00e02032101d550071906030701e4458001541d0f20380d517900d00202000d4043c4205c5005001e1700e0040381c001d1860740305082c020132117640c0d03041c20103081140e4401020340103031410f2446803588203c0d90481c4400324941e0000c1c1680310725005407030300d4105000191415104103c031580c00c1a402c01030044544950340040c7c1c0c0441c00060808500c040c03100380340050740b4440c0401d102c141185024004d10000003007000c160f801e00a0030758004000f02000721980b060b01e4040d444a08540188442c901c564050138040045101c0480c030f4052445805040c811503401412000010001f08000c0c4100c0b400030310b4000e20250001e40c0b442c501a41c030000100a036502d40c030311001d0308 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 441576762 1250 441575512 441575539
    0x62e140a09020304080a02060106051623011e0b0d0209040602030a0603021c03020c04020909161e050c011802090403141201090504060b100f030f0219020a060f05070c02 74
    0x20164010003410015104542c3e13420182415189900f0121100e00180f00b240300100b0610300c038400352907a00c14a00c11603c1c40090540e1080d4400d01096440042c1c520680f45188982509014000004400d11002c800090444803004181c0da25042e0b0140160101149030005881322a0312941c0590014001600d03905d4440900001d407001d603001950250100d82990040e00552081010103807180c1c080f545100c0c001c0c0b0134841a1300a400e0302981c00004080080c24000180c4c00c200c10300140d40c0341005055800f0b10110408443c0a6001400288040350450600f01c0034030484864002500b0101050903c0c0d600003140e13020002c0c40107042114501055172009406415611403285020b2000950341e1070304c50301002820110780a45d101c030708100c0040420f05083d20101c008095680c0c589248506462041e00540703002c40800e000181c4c00c02184a00c45c200264602c00c180580c1d010b81000c5040d400e02105039030a44140c0359400b841d0206105480e608100781c510f040e070f8155242e02450f20b0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 441578012 1250 441576762 441576769
    0xa1104090204020f030a14100b1b070816331704061a04060605041406210123030a110303070c03030329030a020904020a120302062e14 59
    0x346000030740240c000305050829145a02c0910720844210001700056143c0c0079108000000030b0342c40b043c801180c040140b018071501740082560b103800240400910f64061043d0385411025032003e06980c128685a413a40c4142c0b252520042010b01180c03040310400c130001017144440c16001a002c1c414140110460a0207182c02d030510706030410441d140c62a144c00c007940a0b0207643c01c1d03ca559104003013000940e140500c584419601e113a070b10b039820f10342400c1c0440c00c0c0a260160765580004107000c2c00c0d2001d1a88404000c02014403d901c050f0785d454442c040d00072010b40c23041c00a1405180c8074800036510005030003810b80d500460010240d96036400802d0951041d1400584620080003002c0207264254000141d84800c400410b140110b030401459090400e1801165164111a54400140c0382c0140e50f1038100c2d0004040c6c504441e941c000019a0349034540041300560010700410810b2a1502c8440030f0ba40d001d0503649140001c22018404100000d002d980c1ea421040c0c60b1034115a01c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 441579262 1250 441578012 441578021
    0x9180b060d03122a02030a0915090806040f0515091209061b0f0706030c0507060b122515020303040f0c0527070c080d20031e011401020a1104 62
    0x3050410407452080c0f842c1d8101101d1240303403c00404d4651304241120600c00402c03124280c480d0340d55842e210703080808005040a2060700c000c2040003048000c90018810303c03109000714840e10040019030070920781030381808230460002030a2a001c0c002c100c40358502140019a850407070009941da0300780d40000035081c1c040e4800c0984010346031442e030784404c280000d030039544036229011101d180d950340ca021801e98170350040c42030000d5800d10481c4002200d0307400c0300001010050170708500c4200c04400c0d602e00321a81c0c3d1b2041284112004c00510200d10311002d83c09060b420000d485110325040010399684005440100b046100011983c28000d1000205024200080c260038080f9a1540d14124640c0c401c0c3c4203507652461407001c0340c0c49a014040071840705500008541c200b00100c05241e00403c005400044640c0c0e410403031150b1030328103100552095003003d6841c450803031030305622920440160003030010f40d00e030061501c10503a000141150007961291499020102c2c0d88003044c0580b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 441580512 1250 441579262 441579287
    0x30417040303021b0402130b03060607020409081c0902060f070c0302030f030715050106020606060d1404060e0d0309150c090803030f251d0d1b09180b060d03 69
    0x4200218000c42090360100e050304200070b62070140040804032804100482c4201a440881c1124420741006003050a60203194001d8004060340d040c0149500420103403840030404541d44080001c5902d1040d50b002481e10300700700180d0701000020410f50114005218040307180080742c0004c1202020003031490b10030400703940e01a083e1500c4d100b1010321155a90040e400271601d0700c9a59444407100501813041c1fa048483d15401031016444801c10b0142d03e62100020b04a03036a200c0c00120b003820881151940904e11441000a4070010350503c5410145070810110805041031052404a20355444400031070920300c8001800c145c40100c1643c4604055100700010701011082000804005402a10482d00700c8071071b5584442142e1040b07007030034090a4002c0842d07511034103a040c0c0c90340715142104006015004004a00250721140207420306c15071409100041c105003807140b40b4082c080c03207403d050082d540f254191169640c1c0210400010003007409026400c181c4007c0c507100f1032810649 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 441581762 1250 441580512 441580553
    0xb090603042f10020303060d02091b04080c1e090703020c01090204091a01080607050f180405130201020c03120d0b030c0d080a030c050a0507060e01020417030903190b0406020304 78
    0x60b550655110200c100709800e03840d02c0b6074040e1000043c0300b400032040301e03c1030034014603000d2281c50a50030040b040c5000b80c008038040746644000c14258103884001c00140003008018840c6000003c03c00048160070504191802c039440c2041d040c0b0340310701c2c009a8000c442800c026868107d103010707042c01095900000b07036109041141202c20701030401c034064030003101c0c01c40d480181da0b01d0b017006580d2044140c828500140c0104844584c2c5800350020340364054543d510a119141c4c2c1d880001c0c1607c205448605000ca01480c020b0219070701000700341d5107000c3c145e002e084800862488010300c1e0080a8007103103001d4550f0782041507580d0510603031092540007002020700740ca07541010b0134140c00521030100407038035000e440701007180508185c0e9034800c003035900d8a1610301141d80ba18060034090142c40f09540d000d0101003201c01c0680c400341c051780c40b00030045494012440425180119070580440c1c10300d40c1d00000004a000031141581c00751300100c0159880c0c60f41e1822524424000c260084d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 441583012 1250 441581762 441581813
    0x15010f14010c2a050f0d0309090218040e1f15091a041806050109050c030612010b0a0b0a080624030907031e140c010e0d1a0c0306190b09060304 63
    0x51180c005000070f05881c02925224510b402017814007103108800c910140114034168000c2020030455002880c000d0119403a0703070f003905c450001103405d81c7d8110b0048400c07500140c620800600441402c203100078070380d05c400d02150304007001c60720f200302142c06040001901c1d01c41d08003205221540300041c400c0c0c054800c1003015100e594015000f00c0c68901100c0c180c1c180f01c0001034201d594000d0314080c1c00400b010511b981c55503010017545400012488509540b201c2421755603560350711042c4d000340040c2c09079564500128100501e40b20700141070b9841468080914540d4031040c1103180748000324002642d41e43d45404c50a2442e04d400c0c1d520040c000604144071040512510540e407540c0c0b480358030800301035500804216112051900b0950010346200c2011141c1c8c540403420300c0c0f245000b048502003034503a205030760011030030440c4c40042e004000018410217040402000340b0311540c000f81c45103d142010882020b610908207418414030000c0045014008600e101c07200d2018240020710 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 441584262 1250 441583012 441583073
    0xb0c1b0f0616171c090302060703020c0c031005061306080606280b0409060b03060d150f020c010c0809070b030c0d020f12070e01030614040c020a1415010f14010c 71
    0x20750701c021350301ca80942c000000c8142d041858020030341d200f581a0003030199a130b504602100203402c0552480c0382e5128a4074840c0c1d403a00c0611900b00c503071820003000b096500e848014841510201d00603c005180340003810014074201041458010b0f00468004a030000c8516408034540f4004e04460341034003420000041c0d0b07007071b0500104204c405500061000c1d59941a04e6281400200d4207160001500d2041c80005084032041d201509800b0b000040e0280d0392111680407a00320a49043d503e0b91744120000c5003a07005090b0a03440500400248402da081440e481010b01018142c000c06040110703801e941403940d03405442c0c071205c415811039141c4040c5685a40006010b450a002061409940d41040d5100380200d034251a6200c440b140ca02c0c0c1d0440c20710006060300a12038085001e80441c0000051031a41d05000010310100100140c03043c180d21254110410b80c0483c00b40c03080700d0740803c1807a4484540310500102400e040d10080741c1418012401000c00d0348011442032440b1118 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 441585512 1250 441584262 441584303
    0x20708151905010b0706090219091d0309010c03050901140a030f1a15070203101506090e070f0f0215090d1115060d06150b0c1b0f0616 59
    0xc0c45541600a0440d0080c5041441c03812a8030a00030074258000801403400800c40703e03006420719920240412401201509042d00c40102a4000100c0c8a44031040303c10f07002940c000b4607800403480d0000c2c44c50020901c00180c204405104000c046c000081020291680111051502c90405846c0641c0d25040048024003c02da588600c00ca62880e203289255010406d01c0c0362400e000010701080d40070004881079081030742107404226414071540c40c0c58400c1c01c00310700030740e443c3c00d400e452401c40c11410010007a084005642001420f164003c042040b06980002e0554088426040c560222601040120b007030500040026100381111000e01030001400543c048414655a40d11440c0f5080394001c00d0b2101030f1030112154060004010442c0340c94065860760919114000001c0d140752202400c41100301030360b20034035402001007051a203005050040140c2900c96506012411011900241032540e0310300709035000b4280410503281c0c41c902d40318000241071300007150a80f10034206151 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 441586762 1250 441585512 441585553
    0x708190903120c0c02010e210304090c0807080609040f0303091209060207050f0d12110f010b011205060d0b09030d0504110a05010f020601150903020603090705090c1315020708 77
    0x1c903400d207140a03c203c401d03520642106030255816074400481400c1c00c1c1c10400300d82d00c4209040c0c00218210005e80c0503400400041c40100a10140419a0b2401ca030020b00004002455001800a50320030410b00c1e0703030f413030f285541d101e5071144c06a02d20760341d00d0130214018135020100402404c1003030105101d082d0841d102c84100c0754142c0c00c440400781c5a90502c40d030150030350305142d00807207805d400e82c0000345600e250404d003090518040c602140c801149030318001e005002c656451b551500303058950352384610403125140f1503005c14000d5040c072034003080668602920203080c1908003c08200414000c0c0221010300000b21828001800c240c2400800f00d81c20030710091040d55002800035095004064440d05c0a0168020b007c0b0780c0c0c41d00d50410542d200e80d84c080b42c100001030340c0220060342c0d0600514001c48005000702081800d00084c0440760002070300b04d00b00410240034001702c0450411501040d1540200d6508800b11804016440c10109400a020303601501040c104c200340410744 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 441588012 1250 441586762 441586787
    0x702040c0905040f020423180a020c0c0915010c11061b060f060105030109051f0b0c25060528020d080f1b0a120c111c080708190903 58
    0x3000c000c400c0d214007880301244624801c510710b98005044800751f40c039981c400f0320000700d00507204940ca46403000c22401c003904100c1c1c110300d05e00e50108480740080010000c120560b00300f43d6020070281440080c180b00c410090034000d040100400c104010000483c407002c9500701c1c081c25650b101d01920404046884c03024580e060644030300c1d0000394808200300070a40c0166010b84805180d07908121424024240081c80201d50f0240b0301c0030b0b4001100702c40c290000a290301044141c44000e0705c00514100b20008065600c16113401100351588c10080800400310782d41070034840e5441101a00c800181000911080d102c10804031403090302ca60045031800713003070300f1542e41c0e040e540e82c0b40e00d0020f071000b205807690002042031241110b82151131400922881155060007609001070502076410745030741c0d61300200055990030441c0c1c8100010040e00300c4c45000d2058001c9584409540100800d0009204c0f408101f031300c801050000320714141d00c50f04a1946d0320188222001403c0203045048200c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 441589262 1250 441588012 441588019
    0xf25090f060201200909060909190303020711010801050105041e05130203060102070608040506040f0501020c1c0e03010504110d020d0c030c0609080f060601030203060a08150a14010b0d110702040c0905 88
    0x504050025228422101702d1440200981495250041407200c40c00d0010100f084a02c60410a120301c25100301c1d601c40c40b24425034026a40388002c0c0b07041040a0018440d4605200c085801800300e0780e0030406072001c0c0c1d607036482c2c81c01012982040510f0700c80c510f54000382e00708440b070200c00140c4169400943c840c58003a000c50f12401d44d114001c880304601101e0151a64204002050005032241c090303030300007030081002504000d01c06100c00d09242c0303801d000c1020340103603005c06490560009099850002c0440003040649015100e0340040c10324203a50500c9600c141d10164110740d1001d02080020350880d01a9231401d440b45000c0450744040d00850011071000300000561800004010310614003801c0940059126440150b0285d000030b8005a44806503c1011a03024410040408100c400301007420a50401d1040703102100c40d8030424021012484005000f20745580044412115207140c00060044c0606e0b412081c900442d04001d501c10304120700c100890717a000341000203030789089 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 441590512 1250 441589262 441589301
    0x3060503060c0a0302130e1014041e1d0318040f060501020d030c0917100b0402031006080a02070b0903030a0e0610060806030c0303210f25090f060201 66
    0x14420507036078039400c4500da41e442100700310008030705220381c01030110300c078500040c55145611001441078880045403410302484404600f04110001004440740d60f40c003d890800c4a20342d0700d00500348041d41030235150320883d140c0d0394501115005a490031000c0041400f07031b0762500352100640003c1050340040728421801c00e042600c0c9940244941011070b18160024465800800300a40140046003810020310030310280000301032000071051452840c800e0045c1c68207a00710a40002100c1c00b0070300711402140706000f00841d61940010b41025104242002d0b0503503601c0451030400b038440c504008140c03046000030f024040c40000040c41c003541c8030220a124055022009175520003003103c40980500c032480d400c2041c03600400b0300b1900400007405444c00f4542000110346168010b10781e140100d00012600c000c41d8084181d2650000002c844411103801c12103002541e0301422940356012414440314420310303501840280b070060801400342080035649480c0a4003c09a512002210311401e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 441591762 1250 441590512 441590519
    0x28050c010509010801030b061906030609050a0e03030f19060e061f120b010c0204090f02130506060702120a020301090b090d03050105090408160b0114150c2a0d050604030306 76
    0x46058501088040c4d445102513842c6403601903d10341e01030011138002007200403152a5641250310703000906400d46000c52058985400c2e6000c4602c020403201000780381c480c0c0c4403660039001c01125008844041c81030419168125443d2821400c00154880d0340c0c43c0a5001035541100540c1d030348900c000f1140b0f0880d602402562a400c01e504100740b00c001698100c541900c954541c0c07059810b5007062401240364881980030030300700c83c0c000d842910868245002802103280c1015070003a010304d80c00003030080b414081c000c0340d4103001e04a00203100d410a141403a14010301000300c5000250000d0080c0400b00e051f0a010200e07030410f96621006000b880350607035015000c1e000b483e0490344090030403c0c82d0358850f11034889e240c100c01030302140100c44051007804940100c1096028000c00c0c0c1d6950f1050400c5020490a2000842c411030f50a60500c011040c905d00480d040100005050801e841c042c4c0e00500007080445110f10380d42d200403012000410302200041c13041c441c0d807180d2010005941c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 441593012 1250 441591762 441591767
    0xf15030c0201050609180c0613051c0b01180f0c0801060e040b1e060f12092a0120010204060e04050108120403032d020109030306090c12020c28050c01 66
    0x3c115001070700890702e000480c8070911011810039401c1003901c00e85291303410410000340a03921003000e030100070044d2441406036150180384912482c2c00840818205001c80e030701d6514005051140f5203145c41d54002c010448622030304030950100b1030b09000c01500c08540b6000c1c0032100203000d0b00000401c0f0b50404c0c07aa41c2818420100103e20040282e00380c82d404418202040c00c42c0140d10390442e90501056116100f0500a044002c110f121030030f03802e14105016a2410003e1841e4400c604c00641100d0f0000e60b0061a0704a43c0754286040c01c008048a07419103020342c1c500d1052503980d8400140010301039480b00c01c1d480d03844812641031102c0d0766141c800384d6482c2c0c090080107108803020002040040d01800100c118a6031040079820030328040d01342c00282c1d2407000181c00140c0d440344510410980d244c410100030f054402801c10000041c8030009244651900040c11281c1d8001010000c81108101034003030000c600380c1c0c4000c281c0101c500002c40d8a00c0303542c21a00d5210700c0c14400791560 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 441594262 1250 441593012 441593021
    0x20307090b030c0403080702130203071e14030a0905070f0f050a230607050c0411071406070f12140106110d020102070503030a05180a06020a230703050306010203040f15030c0201 78
    0x100038041c07184c201421910b40c032038030b40e100301422680000a0b0b002c009205c20341e80003446c81043c640d214035806036a8070301d60170000300f19505580200305454110520303c00251095913009402c44000040103c0545411440e007031264002121106680e4000100003401b403103000c0c15500155021707403a0310741d5091501041c0c03003400080c0d48d40201410610005084c0840642000d501980441d0003076076408001c9000c460217241c0380080340070001381403010300c030020041d00700f1a180341d0001c01861a00704001440001140e009208000c04400340d1b098190258108080d060703a0904448010b59484d24003a141000f440c84104450040d84800303142c0034010720a8840481c0c105004e1031642e81c5100d82000184401010101301c910303109114010401d041007015003651159100580d5039012000162101400e40304042482c40304003140030424038404140c03005642c0c141001c50301c070786035800182d0840c003440d003201c11541c08894000030400800c121402909030540c0f4100000d260014049090705c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 441595512 1250 441594262 441594271
    0x12030c050c0604030c0309030b0a050a05150109140604030b0906040201480803040b180a0c03061d0a06090c050105030105240f0a02010b0a06090e010e0a0b0a09020307090b03 76
    0x50300008009008079000f60b45e103000c21403007072401440158a03580c4080e4255015507a0800e02580d403400c001d00700040e40300359a00041c5115441e000c0008036400200b0355800c901a040000c40354070803c904c036842e03500030341d4088c551003548176a643c40d0110b0f403030341c4d03814007164182d002410420352411400320141292181e0342c1541030344004500301c0a4503015451040021000c1442c00fa40203002003010103002d140120b20a0303a544181e81820006174a800500c00f1051071160800d40d140c0000a2200d40d40c8021a40c3c03200c804100740200d0b04480800c1a608900c440081c05441c0c950020010b00c0e910852503288607005146500352103800441c1c060209005941e00034035101c2840310f45442240200c003000141403042464109408a00d2140340c1113461603038090f070f450300850b01c582d181c1410300c007000e0603162405a202038a4840c0c058a41e00c418070420040c1100d9078042840c02d2560340000071880d40c003411092800d80d844443c54000d600c1140c050001485d160000b06015180030b00f00c9004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 441596762 1250 441595512 441595537
    0x10911041413210507140d0203041406090307030b09100213120219090204170c0312070c05091006020606121e150406050708091204060e06070204060312030c05 70
    0x140e0395a40410b054511010030b06490014040304540c50440c1e01900100c0100380580c1c80d55100c81081c540001401108808000c068004c81590003400f5400015202119000107507889102040800b15481e84a11282c10303415004403d0040144413102902601131030b0901c040300c00c1c00c2e181c01c5c03006040b80900301d081e508201c0707814000c0008080da03980e2030546c140010590b50031070303041c0c581c03100716644240c1c013200b2040d401050800070706100d020f8022082c1c02c070101a02110310040c4c0003035151040d654861440400100301d400902203500000d00c060230001d40700c1129030070071030301d01010300000d031094200510600001a00c642400c00890b000745040100521081012010701d51801d003c0b40e007058191310801c88400d41406003081e070369000358091000002ea50070400c0740184120030042408800d603020700780c194541c108110460342241d400e403401c0340c0d1001441c4005041c9201e2010003940c801e082030404414441140c0140210750400d4500f000880c480c90829159401882c5d0f03902c41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 441598012 1250 441596762 441596801
    0xd0f020a020129031e1006090c090e09030301030206160b0f061c03020c0424030f03080708010608060d02040603020303070507170c0604031202011e05091e030703030e010e0f01091104 80
    0x200c800164100c0900d0520003007507601c0c5c107250021b10821960a40c0c05030340e0442c0c8800c034240d04660410845009044250321100003440c00c1241607940f0b10061100038025078001903c04040c5904d409202d9290303500c0040c03002d03c0d0901814002c0010016519580301e1506001c0e501d00d400d155090308120345078140c01800f46001100c0c2080001c2c8007180c504000380c0410320201c02c400078400c1d01c4201a500c28144400103030018180140840c0b40280258241b0800c0760050184035084258194440012107180c0103c051501c00725002d040b03154002174041c030001c1510030030000042228425600c02040105940140064881c2d4800071070f9a995003000040100340081000c580031150f0150290002042c0742c211291400a80320040700f02050030380cad0740c0c03040c40140b590a2022030700f501c0507004010541c0e4282c403195a00d0344a182401401d1594801d281461880203411404e1011010825104100c42c41d00c140360283c880d85104445200d003100008015203000c0c03140305139540c1000040c12 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 441599262 1250 441598012 441598033
    0x11040f02190c020103060807030503031f2607090f022101060c02010305060f120d020d02070311011110110406090509220f02030604080d050703061a0d0f020a02012903 73
    0x750b625503005000c0e4101611000017140c0300c501000983c0040d0722510003550340f443c04541d2003d241c442c003840b5090303058100b2002c005102064405070302c541203100d01000d0003031035030140619003e1550f029108060030300300281c111088650140c0030983c2038048406058403000d0010000d0f580900480001c1020403a0820240d4400c0d400030342d0281c030141c01000d04240c124001094040c0a25514546030b001c40440503c0715410301c482d480c100c540380000c11a06055544890407154502c002c0c81c104a8902281d00d40704100b000152a0035840400803c202c2800b1200c460655001d401030b40017280c45a00002524204002c2c210710603403100245281e240c000b0031005203a045800303001d42e400880b04655101680d02801942c0c05070b4401c08080c0d50f0344c580410345c1000e680000341900c0906140c24420407034000c1c0814180300074110403030f450307969416004c0804000d000d00300c00036221030710204031125000d40560100fa0020604040076542c8800c202e400404108a00c2ca0160540c10103041d81 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 441600512 1250 441599262 441599267
    0x1b140a08100b1c11030d0e0a0b0f0904050403030b0f060f0d02091f020a170a08040303020d2403030806120a0f020609041a010f02030408070e0a090b0411040f0219 71
    0x101e807000e2000745541c1c2c07848800c1c3c030014111120100c00341c0b03098207010300d508103a00d820000c1022103141410030900b01d9108000041700c0030114070400010040010740702002e0819141211800e120042040009040c181001002040303441109402855507250131402c81c0741c80030035070b034041c0c0101e80028a00314150007603001030340200010036007043d4050f410044200b40c105140e40d4509045d030080150302c049041511808503550100d64030310000700000008203502060f80c03a80036815080141c2d0721900c0078801002001e819010401060401f4500c40b60800c524443d102224040d44e6040c070315450341e800f04010711594100c4510f030b951100035039000003220100d2000e400c50005000da0b00b08107024020800b901d00d030041c50502031050014035040c96800021800d00c0382c01500c000c600341410410b405956072114011200300018480008004050617005480c907140d000450034410b080914148028899129045110380c2c1004400001c0756800d10a8444800c9103002c2051a0905a02c09 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 441601762 1250 441600512 441600521
    0x61b070f171f060503060109020910081608090f0307061407020c0109090504020a1d090708030a0e01030e1e03130b120a02030403030b041a0405060a050a0302060a09031b140a0810 78
    0x240920151694000100e031782c2c00340200f5000301804c03a00581da032880c202c00c000f8401c40c103054205c01e0140000034004164118100c2807045400d0b070800503030030f40fa400e0446182801d80e03000448184400200300007001201d421129841e900c01c0342109031500c44070f000b644c840541610341030004409017401c10a0074031a411040e0414000303010f81003080e4072844205010004480b116849103031480900900c010200142d6000b0003d180184d0b050010f040b80041ca1201c1c83c80085041513103407504241d424100f8014023143c002c090b00040c448000c41d510040d2a60040c02d86456034040e090000200680c49000f103400f01d070b1180260300300c41e64886902c18020b40001d40280c040596070340ca20099030304c0368450b086054041905110f0404414820003040d2030740245054050390900d002000300d5226043c1c07107016a07604a030000d858501d025400c407078542142c0d10181002500078080e0301010501c03610030080e00c8404c01000064a0f200342400a48030141c841d010480d40414a09088440b05a00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 441603012 1250 441601762 441601813
    0x115031a04110301050a020d064a0c18040b01140702060409090f03020706021501090c020307020307030b1506090307061115011d0a0207050717030c030c030a08130503070b06061b070f17 81
    0xc0040b801541608032b2002d522040f15000c040690004148010803610365291107107560889003800012480740000b0300501c0719900c42e041d2540040b521604558811082d180501a070300c5041140008d0350915014280c41c00c40e05a02500a4910119007280b020415007000d024070074030000b2a074070b0140d908000f004080303410011800103110090045e40d061118000841c0540240744003420301c2c0071000b0b9810380e41981c00340300385d60400c170080880d1808207903a401c84015081440001c01d50520707a0303007001c031441c2244080d038500c1070001c00c101d014070070580f43d4840044010500c640ea0030211404038410800c000c1c019a1202004100c0110904040d105030503004050b0b03410000324418980c59601329651003280c980012561442030340e445000c143d400b00b4051504c58040519450b460788902c100312001e071210304920700181e815144d100484d0710303100c1030240c1d0b074100303a40403881c980d01d40800c1e00a80c4c200b01c0b100c54002844054220104180c07001c480040d101c00514003d40c101c2254001d072 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 441604262 1250 441603012 441603119
    0x7021218030607110c0607050a1101092c0f0423070b0406050d0c050a09030f0305040b120703050703150501081008030301170115031a04110301050a020d06 68
    0xc1100c19102031004a0085085440b0305092202c00c000301c0d801c0c51012001c1c00e00604050000c100031441c0098818885034000f12045132030345924004132100e01c2d131034201188649101c00c0704520144844180c2403840f0000c6841007030f07900c51400a0080303400c00d60b07024002100d6181c040c15118030002c13a0706851350f000c404030703001540d9403a078824198000d41c3c40400402c0c0042008030780315206020358829903d007890308500e000920040542090300e28040035105040c2d8034042010140264115030242c0310100b01309844400040381001c5014003216040000b070704000108070510300034043d10304105c10208002e0061030401004440030b40008040030b050a099020000b08644140b000b0750181c07401055118007051800c2401d42903680000c0400106040745d1410030100d200c0300002140d11408000303100007919603050581c0c2c4000131592407545546000706020070f0302c2c480d0f801082032040a002c140021176580c44100780d0440ca100c011644980c5c034040604941c10000c00102d41241d070314 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 441605512 1250 441604262 441604297
    0x60313050609070503011b0f050f2803140108070510020109060e390603071214010915030206030c0c07030c080d030501080f0a02060a091d010e0609070212 68
    0x2521181d01e0984280c0300602d071038200b0001803029040070b009540c40600b4540c84000910203003140180662103100f040000c0000110305805000c851500705e07104100f00c402c411041c50300c441e1601a91218096035440460328042e6440307035540070010044d040341c0d80d00f40606005841c0000307205d86000c1462400045540ea01501000158944204403540c0d0002c0000c1c000036003018000c00c482c0b800c2017503d416842095a0140c08220001111a0000001d41d03c40d6103a848041e01079034040790300070b1500211420015501412415a100d450490382540c8007881840303044c10b4051004180c0c0d001c0a5040031040000551015a2400034041c9181050441d02596500e8485200100c61500520340680043e40c95065260741402010301500c0302c600500340c2018010f500560f250000500240519030200391003107a00c1c01000148000c00c0c4c0c8416240803a1100202c5500d00042409544010110480440c8050a0880c5102c2c8600b410750000c5c502802207003460748554014960308031600408 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 441606762 1250 441605512 441605551
    0x5070603020d02091201020c0105091b040b120109062007030c0204091e0b0402150324010504080d0504090c09050616050307080705100605030f1f0e0607020304080706030603110603 79
    0x80c903800e4217044070710800050b20740000b0b40009083d5000a09080b13000c0c1d00410103d0311000c2d241c01107400082e4120f0740000c0b10200000460154030345a0754603181e5510385015081440110f4011290400c0c4142a0440c81c102d0740000c040940190003018000407102080b40b001400c0030f5102c3d00d001c6000301110304a580e0b0301d829950003880070540c00c0b59401c0301c00c001d220460900007000d980d4031001540342410351a2a8401c40e40c0504c20340d010306185a00180354007007070b90140c4100d81c040c2403d5000d0f42d2880f10603210141441e0b100e0b00c20300c100c1c645080080c82d04107118541000c140c2e200180071500d07000084103a41c00c0d8141303a8000b80c8442c0410403130800001c0359a0018401030788107001500081c5608290281103480310362116001c4e0b042004510b00c0b43c2c3c40481c65200e00c0c041d0088240300044a400044001c003610000415144111400d0014454000014100700e070483d000321095603031541c0d800c405590b80c03440000d04d50300109441c48943d140c140c010f543d01100c0b40b996814074800c07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 441608012 1250 441606762 441606769
    0x9030304030519062a0e01031e06061704030e01140c0604030305040b090c0619020c040608030c0f010b0a1703120a0b10081b070c0e010b1206010c05070603020d0209 72
    0x3180103e50010b01c40c1c000b89410407095000b5101d50200d43c0761a61303880d24045059075425482c1c401c402d4100040e070725414000c3da009601141d01c1340e00100c0540380700101c000804000b082c0c1800707001c0200c1c0c10400f1100d1982d458498251146a1607614407600e00340c400d00640d003050340c2401c0000d44107014002c294a04c0002c006151186009540115290505062213000440090b00386d25450304903603280c54192b1943c01c119980381807006900a00c03001414022410300b1030204e0301c203900c43c0c14864001240b15000000e05044450032041e50b0309413211698003400c139400000f089800c0050100c08102d5540c030702c1d03106103600105400780c03071505d6482d6000d00301c180402c80d80784094603610407414078507040400342d00075829803070705018600303040111030400070b20140d506d040c007180d400164250070828046a004003d054403a8a02035a58480f903a0b004c1e550040d81c3d107101c03c2142035002400642c41a200511191f8000c1c0140a0740c0f03040080490203588481c00d95a44240c08020500d910b44 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 441609262 1250 441608012 441608023
    0x5250e0a05010e0114090f070e190510080906010501050306220c020706031a09040c150c030f0804020603191e0e10060501120504030306090504110f091b090303040305 73
    0x400d18100148541c14480324608400068208984184400e81c00490503129040e030345800806144801403140d07a030350b1b0120b800504003080780347c103c10110581c0314a09494503c820585104a031186802c1c94460ac00305c1c0c081e4001c488890203644644010040d95018100440c1c01440140c100100c042500960f40c1840b04c0070ba40801c68aa135504c62000282e0713061092402a1103030f13240500c945801e00c1205a4110620450380b0301c034904900100d4100601d1103c080010401c4d043e041030301007901d21010702452000103082d40860f0742852046105441203026601c1658010000c0f0708684504804009852407112600c16160361780c0110b115000105041020100b130798000030440001080b03a850500d2903c10b6038040701410144280416a000080c1ca014403000a40004050751a8201240949110f07400f9101c0c4500d00024841440141501051840b0084c0d68010f048203040702407012482c0c1c22240d49001042c81c04c04d2003c03915241c0000c109030b500080803030b420a905c2e41c45460800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 441610512 1250 441609262 441609271
    0x30406121b0f1101020a050a181203120b0a050d0609031107170f01050105060a050c0723040509071412150c071b0503070501050c0102070b0907081905250e 68
    0x10300115a640d002c1e81d0702510a228100c0c0c0310009504000b00140c000c0e02d140182e013001014801c0480c00030940e241919a0000280620803c60340300100c181400303031584058a03200702d1020300b0300c141018281001601207040f240301610383c0344180b61a40380c200081060b21001c500304071040c100c4004420702007107464058413180218049100105822034585260445004070350790505004100913a60b00041d600300e50076504100e65680c007418420750814a1340e0f008080703010a9203162001c40a0b140b500e240c5883d00c01d44082003641c0b280005940d4034000c601c515114407103410313950311150801d00c0c2c0c07070001c60360b080044848864400c01550050a0b0484500c0c5643c240450301605100e580c8032000218103452107201c018034104008280c403402036024980c10310000054669440e003003541281c01c883e8101c00301507a0790504054454540c9070f00d105400c098480c0802044842501c5488008416071080c02840302c400255400704600326142030b00c0307820a0040301e0001c5c0040b080c441245c840d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 441611762 1250 441610512 441610517
    0x2090406060207150e1e12030d060603110c07090e030d0e010f05010f0f0504110412060f060f0522020f030a0903080c030903030414030405120a0c05060705030406121b 73
    0x10103040540750f0b09405030000c1c11070b04100103214561716940390041015202064000010030745c250101c0031070b0400d5505501e55100f84400115150340100d03562001003030340e4440c0d80c14042c20300c1c400380c0c080e6240104032580c1c0b2181c22220041009024542c400200030000034103407030601c40d82c5004601120401003400741c50341d44400101356000118458107000d0843c0700c000d4204607003805240b030002c800c180203040c02580c0e41c10406041e41405400e8500401d07110800445801d000c0c500075029041c02c10000f18078604080010030b03030590840040043e20005004c5038100396101d10080300c00c00c41c42350807401c1c2d96800c2002c11070150003c00298030400400c14003081c20000d41c0b034010100300c8010201c0100c41000d10601220f900040b003260707000381d0081c4000350122440300d1450b085111b140d2001e54000b4042001400302180400d40e01d544d41c1c000c2845001842d03840741072100600c514040203107280c2042105001d0103001301d5034000200c6056a0004000420300c04c5804c0e07481e10798201501 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 441613012 1250 441611762 441611773
    0x170423032206050406030b0d06091b060305060d150e0d0c0c0b0306010c020405061906090e0c0304030c031101110f0306030c1210091e061d01020901050901050d020904060602 76
    0xa0800010a07111440e040480306095280341070720040070b038016030140c84201a1a000070100f41d5440e181d18600654108204001c59078041c03512040c00040d108140000241d114400241c0743e010348200d510540780600304c02005076041c0d0300c001030314040540036480c166544014080c103680800c03000740800410b49912411002c3d605140102504a03404280502010810000c231640d0001050015070b071305540c0841c60f41c0320b56002800800c0d00040d40c00b60079100140010303440c2e03440085c0004984011611060700c0c1c0322404000001d206c201c4000d80801c0d002d00c80e000000b441804a05040ba0240c0300004524055020302646640600021000070f078000c024400d440c5000d100c502000c072001c450440d80c003080811010b807100e000c48980d00350b0b9980e9160f00d0f000d000520882c4200b004040c483c046020f141807800c80001e00f501d00301f5421004e001c07007200019003014800c40d848444161900e41c200310003c0011240b0f070b40310110039207419400340103841c43d603101c900403180600b010790081c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 441614262 1250 441613012 441613027
    0x130803130617040f03050903010e060a0510080712080c070902190e06030403081501120207051e03030709090b010903020402120411060f0f0703020f0609060108120a17042303 76
    0x200b6031525100c900c10300c800715806200000d0b01d424a8824159414100301ea1200000400640148428030003098280038031800c011030303030b41d40303600c0a8420156100401c0400c0e46441c0910354454103802a96240300c004881c00303003c11450350180000c105413400b00d914807500d40290038280e800c0400e9590344898030b1005030030b80d1908003d00140411056883e6801d500d41034030300602500d4064040910242c41410503172550340300d8102d585643c84000c8095649500a1078000e0fa00e400030400e8070080f803452400d02084404c00f1003168010142c9544074015503090290b01001003404c000ac090500550361000001601c850010b45901d07200d442c207103480c0f481c02d070502c4c0e45d800003d240200e01c202410011105103140540988800d90202441203864151600c0c0581c40d1070002c10204d990f40c840c010400c6051300740041c0c254140c980d00e50668484200d02c80ca8007400d4003c1d045207102007100c0b00d0390a0b500e9080d040c94603500038095525118004004815005001c103206503c5d03000d50400600031 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 441615512 1250 441614262 441614267
    0xa06050a03210807020c100216120204060f031203020315130516050a1b0204150f03150b13090f080a030b031b090601140702060a17090d141308031306 66
    0x10940c2c4003030382081c0655142c0300b04029240d10b0310840c0035120301540000f000009100b00482c0c010200c52031a000300c850380301c0400c44003600708880c00701c0c81281400c402265841c01c0b048250112a40440480c0760059100780030f802035000202101010418048980e085603910450009107030b11940d00000d050a11145401001c0000310350341041c00010071408181c15840018615507545d0710003640d4402689100140213441300c20101c41040001d134001244407820404c090040300c1c450008803062503005442c1400340e40c1c80c0c0080c84c0c0d0024004c04036000c80d18054000d0710f0330500c00c81101e5000000b5542d141c100d604210084d01c00030350340da01107042d0b9040030019071302a00043c03811000500b4840300007a03a0158020b1040b41040041c1009070441c2e0140e800382c59074079034028480b549a401040d401001403500305004420346a40740e02044080c1000f0032440505005075a6990100d07005c81843c00440e8019000000104103000c1d0000b0260018030240480080312580280c14902c0e08100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 441616762 1250 441615512 441615563
    0x100e010f0c020a060311040b070812070e1503070507170a180e0412110709050402090606070f030521011e080325060e0105130b0a0b06120a06050a03 65
    0x1800d0900203401035503805a620704101c581202c06600d0302041e442c88038500c0310414062030780320080104c4041000002c02c1810405051480f25500c2c2042c2c1c84d50340c000c02110404a200d141c5a000340d01c80e00501c104131600d00c01182d004861307080180c07400481e540c0741c48074102c007290002d858804c00314004040c0d541c80001d280303210008403040c4400318200781041c124410060002400d0328202001680018002c54102144071068825525419507501003a00074090440e400c0f449841c83c200000d4031460f050080e00c43c0244c009002c01c00d1414243d4090381c8941c4040d407444004031f1032000246000c9804010035000c1c1c050941021559520306128a1880f031040e0402c0301c540d00207010800d10340080300506441e07024100041401080142005001000c140d541400154242010000e540120803004094144603481c0c3d552103a40d0010081c0880c5c185402e2150312601c00c018103400c1d41c0381d12258681200010380001042a81da50001d040c3c513a4581c011198030402000000110345604203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 441618012 1250 441616762 441616787
    0x4290a15021903021608010e070509071e0306050a090f060b07260904020c011d19020f04020c030313030219230703060e0c0f12060105010c0f02100e01 66
    0xa41540380a0300800203529044400707a40c032150900c14440d04103040c400c1141600d80013001307901c8414161605c0109011304444061308645100701341001400b03041c2235010511507000ca5a0321141d481c21004101d00010a1003011030405440304400302d11551034024200042540c4c001c00a071400124502c07500b5a000c0b903000c01d51800b81070000701c2c04140d4410b150f1600e02800700840024079403a8541c441c00c7c0c02044d09180d0014800300b800242114150f06c072180c00800e80c400c6809228445000c0780e40c407820940c0444541d2000781c0140014282840141d080e004010000341c1045452140d00d840d541044800510002d1040030402c10f00d90107012980d4608121a0b11588102c016200c004a04201116841c10301a01042e02c4401070030900c401d801459000750140a540780103c0c10f10354910f60002d2061040050074412801460100111aa201c803560050810fa030b00c0c001c01505e940b90700203001e4170307100d200403012001a44d9141c0951580d030000d489400a82003c00d00042842007100f4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 441619262 1250 441618012 441618029
    0x13200c0712020603010e180105070804140601050a1a040902190801060314060108040f05100b0a05060c100e0f01020d061a070c031b05090c09090709120f0204290a 71
    0x800711000b40c1c031180c003100d05441d03840e100e150b41c0d500d844103074203d071060b042c1d4107042ca5441c003000d0190131640612854040c0d4090f07100b158255402d01c40d0b0544445c020f01c10103902c01c0c20060200701000e5024030070038848500d4100c1c1401c095440600c50281da1190600c411900200464140030940001440340542401d20f8208118103580343e25075284403029007843d0611548100040820407403620006200c2d13880f90a0f10180003031744a542c070180c0300340032200d80702d01040f04012906003013040648012044803802060341c00300d1950038000820f410980103000307008902c240c014488003400180440440c0c04400141c5a10341020204000c0d000c1c280d0300e180c060200001c20201e10904005010b494000031600c400e115a96041800c02480c0e5104c01d40000342e880410040d0300000000d0f0103940000e98a0b04072590328808101e43c171481601910b44503124a440443c0801e40150207414480e00c003500008807030b40165030404400c210f00f00200d228224040f54070f021802c000d5a510300a10350b24 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 441620512 1250 441619262 441619289
    0x111030f0c0111031302061309090b071d0a03060b03031e19030e100c110d03020405090f0103030206040f15050c091008070518180c12010807030b01030213200c07 71
    0x245c2c3e0700d40c9052600c1c4801381c03050701e002c00d40300510410901881c008084040d000c01c9961503c0c6400c0700d108400710ba000008c00c0c0014007146203200ea002050700c030400002c01d449a11030440c4c2c0d80314000c10f00c28100d940c0501c000c0c0320310151050404c180b4030a00c540c80b012107445003400406040c03c90880707180c440030035080420001c44100d001800ca62481ea69541c0403d4000b00c103081100c1c90200c10100c20094440d40c0000d0541e184c0590080041da130069680c40c03290783e14007120b04031100c0284002001a400640000c011440c2181082c0e401031244c0030700040715000c2142d000a40e402601d00d001001000640151035180031000426031001c207050084462400c010040e000e030260b8038a031490741d8041015960955110b02c40c0c03601c6001007040b25000c9003041aa080b42e150010b448000c03c00c0e41210021401550000e644806c0303d50220101c1e115a0940c0d00b800b12000849805004240c1c46440c18090240c1564420704549002c000c4242c50b0b900c55640a85802c1c4140d00000e01109003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 441621762 1250 441620512 441620521
    0x4030c06090b0f0a11010612060f060807030b070c0b2d091c020a08030a2004030c050d05030d0504030e01020706090f0603230403030f0b0f0907030b0111030f0c011103 73
    0xb601514044420003a030395031105400c1c001651006030844e012080b55207085008038a000204460201090040e0b00400c216004039419800b203440c180207400b007a50100c0c1c401c20000c0e1080c140c00c0da210385540340c03200000100e0740d00e40b04041002c2d00c1800c0503052a501300060610782c1e42403c0820b21414510b801c4608101d6081c9440d81c2c0421141d5681881040e0700103941c41c000c000503020700d40d1014003541e59281050f1038000030004c0140e18040f01169510300302440ba981e4041e80c0a0b01d401c00a10b200c0b06107402d04001412181143c115101d000622440c4c030030340b03002d100b25440b8900035125080d42d050440d000908000442d08240140119480c09000d04a9000304c160f00355861810006183d000c03200841e074018510102c1d0b4003400720f40c9003c1204255254101841203490351006024240a043c20010f60781c0c3c0002d652604100d1800000e00703018070039003040c01140740c1070410b40d48080fa17000e407481c2140d001c4600d820140000127844c040104c4240305034400d44c0c0c419070aa5045042 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 441623012 1250 441621762 441621779
    0x3050a020325020c060315032e021b1603052a130920040b181902090607050105040b06180a1a100f0207050a05010e15160804030c0609 59
    0x201030607904100c040721844039100ca402000900d104590085ca1030340c83e8900201134042c06100741000c207000303010b041070054820300c10f81402c20803c209410006c0365021101c01800003900001c3c80c1007018a129401021061014403400c5018410400400b140381c1c294200149450784450070100389800f15402e41d024400b140900b9865880101d0340c43d044914070799001c40182c0402d14003c0e04400b41c0807042030300c0140d120034250543c00b050b40e003070005c01214810414205611030307150700e01542ca900010b00c0603020345010702144110703c20042c02c0440e440c010074640d0b000b08070101c0d4941c1d500c00a003c18482d00742411030303012800b228041125801c2132843c001345080a00b01d40a45600c03951880360f00455031aa580b410300d0098100601003581a0008050030028403101c000f5004000011889040000d201c100f5514180c4849042042501c1030001140d0424000100380350140001030090391a5910303010b07040e004240041d147c03811420900060001c40e4040414424101010401ea24 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 441624262 1250 441623012 441623041
    0x9020c2a0105030a0b041b0212031905041b08030a0305090a020303040324230a0b0306010b1e13080d17070509030a02030a0c080c0103020906040e040c030b04050d03050a0203 76
    0x1030080c80c2c0203440752a00c0e11800040c10b14605c20701e0f442400e01001040c8041407001c28840c04403594200c410300709a00100d00e0f164403080d2128a10041d20b4010b4100c40546608140c1d0442c1c490500035811070402c400c1603800010300d40260320b06d9040060b0001c480c90381401000d4011111001404c80e034186980000d0b034a118070b1000600910707000800e175101c03442c440f10003108200000d0301400300b1416807031030b2060480c00620800c42c86070010040740d40c07602d15208400c0c19100c00740c02084241d00b807030078862050b0004058007240c0510504191070041c0c460002c2c0503425034650190040e03e04108406040c4140c24520008000d90080800015080349011642280313590808907a101008e6000c2801c00d01c4a9602940501c9058155020801440012011583c82e202561400040314004506901c140c138200c0342d110310140014030911180301c00c9150494881c0c10030407134a039581d540750700d9004011141500c05410641c5880083c60b0180581d9501c440b03211003c51030340c50032203035407286017 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 441625512 1250 441624262 441624343
    0x1002040b1e12090a031101090c0303120608031306030c020d0815120f0a0c1406030402040f0624020c101e09171b09091e030904020409020c 61
    0x1c1458040a1040e044103044909002e200c052940d41440c103031062aa071070304021403c60000f0304610740980040c406204410946600c0b001440e041c40c1b4689027124619008123101c40c41903a10700c00024144001c0008004648841c1c52040a840c070300301000d4121039070340c0640815908020500c500c2cbd10f90014180f6440444c525a810800c000c002c04180c00302c41080d040d4040340f01e0042d240490340c500180c1a001070f0f11460046c40072a4403255503111340071002c00315940180c014408540185025000721500960030705002508581c0d803243d84030b4000300e050011042641c200c403c01d900590510001421420543c4c0302000151141c1c8002c144030b0003800d0800480390b0041c0345225403442620b000004203016040ba100c000ea081d0400e0f0346640c620b210391038056640c4401000f00e407c05e0702041c1d10540900c3c000d070503030216016620925140011043d080c40c00200107240301c035500da1001d0006403210200050319002000c2034036180c402c514041e04001e841c102043c81903049014030801c0f40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 441626762 1250 441625512 441625537
    0x17030313050313031b14030723041b080705090609060703140318010e011a0909010b06030711160b0a030207060204090f05040c12050601050d02030c090f091002040b 72
    0x8803182005070950044030814000742e46240c1000061007142c1c403401c81201003012071000003507a02c3c000720803d0481040001d401d50007245040103a074806010402240c000c104074507103c86551000182101c00008000031158840040714200c958000481c55220119042003071504012000203483ca004520500c1e114030000a0044100762040d0020811400c03095050703600c83c10440c600000088602c0000740c0c00350700e0010402c0798400c050245070340c0030380c240c0660301034019401c1c2440358006006004d40344075903d03401d10769003e4407400d0045d441583c095569040800780954254185018490700f000d12102800050020109000803226410820b060040e0760340d11501d02031000c3e005990022101d145040681c02175181541c01181c03140f8410040c0b21207054072905c1c18070b9000300c0060701078801e5001c50014000c03400d10240305c12000d800101103c000707440507000127100c402c0850b03002036108100c50501c10010300c20018909141b48a02e8103506190a15009039014003a130360401c7c0f103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 441628012 1250 441626762 441626791
    0xf0a0b01030f03020f01110408010b030309130e1e01050402010806010f14031008011503050628090f0206160201260a24081b2b060b0a03050c030601170303 68
    0x10075008000c0c00460307000d281c0087c04882c035030303070a465002c3e000380c81242955428020700b43e6107460044202d60101e4401052502099803412205d001021030b4800f06040380300b02403600e4040400356613070201c801030010000c103442c502803000503c0c5082c041d0650b8103205842400c2d500741500419003000c01c000074481d4980b03e585240f40c183c02c42c0b00316030001101d540791070300800e0100e680c01c0440080d6400b032400c4a94507121070aa40c4003400700c1c95424000b84404161082000340d00303400100c2240e0003101c00455104580e0009030f000d901200d924003805080488000840d60018411241080041000303050b0884030010350001180003059070110558070303140321001c51248003804003c1d010321015105241c0e201c01c10582d4822000044440c007034440860f510080c81c0058000c034003081e2544100c18009183d4020201d141c10035101210300c591640c4101100303841d0074078008003c5001d00c00a05000f5524402c2c18140041a0071003e030219500190f1a0311210000450b6000411042c4010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 441629262 1250 441628012 441628043
    0x90b0402070506192304050f0d020714030a0204050c030a0b0105030606120a0e0d020a1502030112030e0103290109051c0b0705090d0b090105151005091201060b0304050f0a0b0103 78
    0x2000f840207890324205400501003017030b00b149082641610961054041f542032940200b0255901d1429040701801a403007048203010b0041b11109080d41e8000c0601240c2d821041c6600280541744e04440001c16404040200070380020b860040d40e411070420300700340d450750a102011594a01c1260b40341c401c0c9100c4000850a0044164000c00d8a000b0721000d6807480321326071000a40b5404007042c161031a845003c0c000c04024185d108903030484114804440c82c1a10603942038a07a0702c51360183c0d034149aa141c0c2c1c3c03a1000c4ca0b0031020483c244901406543d40340c82d00030005003000c201908024024491031898050b80081c0802d40d404054020903a10403c0d40e4000c0c04681a10507100c00c25000b02c0445d018508100a1070400c1c2d004009242c00cd10283c1d640300c0b00ea548444580d0b881e241e0014070032803a0013400380038200500c080c2502400c0079135038045800350542581c000c0c1d4026011104004104000d102e018400d4095515024020b0318030718125072100040d419041c040900100e00c6420002d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 441630512 1250 441629262 441629311
    0xe07140f041a0a170307030f05090901060306080d030902060304020f0d050f0d0e090708040803060a090e061f15120e0f1c03020703021218120106090b0402070506 71
    0x140d4440300010000d110003405000c0310420b040c1e0b02e0768854014103040700f02258100b80c00800c0391030020140021402c2c02030f6030b00e003190010081d21446c014400108031006098450444550117090305440103e810303898411054504000b016001041501e00308052005980340000c0325041342d0101c3d140800700181c5400540d403440007910051091107541c0707609200b040b0103c1c060903081002e8a03201200d070881c0007409141c40007119000001800140040d00081ca4a8007644d0841c001428890710f0f142c40307400040843d0070b844021041ca500030b4080001e9034074410040b01e0340841d81070030105101d1800401d4214428481d4503c0140080d009802203582079540c84014049000400c0780d10941c0c0c0c000455031165048003503201d103522050010100075000e40215490181e06074001c080e0189020702c1074107250803c0030b00d1480c01c4101c13203520310325035035500c54400c0ca4100c80000285062401002e0400c40d0742201d400d81c0a5801400080d002c20000f0400d0382c0d0001c90b0229400d510079030414030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 441631762 1250 441630512 441630529
    0x20301060b0a090e16080a0c260a05090a1509021302070f0629010305250503070e0103090f020103090f1712060303310b03070e10030e0714 61
    0x12440d14008902d400700c440d4051100d40854241c100c25041d01d8980740294075030104400110700104d040380d80400ca5009241e07002e0b000b000d4032881e01010703440400c1410005042200044041d039080003060000800317507446902c3c1c102120500801010000f60385440b4201101107040784910750701d030074200654880d0070761861a95440744046640e0942450003e44485480c00144c40541c90034913104158680c44a02d10320340604614004c10085503100110082c08004003100c4078036905900801100d640d5400d8420003075104e0710784684a24013094003d06030200c00b584e40741058140154040405e90905c003402c1015020302e0007080b04030090401559a5182c1000100039a00c06036900b54130400d00c2c0090400380c0a9807945890a88401c420141e482c006e468401d1807031241d9502d11044505211400320700340c1d082009001100d580c0c1c52800b1150381007114106c0104151041240b500e141148459048901500b02040b0810410806950381c000c1c901600e1b84003a030303140c0d03200466501c4246 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 441633012 1250 441631762 441631769
    0x1506130b030a061706060105030109021305030f06160507030c03030f1d03030a0605041a0f030a05010204080d17100e060a050a0311090c0304050d0302033114010b06041202030106 78
    0x3015540b81080c11440c00101501c1c410800721800800b82c0040c80c4601081c15402042c0503503a03941164280710741c550096022420030009180b104030005840c0d01e0a0190842c446030004c045e0959203811700e022840c00c0c01c50081ba10401c242040034a00082e0012454614aa01880d0000314900c800702c00700b008140803a40c150f840d203445240000012400001144524038402043c48090340c0c4d4000d20003a50b441c10030401241025842c420614188a0440c6400c05002070032214020415140c0c142268026044248160403801200010340e8000c9241d4640883e2145106403c0c03030310483c00640c0c0c3d0790b14051101070491840c0420703210342c0e84049050250900809a450040c0c1c3c9107001c0100d9028801d2660081142c0000a0444850402581d100da03800001500c43d0034110b030f00840003944020302d4249201e00314202c0b034054050764007801d004400b00642d0b20094500d10300b003d0110448425492010b07a040000e0340c0031a4482c2ca065074100c64103105540c00580140c800207000d4a9030381c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 441634262 1250 441633012 441633029
    0x303040b1305160609050d150b0105070c0e090c01111908040510050405030d0908030f0306010c06020703020a02030f060105030c090604020c0f060403170103020108010612060e0108030a17150613 85
    0x4600719582c104203c1000b25000c9480d030b90081980c940c00c1c0300c01c2c3d900101000e040301a01090300e108070141a0000440c4000503d802d61600c1c1c4690b88100100b2040d0300301c00d5229181d40200001c0b41d000300284554000f0034200b00e0903200400c2801317a59190140130800344040c03194a0348040140b10350945000d0880100310308040b40e00040001d189400620480d4031a01c55140c031119401d003d242c0440c251344048024501c0e08120b891307000d1181c1c0c4043e149504010b0400510008110709102521351903210b40e016001c2c1e00202e004162600040354201c4203250000401009a039500049140644600750340341841a0390341c1e0b000400038080c1e1910b5081c41d000b40e4110300c44c1c03158007041d40c910441c425150303600c5100950040e080c481909000c003e000c40c1101005000756402044d605071500049000410802d485d01054114800c017a40700c0c60240d44040740000f241c0e074021001c070008410354071b01c0020602d012180b024054040b540b00078080d5070005081c03c041801d030181c0c5000f4202c0d15 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 441635512 1250 441634262 441634273
    0x2090d080702011707030209150406200322061d0a051002010f050703090c0b0f0a080406021b0102040f051504030308091005190509010b01090621060b03060f060a020303040b1305 78
    0x185002c1c0203548822307111841000700c819000240900c0740d054070180c2d01c1c241e07100340a801504a0514008400c2ca901381d0302880300b07129109010b080c2d13004545441c1280a0071403201e030b00e13145015102d80c0042060b02c2c40002c02c1d0003040410b072038005080e81144c0c002c492510300c06a03100304c180c0c0100210710f03010321014103180801040b00d800d80c08c04100d051185584103d029519241180345009400c951306202c80304020404070180b03e4480140c01c5800349800529100042070301c511100d80b2031060020694002c1010001c0040300b1100d000240801c1d03e44090100314100340c441e00f4803c80c000182440856008100740e40790401580700fa20100074030400c4a414004005880c1c00c660318181281c0a042c034001801d5054180124034800304107031102d4158a062860076102c7c1e18480d0300000610503003000c10a0103901c0d45c0120001041d90350030b9155241803890500ca504181c411696025180c2001a4158164000304480d8043d400510081c4103458640b44d10890341810348029104e8070a5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 441636762 1250 441635512 441635521
    0xf0305131a0103020a05180718080f06060108090106030308011a07150f0b011d101211180a050616021503010924150c08090307080706021002090d0807020117 69
    0x32600710078140c9000300c17a5000b125507904200680110b0003419084040307903480100320340c0e83c0502100001c05a40d002550366058851841074544201401c400007a0360040341070104558108004c0e80c0c010242c10003d102d89415a200940341d04810b1050f114040c041c3d8201052005410003550241a40017882c1040f08205405040180555400401d030381450040040d180e5030080c01007242010705c585201740c0c0e42040c03c040000040301d075940207052141d41008000720444920880c45881074403840582c43d212030402c01b0100c08e0401da00c03e4060380c03076408103020640d01c0d4000d84d011100414241d00c483ea0607840803031407022505844d5203580c200440080b81206071a00001d0344581c0307880c460b1700044600c0131f8034002c101e0680308005176218240d00118100b031040e140124294001c10a181c0382c001c010000c070345820207592002141d90007609081c001e60754140204503149500c04019410900b4007000039100d40c1000e14010072540001a2a04c210b90094a01c111455038140d48503805240 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 441638012 1250 441636762 441636803
    0xd020a020a11010c0f060b041104080a0507050d0809091f09091e02100e0f0d0b190203010b09010e0d0f0305030a06062313030506010b0a090806070f030513 68
    0x200348100320b400c15042d103110b20403940b10322140c540d415005000100c42d054035880307601c01800345180b8103404c00d07115881c4d41c1e101540d04000380020070080b00240894000c50a200f0300f040300c0381d00201c2c4200301c0c520f0b5207404501000309a44415008456100e62500c400c0298444015881072a4416140c03540c030010f22206160b00141c0b500e40030303d05031890000c0e048c01c0c1118540700110000c0d800588100d41d0b100f4244110681c203400a0702038000618a88541c000801d9442040c10440e10103444004214160b03041c000c0072100c101181e8415411941400c8031400d55005032991766040008951030a08282d44452000440c190002880300341078a40d4280180154801c8404890700e50400000240c91885180e4a8410340c000b04240040c060f415074848070b95920041406101c44400503001c400f0130424814503000b03055140c0c0603030b40c4001d6070f400900725145a600c0038426400c08410031240ca508802c0401c58000185000123060f900c056000305201a14a0041e24003d0304007094060383d030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 441639262 1250 441638012 441638023
    0x6030e19060b040b01050909011a090414040203010b10141c020307030501031218050909010b1005070204050609070f0c0819020313080a0f06052d040201030c020c060703050c030d020a02 81
    0x2c0d0255801e01c1340e003580400544241c8600c090041d049940c040042102c0c0c0c3d41d04642407000340e990360740180313850102c40024055582c074540d0610490007442c140300845c076091288009060302a59265a0007000000c0076001020004070120511000140b804418081c550350b00d01c51010440115220f083c0715000400402c02404129080300d4103e606800741030050706a4440d8000e09180c50454905100620540c11405440030300159200c61413070701187d40344000d02c0c10070201603a840ea10b079041c5004000990b10003504150050600e18148101258801c03007001c081c2103241000c010b0300c0c2040c0b428070454850510702480e00c2221812002155501000401108071404040d10401c0c0d200c84406e9220714101d80014211400c060400c1d001a5150304059031014141c0072120b40e0040c507108002000700c0d6500142d10700107068040104541e0036124408100d0b41620041a080340b8034400b0034440c3c402d02c50050244580403c1e8180300c56000c2048a001028038031040d526152528000380d542d2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 441640512 1250 441639262 441639281
    0x60d020412112b0c030203030703050a030f1a0424260f03030103031b0210030603051516030f110c01020406080702010519091b03080d0e0606030706030e1906 69
    0x20604a00090520b400e1188840d28452903092249582886600d2940c0c2c16030090100c4d01d8002100002015940070f002510b1000c1c02501ca055403041d050070018101ca46040395032594a24111030140814621140f40d07030b513408160380020f18600900d0480700e036045c440000a842c10490702e070104d06403d00c0030081080301a00790354098500092184691961003017103110f41558014070040001c01d1265000c055030b041518000170103940580c0108600003541d000140110b41c940c0d00400411504100d050383c0782cae05015560a01c1d06254510030314030b0f10f044050004040d110340380174040d05804e82c440c041c1e555140005235503614400c940c03039010707400520645000c50070080016044078018090706100e203e500002d0485002c0000c03403200140381148084d00c1e042d180c500107030a10040c918141000e140900078107a01d13803a01c20301c10300981e00382c0600c008150b08000c003800829180061100305880380c80c10049482c520052002d40b5040a85050310480c0e07030400036000a0000a81c80310a05 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 441641762 1250 441640512 441640523
    0x1209190609080c010c0f110a0b0d0501050a05100c08030c0c011a09060904050705090a060e04060e0c0105041d04170d0c02011112040318050d03021005060d08030c09060d020412 77
    0x84100301d80c0159059100201c5c040c00050310f0385e6034040000c121a41440c071841c1c00034100c8040c55118085450a500641c00220650b551800188450701d01015440d000f84021101c42c90242c610300801090b0110b0b005004013251004404551050070b1302043d2071410110704001c1201a10101019141400c210201401801c0081c04170b080d600b09000040e1150b40c1260007011040c0c03806c03042c08040d000051030b40bd0481c1da103100215a4110010b4143d0241c2d00818000c10216189105681018100281c050601004101c20045c4072105000403041c420f81c03c82a030529669824903001d44100c280038078624400000d001d40c0500703603d074804c099540c2c007a4000c00003a00d41d090000010300c10b00c07000c01c0c1c5080313110b8000b400203840b0300c000b103140c01d98400d002c2030466540c00100e1b881e00c010b02d00840151f0051002440c418003c2e116107030303100000310b406440200403912003610b903100c09020703000d1a4000003058096511840101e17180045822003c550700e83c1c0d184450b402c0322211000c00ca03407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 441643012 1250 441641762 441641773
    0xa06020706200403080309070e090c1005030907090f020c0303010f080c0901030201050d050711030301080114150f100509090f01090b1f0e010c06110306010818120919060908 76
    0x1100780300b0406a01e084030305241e41501e441e00355140c40b4039940000340100194420640e0100350100b6580503103000d4111800140421020001001186000381e600001004014020090344490000700c40040b22803440e00000c244003000840c00181c0700e0301201003858800040001030500013028100200c89003201690030300b80c5001d0810240310003c0c400640050000d1200c1607100406030703c00d43d00302005043c8020b81001003244c042c05c54009901c2249643d40d541c0c40c81a00007401d05200b6400180c0829030405003200b0400101c0f6041803d60aa011740014440000018000c030221990081c00070041d141914103000110595142405248103450414003107950a040c4030068103821600010040c4800c00003503402c032502c2d034001c66541d04204903a030283c0d020401c00d00c5803010b448042007126980745070400014000900140000099081c003030440003c404000c10500007284a001919030380d0b003424400599031648403801c0704030742132421000103400e1381c00164500403201c5101c01d039078 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 441644262 1250 441643012 441643031
    0x14280624020307030804110402090d030518040b18330f091302040c090e0c0301030b13030206010902090f040c0807030c030603020609040906020c0a0f03021e031602010905030a06020706 81
    0x1d0b101d00078014001c0c0441d00441c0801d0004080c58104610114060001410121000c1c00107240004d0154103402144002a40b03084030208a01d820840020550342441080c0c180000304180c0a900c00000740222040d2010640e454511411806081c48113440e05644031400140c25900c0383c4150500c9101e01c44059016400c1d0a1150313610b44564403650b0820064841d039024070020300360103603021041018004c2c001c078805000c07880d000d008280d4041031903100e606514002c2184180500411103207090b2000c500002940003032004e040d10013a0300056103c44100c8046650400301c0e0040076803203800c1007000c14405e035100b11898483c1c001982c00340600f101100d403d400f140c01c00d02001e07402400402450005041580000960368400d84005161186004106042905501d81114510034104c5100141a41000904c00794000840d24044241c2a2500c10b6130742d1103902150040341064040756815603021741208001040043c06990301903441f85801d01c000c0d40400412a4200d19000c40e01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 441645512 1250 441644262 441644267
    0x31806030606020a060e1903030609050f0f0c0706110f0703020d0e0312130f170d0201050f0103061d03030c0904060f03030206040323040b0d050a14280624 68
    0x9001c0b200241c002d030080040030b032a9400a08400030389564035215129070075501484284003011440e0080d540060780c282840e04a400b95031010b0035024954810303c00f440024182c2c000b0598000c114091616130b41e1010b494450042c0410440064000c900482c003030f1308402c51500200b82c0316201c1c0e0f0960380480c0700c4000c1611080210785115806900640c2c00c03500315401100100200d2104480280c1c41035650080029101d0464003c40300060051505d034a0b10401000a06000c4860780024030161821a202407505501480054055038541d055125080300d0f840b010115550b64072300741c99681c50060381c0714500798070068050b40902d1a040001411584114041054130380c9070307007d482e040d221920119090011100c3d414016200b000040e2654080c010040000304212208030303486080510100c411904020300e4100454280034940150035000800154441100507001d0744086110000d503605881204091a00301c0c078201c00030840010703481000e02d6410b542d04d007440c1480301c0705004 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 441646762 1250 441645512 441645521
    0x51e0d09082e020a02010209030609011112040f0515010501170903031b190806011223070311030a142a070807060906060e1e0417130303180603 63
    0x40c48019044641007250300c034078040d4100142580d41001060b15a42212020101ea10240c21440942c0d0f000400e55107506050008583c01201c0da802081001e0b05640150010712658500f40100c1a0002c0040d04011050401c1404150040e0071960102c02c1c01c0d20300b00e1250380138000e017400b28410850511481d810030548621410070030b0301850541e01c5801c5022107214080d01c4041d46840284103891740100d00c0300c00d40c03400d006180d80c0c074106414000005880400003004021915041000900908441003440080da04c031000104c0115554000228002c0c600200240380c0b0f181d001040c0103c40190b03030081c1c80480395041034840c40d510b0b1003618800c0c03143c0301c140700c00798088141d10b24100c401c4058064941c1a0113032103120b00c1c0482e140e44542c00c480d14032100721121569601c0074000d2100e40f0140b507074010151030141c0100030f1040062590004005e0005180408100041581c40700b00b4051368a0340903051071940c1c900f070316440c0103040f070900c0003c20800c400700d0a46c000b0b0414407a018 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 441648012 1250 441646762 441646769
    0x605030f030906180d0203060a1a0f0f0d02042003060a050d120c0807242007150906020f041a12071107030b190605040b0f0d0c03051e0d09 61
    0x3e054640500d10b40e01c580400e08100032954003550200204002d62014409180304641c01c010028002145000044500c21042c0303905001300d0b20445030303841036116640d9103225290203e9110307019003058800a8044c081401000781c2c40040c4c900a0805914803401031400b490007160b40b00721346511903040c806a031041d00c002900034890500c4524803980546e20302580d0a000342c021610b443c02c07544a034900860b007a403404c0c1040b0410b0841e01f0a1a490388503429903105559070010720f1302e08448a070035081c016500c0260203460a0b0410140f903224540c001c040b1075034000c801f951241d01c1003402c0c10082c2c110303128a0800c0d880d6603990303981901047e41118042d0054440b0011540c8800d041103524800e8218440091300c0748100100109031400e44031840b84542c0c3c01c0c5031550700340140400313054591a80c07099000c0d60411419801c1c0d59a0707805000300401080d9a60b80480c0203504005609882c192310140030341c05186481c4214104400c043c88405c04844116a940c403210301d0200c61b082c0440c032 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 441649262 1250 441648012 441648019
    0x718020708090607050c0d0803090f06040c06031a191518030308091509061b0f0901050f070f0c050108090d09090c0c0501110408010c09080604020103090606090f0605030f0309 77
    0x4940003441c00784060721020b030060040310041e0020a01082c104440703240f092314010000b00c208110301508000e942501002440a8031250074182d40f10700c4040524026141416201c180003810520900c24038890030400501031000c5d0b00c022852500322440c0342c0100041c08520007540c0c004140592602c000a51380c080b0145804c82c40d54504880d040000b0304500c41500840302822002400010018003c0607120041c140604140503000503200440007816002c40e41030240b6921a4410400e0b6a0509028281144c0d074070088011a000c40c031880c032000b010702c0314101d844028402040e42103001d0b14400e0b00c0701405ca0311603070621680c41d012000d01c580094a007182c24010480e01e500070700c07890741c0765040c03c0c1b4019425941e800e0960700100d02581d1924000302d41008022400d01403006031000078105030060904000d011038031404001c1c0042c0c181500e030511130081025942c0220000d0094010800120380002c110401416442c456184a80f0801404180c1104040102c658644004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 441650512 1250 441649262 441649267
    0x40e06030a200609060d1a01020f0c090705090d0c060201051b270a0e0402100305160f090308030112120810030f0c0b1b011b0906200f0718020708 64
    0x80d0100c40b81d03940b981d11034a030085400c0c0700000258441c4005045000e4101401280b0000c07144c151040d4041c1c3c8042c0c6a0455000f10700515074502c000c07503c00b100c1901550f04580e155036201051365207100c0d844032583c01401c050505e606011810504000b903031482c0d0f000303001c41c1e1144c1c003440e500503440307039001514104200150703a0364640d682e002c004d001002d00105c10b000701142000440600381c9070320080301ca4045c00100400c40c0341c1076003099071440d85c50808022600f40030130322100c010100c000002c248082104101c070654011150f0f00019a808290031741c1d00d44c4c44106000b0040c89140c0101d4140d48519240704080780640140d503c1100c201402c04503440c916259031896510504007a595550030341004100b03407008000400450090010b180c6401404485445c0bc5400012100240721a80c0b10080d03480c0f980201e00300102c0d206443c100702a0042001c00080182c01c40c4040310341c0740300324400001c050901241c0101240d4020203128160200880c880060788950310000f084420b04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 441651762 1250 441650512 441650543
    0x5010b090705041e180f11070b0408160b15011707050d0b0a050301150501090801110406030903030e010603050609070b090907030c110102030c04210f060e0f070902040e06030a 77
    0x40c030a50503200001018040180303035100a00c0c1703152040c40c3c405000241d100c01c48080c15860a0003145100c00325101c00303500d443c07016220a4101d030340107800142080b900240c0e40301c0000600c10440b085c290401180482c600b09442c843c404c070348003c000940031030880f1780d0030100442717030384402c2d80b02d0b01e4540c5a81d450069107844110080c50b840520540c882034004022451351403d02c6044440142640510656401c1c02e001510305100c9030700601d581c1c4c1c142080310441c071560030107407000c41e200307030030042003032010703440c0c00e901400000c40c41c620150b103084400402c2c0100051103e0080e290801594441c0e5211425400da038441c0282882d0484034543c0405d640f5846036001c01a404d49038907042a20011030350105080e0790065600e0a848040814180140141920381405040140c040800c02400543d50f410000140800203003020b5075619202009000a000c40f400211550060303801a41d16440464000d420900036420625409000030702d541c100042c1d844030305900540f008242414 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 441653012 1250 441651762 441651779
    0x5070f0c060b06072102070b040f0b0d110703031407090303021b01090e0c0403031b0b18030f0f13062d1218050c0103061a07080c0d02060405010b09070504 68
    0x425502c03441e0008020003025002c51843e0b8510b0703040e000b1901c000f00c40d014040a0003850000b10350441102d00310104010820307224041c40d20804c03164485a1540c68603c508018002888500c08501858200190f240201a0b00d039209810054031356070701c40c0b900e48440c0000c0f2006841d5010041c0075034003600803410180305681030000b10000500d45041c6541c2c450306030401d1240242c0b0b250b648940041018420903800a40c0c100460080302820807003a000390b00e6240070318401034030060b40e8065442013410346480c203000700e0310944d1041004544d206644414008568899401c142000c00444004601c03984900c58144c10101e5500801110041c82460b1001480c140355100c010310500040500c04080580100d00c01d104101341c0c51907296200d27092850910518810440c10103203040d50600210b480241d4100900681d0042181ca0f4141403400c00d042c1d00c00d100d19007001d4806c100003070300c409078001941440f592140000b441001c2002c024003030092405d4a42101007607090009012003278 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 441654262 1250 441653012 441653021
    0xa0b010e160c0609020612071103030c120402010e0909100e2b0306150c06200301060e0a0b0301030f210e010e0301090f120314042102030f0301090207030305070f0c06 73
    0x2409544002118005540019440c0c7e0010100d0136400015004201880760080c01e0706160f1908400503500e9860036078010070300ca100d001070100000031031034081000c0d039200300090740c210800a00a011582008090741d07980d503440380e20b0203245d2400e0110150b0000341c04209041100f417003448200c12403010000307802c8013003606420302c02050307a85c0000007102c4820004100300c40e00740d9101d00d142030850f814154180c4517800014008a46074810300d0310103500c010101c80c111703912880d0403544440221b00045000015502200b2070315000b000100c00c1c0150010ba00600f588140c4520b4116180808204249940044100003151900e801c10300300d5409800742407010180103000242c0d030400b941e10307080d11a001c100140c03031b0b940202c403050780c3c1c9d02c1c1c05200300d50100791120000c0d07000d4509170b510710349959010f00781c052280c015885840c3d03901d4006c10940716004030081e9113031f490b03603159160302c0002d4100d01d505a0000b82400b0200740401d000c0c0138801204c0b4103d688515551446485800c040e0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 441655512 1250 441654262 441654287
    0x5010e03060a181a010e0703090203060402010e03070e190c1409061305030f100f060b030105060703030b102a08161721070f1205061c050a0b010e16 65
    0x9403c0d103e8510300146840068100311030880d5000040741d41800b10100c0351000080c40c1c02c1c00d051403c000d100160785c0005129a12950918010150340f84035000f00b0700788801644070300105100c03a1300303020f09040c11480703489141c2d188820401c0302a0821104561500c800383d00b030543c0000c20450b404050038401c004140c10b500e003005e04030f52181d980000c24980200d518040107907420541c0500c24009140c01445010320780c408080c80180d0409c40c407484c8621041c0b09652062000203000740c201802500250a0302c3c00042034a0f02c14090700101400e401c02d038901d114065945554110180c4000e00340042d28190008a16410208012411550300180038401c0e80c101180c0703030303e60040004540c02012500f9040f41094000d2400d50740200750b50742c1c007a09500510060104c2c20801c42d03440b00882803400349107070010820352905800704e100d0201200071402c400c090301e8200c1040c00310000d0600c000d0b0b4851b0381c0d03c00c0544ea8584200d81010010b0b14144030440010070310f4032500d41304402601030b6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 441656762 1250 441655512 441655541
    0x70c05100f1e09120b040b0f010f050405180f071d0f160903080a180503010501080606010c1b0b0711040618020c0718060602100b030616110109110a05010e03060a 71
    0x6513102d05405001c8a10000200c031403088020410041110120621350441380001c0703002c54950401c400f0103220111406054001e1395107000007642c804a18036884441120801a90080c030000400c440e00c507030007805219540c59040301600c1038a0424207a29202d2a505480111140c0b07401804001c00b040c0741014100b00071400d180840820b54070001008460315075214041145800600c40c0c0070a103a0b6440684603134074080040150b03140200f0f0b516802802440c1000c1448004c1c82c1c00314030580b40000d00e060070781150380c010800001034030082041500425a202440c4007a1040105841880c0141c0d0000c40c512001504060320680240c052070703003440292403003140c07254280303001401a40040e8184540b9070800308100794040c4241141d030029130030180f2100344000042550742c100941070010041c1c9030142052118480e8141e06c042100c074000134840342d102402c2540b803ca0500000500c41c0c103203048001015070003666510101c1d0360180142c5210365500405000610825055002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 441658012 1250 441656762 441656777
    0xc030a020120010f0c110c090c0708040b040b07140a030903150f050a1a09040809130b0907111b0310150b0a0804030806010c150903020c0303070c05100f1e 68
    0x20b2014081c00b81e420700140c6004006411029130400400c80040d1071644030f5550403940c0c1410042c6c441020450380144d003c403801e070391417100f840d2401a41c8510b602c240212030000c10b020501070b01110040c403c00b40a80a1250248101c039942d40e12280d4180e0000c0100d011160100000742e50202004040b2207000000582d50207040b81c010305840c0122404221150384d00012500c6039040440d4114005c41500c0c0126140351590f501d41c40c2c0e104154002d0301c03d051030035441640104541041032002005001c85000d070034004000b50103030b1404254811107004584001034803c810f41c50b2940400300080092000c090140b100000510315a040c00400791300d150700c003103425004040200704080199a8584640c07a03d42001090418060b08260400c0000e00912020810b050b4410380c603800201d50025403100e0500c6d040e840c0c0034020103c20f41600011032500c0c1440410b2980d83c046400c207441e00e4902c0a01c0b480d046038a81902c55220000c1130240c800070000959824460041502034104080c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 441659262 1250 441658012 441658067
    0x9150306070807091703040302120d02070b28030902030c0609010e01052802030309190206070b150a18060503030c0303041e080403060c0e0a050603061c080a0c03110c030a0201 77
    0x2c08041c0a203c40d17074501d500001d0708100b1424800c110b1041140d043c0e000e00040e1b08400002916010180320306600e801c0046007001d20200c0c1100d008d00045001001290200407212024010300b2000b1820303840b80c09461040c03c080e0902400700c1d404481e05a44030580c10480c01c0064031a504009020042000c24403400860409120360041035000c8131f40003181c40345002941140b078481801003070318410240e0000b000060b261401a2030066500100c0d181e030540c0e400070805c43da00d054400c2540e0040403a503000030030807202c22403ca80007050f800b05109954072081456a2841b0b2595694019402000004c2c081140c04140100184d5030b0b01d1035100d068429155844290043d400a8426681d10700d6258034158000701100d600000640f09034034141c2c40d00b00061000c2c000103000034007038500c031095145182c18000494000c542e11040458580360b48520050180c82c1c99281100464516169807000841c00078400790000300c004c00418843d03c5070390044138201425800c004038000c1000350035 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 441660512 1250 441659262 441659279
    0x20a12051006140907030905030403080f36060304021819110301090501050d0c150504030f050a1a010e040809060d050a0902031014010e100b0309030301050915030607080709 76
    0x200010f03d403420b4441c000c4083c01d8104100c05101030150030a01d0302c0e080204000440101c02e58007165081054a0340f12060100500031512034800c04c081c011011001b00b00084d0b4101450b16203500203e05142c001201c2a801c0c004184001c0c1c43c0030f54806e000e00300c98110200b6191506a000f003000324001541110132034454213440c00c10015014140f400700040c00300064034072405005200440c1d00c02020007154944c0b1001407000d019000110700d00600c10103145004908440080d6401200c6440c0440e250502a031a080e590001310351050442c14210318000320101e0313081c10781e0480c044c6c15555454a0307984c02c410b41d00145101e50031941c24840d800c000c1c0c0061142901c00d1003441000706103901d042c0f04060404940811040f050703407801103a0f00c0c1c01d4400d80d20701415128541c2d038181041c0c484100d1007002c40ca071036101d038140c401c0010402c0075086021003e18100d8009841201040c1c0302d0107883e0a210384860421038140d4414800100395030300c11200c035030b040029070409100c010740300c1107007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 441661762 1250 441660512 441660521
    0x10212010303050403151406090a0b030f06040b01080a0201050d0b13290910140f041d060601050403150510030b100302010e30011e0f0b010309020a120510 68
    0x2603001c240081401c100b44600f0712580a20300c80d41c000100b06441e8903011f100c11f100000340030a809455950002840d01a6680c00004e40e02401400c4074a0610b020307420a40d203800c100e6003203c10b4aa0780c00001020f20001400e031b040141d0585845040a840884100080441c001200d502c8940b06102000001e0648903510803603404503400980c0103861900110b01c40701c1010402d000d2000e0f00104150103424007420425104c4400015203103909020004152000861141c0da01618000d42d20030950a04145012101c414038203440095642e140152000d000380d22014029480d98001c8011010407640016403040d42d06640020658503030b101d03c5000001282c221412001c0c0c02d00038001d41d038000c1c841d04000102220491100c1d00b48100b90304079220017101601040098031002041807100707410a54001002c0030003d14441e950b159820050182c08100b58041031419200c00550751103401410409500908105c1c48145800300c0c00c02c0211042c0d02c260741318040c0b24200d5140e40824080c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 441663012 1250 441661762 441661769
    0x1c11040c0c0b072309060706020d0e0715050f0c01150906090b0402040b0a0f020a05030c060105010f05030708060108180a0f03090509010f050405100302280f0e060d0501021201 77
    0x65074070007460680342ca600700050280c102424405440d4107040e0041000c141210000d04103202d482e1503080c5900070445a025941004040c1400840c0907408105523610011240c81d0707290444900558607100c1103030780038010040b007002600820005403228004002026440003400000036018505c0b40e0002c2001c040d43c020181c3d20351076038420031032034155021710040070304201c03011403602c0d14140041e02d00b481810b00100038825850070302511140240b00c2c42c1d86440e00081500d40d42c05100490039151842401a039010a110041d080340841c89407050300d10400d860303101c074002501c40c0d50054654110040c02e160000060118041c140d003000d002481c01c491007040c02803200001441c0241064075150405400b6819a50040004240300e4191034100d80081d02d0024a545540d00d612840b406250406904006410000109071201182c68002c01122940c82d400311901c503003016408000703e00c604107141000310085041440e01c09042d4201c03a2081c00014a003103040810003180c004d0990 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 441664262 1250 441663012 441663017
    0x50a060c02010b0f010c02090705120a0207060f050613090206090303040b2a1f0219020604022805060306040e12031b12010605090a180209120c1c11040c 67
    0x1018011034540900401140510031503488000d0811040002c200070106103000e4030900c241008908140d000318100c854200418403101070918100402c54069030040b03000b200d800740b9211411408070304034401e82e4058803006103542034064075800a500549818003042c3d07441181040114542c1c0c0e01000280001d00c101031403a80c98030110214059000760003032400c00c6038000c0c00901b02181c00e01045c1d48119140384a0380b02201a401c00d40341009001d15826034000c02e00e40e8422440d690740010300c503071055100b03c0742c031203800c1c031030314030000420b40d644d00b001c0303074000368803030309225524040c1d0155512150262001400005c45e0440c0c91a01003441c600146100c400000e200c0620f61907007145160031010b00070680f9058903583c2c07640d8200f205129803001c011010418100d29542c0c076403e08001c1c0344000007806904082c6590100035400380d188548a110401a41c050301580800c180080801c0141a40c5141001c601c42110603911f404084440e00681d412003484c90f074851148034102440d66 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 441665512 1250 441664262 441664271
    0x623030c0303030402031c02010f090b0603100621020402090405010e07110d02061b09040501090203011d090a030e03150424022704200c06060114070b04030903050a06 73
    0x14141410446004034060280d0010002c2101580300098000540c0c03281c586940c248500103c4120b00408116413a08000c50502c59502c061004001204d40141800c40c1911800d0980c44190005c40d1168816250610702c501c2800c00b12140c2c801440f40e03034600242000d494a00740b00001070483e032090f040300621100034801c2c0040c2d9580b04040624400e84140200300060b5a45030103075444000030501e12a12046010300da030742200c51000c4d500d25180c068000d1004d0350315011500040e40090082000c1c24907980483d50080d103012840310701462010001e8500c12030305882c01c03511400c954031080e4062050380750100c0442842c20f6090b205d0b03409040052012120011078138050001d806059810f50b00611003240800140b6068054007105100741a40380307070501021901800c07044800c000407801008100ba28410300c003000780400c4d03a40006840041d91480c0055805c03a80b0004102c000303510070300c40000001c000010141c2c10601038203010307085580c2e0369145842d00c0d002c1482150a903488 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 441666762 1250 441665512 441665579
    0xa14390c0306040305090415030227060f18220c0617040515090f0d031e060b180607080c010f0e01050601020a030503041e03021e0303040b0f070306 65
    0x40c46061903500003180942018242070710010003a00420351903520441e502c4100102202c02a05190010350f4090030254003100000b0901041040250f680c00e07005034030000080c1c0c603180001002107040001018000008a2140c149440041c024004903160218035a0703e2001d007480900303810340390300c80d150b1800304034140000180001064803103500401e010a050200090b40483d0300740c0c1c1102101048001c1d0f40d110000c042c03421038900103d00e050700414040c1d1440540c1604040ca4280d088441c000d071401e9052008002c8030024818103a0345401840002e041211211500922039002000c0390f060080903100c01d07060794404100b0708510ba40d5403102d118010700c58090305c0d0400c255807000f00018600000046d4944070188802003c00c0300c0080014200050034030040005900310000000c007038403d14000c1d544d0b02c80610700f52001009900c0e4032848140000c11244515440648030320103480b061a00b44114030090454414140c444074082204440040d525103500b81c4590388000d007607031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 441668012 1250 441666762 441666877
    0xa0b16060c0905090a0b0f120a0b0c07050c060a2a11090402030304060c03090806090a1a070e0609030c0d0803060a0909211e03051b0a14 60
    0x309191428070504210403c101c0da2041c148550000c080940803880807101c900003040317a02200c501951081d501c4066005410000520000091040b846114a40c5860405801e98011104024070541c02500341c05c0f01400c0000180280c42c0d1141006444207003aa00319441d05426080e6200c10110f40c1d000180c00d0010711300c6081040207040e204441181800e4001c02d440740304a0103200d041c8501d18620038205807143d038114006080e8401580d905052131280c564561180003000c0c1d54500b281c89115144410b882d85143c01206151a41c0b102510a0030600c8110340040d159103605004202030b1550a4580c0050714250900c81c215040c0e0b01e203850400c01c100c1301d031280c02855007240790424680024441952072460302c0104018403103403081880c1c003103d9424100312070001c0c5040c030040340120150940c1010340110b049040d180010b030100e00e01c1d0b800500500312088000340440340710502c075244a02c0186018007000e03040c3d514090940246440e1024040c3c2003041d820038803035a03605d0244 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 441669262 1250 441668012 441668021
    0x90506450a051305100203191407021606082d1008070614030a020c0a2a090b01050306010f05220305060f01061d040912080907060504230a0b1606 64
    0x81c10101c0c1d18425440384e00d07090ba684d240703001d104e000c5c02c0d03000001c107100021804200109030200401400800842c02c598122202e003900d546000d071040900407885480c641e1000300588a0a07034540d4a1607592104400c0451030b10b030001d4101500109410401d03c151110151146201542210555113005150f625204290b88800d0410016808041e06600f520040f26003000c06841c02585440004003010308105082e04010880f55460300ba00307844550049603810244007912004601698a200110545248465441c0012010400140d6541c01000301e1008036096103080c6043c400c0303840d21040807000e4000064405000b0b84010001c1020401145901144c80a020259540b4000010b45a85801d52054100341c407a4030003409141c65540c0404030f6150080c202d844c4526400d080501084810354a050041c0a46c034004122940650100e80031950711040707018007490a05d4060038600361901945030700248039500001d0901445c1c0160a031032020b8094100c010440e0315200301100c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 441670512 1250 441669262 441669271
    0x80a0c0506011502030406030b06090a0f1406090a05042301171006080319050c0d0503040b0a110a0509030a0206130f0608011a03040816050102040f090506450a05 71
    0x14050503c0c1e102459404015203045600f07908000c6400c0886000041c000c0c0945107041e900a542410001800a13070a08010200c510000044510103004000c0c0b0601c1d220304242d040c0c0000c1109400c0045d81040c2d071000101c80b0103641045c03040000c07202003900c06482030380941403001a0311039a41c101c00c5d00b4825041003104400041240510b41075005840c3d001340740e204051000141c4512410034002ca08441041a81c4e5040e20700c25200e8190241060b0800d0b24141c4061807139100080070340390301e44180700c9050300340c2c004981800d68043c012940360744900105505409007441e80c400584501c405019a03a01d00e00410201c28100f508070710b0900803550041c03040003030302c500400203000d40c00905a00300e65024103e40c1d581d03030340741007291061041554086000e5a1420303000f05000041d40500705a4011444200361242c1e100d0107036094840c180e17401030f070102d69900a01c002e0302000c03102000e16504003102590881c0e29a0548030310092035908071040442c2c0c1410031118038500d201712540f0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 441671762 1250 441670512 441670529
    0x307030f0c061b110f2104090f090c082e06030b0f0a050714040608040614041101110c010e0d02030c09090d020d1e030519020403030c0506061503190207080a0c050601 73
    0x10b9179120101d10364600d80d0107509090400048040820f0700750b0041290043c0c41d2850007884480008242d140003051540c500f40c85000c6a20340c0070908810125031003c00c0b405900c1c0e52a080b100e0b11042034099040c810210303011956aa20000c00643da140c8141d11814200c14924a5862b202c1400026204014240e074100300483c941c103401201c4120980d815285185040c4c0e5460380d031494550000c040e6200e10040540c6807008001c00c0058050210782b4400c001eaa481004c3d0820782c032031507a11030442c40014085080d46031010402e0034030b24907080c80140005c0880c5c068030340301e42c0410382855058518800d26004250500e0805404100508814800d071500000c40e102849040c151404d207d141601019100c401080b00f44d50742658201c88483c501e14110350300c84d88c0e8030707024000c3e41400d182140d46015680008000303107089200000030307046044103e0721b9a0b40341c402035144140c8845038000119802e00901d0b02290180b4040c1000c0741e040d454003158114181070091130094168441d540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 441673012 1250 441671762 441671773
    0x102071a040f0e10120519240b0d0f2a03110105120c0703030905061006080105060721021009111e0a1e0b030a1b030606020307030f0c061b11 62
    0x258070368104030343c04490440102e50042401c80c900301f428a4180c01288003651503e80b140c10a01200c05034000300ca03090801000d0340a02c0182104096070b410801183d44185610007440200b000c1c8401c00341400e1240390308240f88a001c0091020180c2c00d1a0071500600214100f48100101000039501200d000d09100382080c402017254003820310007c0c01c00c86100c2c0003040d80c030308040c007075007041502591040c01e40b00340385404800d10084c50301d13a00c43d00d00000c804500020300d074203280040f1b803002a0410118048180030001c04100306a0f406040d00440c440c0c01400d4012000601c10940064810003204c80d5aa064070100548030b00c003591b11815070b011a00b00c11f00140d40d0160031104039082c01c461241c50824500042d80b81c038603d54400010000004204010251680d0100c1d542d00c0b205001500f0844024004804440040c0101c402507403040010401203800340840000c42c800c14070704484620b1203940d0711400e40d62002250140c19844007001400160045007041b4400c100301c00900c03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 441674262 1250 441673012 441673021
    0x30623060405013b210601090507091a0d0c0815040b0d1707050105180601031e140a0b060121050903070c060c1707030512060102071a040f0e 62
    0x1031092141d40300341814405107102604400405001c540b844001c0125443c4020f15403c0c0c0da07400c1e644044d904284650500e070b05008079203201116002007100000028111a820860070800804002d0b0940c1d0034001c0380b05c8006083c00c4d0f181240240381d41888401511617010200c01d100b91010f545806061048a804108468400920a4052110803240402e2891f4a4000308540540901002d050a00300da41d2702c9609690640003860300501c998001c00c403690ba0309881c070150100100501c00c403034008d1001000400c9060071511101ea81103620050b4019899840c40000d030042070519489401580b40102844040a8520340c8000d0a00b400743e10b07070442c8080200c022000c0351035020020b50340e20102d0b20300b400070000e6841c80c03580600e4200d65241c030785d80e01030030140e2070620840e44008007025200d030480f0b01400765109150325882755800d01d00310074501c0700b000f04001e001504601c00d0400002c1d03001501a0541d1207000c07820510340c2d689040000003041292a50402d0000384102d50a20 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 441675512 1250 441674262 441674269
    0x1030e160e0a050f0411040f020a0915020f06040f03031401030f1218090e16080a0605090c0108040204180b1e060f0105070305031f1412070806061c050d030623 70
    0x1c0383d01c950700c0004410005d88540001d00103023090790050b01c0c2c0700c1c0302040400260f03400a80000554021021000700b596602d00b0481e9120804280300249801040100d400204247e4500c40e40920a04000c9003e204403101024484000d07070003a281e40d950a01c0000a100908000f800f1070000781c50400c4002c03e10102801142003a84200100c81342d0b2003604601d0354a080c091010f0b400e440d5030342008002d40d280c0c1840d07594101c000095842905e0003002c1020004001b81c0100c0100040c0c40d90700e0256240e408010082ca000300302d05200d92081c000410016941e03000140c03068002050392041107014038400394801b41c0003400c9034010b1a0111346d43c46540e8120301500c00079030781850101d90365500c034003208040c0e841040c00030b50308a000d104041352000d0514400d4108100c10740310046041a8480c48507a00c819520592b0382c2c07500b280d00030a14070304100d1044440c560001142210191140d40e4540c40c3c00380326048413000a0340c0310001d01543d48011040002c404d500d003401d554011605000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 441676762 1250 441675512 441675541
    0x1501030b0121060b0708040608010e01050d0f140d02100b220209060d020c010b011205330a150908070b0d09020d061406010809030c100b01030e160e0a05 67
    0x840e60003401c0e0341c8001d00d9112643c1100d005420199416626401d5614000c0b2071038209004034800302d04068000702e11303070306034401c1d0b103048440007055908902d00588403600611000c0b00c06481140c4151039180a1034010840c42c8404521340d8001e041441e4100a5801261100304075135104544229542c0c0028450b02000000e561400e03500696604864001421500c0380740489614a0f00200b1100032800043d0710880c095142a01c1d01e03180100c03029210402c840d011503c0100d2007601c00c07841100072096401c5840704500f021840c00c0d00305140d40010b44142916030080c03000c0000488080c0c0c5103030b40b00000f03000804008004004040c1443d402c1107041c0180a20884407541d650b6445041d5502c01e2045e81c0802d41000d4100100f00348910380000404046410a0215080d4008120200400001c0343c411903610005060301c444582600c5003d0706001010038101500e030003480040304024010304401c50000003490700c1c1c0074608092030110000c000e0642c0742081ca0f00c8204510850b1600c0c0c03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 441678012 1250 441676762 441676787
    0x20a0f060506040912080405011505010f0c15020c010902040c02060405031e0405040606020c10020d05091e0402030f09010b03010c0c12180f1d060d0f1e08031501030b01 74
    0x280820180c2d1803801040041805041c0a82025080c80d00040200e41085041e802a4040d0009110306019240f020725003031038a200303060005003400b070381c0c0c052503209880a800c0c40303101c0c568444010800c0784056069800400d04064180d64039083c1d4011841c2911904040e003019002070314032460951546c984034083d4125001001850101d84901d5941c07900440d4003030700c8011300800205458800081d9a40c405a881178000c0d440034000d01a4036000054104244540343d46003440c0c07a00c0303002442050090041c02800304603d13082d034020959698000b45214008901c0050281d1030040d03c1e45080d21621011603004e41d150201d80e1003565484001354028680240daaa4a28601803e00300c1e10414150010710001c0c01c164000305a00b5203100744c02048402070440c081d4400120317901074011003410f651084e809003404a00500250b2900b900d03008443c0189066076260103d03c0401240046846040b41c000e000042001082078941c141034082850a01e010040e6088000000c3d000340f10011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 441679262 1250 441678012 441678023
    0x20d0e011a060a050d0f050117072301030e0a0302010c02100908070b060303070219050109060302210417030103060b1806090103030e0f15030f010819020103151d01031101020a0f 78
    0x14078403035964004d00803205100048081003000340d03a002c400d0341c001c02c030a0060119445401080408110000800c403050b1410b1a015036005501c06e0400c4d10550562200c25040c50f441e80c4000c01219400e0003c81801341c000d070004244030102c08002400c00f118140000e0045142040f0000851240c8042d5504180c0c46014a10300d6203c09001078914040c01000940c4042c0071020b0282100d01c4000a0007111130a8a0310320750140c5441054081c3c2c02002e65040810004801000c1100804008681c0150140e140e5025690140e95185c00316402600b058450300d8030b45070759061070b0401143d803c565151180300059541000000913520031010701c0060301300221030302c010071181c2d00d41261036486003004100c407036001002120600d03a60012140070440b01a81070002501100204000d500700d4513105901203003405c0743d401907000b400b58401114480b145800e0104146000e62801c92104102c1580c05106600d180b8220000100150b4004d04642088000380c0026662208000360b1365840b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 441680512 1250 441679262 441679267
    0x30207061d0906060409051f090c0804121103070809030d0c0506060f0a080d080f0702030406020a0b0403140a03020c0f03130501033210050d02060304020d060e010f020d0e011a06 78
    0x20030000740c44d8090784e04205800c0b40340009002d02c1d4020510b00d40780001690307a11305009039444540504441400d034214011030809800100098080c0c0041600c003105410110000051405014550781205c4d0089030f0085000800d00290703d4200000e0707540d0500c502d004022042d265894070b440e50000303000d00b03000300110108502d050b0f03914448203015001110441e107200c01070b6100144410030640381180c01240340004112030520210840d0142e0740941c0003012510b61542c0c6035070400000401c10780402034050318001054002400400d07000e003141d500580c403040d03201c100c642860b04144030103000f075004000c10408041102808800c0340c1e42400e00044449110281a148080c000340720704024810450f8507281040c1102550300810410341070121880d01c07071085c4500d054440c100030b548a84c0074000100180f400c422901c0010f403041c10b010591050182740c0c942510102c0030742100c0c01d80c000c1082640c101e9144100541144400020700a40c601c1002c880c40d1030f080700d42c1c1c072030007074800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 441681762 1250 441680512 441680521
    0x10c0f0813022d12030d050c120103030507050309030d17060d0c06030e0a020316210510020c0a020a03030207060f05030c040605090a0e0c190302180603061516030207061d09 76
    0x41181c140807408000d081c0f0713110001c0b1310840c541c40c0ea200c2c0e2603200714a032070724001c158070402200958240c141842e111415503401c50310b00741c41c1600900400c407a41d101c20030001c490f54900340604044404661551001c0b20401c01420350302031001403820740500f04840b254008100c80b50b22407021144142400103541e100d03842c075030b4141411008041d4042c410748903003100c420b4002c0c42d602c04669031105800100321007183c0c12921002510310241c0704e13500c826070403030455007190300900800900200325124240594040f50b0520b01c1a8801e8025804c00d003010041c3c20f401101211041c145803401d1403640c0352107200805039000e1380c026241085004542080d5503114180e040b00606803031991181c4c0d52402960000c0c055111100c8441e003105074641c40820f4900038000d8500b1b1a201d211280100038419050007244e42009101560210b1201c0c0b4400c0c0343d0980030000c0a000e00314024100f42000350b41406464601560f01046c200300710710802c5e2281d03d5444414621815048a00400f180c94 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 441683012 1250 441681762 441681829
    0x109080a05151801050c0a0809070e0109020a03090b130b180601140d051b190506070201031e0608010f1d100c031e0b0f010509060702040b0a08010c0f081302 69
    0x4900d10000150303e410284064400104041e048900c02d0b9038800c1e290342c9d1240c118945035185072054070b5825203124014804a41140c018014120003032500043c00c01842d103c000c11072400f5603804981319925a0300c1c50074403012403a06c1e40d1008000c1401000725074402c0f0980d81e40c98051080240032407000e0b481d4582a074403c2e1100c4c0c0b07401d8004d401c9070600c004105101040940203080c851003410270301e80f2030504640382a580421604002c25035814009241c00643c0549000070000000e65200703201c540c1414a58814000905034203400010310521410542088a500b24000310803800b440b80303008161580041c02502d04c0c40c40c810003182240142005801910141d4200703100200d1818580c042104181c1c01480800d80072640f0200f41d44080c001580c95200d0312907516001201000303094090305044c0c00000100401030500c0044aa40304400d908540301d00f425100000d461b101246a5654070400aa42004c096001001c07540110390000b0300b103c8803030340410010541d00543c00780402 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 441684262 1250 441683012 441683041
    0xe03010f1d060a021806091c0309081603030f03020901020a0210030b0f0f0d0f030e0a0e06130506090c0a113012040f02040b030f0d02070618050d081e030103020109080a0515 76
    0x40d084038200000c550f1440e010f42103510b94000d0bc8103620900002142003d41d8901200480f901902c030280510041ea80031406940078000c014158800c1d030b00d19100585620011101c52001a60006010744c0100100001071050350074481c032940649a494500d1b0355400c240701640c56000d1140d50b402d490fa0b02c0c080d0754282094035019444080c071600001d442e0b062070002481a0706c102d502c6c42c03c084640e103140b8211131040d5100d42e0001c0c100e0000403c9122220018800e4407058144000c0c01151500d44c07a240809100f5000c04a003800208071240e40c404c800c1398540b03210202e000034180075000b6111011274500a002800000d0814803407002c0d519940d00078000c241002e01a0345081c2800001141ea603020720a05074018031405a0016607940f264403500c00000d01c05240c9205103150a0030000c4000c5e460b0300603516201d0800840c06964466074005201505090b985da480c1d614500015107202c03a158061070345504412402d8001135000700c1c01c0e5009078102506e01b55240c0b03503a0a40c90408 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 441685512 1250 441684262 441684289
    0x1903060b0312122707030b0105040b0607050c2404091d1902091312020d0e0d0b0103080d020405031009020a0b18041d0a050604020405061f0e03010f1d060a02180609 72
    0xc3c0680305c0040305200074000924103030380b01650305000c2c040c03540040c020940309550019042d5000750301301440a2a24000321a8a03005c0d481040418038035003c1704426580c000d0b030005000d035550310040301020f0580201d171050b004059014103004074002030012800000e000303000788240d90890024a007071103c83c000400c0280c020905500001c580e8001a41d180e40c03600030040803d1409404c10941d11b40520f0304440d0317950001c285101c03646984c5d1203c40c4c54005074070f1010066003d1101045d280c400f0003200303a0840b291030700442c41110314010b21402c05595000707201c0b410030401c0309906071f0060b0b4100340203206041d00c000924014031000b02e041035003c02c0c54800c2030b020700000c11083c8040003c0a6001d240200d500300519151750301003000d00d000c09024101c3da40b01c0c0f0141c20701428020542c034042c1d1200500003040d904030407000316046030a600500200d80c08a0240d56954000411400740d01c070004200452405458090840f520036072101014490000081c104156031a09581c0a000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 441686762 1250 441685512 441685591
    0x403030f050702150105040c0e0f0301021b07030b010e0c0301170c090a0f11180918030703050d2f0705070317040501170609070e1903060b031212 64
    0x1d4245150020b442e44203407944144031001241c004140c038a450b105203c4009000e03120f464904c0142c00901480202c242c10050b419582441034803441000440c1d003130030604c0a64082e020040c25071811110354001038029948101d8007504101400c1060805c50741035428030070180600c20300e500c00c11031414454a07901500302d031400f400d00200303a0654002104808041401b8020040c5500540d5814019002c403c800300110a40010440c01e02241040c0c01140307214026901d0421036140e03074038540c8050002c40000300c001808042d00702d600d20561202c44910a045190810340400314137001004030b144001e0440c0c00240e134070801074108111070046612007000d00c0d44003030032440004203411610801d03000c9060301d040091030034000c2c41c03d18448c44009014110f1501e51510485180c541c000704242c0094410400b50314000500f0b50400c002c510800000c5000014981494101000b404a280e50410144101c0e0101f00101070300c00d50180503601c42054509582ea1001280d10000741d800a1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 441688012 1250 441686762 441686771
    0x7140f130e0105130e06010b1e04060c030801050d030c061a03060108010605030105070c030915030605041515050c2808070b040b0606040509061e03101b170c030403030f 74
    0x11802400c1d08964121141103510304d501c40c0803c0b001c14103075620044014029006500140607100640c4098101080540503000c629a544048210181c0c86500058003240300d03401c4080405505c9243c0ba80900b50550b08403000280994001d00b013080314140042a294985012001e0b5100724980101035010003000c551407540c1d1818024020551405583e00950038038000a02032405141d10545035541541c403507904030310309040c80038001c2c038001c0766904254039044002210369840c0558200210105108a6504e180c0000d007101e81d2850118402031010038000301c05a842c02091550300c031001c4040b40741c5501d007880c0c03200413001d88120004203481c101241d040c091205004070544103901c00c00c60700d6403a48403d020005c25006074410940d210003003000051560420f10204488115580361004810718030400190500d098070032045800c50351b45501c04110340c00c1040710800035075141482806030b00008882c0c0c18072000105545001d160000100701010300c40c1d40061003c1015200821 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 441689262 1250 441688012 441688019
    0x209101d031516050a02060103110319082208030d0e0712050d030c020c1e0d02041a1c0f0201080702100c0906021e0c04090c0f08011b0201020307140f13 67
    0x758031120649880420808100c90401e260b8083c00480c1c0e001080b0350000c200701d03849e644c5c0707503907460703a8001450340c1602850814400c004003004502124510034050251104030164113012881180a14002c01c03d242400810075a000030003160301c504078141012030148160982c0500e4529580d0016006080841c5c1ca1410b1001c045601d02c441c1c207031680c00740440038134a10202d0f601c0d54507200490b40601410000c00810840101002c0600f00150141c004c0c440640c0014007190300d61403540c02164511580003481f03240602c14822860a010171454030030740d01d038442c0c6582051081000341407022090109141d24000c100750b1261030800c00741400b44100e142001030003c6964030a8001510840b509044a04039140422603d200f03103800800b507403400ca80c200406400890703401d80d100136040c1c00224481041141405c0a0b1042c40c2c00414100d0a40d440071180c024a520043d0031a4814002d000c0c445a00c64008040000501e905984801351115041454826640201052440d465000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 441690512 1250 441689262 441689293
    0xf0304030201021b0f030301050d031b0302030915030c0f0703050408060406091a0603121e160c1a0901120b130506030f160b030403140403030c11040209101d03 70
    0x20000d4000c01d807610801350f414040901c0c1e6410b0788040002c51078000780010702090601a41e6402c2d824020314006801c440c54880841c092801104290016040020441803d0401c81c212050008100c0e50040c41c5113003910504403940504490360807180d50000c0c60a084c0741c454004d403405400c040059601c0b509091814100404518070112250361b090211010b49086113681c4901c100c402602601505d040035600c480070307912490900d1084480b04c2e112030a00b01c0aa0083d1448030031000e142409907200382410115500c070760b48070250500702d0400e090070b02148607083d90b030007001c00c1c01c01c18030903900020420301409030740217000d402ca48443d41c2044900c0310350708058003c070416010b50725110002181c3c1c0380c507100705c01000f842c9a5007150307042100d160140000d42c0e01c103002c0c4c541070203c0500c46012815a5216078000c0e000249801400010303c1407440c14161109011142140342c00c04010100d81c040000300c0502041c4070f030400120b00000010051803070401c0d80182500c03841c84c07444041c4d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 441691762 1250 441690512 441690517
    0x30103080a0e0a0b0c1c0203090d06060b07050303040c08030a090303030b0411030a02090916020a0b0c090303031e0106050a0f0513050307180515010c020d0c030506010b03070e15040b09060f030403020102 89
    0x48107175110b0200140020103810410000b071181c1036020b1440c2c40b02d40400c0c4880d040a1000c00c42e840c0b030350b07a80006070641d81e00c0003030300c03245200b01c0c040c5603a41840d041452068890360800c84407a0810040103060710f4010b0f554608a0358542404600704640320009030003410141c0348030b50542c0380001040701003a0154010500d1030801c07650b074810b980383c44243c041c0c2040c4100b9500050b03800300c96000003003206006142d92001e0746c4502d4a00c4e29101c2e9010a00b140c0054401800032004610400000c06081e0142c0d40542000d180045c2480b080346001071001841840348018842c0004401061014000300c26000e082c0280890301090350300c4504018080044604540d002c1ca004089103501008041ca410b07005416510201000515020454101205071048501c442105070000026809201d600e000b00440c0e6103541e2289000b24025000710491011944100b501c1d0007640c0303000c5041000e8800351444d012840e2346031400100403544610800305981e400c058040200420035505400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 441693012 1250 441691762 441691777
    0x901020c190308074d0a02011d0904120c17090a06030b130c180e100602151504020c030c030a0905030601061d06210901061505030103080a0e0a0b 64
    0x40d403140603a1502e5003120f0524501d44200b500c614030001c83c25003040f6980c04404110820404c403590f198081035206007420000c140c0c0c140c01d0700000051415980c00401010188002c49401107009d04100d000030b001c075030000e00081000402090a0030794510804d07550504a50110200c41000a20004052103811001c5403621589140c1001700d2141d07c01d004620001c8005005584420003002c08007015006802c0d1040421442d9007100d07030403032007074005540100401110203017030707003040801d66030a0320613900032100350350000c0c01e0a04190910211158800c031220051085d060125000030040d206200500d90248400b01e103940f4400404401492a02e0b0581c40f4892002c1e5900103064035020b00340719100c041508506000100058000d50321050071004008a10740001c02c02e54180710100400c241046001c160b0400103a00ea007445100083d0441c0c8000e031000b086084001082c9101c1400014041c003804200808400e01501c500c07480711200510b5003144649520300b03018103811051 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 441694262 1250 441693012 441693017
    0x706090b060316120f0818030c01050c060a1505030706050c01060512030d091115120903130513020d2a08100608280c030b03010e060f0901020c1903 65
    0xd011610794a03001883c40c000100442c0b84985162910040307840c0c582500000f6a060b41500301c29400013895035009100010840303039601e0988100340c0c14146030207000c007a402e05224042052903610300c0c1c00035040b80d11229034800030860543c5150124a020515803215070540702e0b525001c5507454000004d011081d283c00020402150356030104846200469580070072030300708200c1c1c2500380301180c0242508170300404181480440ca840070031003550900f60706490b5903a000c2403240c100844142250340001d007510065042c043c6002826480d400e070f0348155440380d08041c00b0340d5403076078007601036075030309442c44008210744d1112500c060300c07804004010802c4506c0607a24107001d140989115401560703020b05040c01c6500300b4100f510200c0c8040d180c00b01d41030001c1c1122544816042c944080380000060101e40501c0003c0c000d019140354000c07c901c0381e418401030070881040003841c10742c00f51a105d003500e03058842c40b846034024407070007807880c06a00076480c070344640b50005a00d4a01203482607 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 441695512 1250 441694262 441694283
    0x109090e010f05090a081e13061e0903051207050c180108161a09010c051c0909060b090103150914190c1421041a0108060f06010804060908070609 64
    0x3640240c07200d11088005001c01410b004e022007c1a5a5440640310348184800510b01901c0745419085805140c0c408000520744000103a620240010800382180389030910000c09400c40d600e5548a2000005900b21000085662000c0c4682044030007003010300a420b0b000d40c8003414501c0c42c0c414409009030002403140702140110816000f41400455140f0b0030b144992100700740c801d00d02507011030102410410b0010040c0041001403103034010307810102c041364100ea85103540141200304d82c0d501003948140b51050402480e0100d030101c481140c03091800089000c491f01407403a101201d038000c030005602c0d001c0c07100c010181160801d405911322000e039a4181440030004015109489110700015086035034480c00c012035400542202c01d6254a40101e05407011000e00311a80101d900340e50000300261920071034801d41e54500d015100c1d8001500a620341000d40510596003d02580d0421900300001010302201d44d014054065222091554401d220304008001d40070b0310340705170381043c0e44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 441696762 1250 441695512 441695521
    0x11030304200406031b1a19080601091e05090a0c0804081b0d09140f010c020d03020319210603050706050315150304062f1b0304060203070b01140a050402090109090e010f05 75
    0x4020995141c248200c0b641e610b04055180c082361860000340c0407d0600c0140c900102e030000400e004805040c6102407250310440c40d00c410048a03100182496104030319001d00d42c0445544814069072054002ca80b455413030b0002d00c0301c3c4200e00316818601b401c60142400c0d0f101b45035030094450040303540003800c5144141d1101e04024054450b1410315000c50410340300a0010709100b1084036135507010b0300559003894405060489006201680740000462401942c000d10400c401c0e81041302100040410040c1c1c1140e556039601c0036a4060300046c4500800003035440c0760700c0c4100b06207a01e0040e0012218100145000526810039241201e8086c20560203c031480840344540000040d481da040314400003001c000c40f120780c0080b41d5500350450200e404003101804000610007450a0341c02181ea4000300d08000e02c0c01078060f0003404030400030f40120f40b0f080d07443e0794500c0300340c4030222070059403400410016159900c0a2744201030460070300804102402d01035106502c4250041320500c042d956 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 441698012 1250 441696762 441696809
    0xc0607090b04061d10030c0816140304060f0603030503041e0b06151e12070e150904020c0a0c1e080307110a031e0311030304200406031b 60
    0x690140c0c84482009002c10001103108076041e00c2c00c0400c904510901d90b080c04046030483d4201164540883d0302d45000242c031560040403107500c003140f0202e803852000020001065440030611041c05c0305c00c040081004e221032541b210130b514031240700c204070302c0e960b900d0058059041203030255203121603405604607541090240f1800c19034810780418103542c58008200d9000b0b02800f0b102100c120501c07106c020483d007460700045200b8201210350f20b508038410040303500c0d078000b4240c104218440c8000c2c0d2040c4c4909200319005071b01d50300700c90388036580400410001d0058100e0341c8c85501c0341d07241c400c0c00e00011401e02e40544940b00742814101e10750148040700b4030b52621843d42d060f03004115a1010520024148000003c020a04010b0945e251291905100c1709001004d0010b08200c0c210f007010b8104244141c1e151402d0061030a43c40d0030b840d03181c2d254140400d00c0240005000a44800342d035940d014401550340700300201e040b5010ac144200108000c0d015410400e80e00312a4040c1c2c102 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 441699262 1250 441698012 441698027
    0x30405300427090f03051303020a03060516020d020607082503050702010f06031a060d0b0f07091d0a111303080c1006120f0503090402070605040b150d0803090a050706050c0607 77
    0x10f4001070100302c080b134195001c071070a50201d005030303001c40101c1c00c01200594820916000450160390081100d0818003041c01094211125040039503001056185c01c0c2070b00499038990040341420034185e01d80e0f5020401c111250446c0900e05030852041c40c0380b10300c42d01503000c035001d194558020031078101030a044404540303181c0005000c0d00d0041428462000d040d01109038001070144c102d612041a9564452003c441540d034004646400d00c100b2403e0365200c0030280050a0b902c044441604001d46941d5840c0c1000e00309140190312480b40000000c01e503411241081d2010b5401c1780001d903642840d00c1160054420b03c80300c0d0080f40c02003c04892a80211015a40a060901e21400140e9101900171501483c21a02c500043c00340c1c0c1d0301a9214030280259038001c07a00415685024074206030000c1c4d00400a503448500170143c880141c80b101c090402540d800540e080d038075140c7c07040d0a498030b48000b50003800746c85072800204449a005000e480305580150444405445505080d1000c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 441700512 1250 441699262 441699281
    0xa03090e0c0405120f060403021f020306090a05100f1d090601241b030c050105160813021203030406091703060112020a121a0114030405300427 63
    0x544051000340182d01d01640e8240d0f20000036011205d040c40450480c2e401e0810442c1d0681c00758100b000c00268501c201100e01d0003141c00104118550701c0e00c070002a1058401a011014095889001075003001c03a410b281c001a0a22001c0c29854a40c0d80e504204a0f506507402c142e42d21180c04003044003100c002900c541a54240901c002c403040c004040044000706030b05501342000350800c40e0307042044c008240044110300a6803115010b941909006003500d502400c68190307480950b0b070201a0030b40c0024000d0300264480e4039441001300c54000111451884058100580000414001004055800000c42c0791040c031204a0805004400b200e55000c21141a40414480f405000010505600400451103103040c818145003240d1100c0085500c800341007503110540c600d00030145d60300083e40a00b09d8904003940781c9940341c01c0c2d031110707159040e00090419079a4101c00740114103c19000f034407101c6c81804c03040c030703282d0341e480310407280510308240d04455880b103020340d9580030303d0700d4055003584 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 441701762 1250 441700512 441700531
    0x109061d0402090c0309070308040b030a182a0306020433020703021009081f1b0e06070c03050a1b050105032404023a020405100c060902060c0a03090e 66
    0x20f0750350a404c0c0c04c12580010a000102c0c001e120b000b000003941000684040c180d0315440c5602c91030000a903c00b12508501580c900440301c103d07050000d02542e015140e001100d5420a90800720012003c40c01c40c0c80c0d4000900c01400454045030700200507100380f0300340c99606106030001120816605044030310205c481c0c0143c001c0c0345c00780058180320802503400070507494040c1181e6912101e80f400d100e5a18015100042d0b00600c0b0a801a00c4e40203602201800000081c5003146540005d080c2c0322011207818010400800c40c0802c2c44581c6207580c0007540c010040c1d4101501516040982e0010f9245e1038035403000746800400c0551140c020359110742d84640d050f01803900300c0303c2c1c00c81c405540741040c0b90f0710079000c201080344001032802c00c0541d9440c922008840b05405a5142600036040e50034100c2c0500c10300003003165076207134100d07189420502d0070718070390315111810044060410884041e402001c00110708100450020b102d020540c041d5807400300c9c031515100400c0c400340c02610604903 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 441703012 1250 441701762 441701779
    0x909060b0d26070b070e0901151b0c120b0f0a09030f0c0f02031009030e0906060703110c09040b0109050915061002070e010f0e070c0c09051e0109061d0402 68
    0x3002500c0345a609116a103148880d0500712070f0340d0f40130f00512080f03440300c1c002032190070341c220f1a09000c411940500341034001c104402a2030600106940c03400c180c50300c1710001d08a82e100600141c25000d401401e103101280091419900300460300038401c1e201d5060701031400000034084100d6200d0085203952583d40c0e07060504d000c0800310740308894082c0550b00204003c092030300685e0304001d00e80181d1220071000c90841e820b400c0c040c101000802c03499000d01c0101c0304020403544e030740d02101c014940c14148000b803e105040c0d81445c00800310102c98100d1030305001d000501210020319412940390700310501c00b9540740c40005454103c4d28000d944d80e00302600c08101b052400040002e0004203034411507142c41e0341d401e400e40c003009007070744503040000c600e041c140807810103592070300d82c40380caa070820702c40c0d2a002d55998000c85071030344a0300e50040d50380e4000c18040c90103445010320101034540440d0366540c5034000e1400500345c0e80704480c1d0140341e54091110141d201c83c0300c50f105075001000c0c41c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 441704262 1250 441703012 441703043
    0xf08030f0714070608100f0f0501030e0709020307090e010527130209040c0503010b03030a02060c090109051210060501110a080307050f04030c0303020709050103150903180909060b0d 80
    0x500d90704240400c0311801d00000c403160110108129480c02800f0f02c0d41e03104034078201180403100112080d080182945060319041c4894408030314600c045400a1a00090300800020818205000380d04004125800001404074095100070b642d015200d40e03088201c2103980c1e44080100d0300507103c0111006000d540800307010030800c003c03982d600031140450460b40000307a500080c0d12040407141203da0017502d0b107082c4800c1c1001d00c0f03440c000781c40c254000e5142000b03a100180d62581c00a2814400103000180c1d1002c43c3d00c200180c10003020050881c6c2e0240c0541c006083d03d403500301000b60f008500d0080000352540c480c01d11048200015409050031030340344d0303c40030404c0c0e000a00301c50610004212410408950000420003140154a107000c810f0442c03130b0082c201000c0381e000c1030000d4100001400414044806941809107880d80090903030118901034449865140086d2000001c4ca2000140c0307210340d40044016078400c0404000d1600840708201a004500c0c0f00a00b44482c20b10215 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 441705512 1250 441704262 441704287
    0xe1e061201060801020406270605120604060f060f02060f06010c1b031e05060f04082704020406031a04020f041206060305121213031e051b03040f0f0803 67
    0x2500d680d20240000c10b1a030740301c2d07040f142a6402607000f0030005825646000c0603407291203a0280500e802842c001045103000c00c02000ca01807205041c0100300f41c940400c88555032544100700500f00050365000d4965203903406001b802c0344085003400b50181c4000134840b800141c5545200300016150030040111a407150b841c030707103494480441d800214000c00700220f440015907103c0d00040b0400001ea1854501e030060070400007130425650700340c0c104103010001b5944419140d04210841a01d60184205192080607180501d80250030a00c002004100c0c5c0c0e506811108445160301408071050000205001c124820f0070314502c84000240420710003011906240000140144808180c45840380c03078550610300c40c8100f0341042c400000380e400021000d03c010b15405030300c024540d03c02000c6900c1c0607090000b80400429805114181d404215008109891a02c0080b140495100307001c9903101c0e50301d034464001c001151182c008001001600c1000183c190390350440690305010408201 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 441706762 1250 441705512 441705529
    0x1006051309060605091807150905120a0b0435120c0f0d020904050a020c0c04180515090f0a05030f210a0b0f03010623190605040e1e06 59
    0x12030321242c40f8140041d40c1e5030ba50880c680200100d541c00b05134207001c800210b02e801d10603800402000c28102003a110308d0341190000d001c0380d03811b4620440345140020058140001030030004d051450303804c02d02040c44001c50030800618920458440d40d0f8550040412403c42905c0d0401d4401504205140c058072100e9900c0f604049062003c60031701e9510f0081d0701d040e0b0001c440c7d9200c001d84c0842c0c4c282d114685801966046502c4c2c4008511785900e02040c40d4540402c0c10a1a009a48a840c00a00e030b0429951403118241c1040c1a240800c100c240074401108064610b55002d221301c0b43c0c0103101002c0403444a003000c4c1d000c401149408102195001c0e241c200a4140310075400180300d1646403e0448001481841c0b0500006641002d12040003211016101100d00a81c5049000d22030541c00b00501c1c5401c43c0e1011001c0514501034000811509514403003e4070850f000c80d00095040d0040050403d803544a401140703203a03958801a02070b401840c004658012400000c02c0807402c2150f0b1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 441708012 1250 441706762 441706781
    0x4060207030c08030406020d0f1e0e0313091d0c0607170f0d0f060618060c0809060433091503090c150207050f21010b0a09050910060513 60
    0x30401e030907501d1030303d070354582d6041250240e44403a0005500c1040794102d10841d2051520700108100603205085041d610f454159005030345941d40e006441414036040003965035203000c08084e242c25a031203480410213003240d8200c2c10101009510201006400400c2200c66a8005000a41071800d9074407800d41540030b8800d5080b4202042041e402c40304c9052000782844848184041280e20407200c06038201ca469601c07080c02c01c003044040821406100039520121801c40c1b03808034014407142070481a510a03520303070301d03481b1b800058000340a40304452210b020911036a01030408042403080d1075480f50104419400083d0002001c0c0012200e035a0261040062031800107480c40c581e54038842c1d5820203400064544090806000083d94100440c2e40034140a59012131140225000b0424403100b00b000f03101659081ca502000b025400d41c4200c5407488000c1034030300305950728000302005150a4072600c0450007803403600074445030b650003500c040b18006010300b4440f00c45881814000c2038640c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 441709262 1250 441708012 441708017
    0x30a020d0b1e100303020f120a050d0b06040303020a0c0b0309030301170a0c080105060a06090b1803100507030c1707020606130608010501140102070e09030f07030e0d030801080d0e090406020703 85
    0x2890084214600c9030010710a10b0f8018651090780e0450a000e45084103204664079203a200603040c003c00c0c1078034419038500511a003001615500d02c024800c0c007a00c440c0c6170361604044c000c9000420b1560004d00d07607080710b0060a030102015155810010188011071f00000298000c10040200c225041d0601482155550941d060b070386296a45031418699030388520b0080c0c2d120400e0129901e020100b4400412075801c000403107614004412085010b07810660200805d409903001c040d44050010b480200c149100400c0b05e4540400080c0080410203120400a100c81071018584680900f14a004520b0354000b890295140d8013046105c9000c0d900c40c40286803240d0300002d03d61001d02805028101d100e10142c00ca03081540024039050481d0b2000c0402c440140c00d020719180007004503002d0240c61101c0da82c0e102020300f1705a840150b003004030707a0440740003211441072541c07141c4940d0503038004c0015210030108a0204403449100741d01c0070f6a11001070f01c0070500144056004080341c0c0e1007030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 441710512 1250 441709262 441709291
    0x504051306050d0c090605040b1f050f04030c0e07050406021005180304030c0e060607020d0807020316090b130c0f08060307150206090609060103030e060333030c030a020d0b 76
    0x1540031540000240000321000141c251303092210b04500d0140c40003401054404100c600040d0002461a15001d2010740342500095115104240714104885040c00d1200050342d99640c2e900e0703c03100550541c8114451902c109001c6080307503200350226021600d07142d000b0171181d0207094203040103140280500c50701d0000c065407a041803070180080c000441c000c4250707003040c0e031401c45d40c15001c1c6001006144a00803c021b007400513602c01c3c030340c0c1c443d180d00065040d898490501c04603251126212245041d504444000200c403004c9030481c0408440940340d07407035076083c0c5a07c20700550f4903134074070780c2c0204180d40482020341e07206005007544280010b003160030f070310b17a034082030225400309000610041c0c20046c01c00140d010104117490300700074958024019503140d46c030018030300112a4000c0703101c0c240c00004120030f800d20b04031031410300d1500b1140c146404ea1084001d0000071641140c10f009000d40d030b014950705d140100340000b425030040c1912841c42850783d03880f94146c41c0144a40e069030241c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 441711762 1250 441710512 441710519
    0x41137050a15140405090417120a05012d06030218040c200607020d0c060b120c0a170c04180b0403030213150f05030a060506130e0702030a0504051306 66
    0x1001c0c5620010160342500400b0714112040040502041003062041c0190812040040e604c941c680b043d800b54200661040501151042c001b142c0b00d8407281d1042c0c1c0841409100b001100e035800306048491903012000d02c18080702d444883c0800f5a02c1e1800c4505034000d04002582c001d40040c2042400840800a40032481d0300040440d000c0500140014840151241482d0008042c1804064030400209298607040f24001e5891003030070142c2040181c281d00c0d820812001d81c00465007854001d0140321440d01e846143d941d50311070189070070f21403000e520001540340c160b03207100062020100040d10b0303800c41034000d12020b484409034602c0c14071441d1604d0808103034600714140c000c034403a40c2c0160b075072150702c1550496084c154101c040d40b0201c250b2440040c0c3d801600c540d603002c101c0c0c00c03d41c1d100c0ea102d0107407900078182a070080740c0005000465070402d8140031010400c1e50b2070008040c2564a8000c001c0ba0741e030103200c621001051040106114a1030202005001c0600f540c0c8046801500c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 441713012 1250 441711762 441711769
    0xe0307090501090203012d03060b0112020304061a180103021c0b0702030712050301080d23071406010909020105040b18041a0f010305070c261204113705 67
    0x400d0f0f00c001031032940171006011380b4016200c006c0c41d104800c0b1701448409110344401300c4510700d610004020f2a658050301030142d000b610051118903445c1400c640f02d28203424103001401c0c8007040c0070341111100048030b0040c41d00008498100d0510310b04440300307a085500344401844001111500010621503131000036002150700e51103030f035003640a151240e981d460b001d20b52030f200f04010800c1c86420700c0144051180042c101c1480b8149207843c0480e0140d00c11a0219440c01a13008024040300103034403418441c10101d001003944900080310b5150f80da6200500880d09800e10003400140100070800030380c003629000d0030b20280d115520341c60403401c08000a0456031050445189403001c8244812540f41034911521548400c0c00d0621241c94207081c018646d10560600030f1410744410580c105c0c0b450400311014142001505c0c6581d01d00d0103000710151030800315400c59852016250300c08440c20100009206c90301442c00791b460003a0810000c64101c4140340c003c2d82908203491000030075a9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 441714262 1250 441713012 441713021
    0x61401031a090102030408030c0706060807060e210c100323040210020f06060d050102070b011205070b0f030f04020111070b0301141203040b030606040e011d060f0306010302010e030709 81
    0x1803160880d855414075865500a40c04002066291140d2040c000c01c0003040d4810101d070b0b40000d1010300290b40c0c0b010707072414800806403a000131807907204684010466903001611041104c0049901c007000050f20007400b0024500c0c4040741410342c000c02c10a064034204101d031070000d01164100070840c00741e881b4a01044182c02c840081425071070506000640c00c1c05841c100c0f4000c100c0c0b014040c1d007032036004456510280035010300c0c09070503800480130078030200307505680040380c1c04a60300509586d54107024a003030703480326800d4415000f1000001038181040b41113070341145089a00ca4156980c0103280c1040f41002081603041c8a80b0180c0341800410522141016107502d00f0003944035410407884003016541b0075031031800307020b035940c180080340c4000054804071000840300702e9132a581d20b00890098011940402d001c10740000000c81d802521803031007210309003014842d40c82a038514040203060051820400c0e0590003040041c000341d40b05610740d505540d80035045441255407030400760100c0303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 441715512 1250 441714262 441714269
    0x603020d02061b1605011d0312030c0705060c040302030f0304030b04080306060702120a030e0a05060d0f1e1a09071d010e030f0c120f060a1806020406030b01080c16030804061401 78
    0x11300400b083c001503030000c100c0c80703041032000703060040e00c2c40b1400070950301e9402e0b0411000182001c4001200c0070502c3c812200845e5000041d0b50072424042606500350b0480d020891203802048420940700f14000140d03000c60b6000555030015803070b6915804030340d90001e0001e5802c08000c01c80800513072140160b211541525a006142e440d030542402402e25011940443c0324601d840010010341d0b40300000daa5040902000c000707600a0510f08030304c0141000204c0c6840d0b441003c20001c1421300d036a205c2c9564600102000c0a142c003808c0c10041256402c80b04040407074050080018581c0020500303803001601030511100980e680302c00240360000380c6003998016409aa103981035801c00810071034000140000400f40028040b04440d1184030090407140c0c0e5a5440d00041000104000c4800c009a0402402c640d0349407601d02c01405030810309003041c0400c1c44400455444203640c0115060880140c460b003081c04030a03034044505c0341020f4401d0b14407548600d40510500c84807445035009 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 441716762 1250 441715512 441715543
    0x70c050a020405040f031404060c08180d030f120b010906030c09080124050a03050c0607030c0c0905160809120d0b090c0c0607050309070e0402180c09040608010603020d02061b 77
    0x3211702843c009024a9440d8907a40001c0b0041c041040101c0d00800c03000211581302800b00d856081c02880c2c02c0c44010104c0d801c50b0f11842d20410b003c10b05401500e4803402e13090554030003540040c90080c01e003d40d43c080d0b180354000703407d032007042000c075100354008020141d46141c1018065902e020b010b0075541d0101c0045009401c44605028507402c0013112401080151002800c2626544880d51201846031180e4021040060303190101803045103a0403a050740442e90414580c1c84455400081c00c0c11560032110706925941e81e94034078024500d851081945070000c02580002004081e800d801c102c5d4160015501c40708403425aa45070000c003446922691101510b501c00c6503251480c000d0b0240c0b03c2d01c140407042050282140d07000c40c050041e45c3c00107415203a107072203520129080c4840788000d0100b240f801c8003444019003002d001040001d50486040c441207488001c640c4c00ca4030940720082d807082e002c8581400500b0300ca07000d041c1c0300d00036000303d81c10f945007507c400c0e082c40441c0203095034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 441718012 1250 441716762 441716783
    0x318060f09090e0d03020304020315090c18190e1906150f060504050f150a0305041106040513051503030c01090215030c0706050406110a02011506080f070c050a02040504 74
    0x40d03500021540c024001d4007014000084289055500e4542c001300050415400100040554030100132944c0d06041c65891207030382c3d15288082c503480f1030b501e03c081442411210a030b13084000891000902a1045440c6180412030280d103585c006c190445400c00640a101071200a00f034200c40d02241a1f40181c2002c0b0f06c181c01d50050744c030031200b03a40202c010041500410b00c001584481a1815034406a440c44896042c1d1400101d05108204000a4590700040c00001301503054004034087c51141d491003010801600400c2164021382c01986d41086101c4034040c903a030720a820154200d14080c40040360a0141b0011900716480000c03200e84c0c50791104480d60450400f02901c945c036021003a240b50030342c10019010034a41c41040005064140c44034040b44c1800481e80c02a03040318a140703511580c6800d4008041c0c0030f13041d0381e01d4070000a0b0071071000040c802e00849030644644441c0b00d04d844151b498010588100ea0680c3d82a0f407548581410384006884610410740075900400b001d65 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 441719262 1250 441718012 441718037
    0xe281215050903030112020a0b030c220510050721050a020705030106120b04050c0603010f0e0603010b0901171f06090b150306040903030e1606080702060919031806 72
    0x110480c030360391920034640d2074201008046500401664152000002c1c5240004810700014107180c499800000c0e90302000000e202e00c0c1c403042070040144041c81c62264002d030104480b1350500c1591440341d40e40080038600c05003e0148202e008106852058190710281464203014481800300082d4200102d140050034581c51a01004844000c0004030003d03c001c5050598117030f2100c16103040100345031007804c040340402070705100c0d0b0390318400c015140c3d41c8c40351703900c11049091542500c40d00c402d120008012820500703040c040c008540b03030081c00d44203041e480c3c9120071402c102884c11150b890b00540b504809211044402440c450361000f402142080c00c1980640881c0c40000c0100d2081ca44240240b80720070210040da644407004650008000216040c10780192064000d030341e00700c1c080c412114100c202902c0200040e24005d075100300880d52806c6050340d852405858030381c29640b004241007072440c0080c8180c1c800a201e4a012031034009072603654600c03005183c024401213640e503d03581 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 441720512 1250 441719262 441719273
    0x50d05280201120e0706050705030d05040c17011104030807210302130b09090703050705070503070f050601170703080a0e031e160e16020c03070e0f0a0c0e2812 70
    0x1e00b0b0002c1c0e410100300404c0001e1489030344610501c5000e01307000c0003140007024814144103849a81c842c2190901c0b4616041c90812051011409000200d4000c542c0c02507a1031014418686000401c0d00b145e85002e045443c1c5940c560429001200d4181c4c0e00c0e04018041c00b0b00d021400404aa20345000d40c50300344103041c0031384c0d101c0c0c1030300010002d200c1880241c54666520300b040d40c006000e810005101d4447e00c200f01e846119519002d4854403001440108000002c101e071421140a2000d54416036204c258140485420300b5050070301c2d5000f8101400800c7c012401801c0d00c1a0500b0b00911220319100030900b0900d003000406550001003001302500e940078000c030b011a07841040c0502485050403811041104090b2130544909800400b41d02d6582c000c0002c05c14140c0c2c010100d4900b10b581c0d00e0308500743c5d18201c9406e140601e0810125480100714000c4081024450300c0e4201381c0146a41401011411442ca0641080512848414034101c0c1c61566000e05a90400d0080301c16840c01c12 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 441721762 1250 441720512 441720527
    0x60f0d02070b0a0902031b01030b0a120b090d0f0f05120a05090607110d140c0114070e03070513050403030b09010603020c15040308010303080a090510050a140c0301050d05280201 78
    0x3480141e040182c0703580142d0340800c1171f44aa240c2e0000c0e0030100141900100c2c002d00d41858100d0b00f240a00201040c11144c41549000356849480f002c0516038480c0a195141c44603500d0203000320303d4602015149074058600d240d4402458903102742001c1110524406440d001d4a10315641c1c1c0da51700030b00440d09000e201c50380c0d00c8846402d01c0c2c04800048034a06694182d00c1a11000700402002c140c02c3e41ca0340724040b60911008440203000c0d9002c00085008030301026a07000000c106218082c00160402049102c21560001c080305c01465a5071900400f602c402007003141050340d54040701c0701b203544502d602c0f40606207a0360010703142e9001654851800c45010585030810319908108000203a2003100b19065076030610b0406203980350000303054007a0460031801841d0b409000f9466411685560106200303080201091010701c1403048c5000c18010306a480c5c40d1400010001807100c0e0800b04111000a07205008488003010390040344000d8007416061419890410001c0d103040d5a0310491 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 441723012 1250 441721762 441721771
    0x10f08100c051c090b0a0507300506060d0903030209031603050712170c0a020a1d070f020c04020409020304060b09070f0c062301030611040e0a0b060f0d02070b 70
    0x60401c0340e2029400050101d000b150700100d400c500c0440100610f40854001105180d8000d007200103d0400e158040050042101c48100103030004011400c18101c0d01103400f41036141d409148030b540e02c00350284002e4440100a25000342d400c11510200c3c080754030800c503040f8000ea60040e01c48194104040c1000010b8400c0c1e1802e07811070030280301041c5c01041160031544501c280808040181c90080e608001070001d0f0680001c020a040c40760a20100341058100d10071150040d1164440018481c403030b600c118401841d0a001001400e50b50240000f4030050500f8012600d95910140001d02640d00907004101140c0d000700c01c4c841004400c0c016a480750004503450040c510700302034018840e03520040399030f0030801e4440303501040c8442644511120382c41228450b0040e240e5000c42240c030f800a22045444624120300500c00f02c0c0314405940546140c00600e01680d00c3e042e800e48041c29859a65590000c3c0410400204500360002003089080170040941c55400b181000d44406d00c0040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 441724262 1250 441723012 441723043
    0xa14040c080601080a2f0a0803041d0f04110112090c09110a05030f100e09060f0a0c0f0e030127031b030e130605040f0209041a0303040626010f08 64
    0x3e00e400000da1840411680d43d184c1c0300100704011421030120842d65921b9495070b81107005510b010800860202c024002d0303d90b01d596581d600c1c031224542c0c0d00d00303441c1181d84c4400c1002e1000170a001071111a4a40f140220515215410310b43c1074102104440b0501b008170390704240004108181c9000d80141c4503c00081c034401c4d401c05400c0340d00a0400d100040c000c203800140980050940307402d0a030002c000d0810b03c0d000070005d18081c900981e0300e00c0709840324858104080005000203130f0600070840e4010890b0390365012445c401d2010b1380d124002c6041180c0c55522034840001800314410700c8184468288400c40c01f09155080c0903240710407500b01d50b008165a01c2c1c6010120b038200f841c0120180080d24100341003071700003034020002c06082d0801b82e80b007410b120050a03044050740150100001c2102c04100a9480c50f409030120001c0320751203509a0030920007004a1030150074521401002c2040800c0b41d0407500000c0c0050f003109802c02c400202a8074070610010104100c1c0c0c1044c0c21205 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 441725512 1250 441724262 441724273
    0x2060a050406030510081f020c030f0304021305060609120a060e0d32071b0602100605090f0604020304030c120504180e0a2d150b06041a030a14040c08060108 69
    0x80c001c7d440341d500d00c034011200e0350581e202402c51004d683c1160300304c00380b15042c2c9855991000c44103042d94400d46059218035080070095000d07055500c9150701450b8020304031842c0c0f40446003800260710220a0401d864081c00602e440410902d000d918141000040030f0026003480c10b80107003012146040340d01c0c03000c101500850144100c006940020904000b545840380d0251a24880b17500600c14095540f2454800001d80300340c00044e5030403600f1540400780080303a00e900c00d006000800f25840003040354000046011070903c3e134001c3d5007050280c500194855031030f88403000301c0003c1c00040400a100001d0030014092229000340440010200c144961410903096503600c02e03401c00e0240c60740c0703c4102c403c0d002c04206008800000700c030a00c945407421581c10010314110340340c061080c010f82094019409403411004a0341940c0ca8041001115260380d02c40140e15000100904c00b01d55407040105540744041891500c590b11a00d0203151080c01d0000d01810300c0740c1a0720003003042c0d208 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 441726618 1106 441725512 441725519
    0x50108100504020d1d0f060606090d0c120302150103110937150602030406030e15040503090406080c100c050304050901080d08060109230d02060a050406030510 70
    0x2e04d170b86980401079142c4180c0c95443d0210610820781059001400d01d1400c0000b070b048200d00680300700302441144e40c0b1031111910341d0300403c183c5d25060003034408059041014036403803660b5442d6012254919924181c0d00314035024464403035419a0700003007400d0001001c0504807071903001401105482608101c1b0802c190907911003a85040c80d1854101020040400c1b04540e00780c2e000b50301d058034161003203004015450100303a450040d54401813005180c11040c070300441c05100519030f030301100e41c00c01045500341d0b4007034183ea8210703140a08503a6900c0c030041c1009486070415640d01080f42c6410360461095812856000307013000004103d514002580c04031201481c0c81d46a415110880152101c0d2064428030783c504400c5481c40c545440d401c4900b442070380c0081c007903a90398900e507400965a500003442c1030340082e01c04a0100a05075141c0542608104080002c3c0c903501d09 = true := by decide +kernel

theorem cover : BRFrame.Cov 441546762 441726618 := by
  have h0 := BRFrame.cov_init 441546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 441546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 441546762 ≤ n) (h2 : n < 441726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
