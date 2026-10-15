-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5375
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:40:00.050668+00:00
-- url     : https://prove2.me/submissions/2b0557ae-99d8-4dc5-9bf1-c27457745de2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 966546762 ≤ n < 966726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 966548012 1250 966546762 966546787
    0x2010f030c08190204030204111306080106021009020d050f0304090f02070c14221d01330f0807051005310806090f0c0319020907180b070312060b 64
    0x210380403c0075020080440142c542d030040082c01c0040f00c00d89501c1d11550b03800c2450400390307500203408001d41c4000400030380c1d40c006a40c01c103c491030200054102a64008950f402c1007102c000b42c414821a02c0c00c0c1402800000100101e900c1d035201004088000303940c0c070045e44035844000d8146100003106101001c1c121000b410300710b0005200e91440030750100019984a51401c1c1c582c4001d6440319650340e411194410b075070b05100450002c01034232840c51f41d03040b1075520110305443c0b01c601903100d450122090b8054007024114150100d4042ca079145000da42d1405a405818081e034400b4100e080500d02038800d550001002441800042c250001a5558108040501941e03e4050080016145401e02038240115003010241c0382a5030a0022185010150303a4a40d0090780132040c0d011002503058000c3d034030154112000101501e03070100032504803c201d00a40b0310310071600c0c00020081d886600409a0300c0c07183e250a2008040d12502004032002031058100340310082049490208 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 966549262 1250 966548012 966548041
    0x40905071b061a010e1c2909070501080402010804080903070f180606050301080d0809011119090902031e041a01060207090e010903020309010c050c0d030c02010f030c08 74
    0x65a4038165070341d20788000040090050a50059070b00d2076840400021111068886040e00c02081c00d10444880141d40419800380c02070341214049442ca4411404111600e10700c105030702550700511126410359078246610200584100d8003e02c60031000203001c1d4003424a0074420368058640f004250f8036600c940d06140e1203000e0700c1d0f0381401040310100d0b12081912015014044010002224002c160381c18011100e8a401c02c00510009000400c5444000945a1041c1e1194503154069031221503031a03024101090b120800e48002103200c1184458000540540c1407c554038601d2080d50340f80130b54200d1005540d40040d45091106007920082045c071000d030018425650207d010381142d919842110083c0c019400503006004100140012400381e00b0300200303014020084074659a80181d900d11500300024184054104448107001d02484545101000904060707030038102e500d0014141c0c1c180c207508a010640740d07005c0304c48451003272040c0c01c02c07a000c0b0345680307400340c480c1d0702c0f601d1019 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 966550512 1250 966549262 966549271
    0x24030907030221010b010206041e0501061706060108010e040309060e01020a0c08160f23010903080a02060103030305090303090706320408010b03060408040e0a060e190b01090605040905 81
    0x52154410010040c0c07540c080d541c80c5210700c4801d822030a6810240142502c94174801035045600c400305000c04280d0494403400100c004030003a1805058502d0300e0380c05821641d00c82168146419184540d03600c4c040b811600c074180990f42d0043c0c680e00d440050941c41400c1d540a07001951188083c0103182c02400b60000c0b05105004a51100d441130355041c040051941007800240c01483d200c2561030542009900504000c50501007014200345010b420045100d51017000032260a50027107199005a481030013035070308582c2042d51031103400303000b07590303004280300460019240000040203c000801034a006560000203403015900c1c0c614121004012040404983c06010364901855400380d440304064154110429850b02e01c2c00c59030384e084840a01056000380c002c50100000030382140116070582c1ca07150301001950312140030440c02070006410803410441c440d0240280180785411080c040341400809005640321000111070559041c03040401151041c04144a2101c0c16003010343d00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 966551762 1250 966550512 966550531
    0x90607080c0303090d0306080d05190e1c020109120209161206060206040c0803070302030a1b0f051f0b030c09040206090409121403070f050a27050f2403 67
    0x1c14008040c92821036009440000381680010801e00501d50140039910081a509000e0a440a5401806401c51180404880014040240c0c0146050258402078540400500b1074080c00307108045600d45081c0031722099010910a42001540b05005240d50b03054a5016240319115190001028041c0b1201001001413051155840140c4e2a00c0c0c4101001000715030b000f0800f9081c20300340b00f010106103070005911500100a0200400e400104484a2541c0d43c074003010120b03002c0c0d2092802c1101804000c03c4018118010424007000088000b01058a1010703013004c0b1540054400803070f11004440c60301900811050b00e034074506480300382e034030078000780c6020310300060728000038202c500d45c02c03040b20100c0683c880c2c0b4018980c44401444919400101c007442c60409080141c1210f4006400c03c0070070900040c45250380780300c1c010380421401c011040389081d00516001e401c041ea014010305004030006040c0c0c50003842c0180c24010710440345082903c0c400143e0300007141c190f00c0284440b04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 966553012 1250 966551762 966551767
    0x1d0405101428030618050307170c0a0305192307060605060409020301030b0c09030715020f100e0114040b150a0b120f0f040b0109050a06050a0f03120c0809060708 71
    0x410080000b18002c1c000707540302c40c04401d10700311326042c005c95500d190100c0c8240001401c2c600042c41c000b040b50441c907041800000b20f1012154500c0c4a0b11960780050168000d41108808058200d8081c005050402e00a4644000071510072601c0360f81c03c9a003d61034030750742e06401000400c07441c0145400d500414010074002d844102080706540309da441075184c1540040100103200f000011386400c01c541ca001d0740d1402c210400040d0313171000c0901601d410582c005d103c40c210903008010034a50407070300320b0580704441c1c41d0341000c0e07000301714040352103030704e5400c0c04899001e00c0c0744280114071495002000d450562501200071a002410b441800d070040c034031030000714060b00f00b000030704444500c11200816502e0070b10004061058003401da084d03580308030410310001684984810341510350103d00010141d4804e400c100140c022a40425004080d06102184486800b0212404c1e0390142c40140c42c940e69174002140c03000e0b00c104010b042c802d401c2c04001003514089009204241c062101c0c3e50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 966554262 1250 966553012 966553039
    0x70504060e073608060907050603131205090414060a092003060316030506150906010f0e04021902071d01150c06020f04090b100503090c0d0f0f031d04051014 69
    0xf844040c0682006009500c4082082008401000004042e20060346c240d070942c201040e11040912441c40003c000d440032100c43d103031680c4101c059400d42030f8000e009100c6074004040d1170503040b8040d62400d015490300030001c1151240750103a800f100005502c00c008480c5007400c802001d03000540302c04d5250003481e08071034a5031019546400a1409200034040c0b031701706140e1049084596282301c038098503012003000000e07a000b00402103210b40318107141c0f03039180c892000500244554800c0c40d40d10003c0c44a2080b91541c0080c4040a6910314154169110290010245d904000340b1408151501c4603400d0300200d03200702c50241426202c0e0708050b0922039015130003c1c00d9000303070b00450f81d0f155444000c07501501e0004c070422030350882c600740b1301d240d824100c11241e00c81080c48416400382180003040400c110481018a81d1a80c001c4a00c100c5000d003440c0c001d1042d0541d48004440d40624000702c58507142909c501c50281174000040302c012480e083d00c1248442e800c449481e03028151070b0492 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 966555512 1250 966554262 966554357
    0xc0706050106050d06060e0901061d041803021621060f05011202190b032409070c14010605010207180b031c1d09060d0221070504060e07 60
    0x314040c1c00c00c1d440d0a41c68114001800c4120740e80c90340044100b0070100d151400760340700d00f00401e05403205071a12801110403460a001c0c08100d800300c2c0d90700a460040d00c2e205032200300491002d4030707200307500341d03070300307925445a40600718980740a00e200d90703803450b2441101c080f040b40491501511905001c10298200b42002d022a1401d9010075840b94404443e8402c41c0361a069081c5c040340c545112070740d494182080c612803800020328884d2851100d1300d10807140300c440244d031102e0301c90040854000c4e1510040081442030400c0f801c845600e041202d031000c03e20103025004c02e44078181d009009403440c00c482c0020900c00c1680110072155111040350007038505208008140300011000d1880c0390702000002c00f4031011600780200000522850750103a9100d0100a403c0030086980f040851003a00024001207400d4452440039140ca0701c0000212401184d00c1c012200308840c200000307a60740c24081410f000807200d4500080100340560b60700b003032011310040d5942c0b141030603030010403042e52503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 966556762 1250 966555512 966555521
    0x415150c0f121205100b0c0c1f03050c16081c05040c0303110d020304090b0109080703031e030e030d20070b0f15030304141c060e071502150c0706 64
    0x5507842c2c8030600c518035115030003008a20b52442c2d010001c01c01490020b94410b9501032a00452035442d00c0081d04254051080141540304080108a4250b40d60500d5200022110707134a202c00100e4103100005092806290075680d0003100c2c0007102d201e1121640c1e0700c3c210307940645111200c240041008200c01c0e4198030580740300d2442101c220050301e04600b400361082e038880c05460845c3d402a40c210008550200075502110960100071404502050040c2c1300704645412100c114898600700009155103c1c40c88611812108511454482000030880644240c40b8000c0443d6104220200c90358240d035000c12440c1d090003183c0b80500c580312050394070b16404a00b054413260207030414000c9542400c1c0080380c0088421003201c0c4003555220200380c40340194071910030489841513101070300f9120140c5880550b1003040220310800700300d14282c8001d014103202801c5606c00e07440041085201090300d034400b0002c41d001801a001c510030008048000240b80c4020f080c003d1241e400041c080d03014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 966558012 1250 966556762 966556793
    0x41b0b030717090102030702070e131b061b080306060d0b1c060b090105150a0513030303020a020f070e130203010e0109060605032401090c111c0e0415150c 68
    0xc68007907541c10003641c6094102e0152003105140d1040040c49480c80e000220381c8110b9103015615000ca0b51109002c48941910600c06800c000b4240003904250704d000031607800b6200c0f00d80321205191420721990030404200d0030700400355001000803880c20724246020300814070107600e002c40c501745442d02244241d50b0f96210904910b05842c1c039402002000c0c000d040240034240c405000e55851f1800041c1c400000d004590000c140002da00305a080c82a0100c2d040743d4108003012401030b940349802002035120082000c0140103c0041280300307172000c03a4010483e061a415410140c5851099551003417400c00126410f658443d0b10320f008c52401e01501000c41d010362030000d552841c1c035081c542018920035424190282c0c2030b4040c0b81c83d6074101003a0741541c103401000a01100c140c0802e9820030712618000c402481003003403911034140741c103080304031881700b50740e45034243c00d40e0105000c103903203440017004540c07a00c080c000e020380400e6501c1860441003524000740c08020580b00c0c010765012000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 966559262 1250 966558012 966558017
    0xe04110d05010e300909060427081309151701021201030b1b0a0c032a150b0604030809040903030b090f010f05010c02010e2e170601020a0506041b0b0307 67
    0x1540194240c41da11307075030360303191100e40154984424900018881600101064481c80e41c51496503c0503c03170304d0300360700341c4c0300c240300b011461010908020f5500d4000080c0d070340030407000c1e410100e1170300054040ca41501348076510b40302c000c40c2400a20690814051440b0256660a00641603002c0018461034001c60099008042ca810800080400c0040170303000801e848a0401100c001c160b4498442050140c062404d400c00c004d500c000440d0040071902c8900c00484541828400e004202c11a2180203918101c10481c80341070230103106460007644000b6190703101c01e011401c040e08094205104152107403800003072508992001421510301520181c0c0c3d000b400b040180802c2e00300401d004003409090801e00300e49665980001c11050020303100c1c40c01826507500e40c00715000182401054443c1040340d000f400080c070311005194011100b038110210400c0300210f4a40d50001c10290f0004c0e400034041c15095031113454030140b100da101416628154010700002d1510070b22030185028002c00d6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 966560512 1250 966559262 966559303
    0x180a020d141015050304060b130504030509031506031905030d05091c0507080405061e030702010c0206010e01080a031808030403060207050d031419140f0f010e04110d05010e 76
    0x898200c8515102c40d00240751000c40b0b1507080848580210950f580298001d8000c02e0000d074840202e2680da031100303040003071203042c401440201030300540038002443e010b504641030030404142402d6212030a441c0980c054018407000005404901c241e04074050040f0200d03440d00000485990803101c04032030031342c459001102c07407032440254a1407850300c0307140614149040942d1502c0d032210f02d100d580324440c41201c0028611422004891104808184800314141c491602c2c0354068003070040c015140c0010b020b07080c0081001000c120596058030a542d0040c000c10009a60540340d0015905c10004101404540000c03a040c0800003000a940304550260f140c201518000340f07806e608a1100301410b0a003207107c0122603407c010710b83e2100d004203a40c2c00c0d803010180f400c130043c031010380c0940b110001c810800400d0b01060f0140ca0084401310300c8424240e9845084040d080000e417030081959200036080031007031402000c201603450255000003001c82d0034901481c0b82c1900c40600d100c110124 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 966561762 1250 966560512 966560521
    0x101106070e1002071a0a1116150203041503020a180609260a0201050a030f0f052203020c0d03141809010501050a080a0f02070c09061e0302180a020d14 66
    0x1001c0d44200c0d1514a000404c52141014040c0a001c0e2500c0340c48008290046140102c10303110f0b14a242c2c104605a003600c054883c00001442110441c0c066060b404c4000500030380303040d01c0001150f04449500a040c40511000300007140654410140c1d503040108000e05440081003420a54000b0100d80d1600d5890a24083c0400703680030584094140b4981c00d808086051030f43002c0b50051190b03a0928203107964840a0380c040e80203018100640744124600581c8502268a0f94000d9000302c55489a01060300300c107003007512000c440705800a00503000045c0001700c0e42401c40c0403408580c030038240103803104c174114405045504419100124050383c400c40b010a410940301182c058102807a01c130340342617034086003d010b4103000340c015a812940e070340c0e08035071139082c541c19031360b406070310100201e00950740e807100c0005458a40030305000600544c2e105511207140b40008811203030b0141001440300e441c141a490090001003201d00602c0d020400b40c81c000702580705008a0940d00480380c1e20030f041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 966563012 1250 966561762 966561769
    0x4060b040b1203130f140d0348080f0d02040312020133170c04020406080a15030b04020f01021612140106030804120303110d021c06060e101106070e 65
    0x141507010340300403000ca01e4188000e40c0035a07452107206030309480c6640d401f2941d280440e00c100311034517140424481001e20b2880e05041c1c039121130380d070b4110480309241c404c0e929007000020301c09030100802c09402000362110094414003c0c00c1c45400032480142000c0d035030b071501c2da1504290807030310b001030355658100d40182140b203100303026031104602000c9600e9009030400212000500660400c050803480390700d00440200803007150080040d0017551070317964441c40a0141c81c010f0340d8409d070785820203154485074800d03103160004590b04824043d015403034a40a110808414015450443c000d5206034481e90b100c0c4c0320b5040040618128000c440562800c001c90740c89a002d030721007500e9041c2801000400d544000762030036522844c0e058026090f5500e400d070014540f000c0f54504000011402e1480b0700b0890b0f01a109003001000501c08010380c041c1340d00102e603418064940030819125804209041540f120900d040031404c00d1010140780701c00291401100701c81c1c14000404510f0040304a0a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 966564262 1250 966563012 966563047
    0x3200a060512090d0e010c020f1305250219080d0911040c02010203090c1203070c0902030a0c0201150618032f091605070206041701060f0b04050904060b040b1203 71
    0x2e90300c90141c941146100c4e0000c2074003441c150f0302810043c07500000401d56441c40101400c03880300403c1401190f086002c100d020700011152031165049405900c5000c0000c6152208103041a80c043c041c825802200d072150076201c41c6051380c0e0343c3c105210591b100103051042c1c4821178003c0180341d803403000030401c02081e190301980801c02c5900600911801e081c1c001090403040070110341e1030321b0b83ca4400c800546140919800504101034504002410305070035401180a40701103401400001c9100ca0300f6401d84441c840800c0350050503034410004641700e1002c40eaa04a0348007045445140c1e00d84031508101c078001e040715654500c010b00c820188448088001c1401d0080e0303442522440c02d1700002d10060b191308400020300c00002200340841d603800c000c4030094141c0b120700221040e40d52116034000c01850140400c40600301c032010803442540001d90342102e40c001c1c61100796a503250703202e401410508924a80180c0c175007030307601010360b950030105100e02408001951500038443c200080c0b43c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 966565512 1250 966564262 966564271
    0xc170a060e06030304050603040b060105070f0309030210091d060f0312040e0a1e0f020f21010501020303150402090d0602070b0a060f0f060f1e090503240103200a060512 74
    0xd84c41004104010b031550420380754030903000301031020329070703991070058440c0c1c410f00c0f00003800204014019010150400001400e0320b000b84c8180159110340f00c019140742e019030007825041c1000d403582413400000d00e0503660388400e000d004e8105001234580868940710709025580a003400108045c880e07103e00e0750215501c0072480c4c0081c0324160308101c00c4180311140210444d800c0c6d48036180c03041c12084540490390145401440165a400c4200d004000240440d441071000322204000042c0b80d031002082e07a000d019611001c0743c94080c0441040001d601440c0f40541040301d0111700c4000c944a0704c00380c01d8407070085486514503e0148049821620f540e000441130303800c015000d01c1b00d80031000070001603ca071410311402404421809035020300d44070302c02d4000c404419030010b4855501c000c41d03100301d481c150219140e44040034090003403400e9404508264842ea2070040001c143c9100700aa45410307003a140f40c40c07940c4e1050100b00700005039003140000c501c0010345170303106801035401d45901 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 966566762 1250 966565512 966565519
    0x1c020a0614060f0d0309270c020a230c031b210a020f06070615080c010503150114070812011706090c01030b030c0a090b010806031f0c170a060e06 64
    0x240d1600d64001041d00c080410f100f03004d09202c07011142018000c0c0b0b40c5501030460429408070400c1104614030541a1031000f00043c5030070312150140032400028088041640007004410071801c0700600c5250a400401e2844d65125900c5a8a42c648040c4014491000f048a1040754103a17610148040d000e000301c0d4040c1b43c4007520405024858000c03a0244080f17504550314009250a140003031514012000003901c01c600e000c07544496070450400800c200ca1401041d05d000340040e0b0015180340c0400c81d003840d41c01c040b4021038400781d81300d02d0520850f091400b2415040c11030f9070b11102140d400c1039150400da912400c4c018000110741024582c3c0d521303881001032415140c8034100d41e4841100c2520641450b8680c41c605901395802d115541c5041c4016211419203580d0f1008000a8886481802c0c085004280800d056040110b8804c0c2400040c1c038105801015400851000b070540062040810200d0380921804a180c9031005002d1507942c00c0104120f41031061590b60444080d00c018031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 966568012 1250 966566762 966566801
    0x1805010c0807020604030f0f05091008060301061a0702060c030715090c090c050a1d100203030612070b1b0c090408030f0a1a0103020c030f03070519031a09091c020a06 73
    0x296200402c10000032080c48d00c8500002c2000b0203032a1806149402e070750001d111402c13240703545d5010701c40030302c03070003040b4028000c1d240d4440348035010217090106075140d048100050009806c101006180302100c00302281d2908013540c441400304078130214540e2520b51500503040500820190304006032007002c1080008515101c170180492040100000900504c07501c640d0081d00815802e00c80520017130102c640c0c102100c00002e4a17036204460f09807055240c040c3e035007194180003583d0303820740e00a035001c20714000d02d0001c0c07200c0d441c1c3c450101d40f02c0c84c410050424a140c0f0f0f06505207009911409400b910785c204203403480d2400c2801000d4005103441c0000d6001181e80d1103480350b104a00a0800503500c8030303900b484504510804000700d1101e400001800340440d44807009055940c1150b40ca100030b580c8210302102030f84e018030074011240c00300c0c0c41310038042e00d44045025000303000b4808681c9038800081030352440d610704814460242c3c03c419500303001e0052a010300f100c900348541c0b400c030703 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 966569262 1250 966568012 966568021
    0xf020a0b0f2d0d09020a030605280219080a020c0316050114060a0b0703050717040518061302030903070203070618060c02090f04140319030e0a03091401031805010c08070206 76
    0x200700d01039648800b09036526013400d00c095480d074025240207107030405001d1101e45089400200d80005643c0401903002e07801c0c40c0c6000c0b09200f0300c2a2241e000c400c80d4014003440c003919084a848001a00146403503030700304001501c20504100030031440c070000040c0d04074581e80d410506e0860f0301c4007860301e010030701c20030820240e07548070561241a5503000000948070116420300b11524011120f00508800c0100ba07600030306240c19000d00200ea500315170403a513074181d0040d0304480308029540325811644064101800394050b030061036002d13000704122810281c0f2500068a00f21450303000801040015014114020442010b100540b815081ca204083c0b40d9034085220050001c00850001c0b4116001c43c04102003825200070001c5e4200880b0380b41c50f000e907004011001603500b00d1010034544100d107044001c0100d2a00c14058040e00d03000c0d80306141002c0e04040420f006072603410940c0d16070585e19810724040887c503402e03001c1c0300001041c2030055009803941a0107403440c02507500004c2000b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 966570512 1250 966569262 966569347
    0xc1d09071d03070f0503060709060e011b02042c0a05030304080703020a05062d07020307020f012109110901150c0f0b01080303040b06060901020a0f020a0b0f 69
    0x49400405510708007915844403060220155607440400d541401003980005002d40d44480c00025180c04a0a50341c1030b49640c8015603490710984110004100150404a01503000301d020038280262541d1762010194075a0024003243c1000003039100e503026202d11055038444905c0c0d401d612900880041c00120380b940c5945039640002000101800740029510341014400c1c04429682a80310301128902d0600040c055605507400c80000026011415252060302c05010404e0090301c0a8001c1d40c5090116002d0000c0c0c50f119040c424180a403404a01c00d035584885c03090500006240c0f00000c17101001d24001d20709c0d0500100c0c05210300c1d00c1d400180110043e405d50307049065203e0902030750230b0400d0700d44481e06800c0d030040038013a41e081c00300000e00544080010352240340b203490b000e00300e6a0f441040100c82d005000e4400d00590103443c441001840212810341003500052400d2a41951400d0102e0780c0e42c40f0340c02d1044202d40c045400007110801030710580078540b403803840c036a0101103810072 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 966571762 1250 966570512 966570529
    0x203190c120518010e0a0303150303090509040203150c09130b1008090a080f25050601050114040e070905150a0507020f130f02130f080a06050702070b07060c1d 70
    0x9410b42d40e00003080c41c000806003011180e44008000340030000d010406503403244c00c0c41d102500840e04101110703040382c04108491080d240d05403284070001d402c0c042801100ca1000300101d806105050180745130313003050741e00588600070300903c99903501c0c0b1b0141030140c4001048180051182440a406442c1d07030740002041018059140548056079840d03202c6140100710213002d0005040014416001008507004048040030031800083c480040b409a0b044c4256a100240c860740240006008070b603c030b182c0104200e01003280c8141080d031140b8001d04002c0c000c1d41c0c05d2010400401e8100201d0420100307000070f50f810045010700386012280082c000707100f0705000a100b500d04c04034640243d518a011000d2040c000c074020000065160000c2c4002c0d44058184400100c2c800400514000054404029100c400018100340b1760641d540c0700c003400c8045e00d09410750040c4880407800e02440e4014011880c01070001041c0360280b20780c06001e0200344109030840100c03180a0160f903403502d0b1503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 966573012 1250 966571762 966571787
    0x80103050d0e15040b07020103060803031504020f0405180703060e0f01060e0103060308120a0501050a05031002090d020d050a06050a0c0519020115030b010e0106030506030a060b061207030203190c 86
    0xd1465044034042e0009008240900140741d150b04007040101d014a10b040241034042d200303803820400140c0368040b481c0c5e43d001c03c40300c00c0d500d00003648031141039040a80180c56080c1040c041c82c1d0a0030340702d500003144040945a80d00c0781094080410485581c140560001440a8403040403942821480b001001c1d805014900c14032102e482103030074903403203544200c00071034014400c5511000281c003207080050f0f0540d1a1420241401e0010a0344c1c5450756400044950003001000001c0688a0110107900301581c00713644000c0c4d251650015880f280c0300340c403d00d4410000f41015110700e00d0131104031603000c1c0c40d00c0c00007850f00e4401828107400c50101e98601c2c42c100ea0003800c2485a19080703000d8000c4884540c941d041d0144008100001c0c0705999040e10882030b0581d8140e80c035001c00b10300301c2c0e400710380d02070b410fa10a13010200465000e50000102c1800500440c0c5003910404c1c01141c1450280c82a00000303500108229509800150b5024502d000c03000a01c00f111300110b000305190f40948 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 966574262 1250 966573012 966573017
    0x3062412041e1a06011205070e0328020f13050c0c0706030b131d0706021e01020909240d081218100b1903080705160803031305011d07060f080103050d 66
    0x6010130640e07070040400303180403401d54505001514000304010400c40e80d12800f640640300d07003400701c2905114080c1091f541d4050a16894682d899602007000ea40c113440e0301150050700d403085079000b003038190140e680f04040c5120016907450b0704084162501c000d41c3d0051042615042e442c030040e03034801c0c203003016440700080042500c108004000241462025404030300d4894010000307041500404c031920b050b0410080000342030522949142030748100e24903a07030300c1a09d44002800009034103100d0101824100058a501c801d03050100b2803400340900103030f525002c0440c004101e10140d400d0079900112041500c80c20041510010f44d452000c214281d4601340c83c0c0380d82e00541d485843c4114801c582e00078800503601da0344e08140400c2d5120980940310750203889000004d0444002e581300c11190504011031543d83c52608494444250380d8080383c0740d548070706d25408903486038800b280e03071060347c1006401001e10381304000d000b0790031f20b9507807409000c0f501c00104046580403d410485800c0790 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 966575512 1250 966574262 966574313
    0x51b0d11012021070e0102071e1719030302180f03060c030a1e0c0908030a050702010804171219090f1209150306150504050603062412041e 61
    0x100800191103400d242000c164032050020000313802e5121410100419081c0c090350702c00c54650717510944107920740098082c0030a15002c10002d02c6071071416043c400d001c0c40292400c0741d05c2e815540c0342490b9507805c00d0b030000760007007450050040700305450a25058101d81c0700403c40080400300e62924802418151040404000180310700010f801c0745590421000421b06502c890384140c0d002095090f482c000015007007840892000c0000044554542031616280d0800f1995401101e0504000b00219014440c10344030082c1c1701078100c0607060802039941d80345864a40f0120090140000100000780d00c0c0c14500ba48001c241d03140c13081103000d50007050300660310f10310b450244c0d02ea0001d68000602c140c0e481d0014100140d266001e0000c1d9500c14a0081c120340203880e040303a840c0103a02915910100400c04039144d403a180c500e034a0401040c040b1015101c140d600e642c41180c0101d1070710314103000400c042204010ba0011000c902d800d001c4a402540c1c40303140c03104554014403451012280090 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 966576762 1250 966575512 966575527
    0x1061701320a030506090d0207050d060510090603110f010516080f1207050406180510111c03020705011d030a050708090901120210140d020703051b0d110120 69
    0x4558a1104019010340b03038112203541c034030304a03544000440d4918031394094508032113a01880400c8590480b94001c00741a2000f94903102d0000600c009410401c1c40b400d00302c40041d118841c1e0142c100198018465510381060180610045400c0007040c00d042220800c021600446002091044c0da42c0040e0b62580b2079140a02031a0360b0301c203030024044042c007903804105c01c141d400700050085c0c40c51580c0715030700c0c815039a00551a514203030241c142d00c031000c4d00b07200e03100c13030311800f4489080007182c030807038088080315001c0305030724181120035100086c0c0000e00d800c144602401007015001d0060a02d480c1c0403000051243c480c040d0000c0401080400a01c8000303024a03002600c2800400402c1c5c54980d583d01d140d81070041204034001c030b00414411012003140740c010002c1c0c40d0307a020751842c0f2514209420807804001d5011072001c03424000b00b4803080c201d43c0c008140d0f00c694070310800002c140740b00c0c8002010f8514403c00007800c44582c140701124920442c030070342c0c0b4030b00488003026040e01e5005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 966578012 1250 966576762 966576839
    0x160608190b090a021e0c100b01020a0c03290105030a06052805040c0b090a050907050c0303100f21080304060e060f0402010e0f0117040c1d01061701 65
    0x8100c441c1c590100282d001c0c409803102d02d60040260b034080c020050780c14002c07002c040139075000d098aa403010303401000b004000d803030468105405806052041c1c0c2c943c0320444c2e4a034124030661341c105480c90502c0c000b04551000c0c5c076a03504002805100490303055503161400080c2d444804c0e4100600301e540386c10126a000845803141041000401125090103141c032205038028141200d098601c641101d00c001039200107a030454008040241c1a00c002d64203003414040d00b2007024004604205d000c1007a214617190520207540290038291000d10a1803826200c0141890641c020f0340c5501110004541500340c4840308030501940803008640f25913660524500411003410f084226000b00c41c00c014103084500c0802e445a0300c01d0701c5200c0d038201d4160034000190290610140485c261030b88044070044030085165021784982c4ca69006a619032120304403020070010f00100d80903040c8010320001e500003402012520441010600e01d40c503103000d010180c07002c1452014030401c001d001c05100310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 966579262 1250 966578012 966578021
    0x7050607031d010c030c20042408030901120509120a050a0305010b1602010c0809030d180b0324030a080f04031a0f040813030f030c0516060819 63
    0x140091599859564504000c0c044054240b24442000300c20814508950f02441c036121041350035980d414402e109545d180d04850a400c0700d50642c003482c207142000d00355524002c2c000707041401c0c07942d00c5150b05200306202c03010002e60440c1202d42c00034000750340c450364454001d50008104a0b00800e6940360102e189080c401410320090008800041d4480c100c0d4103c001805461699035040003a42c1c0d81e09142e00003070040c019a46022050409403002542c440ca6200300c40501605407246004d041c00c0c0003a20303200c541d0ae01c0d00041141084081d9512030003851520040501c11080392551400c01000241014145800e0120114012a131025074408101c20303080300d1361040342c0d15a5903162042c1c02c9850340043c0300407540b03090240740145845440510550041140281c1850f1645859075490510340180303106060081d0403220001c0454120400396000700e000791a98180a41141880c42c101f511140340019085001078003000030300c1e8020740c40e503488408802141c9446072100300450151 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 966580512 1250 966579262 966579269
    0x7030201020c0d140312070e030c0a091a190302090a0b0d03030c051c0b0a080f07090216150603060e012c03120c03010501020118050309040207060608010e010e0106061704080c07 78
    0x18440070940c011b40300100b0340414003484c0a52582c2c45456a44000c0694612181c074140b6044031160408208003621500b1030703042a18810140049802c40c030340419410882005444a0b075032040b40c0800550070020405d0381c0081c0d07008418400e0380740b04800300e1110f000c1e40c040241016940e92155890a209005640d2002008445501c030042c10703100440140c0300318114144140c9003103c001818003000180558586100d20140022615000d100c10007074000b10038469080440c03924030030010f081101c40c480880f003040305c0007031010700b1400d250741103130900d0f01c004616a14205000103840c1c0a04071080c4035800d606482206041000500e90a41c003d0703000030300c14913421b4014000014500805581610802c2c0c4c002c04c410400c00007615401d40d0600c034040d140760020031066800d030a054000740342043c0030328004910707581d45240031421100302c1c18031008180d540d050413091101c02805070000920b818a0700800100c00000d1940000e00003403c02040c0c0100001c107402d8032102403005d01d008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 966581762 1250 966580512 966580553
    0x403020f0f0409260901080117010204030c0306020309070b04030b0f060126180d1421090c091b09010c05070e01060917210a0e1302180307030201020c0d 67
    0x1081e07545407441040c0713800b1039030200303072111401100c0707036840b8090644480203c1659164040c0e440d00031031065a8503100d800c81581d5400300000300103e10200780010056200d480c0041c1c0d0f034905910780500303101c81d0790480d0802100421080001c250320701045600070088181d84061340e150f401c0103940c03a031104510f610540300643e521100c0380320803aa02c05c1c407031100000417030117507510924540e840d04040e01006c0007003054000319407010340903580500010b816603503c01c3c104155480107000c0b111011a074030043c560096890a0060410303003065904582013840301daa4074821010210303020301134100854108480e400c0354000380710040200b00024a804600c0ca61344d07585404005010031914002e81d0324180b07152007540d03e0704400041c45400c00c203640c4040b00c0004005030316046180d00181c800002c1003291811401c055071090802c48641900d11801030790742d03a9140c1000c171004625009540f10350400d2001b040580d170042118809000f0858003a003450740c8614015501a0b1020b105005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 966583012 1250 966581762 966581771
    0x2091302040f0209040501050411071e1506090e0f1f09080406050c0f0313050607051507111603020f06090612161209170a0509040f060f0e0c0403020f0f04 68
    0x50b41d04455000707040c004000c0d1024000c5a0b254401d10095075190b1020216940b01007001c2c40119038007500805102c0480c400c1151100c800d511000908101600c0481e04544e440c5404c01295800d07204d20f500d031100c1980074007100405104495100e20b2030286107070556a50803903410114107258806224503078401e5640361181d0320f4030780003040341e00301d9031504800e4803401e43c9030074106000100747ea044007804180741d52500e00300014009180c205030400c451502c100600104414405510716119681c01e0740d4004003811203905540c50007046910700451f060000c01e00b8009070301d45170400380d4011001e0f101c1903034802450300450524459040078100101c0c2182c20b10040c00d08405286240250580d81c4030403a9140c07951b081d01316818400700600f0800400c0702e001c20520b04c90046d22500450b41412810241007130003180c255038440340010003c0d5552a018812402c1c01052000030f00356040400f42e0501d40b41200800a104a0001a114078141041d030a030030743e50390b030300554000e8001d0002d02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 966584262 1250 966583012 966583031
    0x1e03121101020d02030a0b1c02040b0103020f0d0b10210510050306010e0f0a0b03031605010605190509010801020a12020d060f0b0c010507050a0e01110f030c0f21070209130204 77
    0x317420175103140c0840d41c00d042c20b10b005890400035940100134030301c010344030104080c1d08000c001c10300d030b401d10742c141a001d10500d041006c5085c05401c0314000c41d01c000c5003909200c4100151914030281d030320180b200d1020030454a05030300000300301036802060005040c0c3c9441e400681c10b401c91358040c2d03a06100d81000032130b14038081c06203070b400b804502c4000145610392141c5002034480ba400e0284d0940d00c20321110500c078091390382c0c9040d401d01420002070300544900200d00703c1c0a140315050046401040100003e0900c00b0701d80e40142038502c0210300301075205900505a0418030907880040750003013036284810042d41d200c3e0008145100c0b001c20744694541030341186800504400205500c0e1600242a0034042c2c011106100c02da40e40302103a01c204100152020b1004000038902485810004119076804000418540b03124400800c2d0007814a910540b501c0f50360b6030100d400b8607628084580a01d81682603e003800e90403203402c210b036a90b0006c41075080240c110040d50007800d09000d107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 966585512 1250 966584262 966584287
    0x412030518101407021207060507141507212a03060803030109020d15330806040c2f07050901050906040b01050c01090b0601091e0312110102 62
    0x1086001c40d003140c80c501d5070503844100000740c40c42c41040300128480c88a0004080b45070380040c0900e5100801d01031020300da1030840e40c0f130440c0b1604010041200000d4900512000304450090b003d405802410810360170144290000d0000d061881849110a90000d1540018421800f0300260311000c1290300d811904100784516415071568401203c50010009a0b103e0b0044000740c6144000541c40c5900c2c04000000075400304141400e080d64a090742e030740c07042d030003680e640082c00ca103041910b6020041c5250250780030544110a072402c0403030307183d840641d002502564402e8044800180841040f0b00030388500b0102c003d041d41410b06182945c22007184000e2090461140000700d4680c55141d03414000454428050182c1c80f10070131002903124607082e04446d40d81c400c18500107042c06412128603084d242d40590803906078116400708882564485000c5005000c00c003c0d40b86890181c10240c100f1942d0382c00040c0141415001c403c880500420000c4102400315000715590184012407 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 966586762 1250 966585512 966585517
    0x201303020108060402340f0f022734020a030f020d2c060726270102011503080403050705060c150a0b120f12030c180604120305 56
    0xc074040b41200000c6846401c1c14802d030340c1191500748140c00c8450301c48020410280f6030b443c100c4031884002164038002800350080c50301e458814115103070190135910401000e0500001010346e0800320460310444a29810310164005050f1600e030340181800b00401500441015401e20000c810410040740070f42c2c0c00a0540340300750007503440c0364907a01e803124202d0f2502101003041c030004801d801000540607a100509403420f0000918020340c51844001c0780e0941c1241d03006441c2861115154404000303681c418405500c6904a030a20f0607942807a00301c80c20342c01c0156007540c03001c240c44d0410964000d5000503021000420080c3c41039690740740c6802554041d0000721000e00840c2800100c0c0d0414106840700c0c00b0f90a005081542d010500d4544843c1c0000c1c1488091a103c1e040342c1c426844101750300016649100c05010002c90a040790740c54064110035690350790b5001c10410071a42101e4040c4c881e01e09428454110441d85e50001036202c2c02940c010100c001031801020f010180c00000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 966588012 1250 966586762 966586769
    0x303020d120b0d1b030501050c0703020f0102090d0816050102030a0c2606090c0909070f031503030815010c06020c0105011706060d1104020d0c020313050a0510032013 73
    0x8692030801220103422041d903010348802500142400308040004072000c1c08050300c111341c3c0e815221482e50344e0303e610f4250f540a643e030314900200066582c0905a06012808021490300000e500c3d00c0010030204441c18070144001c2c102000104000c1d044c0c0508507a0303011090341080c000d54407400c083c8080001004c3e00c0c408070000c02c642041515020b420300324050400d4402441c8503505d0b076551001e200602c500100305070007010b410000341c1d0702c0c0ea070340c50310841c012091643c4100d045041404040c0845d03c004103a0000740095400070800030341d0010389254400094a107014008101e80c2c0180e9056040704801460312303002103001c1c98100e2055101604880c1c008402c114020000002962200780c140c418030781203136400e80d084004c01c10666061400b890080c0005260482c0420b4410840e18141340c008010f80002500940e411480d2840c040903080c01c84001101601e410000b4800205451a64041c540c0307540301c004021001460f190350590b052010f061361182944c0c0500600b064030300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 966589262 1250 966588012 966588017
    0x30a0602090a0906150503040201121b03061d01170a050111180a03110f0d12030608061f05100221030f16121a0d06020c10020f070326010303020d 64
    0x540003c0ca00c2050300480d41101d03551001c02900c0d4840c1141100c0940c4010020781c188202c804800065003124420381c01c000c0200f002480318103040030001019206030303a000010407000c2d80c3c400c0403950046011a411529031018002480141c452201d00301500c40c007010348503500e030050300b0243c610002c006010321220041e40b00f030b490fa00c501c04c0003181040c0e400003034990140c41000850b507041c89800d03104441d40042040d01c000d0440d5070342d01505105003504200198440c0d0080000c170700104405500302d00890344803031041074402040000a440c1d80301d064403400303a00341e00c541641d00078049400002e600f40c200c1c5850104900b01c42075543d1056a0100d520895200092215402084040107003289030361a001c0100d410810070001d080408008584000d00c070700300c4110350f0b8480b414210124403840e00580c440d4940940d090901501c6400364050034010003244600303540c08000c403509281d050070b10800414202480b9100001c1d0200030b1300c1d05054120001c03050680004214000b12a00d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 966590512 1250 966589262 966589279
    0x320408010609020c03040e04050709050703020a1205011202090c12090a050c030114040f230a05010b0613150309051b0910030c06051c14090f061501050c0c030a060209 73
    0x444402e001c074403030303062004141d40040c00140030200c801010079401078015070072039000c1a00c0381d00f00c80c00c8131000ea80040102c0ea0000d03035541c0881d04000303400c11104466108010075850045803907400d28030844004d10501c05800000c1ca040c4400040d1000268046140c555900c2c0c81800301703075504032243c03040d280c82c45101e26843c4189014050a94101c3c2020b031060b1a0f034a955031a4a4001000c4404503103070404e0030095480218106200c10f008070002004100002c00ca080c0b540c00c452a204c0c00c64001d510070407d484804110501500488080c5c581c43d2169849810044008010b003050080c034501480c243c2d2800d206040319003404010046035151110344510141600f80c071040c1c4801400015201c00c2004058015806808a10f0a5003000b003407000c400440c00c001c80d4158a14481c600c4840018400e000404000d55400b0020002c02410107040850700d00701c05880d0310460710b04000000408441c0d6810500000410301d4019084a00c00c190b645040e134040d40005510340c0c020f46a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 966591762 1250 966590512 966590519
    0x80403150519021c0f021306021b0105031f09051b180f04021b03040303020c10080f1e0702100b0409030c120e0303030406050f0601030204080d3204080106 68
    0x110301c00c0c2401280005050580c181c89444110007035005214006a104103080071042862001d005800010310f00d1840140d64484507c5483d1192a80c0c5d0449000c561005507003042c41c45100d0310300a002002400c0080c2c50340d9130a542c1c10404005440b02c906040d805801c0018040c5540d0070407400344111005000e0940f08001c1c0c0710425029011141c0b40640c52070010345080c1c00c00701c0349849644005003015150101d82c1c161413801c3c0c040022002c056910004007001455810310160008010440f40349104070b02e5984000c0c98103401401606e00c0e8500703000881e100c204299084001010050f80c40c1e000c514050601a443e1071a080032120014181081c4a0051901c2e1003940d4005925441c2c9030059425500da80d4a203224101560b0103020005d40b0455107a5030801c003035840340c0c0c840d400100b4245010007010050305000761241c0e060600520080c494000e0208102c1400742e1300e0325107203001442c0c443d05000d09030045800064041d072000041060140142c00800544400030024040310780d6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 966593012 1250 966591762 966591803
    0x702060601081501030c1101060b09040b06040501121812110c010f0f0305190908071a01030c2d060e0f10051b010204092904110904021308060103080403 67
    0x72503902059503d4660214003942c001d50000030b46580c540350019141d180042010708444c01a04801009800801c905ca400e180c04d00544414000039901181410b02c0c140010780394001088040c0c4036552070b200b122024424400301d0400c407a03007056415001840d44035024046402148060300340c0e0240842d48012035015440c401d95604440d03403040341541446104500a040c0506291031340e00d5007120300707074011009001d05425580541425030751000c1c649414240604501e400e0800c40900c04010004650f80b010301c10200c9602c14402143c0e0204480b183c007040d82508003900810f00382c20008100168400b00e000034029092340d418501d0f003039242c1080303288c032416181c01c00040e20070070550240d0208410b64030300340d40c41140098106074a8558200c2500c607101c058038140b12100352402000382454610600544040d01c00b0000b8561301020305c9010311940b00c9044c0a185c0000d0b00a01c86401d060703e4030014030041d01039500e00e50b1070303203003495880d480361000b507480d2107040c2401e0603410f5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 966594262 1250 966593012 966593027
    0x7081305090708010b0d2a2012040e060f040905240603030d0b010909060602011a10020d1b08030a1a01050a0f0e011e0e0109080309010e0d020f06120702060601 70
    0x80b8900e0f8800c0c140540c001404010b44540c005501f042c080007100c1c25030480c4000c0c03241121000d41e44444d59482865000800b030804030420300e10740c56101e42044045440700104035070950307003070002c0241c1d550b4a481c04030b00320840d50411990414a0842582c1c140100840e032060b180c640300d2605400e501000f40880f0301d200055491540c140c07c2004204004619a400554208030604144007140e035070320028400c503080c50303000c100540d444404544080c01829070058043d401104c5111840d688000001c0d40c40c00d028448800340203511980030021034180d2600c1c1d4a059000d80495684d1400100031006022003c020748490803a00d280d81e62150b002d030303098441180e1f840c3e0300e03007420fa0112401110105100c0d003105051082d607025901b12140008684d420032003403130320b42e03070710300b0720018001001a5081e034420b20194105000200450f85c0c005001031005000b110360a0f2074416500000341900382903010554403000000320411800080e14400f4440d86440c0c00fa2041c0b036480800540760399 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 966595512 1250 966594262 966594269
    0x30219061202030901060812030a0b0607120305060a12030203041503090807080304020d0b04030c020907110c040f0e0d02060103060f090b0106030c18170714240708130509070801 78
    0x24091400c2004074225550103180d0200b1800300115040d0360307544041d400d0180d4512503e03081c010010400c9000030450141480701e01007520007501c0c144c0c00b9102d0340b00907088014164201901d4102003810b690712400307140081c0c0310111002d45030038140e160296503a4403501c1800230301001194140d40340c600a100c3d01c4003858101c45258605080d560341d1400d141d0004004a91101c60114000007240091030a5441603200344c4070074000f420540100864824001c00c00000c2051500600f0a81d10020a40c0050800142d0300460f0034406a207440c07015011681c101c180340d00c18404244d0615a0001e0640d040b24087c0104002e807840e500009803c1d5890040054040320398240104203030b5220358411140303094146014640c8103a2103100c8000350019a01c0103810784103000358080580e50502031040101030b003003640b0343c02e86140c001207886001c2c80c1c0080480d0030391303041100c10740024a2086400080d0702420142e51803466071102c80c55180b45001d403038080c401110020742141d003d032465034144d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 966596762 1250 966595512 966595517
    0x406120e030315150d14011d160e01050702060f040e09011506050306011101090b1e090a080a2a1202010b0a0504050a0b060301031119060c020114040e04060603021906 73
    0x918160060080510712104003004400040005c0c40c681d070711501c03030406081c000f1402510350794901181e9001c0344407004822030091a04109004030110064141c0400c142541000780a030030000005840380d010341c0c400070750070000018124500d4500c0e41c006005995544102000544882003001e0882d04160b00450088060300c00501501d40998091603103d10145480b00302c8200e1840818250b400325401100c0413030101044c48442c5031405002d4a040c00d402c3c448441f58601210300640d18201c0017405080b03c000040c04504c0a0f01c100350610220018040c0125101104103240701c07203d03002203040e07503428800400060558818000c0320001d4000500e00e040281c00c01c0100f00003084003070035a0f00804d0b80c81e0006025902e94201560007580103402007030012203068240070340c01c02c400c10005402d580411003401040e4101c000d46052540a13f421030308a4821403234070f40144200e030401c44d00e02140b002040200449500f011059a1094807484191441c181044001c1c0040e4000d1501 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 966598012 1250 966596762 966596791
    0x609091a0708010e040b0a022511010c050703060209060705070e011508190c0302091032071509020d15060905010f0b1e0304151a0607021003060b0406120e0303 70
    0x11484001d006c98105884900040c608100f51880c000080440f44107404980d001038012401d0090006016003140d00030b003480c03011380a01d6901c9546a807501d000c000e04207071b404110349000f500c68200f82e402491707101003140c2c012501c950802d039a55a0034030600c40d1034019101c0c01341145215141560040d031014624030111110110041d028000682442c0101607080c0860a03080c0d0b100c1504c040b60300256110761281e924224001d0b680394081b0031100100000c1d030b600c00c401108900d4101c0b0026a0080746031040140c442d03503824041c100c0342001030345c07080c8511220000c1c041200e003081d0501100c00c1c0c0405c115952591150144e0300c09100740240516680010040604030701e008025000d0800741119906840c0140104181c0055a045e00c0e91014444504504021442004203c0f58a01c40c0c024101d404070000802e80d21591a0003030003020140c42c504070340c0c0d0098211078040c0c100b40d090652959280c13080208110f84c0c00c2c01c104082c5d4180400c007040e51001100b240c0c0500d0200c050001b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 966599262 1250 966598012 966598021
    0x1060c0b06121002030a1a030a0804120c05040504030302092e0c02120f160605070c060507060e06010602030d060f0e010911040e100510080f0610030609091a0708010e 73
    0x101c1880d4080c80c807142da0280b0211050004440d100940c0b042d0440b1500148140e000d0510030094041102803901903804680c1c0d00d00850190b0382518221350703041224446040c403910380265401525030180d504103051105210070542c0580240140140548a445503004080492061940c2c454040e5044c40642c16200300018456003061114030b0000d007007103c030b28020a201510341000420303148000d421030105184d000390310892200050210f4584141460000c0e140c0316600443e80c440c40c41440b40010711070042041d41d411802c00a84404107a40b099a900e91003e9280c0e4800798640f0702c4c4515016020401d074480311452001d4501d0341644800503802c003690b203c01001c0e840600010180240030000d60740160500203031280303058400900a607403620040c0850208151022001c1c04950030070000056096101d41d40e0060302269507180e000042d107410b0300144503a42021544500705160300c0d05220040064600e000d40d0038107000007540d181c84003190341c910f0a01400c08150394403000315 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 966600512 1250 966599262 966599269
    0x901050f01021515091303020727090b04031407170d0b0901060207030302060c0306240c0d051201090203090a0807240e0c1905120a0f0b0f01060c0b06 66
    0x291110041c0101c0382c40c0f8001880b20b0401600407180386040081e042c03021030f00c0b070400483e140c0d001424103440521045440e40c019448500340d00401c504801484800c002c20702c1648000781240e86d540f0300402940303502e4100045e800404850503004141c0302909101c40100d84011600d00ba03802c4115486542d10000600c1c0c0241d005a0350269040c2d20340b0341442c4c1540c3c92403a4a0300908464004020541c40c5280290422a00400c1d81403a440148200007068a50800b4004401d07103104c2190411528500180898017961030300501a2140950036400550402c00030951850020303100d245c160707600c0080b0742c141c3c4021190180340e90072501d81c250010b400e1401520342c2c24402e51002e81d40100203003112240015040a0720425521481000354801050007442c501180035030b02e255019800008001c124201d620895008403003801c4003141940d418402c0103c0315038040c001c0d9024007180d09140d200d566050300c003044558a458000104a0700800b84080802c2c0d207d126014155105001c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 966601762 1250 966600512 966600529
    0xf070515031b03090607020d09211a0c041a040b090112021c1d1612030909020f07020109140f220e0f010c081b031017150c09090105 58
    0x44100d68014041090703a00b500d0000b440c0705981000c010045803504c4013000749041c81206e070f1401400007072101803215032a4003c02140c100e41840300310303050344560301d05000c100e2410500003e030083da003401d0240484641d0002c04c00c840b13076100e84590001040940d0340252280703124907490b095007000381d0001940039080c0304000f6003000e9001428004130038130200c03241c018905c4400f68160759840107210f89080042c041031800208005120300c0107a00826820100c0c00d019102500102e01c0904040502c500140400f9010207681551200c51084920f01542c000c250100e011500111002c100035601e10007600c0100070061800754608192414003a00c6070b00151441c00d00d2510181e00300301c00d0054003504140f11720103c002c1807002d41d0b01e501c160031100164018003c00c101c04c001d20004058043e0045d040b03018404110395640c48510210040e451283d00010100d400d5008884e4417220100b00002c0e100520580c11443d03598006d0500d803188034010b40190b00420000040c000340c01c01440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 966603012 1250 966601762 966601771
    0x516021506010c0f061104051c020901092408070609060f02030409201b0d0311190c050f030406081302011e02160915150804170702040e0606030f07051503 68
    0xe440f01020b945c880d4420f540c041c1c50302c03040da04030000301040b140c18009002a510507040d100501c4007445030f80091081801072281c2050349131602c1d004054a12441140780f22181c16440000500b6521a000c0d62100810310440e808585070403070003d0380728000d9022085a0a556015502e450304141362440100411070022a404845150000b0808610001400c4454a40880d44105c40c5103408883c40d000c20b0208030401c0600f00705070030b44064420001c0c1d440744034220800700340262030b12004460306031083d04042e10300c0c4141100181d2082c4081700510955605070350303e00503a600e0080302002d00d41d2030100240096902c040640d4884040074400e8180742070781c4140d9001440000c2c041042c4087d07a001200500c2d42c0303c00c426640c102c801d401e503005240c403c0c0358440f000e080410103003c403080100007425009919080c2c2e440f031001c0b6030071103020a50091003001004800b440040d5a01c0d408c8420901a10841c50310b003c401100081202c200c0d41c00a104400c1c03041c480300a80340360b410151 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 966604262 1250 966603012 966603023
    0x3061f1e0b040806062b020d060e0706050a0815060d0903030b060f04061701050a0e07020a020d0605040308100f090e190803041217070c08090d05010516021506010c 72
    0x24041160703803120004000501403903008001030b0920000b04645460700c03040395224103103118480039201501c4605002c40d0344d01101d04a2003003140f810418042c081800d00c00c4400c2c001e6400c045040703070700031020708a04d002e0ba99035407a0503502e0901415418416048095005506005a125500840e040413a00c0c074803d140214440802802107005500301f90703d10880a607010805011450b4040b1000b0440c1c000820040b0041d41b50a01194100c035843c0215020102c1103800200030a0082008038551680501207800080e05410060001d29068508030000b94860740402c40500e120442041518070f000082c9050ba0310b491484c3c0002c0207401801419406003960180a01840901e141d100d6409400340c240d99103010310300a0281880620311105100ba1980e108040113030042403164003860905140c0000e00345420078803001c0c0100c24103983d010250340424405c1000641209015030700d0341810b080041c20743c10040e43c503032000d02d80d95038801c1c064800203805980f15000c2c1080050144 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 966605512 1250 966604262 966604319
    0x402130b18070f02010c090e070507050331330c0803040c030c06080c0706110d05091501050402070b152403061005041d06060408011a03061f 62
    0x1646500020002200c034800403a83c9007150b03001182d028050304003588420325001411505201d900b11b03841401405000030002c011403160704009040003110000354144441c82910240098102c17840340000440015296009034000342c1090008850b01d4001c017101810801d80c0032810000140c18505100841002001034291010812150042d07001e50300070441040000d00758280420725042d00d51003072040028183c104030f0741005940030b075450300303500c410041141000001815440c1c003440c0e800031000b91078001401035000c800103041011000b204064000c580e60355040008900070004042d0a01900c0b4001440aa4083d00e06180c6048010043d074003031780c6819000410b10810203072112400000000703200d40c516201444480e01111460000c0c9001c0c1050510645900c00041d0483c0358892000400d00981e40d20b41500e0140080d2002081560300702c0401a14903180e0b103115602a0040f036001c02c0381403140714258200d040c00d070348001248615110103d0b9540e2801c03505564052802d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 966606762 1250 966605512 966605539
    0x40b1e280602010516020d02120c12030c0c0106140a0504020c1015030c140607030e0409120315050901120803070314040308090d020f0d0509031009060c170402130b 72
    0xd0100000c0e10840e40009540e26054980d0494641005164000d5500c458000019036a00042c05454101c2407814039856007103010540d032820303560400707094400c0000f00c10090114841c0d0040c1c102641080000d018142d5106030090034210904581504005400014003a0741072076001410140904021100c12568140910f4122011300d1000e40f13100c03109181c104140104c0d4a20302c000340842c01d07104c8000d60340750000036401f4400ea1400600f03100d43c1003052401030740c6079802203203460341001402c2400d011041c4014004c210070b82c5440f138880040e034008150750801c1c4d4002416204901400d2070780d80000d8540402c0ca401c000d0100c41016200c0040b10404a84605240d018520a4985960300d040c0b0507441801c240e0114030a17421035011959a41c6800000207840321000c2950a000d44c0d140780f1280032a042c0412004074a01050620f8200400c200042d44400c410103116a1440c1d081001c0703110b00182c2120940d0046e6202007851140103150500e940412040c0c500108040800c80b2f6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 966608012 1250 966606762 966606829
    0xe0304050a030c0e0708160f0c0b09062410030e030f0412170a0207090b0609041b02010c020a15021b0105070207140a0f1202031609020405040b1e 64
    0x400b40c00c111208569150108030b6005980a15900074000341080c4a043c03030152000d0a84141d1580808104003041184010160107001d4610220703070025a007511a2400e04860b5681e07000a07102c1c2d001c0088458440d412074401d0901c40040164010b100060f00f0500341822409010b00c1841107105000c100800d090201004009100134a949600c201461030b80b030800003501550341d40d5882240d4000c10403c14420346c04039000d425a521890005801c2c41d285d40032525070b008a070034140e0064a41903408501e003641c90801440c5c204103030f0003445112903126040b030f1a86400c1c1401040c64056045c090003c0901c0e4018000360018120180d0b010400003051a0030f50384251038210143c5c01403d401d01c030009052036000c075031442c15111201500c3c5000c1d0180003c070000d104151aa151100c6800110340d021300034900140d0994101e032001c140c94100c050000d45c824840c440c072451819100c0400d44c1026010300d803260f802d070a440e07540006030a0600950b0102e01400701100742d40e00070181c9400e01c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 966609262 1250 966608012 966608029
    0x11040602010c0311030705030406090309080f06090106120b0109020d091a041106180904020402130312110a0309050f0102150a0f060b040806070c0c03050105070f0201051807090e030405 81
    0x2150354000704603120000d801030b080390018080c2c41d440442c2041001038440e0440308507130300913074445400103c80e402400d0031111022540c104075540d010b0049019410100001c040380681e102800810444d41d0b19004408210b991203002000040a100104600d020550107042c2c0d0510007000800e460394280e848c2908415021103400c01110b500042c0b0080c0035204501602102060360b01da440c02c24090719a880c40c11010441c144a0015500003a04548451701039807804204600300c802c1094580c54541c1c245400c402a01d000168003540c859100000003825460f969095210701710a14200014810450010301009e070540c0b05d8686401c49042c1a546071301d01c91a8103030f50016441d285480c50f4030035100d00798804001c0c0340c000d1006108038600440c141e5006078207810801d4884485103008850001141d002a0030755180c54100010983c00205000d2404d0a588c001c01040e0742d000c402095151509002e0303070450380513100902002c2c42c1640208840886441140c1c2040d5840000071080e1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 966610512 1250 966609262 966609269
    0x1080f130f15200d111b060103020111011112060d020d060c030e030c1203130f0606171b09130c0f030204110c0d0302030c1c0e06090d05030c0d1104 65
    0x60070980d440c50384510ba14402ea0303010309100007104914040206100380035025203031100301c0480c1e4401d4040081d82c0e442040301d040714079050f11980101000500542c6035082484140d001c00c0e04104240741805041c4645c0d0f04840340031801da410100160390188140300c00410094121a005410708050380d15405c600000301d01c107590201c0c41c092815801800d9480752152184c40303601c180641a03000c00b004c42c42841490301242c3c441d480c1d40d200b03902550722514400c000340541c40343c0503100c800c0c080380740c0082d0141c5444c0c1410989403038200c14050381d101c182c00d0f041e05440c07800e00524241888c0c2050744a800404074201c091010318203460320342c2c401040c0e5014950300e800306041082141000d0080d1180d030076007c0c0c90b0070b0803d48034030500c945400014260728100750f070000020301d90140c0b40c2c0540c0d441225211489590b01c00b082c003264000d0608074241c80280c85200002218204006014058013a803036940900b5a220501a403100d034020700d90090303402d52240b10010003508402e0150006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 966611762 1250 966610512 966610523
    0x305030c070323060c030603010902060d092306160201270b0f0f0a0203040c030b0c07110f03030708090310180b160c030f0c060c12060b070201080f130f 67
    0x90301e1441c0307498a580c1c24282c0500c81445504400c60f40401c1020940650210141840341d941e9034801001a005121404000b94000030211b54084095101e500400100380302e22503000080361001d900c154907034010714560312960f005000149045640036104080d90b00d85000100d407000840d10802c1140351407070008251107210325040020301460002c40c88d000104203030501403e04000c1d510420000b0f00900d8841d000b40c000010500700182500d02100541d044500b01c00036041a0241d0700380c583c4107041c20b5401440c40300401c581c0346001010b840003200d0080056290000c50340e01c07045190840340300c1c2d642c0340c081c41540e180c606100380100c1100c59491248409264000d1614483c2105c01034070710a0340b80c01c45025140318581023880075003060b0301400e0005c00da04c1d55103001c44541061500081c1150f003080030307a81000d5004106500000c003020000e1147e6501c90264030001d01030070740080d00240368000805c03141d0000c2005250058400303001c01442090b00c3d1034400f11500c1c444400c498 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 966613012 1250 966611762 966611773
    0xd080d09081b01111614070b03010b0903010b0a0b0d0906090c03050706020d080f070c0f21020706020307120c020a081b1206090a06020d0209121b0d1a100305030c 71
    0x41004e1245400028103401114201000da000c0504501d4100c2d0005001d00c22500301c00300d059100b00010700040c000e2154555a030360311900e1a041503001541458043e6003403580c1900f0b60325008182c001a030b00d4021000c0e06101ca001090005889101c0040e035905555424070000720f41e0010260014500850081004c00d01c0c2c00750080c60132004000c00810020070409000641c0c10740324800350003005c0c6d46000802c41407181000c084030142034800410a00701d03440c079078004070214404840d0205540d0207031104541c0d00d07002039840b40304480e401031103200c8901541440c6030150f4080b848550000d0140041142ca820380c061400b50382c401a09660b80380d000010210b480c040350b40c00840300108003d0641814035400086d03540b80e840100801c0150042441400307513020703070b0541d900880001c04e01e181503c3c11120345512404c051801103100c10f443c0b0750b03090b00390408ea4694860b060344406405818861080ea03500105c00181c9035500141c1e07207031400404071b00308001400000614202504 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 966614262 1250 966613012 966613057
    0x2031b061c23040b060108060f1c1214041a1308060105130c1d0f19030b07090e04030e130c0503090607090b0901030509010b0612011a04050d080d0908 66
    0x142e200882d40d081005400400100000a220282c140e5040300d401c0c02c01050036181c4600060030036615030241c035000860840f03481c40041969280590321405104041248200d040c01100d40f000002004543c1110421042221703815440e40301c1501c0421304030407400c08020f8250000086101e500041c2558040c10050003035103840c1c0650410b0014101e800c000e5842c43c02c1c409420b0b03150618202e102d0010b02e12402c0560346416440c1903010100501c011030341d5400c044034040d000014001600c18100c0500047c103d6030040000328262820640502600d640da40d6040740c1c1c001100c42596007000b0b0150b030300440b0410034007071a04460a141c803415200d18101821070300d0220300414450400c10311040410500700c64504603011010203280110b925036404520341e026003220070f2943c0d009080041c1040820425121250580310144911502c150700302c050300380c11703000302d000c2d141e88101f42959500014003044010601105905e60114403c0706a80740e01c1c9643e0010f06440301001184440341 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 966615512 1250 966614262 966614291
    0x60b0309190b010608040606080d1d04140412020109080a1e090e0a0b06040509071701240804050c090727031520130905090a02031b061c 60
    0x1c9100d0054604241c00da00c095120340d10503800620909040c08105808201409403d401403806045004100c4041d9002e112000780555143c41c42480366840c2c00500d000e640c94a0701030b0450912903034230b90070401e4891f42c03124110041c0759882c0206566a8850500000d065040034001c002c030710b40c540480303400b0651140803503140040302800800103005018084880b9003440700d500808956000144003c81d40c000c10042d01c1a41c0105a10080c04c104002155034003c507030080c40000307444d405807640d076075500e030784007040b1100500c50003852641400262148500e0170141e11500400c101c0b48101407410120b001950140d5155000a021801c8181d4160380910709800381d150b050703040c250703061070340d16241d8203101280b030186103841d1107006061007a25000152065461503052403680c1d00f586415103417420800c0d1281c007480505080002c0c1440784081105421180c02801402e01c001c145000720310402d02607101079512070b00500849010044640010180c011882e40015800c00d0101e0322 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 966616762 1250 966615512 966615523
    0xd0c0c0b07030213090c020c03031227070506090109120f03030c0203040b0712091d19090302030919080a050a11030109020d08030402270f0703020f0703140904060b0309 74
    0x4407000d02d40100408404402c2d0642081c1c100c0300301140006840c10811000c030b040c12402200b550749448003180c118407076403070004e09500071010300e20580c6e00a45100d8070904040d5001c090100b642d001160204103904154005240c60007051500350501e580301ca440c40b4042c002103106450300c8600b41410402c1581510034804802d401d0b0008504051908054110500c80d04000030b1201c802000805460380c000c1d100003002d0442d0120030030703a0850014403e09040ca04440d003450340480c0c4a40307243c00c1c5045109030500182c00d40d0166242030307900d005100c1541240032407081c10400c042000603683d44107100b00d6010610540260400c899035060003c403c82c1d500f20058440e9150803207800040c0c0e1002d0320314424a50044045e0303240d540c1e03400021603082624502a01501009042045031017810440901c1400850f506028546600760114201e000707548a045250f44100800ba02082c050800032143d10076400107249098440e60200e42540c9032a40400c1c000d010100900a591009001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 966618012 1250 966616762 966616771
    0x606050a02011410140d060c0c0c050904020604030b0603070b041503140114091906030609050114150d2d030224070305090f0d08070e011e03050601050d0c0c0b 70
    0xe0300312981002d072940041340441e44030f444150020303141c1062607a191001c050401c1c0360003000810090030580310141529403610f1040f00c0c0e04041e42d90100c4c95282518890780201c0d000b41074242014110b80d142c00c2e21050251440398144a20304002902c055180002c0000e0702c1100d0401003481c1c1e5418001d804e4a040e1880303030740c0840c803820040c009400c10882d2040300d040c003141c0038a441e45501c9042402c90b04500c04030191203060410200c1804042d41007050800e118000803c00c60102d40b5420800c2c0c00181c8083d900d042001c0c100380035a1610242c0000050301030382c990480c1c40042400c00640791010040c0c00640c0c0010505242030540511407074001205d19000d00440307611401c00d600300f5800c000c140405160341e4201003488090204000f103440c90011084510b4405540d00140c410170b412a0190001096409948815441244020725114800c00c00413000500800c094001d032000804641c104a010f224445e0710480e0780c02400f14041c82c0b61564000b28229040c004110b810040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 966619262 1250 966618012 966618041
    0x114010821071509020a0f060207153b04053c07030c030905030d0f0516020a0b040302010b0a150e180f1923010909030219060b040606050a0201 63
    0xc007060106040800f202d0b40d0414800c000580640d5910000d902580e0755000002050003041c40851095000100d403c1900c60f064052910f000d81d14400326030416404043d0f100001c008002e0012030001498648881184418111103180b18034011038101d90040310038070481404141c0d90611071012003410250054030007080481004050088d940c0404c02030030040400d5510415991994440d50111040c4d1f41d0000a890b5514180c594120203088542c1c0c910446030b203010041094140200541580c0800c541c01514001c1c10303e885159030004002c106401b07654a03081c071004940c0c0c3d04084c1c0c1d40600203603041480440c41c850802041131640f0010300d03010f84c0b11040c0d08980070050b1501ca40e0300100e40300d0103115542d140c81520101415200401034254284004140b07511120740b01d43d8a02c1c2d0110002003050f0b80d81701401420781d2141000034016810090070700c62440c401c120006c00c0b1074050000821014010404681142c1c0305510090002e5808241d540100e076081c014001d4401440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 966620512 1250 966619262 966619267
    0x304080f030306120a1205030a02041d04020a1e0314070509090d1205010501081f05030615030f0c0a0b0a0519030f0c0905030607120b120a030206160503070e030114010821 75
    0x13a41e03900300c0054032446e15803e0010100000b0407000254040720003800740c117103444414140501401081440a8604034411a84030b007000c102921a0740f404a54600c9000d03c11f082c851440d19105110400149180000e0280250100707a0b5103ca5032600e000b403000d08000c2940000c140307001010229210301c11840309050800401c9141c0e07001c0410340d0810968003c80200384041e002c1e4030847d406652110347c1502410040184040c0940544000301c1c1043c1c0596030b650380003011046e1074001c0040502c2d40314010f000c060194004240240c24851590f041083c64001d03420031481050014920140000e6110741c4e842d80b04001c40e0243c03655080582c10100580ca0528000a8540384020301c1507040111040d14060782d110b9641000768000c0c0d0103050a00100e5940080356254084080c00b0740240c4140e0000c120000d4500500c008180400c2d9074a50840d20307401c0301211000e0400504ca0745c10f41d218140624181e0018120034024030001006107140c2e4122004c405488054180105502405 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 966621762 1250 966620512 966620533
    0x160b090a1401020c060f09042906070b1303140301090606030b030a3909090c081f09030915080609160507150207330606200304080f03030612 62
    0x3e41050500012217403a6126184030362074180074003448101c01d03405814080204890300c0341052401003080c400740e0761650288600240001c5d440b642900502108c002e10010341c080001101c0c0140c4640b11b480c085100031403240394056643c00070b805c800006955550100f09181e018070503003c501c94203501511200c0350315141c04d2010910040c0010202141031801e00807814038a08440c8000c00781c1c80304200342c644400346100109021041100d51200c207403000f00f5601c000007007100e1420340094111044600c81070420707026003450202101032100d01680841c0c201086078480409880c0c6684250b076a00c1e041d8100051444080e001400c4151030700b8018590030703403080855080c03076004480300c0c410041081070103000f0b01ca08100600b501d585001003072000d12404211241c503040400012a540b030054404c1821240b89118040c086100c0d18a4520062180d020360f1410311303001e000352803d05a031250f4041c180408099280c44d250000005c00c0050714107031240711000b0311510000d020340c050307 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 966623012 1250 966621762 966621767
    0x106030902060d05041416092711030c100c0c06050405010207091d0f07030312050c040909020d0209070917010e03161106071101030506090702030306010f02160b090a1401 75
    0xe10041c03c140c3e0b036150000541072040440f004220042d13000f04442900d107500410440400711405845103043c01c1c071303c0c00301c4a103150008888100c40090340d030501c80b402039501c243c901151152401e82601503a008030714156a089003501d06030049484950f0645074520b819a1010f07070b00e40241c000c0c03102c203104c00d0017180d030700141502c10390700d0a80d800030f04450810800f0540100111201c0395034401e90248010305080864142d04403031098171854100e018602010b0306640c41100c0084021340144401c001407841ca0300200c405e0f0f400278052842421098003c40d141101c2169904046419450204481904c0d4190360010684c40802000b05090140130399450b44107264000d0107004003501d40c203042c4442c40d003070040014401410150786400070b240a00c21001e440843c81d01181c0340078000b40c0181400c9909038405c640660295245542d00c40042d0340e00141544001c0031840741c0c411002c401c40b40a0041405001c00311303440c1e5100c1414500b009055600d80d045072200e00903504040c601c998 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 966624262 1250 966623012 966623017
    0x1602120a080a030c110a0302010213090605030c04091a09010b150f03060918010e0c040e0309010c0326270a1703072a03020705010e130f02070c0303050a0206010603090206 75
    0x590929004c280302420b01001c6a0a8101420156240c0a841e041e0010140c05500500910303090304030030884665a40008030855415214a981507000b0880f00c18452419520401e40588114003916509040303494401702c25a0483d64940d450307644520f1602645080d4084081c101e40c080805490034800740c1d49042140009802c2902419101c80800d08411180d2010340c8c0c2c40301e624008210748c05c10101ca0079a221a081c9070b460180b89000d007801c18152002c81103514078081038641e415480c850307550898415001a142c1d4102200e00c800555075080c08452141c05650f241980a501044490058040c0d030f80d4807110603502c1d405118864000340001540525140016000b0394030b82c1d40c0e40206680c21a50002c1282203041c2003042d840c034002d2051005200c0e140694211881c13203403904015180030100b415160352211200c20b4650f50464250400001f0421114015042084d0366603074001d12400f9030400c50100724045100800c413581001101d0041101d482c0c140302101007034000c40ca803803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 966625512 1250 966624262 966624277
    0xa1706061c0207020109030803040309030b0c0f180f150d1d0706080402130c02010e070902031012020303130b0a0314070504051c020a08100f05090705010516081602120a08 75
    0x41d004140e450035607009403204401123400154056492a10340350052902c0540d000031256080d549011030083c0b4811402c0d560759940c18002c032894407540c408145200c545e60850303e50300801742c8a640b00745803039406496603903841c1031362074039203519003520740c0c1c0b0549480c2881140300b806558541022488002203000444540c1c0c1042121600c49002280301046078001000403103050150070807010740c0c154010451030202905513014180c44003800000da10040d80e6241c03020314071020034060390540c551420300c05403004045a1030101c1c0301d000d081c1c246107144c3c0304141e00c11011543c600c100340c141c0141d040100c0c00300c1e485206840c10000180843c0103c0c082c940c016041c0b044c43c0c4007500e03803c01410010300c0d001000e000319030340d44120300d039501c4150303d0345540000d04041c1c01c4840c0f40c03035600076030f030080c080040909003c0c0d08100045840750032104911003840314206100021030039960041440302958590203080142ca4018854058100c5069039001d03888030652070003103400101a50840c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 966626762 1250 966625512 966625567
    0xb0a0e0a0207022d090411120708100516090509160302071506081006120209060102030d050916061b240203130605090f071802040b0a170606 62
    0x640c4408901400034029090003d40100c0200070044000d0300240250104403040190400d400700e002060280d0020b007902c2c020441d010190850300540340c0100c00300c2030f10341600c0894201c2990f8103503540c6803050501c14405510b0390350341402000740285810510f9110141460b800c1185000003040d4001c03402405207060714620070030034060358402d0701120308068104000742c14840c0a0a00034009041e40d10441810f4843c0741d240031100b80540c043c8008640d00300c0c2017004150381d29001e100f00d40030001c01c5503045000c00c01c00010b5182042c40340c3ea000c1d0300700340d00400340d00c3d003810701480045a86803c031a00b800010087c80d42c15104a02c0c044030f409500c880c505641c040c0704140c02140350222000c0700b81c4640080104481081c0c000311200032940102024003503621010440354580380300040390001d9421080c024400070795038458045014081c0c6600501e00b40d030b507001da0700300c40d040100382c04005500310060810000000103c01d8100d00c0c1104c0315072130f0401c083c0c0101070300319030300201114 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 966628012 1250 966626762 966626789
    0x50610030302060a0f1b02011b0c05030405060306040905030c01060602060f0c030a0f02130e2203021c02190b1902131403010e030307051309020a14090406050a060f0908010b0a 77
    0x104440c4c5e541112221a1440c000b02c05006403102029000c0c2c1888403008003081e0b081071903502c07014402c07400b2140e541e8108015516045c00c0c035091010780d41c001402c3c1d980194440404e880025020001007680020540c00096a103050920003030400c4006010784103125406828040d0f40c503451021030b6082025a40c00003441011012404084d00400101d941c950354030301ca00184007035248256600c0f400312480183c00b00054541c1841e0540ba000c43d0240c01644904a00205a150b21152200968181c0110313200b80c1c1d078189010402412801d0120b50f411000010b022079070382c040c0f0381d900410204200c0ce5091201c1030740f600d480064076101d401034418030303620380c1d8049440a505c0041941c1088060360355031b2400000107482c5901c0409210002e0551510004900c006882a1a00401c082e62400c4800c040d0b00c00085568001d44000d0349c3c400c0e640c0c0c80010305075a499106000610a54a1f008015117011030064001b10980e449155164140140d1030016039030001440151100c400e81c042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 966629262 1250 966628012 966628031
    0x8011403070e091e010c0903080a0e060d020a02010c0c02150901260601110a0c030f0816111801150f1b1109071b1205160b0103050610030302060a 64
    0x78a40a920360140c00c080c0102000d200e8451804104400801d2550791580d400d0b800710041d540c01c845040f400580000c51301d030030030310014950900410b6a00c03030902e0320071031003d0107000094066000301508030400350f00207020310440cac6d020300035030314800051b007412184c1c600f09802048602ca020003a13a6031140d000900e4840c1e80e03024512002c1034050100d003c40c00d40a01d1515111501c00c25500e041c04103004030704003001844c00240c4001c085070312005601c000c84c0f40d9034503007003520301e00c0307104945414087c040950300e526000c2c0210b6034540110b887d114911022811300a10070015281800c414000308018000710820181c404900340242c81c0400c10102034400c00c407104021409804004028248141d0500c502e1300402080a401250317030005c03070303126402c042e2081003601c2613126504900d01c1407140400c0c1803e0307400015001506286d0319042c400240403115061800e803c6030140220801802440010444998840209042c00644505546000c2d55880c001080c202025071180c000300e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 966630512 1250 966629262 966629269
    0x30c090e1504020a0311040e090c0613060c060627060f08060f040807020d08030105191203121e060e010504060b2203080d050a0e0c060d110708280f080114 68
    0x4800b031b11403a02c2c0464603661900d14401800009030380783e100300c0c8200e060309103c620f80700c0200c8089c0340d01c040c05001c410740b800809445040000d041a40c07000e40d10800040c9004d003002e684031072060110300d0b0180d040c070b18242c1e901c21a56290007a01202c805003205010b00c42c1c00060242c0c0101c52345d410721540e41c0e03a610b003440b86132060342c10080d0003442500c40d04003045446009103045e25001c9072403000d44802c03d800301c9500c909912600c1c000c1d140c840e0321840403c5c001c4030080042054904046140c10003803c60202102c090f1442c044540d6580c0401c02c030280c02c0385042400350408481c20b210f201c0c40c1c866846201c0c040d080c2c0c81e5440f8001c0b4801650074a09100b01c1900035603228200d55240d50a08403901c00400c0700f1201c40d503c850a00741c072032484500126003804158002005981410080c54070702009120212182d40a15401c00181000c0740c0a80058085910505040e4048107205400081104440c01d02d20090050f00950401440d03006400346055600c601100c05010b0703400c0c2c000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 966631762 1250 966630512 966630521
    0x1107020609061603050c011406010f231306110a0314030a06030506180d030507080117030d020f07052a12010207060504081e120115110d030c090e1504020a03 69
    0xf450b9035004110401c808040d00180905140d04d41c0d0740080241c0040003942c1c180c1240200c0e40c10f0300085140c0e00c000d44260180c040c401c0c50b40741e41406130740341e01d64200501c00c10782c1c0460810000300c103038400c0420603640d229460144040b8400d002d840c41c12a1950060308c01ca8100034a00201100400011510382c04d9a00420003190088112038550501c2001050b01005202404e03100c3e001d0340e58032000e1107000c0d000d07450040301d0301ea0300c404079070f1729088148620f515200d0720350340180000c01200d00c04074228006498044440380b0202d58505140c605240380c07105003d13124440042d0305503c00c850001c041e0404000100644030103007031880c3c182d4071a0080c030800c000104a07034505010321050202d50740103003d0f1100c00b601b0303a99103e11091140e801d14001c03825226480c0d9103010050003400e01301c0c1d1610034000c1c01d500300039001c0f0410080690400c1100c030088800a0381e03e0341c040c00c600d84e100246400611030340c1e1420383c3c98100f01c60403000d103280201e9001e00554000031101c00c83e620070b610 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 966633012 1250 966631762 966631777
    0x40e1002030703091a0735010e09010c1416030e03150a0c0e1c1a011502070b0403030c0f080f0414151c090c05120619110702060906 58
    0x2411540e82c40c0c45100540108000403043c0c0d82106402d40b001c440c030025105443c00f170140f5440e10a0701204151903449008030700700d400b01c1c82c840d012800c2d80b5052480500c15001e40364215110280b403802182c41c82c00c49440007150001c0040e0f01410202641180c403c0358102040308a40c101c0301c81107802c0a0303c07040e0082080c0d942600c903801c64503480c4042c004d0b400d80150b103544000c2c4032a02c240c0c081180c1034240500e40907480004200d0b0081ca4014100b94120070b01c1c80f446440d801d6041400e03000c12048426800346900c6403e04095500c07166060206001500c8490f420070f0625065440040c5020074402005000c01c80303004c40c4070705112054040d644284481e51010b40c1e215110741c0d00e494082d100240301c0e030040b4032540c80500d10f004900140d80c2e980b40d42d254a4a014145010300700081d0882600c10f8440c1c82a6400124154451127a00d5201c2d030003ca005140c2414038030345e1a0007605446822100c42e51410740074085021403c011900030a8048449c50b8561051600180071071140b580d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 966634262 1250 966633012 966633043
    0xc0801110405180403170a02031017030924040e1015090b0c070f080f0f06040819110114180f1b01030e2b080103020d03111005090c100518040e 63
    0x203040201f080843c0d0029442200c0a0881c28261556400d005094101804e80c000003600300741314040d01d6041200d5000c440f01042002841e07540c0c07030f031074044003982e0282d000066059002c13410000700c2c2c00040700c0b140082c12030251100380100081e100910104207070103a54807040f0006800c550130202048400041d04d100075032028030542e641c800d1684c40c0c01b420508040c90160f41e0710309950180c0801d505129640010705c61f0b00d86000380c41990741030000c4c0d40e0070310188825140f00c440d20800c2482900d100310400702c0e0545a50812040d160b58030308006840d00090781c031102d424081e10401280406c46103685800d0104090360407401a030241c014150940790394030074030300a9402c2035080d4082c1c01c00140a08041c00c0328521050703003241c10b20401d000c0650080126003a14002910400f0f440040f03c490344169038920145e00700b07110960b10140e4181101da071040300c1c5030000d450b00c00c40e031484146050a0544c0b078107030074490701040c003941005010b100c0c40d5188000b00b00f51500b880503941703961a1700c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 966635512 1250 966634262 966634307
    0x40b0c070320060105030f070b030c0a020a0606060503060f030a02010f0315053003070515060607150e060a090b01032303040303080109050a1103060915030a0c0801110405180403 78
    0x40d101030f9600d075424800d1510034440c00c14800e0303803240049840c0040d41d070b402030500c0c078568400b888a80161f014222000452082e480000c0202d407041c8075641c00b41a49582c0c0555905040c4200841c03100030700ba00600c203400c154600001030703030418504040b42100d81404550502094108a80c580d020340c032890f0024002c2e04c00d02c0c58941020202c176452010022085011410184460340d20b004c1c0c03070f40080c080c4d0721413004820019000d100c000c0d80580300402503480c2031070b2540c0d0826a05095030414a03510307100d03102c8070312066040c012240d206540c48410030645d501c0384c99002c00c0780c0c4180700c013138840224101009511081c02a011030450141c000b1a541c0c0d581d2450003c0108200b407084801841c640408682c0581107400750580c0c1005000c00310342503480708010044c008002a00010b1040100038400c600e545052080f002500c0c083c2c80c00416407403800003030303038255004020058041c41c01040144441d6880164408101d0507044042405940b00c6c6820b85111000e44040500c0f103189 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 966636762 1250 966635512 966635567
    0x306060b160615080a080d1d250f06050a02010b030313030807060b1909140f0403030b012c1309050304032006032410020606060a03140106170f040b0c0703 68
    0x4250003808004180c1c0400c005202c0004040505d0480c0b982022507543c10034008143c5007441c00501d8100c00c8001c850240000d0356840381c600141602f82d01c4800811000315010206640a00c1190617682c03054021f175150200d040e00f0700942000c1c5000043c10164003240e90f40034021150b01c030641444029125091400581c0c65071860f07102244035a01a85042404c0c40316079031506201c090080d501d41009a0650315180e42c15000303042172504807030400004920545005a0380e9240e41818180c41da400c16206040c03a0a0204c0c2c2d41000c41c000c2d40e0341e41081141c000241e8000102c6045a8100620f203004030400741594010110031403030154030050102c28404000008170350041c100c5d0030081c2400d4204110024004031510400030000540c0002c0002421030070100e0046c002007076949000601c01d141705604000c85a420b800c02070000b0ac80016203402d038461442020380048118241c4651032416544024140c0f90007003024200d82d102080c80e00416004007244c103040c1c6141c09540b0b401000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 966638012 1250 966636762 966636773
    0x601030903090f061106070c03020d0e0f0a24030501050a0b09011412250806120c0301060f0f27090f0605090c150c0c1c0b0703060306060b160615080a 66
    0x9042000d0285e40101004a144c0c40d00400241d448198150007030101d000190800b55403841d954221203801030a2101c42440640d0754a402d000905082c403c15041c4038001d034401220342424105a0050507d01001880142d540a1809049606002c0150b98030b106000040f98056500e4070202151074001c030f980c091982d1403456180c40340c5c510310210114001c1d954030841200c0d4903a414000424000000b1070b44a081003601003079144107000c1110003000c0508046401c5030555484400c0c88681341c4810f0007410342100c010002040b1500310101c015030f07110450003041403030700c0c0400c0b07860740d441860004124502c43c0b4500744e603130443c0d0108160b103014183c0540702e21400c0061441150144480068032884005541d03200d04141c000303018180143e028008181030030b00c051841e43c0c1040400c07030001b031007a80c0c07400d200c2d4000e95000301c3c4182c59407810105450b00c54001003020700c001e01440180684100c180000c294200d00d010603c10b00b0350020100d14803954010701c0450240ca46400248003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 966639262 1250 966638012 966638027
    0x702030702040b0d150509030c0d1d011e0516060905011a090108030a1d060403120e01020307120f090305060c220b0301050d03050d15090f11030601030903090f06 71
    0x180261018403d5070040400c009a9240713890b0001e03c40340c40340102006012981e4065507010a280301100c0c03a000584181500c0c0103014802c44000541203254580300d0b110b030400e8074803111742c00e0a001c03580b00105680407a03981c040c1c1c46588100f0202259001e1265009901030600c207070020010003040c411810901e0103400065540d1450301d6500c84019528208111030340d04940b001809141000c0e4103040840d1004ea540e03a4010441c615500058100d5131044010401184240c032000042d1040013009001d000c0300c9002d0360306540082c0111408079000b0744000300d50700308503c4c0c0200c0c1106032a03800d4071400c1043c1c0002d00280f04e414108070f22504140e00822003008550030529090700321802d0204a0350007805850018107061004100604100301c4013140d25120382016402c089645d20644101d4061f001407294441300d0382c10810100510384180d010345e131920181401440340314540800c0e1440702800042c1010b640e200b200d418144a1400310001d0010001d280119942d1100c00802c0e80 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 966640512 1250 966639262 966639277
    0x309240f030708071e031e050f060909060610081f061d0301290627040c0201050714030705071703070912030c0611160b090106081b04050a0212070203 66
    0x5818040803a403040d010b82c5503408000000650000c40c0e140c601720483c050104808410300d501031482003030000003a00e0140f28415503080914100610b002010007180c8500030b8940e84064222005100042e2502014000d0128140c00c0080386074a6090b94001c162400c0f52085040104a0b407000c101581d0009030403074800c038182d203819442e8003080c1c03c1500300c0d01c00411503281c0302602c40f50048118127084448001a40080519083c03824a032020103030400504403000710140c0c040207540592425100343c0c0c4143e1010f2000f00090300d04540003403c02100304840001116010001a03050351060342102e0000c2d40c0b09003000c2012410440440654000303488040c00300342400008101c0240781700548041c40c1e019036601070134001c2c1c3d440320070050003400100071406004010081d42d0000032a1484c003c144150b00914991038074000032402c441180d04400819009440022602007030070300c440e4041c400454000078685c50b000701c1c2c3c000a1107000b9440c20f80d95114010007580b1341d00030024010a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 966641762 1250 966640512 966640517
    0xf020d060b1912120201020f070b1e0405030313140d030e0c12070e060d0f05100f0b0f091e0408040e070e090a0f11130306110c0309240f0307 62
    0xb02c1018000301e81d40e00c20310740282104608060b0301c00380030030701e03696080700c6542160000619241c014102882c023640900429076410300d6a80034406c83d040410902007421703518940306607850809580e59078891201916143e140190f4815a106108a52822442004a540450300f156030841c2015010f40030484d06005140640701c05010103080c04c2d20860700000c0c200000c0c0100c6414168907030802c4801a014a400c17005240350017002640c403140071000c00b0300520080034180d0045035644203486485854034003080c1480800c2c1c640e512012944000d100048440782059070b034840b207448170408441c090f0301050692005100a00039070300000d0080d0703020000341c4a115982c000d41078500c0f07110511003a8100c0400400500d00144940c01101c3d1000c151030080350700c074000743d0b912001d81c009510310408000b40700300070810001684210010010035400050070030f00840b09158130390007829100d038003906414444900c98540300c2101150008400282c58882a04030030481e1150000c5407000302 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 966643012 1250 966641762 966641779
    0x10e2b0506161b1b090b090610050306040c0507020604091d060921070c23010e0307090209030a1509030e120a02040c020129180717040f020d060b 64
    0xa01c1004a00300440c40c025441d0303140090403040d002514520343c0002030311400008100952035503240051500100140c081c003145850300030041040009014003014851841100145d902e95088400d03a94010811640022000c41103002030351a4800c009000b98460400a0701141c1d03000725500550240d010700e620a444080c0b607614442e56154103880200c40b41e0300059070b24100744a031440f41060f4a28110721582056156a6030301c810f00003507041001c10b1103d0003042140d5105100000140d02c07003d04c7c04684c01624903000c25241d41d6070f400340740c1c0c040b500054590031540301003003603600040c0d0040e5001c082055911307056005150007034084000803011000009a4a0084007207020841c9203005000004101c1d401c0200900247e0407210035952122490304c0d0312003880801e8030489102c00210483d6036002c07802c001c201500d1104418110706404207100803aa401500c94049880710184940d95407201d0401880b0b44840c0b20009500c602c00542c4881040410f4100c0c281c3c0300fa0542d0f140305d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 966644262 1250 966643012 966643021
    0x3080f040803130201110f011d070b1602010e220b06071119050a0b040305010516020604030c030201090f11090901021e0d0e06130b09030403030c02010e2b0506 70
    0x20069002030340c0c0606860014004903903440080081640c481c0e01c1410b00482e1135084202c405d05042d0300c200125100d0759140a0251420048840690000803100241249505003c0f0740e94880c007900003035403008110300c41c8000459006502805507144d0044c440c88241040b20344c070058540410b01c0210840d401c1c401caa5400d82032603000c0d10405684111100c0c007100c0c03400305010090b015030702d0100211484810008144d110068848080e00702581c10a646900b1801e00b982980c0d0050300c1185418140741c1000c140d258049a5a500180e042c540131114403101d04040f4050004000007804904107c081e020400101060340400020180d50164a0340e960f0b03107065080b40925031749511551080f00005100a12031001400a2001d1100014620179040c001920f4800d0494039000c883c150980c00a00b40451402c403141e21001e83e400440c500f1b82141d030028150002e0b490000c0c180040c034019150540c0e0b03403829282c1c0d4142a46101c440c000d644c968809150842040141e80c180203420114 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 966645512 1250 966644262 966644281
    0x70b090d032304060605100504030b0609040c030209100f06051b071505090a080102120403021504050a062c0d0908010636020c06060126190b030a0602070308 69
    0x500100b103542102c144008840c803000c0824035008100b259150f5850f600800c2ca59140042c1d003020140d2982d0f882d44507821841c05008003040682018801c2072514100000620200c2072030054a5040c0d440d0340654440220090950070207406c000610494900302080041d80180a400078030b15580103e007103950035114441c0c0360701081c000c509030720104981e44025107001e00003c10302e100740a416038003280d07034400c9e10302d007241c00003100713011414226024030081c1507042050304a039855503545103055040a0f5181d075543e03031268400038501307030302d64000154002560315200ea2005126800041c030032040d11407203848481495860f004500b8000f00030812000520800041c0c40114000900e580c07171030300b118aa095007800b1804000d00107032031600c450311114005429000380c00c40003410704c0e052210002d400d090311030001c4558583c64108001c1007290119078942c1007090401080341c500c3c985a4080040c0211604044d018031036658000204940c643c020440030380240d440d00c5091b02d42d0005d6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 966646762 1250 966645512 966645521
    0x1507060c0c02150a200f070305060f09030a0207061d090708060109140d0f0609080412060b041e05100f030b090d08041205030c040f0308030405070b0f0d18050102070b090d03 76
    0x401000a500c00f030303030403002a110041c2c82100325000080346d840d00c030205000d80c070300883c540080f5400d4000c5c0041c8030a9250f0780c2015a0000d881c400a94280a0b140030003d40c0c58142d071144030208400d00c043c403440c80c80d04008100c1110005490841e65240024000c3c01420054500500145140c44002013002d0346002c4a54a83e00041074a00d80c0101070b2590010f034980c81800380c50195490540c200001d40b1040200700070520381c4400e100715802e40c2132440c200ca10344c404c0203008a0038946c400442a40f030710440111503041900c005a01d40340c412300a6501060394100d14401c1c7d41e00c04010060120303c2126a01c551403101c01c480b03440c503e41c9070403541ea10090b00c2c0101070007121076100d40d0b545e00480241d548a106082801d0800f035684420a240c0481640255480407001080c00144031007030007281c0c0a02080f8450364900018105200c10911440000031103441d5240001d51140c0940c0700084401d80d00f0030001d54540c0b526090403625024184c9030181c2a1140c54844170785980203014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 966648012 1250 966646762 966646777
    0x30b150609010c030e033406020102090a180b0a17100605010801060f0e060d0906050a1a04020f0c0609241303050a110d030c020c01140301051507060c0c0215 69
    0x40e00031440c0c0e0b4a6806850030205d0341c1d04075a00d030141441896840c1c2c000400c507500c0d0f44100c400c1d0000006001c3d60340d04001e40c150412001c6900402c00040e040e203032170310103104441629054402080d5107900d05c80080424910842d030110001200041d81521801518400e4411074161010f841c1c0e46180343c2d003103075458800c1c81e000c01c10850040000b1030152a0901ea9207255040101d816441c040001e807660344010300203440542d0728601390003400058400c003580900220170030001805c013400c42d01111140300c05031504c1a80c002424420041500081c3d882000750744044408900b42261815111884c0b0189000e4a184820a011041c43c071000c106000704090102d50300c2c5266983c030b044405901141050041c400e502c07160300280030040140b0302000e11540d0b0b000420003800a0000d040c80e40300d5010302d0400912050002d0f20118180840e07044803070403201e9074070340054100c5202d01c90040f200c0c06040d031450004000d0606030029007071145180f00301c030011240d110207107003040540182103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 966649262 1250 966648012 966648017
    0x90f050907030e0a05060c1b06060307051207030b151005190503070c080a090915030206040e090a0818010e01112d0a11030106050105040303022a040501030b15060901 73
    0x9022907001800380c1d014214070050f5500b61810721025480741d41c5032040a44809800b01c10002d400440017420f00c41c1c54050340c0c00c900c080d221904150b40001d980c1c170f00350300a00d44100d144c400c142c2d005400c10080580150b0740030507030441c58a0b111381d1007003907140d1000c0118007070300c074043c50380d88541d2160040304c1401d1409400d8426400d028078040b80c03260001444042800b2100e42c0390f50200300020080e042d070807001d80d07034130301030703c0c1012449000d840398074050b0107444003083d0080c0010390f1148140c0e81030350302e1880500b8599aa03401c0e06d40c50041c0785030700039200c4100068400e04803814981503141446007070700c801200c0810b1900445001200d00746124603034120050b490302021201f4030b10444414140018580720003c0030906080020201040b500c0305642c000070049801d080c000d4500804003420018101391039610042c0d00c3d83d9040f001481c0b50745135501c64a00210b601504150803242c0a0810031541d80c5900c2d20008441e4191101000442c10074031420032803501070119002090706a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 966650512 1250 966649262 966649279
    0x20f040c050a12060b03010b090307090b101107051c050c0306060f0f010309081803060c071a0a0e120301050f121b061227011a1c06060602030a090f05 66
    0x5038040320a80031000310a40f00940b5400001500b4040b400518080e00c0183c40840c0e89078010001c1516007007142e8810403c00b4104408007001755586142444e94200506000da22031191528a6003421015004a40e001e51008501e440310032040c090202e005100b08100d84001c8082020140c1c0c80d1000c83c4c00d154070014003040f280b40e03424180b102c104440010b040200b580c195503500d21280741c1100742e41e002818180c000382c01c007528007000230781d82020141c2404c9151031402d89800c0c14811003400c03042410541400840c0c2c011021754000b41c640c402040665200114002040c4069802032080303900c5002d40800c01160740c9810301824020b19480001000e51114001c034418640000c01c0070a41c2c02102800900c0d540d00002020320300c2240300c8028100c94180300c00e0f8a102400d070313071034080e60268500b800c204520f000ca0b1204981300740382180d41ca00038102e0703a43c4c80c0c001c413043c43e00020006030038054005902d0f6000000f8200e50380a41c2c41d40348420351100c4003856101a6803060701d6021221 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 966651762 1250 966650512 966650527
    0x12030307090b0913022115031603050a0f050f03190801090b130b04060306051e091203060906060d0905070f270504020f06071202010b27061219020f040c05 68
    0xa0743c1c000c0680c05011005100c662586c801d8403855804221020100790b075a80100340c4d000d160920015011001500c10100c41c0da0560315042d6850b480306000414820440039400c0c24868200140108010b00f1001c0f640e58400c003814a5001750704464046000c1100f00e4008620b1990500540300b0140740508503424100040f140391000d010404e01e595001a500c42c008000315940d030080740d01c601d90962180951402c003503c04e2281103401040c000035074110400b001400c500c404201d035003181003118600010b0300c980c2c001030640e00c03c1c100c641000b50700e00010442040008900d0000311f403032050341e0304c0f002039986a034600e054030104100040280394440c0115019007d60015070024009001000c5901c40c01011400035071102106a44126000500d042c0d40f075030900403811000c80a1b1001e10104505d15140718610640303401c03420000e45000000343ca41d460344024131081c08081000c444920001c020007200ca6524604107a02421801c500c2c40e0080c1880d00505c3c0026685030740f40c5190004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 966653012 1250 966651762 966651799
    0xc031a010210090c090c03090507050117010e0901140f040209072303100f0308030a051e0601030e0f03220b0a050307110c0303030a0c1719110912030307090b09 70
    0x218060407550350700c40c9200440c41824174420013441c8109510000303560304207820b21a00c2cac100c495203c03604001c01a0b000b12400510213100c1c50448200000c0c8070003a460b0010228050030103003004442c041c51034000c0002e05204814020300503402031710808419103a0400484a50481d07001d0120340d024181c1d401d20003e00c0340740055610240d10410030000b10381b03032010714240070815031055400104c0803050004040c601c1c49003c2d00417000041c51a101c0e04d44110140008074001d00c0c4030705055031454010401142440850360940f44074059a594450014681403000074446008100d50005000416211a034204071484186a6203c07103003540c0ea840c4046400400d40311000c2e02e1401414081301c800d441c02c2004d90b014110364003010641c03041c070441c01000b414603001d0b64001e090540060109140f8141c04400c0c800000d41400b10700700c5000050500c9a104035040590803407440b028000b6030100220145001d06582d81d1401303c1280d68803000245405416807040d0300c02910310f440d042a11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 966654262 1250 966653012 966653021
    0x4080a0c152a030905030d0f022a0114121008010b0102060c1207090906030602040e09162d030b04020111070e06060702011e0206040c15080f04051c030c031a010210 72
    0x1440303441d100f038100307841744017082c04c240d400c003880d9001c80c002800c8003511a4050080f10301d0100c1030011042310899201d400e40ca011010151507050040680745566440401412070f402943d00d040c40701c01e242441a0400071110b403601c00d402e07155180c540444c0c02036102280460081d00200c40c59030801c1c0380940d038090503150103400501800b42c098000181045103001d9900218012240103845500d40115410950350040044240c0d400240000250313101542c80002591100081000c6d0941c8901c10824546c0c600588002a9080e1071000000c1081d0149110701c250b02c03c1e0381d40c0401100140740c050b6105000c0c020900a080c1400000e8a142401ca015005103401403401280da55400c4032684000c02c224130743d000060700140308010900c407003003200300010245000f1100400c082020300401c0711001070310034101c0e40e20410104040c88400c205038030079000c45000e82a00a05500c101030000e214141c04d60000c43c0c105602846070941c0280300181240c0107070043c1c883c0310441c0341480c0041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 966655512 1250 966654262 966654347
    0x200d17090a0c1505091e0f0d020105121f03110307060509090408090402130e1e100501030b040204080105011503060e0c04060309061409030a11011503080703030204080a0c15 76
    0x4130034000259159905d215484100c41c40b01c010b4041100c54400740054000d40c00c1002d40200c040003071010050f40d01000311600922684510001911103152050b8490001d0300040a0080b0060300072081c4800110741b4aa8180c0032021100800d5075520300f41c901d03014240c88140d007c0403510003d0f012891040040004610061006107013011182651102100c6900100700403120038003003141e1440c0300d540d050240303005a854209945800001040100d41074050b80d0304040d00c2e404040515242d41e0182c03009010810004d000d00d41c2c540710400311034943d0b00740c1c800000342085800a40f00d5994407480e40100340c04805a032510703003844070a030090241601c0840c0d0060341d901d00c403018401a41025400b4480e030302c014503680c009803070000348031310307907080e028001a45820b20366500c0020380804039040f203901102c025118403a50030250000d000d55480b074030707643c00b66280a0b01046404012072094420841e464994588142c03070403501483d1500b00e03d0402c074049140001c0c10380036045404003c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 966656762 1250 966655512 966655517
    0x406020105180304050108090a1b060806041e270813090b0109050108330f0a051e060408030412061d0a060b150705010506010801170d200d17090a0c15 66
    0x6100305907032b9001e80400e41c2400d682c1d08010154180040f503842048150495011502800309584640d01d044a84400c040305452080d668681200c60b0a41c0c00c10701005011901c000751400e4a140c1000006070b03218078281e030700301175040c00b02049110043c85440003082c0184d58620110341010019554088003070056440041442541d50142101c20b13400d1185001c05020301c11000400000d0100c104c2d20340324554403424588606121944a044d40082410b503122100140b403444540420030740d1040d504010058080001c02003080d05020300a00000392291108000e0300103802c0000620015442c50384a51b504400d074400041465030304440d44440c0c0041c0180001c00300d20b8018010f5070b2001f402101c080c2d443c0e104210301d40d038005980c0360040004804050091404420560710395801c09400c01c203001a08401d04114608000c425091910503400c03201c0c0b0301540c2c080030b006c513581079903101100c108601c001090800b02140d050200d0303500410b1000b044d400c102c0c0d00c420045444010004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 966658012 1250 966656762 966656773
    0x60207050307180f0603080c0703060c1b150908070606030510050411010818030a0806040f02040305030a030203101d040c21020609040b040c0c1406070c0605060a080f03040602010518030405010809 86
    0x41031909008150442d608401010b005e84ac51411405035201174030980c0c203100b4280002079420070800000d48070f42340d010058103610b28000c0b0f8444001e0140c520060040034000c03d8000810285e0b03030040d03090b2800340003150759282504030700100fa1030044900902d5003003a1825078440d0b5009691a54109020f0703012041c581114400003461600b145d5a0900040e02e08400e05c8117504241c0f2980c00c05600101040d40342509503201c440c0e9030301c1010040001c1507030000000c0c4101c02050315500c0509903403512001004180c852020b510380c0d0554090310a9000a100010380b24202e451001c24031020320500480143c1c544c08110254000503c4940c000d900c030115456166218400d00780d074184d10352620340d0340000900340044880c0ea0040e041000303a01c5041804240c41e0441d8454821590100340807030031380d85402c040341c61a041544543e019204400c02c41c081d41101101410a0f1446903008006c00d030345800b2900034039104092180303815081008140169407040d030007142d022602c0e07401c03500e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 966659262 1250 966658012 966658019
    0xf0412110301110a0e0a1d040c090501140f0907020606011803060c0f120e0c040b040209090a050a0c0e0d0206070c080709140901020304110f0301060b0d0204060207050307180f06 78
    0xc1c01e40f2580900d0040c1d620000038418075485c0c014200700d0200c90180c4035040ca590900315800f0442c50b41a55180b404403100c4000750410a0f00c00c82c000c0034040b034400c1403103556074840b2040c07245100a42454800c24122080c1c002c00d042401d0f040748100c0f42c0794000d1030707961076000043d00e80c050411281c02031080820b10100124042c7d001e0700911200f186d54055241103405001031040780c4012607034110600b8000364130314004000803c580240b40071200003507403401007400280203201d4180303195042080c4004004902d1002e500c418403803140044207110054446008a4914056028003540b101c0b2079460000507003852030241c10514841c1300d80c4150542c1b540c608600e0308138143e0080f1603081e2200c0c20b410610381d2030040d0b2904010840029070450a066036084200a000004d0500603c0929140d0301c07983c1e402d4000c3e50091030140403482d901d00112901c00080d500600907035002d4440e110000071181000260442114280100704034400746480d001c00180c120000322900d01504e03042d011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 966660512 1250 966659262 966659269
    0xb1c0227040b0402070c0501090605120c0f0d050f0f090a0b011715131709030a14011e230424060302060f0c0d09060903020d1a010803030f0108030f041211 68
    0x80074880d001c0c0c5001b05480e450007000421198045d080103040000c140191803c107070901d00d031240c0140d90000725546a104034843c1c89618052101110326140c02c003000d11440940d148200740c016070189546031072f20780d00c402669039030300a450310050051302d01c078004101101d1340d401c40701c5613030783c3c00800d840320344000100018400c403050700d1410010324010482410070000b040500084001020180c0c18105810002a00d0303e00d01d0401500c0e48807804081c80300408203600070040d4100c0b030004a022080040800d100030b1001e00004082201ca581040c0f606200c0319404510a0394002c40140e9000340001c144034040ca0104020040e4030349030032001c00180d450324007a10382600030552081c0c40b00d05100384945000915411002440030001e828020640c0c004015005d803501601c41c3c103a04842458035051210f107a142c10104130380254008510041c010006600441180055051698a03000340681300c0c81001e003030b91318202040208100d482d051800c070030b0910b4043c1d03204090841024020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 966661762 1250 966660512 966660517
    0x6030204230601030501030c140a081914060c040b0c1f1415100302130f15020d020105010609051e03060f07021b0312030903130b1c0227040b0402 64
    0xc1e400040d5440d91044410215811240e4062000d01e4140300079455501c43c03400800c0b81e4010386421480e40c11050007940c0f14001c03504000c090078400c496081d07502c0c4030f0100b17060000e100200d44c0000082c07050180c0c19800108a40540584c010a034a068131b084000d034065489826451024010010f1803218561142203900c80c05842150200340e0000812403e080703e000140314010502c04022080c5c444d444d200c0305400600300c64203006a880d031a101003010f00c03000991001e29a02425600400c40d28140c910410200c00c4c6a000c0f02c03401c0083ca842642070b181309000c0c24000881901003000076141c09070f200391081c2c4180b81002c41c140b40700400b0030700701002200d404400300d02400501100e96810004401202c140354000c0c4030025100001030f4a41604500d0b40400d00000701c04640010410700444481341548071441600bc1da440c030610090740c000c508444d07007901141d00c03044203240e1302e03000300d9101c403a1104480c040b0100c8d90041141c00350800c103020780c0283c0d607188101940c0d10b640c0700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 966663012 1250 966661762 966661781
    0x315090204141f0f1d040e0a05070f120f0812040c1809080909090c03060711070e09100509031308030301030c0611100c14030106050d06080f030a0c020406030204 71
    0x80000b0015004018003101400000010b000500ca0300398101d60a544042050503c01c0c0a1504c00500841d481040160784240049168007034500320494800c244005103030300210703200302e00f0f5030002a0f807140ea0382488815441904a02910004140005400703500c44445003841018103e040089904210120000880f0101d07200030b036442d0140300c10400c250b98040442c0e1001400e002c0300040395200145805800f6416020390700c400f0125405450600010162074030260480c1c0170740ca0000030003040d94400c00c007490b41c14003c482c0040f820811908010744107103d03603001040041801035102c40103000050030190340307000078800c0032600c40001059a005010b49401951254114181302070b00c0846a8819024490500b0019460310000708089c0b0a0b44000017002414001b198401e1740e4601c1011200300f1150000400880d80303a41107400b42143c07062a060400020761a00d08596540000c0780481040707900603c55205a58880d08280c2d0082c9e101406c0402c415540e58041070a42e4940c43d07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 966664262 1250 966663012 966663029
    0x171f0b1c0f0902120706050f09060d0e030304140a0f031110060611010f15030b0a060b070b091605031c0c06020d020c061f0611010b0a060815090103120315090204 71
    0x442c0720381549004000008900440300c0a8080c50b171074030601500621400400950441c80407032158069500e0708149c50a420015006000700320403032404035101c2d031007103d04440c2491402e1507403501e40320008510011950101c0c041803064803503141642c002001d2050900300e0710415224007130458081c011030340203204c591a101c048510310074019087d91110300d4000c1c425441c00b05400c80300c2005420181c00c85c0e03000054001d8903241c0090160282403250080212000000b0300c9408200606a007140300718803403410303200307840114400c41000c004a441465850f42c2f0062260b5181003949080b84e9040c5140c1c01c0c0356940c0303845595520b003a60003017400d514150340e01080c3d0010400060040c207074403001d0b4800c54441c0d100040b450080d1915580110001c05c0070560307030282c184009500203050308030011702c01d1400d903540c0d01d0003c0401100701d0301c0d200d44940c3c0302014001414900c1c0200e05070b0754040320185a6990944046000340b590b100700001d0a0101c4000044e034207201d1000380050101039 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 966665512 1250 966664262 966664271
    0xb0303130e09010f18020103110d050c070c060e0f09071803080406030b0102030c190201090b0c0106030201030f02090d020909030f030c0c07171b12030a171f0b1c0f 72
    0x1010b0306084540703400c0c42c0c4402608003404020b415080d500c07031811040d42400c0c0007800360a241c0200020340140341c0700c211200c4c44c06003440645075126001c0c10040c0d12071100e500c0180e0311813008448100c80004415080b03003c1d6071220a9600d00910340f140d220360305241c000c241990a04900428400b00c0d4170030740c1e0041c0001010310120350726001d0540c41e0f1f2802e0000794640207004840b60760f03d140040303171080c40c01d070001e4a0313208580c460340b031082c000e056080102e51202c0440b1a80b034020100d51000b00c0c0401e2804403080c80080c5c0d03c0c0250740c18028010406200d8040940900c590310b10001d058045601040003a0214580208003641c0240315401c1156142c1d02c3d0f045009240c0a400c0d0003080e401d16170f0550b1013002001c009044c6001c0320110b660b00d004241e4400110307444020300304a1491b6808046078490080c0c0d07001c003500e010000d650021040c0da8a070940052140380440200b04074074180c1d00001d001140b0107034010b16041c0440700c1c1e100d0100205a03150400c81d41160b001e00e1586468 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 966666762 1250 966665512 966665521
    0xb03120c010b0d0803010e0c0d0507030b0a0f05061c1b020604030e09010b040b09040603060e1014150603150402040608011d160f120612170406120b0303130e 69
    0x91250b0003806005668400000e0519198a4042c1c00140f181c0e035680411000044c010b8061101030355070006407802c01740150300340918058050701c9005103144c082c1601090004010340051a84801c07039a020340880d14080341c04100100030200d40200c000c0150700d07084036080c0c00400c0300304060b002d101540517112500700351400a1034156005481403084201e02c006120f5400303041c044404135004c030360042d90307904070701404a0041e0246a00240c05145429500030002201003140c0070309000d40708007040380d0700381c20b0005e008000058510b07142e24031040c2200d05560a0690003140c000d40c51480010800c00ca00c40020241d90080e00941c0010b101c40f0010044134080203801c1c0d000214a1861508528202c0d1140103590300c150038580800245124104159000b8040380c0101c65074801e0030b2000702c0d03c4113a080c1c0010010001201e07041c902604166106500c5002d4900380c4d2016980c40e480700103445403d40141600300744080e8503000c00c00002d0b0a4015028660004003400a100c1026140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 966668012 1250 966666762 966666787
    0xd080405150103020310091a1807050d21200c040f051303030b0117041101020d0f020607030b063709120803130c0e061905030613060b0312 61
    0x16184000ca4440801c00060005a4021440704010300400d800000c000e41c1c0f80c00c1024040c55003001d2601080c030b000c4280280450b00c0401e100c0581004401c49411a55034014020020f4103074401403c8001c2820385031840500b10300c41e59031241424076003000c803500050101e08407140602c040010a9015894855460a25004a4140004504040002e450400307202031541540040050030165104100c40d0541c0c040c070080328508030038212441e86403400e46400b00c03e1948004055000d803080400c1c04107400c1c80340380900006c4225501501141d1a900e10550140c14088003456110b6018040c0b05240031a0149200f0340c0c03485a80e8418029003a41280855280c86031011400c1100c0c460081c4241400350660703810203a031200308981d0301e54031009266154552010b008000d038480503000100d28020000d003a02510045403401e0b5803c180500c1607940d1581d40c403610fa0507800c403400042c40407038032804031039990f0f0040501040c02a01d120000382804c3c840302011040c02030200354100140c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 966669262 1250 966668012 966668023
    0x1d070f030b0c03010b190323010801060b04050a06030c030902061612050f0a110102070615060f050406081302030f070801200702010804080c010b1e180106051602120d080405 76
    0x64034035002d03103554142000008140b04105003804406042024490941e03c60b034048801048040d190144d00406d030345200211000a00c0340d001550300700280030a039002007108440449070300400c04c400c40c0d460f00c40e00f680680400e802510a0554410136a80035807038a0f0020035510081d400d07041c0c10b01080e464540040c1d00516844410850b09000325000c120015003150125400c5060807260b01419095540c0a4490b00c10002c00e000d05016030b03004404c0d810000b4100f0f5401c540c5a03070034481e00c041001c071100e01030780c402d54001503090720118a04000032410140d170103001405940c0e58988000117107140c20b0f420b03482242d00e0381d51900142451080507400341e41d55003031108080d1410100ba00000e042110140c8098800c001c0040c48403072100003580640202c00014001d001200024902c4601c804c0b02c52040e14000d8968021340c4c09075880b5100314074141c400545800381400c4d010001d0f81000011100200e030450603055403401150070030455003070000c3d00c0b60b50707001c883c4c030300b61134800e0800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 966670512 1250 966669262 966669271
    0xb0f0702010e0705010c2301060807090207081207022a0307080c030a080a1b030c03080906041a0c070614010f12121206030602160b15131d070f030b 65
    0x59241c0080c2c50b19001000c580e400c111842440c0070307104010181041090f96065402c04201c0340030214142c1513489040d04820308075404035081d03038074466580080006038424280020101c52041140c801e40c1080250015003001c0c070352046860f2003000242400e1080071803111103414510440106503245010880350001c0c01060015140000107078012955501155400a10306400890002c00309445003034601207804405850703460000c0f00c0c2c10302a007444000c803019000070f40b8100004905803400180107014540c004500d8120303114100000307004890140116400309400c004080110f50307140501444000e10f280a0320b01c6502d007150171075282c0c0340b035400041c2e5090011075040106001c40c800d0100c200f170702c3c20039030105015003c0c0d000040402d508000e04452000c03404034030300940307a0361004000d40f00b20380d2004107440310580c0200074115040c01c0342e8409581421809070320407507003110703560328802c0e0400311410003040e000f2820050260403403601d01b0780100b420404c4c4603070724005a400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 966671762 1250 966670512 966670517
    0xf050403082a19030e030f040602070b09030d0c020105091e030c0301060e0a090503041a18030613080c0a060c020a1a151909111308070506121b04030b0f07 68
    0x34094424400d2142c05072100201c8040c41c0e1440b141052406030b0414004a03604106031ba68030100396410b01007641150142400500c035078200030420708800c0b000c99040b114014028403c1c2c10441cbc01c00c03070740c550402c2c5c0304904115091101c0207464880300c4020894501d10010300d00c8060800041c11718000f6003840c07840c03080e03051030402c20403840303c41c13445500030303158110200e44600d103420704525501c241da00c000104140c0c0c41044046013150000f61841c41c40c030b5100d9130192490442019525041507451070f040d0361004c0741220000701c161009000300d001c00002d951424101303842d4901190107072040040542c00c07401101e01080001801c81900c0f00188020f4501402e1440c0c0c00c2da00401c55507001806403c500c990f00f14000c0030000a140206a404014804030190b50814803881d00f015400d0b803003082104d0340129007600003049601c2a5013000e0904c50812000151400410a01600703800d040300031120707200c1d0f203c1c0c1c078603000b80301460142c42105094140010759904440004121008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 966673012 1250 966671762 966671821
    0x2070c05151b1c260f012306040b1c110a27050f0d0629030106031a2206090311010b0a03060213080615030105010e07140703030f05040308 61
    0x702042e00602641459665142c11500703940302061484c5a455240918030141c01d50f4010001080c417402c2c0f20605982c00c08078142240382c01408003001d840c00004055511010a1009100320444c440140c84400b5000030091b1021131300f150311b0412a0940032130303100081400540580c0c10303030b08000303010b044804400b0640511200000443c1d001305107402803501c50010360351000d03900e56501800502454020700104806016202003200c0c81c41010040941c8680103000c0c2126440c041c0304441c1100d03041000480001d0302403110003203050004207ca007460000c1d00303800324601030703d90106401701e210384000540f0b8100c5060251580c010f54040e072500381c1c104050949603840304001c0e201120307440100582c54151032201100c05c007079107030010700c00703031042004200303003c002c2e5200140d8214065008200603602c485003038031143c41c115612400302d03001115031041100b0b004001c0000c140a4900011000030005c54041070725020740702580000c8900041c40400c0c107248500350086114102d4521 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 966674262 1250 966673012 966673033
    0x905011e0813212c09090a120305011a03090a020907050c0f03030105040608010b10050d09120c05010e01020c0c0f3007060203070c050402070c05151b 66
    0x421448031100308004100000c0701003901541109506008150700c044883c00101c4040d440080040c400321040300012184c035200074070300507418204405000c1c24510100c003a5905410301800b440081c210f5141403080c00d40441c0894515036001031500c16594010405514000b1081172406860a000c403c6040c00c00510204c0f21000524030001c59043e5032181b00740d0b03903801c1c2c140c1d0107005400703240007507001e034603825820035802100450503a8000c44040028039124030840e8200d8110072029170300903d0b121841a14039004a026164043d142da40100700e01507282d68981c091424000148080340410714403008100003030141e80401d9403034034000c5051090b0b0b48143c80c0e4810030b800880340503c0e00300036038003e41c5c2c84a00300e000f07520074078044a8074016498400c002d2f41d0aa020308002d414001e141c1c0c0420300502c044201c840c820b81100302c0d444414203060400c0025030221004440300c0b20035610029464507840c040384a80001c484501c0e445407a03029401841014408102d50250000210503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 966675512 1250 966674262 966674297
    0x403120e010c0905100e0901151b050c060c010e1c17070801090e0307020607051f050c1c0f0905011b0203070819021f020a0314070c03050309010603020a0b0a090501 72
    0x41c404c440c1c046483c00c00903145942c05880c00400d80f141150030040d40300011907410070141c1d412810b2146607440300081c0703100c0d601c481c0900c00040801001600107680d4040700e0729020000d03040e83d8005000014805405032080b6107043c02c9414010301c3d2112840403d20700c1500304480102003000118060100e180c8290004c159050500940d210541e8402e010901200100103540c0c1541c1d000e00030568615050621076550700030180c200d0b10810320305048049004d06801402e01031600c4401c1c007410a00c06010900b154000029422003050381c0f082240740d00d15040c02a640380c1c6008900004900006800300c901d01c51035850780c4c2e401e40d401040360708005809001104e54545400f0010414107000c25404c80c01c040c681441120b407002c0091040f8411511540200070b107466949042100066142400303031444001c41b0780c10042400740000c807000c17a015200031540042d548000080160f10781d800207040d0300083d00201241540030400f404001c1d0400020b82c0945801d08102001c0600740c0d122 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 966676762 1250 966675512 966675527
    0x6060f1905060c0a0f05070306050606071a06120a1101091508061338011b1103120703091e03051009020a050a03120305010b0310090504080c03030403120e010c 70
    0x1140d00424000030060f4403d0010b0002d1015076900180145600c0210704016a980b0030324041a2203040c0391201055031442d1002c00ca9070540c2c1d00c88600d841a03c886640c80c06401c0c0003c00c0a40c0113082c00c2e1231105103034070500505204510542d064041d64501c440010000c1c074154000c56000d900340390043d407056821003070780386d8400f00c121103a03455400c00a60880261504d5034002161040b505420102400840408031900d50900144080c1004d2500110740079a4802601844140d000d69070002280c12000e0310403524101400322038264008207440d1600d503108040a5002a0b1140400d004400c11101444511006003c1c01d07440b842c00d648440351150080300600a2850b0b0315170a0380215103590000c1d4005000c01010240219982d00f054942c40c0f039811441c000107407604002041d903010440903240542020440c00501c5400c000f080b5006110241056990200900501c18207480400041d80309038829034880c440c80445404030800d03100382020300b00d503a034100f40c1040246076000b8032 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 966678012 1250 966676762 966676769
    0x20a03030f2c011b053414160b120f270f06040606080c011d040b030304031202030406091703270a0602010c20070b210906060f19 57
    0x4000c1440314034880b4040c0100428544900841040d44000700240d8000e00501513516006000b000d140748405146051a012044440758860003c090320380404e00d2441030204041c81c0104445690044483c01003520304180c0c001071101500103020201200800c02d19504010016100e503802e041c070302c291000440403d01103180350a0511240b0307040302c01c100406541403030390744192162410203061500207003c1c80c0c010029144606641700d12103520482000c0280d0400080d101209540760003003001401e01000503551600c0103100220102e018440c211914440710f4000b5507030345181010280c0001d4130f952128042907803089c00450840c0d80441129040e0f12007080c480103410340582281000820075400c65003103201d00304003007492a0150f00448108145442d41840480e004403c06d4003840031517130301c0300c403034016013000c1001048030300142000207050180700c00c492804108041c14640b086410000c250306c14000e0141c4ca00300504e03401c19891054401c402100390303030021448040220310 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 966679262 1250 966678012 966678071
    0x60e0a0e1617130303050c030f01150e090a0203010806060312070b0a0626010605100e040506010c02060d050f0f07080708040503160302100c02150a090f0c06020a03030f 74
    0x4121001c4600c140882071802d01c00680300000c0781010b4008400380020744408601203494140826214035941065910682c43da042070710682e0308000c080c084460700907820506000350702c41c0d911010351700c40300c0e00343c410a240d140050b160740c541a01c0e14078140002d44182d0003504084845c1c82e2454402c0e040302d4240717401580700d41d01c0e51100c5480e071005241c1648400b1924480011913145622404569200b100000e0024401d813500d410410920520203490304d400304100240e18040c80c280740d041958030010504001036091595008100d181c1e000c00e540d040e080b95903200b000300000080c41817a0b0072007140003102d1074500d00280c1c00342410070054900014402d031100045c08000040045940030400d1039840c07001a0820300c0d02079a01c03000c100c82c801d04141465074030102c207440042d0031450700e07219690020300c3e5200e011660780141003a030b106640300b913480030111004c00d4801c0020307001030070303154010b0071039007a5070800804941d0310b05020f1154034100940c0007001c0c00805112a51002c080c17 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 966680512 1250 966679262 966679291
    0x50604032d0c03420e0c060f0d0606090302012a140a020f0306070203190509150409141005130209030a0f03320a021009060204060e0a0e 60
    0x3060000c58101c000000030110080c100001c020048aa4a5035140402d482c000700000d420070700040056030030345215082281201400c801c80705030250040051136140001303a440c41d00b40100480e086604c400d0800d286000002445014007205106a20041c840307031510f203640c1c0c1d003958002071500707030718803080c0030010381c3c00703908034101c503c01c18404919903402421000e100b41403c1081d9211104004260b00c01c03440803016026a0402140240c8a44003507406989031459800d400c00c068a9290a500100042844840d40d5900c8d03a000098000d0300c41c5180c0d94a0350301e0400751000b81c07180000b4085035046400203106411b6005420b070b40c00ea0f03e00315129043c001e14200c248001b40549400660305103d415080750501080c00340301e80311940031759924980700d081050740d00c01918040c900d10643c001d01d260b00000b503a400c2d034087c044002143c8103840b00c4442400d030754020b4900c0c3c6402503d410b60300050801a40c2d4010404403041034050795040d0046290a40f100143d802c014040e01000226 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 966681762 1250 966680512 966680573
    0xd050c2716050c01060608011a040305121e040801050103121d120114010905090606180a0c0c020d031121070b04020f09040b19061202010f02010e0f0c0a05060403 71
    0x1c2c000e440d0035800102c020400140d580b08000c0c04130b042032051107a41043d46550030102500d0504840c152500100180060101030985074619030201c109000d000c3d05500c6c80c0600c41d51400003c20044c40041c0012941d9410b40c1800c80c820007238042e110045c040d0407090b800365149021490b03d02448200c074501030541d041c0408501401e0f001c1c484008440100c030000c50300c00306540c00305c0c2c010398001d01166600d995007024001804024039480c2d8011107440005520700b0907540025480b00780030f1510200401c034039804601c2d9040d071101c048001c1440454a0360391060f0810810f0501c00c9102c11312201d000c451550504180708916000d4110b040c4940041e040d9121200302108401014000c1506440e0504041c3c0044400b03480311082c2c10f407018180c42001025024040c103880c3c1000c0060000115640192031040c0443d0b502c6043d0354807075030f00c640f2000080c003c10b11510f0226000d0050400c2c810100010500c09030031451198000b44001e2000c0f91041e01c05e071000000e1010481d600c03514 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 966683012 1250 966681762 966681767
    0x60302100c150f06030c05030c0a030602090301110d0906050f10030323042706030c06080403031103181225080706020409090b060a0302100e040207020d050c2716 71
    0xc00b10181806a0828503183d40308400e991000e82240c1c000c42e04200000e48403402c02d9200d81c04400910360181003841d00f807000c204150300030107842400400000301c1c07145090b4512615080940a5889145ea4260704030030302040d405482d521044003030620083c0d2030092084001c400042c080130b01003100b0303940d51001c0e401c5002403010751080c11080090710380d645c0300300c92020302051204200b06401c042c05e02213104d80141c0a0101036a03071118038000d400c1e04200c0d0413650800010310a808041e254100c0ca00a0b070180c800440c01103039035204000301382c42d0101d0b0035807501080285100c03c41034100b00c1c0e490b400a02101107400700000140b4594640f16074200b40781d0900905002030300f442c0c03000a0009143c501c41d07000201151007405c0d4420155515800c00000c10514440a500520031900c903400d614450300e40c1d0304104100400060a085007030300403e46d041c04da100120b9241c0e010303400a4540380b500301049400d040809024410100060070f400c62005c40207400e001030754446030242c141c03c90 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 966684262 1250 966683012 966683033
    0x603010e0705210c152731090813080a0c090905072301030606020a051b01050c0102070605041e03020c061b032206110c0f060405030f030c10060302100c 67
    0x141d008010a1040a10140c1e00c4441c1e0f100e1900d074010380181c0c6448030140841ca0403002141d0f40700920500441540e0041c480703015440610030001c2c80b440c205c0c41d02941fa614450000c02c5800f85401d10b403190b07902008012031076641e80250401f5030000d09010b00150388402d101040c0c4240b02c80200d0301042d18074004d891304074150004004505d420f0080355100c1d40503420021205000d0380c0500c075142d5114000d9031100d0000700d014000350801d00c0031140c45001d00b085101503040c10f150003403508007001c03045400c9030400703c030807074010342c5500034041805803088007100101c5d00322041040304103166801075540c03030040c6019070107000b0104919000c80c012018000d6021031600540e0303660401c225109488010641d60510710407610040400c406101d1f18129088030740803401001418569000c000001ca00030840a40c0004100008034031603c5c1400050721100f100001503499003111f01a20382401c02e8203181018283c5807100c100007595580203508100704090401c000e0700c8501c0d040c0301d80801c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 966685512 1250 966684262 966684283
    0x90b0604060f031b03051b01020c090c030411130903081b0f030a0504020d0b1602070f0f0e190e0a15051605130e01180615051b1f050603010e070521 65
    0x5007e0094454030b080c82404042c03e80c007400741d00b80d4050661410800604400c10388417400e03080010320025002810a022186084030000c03d90038142c1d01c0300700c0800a5410381041100004c1d903c009208a41c48139041d204819070008032110300700240048480700e60301006103460b55403502d52000c141951140020256040c2c0c0048101c5c42c50700e07000c540070340e005070b2000420006200d43c1c800007600c03d0b15082260141d81c0f10540301100103180804448103164007808403a8038007100000d02500b00c0181c46440105400c140c0503104180c0785003058205980c02c0030000150342c1c00c1c60100805a01043c96500e09606a03081c21a10746042c011101041072054005141c040888400403075036400c01c588603d050b07910003800f4032000c0e860700e82c18003c184918910300041032007801605030250b003004031000070340816801c03034001c6000100281024903600909110b880d58131000d02005050038050082941c0d4070070001c101c800d24200108020749951410300140300d03002020105d0004040c04940c903034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 966686762 1250 966685512 966685523
    0xa0201211116020906011d120f0f0c0a08030f03070c0609020a06020f01181a0c0d050123010827010f0e010e071e06050307030b03010906090b0604060f031b03 69
    0x4580a0b5008511910b500b0745040e48201c0610380054895031092080d59944107960542e0301e40200b800050040c50411040d454415002d01c0000100428003008418540e000090003031280e00c031a40140100446640c01c000c00070f03002006000b0441e2900011603070450b6840c545800301442074100500202503c140003903002e20241c40009540d640011511904600c0340001c01c1742030991049001590a9001d00510b1040361920040129050741c0200740d200c007070002240e1600c4500202081100d01c02d0300407050345050070341c0010749401c2040c10620070800070300f88084641017092a04122410011203c584040c55612006034504290000e031109001c840d070a11400030200e1045018100c0d18008155500c69204000f030a001221020b406020200c41000030351407d04c00211801d50005180e4810b0580311800b06d4510345092064100050090f0000210700d401d030710f40740c004044060005845036090403070a00401c46102c0301401141d62200300e29081034410550340c00d0100300c0b40d00141a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 966688012 1250 966686762 966686767
    0x90305060408031b1809010906270e060916050103020307080a0c09090f0605150403021012091403030f15030c0d0f02090c070c05012c0103091415090a02012111 70
    0x284c1030030541745440b5450040703402d01c034140e0703d4400001c1159105c0c447c0d0440121840f260611030316100b2241d40e0070740d2610101044d1408400c1c010cd20742071080ea441d0b28968410003c800c06407115082c01c0c0040c150919041d4a10300784060000e001ca070000c2c201e80d801e01e6440000d140554040c1b601c0d0802000e501900f4040042201007902c01040d1a11680c0d0260165240e43c418050082c000c540079a40e0042820040b00204241220181c101e101e40380318499584c150741e004200700d00701e0000d02d50740d1349004564038036011090b212051070240c5003800c59070710421682c03082c0d50040f030030140003032090b80c0c82000c1e075109040980c00c00410400180d0800320030f4051000481c0071400074003005000307214140716660380c2d4004403800c00f04503050100340c2a52203c60901104c1e031840b03006180205140100d030175612621100010319500b400c80540d5808801c2403143d50581c04001613001803104090818000e850300040c00c0041e448540c140d000901c202100d02d07040069202c0c00040065070342c07054 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 966689262 1250 966688012 966688027
    0x30c020a140f010b0604030c15111009050c0415061b140a02011805010206041104090b0718050f03030d0c021f02090a05040920130203040c15090305060408031b 70
    0x152601000758042e4915401d0804d500b009040c05402c440803a64008101e0290500c4c042c10807030000d000c3e10040081151403001d140310403c00304002a80007032010300001c4e41803600d2800134600716006203c18055410510301980b501c42180409044420b039041014288003c21500c06050345c2c80000144051a86402080c4581c40000e00c14540c5100383c840b64001c901283c1102d1840380c50344100c1d80160301000c00140003440e180b10302850803078050000314000d0000e40c1c590000c1701e02140c0300b0001400758800701d5218002100c118005200556443c0202900030b804262207100345024207460759140e46081c440b403807003005406820082404548107a40510311400060b5000701c0a051290700d02e044003281c5464103200302c4400c00e9000889021010600144051441e0001d109540c4414082400085140503000442c82584164850034003281419070540040128100700c20400002220030b00010f5030008696070090f0304004040d45039070b038101c41c25900910b000943c01c604003001c03c504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 966690512 1250 966689262 966689303
    0xc0105011d010e010510050910030b01031107050709020a0e0928110703180f0306060e0c03040f0803100b07150c02030306010509060d02040f080f0f150601030c020a 72
    0x5810303604155244000c0301c402500300c29101c9000c0c01600009500400100318905d0911142e4420841905080e404c01c880c0600003441580501045004a07440d0080a051981c0c10700c01e4030f00b80c001c000b19550a04526899465452880d8050402440ea0004135111058011042400c2c00701d0020074000301032504034244060b98400481c03a4500302c0a01d030b40002c00c0c0c40a40502003105048801490904c1070b2a10201c68860440402074003104030100c0c08102d902c0202101400303103026820100c1c0c40e619002c060540018010010092080103009010005038034404076009030b504094110b40300d407a95005803c00c030341140d10404840034005856020000310046852800ca4203801c1001080c01000c0b00b42d88034801150700320b0001d0010850300c03c840c503050000d40b01c046040309006081c5500c0300c014024062a41e001030340690302002e010703589084200001c80254074110040c008a80410040840012025215506164540003007108180c4208803070380185030410118043c0c140c0c0504403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 966691762 1250 966690512 966690521
    0x12062806050702150c1f020702011413090f0e0f0106060c081c0203010312021c1418040501091d0d090e0901020909180705090f04060506030304171b0f0a05100e060c01 73
    0x10080a081d4015125609100300e200380c8101c0358040c1c5070720440d102f404260901c00d5100b0031104807400000500401c8400e018890110f000d58a190b001035650001e2000b44c1c9002511403488040384e0404106114043d402400c94078070540c0302e0310081e20346d00c142061801c84d03421201d903018030b80c1c8040000800e0140c1100c0d054030411558003030f142c1c210801491200740b26420341c200004100511502c0a10110341002401c041c402c00004000d582016070000e0103458080c0e1003a5103442e15402449804580400c9128904001d20014403e203040408041d0070040c992040c04000c004180010381c02c11400c0d01161116080102002c1c85031400708101c41103a100101800958480d020020a940c28404109800346039000c00f03400c00ba9130b440d0303140030140c01d0081c410354040c0024880001c0c000000480c10107042e45d04009400d03c2c40c030380c101e1186030854003608c0d42e101e5146410100c0f02138a80d000b80c0c03001c2d80d8041d41c41d4400b01c60f075a041650045000700d0f00d135401c03400c00643c4200d00b400640c40b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 966693012 1250 966691762 966691783
    0x70902030a021b030c0d0f0e1203220f030201180801090b010e2a0903070305100203011505040510120209180906060411190c0812062806050702150c 65
    0xf5500c2410503d8500b09589001c0c1c14004102a48501080100c50f030003003143d100003410501d01501402000008908600280c4800000303960011580c01c401c001c840b941c5c011601c0e2200c4418648514000900c1808581444040d06000c2100102c600b060b040316043c03405864208024040c2000700e11704624003440903c181c0f24014541e00100e003d18425584059410000461003181024203284201e850380c0110b0702650701d48682c1d00c00000081007030000007620740148500588070b41c0b5001c004400b00541000700003c0001c10041404140d40700803401c030b0362000620700b90101d83c8000450400911455001c0f65005210742c076104100e89503851001d119456160684d41940c55100500c001d9501011400e440da15084c0441400b0007070861100c0c4045050340b50000800c00c958072500b51541c040c8950700301214140d0200141c5060030640e8096858401850b0080c0701c1008607190717030425850046000304240066684250341d01d0403102d401084800041c035585244000400c0d80c2c6940700503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 966694262 1250 966693012 966693037
    0x6150d2910030b03070b09040914032709040f1104020c030d0b0409081c0227090f060114090105090a0e04050d08091c03140703051503120a030e070902030a02 69
    0x1c81d0a1141e11a0040d850b9220700540200001d904181101c144c0d43c10004a080e00701d96990800320200d50b400348200900500030307010719603403036214194582c2c20b200c2c101e01070944140c8a0015180341ca40e01903c56006801c045a05044001c0c0d1400054110640250541c014004100f002d145a000b100a24500d00848000c10082c20400244403d071140030102405800c001e100300c0e44096500c007455020300c61482c074018680440d1b036548400c14502c40b10b41c41e4144407c148035882e00e08040042076004541c0f00140f9040e0b2401a0000f0310103101500550520300010a1010999004106413003103c0e01c01056a00d1260320303510b00359000b00088500742e42034810900010000c074050441180145c0b4810040c003117048208550703266109401180b40304266603500c0d507840c200503101c0c00f18041e4006540206903800d00540000c8010010302150307110350801001740410003101c070202d68286a003403e010402e5401550141d0412519034451a806400081041680742690b1300400344035100f00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 966695512 1250 966694262 966694279
    0x260a0c0503071a160c03051b130b10030c021609050f070801140105070f1a061318110604080609031e0f120a11040608011d06150d29 58
    0x800c1d20724070714914a489001840400c00c41041c0100349499414104e41c0076542c3c100e41c0c11303071b01d580e4203241a2405180f4259590850500840c0e0300d8051800c42415084040903c0035040160014071900841d583e22410300d5922251104018000d201c84984850b4101d03d40400caa51010031700042d18044588a01c280100c04c005070009000b8014070341640d0031aa0004e0546040c400192007d601080055806850307074001c40c00020811000780c81000300e184000320030342c2805d400384001e18100084040802e810807210a20b8004401480c0d00480e410059411052900001203140c5215a40007428180650410021301400c0000103200010821200030040c030f03120544225980075064009840c003400300704070107807000118a01070700071030b0b140030001e25805ea44c403580155074800d6000d100410008401000010702c5c2c0c1480c0c50340c00c8c0340f1110f01d60080c92b100001890241811488000041001c60214954880d5500a102c2140340049019058442d5000412503500044129200f0101d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 966696762 1250 966695512 966695519
    0x105010e0c0708030403020106090c020307020f01051602041d03130f0e04030c0b0603070f06121104210807060c0917010c080a2a2016260a0c050307 65
    0x10640092188030309485550404101d540d0b00f00c22980701070030550440d901c8180116100031144030f40620910a50020f56403521036205100040460300d016070b06000080c000300c101011400b240f442d40907811100003801d80803448204820b012101072045007407002252a8030030100105c168011f49030741d100080c0045a441180840d043c0044070018002811405000300060900800301c7d00841c0003025035265903214801c4224030561580400001aa090380318280c004070f9100380d0004204202c9624645418241c0043e8510101c0c80c804e28210400800c0e581888194003d54810943c007400500c18580c1202d0000c102802074000c2600e401c06888105028000c14400c00d899000d5940302d403400e07a503c004c001c41c000e144182d020400402407101c00a59000004006040140c01c0c1e210280d103030060042d10b213180320100c50580400d0344401800d9a00d10340e181018000c54041001d00e0348045060101e280c0c680810403040b2a4a204030083d400820608110010503601e0070780850707684940d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 966698012 1250 966696762 966696779
    0xc09031501030302030d0905190804060311190f0207090510151b060b0f040e0d080915040f0204090204150e06180c03092e110c0309131814010501 64
    0x20b100040140e8020010300503115816000146518024003d40d0751084903440100345001000d5800c0b40c1d200c0c4009000d06c40d264061080f00d002401c480042801d11801d07041080c0202150044031040c00714401c000305004d4406c0283d03501505e0065420f124a040c1862802c502c00c0c210300400c1c1100ba1101c103c4006d42c0d105071006282455540d140581c0f00c04030b902e070500100040e590040e00548a0924410300d40c442e4090080707000c01c000b004000d2100015001807090b00080c0100344260040c19481c4130030450020392540060304000100302d111008c0c40020000c1c20003400003508030741064203483d1000218a9a40101c0f0045c0b00317040d0321550380504004003e8402a42c40c1189000e100c04a40502c000c40d0155074407200000803110141c01e0b03542640024208607c10400281080c000d0401540312805440c0c0091558051b080c240400081c4942d10380c05881d582e1401000c210021103841500ea41001d58090201c14005100074a01d040c800d2400c07900e10740c55081c540c2480000140c008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 966699262 1250 966698012 966698053
    0x16081501092c010e120c0f0a0b010303110715031401050f030a061109030a260a080f130605070302070204050117121818090d080c031f0803030c0903 65
    0x2044464107680c0034181400e00c4480c400c41c50381d420080d944c40000f5440c2c00b40c100000b492403c00c1c18106902e40f2601003000e8541001c02e09020030580140080f000055908100141969814203082c004c41a000d11128900391259000c4035102001c081049403054043c3e004012003d8002c803183c0d90b45c0c1c2ca40050186c071030108040b280d00342d40211000c8000c01c10f60703408422454400c031402c0d0b19004100740082c1c54186070754400d4810500040c0b03e03035040d64022400180039513800000c1410080d124502425004005201c500c040074800001032003201c0c201c6443c0201a032041d420002c500381020010000e40003144201e00491902c0c0010a4461980b03401440c0240440002c000d0500c4141d1107400680203040010200c1d038640c544094280e41d00014840032841c80052a11186441e494841c50818031130000d00501000500f0b0280403070007907084903444400d000520041c40700001244204008540c40a40d060202206110115003800c004100c240421411680440d01d40e20004103042c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 966700512 1250 966699262 966699281
    0x120210050c040b0717071b080d020a02091503060103080903010b120d050f1306021f09020d0201050901050c03271002030336010504140d0509121608150109 68
    0x8000380030030080c1655400043c003005209030b0445e101140d20740d08414141d0458102110014000c003050046258108007071b074003c0c80000c0c0244900046180040d441c0c02014002900031041800041c4c14200450508460074402800700d5a081d039603410140c0c019004885514465401e21a00207141e01e0300b1180c0307200c41012a001b804207001d81d0741e420781d900e034003488038410400000c0c0900c81c800c0680b0401c420040c5090b8002d8101142e4081903200d05941d030f228401041481d0550300c50141e141c0a09240803d0350a080c8660703120404401a90180140700c18000503104c00100500c0e00856400040319040ca4181403440c00080da008000031030100a006000681c014000521880031207101901800c0c140b9034130198041c2c11006401e80440c100ca45103100b0f07074640c4280001c10100000100e80840a140a400c0d05107010350014002d1007868040d5200c0c91541c00003402c0700805024169001383e07400a0955100d9603106a01d4590f05501400001c20315100000591940c40307000e0141030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 966701762 1250 966700512 966700531
    0x706050705071e0b040803090907090b071101030f06240c080f092b03081006020705040f060528080303010b03010b1602060d06050a24080714040312021005 68
    0x1401c0000040d4030242400780c1080c1030b8216100000d5403403604c80140040c04108001e15501d440702ca06204800c60302512410401c11401001c01c004003910068840c0a580001c0481082440f0307001200649410fa0781703500d003107290280c00034041d803001450f042c2c80443d401a00000d0024080140e81c0380542d20f001902060040042d8442d6444140c02000568802030105d4000805040080d03030840b0060b026048a184014024041c580c0080a40d64840364100380300e00e038241442d8000b5107680caa032207102c4c0200d071180d4001c0c0c032000341504841c02401014000000030013540d680483c0f402101800c2d045079265400002c49d25000100842c1d0503952101e80c40e611b1646409007400241d070013180e4011702d01e05501c2810b80140d846000501030300e1840c5d0800700c0c0c03042c1400204540700c00b80d50310025000040c05000c0340341a0740c124010003485010700307080c9429503542005480b2210140c2a59921540009011040000c945e14041c0242e4069003100d036501c0c490740c0a0400ca0700199500c007007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 966703012 1250 966701762 966701773
    0xf021b0d05040509040f0b0403080708060f0a271b12050f041415010602031309050402030601030609051c080f07110a320a05010e0d0e06180d12020706050705 69
    0x3c50801491301504180f03e1010804e100b0074980320f05140032030a8030202c000604040c24172103c203900019050700048100c034103400350803504c0d00007100c0d1000c0388211240c021103c85045030310480c1a0b003041d45d1500210081c0b00003c4100c0f51118412455080f20012440d1018451400f200704d104440c0702e61006241083e07540c03556116145400d165040c026954880e44030002e10303c4540c40c0c10207001300456002140c0311003000c080e8005a9031590024103145152204120240c0c1d0005071584c110b035080000011030300da40d4100701d4107090300034002040c600065203e810710198000c00d4940b050400000700081c64607644011504001c200d8500c01c100e42c0561051404a0008c5610300e642c03500c14800b000c0d80442c06144a003000348003201201654200c1d82c140b006100c803c0c041d0380f6440a80c4400b410b80c48010510141c409103800d400e5a01803480800d1151034031000415030080440024115561104a454141804900903111034014014403000042860145007503840041d4408090203 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 966704262 1250 966703012 966703019
    0x1407050a090204050a0605032a1c060f06030c05121b030408040f0b090618011b03020f0609030a0206240a09091505010605180f0d05060f07050a050d090c090f021b0d0504 74
    0x100e144055516407c0f5040b420014068103000d00003e950348044801c0380460f2907031400103908cc541000e54032100c181030170260140350545d44202101c2940300e025504030320681f15068885200c4519408075260f0b403200100380018412408080c0045460044030007680c60b45841d900600f5005801030190400c43c18008160518550300640041c0c540c10b2525155400d004101d40c81c2c0000c42020640c003581000080d0041c44400f0b020007680182c0d0f2400070340c504606808000d5480d1001017440c0c4d00ca4440f5017101c0c140e884d1000c2084100f210061040312502d4440c0400030042092000072112103510f40914108400349004c0c045c100c0c0c40d2911543d08148580d01404220040c2c950740d03c1d84805903c070440595620f40d0f03c0101d41d44c1c05070004000b149408480013401d00d0026009005000c070a1010310300482c1e000c4221404610768110204081101b4a44003138100d6054012110644c10a20903016225040d4040c103d0040005d4a03c994143c9010019444d610b001c01d900c03001410801062 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 966705512 1250 966704262 966704311
    0x905040c0e0307061d030601050a0b0703030207170d1a031b120f0a0201170919060b031f0c03020324031510031202060907031407050a090204050a060503 67
    0x440c100365035420480244907940c000030382014015002100424400e5014240716090805031003044042940100000d5040500095089160f407103494a501400200039007098402c1d0180d80c0c0255203c2102c90504004d5078080710103402600390100c2d84c525190700010007200b40002c03501d101c140603010345a03e50007905054079031480a0385290b00943c82070002c1d009940c2c00c201031001440218003400c41001d42e0710006020346800c144000d00325481070140411104081021403c0d82003020480c5e135554070710b1030407001034901108501e41c5070140d11001002d580f8980e8425540c1554500100007000b1065415000c80c00141e40c00b42d1010507500708400211201006100f980758020111403003450805404510440200d030102c000e039001d40c00400400c45103042d86c0c0100f92650024041c01c0c501000443da580180e88405054180d025001c0804107805110038070140801034403240000d515074804201a60043c403541c0c0c0030300d000540000314144184281c078002c601401c4681e0b02d10340a040305 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 966706762 1250 966705512 966705521
    0xb01080601050a0f14090d060204030311030715090204090b130309060201140c13080303071733011416050606040912120605040207060c080a051519090903121803090504 74
    0xc17a030300303081c10050300c030030740d50784916109a052140b0300250361982545402420581c4003a800325807a40240003400000ea00307100b40c5000b40814100010706c82c0c0d01c0f070000401038140c2e840c01411a0b19030b1000d01c0032211031801454480c1c2c2c000e881d176421180d65038500b24203c440c81030a072210510404085a4003000320300041081c0d4100c12070b500001500c0d20105030540d801915010080303006110440042071182c001d86c0d42c8005000582d2888440c040c403074002c4803507154075070000c2e101c0b14102c80b0400e80c0680e4801c2e40c0c803180210303607d07194007a40800715552600001e0035282c41c071035200062020b2a1902031204a213900415590703206c94207060980f4500082620001d50603203542c004141900d582c409000200d00401c00451040b1031114064202103014000d400b41d07a042800300000d04d0401d1f01c40e513031030385c2c001d03680014558104610b804040c401a00107201c1e0303504010700001415032280d04562942200d1604000007041e9201071a850300420354002c0201d1a01c0b0400c211501d01a0700 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 966708012 1250 966706762 966706787
    0x40303240b092e02011b080a020c010e03031e0a0b031504031b08040306051521030c01020c0601030308070c03122a03051b120a0207021906030b01080601050a0f 70
    0x43c070100c0b4400d280d002d0040e105103d0b02e602c5100843d4800d0000503034240148180d00c1840015911403500d2404001d05200c00100b000740c40540001c0d1000c070081096104c05034600500d0181c80c1c0320300b024000d20800380226500c45125400101c040388101407544201c15240d04000d00600000c00070130360703403802c003d0014025000c1c801c00b15140700c2c3e5544c2e0f8010707000606200f10b081507911421031612000b100c502500c2540f5611202090500f107446003420008601000101d481c00c0004041043d49903104088001c0255400452078126a550000f6907e069902c01e44814850743d5620008660380c2402d540f01400168902c24450719144059000c1e15028400400c0008140303a1309801c4d5111074100300168000075512010000202c03101289504034a00c0241e1880c0340140c20345c0c10550300ca10240445806a6001410350704654416041256213011100301040041e13403004040c0c02000500740741801f00740700c080060340c1c40d8407590468841100d13a031520030504060341c004444107030480d0b1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 966709262 1250 966708012 966708019
    0x6050607022106040506161d060f072a080303070e06071a040b011412030f03130b040b10092a0e03030f1801020a02090411150a0305040303240b09 64
    0xb089030b04035141400380a10480c050300c02014030342031650418168180380b450240422400d484a0b00c1e81c21503052820000a00458610f51112020140c02e4403d101c0c0d060010060800348585042e0141e403a00b140c0205003c4d252002e01803991006801d451348812210103002504110740030810b885d00f00e0240044600410462558160b2090750440403141a54150341c640a540c00403c6109980d01a10303441050640c0d00038031403030354880180c5d03980c05840c0c03294080c0d68011000841401160035900041e982280d68640682040d040021141d5000c1d2b507c9d020202c5017003c0440e800c2400d00507500c04926107001e200d8000684151703080c03441002d2403000108854900c00f0592642d003000a414050750015540c0e40d02c40d803031341400720b0503088641024150b40003c01c1000140c0c2d5043c00840d400b68220201070a501010000501c202d040c59007103207840384003ca2000010395140e40150700c158480d407030820410301c00c0c00582401c10200c8111070000c00004509000803c22280580b1000a024 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 966710512 1250 966709262 966709309
    0x100f0e070f032a08011406150703030222170d050301050f0f180709051903030203031b160b040201021e06011505090405040506100923190c0206190605060702 69
    0x440f5003c004144d61164103942e440ea4008020030503206107181d0441c0c01142c103064143c01050860038180a03114000d018035501003a4807034a00f00089251410392803040001c21900e840e928082c80e50b03c00311954042d588680c4120100490080084a050340d00050036080e03002400010043c109101d51602504069488810b21890040959450045900b0303100c6901d880d0070f003402d1102020511021800b031031a440700403c04290088126500b14140c20081d004a038103203040c4c40341e81d01c44d440c030004c0600300850340241403040080060780540c3c400d030300781c48224208205040c07588602103002482070300884010041c8004014081101880320706080b0b043c032110f0000101184c000711000d41d044c0c0c0041e401c000500ca504400000a403000c41c00030840d40d14104180d5881400500040c00a80e0480700810b00b0041c0b0051a030403013008002044c001d007803074800000d4031044181c6001440c11b60041803004620910b000e0f00080d264090312040c03e008154082101c000d014944a0505a45a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 966711762 1250 966710512 966710573
    0x30402120102160305030a0c022a0d0c0602011e0b0a0e0709170606010906020d05090f0105090d120810032a080a05010501031e02010e01080414100f0e070f03 69
    0x3c00141a61a00a468460f01c030302d0300b44100c0058070449007140e0b02310341040c8942004110700e040d19681f446100c41c1c01c10450504680070a000440d011800f500703050301600005801941500b11706901e0642c0b0941d411034000341c0380c4850a449541d00d94950112452001344a13244034031490541c81003640c505015055075031060903100c2d45848050807100d800c00c000304140c55800030b50081c01015984002c0c1500c080c40c4400420b507000750701e0b08503c11811204601c040d60b10a81c1615070104008004050b581c84601d010890351b00c03156080000300d8002d80c00110340c400e54052240032260000507180b00d08048500c3d007048401702545e800446120350002107010f031010401f205210384140000509941142010204e581c52520380180c42d0441e10fa039140141da115500c20350420080c00c0c58542925540350004500d6583c1021520038454030891130320302c00b10381d0044484841305810400001e644001e0103500d0f00040d002d00c05189090503020800a0b01d03e4000c00c01e400c01801e1491001c910 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 966713012 1250 966711762 966711787
    0x6060a080417300601090e06040b060a03020304050c22021b07030b0106020727090302120a020d08010b180909070801090f140d0801090b0102071721030705030402120102 74
    0x41c0c1840a5958601c070b00c401e02050b6210980b0f0341c2c0102c10760031600a00e004000280403682d14000d9050b0b0304040c1000c5031813919581c0110040850081689840301603090000f80203400846040d607881c45060400e0345d19040928001c100145130b201000940c0e2103e410303001c0a90701181c41c80c2c0c182ea07031840307000403200b40c18405100a103100c2d41c1800b03180c0d450098000d1500072036030041d41318005800851030032061000010400f00c1130540011403003401381d090680c10000710405000031044000b80c001c003a142e01103902c103c0141c6a88a601050345c9a400c000143d0081d083c2e11300500f03d041c0f800b0743c854500b502c10944e11210020403035014984034115542595024481180d442d100e0310031413401c000d5100d000c001812000b2000700460b0011400082c034204061280c2c0308056aa146c6910269100340300704c0c00505a02c000e29180410f011110550755600000b80114000401362260004040003007160702a860035980c1c9819a101da80802040b41d1415402d8581c41d90b00f00001101c085 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 966714262 1250 966713012 966713017
    0x6040c0c0c0902030711030918090a0204152115111b0d080604020c060c0f1608180a06090302060a030e060702010606020d0e010504030602030c09060c061e06060a080417 74
    0x421680007684a04100b40c1c01b8040001006444145800c20300403400151258480d07050303421b4a01162010300d07140c500c480b904290303002c403020750000e0411220100c0351400c0407802d01182c100c10480061000300060f2000b0b1380c1c4030700343e00034425801d00c2e519a081e84141c0d00001d04040c0030881e0a49491100c00e4000340341240a1071940d5035030441d091320444d1a4200b669107500c6281941c0a51410305070901c031603111800209418400100031074056280609601136035a168a40c44884884108a0500308050b4201030714680350b180703c00e000342d02241024070304941241c04684661044074190b17800c0200a801c10301d614000c043d40ea05c0c040868200400125000302c9454000260150404d90001e0070311301950301c2601072003600c2120360880d9070300000b2201100e42000c00143c983d140c689102929201702c1403403036442440400d442c044c818000c60120300400b002c10043e21100801d03216040c4403039084400c02d500150502c10b804445020f8040c2030f5002d44106140c49030b081040803014083d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 966715512 1250 966714262 966714269
    0x1312111002010c080c070f0b10090207050303090106051206070804020118030f020f0102240408040302060c06010f050405040b010306180204060b071a091c030f060902070209150906040c0c0c 83
    0x50b0f46400d40200100e401900c12500032110802075440c140850700c881300d062029180081c502c070041c40002d800c440040500c280034042100701555240d105041a90b035035001520729458951911100103220f10744842c0724082092018044c2007650754083c401d580c0000003d209a043c090002880ba551402810a150242d4816034010b2841c061a00520951445205019055602054240c1c1d01c1c2080001076410302d49580c01032844596030352405500ca03004580c40203400240205481c0d2241e88042199410303500c51034059000560381c2d60400050350000e0714081d000baa060401030001c50300541001d010007505100d41040e182c1540d022074101d032410790190100500c003160700303c204a02003a1038072200281d40e03a80c90300c038205091000e890701a07205142d2a4203060ba4000701440c0c2c040e4000c4d520707284075990701b00700b101e55030280321000e54000c4030106e104881d007034005083c4031040c503c04c0c240d061020300340c2e04943d9074002c03c2c480282400080c80c070900c80201220380016200ca0803000c0030303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 966716762 1250 966715512 966715517
    0x2070b0c0109150e0c090402060328020406110f0a0b01151115090f030304051c11030301290c0d0809030d051305011803020a020d0c0b07060b1513121110 67
    0x64200c402000d03080c0300c490607081c6d118100344018070026075961400d0300d0700504010008008158012141c488200d43c40d8020303004c3c14008500041c900da04003003d90070030513030801900c0c0c400d608140c0f4035031101340311800100f0310700c180801400300f000010485030700c0c400b075810b05403ca12010b51740103140c41d20183c14a00131000050801460590500041138444542c100560850400342d0381d254a072015004140101c414600b181d80c0c03014414803480100710900401d484d580d585038030305412118a08103018641810b139440743d00003c4056021501c5010721000544100546580111681030000d00114000d200600003102d2070354140c401c15002e41e910250743c40b00314406240030f03425100054030014210802042100100c1d40120310381c600c01d581100e06105100ea20325100708500d1031508100740311000410a601003148550185108210460324010040d000795602c034141d108103601c0b11401d6a01210410601085948035020300c1e20883c40e44000d60b0f020000304580c041000c0d000f400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 966718012 1250 966716762 966716771
    0x5040e0703030306051816020309060c0f15072c042306091e0709120f02120105010b0702041509021c050106020d0c0201180b0a091706010602070b0c010915 68
    0x10141c05108840045c442941c0900c20048607080c601c6100034000d041c1850404003010103d0f200307200f4000c903a60300100030407964590b0105051143e48810403405104240705600c1d00c18a0f001070b5aa00620900040d07548610000c01d00c00c0480902032651104050920301309458402a5200d004000713400c1e110719a00d8200c5240c3c140819074141028041c640100b884400b400f90000c00001841c42101d1001e45000075500d03100d40442d806603643d48852072011103040d0140400080795a0700702c049000701c4101e0480c21a1120180c201c440a108d04e60401d00200500300c010704240d041221100a03603500702c0700072a0348028100517a8000c0c480c068007050140040503100701d05101d003a01400d2988002c0403180340b901400350403120f1440700a814000340e25440d001c1072041e035640b2000382c14165051500c44001e00b601400014441c0aa040e41405c40c00005e8001040021454102d640f9a8000e0600616000998441da1b008100400c40e55480302c081401260801d5024002c140b0b1450b000107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 966719262 1250 966718012 966718019
    0x70f030504022b05030408010b01120b090c07080c0105070f02060702010c08060f0a0801020a02010603170c0a200d1b05190330090906060f090b1303050a0f1403030405100b01030605040e07 82
    0x51600343e400100052f200e00d060305446060b100e40d684154416050490f0f9941c03a0f4090505d01001e0103030540b501820344c02e11040100b02c0d40d01420305118005d0301d40865080343c8584505900703840448000c00c00042e4898009202481e00900104010300041d0104080030b88a04c941400d981c0020800f00260f9120241001049403040c8080b074905a0021001c1c108030702c1083c599115440304074080c05071203181d000604018282c00c4100a1a03000030100f0022204a140c174140c841240000c0880961a60340300007914208200c036210f000c5d04101040d0841d80c00d5984000c81c001c8848a13250200b07500c3e070038241e48036031200c05a1960b0040c40e102c8404030352070000b550b0142c40d11908080100f101d40350041c004070780c02c0030305401030f81ca001e03072401d4460120600c90b508203a565840030b0030610503908510140540b80007000c42640c09488141c0842096481c603da4921090714018440d50021208403101d0b42c0e29131103040c4040c0c7c1450f02007035036640c600002d02900d888980c0745420382c00000341003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 966720512 1250 966719262 966719267
    0x1b0a020f0a03050c0d060b03150105090c0901080c0703090503240c04050927070b0d0509010209030624150a0f02010c1b06060f0806070f030504022b05030408010b01 72
    0x10340d0204040340d55148507030a50340e5507601c0e07a090043d1540507110b50244082040780903003010b1005c0381c0103011222440c0304a907a44411910070b00c00c0900070001c050105040261650407190b074400c0603120352440d40c558900e910050f0b440440140d0400c00755075000b24581c0e03018030404810f16900282c0c0031450f8850002d0243c000d0020b0070f029010241080100540d45a20030001c0d84200d92001191084600f145801181d0640e0042c450140c001d440012540d01c02d614040e014040701804100207a94a80b4a454202e1040c0000c0039896072016000504c1c12030b00c420501c19800b0741e41400f41401d4000004a4882008088101041d100214143c0711680d8022068a00181244004e1101c81468200544209810040340e218000344905e21010701c007141e08a40c00401c0d490b4884c2e5000c1e50f0351080c29840741019942c41000411943c0802c4c0d40e10b10078082d550169400400d041c8004400c042a005000d1510304169a88900e00c203084001c50003d1014200400e80540003040c2e01c03901c030000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 966721762 1250 966720512 966720529
    0x70c080c09040f030e03010e060108032104020328050d0c020f0406050603070c17190f0804170702030a02120309031212010605130b0703030c1409090406020307051b0a02 74
    0x50003498090100008504600f000e41c0500d0b4050521040c44584200402e000d4100d16140d554070b80705260002840010000091101d1604030128002c40302d82c4642c0340007c20f6058a019506030b101c031081590301d02004243d030600201c1c0c2155412064045d5071018241035174084542c0109100040c1403040d41044034a1000d014400c41d000c009650500c1d000030110b001c00380c1a11700308004042000200007940c41a1200c03061184591622144181620051098401c40910018818182c0c20324100d00a031107a0703018a9000080b00c0315154115504111900801c60507a030600ca44140c3c04096105c040c1d60071117101c101d0300a503550701d1184090624000045980340301035001044000d1400c0300408450741510745074500a81c0e41d180c7e88800d021034050700d403c401c4094100150000405805a03c840c1c2207040c43c0c1c881d40e0141c01010074115040c0114605640c00000c9040014005030091340107680c015181d060203401c080004a14540e030180e00c01005403070354400b8500c4410352500080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 966723012 1250 966721762 966721783
    0x406050a1407030b010207080f070f06020f03030a020d020d020a030629030a0b0f13020d0b0406080c12032203050105220f020a03021f110c030307020d0c030206070c08 73
    0x9014944100850400721a001090300c802c05a81d00c0440005030f20a01031074000384071700801c944c00403d03100c50040c2c07161030500c41c95100a95225001800900100e090241d80484402550130761f0389501c000c2e00a54045a0320018550b402c1001da28000040d03c0a8019503100b40c0d0001641810300703403148100a01408404904c04001045003210031105007101c0e8045111007020402c1e40c1142c000c500195a40e000403903100141e0803000b400d06400da80170700b0900c0d40c203150a101d690305403000d000444165005404641c2c000245030100ca06040c070019a5403071000c2e04a034600f0008004c0304454021244480e0084103542c2010000e108090250719044405410b55007032001b040c0ea03006640200b90440140401c10241c9600259526203400700c0c001c0d6000b0f0820100340c05a0900300d80301e99070401004020464850b200b81d54110001052070350044041c0046190200540030800703103400310b030740858010440650210060710341001400e8901c0c410003508400c0c84c2000e000038101000c000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 966724262 1250 966723012 966723031
    0x1202011b0905100e0d0f0b0907091404030f0207090c030f0f02030112020d03230a1e0801060518041a1509090a02030a140103050706020f0106150813050d08040605 71
    0x30000d200d6a991240b0804003103c2c40d0410b80700900c01c210219050701e0030800c01503c6c10321040e0b504000c0c045000605840f50340c500d82075800d00703600c0d25050340466060000355000c4000003030001c4c00090003400c04d003081c13912170300449004640d1400c100080d50580b1494400107a1229814500155280284000300c000c01c4029411581001901224456681800f921860580c6403620906024080226003082d2400c900700e4030740c02500c7d0700011075011342400000a50031986045411501507449600050160303a00001a481c000341212560060718036441d08055011104c0850394407842a285c0c20907560492801c03000c003a6040201642941c1c14030340da101810031800d8042d81c0e0705030b0920b920502c0c001c0300507100d172140b490310401081040e40300300103004100c3c00442841400a680e1040b0307011079086540d9900c05004150a031002031080194180401c800d401e0514000d07030b4466031002c40e811003080d6580341900e03201e15101c038800341c41011400f440203010500c00d860052035406800724 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 966725512 1250 966724262 966724277
    0xc03160f0e09030a2a0b010312020a0f1104151d010609080709020307210506040b0609010914240d0b0a1202010f110f1c0e0d0b090102071202011b 64
    0x20b484035912031080655843c01c002d542880c1901c40c85000311100d101c054210000d0f0280241c5141c100359802080c04140c0e442ea00300029807008920009000310204c2e07200301c200d41c00496540c7c80343d00c41100307003040b5540030b0b849000f41015100c011046a005028170045075819004056546241c808180c12400c2044128142401104000600c801c2181e102c0000165290f41e46e98040f0384081011a0300a065030030075920501c084140d400841c06039000325420400da911040400032a441400c1416020400c52481048248060949a95552400752007492034880c44200340d280c0d901e00d03210111090308003062540846410b4482c900c005d030710a0341d0020b04141032424410b0f86000011000b4100141c280150315280d1054140300f0300c4007440800c6800380505001c80c10b4a8242001418009107045140c0d02c5800340f01c0d418050414501070300f14070101408ad01e8411400000400071100d40d0b400300140400141d003040b03581ca2801d2030340d00010312450100048485040060341c90000c00c07002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 966726618 1106 966725512 966725521
    0x905030901080a06140f03030d090c150203030105060712020c19032d0b0a271a0f0a090201030f020310180204060c0f02030c03160f0e 59
    0x240c8441c000c07691401c04640413108544161364012442d503441d851542800108181c0441000e0f042d03034070340358400e18903405452002d0021601da1500c0d034410045000d1001d0440c4c80c4030414806140345516000014a541c0034010b0054000002041601d81850081000310041d90b0040c10614480c2001e4554003818180c0340b000740c803c1c5a0710703078040b13200108583c200200120410001e605800e103544554400ca0782c0140030310b0310685d031900b9403a40d100c0385d07e084171340540d24008280000301300e61815102050461594800f1002e054081c400345480f5034800c540d00c040c507030354009494401c80c00100e01501c0020010041c8078400001d0000d241030100c411b0302036034002c0c0c42040181e21203e035128124070480c4696000039601010003030000c2c000c0c444580c00240024119812101e4050000e0b007042e1200095078071040c0c41c0c0c0d00c2005001d0103071075010001c016a2032442c80da440c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 966546762 966726618 := by
  have h0 := BRFrame.cov_init 966546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 966546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 966546762 ≤ n) (h2 : n < 966726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
