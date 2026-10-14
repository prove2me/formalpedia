-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3568
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:02:34.986031+00:00
-- url     : https://prove2.me/submissions/346c7136-5fb8-45b3-8976-0cff4271961a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 641546762 ≤ n < 641726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 641548012 1250 641546762 641546771
    0x80112081204050f070b0a091710090506072d05070219080a02031507090b031306020a050d151401030c0302040e0c071208010609060c03170c091507020f0103 69
    0x420000008035400e400078075908034514101814026240d10035483d014246104000c00040e011414506580590409440c0c0b9603440d85001c610300ca440707000003810b00b9980112107000010100c5881125105030160005010a1500c0c1e44050094012795504526410000c80e480409a11541850b10580c81610300141ca437a090303c08203403540c0640c11000304117009070328080344c01400017421010311f5008030103d40c0d81c1c1c0c403000481c1000c18019101c4800040d081c0c142400515058002150424842c2d40c80c1c0c01b0404440d00d803071040740c0115450000140340050b60150a4001d80a01d08140e00d0480c03225480916001041203040c24000c1242d0503d074442d64400c4449002e541030b070340204141c4030422510f1407c0301040031690b00544048900ca49400417500a592064402c0c2d416640f1513102d0706043e0b410401c9c10303a5039032800002101042418000c17100308006101d40c06001d014480000358a400000c01004a14a00e401806841c00001d00603440036a0700c00410b0041031718203080018 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 641549262 1250 641548012 641548049
    0x403031202090609011b020a08100f05060d1101110607121a030c04050a09021207151b080d2403060f0b030a060e0c0918010c0306080a0b0c1b011406010f0801 69
    0x20341b050784c12000703035210f2007111000401d420041841001c1080c4404108001c07065007014070101e42c07080e40c00a40200b4562039840001e00f15001040b402c802c1418100c1e42c40c00c0b002041441d2010458a40c000540c4400031103c003c4014040c00d0889d0f001d405505e501100004082580e0f070000b4418188650b41300d1002c5241c1c02c60603440307804c200c0e40141c05540b03846a801512542c3d90281e100d041700e80d024041000a000d44504c80c0d40000000074030003a051142c02d9115044a5004582c2728410503035112100e0740715850411101e041980410202d00900b8590306020007221031800d101c443c06801c1c00d0280e00c082d5004144144116071255002800381c0040d6040c81c5450003013043c1680000580041c0300c15560740055404000206200034402c03800301441c110142c500e41c1c4100120f42d400800c2d210b001491010900b5071001d400c03202c0905008035240000300018954100c9609a50350724480b51f09070f0b89540103564428428280a0707100c00e051040180201e40512408441d02440c035051f0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 641550512 1250 641549262 641549297
    0xd06050a150801050402030d030b13050703020d06030515090706050906070c050a0e1008070501090b0702040b0a151103040e0705130503010504080c190308071b0b010b040303120209060901 82
    0x1034000880c4122924007403620b55180034001d15090310142d1003440380030384000d04a4401d0144a19080703000c0d00031900740341c500000101070701d0041d00c01c0c0c003450740900481c1940c3c485480783c44011400f50004003000c0c28100500d0105501c0903000c0140398200140a001c00c80c0c101080700c0403100e094030381e6035444c4180e00300b90b00214074a41245074041c00d02100024004660201e00e4094504480716804083d076911403a075842d0303010303c1494082640b10318208001e000d0000a400100d0000d807000c60982c1e40d40d40040c40310f8029411100030407000c1440445044d40c000810026140707404000c529250034004035540701c1c0002001da6007008000180303034200722640c0101c1d500410b40030300240501e051520344000c0a030030002030082c844c403c085403516002079035503a00009036019200c003121921a108203e40d1036850032502c0e103541c054210107000291005056034001c05210503070945036401e621b802001810103001036805036005129000e42c0d1b50f90354046403c02c110034204000c05142e011050f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 641551762 1250 641550512 641550521
    0x7050a0c1502030a050619051c03170c0a030b03010203060904080a0c051c120c0801030201081005031b190803030109051e070207090b030a0b04290a020c06070e0d06050a 74
    0x702210300201c03d020140109412042c010031048402c4506108207810000d0122124414160301056101e0104842c860514604003442e009140900351003200c0c4007100e103043c0068071420400700002402e2040950303d84030fa803000d00001c80c000c0d80f45042003800285020800f030000341000c1e10000b50101d003036015000c070b8103640342e2183c156a261014100c03d1342ea031000c1a00c4040c0480c140880d14542c0000910511140c04000c0c1c6900302103908503001110111002080321903c20208200491a0364040142034840415a0600c1084145040500c1050000400454000c000080d400e0140042c04800d90f030640ba4008030000d819540d0f40c42d0350b450300030701c40d512001c40400725080c000c0729540492254180e031004c02c818000d80c44040b09040c1d651201c014050300c1d044020000c200001c4140180404a21401d07204c0c14250006003040c03401818103840440e600755000510800c0a0000d10010364003081c1820800d017000507417004100c60381c1c119440104482d0b510000100d03104da15610 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 641553012 1250 641551762 641551793
    0x1030b030609150f09031801020102090418061508071a04050d050c1e0a0501120f33061e020f07080d020c060f1207090e161707050a0c 59
    0x4031512410030003080c58443c400c403a900400b603c103c00020701440b102141e84c070301803030004008510b06122810740403581058400580c1c1195020071810901c1d80c1d4601489860b0300c10442024102c0c0790303e00d8090202c5000c2d1651032034501d10450f082204810208400c0226110310715070701440031803904455228480c1ea041681d00012050080090000c00545540d011506171943c86280d40c031540c6d59101c1100000c3c0b223990200300c845040c0800d504c01e0304c8d0122055202117022500c41155042c07201030307440030b00e021441f0114200c1528507010000c0c2c8883c90106160400c024944d04001000f090000d101c41320900b00030200d00c52210052081020780000c071180380c00c2c0c0380100c0c0c81d42e800c1038039103070400b07900001440f82c8961601d403031801c807003100c00110076422082d14040e114142503016810080c0848240074180c03000103141041e1101180c4907001c0004407001c0c006102c81e02030400058202d0707040c00900c006042281403030f040401c8841d0301d4210700f44a5040c049078680105c81c1e540381c81 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 641554262 1250 641553012 641553019
    0x50303040804140a050a06050705031b010b180402152206020610080106050303090d15020c010b0a08032b0b060c0d030b032b030e16090b040e1b01030b 66
    0x104200500c001c1d0009841510040c28030700c101c400ca010204111030b16240039003a03000c4030021041150b18004c00003407103a24429402c0c4c5c1e060440c20308068000f94500e0102052594446808403518a030501211400701c3d100c212030005c50800d43c011861a002e02d81c3c3d0000700311000910000f25111206c0000509080001e41828060f2603030300094552030f05848984060034010404281204180100f00944002030010350910121380104040000a44d201359420b5245030440c0440041c20300080014403045400030501618860a000c500e8281d540840c8103034106000700c080498521842890038210494082d0f00036582d000752500038844d0840d61a0310440000d0b049214940201e0038600003500342e1030810203010b00b603040c942c40d000100c0e1002c091100142000070b03060070100c50703000300300781e5490300040c8000050401403406020200030302a121809800700300d845040e000340001c43c0d000340c40a0040301203942103ea5180c0e5803961511800307080c0600142181d100780c0c400c0d06c031240f008 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 641555512 1250 641554262 641554267
    0xb0306160e090a2901030f09020d120e0d0507080607080708070e0f060703080901233c0907152003090d08040303020609010504031b0f0602040603060f0f0305031903090503 75
    0x9813490036050590041140800d0501c1c1740340700740f12403510840e03d020750054040855001581c0e2404400171885c8043c0003071081443c546100c607203031040d0951001d807080c4004c0c505e0900b4000c0d00307450b159005103035100300720104007040845270344504c0107034202d00f050811240359150341c0001143c135042401034607080325021540c04227069205a1640c00740403840004c00c541352040903031100500b00031070400078034054000414010008010600704010031045c2520142074050808203441801003003080901009d841805070b0b02205104840040102c01c12407035010041e1500603003400c00040e8140600651f85514000807081403088a100c44e0000340300c404080c0b042e141001840c0c01c1804180d0041c4220000161b00c00d0052280b50301450301900c8036a00e0404400c4001c01c0e41103014007c84010b5458102d06000a00a002400c098496910041080c50901d818084d8040c180c0d0301c02000b004074480e00300041140482101c1a01c41c03894640102d03042c0300c1c1e00030ba01408034044010500d1200 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 641556762 1250 641555512 641555561
    0x307020709021c200f0d090512031e09070611010b030712030206100b0d0c050903010905030406020c031f020906190207050a240e031509010b0306160e090a 68
    0x1140001d1001e80088042143c03081514481c4103110700c2c9408007200030030170000340300c1c07885400d000350840b03041260303011401c1c0c001651058101000d0180000420748044284a401d0014030340358851581c4102400101e4a01021202e695403c1441414240001d80c070608540c2c4500303421958000c5400f8003241c603602c1c0c2e03540b1131103a07448990301c0503001401010003082da11001c0d200840e04840303801c2d040d141001316072091103000304000e140e03100070300008000200c0551401c0c06001407080c000c20107503843d6464100081d082c540c0a020143c03003074101205c08c803640d040707114481081c26107180d03006071900a0340f030106103640b0911040c001c0b41c55010341c000002e01d034001001c0081e507d00703403040d45449a55140c1a10000f2005c0013041ea0110400001e00d0b020784903000480e0000d4005040750506080810401011602582d1840c040e9440e0008280c10b42410007120340c00c01c101c001420b26849504030014450714035140001e02c5855100f000c100e40c030505800c5090313181030b01c40c200e851602c01c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 641558012 1250 641556762 641556787
    0xb0405060405010c02030a080105010315030f03110f121b0c090108010906060b0301080d1101153c120f0209070f1d060f07062304110d1106030702070902 67
    0x1000c48080b1003035800d244199444520100c285c03081000961280401642130100541c058004a0700d030b00ea00020a00c40000810341000c11042000c0c02501c5165840c28500b0805090003010541050254030500122507099a0281100c28150000d06040041f500074020203041c0072007114015031002c400300002c01c00d00019813000c00602d11501042024641e5680004000c5c0424480c0540d10341052030005010342c018050712040804403030000840396400114030281c7d001d6a00301040c002c030300480100040c041900303000e6009110782041201d80c00fa400888411300c0d13050103404082d489000d450801c0001d2400710740b80303496000784050104d00d0440401001444000071040000d16080b01c7c0e00d540100c0d16014a00360f81015044610744105c3c0b800e8008145d000c0c00c01210040d5880ba01d00172030403160180d801900c0e03540c00341401107003404e0800301d0038055002c2c5a944665080c0a150001403100204084402001da070031a449030b45d8401c0c141e04110090380034183c0180000350b10041001d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 641559262 1250 641558012 641558023
    0x1803070e0a05070c03090b0c0106050a0f0608010e0112260a121d07060509030c040e06190b0609010804080d3b06010b07050a06090507180e150604090b0405 68
    0x9040030304102c00e079250780c4200e03400f41e0110b070080c001c9034150009000c0589032400800c03070200006c0000c03d40a03503e031f000c10688101a1321842e40001d51060602410354040c00d450b0051484420700c09865040a4170078410320020744009000380c1072081c03c1546101e80078001000700304280442c58480b010580054403103440e00e00078001d41b81ca4440c0e2f44500104200020180d80c2011009200050920384155040d50000714a1941031144040904181d074450182030b181f80810340141c202810144a1a4050714000c843c04480303d0400400b401d50345c46000a440c0a148240f03443c140c1c2d9103850420382c00c64410b019020380785c00d06100c001e00940401c0341017203445082404400fa100b4585420400105030a005030008030340082004000001c00000030b400b0050082e030a507a0070116550b00e210413100543d904650541000c0c00820402d01c04943e411a06000c240f000c0c071003100320004803a1501c9100110102040300c0c00c003c1811a21141d000d07070304007a40090117403103238107090609a40e030300f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 641560512 1250 641559262 641559271
    0xe12090d061e060531060b21090601030f0204020a21060e071106010515130f06020d0302040b070209070e030109030c0204052a0306012c040b030706050403081803070e 73
    0xa41055400071341800d0540704540001175120b40009902d0165a40d26400083c13000400320458546801080c241500c0004015071a0398154504400c20308420600981030010940f021030b402010042000c1061000d050721742d154115070069031031800c081c080d1101080c44044640481d0100c502c100c5a90b03169104806a410400301c0050998564038200e840181141c40c14511b07801c9000100504e0406151a04582907074a61540c01d143c82070b10303480c084155940c400e280c14052182c0c1040780640500001c1000d29245c641940391074101030102481c0c0c8500c9170001d00410009000a8405100b14080c01d14420014000e02c0144003d081c011314020404c201a4800c0d0702e8030010464030803241c80405200088014002c00c000f6412003e00041c0c0c0004001e80d0603c0341d60041412030103001a8410880c1d00c5120032080e0707400c040f0091004a541441407035010341d100101c14480d982d0841d06a800b180d5001070420350740d03540c900c024000b6214014106805100b40c600201d1941d04662120340309 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 641561762 1250 641560512 641560571
    0x6010f06081f03200603060a120501090206070510060819030f02010e0d050a0e040b030606010c0809030d1e030e030d0f0608061006120c0c030806180f190e12090d06 72
    0x86103210380c204045d40c44140c2c4c03a154400c461b80c1003000390120344404168801c0c050300000400821540104440d40c0c01804229401c3d0010700c101c01800c00ca5200d110040d0601c03000512103141051483d05004044540180a00900403101d8a4045c0700750494021000a44107903109101101030280094204103440e0000c07507020640400c450402d4800d00c1040b0384000d000303161540340c4400554180e0a640b01c10f4401c46002c22402c0750399202042101920803c42d46d660180c1c0314464628040e150381e00c2c1c0510201400d2102d552500712001064803555044113200040065490b6419001000c90f03034803d0f01180140c108000e41035032040581710850310103407102c140d0700c1018040701d001c8800065585011404406041c2c0200384200c1420b50b0001c0040e0604050341c19095080e1038100c0c0c01c0b01c00030781700180c1d00100100c1d80b046d00ea9200d00f80032007080a02041445012440e151580042e81110030744003c03404050070355500500b00f8080c3c3d00060108161500c3c0309045036170580d0603090420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 641563012 1250 641561762 641561813
    0x230607020f150c010e30041d01050a0e06090429010e0609160207030803041718100507021c1703090c011d060318031c0b0f0306010f06081f03 62
    0xa6510b07000c00c1d030340250000051840300c02c5c00344801030701801c05040116406c0f12000e0201062550250300c0448100141d004801d1a80d0714090420000140582100c81040c2c2c040701030002d0764640800030b07600075911002002540044440601d140d40000c150060000c107041c00006088200d0004d40b4064902640c0111a55503080c07003d061012201a8880050344030700c0d4100045400d050281d50094442c090780405201e40c030901003025000b601a60f455a0350300c1c10030341c41ca440e20600e1600b03e0415414044e040c02041e0b00058108440d10055048651010589030100040c45003040c0481e08151100e03a1241000540d10740d41704c11802d1218085030070301000f45800c0d20a1415a150860003c00d40b605c2c59680c0741c01d1364840101c24240581500c41400401718014115900d090b80146120740020481c0e0108100503201b030300c000003140280c100300014814110495410340a540b16400c29140d140c0341e001c14000108681e01901018001075000481000314103060118041c410203110321 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 641564262 1250 641563012 641563031
    0x20406210b0607031238010c02060708130501140a0302030c0c0601080a03020c01030204210213020d0b0108010e090c0d15050c040602060a0e100c030216030806030601230607020f150c01 81
    0x400ba20031601d0400a0045d1308151908404098042010071b891706243c22114142c1c164003040c003a0300110000c4544400100b41c842000d4074510202008100074a85902e20700501d049061040c8142002c050415400000141c40c406d140d80445031a840000c0807940700390b035500c00d400e8035448004000c5005000e50785424200350301c6802906e06844000f01e8014600400388100200480901822078000a01740341410364284c0a2010b4005400e0781000441c0341085080018460081608218010090b00c0300b4492608000614840d00c0300e016922180080a0f505100744101200340071600041d050804100c41042030f40e000c1c004580c00c0c0e400700c0305640c0300c1d1803060b8180c85606020382003550180f5050030300050180c001d0400c66401d8280140780100d62911141c101c200c1c1c40d8103501060101c424400035007020019540142400100755482c0700354114881d0119004000c3c0600c40c44002c40e05000750343e50442c104042410080900c100c0740f400c0c0320341c0c1c0015007003101244455440c080108 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 641565512 1250 641564262 641564291
    0x40312080702070e06012601090b03030f0706020f0415030219020f0c0f1206010f0602070806040812100512010e100e3004030303020d0f020406210b06070312 69
    0xd50045606401504009040c0040b105103440010f221604202c6480701883e007803044e40241c900940c00c415014030156040c01c1c1000103588800c40d020f80241d0003044650b40e045450401e03690000d0f8072200c0540d80301000302114400c2e01907a00819021202480e02c08a1150554010f10381180c8410702d49219009902080c1d072121001c085403045034200600040980c50b10f03480f00c15019000424052070705688203102460280243c0100b4019150382e8003d0005540420140300140401c1000b072000e4a000c1c0d4502101f07000c0c4001c44012056810082640700344401550b802a200c080c044001c00420a460607002e081540c15034042e0340181d40ea5615042e03550b000350000c003400000102042c600218142c1112150054840314004405400610303941d0408024401540a55000b5840d0f0204000000403190a0a03500001c144108400c00015421080706034150b502c0c0d120080046a152000390040d05a0342c000651088000910004041e040b2011043e5180c9500c0d08100001c3c400101 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 641566762 1250 641565512 641565527
    0x5041d06090c09100e060f0d0e0f0625050405060309060f09010c050a18030507030f050709020405010e0f180c070b01140f061608040905011d06210a0c0308040312 71
    0x515000b04e4014010003001d405460030182030036015010510342001c0d0105c0008907000f00540444068a4101007046080104503a0851001020152031282080250017484101c0d40100d40515002081d40e07a0006020f20140c400401c405805640e0742d00e00785000356241c0701d040b08c0c1800700280c0301010030750f0302205203e07011040c00c1c5521610f10b0007580040603078902c8100d40311002000c1040030088000b90041c00200e00a511441000070101c429240460601c0d283c1d820100c032043c41440300704002d030b901c0821b0501c0c41c00141c9107075600a121202003154000100042104910b09100f400003100f590307402005464040c01038441c040c0d0b03d801c166101141050348050f802108498400c12615008004008030030100030071040071000343d40d40c0f03000e9410680c010400c07103945400400c050400e903000780d200c0707003061050740710180ba0050000380303084008018080900e074002c000c900300e000100000d01106401002460b200303503407460583c81c542d2140c0000c462607403100f1b43d41e048060182e0b12 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 641568012 1250 641566762 641566777
    0xf0905160509060d0e1002030702100507140924040501030b063a060608060f090402010c140c0409080a180609030f020406030b0a0e060603030c031905041d06090c 71
    0x40702460a07450304100406500702207004048196514001030302c000c001c0282c40c00c1c031480300c10302589034580984082d0816080d180390071502828001041000d0703900c00364004000006191b90703a184d4002802255109003a0b8030710385001c000000000249400e520040c00441e10240d07014419400a0410b2100c0c9000d52580340d00740d060070116819030a581e8540d088210f00450260940c0b946194154006039980c0358001404122200148056400c007201d51401c0e1a00c00d880a9075a41001da0000b01040a07254011f0100c05248948610b88003040c8a076580c1d032103008006128201e824201008a13a000c9036480000c904504040b215500a0480060880d0560b858005007945140c840309151038075580200c0e8000d9480c80302100068820b00c500b8081d580c44140081d002c10303e040c020380341c4003000d043c8500ca544144480a21410300004542c0c0c0c82c1c0c00d900d0900c20121f403845059945004039002001c2c0c0c1c1203c00c407005200c511200c0e0080c03140038100c81d0072032251580c0d100d81d6010b110b00c22 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 641569262 1250 641568012 641568017
    0x110d03051b07080d05130503070312060906080613030504050307062f3a05070b01050627041b022512030809070306053907120e0a0f090516 61
    0x84c800c100941da4002d5900844400502002d0215969a0741c03c3d41d002c040102c000c44d5007941050842d070454410075010f0000040200b0625050403111640c03002c0042c08420007500e034407040c408041c495816030f0010708000d421156420b44030b040c090b06403075800750488859400f03400d0200100a1080180040065000140150040c0c0c28015030943d0800d009d9101c1080d203107299035014200e0010105042006c1da518a501c944052600c9504007906a01c110311920051010f4400003001ca000c1561210802c1e00d820034029201c400b0501500d40003110140b002d045005100c4400c1d000300305c0c3c00c0c000a1000c0340c0d402840000341046641200e5010f0064031603100c61481001a0040d09855000103654003291111a9a55290010703100111800540840c00050300c0210109070300c80c0f408a0400990b5aa404620219400c01c46000300d00e8080e050340e0b1160310150885d40214400054840080c04101031607032182c00b941401541d03845550b001e9454280001e10a0f0100d401000d2200b0456 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 641570512 1250 641569262 641569267
    0x224070b160f0f0c1b06020d0c05060a021602040513021014040b0a02010e0f0c030d0c02400b0901060e130e0102040504020d09020126010303030507110d03051b0708 72
    0x40c0e046414900f01d8a03c4414814404001000300da404444080c004c02c210004507401401d1080080c100107420043c0010300803a90241000100003040c03040d80919072034001601c0c1e82846a208040c0c0d107030290040c2d0880d14240904c40100d0035004000390090081e1400040c604640f9001c40f00202e59034040310386514140801d00c21103e00c2c10040141903178074400840d146003004126403c0903122212101a9030048200790117603f82809100c400440341d0034070383d24070340941d0046000d22000c0d4001407484000fa2020f00f132503a000000c1e0074079485c038004901d00c52640c51000c2c0d5000b0040d1501d040d118080080001030218401c1c14040540307000035000c44500541d150070007006d80280c4001a113655000d10000c100c0e91151700c013800e5411400100443c0072030340e50001411000d051200311a00242c80d0343d5517003420040c0410181120340c103103000659995092001c85001c820300d00710100ca400342400c1c20005c6503154010740e0040c500400c407418056141c641740390007846510002005c04505 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 641571762 1250 641570512 641570537
    0x1b080604020603070c061b180b04052b030509030c04181b360c090b071106071209060e030a060e0a0c0f09060803040b160224070b16 58
    0x9200a1038200d00c0310304041700200e41a94442043c2c8945d021801c950140348500240b44550044c20200e4081d1005100542c0c14144419060203201d0303030090301e0280c2100700c0c003504009000c440b01810082446030244550aa0780340050940e070146010520038401c0c2c005c2c2000c02c2c0742610400032940d60001e8185006540b0ba40e03000549400030007590341e0385e01d280c40005480c0b20214800348004d0701c945040800e0840c003044ca88801c054103084008070520f170203507182186410000c030788140c0d42c928405540f2502145428003521185845058020300301107091420092205001890f1220b00e1300c1d010716254a03808100c441120a180e520791650042c03034007402141155211061481171201502ca180065884040300c0c03141982c48000c045030380788000c01000c18103103d400c01500502000c1e41ca40391403c040214a40105a20f8100d4440718071a1380085640e02c884c00586076940284020708444c2c001400b44080d00f1014055645c2e110300030009644e000703928106180c000305030322075240110a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 641573012 1250 641571762 641571769
    0x15130507080c2b0b0106050d050915040f08040b04151112190215040c081207021012091a010519080304090506011b0b150d03021c0c0804121b08060402 66
    0x30356568803040204039202d003c02140814040d103000c0c0041c0c1d112150349011000b0030000701c1d40c0c0140311000030b42110480e003040070f00c2141300c01e41013034001e111280e403030307549003004903080c461540701144103070000030001004880b150f82c01c10b0103001c03501d40050130a407250405848600c00e0210300110841001086495440e290728070503001d1140c81112031700c510510fa02811080e00361000d6072000013210042081c84820480e03484a411040c070100c1c20425543d010800b0803040321800c80a21503441226090b603441603000c441c45942101d07001d48034518009000c05505004c4c01032501464840780e011028041000c00001143c00903402140740501d0551450002c02c005000c880c1005a40320b451000303104801c065821250088038900750070b092000b00c0380342c0d6000604c111806041c510460202181c1c01040030030182464486504a035107036164219000b4030445c0380104030380e01c0444c0108120302051240041e042c42001f0480c040c50b00c2910201001c3c400e03204e84803990f48080c00040041c207 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 641574262 1250 641573012 641573059
    0x100501090c140c0111120411010f0203030601120b0d0b0907090614060d110301091a10080423070f090608010b3706050304030f0306080a0b040515130507080c 69
    0x4506000054221051041005c4031790200d41c0900d030b07010f010418403040c40f01d18040803420341d90909005000054031003029440780002000641030041c52581c0c004048503540001643d110000c0980900a18918040f48130250960301403a00784101000450308e65003074451842034418004140158480000422900e9805400082c0b80903071200c0d20700d00c0c1c94020300c02443c060007a9607408200350384145681000610400103c600c1005007000d08105540c10981035500182c0041c80007580340b1140c024085100c4905c400310a103482110030014103854400d1521043d1200e00c0001d000040d51030010f80d0076a48000c02c07503580040400d088038000c14a810303001108603202001c1d185c842080c2c1d50f1603500036500b6401070b07010071000410070003099845270010520804504080019600305031996968002d0b002c0001c0c43d441d10ba80110701400010860000e848202042d484070901e000c01103900c459104030700484080c0b02e42840404d0410007c075114050102c0500068079185801c4000207030781d0f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 641575512 1250 641574262 641574277
    0x6030e0a170c0604051c030204030f12090b1902120901090b031305100504060f0e031e120106020109020112020309100f0e06070914030a02060702011817100501090c14 73
    0x14403040103a01d10601062150f80e201c0c501a50140680052280c00120b0400480000b4020588108000d0000560174040c11145a0b0040c0004075800344a00c81036603602000d8008c214100c0c008076994581d0194100c0c41090010107909851000140210500d418044c002c202808102c00080520102c01000055507210004c2c60320040030502c0358031044e05204107507101102e0f65440798100028884140259a104520a6000c0001004001049480740100c400d61021480c0e03011105507221100e105071142d8201500c07240034196511400a4000c1c00b0480c0100d02003842c245d03a84510094504c2580d200d20314190240600e80b0081d15948003d110100741d04c144035544908001d00c24200700001c41c1700d5001600c1d4524000c0c10314820101c60410245402c0c070030340c1303c41380210050b00c0f070760b0548030080c1d0f081c200300301c0c071104031180300701c0020315078011032010130300c0f0101c40c4c101050000d07207183c040c136498804003c0c41e40c0351003020b03090324141000390011800c050040c0030030303480150007860710 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 641576762 1250 641575512 641575553
    0x2090301151811090d0314041e0819080c0309040e071a1303060c090b3405120304020f030d0c03030c050301081908190201051f0e040803090a06110703080106030e0a 72
    0x5480e86940c0c604841d410982100340d644135200003034110f107102c49503203030041c0c2b44160007410311034140411103401110180c030003080d52101240c800c075107140410a0312002c0703900600a1140001c0c0760601c3e41c2e600024441c40c130742c4001c44800c0440c0881203c2c01c40761090341400048071b006056403601805050304204183c03c001452500080004018000e41691001c240f00000c042070000392401162240c001d04030102591800b0200004200281a010100300e880403580c0380e58590001402014000c13001c540c040c00786113400e401c00c42e4019070031040244070307440c20040000407000498881c003090085a4240d80804000c90740000c0170f11f000b9440030302c555003003031510041c0100b800f02040c0681500b00944c1d1a80180034030010a858642c808212660100402d540b50002242203001c02801c0a0529940040421000b41050110701d55030340e0444030a110b02c82d400601d08455030301440c1c00350001640300001040c0603203e8094280040400001400d0211080d00d0b414010364843c40c03513040c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 641578012 1250 641576762 641576777
    0x71b061b08070609050120030106200111040806091b0a03060f1e060503060a05090712082712010b010807030c0507140f120f0a050c0102090301151811090d03 69
    0x43c0d0502500c2d460030311440020900480c0240109422200e0b60510010a0010310040c8806a840300301800e982ca440100c0c905004416003c1038010603202a202d1030104000901060100340020303102c1c020302c08001221101c07089418100c900c00d1040f2146544403500040c00c00100c0c1c007170b8210b640c003100c1e000c030001008030b8041c0c0c1a00036131040c1c4d0102c400082d16000108280e2500f44501540141180c009020f2071174000724040c4c45041d1070052516650381c0e4006801401034032030544000c01514056208054031140c1c1d1856003c950000320340c440c0e6040e60044299a0040c010f200005074181c64004180c0c8440c101603018200c1103c64004010003400103102081150152039001031055001e0050a40191070450074031030602034200c1f22030004c000102d0300890800450f011001c092030401d071201c40c0907182c14068860003414560541c04c08011100c2203c0a0480400701c40451002ca00d03021030b110160f40984010307003905696504140300c410f40c00d09103806100708561003442c1120 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 641579262 1250 641578012 641578027
    0xa1806050f04090b2e0f0341040303050a060b0a2c031b210615120d020105071e0804021912050607090608220c0b040308071b061b08 58
    0x480c010340800c14041d174000c0d00491810103030003d0b0594070030100c51405001d145000503c1c0c400001000c241800c907200c07106400b42240c1c0c007101007243c000078100400003140c1480d0400401a02c0c007552040d007410318040700000d10400001c126856a40c054a4036172900403400c076210301658000d440d814103d0060f034450245a075060000e903120005000a15089503031581c14010f8040181082c1d182d48044420780a059400010380326a0201030f58008100141c4510081a0000f0085200043e0b0703100e03d1508180c00d03901904014440d504503030391540d02d810002003600041c000e1003051000b0400840106000d401c20591340c400407260f03881c9014200e0340d510080b010170019903805503025085001404081a405465400204131610b02810a030038545030003241480417800804150484149041c00c00c002d0200ca81b00901801d2490303070321250760b81084842a448410f0440d2401048052880a9040300d00d502041da001a0380d1007040310880c1c0480d00d03000c10b8245061f10007200911048 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 641580512 1250 641579262 641579299
    0x7020a1106040902160501060609030503040b1e03010306050708090714040203090c0a0308070303051320190602030903010e1605450a05060f01050702150a1806050f04090b 75
    0x108400b541300c092017001068070342011800c42c1d1594010341c0030000b5544040000c500d0000c01c1c2ca040e1010301c4504c6030f5441400000201d106203404000d001804007200000500880b680103a01c40c08240e00c82c0031182d43c3d046c0b495034444100380180609444400c003a4007046c240350703002c0d44c0d01441200480d0304140c1102c00003201d03060213034000c56400340005580c808040d0b01d4011130340c100007183d4521814004550740c544401d00d801600c50013600e25003401d00015a076030304641030450402da032102040c07912032000944030307404400700d6030003903091000b16464072034001180792042c4000e8148110346410101001031001243c5000800340f1007081070b1840810305a04a5544481c2505866100000e980210424580000c005440c2240f500c000c225042c1c0711140107460101c3c0034603000b0b42c3c1e0340c014800221608400b4003004500300e004580d5011080c0c1003026041d50030403040246280e546c1d10141240c451081021000078402c0501c8100086441c64102c0125144001c110030f4104a002c91700 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 641581762 1250 641580512 641580517
    0x1050c0307031a0402071202071a070209041a0130110111100c0c030e030a030801050103150e0a140609040c121a07020a030f0207120b1018060503010c0807020a1106040902 75
    0x2d0304d047e24103044c48000250101b14842c002c00300c146c0d100d00070140341a103003005400b40d150081d01940f9658002010446028019107a959005c031080c155541c540150040011804006403403a064051a540142c2d01a01203454807030340c0314480c0d41c4e401c200c4500440300400322411424442c8119000a1081d1348280030340c00c113000d059039400d51f000c80c546c14024280902444054001d8000c0140040440da0005005040d5902802c021824900400c900325038510b01c1d5004440390441c140502c06030030021b40000034560914490310010f515840101710311600c00340d5000340322060b640c400300611407a0b050351240103405080c07800c41042c034a0010740d074807030400c5904400680100300201d04150704103103010201d82c03481c4014000303603080c59507101001c40340401c041d01d00342d41c2000041c003810303003003484e800a4200700703650444954041c4030401c060b0a05010b43c0e8465420190b2445a0910440b0900d110300321550007419140e280e80c59100c403088040c0565904481e0170880400c901c200c5000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 641583012 1250 641581762 641581777
    0x150b060910030b0108010f1503050613111206030105090307060c0504051011060a0509032208030a090f1202100c03020708070810060f0605041509091802030f01050c0307031a0402 78
    0x28042041003680000400d5005d05800400320844c0c60301044c03011000b000349461075a00345003400903050300c41d240010100c2c24112171070301e2054100b0000c0345503100d44501070880c5541c01c0e82644495180c3c0f1040509803201107800480030780c8240404008640316401200c00e440e56810098a403a4403071010403590960030300e14002017007100d44040030f21841080703135541c0b20000c1c203420012810900c880d19101c3c82035002404500090701c490907000c0584451b03000080c04010103d1f0340d56412068080c0555045108024074180ca140c1c0c001142490f80600e011061750040550200d941c2120083c1d40c004020038040e01140b003040e0001c560040300300038800142c8000c8000f003042d000c08c0d4110509407240303038201510810940c10304200140e04a01540d094941302584181e11185da42401c031042c8001303a00c072030022410300c9104480300510310180c0b50018000da0980c1ca203101d411030421f09130b44040d104508401c008100140c80b551003036100c00c401c1000344815450701d0320844002000e0740c20503403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 641584262 1250 641583012 641583017
    0xa060b03040f02030d0e15090a0b0a090f060503040203120309010b040c0302131d0a05180303040309090f14061504081204080106120503040b03150409030f03050c07150b060910 77
    0x40005601d020032400305c110310030b03260044025619002040d042a6000d00151551201146444682c0c0d140d0660710040e003400c3c08295110620480c00421303003502485141c3da010389810380400c90501c50801ca0380303e41d801070014078042c201c881803031442d5030005140526a5581d0b60000100d070352030307001d00710b80e0f409560340242c0c94201e40070b45040c0024a40e440800110603505541543e1100701524a611801030080020729a807244000280c42240e550310030380c40e00001041200f0140c0008000e020340307102d05802c004915201c1000000c950f0f42d888007400150b02140007aa05150515114200b02c07020f102690a1513912542c1d686881103407080800b203001e0204040c800302c00d0900c5480000c02100d030b0106a042015119540c4038810381c050f030006040000002141070300c401c0e40700710138000041e10402c070000042c100100259242d403140d000083c104030200301885469404e035451560842c0c4c00c0c0591441c1a00c2440c02000003044194000b0303814071030000d5940e19224459408001c98 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 641585512 1250 641584262 641584283
    0xa090210090f050a05010e09090102130b131d04060c02030f07080711090606070807020301090c09090302060603010b0102031b010b060c07031403030c030609060a1e170708030a080a060b0304 83
    0x18014502c0d40701d45801040c010840c0103410000390303900c00c0a241307641c201070322010103d807210307030309980a8802c1c4a0f40003001e20a0602c00624600028000d1004054030b00c1c10300000d0fa1205445800c091003101080c81d01c01c641000b08001c191107a11014588070f07507004403890141c4116400c1e00940088809441c1c2e454042403580030721000c0c62200044240450f0f16003a00e1910400041e43e0740584103000d8142c0101080c01070854601350302480805030801d0883c2c080d1903907001c944e400f60518080441c014052000407640f13505050244440b000c0058001e90b060141c070042004242d507003415a04c0359592280d1000d8010f48640000301940c038000f1001d4008207045003004600b02903d0010100c50b03502c1001048124100402580d4024800321200241d5458010004150100a420010b004c1540e0a034100d014070700b60144204507540b81400d0444104082c1d00309071203154500c0b641c540d0341c00810000c00c3c02c1e40701d1141036078812050000014141d03190761f061016500115411503440000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 641586762 1250 641585512 641585519
    0x10908010e1f0510030f1704090b100c03090b210103030203450d050111090f01140a0e06130305030a0813210c150b0f0102030414090a09021009 63
    0xe00700680b00612110303040c07286007405500340300035000134407018001610785492402004035403291100d0710600d02181c140c5a50712507a01c90014100261154455140c6040544006005000f007400c9590562540e940e61031410350420b0320f030f6000011404510044007010303e4501e074840c0c0c070280030354000d078003c40c1c0765084a4840c05001100d00d0300d0403940210090703c00d112500d5184050103100001c070a4400784450040031071062500390100a04a509003210318541000400280601d4202100c40c2c18030309100100640d0840c0380c0c1d84041900750000c1000060080c00349454117030071076000d010245030140780c8940982007800350b0022185d075040010741300c0003154000030340f9410004c86841414103841545d41c005140d00111800c1300c00040d14000000b00e24020b010940b9025000301c2410f20005031400b910b00102100c83d81d00340b1070744a15086c440d00c1e510010903a0180c603c80c1d001141503a04a40401410a030000d1070351003029224211030006031160380c0b040c46040420385980310160704 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 641588012 1250 641586762 641586793
    0x5070608010b03010b030723030403030504020a0510140c0a05060f0912040b0a0c03200a020a06050a20031908090f011a0d060e0d112811010908010e 65
    0x30180c0c00000d0a40b002d2006110a1580c9011a60400c1d5541403020303507548040c08010907003212420611482c10003004100515130940c0015210b584200c4030142842e444104108030340403c01880300001c0d001401e03c0100e0350300240100207400c0300c2c0c000c40d0205042d581d0748a00c0e0041c12148070355a0b282590038042d01d218200000d280304d411801702b05040c503081c107111040d40c4c05070030015010010000580001d01d030146c0c603500aa6801c8403007007006507e40010480d0b0701d51200380100d000c2d5102c10b0001414920500554001410075685d80c17682c1020f0000010b1a00f8442024640b24001000940b00c00900030040386074201490b20f41084501d050640790f4101118041d91003c140d040204074004d009030300d6114111040700b11001c45d50841942458801090f01030090b0710303284101c00660407a141c018188820b6a16120200c0d6001031494002039a02c0300801c550b00b501c0101070720b100b0001240203c64400c0300e001031401d101c495555180f49070035600c1000c40b901540d0420000922600c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 641589262 1250 641588012 641588027
    0xf03070602031c05040206030a05180d020106060210090803010e15031c02011a090a0c050403020402070c050a060c0f08090310051f090920030f06090106050f040509120c070e04050706 80
    0x1c440742c43c204800e207001d4006c60f21500c03005081d480006d549000003001e2012900078600032a8099080362400a000e03107001e0700034038080c040c0c0301c05817042e2007072908003400900802c440361b6070003150a41140d1a1840c80c08071494080d256000ea221803240ca40e03400d443c2003102480280d11601c9a4884c1030751800044e0840b410900c034140b18501c0402c840c40103484a0945a400c40c0d8230000004003859510b40c01c441070b01807504000e41c024000170f5040b060052402018040d280102e601011a542c0d917030040d68035007946d08005040410355000580410f1290000d05028807015040d83c20184096104804803102207070143c0003981034000c64034001c44508520005840c48031030822110b08a5250400074060016031885141ca501c807941500351800d119210311146208100c5044d820720448080c0a00b0b04c50140d603006440b000300901c0c907803a0600070340d40150b08900c0908654214045580b06a41c408115200705105030b080008407030340130300b4000340326600601c058a0b2107801d00c00018043d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 641590512 1250 641589262 641589307
    0x20403060c02030c0a2a120b100303022104051206040302060106051c0c0c0b070201270803040215040b18091617040204060306110a032007020108060f0307060203 71
    0x543c028058481180c5002420784a8035402c0490402040e480c0038400e0014a1449410268007170916030001d03416a070042c401141900c40d002a0076599505484407010407000d01c0040c0060744000c40580e1420500f4055518072a06004058a05521b0350040f50355241c000700c03072585a81c814010001415810300000780035003210301c1d2071803401c0c0f00c42403444502c40358010945402580c40ca02041500d00800482190035030000c002401468006806802092582d4109800b941101c2800c80300d0074200346524061988450043d05546482e020720400d008403030740c414180f110030440402e240034424060b00011100c8904860b40d28013980c24441040c034003030035007424a5034686041c51025040b150b00d1401c110b1b40c244c60141c0784d880c1d0001501800c030300d070700280440b450038400c08082004200205020000b40e1828824506181c0000040c0594050414800c003414860000158411400b03a50080c6001f02002500210000080d080204039480b4201590000509c003c0d1020303200d0314204036 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 641591762 1250 641590512 641590517
    0x31509090305070218060d081b010509070303030c0806010503190603051c02013e090607030306060f020a150e21030601170f131e0b0603070b0306060a03090201021f020403060c 77
    0x5050040100c0c60087c2c2c0c2200c01000900085001d903820f14205c00c0ca06600140380009100c1030428038412030b11030074a4007099002905007907010013118002c01c0a140280b05c181d403180c1c612741e074240448010140c03110155080645824000000c5141006510f034240f1031104800d040c0481c00c10040d084858000c030160384424140000451180744c00ca91441343d035400444010780c1c110309212054948a0104442c0e402040410120181176156004d1015175a0a84800c40705041000007070380c0e91074880c2401025144074407020300385610141c2103110003a00300b10484054400242007a4070b035941406451004840c00300810100790380c48200d00c52080300400010320541400000380c4010080104010b0078030103400c40388400c11011b20681042540003818417010081c0c031b490900100101504c07032030311030700c100c1101140c11940c50302203a000e0f100040c01d407441d03c00401425030103003000c12020390550280c100c12100c01700702d0788550508520300e10340c01a03480c0d085240180440390002e500104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 641593012 1250 641591762 641591809
    0x318060e0f0115060503100f080307020906010e3f0105061903030203040e15060c0c12032d131203030c0503010b161b09150501020c0102030301060315090903050702 72
    0x410040180500080e80c2e6149000c5e40e9a50351095280303081c0074254041800390300e220b880050740c120040040d00b00c240c4210f4010701c0035111840119684002441000e41c0a50024030180036581903400b460030861449200010b552a0b559140c00e51219400c000c0c0a1a5120000c0003104e1510025104010704c240c4050380c2c03e50f0039078500035500e00840c020400c08421090100ea0030014411501003e001c0040913140e0741d0a20000194985201d01d1009000d002c0f1a2446040c2600220540e054144103410204030418405028401500c40024005200004204264185030382c100020702800342c005407401e0500c40c0d40390050880d0302d2140e40c42d041010500051161030b44110480302c0e185040301104207000d002d820540541b9100c40304448422118203400603a605064228420303000e000441480642e95800043e40c80e00c4c03c03400900d0058100308010310016010380d00c01c24600d01d0b6020422100340d1900f1802003150049075058010a5010401a08514100809082c0032921031242c16 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 641594262 1250 641593012 641593031
    0x4150e0a0212030a1d0d0215070b0601110c0d150c23120109020d0f0204120201140a050901050d150f030b07030b011d0f1e10080402030c060a0318060e0f01 68
    0xc010004140d040c8202c0d211174410f00a160356140f0b007103061079030020181c00e42c00d43c00b242008202e500c03820045584e0f80300c00d0b0019207258007561402a0b40c400300c102802443c2c03140c034200034103100c98010441e02e200c441c20290042069602c990801b076115604c550303064034426a01d240703410b00d05000c0564041c00030020045545200d00c04541195520710b400340e1119009803650010f042c1c51003024080e40d1020130001185999800100031050003a2103409840c0d08800107465a841703260240c43c04540e08100100165101d1402007060346041c4c180005d54044880d01ca0f001d51500c0d51000c0c0018460400900900c035910b20466085400c1d42070030401d100c03100c0e0029200d040710b559074a081d0019070520300280c1d11903040c030100e045001000100700d11030b140300d48502103030a6900705004400c1800c09120035401501c500d0700840d0002c0060210108100070030005a20602e004001c06480d84508e08103400c074140b06052a5118010100310324900340c19151828040c46404010341e0f05011401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 641595512 1250 641594262 641594267
    0x30a1b0f0e0c34052109090105090606130605040938040e07090911061e0f070203010f0e0f1b1215090102091c150504150e0a0212030a 59
    0xc501d04000040040e504000d004011003440d000b4030b50f40a401c05601e45010108407000c10078008003482c180d0f0f0346203044482c00401525000380d16080b5000441d42c4014490b9262641099501c42c500800d9689402c6c00742c0c50a040310b02040c2c0c8900e02050340802e00f03002d090b500340104004040c07104040340c081c0504c0c4440c0a5152052030074001000c200d644a2801d81c0c5441d0003601204441c601243c404550310203180300107004412003502d40143e55002c0c0b00e9946840411220000301d43d031070750091440043c10688540c0d00844840c0b00c071003020880b0000586081c0110a0810108800080ca00a0f25181d40c0d0038200111078030b03d41c94020240c89020010b034400002d08071035054a840d00c0c40c04021142e14607000130301c84501048042e400c1008049541500180800207056030307100c0e100159003082c05406110014000d10710380300042d86540f20801c2d40e200c154414080c510003511800d40e40c11311811108000c462402d2500400f9007001542001c409059854240000a511703000010030300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 641596762 1250 641595512 641595517
    0x10b0f04090807060902042c0d030501030812061c081b03091503061216080f1203010513090c1e050a151206050303030f04060b010315050d02030a1b0f0e0c 68
    0x13030019940300350385429511540d00c0401d00281c002c1c1c61120396450651004044401806c540104c0d1003078403001503c07548240a00c904881d0302208139070910411103c030f2071460600078050350b0000d02050600c040703142d0421028460b00d000f0100c150382d1b04200d644290b96255015409a041d030b008104140042d110654540c030f06101c0800c0e1075449489050000b4091000102c514186124051011540c5120721081404503844501143c82420f42440e240b610307507000040d031140d142c0003800100642d081c0800914649038280340b00050107071050f0b0700c41c82d0b901c6007500000100311242e0101102401c01c0003000c0040c0c001101c072016940e20340a0980f581401c020100c00c10090125030b001d00d1100240c00181c007800000707054903200e14101c240300468803001c0740c0c10b48180d420400c2414030f40d40203208690794a980720b845103140600b8a000c1c498004081081240c05110712a0f61070082100d0200c884203039400d0316031507044c0a01e00030902012000c50f8001d41500d1862105000c103000c8030404 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 641598012 1250 641596762 641596777
    0x6010e03100906020d09050606090901050105180604020c010e0705150c0a0201031e1e05060f01230d050109090c0501321b010527070311031e010b0f040908 68
    0x1804191001d0b6450000060300a001c0300c0c81c0200c0c00d00d0741000400c40d000c103004e441510f007502c1403603866440150940c01e0310790a2040c203030401015203040b85018840780705294041401340c00585420440200c5c0c0342190314001402402d904100c10030f0096203445030509540554003036980d810890040001900d8015011009040c180e4403210911010f03504d2014582d03600c4464800c11020041224041806c0388401060007207134900800110945030200400784480d2041e0340320302c5500501411443e08104210522441840a21005001c05800c0c050300f80130b030071500c02c08140a0800e00e040e003408906d80d00401d052000c1e01803008007035400c01e65038101102c1c0c9200c0c5840801c1c0f048420065070300c14680c0364405080240124510a04150082e501540310340c501c0b200131010000140d081e8035010387c08000640c225110400c045120911400c3d000b5000900707988044507404200000822805d82c0c009a994564400c0811840d04081020803014262420b002000320b5994002d8030b84100036 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 641599262 1250 641598012 641598043
    0x201020403030915092d09051302010c020604080d0504080f0705060d11040506071a090d05070609172b091101122d0e030901020312090f0703060204060806010e03 71
    0x91404102803040144038014030903291a11509a41046000c480241d012804032010941c5c640005111500e8405c0c0d610401b00040b030440c55412503801110320007900f400133780e400030040c840440c80d500244000c010049940d03d4459030b541c0782086c0366081c4091450015116046204100300a0b202c035402c64100d40c20b4a840003230981900180300d81c550050740c001c540c0040c4003045203810040600c9074688402c0c1045080754140e9200b004140d65859044401c50000f107042c42018002a259000b2418051141d200580307502c40011202d022a00310484060502550711040d10380c2550801c2440000800c00000b070000c41443e40b108100c011215002c00e040100f43e84002c800d46040340d00c6070710200d103000300e0440c2c0841c2500c0d40e45014a050000116101c2c5071260844020b90000211020070354180c001e90b041c450546d08044040c3ca000b400a4540d008581111801d8003082c00284080c42c07103210b00607161802d044008112400042c02241440124407203401d456800007101000034508a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 641600512 1250 641599262 641599289
    0x1e08070f020304090f0f0f05040309050f1f0f08091203070c1407080d14030f04290f070e1207150201090215040302090615030604181e030e0102010204030309 69
    0x418080b4034510865100030340040c0b40c0400a2108401e0390840c40c141418100140804603e541880040381c03000e440080102ea000c0f0000c2001d41060310314041d8401009000252420600000700b040d280032148041c001070000100b1000c85400108a03500041040e0042c620081101d140030840d21014050300e040c4507a6500741c00c1005445000215032072910740a490400f0303502c803400c580d95030303010302d100d00480c8020a041d8004128241603a1240041c44c01c002216102c1e0f0312081c080075a42c50b54040c0000302600550110030061070313214011501c1940d02c03c0b16180c00d1500524501507554664880c06d00c190320400d00c40000210b0500b036413840c042c041d4002490882c00c0c1d00400d0701440c002d4000101101c0d9205004082014100700c03070082d20032110603a592000c11041c1c2c0c5400d441109410300901c0410200d0030700c0d42c0035440401c109c10100c603d141c6917850708041c102e014064905c8040e19a4010402c160340105c2090000d9821300081d400c0605698014210008030b0040c460f40c00c150 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 641601762 1250 641600512 641600537
    0x6110f07061515080105120c0f0d110a03290103030f08070e0a081501050a080a12200c01020c030102031006080c0409060f0807050a0b0906030a2a1e0807 67
    0x2d000400202580b01c2012030f00e0004080c0500700c42802d00c00c003403203002808920301c0c1a09001c6190072011400401c20522035100108224050080941c01e03203910400c507001888949501030240c01031030148407071520260040503228005020140140e1141c10300358010000260042e02c401c288140508150050baa50240c04603004840085002e5200d209803000095541000c6030100c010700c40d15544131201ea8881c000d004000d54a40b00c0c1a1581d80a0802007012038211651204520490310f0443c0054402c280051050a00080c0300e2006030030a5074a402d65680400036000202401c2d0029400c5203050031301501d2040f4a44030700d40601400e000000c60146c80c0c0b1040328064400d0441c100205a1616000d05221050f4096142c0f02e02c1260804201032400064481c00c9030300d008609881c100401c7c007400801d41000d000c24203204d4a508400c01224017000713080004210713110a144800e520024000c000b1158400c08007074461007100d000c4002940a5502540207486040500c0040f12 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 641603012 1250 641601762 641601791
    0x807080402040f02030a27020607032010020d05130c140f120d0813080d020a05090d03020c01020709021303060902150d061a0c0607030e0f07030b0406110f0706 70
    0x308140080003413480042080045203a42d1b00c03908407001c45190743e01c1c61401c200410f141d003030000c0c2c5010354401e0007400707904006485480c0b00c0e44401c2407640700488000300c0d52415440d05040501d058070a40d008110b07c110b662180c8691580501028400d010029480d202c80c415241180100e600e11013161440321881d0300d80c10081440960301500107603010350b03031014a94440c1c114101c0900080c9450010444000c4421080041b4640100143d86410360b4022200025030140340c0e01c0c0c0c24041b0500c42810359955402054079550b0003a00a000150004000203007409400d410400c48544180203c51031022008a401c00307981c2d10640000e800001c50001a85070600340441d40342c81030000850000040b4180c0200040b078103100c1a006c412951160000400c1c022440d8940d466404400040d4410748a43c012060030300b00c2d04103440c41004800310050402e1102e810642d005ca807600117000812406200d441610780c80b4440d000e05240c12080c41c0800c038411108060200ea8603407212110b07603038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 641604262 1250 641603012 641603021
    0x6040905073606200703061d0607020d030c14030f010e060d03230708030c0c010c03020f0910110d021c05070203100c0302121503121e0714010c110c03070303080708040204 75
    0x1314400c21142d405a0342d15100d0060320300f80d241d80d500320998a0004102e80c1c1c2c0000c0283c010041500034150555910740100c0003486003c0c035030020040e01c18552881402c0550040d40590b1180607023031642c1d0304150705407428801c042c01141c0504150f840f144046a400f034540710401c01841c000e02039805103900c000c1014041c03104050044070307000040c40b991460080060000d1291000280003903100d881040c1c00702e0242070484e0b000c0700802c001c039000b2441c0c0110015656441420100a042c2d0704414151910360204000c10260b408140300300c506209a5020900d180090b05c0e0041c901849540030944a2000700311a0542c00d0300c0706075142e0303030341e00980503100c0800c4801070740d012510b411190344001f607003104100c5000e8002c0501725038001c6000000c480910287d2070182241440c41d030b81b44000d41e800040c00340c5040d91528100181041c0c00c1c0640e004011144d500c000311400014440ea0a09410040483c4658003c24040000a401c10003043e071210b802d0405030740545e550b0020030b0140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 641605512 1250 641604262 641604317
    0x1605010e0f010819110408060901050103020f0f01030f022d19200d0c060b090402150a0201020c19020a080706080a0c1e120b0a031e0206040905073606 66
    0xf500f80302d60081724084881c05001200c0d03c88007107800a4650300080c41c00c8441c02c1c08060741114100c00c000609040c000b000d07010b580018913000400a084e29818012070f08180071032110211410b60100091030794040c40b00b030500711034103490314150750201404141601c0c1d1000c18188040c45014080b0070b510032240018200405c815076140407252480203014018200e0205d5031580f4000844619052200119100d41c1c0e010700303904515003141c01c04ac00c02c3e801c401c444404542d020802c0e8034140c03005109201504103d1b140c49446110144100a0348201d10b401c82400c6601c15681000446d07880b22402d600300b1504440000d18640c03194085982a1055840d0712404410ba02071881050780410401c11558001c3c0f02084021440010032000b00300c00d00c400381194030072108c1c0000003020340240762000da1004040754a000da03105100800d40b00200d80c2000420380000400b4503000c00d501d003102500c0c1d1100c504025003241081040c04051160040300204164000607078081007080e004c3c6081c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 641606762 1250 641605512 641605561
    0x90708060403050307171306020903030f071a0f04050322030b070909060803070206030121020316060212071a0414011d01060b04050604060e0d0b091605010e0f0108 72
    0x40d440e00382800f0701503901c162060070000b48401c4c85410180f1840221030b010f802184102c0398007440ca0344508000e9001007401c6549030008020543c0d494000030010300281d40f10b120f66408a40b81403185116401d00100000d2100c0d10a4040100040003c021905072101c840d502e040901d8622101070190760090f0070080c00d01a131407050044441c0c100c1c80150845058002c02d00c861606d07000402e40b00d01558a00a401550500040c0043d51160301d0004074400c5441d0b1044104890350006803800b22106648094004c0710042800312590600c140324030031148a886074070b0408643d40b041c00c0121081c042d03110700c0c00302c030020504108160074001038000e4030100134091102038110200015000142082d201d43c030342280003c0e203c41c0103094508503100248480d09182c9018406d0300c103181c00c00300301c50f44982c101112000040380c007071285004807001781c024200840b05180149040c0e9a607008103040c441e410341200c11035519030b00c2250301804203107080d5910783c4400e03084401700c424013140d05c43c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 641608012 1250 641606762 641606773
    0x6041e05150c0d0617150a0207080406081e0c0d0b0d050d0914040e0d050307020106030c0605121005060315040e0d020d17060a030f030507051605100e1305090708 71
    0x42035074604040d102c03d402d070200800a2507902d0000c0004880020301244803500200c00f16031000829081d11580030788690800340c40d100315a9260710595200e82c10100100d0b04002c28469006141d01d8060f0b81c0900200b280b0001c1d007032980301d02080303015a00c5007011080e100c0c490441c45866900c0c50203811a48030044480319015000058229441070145480c2071003030b40842c41c0381e0300d02809103644401006c00034011110107150101e07440d84c00184100c1c299900d60380c001000514854281d00184016a070b0a5110b10034401568480c0001405080000d5902c00e01880b969071000102c03500f00e10640b211001444806000c980a040c5030991180a8040c170300109442c20703004a050007000c40c056a030307051340b91684194a042440c00f0b55800f03801c076458440c00d00c0061702c2c460b02d10061034040e082442c1402801e95031207141588415020032403c8a4100821071810582105a40719103282820b2104085090100d000d04150900310800180c940000c030324002800d0107114007a2142c81c05465 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 641609262 1250 641608012 641608021
    0x110607021801061115040308090f070603020a09090207150b040b0301020408030d05100e0726070c1106040e0c0304170403030c02030d03180b10050d050708010b0306041e0515 76
    0x41c0e0034400d215102c00704000d124004940c6101207030382001c03000410007410003500c46440481d403032080284000480d1042c0c80b280c0034585420000300f001070600b41d40259542274070201c0203041414030740c80380010380d005000d00800a1990040c406810740c2d004800220001d00d90300140c0034001511500c1d415520004001c100103d01200510160805070014807090300ca0403440d405080c050b1181d140d40804013000b08405601c1a8002d04a48112104088604842034290000844180c074841c02242c0c216020804200c000c1d8001805143d0480e1303030905080c5008102501460003c00c521a54800000020104044411202e0424a1941580d5155501c0c0c6c60081e00394450003100740e00c00e114660b084804244240510a02c036852101c207000480c0c00d640c0ca882c0c3c00310001d00020404a02c44a010500e40c07141601907100070b02400003404032902d00840c01e401c54944100150080e00309504000214401180c808480b0f11044021000000c95003000390502d215000c1e07801c0880c83d64002d01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 641610512 1250 641609262 641609299
    0x6161a060607170f1309180c09021809090c0a08010c0f050c0a050319030506041e0e070e07050a080114090103030c0f0f08121302130b0a0302130603030f0201050105060711060702 78
    0x7000c0d51b0704403100300011150002025000c240110006080a0086009110280700343e0040c100f920b40c9140f1207282030070740800298034540100c0e04840254440e101d0b84488e072501031901c10040429000800440d510700400030485090702e004003080c000001108909500d041002440d0355400c80c00741e94076920024404890050041c0e41d11000900385008281986440c0c89003040104010b2032210400c2e1100c0081c00140011543e0390303070f0a001c1c8600c0091090544e680e034520904440d5101d6588844d4030790041d08542041e0002c03041c51811000c951443c0e1950505681521340600b00300b04034621514214900c1c0442d520300034800c1010703103000d074100111100942180c1d108038025a54aa859031640c2103214404c0101942c03045000110f0b0011134041d80c000041444007500c84200940c17240c0110301e110340b55216280d0901c0c1e42c0c0e0360410a15038404ca104402503440d200901c0103515010014a0a02459402510b85002800c4402d617590392402111661903010b0441800d0040340b942c0d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 641611762 1250 641610512 641610547
    0xd0b060f060d0504060203070f02160608060d0615090c051303021203070c060c1217061e030102180906010f0905210d03270206040e041106161a060607170f 68
    0x92340e003c0b641003008021568004100a1410643d80c0d001e0700d1000e04e020022142050007522854200b0314080304100481c0381d501920b81e070040346041c241502460025000101c9012003000f004002080c09442c22450210072030000700c0c0c0d0102c5410221410316400b803401c505c103101e00103003003000b0440002100e83d004503d8091880c007a8028800c0040f0b1841c050720342d105040c8020400e1b81040300040e4152800d4140061342840c6080440c807403200c83d50200e0b0880e48a8804180c1510790540820010702d080d40e4143d0780540c007131800c0f2080c4181054003801040d07441c02040e1088103076040000040d80d090002e030b6031982240f000c035552000300321405402400d08031104014802080f0f000344102d4140c005040305d05da0702510799481d25150181e000440710b00980112442500a62245c00c03681c0d995001d8000001d1520418000004920782010305204220301440c18040807000c01c840d59a400c0141d40c221130f001f221a0300001c03807001151100d48030f5100b003c8003c001c040f03803090f180303c044460f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 641613012 1250 641611762 641611771
    0x5030c0a03091412061f17060a0b03011119030216030c02040509010c0507170f12090c0306150603070c050d020703060f0603020d020d06020f07120e0d0b060f060d0504060203 76
    0xd80e824400f00c0030041c880700c0d4048504144a42c0d0080d40816030051041407043c510324000d034000c4001545a20503005020840b14078218603034041e8003400401c0d0100d00ca00110804100c008101d40000c0c1c401c02c2e1854003c442285006c000110b200c108118000c0e011901400721702c0d000c0c103c0b00c507018640944000003100f01640210701c2e10001410003e0144104032291040d0303103c0d2400c0001a94079000030103140c4010f031151320403d0292030480811038003c0c0c158500080741f0204545081d01003980303040a441c020902c2540801c0a200035424a0542c044000b0780540e01c07240c0d01c0e82c540b0703000c2e250544548002480f0340309003940403590942c041000d4042d280710f901c003400000740700b5089130140c50b040e0101030351000503603183c5801071500b5140c089145100300009070600c0c141d0140c0c283c55030004003040d03480111f004500340744a0340c002c0030520000012a0683c1400c031140d2104050300c2c030001c1a460046585400c4003c032a61003100780c2d442e02030409024801032403d03248c140041c0d0030545 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 641614262 1250 641613012 641613029
    0x2070f120908071401050f13051c0b0601030e150f100503060c09010c0302150903120105100c1401020c010509160b030f0703050601120c030b0906060403050a080705030c0a0309 77
    0x240d501110a214030440000c4414980c02007198a0030504c00c2c0140328541002c803410300c00100309000300c0500c10343c0a09040580811500c00301f51812003032000010065102001180340d115689000400a01c0400e130820400e1030006500e18650f18070601c1c12079101241c0c1c05020314101003008505585485620400c0712589401405980d0014981c1e503003405d407107404500400340251604c0394412881455801d000e441100c0281164070282c042d4190160341ea000c450b00001100e5046c8094802e480b030041006583c680744c0d50040c41401000c0329202d010044c8940c041d05511001042d00750140c030781c90011076000b000141000c0418603030b1031003c0700c0c401c100c0a00b4070b48002140b440c00da0a99208811210030030219a41d046001c5000340401040c2d58140401c1c40030521090340d60384252100d04040751400a8070807894001c115030000b0062405118110400090000031800b05407070790038a60050003103803500b002d803170441d0842c050715440070390a2051207125400e0540c440d1703490040340e1840 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 641615512 1250 641614262 641614283
    0xf12090b07230d0510031e061506210b0402121005061219140c0c1b0a0b03060303311d0402010c0507080d0302040f170c13060902070f 59
    0x1c0444035080c40d14944048032042c4140045004105150082a88510056034428402e0348a40d5015010107000080e01040d0303100c0368108003041741038400c40203a400b0031440100f03050715140009021518000e18028107200c0c488102c58980003a4111075122180244195156200007421840848040700c20940d050760f00540011141050700032903017040003030500607030541c0e215062500210313503003540b0386480c0baa144440c1e41031180c007038003090140c240103e4082e914400d41c400282341009803402400105d46a0880c80013076a0741118441c102e40007072512a4a1350741e4100040e045006444d0300940943c5120800f180e61030011554101d0140100320102c1c0c80c0d03407a011032408010900c00007081e0310440c80082805580039000312240036100703404881a0700e48a401c41d504141c01412141b0100e500801d0610000c2e071250313042c1000d04000641d000300101d080d04541d90b00c400f0000031902480c0403508000740c00c511a040400500140c000c2595105804e00e0041d0380e140100c07800b543c044118 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 641616762 1250 641615512 641615537
    0xb13150c23070305120d0f0b030606060c0a0c06030c030507080906070c080f040335040504020928090e03030415020903120c0703061a030705011d03061f0b0301060801060f12090b07 79
    0x508c00c45680f00b40190041105584040c103201d040d030b100e1214808e09104081090380042c7c0c03002e00c200050a19a6404900708004c070b0300183c00d454014004005000e403540c2041140040090102c2d400b510b10310300030a90345041e0070f122811b40b042e9211110361140002d40801400900c00341c3d5010060386070300d2445140b52455201411101c1039000b04100d4101308010055480c20b90090048044020100c050071906113440d004800c01c1c2c480ca04d112000d0301541082000c4003441058141c0e00c803080a9807440ca896a44c041591782940d07101c08403154081148005518100001912000c0010360643c4d100048036074640e82e40b16a1100f21401400d00781c1a6501d070802111882107000081c0c003c0c0301c071608000047d11107003821081c9444842d10028548560f0f50200142030003991004030340c501c4103503280c10100080013250810703d401101000104841540403030401e0448803030340340440040b003811b8030445507184140711040c0c4040c2460040d5040c00054003400d8001c40180d00c1d0000321608 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 641618012 1250 641616762 641616791
    0x1060e100b0f0a0f0e04050703090b010803090f2e05040f0b0702060d20070c05030105010603020f07060504110d0809040c02011503030302130b13150c23070305120d 72
    0x814840c1e070541d40d024445260150700420381c40d144d074001c604058440b01d0038403000c02c044910071039000d000292174460388824410b0b80f182480c050505c000166140c1948140130400f002d0720345900034041c803603201034030000c0011145524241d5240e07414000c10f80850b03810041c82030b0007501a090724101100000039074243c0000442d8000c0341c0c0501034a0401001d615200002c1880021000712541420710200031b15100000a040c1184100c0b107041d645400d02041c1421a14160048003d040c410803404140305405400e071011b15602c40000700ea143d070740e81f60003030012a600074030680010100356903204101c3e400010308004102641c08029140b0503460480c281c410803a0421800e042284051000c24030980041400d90302e10781400b840141c0d13a4032011015405552a000300d08803607101402140542044903418030054a4481d030039100031b80750210003099250280341000038a1800000080c4240f20903401180c1100c242c03402052041a1080e0701d42c04805007500041c13409404812200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 641619262 1250 641618012 641618017
    0x9050f06090a0209130302010605062b090309030f050709050403030501060216061409030a08040f1e08030a050a17090601080706030e10110c010606090513020705120d09020301060e100b 81
    0x603002007038144c0329229001d0308044803100c100301340d0031952104d401040f41e0700ca10300207101d02209030b420110081ca44407051409040e891a0f8101c0c017500f054118070200c2d5008920b41e050381c0d00018001c04d1018280360061130030007544d20103141c480c2400200001d04d0f41607031100781291100e809889209081c007581541000b464002ea01c0840c01000d0b040c5c01d00030010b005002e1001c0c01070100e034000c84d9692503e0351590450342c00403803070740c0d0350000512001c0c001340d42c44a4141c00401c00400d280381000200e645a000b13402d038541c1000408075041482d123109070740e12010801e68800c0c80c465070500200d45034131100240528852445503010001c0c403e8803910881d502880c1c160301500400856090600283c90103181da155840028805c0140c141c800784030308401010039803103210780a450700060000c11504a0409070001d48103005010100308040b80f08490012400192540c03078803542e01c40380041600f0b1001030341540c40c201c40480c1c000d1408150501449000403405c9050342d0381c81c214110352 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 641620512 1250 641619262 641619283
    0x105060a0c031d06030a1b020601080d030b0d060f1d0f061506040302091008060105010c0f0213180f02030c060a0212131805070905010503090a02060306060d09050f0609 74
    0x41c240c0c06000046803040ba42c00c00f120f241c101c0050451408200015035542055518044113070392800508559207800d182d010704d0344d2190005e07000640c580340c481c0303032645c95555400042c0342c0c84201c03107066551024504142c80303a00c401c4c1048400c2e243d5891500800000c031841c01c8490b0034280c00092054001011803000c007260780104440d81d01c038507149154290f80340f0800d401440c03c4c0300210042c1d42c0c0c240c1d00e03407040e44034450a050340d43c500f07442c852030aa01079100e14140400350252102003030f00b10248e0b41c2002d806030380700d690b5044403890070070007030040041c0e040382103115024590411000642c0c0c00c042c240200c08030b4005207581d00410805c0c0c4140d18214004da8040a2540071905440d00a8080f00b0303c40324560f070104d070785e40c039907038011012540c400703120309644804000303040c5d4102c200c81000d01001e207081411407600b400c40f50381c0d03858100b101903c17488011000444c681e4038001211440c0d4241c003000d02c20a00140381956076901c0c00c0407001c455004034000140420310004015191 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 641621762 1250 641620512 641620517
    0x1206060c0b070e0d020f06090621010f050607080315120309010314010b070b07050702030a0c0302130527030702030f0a1401050906040f0510050f07090905090303220c0e0a050105060a 80
    0x1001d132581d0800c12042070640d15150000c00c180402c882903a1031401400d50410040410300306e200e4886042c2c045100142c100c0344044041c441d041c421911110182d5a581b80e11110140c0d407511052850f1943c0401c4005d055030201c011058020454008005000010001c1c1c90501001104402c02e18032003009010b0401034040900404010030820004990012814148586050a1600031134206070840600307403120210b41004100b107062142140c034244094030001c11080c2002141c100714843c0d94060701075000c014541c4030092602c00e00844411130380c01011901c85541c5982c80c2502e0700c00b921800d41b815205256451090081070007040c0c0308010742c801400465030b0760343d20350920142d07000050764284104248040740b200c0900c01d65014150704188070303980e85400308008100100c550003490440e4100300c00c2c4090b910703001098a0300802c0805141034102c1da11420341c80c02c0c05c0d01e40c40240224944074400140410140034041c026580420309000710380c1c88130700388821481080142c0d0700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 641623012 1250 641621762 641621779
    0x90c02010c0915030b241201080a150e0c04060305070f08030c0613030512040302060f150f270109020702011d090630060f060a0602030d09031206060c0b070e 69
    0x143c4510a6103c1c0700b14200041101e5815141d910386215100c4800e6111003a2030000030705001d01c3c001552205005001c41001002c10081c6a910300349920300c03401c0603808003030b29041c130ba5803043d00a10144504290207001040195030b2414065581c10291103000c0c41e81044500200304180080100d9103228100c100600d01d54030350681101c458201c0c1c903000c0e42005018021510301518220659011314020f600400c0e007810520400004902c02403d2500200c5d04c1010000d6280c03146250504500012a0140e42903100450480121410220354140700d001d45000810f880400e6400b8254150007039070f42c0c4030304210261781ca41042c4003c0d550640d00109100018419180049204940e13800c10328007128010554000c0000c02c0f00320381c0345c549460b0840c10030841005148049258414070803121084681c1c5082d001a44038458005d11a54003034031075030480e0501d40240014001d19070420300400c45190b031382500405d0281d51a0048902450386d03804101d4080c4034090394141142c00a200d441b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 641624262 1250 641623012 641623049
    0x106080c0f0a09050a090504120318020d0203190b0f0705180418120507031806051902010615210c02070501050717040e04051204080a0204050601020115090c02010c09 73
    0x40960b045102c1031400c100402d103001c42d8507254400a0390050055010200726803d051918003104841e8502c600f00301072411542080301c14124001d40107454041c1da44031984002070001ca41404158003900e2846c5602a01282c2002400c0200611903007140c400b040c155110030030111a80e10a400001c418400091210a4030717152961004010211a04000005240a545008440c800d080110022034404034540c01455003160b0030120318100d8602d0b070750009040080103445401000c40d6030a90528031061011454000d41c40000900030284804000c01405030000300790714403c00684510416146400300000b82c0c6020300c0c1c0010000760042e100c4503041400464007600648415600c440c200001d100860203141c3c0188090103c0740c88000345442c090501f50300e0080884079820f01c0f0034041008116901001c580c8104981c2d044401141645654004038003428040400c00854040104002021680d603405180c900708150000d0001400403103003511405a01d01c9003c000307034841241c02 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 641625512 1250 641624262 641624287
    0x307090e060a1112241203030109051f0305030d0c0201021908070c080c0a02040c05040803031506040504020c0a1e08311409011a091917010605090106080c 68
    0x16140302003c0d64940e090040100c00314000f81025900501c14001c00c09a00402c40c080d00f040c82c000c0d160990f490350650b9514100160340703200521840e0700155840340803590003036000c030504406581c11910607030000e840e030400702c1d00c03a44024140b041e0340341b52146c4480c51718018001d035900b40100300000b030f1005143c05000c1d200543c005050208202c0c2200b82da50024003048080c00d002c400890003455201e10780d205110413034100c0410042842824001004620b10010450317074000c01e81c01032400c84545500110b0200c0c015900056400b600125030070310300e80d100048a03078116004542021a410300c01040d50743c4100754800c05400381400700000814800c1355608103090070f00404501580f550024419110282d0076004080004050003241d986440c0c2401002c0c0542041920040711082d0036000c1d4074a40f064440041c080c461140c00030a00003071607075180380185a0241b00401c1144640345c2503000304443e01490b44100d03142000030a84c1403080c7e80a80c4620b90710100c0310300d880300440c480e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 641626762 1250 641625512 641625521
    0x14010c050a0605070e030d0c331a120102030604050f070e0910080111210f041124090415030506071b0c150e1905100507140c0307090e060a 61
    0x1101c2070141315121105e040d00c080000e6551310314240d0300d400c000141071411001c80d4202001040114901c290200016040e010120000c10038500001078a100f940c0080c0503068880502258404040282c0a410003019002140328580c101c5042145544440c541c03141d099091340c4050004081d07110380e22440c03d2040c40550014200016410940c2d0340e1040356081d40e080c144a40c032801c1c1e0114403500c1540007143c0b4074070390716005d4150054502d020a400d842c900c038010009001c4061401980c100c0d61102010381010603130145100d0203040040001c164203510605040e03000c3c6c0c0c6801032100c03d2140180801060b41e0b400000b6012130b442c1c11000310342144017118007010340e940e58829440045d200620310001008410001085003140090244c50b07514081d010601942001c03941c0c0740382c80c102040f01c00a0710000c43c1d10340070040000728100c565005034140241a02e030910a080c056010004002c8100b4808500702e50764a40c0314004141074403808201c00c90591722450207d800502c0c076402 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 641628012 1250 641626762 641626771
    0xf030906020f0c1e0a020d120c060501090518010b09040f141f0c0806130c050c0102070809360c072114090307090509210414010c050a0605 61
    0x303001d400c015022100e500b01c0e51009080c92070f264420612805a0303020041e62204009030900503240307040d55500800d100345040c02004000e0100c050001c0c500f140074407283c0d0f11864000c0e604001560b10342c01e0110041c80d003072300c6070316184040c40030b600138454050003201050703e00030745100341503100da5607230310780d00682c11008039016021103088400c1c16204000c40c030786104e082c0040b04901d00803400500210390590241d04204223078501003000780d44031020104c4007030000040014840b400307200125420300800741c494015500001e00c02060080160240c051140b0031612586007c103408070280c0e12410705459400099880b4110400f80c0b0860711100b03910622000800c7d00d403a04694403205911811038195544100c806544100658007616140301c05503190600c6140c116050002507440e402840781994a6480c2e500242e08010240200c1550104002102407400130043c0200c8854200380243c140e004031401031810150720654035000295002800f0308005606a00c070100500801003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 641629262 1250 641628012 641628023
    0x30106140f1210021c050f16230301030c090b0a060311090901061107060e060f16020d0b0406050903071130011a0904021f0c02040614030d09060f0309 66
    0x100c0076400a0140020074203c100a0030042c0e41e036404140000100300c010607950700b00e0b0302e80420482d0304c10703c20907911742080c4014240b0110500704081100c00d0760b101c4504580e0000030000d030030388040800e40070714140c91141303c58600160700c4495983c101c1e04134012490f44901c845004015a900a6005546041c1c000740c845250139003010105519040070b0340144000f81c003145820359840c000380035020280c00107103800001c22050b42c00080c40350103400a03d40690300d0000d04444a2848004010300300e070340c042c0002e042d041807420108202281182d0903106907080c280003c004030fa001c42122407003a48520748440354440d0f00d00380702c2d8400040070581c54000da04041c1c200001c1c020401024031004000003c5002120f06a4809603101c413400c48038040d241303090504c401a030302c2c01c40c00021a6034079141001c3d503800c03910084070884421078010790402c0c90000c001c00c4003891074860460041e426000c90b101e0514064046401290a20070040040c41341d10103c4c200d030b4130a812122525010742c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 641630512 1250 641629262 641629279
    0x30b120a080a11010614130c121505030d02010e160305061602100f060512010603020f1903150207030306080a0b0c0a05041e05030d081302010516120e0906030106140f 73
    0x440041c21503000b46c021144a40d81540150058a05245801002c2030b2052091209442001028042c07c5120407510241500e80500d03500511030340f02c1c014010300b0001c040760822184580301900a1180c0410b5150381d01030030658201c2818010141c03003c0701c0c1d01800404a5a40344010901d424500c1100c1c20118040c80300c8940200c02203000f140d0740c0006411000a00f189000c041126007200e010084200e6410701100700f015a81d000e04001181c0d1054890200494210b980940009400e800003414807d140910340b11014482e405081558400d45041203102d4583c00c00ea5502c0d460003c00600d1054000002200d000d514405050340242a00f407190501c1e40390b804001061840f04280d000321040f51008000c5854100141124205a410a0822801d0009105180701040507021741403090000e58031501c5409a078003103da80341c01c43c0c4401b070740f00a080c03030090041901c41d510703a2080b4040c0000c944685411303c6200121102009600d101c102c2c1c0350140b1800c1410b070b0780071395804000e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 641631762 1250 641630512 641630537
    0x71a0a0609050f0603011a01020303060d030c051506040b0a0e04150e150f0c030402010c0609080d1d0106080c030705090903040305030304140609010c140325020d030b120a080a 77
    0x18002c103802080024803407880b03454902d082c1801c41d18104001483d0b00ca2002e80130355103036004011284c1000068501c001c00400c1d84c01c3c10f882c3c01042d220001d1a51185e200070900c00040350301c14a0042c0d030708941c2032200c0d2040d0000c115040c09540603080c1400754007030120b4005502021381c0034800c14601c1e4085132102c81201000d0400f40052400303046a40c04008100c004805c10440c103600c50a0401c1c0d15007103042a4000030100d5840c5c4a00805155450b10460140304040701600c2c4005a418014400d1401d8030300d0040c040483d000381c0107484d600300580032031849004102d4130080d9102030014804076181100b0807043c024041e0604420303010030040400800c41c203000440c89140600204e242d00d81c0460201403034020010306802c003d074940380d0801200395110080110310781e10b0814030782d00e907110000380840c0d10040c500d072128039a151242c0c4205c03198002c40c1c219114605c9440030080b81804ca0240329000300d20707117101403141e000480c10400044110000c0d2200804074903119541151 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 641633012 1250 641631762 641631779
    0x50c0405010c050c130c020106080109080a050d0e0318030f0a082b02070515010e01080307030807110a0605100e0108120309122b14160c0605040602041a071a0a06 71
    0x7581d1041200d615240d0285506d5203809005120040c52800001c10544e00d60b074441d11075501900e060360342081400182600c002ca00ca400c1110f1000c815019642d5034a00d00188010542c2c2d0b41040900a000346070340b0b03800122010504903100b6030002102c614240d00351003121445948201e00080d07408a000c02811400741d540b0103015010321074030007440e4080d00c3c4003280801120590007035120506500040c800084c0c040241c80c0c885a0504144005413103a41081e0703422400d900d111691446210084024030015402850160103800c0000f2449038658100b180d90b0f00003401654003680c402c030000010200d960008642c0004d48a003902c000d400d06407a9246554807072a100411203003000300708440040740a005030185188100d04101c40903a0740410001120010b200c80d85162040a102442c01d025800600400303a03c0034007000b503881e00f03140c0300000750003a020704500080c480344240c641c1e04008085601061704208070f130200342588005003688080c010070f07242e50b164076004005031085 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 641634262 1250 641633012 641633029
    0x915151119020a24050d0b060d05041203020f18010216080f070506191119060509100207030503040f110a06020d020f01021314030f070e04060f050c0405010c050c 71
    0x80c10706440191446140100600c500903034000c00d00c0d60004100f4035441c202800142c0040d00080e00382186c803244000d0040c00104281901990440d40029220900c420150b0265205074072500000214092190040b001c90140805441110324104a10041c910300d50f120b07140314a1741481104c801d0422810100310040d801d62004e60b09501070036064800300014808040508402c3e1000d07070a00d003042506501600d41c0b103410b0418003440303030b00440c01d1500c148414010000155165a1146050f1a21200030001110b101e8064018201e49841d031151358000c540c070854143e95003506513103450b01c0b2411080e501030000c542071030806804640c46d403a0300039000c0c02000140c01519040a80e4500641000200030320b82c2d080340d20401031064a40d1482c400c00040c0e4400c00310381d24010354440042843c010041420a40c1031140e03000010310080d864034103d1180d8414102070180000039403010003034440642d083d9088035414041809654489d0610011044c0600b00f155071000d010008521030b81e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 641635512 1250 641634262 641634283
    0x42310050a030b010c17070f2909070e040803070201020919091d070b160506011e060302030f0f27100b09091b010207090c0e01080109151511 62
    0x80c00105404000a405216000030702c10f085c2000400207943e40d903200d0307600d03821300440c410010000c6881d8080c0b00d0000c03214912580c0c09591400013181c540c0c59010480340f80f0300d02e40d00e1244404002400c01d040450100219040201821542d403541d07928400d40c1d40004002c0402c41d076081c001038a007a562401611039036040e81010100e05818000b95000366485042a400c01024030382c3c0e4034170f0001002811804940c20300b410551200c0b2030340741600350307000c0c0320758094810304c240000820088120107010548454240e0f03c5401c65640e01e40c150140d0104035035010040300100d00040340d00c00e5000c091948025a42e000c004000114583c0301d83e4610209200c0b01603030b10040407011607511520914003590320848051600e450120002640c0301303040640f00c05100d106864078196039000701702c9000504040d040510400b864242d00510004044280305d001980c582d00005150b40c5500c201c0c8070140d004d1082c12201814045c4c040011040d601d00c1004000c500116284500e2040c8260100c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 641636762 1250 641635512 641635517
    0x40b251505040b0708130611040e180705030a080301051507050102071a010801111909080d02010e010c0e030c0f0102071e0915050105070f021801060816020c06042310 73
    0x12420030b41000420640300414031410300c09107005214100081c291481c1c3c86c2c42c0c0c090300104070904d80032174240c054011a403001d0b013200003038000e000d0806004800d100460541d407084400301641c6504065031a51a00c1001c1c02109081005000343c0c02e0450116a40041e07001407185007003001e9032243d003203070701840d01074403004401d2a45034003400307002030800d004050560084c070410000c007403070000511505401851046942c12004049401046500001c00c0804251003401b00c900304060702a102440c0b440c07446520b0b00e01c101c80f205000794445501c0c0000540105140501003090040c4500d040d070685041d4407a468000401031059601c40220908003007020050034a80229401902c986050450020aa50500b030144e640c0c020241e5108540080b54210020130718000b1580c600d000d0203000c0400181c1c0d90012607025000308185004940250701d03002604111841240c681d60b01028403a0b01040c10072081121142c0b40c00c140d14001e004645074008031000300c001a0b060b048121b001c601 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 641638012 1250 641636762 641636771
    0x30702030106241d10120c0813020603061216060210050108030f180301050709170a0b13030e04141e010b09060f070c0303030b0f06040b2515 62
    0x114282806402c0003032410021000d000c0c52070240194200120a4004003000b400c03070b403070070581c48401080b04c500c0c0401520980160b010620000e110510b158401500c4078184110042528460101a84030b00303a944642c4020b040e040d8200102684060103099108408407804081c1003010f1280d09492060f0b132511591480c50400c0203802c01e802c51096204442c07500b0010041300707501004a80240100b00e40c0c2d030f0764960b80040104041d9800003038240c0c06601e0310040084054010040750281c5d040c0b008a00400d046043c07032039a580114400c01083c43d8440030114031000400040c180c58103103e03081c910f0940703213200c0c0442c0890b80f81d8000b171028582d601c400e010b40e0f5808007440055002c2c80c1560042c3c81d44c10841c00744a1751003008019400b50900140a25070b622001d400e94580c25800220b11901c1c0d680c1c1d06000f4050b00215035214410382c040c080d52800d501c4d0040441c3c4c100e4007100062801c0041580c04c40782c0703014070082041707406040100c142c0c00140710414540141c1e00f29030030001b07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 641639262 1250 641638012 641638027
    0x3090301110c061302060f040303090501030f1505091003021807080907060c032006090c040b060a091205030c10050a14070e040f0e010c020106170105010e040602161403 74
    0x609403440d12659071240601049442071910b008a980e9a100c2c180c40400b4050400501c0450054403481c00307007070240c0b10046404820194000701200844000741d800740700780041c02803164212201422030f0300c68007001c04410030203410181e843c20b502c0003042d50186000c50342c80c2c000c5905c50a84000d02500d4415601c2000001c0390040c0b6210b41003000200280000790400a000d4030b900380c1420040c007408105800500100c10f603021075104c2001540c19142c103400c000e81041c0c2e0b5800c4294078188160704046c0450100e080074029101c000c0c159a035a00461890a05002469039400905850500007040400c114550400c11410003540e44040003031580b80000a60046a40102c0c681081c0c10800051203400d41c0d00c00c00d41441e11070210380000d0204100d0b00000b00400300303a225a0640c5d4205600306924075010361000046802006000089160035440d55080700c81c24041e4040e03000469000c038021603410743c003800144100000501c0325104a843d03030106411040c0f45089a50710019001 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 641640512 1250 641639262 641639269
    0x2706090c0603050405061b2502182e05100f08060307060e09060102100e150907060c03111006090e2a01030f06030b0f070f0507030504030305030702010f0e0309 70
    0x204001c11140c07808000340c1c10300741d0350030381c68550140c10000140343e075800030031424288a00300d03604020441510b007180402031108030382c0b020140c0c4043c0d105488000814888112441c4c1951140404120501d40041a45180c50584c0500d08100e0b40601143c0c07c0803646440b417580da000c0020242c0c90381d0700003105032000208158401000c1368043d4211480c20000385030040c10201010408481c514065035a010040f4901010340c20240581d43c02c16202548520003c030701c81481205034403000e4515541c2c0d20b1a184e54016030b2040c1000200c03040c0300100804d20400e421540380078501d054901000b003405241096956603000300985603650f03844c1040283e070801c0310183c51007041c1c0c400d03c0300c5c01c14450002a4400003800081c1850f4075042d07191b00ca55110780c800070155500c01c02e00041c03400c1c40340c4c0068ad08a41100c130301c5c0114190404e002c0001c0d0180040c0ca2000b0342c1030313840f01d1401e415507904951700e40000e804541550340324440846054090f01400c5201522400210740b00e048041c1003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 641641762 1250 641640512 641640533
    0x5060a0203090d0e0607020906010e040501270b15070c0b0d1a04150501080a0902031002031f2106020c06040f05070b07110603040f080c10141306270609 67
    0xd000a0211a0313040c0c006640741c69055540039501240c910929035240c60060b60041c42054215903c1031818001280ca4041c0007030707a00120410480344d616006107040f44d0401c59003010403555010201d8001404022404402046c04c0c500c40c51520004c590f0707d000703040c0c0d00d8011400c0c0802d802d803100503540502040e00641103e04604503130070304c17070417104d039010410143e0140210f50400c01035900003142140c0a07001000b0b00e03680502211010b002c401c0c0c001c1c00039042a502a548008050f0305c8290105c003001015094031154589104110003500300c4800110180303c04450b402e40a00034805020340511507284030b68040d03d01c0190000803450500c1c10301405803c42000310100380b01c01004165280c104064900301920480d603681c540b0f081100215601c00401010303400d000641182c24400840c0d14040c0128061081c05001449881b10b040500101c8880b00c00040361941000402c1c069080f004040030040080608820049504159414914825144280c13103144080c00c01c10711200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 641643012 1250 641641762 641641783
    0xc0a0c0509101410090506120f09030304080f13030c183c060806070c060e2e0603080408011509050610110313090903020d020a020f0d050a05060a020309 67
    0x44420200c2c3c10520180358031502e1248641c001c1440d040c404d04154041c408080240a000341040c4d1200680458072841d80c1c01202e030303100e0004030b03040894842c40d000070a4a00556002d0001824848a2080900780d0f4001d00785200d03001e04c59030b000201084414120202402d52500c0303000340e12000c0a001e005440401180542e016500c90142c4e450101c000d8040003062180c1c50030701d88803542c10320b245024102c0d582010029000d0a8148250750f03400074800c0150301d01c280c0d81403140a41601d52140ca0712158018580c10207101021100d0703c840c4040480081e0b0848100058502e480ba250400e01e600950001c0d04281e5407104c440301e03e29000c4a52500a049409090025251400219040b4810b0440e190144820102c0249584a0510a44400c001600041c10005170ba40c07044801800c91800240c1c0503010307048502e1080d03480801d5881011b90041c01d00c000840e031290034040c6400c0316000590b41401060800f00c00114180710060190744e01050147e16800c212450604141c100300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 641644262 1250 641643012 641643031
    0xc2a040606080105030c03160b09010309050d020a12030501030f0204021c060b030702150103050a080f160813050303120f07030f090c0f05010c0f081b0d0809010b1c080307050c0a0c0509 81
    0x80d508d0801e19200400305544580c2d0010741c807013246600507405030900d804000c109000c0d2201c02034203a0b40c00108113038414015200e01c58940804107060742129000c3c08060080b07001c40d100c1c4030150604e90000c041420000d17000074040d2031051000000c55029070840c10b828079000041c80244d99041288201d0160b024500982a501d540d4a56545442c0000010310001c1c000c1000488080c01405031a000c402888035604100a0741c03a05102c10381c440031800c406440f110f8404162424000251005400c69103030001e150780301e4404044400302c004101e44101030311001710005c00c40190255102042c030a50043c42c4203424030b040b611414140da004103041000300a06a4085404482281152500881e51541c0d440b064000f41041e038080c07241300c0800340704c0c081020b10403550210f0064410300c2004003c0210007000700070010410382035100c4036030202c0e081c07062401180c0000b004540245260904914100c0d400c00250708080144409a4003d46040410803141c24800e0005034010800b5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 641645512 1250 641644262 641644273
    0x507090f1a0301030209090703050a050f070e0f0a0b060d11040f080d050a3f050a021903231305010621060b0f042f0c2a040606080105030c03 62
    0x41d0003440e034502052002911541204000c990000400d1082c07201030b64004043e41d80c281e207a818501c1c1c0e140001c000e00d1301c1c2441401000115038200348030660003190818680d1100303454040a001c040c2113107810b0345520110811891500311094801c2040290043c48001d44135864a404c00e04000e01030f42c4a50310f903401440040110300e40c40000c45002a901d42418900740c01c9260b400c1106125205450f802c502e800c0075061701080e00c500da103a803050302124040c4095510482120141e0280b07d10ac4414543d01d218114200c0d40250441c0e80401c03214401400700285202c0c050035043d0050300c401d2040402c0e44221f0051280a00448029050313030340308a00c401070f0040d07114a20040721038000d44015900c42c00c0301300c00c0d600d040c3c006c0c400000003001404039440c031642001c0040200045070510080320100c0c0f60010b01d440b001d4869840d0040040c00b0f2005035805903001c0c03100290300900c00c005100130400025903d902c202e0b00613280301c0d955400c5541c10001072601d480c04603100148a0b41c001d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 641646762 1250 641645512 641645549
    0x120d0905010f020c03031b070c09050f2401050a020c0603070c0209011508060d11100302190908030a18170a03030b0402070b15040b12061b0a0e011803060507090f 71
    0x4101c03500810030034250b11481d1000c10340c207c61070080c000000d2907000046030000b002d44494104501440b0350300078055003601e807018611215840c08101c0b10396104040c3c4815419030048000d443c000030f0a00503200c0448001c0300154a03035004581e407201040360340711910154149807958a015160300e0f01c04098a645e0400701a2680704028400741c8103140c000d0000c400c00071040b501c2c0d003001130003501c010200362900360094080c0d044840280070340743d03421140c0c83e80301e807181d1102802c8842400c080e501c0c0c5129800e046680700008902c0b001440102034001400d150034010310515291140040d02d0107808a1500600b40d500c104a541d100340d0043c420300d0040707108140301d1900900c42d91001c02030640007030302240240c040403400c542c0c40050401e00c00721001012901520030002184540c41552001144914a0250310380c5c060000d0f281c0500101c00e540030390f003507040385c032200d401140303483d656583c03a9400c1d244c080b15007800040342800c007080103c001000c03442c040c00e00070950401d405d01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 641648012 1250 641646762 641646787
    0x30506070206090a0206250317090705150a03060503101b0305090d0309020a1208091008070c0b06061b0c0405060f0d110402070f030203030702101b0e03120d0905010f02 74
    0x40720030181c1b05d80400281e84c01158994104020058022012204142900c0c100540188501e154282050f0001e8000170529040455840140d03600144006100020740c0c4821020340c00204180c014155604030126541da410000401c10140c440b1000c04c1c0381c0c04081c00c02c5000c0d11804010b1040c50b06040c20b200344500045100b41000c0041e00d000030b100407150000460303c85140d4080456801c0055078042801000c42c020020050250f9101c02010703018a02203640d807008668400c001007429040000180ca0811019084580148600d007000b00b0b42101202c5e807070140040f410150b01441401815003030074041c082e440301c02190400748188410010176841400a24000d00000300d01104011541e0307158142c0340d9581e006505450000d2080c58065540c0e4001e4403000054411b6107002c00341100d0a0081c2100e1540c0a412040004031600059507040b10321140f41d036150242582460707160105501902e200400c108000c5000e1169041460844110316064101d8a004001a285000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 641649262 1250 641648012 641648023
    0x9060e09010626160908070f1208040518070315240207080106080a03020724030b030a15150501020f0d05071a0a06050f091605091201090b0103050607020609 69
    0x75480d00b4103420441400d603540502e40d400d8280030000f28038203401e01059050202c21804090065284d0700d05c0b16440300c800a42d40e0005100d94030700111400800d0114900c09507420085030302c41c809035824603484500145079072a0014a081d44501d0860070000c4095043c09100c1c024103c010b482001542405806401b95080007813007610402e61000b00003416108200490080602c103000300729680d220314070b040d1145240d40c816401445161000300c0ca14480a0002c090203014003004809040c0c088401e401829100781c0b501d074540900d00500020418070440a00607004482e00001c40c1d09000500616411140d0805030440d8008404d000b4120400a06e4a41003050f0f03040c042d072207461600e8009103202d0b00360b000c024010042c0080c4030805080b40c00c0726059071030071a10716070b00d8004c080034004681030448216501c9607032004440e5480b4040c0000300101c0402505005011051203030003800c0d12440c0f40b04603613003a005001041400401d100711600a901440a0f00705420522165035032341c1c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 641650512 1250 641649262 641649269
    0xa18051e040c020f030c010f14093c010c030f0b0616021c06050f0c09090f0703151205010b0f1809031b0c0a05060408100e0309040504050a0309060e0901 67
    0x299900c54000300e105008001390300c5100c0449044076518417085081d140a441d2086500c0b50307180c10450481d140000b5401c0c4184031316456801403070f051070810380307031042c548221500c41c1800c1c3e80342d54800f42d0154501810885402081c002180210107003200400701c4000e14401000d4a00d8101c8600d602d55510048654200c07902c559900a5400ca0000a80303841d0300002000d25107a41c01300000800c00c9982255101c2c00c1681c041a182c2c2d03503000c1000c1d226205440303106a02c07454540020703024000c04e0401d00d1300080189000104401206c1d081d10000c12150810100d04a0b555800d404015090107111801e4206a8010510441160210344d42803018102c8182030700c000c0001414000d01081980c1d5603442c964010718074422001002070311850b00260060007943d0f0140c0101e02810031004407421928242c0007094802102c0d9448401803804031003144142c0810401e071011035549015040c0183d0188000e080114211303d802f0b04203c0e2160b0124040c010345002950716683d428050b541103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 641651762 1250 641650512 641650519
    0x70503071b02060d05091e06071202030928020910030f08070302190f11041109040926091801180e0a170a02070b0c0d050c0f01020a18051e 61
    0x3481d01c1840041c042e8092584d4808045203007904100c1d0f40c03400012803207138024108003030b001040f0001310032588484085030b1000128100041061406d031040c1d0065602ca100c000998901c080c81d020003040c4031811159410f01c0013280c00c0d00c0001d502e401044250010505d80d08991114510341d502034040b0341c8410b001e8543c10000c0f403440241402031061403468000303500d4100d11101c6601e4108694006880c0503103400e210310714401c825080600c141000c1c405001d0159041c011940100701c090803003130004403906480000c1001d0030103041d500400391119201300d8603171039030351100900500c118054100706d0b22480b0304c00100080d0054402c2c044251881560104850000083c3c0c60301d00104000020204d0b0a2000030884048103040a0310002e68190300799100c9a90b181203030f02c2d9900842d840c0d28541d4004940b01801d5070302820080200d10f6403401540d8441403010646404ca0300f04070300480220314180c0e4028051141b10728910f0241c501143e02004005814415140602c081d4038040e01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 641653012 1250 641651762 641651807
    0x30c14015c060103170c120403060c080604051314210406020105090d0f18051002060a05060a081b01090e0a0e010c050a020a0b060f0a090905010513050312070311160b07050307 77
    0x400d980c081c1f006020140e02c9005096590380d0b00d01e42030300200000101c0030b00040050011420502e01405054000d043d10509c0c600784a015440700c8104c0041c4904d9401c0600c5031094000032605e00306034018040d0011590252660703c1c0c040c1c0a4291100100118203542085500e03090180d005209401c503206a46050303a40700b4204150354140c140a50440745d07003c0840d0120055441e80011824418400340d001800720b1b8440c1010300c0b0140603903000e40c190700d0f00003404040001c104c144114654030300514121114668500034102c0108007507401c08091511180007400710182400b03000ca4860b06840c0992410101c000003c5d210014210001c1209041c54041810707950703641c8810045410080043c001d07036070354410500040450040444055003040000b45040141030041d000a80c0c101010390f1802003402100c3d51100360091600e4180741d0f40c0d82c12401010340400140800c88a00f40c001e80e2030b01d450341051b524101008040c3c030204842002003100b0300c1d612154200080c44c403042c4441 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 641654262 1250 641653012 641653027
    0x603050606040f1203020d090515160f0b010311060a081305070905190e06040807120921031107051c1106030c04030c14015c06010317 59
    0x3105071156501043e941207500b40085807001078548008401d170310a03000c55081d2010313404140c584980c02d2140580c400a03c08520201600d407000034441488603c04408003090183e96011403210344510554030341030034100601c2003001c04000002c40c00c1d81201c0701801c003950514001c0c01c000c802440e5041c010324811142c82041010090107024001c250360034003203464100c0c070784501d070750800848a0b24281449080c003110900460070a01594201040904c0d040c099202d101002d8601400c4000b0022070b0100090412078070800218a1098000007210f2a1090b0800401c410101f01e080541a04031907420081c9581e4865000066024010602812010ba08100d0103000e025210550005400810460155405002007050f00d03c2040b0010215480e102c0c00701d00c0d12603540c900d07800b2408501c43c0c031840b40040d08141c81c0700c1031045a1701050405030a0a5840d08040d1003300c80501401c114260001c42d121001000d840c40000060a0640c075613120030240398100c468001d6203060006100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 641655512 1250 641654262 641654269
    0xb030f01030f24020901021908090103020f040801020301060e010e010e011e0212040b1e1309050c090d0b060418030c0f03021606050d18020123040518040605071806030506 75
    0x40303045603c48264050b10100141440c040c0d40005c0910b0f0045c000c0c801200700c44141c040303c3c01d860b150070401003402d100d4110010f600035801080d18030070303e20040c80000740f040c0702400154080d050f1a6240b4071489107d2002500d0f10301c81c00e9210703052084c0b0403065009640e0103041c483d091300c8107004500f0008100705042e4241401c01c3c20110464070700280129803034408a0040483c810980e000895082c520035106041340510414030481c1c1506c07440c10030648615420203900100000121441c14891070001070410080042c11607c00315010b040203201d107400d11981520382e000d600d1841114110342e41c000c0ca0803002001c01058405031072282814980300b0819411317540c03801c814003180c95480e410081c0c61034005480c1460301030b0600031000c844c1088848040e03c1c040d030684036000d404072240074050440003040017003401c5031810f00002441c1da03070301c0340e038285401141c00f45404035050034141401640d6006058105010f20000c07135001c08000e10501d43e046541d2031400188584400000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 641656762 1250 641655512 641655533
    0x3020d0914040f0f02040e190e120a050f0d09020a050306310215040312140720031b03010e01050c0702010c0615030c0e06030609030f0a0905091f0b030f01030f 70
    0x1d01004c1d07101207404149401640c4016006038000c0c41a80781c050300c640c0210095076851708181c2c24540100c107d0440c595000f1025040b85190303410000e0a00041c3d001c07102081d003002c6500034039984c07140320400c03e5007001300c1c201004c1e01c01600505100c1c906205802c90a80e080804019010500c40c0b50900c00c94850991650040d40107150301ca241003812010b0f0300507002070009840c0c150f0031034044205d55002c0c4410004904101000a0808010362200750800f4040462050200030780040728440b03550034440c1408034510315010504080300e4000341800c45a007070044135020f80c9800240301e00c00004800f030b5240300e542481c100f4003560f62840d0480c00313400c0400c00309200e240c02071404000c10004204001c00c4d542d1a041c41c05003962a04d00301550350b0f00c1036802e4806078004022030f04000007074200408a02c00f81e03081803201d4940d0b94012a030070040448201b00411b0310455205203d0b400050444010541d841078581141400240e80030b0b01441840000c0100c0ca41c440d0000402007402c1c0e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 641658012 1250 641656762 641656781
    0x303220609050f060903071211030d051f0807050f040908040e09060f0a05070c0b090316060f141005130b18040b2802130503100903020d0914040f 64
    0x3000c1c080c022003490040e58903144260400054014100050b030740910000176146d0309034218022000c1509504010780e0464520304002e0344902040044610b580480c2c05514041c20303440700f030040429060542400d1030415600407c0d0150000c8008002580e00e8035452038885404031070004102c451854000c2a51003180c0c0113401c40000c1100f04140140081034445c4524070410120410740ea40c2d1400c00101e1360100c4185011520729038010000c1000d00300b403640d010f200311040b2072401c0c44003c040140030401800480304140c4941c0c440303143c00c8107400703044d0b421a1400703501c45250501d03201d0f40008203140e00455000d50382840803030851481d180c101042d2604040c2040d0180d0820640882000c0c03811034060b900d2803c604040f8511072100580402d5001e641c0c101c0440d500150384581000c0d5008880994030000000c81c04903483d541446180d12030000e29200040351451464040d0070f2000880c03c0c1e80921460703103c01c100040104070030b48180c0790b080303500045841020140b40300402c09441d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 641659262 1250 641658012 641658023
    0x30b0103151d03160201091e0f0b0910110304050d0b0f0105010813060504050a02120607031103040c0302010c020307090f0603051c0903020910120606170a05030322 72
    0x1000005220280c40c0403003490795010018400280809801c94601602c051000d12982c410041c840b00c0c034805041c40003800748145000d80e4420fa81d04604000282c8050320400c60004119040001010440801004001c0ca803074a50800c0070399000140c4c1d07a090850f5220034089840881d20b8407400500858025100003484c1000705081d5040000c0024070403145034460b0000000045510f43c0106602486a20764110300703041407200795116406031001410072562482110000b100594407510020b0384050100c0040000b1b00d0445030003015150007a0419841030010010303c404920401c1b440015640c080c24510805c80191000ca890000541d20008000c0e00d86281140c2c04500713034100f0021607000300203c4803403182c01c15807800c4965920020b40c1c04104e00030300c20401820b00000c41c6600800c13540580c405696214038440c0d210240031000c0710070903030b106c105001181800da180c450f841c083c5001000700300003a40d240ca65a200180c0038075400c0d1015190241c0348142110740c2410942d018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 641660512 1250 641659262 641659283
    0x30309120e010314011401110709050403110d0804080f0c0f010f0c12022503142a030910080a0f0252030309080a0e15041d09010603 58
    0x40303002031100011103009400a0b00b42500e140c01070084010300e60680b04010410b040414141c001900c01d204c2010203082540a05038000800d00100e20807244518041c5d181c50b4140648941820705100580e440e450501120800b4440400d00315000e4840e410b02e0074803055a41d03440f0b5842e5500c0c0450b042c4260802d0340c01c00341402c00c0144290401035688104e40c503210300108a07039140400340d01a085050403c4543ca42040308020010f002640c40a030090030600e110404074442402240d2200a60001a034100b5407004400c0502085a05202905801440c249115030300011071250300b1503104c504100c003081c042803c4c03030210340c0481c040e06c5001e082155038908112a0901c0c03400b0b0401c211014086068045600f42c1880d415940c5222481c030542800c1d1074518200420300380d03142d00560825568401c654001080c110041141c283c281c0c45901465652100700101d22550242c84600b0180504c41000f0480c241e00f9002c045809404080003e9601d2400c2c150040031107901c050b0907001d59 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 641661762 1250 641660512 641660543
    0x2c060a0c11010e0d080c04050906040f09171309090803041b1e0f060e0a12030c240f11121305060f090601090204050901290c010b010e040b011407030309 67
    0xa590010000135407114a200d68802004c1c010743d01991003820740100241d80040c00354a001ea000107480400801c0014980140351950711001000404010030403400203a1010300c0540c1503c40001030441d2101030103000216034601259001c0074000500c0354090030740310604502d404d46240050300f114461300226018481c5c080d042c0d07405520500340404201d000101e6510b203d881400d902040203130401050314a49008880c40e41000d4000350200134040d0300c0b402c000b07035a41c2800c04e03004c10140400c4441d803a2801030388045400043d800b15109191440401c00380e08000150f515500840300382d20b940b542e9018040c1070112110034002c016028003010001c41985003490107014a19000884400f680c9561600c0128491800350941c000103110040100d101800d91040707500c0d003141c0310072500b8261586140d12581018112100d640d4603504281e1065a0203003100c451540100c406004000c1041c0000e401f0804440c501440100000340850515029401c440b4a40e07500030441c00c40e4420 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 641663012 1250 641661762 641661791
    0x2090d2901050a051f03020f04030303060824160c02030d03060e09030307050712121118061206040b0d05070303080403120213050118182c060a0c1101 66
    0x129103001214114448000310312070802c0100102070303880c06030410290300001c040c1d10003852192582e030713010940c013042000c421109203000f0b00011403203a14085801800c010302d0a00740b0491509010b609517030610240e00450075010525080101c800707541e46404186030003103505801c2c40358065098132958180500e2154194040d60440341100d190007445e072100741c00503840b0303c01596801d0024178280103200c04180c0b0007040070401500d07400d007180104100c503035a0040d159440c0039100340440200303202042801104402e04540c1c001c60340645410001842141800710241c0064042c550303541c0200e0311a00c0310300c0034104880c5c219048031801581d13403034010004201180d00700c00082d42c82c481400c04031080d0083c1c8507051180581202d00d13034140001142c1ca900e182003000c1405241580000791941481c0040014680c1a5070219010f80d480c0d0700e24075001c80c440b90816540100c0b103000c00d49d00740e000c155180c00c880d5012020442c2c602c245030403502c800d40440c10280385e510b845141c0d0390090 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 641664262 1250 641663012 641663063
    0x24030603060105060a020c040b0103090b040b04031e020304180204170307030e0603131103120708130f0f03032102030a021905030108070e0405120c03180406051302090d 74
    0x104808076001d50ba00e540510510380140802040580c0c07114842e40050300e015041b10000e51310614000030114000d40b212065184240c40c1502c1074151003007032000341035210118134009140c42111450b04102080300942c2c91003180308510039a442c01d8003102d409011074040b50002c00e0030f5100c18200d06100c6075425103981c008101100410540d270038514035400d064068034411015850b80801e56a91600c030414644200d100856050040554150b02008020050100030707000301d25941e00d8507505164407200c003089400001c404640c0b41c4d0104403404080f0052802daa034180380c82aa5648500c0781c8a15100c07007148002e8006001004010703441c10a40e014040346100c81c503102e15030300580c04040d51188000e0207142400c0e04801d00500c0000d907154001600144103c0031a25814240554050305c0d400c801c594504070b800000c1ea07095001403c000211009004450402800c5e107801c00140340181c0080358801c1e541d070085100301260350381e038912584e602c2d00541e0741c4006035800c41d80310881d203 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 641665512 1250 641664262 641664271
    0xb061306080a06140d150e010e010b03060108070611011104030605150d08030c1e030108060402090901060e1305010209040e03210c0f071506030305041805070207060e2403 75
    0x595281c0000e4100d90450041c0c000715000055801e03c0c403012042031000d00c5040c41c40607070300c0c10a142c2c1c59001c2c2c03000510850f89040700000000401c1042c43e40343d9030070360b617100c0c00c030902c01d5200c00018021903d02050f20021611581454110362419490040c00740a0f110801281454003080c0001804925042244255115001101d04407400400c0080b80105058080c00d050414000103002940304001003c2d014801c035101031419440f01d00501007a80260000c0341260031507000e102c110306101d041c5a802c004080020b0140383d00740b44102030003400042065250000c00d1800409001d420741c122403011070084c0081c8624400d14440036942c3c0d105540c8a980066544032400c0e60048503158103002d0f51606456910b001040c58402050760005441564040c0c051840c2048044413481441d000394805d803229522203141c03201403528800c2901c1c03103070000d074244001c12501c645d002c1181b03400e0703030241c0c01d100c4210f00707001c0d011481300c11000310024500e503c04203250f10381300460740256109 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 641666762 1250 641665512 641665517
    0x5040b0603160905070203070204180303360201090e10081209010504030605041713030203011a0d03080907091805120c0d0305060301200703020601090612150b061306 73
    0x954940c041455651100d050b10780342003000b0b000b414016050b103900a140c2080161040b6800e0001a40002d8100d891000454028501c0302d000c00e42016003600820032100e820002c06010b000000c48030302d080d002540b010000003642c00c10000110381c01400b5203406030508000440340b502d001054007195600c11b000b034089a20800501da44003117480e00841e2403140040e5111801d02d4615076442018201c0500304860041c5d0001c114000740c5000c80140c4854414900088881407440c014942180c020180300c59442403110a0400a0f40315241d0102d405681403030440480c1c2d9400c81520b080c84144d41060784800c2c02c1c5054011021103072403c0e02001406082610318811004005100c103100e00b160103034180e0010740c082c0f04264084d0b4001a44140d000d00042121440181c02c0f52400c003488118100c0001c0110f14041450340c10001d25002d1700703207000204991800c0030309041c49000c20000c0200110449210701d0b03c200703000d407c51441d441000d000c80e500e50005051000c0c4001e154083c1400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 641668012 1250 641666762 641666783
    0xb30070201150f030308251706090c04030b06041b0e011107060e0607050a06051608060904020123040f1d10210f1b0f060509090708130b07030504 64
    0x440c00c01c910181d02101c2000d560350b0355044c0b4540e42a03d840d4030080c45102d2600031105500302c03000e520365200c13441a00c039a581d41c1284001301e518955034a00649220301034900d510400900020780021101520b41041005690b9501c500c0041c0150903080c0030030740350000c001842c014083d0070401e040a802401d890303140030354006503120382c4e0301c401a128010009003c4c02d540600c0b0b050081c01000d805004206071540c204050b2540c1c0240d90b4183d0303000c014980f4101019a07150342c0000410340055040b500800c10342419000240580451120309100c0004103024890700d0315040704560040140400190f2603990710304801c20264244c00c04800824548000680702480061020094603e40005402941d800d80441d040c20300001c82c0882d14030400900b00320211317000c0115061102590500038094a0801500b00e50620303040d4850010b00c682030040360503a903511200039600c03250300e241c041d100340d40d40b0301c0c1c05109210713141c0003074a42894201404001c6074980c0003144100d0040c00c5004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 641669262 1250 641668012 641668031
    0x3050c010b150c0c1912050a0804080c01110a030c02300a0b1e0705031314010c0f02010c35010308300601121e0b0301060501050a090b30070201 63
    0x10152909507006181702a43e1034040c8110100c00c100681c64500440c103c50084000795a07941c4164480e400c504e00c030394443d0f5250421580c0c440e010070404100d000c081c1003603a000d0b95000d001e004d020386c1c0c000d100703091051408440d40682c0c0a00c400d01400c40701c20140a420b0030802ca0f8440ca07100a003643c2417150800040d006115042c00e01c0791a03864861301c021b0b65501c102040b5410380020b4a403e458400b2142040c020901584001070f000c940c840001581c0e0b0000340000d08880d01e0740b1009015a4100548520041d4121071110000c98513040944040b0160308038852045c816908600c103401c4040002200788514240074215159105d4200144d04c06010080c000074000000032400111000740020019449020214400b1140000100d0b020400d0307031010400b02840000f201c4050344c1d840300c80d4602c1c40d09000fa00001d00342030034603a113448240500241840594007a0300c0c1c65283c0042c1d80301d110794000040d00d10100b1640103581c2c0100c48a0a46c99512a003524038000641c00e065004 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 641670512 1250 641669262 641669269
    0xf1211030103170705030301180b040212100806090c04051302030105100315050105220e0f0a05100b06030115170112060509012d0e0609012003010501020a03050c010b150c0c 76
    0xc8000c241c05c40002d6041d0381c60201d0403a0300b16a1144810381d0181caa564086160311036002a1000703004840ca040c1403854101158084841113512004076684802c0a02c0108880400c0d0010340d240b041d20040b80b00c3d500c240c89441d15100c0038100039010342c40d01040004004050750300c0002d0740e100e1040041d4692060003050150b800a0150680c04111410706108400b40c0c42c0b0b0610f03044495000108009540f04051414a07101031a00038494000285403410040706001c2405134500552080110342d13502c40205403140014000c0d44180c440d800001d60841c2e000b2246d40f1100480c0c0a031050107907031200603414116110b00c030111116400c0c072010408095040c00b900ea400000000d100010140302032513581901f90009190303410319661301c0c00b40c1010000f40401440340202100110340c11044850034440e4450140c00d25001c5230007440144440da07804611020007541628106071500300c0c0030040d500400321a14150740c05182044c60904c0e242400018140c01000c03042507404203075440c820b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 641671762 1250 641670512 641670517
    0x1050f040618121127040302060105040f050f04020d0f05010203160306050108060310020d020c1207030f080903030105100e10020705150a0c0b040602070503130e010f0e070f121103010317 82
    0x30130640c4040600c4000d4105001c0050695031900340c000c80b0098000100c11198030141e4041d40140c0042c0014403442c03d1a009042440260f05010006031030045c006404114000d00003d02c074540c00382c2c0d00d005008010405488030343d0028000c55403414560140115403c080503003401080c10064001620b40c0100d48440c810940540a40320301018030044030700941c4401d00c001505503090104501b2030104215031825000006c1c1c003a60f45602c40e0401408800c0154901c100300085a13081200201020090745d044074010740d03000c0c10b0380d006414281c1d820081280c886170006c00011b610100b040c2d0000750b01003201c500752010b900d001440c500d8220300d489007940400100d100025244001004908030305e501901516005050445a44d28242142e201c9541010b40001e01c10041c85104100145507005000c60362904000a280c000d100c42d0060005100c030080c000308411400718180582450010520903035000c02000c050311121641e1030b00280810382c2d2035801600c1c041c2d040c1800701e04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 641673012 1250 641671762 641671799
    0x307030c0e0907020c0904050330100b070308040c0302150307120c2007030b010f0815010e19140109020409050a02040503071a0f03040b010302010806011d010c0201050f040618 77
    0x5c1c0a1104100b8140301110102400c2114a03100c10070500102200e43d00c0e8650320303130600250400c1908801c0c00a030b00c201d500681f0700e05140d00104000c202e5000f0307250843d40c0d4241e15090040c116601c1d13041006041050b680040e4010320001100c0062480b03900080d449405a41c680c09100590894040100c403100d408440101d450016520485151092420294020704c42280c88582c1c8994514000d01420390240b52030080944040c410480240b0199035408070034601071440b985040b026186852001d40110641d0180441000080310a50810024811803901e503103038550b92800940001d520034400c16508602e094003041e50b00380d41d4000c9074201c6a0060050002c2c60400a1202c040d98004281240991080040d9007e8201c090003a5204900581003110990300d140005000b425004042e1810040c01c8a040034680300c1c58440141c00d84000e1a0070100450b20b4030058460703110320034280d2040795011500041d83c07903001c1d044c0c0c000d110740040c0e2444010f58944040c0e032400d01044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 641674262 1250 641673012 641673017
    0x1a0f070212090402070606080703051509030307030f020702151c2a360506120a0c111005071e050301030816020607030e100c02130c03110307030c0e0907 67
    0x1c00304040021000302034480814000c000500d41490390780c6007007c0b242c550b40650003541001c482001031000500c003107900d4811b001d00140e010325225180684030b02c00103103e1130601d40d846140001d20802a4162403072540d020780b161095002c482c2d8034921035042480854501111080325514040b050b01440d20f041442d03804000c41d0020145290101c04d40c483d6240c401c00210078a542c08034140350903004848842d1000004442100e01074051001c912a000036025100400800105030384c0c445100d40d000308182000071b14201080710449800c60303242c5072828284140030900700151201c1c2e000d0381c094912615220421881d151001e000d900c1003640b00b00114a06000400c045000380005140c0400d8000d0440e51074282d5600155594101460036000521807614114580c03c041240c500c45071041e00781a40c5000f01940003440074403526001c80f080319200c00030010024000d400203810108446a466124605045c00400074400080c01c0000134940c0603800005050101041c2d0151100760b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 641675512 1250 641674262 641674273
    0x1915180e0a0b0406090221010c050c0a020f0102071d01080708060906040807020109030c06030f05090102041206180812150409020130050c1222171201031a0f0702 71
    0x352a00d26a41c2c100600640d080c40d21480c0e05001030391810154480000f6505007170048500781c0e000c1600b15921400c0d031506100c3c0c10001c6281d68040024014485513049840303001080003500101c0c10b14440c1da1007407000004500a4400e458000700b02c51f8185c400c08030480f0115036442d11003903521030f0241d48041c010f030480d0011801241c000710003014014010f04019000300d940359510121084207500c840006503407654540d000960301d02510341c014820307000941c01d00c0c1c20324806041070109802d0080c9055940ea482c000e9000135455407001190b0031041164441310002046024400101d500103404208511b01d00142e10b018452548110380695030f01c01c0340b10340b50300c840659081c0d030752640003003000b298900e41c0321198601445214540440032580c807134611150850250030090a00c03070140c805c2440c0040903090302d210241549400c0542c2d80340c0f00403400003003a6544a440246100c0341c07094000402402900581d000d4003010940c01440980c3c0c4200e1403505d01c180980d090320068020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 641676762 1250 641675512 641675533
    0xc0611030903030a0804030e09070e04020c0c1003020909160518060c0d02100e0a12030c110a0c0608150d060509010b040e010903180605030a051915180e 67
    0x410105504046880440345070240d06000070346507800c0f06100800240044013003004059120205150b422406d450440706814504800340c01c0007a415401030246901040b9072920307a0040201c81031005015160b10002244110020041d40c42070103194081c6880741c0109020326101b14031140d034070260740d96071400c095141241d0028900030155043d4008030511a00320340d00b01c20b0190740503402c2d564004000a44480c0c1483d415209503c0c03015800d50452808000805c4d002000001d40302814030f00003614115460042c3e450700000d02a19026100b2071442408001c851496541a205543c070751032002d80d81c4a0198907603410201065800c0416001a003001401ca900407a41000105e400422400000707030114044039841d1803001643c0e034407a0015424150880320f030901c0485080800051942480f01c041c140d440060070307001203140c3d00e40c0000c0c1c1901c00c1d506208024141c0301400c1c00003442c1500e400701240000d0107800400105030109800d5101c691113403504400e4444054084400c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 641678012 1250 641676762 641676767
    0x6021216020f040225020405010f03050c0f0307030506010909031e0f1202090d050a020a050102031306260a1506020d0c110d050a150b030102071a131e02011b0c06 71
    0x1412016400540911170004000d40241c03500c0346a900410b590301c00c02c0040c0c0100401d40340103a01c028030301c8500b44800e00c04500d0116000c0052002900c0011002030140007092a00307419600103030180c0110400400c60500035000010070501031307603903088044442c20b2420108900b448070b41c800324088200c41340240b80500a85d14014902c80f01c010704185c501004148070f25180c007403c0300c0315000000c0034011454643c0406000c2e103404c1c0300841c10b01c07000702100080c41915018840512401c00d50f0340a130140091204c0c0d40380540031850030340d14109001182d028000b400403030248c03c04545804140b562000a07500809190340e91046403e82040d21002507210150142c50340044940d1840008a40c00308809a00035100e030140501ca02c5e41441c04c00c007219600401c180c86a4010821100403031a8400002445003101004c0c0c001900d400019060005085a00418102540a60680d50501400304074041130003a00c0704483c01d40d045000707064504409070002c10105c0c4c4070200780100c51 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 641679262 1250 641678012 641678029
    0x3122403150e03031005030f0105010b030f1527060d0b2a071a0703020306030601170a0f1101180e0a0207020127090f0c0e04020d0209040e06010602121602 68
    0x41c10000040d40301021445242154401c55110144080214042285040402842c1c184000540c001c010311b50410744c840007517102c0901280095024240450b8050a40549075003442c4002081c0b1110f1000185001508104104803c100c50070342900007000d506081991607203403503100d82050a00d54600204801886121740d10b4507181500c031020501f10007512006101c04e50040c0141d4100c0240020314103025003005101104040c01881400b030140c038000781540c155402946898540782c58044081e00c1c003201010040c000fa201d030241c1509110b08282200741c0d1000a90b600c1407000103101e10459101c69a00c0b491411802c803800007803480c1c5444c2d014212280c4140750220700c0c8a1000d00c11705064201751440242c0c000c5440c4200f02d4031405100d1102641d8080030b0601840300540405040201c101000c20f0107107400158410072440c0d90344c120f03241d56200900030003101103881c0240b82c0c0e944090282201500c03898050314040070451050329481c0c08095150317010f0811641c00c3c0b1004a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 641680512 1250 641679262 641679293
    0x108040b0a021305090109021b0f07031502091909060824070e0d0b090613030e010305040c050d0602300c282705031203040510050403122403 62
    0x1400e07041c004213481e40d07a03400440c020810250003584030030071040301c8400920310103580e9103d60700c01d0010150190b40490300c241100d40210300c0c07001c0d4401035950900644650040c80354801d800c41c1c440100c011840c07108400b078482080d41080a02c0c2c846641c60303030f60307007946131100c8800c034414403408080c8480100072640909507291003088a610380e03012560000403070b00d088414408800c108803a80c2c2c82005081e5210606841c10883c5114540380681b800c5c1d0705100c6c80b4105034032480010b007406102c5008400400000d002e0020703000d842d0800d2402904001c0c841e2070300c90200c119203020500f481c001054080c1c1001040916900c80041d000d14035445504001c14a19140300c5011038044482d20043d42c10819407904049070f441c0786443c050308011000d61810388801d03c2d80c00e0010b80c90001c0d40f999001c101285d0f942e039070340720750030020700e8a841c0400f0102240d05040400c410181d004818010800121009019540c02038102030710482c150103c07065842c203041001c2001c07868044104622 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 641681762 1250 641680512 641680537
    0xc010c0e011b060b09070822150c20030919080717010b030d030603050c0306010b031306110a090e1e0a0504060222050109061701060c03171f050108040b0a02 69
    0xe000c00c00010904145c1d00b140e030b400125400c9820042c8418000380003604207040300702c80701c41e0b41c101541e6001900b44030f285601074132555a8a600c103914011980140102282a03103861a900c0b050041540c0f03500020540b8050726020740819045015400c010341a100018050300c445418184926072401001001c08019901c900b601503080d1400d004040120229980129a04d400c5040c007520341320780ca801c918080c0d40481c0041042018103c1030f00e4008900341c000410b0141e203400c14101501701a40c000041c80b00021b17030700320790b40c0c0c0104c2c801040b201d0322070307008000c4e82d40c0008503e52101d016480d55086081a40060404411544095406403003100e006052440c1c0d9550403002400d070b81c06911074505211410b00bd60b607006a03100c4010300b258070340300041c0074811030032150554040c800e28080c40b005005c00c1c004c05020b4040200c11060051740840c040c0f410b9800c113020602d01d0304520024440c0140c002c180b95100390f41c101d01c21a0071040c540440d48654883c1d00080d440a80032000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 641683012 1250 641681762 641681771
    0x16020f0d0f0809011412061c0c1508060a030807061d01050a0501080115050d080c0304171c08150d110a0303030b09010801152702030406020c010c0e011b06 68
    0x1080309040c070024a0203120503940315100c0100140540710902c1c0b07540340010301800050b04175000c18060f03503803200c02981c40c25003090960a0b6800c2c07030a80d944006001c01c444800105030a1403031044007070300d0a240c0d66a4030b01c6403110020b03c2251122804040d0415000b040341ca00850b00c075401651070000c14460080592940498141c01c4403020b480d0307140d0403521400100b01c40c1001340a20040c410000b4000034095180200041c0c3e070703060185000303100800c0410307149080c7e182401900c0052400b445808035140c03030b002c0c0300d5072507644902646107040345c141501036807103200303d804500c0355002280b4200340c01900001c00c060408862f5045580b103170f01e41e6405199031201805040110300c01c0e1000300b10500300000b0051074480581109515030b14003041000d038071200d560a14102d60000314411100e28072280c0c3c054030700b50400040525240004203100c1000403a070b00504075540030030000c10941501007422202c4034600780ca01400504c4030356213000e19280461880d100c02e80310780c00004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 641684262 1250 641683012 641683039
    0x10110d08090a02130e06151305180d081603112a07060203070c0b0a09050105070807050a030f0215010b0a18080a0309050319120f0c0b090f1216020f 65
    0x381d04c40c1118140e0b004041d240d4100303001e405002c0000513001001c0c0c04006198000060204890400e218025440742e903c03040414042c24000c0e078844444c4201e0003d44840d885500390280041c8029603c49894505250440e803c04d4800c2c0700701040c0c0c0701c02c0725040c4c3c50002c0f102e04810340034013011500740c03025961040c2c0b1208400208210801030409801441e12003426003049a52001ca0fa40031a04901040000030255548a007451050300c00900b000c0f030700e500340c03070a00c08000d010b5580010051b12a0b1101c002c140743c2c00000103c001c0c107141d0b08548411090074144803010764288141401048107100c144030444c0a03034000103c540803e424030181d0765540800620f0040c81d0031068000c154100d20a0050707041c20703c004a400d18544038140b0305500c1036920000090458100442080810800005070b030b441040705d074507010307040100310070f003807d24080590311103e4540c003058a41c0324940010f46020404010b8500c40301d4441880b0b02c14801d9602880380801280907a150700c00c04031780800c0d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 641685512 1250 641684262 641684269
    0x5092206060f020c0a0e0105010c15020a05040e181b04090501110d150b0a03020d060e07030f150f1e080316050d2c060d0c030b10110d08090a02 63
    0x6100905980d5034042c840396640c81c2c00381c1411008080d4502655000209021582d20a152541115000e18240507070312001e060199441c05044090b03982ca500000e0100c0800f58002d02038019540c199000c0e41090b240d00d50032200c00c0b40c2c01c03e071050164100c5401905901303084040065441006400481c3d80c072595640c0500719984404140c10400c4081001384203024544580b21038011110755026625041103a005851f0250400d03c008041e000034a001c001c00143d0018002040d420140b40d505061100006d400b0f00554040d01c0011450002103111940384001c8000071204180080d814040c14812a103085106401c10700802051802c07001803a0002040100b980030114069130001c081c0300d00c3d09504000e03450010f41c040261100400700300f020108190700f10b400c14140c0314020403079181c000c10f4042c01202c9c0380380112858907100f0030b0300c250107801c0440c4030802200e4010303600501100984201d10180c01032500342d0b0040520291140c0501146c1c1c4c1c01c5468070081303c1210f501603002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 641686762 1250 641685512 641685521
    0x903050c21070603091101030204030b0a0b03071502010b011103040501090902090619020d020f010b2b0b0c04051504030b0601050c0c13020c1621020d0c03050604020a15050922 77
    0x1e90002a560540c200a006c004c2014400d441c800b460203503c3c152440e01c8008110780c0c060031503000c09603580041c400660301040060b0082600b401e00700640080800080c0c02002c2108140d0302044880c1080c0c90010004011101078882c141c44c2c002d8a030b41070100da01d00a4120003903140e00300c0800c111082545172007065841d6001e626500402711000c40540003814081d240341500c1d40c070781c140075545c8100d07500d140c654086440700c2c1c1586c030012030100414201c0500101405000c0f03450030000c1c804014040001003054030010b03203021a60300c0d40000e1b071140600c0b4910010384002031100c049203566104000500000c10324100b2604090340c910001010441c3c806010702440f42e0001e4407401e19403091000031080001002044107207440c0c0398160440d20329403642c40071402d400356841011559100e4184003041d400990904050f40c50b03250142d41c070102910140c1c804c070607800c000100e8101c0c480100d903106d101c540d201801c04c00300c1c2d0188010f01200482c030003481941002d00300040801da115 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 641688012 1250 641686762 641686769
    0x40b1027170d11120903150708090106060e03060a0506031f1506031b032003041202152802070524060d030503010b091215160903050c2107 61
    0x3404021070255507490200610340040c00c1c84107801d03118800300d901146003c140c254880000fa5111010400681002d49194207114000e0411042c03000071580100d03968458800000200115030f01c6942c140d400050a200c2d141e4164425400078a5441c420b4011035040340003c0d0494cc1030034401c50007584d086000580507803c180c1e40c1c0d011414449040d40b204001818030703080401a2040c481d500c024440d00f81e010351014551102c6500c03100d44114144414546030100825403a03081510300190700c850410700700c1005100d440e04c140e980c401c0c0714203a5401101009040c48604a0b000c00000d400044820810041c0342d0900c80c20005c544140b00c41264040292007002e00f0b0082081c01c0c0024900c0504081c2c00b55001c1b21842000a80000840781560345c1c042515440b081c0100008168001c07a51025002d13002d0381c40c540c3c521a1a405d5454000c540d61030903001c40141406003102e200c40c86100c0603001c0c0c2d02083c00500e06083c400c2c14407009420740f10000303d01c10306d074105640c6080c000d9032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 641689262 1250 641688012 641688029
    0x2030607020a02150702030a02040c050c0f1c0f0807030c0c290c0c150a1d060709060c0f080a0306030c08030a02010f0e0c2b06020306030606040b1027 66
    0x11807402c21403901c01c1e5244000ca0140142d14241912034010a40c0c2e000c2e07c1034000d010b60740c0d8041c2006560b024100761200203051000710f40c031400070105d00b2038540702461911120b01e030380280f021480074001c420100680d000d545d500d00c0c0c15070b548001100a440d54004010502500f401d04502060b0000408413103002158200d95190302d801505601c3c480004040c003a02000c144810041d5540100d035460b0800c122122800c1c154aaa5407501300400d000c0f880c00041c450282c4d400a0480408104244544040d8541d091800ea851200341d810b10000600101141c2d810548500060f1580d00603058920862900181070350300ca6641d41e04075181601b01c1813180e440400c4080368540c5c24001d18a81040c4c82c031062001c8210b05800e0f640d03a0001883c203d08c103592050b118106007078050f4984410003506803076100c000c01d89041c4100258001e4840074000e024a600080e2503003014090948898005010701c80c050b0300160080340c2280e110140c030700240c000344000f4401e16001c003d12001400454 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 641690512 1250 641689262 641689273
    0xc061b021501080d20010e010b120d390c08010f0b090105040c0507050a0c0e1807060302250809042405060d0b03100b130e0615030a0203060702 63
    0x603207400242500c01811150710801071002c032002050520310700c022070900100e0b0714120182c83c004002c80300d0010b4055880c20782030561000701500044030041013a0743c0d0400200395255005d845030082ca0b80c010203c5d401e076104065030034003011140e8010b0202c0c80c6c2c40240018120b1035042a1001050070348050524050034861240c0078825000300d0303d041141001181607a6000c9003040505103c1c0a1280ea954503407200713081c2c02030b01100e984076417000a0354041c01240c540b8240c2c001150180380808800007002030766000040d05240d22020450000700310182c41c01404401a6001d1030128001000030303030100c0c85004015041d03100d020320400341152500404030a01c01104c100c110300050410f0f42c500c001d40884160071031076080d550161101917580400d07000c8400603150b64038070590035100c5c000c1d10600e080c1d5640c0c4020032544044038581c019504601c0208251a08110491201d400200c00305000c064580202000c4150190541d00140c0796600024200801144c103100580c105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 641691762 1250 641690512 641690561
    0xf0b040b0703060b130b091804060219031116030e030f070e1b0d090206040b070b0f01090b18041403040e010e160f050313020a0f030201032f03070c06 66
    0x140290780c003410000c440e06040c070f5170b1811000031000503449240c0c070502000804488a4503081c00c64940c0c0032046415002500b06842c1000083d03124040080c5118201c50100401c2c510a0161800454041d4022400c084000304150140000f07030404600740310b9540007246e5a0344080c01020032151200d0041d090161500300301031a0b821009000d0038071320003407172100c4070f070350107072206580b040d0301c80e00c4000031100514400b017103080c86240c000505541011a55008000303441400b580303c0c0460000d40c41007039907159004016100701000e5582c2c00100e00d20250701080c104d80086a00c54051200318030000c038042d10f051300390360094200ca01c0c0550b65100600c07052031036544843d040503500951040d00391869400030060040b594014042000000c0460754501c0403820380312910b80c0040440350600d54035200f03ca41c0441e00e1000324003090601e9030305c094503003115081402d8800185000001400303928400022540010250418418948071400129204d0711030110740c50030052000b9013043c2d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 641693012 1250 641691762 641691767
    0x51206040f0f0212160903200603040f112d01120507080103021903031403070c0204060602030408100509030f03061908160519050f04060b03131704060801060c0f0b040b07 75
    0x40003017030a4a06081c02900e811002d501c50055130440c1d8008490800e1181580d032000308410f07041c83c101d40d00c560040240010301075581c8011407098440d01040b0300b081e1280d018007000203d00c0381c2c049998001d0000f101c0041844003072440b00510145050000c144c8855001007c952040d1141d20009083e0b400503c06c40c203100c1034003001040701850300c1c452540355a90081503d00c0e5044e06110a0101002285c4030078010341b00003600303d40c000c205000300d903140d4600a549030014440e12296120f00075511140c3c40711882041d010b010b030400910700d04981e488030b40800d54030180015421039030381c150b2a55018000d510000181c1005d40141102820000360f40003d050aa000540b00c1c8200c021803024114681002000701e5505a445079100480300300020b00030b003025031010380688000010801000c0100e000e801c3c01500c20b00c41940700031078805101c84540510300400002c0380c01c1d40c0c014082240160803245015202c0e15500700d12001660310b0070340704007080e41c04980383c0c403408050094164 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 641694262 1250 641693012 641693047
    0x30f11120603060408191407060c020607050715020a0e0a0b0324030c040504050c271302090a0b0a0308040303050909150d030c0507090606230406051206040f0f02 71
    0xd02100140f0250402c1e4690041c244140203c5900064488403508841401034011404d850786a99101d078507070f03000342090b10107010b00c1801c1100600840b00081c0c40c6138082d0055400303d43d008800c04e100500382270021030003540f00868413030500034041c041102980c0c0e581b803148060f014a1071415180c2c28001504490a4202e520005403109044001065a100010305c0c04504100310741c08252074481341040d904241410b245c43d41c00c044050b00348408040700718056010004c1424150b421039a40f04032006440700c0b004002541b20f150751011800060450f0071a251f0725000901600e4015682d51f0703201d04a82c000d900480c0451004180c40189140600809074040d142d8a20591000b12440000310340034007540009041c450031080030342c1445010400d00c800703442000020426603440e144040c3c8100941d0034640904242100b140021070322000943d021200c1075140c060403c081e0481d03402080703030000d0107550400c0e69094035129400701d9000b0048411000c010050790380300f800105904c4ca0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 641695512 1250 641694262 641694271
    0x30207090c1e0306081603170301030203060c0c071e15030506060d020703020321091905070b0c16030b0a060f12121b1a090c0f040c030f1112 62
    0x207840c0822011885801c09031403114480344441e102c1440e03070034400550081c100c44c1c000ca20f041c81108410004200e016007a101940d0040900080c20b1320050074110261009000c000e40541042020a5940491070b029004400c410800d0390a00754503040d03142520200b0f141d294042000c180070400401844001301c43c1852040d150a10852826501041c00c0744182c06000801c1c03680014600c1c01e041c800d0080d5003010500303184501d161008451204400601524510014045c440c0401c11705100c00c0241a161a84440030700005442c000440d0103030b4001182d400c005016140d525030440b071110304c5000140d445a00c0805082c10319107400002c442142d0001d40d19040100d000344100885280c10090340f40d0301c07201d48054204100402c41d8411600360307080d142c1c0d81801190f107042140551503c04910814059075502d40d654000290750f800e90840307546d40000c0c02c1138204040707042941245801d01c041d82404030360900e540401008882241041a540d644045042006100f0088146400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 641696762 1250 641695512 641695529
    0xe0d23030a090c060c0c05060d062d1508070f14030906150a0317071406090f011b0e010807020322031203020403051207020a0513020703090f060504051e03010216030207 74
    0x203540e920b9580070501c00b46ca0150900c01c00010850156800035904000c0c0030f0300500304541c1014040c11100010066901c01e626248800860082410400e000e072408550b00c80b99110803003516460705c141c84411019407080c0c1002501c2c2c1e654518030a40100850003004e500005000314030345040d0140c030581082031564802c041881040012030718880c0c29000010340f224802d60740341550300c0c220a1224015000311058080c4104200c600310001c01c50011880c0001c009002030400c000b03070905054102d0071301002040045034403031003d500c40d0780285c0e40141c160049034500328a01c0944544207125a1510500364000c0206000b00213040c0582016006c4038203082d82440d046a41c0e072070b2200319005408040d241e0101e054001c2d50b4a00011000419000d8181d80181070700f00e1381e0340060350150780c1c01c1d13000c20500d900004d440442030300a03500b250350325900e02c0e0806050004200d0505010208802030318003807910004142d40c00e00c0101102080da000304040313035805140c040e04010320b13540326046 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 641698012 1250 641696762 641696777
    0x305071b0312094d030f070f090609290d061a01140708030105120c0d031d0d050c010c0807021f08071b060e010e0703030e130e0d23030a090c06 63
    0x2a031801200364107010120300c4842c8440c1c2d19100c0040703450888001b101804501ca601c800040118a54040b40140d82c04c18209108840e201c06022090700c11a0f0404005411508019004850301c0d042c08004040c0040a000b000c02d01900c821040d01d4065110741851030120440d1300c481e6801100c1e4008807011004500c0c1003003490b456281950105101c0c0b207000b03e5850b031950b8100b040034040392034002c500030000100c448440c1002000a4003502c0080b1101d100e1103600c00039850010340c1801190b40c80701c02841409200001102d069420000403200c00400348010801640c800f180800515915038070300f105000c000300000e0801c00003800440c1400020510f0019101c00102101c045942040000c140b03555032005107030042901d103103008258080c0364004410150300c9601801038143c11075109007004803080d2050200c400c5c400d000441c0750b20007810000150700502140607800d410382500721407844541c1080c0c0341c3c1e620840c0c0032210543c0d01c005010800104110000c0540100c0c0340220 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 641699262 1250 641698012 641698103
    0x9090105010f091a0111030705010507050d060909050604120c051c02011d0a0f030c2012030f030129070b070206010e130f170403060209040501060305071b031209 71
    0x512004d100b00454104a800e000360550100100300307c8109541c0300000308a28540094002c010f074121142c2400300d0750522400060341c40c0580500c0005682000181410b61500d51759070f5000107a44400005000b07928011a0110b40d051010354020461120a84504810880000c6c00c54045500710b40180c00c60149442c80b0a0b800151002e000b9400a050070016140d401c080e51218003207103000781804e030301860740c424440610503a60300038401034a882c03510342c020701d401303070707124010302d80e40141000c800d000400c00070580c00010001c18039a080741c1900280000c2240101c1d602541d802ea56810388002844401d9a0401140307004010004400205040c88490003150b0000048068030454100042c007081c4214115a42c14100618800e566550ba40b0320b0484060340285460901c1140b07044e0002418900030700030148111800d91f250361402e080c0e141c40002c00d00ca0140280e08000c2811003510695000d807084880841c001c969600d104004881160101c5a0070040409102144007240 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 641700512 1250 641699262 641699291
    0xa03090c12080706110d0f0b0f1e0d06061a030f09011811030708010c0f2303061306090213080f0f1e15040b040302070f0518070e09090105010f09 64
    0x40d040b83c0e60151020032510707582000f000c40c41c003c55580c08002440c0021704000451503502c81d008540080c0d91503181141c0210030444190722494000300130801402c3c0705c1b01103142605200044a114200c0052002c0c0c884002c0c416100c0303581800034140b4000410310400824407290182d0140c5190002c0c00520b00b040e801c600b0100400d10b00070150034403440b86400c1a43c0a1200001404a01000300060420540000c04040d401422034020135042086801d480c2c4100d0880e1280d0b811402c0d040389503840d031400303001401403074200700075440d5501c05000c9240394190004221307543c04032082c0c3c01d0b6942000c0a075804c143c1c01d0800c19245601400d00003641d40804100b44640c1d080c07094040b0440b041c50110380307080c0004850b1190000780c10908000410407400400750290780280d0842e00d01ca0b840c1c40e003c0901511034081c0c0703a8403016881c0c40031910700c0704645a03640700c400ba1620340240c032000800720314150350540312000180d442d200144040c981e0051104014131024200b0700c509100fa000c1d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 641701762 1250 641700512 641700517
    0xc1c0210060501090e04020414250206101a0705030f03150405130605100f03050a05010b010c0c0e07050c010f1409030f030414030f030a0204090612080d051b0a03090c1208 75
    0x210001d140175180018150741e0f450b40820b4000020b50000f40a6182c410310710411802400d040c00ea00710028000c1d441130314070006603140304500160200c0545414860101c2c1014001ea61003030208804004c44000181c043c806000210300c05048962a410700340456204459903128560045140104009900360160300300c1000076001540001c66444602c400c0001c170403590848440c821000000100300140040c00041c0381d0300440c02000b000441c0d80044504081c0d801f005010480a80710902c0021107044d2415088181818901d160903440c49211b82560000205182e04503501c4c11a42d80481d0031403041d540c0902c1e500050361070650021612202800040e0029112021307448942c0101c103800c20448855150747c01845440b45131009601001e5070180c0a4203c085007041c070005044080441000b40a5920503009800c10a05680040003408001d107507464540c2219946908956280000d02ca008071503540454168203c1c10071a600081d19441104102494000c06000c902440306 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 641703012 1250 641701762 641701769
    0x1609020703080f07020f2401080307052e0513030206090705031e0f0a2603190e01110a0f080f07020a0318050a1d0f06030606040b060c1c021006050109 66
    0x1100d038081d1104c560480c602905840c1508642c07040506071a103851907440040b405d110840001d000d42da888903442a202e0040140040a0303a01054001801350143c0750801c20458101e616980040c40c0125075100741d860680d03281580030089580710f0281981441007070340c0b004001004010725454180860780e91010b2410030307840c07610030f00d280350101c240511580e06c01c0312212046070020540c90a101e031558001102209907200c6044c6a000307007000144c00d40c0d100e1390240b60b8001805146c2e0940001510010540704029544d80f4400755443c60440d001d400084860b82e10f44140c040704c543c0140001802906d042c5034844803804104282e80d00142180380b080d0b140ca40414507610400302c42c02d003a06e56802440e40b1081001f00421650314030381e20640e2108408036245096240d44001c1e54039894141c8003e80c142d0010000220b95040a8015810500c009013506140004d641000c034141b14a070651066800032000c212800f041d410081c0404040c4280d40070081c080c64500042e205503c02d12 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 641704262 1250 641703012 641703031
    0xb03010e0d0509040f0e06091006051e03010b031e010b01080606040312050f030405030d061e170c040e0607091a04140a090914010f091a1f0305160902070308 69
    0xf03062002a11203404c00020a03c0d03030302c07040c40400d13070b201c080702e440304000c0303840ba4070600c143c072300285150302035001d214201c41c00581a40c00c0c400558501720010074841b03050a070550348850820a064030b003080104113100c541910500803070910781c2e00601350343c5881c1a807810040030400b07001c10703541c40e00704580440768060302202c0c4c806160142a183c131b00070350102d041c025174040100818008084014801c5031851075042200303e881e0038143d0918054040e0541074174181d00828060600d583d8480c0b10100700382c0e803c0f10300c0030400d04005800d4410101c103c40d240c2d0040c0301030040e010303002040e079000390940f00700f40407012924110703034201c501072485480c803003403030030701d400c2140703840307580901c0044d20039281d083c0100001810050440300c2101d6982c00c0b190b28200c10306454180394410000c4196000112120820070b2400c1d0342d81418024010001c900e00034000802c103206030f040500c2c0218860009010000110701e8111060002644a000da850041166400096201e47c9107a448517801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 641705512 1250 641704262 641704267
    0xc122a02060d05060d02150c1002160311070807060c020a050306090d0e010327030e060f04060305220f0c0b0315010c11040c2001140c1c0c08010602010b03010e0d05 72
    0x1500007411754640017001a4101065041620121003954014107100c0a03980c200c980e0480751110f854100d1146031140380202c4c042000d00300000c4e01c2102508555010310007107500c29626050168108546507100340082018904004218181891040c0050004030050500c5240054041d0740326a1081d21020400c030896200e0f00b00d6a00a510a5146007040040c100008007514070102c1c0d00d40380c48c00b0035404110713910380c050164034014044881507910307242d4003800c09241000c1075000d490007500141c1e851003040807440c411403007011084021340c000e12181c0391000980c10000043c0080350422100c030303001002084060422041400240300f020b103030904016000303040001d006400c428a131a17000e4200054003003a191701c038014580d048003c403540032024040c2c1e0002402c80780354941034446400150000313050300c86240e02030b001007401c00c4600e1181c2008000f0920449520114480110348001300501c000341c0e091061600b05078007600200300c592061030302155200280c06001c001c00500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 641706762 1250 641705512 641705521
    0x5030607020d1206090c08071b0203032b0f0209010810030201080105060705010221010f080c100f140a0c06061e27090c050f0102070e160c122a02060d05 67
    0x44e07020400070403102008105010380040002c0441d10207546d0300001a0580c4080781140e50b081d59207241c56640140150f00c0c0000c0c4036203036140001d903141e01e4003644411101c58251280d5034011a059500061001a522152900050300850018000f12132103400250140b0050760000d10050640300e084444549682051a0042c00ba02c51129082e0303407103072b900c586105150010181d0505890602002240080c2c4881100303588a0b6803c81140c0c2c040000c1d64001492400b800707032080c040006281952510305901d4140c8032907804102c002000420410581c023301c0b00b1403045201910101e14400e1100b0045407030403858910307600600f0020507481180002058242600f07100504519506003d0a001403e1190751100340c1e101c2c3d24010100940700c0e250703961010600702c0c01d48a54201c1e000d19038582c016a004052204250182808400c51034140400d0000f100140e0349000da50358440c1e01050f494a0b000320a205054840c1010110440c1c0701c01a41e0399410f44606d003695020024580d501d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 641708012 1250 641706762 641706797
    0xe1b04063015090507030b06090402031003140307050d080403020a030f03021b03031006030b030a03030b0a1703130906050109050d0f06020a020303071119020907030603080a1805030607020d 83
    0x78000d050300c649142000c20301c0802c814845080884415000410440d61801d60540036a0300303410105038042c1c0108a5000030740340642c0a55000031000040540c0d80341c5a80d1181c41c200c10a00c00010a90300104542007084000c00100d02e04001501e415015401d00ba6406035170342d0700c003801c01003d000d1003415880c00c680c0310354140d85030041d64420005880001c032b09426100d6005840c0b05400700f1000c200440c140b402030141040013200900206004100342c0c070104d005201092915a02200c4000f0000e0348022115920010741111790103035a95482000100d01c50340c034507500140b811401c181081215a80204560080340c40c1554a27103000c2c1901d00d052080e0040c0c06000529080c404a240701c42c069000018522810443c1c03503100100d0f00d9030548540e1880140e005040451021606c1801410444200d5401404a040110300d00f62039542d03480c0142c000004113400503c184200c1c0d2040343c0b03004510030040205801810060a21400003500d03481e07213000d100c060004014114007001c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 641709262 1250 641708012 641708087
    0xa151217040f090f0507050301030b070c1203021b212b091a01080a0f0201020a050d0e0f150a0503100b1305091617071106010e1b0406 59
    0x50201181c1c0c1e03161601a00d603400070460050044982c81c082c2d0310f644036002e80c0f0400e8041c04139501d840341503030b00e1a0345003030752804000c1c402c1041040b407000d050009104d05600a010401c01e031405a12981e42c02c6900f80181c406425101855005610b0701e11400541505880c44110b180150b9030b941c0c4003018521180b4039030800c1c580c50402e07200e10446c080d0150f507000902241c811070300c0d00320555503280c4082d1442c0d021700413420143c02c44540382c00061041035912407591f00c180141c41c000162500d17100d08150304d58195802050300250602c002d480c2c000c40a0781c0c0d05400f200da0b000f841d021078240703030303000d0103060b48400512400102156003400c03c814490028481800165078486482000001e03c0c03c031072107290b0040342e0b0070021035404480c0c03200c0104600e00c2540c45040400306103501d000c000001400d142e090100b241c024060b040e40500460f4080c04500c0c0d10702013542025826940304003c0c1409041d14414180418444240c4c80595041c10706003003c00c0081d68408180c013404c40b00b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 641710512 1250 641709262 641709293
    0x6131b0e0a051b031320090a02130b0a0f0507060b19031101050a02061b040503030c0c1003021602010f09090f050115091d040303021b0a020f040213030615090e0f060a1512 75
    0x80310010070031003c2c04458005060701d070046001001d000d5510100c048242c082c400b080404140051a800100d620030ec2c00382581f140540400310304003100d6404600901c0384511500c2c2e038a000c0c00030500c01e001d00030315100b02d0214286095860009009002515800c01030064040b1840303417505c0c1050345800c84241c0d800b61000038240d84ea1100d2480440d030769841002c1695005000781c80d01903030024080d10035660100a58600b80c1070f6901c407580110b0360104075820031818003584003004226600e00d4031629018803810b150002e42d6504084000003505c0b8000184410020344c024140140241158039103100c0c5d040340c020010355156480c059010740240100c12303000403400e020814a92000003406200c4900030744031075010076032010511007a032180881004144500403402c01c00500103522034083c0004408103041901d0312208400162407803a00c83c90310661140c5039410605005204040c0c002d0f404441c100020358280d0000f40b000c0c00f6030b200e088010301c0d8001520052018070040c16580 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 641711762 1250 641710512 641710519
    0xc0f0c080705100e03220605222303101112090a05031204020f040504030e0d15020a05121005030a0206030a0209030706050d0e06131b0e0a051b031320 66
    0x1300d084003070086503070360012000014070031041101189645a01e030700702002c1d207100e03644252416840d000300d52402140903004450382c0804420004040310540f6600081744100c5d00d0800705c40840c00304040c0307020101024420a01d161814100018200000b00d501e4481001394500e220b945082c102828600050f074003170454040080d0040c9440010000e10384201d00c21070b0703405034010810052004651003101c0040c003280c000d061080c01481c2803620b865602d48201d1401010f05545100f41c0d059801003e100004030f40040351800340314111140d41d80e0300c280c06c40240760300c5500c0c0c80700281c1e032184107400c041c0c00b8620000114850f18100d0b0100c90010401504039501140c0e140700080c9254040b982c1c4022803868096800b090402c0412140c0c000e41d1200801103805505890313090b100000c0c840d207841014026000024628461480244600303010800001c080c9440380d03094032940102d21242c81040e20800810130746920040c2e9240038981c0000c1c1c10301408500d050700321200705e421441c00340d2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 641713012 1250 641711762 641711771
    0x705120405010b01110d172805070801050105210406020403060507090e061c08090105040f1212091508060415141c081e1614010c0f0c08070510 63
    0x74028150800041858280c0c3c507007650310f00c0f82405641714a00c07909103000040c406184101c04040c4008482e800581840014020501c4c54540c2c0308003551404001c04119250000c110070650803510391401890700303082c050310b01141078a03500a83c001c1040c0540a0800417008542402002d60640b4065030303100d84100141e0400c80350140c1084000d11514002c800d101c80081c605041030142d904030501d9007008076501c10510b81d034058154024803e43c0d81003001c20b20000a541d20300301d032100000c00c90304000c1d0040403c113040c040c0c4043c5030700302c030a018814119010401620440d035660740a611501d024001c54a40e00005005014200311850200492540201e00402d01982c201c0070940112262031070103080c05041c3c400c1102c55080030700f03100410f200c5142d460000450b1aa0301c500d00131040c0b441c04560040d0700400c0401c0c0c2d03609a9450301c488450000c452002d112700010100741d410100d40c0d00c078540f44010045140c2d484020300c03015000c50301ca400c1060420a0640c0122584820700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 641714262 1250 641713012 641713021
    0x6040b120106050c07030f0f06090b01060f030218042003090d0e040b1c0309054501060c02040603080f191b020d02030c150414010201051e070512 64
    0x1802500315111503450300380503100000740140030f80c007100c1030382160b40c01a004407459503c4040e854043c08006860b00340e040c0d00808001802881868503a40c401c01d000b44081d4141031006000804040010090610410118441c180d188507400c280702000c40d00450a4003085010f80c206804040400d6100400030040c840703040004242440713000055511b007100c0321030355010041540c940740840d0707800090900d1411032141c40b20600702144da0107030501451250752600828a540002910704800c400d68004d820400810350039605542d20421030501c40302c0e0240084005c0c8140103114141c18030003144143c0045403100d07000607000707642001c0c8080c2c41d014030091404c045da114540d82072040400c030703001042d4907009500b40b0000a40c1d141d100100a503856090100c4814000d00580c2d0510604211010b19912490790350004a50009565110fa180041c00b00303841102c0401281035904000c100a0f103c0c48285041132602d03582e20304c039034054541134001c1d261403140301000e094801d47d82d000c10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 641715512 1250 641714262 641714279
    0x10606030509010f060b0d021b060a0218010305100501110a0803160320030103080904110c0c091005030a1203060b0d0b0f0907050d0e120c0f01060f08030301180b0604 73
    0xd02c82d1190b04024442000d900003600c00300c3d1107a0164820440044c03204201551041c0d020303004008007410304680c40c2020000071071502c06c003251162011500042d0010700c808280c80001b01c003090a080a001604100f140b00003d820b240c0203590402011070340c3d05804401c10404030003003170b400c0038041d6664101018102d440300110002c040203e4203080b10302c040020180003426000362000d210a06607400c5035a810101d03031211002d181d12544070b445c088030000414004040000c0684003c0840e9100201800340040780140080c0f00002490820400d988001c03441c1c200f15507202d03609000d805208041900200300c2c0360801d020303000000c19030301d10700c804a901411300c2a40c00c99008103803d1514080108150040700c0d10b400184060191209030300c040d401c2400040041c800761075440000341e0700a5165004203100101035448a51070111054003881072401030041744e01d41d642c1d0300381001999666840184220751307048462038816144040d03640d2240384c500d140180441e40d00d651f500401d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 641716762 1250 641715512 641715521
    0x80a110a0908190c061b06020406030b010e0301060810050903160506010f080615100309020402031f08010203041a15060706051e01050a0506070302030f130f0b0306060904110c01060603 81
    0xb00080341c414041e0b00c0105036502000c02c9040c0d42e000c00e0b284010343c24007901300c400c040c011352084030001d8451401d500103141e070b001034009070965641c0011036001d8440010400b0303030060142d600992501c0c10500c4401e038042401410a1940980802c0725101d03000402d00d58811309a19400c1c80004100c440c08000020417154100c80303150190542c429121003a0b6078a9080913220080001d0803801a104d01d428020f00300c04110419003800141c03150260046820390f8000c40d050700c41d491011200c203409891504240e006405400300840c1540360a641750340d0401f100d102d40740402d040f0100014420408000034941841015140c5501d03140e445c0350803005000281caa00b940d105200914a20407040e22810904840c070007000045210300e03100512496a100600c19002c42c00200b2581c140f507810079004107801c01c10b24448102d414906002903061140380e8104e009100350800500c000c030b1fa039020030380e00c0707007413040b00c00140c1d10401e00079031461171080180b850340d175509101d0001101a050b034031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 641718012 1250 641716762 641716769
    0x1e020f0309100513020907030e0f030c0124261f06060c122001150501090803031308212a0403050a15022506180210080a110a09 56
    0x101c518000158025005541040304e80703200d50030141d01c03024054541480304581140c030a08000a4803240381036141d04203010415403c0c490f610001d41c02c0c1d06030009104812910441508000d01d030740c007070016440b402116120380c7d0945414019a4211282003400300f42c032400a99084070398070b0784600c034003062040a0f400304070300161412000058030740c05220f644440642c494540602c0c0c010740390301601d24800009403040781240b11540b05092000920236030341c882180c1201c040031140750000040c6400b20b030707411051181c0c0042c03040c01520f05d6941d4280d0364a41c0d0049580e5103e42c5d44224089404860803441c001044c2140144122900b480300308260b04180d100000d070403c0f5091040d60441c1c801c520004100780e02c00031100d0701203803103140003a00c240340c154809803604070b050b5a258004481e0001542d816001e401c1004200a80d5108802e00340050a03944144c66456800149581030b04d0f880d214140920880055540c810650249035102d042c15201900c4020480b0000c085954500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 641719262 1250 641718012 641718031
    0x110d0c080a0b01080415060801061206060605040605030c090f0d03120b0901080d0e191e062f071802070c1703030112030e04050c090906040b010504091e020f03 70
    0x201180c000562030040c0481c100042c1c55800785174885540340305800081d034001d40040d640c0c408010a0b081d1b028094980140030011410840d4042ca003402030848002303900c14428410200010010b8541100035658481d102c41141900c410100c800319425030104054030342d0241601d4005010940c001c150190b81c8030720708000300800d1060000f801603002e003e0040350080d501c000544091030b0300ca09200d645a00001d043c8030f0f07601c00140c1200050380000c3c0c021103041e03111032940c0c006000c1e405200100400315442c04000c078040d60308400310b030f241c10a0344903140c01140f2004000404c2c0d040045000a15900c501500741034000c0e00840c009410988084030100042040054100c508002c0225100417a0b0055440c45c3d18019860f0003c10844008405000090b40550720541d43c604c10544a4415024001ea035840d8103801c0110300840207003580d1065103040740b40c0a403664000d00b6541036465103400010031000041842d100010f2041c200d6800ca800041e0300d00d6585900d201950043d203944 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 641720512 1250 641719262 641719277
    0x2131b050c0123131a0901140907030c0e0a0e0708071a1c051b07030e0f06030403090b0f131206050105060315060304060b030303180d051809040204110d0c 68
    0xd000c1c01507800e02c09120100310f034800c000400d900d80d4035400034a1000d032140710340351182a010711003161161821103d44010b80d5507500360041440e42402d0040d40040f011015104242c290359a0195510040c0039840c0075000300c400190405025a00141445122004441301156582106581c4e82000d000e089482e06904d07110039580152242900d501103c40c1d62514584036a131103400c40281301c000c00c100d01f070925100f043d54100700d400b4002c09500740240e883c41d0606182c80148900c0010060010340149410820000030a0380300f060601600c0080408a40d038901802c03189050b40188080c2568038010003400091002007202e40280b80351042c1070a11440c5c0c1d0714410001e0500089441d00542e403100c1e10b60110310325100f002942c0c040d1080000003940c4c10b0000100340b454104603144130a00121420000e05420100070240c242ca88620b001450b0a00b6641c02103421940746003024051a0440b011908641d20390300110500044101905e803030b42508881000038003a9407400348007080c4503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 641721762 1250 641720512 641720531
    0x10e06061e0102030f0d09020907080a05100303050a08100f230405041a130f1209090c09260609030a0e0402040501050901081003051902012a02131b050c01 68
    0x1c000c090295005802a41c01d10901c1c07425148980e1101c956108541d503a811403000699803507a00c18080c54190707035148800c1c50201583e81c01c9500190a032090342400f003008000003070b4032004965010b0a03501d04200c050326003902c2500d01c03c9072904001e14402030f01c9008034ac001400c400783d0311000851502035169500300014002141d0007a40e001d0b00c81ca000f030003440030440c0c0c000070b0190401050551303a11070a4598403001c40c4414013030700441d041d41e0405c1203140010342c408050320142105000810840c200882c010b04051030034402d10140e002f510880010320b0840c1802e6080c1500e560065610500d0074009068a80e80030b107144da00800e4545100d408141068805d503016200c0c182c4580d80b0f001c080030019101d907980180100e604490f201b0780800080e00c184094891059040c040c0844840a840054412460203603c0c400c00f240c0c20f0445100762104100d141e98683c0c043e1220080e548031810508090140b44590407000d00c81307055410a180d500c0b100a16150980e00e0081100070076 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 641723012 1250 641721762 641721799
    0x1f050901020c0a0f030807031202040f05090a050106120b0429100503070f0806030307021206010501020c0f030a081e0c06041707120e010504030b0a0b0a120c1e0305010e0606 76
    0x103d80141c1c541a038840100348002100d0000a003140c0e8000c1c01c1888214454000342000e0b81d00030341040c082180ea903141000f07103040c80410150003012601c000e2000f503040001c02042d40080c42044042d690b250024007515469941c820919400403c17010205501e0b4500100160400495000d00a044510108003018440d07010b03a40580c40a98400c00b02c104007071070481b5107030006064640e25000410000d401650b8503d40491400008000741415603d406c00280c00d250f41c903410b15001c2e8100100b032906640e0701003200007031340b6030240d5100c1e240c2e91300d8049074007042004004100880c0d8002940c40c0c8441d0700203246032046118074040c00c0b07503003450800411a0b001c0d103800107245031541012815428010340400c2c400a2042c03420b030b8102a0b40c0c1d203600f02d05500a030380034084250345813031070440da0800301e101c0c0c03002c0c020160740b803170010100f40d0f076544110405101c1d00c1c2c1c40c03a14005001402c0315003212410010b58116000380300000e007081c4401d85404d800d49020388500b9484031032061590 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 641724262 1250 641723012 641723029
    0xa0b0f0a1d0601080c03070c03110d08010e06031f0507020106210b060114070b04080d020a030e070b0408060c07030905120c10260a1b09090606030b0a060302091f050901020c 76
    0x711750141c0c159112100140c95a00c680c2200311705015200340b00c010a01403c01c0150800d0b0207580e00d01515501d4504000900c03070010300124000c0e0026417502c0000144241c451181801c7c0700300000c0e00b9a25004200d00402e0b158210041080d020500d00d24041405081481c5d408c0c090359968165840320001550610038411038105100320600940c0080380b28642482c0d409405030408901c4c0049038140391049030f214000003004645e07500740448450b82d08003c031030007500041610b01c0c038040c200340c205940d80e0f800400c400d0b045400000c00d5400c151241044900418010342030f421b141c111010032503241c0c40c41e1004140a20b400e0000701e12040d106412001e00c890385d203914241502c0d025007001d030110301c0062805c9069600c0c0d007034904c44103102c0700c0c0f02503d5551743d69034042c1c49400e00c8640741c10703035846601c082c2c04c140c14400308108907907130715080c8001c990f00c5013001aa11a01d104c041000c15503214087d03016105801c58114585402c00d0083c0a481c400f42c0c240c918240d944400c006204 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 641725512 1250 641724262 641724271
    0x16050a03020c01091d063006010e010b070813090606030209010f0309021c0302190b061908070509220501020301171204121b0b04060909140a0b0f0a1d060108 69
    0x303142e8030711401d0f002010541042d04141e000d40404600106501147c0200da1400c081c1c1c0c42050342c0803810000c104041c044580904140d01d82400e4552601c09104624000e0003006094081c0004200d40c0c0002d800407040024055920701380a101e40d10f550140003504442126404144004d4040b004c0d98400d01c1041e00c03c0e43d00070075903066481c183c120800c3c030302400d071401c40551041050303000090360864040c00409116035142c402618181c5d05000c6142c0c0004001441d0311811007040c880481e004c103000d416a101070b1101c0d68103545003032030300070fa41101c0c0510f581805600b0240406116040d001103040e240000c0310300184001c40b00e0559981c440013200400245420306c0f050000c8602350100e07032021400fa090401c1045010b82020722025107650000f50142d1000408212594108070304c1e000500c240401000303d110b9603200c00c1e070303203110003403582c00304e19503034800445582e50341c070360b00308a0603009030a0030456074a50a81c1c02500c1c0c401c280103908075481c040025290362141d14210310a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 641726618 1106 641725512 641725529
    0xd0203040606030627030309020609060d0c030b060a0504090b060c0d050a0e04020a020c010e01050c010f0203040215090d08090d021509090a1b050c0316050a03020c0109 74
    0x1107803a0000b170b4025112500c105440090261021280c3d62501402c0214041146200160441c496216143d0380f00101248440062000d680100380d1307807100b924200081c24000c000c211050048222101c00108100400d00650785075800100030000050121418000c200e031080782021610030440300040c102051001c1460f41c481410074141701d0542c2c00f1407402c81c02440080d1076444d404c2c182810b0011114001100364402c00498502d03403109170003000344071500003004010b13510599080e40b26110342a400c3c074880c82c1142c1100c641d075600414410001c3d9103945e641400360007082c0b03000d910004070b260300800b5803039900d0050141c45040d840c0903640c00000040051051014100c0d00d5414076040c13902000c80145e81a0030b030440141e0130200d0312403c0510001c0c0c61072003180c0114038042e03c0b201181c010403100240c2d88016a1103034003a1909003511100450b100b640764468602d2 = true := by decide +kernel

theorem cover : BRFrame.Cov 641546762 641726618 := by
  have h0 := BRFrame.cov_init 641546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 641546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 641546762 ≤ n) (h2 : n < 641726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
