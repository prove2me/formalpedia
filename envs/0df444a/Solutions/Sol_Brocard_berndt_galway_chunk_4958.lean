-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4958
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:17:11.119987+00:00
-- url     : https://prove2.me/submissions/39701ed1-be0b-4567-b276-7df4371b5244

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 891546762 ≤ n < 891726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 891548012 1250 891546762 891546767
    0x40b0433020c0d06240f0b070b0f0405120d0207021018060806031c050711010c0206040b0304060b13090219060905120a1e0209090a0209070309031205090c1f 69
    0x1a90202e0a00401c00d0224010a0090036404808500800c1c114200d075031001020340010b100d818050b03903440001000700856510314600a44503520740c00000801c1d55142c03106030304083d910040c0122254880d0030030f0354a450300da010142c00c920281a0001d40c85074241d02c100981c000074a0003410802c180d03800740701c0f43c10810b0f48100081780c0003400d280c0017070707100c4074086401c081e00c0b51076040c800300090006040180d03010005150040c00703041310041031100390004480d100c03192800650301c00350500003070014410340c2000390340081c81044002404103480e0003044d4000c40c2e0040e440d4004d96503200143c25401d1510f142d58800c0010680795030001d0610802400400342070250901482d501c000c0003d00b010700304540102180c102140d046120041d0150912040304160200d0003404600d010820105001070090811075008210052980e94010202c0007040b81403410f8040080048100c4001103040c4101e0b80a8281080a0582d00907213800303221395515170020758489651824101440320784d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 891549262 1250 891548012 891548023
    0x9150b060a1b05030c1c14070b09010207060e03040801180515070216080106051201200d090819110325080c031303060b0a0b04140303040b043302 64
    0x48041c2041a400394240720007a0500c001c9560040144c400000c0d0038210328000107800d046010480c101080c02242100100c030131010041003032000041c180803410010700340368045a4001e58220005080020580780d1400781c650051b25010250000501404241428001ea06802c0d28110929202c02c5080d501d4555403c6080300345100302501201164001e4800d0000f800990b41001c0755007030490322060352070300034240c2d48103040c4985494000c403041050180580e03800442d6000720440b8070803169502510319030200744110070365517941c0100c00024401901410b45220a024110f03040c644018014040000c0a5881c80490f40140448541d103860509140e0701205204a1415280c00500c0d0103c807900030011080d555000200700500e05400030000813084038052041400003203464020300030211180d02170002e10000c10070092000c02c580c080d15800301c0c903002d4103d070b1078243c1e121240703040c3d0780103a0052520001d0b40c0f1900c510041441040c600c9214000b021401d00001401000c0c6d61503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 891550512 1250 891549262 891549277
    0x9060316090c0c0210021506010c05061503011b02010501050a062f1203130203072909060702030105010e0a0e01060f0e0403030b1203121608040f0501020405030a0609150b06 76
    0x10348402020b41001d200f41d0b034040400d0f9000d054510f02c050102c0010b502d5501400340d03460049610700c0013816542c840e2240060983d001030152070f40d511050044541c18504010322070700b66480e0302c20380002c04000d4038490500880c1d81c0c00014154103000401003801c80d268040030803c9051280d6654410012a01001640c2c03007980001c600c1846d00710550030800c40040410310740001100b04011b41d04044450b040345031007201a20501500c0384920fa034407030864044004d034002c0c100c40341403a070030b8140010020313074600030b142500300121580000d0945070240c00840c1c051700c040061150b02c024034068040e1034040c003002440740e2030400da1141041141e91042c11008101c58004c1024940a41d000c40100301c00548040c9800404120341c558030340c01040d1402544902e40c00144107181c10721a82807015007242d9855410b51101c1d1940c2c0018040d0420503102550b00f0040045c1c60390301000a810417611a40c00800c401c43d89003070480f114030400014903081801c02000c503a20369035100444081 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 891551762 1250 891550512 891550529
    0x3050c0105071e0602070203012405150c0106060f080c07200609041a0f18130507080f071401030b0906091b03010b1b07080705210d090509060316 64
    0xc841090034540e04400f80018501076109418881000380061a0003c007400707402940240079841d040d4171361000f0552500b41240250020b0344051001e8030308000880411564086414185804259107a08494042d807019003c11032300001702c41800e03082100360b90b021020b003902a050034082d8032141c00204031051800080c00340300c6200740042c1d81c0d8000b91101c01d14003410400c030a4410380d02c401d038000800c2c0c00f418400c00c204880307003886140214440c200b0380745a056010268840c24240d5030384915048084030b050190100115043c0020052607080c0000c07a0b004000702480d000a40740b60b11800016035042500300000280b8584403c0179040d00510b041d80c20740e800b0f0f42c44650305200510545800c043c07010001000040c8032880c1d80181c0300c03c05199103200c1e229804c0300d840640d40c0700d51348a0700650b1780002004100e50b02c1c000c0c018400e64202c020080184202d002d803268142500c184008021504401c0207001505017100c0743c80e48100290300504105600594041c80040c0c0e80c810141c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 891553012 1250 891551762 891551767
    0x510020a1a06030607140a080703091b14150f090102010b03030d05150405251e03020d06050316090203040c090608211e390d140a0f0c08160501050a0603050c0105 71
    0x3c034207108bc0e200100c1c164001241901c0c00d01c1414201403001390510030600a210691500c0e0300c9460001d401540c48a0320748412441d2a80701010310700560000c0310720300d0542d5600c0024240d261030520040000b0f404a05000482d40762002aa00314480c1e403003019802946044200081361915054014409035010036543c55031304a624225226000bd0720104803003910003d1a260540d0107030090b1402025041090050b280c5075800e2659446001a040c007410342e00d00c00820483c1069401550010700600d4460440d40c2c40d0381c003010036900341d40e00401d40c55001c802140c80605158003130030b03000e1284808141c17a1414040600b4108840d844003083e001600158410704005450701810801c07000c2c4c0c10034852010050705510324000360180c4642680909959400d01d64485c40744403d202075007004140c1040301a0804441134003800c911075080c002030380504808100c0b030348064911843c5100c5800f41c101c00b2450201d0a41e9406800825502c2c1848820b000081c0d0105403010340c1c000a20305a0b4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 891554262 1250 891553012 891553021
    0x306011b08041e120305070318030506040f11011e0e0a0e0109051801020a050324040f051503060f0109020a05160c060e09060a0510020a1a06030607140a08 68
    0x25504034052100030000301c00018000340c4410000080e06084140b00040760b04540c0d201e280034144070f89038000400050701007005600203805413024001440400e1425414191130742c0d25075240030416141034071840720300e81001080000082e54102ca4031000e20340300b855204a18030160f0003070080ba01c02c1040c005c00101e40710464a5208940c030082c40244144401540d442a03444024182030701d501800300c1241003020702680c0b050089a04003400c13613450501d10b42c1c6420300b1003c0d02c1e4542209016155200c200c041659582c1e02644490218412000403542462040e11910040c120056030198104000b000441d17059015001d044880c442e00c00740c2d58803408142103903284505518043c2842c031a10600084c40404900c481c142c844589416800800c058104951034900700c5046520070702080c0288550b040000020a0002884c0100c03003058405540e11040014108080011801c070241044a14501009070700c0e0812030138103201b01c00300741c0306c00d200949110320303e006400e0060400118 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 891555512 1250 891554262 891554297
    0x120c0306030118060c020d0504060e04020a090b030a0b120d0c0b0604090b070e01020106270b01020c060f03040b06240a02160305030304060c0801050303091e0402030c03160c08030601 80
    0x20000608000701c0855020002e01d0030f030004017a42801d480041c4034855091044500130412074007070b61440e4544030000803820302084003a42c000031007c0e0400844200c001851440e0102450158400840101d841080481400903800c2c9509042000d0340c044401100103c0e044061042a5500103890f80c080b5500c900205001c0c01b20302e040144518040d204020a4030781c4540c02e8010704000764001e00c415a038440c0340e030810142e12004070180c4500320030300f17074001c440075440514007800c1030041c1d4104030900b00c00106e8a40040c010300c501c00900008200c03c00141c8240b25a000d00c04407243d00c081019040200740c3c16280c42c0618101d45000161001d04600820080c40b446d42e101512240c006d8481c076056440c2e410a0310100c407014208010001001e0003480100e060302c5004c1e00550516000104104002941c034281c041c0c120712500e441c3d13040b91110b0000710b20554140d07a4a954a0030641a52a018150100001c0c101302e4041c184d1000030b0346110481e500490241b030900d480290307400c0744 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 891556762 1250 891555512 891555521
    0xc0c0a0b1c02070807080406020c04051605090301150f091805061816060f080f37020f12011a0405060d0f0e161d0705030c0c070e01031205120c03060301 67
    0x240030300c4d002040340c00c1041400c2c001041038441590a0704d030000c11484c2800141c2e00b05581c03400e1504840700303005052a10070005048005401000410b83d1a01f0030740a13039001c4204d0b00306a090f030051000a1005540c04d00a40c1d56064000719007040c1c0c080c42d82c48450710781d040604104050081340090110b9100100a01400780b4250490300c01d075181d45013030103000d2000c00083c0720040341c01c42d0002242d80c04c800e01d005100ea06e41081001045c506803407441045d030340e2002c0c034420082900311510b072540894030150410404503500e0070382e510185d1031540c4090300140e2000020034107840b500001c120801c81501d00704c030340c01e0300e825490341000700d40c41018246072142c10f40b12520300003101c0902a0002480340b0014800400400001d466180c5000742211002c1c0600e455035044001c1010396224400650740102500c000504001c910800d00d030825041d640300261500c140001442804201c0381000c03140340d00d5040141c0781c0410300149009201c0c00416070510b0b40800710000b240703500e0a410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 891558012 1250 891556762 891556777
    0xb010b03190c090302280513060306061518120219080124050f0d1101020a050303010303050a030c08090a12020738030606040909080d0509030c0c0a0b1c02 68
    0x3020b000760311040400a0240980d0700c0706a10640004100182c03c00070754a49903101c038018048080c0850800081c40042a1030146424907940e69070000800b240040c41184040c22240c0071050b030032040e0820003004a080100d0a04102140220400c04108201e184448160341511720b00c00e000a0309000404000e16503024000b55400e140340d0482040ac589590440c03118007003101158a915401400b114009100c0e0741a040040c2d00e04c0b68011030303509411101c5020f0144100c03500c0840903641c071030039a0020782c07084000c9000424a601601c0e00f500030543c2c0116546890030451800150742c1d90380b1440030402401401c0e4111b4001d4090384280020400360281d40c0002420f000b54280d61511071102e000850030101d416402d410025102d00c048034011340c002482d65061030b00700b000c202d00030031214008842144003005110041041c500407588110000009507441e048c00e9201c0c64107048040005500ca500b60742e00600600c0f5642003610050050741c008030b403041c0d02c0540280024402e061 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 891559262 1250 891558012 891558061
    0x708090325140105090d14072f03060c040e04230c090c070b18010e10020705010b0a0f06030b0109082e2a0e040515010e0901030b010b03 60
    0x200c400c0460a8100024840e50388254803070030005002c0c4007014203c400c1510240181c0d0400ea0350252110f1107202110000918894000c2c98210180d94040f011209c1c541c140c00220a0003100c14580c0c82c48045503051008194042c1103d4504012404d0a610450141300c1010340c1e084045428084103003200c0314802c1008814032071000d100d02515640c0c01d4501c2c101403180000c0b03400160005000c1c1c00b42c41e1780984c8503881020700d888805001c130a0303050130b419100640d0350380d04c903051000104201040f40017070301030780c0144e5580803410010b00392492504c0990190105503010000c000402440004a509920707000940b401820012640c207171641d400b140e13041c402c0f80e10307044c034000c0c24800720414070398900030000c21020b04043e1a01070b5040800300000c155070f40342c11090007400c0001d888203240058070342000381a401000003021660259400c201c00b008070605c050407943c2105d55081075040480309417019615680d25001806414001c110030b01c800413020030325003050a14603001d500f0410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 891560512 1250 891559262 891559297
    0x20708160804050406080708190f0f03120f020304050c0609040b06030115031826091306031412030105040b0d0b090105060a05014b0c1109070807080903 67
    0x50526000750341043c0509880749191800014000c00009402e1084070141c002401015101802d55400411021803d070748800031903030328400082c0481140e40c05c41740b003a20ba07081040d000005440842d0951240500410702c108240004541c0003c0c40a17800305c01240c0301d03a84d0b040a0b90114000e004a04506900308401200103e800001c00c0d00010702d803803280d54101b0891107650802c00000c0110500a81780c8007090f03194580803105c8a4400401c2150b1707000b014944006400400d000b046100c02161100d552524280201b00e1186241000d00c00aa402844400020322505000d440107110b0f00d84519507a01000c41c0c907803610503d0754101038100503c80c100b85030290303d0728080c0801b121058440c89802c000805c0c503602070b40740f8010404862440d60a5540303010100b0950a504503c8000d60420011800d00303149015074041800489a5030380c0c610200c01440d1110414800c0c2220520503180102040322103640184583d42c0010245012441c946940c00740508600c14201c80f0b0030745d0f0180 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 891561762 1250 891560512 891560557
    0x60306030521040504092f0105070303091b090218010e0f040e0111070c03051c050d02030601090302031b0f0607240f140106081b04050d0201020141060a030204020708 73
    0xc40d0801f000c02c02031266424091a0401c0e46480001401c0f1025011400501213400864480d6104003c124803a241c107041e001031904c20502d004095500907a08980c000820413500c10000180c004410b01c203082000011040d00c0000d403245c00e0720f1040d1401160b9a40340c43d40e60000940200b03c00d504803158041d540c1c03000c0d0401421241a50200303940500c40d030b5030300750007100f22a02c1460101d50260b54440c00c004a82d16048040d40c005803460b8100701002901101503a424030001601100c0c0c401d908425a821400b448130744041c00180601c00c50003403189401007852207515a011101140480a52079482c4c00440003c01d06518922502803030209405600b03682641014144c0728140c5404459039138151000d1003402a400c1280050501480100401c0c01d000e000c0d0041e0a1050001050700201c0074109500b241c081d11100900284007046421403043c04042c080d2180f01c00d4441138a645001404280c002d110f0b444000d010303950001d43c0340d00b07000c820710070707920100307440340c85d0000a40b50b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 891563012 1250 891561762 891561773
    0x20f1b0d1b06200d050703030513020910090c1409090c070f1109090615040b03031c05060406080a050c0105250303060509130b010b0a090b0c070f06030603052104050409 74
    0x26021030f810400150038555001c1c00001030982c41034090b82d5140c0d460513826a400b14045e002c081c2201a800038600f5a42c1c0c0140e032201400382c07107541c1008903104003a1801c2141010f80e256413000c90140410001078044520910048540c00401540d0300784541c0c031028101c586510a008c4c2c040d01800c40711200c0402c2101034800d00d904200c04031613180c0d19844001c042c5071240c0c000e1302ca60342c9500c88180b411015003443c1d00300c11010742c4002c0540f4242200c011509a5000400314010000350391003081041e01c0c50617200b160058a4490300034589a05030b50b4465a8514071507088505000340412003048001107680107186120840c07000d00c02c02c150610f009806420140600c034428034011000940342d40301150b4980266801500510840e40780c0801030f1f4640e4807a240d800101704002c00042500f81e1810020f0200001190007000e178a8034002800c0e42181e0305800c110209410060100041400024544803000d03605128032600390303080d42c0c080c50034410365000c1034001d07081c202d040d030605ca03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 891564262 1250 891563012 891563027
    0x11030f070207150203070b010e0606090415090c020a0c0602030307081b090a03080a0f0e0d06050402040e0601240504151d10050706060b0a0938070201020f1b0d1b06 72
    0x43c8500c5002e85039903203900c0005400c927422500315400141c2440005510318103a045000000241d403050f50300a529100c00000390341c0c00c103003400056440401410200711b0034121120042c411403000d1419400d010f1401401100003502010441509200310300549600c0011607586400090490a141d03030b5074541004030350403100c400b0000c245041d042d5000940103030002d01e082c520082c07001d81d00c07030943c0d035503a0000c0001510036a005561464489010070040101c103001c0e1000b00c0090441c00381221a0a602c8034100c446001000810b02041120118106034962181c2c0141070500300310b4240440d0394000c2001035203041c1d01c03502e035100c070004294001d40101800c5000d12000c0c042240c5460840900780306001c0b2400008160480402c080c49440d400c2d0300000c00c900d0440c01d0340407141c0f107603180403002150145000c403d001031070000319070701006a13112040e0080094910a003c00c4c0b4407054120070407039640e00850b0034008030740800244e82034541706500c003000c480c82c01503100d0384003d0581c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 891565512 1250 891564262 891564277
    0xf0c201509010c0f060e03310305070528090204150513030308061f050409110f18150f180f0a0b0c100f0f0b060301080d0c080d0f0f060911030f070207150203 69
    0x82da04c0c2c0c003030f0784420480c90240d100b2740350004000c20f441850030043c005101902c804110112400900080e01412480c520000410f40500056142c9050021310008141030200321014001c0c1048241d41d511040c4121904603a014103020316250703a800f0200d1401505402042c0042e550401d0300b81c003194000c0007420a0f200c0c0741c03004020b0f046201d500000070b4400d07140c05101e981070a00800501c0b00441d5030b0308601d110040e250701c0000088030b14400c0245c21040100c1c1d54a540420700c0c0b8144072030042501203840d02240e108254001c182c0214252008a0082281c80c84c0c0c00078040d80754070410000c101c100300700094204404110203c000004101c5007502440311418100d09030294500101500e05030b45005000e8400c102c4034540a035078040c2c1c540011500c5a02c04e000b2901d01c04802d02c141b4102c0400070034081803051071400c00b103007160059007048458074501880f0403615100001905e92140c0141c485500036100e0b0b03802a454042d459100c1045e130914600940c0b2583e6020025001c80d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 891566762 1250 891565512 891565567
    0x5042105040503060f090f03040f03020102010b01030204050d0b06121608060a1e05090a020405040b0a2403080d0e0708160819030f0c201509010c0f060e03 68
    0x51195814003200c1070700c81d80c03040680c141d0000d00800c2208001000da0303a00141481d044842031103003460134078115045603022855a580c590f02c2002503580a0145040a403000d2908515050030000002d00c1c204003040c0151484007018002455078981c0f00703045840346000b604a03076400d0007090355000074459034040c40000380586404100350644ca0300403002290b402d4075042202000d00003815004100c0201640400e1041d9640c90303015850724414580076034001c9001c010185007204207070040d1303002c111045180d04c010f00e0039030311404609503c038800d5951009a596507070400741e601c14050801108000158000d07010700084084002801d0310520101c507841c000c0d895034800300580c644070440781c6d04050804007418540064410b00b802d9520445508204195080f9501d810128401c1551552080380d941c60500b00c081c0380c14a040844181d0302c0e04070720f1401010b80c0c0001d00c034001042005200001c011203074004c004c4290000010046d50008403a2100404664070610320503007010707100c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 891568012 1250 891566762 891566813
    0x1e022a0a0e06031507090b0301061e0f05090d020a03020a0b0a020f070f06050a0c0506090607020708010621050f0307060522030905130e0f0d020d0503070e0d020402070203010504 78
    0x3101d4101400c0e051281030020040c01001003914110141904c000b0700c4841001004400441d0040041002c0e601800482d682c2440c802a07030f00005180d11628102002803001c01c002d1180050b0388002100c11040043c0c031441900125440400c48079112500f00940c00301c20078901103050107041c0050044d81c4200c0d800c42d08003201c241055500ca103c0c6014100356042145c10621a03903000300c00070b0040250900c0c0c00c9a5420064844c1400c1c14815190a4801d80102d8140064240e04020840280000030700800419180400182c044031030001c000090711a451490414014148004500a07030340406407a520030041c9454001071004456008003101200da04005501403058641440e42d03154480c4082e56080404000301c1c0c00f0342142c902d002540b1006221185030043c0500c1c0510080d00c00185905256620003034103182d1074010743d900b0058203004000c245540000c01d041650f0041d1240040202c440c004140a0300c07441c80f0181d055800c290510003084080001c0181d400d10160f107409 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 891569262 1250 891568012 891568019
    0x216050105041a1b0304031b0501060519080c1215040c26060406050402031e1e01020a0c060209060f031f05030705060a031517060109050c0304031e022a0a 68
    0x90010825a00390105020410f0888103440c13110009507003080c00b0b410526140d0081e14803000d0a000301040448050751510800c2050b414400404071103a0703180d680115100e42025003513036440e868403200f58403881030803024000d407682c10b0088000101e42c01540b0b018a191500784060585542d01c5007400901d04551001070346025041d0300c22551025038041c041988030b540ba00e1000d010301620503a8580102c1000c0c2213070031518000c9014040004018140b0017240044203010051000510441d507401002400307c00360f400b1840d500e0302940848016100c0040b0408a82d0502038007840c0d03010881c0c000103120140d600c0003515030f880010340f030b240c4107401c0c0c9500525072034100c00d110713090f0048004e0180d403842600030f03003200c0980e190009000d5220340d1b540d042c04203001c240c070f041300c2503030b8001000500018002c0e014032a4494080b400309884c1d410076a0f4001c02e1080b41e075180c0300c00a0790101820244034801c0c4901024201840c14440203103580b80440d20701c4201410045206044481c0000b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 891570512 1250 891569262 891569303
    0xe25030207020d020d020406181a04050f06061309060b2805030c07060b0d0b160f02030403200405040c05031005012411010906021e0702030718021605010504 69
    0x301c9003a9805024850107242e284d00348141100d00c060200c0c2d0182d2076900200c0e040301d00341a00500c1082ca4903010030400089109030750540c40320145180100e082a04002400300448106a0844416a01503560700c45010381c1c441640d40c15000a001d1504040000038045409409000c038020001d031540b1070400e041c42900c4203d1154051100881c4040c0700080d840c051b00400362403002e02480b00410450700800004d4481140c880c4111103180444060040f90700c0c001007440c0030000c45082c103100c2c3c03080032000a0343d28081c510009000c007043c0d400e12000d1091100304c5261025000d0006d20150400c1d1030250a007540134040c550080c41008101c1c0c0c03603c62039010703060486000300c05200318114600d00170901064045140e030140212203580308100c40b030901c0ba080080b03028850061700c0e4110b852948044c1d5920410000101e00c0c248848009030350045100011101c024032403001e441650444071001c0d0059030f10808061040740c80b61818400c06401441c8a80c0c443c0b000880c121000300881d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 891571762 1250 891570512 891570517
    0xe06130e07050906010c0501020c0d14071707020409050105040f0b310804050603070509032e0509011805070f05010807020d0c0204020d0e03180103020306280e250302 73
    0xd002540224410031480c244900010b41020041c5031484800c4041d440316801d90f4450000462660310085414170078030b030300c44c2d0360704040f1088145051078401c05031100c41d10001070000688884100140c18400c540c0c455102800e499071010003400325140a0030a845038061090017a5641da440000181190720309440008400002c080c0c034000700c0c0c0424891706055982e501003141c2e900d604100100d501d99032580074522401c0380740c1d2160f503950502c10505040840316002036001c1032202184401030141700510007078407441e200340081c01c2d0795111242c901401d5000d10800c00002203184020520001003644416261445141258640e49400455034810b08591800060700120302129445109503442c1517210300040001d801e06801101250071603000320f01041d0268000035800c441030390845c420700007518090a0440c210314104000ca103807441e19141c01d4511851017900180301c00704401c1c0050141460b45009505417501c0c4680269104582d0204c154a0303025800c2008442e00ca4002c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 891573012 1250 891571762 891571781
    0x1015050702031605150306040908040b070302070e040803040b0907091e0b0d11010f0519090603150b0d0e19030305010305120a1d03011b05031e09030f0a05130e0613 72
    0x185140c0b11105d543d08042c29000601100e501c40e8485501c580072483d44806400640403540e40340d5070740d852624011745402c00c1d59014806400a890400000c00c0100c4240da40c816003042d402d010720398903c0f00407814854550444840c0c50318200c0c1541a12030004000400819613680030000da140c18003c21012440720003004140c480b5000c8070305095441070b07a019000c1105400e0150819210703c0500c009000d85000034000940d4417041000480c2d854021f0b0b4064160f40514103014606100c400b180d144507810250245a448507075034001120108041d041d503511006503c4000202c52400401800c030a102c16a40c86c4241c072100000d0980280890381d615180d6110482c001d0300701000900080c049403666680b555a80c00c021150b01d49040c40112034880710350741e056030b0780b400c8420100c460300e490b601f22080e0f41c80d0900b000085400001200c0d030360030b901d9080c01c0c0c40b051619002c0f036041c81f88024a6613003030780000d400680c000500c1c04490150702c04459440980700340321a054116442c028 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 891574262 1250 891573012 891573019
    0x15121406010c02031c02030304060f0203090d0e010c080708030f0105013b10030c02010c020c01021e07030f050115120201021e1908091302090a030303051015050702031605 75
    0x18046649907014040300701000b880a016031381d5a00c2526451018485840150000358200100300303c1000314900c1441180d0303011801c2107046084c0740881c03558807440c0140b810144040d090150005a00602c0120344580d8004c000c540d480e009464540d405800c15104031110071689000881c40b58007540d404450000403000244d072120825030001c100710621800781c204642003010b814150f4558560300a6480c20a0f2400b0490f180d0310309009085500c82c18106c4115006681c801c0404e80e40402c008403085410424107031010b00411403a810000356501c010680d1101206003010404190081c460001d81401104051a65900d00102c40d5003200c0000b80103070000c0c022040b040503c415035a142c080e220341195141c0910f00361100f042c5016003020748400310042040c08036480c21840c14207621038030386815400d04200401040280c2290b0000500740b40d11000016624100c0002d900c0081020304126160410000b40c09065903000328410390081c080c40d043e00150f080803a04032001c42c3ca015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 891575512 1250 891574262 891574301
    0x1a070c080f10180b01080a0b07030501060903060e0102040506070c0806090d0c081b030309012924070c090b13050114010516020a080f1009051203130203071512 70
    0x60201c2c4004003d1802d542941265603010340d00030995100c0164060115075005082588107810404c1c0801c070010720070f800309420000180111513020520000b00d80d030191010400c000403c080501a0169410880e001540403803184180312100c04202c0441d15080700b615103e03151914403544641030440b203900410340c1c4403184400504200000c00072800d041107100c41000d26601a60b040d54001e450180d09a03442d84403e210011801d90840d0a01142c4100d00708407048100c0490f2401c41642c280c0071040007000c01c0a8240a2540211001c450703102d00e0225405483e02c0c58480186082e80900340110400c8901070f420146a10610781614000314142c00402c1424004441542c007045a40e442d550a070610800182c883d01c01d1100a80242400351042500b02107029142c0491403000ca8002070911070101e002c10340201e011900c0d0040c40c80d40c0c60f5240d54140159440c003040d224000d400d4030941b140081c0039a441c8444000105280d6103080c1807001c028540002c0ea40c0c6601861200e2518 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 891576762 1250 891575512 891575533
    0x5130204033206150f010224010906050a030f030c0f1e0b09061306050c0f0c010212090a030903020d21020c090a020c0c040209041503030801030201030c0309050604020909071a070c080f 81
    0x40c05d034440c000c01481218140700c80d80911000b1201880308160065005900600200100b8042c3e80c0207001e0940e140c0c4203a9107140c8490102d07400d86c410150901040001220a1005550021400641040e0300084841620000c01c01102129409a910581c540082250102e021940b0350040351000308d21034140541e6110725004003000382c100c0700064800c1000040c07410211010f8101c3c6d8100d81c0005845130011f486818460348005e000d690303981c0041e091400041e4000000c04d095070340503113072100540c51030300e00608216a01c1c1c14002d0355490b046000d00d11158005505541400196200b11707003502e980b1030f24026030180ca6815599500680a00b1002d070038194013510507070714005c001203031601202c032060200c880c40b60810382c0042c00f0080103005658250296640c0ca114914080102c6852515030380c0c0c0325100540000c1c41255074070007040c1c0042040102002400704103202c001100c00b01442100c869009010881d0304014180000a002801280c00c1070200340440141840582 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 891578012 1250 891576762 891576769
    0xb070c11041a151b0307060f06050109090c120516020d0f170907090c0504080706050720040e0601080a0c0f0f0b03090a150605040b0f03070513020403320615 69
    0x1000700803403070b101c2d0305119140f8100c0349484c0060506660a0240d0b5480100b0b06181060300c00038104541c080c1d0610204214599004804000326100084001815924000200d6040e94404024852a420f00c01801441d954580140c3c2c02400c0c19021104a10540309090758104802005000454690000d02980d50400342d01d11354860880c8060b00c5000391502c0b0320400300c54100e244000018408142030010315020804030000d000035041c041e007401259030f203660305100c0d502d0030356200c000702960303544440d260354108800300407041060780c05943c2c40780c00560380c50038549000e5424008071140000c10081e40395080d01603c078000011044d05040088402c2d083e8005042c0c9419403207135660003408204429500403500306502c0000c10118945002c0100380c441141e03d0a12850036104804c4c09030390700046d56011a0f100395864401171100c044200002d000b5940701800421007010441086412301d1050300c100840e001c0b1402151310504c010720741c0c5140c212046e401d01c2101c0b003180310940c80d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 891579262 1250 891578012 891578029
    0x63601140a0e101e0e24040b150d03050c03090d0620070b041202030f130504060602030a08070f1b080306010318050c191509052110090606030b070c11041a 68
    0x90240040b81c042c956001558203804224034951800158001b050108115421750a1600001c5090b2101e210102910003d07141000e140801410b2000c0040d5071620058140140c415410008118151000d800e0a2400c081c003142481d050400743e80d55a103001d00c1c400001a83c10782d50b08410f1243c100c0c4e81d0303590765810b4003920034500010341c8400d00641e40541c541c80d0080211814048a90614600d003100740000d17100641c1001003503404c284580440154041d000c5940547d85240c02c507080c44004409641c04c803c0c052600400d24004079181c424810ba00000354020302c400c4c5e804200012a041720184a4544008004c02c0e0b5008011580c407145040c1004075000322980c44022807840d50360114141403e003001c8034a0209400318000c00441ca46590300000c00c038100a2000128031a00c1c00039510340041d58000e10381142c6e00c00128092002c3c1d944038a02540c0d2042962806080c0b28002409188000608a965032040085850141001d00a005010100d05152840000d22004200400c0d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 891580512 1250 891579262 891579281
    0x60e06161b0804030203100c0806010e063705040e1305070311010e0406030f030206061e01080c0408010c05070b09030a0e0f0117011205063601140a0e101e 68
    0x242420b02c00400560303007d02c07454203000305204001070001c15005015159880080143d410320058030000c2e0826100c00d0304031406103c095069000f440d1480001c40f00040141080b40464940040810607885c1c000b03004105032841d80d09419039680e00c040408040d40d903140002400c90300104010000141e81000d48a506841410304421149210010400301d030703030b161f00954003101d484001800b4150148422034010000b034522984925200807420036074000032540030304002c044000a20607000380c03800e80300a0030344c0c40003e100c2e0303400281008005420074102643c400010301c1c003090708801e00200310340b01b440054445c101c0c003001c0c0c00d0801c0340307010800510314107101900042d403240e20f0400c0c20b054081e290300c000407408a41791b410480d02d041c000070312802101c01141e0340b4031000803d08225449035060f41071202052156610740e00d000d8509030a21403002807010007880241e01841d00540001c41040e41266014504100704038152010343c60b0640c081006400e2a01c2901515040000103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 891581762 1250 891580512 891580523
    0x6080907030218040b072d050705070308190e0f0d0f0501052406041410090b030f160c0c0317070f050c091b0f1b0a060e06161b 56
    0xca6403500428a4110500802c488118410b000c010820600c07000180d040000d501e08041c10944c003984106282d1b40503a180d100d03003010b07003402030181da104408a4072205c0c0e00100347d4480c65038a1404074520b0300032056251207000c8051441102902c40c000159038800b00614220b005150340c0180030285060b01411383e940d40c40240340b6400704074240110390140700c0380710400300c2c0d0307203400410045000c80c0c0010852150740c040204200282c070441625804440498901075000714181090b650321101c3d138054400106d001c400c2012038061081c0c803a218414543e0316110f074a1402404403021940d0740e8000b00000c0c400b20007400030030700310344081040d5490115140d2400c1c41c15216043c0d400b80305507049480d035100c20120081410070304003003508021845103000c3c0c41a400e01d0b000c6494040c61a0303060740c0700f1000c149009410076556040c4020201c040c103460480c840b9040000181c550a101c2e030420b0b10900e004a550f01500b0104e020020f81c159075481c400e074075a403100d05142d112681c004c0e501c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 891583012 1250 891581762 891581773
    0xf0a0305040303080a0b2d010e06180303071a0114012a1e061a060301031703070c0210020f06150d1b03020612040c062c0121240807060809 61
    0x4007511752860144038808010313040e06400c009031500862200e550b007c29030401c0020000d582d00f81d15803100307840e8451618145000344010002c003203840c40c043d101003d80494104448400c0081d401362006068541185a00c1086a11140107503500980500c0c014062242c48030100e44107000c0e48658080688619041d401800c291501307440c1c10502d6801c1076a09550f42c1c0002e009104242c0c0030602640c8080e15954219899900c4e0111502c8018038401c4018400000040c0e0369403188658a0b06598020031f01d1010a0000c28000e41e522400c004400f528401d0102144500750183d1050441200081c14800e8405a40e9030328013403021484d5444078481c0d8020340100060f03850001801030091a43d150000a14250400c0700c450076140d0b0007030003030003005c2000c3c59402c4801c4800c09244207003101d0880c0ca00c00c06400488a80c6e4000103140341c551004a40302c10544001d400c2803a515403503802100c404005400100d03803c3e581c61140300d03019400b00c1810028140220320a96101c0c4804003500c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 891584262 1250 891583012 891583031
    0xd0b04020307170f010501080d080103080f0d020d020309060604150b0f0f04090902011b05060a110d0905010b0a23330d05130b01032d050106080f0a0305040303080a 72
    0x4100e000000340203150f0750050700035110300c0741c2d091080340d0040000c04003c0c60101c9800102038141801800060818030b0f000030880c04103051030040300c544518414045650f203403c0300310b4200a40055404141030b01174200401d03401c2c507007409050b20b0810760301c4a0300396162401002100c182c1c4944260a0090800e2005041d5010442c1c0940001c11000d400400c02440d18800140000100c180d40203400e1982d0710100007003800005c900d0340c0300307411200002c1e01200040700c0c0409070203492141c00340c082c01d02e0085401c011040d00030003600c200990f2101890354a81000139612030b00c00241001500c000c62b80442c49151103000d604480c10404550440000c926100420284100d00e661603100400a00165070303120718410664040f0080c0c0f06801142000d5403650800c5206110203082880700850603001e024203100c081c0700420f04241c0d100316600d0f40d850150302030441403060030390600551404001c1320300c010590342c0c1c00b41c0d4103541d52450035040d6a003d0391280303000740c0310012855a50b01040e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 891585512 1250 891584262 891584279
    0xe0906090a0e060103140705090c031f0308030403391506031722080307030309023c060306090a0c0201091a09120c0c04021c15170c0d0b04020307 64
    0x5005c1c50286020318080701d0a044028541103250303004500428900042100802100003601d07001075148441000e00d07102242d20b500c80910b2030b000134101c140c0000a01080541142c003400d462440017040030070074540e40b0840ba144d040045200f43c250200c3d052950300040c1000b802201d1110030780c10000f811f58490715609030041840301c40f80740d901d000003201541510106100d001c41c030281c00058207070b40d0511074403507220700448400500303241d02d0302118000c66803450098140d040180000000c43c80004941117207030110303282042c0041c0e00d4503180700c40d2800c0c44070449220b4040505259819140c0300d41440050810040d080119582c0e030340c0c1c000c000384c080604011750f20b040542c110340758185005164140954101c11003e0804100140c100c1d80ca8040b0b05268010803c4030010307150302040401028840d021200c4915042c60143d019145859680c030b0042591528090040501c082800780b5544454221550794841c120450040000e81d003030034100e030310600c0607040d10342c0340c0d540d243c90 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 891586762 1250 891585512 891585523
    0x2010e1908071b03060509030a140706060e0901150801090506010302061309020d020304120c12030e01060e070507050709150308030a0f05040b0a1401050d1b0b0c100506010e0906090a0e 81
    0x1601460f1941c1000c105001550240c0b503006001c101c0910704d4a500e12402030f208240819a0110008000c07464009000d00c2d640000020801110307480000d02e01000c185000300300e00b00c5940383c02c0300c00b401c0103e14000705105102900d0303408401030465908680030002c1941181c00810300c200704c0c01d000440d10030302070700141005802209005d45c682c14945410300c3d00301c3c510b0102e2820402c0214100c2d01241010340d5000c5900c02c141000a104000351180c1805090703941c00403800d050a82040c484219807000040c140540120309032400581c0300c00e105416a000c600e00350300801030400d000e00115544030700464009840c0a03000603070103283d1105000b40c42c01103030182e40c0104ca02c4200040074103e07008030142c45c803800f45000f02c50340c1410300281d101a540d100c090815110304119070038880c400390408018015041761030f034a802d10b80d400b596844c0501c6143e198182e042102107503280d405020060b40d60071004280310903542c3ca510600240c502d00402003070845071600703080c2540f240140023 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 891588012 1250 891586762 891586793
    0x1090b15150708090108010b0316202b111c05071a060a0501030c1e0e090a021e0412260d1a0906060307030b0d021203120702010e190807 60
    0x49513440ea0403402c005060040141e01030480c46904204012410b2010036088040108500b4010310300b101c2d144010300b000b4070f56030607480103114040094006800d148000c01c1c071801e440328041e4003000c1d480d030112191401a0303020300440d0300400b5403251006180c0c280748401201e030302d80142810709a40310b2050503404c04100f0b010072603e403410f00c900f6003021952203025200a0030700b80520340303a10b54010300d1091740b1011448a4805800d9210326903218400c0b540c005040140300705003074201b101280d07000b07500c5802c000548403e0b18a080c1c00c00c04201080c0d03004c8800c1e048801c0228420780c2c40d200a00c02024091840040d60460000b40341c5501700094071200100180c00900d400702200c40d0550499000d40c0d0511500780a400c116265950004980e800501460041100982d07000410002c200d0508001c3d44040c801060201005001002d00403400018815007095100d80d00140d00720f6680c280c59004c2c079006402c024105400104201e000b06104582c0113107011543d880c1d0000b40310040c1c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 891589262 1250 891588012 891588023
    0xb01060f140c0c0919290a06050406051c060807030507080307170d020720040c0e151e1b0d0e030601090902061c05061201090b151507 59
    0x84400c90015400000d091804003020903051900c1100740340240d8a16010044500c42c100c0704000038840303800c03040000c1c400161482c050104114105124905d006100c01c2200d1185030700760358070498681480c6110445805d521010b01d02400d040302150960f010070510f118080120042c042d00c00172600c40d01004210000181502e40e05601e4101d090080951141e02c40d548140311107004261148900360b5034000b249041d43d80e07001701120340300c044d02510b007000d41440c6000c0c290303041f03200010849400b018021241041400c11494040d0b8440c48514a01741d0000c1c441100381f030041003c07078001d00000390040c091008510400440012550000c2c00c400e0301500c140f045188189070410500070314090904011107506101c0d07010996420b03051144d02d607000e03110354081055454903411102034a4440020040c28503420110300c0280c5400c1e90002c3c00b40c51420345080d81804103220380034019a004003000410303261062100c0407490b0000f6001d500c52513042c0c140038103041e06c1d0000d242c1c683c8180d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 891590512 1250 891589262 891589277
    0xf091d0f03130b130b070f170d0b01031e0b0301061a0a03050106020a05120a03020d1a030609010b18180610140103090807060915060f170708070e130b0106 68
    0xc2d0141e11154003090421605000d08100c0030302c10800c50b42034070f100d01510b03620342e5200d0402d100708500401c006011010209022501c0030203143c024070851940040074010081d41400440450b0a204060300641d515050203240341602504803074080701c07004002248003516040001005050f0304040007016000003028a82c480e014001d00d0300529803400036141410940d11402d449984862000d0310002000800c800c4d028082c0e0b040d9001003140c10400c001c0000d84a001e6a07014101d015080e10a00c030303040010346d48807814098003440c0000035002945580030402c071205142805407940c1d1080c0c07141103151042070000c1081520a000c034801004142d850801c030442007003c0e0813710350425091200d0940450014421140c84640c0311100140d400d01c0750401c01111007640102b540e007d03040460005a800c5514000008d4640c9030030003070640e61200140700d6848102d031041c83c00b560003a0380d00f0443c0000d03804140340e100b2000b07402d880880141703907071b5041c000201360403403400305100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 891591762 1250 891590512 891590527
    0xc170c01033606060f0803030c071502190e040b01050d09020402040e040f0c0608042102070b0f0418090c170309030607031a09091e0c03010603050c18010f091d0f03 72
    0x83e406150001c1c80101c5070405400d0814600310340724800240011350741c600c0080c1030010408120040200c0d031035001c60441d2100c1e05400030b00701c0c03844040c800b040001c46406000501c0c0c5014881c1d042c03254416102c0605d00045401100090403510009a034025402c1c0400607113050100c800601c550703c01c180c03802146045150520104c00c040d0807800030001e0402c10400007a98445c60002403c01026a00b81e405600c1e58040380b80440c10f030080d1121010214000d5018480c0384080c000b6500c2810403400b5120011200404031102258068541711a0030001c214086030a0801144031401400b40c0b894044a00046890407c0a03100180003c0c0d64030034011028800181b041e503009000c031385041040c208140b01c0c0d9030718960741842030781c0c1001221039110140020840c030031016001400a00007a9030300d007010f030348408410804034011807181d144180f030303c9007681e103050503248401c101480e014100707100180101206264102c40d4800b242c40369520000400100b02d2800342440150b48d15003d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 891593012 1250 891591762 891591773
    0x602040f06030204050612060d0f12020705090603100908070c0e0105150a02071e080a08090901080a1205070c09050f0118140412031b03090c170c010336 67
    0x26581c0480101031040c00140416624082241c680c00810a1040c6c0941c541c10009522400d400c000100b51244015450040001c84130002441c1c920350303000c8c1d600701e079a01c10a2054107101100e1081c2d15800c8803801003004901c9501c151502409007103107509011440d0381d100d10140164202c01035a1186000420407403421a03c0700c4000d181c1030801a0400c2080b04000c0e5403002e19020b2140455064890282034520310b04060004107009022201e052005040020080d80100c0905015400003030000c00d9800e000900c504140380e0244078103035034101c032a200301c82d00e400c02d060803241c0a6500800160700078013400355034080c0c0c103d80c40a880ca5413500c00c0c000c1d4050501d04e195203105040030940c44900f0041802198416001001c480d04803480c8801100101074048840043c150340c0b80303e070361019a059011002c2144101201104c054889404040c5404009020b002c29404617140704055403080d00b008014408040d400c03546110f6102c030140003101131701c91202c0a0540c000326003040c0032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 891594262 1250 891593012 891593039
    0x91b03150301051e04060e011b0c0605090a0b0403050a0504121109180a151404050f060901060b04050126240d0203030405090705090306010303120c0e030601140102070e04060204 78
    0xf00d10749030f440c1a04c501301e522509400d80200081c00c0700d683d0b105c00c400345035003e40050310401c078980c90181c519081100080c0005071440000c0e07407060300d0711b0300080c01d03910000764010000c0d4004510041a40c1d80da0b408840b03c1e4030041080b000c1050038040041e41c034908076040700c05144140709401040c45001e01340281c1c400e008201d0060140d041c3d648050038100441c1c1c81b041d640d00000c00d01000c1244050a401070401c1411004000701c00c1000c00c001c0c80780100e8010b0040f01c40c0d0741940d0898590540041c281c0e4598040c5541e51507040004116541c02840d80b03074640800040c0741c0c000c8a81c50905264854022569200e041284451451104100f40b03200b60f00700030704980010b10b009154012076980d010324091580540c1f00f00020940041c003807805d44008410003002c075030b900e40c0c503440d0040400316141d08006c0984e00340b42d0002c0603580115683c0a5150002c0c005001c0341e881c2c100103880c0b200311142c2c018158000c84802003004000101031238840c03030150101590b1907140c90802c89920 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 891595512 1250 891594262 891594271
    0xd0203090105150a060e010509120115140a14130c0f12110403030c1e03020a06050c07020102151308121f080a0609080f1c05061806091b0315030105 65
    0x60700307946600c1907841800321029100c17585040c84041424a005a40b140f04502d012a800507258624607000001508030070341070000300e070440030030075652001ca40d06920100c00c02c0b039020070500350500016030f8903002d4407106500240030b02003031040c0385059805c032a00244140c0020704140d4080100d1500603011a890070580d01d000c115850b03681705c541e815400355000040c01c025004c50039209024050110398502020300c0c0d100100c2c0c81007403401130f54814404100f20346c00740c1400300148403000c485055aa2481e01a005401c40ac12a0b40701810711190003400142c8103408a41b500e030200305440003803c099081ca0f04040e54a040c04011020780b0b030f0003624188030310114081c1c18014104041819080c1d00d0f0301c0400403403030042c17510301510070780140390340e40300c01440c00319044040d0f0591a890b4015820900020801e41c0c4880341440b000c0310111001a9110040758041040d504000c40e4060340704e10000c101c40b80500320003900b039075640d1043c1e801d10070401c104400f0f4029072a0a202d0260031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 891596762 1250 891595512 891595531
    0x7050708070f0f03060f0921170f040201080403180608060306090105070203040e04261305091522230a05060108040f020a08240108010635030d0203090105 68
    0x5403415200d41c3c03240d80b090100030302072a11a010555a001103810080c0840d5004040d0304246800c600543c4000110131002e40025911144072010f440c1030074130032805002c1030604145699141d400544200740301800c00c0b020030404108010f480c1c281d403280035000e000261303948001030609908046c42e001000e44202456450002480381d80790300081110101c0718840e140314540e80e41d0f4101200c08140b22403602d13400701e02030680240a48130300b80040c07644002e44400d44040c1a100d0041c080c0e0a0412108814194880300208000745010004000c0c45445514145650304061010380306482400401c1c241c840b178603105a544001070f003001c650340504a050100070910b083c900092050501503c003a0450100d180c06006540b80c0d11034050241841c0021030340781111016200b141c095884110f500b5815034000046030001c41070250004486028a00742c0050103020800c0c84400c401e007104401e000e5034048040442d000501c041c0100301500c00c40180c50380740020b416400c0d5640109146035 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 891598012 1250 891596762 891596789
    0x330316080c191b020d0614090c060d02090a0b0703030e060901050403020a022e1d010815090903041d060103061d0403051c11090a050108070c0b070909020705070807 72
    0xc1c2d03440b000d0a0514056851030f21800300340f400321400c40703650714a400c06900198240c401c6010311046402421039498404a2001c4960b80c1d0030b00309485e01c001210350303039003c0403c001041d010030098004d407070031040040944003025034451607850306034050b45040380401d848100c07102c1c0030301050041d00d50005501000b44072500d0503542c000d4640d098035100a00c80e41d902c1c08000b492800100c10640618511540d50b03060701000100030b00200d100119031540b070100102c400186520031403820740240001c150082c0d003120300c1010080035110041461003544401c2c000011443d01c28066030941d032420f000d902103d4200500018240c442542050340c1e81514041603983c11410400c4c850740c05901440c1039512040b020207000301d400c56101d044c11980c2d050104d4020204403580007804210b108482e0301d100190380c2c800640300300e0411129107000c00c4180d000b000220780001d4003107070302850b1458410081601c46d601401203070804c120030f0760594400700043c0050a0304004260140c804020043d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 891599262 1250 891598012 891598027
    0xf21010f1406330d0e1501030c0504060602150604021c0b130203061f02190302032106030a08130506030711070602011b3203040b15330316080c 63
    0x103e40c1880202e000d01c4103040050307005100b0726a94440f4410070005000c2d070b0300840d411000070030340c1c260a0000781c03055028803500003070300d02d031901c11001191199005001e00858086200d000218020195a040340d02000a9140c1013902d5242c2280c8000f10000001c0b0311100c1c805114922038030060200740c0ca4810001e100050f40c94403107042e00204807402e03400290701d1300103049051400c100900c9400004140b542c0c030401d40c010002d001c1c00300c044509010f4810b1765407544900020f040d079000e5096000b0164160104029500030681d040342c9455103501c2035601ca0104065a10480e884c80c0054118285e4070808041406090700610a0f0720082c84a40c0c1000c0303000b40360b1003580490809020802200400e44011032842d56404200c42c052500c55181c1e15590036082d5104950444007258103800040b41b00c4075825110284070300c00341601103401a80e80324004065400c9420240030805a00ca00080700d0190000b14400c0381da48401d03140e40c0b030285002801028010f1b0200000400600014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 891600512 1250 891599262 891599329
    0x9183918090b01090b0a090c2304060801060c0f0c171c020303010b090307080303010e10080109050a020d1a0a0f0c020c0f0904032604110f21010f1406 66
    0x141035136280f90000070001036040000b036291085030300c500f540ca81001b940c81507680e0080003a00401d400c41401c61198201d030070081c4041c0c40f4074080c9401142480006018940c41140070950581c0304000c200c18901803130311740c001c881c000c903031002b400500414040b1048a80900c900070004204e800d80e02d2403400a924081e441e07010500414038080d202180140c000e540c204200c80040c80b107141500d940b5611900001d402c11382c02c43c0c110f4460ba40704240051145414030a42810540201c003421080b05140e00700300b20321187c5038090365080d01d0f001e107040303d80400109603400307a03004400000f500c1c018820a40140d0310306652900540d00040180b10040d29198001b00301c024049805c84200d0307540b440e0640740c81031803141e56041e104d0700140090f011300e00201d03c0c6006a00410300398038035420010030059499004020107400000c003150a40724a551710128183c20704c844000418400b000f000c1040440d8aa5140104403400000030300c00141090011081001c6404a10390099100c507141ca = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 891601762 1250 891600512 891600533
    0x1609060f0b13090b0f130636050c07050115061103090604090902150d0509100501080d032a090e07030c0212070f1a060306010918391809 60
    0x81e03141c3c41c0c0e215884010316582e80f54001c040c1940040c0504403111161400b080141a40d010f10516008141e1500c1444004034109048280504807100403140b040107201002d031401814100700701c10140540e400203602800340700103202e20380c2405074100c1d02c2d0840041c09108000f842603c10b4100300841111602c480b0b0480b0107645015a01051104180c40480c030f8600c0141c1134207110b00380209009000303103126000304d8014040328045030581420007060034122035082c0301d0028164481c00030801031501940010000c03010106000c00703858070086c1c0700e00c2c0681f0080c1d110710009103500c1041c08106c8040c0c209680109407440c2c2003002c1480013074040d40e00c680740071001c0d600700740114500e820810142c3c1d40f044207903405040c4c0c02078900382c001e066003280c00c01e4888034424022280003040400f07441c030980000505840403d00d0490617515200110419144802050000c4030072038920020040922089101060400152286412981c40114031103e9100114038103104446021030280b488 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 891603012 1250 891601762 891601769
    0x80604021905030c130f060e0f06032734030c0501080c090621060d0809150c01050709080717030d0b010315090606030c0320030601021609060f0b13 65
    0x1022581e9131660800e4140e80e01440c000032105800c082004280800c003100300004644a0703031542e0300041d14030b80810802d0711541c4206900804148005000c20604005881d01556004900b040d040c0c203103125076080012000300c1c0040140100c2032003012000c1244440003500300c0c90039056440b81903540c0e0800c1e180c400e01c1041e0401c5200008035a0320344480040354590b0b00700401c6140c0e20100c0360310800742c1c0010020001c1e144161100050644c0c1402140c4e44682c0c1d41c4203001c9841c005001c0c040100d2101d540301e0764040d164041c0161401c0034401d10038180190700d180c40d4400117600d041c2510b450300030141c2240704104c010707450381420700704004290341c01000c00c401c0204d8910300d00d000480041106003540c0100c04d0200b0350008035841c1541c804025507040e0765092020030f4030361406505443c4140d031071929413a440703040c800d01130014402a40e00004148165401a05018000c186418850304000c0017182e840368108101d86e008030030070004124443d00c190506403500c90802052240f40b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 891604262 1250 891603012 891603017
    0x5041809120302091305010f260c011220070618030c030f11060a050106080702030c0c1201060f08030a1209020f0d08160b19020403080a0c03030b0d0302030a0806040219 74
    0x280c9082507650b11726100303003c0950600c1080b0700c1d81d40c5c5000104800c02c6110b0482c500c04050504981c204407192107009079121580201850317001d02c0300440d00203044209200040d96640000c1146484000c46640070040c0040724680340c8565040c01e0084894a400012180314134008070030019801c01c490b00c0050303030035007404140803003a0349044d1010340030741d501c41500d401030000300112006241e001c20f0637524a9031381d403440f071307a90030070285c0c1e488c441c070501a20154890b6001495a140515000b40040d8030303200045040c03580d038212034030180410303005480326400104200e06001da0045540442480b51002070200300c01d140c0100701d0040031980c6142c09118003102a4060020365021103d03081d0354511032141514850900d100d001d4015103c2e00d0340f0111100301c0743c800d64014001d40302901d4010000500d8506000000c0c0c1c2c02ca06000b0b01103080c0364640909030084c1d5a0b403242c00111601a4015550b24070542e034005084000003401c2621852051120340170140302003028815a05207030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 891605512 1250 891604262 891604267
    0x70303080a090213020304030305090d05070f141c0f170a090203010b150406170f161416050d0822050309120c0916230706050705041809120302 63
    0xa0884201418030602c0c041c0d0010340741e0b09003656080c200e07402184a03a0180d6000c05c01a01e03101001511900c18481c2d45000a400b440513002055000d12008800b912500b01091a03260022249050540c0e04a00c0020101c441e40700b1070713800360000c01010b81030581e80780c4a10080c00380302001040c03181c040d020030040b0b941d4560380c0301152000d501a00070a94002c114801205061034800c0240c2c0c41401041c0014403c810240c0600c0144402180208400d03602904030b41d644040c000300320618002e04000b0440c00020711a001e8620030000c20030790318040c1448120b003c03d0b041c240e00c1c0501c029070000801c14404100711101441d100700d62034100740c8180e41c0074401c0c0b550500600c5c41c068006140d07404003208511403100c0c0300000c3c1c542c650040586080f0196941c2d0f0340d4030300d4640122441c90340460380c0d40e0b56500038210445641004802c01c20105410700399544c0f941001c031381c412a401d0700881c000003401e000c0c2e00741c0a92401a0011491001d0068442c256102001220849005003d05401 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 891606762 1250 891605512 891605521
    0x712051309380a0e0c091c1a0406180f02040b03030409050a02030103050c030d020a0b07090e0721090807150e0a05210901020a0311010e0f0a060c0203070507030308 72
    0x240341e02d0201e03180000107052100d00001007a407a00c010910b00a0311841e044000011102034a0038074901c6030720781d401e0329800c007101e0701305212200f0034030025500c6404140f005180002c1041c00880c102102c8029240450b00d03103450580c048540d0072981040011619610314002092281e1080d41d1645c19180496180f0341c050102e803031402550010415141010200082c24030b50341d0145040b6401681240d24644500c018191204105400b04e40141c008174004c9000c03950030194180c00168134602040c82039074034910110708903c20b0b20701100080a141186101c5411f084011050a5084000b003010340403940c1c17105d445100d4204001c1c0401c6002c840c3c04121090350f4404603004024a003918240a001c1c0341103a10f0304030086840c0a0b814109028620101035402916026841a0000e000c2c4c0015034600b903038038581d51185640d45640743c5c1041d111007601404482c0300f045c9034000a040f501c2c03c52804d003041e90f0784201c2c0c1104550041c420031001c5030000a01c002203075018200a44a51039 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 891608012 1250 891606762 891606791
    0x61309060605130b09130c09020f1e030717011d09010b0a0f09050a150608180f0c0a0e0f1f1508152d0d060c050712051309 54
    0x16484154444445404104400056040540b008004645c064030381c0c0d4440460000d420740d0f1100203004441c07403507002d02000c14981c2c000c0c503129880d607107510b0410168540001c51114a582241032038000441030200c80c80d04560301c0c0b440001d080348820150f40c10220040e480700604030b0f170118500c10840218124000a40c03089455420107080c100c0d00030f4485d002201c402d445445820f0100e490700c00000c4812150380300c0e00100d1104040c54417042c41c40e2020440f240b40000d05180511240394481d94a8070f44100042080900d080c005813032402d0907102001490040e69100d20486120302041080b030310201d845565010340d00c00800110b045c02440a4100581d131604201c0c1d0050540ca002c45113035410021043c45065085008140c403c150dc00707210034070f0070207600b0b0303035080001c0c00c603248140130103c08224000720060202c100052080d103a0f8402e5441968001c804280c00003030000c1484281d10101104800c076041842c940340c4080b014120301400c4e845079404859840c0300d00c0c8044007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 891609262 1250 891608012 891608021
    0x1a01180207031e18060f0905041a041a0a14030309090717090601050907051c05070c0203070b040e060603160e01034218050c070b04061e0506130906 65
    0x90b10703114080d420800051000d003554410014002c1240310340c4070006103030352088681c2840404247c2d01c2d03c059134900006e10000e44143e440c1e103000041412900280307500c40f03100c1c044122000d502c0c00031f211000c90341400340c410180d4000da080c1480d403429101d4945c034004111500c40800707483c070a50039603403c0411281981b4038440c10228146020912641c400300181c01c5058072801c0340d91517200c0c3c0741c110080d111403150341d00089a0704415460030031000c0c0a41c0c05184e000c1060300b010440841c543e030000b41400f849070000080d16401040500000450326010740c1e0011050b02c01e00e00e0350078201000612003000c080500104140150421000d91294020103e440103400d041180311490000b0009040c0c02c6018682e407407540b842c44102c206010304001c07821100700e408600324521052074424040c1400030005000340d075042141c400001e168000151044d806032100150721100207030009a81469119242150b45c28403090012658804178480c02c2c0106a8400284081e854a460000350 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 891610512 1250 891609262 891609287
    0x90922020303031501033c2705010609110322060905010506090c1813060f0602150a0b010f210e0706021005130f0609050a0c031a0118020703 62
    0x40c00040f06001100b82c40304501306802000f40c03814085051f1160a0680c09401d100014205545150084c004080d201612581c805406c00010985c20009103089140326007003902d00302c0c1590000e40c0f0b4810702000707120f6400139140c0d441047c0036149030400c5001c0c0703900010b0101103d2090300401c000c810203003c207180d04443e034004028001d01c0c9071810b0250007800c0481e00c0d40e004102c070b0400200320800d03040c116099566201480441890b40c882807104075020031241e0b00401342e4030040810703521003001002004149507401058506200741d40d083c1c4d01c480c0504075078170301030400c030300081183e810100c0003c0c40325031481c11078902c074a0408009054050301004002c5189000d032941120080840e190060b81c0050702101d50074180001d007002101c0080f5882001480281a000006a9004030502c1103e004513000300d4102510b40322303241060b1074140221440340300540104200103008040600c841940d0514400303e41c5031110125007a0007203002c00c01000ea0010386c984c101030080c84080803d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 891611762 1250 891610512 891610519
    0x21305060f07020414160f0207060309081c050601020d1103030f070516030e1008060901030f170a05031b12190212010803090a1e05130f020a030c0e0609092202 70
    0x41417050b0304a071440d0426078012401405001200500300d00801c5c0c0081100703010350003007c040c1d10b0180100d004203505070b012a5405004c00103112200f40c00410f03c1030000e08040c1c0021282494400645840700014400043c003480303c103100c02c02c10020040d80c1e40144000c400c3c04d05903132840f0003290f00e0f22610195000c905203a44a00c0d080c0355000f0b20b0103081c0314007510032100a003584081620900030481d00700d80d20505010051001813084010483c056200341c1100103d400d010314800c240b504032058000000c2d00210400c11040a01c0280141c006803850a041c0381051200ea0241003441c001c280c0d08441c01081c8842000c00c1c090750449001c2134620441e40c00c0d5513103034209603440c0da0201003443e208100d91607020039070340500840001440e49018110401520f800c050041080342e4203d20111070750746d40c0b0300e00c02c0b19a4a00040c10403d40302c4c7e8000132003c031750b850050001070240005030700420003400580c2e03858590f0843d181d00990b4032141e8030842c2c8414041001d0003d08681e00940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 891613012 1250 891611762 891611771
    0x150103060312090602011a0a0b0f0c0d0f1403070e15041d06090919030c050309040c200f120c030c1e0c0303160f0201350109021305060f070204 63
    0x40942c1c3c4800400143c4400e64024002e01d10706d006140c40d1285d101080603400702c807213a000c004107030000b4004c2455036840c500442c28410340041c0369050400d00030098020600319118074034840d034459210408000301d48003e6003541407085c1e004200d14620300e14240260b0101d01010002d8600320281c078020107040d0742d00d0307030341080e91075048450f031405840e0b0703a000303000400210748904004070340315840c024a4011300200c900309481c2103c510384900341c15600e81c0130801200003281c889011b079528902007521244480b03540a41100d01000d1401c040840340d8110a026682110000c541d80602c141c034039120944138a00421a0303419445a51604180d5115200c0c075030664060440c3c3c2c45444807241020342d208185c1e10024107803240320300399810300707409940d032000c01c005811003110601460062420065010900038070302c0d8201c001c030300210040d290500b1032071821544800020f02402c070a1030151308086041885022003082030195912581c00031940003040c60070b00e01a10b8200ba0001e10501 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 891614262 1250 891613012 891613043
    0x604380a0f120e030d0b0f0306040b15040c0e01020c090103110d0c0e0f1e010315020f12090c1c0f030507052e0e0a020a090c050409020d0501050f0a08061501030603 72
    0x6984c0d50041480110541c2418000c04051420444900784080e000e80030b00015680c070f9a4050000d00001c141d003440c80000300036001c00784c480b07100c0e450300d200b010303142d0602d03441c91000007926007104500014414109100107000040220350f125400c0b20042d194060001103502d42160300034000c0c0c002403071288080c0d080040f20041e80b0b103c1c074000c200f05c12024089031100c2c4d00c03551010200b4000a00301580350f54003001751f100380354001d001000c45103081134142549020031089448056460145070340c048400340034181390202040a4480d802d0070140704000c441d6940c103140d0041c0341e801038107001000c11084140f0100384207a281c00d04051b03001010310700d041e0b0300940c90510036402c001011440c104000c4508140000c0300c211098000f41a10112442c00d0042409000501071740e00420500384800500300146001400d01404420300109407581400184011022108406442190502d00400a4482c04181c590b00205030000700e404400c0c508005a0103010385a00c010844000e58001a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 891615512 1250 891614262 891614291
    0x720061803070506070f09120f140c0a0b030a021b1c03020a020a14120a0324060c11010c0b01060305190c0203040b03040c03020604380a0f12 62
    0x154800c84021603108404042800e400e50703079002d07540000384194003080c0840c80e00790042c036800d024081640380018403540c50389042000700d10700f9a011105940e441541c202040000c154042070152078200030110384040c0750000d00d070304075507210b45006644000f000c00c0d480c030019011500440070310a04a0078032420a0b109503038a01902601810b1010003810a880c401d100c0d00840e000d11045500914242e80381d038a550f035442c6211024640c9a00c14030200203e51010103014084000c0c0c3e1741c03000642061051008003103031070545000d5a201c85c1d031407418080c82c1d4201c5205a121a001480c9080d042c290764010303620303030035204405040115440000990300754140c1080384141c510704003445c650f42d1104100740c15940000c6940c0d0150700141300074070651a080e0301650b0b00c540544640c0000d1956900820281d500c0b64004080b10416202e41d08440b4034150b85058064141164121640c000f4004c00c038618022100d4081c10004204e8090b080350340b080000902c0c0000180c1d040140341d0403501207 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 891616762 1250 891615512 891615523
    0x2120f030c0d0804170c0703050d09050102010b0901060206180705061b010e0a0c090e12040b07050f06130f0302010212070e1c0203060f1801090503121317030720 71
    0x74211948039144103440c1d030b00c1c414890342e4042c5600040d24480920103e000c2041c0c1d41003103000d210b491140e07000000c0810340410900c41c0000c1a9161031a2080c140000282901c20ba401a00d00581c14031004100681c0d0000e5030795070121030610300701c08454068122908000c0315600169000d82d001c5411590445c1c112a40c3c1b294800e0000200030b00c4042440c03154484580c01c4010301603514000040120f00f201d42c00464940c11309005950341084500404c07405904550806c01212402194181c00c12008000780ea800b024001c000b270200d8a0082990322186012020042040b5031903118201014001d4041d2440e07018001003100003031418a0004007072000030b00d21b072441f49101140a4411745030626a030310103aa00030f00604400c1e0b44000c54442c041101405200d1020748441b41d210f000d01003882240f404510500185a42d02503031659a5079041c000b40c5a0a80c80010518800004005926442041002c0000c2c95142c5da10703000e09944240044040c04042d1803913002502c0006000300d01e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 891618012 1250 891616762 891616777
    0x90d26030a06080d0f050306131107050609030310150302040503010914010f060602060c030403021c09030c1703070b151206060406090c0503070c0f061103100b0c0304030201030902120f03 82
    0x141000466a9121804d82d00d03c031326110340e00400e202c00c03942c4441d42e1003000215070010018143c030307150301403112011023110707250349a11144030f4010550108000c014804141c00c0882d0000440c214240400038214071402032252082429400c1c880a00e001c0c0650141c0d80107200c020b000700301420060401038940d803c500680d00007540b0388040c01c01659454420b00b015501d26a004009550782c407966000580d0025001b0b0b010352040028a00e41036042c00c121000145050f81c0c0d01c10070520f50714001036208850b0700180050b00003040300f100388480010a50b40c2035500281c51600036190b003130400310710100c1099006d803c1001c05050881941000489600843c070603141000215555455081112004030140d03001950400129400074403d40714440c030755005070394030406880d003940c8100885200c1445000501401304c01c1210f02191044900020b20703004500600d4500340c0c4030029200e01c1103000003414075a0715284401075441d5440700c0040e10401c0c3c0100c80c1e1a030044406190f89030801c50 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 891619262 1250 891618012 891618031
    0x609030601141345020d0c260606011b020618030723030c061b2406100e01080703020a03060b0408030405092505070f1a1009050c090d2603 61
    0x1c0d0034404c203800010b410314251181040032580d00354140d08010410002da94162221007664201040e220705500d0385e00d29400c04007030400d034510703224010541882c000420250501c402e101c40d00c030010003510060240180e04450b0f0b01e070303550316910701c075101841e031188000d07050302c505a40440d051080f04036100608101400e0340c015408900d0400d0358445000ba016900140c081c411000d000503401d124070340410b030b114140d40b0008500f0700142c594580000b0003c10300e20301c1006110f041d04116903108403640345c501d0040d4032b01d0034050001c0c1c2111000717002841050380c0001c2d01800588a07900820190000881c1260f07540e545180d910b40c0c0c0e8100e80980342c4103141345000f281ca48074012a0b014800b901c0e4800800350203140010507681900031240566810018046240c00202c8004039071040c0c41111a44408a061440803801c040100d074010550171440d0905004100000100784c4402ca0000c6403040d40121052900b95203d4800c00540e545240440070050444041400518850442138 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 891620512 1250 891619262 891619331
    0xc070b0c01060e0115030c122301080105040f030e030a2f0604080d0e0121061a16060b0a0f0303090602011506050d0f0b030a080c0c06090306011413 65
    0x100780442d02000f00388a112103d002480707400350b055000342c01c00b100803807583c10000840341c0e1076001c10040d1030400309200f000304040e56a985ca8410344680250142020b6002040540360541d104003800c141c4620190078054544451069a43c082000d40d0703800390312008881344082120075000e0b06405840b00e401d010362071032400c0c51040c00e01c5025202141c070b20070024131410703038101c41c00d64201d1001028075040110395489681c80f0400032803003000301d22155a001031142e02d0280d01c0b42c903005040c14101603200c1c0c00c009104024141c42010b149454001c1d00025164448000148110200380e020342420003161000009064121800c00100c0d045500240000300d20410348140100043c000d034000300e0001d01007070609103101d0b849090646000d41000407840c051000013494554034200071a1074100010701070561000504ca15440718105848050510440c900000d4690340f050103038188510b1400b24491719513903800d50142129034000000c01004101c08a0b400380319107c28013044011114 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 891621762 1250 891620512 891620519
    0x1e120102250c03060225050d1205010f0e1e0c130e011a03060f04060f051503090601180b09070801150903081b0106030c080a17030f0a0b060c070b0c0106 67
    0xc41c081d02080542c00b03084007201c00d0850b0b5030003001b034114641c6141048000c219494000104440f501c89450050004028030501100d00a00c000d08007400c00348024207103001080703c004009008006d483d501d4142c01c00c20b596555100260020307001c4100a8203401c003042c007190b070005400503d581d103118036404075035684812440640c20b000f0311803000040301c0c0040c0d4100308901c40b03003c1c58002000070600000601040c0000702910790302c0d002900300d00c56a0004010031300d401c0c2184045540d014a102e4203602c0d005240b280c850030140f04030746040034402600040042140e0080035402c10043c01000c09083c03d14000b000e0403024050800c410409501080e40349002d01a0744040b203520086092512100f86140c0551685066039220203640b180804800945e2480d8110050103c5a0040070102158141100303402c020442d02c012140d4104280310400300c00d0313250075034800140d20000c03075850445d8010424503c81c141c048100b60146542c0425003181e0321000340847c0d0600742c0240801c545 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 891623012 1250 891621762 891621817
    0x12050a06180b0f04240e13032007080d030b0307051806011808070f0b2809030507150f09030c03110d080a1707030e06150a0b04060903020307060309111e120102 70
    0x141940d200070a10311404207180024800c0d0710302a00c09c6041d502070707801c0c0718138403810615150386608140b18940000f03000441040d403503c9603035900030341280200b100910f03042c0031500c454030310960000c090310810002101c50b409140d400d82c24008855130348820503038808010303232200d505024546950f80507240014008207030b2020741d26a400402c51500742038060b805040c4194004050000910004100010118800317001c0e603c000c02c0b0006104086081c40c0c40001c00c016805910709040c400d048100b880465201ca0000d000c0d41e078040e40c211404c03044100000c07800030300c0000003040108005501244250b1106032051185629850745400da00e401c60180c00744c0700352807502d064562100c7d00043c03005120000043c0754009c00390208444a845000ca0010782d8425001903000c2a442002001103040c1040000d00034411441e04004010469941d11031840118031a1880b03080500410413280402d0440d060312800003c008030b451080161940d400303500410104800082000380d540320840 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 891624262 1250 891623012 891623039
    0x506010504230111030c100e030a0c0314040909030302090f01110307020f040b04020301080f06091f090c0b0c0a140f03030f10051012050a06180b0f0424 67
    0x10b040002003004803241280120580c9200d4428904020b0300c159031101c50f0600f400205a940750b6900545141d00d48901280c0584105074040c00312030b803080140264041c1d120780008400c56162810156960103081200914041c43c1c00c894a000c3c0380c50f203840301305501903000b8100c652064803403403110705508005445200190b218429a03800400c0a2801440c140b06206c500900040000542d401e0300c0c00403e040340c000340c2005820b54007132607a41c001100204036942c0c0c4001703e2802032010040e50075000408151070050344030b0407078640765403900700321a00140e100039203244c061480d00ca05080c103070036036141503060080e5a0000300303000344402c1e048041441c030085561400198656103d00160101148e03005101c040e500e00a01008a00c4c1d1ba1031100b5548074080594495990301c54201c0c81c42c1c110351026005540300e070314081c41000310f440e40440c0903c01c482440b4000a0090349070021980b0900001d04a40e80a03107050382144071101102c4003005205d898407254441d071502c0742003020121 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 891625512 1250 891624262 891624269
    0x6030a090b0a2c030f0901050d0608060f0c0c0c0f01120c020d1d06160c03140d0e01031a090c071e1b08060109090f050312250c020603040503120c0d0506010504 70
    0x1c4d0010800e40d4904c3c902c10004008444040c50030a1a10000421a9044039495004007809420030303814041c0051200c48040e4101202e500401d01c3d01c090400b08590310788010b031040d0302a104510500110b41e000700d101080d04200c0400a0001091140000f5140c0e10740e40c800c030001c128201c1810201803003100204000350740103090b0510340401008000c40c0c402c091001162140f04400e0080000744105049c22403104100000300000d02d04001c014245241d041d400780d0425103030960490415054074044130b8855815110f04c4040e8469180a1034140308811000d4100400c0e25079240c401c851914503818068000c88144800c00d40002404144030310728030480344103038800c4005008031840340e488080300910500c03005645422aa070740c1c5065400000e03100f0b030105408404c0001c0507a80c2d20340392090075092a03240000900d03901e80070705182080701010b80141008000101000b2081084488014001444050324a80f2007038404840e0b00c0b1686403280320341080007140e12035002d002540d058 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 891626762 1250 891625512 891625601
    0x1707230d0c1a0a1104060c1a15100201022203050c030304030c0b09030c150d050108210f070614070311030f0103031209020405100905090d050906030a090b0a 69
    0x540e0540c0107001c0121405042c0201e00743d84d0308100e449420010001300028016615204203e000c0c46c242007002c0c03d050300444151203c1c02081010310702d08007401403041c07030f13080701d0041c078016031803404174024081c4507003004051b040e1000824034607042c861008216403094080340c2c0074004080a142e2240038620008156a9040009000101c2032002800c9104409000c4910b1081800c0000c1d54054242c6001056810001000d200c10045401514090101580205068810645031514050440e001d2204540c0d000c0342c1c00b9500d240440c00c48071070b6504000103011003a803502d1100c03d451010f552440120385000143c0c03142070900e0301175074818100f0a0801649a1858406449102c002e41d0f2104049541c0c1446000680d80c0340310300350250403000061207402c1c0c20164043d044902c054254180c42c2e0100d00415507882d031220403210300e41000e40300c01d030b129180c17800c1c040007902d10303501c0050401c510f40c42040003001003940445003203000b101c82e0fa00124102884010f0880d641c0f03010540 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 891628012 1250 891626762 891626783
    0x903081b090d08091f080105060706151518030201020d08041a090607020705030a110d0f05070801090b06010806010818341508041707230d0c 62
    0x44500c030410000302030250503040286045080c4002442090210008031000d82021480e105981021142c003140d9144c1016031240201a00c0000342c0101c00510030300703100d410001040030070005550490714184900318a0140100d80341c0295484007200c1e0b1304000c000030300242d250440741b410406460100c03601038018003000c10684808540154006009540d491b9807800088000e0070a4004188542601006030190741082c00000381421032541c005407107540140041c801054804031705070302a480480300701e40c1aa001d850404902c5844140142440c0610500018a814190001014244101000b24041d6500401941d103281d09035845030020740001d000401300842040544207048060f01150380b1341c0e1007039610208003602c10445562100d800342ca491040080e510100010b440b43c40c2c4001000e20380d0603002400c1c0b200003007016203070f8035001c0300c2c0302220b00c280740840700c0d455080407150750010308011617620342440002c5055036030710502c1c2d0440c2c60b01c1d100304103414020350700600303101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 891629262 1250 891628012 891628021
    0x5040b090112090803070306050307150219051504060906050a05160309030201020c070b120c0c030313060f0c050c0705030609150a11070308100b07022b0204061215090308 75
    0x1074031040d074581040c410960307070f182110100322050302562080c0e00c0d55502092441c00c1506242c2050b80c140c0c4070b844600004805180307081e4002c9446042c0e4030300046200c031041d03c0c50402502c1c00c80c83c5c007043d40c0c103c107445062105010b415000310403aa8000c800601c02da445040b0210201c0e102210040304c030070b11682c1506034503071007a0019041075020388009401c2a00d84105241040510340c41030524071000120803400d00c0c1d02001803580903040850301418244c003103035034a03101c1c4070007800c1c15004040302120304108070956201c202c4019440008102080c0610b501619a500400742c6038003030720079400005014500010007920800500d005062104100007031440c003218040d0000c0c1113280c0741c01d401c1d8003041c200d00280080c0307402543c40320242d00303024074000003460141d0020b032500c22081040e500903844001907681d845a0f50040d07912186180d070b5110891070b100c0000294000d0420000103410f81d40b10540058182c0642e150360a012070a005070b00803109601c034024041452000041c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 891630512 1250 891629262 891629267
    0x61d060702010f18060f12020705251a04080c0a051509060d1a19060e0607060e0703080c15011802030c120f07031a031b03030d060b07030201050705040b0901 69
    0x41d010706403e41041a8032101d42c4404181c00c00c1d440d00240000740d00c00c0e140c804819881908111640e410680445c070340155521410b403a400d01101d421800003c8152440400550040c00c000a11000c00319054072280004120381c2035110b032003150964402d2499011007480c01c440590205da07802801002d92022540110249800410109038044000e101c070b42000810750103841040d00e05d1401c10b121038400130040000340442c404c4403482803204036100740159034021102003110b1a04462240d103508070f41c41c005001d49520071224801c1d000701078001040102000140041440f004207443c0100c8a01100b00d8803a002407091051852041c3c1040725a031000350f0045800c51149212039180003e401040a9103490a4582e42c006640313140c10011941ea1520543e620000c0510501030b0380900c080009945a503440406281054041d00e841290785d010000c403a218043d010092000d00e40c1c400c1101007e41040005501550034400080c50051058040704c00751500514803a0604800a004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 891631762 1250 891630512 891630527
    0x80109051801020f07021503010b0a0e270f1f12020a2115050402090403030c030b030f01021c020426010605090910060b0a170c1909061d06070201 64
    0x2510900704010040c082400c00030700040c40c6a8501c2a2050f5076001d1501c1407100c1c2e10341060075480c903004280014401e20100c0002c4811a104a1500d243c07502c2c0c1080005203008450380816440f01e5115a18900d86444109800e20480d500100c0005555801800390403d803650070203618041d4a107241440418000080e980f400c5001038070096003541c0303030902c03074140d4106200c0303038604410b54001e080100100d250078401c1280c0480d1040c003071818a5800324141d8003025200406143c0c5a1150a1078644280e000f96400071b4001c04031041c0c881c0900e800b50003540b08540c03481c0c80000e01003490318441d5550080318111400c8052209013030703501c4078041c1e14080c1903c0c0150900d540360a00001c0e00d90383c0d06a0709001d450640d01030800049102458400c840303e0740e00803030000704144894150107410001500402d24158010800b0390342d0300c09412001c0c45806030054030444110403506003244e21000320800d0b0385050311103410300c40d0f00794a03214039418003100c00e40c0e20600400034100194484e071301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 891633012 1250 891631762 891631771
    0x3030e0d0c0b102106060906060926120c0f010905070e0a0219092c0112050102040801150518060d20030d0822020303040323030a02010516050a08010905 67
    0x200c4140f503901d40c4040701024501d01c100604400030201d648041c486a44500d030300604101c1010800c8030300e0001d015154201c00e104841c48085007444a45c2075003020128442c1083d03002c02030b40d05c00c1107403036002c4c106500a030850050911070055080810501480381078072542d00031000780303600c51420b035000c09446001829035900c1c540074000000480c0188401c0389009806032202d101c40d40c02e11810031050200c06460040220081c94021682905012924150782d501900100000001e0030311034060300c9698012100e40d8600341042100240f040d61541c2602c10881d411820300c0d9441284126900043e142c1035400003170544141e0010303001070f01c600c46405141403a00390010440b40040e09120380760341c81030f001c20f041e00200080300b410380c5c41045d01c00f054050314103d0700716070b83c001c00d54038022800000d11000603070f05140b42034400c071034500c005d214200c001c9a5990aa14800038080d000c2542d0203800d030556482c02c0c1c1400383c040c10503906240c40c1c0740c0d58072880e03a2802c4543c03006898044c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 891634262 1250 891633012 891633031
    0xc020a0b090c01030c02062401020a1b0302120d050a08070905030a14011104080705040c020118120e0f100804260c0705010207080304121a0108010903030e0d0c0b 71
    0x2000010180c214041c41510900c01802240700e042c0c00140c01c0c0d544103100c100854000b0020484007202c0307400758184030081f0300345110f40301a6400c010b030f00d4282450b80142200c0c55025442081550001d61401a03038400d80d030507801845607030f01c100c1c0e0342c01080d440403022a405009410286102d004440d0744141103140c203e15960b51180440d04040c141402a51a00e01c03541d09030041d450240100030184000d0948a0f29091a02401944544503400b23194459070301c0700c0c0c4c0b80b18824801d4004503486c031094a0490542c0c0020f2904050440c40090164045520490036481c5403605e0b030090b0380c4549010740b4401c1282c400d807500f1201404003c0080741c54110300c9642c6042081c403410a10300b5070304814403d5130381e201c2c000d84003407610050760300840c11035115503070912800d14088103503022520101600f04041019103404001e1088500a9031140d0300c07030100000740907205400241e000c50082e1000c0242d103508503181a181e0940c90680c202281c080d080760000181d1621035541e001c0d0414 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 891635512 1250 891634262 891634273
    0xb0109020f0f120703060f051302070c080613050c0108040f0809360603300702060f040e0703090206090d0503070b0901140a02041404020a030213030c06140309100c02 73
    0x90305905000d80008481c0f280c1000400108100d2580510528004d4411030389000100f500c1d040010740c1170b40c54007041c0c04100303801040d500b04129241c451200500405000c0e00d00c13a140080c0310800c0b18040346001e40780c0d8824036030840c525500806c615401650081226140c1d40040d80302d03c0c07001c0c2c0c00b00345501c0c0c020185130071181d008040030141c0c17001d01c040c14801214948880c5200100070710007034009840798008500d00043c06203100c3e242090080b51100c19000d28541e0150f500f000c2c025a00040c2d004000041c2842d01704c02c10343c004109841072200210a070b80c80e0101c0440854003c210025000001000072450342c1c6803101348010303882c0c443c20480e40f6151003079a403c0310390134095a00c1c940c40c3cae45441883e80000c20b1310440781d81c03003484c08501b141002d25110440c4800f00c84010010f01841c1d0004e12404100e200347c0445440041102898103030340c2d500c1c54a0f9a41d05480d10a03400003644500d040c4215190702c408480c0101c00b1a4000e01c22080d21480c4203009150f558036980a41c400ca = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 891636762 1250 891635512 891635527
    0x30e0a050a0b0108120c102706060905070e0a0e091f050907170a0611040e0f06031011091504050d08030901051501020a120306080f01090c0801090b0109020f 69
    0x108001c81c0194440d01c0e15410a500d030452070703480e00603c12440b0a00200a100d00e25204200055071003441c00d105402054002c40855005484035400c143c6400c05615881d0503000d1041c1d9400000840d0300c8580100440e58419000b20703030002d11080316950100d82e0540801c00c221540030b0141e0000550801d03601181a4210211003400c000364200300000c3d151020400d110000b0701128004002002c8110305190b14105010780790001108010b0055584000640c2c1c0f200d655004e807800b800d445100d141003803c00d1450090303001b2007121414440e20a207810002d03841c2c00740c041e2814172440d20310100e0900e21000200800405200052140004240300000f0941e503020030b10310b041c90090304402d65908025403001d0035502c0c01840d100c1c000140c12110100c13a64001400d0181c1c64101016555803461501d0460203000c403580300e0700300c0303124000791400b540d9011352091003d141310303041d40d46040b940c441859003a41c811900103403404400200400036007040e0340041445580918169180c00503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 891638012 1250 891636762 891636773
    0x19150f091502010f0b0a0617130206030703050402040c111002091516110a151d0603070306060e1e0904030c1e021201060e06060a02010f0c02030309160b04030201030e0a 74
    0x9403070000c801070391222000300d40c401c0302e4490035628240a03906142120b00b45280a010141418440d5008042c00301c005038100750742c0740700c22041030b5004005650360f045c40080203001c0c01003940d05a205500d4101081e500c01e004c0d040071124101d030303800a4885000e401c00ca040081d0001d0355841d410000030687d030012101c98000408032602a0481a40030301e10360308002281403400800140245800d12080c0544040039000e1700314840c1c0c4d80390402c0480d00e084544448841009c03016608040f011081c8034469030580c00c041d09640d225581c403011121828100204420200d925090340c14500301c00c54002d003041c0c0a0f40c2e6001d40a41481d42080c1da050340c0310f40035001709411075164020010504401c51a150740b41402080051000f44049820314000c1419060045c0415224240c0020742540140c000c3d00440d010128001042008003071000002e0740303030fa0045030181254050022698200340942c12030f4000c4c2c0303000c40b02c800c0c240360031640158002c2041e0040112103100d00b0304000000350703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 891639262 1250 891638012 891638039
    0x6090a030206190b13020a17011a180415140303130e040f120905090601020a0b0a0c0e03010504051b010207210602040819030306080705030a02040f0908031519150f09 73
    0x5170b00714801a070b00e183c1d07000010300c131441006d581800031540704010400600e090b1030031b107140450343c042540d07034968850100c07070364504c034030300e840d40050030103c0d03810240c08909080f034201c5000000070f4103128540e03410581c881c46081d2403441408032481d0309214088a40c1c07280c9502920403503981c000b0000b41c2d01e130705102100b107903c2c15002510410090240b4200382203160b4020400b030000f1f00f070103c1d00781d03110211800002c14800c403903030b41d403031400d10921310440c2c035501c25a0018000300440d00b130605050b07854500e50f10311044070303004480300030710b555100140d860112900c442c1500c543c62800400320394203180c04903042d03603840c1d000c0c880403030003a90034840d004003811402c510a440424070300d401b900f43e035841e50100d40181c1110328208001e131004100c0b03c81e200d40c1150000780001d05400600300030300802c04003401500d400300400041d21160344c815981024116610380750792030b07180e940302260300301801884102228040d1182c0514040c0c4032241c4001c08500b000b91019855015114426 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 891640512 1250 891639262 891639289
    0x3060102030912061b12070e0102030d14060405071704320d02070530030c120301030309081605060d06051905040501090212040210050f0d060806090a030206190b 71
    0x541080017070150a01c3c0e44038000d0150b94410340d2031070401080c002040303070400d0300603d40e80034083d420030000d9a42e0300c00e01c200c858409100d01c040020074002d509101d032204080325000e02075841d0001280d900c1d80150656145c84140070566401942e41c0d6031402e00404248085003407080707900610384852185501900c111022000007891585a05000240381549551205001e0082c184203860b0b0203a40051290041014605081200c550b4a118038138610400c0003905040c002c10780b410215180e01e600a604a0380a0350701d88140325100c02d0a2900c3d1403440c4511400c0c205004030800c50340c10010050320307141150803000a0506c0e0f81e00c01040301124041c2c0c07031881000780c400003844a45040e10500d40501010441141480141741d0081c1d80e10724040c0000e8441c00d4502511302185110304100c0f440d02400c41d0342c581d01d07401c404904070090807141c003d00c3c4c524002d43c400038280074000201540317031a03050f0703004100548070384003007001100c41d030340741c22f1201502d0700900219521800400d00d9076 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 891641762 1250 891640512 891640549
    0x90111151504051f1e15020c0102060c04060503070f030902030706020706140c0d11120a20012c07050d0803041208040b0103061d0105072307030c08030601020309 71
    0x203040c20701c01000b04403100204401c0786600740840403050107801d018404250b40c0000c0100c00380010801c0034020243c01d99101000510b03000341d502640035030208103018008000c0c0c08580407900d4117030a07055680200d01400002620600018001911880d6503003104d045500740065082e81c00d802003800c000503500311401692025100f00300740c40c3e12034a91030385a11100c2d4502c5c21b1850b00e0380440d496400945e070003003c1000119011508040178400d80000700c01a82509030386461414002d0128041c030105800480340c0f40726142a03000c07040c0107000c1d01004101511100500a800c07242c0e00608a0041c5c034090700c1520380205068a0707a80400161714003805940b62245028907041e0010b903118001d001c00c10100c4418400019405192a4192039204101040c402a16100850130a00a0307082c035110b0760904050241d600c0d00441790300e50844030354419000040c450b443c040aa80320b43e004c0100055018a08900450542c0000e560014014030540380b900c214800042d4004960320901d015 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 891643012 1250 891641762 891641791
    0x60b0d0f050f0709060b0304111207332c03070f05041802061b190f02090a02270406030203070b12070305130213110408031b0604050309011115 63
    0x44000c000c1d0000801c1344ea00c0c00e00c10300c3d0070261400f28500025100400700c600032a0764400c242d440c80403090146241100711051581e035840030314200d82041071101d4140c4940500d00c25084241d0740344980c2e032101a218841c4404103000d0480c040d900403000c100003480d0818a245599400f8002c06004015000c1e11880071030412040000711003c00c1d820f40081111429404c0050f01c4401c00e59008680038103050340c14003020450f80f41008041e60100b8147c800421000080044000444840074000c0c0c0305104d6503901e03000d0503012889040d000080741500b2003203a910403500700781945101c01014101140f55584c950203e0304e80f43c1d858100c1e40300c4840105428004220100041c0d90050741d81c513061102c0d003030903101d80c9000240c0c18006030041c28100450440c108a9400c05100d0790801d00e01c6a6032999602c00003a105e0704261484050880e010042c00e5005100290081c01540c0007405185070019100042d40c11180c0d140300c0300030341c0c014003001040150400c0381081c0718001c1003606c080e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 891644262 1250 891643012 891643033
    0x106113f0301060e0906030c0109062001060e1504060602190201051b0715030507050a05160f03031d211e0301030602090909240a1e021206090c07060b0d0f05 69
    0x1901700002082d0034000ea00c00400d08015a074490004022240d1030708201528000381100070041c080c01e80b400c0c40d00e56003804000a00100358603083c6202c0c0710714929103a0180c280304d0420043d5080c5119800040e4408a0340c69100305a0f0b031600300d00315105050051405440501c0c00d1801524001c1c100d0042d080b09504006440080140c01c1c03220f0410300c2c00308283d190940010f0594020042a40200303d0003207014240c101d001c6109090381074002c00b45110506007854003d0190140151620080e0b0118030a580400b0b00014010b0882c01c074882254125002072460341042d0308a040fa0000c134a00d01c1c0f0301e0381c9940420030000d6000e9406050050783d19089001407003d00038000e006005282c1c060585090300d0039440c48022090241a43d0610083c1c0b00c16550740003400080c654185468604681618801007035030003803021101a8800c6501543c0f55010411044400c0329180f010240c1008500001802d0f540000d01901c40184000000061341c0c83e00d1600503101ca008441e594040c01010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 891645512 1250 891644262 891644269
    0x50103050d02160e1302061903060f0302060301090506010c0b0c0c0106060503010e0a0e0708100b0a0b0307050703030b04140106180801020c19020f180106113f0301060e 74
    0x707460101d00080000108a09809a000a80d4801e000403542c1e80000301307840c5582d513100e5154490b0000d041c0742d01c0c0e0010340b11003e0300360301c1c094040707011070f02d0721800040c1c0039000c1d8054004c5a4006000300d00350382c42c184641003e40001401d4604101d500b1105800061605403404e0003a01c2c0c00102c96110825020458215510f98001030144203080c401000a00d290024050b0302003110718010500710010707412186080c0d41500020828020f182c0940b06c0d00d0b10070350001b80c0403802144e0340c6a145030384040e480740350f20080c0c849000256040100701c0110340280c1004104071000384c0300003854168207120400401d420380240001505651103424004421342d10500a400c615000718a0200c0503c0ca043c3d50710445185074910001d65811501555101440f91648000c0a0040e030051255031000c20900c1109029074400308030494602080350314006120248049c000c80b4038800b400c1002c42d03180460325074003030143d41341042070340003181c00910801650080c081900c44c00340c41ca80344001c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 891646762 1250 891645512 891645523
    0x909050a050f0103140a0c1e12050a08070f0f1a06040608070909062405030d0207140d082206090b1905090604081203060f09060f040c0201091505010305 67
    0x804011909100522001c07840b030003891411254004211020800c84000903810580403880251007403c071403d0000b6556a407105032081070b802d444201103074075100ca0b040d0b00254040c0300003605c83e502c07071174031100003628420007462070b68098698031005100c1aa510100030702e4281d41110881c0c0e1480500040584240f00319400c2501200c00348007007420001c3d915078510480c4514240242c03503403443e40074428940e0207615102c1c0d442e03420142d0220400d0521030407083c03510850b80684200900904a2072011030b010701564001c1c4040c0185a0491040104100071703000c007941d904204000260014074640c4500c5604607a401045401a20f0318002400000380e1364060915008100030000c07000440c9103000c40c41e100e42e8205980c4960111020519600450700b00c0d22483c4201e4000c8412401d03031902462103018110b032044000544041841000e140507203116801138800b41d440070032490550481107101d0b0152000003210400c5407144104c48405030b14103500706176548014024400c00f8400c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 891648012 1250 891646762 891646771
    0x309090e0a03090510021b0f03061006081605040303120e01090606031205040308090910080f1f110904110d09080909090a2319031d0f03030403020108060604050a06090905 75
    0x50805c52084408006511980c070080036070840d010701e19001c1441e075031744401002902d801070101c07402d515107000e170310304240350758001d04003c520349000281d0224080655058613442e540c0d281380c2424690b540a079010481804500e02560b280c200306401030b9000d108054407240540d07004241c151031404c01c01d030042601c510038000c1040c104414000318183e0000c4841003207080d2440000d544d6485171a00940740203400c520078501400b14104810100060302988610700048584128030401d90365070300300c1d45480c0501040c024248000301081c078103a804013800c100070304030f02803921500307011400c03c861092004035010f1f54081400b07070050528054090740100702d80e004008400054568207003003d00300009041400003901140c500c0c1d1014850071940b00300404450200004501e0b025080f0758000c0348584c00210003440450b05131404522890001c20b02a01451402d8156001160303032000040c4140d8103d2420400080c0c075031110b4018070700030f007403a1307a400c2c50444c01d0201d800e00340d0f0710282 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 891649262 1250 891648012 891648019
    0x21c0207230a020d11030303070f0e010906080403080901061503140a05040f02150f070f030206090d09090e07080d02010b010206180706030b031c03050105180903160309090e0a030905 80
    0x145101c040000059100441c035011106600b07140c0c80b51070010030003030644880c590103000c04000e015101c0e4001d858283d080200e52901030708140c8407001191602203d00c260000100c9103804100400d006503202900480300400210701310782c4410742481000d10141c441d200003660b8041c5001803803518954190000d0240d10b083c0301c10704242d281c00074005107449001c1c0c4120742d415204c1000707080c80e1044591030400d0014881d1501d07402c0c2401050204661410b401500590b00056010080072440c0fa0b680030854844a038068101700101c4000d14041a0003007a91089413404a01d00d2410014414210910303400401c0500e100000282400b101809040c40b610030750240c00b16605000c40d0441c152151840e000507034510307080c00640b43c58403d00e41c600c5050201240018406e5041d00014180c4100b40c0780d000400e501c052040b543c1e21812a2480120b4105024001d0155184400080002d0082c646810000c0d220f5544008417a1042140c071501d5100034201c104264000e1550002840c00702d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 891650512 1250 891649262 891649313
    0x617010506090411070506010603050109060b1912060302030303090d02070e010b0f0a09050607050d021903021b0109050a0f05040c1e14250213061d0703021c0207 71
    0x880454914002d1034005441a0744541545006140c05001d403180c454105040396519603541d140507005140a004901381c3c641030081c01b003030038001d1000f16001c010a1050365140107001c014102d403060714100c0311480c2e05456910000c0965410000f1b9405042e0107405008c61214209010b481c202a541c001c100c092154001000071003203040c2a54010703002e04040c00e64502040c0c80880f060140ca0b00107950180002c5100000d00a00080d03003c04034455800b1124000001da1b180b01085044d0400180160703c02c0700751403034003c5101c441c40c00e0844181440321a0544030000900c5904980d0071411120711402020019480c0c2400f54041c800d0540c1007200d255000c08000708a2820741c0d0007520107001c3d0411060f1038240102c4d080303c04402d01d40314186e0781ca1000140706424521910002c4e84240000144803800d41407030300c5414202c48504d054145800c0c01208c00701401d5a0040c544000d040d801e0003004105c01030760700390306000e154480005a0301c00c010b160580c03046554507036111603001e01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 891651762 1250 891650512 891650519
    0x40201020a030309030e1e0a27090204200309060c0901050a080709031212050a051012051005070804050613080307051c150e01140307090e0a1209061701 67
    0xc600078401c15018035000c1000441c03810143c0752813001e0f03180c1e030381c002c148080c0030800540100754101281c039089030240801990340c50014400701d840050142c41d48440750603134188040f15440303034070700d5880a000480c06a00e0001703d11008080c02e8012080c0741e50000030492032040620203aa80860b60b412001d060100e100f0008040b802400381d0340081c0001400819200c80c021143d450056502680300610b2401d00c0400500c1800c039444d060100380c2c140340201c1e02c40c081c64050395220f0f5602e401211407080c0781170120404800d02c10800c1d680d83c00340310284c1803841c025000e081e02c244200c0d1541d29440c01c091509170701c0d20000410086040c10307903641040c002503103c1e04480e00612185840c2e52070b0b200d400110102c2ca03031096044201a0301d4050403052001d8848007103030440c1d242d507441d02880d03a030b80d1441400400c0c1240340540e045c1c00c011410302180a044d0700c44405044028101c989050303041d501c50114072929500390740402e10b085402c101c01503000f0380c0020010044000c030b0445525 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 891653012 1250 891651762 891651767
    0x1508010810020d09300c05120f040b0408061602010c0c06050712090c050307120510050a18060603211d01050c100c030f0b0906010c0213020d14010509040201 69
    0x602403580d0820780d000600219104469040644241d41110003030031540100305180108842c2a40c801c588842d81050b455038860150425203481d076040f80c05050103000b002511026940001407242065200f8040031603240019800380003d021a40001d16a178101840000111442800648116814410920540c0b07a000c081d00d004954082000300c2c1c40c2c0ca40e503c06a0b035508054009010103442d102948041c04049400c0008564050701070760003903504d44100c1018000005000380003907001450785541c41d61158001f0b64406d800000010320300402210b041d82984541e00c068445a403604030a0041c441e44001c00b6a44074007000603240c1d81508481d003d44466078450700440000d8104407070903e030764020302c1144c00c801d40070b4050310712200a21066130003c1c0004402c000000b4a400c031213100040070791080003612000102400850359807140110303102c104030241203803c040c40c40c91410070060940040c3c90342024581000c51603014000c1344402c008016403240b1302c120f9800c010700c000341c0d8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 891654262 1250 891653012 891653023
    0x5060a051806130e01050f07020609031c0612110a0e010f05060d0f0203010608011d1b03060d06020a120e010902060304020d060209100804050f061501030c090b0f0415080108 76
    0xe54102214182d82d51000090074501d01c16400d1440307039040507159440504107500082c802e07620b44021005645131800201c0e41d55004a6621440c0c0c0e1040013541420400c04184022082500001080701c0307485040398054040f82c2501110810074442c102a16460402c2100d0003070100c001c0c19086030b41c907003042c034266203280d40b02c2c0381d01520000880b0a072180c2582c218000021a091066589594541c0004c1c5100703000d100d28a5a0b018844000d128096801e0702e0b02e015016054002a451400c986440150740c00580b05951090b101d000034000100c04e400501010300c0561038154580303400780203000a40d444404074040c0d69140046850059403500d003030300d410940644024220449070702c0c1250080c841e03284103d0f072000001c1031034440d07035503c000040d00c154802c4003940d194500499049596000580300130400640241c0d40c0c0c55194402c0d48143d420b46182d150044c0d81c0c681d501c6074189298403131200c2d00c01413000010240039480c4521035604a9039803925040c10150300d005a51912071 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 891655512 1250 891654262 891654289
    0x10513051f0902041817070203030d0507110d023f030c0706091101120506150306060d060f17150402040b12010c080711010c0e04090614010305030d05060a05 69
    0x40180203a4078150340c010b9110490701c2c1d9000c0c1c001c000303c0b503104c40368074a00e41d00803d003210400c03802c0300008158907210301a03800844d03025005604000c10f00044001809001f4000d104101c011503500311007500030003243c150080e00ea00501400c05800503c242c0d514444c003104005102028030420410740c4c2040e4496164610135910768407504c440c1500c4e5120f204044015003040c0c00d21110b8410701a101c5501502a1000d0700c3e401d992141d643c004d84203807081141c1d1076920504502e080400d11300e2041c015a4401d00081c0000c0c6094403001000040314156048104038031010310301400405620080e14080340c108100900c1403401c011910b685600d0024002401aa00c40e81100d2440c0c2303c00919040c1c1c00350b00f40007805030420b08080200300d0070048500300000351400b142401035810601c500030b190341e4a035680035010140ba00510014085032074048822554448184018403c40e45286002e03500c103c0196a4840c480140b04040d01d1001e40045d00c200c441407000c11195582c40c900c0c9200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 891656762 1250 891655512 891655543
    0xb040b030a05090a0c061205010927020f060705150105030a0b150a09020a080a0b0a0609061107080604050d030609180311070b0d0608060c031315111201060201051305 73
    0xa40e40da07061035003407540d13110005090194092001c5803258000e102101c484038102403c012581e078440d0b0600c29101c1d4080030340344c0598511401044001c0f4180d40c003a01c00d001511003c0d203011002c0110743d0aa022000564941c0c01c6021170035806150920401e0041c04110b00074404c2028545032116480006010720861012015010079039854000f02d4000800c0350310411500c4201340700b03002d402810121031072880c440c82c11242e0484c1c0d14140c40600b0950300690307512000340b41401e1342940c0915041c002210300d48208900010701c04420044a40b0651007040035000381d03085401e001e400e0b240c19411200110b4104101d1429188080a10725032140d0145025008000c01d03041441c01c11079940c006440000c0d0000d1100d8108101ea0400030031204001304880065030345142d020742500003500d01d0880310f5100c00956001c6807001d01c10302c407039080306ca000041003144211000042d80c004842008050082401045601e0f02031007501d520441030421808d021101d541d840307444042c0c401101d0203 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 891658012 1250 891656762 891656771
    0xf0c12061b200c0604170c0316050f12030d0e0d0206040201170a091a060f01080c030105040b0a0f0306330302060a0306050604091a1509210307060c090b040b030a 71
    0x10b0040c10009450148006040c041d541da4480004000442c428240b00c0d055114400d0010624180010140302c0300101350042610309082c4400c20040c489180c158036400700c914210444012000d000500c9941c45100c030004569411240340c5040035400e440c201e0a40d04032004100150360046440341d25807000c080340c40d006a031400c100b14008c10005601500d0b40700301540480074103080550140c040c01044074640b07202606034004440d00e40003259520403060b01403004002e28101504116401140241301214094403440600401c11540d801a240c2c1d9841d45010444400306000d150b580400751003041c1401180203820b81400d22441c44024040c030f400180346540b652080d4418000383c00010805540d5658480852015000c005248500c081403080007010038504102d42d0210683c0310070f0090700f05030780801041b4080d4000c01e01503898010300081406400000d20040c0181032080d0780015040c401264003c1c2848415001880805401c210a01518031007900343c0f0b0f4419101e140114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 891659262 1250 891658012 891658067
    0xb1905070206210405060610090e060f1003091b06050a0e060d0e070503010501060504210312060605031806130b041412030414031908040f0c12061b 65
    0x185680304400f42c1c03044640c404800603001524000880e80902d00a000b1501a5100c040420010310300d6030704404045011a1002c00016112180007a403046000f4000e81035a40d112011408294040301c0540001e07946645581c01c02c40410142600c8604040021200c02d0418102030264840c047c020028008484252001ca03510001100c1120050407010320007410034901281d5696020300900d0310950820b000418698480c00c01c1d20110381c0100010b1f081c4900b1070714000282811280241d04100c1d807000c04080343c04a41c00303000001c04543d5120b076540d286c201c0c00031111040326100c2008a40110b003d0040410230344041100d50381c0c02000f03040c05621503161185801d038000e03045103400d0044010541c018418800914810340c01010002401c800740000700740c803440b680340f801490340584081d200889204080d007a500030710981c0c1590042d0001e4a81c0204508560302000403d003001d010942040001c0c010302d12800c0040c0c12051103452003040c00342c0b4102008095061050112a045 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 891660512 1250 891659262 891659269
    0x708011406210f0d031b0e09040f1b05010e010309030f030b0a051206040b150d0807061508011a0f06030a090c030b0f0703060e040506010b0a0302041a0d060b19050702 73
    0x2601d00ca900b40341140c06a180701800503032560002e12107240405d140501c2900e94203034401301e00000154a640d411011101403080006407100500185e801c150483d10460014051501b50040082164428060949020001000c244410425a0406040404000009402c000c1c1c40d5038400306400c01181d0340c40c3c8100490001c0d9000d03841550720021104501c501082c000c116240142d00030b50241c80150b6508240c0803954980e000d030f050300a172903c0c05040224840c0c03000f07400000c1c072548001c55102d04903c01d806035989540c11070300f200c0e591091914148009200b032111200d1003a682c10350942a8680012a0380c00018041460340da102d40100d41044101c4d43c0321005136600c48003514041c1080e1031411040c050848800000c286449004510640c0303201ca0107103e03580c8080204400d03800e01c01040303c5a007221003080c0174981c00384800301e480c640d40501c945c920348000302c0d410f17240e06d4504004c0c1d09803006644040b5041504100b51a42600f0302c2d00e42c0b80c84001c6d10704086540c0c903e00e1020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 891661762 1250 891660512 891660559
    0x51009050601031103240618151203210a1407080115030b030604060b01030e06010603022a0c0d0314070b040c06080c0703031a0d1109070f05070b13060203090f0708011406 75
    0x181c80d03c5117002081110256200003194040c2c4825100200102c2035a062b1642e00d1144050940021000200c6401c54200c80b83d840355114a801740003089000b100040f25441c0c100698403803011550f008010f0009030b503105200c20751010719240900407a40f448005c80d8071070b03101400250040c2d8880b040800680d0081d0054400b0b04d910000301c4000d507954100040007500894a00200740400d0003500b0703c42c1320040c0c1c1c80c003a001c141c02c02500107040b00390104054410600822001d1001c200645032411103440042c10f0000d028151f40c031060301c1c181c5012442d1110f41e810510500455030244200c5190060036601c25952604000813441c40d4850303110400301244040380c5d07001140e22403800c01c210308254070b80c403601002c0da510755142c0c640090036a080c0358a403209000041c030500407d000705041e00540307500881c0750364900160b08241e0700d40c042030364011203201205034001400c031035011404118bc0d800070803d50f4020070920003107664585000401410301d034825940c9a01070301d80140040c14 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 891663012 1250 891661762 891661789
    0xc0a0f030b131205190203120a092103090308011505191b0c0618051f1b05030a1103040305060103030509041d06070216051005070510090506010311032406 68
    0x2052500c210403c000420136400f003040c002c002a1700c11501d0b10078034000000c2c1c4101ca00700030809001e030707940c006840000700740e03101050780e43c03140e8440d44012003107840018130156079031564041030b48122824003410f01d00040e48040070019036030040c000100c0d40a025a0440001c0210460800142c004100d4a2440104500580c0d050550310a010410382c118003c04984d01c549600c52100c40004440300500c0701403140a800c5103458111800b4104040c00b1860145500e042c5944042d00c4081c0b07020346900d0300716040b2441d40c0300180400c04039801100b07001082c510040110b280c603085984554803100d042c8030080c123100010644038519999500700c15081c040c1855903840c1124020f01ca0f40d44c1d40e41c180d4094000d8019030900364400c011008685050f144d001c5c0c251505049110707000c0f5465403148006a6103030159421103032140e001801803030b40860040004000ca9411414180d600c59884802c140c8240d1051b28038102031084902d0f603c410600c91034106649036034174000304803c880c0303944 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 891664262 1250 891663012 891663023
    0x40c12050f060c0702090a0507090b0f1201031b0510121d156d020406060516030e13021b0c01020102042405040510050c0c0a0f030b13 59
    0xb401c1040003a814009808803030700031076010402d03807140e122403c1212401d903031820020b00c0c455014452442a1030007012804e0301c1c421014a02100e4403c034841108081e00101d6040f00e05500d0751f02d11415880d001703400b45c40d04841c0440c1400481001a00c200b420088004030742e5100c004006040450071081168140008281ca00300c592459607194951004c0b541034021150041d0641d483c108034511a4049005c4131012402c40340c42500707400b4a03038850b80b21054a21103010014a20080001160b0004440c0303e54a0a5509194810001590b5680d000f09080040a00120302d4201090020405407600341c20f0400c540407100c400701c0d1200e150885286a414000601c3c5e601c44003007070300e44102550941041c1d80003016150012420b0344200c3c0324020075070464014003030002343c42c010102000034903802c1c110300d01a514004510740c56070f030500c0000817170f00c08503a15044100034003c02c0304807a01140c20001403030804400740d036401850700020304101c000000103a50f905504200609194208 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 891665512 1250 891664262 891664273
    0xe030d09030f0f020714040203091c021b01050703090e0a110a020a110337050a0c1412061504090614060a150e04090206190201050717040c12050f 64
    0xa080c0a000c10300500c0030ba070005506810592800351020502c0000d6a41e084054a5036582483c10030001e500042c0a00484e40229035004054245079048006101c2c1c264001c0d01c640d2150f40748030360310403042c0181035060120401c16400003950003084442a1481d441105503030f6265005080014403013091704c0c0591100c0015401c45498000800d040e12910078454601400145800d05441c0c05501c601a40201d900048103030100384201c801c0c15182c044640b80c16182c86494a441d440e225840320142c03040300d00c036141800702c05911a50302c0032f033800c140d03107049150b60000308059840134010f04841c2c82c41c03031540705901d01da41c85401500d1220303040107040c400074403443c840c8940300500799650740c03040411071000205c0c81d0200700c031003c000c10b103920345100c12489081480060201418200d80c440c00c10400f00040d0260700d405a8000c200030f41c00011540707071092000c0c01d00c1c3d40110f158440c005540d0108800100307180d000707000b41c17800304000014000305072814a00d4640c54003031120346401007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 891666762 1250 891665512 891665531
    0x90303061c0f0b0c1c0b030a02040905120d39030e03090a03050607020606010212220b0a1206050d020319060209060f0c1e0c1020070f270e030d 63
    0x913000a41008200c00b01c020352442070440d140e00454085164164250f000003040300d000d450035602810388140640107507183e00d031224104001c154440c079400006207540d000e00f0401505207078140b940c40346a06a5a9400c40b403040c0e13081c601c454000c6c03041c1c020152564042144c2c10414010b903450040081c100c071000b0b075105d203801038646804542c008014826403000401c80e6200103225040100c2d070034001c1d031902d40d8120010f29001640070a4940c004a010000201c41094000400c4041500d94843c08800490600181510380c15800702d403141048072314003409645c000c6080c0120050301c03100c0503055030039031030414003a015031485036610601c04107002100b556240003c020130050001518204413140c40c0c80041c80c1d0f040b036003410082c2d008207410030035801e02c940d400c00954038500f05100040f141800c8980080c008001030000d80d0004002002220841d0311608041c0509810101d02180e00b00d81010130550aa4101007989486240d90b41c4585000d004494100c0319400b006d00c01140d2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 891668012 1250 891666762 891666781
    0x20a09050915150705070b030708090d0809120d0b0a0602100609090b16030906021602010e0d120c0f06090b04020112050609011505040509130b090303061c0f0b 70
    0x46a2040c20300030030720180001c2142110b00d84841d080c140080c02e00b10100740014a440b00c503007008000312100c5c0716600340410300315091005135208402960310b42c0b00514100311001d00b420240d150344000e00c02c811040c401c502d500440c034440c0c5078500445581e21000d010314408080c061688405030444400280820187e5011480e02a1507809050500c42a6504c10055017101d0742210040d06c4c003001c0e1800b02c0c900580951410501000518010403941016100e4038105e83c4041d14503503007840d14010110855801c600c4045100d45d0444145001903501d844812034811110307140070410200825a008000114000345841500048200158205890045000c44040d01c0a0f070100703041a504901407242ca00406110301c5001e070000300941d1a00220403c06c51075484d2920038040c1c140404901900c85012040c440c440a612045040903103080072898038201600c5003500b50010010811241c8600d1ba1090740d00c2840b42003000700c0c03079050501507540c40421900900c040407038001c0c04207424 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 891669262 1250 891668012 891668027
    0x30a1502071b03031e02030912030a0e040509030d0b2110050a020a020a0b310318060801290a0807020d0314130c0e04060f0c0c0201170c090301020a 65
    0x34802d10196070101c0c90360010328004140c0e84070050001d800f0584800c4188040c2412100c060218011031341401000400900e035001e02c0e80905000303a0000c504d0303c1415500140d220740d00c0c0d00588041051b030500d05074007908c0707101c0c402c03101d0325041d200c400c09500b40d241c1d40040e204440700c00850940095075003c6080e26004c0e84c0c2442e1592505240100e051211140701302c0c8c140a0345d5400510110000c1c1c1d03a0591442e6008000700e540e40350b0040d9118204440d90f05805c24180c0b42c82d103180b01500036180141c010f02840c1860f65242c2030402d1b046c000180c01641c140e0645842e00410fa25001d0f0050040d000e543d2032a08048a034800841c070351102c240c000760610300807150b980a541410422000c100c00302e60080342c42c1c5490718220804074030982100c03c0c010300001d0203400722030045616212000e441d00026241114a940d6501142440300300c0c900c55041d1426107468040391002071600020120421601c0241550440b44c0109200c070013070004890080d84040c00940d11105980704c05071584 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 891670512 1250 891669262 891669277
    0x30c060c010203010f0b092409120a020315011203030b220b01020c040c02030f090d0c0303090f1a070209100302041802031209061e0d090c03051c0e0f030a1502 70
    0x4070080c2c011407800c103401d080e43c4400b000a08103a01010150190741d4807010300c84a00350130348d00d0400500601e608e034a0801c4008100c00c40040554501030b1044c94036141e000d1100c42c0d540b030b00c0ca0b001400703a8104105070080c2c003901741c50046242601d500001c0c0020800c013a072140302c20940301010801040340c0d004401c04034402d809a900c00d89591040c44166141c0000070300058004102c0e040511038803101074000c00301c020b440c002d0180301a503690400c20300e40d0780050300450704901041208144101d44040540607812840c0003c504c800004000c074020200001e12a1040390001901c0700c05009480d0020b54004105001c011003c2d00895484010808182d00030301a01d00303210301102c0841c0454101c0d60014010528000d140003541603070f405a0315582c41610002c200e6508105481d00800c0c40250041d4031543d000361452030400e150120607003e0410018041c0340300540c182e0000c0c1096011313a81a100002c600038a04000703800c003840103200500850ba492402c58080880c0ea0140000c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 891671762 1250 891670512 891670529
    0xf12030513092a0e15070b1806010605070506010302270c09040c05071707080c0f01050a0b0102010504020a051309080c0a1b03151d030319050c09090a0b030c060c01020301 75
    0x5120036200d621114550400c8180844c000c00e00c544000d003070440148458200c101c105030f04010183e6681d650507002914052001514a19554030360341040c81203a005154a0030310034038003e015603640d5181c007014070000c0d1103a08004900c101125000700f150b00041f4155008070700741e01d840c50b03e403001500040100c83c0107034a00242c10135007074010703001c030b03034400790866450031500c2d80d0418480b120368013681c0115110041441202c1c8080b00401842580c01d120b400040741e14a8034845600c11a410604a903045a050000780f0015841c0c030b485031800e42d01c0948001405540e130b0894800640b41100c0700501c0064005041300707190102055230355156125440200e10208080204a02d03800700e8040506808140840020000c0d1a40d0014a800100c01480c0c458201048407103070450304204c42c40403e00c82e130b480d03007d01c0403445442040d522041e00b0f81c5260070002d8100c04504d00843c001e207880d281a41e183e8262100740c2c0c042015052081d001447d80342d68541105050703010350800c0c8a61602d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 891673012 1250 891671762 891671801
    0x31c09050604080c04090215070c060e1f0e1c15200f03070216151806200102040e0103080d050105010302040e0a0b210114100f1203051309 61
    0x816103440d004030b50444116000800825a0039030400006015800c0e0881e806800c00d0591410040c00704094a0301070b00814068500b00d1411138040c0040d620900968892010081140005082c002503a8040b40040c03400c400b07900620310104070030381c6020024040d1746450300d414008002080349000c0d000005a2018010b21000a92401c892074400c038168030007580034040e5070b41200e142c1d00603640c4250315204542c40002ca00701040202c69641d0040c0c0c504c03070700c1c56a00d0311103103802c810b04901004580348034000d0145004802131060f0490440000d107001ea000e2440c1c00030600750140c07005444134161503080c0c0d59407881e224a055106283c14854542040e000007100e6001e4425a4101c0b9082c1a2102540d0f40d442102c0340200901c004d110b90181040356002103800d020303403104840c0c4412030000210350843ca080c4000130a40200049080302800300305100c0c0f48100b128500c100e076454881104200100e10301660342d801041040c160712143d88200003242c040320f0b00039045420013683c0314034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 891674262 1250 891673012 891673019
    0x3110a170d0f09121b0b010f0e090a050d0f0c0b0f040203070b191419180918030f02330901090b0c030603150c030708070801150f0509031c09 62
    0xc01c0d241003d00140100d0a5042000340e0940034400c522040620351750f00004490300c039550a203004000f038000886400301030030180700e41e000c502c03803180e0400810b0004080d04d4100d0b51b03030556203400d0b030300d05002080450701403200128001c00401c0204c0e80c0c00101c50842d86001c490b01042980c00311020781c400c0c4500032000402c4031a90f411545443c80000c001400b00d090fa000079500c4032403100302d81024200411414a0700c021110b12221040210381d907030b2020300d05ca01c402c503001201d2038000043c6545050307400e200540a4000000000d52315080c80702c40d18180340381c242c0c00c041003045207003008c0f8a00c491301480c01c81c241c2c040d00d00e2950226014811516840085422100300d41c200620340044540854061000f03c2d0156901103030090071116034008041100c04200415a484609200084140b00e0220b81000109500031314900e000798180d07150580c904a0b207500380280005000011124542d01031103036048032110b050103002c4400e07a0302c16050403800d040d0320099010003d420150f021 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 891675512 1250 891674262 891674291
    0x1107200901060f05040603020f0d0212010317040806190e062a0333030106031b12020105030a05040618050a0c0506030702100f090f051c020105040f03110a170d 70
    0x1c0403043c07080d51614107190502d68298025407050792440c0000030309001c4110900418001450b010090b220124801d501d507190580b4480d9412440c0800114280000d001402002500c00da00c031766a01009500c0706d51030035504000389240080c0000310b02490341000880038415001c06900c503141618031a50310800304405186010507608410340d1007c4100403550044000e052080024841d202809941c600a0010742102d4055108507880c1d241509820500340210f451b070760003840255810403e071800c41d4002401848000e02c0d620315143d5038404030307092040c1c40d03200da06000b07401d00e00d1012926890401b25030b6030b6030480b800c88568884101c04101d034100042941c4c010176182d0020100218024880400343c41d4801c40d8002c0d0b03a0b5107175204408284600f8880c603505026902030b00044880f2070006014096029182042d6810601807000282d071f00c800d10116036030140b03002903030010605c50790307401c1c03541011000e411003281d10714500317089d500c00009040452811108120f02103040c070702c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 891676762 1250 891675512 891675527
    0x80a05030718030309050d020103060f0f050102280b09012003090f0724020c060f07050708031309020901020c131a09010f2d0303020c090601050702030a0204110720090106 75
    0x2c00081c0315070806c00107801c000d41000300171841418040307030b45d81c0c0f554151491040942d0208120200c05a400c10071940c061245040c00e00302e2914246080c00e241d900510092003000b80207202d03c1c1c4100004204603402c0d0b101011040c41d02101030094064416803c0e09a042521078001500545140301d091010000d41070003161414a05840f00c500e00710120402664109000030070b50090041a03a0240eaa010042c02040b501d800b00c50b03254205c0d401c2403803406581d03402401d025407040040f10342c0c1d5078643c00040300310b4100f2040075030f441000c00c00407400c090294207513a0300140c001c2895500f0050be504000b00c0039000c89040311740300ca0043c0401203003038028800d0209016060f501400301c0b84458030300e2001e850007941e54044800c03410350001003401d159803003600181c00c07041c8412034516000d000950451024a0564101142c076000240c495580c0d03c4020b00c603503615161200c00444010070354a50903040b401011040d24048109006a1460a07007644501020790020910030700903d017 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 891678012 1250 891676762 891676769
    0xf090109050d030b040207020a03080d05090f060402060f0723010e0106032004060b0307080a0507031a090601020c1c0506061203030403081f0303120605060f070f020d080a05030718 79
    0x3407002c009001800c0e00203042200d0055003080d020441100580c40e640d482600442c4120050303651048400c4003a4210340025000c00340e80c2d007202001c0b03c0710580000709036410a4040740c03030b540d480c3e032407407520101c62080035030041c80d8000a4111400410450301050303100c5255100a014411441c0c0d0f01c20700f202da65010050603d031003620f18101c031500ca015503140c1d00c0806840021459158500d001040d00100c501c03800040d440000c000550303025000e400e401040b2030a050100304043c105002c4005c00c02030015000f46075020000d40d29a100f085030036200d201c0980610000603959040f8812002c65401c26201072080300d011850b00d05022240303a240000c02e001079411a210790b5012109200081c015121402c0c80310350b00720035010280181001107101c1e454000c1c030914403c02501c290354a56115030b10070102030142c244260f6600046440a43d03200c100d8400307000981c07000407a0401d240d10003500d10140480c103c003210340c02a0080d40580220384500d0841000a00c0d40c0358058000d00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 891679262 1250 891678012 891678023
    0x7050604060e1201051807050a03080d2013050a0509070804140102072003061302031b12030c0c09010f03020312070303140a0501060f09030812040510140f090109 71
    0x820040d1a10400c00d0806002c0c00a08030740c0d80180c070f070940341e0030f41d40240d91068620303021401018907100b00300701c00802040191104a806403460310b4440845c01a24501508151a20b0403017050760014003000b80e201e544141010303140d0800c1e4a40701c028100034090b0740e003d00c02c00d0b0008903940c1f0b001500c0c144150039594400d00745e555540d60755070004121a1a01e4090340d001d000f21400501020b41700b2609140d0081c1d100d0b40c411804003090714003c009000c0300207002101400d240542ca0101e00310a20202044604012844030340c0441d81e120f141444d811458000459209046200812440d00c3c400c0c0c111a40d1940341d89410b4035444415140c40025855409600041c413081c0178500034100c81402410002000210f2a4840c0107400c4104c404610f05581d40005201040d0005101d0086013080c0c5440740020341140c0c0c60550700d01c07482024090792200c00000030b0030003030f04005e8007002c031b07001c0c03041480811030502c02c2d842c1c1c28400342c400c0b201f210050310000c1c584d5003051195144494115 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 891680512 1250 891679262 891679267
    0xf221110031107120c050322050d02030c040b030c13050a0b03030a1713080d091e0b1308040b0403030201060608010b161205040f0e09120a1409061308010c11070506 72
    0x160364009a80c00c158125005220360200d5100204e0b1b8140302821402090010202d011044107050303451200490308818071034001040d062004d41c41c00a03400b40100c0d82900d00280c6400c00741d0000c1e01d09018440b8155001070f0000c1a050386800c903030426030040108001c180480701010080640782d006150307107080041d0640ca0742c45007a0814002d81e0360030841003140d503841440d81307031903180107a840420320a690036121412601040110781d0750000c03900000390700f50b00303080c2c10760f607889001392001d0700d000000d002012076081030002d0002160700400b440c0800030707a03a070341c2c1c5d1038040c2c0648080d21903d004149100c000189502e540400c03191300b00450304101526800e640e0382e001e10440741c4410786003009070030704c80480c1c040101d02144000e010ac0c408030840c24a08142d00030316001400940b600d000d042400700e80e8440c0c0d0044480403008000703291050f00d805130320000c0780c69401804800982100141d5000808030010742c40808141007644d1441c0c456440905010760b6014141b0a040c0c02c80b808 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 891681762 1250 891680512 891680527
    0x180905150915040c090608030c0c151206180f01140904020904060e0a06020406020109060b0607051c1b0308370b0103060305010c0302040f09050105090f2211100311 72
    0x611401da03800f40c480c102c0f1444c120740b2208141e044072002d80001e517035a030001400b01102034040161140c5a00c00721a410603501ca01c0c0000c40c080d028111044022140f0800890381076903a00150b400750400d240c40c204003034608204400ea5540b401e01c104162183d80f8219070055050828069104c1c03500a000c54009440f41d5407010000c2c0070940c9038504500a1070300b00750004205000502c0202019400490180d15500300b440c11112280302e140d1207000304001d00000035401040840e10300b1180c06941201c0c09003954141d85007040e00341041700701025480007504058005001e10701594040c500503505400d55801607031071140340c801e81d40740103a014011842c46a504d40109406240c103140100d045641c81d81c840f42520310a514a101007038011400740040b258418440004046001c0c00b441594500384c0850035802010b852007582a00403030006501c481c015401e2040c25003400c140005154290829030008010715802e01d2051980190b0450034070710038040c25840d05488062907160066 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 891683012 1250 891681762 891681793
    0x4090507030b1903020f12011e20040f140a031e111903020f0f090a0b1f05040308130e090609100b0a0b0901020a1202010c030606090803160204061809051509 69
    0x241f00a43c1040b540d00c0b52011140301c1441c3c0c80903858800e0320320004c81c0c1a842440c0c424081c419804005c0740840e4288000c1001803203002210742226070f094203060703a80980002041758004580c0000d050045200136a411500c140c1501031200e40c0941e00c80000c205443c010042900050318601210785044a0107001600e845004108180c20003840c0086071303e03154020404021301154040c0226503225440c1d100f905207100b41c1c1281f020388901d61a072001c10b203040502680140c3c000904070b100c0c0401c40c0c0b190440c419a00c04c028103070f62042c5903010b241c00c0079455500ca0f01111003000b2806104000349045c0410300514041c3c80c40102291046810b00f0140116a000107045d07a04510840305042d010400326640c030050041698000709144000f028042c017515a43d034041c20400800c5801080500804000d13100c2001e180b003c04030509200d400020040c10494122000c40f041401c40c2007888446a80b240e510188104295010288245840304a402c4102c6002c1c00380d410000c07040c40540d4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 891684262 1250 891683012 891683029
    0x3060d060509010615030f05010e070909051b040e040c05120a1403090402040806090c0603160c02010e06030705040e01140a0b030403020348100b010504090507030b1903020f 76
    0x1860b42000050a99940780b0302c0d000007004000b00c4000c2590781c440c6020500080c02094098140c080b065206070038040c0000701414041d1082e1000c942e030b110041400044401c15844650703842a17180e0341c58940b1200580082c40301540d04940c0344200c1c103000641410700c2d00c0b08580112040010308000c100035280c003d501a01c403070081c00d650208010b00c007500d58880c8090710103803071040020035162a080e00c04d9458014104000e81c4a10403e100f000381a2095040324040b6140c149000052201d4601c0166074401d0740707040059008201000700a845039118015004680c40e81c10807203016640e80303400c00c0340c0311100414543c01c040031980501c01c195407500110f801520a1044a00d01a1142c0d4850b0394a810760040074060011060b14032146040000490304203840700c0004010210f01c151010350f01d0108100000341c1684ac4c00514034140c0c01a81502d0080c0040030b002d000500d0121001002130821076500e80c851009404e40001401d0180b000e0402e580e030207804036150440381c030200f010301d5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 891685512 1250 891684262 891684271
    0x303051b1b130603020402030a060612050c0a030c180303121d06040f0c08060c0d1109030d12060b0c0703120504030327120b0a06080a1707060b030313060305070503060d0605 76
    0x2c60f2118000401a2160710081d4072440c08100700241c01030030400e00038150b4401c1485d5480503400d207804d004c1e02c08041d10842d200d049007400d00054900b4008000d0f02c03160100f0540c0710002aa48500106068006108079851441ea890402841c1c01c03c200703490f526041d5a6402034683d11140000d00000e480c0c00341001e1302d90040550564040c0e13a000424135108084034101a60701000c500300401304518000c40d21100b800034a0241808507060220703a480070750840f83d404104545c000005034054690100d00030781040840181c0d20041e0040c0c1d1075407130455102c1151000c81c40054007010502c102d0540301984e505645111440d000240700c0e1255150410184d0082c400403540050070340d40385416010b039640700e508140540e01c1d015a215080b10055885000741e5000803280d44000360014040c640c925540f0b03100181c5139002420303c140207091038003031a0340512002031408141c0903000b88407003ca451a035030a1086540300f1000700ca003070109a452070b40200c1d0b0240c500000a94541200707900c07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 891686762 1250 891685512 891685549
    0x30705100b0f0d0c05180603150a0b130603140f030f0a02070f060305060a0806010f120c03060507020a0b07210905010902060f0c01050a0507050304080304050106050303040303051b1b 80
    0x842c1c0c0d503580014010410f501040300c151040d00c07000c0220b81890352105440c003150078000d0100f403400d003010039210342002d80185a040c0c109800501a5540d40d8041c00d40c07030304058a4010f4282d005d00d1181c0c010b207a18041900e08950803161007050200010b500c102080c010005141007040640c03d41426420402e450303030640c0a09000424015801c0c1d0500000303048a54000c80c0782d04000c17091104162980e000700c5880e4111500521448451076802011560038405c410035100203030522413408542ca8000503c207a042c03905010f055680005c5040305a80204402e24068a400d01d06490002c4e500b12403000d80344450f50690b2802c1640d03401540c20750b015400120b0460015070000d40c1d154014000400c0360000886c1d0000104002d01c40c80790b01034442c2d28100f00c94105080050302c240030051000f002d4140000008040182c290004c1c07008180281c1126241c079100d24000c1c1c425040400141c0000300c440f01d08a0308207000003030b484244030282c5010010907402c0410b1005803551403a1a840 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 891688012 1250 891686762 891686779
    0xc0c030602030709170f0303070c0c0e0a0905121201061202070b0c1b03040f0506030402060c0604231501090c030b0904050c01020601050d0305033705100503030705100b 74
    0xc1803031800114810005940e540c0d140f1070410109a0750884880c0b07020364a0340c0440315054a001002086941085070760510b1801d44469181c13040c15010650030401c8400d0345107080c4000c0018a81108003c540f07d4801da501840440d05204039900443c1d81c0c00582d00340d000010429a805241055102c1e141c0920151070548c113600c5e021140d0f40c00340d5070300004182c00107191203048680038040702d4034040700b07016510341460021410382d100c003140601485100000041021540c58000301d414106002059420600d8241005001c0e00a0007681c541d03080300700c1402042c4468003103044402040e0340400200c1c981d00b8140044000c0003583c01d9007042c15a0380401c00110b565058000d032245208900074602c2034000c800090030040103901081c000e41101c4003010001e5008000c1c3c1e6488000302001040b21400300c00e8000c40c1c0c07200e003078411030514098249002c046440350031040c810b01104400e909441e0f03a44091550300c1c480e0060181040d008800d80714000c4d007081d007151941c07203002890002c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 891689262 1250 891688012 891688019
    0xe0d020301050f0708010b07200402040302090a1a061c0507030608160329040303020d11031312080105130e01061706010608100617042a03050601050409020a060c0c 72
    0x90071640c0550b642d5125801d400d04201a0b2a40301c00c51700c0c0581114800d940c2002d00580d1130120350400200e00b910121040000000c441d2101c0e41940c000b150000d240360900d04107509500004e02d140d41102442d00d110f40b03d01c080d9400c08400f201c1c041440f110744110a010301c2506400280800b504540c101758036680000340000c810002085010146c03110450114a18503003040030034928a110080380c03100c81c1000749014441c1102c22350240e00f5007805a5224051040035004142460915115074004002e0249107214003180d00718080c403c44032888002080302c416941080300b44034055100316181882d400440960304403070540c420074800854026102c000c00441d4810004041d82d20768000300c010014164080c0c04590801886850b8018450503c0c200038801c02c1d003e2490900b200030072000c0f4041003d60080c880780e04208140700c0e4181c000200070007000c03140b2488155402c1c07241c48004a40b6190510562441b41c0d070080038620325520341501500d0f204a0540305903980b000c1c000000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 891690512 1250 891689262 891689269
    0x30c03110c15090a0c030803040c0807060305070e01020f101112011d1302091b0d0903180e10120213090305070c35071e0603050c030f01060e0d02 64
    0x20211100e140700070700030300d4448000d480b244080c0108001e94a9000c0200b05001c1484100d014090b640c2100d4120340c0c039640c0b0f040400c400441030780589038071b2061210000300c0503450350040307014009550b1080f43c0440d4690049030b43e009801e5007810f858001001540003605c995005586501406107594200414440d1018500c6800d0307006011013400e4265400044007959800c9520400b09120100160100e80100781400c6000340b4522540c00c0d0348040d054104110300598014481e0010140b080b084145001881c9504040b0b501c60100388200f408500c18039400846489509604c8581d482ca511f051402c4c450040d080c07074141d811003c03212100e43c0c6a001400b61048050194942e41d50f03030801454043c1d550403565201d41442040aa20000c2c1c100c580487e004442440e40c0d908550707003140310400e0b403e001896010795459900705d04400c250714086c2e0b501c80100c0d10b16841c10401a503403000c00c2002d910007198410074592409006111359030048107407a1001d2000350644d84550481d9020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 891691762 1250 891690512 891690517
    0xf160e15030a02070b010b07120f0507061b0207080111070807030c1a01030c052e02160620030405150309160e15120c04180c180f091101030c0311 64
    0x41c1006540000707140c8240100d007145d0340c0c0102a0b00400d0b5103020701a0300c0f0040d00740c201d6040d65007000701c040792510b14103204c0c0c030549076007a8201108101e000e5507030541c400c41c040340d020f4100143c041c3e910000748a038018070440440f201d4440660f131411107683d54a02465100030800c070280301c030f0781c0d405002040c22004d00300000d52214101c0065941103003000d0360005078130f41c061446140c039401138209500390450514048024094205401c1e64044810b90a041300c8545084a0903000140004c1290303010350500261110004c880e100d5000c551b00c10760300c13446035000e110780001402901e490005103007001940c0c4811014241d80b5003d15034201032000c0c0c181030340140e808400c00c20a005000382d0640580322100001c0302d6030032500c046010a203072140200c51105100e41d54461031480c1c0038109998000c00c00703901c207110f800c0300e544415200e0300d04220310204c01c1c001c40c50b0030325034500408d06100384440c26400c554500c041c15040340046014107400545402010380303c103c40c00302d85500402 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 891693012 1250 891691762 891691771
    0xf050f121e010f020f0403140c03030d020a0305010f060203031314062508010e0a0c03091406011a0c120c0c0a03060f0f0501120609170c060106080f160e1503 69
    0x911550700803111007825550030514242c1001c0c8104201c0c0300d660150812075007160390000403601c040c03445803d006e0910168070007042e01404006460755400c415135004001450031510108256602c0c0c4110740311842c032501035100076030310401c00310360399880700781c4038401151103441c609412441d2609540d0030a007094170320401405011000c00b00c00618403980040f9038800b8500600d1070740c0741c0003071090504c4000e01610708141e51800d80c043da0074840d0308401170064000a01e2282d03520380a003150390b43c10091041000210314110ba40000c0904401210104580c4000a0410f01d00c1000340824907403240090520318460440c0c004007607128081c00400840c000d003000692449042402c00a440407490780c1c182d600e01d803030014006030602d000c5099078141c11210001d0400c80c00d260086c0306034071600380e40c07810384000306980744400030000b90b460582c0c00d142d44010712611145d400c061424010759501d0f803505022035002a02070312485102003165001000b030050f070300140080300010f50040c0d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 891694262 1250 891693012 891693043
    0x40c1a070c06080c16050d080a18020f010c061a040b0121270308010e10031a0a090212030d0c1d01030b01050f040602010b091b0f030705190203220f050f12 68
    0x7c0000b5500b50700862a01c0c0d00c010421800d2100c1e58111003210743c40090004024884d40800380e61142c1d0740d1041c41e5044150354002c408100c01c4a0140c0c050412401c182460b52040d814171002d10060f51141800b240e5106007a4503005200c05880d200001410b0b45103c44410011001c034110783c0c0f0204145210815030090f1035015a55041007407102090703800a0240f062640c03078100400005151681009280300c0b04104500c1d59201d454a400281c03101c00341c041e5000c107000d440501043c0c0f010008280e05007404c0b504009162660030180c0314001c00400002c000410350040c02e071254043e03080b6200c2c005051420620f4004034444200460304aa0030060050795100d8505400f401c01440c041e410003007042080c5003200019104501a214203030081c40c9070038010010903a118011401d60300c25400c0d0440c03401a14000f240000d6a0380c1103100640610b070b00d601d094008406500c64003405807041e842e0416112410031081c00004200d80e55070030b070040ca0415040d6000c2c001840030180c0c11041c1c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 891695512 1250 891694262 891694273
    0xd020d020c060a060803070b0a0b04051008011a0924040c0e030f0316123b04050f220206070f03180f060e040f05040c1a070c06080c1605 60
    0x10400900d0311070001c0c0602d020604d07000341888240000019900003d6014006166503034030110500045c0c21942d600301c0d005800d05091200d81c841540410055507100f0000f040115040205e68a039208807030520742d00320b0801408a60442d0030106c80440c8224a41c561500c18084040460100c545040d04d05000071201d81d04400d0030314051002468401158000b18106104407115040c07007a0341e20720041030503036040c00135001240a4051490304800b4a032890300c5a00164140d650800c0c1101a5110850011402d410140c078051050074020302c8040e4821110340c2d92001020160040300061000301c5504601c080c1c0140d8078075000b0306005101c0d41c2410031050107440e020b8484d454880c1880030f40301d038032030090013a42800c0000b442210054034010011082000c0480c00404081401c440c416041108100c2070002140a410483d00e504e1803c500f020b4040040300c0403406240401090611030b0030041158903c07400d0b02c00d800281590703c441c03402040e104500c61283e5002c03002c5641d038102 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 891696762 1250 891695512 891695527
    0x8092202130e040503030a0518070602060703050a05100e06220b01020d08240a05130b01090b0a0519170f040506061c030c06150e0103020406050609091b0d020d02 71
    0x540c44030001010444003240450903c3d80d2015240c0c00000c000078100d9584000046001da1f490140300110807982013910307111a12070900030b440742c40403504800400d0502c00840e07500060351140c2d174030849130b802203049458101213196000d580c000d0032555018003c1c1e1040e0407011610945070540c14420070703000410405040019043c0725100c2940400e100070501004036145600303480c0d13440031915855540105101400149140d100c54000340d802c81d001200000311408903621880044109881d4208984e0b940c0c4c0001c281071007003130101e100046080c0522510000780c5031022005582a0402102c2c070442c0a0302d40f190381400701c48900c81107001009100074003100303102482c0c0003042501c0d40d4540c0c95030141c08040d02041c070701004042065a081180510055a019425160b0104101041b0039a1488545407400003800142d01c120305e843d00024540ca4403500300d40d03201601912130801507407100d003e0000201da00c4903090141d402003000a003900000e10040c841944025001a2220342 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 891698012 1250 891696762 891696787
    0x8150406150b18010c02090a0c03020f0c0c03160b1b0703051f0f060f0308031e07030b030c030a1e05100c080a0b10020601090c1b2103051308092202 65
    0x24003c00503060145418500c000b60f00e460f214a64040d10a800115032085407001c201d00900c41c5021445a000000c10441034030640032640802c0c141d021012101035882c02c80740b1550003055441500100103003084501c0c4510900d1b04840e9009000d0701c141c801c840c0d0340380c0b900303800d2031110403900b8103044c600481c510200d20b151080b500340701c010040400805007440304203a81c0703901780e000c0034212031740c080001500340800b801401091120402c1450150520030340150207043e000d035800b48240104481c001e02424001440742d0101d0b040800160412000200410035403d115019509406030070f00070806000503010b800000d084981d601c400c0da10b0402008411194404241403007883c00c0c5039000303501d0303600040e2981503407000c507000140c075000054160b94800c0e11b03640000d08490301108420038060700303c0414025a1007207440850540320610b048040f030700704840c1303c40180b19130180721010030072100161074004000b8208405120b101410700d00030410782c80301880d07032039000616400c8410 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 891699262 1250 891698012 891698047
    0x906100602030702010e010302090607140607030b030606100f0207080f1c0c0203071a0903060a0c02160e01030b040303021b0109120201090203120c030f19020105010f08150406150b 79
    0x4903901c007840c10320307216a0008140554410307105042640215203400281e4031003044804c2207500032500c6501644024450762610300407104000401e00c0e000c00c100b418200400c0c00d41c0302c1d42c0010a1580140381829080e02e5050031002080c00f10310520a0110315105c0410240201210341c0d0010048034400110650f95803480c620501c04005524140c0b00042e00d0010302d01d425203180140120082c240f00343c8581c6907001e61000d03030f03034580b28000501c14181c129034441c65040c3c80580c25100a2400c0f01e000b50020501340c403440d020007003100c004001003464071801d150810b2003803030050f14248000520305222000b540d00c04030036035950200a410000700c04802130540322940003c0c008030b041500002d0b1100c403120007050b43d41e0000105c44038003140c14001c6405c0b02060201a03a1212540c0310f24840c01d00800071070102561070400040740712003407091302e80221803203400100a0b849100020950b5100040c000b103601c41d40315200382650480b5201e081c07001d0f1080c131110039100c0c40c1d10002100542e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 891700512 1250 891699262 891699269
    0xe1b0a110c010f0503040b07110a0303141509070c020d0b15120706051b0c03030a210203280e06010b0c0114062d09190515061603090806090610 63
    0x104104020084d00101543e510a40210084115503030308401031350707400e90881484085000c1c28000130101a0550b214420711401140c44e40703d541e07503240c442c1100c83d1091022176404240c0c1e00000d2005c1f480f901d0300c0d2203020300c041c2605c42c4000301560341034401d0406171070003840d2290761908509241401031405001e207400340f000b410700a1501d0800b81c002e2160821502281100b4242c0c5818200200f000d10f007805000f60850b0755552000c54001e011001503c9600d00171b042c0166844560005402901e002d0f0b000f0004102c240d05941050f441d4041c0580340d003003c4180c4541400c2100c90b01482854000d0180c228034560756240305d1ba000d402c403080f01040000382403000040c4125901d55140340006074a4107040482e03417514407003940314040103c3d8a100d0703220452000f005040701101c4a8401c0224044000340015100d400440c6407011483e031045400502c00e001c0d410b400181c440c442d8005078000c1c20002c3c202a02c0781d03490360034020100c2e0565890b600290500010724100d20b0040c008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 891701762 1250 891700512 891700517
    0xd0f230c010f050a11070b0c06011a0901020c090a0f06140f1f0e151303171602090c070f110f0a0609121a04050a03120b06040e1b0a110c01 61
    0x200400c0d200b016180b070107401c0d11507040003517000800f1580c100030880c40c8041c0c01d41407070703294503034030741c003024654a09090182419030940850007491803040041a140c81e0f0384143c01809501d902e0400f807085e54030340200311a50640d12031031215584413a81c40f50030007401c2140a0740c00c0c000d1702c10040c80408514800c145000740e207914080316603500038001e40c418000e000d1410b40600da44040004000e1908030210343d9032910001282c031409101c084400c01203c2c440e4000804000481d44404a58050701e581010340100c94890f0b0b20051809004c03090b80034000a44040c1000c9d4140c580c2000d144081c007084417607021203c00001c444c80e191102c4040c2d900c044510101e250b00b44913009110702460b1081c4042c0766546407440007000803030806079a003611010704c00c40c1d5501d032a081190b562845d0300410f81c0881c4c0304d0f1449032141c90f203500420302045009881d403482d103468036002c155602d400929403050300044034885809498030f84000c02020304250f440e40814415102158140000c1c81c0c1020306 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 891703012 1250 891701762 891701777
    0xd050f0409050a06331d090414031305010e041a01032d200702010f030b03100e031b06010f1707210605060303031b070303090b0106030903020f0a050c0d0f230c01 71
    0x1086091340e0031b12099020141c4908010b5203c03850f20203c0c4580108041c185400b01080f00d00451014040001c03c55a090f80d07001400101c0d1402d01084840c2d0b11031824810104080241d880c0d4060b80103c50012035401120b250b095048130031000618022440791250350b100c40400c1c580f07409000d00300109083e500f410340e150501035400a441e6445801c20f8005041d121f0464a0b000d40c2c0c1800f011b021581c8603c001e100084000f45025100c0c0d101040710300d40000046014044220300048050580e00201803282d00c15050140400106025412540302032240c42d50101d00140006100054034010007049a01c51849241000030b83d50010b000078080c0c0d10600400540c000742d42d40d4802500701e890982981c0d40210f007030480c0600036003000900ba0301c1d220000000c0c8254103601421280c0c0c0203a09860020200c3d140c2c0030340701c1c094090301170301341c0d405001d9054081c03400328294808240304e010309440c02d24140d80d500985212580310466450404445206001c000340b00e2807a607020240792480 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 891704262 1250 891703012 891703037
    0xf07050a0f0e10030c060f022b2001110702031b0102070303050c010b0301052503180b07170103060b102303061203030907080d050f0409050a0633 64
    0x1454641403060b20450000d1070007041a0050804a1001540d0000c3c1410060b54980001810940950391100014843c2410700310840e041441000314810360707020b40c0d50540f004080201c0c4e0b200031095803d09481c4044500c003940810902c1019100e01480008540300c8903680101800e11f81c0613074071014045a01045038443e0781e80800d203001942e40c1410f00a480d454881da4150050110040c516010340c42e020038040700101c003098071030982e4400080107000c0c445110049003030b52881d6650b4004030340f103400c1e007000103041d6966071540b06101d440c10000803621105041c034110804e901c141c5996954061005050820407020360081109040c0762410740e01582003588924070702804e2050140c800300120304655642440f601d00103100800312512424010035140d10b030001c503c07038401c851080414200c00980070304141c800f803041c0e420031079043c5450440c0040c0a4540100103401c2c0554522000c250400d141c85031480941101d80760820f0303840c0400541e8611000c00200070113001d6641d8849 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 891705512 1250 891704262 891704279
    0x10503030c1f02160b0105040b030a050c060a050c070314240a090303020c013305011b0215221e060339020d03112b06080f07050a 57
    0xb48403051551011500346119640d4000074040c030320a0200c02c4102c503251009020588503002d040c2d6400b25001c01c001454541050380e9281d00b8000101b10b600445107402d01e41c0b4100000c0c1081c25a9803e00c1c43c13034a007000c10202d0400003a90000c48403403140820740c00e400e00c003c00062510120510136090070007076460b003410031140c00501510240d61078414120815100390141c03440144010001e00ca03032544c4d607089540501074164105000f4009400049990100d04445400c9400607114484680c25200c00384c010600c5e2201c1c11f0303030049002502c8000c4004140005c0c0b00c2c01d00503405a40e200c8160107e5003056522503807000081c00125101d003400e0001103010301c81141d595090020710f0640c141a100e80b64110130203e042405492911066a005a0083e203da0311802d5400d0b2400d4071109842034088514219107000e0000c1c060040040c240307501a80d00d207003c0f00400d00d0402e0fa00903116060155241900000c1d826088041072680c1d02008000b00c5002e020100c070905c582a0900540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 891706762 1250 891705512 891705523
    0xb18300901090519090c0f020f030304030503190905070902030601030e0c030c0112140703020705061e1603020c0d0203190903080711130f0209180906010b030702010b03071706010503030c 82
    0x80710701c01e0401d044d0030070002105107a403100811800b0300600000450381c0e8040c08201ba29011000580100300c07000b03541503c080b0880780b040340e054880720306641350300350f01d094500101d06001001682d1885007101140c4104000c0e001410340c0c600c0903a6038984040010180e582a501103845507200041c40e2005660200e0030102c0a902842e14030300240e902c1d00001c1c041c1556140d142020541c3c41d00b80103903035504d5001089941d0080c03048074215140c0b00c01e8011055421880365030907180600c0410a08070405034529691192850098140499103520314101003030001041c015070b10028504540300c0380b980848080a01a041042007146181c030380c564075128070306000f03210016605283c1420f5645800203540140340220400450b0303e0203602c0700080d4805070603184109560380190054101d0700e00058840e200e10340140c00711ba440c00d10050180d8102411031029035480710202c0c03500c0d490410140f00103002c10540300d08901807055140341003c206800c024025001040204a00e4000058 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 891708012 1250 891706762 891706769
    0x1a03060402090c1804050f1b04081002090a080607111903050304020906190603020c060a050702030a11030405041a040501080a02060a081f090c080c04060c0b1830090109 74
    0x403066900c40c18201c4d00c000200710061002c3d0301c42e00c0c0c0014840e480c504031100d039100d10603c24250108a440c150306502c1d9000d60b2140e0103aaa214070903002c0d0020702500a408a510b001e009169600c0d11008003034288042218868009240000300c152640303030400c1040290b003118400c0305035048961f01d00510700e100042000e0702034410300c400b00d8915184c280d448540e00b402c50040103400b9071102d00090195101d02040d505910030710020810104181c4201030040003140c0085203803203010b8006841f08004014098114041800b0002d05600d0720300811341d840f03e20554004410b145c4004020807034030107822041c00781d1b11040080c001a100c00c81114007205050030004401e40d03c0d40c3d8024044180360a6030252003120880010b002c15440d04410324020710398a6805580d82c8140700f007a6180992721a610000700708c0090040441e800e020720a801c0041c66040b0b1040c1c100d00c000702c62038161701321900041000030800b02c2981c01c000b900042c0c032030824040210314000003080000d189900c2800b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 891709262 1250 891708012 891708031
    0x305071b080403080705060a0b0f062209020a0c2a0b1b0d0c02040b0f0a061103070f12080f0105180601030f090506060127060f020a151a0306040209 65
    0x6010344280910300c01558011030b44113440c0c40d0758840d246000307501c1c2e00c000e8926544007414480f990030f10349404c0e0038100003198040c0c410382c1044c480300520070041401020703000101201d50303c0401d55044e580021b04000c4081d0f1242c10b0751028a107040040945040c0c5449900c5195218403411075441040080c1242c1d6598201c0703860702402c00c21440300c141010003010591140050490746160860002c0b00e0f00d6008407410003070030020406004003015076000041c1c0c0101060402e00c24180207080500d848607e1074101c82c2003504030340e64405510308a4100f80c50125800b070a8100450f44804415404507020306003203074039413508001c155070031252030b00010529210310000300d003a4807950110710000c00420050000c031546041c102d84440b419110b090004900c020900020040e648503804d410030911100401d8918210080f03031341c01030010012045018400104010542d000e1902c1c4800711940e00004d120660600b0824080410004150198009030204005030380c401151503480176040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 891710512 1250 891709262 891709307
    0x110d140f0f061b19030f060605120601201204090507021b0d0204141f060f0516260a08060a081519020a05030115020102070f080c0a120201091101030507 67
    0xd003c0400714000c420707040028200d20040c410180e0342c190060103915182c540100030054488808503428807504212007818840b10000c5245948608102c450784c8001071400c00c2d014407540c002604000044401c100189000b280501c400e19251050382d4104040340001c0c59a4805a01c0c00040c41000f04200d52080c0001c10005041d5203c0390071032390480040082c404486d04c0e0480c1e41c0411760341d442c000009421120300002c00d2140c05580c41040a602c02c0d00d5081c01d2081034512041c804081c903c00701e0790070a00b00306081c0c40044c10441410322224000056031103100c0010020004000140f11511954924608000310350001c10814445114500d90320032980d18440744940030032000c0080c0220a2001583c070f403040c6e0f8000091816030301001c51888416020040403400d0303015980c0050400714039541039030009590714005003210224101919400d80e01612010503c80380710150303034050303511042d00d0820014221a660f42d6440c0c01d0030100454240800008c001041d000c41709a0f00c2150f1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 891711762 1250 891710512 891710551
    0x40b04090b280905010c031a0d0f080d1b02010c0e010804060c032703120e1f0e0a030e03060703110301060c0f020301020705160f0302030d0c110d140f0f06 68
    0x10182e06602c503a1603020a100710b550928001c2d0080103580d140c24006450004481da14450400c400e0090301c20013843e250840c903080e142c08400c107200d1030701150311140c04c010344a0311100074080d4181c10784040500c1d1500c0d1140b8040a401e4940c80102d1004001119408a003281c1c0c0003100180c01640100d00040c03490b152003070030380043c05031783c445005406400d80d540114075601c2410208aa120356903081043c280305044605498010340003036200c1d0044a49595600200c001d0b014803040301b07100101d0000a80752540c2e040c14001507007640004c40e0520f07956540d041c10050076812802c0c500e0200404107450440300c055020600600d010000d02e00f0712442404241e015030795160f078000f40215501c103044e1609940d82c0f160007140c0e03800990720900004122000100210443c2e4000c2d0140c0500010b07403400b100c6024000707200301d8510303a007281140e0036520fa0030382d802c0d40c06210f004050300000004400a2400070380454600c02544103041500c0c1200c004110280c0006140c403007480c0303400c0b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 891713012 1250 891711762 891711811
    0x100f0b040b180d0506010b0a09080102041a1e0d09061b020d080c0409061503110c120a0908010906241202060901021203072102030103030c030804170c030306040b04090b 74
    0xf05a000901039105503c00441c0d03215602c80208001d141d030341c41d501c40031075440c08405d00b40c0c05203125003c0c0003c0e1403940c2d407a07000d0940340144490400c2c0542142c0c114001f900410941c1c119002c035080305540c941003a400c0040f20f1140f070700058003150449240b400200e600035501d5200200f080c00300000c031408240220000c206407005002d071010180324241c0c9031804007214081000b5003200182c200480c0c48800a854011101000c0480d009000100e03161807481c1080d81c0071910040401c29241000504104203101d00242e00340b182c4404102c030060744103220860401890748074a0080c0840e0708111184a10028000059043c0d42071901d60840702e00603402c211122000800e121030000820490707582c8854090805404043e0721210b5968844154080340000d00005000c03a00000314000440c2c040d01543d50300c18494004241111680180305629400c9003400e03092517131020091049619013030003464456041078804200359440f03512021510480941040001c42c0b1034644001c1300c40d03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 891714262 1250 891713012 891713029
    0xa150527074e110c0604122d0e100c050106050916080c0906030103030207030c090504081c06050424080606030a081c06120b0a0e0c040c050c06100f0b040b18 69
    0x1030150206912000d40e0a1803176114002190b04072940d604040907911098001e000714003881c4400b821149642d8640c03104600c45283c00f22642c07050252071411112075542d00350054803100d12994a1a040201600d461070139103c0a03042144111055401c21691400314490310b50b1140701c901d0504815140d01c145401144680c441c1d40e6045900000040141600002d070a8220381c821810000225036500d03014003125003c3c0d500030700c07100d42045400380c0b0300c00d80c1402c4060b110903107030b0004592f596a8009822200305000f018500358000c2c075100c260300280c007a01ca008021590241c500c3e031a15100203a202d018410700281501d44c046501008210240300c40b40039130b051194100301c6c043d1292003070318002c040f01404941c010506000181c1c01e4017907029030000b40920000038212400107a0410001d007290800c0d10040200a00c0401d81324182007281d540640200d60004a0712801c1669010603425250000300000c4010002044a00c0284c0100d58082d10201a41c1448a219400091094 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 891715512 1250 891714262 891714281
    0x30e122b0603060b10030213030b0601020f1e011a0a0b0f07060504050a121815210204060f0f0503010b0913050901140a150527074e 58
    0x12803a00700c0c0402000300c00c0d884403144280c11100c2d2100f4090740c8070110168030590f20762450f80032030603008000140b0008820b80d00f10700140182c400080c1890001841c01400c082072064209c0b43c0d01462800600038410800032622042c02c048541c4d40003404641000c49a00c102c101d41c0c000040d0b40491243d4040c1a5010968419010f0165003402d0410503501d0308a50380c20344500c8814140e00e22254041e8115003624000302d60110401032402c040340202e0800001110705000e400e17000c0c4100d800c0c090700030425110300802c0c01a103c0d418020014044080d0075006018410303d80804005a83c201080c2d0b4112000d00e0013203a0740380500c1011540c0c400e88104404040350910b001d0007001001034201c4110000e5a146181e01c5a0fa111406d10039114980e03414410519145c1040c06541007012200c0034011410048500711440c0200001803200b00f12882030000d41c0801c550060300b282c1c40c01034485c6a0a40c00410100c0e2071002c208042001c0d005148580d0480c03509800030840f20036040603031003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 891716762 1250 891715512 891715597
    0x5193b0919060902030105010b0702030a1101021c0c0c0801140a020a03020405061801030b2b0602041a0d1b051603020c03161e0e13050f030304080406030e12 69
    0x4030300c81d2501c40701404100f181280f095013880000301700700300c200041d501a00d07001801015001001e444440d950500f070181ca45c1180504c440c001140100b00d800d10f05210340c15601e0040102d41030410f100400c40c0c42c1c020450a174104100104101d0300641800e23040f113091040183e59281120b01a80240304590045400800119008403a000e81d01d420444108080e2000e01c6000e044508000b82c0703280403c5c0b00f8440c0c0b4642e8441c9508522480054200284615801498203850707001011201c03660101c0403400d05800078488819109501545440340c206070b040903103d107207000015109010794081800101254080c4000b454820040940c0820002c2e00f40c2d45042980c4080441481043c040c032000080014110015581c007c4440d03000c6a10071002441c003a11000d000c004013005012007501d0718483c0b240b400c45054400c0c0000c6000c0c03441006a80c0e9158a0290060305441d0f1000e507600c196082885215a080030205c02c88035251062400d40403010755151080313070510b210400d0701e0072 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 891718012 1250 891716762 891716803
    0xf041103040311071e081605090c0d09020901141518090423060a0b12070620010203090607030e010b10260103082508040302130605193b09 61
    0x2440c1e42030882c0d00161003140051710659407c14070102e03440f0340940b00e0280c12000020000301c981416001404c4124205400030921310310382e4000819911081c0c100200c2400320441241e006e180030044e8041e52040002c3c09410100c011950851404000207800d0281d000c001c00a010000e50414905e13644d40e80403186614010104e20312942d855080f522000c025180880602d800e14003078110383c0c0c0c41903072000204505401c000045501003c000484e1307a114001000ca81c141003420b0000c2d501c9660030000420042c5001c107030082c02d8504004c00034070130b03900d4555044660745920201d9004403455041440c09408100811000c0b61074030400c41d09020030020010042008010007042c00d2107250035862a0b01c00c600417229010130100c200100904420030040005003001c0c0722040401741d03103c500140c001e9840740410031000c00040b203555a480004800d12950314403a402c108843d03440084012902108107540d0030509041a0900c07003084c280c000110008020840c403480440c1103040c224 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 891719262 1250 891718012 891718049
    0x215010305071809080c070501121a060d020405031b0103060b0f0d09081b06010302120d0504140d02060703030b0a1401020c24040e072c190506030907050f04110304031107 75
    0x50b00d070000d5016560002b51b9504c015802d4580317502606401e410811540f0305001c6801c0100f000c598450403078265020340a12000030150313018007000a403c4102d40351141103400c500c0c0010308680458001040811003405408507485910f402d4411382c000b550300009410340141001c1032240030703210102d084549500202d41d0154800709509040302c1c03003543c00e20b801201d4940003544400c060b0104c01c0000302d051108200070302c460502510b528501a011580f001c1d015004a840c60780300000940100340c841d06200c0f068100f0b81006801002c01c16409140d09141100003034035140400903161040380441951661101018158410484881c10142d900c5030b4900000d40014001c90b85000402e41030304108000384861070b1300d11201d20340503d100155840c20717001c00509103400c0c00d0b01c082c1c0d81d10300007012446403124030055016161602c02460510710703100800c9481d150001c1a50301a90038454440d103030442d80300643c0c1e00261315050840c45899082d41c00c2d0300d004865484190035000c0c041000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 891720512 1250 891719262 891719287
    0x10204060c0302010506060703020a170c120a0f030e07091a0d030c0c0e0f04030507031b03030e10021314062101061419030b060409091101021501030507180908 70
    0x40850a202e90000d01c01c5503611010010f031401540c0010300540c008100050016a4110311144541603680265040c46481c0303000c54541384d001c2010035011800011000c651540003440301d1045021032605010940c180c40b425a19000d4034030039170a4280e212401c01d0502c10880d40061000741c40500454181c2c1c1583c280140302a03601003040c1d80d030383d08030200414402803280c0d45502c01c2203220b080e1002c64465940844465100300029002c0088280c500301644030801c00f02950b9074001c0d5004145890004240f86c01e000510803910221441040742d00001000c00c56040704441c0405011a4040401130104450b4444d4074043c1c0c030321000d091108200c607103140307102030f068442d10b5440c04004134450f504014141310354000214401001c501d450082da120350888516254007400a908080e51a004001519101107003201c4c0c0004011700d0750450359040011102c122070011410f601075145455050300c0d0a200c0c0120450700c1030190803242015000c1c0c100f60800fa600850345c0d5502c41001424 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 891721762 1250 891720512 891720527
    0x241b030c04030c1208070b040c2606010816180603020a0905090c1507110a260c030a03120c300c02010507021015091113092901090801020406 62
    0x3c0301c00b5041918040346454800031032803010381c3d00550b9146416401d40702d10382694401401203074014000c2c400031405000902d44c40d000c0c880101c0540300410500d940407030800005070401d0b1113aa000340b03003410800b4880c6402c0801c68809969441d031114040c0001000b411044d00080d40060004200084c11080d075481948142ea0004c180c034a0794200303000b0404040c010004003c0014420303c81000032a002c50740c1e285100b14000c18401040d035640d14a05100101c2d081e2103100001500d14029800000340070080c904030086001d004046040d903409000c0c1030000804200349550b401000440d58011910844a1141e91000002d51600015007140011004040d144e4046c14007a015000c940140285800341c070780d40d00644002c0600c10f091100504407984001140034540d6000a03c0301090b10a03028a0110b0078032007540d41c400442c1003020307401703540d0090810518160300300d0340030f900d400d08801408001003450400140c56000487e44160389401c4100707a5440003600243c1d01d0380101c803 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 891723012 1250 891721762 891721769
    0x20c0c120717060702010b091506210726070801030311121801030c02010504081b03070f060c170403201f0f060605070b0403050c0a0c080c0a08241b030c04 68
    0x28005000d40c1e0307042c040c4498003940c48248440328001683c070585802b1000e03290171115081072004140c10740060380c4448409176800f03030200314528040e00f000b17807402001405295030f201410420b82001c0e8401401d5240500c005010800c1010440035150710034480301d10645100c11120351100c51948540500700c481380c0c00340d404286409440c11900780180103441c45a0342040c00b180c00c00c81c2d4440740103903046001c452148076020800004000035142c640080e4098050b43c4005546100010040c0121800700071300c1d42d119000c9001c01c000213a00409042e90ba034148012000b01e007500202d100c1c40c2c02c4201d0100301108045d4510030f018045182c0c0504004c0074403402c14414907a49050940c0d10344205500035012040d03c10000d004a800303400100001680f43c0d04507409044651502d181052058200e00411781050104a0321748c500003000c000070703040000150000107540c4090785401c8a150792301050003002da00000741c0c0710902015404104504a01a079980c0c41d102c08040d14a500900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 891724262 1250 891723012 891723017
    0x60103050c120f0f1f05100b09010504030c231f0f0c0b04151a060f07030e2e080609070e06040503030a0e041d1f06050d24020c0c1207170607 62
    0x406a26185c2d00a02525002c2c80d403807801d01543da0305101e8004044d03404291030710705000c0100030010003d104449444021300110708818501e0710041201c0d02c0304126140030301d03c141c46420102c0a045c0203500c1d03501d5080924104400318148000701950041040c40010b005c0c210040200014880c411648542142d1803400c01c1120004003200c0d120300c40d00900507070781c004400703000780b014103070210307005003130450003030134529104151000003450011a080d004c2e00901c600c40d00302c1713101c4141081c1c40341c080466070a00084034034000b4081565004018207a004102c80110702034400d8841100b00d0700a448054140c030756a81100c1005040c55a5407074241d13008034540341404d80140d1b200c5c0c3c0c4e0300b10b441c1c8841000d020180d000f5000466902145807141c4016a501d000026036682c8405110340720318868000e404106c1e10301c25049200c900404103043c600c40c0100500c0c4000400418201d021200c00c6030300f0f03c1c28012044240d45450056000301c40c2e0710040749a4010b1400d80064000e210342c040b41d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 891725512 1250 891724262 891724303
    0x13110304020901061404171e07031101030207080702090601090503030310061106060d140c0607061e050f01051c0f032115050103021c060e01090608060103050c120f0f 73
    0x104d5049a0221700100144481d840500052003040300416503401080311090031516009128822000020036205404080c1e6000500410801c10005046855410b003401c085007081c05540322001c480c4602c00b402881001c0c42800284a41e00501200000d084003508807a200d01d0400d290000101c0c1500500c800700d840a040444420000078a40d07201b543c01505203480050b00390b1b11004100d41000700d11500d03024240003264507032104009412410300034580400c0451624090f0440c003413000310004465814a020801c01c01654000c0f541126010b841c0c0d40c0c2416910340801000260b54a00140543e6013102c0383c0062660150030707120140c891000b004040b10083c2d07502422984244d00050b9018243c800410607907010b540030384189100902c9200104075800340f808210f80c00340d0065103207001c42c0001401006001d204d054007800701b40d401044903504640301c107540d4450011286200d80740c0c80100990f9010140080240e040c4408112071088858680300b40d00c07006c0700c0c0e007a00941c10300c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 891726618 1106 891725512 891725519
    0x5070b030406090308090a20010309080408160519031b15020f011104080604020f0109030b18010b040c0f1101110f0d061a1813110304020901 62
    0x51400084044552801170f00707895010701400d650fa40864403c0700000c0c00130219502e1280c2d50303803100307240c0b080c2c40004a010380172030803001389040c40210703001030305000009042344030549950304038410b203840f241880203148051000c500e40c009002da080000c40e624100411801910510045000340c4030040c00c10160b041c554110b0050703000e0f210030021903200f88a800341c0d1600d03a01c1d4592403c0e00e01105140d950746c01070030203445a070035200b0807060b50380241d00c07001c01154440340039811803030301445001e50500f910700b21115070750030402c00c08000d1400d84241c41806142d41c0794007000403842401220700c0f81c5410400c440f690360b1071907074150016103840500b160a10801081c0d0755000c1e078100c0390080c3c81d038079400841c017031810010199072800c010f400d82d580c1645c14041600300c007148070000b4040c114107120010b543d0386480c4110701007240d124002c40c03045000352440807050b49c2c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 891546762 891726618 := by
  have h0 := BRFrame.cov_init 891546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 891546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 891546762 ≤ n) (h2 : n < 891726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
