-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5135
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:52:06.047997+00:00
-- url     : https://prove2.me/submissions/917482f6-6970-44c8-a7ef-9583e79cfda3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 923381294 ≤ n < 923561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 923382544 1250 923381294 923381297
    0x30201060f1805072d030608010c1407060207050d02061501052805090d0c0806060d0206370f111c03020306040b0901030309142d03071e03051c 63
    0x200c02d1010018a50341000398008240d0034504403c2d07030158840024881070000086661070781000a056081d00b5114030700150925030001c00444440c08e201074001c11103021448803680020451908000480c0c0485080c00d5201e415100002d80d2030201070742e0f4403001d03580b101c0b04903200d040544295105800340c3c1d00a85040c2c0c0c9403c622101101e0800010140341142c40420404100ca480e09450f00811110402d00c950b400352821441d110a0609000003d448248101c0f49812800c0260756030100383c40c5200d80501010501044130782c039400220003848020002008041c0340300701c02e80d400ca80e0007100a1081c1d10b0304075400c850401c001e03498149280c003412641d134031450b400c030b0310f984a68003859000d680507200061000355540020f01c6080241e10403000950313080b406100210025180c0e440d000b4040c0c0790f04040206089505e105403d00b4500d0206040b0780c40c1e080302903940c1c1000301c2c070003d081c0e0150700b068148601034001d20040c094082940c09103c0c0710300c4c8042d40342c21070800301c0c02108507 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 923383794 1250 923382544 923382569
    0xf070f0c0807240f0c0506010b0c1c0c0b0c04030b0c0a120b0303041a040803180312040b071101032004060f0804021c03091806140102030304020f01080a09061107030201060f 76
    0x4003015a4409503201404c02000000701c03420380003c8003084554060300710b84042d65168440c2e00440da1500e1100c0e600300c1d003443e0003a402d030201d0381d40000d0208840c59102e911a0040e50314001c0f1981a4003983e4006072002a940044c0f06000d401c16005003001c805994130210300406c03161b030010135034908100b9943c00d80e0081004125484544141c440030516400c00c1600c2c00780d0700c80c095031550704048000c0c0030000710000c414100e4941000317080020348400d0000c50401d441c2800d05880390103013000180040a40e0380340719075540e201c3d41c4403c10303020a12220f0344001300803c03906000b0b6005401114045401444881d22103030040c07644500c41d550040844200e0f910801c4480c41848011030100d05001450501003003640359203980c14840c40300090001078940c500059601020b140c0845c2a05542041092001689814510443ca8402070920718007545580000b0001030841290240100780b4044a4010798001100200140c03402a4001d001e85902c0b841802c10428151141da03500059 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 923385044 1250 923383794 923383859
    0x1809100e070318050102090f0d0f2004090c050112020405060429030a0b0306010b0f031b0f04030f11030105070f031a0901031b1e06050f070f0c0807 65
    0x81194030300d07801003907072601003920f00010804829a89940000b190742da500401c05400e5070404000052214000b114100d51682807034685003445040c0c0311b400362407100c00307400b04594214031500c0204403141c003400820080030281000d00c0306155501805000a1001411080031085030082d68140c42000b00b50524051400001c41e015841c0c0e60245154682d0700c8802400ca001048050361156012550101e80d01c858a020142070986c160803890484005000040c680c840c4c60017600da00c00c4098800b00e4201510805101c2140600110b2011041000070040700f0030050f403c0ba001018400d0b4000c1040900329070402d07080e140c00711000000200120280c0a000d8031940014060803001800c1106020500d0081350f9892800d1700203580501919450303903c2002d00035141c800820649180c01d401c0d01c10b0202d48039010840e4482c450030003e020403c040e42007004001c450007541e01150860b00c0d400140340c030102c03020092007000b1306030040c4480002c0d02210161501c80f582c0948070009104003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 923386294 1250 923385044 923385059
    0xc1502060a0e0d200c090906090f01020319050711010501090c230f07060e0303100303020d0c1205090105040801180c060503011202041d0138181801090305180910 71
    0x1042e2020000440c8102841c000f001e13207914030514010343c400409000d441c600016a94a80700700700040303011503881041044428000300032402d00c0c902607003b000c5169120703054101ca4441d29445659203030351910380001034003645a44140b00320101500d508251010b120380c1000360021295205481140420420415035003440003004005d10070100007e94903420092980381d5001140d10800320020810705105040e01003080b00c03820f840c1460481610b0079196a06030800102c40030340c10901030082000b182a07802102918040c2516074020021140c00d0160307010003441091040e1000c1000d40008980030b841801228181e65003a16422804001582844000d000203140304103c620900743c00e8110003401e0081922900b00c02918001e0400c21406101c40800b0200c0030700140000e9814041c025183c1d04021141d24080d4540c1d174646aa410350000003941303101c072071078206c0c0d460320400008154100010300300103a4581e129510740c079180d030b051201c0100c084d030b002020000c80c48400c01541 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 923387544 1250 923386294 923386337
    0x603041b0308040b1c020702031e0133120c230d240b0f060a02030c06070f020106061b061d1b0f090105090705070c1502060a0e0d 57
    0xc84841100c5109607640d445100454001da0008189aa400140400001300412440c5840e0a080000b10314061396540066900c0030254800b201da205031060000b0048000c0d4005800c00c00301c1071303219044a80c201e0701d1003901d2600c030f1080c8d20380200d45480850ba0403195001141810340c44148520040d04204031968203c002e1030340da069030020404111a1926401c0440c20b8851082c40100d5400c401d0103c60840e80d425130086032a00d520788420714001765942480c07800207000aa6065540e101c0c0e400c4e0880c114424003c940615105240505c021282c0c40070a0b800c80060640c001c10042e6203440007192200300c4d80300404469041e698010021500f141d12007641030142440000d4903054003d440c60518044008003231030140c02c23200222103814464032442000038110381c4130740700d9070404002a04910001d402101003007808110a8208103100c80c6080c081d0009102203d01046443d50095450a04a03281a0740c0b50500d00180c000070000035501c0c0c4107114035120b032050303401c4100c0b2902c0740 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 923388794 1250 923387544 923387573
    0xc0a110303071709090901020f270402070503070b0f24240c010e0109050703080d0b060708030601020d0f0203040501120f1b0f020a0b0c0a0201021c05090d080402060304 74
    0x41c0800c006400000f20308400d40040c0d80b0320030500c00d40354040d0300e00f0006140c00060a84c01d00303900400200600401250480b102c88402d418003c80319080307001000303000154911940d401500c001071003810300000001500f22144100312030324083d5200c500b40c00038030209a6003d00e0442021415000000e03100080f41e121000140642e1101940c0c20803600c00410740301021413a52100260f420140d00003030040c610f0303400003100244661540303640c60b43e07990003c92101420800d00032030039503030407802a0014480e10b68000c001544330750f0316007081211a401911154003502c108009504502d0150808607911a003a070042c5041074905401950580003074490b4030304040c0d0300d03040b281d0502c00610401c46020302c481101081c925500320085d010402c0350b100c2038107541c8200c0391500080e0328203034000e80c0f16291a0009484424400d03080e40079000d202c42068003080955400119902c0b6075100602c030744c001c40116041000c01140503907803c3e206545c080d41002041000a0128142c031200906 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 923390044 1250 923388794 923388799
    0x40f05040c0e0405160e031614060d02031f05120601140301020412050a02310902270603060a09031209031701030b0405011b0c021e0d05010b04050702030c0a11 70
    0x141070440007800b2543d08171030382480307554903102c2d10320b005a000c0c20b1068030b12000e60080103950004509030481c0b404070b20809400400c0000e02e51001d44a0b001540ca8400315504255100c3c1403422030344036001d800c0c1824280b5920f898800150b985000d00c03090030042400c802511403030742030440c41d2000340d044403001905503408200c00207180c4a44100780c01070343c1c0142c001e058401c02074810001c43c041090303103c22249180c2100381c03181c203c0e8864074184004000c900000d1882c03682c070119910703448214000c2e039a0158100b980241030304460b1981c0c8a0402103059444aa40704401442150300d9550040c00066115086d0139480c070b0158490f4a8107406800c00b1400da001d004524103a10b14240c004480b910002014002004402d0003591100030050014640354000070400508071170400b540a03200e60341100c5004889044501c1c40c036075101015080c1d198008807410864042d20000301c40600072031034a00080c0d01184040b05031290301800c85e01500c0a00e5043c0c690700b08002e595403040d40e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 923391294 1250 923390044 923390057
    0x3030b040213230108010819050a12270602070608041e2003010b06030402130b1302070507051e06031b031305010c0c081b031c20040f05040c 62
    0x5003042c1020303407202d00a02407407142585240040401401010b143d030f4505050107040c00c01807040d02070104801502107004141060b2458043c08d0652400d41d440ca40907158088070300e03901d400b0320340c018015480409080e0000541d2a0500c00e0340d180e03042030307100c1d20380160061030060004512030300c143c81d0058003800105124100c0107410a210203000a0201c900540800d04040c270f5005200070641c2090080340200305203040c1d200410201d1200600c000d01c5076070000d9044031005000c0d0b000250088002d05040000780003416418004e500c400c8041da0180725015001416180814060091403040310901d01700000c10011b10501c0d4001401201036403091000d4562107481000107948650201d40021101007402e041035800c4421424201040100444552000c03c035840101c521041c0d20345400704803c1c400102580c110b01030015440740b580e06895a4040e8044990004400c001c0300000c0360110541c21054601e051041d413003081c5004400c40010401ca10707240d8001c0032588103608254 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 923392544 1250 923391294 923391307
    0x270f061e0f0c1502030f1f151412101d0c041202150a05090405160e06031807090c0206070c11010509040f181203090c2c070302041404110703030b0402 66
    0x42e41039800807194044901b49100412403440c640c40450303401045486d2200c4403150500403003080c2c80f958200c418040c418880d01001886401c0e100f2248421600514188581020b80c0d040450080500ca198943c1401084241c2114500800c03980a80159039100b441c05103008500c4d079508691440c1039070301c013501c490507246200184004280200340356071125a203038401d808100031100054010441078010000b15201550001100025890112856170712a911105107480d108030070884607290b40544040012103642030740103190b1407010340d000e90780340741e503a07400841c3c2c44144540003800030060180d0208055000310b008004606000c1d001041b11150203e06000b030f20400c4a807660280c034054400014440100407a111380f49480c9020300c5443e60b107849014014555000d004000d028901c460f0b058120307401d04400180d040340c100b0074040c2c6010b0902034001d400c64803945c01500f00000703424905142c1071040580002034070810314103004054400b02c2c0200f0f07110807815041603080006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 923393794 1250 923392544 923392583
    0x20010e030d0203100b0909060411090a0b1308010b010f210903020307020f0103051302041107060912020106060807050315030f03180102012703270f061e0f0c 69
    0x30007244450030005a0750b03080c041440f1001c55401e0f48000541641030100400710383c0c4043d8000d4224070121404030313000d0682d0016103018841d001d0119032000320501300091044d5a0009032801340003076031000030130076030364041a4240c81c081c081c454000b40c080802181118042c50980304e100500401d0040c1d0342921519000c110703504940b0030f0700964408129202103190441400711042030a190078402c5003010040000014242c41c0024817541d2204003124603044210242ca0840d500301409105c004007a04000500c03100c041350311801542090b02c0400c1090207400254000d401955a192031a80d4001c11003144680c0901c00c980d16014801000d4460101003010b40b40d0303841118004a00d40450a0001e070031102d03006580d10f150001c1030100040110510104c0d02010f4041c1866055005a1000036540350040c55500070000f00c4403002080c2400407420042c180d840c50740ba444031250a8064842c1c5940d4244080310000314401d00003000c45214441c00280e862103040c01d5044030104401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 923395044 1250 923393794 923393797
    0x290906150c0a0f410a020a0902030415060b09010c030e0916091a1912050c0901030b0102030324011107180c0507050c0418021816090620010e03 63
    0xe0f200c81524602c9401840a1081c03a80c00410a00341c0020b518440c0500e10030340c00209889420120588900101084038240002c40c0e0f100e60003050561a02c1d140c2c0b042c41c0080d0019282910b010b0a01c001c4103000340c070103129000554007401202c43c18400000011034071018202d81c21000c1021420742c3c1c0c01240c481804450050701102c01c1c01a41c40e0f07009c68005c0120300329a220a820708003007411091220243d0045500715842c125010010103140e54081e255211a0000c0e600c5c41c2d441c0c1010460000a880040c04100781d00743c0c0c05006401d9650012a030781c2c0810341c1da00400c0e0b08856080006001e01b910445683e030410706042140203410030480e0706007030603a8403a45507000c00ca041413a440080d4404c000c6060340908089040080b00c0d1076165a482c1c0d4a842503000755564201900042e5404001c051125030040000e52107034403403210810030340b400750713400fa00c107030120000c85110034010801c4006803101341d55107a840103c01c0e500d020301c0121802c510300d265565100c0c1321145440910 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 923396294 1250 923395044 923395063
    0x209090a0506040f09020d0602070c17010603030f1d100e0301020715060b0a05030a051003060e010c0e0913030c140607020601080f070f050108090c090a290906150c 72
    0x5a0000d194502102404140e641340c00201e03008a140c105600016514a0840106c01e42c010708016103c80151a01d51180e2907550056010f41e03180d08030320b080c400340540204082e40d12a0361020800c204424040c1d400c02228911f03031030114080e40646450703040c01911040030800340d1518020750210301000c40d08990061070103a5260804000d4009a01400d02800c2c000f45152035400e880c041605070000d10902000d49254a015100e00200d01180d8201c910072002d942c1140d0104401c01d9401a128000c1c1800c410110102e8179000c0700e003030a850000e10103481111a440d003d61001000e980803510040d80003000c030b0350b2002e00b580307200032820f04124042c803440f1150000c140550609aa8500e4a4100310a544076030b071002c9418009448030b0707450b22040760b500782059801c944908580509010147c03c400c1d80203c0000704104154025230404c44001c40080c1c054150104840815006406540921908110003c01283c03050500f4031100c40780c40c581005050a00490100741170030040c988 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 923397544 1250 923396294 923396311
    0x3060c05041a0405060f07260406030b040614270c1b0102180405041e05070611070e0c0307050d18022704081605061323031c020909 58
    0x2180c00d21103500c00c05110250b10035030048040c00c0c140303407400261882c8100c15003881c1500380031501d1010009103542002000e0241084400c803401c4440c03180d1620341040c1704c0d54002a0905031040618202842044150788402000c1c9100400e2541070000340440400c80310355980300e101d600c40d2039031081c20307609010322180c41d00c171030f550070300d0244004e605070003844c404070300b6441004a007809881000c00e100171a00e042c1c41c040707a107030303900d04108074000608811144907003008445030003004004181101a22665200c00311000380061001e40d48003410b018001d041c410301c1c4082811003940c20080c540c82110b901e80186030403240c401c1c0ca0103030f03040307204022450040c2c1c0702e0420446c030309a1350207406c07408801460041001c0c2c600507481c10301c5020300041d120a000003001c00e042e01455100c103c0b03050300142110490704040c1c840390841304503048142c0b02d403100c14000e944800c554050341d014140c4100001c501744421040301c5810911604a5112071b175900704041203040e2038044801d131150b46003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 923398794 1250 923397544 923397547
    0x3050a1517121305091e041b0b0a09080f120d0f0209060a0201060503071d0412030b06041d0109050103051e100f0b1f05040902090d06090c17070509061903060c05 71
    0x140000e00c00e042c10301806005480303075000c1c1c05002803101070421b143d000790130042a451601c450541a60b100d94150842101c400313002540120498000c0d904e80222100d02c8229041c504500000c45e407600003507064486201401c10681a10780c0440e000394010010b982e0700140b801d80504005042540040013900141c1d441d00c40c2045280303000d20010000f45490300c01d01202c49203a00e042100b03980300400061811916003003100102e84650302403040c0e82c1024104955490f1223160151028106035288200c11483c40d00100b54400d00c0c0c0100b0b41281c0e8414020003180504c02034000d25a00c04070420141445812100768058006016500f280741003c03e000810b1481d60003400380700c10700000005000044114080090341d0710108903000c03680c1d40400140c0b02c1e10b441000a20040b4005006015035041c031034080140000d40c0c0c01401106d51940f0f12089450740c900000e52145540e105440d880001e8000007181400c000711f0704007503280d400c490034940c0c94481d5203480489d8108035820002840 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 923400044 1250 923398794 923398799
    0x9010c03081026010e0a030905040c0201150b072f010c0305091e011d13090206070b0a39080402060d060b130e0907032d030c0303050a15171213 63
    0x380b0034020141d654002902e505c0240d07890240009203236205140c0210707660040080814400e500c905248814040c2000d0091b03540c15040303025030030186090340d424004501b044c00310003119240d0301240740c015024140da50314100055840030300c2c5030300980500008000c180d07010f9490307240f4150402070400c82a8410a541e800043c0000f90324801000700c2440d5810001840d0786200d0206004c1c05182d81c0810089070f10300c0842c540703000340840280108504000c2c0080f1544a13002103c40b00c3e1140664002070706056910f5010542c0101004d03a180c181d0203000400c50720450401d0b82c49400500310030b282c51040a426030444581381c2c403600e440440400d007200c4030383c15004400d001b0200b100d030b155014144400800d40b1180e40780700081440110b844030308242d400c1c0c0312111090fa00e0510f401c000701d10850902400c0c0009811045001903d07080004200a01e030344035112046160030014142e281c282440041016440603504489101c1d4080c00d07038003559402e0050400d03580510b8604556403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 923401294 1250 923400044 923400119
    0x9011116050f1c060207110d15020309030f1201050f010c15050c070f05010c1b03200f070b2d180a150e0a090b0306041205040b07240209010c030810 65
    0x401802d1f001c0c0c420301c01101c0400105049071171100814482d1000140d0320344581c0d800a2031071142e2882c40202010120f030700d40015a200700390904849090f6032040e00d1121000044541010303249009005c084100049182c4101e10f50102e07501c02c17055650540361405585130010844100c1c8021603a507915800940382440c0d001c03041590101c8a02c0368007041d00c909580243c65440c2c00121041c3d81100740200c0503080e9010409945400c0303880040c0d0300c5854941882c945254007128000900d602150940190030342c01c100c1d6582007108409100e800c2c41007500750802000d00b081001c03980502c2c4180003042d6544640492114011207840d280c1041450000348074440c10668804050246031013203903a695100070a1155009a00c5441c11000c2d26400d0000d40d0b4502640d00500c2010b00c02190490821080c400000413200780c410f10100480c9841a8403801d0b031040310368050004908a001c40300080c000e045068200d03e0b100e60800060b43c40740200c501d080301101100405500006a42d608407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 923402544 1250 923401294 923401313
    0xa0614041101080705070609050a080705060a0507051e0d0e0f0a020f030d0e10050c0613021804051f090614161d0618030609010209011116050f1c060207 67
    0x4082803d03c0304403480d01030005003003401001405801c0c15102c0300003100300001407140e200b02c070341c0c44807615450b08240e0800950f90203081300e0307045d602c0b854003010502850050f019581b43d1040c569220340711915046204000f81c20415412100fa516080a07600700201400021114200c0350700a045002c1c43c2c0c010490b00842010510380070b40c211400c0d20943c1903101d5203070050507074140c1e140c166805221000322140d2144001c100001d000d000140814035000e0009454014004c80f550740002c03840e452030355941403080e2002070031944011000c031414121140d25481003200c0100000b503480c2a500c1c1c2109681d070030719103c542441d4090130070980743d80f141e405a140da04949003aa04c245034002d6421800440c60162500c14440800c3c0000010051481290100000b40943c0c3c0d0f6400d0148029010350080070707031030340451004211030b40030410000360411201d860a0000301424a40818481c6c0010440d80c0190000b545c00c0caa2204240b041d403011001e144a0100140e90304690b0904003100e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 923403794 1250 923402544 923402573
    0x209040908220b0316051902010902121f0c1101240f18051909050d110c090a0b01030902060a1d2e020c0a080f010e03070503040e0403020a061404 64
    0x80b001151051191110f40c3d030075241e201d0101080c544603400c58450030f45075030050f00011803e4849040303004e1a015810f40045034594405d40340c400800b042c001813135440743c00c6820000701d82c0e91481131282045600740c01000d81000d00d802d10210051980701c1c201e00b96100780a0f003000c0d02030074481800420260364050380050007280241e540c030318186161902d4894000020b81003c13601e55010a9101c0c031003458040c40d000560000308039a2600746842e40d1174000c4500003601048260184042006012400a42c480d02c001e20034100ca50340c2d80c504100503c0d90481683c10151340d1015080161600350060035204c00070b8071001025159200f10001e001001c240c00d81c056802485100040101d003000c1c1c0d401031500040585e201c0000b62402ca14007c0c010031440ea00402c02000041d51200c081788450039000104c009010b0200300e489016a60f20400c0002812507008100410460f4417000703c140d00309201c0d10540b220a1740a80301c0d0820744409961507c0c050710000240805c1007a00541a02d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 923405044 1250 923403794 923403847
    0x3060a0609060507080d060b1207030c03151701090c060504031b03030f03051801020f1305030f030306010507170a050421020108011503111303020a080328030209040908 74
    0xc034241003800041c42d60045110041002c000406c0034010088141c115201400c0d600c00701c15100d03080482c10380310800c0181c0d01180402d20300914071030301c3d40c402c2c05104881440101500759041c0b4110102c6444089050a400103550712400341002940c6c150949000309210340e101501c1c1c90441c03c0005401066980c0e01c2000003000004100080e00105080303c002c12030b00b400202540c83d4210a142c1012600400ea007170f5100041e00c92560344658060090b4440c00d0640304c0805481f07000741980c40f1000701d249602a84140f002900d658881d41c02050001c0c8203c200d42c0391042020724107400364000403504d401007075000c1814007103420384030300c031105c1c126501140e10804a034680018240a030180a41c3ca603101c6031080168015001c0d80000040d90a840c0c1440d40e51900d8105c00e0150b1542070000b09e02c00c034240e103000a4041c01c00000e89124400c0e2040b581131940800034401040d4401c9404a014150241322204140e40e40384a881c0e0040d001e04405c5070303030f125080c0360140301c084542c40515 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 923406294 1250 923405044 923405057
    0xe0d0b07020d0503090c09040f0209040503210c22120b01060815010f030c05040e0a02040e010609141908060a09050c041119020a2102060106050c0607081012030503060a06 75
    0x10000c40020712906e5000d0980340b1019546650030b00300314103540c014019401c44a41d6080c0410004000020074030404510040c48408403840c00d9402058030690307006001140500240b200c0d405201d52500703600419900521016a41d000d0441602000c0d04040d915909024010032555800a108a074450380b0740c080b050503554020000303010940e000a2001c10555610781c0c80120501560441d0b0151620000d070018601d00001044040e51040c0a00c0102118800c00041e4407802404940207031000038a0b4070305810b2205051002c00da42009410059500659000540c440705208680c06140e0080d4041002c1c0141d040c00c901d80006400160300880c50016041303052401c48041d101c45996469903000c2200038401c049140084518028000140030703081340d08046655103000c2e40140054094aa15a81e103d00c1924a8010f0041402554001e50001100d0350300c501c100f154000c000d49010182e00d5241d00045101900c4ca84046011420000601600746004094900100824038140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 923407544 1250 923406294 923406301
    0x30e0109030f030c02130e010209100305060a03060906090804030302010b120607020703151407051810212a0801050916141e090108130b13030e0d0b07020d0503 70
    0x11090b8903401100076003040f103500c4c0b4582c03c5503503801d030300500700714150001e01110301c902515500039401046507505c1022401c0135900407038060b0040c2071140034020040b00d0418510340310381016010780f060845941d952015801c2c0002c91050141c0003a500a0f400098030700070f024148440c2c0c01aaa5028034540d000d41b00b002030450340021800c0940354080504071301010712003444009000511103003800c18a00d4401c1003660344d80030026100d40301288450349a1041c1400070b0240b600d0851104000040141c9a40c2c003102060644105015200510015103d0301c801030980014500d059040c010b514030f4281406c40c6540b14410351301410741110720131210f05100e8400c03114184040383c2c1d141402051203031400100c80c0c0030142d900242900300302450301c401000c070400069210058440c01304a210780420501011503088021055221144003519110301980301d400711644d19044040202005482140f0b45070b003c1c0350941c0038031440903032050b81841e440190800320700044031405c200060040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 923408794 1250 923407544 923407553
    0x20a05040e13050d0c15050c07020102100b0a0902070f020a0b0d0e010e1e1c0203030f01150c06051b04030c030c08030f16080705060f16021f0c0504030b0c0304030e010903 75
    0x903101208178206188002c00c24074040d40d000c900d48000210319841d21b402c21030000c0c8108014603080b4401d9094807a084031321282c5000b21603035400e11941010720540d06100c1d19119074020081c00303004000d0b02c00709400d0380c3c2c001009c0c1000d0f03802c04028440085600c0203480d086000d1040d40040000081c4051031004480b159221146031410349100811840c00d0117140060101c0c1201c0c00d910154441c80f6840d6000103941c0f5403080d40d100b4080422900006908074884480b0125480c265031450010782a644031380d4094070000c1c00d003005d00c11000d100011014000030007072000318401c1c040c17116141d00d1424802040103440c0e0245c910768100700406484460b401c2d04950300816929003c0b000940c00f0f0a00e44030902401200030481c0c459030050111039040b48100611490551110b02e80354070307005508a072606040304140f00c8243c00a001c1042001c04d80c1c0000d000c0c50b9080c0740075810143e0300c2c0c0b81c84101240c01e6441024024001050205040e0b0003401c0b107900300000c2c20210f88542c0313035948 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 923410044 1250 923408794 923408803
    0x6031103011e0f020715050f060901031a220309091404031709010b0603040b0a060812040b0c0109061b17040f031101110408150610021c03060306020a05040e1305 71
    0xc2460500c2c0d503c0c1d1001160b482c0ca641520041600520903100c800b4019568600801e02075601400e14850b4100003621460518845410380c3d038403136602c52042c1c040b042c0075a0300b4800030344172120034007815034402031881c0c3c00030105858902980da8044014503014240c1c0c00c0b00e40407201040004941d01c204004039411441d50040d1540318000300040e0b070342d0740807468010808194640e500023800414002440310a00c03145010350b5900300108041c40d0ba4820840e5244860b07181040d80c050f05001c01c1007000004e4010f007021031941d07000401d208809035105011512062400c2c8000b14030107201080e8180e02002516590071202800c030138070b08040c0c5030180444402c0c10028200003404120130002d403020740006401c0c140180382d4a48943d200d95400340c6a0b0000c90b20f40904c640031200092080c60700709156030406005030050005900002f46040c0c1400460740100305146e1605400400900e4600c02081e004140d0356820340c5403401c1c603110b126a22000381010000d14407414182c00810310100707 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 923411294 1250 923410044 923410091
    0xf030403170f1b0705042909010e06010c050c1302070309080f150a0b120601060f0507020607060b010203190305010e01050d170904290414010f26010e010603110301 72
    0x81ca200320b41c15240f0b1a42c605800342d0001c54100d82080b80d1002a020b8040050386120751a0302c020400c0c0661405100d580e000034403981e0104c4400101284080d401492000705140c021000e84a055402c1c001142410381151a144816507001400c1024968090403210280000c00c0150158108403244203580725040d1403000784140810020440312001540488409540588482400c04c03c0303c0055450f42000d01c036400102c0c820809070340c003151152044500c5194010034080c100709043e100c4000400c070011380f035415440708001c40c0d00001401c01204440704507035038000c01c05606000c001c010498041c1e02450007914082000ba002a5507a5498000d0401c140744044d00d494140001801411010398540d0940142c5503d05100c00c144a00005118800395418814450b10205c60781d010402440f80b6154422102d03000d00c40940b0804c0314441204406c80100180140c1200b0345084900301b400004ca540c0d5130310020010005060800c03c00303240124000c00165003902e0442502c0700791700 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 923412544 1250 923411294 923411317
    0x1204080730080c09031c180f15021e01090302120702130506011809020d060f0803030c0f0702040216170a021b060d06081e010501120219080f030403170f 67
    0x102d002a0502e00e443c42a140c0b0b0f03410040403102c0b1108803410401c0b004490f841c01e80300007800203814800b101388116465007111503071080030384054a49201002d81415400301c0704114000c444241d1020805900b03804902418100000344039121494042d01d02450364039080c3c1e10070740600065002d65103840d42c480e0788000c17010021034265241e0b00121a00c0d07100d200b281e00300944600c400f144400701c81d400790842e0341034003804000c041e4541600c0401d2800724810801e041e801000060301c81d5000f68080c048551507512414103010890380090140d800c4030707600d82c04501c05152140c1c28019a1108070710f10000d41240035107000d41c4a00000d4446003a03a01074402e010201001141c15142e000440340842c0601740c04101c84c80d283d20603d91912800c0044d115070086600d000200740d1818483c1c1b83c100c42d0386421156045906a090285580210350195200c0307100c2540082e030700401b40481840300c0343c0310024503615402c624012800d25501c0065601d0703046c045c4281199482820212003450452 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 923413794 1250 923412544 923412557
    0x90b090f040305070204090b07032004050d08070f15050415050907060c0f05100624090e040213060b19092d03061406012604060209061204080730 64
    0x7030002c5030260a896038014142e08d02242002a01603040d4450120440c41e0901c00c0e1110071403150412041c040d50090341e0f0f01410200034900058030f200024201603108840704007448030980c48400a4a1400d058a50311f141c84070304200811091b05000340035141140000c01c0720b0304200c20310a540b061280206001c0c020b40d500038100303210142d0a00e0201c0342c0c2c010211591840100344110140c80d940c4a800540c410030b80e4250700c2d0745040c1038080a118a19580d8001c00b0346001a111310100010340240e8005600c910101c902410714003941010f0140c5420301541c0ea11011400400341c428040e605040141100050051341d511040c101c5031040015944242c41400c0130b034076107500c20250b000511140c540010031120342400103069105030826203580e803040701446441700a02c20001c031200c8014501c040050002401d0f640a04010b143c050191420a04140b14190303a0000959041e110b0301c9011402200700040510210030003150b0702134031294010100c139003418421042c4180d4003407005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 923415044 1250 923413794 923413807
    0xb0a080415021219050f0108060708102c010617040b0402010228050705180711071509091107080a0509180c031605090312090301020c01090c090b090f040305 69
    0x10b901501c01251059808042a0401141c1d1268910741601d0808034503041400044030354503621070f039034100ea8216028000382e55400c9403c45a03520010b100e0000d400702e450004c100b0525070800f0044110b15540c0e1000c6560809507400e0f000380d4164000e00800c10801000342c15001a8114070b074205501c110381000702d440d6480141d081005120305d602c0aca811200521100b0359071061f11402d0580608161440b544e100d80501c4181c000300343d41080b04001041c0441e00841c454030b5280744000a500030755401e07a4030707410500075095103900c02100048220b002400092000d00c40e0b49400502c55407424030701612030380c440b2a5401504680803e00c0390214000302103480310200c0100d803603c02000d042240c034141d600007845800544030485c1803040c81c02c8503203469000700d0441e80243d900500405102040c9520511641d0280032040d07055502840540b4403544240030720101140b003141020581781c101030382501101d03643e00700c040c03283c5580c0091080b402c600329051904980c15282c01d40c1d40b0391 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 923416294 1250 923415044 923415083
    0xc1009170c0d050709140c070f0c0e1501080a09050601030b1f030b040615080712020109081b180601080f1314060613060302060901050304140a1b0b0a0804 68
    0x9040d480c040d00305444010800403c50042100c405403116040d0420411002802510b03040c20215021503a0302000c000140102d10000290b0030203503c145501d54680c0c1d22a034a0041401c0c0a8032290716040d4042901c13611980c0008400e580100d804000300400101c94a86a5a4010622014080c4030401020402100d90004810074200940c03c440a06540d41e140ca0000c59008590949280b883c2001c80880214100d9000d011941e1000081c0802414100c0c0304005000051003241400034005000940344400d1055241c602c0108100280307050302c407010300c02124415100b900d00090b110f000c011083c2c0c0c11080303540d000744000c10f28840b61b0f83d640c0401280290300000190490a120928290351500081d0044c401c2da4140c55543c038001d48248003600703840603030000030741c0010103120b0000594410405980e10a0040c1105012595131b85082c81c108000c07400140e404504000c1041030b201d07050001d1200502060720b0680c030306003000000600c0c00070050002886403055605950095 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 923417544 1250 923416294 923416303
    0x602031503060c1b120414011d0d030e0310050f2e0e130f0f150e0307063b2803180b120108010c030606020a0305030714041203020c100917 61
    0x445d0040c10f0036940c0d50b01d0340e0460300078000c0742a480b80010b150740803134000144400c9100c150a07501408010300c0c41700b166411780301e80c1d40c244051030b05071041c00907401c0d07110864050745006044c2c484800c0664144080c00a020f10500483c2c00c1a603041000c0310880c4543c43c4060108498001030401640c3d240e4441f410303c4000c0c100c902609105d00d420003c0240034010848038507281c0f040169900b400010350558050b0f81d8000080c002d5078005000034004200a03402942c0341c40d50340704403041200c094160802c0142408070006070002c66088220f06058004c02840c80c001041d44400c00500814080c4684440c1c19183d0043c10042a012170b111a0082461000040c150141c840358a81900c04611019800e0034400c440130341d802c1640c003440980c0207100e580e080d00e29590141c00080400c0c0c50548155101404080c02c101c0c2c2078280705600e04034240503001510050042070750202d25424000e140000c0ca4500340d1140103141d40515480390000d022030111011640101408200c60714001e0a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 923418794 1250 923417544 923417563
    0x8040f0c0b0c0c090709080a020402090a0e161701030b040f030c1e110a0806040201050309070f1701051605390d02060c0a1b1e0602031503060c1b 64
    0x241e030020501d02003030200451a030341d1001c000d80c3c00e080d09540707420707048800006903c81e0106607040151328001504294000307140d2404040c140298007030b510502181001c40403200001f41944e4180c020b04119400a5228800e03608030700440c04c294195201c01c1c1a071600030701300825a0f004100d42004040c0600f0412808540005240109072050281940401e03e807000441705259038080c0303000c4603e48024180b007a694800b000345600ea9855006540940c8090141e100720f00c9524030000b4040441040c100c003a0101c40512090036080c1d400c80d03403e440d00545071118004030701080c250b400d6030001c20b88040c51a80c009502051846681442c20b50b444001020768050146010104054000903121542070ba03990031220240c1c0c03224040e11030382c0104028000090103841103007540e001042003d06c0c0e90307400740041030a90703841d204000c0c607040180c841c2101c607a0b1b000300810103103101d10001c4100c83c01061b03001e808030345407030b41070600e05118000034170b8800007030103094411041c82080711044 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 923420044 1250 923418794 923418809
    0x5180706020105100f0803040b0c070305061306050c18060f0d050c090117071d27100b0a020a02040906090203060403050c0c0f060a03090501240e0604050708040f0c 72
    0x450325808001e019203030031603262250741220b44000807804074100b0040100c80419000e182010f08015089040341c0c0116200460741c8a02240800410810700c00140100c90103000801c48180c40d152400c142c680003000080c4180e07050000d103102d802c55900300040c2070300407258030340e41e0448505840020b00440c1046131710303036182c401084003141d014001818401000d07240c5091000d02120164030383c1e001260b1030000128040c4004010600348800e6920842000b45080d0300c44586420408031400d02902c01d0704102ca40b00c003444035201a48100700c02070514807150350316140ca10040650b1f83e065080000b4000c03907541450b0011b00035107501c40f06103184d005081d00c0703142c1402e042c020401e403c41c10325206107008041c4100701030303e0907a40c141c40c2180041c18450810404260550040003918400d0300d0355525a02d0301034012000402250420725448603000c003007030038000b80903c100f4005068038011481c01c003e000003242c0010f01f41d80c0c041c0c1d00928a0601c1d44140c40c16001c1d101c0998000f95 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 923421294 1250 923420044 923420053
    0xf030c09080a03080901050a200c031b061605130b1e0c0f190c18060b0418111e031003050a0305090414010308181c0b0403080a02070b0105040518 64
    0x2002c03d03521404550040401900901c070b00c0e21025514012580742c540c2c0c2c1e03590142d50075070388030341c0900540c0070380500041402644e042c800e0740e0101c1c4c0c00604480c8001001900500d0420000d40d00c04800300e00740981520341f0504040c80b8114048602c4494011b0641c021400b04000c26604985414051860400d0a0240d12150b84040322540c1c1c0444003003c150074040c60314212401f0100f50100031205400c02000c9a51900e0300d02900d0708824240504000c980c0c681802154241110b4018030042030310004501c00155084101d80440e04818060010900108107074061010402014001e951442ca4265602e0712090700801d41c070400d0303a000a14900540141c0c80606400802a0410a03002e8a0030b01824040c002c440f02d00206c2400000d0480c0c40901010780c1e64020301d24250700408020740780100601200030401d41011001c44226120700755481004101603010300351a4100301d1405055041c058907594014003440140a01400b030b55a420004516140a00c80c03413400540003130588 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 923422544 1250 923421294 923421313
    0x105121b040f2406110d0e0402070602090915010906110c011b061107120503070f0e010918050114030a050d05030a090f062c030322050d0f02010b0609010f030c0908 72
    0x600840f0b40034030400780030480407007410440c44004100191400c05565441c107020400c0400c02009400015081c1c5d00710380e09000e201c4d11b135120004518000c2c210b10f108004400d0300000018a0003440b07070082c1c420800b6000b0703549109400001c65404401e02420a404610444131a00d100b40b0007280c0080d1809040c49981c100402d00d080003040d41a0091303610400700455034406031030310300c4180d52003000950405483c0303809600c59084038000520501d0011020380e5502d10f00040700440c0d0841e09281c0c1e035110010070004c644500c80400144054001e0420502a91541a11410320700c0c1007405000740080003400c504c059a0102410581c420382035030b410582410400b00400001c8a4510090410305c070340c180b407a0b188034035000820443d000442c555560322034002c820318010200c10351024900b00c81680006c20602003804002559500e030300060b012001e000b820b4075590004640105003c0100006507603220350000002d50036400d000c1034840740b500003142c008460390300a40c082c0c003a58011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 923423794 1250 923422544 923422601
    0x3030f03010f0302030714060307080a06090608031b06010b04030b04060b0418050705041a0f03190302030d050709030305190c060f020729010312030b060409050105121b040f 76
    0x1c0b00d06a03070003a41156042502c500001d1420041c0380c100c0c80d404001170000a0140317209110b0103921400d880342c007041c010340c0c94100c04140ca6a5400c084503d0b000402c4031002d40c1190381034039203002d100c1d07402840e25500d001d4200310a40704600000c0d01d40c00c1074500181c18040c03281c0051103591307030252041100d1044c1032a000d91001c4e1010007102d460080000c0000d40e032030320740031342132200040b020700c5840d042081d800c12035090200d90f00b0607018003c0d017406080c421501c14290407124001c2d00550360b15491ba00d044022103400810040502c08075120520120394050162020780204514030700d901040c24070305484410140c0b4009005904008010b0114202030300a08040751007486601d10700f40401c08000500c002d00305000301b11a200d20010004030380e110488415000c3c0d241000201080350b071300400c25030381c8a40c00045105458500421660500b060112590140e01d4050001141114071160042d8a24608144902c1c0c0344d14803c088880343c1c1d44500321038040400c3c10069221030455 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 923425044 1250 923423794 923423819
    0x41d04141c030e060709331e0804050a0201050a0e150406171905190501080105042d020f120f010b030c0d031e17041a07020a0f0b0603030f0301 63
    0x100c00c0c00190402e50110700400f80090418080c0805490329800c590800c903000620b0440c80388040c1c5c903c0424540c1c181e000030811050540d5012507980ca40040285850240d42c80450700346901c00c00a00c1000c020101d2004a00c0340d405560902e4001c0c2d40300241c01089419a00314601c40c0e50000100d010305403982c03240c000a000701c0300f10ba1a10b100c01607a00c40e500c0031f02c00c42110403500f4003070040c45409001400da800b0550014031101e40784d280300c00d8078065100307c4000346c03c40704241e03642c0c1042c4800d0180001806042c0e40700845007a0b84249500c2040c90150002c2d007000f805100318000f0303102c0e240d0352022461101c0a6480c02c9440600e0300382c0c01c1d039020740761081060f0b01a0094003101c21060404000312032403e81c060311001c503407031070035943c604956003442e4001042109250301500001c81c01000d8500035030150001c1c001c2e00f148125803400c0c400c005000300c1c041d1b5001e6121030000840700c1e0b0000b408150003024495861b518180800d00314400d11000c20502c0b10000000301d0317150200b45 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 923426294 1250 923425044 923425093
    0x60915020a03050406180c1703220503070e010621020f070609060b010206131202012a031a0d0609051510060e06041d1b0c0120041d0414 60
    0x3242408610506e0b801d4141c0d44030400c2d800752034924286003c0c8104100c000c0d41030500442407040b2443d0075070802e600c002c0504001c2c56400144841c3d08108050320b4204a044042c0c60107100c200c2055140660261064103c40c90907507410314100f428000801856040e01d140f4130031010001d59402e03044c41d02c2d070005d2a00c4003040381c9407440c0c91502d44041d407001500a11900342112041051946a2248004400060341803002c6640300c40501180260400070341e10310400442e041c19407085664006001d54403079a00070307144c94013500c00440880e42d480010580c03e94200000040980341810603906024038852170900382031100301489481c044030315443e8110740c03183c0c1d100c50240304a981002003e00c103c1c40f80b040242c0b641c0e2121384500005c0a96280c100d41228800f208d02e4503180c0d460b4245402c020100d6000741d543e00700100c030565503c110200750b0404400410b141c41d00f80110300c00355041c1d50194417140d00d16400040e0030080440740d0303a05043c07a00000c40b8441031061034495189040107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 923427544 1250 923426294 923426303
    0x51309050f062823010320060a05090a0306022a0a11211f060f051818030f031603091a07021006080a0317070804060915020a030504 58
    0x250750305994a03002182d4140030352034441d443d03082010110200c002d00d031186500002d00d50340d038520344110f404003162540b5014003414002c0030550302d1404c08101100c01b0095007403180342212a040603950f502411640c488045050881d00da1503d003010825100303080c1c000401c11440018014083c940c02d802000d521444030344000f95445c071500c00c454032080c0d20324004112042c60300148146107031a41218400c030031a110858802c1c070302041740354a080b50310b0400000e90380e5440c001002c5001540680000f42030b01c030060400c0a441c0a0128000501c3c1d00c1c0340c00b0468480001050000b807242540300c01c03020054046076201c20441146440d181d00c00d0b162201a95030ba191111080c074000d0041030001c0f40c102c13620041c405100c0c40b011401003401000314045002d9000c070081c0c222a28450300001c0c110500040401e51040c0c41c002e4058209290303103400310801c01d0200804686d1080e0155400340d403001c0c000c10078400b185800000e49540352240202c2030300200f8000d00703850741903114522640c002c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 923428794 1250 923427544 923427553
    0xf090d0c050901210b1302100c030206060609011416050a03030f150b0a0c110a08010b03060705120106030c03090b010b030a05010e10060c1e0b01062606040903020705130905 76
    0x210351134144c1d0a20022040c031060521020071002050080d4043c0d40c1c440845d62212020f2401540082c915001442c0c038800820440d10141b42032683c1046055030106017079810a20308940400081d02c5d414080741c03c5001d00400107540003a0820b280d142d5448641e1000c11100041010310b00038010f010ba010b2101c00d070f10b00e0700c085003002100c462101411039013080109441d140c1e40c20000ca80c0c13100814403d4410125190704030710b490f01e416107000e00410a220001461444a03800c0508000d4007400c22810440b00f4010b9491420b8503a01d8070341101c0da18140010705806024040d8003500480b980903165007a00c000000b01402180c000358400d40c118202000349a8880800c050304132800d407000000c403190003500340f1040d8001e240301d120a500407101c0b03005a4010a12484c030381e9111310702c00c482e4407448100400640f0781000c0c0c603124840c01c81e1400c00401c5100041d442511400614051180d600e51071030006050003031010714041d090251000d403201d800311840a025040d42441150705109 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 923430044 1250 923428794 923428799
    0x90a0807061d0f0d15090c081e15180703050601030b0115020a2f0307030602071401050609060f040e0d0201150608060303030f10090207150c020c13020f090d0c050901 73
    0x707000c11a00b646003c0203060780c2c105034058517501500864000d031200c0e102d5a490000c004601e208030b402c0010700014005081e02910b161b105c0c80581d168440c4801c555102c0b10a242000d090170720001d41c040d5110224020988105044600c1c003c3ca40e032000c0d00c03501800e800030050105102c042c80c1a200d90641d0300d5010360502500700d0340c9800c40440a0030000701e03d411982c2d0b4041034011400b400181c19045003001007804002400e00c40355a0007100d0b0b00e0341c0001d9032010884116001c070f0304007824000802081c40c094011a609500040140340308078000311000c00c071603940303074091008010190200d0303101c0d030000070000c3e009101e00d820340e4146181c0e089000584500c01c91203e1f2140c100507012b1415600c6042c20355402a0b00904038445001c40351401142e0004c0d503102404200e40075107a01d1440b00d030b0340d44d214401c0782c0a500c180ba0440d00007102c91100d60301e800c807072901c891500000043e1b449a045034000310501a10021a0340071988886101c14404030018510640c0d008503107041c100d0b40d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 923431294 1250 923430044 923430049
    0x6070609110f0612071103091509010305130809150d02030405060609160e060307030216030203030601080f090309090405071703070605070e03060a0c0504121a0702071a090a0807061d 80
    0x40c060b00401105000300010ba0114812039400c581b1030404c800f1242012510400282d104c003030455845144007000c10020300a6a141c068160495041e2281102e4131a607034950f5130f0203100d580c440c0350180d000d41802c540700d000828100c1d110110704810031500d03414249481901c0d45801c1e034603c0d10500d041404074000d8400312000c0052001903865407401c0040b81d90a204898100500c01401d040c1c0c2409050811910101448803035407080c0c1c044c50366850244000b4103203c102600d44417080c0c0080d420040b0441c40041110080325080b10311080032381d1039240c041d2500019801c100c842d5401001104039020340000036080041c41203c041c8103c2c1c1ea8140103c5114010f1015243d040d4040004501030388040d5104901c100c034a890260724040d245c400403507060004440441d42c0e0340301d1151a000b001c1107140519000310191014010191a007145840301e22502c81c91003044c64030020301d9601e00c4d03461910450081684d1015524107554420000e800c04016011040030302105036032915091 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 923432544 1250 923431294 923431297
    0x20708091003180f02030c030102031006090f05090a022b140f0f01050d0c1e0303020f060601050a0509031e01020a08070e010915180801021309060506030109020906070609110f06 78
    0x3c4201c840035641d4001962210425400c260300c003617825010700405000e15840c2030004501c5140f5900b1206007152800000600031368140e40101c07000320308448240807684d15098038582201d581080503880d19910b208000300b2010800008500002c0402c00f81c003841881c0c0c000041c0e40010140c1035141e035848254402004904994420030103a413a03005106500c1c0c0b50041d0000300b030044240d4440c142d00d0356031010718404114014404981c0c1c0c98400c008150b410022808040d24030000f03170049040040019100d40145180417003404404500d400050700c0030041030038502220302417011b800c0d02d0030348814002c1d400034086500140c0d001c000120390a004014030488410184d55503240300d450002010b0b003000701900c810041001910990500c2003142002c240506004400182e13562008a040c40c0424469885101d860781481010841076441d0381c00d407811240310040c0075940c0e9011000080e0a40315054000340742c680390046120501a1241110300d8100007500c0d4614490803040810819 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 923433794 1250 923432544 923432561
    0x40b040608071a130e071103070f0c060f0e1509030105010e041a0708011203121b0207140f1002030432040203060303030a09050715031a0a03021c0203070306020708091003 75
    0x2504d650580410094481803102c503401070091074200c0f4600200468507007954043e103015078003650403402403403e103c0701c02414401001720741821040c10a40d000e00ad400300c2400403d062058001460300c0f0f0084001104a07401d0b510014000c00c519030b1256072400c000d103006d0720251860140080603003c0c154281103200e0041c241c540f200300f0540c1ca0b261034005207540c0300344110100b100c2c8401d02d46a000307050062a070100f01780d0603407241aa840b0940285410001c0c3d020081880540c480301509440d00c4030212002d05090b100b000e01261841c1080e491031080703038010303014030845c90780030050326416640206425008600300702d0f40300084020001a40415110382e03030315420400126803a8001d5a200802040c4244c0565000e950b6422450b0148040c0c420340c0d20110741c40b86024500780c9071000c0492001c000071621405400d007103401003042400440f80c8522440759404c01c204c2999010004d00e002942c0c0b114007556510424640b0507030f0750f0420800540110001e0384d105129a0187c06090300c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 923435044 1250 923433794 923433817
    0x30c071703040b071205090402040e0f06012334060f06030b1306090215090a050307030f08031e0c0c0d0c0305030c1c021b300306040b040608071a 64
    0x90090503124850100310050385d800500004115000140d151400500f00030720948040d00590b20300569208440c1400420560401030b084820b550f00d81074100c100008911a40c580f29222008002040400c1b072102542d1482080103428081101208038510720613980b0401040c003040b02e20b01950000d036062400010500720406000500d80b80c00c005c000c2c0c085500802001c42c118607550045400a022403d030340501c1200040e8800d8641402884074000b444c0940c02059102c2c44c64072046000b03211554002c0942c24000085a184859002072143c1180810031142060605520301041644941c500e98418003440800c0600710b40290b03141b05840c1d0300340d19203600c0c5548041203006582d20503445031035040010390131442207101910241101e200804410804000300c850054641213030303400d2840c1c19101c0c8400805c8008010401400441c6218800d182c41c0d0b11030200081c050801400c24503041032038a50b001503031071000520750301100d10300318003120310b082101e18503200e51040c000c4940b07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 923436294 1250 923435044 923435047
    0x190b0601030b03100e070f1403070528080d0909020a0f0311070c120c12030e0d1a070804030822080702010306050a080c09010b0306010c020d050f030c071703040b 71
    0x200554026081840e00500c0202925529688079003458104d07000c40c462007643e80c0c80100140f05031320003602c03d44064403500401c021072036030240000303950350010b001c0c2c0c900032141c882d02c01d442902c1c242002d8680041001c680046191600980c668602a1605c0e00c0009401d40000081640c280d10845842203e20f503940000c81c1c680c4c00082c0c010b0b000b801d03c0c034404074404200990106c0d1241001c44090708400541c8074108826040400301041c06420640241d4400b10030715001030b4100480140300b42c01502e10800c000d25904200b83ca40c2c9206070035040c041c1103e010000030343c1c1d01c6203141d4401c6120b6140d2200e9a22a0803115800500d1650100341d20011803803c640400c500348050401d42c1d10500d401b21324962500c0103e20318072025400103450b82c6c46042581c40034900048200d0242807610149421464208002003003d20009406030003002144041c0d001d1080600001e0504d40701034080b20b544030a9072000e0380c0e0b60800c5d4030078551102a04003c2181032035001c0b00319412510b0201699 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 923437544 1250 923436294 923436301
    0xb18100c020f131505040c050a0219020f0630060d060207080c0d0906090e0f010e09010605030d020f0c0603041205220321090503060705090105070503040807030302190b 74
    0x305140d0244203e51011543c004126000c1c0359008003e000b11000c03402011072864203080c0030507100200804018031100b403000c640ca0307580c005184c0482d03002108007129501d0711400480c8940070240c5015400c0100000d610042d682c1c0c6441ca11644002e101425048510200803000c8405003551219404040c1d13010590100d40745170060420b0a008074030061510303007008091407802d40641d420305e02241c003600041000c0c94021200c60024039031a1070b40012460304000422503003905007d040a0f6007035800124121840940c0301e18051701c0f02a045900b081d136594000380d03403800c031149030012612036501e07210107a0400109981c000e643c082c01c400c0481c1402401071350340340c1101d90440c2c0d40302d110360003140700d45c144480c1c4540114003c107012a000d030b008940c884440d080d03507518001400b400100c00c100c95100042c106500c070085103000d544511480380100d45903c05c86e440034045220100c5d0108007000c0226046049034820b8084030450341c2e160f60220415895540c0240c078001200001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 923438794 1250 923437544 923437549
    0x191e0e01050f13030b04030206010803030c040603181208090f0f03090405131203090b0901021602010809070b1b0613052e05270c030318040b06040b18100c02 69
    0x58140b4030642544035060603258505200070f81515401541d40003241c07020300040c142c040c0019400f40c0403c201440c910711703112802c9031051240e882a2401c0641d102044c4007080240d80050b040c00d5840003000f4005507030000d0003080854240d50900e56409848038403501c42400154a512070304450300590300b4490108200401401e0080c41202518081107ca44c0003c000e491040c04180c8980c074000755440b0281440c0711001001840a1451381c8100f0180d00c5100291049007881642403a008100e03a40c1c03003442a003014100c0c0d0280490607000b0034401c44c3d840c2c0800c41d9081c190901005c030303101580d804080e041c1111040e800509a45c124a180040c0d60109001c40f60b00d0b42104512070404403072840c004000c5450413a05100141e401e0418680c00c900000003810742c00340d8150060152012801c0001d8032440b81c1040b81c0e954051912143d402c1ea161600701600700100103120f203803030700e07582c8010040e42d6104041e01403000880c150101030a01e400e06000103180055a6070003403044180d400e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 923440044 1250 923438794 923438797
    0x9080a0c210506070807090603091505100b0c030d11120a09020f10020c01140901170912070f0302061b04291303050f0703082706191e0e0105 62
    0x15014050140e035007031a008074400f008042e0040780030f40d40f802800c0c505550000d01b800300a80003d006c250038059880d0100d0030030340317032989085040c00001805403507000c81541540103650110754001d20104103031070303240f0010000c1c081524915200348442c00f407a001610f500e100390150701c5100040140401d64150460f4024400c10380f019009a035110540c01c00a00120000703000c600051340003010b42407855030f004900711a80b90100c0882420b0101d20f00020b007038481001214400920000001035038881e040164140040c007030f4620b00d60701d03155810062901207a03100140c0251203030310045980a50004042c03450743e61010354250a03d4200074000d80342011f0004d80c140d08030070b68174201c03d8a2000d41f0040500b0170001400b011036929501d040da080c840340180030140d81d041000200082081c02040300c51030485848401e10300ba202c1810a2b14011482c0c0c42c4a41082010a03924a98081e04400c20f05001450f2510200034200700c0caa451b2243c0040b40703040003c5c42401c612140c07540a1340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 923441294 1250 923440044 923440079
    0x60215060904150e10060503010c0806031002090a031403040f0e04051504061d0d09090207051c0c0807061e0b0315130209040507031704080d0f11160609080a0c 70
    0x4404200880141c52043c40d09408114003c80b0941e1046c04001030302d4240300300c011441041c02e0420300e52030450002030311001400013122080781c00094105123951010305a60140d64000002d10381d124407203003541d540f0b41050141c20301d80414400f0100c0c005040b4600c003442030354000c004218400782540203c3c8a400080d00448541780c88400400d48070003000300c010a1501100c00600c44514207907001004d5110551040241c2481000ba0300b010a40128038800d00c1c0000d540d00400c01440072030111420414428003510000022400004219007a0000c060422139040111042207002c400f010443d40c000c8241503069100245500b1500091a00766500c8984411a40b00c1c0c50030310340205012400860b012510398001240520030030004134200503c0d80900d00000d82400d0801075040c0d075071310b00c0d48510402e00c80b09519198900c0d00c989424000760b43c0600c2070719404440c5040c01e4061481601503003010271a882c2012aa020b030000d041e49200741c00c50b0b0700740031013490203289295034030001e27 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 923442544 1250 923441294 923441333
    0xe0a0807061d2a0d020d0b060f19083d0e0f070315020f04030308090a0606091407020f1504020609040c0207091803080604051816060215060904 63
    0x400c0d94980e001428402003000e041c081001401c05018520882c0081c03000161044c07094559800c26400350300c41c1070404400300d6000041e0406512502c00140d21b0f486420b4480d580b1003844914001441c060038401d01c00c403240750003184d0410582100c10412510303990107000800403112a181000201495082124401c0355400610400c00e4050035041650310100d0028503800160208100000000050f200000d0315008500b0000840101e0505100c1c900c0003a04000282001c10751151061028020941e440708041207010313506c0b41090f014103c0c4043d40401c102c003881c0003990140c00440d50300d40c007501a0003c1e090042024a8104c1742d05030251040e6001a418000943c2584075441204081c04a580060401a00d8007050b081601c41480d140b5a0800040d103c4038006074002880c0364025400f21400b1600f50703100108403082a0502c0d10b0b030412031003810400720740e010750078164006960036642901c80e4200358600c0362030760010544009400080040000d004550802020031040010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 923443794 1250 923442544 923442581
    0x8090d0606050a080706080a0c021905032503030b0405040c06030e030c0607030501180e030306061b060103060609151217071a0a060608060a090e07050901090c030e0a080706 76
    0x260004035404643d16041071509510140c410300105030071200c05580081003074001e120900105500039110b40c40411001204c0c030400720040100542401520a1220621900c100b4503589001605405d80d1114040e80800d140150480143c2003501600b4403c5800031002070000380b811303c040b4010101050401c100b40800d000c401c040c3c041c144189802012103640110313807541000320300b1081c0091045d40c03212051902c240c100c01d885000c02600d600c0001180c02a031034100d1480b0041700c00d00e801c400d080031385c00341000100403c800c0368404400e4030146141080044103011000124007010301828010750018006071001440c0790b4028000840030900f4a8141001e564401030801c465208044881e41150100020340d180c07031007a080181100c0c501842c0c2d505100001c02c0112100340500f48100d45c84200d00c0324410000c0018800824024161100c213680d80d041000040c0072a00a40340001d04029601d4038400c00051201c80705c5810294080c6002d1096640c40c00401030341e210320105c20030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 923445044 1250 923443794 923443799
    0x1009031101020a0b1311030f06040b06010507062a030603110d17070b06030d0c21090b0c06040212070803180a091103060120030a0c140610180908090d0606 68
    0x11814028000d00171502402058685481c0c00707a1140c4400404074026071100354a000030420020300141c010343c0000011496498200c01269030384141c3c0005081709040c003510700d400c81c2c1d01c80075041260303803000d05d030300c1140c0d0401000310180c0e00076200103030015618800c18516481d0514801d50000c1c03040710480c40294000da85d0080c1e60300001e40580c0c54006090410001e81428040c0d0105601e40b440c16041600c1690f0361119003500b0484400c1a1a00049c90032118070701440d41c078005401100ca0490701c40340001c0141d0303074408040390f00324080d515410803c1012500010030f542500c0740c8202a6052040000300e1400500b10410869481106404006440b286070f10074410320602c4084075640d0313032814400140001c08034518001580c02d60044d0400034a0307012003940c040409901d00a041c49100e41085602400c401000124a02601c0c0601924111a00d141000ca4400b0750034000800819020034049031981c41000c0c4c610301c82040240c0d96450912075110000d40300f0100068001c0c3c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 923446294 1250 923445044 923445053
    0x3c06050103110901081306140f060910030b04030e090117010e03090a03081612080a0e1506010c0c08010c1806090f030f0206070b0403020d110601150c0510020a09141009031101020a 79
    0x40a40b0140e666070f901c038a0501c543e00702780b01c0c5c006600c540281c50f9072407075080c00c00d060007031041c0360312001c0c00040080b0046002c0612580000c184680c00a281d05240c0d6101c44040d1020708404a00c0e0050750310345032031403c4500c6d020090b20310001c0000c000500c40381ca5a19080315a500094100030759000011500c0001424003003066480c400b160b0320240189481c17018001100d40f40800e4506030ba0240030381c0a50702009a00041d8445000e00c2c0000403284e40d480d1980070702c02c45401c039003607550a08048061440d4081c00201d140d1003000350b880101030780c1e9001a1084680740c0220f21800711f006030144042040401d91350b11040c1f01810315850800740c2e898500c2c50000943c1d0840068101f41e03d20381c01e031644804a1314084440c04040d0080394034010200c1944190088000306009542011806114007030110341d1004005d03820075903035404c0e1036200038002d456038051510241c640000700d42c1c40741041c0c2060000d11446484224100c2d05544480618040b440b00d42c03411072140740760680008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 923447544 1250 923446294 923446301
    0x15160e0907111c080609070e09060103020903010b06071a1b16080927010803040b1801050c1203070f03020f0703030e0319050408121c3c06050103110901081306 70
    0x4070f0b20395960602c68180b100c06c100005002800c2131007002000120130340e140e0b60326480507400242c01d0800503501c0d001c00c40400d000d85294020150300543c0880d440c42403088030b900b5003402d044241c00c0c1c103417959558840c4a00074500b0840c0c0340d095100500c000c5518500044610405c01e000c3d1401c181403030307507884c00103903006a003030004244100c4030b6084c600655070407151f0501410b280c0002d1800d1034100b900941e668050800e60590001d8034035440c80d0140d000c0d00c02c03100441d00e1030b030a40700348203103c1c111124581e000390745203000903003120011418a8404c0c829190003903000400c142c5024001c1c1c80803006012601042c6c90719000030400d990100900c071305035109a05140d155075884610344003815084c00140d4000b1030080b541040307000388c002d404501414034640804400521185501146101890306107013250a004806080000c0e50f280e04075000c00481400c6030620000391224011029540c04200e040e482504c01d1002505941c09120055407000c00201c80030142a00d5490755803e8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 923448794 1250 923447544 923447593
    0x70807030f03050a0204050f090a0f0903050304030806030d1b0c0905010807081006060203031317071a07020a020906010c031103180a060c0c030b1815160e090711 71
    0x100710300a840d2446a0703014081c055000340e03845811400c152411000c141821580c005c118428808180000c003903800f283e00200503c98000000c0004180a28014000d580259000d80100e06144002840c51500051403e5540b00750740d01d00c00c2d03010040c0308520204461440403901403041d080c0104100703c0d50f101e240d00030701404d030040440519084485040100c0c12500d0304400d07041c2081448460303000411280c111004100a400c03220380f07401c204402d1900716814281d002c0c0001090001d20031080b40500c404524100000f1094480901c2603070b9074004000300170b410032003400c00a20b485d0301401309000e61074003904126105241411800d0300756032100044a1900002081403685030622221640c040e101a00f8800c514002d1602d07621044241480020050303110540004c00d41c0e44007488184144601c8400c17030b40900d003000c04a070b4200f1400c40781c00d4281102c045140345600c1c440d01c0000d4400001405426a40d00c40a0080f50741540d00d620146040c8104018010049184442c9014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 923450044 1250 923448794 923448797
    0x92208090f03100b1011151e160e060307020d0509041d031e12010b0d020c0a03120f0b060306040c0c05030f03040302010609020a0f0c05240405010f050c04090b030307080703 76
    0x104e41c0d90700010030000f903a04146200030420101c04003081c85100150904a4010480c0710100c030b80d44280c190320040260b8503c984c13101e0120820f02c288040420084541202d0548400f02180400f07000e01000b404119002e50040c0d00c145110080280120001e18000202920124038404000f0070308110207034040281d000c030791000900060454566010b07020780000614098600103c8403559003c691040c050905034580006511540d00400e904031041c08a0700c10607582c004095090141c0310014010f10b02e841141400300b210207045841c89550794001d8014016402c5413120000e0000410a98840c074041c04034035907002011980401c0034110703410207201d2641d501d10341f41c50024250303085548458041c4c0c2c0144541d600d001e41000074008150700a1409030480b120b6400d1007450801810001c0e541c210101c84101c846801d103d41c4d19100390b004070000d00c429003c080e41007040321411210021002d00a01080c070119829403c10004407000804480c1000e0b140d03201c603030315a8000c010850 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 923451294 1250 923450044 923450051
    0x10b062b1506091406040509072105010b0903070602010b0303071403070b04080a1701030c091a090a0204030606050a0308090d08040b030f010e07090b031b1b0705092208090f0310 78
    0x101391400c880005441d000d40f6141c3c181454500418000d42000c1c11a0061103c045804440401421312100d05202d00d91024040d40d43d40d0b205080e82a407040302d0850103401540800f03d9a035005010308081d00da4054020b500d0f210b455150a0340d0301413204884066400200000303800300c0d002c0418280900d002d14903083e0350300c4415a024103200c11040c07818802d03d2180004001240481000320101e86154901041040d2000300760b1080215610502d9440140d84040c40510307850396005d041070701d01c90301e81000525125002c1040041e00d1380b100810456003003020340c5c2141000405100040d10031480c050030b00703440d42d004080c0358104940c2e0316000410000100484501c800c115500500701c0e04014105d2410990381480c0d501c13005003a04a021100030402e00500111011a1031040300c9450100c0c07003d00180030380d512040d1602c02d140c0b05150715401304041881440e04403c0755000e04100f01c0341c00b2080e41d0341c2c0311103801c001910380d4020801e41050f4042c4e2000d000612030a807800c2da000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 923452544 1250 923451294 923451299
    0x5030705150106081003120302030c090a060908010f2a17010915060807020c060318121e04210204060b070c2405120402031c05090102010b062b150609 66
    0x134903080c802024008840782c11001000410001c1c0c03040f1911010a1902603a20394071130340501c00c00c0c801d0303440c529001250801c1c0011042d901c483d0303044c15100480d0013804003110382e00091090310180b55452a0751003041c034a05c113408002044042e400c10041c01c14000c0c080404030800c841c940240e02401145449010404c0f600044071800030152000e414890070500380218000c0d40c812012014a0080000101040031500e1040041d01005c4180088502070204245002e2290300304070100c070740300b008c65960f0420f40340511040c0c0d800d580990b9880c0c400caa80307080700a14241b0212070180c0e0015910b02c0e0202d0300385000c100400c04c170390159140b13044861038142600d00e00600844c0d42c3d01d031245001f014100707060f4048101c401605ca04000658281c86900000303003400d000e5401c0c0040d1f00c40840091000719008005030100d11800d800070801114500b091206a114075141034141d040490400b5160314205400300c00caa015002c3c00080200626040341d00d80c0d005500301d14082041c52204 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 923453794 1250 923452544 923452547
    0xa3b0708030c0c21030a0c0203160303020f07060e0907030203251d0a0528051009030c0501050a080103030503071e120612080301120f0203030703110c0306040c090905030705150106 79
    0x2585106480040f84c0c4818900498490180d11030310401c0180f654860360030342d902081a0b0141d00c941d0500144115964076000c1c0d43c074a41c0a142221a008040000564600980802d000780a005c0c0040b40d060340c45d000118025840285000c0c90b40c6035098800510303130021190306403440c070180c40321441c44042254061070920b01008451040588000034072494035908403180c3d881c0e04010000d411340d0b40e90b000031009100e090f0070558104d9240f45a1100895014204a0450b4090140c81c0e440319140d800456031841407440640c0800d000d00010000030f4402c000a43d803168071490201000d6544003100c10141262040000c0082e501b030010300301c21000c501c14030008040015442c0d0564055603a000c8660005114400510030392206210500c20304149510304694003e050302c0d654000d0749400740c031030f100d1070220700107610a880e11001c041c20000340080c0207a400c112134540403031904480001600d9141003c4030710b0b01084c00300344005441000300c81ea03c0348d00c0181111556050100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 923455044 1250 923453794 923453809
    0x3050a05060a12140303101502070308030f092119030504020f040e0307082106010e090a0e0a02060f0a260103030e010306050d0b0a3b0708030c0c 64
    0x10a54024501014445103a03a0020900102c0e0144810200070078050b040034243da5000d510b400016010000030032100044d2414940242c0d0a1090300b01648509054226682c40580c000200404400c1010900e48a03602ca1083e0780030000d0030481d4466262403c50310b0242400301302c841c0c088100482d0400c01c50100b10068a8125202c0c90100050720b031940010b00b100b100544010701440c4c1d910401242c00c0000e0003103400e81a00300c051035aa4900744031009540d400f4041111820f00c40140224205602c02c00941903481c0d0014106005900e800504e00000c201220358103829100310401c650040e2580f2000d0810240f02d2180140c0b560102d40c40070b02041c65816513100d03c1c0b50903110a551040305440504d05603501850840106580d29005070001c080d607400a81d032055585052008002c00d14034014403540440001340100e40c204101c4d000300302142d850680315108075800a10948a1800f014040f41030103400311000b03241d03511a0315055501214443e015608503d4000145040042c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 923456294 1250 923455044 923455051
    0x9090b070813030e0d03091511010f052802090d0c050a060509030703030806030a08070f020a1715060414040f0b07080c040605090d1502040515070f0f052109010305 72
    0x40c0400d41c1142e00e607600504000d030a80600f84950b09030fa12200a2511850354a00070b42401158080e0320081c11501034201c900e400450340f11582401c1c003400d00100c06024440c001e16481c100e07403228004401011954214010a018066509205180300340c0d8880b000030f59924082d5070111131442c10441480200b0099401501c04d200c01000450010303103000442d581240c0d0180f900d1103251b20b42000003810b0141c0c649028100140106294090000003841c6064091080315440251603498030000303505040b803040c02e45d594000c1a1143d0b8890360351804654000f80042000607a180301c000c20a641880980d01911b20341030340020f040030040c3c0c54480d01e401502c1c508029182e40303081e41c040325152042d4001c010404c00d0101e03a90450351230340003c41080a034089421554588040409402900030384141071240b0b0802108915000c0080100c0f0300450300840c019851050342c2d1a4502c0c07041303410008075000e1240211007451188034181c09541048581c45c1030f5601c09290000505803000078 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 923457544 1250 923456294 923456311
    0x10f050c120105062a25090f0e100903090b0c0d02240a090f05012f1305090c0c10050610020312010509071101050109060305010e120a08060a09090b0708 67
    0x4000448500010a00d41c5c00c1001c80c5400d0750125420f020b20443c00c03c0b5020255040080109850001125040980d981550314881c000c0042c00e480e9040041514103100e01c0c0c4d01540c01c55102001c00c2c080030f40140d0401b50090414a0070701340e4450724030311107074481801401c0580191801c92038003503040c0f044210700710700c0c203d40d140d40c00c0440f604490550300280c5030031402941c8603020004c000d11130000406198112000300030b02c2c0d4143c464141c088411103180b42c01d405200101e5000914000f0903611200d0542c4000081e9600344400e0103030b10311002d002c60340802c00038480c2541048041041c0c0b054541401408645810030b101030064001d0003603529020341d001400045e202018120b5810b0454100b2034142c00e40e030b10b4800c0c040c0c90810ba8805201115400c4c00300118200c1d02c56040f9004403482180200102d42840348070549a0800c40429805854108444112140718440d06500b0003001401a0242541ca4501d6422500741490440303144186208215080b50880d51041d44060f51 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 923458794 1250 923457544 923457547
    0xf060212041e0e09010b01030b0118031101050c1e100e03030a0911040204080c090604050714030a02040b0d0b130204050307180615021f060e070f02010f050c12010506 73
    0x140c032128809014501600d0b08403030060310390700d2400004050b010001d005031034403e807150402248083c040d0001154242c0072904001c641c2480d540f00317015050041070351704d0111203000e08503602c0c842e00300c00c9200c0e02c3d4104842440405c005202c03d02c40c1c13110050742e04400247e2015851142800c244a441503c0200e40c6010b00514920b01d020045981c0701d0b005860000d40103803d8582110070b40141e0004607040f900c08200030601500000300c1d1003140004542c5659070ba5140303020481030b560b00b125a000020b0f44c0d60504008000b52801071904690000c0c005410503845840e12030480d04000b0300d100100b611010510b0507800d142210040d500c0501d00e043d0301c0c081c2040082030317584134180b0400b4103198190041c01a5200300d039002401030002d4402e044d00070100020000c0d0fa480c14564581c4880542206078100c01d0001e01c0780404884001100c4041d540d03442c0c500780c5250404407a590199520b84c03185e8078000c041341c4103952081d1000c0341c500d03456000c04050148810016000305004420 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 923460044 1250 923458794 923458813
    0xe0312090609010b010e01030b21010903020127020d050a0f111036120302010c020d090e04140114090f101104030206030c04090203090a120309030807080912070c0f0602 74
    0x2484400810707101400e08000c0740e0307000100c1c080f03600d102b4000b603200481c1403100e020000104064100030400c5001e54024081c1c11403604100c001100e404070000c3c06041f010440e040103041460920100c0703402a4107a480faa03c035034540380070089000f1130440311720640002203c0145803404010452100718030303009803001108d44000780c07100c40418450640b2601410b4900b20b4042c2c40042c080a0403149103074080780d800d01d01e4064042c00c03c5140303210250288511146055110780c22460446207a0044541203032260345900c0320201c200030b480201552503400010707281440c025058003a00100300145030551840000f00e04080860525140c2c20b8180000001000c0840c070549d000e86e901114910703aa030715940203821851049500104210380040b0401c0000352001c80d400e2111801014080075400264000710b0441d0001000200800c0c01840441c144c144104080d42d80b20704c0c0c00d01100c40070400c40401c0400d94110090450304072a80c10414443c4c15107990901004180a000400d2002c3c2e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 923461294 1250 923460044 923460047
    0x7020d0306140a0608130f050325081e0d02130614040e0a020a020f071517041e02241b030301050d060e21030405070f050d020d060e0312090609010b01 66
    0x1540d226803020060a000401e980058203650346c05219071000041181c0072051614944070f400500a000040e00a800403040035001520300310042035020035010310f01044484204d900c1c5441c60400e0201140901c100c130f401d09102d10080654401e5a0b9200000341c0c0342000040043c0d9045d11941300301030f802d22041109005041c039003600103d014401503100c1b8014030301249080c4480d10241e00c144685900020001e02c010201c04001d8600e5031901c0218120450110a0311010741e0018404241d040020180041d038082040c4010310040031900a8940ea040300e480c0e1848404c2c290b15070361000100b00d1182c0076400c2d521395245100c00051800c56150900240644008032009059583c1315034001d1450941401003c51400c0042003842402412000308031840d00202c1d01180c0c01c1c4904d402c0861004a400f1000307007101d500a24a1054111603428040c407401c2100040f11920785400d040e01d000c500c02e1005d441c40c0c50785003400340c255160013088039181000c050315400c02c43c1d141c9030942d100c0381d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 923462544 1250 923461294 923461309
    0x4060b010509130b130203010b0c0127030c11040614030c0409050705092a03010302120705060f0f09040c08090d03090203060a0911030a06061401170a090206040305030307020d030614 80
    0x94903c00000191605010301080c1802c46001c100c070760301403001001142d040ca454020b40703051003a850081102d84107500c1004800c0b24000845410401c0d030241080000e8421555084c040e803140155009601002010909440da240c000d5080c0d00450b64180c501c500301004441e0388038404031000e12140b005d580b94180c65003005d00810780901b02c42d0340020080e00c150003841e880d0f02031144682004012140c3c41d40c0e402d420a00040f44526080002081d01810001e582c400381c0340c0007405285002840c05100721642e00440307403c41441400d006040041d601d46c815100320f800360f52116100b5140c1641c940341468150884f4100385480c4c0902100545c070f00161141d4045140b91001512003010f00f0401c00b00340c0b40001d070551601c90452880300300505504100c084403441113032603000020042c0150754100c038000d84680300c00c4802000426a08150300002283c45c0050407541ca015125120182175610480341000507901ca4480f03045000e0707242c40f13000020080c41024011a000810008013038 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 923463794 1250 923462544 923462569
    0x6181f090812071a04051603240218060c01060504060902130e0c040b0901052a16080c0d110910030b161205091609051905010602100c0c1a04060b010509 67
    0x584c504a000141000420410b000c4148285030180c2c0c0c510342e0340d280580c018070401061030000f80021258007014111f6000392980c64140284441011483c0014402c3d0703504002c0f00c01c0141c3d03489640c00030b420f40380d81c0f08a00181001c0c1a000d0394030264842c0c04004107003507521000c102c0c4e41d01002c125210780c10009440554070705041e01c0350b5074042e10700105c405001301d8440c0e03007001c0c00e40404058214410070101d411041c140d02504c003851010004214007107094400d41c5402c0e0003001105101d03107400500082040d20649080f140d80c1c40c2d040c0440e184400441c1c00007415100c10200340148882d40344803641c440010019501c01918100b401010f546d4040c1d402c00381d41f0385400100d03960036000e1102c203665600c980c5403050f41c2a91410000c0c00b0789019501583c00c40f0042282e00c0a0440a014080c16034441da00100a0b040c401e103241d00013003014501074010400480002c2d0b0001c0c10507401c00094508041c7d9403601c80c102810310004846c05410b20074107002c001c01804803142c44440308043c0c1d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 923465044 1250 923463794 923463833
    0x1207091a0a2112020a061b0e12030d140703150f050607020d0602031e090105010e011707121101170403080114030c040516170606181f09081207 63
    0x103408031040e1068041904040c000c0021005a03c0e9401d81036000450070469800380c2c038203024400400e24000484103250f000070001455201c10b01d402030a02521445850394198210380c82c3c08545041c2008840000c1c01c2051501414402c4c456800c0d8580141c83c42076544001079030825140c406101d03100045031050314000d42c00421a90199503880000f000794540082040d581ca1034a0000042009504200c040b030410702c400205599400500c07403d4180c6041d1840c00800da4201140480807010b00301445c18039100743d00380030500f2a010942c050003948a5840c081800b440c07040094805d0b041e5482003030500102c5420400032991001e043d40c11608100c0320100030410a1000c40e00f040394860710141c00c1400e040611114201944d400840e4006a56661450103501850001c492030103072885035110506020000d041d402c4d9180e000220440141010b502200641035614240c00707880039400459051181081003103010f1151104200592308228a414907907543c940810044d10a47c81 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 923466294 1250 923465044 923465069
    0x9060e0a05010b0d0e010212040b100b070f02010513080109051e0606030a080d06030c030b040203010b030604170a0c0b071d060c15040f020a12020f090f0f060109051207091a0a 77
    0x1e031171000c2941102c103103c0b02c009100b101441c190a01d030b8152003064622a59030341d0012000182d003940502665074896100d46003c40c41001a001141d90381c00280c058500c8071902e24000421910900c905041244200c019000c01d00304101d1703140300603401094603007943d0071002c100002daa40200e03640000d1940641e8940e1100c1c03861014030b00a2080e60401001c0800381e000220501c40c404032440d104034400c5000740311882002c1d007496103034a0281d40041c6840700c0b4511075608031961002804c1c1d80381c41c0b4904580500c00580300c00745004801e55071407000c0b4020b201d0f03c00c0815044c1d8800400e000054a64901e003d000c0c190381a61400c1b410f0100750003506c014040f408000c1c03214140031466800a00b00a65942ca43c4a858807140180000b02c0c410f030030b00c1e0f0a0703410314200845481d100f50200b07000440c007656160020000c81800620840c1000b145401c00703d03065482100c420340d02500c441c0213280c1c950400350140212805140c2e511420701c03a800c4003032110383c0c0c1c040c5c1d41001ea80c0100c5018 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 923467544 1250 923466294 923466311
    0x2010c031a1333060f0804030c0611030c0c070f0f060804050f030708120109060e0103021c02090a090308060d0b04080f130e0a0510031110050c030409060e0a05010b0d 73
    0x220010010101c044416070050fa4030180000c0c5965030141000809031240702c103c40c0d0354001039440f51207160f0301c000410556030004010038018200202c0d10780c0030b580045001e81048240420341d6008a40710421254003040682c403601c170801c02c4c4400791400c1c4102d12049810310b900502101154410f00f4204040e113000507007000400d105c07075050444d2140c1225290030580c49c146000ba0401d0b1804040b4001a03030000411560130700581c8221040d845010006900350380078408401140842c007545007505804520050312040007051255003181000200c0010354034008103074490190110748202008000701c00450b10703030403003503422680c0441090340c0c9964201148003240500744007032100c2c1d90744110005402d104200020301ca8100c0d0802041159681c3c3c900007480b1445020180007031002960240c03d5003441864551910340c1402d04504204800c6405442c43e4000e41040824940325102001507488040c0036607003242d0b04c02d006014641c1083c408800394064506c10303504149c0c4030001c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 923468794 1250 923467544 923467579
    0x30105091c03020d2340052b030e151308070303140f040f06020d021c020403030818032703060403110d020114010504090321050702010c031a 62
    0x40319a00c0f0a1184280200c00180f540f00c917150442101e04140d40f1226000595240c4204203156103d0701c01c100d120380109941a04484070410b80720200c0c0150072501d0300c46000c10303401c200b22403a00803c41007000e46a07910542c5030000c0340c040340c3c00406140c10b2020242448070042943c524003002c18031040d0060b80ca000d0503a01a1900e803402a04d5008000783e001d0901d07a0540080104a840241081440d243c0b00c1011172254001c40d405421518240700d04800614943c0081550086020015003000c00c403043c81c89458140803100741e0b0090340054200201504009090f6002c007603415890744401c610050f49032030380b2840700000902182d0030000c0c12610321100e8030101e0518090700700c4950b0f241610b4003a110030709906487c501c17881818041d0981610501034011444900110a5101c0c2d191034140320242400c450304509200950b4014480c400144110600c3d00803950303030210741c07414100300c013a084441030304c010410542440401101c0031422602d044030352100b07641543c84c11031071410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 923470044 1250 923468794 923468797
    0x70b040509090718270f020909010204092f040513050703060e07030e060c03091e100c1d0f0f0d020d12020a0c1d06010c0312090804060e030105091c0302 67
    0xe04103c514805041905038000d52090300f40300b4090341c015a8001d0960914100c0c015003400081490041b15140c01c01400c05a04054000003444005414103480c1c0d0361500503202100303424690305c510100c800e0100140800b40e00c2d484c171408640300780351508000c08540f4541541c003100701c840352101c0c0440c260714440d43c001ca00410074822516003e0404110081c0a4503c2a00f00d080034401c4001140800c2e10020480c0e01400c40d040c004c00304421650224158142c240d2030030619405940070440c040310407800b62528904507950f138082d0b103642d0000c031101e05075001c501090141c0c00396581c841441c0c4a6036840b076510501210340000c01c0d0901e10003e00403600b4000000d1084044040c1c070001540c00240c000c1c2e920740700e82c2d804144262103080c01101c03066000b0700b284170b141190001c03404075409020502c0141c0d020745030404c441950b06500c9800d980715103808462019000404200031540460340030303807481c4114004d010340e003091034036290381d9a01044201d081d89256a14070307507064020360 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 923471294 1250 923470044 923470049
    0x7050708070804060e03060a0e0c3a0b0c04080705120c040f020a090e06060304120c050d0503070801320f15040603051602120d110d0c0f02070b0405090907 68
    0xb0080c1d91142ca07070800900f902d080d500d91034000c1c850480070030070300b003001d000e401a03a02e403a038020002c0d1351000c1c0404c482c0580001c4030901c442c0550b03445600e090400c044000407000110941a5040c6031031420007041c1200902c00f5410510501081c00001004a464000c23100c0031242070391b400c2111141c050a040e03070300d040a0fa01c00d10f8100e11030070500d0f29802a04d03028546032500c0d00108d070b42d40150300c0c100404480d1907034490420000a00010344035120803c000b9060f1401e14001c040560310540341c034495003500404620013004004c0c6080e0300c000845d0160039940a4203070486c000f0340c0f40c05803484082032505442c02c0301d00d941402d140c4400d407800100900040690702038030040105061540d00c90300821001904000c002184103117807141100700e20400e98000d2005040c03402d0003040d16003050718052080c40c0c4a4079000d8802400304040c00c07207020190344c00540035892030b402500c42d500c40b4607090159000968200811116201541c04848058031144190b580f81c0c00344909260454 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 923472544 1250 923471294 923471303
    0x60f0d0c1b0b0615040e07172214031213210203031504020903030d1406220c030b0d06150603061503051003050303010b0714070f1202010e1011010609140705070807 72
    0x6003001009540907100070200568814400c0264880b280c9c1012003610704c0c903080700e150040310b6000300010a454107041c03007682c000d8192810000041c110321000344041e91103252914002d40000b013440640c0e500d1201000400040242100007040065202c5c000180010724001c3d4074012501303281c441c0d404840504400900352907944007408030000092840401d901032224204000030102d05011360a00c00020007034030554980b042103d015005444850000c804054a074504410103848026004000c00d02c07484c00401d0940000d1062000300d12942d12000415003045000c20104100700c00d00c0520f05514a00442c1c156500341164140c0720499000400c10b1000000002d041541e9601420f4000c0c41003529034440c240d1078600690b01c20040c00b442c42d000813024800c100040c0f0a115044c0c20503c181001e180482e20385000992440c407180c80f49000c29110304482d2000d010a100d400054881900100f05a031276203100703c40e20110041c10442842000154241402401c0065680d03c40e0300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 923473794 1250 923472544 923472569
    0x5180603190f020a0c08130b070c03050c010804020a230d21030b0109060c063c3612210207150b060f0d0c1b0b061504 52
    0x90030100041071401030401e81207a140081140d07100740c19000f2207082c1d006070354825400000a45800c9060752180310111010300ca080c00002d412040a400f806259010b2145262180d18500703107281802c04001559040284000030400140c3d140801030381038801000303401160b0005a004110918030000c585035100c0c0c42d1404140802030308481c840b03159031210702e002080a11200007a001d0b5100e4000362030100e8003e6800b0f0240c0352240c500c01079428005d0740085191310300440400350b40c0d8400b0218080c0d1540a007041450000c582860082c5041620004c22a4002c0055102c0c0352809600148030f030300d9030b146004840f48000c2d00466182e00e0708001c110400100100d000780010011501740754240c05088032590905600f0b10035216002d4104800400d02c240e405c4819001740f00d1560380c140d1040050161303140c541d1201001d0302550440d6400041c482190000c050451a0a5403000741c3c06a070752486c2c100040c060001d21170300000196200a81035081d00010788180c002c1e03820810307801c4003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 923475044 1250 923473794 923473801
    0x12009010903260706060503010b030307051506270106140f12180313050f0121090302100c09140f061b07170307060e07151b0b040803010e101505180603 67
    0x111039006d1412208200d000300410390f040030505489008904c000703059a0090002006103600c8440c44a80c031804c01004001c09030a070903000c05080a61082420002d130b0300100500403644c1016040070242e44030440503090150300c4600280510905070055540000d11002c5250107200807d075050130340000098a403120313003d40803580c120b1254820706110741030480d80350400794018805140890110b4a102d8600034107600c50340f01902220804404512404040c124500c030700c0e00c1400c1c8450503039aa40765a481c070745540202c1500d1500d402522a00d07a4203a0f44440d540c8020807100008400184a0a9140d114002d20300340003055001100b44c4841c0c01e2a0503040c000800180005441180d007008902180c059040e6a0881030041441c00d000714082d00c00c08070300514405036190b10b11410001415015503c00340c503000141e400312038200d00480103200c2041d034520301c6940701e1140314068105519108090110000000310441400400601d90074030f801c00c1f001c40042000090700d065940e04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 923476294 1250 923475044 923475053
    0xf0d05040b070207090b0a170f01020c0f0705030c030307030c03090504050c07060c02012c070906091b020d021902060706090813080a02061b0304080109050120090109032607 76
    0x1d5003210900014042d41e5000301d800e03c400e104140d8140c3c07000d4404101c1c142444600d02e605941400090140c3c45002e1401e12110401d0009100c1400c1400c003902d00c41e00a00c10789450314010740c000c1c2e4820742010724005041e0310000f080d0360380203405151a010103215824141e6810080f034010a41203824134082082c1045003d0040507a0f6206a00800020380c075402c00300d00f00d400a406211802007403030300041203036070b2202c1002640344c100000d0b105910b40c1ca80100c2e00b01ea490364080d05805490358a58101d80551030202ca090200c2d50001e40305403036803180300035110641903220142c0e07003020990030b500f55100e200c243d83c03603103512150810a0700b0351810080c4590308151081800d00380046030204150002095040360703140c0c054141402c1a1241d400c0100500125904800601c07040c040007540403c24069050507a0042000041e9940c1101600e281c00414420f103500c260010040780800d640d00c03940000413030790049115440040c50220842c070084501001c202d842c800410341c02d0602 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 923477544 1250 923476294 923476313
    0x3030b011e0c1e0b0f0a0b09010905090f0d080c0a0311032e03020603010b070323040810020306240c0109110316060f180b04060503090705150403080f0d0504 69
    0x3607009010341500303c007242080280000d1052030082c02c0c0c00c00000840c40c5140f80c18415500182a110089520010380340850107a078001d900c825151030301c4500b400071500c01130051058680310180644810003800c40c0c050103420000e0058554400009140801d00d446540b09258003080c510341981d803403c0c03c0003d2420354241d920051a60007400303000701100c0325901504400c40364040e0850b803d5a00e8540c0c082c0940d04031700800c0c0c040c04103441400030107810310406605c0602955003d103032035506221005141003000e48801080c0d030320410a00c040784c4e4440d030749098526503d80c40e071140308060070f0b00c444190051130000c920941c00e041c180d000f0018407812241e10b410081d012103070b603030b0080c1c010003100305028400e040204600140d00c50450784200340303440c0e0003000300e00d08400c1c0340c6d92a01026266445940008001000401884001101400304600901088801d48800c281d480c115000ca8400d03440020400c03030001954140075601da0054a90074070500030200507501c0e050400c680b01c1d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 923478794 1250 923477544 923477567
    0x513031409121e010e0a2010020f0607080f0f0702010f1e360515010b03074d0706020f07150e040506130f1b140703030b011e 55
    0x1a00321692050500c0e0005200300302c01076141000402203800c40703480da80d03203140100c50700c00391070604030900d8581f540f00c94550200d0804940e000340b0040908140482c00d010780500700c001044007510a0001544044514681005003061280019262400141d0051003000c25940d5400d00306100020210144c04e98461443c0c04000309121000c00e02840341c4001060300002864440c140c2170704028412440c004150107440780c4111a01d910480c0a4005503e01c242d01c85850403200104100303585501041e49000c200803c0040e02e00c00c010700951000f0a0b04600000400d4104020b0005010b1382d0740d800d48550750500016966440d40301c040094a41ca8000400c1d0550f00c108000001e90140600621882a841d540c54070341c4403c040007040080d0801802d615848860000780c00c1c1c264205101d20b03035000c2150100002c04014240990f024032803040c180405002c4145500c2d81100e84102c102c84095605150000b02500900c1c010781d1290381c40703442031120000c2d5401076004581c000418152 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 923480044 1250 923478794 923478823
    0x60d14010303081017060f130f12030e1c030c0c0c0e0403030501060908060c070804050315040c050a14060724020309160b1b0c0d0c05090901051303140912 68
    0x91500d4605407003640030905c030b15a240e50711201c0025180d0b840b4902d110b401c51200354945147d0621070b2280c5444042d140019141001c010f022088456007600c91031020050440142c09006080042401e1400101c007081045c0764440c00c0a20001d81b1032454106d5451b4008a44200e690300e6000c81d088800e070460301200420700e82000401c2c0903015010100c102c424623002071100b940c590b00e00e00d0554202ca5021100030905020100d42d95505000c0c03807080c0d20340503150a15a03d4a400c1600e544038071a13004500541040e80140001c0050b10480c1d9541c010541d050742c0c4c1c55181d4900180050f0642c1c1c010f407403645451503180d00c1c454003500298000c0c004e0300100c511101030318240000c0e1940f28401c12603560710802ca410102c01494036048113114103401611010107010010038218558031404440041e8501c0f000d020070f1400c140010742108001c0c0007048180381501004030f804c5030401018080c02500c05890384540219021201030032030151080204d03040f810080d580d034900b41020901c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 923481294 1250 923480044 923480071
    0x3021b03030a0e21130e070815040204060c06050c0f07050a2d1407170106051201050624040302040c0305060915150c070f0815100e06060d1401030308 66
    0x111180004c104040560020a420520016604801160f444030380814124245c841e4002004803480b110780c0e10500007501c03203880c0d0307140c8200130b4403020b8091142c0601c924414401444034681c4240c28000b40355001400291f1520780070b90350b02580c01108a681d01c0c80800084510402034041840c8400a1051032021400000070a0306000741e02c920300300760710180344600e2a1340860045901c003004404503000352a400760302c8205402601c05809241d240c1c0c1da465600821540c104800c04001a0100c2d000800130703420240c0010307002401e01c0f211442040703004502c920145010b030702154003c5034014401c008030351070610080c0161104440c1e0500c50b190810004403004850424480c0b1030b60014000f20307011240e410802d00c560002c03024001e003441404808152041011203030406041e40b00d004100c40903801030070580034403009040b52420720500000b000080310700030b0140e8000030121102a2904403410459008044118a581c55500d10764000400e1540013407a00317000e050000c6068 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 923482544 1250 923481294 923481311
    0xc051e09030d051312240906050702070503100b0904030c0201180e1006031a09070320070605010501180e15130b010311091e1507121b02011e03021b03030a 68
    0x2403110301001c0358094025a030020203185180d4241d03c84404802d182080000c0880e1f240d01d07800216081200c2034005a40301c41d009004c82d01d0200007007040d00300480720602108250703c000c9107880b80003600050034422904004002c5a00408129036895505440e81d0006130391003a401102c00010f8800c9000341101c0980402c04901c01d01600400744085482e180300d401c05082800f60303440009000c00100350740c900300e45100b54035002c440c1808000181410752200c10a0070f00380101e0307a06034400d40c181300741c44044018075a80309100740c084510790802040b86a03120011405450007481e0981d42c40100759a0554585116902803d41c815080c0d804010110602201000501c50340c2c1d0b901e0380c0140f146000e8400e1610f071400d040e03050384010340810040c1034440e007540c002d034212000c2261640c01d0701d20034121299102d9030484a1001c010001c600104094002a11f2070140d0714a5001d0010342000a8a1041c000d0b012199810b0030280280e500000e00d807007042c0c898006941070fa18060401001c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 923483794 1250 923482544 923482559
    0x90c100504050f0910051c050607020d1407110913060b01030606090b0c0111030403050c160e072f010605010306090506100c1104060e010303120c051e09030d0513 71
    0x1070340d040d40c0c4041d082d44401e00891003080114580189050581d940320b042c04038043d201c00c00841426224a0034000b440307c214948035082001c010b025500319403100c5d80c0056510341c4581100c8840c2d950412090b0765006e68140742c140c0381d25110b00c0c9604500c3d0303002482025200014002e8006004110410403000103600440c15540700340301d110300140c20044240f01c807001e6080141261480307400009910180c6402500b01608122426804988003048018000c00140010f004031509581c14200b814244465a09620400b400040401140040c2c000c102ea070303500300e142c000650b141da45401c0584040541c501071f100d58040e03a0f000030300381040010040218081c0e03600404d00200301421090020320708a07581d03600450306580341394214046203610303100c62040e007024100d0441d4003600c0c3c0d0b0440c00c0107410140f110050b5800380746400300b131050003540700d003d4942c60404a0350001d50108c0c01c24190a0502680303001c241d242c06038180a001d116000001015034268028080c00d515030b48010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 923485044 1250 923483794 923483797
    0x1804181b0b030c250b1008070b1803160f060e0a050a0308030c041206050103031b0210080720011517060103080f0c010f0902030c101b030306030b090c1005 68
    0x15210400c100788007269800b440400038140f10960000598240444c00d510b040b0030240606080d5045003d190501103006040c800003c00741610200034075950f4506400002113204500708200a200710060001d03070359606100000f0000b42d003584040960f81c4034001d6000c0b145082c8905004a10222030401030b501b00180b01d98103d07140102803040c21803464448502c10781c0700800201c4413100c01c0101141d2055090fa19400f91401000009040d60443c50301904602c42101401290b800c0c6110720b82c0180c0d950300031104181315503e001da103151aa00f00c107680c3c5a4800d410a00345504021103c880040305510100801e18102c600500195a401d6100c0401c004a940c003c05900b045006101040c444e00c01406003200c99420b80380340503000060705086074080c5440200082e1540d120783e00394a010816440c40c1c01c1c0c2140c0491030141e0340603002c2c007048191488252040c0c2c0714544c8c0418103000f035104500650300030002114519021083d10f46400110307e55600c50304c2d81d0314202d0a920310660 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 923486294 1250 923485044 923485049
    0xf0305090c011209051504120306090603230f0a05030c0601060e030304060e0105040b180f121b03010902040507081006050307090e060f060a02160b0307080402061804181b 75
    0x311070034807520f02040e111020384003110f0182da1500c074403c803001d000e4440b9030019100742c0c016821703480d04852014009090b95143d6108001d039a040000038070104103550b00d0030340d0140e042504811001d00008800741010700c0c40607000750030300a019122003030003400302c0108000b900d100c1c296600340e80c88035802d544601030f00c400c690301a40240003c2c80100e01805c02c0c0c5034456070504240d070601e03640341d40c9044036a02480160091540e03101c501c00385410808503800002000300e4003c016404035160256a402444203e04480c12415030007541385c0d20290f01803a807045d0081c0003071019140450340506144416a10750300400726501000030f00f5881102568015512a5500320300075141510000103010050103456001c40007643c00b070f15030ba94500007400716000700c4d009090018100c15000f0001d5886a0143c44015020010003400582c03000001380c1c45981102c00c1c50315011031400c0c83c0c9030381e001c0848454015142510142002c2498070030440610b02c5010280c40e42071195020724049030003031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 923487544 1250 923486294 923486297
    0x5090c071e050d0813240e0d0e190302060f09030f060c04050d150603050d0f11151305010e07090b03010e0a03050f070b0a06050414040b0109180803070f0305090c01 72
    0x40742021001485604c040380c2010440e00506071810454a0340341c640041030f8111102e0800c04d03c481080c2c040d20740503002d41004400c01500c1d0b441c00051020b010000c41484080c07040d0509600095141a01d0841d0005541c02414480e00e410325501141083d6102101c075034801d101d829a050545c03c00014a00d204011107501035062078a081c0510032020250f95044604243c00b1814203040c800d06d11601d0011030240d8024104c0c0a9090401307000395036100000030030061440c0c00c0706414600040c00850018606c54a090180d80d01a100642141c2d0814001d0042d4240a01a140c1441c0010004180c0315149010000a1152002c15088902c245d0703058003560400c58200340802d0185004e0300e000c2d0340d81d800701072400303529036514050101c2c01c441608110740e60318420300042c1418401c889400e42c80b45002e401905150700c03180c0340c1c01c805100d0703070b030700c0719107a140c1c0f0b2080d4041c40349090140c42c0d106482c142c9a007000b00c4058103032030aa07900000024907050009045102c0082d42e0140c03054107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 923488794 1250 923487544 923487553
    0x40e09030424050d02070b010f050f1e041811030c010503090604230109050615030607021f110406020a0204111806030a060f060c03090806010509130c05090c071e05 72
    0x125001072140502c2c034075804090100501803c4007005490000702401885200190304039030529404920480107504030038001c800100c80c101098454000c02c500210381c8280025034041c083c400140941044520361880c1083c43c41200100300c28025000b144050460540d116120004011100d0b80811514020940c2c4043c1c007080c0480c11185581d12d800b881100c04139150181c0d0074410342074031402c5c441201c0b9a885902000901d10a030040031030801003c030040e20190809a000130354841c7c480e600300da07001840081c44810007c45501200207880242030464460360351311006503e55600240a900560400f049400d518208100f11102d0702054410140c45003140001d1043c240c10040c140600c082d0350785030125419030b240700e040004014640d2110503001c810b25000f025010f969000880e0780c0c0c86030340184581e544502200c1d6204040170400c10b000d504600f011500340200d0360120f9000301c1d03921305000703514020303030300510940d40070301400c000c061800c00c4c8940c1151407110020700300741c12 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 923490044 1250 923488794 923488829
    0x6060b07122c0609150c0a050f0d0f1d2106090a080d09020d02030f01060303021c0903080c0a0c090e0d08090303010e190f02090906010c11190b0301030503040e090304 73
    0x7443e60240070704820150001c01160464040d80d503a0364094130382990254880c55451003000030070091040c00c982418083c000e035240300007000d8505014480340c4020710010700e054827001340102901e0040300c1c0c0001c02c41054660740000200242c0e002c000c0b4200b480c012500001d21848001a9641c0d4443d8400a5545030540760759905000b0080880c040341d2185035404c228000d03036030820401c080130300b18000001c0c0691840c0350180c54840100c10741201d0000701003a01c0700b201e401224a504032900050200e5407101c00350b840d2814100e020200800c0b003e9680b0001c50305c0c0d29240e0041c40034801000454901d8002c2e400240d641e201c0480710550140e00800040c000c8541805c807598014444aa03004050715140442c4000d40b0841c1d035280700310039030208040b0020314085510030341020080c241040d01e41804c2e1144010820806110780c014502182e440b01c9400c0b40c00710341d20007001e00c070729102d4995861740340640d180d82c45071203601072442c0908041502648003204030b0b011a0018070b0306140ca8271 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 923491294 1250 923490044 923490049
    0x60f15011809050606040f090e070501170c21100512030c0c0d02040b0907020d08060631080f2125080405151b07080d030906060b07122c 60
    0x2003c4c10380000050000160100d80000c00e100500010a008a00644803c494078030b00111944054100000000c032420324410101403560024980400c4664030100c01e482e484041c180405003024000340c03074007006207040b0300e02840425100704898407a0030b515031548a99407402000d1652240780c2090607280c1c0c141c41c02212000190b403010b070000c2100701c640c0c030000d81c3c083c00440384140540c00118a9481c039076403140141c1d503c000c044a40f242000d0528400d6281003180e640711400c3c03008040074030101745a004c01054014152181150f03c0a1484141d01b500c1c0d5255038a480000d00d503031940319488000ca0400c1d54120104501221340751018502003006100d2092826640d04004000106282d1613900041540740c401d000c4181d0b9170261010f88402c04450700c60240c0958000385000e200c41c900204811600c0122450003013103c0c0f100b81040c130018001a40030744111007001854004100c0d510404085040f442d07150b8121141c0c0040e5400402e032603003460301d1107038264150040c0c41c92 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 923492544 1250 923491294 923491301
    0x61a040c092d030b070906392312030402010f051308100204210510150810091e0c03030c110405011e06030204030b011412060f15011809 60
    0xb8001c54102c40d41e0701600c00790450111020782068580701844010044010340041c00c500c000c04161400805e091202040710358440151140d8110b03a000410404040c0c00e0300b090840a0075402c003140182d800d8445002d404c4007520380c4d062035881d00811803e12800d08943c0f082d64031940d010384803503d60004802c0d01301c60552204003800c86100c000704010804036002c0041b8410242210801a5140c0c181403000610082504c0d0b2440400400406840022804544103501580c0072801040c40c410003c030030340d034104950b00916040d104035140e148030b003e200d8100c100024000c80c410201c90711100100030000e984400e0141295541e8002080020710408040301d0070360003060445c16058046c07002038151034080c1c0c0300440164010320b03000314805020000000505250900714982451956040003400701480f90b000488018135507071429032241d8000d24a15410a02a52024544210b04c81211941030b5103100e0030390b0080d2000304065002e458460711480203003100c02612480c003894107014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 923493794 1250 923492544 923492579
    0xc02030a0201030c18080a0209090f100c0203210a0b0901080601060c11041b02070611060a0c0212030403050d0b090108060a150803120912090105041a090d061a040c09 73
    0x800c200742142c0d005110011700420701914100e000391019402c00c0c010007a4406d80034040b180260011962200b039048000b52002140018000100300b503540804268214014046501c23400d118900e1105c0c580021052030700d228190400c030401c01d480451040c4a501e4200340201d80b030741d40c082c400500500d40217040251510784106424201114510003080a0b22200d400702020355040103d4030440d6038051140c400504100d203001a2030040c150402e694504010f406071189681d1810300100e090310911001c008ac22104008580da4240782c0f40052056000ac4590000c0340e280002c5181c40e440c24140c4181201e94100007403159466440300107000700420350b038411040300e5414001900840c1800a818041010745200b040340c03a01103036081c1024040016200d40542c10080411142c4e00a4203680a6a10014440e513081c5008001c2100a120307400341a6400381b0001000c42c100021901314800c8a81c0c180c80c0410f41591482c240310a440f07406038a003000c5070055405022103e08261002c01d03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 923495044 1250 923493794 923493797
    0x10e030a080a0f0216033906020724060b0307090303111e0c04060e01050d08030711030301090f0c0903110609010c0f030305060a060203030f0c0a02010b040e0606040c0c02030a0201030c 81
    0x803803d01d90f0420038102d038844250001c0c00030110101405040d001601c0060748035240c0003400f152108a14148191846403441c00c203c15008100d0006000307803603054a01c0258003004009100d001940c5500e1540882070f003c2d12802c5c10424042802d1000343d0030349008007182c0c1c40f5120064116601a145441c400c50603107000e209502c01810803600d0109480c86080954000d401c070745260b03400340815562150400d0358680d2211004201c6c60325041044200d240c0c00c04501501e90306e426804982010b0040701c1c80d4461300c0040b001286408080d80049141d40799100c5c10802050104400c1c3c41012141c40080d000810160440109090410081c41e001d1014903064800001356a40c3c1d07013004141500a40000f695031080008034100707030083d0405451980011400c40c0361500815020040003400c242201c0c50110395023075100e000b50001c400f0300d6002401400350f072007400380d8141d07500000c03a4034608c180e041140001083c0d00030405d103018a40c020703001e050312604640042d0041d010200300e940 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 923496294 1250 923495044 923495051
    0xb0f16021332010317070c1a04091a0307140d0203100603050610030f060b010903140d20190503070209010909021503070c0204050c04090f05060a08010e030a080a 71
    0x9825403164416007a000c0d8212400c440c2c904811840710384820450b01c624803000959400510104041120503864000043d52aaa440a82d032822141982d115409203456440010300c40310381d150010042c000ba0362041c038041204800d034014a0421144c10103840360940c00101003409280c0c0048040d0200040183c22414000d81c0d990100345030480b40c0d10030701d07402a0f86000500c204201804003d420609000510300003a0941d15445084007104400030049585e400d810650ba0b405031010344001d41d0090f035080c090909400d0541d4452920800850014001d0103850002ca00700c0346941030301828030801441091060000358071903181403142543c4a101c2803003e04010b903284100240a450108008602200c1c40e05c107001c070740c10341035072041510401481000b2141d41e0000d400200c40d601101d02003500d80b5603180280c01849641c00c05c08000f4241080302c0419219500000e0003841c0940b01700009940d6180010308039039100401c2a416001048580a0f091185044d40c0d0002d180740c0000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 923497544 1250 923496294 923496319
    0x6030d03051611030c030429092d040f050a0b1c06020c0c04240b07030c060c0c0b071d090f011503060506040f090c2d050909100f0b0f1602 61
    0x49185820a5010400200f650501d0010060380d042d0300c0d502d0780e1400c00e11903050580040c006611b070319524605c00cad68108004114004501d440020b29030f202e00c040c004010182d140d26004001e030174103c91900a00d401c080d8441401d003000e001c0380e41c002100842c0741032a0325840d0b8600010b548407401c020039600ca591100980c541d5180f040c120750710100c1c200c0c0613000c00604504052107409a210840780c042c00d011003008a60400c81e0100c0cca41e1042e40058960403d01e002d80c0e080e01109001340902d11070204008940d60004c3c003c015080d251400440a000107500b0000d1501003281e40071b425040040c01041b40040400d4914403005817810003052143e01ca00101c0c06036005940315180c0d00000000c10024001148108000c0f03404601d014002558082e902c0c1500a104c80010b41110014428480c48244100240e80794144010007041103402c00c20308200c1c800140d030050400c414124030000458440000c2194008001a40400d00300341074075000024405c2c2c0018243e0f0000c0c51030349003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 923498794 1250 923497544 923497567
    0xe030f0c0d050307120810170d0f020307050d05040f050409170702031c17060d12080c070602030c03060103060b12010311010c02090906150316030803150306090606030d0305161103 79
    0x5010081ca6078640b074607454010703040c50346052903600c5235a0405501030200d031000d0000c240c000f041606410300303001c036080c0d0007012451351080810207041030007903440d10203003260312800400c11100315105030008162607104201c11510b8a035801013110003005250f09084504e000034040307443c0018142c521030b403155560390700c0b5a14590501000200002c02d040b124403403006140b50085000e075100b00003d4010b6441d1042c1000650021060044100002e400c100001040f1a0842d512810654590034142001e1803140c2045d24120f02007403d00b640407074080c00300c00a6614800b1895120100d0f80d213142c540d00c0894902510740360400c90002c11010160310b500c2c1d8128007441c03041008244e10b1030001a0100c4428091400c03e10075040320740706440c40036040040c141502d0300f10851a40c2d94a0790800c6140f07850124048540501a00b03041049501c80424041d20440e0300b40d0544a0311300c2d01c001d0460490701e044442c41500c030748659104a0140c0305407013400101124500b01c0b8500b4800407036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 923500044 1250 923498794 923498813
    0x100605091801150e0a050a09050d1404080703080d05090c060f0c010b0904081e0a1205061c080703080a1118030a0602040f0f0f0b0306090c0d0510060e030f0c0d050307 73
    0x4107484d40212030044c012a500d951148690007007444e4010880d140041d52881c1c1c603071040030604c0d81004402c1c840c916102c07103040103d900500d42c003822142c1096503440c02da803880d04008603000c0d00302e2030180003440f01c43c400b081d02003070000000c1820b40352407003500f200e03040354000881c0058190340c0c40d1507006481c0c8441810074044c82c015205551684403603640800e840d01c6041c5055001102400720003c081d070002a4013422206041002c0b0b030a07035034000402c0d02c003041548800c0c0da44598601d00010300c10b84000602030103009540702c4065956043c084019900e45262034181c80b80304004022210880e18118041d143d001000d45041c0c40050b05d43e40c1c1682c0058020305110084000e00700020030710450030100900c02c03034030904403040c9001c3d0281c1c1503002c000c121501400f640f9001034250360300c1c202100c106070340e101d4040042c3e00b41100e2140030724406014100c0844c41d5040d10903224900040c4680400c20b010006280b001c80d41014043e821100e400100c3d00c0384410f22070340300003484418 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 923501294 1250 923500044 923500049
    0x51603030209040c050910021225021017010b0a0210050a0207060603081308010504050606040b06040312020102030a0b013002040503030d1a0108040c1215150810060509180115 77
    0xe0b24640c4900d20b01b02007080c00b14420740014299805034100900e400095030940da101d4191542d80201c072091103003003102403041543d0003540902098604a00e03207400511150798601f0407081002540e0b00c03a040c00145110b00b1540c90003603400036484047c0c0c0c2c030142c1c1010340c0c888180e1303002500708400759a90009641c02500100c0e00d014000c00e5030703400b88055503407020080048400034030241c1484d4607943d03154000034110b81e00032500c0c0d03804942c95440e4942110021540b243c0340340850300d45c0c110000d000b500140c1b00c10310703807074280401c4540c958810290042d15402d400c82032801c40801d20741070415882c03103240c0120496001e110000300c2d55014005440c5c05014010045aa030400d1240e00001807403a4804e80e040c01248000d220100b24200b2005061b19904d5408403804102c40c1825021440021542d00d0310a052000800107856402643c004441c5030303a0466184005800d0a4030070340b24103010b0b060b041320f039480020744001d140c03c0582c109641400000110248403171084c0c070f4960070b05d8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 923502544 1250 923501294 923501297
    0x15030a06090302012405120a080a0e0103050105120d111905012304080304080901050d0603060e060601030c1d061306021f051005010c140f100e03040501051603030209040c 75
    0x240c1c900c8091680a014414228512170782c14000c6016000312038000070b02c03a01540e40212030b0008101d9542500300070340110300360041055600c9914050b801010b03050b6039802c10380041c0c14a0000116420a1001d040682048102400c0104400c16003260240d07142c0b17444c1a003501c1540c9400d0305404034854034400300c03401900045500e805c0065900310082003200202c40540c003020403c80490502c1c01680e8100360310290302e42d641e408017030049800703001c1c5601c0c08400340d00e46040001044103075405117007481c500ca001d0b40e680f039450f0320064040f02d843c3c0c0d802c0d0011030080350700312000da040041c0180d800c0038014800c0d41880020801807081241d250007100c05a071085058180c100719608040f030803809648402e209510f0500103180a40e0900c0c400c6905110035040f4800810031000c0e0002c45042100c03089030300d114513080341c255072a6001040d00048915000c1c034004003810210448041d940e042c0c481c249040c0c03040a590b28001140c3c0ca05908041c1d0900c000d800e00e40d0340c0d003e41003895626 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 923503794 1250 923502544 923502551
    0x30a1703040c0506040b22061709031224040902061b1c030b12010b010e060a1b0302010506010e0604050a1418070e0a05040c081504020d112d030109020315030a06 71
    0x3403c1e42100c000806100004810f8171400c02004101d0b40034009a04804850030301540c0341c4c588410b40c52070f5002c0e8190580c7c40a40b600200070b004400812041c00c0305107001c1d10000420340ba8dd0a01044902084019401803810006041e0400c03000d80c540188148000031034101d446902400d140280c19803800d400000d884641c00b1240d840c20740c00000c41405004020480f0154440000c0c0c4504451140c460140801060850f04079018241525440c0d492285191503401c5a240081c001e000490307640703001c200d04070680070960a0031070a86050790b42c06400d001032039003410000c0302c8182202c40c1c1d896001d8200a1520020202e43c180c160080c841500d54111010000080005949254000134011860414401180f0740d019015640001c49024042e60000d09040403030080d11410b01501c00c1c0178203182a41003541d08640052900340c041c20440349100507200c5103c10f9491841030240c0030000c0171310062140a08560045400ca1064a5001001d00309000407a0a014400780181c0321282d8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 923505044 1250 923503794 923503807
    0x18090a060504050c041413240e0d091202060f07051e060708010e37090c0509100b1912050c030f010e06010504031b0509040b010311030a1703040c0506040b 68
    0x4180c05961084600b02014034a00c4c03411030807103200040c5e87e04016101e100d045407060740d00f50b040d80e0444044040380c203003071010501c003031640c0d5960305070310030100000f5104610010b0490490701d40b6000c0b1540c014645480c028000f680241c0d250402c2c501900e05000d40d08081032049007240422a8110366000030340114600024042c00000c2c059000850000d100700821000680c07216516060071181c90300e2001810144035900c140b60514000e8201083c0b42403c0042400803112034001164002c6490f846a03171b40758030031627820003403c0c480c00d00c40c0c5d0000c2c0840308403501600358602080780c1038608100c2c25000c0200010039a0741c2a503451101030740000501c9880c00e4070700c0181d400b500840f070200f402c40c00c10780300090007481107110290081429210148510140c8009100100f900900d00300340c80c2481c1c142011548028441201e100892111250480c1008103216540542009100c2ca0542d00e031a07030966550300c014400c680e41c2c0c100c0c01c070216181e561440500060040354003a2520307501c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 923506294 1250 923505044 923505049
    0x71106041e09050c030a0e07030c0617160903081612050d180c140324090d030e120f090406170c0f030a020409051603121d18090a060504050c 62
    0x2115401c5100b58508101c00c00c0714142e0001d0480390400740018002810240000d134050030f0150541005040301c0980400083c0d1355070040f400301d624100845102d03500e895011442500c9490030305142c02041c0c50306410004190504003070501c041801d0850304010300380f5600d00301d91a80d0000c0301c101007800442e5aa008445510941d4821510241c04003401035640d150f4040c600820702c102190045108040d82007500c050041a20f0342102c0400e0034244410340c0724280b2560402c888054207885001130745030140e8424000c0342c2155404030003230042c443c80c8200000c03181d8030141941942560422a402068840f440f4131401072000341503a018035041040c0250501c038412071301c07600c50f10454611001ca6500820401c0c600c50341110005808606071030410f0409511015030038401d8a00e40d000807d1040e10101e59000002960312100071000300d104100c004a01420111380080005041c42c8148a2181c10140c004010f80200d80040c00c00d42d4405013a5081124112010303001500b0784220b50 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 923507544 1250 923506294 923506349
    0x10f32210a0c0618260601380d020306010302190f080108150c3703110301080d20030a050417060708070c03140a2303061507110604 58
    0x180003a28042c842d0034000183c4c40310003a141c0c0900542e00116040e00b10180390b144400f014006a01c800355501c2c1e42e0345542111203c80c000304c464820120301411401002e50079113840e02ea01012114043c1043d50045c4131310000e4100400d40d40c14540d003004241c1442001d1401d210000500d95030b40c1c1c2626608040040840d40103030b00c039401a62040003044a80b0551561443d80b1004000c0e80b0354841daa041c4500d4900c104040f01c0c0e014210000b803061140c8031001c1e000e00007101079914103000c002c9500c890002d4030301c000d100d80192504001110f0480703038829840e50200750550070001c940d03802051006815680140e094a0100340001020454075106456100700344041c100903000b60328104c0000351540b1802400075080000e444403810805001f1200803011135802c00001344c6640c514800a090f509007014151103200c0040110500b400707402c1c044900c40e40380680518900450f940d088446c1d904029422504c03c4222000c08540352030341c9001c0c00080041000d00d20303407020000309501c00c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 923508794 1250 923507544 923507549
    0xb03090d03020c0a0809040b041d251e230a0503070506120405070f351f11070c030213050709050f0d021008010f32210a0c 54
    0x1e05005000007400c0c054041086601d503900700c0c08007070340d51a5001c00100204903800d041a4000c3c9040b61021460740001c41e04803016520400b12910200d102c4581c104107402c000c260803401002a4041c424030844ca154040040c4060f903424480b03580f10700001c5461a110503481d0404000c0c0807031030083e0310785140510002d12080d0003a0007940d060401040c0c05100c0c1201071081a01400301003400c20101f005090010018581c0b00c4681a403074007038118000a0040040e22950001125176920002503a864606000340000400c48050140303003c0e107100092102100e2210b5846814500c514402001450342c948541c0d807880e4402d045204100d034052241115142c02883c1004026540b40c00c12001016200d0855084100007141d40000b01103400c0194000d40201884c20650445504152100d058595a10640c2c4005840b85010b8586040c400c40c01901c2e41c46090100c0c4030217141100050407420041c01130380046042203822110b82c02c1e00e010742c400903440b291a040911581d0f990482c007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 923510044 1250 923508794 923508797
    0xe040617070f3606060806090109180b13050a05060a29150d0c030603140d0507021201140708100e0c1804061e0305070501030507081503030d02040b03090d 68
    0x1400760400d02c59403c4260860003500d65485000d4010010b103610280b80b034002c1904140c00d01005440b1140100720407015074407a80580d01080001c2460341c59802203c0c002d0325803c0108580500640b213103040074802034621510800d8044101700403e00602405070ac40c0d000308010083c90420510740f8049440d00c1382031519980800e0507060340c0c90080d10b440101400225000b40c1454500540186076101c0d001000003503528050031035000542580144084030300130140d0040c400b0b041103440d40c0311003000c01c9890014404200d0100185440003540185680b15400018000e040035036641204005881d4500070a407644108080c80c01105407220140c03255151454903410200001e1000c0e00070800e40a080c180c003803004804d242c03513135800600201a04140701180060401b03082c038002e410380c0015203403406100c00218455001c2d000e400c1c000c000c0c5940d081100c1d035501c4a446102601140c465615000800a10442c480c1500141019011250130150380f820210a00c0b032908074114078120 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 923511294 1250 923510044 923510069
    0x150d0e1e03091e0102150a09050f030f041e030206040314060601090e042901090c080a1a0603090109080304321002090301020c010e070501090e090c060a0e04061707 72
    0x999443e145481d441c801c82025100104128002c0140e0400c0340c5185045600c504940c00c100030504030745c01845000780141c0c2501c8110030181c02e03560b268800c003aa20034602c00100310400001008a101c48100300480099155641c2c0f40e0340000d20aa101d6801a00c844103500000b08644c0b4040c4561074001e0b0017401d09160051425064032140c0300002c02c013901034680c5a502c0005440d85641e0203155404158545006685070b01d0741100070411100c0240008900d1000a410141d1070310035000c1c9140f504170300c80d030340345110001c0110540c4018032503c00e554076103c02e9070004524001440c000c030f20503200c6004c25207100c280ca84003640604070000b088080500300171268030300031403014602c032500341025030f4030580314000c03a000e44281c001c000515842c08007070003003004011401c2d1042d114240da0302d01c075040da82c44200041b00010744508801c1e8000c01d8920140c0c0c5401ca00528490740941404d64002103004001421100242d004c250701060030048000b80407014024a400352800340ea00383c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 923512544 1250 923511294 923511307
    0x70e191703041e051f0e060a0201020d1401170309090c0a0c05030a0e0f030c0f04020a0314010b1305010237022205160e040504020d2f0f0f150d0e1e03 66
    0x900203140c841b401405400000394500b00c40f07101790102c9102902000040c08a54030701d0041340105402489910034222202d03060b045924404400c13904003000050407021641c0b188041c103042680f01c000b03d0000c3c45814103480001a0b020f002070803080c0300d44d484141040c6030301014842442407100115100317401148010100da0741d02c800a0700c008000786d42c01611041100010340060420b80700a0704840c52581c000200c40340341600902800c503207640001e8105e55614016640d4000c040e07004a41e40000c0c01c40000e444142c0100010040000e00301800741c403c56402003180711102c0095868003d0314014074041c4500240507075508403908204006071800c2d042401020300503410503c5100e01e44920101d000c1d50340e04000442c20a07001180c00c419091282d403000c180355001d541950729402000300910a41c901a65488241e28000c3c049000d0644010700700315685d090054440240d15040c000030038005058412010040d101072300800401d141c840c915020074a4801041c0c9042c3c3c02001071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 923513794 1250 923512544 923512547
    0x1101090f2409080a15021c091118010b2b1a2d06190903061b0801060509041b051c1104030213020d14070e191703041e051f 54
    0x41e04c6415070040b419030f46904035009080d01078884c01e19500890006c0840220320b4419030b0b030003841c1701c4d8410313801018103280f040103015036254590301030300300d140900b0010040c0314510310061144c81340880c29212600d0340c00000a003003008420110700000c2e500c00002c3c0812841c41d0b9125182e80049900b0841e050024020868025a03011072045142a0079010000c2d41c65840039503910074499401c0b607000d800040c1c002015852948010b468040c107050750749180c20101d24094400842650b10b00500c0e07800c180c41a10300e980a00f907100d030026034a14000b0741010660220090048080d03441c641c0d1070340300d0101442e910f00c040d030400d600d0500d00503008041240d40d00403542200d90507030b00c0090820440d9608002030251010302c001a60502d07900b1088102e860155600c505660740302d0492400c45003080c00110b81c0496a00241881001d00500000e440d444400013000c2401044914040e15204c0c690703400080701c05c03240c080c202c00078424000da01d8021132400d5000a54000309000300c500800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 923515044 1250 923513794 923513803
    0xf031104090e070905010902070c140303031819030504171c14300a05060a140a230a23090a0207081b06071107031101090f240908 57
    0x4480c00395980b02c005010010091250100a1030301c0c0d4400c0085613035400b040c0300a507010300300460310204201404240c000b03030310011140c550b5001d8011801c42d5034241241500c0c141c640704c40002849081e0284214240030065801440d103c1e950392070b00d803460f00c0c5024140c0c0e94500c0c0c030030700d650300401d6800c400c0080c01580ca41c204440b514015202c814003810549061007050412000c40b0855890058000000e0b0113403c10200702500d0b5512554802001908888040e269a5403150030044200300080100f00081059240208050b55581e9100c510070031203603032098003030020016003096104038645011385000070a500103600d140d01d80040c0704048003c2c0301182d20b47c421080000821410346099059620300360340110341c142e840043c540a0800701e008907a9110356031203400c0c0065030492245441c1c4241410742401031000600390350b1039140b40411440300c14100b01c05110300140302a5540300000013400303141622447d4040486444520300380c0c044650003800311901040021540016 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 923516294 1250 923515044 923515049
    0x706080f10230f030f190c0b0706020c060c070b0a09030201021b0c04060b070c030813120303020c0d1d06090414012d0b120a0b1509040510060e19080a120f031104 71
    0x31b03150b140108280741c2084207244a822089640a0208203041046080d40c000c0503194840c40842c0c41a554202c0c11459034810602c005000f4200c441c081000206c0075007140d20100d21034000542002100041c9000407004a40c01c41240e51141050f01840e0509225640107000300c1c1249510700f08164541030313030a150a21004100351000900c60981c1c0f4501000d0a0241019282c14081c450603420300401035004070a03041c0060062a0306c10f103800b070107510003000303c8007180151002e14880108102c0241c01c200c81d001c0d0019103460000410f940e84035450b40c00f800f82c0c84100c408020307010210760308080c01c0c80101d042801c032452050180305446015140e54262425419150350780791140b10b0007500b000c81056400009140f81706058202d5000034000d8480192010400340e80c032000407850480b040d01c11100403420380c3d6510329042c181b820f514900c1c4c030002d0990303020365556903c2c060f01d1710560030741c240c0d514003d41040001e0581c0c0300c0025240148503140a205241300d50240380340034030035072 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 923517544 1250 923516294 923516323
    0x2041401030203031617161a15040b0609210f0118020d0f05010c020309010f03060312050f041d07080c09010215280c110706080f10230f030f 62
    0xc07001030100800807048100c60b01844000988515008001001f0031030144e40854441900002c040b04c41098140805d102d4803c02c80b030102d0690008092000401000004030382080c400c109002003030712010002200136095022000c501c0040b07002050501c51101524074499042020f0300c4410301c98040912002601211003170145079803440c0c64012031642c008020965420444801c04560300030001c0c040c0038500b0707202d80c0d894030700c1d01c0c6044084510a002c014021050000c9100150b4450400381111192038569549000e4030b0344c503682d0401004001c2160a41156000c11880380d5000c0507071034005400d601c2d00b40c02d1404810003c7d480301400041941514890303030018030307075000c98040b0451550b5004801c09659542081420280c05126054404103034000d1280800e108001000d0f01101c1c0d00341c0d0b428500391030b0a001c05450240c003901c880d00195260701e000c00c071032007100d41448403040301001c075086010414092010180300455114881c0d00302c0c0003660f00c4a1004102c4026a8020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 923518794 1250 923517544 923517577
    0x60b04060c0b0606090d110a05030a030207171f06060f080c0703080403030f0c030603050f0609032b0507200102040605120c0c060708090f06070c080c0703020301180204140103020303 80
    0x100c9020130100c4c00f0748165140d2082e4031803c0300051041240742c01510200a0329001140f07a00c90b800e05603100c0700d603000140140d002c0601000403408810f8a140e07585e4001c000e0302c00d810011600f42104415590010706c0e4199500f40c108411604184802c17200300290a15000030303d0078140360886e9004085014040c4003561000408062003a84060301c074920036907041210b0510718000a0041c00c5a01084507584a00d00c00d030580407000040841c4136502d41d00043d441c001240d1403054801110038030041c82058018070030041124640509489496542d42d510f410340c1503804130b01654000e500c90094240d104100c00d10002e5400780403100410280da0b00c107000c44e01c44201c04441445040380f40c098a00a80c004d02030110b5020fa0748a0242038450f08940c000d458800c1c215844801c02c1d00c440c2d0200d045030b0b880d640080c1e0480050088004140c1c00c1d590b5099407500400d013034821410408100ca0b0f2a80e4016085250078441c00045650400c42c200c519130441e030200e80d0300d1142c00300044a0004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 923520044 1250 923518794 923518801
    0x6081015090b0d0f060f0e090a020603015a03080a030903090509011d0a1a090703091406071101140f0612070618060c0312020c01020409091401060b04060c0b 69
    0x182e4118224001151004001701641c1c4c41a56a54a00324011103007038a010b20045201184c7c0040e041c0010b6070024401c0c0c0c0345034a802d1000900f182944215a26008241610042102c0c444c4000307055140e143c90b00740d001d611640940e00c0c40002c19905200d03011369940c082c0085095241aa11418000e040000e5815501e08003034a4203a002d03844180e003c450000081050030011704401d030340000c8100152201e4407261000c6054a2840042d00204064182017a080386400194260000200d080004442860f42c413103162407095140c010358654084402d01103030b580e00c04010428000340a000f040040819401da401c1803102804140c0b802d030a02000c0340302d07540d6001d940315080290100320751040d80d41e800080c20340d04100352848c09910303c9800020f605070145928a42495142c1e445259850280c180d040003500503002c99103a0f99404e01c00404c07502d41c2403140c000c0c0a800782c44d4070914014403c6902c3c1c20358804c1d4101c1300c43c0003c01c0c0710401903c0d41099400103c1c650201010b10940d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 923521294 1250 923520044 923520067
    0x71b0c0611010612111914040504150509060610180e04030302120f0601030b0f1305191d1006060212090d1a0a0518030d050907030b0106081015090b 65
    0x721900450038402c1204c6807501040320248101d94900010741d07407840c1da91180580d031401c400180c852a070510076280000d500c24909540020313480792082c00c8500c50500080401c42c2100d000b1149501e940e409101800301d60304d032166010240c81c1c0e0a140496002c0c0000d9a40d50f51040c0610031900c2d55125400818201406a0144d0706460742060441416240508810308a8031007980e60703034017103813400b1180700c01c605296210280381d110107400c092881c1c018414240081c18000c24106415180b44540c1d4400c00c0700d130141820850600d001e4a075292130101c440790408070400b040c0c690661602c4410002c540d008200c40d00d82c00012030b003050300c60315000045020f0043d40c2e04014000f40d0400401d8171030051408110b8020309090204202e250340744010003807904100007104041c1ea01c1806607092961141c0c206950008050080e034a0340c960740d40d6003a45052007030300480013148801c000c204464a000305644010076194030351102501040c2d2014008500c0c50041c00a107480001e015215403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 923522544 1250 923521294 923521301
    0x1e0b0316031517030d0b0619050a030f0e03090405060d030e060c2103070210090803180c040f091506050d0305030919051e3403050a0308071b0c061101 66
    0x800d6480103a401103d40d890312035440354400003a0801c650701d001000c55860030154140d62001d4084146003da0703a030301003070a0700c06400c01711030b043c1015162810380388500b805004640c0c0700741000000310f2320352483d0300400c000e03a10700910782400307241e80248a60200b5884061100248019284981c1e1400c8403c0da160401c03400c205800303074500100814001000084000310f208044503403c3e900000300a14056040d00c280e45c00150003500b040c1301160845290380080e00030300200c5000c84240c80c402c2c101041c1500e1918402001243c0e6611815042c03007429a410901d07288801803c000d4581420300060414100c40809401c00034003100090240d54108490381c09400040d10a00c1454107030302d00b403655840c0b62200d90540e07881b80380440107208000120701307008882d821072000c0141c08100d850504400c01e407100c2c0f084041e000d580040890300a014504001c5c0c000e83d9102003a01e40200d000c0c200b030009591040c0304a8010101801144402d07101c0b805070f40140c640340912107d2010281e024 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 923523794 1250 923522544 923522549
    0xe070e0609060313153603080622090f020f030d3005040b162102070c1206050f150306060d0c0f0b071208130f0204151e0b03160315 58
    0x1c0528080380008900e10010582149403c1d0703000041b0a6584019404410445520020046040c00001c01c2c0c6910b41003005482005031350050b4140d1031444c0d007118007500c28181040e81ca6038910b619080940c18075801d200e21410b0290010408d0442e40c0740010042004403580348248082036162081c0e41c1d45003090135000481c5510240580d083c80c0c20101281d030f90544400d0245c99118015500c107900400383c0d24505a858030070f401c03c040407040d801c4040d50280340101c1c1d141c038181402141806428400312515401150000364518140c3c1c0041070192002d801700d601c6080040c0c6203586982c0010b1040d0303020340290b40c101026001450100010f0f02503030132000c06810854804580c044803035014001d220b00405008245041c0a070059907034003001d540e61904d80002d40306810102d0340228951a4007440640009000072003104c49006040c0c0640041c0003040c11030061024030f08041002501604403101c071246142081d01c05d60f4040340154140030700345600d501035141e0300c2c207415100200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 923525044 1250 923523794 923523833
    0x82107060b10030507030b040516080a020403050712050106050303090d0807061d101a0f150904050a0e01050f0105010504090c0c02123007030e190e070e0609060313 72
    0x1082c1059000250203041c0c101c82240c0003a00d0b1103500c0c001860a409211701604103246800c1d036100f01c520b42150b18240081c41510001d408000010004004201690041503103001031981410310b490404d003914203680c4485d2180e882400780c112665100042c01e003a555200080503903643d16450000c015100c003003644c4010300700001c07048500342c4000c42d0101070504568400c116062090003086600d007402003680d90811040340001806007840c907400170001e806044e034a1b00740f030858800501a1201121820440c42d01d809042c605000e0034010b4036080b00b000140380e21258100720000b482d40c012481001226078036456404201d9008034035000080da00076102e00504040100c40b40d80d140707030103e0368148960311074030150344104142d80c04880c0c04100c4640146019001d440407a611f00300c65603515402005941194010501420303404014544062110454900403501925401c100e006140c0507010400000380b2541d9114100c035800a03a142c580307061111907080c201d07003040c5ca0130a0101c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 923526294 1250 923525044 923525059
    0xc09061306080c190305030904020c030d060f062c06180d0f0b090613060f061e030506060f0127030b09010905060606071a041b140307082107060b 64
    0x140c0b000c4082510f1105040955029184000b804280c04d12000240300207030042d042440750743c0d110303d0300790028400e08045070304803410110303d02034802c120760b040d60003e0b8200002050421505420003007100387d4000714011040310386c2d40c450303494403401c20000200b84514000112602a0042e040807402030346405809500340795018903100c0c3e011109040b00b0307a03d401046c80015401100052942d02c01c203c5a070441c10f240d507065403007034050050385c81514040c5407a4000801c1022101e0b1008248900500f1035650301440e40c01c000d4103289024089038090288103106000c1a6008131248116681500e03989200d083d483e500c2920081d41900b006010248000900101c06015000080c2c41c80c061030030f442d25521020200306441c030603d80001e0005c03402200780d0200c58800c0e00e407641d00501480c043c80500804203900705144029810040c40c003c1001001480360804111102c081c04410004014078140d4485040c50301c4035030154840f40302e00000742c240810845420007000c0060150210707 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 923527544 1250 923526294 923526299
    0xb1302011206121103120406080a0b090405010219030b010905061e0c0d1806080f2701020d050c0f19030207060903080105010339020c0a060c03200c09061306 69
    0x354950b060f030b41c20a54400c0c2c0c20490021143c580441d401d01240d01e50b9880914140c58220240c5425800074a0581c0084e61100200820340301d54200341c0c4070b0752044000699400301060744c40030542401c94001c04240c5004c4501c0e4590360884200000d9603002c40d0709030f4441054461807103501421095002d680c1038042041c801e50080010b401c011306007130703440e45200f01007400a000c0700402c8501ca52400900700c0001310301c18040040205810540661f81071490007a0100d0000381c01c001008503035070a80d80003901704403c43d400e02c2001d030070800e0b03013807280c1c603010b030b0303840000014060031030150000c451a0545402103406a41290403159203c2d10521080480d42800ba01120092203581d003c60b040a800081d14580d041801380034102903104840040703c010700070014028243e01c007d06603c80c8419041e0307990749907a8000000d114541e900181d231040c91800409618140b00e0400b0b42c13522400400880040118403a07a1000c4d046e41c05241d10341d1002d000640c100b00e0008194415490810003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 923528794 1250 923527544 923527559
    0xa0e030409180201081605030a0b031c090503071409071107080a0303021b0a0201090b0a0e0603010b1315020705240d060603051302010507080a031d1005130b1302011206 74
    0x11805058000d0326268803035950480520070361b424208034032001a000700300007003c2d07035426400b081c108030303000d011030b00480d01040699100e2004071300d107074000c5841b41004000d03600c0d08024503c0900082140e10014070f100c100840c6003008003504601c00e22940102100b80038108002c0c0c04020400002203136040300d2079083c054002c0d0320982c10214805941101039544e44c100141204506e603043c1d41d07042140b0b06c3d0102403611071f08015011006c0114030580811075a541d0405034ac06000483d1459903a21f042c040d021404854944c05001521308402440f40704d1500490003170b0840d682521100306054001c500340d07a60385281c0716400503600380402c0f00d000d10b10f0365501610950b01951402c02070b80e1142144141e810719040c6009000a80800a040000d40d15002400403440c147c01d0101d00d030000342d11204a41c0d40b001c200f140301d0381e000f84010b0394081487d008003500a07010f0044150303042c29a885403281000300070a44020303151071032111011a4071841c0c1b00c64021551520030001039845100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 923530044 1250 923528794 923528831
    0x913050c0619090f08191103010c030614032e02040308070f230d03020c0a0c0b12060a120303020c0a02040524300f030304060209041406090a0e030409 66
    0x1404002035100c04010130500c182400d8a0180d40d6000b000340150104040c813004510411030302101c09901045d88500d15403424000c2441e05c2e0001d48011810609041c9203031040c04d280f1021032302c258004100b2007202e900f80c00d60410740f4070212400c18014075030119580c0192050703600042800b00c000aa01c020f01000c641034003981071244480b406441c0d030340140c500b202c03411140510711541000e21014400303406980105a00e27080c600640384425400c1d1140c0030400015805000c0f4900002900420002c580e05140e038801000c4502952540c14080341904c1901e041c440201815400100e80040407002c01a400c8080c0c0d008009014900e000543d4210004a01214009801c6450051161072170141c0704819241e00314150380c0010000c54410707000c103c85104115101703024030703034004198541c00d00046220383d01403000507944090006c1404115614550f49110840300720040c08040d60340e07008000e03001105450046003401c1c00305803450540c450399020b02c035094500201000d00ca0704541 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 923531294 1250 923530044 923530087
    0x102071205030a2a0c02011e05030106110319050c0a0b04110a0617041e0b0a0204170c03061b040b16060b01051801051e0a110106140913050c06 63
    0x5013440480042000e024148044803048540c280c01e058180e00c45901c11040c6082c00360051501031511403e0044080a4041c20304c411000101e000005001c11a00401070b00e0f20075012000952809003400a0104c0c040001c85101040240010300d400d84a071080007214903481c0c010f40300302002e00f81803401c0c20010aa15480394059420044009802406103800f0f141c075420054080c3e8007035407030399507a4603401f1035420113400418110600c00c000c070358542d10591151016040040c3d8490074040780c41d040c910610103946c2983d021401e0160103450200f141c3c1c0d0021800203000e601001002000b46c039501a80c1c014038140311010a00d45c0f80f061201541010f500c3c0950b00400441c64000011107039840388514048103507410001455040d4403881c0180a8108001b91000c00401d4400c4000500c0d40920301090000d009051100d423584020703c5144018550026502c0350300034900003140181100810110400c0540707100e04042c004113200c0061481801443e80c0c0c0c0e01d5084004007502c0401c0b45 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 923532544 1250 923531294 923531311
    0x14240d0608070f180c02010e061008010b0639150103020f040b091602191b080d09090b06040905012c01140f0f0301110d050c2505010207120503 63
    0x6100018082c03201070f503410709440440b5100440c00b460044800007403c40e03070400400315983c0c4c7c180360407a01d1080c45001d00941021904005044c80c000056007500e20301075025108a1003005404004007401001c3c6801d0310850407200304000500080002501c00032001165a000301c0a18001079901a4903240c142c0348221821210720030940c007840200c6030300d211040d821034920004036010180d089180898000b80348112a1003025200707025101d0f0901100c203c070201d40200301c07040b00302d020001e00005001203100400e0701c1c241d42c2c04000c10300107052080000c99a030f20302204110380c2f580c004480190040b017000b403206503554a1031600048110b615150394440e000904400c5622000900e8121440561440301d070010381c00801919400c08000d09900c00107003002d245c2d40d61400e01035110096210f03901691501100404d0400b0354070b00070a00c0c011481c2c201f0009125103003075100d180409a560506490540c0c00785021402441541c00c098415050034800b444c03401c1d40301c0011403040c2d115 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 923533794 1250 923532544 923532553
    0xf0c16022404090e010f0501080c120a0c03060b01030509010905071e0e0c2508090402030c070512042c040803100b1903111305060904020f0f0a0f080114240d0608 71
    0x200803a000c2105e02c00e010b603400c5504004188ac0ca60301d81075842c81c3c3c0c2c113040745080d200303a071421ba50350f01690021079008a4106445405400440d038040c45500d900c40d2405009024041041d950540c0ba520680141d4802040140409003120142410440901099540e50384207042118052000740c0025209500015114030b00090b22000c03a02c2800c00568007000403404d1203c00f100f01f1000e07410003020001c0c102000c1c0b02c181e0109500700f00c00e242101c40c0805442c0d413142881c60540c52049550303140d6400070b07030141141c22589045601c4e690f00c650005680c64494807289640c850f5142d580d4000c40d0015408a0302101211980ba044c154201507500c0c00c21210301190012445806059020100740380d01c10410490307401c1ca17000a024814004200621f000440c000d9003010703402140316400805404680320b03000c2ca80064440b03400780424106500ca96141090b464800940140c00030300030a140445003101104101c030b0440040c021501032a00c8003036881d5040020a030034419030340507108 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 923535044 1250 923533794 923533811
    0x1e021203040e060a030f0308062e0207050d0b0114010e030d0f0813080a0c0503130618292101060c020316180902060d05010605030f0c16022404090e01 66
    0xd0044c1090222648040c1038110b40c0701e65241942e00303c10090280d40c00101c0d0f90a041001560507403480c4520300094880401c503022100000d1604245810040c043d03800c129103000403403002c0c42c80504649042d44502e007401c802a004a0b00c1c1c41e410700b00e10740c0501c00c4a03071841c07405400660035482e01000740c0d01d1000d16130710b41e0b17040c480c011a60000540600b408020f844071461240c1e00b418030041c09002240d1405c0f040311030301034001159600480008911054100300304c101120900e0052151002c2d003140b1510800881d110340c00740d8061103201810006407040c8807150b000c40d1586440828a0070b100c00c0d03070f6030b0901801c0d100046000302d200f8090384218859855800c601c640c25034195948074003880051083c440010701049005913801503081c4036010b002641ca010316070207001641c0d60701d61a0b0900f038401801c941030103080500890020b009901c0030001041d003101400d90100c0b110700d0040758040502803176220840004400880005020401c3c160301d4201603560b45096000700140c10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 923536294 1250 923535044 923535049
    0x60e01020f0324090a022a0c0123070c15020d0816200106050a060305190207022d0f0a080d0302030c0d050901090b0906131e021203040e06 61
    0x3003510300c00d580d103090610100d0030782c0c071070088900141501207110750701d8100c01000003503007013004840071a205500045c501100c0e803201150200d45210080f030b50441c0182426100742c403050a44816030400c164003600c1581c4100a00c0c03282002003050a00c15521041ea041106441d219400340102a5001500001c0410b10001d00c51103265100e9032104603a4981030300c81181407801c0401c0c481080b40b080741821451856840c0b00c00404032043c0001640e03417401041c00012100d0b6407010341810300c3d000030807109120b980711140b4640150400165100560700c0003c002c90303020703000101c56030b2841c00f000c400c102d6400740440b080b020458242040c1d1a610080100b00c074103902030034030f181e004005100b942c0c6006c0d8000d1500300885d0f00c180d50410080c94a0801116000c90b0ba25940741c0d100c440d803006101c4840030003600004040041c200916004616062901c0c00c41001407000214a43d22402d800f40042400c00403640100081e9103240f046012a950382c005000f41119560105d01113811032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 923537544 1250 923536294 923536297
    0x5041103060904081606060e09071d0705031b120a06090c0c0f020409020d0c0f060504060f0f1202120a0e0109050616031104090f0b0f0d06150b1204060e0102 69
    0xda03401003102810341c0d1680c1d590000717508824038202d481c8050ba2000780026445009442c01f4000f124203051b01e918000880c0c034035000241e402070544001c00d41d54809441298480300740d1110b01c40c03c00d03c7d03690302c8480b5000103004a21180d080c1e8000e000c1072500d0140e40c615241805074204a03818400546c40c0e09440040314552040d42c404140300902907400540070b813080d690054001000000c03010343c3c94000c1081608003440031114070214043c14400ea0b0b1009012002400562030b10500707050402c00060000121400d2810510070056954010503108003044001c03988015020f54541484040804096406035110180300303040178600300240307038144501036207950000000d040c81d48031a9250045c82c0f40904010f0200354527074500f28005036001e002440100342040b000102850030003910022030324002101b510a4451031101c8805588010351404000d4000c10700080d0414601e05566012078581d02201c1100f00c045144d046031800b0074816480350707014030b00c03e02140132400e4007075080707 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 923538794 1250 923537544 923537551
    0x19050c0403240f0c0e1c060906090b19150f0b0705120a0c0c090e031605031e070308060a0305030d230108030705210304120314150f09011508061c050705041103 70
    0x1100f5080201800301f4980d0308000b520038003a11001a001d0925180c0d4081d45a00f2104c2d500d2120340c0003580000482030744511b10303480e075000a1101c2018240182040c440b101840b0b4031040007004120b66043c094203101ea062103c0920740b2080d42da0a0741840502425003034070b41502c90040041d00001d441140b1700901070009140c0001e58130301140e01100d130f50440c3c0a20400e40f1131340310601c811119058104e003064003100e09445c00545a00042c07030018644c150080101f40540407401c130410005800000783d03000000a11808504051540b400024270245601d90b8401c0c1c100080001030f60b02d5011004201c1103001c0c0d015100b86d80201991712095480c04145004003500410015001c80d20002c5140070030b2407286004149272700c40382c00d0394480880684070200513100c640d26500d540d181840350410b5050040d40d00e90819890a405042c0404060700040203009061000840c15078a01741c07094581da0f0381d203003c4c04940303100c0d00308203a07940c1250240a00071480d186690100b0a43c81c800d0320320 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 923540044 1250 923538794 923538829
    0x10e031005150a14220203010603021b01020903060411060c06130212120d091401050a0b12070506030f04020d1a0f15130e121219050c0403240f0c0e 65
    0x52181c0700b0303002e004070107140c01040da0700221740d0800204000044d000550017004103950158a522480342d00381c2d044001c000c034800032684100b00c50701551300d001c1121035002c1d40210703414003d9402140031502511a404202c64a1b0180404218490840380d0032190b101307000366000d503548171002980301e82d40d800058008141400a2090480d0084660004840c41d48500681508509071201352400e641007507614002c40c584413a4207074028148020b40140d91544040206080341c03900001c250b540c4000b804040801111a00103815034a4924100244980c04401a04135481c050501402010f0966080d22220318501c08130f05449080195030307845040040905030440b50b016070200041030340d0790319841e241c00380c1c10b00d03d6a0710800d0409800411800240d08860b440c0c8030302c101080c62812601d01c00403e180c03900b8400c82c000001c00303a5050f41d80c0f00c803101b01065200e02085c4404250150f0740c449040c280a00311342036006a801c81070100000c0e03110703480490a14000c1010b8076404010506 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 923541294 1250 923540044 923540069
    0xb040b0c0d090f170102040f120210030c090605030907050d031806030504021c051005090f07231e060f0c0d02060601120c0504050303070803010515030105100c02010e031005150a 78
    0x1024402201070801003904c51000103217000d558021400381d00b603040d40414000402c203412202503080c03c20011084805a1a08204122076403401400700d05d154000c400c1004404400203100001c06c12000c4086c1100401c0c550b82259145002449002485200c00b240f40480c640003400601038090180580da0017000420010b01a080c07010501500e14800d460610a0650106010440380324031802008404050050b1300038520666103018440d60150451031400450080001041044280f4031042140c1c0d4910000414003941c0362240310096690780301c0c400141c4400d60004040042a4541059040c0c4c2c00340404040140d848800444009011801c8220f54072070308800c1e68481c030348501b074a0802c14180368994002c240307160030000b400c03601414000014881850081000d60b0501030052140c1d1a56040c9004074180e420003107414000e0052850742c02045a01950341003030000005030444000e41c614a0182c0081c080c281e070364001c032813450743c02c2e400ea41c1044002c901c00d890b00b085c45807 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 923542544 1250 923541294 923541299
    0x7170f0a0302181002030a14190e010228150c0c021c0f080a030e0a081206011b1104050702030c1e120a02010e10090323040b040b0c0d090f 61
    0x154060f500c0724009030354a071907880c42c082466a482030040b00302540303540155200e1103080750151842035580c4003c2003001c0148180800c0c4010000c0707003044959145000040c07503005c0b8005070310746244402d00c0d0726a4481e903596405021b5860390000e18280c040d175049a02e401c0745403074400c01c40350340024910002e001d880c080c1c1c0150500c50701d190104140f28888141d1f01071241c480c0e19030000810011100c82c840026000d8540b585800303401d8074060075070003505540d072041c2c0d900001481550000c0344070100c00800a05c1980c042c203000040007202214801450145244c0022201e070803d400c5032140389800041200b1510000c00d403540d1109900c0208180e2825540e420312040000030490352a01c41d03440200009000c503006080840c45540020949100c035a6640e800c105c010340d10300c1401483c0c1000e00e408298000410000c12448610100004141e000c0d24503a92203a6000101680c500060026500004100410500c1d080c141070310740203225080d00715090151840b84100007030122906 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 923543794 1250 923542544 923542547
    0x3050705031f0906180501091b1103090603190c0527030a020d08131a04090b0109080d0e0312040b0304140a1e02091f1a0c07090207170f0a 61
    0x30b00861036440480b5078861030f80c8106140940d88150807a2601029042d5182c040410a00910f07000d0300c0c0c0781c517050140b040e4030aa568001014800d6503070402940c0b20311000b501b0001e004440301c280b8040c0c15640c1d6440c0c5003c417850300800308000c071440da51510224000043c800c0c0262880f01120840041031b600d44002031058050000c0318650b40342c091401208016507a0700000802a84034034103240d1601010026209002d125078061442c4101c640c244a01640150302140e090b0303010124001805084000121000540c0703401480c141d2013440712001302c05810000b040039030b580440460303584036401c01e03048080340614880c410b40c491040c000b040000300e0b100382c5101410040001c03107030310b0600303510f40c0000c41c890001d040b42d103064500440810f50030060a00c1e07600203410340c881030888200d0a441c010300c0300d80744a00b14801c0340c211008a24070010004030340384039600c1012100c400d03407140e6a40b030080d80b001d0021250b1410400301c560380b2001240640b010200c130840c0703850528504940 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 923545044 1250 923543794 923543821
    0x60f0f08060f0307120b0402100908120c16063b0d020102030d090b0a05010b03090703021e0a090b0901050a080a0b04020d12030c20210415020307050d0305070503 71
    0x12455030501444e2408039400100c0142524032600903200301002d400c19006102c0080e00c81810b074020454070903420700c811000050000e01100509031400e507107940c01d01249090456070f044400d20b2912030500010b2403a0311407280b904000301100d41030056a00c42d0f821b220464000e50356285501d9a4000c100580d04d4065200602140180140ca02e00345080c9038031130842e0070132041141c2c2003111005000c01c802140c4512405050390f041840c0c82c1d410038280d800e5442c03086101c000e10400c40100303a880040f4040c0c0400c841144068919480c86403205054809046c4510006004094000c000a024903002d00950216000e1002411100f0402d0f00da0800c480c10051059801103060046100003d0303010659841003681c5541c00100018082402071000650300042504003058a0120310007140c0401e440031060401c15501d80301810072000e0011600480d4090000c20215289049050b5004070080034114419402d552604100010550032201d003a65400001041400000d2054400c40e1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 923546294 1250 923545044 923545069
    0x30d0c03200604061a03030f04030c050f0d110604090c0c02030d020a0f0b0703110c0303150906101b02040204150212031504020703020a06061203030e0312041b0e010e01060f0f0806 79
    0x80170341c4440016940844d14590025521101c514800030341082400018590f22001e40300445401c40b84101100005481208001018001c805070f08810101079803014104c4000b01183c090034001c000000601400d2040d02c007005034001c3c060105582d81841c404654101001d50108413202c0c5500e06441c0c40700d43d90402004442415610160010008480f80280801e4120f4070000c507980d10344445200c103802100c0e01c0e090b0003501c2880c20301031203583e003249600c0120450320b040300b40b48c45030384200104480302500183d045880003d0201b4400541e070000159810140c003107a2980401018400c21440115190101c1c0c41d084145d2030901d24040d0010b00c0c0c214040d00c115011200d00740c41e100c040311400e80c00032000d40003080005d0109034244c09804280c1c01e505020714200814003200e4a40450010401050042a504a248080300000c0701c0c070054402812008029a1185001c40c2041d10a003d28800f280c28088038420007407244900c4ca41264843c0c0c0c03287e0290b1642810f102154040c503 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 923547544 1250 923546294 923546321
    0xc05160c03051c020c040903020d030b010903140624101407020307170c03030f0306010c08040306020a0e01030e0105090c0111011e1506020628020405030d0c0320060406 74
    0xc038001001c51810480b240d0385481146501e4803070000440c010349000031160829005a040c0031080c800300b0740110354544070f01400d081c0822449008001203d9184090f04001c1c6100490a2091171290f0005020303403107040300041800384041455408141d4410a50380550721441240301c04010720f22078880c035180110740903980c80c104801540020304241098100a03490104007041d05915542001141890f5406402a51a088044070712411034030005100c1414441c802d445e00b8200041e00c0111801560800400c64545200940c01052054040503850000c0d00b0890b51070300003107040c071815014840c520001c0144a49000041d100d107040519000c059558609050200768581c0340c0e90b401540c5020400101d4002411980d040c140f80741d009101158031100801c000031010700e441c0c03150a040f0710f81e5121460751190b0444081c0c032a58204c0c030340600031083d0120300310307420200d10040c031446500c0c2d680300300c1d150a01c0c0c0d004081c1d0040071086164012401304010039601d5202002e0500003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 923548794 1250 923547544 923547563
    0x8100306200a0c0210050702010801140604180212061f0c03260105090106210b06091008070305010905072f01060602061b0f040302130b030706030f0e010c0516 70
    0x205010840d5030410302540010030740c400341d0f2004614000c1542c001420560600f1414801140c000802c014014040c86030001071182080c5c485a4440050790028403c004280d0034001c004081403001e5000b4000d0603007070581c16401300e2800d00d080c41c01c900010341903480440c5101c105150803507042d210b042c0141d06001c070040d40004040022062401c007081d04034989116545040b05016820b0310503405942000702d9104108ea074500d820150f08540050960041100c0000400003001417050752500340e0b100d456400120001a00164400d1084009403001c02441c2c4e030311190354090310b80c1140d04c10b0000c2c02c1c1c0000c14070b401c00403140e8001280e5007102240e4075004070b02c18580c21075085422181c0540d2100007007002000c0c0320705420000481e101201424004054440b6065004500009100b0010400c03103258840007640039010304c400c0102140c28055403240054010411880e1003030043c1c6c2044101c14520005015000710008140d454500e420100e41c0300c40e020014242084030030414 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 923550044 1250 923548794 923548841
    0xc060209010905190806221214040303030e060a0b0112020d060b04090b12030c061314010c09060e0a0f0b13150f2a121209060c0f08100306 61
    0x101d94504d0708451440d90710707024003281401744072032401e94014011760082d01041c0f0349520b260f09903200790311040d03842601100d0b0301a90032420745000042c8050500802c1000c1400828154950000c00480c0b05c07031410703242c4645034840d03500b0684aa002609022031004149185089040c1d4010200000000d10005186480b1412180550f0041d0320221406444440000e842d260240d40c420910080d500214035018120310070940b10500207100110f500c4002c400c030010b200742e5211240d80700e9154402008007a000701c2d800740104901d03000f8880094802c45c8a21003909008901e271041e0b41d07401c41038400051400f44041659844807008600c00c1070507090000c0d2030031341d069220300303450100e03220070a080300d66403801400004006c0c20044003031207480c3c118030903600401102b002c15400001201c50a12525002c0d10b000d50000c1803590024070b08001042440300542c402800c4080031341e00d50b07600005030350080f1040d04054900d010341241d120020000100c0b40c1c0d2003440c210020301c51036400b4a1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 923551294 1250 923550044 923550049
    0x60e090f0711010f091101051903050a09020d0b010f1a0306040e011e2909040213240e090d0504120f081605010e0102163f02010b0a060c060209010905 66
    0x4001012a03074105407a03403034245c208452120b01c11994802881c2460a24809207003c1000640303070300d864024035030340d54081010361500d500002c1559402500e070340d4500c1590716202a900009200b182c1ca42c0982800100c1e403118254002d10b00081d400c0081030a50321200e007080002c01c0980c500c0d10840d0768480f0b07206500c0e00801c0b681c0c180303d52010303000141d10f900b02103002203140c10103011108990f034003c2030f24881e030340c0e4100540d085038059407030f001d00707001d2801020000d21400480521200b90000d00c04114005441803500717a440030107459140e0b448203c69182d568034022614008280e00f0311040c011210350381d6807200c81e01c0c0519460800c00a07541c451944a912296041c01c00f030044103c40400d22100b400385440480c02180210b20306000155280c0c40e11a400c0c2c0300400380e040800b0351011940c840c0002030903000c281c0709483c0410a110000d1420301d0211000d4001650070107010100c6803400ca03520300120b0304180c8403542c0d0f42c1801c0da981002503200b81c0e461030501c0340d110000300b443d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 923552544 1250 923551294 923551301
    0x18010e060a0b0a030b0c0702040b0a15020111070209160216060f1b1112010b03100b1c050a020d21090501090905011a0a0c080c010b0406060e090f071101 67
    0x105014094002420100004402d54030418462030140d0824207003000001c0820000b0f69000f41c0541c81a61108000d10018024296010a1030740c02a503920000c03d50341071000456404602c03a4000308079595104680b22032502480c04040e41c0403112000096410421915000c90031303001c0c4c0b065500060344500300d902030814a810140000c0c060300d10511456070800c030252600144902c852142d030025680b90040c1003981740c0650302600e0800d20496180c1401d4116065420000741a101250180749510008102001102c1d04c681c401e4846c200c84144840d418400c1c40350484007400f042c6c002e0b5000d000520740b00305012650890b0900c0c0388100074400d01012614001c007170380c0e081b0481d80340c100014803c18258000d142d030b9525020040285050303c05100044800c00c0d41e00c203484054a1070309654031038a90784040c10300d210001d000c0d401107806511002c80b12104840030440c09845800032500041d045004907084030003140840c50004100648075407198040c500a0031460301d204851382074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 923553794 1250 923552544 923552561
    0x201050a120608150703150b0d060b03090d031407090509062b030908030913091415091b030c210307030309050709180f0302010609060e07090503160e1801 68
    0x49400404107550803604081c02d0682003192480d040c8048031600360403119031f0200b40b00340028440c00203800b01901d5400d400c04001052405010f544900d011600305490b070308114003081c0000c1c0b4081c02d4480c2101604c0002d401103085564140c1010b05000607c00d0f03121000c2c0070b0742e80c0801c41d0385003504042910a81e042c840710070f039500d0002086191402034003c0005800240c040c0d04140400c080c6a114a20906010144440c0104800702c00d4206005140d40c4601120707440d02805e50342120598180c94400d026040c0c0c03808945507809441c41c0c038040e0003008604c1940c190848038841c505460030140710000e40e000da00048104024480c3d90500d154800d08045001c01d4a6a01000600006001040c001c00312031030184201d41240340c1c012141710026500400841a030f09245003414802d521041c00380904000801840b81c07201504140400111200400100c42c2d0102040e94140407030710701e590580c0c44001a940e00d0414210545441c4002c0c1428400342090b0748108081009005000300c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 923555044 1250 923553794 923553809
    0x10e0a031e030f02210906061c14120408070602030a1b150e0a03200c06030709080a06020d05070306051c0203120a2613122f0705040510030201050a1206 67
    0xb9544017094480c6020600506884150b040030042000d0354071400706074403902c01d4004040c0307030380c245916000343c501d00010b02119003840780015000e0350790305410040050b50110801c03122041c1d07407120300704c0e9640703d001502d60000c4c21102503003c04061160b80c28002610401c849a1065411a04542101c0c80b0265040440d0320102c0450285a00056840d262004060200c402c81d4844020540d586200c40b21b03581c02507100000044400d0320910900c00070700b40b403c003500c4009585081c0b02000e50400a2148000352514001c2044c49002c2e10411084942c06024a19546181540c4920b240301e02141030342c040c0182e00300700aa2001040041440710102c0d2141c0105800c1500f80000000c607003405215507900050500000b81c06a058822005901641c18040c4c13540304041151110045c03c11038071810b24100e038424006509603111301903840c40004131055241c1d501d040009031903080d02c1c101c640e1380c0b0070002440036500c01c6005108240e12403c01000c0740c4c0d00751701944222006a03000c02c9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 923556294 1250 923555044 923555077
    0x60903071e0f150209040e190308061201050c0301051807020a0312140103061a1017060109030f0c081b0105040909020a05120303061c020102030a0806030708150603010e0a031e030f02 80
    0x8981c86e1a05c035542000301d101c0001d0410340682d030488810b00684003c0602030200b040e0003c4d6441d501d0044060700c40002d00000d005a0425041d5814140c100b801035900c07405c6c81441c1c6034981007018808a10038000c55000342880101a28203031044040750300c004034001c0d03c41c80010b840d1140d1000c018021445000002800c09000c1c11100003030f51001800303441598807017204030380c595001d04200c04440980c2c1c40e0200d661501c4006032800b010703981c00101102c105614078018400c426044002301d0b04030b40d06030f807628880c00c01d804155165015006001c62024442031002521680c40f8204e00c91014008803145907e42001504c0403032809071401c1c20307520000c03c000c0c140c2401e05c0403840c0030902800120b9000500e500107512030007690f003200c00300111440040c0a03568100150f070010402142900d002215030901c45071440703000c9030340501035820404865005000007541112880d01941d03201105510b1480c1c0440001103440d9650806072940b10204000000344002c0405602c0c4090381d9 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 923557544 1250 923556294 923556307
    0x20a061e2f010e031c2703030b06041a0703030b1c031202091c140c0904020d060b04051e100f0b0c031909090b09010f15030905010608060603060903071e0f1502 70
    0x5403010424074a081e1801000009603c0c00d401b003c0c82007880d890700b40442d24066860200e400c82c09264041e00350101d0381c5241000e407419000007070022074040e542c1844486c06d00c00a0103420306055100750204041c40355031030003081c46000d00d500c120f120f13040c01501d01212040020342c46014500012000c4d420f0a503a0f104000c102d031040ca24075200280070b000840090000214182001000680a82c100000420800030964800c0f80340c2e4200600800c590b080000c1c01483d071051928220300005072220205200350040910001150121039000d0fa0702400c00300185880c4d00701d03e0013036445100c10b00071540c62009142290805407010303038694208c3d61826600b5020303501c84140c082d01030b01c540001440b02c0520b0914800c25110f00c0340180f1105407074800100c006000503c00a011946000000304000c10081138190150404400312034464494640ba19203030b04c90000c0041c803180c8600d200f021108281d0340400021802545840701040d60707a00c1c0c010a145840380c001a03802d60006a4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 923558794 1250 923557544 923557597
    0x3040509100e0103030c020d0501090803160e130c0c0f060f0b09090d050a092c01230d02010c0212070e0907060504120c03020a061e2f010e03 62
    0x1035990041e9210300111586140c840310868003003041c0009000c10601004580654031000403c02307159a02500801c07141703c03241040d2403550000d0b540041509100740c1d505100d188582c1c190898800000c0050078038180f820404070060004401c0b604c203101c81c0f020300340003154582e001c80f9182401180042084090401c075441103414044407a132040450390180500030400186c5200c00e0742d214108030780d40e011140001e0b0f801c50401e1380301e200a1541e03e0a030145664810900d680002c0341e141d503000203a41c03920b20310380b145002c0620020180d00e045120310028640110064500390042c100f950844510b6004510303400c00391040f00d4826402080108840c007a1418001d030300101210140c01d0560500074000d00340d00c214445d403001003004051440901182d4200740f0011580105202030303855541501500c00c6012441c400c0e0490401040c06c500d4038040c05a0940e05805104140c0100f420b6644c80038107495200841d000c50766079518440030a080400081c802d142101c80304600c0758040103d03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 923560044 1250 923558794 923558809
    0x3050609010e060411040812041d04030c0b0402010c021003020a0f020c061e09061909090b130e0a141501081506120307051006030b1f050d0221030405 66
    0x10300800040c40104146400300b20459004241150003140a4038180c54210f501d015503000445c441c0541521040d10200600c020021198403203c1030403d281045030302104440119005804121991120400160301e032803500e91051050400d0704030307601160007059100002e40c0c00e6001107540000d07910700950300080b400341c45c0012032000305015007080020541900440d1500b1081007040003174080602d02c850141c6607a543c0191016441c0d040d505e050541980c041d0f4860004614965030104044419005641d43c42401910a801030704132404200020441c20f0142c0849016150300080003a078803e5202407031021890042c4420080340d46480b0010034103901216055010700c1d1002c55134007812210030f0b400075045a0341360149905201540c15481402e00003013007401003845000c544039240c1d003c2810340e40244d08141c129a03603481d281c1406102240e01295404801108200c5482c180d052010194809840d61001e003003282802c0311003814046100c800754001140c10302842c140803d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 923561151 1107 923560044 923560051
    0x50c13091a011511030f030a0f0906020d0f053607081005070507050a0b0c0c0304030606061e230c0d0926060a0b0d08070308070305 58
    0x41c01e055114401d01520301c000b40c030071101c00155449441e03140780c0500c40c10000c52030f2a200400320707115030300014020400079854100031f4130818610701403c03c0d4240b0803000980c445540c000741c0e0051300c80384003e41d1650f61800d403c0003a460041025262002e11620078100f29001d03040c0c51418804460700e0000d00c9110b05900000c000c88001940707040700e281c0000810442d19a400c04840e640301f01480a0201da01141c0840c02081844030060703001416207244a18046034000c2da02c3c01d680043d80103841041c0e40304801c02110350446000404a2403082c49080c0491440102500c0011248000c0e81103049203548002140500000c441d500c0071080308a5100240d00c100c000c040a01b030b801110301a440303242c4e405101d5504042d00c40d64407041007001d40025074403250800010f1403202103060788103240c102c1c0302002c03414000080c0a000e020780d49159840c41c0004010b420b4071f00c0503 = true := by decide +kernel

theorem cover : BRFrame.Cov 923381294 923561151 := by
  have h0 := BRFrame.cov_init 923381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 923381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 923381294 ≤ n) (h2 : n < 923561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
