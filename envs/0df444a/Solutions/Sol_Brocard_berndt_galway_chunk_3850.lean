-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3850
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:52:09.569608+00:00
-- url     : https://prove2.me/submissions/83396115-bf5b-4fcd-887b-795d5b64343d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 692266187 ≤ n < 692446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 692267437 1250 692266187 692266199
    0x4060501170c030624030109060e060d1403040e090102040f1e090c051c0b0109050415140a080d02010e0d0f08060d05100c0203040801180c290a0f031505010504 70
    0x2c0516007082d0080c000c2170400c24015007904201d0012078003103008560101c01044503540034002c80c0014002499807038014140503001c10740811074864064440c11502c030f202d242c0340320b0400444008040700000f00c2c465050005c00c0030b010f0751052082d000100c04200c8080388030001ca007440c0080c2c02c3c070b0300e0310104c1080c40d0054040180c50036070060800d10400380711010386d0901d21609580501400c0c480010040c10102c00901540440c0d00705c540120301e000e0110080700c1d801010401a1501d015100c80c1c42e041c00d40c0000d0a00841e41c10440681c0901d07658000041e8054004605555241c03090707a200c49940741085500f0081c42041d000042d061402040e000e042004605003c1c90103441940c000d4600104050291018105013200580c8001010440001c0078440d210000c0202c4000006483e0243c641107580003550080c0703403120651420180ca40d140d540c000c203061a0742c07890140d46600051402410702c00054401801081c1488000c400e5881440b002100380c2d2016103c6500b071a080c40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 692268687 1250 692267437 692267461
    0x51c03060617100b0a17160c032a0b0403030f050f060d021306170f01020301080c210a0605010e0609010803030a0b0a080604050a1a24061204030801050406050117 71
    0x1800fa86100301c2c1c8803502040016022000302405100c91b2503100c07000c2c08200d8480c1c01d00310018009081c002180c82c0c294075850303002c2101003041e50103151118141e28140401941d506c51200078401c5840d0b0149600c0822440c401100d1123a4041d0310200500d078418a8110306aa208403085c001402070500003400600e000d0240a03c0d040c005403241800403800c1d03501d902200c1d01ca030001082014041c9080080150400c401110200c0010080d81035525040c8040d81d1405201d01091040802521940380d080c2038580c01d9070708285140031294100005c0c00c100c002400207000c0c80300103408490016419017000034410781222021300040d440c40c0e45035484103000b450316004c1d007640168801800030f0104401c004c414021030181c0068000f0b4145803070305135034203d0a2094168901d03060401c2101c826034107603208000c05881e2601c5065040d40a0020b142031007402545604002407074181700c14540e012080506883c1c0c192003c03c4882e0715800103607128042114188100722000d800a44500200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 692269937 1250 692268687 692268691
    0xc1f0f08090d1b140609011d0a06180f12080703090b2a1b010c0c21090e18010f0207020a21020d0302030c1e0a171303051c03060617 58
    0x303c0204846800d10303943d514500d1309a0400200b5642c8000180b1000160a115104007041903401240060158190940d210111389002528440e920303000c20101c02101d03020070214036444250b0403007503100381c54151400b00c4151003210010304c6250000b00340364000c1c40b0700005107400c409000003580c0d0350000c81010b82c044900c0700c1001644c0c0a0141c0e4280010000780c440b0400c12003800150301c801c1041d480c21507421140d07a03c1005080c440010100c0c0c24101c08104003107040d0540c40004031a082c003076810701b0056011183d1180c810701080b0300000c04085031114200305400900c0040100c28242090303015500000e90b02c0074806a08001041080401311400714003408042d0248100741c00041d22000e80c0c2c4000c1d809a00006000800500c2c00c0c0000d84121000807100c1a1414100080c15905c2040850083c081890b020b0940000c1e009403094039180c10500328076a543c1600c900e4126110f814002c0b05a00281090100052490181c0215130954149030f42d000008600c0c1c2d0020115000c0c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 692271187 1250 692269937 692269967
    0x9091605040f03050a15090c060e04090c060818031806091302040308040e010b0a14030405012a14040e0610030b04090317060102010e0d050c0c1f0f08090d 68
    0x3081000003100300098050038000c50068000d403041914500b03200e04040115020364050510b41004240003035507040e00b540a40d6582d28155a146440c540424000d140310540a0310315074071940001f6130550700507911442419200022854000648004c80d81c9000310704c4645120301d000400703601c4a0070044003501402400402003480c5104110540c401c0340d00903041501c503507800040600041340b60381002c900400742d0103a84c503d03042c0c02e514020089040001f80011420000022900b4001d00350481e00c1d802c0d942c030522030314001076203061602500c04410b07030101003000d600e010704e240c0e02d00300107881c1114003040c038001c000d0b40d6800c20031400041c449990018140d54009412850310b5900c122210325110b41c844600a280a600e40404514002c0955045a040c001920391001002c2494440442c5600b4000d44640030a03110070b041c0082381c2c9595400105070018542a100c001c00e803078198506980710301f41c503144d9251003144c80310821102c400310741e8001e01207240d503207104000712061000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 692272437 1250 692271187 692271197
    0xb09240f011d130606050a0f0207030203072d0b0408010c02010b0f0d031202031003020406050402031603231f12030804030c030504080f0109061a130203060406080a140111090916 78
    0x800301c3c501c94122403030b6400c110300155001c181581000c3e04451200314088240c0000c0c01000d19503030001e541c0b12024000e0059070110401c58804407550350800750004e044c00c20f0200385054403285443c10030b401510420700035600700540b1452090042c45240701000740544100740c0c80c10b1103024030408005880045041043c1185100e00302c00071032001d1800385000c0100301c0702080c0345004020030f403440342e08964800c0c2c0c03041003882400ea44100e4002020780e6581804201c00b02c1a1002c02c010000e03c40d100304080c0c902c038040041c019481c8155061041815501442194996880a111174105100100031070041c101113070119010b18140f64115120f807030f041c2d1502c2e881d038104a0410501c1c0320b1010041e915040e0210410010380294000030740c1ca852042da500004000140e011401c1d07130b03859035159038004041038568540d42c1104015004180851701e451241b803521001c1e0300841900c421440d40fa01c1801403401c08004115544c90900425502d015110700c80c0205800140300b0b08181442 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 692273687 1250 692272437 692272459
    0xb07021005071b030b0615091927110a0207061b20010f02011a04090519080c070614030408090d0b010f0f0807060c150b09240f011d 58
    0x2c030340f001110742603440e032519000080e103903252082110740f0140045100da03600203070301560312000b0300940701540d00c12603102e4200301403043c03484542030f010b8010308140c4032440301c001c820b20b0b541c4008010302c8018100810290112000142c00e034008e411145005800186003008002d200700049407070040d11941484148a03540d070740000410700782c1c4110503041c0b0b84144840140da00810f030301d00b82d00c840f03000900802050035400031800c2240d0810510640d40c0304201c4043c040100070b00300e1603054a654500c0d4080281c2040c0000b03420100d1168003521800d5804103c051180d8192100e29042c00191405c540702c82e0b45941c00c03508410121a0840110314220010130070842041f4000c1c50140c4202060b182010311081441d906508174258079070144204000c4140d002c1004640c05800c960050094100c00701003e000d41300d112201e9500216890522100c0d105154903a0340f4001d4604910541b6400c0b8414003c2c2404800c00c2140480c1804030510000c03a4210003030201c420004002041d40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 692274937 1250 692273687 692273693
    0x2040510030b190501080115050f0a0c020a0816030602030612010507030b010e1c0221010906020d051f03120201020f03100801050c1e1608120603160b0702100507 71
    0x4240e98500d5003000a40380c2c1444850390821151902c62100d10240c004015418030700080c10b801d4041c850f42e400c060b02181a5010740f403044050f50580f1481ca00c00035590b143c0c9400c010031502c503d45080c1d1242d5040440040c0c0708600140111080f0f030a0803184001d2480c54542000940000305107541040c1b07030541000400c1000c1c811107214400645002461322a0300000601a10010441501920219900c640406c000704500307418190f040303501d546041c0c00b0526202e00070080404940c1c556082000a008025003600500201044c40504001b1a43c40d1101881600845502050480e50641050010170340009180c2a0041140000351414805c0700d0101002e41c0704886440c0b103445145018001c2c40401e009454103c41040302e06814034242250a2032400300c51140304845240004541090000c0c070b0081e100d402d90049001c0d502e031005d100f4080500300045894920034000c151101225400c1d4103201c03416900d000352298144000e6134240002c0c001c80b01c032280c041c80420301c601800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 692276187 1250 692274937 692274949
    0x506070c030210080a110c0a02060a0e0a0e07120605061b0309031e010b060406080c2a0105041208070f05180603090a140c0607021905060c0309011404081f020405 71
    0x1c0125541d44c0100c0b442c2c16411034080303030304204107299903000c02c10030341008140c00280f4011070394049030007a50b41d0403564000e0b10b0036045400340d02e4200581d03440006411032400e0505125041940302d601158155000404c116641800340ea54000030521000c200100b12600d10344056448208881c5015038040011b840e02d10303102c0242c0c50320095800010031004007070241c0104d01c01d0a46010341001d0600c50090036051004012046005000c202d09a10542e041584464044c4400b406552845012100d5020b07103821281900c082000c0c0030010019481003020901c5150203a03039220320b032265403070700300c0701548a400100d660390710070b0094a4041e6164001140202c1b0910010724507a00685058140f4002001001f542500329841d0308241b1707110282191f2070280d0454a84130900e0045c10240e1811381c080e00034940000005c942c030540080000000d05022000f42c0351000703900000001a0f000d40b03d82d0140c3c101e2600182d400b420b21507800000e42c980f143c0d140b440981040c0c1c8400100b50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 692277437 1250 692276187 692276209
    0xe0114011419090f0b03012315130b010305090a020901060302070c05060c0706081513050606071505090f070b0a110a17040504050c1207050930070b130506070c0302 72
    0x310283d03032200c05130b12042251003011103034035007500280013000117540407402070020034a071452030210000000d00c02c03003a04040c189040c2c03002021340d82007001c00a100e6009007000180603020920340b9003c25500d50002401c40341c003590040c14601142e007005d2046010303410242c1c04a4946400101c0480d06550b100007905402008000921103640b0b0600001e2402c0380c00707850204074441380d00c034820b01e0f602e48a105008050315071801188540781d07280400c1c1184079410000e064079000342c20301d0000c0d2074540c01050080d810023003110056800288030580341d0707405125001e03500b1801c102e1881594000d003025038603c008001940c1c0f180d012920303030401d840103070b08c0c54213181a0005420704c1940340c01c3c410b450b001048c440d1803508100401e1900389600384050072010901c100860700801540e0382c03c0e001140c40c01c02d1000140e800c8003841c94000b411411030851102030007000030115817011b03004169440c94407480d00c4800e45034580024401d6907401104141d4045040890202c00b58a41115542c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 692278687 1250 692277437 692277449
    0x6111005150102210304060b0a030f150b03030f030a05090a080c0105070f0c020f010c080918010e0906130b09150c0c070501091805190e030c010e0114011419 69
    0x1086000401000a0925208450b8405954007441070740038040d10710405d480d40954012030004503011602c000400d6143c0c658001040309a000e41641c04000d80700703205c52500100c04805211384ca01c004100364580c020b02e204203202c07500600010300700b07100c1d0fa0003051b044101d1000380c1e0a58403458660038520350204220120b9a9100d905000441c1d502807550f956034405894005540921030740040e138842c0c00d00c184a1b04108034602040d0501c41078208a40d64104020811100c04071001003e01a0300000d1180011020203d0000349102c440404d180703120b072501081c00c8080540302c2da698420f80d02301a000300c68502c50000d50f444408054000c580c0109680200710741c0305e900200a05150030030503040a410050662010451242241000307041c0e60500d03000440ca541e60740304400b010740054900000d28034209000003001d900040024200103103035030024484900411700d02400d80b58a06403411506820900404c50290030050b280c04074140148138402107a40764100301449550781c4c01c14 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 692279937 1250 692278687 692278711
    0x4080702032d0c30010617060f01030b0c13080d030501090c0c080418110403030804021306080c120a0b04060b0112090503090609010c060e012007020a06111005 70
    0x1002c0700340c0e640000e00104104004003042c02da2140070034000340030507150010740390041c2d42e2142844280420701000482c001c00810001f551000300600308075a04103080711501600c4040ba2450a850301d00c1c90580c1c1c0c00084442d0291151000070040790320102003040107107200c00000c43d0150342400a18491141660041920f5040400c600c2c12103134012411000c0c8001080314030300181501c41650112103e0010001800344010001400741581b8a0a1082844c0c005404401c042d0420680c1e4016170080d03901c0c00850a2068410049407514011400d0076409405070032514903183e043c1d0510704c00c010301903840741c1015550ba080000f4003582d00f10340071522000045000d580c0310301c840600002d100418001c030305858441c43d4407441981000390040c900050b62010036401101a280d6817584a0801c0040141e6070440038000c0240c1c141006956121070500c10710414a0001d45040d03a80007022410800e10f090310070340d0b4070401c6440e94800d5018a00300305200e440140300b03403840b070085001d00e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 692281187 1250 692279937 692279983
    0x910050a1b03091802160201030c0e0a030506044d09090a140c0105092b030203040501030615050d15080a1a06090702061306060f0b09040c260408070203 67
    0x8011034004c01c0102d4492440e10611508030002c1d203c1e40810002c03502824009407441d2018011262445a2303800395400120b8004004200203002801500c598068113143e10b400c850b0301c2e0b401420b016001c80811212043d103400707443c64250042c0d00c00d4000c2c004c40a044d0201c0380302d0041005104204c68104403608605482801c0c400722070140e000c0d5041c4a07010300162843c44002908a00610715080d01039000c444900100700b844060000420702c0c2040c2d0b0f000320b803100c0d1030700a44d40d61040c020940002c0c00c00c040059013960780100c4120060254960508089270303541a840100610741000100024025001407440800e00c21030032064007aa2088403c058040e01d40207001401906190203241c284081080c4d107603001c941c2c0360700008404002a461801800d0460260209411110000350800c000189030f12490713008254410081d1024450403001c0700c01500c40c1300007203200d82d004061030286d20483d50b5a02030840d07403081c030a20702181012007540100c4e29040c6522074021901101c1a6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 692282437 1250 692281187 692281199
    0x90501060b0301061d031005040b010f0e10151e02010204030506150a2927010807050a050c01110a03020717030c070209090c04051009110910050a1b0309 67
    0x40c0ca806006001140340c95035240ca02c00600e64588940100400300010200d41c0051390140301d00c08605036200300034005428107043c01520b08500388954403016080282c00181c21070515032043c45040b00c01c00c9001c1c424607140400a01d9411a40c0613000c224805141400303c3c460888056560215940016145c500750f251aa02d406000392003a00c42d407120725071100791580d90724070318020355068020b003a08c04900051445005001c0300710054403040041a100710800b2990b1445a0701751520f0070504401107107100660300d000741903402400280c401c210039090a8050300051000407544000000e80c450091412262a00051700060020383c00082c00c506001c000241c071a058660621100c1c550b09210020788064410114001d01658403440081d40328030040c482029038601c080d009000318130744000641e0710b00d5074030702801600501e002d0b41c0c0e22852070300c001601c61180c1c0c0038019890380d07003002005481540100565004000aa07004000e10790521500b001003d4070a4650740006410304d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 692283687 1250 692282437 692282441
    0x209010f1a0c0a291e070c0308070f12090b0a050919020904060f14071b050705060309010e0d051908160e060409020f12010501020118080d140a090501 66
    0xe0195440c07000d001441c00c0b800e021400600140d4444103000003a0308452900c4081c40c01c0303004201949000c402002803840380321340f000900b050240c1c01d00c0c1070b5903034401c02910048040c070006400101101c00082d0b100740500d80c458034013242c07802c0c84c6652141c50615201aa1000a4100c900001c01014403040311102e00540760064809005030691a1002c00c0030080d401075070801074800c2d013408010500b4031059a1041055080c0d003142801008544c2088004491050312420005611903800c1d844081c3c1f500343d1180c045901101800c955440c01c0204046500003900b0490255650050103204120410480400e03000301d8591030703142d403900c000c600350a840080c068414440050100401c0c2064001c03405102c5c001030402001f250341c24800f1a8032801960450f000080c030000d9150140c104141c045d008144403030810221503a01c1e00012426100e0001c800750214070044840b0300002c0380e8a015040307640c00d40600264820503a180700c10079800944859000a9550507000e080c88028 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 692284937 1250 692283687 692283719
    0xd0c20030301080a111c050c130510030b1915030b0a0203011503020c070e01081f060501020606060705190803060111012d0608030403060516030c08040f0201020a0209010f 75
    0x10001560942d03141030400d944940c010031004000034801450482a555441c0000404602c100c08001a00c211483c1040d80d420f0294404c0707204043d2041101900640c501445d4443c0302a1341039000310382e06c1c6950314a0382070800790449001070b003500c41c1302d0b11200852140541c280081d8503000c40040c90b50a01c1c0f200300380f01034407140241d40100b0041c01038141100d20f104507036a0038a40140d40750140c600403401c03d1515008504003640070000003030a40000207002140c0400404400e4030715419002c85001c84906200712070150300000005005860401c0c0900b140e24002c00645601000fa000c0d881c2c910820301c54100c90000001c0f0504c015542c0c4003841003c2040075000820422000000c513004001940d0303c07452604411181100c2080c14a402440041a016089a845076100c1c83c25201618080342c1000c88200e50b140c00302c0c0610f00c81d000b8030450780b003140c40d82c10235a1500c0d1201c92018039110f50683c15803107194118070050700c90005072070003400700a114881e21410050890000141 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 692286187 1250 692284937 692284997
    0x503030f09060c1605031207050c0c0609031903110607020d030e060402030606100203040b0d0209100206100b0304020f0319061d0304170c0303030a0f05070f0507060e030d0c 76
    0x300008000006000004580f13001c034284103681070018a510b00070385580f10340701b01344140120318401c1c130203500d07001000382585104040a41d51861420b0342841601d004140c029a4036611031069010090f040d03804103880e40d4040c0c584039901e000c0e005441e51410708151140320041c1d00c10085c00385da0692520a0703160504070ba0b4007a123198242600026507c0c80c001c1d144c1c4d4841c0e165070305001c03ca02c1c001c1084030000c100e01000561181c00b15400c4c08025001010128003900c003101c1e654003034034400324010784641b2a070036442d0072143c1804441a00c0d6080280300b2600403500380300d4100e6555040180a6402c860341d62410301001081c6481019144c0d04e0450541082c480c400380c190112010054405540c6000440c5070343c60025186e4901e071403c60000300703806000000c140404410640c01151036204204c0007480161a81041180c0b14400400c20a00050090051030300003a9560400c00c4950b2020f03048030300b4801207194260856162035074500203d1078890380d031040703030010010300c40d00003031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 692287437 1250 692286187 692286193
    0x303090f1202030a15020918041203020f0409020c07050607081309060b040506072102030c01051b03041212020a090317250f0c0f0303030b031b12190503030f09 70
    0xa09a40401c2d6249031408000b09441d8161181c0403000100381c6c1620a0804010b145070b1192002a01e1703402e1006043c3c4017030341d1a410710842001c02900a0003101d020507140c0c40f01c80e181c03918042c03020009400c01241c00c001401041d03030020785940c0f000081c0509500030602951348051294041c1308640b00c662004141c41d051003010040c00c0d2810064804840041e5140c564802244c0b60162681c4c61010780d1703a101c0e800c12140d035442030754004081d00715001624001c010980350103164a10051110060310305a001c1000060300003140e05105400c00d81460910640320051100040140c0c2c2001032605c0004103242c000b04140285450002e1065105580701c03072030b1400001800510240200507040d42d001c910109004014038184111701a940003403100203615151040545100010f02c410390000b414030f2000546d034503010401c8070b82c03407000081007004c0020040c00d100da2042c0c584014003440c0216144221401442e0707901c050b040d4890009507640380742c0030074660b0351a076019144015542c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 692288687 1250 692287437 692287469
    0x301150e0a060905010c1403030a1b0e0a0308070311010c0f3002090a0306060b0909010806070807080c160c06080903030403050f090616030c0309051c06240303090f 72
    0x7a04200c43c4800c0d15020700c0c14142e4003010f814140280810203a06405610001081100460720b962062820030048810fa69500003010002c8603510b012194465008681003000c00001d00c5500080103100e1003800e1002d90300e182548940e007100d07028443c5401284c24000511903156000392a000c01303040300c0180c40c4505007240900d00328026010a814001540007410303440b269103010104008550100061015584400f00e2100d142c108050700342c0074102c4440013103164000411185c4c4034244175540c00d02d4603500c1900c04c070390000c005404004082010018602c1e007520b00c00030350311031900811084c100c0038a8280000c2c51060001d01d1080300d07420501c04e210010b03a2000445680154400003107440321801e09c0000c1040c8180c04003070040160a8243d0303010182c00c0003a050480d802901e502e030303031903075120300303111441032484450240040400013160004002d0b03409245404506000b0905c0b088885024401c910b585070000d4001c0f82c07022504003c104000b4981c1d5020f0115588075072040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 692289937 1250 692288687 692288699
    0x3020c01090b090405130b090114010e06100c081e03040b071701030f0309090903030f0f060b0a08090c09071106070e101101090b01171510120c09020301150e0a 70
    0x40c041c0f0110244120303110320100e400901c0190111074920b8000300048060f080511000c1c0c003c142d00308000743c21500c05000040e500018007422886900c3c0942868805542d808003201c441ca030301c10381112210000e2242a00803a00c1d528200001c0e500000d03059583d0a01c2d00706140400c60042c01041007141100b903440d41404030840081c1120750060141c610f2505620301940d044100c0d0b0007030550705107011803920506500d600004d1003c20255404c00c807000000c80500f003981d07c00e00850309100c408020110050b4490315000340d011280006486074040394800003040d01d201a01d0a000141c1c2014000400d90070078481a90040d005081c0501c102804101281c22080a81c8190090281c11641124800001e4106481c11a44100c51480d6503840c1c0c051140504465101c000e081d01c15243c030301d9020580c4126440c02480c40c0c2070550040d41c034185460030609690041250310b00740d040c100192514071800514040c00140c401803400c00c0300700c41300400341218130130030510074995100200b04c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 692291187 1250 692289937 692289959
    0x7050a020613090f020403140114130c080f0325030c080a02011503082d03060906030a120507120c200f030f010203040303360f02030609070303020c0109 67
    0x409605a400540301e80340c0c00070b807407a800050762080310280d0a080342c101c0e2a080d280e000300117603442600d04201d45450241c05034200c3d00800e40c20345d503111030207001c00d507401c4000d010b850b0904c1c81004403000740780d2210395160a11010f440420328591011604100201400e800b014980c8a0707451380c819035560685000700300300d0140030041d01500000681c0c0164a10179008111050a121200c2d508a65240703408407050b0f10290b5068003c20b044a100341c85a96504441051003244030310f45030460711940200201244080c000b254144910b511801c00100c0403103a08203119041d8440e2030f292035190924040c12410750b8944010894500014000280c210240d0980c40406003030f00225500c10201043d04400b44505a43e40751107400ca1010030a03205400a51007544a80e80034458582a12a184e80070542e40340c110b40b110701c0c03590708482101c10380343d000000980510b42688040700a50046030421800782c42519031504020402c0c0181901000f100880e2070007880c018140c1490412034902e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 692292437 1250 692291187 692291203
    0x2401091113090b1f0c0c080c130b03010b100e0f060406021f1122090b01050f0313021203091503070507021512072d0f0804020d06051008120705 63
    0x34502c0c3e42ca400d61262921065000d08034240a40e80c00c034900101400d01600d00150a441106c20000054010810300008955009400d001501c0a043c0f0300740f45e11076201a00004c843c45030559664102e0010607a210910100f90407090740301c41344203040300800e2148203002807805902a68040104200880d40000c84c1c1c1c1040100c00805c02d0342c1c00361000c0080181408544490a415001c17588850141440842500d10f0320a0020350f1616950b41c100b00c0e080c0c0d142c2400103408910140301c9150f9101180c0001c55010301e040701144640b820070350000740c03800680100000298001b150003200703803d040712401c012220040c07400e070461910580044c40740c424583c1c002c0c05130b904058100748007696003050f140740500d0f003525031490b80b40c494001400d0a0365024101d00c1100a080314040007103000c0b0714040200360795564ac8140c91805801640c41b240042c0040381c0010104140303102041c4a4840d6a000b607504c0f040d1009801d00d070040482c030703110040725080c0c000741c000c0045c000010b500042c080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 692293687 1250 692292437 692292449
    0x4022506020f0324010906080f15120d02010b27040c05060f0702040507230a0c0227151e060903010f0c090501050c0c010c1407090b0a090507080c0306032401091113 72
    0x4242ca40d9141c03c00401c80c5031075500380e40c000c81600c9403192f10a4002c103c4254420080c0c0c02004030440c100100041460074000d11041d003503000041103c0f04840c100240d0380940203d0012250039a5800415810f078003211040800c08400b00d58481107151600401d4ac210480d17107001409001c4c00a90303040c10048448101003201000030ba550030241c02036000781510340e001805001441d5000094820403402082d43c3c00c040d1140d00c0c0010301c3e54000803850110018041c003400055107900c403105010400384c0083c203502540500901300640e030240540882e81c4030022000c207686600356000b800c105116004641440410305c49110b02400004942e46030031004d00c1c180b80210510306095841c4400d6016aa840340202100032075002500c0d0404a1428000d5a0320150141d91380385c0361003254029642000010441c1000c11f210705910b40c0a9500241c0045c2134844042c03400c2c558001200d06100c3c40d246400e01d50f0b0041000d0219841100c80c400351980d41c3c140341c44c565903507001c41607030140102 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 692294937 1250 692293687 692293711
    0x11e0b0a0f0b1909140105210a090b010602010b0d110f130e061b070314090402040e0f1005010801032604030b0f0604022506020f032401090608 63
    0x210950340e48000003009004a00d41d1007880c82c2c031070804042981c8503000b181c20704001214202c60b4a4894600401214842d0114824080b8104011140d030f501141315480d01304007040f50040600d102d5012940104629100010610803500c1c01b4194410305900501c15a49400d03619401350300c41100d481500f0340c0c4001549250001440058144106646040d402a000d07003150b00825102c0e0340600c40c10120b070b10031942d10b940c80d80ca45035040c203010455080c03001424044000024099020b02c0041c1410740303105824601c00e000030608a0f00a9400040055070307032410b006500440034a0b1030b401500b07000140d01a141883c0000e045004180300040426105104841180c20000840760400c07181d8515070f0766460b9641400410b0000c140c0f03021031900041d4001c582245000c0c400c6846c80e000d844000b1402c0c441ca00c03404114100f1140701902c1d82034003003000303180c0012150f00451040580072000c1d0002d804400d0b07043d90005d011280c8c0c50500030050020b10015400c000c24692141d02c140741 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 692296187 1250 692294937 692294951
    0x718050405270f072306030403090308031e15090c1315020304090c0503070215010f06050906090a090608150f0a020d093206100308031807030b0a0c02011e 68
    0x42d0700d411a441050741d02c501585402042e00c080c15145043c44420500364521699088010410721b8817095500901098505d1400c03c0020860b4001d1769002c214078210b04410021289000002d08040b101c0d440d031a91140c294007860b1825124042c1c0000b00e0790502c40c03d00d0745280222900100300d009441c6840d529640c04c1c04560310800842c0e0186c440362200740701c0c071000d825000d02a03070816101d103000f50084517140340050b4111086281251040280316010030314000e815a03459000d103a100340c00c040300300120000345d1516000d900041009071000551a460041294248198488203000d460150814002e407540c02160b0b00f41c008066a20042c0e61b12070791414600106081c6800410040701061800801088904c02040120500f00244200d0f240b8581807529614100c90884d1001a0883d0500114070307110041c0d940103400c42903d40501040c81489071070107509030b204a4580014108020031138100b0700400c4d040d000c031030000344440551000415001c020f5140c03800e14055403495 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 692297437 1250 692296187 692296261
    0x40b0f090a12060510090203070915030609060e0403021c0f0e01050403050f070f05060403200105041e031506120201081b0c06061503091506030a06050718050405 71
    0x31284014484960b051003180518501a00500340417200041480f09031440010068281d0003168800e41d40c9554885200d401e0110303014000405000d0365041680c0e541000c00ca144d01e51003542d02924040c3d20002c5246001d00c0e000340352070308070b0240341124000900305a00c0641c1050340307200a90382d141408000c403041070004841070b0155600103080d0b44200420424405008105001a60100b13001502c00799180d45c24003e0a00c680d12000b84000c00404e5050f141031700092425030308240500d441490580e6800d0400845180d964000640c3c40700008208108072100d09040b605155030790301804140d00c1c054a1085154600c000a418403d4180c000b80b204060091420140f880c06040240c0f83c2c00081e00349030b0340c2d890445041c1d01984139040302e2040340740004207883c86070030000c00400019282c0a5100c0d61160058480da40511424083d10006401c6000d5144501490795440b061550000b4044818070602d81c4024041c5103008244900310384025135801c0004421b0800e00c904542400e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 692298687 1250 692297437 692297449
    0x906032d0a1e02010216050a03060b0d06020a020304080d170a0f09080307021e0a05120a0c0203030708180406031205090102071e0509010602010b0607030e040f06030605061005040b0f09 81
    0x50006000c2040c6507a9000d2012082a090b001d040c003c0e400c4985a042c0e98494802804c842c1c05070640c00003071800d08000041054100d51910f880c09004035218007019070b030b0340d020790f040f40d50b4900140e0404101841001c004205017018041035280c0012041810a82001030201c050314440c1100d031644042d40340304800307401815078070307078009051940c918000c48004d44400d00c01450110f0380703040709040300354101c0006000c000079030040c0251802d0883c5401420103907106501d40c80500c24446210005a40c060014211050140071070075902c5882c2c03031104002244c1a503003c2c2c4261719088042c40415528086440d6095040c18015500d058000c0103134600740b01070f4011000410380700340a1089a600788244012240c0c00e48145109903211541642618500c0c5001030308a1010711203000401d10545030001d185da000f42000902000340000d001c15904a80c00039118640c64500b4488541040402ea0514041c0d91910500b41414411003800c1803107842e07003081000c4004202000a42c1d0b8207 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 692299937 1250 692298687 692298703
    0xf05040b030a0b150f2d0a1503050106090b280504090504060b011106160804150507030603031d0d02120114040b04060b0a03030813030e0a030503090906032d 69
    0x403221590f120701e01008540300b01d026084080d4044c1d59943c038900d00078182010103000f174102400c541100d110f40c91445880d0321154002560b80424031000018801c5414282002c500c01e003540c011645605000b00a030490b04954440d501a02042000c04e82800709410507443c900d01c5c80b806509075080c0200c045030360380159000360011910705810b0004000d1039600140500c2c01c01e0b2109418215402d01c41c2d078482d00200c5100107082c1c070000e0407400344d6224103031403a402031007900306c2e244600141001504480e800c45240d008290b66620030300c00d0503040314107000b00b210a50f044030a10071494020803c6403860f594000e00520809002d5461850701b034114196402128000001524003804c01c1c1c0500c840131b880a991a52920240e1099070500031001000d485e05034441030001c0d1902c406854800c01003580980400441404000080c0d650340301e03190056014000560329042820100b150011020303064600c01c0c1c0c0907104008100f10650864040e004a1710360710002c15001c08201420715060b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 692301187 1250 692299937 692299943
    0x60b0304050a2021010b01031404150906050901091b0807092003161404050f090a0b030f0309090a05070206070c060f110d150602030d0f0b031c11070f05040b030a 71
    0xf407102c40c1803c01e00c0c1d4980c80003400700d82c0b00207103d4010700200640c205ea270070a084003400300301c00000902185a0340c0713a030020700c010450000b1b514651030301c90310308448c0181c62808881c1d440d0312209040c042c040b401c031b22098040348020380080703140010a40c0d41d18140d100e40040292142c401d050b011000d030610214039241c9030032aa680c1d140c680c40508502d0113981d4030300081403408204c0945545010240d800755070740a0120701b011a004802c001885000410381c8480030f469400d8105503460a000c0d0001c0f446400c0300a6498000540c2000480c52000b4400c060081c6444d003003080076580015482c1e0000f915040118110909060101c050007429140000090030070784e61b00207581551707000b017090084c00c513001c11004000d40e2951401b2095442000d00503070007402014440500c1d940864051403141c040010041d04240c0443c1c113242e40c010300744000c04040c1000c095040c0c1c014104500c2d0f10641d07000340465504000a502c8164881c0c041c681c01155224001c201130740301044800085a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 692302437 1250 692301187 692301199
    0x902271e0f030f030c0d030c0e1e040c05090f01180509040c0b0c07060906051603030b120708010203070e01080f1b0d020c010f180f020d03022a04060b0304050a20 71
    0x1d601200341e5642c5c0141600e03403280c0702c1c921446030351510a1003600c241d1f4205513125520000340800704542c000e0054040c3d880f0500a4183e0402d568035446200b00552040d02c03421b0b102c101000400a50050100c00341303041c08a01141902e000d0325080402050718001c8a89080f5600c1e01d04000d20540d46d144c02c01c0800c40400220350120f50300001e10002118165034a10b101542c8840c01128140907089580d500304095400c20f20000b0b01036000070324205800781184104102030507940d490300c0c000364001d240d980d500000b80200340c1e90101580d03c2c20503081c01c014100d418415111a4408401130403040d905107040d0442c0e03541c3ca003080c11071b401c49411070030540d00c0e01c801c07440355130090011062070922a46888001d10002000d9911900c4558209109800001c03840c2c00384011448a80700860031402500310901c900800031910840020341e6040810303030240060140011288190400c001121061003000005003000484da16429484030410194028064011415503e08103c90b54403807 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 692303687 1250 692302437 692302453
    0x10909140a0c0f05040e1c050903030406032003090709180210080906090f0a0303020d0b09040c081204140112151502120301030c0506030c0d060902271e0f03 69
    0xb200044109445412207606402d40d590f104000440d800a100301d8900e070040000902c500f8940301d90084110700a0408918154215000908580c055041000800d641c0e40580003c8210742002070340d0b180c200c2034014a5424000b00c40c6617100301511a1040c0140c440031911040c54208888213849a13006d004154600f0000744040c209800c00c40d0f240101d44154000101070340030000d07000040c804440c2c060042203a007070706d00324040d6000c188901600750312906044410f44802030600d20a5003d03070f2090301c40da42488178080c10500d188215082c800000e00041c000000c941181981804007420054902c0d500b0302981d4000d0f04601ca802c25243c030720103200087c4050f4a0b03298911000060b07080d10a481c03000c000032105030000b800003400c1d250034900140302c1414810021070b048481410031600f0400002200000c5c0c072a15001012000c1d00455034160100011007200503110002b81280b505103140c0c00440c2d05035030007820904101c1c24100e100d002949410350191115813014080c0c80481e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 692304937 1250 692303687 692303693
    0xc0603050901140103030917070e01090903110303070504050402070204090b15040b04060b04050d03090b04180509010203070c02040c05040305010906050f070c050a080a03020c251d010909140a 84
    0x4140032034041c40654201031842c83c8071482905828140c0c1e5040d141c000700031381007080040c041e03c0380b081804a02d2155050101c0e02d80780f0041514020301a152001c100200d0514004058021444000c180741d40b0920a00c004242c001c01a50182c61003900c0c016200d40c12800000c3c060f2110101c06000302802c181804044c043d07104001c42c0380319003078405001550b0b40d130050104442a40c894080b0382e00050105201910380703644800381d541d000b0700c0c1007a0b600e51591030051032030380301d68402a0b510301d071440040c10f10080d501030a50700c445081e00071411481c0141002c1d1040c0d500200003846030350341e0408100d102d80a00c043c2c0700615007240c000c12a9500524258004040646009402840401c0007903034140c460788045000680c0080130b0f012a24252740e600c0c82a0b00105040c0007410340034049034220190070000103d06d107103500d00c24007030344c409010410010070b07198008601442042c20004516400040024110750448030001090800b505003c03255000c40040d0044a004000c91031041c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 692306187 1250 692304937 692304941
    0x103110309060a150308070204020a05190c050d1d0f012c030105100501020a0807020a030807030302030414012d02071713081b09181e010b0a030206190c0c0603 70
    0x42202c3d841000c0240c20540402e440c5800300901c001000307a0410803000300141019005022000391904010f8107040303001d1101c070300c80403141031000001a1600c20100500c90b04010340e20302480c2604200c8180d09a800c0030390020600f54940030300601c40011741c160240d00c030301e0315298100e035001582081c58081402d1f441c240b5424001c1503109608020216140011100f410030803103805800802080d030150390b4505c0540c202210603030b417240d000c040000202d090140103120f594401d075001a901d02c0c1901c1c102100d07290800f40007030b4a80c909018150144440d40300418580c0300704441a4041c03524054a0b4040c2c4a100b0009020401c60140c103501d042855003c1c1440381c1000000c001c480c0d0311004041c0d5200c664651850340010a4040c0600c0c0b410f110000b1500088640039040b15060045641c9140209032181d03102e8290f4482801d00200310b081c03007402514502186e80408591454000440a0203460011002c2101004007001400d0155a4034542d0552000c0d004034a69135501010300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 692307437 1250 692306187 692306191
    0xc0f070602030a0e03030306010e0d080405041a030d0908070603020706060503012408030906040902070305092808120a03020a050c0114040b070c051b040b04060909030e090403021902010311030906 86
    0x3020941146159604c3c0c900801a80e12601e010303903c600106040204103d10115085010303199071501300302c0801c560f110f6002c3c2050617107898110f07200e1980da040a02d450318800211190400109040034041c0e0400410440304a8007249005601e654603418018010000b641c0401d506629280203100310400c8c00e64003100e00d6883d188510410307a55903d020344c5a00c5a20420303503116004101c00d129510701c560140c001c0d00d009207029810b0103440d102040c0e400804114682c4603a0008500c0406c032100440448090507690340500311585103007000c260a4012143d0560505402003021121580300e04c040c1d80307100740c40e0fa000f800750325140c0103900b03400c06095806458852a010014007628000c03808101e04991010040c4480c0c5528104001c2000b502c0c0480f551048d2101d4a07800b00b5a1103015000c0034115040000400507080c0ca07001d4103480722440d000d80109118020040800e40200b035404100c9070b045505c60000142c1d02c012030040500d0800c40f1404080131040c04050800010214 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 692308687 1250 692307437 692307457
    0x6040b06030d090b09040207060b041401150e06161727040506130c0909091104060602010b0319080f04031103070801020c0a1b0306092906010e01050c0f07060203 71
    0xa4010000c400b007103a81200303500400b10b000c0010860340440d13040950040c854680503203070004401440348001403d42e240700500d420301881a00052210120012501e2075001305410120504e51541012440c03a0041e07408581040c00010890710501801542c050020b44c0045540d40d41c804c0007094503a0301c10404900c1e500e45003d402842707c0c3c0c030b05085c072689010380c1c2c00800070340380d03607203d8040100600061280300041000390113000403400524060003040314450810541d00300b1202003807004a4100364000ca046a0404080343d82d2900c01040300c401c0240301d80964000d101c001d05001a580c030030001140011080040e001081c0a614122043c019400f01c058134082990350540314240e010b4190104441e800003c901c3c0d000072003041c0d85040c00c880740d01a50380c2c0d2603030f41d444031412a804401c05070380065450103801c60b20481c242e010450080c0702d0315241450704003000001c00090740041c3d400d050000000c0c03c118400b0080000351028000b05080350304203034807810000d4980d0080180c41c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 692309937 1250 692308687 692308693
    0xf0806041a060d150b0901060302120603070b1c020403120903020102010c1106070509030703060e03071a13020609062205030c120318120d0216120b010603020f0c06040b0603 76
    0x80d035107041c106114007400008010b4148507075143c80c1d888081205024a1052550310070280800740c0320800e44074001d0816403070050311800404031150342c104005004510a402c034903414440070b0001e07016070b039107a1b6540702c405102405250030741c0300078803a0750001b900000981c8170905d001d03980001c042c02a00c1c401e9000303000003081c400050b6081c3c00d00d8070512040350005000241420310820180400410007001ca42d92140d172511100d04440d80707699901d030503410001d0721009100d0031101c0100c803c030740c4028001306d0746040c10b0044a40e03022510024800d400000d03049071942c0e590416181d120071041146a10541d101e0102840d0b075005103d041e000e03001d5000d003100c6500c0c0c4019012001c880d2100518a40035507503c60250286041a4641d44604603694090136040c042042c1c40c00d402c180d400801c5100c05210588451a2281d0301c410f090b407266540500000b180c1800e40c0381102c106090150301e404801381c1e12001402401c8005480b031240808000900c43d0720340159006200a43c25 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 692311187 1250 692309937 692309963
    0x1709100e0906040b030109080d1b051908060105040e0a0f0e01090819020a0804081f020c2a060a120507110d140708040b090406050a08070605030405070f080604 70
    0xa403144466594103030340c4241107a00094007400c041c0c100000b4070b840200006051216a954074080390407076000c14a0303541d0f4801403030818030010405680810034608103541001c5c0030503c44100c094030001c80108100da450003181c4164059016500944820072800540340703406402d000003000307da4480000c00d4241170b446550302c0f0f01841800d00c000d4011000525004c2200407590490200304510800c5100f41e2040c03201045550300640007402006000d41004080d02002c0d06482c1412200000720604c10450080c2c20400051180050307032420100c48074800b0800c510300411030751a58410b82040b40020140b800c954402da1280f205c0002c0b0104010a4680b0b1000b201d50001d02e1203030301b040d940480b41c801895402072821203150300c001f1403603d10f000560398071008036070020703440b000240e0720225002d14945458044c1c030001c1d05007039444004185c43c000c0301603a02c40701882410b003440780000100d010f01100303100f014094120244003e4040b682e4188013a42c8400c01c0307800f580c4403a641c1c80 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 692312437 1250 692311187 692311219
    0x2b18030801090b011709070306020a0503090106060513150309060c030b03011406090105010c1523070804081918121707120f170c03070210050c0717071709 68
    0x3c6030b4544080c040c3d4039103210001010a4126440016164030390500c00c1010000000300d40380000d200c001c95a543d8240c803800c04c103801a0a42d0240d410800074464280047c1400c9411910340104981c0e0090144032018918081079006003200d520142400d42003100d40e4100e990550401d8840460a40007085921010719403004202d070103540c12580284a04010000c940c410b03460b148419000d5074507030900741100c00c44d00088030900d110741e0381c00841855240a420291030710050b8042c4160801c54003925290b030304c2d40310520030b811a42c0280568034a14070455840f0b0751812000003811031004059944600044000c40c0400c54200c8181f030003014a140a114020b0542c2c05403944985100c0c410b140341c038002e0380c0b07036000c82141d442000300c100345070070858440b404198000d1352041e903180d40c1da050120009040035105000250b8403428041402000101201100d402940260300c50403003090044905540e031046450103000c00202594560652000320b00400400200b200c95502c081d0140d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 692313687 1250 692312437 692312441
    0x804060b31183c0b0105010c050c1507020d05070e1b0d110c0d0f0e0a03110603060325061b0f0f0206041508060307080708032b1803080109 61
    0x2858140c240400c880e0380d0340c0069402881e0381e1032031118810102d0b602403c1400301151166001104904a0012201c181032043c0043c4950140030207103046113000000d81c840079a80c2c000404224010001d004210511076610380a4030344281e4024200480c0301020309001741d03241610702804500702004400304000c2400d0607aa041d0903046149800d0a00001002d510001c001b0072070513656082c001c20242402c0c100500410030f20382c2c116120080359142c1504000c018111025807540134944003201400807681c460101c04410728201d075056076035981c090101c0d0070913507242c40405000c19a411000c203070300c00c0322035003034203076855582c0719180c051606400c26007d41101001078003c410442d2441c01190710313a90341d10350721800642601e15103507540c410318020703a210003400d0780090a40ea084c42142c0c903003840141c1c010038221005200d2030342005009a240d1180c44000c4000c080d24268071644280b240d02c11072042c04601404004502c030341c0c0844010042589021400940000d0011656005e14 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 692314937 1250 692313687 692313701
    0xe0f060702070317131701090303050609190b060c150103110d030e010804020a0512010218030c09060d050109020a0f0302011709032703060403112802010804060b31 72
    0x1d109542c164428068484c01c9038880080c4000b000395089011501008030421203040b00c0704070000089008050500170b00b00c035005403003580b048040805014011071480402c07810303481e5130300740003811452400002d9164841c03200003103010301409022078810b00a05045034100da000342d0080382c080c81d454081045115103a8001804599455002ca082d0352044800035405403002e022592410384031000202121104c888004c1c3d1a07400207007101c6202500701109034041c07000c0c1c0040060b0340605d00001c0c03020500034a0300f4040c032080c1081d041031240c00d4000b035841c6600644104a10398544e450455004080e01081c1c0c0803c01541400004401c1c400c50107200304a11400765081c05000d44204014200f620203c0d00001e03071010f0680c440344e50034000280038910075113501010948550005003008012140c404e0191410101030101c20301110fa43e076036880d4246021034148c2e941d4645107009200750111550003ca5105c48440101c502803440c00e81021500e401000c001c4e1104201c5055803d2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 692316187 1250 692314937 692314943
    0x90c060403061107051501150918090f080301090614180106051b01110915030906040f1a04050a0204290402280c020a0f05010e0909030d0e0f0607020703 67
    0x4104030030400300791282d0001c010f04051241c03080c54010b1903100d103880d0441101700689004944401080005480c80c03c0c1080800d107400c0c0720f150f95103840781c9034000b4001d051000f800251511318172020004c24003141a51f850b8408141d0b6120f503100c100e0000107009501035030140807803209403502c9601e07294040c0981112007031503c4009a00b0080c048030103810801d01c5680720090700c8001100b4107020700600c01b810780d5000b20389455814071000c00140901d855000090840e04005101b25002c0c0440e045078015002006004103802a00c0d003030718410340d00e58411008801034000d10003003210100781e24902600031030b0103000760001c000c1e020413401d9400b43d1444507480f0034250f160b40c031f0034a5006048010050480302010580004051a0b003110b4043c00c0800244480c3c2201c0231854100c2c0c00313001503c581807080800d40e0030000042e1190020783d081600c036410003030000f1554401042180c158400080046c0702c01103921100c07955034606888590964011900003801c105c1c4000b83c600101d1350 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 692317437 1250 692316187 692316199
    0x25030318050307030e030f01020a080402090105040903090b09192d050a030209090f01050106080708090313050d0c0f1e05060f090603072303010303031505030c04020f07061112090c 79
    0x4035642c043e90741c1740038400301d203405000e400d600459409083c40500040c40c1d198940c0002858248104000414141c200611503450401e0600c0030a91142801058a48425040e07594503a02000141000e450023181d0089400c80c002c00318a042d85c00003c00241090600341e0151103454034092124005180511500403d03c200704002502c0c2101c4032607003100700c00c02502e01c1c103030348408942e0944009801c103002141d540014000c000c0c0d440350050354424894000755052022281040400c00c1c142d02c121489500d1a0040c10144003074842d8001c01400401e0304120060780d07400313800440c0745806004040f078900360703200020142031440442d00440e10300b180c03c61600005400f003000580010340110100718000590b5085090300c0070007480030f4101c1d01c0845850b58910703d0000c0a5170074241045c1c2500841ca94200819100041d5008029070f081f80d001d41c0311001800400c00501400c900906100e040140e1110803001100c010310541e0700006003500300c0e695040000d030b030303d11040c604039410803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 692318687 1250 692317437 692317447
    0x1204080c0c1e040915020408030c19050a03050304151e0b0102010e0c2707050315120705040507140706060f062d030b0618040510050d12020102250303180503 69
    0x22a26610130b0141c640705204000101e000c07882110101d81003500407825039440000d83c40d000c5242007085101e0b41612200a8086d06d4250780d500d5210b014886c001410f005c0d010010034100400e80c3c0c0d103280844910541008140c0036100300c841c141144090b90300d10645001d0341c0d50a0740d4418098000a850520001d0000403500c030b06021002c0000c0300100501072040e0805104200083c188500565199951a8580c02c124140801c0180b41103119072041d05d00e07161030040c035035020601008440e411100042e00380d45502003a07540180d0390b503c10002c0e00d8002070000030000241d0190b01075404110303c41c4409500c880081d00e001059100f400c2c0301054000c400240484c0728103601c16009041d1902085403412080030850340d07005003040306500701034605c08400c541014424954082071480101d002d052402020801a01104001505680382d01100c0a0135034000d4041b2125103640c640d01440da0151801ca0090718000354404030700082c100761100e8a07041000121003125900100654507107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 692319937 1250 692318687 692318689
    0x9050c0f0414130f02150904110921070f0b0304050f0610090905010f020a03020c01050726040609142b050906160c09020a230405151204080c0c1e 64
    0x14040800c0c0c22181c0c5555080801300685402c2030785101c122400705560345405424041005640343c002e146001c900045c060b40700c0503510710304002e00824209103020243d003289042d5500700800c1d5008606400c215240005002e803a0034000c62040d40200150b84110a21051280d05c4030307400c0e9411400c0c04498001404a01450781c04002d50611400c00056120711003c82d590982c0c1128444002280d80400c0c140d018150a00a85074800d00d0b910b0a00c103807140b5601004007611a41c0c00c5542034101d803000280800485a10007031080307400c00e19681940504000c182d0f51a40381a040009070000c4003d0607202001c1d01d0001e005080c0f1503203407207040c031404005100694004609069071030504115140c04030306484802d1000c0e2680d0718002d41d94414240000c0c0580080100e031299007155050400404003042c1c080d181650303021103074000182d0083e0003015850240300100030034130009100f40300400c0340400040820850420549103520092802c2140c041801c0008070056150300a202c203007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 692321187 1250 692319937 692319961
    0xa03090209014a0c040f0e04030e0103201803060f0403020d0e0609060c2d0c0102070e0406090203210a080c12040b100f0b040503070e04110904140109050c0f0414 71
    0x804940c4c4540c0c10b081641d200044603103003055904c00c140742d40d101e0b01480305140d40000c01402604081c00d040c40800c0f81e00c071b0442c4030700e4443e102c00d19610707030013044000c20541e298009c03c06050006048840d1401c1c0005054400002510102c01503c10345c1c0e512a81180581c4402e0200d0600a03c0c40c0d051007400e0b4203118a5511a000700c0302c0500614000c4241d580b034407a6401c418031100404000002c50038141e140ca4330300710400580c190b42c000401080300030340500116503c80d5014001042d040d44520110f440c00e0b1801c0c1c40203001440c4261020124422000a03002e07841140c1d88211094a54514402e0944250f0000035001101180020f002c5640901c54903080901102818051941c4851010038159540c00c40f007282c5000103010040c80c40e080100d000903150010001c211400c0540e111140c201a0841d018003480c03e41d400501846100718040c0103a09a00b40240801e40d82440c10544485540640511540602d00004050f040600c55038503080c200e02c04024554541c0e44002031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 692322437 1250 692321187 692321191
    0x6040905180d020c1c21120b030c0d06090c0b03060411030f0423070f0f060e0604140d0c080a031106070c030e0a03080f0d06120b0c0a03090209014a 65
    0x10785042c0034500ba80009141c01c43c0f0003041e41e19241054000550820b00800c24130000c41c04a240c1d07030070204508181d980c04a07141203280d000f0bc035140c101441030b14002000e0640f680300606141c6480100140c02c3d00030000842c4105001c440401c210310741502c421000b0700054490792070345090440002c00060300c4410b010000c0e1082c5c1010710250000b490181d20f0500c045c0c01c00c405414032040308001451060ae4408050003050401e10310b0814084085050b9018078810b84640d0221400e40120684039101145950385d00414604a45510345503034036038544071501c0440020300d504021050080010a440303004845c56a910100b407104c6072021a0f0b0614000041584988502e90000010389400c0007000702e985000300a0303484940600c0190200c81107a804001d82d900307010150800549400d0321940c0c442525181552143d01c0003408070000c00c121640207400506440002c0b601800851130100c404401d400111104036140050403040c40e41e100c0000c120700c0c0000c034061400c031100c40400e0303 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 692323687 1250 692322437 692322469
    0x1020708030f040c0332060402100c151a010f0e22180c15080c04060503070c020d0c0504061710021b0109030f080a020a21060506040905180d020c 64
    0x140513a5180d803500a8401803001c041400c007006550400b08038080407400040c10710100b0701400c403516298010814199890b0740001c10070601d035110358108442c854000040b841088030412503c44070034080b00c154541901514003040e562011300080500c151003035006840e01034003443c2c45011807030300e6901d072034240d4068840d140d880d180b10443e21029980107001060280d4840fa80395450821a50304002014903074508002e070344010014104031100444045540364075250750760307680b41f0404507122800b1040c000e50080409070840c3c24000440308400a45400703ca040000c1c070b944000e0151500e1071100d5040803a00b03e40070030402c5160750b40c00341241c2d45100c09004201d5100700342c49800c4490503641100070407030401c8800b40040d07101128542c440e402e0b800031440c05d0403112014040e6020300c540d03900358261207001114401d0082d00840d0080c08054104c5440302d484103901d6014000450304c50301214207110301e0309003406000441049592440d0064000800440f0500c039172182c2c07a140301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 692324937 1250 692323687 692323703
    0x6071e02042d020f0706180b060303122706040c06020c030d020a0f0201022d0d1418150a021e0d08150f0d12082d100b040f080f01020708030f04 63
    0x1540120348280038071047e06004a001c02c2c002e80031881d00035402d41e4042c0c0070f20b0299000340000c0d4042c05003201c0503908041102c25142d01c480310284840091411082001310340d004801c284000c0042142a140903900309400f070f07810000000041c960350741015076070900140e100a0040340810035060045405900604c1a61003814211402a041003001003210030390380b44100819210f100184220f146000c090b00e0520080805510000030301c2c0a0703442c0c20120303403100103280b02603984c60a194559014100d40419141e650803400a922810661029600348030b82c00d003890503094011403101c9111002d512402040c0e16160760700c0c440c081c50094915004150001c0fa254181d6840d641079100301d229240501a9071508403008040d0354002c0d02d0001c5048002d00c14991000304803100c120315181c1070084594565070100c8000c8803042d90b0748201004180002c01141a0700e1440d04101641c00d080101c81003205c04444a900301d01c0b60303502c0500300c04014004220328280741440e00c0d070024015104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 692326187 1250 692324937 692324947
    0x105062d06030108030a080702061302041802030d0e1e1f020c190510140f07020102010906050405150c0c06010512100608010203011806050a06030b06071e02042d020f 73
    0x100d2402e074400c1e08030303104a41c00810b04910080d4004182ca91003182403000e0951810082034080a285c80c46600a100e241c5a103070104034503040707000d00003070660001c00310b50802c20000c1c0003624803900d55190500a0318447c44200c503032007070305111140340e010103002c890b4401c03801d541d5108a144450448421409800d01790310326a5201010b140045c40b05440c801c1d015442c0c00100700b20704101e0b8202c20305000008607100c110144803820b03501c10712059072419903030341601c0c80101d00600c090700d40200185d01d0801031100740880028040d0700b002c3c12030300388005512002c00d200d05074041d004015903035500000043c41755061542c00402c101400404444c0490540d0700424141e0f041c0340c000100b5698040010072581c150108130f05800b49104808001d614240030100300480040e000b400145038840746500096100c81c011502031540000100c09a41885000d4410310205585c09078171850500403003158141c1d0340c4c40201441c134244444900d10030b80741c03148140a0340080f0b94120f40681d052113 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 692327437 1250 692326187 692326189
    0x150705071a04210f1212050a02030f0c1204022709060f01050a0513020f070b0109020711010e0f0d1b0b030105030d1b110a05061c0e0105062d 62
    0x41a0003420740806a5103841c10704603591501e82c4490604502e142c0400c5500e0301103440f6881c200710064010858403c03003505004c0c156825180304c0221004a89400c04000d41090554050b60080d01d0f045a040c42e20740328220200b03401e01407001c4014a0025003c003041c0141f0309000c0303040895562881d500407a40d0b0041c40618031040489011030150098010403c541c0e1040c4c84003070151500300c528480080c1424007083c2405429058044203540c001aa6501880d00300107903100e9a0307002d0f000600641c0c4407100400a074216850440c0e445000e512250047d40c09003a0300b40e9001d6015142040500c000ca0030008205a04c00003981c0006a1801403c81c0215110904000e00f13140020541d42c0e51403d4141850b0100c03981d1070300700300b150401204c1c8944480c425900341003034010707004810841d220030003e0821500e643c8010307802070000a602c0d0f400d402c1034890078807a11400408005c4054404011400c0e80d01c100c4860750301c400300c90185120703032a4044d914051a086014a42d0300d40d10410 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 692328687 1250 692327437 692327459
    0x913030309060906021b120d0209040b030109080409050f0105061204060912170901021206120304090c0806040b0901270f050c04080706020d0c12170f0a0b0f15070507 73
    0x30074181c130656000180181484500d454051515403a01c0042110841c00d002d01c0815020b686881190320380c0008260220380c0d2103802088440100134003c0214070001d207410541036009114400d0420304246c001407039021004c0c2694100d0387c02408846c5885010700b0095503030034000b802111441c0d541d8030540c1c04207418800d5942102034030384801c00460640e02c0b90200c3d07d000240401c07210382c010441c000000700c600b5003184d005401920450990f000300f4621500b140181c1c4c10001c0b20300e10340451102c800e0741c04010345025000643c0c007000542c0d01c4030148440000b00b40140c800d581004940d90885100030700b02c40704c0c2c04003910030004200c0b86484a05e002d54500f60341b03121010402003801e020501e024032615000308135074001803000c48803400c4040d01c0b90812030409046444c841e100d4004090043c00905496026452151041c0c0750055080c01c44810903112140785a03e00b10030f41f80582454422a201c0300e00084c185800d00c5140801440c442d400b00707804503040d000310b400c00a003a0b2100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 692329937 1250 692328687 692328701
    0x80703140408030a0f02160209090f01020f090406061106060f0f0a0b03040210091a0706060b130801060501030c0e0402030c04080a0f0b0709291312061406091303030906 74
    0x15081d201e80e24148181e10606482511034082c03102e610400c0074003d81111f86407245441541511201c4641d51980702c407030b08200800c291241c1317035400068003426201c00c1100920101c4001c640c01c000468542004540078a40162401d8082c2c4c030030800304ac4249400021681d14102c003d00c11000321000390045013291456034000d8031a90004801d02c021860301d900300345081d00300d602d80b40340c40500d094a4607072a0714400702d01003c0a100021194240406604001c0180840035001030751200c4200d81008100114824110103518012021500c0e6200b80507842c1600700b2640c83c002240d250f601008001c5d40040c0c011020000c08101c002505002481342d24507050040750411946a03c500701031589244c018089010420001c405000d080a604100d07403114442a82541e001c1c0080c1c030200a0520400f09201d0070014511000540907070480c40740701c4400d1103800d040c0010524140c2034074001c0000e072030250b40070f074031400000e440702c049082e1044c842d03010b40b401058000e600d8445c0d40459200c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 692331187 1250 692329937 692329943
    0xa0b0a110d060503120f0d020a05090d0f02190b0a1808011e0e070f1e05041506180e0601110a061d1506010f0f3f0510060807031404 58
    0x22120300f0802442d05100300f2203c00311000215240031044103103038065208244180c0501c580c041030700c2d00d8040c1b00e1006d0f203c4070b10000c0c04c28102481c3ca0b052038104407145440882c8182c1412041c0740310351130380030140c1d001c0b15262510682840d071403481c1903480c04186000301e442440c02402c001a86d08090140e8007040f00340342810208c840c3d40720803a03c2500d070842030302d00c410360046c4020005666007841d600201c03240d50210400e02484940440554005c82d4002507101e4140360351141b000094802d40000c40d40151980303e0f1410a6894100e21180c840c800d031381d001d00b845070005079030b94021140819103c6000054480040180d0780f000c00b103940c40380c4810704210183c14910040c800c00c00807005000b07202c010203d05868010b0008200c075000c1144202008a036140600c245400380c9044049510032a030000241040541038440a0410a04001021590103640551540d407481224040c5200761594103800e4108542075410082c050f00e2801010307903e03000074240034079452030b03179024901c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 692332437 1250 692331187 692331191
    0x306100806011502150a14040302030c010b09010e0c09010504170c0a0602150a0f060e01140301061a040626100306151215060b120708011203020a0b0a110d 68
    0x10401003500c1c904481600004401c0000d845959405074000600490001e0380280c90411582d034107110030060034000714140c202d244c10340305000c00c268012024002c3c040c001d80007000785070150010030000810a1082445504101c40404d520160800041002e00e9042c105030349060f940e2200c03004c4141982c15014515007110500000a240400400c0c1c001c2c90746100501c0b40002c003407055694000c0241118101543e95824401280e0703030358110000509d40b80c2d14100c410741c0c1d0341303036420610f1006400007446946800404240d0b14003c1ca1042c4100e02c00284103810f01d8200b1078180c07000754840030702c3c0c00c03016080300310040598104a4203520030003050f501127400300d286150003c145e45051100516602c11498244009482190180c1c6019040300318060001285800070006140035000300401c04030006609000c84424045580039482039510400c0c40c3c0c0e40c80c59006090007900740c1c010016000b009403013010850f0452007a42101c2403002c006101c170314400208410b980300d141c82e281195 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 692333687 1250 692332437 692332439
    0xd02030322080d1d010e0f0406030b01050a09050405030f070312091a0109020406050906090d080406200319050c07080607020f060108060705160812040c052805041a030610 75
    0x259040c000c0505000343d42c20480c040b003450310b1842c41d5019186850351304010250f81642e00360355542080d26503504029104000316526403c01845405003405040d0158401c0310b00024040c0300c5118030b0b84115001800f9504003240103020800a030309c00d001c00e6080101e0090015015407817846620320041c4510110340200940300203c0342a01016440007900301d1043c007040121540000450b0b904020895003107a4444204001500340c4505810141081c80c0100e00400c0a50700b10690f4001c81c0ca080b00480c030006001221550340c0d200361840d100c909903006017141502401140a400804840020b4812082c0c59500107490b2000850f081d900590108002d50010b9105020140c05002e41c08054280d6242030440074000d84039201524908107103000e1254280203150b03064808802c00c0b08451016401d103801d01004400240c02003900c50b0804444a001c01601d102d5018604001010341e00329151504003080300030001442c0d61008140d0982600605540600580d441410000c05102c585 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 692334937 1250 692333687 692333699
    0x80f070621140a0b09090c010e131d0a031d0a06051b1c090f030b0f1f060914040c0e040e12030c0a08010812040b030714070f032c0d02030322 62
    0x403014044202c03941259111003641d03640140300520484054616090f41d0280f4643c1c0c000072f1101c001c0102c41400740390300c1c180000d000405c0c1181c0180c0030307075100c01d01000ba0781d200c4840e000319183c80a90242c0101c0c810482d06000c0c502500c408107451498191400310010920300708044090034482c1203e400c030038442000e030809180d00107030029415440c806400c66440092044000d01040340b604001400150301040c0d001007550540040c4000c50100e6030b44003005000042240101003007910b00c0c440c2020306007031503c00e00c800181107640310002d03400c0141c1031000816410803e54010300400301c881c040d00305008020360141e0389401689030f0300d135001c0e0402490804180c1103120640c120011400da1881d826040e01c05481e115285159682c5422809070744d400b4081229040c004008146581441f012065020950340039480700e1003c42ca07075114901c04c04601110541042e558103481e00440e080c6149640f11443c800342c1200d26241c05080040318101a0300010b114508603c40d0910207 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 692336187 1250 692334937 692334949
    0xa02030a080c0424110706050f0711211e1011040b0f0903070501020c15090a032f06040602070603020d11031602100902060403031d0402040906080f070621140a0b 71
    0x8008601d0141540c1407c0040040552061700b14214940d0404a1000180440b8400c1260444401090b0f40155164206410f41e2100d000c031810405000b00d81d00e50819a0f484940590600307680c2024212401d1080780100060000d12288081c0100c2400003151010742c0000600b020106000d10a88607065078003014a4411170b500001d046400a0351450410b480341c0b4010700048030080e10403515a021000400e08401c250760001e00000c0500c0c01c14500a40ea4442d01c81d1000c0e030440500703603400764800a010052140740302c0c000050384010000c02540303110703501400300384000d50004604481c905000500903042910075000d10342c004114003490340d4040050400e02c010650301840300e0003c03500001c089014610025050201071004420b90714031180085075000402802152103680f40d45018005001501800c1220b1244400521006100254240442d0299500c80010104170a04000d05085090102180a4070380030500340d005000300e02031f40714420000c00060051310500c05c0200f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 692337437 1250 692336187 692336207
    0x1701080106031b030f021201021306170a09020a05060c010e060103120f020106050105030f1305250506040b07170c0a0302010b1302090f041a040e0615060a02030a080c0424 75
    0x40050003d600b00001104a100d581d030f05901210241c011964154209000e0b1040b074240c20400b50440a000c590560000ca142000c000b01003844420307a03a80346400303030890318003a070040d6106440140c2040189440001030103921143c00c00481d644c001c3c8036400f49030a82c01e80084a000c0d940d80c48801d1000d601c111081c1982d0b0280c8001e100385858400041c01510003d00410446c900202c00128210884401c0424040d030040803100d041c0e59005130080b8170481060791100f0b81001d29000036244ca044030a03a800d070740c0301510003454030400741e442c1c07a07101c04c5e02c0e009824080d100b4400084031307070001e020452245021b5000450404180400c00c00c05149410751940c00a2041c400040719845401d56040e40200580d80002c25407000d4030440410740c05031503001c0d441030400d41603901e03d620202d402801078455440b081428950f040800c5894007501500100581c010b01041c0d449510840102d60480500b840c0035280035241c002050070b5080712004c010b04031020b00321460546a00a54160f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 692338687 1250 692337437 692337473
    0x240402010f050307091802040521122a0c0d0804090b06210a1509140a14070810030f030531031b0906060207090b0a1d07170108010603 59
    0x2c2d01c1c600e00800064258807250017644c481e913103544404070b42000300e54100c401610000b0f0039000b00c0c4000c40c81c0803c0901c0646814121805001d4504c0443c0c00b202c010b4030703010340c01070401d0002c150b1149281c61100c0e03140281c0080510621201050a880b00c01e0b110080e07900030640300355140d0401514400780d03284403807034a0184d24200f08545482400304a800500049107000b02d106488000d02c032405003014100b1080d071003141d1280041c2c0707000241d000c0c0c0100032100c8869196560f8001005044486050b203002c000d0f0b49801c00120924070a416543d4040e18481e00061210f032aa1100341224001d00d204038049440001c15901046a0105091941080c002460180503c194580390085528803009016000031968161400d600c0d540c1000030704100c00b0108102c9544e0103001399102410311617551907610b004100d40030b5080c008068420f0f10410356410516004ca10703260702040c01d00030104401c0007081059401000c4241420500a100c0c100020450700c0c11800c294070f164109840d10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 692339937 1250 692338687 692338697
    0x7170901090c1d160804060e0c040203130309120201080408070c08011506030b0906061c06051320030c0a0807030f050106230c1009020d0804030606031e05060f0702240402010f 77
    0xd00701071517204008551041e030216020a4004054030283e04d050040c800d001d0303100d40080100400d22401c611640c034000d0099a0302c00340c240d0f8508000302409500c410103800900341341e00090101d010003000746085031103030955170368203a076800410382110380d504105462180340d913204100944c0d15001e681d20403107044500b980340d410004006441480360030000080c10034040c1041c001d1003c0c0e0707400f8070018003029022204113040e10403484d005040944a0341508001d480e860780a8048803020382c0c0c441c0032086252898041880c006030340307001004111030100b41d00d41001503a5254107000300c2e402803a003138032003074204414844410714480248003210245907050105078205200000c3c1c0b00da03000da2406000039020b00314008201290701046019007030040001d00041088540d5103c80212070242120791080f82c41b12044c507003c046113540c081c0c0958002004502010071400a0540010b124011104a401c04e05243c206181c10410701d000c66074000401c000540d42c00c4440d03090210030070720f41 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 692341187 1250 692339937 692339971
    0xa06050f0f0913080d050f100f030318120501061422090c050d030906021e0a0219050d0b0a140f15060f0f030405010b0907170901090c1d 60
    0x418030114500e10000e2058050b44041640819050380c1800e00c2a007014100759030340802481400901815514242181041800035081030403100c500400d44504c20800d500c0742d444d40d00c0440d540c0c013080c5180e40005080100c00100109810301140c1c8042c40740b000814894500b1035041c007110a0035502500a859807140801404142c4e0b2034004049504035001507240510308140440d0520750b08425004441003407404281904407a19604445540e800c640401b0305210100850030300501c050101c0f03a0044c08100c005280030740d0000720404114062a600607520360029144400c201c00aa030b504a8130300070320042032034078012805481800600390350310781403c11540113000d40062039001403c8140c03032045c100e903603450212203000a511251300e4681d503101c108006150700a40b822a0b00390b01e40101801c45003007044090b40b00c0c020980360a01c4e68007060020000b45907000345113041c1c41d507a42810300700003003c4844860207490484035090980004ca103003407441c450003809404002140c84c00d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 692342437 1250 692341187 692341189
    0x50d050d0905040b130504080c012310030f11042409110702101115070f02060603011103070c0f06180b0112050c0d02011806021c03051501050c0703080f030a06050f 72
    0xc642d041c08001260006800c0d542d50401c11822700030b2001c000c200b5401e1441300402d0803100a40d0f07140e035145003405c1e0929030b202c1c1c2038030000b101c0c1d4503c00100b801c081200c401c1c02003180ea054110041201502c04520314684070110300c001581d442c0101c078810518081031041522500c540b90756895110700303052400d0380d181c0000c0d040076006031102c0301700280310b02000c1100400380318070b541100c0902a10306d1203080807103003d488160091825001403080c2c10000e0840d14050080044444581403560b20b181c0310340c0000ca1708100d01a105943c04400d103807201000506500c500c8210444c09104a0328640a61416880c0d480d81030f44101190000b07800d80c000461004511480a9201242d60070000c980900c01a02e07452007480042c41214844c600009001d500490101540701410b1070340c804079800400d041d01201d07016964070800080b180401c41d40365000340000c0c000210030f042118081640c82c0c0d07511405502000045c140b451003c0180703c01c1d20030720702900e4007511003155102c00840f10300c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 692343687 1250 692342437 692342449
    0xf060c0515040f1b06030b040207030816020f03070507052404180f0f0c021903020604020f04020c100b041104030816060e0a050c1207120615050d050d0905040b 70
    0x100c00d4900080c1c00c0c046401c000000c0b04103002c0ca0780c0f14100004001109080f0302515446200309070200b805d09429030714500c0d0910850326a03d9164441a000d9150a00650002d00d061141502035110390202c2103201e0901300003900b4078030300c1a8001c00110f401c0c030040c40700d07203100b1009c01d00301d113203840c2101c4882c000a0419a004c3d1824090320400200c101c01da21000342980621041c08549000b81103042c2c3e00254000c140b5a1455801300c580078000d00b5569070200d400e403030300540141c21a001043c01490a6078122078036000007800907042c80140403803241840f5280141201c0e440d03503454000c0d020706043c092180561294505141402d140d0b44400c09144110a840c0b003d80c424001a071040040d260f0044950006110840d442000c0510b0210f903140344100c080c074810b440305c0003240280360000818100741c822201307251056601c640d4900024083c000e44800d4800c270703440b501241d180c48000701681400d000d4070080510006084010f44100c040741c000a018909003540c0c0c0410751609 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 692344937 1250 692343687 692343703
    0x1e0a140f030301170705040204030503030403020d090f06030b06070503030108062505030106030c0908030c0a060b04050103120f030e0a11040f060b0f09150403060e0d02060f19240f060c05 82
    0x20301d4142c01d14404c0e01c0c801824840950007595015101183c08401c2c03003000006188031754440d4088441e0305030024030564000810f131159413605414141d044c06450321075041541c0e4a00060051030900c15156246c50658001760082c004070340c0030908118085042c0186801d00c00540250340c9041051041e0040651005000d0803060546603010742d0b483d18401c6c1e8580c0014000c20003965150508005020344915035000103660150900b02e280034281b801d4862a0f040780d600c0202c82004240344041070314070703095001148040c035598469084104000b8000181028802c04007015444482000c01040b1048028074019061031300c08103104210a04084440f014012a580303a01e540c3d000300003c00d5115090700890b110a000304000003003080940103100b05000c29400c1c0c1c0c440c0781681c0c000b01d90b50401110f400c80e5884120000c42c4e0b41e200600300c003580f8581d80c0340012803500710040e440098a0041c1d01015246506d04800304030701c80da8000c0103c090100c03490800d5604c001078507015520000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 692346187 1250 692344937 692344949
    0xa020c0607081f141e0a0515160c051810170102040f080a031b0b040201030908070206030405060f0a061d09010b10030603060c0503040818031e0a140f030301 69
    0xc52404159002c00750054006001c1803210108043c0d51100000214030600c045202e000711040c1c8504078141c40b4100320140c1503000544071900b01c034074220030040301042c144c6100900c400304010401540c00c09800d50130450b0300842c0c0e2282d040e0310740000e104280300c000401d4140500041c00f40440801013190302d10480380080202082040303611040c600912541e4003083d0700112010001444110119581d214980242c6415001101c00540b242051841440041200c0b8900000400640c000ea0200c0302e0a13010710180380c28085254086a160f80c03041d101503d495010404011000b04c1034490a50b214a54500521182d0324041907022000204140c0c040a0520380300001c2540c4800d43c00055481c00003800610018501c00c0058010b1545000584100d803e00d51410101070080f42264022607002d00403520b095400303a90000c080302183c030010340c50b000306403460300c0341d01d550b80c0098219049680501442c484a1400c1c1c01454076807480c1403075540004c03561820891b404400e490440b40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 692347437 1250 692346187 692346197
    0x2701050922080c010212011403370c06021f18020105070212390f0d03090f061805151b01090206120106081b0a0c06060302040207080a080a020c0607 65
    0x751622071014003e031145401e196101042e03106415030a004024121560100190014846101815283d48a081500340b0240003414003014481e0001520b05203800040403401520041e0380e03510308003112079480200181e100c40807080d000ba00c1120540e409183c50041040380d00d00108680d8105c1819950280c18010701080380402c2d515802d40003c1202e0395030099031200400c8182d400602102c2c01d2036140c000d141065a2080044500d08d070801c6240c004001074850083d40040040300b01e0b0000c0700710108000701d00c1c000382c1d00b0124180400a041c2c580c03501442220415080002c07004958080c41c81021104041031144000c18121000352600c13a50030030132108801c0340e0a0140ca881c0000941003c800640d0700260f0250032981416a00303242e44942264403400740040f47e80541c41400c00e0700c2d845c100a0300a8640c01540344d680c0c1584a0400811075613940d400040480e04070f449c003035074060000218410200d071301c10141640080c040404501303142140d2091607403800c0042103502444 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 692348687 1250 692347437 692347501
    0x1e060806181b040504111b01140c0d0f0e0f0c010518060f070804060c1103061905220c150c0b040605060d050607030c1b02280527010509 60
    0x32507071011030300a80710290090104050090041d00c41c1d41c40810380f0510f14106007980524480d040c027842c504044198140d5003141c03941304000200f580146000103000d42d8801103208031610b14050502a403080801806003025108206820810301c03400c0711381001003c0100803130f00495841e019404c2e00081d00d40988504501101114503c14450b0240c200e000100b000248698049051181540301e5200c0042c0c0001c0031081c140d075400184c1d080718840c510441c0d1540500071560055504c04982100c140d9158847d4200d0202104041d0f81038070f0030780414070240545480000c40081c29600c1e4504950b0114164a0b890031005000c0d100800300d540302d0340032850f10b5403466644080550030108ac0d40c1142840c2034080c0041c041421420080b42d207002c08010040140070541c1642a0041c00589030071400c5200b1080c9103040164100d03400c1052440490180c44904170140310816102e91808035081d2500c500c0c4440074147c1c86903104481c0201040180b078042900c5042e00111101c04103156 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 692349937 1250 692348687 692348731
    0x70e09010213120204060e0f07030c0216061e140a0e0d080a21060602030a05070c0807080a0501060e04021807174003181e06080618 58
    0xe4410400c500d80024003029011a03c203180460030403209200300d0b010040740d45e4807582030703890702000c0b0303103282c10100312000007581d880c0260040004e10b80c02d841134a1494980e80000a200c1455402840c0050100341c0749412656041c10b1500c16504182401120705038000019800c40c42129400010454007034a0361a060b02d4003058030160780d510146d02a1207140c13602c002441c6900340d0b003116807a008201c88011f41c045891003100c05a65160b13018605e803116020b02980c0e154807610040398841d00144000070a000e0500071038000d0a00380010781650302d8035080203825185070b9080101051940000c0c84010f83d14500703030340000407013100d02070700560b41d0400c01d6513220060070049522001450810807414081072296400e80c164400d807041e0003011420354010303030800922054054480441420120b07010300c8000b40c3c5000c2100f11003840360b44a0f502c40713034400c41d0810507444101e4403400a108003500041c40540c401d00640e0034178100f80b00307001a507405030b00c05400c0010240160f006501c407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 692351187 1250 692349937 692349941
    0xc0311090f011209050615100309020f0418050703050604020a08150703051504050c0c010c0e0f04090203100e07030209070e0907110309030712030906090e06131b02070f17070e0901 79
    0x441e40c5c020042d05d24034a0329010b90956800300c1041c480c402d66a1004408401d070180c4124a660b6401804007450a05008103100051030741003942440403200c003100e100011020000000614882c1d005040c0a042038810300103c0600b90b0810b022942141c172640c5143e00c03600c10100c0d804203040c070b4041195120314a210342c016014180c1d03141c2103410a001c000c00307d15008000c085098046008201040416000b2150000c000710300a60200c0c05054050061801c0e0f084140700038002801e5800ba41050102c050489542d000da950359030300101020000e62070325940e0385601090600b05402d0103401c4c007000074900e0900600f413209100d450f50741c803908a5130070400e0b5407001310701800f19812070340c0311a036500208100340b20032400181c082c080481c1d207602c224503150446010030510b003604d44419041088800e0203403551204a40d171294a1f4104220305440c840c4040780c56005043c1c01e5042c0703068000400640d40102d00c07103c0314030740d2030000048006030f070204554200d1a0014152a40109240 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 692352437 1250 692351187 692351201
    0x3130f0f14040f1b080403081602030412140a1a0c03040f15110705012004031205030702031e0702090601030c0c03140702030303010303121a0d060b0111070602010c0311090f0112 78
    0x2244015181e013064038240c010070440c1c05075001b80c55800d1181c0c1c480c02c103031254050000320400107800601c002c0146c1c80f28034040e03d04c1d40744617010404081003181a018030340750030700c03000f0f6484d00038050142c1c040c0c2500304540d40e00078200a00c007074074501d820349031a510544c113400d0040100420f1619020341102c154443c001c01034403001056621050f60403c6801380402280c0b1200b2004e642014520441d09002220200e03548500ba00c07240302c450030819109504020810401c0d070000704070743d240500c1182400e68884221116440d16042c0a005000890000801440c14140b0308050303044026000300e1100c3c1020b03418902078810070400001100a1300038550025003620003c0004410960800410109a08900340c10060844424901110441003d2885810200c490701100114505420800c003032181810080340000d82d0702840d41c50010540d01180c0140d6482000000065260042c040f00303128458185040400c0e81d0001001004245c1c07886047c001005209045520f090304004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 692353687 1250 692352437 692352461
    0x105090603100f0b0315130b041110110d03060e1b040b0307030902100806010f03110c0d110c04020c2e061d0702060f0106030e0f03130f0f14040f 64
    0x110002002d000140054043d00004c41e2003809260440f0243c844a200c84920860161a4840e90024107444085007007070301410543d400c01854a0344005610b500e040303025640010f40d45c0f44248203402c440c080c00c10100742a55410107040400411007410348418803500450320320b00175402d20680000d021118421640701507440c0784007204102050381c066200104060082c0c501139441610a241112940d00807100140412400d006042c41d2520039800305510b50034005206141103083d21171036140540c0d61000d0030000c0d03090b2100c04040e0a091043d500541c2c420354065040009058000da01e4802e83d01e00070303260350803001c0080c002100142624640f890346110404c607980d1500a00c80340c4241e140da20725101c58200740411002c51000030160b114140490700d0034004c0c1d080c103000710054000030f80c11a0503031150803620910702400b4001804d40a40703001d80080c0241c50600c05412245040d803002ca0000d9911004000d220340030b01e0700c8500c10404540000d07040102d4841c850003031082c44000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 692354937 1250 692353687 692353691
    0xc0c0c0a0b040f171207030918050718030312050604180605090706080f07110304051e04050601090b030f0403140f0307082a07060204030503030708041101030212010509060310 77
    0x450700301ca20000c1041c0c6102000d05030300c0544480078150203034410f180b200c41e6540f12080e01c07207036283e40002a1018038400d180c05c030042c42c1d4440d641e8480441280c0d502c1d18140d9500c092103111034106028800361102400e031a18a41e01c0c54401920140300c411180d2121911540051500d0761182c0c003140c210615460004000e03111390400d00002c140480310b45d281442001c5000c03861901a4005a00c0741c20042015440c03969003010444114108001d8042e0b10b100c180008501540c90812000c005003a030251031515001e032004000503500d024010a050000e00f030f50602c1750800742d004aaa000c80d1a054504103030700c95140884190782d10761310008982c4070105800c11021103880045008040543d9603000d641c54650711600031a408042e0318818071104581e14112800844c046d12304903015520040c1003958a03240c241c1160b004484820005c2c2c019403c100401c0398002040c034081c5820b180031030500f40041d441c044800410b00481e442601840005413650342d0400080242003004141 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 692356187 1250 692354937 692354939
    0xb0705100e030d1512080d0f0c0512011203090e100504060b03040b0f0f01060311070c060c020108090d020c040e011d06180a0203190201090f03050c0901090209090c0c0c0a 75
    0x401c60b2a90000c0c00035a4001e82440d0034540e2004001030f015041e203d501010840c044c2d416601d840071503008451140c007154441d55220f401c502d1910800900500139203885980381c0c80e0380c42402920320141c210900712030750949150040b82d4000a900241c800888802811362a109070494501038158049540281455000308842c44200003550050b44111141c035226128080741515501f8126825010390003044010051544240c01c4a91485e40e1507100901d8002c00d500ca043c8144000e40080000c1902140c01c0703400c6503401001554030000c0301d00a00f10141c601d0100a403201c51811200b4451030b160050019280d00039031019003a0803c944004c0035a040e540300b881d031540000c0740e1204245003110140c0d40d05c1440410b400502070b074024098020102d1403624005030541c2c8004c181e04002070503002044080f801300080c0c01440c000c000414a64039150100802c0c40d60580098441030300610a038020764882d00e20f4a50040003100d5545e03141d000680e1110b203010784a031659544078442c100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 692357437 1250 692356187 692356211
    0x30919030c081e0a2a05090c070507062615030f010e1020030a090203070306050a0c0c1e03110706080114040b03030417071203020d030b0a0f0b070510 66
    0x7400200880c06100c0f070b400100c49030044640b02d0305100e0016100e5003d502440104e1145c00c42003035a282441e1000c0f021942d210b2010038a0208104c80c58600301c1c00000c1c4203000d121040044000500182c034014029406058180c076000750300307184c102c6071071042002095a801d8880c03030359038074010082c00702c4580425040b005070103002c0740c0b00300049a00848690305044205c5c1d0161200002d09400309006400c01101c00741d115520003068554061341d20010000142e9051114000944c00340c140400c8e02d06080080c0000c035051807080c03406004c1402002c80016072024070106005c01080b2201c1080700150034255200000500005143d0141910228000d030704a200079042c0c80d4941c0000300c41d0440d000030300003101c2c0f0b90104103516500a11080103101c09030700c0b02098510021060fa030240d0380c0c540da400c0350111800700880241c1c2044d00103403002a85807049801c402c0049418580382d034a0000c16201e44a024018944031f03040001d650428001c0420003112048a103040c20131200295407 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 692358687 1250 692357437 692357443
    0x316063908030406240b0f0d0e031e03060a062303070309050c030109030206130812010603020a0318021003090317040b04030f0509150903010e011427030919030c08 72
    0x45044031182e29001743c110044800c201003980307481d004801400003a082c000c0c2d490198026101051007600e08202071600d1454500922032103d000d48020340e201c05950505a21707a60b02542e94915114051040140a0703440c3c0010408444081c104103ca00b901c0e054854a02003000240c0003228000005004c1e20710341c594489180180110286c0c0d500b1928201010300380c80d00c2c00405030040c2d00c90303804504d480303aaa80180107020b10548119191111031694207803904070980c4010003003640401c0000c200ba81602510410702d1503031008010b004c0841e40012100000b03084520105952810300c0400c2501900358050b44452000c851922450030323140141134160201d50880000300c2c5040800c000d01d0082060b0381c0701d0038000b08400c100d03c030143c14070203c1d604180310141c1c0c03646d00c501c01107100d26021f102d1088103080c0b0b011001e00718a480b849162000344102944005d09503201c03c9140c0500c004400c1e5041000202c806a032050045100d6510038074040c5c002a000705018580014001000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 692359937 1250 692358687 692358691
    0x30509120c040e0d0e030319080c07060f050105040f0b1e06040b12150603100317190903020f031b131d03070618241d030405031606390803 61
    0x2039034610305c011140c4001d050f101c1c0541444445012901914038074464018400741e079120408010306800d00c402911010150740c42000040826555500140f155081c07a00a00c040c502000000f84103584c20b40000c2034944030b01d14182c222650300b00e0071074402540c61400f10f80042c109101c05039115002001e002d54405403ea44d200d01c1040c1c0e050164506041c034805a0b0301c200e0000758001d90f680c0c134580301e03642031400f4002c1111810324100864607a402c0704209281ea80c1240795100d80000b81548144840b002c2c2291646210754400e542c8041e882070103510740524440140c0740c8600c3d101004080b203002e400d404542c19010f10240c410f400031600d00002802c096400b4103004e11400d030070600300701242450100054080045400810b0300d6a2001c0d1100d03082c0001904001580b41c09080004103203000710046041c503800024003000b035841c04000891007502c40311088040d192512002501c2c0c0d28040308801d0401182040440300460301401000098030404800d5440c030300e80303290040447c2e00c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 692361187 1250 692359937 692359963
    0xa0605011d012319080105070f090b1b0106052d1503010e090f07060f030608010c051903060e04060f1404170c0a0804030b010e07020a030509120c040e 66
    0x25040581c1c07a8150068102c500c0c0f1000d803020b1420b01510303c03a0710285203211540003500700280d410044422000100200007030b500018007401c00e442c008008007241d01e01c02041201a00c0306101c0345c985401100c0350813894070b5200c5421015442010301400c1c00d40d00c160740c40803d14081c0c03105500740c20341d1a44441c080010500c541e1100e201040307401040d4803140c0c094200140010301c1070821407001a40c2200d0b90204a528120710702c4d1301d8600d0107480d9000b800010f83d00141320200c65400d40200f802802c078160081c08050825800100f040c0200a0003c07507864040341e103015400e010741d0082e000340c0310104029050b880d05080510160591a9030300100c01c2c40c00d4549400500c0741e80031280543d0340405942c2c03056180d03801000254112200719100740c090040001f0001d240710300108001d502c00ca0681011b9803401d081d10091080c000e00c103100750b402401140c00000d5010301200c1302d90104469202601b42a8030880340390103d8a805144c00c5407400001219001002580d82e82c401d02c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 692362437 1250 692361187 692361209
    0x29040c200304060f02120f03040f02030105010305010b210a02010804020d08030f2707030b280b030c180f07050d0203071e030c140a0309121707110a110f030a060501 72
    0x207002282261348001c1b10f01006110300b814403024400c0c00c0d512008641250003051032346c0342e0703104c00e40011b03003101d400b03910480d0030703a5660803085180d09158001000d010340550168005081c44a0403a407214181700340241040a850005000c5603962504c0d5030030340790860b43c810b171207151101207412803000540c1d4601c2c40f0044c0c1381110345106003442c7e8501c00106072402071309846203540d54401e20402c000c2c2913484a518200e4000204241c242540d2a40850980c80031903604010740500d030500c6001c04032280141c180d034511500c0381c602142e1540d003200f80040205016600c1403c2118240500c0c0500c0803401d00010501400703070760044030207002c58030016651751041010607080c1c003103400c1a0380c0080400c40b5102c0301076a404041d409858080402c6c100410081300d103643c1c08a284489070a96000f1515408403090f540c65003022240e0300c03070400e05013607900e10700c210b071540d96035111814014941c500a42c3c0301003454440d48906401408060201c401802d410324125024200034010525164 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 692363687 1250 692362437 692362457
    0xc1701170f0d1107171005060f180a05061008041127040507081b1e06120415020403170c0f06100e0c18010c08090a030f050129040c20030406 62
    0x5ca4060100800405200e000742820035017102c0210280074010704131540104403001f400e99603168540055960061001d500b42e01d4505803011104a607000341c440e5020707200020559005581050380190000d410045c51012918440300182c0c1110201c80c4090069945981705c405c859038124215008900c076105642c00c00e41c0721080340e955005444500d1004000d800c50440b29828580410100c3c000c40c0c0c01d460301400c00010100740f0581c071255074100c942a030706c02040140070341105006441c200c040000c0d8501031035520f034040052082c145032646000009420395444008000760712003841500282d0310035241c07c04409401411921660400070344900025903003501800869411280484c03502e022902044d004450403241c504040320031300c0081100e6000c550b81d410140004500c194007204409080d460102e080d16130240710440a406903114a11860305186e014000100c01510001400803007074004a600c0c0301400d060000240c44a8190309144202000800540e80c8540354002c000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 692364937 1250 692363687 692363699
    0x4080111040b042129240d0609080f03100b03010e0106110102070209090d0306061701060c0c0b070f020103060b12010306020c0703080c03090f19091d03130503010c1701170f0d1107 79
    0x10300b2104524a1082502504a0580c0760101400e00741e52300482000801ca00300b659169160703072110102002c0144040100800324000fa1f0b0008042d00001d921142154502402000000390600614090000104040468280075410390341da5a0700140082c40b01d060035424141c498440011580000703003000300c01b0441500a6811414034a103c20304640307135a00e4060110740601003103004a1764106907210000d14801a500680211400b5044410920380341d44005021583e540e444035007486000d0200200000041c40d04604503600560056690241c1803a40c03810058190401414140086450340502c40000003900c01007070166038004210065000704542001c007100329130300c0c400e1880828880c148180d001220b110701c5103000540d4402c04404014115084017201c2d58001c4244103040009140c24000c0300411083c5050071550711485425000020405026201f604803011003d043e5a000810504049040ea1f1041c1c81c0d401c1002a4001d1400b14001d86400d01441181c00114034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 692366187 1250 692364937 692364961
    0x2406090a02090d03200c06120603160806190b090610020c0d03030e0d08010321020a08030703020a02070e072703061d010606051809070e10020304080111040b042129 72
    0x83c40b004100c18140740801c03508ca808140010aa01d8050042025100e400403d5401d248003429910000e890365182001c4946c000c0c2d802c2c080120100d03402c1070b0b03540400d81c41d06248960003070f101ba96100b04d00201d90305c05a2401481450150b0003481c540103402c00d0660680c069007614450b03c0680c1c281b282101000c841f8000280400b0306000008000c1028103a41e56000201c145c4060065411384003140e110554190000c44d8410042600094080840f903814010003000c1c0c0b046441182c1c0e207040000f03005001c9880c07111000402c5108080321a615607505030f1200096034010028044d1100c024030600184a03065845200c40d800c000c4082800e6000e001070758001f00018410b08a004404000c106004601410280074401aa04251855107804090a261075075a40040d40d60714501492282100d01c5548011001c000c180000d10003082e45d41c0445040352480303191000c2803114014807010f00000e92038002c011107160142d945002d66031280d004c958a2110310351503940d07a18103101400b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 692367437 1250 692366187 692366203
    0x30307030f05070c050301020403060209030f01050403140d11040b040609060822111504080c150f03071e0f030b09040b0115170a09052406090a02090d0320 68
    0x407507104500d140c0068440c00282c01402d0140d0042c10f0040d980d40c000c0303800c903402a0003c0e6600d6400003000030681c2010840d0702034205080c0c000300b01c00e1800361030003040d142120464010200000903090b218203000d0b001181d41d283d9440740c00ea44d51b6a246e00c40000b650043c4104d501190122500041a81c007a02d41c441c4500410300400202c1ca2203410701c6812004403407001c46264440c500350789926102e40501e55602102c51480f1a0745070706110005291100c1d0340d40052040140510304078a60304800c0c1a90302d00320512600359225160614150340c40007405110000c051010440300075050791040c05102d0442668a04102e6203071290103200000d902140d001d44444903007001009040d8843e188480c4a100c10f103081c41c500543c500c40c0d4071914400741d03024032245407904100018000c0a1000c080240050500c41414001e445a581c0d030066004100a114040c0180002c11080444d011240c1e5050300419104a090080c0b034050101241901c030f51017070541c084600343c8030000000d0f22038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 692368687 1250 692367437 692367443
    0x150f07090e100807182d090c120c0503010608031602040e190b01060f0527190803070b0f07080a0528020a09140a032004090c0305010c0806090708060d0b090a020f030307 74
    0x420302441745030780140506003140023150403940c92600014814290740c11030380b60318460404090700b689401c00b003500b5100c01d5007102000380c0003001104040800760700c0780550703698182d8010640d140c4c060f01842c2403040070b10820a6a03c003030038111041144800403241628803586520498a60510044905019602c402c110900040ca640c5089840f24034000380d000e030005141c5024003808042c03024001449902c490300c281d201003007260405c680c504001303901440b079401201c0d01e854a0040184410300c0644a011080c0d6a00c0c013103000c000e8520788010200e103d000441d10780c0c900c903d200740e0003035012040c42400560b0505003c24400c0c811041143c110310020039501c0b40c903040d501ca403810040035002001742280303810071a000c2c0351528065603610324040c440c440c0c020f6166082081c20744d03480b15040810011075504216050359010b0000d604100c0070310b00394442c0d40c2d50030081400c8410008015091203504020404000c5001912054051007510700031500b4a41f2018160b880c06101002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 692369937 1250 692368687 692368751
    0x30f07031a070c02090103081305060c0d080c070f02120307120905010e03150c090102010f090f0203060f0108071809050a050c150423150c150f07090e10080718 70
    0x4001140882d002751584821880e111a007465030341c000a51654030030385000718550003220b440b02c500c60300031020540c00f10201420a1400401d56110b440c0800394010081c452407c05c030511040241c104241c0c0c020329400720b4006607800e010b100203401c14a10f44907450000e108800d02862a00380403404a2012140080041c4035481e100c54031066600b1040401d41150f50312140c0b6480f000e00c0d03014488003e80514841d98408119005060030500010141e40150190b6801080f022000140d9041180c261101c1c0f00103840707088084001034800c4120141082c400c4549030360600c64046036a6051007000c9880c0748101e40490706001a070301980c03060702c1c401e00d00c209040d410350014106509002000170825a80300030510410412a004580300211951040001e045440c14482c4810341002d41d0b00c158070b82503d0f202a0040016403030340144400425068007052180c241c0a804101401d1864140c40100d916042c62038024104904598229400d0440703903064080300c1010740b074a802d864904 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 692371187 1250 692369937 692369939
    0xc0d0303021b030409090302071502031c0204051e0a15230408060a05090c1e10030f090f11040b090103110d210e060c0706030506030f07031a070c020901 67
    0x8103400a4022418190303402500503003403030b41108140f0080010b044402070001e80d451050070024a0704402e41c1141d650005490b28180b511034000058486411040c904994940000701d41a400390095901807a000100c44c2d015012041c90400035000c048825642c280401d03a642a0f500419000e50b00d10201003641010300700c40390742030f51034920b4107886800d91291802d5951070010707241001c01c8030034191580d51081400040f0718103000344c003840d010031101e0075018102001190054051001d4840c03040002d884c0b0036140751701030341080c01122646e41003084481e106007442c0b04000341e034070022102d14034101c0c40c61940c0e251038858000490000ba0907a00c50760308590b2001c0d840310481e805254030a0b0360101940002c0c03025000d5400d10401841150030640a10001605961202d40e42500c154814054000d226200050201c00c84840e0b2a01050303d031600c41c0800d040052008070114103002d0110044140185e0040b030341c0c882304506c1c240366260b568180080791820310450000358002c02e8440 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 692372437 1250 692371187 692371193
    0x904051003021f0e0904020a0605030a060f15080105243f070f1b020f06040b04180207030504030609021206091f050114010c080d0203010b0702120c0d 66
    0x80540d6000c4040040055040c0e181d400164524080010b5041c2e011504143d03058610380c0980c0f40c01c581c1c0e1054036250010b040039400079034821480d008040410101100081c4000b55039040030703005001e00580202c03501e0b100e500a403003040704040d00b070003c60221390002900f401c065241e03034a50b464131006215010303e9032480541e41d03805100800c06072940e6803820b4050705041200f0204000c0041020910810006c000042240e0020024400e00080c400722840c0c00e6042800484d821255220322441420b4910010302c1c0d45c00746800c4142c02480100e40469030b09481c40003401600ca440c96480302e006201400c2d8020b03481200382c01000104103000801c00501d1070b80151444500c01441242d02c40c1d0541d008516000301200e106186501030310403220055035581c45a00d01c4000b1003000c0c4110741c10191000000141c1d41d081e9810040004c0400c82400b0ba07981c1034443c0d0b00c1c071100c0d0075035a0356510340e0145076035000345005a1054030306045031040c450b0b0008049200300000303008407140e8081d42d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 692373687 1250 692372437 692372441
    0x1c02070f0603020f2203060507030b0102101503060203150306100317091302030f01050907030e0715050408030307121401080c04150f17150606070b0a0f020a03091401050c0904 77
    0x2000044c00381d40a0101003000e81e071500740c900541050011010a40c0d00d18100b000a44a028000e007040c903144c00e00d5102541d80c003141612400c020303440045018116030201845000d41e030303400501001e101009122042a40c03802d28003201d14110300311203c81d1100e002402e420762031448000d1600c56031404820001001502811a0840081c004c0005403001c0b81c0c81e000ba648115404d103c0ca049440041c04249042890281c01c0308151404002d82047e000303049075a842103001d0515440351401b400c1001e64030590468010b02035010a0707913140e0510b41c0015107914080341010a16500301103002c482c070406511070a0488824400409c00b0000040901c0300400980b1406130700e40e0070440000c0f500b00840c400e103100406000f0120040c00d042100801e007400301c0903220280c2d19080c2010321083c0e60350780d01965070f5070740c02180740300d0b0f16103600c01400c0080400b1080304104034004110b2000103038241e031000b0812400b4218107070b011007000d41558200d03041141e1140c05402e040c01000070b541040c0d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 692374937 1250 692373687 692373697
    0x5070503010f0611011805010b0a0603020c070e040204090c121202011103070c11041104170703051f15030f06050f160f051314131a04090501090c0303021c02070f060302 74
    0x2c50f00000e0170340006c903070011190014150903210b581d12805c40403494200b01c18410001e15a80ca42142441020300d0b416460324010b201e03a100000d810360125080d076035141e1014400b01d600206078124030799981c642e03804600d07056030705507030034000c400f241e580d564018099401480c44480c019480c682d101c2a056030b040001c0c840c2076601c4420f0b21440c561a4032140704d105d8202c0342ca2072170030351590b1424181c041451004124a03e442d00841420800650b00050000550b10040b901c0d405030f1a01c2c0d60f01070011704940150030b1007540b020100205011644ca80b01d900c00380203d005102c140d50314a4100400307001661350b07003012044510a08516449000801c0c0461641c1c60041c1c81c00102d1489030401c443c60750002048120341400304511490080040341c0344c083c1014040c4451190fa10340c4003c0300300c014070003a00903919480e0402c10080298014408207610004103200d640d1217040082d1307140d40002190301800d5400c01d9070700c4124000a040001c8464801c80b0519079418000118041c0d040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 692376187 1250 692374937 692374967
    0xc1e0a050d050d1a060403080f0705010204180b030a0201200f031305120a2604181a0a0f030f030e0a120b130f0209060a210605070503010f06 62
    0x6804044400200c0500c0a1104211290b541a4564642c40407500031200b030060f16800403098003403e0000c03521040155070840f9005002561500c0340b2140724030361072050035001003840d48006030202e5803220700d0b00c03014598084004100440900d080c1419640c02c408a00613000c9000c400c010001c3c01c1e400303080040095100f03405c0c1c40340940030180c05072440c0c200040540c40c42442100c148140c3c02d01074151003062001f84000c1c041812641c48803203a5a4a40c2d901000742a490b424150100f092613049030002c10001c01003009140900740303841c00404a403290b082d5880801c0f40015a41c2c40c02868090540f60b240e0880c1152a00d940e55010990354001411401d001c0610052001c80d9512000c0d80d0042404480e0798501c640c1510300402907850040000801400707a03280311002c500d00c64101403403180d058442c00c01913250350b07000481d9041d036070b84001c3c036280f1035034403103407403031100300c0204084034425107062200d5128000103845034082406051800303901124204003151242c11408602a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 692377437 1250 692376187 692376193
    0x609040519020d05090c15160201051b030306180115032408060a0e011401330c1b06020c060307170109061d0601022a1806150c1e 57
    0x141c910000800c0c0d8000845050669550b2801c02030808420302000204540441da2042100c004e01c4440956002d0040b8800409142141800031a406041290300e400308000041d00031510304100b4a6695008942090103503014400302e1101c03500b0343d41018140d90300301e610560340e40f03a070300d408400403c1249103407580a802c00c04900d8404000c1d007461030242c0341c1203001d080e03e81381c40b40c00101500c000440c0c07642e40d03a140c0744010940411008615055032440d00391441440d040d59110340b420709541654289504803210703d401141e412641d1b2000252003a008404403078030540d15030b02c1c251050722902000d82c110b402c40d21400e1030714038011076000c3c0c03040c1041a80a40c6042c02ea0004d00002d0304400403142d5580c9080c011801ca001c0001003422503500c04015520340980000d44403508848590038461408908070701d0740d0241c01222104400103071450149007003440402c8103100c1c04bd03d0a80c0600030791448084107980741030445149102c0b21004003203030030310008803988202031040504c1c1d841c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 692378687 1250 692377437 692377471
    0x3021c03060504050f070807170105060f0721020706020601050a0303260a14090a030c02240f0a0f0503040317220b04170c07030b070309080c010c021b06090405 70
    0xa03865210b1341d80070310340310b4240008070701e0035180c080c3c09400007030080424414001141398141507032030f21325415641c1c20356460782c8070410129003083c54014200d00038141f80b81501908003056416034280c00d00803146c5e007100c440c96605c54040e0b8403102c083c0911070300b29280c14824804280a1601080510881000242a2140300c150b58103c1041904c44141c8552986200c44190501828141c1c0020595018107502e114990300640943c60510000340503022a4031004080c05848181210712075415610654034205041c0400c82980711b12565400721f091004010112881030060720301c2180d0544401d00303040b41e08a0010b1020074014003100d04800801d11029401c00d000a0904242e0702c078510602c1503050a181108190480d62001d41082c5014440324001c00e2000403000100c3e50400c00004590b100e40c038045000d405d4a0402034201c1c0000600f10549000542c4900c45000507036095034407000354003424048071620b64054950041c018010a041071030158030164100d0a01c400c003a100f8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 692379937 1250 692378687 692378689
    0x30203030f060105090a06020d080f0123010207050406031a070e01080109090c05040204030305070204060b0f0f07050f06010f09050f070c080315120106030317040807120c020604150e040903021c030605 88
    0x494000c4c0c02c007c00680005060008040c1c0100426400c804280c0e45132105605041c01c10194030a04615001d003030541c60040d0711a80d009000d0701d805402d0242c4203100040e140d00345450781c032340c6507080301c1c44000130000000c5400c0d128a1031030512120507900c00b02c59034070b40240c8034047c003068201600c9500c000b100c0011a556944024001507100703848640d00c91280d03004110449826500a81c031184040200c03002e40840d14044400c3e07043c58002c081e4880c80035092486ca042645201441e0620405001065501d5036640300c2003140c03891a0203011a40e9082d40210007000c00382c0740d100120386110980c80004a1a2001c3c0da030041004101c07640400394031001506003e003014141d03042d0f956480d020b1084c1a4003000d80801202101c10031905800c0035540d500c142d110b030100107003081c1d86001103020380910407208416240d40080c07100d0f882c1c3d903c81101e0703074014401d81908400b05031442c9004401e41014001e5100c05501130300603184901e51480c1040900301411602020155250404522 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 692381187 1250 692379937 692379949
    0x120f071412041e02010905060d0b0d06050414121e0d06170d020303010e0105040203090718020301150e0904060c09030609050a050c0a0f0b0702010512071d040207030203030f06010509 80
    0x81c541000900408604050500c115101030020070402c2550881d004200075076044420364048a4003515401e648808440711a8001d0040c140340a611011610642080c07002c0d40d04200d0090303010313010307001c403801d000702c0c07619920a01d005030043c200700140a0a0710b002c0ea51400360b040e0200e180c21003407428108030203c40844003560054050b6445410450180840420080014100b0b0340029855541040303140d00790310718140310f0184034903000000101e22503014840d0600502800c424001c1c00105078500c00042e40003401030003e01e5a0440d4840401d034460102d0a40c501c402511855103500c2d1506d441e0040c040c0120700b8400e01118142c000b001038080d1150071800c90058010342445a4145411070410001140062082c2001d04040c0020f00c800c00f00b90781219001d00c9825a00c80e020b200507601d50060314122042c40054a0810511640040b0203201d90710f020141c4140105d4800c0801c41280516207001d001680184005000c00c2e41ca10401d5812041c14103102d42000e20f0000010701d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 692382437 1250 692381187 692381197
    0xb070b15060903060907170f2119090801050a090b0f0403031d1b060c070b25050c090c031603050c070b010618050d0f02220e0106031403120f0714 64
    0xf4041c0c0c451b540c00c026070300c601c03101c1042900b000406088280708603207109946001c40c0500b400440c00c10000840d10417010411541620100f034244103200c50f0070100680000801c0c403d114081d400c2200240c80c000c4280318006c4150352290501000352200354014107001d0005004074245540c3c3c012102c1c070b0407098a8900e00c100342003001004003050386200705400d4200301c0c031200d0081e4030074003900a8151000c00c0a2003550300e1240c006844004000b003a180c0084440c000e521003a60007801c440a002d404101c8040c44002980c003a0300640315800d018060348000c4507440b940101c44801989540d01c2600308940021b4031521a40c185203064450b0703003029000b03a1002010a4011507402c0c09021000d09100013881c0440e620708540202d5110794400520ba03807002486002107101d00d60200c00c051421036000e481e0304000b003060040e1004840d000700340d14081036424044441343c0300900c0c880001111382225206182c81e89036118480f02000328540035160f9020310a80d0140c68883c0c2400c640604 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 692383687 1250 692382437 692382451
    0xf06011403011a06040605130b07080d0e0a02010504170c0628140f0a051b06072010182108070f08160c020405040506070305010b070b1506090306 64
    0x1100e4020604101402c40300461103074102e1044402d24402d89039542c0c2d0580d01183c0385c40c00c4c600e43e1011080c442c2030300800c4580004800b250007140240512101802910300d000c410001000948201b803600380e903400a0780402800100d041100340096584042107000030311281049501c850a00e00005420340c1010740c0d106101a5140111107a40d10a1503840030003000c14185280b8144034104400d005101e501401164150001003402170b46202d8000c556140724400004408d442041461035294201a940d54001680c0c0840c0740946000d5851510719110b00d20000340300300030241c400a00030303040703500507000d01c00c00900004020401080848049402100040c81848190300707003c0c11700134010b007148080108039280d6828640c3c02c00e0000e40c00c800900d1469000190a0004540810b00824001e402038107290901081050008141d406088503803400c0c071aaa80b80c0c070840320b16006031140a4003004514001c901c40c03415206070440030303807005400b0a00d401028008245882c005503018 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 692384937 1250 692383687 692383709
    0xc060a0516111512070503250903050610180f09150e01110a0f0c1e062f0d090807080403030509011d0f0910030c06050a0906031404140f0601 62
    0x914591030030822000301ca11101c0046070030881c030018a5444004e00030410014000008042028420100c001e1219120880c05c5205071501c0c045004200c401c0b544000c84580c031aa202180501105075012010303140c05882c1c1b901c84401006043d005001040f44e15200207035951200404154409107143d1030044003080400c480c0b0101ca21a4216520035656280c20394040c00b04805540d4800d030080510600c1c0e203400d403041c07a61820b0484a83c40c440c500b58408204440c01002080b40c203030032980052016005401d42c0401d40035002c0785035011003a00c00c4603600104000902100242c0c0941c1c00a405600181e0405005a560a8150b4441d0300140d010a00216940071507680c8104c005c0c1c42541c0080d0071344070480900c3c0c04101a0525100454480c50038040083c00344030200c035001000755003046050207d15500d107400380107a070104d0360308030014040020109060f8000c0c01035180c1001301014940e02580c80740c03103410603155030110703e4409001e0f00581c0071262108210a80c0642080100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 692386187 1250 692384937 692384963
    0x60807050703050f041e0f12030801180e100c1403042d0f0309051306180902011715090f0c0d02030402030102070b040507061106040f0b04030210150518090c060a0516 73
    0x500e811402c9952010701048c8180c83c450340004c0e4030000031411685100c880f80c41d01c070035403048500503061204481e40c03030b4440c41501d012000003603000f1030100001900c960646202208041034944001c840180c40b01c00c110203240700d00650007a64001c0ea6640c6030048005240942d91400402000c1c1416000500401414002da150400700640100c0050f80b0400c8468a44000703801101c0c0c40002c54401c095403280504103690203801c1c0b40c45c9650340c100811100303107405800f510550800d400b90900400d80c107030019400c00507048042e0f00400d000d043e203500f00f0a2560883d0302951005004a07015502403010200258030000b9241c0500d10410181001d035084c92401000d601c5170b44d01c41c01d59988908140404604003000492030143c11034443c0450380c2c0d560605a1400000040182182d4503007801c880c100b91841c90b0b030700c3c01e03610200c40ca881c0100440002024400c0c0503600030481760000f100300d0000d443c000c002004052a181049800c00700810020140c0c0d00c100201940d519184040c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 692387437 1250 692386187 692386199
    0x180709120605181b010e031002030c030912030c070f020f120709050a182d060f051006170601030e0d0e0f150f030a09020405041a01060807050703050f041e 68
    0x4454180c001980b0028844039000780680196841e966100c141072011b21b405481c0c540d10180b10400e00034007010019980c034102172a5035a8a940222401c042c2170240f41040010024900c0840380203102e416621810402a0340b84c01307150b041d6141c1c00301c1c0d001c100800d051200d030300e50b680d22014100fa180c000c0c0c49040e1400b01048240d0308010702c01a1494a032038030722041d10b00d070210341c0054075401c8104034111882801c401800d030040c40e005003088403102d981010801c043c540101241c024004414013003625050300601300d1500f28096940840c481907028070070341d80942041c0b135000105140224020602d6050141406003c0e49904001081030806540c58200442c2d542070728081078654180d00140141c11034058043e4003406c4ca0a0480000810318a2019800925005400130410015403d0900e440e084200400b0800c804800501c030001403031034011168039200d5101d5032202858440d0542d01101e05078440f00c4405003011080c80003248003841d00c94241040140e104c040480107040c15 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 692388687 1250 692387437 692387461
    0x3051206060c030a0e060c0109080c0d180506030a0f1b1b0b0f0403050408150106030e01050103051c0c1415100819081c1b03060302180709120605 64
    0x34842070140004100408615500000315242e41e2240d14001e004071030131200280b00d40c03140040e401260b6003403230240c6061140d00030081800424640484190441000041e20840507100c0d041c0f0000c0d0b84000308202600f881c5004603071141e032841001503000301c807090a0044489240801241280c0da2101050203508079540781503200c00b042c41e0b248180030907521081843c00c010504034030501c05001040c1010b001e06d050305d000c0e000d00401d071416801080300345800001c0920403000040e080a03512042d241c0188203090507290404040c10f89030602002c0d00c08402540c0050804100520f102100030030510303818042d080c191074010b041100040940203440603800b40c0b9400090080c01e41c00c02440300005020f000c51144400c80d90082006402c00c40e0050084901620780b080046040400554690b48682149104d40c007410a4504148004030101c0303103207000c002d41062100c04000c512001416459a0044070b5280ca0a0b0040d11058010071115511508030350042c2c903042404680c61180c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 692389937 1250 692388687 692388691
    0xe04090b060103390c1703071409100e0f18090105060306071d0406090f0501030303061a03041403250204050115020a06050907120c05090c0304200f0d030512 69
    0x90fa0301200200110400c803044c2403001e004001121030141416001c203000d200100e4038281c203e0040c80551841c0810b0b0503403603000305d400c54001070724a041d09005403d4070080c0e512000380640b103142e50b0310000d0001c2d0b8103801141943c0d0303805115000c480d84150344e5842c848030600c1100741203e10b141001c1c00c2d10313820341d074000d032110744283c014400300141c165000106210901c0343d280d0a454801c004004a002001e094002c540c0250804003050b1900030310340c2008d41201c1c840d6908000c10b546e94480300d8140d1524002c40c0c10300101c00c001050104450051080e40d68141505032803902d41c128240d060300c141000c03603c002508012502c08154905032140b240140303111000110410000b500094844e4614400100907c0e50742001c03e05201003045000064100d00510701014451401c002502d40028800c4ae4420100d40b4005648240b0110071b60740180d9109000c00c20816030340d094080011500151280c00130411a5840160b69900101c1420b19009440d203658400c10740c00c800c2008100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 692391187 1250 692389937 692389961
    0x50d03020c0a06110d0c0c03171501120b040207240209060a0305091c110709020a080103030c0f060908030405060603120d0b15030109021308010e03040e070e04090b060103 75
    0x41400301c8100c4401c00700d00344260039400540041c800c0090b08441d6420b000c0d40000240303c0c1d00e880550301885030407200008203a4001d07110070011208110f200404403000325508040071340300174030340c14080d401a40104071281450202042c44800440400d04a8100c11800c0e142103100c03490001681c0348048030b9028181c00c80e081546040798a01c08103600e071007494115002c2640e2a0300080c1000030a018528201410140c00301c580c084030b09000b4806c41d204501a038582c020711400088440c41403082f00c0f40150a6110340300560310b95141642c901041c0c141c151394036100c041c0300700c000551902c82c1c000614441d00380c07141c8a00b01401c00c00d15202d8010030450080c3c0c0201c059050540c0d403041902c10443c0b0b00c1c8408100070b0b80d0800400c60070000c41010069828020002141c005030701d801070f100b038414214244000030755880216081e0384009100717200c6900b040100f408801a80c984041d80000c40341402002050700a01040c01c81e0b60544007904c0508040003800155030b4103019040d10110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 692392437 1250 692391187 692391191
    0xa06020d050708070303090219050f040203061c150e03180303070f021507150209010e09010303090302040c1e030605031002070b011214060408180a0b071106040b0a0c050d03 76
    0x22030501410302c0c82140c07406080c259021403881d040501c0303070700410240c5da4040c0064045484084082c0300c0400c49005070b91081c0c110410142c0030742040c1c800e8034442c000007004000624400d1a0b00700c0b4003501d0a0069415900d00304520f0400c00e00d40c01001c0100019000440c1c1da1910440712290250400025600c240c104204110216408003000079005804882030203025038528103440c8640706d040300c014610450700c0201c0810001c960301501d001502a210841054200000c22030141424080140415040300d01400941807542c000340b070b003080e24106102c2e0560f2500d54000c0c0903072307507918940010b5290341050003d401c0c140103400507100c2040055080080b141d6410301291014060110240201c01c456003c2c881c0502d00e20321036030b0002d0281ca070b242c10a230406a40d103074001450392040a42c00d245551282c10190b072100c04071891a1425030405a030799480d056620a500f090541c451802c1c0701c00710700d002c0140010a00c0000e0740d106d1841198030341c90311900b01080a00c100f02418 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 692393687 1250 692392437 692392453
    0x27070f15081603050a0e070807140a0e0a09020105041d07121109060c030d1e0e060601050a030c030b10021b0a030c0303180e01030c03060b090c22051305060a0602 71
    0x7801c2c1d07020096280600307040120302c655a10b01900010310708401d0520092180e000e000480d40030108614041d507002e00420802c0340c01400c1844110b00d1a8840c508481041c2400966a00244e81c864150940305140542c0b60075a9003103000b0140300000010300101c9000d0782401002900000c03c1c905e4103030000000d0052001903140c2e8082d601030740e007846014000010b880c07802c02e0801d02c00c5601070701110504100d0402c200e600301132000744c041d4a1411003483c0c0035440880c403070000703801d5101c1c5c84145d42d03640c581841e90004070007030000d80d101d05050580b103041140381035036800350344101e1900c158024001c9642c41c54040254038407543d09180603000200d81440412170392401d000136260903003440d10340c4070400000b400a0f044154460072100702108004402c100500040701c0071280100010301514903400c0030440f080c0426501e402c2010b9080003020852107a07104030008146075040c00002e160364680c041080c40540d590300b030003100c0e0390f0001c0080318580901c0200c0a0540d61000300340c50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 692394937 1250 692393687 692393701
    0xd0614010f080f061203040306050a050403020708011e0b1903060e0709181b0e0103050c0a05101d04020405030a14010501060804200d0602190912080327070f1508 71
    0x20280079001303a01441d1052154082070b1002c00c2190003d540c8010704000528120303117034000905055030110014003a05c5d10024544c641409040000a50084070740c040d1540e60350200003d1900c51002a00100368001031840d00103d031030340800440c0901804a9200410b00304503003001c0540c1c004c80c040c103140514124030035560406c2c510007242e2140080c02e82a80880c005800015a41d00c1b21003c910502c001000b004004554400060010340d07030002819190410031400484240242d8006400b80b0b03c407800590000d01d0314000c0e040007403c010318264950002ca410403206060549040740c4610440c7d4519009214141c0144820b2800e011642060b40e200b1829010100390800d4003242d0316814003c668400709800e8070702e68881d400b10741c0c911581c40043c0401800b000c0d031102192400d10300143e025108100c00c1180ca501c41d41c010705e9603442c80d002c0c0c001c25440322180c2c96002c40c41d000c2c500b5149010000c00002c0e0550081400f0410314010000091810480104040144031003d1101c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 692396187 1250 692394937 692394961
    0x1020307091412031e2b0507110c0f0406090f0b0306090c150d060b04121218030b1b070c030b1e131b090c1b03230d0614010f08 56
    0x7200350310701c0510324080f01d0b4a403508090285100050107141055000319240c0100e800300c0140d2104007106000c159208003059400c0c030300018142711aa04a4044c504880c40c0400e5210300400f0006c10010300c5980760b0700b4074030460300e0000305a042141d032848031040740d1404103e1554400d0307820000b0700400080c440441c2c141e0035010b00c040a69400850f90144a020540000c0007a204501c1084e480d42d82e02d400c061010849007000f80e640c12840d08003d5882e504ca416144c1c4d2041c55600101170851035555100040303c0001d0400309407001651050140d1206003004240300c602951250020300d00714101070845240160802c4134035407142e54150743c82241c0c0110740760300c404c005803200715011450501d40465103c4010b094007000041c1d02c0402d010819a000c4003107942c0580d00e91110105510107015495038000001d8045171200400d1425003032001c0d28007040250080c50036080c509620898020b45070030ba040b00c4015000c40700e00c43c00e00d507800b00440301c00e48040d00d400d1005042c40d0407510301e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 692397437 1250 692396187 692396197
    0x91106030a060b030c0d0c0c03081305030f0412020a0902161202030d050f150913140a0602040f0e0606031003030e010525261206040e0102030709141203 67
    0x8059100440001d065001d5030b40700500600c2090255a03a03850308580305803c40c0c0c801c40403c031000b482c0030000c00307915109110380c001f50742c0d140e200c1c0702140d1990581c1c00c2c110102040c0440e000c0c88100f203401400c0003820098030090140c403110444201e114410050795031600e0300002c22603032060220008000f176070b940e03401115800515100d50a211481e04905520802c00748140c3c69061000740020000d030601910b10070924440107584611f0b2160400c110610203584e201907810400740c0310340116003141d0018034991490400c40c0c0d441d0285a840358166003146c2d00ca442501001401000924481501076600203421181c203882c1d0301d071aa1481107912040e00001d001c00c4034001c00e03003c003039006a085818402480d2004080e10012400517403a00032456800c072082d11a5000b0a40c90f9801e003040e50f04903000389150349080c046982120324590318000c2950340c0c0503484140400f55070100388000c50040d42d00713a40f06850300d41441c040d4607104116404a80c0a44031001d0306100715040402551 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 692398687 1250 692397437 692397439
    0x6011103120705070f02090403080402090a020715050a0b120708122106041d0115080d0203031506120a0f0c050a0f050f0c2e0203011505070212060901020a0e040911 72
    0x646401c4142408844040c05100094204c80c8030802c8c8028103405c4000719124510072075002090342d0b00d01c00f05009a01074490010107014680c03580e030384554000e03000103521001a400001300c03074810400040890300d0500f0887d001e40c11000051001c90420b0207103030f181d841d00f501181e00c0c20f800c1e0b040b010300c525600c0404c1900a01c402020400740e41d12504020390001071510390090720090040c500e402010400407a004c0040e0107200001c106d4400b00b00b80c46a680113801450456641c03100c1c0d4100d00002d81d40c41a03000780200541c201c0c0c3c0200b80780041c00362049003800102c0ea00c0400040c8106da010300c0080341480410701815203026442030110400c42303100d05d401e036280c48401129000900460410151600900303110b0405044480f440a800f84920305c07511810480c11041081240300a005a041042a51829000d2140140000c101061000e451640c0d00800310b40400d0174400180d6500e00541d40024100280e079501045418102004440402503241d82d543c41e1034016400c04d80d41 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 692399937 1250 692398687 692398697
    0x308031303030b03070b1201090606170c040302030d03230c041703040b071208220f0201210b030c1e2107080303010501140a080609130606030b060111031207 69
    0x3108261003500b0200b10254054201e445144c1c807000f540e81283c0205440c8288400c482000040f048081d0081070103c4a458481035180010043c0f00080200d0040c00b504080740100400070047e01c007040501000c09040e50001b2b12544000e100d490902000b091030a0700b4102c0806000800d604403040720704640045c2a4803c0c2a40080c0c6141d0460140b07902c0b030480082d0200c3d0b83c0050241c447d007110507100b000e90314812030f40d40d580c964484080c2c0320303180040d01054805101001941d0036900c01000742c01410005001c03840c1568032600300045040802c0ca4a448020621040c1405c0210960300c030740881c0c01d81c803281811407650010762202861188280240c404410011500030100100f99a000040e5107003592a00d1030142d90340c2c030a108041c006140558a1442d1517912019640c01c1d02459450451580301d4070200403101002824200c0040c0d0000010350008446100d000000d51050760300852a283c89800034000c050307440303c00d800310303002040a14441076540b2000c950020150402d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 692401187 1250 692399937 692399971
    0x5120a1211010915090b070807020c04050601050f0c010c0e100813031e09140a03050c0409020a08030c06011509050a060507030c1a04170405010504140402070b0412110601030803 78
    0x1035a8094990b43e20042c140310046085403207004241e404c039514a5004651240c4691030702c0f201298189000c907804801a00304814240301440c0a82049801c4101450a10705001400d031001603d6440300700c2d11545a9950540340820a03000b003000603c41000300c0c0c50a00d0b4400c00a00a450110300400307407620041c407c004502054000c003010801450401c2858142544080c00a4100c0f12140105c584600c400100c0107143d25010000d18284ca5100d40908514036a075010f02014041010040f43d100802400119500008001500030b61600c10010405949824032440c03000204003d0301003000740b00202405161101c0c81008100c41152400b15940d82250904841e04111000000d0180e1506140d413484613250390768640c0502c3c000c40c44038a1380c00c00c0c0f46c1c0c00c10030751242d48541404110144020450307285a000740d0841031030701800c058070304041c550307410001c000220340885801049441e550816a0b0002e9411031000c0410001c00c400e506544078500035010003460000444541303d5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 692402437 1250 692401187 692401217
    0xf030204150b0f0703110601030c0b090f13060504050c030105031f0f050a0b01270501140c070902040323070308030c19050306310e0a0c09020405120a12 67
    0xd07400d00204521940c90392614070000d41d20319554424030042c0c00003800117100007244038002c5002c0d8100c9034032902a444841c0303032920010694000d8124240d026031542d9602d440d075200c0d400010442a00c2c1280050400d080400304130454001030800c0529000a10052100b514000743c00b019009840114118031101660b603140a0850b010300c0401f000d0a110a00646640a40162003500303401d80f0358000000200c90300300c1c500550104500482041c90608221075401030b0089030303540340e5014a21340741902d4801914500250f540c2314046035540041d0400c140308120000c0d14803400d1604455000c000b407504044e5451030341d80000b401101d80000800e41000100d4121003c002c1c0300203a0440340c2c1000d140207026a0421140180562150f00010542c090b452500b00051000d03078194045c41c00041e51031000034100310502d014244640a2100c01064803001c4d03060080c900003c0240e552402c1106000252984038503003802e41d40050303130040001d0840079a91080c2c143d0351030200030400040c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 692403687 1250 692402437 692402471
    0x4050d1412070606090b090402180903070f0507060327030f210506030d030903140f0f030c04060201061202101d1206060f030d140d0f0c0c02010206100f030204 70
    0xa650720380141001400004024041c0c0003102100d100340c2c0100015150481489841c9000305c8000354400514048118860190410580c00480b500b045900b40043c0d40d403188240c000100d01914a41c0c0440001c00c600d90b8180100d800b01c001e80004074110100000340080000340e04c5800409000b40c05031140c6280e4841e20032081c0d1205000410701411550106a40003004180e03030030341c024000e241e00024454060300860040a51599400178240a0b03a80380d000d150304116824115078a00304800303480c1400400142d07000700100b10300d8603a211315065010b421180e0f00c0e40310b600040a40390840f40940d03039018055100504504009139014003014050210b608000249940403032002103000a00b000000c2d40f0b8801c00c01030f00e1035041a5418020107a0f103002405107200066225107038140d1510b42c43c0003a0442045401c00411140f00d41a40d01c0250303110699010005080c00c41070b0015581d040103c0f507004000400c0310005a810560605124009400003a001d01c1e19900307000400744040c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 692404937 1250 692403687 692403703
    0x16020a0303050712060e0f070e0f131404050f060106020604030e100306092f030c09013b0907111b0a0801050c042c060d021210060602010f0204050d14 66
    0x180d0420032146c44865008191505940c80b00c480c004e400d00003086d1a008407900e03001420f006100301990076a0004001041a2030043c5814003078446c590800b508461102c01e50047c1e01c1000903110915011380ea01c2d01e80103059003c201150701607001d00000c0380d0000307041c6207000425100c480140ca42c0c030304150042d0016030322050b0050710300740038442000044c0c8000340d03151102074848980c500000a4400f9680015a0b40080201c17040261800070b40c0030b0721a665032500c0305020358506000c1841d070928803046400c4c04410584403510645024581100c1640e80f108850030005540104451040d139160302d101022282000e00a1380a4159038844010030001c211820090045103420b4141d02e00e80c0d001403191482030420030f08046810310321508010603040b0044140402541e070081000305c203140f0440160b03006064010036403107400043c408801607400700800031403010315254009003150034904183c02c00a105000601c65541d508240f83c0300c2580190300c0070030014842a106007400c0721 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 692406187 1250 692404937 692404967
    0x120e030c0f010f06080114070c0312020a03090b0702012307090e010f030201020d02070b07030804111e100f0804080d14090c090709060e09150d0303060e16020a03030507 74
    0x3001011040700605400103444101003940c1444016511700040c2c1c2680c422882d07002200c01600c0c0040c1542d44284034800e00e0900914000d29002041c41c01c140403644600d0740d600001c2d40720800d22060040c800c003030f00d8018200340300801410304d03d03070814062000d822a051110507103c3c804210403a2094021001030805c10424549550b556401c51a900d91580300490140c040c0f4001e1120560010801c2000c445110800524010096400302c845c0e641c0100104c07114181409015035684406842c00032400b1640c01d000c460b101c1d00ca041184802d0b14031005804c1141d80844109090307400b0f68070a8005911002e05500d400e15100080007500ca030800e0118800301141c200310309204002240000c1d107909803102141c80d260020f044400b102c607030003420046164000380e00b085040c1041c440e0761110300e024580d20510303046000911241645c880c19030000b9180c0b07500748040c00401a400340c00402d14081c2c00300003000f032a0302a4441c16000c00140903da6514006008540034002c01168049 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 692407437 1250 692406187 692406193
    0x10c0b070e0f060a0819151a04090207050309013005041505070504031202060c041403010e03040f080f0d021e07050907080a0506010f05180301150b03040506070203070201120e030c 79
    0x40f03139010003441c0000481c1e10741841d50013030200103103075582031203810f0001824400c91540705007000d045c0e040d060140b00c01d448a91204000002e84492144041d1601d1481100038568a0a8010005084070b580c40088a024068108240380e550320321006081175446004e8003040566841c00c048400d090040011440c003418041000100355000c4010025a031040842821000b4118400c82c0c1c0e854080780c00019046042100b48141e82c410f0800c00d298040c02000400c0c0040120015030841c0c1090b030054081c61071050090041084c14400300c6030290520340249020f031000c2c400203580b050354007100030b2100e4002400442112007407101300080c180140c004c460504080c0c00003400642c084400109581c41c0c180828903540c85412034601599440e074a01e41230807880801080000300d240340195241d91b0301c92412284600004160009040352071200382c0740c0c039143c01c000d800c10400034540341c2190010004c080060782c003c140060016001040041d08450501e081c910310722405c1142d80f60740c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 692408687 1250 692407437 692407447
    0xa0b0a0e07030219090602070501120f0f05090f010e0a0206090a030f120f0e030a0204050a060e04050c01020705012307030e030102070b06030f030403210203070c0b18010c0b070e0f06 80
    0x798160f001811241c001c40a50042070030148822140018903001e8140140c00c100020002c41d03211b10040c4014120143c0001043c99202c0c8519007101e403828001c0303000b5600c41c000c21010b41c0b010300000b4120301e43c0c0c200a1060303850f4085501c2e100d00070310070000c0c07103158046003044240d1110040c071805103622622281c80c2001900700102d0709504c4848020001b0400750a4040b85840740da903509003600302500604800510f9401c00c00034100087c03002c41841c0c1d466100240142c24040b240d4081d9004130090303d007900100c0002800c1111a410041c144004007500081d00c00b420368440c4041e1440d0b0016944400c42807408680d80d00844104c29859800410741e0001e2180300030003140503c4045003215203001001e56080c1c4c882c040c610000c2d180400d0003103054041d010f10020754146030007520507245000c400317039a4010b01d01030300c3d0824112440049008054400c5244080f125074400b42814103915a06982d010041c10004028104001941e649201551202c8080440caa48018200b035210 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 692409937 1250 692408687 692408701
    0x605100518091e0f010e34051e220e070e0607023006011d09070f1502010f0501140d02031002030a0b0913020604030b0709090203010e0108100b06030a0b0a0e 69
    0x9130700030b000340544001c01002280e2000f01000000c04041240ca080780021141c400c051000c80382295400710a1181c20000e1410702c40c0d10b8081c19004400c005402c1d42c54082039503c2d440c5501b01c88604c45500301d950360b0288005c602c5000342e103a1140f02e615185001d284c101300850114000c452000350042c103803d80800c403810b041d0640d1070105081c410044100da1100e00120340c2d6107800c0c86801c1c18909001c184800e42e00300307200b03941c0e4020800d00886541644da1701200b40c0e095840c0c2c0c001c507031502c0140104400c0c41d9081c0a50b11000d684124140215410150f84a5540c2c11b410800c0307100d80304400c40d500c219101402010281c0304500d808540320301d40b0348004400741000c401d082d44900c1141c00010f480b21051203a0f1501c040d0007805090810341582d42b02c0c00f03d6600a418003090001d00c035000240740d81d541c0000c6029209007030040110354901106030746010703161102407001c1030500301040d015465207010349520274200000454140c607810003107403130660755070030075540704104904020308 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 692411187 1250 692409937 692409961
    0x1801060b04140414070806060d06030203100203040309150906031a09040501060807050d170705150a2016080904020f04031128090203060f0409060605100518091e 71
    0x100e42c50a4a040c40440b000100c50744150704210340302c5d00032034100030105186062100c0900b468100d5900b000910076100c2c1c000131b10b4a60b10701400816582c002041004040d400b02d010b40007801950703451070240502d00c0c40608030340100e00039481010b6850414010780f08042510038400342c1c2c050b10003652811b00b400d0182c003900c0039028860341440343c0c0400054504054560000b00354100f041c0400c421600005a4241c1c0d1000e8001c3c0c07420b201c1c0382e48016031007030020a13040c0078404400d4000340c003004c01000d280b0301c2c51107041100c48815040c8850340500004c01d04090705a944820401d58401c44500010000d0141200142580d14042004000c2288038440200090001c80314013940402140041c900c698059001441200990b07008020300c84054014640201d40201a03000728041400420121884a072081e28001c0d2149010403960038100102030351042649086840c0c08040103500b00e0030290b02d40024042c240400006501c0c68010440d003880d00d9001c40c0c0320300b06007010b9202d001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 692412437 1250 692411187 692411219
    0xc06090c0f0f050603040818090f01050f010804051b120a0308010f080f0a0b0a060512030a0e0303090f0d0812040804060207091e092a030311030309061801060b04 71
    0x46400007030710010032801503000318002181c01c001c16442c0345503103a580e2a41d0039041080e40344030f080500c01c148003035661051440e61141c402c4c03080a9140e5850070b0304104d02d080c0002c0246050040b25418040811004a0000000c50002d060a07460b28070110116001d4030174100e6032011409442084403c040d07005540034102c502910107150080e85410003151288000b103041c00c201d60285060702e00103065182002d0317002c0c10400700003071b0342030740c940125900b504401c0d0074040c43d400001d821000c0c1a04911070b00545c900513801036041198120204084080351401e56108200141c00d800c10801c64030216540007036a205d2503a55404c0c1403405e00c4454203c1c1c019140035010300c1d0400314540445229070a100c00c00101210107101c400c1a04c00e00510080e50241e81d24140b81c055045e0341020007000e40c45241c40f41d801d1034161469820001d01c0064603541e100e04c950400c20034061b2403600042c58940000031382016280012981100d1070050105a1208195200c0440c00050003501004824 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 692413687 1250 692412437 692412449
    0x1050423060a03020c010b04151703090a0b0403201c05010b06161403070314031503070621020f090f0105070f06050f0901021306050c0304030c08031e13150c06090c 72
    0x48040c0c4020000c0106503102a01188452904062700700b00c076041e00d10801c4940302040094034507042100000c0307245e0708007030f401400059400090400802180c240da50319002005101c41c00c0c50003860740014408002d10942080c503c3c1d0001b040414002c00707500c0900390000003002c50703585007101030320152035180200c0e05540060390824039416084010007107808181e03265986020302e409196040c0300b150400703070104442c50024071007030400ea1400c00c11100034000365120f400041032200100490045054039421342e00e4014440c01c4005122801507420990301298016010100305004807903501840c50064a04942c0c0340d50007003130010f60340c4031030301408034074204c003e01c0d940b9021018280e2181c8082c1c0742c00b0380f001031010403086224401604041d00c200e002d40380380030740d00d480c0c0b0451022290404000b9400c0026402109003441400b0050030520480550800907c0f81e50090f00740f86510481c0c648031000030807414483d201d040c25418040e030040c01000f8603480303405c2001c0703a200c80d40604 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 692414937 1250 692413687 692413691
    0x1d030c100504050d1109340903050f0a1506030201050904020a0302070c09050912030c3c0309060604060b04030f02180421022e1407080a1a01050423060a03020c01 71
    0x701d1a440e000f0144103100c415a01400310714946805c400d20300345d81d407c0c2c007841e0130040f8005011001803414031160340700c1c040c117030001c00031140c1c5401d24411003480031100c00c0401d0300e0041d0400050760000103a41c0c0c0042c04031030043e1501320800064011b4828070100402d8034100d500c010484020303a0f486507000f44d81c0320044a0300b61501e0210400144002c3d41d2841d4003000070b103c0765a040f20f4402e141d0004a071250049a00c3c7c1441011015022171081c4414482082c0881001a054010000240d200504540c10b0000b54075090701000c8038400c5000241030700358014019015519a0038a1444801c21000c4003501c2e0300d460300b4803030040a140c400308041901c0b0000c18282c0540f0000c0c215005400f0b69144414202e01c0c0c0c05c007100b28100c0c001a48400e00d40b202e0000001d10103a80205104d890b481e21548900c0c54480510300881d103001c00a944030400c0c140c01070b01c180c2d078460309807001d40b420300c3da40301d0000034001d40c2002480003255006034014000580720207c154190050880c18580c007000f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 692416187 1250 692414937 692414941
    0x5011d03070c0902071709010c060e07080610050603270703150c030525030b04020d050105031002070c15110d2f120708040e15011d030c100504050d1109 67
    0x846404d0344540031024200254001c4a1001d00d040301c0c000f480b9a04050415020212865451b10156484210141080e40020b5010004440244141540320dd14803142105050901c40001c04074000540744a0b050701c0d01d0446008070706040803d00e9200c0080750308640482d50b880c94400e15002c007000200b031415050500042c00a802402400c1c06500301c0e49084001004041024000c0d185040c0c1a10806889100034030560f1114030040041901521022585604080c2030514082c10103258180d014410048640420703010041d0009880c188442c00103500b401050480303000d0b9841400f092980525203013140c40b5608480c02c070800c0c46403d804034903503403204409800001c41640004a40303030007500d0a4451b0782d0080b0020260180314140407410551a041c4404110200b00c484a1001001d828801c6040da04850b01da010b101e1600e00844801250300301080c0c0386c1764450074290085d02d2052444099501480030b807000380c01c0250001e0840d00c003904141403401c0d0380d20300b000e0145510b800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 692417437 1250 692416187 692416199
    0xc170d1b05100b01031514030606060c030403020d15050906091b010c020622090b0310020a0e090c0408100617060c070f020d0b0403030e010e072105011d03070c 70
    0x22280310194000c009010a10031a001c040c01504402031040c0c101a0303030320070f11803d070030010507000060f1142c1c007520200000300000b850318085001c2d1205106034000e01000900800000848068030381c1a55004000f860341d00c0c02e44480f50a00121000407414501000301102000401511079031124044904640e20061040454429104094009140b032030006c405401c08000034901004115103600c240c100c40242206140c0d4641c01840c213190300d4034140d500c54602001035012000c8910710441c40c06038000e001514480308940002e02805641c800101111012420fa400910145003915030407000c0754030400042c0b110380900d0625580c0c6114508652400003032481c03296000c802041d1418140d611075480384008090226403111090a030761000401e141d20541c0100d2182d01c0c0850420b450030015407c0d03800d08404501d07554824101001101c100c0b84440703807107250003810360194410a00b4041c1c003410b245040703074018515003c22100701e03900010081603124040d1266030192501c1d41 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 692418687 1250 692417437 692417477
    0x61b03190e01050d11090411030a0c0e0906010e03100216031701060219050106080316060f0c1b02060d0510030309060306050604210215130f1a070c170d 67
    0x806007600041c1c0a00940340050a60344c0246041c490618401d41031610000000301034800e4220741051740c400102c2409548000c03801001e0944919040401c20601110045101e103500201000d04014000f500f111607514140240105658034040c255603c02c8070520b85804401d68440c01c600189020300c3c01c41d24400a030070201e05036003041d805401402e02c5081070010440039440c040d00c6a540c3c3d0240090800e00420090030303c40c0f080d006140c01a41700b414081d04550800011091035414540c510035560b500c064000c03048034103980c02d04542e80c0340340003007a0031340100380c0e002040601e00014880d2450810103074400b1681319981d82000b1940301d180890036541c01e0f1003425041582800144401143da48c0c940d002182e46842c3d00d41402080e0300045d10440b40342010705141100011101c480b4070783d1084180241154605152140340380000c0e0742c0c4a60401544002c146001103464020000e84090740c800410600007100e503c0f106110301580c850010300100c10100d5195a1029034031201d41c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 692419937 1250 692418687 692418707
    0x4230303070e0f0a140307230108150a0306050c041a1210030b07080c0d020a0c0c0b090303031503210a261311040204030503071505040f11061b0319 65
    0x303041103d01310724010f4000c1e040c2c4c01110307105606002d4a08040740c0c80c410001c0c0d41741d00340108959002ca0340104c2002600001d80034290700c032840c440315400000e43d101e201034503089a0b4081c0001500c2d0317130b0f16404040079000d01d81080d0707031070740840d0015228400d00310044d040304042000e40d1070050b120842040800d013030303522005140040c08000164014022420756500615800c9003900d000c0e20030794058100d0303010220150104105881c1e000c02c3c085880e1241c00079003d40c4410381d00c0c003c10307840060365030f00004015a135022441308203006c240d1008c0c410508503001c1001d061080d00d131980c0303001035103800c1030140500041c0b0310f41400c2e4542c02103c03100e203d00906044900c8054407008a18040c8100b0707080d0550b00603031010b030168001e03102c61004000071800344c0301445c1c551820786400460002c0000b10004200d080c0018400416070240030200c0d035541c48800784a6090030840441c10501a07154542140b6524000c088542c400100007011920110004089241d072100320541d10f41c40c103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 692421187 1250 692419937 692419939
    0x1141008150c070c06021e030f0409110f12071b080703030b01020c09131a010e060d0f08070809031618020703112e0606050f0304230303070e0f 63
    0x7010205507400040600200e801c51600480340c0e140c0802500d40c0c1d094400103501c0400141e100d4183c1c5482e0030130040c03860350300609002c05036141c01da03102040b030303460700032805003c02e00d40c2e03246c680040c0c3c00b5441c022644440103442ca802c0d25000740081c00030700d103142101c501c404507074415900315a0112024005079800d0b40304108601782141c60310110300618040303074482e040d807103201c08440d03940e691104950300c6480c0682c0d00d0840c485161400b2600d1076070800c2603034980303c00d202c0107115403100d450025902003401e4a41164107a03143c02d0460040040c420060100100020003600b84103190340185850041074048071070480080e2035401d034841107440380041c0300400c4482488081c100d9001024518042c1c40c29040c0e80c031140d1100c904060401e1018003201411040305595101c1c0005d043c1c000004880c010010f0601d0510041c1140c4550005a690050700000240412100010381c540000000d0010002c1e804528007850f642d07170042d1400c001050115010030b1207443c00500e40211150 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 692422437 1250 692421187 692421193
    0x30a0909090b16050c010603060501060e010504080d080426070201030b06091e0d05030d05160807020c040c1403130c08010204051c030c02121005060a0b03161404060201141008 77
    0x380390003140c3d010903004002ca00c10000100300201d407907802406050040c500410000807154903220002e000e8140310941c0038107000003070000300700307114002c608100041e5540c04c000000307946d23906e0040d041c0524011185801828110b12a500045d6140035000d85403003a2000c210aa0405080090078065680250b5200d22071030305042910401841001c0004809802ea82c5200c11554a2504680140b4004c41540e42d8800030400012240d0607201c642c1b4140b4101a6028200003100945805900840700d000c0d585459512551754498042e03060300070b0300202c03640e459040050001c803550100c90310544203000103c0012860002c184200c070200da800500314100c091000c035128103100003461099040c0042d400d05070015031620344861400b82840c80103410f820720180210341c1156400f070503c50140e41044820b2010350640001ca07030b004000c0d031114000e906c1c280d94040703940c01041c0100c103002c03000c089400600c0c65015040700e070203006808201d010950b03481c4107000d8480300c0c43c49441c050341c1c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 692423687 1250 692422437 692422441
    0x70305071e080c04090507080706081b1201030305181c05160506091909061d090c06070605061504171203090c060d061a0d0f0903021c120e030a0909090b 67
    0x1300d081c3e03105403240391152080c0c8110381d03a201c3c0d030141030403070380d0740f022004c601d00740c0030860b800d03242191139181d100300c3e0392502d81448480c2c07541e5a00840140801010302c4800540148400028000c0c00c04600e0010100103e03522050000e410b140e01c0713034000711040c1c4511050a0701c12148081c2000a45401400603400c0c40068403c0020005146c501c01240002c0c010f004a103005e21406060003919682500b0501c01c03460441c112400040180b0a55080d0031502048055648001c01c83c0c4a03160000700106898850200188034180c22141d20080c00c80000b400254501031490308540d104000002d4034407001303841c0b072030600520040701d000520b0b8014482010407031070803501030102c0d540760610008640d034803001b24008003080305491145074003020452204140e42da0051441041541e01d060018851a980c0039642d05c22000c1000010340d07150301c030846224400ea241450804054206026441812000307940780d40c0200c10110004d980d2101c00300b4500300a004640b031155200d408000b0703507 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 692424937 1250 692423687 692423689
    0x1e050418120f0302040801020307091505390d0305070917060402040507120203010b04050a06021b0405070e190317040807090c050f0a09181802040914070305071e080c 73
    0x410392a102c00410725909102c0411540c07404d2000d14400d0100d502c809100c0d90400201528600200c400801042410031182c1c014511005182007410078072060010148800607100381070015001d065601441502807039414982e141c1c00260041e5816103c050391152184403041800070141c04502c0c0651040000c10014205680210b90240d485d240000127180303030060f8a07041e41c1c003c0c0e02918101c0070110b800d100d5854098a101c000b0031003400244400ba8400313400c1030010751000542d5115035901d46c0010f424a00440c106410342c030009111410154100400a0a03801140016620b1040d0000804c0d601c000f05001c40b400c2e98180c40040c010700e858120b40740c01500104280004201c401d1040404040b10303039000d0100c003401620b610b80001d0030f00c6410308452082c0c1d00c1504c205400c00714001188042c40d0070300801075806480108003420b003801c10442055039100d084c52a849020000000d0001c045100d070141d5284c0c120010403039408c03801280d041940c6002c0c500140d003142d0310780902 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 692426187 1250 692424937 692424947
    0x30402090a0608060108030a080703290f1302030a0b09220c1a030f090102030610030e010902120304150c020603150d061b0e040c02030301051005041e05041812 70
    0x101c41d00384100030580940b40c4100f00d0400c002030307010b00126480800c400004e81c0c1c000041503405001c40c542003041e8400d51710602e08000782c01e1110209020603903010180d0b42c55030b110708024000007a01285002d80c0250607a0025801190119140c41c0340a5000b01c0501c0c0010115000d4003000c1c4440581020217590f850a20304c49000440d4005100c01c00081e800e4100b03110f048100101d9420f003501c0c1c0c84c1c04101700320200360003004981142d10420801c089a62002d000900028041c40c0c005040701c2c4015410b40184a2200f02a40c403030b9003050595141c090000081c01030303540004030001110028503080e20305508003640294441c2c03050000038503910840140a503a884000c101541c08103281d183d846c11a401c000b110a903594000c806900c1c0160402481001020103035070812030613025100c0251240410701805100750042000682101d100b4019130f0302410448699000c6046001c150421482b050b2140c54040e0741880b41a00754030a540c0b400c00c540c00d800070407041490300540c0301150 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 692427437 1250 692426187 692426191
    0x1005070e131503140a21080603060103050303160e03121b0610030602090402161b0f0509150d0c080a11010e0306070503061201090b1b04031a180319080c0f03040209 72
    0x891700c944a0414003161403082410202030480711780f200000a1210001d0446030f00905542c02648000010030001c1c5c00001103a601c03449401d0242e0040b0b092180803a658804e11100603414840ca210880d0301a103d54000c2007540c1c0c0f0141088910152004210f466000481e40c810003550310307030020000b2a2194000704400c1500400042ca01f4124202d01c071586100440141e13421300807800125621000c80c24004050080103010f8589549002d0000c0c06500c401003003c1100a0201104035083d101e51005e440070700d50010541d145c0a072142c0f03c40c2c1d82c45c01d003124140c5d8603000c03201ea22619940551014083d000303000e005002555601c1c0320070355040d44054612038000101c0e0a4420282d0028070924200b00d124403000c40081c10f0140030030362522010103060695a078100000c100140c0c1d228103510241c007616034610603564a04400610300d105c034220f01e000c503000c000b8031000b40d000c0b1002050a000700f036880c1c04003103456584c80380089006d1000004001d413410000701e005440c280c400e0b1a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 692428687 1250 692427437 692427473
    0x8061b04120807050607180f03080702280b0d060605040501020a0f24050411060c10110d0c0f11010b030c090a021b03041401021603141005070e131503 66
    0x50318041c079030f60b181454070030121046c40004005050405981490751a4030340141a4a10a100d41740c0c116240c1c9002c078424100024441c0c01900c00c143c0400da800380100203010300d0700c0e800000e4181d440c40810802e0b4003142249007070500d8041c0c00f14090b4003034412741c2d041d6001039004201c03c41c0705965018030a01e49140540e854101c481d000405020603903011402d201991802085900300b5250001d401e007020a1414030402c0b0038045041c44003800501440c0c101080305010542c4010550700314594420680320500d43ca00f13012050607860741104e09a8441d206a0740c423402e0000030010010308907031203041510b505401c50b5034070150a10700128050b40125610100514181d41101502d9084038000f01002c0c0d190404203040103000584515034803544000e0028260400700081400f044a400b4007000b000c06500b4015001003a0b800c0003620303a0b08002ca40100000e080c280c0000c2c0c201c01480d5019407041c907081b82d0041c40070803640990130498140003400007205085a55207071450550030f10355 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 692429937 1250 692428687 692428703
    0x11042c010b0a080a020702010e0d2d020906030a051b0f0604060e1903050d0302030a09060c021b030f210d0501180506100207031218080708061b0412 65
    0x85452a1556011603000348035440c2810390301c200001c00503100b200003c10203040c0364810701c00000984d812001c180e00e9030408075805c425804451620781410b000d40b0350040c8403070612606150b00c512801c200380120600031075041d20305075103440401d603407a102048001e00395080402d04d101c1d160b8108a01c400021402401c00820030b034140c1c0403d22036045580103100090881070710004504154034880010201c11014803080c40c15030701c0c1d850340d4100640b402c000b01680000002c26075a41039211a100301c0d4000700c14804015100c0000303513601901e41c01c800301008824a00089880c2c00a011412444a4406824007030060100d6540c6482c500141d911070300c00400040160861300d100f56070190142c00c14158006c12042c0c0c43c3c1044401c000c1460340124014100080e409400041140440f0b501800b0032491310fa6600e01114000489151079880350114080440c0d030301404284203007500c403d01c00f21029a52114040000f803452220040100e9000304400e001d20300701804007000c100d00410907 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 692431187 1250 692429937 692429999
    0x16120e06031609150c030c1707120f0f080a0504020a030b0c03011809030206060f0609040c030203090d0207150509041e2316031a0a1d0a1104 62
    0x30414590080b1400c00702034031000050182c0c941c201000c0e0f8080c208104105441c20070714000989507982560025081c046660030013000c2043ca40c407544015843d131a42d1a803604441e1401c089041e0785d110000d40401c2484101c054010f10500d040c1c2e600700c80d2a42c0b070510f95207441a0410051401800603a00100600d0011011950107541da9018111030855196658586004440800480020815500c2c01d00e0f110b18003290380000e00a410042c03c59035140d1000d40880051a60300c941980716411070b003400707001203009030954080c610440d0203609590007511403080403600d604507409184800d81000d26504c078040c1c4a04040c061003400608006245110003403044444c107210940306402c05c0e19030b5210b030b404000034261075a4a02d601d01c1071b85000e0a0030b45860904c1c0c404c180310324082550328514a0a031819584241985c0900a013805030156104c1d07040101e400041003c284208100102040b03c4030f03014850407180006000d0f4050902c0d0074006102c40c2203280801224a40c01c2c0008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 692432437 1250 692431187 692431189
    0x403021c061e060605040b0406030e251e030c060f050708040320041103010b070219030303060e0f04020d020d0203010f0c0e1201020309031b030d090c091116120e 71
    0x45100500e8601c009000108140e00b442c0d841a540c880c0c00000030010144401c00104c881c15055509580041c24081a80c040f43d15007035203442140440c4200d0600d8803183d1854550f0600102c2e02a102c00341030000b540303d02a0345001006c9564440100424500b00c02002442d03c02c51304800444520307c2e140340703449201c0d00c0780341c402d81040e0001d90305002610b80709000050110b451030901d01085e1024840111504c3e04c21200e4003051241042c2131600060100c11951040417011701082c0b4a11510802526030400030010038407800f9454082101501040010011404c6244601d40c000c10500201002d642405505a94a01c0890705903403512039074140050540245030056545944019005d2610003c10001041100d569681e691040040c0300d2070390301c0401142c4640883c0050f01e805d84030440c3d50b4600d0740c070070102c00c40c5209190a042d0401c00040212107412110680014807020503004130910b1a88104030100070481615040007001032410705445000070311f0350070b00f8144445100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 692433687 1250 692432437 692432441
    0x70308030405060a0f09050607140d0509030a0f0908030702010c030e120a06051003051203040314120411041a12010b300c010203031b1612090b09060403021c06 70
    0xa40d040b50550040700800400391554824001c60340a109814030551019803181601d4440c090701c200300308184280c140841e0265201229803009540008000c0340c9031080c0004d40f29000b2010450003d0240314444030301d01d12402c2800c050f21541805985004030a90056030b50908003c0200e00f40039040ca580c00880d651051900019a40072010340800c40952030110104c4200405032103030410420000c2c40481d00c001160b0070700c40d0b03400c00c81c0c941c0d83c1c0b06e40c101070724050101c00020318021030000e0549500702c0005c0c045401944202c00030000703840540108011380c0c1c091000c00c4400440c107100c5130b07034500d0059501c95001920301c000141d91004800800c011110795040d04030300781e0103541030300c0b140084000503c0c02c0c0b07454040680314000c583d0780001d407648005009400399030944032000307500101d5001203030340c40c0104103042c08403100c00d4a4251148000240c0c00030200340d0222000545511a80c12200314060040c8102d160900f10341c02c002e0403640d032011311206a200c804034500000c8580c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 692434937 1250 692433687 692433691
    0x1014011202041205070f120807080c0106080a0311030f030f04061b02010b13050705031f05030a0b042907050c1006060e0307060e010e0120161e0807090e07030803 71
    0xb0b110018107102c41341000b61a0090607840015a50b4002000f04407a058800c1e2814101b607214440540d00c100e00e0400c407010740107174140005194130b000c600080103140003e07803480042c840e40701d15403e031804030304060301c074055020b403480c40d5001000010340107d0854989a8010702c900c030300043c2040d154003159040110410a800981e5541610074000d00e084d9480142d6030f45412014001881c08a2006142d0700000d801d01c81d00c2d07065001d41d10b41d1207068400f201c1c05040058221440c80345d45040c4902c1c54a01500c083d243d07052460104090100f00c5caa0078100114615808481a01c071144110b03030710f0348141000c001038003e0030114401201903024902c010102980c030140e01c0700d0640100341c10210f80e80d0246040c0301c44485d1200c00369820034500707a024102420b2a003101ca01c801b094142da401000ea104c07a6900030300d80f01c080c210050100a0013990f0710b070000c4c820301941858031140010514080c00c002580103500410202100380c00102844601c0e805403a0029500d5543c5030f015001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 692436187 1250 692434937 692434949
    0x616030209030604060c023f07260d14040611030f180f010f0b0a050303030f010e151c05060108070b120709081c0e060307050706090203011107150c0206101401120204 73
    0x12404508d09003042d0010440310140b4211f24524040f016541d0442c80c2e001d40030340c81c984800300074041400d91825800d072582c3d0f561720039007408407021407252125040e8084070101e800500e000e14044808400409882c0b140c00b504c12490015211840020322801580c0c0071982288141c2c801400651003e0088070001c00108102040c4c2a011808100030302280382c100038043c3d07200f07104000010f580d041300903045070000d5088003842e486458040030312817130141046810145051820312004e10050729110070600078429900c40c0d1b40c03105030250311400c20303100c0d8542c0c0d0b079020311a400201d2500692203030020840c1c2017080c00540e0b80c844080c1090640c00100603450060300b64155030940240708180f8100b4111030040c50352a00d00005843d1740100c5c400034000c81d0362020342404644003580010070502e800360400e61500c2c041c0c075240d01428200110708145504002484161a00006080d8043d03423440070320125041c1004400c101c2e52010140807410004014541c011900652005002902e1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 692437437 1250 692436187 692436253
    0x1f08010501080c0904200103090204060b1c2009030304080114010806010f050d1104110301180e06041a1b12010303021902011b150501080616030209030604060c02 71
    0x890400440e007012500a105030041d1303c18020800060300002c000b1003000a0034524002c3c0d000f02c500102c0050802000094025203000c00110b01030102c0005402d0704464503446008e020f6140002c4030544030301c0c1d07885e01c41c08100040140e40b1010300c54003a000410024044a042513540c8450034203458982a203a0305070442c10005210002040c012a40035003c7c02d0f6000f0102c510303001c01f054051084100103852000341307041e030040654540d0400901d1b4441c400e000c540381c0d40c407414000750703001d450f40380c05e04000d1034014420300414001c2410380c401c640050b0350a200c4603a03900c018403031250091492818070214403011070740c4e0910801a06030b5501000b0481d0041d0b04503d0040e1404041d0f542c0d82e003407000f00783e00000c0180e9004c891b142201ea8080002901c080741441d103548591845406a4001c9081100102c0c100700005241841503860440e403241410010742c003030f42207201c0c000382943c150708018002808a0407541202e8200c00c2c0d107104480ca280620000450368860342c0840c101e00304 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 692438687 1250 692437437 692437439
    0x20a020a150c022e260903130e06030d020c0904170c010501080a151506031104050424050109121e0f0609060b0f012a2013020712081f08010501 63
    0x8180c0c106101c181100d1800e01c0c1d020307801c91705502c6811040801e09510560490000225800301c10720a542c440002000908203061725426003180a0380210b4030303030f40203109048405207924400101c410400401600d01d4065031509e85459201c2c40350182880319010082080c411000b800344500303402440024041c001401552804098030074002454060042c1041e9400607200c0c41944000215442801e0020f04600c9140280416003d00d500146d841881c0900c501c10751040340c1c1f007030403542d00001043c5403082e0b02c490054407085c0090203102416241c1102103000504a44000b0704403505642c402d49640e07155999040303229050f22000c071107440d10340040e03000f007044a0107400b203200800c88100c00c080c809840020800707200b003819619511a07080414000006a0a0666401d5004102580801c040981f45003448101d15030701402950002c2480c002d0245910035164801d0340510b500b12803806030074049034400b03009421054841010501d14181c01e44c050260030003016840b001041035 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 692439937 1250 692438687 692438749
    0x60305060f0709090b031e0c040905060f09060123010909060b0c0106171911030607080f06091005060a020c040f2918040305040e011403010507020a020a150c02 70
    0x11240c1d0700140495041911700302c0940c1e8041000c0240c0d0f120920300621b00c46000c00402e00e00341d5802070b0941c0062401da48802440302c0070a07040d01c0f941d80d141c81101d4035190751f0300c40c5603181824414600b900c4661a100070012009070f002049030001403400c4115940c42c0d0b1103000c1140c035154442d400180700043c40c0c0d5003c0b81d082c069400205260240150303002010f01906072941e180d80d100302c0714042514000800c00c00ca60003451207410001d41242c11a1810036005024640150b400052039201840003c0c0c2a150690005125110280003a0107007440d1005003d8250000c1014500f5801400c040b040681c8591080f01c40d01e041e40170000c65243d0300c00366403440541a904060b103401c1e0b10341c541d400c0e5a4845c40101070803651040210b419550311414221200c0c081d64000080d0303d48100000130f604c840d8038001700102c58041b03001f00900c0c6c031480b000f43d030b81788080c080094014441900030003d0144909280108020a041210325021260700044251b81b003140b0110015468400f002d82c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 692441187 1250 692439937 692439947
    0x30103060e070602030901051b1e190201050a05181915080609060607020d14030409050c0703090e070c050109060207031403010e010909060e030a020106050f061c0906060305060f07 79
    0xc520700d480203400074034200f0301c00031748901c98903070028148103001655a510510b0800c41000707003488181983c40024081010100c00c0510f100c403039007580710b0803600552212804021401d400c0d07058403060314008041c48256440e0300b2814070960005030395a1006d16913100c8242c2d40494082c0c205546401c0c9040c0001142c0f681140954034080014034000c000045d2140d900c0c07542c112108680701c0c0c0c0c6546140c4009a094890180c00418600c8030108010324040000060020380746116818865640c490200342c041c0c4c0151580600006c203060390410180c80c0506282d60000c0c00761410b11848981d5440f03203420344e04400c40868070141e000901c1d80502d0340c404000c42500000b145004d1641d4940301075051798081c10302030a818030303996084507002c00440d9404040c0240c1d4200543c0d44884052002074020443c0d4450349016001c01010300c265071900f07000300c8020040046031a5240103000c0f5814000340040340c4215000340d9188004400708804001191113400007001d805001d183c01040141 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 692442437 1250 692441187 692441201
    0x3110111090105090409080c0304090605090c27120a080c0d0503161d09010801090b010b09101d060705070929040506010c02100e01020114060f1306180203010306 71
    0x19481071081440580c0e0040c111001190100d801091410060401d680d061041200303020280c800098001070241e5a034001d0b008071801110002c01d030341e803100c00000b450321402e4008000110b40c00285003107030140d0b50007807070071502c050241c0c040c4100084015140c8510040241c5120304007180c4000c08140030491800c0a00c0310340341c00c07411030070600c2641400145160840c030a008401d801a078038443e80a01100340050300800c444415656121050300a103440c05080d20f810024030008141d0081c0502150880e00f800f50038940d004401410403130351110491158444100039800301d407030030740c1e5441c050b00400b401034014064403450166140103c42509031700c03405900c40e10b10b4040401e0980900e4605144d02950301061559608004960540004200070b41c0000200000007195620040c503c1c0040000e0f0000c1207a40e00503003005500c180200c448070b03405020b1024011003400c004519141d1000c2d001004124983c8514040c0310000d4080344500e103d66004c001001804054000c941e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 692443687 1250 692442437 692442461
    0x6110f0d060504060f0515090306131202010c081b0c011a120a03080c09040213150207050d08040302010f051b24040b07050a0203040801060320060a0203030f0606070f031101 76
    0x4507442c1c5a10172403000011b11441c0d215160302e000030707420020b0201c202ca1a010000303055070b00c2480c06040c10540842c2000055a04585520600e82601d005124a0b11009003540310040d0940d20b814800302d10390700420788541c2c009020700103084014824025107080c00421701140c40000008000d05c01050506426034806500002e880c04c0440d4002c1480c5411408161266580c0d01c0c000010501034803600c1031100202d201841d0000d807844201030794840d090340d20740c00e54010503912030801800461540c40030303064010030001000190700521712080300d000705040c42070030400c0100c500c10200b65105900300071504500742401441c00c10788541d00a08d2940441c619140c102600e887c111000010140703014080000b880140560003001179400514001e4000e0011036200c1c1303010310300c40c0310800215080d1a82c042c48101189040000c0c0d40d080000380d4000d40c25581c88410b40303a1a4280905a250071070802c210082c007007540c9003e6000701c68041d449055809804441e081c0c2110804d101c80 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 692444937 1250 692443687 692443691
    0x4107050105162c0d14060a0608030418110c060403020705090c09010309110402131a0c0d0503060f1503070206150109050105030405120406020a1713050d06110f0d060504 74
    0x82d1085604001d43d05061071846030100310414000a00c01c50b0a4426810103500c4040c0c051043c0c104403e000752030001e1480c80013603403420f031100300c8810183c451500400000741c0007071005000501805000400504c07011102160301000d5000010a81d8012aa0314403160800e0b01000b0503d82c0401402000302000e40ea107540c41e04c3c2481420415014000703403603042680340d411003c240b001202001a00d198014011503030b8145001c000755001c22184550304100d0301460182c0015200401607400407071100f005005501c2000c4c20071183e135400140210b034020520135070380304581c031a48000001c00c40d030425219542e00b08104080e18000b002820b040c40b800a00c08494040d983c014801c074216074007030902540340c0d1164070b000ca00b84081d4944506020801207400100c03290f0006000d04500c1c0a402c0e0b0100c500603140c0b00818074400c4c00494041e030a100d5a08010904040d050380d080603000312070000d40660181c41090307159001400c170b00e041c0c030030200e001c80b10300107984100f10007080c00b1982 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 692446043 1106 692444937 692444971
    0xb03040c03050d200a05070e0a020c07033e12011b0206010303080f090d0c1b0612060f0e0403050901050d0c230a4107050105 55
    0x13041604080c0941c02c2c5130592408a0415006074201e00500795950074501c180c600c17284050503194600f46c0c20481d5110320031040c008000654810309070200703501500f10300b11690103a201c070020b58028960301c01d4940311480d03a001103241041a00c0e0700000380381c0c941c0050700400400b05010091600351001044e126808150726040c0c0307200ea115140c464a428000c51402802160f106030340d40c0c805105e07105500d000d0402c0c0044640304800303900b00c80006a6034214141c83c04e80c01900445c064118400720a8040c0c010540a4107152000102d03551400303460403c6d40801074805030500000042e0781f070460b40700b00f003215046080f40c50280554100e11000900100d003540c400a03891021001d81101c1003c00307002c94614060715951301604001c1300d24000d2020051401032000d9240c40500c00d689003d4824000d0000141d51080f1a02c40344141031035829205d00801c50350000300e10801b = true := by decide +kernel

theorem cover : BRFrame.Cov 692266187 692446043 := by
  have h0 := BRFrame.cov_init 692266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 692266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 692266187 ≤ n) (h2 : n < 692446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
