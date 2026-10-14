-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3176
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:53:07.48521+00:00
-- url     : https://prove2.me/submissions/3e3e13d8-0d01-43a5-9475-133b279f5d5c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 571043165 ≤ n < 571223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 571044415 1250 571043165 571043173
    0x604030f1b06151e030b061306170d020a031706131e0513120c03031503030806120601031e080d0e0a031b03021911040501091a0f030c012f 61
    0x1842e40070002241c1c50042c10300f0040140c0e0b131420051451901000da2201070514421400094003581d1218040144680850800c1044c40d03201c90a80d0340b1082071800b611858400d80d90340740f102c0c0c1c0c00060f0f0503803803941c183c0c0c441080d41e109100c801d85142e8007820680d0000c580c1d05409071002001c2c0540f42c2403c40c9049805512144415210107688000d03110a4211001089101c0070500c0e002d41c05201f0b48007820326124102640c60210300606d000c1a407203000d041c24110210030968000e480c1805000304980078050200c1d41c4070420344a08007031000400d42342c00142d4100c440c04201c00e045500034024503000c2c0c246601d0744450ba003680d6010070008140c2d080030003007400b0160020300142e46a803410000012240066401035035516100382c140010189070130f807003420440092468100800090b0052000d07595490321240500203880030500c42101d8aa05200e06007851140c19940c01c000500504580c0814030056940d022018004140340d98104000c0e5000401c90603040035400c2d01d00c0080c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 571045665 1250 571044415 571044431
    0x305282d060f08030a1103040306020f30060120010231063c08010302130b130509010e0f250b1c0e0703030c060c0305090604030f1b06 59
    0x5202111a181c100c0c210b031408248040c096090000107507420300009040800014580d00c5000e480c501455100a02c45070000a0515690855030040c100c14544281040301e590146210409070035158010303118180000b00001d43c0fa584030f07003d002811070b003041014a07900e64074004142643d10100303100c61a04017070341c0504103e90142d207800d140d0f13071643c18414544604003400180035404412072a1180340d00420404840d4244500c01d4010480040584a10b04c04548000d801c0150900c4207a20542801018407541842c41c01400300c0b41c040200303044001052a004240207042c0a01071025942d40c5034043c004070350341008040c41c6405403500401100d800203c01320390038002d615042e06c85450790f540421082091105844100b103242c800028030389210f4000c0f40007840c0b0f20700900039030301c41c00c44004241500244420452400340000384201040c0400076010307608282c492101590025001034003184c402c0200c0c1c00100c481d45044030101c3c00144200c02481210710050f40c205682d8100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 571046915 1250 571045665 571045751
    0x1608041d040b07050a3f0b0a0f06090b07080c0a05030304050607031401060c0212010515011b0c12060908040e1e07020606060d0e070303050712030528 66
    0x10b42a84411189001c1380380850413400108240350900c0d440c03030350544c1c07110740410f005081c20740c1d07a4002452050301120700c0905030340308024042c0c502540b0300820b8911404101c610880781e0180541c0d05581b16080c07494500001314602e43c0c050141901d02032012b10a40c0c2c4480e5082c440d6000341070282000316224101418011300b030a00160445043c14540b103558a4402104003029044481a04000710072815a0011039039050000b1652340700c3c0d510b020204002540206161f0f01100020b0340d405e0101ea106010100f03c00360140c1d00503040018001042001c000c000c0800d41044e031240c0e9012030101c2580d42c90842c1c03504581c0001e440300741c00c0000c02810074991080310340101c0c2d1040004420b410100800394a5142c064029400303184001102c03940200d903600324440031011401229116940e9080041c00c580065904071071700c140d6400303030750701907407007401002d0146c0e01040b44800da0050107006c1240202c2c404070031010781c0fa280d000300b01c4c80700326081030703002c80ca0401d80c40f60b0509610071003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 571048165 1250 571046915 571046933
    0x60f091e0812070b0c09040e011401170708100b0102281106090a210b04080304030801082b090504020714010b0d050604060216020a080102121003081608041d04 70
    0x11809050960503c21080480c10240300719800041c099803184e1740e102240d011402404a040741181030b50b0802d04000b10b8035001e1101e590483d014991130706103a02051785882d441d050184140d02c2154410038040202803a540e000c0030895005004403510090001c0b4101400341343c400c0b11406240c0300d020301c2000c2c0300000485070f01099007161418038011899002801c1d0284c2c50150b8040100f8420b0103130316000c81c43c00d80b13a40a035080100c40680303140a00d480103066004072000ca0004164000004e00003078001000000c40c1401010020f0000c3c08102150701c101208030240200301240e64001265100c910080c5850ba006286602c403140100103224251014000b0a0b401130056061100c017140c40855100d411980c00750000d41d9440d5100e28800e0810050980a9480004a20006034800c0c0560040c510100b110746018150740d95040108082602c03840064203800c4100580c00c0100d202010209046120340300d000d0030030f03031140790490034200e5261400030003000850500c0180a4100c0d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 571049415 1250 571048165 571048183
    0x6010c0c0902030a06120b130311031810050a021b0411040806180f0304050105090609030d200c010801030f152903030310151713060510060801060f091e08 68
    0xc00801100360b40d0362080e82c02080141071f00e423000c0c83d00d1a82800c041c410502100d03650900000c80f910b41c038400e48403682e060301e50f85c0124401d07a60340e40b003102da90b8011000e50320300e12201d40180c80204004940081207441060700c0c0b03940180c2d01d01d0b440d4601d10380c0c41d0142010705541c8000b4015840e11400381c105564119009280c20341c000c0709004d048000000031039059030400c0c0381180e141c1ca01400850150300807130f08110741c503000300e011980c0e02550000d1000c0846403034840b4035400c08490908075464543c462049400140a00d0050000c0385501e405450040e1241c40c2810f40204404000011541c60b000b00f01c10b096402c50402001018900c190002010224003035451401c055801c2040085103200d07202400082d010000f10007402070800e1085440c014007c0c021038640f00d118011020103a090403207025188c03001040282e4030b1010700700705032041511100296401c2c039070141c410f401080200340802c4070221002c00e480010001c0901c0200c0102c03d000501401c3c0040c2900300a440c07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 571050665 1250 571049415 571049429
    0xe090a0902031009170f0405040c030507081b09010806181510090e06012102031302040f050403020a200d080301090e03160f0f0818040f0c051206010c0c0902030a06 72
    0x9109000402c80d48045c6a00d4010304408040d0b41d0b803000011100c0310701445d03201c6a4000d1502c8551f0803004e4041e004548030724240d80c0c9041c03069641d407480c00c100d402c080c2d4507003c2e22901404903507d25401404002c0d0411802041002e0180f0b004240e00308503401151558418550640682040d0030003642c115040345131801c041c8016030501d520810036182c004c0100717042083d401c090009414071140061084044140e040d07542c6d25000d81711010015643c0001c0b80100c1c54480d80400c10065481514003865260b0f001c1c16001c5110303125410724501400045144010450035030015a4488018952061085003050f840758074107030a41d0304907094008080c0103500200045d44d080c82c82040310f00400381c1c1c0084001204044d6003041c41100050100080010b04001030710440710b846c0d00b01c0d904915404035010300c02851400c82040c00d44900c8200ca101080051020142c00c420b05465140d02900c18500544072507400d0b00c80c3c2a01e8407050b40920759442e4000140b1070746000750f00030b01002c0c2c440 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 571051915 1250 571050665 571050671
    0x405060c25051513031b05100816031e020a0309060f090c1502070f090f27021309060513211706030f01060b0c190c06050a0e090a09020310 61
    0xb800300400c400c1c2038003d03560b00c80d0400000302420820780700d00c0882c028613003260180c40603091090740c04000d01c0103401142d105541340e607a001441881a80c3c000c1c85040080d0303191411002c040c03003c1e00170301813080900340002501e8041d51034114071440500000d020a0764086a403400908191040310080c2883c40d0b02a400c0c0000f880100d080c1c00031f4401200c82230800e90b070402180220403410007490f0f420080170098201e4000406100a030044a9041c42220041140e048929507038810003200d080100c4401c40102d45400c098501691b0074424440400004101c501e80340e0355400841fa002c481c814054510400d02c0001d0081040201c55540c3c844809901c6260309013001074100d119201c088005c0055640000d40030381c030140258103084020200a011050f2a0700c8420103c1e08080b1796202d00d03201d0307500340400c54010f288446078296000b6500245040c140003044802d0360010400505103c41c00141280da41c5540019038400c46224400007000750080c0b041605161041d10500c00440c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 571053165 1250 571051915 571051919
    0x706060b0f12180604140115240c0203060c0301030c0e060306040b13050708011b0504050f190e0f16052106010903060509030901020601080708060412050405060c25 72
    0x1851108a03045080341c018925140d54039841c0d654103c11907560607121a0161800303200401014100b045020407295000b030211281e6240050354001c00c502c107a840d2814110958002c621900c42000c0c2882058076240d244c0312420f4000c83c2c50210250b03420350310b5002c00001082804102d41c600e00240c641c1d1782c28811507044c03800000b5901c800140001d8600c082500200f01c1e08007080c7c000c0510258014190b40500d50756960360780c001c0612018802016011150400d0001d106808450a8801c01024011103481c3c0c89d00b440042542110414100d0f0ba401102054022603205510300c9071041d40d0030043d00e4a4881c000d980103107a22801c2c401880401c0c000d4a408840d0303c0c3d0050300d0215103141c6000755075a135000484480c0c0090f84090685442e040c140100d060000c0000c00c0e400500f23800300c0700c042e60b0310100d8942d41c202d00d103e0180147c004a002c03030001034150460701074152892071b14901305030b140c00c00205903520541c006041644805c810030010140c0d40001e0070800d81d0f62000e900c0b114 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 571054415 1250 571053165 571053187
    0x20f0703080a0518040504061b02010c200c131a040603020d1704150801050f010e0a03030e01090510020a05070f050d0201081902030103030f080c0f04060e03070b0a02030706060b 78
    0x101403450074a00303020f00030a0a0303890405003540720494100c010002d10641c18282801002091808154419074501d820039141550050040c0c400d245040d42d92a059076000c0312060100d5601e6100705041805030640000341c40d43c4514101c0110008401c00141044440620803440542510f219000710b04100c0300304003503540c04032403000080c6c02400340c450101034140d581c0c09a2245400880407030404100b140754456201e59000e046c1c41c003d4a84120541014006542c4122044880355110281042c20b00000c2e114524060368858103041000c6150b0f100d100148650941e07110707403001648001e040c034050103000c11a6070010440044a030012904040c04036500d41b4216034042e05001c2c2c0540441c101a1603042e1104a811101d40119200d503164035004051a440712202000522400080f41403c0b0124040766050140c0880c2e240c5021310b0f02d40103407004c8080d0340c8020341c94090204001092805031000341000b8a4a80c055035407030740e8a15200c0220b50b19034200b580f131564140f00d014610 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 571055665 1250 571054415 571054417
    0x5090406090f0c171204050306040f05010605030d0c12030c020d052b0507200709111b01060602011d070e0624071505070807140706020c03030106020f070308 69
    0x20540100c4041186803907410007980803044140002c02d19000e5000c0094050150091040525008810369010100c1d815031000a80941c0c0151a4180c04c550081380c0000c1349081e10315900c41c07040001243d01030703440d40020b00b4040104a00e10205200300200020032500b641550030411150804000712082404005c4d9074550345e05c400000e101000520300700002c002d14100ea15014030300320141203000f1010200003d0581a102900131944040b005003000002d1000c03480b280311840001c1c1140b62800405002a002e102c0b14003500d8403040111055a40040240f0810386260f800003060051400200908484944c02d51001000440d010085d09480c0801c002c0c08648903620314103941c2c1c40c0c100c006010b600e4010020041c000384840201c0307040c01c0c0312002d40b201e14003400c0768010f1008003501c9501660f000300c0303090000940b00070010b520603002c1c03091950810444184a0305124440c0d541004a80c881c1c4e0200129a1000c8010003078154100000900b00702c0800250208601e03550b181c4101e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 571056915 1250 571055665 571055671
    0x1106090607111002070f0605060a03030c02060306010c0206070b0106022401170f15162a05030c03070f120207060801090c02010f0f0c090f05030c0d08070203011e05010f0509 76
    0x20010400d0701c0d924070400821103400c15004500b821561741d251440d2039000f03003039916421615141070800207211840e207564040d003102d03019100c0743ea0318042c550070014254002040c603810300880c4803900f40940c03200009000c500b0710904142800307504002020b480d205000300020300d80716100c440101c02d4440c6261490445001b9180103c40b045120410307400e203c2880d4441c2002d1080035100800440644042d90151039000c3d0a00220403540c0300885040d4003002d0008111900c3c070b04101d0142c003074184110203103401481541e041001182c1c1e010700b1640704034001c0e03d03503020050300302050200b02d421451075081c039400281340552815030040c108089c14860b04613030350342e0751000740c00240c000e40000480a40030348081121101d440000c01c001c2030381290b52000184d194038040740c94010066110142e443c02402049280f04d000208641c2261000d0100c80d004028040f03880180c900f40030307a0f0b9080200311130f0341020100c182780420486005a11160807040d00c12000c00081d184c0300b03001c40e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 571058165 1250 571056915 571056917
    0x130203012606270c03031204060605030d0f050c070e1014030303310602030c030910140c0a12060f0e0708040f03080a0e07060e18091510030c030605071106090607 71
    0x301521440c03283d424224000c030382a400d4080020302c0d21011900f200000d1189110b6082006180d03107076010b06941d0301c4030201e04000301b0003144104202c2d0b4007560241040702d400e181103843c0701d03413100d0701c2c54844802a168030f403841e46908424002c0800c0090b0030b5050a80580007035056181804041a45803d101030b0050000141c03841840b40900c4541c2414045400c900150b5903810909411110f41d8007c84410030180135247c11400700b0b94041c020784038030144c803640d01102503ca0b050504400d031f0010040c8000e10100250110005030140104001050000140a100c034500a0a080e0074a0001c183d0310821044004110014500240b8034098a405103440aa42d68509074000010880092074018902c02c05600007a4180d10034078070031030b0b00e4059807820380e4007005c6115030a01003016115040c0030b07001a80c1c1003030201c00c14810aa4007418081e0f070050f5031039407510b40540c0340e4416042a5002c5841d24108480c1542148400a51035a00380082c00700d8940991b41d59150100540100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 571059415 1250 571058165 571058221
    0x30609081c0204170303060a1403070801021603030507170115051608040302040c051207031a030a0606170f0304170102070f150b100c1103010b0a080f120910050702130203012606 78
    0x210300380c90420132140500030b65270084fd910381da0004085210500b0003400c40010b802c0000041d070b8103100d111808912100081e03030314004e07402c0c81525000c41c0c4c00c07850a40200103051080c2c07000a00c14144c41943c0c54041d0304115030303403400d50043c4015500d8130b00c2d80e1000e01001300304009084401d000c00710381c0700c2141d03d00000c001007018030780410814100c04940e4544030b044403020901105910210480300700042c011514001200c0d610303203c10b0000a11600b540003804100485007554482c5039a0b100400001407030104550390706200c10543c0c0d1415560f42c40103041c02c1240450a12403d441c81404580c2405010082c10000b0040f0252441c020554880c25000c0e410030b07203094215413802c000c0140380b160081d44400c01ca0f82c1c0d030340d004800d4004a02c80d01d0880e10700f800540044842840000c0c01054200b044ca19040e0b5984d40301070000c82c0c02000010181b965102c041c4095400307801342050704007040c0140c0071000c4004141e10000c21040d0084020701800740e5021891180381c0484072510 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 571060665 1250 571059415 571059449
    0x403140d091a090f010e0a030c020a03080a08070f14030105102a020112090c05061323030c090f061302041d040c1e030609081c0204170303060a 63
    0x800c0030701440c90700100461240b6000d6000d0051500344507124011a40840e0500b00d2041421401d9a48281603c03080f50007100559001c45c0c0b15101801d00300e0f001416030b140709642c07540c50301442d41c41602c011703001804901c03e0100c00381d404051840088104c0c50284120b1890720b40501c0030380310610584e4800c81070440000c1045024141489000403051108103001d03192080c90410031070810b208900180340c07082181054212841010110b03030708160034882d0b017070406090080b558001e5064400c4da091003e000200d00b040e440300068903011082c03024918080c4103060600c0d0003441480140300b021401e04110865580c1ca107180d5000700101c42e02c15840d1344410b1844c0092290760049119840020f110320701c03102072000a507000340c0c031030410700740340340e9039104560a04102400101d100d400c00102c2040421041e420001240d4010032040d8901100080d0350881141c0300e00170b0101b01900400c0030000081e1447d18091000c2c150805149545080c0340001c4200ca003500480500c04100f07051 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 571061915 1250 571060665 571060687
    0x10507110a030f1b0c0806060301180c03060e0a050d1706030d020d0503070c0204060b03060f030304080703080708091011010516090510020f030d09260702090a1b030509010b09040314 80
    0xc1050f4a50044007071701d0030359101d00309103850780c01c112003141c000d6007406036a80c45031b00d0a4600010442d00281144101404c603520352011b410405181c4056100303414640b004118240a20030540000d91661244401945004100d0f0400201424801c3d08020854080c1c16000704030308141309481d01c1e0560f642c0e51185015202c20000200213508035281000100d00040b8400c01103019800480303640700d0511400307003095664840c50144c0f61980d040108100000b445000203051568454400b0070300304004140030a410b00c440e40d49820009041000c040110402807190941240450284030400c251265018064140c0b038490302c1d003d102460114030049201b0303c501039440920034192641c4007004035001014040d2400c0c162a5140c1d09000281c08841121900c0044a1f00c1410142410441c0e020071450520040500d00c05a4551020188281e0840345c2c5000b4286076440000d1241400c04981d4210380b04007021500034018003040c4030109410222845c44402c042c409a42e032045400c503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 571063165 1250 571061915 571061957
    0x61a0712050c1b01201509030f0d0c0302070204050a0b01080630010e01110a030b01080f01091802090106030c080108010c0e120c03070906050414040221030f0309010507110a030f 78
    0x3c1005070070f4030100c0c0c02c050540070104c0c44242e02c5050000454644e214043c7d1179440c0d00c2036040703000c080c2c1d1003001640401045a000f0041440743c90070011b0601345540c0101d02624000c41c0c0e40041c00340e448a542c6000d68215400342e81010701580d80d01401c1490901c45010304401c0d040200f0b86040c40348402080d84002d4000d049040707855402400480b104003100d8006410080250010030b05100390845c075544281c2026115002070403402120f0303440c1031401001003a001c040c10b10814204a070500250710b9041d2101c0c0244195a0300080842e001c0d40b00514290040c1c21420903641032035145007030346600c201200c1c0e1601d800c40701304880150810b10549042c500c00c003116058080c1d541c00080d058000ea10520448100391000d005141800203030340803009007120300a501c082e02d254044404c000c10303440080c541121208482c40c2003890b00844895400c00c64102410780e440d0b20403c5815607001030340851500c01440202a03000d602e40d0b028110344201680c6004004d0211507141c50307050011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 571064415 1250 571063165 571063187
    0x80406180f090e0f011d060a0903050306010809030705120409061a04260109030215070f08010b0d0f020f191707030917030702060406180f080904061a0712050c1b01 72
    0x140013040900c1036200f1b45080d10204011840080c062000041c55150705d43c041e007038031160305a40c3d5524540c0c500006450344100a860064144014481600000c41c20845040c41c4000c024080b0784032441c1007990016070f800c1d900410740c0f10214150340e40550048005441c04c0d1994001d0b0700d115080307041200450582c0101d02c140743c2c0c0d804c0c0360381a0180f60300481d0091240e8400341c1805d94554440c0703400e0320300e55100c140082c005040340b0010410900f840c005003400701105140880c7c284014201c940690f00304000204d064100001c00940b84056034244003400001810216550340c0a568001c40d5034070010420f01c10300d0f403034008030010016207440034403841441010b513644a00301490020b54685c0102d4084884600e020840c0804d101d0b171080d600102e82e4040c44903000c0e91302a580e01e1446e074010306900340e00103072210404552030b10300d9405a54031070100a501c5450301c0b0301f81840c104110302c08035090140602000130b409910740104000382c0310440c150102d4011503003540103c030456010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 571065665 1250 571064415 571064443
    0xe0c090703230103051501141521150a0f0315020706020a03020c0c030610030201030e101b080a050105060f0c12030901060618081c020a0f080406180f090e 68
    0x24640c1150000320340b0310054141c0b0b0140702192003495244a0340d03000910207004414060002d2001940f1900d0b103250420302d25105d04005a042105142ca101441c0e0101c42c0a84607100380102040107501c0e12410900e4580011114240d6581ca4541708081d048400c1c0070103001d042ca41c4580d50340c0723109a9011522203a0380300c0c40465a135803185070010300940000d03882c18400d00802020703928511700000d2580c002d0405692030204245558010740007803009032040c817624021413009200c41c444600c0703a20801c2016164860200c40c0c0300c0801403584000a04142d2100d1624005000039182e913030540f0300c00e150041040e81d4812075014018601207100205a908607400070401000741c0040d01b01c94222040342d103da03a40070201c5911488429524001c0040b42e42c00340904103290710141c1e0540c081a0f4060040e684201c0c0c583e12085102e841030742c01034071a50300c001030030400302c1d50001032040708422900700b03201201d090404150040d00548965501207840e0000582c0d41d91050012166840803 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 571066915 1250 571065665 571065701
    0x1106010e1308070b040807061b14070f02040e06040c210311010905060420090f0f06121218010323072601090507050a08240d1506090e0c090703 63
    0x820f2411040c2580080c5081320b4281c20720b51401203400108100c070605c0440c0741c850003d500c10300d81d40c002e115088240c095030341540023304000982c40c1ca01c6040b20032204400a000285020700303114030352503129440000e000b60040488010802800c0b052506d166041c0340a401030301c80b006003d0702600011201a001d80507000510080200340fa003015495000d0107a100d40326100da0080140d03180d42151b1041d44e1810741d00001c0d10f10304186241e964858070090400c5a110808140345140441d130f80b040d00700c4840005140041c07038a8513001186221001d2a050020040c103180010b4a0300c4650451000350322500c012a06a5018080c0d101016a000c541900b020201c40b0302038420310400c1c81160030f164604408181031600c43c1d0101e490080f4150ac602d1801d0705e41c403101018a2a00bc1610b10408010f03a420f0f200750340d11007400040d2036001e040841124044010500c04841550b48110501e03072521440c421284400724039090380e400c04452808581d604c0c001c050340a000090700d2500070450f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 571068165 1250 571066915 571066921
    0x320120105071805010f12020c0321061309320a031205070206010302150307171801110a121505060a020a030906050715052509061106010e1308070b 65
    0x40d00c010084590701c0720348543c101e6141e942e00150790b1742c103210703092000242403e0036240e0040d003c3d400402c00008001c045074584015445242582c0700c00b40c5940000c4103040c41400301d54904150000242c60b2182c1081001d43d02564807070036403c110140461001c840c018100c2c00d080408484403030072000700f10540b075400d03c603860010a4140201c10ba414081d16090204045900c00246103041ea0707400b40c02c1101c900b141c8480034031203400c020301450402c60581c0c0c01d01840648200c019000705207c90490031403854800f451402e40f1003540c022174902006202120f192980720a0340070101003242000a030318540c0d044c08070810400fa800c07094200200040d00c940a80e40054130466003802035554243c1c00d91100d00803286031141e02800b4000c0245182a203500f00386941c4501e4000203011070351880202c200803c0c0e100b84602d624102c02040c0c904038200200c5410a46000e500f4102101920300b641c14001240340a40b0040c3c0300000e48416003024a040080c00802c484409800100144c0945 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 571069415 1250 571068165 571068167
    0x10c02090c04030203011b020c01050c030c0316140615010f030b060c0604140604030c02101b0501050a060503060c04030f0305040806010807060e010f0c1b0306090605071404032012010507 82
    0x36002d88400ca00a619103200c200e1452000e60001416040070b50103801501c5081c801181c00703810682c0d80b4192400304004000c68044100300500680070709603088d284007003650400512a0704100c1d014282500310208200f000080801e860386040b80909240d10503101a401c120300038699001019000a80003410710348210001521030b200e1441030f020315500f1000168040d032a40c4081e2002004070714000d80040061078030900d0400c0002e040e01d41508408460b05880c48403491690082e130761a555182480140c005030302a0074090071040e0002c041c0382c1008901030802d803240b844080c000b013517016106001c06100c0c170102d40003400500304941003941c603481c01685034a03162140002040c08914080e8840d40501b00c1c80d510100e07581c44010380301c20540c882d0500500d8240050722840711f40390700400021814406d40404074012000010a894145800740408240025410200741c061000300000b03124450840580c1d500c0f0818244400504000709115099000307004546501b424108101c035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 571070665 1250 571069415 571069417
    0xd0905030c06060a1a030a0e010203130c062a080702091608070e0d0b060303090310091506030c0b0706020f0c0c030c061c020f0910090f08060f04060902010c02090c 72
    0xd910401d040d55002c0d1540810445042c07814400c0210281d070800d07500910341d50080142d584140d040e500031883c1905023450f5800c80c0e0003111941410b80c081c1c804942400b240c1010000509240d0500e40303485001d1451020a03001c081c006120456483c4000d03030300b040342581c16100300c158058521055402d00748011124114500803010002e011900002c40051003031540d20450035000c0d0207200310480715203600715050401880141c03d407000700510707942034034200480e030010400e000d00003a1626180c581601c9002c032801e90040003074201902400444c08416103201103076840b6084983c0c8002c5464100041d01460006200300c140100d45442c0c0400c0118200641d00340441c107403040403200d00d041065600541a04000520a11100313883c2d02c14141e0042a00628030543c0c0fa007001b40740400030361008804100c6e0130000e241c540302000703480c1082e404800584041406400c5030302d0b1103500a03007928002003000e04110b88906144095900840c0c00500164002d402c0340e200c0d1a1a21440340e003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 571071915 1250 571070665 571070677
    0x30c1513030c0905060a15050d0608030a210b100c1505040b04020f0414010501030e0c0904121d010e060a110a11030d0305060a150909050906010302210c01050d020d090503 75
    0x10756424030000880030710300241e02000b0b907201841d20380291f0600800c1180c2c5900035919010406a0720f07400030690540802c0a89162202c5583d51880c0b001ca010313030600c02d07006580b041a966410001f01510665940d00d1403501d869140c5424442d0030100e007004d003c1059201c800400031481c100611003800030b520702c0144241d00076521140040724150500c4100c1d0004241e000204c1021300051003a503110381c101c101c1c4000400100c80c0c0d800c01d003200240c1405800d80301142c048402c01403c0c031920740c102c6801e10995200310b01640445041c2800680b0740c0701c544246501c100b10000311010400d003c0c190031882e09203e4000c48149440d10320b0302c03201b1007441d1661141700344104800114100e10038000c0343c0c803ca002400260015103081c0301c04011081c0b08800c0c00c11300801000c0421181a64130940b8403c1c10410020318203540345005000c100b1840425480719200e5800725112030320000920002800e000b1304e80169105d080840c10b02c02401450000e0361400e0500070624140304000000d001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 571073165 1250 571071915 571071929
    0x906030b0105030303060a091a0319030e010507050a110103110d060f050613030803180a03020105070e1e09041e03020705040b0d0b0112030207090603050f1209030c1513030c 76
    0x3115076280c500700356680c0411100103074030404108040c891082603800401c086112a01013918000d0040c0000b03050006a0b8280d4030940b00c11884042032592180700060354036000c1c207265181008276143d0302d403211900c2c4070107401c4102c0003c20482a0f4400e0b44035000d40c1200c85440b42d19224400c03080d402501040c4034111200501d1800407d89240000485000042243c200c003a11031030341c0e44811030343d003005105d10405141d1503881e002038401440012160340c031990000070139203003102000c1e11900080359540d0017000103110300003100b00c0d610070740801103000f00e545080c0d41c1c0d00c61501005418a038145094010070002646042540000b201000d80e07808032401d02c1200802020300601101026000e40f840c60210010801003803680e142801e070710f0180c03065545840e114889542521295401100c00d0350107820708100364802400742c869400304a08840e460f08c2035000000c0c0d41d518103954413602c41c1c0c02030003200c40e032921640d0482d82543e40e230101100380c0c00d41d28104180c7d15040c0f0321801d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 571074415 1250 571073165 571073183
    0x31b0c181d0708070603111e0a02010c03020313020108130204020f041404020901080c130e070507030305070206240d1203060305070e01080a0311032b0608120f07081201090603 77
    0x185021002190940c152452003005000d454500174048018200031000c0e154013810401c109084c884203480708906801500221039903405030088001d0031074115072a075030704241c03041c010711200003061185003803c4d9409107800c1406885094030340350080d018010096000b840012203043c0340750084050400c542c00035004039000312007041404164032035547c072180024600e000042c808055a005400d0100501e241000001e441e1401c0e0404130308251540404a14080f0b00c45003090303851700850743d10008501c06403c841c00c190f52036030502041c241c0c0c070683c00d15842400c80d52549500182a00b60f0742c00c0790340109080d5240fa806001410940000d032800d0094110200c2d010045054103412581004002c0c04050410748003107840c003400040c400d01e24041004109200300c1801051625020000b445004440c412440042250756a6009607456000103544000d0549504151034414200080643c0c0d100ca243c0341819407031043c444100404038181c40003060b6001e8640c0f100d02035900c500704803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 571075665 1250 571074415 571074461
    0xc0e01020604050601090519021303020405010b1810031112040b07081006050d020405060c0705130c0206060415030507030c0503010f06051c03210b0319031b0c18 71
    0x1240ca50720202c502a0080c3d00c01030040020300155803210341d102c61590194880003400944140aa038810b40c08082040b80c214014819071506224040c0149200101d0600c1d0800c441000198501e00740040c40c8282c00f0414403801840c040d80065249072141074013a55202001456005640d0301550169058102440001c030708a025840e428041c0180314000007039540791403c03c541c107901028040e02c3c096000c1c8000142501e40f40080c21003000044050305c000c500741402e00400b0700142c61107000b2941004c004004c020340100d0076035006201607801151050100300001e07800d003c607074002011442440000014003140a83c0756080d07a4048000713000070000d0488600542d080c5009040e48800f503030f80603036840d401c0c0d070401c9610f0910074281691180000070865600c45010940150400d0b11071441c80308500c1c090000320403c1ea50a1146480400152801070006860b180025015000036900109001d83d507500d0310001c00f00902e442030000004141040680041191901d25030000c2e452 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 571076915 1250 571075665 571075667
    0xf070507141203160804050d12080601021606030203100b0a0503180c100e041103131b080d260721112205030d170106020307030909020a020c090a0c0e01 67
    0x100744490710b00348001c0d410085101840ca54400e4142030441300c040007000009000d0300d85001e084943c40c0541d0f1901040501d0340009040c140004100e1411500700c41d0034001c054549411403003e4403401d240058595071150400304503686c050f0454100c3c00310110301404050b5201000758420042c00c040b02103038103e91540c10741e40303810400a036607104018101b440322041c459485240d084800030300100c0c1c481400c101e07000e03250b80142c8594030024401010041404101c1060301000540414204026498042c0312a01d66481041d8103042121807913400c050b00700f900b111603075070b4005034428440d40d040103400980344e1500d0724041003100c0d41440807086101603500c240421181c82d000910324007412130a1507442041c4041409140c1800c218020030300381c408100b0352010b4060364844809054440c1f40c0c4a100d00710590002007150300c10006900026442030301001103405c42c950141e120440008242d0501140c00d0420303801891202c10089100080d0704641400203264440000007040703400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 571078165 1250 571076915 571076929
    0x310050402060717090a0801060501090f1404020a140406200109050d030c17270d052205040519060f08062419080111180f060f07050714 60
    0xe0040d500010512141001c10180040807000c2142d440c1c0d1545012503200c0042c0c8480910303000718180e40c0d510081840a5600030700c241c0c01030700ea0042c01c001414680380782420303080c18003a61702d03001c3c54000c540d00070301c1070150408450300505244050b8840d0340320400181880d505010b040c400441c0040000c1c55108184500b403442600302c006400a01c1611200340d0150640031101000c10590208050000c041008410b00803c00c6814940e1010301d001109182810030403a1050700d5007080e05c8440486410904445003940b160f0031054a046a000c015094083c903540b1203a0001c0c01c10b4104043c41000c0140141c496020703603020040070b0384820020014008602845500d1b80c00390010940c0c0884000e4028407d008400746103110030320020108081e00c1c0761101070904551040c074284400301c028014522116080030900b41800070020a50262640c0c10280030301030060b0003201042902d812046540c6003503244426603551180e407a28030355800780c1d80301c1d2121415032510145031a1400031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 571079415 1250 571078165 571078171
    0x60602031602010e0406060306080c0105030601020a0f060f06080a060c050a1215080102190e10050d0e1005150310050408030619030b070f021b090c090d0501060311031005 75
    0xa40110704207803960500040c60980944140d061000411913a078003540c1d50700550001c3e01242d80c0214000c0d1405040ca442c00c610108030380c2c1480418410403046907070000716520401d422044030b0069583e9810404000c0141d50210303600780d414110701103481180003a020382918420308041041e048007030000c4607103009008080000881c130079109003030304090790010a26400e86040d801001652142418220380c407154010280081c000c17130221003207401c01a010103000060b41c508907280c0c0540d10080062168144030030307a1658030a2001124001044001c1c0080d007090400c00c12420308030208034600190400c05842485a030391040d0f4241c2d014000c5a0044c0c1c2d200c0038090840e250b4004104400b108800ca502c541e8076440d074000082070007130724080e0042d081078840c10041103036504005e060000e4115900c0c204a90440d1707840340c540720805440e41c0446501d1441e87c40d4200b90001948110420300e0240c015820000c002c414000e079500006040d032822070844400a03030121048007955812 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 571080665 1250 571079415 571079417
    0x804030e0315060d031103030108011e020f0f1818061513120807120c0b070201091a0919080307030501050904050705040f090f0605010e011208180a0b0d0c120606 71
    0x1c00842c505013000760030f1181c500c1c402c3c06d0407221480031400c054650380007640109030580d1540c07194031058a2001d500c00c004200110f0a51815074414500051440b490102030100c800005408080d408901c03d0041803400040030107070300320380b03840c86404c0345041940d20510900030a010440c4090009c4e048a440015142150790094070f44240700c4c8880d900e802c0c050710942e1007004804000740410050010482007500c58a034080e041d03003000605400f005002006580c54015840c020800c7c8428000284003544507510f00c55540d615004e0400c030036911040b98010100204800300117964000e144261000e82d0100016079803201006080101540c000d031083d001180144514109074201c40711846c83c0c1e04000c281084240e030743c41c0c0800c10440b001d0356103658600c01070040386400c2030b90a0040100800064018541c2d0703c81d100e851040f403c40b0081c00e0485d66800d1100c0e00c942c150000200000307c00c05844d1100c802c14940030384205085d110000d2000820300490914500c55082a0350007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 571081915 1250 571080665 571080703
    0x806011a16030f08092b0201060f08010203191802090414030c1b22090302030910020a171809060301061a03100501020604150f0603081603080c190f03090209070804030e03 75
    0x120701d0050386c0c0001000924085549805000c90500e05408017000148112800141d4a00d04002d000303407000400c196481501d0708103181680380d2040001c12403021901140d030010107460314a055001402d25000703044003400003180310240010046002c814040c0ba0391001c0484004640412003403452400203209041d02d140f0194221604c50340c010307d0030500c00e00440740b0301a0007100190a1035200c054400050f80710440b1001017107030707644c0c1402100a442e501503003040308503030182c2c1241e00394010700340c060019a00040c40ca03035400d41100008105006c2c1803d6610107a0845403550340c4100e80c2041411240c01000965500c00502e062142c0d80251500c401d0305800004c010103000074041c4810405e484410103c00301e41c0c0203004180540003076004418509251070054040e40c0003d0882d20b04040a100845000c401003554640700f0a0501e0040190280000141c0c000c0004035400b1b03401ca6454810030128541040000b80520b020b034030307140e290000c510201665000000c180c4010b41d81 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 571083165 1250 571081915 571081963
    0x306111e0f070c0308031603050c031503210301150903031418180709050f0d020f01090b0408070321020c120f0609030909100806011a16030f0809 64
    0x800200a0201d00014603822450b040190311020003000721504240c61800c0d0000c280054200015010601308000c0c2c00d00b40080d00e080d102d5070405010048c900b6105819224054040343d6081c024140614010200c0c0e0340820103050040510390800d0180c22031180d402d50b10703010380034084c150340c070b080b02d5259450000e000e1601144e00541d40001c0d484030320481c5040d103071182d40d5071441e021014140b11030503c04070b946030000d00100400c0d81640641e000b40300d070080c03503a0192201050358982a8058804540a034942001220361600070740c01480410000300d00483c0300d27180466180204c82c01040602c0c0894003400315a156001d148004802580c03102e10700d00d00724240f00069102410001c4103444061680680840c01c0079400c17031300c4a1040e040020004240d24290b520380c1e805c00b04c000217060f2001d040c28122541c4800602807001202d1000d101e804519182c8021035031942380c0045903625248113850003420303a4000d080700030085525500045c80e60351000980c010f541d04000b05c5621045 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 571084415 1250 571083165 571083217
    0x1806130909020d0b04030806040507031104351c050424030e0a0506090601060503070c0303050c0f070b07031a0612191b0206090a11040b03160609030611 67
    0x1c0039001e400c0383c2000035886280003040c403081c2e890384a90f020340c580354018a4183c040004075a0010054070500d450059415440a85a4191000d40d1048904203500c4080d0201d04003030144840c00d03401c000c0110009080c900f00c0e010030850f040140440c21034980041504058030b042c0103602071428207030410f4410342a030052030100150401418200040c030011003170402d9003082600c03481510300b42e20150034058402020066036005050f2132a10600f9428280d800804a17222050081d04040d162808507031034889000884200c411480c00e07556542115150801004104443c40c1c00440d10780104110030440c2c035004600c03107807030080020789013001410302003580040c042c280c1000c001900b0158210444640300d0140c0000300712100e00540740510400030b2905900900d00031458021b007010100180c000403200d41c00800031180844d00e12087d0300481d02d040b4024250b840005200b100c001403141d040320045060340d0143c3c5040c001000400d2140045106009460880740700d803403050f00e114 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 571085665 1250 571084415 571084421
    0xe04150906060b1b07030f0224070f1103340905010b03060a12031e110105010f05040b120a03030b060c01060f210c0b0a05041a18061309 60
    0xa905482000418204649462044441c0707600600d4400100082c3d00070340708100a80b000c020010000100022815035403001495450140300038092903090001240c401000e040000d03e41a43d080d1180d161001800d04229140301d20005550145420205c02c10600340850340d5158191020f4504030703140e04035001070b4490b00b90080203c1859030355007404142c10715140101d9000380742d1600d4140e180e003008401c010715288960f11442c00060003001c0c003130019070410035400d410420255003064506005105a50030600290380700b1840d441c10001045175121401c0c0842030718419130341040049152802d00c507450100e600c3c03009207039214406140010f8440e401c00304c9000d001400050902c003000c0015801e4a1541d08102c0344c3c400c10440c00d015a11042c10601040c0d4500a50380310b0707852700f03515a502e0340c07140b034018040054000509151014040c0c0300300e40c014004403180d0246207000c0d03051a85a0b8002c200321941034000404d071002503150603005c0c1d9006062480c0c104428078a401213000003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 571086915 1250 571085665 571085693
    0x302010f110a0c030c12032a02030a06051006170103080310050307030f0201080705160b0919050c0a0f0b030a0e1002220f08070303050c0f06010b220e04 67
    0x82041086000c00d02000501039001164801d603d107149881c00d6240215a10010360400c440101c910440040441e0384502031005041403007100c0e4009a500350004000c0440c4030720042d4040c404e446001d4100009a440603100300603d80c0a40d5009443c0d400c102c50b15030703140f0340c2204041d0600c0d00510201314484010340d0484203031140c42c80038556aa0200e810308100307038030030b03a50540501041c0e020355810094031540f1007a18607103a071400566400d03001c4104468007015101444000008002d04810444820320240034480c2204404480ca042680c81d10715523031f00784c0140b60075000051000364040601050b1030070700d180b46042d41e480320341d00f0004144c4c21041a604e80308100b07800754104918801003502044042043c0001681d03456220380c091705030703480440301244200003003000d11800b08110056a6240c50225540c40d0780102c082d280c0150011940350328040c0c0b600010303c0d030f115840104900c1e00f000c600c0c00c003200e03540760580204580901ca003808d06104c0c040010005086491100c030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 571088165 1250 571086915 571086917
    0x80c1207030c08070305070b09010516020a0302150a0210021602240a110c0a06080a020f0903160315050f06010509060c06190b0303180607080d0c1e0e01090302010f 72
    0xd50568a454186800075954804400382e00010f405000b400802e00407113026010089031a440e24607081c2c0000c040e032085145030311040d000703908030000715030311181c10344011500144000206d59501400c00c1c00e0354008242a005031140e46220400c0894500984555180c015282c03007511041d0b800340600d02d1b4001003002103034510010750005041c0790340080c041d592556928004081c10400c0440d240c00e000080241c0325003030780e04082048039405240c05900c00036428000d0f84a58030105130441a0041300d14255140c081c69250707a40a0a41110301d404990040f2480c111140e10301d22131004848007a144503080b1000d1100213003055000b44000c001420002e4000d030701d4441840c0103142841010750700040e552035541c000300403012481c0508000c0c8a402c402a524005008074403443c076a8414200500404004c40c000e000d00c20742d80c0a41e50000b00754802405800c43d100070040542c0c41081445040c00305540302a401e00344500d080041582040e10307000e07400c50544e0019120b200d641c6941030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 571089415 1250 571088165 571088173
    0x8010c09091416091203050301030b071106010311060c0717060f1509061f020c010e0a0b0412060e070f06090f06020606010822030801050a1d043e040605060301080c12 73
    0x217010303443c0d6000b407100140079965007503d035415494503864680300500000c081008246d040c0002c0760000c80e50380d04403540500031b4401c01d420540810b072640035126441005008007523001444021425000010456400c2074650540e501100d011500c0015128904044083c114550716420076611903a00410001c0400b0042c4202a00c0c056a89102401400040e0004190201e481d60425840c080342d00c011503501c0e01d030740e0805101c0292400340d8403a01d84087c10022643c42840038982c080711851941314184c999070390b11040032042249692041000003044403400260103940e8020b5001a0307804d540c00340c80251215401150300c410302900000802c0d0100f46108100f02c1c4130240c418038584640c4503070b05c0a41c9014200014000c41d42d01c4070350800e41120782c59120000b401000355010354030120000d052070b003807414000e490303c608180c4100b1b40c1400c1d409000700300c00415206009501100c003405866101c00a0088901080c0314211081e4414a1020070914003058a0403441d40004d00329 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 571090665 1250 571089415 571089419
    0x7020f09040f02102a080c01090c060e030a0305040b18040c0903050c0901080a1e1e1b050901050409050a08030a0902210606040f021308010c0909141609 67
    0x80c0408106480481e40080354410b00021801d01e40c0c0000449103131800d151402c00d01100d406084001d8140f000c4c1c010f0f400340c8120b041003044220988030340e070707035010000c04c882549468042448603146c01000f0100e0b5400749071003c036240002c0c0340d90220358541d0350301e42010b1a22450101a401c05540c0e4000003039400c040d01e010b0b48861242040240031a501c141103a071441c107241341000341c81c61610340941b0a040040c041004006034032113469030b0040c004000d0940d83d0050414658800d8401031500c04080e052016005088141c40f415501542c41030090380400b1006900f030500a00c90701e508520644010000d07031500d079000300d451a00034000d5030110455990703a58a980c0c0f048444145c26580c0d45011800d50808125483c010101c00d803040d03500300000700e2802c0c1d6035003004245601c60364503429101003209841d01030b20311940d004200710f501c407a1142d10307d034040d01c4488c5800000801031040010340e444580122100d5800c01e680c003144680303850003036050030070f058003100013481a10540 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 571091915 1250 571090665 571090669
    0xf0c03070f06050a180b010605070f12030603140312070e01020c15040617010e0a1509090f02030f0c090c09060403080a030e060c09060d0c1803060203010f1a0a030207020f 75
    0x307000207551081000007030f5403404074001000c85d100e0f0740c040c45048459508800000d01405201070658641e41409a1143c1c0c2c5460314101c1c010315a40010911151500040030721074041d0003890903a40310305150f600031b54422507459564028425a620000124000301c0c4083c0c0c05842140c0980318184181c80343d0b6103602d00414400f20f1034101424101d0070000302007104950000c503010f40e0031003006440590303524100e0170400c00c40303003d0720031a11555996204c6c0c04031682400840000c0454910900c0030046070306100640d5140301006900901440e4282c0030300050120385003c116200511000070307621641466081a0050a442c0f500300c1d10420021000c6030304200904030601c60340d50f0126013076010365420b50609001400d1040280424131020400f944c4d0f440c00c0d10b90000c06000001984140a681124a0011441c101a815018003008420f106550f0002d5045c7d071a881c040c24101c99036402201444901c40948585001040c00136841241c440e4004100300350000b44600780c00754201300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 571093165 1250 571091915 571091933
    0x7081e130f0806010602010b0303040317090901170610051c0c030b0c04090c020a03050304030c06060e0c0a090806060303090607030e04110c0c0108040305041707030501020a020c150f0f0c0307 84
    0x180312a4036030302008110358202000804e0142c8040c2c8000d00c9902d4800303000c03e81d2070240b404010000c450420701c020b005502c1c1821f690f1054401400c0c0062945d58001d02005200c01c001a24420300450300062032404c3d55941d0b44c0c040316005080d039003081000150350203200300811000c54940703c00304d04c0080814400c4000b54060303003000301400d0f1781e5840c140102c411646004045400c1d5000451094042a0800706980e441034150a04000481c2c89180580041405402c444400c81100041c040303081541c8015203030344001c40d210600826219960240d84241c11125264580c2c02003041b10000e090800103820b9080c441d08120078480552030000b010344071101000c040795280883c40d28640c4204004000f00c811080c00d01050b6810a518001c010780b041c1d004041b00c1c41c500054448210f081044000e0041d60008004c648591035070000070f4807010309000b074070702c508030400d00106401c01c3c08007101c1041c500103640314540000c600f003c059540101c0b0400c52140410700000c3c0226180740 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 571094415 1250 571093165 571093169
    0xf1c080c0109061b0201060303050d02091207030804050406140f01141b16090c0915020f120702032e1802100306170a02010509060904290a060507081e13 67
    0x10105111311144406004401440644d1045a04009003000807a070001c084030301c60142c04001507a6aa8110041500c0d68071240207185c0074031510100000340051103000e08140c4074225010721a0b942c1d9450541c0e0129580141c8a40c030003203010400304a50301800c2200c12103607442c0d8205003480d07100101d220740c04000010920180c3c05c40c914a22400259844043c082c03c1114020059103908000041c0101100d019182c4030b400140c661051040c0200311400001150070304684180f41c00500c4150660420702049000e4420449040f90800e00c003540d46041c20110702d4607891b25400c05a44802402c80140da00202c50060b4481c04003517200c40700e021f0f40b00011502e010600300d16180c80c0d144403c0b903038041c601d400d4000180700401071b030b441400c171443c194045a0702c0b5259005000000c0041032000420384400341061b18030040300e000d205c2440b4508400f16012114559034090503101f62003640c9005011000c20401c100d40c06103803c003480c020300d0307500c81d40d141402c4094184400c080225 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 571095665 1250 571094415 571094423
    0x100905100507020906040912080903040f0902070c05030118150f02040b03070806190306051e070c20060906070609020402030903090a08071d0a0b1e040b0f1c080c0109 73
    0x6620056003414031800d0b0f0400006e880c20001201c00e0b844490390921040c1e420003c1000c02000b14007060820416100607000c0000411207160303440a4003002940f1190b4115021744d10001d00150750716040c130840416075069106d5180380c42c02507403011003012030881500700342956040d10200e48015071018102901c001c0514595034240004041c01c8100018255440341810000350400780c0307210038039481129032152002c070fa25210a1154540e0304c41c240c1080202c10355140070041026800801d94444071300441d03541c1d5005445104046154525012140e0440c5041203440e0080c00c21030024810107005a8002640207500e500041c160391059605080d941e00200c0d0b090641d18045038144014280d120003010000c0c5040700e0929034aa001404915061050001800940f09a00111940b0340e0007041c0c042001740ba82c550311405602d807180380380900e03d00144900b0505040030400703641c5800400c0540500051f401c90005041050021100303000144800c01c1024024081d6044036842 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 571096915 1250 571095665 571095667
    0x210f0307080a0b04110405010e0a0806040c2301020a0f0510050a0b0a0e01050306040201050a02070e04081c05131202070e0f0a0c0513030b06010507050d021c090806061009051005 78
    0x2061403400d0b43d00241400d4455440d05000484401e401011542241c0c402c0c02c00c282080445000940140240d9000300028081c03003042000304907500d0400c01c04d90b050350300100701d80c20410080c110110030721864039000d0b900041102c00441c0301d032111401014810402c0300c442c42c00b50341410742912400d4a0621010741c9031005140c0b207183c0020003502900c40f25849138800d614104c00642c0e01c41c005271000c0c0c1489400164020201d1003444403401030f00c004803419500b0700f407074580f0402503403010b0010019243c94160b03141d4026200d0181c98001e03100f00c0300740d1a004440d41c13100d48080d800d0b00200d01c1035118503c400181c401c04840301e070f0b10a410350004281d191030175920944c150384a1400c1041040004c0104000550802c0c000c1015281c1201103000305669000040c1c0b0300d481900c601801c00c0c031800c500815403641c002129242070324800103520089409403400d031a0b1241601070034078240c01c80c0c0002015400c1c10448402030003c00e1a1003480c1030381c0c03140492b840f2080106440c1c00294 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 571098165 1250 571096915 571096921
    0xe130f051b01021209010806212b1d10110f03070b01050303070c0b0d11030a0e0f0706051c0b18011409040c051e0405090705180405210f030708 63
    0xa01840f40c080540d15404c140361130649100002030644c4030043c1020f203d415000391003071000002908011000d120a0111444a6203c41980d0364080340300801d080b140c0402c071441c4540307600c0390007a200d172110451000200c1c0300301d9008004400401917140c5e02004031069035500950340030004903150511a40c05956148000e041001c0b4241058101034002d51041007141d001a503000f00d03a900720354424820356290790741e184100b03001c3c1200181402c080c41010041c402e20031000d0f0300c5000c0c2d0304441000c84802e2040c042400d034a0b0301d941d2103400c010030414403484010110b1802403529280407070000003003d0703120390000381184443c941d000001450040c014000c503804064110720007070080798010414a01a0b1340d41240050318011107000d103244c1581c50f501d00300d03c0100500d0f003c8004000707006171b103020fa20040e620100c0313209103407084d511840c6652101c1d280c0203645003e036400001a048001c101500c40d003d0307140524003441208410400388440104580107140039246c580c1d20703004241 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 571099415 1250 571098165 571098167
    0x50102011a1c03110a0b010509070206070e0d06090804150908031801050703020309090c30151c030203031b091f0e0310090317010e130f051b01 63
    0x105169140122069a9640c2004a0ba2070060380c0b002034038107106610000907145001c49100411600e00c22082c851502203000304052020441e042e600240d5036014155900c40d400c03030303403244142c2d032604c04112444a201c007582400080d0110f0980510b40119120065940f0b240103032348164841030b0102010161540c100d644000321a0040100d81c2c021410045001d080e210140c00b103607002410b0084c00681041054000d109030341c04c1c000010000e002d03034500b00708403684587c4070401d00740ac480f080d14480c0e0042074003401044130007a20b0144881a640c1c0b81d2030800c1c0300700b01030000e960344002c550740c003000300c4580f15100d01e404c0c2d807103907000d5522420b0464601000342c0c0d411804c4941400c050040213203c3c0c48031102100c90440982090382103584a040580d88aa4030001441c0c05010745420f00c000c426a9810213940c1030300c04c1da0780d01c124804203151220f803040280500000121004085148003d550404081460040206042d0420b60355101071070300926200c40720001c0001c00d94a1015 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 571100665 1250 571099415 571099421
    0x50915160e0a0303050a182312011e1515020715170a0c0315031b091503081c0204030b06090106091505070f05010203040812090109020a26060c0405010201 68
    0x9440c00e03149104075904584d4090001d001e18a07130b0340200f140c09480440320300040a1054020401d0000c12403103c0c0400110301001041c1c110200d00402c284010703005040300520031440428442e2080e981e408030700d00511405019140d8071360090560a802c04504088024601401d29116800800016160114007000c840c0480420003e1100c42c510403120b40b201041501d501840703412001030403845004c004d5008205140f046049014805004820841c407400c007520b403595404ac024076450741c0c80a101c000e0702d031a02d001440d201e440d548100700180390034003c2d00c04809100d05120441c0080c4003024100d07002076005480003a070406c1404200d04021038201d014140524140803034034204060780800c0013140c03100500b0007100090520a1090004283c515154850001d547c0e904040c10000c6154100b1401000c10b00c036004007240a4140500c40c90001e554007800f2000740c50301c0c294811b8941e040070f0b81d42d02071456030401140d24418050050b0f41c07117654540e1240751124140f100090031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 571101915 1250 571100665 571100687
    0x30724030b0d06021b0d02010c08060f06090108090a02130203010501080f0903180a0f030b0f091b0d0305070b04030815030106051e0105040305010204090501090b0301091505091516 79
    0x60524020407409a515003400900c51240c100101581e551412181c20b04001c040b40840b010030700030b40b0401c0c4941c17a4107400c001000c0056586582568a44c80108204d42e4030150b10b4541c800d0041218034501d5001c0c3c9402c03640200b4540c2940c92006464000c160001d104000032402c450340040180120b60b044004542c102d10122141040c070700e400200240d9902c40e041083c140e07408000325110041d40e5500d0000301410080201da11302030390301d2406130001c1c0c030f0070385a644520088a002031615a8006122010106080d403ca01010541400c3c4070301c40196460a60030040108290000304495003113440c0501c1c842c0d501c00400313160070f551a21482020002c072620a074104034040041707030313200d802e00c082804114501356800c414120043e60648540e50004200307500110b8005001005c550050f8100c0796009004c1c07000c1d14101080500300c64220000034114031050b811151000000d902550340200c0060443c2c140300f0340741c00020102c0c00c00b299660140c11043d040c2c2c8041550000740440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 571103165 1250 571101915 571101917
    0x1f09020a0e04060e040314031503030d0501050a0b030c0307050307050702060c0d090603020c060a0c0302070c0e07080a1413020301110d05041703130b1509070c021503061c02040b030724 81
    0x40e550805d60340042c038548603104050851100070010640fa2100c003400c21a19a400804072503032a020007411002401091280c40c2c410401d60200040b08804042264441c1d6900540940745544005040d07509400c0a05404200b05017884000016120007004001c0440d8030002828548080320300100300000c143c102c001014010f004420340d0400000f20250405c4c2207940224503107041d80340c02c074002c3c003503c28003034081b161480f0001041d102074034406020315210303075694005545000820742560441034040e4140f60740840000d154100c2c045401c1043c5200030000304041c0c40a142111668111303a0100b54415503501c24030080000554446641400c180c2009040d07140044030100c185050060161100c0c0d41000060443d1448109859201d84001e08508503410b1002c03000300740c001c504c0000c90240581c0c00000c6404480c2c001940d1040300001d2001d101011100c05c8000e5134900e01000b2a001034480000741d405a50078025040903001e840240545c821354480ca08003111000c0880c28 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 571104415 1250 571103165 571103189
    0x6072301020a0903030c020324010303030b150a030509100c02030c060610020c10120f0501050108060109140d030c06330f12020f0406150210050108061f09020a0e0406 73
    0x2d4070340e900650b07070b441100d400d801c00d00c640c1c41c041d0004c01d00f4130200030003112041017a410b03100c0c9022003150034031741030364040d41d000c10203521400c0900c29490300780355030301e0100700050204210b1140719400156000c1e032000242e41c1445545200c03e0159603905140001680000c40c81b001e80b800100704847e4016030440f04204a4001d8400c00380d1500c0361030b00c5141c081c20424003144107040c060004a0f02090014104109507000344645100615081c002c40e80040c003900081605ca41c400c10035034050b074065514407040c101a1008015401030300d59021802d11401d40300441c081142c511030a003003901080301c04065880c2101d140d481c030000740c5848103c045c0342031000380801709040c1d5409050b035505402c60340c102009400020481c000c94040b0961003410004003050141c06042200a0510280c003260107a904a00c810403da940034020010558480c00020b00e43c0c1125140c1130403140754030898a00c0301525900c00c1409d0f42d00c40c090000200d0b9120004541904061282e140200314602c6c0031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 571105665 1250 571104415 571104427
    0x40c06020c0d0b010308030c04030503041401120b1302091504080a11030303071b06090503130e091b0f0105130f05030d0e0108060112022a010e030906070605090c0607230102 76
    0xd911900300602016150080110015801ca19023000702c030055501320703003182d44650f90382801d50802c240080045000469404000403542d60501031039099a400606410521410004c07a0300290040660183d0094004015202c1107140c10020800f030320034080580401c540b41d00300b0890360400000f495000e58010020030030303090f074026076102540001d4401942103851b2401c1020190101800141c80b0303000004400003400e401c1301c110000c803522000c0801d92a0344200540d500c801c090041114a2850348082d85540d141c0001d02c03c0100105040042c14408100d11803440702c3c4240d00100d24500f0451400e004914040020030340c801c0040c42c1100c0d043c520760000800c2c4040c0903181c2410703c2065002110600318940580350a150040c40c0c90f8101c0085040c24243c44076401d01502031940b84c41c9000e003190001000b01c82d43c106000c0e21082c5072001d9680e480000b03201c01440040a40110398a403802542d0749001454014040c0158000c03c0811007014112410110104a1242e104002d1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 571106915 1250 571105665 571105673
    0x40504090b09070e220203150a02183715050703140910050c0109050115060e0d0203060c0705010209150d180c05040e0f010501060507120f0504050904030314040c06020c0d 75
    0x1554240008545d0015046101840401d1a2400308a120030340c1e154050200500550158040c204101d001000f81c00541c24400620071405040084489031b2021315244e45044040248030892041d8104004108141d460051103d80c0c25040c0020000840028564082c0b42c0c0c041c40c0561840090005180380907080000188100d401088150030b00c000461401c0c2000310070b51007405055000402030010380340030906100030701007500801001c10b10408240c00c1a091402c005032400790301a008241544800c1d0100724550082002210950b4003000042100c0c0c130345000b402c1580150250301c90b100c5480c607441406855880040100c04034945039a64045411031141804413a426180020b0840f1450721700740c1449401c2006507025820940001f42041c1e00c4801008014040d501139800c0c84c00b1180200c800c141c00c1402e000016402b40001d11041c03038618802600f1510030300300091420300b01d280002400404680a5600c42403031102006102d030140301030340740c00b00200d07410480088a03a40f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 571108165 1250 571106915 571106941
    0xe120f03061306053714131a0411070606030b18010507080c0c0c0a140907020304060903170c010f09050610050102030304110103060e04060516050c0a0b0408040504090b09070e 77
    0x3680c2401c692942440908040c98115405102d000101740280f5460700c0300180110002900c290f14010a0074141ca0111480d25101e10315101c0303210305004080c2224201000040d00c901e065a55030401c0c00c1000100048161003400300441c403404060b66103141c4100d03030b424a91140122440319904040400003080e0740b100c2000e03445081a4040707601c9040b29003006e031400b03517007031200f0360000740044011070500c1d07030300d514040050300446041c40c440d5500c50080382c0300d0095114450104a6828040c00010320244900c5112064001610f042c1440b0686003400d45d00780200b946415030b40e4420910a111081c0000d0ba80320b820114038141080c54800001d641c0e200085c80a1711010080c3c03100c81c01c80e8465080072004000300c80d03c2c0740c04c608203400c1070b00040c80c05650410030200401c00d4014094082c00580c2c84c044e4101003e00107170300c0c558070303100740300700c0000c2c000c83d0010708c00c1102040c1036072103106180c017060150012145078600300c18000c3c07a012158100c061924411010841c3c1c01e14503074 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 571109415 1250 571108165 571108189
    0xc05030a030c0912080405090a02070c0605030c07060614040b010201110d05090307080a2604020d1506051c0c0e0c160302150a0515010810090e120f0306130605 70
    0x301e07000030008507100c012120f8200a0700414840d2580c11807580601010101800648104544182d0746444d4808200c04910809100811484400f54101301e9540540069a4407102c1c10b801d0f117140c108156110300c200c5009030088140706a80e911958140e0400e845511241d400c280001c125148200310021002c0c080c0407449800d15495100103240f01c48140150307030290354000352060704d0300c3c100718000e0000302172800f050050400640d903c410107210f181d40d03240901d0700500111500f000c070362117184da07903968001002085c42d00c40b41c0c000340c02d854001586888202400d40d00d4003902e5103150844d0b10180590042da41100f410042c440e140c14420229501c0c160f0211050004095518043c0d080c10b00c3c2007001c69111704650200603904155400c014429901c1d020350f0b021154008005540d50602611119055107898505000c56400c6502501d407262240b41203c4410401c1c00d0502c10b19070140c0d1584603000c00100c10310215092040508981c0b200025060089604200c049441e5000345 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 571110665 1250 571109415 571109417
    0x30d05090610031e05100614011202030114090a0b0a0b090111030f0301140a090c09260c04051b0f0409060503030705031c140921121602071d070806010c05030a 70
    0x2004c01d60342002400c2280c8401788407038030828007032903035aa006e1004040721a420355000c5900380d400280d921940c1e00c01c4034140e03010f59100038820602c000a0009010300180303146140340d174a182510041d9580481070740182000041a982c7e4403922000420700005103081c90300c0c0368414001c4201d40c02e000d2041c0c9054030749100d80b5070b1107003c6445c00500300030440e501c00c010491a080c1d04a0030750707510980b07420230b50340303081e00311a4001544400083c0300341c01c0c2004d50050303400000c9414010b240507003084c0e400980c0740684003020100d6030b512031600c0d072005030340fa209281c00180030414912203001d0754000385412005981004840e0302d40c292240304071283c0000e52a0f0902060b03400488a51000c0070a280d024050411850104201a600c1c080c40d800440c400144078030282070811414100d8000811041c0c0d00804d40d04e601c3c0e1000c4601104e5000030f000d602840801103040750001280840302500003040c00000d007401c4e8400f60030000b01034000d85c1008030006e00800403074000001c8a81d02181 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 571111915 1250 571110665 571110713
    0x5010207030b0403021219030b0a271112060307060807080f09030d06090903020c03010501180e07050d120f0c031e03060305010204080a0b150a0e0703020c030d0509061003 75
    0x640d04e0100d05001440e0407030742d90b214010404202c52200342400c02820541c54500b006840f039101c3c200664801c803440340310f01c4400c550b450300c0d02c100071094101206207440303c804a424030b042d21400c0001d40211b15102d400d6000301d82008942d1900b004030720020040b505282c3c81b039050550005120540081010310310030784903c049481d9040800484d02c1c0d007440d18104108094460b1241805440031010a0f00144650f42c1306018514061055a04a0b0b6110036000c075001c82a460b07407400341451805001150056450000d15501c85403000c6071480d105009900401c540040b01034040d06448541c401003200001007c40040d030411a26480307240122400441c142841e01b00324054201504000c040d035001080003d6110000036070512268030400e8078041c1c42e503410480703051018007000c600e45c0c8400320050400c01d40c0480c452003600040d86140140c070b010080c0a1040c40c6600140c0e00081e03940c3d5440801c11a1081440300c1c2c1d810900f00d0702c80c00e8059103181ca0300b5010702e042000581e46100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 571113165 1250 571111915 571111921
    0xf0c0906111612061506020304090e0106051008041401020403150207020f0d081305090c040e060109271d1e0c040911030d0c0302120703050d020304050a020f010905010207030b 77
    0x24041041c480035803030068820a4040d2100e24400c00d070f07012108100c40c078508000201103600d041c41c205000780c03921036009605003881c01c6d04020161452440401d1203550b50b070004110307031b1a1602030400740c04958480300b049080620740304008401001440004da44180400d00015001010030862000341500260b1210034600004002c030074441e2005502038001c66846013005012001303081c07203210070680e20040075643c4062040c905e6040311410124841004103100130740c540030b000d50b003040d0185088058152603482c003200700c01d903e00c045140243c9100c50000105854080c217400c612a9000500c0d0500e4038141c5070380c0d680d55a01c100d01400c1e00075494400f115004010b10071648500500a0200959500b0410b8680d00081c01c050b0090150740704281005014501e094140341d4141d00624400c480c01c840c42189400c440c100b1000c0107070800003580840f129001840c021802070001e41200b00c0141304205001c0401c1c007906040c880c141008204a07030b004280d05003165040009181256 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 571114415 1250 571113165 571113197
    0x30c0310051201240b160809030619110906090f01120c031409030903070b0a0c021003020d0f0506030c061e120412031a0f010c02220f0c0906 62
    0x829250461500b214001400c03035038100c015000850552100f94495499045440c140000034216010740102c520040000403800400c1c150502e5480780a46801810081c1c0038000a05144040c1c80e80b07128901c07142140c6141c581e0b00c1c81852000c0784600c500f80d10300158100810102e01558000270700c15040c00c0320100c2c0590148121070440d40848008024114000354098002d0000c900c11090050f009800171f407441400004403549180c000f8002d02c0c0180c94010b1401d01a03000761904c9041201c203c880d0401a140e210304460380420549026840b068070705d660404485002e00303000d15541c1440d052108a48010919080c0f03450181c4901da035601b02840d0003400c250802000c502d502c1c00c00039110940391501c2c1c0b01075010b2071080092280100e60a07c00318195070416079810380180743c00c0d6142d01207103000c0c23800041c1c84106040c026540714881d00083c8540b418044030f03861180392603c0380d181c11004c078410b201132011046e808101b845103a01008100288901843c4140301c98100c04074118 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 571115665 1250 571114415 571114441
    0xa09060e1207060302130b07020904300809010e06190f0204120803090601060201051009230412020f01110a080606070803011409060303120606030c040906090203160c08030c03 77
    0x645000c00071503002e43e96400000300207500101e04000516054400844c1c2000d41c002101c500075002481204503441e180c5610444004440b1500b1643c5500110403c5c407101e010b0342218441d2141c0c803401e407940340c0605000d096512081810f14150801010007103c84441d904010108000701c1001400c1c07107403030704210024481d6801854214908541007000c01c40301748001c601c280380c44015280d059984810a03404c0c2e0f0400c2e208100c119050103410301900000d40d01103410000c03103214403405966811210300c00000b080d81d090ba101d030400080403054540403c003800c2d040640340020041daa0b42450102e209014905001041118220208041d90b480e0b500351030b101034200c29400d41c2c03565a04035210010084104060003401640c00080e200d01e80482070b151204400c2c0100b01541d50b0302010840c00f68001001056000401d000200315018070f4880c4a0141c24409001607403070402c40c6c06100b01120070140d0760200305101000000141c140c0c01900d8020018000280d100d45504424220f4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 571116915 1250 571115665 571115689
    0x60d140c03070f061106070c060c030f0c0903060b030c1f11030a020c030c1c14010f0906090b0a02190806030a1e0b0114180c1e04090c03020a09060e 65
    0x8144500080820f6540f0b418003000c2c11900c082d201c0c50350381d500d4016110f880e11400c46890000ca8240c8160601103000c5402c00d400100780342c540000e1030000e0420040484076800240800514941024400c0212602c0355020f0210114000d0130207003401d100041d110500c2c05121138143c01400d29001d412406500944600201705060b00d03102c5c110340000035600d030b040d403040c3c921034451480342d00303264201140c100c1c1046c4459041040000300ca9200d2070340103004401c0d015000d660741c101c0240403806510441c4e41080c40f402000c81d420711103080c8800c45403c00380c03020503103520410101c0300708000c50305a40540e6080d420b10344551b0781c82100185c10180b01180280c1a07480c0c0650b00100c0310358840d07818000720300c41c1e200a130959899405012a00960205268100c80100d6200300340c0706ca01441150301c0406030350020f160152900840d100f0f01605030105e603040e47c010038144040e80090040034003800181ca011818064000c60081000c41640300310405d1101204210445444401920035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 571118165 1250 571116915 571116919
    0x16060b03070b0a110d0c02060a030b010c062405100e2404031515030b1306090212010e0d0f0e0d0f1703010f0e01140114040e0f04120305060d140c 64
    0x1d1110345508010f01480c01c4c181c2c0c048a54007400100044060044421410340e940141550b8103000c1c104d2829001003401039030a074140b20010b802c00000803034502440000205a00d01012030314901404002c010b900ca40001d4400e416a509000d4059405400d442062404561029403201698000c15911891440b81c0c0c0303e68400040210511040756201c00f0326401e02e03101041104104001c04010442d64000280804401d10101c0c0c070303441c40c016540c902580584000980300f0910750015205c4460f20301440c0349a51a44a1410403075002d001c40d5404668500388006913211140e00100400b4900c6c1c2d46610400385103400f14144903030600c443c40034582c0003103541c07c0e410700300482c000607800901c5405508540b01001185081c140007069040702c08004416440b0944d980064449400322803140e00340070340c1840000b4025032000d0880d4002c402405070304d50702e4200341c00c0170307101200980e11040c00c1c0360411b0140704c199150702030b05095141d0058200d000b200c0002c42154240010840459 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 571119415 1250 571118165 571118167
    0x305030d05060f060a02120a0203040f0e01140904050606040f0b09040303061e0612091103070f03110402040602030306040c050c01060b0318010507050a0302090a031e1101020316060b03070b 83
    0x1035404240e4002401084200d811680e050114070400050b0b02c60036a03000016007016900d2454415903801030121484a0b0045c2d038101a214003216200e40c10952002425610300801048210f8610b103441c042c000e001d4640c2445450140c0b941c0d959070074060540c502446e81da83c13a00441c0c02065009108507075004080391040c2c00d00c2e04006020f4600c038081c0b401410041c030714200d21940545007002c11661240c039000010700c90074400c4c800030311700d03848180c404040009101c0c13039680d024412600500000e000280d980c0d811401d200006081608581d4002c91040006200b5103400000340e036070180c000c441c0445c4c180d90841046030940a0201040070541c00c1050214025901101031885803100d40018141c100030310001d6426141f05540000c0030601c100812032099100e90001c14900b80c018240c0750103955266100300c4078102c880100f01800e450710a14004002c1280b406a403051001d100840c02d0030705281c01100c0b41d01d003480e0000e15440d40c2c2c0d0203414458809112000081582c0d48070344e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 571120665 1250 571119415 571119427
    0xf0a0207050406120b01050306060319110d0b2d04060f060503031b01150501080f09121206040c02070e0619032001120c0801030b0a021c0b0a050301020f0f13030503 72
    0x209003402d01320b60007240c0c0b01e00c1c0000007040b41d00f0000b940d2840f42c1002001450000610140c0340703140c80290000b500c03101c491485035803098480301241c00480d031003801342207100e140114900d503081c001074107102003448010310083d4041e04201d01c03003034015030400000600444100c268400409455000e65014040492051003000d02d815540782c00480c901c00038488410b0781c4c061641c0380645c0f801441d01050210000c10000c0483c00310f02507120105604484140f030207600e402c105a001041c001548086d00010000310b414280038889840501d80010100c080c103041c4002102d040080800d8026810b204131283c1a0500d10050402142c00001c0c81e884c2c0c3c04045c500c503007502e00c041c4810f404180c450450360003201e00c510880040400c0d40d40c0310f010b43d0342955a00f00c4414006040c80c3c251070340034008483c455840c045002c00501900c0000500d904581701413000c402400c0d48031511030303403041c06a100381010920840301e20061080000313540d090058040d8134060002d400140180c403010400c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 571121915 1250 571120665 571120679
    0x1180207061e0c05040b030103030f05130312090503060f06010f0e06030903070b01051021020918010e01170705120a080d0509011a0102030720061201090b030109080f0a0207050406 79
    0x2d90910108490301404214a0400d00343d07414810383c4100040044100010030100f4410842d0714901241c0740b400e1882c00e54500f845502e04035850300255800044010245644c58000361040e0081000350040c080b60301d050602007440c0a0001c00e080c0c1400701c1071170300090301f83c840c07007c0080d8000700502880d12400c183c040d081d5642c012110840d4011040400031410f4a0b005001135841c2a11399a803d0050610700130340300c41120340c5600c01c182c203502440881d42d659918504403420800c0301c542d8801c40d600d001190820744070180e000003510240500c20031030042d8085010402d8510540e205008030045c000c040d40340c904c007414050714661000c203c950803402c1360380201d4003403000e5400a100c840440305494602040748801a405a84100205000590481c1d500200c0c5440610b0300340402180e400450075640c44004501e1503c40d840005000c120011f2207410200001503008212811244d5980101c51148005001c09180c000c11164643d42c07080003400701524001d00184190395075015 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 571123165 1250 571121915 571121951
    0x1812060506040f020f030103030e011e0305091501060219020613080d090b34020a140111071409041407032d0308060d0503041a040e09060103020303030118020706 71
    0x103a0a11543c20000414940e04550094a01d0541d090400301c0c516441e55805481c40010104114140003810801100b007240b41441002280b09a8a0104261030402055402d014554000c00d400c00180c0713006010003580050880300580401ca000340c0b5001d2503000060141c080c074445c500080c0310080004c580000003050140e185d50790380d11540040c0762100031001d0741d03020740019403c1083c20800240b00260445940381c81800404288800b0910603401040f003070071140e0401109003003107817420801960b0003080074075081102c0c40503003003141c00e116612076412203003510a88902c0008010905011700a1a0044503003021002c44821550360700c1c1692070101c41c145c0700154194544403030030054001640c0c00e000d10342d0543da11100366840c4000c100c0c0c0383d1480303e0141c402e03100600000c5030301020320b0300411a07420681505c81c1c54a141c04581010032400400801040e00a600100011389001003070b80d041d180d20019886c101d59481c001d60000307004685020304040d003814203040c05101404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 571124415 1250 571123165 571123171
    0x41808040f0302032a040507030b0909031c06030213020c10090c09050c0c0c1002031c0f050612100b010e0d032307020303040e100506040305011401091b18120605 71
    0x3505a17403020b20400c07000103d0014511001c2d034842c45000c840c60302460036070300c03c1e07600c00424107000648030b80c01008605888022900390185a00004650407900543c4039a00a080d006481c03d000380c0e429680403451890302c40c0014281190049024103aa040500020002c000c1c0c00c0420009c80d2400d0505c8000f07c45544a040354142c604000b00385100c101404568078404220020b04000c501c0106010303c040500072182c04602003405031410055424211301c035100b04103200801e20036a00d680340c800b220000f8281f9442032901006580c4500e40c04070700001046048a00003550310000001603810890455004d03a00c242518031584c1010740040707000400f6040203022804003c000700602c2c19602ca210800307903056009000412004120749452944400c400c1a82c00e0800e40d2200814229009900111010b0351200b403265910b0407049000c07401091140c206000b50b0016040700040303154403041c04010000d1040001e845528100c403540014000c41d204003641211500704039005000607 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 571125665 1250 571124415 571124419
    0x10303031104120b0603070b0a09090b1c140703060903080412030c05090613050901030819090311060d0b03030d060801050c0301030c0e130606171911041808040f0302 73
    0x54000981c1c24035a00b520151151a2405100e490568031a04a000c078020081e981c58418403401095050b81140500040c03080c5440b0b110704d01d070400701e4800c00d0300c1c0803595240c0119114103204244903207c20380185002d400c403098864142d5440000c1e820040d030f640018000c0b80c103002114080680c0944240c0c40b441c09007040f00c2c00c605a24800b202510400540380d0001a01404540aa45402c20040c1030410000d03030b50740c1407195144049101448240c0c02668000b0003c140840c01c07003031069192500385101e2402d402040c0c1503640d2405421440c1010300c2c0038490100380345040982990200c845040010100c85c0c40b112814581401780003a402000300c15428440894040002d68007541c1c140c2e035101110304451400d00000f09a03800e0300510b880c002000c100991004071315140b086102400195450307602c285102031031945407203070004108403000c00e003245d0100450040100040c0041c1c1c2140c0c04505098450030540e017510b0310780c0001d0604400000d0010301339444a018001b101d00c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 571126915 1250 571125665 571125671
    0x60f0c09040c0c031701060504300506010501020607031407030c020c030a06050a0b150901030b190b0a0f020c010c060f020702091e1b1207260106120e151015050301030303 75
    0x400000c084e03003005c02e100c1d51010900610013071082c01000c050110b0082c081800e00d0b103003000d640851881d00b502544082e6200c1d003113840148001c4d681131092903030011060500f44010307071060000940c10400149088101039035440e20064180c424072459501c158000c0807224010354605225004010075686e0303c0700f440c6030002c4c403010340c06d015001c085180c01509040b402c022a8030010340c090108031980e10340c0030201032540c03c144940310314144041d0a441d02d104d52a0000150003070a010f04c28941704096601c50190031801e0782e8002c50340124954000e00109829107580c841801038028824002d502403020300c20004480500040c0b0655800d00c0c2c091f56030240c4422003034880807004400000d0360704504100d400c03c40c600072515290455940e1038080c01c0080300800301800c4102d0220540c81c8045008010000e441d805402540c40d03d0309038000704683d10015001d02e54489080c500c03010070302c02d10030000e0344040e81e03210007200400140c034950203025007d00c0d0050565000740001c82c0401e01d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 571128165 1250 571126915 571126937
    0x18070807031b0203040311040e0316030e220c0302090d03020c04050c161b031e020a08071214120f03010608010f12030c11062208060405060f0c09040c0c03 68
    0x44810684a0662540146180c0b0381180c171412601048044404e401c103403609d111100a603030070001008601e110001062710208907250080c40c8400840d803c510404034030301c18102c0040a280c64911b45c10007000006040e15191105a000e0b000314054036512549100c551001c1c99004200c040c0d0301c1c001210100216594070080c4c1c001170190700440c0a07080c6003d10f20000180300c0d075070001d40c18082c8107240300b041b680c0c3c6c1d6203002e03a80242000103842212070420040c00c504201040c5c5000d0a4440e000d003080c42d060603505007404441d4540a0b0844146500c142c01e148003c0c4192052a00f06429260740c9011003420300c4420b90083c441e080c0041c800100028540115251040c1560003603e050451140749850480b034880c20304600b5901c0e00f82c4420400301c55500e01c002024010801f003003542e03002e80071a0031190b81082c00d50054a55400080030840060004104240d000901101d41195030301c07040c0c1221200c1c0035a032a103542081c600f030780b08008250002580603015100e9520009050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 571129415 1250 571128165 571128191
    0x70803062e172a0f042303060a06030308132301051b0c0d120216050714030c0f22090602130b0705060106031e0f020430111807080703 59
    0x2c0045040001e00146120740550f100c881e0092200d4513064940724242615140481311450311588090f48100c0c046546564506040c001254000d01c01d64040102520b10386010f0003000e0020060860990640c0ca06800c011144008840d88443e40b104070310200c2156142500030302d003d440b1100380c609001c4c445601c59648a04a41e002c617019000f5100c48902420140c41d504c0010700101040c64092200030030141d5208100242e11707002e070b001440348a2500e0f004803800b1046603011340c001d80001da103e0710a9100c0107a03450b500a000e0b07036160111020350180c25100303501c005000d045541800203840070b004060300500380492820240c030003da552980c400b0b40074419650001e110390007038001000080d01070b0f802001140284100501d842034100441d004896840c40b0400038564003107000e002d042982d5540070308581d41a40e403d9049100b5203410300c4501041040103091421681c9043c0c00c548403811494004480404414140d0410100260801e17030300704c42001c00280380c0800d1026407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 571130665 1250 571129415 571129441
    0x30a0515120c01030f0b0919060f0501140306060c1e06061002151504180b01090e101e05070309020909073b09030d0b0303070803062e17 60
    0x103408070341e0041c050030003900010350103001d1046440300c00030b695580e000030644901414603c15042415018088a60041c5020840f18207821080755400000000d00c0580d802282d0107407014421510180c0303079070312880090071a120380c0f144010030740500038501c1030103424404a02c40d0880d402c81651002d507695000c0c0545140e20004190050b44540d541c4012000c10383d010300e03000004046103120fa180b204020a003035a40c1c0c402c210b01c000c241c100f01a0107104003409480e001d018500003e01440c11030f800c106c0c2d500d07182c800c21704021036900c0303901075122140d40b03100c61840011034105110070b190003000640103018440d0144d0160201e00005464442c0c0400c0340390039102a40c45205080d00c0740c43c07a40425000700c400b0b1b58402c85420100c0260400c940c110f040c49541c0002c029640ca0281c0c29000c0142c5006102243c002c0c2d01c18030415002650b801c0c1503961115007a500c500d000240c0090f807850200250301d15020302c044e005c540e903000962114900d500c06030a0043e6010684442000d0f08407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 571131915 1250 571130665 571130689
    0x6110f032b06031205130b090a0e190f020307110a031e090f1e1502030a121409010209010e0609100513030b01080115080d0801090e01090602030a0515 66
    0x428220146901c0202440701d0500c010425a100000b1115283e07603130034580c4144403d6010100f00082107071200c941d182c404a1024044451400f802d10700c00c040070a042d1000d070300a0b0303000c00030150005084c82440345076102e83c20004041c2030202036110104100254402d0700c8450000b40700800206c50440002510103010350301d641d40c4d00640e023a200788103480368401a080410441032020008900b0f40240341070025105030444401c039190303801c070700310445031051f03203d050304000c4024008031007900441920280c7d042c50810f091829042e40c000d1006000004800c1080f180450900c11144015405081e5180081c0ca4080102d503844080021034000c15070100d9100c10311081003c50b0307070b119402814002c900100c03030f8030402c1d42707a642d001010002600034420030b03991208449094001e2244190080550001070a04c11421040080090760140950600c0d552a01b95012038400250f011851240d00f1082c05c541700d0401001e5100039000c1682d0182c84806031044520503442c0000300006 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 571133165 1250 571131915 571131937
    0x2130902030411060d0b130509300f090d0b07030b0d020307052704030f1e020c01030b0a0801090f11042c0a06090f0c0f08030f091201020406110f03 65
    0x68400c06000400503240c1c0140d40410300251984058038107a00d402001f200381c00304a42000c265072402501651030318140c0207106018080070600c51082c025282c0740c1c426115400011b1a40c0e502051346910030380d2042400362500f1001c009c6e03218003400445d150b214001c4840b5502841040344100c20059030220f2840d020350f00d9044500100150701d404c010540380f03129040d0f092070406007041c500c080f003103c04540c140c0c00704580d141c4c40c0300141d0b070141c020500412421480fa100255619009584014900340740b410300d0707621580701c1100d43e100d1104000070542c0b00002d1141d00303024902601000c0e404d0310200c80301c000d0821003035003030302e068010b000e40280040e80e01904001c0181d075145500d800d5000035200c500031903d15401103a80d1340580120140910300c030480e030500c01e140004805502c0c3d13001000d03110860f101401810008411941d01050442c2d0a0f602e40150400003051401d00d03480000c1c0540c4002000141980c000704c0040c0c15003504400d44824024600205481e8070a42d003a4070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 571134415 1250 571133165 571133183
    0x9030d0e061509040f061404030e0319020f03160f0e0c0408060f1f0e0f0603010c020c270a0b01090902070206070f050c030d05090f0a05090f04031b06021309020304 72
    0x609141440c59443d0744c0240100d034280440100783d00c420040b01c0e26072036007a0300340000b4810001496041919064005801c1d801480c005941114080c140b0019540003881007106001c1005035070340030420008000c40703ca06452a299072242c0114a41d8a00e01c1010580d202030030020751200403120941c0c088800003009880c4d29074980c0407030309000d14010301102010000018841d80c03103d800c10705502502c0b40d2002c40c61181000014041c91203c0100018440da0500b000d42c2461907001c1602c10420406840610400b40c1800000c4640410b50007052150702499040084540d02a005030703400f00030a03200c1c003940700d40350302c0018164400c41801940101c801c000100000d408900b00542c0d440c020b0050b903c400d0300d00c1000905000a0420071000900c000c01c035003507289800d260b140d89200c0100c4203640e42e00e00d0000411412500209900d1641150390006030600d4000c0c00410742041504001c0e0150b000c4915095000b500940350502c448542d030340300899041480e100300c038003403a0420a41 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 571135665 1250 571134415 571134451
    0x90b0603130b1803070305040501090e1b0c100203161e090b0703090b12150303120a050421050d060b180d060b150403110105040e07110106030b09030d0e06 68
    0x2d600c2c0e0510240c928000b10424992075640382400307001406a03503119a0700c0681e5180360030001440005540c1020904e0f81241c002c1c40500040b21070301d0b5542908440180340c640c502200242c1c10500c0026a0b002510300003c01c014003c40b41d0b00517403408556645402020703941ca0040040d80d4407800c50180046400d94400380b150643c1c00340540140751091806410f0b44c0d4988130a00b1503a00041070035075903c81e02400b071040c04e1086580303103d04520240c0040d41000441c0c81002c41c0c09801818484425030380300041010300c4208858038200f0200e52605601c83d4011060040156000d501b804503031a18020010522180700c0044886010012005000700c1c41c665040080c0741c010000e0481e94a9907441e0300505a0f1294490114003a00e503050130b076155072440c08d0024210071303900b544030b0402a0401081c003050040030003031303500196245002d84c046203c0e80102030040c0ac060300302814020860b4208007203a94000b00621000000f011b0030300c800b454514030580e4030a01a50b51000081c107140c80 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 571136915 1250 571135665 571135673
    0x7170706110316060f0b040b010507060b0d060e0312060604030f1b03050106120302010b1807050c0a06090609030219020a0501051c020310030218130b130219090b060313 74
    0x14a12030407081406481c9071002d0b40c011200c3c05090f0301c2d411607450351580032000d402c3c6201d01c100c0003514400e0b113051014118040000742284120b01e0010000c40e40c0340c40103015921070845810125900c2441007102c514a116440d5070380d00101d0f00c1e85140054840020300b0782c1040c0084c2e504403070b403181d800650310381c4c2581d40700b54260000c040c2c883d6410006c00c002010072402d004000007800c607a04030b046000d40d0780c10000c2c02d54990340c0c03459000b0480c84900c900342d900b86004403584500d03a864841e07150308c945054241012000074003c1e01c03242c01e14840c02c06001c92644a028410303c2a004c076000c803518804503944c4003050702c038003039880403061208219a5009070000d107205007250420210848007000d80f1030490b0425142112101c0c17190310140114100b411402c0001404c0941ca14014036004014411a03681c0600041ca40d11044000c280c0c07075005000c0c2401110790040180809440e00d0034050200ba00600c200c0c032406040c00301e41d140c0d0703043c84411203010701c403002c82c0e10305482410340f2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 571138165 1250 571136915 571136927
    0x50907050c1e161e08031317120a081806060a0e0705220e0f100303033b0d030c0507121b060203040c0b040b16060204090603080301050307170706 64
    0x590b680035010300c506040b0b42689690300908081200101c80f00440c1c10310003094061034003d000d40c2c0e441041031144840e8114030b44400c560751101c44070310092041e001c09050003544181d0889510002ca01c090034160000c0c00c2b184a1641c0b85000341031003d034014030036501d071019601d494003c00301d640c00303200c22001e250440b5440045401c100b440c103411a00c01030790003074080c140006244030f42c500034001180004e4042e9008203103101480b4040c10071030060a83c400e020710008040c03651300c802c0107400c1500d81291800c42108820402c14049040c0300c0d14410056454405803140510b0628107019070083c402c0310b10742c1c081030799140e003010380303d68845c400481042c4002082c0300c030100d1500101d50f120583c880c000e901c40d6001503120300381803030008000c51890700001c9036000284000d0000d00704031f0b002e4400d5400005002c80300c1000d2400c21200034800c980180340d819040070404001c1c0000e0000940c1242d4095003144c4000381c2c1d400c21450940020302c02011140c01c050f00c2001110720400e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 571139415 1250 571138165 571138213
    0x80a060c2a11120318040b090405060c070218070806010207091b0806150a120509070b1c060e09030c0708010605060f030a272907031a031204050907050c 67
    0xf0300000c12054409008a2568000d00141000b072022404403c0c5207041c680101c10014000761600303501707801c243da100368580d000101403100e21100400e440040d55501c03481c045480c03286103180c0c0c20074100810024204981103800501510801000240d510400d01c03c0800c845031681609426101c40201100c0b0a0b0000d014194001c602414101d01c544042008010340499515200c001407001e4080109441008010185680002d04100005000402100c1c5280c18101080e0900100381c0c0b900c40050001343c00c0180708002d070070104520003030004010820f450b4003d0489401c03d40e100c18032800c1c1c03426805019000740080c08240000035480d400781d600403000143c08070b4405110100398410700c0f50244ca07072000742c0b40c3d0200f440a005806078841c04002c44c0408a0307071210440c455000650030050a0740e800c042d0342e0041810020307842d40a1803501b00005003503030034001c0001c04e14170081d081401100d101c0c06a90004c210154014002c403083c0c1880100603054003061803270440d04000310702d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 571140665 1250 571139415 571139419
    0xb0a0201110307090e090607082d07050301090f0203100306020a1101090f06050a05070e0f032d0f07080a08070807060e0610050d1a0709080a060c2a11 66
    0xc0c518605401c01d410051403090120355203100e05180342c22841743caa410301402e19201034002ca010b114080d42d00c04402c2d640714030f4a04610150b00c41015100d001000b402c6c10845110013600b09024010307601c4030046048a880960522080e01c0c403120103002c0f48819503000e0072905114101f01300049007900a07015091843c10400c00084040c110142900c00c090012140f200000c01100c04014081c407030b540d0842c4007480300b000b0034a010034029004040720707000710344a020304c100032000d15603007081350510707400049900222070381507881e10f606011104c440c0e48200b4062100c440c03043d018006281412100914010308110605456500195010000980d24203408100c8400800c1980c018078440c031a148004100900d8400701e10071a840c2c040e0015442004a1211a404212445031140204035482d032824116204d10f5030070f80360011039520442d658042d1420001c103101c8030360700c113070705c188a551608003104008000c9101d80300060102d0411489071041950302103040000c18400401c40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 571141915 1250 571140665 571140671
    0xa020a0b0403200d0f03020702240c0d030905101506080702031b100507021b0f06091f0801050108070f2708071406070f140a0b0a0507081b040b0a0201 66
    0x305000c50110000c0f460744401c180d21000d0458000ea030b0004460580324000d140c00c50501c100c0380d00080c00b01c91045005144151030205028440260108858091101c2c00445910307400c0703001d000e4060b00b09030509413503070301440d12680350307031101c0f8011034441410815203003255a0030700209980c81c15015107500c00310f00c414003246c0c51241e2454000980d04020b0002090080845056542912802050202103400841c1c0b500205c980e4001540c03c00302046800070200301402000ca416070040c141c0c042c1d480074903404481c0c1080c0098002e90303120041b82d55403d501d43c0e21040151045401540e1140004210030543c6036183e01c283d4480201ca855403820300c12564000031400c50703400d030640108807680c000010400c1a41d140c55140101703041e040d00c149003800090348400003802c0a642c009441000000446013066009001e540c9000791300100d080e0039402c1c80c11110000b44404c98107000440c03201c074042410b0b00103070307140840d60500b1710040380c0c906424100340fa4066046140341c8000c3d507407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 571143165 1250 571141915 571141937
    0x702120118080301030209090f0d030c14071b0902180d0609050a05010219030b0f191205030307120519110f030103080a1404030803010e0c04050d0f060506060a020a0b0403 75
    0x40750304100c00c0400c2c0100d003515161350560040194908010307001d01d00c1039010f400d20034507050700490703c420203181134100007454041082e001d80310071210208245103d4000107000040041e694990140313410804070751846651101503e4049104510001d26800c4038070710440728501c1d2410b14020040d2207041c0202d01c46040703030340300d601d4800490011550360f5000720707803501001481160000d41c4485032505215155500d00414032054101c1040c0b4050343c01501ca400c6141e0401c04840c0003032407030760414181450345080a60b01c941060369031a001030856035004c00c5205a0b40119405403040f140c1d005141105d14500f04010103806446d80c0740d0076401e00042c569024000c1c0594004c50242c2d011550b5182e01d40e90003000250405203103880110140310510202303034220203990540e5101410840c05445541501c8150701442d0700155018202c55060b01c10071541c0071801c160240b05010600003511018100701442c0603503120b080060f0f01000420001c10030f0351420a400c40d00074281029244 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 571144415 1250 571143165 571143191
    0x3030c03190c2d17091c0f090617060f1c0503040512161502100911030c0405011404090f02030a0c03050f010510090504112206090204030807021201 65
    0x194000c070702c180110350401881910003d403083d4200c00725004410309041890380300030150410314203900d03101d804c41900d0b00141e02070100300b00d100c402c040c010b002c5007501c1c1901c40f001000c82240706a498001000b004000410782e014000078080d00980038600d440070f5403201c05011b405403560801075400387c51a0350008107843d200c254880010302400142d6a51400d043c00d01c004080345030060305003944804903548005807681032042c1501c02c0e07a03c441c8a81c4400700002c034034142c4049644002079142403846410406031480e845a1401e0a500351060718541104000484009108412a08c08055205907003860540c1c080c81d030b91441020031205603042900440c0c40d000001408031111280060240103100041001e02c254044010007444203180054a215850101e1310450440540702d0010604200d0042a041c0001070040c250103900f40301d440c0888114222b040c1060342843c5444000316030514035008039019a90410b42180c41c140950f400c3c1310018003c080802501d542c0d0311315a004a0f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 571145665 1250 571144415 571144421
    0xa0e04060e2e09020a140915150307090308030a09060b1e10050d05010f0303090b0705030711031c09051c050c15070b0a09120503090d081e1602190503030c0319 70
    0x2400d04021b0192015841000348600c401c405004000f100c516018507290a5513900f03181c00615404c0c0c14038640700c1d150340d041a1401016500010b14401001c410011519003a038001040d06000d00701c10b00c003074690103040c40100c9502c0340409680004079401c40e040d60501600201300b4449924095244c10b40341146c0c081100c40a070020101807040510400034140e00c080c42c680900f0070041c009280010b16940e0958034440c03e80001c0c0307002441d890303010580d9814451480100d5130072103104942840c56800605040c0303680a1036215010000904c03982011242d0f40b03066050307100e0002c110f41c5214000f0014402c810510f6080c04003410032441d03000801020b0003c0c0903115010303000c038061149203045800384d030f0030102e55000c00c02d0170700402c03d08503070004101d000d5421a0802c03043c0c6840d102d40704030510703000c481c2a6a0303654040b07051000b608030301d40071010000380030b40c2038410300f0b1081d07031318a80c0c150b4264001070680e1340140003089026070008000e540008c00265091600c40c05198040f0903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 571146915 1250 571145665 571145669
    0x12050304030204240302090c04030f061407020708060a050a02071403070204050a1b03050601031503050c090f040506190b040603060207020a0e010b16020402090a0e04060e2e09020a 79
    0x52608041410402c60400c1d0090310348900201c3c00d0340c0d07049050715803412018009407101a20880a040200340081e1111080b40c2c0a10341080e1940c408050702d04111001e0465032804801e11641100002c00d420302c0030540e0425612080094041034036100d003200c001c2c2001070040021150f0030009500095070841c0c2c00260241640b001e0341d2556031500412085481c01812040b0040c180801c08040244800041304204402d05000030b058070341030012002401100c0d040340000205000100034041c0016554600e50030440303814880390703100c10210000c50420746004000e0b9003c500450900403031451403520600300f00c0710016a509491000605894007603009480e095030000700c04003982071592118014180c8409032410310351501015258074030071003030005000d0000d050903104540e034070b80403035455800050a41c00300c87c0d00c03407207142c58242e8156401c444080c076017803a100d09504046400e002283d078450240d00805a07d004403482c0000c1c0055689143e0b03907a421810060f6078403100240 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 571148165 1250 571146915 571146923
    0x10e121e030709031a0c0a0c05210c12070206040e1902070b1f2102010c02030102040e06181003030509061b0c040b0a030c05220e01020d1805070302091012 68
    0x203100c1c03850410b030022840442d4041317100c0342043c2c100900c641b8041c0440301c17941d0442c0f43c1114001060b007002420141c007814090003801188029034000c0e0700e00b01c040c16595200c902618200740b8291104441d40c8180c0800139001042440100311020101c07206a0340301005072182061042150000d101320307808004222691011401403004201150102c840d20720f810a00075043c00e403d06e400340520101d4900302408035402c0000d80d104691188892000040d805070096488984031081c031810403070219441401803903012000c0720000100c8068602402c1c0302e88044a80a0554600300c41c20b42c040c00a490b0070030010401c40325902c0e035444c5020700700c2c0500d101401d40ca034025001c100542710707207a11051144001031018804144100703001411544c2c12100c00c0d540c032414442e65450602c01c3d598009076140307403280f200000034064000f040c81d001030301c1003084a01e0200741d41069110740f040c005041e039808102e051005050600b078658220300c55081407600740e6901c80d01d1007881941d40e5408c403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 571149415 1250 571148165 571148177
    0x303090105153106050d0f0201030c05041514091201060302090a09150b0a031203050106120513120e03120408010614030a03030b010318081803010e121e0307 69
    0x9070724807503140208112141101c1151041e000c06460003080c0c003c41c10728640c0d82000184a69803841e1590000000b0080a0902d0003044040d05081c1034844079040168046810038000c054040c0c4914112400d0310003103000071440d000800c80c1160509205501c606848030100000c020903034801d0720306885108400004103c4334190700c10b10550590240c21480843c1c142440f4000040240072001142c17069840c001034418120b03000545c202c0c4c0550f001401d100c28006a41c1480f680c03603080315040e9411502e4074099078113561051011100221522801070041b61740020000e451074040c01034850a81c5011840641c0010009080076400007c004841400040800000f0402c0c041c0342c000308691144c000c81085c0c00004030380c44500c00680241015034540e401c082c01e0f0701951010481c204000d08400040c940c0789404c042d90b40c446030320850b101c140f8001c84002c0c0d02c0d0501959051001c100c02818101c0c44145031480c840d004001c0032002c40c545a01000802c0355410003451141c62181c1c0c0709 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 571150665 1250 571149415 571149421
    0x120c0b150102011a010e0103150306091a090705100302031807230405130816080a030902031b1003090206210708090d020c0607050c090103080a02161a03180303090105 73
    0x1a0848900007072290b03840411540d04da50981c1c00c41060100301d00700303090100c1e4100c04000300350030461943e0002405a4035006c03e46041c0038000c8900040c0c80d01e681441c01c0c560b00c5042080f5500d00032071041d1a405403211803141c0d1101c3c400d0700a1034104440c0c0c60303200c14225141261760300300012504004100c09950b070240c903021000120940c0d100d401958200070030304121407403211204409201911450380081c407400380c9030500c81610f428540007000740da01d034004d00000802800c400e24050740f091041101000076400190700d00d05110800601050800c005030707074194090098070070280c0e442442404403900d44035401501d40e288400002c05030080f0300d00540050b00d00100580446160f62014103402c0d4180e400260805440c50200c91458648403946400c1d81351181c2907564603004540e100001040104990280c4024104e60b0240e62036070341e0135820700300c03010300501c503c0180d424000090044048094001c581250301c904803040c4295403001264070b90f510694100040740e54410030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 571151915 1250 571150665 571150667
    0x702101215030323120f0402030a0c03050715110607030b010909050a0209041103010308040909140a11011d0904020d032303091b0603060127082116120c0b1501 70
    0x110804591504c04031800d01c40944d6205443e45002001c194080b180c410200382907582c100a03501e501070748110350026281d12454000d0701d90740988500410701c80e4001103411060300641203000c1811f290320040c885aa15001c04030003601c00000c000781480703003205000c543c80d00c107070181520504002c1000341e82e40d00114240411140c038400a80007403102440107000148601c0c0c21117003181d20304034001c204000700d800d00203042c003401c012800c510b204281690301003203451942c804114400340c0707a1400381e0b0141d054070410207003484c1340240d10100c6540014018a44003d030000c140740203280164503003d060003814040b295461003d06812408410061040350030821000312200011040300c800ea400340102d41c00340800307403500c0d041c082c01c03041c0d0480f040c20301d103803190100030800003050b60395903070709140c0d901d401e55140c0360320101c1304151007100108981c404484035180c6142152292a41c540c03901c40544020308119170410501c1d44152000c501500300d00f40c0594000c003015a0303080d8420340 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 571153165 1250 571151915 571151957
    0x11406030f030f070303060f06020609161a030901090813080c0406030317040501090816060e0d0206040f030e03030d0c17061c030207150302070309060507021012150303 74
    0x92244694440301c0c40c07440a03803021050faa002c4000100f060b0700c0e03020914054000d84041d0704184211142c0c10b030001000c0c0e40c0000d0103401030000c0c409451031092503000b0b180b1411102d003e00c2c2c5000c01460308202500c00a0401158003452102c0005080e0a02d551024880e500c021003508400c000303440180a0240107100010307242604950400c11586541d6000e080078043c404a40c0c8801c003490005018030074207402540751664080a0280d03030f000d800f09003000342585428151182450940380e10484900003ca88000409a800610b81a81c2d5075841c1001d03400b81030300840c200f00c0e180b1100b407910b0300d00300302410a0300c00c11030003c50621130340d07007005044803004605443c80b64070060500205855440c44000000c040031081800c3c03510908059140103040c0e8005154100900c034a0014140d25502030700701184a5501c01404a0f80e4a10072240e5000d00e460113540944408002840503000321012032450404178004100d01000c1e0200f2220500a60300035030209440314a904501c0c0c0c0b0b001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 571154415 1250 571153165 571153171
    0x902060415121d070e250c0f030504140901080a1403040906030302100c030c0c021c0c0902040e06030601060807030507030b0316030605010b0c0c04050915151c0201050a0806011404080114 82
    0x88041c401c949444140d1880308070401c012460314549286c04607070100e22800d504210250458006049541c50707180c014120740c0580300e020314070810510302c01214601600c1c164100d4001500522040c10f80d6100c0303601d81803e81000c50701ea440300300000114072100b400b900e030003140280c014040340610400d00340c05455142c01100f0806251030752816045411502802209405981046281000e032201c0e4242156020340640007444260000481445640051056501c02061000c00c0e0701c0c1c0406150355003a00307008207001f09002c100050b020511139441550f0104e15460b0120781c1d403040030042424001140c8408007540501e00040c014003443d07005990040c10449580340c50408101d03400b9850303902c848100d504c0b8075158004104000c6041040740c03500c0034815000199810141c3c41c0050707034850b00c10220f0048004450340c0c50200c901c500c00c10f000d660103846151600110487c202c0d5070010090a26040c40f00f07480450b01060716036000f1304060b081d91400041c003007411081c40c01a400b002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 571155665 1250 571154415 571154429
    0x702150403021302030618160c33060b0c0a0b10030210171506040b0c032802010c020307080904091403160618030f0807050906070b0403120902060415121d07 69
    0x401f0a101000382d281031114920b4001d450302c0d558609103464183c02c980380080000241143c1841030700c054056032112a04c85090041c01000035030f035200410b07519405020214242904058441804100c0800c9100d602c49401c001020407191207500242401402850030b1000445140d0400341d0044e8103540c054101c1039041d004010410307040d0028038103204500176030085000c04030b25804204410400e9824101c00e498101c40c410100d0142103582c15824400341006609054004894070300100c00c40d00c0c4550880702981c80c120b000e40c203100181c4400082200c864140103041c0031074034414000f515010165005581c0ac901d15401c2440940b00390300303100c94004403241c030b009001a410501843c042100c90401000550302c1681c160744074007580c0d4031550400c0001483c4410000c031140250700c00c03032080e00d5881c480395041da40b40e811035041d258001c1d009513081200b0301241c28500800300136003560b0b1400f16131302d141001e110429202a00c03001c45082000502d2a14201010300c4410058000c0e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 571156915 1250 571155665 571155709
    0x5011e0e06060a1809050139020c1005070f0b1005030708191407061214131e080f19080906150d050f0d030c1407021504030213020306 59
    0xb244001030407041d41031050f8a14400285566203064410340c0150701e041c2e0700000204600500384098501e403c0d8620f100c080e40390b800c072815951281060740800a800b026031300074120141250103121200107080d58801c20302205100101c0040e0140e10250000c0c0c0c0f042c42100c0c2c00303080c050260210501907411040c401e40044105010111740015100030410510a0503000d4800030305091001071f01804900700766000b28040800c3c10342d0025000120030003840d0082000c88016444011440b000351881c10101819010010110307807503203031403d0110300488504010340303021703543d05049070b01c0a01030301075000000c41d0308115000d498003150130701032285c1003018803840c02030812512110024590000140c000c6070000380341d1500c641e007905140c0d01408865000500600050b618125290201c0002c1e06141c981c4130818414003015848034000400b0605110881c0e080001b00e01140241c4040b90070240300002c00b50703540e000084040c240c403800041c4c0d281440400d105030720b5000002110311200d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 571158165 1250 571156915 571156921
    0x211c0e0307050f1509031212010e0c03040b0405100c020c09100302060f1303140c040e071503050a0219090608100e0c071505011403070504060b220305011e0e06 70
    0x407002060440c500c0200d035800e44138010b0307110010141c024084540d81521507108010440c1c61084000d20100711031160b0144c503a80d840340308002403401125080a006800d00100780000d266080301d13500b2602c60800e46400340060f03007006003120403da001c08011ba224080442c141d05190f0340c0c058008400300700402203181140c011074014483c51030001c051351400110600d9178400340f0720400145522601840c158401001b4507980c2d1000c22100c0b034452842e0500c03450304940009001d0049a1401d080707403021442001080c0d00402000300b031a044181c08001c4400b203000d02420240307100d089c0f40c4a42c88201c0c10648018011000288100c0302c0b18113000c801d101c44910751071000d41c00400c4440603650352450346040d20466003c8450034425500302400414964620407800c0c078908801c1c0c040713612a554440400003955024030401510360b808008045103841a01070130348010581050402240e0360741e42e50385007110036001c0345a8461b64143c599242c1521603024412880c400c0400500482c2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 571159415 1250 571158165 571158169
    0x20a020a140316080903060901050402280f031406010602190f080912100c050310060c0512041401030605042d0b09040f06050c1206211c0e030705 64
    0x2065840c0644540c0d0058221001c41c1e80030001c84244207030388510035070850340901d0840c159410440c1014428050140025a19041440381c207104d260014031000d02ca82c10348a10502136902c10000240e106c0344130802155200c01c0460b10002144107095510702002c0c0c1d10042c0b41428410b030450011034100198103655440e0304d0ba0703a004000c1c0c218120700300000d4a86054100341c0300c0d031441d583c0c0041103040388081030071000c03030154070000744100b0600041100200465041c0b2084800301c00582600d5014032600307200b40350b00c3d80d00314890703802c49134070844401c418941500582e0064000700b10048070b50302c4550b0b0601410b070052405031002d220305081074803200c0c142c8002c00321f00c1e404a624880300844605143d04400b10b6214040e0201c0420b040605000100710485017064410b14180400b046261060344115007402c644942002507a072284c030104199284241c4c500070001c07000310b1500c02510b0007440b443c030803d07090883c40f0624040310f03a4041c00300f43d49040000d210b5000100100016 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 571160665 1250 571159415 571159423
    0x120f060d08220806041a130305040e060121090501231f17030c010c05071a0a0f052a0f12040813030c06030623060c0c0316090f020a02 59
    0x20036035036141c2201d100794115a441d00e0086940410f490703101e13920500c402c2c0015071199002004080d0303000030b119030721205a040030528002d0000c002034820042001070b8209052900e41104051508101d100000405510f82540d0745540f405910b54030400101080800d2146101c1640194101104102000c0e140e80e220311008003008a0f420064000c0014882069010070151032802c074075030718508000103800d90725013000c602c4090540c41e000720700c1001400703101594a1294401b50440650b00300070a51455050003415852540d61100e012010107149030040c41d1041e5246d100b4000040c00341c94988800d2000c0c0311180d50b0740742c01001603401c02c04407003044580303003540d042c1d1500550b244c1d450803c65130311600384001d850b421100d4021041007840300d10f00d4129680c9030360030311910351a00b4000f110711040180711020b050311610000c00d1400e100c400f4000b17181e480380640d00c0e012003000c0402c0c180310300c02e0a07030540c003d44080c040c04411540d02c07912100715100a01107050040650000e51360b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 571161915 1250 571160665 571160677
    0xb22060c020103050628030c050d0210050c16031514090316050705040f0b101d0f0d152717090a0911041502010e070b09060d02120f060d08 61
    0x4043e1a240001c03001d481c1d51030920042544a406d2001440000055010041082c081103c0005241034005410b1502c9480f010009800402c00701e07580810b000141c40b00c3e805551881c2c05030040340224400803082d5010380c00154004c0c07002031101c3c0d1414902c40c0440b0504284080284801000d02020140c00001c0c1c4000300d01201510a1341081c0e410a41e240030302a9200540c094202018903020724007e0b0441820040262440c800c421850307403050b1200d048405400c02a040300300035200c03c42c81d00d403c1c1e14480761806030810403400b205494040b134070043c00f14071001180d01e80b020184900048100a07a07078003004440034220540302c7d5240762004013655001d000369070300400e480d012030303540c60b035150000c002e03883d010440d100120344d0700c0d41150030a100d880d2403403003100b005c1100c003401030141c202c1c0d80b180c03100644403840c1030080303103d039981140050741d400000520143d00003842620060040c820b000c41004220310341401a001c415800034005802540d0608594000407021030030b03070300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 571163165 1250 571161915 571161917
    0xb2d04020c030c0609010e010b01170a1a2112070218040503091906020601060f1b0309230f0301020a080411180705031b041404021b01060b22060c0201 66
    0x81d07140d0960081520314042d07803100c00381d9802040c040c05001d1205500400400301504020701002c10000c00644450300c0512a00c1c140e400c02c28005822041c8690040c51074419585201401201c070030041212140c02612103040d00c49407a2610031180820881070000300d852a5005107000d0b410340c081211440031140109494001d1004101001800c0c4141c1d518000b0182c5400ca001048041030f0b10700d034101d4414031025014a00c000f01d61288180894500300d00c003502c0b004d480160040c0727212007070341096209604100180a02048a035444001035080c1e6001c4ca031501800c1c020b5604200400324000c8903603101e6807040000304a030a8002000d02e6100d41c004800000c010a800d0100302d071042c07010540100c0d80d15100401044075044400343d07000300401f06890a00034240d03107504d8464403c1740200d00f00c1d054183c3c000100c13844c281d002000b00c03089114092040c0c03200f07544bc45082d1400394100b0410044080f50300a00b444405031904540e0001c3d040001840d45451000303000f203402184082c0c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 571164415 1250 571163165 571163167
    0x140409020301020405090f01090c05030c040519051002030d05010f03050607210204151101092001050d141801140126070e0910050f07050a0210050a0b2d0402 69
    0x90035581d00f076040c1c40003008050604510381ca4a40d400c1c03214020f09009078110300d8078000344801d1041c822402e880c410451202e07054500340c01e01040102c45034990300500c00034424002c01107442d444940320145991025001035444110b84d04510302942d8058103d0035414010307030001c0000c5074000413955041825428048140c0e12410022840341c1e406810310110140005000120b11000305032580100707042e41d4959520302080c0303004509880162401500210301060107020f01c2400d410700790b15125050400f58500441c2e00350001c142c5a01c06000c004180c03100b8200311502c00911030003801849448001c0041d03802e5410800ca0495044c0902070b4034141d031404019070310813290b50b408541c000207001ca0303800316960480c1c814490402c40703a804650140200b00030840c002c80c000e16010318485030650402d69520901201c5603006141507a0440c440e00c43c210b04d5488051150b0360042c03401013408680da036480000e01c44021001982e441d4a0042c0c4106004980c0025144001c42c1104403409 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 571165665 1250 571164415 571164431
    0x5071a0c0f070c0e060904050703030302090103020705070e0108060906041203200c070f150c17070b10030209071e033c0e0712060c03150b0a0e03071404 67
    0x103901540100e4071206040798000800c001480084000708007261151009540d0542d10030342840384100d0107941c000c10a80c08604240b00003406a00540ba07018010f05d801803c01380300703407101c5203030020640c031604081e01c406005101000052010950041c050b000401c80e50400c0c5c1c0d81c00d0460740d0418044400c060342d500701c28080f0600000d40d40c241e84503a512181e05c0f00c00fa58001919801c0c03c0c811152824000c03400001c00c2c49688100903144842622044811107031510360244d4180c2c2481c0c82c180b058800c01000b00090305888041d03000e00320000c078940c02d803410761040c4600c1d0780c809066201805081c0300c1da00b115140d42d81c0020302c100c03100c5c071b0040b82d00c203403642c00c10001d00310402105031986041213641a40e100500482046440514010320810000c04003050302e800143c01020248500900c01101064158000001400b25840c00203010f00703170034031842e5a00240c1d801040940b203002804130717141c5906c4802440c000c10110302400b00d6514140d4210360080081c80d40c14001c41c0c6843d04c2c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 571166915 1250 571165665 571165681
    0x1302300106030b1f1b08120a060503030f131707030512180f0d050f03180f0609010c0507030602041d0601020c01081305010b030f0f0609060f1308070614011505071a 72
    0x7000154032040b031341d11102d00c0c503280b511118a401220101fa441988100040d1a0250a000d400101d0b85d001e8007443c5028104139442c910b6520000000114082c0c00c4030005068840360201404a440c10b0050402c5e20309520b802070408100030181c0f0000c071403e1040a88141600500440d0400c086500300049039001010843e00d009040001c0c019000310340069001e004040020105200f4803010b0380800f403160710801405407158807074150003042c04d000100040d4000c003030481607980140c045424065496640c00d05990140d048010110844040c1082c402011388450350018801d001401e920f41070100020100361000784480a4141850b240f101442000c0d0b11801c981c481c058244c501e0b104210a00c181d58103061400740d1914400d990015403d402c1c041111070046803ca81ca02445031264140c2c8107000e10381d85015607040904008040004166120746020741502c0b1003e62010743c50403a410082410386081030081c440d0401c29030b000220841c0900014112a494954868031400c074 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 571168165 1250 571166915 571166927
    0x21b030d0e1305101806230d05071d060d050c04020f04120b0f1f140a1203030e06060121020703090f030b0a1a010e1302300106030b1f 59
    0xc581c940b6140740c141840046400d05904409075050354014071038028683e0594070885801d48241d007840080000400c000c601b030001407041144000380000160b0405484071401c150072680324519241590400450440d4800803655114500b01d0340072042e0710b0b0f162607082d11008070180c81031140c1e5000503205100d00c8841c040d50302501504151000e40d517407500e44469020016188210540034090004040a158a08840156180403a0000c00d40d1a00d0406501c2031205800140d00c10710b0f1510214003452031400340c6960781c2c041d641c041846085001c5a50074140c0242c101c1d81080044000f5001c42c07009020900c85142c103003400165100c0540c102100c0c0300701281c1003402c10181908001041c464400c480780d024080501c810010f08004900070b9518200c00c0502038045081c02d980c614051500188180b0740f4204400c003d4a00401c0c10302d1581400720118604161411043c0c12110b040c800131459409091181801c200301000b24000584c00592612031030680241c000354401b00501c596 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 571169415 1250 571168165 571168189
    0x614031519090207050105090106080d2d020a0210080106090302010809010b060a1701090c0f0f0306090e0f01050901061a0a02030903060c0c0c03060106120f02040b07030e01021b030d0e 81
    0x11101007141a101c14154000e5804044141ca00f5820800800c4903c0b2062140e40d040311580c1c80106001e03a50b40c01c1c269058031005004c00d41794203280b80d0081c0c2c0082030a41c15003aa006550140c000c6140e1407040181c80000c0350f502d5401c101c606070051040f2600b02e55090300352502402c14080e16520380035414054905038400756000b200124000000d1608003030200c56941c10b01e001c819032a07881c2c0071140c0482d00c00d4a07007070300020b425009460240b4041c0f6207164908815103000f0603501e846900d104156407242609102a900810504004110a00c151a0040b00070310003400603914254008070002c4c07050f0031850089000107040300ca0b0b1030082044800302c41028064440c2807420b0591031604c0c1d0810020008540135500400506180100701c1e0f9041c0c0b071b00b0f9200d00300c01e0b84041800f0001403030814100d16440b503080101040605000c4003a0041d070340309130341301c40c104010a0f0009040c00801e0211510817560a61640010755010a0400e400c50403031520621030800320000650303130282c030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 571170665 1250 571169415 571169449
    0x40b010b0c010b04090f0224090d020612010b090103200a03020a0c1e14030304411e071d13020405240f0102250b0d05010501080106140315 61
    0x621103000c016000c11107002e182e000b03d0b1301500d0035502c20323401d889281d03000c0082240d085003004501c840340340101c08070130f915001520341402c0c240c5000340350f1706a000c207800c603040c09d42001c41d0f00300c2190707410f0042d062410380100290045e0446003191100c0c80c02400d140b1030038150040b804410072442031511001007138000c032140100045245943c000c0c0f01d00c0394400d07102c0800070341690210170000000c0743c5c0540c0d4000c989081c141d2440001a00d0101d1807181000d0406107084440a003583c8540655059034512024040340d04203640f44402000c19890500e071325801c42d04040122040c031403142342d2104020500304030241d80f20740e47c1c0c039420342501c580254801e19020a210511034220f0051000b20360513640d1004103280f840401000d50200c4000030f0069000e000cbc500c2d40f0301c010028440b1890703c82200501e00a4990194000f980c00158405141e20313604c03001009103681c807040c0280103241906001048c03c400d41e002c41d1851000506035445240503c030180b890361a640803421031600a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 571171915 1250 571170665 571170671
    0x406082a040f03020a0605120a11160b060f0409030f08070318060e07050405010b0d0b0f1002030a14030f07050a0e0a0603153006090209100617040b010b0c010b04 71
    0x750b20716104046a03600059010754085000414200c5c0240c003203402da07800c02c0700804029601d04540401a0008504d1190400c0c000c0c0a52a81080e03150401440305125442134915860180184500c070300324540600d105500303090102d4040ba0300422103d6260315507140c5540c150342d8107070040e400760a21034214400380da42500d0031010b00005502001e140c2c907524080e2610995039008010640d14203000d1009101c0303040000040c0c40110382e100c40e4400e00c000d441c4100c480c9840002502041c0d00009010142e00000f8041d440b0a0b4014840f020210041203032504508144282d02d4035035a004000b8000d01400048038503074540520700c0d401c251440100300c102140e442d0040227000d040c00b40f1211410b81420680800e1109200380c1070b1100f10a80c5ca0400051a030800e00c6a07204114144203031012503440303e2510150700c580741d00134030a5526400b6006094035040d00103111815000300c0c51601d988120601000490030607d003411a003600d5a01c0e41c03941221035000307005200d9544200e0740302e0305d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 571173165 1250 571171915 571171919
    0x1410140f2b051f0b0a0e041103010e010b0a0507120e0307170c0603011410120213060e0d0b06010305090304050a0f060e1203220801140613020406082a04 67
    0x446200d540414071207240c10700854035034240810b80218031004841d054010745100b8070424001501030030710b0030350340d2a000e08803014050115003242d90190000d008650000010b001d80b02100e40e0351401841d019140500e4460400c100070100c3c0500603000342150405a04000c1052082c47d4414402c0c1d001016600c545541d40d2140b4811109210040d0950107130060241c101d1409505427812170780740658065008110706c0c00c00041c41d0303801030304105008110f520850061b0051002d131800c0c48180c010703180c00c0e038103201c1c0103042e40082c01c0080c0d1045030040e6901c0e002072107070301607280c1261003824041040e844150026003140a00d4024a8100c20040300000f140340307894481c1c0082750019210000c4030708c49581481440b1140c040e00341d1042d8400c22450310401d88001000103044c50320102c4c0d100303c81d140c442d01800c0d1801d2a02039103d4464400a000311464002e222408070b0462400441c0361601c0c02da405024000020302e185400079001c2c40e1100e0b49546550000001c00a43c84034a60f90750b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 571174415 1250 571173165 571173217
    0xa2604091a03010606020d1220040f05150403150504170c010204090b0f0a1503090c080d030f050108100504060902060a09060210020301030c09020711040f061410140f 73
    0x7200c241040792096007024000100307140041402c0d80300d41e950742e49442410304085024809056410f001d01100f843c2680b05040240560014202401004900b403480a01c1c1c5001c002160042504d4890341103401c200070400560724048440c1209014000070400303558500706546110141c07840102034807400541d1103a8000c041d802001a0b549210041020800c1001030102e0058052050f60f04a0700c00303c0240b16000c2c00c01c00d2680041030610b00441c81444640e030390034505c00180d03c034202580c030101d0710f100100e81500502c00482c102c3c0c0000c01c265803600c44c940e5681c0140c4890040595643c501203014485590046440e0640260840e582d5100540e4020183c4400d407095000500958011800039030b058000c590480343c00c0425842c01500b8024004002e50110f1403c81e040704a590b01d50565407214040d45154005074480000e0252914041101c20154001c28a110303200c00c10720010b00e42c0d00b01ca5010707030404040b10306540751050054440c64a00c01c0da00380390140c2c0d9144801020350 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 571175665 1250 571174415 571174451
    0x81612061715070206040213110703090e06043c110301052b20030105010801150501030216080702130e01020a0f0e0108010509130b0a020d0606020a260409 68
    0xe00c4001c04030341040ea0340303008a15081009860000045e0080c2012901521b4400c41008010060060000e204100201c90352901e511071482100841c1046c441003180e2040c1803c407640c41a000d42c1c1c140400f000c03280700f140321401c82200380c1c107a0640a40c01d50301110842c40300100d24031649581005401d002ea41d407a240e6802c240300c0c00f485030b02803209411a00f100050901500b013088484107042410076551111f2045400004282001a6554042855409004450090034208000142882e1150420303d00009580109040c14010409000d58402d81c817200000d458101c2c100c103031240c010f1700c0064003080414021091031414a51004c0c0d107501c06500402c0304000c01e403214402d6900d0820242d444106001c6150b02140c80035004016038204000c0c250342c0014000503001c0202603658483c0580181074074251072407039001c2800110800e0500c206406458240010b00341c00405645124807400040c542c0c0c1c0d00682c0c11000c410809000b9420341c0c002d030494000503c02c2c250780b08015004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 571176915 1250 571175665 571175699
    0x4170f031029040905060d02030d0c05190b0c0a0207050d0813271a0604081e150705090103090803150a27020306031c02030d06080d08161206 62
    0x1400c99488a016000b00e00c070800362555030201d028182002c0c50500302400030034005040701e400001c2c05c03000d100181e9041c00100c100c03035115110400840d80d03074207260b0302d4481c074450114189248004e601020451101035a0b5010f905150150342d01c82d8603440807800e00302d20f58802900016003134505820030080b000507092032104540c40e00c9440346d4443c2100140d000e03030044159400748000c0e00d510a40303119000003c4400203040b0450132003001c3ca01141455000358080221908800300001c0d10052514001d401d4181c60710007006014400c2840e000e12500c0604500c062003000140b40259900940020070a00c0d001203400c0d07103901c1e04034000d012868240185c5031203845294008140846c42c1942611140e10341c03200c015206802584e00c81c000c1d4070203094941d2510484035076420b2284a0340880640c060b0560141d03480c0d0a070840d42a0564482d0340080802d40c110401c4140100da110015580c8102d03088801ca10700e0618042c01c0e1040102c0340d030a00d9032142002d2022030300301341d24100c2e161 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 571178165 1250 571176915 571176929
    0xe06013204240201090305040b1303080c0a020a08011127040c05030a0c14030c0d0605030709061a180d020103140108071401080402060703082503090618050604170f0310 74
    0x14094600010813405c80d6100c2ea4024007081c024041030200c501800083c10313880c0f000050020344e040d12601e40c1c9050ba001044622015842103200785c04504000f1505001400174070021b03c00340c202c11b21000b05034010f079070014035042d00450110341000d4a40b40400c04a4001410800c0300805121005103140c4c421110144e00a0624420381c11043c420100244030341d01b102c01f11811510fa00c01c048000754032091a111505450f100080b501303176010b01013680100031248001070320600e00310764813803640c0080310030f4004402c0a1040301c400d050a00003a03403002c08100e480c106807013a6480184d0040c05440e92051501c2401070004ca040c800001d1010151920300d0301c00050350204400447d0600b06c01c44009401040511075600001c1c042e41841d5001500744002103880e00e80c80b09545903286640540c10b000940300d9030000c0507c0031600c00d90400d000c2d11181c40748503501d5a1900340e903452015000034900f40d801b41040110030440303016103400d81512458580e5908141100020b1340c20240a801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 571179415 1250 571178165 571178219
    0x909110a0905010f020604110307050406120506061207030f08190f02060c2b090b072a03021c0203041e0e0106090e0c0705030909010b030a05010e06013204 68
    0x210b0a0b600070580c0c0d100c42002503000708001d564540c1c0740c4528085004009805100d10100410103540f24090301c1c02070002c030a6181404a92810142d02c1d150300605114000e89441c1e2a441c4102401b0070100c0c2900d030010100003007940c42d4506600302d0310a100f109013252003e14545846580c2c00700310080e2070001582103a009880f0064004054440d81131050149080c490366540f49880c5500d000511440807180091020036544a07003850110031910340e400950741c09040c540c50308480800da46064510906286094001e0390080d41d103140301000b0f07001c0c00c0540400740307010610810482e405492a00141a07174000c81070031071540c09906000b1500740583c00400483e40c140314031018011202c0d181d42880090321000c1e00d4040e02d030f004182c00c0d18a800b0030002088191a03d2401900900182103e5580c0b0b00e000b2801000b02c80d410381004d603195200340d05102d003603a1b11000800b811460790403028040c1080805000d5070072829044212000c0d004103000407582c20040760080320900d040a0b072 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 571180665 1250 571179415 571179419
    0x105060603060f09091005090f16052d0604350a021002010e030a0804030e100f0323040f02120d091a0c010f150b12160909110a09 57
    0x401400100c9006070031000c1c44642c0704440c50844d03071203500042030206540c030882e9689140c800380c4000300d510342c400390b00c40c03418404165820412400c1e10180517403805400f5007410002005c0b07881c00e01022140d50360600c03000000f0a94522030392204400148500d5641ea40c4075502c00f21203c142d035280500e5100c10004404152206441c154048075580c042e00c0c143d010740d400c22044c1120905e4250441d0342c0c41d41e02c6041d01404100900408481d0b031207111480c03a0918004040510048400d4041d0101450f10882c13150044010b90241180d0304012038240113240484001007200754401c03c0104811042c13100780101c610003084150700030386948a61581c004900f55417400801d03603850000d44049800c0222522400d4442805224240d80c203203400d90055981d4213403020711040150480da60b00c0310340300d50300481c8610401400300c44025820400903034810780d4461001851101d10a0402901c284114407036046140905a214020464110900074002854005006100120300c04142c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 571181915 1250 571180665 571180669
    0xd030510030210020a0b15090c0705070e1b0403060209041107080913020403022814010806060f0f07060203040b1014010e0a0f0801090605010e04081905070f0f05010506 74
    0x180600c80d5a550210380c000301d00d150309124510b1000c42d160421030082c0f590500c0060340440710107000d640862940428445440100b1140d52000703003074094904030800080e070015402141d504200e45800e16942d040d652880b20a4410107080c0070007030b01041c800600401001f00300d502400c010841a1010807401900900d000d03003511540310301400082080c01070f120700e443c007034440c41020191280051305141d42c0b50302003200b042640103915868100310891002c0d0503a4012450020104803441103945606000046c10b50a8007400d41405004000780380050b01024104986511fa80500ca4a0783d848180c10100d000b0341042e501250070100b031a000c44d0303042d41c1e841751042c2640d1005602454040903200151446903540740429008003007000c0008101150b14010001040c82100202d10941c131072038000101c0d2030580140100103200401e00000c1220002550503443c0b66480c0d810508035124400e4609018460b4001c013119004185041005100c00741100824170900c001d011380d8981c034003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 571183165 1250 571181915 571181921
    0x30d0e0703031202090604051021180308043002010f1e0902040b040e0f1c02030a052203030509090a0c081302060904020d2a0801060e210705030d03 65
    0x12001e0700086003090070450380a0310313038018154184000d2503036190039681c43c04500b0300d0b0549041c0c274000c2254541144068100702d01c41e0007403964610010000c2009000140308604002c007006001c2080e00000034042202950b02c5001140000d0001c2d028140d0f01e101c80b40c80b00c2407241180c0d0042d4280442900121040d00843e05010016001c21010547c588801c2006103c90035040e0b90060f1221f809500300d880b5849a8403a41d01c402c40a0700c901c1010804061810740c0b40406640e805100c1c0011a550319030110a48403500168580103643c1d900c0c45402010301030100324040141d85d6095400005c05030048002c100030b6400361041d185540e2411000c5c0c0c12540690000170201d0f015200055044030300b001411031881c030007040181050202e81c00302d805c1760000104003062075591070b000c802074100310b44c510b5194882d420402c010309100c2c070002040035070b040c0700c3c80052000000c900340036685c0d984841c0414035000152505d91080002d001a6240441d2055a0080c001c00060034a02d5200e40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 571184415 1250 571183165 571183169
    0xe04051905070e040201020c040905300313020a080610030b0106051e21100e0903070302120a033309060f030206070204150f0504051501020a030e03030f0c030d0e07 72
    0x1001402019240420f80f10b901d0301c0040c0100e0441c05500400001c941d103520031a44d001c0d001e54003c10317a542083c41040400c1c0c41a0100c21800381070050f4050036042c580c0100c1303502425182400011041500c0814851515500152242e000310030400c0511440c071078590301103038058010041981d80e10401a62144100c104141540751000c15418048000e07100a20b032031010803140c0d001030b200702076001d00400000e8404492108000d2000c00c400020703c1c164582000682001c2c501d004896a4040c0d03030390f242420b49131010321700880c0c00410039003c0e9000c2c070040e60700040030195008051004400c034245600c08074040020111010038042401d05c1000c1c180c1d84005038000d02503055400300605900400022a44240c0b50f03914400005480104080141030000c20426010b09140807c000c2d100c00030400400071a03020401c8081d03070f83c00611200d14070303010704001c2c8003001104007182c1148103200d01c040301080c0001e040c5105420020007090310b200314450030404c40e0103080c55151078043c68 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 571185665 1250 571184415 571184423
    0x200418030e0114130806090f030313140c0406060206061809191e0f050c0402030408221e0f0b0a02120d02070618030315030215090f0603010e040519 65
    0x2003071980e8255002d000700f012042c2c40099481c0c1001c8207101803441c42d51898203c00da5a4101c20180300201000b001590100000d0f003028504600d0f00782c03a1510100315012029150540200380307080600000e0089051025003c3d1003407003210345a01c0040c0d40c40354280c40700303409548541d00c2566000170f08010030b401480410050000c1010504509400c014864015102003001c40702000501c10003070081c50219100c0e40303c0150421043c200a42001e0a4221481c09103004000304400180c2420484160038141100300c03103c21070b07191326403070a0300c01600001c40c141402c01050320302990740e00d000411101c8400c6110030300e0343c5450040c4001c0c02080840d81c0940d0100c61080c4440715030710302410700f0780d905040041c144201a00e80320140c0303064079424184050495a05400e06d40e1601a4503001c000510011903020701d594003280c084042c03182124442500403d03c18002d42c0c4210382800310b000001d04c143d84079619580150451842607604550750302c9080c00281342d85840c160212105500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 571186915 1250 571185665 571185677
    0x201020601051e030114040203100203070818100f060807080f15090f0a060203040605090c010909200409063611040320010f17061c20041803 62
    0xa000700340b00c82c0c3c4040402d102c0c030390590011400c03995202441002502c42401180503402c4c282401414140141d1141c0085554010020068226081320240381c001d816180aa18101126007440c1c0c148450351000d80b01c481d003420510700c1504150b4100405480300d02c410b40b1082960f51442c242d40d01c0b1a00000c41c555007003c0e074020884230000c136000b603001468a050b2416100d01c0c2618a00b804944041151420390100901c41403000324401d244d48910140014100410b07c0310000c2e014803900d01c200e0b803c00703440b44000202d01c20b280f811100c40d8007011395983e03203898a070100000500401d00513003d51001c20100070584001520700340d01114240041c80106040c81200080070b0118080b01d1800b540d41000300000250f800383c15420441440c2804020751141313078000500a406880d020307010460448920544003840c0700013070390007001c222101c02801020846455241c0e404541c00b0b0110069202c3c42c040d001e9010201000c07112049800300081c4502c43e00c2c0b00c5504407100d1002d000191 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 571188165 1250 571186915 571186919
    0x1110d0c0f060b031002031005100509040f0e012d060302150904110c030901031103011802030901090503130609120b07030209010c0524090a21030f020403030c020f030a0201020601 79
    0x40200d1076881c00502403440402c0182600000c2840c02410105d41c1108560000c20400d0303051500a1b190040c3c942101c00050160803102e00600d503025407490907114a9607059034041000040c5d000742e5410015400a0019036181100c1c0b092084900003c42541c0c9052041c08016280754450041601d42c010100300ca00c2d80007088d54a59030f080030000c41e403c140e8510006900500800c080c05840c001d0000440c3d8480c1c2c010001400c0d035034202c000104290b000d20041c4062030480700c1c62500071a5425005849a590043d800e000d441e0181015085010026458900c45801003041080d0f079100e44841c0310081d035803180c03101000b44c4101c000c0c00054061000c034601c0762003600104110340301490501140c3c107440d00c850781808443d206900c0c21b00c0b1085c10b03c0c3e0091890040c103652016252001e002100c5040c0c64003a120341c000607100c00321656022564441600a80c00a0700c51b031500042191101d4503890040c0258102e40740c2688209610180c1401915000031203039001075040c3d01400e4103034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 571189415 1250 571188165 571188173
    0xa0e06150a090b031510090602030a0c03092612040f030209090c040614031002030606091c060903020c010e030307050d03050a0b040905061533040801140601110d0c 72
    0x9040494101e042044110001034481400c0d805035009031101c840252002c107280e0204582c1d010380d00002c2c418040c51010400084e038020050340c5158040d82080150100740340760480e003089094020b010141c030300c101a0302c241c5019100c48804c14075000100d070015555201b81d0000303805541728040c1101d8621030140010300f80424000d0304400b51008840800181800140c159445500007000224030418001c40d5440c0400506039011910b40e070441c81d508080c070210b0110b00c124400180244601c1c40c0f64629103a04c82602115550040700401082032245002074a40246652041c0003c190500002242c6004002c035419203600c01c00070484940c1c1803c00f80c024140051144c650117a564400b02c2c20307519580074140300d0620820140c9028a0308801452040c0c12704414140505140124030341c0e032805041040217610340201c502071120350300030109181480740c2c0d00102515420200d0f03659001c0540004280940d0f805d03200d120b421102c00c43d510b81e13645035811f9880c000801001d4400d0202d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 571190665 1250 571189415 571189417
    0x809030a03020f0d1b08011401081302031e030c160b030f060406080709020319090506010603050c0d0c0e0918030a030e0109210e040b0105030f100f060903020a0e0615 73
    0xa040c400300030f5041181c0c0f041030038119103203640c04805010800d000d16140c940c2c041502409448041d0120a0940946000a1020030020080080c40600108000a6541c1000658240c401c10b4100b4044800b07000701460301c0b40c00040301e208051090b450781e4070062082032403801c2070300c54003032885096698141610389198005845140c1265958401203510f0500340054006484070361402340c0da80c00d0910700110440c0d60541199102c3d80341c40c440700002100405c0050445e405072901099917100c6404009086c894402c11500b681d2405030404503458118112002c5141f00301c800303800558901084c1054070b00f0064840c1100d400030007108d00c1050095000316070100070f100001400d1101e030782d1000c0c04071441d4000e2941074120040340405003a84088006058841514180036040c16600068140d010250130a41c0840085d000580c41d000b09101002c0100341460b20481c1c0b140e0340d08000303018541e9034081a8081e9443d19000300310f840303180c24010302680c005442d0003905061307001d142560b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 571191915 1250 571190665 571190677
    0x415080c0904090c2d080703020102031603050d02040f21030e1905060708040e0114030a0b22200a05030604030c0201050c0304090c0e0d03120506040207020301061d01060809030a0302 80
    0x4980585000b0824032a0600e0520102449814641404202845c030031800c0c9040d0f4800485c0780c1c0301c880148010303640070098070400089245505550712807441c0c152440d004000024107201e201040000300380407541c0e212001c9407062145100c040c050446100510150000e000c1c012452081e0245024140340f02d00e9046500b0703c496100c2c0c9a41c640e40007400d281d100c0f400a541120002c1804e1140050340d9035090300404a80840c0c0c144115000c01080c0c854200b024050103800840b000250b07040b211454554000b14009e94000980b203051400c51032040040022440307016485004d8006c90400c1e102640a0f41d50040082526075201e40d02200c289488403012070401c82c0a00c461030244908101030006010551000700390081300300c0000700541500c0650610440341614801c01294000604900d204001304010410b603031781d10040340c060f1040703000c02501986400c00010f40861488017440c1501d103100303010000d0381d81e04c5004544408090796440d8080c0c004000885083e4001d03401081 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 571193165 1250 571191915 571191923
    0xc08041403041809110d1703070c121701050a031104020a03090f0308011a0f0910090506070515100b121302040513020307151407050a05120415080c090409 68
    0x102e01503e54182c0003011052026030340d55540c0b208144000c02050401c5040e002e0003e964800041c810758480c04141e0000400214000400001003010584900740d00d51010341c0000350313190b01d0102080300600e0710319032440500d1803061090005c1850b1030b01000740c40443c1e0304040c0c0350394190382c1401004002d5200c64800703410703d60344007209000902d012294040041c001c0d1141010b82d0315041c40c032903811003d50307415545040704100f0900c145100000340d0b00c41e500b060707030031000000c1e00345000d54501d030150b00415400400070032000200300001400360110760480443c0807458990300f050310703880c0390240100980400240701001800d488084a40c1e88003202c0ca400e15001e2030f030b54011034100d032002c1c2d40c03c07801542d0a013401d0b815410208004801000d0b51000c55042c0c02050700010110403000c0814001d04c00c000541d03105002c0d041110504182d000410340b0488528814440d000f58014810900c1d120b06504280c45458040e034401803003030a60750503252034a40070804100051140f404116 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 571194415 1250 571193165 571193167
    0xf06031c030b0303120103080a0e0607031b0302070b0d0b0316080601030305160c060c0605130c051c080a020c210c010525050f0c04050907050d0c0929040c08041403 72
    0x135048102c43c001b8021800740014640c0ca001f155002009c4042e90140140101310801040c0c0000341e10580000d06141500c5015448090134601242420455409240b0009011070100303900c2000341d001c0d00c200c440450845920441c0180030151503035041c0300700c00c01508000010408203021320000c001003c501d60040240c1401c80d40c98803400c41d0950003031400250b50700740700010810305100ea503410008000f1803900751402903540005091541c06181e0080040341c0e111890740749591095011164080c60b040c3d25009640340081d42c035000302d880640f14480d4012524020180c910b122403d4400c8031000d00a0b941240005485541c040e8031590000000500710009036001c0c41c004401c428802c030050050b10070415000c0d40703400303141c051251190f454a02840203000000860000300d52094800101e440394909101c03170102070503405018514100507802d0180302d10f210038076064040c0443c40d4000c24058906100c01c5802590b00300b80400c2000c40171401080e440d64403849100d0782c0404407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 571195665 1250 571194415 571194427
    0x309070807180c0806030c0402090102010905030301030b0411100801120f083907092a0c0c060305060f04151e090501080d17061c05060f06031c030b0303 67
    0x80d03460201c0075401078800c401821902c189200c201c3c0241c2d05071031890b190401050620000103500d03000861100e51140e9400241c2c0c1c00240d000b90848601540c05c078042d241c03a585d60307041440c0d041004440031220035580003849121032402900c01c0500d0f880ca5078808002d6800c0072030901282e00f5590003655800b903106800704c002890a0300074180310511070341c4003548640d6941d03464450701c403c460900d909060840d1854621100240c81011122024400b05500008681d014603000080d6003001c83c50520040409080303800003d220b030902e10600c00700055566601c13045080307a00603112a81c3c007040b200500102440c080c0c00000d245103e0a0b0350f0700c441503903481401d2150654100c0d08100714062101080111528071441c0d0052a5040c00b0f0308004103104401810088855120902c28850001160103501c484099128855102c9100e800b0b29110381400c90307498104864920b84083c02d00005501400e0119000408800c0200200200c10105106501070320000750900d41521041c086 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 571196915 1250 571195665 571195679
    0x8060d060c020c0f01050903030d020f0d05040f030e010e0f010e030709060807081b09010303050304060b1305180d050a110f030304120f09060806060307030f1407031a031002030907 79
    0x101d6400c40d0050300207288100e982030510980d4042c0546a03410320005000300803080c0c402204071520341c4416a00160380342164060300d0752034042c00c40400c0080385088100b1041000c501e00a8000c940203032140c903504185d071b20044807818070068105402c504810455841940902e92008032202d004041d034038a1512100040308880003980720070607503880b1602c2046012000d211082160004110381100112400c01240390142d040c440201000400000607007400650782c8078031981c0c100284418241c000d60240440680010f448035482518280e10b941f0134110300040c1c0a01c100c445880f10350401507264001e031001c1003410821380160080101c440303420b5901340000c1d13104600c0344011008a40301c0c205d004104044051a020a0140b040f600740015034102c0c0f11640e0010080b202ca0f039481c1e6030850224060701401c1c40b0101c6040c14140c0450010280d031749640d110704841ea03400c1285c40420110980443c10146110b13030550020503134a4408403054004640c0000d441c01190346503a6544030b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 571198165 1250 571196915 571196921
    0x524160804030333080327220603020a0801020a0f0f020102121017030a08010302040903030e1b120a0b060607061d060103120801150305070210140a050606030705040608060d06 77
    0x8840450611000d9182180040d40d440180144c00c003080150704100c40306004c00d541c50341f82e512002d40707860582500032a564462000040700b40780a0148815500300007805000b8041c0b80c001203100b41280380c1c012801007414425074071111201e5030340c5039000b520220159110f803204480d844c110b5400f0013000040d042c00b40800c070f000c0c00c41c03200c40c01c5c48240b4010800c5001c826003420070010f50801c008810380180d1140c1040e040d0303601142d002800e0901894181c0c0100441c1100d82c14a000b114440591400760500c1c48180350b00c02d42d03040618900d2a2041503c0307034440400180941c900101040c06800c000024004c554803500d0005008840b5449122890240d0344003903aa940c07203500148100400410201008500c03400d00c0d0069504003c1e0035072608103d0f00403001003554800000e40c40320301c05c00c4103a0b000e014070582040540c0f4601c40c0507001c00401c0b61111949410300001c0380d82402d00a00303d034031568031540e46604050800768100c0d03800e003001d0800c1d580070300d642c0441004110584 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 571199415 1250 571198165 571198211
    0xa0f021903030507060e0309031203090a0c122d1b050303030c07060609150b0703090b0a0207080610050d14010b03010212010302211e031605241608040303 68
    0x5200d030f0340c603240d40e40f03408400d4404044002007150000c3c0150340f40c4d0b4800240c3c100c040b00c86104403c1c0c6954603261007510740480180d01070a40d4542c5040000c01c554880c51054504d4003039890b00004000f000300221401501c000000340307854a99800101161620707141c489102c014001c000c20403075440b40000d00e140c000b5640703030b0115480040c104003001154403502000300207070b0005000880f10504a50102141d51240402d580b0340022007000b05481410581c001d170603543d002c0d40c1c5480e00000001d6a65605000c0c41c501d621074000410204c0840640820445a000b041c283c0b20118590703c20365002002201240030b59201c8000000b83d68083c00580111014540c20490642c0f66004002500c00613030090703d40031a00740440070740a000450051a030790f4040403480e109446224200340740d072158185030f18031032081c10820030402c00040750f24045a620b101560f032a1400304c95040d10303607007004c0d2040c0c00070705280030740507109900488034545c0c014046e05001910840692105802c2c00d822 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 571200665 1250 571199415 571199417
    0xa080f01060608090609030f180d05030a110f03041401110604060524030c0f030a0506100311100c02090408041e090c0507081b0f07090e0c0607050a0f02190303 70
    0x25001480700d00c0d444110140d01503003100045c0745900300740042e180c8a100311150451941c90008201015a00d050712429028102408490711840b0301e08065450307400c042001000202d440004828901c0c0019050540380124406540780903d003411440341d42880c61080745c140300c5d04012211080c0c10910169201e14080e00c00400c880c60160b1800103003040d1844030103103c4000c0d4603006e5a9440c00217200340340e40402ea40c0c140c0500250400079180240d0031800801500c07034201080105c801c0b0480f05070449100f1881411042c00b60810069198518a60780c4001940c2d40103144c05803800f240310b203030000e0044102900c1d040e20340034015010040c0c2107104c030391001c520f1010807a0300514484c1005007069480c055061403e0b585c3d66502038425111004640c2407001d000c01080f103c20f0081c1d2813100d14440445403411340c0c030b042c10009868001110f440c280a03a607003d000d2030030040308585056a00c44050040959595184524400105401d036080000e4074030580d07030300d41090b02c400c3c059402 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 571201915 1250 571200665 571200671
    0x131704090605040509060a092d0b071b030c0c05090705070b0604150302041119080709060c0b0a050a11180901050604030809060c0a1a06030c01111b0a080f01 69
    0x1403200820554046501c40c03406a460721040206604020511303035007141210502140e003a41505020f5000640705401d9a845a00015013003110071104454100c4c05110301c1401455656110b405c0d521284400380300d801c407a5200c400400040e201c0c82e0f89014003481800555055511a00841c0411400311000230110301c001985c241403103c0104901d0380588204d8007400155070007441d0020514142c800280669154441031440e1140503007a214680700c1349044045441e40000c0080180e1410b65114000c68a0f0031000301c0c0040c4514084001a070300000c1d0b1103401d45943d1052001820002c01d6038054503542c1003402034075242003004203080d0940d00880d1480c150322100700705182d841a80150301c1400c0800c01080000c1480b403c1c1c07420b1840807645036440c0c0560203141c1c2d00703001c002e25005180c41c0c103441000f103a80b110300b500355000380000c1e41201c029244080c0150351400750341c00e000880b41c0c046240b000a03d420907421080c1c21402030300403a80030b5070b40c044651501e001462203121a0751 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 571203165 1250 571201915 571201919
    0x60e032e110336120a030e06010609090f0204360203040305121302090c0406030e07120b1308040308120601020115090b0a080105271920131b02012003131704 69
    0x10f1b040c01841200d02d103110181005524210015018100511800751600d854030181c04100213658150740007080450407900024000c0c10044080d0b00d481c40a11940081d410080100a4080e00c240e902c03403a450b464251410189640c10501100010001c011460000b6a20401621480301c91400796190392804d07a200d034141100038050301c04241c03400280e80d00c140d00c20005024640e60f0308041d142c010440e48500d4558010000207070310300b510042d041010025002007080603031001800d40b200e456142c2c54054881c040128242c034002900d0b40d0662141203c1417140035101e0f8861041500300414054a099484143c5800d54608a60380c1000008108036031480250a0960a10002021014090041000c40341d4130381d8014450340500b5841034241e41d90340607003d801341d00990711402800d0f060880014000704026100300a01c11411000342d451400780c90b4014001c84403441c1d0420000a0071501c03000200207560070040901c0d08807101c03100c040e00803c18900e01401a00007401141da40c8038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 571204415 1250 571203165 571203167
    0x201050a0b18010b1332040c08040204270302010b0306010b0703020303070305060310091b05010e06040308070219060908160609060e032e110336120a 66
    0x120444140360140155000c1d02d1810406030b11401c2c191110404256261030100e40b459100400355040401e108401d003508082d1001c0d419425542c1300740800410a0002c000020303c0b0a45011091040125020501103001840e041d01700709042c4d801e4040341c140000c3c07001080d80da000403110040d40036075036411480c505410f00b0b021140c090f0000c00300007480d24042c1e980003036903884020708a404240c2c4e11000320388113660600112042c0071194000744454a17850410715140c00b400c109203e0001050800002c1d15401a509050016001882c0e58145407071074442e80e030503074022030342203a01118004160760790302d0b181c0109401416417560364404041c02c00311420700c1d0100c140c0c0c0b441c035002d840d240108041c42d4400c1442d41503e03180d11b041c0d440c0003030980100e8648001c44441c0f9580c0c000c1c1c101d1802c1a4200f0b0301e41004d132180b592400b032106400361410b403e8248801d03140e03446214454803007034403000511150025940004030046690390300c0040a6070510080111103c0c4e4410700261503241a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 571205665 1250 571204415 571204421
    0x4120e0603070c150509060c030403030915020a0e220e280302061e04021e0a090c0f030e03070206030618010905160509012f071401270e1003080a0201050a 68
    0x10544c580040229007468003140e6a24480100f2281c11454000300007000c142c0b1a400c4140321035400343c1900b900c140142c41d070b08007940003009406d00094a02503c3c0c00c2900d01003000c0f02d04034090308a591080066048840085d0101c60811b440030310071a4011802d640a449c005201a143c085540c1602e000ba0324000381841d10103040020b41144c0b0100020007001e080c0c0e481508030394100c40c082c984403c604800500002c074108070f168851500180040e20850341e800003c03101c2c280c0d0392404c2103804c10040a030100c4e100e080011003598400d009400041c10b006c4000c1d900400c000b045005031051041c08408210800d82105030700e10b071290207002c014242220411461000d6082450905506500081c000c0201c210751540d504520345484046080c69800012407580b07076001c4d81c0c0d8003900c0718803a103880ca00c80f60806000600e921010140c2951b41c000803002d2070303403601c0c0d00d0f01005d10b00446284a09005050722002d33000301a00040007440810003400b00130302e0740d00007013401d1508425030021 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 571206915 1250 571205665 571205693
    0x10b010306300309050603042a0803030109020a05070c03060b030c04020f0a0c080c0109031112030f07030507020c09041a060603060109170c0a1d0106090e04120e0603070c 75
    0xc0169080904098852010710032000b60b8040703a11200c0b61003402e00f01c9200860341d2000b07400910010511041c803010010155a00b01401c014841c44c112440d80c0c0c1070910035901c6020101c1e01f060005202113450342d0014441c42c012031420b50305054a80c1c6811071900d000303a004403500b0343c0c0c410762000103040a0010225207007003290300710f0400b500909400e405100d24040306040021001d80203081040b994150744a1954640003000648000d00d8058032220743c903140e03c8041e118600080c100c0424410460b4458400038402c225240c8031040190007410700600030b9000c0d400b68254000c000c1d1501c0700801d2003580200303214030071071310112660001040d002d80540d0040c94108100141c503600020f2401c11981103201c14162410050640d81c144400c004604d60b000f24910070000d050000e030101003035941546581a00e0603642c07018166442403061103000d001090301c40014010034100054800c440c0340a0420000090b500ba0005425134021030b400b6020841a0b0603100034000f01c0c840ba1341c6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 571208165 1250 571206915 571206929
    0xc040f1b081902090d021309081603140c0d0c1a0c03060906010e0306190f0608010204050907020304030506040308090f0d030e10060f210b0a02071e02010e120705030a05010b010306 79
    0x45025036800100d0440c0c03060417400790050700d165840d080314010903400420312503000384045446515905055a041c0740342402680000d0301200203403c4002004102c1e040c0c4000c90300100b540408881d0203070f84050030340c24290350140d815288402980403050341240b1545020794102c1d52842c146007004140300018040904000c621003c44400352400240c0342c3e00304106500d40c0003608001d92404c0043c0901c540d98100340c030309003600000e00d29415000f600a5900403184d04d00d02e0742e0ba080c01266a0300a5200107880c96016601150200707000310311403a0040002000d0302c2d60410540c0d9128541421020000c000950b44d9854070f144a2050201100e07906640806120b110725015504405c040b150003103a1400d80410010206442600080c8805540c801d070185030a1800d110b20000a4204004c10703603400030306c0300c0807607080207160284d034907100e070b05031034440c03247c003c0e203003400111214000342a105115488002c80c02da6000c000139010b035403140300086000d20110000500b40c07011580410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 571209415 1250 571208165 571208167
    0x30309140901030b060303040315020a0306050904080a030b01120504030905010e0a0b18040e1b150307020a03120204120b0402240403030513090527030405030c040f1b081902 76
    0x300c0c035030741da6448050450742c002d0000100c83c0c8403100082c0c00d610031a480101004020703a00d00c00380c80b4254002c0d0058a082c2c0d141002210b6940048c0803507110101d40091090904021040c449070181c0c0c060080ac900c1894a070040c06206c1149908030740c03003920705501142c1d4802c01044190792110140810324415030f10740800901c0c00b400340400340035000144030074080110418100d038a40340e00c1140390031103c2c0c0813252011a03c2d04400814040781c0c000c40c1c001c101d80c1251101041d56081100e001d008994005d040e15091514111010007108a41000d1a03400300800100c40300301c0318413148254000c40f003e4015003800c2c81040110702c0c841a121084104aa81980b020340e562001d03075046940505080c0e5560542c81840300b61030300300303810000f1502d29210600004121000e07141c01c03a00f203a20013100e01602c0e4450070640d240a98803603154594001c0108414906054100c00c1e1210282e0030017180282c1807100e0381d288022810002800281d10f075040120a8418941000301208040c0c411 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 571210665 1250 571209415 571209449
    0x60906022d07020108040515040b0a1503030806010f03140a140906010e0609040f05030d1a0a0b030703090f0b2d0402031c120f0c030e0303101a12090304030309 70
    0x25542c090b40c0710181c14481d05200040c180f25082c400d00301265000d4084405614040c541540e0040d000e81d00c00e6aa2403400d0f410018030a0700c81d0030714050f40e40540751080c40e503407124011100c1d1301c49100c42008054446510400014030f501005000d848588800300720304c0080c258810107240e00034a082420b502420042005050401940350058019030300602265501e04162046004841005003584030004074601c08500310b900075108070304244030452400016500b00024000d060142094851040010940d03c0380030340d1141c00c20502ca8070486140000c03d07110303d2008001241d2004201d2049034000304807001c803506400c44803a00249500c01d500705a00442e40da209a00546010a55820307000035045000d1842c20f9410080d1903001d01202c0c0c040c0e609680a400c100261801190030181e01c407020403800310549100343ea231507d9070b1404c1e914014002e10b2054103c01002c801d460100046140c1d91240c3e1441c0e4031401c000c00086035200c1c0703189001080c20300e196100c41081120a981 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 571211915 1250 571210665 571210747
    0x406140c01291905090109050403050c07080c0a05040c12050a06050607060b0108100f060e0105040302031b01021b0105160c0513051504020702030303191b030603120f02150408040306090602 83
    0xc0e080c1900c7c10620009404d6980746010750b0b0900c1000c1040d5504d10076450001280c8000142c68200c201c01600c2d05004660780b80306110039142411000000304001c4841ca000d01c50140c0c0c0580c0c0d1001d01c500b00440e0450f038480104105070310010080e200b21342c64168103c282d58001355019084680c18032080380503032404000c07403940480c0740609810040728031032090180c0c0c0f0400a503409507030002c1c1940c07200704140d4a0410b000c0c1c00100c01c1e9000d03018104013400b14940000c80c01040600c10384805141009099010388141c18040c4101c0720607295980118040e111401d02d007005455040300001c540c2022081c04400300d00e04060184603e0040140c0301c0141c402000b039070340210010088000c04030088440030003401a0f1120f040c1441100d1300c01c0160039a0580020044a00809203482032991040003120312000011008016030300601040c521056860700c000d80c040e000c0c0c200d080c1040d807a075903a81e05662008400391441038000c100d02c8005800d11820700d10002424560003c2e203030107250 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 571213165 1250 571211915 571211929
    0x20100c110a060b010504091e05070503070c170403050111041a0708070312090b15241c110703200d14180603040303061a0406140c01291905 61
    0x141c010300300c6444420062030b60340168141d0300900781d0300d00f062040c6e809001c2c2c04000080c43c03040c0a0400381c20140070880841c080d00440e4002e0f006a5917070900c901903a2501d00c45889105540c42d00ea110810000011400a00c6681c0303440015121a42da21480c10310500c8640c4a12080d0070504007082107440005000001200c0c20a545410203108034029110410010000104054038012280040110b0701d0001001800052401c41e11195890440c4101e101c0400c00200311001680042110500502c40410644020700c3c81080105030105041181030040e008400120046092800b040340f0a00548882d00d40ca0f20001c0020111a0700c0c8250081c800350440c0720b921601000041c13600c4217044c580300001580b40700030303145941c0c0c0e041038600207000785000c0c802c05003610a680450502c042c01c20040310300300c400a555a2110540e0410051000c2d0300814200d8000e6580300108006402d490a5030f084a510342103450700202a00c1050085030b035079503001c49002c12a400390074021540d03440 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 571214415 1250 571213165 571213183
    0x105031c0f03091509030201020d150b03010b030c04090e0d140307020d110c04051503010615021515090907180204030512030a1104080a050706030b0f010f20100c11 72
    0x119010a2030b00150400000111300340350700c1c00f900c90502040c0b500380f41d0150000c0220004001c4200182403200c1c4075410140000d0007080d8a00c3d4003040104460341c0c900002c1c581080c644c4984504d01940c034500c040481c1e02d103070f0f1000d00f190043c5610040305a0083c4c0c1c15054012640d100e1440d520303140300300079100d814102c004814030000c0508040c0f4050304021040121501070810882401c06100015030390356807650f1340d84203600700000440c04e2010329803980c0c90050780c0e800405282a0b0300c80c05000e03088005207103030207698031450710310703030580c0c5210b1050b004520f60405010701c0e909102e1100144034007140b0031140706004201c208001080028580300c4000c401a04940ba600c0c1c0800b0343c4d02030800b200b0743e1000c501e00031801042c402404507011102c50710503c03c0b86d60b0b550f034030f40c0c0540913240360081c540d07844400800d91542175400749030600216401450016241c20600c0d142d8210310b07909010030f01460340008940c075003000c003070722685180032500d082002140b40249102940c8003444 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 571215665 1250 571214415 571214417
    0x120b0108011224021b011d10020c0102090d14070522050c040803130906080106061407051e072d23060403060e06100f1415070501050105031c0f 63
    0x204200e92000c6643c4496003a4940c1c0d0300b9800c2d55a000c03141c898103515880520410403d501e0a51100740510358103164800103c3c1d180040c08442940904440003500215410035403035400308400e401c02c1ea40d0b85110042a403142000d801c460344a400850710301005504820b003d11034607503001c6004178000c1c80a400864440c4804100f56803800c981003201e000340c2c1d0103524584000f180300d8621205480c41041561400d00d4100038165a8107516400c2c0d840d00d110340004a184103041c000440c1c0450000c0092500440860f070000442c0081900c41d8404c035214100c4540060070306128500b520707141040002d07140140e550400a00d5154040d801c00288103070840d42e02c05411000d4810720700301f20a04c0546004148503100c943d64181800508900000c4500300d000b490000760740580361680f840192800200007030482410801000316642c030f8203d4240e03001c000415000c4103001c212000740b440c0c91040c0c00210742d65142c6000e0518041796420b02c6134100c500c004040440640c490110a022121 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 571216915 1250 571215665 571215683
    0x303140c0315012303011d060a030303020904090b0720060103051506010c0f1b050102210319050a0207020406150f0c021f020601050a05330408030406120b01080112 72
    0x6082d0041c0d4000d000850240300d4200f070844c440880c3c40c03506002e54103c0300103203440b0301440c0c2d202c4540b20409104480e000c0c1d12800190b401d1003c079100394082c104010001c0c000142d00845903c1340d2034001e1003203c0c480005410810808840d2440036a001e54120750900185240d50641d40d601c0d0f2594010a40350031030011407000a845030b0b2003246140c0b402c070f400002c2c41060300031b50b04014415000f0308203020050a00c0b4100041c142d48001240200e68a80300160030b0050905820410f8551000d0030343d006040c058040b0700703110304c40d904c04d0500407004207600603a0b444070303481488190ba2050b885049070044804002805e5900440342c0d95081090340741c140c1891035503100150054200361402d284078046403140d0f17405650002603003810385200b1030b80301a17a2036a541c10008008941c44803941c848100f00e005400c23084080b0b0501d9031446022400608040d16950500d2654020b41e20040000d6401d4000c0d81c175040a510036007038114000c1c6008462903050940901c514404008000c1551031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 571218165 1250 571216915 571216951
    0x30209060312070609020108100803070b15040606210203100312030216110a0f0602030f16141605010525021207060309021f0806090408040e130303140c03 68
    0x240074001d512554000b021074603140c1100d03090400080c079002e40121701099409000c10880e0034400c0ea41002c441503040214a498081c0c0d0fa0003074100c0d4081c1440400b013949901039101542c650091074042d1482d941e5034a0a40ea010400c4490105840c683c00442403040052250341c0308500b424000f0780f50410703003840944810400071070003445805000850003d0144c41801002500141240d450b8011140e00c421941c4484102c102c403000c0d4451a000340c2c0c400c100721028900c00002422114041013054001e1041c1e40c0c80311404140000c80304401074010029550000b1160388121010f011300f807a0060400e0b803003221030442d1721982860107502c000155000002c40d0340301d0b200701441094601c00e03a25119941c41014000d401c4074a012481242040800d8101640c200780140085456a4440300940c48403024000815000341040e1010b000410004c03400b42c0084150310300070480c1114004180134182001011980c40c410000c00c00d4503818180700e451030551007901d4002c130b0000400d001e888 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 571219415 1250 571218165 571218169
    0x703080f07060213080c0301060602100b0a12030c05061807050d081e030601090815040308060109091113120b0604020a09050315010501320304240914070302010903020906 75
    0x10040c114018066400051304045155000710a4030032620f01c07004944001005000300b500707071513460107003400691011111240c8a005500600c0c400c610150684860f1621056400c1807069a1001a00400c24a072151010000d0802ca02d50707001d52001006640b01001d0010291603100520415118180003034000e4107001d8000c0840f215800c840c200740e00c6414602c05005850b0b001117400380e000c1148a10001840b0101003161040d00c00591810742e10381d41c85aa050701c6501c8060100c904110b0991004506402544903051070012081c0100c0e07250310400d01105090a03058002c07500380a080001000060030705d000c01500048201c4002d42c49140c1080103ca09031060f601c010b0740b61056441300d1300c8140206c402c0b035050b528203999455800d42145802203001a01c11400e0305403400900c03101d00c0005080c4c01a541140c402e0b51800402c11021482c81e19045070741a00c00342c0555a00b1150041200105240c45801c00305006000a1440c540010b4504111484060700032a180c0001070780c1e40d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 571220665 1250 571219415 571219417
    0x9190b090402180d11010813080906181306150c021e030f030f0c0c040e030307030e010f0c031a0111030904090c080a08130801110304230f0f01140601020703080f 71
    0x3c0800f40018400c0e500c0f0b800c04418a01c1c214540754086104130f004288c802c903403403040814803608103d650349444070070000c0c40502c0d0b00070441d4810020880240c903001ea91a00c1c07101801000f1b400c4086501c5040041c404080c3d4011074142d8184902030402d00010380f103070b00036440000c00da04101005042400046402c1426900c80d5070018000024503444082d04d403c0500307003040c940011030302e000d00458103002c201e81000c02c071000390340e00c2440000d09082c8242c10081d840103d000010401131090b03240c7e4000e6030515020200440c2e02c41084100b41001e080110703031030003000d1030029400002183c0c0c1d0b54407403040d010080d005a45800000091250303605243c8000c210b040200e0744801901d081200ca01d4209108682c103030014410000fa9086050140d29030300d030740188200f4515180d035aa207488440804420a031800700040701074503003003c00d0000c081c0101408018100c020841c12070725084074802c0040804816403002440016603001078040192548141d4081d52244403c603080e02c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 571221915 1250 571220665 571220707
    0xc0b04020f04060509100f0f06021c03150e0f06180a0c05090a06111009020a05010f030b10020105010503150411120a121206081b0f06040801090809190b090402 70
    0x481d100b00180b01b00c101018888408641d5080202840180c0f41d44d844105007038076100d0310005901a84485054031500191044001e18030f00340081d0071007180301c681c00d24204030f41c00f800040101608018421840b26260350f800b0004803801022140301c0a00114140c2024245800e016a916108030780540568200c3e031070040014014200c0315a941401841049051001c25041c003e9103190302d204843c0b4001ea0b088198002c00c070030300300e0b420180115000c400d0700514070300301a2240e800d800c894031540c011101808260740013240b04d42c1080145441d09e407114042d0140c010030041004085000c04005640c0a202140c0318117204521074142c81c5800043d59015240c503924180ba2070700e440c2c000d4200b4a0007220010305010040d510381f9400d4540079190002384c1c80c803d501c800a811480c05601d13452a0000060515080035150b054917400c60f099660304450349200015050303c540341029110795089010011000c0103418070603401202e024145c01c160089402140346200c0c1140390006001c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 571223021 1106 571221915 571221919
    0xc0b030c030a0c050405040906050a05070c050709020d020c03030a090201170108190320010504060609060302060a053f10061d06070605010308190c0b04020f040605 72
    0x4054108443c0c0802044001c020215440d9150300c103190050f80500d800103910314080b0b0b8030500b1241c004d4098014490301858400005400140d008141c8203428005030710f07080492a400041c2c0602d01d03c5620900010042200c0b0303070540d03401901464001d0381d8201d480707603005441030312000081c02448603541000080c0c01c0d10222180d0030546480c864039044032505183c2c098600704005850cc003140594640c3c05100034092540501c2000c1d00f85c0301d03410000b240c0346600060076480380a0407002800300105250b210300c03501c1d00361382c52000d501c2c040810b400021404001c185014007170a0940280b40d090200da894840100d5010645003a601c03800202d16001c1c180d40f085110407180540c0c800c404214103000180d640c042c00d40203500c18a643d58407500d1020a140100400c4c3d15000e041000c2c050b1807801084800d852950800d0701503c460b82d81001400108004d444103070444c035 = true := by decide +kernel

theorem cover : BRFrame.Cov 571043165 571223021 := by
  have h0 := BRFrame.cov_init 571043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 571043165 ≤ n) (h2 : n < 571223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
