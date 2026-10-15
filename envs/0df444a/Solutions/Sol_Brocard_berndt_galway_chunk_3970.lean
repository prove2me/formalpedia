-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3970
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:12:02.450411+00:00
-- url     : https://prove2.me/submissions/d04ce9f8-dbff-44b0-99b1-2dd350c4e299

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 713848920 ≤ n < 714028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 713850170 1250 713848920 713848931
    0x3030d0b0409050304060302270306070c21090602070e0402101110020d0920130f060e1302031c080a090f0209190e070b03150f0a090501210510 63
    0x1601d55800801c0703030030b5000c4103682e039079501c3c4d85001e0000c0d00000450741d1000003060016059108103400002001c9004004001c0d80d91002021140b00045170000c984100804c0e00c1480d4507241d070701ca08404030105407980c51105040c1400207281c40403550040c3e0050113182d0510006d6250041720b081d40260314603000540841d81c9401e986000d222074960b10101c0e200080407005ea507540e501182c08103104000181c08a0704c8981c10740c14040b60204400d5029015448000c042d071031341d6000d180d842c034040c40e0104060b940c45003820542c6204903007102d8001c0c26901ea213803c40c5000d0000550358142100704064240c1c1c0b1840042241c44c000b0308010155a070341e0104428003002041c1c3c051341e140c1c01441c3c0c1e1020b182602d291010044580d12161102d4200901d00c3c802c07000108242040c0c0d25000380d0faa00303503030700c1c100c0c036615400c0b01a400d6600145d000403d00b460b5207410841801411a0200c0406e80c1d5261420303800100c404100c002410141220010002640c041038003030303614981c240f01050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 713851420 1250 713850170 713850191
    0xb07021617070b0d0902043911161716180603150905010b01261f030305190207060507020910091b032306010f1707080f09070503030d 59
    0x251010607040409080030100b8009220b040541202907464401c0e103080c00828030fa43c600080341004480804642c1c081c01039141a9403a0b1141411080c96a610380111300c851050300780c1d0308040c22b442c8078021071070664000b40031440e12401003594500502c0c0c018149200d49032280342e04d10340140117800e10742d041500241000c4180e9000600610b0f040360240c500c203028078148500400300072004903165400c04109111383d6000700c010300a0300c0010005586490240e00c042103400c08010007001101043d20782c6000256021110310300554400d0f19a20340c1c0381104c0c64621061a14038011804540c00294180034040d03102d41681e04030360b4180d40c90741c0161101e00c0c1058031483c143d008543c1103850066054807001c0b4804c0e000d43c48038403a031800c20a4071a0400700c0103201d22202444c40e0a00e0707216011410139445142c24078004c4501e45443ca058030300040400c802d01c0000d0b5418800129020244180c00c0d110b801c2803a0002c62510040201e00e1601d03010035240d010b0311840c4102156034000030350 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 713852670 1250 713851420 713851423
    0x91e040f03050c060a331202150d09051b030a0201120240030b04081e0c0d090605031312050903030c0604120c17091c0f0b07021617 58
    0x6040724109416900503150110701701c00105030449500c1103403a5810001801c2c13a40d942e00d05850060324203404c419090520b007d03558441001d20040743c10910601747c8800480c070410260482003541040401c0100017400c00c185054010000802d0124006400005558001541208007982802c2c82a1203180d0499404024042c006103024001540044803201c01d244004144441041c0c0d865a4011000710f00d60141d105042d020007032090406001003008616058040c019042c801c01c0461201d01701220220000d810040f0554801d921010500c14031075041640500a2310a0b841c08074107601d00850f0305c150301203130085c015181c00c4418417080301e03080c411401c0710130300307003010b001c50741e6604400507211b0f030300c40f000c0303031300307a89a40d21040200c0c9028031440b49110710680001c6c003040980c4151215500990005007480e610400c0588034404200312160b0004281c0e0045070220001c884c1420003008582c00200160210f400c015402c500400701240643c041e00c03c00349040100b0548601084d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 713853920 1250 713852670 713852677
    0x601151704030807112802030a080406030e070e040f150b031212070e0102030703120f09110a060206060a030f020d020d141908030a0c0e040606020309091e040f0305 72
    0x100c0c6250021400c0105264200300c0990003031090340c2c0d500884100f007114980e2120044040002d5004c040d400d040501c40f610300300c424002d4002070555980e040680e444070810382c4941e000f4030100b0b8480032003441030082880a031004000c220721440315480c0c01d41d105540a081040010203420418201440282041d0b00241100c04080d085624100388910b101600b6000302640d0349000e174200c40003d0b0303442e00c0703000d03850303503400c03043e0000d60800420b550f040d540480c1c0035150410444c0e40d2249003d07411418012440503030b0044040c048143c1010b400d00589207082e8014805550200d000d00101d07891b44840070701103d81100d805001e56a0380d200042d02d4095200029502a03466520301040c04a202056500010300c00221080d800102600c8840780140b5100901124000c0c000110500300c0390704a5000889507161002c44000701d100000c0c01c0b60030a401220042c0e00c08078400c0e44d507061036140950005840710034400f07101e40d40302000308480740040004180300400d0000b0010140034806a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 713855170 1250 713853920 713853947
    0xd08030a090c06120b040606020307230105040819180504231518070c03050c0a2003070b03010806060d050f1c0e12060a0506030a06091220060115 64
    0x2e00565440300000d003221402c1d40100c413024035089840c0440e2030b05128240403283d464003c0c50a020329901c0c2c414a00001e610036403a490114401c49040e11004c0c46014451403180d404a5180c0b0320301d0721052001866942824184064070b110038130020f24400700340003122404c450202d480c0303d22800c01036482041401c0410a02d80032000c0c410458601078420f400e1040542d40c0840c20703000441070350940320050740c110001c1070071803d9410109200c0c1c00204000401c3d070b400c5500d401c00999540c48034010381e2803d282941540010391025207030038803161000b0080390000504550500400b5911607901400040c03158007501ca5040401070180840c42716201c603002034810440381c1500801ea03d58030300c058203000900340035021100b85044062030101302c6000004081c1c42d5508142c25000b4200a01526418411100103800044070307070189580c80c61040a01140d00070000034040c040c1c010071288c8800c000079001d00300355400030014103c0c0c1114a0443c04440c2c85c40d8a81d02070740c03d1f100c1d0340030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 713856420 1250 713855170 713855183
    0xd06030215040312050313110d0b0906070306050103060503070524030f04300c080c24091f020d0207060606050c0c040e07060503101707031a060d08030a09 68
    0x311120702801c60000b038412240201c190402031665200c00702c03030ba48000c40d182c00448600009540121b641040450600b510113856001600038903100c004401a007150014403a03482001000041a414002e220042000382801e00140d03052000194a07400d030b5004a80c041c070701c50483c0e10300d4102000c07400d009042140f0309140c1e80c1d0400515403000440704440589003c454100b03120325040c0000305489a042880030407904611011394100e9038900e8154003036804044c1800f0300c0c41020414030045214404144000524000344203240c1d914500c001d001c0e0440ba00301c4804030425040751500200e00d5620070f0070050307440501a421200034026038001a01582c03400201088980e0407c008010411401e0304441c591a20306007007109071040f400d6040c2481d0004070081019900a201964201c0c04a200e03401c4280c0e180c00b1500589403070315600d0519903010728410814845001009015801c110b544246a40380049c04502c91009280e001020300c2c10000c00180d580300c1c641c2c084007641d6400780 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 713857670 1250 713856420 713856439
    0x191a031509071a0a080108212803140f0402060a2a03050409050f090c120102070b101701060806060925050a120203041a04021219150b13020d060302 65
    0x101a10f41d6030002e01d90380012581c000d00128141c031001071038500180c4244803810a8400100812280e0782203005071903d0501e80b07800410724808982d010b010000182d68001880035400c40b088403020760042c042c5103800c6903c2c024003000d030303c441044130480ca1450500c0442201c5004000c003904000c0380c2100006104da9140d0f00030103038020000c108a480252007440551620303400713544108800e0f5940c101683c01045106c501d800c2504010751400c540c4000141060400d4403590042c500c1200c601c5000d2455540030300440700500d242c81c040f0704e0408003c00450f410504950b40d2031402909882c481c0418000203609144460b081540c91094045101d5680506200103040c5070020054034011801009540c0421021071090340d224540180300c20000d40540840a54a51009401642c0046501003409041e200c10000740324003903440903034101c0300b0081d401c0c07400c8010486410b90003054104803640301103503101c40d18517095a8500f880140d40b2181181640002c0c1000d5100a4212203141e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 713858920 1250 713857670 713857709
    0x40b1f0602060a050105190303120f0f020a142515021803010b0d0f0b0714070521090120070f0902032706220b191a03150907 55
    0x10604900603e450101031003241d8859080105034650400001201030034000c0401c01300340b044821a103110b0b0307003e0001031101d900d024200240e42a2001c1102c0b040c1d00000d51031482503105903c280700c440150880b0781492100404030780380302d0803806030760140c850240042043c0301440601100d58008503204550391000448030340c43c00f141d262283c510075440c00080d4580d0b414504807a0b42c0300c6a0106070200120443d9803072071009103001d03011100300702ca00d40c0303d41002c580c503500030818540140700408040300481190352281408681c080104c441c14420030a26076000b0b00882c482d00545120880c3d0800076a020524040c5168081d404060102400240d0004940d0095010341c1c11301031120300c0200c07180d004c2801c0c00c1c00701035406825070015000440307074100e0100c14803900307801050f01038890440d9150005240382c240d0300000c0d0307400b110706402e210041034800e4551034450182040e00c41050000029100e41110460f022131994441c0007520422080c04681c01400e00c800d00e495a203240d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 713860170 1250 713858920 713858923
    0x200a0305060a080304050307060810150804060501140603040b090a0813030c0909120c050c13052a03070e0609030a05030c0d030b0a03060c030e0604062909040b1f0602 73
    0x1d4a0460081401e0704010503484000b008440954002900402c03100d0314005084403201801010042d490084840100b9098610106c540603081e00e9a150401810103040107411550b040e4416800da0f0000c12962065072030711001e0300ea019030040c420706200d07074407208c0441c01e02c90f40c030b40020700e038000c000384008460044030001e406403070080002c40c420b41d8540400400b1280c407200090000d022050580310401c0c418441e1480700351103202666044090040410b4030505200300241316a522442046a101815900c0703065640000f0284013024181c240101d0302ca12000d0718034000c2040880102c240c2c0c0d00c1d00030880d12004000350480d90b882c0b00d1820425129001840c40c00d4460041a209001017407290081d4401c4880c000d00346034032140303542c0d24800100a07004c0c1c07520500d92560100c0b05102c0c014810740b07104900910340402c1ca0340d0f24803480004510402c1651001141e4042c112580c5d4076281039055019034032081840307031034442542021308088451a00c0c0300c911440032012884660 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 713861420 1250 713860170 713860181
    0x6110912010e100902060409050c0409060306060608130f03180803070501060e06180106121e0525080a051e090c130c1b14030406050c0d05040b030a200a03 68
    0x89101507070034400005500b0404d565061401a41c089000d100034040c190055110540051011078551f20302942d4050b14000d03a4156401503c0d10765845104001064000300440c0d8413000e1600448140300365903885c203028822041000d0f04004810340c00481c0e524a580c0d0010241c80300c2c60403291264841d15140b0b002e030034540101014503e021000c00d120b410902e01201c04522292400d0b42c0796130805004850004019185102040e03c50040c00c501c0400300412203610035000ea4003164510b018000c007000c008101c88801d07407800e00800f02e5040298000b41c41c5400c81920200801c031525800c0745421044000c1c1c1c1d540460030203100170b005c1407003c0003460b101602000d94070924842c4402c00c04804a0f181d00070000d02080d08001c00040210400460058180c424000030345054080c0c100300746590010341090004c0340c0000b0320024420320401281c2941c0003585041e903c0c03c1d0070504282114000500a00340c81d940341c13034180009001c81329440aa02c4c0c0718a09498030703444000b42c01009400c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 713862670 1250 713861420 713861441
    0x708041a090c06160c0905010b0a050a0215090c0a17031c021e0406030501050306011d040203071a1e0901020c130f090804140f010f0507050a080a2303090a0611091201 73
    0x1743c038410001220030041c000d8904031114011200d00b4900701103401d80d017552282d01c001c000c50282205a04296800b0b59106000d0030700ca80040c1004220042403000c200004d40205424003013600850707100300b100104580204041100c0308048015064580c0041c0c0110b1365160000d00300042c40442e481c4940011703000700d400719030b8180026640d0b0018541c440c0401c1c05000a0185510b60300030403020700a02084d0014130180440704810703500d04201500110415142a4420000418115960401e401c4c3c5800d20340c45054246444503280010356901c2407040a14011074104801b001c205800f0b0340030030f0b1110041310040c40b1400c1c5030314014243d903101c1d00584c41c40050004c6c681c003240c02c0401380d40b05c40e0700c0103845e0b18060842c801d4007501c103904849d4003107400d031054141590010700482c01401900c01d9a480700300da0301ca003180d8074004801c0029100314050340c092003084041c2200285942e81030f42c100c50001031420010000c072803076100d4851682d8203ca02c2c8801e84181c4079055000c9040320 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 713863920 1250 713862670 713862683
    0x103030f120905030706050c090312031503150f130b010803031006050c06040b060a0f03110414070c020621180d05120f0601030603051002120708041a090c0616 70
    0xc948010703100480c0c400d1800501a580300303200c44400200e56911054000303484000c041e0912103110006850141c3c041710a42c01441c011003884105078a50006c4c482101c0700b1409844011070910b6088c8160703000403c20790307040050b00003007900b8103503203442003d00c04d4002680c0c500660310303504100e54a0b8400d0381c145c10a0344400500040403481442901c2d040790004010300075607199030b00c0e414a4954050502176101c1c80d020700000380400c100e1002c40055100300d090640c941d6042080204807003a040032044039800340010050582c1c4c2c00440d84007103941c12515a078440c82d540c2090404000120b0080c00b10440743ca0a011280403810100017090806000b2106802520041125a8020b180504070200e03154004160090070440303003254405030614000982c0e5941f034845c0c61810040d4100c8407040f41e400034208414480070a01c4a90054807820082494249a6610140202414001c20203000824003150300c401c014440354001c014028400c5071140c2c10300f044101184076151048484 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 713865170 1250 713863920 713863937
    0x1c050106170405061501211406060901020613050a061d070614090123070f050705030606010e01050c012c070f080309010f020307080f0904050a0e06180a0b0103030f 72
    0x500c01c5450080c41150b01c0005410b050701c84002d030b01ca0144000c0400342c1405224110a141c03a102035001f242c1c2c42400010102d1585031001c9008198a4040d0840740510030400c18400c03aa600047c241e17400611082042943d1107107070520904140b031120000300814108103800100c00768058401341ca1074088815114102c0d46c490081d124820044120300343d210090100364802d6024420b010440c0c801a03401059000d24003039a030070140e000b80d0046030100782848150041c06401c0041c40080d1805a00800321824043e0020b810342c54800400e41c10041c0008410405000c00c0d00100c5480d9551207682040081081011501900c10091111a44038121000030b00d0b4520306001c0301192500c4003c1c1d803500401c00f00454440307003240d11803001c4d40300400841c000245201d0080001050310380c0104e4841014000f0071050320000751a866006081c0b0a040e482400d001c105280c101c2e000c560301c8210003220303258081c06c24a0b600006095103a001c40000280342c0c003c0424102c104466440c50036 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 713866420 1250 713865170 713865197
    0x71203090c0512071e0303020d02030307021f380d11042f12070201151e090f0b091006020d031d0a0302100b0d0b060f061c050106 57
    0x110390302a203016200840703a031030801180c1810129080801e03e00380030360700c04e02d031034524402c059014555075032039180b00002d0820a25605204000c0050000d2001e18075500740048004e56a84960b070080380c400d4200c00324281d05104030b1b4407026040300c5501c0702000008044201040547c10041d200368102c14180700035496280503000d11075000c0d44600b05203140300c049814007005200d603c02c0b940c1220f84e0300640701100c000f408515044c80c1c410759112039544145028540c2c441a000e0720800c19a8186084c520100c0140c16104c0c041d915203c0d003580c01c5d003002c0302804054000d540d014482c000c0c0b030180550000303000c0ea0400c00002c0700c00d641d522403940f00c01075110102c0646100304070041e0080411201c106110703170003c0724806141034180154803341400c0500b41284558128096400246030354802130803406885a200e908546000042d0400e13100e10300c031008000d0000e4072411001c01000250745e01d041c1a2040540e01072a81c0c0b040e101554a010004c00082c001d50003c12012020240c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 713867670 1250 713866420 713866427
    0x10f0902091809070905130f0b090c0a03080d0f05070c0222180611090117090115060c060c05090d030e0301090b01030b07081b04060e011205100927150e030f0712 71
    0x10300c503071011449010021039150a9202721b40a030030103110b80139443c03241c02c2e00d5480b407000741c0c09940aa14096690b1171078034403000440340c2e610410308001c0c0c10003080000b1950001548241c0c10380546030320801c0c22446a14000c985144808000d455140c0a00921520100486030382c20341e1280710b0400540c45000c902010320f01900b80114000b4041000c03e280000b0010a8250460000000810026141c40a074004894140c1015000a484203c0d03007061001c28000c040d007000d042c4c00c0c0940307010071400100382940043c01e070240501c05000c145184588095000c0140316400280c503200380d5860f4901104441d6095505400191208011030307111941d5104081c0c0200c1c1c030b000b10718601454850144e845504a000c92410b1003039032031004213000d08074020b4921815130202030340c0c0700b1410580380340300f280c2c03444404018418116490001c1d40b6880c10300c0c00034540d0407406c031511039244016a807002d0144802d006005000c040b8911046580c81c102401c030592003665803200c140403007642103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 713868920 1250 713867670 713867701
    0x201030e121b012706060503011803030c14030106050f0903100914031c0f021209011d0f1e0f12040f0608090601210212070f0e010f0902091809070905 66
    0x3405808044d010050780981303000071032080798455000400c1180d590800030b403c58904c4081451404c08540810003090b51510605402e95800e0415144190f2601005481c2e4001400b50030240200006d6840e111483c0609443d60310030010100c0310b440c0c050303031507440160001311801c031030955903ca0000880c1c0c0c2e0110584005c2c15072a2408511640d0040c6a03d002d020003240c0074000d603508000d100009440070204602c2641c20300008580e14007110418007030850b480c22500c4040e0007080f2003050440001c220315031620f207541e42300c10a41a9140da400c1c1007075a1070300308445a20504000a00c51040079014100b111200028001d201d5652041500d64040840e5018216000480103000b0114151901c50100240c2608000701d02c8059011809040550303d50341070310313400f071a010804806041d0041c8040c00007000e417222070307501d48003252014510a00901017a5500445e001049031500e504401c00e81c034000510710614148801c01da9202d008600554140e141004c0015113404411240c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 713870170 1250 713868920 713868941
    0x110705010e2803030603021e03060105060c060402040b01021f1506050a2c120c09011202010504120515150306280504020a0b0a112a06070201030e121b01 67
    0x528000865019100100800b4411000e050b40e40c0c10100c00741c4c0f101d0171170315044004c8140070113129409078201803820310140e00c0b0610649082002c0510031a001c955070303030081c2e410b07280882c514044000503410011030541200200b503141d114424201820707048582c2003d10f40b018091b886403200400c1f01c540c03007510a9500030401351540240d044c035501c0d034000e500269002c02005000344a10018509081030a413021095100e84804407562400d10105401031114030000700c09600c141d400a07107903000314401c10705855154103403401030000030f0001c4d000e00702c0200c40c462000d1030f107120510740d442e90040820b4024030403c00002c407407510000c90741e298640b0020a42a99844078103072040901b600401c100d800802c01c00340040c842c00d80f540a000c02d0865038480360030404503070b0765441c80c0c041d140800d041081c200240101d9004026100d06001c3d000c1a40d0895544c5102e00050300a01380402c00500144541c3c1696050540d5120280103d000c54896040341805946078072402d0354455641d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 713871420 1250 713870170 713870203
    0x2a1606090b040b0d1401080c0411030411060a0e0607060903030e070806010b0a031d011b090509010e040602160308010501020c09010803030708090708030d060303140309060408090a09110705010e 85
    0x10500c51461a80044c041d100c416520201e0a003600031100b600041c4280c1c480310a0754840500c120302c2e49043d020380c2c41c2e0384a1290042c0d007140340c19150380d01d814004204d424092840001c0c0805198030a036901c04501d00007a000c0c960340c650307919003800140300a0200b600040d207842c2902c899283d022412008991190b801420380703909221507840b607a80804504000c0c50b0750f425100401c4030501025450740300208000141c04145404106109004da0321000d04000f0145c00911007030303a441c9002415600b0b0440c0c40145030360745290001c028400d4102620312a840340f0202c0c010168021141410307a8000c0e42603401d0700b40c104090181c0310b502130040c11001d42040c80040c1955204078102c5500c1507281080b030350515961454a81103500642180080c55140c68041c41815040180c912105001080c510315600d0400c03641038564002078002444c1100000c0c03c0341040da2000514409806680d1041011610450000509a200d0001100c055007001d08002c41010041003074405000c0307650 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 713872670 1250 713871420 713871427
    0x4020d030e0f0307080f06091f0b04241502160e040519050102041406040b031308040b0c0106090b032103060a030602040909150c142a1606090b 63
    0xd8054509803400016150010300d0704141c521296800c0000200400403580a000e9020300441c0d19824110010309841069100031038141007a120030700242e128060890300069400c0c80440000c000e054a520407528030701103100b22101c0b60050011840c21070b40f400001c0d04541510b0034099864164102200c07001000000c3c3c100000c0c01101515540f02e441541a203e101240c40344010044c80546802c3e142c9a501040c1442032112261001440c1e00084500f181042e140c01650702e0f81c0d101c0200205001d031074005c46e220400402c6c005031009002924034158489078280113183c020a003e00c10b42407a42c2c02c2c1401d42c0c0e800c0c00c020441180844807001d1586007121080c41850081c0c5c0054091904002110b2000002c22440d10141001d0110744602184980140c2459a0018036000e201800a803814070890141600719102204e244404406c654030380b0307104d8159600012600d4038048134401c041d030394902c4000c030114404203d60301d103101510035651549011101c0e41030500404d4601c81041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 713873920 1250 713872670 713872673
    0x8091207151a0a1e12021314070212030606040312020703060e030711041107031116060306030b0601082a04030c030c0f0e07020d080a090204112d04090b032e0e0604020d 74
    0x642c41031420030700241c249440c1c4287d100180007141c20140100d11501702460a00806aa041c800b01d1000240451070b18214200130000030031170700c80c030720008142d100403015100c0e9541c002d015000046070004800c002c5561851082c075241d500030704d0211201d05d0318a060161601d4540301da0603600c034070085001c0c20800c0640d001d40d2105c0701c6400c200c820388141c40e2000a20300014201c903000d4209654081440d5245141c5045010405080d00341400340c85420010f104641d181c05d0300301401d11010000c0800c011405401c0d07039200d1038002034056440340b10080300f071007105845841194000100080b12664502d070101921505031640c10060b0043e1100044540c4100b8a49400a800b03900005101d08654001400c951740c01020a40d43c0001003003050741c00501c00520450100c610094048041c42e5400d0702d80103120364007414010030368612040ca4aa101046040c20071416060b081c00050144100603580007044009040c0c06801c0c250554804003011902c0750207030b41c2c09409030240d100d06 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 713875170 1250 713873920 713873939
    0x7112a01050f04030b1504050c071a070c0206070602030916030c030803070908150403120b0a0b13031e02040b060405130915140a0c08091207151a0a1e 66
    0x28042c2528506414040440840d002413101805000645522540e242004003404190f44008100c400392410a00c061404110001d0316400c4900c440761102600b5501d4440079244500f0500010b504140003003103040411189a0055000704060700445100c01c09003900fa220b52603017808000d040701c1c119001080068140b402a6420004c1c2d03017056a8050303240c4255034a40b04180d8042c08480c100c45007031205264002c00804501d0001e0981404180280408101075031264441c2c1d03451400700146170b58039100010310110180d80c1c082c3c1c030084408691083c0c2400010b107100142d12072813810801c0240d0f41f5000d070031103080340c0d400340219020101100c0703807500070940403c040d40c0b02000c000121444480a128000034002c40c0c54110300310b170400c80e1203e03044401441310402803008c05814411202000903000e0300b0080054549075881d90545004001c2c02282c0000481940c200000c030040707201c2c00e00d4440a4035009441003807103542e950703110b42440c0300805c0c00040d41c540c030100244034031104c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 713876420 1250 713875170 713875177
    0x609190803060303040515070303062c0a1407080106080a0519050901110406020d0905040213030b1f060e090f060f060705030f030c03090d090803030610030e0607112a0105 75
    0x800713490a0699550118400c904a01008002000c0000b1300204050309840742d44041c1c800d401041702e4000308100c52a800681800100f1503507094840020700802e41034101c0c59008107850300040c2d150400c14005004040c0038001c441c04921084002410030700d071072050f6403044021855244007111059501d00040c403020304040c2c415501d0700c600a91406103d03000f000102110350050812020450004100d210680c0025108500410400c03401580c0081c2c81025260000c0c800429900c4460441a201d8030b10000080841c3e1721400004041b40c110710103140084040e200840590703201d001000120000310742c0309511a12640b060b18031810141c0282c01058803c804403460615501a484030036041150b406510040000800203540000e100e01205061141001d10b9410b00380800c20362680401003299010390300c4811640c1090b031080d00070500c11002c03541035459500700041300a02c010440c03100c030102803060606040ca070f01c0000b05108001cac0350111505510303902034401106d2590 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 713877670 1250 713876420 713876431
    0x402160611040f080d2f06041b0503070f030201050f0d05010f061e08221a1b031006050f0d09050d031a060f0a02010b09240d0206090409060f1401080609190803 70
    0x586c00c1403038207110081066500580c051410403081c1d1100440f8105107801039048039000390001102081524030001340c0d0019170f40d090030204d0304c1e0310f6250109040c07030085000c074520f41740c14040001080c1c0d007081d64100035140c0139600c03041d000c1002800d100c2c501d0010300010b40011002d80c0012200c0e010361b00d010b5041c6009403103000c801500b50b11034401114446880300c808011402c20f21814448241903020200c80e000c0c5510700b076282000c400008a6031074400c020500c04002106002611380004440c00c94101100070010b0607224104a5a42c2541d1420500840d151501c0001c0203190b90300c000390120b0300103042500d4041c0e590005000e039000304192009640d20340c05554007695440c1281071144029a00070301b0344071682c240b080415092400d80c20f02480d100345138203000d80c5407001181d45a00013501c000c10200b03c8d614201000f0504d454071070048074900144241103948100d034941c12181c0901c104e8180340c4440c0b15070350322800b0303407510f4400e00010f00082c1000a2821000703180d020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 713878920 1250 713877670 713877737
    0x302210c0d090605010f120b0a0b040b04090302030702040605060c0304091a03240709050901050609011e05090f060c06041b0b073009050402160611040f080d 69
    0x10801c5401c04103a4030750301411a61a0340f51001800031440260b503220040410005401c81004140c580c0d03000c2e0748014002d0740d00f003034a5a0000395241c80d640c0040c080808082e0007001220400c0c01e001307469400c58070301207100d0b5040c124002551714041d01a544181415805140b5103842d01a8110013131202c40401d5001c485581c9061400d6501408549602014006070f41c00b11405043d64013202440100500306105082030103012907140e207440716054413010358402d61340300180001030310507440040201c95800c0300002241050707548003000d40200c0310140c90b4200394000000030040a03000310051400309900040008000c240064143d0001d8100d034010781c0ea111340c80e54034044c0703e030344000700940b011652105000c2840c4041401c101c0702c41c10a10310001c40d003a01d6007006008803102d1003458400d54011458410300f409010380007090b281c0c00700e801c0103015100c1100e80d400b90458401d00b0240198103000144510b000300382d082480e4800e9540240480c651020000c3c1d801c8103449580d0309 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 713880170 1250 713878920 713878927
    0x20f03160201180b070320072c100501030b06190c0218070c0b0a0c0c0210030605040e150709030807020d0809040c02060f090a02030a0b09011107060506100302210c 72
    0x78422000c0c10760150602d02038007907a5810300d08000d0070782c60795400c04810151001031f40e090229004a01681a9a0b05060a02e010040c0309200c0d20030b154a4000030310f41d40a90000d00040c40c0540c15844200d640a1724140460049401040b803a400741803000344422680006100c1407a201d90180140d41d44001d01d04140740c01c100e1035840c4110802c56124020a20801e4000280541804104d50018000d0030038800400c5182e4010008011040700078014003915810000c020700a400ca00d01800c009001000b007a00c10103091070341c4024640000026801a4010600302c0c0e109001c080182d03a0004c100310300c2c0c000d86500303101d559807849001790b1700e4000c248480c007001d6480f4017a228014145074018001e6040801c07080c170000d8006407062910354800c0250b0300050314045000181c09810150310002c0365203401185025000d4585600c1411310001980743c200f00c51503200501442041c0c03201c00210301c03002c00541c100d00c2134441036802100300451a4885081e1a507c4a0340300d09903202c800e06 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 713881420 1250 713880170 713880197
    0x100207030806042007030c020a0e06031b130e1e0c030d050d06030b0f04111f030e0712050618070311040f0f06120201120b101805090a06080d020f03160201 68
    0x11242c0202c0340440016075100301800035403401e01c49d41e5011300781020303604030607003004000266034a00102c103101400224608039506913540c00414800101c460701b080c000c945010441c20f485646004249040d04c201d032800c194011400500381c40054406001080350707200c10242a100d03070b0400e4041e0303024141c44090200c001141070041a0181da003041601c011030a0501d45180c1944005091030301410303145a01901090011444100c1030710142000550036003014007240c00e1140716000303100c101075165582e004100e000154030f031044900e80e8056184190f914000c94503441c83d84005004000340f00072800483c40d043d4840000c5c0f03126601c0006031506020a0101a5822a0301980b44040e080c0c00030029942c1210301400c00c070390180820020902080d00159000c0c0031041424100b10a684074000000008103020010f00401001c07100245402410240a01903c0c01041914010203144600c1e060000488640000440c0083c60030601c42c0032071064003040c200402e904004920000c0c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 713882670 1250 713881420 713881481
    0xa180f020d060314010c202b02070f0308040603020c0f0a05071e05090f0c0717280c1518080a0e010809101a03100b0310020703080604 59
    0x9500c0d9401c002190052460078000040901d0807130540c2164105410011529400b00c09040ca01401e02e044001c90b5100004c442d180080e0300c00d0b0050128424641c0c150b001d034146090407201c603003a60896810340d40300c0e10305d6200902141710040030079005105c24080240a81c010703000c0382c2410005c40745101071100c01701d850f02c030700d4010548464002e40c5090141880c2d4900d8004034802d05401060000e2030100410310f040750003800d4008004260b00441c0079100300704220380b01650400d0141941c090714030f60139585540001c2141110b00000010b01c80d6a0044403600c0c1114040341d00c800501040f161502c0b110a026150959110356440402c001250024000c0740341080c05840d4460321141120300c090300822060444c44e05110f904000c11810020004028110050300034000c11168005240c021513005001d040a41c1405003010500e4801001d074418540d2203021003c585c0c4508c103040c01801244140c000140c00144580009140c1c1d01341504a0854005031694001291194600b0030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 713883920 1250 713882670 713882677
    0x18020909070905042003040f0219061d100e0f0f0d15050117191502030408030609150a091a10120507050f040303030506010c05060726060a180f02 64
    0x340402c070785400070302c074505142c400c84c2c0e0b2030301840c40340c0c00c0300340000c0311040014080140003c201c0900301840204544500000d560b5001490603603c01041e146c00001c0d0100001810301403461101c25a1503200340342524108407102c0142d1200d00c0304030414420300800c8a0380c00071081c2c100c10b101e806540c1549940360381c0040c0301e004114040c441a1240350a0040e00c0c1c0c1a800580351003900c95a200d44c94201280c5480b1500803e0403264680b00ca0380303490313500b00702c0b01e02d40c0500441c8080100414003540c8001181326210485100400d0342d42c410042c1c40113202c0030070300c0340c20084441c0c05020b01c10656000c0101d40e141c0c00d21052031a00c90800140c003101890400d180011f4401d40c0020704c2c1715280c01150b420a0580c20410700b46004011060214001c500c00501015101c8021400300e9002e92401c2912941050544141c1d1514030b10180900501c207140b5005512094104401480301c0c6840701d0040c10003d000030b4401d440d0038040d007002000005480c0360301e40d6980c0b43c1c0c56180c8007803005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 713885170 1250 713883920 713883931
    0x1142e08120901090f03020f06070302070b04031211070303080a09060f11070212060f07140705010608030a020c01050301050d0224030406090b0105010521071407080403171318020909 80
    0x680da5126282e02c0014407044c86680008040c5a5007441400140c2c0c400700302e0100d20f80c0030389265407030f0522414202d161940c964007403c02c0020002c2c002c000c1c402e18142d40d140004003503c403580b0920320401416950960b510002d00026500d2006c58403a4034250440c41c18580200350109030159003150040c21148200402c880500002800404504000001c180c449144002410032841d00564142c5d41c040300404100420200e901000b4503100801c0507914030035000402006183d0300c424210795290300480311000503105d4005003094a43c030800c04c1301c4c140c410142519810f888a0b60901440c08070354210100005070b00042440c050140002442c0b081d400303400e0208035031106003401c004000d8103070081e40c10020200103244001c640307111100083c1c0c48841c0c002c03001d541c0d501c80c11140308288a0920344400d400090801c184103862020708107403400352860000f1090358101c1c0b511144184058103024098032541007000c002986a140c0c84c4800c01800945003e21940009400d864100d61 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 713886420 1250 713885170 713885203
    0x30a0e0105090109210b13120c0c1e080105060d0f0b1b120f13020d030e0303041e090f09050a121e0203120a05010501020a02061308060702030c01142e08 67
    0x171002031101c0d200025800c100e200110180c0f00300b068460024580c00c40c81c2c0b01302440b40310b00a40c0200407010044c5001021900510b18002d040001c203040e01000d40e10980c180e5609000c045803080c03601036020b601c0a90300c020200d003008280c0d51180711001004005092008500c482c0158000308100107206001844043c91054035000b20b0360307841107501130b00180c04042c0144400c1c5c01611410301c03141100b9094101050f15215190020b841c40c41207400c00c01d5003054000500b800c1c0c0b428a8940002c4d5560924240101503208202e8003c84585000140895205141c0040450088641c594814500385030404001098141b04503121240081c0d09006030710008414480398044009590043c00c0ca020501c10b9515140000707640703500c40000039200d100009002c0b44d583c0300502d1050010031145049e00c4280c07070b141e44065100e40003139010040039420032480b110300700c5841c0742d201e00c24107965042c00c1e400c900342c0300c200300403120311760760015281c07010040810038400c00c01c50600840c12800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 713887670 1250 713886420 713886479
    0x4050907080319120c050d02370e0603070203041a040801060b040302030c01140405040e15040507081e150a02130b031e1611070312020a0311030a0e0105090109 70
    0x1a0010001980d04c41c1482881e80b40c06401801241d201007120405c558502001d0b03110b2055440034152507080021004003404400c0d02c154070803008000e824143d600c1b0351603070407002c40e4601c14002944000c6600c100140c10400c0140b0240c8004200e500c40b49440b10384c0982044d845a0240382101e1b000d411400d10000041001c204510b0f08101c244074511080c42c0601c202c54183c05614140d000d14003840b4450350303e850038a07842d0300c41044404800403040c10390110f10300b03150902544a88560203507403554015400806c03034035021307c1c0f07000c1900e042c00d10082484e00401f100d400c4c12800042d0a040c840c40d0208505101118116402406440080c9010351b99003000003400c802c01c1040500720042c0c20f40310003040220040d4085944181032b803030910103d00030750003a11504055460704000c2c1410420f0301c0907503030b181d400140c0c0b047e22846034480001801d010008070b0790364000c003c8503000191110004516951007800504104072042c10146880e64440818622850f000c1561428802010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 713888920 1250 713887670 713887717
    0xc030403140f0d0b0607150b0d061a040e12040614070f1209080f060a02070c03020d0804031a061012110406120f02040b030a091a04030309050d0801080705040509070803 74
    0x10301c14013407035510031118180340142541e18540c00032202c6551511060360380d10340102039203440b1010f10303aa0b40d0105007044020030800c10680e00c01880300c4442e004515101030909959030010703004420840102d45282842c0c50000d0481301c40e82c0c240300c24203034900203000c110009a1542100120356114410300440e0381309805000b0014840c80e03010460076841015541643c3e000801d8042d00100d100038056602c140505013006541500d81c00217421888009003001841640400390090300e10402d440224031007007041058001d6810b50b51580d00c842c6502c50700c0240b81c0243d10481e4080110a00420030840d0180e914a454000340c1c024000702d402c080d100c03400302c041841425500801814110b0900c3e0502810464070300000780350100d092b43c0c442080c014000d6002a031210b20804020326005441c2518008014004081080f281c0d80700d0250050005c50060b04882d05031220040105800703494801004054180608520300034010403501042c004420b000030015000591104480c0c1c8031507 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 713890170 1250 713888920 713888947
    0x31b030903010c02070b040905060f2d0604051030060e010f0f0b0a090824060a14010c08250b010e0f0103030c020f090f1803070203060c030403140f 65
    0x6100c0d400f0115007001400b80a801c16100646096405501d80000d090f07540c1c5000c581d55450032502994441840d00945c00c0380c00510350926038040a04030310164028280060007914041d6010396644644d01c0740c40c010600b8410030740760002202040301200002440001e080f10804080191a03080c0d032202e1080c4100d41d84c0d8003000380141030b120b0910810f940f912910403843c2103640104094200001911040c0603c00c0740304602510780303681680c2400001903400b241c08000d801f004503140e03141c903000484038981001c020702110803803001d0901203c3c1e00f03401114610b84500d82118100d0090040030082d10b4810818a0f06000355000707a81e4080c041e007040b40c0c881c1030591108240c1d9407264108241d64007000b031580c0c1141d03494140b242503d07400340b0014004c281d800c003400780c04c11880e00030012440041e80c145402411304400c0303242904220030780a0748070b2040000182d019400200803441d4199920002d44d071003402854a1920316140b0b101100095025208000c111003000c1900c04800aa = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 713891420 1250 713890170 713890181
    0x16060c090501080c030612030f042909010909020f1303230d3f05040309060507050a0818030703050a0c151b1502160512090d06020705031b03090301 65
    0x9007000070042c074090b40074100070b02c402007241c0c2c001e010b5140047c0d03144404000f0f850b080c0c01880000b54075162505480542d44c804e85050748005504414070344005644071040f00d00c84031060303440e0102d041c03c140d500006580140c00c902c8440e24104409840c2162407403003c8050746c49800d904a45101620605003010882c1945064603080300d070626849541002050303568020f80e6201204075111104d800e100c0c3c6c1d144840801074000c22004000c4a0103240e800188100d100e0340314201d0303031503c60f48100e030b850161440c01032440d070100b001440411ba40c10081c203201040050744200c200f0b00341d00400d0034060ad6500498195001c547c6c2c034800c00800402c00742c05820241c0d410903004070b100d10001d0603150383d00501c15060803044156818030684800e0001c20b00e48c01e035000d55403489100c07c11840e846402c4429940ca00450a4a5981104000444044040051680d00c51030b91a4a07440700a40c4034a04c101d545d4802081040c59880030340e03a084965465110143d5180c0f40510141742c00c1d01c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 713892670 1250 713891420 713891429
    0x916080606031b060406080430121a15090a03032307150507020a060c0e210c0112020705340308031521031309110904050402040216060c09 61
    0x24040403603100f2988480058900b10783d030a151800c050780f80c9051084400d1101c825894000c030082d48182d41d039000111414140341025038404040c0075040e0716a4084480c6014806007404a210112406141c031a42c4441120108100e00b4506201000080d05d0000d00363f2088000c02c411020300c04010b0881e00819031440030065001c1c0c031300a49642c88400f80f030000340b4181d20b032a03074803004a0b080394420005e4003403243d8000401c2202104d07640000d003120f00c0c0c04d4409845058500200300349801c0250154908040340b03c01825100303181c00040d520f04034284c01103040f1507400d00610700410420860a00505c0804d442104400064409205121008070800a91803220320382080090482012607a01ca8040030081d001100a803001841c0740580c0c074034a686001c014500c44d075440102000500306144c0ca144492912a5aa000134003a134066012148541c4020700940d5080d090a4100641c441d1000740300501c1c2500c249481005405034070015a01ca991302d071818060540c010901c0c00150 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 713893920 1250 713892670 713892703
    0x30312010810090b07140d09060605190f0311190b03010612020a08010314070e0c0a110a0507060503180d0e03100b090a090302030f12061c0305030708091608060603 72
    0x40f88030346030039141242c0075144508100f103003801c185d44a06c4813001d4030341e420407100b01400402c4050902c100600850f01450313210b0b903103690703038a50b1036840780c404031044400e120340300001d1615540758059520381d2241d406030009404900b00303030b00d007200c41030301c1c6d010744030402400f0303287c2d410b020006040b00d02403002c0c5c403011441002081212a0005ea100341180e500c070041c1454001751068490a01200d0b5001c5246100035006000d00445840080c7c00050015642c110425869103805550b038140d2507009003181d045940c041c0b0920f88100c0017150702145550b030090f02e1030440d0300e240c1d00d429131000c110700004480d80d0460525107030520030000c40000864081c001748203c130001460000d000341682c01303409d650b00b5030b4004050081c800c1c1c804e0403803a81200c40e2512000030081140060407900140300e095001e031201c400440c0004d81e400741640582e1854110355401d807054a40d0303000502000704034440c0741c080c2211464681c0310b0f070001e03045680c054000c80c108402030524100180c40308001743c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 713895170 1250 713893920 713893931
    0x30a110c010f1d1f02060402041103010b03040303020a05070f030210050705190c060b0603073b0603040c030813030c0504020304170304060f050f040b15030723030312010810 76
    0x60541c050000303100c00101021036124090800d00256020302914000c00000c2c80740501310311010b0b00840c0f560700c1203000380e81c1402901101d0907405402d200074040d8030f40c480401d10101d000310780311380e0143c10394814505119141c01143c0d1520346642401c104104c0042c0d0120b0348ca03144003032240c040c0e150071050f035080c81c1c3e0404540004103000c10f00c0000707107182004002e020318011b00041e500300d19140c3c0740c09421310b071b500d05103600010400c0401000c1207103038a241504444061302c2500010f0a1341d20014541d50704180700c0b00802c583d0b41d0001c0c0c000c2d1207030034128202001042d103800003001c0442d11040513907903062031481c114202c02d607140d006a1003180305108003c04a014040c1e0100e0346044040b040c3e0356039807030349440c3c002007040104410100c1e107440b080128025181d0071007402079015440041d03c40c0e949003c90651440580c0c07280350143c00080040000c101d00215086501800829803601d0701134110110740b03990440342d00007103411100341c0100140c1ca4140240151002c0c960400c2c8038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 713896420 1250 713895170 713895197
    0xf09050405040c1e030b150d0803010f0f06020d08010e0406090204050705090a05090606030105090c0f0a0203070201090b130509090705030609071509080a0b06010e040207050c09010504200f070203030a110c01 91
    0x3031602c00201440c46550840e1f141503140e41e11040d020140b83c2d80200b2460b12541c46600500d03c0c1455170003031021103001e0620114410340001010841c00d2180eaa600c0900c0e8245601da0070181e80c09481112800c1c0c8621915006a665000d028881c01c0b09550302511050800104045402c0560146001d05400300a011003034031054110313419194203461141c071503124451341e03080780d20482d1782d880c16150700800d5080050354044000c183d818000d982d1000e040392195683c46e264480c269004225501c2080c0401ca9400c006800355030041d16602601d400c503560788007181c10007400700d5514040d500454000e101c0c084a40c11400041c000900e0242205030800d2001d640d20380303c50202418006a180c006061603100d880300e09c001001c003500c02d5440b82e416240050340c0d5030300c003081d1a104215400002c585801d2500c03e06200740c00c06c6441410400f00a0710000c0c060f0301c4a01c40d2030303828104006800c0503840c02c10003080070001ca0f50b0740d12840713122820799a00b02020500c030141040128240c085 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 713897670 1250 713896420 713896433
    0x140405041404020f0f1f020a1a060a0b03070806010c05010b040218030d0305070c0605060f130e060a0213052407050304150c020612060a08070914090a020604060f09050405040c1e03 79
    0x614a003d640c501c00e490f113a200b509a02d40388c0d84010040440b00d090121640243d0b141c0031030340c0103c200741d82100026450f5200f201041c00122030000010782c611000500e203620459500c0c524078058030002412003111000304003680c0c00100c1e4003026406028001c89181801c011f40350341280c27107280810840c1400c100003440140404000780200d610351020901c0355492603840c5140c0c030f000600800415004c800040043c1040d0380041c0d440340541e50000f100d1541038005c5031001200c0e5100f80d9038140c200001c105c1003070280d0140d1899041241e0000c4400001d802c0140b01050186005517207851500c50f607070500031495040f40d0100140c1c8800e55005880e0401654180d880751010308035103541d082c0100300c40d485c40e523020445501c03030407100192000181c1d108005410074542c181001d03a80344513600d65903045280000f9081300c000c00080084034410442103410141a1800000d65545c40c00010207a400c1954203444e020340c0d088041000908801ca0054400d00031102e000c401c40ca191a40c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 713898920 1250 713897670 713897689
    0xa0212070b0313061e05070f020604030e0111010209040c030e1b0d060b0f09040c0503070b0306150901110d0216050118050f0301020c2b020703050d140405041404020f0f 74
    0x1600c800203000001d030f0400c1a0b039042203101c00c208030240070540c510b03c810f080140c00161403550124000351032003c103039032000c1034940c41140c01d034440641c0800004011a20143c3c1c228802000d55401c0c05070715030550740d0340280e103005a084e66000c955088d003541000d0801a1450303000c1075200f1100345004264881c61505081207800a000090b17421203040401c40c00c4407044407066201049404000400002000640c295881501211103280c0c40e05056030043c802941c100380d021444903090000390707603140005d06206c0c5041c5048442103042c89106850011819070503409a00520044c00f041500820628001c01091911405c02c0ca040410321000f8506400750350300519400f501010980c03000d4041702ca1030030750030301100c0000d0802c1c041070a00708138682c10842034544118440303180c83e100140050a50341c1010190034007501c04941603410f00b085510b01650b108007400f000405680714420060300002100d0b481201d46454030401862501c1030071550711030501075040806640396000030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 713900170 1250 713898920 713898931
    0xb090a121a16020a0f111c060605010c02150307020c03060a0c1205011d100b0c011506030b010225030f06022d1e0f030108070311030a030c0209060d080c0a0212070b03 73
    0x1078291710002410103088402e0303500b076101c2d0400001c039400a0340c45d0f2665010070300603008002c200442d0b611440110f60081c1c0c0703480007943c0902044403034000350000c0b0b002107411000e180110390416074001f02013820f250f000c41d800c1601e1952021802100b42d084000300700b18195151040001d581400c40c003017010800403010a1221070200d00059404180c20095000707400c80f014016103410750041c21034080c01e480310b05c60441c0c1c4103004001510074000d000c6c0000e8144160040d000540e11006455011011646d07200001e10902c54000b02140e451101c2001540c05a040542e031203030451117031200b01c50100e482c2a089000d651480586030700d100180c13910015903d000046104d03684443c03502502401d0080c00422074000000550000b0014070103007100d03c24107d1469040c5c040c42010380b50f008040010b80823401c0030240c0303001890710500d420b40c0214024078100342518245c840396183d8004407041c51456005820880a42c41c0100d0540030142411005010050504071014901d0001030417 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 713901420 1250 713900170 713900183
    0x18060c070807170d06050301060e0714030a09020418030201230114041104080c090c0421031205161403010f21150b09090109020a0b090a121a16020a 65
    0x141c880c200168540c0ca9030001c8000000f86882d610245840d0000342020b2080030300c80c3d841d013500001c7d660703801c1c8201440340c0351903229080364440c12004241c865100a001610b02c50b03480744d81800503583d902c5103403921100344a000640d80c0441c6006421904c441804030405140d00b03202c804d03441901340c0c8041c199100a100300e01000300384030214000d014104407440b40e440010501003140b00380002c0d00182031000f103030540196180c40402030490300c214014030440783d003d0400f0103802012a080074000b144a80752040020b2006480481126006e98038826000c00700c085210300954801c00210b02140001102031540d4504480781d04500841d02c240005102c800d00c094003401281d40d00c5102070b680106018401040c80f800c0e40000701031900059124885440200388117003014811450100d5001c0d01d0141c010b800e00600e0321154000c1200540d00201d681d078013041c0d28040c070890b40429481403824100009604010041c2d69100802d5030000b140b000d0640030056900143c1380044a42000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 713902670 1250 713901420 713901427
    0x10b0306031b22050703060f080309061305131e0c090306050c12070e030105010b0909040b0c0c0a0c17011401030f0302070f06080603010b011b0308100909080318060c0708 75
    0x30115110f144002425400c0741d0382c0541440704103030b03140c01c1a03115620656040010503241c000031026508907000301c824070340c42440901f840c1c1c20260001c104950540c10f41d03141c0c02e591100004c1444004038000c1d1016515051512014004000c0b58944982c8003041844502d5000d04000c006041610000d08015100c0010403c02d400c0c040848290700285483d10589191542c0060090b0b405060258001d45ca000000901d4001c038005440c02d8940040c0380c081a601c55441c0c1100081001d0810f4400310401c0000126560742089441c610521800003c207181e03180c4007103d440403002400d000d44690511010566030f00c003408000b8156540414684180141401d0407840c3c003c05401064207a84a40c10100345140c10882083c41150201c00034001c85006400449160540381107454401001c1600a80080e0040c2840383c0d001c000f012811900d2640c501c00d40062340c0405005072401341c4c000090088007003824504c0311881030000000d0940f8105202d0100e8244103140b00a04003d1010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 713903920 1250 713902670 713902723
    0x1903050123042f0304030e0d0b040303020c0106080d11061005031c050f03010f0e0901110301061b17131a040e0c0c0109141006050a0b0a020319050d05010b030603 71
    0x12205400c00f644004041e03002014007829000141d0710035a01500032031311012168480c7e00d0300743d854600d2203501000e210a50348841d5000e4000c0e40010000204035501c4001c080340d0702200700440001200e26030b4918400c91403a01b0303602e0070910050f0000c2074642c1e5804051042ea02e0015224260300d2103840b00c004d05007280d04040340c01c1c0c000c1c000c0c459010740c0000000194204030154100070f82e400c0f0403250209868850330182241c00d00500d00c05503407414401003000900840b6105041c039030041100702100d40381e640c0ca02d07640c0c6291084500c100760108006150780c009402d0f560207803003000700100b0f0041c03140d1a00c07002c50040d441b0b00b4070800e610000040702c5240c400d081d541008003060080c09611030b1032401020600301100a8155032250340161134aa00c1140101000c0710006030100420700c0c00d00080c1c203183d40c0310201c550103500c000c03c0b4250f503e51481d0101107014109582d100e440e150010500c2099503c10390000307640020074030520110341d4011401004c460b4415002c0311034031402 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 713905170 1250 713903920 713903951
    0x10504080a0c1a0c040e0916052205180d0512010509040201051207020105060f031605190b1207140703020d0c2d06050a060305100f0f02190305012304 66
    0x225038040050303084407090100f0313500044082d000740d80040c40d0303039850780c0d5444051564a81c444c411034422907003c5042085541030121007800c00520300300d1101d03021204404d4407030584905407a42002e9034504800890b08230800d0001280600103440d004e0300e0710707031403503100c0c1c0150744180502c0b0700c6200c0b0000450704581c0580201c500d41c1100040149007858801d802a00030481120190b004080d03150344000540b80100e8880a14400e118150301c20304d00f803205006880002010320040c0100402001c5803481081c0e0103060030141642c0400303211703d003042009000b0750011004d09842c040c140401c100081c0c011032041c1c1c0e01d20070b9181c031034082105402c00d41e14803802c052203610700702003000390610211146000301c841103014001c02d20031038494012030404c403074251201400030703005080031070303590009908440e81980c10b000001c10344803101080b0314120391081d2855007000c810350003071403210348d0140203190040206156400905410060b40aa0000da0000d02d03846141e075080c000958508 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 713906420 1250 713905170 713905193
    0x1515110703022106070318030516050601030c03120507030e0609030c0604060f030516090509130b0c0d050f0c0f09061201141504060f030c1106090618010504080a0c 72
    0x2c0081c0511890304419070901d10103402e105400c00305000740350000712028024000d16203007800da00300c030180c40300d000c4d1403c80e46a00800c0203a0700c00391249400c1c00210304200040d41c0030b180610382e00b080711407841c03600181c0c0c0c036500e45d080000d014061241e48042038000130007040314a0709846260382e803c10a8000303030800d14000803c6900c0040400c012451b240d01403054802144180c80421003078030b5281801170610b020350343c15400610f09100071710240c02c150314880d4106252984000e01c069640e40c440c41c0c203241c222404245120045143c160102e42030148641000b08404081c10780e00381900c05401d0791080d2054015a0a00060100e609840c0d4004540b0303003c0700358442854551319010185010400c0841701c9114500540a50300140651401c4500f114020f854600d14200d0a05081d801741090303c11a5080c41050f107822411000f050000510904291014011078640035543c80300e80c2c040601d0380f251603850a03003004002079007007040b80c407004200e0518a4030302e0081d18144040c0038 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 713907670 1250 713906420 713906423
    0x80c0907032f1c05091b0603150a031403030726010e07020a050102130f0e01080c0f0f120f0115050114030a15080a06060b18040f110c06010305011515110703 69
    0x501d1071050105030740580c0503a0142585c4426242c81c29206810000956030840050380c1c00801007002c15180b1000f541c490081070300c068030380e000a40d034a840340d10150107444290070264200208200c60307154486c101c07818400021200005140d042100001d9010f014062034902c000418045031001e0f008000000394240e000e8002c1d9654174042c20034416055162144411846100c3c80c0031500e002c08103503142c141c0302400020402111100304000707400c91506503980d08040c020105c2c00d043d840346880012603003459402841840c4c4550803060868800108031450402c2902d801d1207160b0380310900142e40399070003060035140d0f10b1b84407810b0018080c80c4101d60000c640f8103000641d0b01c10100b0300140303060055404000e01a925001840c007403184010007103036180203031090005460264040301000c0c145240020b18418054000d9001d5400f221040711a40c0c04140104108130003406003c590291503500720410a14100140b11180b54001807501402a80307a5003c40c1ca1504101c10002107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 713908920 1250 713907670 713907697
    0xa0b04050309060c0a020f010201110a0513180b0111030405011715030a0302240f06010318080f0c1b06031911070606031406011503020c070f080c0907032f 68
    0xc04513a25031a03916100d5010403802216201040d10042d80184035804e10502814000341c030704504104103c0c0c043e400781c80e45035848002502c000c10040308078500c480f45401c00b05000a00039450a0003d4020a01d004e06481268810401401a80d1388000000603010304c0c81512402912820aa28199200c81c0c6407141c240c492030303921310141a800035104d00250110724498807078042803007040c06c040390101e41e0040a8411680460125440390340484940b0751b400c0030a59a040d503640c0d032000d4591044144007250800850192200391083c01301c46c190b2210701d4003036407801c0c1c604008a03a0034000140303112840c4003000300c620390540380740c0c000c8541c03802185000f83d0360b20803d02c1c10780010200d0780425545008000e490580d49040000c5050594910942d4007994110369a801c90182d4440c00c1b1407959402480f800040c40030304214040c3c05400490040c1c4442c1c01740000340300f00028010404402c15041101c00c0788a041980c0300a4a025400301c04240c40c0041020381c801c003442480f0510000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 713910170 1250 713908920 713908927
    0x902091804240203040b19020d0e0d0201110403020d02090415020d0507030c020c03060115050405030f2125020a0b220b12010b181201090302010507030e0a0b0405030906 74
    0x300302d951015402c400ca06512040740c01d007503034040c02d07040340011a0b000705008009408502064004210030581400d90000945040d0684110100f80c0e494a24600981d601081da8058603680a0142c94061403180000c83c0c01c1503c1d6800191903102c140c00e0107030142400c080801c042c0a603402d2030b89240c03a1594410b40d91200001c0b00342002b0300040343c1e001c001070315000907452203620125072841403040090040c6456400c0c000c09880071000042d1030018004100310015040c0c8040c8201d4400040031006441881010a0391007404400d000b04028585010000c0c1030300110b10000c3d6500d81040580e50000082d903d20104260301c1240d00030540c100701c0444d03007000c2907070705503180b544051039041c040007229902d6400f10b00900a840c80c11041081c3c0d107005100c0800104040c3c00c0c040310f00700c1048800b2a482010900300c00702c4000d0701c85aa51140400c00a05409002e419000030700b91404012080100c007099444551210340103014091100204041c4801002a00c00c04000284407566 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 713911420 1250 713910170 713910173
    0x3120405070603140405060f0603012403060c110703170409050f160206070e0418240b09071b0201090f35070519031a070305100303090902091804 64
    0x251141c0074440d2100103420048182084400b001a4600a9a000c00100070070f49412058054085000b0000d42c0c042d90390310301c90304020f0490300e400303d000d030800240c000700035046082c50b10070f690b5542194420300c0500703a00c0c01c6502c5400100d8904903900710549011804810a00d83c6551142e940261081c904090500c0400e01d04448101e02601880f240b10400368400c900580c0c68400445400300843d20321100c441c170754106070300100d8803045540780900441c0603543e203001140c25600300060517465040d019021820740c0d445060050002101c0d00c00140c54101e50080440300584180307140c0161003910003003164007030f502001c060132003488640e141c9a203c40a0f211001c000c034905c841c0d4171502c5030180c3d46103000782440040d41c3c406280909881e904042c140b1114a1203920001506185540004003007005081c210280e0a4444080c80081c20300d0304c0000e09462015016181c1c07004200380400003c1d402411103021501803810250703d40241c40005522101c0c50710f0380c2c1d030740b40314510f04010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 713912670 1250 713911420 713911423
    0x8040606030b07050918060604210c03030305191506050d1b050d0b06090619110109030512010e0f220510020406090e01140108060f031501030b0a0903021005060303120405 75
    0x4070b400406e40d48180f8040110402d891801400e41e88a03030040420001886061109441001d110b60201c03942d440301c0000d0f60745c10089008503170050b00000da5032020310500c81c440c41034140144249840c1441130810991105070040100d100c1d90b010b000700012402c5004400b90044446c01d070f0703070202c802c82c0e0701190000680349034004071703074003000c1454032032280c40d90b14118041d141034950240c8802c1c10401c2902515a40304985100c0f00b080c0614100002d000e04400d001c0d80c83c09502c26178503070b511031120742240042d8510607040900c442103000100080e055042c1256030348010002c4000c0724a44c10071241c48405440018050854015140031010201c0b45400400407980c40d03035151149565261440d007050f003030078001c0f80130f60350156000c030019611485d01142c01943c02000b001001c0d5402300003a1501102c41ca100c44440220270042080c420940d5050b41d020b04042000d00200c9050366009440c0c00c3d00c3d0307030542c00140d607480102c0c3c1642c800b08140e845c2103810f44000c0c41c8900300b5080aa = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 713913920 1250 713912670 713912677
    0x71209030e09070201140402060d1e020414060418091103120c1c120b031203040605070e0303030702030d09150e071806050604031e02090c07050111120708040606030b0705 75
    0x18002d403002d00200d54001d10511030301d83c1c2c054803001004d60701d84940d820410b8951015414402c00c6454004080e00340840e409540c0342c0c0300c840f190042ea40c0d483d005150382d9002c3e8584865100b61814402084400f1402c0c20680320700c00407010019402c0001c0c500032519052202400350144a5107219800c8030b915007000740481101902100d52050108824001c01800d226003000000c026129444d0785d074950f0b4200050581009042c5c5a40c1004243e4698094100321015600c4a44403800c1c031004c9a000200480700801c240d0140d0b24620f80410080d41c0d0344552041078220590310942c28050040590320307910302c5030160006010f5044000309150343e906880c05180349407684074148000c0da00044c4075940c00c6600290005051518584880c86040c0c248a00e803a00c1901c1c0119140050b550f440c001031042181840d0541c50b0105070802c00d003102e9001c0c41c50061741900700100c180c0a00b100c03451130760160b424940640d070382e5514a0400090085548000d100b206510b041c09811500300014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 713915170 1250 713913920 713913947
    0x10609090b061c080f1c0b0108090105070834080108070f08070e07020f01060b040807170307230f010b2d010f020109050703050c0103052a0307120903 66
    0x40c001c0e500d0340340c20000100300410350480d41c1e007900c12031200000c1c1000d005c0e0080f098a883d10900308100050100070540001c1d8521100903a0f42024161540e0424251078211421000802941c40c08100c083c0200300040c00e80e170b0354011107a0003004042d07810100045d0103038200000c4a5840b120903800342c80030074203001e55072560007100c00105440782c00c0d0030040200d031b0250b4020080d051400c41003699112020b4480070450007400051500d1300400d004445c001c1180b4690144c3e501e103800003480c00c0c05481d41105404070302c14809044064000002d580c040b1340c0007025124200718110007841408040580d5442c1c6024000380d401c6020011751090701c480d2001c3d903424000103449041400d9032440c044854141c00ba9a1492007504c1d48910301900b100030040c000013419101d107032500e9140c0941ca034802c840796480f04016800551b454021039400408c402000811032a0fa042c031445004148540d00040307007000300010302c00d80d104003250307405860408410000e0710458203004060751410201d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 713916420 1250 713915170 713915183
    0x150b040911030c0105210a06030807030c030e0102010e03180303120f190207050d0305070e0a0906090b0f030703030e010504090609020c0f072102271b040f060c0501060801060909 78
    0x580e03d940140104c0e84510b51a030110110b005030a0b00031200d000380070740004c0c0010b5490b43c0100004c3c5412008080c0f403406501d441008100034070b070003040c0c0e090040300c150469041640010495000000b926100c005041c202e40c6c1c0c0f01d1048010130b203180076000041c2494081c1d5000d0207100c084030880310740210640000741c000e00c1c0302c000e105000da01c1003000c001e146500540c01c00c4141072080c5e00441e0840c0d203d1609240510303c0c100082c3c8091b0f6190030a10300e040e0b5a8008020010841c0300319102c188041e1180001e80d0061400a40c8031319540c0700150520402d03072460041a03220304100d40107030003045000c1000a4a8043c804002e41205089075203d00c05c00f5020b445120001896000b10303419402e44104108140801ca10007111030041241c00c1421000300ca00602031400c1902100c10f004c030552810341c42d00d661401c40d0403036551819141d10404010a000d480381600e14031080e2101803c2017082c807940c5140c83c038014045036002d00d48035440c0c1880481c6861b1070384c0040410034000d80 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 713917670 1250 713916420 713916433
    0x90b0c010f021918060912051f0f050609010602030f18031614010305040503030105060f091f140307050f070f0506010e0118151e080d0c03080108031204150b04091103 73
    0x1d811394041d41180c007034031000c140c1001003044509103040d4040201e6209000b941c100102e440c1402c42d9515943c1b18170034049803190387c1d0710401e6043c3d109040c1c0c44207044030032032425403404901035200d100340b401c148038841d0001200c0c68540f03031009001d00d19150103403c603078500c92072041c03154586c0d18600038070354184a11880b40714958403a00815006a4010000d14910323483c000c100901940462001d00794420140815a142d903251502c03807040b6000c0c2000540d404103500402406002c0100035040b00348014010701c0b801a90280c207a030035603002005d042c2d0b900d65050400c1600100804030062440c81038100102c0c00c40d0906081604071510f4840e485036040c00c4000c00c02c03c0d9152998a06120a01c005081101142080f203202c00030100c020000059501c4130016810120504440408180b4107400c43c2c0806034408ac90074010724290000d103040200d42d21100011100107040a0001140c2010351007140445038040c98110400800c1002500c21a2820800003640342d4800c607c28020003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 713918920 1250 713917670 713917697
    0x20f040501090e01143903130b09061501121107060e0f0a030f030902010507051b01110c0108060904170a02060714040302010c2a0f030c0602070612050a110c0c03011506090b0c010f0219 81
    0x51158001c0061820103003070040350f0001190400c80302c24000303841988400c820400012402cfc014000303580071700c80c045003640e581143c2318500340d9040f1030700c2c00d0340d4090000c0300017013070780641c0d0002104000d04d00401c0e101101c2c001202c2901826401401b64040c00d8044041094118541c0320a000300ba02e5031030000e0ee400410070713100d5403215146800b103540d49000500a00e02005403950062168040c80d5140307200c082e8200903504002c281c034002d40d00403c00c1c049072076000940443d082c00517803c11440c1500303650008001c09103140c002071400b5030703020b240e01c0c01d250101101e030340d200d8100d50030002d07156640e42070564518040c40b05951440221001180240c80030400c1c10076100d15840f04c010f003003010f440c0040100030040040c80202e41e5a003400311119241c000501c2d070b01d88a00024034440c0c0c02030042608658000c000715102d50040c030400c07c1503030b400520000440310310304051078603103405120840c0541060800d5078181c0d880011a44040e00071481c0d980c68118090742e4800f0b0f00c041c01d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 713920170 1250 713918920 713918923
    0x2a051c03090b0f010803042105010e1b0d1208042a030308100806010e10030b0106090e0f04052104030204050c0a090b0f16020f040501090e01143903130b09 68
    0xa0056a681c0d8108010900c8070401c48107180000c0c0d03c01048d00e03c582002900d845085030503104a40c0c100e500704a202c0c26025100310358024100d201114885400489035980042c076080001c400414072400200007400d106541443d40e86500d003040307030010986510700c3d040c02042080c0c0401c03804600c2103004100b02c410345280e5501035070010703402007000c1d90034400507010414004150200b05a00c0c2d100200000341d294859078004e1006454815250b41840788080700c1e000d00820100c2e40445640070000890300024084000c1185030306001078010b0020b00004040c41103804c0650841e04040601065800c2c00c0000d0040308101c0d80e54861103620b42c1c0c104038052254545d800c00b545d0b0140b20010b80c00780c50704e070061540c0d0300c02041808210130b50804241515001d2740f10002055442c2881036800f002805540301110f2400401d4182c0d140c00c0c015100000710000c10500d00b01c0c10200000010185000e000c414030120359840c50b181d150030852590070214040044682101d8240800d920380320 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 713921420 1250 713920170 713920201
    0x2031605030423061605030c0304080105060109060c05060705090409082805041d0712050a060501020706020c030601170f060405060402030106050a03081905090604081c2a051c03090b 80
    0x80503180f420401c9115000c610500110986d1103010810422038442800c100800c02070003004004603071850400005403848009074044014003124a4148002440104030640d100072030f030520945440004020400030410350100403d072000c001014401c022006861201d40003043d030010008004001048039140030780c0c4030324021440c81d10800440010b54018030f581c003e040f46090983c00d1000349100c07058400540e0001441035588605100c1964180b02200c0a0900f13800100040c0c40c441d00420350380c580c14403401c5006200e0300c008042156040c000c01c084900000201c034031606150074125107c10095500320310940c0b070140002054100704402a0460342c020543c642424140e41080104c01040801d00301000700810805085550700400b600180480d00010700001001c91004410044030495080500c05080c5809108101e0f03040995041100320840340b00c00f80382031030014138000c0700f0308240300d034032100e040b1711b02c502541980282805802400300e40038030f4465184070180141d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 713922670 1250 713921420 713921489
    0x50103120c050d050a050f030f0405210d0f060914010608100e0109050603210703020f07080a150f0218041505090a0b0a03120504030c090506130b01020316050304 71
    0x100f11924003650940900c000c1d180e0402542002c0d0315002519606154030b034000c40720f0001d0705601d24180030500904000c03050709400d80e4110320705070041c6d9034504400c1d8014a5180b2100a40b2070b03c250101040580141005003004042400203002201c81e40b03900178002d005420001d4919000101c42c0c0407141098000c5540c28404048e0310390078030350b002c00513090050a040d01842004a6071000064110240f0080c1000440c0e4503201c0d427030307840d0090a02c00905e40d40341158cc0548421b104c00c40703000c01c12400386640302c048904d425a0100c1000050441400c0c082c0b1007a00c0491000010900c07002c00a2501c03800711020440301c0c1008401c1010002c0300d00038280c20a0514002030088000c56101d9088000000d1401864541e269128620324000c8440b10f40014800301d401c1081240d154040b00c0503009484c4140302910304040802e1400801e41d11050030b9a4545041901690003030040702c2302c071105200750b00c07500101410059501d620920410200710311440c0002d4103180c01c0d000b80302494 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 713923920 1250 713922670 713922673
    0xa02310527011b03022208030406030f09050706081306020c03360103020310030f080d0605030d08070c0618110f220509190609110609060a0f050913050103120c05 71
    0x940050480094002c00901c000c0814007104031403218240800a070010207c407030046543d903080c084000e0503a0003440d0407081c100d04144d0f6802c0024004161030083d01c2c0c051601d61520742d50003a0b40d81c0340c465141c4c2d014004620000d0502421400800240b110b400d0829000140f404080c108901d00481c0c40b900c00354103032820b01e0b9030001d0340c0b003a001148c101d0501000300000e580c8039103514440584544044a002d071000480221010207401454000d00049014294000304441c003e80400c00c020144000c1021030341c3c40f401006103030340c440c81800c903003160b2103041325103e8605510450980c0800c984101424180c021701752070800c0d11f2600d102c40d000e80b000403000d41c450040024210280c008103207405035405040300c101c09000340c5c1100764040d61010a00e1051405c0048282411651260280404000c1040b4a0b120002119415106413030201008109600c003282c80340501c1c0030b42e03680840840b02200c642d40d041c1d040603040c0c81c003501079a0010300e2201c005484211072a840141036 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 713925170 1250 713923920 713923961
    0x80103211e05190c0209130503040e0a140c030a1a0102030a0e030a1a1503030901081f03050f010e15010602121c0912030b030a0231052701 61
    0x41079101d203404200c19074105507042c052505504207580c81c0b02c10700749000a1402c5100815850058069600000350751401c0782e8030503550301d0f42501c030300c568095880c0a045a40124005240300e5010204483c04e00c6903000460601e810849640c2d403041d901710724000d04100d1003915420900000c81c001e804141c009514111900700c0a9a07500302d91031440d9814041c1c558114003160b070503d04c0e210503100c40c00003181c85180c1031680c5581508180d030040c3c000e83c024801d003c2e003641c000c5001600f04c80824055000e03084c11000e00802c0030340b59000200305000b20a4080b401c1d034815007210340c034480100240c0d0000c5407894200c1c140d45c1800d00c107420041c0e11600c1b0901c1c48941c120010005001104180450100d102214006a6503105c408880700001200003d45546e03040c4110350131500300300c1c058503041042e45c002851207040703001d100002c40c00e5494002c3c1040540c03071010701074071000c140c240000e00d4101c1c10940c1c4821640544001d603040e46501458800040c03007420510031100140120 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 713926420 1250 713925170 713925197
    0x7030b0f010f2010020a03061d0114010509040216081c0506090c1c1a0103060815180712060b010f020a050a03030203060a03060f06091508060604022808010321 70
    0xf40d41c400c09601039805a0640e0722560300c690700080c0b0740d0002c15200881c8080c45c00140600426580318499402c202100042c041030b94865204a2800350904e0a240c8078001c0380002402441000c20301a401103450319007008005001001c1c1200c031524940600000c2e03210007246058401c203ea9a6078411400c80000c4d0782c08171400c019040b4402810f0740da81c40005c00320300e5030045603150414004611401c1488449540e414003805014044440140081141a110441007d000548005020080345655014404041100f840280800903c11401c0d4001e800c01d24014075019034120700048201804035070141c0001004084558400c00800000e100c4d030301c00328001e400213003505038000d6181c4000004076200c0d00071030031400800000080c65511304004402155000349108064080080d41000303d0207001c5003480d80030070300f0784003d0307602d843d00d200560010b4000144010a40034030b24091040551027842d15043e02d10400105a02141030420504030708002e400f5100011500720a021 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 713927670 1250 713926420 713926457
    0x3020607080a0903051b101b030309060b1003090b0f160c050c06070b0f0a1503031b351204030e0a05130e06010b1305151207030b0f010f 60
    0x39120b0705a01d8402d0b0040c0c1c0f81d641c1c60342444404407040c191042265240070031450a55249015008141400055032490300f0000741d080c0e00d10344020342490f03a20070a00e424030285400010031000021b010240c0c060340700c100a802020840400da82c08604440042c0700c0e020383c1208035000e03c1270f204010760850500c036002c907150000120f04980741e020b650307540c4000d61139403c082c1000c80c0c40b40c0c180808a10304407422142c0740f10014400d11000d8100504641c4000c2c0a00c504c105994052400c8141448980011810b040d00c05400401119081c40ca00300d11007400f018110000c84003040b20410641c0c842c003e084c0e14090b003140d003000c019110f00498002030140c16508007856000e0050420f0b150f0b15000200d0342e40085e5500b103810707030302c4100d080c880400502035140900b0b001e1400c6800c00e01d040c0c55510148600c1d00426009440303004a0f0321071100c104050f01d059080c400280c2c0c19601d01540d0007000b0b003005042d26030156040500c018510b60007a01504407100311547d0300584a40e0040420 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 713928920 1250 713927670 713927677
    0x30e0a080714030f1602030c0a030c050d03020c09012904030809060313060c0f0f020604051203131202100b0402360307030b011706151017070f0908070302060708 71
    0xb001d88000c20803c42c11819140280c5080048019041440c80540c01410300308004000c07514030034200c0403024000600984a5201910402d0700c400703030304200610b07059244c080d0200c0c48641c4a021240000f94a501424403801d107007080b02d480b05000c500420b004613140c000c500000b030680e001071044030f520b410510061544804620010720024419850f0641101d4040c02078000040e0680b6161a0f03880d00007a03d641515040c0c8003d0009103840d441c0c480e1615100092841024070000100b412150700c002017190f81d130f40090000745401c252030006559246000c0c0d5800000b41031003d04505441c0034401c0c1c500c2c4003844d103c65100c0c01c0602c3c494500100a628401443c154030890004207900c08110a0020b140b04408200b0f40e5414000710030445a2401032014103940503030104010f8440308215507102000503204024002c0e00300d0001e98040300801d49030140c0700d061100304109264001065000d0b05280e490305c040e000d407590032140d1070794050f020194100ca801c10410703001a103440b004 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 713930170 1250 713928920 713928953
    0x1e03170c0604060b0a0e0403090e1005030a080d061d0717132a14090f0403120b2220161106090a06020714030c0a0b0d0f0516030e0a0807 60
    0x1040485e907100e0f524030700d58103070039070f01500040d411000c14810f01d0f001496140d04013841d03030403440e1000e00d041d0009a554041100c000c0c1055004a003d00100c03489401002c050244215070754101c859603042c0000103c1b00702c500c0d0f0000381110134610100c0c000280031034050080e00449201e22401512900c81c07101140d1030074042d00c5c288000156003132001c100390078042c10f20b440c00703078120340714074000c011040784060581c1801014000c00d01c00000d8010641c0840303a20b07140d03004240e0303071803c0c0c000640f03e80e00d80b070300240e10b46080152843c0d14521603101000800300400724140d01020042004800c2c00340d00c2c00900c00b4a104540403001c2081141070421703101c4014090f5141c00c0640340071844100160f400900540c2c414101801032401c2045076148808045c1c004040e1390b991100061102030307061045541c500c00004402100c800c5a070000409112000014071a030708200309440040c014034000000002d2900380740405035a8041554101c85411110b885e060141c80c0c0c85041d43d00400c000d2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 713931420 1250 713930170 713930179
    0x110d0314060409170a0c0b0c0406051905070b0a0f242601020d090b0c1606090305070f12090503121b0f060a0c0e03060603060a05101e03170c0604060b 66
    0x2204c0003ca10980092081c80705a596070f646840062900301c2c0c941c98003401869290744188424001164014181c48a08044209018400745245070558031481846406000c03a81d0060400103803035402e42000c10284c00d00d680400101020700c0b280180d003802d4581c05180010350640800038114030a118900c2d4400809404070100c2c0a00038442c2203a012818403140070b0b072102083d0062110382d240140d80038151a007594604031481d211054008400e0000905e020381c1c4130510410b052007001039446542e48504051094061070401086114007801d12500142c1164004a800c3c100801d0b2144006030179040310b41002ea00c44602018168848070101c4244900005843c8868042082790301824411000003681642200700404150110703111fa402a8400c40911919450001c0ca40e94002d00304000018236854848102e06001a2070703000e400039010b18400400000304e200801e1045900c144028a407981c0036521418450140f0002401586c129000240114500e0f4000ca41209030040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 713932670 1250 713931420 713931443
    0x607050d39030305010b1608160f050a0210020f030d050c07020901091515050a080601030e0706051c141303180b031017070909060615110d0314060409 66
    0x240841c8008140c10448140001614001c1c814150107100e990301424003500d00034a0038120007808458811f400100078074206c40000c805420b04450b0703109540383c45c5d001080f0f00c40e910040c1045a03031007500c580240e00c18224003d400b1000b90000505c8400c0504500165090480000c0030000800c001042e5410b4000104199001681d9455001c0d000e000381640015548501d00d034020945000d0703820106281c082040b501913147d80120644a103800641751900040d5920001240a0403102031202010302c60383d04041141e640103405803040b00e038203150030100080704607030100548106c0c030318000d07901d607500300030801074038090340000b00890003414081d07403507203814402002058056211444e900c00110621034107203030b203035003401c002c100310030300500d0b426240300031151500e60300e01c00d0051480d03a030952401007068a40010b0010504c1d0a24107000c6070f641080a040e0700601410080940502034011280e28000d1041048040c0c4400d8074442035510401804000d040c0080282c54842e00340 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 713933920 1250 713932670 713932727
    0x5010c110406080f0f07060e09010b03060103060f1502060c070c03080304080918060f030601080606130e100b01080109150312030b030d0f09170607030209270103110607050d 76
    0x1000b000c1c6130a01a80010451041901240c0d400c00a55820400c00c004d401c00d54200381c0e07601e80c000c481c10b440082c41b240c0c1e5652070303407401680100107ea00c051401c90742960006500414a40300c200303422415006d9071402e56802c41d5090313140c85104c00040050001c03010500104030f40300e01840e40309215041581c0340c00000c000140c207094241c40d202000464580400825050203842200800801da0007000d05504052055417210783c014078040c060041c018070040e60112540108d2040f040342803c1d50707104c0e08182d46a02c0581505407000f404201610b000003000022803040e10002074000400c000001d09640e80c0306040c1109030300303400403d52680f100504a9405021070900d8200c981c64005d4840303010f41c00900f03844900d40c842d00740864100780e00311458601082c215171221852900580e141d41140006413292540c01480d0765401ea081c0041e6212640f50741038174140c9008013411000c0120b0300040094510580078002c089810004114041900035410b10700e8640c9949850401003001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 713935170 1250 713933920 713933923
    0x3130605090102030a0b032d07050402070b0708071d041107081c0b010e030703150608060910060b03160305150301020a020321011a0a050f04080d030f020405010c11040608 75
    0x5440740003050758000180f02010701a4400c90300400d0040d0003418448451500130000010350300004103062200e100408040c403000d0021a000d010002c104548074031301414402c1c26a101103440c0d00100d65100080b0399111301a8000359030f14000c9140c3c5030120701c45242400043c0603007101c09191b002d018001d000005a04502030440e14400000c100540041c081d003880a07510038000642c18090114826100d9490104000058a4118080f07108002505501c2c0bc010416584900140e0051744c00703012030000007060f40804a006201d0a0169503255100000c0b1440240c5222030144007000b229040305000e90042940545088800e500c50200000070a09a074058140c0b080160800100b4810075400708803043c2c01d1a4418001100c01d6040c4110550200c008955103841c3d5000840c64a0169124038120340c07400f0003003480d0075115542e42c4505a40e503400060791602003801c0a480318082040c0d442520201e4070f05948540103070405464104a03021040700654200c1d4031010081900c120 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 713936420 1250 713935170 713935181
    0x3060e10060e0f0c041802071e1a0105061309051e270a0c0302090a090c0f080633060403080f040f06020c06030705090415090f060e1b031306 62
    0x382c0c4550540940b40507140c0800011000b0220003020034140070074054445607295010014118100050b51031101c1e06041c075064461824420b021040480ba803000c01071070525103c09085541c02c0058940d0300c1c0c0d0100101e5005000100d49c0c000c1d402c1004014850168010380d8102c52041d02140c00c54524042070900f00e0011a098403154542245202d1880c0104050904044c04e071006480620781564540c000304003a803201034402d844220104114620300e03801446655808210b6246065441580000841941c46422568010f03500061100750b070140d583c030129014522210385044401c40851b4191003081580c5807c11414031022000a54201c01421f00070100da80c45600d0b0341c6007802042e4003807055002201190003a09a804003516404c0640f03801800e10304000751070740e002901160042000d0304400310f134040304000004400080ba4000d1004040d030080c14010b15403035111117590340348213813030540c003442025070220f6085106e5000b03107401260716084c1818214181e21070f10b040d00c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 713937670 1250 713936420 713936429
    0xd0c0f02090a0b01270b09010512010807061707020c2701121e080901030f0b09041b120213020328020a02100b130b01020106080109060f0e070b0403060e1006 69
    0x1035483d8005070441d170f08100120b002071000039145610748050f03a840f40c0c443c2c00c10b01c07604050071000300d040b2085a01a1042e03682d00b51100075000250340c1d54500065450b481441901d011900800340d06241c000c800c03211500c0385c1415001440d06e00e0b0400d092003482590000310b01c040f6052800c2c280c1c01c00d2000c4d80da0b54000c004072824902c81c41e10a0a0900000e0301c40c00c46141d104044818400014940c0010360346403000c00d0030300251400001c000540600551020140c0c048581d0f001c1000b0031980d29624425000c0f49940c0c0b40806440e020b88890903081c40300c0103540704158120a101004898000f075520280801d0700708081e0115801d0034a030204003420350a10302d0780100c1d0a0207159410440401d0150b20354409102c0c458060300490301d0b00b980041a08407240c0c944528413440c0c2d0007500204000e243c031000811403c1d9407824060001c01c01801111502418100061031200300040c0140585282e00d443d00e20b03192555a48000501100e02d2800007401003003540c0c2c283d001d40f44107000082 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 713938920 1250 713937670 713937691
    0x702120f010614030d11120a0504170d0e030c0109051e0306040309031502091f020a1502210402030d1215060807021005040c120309030f0c0e090a02030d0c0f0209 71
    0x5030020404c042c1094802e0489004000039007181030102c10b400101500784600500c40785503a00c6c008442240c2502c0341d5080058001503a5a00020307031540020b80d4200d40b00707507549400091203000101a00c800001c1d100750700080700450207000500d0681c0314450880c25002442c0c40c60504107011904201c800c40e81540415102c1e1810024002d00301550001c2c40000c00d01140f80511440029107a200c60240360001c080d0300700703169010107008000c3c05001603003024000e051282c4040199000e94403002c2c3d44200c0c3c089210251602d0f580d15003e03280900c0e40140130341300c4000d03205000c54410707040ba04951040394032000300c1c1c8952880c0c1c0c0540ea01a0942d036403107a0007440c2c1050041e10b0000c40e40c0e03143c1091441c0c9070420002c6110761a1200c00e540c0104110041541241001c4a005d03120b5000030300800703080700f0a481002181c1d05485c0480c0c201028403a0b90f83c0da040c511985400c40c000d4040d4264208078100f00b41d0030320642c01800520311070f00070044000640d40105218420440d240b1030300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 713940170 1250 713938920 713938949
    0x6090603060b130c021905032101061101050c0a080423030306010305071e051b01020310080d02060c031302040f150306151a0d061502010b04110f0702120f0106 70
    0xc1e041c03403880f81140c10035210040c0900305007080000d60720b650300c0d540a241454000c25400401070280100c0e00b1481107000340c00004448101140001842171003014041680d4103c0380503401810301480340301d28560100c0905094a0311000d550480c80103000322044503100c1100d00b07400c50070200c80607001544100070b42d01c07840e00c030001404a038030260028040c01204042900d00001c400e650b2501400d080c81c0c40c98445e2400c205400d40a81130b662a10f10300c1d4004010070004080da02c811038200c4da01e0004903074181b4403828040c0e8032040182d038503584400e01000014411880b410026400502c058000107142c20560492811600030b102080800314130000100305000e0107001d040b080320b41c15064425020302d00034400e4010b40d0019940c040c2010042054628180598844c2c00106070781d07144ca01480c981120002d00910b01c4807040d620403841c2c0b00082042c0011b1600380c8103200c01810b01ca0385013076815020840c1e00d03032280402c40384d58854a040028119002c0c00b0b142c0080401c0c1d0200f604 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 713941420 1250 713940170 713940191
    0xf0b0d050408160302011a0a0312030b030102041505090405072109030c0206180306220311070506070804181a01050309010b0a090207140606210a0501020a0f0809070501050d0f0609060306 82
    0xa61407d0194601e10032a0060700500100380c000b10a05e1081007241400540100c45102007400ba0046501101001040b054440c20044e0003000030201d82604480170030140c0c1d204035050320001f4a81c520000000c40301001c944800c00d039603101e00312060090420b40c1c41a16076900181e5941c2c403010090400004062443d02c00f41010010607800c02900380781d885844680300710b141d01e41c00c01210060b080100404110189030300030310051020b45030160019580d03103071500340010680c1c0540720b6082000d918503c1d800100715036103d1310310300c0140f8408480c00c100078100115a29000600040800e56880300b0610040d954043c9000c001c5c42e00c0800940c5400040c1001143d80e007002c2c1146c0801d800000401c0056038a0480302181c1c1082801d50151120300400114038014280d200108958400070300091a00d0b0802840a07200d9100d82d030364042e07030b40c40c19030050711070080307102d058085041402464000c0d825500519440c809e2a800010090354a5a0380300507a110f9034829642c46603600e41990 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 713942670 1250 713941420 713941451
    0x4050f060c04170f0c06280f11070e04150e0115150512011e03050303040b040b2805070507020a180606111b010509030d180f0b0d05040816030201 64
    0x70391005111000e801d42044d001c45158840c00340d000030034402d410004445c00100248200d09000004c400411183d80c0e60280001d82040c1400903400301098070141422001140003d40030143c030681d898140305520b41e5622403800450840310100b815860b10358903640414240302c2d2a4600d800e054031907028520708034911052865020314801044410842d03005040d96503450241144c000d0380ea10341003001e078031001b101401a944c100901e5070200000340028442c440b901280194000d20300880d503a2035400c1c81c5d90440401c10080403200000c11303084030102016601c0f482d804081408d02901d055002d6002844403907142e00325900089559800e15215100ea12400700030304898140240100c3d4038025550b900c1c00c408000250500c0001e07440c41c00c5901c101c00742c0d841d0050240440703c1c2d03644504005004202400a0f02608141540c000600000303001c1c200012640c0e8412072520f07000b0034418407806000010000e483c0c0010070486904a150180d4141d847d1034000e600001d108041c441040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 713943920 1250 713942670 713942699
    0x8060d0b07120515012c030a03120b0901030b040b2503050108011401030512070507120506070e030102130e0915040b090c0409020109060503180712063204050f060c04 73
    0x903008155a130351011a80d8000c1403a80525031030290a00c0d40c03038040041c41030681c146061560b0103008501c0c100e4101600140d01840b5850500003e1040f18142406c0c0114100309110107002c41030240082000310f0008084a508000c80e040520003003c016100b445410728070300704010020359500300401c81340500b88940c10401a0880145010b035245844499851480580c0388480c1040000c1080400404100f00c030018640c1124000a5100a040a030b40350441210440b0200d5042213400c089854180b0031281c94120703101c4544c0c40c450800061040030311300203020001c5071180c0d90b48040c1081c00c0f83c440522880c8201c50f00780c118a03041c00601d00f8220070030301c1140150b08100030a40141e070000c00702c1c000d171032032031902c0794980d540c0540c126114076850350207100030b024088d0003261100124549410840c0200c009100c40d0b00460b04180d60f841091000e9440b48848100842180390a40b24407034110307000340c0413502940e1125420b42c0c28944191003904040000040c1006441c80300c1c401c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 713945170 1250 713943920 713943931
    0x1060e01260606010807080c041e030210020610260111090a17030d0c1b03122703081305010513140f0c01080c0f0f04090e07031208060d0b071205 64
    0x16003824148400060030020000c0c003a4011b000b031f2180040c00108542c400e4074010608681402c03209620000c8100c40c21a443c003090b4002c250401c4d110321020300000d4018021030040c148a05a075141580d030741180000142c101c10403807020318220385450f009028400401d15200c1d2101c2e42d41c40e6a004100040126500c416458116034100c4800054044107807286214028800b1440c4500003008681c01e4106030403c51051101403021001c0c5940007002c8c4400300c2c01400104400c03e0b10103500b00c0c0c07c003200c219200085106038400307000280f04000e42c1c3c0c1c10a280702c9112f03410030303010b540300b03400d45004680d5020440011080c2c80e0a204107448500d180c0303c104400391800a83c2024025190031080e410b0390306100c0c0c0040401d400d12181c10480b001f020b040800e0f25124004506074582950207485001800c80c00c0c40081751102901040900490343c4c80b101c0c203140300070402419617000c00e0003010607a00c007a03840c0034100412071400304144a01d0b010341d544020076448024120460303101600 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 713946420 1250 713945170 713945173
    0xe2106070305133f09090b0105041211190b0307030c0c05030706060e01060309351204020a0902030f0604050c040b0f1b03040806010909060209100f08160c0b0405250612090c060e0301060e0126 84
    0x10800115100c0f3b000c403a001421840e0104542c0b4400d88103440d1110b02000c000d1840c48001030350380034003500c1c0c0e0142c000da401035210801540d0340c9080840c00d95154a2010b80190204100d4a21015100c0d002e0715652468101c0e802c100d212034200441c2a82155410704125290315042108624103900b082028100f2001d0850640c2000011074544c035100403c060300807540c85010900b420200b200741e900810303007a49180c1c0d585903041495407094000d0b24050703091007500204400050b2011040c1c4094420803130003011a81c5c079040041d0301920700c00344250b806a07420840e80503940ca0310740540001d11881d8407299a549048000206501c60041001070030b1010826100301c0315500c60300d01d90200d070b0403400002807902d40e820003c0c1018581d0308609440c800c01c1c840e17402c4400800c11510122401516a02200402c0040b000d09031070000c9001410020202821f01c6501e0041c00c0e41d05181402800000f2299203414058401180030b8000c01e40c42800c01e503015a20320203581c0742280081d400c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 713947670 1250 713946420 713946469
    0x3040b1b030a05130623160204020a020d0207050a030314130f0909030206071d06071e111f140d0b0d030e2106070305133f09090b0105041211 62
    0x400700f060780300b405001c6e81c0342c040f40062007010106683c107611038800d4000340304650b2001e4900c070196039000f070b4001d840050302072140001002d05d02000c841c1c0c1102d80549615449820414841c0d125030f000c104100d6941c41d655101242000150946401615103014005000815802d0117407612100a00d07103010402102008451305c600c08842141c611816101541c94030224034118414011003d4000f40c1d0303420340c40b070311343c00c0c42041101100b08907007e80d007100c41c1203045441a1003040c149421680820036121007034100b00762002c000d15041d040f1150000b8075200c068000b405e6400c01c0c910503000118400340705c160034541928621003811400c074845100b4035505031059220040200190181641c5134001000c08812200384d0310b44550140d0041d110b04240c00c84400141d0561060130910301e0f03c05104400c803040091130004034003c80e00c075207650b82c1c030b0440014094075944011714100710f428040003c0c100242c400c9454610300c500800300420352810244031900d130040c18100c881840c0c02 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 713948920 1250 713947670 713947697
    0x3040b01080d1211070611030106030c111c050c0a060c030c020c0a0b0f0403050712110a21051c020705030d0206060a06030b06070b01030b0604050105030f03040b1b030a051306 77
    0x4511609640e6100c140401c44420032451000503000d640401b030004d40c01c12980c582c585290700c0046060310065281000950310b800030403034410020401c290b51503880603040180840e043ca16480c8000b0007403802c1490a40c0d000c04030740c149100c4007021220141c959400142c0d158250080180102c02403000b084144600c01c0041d101c43d045101c5d000600300c3c002850007003140008100d41c00303142c00c401111507550f500d5048010403c14008107440606400204915500c0c043d01a0170840c3e413061304e403440b80c0c403103170603900c01588030407608841c40d10802100b100d641c540e1060808203e021500a00b05051134401490f040001400030b805c00c40d00404108101a03442e85c544109940d11841d00090701c2c141c41020907001e120f201e101601401451000000304a07a1984091080c50296014402640e855042c1075845800d102c010340b0036003051109104e414a040040c01e0205c2c2d44085900340322140c040d88906540c40b508025001810001c1ca0080c0c08100004540041c1103510b411039255200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 713950170 1250 713948920 713948927
    0x8010509190b030a0503070b0f010609232d130c20010b060319140603061303090504060b0403020a0e060609130b15030603010e011a01051b1203040b01080d 68
    0x840c0e915003a09942d409035035469031010070072210300507405070407680e50f0200ca041c990500d20040b524003000c04d0400c00080303500c07407142c400203040f44c2c542c41140304c4444035034900900301050a07803000d401580ca001001000003100768513800502c00710080f91980d0214206000902c00d106015100b11410300080c060000e078000040002c40c4080300c90700440b80f26441100e801f610740003007807680c41034002c4180441c50120081d210070505008004002170a49503440e40d0400c0c03000c440d09549508840700080d080b90024800d0f150301032013890850b04035a1141c0010301210383d603030081021b020002c1000c1c4118140400d114001d400c4803a040f080515100001039418414066014010005103561042e05089908086001c1500070240c000740841601c1d031442580044030784500c02d608008099070200c006104000100e20194002e511040844006403044d0703000c1040ba0755203880906c81601905400e100092102000c4c4402954070300706801e0038603030082e061300011119007008800d2204180c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 713951420 1250 713950170 713950201
    0x2012c040e1b040c12020304110906010f020d080a02120906010812032509091d0c04090302030702061605120c1c0e15090d03030e010c0e06030c1c0c0f08010509 70
    0x40c1190045000d803c02da04c1110428401e14420841030f002006000800602420b521094075080e280491580e0700d600044602c0c511102c07500c2d0140c0c108071700400320399100c6d94510343e00000b1007201514140350140400d003c040200c42c85c0440e6006000140300c3d1a8003441300410300000019041c0c02c5050441c528000410310305101000d60180503291703001c803130250b51244000e04103c40c04000003145000c105c0d02a0019115840c1980560b20206205103064482c1040854144e4011402c01c0d929a0922026034481c2c1003402e1a403a01e80e481c074000072410404010043c40d0102c119869034181e030b0381c8916000003588400d17020f1102e403080c0c0456035032001c0400c000e0602211105104030040e03003202403a10034101c510b500018460b10210074141c140c0c01c11b68115040e4402088034001c07240d0100c501011404505510230410804510380e4003c00028107916100c0303480b001c0c4010101442d8804480c00c1001c49404a0301c011050b100b5160000c46485c0108003d958010032440e2241402c481841c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 713952670 1250 713951420 713951473
    0x20403120e130905011a0102030f0f07080c0105130c080d083405040e010f21060f02030a0b1207060503240604120506092802012c040e 59
    0x9101d00004800c1d079600d0004003941641d40360411003410380d81032860107008005000342481d03500312540d104a5100200f00d5071417800210200d0f05001201e9118035050348012401e4030682d40078407403807140d003000303116060007410381d07180c40c0540417850710b040092116507600c1392045400035000000015000440150700100303212400b520300309540d0148000517000044500c0b400e0502100c2c155039500040104140c0e01042c044102c4d40c4c0c3da9480e0b01c0d402a07403a005180e4041424142014510b21030b82d006810303a4850180441c1144614141004030b0b04100c030020705094403070391803141c24140707801e007200490200c0f0054072806007056006849440080c0c95804903403035640c02c1e003084000c80f07080c007070900c0d1006040b0740c2e5461b510282d85075a005014016640e50040c000821021080084d860070800400004540c00c12004079940317000d6003801c10180d06020b9019081d01e140f000d55401c1d802c0300542030f24007155180e244000c0c001224904410506940d110500200103440c04105802c07401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 713953920 1250 713952670 713952677
    0x705030d020a150b013b0406120318090c08060a0905090618070906090203062d061b1903120915020d020702102606010807030c1103040b0304051002040312 68
    0x14898012151421603202d214000d0b2600383c0700c0550000705140c00c19059075024040c0e1800000c290807c0103c80141c400d500c81c4010074404100064010741c0c000c01d1000045ca4583d81141d0b40d01305032415284642401000101043d0401005103489800300c4040e10040a040049103404000f0680c0c40e41e02410800240543d102c2884501c802003041d000a400d850300240001d5580340d4000c40a500140c5401d0300c1100d002ca5540d0014154110b00d1002c1d0345050303101440c8600d4141800f40302d521151200d80c200854004407071100310100500019400068085106c0d40b0046c20003d04101d1b0114030001c0c3e0b6401c15124402140000d6120024108d48410041e5100161807001001b0703c24804e009400c042509055038241341c0110f403404030f02d025501200d00321040060100d5034134000300c9500f40864182d00115680b02d02c2a0300c010007642050900f40c40010340039180d01d00d035800c1a441260840000801c0100b00700d001d000f2000105500e550079414103081d50f441c040e1400340e080b80d25082 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 713955170 1250 713953920 713953931
    0x200c0d020402090a030305030f0c070206040608090106090c2c0a0506160606170609070303120c03060b190e0406060504050d150515040c140a0e210705030d020a15 71
    0xd41d903032641240e41c0180000c02c005080390380e900c2c0141042d0000c541500224100f01e0006850f01c6402c1e048800752507000700850700e00f904205081d80c3c80140580618103540d170324000422454864441c0c05130514043d101c100e58000303102014407040d04c000c03051001c041c00d51079105113940c82e011003071000e941c012141540c0715802c59030b668000d40180d8602404140c102480007501d45c0340d05165480d0a400e2006a801c15544da003001950351195200040020b201c24000e00e0075000c5540c0044800b8446280c08280a0798601c80007009420801000165001d410042d50005803c00c0b005030790ba00050b01d00b44506ca00c0d2100180483c041c0784502c3c0c0c080d44016184c40100314010f264039644034400c4400704400c4c10016081c5d218080103642007801245410b0801d101d560250b0903d401c03007040340c40348078038100d20ba9034202c5400c030740c0e4881d0f150005860600f40b101124030400514611014000900000b460542010f2800040010403401d6400c4000303c0b1020030b4919007118001400321001003078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 713956420 1250 713955170 713955173
    0x3060e0c0a030e03040f030212010504240902121b0102010902030616270303030b06030426040803031f050604030b22200102010f06120b07020a14070501200c0d 70
    0x15080035882c1014a001c00100031550400003e040c6c1d041d24001c0d1140c000042c0c2d09880182214070540e4041c00f01c014030b110b841a840030055080040300c1c03100401251003103c0e40d02040c14186413811025642d08800d403a902c15001c404400101028248020700c070909490700403030703103a003400b4005442c07000b40d0140f01e0000a006080340c2e0301501600c00814000d504030201003808007121701045002038208140d18000386000340640c0e000719048107500f0f8000e502d14480740b080600203050000903000034000010205011300145100d4445c5201d1452124004001c40e01c2010070f40d0040c0e842200103002c18008500c07480d9140d07501852440415110581031301e0807141c0b4040c0044010100034104865210510700c0841802da204020307002844042154103909040e10118080c48043c06131368000d10011031400b800c0e00d90400014016210106a07030703220000401079402040c1d403250b20047d000c0020356030010181321140c2004150058940090201c6a11485c0d804903d5101b0364841c1302060 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 713957670 1250 713956420 713956427
    0x4020604050a030309090c05040602250807060e09010e0c19030b120f060a050c0a030b0d08210c160b150603091b0406030804120f0203060112021003060e0c0a 69
    0x30041d10004026005141c0d503032500030180c124034080e18500340d041c00c0707001402d42c0c060000d60742502c00b550003500c041050501d80d1a0300000b41c02c5008000c400f41200022100400d001c20400b130605544e400c07801048500078401c8950041e40b0540d02e403611002000000e04e20a81903410100381402c0c402d61440070b00408034090004a4141c90340010328540c0415000c1c40020101c009600e20000d0750020f940d02c0e40507070100c9000b284e100b8180c8000300607088025109900c220200400100141d20006080e190584140c01000e1500d03080c0c0025200404083c5e90944400c5e031103149a24902c1c604140c0300b10f0000000c4100390010301403000c0ca00454003c034030031b12403c00c22405c080c098940341d25280c07400c05c0e42c4200384013428421500035041f100890900b40070f0388080d02d070846221490b1514048004c145c0162126082d2f800356806659100107a03020f01245009011440b00307910065207d0041142008144000000381807404404100c000da00200b1142d00003242c4c000241c03900d1405500740c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 713958920 1250 713957670 713957677
    0x3090319030c021903020606151c0c02060c090d080705030d05070f0f05160b0714070309050108010b180103182306010b1e1b0d0207090515090f040206 66
    0x51a25030605184015095250b0b000103181c06256007103c44890b9002c2e119440301300e0300c000140068100d031000422030b0a081140319501c1113260b1000c0e14080252810280d21940144d03007401c156191b180610030f00b076040050039000440341711607a1414650f0000070380b809410300e10082c01d4400110f10841480306c188182c136070850220100344944e02e00118020140d004021643c00402c45e9030030051800c521603425102c140c5c0319050381f003017071040da9114017202060080038001001130b800d00d8241034280c00006001d07098880e44424100d241010000340040e001600a14007608040c0802c4035840316a4001220324242820000340c1150510702c1c1e1030401111030030242070034508880b00021134005641d41914403280c50261036081e40c13038208160f1141300310240e00e11500303606124032609140c00c8000f03080f0540c0c085495004840e8044005051040303002d075800c00368004050400824079140500342d4806002e0740503e40c804055000620200700c060003800303000527248000f07011502d811044 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 713960170 1250 713958920 713958937
    0xf0c1c060e040606032120160305031201051e0411091c0c050d15183311070f110904140f2a0409200a0e07020d05030903 53
    0x140c01840d02d03040201c043d01c0c0c0c2e4070048840f4180c4e84111190001024554036000707006965491316507007600c8448030311000d410401a22030080351005207054141d41d00c0680210b10074005591514540c1c0040d14241f207059020030f01030030f030705d010038882e08981c2043d1408450044400050b80c0d2000420341e201402150b00300341d000085074421001160040c122200828820700c004512252114144141c1203440c08000302805d0607200e2201106440e90010040c0c0650340c40c00126002c081e8940600c034081140349086822001c07854800445400c0b0300400001404603414010900022030820303081c07040d020040d0901198202c801d08114a2203980c500d0003100800070022410203041024140b40c1603032856120b481003403440295444082080703402c0c05002c0b61004c110501e1041c51940c205592038046a119a481250200003411548200000e108001d241402c0114241c1440f4005800746c0002034804107000030005040e60001d11038070740400f0b0b031404c035840f030700c0705410b44d480c50051605 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 713961420 1250 713960170 713960189
    0x708010312032d0914121b10050c0910021f1503050d030c020610030b071d03011a0a0b1309020702030717010c12050601140a020f190302060f0c1c06 65
    0x900c0e03d00650590012407000d80502c14003103440000c4401d040d51600301a62116410601344003080c00003400c3c520203d403220311402516000c5009498413011100c0480c3c458030040400b0171110091705288002e403070503080d01e0008003041c1d52503d500c491441050120759049503151011840d594100301c07038500056601504480040c2d50720a80034000d840d498140c480144030b0400041d0041401c009007000712a048051101c10341c454940441d0402c105812030140048200600d80341520f0034030a0814041142200d20300a1086200300052818550b1100515140078060146030320040158441189c41203040140d0f81c00152001c1390410030140e124810f01c0c50b0040718a40131f5401900301e4079a40c81140d886441c40d114050500007200c4082e106140045d43d04100103043d420070f0401000394080742e00403030b030101d81c86040c0300d0703d401260754003c5001d105004a640400d501004015008140800c2c01c034050302e04900301441d00d009401140f0b81c02d0080482030f4070040c446a2110025140410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 713962670 1250 713961420 713961491
    0x12090415030501061d13060203070306031a07090506090a120201020f030a0906080601031a090703020d15141c1119090b0307050303041a0d0f090317070801031203 71
    0x1400b074000c14452041e00680c40001043d11490700e06054107510900d03107035901c416a0455521810000d410091100051556a81021000c00c49100c000e000c540554015810945000b1000410701020b6600080c000c6c0028401c042465892401e03100c20b661405c0c01034807402c012400100d16180d0404004011070200107109401154480849400d851050711001520745800004400716003058042190fa0b016200b0301007070300c0c81c0c09003086030080094030b000750501c1c451405c40000c80b200021820908003805004000c01a110b050035202010b00b1204010942800d85540c1ca01802805005140c0b13540751004100c117549520081c0c0c2040d002441c1000540c0e16024020014184506400d12900c031fa41400109842e0001c2290199000003514078481d40319201603108941000307080d00200b0380c60b29024005c12040e4400c40b60000d01135a80e203203001c0545500075007005000703000581008440c00042c130104c0d0802070440100380301450001404240c040a08410703100e030070340303000244e129003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 713963920 1250 713962670 713962673
    0x10e0102133305070605010e0705190e031903030614060a051b06010f0302030613110d080f030411240f1602040507021e0304080703031b0516170109051209041503 71
    0x40d0140004512501e4100587e907240d15590f20118011500b4000043c4100b22000c4d107241015003500f002c921500304228803104810000f824207140e5815141c45003e451424001e040e4140240b400400444039a403100f40004804985644a0b01c50288140840050701e51342e02e51064865100c03030f41d01102900c0865869201d0608045454441a8400d2240801182d201044608044100c651210b00c2040c5074111000b40040c004455000b46ca0406040c0880b105030140c081c021407040384602c83c116280c1408608220319280c0300a82c0c00e03c0c203280000302c146541d148004a441c416101d481035516421b801c0c1460484a03190b00d0029009030a0a003071021441d00040c5038250440520040038810111800340390b034a0089124214081c0c0c0b0001080002c40d015465002c40741d0200f1490380c3c649911611103600d0326096241e44882c02e964540c007080950100f01c100759510f0316050080c0a00080748d02c600f0340c0c55488400a048141b40044e180d102c541e16644030001c8070605650303041c8032907540e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 713965170 1250 713963920 713963927
    0x150115030e07170d1403131209080f01020d150e0a1505120d080901020c1203060d14030711040603122706031401240804171902010e01021333 62
    0x510180201c0c5c0c84140040c0c002a2807020340348a50442c0011001c02c0030280c0b41c3c41400309120f0078180030311403000000300d03108100b407081002c3c0325007220015944d42801c110340011034241910700c003075800c00e014040c0003503020350303014940040321100c002c2040d4004c3d44454020502e0fa5120541c02205495950625400400c80040d2040c142d02c80741c02c5030340c900231000d00740c1c410208a54520340002ca130100a90398264042c0d40c0050029164110603180340d6580d941c20410b808806080d540302086050403c0766444c2602170000040c0c90501429165596072800354a22542000c103104c00d09400000c140813518125100d00342e15540803641c10f542d10b001070020300030142540795001000c030020400001c0c2004151410300d5005002449111001085415041c0070b0801c460107000400a4030091104101601158041c2030a0f01c40c1e846d08c4003030182c00c540b8641000c001a90040c03080d101c008204051000450740001602c2090f9404608006190a905d200f111800041b801c45008401d61 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 713966420 1250 713965170 713965183
    0x12030f0e0c0312041a0c0f160e0619060813210e0303030606121003020a0b040806070e0a060e0f04180c060e09070309110d030809150115030e0717 64
    0x800d50540e2010f148219040d070140c400d40c02002a404101c4081000c10755946000b001c005100d8070a40307200c0c000c4014010b0401609462910312010050020311902d038900c003195400c4101101d0b0544820030400c55081c07c800749100d041c040c00340000008580754070421001107000c1c4c0c0304520403004a0348007601070801818514000c0010b8528a84d540142000403c90303000b00d1008181c182040605001d681c01040002e15160105584800020043c1c071003030200c1014107032842406483d0b0341410f0081c0d02e00072000b00a0f02c1001103842660f0b1554a079028010b09030741051070000080d811900115a4001c1c4002000c0d42151600c051240c1d40380035491a000d04034403031491100e649550f64000c4903105402c81c815a404103514010a0a0600950000581c00d00c51014181c503401c00c500042c9000c04613000c1a4041280b2404005c1e0b64030301840b02e110358441d982c1d111003140d418032100c80c2d80c1641d00b884c51070a050391410200014507082003068010806200308105010301030300880d44449 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 713967670 1250 713966420 713966443
    0xc0f050c1f030f140402190b0a020307031b0f020f061e0a27271404050105070201061202040e0708030d060302041503150b01120e0601080f030a020a12030f0e 69
    0x70301d4460310f18a41002c41c001c82004518825040d071072905c0342d800700284103468900c03282031400c010b00c0000e8080e558a02400b01d28800c1c2d0007545d201c64041c20040c00c03070780209442e070011000385401d0800007000c2024800e105901a01c0b115501140341010401c58450844045480c6c1c080780d502d00c030440c4505004000c001c02d183c0e1400440c6030091260048941e001c0d0880d118081210810700c03520442c3d07000000414a902c19004034010804603040031187c1c007500703031170780380007a58108070520409009440e0002c40b544002c1200a00d030400e000038207a80e240c002481241c41e8074540c84980300420425000d012802e040c0e84c5e07101078800c0040014070491004178010f40c10700101003060701c0c0c0c981c0410222038002444407101d80c507983da0f10f001000e00f600000d041c41b4021208100c0182507110320040340c508403008040f0b550512100614000d02505007240caa4010010205074030b9001c02d4038440d0580c041c0c2507070007042c1d000206502030501d20064402d214680302d01c0e1886640c00144e04911035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 713968920 1250 713967670 713967677
    0xc0e0a120515010b1608270406051210020310050919150b0304080c071a040806060301110f032203200601080d14070813030b01060503070c0f050c1f 65
    0x548842d201c242059409110342842e140c4180001031a091011800d000f20610a102c07440c40c007480303111205954800403461800c070070018a601c3d88a410a48a030102030001128045120b0445c407902d1544d03920301503054802e00d5000320100d080e54007416910005401d0050042e1361914201c1c0c030f0b811104843c0d0810403003013404d002d0702450208006000405030b504140e401c13860356559807614411607100d003514500e00d12070340f0800681c202e610442808040c0c1d140030141d60f141d2401c60160b1422030050306d4140300764585588000950300c10003c07144614054540592680d40c0c1c440d2095100142150230740d205120590003108251340222800b10b095512100e0703098141040ca09aa40c0345d400f401a21001e41c4014840000d00d4045c0c81c0c00328200d4000c081d0710785131441d07a03600e07220701d03401c0018003c0b0300f09014030b811b000300036104184034098a0649400da0951a02c160000e1601d41000c030054003808544441c0d00600406000c0b02102040c00380a00c4100070340c4080c8041811041c00715017001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 713970170 1250 713968920 713968933
    0x10e120a2306010324050f0108010e070e0609091911210607080907051917060c0d0203041502160b1623270103110705100c0e0a1205 58
    0xd4a181c181c03001000d48074900100a2a800c641e41c0140346120b04186042d02c0940e540c1301000b40c4224001d1520076020030508045139494110340d10b0a590600f03201180942041100b40076a40804810b558000000c50321020f050319030030400382c104011744120080322034400c04920284441d520303040c41c0914064806511450ba11900003501064000c00030f41241c1045002c200303821f2007907880315000010380041d10059540c03400041c14803014803c0c9410780d074000020030081d244580c0185402440032901034030203031601d02030b00501880b61200b0000543d601201080602401d0303503060806840c880407c41d0b5400c016540002a9480c4d4001194004040700000f48070545c4d007082407907029460b0300c0b40300a01601410f0561420080e03001001400b80510031100f0314191115001c8207200c509580b0042c0054180004054400e1954401d0800504014410001e00002000503101e1180c64000400704c0d4901022150490b2491078168040700303401c0081119030382d429412501c603100b40110f414 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 713971420 1250 713970170 713970203
    0x3031b050301320f06040f03150c051306050a020a080301060302120622200406110f030702060909040c030606170f0a12080405030904020f0301060f0e060a030209010e120a 75
    0x20f080d54002c402e01860742410740503c50f20b04103a2101685040010419402d040d2144da100d0f10090013a4001e881090821140e0440040b09124881000e10b041c42c21500c6c280c003000c0c0414411205100b05d2040144c00104204214821f020401550740c1c0044040e9482d60f4403c8000d019410460781c1440760001c1202085440c07030080c8030a150030040d40841c4404a4003061003400410008003010911803100e4501402d08003404000d10140c902a2034118040d0101d443d428505403414070644016482007010b0b41c090ba0740c1c4810f864154400311190340710f65940d45048a00ca1142d1350000700501d00385140420702c490f00f168410007850b81101100c86030100c11030043c1d500c400f1010050401c02c149456184400d214071451948503000d001120301e000c401a002c24100c3c1e003c0000613000030f1010005001c8507510a0503404405020320305207030700508443c0041c582e8810900c51405040d1f000034406001c5c0d02458143c08541c42c01402c00607510034002c43c1c2a03ca4507100b40c100caa41010110844 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 713972670 1250 713971420 713971469
    0xe0a0c031d1002070204090f0f05301b0d0207171204030807050f0f4206040b0a08070e010b04030503120c0c03071a01061403060d03031b050301 63
    0x410040a40003041c81d82c0100031840002e40c41204166000380c1c4980c2d080010403065180715000724400e2003841c60709405c0b82009030070803180c0504150301d5902c85181400c400311005441111200c0780704029030380c02186a40040c41080300000c0c43c81d5001b4095031040c21900480c40070308494051540844481d0100b50154844000130040010b00714180014000306543c1405420114840c42c111141050a401001c2c134100340000100041e0b8040456160a031120318409840034203015114040307800b1990b11010f00f192200101604246242c00041d4542d4480e0040da88606020300a181c05030b4403003c0e00c41c0c4400483c0142c1c0c00e0b25129100014501c01c1e110200c1d402ca84c0c0000c091801c08480c0c052000481c5005040d80e98001030601c20031200d540c0600040203a1803150f844042803840d50402c10096290513030145003400400c41020121400030000c0f00c0c0d0105049500c18410358503440d060b001440c1c000c1c41c042190195070150380000d90041c000f18107948501055145c1c80d440100780c81d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 713973920 1250 713972670 713972711
    0x9090309030307110a0b0f190305061f02120f130f030f17071e03080108120406180e01030516081b010c020d060f09060f0b0d080c070e0a0c03 62
    0x98050b4400c004074004100ea1200d101e40c03200009200d51001590750b06121165080320030714401203071000079115030321035241d81d800f0f5140c401c42c241404a0301e401c000041c461401c1004611141100d000152081031080c001464096000501107848003513002030207544d504041e00d280b002607030b40314011801180000c0400100c0fa0310600f20f03040c1c2c0120341d8415180390301e1180c4815070b0a00c14454100061007091010052442e140d2009000508a0a00800c282c4060f072001196400400c0d100d0340044072042201d05079030b030a0520b160a0121040c028045052070307880745010107148000401007003c04035074414a084010020b503055911601c20b01e454060081c00044600c0707813460620b14950140d28610b040900050802c003178094541c031031205407000e0441c8014003070b85d40c40d0039004020a5124083c02d01d201c01104101000364480840c0451540e102c0c09820f444011403012548602000100c0140c54180728981d510306140e1008005070414404101c00719040004010145650414a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 713975170 1250 713973920 713973937
    0x90c15020f0f0703030f0315030f0506070e06091009080a05010c180b03010e060d020a0605030a18260f0a03050720070905090c0415050103060506030c09010503181902090903 76
    0x41d126080c910b9800741c075040020246c0700241070b1035091810301d000d080c00b2500015802030300310822043d014605907040040c018000014032280039150055034941e00142c9803e07500a40394000122692602516400903e03800000c2c01c0c0710b000c450b0f804210303041d040702a051000740c0300c90a94070144444110361215a004175121080c0070b00040080304030550b0841e40040000e482c01c41d0401e01600422107030300d086c2e0081d502080c07001041c003000000300c0c80798403101380d003440d130049241d01907070385005040c0070010805948880c801c90741600070f40b03900216118104000f00084d940e114034000a00504012941c440215003403641901b40348110300542d14104c00d101e000343c990541422001e800510000e4101440c510500030700b02d00c2c070740342d41c0304a1585501c90210066002e00d000001000d8404070780003a80a424203105003c440c040c50b0058504200003400e18031740720b580e015500e941010340381106170300500c11080d29807a603043c0d401d03503003082c140244c3e040c038003655985140565a120f501c04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 713976420 1250 713975170 713975173
    0x70207060c080a0306120b042001020a0b0c0913090308060402030c070f03021c020102030a0c09080a06180209011d06030303090a1511030108030408010b0d15050a090c15020f0f 77
    0x48110025105400400020354a410001091512130070342c04c406d041c0d0f8172403c48030070b0070000506c8144200c440310000400c08522900d0300958803030000035118854908002c0020807102d004c141d10751084020348036102000782c542035100d8011448080680600d000544c0460600000f20b101c44c105030080764415241988060301c0c0c00010f0743d6618480e401c170175080d011030003071124030504940309170b014444108142c2c0c001350302e0742032a030010422148200d91034000d000d2400803c000600002c608800c6454218600180c0701a00e1112080c0c0070300c00030381c000d41c00090000045000714066440f14030200c2c20817181e02c601c4da030303c4092603038a10082c3c942441d641c2c0300d25005000120b02040c00d0740d081c0700301840812080d80f403010040c00c540081e0407034030f426080454103110003071013441041a03041040794414a241c0780c88c0c4031542c102015009240e04180c5840c00540c8a0225400c8988003c1e1f008a00c0b140055840c2c3c1011303599511070480c0c03001802019007091609500250b04070986d800d440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 713977670 1250 713976420 713976437
    0xc041b0905040507140d06081603020a080304080a030f050d18060f09080d09060b03032d0f03220b0108010b010917100221011206110c0c0118081e0607020706 69
    0x2c1c520105410070035496411b1a100d94002c40e14901c10300102c02e990165034000e041d120f003988100404c4500a8000711000d40c010301c0200000200010400800c0303402d4200700d400080100760841e881c1c070a82c02c2800c0c0d514101174961005031082c102a01d0024041c01c0c04105104c103540e0351500340c51031240d016200700b005000000f10b0345204c0d8403204032a8410540020b098070320070003007030550300080c041e18080e4907905840700030036074008034400e00003034083e103aa85030207045152031842d408040d08283e0414508101817400c40c0818003009100b0390040c103e40310941c1d503010018017800c130030080c090014021081c000b400c3c84900c0000901281d4000c0501030f5a00040a01402501321086540c1031020303142030103003110300c5040c456000c3c10329411046240d581e581048819a580c035000001c00031810410742d0511403000c9103101180109203001e801c480340c200401e680602003504811000d000341d121b40411b948006241d1f20001038001d05940050703403442c030140e8642c0498411040400c1119 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 713978920 1250 713977670 713977697
    0x90a0b131a09150a2a1406090601090c090302121c09030c0504090309170601080d0807080f0907270c080606030c0f040b07031110050106200c041b0905040507 69
    0xd20181035040c1d820315045e607007120080984d84880000011503001602d07141c29040038040b1107540c0340085001d03070006228501b8080d9200780d44180511520000603540c000c6403c0302e0f44600084002182c004100741203203110110400d44944070091b80180e503914800c0d0105005001d140c5031012660031403001000c0f985000148809000044021010410018004911160b80b402540000c4035410010328841d070509444034074010548040005103d01107040000107507014088540c010032203c02203500340c03074004100707103045240c4c5c01c03800100107080b29039004100700754a041418004d10350288240f00e02d0510698007d4420741e0805e40140c020000200d4000c440f034020700d101070109401c1071820760b81d407110700c1c9a50040a0100c00181090042c074000c03c5080001c1c0c20315503410b51041015516284010b4501400015003041c41c0d85982840c0d003250b01c091040025a040151060140700d8440e01205c0810b00f038000b000e0007140700c003503010a45080500c1524840ca8103603c411103420110b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 713980170 1250 713978920 713978959
    0xa02010b10180b030a0603060c0906091a04150e04331d0c0c19110306010b030a090302010204151106011d062b380705090a0b131a09 58
    0x5c0c4a22031079034840800100044031481450941c0400e5507c1444c0c8a08183c002440b4913403e622100350a407a02d80f820781403070022403c83e02200c20b010001019000007182c00e81d515280b101d0071035806031034118a4030b92201b40e030700c0502841c0304008241d0a02a140d0740c82d03000c002c8990295003260035a1500f101c01070b00c0206070254110050441c0c003030514490b48482854000500f003038000d1482a2113180c41040301a03a100a14010224003404030f0b503060220030746071400010494203299482d403003010300b414000c0d8100c8000d00104a0703880000c460301c0708068940350b80e1005200b0244202000012100810f01784540300c42183e1880d41580d0300c8007005c1055560b0b0820000745407002030384101d00c21111005014003103c1c0315a00c20064401e6020544038104010002c10080785540411840702c0004124080c0c2d11400c542003840d1260654408940344d01119007140341c042d00002642e04008502a801204503025400c16082008844e200c000d214010325090396002285200c40c80007840b00d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 713981420 1250 713980170 713980177
    0x31005120601090518030a120e0f0d141608041518030807020a090c032f0d0906020405030f060907140616051617010606030501050a0b070302120a02010b10180b 70
    0xc0003140d19806103481c021080c02e55114110b0000030640e2307950000c0e589182d9000b848003c40c5000003920b440c3d03900448103a2280c120700e51090400070806003040b02e9a9000060350901d103e070944603040702600c0e02d4101e11b25032103400340e0801d241208050a010500c140d0240032850a01c50740c05072139900d181c2e188441904410790490380202c0d174400c0441d1000c0ca522844086500d00c2d540800e034014042104000b12881459541221440c0c200640000102d1012541410210600000e901209003031a000078011030304501c0d810b020b1004480001400098203d0054101c04141c6010941c0c80a00610088080d0212500118240f00055107400841c1d51a68414020f40945080c510307540d8400c03030002101d41003140c0f2001501c605103000f80c02407003100082c12342d508041010b5414600025031070081441070758410300c2c0000309141050700c24020381001d1714111803c246c4a4100307803400b9003c1c128115090b0b0103950803a2100172114840c0e101510080f0a070650340441c682003c15880c2c2592 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 713982670 1250 713981420 713981431
    0xc0f101a060d1e0203040303050f09071508060621180607090608040218390306060c0102070f0809120a03051602010c0f05030c0607050403020f0f040b040f020310051206010905 77
    0x3442062006080b0b0f1140c0015845031b4800d58000680f403404086030040c00b40007402030061907000302c0c414807100c0021001403c0c00c0d000703410701c60140d07070b50351002030b030701d8451010401001d000258028110320140380609010740da0855059010150b8881031a0f583d04048805500280c00b0700c0d400c001d041d00503544160490300241400c14000800e01802d88180d006886524051040b0032a80c0c80040101007483c100040d50300b145804032501541025250102030320541c4034400004800b80c00b22400d5040b40c041c42c1e4130110b812002d00c200e04243c007007504062011350107509203840d82c02d01e1140101c1c0000c0b41c1c0d5070544031076050400017081c0c200c002034810b808906000040f0309020100724581109001507200c1c5005580c2c400c6452011400d0180c060901c409111042c08144010b0350b0700203424501080c15103200340001c3c043e40001c0e0141c610001d1442d0464909020030040d2003941c0c004611442d02c101e981100c2a40d942c06001000110010f021030540052006210b0752251f50400d54220 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 713983920 1250 713982670 713982701
    0x913020105070c03030e041a0d08161e0201030b040509070911040506040b0a030605011b150f050907090b0a0f050f03070b0c010e06070908150603030c0f101a060d 71
    0x71515030f5402e6101001500250040348110b481d0784200d1500b4010101e501c0751301071074004421401e2011514000c090342d4000c5c00d404012404a4010f07010420b0b642d8556040303806004d900e151026080740300100e489046e4002412f140e4600064182405130500035900c280081010078a44100c01006000000f0852079074002000001241e40e126005070003e1302414645554503200c0c101d001d4212000c0b68005414421a4480c5200466010460249098200c001d85000d43c441400a2004000b0b841d000d0210324502400e205044800040707420681d840480208500c8065904000020410b80300d40016915400301c02e0101d03040c003281c0d610445601408503210f158452148107202d03003082c80c00c0c04003a903662180c0d2440b554108402908024103082c2022203d0a1070083c0761906a1004404800450603001c82c0c0152001c1003220400300043d011b480b40064000000d60700c1d03045501c1410f5500b8107080e081c0c0d4507424150650911140300400881ca0490443d0024000d0241d401200c13448 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 713985170 1250 713983920 713983927
    0x60206160e0415050f090603100c030617030706050108010509030d1107050604081c0207170c1533010e090a0908071101121e0b060403020303040f06020d0e0913020105 73
    0x1961103601400d00f0418038148058107071420003040c0442c0285036041c140c4110ba4110a0056075103020503050007038075045001095180d0305010503406848942c2c019100400003c514000d030b01c1010000d814482c0c4280030a201c40c3c2da1b906c030601d090303440a1f07070300303010a4008004012082820f540140404c5e80b29070403007030401c00b8070703241c041c00c00740b040781d0517103640d240040c0502440d0b1254120032104a00b0003000c6040c10b00544074030780c0f201e20501c03500084900010300840e42d000c040043c0035503a9010b0b40e02403d24a0100000041004c0c59600c804400715203800d0100c007000e8040d0554000001a5030700660142ca080800490480150841c885965a003c0407404a55060000c0000303500600c0281130036603001000400b2805074a0000040c10310b401003060300c6900011229034102c5600d000420019903100001340ba9200b9548003e525200009000500f4810f0030040d4040728019001d56100b83c0c9660400d60781002108038242c1c0c40340c4100b0014a401d00c0c00c1113400151801032424905 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 713986420 1250 713985170 713985197
    0x708100605070c031b0501020d0201140f060f042a0e0d03180b030c04031401200d0e01090c0504060506040807031203020d020711030706050702061206010c0f060c1806020616 76
    0x244881514402c1494030410406c1c0100d58040000f5184091184000c000c0c0703c1300c007001d42d00741e180d0103441c4105601c05500494841d5644003050344031650010403c01084410184c98840c1e034002c0400010f0341e403000ca08880c40c0e80d015048410843c680034000c0c2010440c16602240c407042c0003c41070000101903980404c1c43d5180b4006948a072641c040c019030ba56040d030416405840c3c04d0480e02d0308581c100444007400301083d0b4003106201d04806a142d4840a00c4001e1a0181400c110403040e590300c0d03c0c1c1020180700280c1030b04012103005840070007480d030b00c6500b444054411030017042e082c0e5206040810006444401e100f010140307a240041c10415030b148040281da00c0300006a80c4200400240d42040c81c0c00d118440003007084e07080591038020780ba0b010030b5003402810190103c0c81c00c5e6100086160340640c40d034404169028000010750580c507c0c0071401880742060070800a03e030f58601550900e11405281c00780d6940c0d4000340807698a108072001c1102540c40d013a0b080010452050b10f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 713987670 1250 713986420 713986433
    0x120403051e040e0a05090d120b060a0c0605060d020d29070c050d032c0c04110c07060f09090b0f09090708330406020c0709060e0708100605070c03 64
    0x1624080d001d1069a07035145041400d041c92100a0b000041c80c1d8a4101800090500020010780114041c01c000c0e4020f03242c0c020b52401011072900141d003056000400d5081141c1c0b280e26025a680b0809040042e0b44a44043c80120f040781c0000075004103005c0071400200d007640c07407020034482000c0c100c00100030300d03e5011700d0392000076030b908000b050501fa0f12404000050045072007040c0c00340340800600f03100000c1f031154040000c24144c0b4a105200729504240404d00421000880c080c00a202d0900c45c5400e940c000e60080b8100e44450060340341c00b06180d0700c03940d8003540321310f020355880c4002e0341041e0380e00c40141030b84048154401111400a0300350f444584480b442802c00038042c050080c9403541c8942409800c0541d040c600503040040e0a0883d90004011031301c12100216144903520b07450010003c1c030504c0010001c500c50440001806805500144161a0003c0480049440c1c14005440400e02a01c0704809804280820711095215101400e00035003e0640002d443e652a00c510b13 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 713988920 1250 713987670 713987707
    0x5030a120603151407110309040f060801050c09030d02070b0d05070c050604080c010608030405151b151909020306040201050d0b04020c070f05031c0c2a0504051b12040305 75
    0xc0b0741840d160703041000040395140404d40d1001240c01e01030124403d1a184580364441c841400384910360764042c5a0b03010f40e10f5841403028001c5203008110a05080d102c03e480c0d600306115140c0b00c0d01c2001009008644003040e46400c030340041103180c0c186144c118006000e004020001d60401c1412201600860010841d140c00f650150340c520765100d10750f180040c01d5a0064010314000ea10410041201e038542050518400101001c243d44640c01c051403815a40d0026102d0072140c032401000e000106003d00c034460084d2903014100024030210054542641d025210195040c0c122100040c05940110018440c171010440002110410440014200e8124001c0744540394041c500c00c0c001d841c9a00201c0c1d0142200720020414a640d079002c4102103003040c8041010440520540c000b08062500030f140d0407480002030b0b15000000005840c4e800c440c6105092107a07040c540402c078100c119158016090501c243d401d849c001c00c0c82c25010300072502a1084003000401c00071040c01030100d04d280c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 713990170 1250 713988920 713988953
    0xb06120d14070f0830070c151a030c04020406052a060106211802040e03090411030610030b0a06030e0a0611091009210f02030a0f0b240f01020f030a09091805030a120603 74
    0x1c000c000270404060500c0e003240b098174640114810001801134640140030f0fa1411210350342000c45520403060a401d072078680c0e803800f81c030034441d8000100d4400e81040c0d0740d2003e84803403500111103803410021081601e64001035100c80964428107031b0090705094000389a4040c1100842e40303442d403940c0100c1e0489640203840b0444800200500c00c0c00c1c40c002c1c000d2581e900c49854180700d00e03074071107000482e00e0003503110b241c05050340c2d8101d415403504140146108141c20117404c00c516001d40e20755214590100c1030703061148040c40c1c00c49038190700440d03030b580542e03000f845410400c10a446620310310402d20b100546242211500040050f40d04102c54082580301c2c40082c1000041c0c1c1c078007054400c0c40034100c011404c95101e8603040c00410681245614001145c00002d21210000140e041c03801504e0400218000040c0061201341c0082c403680440341400707420049070100000c01c2c5100c11004030014059007013044101c2e65284036400304a80b4410024000400c01c0c0d0300c0c0e981c4078408101505 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 713991420 1250 713990170 713990201
    0x50a0b120f010605030105041a090a0807030c02030c012d0302040f1409070e031b0105130f080c0d0c090e0304090e0601030b06120d14070f0830070c15 66
    0x1070700108007801200010b12040d0000d101c40d0500e980d0b0501d640a055480e000b616952100080d6203003010000c1103160740e001030240b50340e03030b010b401c0007030258100100690007445141d010705950351040f600000c08440008a40711003e4954490f980a0f160420103001015000e000104034a20304e00e20040c018000310210b08600c4030000c041c00b0340d1140040805041c0b200a4555030007a8401144154060b80e001515540c2d155041c801650540100d0801107000748001c0d00c08982c1140c0d03482d14a060f0f804404c101c1c0c45000322501000040802c9450041000725100000c20140f1102d0304a83d00090305141542d00b05602c81e155641140c00c4502440140d5014200420900801c2a8100e4003e5000d03200302840000701c06900380d4500b000d01c01c8030200320310350316a000d00c03812401c141e903000c0f80d21820001d040003d50516601a03040040043c43c0541c03203800b001d50302041c0802d8610760741c0080e46c66074000d694100081d42c000d04d0350181502c45402c03144280081c0c005038030591401903036191 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 713992670 1250 713991420 713991433
    0x601080303070f0c031b0201031404060c030b03031c0c21151a031f090603050a050c12060708090a0b01180c020303060109290f121308030109050a0b12 66
    0x200003040d0302c28a429980602400211180100b40d00140c00b821b9441c52010f4100e038950f180c40102d0040040d4010700a21a00c02c030184001c100703036500290b4000000d9070303040c4840b08114003015102d00c205150810907070500d080d04000b4802c83d8221034501c500d54117002c20184440c400404041d103041c03130302d40c030200e6580d84541101400e001c010805881400c200fa0b08108000004500c144006002420200c175028140030490307030b5082030740014005050080c8102c41d920f1420a80d5040c884c0011207841c000c10402c41c0c2e65080840d0b01c1802040464020b1070192550070003035511481c05411100310b8062282050003081c200c0400c10f000b0005d40300042207150a4001c900704070740340d20543d0400c54100f001401403030380c1e201c804401900c065114524030304400c2c0445100342d240180c800340e4015004240c42090059000140103a80742d842e06949850f80c0d192644241c82c2c2c0003800080c085403042c0014004140b540d0f10031507010300040000200d8254a2000038080074003904080b4190f0300c940e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 713993920 1250 713992670 713992681
    0x30a06021b060108060f0a0b0a0f140301050f0f0f0c090301060e04032003030a0228030c14090312251226010302010f140f070204061212050306030c030601080303 71
    0x108005401082c01c0c2018005d103003040118020b107800080c1445280341c0d250701600c0030aa0741c07280c40100600140c19040c214030b80d10184142108401d0013014401e503e0240083c0d000400c0445070340c450000301d85008610750f2040852501c030b49000d00720a1211300d06000c171540503142441414060900041e1003039032480d251074001c029541c0c901d2294401020503000d11282c8030000241c2c0d801103802840036880300340e8810b0107a190f041c9801108072800ca08061060501d8155121050501c0a951800c010340c461101621131031050041d030315003503880042034905c107440301805490280c2c100300c507604440061050314140b41e400c07101c060321105e060f000704a00150700706140f0b014888506c20308400b012140c401c0350600860500c8081d040c0221508041000d51141480e001c900c5440d03280340783c841c0303030125110889400048040340501d1078918046008010340100c52542d03540560050461650f80c0000c83e00c40d040a1b101e0741d09441141444001c0b0fa40500c500c034060120500156280d1404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 713995170 1250 713993920 713993923
    0x120301260f0a120c0f0c05040510080d181502010608060a0c140a020f0303092a130f060b0706021c0501150c0312020a03020c0d0801050d0b06030a06021b 67
    0x42003400141e001803418690034002003040c03140340d90451400d01c08490402425030700ba04920710000d011401d00010402007200e40f900c4581a01c2d0241d9081120f0383c0c80406240e41807090f4000c4d480b981e80324055503180d151180c0c040c029420040191041d0840c1d0320010340340c03c114480610381c0981d4580c5401d014511041040365449200c0950074031a810900d40042c1150208030b03425101c0c0e4000080b25040341d8020845114120300490881c0c4d07880c076060f202c0c561540c41d1010300b82001e11442c2540890880e001000d918a104010004600d141603800007400810400c0305250150b61074007000a11140094007410446000c3c50000d6551040484002042a004004ac03000140f400005008241c1040b0900c0942c5289083c01800707041103040650b0f0091544803444d43c9140001180f181c4181d0640141156510201c01c5402d81280c80300255504002409543d4101c150303c648070300824210f022240c0c0100000c2c05035011040ea6407140c0050380d008044a5404510384020207440010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 713996420 1250 713995170 713995229
    0x1c0302010f0c050913090f050604031707030203010e060108150406080c0103110f072301060b0a12060e0a0908040b040608010503070e090307060203150a0f092f0c120301 74
    0x1007510f843c6142407100f500060a0505407071200b0101c0d665545440c00b0044002c0300b91050380c0c0c01c44d046801c140746c07070b19000789552122181461043c4000c00031a40c42c0340a0f00989043c1c654070303800c000d0380d0307595040111443c00740240801d60800200c044d5202941f10f030312800c0c0180c82c0c00405041840048000502543c1c801902800c035698208020710389654280c0c00c1c2d07202d46500c00821000c050802c001c5134030409030100003102a510301b140010369425070000510540c601c545601c403084500355901d404503038040c4507001e139407080c01001401c4508150700005c8154840c20325507042c5a295003010904d6041500071030081450f147c0180911714003003004074018070107042891741d81e15100f05004d8480c01008001880c02e41c010002c1141e185460505001c1a0303030203000c1c50300320781c0c5d80e251085010f071841c400e1540d01490205145440c3d819081e000b20003561419410400c9003203e02020000d90056070044024010b00304034400314040b180085008001c10041f146d00440002d110f01b98108 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 713997670 1250 713996420 713996441
    0x16060f02070b0403020a0b0304030c330b010906081308160201030b0d05070515190f08070201150315060b04090603060513150f020417070e090703201c0302010f 70
    0x1e000f40820001645d4000c210400d8441c284640c60301c98541e45419034801070808001004070309940300c0300080010440c44d00b99061881c0f500900c41b41d000d1902d001c01c46e0381c03a0924038006524a242442070700c0c00303021036541054803107d600c202c640b003503100c40d0303010741002107210006a500f0a0180c259a81030282903071841742201c1c440700708100e0380d1700d15560b0003103403044900909851240b0320300110100141c503a044400045100b00c902e61000040541400c082c121021529000c081a0700610511406411100003020001140d0842d11004001d0030b40c50441078910780c44510220300784403104040e0008020354607010a045003149884403c2d580300800700401d1030405aa44070100305c64080c600818020b65a00180c06480046040c02901c41c0f50404094451420014841e40d440010b03d8000c4804414501c0c21940342c480034961517021512003c0e001421200751041c2c600540340000c1440c400c0101500200c1b200b00100c00130420500d01c00340d001d80d42d601710314607440f401800303a02d0349103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 713998920 1250 713997670 713997689
    0x9150c0203190c0602041503050a050702100f2003090f1b06070201020a08130305010e153c070e010c08160305040b040e10170a020f0316060f0207 64
    0x1145500025528002c030145812024100d03051458030034050348009081c190030020079503071651100048502c4a06103240c100000f4540000a150000c0300e1003081c3c01900c0e141d016180108a45807000c01601c004036245080700da0398004c002b440a075888880109200441403203071a450490788260401e00f50040c0c00c80d194000d0701c0140041d09040e000d442d43e001040b0380040c1c03240010b0004034a48140a6002408110001040e03c20010421122000ca1384150024030013031100388200c1352210312844015246543d07120105180003c0c40000da108001d41540c80090300c0d052840c40080380c0803074503002d00650300d0b00c81440205544900010a89203082c00c11075800d403007a58a243c01803050403e0440c000071440e0b0a18101846542201c005015070014980c5031605ca010790468040c0c15209150102d11011001550001c8000b00318010f01200015006001940e0240b00030403102011080d45409040d4000301292440c040c0d030300103029656640d441001513580b020f403400c02c454103e000d96 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 714000170 1250 713998920 713998931
    0x20a021003060509041e05060c0d061202130b030a08030106050d0c021507110106051302090103060617010b090d060e0c03013c02070215030a0b01030501140d1401020408010915 77
    0x40d5120b0018075501719034007039404d0007448008805500340b14400c0320014401d02a143c24010203d1400000e030081e00b203004010413401d5652070320350810104040009400056010214807408459486091358034000303411f0703900000c082ea851120503403098004001003440451083d510a10354800d0248659a900003094852129625a140e10000500420401030414010000c910f070a41006004281c003a11040d08900d600306510080d400c004607050009180140c0011424815078165a02984054031552031364241081e41c0c0b103561000c4183e640006002501c1c1c000183c491080c0c0c052400030101415041039580e04050a64004800002c0628407805003c1030b400300301000184202c481310b0100303150401da02200d5009e800744c1c0304003951000d2014803405004003524011841401710301000c014449a220054048036400c0c011984402050044031b801811304c20705216415015110380104592180091800d981c810341240e0142d0351620b50306010440410314051034510307401400d021 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 714001420 1250 714000170 714000179
    0xc0c0a0b251a180a0803090111160303090203010b06070f060b040c1205150a030c060f05030c0904090219080106081b31060b03070e03070302060a0e1906020a02100306 73
    0x80c000890020418608084404520b107602c0e1010301d824800c40c404103442e40801c585c1020012070700100c0f903c0c9060350904210300c5205400c0002c44440080c14003440d1031802c6280c030210010850b01c6400c0b80c066507918201201d40c1ea4681c080c2102e03d100c5c0c46204040505840c041d0192000081d0003030141c0e05105030680300a41102684c25001040c040010300341d0395881d038801310180303983c10064008003610000310034003000c411224191140c68403038052010704280d003100e1610048844907840b05040c0003107190382c40c00741c0210a031580020303c010800519143c0a480011050340000740c50381d990a42002081c0040c0000c0c500c1c0c0300c040c601c05c00c000084501180c00c02c040143c0d6401081c4403070a02c0c9a1400c1081008000500105010420700d0b844001c002c21541c0b050300d82101041c2041080c804600d000150b4406903640034107554207140d40e504040d505910b03510f40041e800704003182507503861990300480c4801800700ba03005113000d00040c0140302d034058100307203884200350801c1410702 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 714002670 1250 714001420 714001433
    0x21f0203030a0b030c09130c14010503241306060e01090b030f040302151906050d020d080a0306170c150309070b0304030e1002070807091e020c0c0a0b25 67
    0xb0752105001001090301d000c0301000a0500380c1446200754401c9800080c0300744c3d90300c1804802401803103490701c11503440c0c841c5c014503032413884da40815001510400c00140502043d8400107100500c405450311502680c42c0010405640740e280c80861030b6850000b000070580c40744210000d20028248004983d007000100e00262000805d01010180301401040070540300300088400c0211285650040782017103580900f4459403155015417003420300c940410103290050b000420154005c0032a650040c5a0b40c65000310f4101d8000482450381c0c1e0000069102c9070021044150b24460015240c40c1c86200c0c01c10240701c082d1a0800120a4140200900c180001804405640e0442d500c540c50303603560324084503903070034890f01d05410856a45040858540000c1e042054072100000e841100761241c15500440d40703002d4606955800314404001c90600640c002c1c2040c0002500340c07040b01c003145d40440c40300c4e000e0764040c0d11401800100340c2d5a0601032481c401011316907a8040300f68060544544 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 714003920 1250 714002670 714002677
    0x8041814070e010201060f0b0714030f0403030c11010e0d06090302011e0f05070e0d0308040203072303010501090524150a1112040e0f190509010204030204180507060503130b1003021f0203 82
    0x414101501301403854408041090300d559030b1030415440e81c1c0f19146d00e4020040c01c4349540031100f01d200c10501c1c4129602640480c0d40068010b0500815000366440e42000b601c00d00318141c3c1555620414101c03014200c001c0072880c9110014089070318541880c02c54102d40000348840104070024201741c265984944c0c00e040300580500d011a81070320380b800001d0030035400d60700c42610980b2084400300c40902c8040943d0071200218003c00c550b17a03a98642105a41c0b0440d20294625180e0440d40940c1445940400c0409409049400050203514102d5081c5e4828008140031440700405103240f180d08000d000b0b40c1003410308002d82814030704010454821000b03400340301c0c082c0c914000038007e074010700d205041086090ba001d0045003014040e0900070b5019000030f03070040d8206100c02005840b1002500c0030f0b03d511400030101149060f01c00c8500d6040074205d5100e0403c408541c80118201070b0350385004038242030810f4a824035500c104414160b54022040e401114404000314454004c42903 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 714005170 1250 714003920 714003923
    0x90209130203250905070c1406040819030b0d03050310080c010206010b0a03020705010f020904060902090a0b030613061e120b0f0c0706050903040e0c030408041814070e010201060f0b07 81
    0x1100f0a1040700041112040f0f15401102055180004001c1c0307150380190384940d4640500d90100b8107034940301c2c0068840c54100d0f8007170480f181c10040d81503151980071445804851a103000180030000c0400503440c1142c03d4010780004201000b44802540c070b01d60920000d050240051101c1c0303101d000082d480b0f030014816001c28200c081246034100c2d01036011a440c1e5540f00300200b1011201c02030240003908085481c40c050351400001107141a018400c031a21040c008103c0460ba61509501000550009201c1034108143c0303208903025a41b1070145002600c0171a0b11140700c600041c1d40c2c0b1207030501035480480c4000c0000030420124594030302c0d498100240d0b0043d662705943d0460b41080300d04c035180004000904e400e041041106020011f44141d45000349080041d0b11045501c0c0c445000c2079070090588141008100700340078941001c3c130001c05443d00c005c01d2008000c9001003018100b00c410601103461100d07924125079083c89800081e084502c428503915041045061081c00381100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 714006420 1250 714005170 714005203
    0xf0412060b01090806130f051e0106060f02030d020c0109020d0807060b010804020f04090201090803220602150f04020a0b12090c011b0222020a0c03030608060601080c030622090209130203 82
    0x41b03c014041402c0c10242142e802008482c810342c0105010b101c0030410340ea040c4180d501c1d000010038010b214200c5441407040c40c0c0d00460400c000c6024100003580664441840347d03580d00780420040e241e43c5c94600c0d0441c0500300041d12107405061400544800850807070401c20010100801652075100c0130700c2070842030f41e0000300e504a038070068659900301e800030446d07488049180489071140310002000d0091849210b24840daaa50007640ea8019210442001c0c40d44500000c2c0244c4040d21516072080c00101070200803035071409221447d60000c1d42c1846048901010040340190420140021490a20344000f10070030111030144007074000c0a0003031180503804400c0720801600700e00018040300c00c9038210355602c843e01000e0b01c846030a0b503084002c02d0400700005108080071540328800c0c881a100c050b40c599034150043c25580c0014200c59024284d43c15540144004080e4006240148030001844508900400c8110b10f0b001700b20f982c03036801c0e650b604401a2000300d500ea0b4030110854 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 714007670 1250 714006420 714006451
    0x80105010c141e1006120c06050a05210603061513020715020301090905070b04031110030f090b060a0806040c0302010e030a06091211210d020f0412060b01090806 71
    0x10681007900c0c1c2e4985414003024043c55020341c55003c503c079080350502e00000c21007240c0d1070580030101881414068010109110204503480c0194010b003200d000620741141b034030021172916001e03088050211508034032006d0410005003410044181c0181c401006014200c3e03815001400e250502689441c030103401154880030003001c440b01500b200a00042035482c0e6854100001c0100745400c419030b014861000300241c0501c161046406490308034141c2d41102c0c0401007070241e045050f40c9004109a51040490701580321407041c021510b104903070604c00c0d410f21030200070800302ca40c0c00c44034103038206400340000200343e60210001c507030342800c04442088122000030304056410710060401800d01c5103000810a401400c0d100343c515588403003060888107610750f952080c27140f94080030400034401d40b9040451010141c142848030000241c503050f201c03a50300240e50041e51010300240940450340081000768001c0e05441e03142860701640640c5080e4607180c2c0d03078070040c0007440002c3c10031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 714008920 1250 714007670 714007703
    0x1609020a1d0d11180a0c1e050d150b0d060e011e0e06060903151b03010303170903211009020f071e022e08010f090e160305030a0f080105010c 62
    0x5071000b100c4c00c075503104078500c1c80c0b401c0380b0080050503903c0180000102040c024008002c061402c00380002529902ea80c1802442e002c0301d0003c1c1010451100c00c00c0000b940040c5c4a401d20000b829040103902000c02c2d01c52a1200c1040266810f1300992400945c2101c94500c041000c00e0030402c81c0c07100344500e5080e445550100d0a64410140400d0b014000d98100410140110720400d00645c1e02e030507211600e41c40d1040d05a4580428000200000c915880b24441c1310031070044907802c050510182c030300d010002c000080c800302070f18083c248241d000008010f0403c4807080c4000040c007194406602d010420424140a4490300e007009001d1074083c0029044007548a0314110129806030217048000c481000c0d00c103440d0780c99820749482580c000d9400a0003481510802c3c1250502140011035034181100b0310040c2c8106521086103108a613103c82e4840d102c4a0241d0003075001303001850740d0307440c1240c00424100d80e10884500344200c0100411141e60300820016805800602c95030380030021 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 714010170 1250 714008920 714008929
    0x60b0319021806070c030c0504150b03040515090a1e031418040603150f150918020306010b07050706050f182709010f05060d0201111609020a1d0d11 65
    0x70341a02c50304802d01103100c0082003001e101c424240c0340140b903501105070340d42003003000b992991350204000e218806401c1148600c510091508503124006540d0110343d403000030440b4140451b100045940720f07100880a02908140c03444400c1099034001040705802c1d10044d04170003801e131410b17a1341200041c03c0ca2028400e00207072003084200034018000c0d140d403814a0700b51746c03000356006c642c43ea141000d004000310807072040d04040c011200c1c211030004d1500340c00c0d10061a4186511a101c2644019480140d50901006018109003a000f540722902403c11078644441508404280001003000b1076040d210107007035405444928100c0e00c2400c1b030131004220002841001d150303152500ca011145107420922005101d03e461000070020340c4100389100003a01c400340c2d8810341200208400d00d000d0f5101d80700580380444042d085400c0c0b200446140343c01050584d000c48282940800e400c0c0d02d155010403050311440c0c4244000304050030107800100c2004010900a05a00115410f250341e0b454 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 714011420 1250 714010170 714010207
    0x80702090405100e0c0f030d0206150a0302090a02041403070317032806240c110402040806040303051e0f0619080a0c0f060f17040507030b0c0d060b031902 68
    0x3549091046214807103070140c0e100781d040c4681b8030520f501c014000484c100040c03400e03e45c507204c0c0e00411842d29440e14a150780041104c190750802c500160100250300e1303038040c0c00d0003100d0013680140e403107141485080d8030490740c0001078402d810095007000410400ca24408915440d030101950b2602d550068170100d42e9101c1881a20203040d03080210319603040d9002074100c0e40342e01d020420b800b48241000c0303900346001c4168008105170f40e4200000c500c0880841c084003801510062401340c650440502e8558101c50480009460f1000c000c3da0b600281140032007034505c58082905030502c500d44032203180005012038010084101540c2d05a84804074a100400302071080e03c040040354104034110007000d0103482c084c29555117001400b0b501c20100d4603118012035445a040c400002a036240301d0502034410b42d01841200c0700031021070142d802082c000d100400c911580d40b0304005001d001d4030280c2d449596504405c0c01041038042d030f01640b1a10b084050780c001030f601c4070f035402d05106545 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 714012670 1250 714011420 714011443
    0x7110604030302220335040e101212170c070803070207031721091e03040e010609090b0919090302150106050301170c150706020714011b0c080702090405 67
    0xd03c888000010b01c03031000c0b01d0405030445511000000c6030304400c44044100407084506c07560208100070003c0452030180181c00240041c424910159145034404641814020a4441e25611400300c0141a00101c0c88210b00543c0c1607440f4880c54406035504003402801c1d0080d10428001001030101882801040c01842c4c0c8951462075a6200b28100e19242d0481002c0281040f038081d0211000d540d98150107205000c0300000b040c414542812035504c6405805d081c4c0c600384400e1001042d0011503901d07041c0649119940d0019075441d00c01002c099400c50f42e083d90158400350144030000e503192400001500310030701c0110f050246440c040780313015440e0b140311060081082c0007088407580400154102e8a514000202d400d03616280961203400c0c21203416441259101c0d01d901030080031005c1e03c41940104001805c125550f01da08141030000400c40724165510008130503412503805801d514401a4078001907441003940d5980003d100e0701001a108035449000101040400c004419000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 714013920 1250 714012670 714012727
    0xa0b0d09060905030c0d0518060708040b040905100b09130203090a0b011202040506150307030c050c0a060603020a091503110619020a1e1a06041d070e07110604030302 73
    0x2c400750900fa03031030741c0003504030790118061443d4a41c0110322550561700007a440e00310501d0f507040d8000410106034000d000031695402c0a01c00000e01221110190000f0403495802055900c2c01c0340651203c0003458204104c1000180800c0c10103882b68442c13848000f0400307900507525114007181d2450080c4c0103900600c000400d1001240c410f1003035030308046552092314280501d0b2204806c110034403894080c0584410001d00008086511a4000008641990402c9854100580191404c00c0c41030389040d00d140c1d45400c03040046003004c0e07040c07000403c074405003001082c40340c00b0104c103410918800541400d8012800600d684c1d502c008a540220721f0403030310a8822034205019440b629044010b95220100002c640c982a03103595101101d05c0d44000041500910080b00d40b44011010301039640044e0b90f00a1040c0c074014a000010300842848000e01c0c100c2d1609650081c1c508004202c43d04010020300000c052032800100c4a8010741d0509000d40c4a200b00180741c0c0c01071000d03900050b001b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 714015170 1250 714013920 714013931
    0x9010b040c02010f0f050106050f0901050405151207020712020f041401061e03021903050a06032a050d021c1a010f05040c0e01020705011d030f03040f140a0b0d0906 72
    0x1207501540190f1104030f422106205c1078003083e0b11541218003d106003004600104a40e1500322901c800410341c2171014103000b03040580782c1e00841c0c0c041002140d01e5001c008001507865070350303071004d1030315901060500c000d107440e50030301a030104820070040d80280506070600d5021015502c03500030100591401360300505540e52004001d140403a850000c2401800b10b010424000e0704c00e000701c0d82e40201070b910380d410a480c00d040840084c00002d10045010f69148004000500c009034020068842e100c80812500c04c1210184a401419031055104241491a00006071101c0d401c00c507000c65a034854040714005401d100000010700c000442207480090b001007480f07500b10340c507007050701c0302680c0c00c1000207114001501c0030510100c120b030140c2d0213110704014641c481c058190105a5100c0020301032001c1d1404246000d40d0b09543c0d50321a0000f1405012040341120540002d04411544540300d805940100e800c500407805140e0300480700140e403804a405a070429440540d10100c1000b4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 714016420 1250 714015170 714015191
    0x1031407020604260a051c06060f09061107090917030106020d0806060703200c040504060902100206132d1b0b09090c070f12020114060a150809010b04 66
    0x100e880b800c0303508441c1101080b580c180146611a4481d22803802248058a0301c0720084003a502a00502211940607150844140e81a03289001b40d0307004141d01d8803540c0013031104407400390041d171094110108110641005030420b07080003c01130704540381309100180e41e0b461410510309550160b00c07a813946c81c00020001403505d42c0090031030100001c60b80e0703e88080d1154410001e440c420300501a000070007000c0d60380e562004c036400c65403a002045080741d8103061503e0104003542d40072501a510140e0314500041542411a2186021440c6e840500428645a03158000c90300020b030020b04405208410b1080e224078a54072040003500a00e9508035440c00e514103a241c4000b2102e40e0014818110b030700044a85c8250290f810502004003459005c2d40c4201042c0140c0d0882c1c01c2c2a64a8292402d618010812001005151082d075a00100d02c040d01c0c00c20300044080e000c0d10542c0030703600c41070040045c0300c80991603000d450030510b050360703007522800341c454003500c3c214030b882c0d0340540313007845568 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 714017670 1250 714016420 714016423
    0x70f050a120909020301060c030e03011503031e0201061d04020a03020d120e04020f04181515020c03120703080414030c01020d0f0c050307050a030e07090f0b0d051b0103140702 77
    0x85400c1040c0d651880340c1e0303200c00414084e40801c2c4034200100c0da1141c030540000780100e0346451215006000058422181d1800400c8104160700940208003a15107120300c0023490060312a00203003a00090209a180c00c808045184600350030300750780841c03c0c0c081821581c940c0c0550303000716001880040701940a0421610a201c1440a030b004945c034042d0144140c200342c02500d90544146d030181d030404bc501405000074518524565142968600d101c0c50708640c0021080080c100340d0214076901b0304081400380c544610f04108a1295005c0c8590005050a0804a5144030742c5803400302c0741501d0311314000d249800500303619002404045080040904158041c04196075503c10072f0140301000c01140003100d800448203000900c00700000341c2c202c1e003d0401400010000c1c07500091034509101040d0901c01d40e0780140c190140c072a0300980180180e03005000c4800001c540c0094101d203251b03500c6079075204100140c9030854082200b99960786c004da0100408000068044800d4944490b00a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 714018920 1250 714017670 714017693
    0xb2403060c09040509010614041a1009030218010e040f030509030a050d0e12070e061507030807090b2119020d060e070f02030d0207231501051005040b070f050a 70
    0x703d00940c42c3c13100003070244605001c0d00302100c0341064070303a0b0f0022102040c40090070080089035910303005000c0c54015500d443c0c0d10b008003c04a0303a0303480445400e61040007484e0300c0060b80402c4d02a21000140404440300c090f540c0c1084c0d001c00e40702c2c0105041d1609031941d0250100860745801069510000d01a0104410482040d6a900c030107803403403900b00b0800d01a071042201c0c509640407030010b0001d15406820315421803802030060700d42e400c20760494600c60b401020201e001070002c2c002e221a143d0001c0221002e00094001942084c0310209000040083c1c010846c0b10008007201081403520803050319003403504105015035030784402d40d1402016010b6449107980d40c0d008000058007892081b180e10707000c1600c0740d0156141100c0c459014000e034116040540e480607071044030703081c00d03084491501c0c0c452460b10302a21075666040124684904140d02450107040650700303a64000754045c00701e40c15101e1007814aa280c1e02c0500b4203d10941401034020603074031401d40308006014a03811003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 714020170 1250 714018920 714018937
    0x5190c022106060a030f14150c040303020d0516030e0105090a0803040f060e01080a2301090b0102060106030e1f0603050106060908010b010905010f0e1513140a030b2403060c 76
    0x11200543c481c03006100314903c9511014012000c0b1500c1c100c0080d15000040700502c0d40007084030030002480b981505802c10a9404100c051800603081040503014041e200000240c0d00b045401c1000102800d501410b0307040d0000c04000f4804030702100ca078064801c1c2c807002d04000c1c10340c2d00c2160311402503d43e668010300071440c0c2e110000c0030004002c0d203d0b512840315030381d040c1c0d00c00060f0384400c032101025080200380c3c1040e10f01850006100e416a5500702c0340200250003000c02c5006941002a06001041e0450800c041c100286480c0e21100001c0e00004003120000c420941d040c0691128021710a07500020215400c1c03080010700d480c0d000701c0c0d0b0300a0303030302070070007040300d017210704019203107103205100c0c8a0224603040a41e80c0038500507002440ca110340a01008108907015940c29901d074400ca40982e0f50506550342407040d405400c1e4a2484140d094802d100d0340c03421501c4100030304000400348a5024940d8013070031449039400b40d00a48880c409012904a410503c108240d5900031010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 714021420 1250 714020170 714020173
    0x30b090a020301060519091805011707081c1803080307090603050f040803220c0617040b0109021308030301182306010305060102010204120b1008060705190c0221 71
    0x8910160390600c01c80b8100c3e80192180c0c1c1c500b80701e02a00280c3d80025604039014001aa03000091094000d141c1c0d190004080900003010341c1800061001070b0000d05000c02c9a80c400743d0148440c030070000305181100d804201082803442100c400700d031411104170300002c018090441c000704024003400510b0251720b40d602c0c1c1e19141c6032200c8045045540803902503107100c000001217004107102d04011754201c1d240d40b081060072401c15104000c07000c070850703040303410940c2800c04022180d4000f00800141303003da041803820342420340301c9020004040c000d1440c41940051820300f92004001804020411001070300d480c0d682d19a206242d1100045142c000b0600349042c4048a80358000380100741c4804000c0c1e8a41602d6440044000341380c024003150566600f0480415103d1a074000304200c0d500c501c00c6d4a03a03500d861009075a101a1940c4100303400d500000074071000e640c118081e1100310040689009894004140891b1603180c91200a03400c0000ca06070032618061140340118401702440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 714022670 1250 714021420 714021439
    0x513050d0b1b0304110d02010c02090f090106050d0c03230a08030603211206010e040906020c010c030c021b040f06120c0f0501020a0602090a15080f0114010909200a030b 74
    0xb90101e0180c80121030050000100303400c2c00d070403072419202c3c00c4c45990061401c1e03413402c8103990100d41c01d04c1c8140c0b08502070116100800407600c00c00d000c0c0300c024210545000768440029528035107408624000203104100504a4440808070390311103107840d00c800310494452098031b060003981c550050795024064003800b03064842520304910f41600010070420340a01c1c02104000c14442424060b1215042001c40001d185c081d503101d0081c900708600800005a5440100141e942120509605c1c0307400e00d0b040c00801680160003081a03d407444440382c0d583c401d90040f100140040001d9200d444a0038a810000302e44d1501d01c811620a00d8410030f02c1e2540c50f502c500744803803c0c0c0d181c0d07c281401a40802c40c15800501641c01408100720041c2c840644180c480180b0a100c0210301030460000c0c240b08100814014013500d400c0c0100400710a030b10b01f620a440c0028082c00090041803040c0c1d80750160501c5031100801d404009800303c03404652070b165400c1004001d04101c0008610483c85c80c0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 714023920 1250 714022670 714022711
    0x80c031617070f230f03180909030702010c030509130902010f1409041e050a140a0c02030f0a05070f0c08101b0e0d0605072c0d030513050d0b 62
    0x80c4122004290010411008a41140d80f0398100e1048401483c41d64980c0c42c0880200710300030030410907204448800381d51500002c94413510000040d0001130b08c14030090381030204551004c022503800580a10342104440f010b41030030b403410320a0086e00354002a0011400c01e9034007207a40544600c900c01d0f603c40300c40014540e41106d07038466840900f0f0800c44c08001180081c0352035030203040c0c00c1001601d8402c2000c010040c030411100101c035800d4003143c42d5000b55198000501e00c55030700c49a8600d04018060100c2d800a643c0d00907000e0560041c0b80000e854038072180030304140d074026a402810381040f070715203180c101e0351020a131040741c406100f50101360f603100d02c141c0143d80000030140110841c14440d500201d507460030800c03002c1d406c06142041d0030302007038213401124410181c41c0c030384603250410141c0100100c2422481040e4088401d00040340590b40e01c0c451601440d014901561a2550681d5403183d00006a200c0c0340d100e0440c6100c00200804040300a00c200c22080d04c140032001c0c41d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 714025170 1250 714023920 714023963
    0x1090e04030806190f0306020c12190302090105090d0302010c1b050c0f210607020c0f0108061e0d0302010504050106080c0108160210020a1e1d0d080c0316 68
    0x303440c0107001c106102c00080581c1400c58040780d401010452010000d90b036203640c84102620381c0c20680700380342c0002c0c80180c424000c01241220702542480f90b403074030384203844943c04441c2c022000c0b0201900018103205c00e81c454407d65500c980010a0b5080448080c54081d0007040b1030240e850100782c401012000c9200d0384800035881c140c00070080d0a416003000d04101c2c1b000041d051041d441940c0c0100045c1d00700418501038545900d05000f06690f0501007006441c1c156403100c01031040e06090700600491742c1c0726908a0b00b14006039503203901c040500c1e01c04010000d10034810307604520540800e0082c03550541182e80141d008034005c110242e2151102a111901105802c0c04034032640d02103405a05d41c407940d020303440020701c1602e00054014250005030307400f00e0200d00014081c034843d8100740c81803124951084085042650b270701c401070103402032248440310380103103c0c1c0c540d600e98205000515040b140c040c0820b80541c0d9550300d071001e07500309181c00d520041e40c2c61a58456412018450b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 714026420 1250 714025170 714025199
    0x6120b0f09070302010c050312090601143c060f090a1505030601050705250e160915020a0501092103020301050d2018070f032a09030804030602090109 66
    0x28501e018040305801c503001501c0454806608584602c0f0412203411a0410f00e600c0c0c9001d0345880002d0304144d490110612171003105400081e1040e403039010a0040380c4542c0e02c0d000882c500790682100320f1103400c0c01907050a206420603607044000041d502d001071600d1001400b126104a50500303806489500001d0541d40043c061800301f00d0420108000c0d41c05440648000c510400031a100a21160356288e65a0088070001144080c6180e09000d0a8805482c580d80240f10302288141d4040d103d60091081842e4400d61619880214204094610a100355100d00350840c1c000d000c01d061078509425a0b0460b4a01c45040030102c1503203500b007034424001c03a812910001e050200a1807151030705402190140d04144080a01c148450710585840040340c1d01d010072010802c1592400280c09060640c2c400003200416250940840e101030007080c9282e0f65810540c50245050010b04043c0c83c00c45081d0800780201d14049000003c020940c2c00620300d4072000c0c0e07185030300d584d80d88880c4458031a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 714027670 1250 714026420 714026431
    0x51e16030606090b070206071e0605040215180f011106161701081b0604150201050402031603170a050408060a020706200d0b040b13091106070803010b0d0603020406120b0f 75
    0x4130400811025241c5080500b003018050142d8104003401e05105021804240340c08075241c544070030802c401c1d4600740c44100ca1140860300754034a070031040b1480b00c1c0c3c09030403440c0840c890240c1d0b407100b020342c0c0d204546950615030440c00b101c4e2282008460b9104c507141840400c070000f01075140d800382d801500407106049580403c010010384000340b41c4401305011040b1100d400010a020018040010015060500c54580c00008803070602c1c2c0140750030807810301542051101c14800800010399105042b8000d1010366001c00d84030b031000341d002c540c684101c0e8018080c41c4500c07002d0101240990b8010440325229600c1001846400080c0100320341d0082c107105e0400704280b040440070a07207a00701421f40240103200180b07404010700082c80e82110010043c009903541c040041c200040103031700c0c0340d50f1501150410b00700201c0d039840b03a10b83d1105000e08001d00d000412809001016034000070061039004005025840d102c001c06128200200c9007540d0340c1c1074200100700340c01c0303680324514004c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 714028776 1106 714027670 714027689
    0x60108010f080c0111010b0a0335030a0e0708101410050d120c050d0807080a09050c06131707030201140f0d051e1603060609 55
    0x40141c00440071a81038180602071200001214259440240303442c81c2c0c141e07400c510040c09415103005007504040c00ca000030040021840961002e00b800214112001c4070310b0403030a1400c4408000001301203800c1010910480c0c81c0c0e00300304540a0003030212110142d48080c0c3c1c074500402c00200d81900755940f071000980e403910400301074000b550100c5041141d8203050000382c083c09102e100600c3c106902103002ca1050060300d02c0624a0b8100094030081010a040a80710352001c03100030700015410000940200c00368480e542030320340c00100030800e54a101d01071041541c44000018440380c0e144900280c030031600360500080d1b4020030302805001d46036100140101c1544a4406076454080c006647e018401c2c8054030314100300c429000c11aa02c0b4010400a24107480070380144400c143c100b0000c0c0b4140300360074403905200301d50b03081040c165101310460321b208960207112440c = true := by decide +kernel

theorem cover : BRFrame.Cov 713848920 714028776 := by
  have h0 := BRFrame.cov_init 713848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 713848920 ≤ n) (h2 : n < 714028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
