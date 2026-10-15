-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4472
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:43:23.08566+00:00
-- url     : https://prove2.me/submissions/36c5363a-1867-4be1-9b5f-baaaad55409c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 804136690 ≤ n < 804316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 804137940 1250 804136690 804136733
    0x70f03111e0d0f0b06030f100f0209030f060901050a0501080607030906020f0a0507050d140316020a0b07030e010e0304121e020a080714100c060b120601090c02190804030f 75
    0x280d4204110000c40c0f522509401401c9050043e9075003000c16594841a80400d039850300052035071601c088141c0c01258020302000300140c100034108011a10341400d601c10305074207610840c00d00c000900e003881141c1c2c0020040a0911956042950755940c034035015085200705960f0381080d4050010640c1034400101c45c07200c2036a942c60f502e05004016030410303001501d050151610003d00c103030083d030115440e19a03100d00f82c0d05640e01c0d00794021008241d2100001540034a107007000001300c00300412803080500b034800061200c01583c1071421101034009008941e07000700320a11100131900740085404c3d50152188160038080d0462100c007041c100e200039040700d10300d0800b041144000c42e461042d624035080300103032507002008008000d0a002d04401c00b1a44003074140c0041072590b0042490060b000d05001c4000d6546040346241c040240c1c040c1c0000ca070f1b02c14800c0f10071a4180004c6038681920000000305001588034100c69216620004024070510340113081000440865405611074aa0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 804139190 1250 804137940 804137959
    0x3010603061d0402010f080a0b03070b1c0c09090e0c0a14030615011425110102070602030909012904080106050a0611121b031b070f03111e 61
    0x1406805840c09024440342d460750845115100194000303070a00c6150140e46940f00345620003801e647e68203010701100075954440700d0350100b5480c1007102500912490b0806030365500c030000e44120310f00c500f404121074107051503550340206500610540544045400014100c42106651441c00590244160704001c1c9404c0c0065400700d490303502c03508200c06134142e410f07a075151042280e01c488080388050114403140044900503480d02c000d4401080c1246a0a03098075a00162a003103200f04201205c0c1640980b0740035201e56418425140207083c0c40c001541031100d000b00290660005008404100498440702c01c40d0805011001c05600014003203e070fa00c0e0380f5a01d03818060300d040c1c01228011071481c0c0740040c003076102c0d002c91621046d0400c0030700344018140010441c1e950044041c204005110844100241403c1c0020071615103d8012341903074440d02c0c00b445003064201d40c8905007a600003902040440c682e98801c1c0d403800b004640e00c0c181400380c900e0000d80408a904013640240c03480 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 804140440 1250 804139190 804139199
    0xa0f05010f03050d08091209120a0f020a150c2a0b0c1203040f060c050d02120f010b2a07091d010f0e030a321b01090b04030f11030301 59
    0x1d68405041d02e0003141524071341110424141c1d18060165608105a403140440700f40c0e0880f02c102801410000400503c860803040c441c1c5440c144500e8000d036907401110031940114986407101000402c0e400030b8140030100002c070041d05200d07108502904104a50000da04003a1320300c141031001420b4000203046c5180c44100680850300010280400c078403a0758215441e0307440d8032080c0d0b48566403004045c0301000031955035a0180044c0080740c81400f10600080b0b101030510b0015081c03c9aa0751a502d4203071501e80d81c0809440d00c1a41701d440c54503000c00c00f98a090003600d400c4c0c040a101d151000682400941c0418605000303940300d2801c3e940360070b0400c0c8203ca40304803600c0500110000a01650030a40700480403100c2d44983d1000c180d000b0800c0c209900e02400301c012a0390080f84c00052103020200345910005000c42010b45100c0c030004095425469400c42d1034200c4544074020080d4154603130716801000740103030001e81880425100b560440e03200d001700b00740c01405030741a0707610381d65203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 804141690 1250 804140440 804140459
    0x20160f170d14010b160309080304090b090a110306060c070b031602010c1806141608030402150c030d05060d0f060b0f031c030207030c0b01030b010609080f0d080a0f0501 74
    0x3034107500c0030b4100800c030034181510b42c1000d410703030f000c1510451410100e081d0400c0201d180200072002e0080484000504d04414005000148800100450340e56032110402a21000c001d055829803841d0225520301d80769244162944151b059030318a0742d40c881004a545089050751007030b02d05a00010030021301c4502e25000007000b5000d43c009020300003036800203440c11812040d041141c00251941000030a22030803200c07002541c0c9810291030030420b00030029610b11002e00035201050000144021400c0c81176020b0b0380d1821346411141400120884291203100b000d00c1698026220703030105007a90344042c4004955a8885070390b551230141072401c036014021105500d44145c801e01c1640c0c03100d04001c40d0701d030742d41d042c5141014415072810303000307030b009420000c2c041e410003007072181440011303843d00c0e032a5020314010303440d00c141980f6040c4001d1000703201c1c5e08520707941e40120901040350240014102c04d200308a003800302e01035403042c584a00a042c2e03111104c200030300340400014800038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 804142940 1250 804141690 804141697
    0x18010303090e15090601030b121203220c050603060a0e1f05040c1b050a0b0703020c0709060302030c010c060f021812030304020102074520160f17 64
    0xc00810010503990210f6401200c4201580c06404c480e000d0700080c050b41c4654000440d03450020540e514200301c1840152a080b1907214800300807000000303001148411011000501c0c03040716917006d900e01d41d0b031354030200320003a1f00c982805120080041031640d41ca0013048409055030f61080b402c1b80c60540104a81c4111034800b010718000055030100309401c0c18000c0700f941c2c0242c0d8450801c4007a140354140c14558a202e402e540c0c50181030794240016920b01e5550707000d040a81c1c2c0142e182c01c00100710034140382c2240e0000c040d6910b005020070060f01c0114074030303000c0361090a15030701e103460030708100028004010000c440c03d40300141c44021000540050214041c0c182e41c034905011041d1005680c1e40b00a076400390159024a10402552410316984511909141440480802e240c0c1d4100a00380c68025004072002c60b142134910781405502c94451740011501c114104500d104507000d00303a21a141440e41c005c003c82e14484240700741c0c0141c0e000141c0c0d0001c5c0703440610a070501102180d41 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 804144190 1250 804142940 804142949
    0x1003090317071205010501050a14090d050105240d031d190b0a0305010b16244803090507030f061401080106080309010e12010504050601051311070609021801030309 72
    0x44c904000464036500c5101500c0c2039940d03a403a14000852070980260058001044040d44540400d0333410001501c20b020b203a015503945a910040407090801512032000600107190242c81006250300200394400b050320507107030a1a980c00742c090701d00c401042c0c4100b151640642d16240348440010100c810781c0040c8200c0344255820480d90741c8803501901603200d41d982c0b80010038880f2a0745004241500e450342d00c1c480044402d185422300482c3c10406035403c80d80049040c038070303c00510740c2c40c0d5840040b144501c0031600011251404a182850014212507a48010180c0c2c600303145040102c01c122540156800c01801c007006090f907e4040301a11001c5c0c41d1050394182d01c400010f80403414050740080d030720680701071410b04261800465244c800c09c0c10701a0700502d6020001e088950a104450190340110003800141d810041400703503c00903000381d481c5207441c3c2903411035060a40b001341c4802c982c0c4004045034200301c07400000e40c0300c1c0c45c12015a0809420710000010035030009040b41c00c84 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 804145440 1250 804144190 804144227
    0xb1207080d0e0f060f040e0103050a061d1b0f030f010605150703050f0f04031506031e0209060f01211a0f0303160501020f0d020702040614100309031707 67
    0x1184004402c0780c0c000c604880745038000d0342580c80e50079035241a8000e4182d40d0b20583c5030600f0503644804141108030203910585440c0c1160790300c80107006c032500803211694200800c0038405042ca12000390f030303035503008103481135070300d00c441c1440301c941d15003d603600d980d440201180d114141525070140241520f1241c142b02e1030100c0000340e1096000030a403030006030107840d0542080300a010515080d1b2003085904101d04041001000103880440722030f012400c0d41358006502c070704504e404401410817295207128510f40700607180c01696002042c960209042d103110646140078030041c1c2c2d0888204450307031200e17038030500c1c0c0d00e82c213040b01c2e80a0410744090080460034114200d0a101c000e0300c000c161036801d5002044905040a640721540401d60f01c00d0000615101400080d108190070900301d072401c0c15000584a03041d481c1a004030320180100550020180d035000d0001060345100180c460145030300c40e00d181741454000c075980507620030b0b0310f000c1d031049260540700100480b00c0b0086c00070380d5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 804146690 1250 804145440 804145453
    0x1b0507170706141c060b09010206070302090a2706080a0b0105010f05030604090f1203150e0f01030f0503091e01031407050301050d140d11100b030c130b120708 70
    0x300c0c44005004421151262205031628105212071801603000701ea04804c00c030030581c501c0e88090070500c1031134000d00c0c040c803c0c6500e410300c402c00203040c41c902030501c1d130400d80140500f0000e9550814040308441e1310301042d861f0100d0701c0303000007603c0b080700c4411030341c59140003000030354a0000716090400503c514094606680c9034001543c3c46045407200b100029406c0c4005122410f00d5844103040078000d0000100d082c80584e1410020034a805421002a80344d03074010f501c290341e50034060b0150481000000b4185013401a18064000504c00503050321444540c0f0000d0060900072549010005041196421490300c4044425841c203105140082d2403c0034000c604030843c000d17580102c00390b0360f17558039603440d00c000c010b00442043c1007034030400e00600d440701040b401040301000b0782c0803039100d90703041d940a9030045050140036040805542c3c14100c5407501c0d96808559002c0c808070460b9200c5086103168682c0c40200700b2000030b2a04154082c85500c4040c60010701b20048940d00300407102c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 804147940 1250 804146690 804146729
    0x702010f051c0c05090a090f0b010e030a060b011413051203210615040905010314150c1c02120a2717090d080a032009101b0507 56
    0xc880c810814094540e42c140444090b0142c034a80094100c00c2140c90700504010001c00000c510024591040c41e00c566100c0788040415038a0141c80304664090810008116115007c2038540e481544004d00c050341e101c060b286141c0c040c9010060b8500c409400301d860f441c200404040c4c2c1c0b410723401841e11409954014201419000045890115681c1907000c032241030b01c0e088066006010b03000c01d07030000c603441140d804c0001041c00703000200740b403074804202545582800c9400c0c65000001d408141c020100000051103120010b5402148250901c0e076030303090000048804c8144040303011289400051012700701c3d091110118010039580b0f10410414141d1982c48001281e5056034408001858014201281c501c8030840000b18031100010b00c6d0110000000b64421610401113502c95400b192070b91744558140301e2003401c140c030b11403007c000c04030040030322881e4001c80000d54810501c9029440c400b07807041040c94184045c10080b9003045a040c03a20948904203400b901554141c903041045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 804149190 1250 804147940 804147947
    0xe070b0f1603050d021305100c0302031c090210081806070f1202090d0c0e090622050c0603010f0329040b090c06070f110d0c0b090406030b0c0702010f 66
    0x5142080020314246010030300600400084041001501400000d001c620b984004034001003001007001e0784010002d504180801c4401c41075141e404041203540d541a00020740c00001b1a480585950303040704014140c0c1c107801002c4c00320f61100940200088404491854000380c8060143d0910f0107024200301c00018841d682e000d0132604140080c80c01e070354404089021381c00404c54803000e000094a0951020080346490304994006c80300c5070003955040118804021741650032850a1000d0000e60401e1440e100324412200034050341d41c101d03902e2500811104111211810001a00322901ca42e918540004a50000e10043c2c0704030820038054807035041e20707007005c0581105016984d0710390b4503076440c1c00902c00ca00601054840c40f8801c4080742d50b5481c030b000341608078444c103a10903003241c59140089141c0f071803000180c00381d8901c00c0e50500060407218450251107540781c909e62510300e6400018068896540080e1680401d0010f001c80c002c0c185000304a4113000307880d18040244403d0086 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 804150440 1250 804149190 804149197
    0x2010e0d05090d02012a020108130201021e1005100810020403120e060d06120c09140a0218370b0909132009070e0303030c0a090b0a030e070b 62
    0x14104001001441ca000e0f52030781200b900605d1320100c8584200607000d0498030040c20200c0208070321401d1421580d1011a07680d00ca4940f6a03102c11242035640042d41d40e6400c42408104cc0034030302160411071404001c4140c00300c0d04d500b0240f000c0c5c1800400d84072450084d00405105010344c1001c07050850f41402100c044039400501c4942c00036a030701e030445a615103080100d60105003004001c80360f030030070301442c40644100646407009080c1440c0c11000ca104030b80c803107240e641c00e00040b890300fa10250280c59000310880700250b9554018000684d680300b0342101150312400992201100c0c050032245480c02c00c02d42184900d0404a150303588070701d41606d1269820000f030400403030102c0d08018400582004000c0c49a191540344c554880c0c0002803402031002009080004a1800d890440c403260340161090178000c50040b65003010075142d10009140728000f2500148003c20113100f24015001405000091920394040160040180c100c010b001011f9100e0714101045030341a41085 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 804151690 1250 804150440 804150463
    0x3181a0106090326070f080a0e040b0d17090d110a090e06160e04050c0c070b0906070602220b07050d0f09030b0601030b150405091302091b04090c030c02010e 69
    0xe442901640b84030800702d040907000131221141007031100b0070005076028801e80c161449003a20380d451341d5126100502d201c500829181c884c6051800c0c030581c030b849040c900e0502a41007114542080600071a0500c41c2c0303c3d40b0308558118028000080901060112501854104851008096545144080940f09508400b111030b070050300120b81500308240052540e50300c07509280044084a0000070100c400c11103d4540d203d41c000343c1c10019481c20300c200d001070103032000c2c014100080000454443e0195040082c9102d0340003420303911100c00702104c0310300c3d0741401e0315083c0e00079180e00e21840c043d001000115040e11030349a110304068001d80b90505001c0f0241c1c1c039101c41034656102c403202028060881d90525680e80c40113207080e1114020a134440c1f204034566541c55281c40305000c1c0c40f0300c000701103421105803898910010382d2420442c80d00180003001041c28600c03401000030641c4120340c03102059503c2c1101c18403020b40c05801c59a9810950b40003000014420385407a615003610002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 804152940 1250 804151690 804151703
    0xd0b1e090a03170a060807060816171b0909071806080405030d1e2a020102030c0f092d182a0403060e070801060f0b090409020103181a01060903 63
    0x400300c0c1c0c030300da0320103070700e070b132124400c40041403542e40e44040c541002e415420000c0094010000c0041c50100d0000310703155146d06181154070491408903240340e03031801502000303200400040c6000c5000340384003513905041e001400e26602e42003100f0050000304002d40c14000c4201a80780001e080e9018410726442a6000b4000c0e520300b01009454000070060f07900c44c1c40b0b008001d48059403440400d803007806041045041c00f03044c58086a02c0002e90341e280803041c00116801001040307660061003058810714541d90002580304c02543d4001019001204250224280051500c82c0c10702407146020180780810b4403500000c4401480d0f0021811084030000d00c0703070b1040c8004017101003100502401c40c42c00000384900300340d01c0359109030549072092048000c0d540442e200340641402032144a0060030309214003e000740c034002224009005200006200d150b59112910a40e40284c00851500304c1d12580010608001e180c44003c0d8411040b0b91b4000c21140c800110346203004000c81c0003501d030010b5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 804154190 1250 804152940 804152957
    0xe15010b030f010e0606070f03020a1b210f0519060f0501050d26040f1701090203070315150b03160e0d021c02120303090c011b02010e0d0b1e090a03 65
    0x440c6130690741c0a0401340d0003c500300141d1010450300601b00504620a0340a805181c003282042005583c0d5890011207400d00e0711420030080354809a503030002d42d900380c0020368429040c140b07601d041b00301603030107031a07030051080303038101c094a00e2981c0c1d014034410307102040742002620b14901101c20034080c1580001034005104040341030b1902042801040c11490403c00e501850b2803d51500213030301c419046019400140901e04004409040c0040e416000704060280394000903070348c946600c030151220100c40701541c1c462000d500040302c4801c03c0940e11110f0b590350786800c0c81a03801215080d4440c45c024540941091140035006102d8000429514074400e941d000c00851844d1224220760320300c0d502034200d005071a10303a464040040180084d40e201e151a161031800c004186d02c1b040c1c1040001004030041010155404119540a10304001d0010f04000850204030b05082e018000c8405082040a02c25410340d9508580410404501c11a02c03071600d007540d42e51001600030040390390b00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 804155440 1250 804154190 804154199
    0x509010905060a180e060f060603040f0302030412030e011707081b04121101141606020315040f0c0201060b1e09190905071106100b1c0e15010b030f01 66
    0x3500300a400010080c007011000c0c4c3d40380701895040461140440a05407184044a04e518051040300e41c05040b2605550280c600403002400900c07004000030400c0503102c0e000d00c1818404c000b42c5002d0107640250898044460501500c0310030900007090014a0015100c02038201c0d803507005014034165282e40c038031500c0b540740c51940c8600304120703050110020300c4001001950052181c080900a920b00441410079400040409581c403406003a0361104000454a0b41042c00d103d040958220000607103a0b03d80003146280c101a0400b82544070341840b6800d002240305611200c40034986800800c8025030319080031585025540440c041d01c0c90050381070072010340213002032015031402801095003a00303500d0404806425074000040203680c8000308042c4981150f0f007503c2a4002d07600605031403800d4466440c40c071031907000e50008481c0104a445403a0414202c800c01c0c0240450700f8484d81441a0340641e50340c851400c168000c0c0f0200c000040d006d41080c044030f0080c0c0300c0342158030303440e03090 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 804156690 1250 804155440 804155459
    0xf09090209010201020702030102070605010e130f0201051303050625020f030712171305070603020f03070309080c030a0509040507170a092609010e060a0e0f04140106081906050901 79
    0x7406045066540810194005903000e10041410b01d1266000141030f5042c40f5a03402c464100600026a40c1d03019103090021980e000a14000c4c01e60910302540d807203141141a5841c0e40203035000030701900c500070034041c1c1341020740742da64408104185108001d45051004030f03a900d0354500c082941d03810810a24002c00c03040d2040442030900350410047c019142140d041c000081115807842c1e001102105000300301c02400000006c18140ca025030030308108075140a29440007510040516584007118400c1241201c181d6038000c8002081d242c8038552020042c095511142c1800e00c6030340703850000741540c0d0141005202d11340d95080561040d0380da0700038100003400b80c4803083d2550603c1c001e0600b200050040315904000e04050600d4540c1810313000541445c50082a0500c9440103000e510413055100084d1724620008841c0503000c0c003040c00118009112646070304941040d40400440d1084e003014015001e607048118004180f924050400c0880307030640601c80e407101c1c00000400c070b282c16 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 804157940 1250 804156690 804156697
    0x250c03180f030f080c030307021b041a060d060302060d0603050f0703080a1b02041104060206180c01031a100207080d020a0309050f0418050105240d0303020c031207020c09070f090902 80
    0x3150010324178003521610403524503001104e40f54016404030707415900001c8000d01440c0710082c140d030103220b51030480014200344c0309034511f0303140288400300714551604210381102e401140c000d052259210300724600c0c40080d01c2140419541c81c4070b00e1082242191001818070704032500102d2003420400d00307000441c0d803100350f005040c1241399852100c00140c1d036148142904840381c00c006940d95072800740c029040c610b004002d4110409242ca202036000c1f004581040650424a00054001702e031b040740c80020003042c2c24854102816280d040941c0303030005444810744000408a450710414000126540d404d0b04800500141030180100400d040007442e8000a0f480100b01041d00703038682020031804940c503141903545a440d401405034001000144860214941c0c08044e00888082c02140034203403003100040c01c140d8001a1240e4007201402594000c101f030030150041800c003030000071366840c00300a10b2403007a180000480c001a0042c04e054501c00c41c29154100350070710341040e0a000b0741 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 804159190 1250 804157940 804157943
    0x30901050c150106030f18050c090a110d02040905130c03030c151a04050601020102040e0c030a060f090911011707230f1c050106090e250c03180f030f 66
    0x4584500d0700b04100715505124041d15503a600003c840441800d80400c0d22601c0101920080e46007a000c40841d4000c10a01140302041d078000011b41c450b1400d40e002000c0c04610b00c1120b40000c074a491030810341d90014403c54521480a000719103480050000c6a0340c0d41d40020500c0e040e10a041000a002d1811040c1c0300f4010003410503016142d0f5103082c01d0311314118071009100d01c04414008185014460385030003410a00c001c60410341003500d0741c455100058600c1c0707803002011000602c0b0347c0c03590300500c001d442e000ca40d503050155981301d02c2010f001400d230f048035840c07032586600006511030203a903005049d1a0092001540300c151081d6055141c41c10104248043c05c210070386613241b00c2c002000414008a420355580c141800d022074200c1d0803d4451601a04250040080c40c1d845015801a5514500500042c2e10307a03c0604200d14402c1490182c01041501a003a03090f4012010030002030203500c80170380d03088103542c002200b24520300030014a44120b407001e0001c01ca844001a0885 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 804160440 1250 804159190 804159193
    0x1050901051c210302031e060a0b0d060302031509011113030201111005070c0201080f0c0421021909180203120a1205010e060a0603020406050d0207050c0d0c170f030901050c 76
    0x400d9065854800c00f200c0300302d1030b000b2a0300001480605551600d44018486815180d80360504081d800147e4440d02e500c42c60f94041004150440c200c070036603103c600110790003800c465201c2c044803e540750681d0201c804440315480d0400705286220f40008503150000c10400c2d600001e811a40151891184007032818030611407030201d507000e2800c44c440d107030248000313850707040b8240031381d01c001440c81c90003d024400d5800e03807500b4071458464040aa6003070301c011405100030b45448080b4200500301e803800203076003d2032110341c007111070746490486029111001810301440707031150048030000201c03140081d01a845160184408501440a003555040c00d150104010010b40e8040040d1075080c4c208001c0c2005540038042c0a00e072040e0004020001810194105490520007402600505405a41c44c6800281c074004000341031080480b1020010182d80da40d44041c00c05114101c000e01460b400c40300281c000754407400000400007554141d40300110300c1d103c131407001141d0316042600c2002e035a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 804161690 1250 804160440 804160463
    0x30712031e06050301180b1b0d02040b03010504050901140c03062e180608060636030f03040b1c1409010b1e010206041b12030302070b01050901051c 65
    0x104441038900340d804400780074000c11900d0420b01018211141c15241030603079100c800c03011002501601c40b0540c000300c00c1d81840c8810100d10100101e40c403c140e03041801600c00200895202c05141c0036605807281030302c04014a58032180007500b00e070301d80000303162040100c1001410603001c1d0030045034000c0020304846c503058181d4007290242003440072071403444e00350302c2d8100b054a580507845d0a070041d1420301c80b5082618040c0c01504500019000c10301030003001800ca082c0080149429494410000b00c02e805e24402c0c0041da41c45090000070b9038800d02603120b1030a5448400001c2d40c003542c3d15003540d14609100e00030f8190807001c00407465164551100c02c003408254014800030b01c5030980900105034100c0100401001c2c4400c07425094001e00210006480e50340d0010b020f0390311540c8042d101c100c607500c43e40b582c000c04001d64088000231070454a42d43c1019031640180242c14402ca0010f00c20741d0322a03081101180003400f43c2e9800100f001040c14080b0702000088200038002c1407446034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 804162940 1250 804161690 804161711
    0x7050d2408060118060e0a020d1508010917040b0d09020d050105070210060e0f07051c0c02030c0601080706050715060e13230d0c02040e0715090b040803071203 70
    0x5090344154001c081e1a04000700400038030b008011010b010701c052903401c0181ca82480214600050050201d45003a80e011450904180c5941d00c071a8819040c4a080c2d085155103170344250217860038240440e1105510103102c1d840058540950f4180c0301900c148909010301004000d004120502081e40c0c018010409000030507003e1240300e001e001254013a010038003030b0300107410035174010390b0109643c01007030001c01862021035070a05809c0401e900d00a03590310605195002405044d29010031440e1034140e007a03404a800000070300048400c030058918682c0d80d400d2845e2103400503c10840424801c110000001d85102085601c0103080440080c01c0c076140c0c4041c41211004940c041120019030b0003d0081c024a0b4500824501c0a0118609092000d03028a61a290450344900c01d0280c00041c000031540c8941103101c54004820850b030005503240301d00500c0e81c942c5450303800841c01d1a0004242044050304450030b4078240c5005501d42115680c60203001c110b11315154080540e038842004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 804164190 1250 804162940 804163001
    0xb0d0b041407060c0c051c0c06120b0105041a0903030c0d0f031d0c12010e0102072001090602030324130c02121e0a03020c031b07060807050d 62
    0x40c0654000c000c0c03807804210700d01110b40303868841d4010509010030308035540d000545410412003980d00c1500c80c0045291038000d98901c01003107403c02420b20f44205000700301507502042c803222070703009114217101010482c1c0c0155070034400c50160201c1c03507019840c0800f640e1b0294004080030031000d03048034a080709225946060055200f088000140c0d612007428000703615000340b800c00f44080001d10305415198001542d541003440780a40600807516081402850a44c46983c01c280007200940d0759036043c6c034101e000720b000c220b81008c0f540308817410240154801c10707aa205441003500110b155494103035240d001130101c080090000c220050f900b40303079a21010030798034410100b0300300031540d0100d0941c068100040c1d0110012800424011071144140495416518144202d0780a079110030251701100070788a0345100d000c0c03a120000e40c500c81e0340e10b4075002c0c0040003c01d03001d5030f240340e48a144c102c410040076100e110004809000b040d20940e01580800100240101d0b294840e004060201 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 804165440 1250 804164190 804164213
    0x12010302152104020112050114041a04090503040e160c08030924060a1a1803120406110609070608071107031b0e06030c0a030f051006033207090b0d 65
    0x40064a07880c506120131940c101c0050000c1607400c00302400158145194078081010542c4510b20864407544002c4035030107016040348038a2409002808400a070f81401542e9038450301c42c14001889500020710107900030115081005902e50350081c040e4513a8943c207020f50805000ca40391401481941c03c1210881120744507003449003081c040300c910b080d400b0007101c60750702c0d8022190b54031590b0b101003801d00d444040b61005502502040344606540001c2843c2ca03a8089031104004070008011451030340100c0c034001100a030204a030072a503190018a07450b0401480b03503901060184010960050090061003a0100c0711801c88028a036a030711502c60041500318800c03500b81e506001445000c140e4140c050348050143c006001101e0303443d000c5030522045101c00f1b010711000c031080303a0411005100884207211030301d0041c48403e0720f03402c084209a032490f2050a2021f000c003000031340d07504c02205206827040640c014140142c80c0040d1500070388007208142d60710000c4011500009000c20841 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 804166690 1250 804165440 804165487
    0xf0a1410050f0f090714070605090604020a06050a0504031509050d050c07050406050907032a020304050406061b0204180b0406020405040b06280903051506010f051201030215 76
    0x40006036260009110b00044800d80043c02040b401d010a40b6030303103c4034003681d080090341c540840308881c03615100055000d080002001c3c0ea04100511150400c0003540380d0280340200c1e6030604c515035904003034403640b007071400800100b04144030030408210440b0214100210410300402d400c00d05a5480381015a01d054031408188081090360070721f102001480d024000a50381003040601303040c0003ca0384032009040c0c808254694120141c40e400c1b460800810702c3c560401c1c408840c40807e0069100c1d000b50203507030300481c501100040c0b1903101e104844108400c0c5800703048088000d4080c0006401031a03906627548030317081e034500002a4642d007a1403084c0d004290040c2c41b5030070442044152094189118410207040c0030f000c43c19060b000000006024040c0f0080c0a0103800ea82911104c000f0750000c0c11a000c0c05030000d144940440c003481c800e0130244ea551011000350b0100395428010a04040c0651062800500050800c4000c054803e101040d50030b04200713442070b440040418a03400c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 804167940 1250 804166690 804166711
    0x30c0d09030c0b0105100203040e0a06153902010f1b03121d06070302070201090506030103050f0609161701111605010c020a1109040201140408010b0a1202090f0a14 72
    0x152003c1c0a401c002d49409040f00f100e00e507103029030405000390303139005500480784c0c2d0700e014902042c841102d640c084030080991904044502ca90803a001d400c0d001e141d88540816584402911814002000f0700c2c140d40407804108944480c55800440701002d02018490500a101d895501038820a0500e1000c061182c3e440c4241c018103540b02105880402003201421841140141c800403008030340703e40e0080061030b006032203d0a60004881407400c50780602d8100c140000040240b0002041e840302c2450910f08403030300d03500d2354416140d0701c20fa0b640d814079000c604081c0a100c145140201c140100d03544c40c1c00400c42c80121100c0348031581c0250352a002040805c82980100842809400c1ba0100320b400601072400898032001c1e004c02d00035203058460024580000d0440e1b004841054001602501c0390742c45548540c5800d000300b185c454481c0c4100c1a0103000241c9a6000c5212402540d0141c0134109540f100c400c84a8150000b501105441c2c1e21000d06002e4501c8040100380329403580310 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 804169190 1250 804167940 804167957
    0x17070903080c0703061407020a02090a0204090507080618090c1002070902041712040302011b031e0201020a02070b0720011211042606040818090f0103020f09010317030c0d0903 77
    0xd0901c0894581000f59101014485d00f0004c0d09238012075161040c40e0103841d90f10707142e900d030756520000340304513001030b00c405140006003c13000d5440840300344140703802e0350201e014000304091000c12a10032501400203910049504105003060b4040c070708040c159004841c6c00c144c0710b03c13510023641c00640246d0301c00c01e0100ca082c0c018081c20002c5050f114a254440c514250843d00000d00340c01810758508290f50300407000c40201031081480000d12103842c440841c074006c100800074040e40c001c445150042c4503035103010070b0401d480d0048445283c0d0110014071044c80c2c1c84c0300060608181c24100d8140301590f16441c440c03440301c0c02001b840d40409541140c0d2141080b00b540703160141c00c50070703001d9451030021401e01c0000024410381c10607008140c07a03880d010b01078150303950f010642c4900c0b601706507941e09002903000900480b6058a108440c1d418481e0f41200c1402110f840c00d110240104131035503030308500148910020740e000203940f204189400d680740e41c0c2c00d0503a98500c01c1140018a1070307 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 804170440 1250 804169190 804169193
    0xb13090513060c05190c030e180103020310060b1611030f010c03050106080712110d0f1514010c120e10021005010503010605130b0d020406080a050c030c0117070903080c0703 76
    0x41c803405031007496a05000303003442d17a03644102050321088140d4005215400d16480140350040b441c141000c03000420f403040040c40f00c4080302c450042803000b28000c1c45040031345900000d403401108207680896407603d0419030841c250560300c48080000f50b9500a00031100b030000c2e10300340090b1000300d04180010903030840400b0b0090880780164400130400c40700d2400d01c00340c0350703100c0030a650f6682040000310344401e60345420300646c86800c294054035403070040d070b00300ba0003050307040601401c01001c10704140700d81e60300b01d05002d41c0c0c45904050000c0c070150400000102e10500d0200c200b5050715100c0820004a404184500300ca4010306002d84c0c0001c7e018000501c0b07a0041902501c0d00790024403020f8640ba02061044a008254050507511101000c41e01d4444008600d41e4640003402841003a584601b130707640301d09801d02c05865600a0150b00c810a040c0000ca00c3d503034138410785d2001070035401c8943c0180307500d4002c3d140508100c1034460010104002e1000307400e050503640b02519445186 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 804171690 1250 804170440 804170453
    0x7061a0102010f1e1130150a090213050a091d0106050d0b0907030f0317060f032d030a03020712170114120604060c02071d0718080102040905040605090a020a0b13090513 74
    0x70a44080c7c0382c1360070050342854803525650340403102c078400c0c0940c98480b00c403e940040c8002d50007147c3c001c06511400504c00d0600d070005601ca0102908103c0f0111544102600341c503954052a600060203035a0000025070106200358480000b0050340c1c01580c90395a80450280c81100c00e81c001022400c801184079410049942c1081c01200c001d8401d0f20004046074550244407407031407070724008200054005000041040f140380355003007660342e15926140050002c0d0040c0304203541e508841c0c8040202c083c0910f1058902c25a11403412103103a203080c040a2410010980c91a04290030210002e0056001c0001c540503900c41d0402240040f007107003009180c26003a5000203d091156041c00b075034034503401c044d20b8020280d494842202c004444407080d40c2d41059010910b00e61002600041c10340c110740c071150141c1d03c940c05c248400d40350200764a0341d4809800c0069400156440104001e072015030090209101c90070308144180d45d41c42183c801caa40803250301c14244070814402041000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 804172940 1250 804171690 804171787
    0x4080a0c0e010e131e0b18010e0604050c040515091305060c09013203070f2606010e13020a09031a070804030e010507061a0102010f1e11 60
    0x3000f000e41c8518940b40c1c501c107504141100380505014220030b0400d280c50080e25071115250781116103081503050401280c020705400d803843ca401c41d460300d03403807490601d000b254140c0a10b40050041281d541444c0411009280c09094403000568541d140000c03616001100c51241900391700e0700e800c1c4002420b000703040c00801848001c07030b10805c110840c0142e8001e50885e840705590100c043d504907550f051500000d012202d49102c0c02c03004803c10400c06d074000c41d2520a000f150b0b5802240031854034081e0511141d200c0030740781c0800c200001569551141c2082035815400502c2880c8640910ba4840101c2c3c0c0005041800907280714414020b0240d0000580c1104660004465403841e11000c000c00000000d04001c040200001c2c06034080da10500a5a11f02d9410840070411007980b03880c0c1865106040346c00c14059400c004681c001500c01d8030408200742c1050352041040300c80100180c004000442400a00440c1400840e00c18001c0300310b21a14400000c0401001304580d00090741c0108 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 804174190 1250 804172940 804172949
    0x60106030c0c080304020d02210f03071a09011b02070e13020d0f030512101404090b0a020912010c032309031602061605030405011202030c03041704080a0c0e01 70
    0x608040040c50000d5200b00699503654000e5191a16030302c0c0e44c400a014180d021030060f50103595030700920780c100c120f1400f1ba8840d44441d0200c4070f12406429000f912402510400f501d803409500048031036001c0e14088039400703000200002009000502d5640000c04e4145043c80140c0c0015418014580360032002c94000d0350134071400c1100c0034681c0c0099540c04040700000c0002d04507410080c00c060007031056a4110005100d080094940b5440a0035040305600c81c200c04100fa200d0303440d40c03e00b064800c22101c182c1000384080550759031480007010398441100c040e0051260144955001004c2c4160340d01022940da0201d903015002088907030f081803264182d00c0c81c400500070301a00c2e62001048940703c6244411550102c032882c00068070b6801010904c401480d22045203504019000c002002078031004d80302c1d0860194010340307040032800101c40780c520421082000c54007192840040342c5400702014059460182c5415a0b242418510441107030f03c074810344014418814090ac01b00c0c05032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 804175440 1250 804174190 804174197
    0x31015060503101a070b0f071409030a11030c0628050c03250f030f111b0d230318010c02060d11131805090706080c13051011060106 58
    0x103042068484000390124032640156007009a07481c5860301c800801c2e94174094005c0c410090500d00250756a10990045601c4000a501845e0404000e003280301561001007000d4014031441055580701000f0820462505515104880c1c02c80c02c2c0340d071358400a005400c1c0c0e0040008607040305007442ca4420301650507000c180041489074081030351000054407100c00c0c940d444181c608908140340c030390424548101a01c2348612102d1942856004a107102c400112a0759000c10201e80e020794a44402c0040e0302c000b641d13105042c9591551400c03450845029018a8104458001c10700b500340414268810585850b0404030350080e10317043c81d07903d13060050400c4c00d04107080941940083c1141c0310348103040800c2540c45026805604a00003a1a41d04880750f4400e5015600c1d50860384000138480754401e2090304110000d51005004a04442180c800351520b60b1540c41d456114241504207039009409100c40c4800014240d47c0c403071807805115203e441c0e4000c034107501c2d541c60b400c6c0070050300b044051 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 804176690 1250 804175440 804175447
    0xf01051204060f0209060a0201021201061b03030905030c06090703031e050d090302010f0507090311041112180616030c09050f0d110307030c050a09090b0a18020310150605 75
    0x40d820519030081e40a50301040c0060f55032190074101c4004d025080400e6003108022843ca03031140e40550007020b0414610f48010501e03a80d41104860300d0b00000c8101703181c80007000322880000d01035000458114421030540b0700b800072080e2042d02d8035500300c80e504541c0d8007500707080080c0341e0040040070314844882a00c0500030781043e4081c0c0544605000c60b80001c0e0341e0441602454802c3d031004d031b007002038020705001e20704201d880180300c840940001d540451000041c2002e52509214644101900a050b9030402480c1c0365a000003041c010702c0801d40d421070110071140365000b07004051184140c54031407800030911082c000c0445182195980901811040a001f60b940f480720032400e8071030803200d0628456940c600103a000340c01d047d8440e09841400300c003100f00000c014401040c0c1d0800d0300c02c080450340e242c48403803d681c00e1040140c01c1030010070110300168401c2c1c0003800c2c0c845150305001c96084850f030100c0e190802c4091040d0f5055941e140200c0c0d840c594aa0303080082070760b031170120b04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 804177940 1250 804176690 804176707
    0x20a110105060625050706050306010e0102030408070312050c0a0c09240b0309010f050c1b060c031308091c0b07090f0b21010612111c0f0b10030b0f0105 67
    0x9845511140d40950601101144515556111350711605620005403080c143c0d5411005e0319a402c2954001d01007609158500615440002694100c0350302000901c56140341d5190385180d00302104445c801c2006c1040554048101004607201c0640300303c1c81006088c0c40d0071003917801c4661042c0b000c2000081c02102c044860285003a82056a48601e10156a03071a503014041c0100100e6454001c803030304010400c01c02c2031304031020b00040c44040342c0e42480c40d644400e03080d407a8241225402e034046000c0c401700f90b0204d0800240190785200d80c4080c0d2410380f00da000035003c803502d40b110b50b106603d0038100204110500030701310b0308544541050901a03040010350700d0400024042c40e003210a0202e2450104009040361a07000109408490081d503103ca900502454841080320146814215000c040004100460f1072204400404050340c24141414801901d110301c04060816100c103810341e102d50310208080120400394500241200c01581030180580d40001c07940c0c14004284400341 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 804179190 1250 804177940 804177949
    0x30b0d0b0a0b0102100f0b13050c1602060706050109050415021c050a0603061803091e0603021308011a1201090210080a06030f0629010f030207050a02060d020a11010506 74
    0x507044610a0303008501d000310038004034039040c585c06201c810303203050400304070501c03c0690000710b003580152000e110711402d98110105554040e0b03004130144200300000341104106c0c407901805684000c114904e071030b0b61a140c101c141c50302a08040343c00c541c0c07541804200612880c81415001c516038080d0305100d01d50741d440c0100c1046038841c690860f00c03040068500c3e0420342c0000050742d0321060030841141e03044030313400d0048070f03803e42140030a107000300c046190049400d030350b03450810355001c19504506247e07048005e0f4000f58504080c5820380c2501040f411000e01941030b0072181201485240c881b00d00800141030201003203451903914091107500941c03904036005040200702c0c20700440e10789030314016400810066002070080c8505480100c100030540e0400c61940c94031028800100404842110011508400b42030204502c940382000982c00b0760080d044076030061041c0c8a01c21500e4000c40c80c2a03100c250100280343d400201d16129a41145642d019120908006c04c42c070714100c000704 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 804180440 1250 804179190 804179213
    0xd020d080105150c0d030615020c030c01050a021c021014090d080c0c070608040c140306190b030a0809010201060e010f031709030a0605100510092306130303030b0d 72
    0x20f4051844000b0380c80c00c0503040821522110241011145140c00404004000b441140101d0000c1021328103a2a038070342c400103150700f04d48002800b410040d221140152515442144d0f140250b00509443c07a08580cae4004010441c07030f01503001f07003180840b0301084404850520080d094845441c07414020001000a42400800002d08009640c0d48855009540c0fa01803510130f040113210345a404100181c3c02800c0c907004a01c10740d17003007a01342c0e2120504018004088001609540100000381001900342c0010700c04480308240011103903820b402090400b94000300031307501c41000280401d080d5909200700001050080300707201455042503080c80607600c003440081c0c01602c4075007450940203101d5080340ca003d00000e080307a102c102686008405440d041b101100512440c501c00207045c1008100070500e50003d54804401906045024400441200c1c2c1d1510b203408a040c0f0780910307280c010050840307480310704a100c4c2c69465032400134150b40e03245e081580142210088100000c0c00800b18 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 804181690 1250 804180440 804180449
    0x190e07050904051606020102091302120609040318120b09120706020a03020918041104060b09062a060405160308090913060612170c0a140715110d020d0801 68
    0x103003103050b212420103d1a01ca031503000d000c0d01c0c0710001c20010fa00e5130154014640d0000a88603140c17482100c10621049009440325000455952800144640360101545d80e00078420b09100c050351461604002941c2d0042c0c000d959810640703c1c014040c000a032461650002c2c450009041c0d510b0742c1c01c540d1855000f000381c01400581c0100c1da008145000b501920100d000291400f80c440a640c42901e10b02841a141641c00da104000008030509003400740c0805d450b1401c5500340b414049506224055101e045105410340c2e401c1d0745034004114185179484000c22440040041d414681402d5052400f80d044402d0090800502000022020350a13620005411100c41c43e55035580810140d007290324100040040c0c5c41d0035400b0820b417402030002d10146009090015103400703031480d03046580c0708159030b080660740850108400204110345404403001c2e4902550511a903412161591500d034035010400700b0340c000c0c4412f0450b0740401014841c0009072005000440200700081c2084906005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 804182940 1250 804181690 804181699
    0x150f101a0c0102030c03071b021011010623010210061d070e10050c0d080f0f060a03060203070801060f0512040813120f02030606010815100323190e0705 67
    0x921034249103034405841900418000944d40e80ca4646038465503940304849040108003544100303002e0303007070252005400703d5001c3d0062034064260035080d2245400da0341c0c89002036480b20700219131001183d00c425000c5440d2244806034103140d000186c00c041258500c098030500c1c0060800c078844001d40301101c450031004044556440d082000c0303800c03204059030185c0189840302502000e6520030010158407110100351883d201039004101d503035030b6055400c00096101000400c415003a8040091780014000f4107140400c0e41d2a91403c084c1c1c0c00c00c40c0e5490104503141d0042120a802c070002c840690398500e04240f40c1000c2c0305c81c5000a0501900250440c000461030303644189011300c140d000b8002000e030408624240d403501c880a510003c0040340203009040115105500a0722254000d82c40d941400810800d241d0600c0901c9a22070400010580c503a04401c040e01d18503282d251410f007800400c2c5216181c51504040f16040c031010101c0610301e0310518000c1650003003480703c2a11801c48 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 804184190 1250 804182940 804182969
    0x21060106050a2a0b0a0e06010302100201020c061008121215120703080417031e0f0f040e0406050105150717090a0b12010801060302060702130e060702150f10 69
    0x6400c5490360300384542000751405a00f5112800b204207400c6480071845030740c1103c850b54079200c40300182c41c03001c051283c290b0312001c018401490f0454140680101c140f00040c1068000c400a83c41e0240030f881d0300000381c1c1c1c04041801403c5090101e50307840c089c2d50784120b2802a14070441000e03407000602c8180108498241c442090f0380e107035846080c050040c0c04403000d40c1e4590511030155072041c03080240d038451410041110f50303004426259182011001c40642c0c40c00800c003c40d0540c04228844a0303d6020040f091040c10080090b1001d089942100b1200d4a0300d07107403010844006230451882640c50804030b890660020302144c0000b0f500c102e0040d0f482c0720702844004c040c02644c0301554400a4000301282c24900400035003c102500c000108860740e0b2281420308035003131404041c0d00704000f000081c003d418492442501c00f02c000c41c00007031102e0500f5a0a041140654508006030481d00e104e0440002a600064009110204001481c2070190b4020750b03c800d184600c00000c4a0344 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 804185440 1250 804184190 804184207
    0x603061d06150309101a030a12020102040e07031b08040b181c080402091003260706060314010c090806070804081b160b0a0815040209030304030c03022106010605 71
    0x12107001c8030030100c0b0750b407254a9080101c12961600c2000440440380c03498290511040014401c8060200002030040d0903100000d4440c0140c18128134005d00656408000004891a859800e03d02c80c400c50340d00010090040468201218160000b1000b0407010b28140400b0564800100e6000108041c083c6480020120390b107043ca003085007140e1800248000310355049421424140c8550b208030307002d03102d40c1e03290000700b2104600d80c00060080300d0300c00882904564140b01d00780300030881e07000090820f503043c1d0701c49058400581044803952103284c511260114240108015a80340d420403464680c02c1614260f07803501c005105c9000c1011800100d810311440f14100e410395403c0c0e8022102c00c031000310010ba600d0446c045090241180c4035000039400f9260001e5a12290141c3da07260840c2d222281c407902c80d41104040e80f0750007582005091070540c1c0c2000200000e6200b8002d02c600d682c0b46004105110510000c103001080c80206a900d44100c0801c400703041d109981802903c66140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 804186690 1250 804185440 804185449
    0x20d120609060f050316030302120304140f1e010b13090825030e0904030c110f0409141204080312040f0c06020a0b0901061d1b0a050a02070603061d06 66
    0x1a68800c85071940b8241c1d01155450b8100c0900d03042c0c982c2039080382c0844441002e0a042c98040d07101c080e00503040000050300c000001402150814024101d6000b20f008541502e17091007060060301d5820f9000ac490740c000510f442a22800000c83c0302c00802c00380d0320040c00305900000f05101f80e80200e88d43c500300420808540d096030840d40e400c0c0010420307005d080ca03451030003800364901035020410340301d00140c0c81c0c41c1503503045114580c5039842210010b22580c0d076107039041710b145035030740e02a0b001d000b1100b40342ca81d4410419024000c0b9640b4808240448003142002c1c940c0c0032810741c100c2c08010a0011101c0041245e50312000b4821201c00303a9100d0824207500050392400030072121880c0380006103c0d60029144e1510740c01140860842d84400800c0d90803500300307100b02e08200500847d000024211850f0303540c1d000250340050005114100c48140007580302051200209034049911131200d41d04104441c00b130300340c0d41400c10200d0300386443d4110444401c04400002c0101c6030010702a07855 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 804187940 1250 804186690 804186701
    0x24090610031e0e030409050a02070f0210090314011a030c220e0a08040510090e01092003090a15021e090609030f1e0604110402031305060c0a0807050307020d12 70
    0x4503500c04201c43c5148412640c0c0741d60040c4582d9600034201008241c0c550910301c01c9481c0310743e002070f0740312100c0352a9003400507180d0f28641500900000580010205803448003520303074201d545000140e0000305102079003981d04c103407200078040e40c819052090300c2c0c2c136081001e0220340d80036400c000003810002040800f428000040c541e2601036207091400f00503040020b80b0903188101c80310340003a44407010848201d252440b80105684800c1d0040100c1485548540d214401800e10100f2005028024036000d60050341c1034603090b44034404200500c0728055504c601007803800e0f4103510349400304440507503181c02840c000c00300d082c0005d405441541e50780110740c9004006416a0702607501440000e032036860030348014005c030381707034a0459115001c0030840307600c01c95000d40300300807860304002440001e420007030555004410040000c408070b5010402d8a00c03550000c0b0410b5a00c50301c035103000700208001f5012405102e02401400646034021500b000c1640b820b2410700082c1100c00c034003034042d04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 804189190 1250 804187940 804187991
    0x2183c0a0b0d0c08010203010e07020607140c0a0209040807060c1805040c050c16060f0f14130317030702150601020a0f06061a03180d0f0516020402032409061003 71
    0xa03c2c15001506035819005981220566000580e03240d0310010141c0c1c0b104411034031000050b500012884940360640c000d0314500402c13204440c1849180d0b0301080c00044141c500741e91103000480d104003000054040c1d442c8214140c604690012144500211440841e00500d44266110941d5540552141d0140d81e0070500d668100c2da030300d205104d40d0200b521002c2c01003000107451041602410b500540c04400340e000d140c3d99003000446000f070540b20703940002d50106048071440e036000001c02d0101030560040e890240030903680b8201440702078580040002c0e428519039080b010807615a8022941d5000c65030040b000c602e5071000c030300c1c04400804841c0c000c03640b0000c11041481c02d00240e68040c1d80f0440e81300056591a0316000002c507078440ca0070b2590400030740c1e94040401c0e600e10440207800710580d1030500e2003821300d460740041c00f42e8004a0b200007030080c0c680c083d03002201c812800b44912070002c5c2d80c06130660804d40701044039900b4195074401455268032680440058142401140c2c9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 804190440 1250 804189190 804189203
    0x30c03060d0204110a0e0a0515130f0b031005010c020a0302091f260726030706060909061401060e06070f14030307021b0a1202183c0a0b0d 61
    0x2100304d505400305410030809a000280517244245031410f0203400001500d000800844040640c0030020120781d01c041070128510340c0c45800001c0800e03021065902820300982000d4030391810001a0300070103440e03401941082046020324003d6102c40c84900156038060722070103410f03510b88800b5040200001605d024902c3c10301d81c005009525185d039040780900091150f055452500121070707613101340307001e2465602d083c03101400410001c01b9010703441d044c400094900700000794603440100c40307155004849058451500c0c000300849403141e4040402c44a640d1111941440c400424034203030007103054040e1500103032040034494103000c220002640400f0401d8110341082c07650303840386c0060300e541d4054864845076051140320002c4500164402030107181019281c00804460b030400760006a802800a01136030b0181260440d4039031240c1858000c00121040480c01030114408401c0000440100c200c1d1541c1030b540700d0014981c120781c0f0002c0220315200301000040c000c0ca0076800c02003c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 804191690 1250 804190440 804190451
    0x2304170102091525050c040e01020712030507090305010207080901111911010c1b06030516020a02010c0606090516020d020c06030112140f0a0501060603050601080a0e120d0b10020a0305030c03060d0204 88
    0x40040011b460202500181c0f0140812002c2900840c280e0040000061106d207040f10500c4810341f00340e028560082c100d10f054000d203956500d415007268007002e03055403e000d000860041e04d50304100b01141c00f881003001400c100c003000450b030703221000c402d20041c94410384044112241e84103034038058110b40c00c070310907000c519540440300b01d0122661046034042818078002800100d000b52100007a40229005402c05410710780c01192107510400003100c0403566a48041403015003445014460900e01c811a011150140380184c9040442c00004007103600c0700300320250984034441500d046804108010a00c003019250001d00c482081b01d403003040384903540d29a02c65a07030018042c4e0146000d071001300255038842c1e00403401d842d401c0700c070940070640b25000304e220407085602c5080303c80441015100e009071041d04003ea550302c94803541c0780440d10380541c248a403600011000080280d4001054402c101c0d0364090001e00004110f405401d8010000030070f0b9072140b003241320f002030740180100003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 804192940 1250 804191690 804191693
    0x90e060105040602060f0907091a041a2b0602181305091b0301020d020a08040b06090402010507201002030a02070806010609210204140901050a0501030b162304170102091525 76
    0x560322b0030001080c2c4540d04184500b100d52115a59003d4108809401d00000ca802000044c4690261160401408881c802d0810204041d44090032070142d060840382407645059080095101018907913500f003030f10304014041e85400018801030300400c9610854504549071000a00a018881c0e00a48445c0001040d41a955100d0056840f03588900040605031312010140002020b0445000f80031a00c10401c00307010506000f180906000040010601c030350201c804906035009481c0c694000da40042144101d0540511521001c0d011b190000c22036985030280051040b17038144605003c0ba400400011000500c056640000580103401806205a4202c03000b004440454070a02076502e00070110f81f03131075114000c0e1130480f6000501400c01e6140d020078000850300c02910b01c002d110001d1001050300c1f1741d0407010100300740a45030482e00c1d07500c0c0c82c050203c410200c02032284540d204020f84dd5107681e5403c255200e082e00c203200b907a10303100003070102044440c0754124200081c00c17002e03e000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 804194190 1250 804192940 804192971
    0x2b080d050601080108120306090c0903010c0905120604051519020301120201091d061e1309020306010e040b1902091e0a081906020a020a0210090e060105040602060f090709 75
    0x900a50080c3d8580f8160b07039a65043d00d444070f02e51013000f001d40c0800c00100f01145403844e401038020003100c0c0d4551404d5132040c00207003114500003065000c00c0003038408200a2516480c2103400301c08040160000b03180603a03886461740380903802c041000303181402189600c114000501030b0400c904400319aa540c48400449540e10011812400200c0342000400c1030403814501c11025542691880100e032901000c10501d61081c003c55503d2148070302004461ba564100500c3c0300f007080c02c2e40050418080d0050504204058012000080c480b40501002482e0021003645c42810030400041c030382e840b100200c01070300c50000d18591006d0034182c1d405411001e03064101100004950404215075243c800030348414003c016101d110545100c000c000c60f400742c001789042c031014410395a8440341507001502a11144d041c080001d4040d080034071402920702c03981074200c802400c0560409282c000000e5a0781e000070310b50070030718003064040b4005007402c00484015001c00c0708244203040078400d285 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 804195440 1250 804194190 804194201
    0x160060315050406082a1507060f0b1309021c0b1009110a1b080f03010315050103020904030c0c1a1c0902030309010516020a090e0c010e2b080d 63
    0x203240407080c01d000191031030580f03e103104a54010300586402c02041c02c102800d42240d4000c00c00d080d5540e8072490250360b45580c1551035013240c0020b03035110485070078000101d52004a40c0484640b41001c0c4001d165034901c0c611618404004000c5800c0e821840441d503160080202c0c0840c1e4462920078100300100040303060301c16002c10b045c0404103a5521010000d480703200c046030040c0507003040070300103151140c0c90480f1102c20703000c0d09804080843c0e0340c00d015540141008030901001200501c208443c001c070340024210718410902165042d60002112001c000d0310003030030700c103401180030300301701a44012400400c18a00101c0307a240c440c242d802c100c0c1d403000081c1020054414008203203000c4910591100503005401541400e07060401524241e00060298980107240301d41b05c001a500c0543e21300141148040114071050418103592800d0010440c0030b05202e07207105c41503190381706d4621115109220080c5020541031019800b0811f9404020252900c4000150364000b0703686034200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 804196690 1250 804195440 804195461
    0x90304080c1005070b1806072a0501060f1203091a0306040203180105010e06180f010e10090203040302010b090f06010c060f092010020601120b060103060b07030201600603 75
    0x41d00c0c03080d88d401004036103424035006c540c04a4400b00700815040301241138a90810b030702c50000000d1031500d4081185203003800343d102e1511070306540e81c1142011f0b48055440c0052850034030820000b44607848940050100030720a5004550100000c1d1003141164401c1ca01840d92a00800413940c45c1c481000060f001215a02e0058200c6d180711a4048a044c0801d0300c81c210301c2d916150b45908050001d40410009400104118070b42c2d080810403e845200a500440c03098000064600821041c0b01c21000e00a0000e1500301083d000c100c05a41c20600c00d405d1035a021800180150303d0408010003000030704009401c0080c2c0c20f611807410000101c0d10500e4010803202500b00b0642c00608903542c0303800b4003500c80301840d00b4680900040d4004456600110141004101641c07a07403c900d14070740121320140c0050f911100031000f40f0721003a4204030840303510503440014408003001c2448c0d100742001026a1119a4103032407020035205c9622001f000a04041706005176070b2000010042d1609840 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 804197940 1250 804196690 804196693
    0x121701050f040f090c03061113090902030a140d03061401050d0e01180804140d0f080309070509091014090c01050f090904140124050d0c1a12090304080c1005070b18 72
    0x20001046511b00d001e4804250440000c9c00403103040c82d40c0c0c1c401612110744101d805201d4800c0a00c0000c1d20b0802c240d01c80c01d216030040000c00400d0304014159400d50348401c407504801c108803400b41e40d11100302c494068042e54007090008407081a90b0060000c540d446580c90442c405940810140d10000d004654000c5101700c2e0320646d14041250350054200300401c8005d1183d005000910500050b43d8000503000035146a141e40e900403840c0000b00f02c60821154010000b45014080b06101d0328000f10000607584100e403400c5035110b80d0301d4a40500441c1032000104004556200c441c0841e054500d025052070003078101840c0010a410704064030304299420b1504a141060054480713009070343d03998040c00c0e0703a0f5280c0b8051040d16040080151a204100600800c40100c6850f0110030700c1007000c1c120703648543c0d40144842100d070240c00350003284c000308010042e1000c001014010742200f1035884620100360242a6410f205445005100712880700800c124100c000607401d504020190 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 804199190 1250 804197940 804197951
    0x90f080d0905031209220603080a030e0a02010e010c062702030f19020906030c030f100c050c060c0a051309021305010503040b01091806051003121701050f040f090c0306 74
    0x800f0941c84221000502c140080140401d10741440c100d040001340005c405940441e0190510601059551503001620305040005e00403c90310360511075003d080200c0f10240c24031412640c0001d03c800d44c84c1c2a41c0d41009000c208010074400740c0d80c1b050030304a110305010b40307001c10980c200103103103c00301009904c06d00408640d012000c0010904a2482e864803a22082100c01035080105000d409482d41c3c0c4c01d8401d0529407035080c1c5003001403c080040220042210407100543e00302070741d00c4a120001000350038030180300000000a2001d810441c0e034420182c40344c0c0208811035460182c0740542c440700c1142040010740c51071a900a00c00c5400c0d0015801c962921040191014070042d170f0014480c6444400401c0344103034641c00405014180121164200074540b645c07001d803035007a50080449083c44104004200c41c40307519103103100341070402c0740c0c01200299031081001c105100340d80c002e23445008910710079a0f440d40000c0d50740500c540c0420180440d41400031050410f8041103a03100d1902 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 804200440 1250 804199190 804199199
    0x10501060206070509012a030c020f0a120b220b04030206010909030203090111072606010503010c05040311130617070b0c123906250c0201090f080d09 66
    0x100b0000d00c40c1080740ca4542c80c0120010046400c15084c1000e0b402d00320520502c040448005000000da460103660b540c114002240100818121004c41a5100b4000c040701040b40403281000850a039400c00d00b091140d9131404901c1642d805089103440b0401850388e1ba89080000741e0701c40c9030065002e07500b00c1c0c10070382e03c4044207012a00b1480000c1c0160b40103001d191138942c49221000c1182a0341c0064500c007694907400a000300c18003040500903d541e4240007400f41801308030003070040c2000c070300a002c601200341000d8001c2c822400080e154440103940c2c4815a1201108280701a034486020040c0a41d01d20603100c0d40b00c20856018040d009981c0c0000e030b01c03c5042c0039034100c501d0190184c40c85554261061030f580c3d1280d0340da060305140c1e140065038a100e4854052110800b450194200700038182261400d00301e0040c4840e4104104d00c45140380c460551035682a490f1103405e01c0e00a40350b540c00180c851450550041020004070380002ca41c02c0c40100b0a01407000300c0741c5940c02c840c0c0d141d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 804201690 1250 804200440 804200443
    0x903021020031603060503030a0e1206010b040b0c030c030d090302010e0a200d0206071a0a05090304060c0302010e0106140f010801080d1b0b0f04030806060a170603010b031606020105010602 83
    0x1d880c01d24a1003002d1020404411240c0d1462203484203d003000111107942d4400b00381503070030123010b400100e441d80d10030900d1418201c01d0b01d912554003d000d842a90305060f01000e0034000c0b40940302401d40045079001e40b40f0341c20030803600d4094020084940390304000c0001d0001c0d01880204070019400d00b4819a60704400081110485034400a82c0f0181c052403c0c00e43c0e8076a03501c4010707681c0094907a4a540150700c6020061110702e02800e24490b04407440c01014070049000741100b490b01e4170b00420400804004010789042e42c09500e0900d10300c40d0b02d13060032805030403024403c8005d94a400310000d054402c034003240d0b080c140c082c4c400c05100c1e052003005480800c0d0034403e159640d0003046c8070702c2201d48607050004ca00c40c4c8a0380441e40603017a6840e1002450800c54503810310f003504109010506400c0442594010421505a49840c0380500d0050020750103100034446103103064082280d07650700b904103101c1c002019049412080425001b500580c2c1940700c0e0304d015519000010413407910 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 804202940 1250 804201690 804201731
    0x1206041b080402010e0a050901120c410405090f0f0a08041e0305060c0909060d0f060c031e0204180203060a1221050a02010c03050105010e0913050109030210 69
    0x2152070308101903650781c0054404440c00080c080d03200d0004100800c1310b9641c000c1041c007030b04140000c52803040c0307189840200d40c41550080c4100080c1e900f80740141c000300078114a0580600919108124030650700503140c90b0036400d400b5801400c007001c001c0400380010350600c0034007400080700e10051444240740c4e290000d00b0406003441c103003044240101d005418003050389450310360900c81000e070f40e0748413076003040070540b245c80d00d040740082c040d4550b01c1d03c02aa5508100c04403051011a422982c2c0c000102e10001001458a5112240e403203205003e0340c008103a20f5460198035107520500c403a000020740c400e0041600011882c05100022105442500c6c0f190401500c82400305040c80350712103240301400c1e4101d6600c0d1001c04d10143d50002d00e030b0368014040c1c26450b030780c0d01c07210140c034083e003035851200320700007090318040041155a81c080d410098014081e40d44001d2600c9030750013010024489000a007056003880345030b00c00c0560004d2400765504100500304086010b04000c0b01004e003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 804204190 1250 804202940 804202991
    0x1415160e0906012703080c030301060e10050d051003050f0f01140402030a1e080d05070f0309030f0f12021204021f140906090406060909060b0910031e02120604 70
    0x800741100c0c0401130707114506101c19030b103000c007410781a280ea0703641d42003040e403010320294216000400100304880d08000c000c4119401101c10034001c5822010040060089400011240c0d072100d0200b0841201c81501e500a5078008060b14840100c078690544d50711200c02c64041d01d9032070020b1240390490254072450182b54010003810007030384141c8401c0f20105031703040340c049400c00340c0801e10300040118004201074041105c0119887c0b8001d00060110100426141d0a00d802c00780644000381c0e010040f01800505401d19180c200c900c1c1c8030403103102840c42c0c4c9116216100103100b00b00000c3c0302403580e214500c2218040c0c05000314101a020705900d4101c101301282005800c0501c00000c400604070202c000b4001c0e41c2000038080000d07041c0c1e003155114201140810780f00303001014aa0141202400403500c1c2149000c0c241e0000c03414181044104504140c1d07904045410301d02201820644081c08201c15512032280060740fa2095009076640c3e0b20440c94080302500b919295018801100c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 804205440 1250 804204190 804204197
    0x213080304080a020d23070e060108270a0b010344030406110a090302100203070c051201020f0a080a29041d0a06021809040f1415160e090601 62
    0x14015901317100074500030001c02c8410800c01d07403040080c070400c40340c240101c543d00780040c03210510f0148130707040304100508004e0401214208100230b0b4112860030a0b8413458802012104101200c4d403c0c0c2005078107080108494103c0e03000200384a00180d40e1000268102d0345110566081f81d9209405880001c64040c00852a811889184074202c090b682c072078022070f004a0840c0100000300203d5000d401000d0104086072010701c1542000382da2000b40d444940010b524012040d00c64076003100c001d00c034480c0310300c5c004500703010088000c2d011b556520040809054580c803020201501c0800e0072103220010310b140400c440c0f40702c0070b00b0707014079108211507002c41603141040c402e010107084030203400c07103040c948220ba200328180701708015141c1ca030003207000607240c050300030003400341c041c0030f01e890340c800c46a000520010402c10001210402d61084c1c90b0b0140c520404846802e206005001d612034242c020200203100c114240d03080c01c0030f0040d40c2c50031480840d410801034a041c0685030305000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 804206690 1250 804205440 804205453
    0x3030708210609010315150b0a09090209060906091305090d081b0d0b040902102006010506090108090a0c031a090d0f1407020402030c2106030a06092103021308030408 73
    0x4224208002040e0b6684940c01003182c280e4181e9154141747c0c1c640c0140c0604d00c00140400d1728a0b80809032101070f00078200e043d8a01031048000500034041c01c151280318260000e40c006480d9144040a940c10001c8441484585401001580c807030b1001920f0750082640324000450004502502d2842200d0031500242880d04040209000707040440e04940c00c10b0740d80c1d8544d4003680c0c40c0c108180076808103a40b102541c000c035908040d080c9004400c1101140e100c60014450359841c0d45c152000c461085c41c0104c0155540e6030198640b1030709402c042c0c220128202c0120510401c182d06110310400d8802c850129152038060903603d4102444141c0010303031410201032013034410810b03030610f1201100140c0c200300c01c50700020200c0c0c2c4282c41d002c074100b00014050000c480f032500214a9058028030304441854010003098882da400f0800038203960f6a001000c080140d18618400841d54509031700f0a0b03082c1e4124054000d500c4060081c001600303414001803941c0000040301c060b80c1c0c010015000c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 804207940 1250 804206690 804206693
    0xc09010c0f0218090f07080a08030a020a090f080c0f0108100618030b0a051501020609030a180e040f05010501150e1005190530060f040209030307082106090103 70
    0x20024900490f0b00c07100200141d0050000c0101e018007a28090b00030344040c186501d03046103048500c1d40200030307640001800d20041100300040d80d6000c0c031011405070341c800251b6412565410b10b5044403103c101110300201c0da0840015035a44200c41c1920b4079405483d00200540f0400c2040b5002c031110141d0a00522405108034008126049a506181e41040d100da94002d0300040072500010307101c0e503a600700f1011548203041060048000c0c0050542d60030140101516840317034410365018040ea69480001803d00709100d0402000c02203c01c8915003840d00d003480301801c243c10300352215030a010001c02c02d01d005140f4560300c1402a2108048001c00398148408142039080507002d22400780804603009044560381e0640300c07a2030b611b0365500c40e09900da07070540103c070680280414030108424104c40d2207074040c0b0b03500103c048403d19160a41100054080d1007603034881030f05400046a480100402c00010741440030590b046060307034107003482c0c13918030340c0c038080b0f51141d03019940c2d500400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 804209190 1250 804207940 804207953
    0x1110c01031a04230604090c0e07051c0b04380d0501150e070302131e151805030f15071e0804030e0a0515091804080703080c09010c 58
    0xb45010051281042c03100e19600050450740d002c0c4040140020b40301a0402840540c20b4866110b5401c590400810f04a622000d00c141058000c1e0400e49080b9400b040070305000e0020f40d0003092214940101a00d407880000011f403045403225401a802c0041001940d0926044e030061883c2100240c1100042c00c0d2203285034840780100300b60401000b214420100d0310070f000c0c00000c240c08082d001c040c1481c0180c130503c00c1d4070090042c01010310501005110022a0007a10201d0315218014903031500004405201805180e108103c107120744061000101c1d002242065208000c1c4551200030b40c0d10028146c55a903400000e0019400800002e4880220400d8551304008079203003088950301c0ca03403218284600020300c8400851101c004100c1050341c0000104942c180c00d440d804c8005140c040130400d44004076034889540305010400929907120003d0400500741c43d08500c10041c00c00d0300780384445510900065002610440000d002d0080c4801110000a0181d40b480c80740000e54641a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 804210440 1250 804209190 804209201
    0x111030a020a050421120e090c0304060e0d020105010f0f080a031107171f1a090a0f0203161403100e0709240305060d02060f09061b0709060501110c0103 67
    0x11403d000c0c0600000c03900c000740c1407101e030b4413080d40d4042c06202c0e18141064042c0e00c020701c000b18200401012003104a4403218031442e040200721291039100e4940c0c0c0781030000750083e2444400c070707441042d0b1604041075054000c2c0f812551180130305840151540000400c2c2c0e00c41b801800405d60103000303080000791058445054a051520031703100b64070307210100610910b02c0d556455441d5031111101006500814403d0f40214042e507104021803541c0001c5403c9102c507400321144a0421040061904e80480d086910070105e1500115602d1801400c2c0e440d5030460314940c40c001803c40b6061a510760015001c99010b0300d540040e4240107441d000498904072380042c902010444540400980303101e0543c1030002000c04030003410040c03602d146006040b12800dd0100744180e840c0f1840c80c0141e207039801210b44c0800ea15410998603240c0c000811190300c9040000344468020001d1885003440110f0018180c414451062203c0c41c4e030741c0700441d00d8504d105c2d005040340c0c000c100050070b00d40c06603021 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 804211690 1250 804210440 804210457
    0x503090609120a05030d11070209280c080415060e0a022206080a140720160f08010b150d24090212090d0503010317280e01020111030a02 60
    0xd0840800c034819040c3d0410881c45011141c6510200e04a01401d0303840c050000806591210304e1f0901d100c0e500003608030a40a480b400348681031024080e403481d001c003089402503146070410300100300342040041c1025022542a00c1d50880840c0c0d1030003000142c00380301d041710825864000d0f072307844041c45e4200070360000d00800d041018608590300f00306103200c1c0c0c01000b404591281181403501029049c2581c0a8110f0380000c00c14a400f08038046400c40c40c0c00c4521245554164144070a008190780741c001e504190380c0a6680142c000601d51340c44205403016101000001d0080c3e00d040428000c116490050344042207405105417140e8071803540c0001e03400401900b2103130070080100e00c0a8900070017600300d400556000181c480320000101c0001c0e4100d06054000c20f50107031911402000e5000c103020040c0380709400f0480b40390800c8150103940c01c1303d1800011002111120041c40754000c40740903a0804a11001780302030b055030041c4151038a2070803603000c42d4515901c1c2c6407000001c4d4803d612 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 804212940 1250 804211690 804211699
    0x60f140408120702040b090613020f0c01020301080105180601060512270313080c090f0709090e0304090606020d021b03010905030d05010302030c1c06092a0e010f030503090609 77
    0x800a4500303001c000031480810b2100002ea42c80e5030a00600056445845400d0700071400d500c1800790b1521040c4405080c00340720030700161130300c015004c1220f451041c0d0441039595800480007280514042d4002e9018090080144240c14902c074200c5894241c00d11581d00410414400400010807410801b80e00c00c0e804580e80d005000d1300c01c1941c4030444006a0701e00d007548080317160035003040301c2240440a03100b100d004000d081d04035030003c0c009000040c80b107860700714094040307030796680547c000701d012707140442d400d000180c135414007541c0e41c0d08640300b4402c549051840008bc150300200d00c0d08881d800d07943c0541400703980c80c800e0804c8001c1302c043c0c06070590350f504121004601c062006d842031143c18a0301291039451070040525110154030100d00c101048014480010038040c1c000704036691004002c980311324603083c00b00448009030b034084c2c16000d040b031504609010701041070f020356122030180206a600e4a101c000c00382018040100280e0003048501c07400e16101000e0a41200002d2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 804214190 1250 804212940 804212947
    0x20030a020904180515070e13020c010b0306180705010804020108070e1c05031c050c0a0c05010b06070b060102060a0509250504110301140d11010c150513020103110301060f14 76
    0x1c10f4141e41c0400c544261030641018100c0c1c045000c0c26103580c1e400c10f0a52801414185914000428540030300c09a000802d50008455010a0003900280208400102501c0305490030f02501812481c889540a905015401c00481d007507004401c160300540d01a950000fa5a640c0c02c01603481c0580c4450b09948485485152610000348000600c0c001348688043c5032031b0403c2030702c1d2040a494103034001901030b060034200034510900ea01500d680d586640b4010540b086203042c054010b08102c00b841380c0101c0300113000b00500042c214418002d42c82a821151590344142014045600c260bc1804c036a07080b6181d041c0c44800046410044c0119680010440ca0380e0f810008080f01c1d81012444000381c804001000060340d0585540400d01007580c0850346100c03255070303190105e14035011050500c080440ba0307006000750410394400c90b0840c0784c0d0421003802c0c81030984940c9070b420703c81240041e0500003042030941807501680d040303450b10b80b150400040305110594520a80c0385400302e4011703091 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 804215440 1250 804214190 804214211
    0x60a03080a030b0f1f1808060420090106080a020721030b0a120f06050a0b100203030a0c0c150504031b06140703023f0a0f20030a020904 60
    0x108024840760308540c8000460f105548140030082010301c00a912603130440a2030714084202c100c10080c1714449103414840110707402d0208206d070030150011079152013400100310070084080465010fa5071158504113000f81a0000c000a16009004500005403034101040440301c42e9005400124418640000c000300c000e03071540e0141303a1100840d400203884040e01021030802d4040007015200b52080840c0c16030242e140d40c41564102e003001484143d030b81c0c00003410001680d01900e62843c00400c40002c00f6040c2c08000d540390070654a40c00e01502d000701e903020507030041082044030350b4410315450350341441c1c010480007024010401d40502082102840c49c1d540c2613908211854810800090f1a4807248001076010328024003a5041c10300c100701e0401c0d01104641c0310348000c564022111740c0480c1e02e00300a86035050780c00b5001680d1142c041401440c884079000035180c0f51600508200050348101c00d07129143c17131042d52901188080010906555081c0c00420006002420100300000032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 804216690 1250 804215440 804215453
    0x5060a06110c04021602122b11100906051501020709020901030207020a09020307030f0e031b07080115050f0105040b04030305030403090320130e2d0319020106060305100e060a03 78
    0x8131102c0545c92546680c44c00714a4140c8000162800c0e0800820b0700c155102c010b00c00c4003401086980c2c07442848005034004501c1100507500030ba03980000e480b10079200c4003a510250100160407140c941c21b040000d541c0031100d10440d4000901640186440d6280c120600000c0d40001c01d100e04054003040140096200d80c4507000045c28000c40040c3e5929001b1342c010103c80c001155564441d0030410b00f21990400081501c40780038031480080410400800c1e25443c1410320b500c0720345a54205290b84a40083d0010741204954040d91205640c130101d10045505110f2030081084640d0300340404d00120b84140c001e168028402d0904000312501d82c0c54a54104111024000410300b019041c01c21600340b1105411100074544018010021010902c40d100c03450321440d04091821810034407412501031501c0075100c0071301c074141da65402e40b4041d48031381254404014409907080c445d0000b81c99110384a0303544148600c0390b10014060074050308401c25040a8000d0747c0c4440c04032000f001103040e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 804217940 1250 804216690 804216697
    0x114071407083a0501090c0503271c09051206011e1e081b061603020c04050109050106021c050a08091005090c0f0301020f09060313050f030310080105060a06110c0402 73
    0x203518460480c0c0c2c0d0310340c000400e130390050300540324040c1070210380200c172074201d401d6035003245030106100c4000312406185400d106461241d1000340c0b08142d40d41110203120348804c143c2c51010351f2135088203501c40307051000c24643d40964090541c000c500410005103c0c00d40c8041b440310800c500403c0664800320365100444c0c1c00020020b03072800e24810006d2250401031a00c5442c88000711001c40042540090418080d10002c0d0282d03d8001445404140c824480d4018081000300100140d503125100c100082c10240250b001502c80e40043c040303c802c0200c00d58910100d41d50310340c0d103001c14104d030869410b500580300041038406c40090491400701c90260a2044d4221001031005420400400810070b180c6102c0c14080d0b44100320302c40c0d105407000119000f00c20180d60701d643d01d407176020000b00d0140408802031310728081c61501940d0a00040015406940c13114694441a6110010282280c20503035006502031842070703003009114080d690031744400710203c050740c0c2012170010108040c3da0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 804219190 1250 804217940 804218017
    0xa02070201020a0f0c060905030c0307090c021005010e010e1b040501030c050c011d070b0c0c1c020a1203020111190f050d060603090c0b03010e041b0f08011407140708 73
    0x5d02c0c90320180300c200d61118015004040460040102c10041d1000c01d444102c07901803144525221000018842d008004404590402807002c11166a44030903d02841c2428003e20b01e20003400408640081c55452044200040000b0280c0c40c082c54000198024107000c40d500f018020140004101c80c8001e110303504540d0001c0610740326220310041c41d81d080501a802403000300070140051403035110000341e4070080601c20303110700c1d460f9800c61111802000740080c000b940424001c10201e2200000d498540d0b540740b20390024441409002044503080c09140c52031511400c00064504029100f0200c15120702c0542c140b07107151040050442040d182d558100320042929080324100700140152000010101034500600703550402d00b1003103034818007030405842c00c0140340904010600314004c9070000c00c03000030500390040d030b28004240603012606280100c009660005046140502a000014040d4541541c540242c0341e030703240ca13241c1028118220780d112100404d055100307a00200704581 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 804220440 1250 804219190 804219203
    0x10b03310309050604180e01020f0712120204140123030a14011e0b0c03040b2b05010b16050a051204050a06020c1f0e03060106030f060911030a02070201020a0f 70
    0x500c0c4034140501007030b916501882c05220100010040740c0c030f00e41070310b040c080340d601c3c00403e511800020321406030081c8115030000071070004034030b0f040014183c144c80c0701c40000e03107655a400400034286812401a8414174850060766401c100c1c296124a0482d00074444103144403000c0e00e0103424003c05034100300c07006100d881d0f561030044007142007070f00c0d12401402c24020b070a9080f001310b4003000412085116001c4d0404000c90380511880083c01507030040c0180300809a140d2600620880440f900c1884030b044205103200c44d2890003805e4011035044e40c036000c8925107450154150b13868150f030034441c25a080d024240703e00d00090300500c510312116006c071903142e4441c0e0400b001c011054040342d0010b0290f42c00308034098103903190390369901d40881c01c1948031030076a500002c06844040c018140329a250142138004581d054160f8003051250382e4081c2d0802c000d503207454800089a01c115029942d40c0e0301400010301551883d001003415500c1803055480442481e40d6181729064030440c11a4030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 804221690 1250 804220440 804220531
    0x7060912032915120f0f060301090f030f0309060212060f27070903080d1a0a06080c03040206040b03150315150108073e0c09010b03 58
    0x680ea050181c0b611040120040d04441e8558108004159460007801401010010110700310080c000f8180c1d181501120312880b0036103003031214403034002c00403100c0c00c44010000000c650039080510a1030485580003081012340040d94070140c503902e000c04088030406495104501c001000c44c0054026245405100038080c1000c00400000c04141204580200007444540b5940c0148031400404003030200080b510740c0d241d94a080390300082e142c00c05030810300d00042c0840b5800349903100c0c0c94500381009002c10040114010071464801511510000803a038502080224290b8002986c1051004007014640b0f42e4826181c2442d0300f044034240f44810481113101030320308040c049038452082102a665040ca0903d100c80e050b80c3c0c2029500c2c0c1041702480019600394010502c3ca800c404c100030305080504004504403102e4a49441200e41d902d5041c1e5000b0355055000030f0101d88280c1c021f0240da4642e01707001094510780c0000b85890f400610302661215000d23215199480c4069078001c00344003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 804222940 1250 804221690 804221723
    0x40906030b07050903030301060507060207021215070503090c090907050d0c09052503231f1d0403110a061d1b090c07050a0512071b031e020303070609 66
    0xc28600204010140442000501051781e00402200e05550890401503180c0c5611308200000340a490741c02034001e452144007603000400090030130b41c05411880d10a1243e680d003082115103000c02ea401e184c84d82e220411340c0c5076503d80f5038903580e4020500422691440c0d91000000d208008081c1c042c1c880e0b1010700310900c50b03825240181759000302c40c140322a45048555100b43c0303c08000700f517110109030703483c45d103203c001a8003c2a142d108c44a5116404c0381d0038502590386d01080d8200031808415222503001801140d2290003405000c03c400110882d0f40e81c075107054816000000044410303000b0850880c2c0000e01521540607600e4911558550350745050704164030300144446603951401900c04022803541e28032403203552003020144070075150340300381c9056468041e116100a00d40c0c02500c594501c540400340182c101c0a00500001d40ca150034030300881007a0311b2902000d800c031605440c081e00c01c4518031140b00052480a0100d07494280c1036124001210107946080b03135400e20b00c140341807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 804224190 1250 804222940 804222953
    0x30c0306070e15040e010b07020409020d06020a17010e180f010509030307030b06162003070308030708070c03080604091103100f0522140f0d020106091d0d032004090603 74
    0x40d00715142d1050f10740790070b01301039150203040700500c106e00c2c5499000500780110b40707a503004070070810340c00b81082c841c03040c8074500500603410941c20303140010b880d601c58140a0081e01c607801d0484d001c0403142e0000f9115a600995085501e50507841c051044540003100d80c0d400b40319551059900ca03001d15160309181400809842500791140e01c6220240003505520440d00e581c0103429500c000800035060303488400c9a03440b9150007505900d1701551400000b401070000056204200c0e81d510b540e22603aa19005032001c51012601a00088800000407850f0825600c102002c81c0144105a400201c1c58002840c0611030350b44e258850352151b003802c50b07104441c020281c0004070b64100151041100801500100e5044d45c041c00c00792000e5480d107801c0e1030a0004d00301d545032007815503521a480c2d00b00680030340a140306000c0310343d182081b0b01d80401c0c1d68100a4403841d20401c045e04681c0e441440c120050101105a409480030228107104010110b4008000820319900f000c00e0843ca542440d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 804225440 1250 804224190 804224209
    0x9050c01140306040c11070605040905090a030f0804150606050d050a1a01140c010207080714010605010507140c030f0709050a02090d0b0408091314151e030c0306070e 73
    0x3410300100c410000340001d060303001c0d6a0720060613540010021160101241c0b400040c11b081122401340c14808103031a50703c40c0080060340c00002c000d0100e519101d055503170301d2010b06c80140000c0e04607500601054414800386030010300480301408071050b688102c10444580d40e10480102c0c400044403802030146006107644122808410800f0003030200740501c0e040455600c090420140d4461004400c401c042594014228a0021903d030303407041c03a00c89003503441f06909407050724840031a10207012050103050255401a9940f43c240802c0795107892880458a04021150203203002c02c40150314100f00e8000e200c0c0c0c108008060030b0303140c03224040403500041c004002450040046000c1c5841c1d0294450f1132943c803807041c880700e594a04107540076005083c42c06510070154a06c01c0c038420480e810103505105150906040c9803245030204543c04446a801a0420a80541d81050a05010400b524444064203860031542e50100290801d40110743d25008150022807259503800d00b9074030b9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 804226690 1250 804225440 804225463
    0x50607032c2e08040209130804090e070302030f1c030207060905061510030908070209100f15090608060109090b0307180c110d0210200a020d03050a110d020a0c05070303030905 77
    0x9403d042c00d01c0d4000c9504e045000740000d0100010072a24403c01c03032180308407002400e00110400003561924411a00c800d03040c0310a038424424800c6403203141d6004212821088026030800301c109400c01d0040d80a504005000e9510903551140c400100f0f906000e068410f40b01d070200041800c1c40c103000c101c00e008029042508041c5048c10010015521404560b07440c1d030121444030090752420003203580d030600c3e600141c034104c81d4180000341120002014400501340c50702c4445069482e42c101710b650000807251240010a201030811413003025602060100c2409400c1c0c440c6141c0704c90210a54110300c01c003000c00256503840301025254005151540400e401015104140c2e803000b0081d0303918a05150000103940c1c4d459081419140ca00044112075260039180341c560344440c402039124800d50384c9810209007050000b84880d1400d02c00e01000780d404204090030254001540c074001e4001302c0200c020f1181e00380480c0003281c010031104008510940e0089800501454000c0c2070030302d003441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 804227940 1250 804226690 804226697
    0xa05250503070b25050c1005030f060f0109050a0311040b030304052107120b070e0402030c0d0504020a030b160933230a09050607032c2e 60
    0x60080395004204142192080c1409980f120131510103a00740c0e420700d1000c24100418103004000304940401c0980c000c140480d8812034003032503100280da003403104540041c1c1c2e0003002000502c5a26040d100340319000010b04d001c1030f03d6502d07100442c808003c503410030b4071aa2404550300c03400d8680350140046d03401064024508092814000c90344100524400c005001c1005410120410007046820001e02c1f091408120f456941d04103904c01c40c106039544e00029601f402140c00702e05090088074000c0900d4040d05207450200c10381d0340700500c0040c100700c0c0d101561a1000004c00c01441380c5900441b14000a002d80dc1c403c0c044c0680010851b600c6038040c40b4990100d041400d46d94078070032405044800c1007942c1e150783d0940c01c94060070804070101c0034807a0b0501c1d000b03502d143e000160100d80307041d4549110b00c94a41c000c00c1107900600300002c00103a02c00d60440c295001102c0401c0f24510b044015000040c030501c009170742500d40205020444c3c50350341d110b4880d01c1c644500108850403504 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 804229190 1250 804227940 804228013
    0x201060f050307030f0f171206030610060519021009111f051c1407030506150c0a110a0f060224090a060e03090303030a0b1008010e070810080a05 64
    0x743d6917030090b100113101030017101d5040c0000d010301020804250528100c048125911000300c03024410041c03003035400f14000d1080d000010041e0a8841e4400c040d950684c407100d06040521100f81c625081602c080c8003180280d210340c080c02c04603030150f06071440c401c0c6a0303c80d50b441e40b10b0511140300d00f045e00480800e402002501841d64100381184c1e0200840c000141051840b2104440501610000000c2800c1d0300400c202d102a03050b1302a501900c02182d91081a600503a81007945014a0030f6125950300014808000601d0a5402e61a00c0b00301a04000e1040d40c1e0341400706203d503156010f1070250300f2079000340d090700881c1d10103018815000814200345080501c0165507400c03800a000304150354130817800c104103008100340c60310742000030112650b900e060488000a4900780c0340075030049a5505640420601031140c541c16110354880840300c0c0d40d0f45000458044c0c00250606002440150300412400740c2805000c203450300550092007000c21244161849020303d9000549500801 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 804230440 1250 804229190 804229193
    0xf2e050a051602010c12170702121c060803030a140a0c1d0f2701050105070f2015030f06040c0512100b12010602162103030e0d0201060f05030703 64
    0x20303168030340108960905551190303c01600c11404165010781140140c2c601c0542080d40519090b407406416102c10f60305440d2030b80140e81e0f40160424030311030450144920032100303501d810300c40c41c040101c14002c01c0e000d40e101802400c55000751819111a03455280000c422040041d80603007203225501d081220840003103000782605460200c104d07080d400301202e1a240d40e0380d640c1c1215200c03402480b078906402a412200b090717421808020b0302d054007080c00040c0560050302a103510a80016941400f0156079840c890b080903607800c0450074140b59000c01c01e150301ca00c403c40400a02c6015a06d5490600c940c401c601c41c44001e10341413040d8100130231186042da000c000d40707004041200243d12680c5801c41a0350702808a50021128041c0201e0001c60b484020131882c0d040720b0083d0240c5401a41c040e00004044180e40a08100c082c5284689031000e602c08900c90740180c040d1400181c194074100c9070074245840341c04d850340140e45442090144400c0c0c82c40d128010802100106425440c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 804231690 1250 804230440 804230447
    0x6020f07050d2102101508060c09150c0f0d080a05060a03171c0207051f02040e010506070302010b09091609050412080c0f0c070608010e071d0f2e050a 66
    0x40083c406540c070680b01d003402c01500811000a0b449040700e018031199a000241001c040010300c50121644620008a84620760a500700d03207007002d024000d04800c036085400301c030b0107610140c00400248100c00b94000d40351418000700b16011400da5461203541451602001130341c1020303014511030303c42c0310310800028805036683d25a0003943c09001d621400e209000d002122016910403042900000e0614208a0041400c56150140c14075610105074601e00010480c0124011901002d149400502043c40c0c95006000100e100744000300b2a0700340940460a090029500d8070710b130344e02c80c0f10040c04170f8281403038610281403600d2040046242640f2500c50741203000c20749806000030480890310129180003150201c146c20016555907035004d94505035240350b64400d5000040c01c000022502c4640001410300480300c0c2c1c3c2d00d000c400911b0b41d514031144001d40c481e66500400c21006010543c80d902640030042000c1c1807035010b109100c4c1382071f03128440c0c0c5410410800200300071640b45543c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 804232940 1250 804231690 804231713
    0x6170604030806031212040c0e04030e220e0604020906011103220f031a1b09010e040b040f0506100201180b07020a080c0c0f040b0102030f09180106020f07050d 70
    0x105480c0006403500d488000c242410b000103d4025040d50019000428001411b40300340503900c51655015002d68804084074280000c0d20010005450754040144515250320001701c2c0c04e00003480e11b4004601091000100c0e05017905005032074001e4404c0000b5494000041607020340d081c02c00307900750007000159586a1003400003005011006100391001410a006054058494038002662550710b07410150142c40d17412001d004110500c100043c0c4018080c2c0b0507100300d03200724070382c0d608108022005581708020b10340304980150751407854215a58840c081c0550548520030005141d003046c0703041c4148a50360b01408015a0f04261490600c41c9a89050b0b1010310b410412084071621400001c0f410100c4a00020700711600204001e0301800021510044d88a0100c0380c5001812800c030070b010035510404101707400b41e041440a04c0d8513101f00d100074103100f800107080c810070001003490900c400d01c0c00e0304a080181d02c072162200c1210030405c800e201800c8116070000c3d0341c107007d5881021146 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 804234190 1250 804232940 804232943
    0x506160305360a21080904020c03040f05030c01050301090e010b2d150a0c15020d0c080a0519020a030e07030302060403110f0604030e03010902100e0307090b030a060e070f0303050403020406170604 86
    0xc030403c07481400c5c891041c09450744188010b04c02d43d0340340c000390750302583d94005029103010604210000540c528000469444010040e11018116860480203070010f1100424840165480760110340d00c0c1d80d500c0c0051b18400c1c00c0800301a40005007420700407001d820604540740030f0045101d220024001801c01d540445080e840c1c809000b00451409401d0303140e44c0118610041e0002c165030791141403d40014000846954031041103a844010f00e909480c002c0d0b803039548884200700304413541c0c0d9040d002860000c0c003070f040200d61110100880c91914000b64005e80041e0410800e20080561007460f00345400d4071007000301207030740902c0040da8881c00058802814420302000003501d9032000c1d080a200660010510034982e89901000340503054134143e07152090260400209a8003030522665104182c0a4010403c60070307140e83d044014404202561200d03c10075a00290a1600303081000181d44690f40385d5464074a14414081503600641000300d8112641246003a0201c1c0043c01c0c6501c45d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 804235440 1250 804234190 804234239
    0x301060e0a0f0b0c10050c0913020a0801030605180f0303060102011521020f120f0d0c05071a040806070201020702010915050a21060308030609100506160305360a 71
    0x2107101c4618580345c00000c14004915034200f0040000d082c0c4000081c03c41e5010039a81901e1704205141810100c1c82401410000710f580000140085540b581c041c27940303e05910745201c03a15144000043c94104000081000c0780e10010810100756828052a40352031030341c1d2440e403406401e08000d0841d0b4800301001d85e07140100c007003000081d07594403000381006585c00b400c0200c441c00301d989042d844183c8070b1500e2a051044c00f5007100428400d07484107403420341003806044254180000c40c09150b0700c4044490000303200b804049070110b801d2009500950042d000180d45180e60b10001d00755040c681c0c00707a0030328000d003005400201d4002c0b044407102c130740c40c0c80d1285a0481040109600c03892500d02c0c1032280d441c00c100881005074110045000c0d04086640c00c001e65141c240c01d54940f0060300565400c49414042249920018500740341d49500c00d08000e414800080317140c400c1c0741d2950440051102d40a104c080030b42c00b07000c80710ba0850b20255442c03200e4504004885000b21204c1540340303044c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 804236690 1250 804235440 804235447
    0x706050a18050319200f011a0a0905040501090b09071e0e06010804020a090e0c0406081b0603041e080301030303140f0121080f22080c042706020301060e0a0f0b 70
    0x4c00c1c49070301307504504000703c0e40312019158060162641c600c200b1b40002c00c03039840e25500c0d0350b058560444150121600903c0448103030b0400e0f031110054800076008890b80d6407070706840c2c1c0004000b00d05d002d21501d4403800416006140c1080001504040c0d16600d554041e610002d116400754548015840300c400e003400c0c50181c80b01c1c8007150001328107a0003100307103929088034801078403804600003044100440f4188549502c5211031600c0300100c00d11f242c1034031080c030b0380c52419082450145030300900030005143c1180c0c6c031540c0040e42c401820011150140c1c00001401055010b11907280c5c60580c44117920715500c0c110004140590041c064085000211803941410545044a2004a03540440540e4990414140300c4900d90040100360303a0a07461501426901c17091050340380d04680500004010342404801400001c0184041c00c1d0740740031220004012035040707101c955000354882c0c20011703a45d43c54010000c0520081d80d088910507002004100003207804604018107072200c48000c1c1da40c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 804237940 1250 804236690 804236737
    0x30e0303070501060b090a05030c03100b15030a060e0f042301021b0303010311031504020409060902091302010306050f1f300c0507031d0a09020706050a180503 70
    0x14602440d000103080c0d41c04c0200101c0e080c04400050810000b007591a0000d0700d032203108158aa0400010441c1c25500a040c1440010455081540b0802c0042c005140802050180008561044072010030490301d511080000c66044d448075580000c101080c10102d0038140e0784e010400803000400718189a05010b000350060003941103030484009030034000c04406041c0b804580340d400910040d21180300c480016802401e0103e00a40d0619048140c181780d82d603280e08203c01406100c00a640445d034440c680001620b64040240c0103102041021003000403a20005095036180c4e00002d000f8600e00f060011103488005e80b541c0001040259003029a00101084400b048801f107030401c1d540c01c8144003040d500d642e0040120710482500700340216185c940c020340c1c452182040c02400144084036900603201c80301e0800c2c0c07007500c00815458025688450780401d80e0014070007a034820396100148044525a449880303000c54404006542d00c0302c4030b0315000e45034005c03046480340d6103918611489 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 804239190 1250 804237940 804237943
    0x3050a0b09100c0206010f08120d0213050607080d051b09041806110d05090613020105070c0306050c0909061228020916021b060901180506041e120807030e03 69
    0x25003014128080090300f40e040d20081d5103000070b11030f0001900c21400017080d0404c01103501503d5601c100c3c50396140951108142c8001d6212864044221f41c440c980824603035680c6000340348150040825a03160504200260115007024140110352503010032a80c0101c0c032120141c4074000b0040701e000640c0141c020100e01340e607140c0784c40100345d10f1a0103132101e4424511405049a5040504200060b0340e844495540d02d00003904d4076a4020440e001c5040150310800040200520482c007040c0e910381d807a078801c01968400c0e205001d00e03510102d6180341c00e00f88412442d0703000a08407070076050f0001f00040c0707a4440080c411000350404058020150b13023010020b4400e00790f40d0240c040714042c500600c150b08401e0301110044014001c50f500b1b206002080d100314001f5a40080901b4509840c81006540640c02180000403400800304009401d43d250000351004012501594602c54a201c1c285d4880e9401c0c0d0700080c00060109003d80040f880300c3d0192002d0750743c14203140178249030010029 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 804240440 1250 804239190 804239203
    0x6180b090a150905040323031b0304080d050a05090c2d0d08180103061203140a12090503090307060c210509030a031d03030715150506040608060a0f03050a0b09 70
    0x64440074108024041015488800315481f1000400d0148400041c01200b04841c031003901d40c0c600a22081c129100b0030418040150340041c424038009182c00c0c0702c01c80c81010340b081200c2010850b0350303401c2004103908003406503200c00b040c00c540905011810040c0c4020710a58140b0594903100000c0a080792501c07440a00400c4d6904031801d26143d20b580041480700d8400904600c6c0002c0c00d00e1400100210010a03c030a0203505da228100000300403180c1e8035441d000000c4560030441d803881174030700d029858810000250700410246580d64442c0b014149010115449901040103031004800403404858141ea0300c4101780900050313a0303804900c100e683e8025080c0d03030b640c076002d10700c40401019000862070031990f40c00a46108030045040405813240244074014207072403861a00710006110170340c00348400c61080d011a81045894001282c42c54001c0d420440102d00341a051050070b213807a038249070007041060316140c6014116a582500da094045004000c0c900080220b8141c110900c0304 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 804241690 1250 804240440 804240449
    0x40302010e1f14090606042f09041103160c02010509100c1a06060d0b1804030c03230f070510050910063c0e070306180b090a15 56
    0x403207582804400b40b849060400c900070b00e50062410b8000303001001105007040c410340744040035244d184e44a0080c0300180c02c0400300360000145010035a414008100f25600310f0542a44520340c40341e60f49000e101c100c40e0f0030b205185801c40c00340200b103420408135031213445ca05410719240240b1481440140ca03a8000e01c0303c101c0c1d002e0031014030306a0080e40072078903480702d60003403200e205e00740070003a1a64016541030b124580c21140030024000c010f2165000525140005010070140140c001031106800c4c1d02910110006403402403a00140b652240410303132000000c021191001c0201001c080140c4030740c040c3c4905019000c07a8007001e010081c040402c8030703850020103000c14580802c0c4a6104d40318040c2d485001c0d0302d00100414450b2503041901c02071038081c694460ba40d860300c1450b480d046501c0c4100104e0300c610150200f03c12131140070a41c0162143c1c4c601107599410040354144031403240403105642071800c426807205a41e11240c55070050560803002520f07000a117054400c1e503a0a400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 804242940 1250 804241690 804241693
    0x30b1302031f060f0b07020f04090302060a0213030b0108010209030601080706020c010f030b0a3206030105060c100f0c030e0a0b010e0709091b14040803041a0702130b0102070f080312040302010e 85
    0x140050b40c2d8894100422040c2c7c42202c100007411020f004000440c0e50480019005a0014002400d0f840c540c0c0c0c028200c020f11050720300e51481c2d0b80da8900c60185400d800802c1c1c50b9401248600b06070904201c0345025206010203880c1850070003500039641d0b1a00516a0704220f4102c44a080140c003a41c405010700c50b001d0403880c41c040d11440030220950228030200b0b40700030310646120754408245218020544001d15843c9035929100030031515030041034402a003405000c0240d05542802d104000d003501e2603880220741c903001d1460280407110f42c3c2d140051150840d40e21a8005103401402c00d05440c0c4050502241e070307d030300904481d1710045402809a903464001c2c0700e100b511025204005000081e82c0b299058103500c840c80310180103500c541c403c44d510501007481844040c403010b8050b400138030170050901036607400260040c00039911000b40e0540c1c80a1a080550f41405510301a010003209600381a18043c0620b60302d2042281c01c4040544030030100d4100341c0b003904480344013045c4c0e40 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 804244190 1250 804242940 804242969
    0xe06070209150111030f0706021809040f060b01213b0111070f0f02010e0a03081206030c0a0504050c0403020d030908060106140406030c0c0b10030b1302031f06 70
    0x1e011540745450b080d081e02054080d0b0340c00400b40030000840b14002c500410146c148440c69960070041e400c0a05400c5403241949017542040d106c1c110070910540c0600d019a0682109040000072a4820b208640c10801351000790a16150004600c0e0000341020100250040e43c1018141c4080380f00c0346101825010300c40b01d806580c02c0e600302406203030341c0000200401c485080f48411244038451000b4946000b0500c0c0b003002c101c82e00204000b542c0103041a0340c09102030300000351f569215420840d490000401d103410415410742c038060303001c001070b0300501e040c2040034001000d2503c1442800d02c40c81d16080000c40c040d2131041610300969004e00280e01e2000381c2d18010b4440484c90080a403070740304280c00003484610420030f001c56040f080203500d243c00d01b0a00c3c00c501400c469004070302441a95450748001401c0401130500c00c4081008070b1419a00b9444c01a1088038041c0c402004a507441c0400409a98003103080040031041285070304103040407804000290800f50301c10490340d110344 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 804245440 1250 804244190 804244201
    0x8071506080f0d0225060507050c1507140d080604110d020d090209070216350f0d140405091b0a031b050309071701021e040303111207030e06070209 65
    0x180c43e268041e401d409845150b032004401008032200221070a120b1078220b102044494020801800c1d041e00440585600c3ea80480200380309030300c10103049c4003581d800501d94041c001503924800b01e000b86203000d07000c55100c2850040c80e000d0090240c41c0300d02d40d0b07100790341400f4002c001101d030b00340b048810035502c8840c1d010b00b10008100c040404c0e8041d2000384001038405102251220003c6103098020702200d04120107030006240100f00d181c0b00303a031503100c40300e40b066031500e101030801d1081c0c00911104403041c0c500c80c204041c0d03615890500104000000924021006a03025101c00380c80103500fa54411000341c020500c6503280401440c0c000505800c0b050745600420b0126108100203201030340c5c280011100b070301c400c4608034440e40003e40c09024042e07504400c0080d8103030910000d130500e207510010300e86510380610200130401c00000d08104060700103003a00e00907136155024000c501d4038027800802600c503080000703081103807503011004159250816910f6070798000c1c220744481d1070300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 804246690 1250 804245440 804245443
    0x28060306020919080a08031b070c090c05090102071406160807020307050108160e13060e01080c01030908040b090a0e01080309010305181e0a05190c080102030408071506080f 76
    0x58811409003203841c0e00340440c204104035400c2121041c07401000f10120640701c0c48001d0300064000c03544580e03092001c8c5031b6094808003038021b860040301c01d0b1400614283c6042d048030001800d1400f44501800018016a00851000f04542d040305501e260150010700080c254400c40005031140c0f210302c070104061150100c01790140501c01d8040300c42e80c0d40c580c0d0040d9000d280880d240b150b0039649241c2820114401c1c1074051420401815540c000d944904103c426103c031074020180002c1c148004001003501004014252a000c0c02c0c100551616078480c820705100314050303840f40c2e4000144091280e11040f00e4200100151064800c09584901a590b26540516000c83c000b0f420400411071031403d10980042c00e902c4c0c0700c000c1ca040c8a00200c502141015842c10001c07034000c01145402042c0c0500c01a1000241d6044d0305030010104d1411208400b45a085102e0583c418000c1000054504e801c590786580c02882c02848500d40e14980c0c1c024183c1c1750030500d03840c0500d01845000540 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 804247940 1250 804246690 804246697
    0x42d050111030c0403230d0c03091406040b0313020303040905060906040501180e0111120907060c0317041b0807090f0203130609051606050a030e0d082806030602 71
    0x8514028040811a060000024041620034a00009041000b00001360516507482d0f10307017800c0243c40d180c102c42d406091781040d8103c0c0c095004105000d201408060344112100042c1090f0b6140e126070190a20104500780614020030110308400030102e000100007003c6180318642c01011650381300d899220b410080d0030203071035190040c0450030100b401860103000380786c11b07641344503205c5031003402c01c54001c070140c4180c81c000381481d542e6150f110b601c2016100101004c41d0b000341ca204150414402403454079a16a02035020042c04a0b410b0002a605c182002c40c1d07040b1a16001203a83c84a05000e0301c861590700c100d610311081d891001640703400c0854002c08981121408014080220344d440c030603480120b401d01c01e1031078a1020301e40002c1a07903001281c3c50340a241151401034107900d003001d4a90341a00603c010840206449a43c1985401341c001c1e042d410b100600f001100a010160a44402400c80e1003030010002c2022540340c011030710214205841c6809000065607400c0c000000d51 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 804249190 1250 804247940 804247943
    0x80d09060501050423100905101d09030a0c0309080a0c150c050c1903020a030605061f210e120c1603030503070e040612051c03060f0b03042d 62
    0x781454000101890a032050844031403034580d01401c2c5502c405001c1c004444010107100150303441ca040030441d02e4a522600d88500b130a04500400c00d03041401000c00076154141c0e01035124241c03010007c41940100566180d401c0e00d08292002c402c540c42c2c04e803000c0704c0507001b40c5800d2140c1c003103031001c0c046502e124401300d0f09100081e010309201d2044c00c0f0744031604240094400da01c0800b820000c0c1c1811400c07900d2458001e8150044d0545070340c0010031302c49c1c01b58801c0d10200c0c0c6841c00d01000c2c4c9400040d0541c00c1d22507510300400108900c50117003d0b0348203800c400080400a101d01012414030b50841108010003800740e07a0305155210040000350440e00306800e0034824560a0544010002d41460070b40e90180c48850035503460240c2207501080c1800300507000798603140000390700b4000342c0066101a10079030103400c00c01141c103d81d0080fa071690303060f00c0800d0b090840800080c02074803485400c2d00d00301982e142d41da6585040003240910000403000c901e4444100c80080424035103000518203 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 804250440 1250 804249190 804249203
    0x20d060501020f12091c03080f070302120609060d0602401809050a030512090a0803070c0503090a080a020a09060f0603021803070f050a0603020322050a080d09 70
    0x140d10354004a990304444615001d00781d0002c00d00d4220441c10354054a01000010a40c8803140528004031036014035040d0111301040d041c034180314907131540105840d030040362450b003113040510302038000d0010940034140d1030041d0600c5001c690b281c0c071121018140560042c0c41950348404001090003503d0318243c5822440c2400340201d00540300d400500c01c40da04ca2400204031541c140f10143c40b00e40000c0420300c40c81c81d562a19880040d03018801400101e009071038841d152103214240001e911001804825250020443c003c0001c5e1040c0540780c01903024a0000f2400c03441c1c2c50840e107540b083c0088580e01020f2650b002039031304400220442080d100b40c0e007003a01c0a6981007000141d9110340205602c050060a040c041c00c1e2203a07025020140020080e01c0c008a1650080b80c00c005064008207144100410180442d0601e0382ca008014241807034210319624159a8820015400b03000e5043d020504030030301d02c01d00404001f40b50146410140d261f940e81d0429600c0e0004101c07200045401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 804251690 1250 804250440 804250451
    0xa0207050102030903060f090708010c05190201020c0a030513080a0b0402210a030e01051218071202011d031203190501060f0f0f120207030918050606041404060315020d 74
    0x103652000c0151000140040c001740069100c000d2007040815000709a01d080e84121240000e8078142405030f0004c103902902d9496680c0e1142e90002000c001518600e81568010084034840d04800514500501c0c0c00d40361454940c0400400c6600c000c000303900458141c801c80a11000f030000d1306551a00072032085508012111841c2c100500c000c000d00c442c404980c002e030220401190103010b02d186c11101c149401032500701c1403020800540c0c020340300035043c9140140d081c03802d10010081c0ac005000000d01d004070082c0140d00003003002104610222103044800d600d0b00d13240c0c07810052090780320310512200343c50b0319081048082025172030680004250600000141c0035001d8070300240c1e840f00f182d40c1d030706000c4c0c42d0b0314054450010b112030317010030482800c03074008010041d4409001c81d40e110780e440c1840e03141751110340c03002c030a080e4400500203481d100c140a029562201240c048900c0380824400c00d113080b0000034018000ba620140031964000c01c1780d00d1030703011075000317025601c1d450408012 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 804252940 1250 804251690 804251699
    0x608070f09180f061b0e090609100b0d020c0109032304061418040c050409150b0306010f0302090901090516030c021e120a09060f210c0302120c0a0207 66
    0x1d41c0c09040340900600c441c0600d200220f148100220f0320030b03008020104085d18110303540c1d50024005824400020400d5004d4416071801c12515504020b04580c058043e0403e0000500c49020a01c5050200380c800a1851520300450301603078008d10550b0001c0022806909005d0144e03244d46108486441440c22200b60011641050707405840865a4148801549100070700e101d5002681c0c5400d1031a8131041c00d82d5130340c0c503402200740010047e0780b01d6881b18038201c000f505803021000c20102d60810f1280910004041000362540842c0901e0000c0d011038401b18180d0007840340e840f031141c21030000750000c0b41e08811500300b140200d009404188228030a000214200c0380e0f070400586c0180c01828a903145000740c3c8004403407188540301034920040c0036150040c06503010380f4290000c500100e10800c1b4076a0001c0c00088481c41c3e600b441240740c4400c00414144903440a9951451a5141c03003001ca41c074441e5042e2408a18034200d881003506010185410503003211404200600c034011001c03d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 804254190 1250 804252940 804252959
    0x506240702061c0c020705010228081c060602010b011103070b24040f050a05160203040308030c3928020301141014090408070b0a0f0608070f 62
    0x2652010018650500c9456802c20681d80d025121010240740d2020b14104030440c18400d6112060440d0010f0403098501000a82402d42e1540708003461003441c5d4100402588070348074200308503442241d032503891011840c082042d40c12203c0b1046441e00c0d001c404505150154071044840301d00740c071458804c1c1803101505690b031240c54402045d004440700840d843d54090740420300c0003a40b8511b460508030503000031501f12403d41031140a070075114030a0203c090b442d840b40c20340140d0f0b0200d0400880d414040080e549114a1200400c842d5000000504094100c010f03115406540341030840c51091030030842214464607400d04030000124401c00d0500e280004180c120700b18043e0103c02d0101415400d20b000a1070084140c0c1c15548507401c0b1031444c65000c00840c4907201c20320190403464104041c02c1041c120010a440c001c5821505210110700308200b60380002d0b911180e8450309948114803600985581100a440035040240100e1014070122b00401a1030340d48072850746190780d84a518 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 804255440 1250 804254190 804254239
    0xd090902031905040303020d090305040e060603061e130606050c1513030e18010f030c270504020d05030406210501030f02010507060605060313030323070e0f040501090506 75
    0x1c1036440d50110089030a1042d40c01584d4081d0090034010304090710302c6a07000507107001071000c5001503000182480048400c6a503250049800d9407094290f15010000c100d01c0c8010b04620094880241001c0e42c103503440c1d42c441c100d4444921014031602c3e40c3c80300007074000c0d001400c09165500501030b54106501c0c28242251040e520b1080941141c1c0154605a0b2551400142d0f50b40103041c0045042c040241a207446000b4691048000300b2146941010026600d09801080e00808940e007400c1d81d1042980d6045503041d0064000140d40e1140d100003541001114001000b9000102e0009142c07500708021821402c0c45822005c0000c40b04009038049810901004000340c03185690140954442e5001d440c44601c20030001800750340303620010b030f020f41040710a07400300c0c01d010405104240d4140a1640342c800c0b041c00e0001400e0305138580b08880f0400421400400100703000c528900d0303071401d00020102da0007800410240d40c60352010f20250200b280c00314000c00041051a060003241040d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 804256690 1250 804255440 804255451
    0xd1205060f0312090402130f1508010302150c0f0715230f0304231b01020c0f09101208040302090132013623040902031e0d09090203 58
    0xb070040b030b41125210302807913003211006a404c140d0078001e4140d901c500600100203051016401101145040d1501000d110141120030400881030700420061b11130001e0310403c80614a0201d0300c0340008084649400701c40c0c1c411182d81c6c42103d100282680032403011440400c1260798110108644078528a10051540b0702402d150b002002034505014041c0c0246400520900300f50034102c01070500b000104000042008154000401c640861100c2e04800b04034654280081c0080c5101d2000007500c4040c15003c3c98094072040c40003400c500e522400d4080900b44902060480c010a41445065600980070483c090303160600040b8107581c2c4a00d20b200c01051400c808406030481c805402280718003000c40d68140101064100b10688c9030700301c2420383c1c0390340807090314480c41202024960607002e03a000b4865081c080003230041040c020b20b014100d0400903540411400c0891010a10708030280942c92030f0076050041409884d20f011822500464040e602d0304100b40e12000020708078401500c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 804257940 1250 804256690 804256693
    0xf16290703031a12150a1d0c010206100b0702041a0a060c06060b040b0d0903170a0507020c01140403020108100e16031a0d02040b01021203100f0815071b050d1205060f03 74
    0x800c1c542c800c10044254401c116880200707d00e010740c1b0310704e004a050002d01c60001e800c032281070705a950781005951350080307015442460341450100941c1080c1700b8224040d0050392a003a041c8103052581c501c0c500c0c1d8000181c2044160341d82e40d00000e04901c01140c0c1150842d04040c03002928401b0402613409030344054134810700e4080652001001000c0b094011800d10600c035192407607880090424038443e201d0754a001c103007450000d81c000d0525220902d454144240042009071502e80f40003a20300b41c95080c2052401c5840d2402940e1004070300382d010615280040382001824001c983c00b00c40504a5070324244244600d910300c1d512207040b01e440c00c07600100007900110161502c0d4000348101c00041c01130340e5521942d402da400641d40308440c4038540544617a42002600c80c00b2801a000f0a015405042c9000300766500101c1c1c000050000820095110451381d9070600c4031202808a590000464400003100c100280c0f42d55421450501d1035483e0000080b240d060400b0075040b0303600001c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 804259190 1250 804257940 804257953
    0xe090903161b0b07031704050606011409060703030903080c070b040f03110a050106060f081003060e0708100902014a0414090f16290703031a12 63
    0x1d100405480da1014191240286464401d41c1014000c4180300600350200f0300c69074814030303818082c2004407000344404a002e03101c030030400896000300e441904144246084103c0300400340d1203445601075031145a9000c0800103d8030201a00f40c0c0c440030740640300c0d894810304c5690796081c0c18081c0c044c4000142039202a1000540021100700950034054401d0a14456040d4004401444c06102100c01c50b05613540f441c0910441d60000a40f80000c010342c503084a55280c0703030443c4403006005100080109031100702007442690180700040c094070000003100c0c1c005000007038000140c013900d2000d90200ea00442040f0502c07803403804648000548c42c444403448403460240c566490105650ba042c11051610842e0700303a0b4072402000f0402254600300306642c03c058110314100405960b800b403190703210511061280d81b2140814046800c034070300b40c0000600741c85200307101580580e54100e0681c40016080100342c0c140d401405a0f048164080c00e510a244050094034808410802560351002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 804260440 1250 804259190 804259207
    0xf110606040906020f070f05010b0a1211030705102d0512060102010f0e01020304050714030a0b040f060c052a1009061b020304150306060e010e151303030e090903 71
    0x81d003095845034070a4600516103d00000b1100e0751b90442603089481e2268106002c007442001d00407001404000c403600900c5034504101c519410368204002402a0706c560502446070f6014442c94000703002c0075083d45044000c150004081041d0103610303041304205900d11385001045401c1011848000341c03a06480c201c0416100d03121190003d005c18119034842d042d013220f950b40c82c00b40002090b2600f0000d43c4a0500780780990414080750882c4020914580002c042c50b80c002a01e40710080c1c102c405083c20b80c80d207042254050b00c0c1100c0c06804142045416422694068001c0401014002698441c5a4140003009100b50504001704203503002d03c3c14804041483e5108400701441030310000f078031000040019400c10602080340016070804141003040f81d40311314079515050600c0c0340810245090050140004864940040c100600078050700c0260300c444100403c607200320f42065803250601d064041c41840c840c0000c500007141d2145000c01402c0100c02c0600034442d080141d818034808 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 804261690 1250 804260440 804260449
    0x20a0509040525030204180f080706090209040f1a2701150905040b0a1808160c08010b130603080a0e0303040e010b04030c0b0a0f0807110118030f110606 67
    0x80c0050b6050f009400c800d08081e5a03003031559504641e2504110300840c91401044101c80104030242c44a00107005118006000b03001b0958541d54884620b6441d0381c2141001c8004161031507000b50805070501c03d01c4140030100e1594801e06200d00400c0890000f22901d00d1460401a03a8490f07030f40e690b020b0110080c01030001030080d0302c1505400024500c01c07002447d1001d840381c0e880208600d940b07409101c1403140c3c07444002e6102e002584180684c068840211b482e8005c0c0140103402e10348040781d80d55000700340da442d1408494100c4508a02e1070780b04c03038004d8002c040300c40c0f281c2c1c8151f0010f18100400e0032980103282c114bd4001d943d01e070401b0b50043e01a151040b011004540c0360004000200f480003034901c00c18040d01c40461b015496506628142d011001580c000204804e1305100241416a0000c46004070659520344626691034194081da603248000700c01120a50a00ca0b014000041c49078080c0d035514000e44e07500820070440d503010796028400071342d0041981c02000014400c0d081 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 804262940 1250 804261690 804261709
    0x804020928021803060c0426030715020405060d0f051b03010306050c0403020d0b0a0b0a14010c0204020d1107020f0a0608070804170c0a020a0602030f0409091b2402060103020a05 78
    0x164000340065040f2050000317824640d04030307006040c00034003280600084059107a481604407030080309103448200c40c50780f580c0da030040003001400703000194603150030b282c1c0b540c05a8000304001741030781da250101540500c2c060003080c09018081c92030500056543d0001d041c04103031400c00c981400c1e107107900350f4903000c0103000001c1c1007072100e100c20080040103031161003102c8180b5000d20303600042030415440c2071050f58004d030f501922607100f03034005100410314800d0001c000d14090070509400901840441c0280c0150b5208051207403401041070401d03200c0000a000140c8222000c1503a1407100e010850301815038081c050000742c00303000243c0d4450003140029040f0f8010504140c1910b4404000110350340304018055a64000000c1d02e003c50a084042c10040c1c01c060000c0e50820100040e00f900b50f02462044404031906c41003e00144841314114034100c1040000d80c00c1801c1d00c4124004144501090f00e130340c5182c42032052000d480c1301190640c180c0340d008100982d4a4940020014043d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 804264190 1250 804262940 804262957
    0xb06160212120708030108150613020c01091502070501060e0f0402060d0f0911100908121606020a17010b070201121a04050115020706020c0a0b0703020f0d080402092802 74
    0x1c18120340202e464400300207054107500c9100125582d60500b984141445060310000c0000c400160600c001b5580b02403001031040320601c00180c40d41c114075409405011205405005c2000798a0300007d5000703130350000c01c1c689000b60020b22880343d603000900d00700c034812112a141610758038041001850400c00520011566680100342d850040203210111241c1e110201e0380d403c0315980040c0c19007020140520b003c8028208049001d1802c1d03501c5481d116180481c12a00c200082c000017040c8540015001c0309810581c11074452580e840090130f45000030201e40025000d00b400000c42c804a04112141d056041c0e40390f01d0b80b5204c160900c400382600038008000d010030203102c1d42c1d0070b4885104540c020404844484038000030b010002e070030f290054110104540055a80c4503e944444800c4400c44125221165440300c01e400d00f2400c00b600c07401e0f41c840d60300131f60401d2100070f58407000c00c40c06a8021200d920144d02c4244a030022000410b4511412558950400e07155680c1540039102c0368 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 804265440 1250 804264190 804264193
    0x6070807080d0c2c0114120a060501030605030f0c060a03020d020a0c02040e190809010519020102090f0103020a0c02150d0903030516080f0c030a0b06030103150b06160212 75
    0x14005a650304202e4100c0c2102212080e5540002c0034542d90241d1003242d0040c480400740303214500030740000304803010281071505102010001c40e80364905070741120900184a15108150b0404034010350103000680307c0c880c000303030030244081181e20300031603c240044104001012601030100074048645c1240441c001455400c0c010018513026074001013250102c01d594581c40030585104100441d01d048101080380d038400d52040058500d886041c1202c280c100340c42d5620303035111030012241c07032040a00340e5803078800030298031120540540240c91040d4044400c00c07106c2094200440885c0500c030880360005103031003180d01c05400d11b80d40c0c1849240740002900e141c4042c1034142002c1d10340080c0202c00003075440c1d04101c02c02c1d00752143d00c5503041c414a0054003d007840040001684400751100e42c00510000c0400d2550364182d226441407140500a2a1250395030f08152181d02c2d00115045003141c00d02c002851903151150480380c40400e080818511050141c09001401002079807083c002d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 804266690 1250 804265440 804265447
    0x5030a0f021008160305130f1b090608030f0706021b0d1b03080a0c020c1c031106010f1707030515011d061309020301020904020f0c071d070c1a0907062c060708 70
    0x1ca480c0310100c8d00d04e80e000c5c5803802c4661004c01000c035140c2c203c90340950401498180284000180070045491106014180d00c0c0c90340c107942401402485100d640d0548085151200385440d400812880d8060308162600f4680b802c540303881c418070191803280200020304c09030004121604651110b40d881c0c4142c070448a03603402d09400300c2c5030a400041c007041d0800d00072071100101030b40401000011102003020380719551400440344105520343c01000400701c1501c0c40a1082c0c1e10411148009540000440314244810700d00c140001a00b03000c0c1808024018003140e0b100c0d542140d410b805101c0c040c2809d56841180c06140000b0211820201e9165408011000541d91640098550545000d0000d0794810964580d40d207080ca50741d000f940d0060503055a40d440405100d403159103c1124102211030044514114011000c001880300c07802c9001403d1000a100000d000c4060340e9058a0b01110414103809510202d450003035440c040005513201c00c1c8050070268043e10302c461041184609 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 804267940 1250 804266690 804266693
    0xd02450903030106111e0f07060908060106080c0c010501061d040c080114030102041a0c010c090807030809150318190b31060c08060a060507170405030a0f02100816030513 75
    0x8080601e1b1100510b141d100c194210381120701401840001c103120304101505500d000e810715254841442000700303001d2684002001d9403000c0040b5204006070313030020050380d030f1131f41d0025041000040b5030a405a09503080c86280341824401c91100e10855180c0c00c1590703283c241c0c44000c0b03960314851190155001c4c840010180d103801d0042c3c0d01e145c03440ca001350300e40004030401400c459100c007020082008e805d01c1000701d24404101d81058982040c3c0080d0785441c0d800c0844c0604442200e441f0a0060001c204001c1c1120074240030541d00518080c1c0707258903460106240012031080000d400c050503100491140141d91404020118074100c100140c0d040600c000008400d00702c405440850710703000c6010a0360f07807041c121580b050048480d07407031190400e04024654001d00340002c04014089407088100c20f0b43e0025503004010090441e40d81e0050b07032034010094240c40700101c1c0543d60704090240c1460003a0516442003001c4070105d1a003003842c5808402524014001800e0203402908060 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 804269190 1250 804267940 804267973
    0x1b010e030c07030506091f0c020a0206030106030b040e0303100509041103061806010609140105090f100909110708030609100302030d0507030e03060c090d0245090303010611 76
    0xc030480c0c2080034002c0d45143d03081c8103007061001000d10816801402c04800404600c45010a0841c01d030500080d0154400405901e01084590040d501c103d011000198640d89a000301d080803e003554144190300000740d00d1079817404240d40d90003440421000a00c01400e00c0c810055001c2e00458922940c801200040380c148541503484840f100680c05071000403200400496004044515000054a00d000d0011196480009200e8100440043c60310f1260740c4d40100e042c18034000921591400c514241c0140c1200c280e07110f00c09201782044a80794080d905101607801003a0400c401d18907540c2e030301c0c081001e0400024540d00300040a28000b0000d45c80c10000c03c9001174045c0c982075610040ca040c080c1055a110384d910380701f54000d208102444d064141590311401d0265040d24070040700d440091001c20718111100300003008140d000350701d81c900d940c50560703a4101c10400c40305003441400d1005180d0084800d0b016a44c4104010881144110040c803490074400c01030324105101d001880 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 804270440 1250 804269190 804269197
    0x20f04050a09050d0f09060807230a030f09020f1c150515030d0906030e010b0402030a1401060c03080f040311010906050411060903060c0a020f0a12080109060b1b010e03 74
    0x30300816a60190b030303001c02c181000429005650760609589560756134900400303442880c01008100080040864401030260000170019110340440240340ca039240d5032803115400090540c000241454000c5040c41810700c19a0329480e000340198668501e84c9050100303092445080da0310440128140001080916150182160824602050606010454850304490441c80740d00c85e4010b000030340c00242c2c03c4074500e01141c00c00e00340032a0801ca400c84a500500c200c08209410900000410501c90481e90140c5d2001e040d0414551850741c0b00d1108481407040070030000c2c08203000c1c0000c1002442d14403011a07000344680b5054080320102c2c00120b0075035406040403905507403545c0a0000304000780c80009004001030700e40031f00703200c0400c000950302c410142800303086000004940c00088e20900000704181c03148401c5800d510550701d8048008244040d0840002e16008004155443c0e1801150200c44000102904011828a80d800d0209101254000541d6100c0101c180000144045c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 804271690 1250 804270440 804270451
    0x41e0e0106020615150304060b0319210e03060c13030618020906010e131d0a0507031a04030903080a0306170c03060a0903020304260a230a0201090909020f0405 70
    0x83c200508081a0424141d045030105a102d04a00720142c000340e0041410740380c0c00368001001240d80019400400e0515901b1402100d030808224448000e01218500840d008800f1004002030401903420445a24401c000c102e6416000400800c00c000c0b4000064248011b4004824442c2e59a945e10b0310220781580c10b00681f400100406202545408220329500c02000c1c281400ca41d0700e1800000c40b0780c1124902c1d01211991044001084902c15010400308001c050894628035601d08089540303034404d00c800c8071082c1e8100601c03403003650751106490181c3c0c4e06071140754115003180d6031120140c02120390751041669944000800946620004c1c5661702820044d01601501405143c2001030051803440340b98240182500000d6000007160229074001c010410709501036a00c500c140c0100c480050030724811107443c0018450b0000819000e0b100001f1204100c010106d07103c0d89801031004c002e03011450740c0c2c07010080102d5540081c09143c3c4018003296420004100281c2100c030251003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 804272940 1250 804271690 804271693
    0x1120215120126070b16060b0904141e07030303470d02061b070b070317061c060b0111030d06030501060b0f1611030307060516050f041e0e010602 64
    0x4840c41e45802c1035a8624558051101600400c2d0908170441074078882c0000100c00303092902070a80c2440300070f502c2800081c00080000c0030034142402c0024035682d90030403070307001ca0041d001c0c900364800411b06010141c00907003001c2d100303061940e182074000b0004051009c040c551092846400c103c464a900402c286031045100035040200004082e20702400b24154001c410301e00c0b80c0800f59442d035042d50b10b01828044c1894400d1184151181017907100d03070001c1c48030200410710508250700049250304540c544d038030200065440908010805200341e040c610a000303900980404641ca80e0007001c2c03988018181550345401c01c41c00c90b4556401820260b103040d42d01d602c1070041102c2030003060300500b9034031039590402ca1304100c1034000c0d21940401400e052a80380c50441007100c043e030f1911103d04010241d80c1c440303219080c00000f80070100c885070024040d41c0c01036003105000d4030960b491301070003138984c90801d4107000141880e0700c5042540114031201841c00201d000c0e2040c2d40300c2c06080d140d030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 804274190 1250 804272940 804272969
    0x20606010c030e03011b0f020c012f0712020f010801053d0207090507030203061806030a0204020d090c08010509030703031a060a021c09050922081303020f0306011202151201 76
    0xd06c01080c038005801c4000441d00704603090101070380e01c02071240503c07a030344400c48030407601c80000d0172403005407018800c46401541c0c80041e46011207020f441d5194000d603031341d51245401d88011540301209000d03242d44505003900d1512800b03200e00f2980c0034054125000d1941c0a42401032868841d00401680d005a202c0041400090541d002d0f40c2c0d00401e05003030070b5045042c40c8002884202d0b008901080c846680f074000b80f419641048581e1030a500a881159119418039400e4094204544281c1d16610101000078114005110711841000e00d6009142071480a0f5400c4029000203d4801c5c031112000311000791580d9010000d01c80100c0c1c0750001c1c252420311f0181540c8608450300d06809220440b801001561202000298010415080e0849998010107405d03605403102e10301902440e400700c0d45120861700702065000707681c0200d407031080350000340702059a41c00090080c4200000c2030544c99005081501c1410541c6110081c1c082c21f10201405141140d00241d1103e0502013400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 804275440 1250 804274190 804274241
    0x3080d0f0609060f0506070c0f030602191715030a0b0f1803040f09020c19081c1a06160b072f0c090c0c06090105100b040303020606010c030e0301 64
    0x2442508010482e0790801e00070146018814150401d40b03202c0c003401150002124403c100e200701c580005000c1e285400710b021503c0b810528025080881d2450798240341410540d5028000c4904212241181e00c0310b8001e0380e640005298250900104943c06111f00015a400a1400c8406174491694100c0030312003803901e003100d4413101074002e42d03800c840d8000b08803d106070074607480d4003001d640c0c0500740540c0d1002d43c141d806140c40a45000390f13a002442c2d640c60410021128000d0114030700705042c40000c1c83c00b806410003291521480982040b480f10307046070607400d180c0c3c06802000310010000500d0200e0740c44088804404550b1440010a100740721040b010040c401c02c040c184109810b10149440d400c9083e64507a01c2114540c801c01640e400500c00744a2501164040121141901c081c0d0410f0340394a8040e000590760000340e07080180c404104014040d0558040300c0e05a40100996200c0d0001521000c6c1c1c0e2480a40400c100c010f040ca2103074609014203450f04003114030600e0aa0340701e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 804276690 1250 804275440 804275471
    0x2010e1e120711040209010c140d0e06131208040e0103050d080c190315081204090f0b01020d050306040f09030f0825110f010608030d11030c03040f020a03080d 70
    0x504062107010700c014820000801e02c0844100c0c0d6150094030010707642e04070000144c4c5d600c18040801000d03c0201e0881801035500400c1a0b4001c08035a190a000c801da0102001003a000704404441c4840390804100300c50140e0040c800c10b0301e4091401180341c42d80720070072402116400d0300262110f80c0142c032034000c000d0303001d101c4030b80c400c078903002181c201a481209403d41003644c1e40725404041c0c8406030081004110340702c15006101c40070403150fa56404880400c07451700984182d030603040c03400d813071544200302078054800101016809031461000c100c400351942e40000e820b00e5003040c2d41c0c410865240707855102c0d40c64031500a8070380c0300303d6800741c5000a01001c801014000d45040300d14242102254108415902030201c0c2819508941000103c80c5403042d40c0b01104c0e035640c03d0540026201c034011004000e9070400d2802449075014462484002c0d100a031450f200c1c0030301c01c10002d004120384d034002990700c41c030080c817002840b0303030720384400045d0f811130210703508419518580421315000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 804277940 1250 804276690 804276703
    0x22080c060c030c09130e1f0b120a0b0a0213060e2106011a1201030309080d05030408180d050105010e060f030601030f0807080706110a080f150f0102010e1e 68
    0x1841c00c0038914a010203016581307008050301c032406a11252040b541d0324500781c01000030160300000301c2e400c04000011034001c2c203541748142c1800902d0a2002e01e8181450303400b00141c01400da0040c0707100c1d00b00340d0300d203040d62500910080b0159400c1c0045603400da000032070034004003240c0d5521128495a8410801115100e510143d50b002c1e910840b100e221002180543c1114500b410714061281024265022442081c40841c2e44030141c0d0004000c0541000024040d81d80719000c4584100741040c00f640d5030302c025100688402d500b409040b1483d0f106c5c805280584102420740124604145d41d07003400d40c0c0081e04020328028040040080900f0644100004c103c012002029036514503200c84008000c00712002c2d0508a00250b1304003030001d0141120040b5030300241c20400140c4204400c141c0f5007200307003210b00103800000480c4400c011000301c240030301c0740c1031042d560307101c0c4050800070b03550701406049041d5501caa01071511403078240900903178050025907110142e0705207950542800d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 804279190 1250 804277940 804277951
    0x3030c080901090c06030506010210020f0a0905060a05040510121a0907020102130b0f1b01141602152806030c120b1f0302090910051012020922080c06 66
    0x20f00d00122803000c00c0c40307024240308880d09030900250544401c00100d04081620b1350750110740f07000140c40103144041000400b4400705d10b507600d4003016110820094140f165000c03a100103001403005018a2502c040140340180c440c1c1080108e544610b507810042d9824984c1c0300c1350110011307603164921304210040d690b21080c94070007140749c24401c24917200c01d50b0480c094101c18140100d09280b0510300c0a04456506101c020306902003102040a54060148a01036045000c141404540c91040c0c0e9081c03203004298503000703081d090a001011101640004003103081c082ca00d6521006803020004007a03010950060010403441c0c1181842101610f182e40030385600c24000c1c60b404086914803800e2600b184504280d40d40114554614100da8401c0d41c1002c0c0d13000440d0810b10120f40400541c040744c1d0541010140119503500c1031340324500781544078450303500900007a10801440c0c1941d80c80c0e840b400e4a03103160380140148a00050f0b07402c0d000f8080381c0b82400041c0c421307682d100400c58143d214 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 804280440 1250 804279190 804279193
    0x906180706090603050603010204050301020f03100b1303020607030e09010f0323060c07030e030d0c061b0e1507050601060809070b030601020304172e14010e060906010215010303030c0809 82
    0x8910340715004003810442c2c070849040540c2c030ba001c2901581d081d0112001002e00400030b40d210188121400f000350300c1078032182c0104403402da00183c60140c150507201000ca0740b00c110606a4550380074081e260744912411010442c02c151600d2956444221842c06010710380128034120f821881c2c09269200624030fa10444401c00500c0c4007030310400201c0d01d03070050301c6a0380103031a03451300d260a487e00e00e820940c40c2c0d414025440d00460940e44050541403a41c016401440f0780141c1c42c80e42c0741c192a121061000155208070b14107140e0a02d01c5040f5140c200315104103142a04640328941061000c0c0c005500040050081c0444c0540c104850405040340c14095442d41c201180080e5032489240b0603c1040e550301102d06080d40028001c2000004030102000d40e04501c010007003003080b202408e80103240b0302d0140b03044e51610511521a0684125103401602510390400300919440004e1540d8110721032007200703130300c010501e140040c000e40c885c0d2004a4040400310000c0d012400007010324545 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 804281690 1250 804280440 804280453
    0xe010c0e0310090312060605030f07050a0228140f0f030c06060f0d0b07031b09030203030d05130c08030a090909030203070f0606050d0f1203050714160b090618 70
    0x41c0e03000301e02c1d4501c4807003222001030492010318054aa20840b0701070401307540c2c50300300300003541500040110320401102580034503980d201c0000792400d010704260740300142e00c4007007031442030354042c07400300301c03040310000c0940d40250a0380d01e03001b215190780080102908a0b5103141602c00b41044010800c007002c02c0030b035041c451080b224a580e20001810540302d010242010341d52502c40707980e5807040e507030002e00d0380060340303010035014004d0514240791014625803407890031803d074401c0714000103495009000d0f502d072500c01c0740f01d480a060060724008400c81304103114000074521840c0c14008145001c003031522469502000ba0002115502100c840782c2002c0c0000c00007030b40032040340c40c16035000100d072902242034204600140240d400594002113071078818405d101c24140016001c500c6a8801064050088070840944109840c242d0100e8004000700c0140528840034101016207110a00000c64070750300d40c10740d141415034100103550040c07030910400c3caa0350080c00c0c40312240a001400b1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 804282940 1250 804281690 804281717
    0x60b03040b0a020906090d0501092a180e070e1803030c0703110a0b09070503010518030901110a0b041505060f0f04020a0908101e0e07060c11130e010c 66
    0xc1601d0300508000e20300ea4005280c1006a44550a88000b00c001410401c1901c04c2880c0c850f0080c500c2100c10798450080300100c819042c0021910f200c443c504440d0910307820b00d46042448030740007840003004855203c0c0d58116008c6010000c078802000304a15018140c20f0141c4001c41d0300c030660702e41a0300c6070000c00801612141e200f00f1240410350500c8c1c008085e040780e00506051031100c04009111140103814080da0b401b0000e0864140c0d98220000c0085440d80c01c18001103105050000405410521100c1080e6010340095440d21581105803601230301300ea80d0380c40809408440803512919440d505440c104880e1060680c0311a040c1c0344030100c0305204001031018030031014002c0c85140c00150401c6020710419402c401401030f4000c41d440741c041c00442d00041c0c90103c0e942e4071194404400110106202e0007003401c0e600c2c0d1100985501400d026040b5031140d240b100640320004000083e0145072030308181d03940520300d542c4001541c9800424105d0170f41d21044040410404803940010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 804284190 1250 804282940 804282953
    0x3050307110409050d080a11040f0312111c14090a09050a090606080a05060906070c082b1a040213091d0607110610080a0b0c130305030d060b0304 64
    0x891007038010040185044005000a02500d94004000c015025819100d0801500400100c1c02000c100405000030315540c0c051444902a0b03100d20b003050303404442d042020071040490401014040c2c50300004000d030000f0300a191103050030382c031081007a10690f542940c0303a01044018041d0344150106142000c00400660643c020740200500130382d84d000405c2003a1110f0303001c3c002055010b00280401e42e9500070007a1114081681550940258000508901004500b043c401c455035100c0b40039890342611520039942055240349620b4843c042c403018103400740030244804450310103002c51480071403aa840e9640584030329080c02140140b100d800784a0310180004140c0b84c4822001801c920f0100d81e00e010480550741c000b00303e005450603c074590f640303e10500e0383c0500a400b01d440301d40b61044a5018280148038210054014a001000103111081c2007a00089040695070400d100f40d4594404042e455208641f203520000c0d00d22844203213402400004d00701c1c000c038903085180c10348509 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 804285440 1250 804284190 804284197
    0x40b0f07080610030615050301030b13020a1a0d0624091a0702040b36040305070f020a050604060c170306030d140d021303061404030f0c0302100905030406080907030503 74
    0x1d41c8103c06a101c040309162081c1e0051000b05241030004016030060400a816580280000d40b0050303503000000d20010035001c260450503a0151001c10400d280c41941c41c0c1940440c0e0f145203440c5410401e0b491214107902a0301c0140ca80701c01072a000c0c1440c640040b000c950341d200a1824032002c44030402170404041e000380790a86001078456940c0d8070900c0010000c1900c00c0b1241d500c03100031030a07401c070346590526012000080302030b0708107200310080010503101030444000700016030400c2080c002554031800302035105c0c409895901441e0715030000a4154110350001000a260b140d060410f10034101140103001040c4e08004d8910304000c400310b511000c02d2410300d81805468100c05011400760812100f9210038144210f40724603003150104402c1c00c003403006540f02820b0594100ba9520007084043c0600e906849650034100c6650054800c032074402015000e40c01415010f11050149009002090303200d81c001d1580c40b400e100001d04141805031400714146d001c45024400100c001044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 804286690 1250 804285440 804285451
    0x3030302030123370e180c1e030c0915040b0d02130c050409060b070b010902130509090307061103011d043c030f0207060309240e0303040b040b0f0708 66
    0x4a031075010b180c001035000c3d442d140345459421300e0503a000440c0d00c00001e041d4000c5c008603c601d1042c2c1a0b40000f9540ca88030401e800341d000345911030000000003041200881d100c809015107840148240010340c00d0001103540c00910010880400c1c0203203400d100304170000b0404c950300812100590040b410144040b003d1b5034071315940344100410240910181c1d0004c2000d50018003a81e5202c0a0313036141900003a000b2074100c2c020000201d4113114900a90300c0460080e015600400c0c54201002403c800c05082082140402c00030100810824040e280050701e51190060f80c9524103103110000200c0c0030ba04801d558800320a020006030b00388480c05900c0155200c0401c0704000d03001400101d8140c010407250710480c160303507104058214140c0c141c880300c0b5400340d600305541ca80040e41690745080d40140300a013003085d911a501d4400e82c112a1802e240840083d11404c42201140b4640c001e0f6801c0d28000403403000c120070492a500419803104007442440b407a8240268080c00c9824007800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 804287940 1250 804286690 804286729
    0x60e0c04110a05031f0e160311040506030a0b01050c0d1e0801030201021c09180c02070801051003030804060204030b0c070506070e010f030c0e09010603060806090c060a140c0703030302030123 84
    0x3c4116031000000d01c5c08018050265030b040c81400c1048602911708009265071012a00348004a000490a80290303011a6000713070101d45140e0b074501d407400040655a1005e07040c4034040c4201d840469003045400000c200c20788984000c501c3c07141c1c0000c65035070980c0c100401c02c0aa04010700050f40d001c100c03d0b80c404c1210900000c0d401c25064180c848440b1500324002d03ca5485030074a5100c01c1540140d1064112602a078910a0700c030102e403826034800303c0301c200310302071045070410000c0d20865425a005028100040c03d003903c2e50355054010509990008480c82c021032a2030921a050000702e4004810341011150740c011000040c141e544202d1420050654521300004a079018181010348010000d0074070707040b0360f1100c101034010001070050318424030640000515101000810010a01009215600707088440d0011070f000141c04d50360042c0680144451507590404108100145129407070240e203075810200c103200504040c4044110001e2858418015034440e0441c000c5081c0302c194 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 804289190 1250 804287940 804287971
    0x4020405210a05120306090601020a0b16090e07050c0d090e04020d080c1005011a04050d11010918140c1206040507030b030a06050106090605040b0301180603060e0c04110a0503 77
    0x61041c2c1020400c52010b80240690000300548594000045215050480ba0003c0c01e8452074012640c81401c40310040803020305a01242503c601e0700f0401241c00214585012000c1d103030040002e444500361001804110007055090004c10305200e982c1c01e645407450b003060003616103c600341c0c540c04041c10107401031f26401025014041428200d501d110315107030880b4440c00c20400d0080041a091040f400031244444d4403500c450a500110b40840d00c0041082001600b940c5420148003280350030303d414040d178004001200744621400303802100c0d040800250f00003d4486241c0040c200900d4100303800c2040046c030035000740030102c081c3c200740d01765000900d132ba40d03844050380240300842800e64584031b41805601085019080103050341d103255035a07041550f0741d00096403517009500841203e01420f00042c0b04440417041d00e4804003000980c081005581c9444507403c6800814405803642c0100c1e048070b0041c10140640d021031460341400c1031601c0500e560041040c080501140060000072 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 804290440 1250 804289190 804289249
    0xf0606210703080d11130807080a0201051902070e090102120c040617040201141602120a08041a07080403320c0405130c080a060b0301091a0406240f0504020405 70
    0x2c0c1d02c8120800381070005940c4c1c8a01c0c08003241081c07811445480c07600e00c11f0230004900d913000411810401581a1201c600b40a80385548491040d01a40b01d1400c510501800140d038040d03060a440c040c0703101d0360005a841202d02003603512110000d00c01640ca84c0100001c0040c103511144001d0301c2800d034986084a40ca5070b1004942e0101000d84120f005080841e81c07800460302c0c0404012468401c0b207400c0d440a6a0b0a0000e481e0a8220b5010f000c60100340810031081c43c1070900e0039111003031407101c0c52400c0d24030741e900c1d6031541298000381c600410320a0480394000340e07a00d0555aa9100050541200e4040045c0030341c0c40c02e1090586015a440382c0125112010b040a0220007540c01070740b61001c9600d51000796541c2014100a9921a00300301980300182018407544c0445908031a80c0e802d00c0500c0c407a000d0443c00c015100320340302c45e6074440d0f8a008640441d02d001000d000400d6041c02e1500e4103981a11400650300010310481c4104020445503036075504940844d55042280d034101c4640c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 804291690 1250 804290440 804290467
    0x9050d3203041401120603030e0d14030f2104020a1e080d08040b07051207030b221e1514060d0f0606030516090308030604020403050f060621070308 65
    0x29500d180c814800414040741d070b003070052910b404902c002e9032002c954590f03443c03000c000d80e1480e20014000c21100300c0710460340d0030410892018207020785a03102003540b00c9520549150f100d010240c040c81801b181c802c003001182c07004022883d8803082c071047e050402d6000240840090300c034402880e218817190801e41d5401c0242d00380144459000d94882d485044070103010344004890071038142c1a03140018894500900a0320107c200c5900b012420756a41c000070307402040004c028540c89000b169407d40400d8039600804440f4034003420129807017000f226101c8400c000306007001c452604003c602c102c482d4200c1c210208030342c001c0144455107e09080400e031244521a5010304a82c10111f0b504200881500301e04111007455408100a69821103440c5c07858002c4800e400004801120800c0410f05075400f1311780254008100602c1c0554a5840615100c40d58103c40b55a400c0b40080003094a08002c400204c0640c44640720700d01d0040046071600c2d1034490000034000500402c0c040c150812 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 804292940 1250 804291690 804291773
    0x6010e0121200307030c03120e0307030f0209100e040f050f0c011706010e0303030a06080615030a020d170706050906090a05121303061d0705010504050609040f1b080709050d 76
    0x420a2001420300d4980c2003034a82d002648c03000501092800403d03141c2414005100421642c11200c0002000c105a080200365080940320f03d04003096540045051a00200580d00480c403400b0000034603c41c500c3c0c20b60401b14021460300311071b0442030f92042103980103040c800108856900b023450b140e4504c4010303a8600001c4d007035207804d48804410003204070740301d034040010783d081d02c4100d43c115501d0942566008088014a03078041d0171100c95080141042c0c145406154441c2c47e00300c81610b10000344041c40e400840c0e050b81d1441e01c8030203200c1c160200703101c1d02c0d4000400070b0180c1a0006240c9a96580b0108a400c03096030400004903c00100b0103e550500550740c031581c180300c0600d200025141c11500e03116001d0141c0030b0614000344da580144121800c0300e0024140c0760904200008010007071000c10700c2c1d01015601c2d50401400140301b4003a0344c901480503210004241000a4000d00084442d0071090180108141c0c590214809580000f441c50780000070396251585038468854800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 804294190 1250 804292940 804292943
    0xb0306120d080703060b1e0a02010b10050a120b030d140f0d1b0c150e1c02070321050f0f0c0a03080714040b0409020c030c06010e012120030703 63
    0x1da01c00241440e680442001c0c0601c440395020b112054440c81c030049030344110080500803144403d240700c2a03800050240c040f03a800d5000001e02a5144070110301c107404101811000a8070019101001d650041d8a417241c1600009042000c901e410003c2030b0341d4545445000f060050520120003035048210880d0305400740e001c0d0b190780f00c0301b00d0580480a8120035403104034100d00444010b42d56445502d280d540e080e000034409002440c10403408004060b5102288206e0090904070580700144801342d00140c94164000c000b141c0c95401c2049001c0044914900c0216071000241d0815078070034140c41c8003c0c01550500c3d07440c000507041c0c014038842e0440c01100c80c000c000031082810f801c1610302e84141c19544908414038240030821055100b240110001d40c20709000030702030f443e40c5902800c00d00d003004c012240350210165946103040000d03030000205070040c40061084d203111141140001030b8852a6a2800c03c01c2e640d040c1e245101081348540d88615141580c1803a03504101c000c0045 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 804295440 1250 804294190 804294193
    0x2009060d0204030803010512010507021e03040e0c030a0c020307050303040b060604080a110f0a08070b0901021f05070207050d1115160b1006021c05070314030108030703030609060b040b030612 84
    0xb07036540c1c54001d80a400910446124440021240c3c03100c207410f020f81c82c883c240701c0d03010b04203c5402c503098a0714103029041990b420b120500020034080041c05185000320000e880c0790b9101d1410480f01410396090035406401c5400a10420f40000e8000043d240c200c0d60289005685555490100312140203a5005d03001a1040146903818443e00200c1c40c0c0c0f0840c0141c4080510a003003038180942000d031403207954196401110200650088130380a030886043c1481a51141004501c3d08000c5542c108100c02d581c80d902c1050004054041040c41e000340000d46116050301160b45034110a800034914045c01014222511502e0070a10001ca0788100c0b20b80e818400d01a07403600b4030480b00d40e003c40b01c1030801003030300b42c01044481c00010200a039001c610303c2b40d003c0d19110041140c0a4001031340c100d0034041410710b546840c4040300090350182940700003c640340c1045040c001e0940d040d5a100b1040e41d407030400c05000940da000d0845095500300c80c04103549846040110b568801598080f6209 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 804296690 1250 804295440 804295447
    0x1206010509180603060a05090a060b1309050d111f020901030609020a05041d040c170a060612023c1323011a030403080a09051f0f2009060d02 62
    0x200d1250b01c0b540102003e608407085651112800c0040310300544000042e43e026160400000c0d80d030340c00007500d1a00151068941e01d0308105c898084e81d201d480105e4417034010300300301d044050748090b01d0401c00c5544801000758641070030013040c4484085010595864000503111503c0e40240c000400034641480d0466442c0c0768a60000d1094106001d0006d1a90003082d117109811030540c0614080ca400519404080786490043c04000c1403001841425014082940300482e5a85c071440008011442d00710b0100112481006812010310441c0551f507000921603058428040e002602c4214101844145450317030200003d0900e8190794001a0f1541080c0e910038519100d0003800d4030034400301000c1941c5036207891003500325028402003c201800d0520000c2c001c42d20510f102504600075450004010019454650421070307444407080c0c1c00d00b0f08403417040617030030580f2401c0c0815690030000c2003003401c40c8505442c4442a4014581d607808041010246582c805044402031203103800c04568 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 804297940 1250 804296690 804296719
    0x2010e0d0b070f0909110307051605060411040c080403210e1006090605060a020d03051b0a03090c0522022a161d0a0903140f19020d051206010509 64
    0x207030000032000800075503134020028118640c1e000e420241b43e2034940301401e5584500c2e040380e0343c0e08007806010380301051101000200f5814007225000b41e006107100d0b040c003030701181400103485c1481150740c10440c64504002c0801d0b032018a040e2603003d102c42c003c0100d4000c04c0032a01034141c003000d00b038650243c3d901000c9184601e9008204a950402003400700c907540d0001c010072030180d0344011025030031101003015034921a922455104010700403d45c00c1c88002c0c84c10041503000b03032003040301203903035200503a0038009418015001042d080380c010b901100d120302000301958840c90b40c0082c041e0007140302d140010400b04d1001e4171890201701e50b030f0240e11032000250340b80303264005486605030f03088005c12950042c21000c4000c1403006041070150301c9991080c001881d051209604010300d4049502601d000c0340024480044800041900c41d42c1201144040302d4031281050103640c842401000d4158004064a500440f402d500821b19924100142d417503214141d20658080092400400c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 804299190 1250 804297940 804297947
    0x20a08040c05030d020303010b07020a0b03090303150406061407060615181a0906070f06050a0b120102181009030203060a09060c2a0507090504080a080c120402010e0d0b07 75
    0x40c49140906009540c01e90703600141038030b400112400c0030040e001000144030a96100c001004120300c05495051255507075060302c0c0c4a500241d0765100607400010500ca8403070142c0c2500c4210117411101000007034a00b600c050102001c1c0b00c1c5106041c00f01240300c10a00040fa804000105000041c0014280034480014003082809200444070400c0b8900400d14080808809000840485a40d8681610701c0e04200c290382081030100c0e00890000030035400185035010303450090b03000b10307400b0034074103070740410010101c0700c05010b10380f9a807043c019890310346140e0240d00080c01d401c2c1c5050031240a004811540382c80e00f600040d4252003800c0901c0040304503a44203411007402160b0420424801840480d05100400c02e400c41e2907008504550361031900c01015000640b10707000f203c03c460b0380e81444100b600d10480702550700f0b0101081e01c1840c6904050b000340d114083d49030892900d5544441c131441500044d001034100180800c200c14243c50b0644401407041d040a6072524904c3c1000008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 804300440 1250 804299190 804299207
    0x60305060f0a0507020d1b240b0102160b070203070918150c020601090e15040f0209060a032001260108160f0e0a0b060c0c041109031e10020a 62
    0x501054503110010b46000000e20469010396407543c0605042180940c0813214015590100342601d5440d00c0780d1400100340c04c00204654030b50006043c3c0c3c1440d408140300c2211400c1002c03e056401c1a800c12508542880c240e03402d45010102d059190722060001c2845c0ca60079800000b405854101c03a4001c4101c0740c503510071118442c00c20441c80c142b821030305505540122807040056403082c4014813014131640c10913001801400b040b109a6800b000c00110045000e8a06490346101078802405500744000c1e0341e5800380b02960036011451942d03130b41621000c8907030340d448400050b484426410340c3c07107410800541072200540401104081a0500385240b0a218985485c42401e00c0c02981401d00c43e200c5080310041d21445281e5072034a1850f0404041c028070b0300e88200d585010803d4160703103500140c460400d0303080c01130044905140030720084a0919042011880c000c0c400110955800500700c29001e200050302040162034100a914040409180c00711032400481c00c441025403080c2d86 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 804301690 1250 804300440 804300451
    0x305041701060314161211040b0103150f05130b0d0f0303110406170702010b0f01032a0c03020d0e0f06090f04020c33041412030a0212060f1f1206030506 67
    0x283d0300c140c0c0d41c1c07a02c100c480e206c051001005050a5281082986840c0d84284049030060501007001c2502c039004049001c01e1f500240740c0140124400e0005041c1906107000300c15400d0820000604483c1c0000c40c0c01801e800020325404d0b502d0003c00c1014400e8000c452407a1b100d4003c44d45650306da25003c0e00c5d03a058182c111841c12a460002110644140142018540b02a00d075020404a100c0118045c01e491007458564004080f50160288440b1503182030109250741c400300a00780f0791400034100283d0300620400c010041c551581c00340d440250702208410111011590b4105400c0403490601c08580c0e4154400d10218008030000c801003440544a086200c3e1094100c144981042d40100e842061605c220060070000d00065258402c544032031401804907290440504a141b40c0c907403080f80c00c03402494000c0b89015050342d100c48001e4103c41c0031941206814104000318041c041c10003100507008003101060b459141c02034980016580c424001400015141d0904594500d000d0300c8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 804302940 1250 804301690 804301723
    0x2152d0105120106030209181f0b01020706030c120c030b03060712060803040f05060a0531320d02032a0603010f03020f042408060705070305041701060314 68
    0x1d52620300c0406110703000a40c0d03402000c9164607181d08811844403023031500c000015100b0444261041c41d03a0100d29401c502481c0800310380c01d400301000a09040c59035025009160038600c50580440c0c010240b04401c0e0b8100800089071241000220054101804527941500070030041c00102d0782d0001411480300c003220010710105130399940c1299a403142c0d10401c900c07a83c807518144032610341040100080c40e003d1808500300080c078501016a22040750364600c46100e000070001008110b41e50a9005020f4101e4942c1001181072501b0000c0c00038968210100c0645c080d441e52503590b044101e15400d07000741c112000038550b01601c12000402100002252410000919861030301604590585000c89034036614203155500384562031152a088690242c2c03501000051140e609032800e40d0b540c00540c40d113010500d4640749030304024000d0113203001c101c000c0240c00007083e04481183d00312000075104030040a00c2030499401021a0740000f014000d03840a91030000b940002d84580e171108040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 804304190 1250 804302940 804302959
    0xf0303050c04230d02030706230c0606040b0a1706042001021b040603140c040e011a150d06080318100e13090516032102152d0105 57
    0x20001c0301e6010b80e1040c03a400c1000e0880143ca0320304100880070329410b001c0c000903040d81c440e0380001e0070300b481604030b00d0016114205a5140c04804a1064804c5012414040c600b08601303a00035111078004080d02d00658039085c64000350f444141070b140c001c0800d000b0b4410f10000340e10005841d410250780c2034544881858980742071182000e0341c680c038850160010502071092800d0111543d07844541c9540c003660f075500c0000442e0401c0c80e5806404861005000c641d0100002c010450340c029610340303803a80c03400360302c240e140010076a006001d65048070a80010103024106c03a255104441c0880c50382c2e400d00800040c50900000608500d44000810b5055514908240190b00c6590140080052080e01c059013050400c080d040c00c4810500c540820241210340f01c15181101c24060200d5005411904006000d6000c0754241d010384250340498015800340c000941e07410040c440524031503029400b242c00743c0e906002007200d5503948504940401c1a0b4407030381404e0b000900c50140281210b4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 804305440 1250 804304190 804304201
    0x40e0c1f030b0307050f010c030207050d0f02100309240b1c0309141525050c0f061e030c0c0604061407020d090b21090a170a14030a020d090f030305 65
    0x2c04e5000540710082d0400b49520810030045600c180302e82810b4007540110305002c5415141c80c90301c3d030421130043c4000102a904c0c0d106000c000702c464801c200416140001c0d406c001282440181c01804441c4080c41d07000300214085002032400c5e034171066010342904c010140085071301c3c9800803858069110120b110b552100d003e410340850349501070b4860505007102c202d24029402030070f20700a0040f64881c43c1000009031040311050458141d4159201083c8128240703001ca0030140001020755886060840c035092100748160010782c2c07200303010710200000790031029100a84144050740c104659141c142801e05400030090f44101e8400307106031000003044a800019808042405503481c88020340c500300701c490382908201c15080e040307010710740280c1d040f01c4604840e901804900016107421104c03031400395045440d2042d103601c520707402d210b03003055a50440c003440c41c9074080c50042580d982c0d4111540009101d08003410a40914103a000030501c460303e2401013240d8840c1e2030400a03911403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 804306690 1250 804305440 804305443
    0x206061002070914041a04120815131d03070c0b090d0b0f06010f0c110409030519030e250603020307090506072009011a090607080c0307061a0a05040e0c1f030b03 71
    0x1220041c8c4101400ca58120515100700140740d4403140c940e65003590507030070f900014030f90701002c41d01c511410346640041d81151004c4034280007462145000790302d030282c10f542d03c50408446105074403600602240e26486502c0740100c038601561f0041000c4524a0914840000b400d420b0310a01d000950181003000c0752030068040348105c2e0307001640c9248281d80302c01000007404404c54102d041050a100045a02482160380c1000b4220b030f03100440d0140320145075078580304100d80e4102098115044807810121811440801c0da640c501c0e02503641e42c1c80c6070081d41c0d410000e80c440c40c2c20880024601c820b200f500454651030350080c00850f521181610b08014114000f802800c0384507140e084100c50b0402c69600030508010090030355401d0020302c1d01e4142d02c07500302c101034034616080001c0f0201085101e00c102d819000b26013229102c100003031008101d2903010b501420b806641d444034036240040d0300300128454030300000e1141076105104a03c2c455500504070131880428200a4400364a250 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 804307940 1250 804306690 804306743
    0x180b06070c14030c0901090c03091b0501030b060a050307050f2802242403010e0d11010501140d020d120306061b12140d060303170f0601020606100207091404 69
    0x1300104401c0d607a03402c10b19804002d04924000c071062564902d00040003a03211800c1c448025428142e0700e40051a000000d0155042c0c49020f44c41020f08120b00314030ba507002000e0340d80041042c608192218040107443d0040e200f0b540c05c0a000c03e06d480c4407010364200500c04140040c0303540d42035442c0d1003803c01e11400b030300307604190040104407820b00091642d032034a00d1200880e0718042081c03100700d105102290031100341186840e4190041c1c451005816041700500b040c0e803004000030441980740010360540e085a450720700e44a00b0400301390000703556403002c07a40b804942001c010880341040000c09002007481c1d104520110f0500a110340d800310700c2c1252070a40ca80c000c0c0000c22840311b505401c403800501006906c81d00c003024064182c1820b001e108060265109454256002724802148440c40e0801080c92074000000001c1081ca43d0380801c0c42d41d001641642e20100108010324141d0400c407458000b04207141c070700810b001d8860300001c03070700d801513000740c142d01d03c0351001098074080c004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 804309190 1250 804307940 804307963
    0x20109020a140103020f1227030d090c03150b030d0504031707020a03080a03020403111c140102041d1509090d0c05070302041803020c09010f180b06070c1403 69
    0x7008408001c201d000084007012014140b40051600003080900316007a041090131071240c1c070000040210010003941e05aa036140244004040c1d1060388009540d01e101d00846082d40d1600c5050910030007601824903030185034040c1c014460340041400711001001680002c91092140040080b9079500880032141500d40002a5810a1b803080c034080c22158070000049822100159002000c10107a601510380c0c000c1c40e0360056130780d40c0f46080804940029000051103000234020230b003219142c3c030300d081d030f150342d4841c08000c80c2e08625016940240143d40c4084040001a0509221440101496440340144030610704598a6080034046501400c54480c001580462599058a8003843e504800c60344600b003150b030450b071203501090586011000250312002c1ca502c6050801d41c05000c16600d05078150303144a401d600d88007c41d400f50741140315889011400c116036207200d02807034226032881c030b4003d00300c2a6a5089490050701d8001d040c030030300889180e403040c004001c4c031b00802c0146044 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 804310440 1250 804309190 804309199
    0xf0f0b012114160b0301080705042c0a14012307080f18071d09060c0d09020a080613050d0906021c020a0507140f01030603021008090a1407060f02010902 67
    0x140c1c25a841104034841503010200742d108100c1042c2c00800e80640100241c9640c0040548a500d0104510315202203500554419030500c244164030081c3e5040085c40304135410f607001124000f1400c0141045000303240602242030500c071070070840c24150480e1442504580d458070100c4410780c0c4420743c02c0415680400003410000104a09040d42040c25800c00f400821100c2c1c1c00b03084002c1c0d2482c01106500075010050b030b1000d2a40d5508225100c2c56020308010064041807a200da440f080612442d044005420747c1c441044013592184041c03c1c0c090205d85049526038100118004181c403400e1380101d406105440601c2110b43c030841001d0119011900105901e0082481103280244594650310461007103400120104000700403500003010124200c0144680c1c41e0705001c4a40c400c2194117060504088007040140c036083e9000140505618041080d9210034040901302400414050048031054809000a034004500503044a01d1501d035245a203943c480b06a003a90070164002e50310 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 804311690 1250 804310440 804310499
    0x911040608340e01050c07051302091302040806090d0903030509123c190f0c0308250201051c1506090302030f031606020a03090f0f0b01 60
    0xd40d001c0c1ca206604110402d1000036400b042070320303402121268400030100b9030390803031102282d581c211104a0b0801c0d02071030018540110490340503a18042c920850f80a41c030118100c918180242d4196140b01c0d400401340350080d901c1c25038840c041d4200d0f0155900e60700459020450700400040d028030480256280c508105107107031402d8596420002c800758010806c40c000f0001c864091252010101454050103041030000014085c0c0202c00400d0300031110420b516040044c00014504102d41200c40310b406000303a10b0314080f1030408006400030844000301e2808010020914007801a92411070415108078480710b5007054040e2a210001e404038804000c0502196410700300280c10442d406400300d02c94074400414280c48400d64402d10014001c00030510851809000b540341540d003100c0111b052910761225080380080e566001028a0740c00548602101c0c002d40010030150f800c5a1b244503070825900b0048440d144181d002c980500c003420003c075030b03141000310072481441c44090311101c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 804312940 1250 804311690 804311699
    0x220e13080309030d141b0f0412140706080f0906010303050a030b03070e15120f030a050c100603080711010f120e07080d09030c08193810091104 63
    0x34150710191404030326001c20403c900c404441c6000740700304800515101c144924110a140402d013a1141406600c1c400810244111a0504040d1825201c1303080000703010810b41d1500828112952005400390b0080d4500000c100d03030009009481030040c120181c0b11681d036080705030307115103003400300801080f024401180120720075032201a1000c0c000e01190f00e40d42e21910030340d0b40390504441000c44600c12050400027420f0011184107241c0c96000100b50b400c4e0003002e00d0b92030b40201040c40d030401034085407140f04200d00300040c08500d20380c22410041541c49041007942e6600c125002c0c0d40780d00054011010307035407040004403c001e45070380c0c5245280c0407034401040602006000042c8a2080310380c04980704509018025200340551a6161414607501e001ca0070f1500c6a0b000404070b0700316224140602c02900b108516080c2d000a04040c0746482410982d83e52001c82040320001c0800d850b16071550400149103030140058003284038105a031807140e0b03010b035410410f100311140001d100030003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 804314190 1250 804312940 804312953
    0x7050408101e060902211e04020a330c0b010302010e0402040906090f051003080a125109020a0c02060c03030714030c22050303220e13 59
    0xd0300d00554210302100d001c02c95012809480154100d0321180340c3c00549400000a411175204c111091240101c2142c644080404c29105111000080c007a07581c8001408560b900311058014002d02e407110410a07190070a8074910707440744100c0e900c20720380386101c942029010b041c489088503800305030302c909030382154011150341d40135040c400d420640030b10020807480da1500410016004440000410400790400403060300d82c080c1c4044892003c0b28000d102045882c012100040050b0500100a64a01d400c21000b4240a40c01017000d680c4280e003541000040104020340d12502d031810a144130801011708140d00244052080c20000390070304000c00b00321a00034069080d11800c11000c42d1303026402140c0b0a80c491a5041f0181c4c01c0001000780460b0498134000d40929011410760071458109004401032091703d0905100b071400a418a00304143e50341880301800010341502d0700c40700141110316545c01c1d24441d4011404600402003010700340200510f2191400b40c015a0f51181070780c4604 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 804315440 1250 804314190 804314201
    0x1140316050c030403110a0b09450a0c1803030c0203030702061209060f0412030f0605130f05061c0206130e040b0603010f09261b0102040503060705040810 68
    0x80080c401c0622140981d01401c0c00134000850150444d118109189020008035082503040050210001e0040304c030703681c03515a104d600c1e255001c55568a8180d0080c0707000200004004c0c0486811420340401e00e030100920f498034000d044041c010302540c080250159950756050250904035a40c8801c01c0021034031038113032848490300181c2070f203241c4040c2d0b802086495102840c00340310705071b9407000d01c101ca100c02c201c0b030760f44008074403030101c2c00d0b0a0560310314807848081c07801c1004064031860783c801c0c0206aa48010000d100007418420045010002c0201410f07011290b07250301490312000a0882c106941118280649008444580301069080042c65001202d5200424010000104000328007445090003180919013019951400030200360039900f4a0a070301d4105824004500002071686131a40320002010340d0080040031044840e450742c1c003500c01e400b14210401c4901c0120008103500030025200d003079095850a69400c24141c441c0d00c80d034451840c0641c403000c19604280f0255000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 804316546 1106 804315440 804315481
    0x609100504030e040b0613081c0c02060301050d03050c01020c0106030c060e18060102031c020a090e1e150d03020708070f0b030f1b04031b05011403 65
    0x1400034403c650f8441c060340d00c0e481501400da656000342d90380e0034104160507850319501c3c034105545428909206035080082c40d050b100031403180d055894110b8000c3c098034551b901e000103119140741c0d8500d040d0208507050010107003500c801c0c001003e01001502c00422100d0860820410303541240e40300c0d4040c00001d0320149620303101c164503400030198a030061215540d0b4000180d09510400300303c1003004110051808407009198094052007003296103211880381c940c024088048030540d41b031119103052485100c441006040d02c1036001c0e5290800c0c03071204843c400403035000e42340090102c0143c0c100d100c041c4a41c1508001441c01000614103c1d48a1450421100d44500c4003900e103030014500131000030551904c03045c1055884902c100c0e2103603141e41c3c1e03040541c2d044a80301d041401c071a6009500003102d6200381c12203094001401c404070f2450f15621b007001100110940c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 804136690 804316546 := by
  have h0 := BRFrame.cov_init 804136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 804136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 804136690 ≤ n) (h2 : n < 804316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
