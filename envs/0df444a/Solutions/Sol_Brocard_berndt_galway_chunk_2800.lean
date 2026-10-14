-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2800
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:46:46.663294+00:00
-- url     : https://prove2.me/submissions/32665364-f777-4d09-a7c2-026b1509e8a8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 503417266 ≤ n < 503597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 503418516 1250 503417266 503417281
    0xd1101030e0703020a0b070c080f010e060702150408160b04030806030c01051303060213080d030f0606081905060103180b370f0b04020a03142404020906160b 69
    0x703035000901411000706a0310f890350700014403000e181e109490754103e0000310350040c4504a607440300035005100c201c030610044403d40350b00825481078600c0c007a009080104400501c0803034001403c99600901d05100d0320340d921001ca19038440001910705c2c03258280040e000502c0c146269128034046c0d15200c0d1305180642c10306007400c4610071068104881041140d480032030303e00c00300c1d050307031b410550041e15503e044107a103548180580100c0c0317043c801c02c085518420760581010103a1070820340184100740e59211709442102c0140d07020404546040b214021500c0240d00c200e51185052401264105800d4940403103858454000d6417000d200104101f54802d43c01651039140c0040c8080c908484034024801c0c40307a640f030056031129580c940c0560740200300107401c1080500c1c4001c2c421503881c2044040070f401010f102444800c4884e000700001c2c507071922040a9040c3c00d00844540c1c0401e00d1010411000350300a0000581c0002c1c01d1140260031301740c02c0d203000f591b14421211703c1c038075060548 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 503419766 1250 503418516 503418521
    0x2060a1e1508100606020303040f032d0905010f2c06130f060507020a060c031e020c010e0a120f0c0905091b09010614130305010e0102130b04030c0e1003020d110103 72
    0x10007840031400c001042100031b81c0001101e0f40322342c00020f505404801803504491440607045100c482503501c90302c60380f121038003007188403000080307459020b900b581d07410064a445150025031004201c007000140d421194002d40c0015551b0240448008440818006202a0022002e601d1144050542801140c0d40100700401418040c1005030420540d076000480d0780e00380d40107200c20003280e0b03500e403410140242044503000310100c036002419440c10310025550007008622a00089a40c140043e07141002030700340007178a00500e20022140280c1e1034030300031030844010848080b0043e80c0002902c41c2c140c4943c03800b03503040c00b014001c1c1035080b40c451a825000710506d580b10f031807098010404e0f55081600042c3d0584c040d515a500c803010b01e0b180d1011181182d20146c010b500b0200400034004041d0b00414a40d02c070484414101603c5040d041214012400b005001030310025080c042c0c40c05114803240e01c800d2207819100c0300d503143d0b40031400c0078040c0c0504858034403848680028035a01030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 503421016 1250 503419766 503419783
    0x31e0901140130080921060f0403050a030c0504030516080d080f04060509030d0f1b140405151306020109020109080615061827010608010602060a1e1508 67
    0x503201098040050f14a00000d0800750743ca00d41e80e01014018002c00c01260140c81c840d0380c1c010003540c1610540d1a0900b889102d8000a41c601d020303510018042040942005024540640c1d50034202106640d06400038540c00e25988180711007440004001882040640d050340404000c140d07030185000c61a0386005180c0e8003140c1844084810010211005143c56603c241c01500110f26038070751070171443c11885514428501c0905008101452038240d40003195001710500f00c0011704040718030112001c42c00010542d00000c3d08100801c058580300800c1900c1510301c03140c042c82d000c040c500c030201e100001e60001000d80d45601c03400c015580c001e15401c00601604024042c68500514603a004164440680340f00c0d8401084016030040400010071380004050301001c85c030500301200704890541000012141204100082892072143c1c440394100c0b0299001400c80c4c0c0c03503050645000d45003008002d650140000800712514a007401001c09800b003503540420003c2c03d00314800d0400c0001d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 503422266 1250 503421016 503421029
    0xc0c0105090d02100917070c03030e030c0f2b0606090506040b0102100f0617060a0f02091c0f120302130512071a1303030f0305010f031502031e09011401 67
    0x602c1c14141007600031440343c201d01c820801c0001c0420203480c0c48001c201103080303205c544030400f0584008000041000d40180c0717020b61150040c000c40c5070105680c80d11205d04064111441c440ca28807182840481a240384414403041403840c07401c2c07a0b120300c450203400002d9941d0341d110801088214440c1c072495400080a840511158103e100040d50340d481c0c011040c01c90591f200001032140d10190b00c1440a0141044520040c480b405001666280c0a841c0c440c5240d10700401d829440b100d92003101c1c0c4084c4080c10008000d1444035000b40c410901c0031003035603030385d0b00d003c6580c0020b10200b5a41c01c20307150a031070060f01c0341d40001080d40c07081c2168010034080c5400b0389216580000000b40034080310381c10304800c1c08059054104c0708807070281c9029070034032400403203001c001c0540101c000040c40d8100d0703400b0801a81d84102c2c5610002640c40064440c1c040714916824104a42d00156840b45c0704958a08004040c80340450f42c1e00d07c00c90b1038803610f9545110502c034008101201600410a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 503423516 1250 503422266 503422273
    0xf0705101803140a090510053610170f09060709241814130603030e2107030803010f0807300f11040506030a0b07030b03010b06030c0c010509 62
    0x3000e0b80c1c05841c2c19070182003000d0440012a00340015032141d11000068a005841d1210785001c400014100380c000f030805a6881030340b00d00d10148003061450f80072080031854204040e140c03d880070f214901400940303038010081c3c40545041c01c100822201c90048900c0048080c070752400c403140c28101100600044200020081c04000e2807070002c40f149a031642d00303201c1129020341c0113400e07900142058040380400e0340c00c140006400d440110030145840e01640d114031061800e80a02c001c484040c00000c2c085503000510b94006d007091404180359801981d040300c11100c4d050380481c44c0104070b038003c4922400003c014400901c030035a010008105003002400b03924240405a01c503101460010b1598a01c0c0012482c05a00043c40ba00002d079005980c0150751502810044828104205007034011402c000100b100ca0900141c6003c0f030580006001c8050303143e4050840280c040c1030320107a0306640361038180c000d0f41c2d00d0304003d500406c000c02e07199a450b9517140c9050b09407500105403200079003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 503424766 1250 503423516 503423561
    0xb01021e1516022802130b01020f0d1b0201110109060902040c0c0c050f0a1a07031b0803040311070b0f0702030601090b0612191a0f041e0f020f070510 66
    0x3d80005881828200101e800c010811500c02040800009200060343c403006104030201d10b070007154040031802c002030f403e0701ea18000400e04035682c4c5900c0e0070f00c1c50019400c024032403224465407a040d02d00d10300c14540100349501b007012541c250341c4400c20a0b90015580c00c003072021442c280c490000305510030300780390038106c2854441d02002c80481c402c0d44e004006042220390b8903900d2403c2907024105a640e10010481c03c0340b400b04203500100e84c228041001d0280030640010004031031612103500101261450f41c0d169030480b401d1107503441c6d081e5a03104188000c113000d20b90710080c0c8030005400c04001d89518860041516004040e07000001c1146003d40c898083e8680d28101c034a1942501140c80742070301c50b10055896041d50054400003585011040c403d80700700c41d030107001c1c0c402084070510014114002044101c459001054038188254200c100c48006940c200380d030820000d031f03001406c1600e049850825030f0b0060101311940e401c91105154a500d141c03094200044038442c0080105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 503426016 1250 503424766 503424811
    0x61903060c180b0d09020d02030f16050d0803130203010e0303070e0915090609150d030e0102010c2c06070c0e0603060a05040807030516050a060e011406130b01021e15 73
    0x500c204030841d03e00c3c584861005086d51540b5400001c0e8941c068211202c0b036140340350f859190500303500e142c111141201c000140d94076241b8580f000280e0080c00795861611001841c001c3c01c400c402040742c05540740e1a402003540010302c003551040e1130a458548040e0078042c100a5210001401200300f120030002015440e22104402c5600c01070544401820751681c010914144502803501a805030001011404141d800703c90074014000a03002803000540751841aa164001680d00f581008410384a00400b0418041900c4d801c44015003418034014040d203031a000102c480e0465030700780b070002c4144030341402c00f0030807154010983c910401042c01c042e610381841d8403600070701070101700380420f04401e85248120b100841c5640842160280c400383d1402070082c146a02150340b6075440d005240d43e103030101028003841103c004080100e1108055603020003444a1b001c0a8118400c0203001203079088040c0003114000c003404024540d200880e540100300d00d5000b41980212600600280b694 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 503427266 1250 503426016 503426039
    0xa051f0e0c0a0c0b010602030414010f170c0d020d0e07080d080c0d0b0402120a0f1806020d062610061d0a0b060f030411060c0604030503061903060c18 66
    0x5440200d90a946421002007114aa1183c51000d0034504201c0000a0403e400000402c100c0c1c92503079100039960321846c01920001c2d4a04154008a0011801c0c010352302240c5464517486000c41035801e0401401034544401ca800407400c42480541e68070100c0302d400420450038004007071020080c0081007a1020013491400041c2c050060b05501140d05a50100e990708100121440a4801c5484400b14043c040341e5450076120300c91074902d02025190440070350701544c4020141034000c044111482d0341e5000095116496202070540c0d9543c010802014070741c018007064940d0310b415400110040c00030360a00c0944011007040500d05a0100881c01041c40105048842d8512409a5541d00c0c140741c0e01820382000d1065104a00154180404902070003940c01203006000301c1016525036018403046204032126040c00c1c0d0b100c1000200085e1246000716400400a0030541d40c050b40040750f194002d946400417540e03e500e45c685120606e40c00320700007141c0c0c40c01d400034803d101e241042d10b464 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 503428516 1250 503427266 503427271
    0x31401020408150603011d0c0a080d0905120f121e091c0201020a08040605040f0e04051e1903210603080d09020d0b01090c080106020d0e011b0b0a051f0e 67
    0x3c0d0141032000036125942984641881e09404140708805920f02c106036407a40202d940b181d114004000300420003080c002601c0c3c80c15129510750103441030501007008024000107115208611421024031003103002444680c4003e051484000d8079040280160340d90078441c1e054840090310203000c2004a5959140e0388013103d45060258013a892a6000403400e041e20510040d00c0c070200041c00084807030307110008008070790300c80c86008000341d124244009501820b460140142c2e001c40003011070314a942e220445400c5054040320b0800314008403401040c2c001220582c046400b01043c50781e510004080804000340700003003001280e040d5034a03d066802040684004941ea80407180c04541322003000080007900b140189881c1c3d0b0307480300d1801c0078000c1c9090341c0000488410002a48070b00003c1e80b1000b040c282d0301c91000311171500c001120013000d404242c42d45040400c510a000c28244001140258545880419103181c0788000152804a0b071007000c08503901c40301d04000481c42d0503001074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 503429766 1250 503428516 503428543
    0x20a0512240f0301091a15060c06010506090a09060b0315010f17071403190605011403160c0b090106050103050c0c2a0a060908010612050a0b0604180309031401020408 73
    0x604030b5050302003130040c80f11a07001085405c040340c1d00b950078046030301020311581d000c82c2e00c3d03044041850188400c0f03016880803200389511200052090389400c20182883c100b000d48100c10540d543c524240c19580e40e580600c1c0a2107000003030080c03c00c402d003840c8855240a00f44009000d550400050a041504491105101001d4046251188142c0c0304006e05240c4485482e1a4140680480c0310300040491004903203150000000712940503c062900520014a0250440c0c0c2c40d8410424100190311031201000a125a903200080c0320107040c0b8001c2a402e400019058100f4001608541c03007e08015141e0405002090392150001075080c00048041c040c0703100d08448800c65481c08082c15442d6501c16000e00c1c022480d158001c1004049448600091028030f648426017141c0340c5075402d01030320366004081580c01040c0301043c0282c0058019000140240b0040071420075000001c0044001441200c07040040c0010003240004002081000b18645881c18034416a036400c1a0f1504 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 503431016 1250 503429766 503429779
    0x1b020907080a18031107060201060602120706020f0a050d1a030c040b0a12050d0215060a060507050a0602030901020d06050306060306010e1e0a0501051002011104210204020a051224 79
    0x15810803015000f510044150b100c04030050b054034a070140000f10000e000072001e225100f00051800d1050051804803034107500680b9000034101d0800e04640d008007800d80c0d03400c0d020813001200700505c0004020460383c070750303550351501c1e070014992045c4d400405c00343d0940b88002d000c04040c3d64001c5250000b16400702c500003084030b01100071400c8070099500500075039550023900014448c000c49c10042075101c503401d46591740002040840014029143c130ba4026030f44442c00d000650041000f415924058003c07100184240d0b5141c400741d900c22102ca181594002c0703002180322407940120409814201c003d403000d450080d012a542e0b1605100e800d40c810364082c0403804003d000c1c496910122300c070034190250381c901030290702d0144c2000e2040c02e000d8040d844c1e104100d5407040c41943e80c0c3d442c40502a625044c80d0042c191400040e40021180348019040740c900181d0b21480282401074454036902d440b40e000412003181354000500007990074010700c10044000f10590741440c0c4000003152034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 503432266 1250 503431016 503431021
    0x31a0607020d021e100903031e11060c1803071d190e01021e0702010804031101151811040b0702060a0e0913020907140f07020609090a09031b02090708 66
    0x2c1e0401c180b00e002a4003c54a0901221481c1140d0002d0701660000d40d07003200b8401103034008448100ca40e1001a00040d0b80100340039a9400822410f128441545001ca40840344618039608100c0d080c0c842d92a403030400207020b0000e03000c03200c1c290b401d0340003100944035040c0f0b4031600011030307000155542d1526501100050990445800c84100f0a4094a080116083c01c3c078880b8000d50003a5500c884c007121b46904142e151500c2000c84036030a50607501c0410945607507405980e403c48900d41503066548520800c1d10781c0344008600360003420300c0131088544040c403c914104413164202c0c0c100d0021ba04000510079142071a04a4a20b9941036918a58800d25103408071601e00000a1455000c1c004d041401540f054084c40d540095008441d84501a111440140c9510901030a056003c04060090901140b9041d001d04550b07070014006500d01a07007100044c0e0350080c2150003184140e0b80340c030f04000345540462a4908008602078240c200c81254002500081c8000e00500411601400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 503433516 1250 503432266 503432269
    0x140403031b081b070f0c321002071d0411010c02031903021f0203090f030a0f2a05060a06080c0a03150b06040f1d070c0305031807090e010b01031a060702 67
    0x131502000c1d0071031030000080f1401c1c5400300380b140c0701348070b041100303507140003d0001c0c0b40c0f07070819214507442d480311603500e81100001880310700341005408009500171101b0015011207403a0220107103615204945100b4a460326160001d8201c0c41819810082d50108440040e2000504000160b0a820b080f5020705028078080b460040490448003140084031030400c9000300c181c000d9030040290b0410399040c2481ca82c2420f03034a0040d6199400041d4400f2a804919805004a00c40c1e8220b144008000c0c2000d0b02200780d40303444480401c80c2c640e8814010404114994815100078005034006410111314031130018039446030340e0101a00d1441e68a03090325580c910ba40c040c86080b14007400d081c2c3c0b035641e161000c0642d90340d00c1c828000c8030008805885101444a0301c4c2500c1b0300f038191241b5500e2001038030129482e8100800603056404195800c010900041050038000c05001c1004641c201d0882da40c5130030f4138141c031052070505050041200702c0440c410410301e94040300740c17a45074490030b6500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 503434766 1250 503433516 503433571
    0x8101d06010b1810090e090111180301020f1204021f090605030a0b040e03040801110c06070c0807050304030b061f0206012102040203150103051605030408090103020706140403031b08 80
    0x802c1c02d0b074403403004460140c0030750704500b0f44000c90b5100400c0e18035550312600071602707070380500750380c0d0b070001004201c501901070007038141d19036120014000504084148010714900c1e4015012001d018400710108000c503c0e00600e2601045000030004086101d0303140b02800301c1e82280500c0d4140b04000c40001e40c207800ca644040c00d0020000c00510108501d0344007581c49600c0340c05018015400e101400b4045500c02c01256002c800110041c40140e84465040ba2030014600044910400400c149000304c0d2041002d40060f600130030340c00e41035003080c108002d000000090980c3c00503107514524200a500402c429044840706a00241d42c14039904a030062082e8042d0300a500074804000c7c48130085208220612424080c0c80c01c0186441e0080a03811a400340c2005c60001102000014002003a20015101070f410604005d81058115951a4103540700c2003546000d206210f0204802c0c5a0f040c000c0001104030b041d6001c810100040008103031210090445c401c000c80c0800418000140c130 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 503436016 1250 503434766 503434807
    0x1205010501081f0209010e100f1e0210020f040506030c0408010b010c02030a0f030e2806020a0b0a230c07020306062704081308070305160b0d09050703060608101d06010b 74
    0x3085c0c5900d0b6003195001524000000d011000007030080c6032422060402d89202b0505859244c0003081c2c04804038160601035405203100c0c210080e0140400521030300e81c0406140035509001033302da100c900700504542100d06410003d410030040c2030814000d46c81c00b0954000785500b200310040e002c6c0c1d803410140d603140c070304255164000725102ca814a0b030241940006400c4c0e149042404580c560340d4a04990344c850880c4082d02d00c4c0c0d100008900c10200c16406018241c3d1501c107060005030800c11030903c090340866840105800003d0850110300c1c0a07c5455880300c030840d0f40100c1c00c80e1507214100111140784400754985005004a010310049070203882c40d29090a021810841e00d444921313845101511040700c9512070b1aa1030540703ca003510311441074a40c100c0385e060421094113100070141050b0700303003910030f80203450002c00800c10500400000d4003000008004442e03008010300308950f0028071001c050305008481720003004003c950641110202c424168541c02c0d94880d69000115a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 503437266 1250 503436016 503436019
    0x20304020d020d320c030706021c090f0b0406020c0904120e1201050a0c09090203190b060903060108060712020708120c0412050a061d0616090f1205010501081f0209010e 74
    0x31030110040400d1300b8140024066005420340d41000d911034181039035541036000b0080940c00a075104003004030701410090640d640380c0750008440707541e045c00044800003030300000c0b41104002000e200d00f54040146c081c03100015030b0304c9050f03403a01e6200c2d800300464400303070403041040c1c810800c0c0442d59848a219410400038000b00154104241c01c0d00080c0709d00802c01c008106040381c0010b546d0002e109884c855599002100401d40201c80c82c03100510002c1001e942c4001c0038001502592410045a4060105c3c10010030f054100b0030805854800114804000385004000e40d60004641200350350740c0382500510b0801d15140c42c1c001c90103d00454220708929104100c40b001030101c009680e9840c14001c803020001e407441825442d151201000e0b01481c50760210000c1808022076107a030615840852030100300b00364440a0460714114280d0000e07400000242c003d00511200303114650040030a0001020f039078800700600384404c01c14111198509901040e96440750340940110b40342c3e100c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 503438516 1250 503437266 503437313
    0x52701180905041109040c030201211b02011107050703022e030b0f0108071b151503050111070309060318080327061003240903050c060a020304020d020d 67
    0xc40d00e845000a0100b203c099901c22014074000509040c1441214040c60300300300c101d01c080c0d0440d001542d0a4800001141603498100b851040d5489107210342d00042d408006005a1941c4c4030304000d0948800c0c240742411020200000d000140d000980d8204032603040c2da04200c80ca0005802c4c001c0c2a004109407100520a41c503605295079169000702d841d03010455115010821640044401c04002c0340d80c41c000c203000c1105280203c480e40d002032006481480500c0031140011420750a1310300403030020800003000581441089828007603000d5140300c500702542082480d0700c0041030500c49200317800a0503a00c50000880f5000c45401c10403051700310000d0355032810070f41020f080d140020030480c42025055151010808000310741d25014126501000c414142540c4400700d1b120440003c0281030031202029406031041c0c0d00540308040e000703840321741e2070b10f80c0c0039005420032200500c40200d00388104208401aa40c120761035900350740580350f84648904a01e4102c81a000b03a1812100565 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 503439766 1250 503438516 503438519
    0x80a110c0304090c080105090406050a0905030409060e0f0c1b03130b0d0b0f2206230a0617040f020d061a0310050f0414071505040e0705270118 63
    0x2031001009000316440028100a03059004204452280086c00707a180c0c0f2035401d402180c0818403607085640c014040a100045074042662071500d1903001c0e605c0080059200c0300100f04c031400b600240c41e800001c041e03500300e5618040c1414209c80c894030340941e50f5038458103141813031600f08000740c8640c52100400304a07031070388444048020f034100b00d0102c100b042c01d041e120415418404044810300070003030f0000540031003180445004144411580100c2c40c2c0c0d82a000980200340d10f5040c44400c030458401401d03080c0042030005000958018000b4014501c13452401d400002400303941c41500300c20b03a45800c2d103041c030016088034001d0304058080750620f14160480751903800300c845005000c07401c441429548606280c291142200c01d044280f1202c3e001902146082c552041a20180c0003a10340e90b50f01ea55410b01480d5081c003801c80068070106080c05245a07040c1c0c0c054202245041460800040e0403801128500c010740c01950701d50b0000c81d03903500764002c000380080344040822521031513 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 503441016 1250 503439766 503439787
    0x7020f0d0e1c02010903171204060c172208121603060f0302180c0906040b0d0513020907141c0f060e01030f0f020303070210050702010f180303080a11 66
    0x904881061042c050028075102456030341d00280c401030b034103031181d444142ca5030700c41003600e1148031007081403c01c0c02c00c002800142141c4029100d64440c0d42c1c00640c095101d44000c0803902c0322000c02c810b403002134050205400308801050401000c0065181044500c1e01d0420094001e01007840e0b441c1c540d03001403043c4441e0314074001e200c5402d95601002800d988a03614032502540740703c0a508a42c0d080c01c00c002c5003500380d005507441000411002d02e800c40c03d80200d00c0c3d603803040c0c3c0a5004941c01103580c0b02401c42c1c5014941d0404410102e118010901d5000551004005441e40040c0023600f10b01e10400803c08060b20741044494190400c2e12620440c460090200221103031040ea1a05102040c0c2080c243c080b02d0507285c1120340c100c0d01ca01107a4401da8900720209090b42d151005100c0c1700010383e1602c074940b151485076901c968640c2c0d0700e40300140c00250415600d90512984c4001c4a86c841d641c40040c01c100ca401d441c1c001c00c0c40c0c407500d0451000706100402803201440c0010320b1200d9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 503442266 1250 503441016 503441027
    0x1306030509060c0a0504092f07110f060906090f090c0a03050a0e1e10020703090302090702070b0d200a030203160806031c0203091906030c2607020f0d 66
    0x55030341c1c003003515480e50724001c07071070f8081c4550314410020a0301404148070917443d642c401c040e00210306402401c07480b9032041c151400103014807000e01d0581300040000c2040448804030701502826a149c801c005411310008102d8004d040040e401703501d0104107440d940d40c402070305400c600c00141a8003020700706842c0035005680240003490101e800d00d000b00b24221040c0c410704801c104190041c0446c0540e250141130340d0340071440d2690785441107070800d48164113a4801400f0b0307117100e030711204511031540c4180411a07200522400079504000010403202c01c49104071504402030050000e50081540d0460040b140c040d02c1403142d419001c514500c015805a0065000b6110b1021000208803e89400c403005503080300c1040e0190400030201e2091801006069164200c50069a05120303034540810884441c0c410f0300b581468001000300640343d0580701c0c1e8605007403149001d518000f04001c2c0b0200d401043c45411741c8209080340050252442409404006100d21090351500390054000510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 503443516 1250 503442266 503442271
    0x2060304060b04021b0601063917030a0c170609071407080408010506210a080d060e07090f060507030905060304050c09040c08011a011e02030f04030b0f060a0b0d1113060305 76
    0xc500f1110044145e10b44035003000b5027a4216002c80341c583d41d50744004000c140c03030400d400c86006902000c04540c0c0c40c14800594404c0615000004184003e0304005082804002500707400000311400cac4407640c0c95036031517203a0102640c207000768050b480c14141c6a0510940001402036000802d010540c0041904440c0c0220411100340c10030703980090540b81c0d506c032031040180035a840680c503040025054400b030301e001c074180000000c011340da03511154400e81003244c0500005400030801d1104107007c81400780a170407245030580c10a0380c2d5950151208071540641071040c800400000c0400904201c0021890790141801255041514254a61004500454074a9403c00308206095078500350413000c1c10b0f8050350703050222080c070122440510380c0300c03500d2011400104101074645083ea001040294400c02000d0301d5890041811082c10001900980c86094120030405c8041040030644610500e117440000301c114041a00340c0c3c0301c0c46111503040e00c2543e50140061040d40540c0600d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 503444766 1250 503443516 503443529
    0x803010504270b040c05040c050a020106170c04150801060f080111071707050c1011010e010207121124010e0906160320030108071a0702060304060b04021b0601 70
    0x4640a41440451444440c070030361580a035541d6802c10100300f184190340e030803d015440100116840b44003050681b140f40000002080c0001030100d00c0c00da091141000518883e00c7c0600d1b0407144001d072035100c054440320b2a200d40d464515000c01e0041c0c1c0c184480080172088002c20589907600b5600080c24200c0c820207059502c0c0c849500b08548810044502195000c0d01746168106520826421600a000280e0380c0784201503034900c030f0b40c4611410202c016401e8071640c402c4200d2405c102c0c291100c1c1718006c00c040c0d0041c00034000048240030219100f803664104000c203013442e01121882c200040007548c00d440e90484c600401a02c000c0e0000d81641c03c541c080410a503075803681e140c3e41c0c1c40241c80000702807009000c00c6a00328803d034004d541906a90141c1e904070042005881c0c0c5a400a80043c0b0903a00400d20030810070b04000c0034200c0036100f660000d8209040380d00040c016000092010745080c1c0c5031440c0752802d43c0c665045a00c413030301c40074030b451203900d81311043da946000034091340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 503446016 1250 503444766 503444771
    0x60607210804150c0801030605130624050a031128061d03030909040b1003060f020904180b011509121a1b0f1b03030916150503060d0c0807030803010504 67
    0x1a00c04003030f24021124920415201c02030030386d28590350000104001824020741c00184140e8800142c0d090143e4084000040c0401c44488010580408a4015a030000d403013040e9a00003000028218410781128420448203c529148100078820b041c0200303407001e92841030400380101c1c0c605d8000d01d04082010541c01508500144141499500e100f440c0d01598042928800100010010074090303600050007100c02800c0781d500d50740e060a45070010b070f0400d0425004038410503036080a103d0805081580c2e0102000386803103072926841c2d480d040c00f0b080003104042c0c071004825030254040000505101805880300d0805003070046d40c0300d20140c03910401644020115500d0f4010100c200d504400b40040b15141034042814217840d58001004084100a0700d6a4854680c0c0180081c62040382c0e0440903160400060751031650000b410303003228140f580300f0002c0d03800141d40941982d0b030111003903918010540190400075406038955020988512459101004002d00f140207941255403d4806 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 503447266 1250 503446016 503446043
    0xb0d050705090f120c030d0e090709050d0311072c06060a27032405010501030203160807120501060e0306061c080703050f0412030f0215060607210804 66
    0x1c031024420310066540c401400d5882c01c070f0620b04a1400810121428200d80641c2564008a4100b2106441d08004210303c09040807060514001c0564800102c0c0740c03030b140040c10680000e0440400d10405020004a0701c3c0c0101003907400c010000180c8051031480315401c4010f40750845209510340f1a1146d40800b401154443c10170320140d0b0f008041a40340c091010610100c1d0326042c86060325454820103003100300001103400603080d00c42c5071040d03080c04c2e51700544591001003525010307030100341090320400070400d180551221000c00130009180050250f01e40400c1166071401c00c0111104062404c000091150f80140184509000942c252669a035a040c1045816201300889089009910309481d000540300b1000f0041e4601c2820300f02d051002410189d10f0039041030b044003c9040240074480c040c1070300f15040a00c21500740c03004240507000d0211907200f10001401ca1409000e001c1214010030080d98001041913450b00080315058003070a100414040d016601521280e403079041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 503448516 1250 503447266 503447281
    0x90203041b050604050103110f07081b07060e0f040b040c0f020d02034003030807090b0918150415060f0504080c090a0905011a040605060412080703030608070b0d05 72
    0x401d20484400625480c10700d841e00005401424850000c041c242104000100c052002c542c040c25213140260704c2c0c83d45034000c9204030542c8064820001405500c503010800500f6804001050501401e4074013a8846241703501041c0680b07010714019038841d050107500414281c0c08040490b1a081a508a848040b4911030a90301c1c1d100301000359081c140c1300380151921a84848880004c41e210905507032200c0002d20700586040d89540044000030000310521021990113150100940011b020701307490044200002545424030b011a85015040e07540015031016081d480518040c8000c1c0003840480d031078400791105108075000d8540460183d00e860000903101320299416941c4040c020b01400e1510301c20460081801014550619110310940001580a0141542004062210204a004503c01c00094881d0368000500810040c481002040c080a00c40300081d40c2210f81c040d80d072a4141801c03006003841c0e4001d1030b807501c81c1440000c0c0c0c0041d02401841000c2d070f051010402c80c0c58101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 503449766 1250 503448516 503448563
    0x90501150e061c0b0c0705070b04180c031824020c06011a0403020a0312030b011115100b0f030a0f02040e040201110708010c030605030c042f0403020a09020304 70
    0x14001d04801c0000001d000340c01d01e1443c0b400c2080040c0001c0307030404420f6880c0c1c5440e40041760b8590030540085160810000c0c1001808080d2044c02d050505150402e9004900c13614550032024140c0d0b01c82400c0b20100d402a8444465440c500d60b04441c12515400c200150200910140307007042090a074000c0d095000b417090b038080040c424060100359203007510b800d404000c8840c81464900c01080300200580d601d1260703c000b141329000100100321510000380c126001c01c5102414006249031032010300f0030120f1146168004090544001c0d160f6104034098480c00740c00c04010710700c0c001012100d0300119800b9500c0349840e2141840003984610201042e03000701d114113000d001880d40030500541c0a8042c45c40114074507022242c01554400c0c1090075140304042c0840443e81d501c0c8144100c0c2014000411452004c2e10240061030303502d031a90702c2e40007182842c00311800310103102e0905160030000311340041d81c0042c54404800e4a907000740d40254800d4070704803402d074981c2d50301107040903000c0d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 503451016 1250 503449766 503449769
    0x70311010603020904150b1306080f0d0206190207140102090907031802060a020f011a030c2b02010c0b0f010f0e1e060a051507051513080711060a0309050115 69
    0x80c0910641741c445985500d803c2220f402020035880d154098030030a521081e003981061814018007007440d41c0ba2000b2141030561455484d001900840c155840d002d400040f180e40103468024100a40400c00200d1f100034040c4000c0140310b084d21900c0d40700243d8054014104102013240c1d105255241c111054085900010710034070398916100280e40549400c401078170558481f4010341d40700001c80b446090840322507029460111510051440c860b040400a803081076805480c048a100000b081e4404d010409903200241c01d4040501c001c01c59202d0701004501d00e620220b000c0706401c1c0030040c1d41004909001c2d00300d4201c10b041001030608192600b03140580c48801c10584030303079400c41c0d500c0000340c80180040d4006507403d0740010661250070b41922911080c08209031184040d14101c0d0426070104400307100748003164103010b84200720705000d094165211b040c0c55660815481c2020b032020307480020940c07280c0045642d42c0a03a4260700f014400910401c0200010104100780301c4400c020f9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 503452266 1250 503451016 503451019
    0x30507050d0c0527090f19030e040b0a0b030108030307021009320d031a030a0302340b03040c0504020c070501180807081c0318030f0306170307031101060302 69
    0x1c00004100e54180003000030300c07442504540c01c0c544018100004140c0d2400c1d07442c140c61b0381c00b000440c499860207005004228189880c1043e48120940700100b0211000c104a88074503661103c0d0000c59a50304042c2c002800c03e50969a200c1d81c3d00d101e00c42c2c42c0d801c212110340150180908413181a04117108008400380c1c00008100c038003c14000e060100750114101400300d03c0402d80311801c4510402c07050080b2452590041744002e00000748006122a480c8814069880b021240e00007075000300d00950445034101c80c005020702c0d490202120b245504000d981c8848284101050a41c941c0000354402d9005400444080355218240400c0f4440c6441e107041135001600c0c240718540c4101c01201e00e0007903800da402c041d2a01d03054150308015030341d44000729a82c08030340c1c11454440a4000300e000c8840d9401d040100c00580140a2900240410000c041085001010200c43e0181e80200050122030600b4610102e008100640ea0f0740454810343c081404041340d560300c058140144401c2e40d60 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 503453516 1250 503452266 503452283
    0xe15040f11030633040f020d0b060c0a1205070c03031725110f10090c0e010803030a0207080c01091203110306150f0708070c030b09210a0201110310030507050d 70
    0x40321130b0394044c081503510a6a40f001c010031208041503589015030403452070400801a690b08841c00f80c0b0089602802417180a10000d00c8000c00805000c2040c45915070400c2c0d140300c4403980442c04644900c94070000034841c041110010007031540c440e141e0613990600d054140900e0320b65043c402580c4034030400f40c500c4500c02e1035200380040d100311200301b4400c503e0411120041a07441859080800c00e6020019040e0798410f440305102103010700000034025006451129410100003e03207c6c48001d101e503a2441e00000c0c0802080080421a08007952041c000c200c1040d441c5402903428a518040b1800642008501a0350004032000c407802200c0050600d200c51072030840c11991600300b107102206070071090085201044c1814000c004071803140f140424020b05518116010030305c05040290107502c1400009541e2000f03109400042001542c916211080d00d001240500000060854400c5c8044103220503902c54046031029070340303d0f0090320022900c138824844c0480d00e81502030603521 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 503454766 1250 503453516 503453551
    0x90604050f041205040306050108030316050c10021602090906090c010e01080f07031e0504120e0904030809010216080712020d051207020c09040f1101050a0504090e15040f110306 78
    0x1075100f0307590303407824040d81801402c20b41c0d80d80b01c80b421a282688490142c1d0400010040710f0313803a507a0415904c04150804078202000c2c500c103030f5a10311400410442d1141d001950000454194217807450b0a6801050410145001c511080c0c0712082902c01c20414424000191203e6015200c1c016402c03906039900d011558450032124040ca1001c0c260b0014150b9a440003800705059004840551040c0c100c046040d09042ca0000900e03142141201c04010000742c05441e195104011907030403507050f04e0f05c074000d9101c821000b0f009110750305e92000c000d0000b154a00c03c0214120250085500880b41d840d100080d00c0801da840e00451104540002e07010440440e681d010944034036000302252044030646410040450741952040c0d030301359112070902c03444604000d190241d140c4103050a01e020b0341407a9844e40043e046004500035080910346402c80420021020010110308030341c5a48891084d00b0582040d01d410b004c1040280c50b1300e5080d50742500181130016003180640812021101c581 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 503456016 1250 503454766 503454773
    0x210a120b060d02090402161a06010c0803010b0319150513090c030b070c06060e06120705100c050a051e06010603020c030f07032f07061412040503070818090604050f04 73
    0xd600c100309617944070758240068a00d122664506050070362050307450001002200881c15000c0e04c0c005c080394100200400705000090300c00d001ea0341181e4024103129103d44503c41124800b05690b00400c4005140203000045054841c03070800841d20180e850b001d600d8030a5000c00c0c10749000c11030162007020500d004000040c181185607038808030b00d1429252031480c40d91400c040e11041d6200345420b0b0a400300740181d510381020440412020840201009842c04011501c4480100720002c14008a100424140320052080c1034407160301c041034401c07014004000e0400d441d490003000480d40324080004c030f40700d4068802c80b43c0c8090321100a6040c0f90340300d5030556940d404141e040341007201840c003216213120118400c400c1c6040c001000400e03044107241062810065a200d502005986003500f03100e244e45604450342020910310329140e960701e50a202e1710314407404030000d21603000003d601782c0701110400b44003181c0c1022208045151980020402590320946410101e41c4010b000325002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 503457266 1250 503456016 503456021
    0x301150308090a080105010f0302090703021e0c0f031303110a060804060f0e0d0230072a1712030c1602030c030f01020c16030308070e03210a120b060d 66
    0x494600801035442241c03689011829186c081e070210080013106c0c01d0034001c41ca4400c0355640c0c40181d9103811410130700801711b17241501183c48188400c075180040d001c80d00314414000d000c08503803100304a039518a0388100007440c1004521007912081e05100c1071580318a803c1d45000c045500c0c0d541c034008070380c4030f80e02e072400102a81190700a11665858100c00042030a10101218071955009000c0e120003000e02c0400d20780e4170400e4080041c00e080810111f580a55003540c14464210700031079004014440d0300d84802d20b0318607103880101c40c40740001130300041d61342c07410701c0c1d0850b8038055a83d07801030251250060701003503c580820300d0003403004180341d003100c2104421490000b811101c000003080d0101c1c5c140f2662440031081a50000f901030380d91101040840740c242030181c000030b0b0080c91a1002404000050300344070401140e2240144039550411400b12040808404400c000b0000c04101c402548120f6540700480c4c000340ba00308070080c46110f1480d6244001c1c10300c07464803442e880e80720300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 503458516 1250 503457266 503457277
    0xf1404110f180405010608190c12021c05090d0f050901120c1404120507081b12120f0c0c010c2303040b0705031201080105070203041a09030d03060f050301150308 71
    0x10b041d0102c1e00b0504042d580e40c01040d00916842d101c1c00301a042c00c18001d15011081e04031840c84e01e0400c0703070012100358408581200310300c03010780050701e40001c544504002000c00b140040c05608003021711403c0381001c608440030f0ba8260703c500f030f0030042030305007941c04e800b401c0760f52808203501c03039800c2c01c01c07078640e80002142481603d0700c00041c01440400c0c0c02c240e0000c1d0480e50246003000002003c2050400074840034241610003003007244081045400c0c0300c0340341c2d06098050441c200351688040810404071003020044030000b41c1310000b003d0315104a4215070308112152082e101d2201695004102084900360001074050034903542c90085404801c1402e28004288804c1100150940c06d02016007420b0744920040d50783c401501818007000700068111500c0c0da4034103401d01c10b02580020071102103964019029881d06401d00c40c40c00e15015140103560140920703402ca11016078180e008400782c50482420100c42da8850060600322001c10818108031761040e4030a102150f0403502822 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 503459766 1250 503458516 503458537
    0x8030a02070b010902090301060b04120611120a02250210030507020c0d08070c3002040608060a050709082d12070515011a03060f01050906040f1404110f 67
    0x1032500700329a44102e0104803d902c2100c24070780c0070802800a00d02809600001c01c01200c2642c01c0c141024001c400e0f150f8600e000400d00c0c0d0341d64075510552540c000658a08080311981902d092510195600c080d611401400b11110303d000304500a0364101c1c1c101040107500a04050501d61642800340d0003464050020415841101d81c1d038212a6280c0d07140041c81c80c405c0c00daa98440c0601d01d0000300440007504140310040c50501c44448030710107540903e182031105c42c8013110110460000c5002407035a50004499030081c2c400b005100c000503080325000d002c2e0356581344110707623441c110701782c642c0c180020b034495100043c6d80f0700f02001c0c00da80d00940d000c4503c2c2d0607a49010714001e9084441d9101590446294100d2000503805d00c10080d1810700420a09541c0c03440d05100b007822040621000788803a1181071240c0c1036000a0f4031030f05c10755480d04409400680c0d0b07551102e003045420201ca1040a505064102c011001c600301801414030300000009901d0420010400f03030903482d084180b001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 503461016 1250 503459766 503459771
    0x1908070203040f060c0b0903190e0609090a050405060c2b0b030303040b04061401060e0d05100e0a0209090a0201050306011d03070e09010b150405011427010815010c08030a 75
    0x841c2003140080604002d1004d44c8540141242c0c0386403071402d580c0018903403106500140001110ba1829102c0010311600c9850241609100140001c2590041401c1300ea003215040f401c1241c020403d50146018901900458419981c0c14001c1400d030320071324981c012042604ea034101000030001d90010803010b020100400d04501d84004645150002c44040d0303076202030300041c04203001462050544180c0110f208800640c140103000d030102d406004c130300340034811310b11a06007440030234000600602d4000c10240f2001814621540e079950b61b019059103d4540d10004c21100b00000071fa440200d5410f86440d41144d40b04001580ca02007009040c0781250b9445406000782d035024000940540064450851103042400717046003101c10580405000754074500281400c58100002c1d901241e109190070204051003100f13490f001c1c0070b1a038040315840d40400381c4130000700c00b213010000011000c0c0d03101d0340165680c000d016002031b0500c4a03103004c6840500b0b21070100f0074002c029a442803440101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 503462266 1250 503461016 503461019
    0x330f180601061b06060806092503080406080c190915020102210402010207080604051c0804030c082d04030b1f030b040204020c0f0705010810080705061312030504050f06190807020304 80
    0x101410300c0c504035408c8500b46c00c400c204c0200564000f03000b01c015040d10701c00c1030030182195200e201038810b40c0075003028440d80d08e0005d451303d000b02d81200c600b1301f180031841c81c5181240d0707005482c5503241c2c003499100109550045040d54414425200701071420411139030381003241000201e8000780030700180c2c110300032200c0100b480b903410000303540101c0c846c4000303103a0012105412800704501179940d0041151444c140f001207a070150009100741e030060982a65050310140d10064210f4056025030312204c5000344184920180c000340080701e008004414a0381d4800050222001d01c241001c0d020b01e079001000e0010400340340d20141e00a202410061a00c10250301c070a26001d1501d50503a0641d1103001c060243d9644442c1d996001a04200300780400303401c0518203034895030745004050183c0c0000c640038446140c400801700003051341920420141c2c4c024100109264018003641d4000d0288003181c401504080b000c80701e8480c46820480404a2011007c440c0360ba8054544030031440140030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 503463516 1250 503462266 503462279
    0xd14120a0804171207080f070302040e240d0c0e071b03030b01050d24050108090d08041104240f0303081501090323010e07050102330f180601061b0606 66
    0x21240102d0171a2603201d1103107001d00b00c1c1030329454003d086204041c0140300401400420b030f90429003090700604545500e03109540001502c050003108158491501010103003030000380143d030020340c3c0e5050300700308060340e4a00080d50910b11100c2226502c100d150341c0080483e21036400351644190500d080c51a0600b561401001d0b10f160048014403000c0c40d848590320700070b9000801c0b00070b06081c20700c3d11462900010440d02d41c00e40490070302c144a2204005006c00c102000c4091004400410070020707030210b61500f88403601c200e221115004a0003102003240594060038000700e030b900d981c8900c0e003a48c802550701d96480034403102a05101c01a00007100184003807000b213078102100a801486450308404a0b800d4842070040e0894130b810449040c841c99a020881800780c90810280b16284c80c2c0710f0424400c0c2000c0c0324006075559500f0b01c20312030b001d80c1d8001c030f03103015881178603803088000d604101c00c1e40c0f113a000784219408500780c402000c5030814500041656140248000580a642c03404d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 503464766 1250 503463516 503463547
    0xc12030a02040e0702122205060a030b090c1204150e12030a110c0c060703110f16061707030f0b0603040c030c1a03061c020d14120a080417 61
    0x3108481001e40200d0240311030780c1c2c0340c001c03c2d9010499200412401951100000e000e10403080da0030f61004a00d4610514062580c560100030007015000702c8d904c105840008005018040c0c02d00d1084540c04041061038103000269000f0000540100c12075444680c0c500311402e0007103e56100c82915100302c3c1d1040c007018029508034801d2444810b64915040c0b4500b012100c50700340c03800468106021820019000243d40d044591050b980c0c95500d0a080c2020344013501440381c003815500c0b5440d81034010060100e0003a10079014a0fa003010200c0c3c40324410f45c2c150806016440291171a100014012480780e002000c94103400c00c0b0004040e0240004245194002c950540320192207510400421075035445a1004100c141004484941040c107500703414030000e410b0354401d50030242c2e0031401c1c6615401c14444981e00070000d40307440c401c61402070840c14940c058200d0074007600c02100041c80b0800c0460300c0340344640e645ca0a095031142d981c4000e0714404400d086140c0b1003803082420040265 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 503466016 1250 503464766 503464771
    0x50912030a030e010b1507120903140706090504050702030a180b0c03030108280b150402040305010b040f0b0102210f0a05220b030403030504020d05100b01020606120c060c1203 77
    0x60764045820b070841d403c3c00e400e4440c0104c05501030325888048200c100b11b0b01003510805076000011030100410600111402003070b83c0c0001c0e21106055a81d003040040001e401c40031203c0a85035001d8490792a810031080324002c8502c1009a002001441c8004d8452401000c15203083d01502d0012500c2d5062092250800c2c03d0303500443d0702c004018003a801c01000000c0540710b02c0c0c400341802460751010300c9551503841c1c4005010002500210b1007100300e1200c0c8440855000c0c000310345541d601d081c554081c00e071000c1e180e8002c91419942015110490003982c144002c103800420804030000f8400c0251041740068580c1d810003488640a5001e00038000c01d40e56596584041e216603a69030600071004400840c440902680c1070200116440c44003982c0d405a007504000500740d55138004904013a2079604000c1450240d5145c0b0704030054194404886a4401e9080741c0140da94038041c007000d440000c141908039406800d5028007403800400400f911186581901c400b10514035402c065a00103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 503467266 1250 503466016 503466037
    0xe2502010207060608060907031719030605040506010804120507081303060b010f032307020109050a0b18010b0604090c0203130e0604050a18080a02030f0d020c0114010e0705091203 79
    0x140302d8188081409484090545071300904040d04104200170b030f5404032448000c100240c02c1b80207810702d00c08242034820b00d40c680c5580048800c481c0308001c2c010b00247c060603119602c1d01c0c0c04203a195104002c4a48100d13480b045441d040604804243c5543d0401c50307088403000701c2000050444003520300c00000a41c424840842d1a07004040090090030306846560300b010300d010003016400d280004e10015003225203100180079201e0307a10407030140150360805019485154104401c01c022034584600c9100b0500c3c55210310140c1d214810700741c075012810759911850900080c04402030551160141c50640d004591804403840700308070404505a2000c02c4854170407081202506142c080c699000408903000c1110010050141d5005000040c0241c83c0000c042841c0700e04900800890b85228440d403d055225810006403001941c01441c58443da54203001409112070413510b10a416649005206484c035950312008a07059001102d9070307603214004a50600008500f84010324070b00a8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 503468516 1250 503467266 503467271
    0x209120106170f0a02040908070803100905090706171e0108010f0b0d0f1104150b090a06050c19081e0a090527090f03030106020304060905060f03010e250201 69
    0x142554291040303240b1800342610750000040b0719143c1034041281c9420300e5040b5070000c0d0104503401c09454901a00400a02c400c0000060100c00c18408450380f080380d04042040c02a90303a0510a6503c84080d07214504c00302d0759146a07d0030100d200002594002e1041c0c07000d424203030228100c607450000c203902542159560b042c4610703010040303020300342036008241d402c245111400da44400300381c0302d6100003420b19a03c000f60500107036180c0d0401490910f00303542104e4495100e00710219940d00420710148030303803010100018003a0243c41500c1070551680c0250031068007510324050075914108040368140780c2000740c80013040200c8600c0d01c01c0b1644012454542414034405801c0c1e20f102d420031442000340d40b940300300302c0003940d0144211070111024082240c032a8401103151201030968031495010200012880650002c0030b80100c4855642c2c40306100d64031000c1c0880d42c400c100401900d44010001031091406184c0901d80051344c1d00584a5100c20114002441800300c40041e00180d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 503469766 1250 503468516 503468519
    0x140d0b04151a03010f050d0f0506280501240e040f060914040510150504060e0718180b010e0a0f090b0f03030a03150f0f03030f02190201080a0209120106 67
    0x1240c020b441051295441c0075545194104415039002400911030103101d5011a6580020840350000300a0703110b5014080300c09500308080e801c1c0c000d0f22202e8103e001910007403c20387c1907494600559040300d00045085140c00c40c1f010640500f071000030307841001e01004036445200c40d20307144148186041d03030b01c4c40020300e281840780d504141c40f202864440c100c44640181310100e0301c0822010070a03909034000140002c61907030314013a0001a40d21480d03010b0314000c40014640040394a4502c1120130b69070354040c000b4620f0030110328007130f140a0b440d41c0c8e010520004031550000d50013180825014105407140c201c6850000c0d03008030017600b103502e60f0260703c1c1c000c11041c1c5c268055a41c4594040b00c21803001c40550000c01c0e1b50f03001d4505200300305512102030714003540c441809100680000040350303500545411024000103903503c01200042d100580035105944085103006a03a0004001c0c601c03001546e4004440c1040081c1c800c1c1c02244c1e08000300c0d9143c2d1740c2c082c03545500d40709038800032075a103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 503471016 1250 503469766 503469779
    0x27120601060801181b0810051f022401271508010e031809130b070e0f150703200d17010e06010c060c050412030309061b140d0b0415 58
    0x1800007007200124281014000c1244816417001d03a040200e00d03140c04120303641e4440083c2e04070003880c0d105942060750242e07644100f0044a0350044005140c0d021540000b0704192000858160f1494003440b498031500107000007106040d0584149160041c52110849204060800c84075090001d8509a40443c01000200c81c00e00801e0034107200017001d5030404542078020300c0e000b0900007030f00d441610102300244460b20560719000141e5088607940e2410b20300510003521100e1011821449004002c1070350010b03103801c14004081c403040e95100c034140805540c2c20f85400e0f0038585644020020030040b41a001030400a1115445a5070f0741d900c4880c20243c621200c108041c0c0000c0858030101c0208007041c0d805c0604901d0095000d84005200110381d0011211401507401202002100d00d440c9401c1c0343d4541c2080c543c07140110070420900785000c4000303c0307030a9204494004079650079030703040c441c0c000207000d4180b107820104082038100f0240e00150443c2d100d00c42c40d85044e01200b1051241 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 503472266 1250 503471016 503471039
    0x309020d0b01150906050a05120c0c060c070c09050105062203060507050a0809010b030304060c0807080a170702010e2a060d06181109151c0219020327120601060801 72
    0xf417502d42099890f0028540d001050f5100c0e11603504a40c99015000c101c15551000880d84a44030030416500141852655000150301500003540da030100e2407004900d0118603c5444d04803040280031a140c048207000381ca65050201c01c02104180d8810400004a0000e0140358400e00d00c0341d4a0076030301c3d02c0440016140100180441180b40c0c903211010742241c030004111001d031411400c0c80c44180341750b8074002d0410b02c070f0a003008121200102d050440690403000101c9030b000d2052a00a06a803500c0c0100d08a03020150b090030258450f25030512030040840030a005101468403410400202001040642c4d01490307a0012041e1b5681042020f660408444089204185410b0100712040c1070a980c00d4080e50950714071a03000c43e8514600d80120390201c80c050604145070141200070f11070b40c00c00940086611070341c020700d22400010858030103c121a82100c481c1e6030820380c24115030b0f0409514035094140d80d00324000003940c2c0c000712000c002460007800503698544907981400242d01c0e1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 503473516 1250 503472266 503472269
    0x506040b01051905090402090408071209090c02010e0a0201050c010f060312020c0d030206010b0f1b0109020307050406030804090917120615120406151205061f0305030301060309020d0b011509 84
    0x401c40f594000600c865603501c0b00f9150000e4044556494a40b034a06080c08a4031416000030f08a610419034858081d80045008046070350b84c000030005540b050070180c1c00e899045041c2c10780b542100640350010341c002c0d80641140300301d40c800005c1ca600b00d0820001200c0c400d810a880219045001c207045503030400a03000100000d607140c000c02c41195501039134458040c0582004842c1c042149440f204070102511001240010000d09440010046500130129900d051303019001e5000081450b0400c2e024400469078084c07007451400c0c0c6082c0003880140b620381d40480d4415040050b1071259040b142c041e011800890f1307568409401c005041054110001e9902c4440700c81c1444100301c01c0c00d23140c0c80d03940e21070b030401d1000c80e84403000100e045054055802c140800d51403407120000388140020018851740022507603000c0401c0100b0322560807036643c40010001c0d8010401030043d14440e411510410388060301d80714406006585844400d80260030075035800d0045103680558640c000004030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 503474766 1250 503473516 503473549
    0x911040b06070b0f07020114040b100b04060e060c010207023007030b0406020a0c02030f010903230703050f040504140a0c0f020d0e1309050d09140a0e04020103090506040b0105 77
    0x2894004150348800b41c294000b015201300c100b5203c00250b0450007900610982180c80c04590003170301e41443e0200f000181501c2031240c4194a000c08108140c20b1800c0f0f6044e1800764540502c0031001e503080141a5001e0b40c06070b0078030354090101000513162a04102e00740142100d84c0e076200f441400d080c928445031000841d2990380700c01003c1011a00e000606600f180d04a01d015a03541d55601054600000da440d0080d018880c1521420580406510030010345203c0da80d080308040d040c500040801c0700b12030381d00c900c4003000c0100c0b07030001c0d00420051002d1550031440e0760030b003569100058100c950100220300c2407010801040040b01c0540b080c8145140d05060010700300b0341c030000003503940500912200074848001095002035407640100c1116050100f020f2110020034a001920391400801110114130040d201103940c66400c0d101d5014a940502590400f92400f642d1514110018000781c0c1455652050840424414411a841180110781c03092003545040184220014902d0009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 503476016 1250 503474766 503474779
    0x2041d070f020a030f110f060c03220525120309052d04270f03031104060c080d0b0d0b010f05010302071e02121e0c0901150f120911040b 60
    0xc0000980040d1817828002c0689001001c540c042d1a049103031003051500580144903540422100c20310a0004500c10764100c25940c0900900c4032036042072004083c4001d100350407084082107150401d4200307940e4098407040c005100380c2e48004013104030700e0070001600000d0f91400e00b071080d800c2034018040b400b113030260845611005c0180042d013030907031313400c0755440f8a8540044a503985001c004184d8003143c4540f468000380400c5c901823132601c42c0400110f0209007403408950a030300c580410741d012034891b0340b9010042d1440c2d50358160030f070b800301d80180c20b13103503a8284082040d00c8800c20000346a2103a41007030000d504200420010302c04650010341018010041000043d044044c0132903101c9d8007000d130b004540321502c0090307071180a549070344001d449030002d011681042d941e04181e5452100e8103484002c0c4495013801903004e024007608910300501000c0075041486882ca250480d00245054410201c20422500940e803000750155a0b8041c0088400c0301c80c0b8061240007480c9408480b503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 503477266 1250 503476016 503476033
    0x1606080609041401060503100207020901120305031303090b030a0f05090319050c0c0402030f0711010b0a031217070e0a23010804110303070b07020607090320030102041d070f02 77
    0x880800300204003c0881d9054443d0700c040c690250005005803400409a0b030501050b0340e9008000d40001f5801d80c400e00401c0c3c0001031480c0701b00e080d40c0303080742c00d640c0385861581e8030307821000b410018281c12001c11100002c0010240721003009140035005014000c9211604000100e041d13603009460320303042d074100300410442c1122941d01d810324036650742005610b804420300e40504000c042c4180a070000c0c0004100703c07090350036000151280c10380b91511414924007245481c2284c0c40042450740000d403c00050000c52841d0140e0f09220081e85003601c213205d0701d45220780300706005030341000108411204041c82485e191071035070041c01601c01d00002c04400f0b414400031110002d4005070500481d400440e041c400142610184040c010f404c6076514681c900c0d007070942240031909140140240380104204910510105d02240d40140500c40c0c400064110354011104c011101c41d4159800c000c00a8454a01141c4600c6038508005680d0300385001d100140c02c01d80081025001c64201500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 503478516 1250 503477266 503477269
    0x151309020906041b11010b0d030c02010215331005031b0913020309071502340522180512030921041d01180c0203030105060c0a1416060806 61
    0x41080d0b4450262401c003840b20317103000c02c490040c4508000d00f604501c1440480080c0f6400500c40000e2610030303805c442185001080e048050402a0780861040c0c5a4207060103d40d40700312441e00d590101d04149079020341d20349000480b41c402910000740814804010405410507041d0034511042d100340c139840c60012441c00044031a03a0030703025003105541c0400459800c0d24104441e1010b002a0354142c15032440d01030003e5a03885a51082c4034a100711812140c1c0c00c00d0200307407060600420400120511360030300040200b4020182c2c072070401c941003c00941210310302405403030659840c0b9841955007126a080850a005010036900c000e44010018800750903000641403140a81d21340090007111502c00240c1450310460348076003410100c11070003003c2c00c5194010981280c00c0e1744540501d9203170150b60502590b051900210140c1c02c180010007440c20440018098440403906581c030420b0240c0d504864486180001d810641c070a0401144180282441c0c50143c40300f814071000c2407400760b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 503479766 1250 503478516 503478551
    0x12220e0f01170726070302060c0114100312140f12160f0206011509030f14010b0319020904110a080703060b04140412031407021605090405030a0815130902090604 71
    0xe88000c4042e02d4110201c4c0d2254050000b5800380d0346c002c00c590f0391086890714460113804070603000d120040c0140003240c0b8408a400148040341e40c00b1850650454a50a054403e180c42c40c1818201a100300451940c2200b4100281500ca80030a0035010a00700604010410701520b05100c041c0106450740e002035580003d0030904407800d07580c0c032241d5480e18010032142c9005990000b8440d00550300520100180546c4010641445800030041d147d404810141d840500d80314001034603061007544005030510186280e80903002e02c5100851001650106000030078982c481d5401c0d0300041c40610030032160740220742c80c041040307030284080c28410035181030818016200408036058128501d2025009400246a241c4011141c1420b894011400381d02c818403c0c108641002c0341c503d0110300c91504032201c2d40600d8000000b54103040d0420419140800050912502c15039001c11402c01607480c8040404200326100c0c0c00302e807030540e51042c4160b191001e0925840313681452400d00300c035810361 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 503481016 1250 503479766 503479799
    0xc040506030f101208090306090a0c09020a020c060a110601090207050c0f1314160504080606090915040f030e0d0b06060d020405030a0f031112220e0f011707 69
    0x40344014190740b2401c0c0e4088002c0b03d681d100070000014408120280407441c00a000424001c0d8282d80fa650341d4001413540b1104032040040c110045c0c940d0a0040c00891348c003520078a80c0b180100d0345006451030016416411402c043d80c0000e550000c020f0314580300b44801e50050050b080d040d41041c4090369032644646040201c1030080e40c515100500565416803025080e4107280d40c04c000c0c084030720b0b40f9a0342c060401c0758001040c540c089860001c89216104030342c00c4032242005480c0c2e94560408001007a14041d201c200d062244210a110640c2c1013103105004a200314101c0541121306d250180c440032400d4087c91088042400031004034200c0d040c3c180d404513046640a58400c4005038410003070140790440c1d0f415100360700b210005c0000b43c42444906070700a4a0798201d0601009810342c1c0e80040c46ca0200700d4030310900440000141a241801c82c0120341c03168501410784580c000000302d079049400e11404402100100700c0080004168a00c1c00184800307040c145040501e10b102085e0361 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 503482266 1250 503481016 503481031
    0x3030f09060906090607061b020a051c050c030d05070906170a092a081204051c0f060218100203130b13050a06050a0807090e0a0e0705130e060c04050603 67
    0x41d0340c407025511a01141d2030302c140105030940352041414054008e1140000c1203c130f034880b0a4000400b00e000158024000d64032070f008014080590300300e0342050102c0c00003101408010302c11603104007030031f2002c0c08940000a000040a150261006000d031000c0d90041090101c2c0384034041c1060800d0001c9548102c5013100803a01c41080c0c0b034802c5000c4e84000b075612081e900d1301d41e01050390071100d03d10011511000101e880c04070307441c01d03216160300c500c0c0310301030340441e2a00c10903811014451502c0d0109003e040d1190b14000c503611104241d030f003d14105204403190401c0134409103011081d0310024400751008508100d85c0c0c850541c0824070034013804c00c50b0100070801d05070b2010101a02c03005000090107504800b07554120140076600001c4240b4086020b035000030b12041e20070b1141c4400c595503a01ea1080640722040b0340d100401701080b034000f00c0d008100e0301107102e0310303646150101d0a04d101e200050b40b8040b58040c0d8107210000e0040c200307030300c1c080108010950390764080d07075004210b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 503483516 1250 503482266 503482279
    0x41506060c0b24030f07030c090515091e1e0a110306240c0102040f150e010f030219050316031b2001060f05090105010806130e0a050a05010608010b03030f09 69
    0x10450070440312008002d0420342d2520070a0110144c0b00004a4001b0460744031740d046071070721604c0780c59500960341c048804000c80c0747d40c0742c10040945051022640c00070710b00d10321007103074544010b140c25040d0002c44841254130b08603481c1c12503144000310582d0b804424032000704000000d0500800039403101030705942c403460300300b0301501d1143c044007468070740c40e5500c207078640c1d441200005c1c0714081d40061044658001344048005843c0c44500c1e10102e40b0000c0d951043c0c0d6072001000190348500040310507608246d82407046a032221203e0460a480c5040343c0c80300c58581ca440080c400c220010307001c4603420541090170f070301c6002c00c64400c00c1180045c642420325014a1103114032528aa0b42c20035040380c0d40c2000c4c3d00103084041c60301c3c1071050311002d8801444617a00c54006503050a01900c0882d0490900310120003408555800b090030400e550b002c3e151030780c406031110741c0742100502055405954813542009100da01344500c07040c0040c150050b50500030500b0302c1d08024000e40090900408 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 503484766 1250 503483516 503483551
    0x504051b031f150f0e0603060601050f0405041806020313140a020f06070f051207060612020603060909010f090605190606200106120f020102100b0a1a0408010203041506060c0b 77
    0x100d644201c580a0b003540351090051a0340d481d0170300b2064105450260290041801040d0b06500c80c108840d10584001c0416242c0b5207001c0600c00140030302607401341d86041010b03100300040c0c01e6000860040c01e085468054488503400c6c4090b0114018803480c419510a4200c0b100603119002c10b01c0c0d104600700c8140b5101d100070f00b001510912440c100a14900401d00c0c0700842c1c4403000080e03d042d034010355007000801e480f1240908107921f203100103580100e060001980500c0d1100710541c0c0003200c48000300d141000780ca000d0003075400c05030044400d981c8071402c0116103840c0031044c480103038005c3d03c1400301a243c2240030707100184c0c800018200489407500c04202c0034003500f00c0001042035259164042d06142441c0c3c0c202c140c4010708038018020b4404404501c0000d0055041101000304849403041c54114917180001d81105d9102c0103400501c00022040000e01c080c41c400c900800340540c0f0191f41d81c950404458054000105010300c904805001c5201c4c03d480c0c075030001d0518605440c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 503486016 1250 503484766 503484791
    0xc0611091c0204020f0c0604031e0503150102010b150913050103081909150c0201020d020c0901051c0602040324050403080403081f09060f06091d13060504051b031f 72
    0x24822145810140780d00014081041b580003d45644034134041d58034602d603402c801c410134411001c003020302c4000403401e0001c10a14280304070500e1542d4070500000911140ca176020400da00c5000702401088440461000c643d8185101c3c0e075400320080c00780801482d8110341d9007500e1401169000e200400c1c0400d00321b0740c0c050180c401d65025240d40d210a041e861403282c130041c035000c2c0d800e070b0480c014064000c428000500014149480510042140b0100d81c2400144101c860ba050f20100e4459030040320040400c03a18401440554051000409100503481d11000542d4101941c03d5001d442c0108000c04641d100c1c40a90300503a040c50045140d0319a00c04081c0003500c814088500c0c0d01350341000181c4e00d041c46d88400c040b0348501942000c99540c83c0c1064440c05445d10a400490014607040d10a18410b556080c0d8080c40d80d45440080c4d0002e80ca90b0400c0320021101184d85901481e504407040304202042e40b00410111700801c00302101020030b0384100656100350f100d094840d0b041d03031100e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 503487266 1250 503486016 503486021
    0x90a020a110703050105070e01020c18090a0602040f03141b040b0f06160c06091202100201020c060112051513111210090b07080f010b0c0c0a060c0611091c0204 70
    0x66841080071a184643c60742040e0340245002d980160106116840880d403a500100300745148000042c03000805000210703101c4640c85004243c4103150140700d5032140001c21900c00f51014001d0f000c003240020341140391000d0114a08080600d003030780400e5028401100c00050451130388010307200442c001421402168084420314020740d0b01080105070643d0498103800341e04d40190181d007900403019035589003aa1000704500640640b41d41081065015007403c0c2c032012620a150b200040c90006048891410100203800601d136019103a2609414031004000c010340e900c40b502c41c58070260a090701ca0040313403171a01100404582d400c1d10350840e01c1e51164509411030983c0416110103010648443d40141400a000c480d02180e500203e4030051050030704510444080c1c5c040a0f0316400c109103c1229001344212100034400c0c2c034100c0480c0c0c1c0310348000800802083e100e0350320031241341c42c00d481601c045031060082c43c03030248a8400b95070355502001214004640070994041c1150010402 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 503488516 1250 503487266 503487287
    0x203040c12030504120b07270504180b0906040c0b04050105191e03021b0c280312080f24010c05010b0405100f080102031509060f0a0603020d110702090a020a 69
    0xf4170100c01a00c810512403003400181c422025036135031803030b0b8140c0e4250441d03119010600402e070750b030b000c000700703000301e04050b0310511001440c100c1c0280c0854080d59000c0c14502c0c101c0c2d000341079410610500041003450510280030f00401c40c2c96505280c20800004c116000310410f80101f40808884034595030301818001190310001c241d074090304c0c4076400c0f02030040d42c400080b61002c4ea00c0d01c6220705e0f244001040140e0198801051040003441c405500141011202440600e080342c8c80381c0000028250f07400241d821031a40c43e8984a880c2c00c0c806400c05000040c43e035034000007940c83d6204043d295481c4000141d0342420810401849400c08038010300d44410b80540040ca08ac05100d8000c7c0c001d03566500b2224484860680140c03580e05480c00e034001070700c000e13540b504819903841c4580380550140d40d11020192812804a80c4140040c10399078242c2e004401180d80010003051f280c106000d0803a140c107070010b406281c03204a03808103030751110080a043e1002c0d4089040405039106254880 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 503489766 1250 503488516 503488529
    0x1416080a03090b0901150509190504080f0304050a0204050105030f06010905191104090509031305090a020f0310030212030c100b150712080a0b130c030e0a240203040c12030504 77
    0x74441c9403000c00ba0b8006c02c0c46040c601c2c10f4220807070340081c50b8681031038098482d0082c407101c4040e91201c0010103001d040081c00407a40040244030b605078078036642e800303075109900440061030314140a0041c441215410381080d40290400d0410752150807000414030704550350284005846d50710a4080340007440d15100c0c2103001c83c1841c1c03801810080381005441070319503844082041d40c0b01d0314441a50791081784584012458201020000c5203400010654841060100540740c62200310380c045650340103e0341d207000c80308200d40038020745c2040d02900001e0ba6201000310b24141800060964806c00440401d901684031011182d0700d440310040f22044680c0320f41c529464810900e00000310510300c1c20340340002800e8600084a02c3c41600070034000300300240451050701000b424400251020708004418103032202160900c452040200d181c405010320103050031095000340104036001201d00e0111494014401d20011071410030a8004940443c1050503c1c14590b05d02550140921740c07214 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 503491016 1250 503489766 503489783
    0x303090108090c0a080a021306051509040603020904080705010c03020c120304140a050f010b010c17090a051e091501020316031e1106160f030b0d060e0106061416080a0309 75
    0x2002000041c6c40b000e154070840390f41c007614401c40307c00400c95100380300341503000034030fa0050320030b1200150050a80701c0003e00040380d1070b601d0b03402145901030706035021114420006088404c0c800c4c207125001400900380360551a0807940d44500740d50340e03041c1c03180c602945000008541000403001c48554940d403004144c4040c60705508001c0c1d00d4000d6041100500c0d400c1640310090b075842141c0b80d124180d4059281c80d407002c160b00e08443c090304105103017601f050824a02103419500c5007100d5000c03a0b88600c080002d032085005010b4500070180032400d5040c49140d2011070750b0707008001d4451500f01c45500f51043d250b582403c94076940300c022200c0945901a54290b03030729502c002605a980e4a103c112040e0f901e5000307840e00310509500c10a40021102d41c00030006900c02d401c811000100204440300e03800c0c05880b801c048819002d900000b0769502d0b13204100440e007050f11105182c0c0010312950400195624104c06070814020051241100064a01d40d860096010321501c0e03402c00c004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 503492266 1250 503491016 503491019
    0xa080406030b06070c0b0304020a1d0c1b0a11040b03150f060303042d120209150d060f09021801140f060c0a0c1415041203031107030315090b0303090108090c0a 70
    0x36000141c7c42540c080e80900c00d140350118912150b4000b403400034030501100c3c40d5035510551b4811094102000381c1c1c0b048040000f80c01880d6400700540a1000e000e0380141c55000154410030041380d880316460f034000c0e0004002440802d810b4410039038050541c07070044040c2e035150340c0020f0441c07007180c00601104001d80304171034640107811101040360012000141249031910030458642c099030310000d51150354500000d100c001c402202850040d40136213040401d4040c5d139502e10179118160b1118040c141d132541c608040d8a084003100041020b24601c00a603035040608020000c0001442540621840c03030000032243c4440d000c40c1c80c0d02200c18190342444005140c4941d840f4180d101d288d50400c8900940304c46440c0024200094034610395000d03140518080c00e01c411748500c0364042d814555903401d000e064517070110041003036074800d6070b00090240340210350403c203920981040c2e0886103481034207441a1000400c589180c0001d003005504c0d543d400c17a02500d00300780c034010150080c2e40e0810 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 503493516 1250 503492266 503492279
    0x4110f12040c060302091e010306050d0326014a09010501080606030a03030519140901060909150209040f0e01020702010206130203060f07111c110a080406030b06070c 73
    0x240e0007244104045080c4680da01e004074213a01400c880d055004084e0861883c0b0352400c21051500004113040202e070b0151780d0000101410001c69055000c01c1c000300001d410328250306e001280e03002000c4114906075040a4009842e4000035a0154200d65440b041c820f05072400d49c0c2c0301051400504030040e11981d41c0001d103c1110041c1e6800000d5803c1034004100908040340c071620070400540100324002c000d481c201c2c040e14014140808240410a40754078909042c0104148503102a03840006402d1a44240c0c1c21500190b001034142860b02054000017201e107480403040c0441c021016882d108181c0005005002030308200c5d1010b4a411031640d04014190082d00700c05000342c0076528203030b960140320000300c50102c000a40c90740118000403481124400200e0300402d251500e900056074040e2181c0c9041e030082c00b03a40e0441a04501030b07030050780c0a8261444200803501500c00c0405c03551714155540600d00a087c24180c0311040301c081034403060f0907a040c1c643c010801c000c001c1c0d1b81d1b10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 503494766 1250 503493516 503493547
    0x41b140904060f0617010308090607111005030f0c0301061233080d051905030c070c0815010b1c05090a0c0b0a1106010e0a09061d0601061e080604110f 66
    0x401d16001c01c5a00241711090344c14048454122a00718070b86610f00980c2c00100201540700c0603048800000415031000c45880b1805808040030850f2201fa0356820400c44110701c03142d004007403039140c0c8010801441403d90000b08001c006507240390205248000183c1c4020b11260300504194408030300b03d00340041c4000050034401c880002d8251205400d100c40219050320171071640d403641100d42485122038500c03840003198440c10b0403840900f00341103641ca01000c0d5a69134464409944030519203c1d00404140d5500c0c01080c2540600e4942261a40c06100c05030700700340000f0181d551a000070300384000c181300f03c01c02e255000c042d00c12195220340380324615030003070207203100000c0560030740c81c8200c000058198181c03010080c242c0c1c0240d880302400c5000d00000380c011645251685640c0c1f505807000e00c5000c0100031244c001d4006507041c8140145050f0b84c1c094868050040000300d0314085411040c02030b04000c050302c01060f88240610003420b14401d02030341e004043c0000442010313407120034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 503496016 1250 503494766 503494769
    0xf05090d0f26040f0311150403051507170703050402031e0304180e21070c03030503160f200f0312010819080d09060605040f0b0a05041b140904060f 65
    0x105149542d15200ea82d012416000c0e40c0500e050030051800b0610210700c2c0d2441503000c61600410016120b40e54465840498004d50b1084595030b10010102c94083c09100d41c03e9840001441c05a013003c03030340404444c1c02c04d40078141d40e0505580d01d02017010354a05004150381c4851809980f403083c01c01c916450781d264041c0c400d841240ca1003c0c040c150000e410700602650700c007044010b0140d6001000c1005a06442c520300071540c507030420258000506a1030700500a50003a2a01d540fa4034120040e01c03130048100c51140104000d030007408250f650082c29403107800e03441102d21203440c030700a102c0920302414121101e19510011035510400d4290992241c1a10030b40310030780f02e6401c0d9074001e1810201c6200f00051042c4c0c82406515140c603119486400303007e02904c1c3c0455100d0b5503502103800c0303d44901d420ba0a10381ca035520042e06003408104000285000d413000c214900c0000d11240449201c03504901c2000398040c0340d040d448107070505594404000a0080248a0b07035880c034085494041e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 503497266 1250 503496016 503496053
    0xb06061317100612020d030f0e0d080301060e090405100e0309030601080109020a0f08030f0c0c0a0609061106090c010804033516120c180e0406110a0f05090d0f 70
    0x5002c0007081d5140d0f00e038580d0504c558043d01c2a490296aa0703016901c0e04c90350b0001304100a50030403998407072307601d410b0702040c00c0b8011204c11fa84d80d4140580140080417500f40d103070240380100c040c030000400000302c6500c9124805e50026260038490640c1d030841c0b054000c0d1540c5880b40b00d001294020040d80101e4406100b00e030380c40411681d9000101c075a00b00340c40340180540040c80040c85107018080207045107100c181c10303545d80706201030000d0803030000c2d0703002880020b001a0b01401850713040803004540707a0002c0010855850861030a50703680c0c035504801810000c3e000301040030980550203c10721154000c2d40000945040e00f04483c80207114000d510100044001082c155281b20f04000c03812102581c40c03d0f81d042e01e14202d08054070601d444a410060040650000d48502ca0385083c081c09030441c0070b0310b4a00f4203080c0320051b41c46841a070340174148100558900d42e500400ca0201010031428510f0300c400190300003800035088083c0107802403281800d00401c04c0510424841c840700d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 503498516 1250 503497266 503497271
    0x50a0e07120804090b0d0605090106080d030204050d020613050a2c01080a0b10080312060315070f030515100c05070f0503030708130f081b030a0b0606131710 69
    0x41e140114030a402200070094208203080000707010f00013030354000c114103070b1003c0c0c80d1403001503032551a0070072103108444646440e59605024032120130180003403111028607141c15401c4c0f90402000400214000030002e10440c00000c410b0710301c0d0203419022000b44001050200020b03a100d140030002071202c00d2025040914821752403000712181c3c3c1c503070f0603280c4c80300060002801590340d50207170407409400e00104003092100080c04800400041034052a51a48c1c00c070f0740d0505d1010b040c034000700f8001d48000d41ea0705000300080c090b0b200c051100780c0c2c4440e250216054880302d41c000024245040069080a03010a2900203160800711007203840c0d1281089a4100b661040382408091075800350030f078160000c02416011403041d0025041c0044412400443c2640e80c1303200e4641030200d540202c40030740180301084082c582840d0141c940b0b0070103070081c168955695480d8511030310300401c802d224010108005e01181032a030128405409002c84c8104044440520f02d952151042d110401060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 503499766 1250 503498516 503498519
    0x2061e22080408070f1202040518011d060f04030e1315060302040501200c01030903090e090a1208010e0c07111003020301090c090e0408030615040b03070f020a0c05010509030c04050a0e07 82
    0x5c05018101c1180c2400b00000345200b803a40c01c102c0034100c00b41c41201a80c644180c0040c104c0303030a20514071001c5002072100103880001481c941070900082c00ba00424495a0400c800f0903084001c020741100b08480b40078404410303000c0380c0300078070030100c50036086c1486801c04142d040c4c01d40d000f0410b0341c009032104500380b200740d00c00310006091003104c161240c0103840510810350203078100103201c611a080c28805991a120b101d9411001110803014650011406c1401c0c0020069128012261894081d40543c1016127449019001a0680d00344860006001041c0082160301403003180740280040010b01075504002d021350400c1c082c22a505182680d4900703194000c01c03000085800e921941d10580d5615240e00099400050202c1e0304000080340200480b070a4000920182200a1415442c0d003031005004001c0d112003a8041c05540c070100488001c00c00c00f841c2001151b07000d01e8a0381c0d81d07440c0c1340e003c681000d84c1d040f40241c001d4102003e1147c001c038281c03c4074140100150881d80c905 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 503501016 1250 503499766 503499779
    0xb0d0c110a0c0b090111030c06150604030c030213060806180d0512010302061803070303030903030c0807082a0d09060e1204150912080307020d02061e2208040807 71
    0x4800d0003400401081d80040100103c01442e009402000c10504010940d0300000e00c00f641594042915100190418003c102c20030341c04c0501003120302c2055403041e00346819070740c441401d22014003000c2c1c456801e040003e048005240c200001900302c40d002c2c0c0e0142e040c01340d40c4038820314052104840d41c0c000ca80158009611600c02d6a10304626000c4542040c1d19603000d0101c80e922840350147c0b0303008480803144581d201000030b84020b500c41c2d940054007000d01c0c00c0c0101110521b01402040100302d0b000d100040d94080861504000030b10031180803058041204800b201da000d142449000d000300700b00e2001d181580c044032241740118402d21006000407545174403403c1c00c002c82003008070b040c0403d0080c184e004090b01030b107880d0713410b100b00050b4681044018100a00c1c9080700c080e5400400c0050040e814414186140307114001040141001d52100c04820800c1c494455451242c10006203441a103401021300741e03060140d02641100e0a00b8448619440b901440f4228030500c0b8002654 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 503502266 1250 503501016 503501023
    0x50a0b061504090902030309090106020312061e091509010b0408010e010608070312020f100219030603050309041503211b02010203120c071a06010e01051804090c0b0d0c11 75
    0x8840e505038020b071601e030800700140b00610807440242d80512041c401c140103525a5201c0d54045c222980003980c03120002042942c82182c0204050300440c00100301d400400d030035001d180100078007180c0c620200d0340c2c0d51550707803042850a2055980b0023080000056560301c0200241306860102000344941d00c07120341040d0a03a000c0d48510035a030307446402300f00080780042103141402070b0f861042d05d060f14000c1600b1450030428600b1180c0051b400141140018003076152098150000c0c14180640b0303141d40c603069100d02640344201d00490316028044c1c00d030744409044c50b0286034000210a121000080d1014110f04244102c802180c880300c21710001000c0011000e181c254141e00450de032040c42d554201200074040e01d054901c040500c02480001c4101044090311640e81041c40c0c094a00a4001404150490311a07410b104040008103003844a1021a6030080b2068401280c0099117180c0000144095405413405000100e4501c0d403404441d084845a90074941d0703200c0c2503d44802c0219103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 503503516 1250 503502266 503502289
    0x22090605040e1b01210204060207060f080f04080d090803090d0908061302040906110a030f0606031406041a10080f07080c1209030d0204090203270a0b0c07060207050a0b06 75
    0x2000b40310a20083c0310762151541050611083c000d134505c0c10034104c11034050f6041504500050b03003001c0d80a1110a622030203102c01c010300c600d445003c03420140e1031803c2c01e1401600251a01c1400102001d40400d203400a0b0040765116040790303502d141c4404525101c49020000070000346680380000740d00c4400059041c0546d40d4031800c0c06e480d00c0c4aa0800c001013944141c1110384039100c1c5045891240040081d0800881989001c07480d440c0800300700c000c54680360050020b261a00d00c07140c0d80c0080c041401540150203985c001440303244900310303103c00001900540e520030069030b002c58205030310082c50f07805040f113594410019100c641c802e0703482100071180f4200302c060a0100c80c1c00c180d103699007260007030700c9141a64a01850060100c081e684941c01401800d03400001740072000c5540e4a042e000c21910004000903600a000100d44640c2d5414014282e0791181c400700d0100e448110842d0200366000b0421561420709103403031922456018000d80b40f4400200004105080c580c00c80c02 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 503504766 1250 503503516 503503543
    0x417010501150e03010b0a080d0f030c0e010c0c0306110705011404080732070303390c05090118050603010c120c02070305030723010b100522090605040e 67
    0x15031010500d4122980e022001030b0a03455900c500040c07146d41c8600d0b50803000fa05a100140a003d4144c80c8060451103412954004040c40d04d000d8200f0310381c6c0610200100502440c1c040b15070241410100344022481d007001e040315240c0044000c540a41c5e00040501c036110310000d100081e400c412910505008031000b0340311b200c1c101700401c0018102520b68200140c1c0c0310342e0200758074100384c0c0f90300f5680030ed4030700103215400104c082c801d241d002469003000e14802c40c103c1e403900c0d15081d084484009610401c520f0310108000280c20840c4010001001d4100542070081035039440085c50190001c00c1c4602c001c080c9000701268080c20117020381385111a280e140c006000c803040750820005c1410950700d4045020707400010002441c00c0c801021741c54000d20441e0911101d0311080310038441c48035001d0840c0c1e0324102d039404550316100da1140000758a414002c2d25001c14201c003a5209482803080303c521400d500003ca80d250311075222005135002507908204d0100d600c60075550700e068054a06 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 503506016 1250 503504766 503504789
    0xc030c0605270105060a14060403030807110f01090b0703020a1403060a080f030c06010e0f0c090a05180a0c0c020d02092203030b0f09071e20030417010501 68
    0x1400304659401c140d8114410a88007210901a0308226180000d88030515916035100c0040c0810b500e0191045c4014082002c01c01401c51252400528a031095110007418001d104002030740c5d80b4011070704400c0803d105d900740d800310390200f0f117447d00818214204941c006a180085000e0601ca4400d403074003003199803145024440e002d8840c00240c0c00090401d54030014482020034541c00a000c2c00c0036000e0110011a2114104111139050580c160018448080c19004103c0d40640340c100b085d42014085806950f50080c00c008a80707005034a400140c0c03c1400c3c40844c034000a4980300c0c0d00c0c4980810701c402c010550844c613040380c01e510552030180d840240540c00e43c01603e000c0c0112a001460403200b030241414000a110405042c01c40c00e138003003503032152030840314205641010303940c1c481101c40c60141e240602003c3e041c40a261006041803032034030b04004005000d12482c00c48cc140d41041c2e03da042d00c8461140340d032a441809407134040024401a41c000100501032141a00c0740709d10f01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 503507266 1250 503506016 503506037
    0x5070503090c13060506040e040507080f1911060c10060e0601170c0706050c030f16170711030c070f050d0305121e07080a05060a0e070e03010f1803020d0c03 69
    0x200402d90103c4402c80b00b402e40c0c1d50350001080c2d96004020070040c02d0300e26136500742c0e24090030080d04005d100d074007420b0306400c62099100f5098000c1480e41c001c00072221003110500c0681407801c200008850700a400800019040382c001000150130109012108000d0258944400c10b00b9a4039070142d91150110b00d00c2601d031800800b003c0c594680c8090091801c0d41440c181d40c40d81c000781d80d004c0d2640400b103940001406612a03402c00301985c40b01c500f50664581044d02c0100030000c500c2a4a0f10703001450f820b0100b84c0d42e42c0304101d5150180c00b00c208980e04d410181039002d4031605280b054003401d503a20f210024407402c008140c3c20300503406444160030404513180800c0d12800c0100a050104001d10038103d0906080540ea800fa80c0165900e01082c03402c031003400102c07072000d414144503280d203000800415018091031640300c0560306d0607041c2a007425012a0250800718118142c20781007251400300080110010301e1580e00070350031503034807800b40d04045d541401c2980000e00001e02a070358 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 503508516 1250 503507266 503507269
    0x305030402120f031c0e07060e1002030a0c020f0103020d0f020421020a0b090109330e0d020f03010e03070f030801050603040506010608060a0b16200616020103020c07031505070503090c 81
    0x2c40e01c6503160080c90101b000c50030329203118103140301900039001050b4103a07003940c41c81c03e140d5810b8801e81698002549072a20f40100500007007a0000001d00c50040f004a8651603413183d01078034020040310106220206c0511070840103504140549a10300301c0d19400c01d0302000040380c0e4041550780142000c540d5505021078011103502ca0303005241440030700000041c01c0d01e03020f182a6005100c100c04154003c1c5c1d4018031068504528400710200246070112074181e40e2040441450760742d04484900b1002c41d903070701103400740c0141b41e604415030001180c0401848903e00401807214425662020140e03203507000c001943c007040d44c000d0301c1c80d440340e00140426801600c2c1190070550080036010317039982d2491f0200d01944201c0390618000714005140080040b509480f54080c0d858a80c0c01000e00c40240103c1c1840c0074034a540c4c11010364a0044100b90b9000e0740c11170302d5086800003951911900c5e070401080010b61030411400e610b18000000360060f02c1501524081c01380c410290484991240 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 503509766 1250 503508516 503508547
    0x3010b060421020f090a050910110a0e0a0b1308060106030e100c0203040302040c02030c0c0406080d050304060906050f09060c07031b02011205090c040b060901091211030a0305030402120f03 83
    0x2240c2113518484c2c0aa9550758501c145d078404c00300d900002c91189403128a0f00c3c24221250620303c2c2e89824246000720403841c0409503080c01e0b22600c1c120f0000724441c8000307143c2018540c03210600c43d40000359440030400b000607046c1076034010b000f121056661150203c045410305850500703180c00c04550029140001d80004201c484035204172800d040c0c4a0700082e00325400f080119000d6480020102207003601072014801480b17007140c0c00c00c07a0341c3c45d203040281c6825114101030108500080050108181e03940241862500180200003901d003e803e802c3c0902030545036800280329200000b46812124021920704541c50b5503941080042500e001d1090641a4822070600c021880003440d4140c0c10300c1014800e0620400030000041c0040500085400380103d45005150400c00422581d0304400000101ca8000101c80c0300f0100900301002a00c070004d0005a05009149098052503841400749d4001d40c02260080f00041c8616203480e52084100e80c500982d41052103000d2601c0c8115 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 503511016 1250 503509766 503509829
    0x220302010e03120108240c090102030f0703050406021917070201030b030d18050111070b160803040609170a0f05030606210709060f0801031e060c0c0203010b0604 71
    0x90002203401c842940c001c07400c580085803000710355191007004202070300003081a031059002c4103103c00310b004404046403100b100c0061221295220000d000c07030182c3d1080088031310340503050317045540303580142c0307030050860740207100e5036005226605c00d0702041031041c4242100d496000c038100700f559a54000a5131143c00c184400d9051658410400099840901aa88482906541d103085241d80000803803805143c50f0400b9040203503e007100c00601c50700044007030940e80e450380b400c1c2c0c03280814100004024041c490007490b80ea00801808204034640d040030707003000d01c1104070a558032000a15100340c0d00031744a440c400151000101c000442c013070401103400003030290516107095000c4000e14030001500f111100541002800c003c5000d900420340320140c0403c0c54400f40f01a034620004104c0314060102828a0308180030216456881c5821800500e40c0800d0a01134a200c410001e03040710500305003a4002d500700103940312549070000c00c81d13041da0b0750050000411501c135000c1a060740d250f07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 503512266 1250 503511016 503511023
    0x100e0403031d0a030f0309230f071502060a0c0f0c060e0106032927032809080601080a1509020909030703030c08160507170a050d05060922 61
    0x490220124501d49040b080c410381000000400106200b494020001c0d1150948441014680b18014000511072103640c00018005800d050380002401c51140c200804030001803801d2203a00340008042141c2c80100700b00c0861902a1503280d0b4805440009540c88500c00ba000148800c65100206010306482e01e446401640001494204040d4140c2151482c3d0015181818440e061143c03080100c000100c1000d00380d00410000e0422604030400842001607004114a00b6900c3e95a030b20307010810f0b590520b80010302e081800490b0568403d002100072030050000d0480c940114400b10005901c90489003030350000c00107281c0b80d4440800d0120b50740c01e5040050b480300c18040150f40c56002d614001c0700d04c20055a5a4000342c900501210305494810040c05203840401c4000d1580320b41030344e40da10b410b040080d685c10192801d600701d03000d0603004824800d4046068640c0320f40c0b040c00b803c4a60501d42040125031580f000300a4104030803601c80c9a030440c0058000321300d030315400ca200c454510 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 503513516 1250 503512266 503512271
    0x18080a030507200a051002090a03150b041a1207080706120e0105010f1d01050105030a050414010903050408071712130e1e130f08130503060108030304031403100e040303 74
    0x60710041c0c0c1c4101e020f040982c190701e034030481180040c03040c24098000fa5041d0000214071307258610b0045001c0400510000d0100c80b42002507004c0440241c001d141c2d10080180204080000c602c4c8480504c14828182d40c0186070b03110912005d0540040c10005840b0001c0c010300032140790131011588003181c0c440e072100213034036030150b0141d42c2000d0194502a000c00019599000d0034811b210b4000d601d007a0015000440143c01000542d80000450744c105400850208859860b42032070883d4080c0c443da000455840c0c01020014140e006d0007800594140c40143c50348a81d07a04480c01105040c01100c20765a00003101003079002c2c82800003440c5c2c90034603e0302003181e199640610400c8020480360b00a07907a50100c0c81c041c4040301054407560081c2c8004000040c05e01d191246a0081d0003482c006056540c0000e0041000268840b50401801300800321202c0750b8441000035102d4006690440c040791004040c50101c00038401074034031035510a0301c014103e524240401d41c41c0000038100341c081c0359 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 503514766 1250 503513516 503513537
    0x402092a030103060c180609030b1e0405060103021e030c130e06010e01090b10020a110f0a0303021b1c0b04061e0213050405070e1e030a0f050118080a030507 69
    0x400240070750300031400b8a00000d003428007000c010f0200100c1080655100485060074000586c01260010941e500704080003295603a0b10070b0034810722102c10381c403240c209a4800304004c100c40060000d050302d01c00d03a101c046c03107221090300380951403911b001c90303606402c03000e540d2202c1d01380f02c079a0012018250001180714082109000d0078182c0c280c01180c42008070380c0c01030041b4080c0d4015489403000c10f5a45419000032607000948a1188134001020324404d4120b440c0c1c140d841208074030a0140003004e02644660320315019560704141500c80b00405d214401070041c51500f490802e58500401d2240403204007030313940350728030b4043c02002260320a544d401c01240b101d14250422190030844000142d8404140d240d80d040281c0645c000e51040e8200320802012130303404180541020010f489070051255007829250140555049440e05803107a022040140000600d000c0030040c00f55000700924109a4a0160700c2002c5490140c0091810041610140e02c60751003540d0200c01d5252588000c1d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 503516016 1250 503514766 503514841
    0x90b040b0a0c39120804091a03061003021504030809010c08040e0414010f05090c13112a06060306070f1e020d030e1603020108041502030a0507090e040209 68
    0x52290000004002141400040d00c030540c0e0802c40c00507110840040c400c0002d19a64828288914040e1400c1e0545400d0740c0314021410008c58800140c00074142c40c42d42c41c003461031010b03111035440241c1c400e0125403a4201c20810302c40480d410f5a4102a0062400c42030344015500910b542d00101c1d0128002c1200244120150b03480e14026841254102c0f28881c0e040041c2d82076034050404141c0d514a8002484918980004c2d80310701c5081c00da03091030304003640c0d246441c020040d0030703161740f030480740091409841c19060035074581c410000030b84c0d044800c484009a070317a01d203011201d80d901640304201242000b4000c008400100c8080d1801c8940001040922400d0440000c0c4450142c1e101f0f03014054144d40601614a01d03000c03d900030900609032500c5001d54400f180300181c140040b4401150070301400169030546080109c00565890801c084460010842140c000700081d1303010030042400314044202d90300483d0014882c1c00c00342c44420f4031144581c00c8030320400070b00ca000301c0c914204 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 503517266 1250 503516016 503516063
    0x41e0312022410140a0830131a07061b080a0b0d0611040807080c0a060f0c06050a021605030d050f0402100513090f0b01090b040b0a0c 59
    0x1500ca159015080340e584449080c2404000d500c001d49010b1022003c00140900b000c2c400001c840190840301d407242040000b040d1494256000410075000c0c01c4c1441104043d03441694440103110518400301c072440031000107440c0200160300c0d2511808800401941507589400c84020411802c01e43c50702403140d484000301ca03511402010300b248455003510b55075402850899001c080380800b40700c900840c00008031180d4101ea0010030260359443c00f03c140161140640e0060320024007110381351500d81181a07034501e05030440901c00c482034440401d819101e007040d80310401c425101c0d5050b44d00c081d40d40c0303005000c5c020154810150f0130710090310b840803c02c180c00382241c090f10183d9520400b502180342641c00c01030040e081407603d8003e00005071100312115040000510340561510f6141da0007192401086e03100d180254100305e8910f00d1080c0c59880140400801d0700d0324011255981c04403180c82c02540305501d039000d010b018075014217000320443c0e0003d62180031410b4000d40c1c2803002403103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 503518516 1250 503517266 503517293
    0x6032f190e0616020405090102032806030f0f051014150f06030a32040f320d0801050f12010f0e01020a0f08090a03030c11071806050d0206041e03 64
    0x4849100c0070f800b9802c05121311508484090001d61552400c0c035902d400400d96044a100e00315050303078201c000199a517200c9000f840d4811084418900a814041d031a00c800c04400e481c3c45c01240f942d840300e5030a0b4855075074075100d8050b91608554440d95620b8071000800076540d000920350891102c20354840c40114494a952580001c0501c1e24454100800502410411504402e251405c80c1000c4400c2015403255100c61409a0f04030b15281803001e04030340f1518032220002d9800343c51b500410840041c0392045030a801c650314000c0c80e81c022161000c0a109081e042a1215541c850b1401d1450401611b01104400032514000406840c1c08072207006026149903540890800d41996000860341c2e40461949402013540c2000c62002e42c4814840030010203150b0344011301d20905002c0c01064000e2054401039841250340d81c0c42030303050710320b4150340000494a041400b081d28904085042c0300d250700504100d04140c2424035000721103d10180d644101c402e0f11a0000c001690841c60300c6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 503519766 1250 503518516 503518537
    0x206071403031f080304050d0c0b0408150a0b012309030604051006060819020d090803070e03010501060507081e07021f03060f08030702101806032f190e06 68
    0x190b603450400303103d25a659000e005900d004030a100c007082041400000d450a5a0f03084905001c031800618000096210550001c07030500c10200340050107680c082141e0010080d05030004070a5030f6441c006030300b15142001002d004c14600b10780c809080b10403070300b0251001c91a2120714a0302b603c03880020710f041c00481d0211686d0340001440700c02d9400078050709005018908050806080000352030707000d61419600000401d9001c54103007003511207504844e549540054426549091000004003117000c450081343c025230070403000250703442c422030271207020300e4014440504100c85070f00ea0481303020340500c000c00748800610010000d680c800b40086250b488800f6105040c01035094081d040d45c010368085850344c40501801c010f412170100072110229070449803503d90070381c4100c0c03d43d1061820324095a50b0030301d40c1008204036400d0b41c890305160034044045100d0905e00348a824203040301601040c03100200b4007908801c1c84440a1f10045131009080104012520746c1c0415142e800c0315103480d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 503521016 1250 503519766 503519773
    0x100c05090301091124040b070507050418110303040b09042c070303080610050f03100e09070819030e010807020a15021903060803030105011202040312080610030b0a0b0702060714 78
    0x1000075107008051030600040c806501c4c1017488141c16405024042e501c030b000c0749454005070381c03020020709100d42c4020701001081000020780e00208400e130301c401307020210f5040040741805101894004241c81c00c517007070320140c145094000414000a01425a00c4980d1200d03402c0300400c641c40012091755660038400014004a49113060050500070045d103143d000c0d00451075003081c0c0d5035004089549190780d5400860f0b690311906070702c7c032035004240e00c207105407075004090054214012445000320b03100402290764880cc81050b081c0c200801e040001d012403c16150300c02135502a1419640c080e8850055442200568503920884a003ca0884002e0741d4001171030710304411042c0348403c40040c1407a04008090070035200541d00d20060280341d050000309129010100303101d0b01160003a592102003c0d41a0340c2c1454060400c1030700352203151041c625040324101d49482032041d00382c1c41e00001c004901007881d020004285500500703040c0e81081d02004003501084003003940380c50039070b9a40000d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 503522266 1250 503521016 503521043
    0x200303010602010e1009050307030c240f0b0105040b031f090203192301170106030f1b05060c2d0d1e0201092003331602100c0509030109 60
    0x840c10103071300c0641c2c00300080c505404500811f20000c1a00c400c1545420038807040341c11401d000308200445406100c0d42c0c0780e4541e8a04100392180c020a825125065051103007030440c0e030040d00c0c0d82c0101e000b02402d4160520014640075072414074001c040e000380c0300b0b0305525034070307100450240d0f80700710345003141030300341c40c0300034101c000544505448004100520400e200340001c03190700b0344806210380030001901100d281ca050b0020350100009503030212201100803000d02d8142000381c81d045104002049519000a16040150403110a869404082c2403020081e00c000c0d1a0180241e02d0500d504019543d0708022a03420450903000900d1611110030000384800080524542040180116410f00207480c00052020b00300440858408014080440c14000441e24140001c19001c0d11040d4442c05100003440081070401010301203010711403a981d0388a4402e1205482c000e03d0001a40006586451a4140e50109000104910b09945885005030000c0e0135220602c00996030484060716 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 503523516 1250 503522266 503522291
    0x604260406090e01050d0b0402100e0d0312050c0a090312090e2a0f1e070501051612060617040309030c150806030601081518010f061712040620030301060201 69
    0x80f07140100821103001054410075500c050b04070310f001c1c000034000d014411140d45064080d4509400d4010042c29481c0001d180b82801440411078510500c46540fa01c0003150b214100c0a040f0b800c010101d444000b0303410305d5580c0b9008510220448401041510a008200640a04149801990700740c5210266144c1c00031201d0300075031503403802501804100f03d04c10780c0d082c039503050303c1d98204c8064110307451030030600c0107040301d10515100418551801040001e00c408216412207402c409503100c15180c0b1840010004403446400780e072000c15149198565001402024158061b100345425920180c0d01e03031790414001001d42200910200856400488a5000d5030842d0301403022002000300c0e514200d5030380e4031f5400b480c041900011358a00005c840030200582401d5540054008001c0301088484c00c1004190074000c54240720800e18500054510009628941c214003401c81440e141c0340c070800361b034185d00308000344440c03111090400d84061824000343d4004c080940010900681811 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 503524766 1250 503523516 503523539
    0x130303110627030f030702030406021908030f0613110910170606070305070b1302090a1e02030a1404050c010e100c0305030c04030f030c150608060426040609 69
    0x4800049038445400c101d2059948440a5072000d40207003070b01c0e090000180c0c05421886038916141903408000144129150700000a00840c1c41035420f8032100011222103586841d2000406812a1000e001040324040408900364121800600a1170003103003084482060303501c00c0c90f131a0241400840c0315a220304001c560007204080301e213018203a00110047c0b00e031035648090304641c0510b00c04120b0500f058003c601315415960051941c06985c6800c1c3c00e9200303640503180040703020b0305402020401c20000d5020740c1e01d10380105184c01c14480d9894075010000e40000b80408481600c07038a000b10741440191010b80258052005041d03c42101400507158034007048800b4001c07079031300209201c1c5560120050b0803003a41031801d2a6203480d00302c40405240201c0e080a02035403501e550380010507400142c1c031500c8510845e0107c5c44071514034011001c440c80344c0300e13021389034001c00005800901c801661241c410041c160b0903003242044400c400d4179800c02e03005040490903501c414400d00303c05c2c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 503526016 1250 503524766 503524787
    0x906010e01051002030f0904060e0c0c0114091903020705130509010507140d0207021807020a1b0501020a2303040e100509061e04090b070f0801210b0c0906130303 71
    0xf62840700011042032402545d900c207150036400180000324100c00b04d659140c201c0b200802c040840c0350031500300907040300348950101020f91641d620701100360a00305c00e00c1e484030380b0848182018102d02148411185100c80415008908600880101045680d40d070f8090506103d485480000d180c40c00c00003441c01c4900181c90a020701c6170b03101c400408503100ba0210350114070040005600c0d850b03a44041210300446032499804100b000e002c00549642c001082c0c85017031300440303a000007414103001c000860321050007450b0050f0441c091000100c3c1124680042400c000c210030951511241610740c20350700aa001401e50701c4c2c4820502c200301340d010701200041c00d02250051058102500000c886620455000b6264820015911115607899015880c0709810000104203460880710082100f600c0416540c080740a500006c2054840e0340e010301d025004250010801d005261109aa0381d04020b0559003028070400104120783c903004080d00c0807680042d80d812000e1f0035807401420f9981c0d81b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 503527266 1250 503526016 503526019
    0xd0c03090f0e01170a050a0b060f01081006110307020a140a0e09061602010f06080102030714040e0f06120706021c0503250e030303011d13050d0503130b0906010e0105 73
    0x10000300348070b158401d440180c1165510400d0350b4441d2003400d001c5040440d1900702078602d0003154044424000d8400100f031280d0821039824154590a000540f030100c001d803000c0c0140d120300310040c41f540b4080c000b5480c03000307018403c490615540340d0004e010308600307800c410400b103510f420034082801c1901c05c1101920010b54445420300d0030044c01590b9150003049000140441c0d22030f415418007e502607202f44840c4501449010344580042c1d010394030a844207000140b0341807000c4034628026041e60305075508103440700e145884d107804102d6140703c0503000b6039000c800a510001015000c024210060145030003030010708500c030300c00c3e41c902c1b401042d00c03000b40310040040010341e003c80c0c0750002e42d01071865510350032660b80410864056400d0b000090705440000300200d0b91480b101c10751031704d1466072010201e03584d48460141080c01d000c07100c002e08540c0500c030240e0586010300c000d150701c0313003035410080d10b06e41d01901d60902d03910b03040c0c440d030304c1c0c5420200040c00782000c0e080340d035400b42c0790 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 503528516 1250 503527266 503527289
    0x412060e011107080a03150e04030906080709050108010e06180411040b040b0117091f09140114010e06031009081b01050907090e1c09060915050712020a050d0c0309 72
    0x6a100d4130741911440001804041d0380f40fa6944039541d50240041c007610100120141034030b01480e000d0b042c80300600628020600020010350070900c20032164040d00d070180e440400356461b0014500001030701504961340703c5041390845000140026400703119078040d02070306030b40982e03400c04d2008482c03d14401e21300807801c0c80040c02890342c002540c40400c060b14000f800c05c1e0355035040c4407418041180f1201049203108100c0d07240b0715516402040c8003138040d0700300c0d1045d009416006401c81d20610a0584e441c003c000042010307151403101c2d0741e0f00220140c145c980028400282d08215081384a0484203200080345203d05651208011650513013072a008100310f080416081e40e444499104220380c140d111845005800c0b814001280841e14400e5600e01000c0c641e8030151940350b190185400155904400003084280045156607082c2252103561138680607841e503240c008145211a01584100c1c094540019000c004108650000c0d80e9140020076403803900601c0703084c4680c011404400c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 503529766 1250 503528516 503528527
    0x3091221040b0a081b03100e010b0c0c0d151401030b0a090c120305190207080609010203130f05030c061005100806060a0c020102150a0606110102070f03030b01050412060e0111 77
    0x9080803515002032500703040740140d07503039061705400780c5100d02c02c0d1a031643c2c04014410880f00490707558040c1c4900607408100da0780caa0641c2c10f500d00440300505241c0d8007411031101c80342880b40c10014510300403412002025411702607a01607901c9601410240b5084400400a02580246298001038024070a00405d00e46894041c400041402404250007124aa0004040c01601161000215004503c1406101e08400381d190a200d115801e05e40c0560000180844010700c01c403840b0301d0a402408425035030540b61117550700c40c82c5508558501c820004032718201c400f08401e5105820744401d480489003464180a030030140300c0700000c01d00452174180011942c0303000554103c0d281307516010f80c0d11042400100e1401017241040c039a580c1112040c000f00c0a00e81d0000740580c0d010361250501c10303000d001081d08074461500050300d0704000c00c07000030000c2d120750070980c8c03801414908541072689400920706001c0905004854044d030f10440b412030410700703000b00800b51503000c1c201424503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 503531016 1250 503529766 503529779
    0x70e0306040204051e010906032306130305070b0a0515010f0e090603010207150e070f063f2708070f2102160f060906110309122104 58
    0x400015200920070f603120800038420750254040ba5011802c1040c90010650392082071718000c0429000c10381e101642c0741e211340c00c0c1c500020001d0406d40303051001080705541d10400401440d07400301d012010818100210800f043d611190b450007051030000001e0b03141000141c03900d6185401d03030441c0c10312004a102c40302071a00103900c0b20034944152008000d0303540d0741c00003e00a02c21034000034107507420b00c41e05140d468210b900c0384240d001d84404841030b55403560f49800349801c1300d10942000500e8241d80c681c0c07010f00104288500040b200c981e00410030148481c45800c5517010380e610b09243c1d141c409124900c20080096201411109806071041485e110803100b0f100d0307113102034080c1102d02c04d4201040500c40b9540d00c040319080c1c1ca240c28241291000b5150f4611160600728060003550124140c05d41141720b40c00c480e001e842e00c0c0c41c03031407900009980245c00c17841160240c6c041072080c86015114224031414428580c07016090315445503920568015050100e030071040c20500050001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 503532266 1250 503531016 503531023
    0xa03092102071715040206040308040b220506040b07060b1017010f0510050a050c011103060f0f010e0d0f0c0b040303140301180b1914270a05040c0b030c040608070e03 73
    0x102c00365942c8001c1316680d00c0c0041009446154002841070300c00007400524942034001500d0266002c80c100701e040c510344011510303255214014aa07022074108401c000a9500fa80107150142c070030300011800d102d60900043c10080104603001c00315a4001c1c8642900c1c03004c82c107681c098140740540e078200c90300b0800458400c0c5020202102407000015568900b00d014100341c4060202c070200a0005064100a030f2809410a03500c1034090b004110300c00c40304d45003a00f0359848110060790703540c411a016008101d8010030720007064441e15070350f40000b004500c1e070f0710300c4502900c03581003465503840c030710300e401482010401c002e840e28a02c20f100610184004c40003d0500600b80c10000c5409012000060302c104149241c2403140b0940c44000140403082d00401c40408608403000107406041098800000c40b05c00e6160981c801f1a0001440e80801075000c150001e001c1c0520003080d513110a2260380f103a0060314110b91200000c24100081a88041e519034800014a8000310b01ca0703c0c2ca020035903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 503533516 1250 503532266 503532283
    0xf0204080601050105031003050d120b030307110402030c0f0c010b011713061a03100c080a020909180304030503030702030c0705121f020f0a030f11030603030a050a030921020717 78
    0x100003000000c201f8140f560090a409190400280c0e005220b0000014180d40105128603484a003081602c01c1c107464040141c5440c1078000e0b25108030901407a04001c02584002d00120f0891000c1c1710034011f50300c0b801c018241d0b41c880b900c000945860b81c0340014209a800a400c510a40340281c20031103510034140d104105586d01c01004181402207403105207451104580f4940c0500c500d501c56031154a2607040701580e0141a200c20070207407518210702069204035803e05410114160228240d58500c0c08002d400e0450001680e00b441d407030b6504c0d00c4c190b5006603a8400160b102040ca2088804140b003440300134030080341c00d5014410400c0700591290540c1c0000000a0061f59400f004403045404031248000048422039a0755114030001e40109400403412101c00d25080544040440342800c403401810000e0085060400c03611044805511004c80042015103650308000052040400002000e040070140131403003404140092828401e030f8000351a00c0c1d40d40d6901880b284c00800c4109 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 503534766 1250 503533516 503533519
    0x150a03090204090f0b06012a080903030706090803010e0601030917030702070305031b120702030703020d0c03020a0306062301053702010b19181d010f0f0f020408060105 74
    0xc2681003800010000c00344103602800041c071051040041248600c000c0d48104004d80312050301c1d0142500780b50821040c0368007200c980c141d416101c400b24403d40b01811100000800310380c82c041040d0b68001c10b40d045410304451000e800700050004080300200d06a000400786810071440c1a1a00d55000d0010f500e100301038668000800303e82003620901c4031b00042d64004040300c0d0385042402d258203a01c0c00800d9038074820300606814000e4044803804403400c0c903400130000c0559a04540070017030891100c030000c96000b54a5000040140c031948a030b01d000b14010100090081d18102803000b1401e509040152540505000c00c1d106030380000a6900c60380101c160112013000c03d03503504000340041c50044c00800036160340301c010b01da815007101e405c000302074880015881b0240d00a440c000280c0c011070003001d10300f40a514003400b86500411080c0c00044040010007006000c0508450011540185030f82d200d4841c0009041c142c02984160f4134407030b40031807401c0c0c0383c80c1101d52661018091076 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 503536016 1250 503534766 503534771
    0x807090225051603030216050906090105091f0b0a110a0309090e03160609060e0f2e0c0c0b01121a0711030a02071811030609040318060815150a03 64
    0x801c140841001000c880307042050004034225107a08010350b5484002c80c40d0001040385c00804500c1d4102600700343c1c01402c0103040341e40f80341d08000400000d170300001d00304160401c001c01070020740806540741c3c0c0d00415070310070408da0b1130300030210042811101964008040d400006074000095000c00c0e03038800c072135592000080180c1c2032908a070447c811481007480d44c16801d0b0241040c01200e6000c074031454850340b0200140910040810303107440503000018090340040c0d030707100b5030940540305034421942c8400c00083e0403401c40003400304480e040c5c049540043d81400710307807040154a84500e800340c1400c003109690307031040781d4903101c805030b070000100d07070441041c03001c1120107010f421020244110403003526140e000b1004001d50f1005a40304010341400300c12520000ca411500c01c50301e95510110f004c51560f51504180072104401400032020440005001c00e0300302c48460004010381b0090b590b0006500304182ca14607000c0d0001c8006210f0310104a10750030081c0342c601100e60891351130501 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 503537266 1250 503536016 503536087
    0xc020c042403080c010b030601061202030702011b050705010b031c0309050a14031c1107030309031403070201021c1107021c0204020706020910021c050705210408070902 74
    0x3001d64086444501d01550411224040100619003014000041003c002000795000100c10140e64000a11440000c161500c0c401c2d4681105074008617402402c3e1300000c149507081c4440e04800400202070400046e40c0400c0003020008280254192450f00300e000701012007050303aa1240e041c051010300c2d0141070351802c44c00c0801005002c5611141d0b00004071401e004038034015961a81c0c0042c1c0f080042011540c0c1d1507542c600103109015000d40500307003490800701c0b1a0307001e9000300034000303040e0107125000268a4509e0700010042d0320910036580096250b0b004034104400790a0100c1b001040c2600f810f5001524009200c1507447d02034044035100701144505002d001107412060019401071700005d02c58040c00f0268008003400c082c20b49001083c400001c80403621402000380f10710848092500c0d000007940700e803001d00781c071601603000d0752035051402c07071290a0010105108944400046800c101c118400d02017100144a22802540b4095150444110111280c00000f07a0300d206801c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 503538516 1250 503537266 503537291
    0xe042004150e0a030c0e1609030b0a0b1e1e03060703150305010c0207060f0c05070b0d02130e0402030d0f0f031a0306072a02010206010b03060315070c050d030c020c04 73
    0x50389008014042d05070300c4a544c4a0404040e0a02d60340108a0b039501c3c1030022410808800041c0302c800b0713016959041c8090700710368501c1e46102003c1e01c40d0009039250304210140b5581e00c07400c100010b034071511100f07031034044c002441642c002c6082440e40411348410fa81c11103442c080703a40d0307500048a10300051848140943d2801c0f0f200b0b160800b41840d07190808040036903400140b610b0039913865449500e502031200d207080300e80704d0340c1660042543c0c210701c00400c103505500703002e4020240c1c0c80381c0242c18400c0c481380541c000035040d4000710707021030340c0805e020950405001c1058502080e00c1c0002d80c42103070f4800501001ca500b20b10310201680c51030700f8030b003154400038141c2c040039000f000c0e03492508080e4402041c81c48800480005018000460a1100e01e100d0180c50f180e81e068018041503843c100500d28280c00040c0110340600504015056024160110b01c0c072601e5551143c0c2d5038003c05040c403501e0f24400c0210701c4241490441401096600000ca21000740d07030444010450b04240103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 503539766 1250 503538516 503538527
    0x3080714071701090c0b0a0c032a110f01050903192105090108010503070503070506130b191103091c03020f12040602010f1a01050309030405100e04200415 68
    0x34060700c10115481c000b264082e106400c20745080c1d00540680c2c1c0082e032100c001700d109128001525010807074001c54100020f014070181d1908410040100c01c045840480b20b56600a06140454101d0710341740030a029458042c0e0380003000b2900b0318200f42401d140001180d5207a00000b001d006e9a81c07110700e0b24042200440b070850452441004803c00c1030000e41001d0840c1d0072910503a03000c0b0740540c001140a050001c1c00100b150001402446418902014800319a1010442c1031f0526080343c07001c82c1560f455401071440c2d000c12901d4a07150440e07004002c10808016031fa00320980c0007000000c645a480d2050215040000559041400423914050b40741005108082d100c1c0d0280c0c00c1c0401d80005050090400c85000e5002480381007400485102207804501111545110903020070302c5a500c40e8014580c4440c0880c222450152a4000542c0045107405044009040c0c4c84d0301948604160141c2281420680d070b1150961010a240d0001401180070b104e0500076400e840505007403045 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 503541016 1250 503539766 503539769
    0x1060903230a0f02030c030c150a090504020406020a031803020a0b0a050c06010303181706070e060d020c010b010318020f041509061212090b160f0228060203040308071407 75
    0x1208488000701e0b00d203000c0281d01205181680b2030f015145102c041c40c1400314022031081c0d8011b02c43c4240d0300040da400c039080d410200000d402c1009811001c211511103100800192120350002c10078a04246402006180c00d4821a00e0858003100c0403c0140c5800076110b046d140f50146180d1650f2100c3c10031a094091560481c0c101e200340300c00002810f070042070600c4c42400c1618944080b58403081c440b00c07000c403c441100031652040c0b0020b0211842622485503098000700818075022070b010340d038000d98110050410007a50341d104003001660b007511801404800d003900110f052070280e00001c0024000d01c59481c000d94554040c19a6a00c3d079095010203002014010000f503621071a02e41000000804101d030398001800d55109000e008002560881e19030b485058030f131503541c0d080c070700c844018800704551018640741d800300141c4e218656075200c00007400e2882049248550f11000d00720a50340405c1c1550801c00050002c54400c800b190441d5400807018001c41c010400035510300a20b6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 503542266 1250 503541016 503541083
    0x50c0f0f0906160f11010c030518060c0a06020d0c0c0203150a0b06070f050d110a1214030a091203480c210903060509120a030b0109080601060903 64
    0x1d9010110030840420741ca8208140281a100c11702c0c0c13100e81c01900c0d204072640014002c100f003030140600982c1c0e912682441100c011300543e003043d00170400285000342c0c42404484450b0003188003c80324a13140b0580682103000e10344200110700d140c0100783c403440b4606514900b0b21015002610040781c07a005510350840282c041640d600590401d04c40f00044d00e02c017210700340202201040880d218251400c4a42c100401410080c111641e640b00170021003080c1c2d000b40131802c0f0072241c0349400c1102039440713080c540341c0105210b01f0624264900c00403080c00c01c42894508582004062fa4a041c0d40c4109101005554100d03803500c0c0c80d883e04070b2040ca01e011882c402c20255403075030942c002ca644109074850207080816208c140500003000318101c200b44001081b400d010000304111341c100310303005426202940c3c100d02c40751081c40036036440101d800001c02e403242d100b50010f59200d1614402011000054085541843d50007401c0c002c8a02c03000d018805002c0285440011030071104d0050880b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 503543516 1250 503542266 503542297
    0xe07081302030f0703050610050916020c0a0f0e060102151f0503030a0c02240d020a121127130b0a0f030c030b0105180601081b030a020409050c0f0f0906 67
    0x1074003540c3c2595114540011695802100c02080180002d10307600d800791031008140410540e0390020a08425042d036005e04110b10039003c40d21060340320300328003401800a0305001052142000702c5030b00e0342100075100c00d0441d03020007001c0300e1100040d8000c0360024138520760481961200162510052070796041958503000000314198507c2d00b0442d822901403080c3c41d4000c0c000701e076800c041907141c2181c4416204003410003250042c1c2420740e00502d806503890070900101040c105a003011100510318806040200082a181050310b60707111516640c03a0001d040e81204c044000b25003005e00300d903080358405840f01c40c82d100554a00015101900001300c84100030395603170400c0b02d80ca800300e100035210b42e00b0306400440c00e0300b0042008140b0030314062540c603141e101c880046402060052a20103108a420011f81b031852641d0001c6004803940d4402507203075030030f044c01c0c4800c50f0700282005800c00070801c00405100c8508040c1c4000c60080c24129454252140125090340300e000c03104e01c0d0504 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 503544766 1250 503543516 503543533
    0x1303140d02040902310605130e130618170a031b02030d06090b0108400b0112021f051b0307060b0f0609040b040908130e0f010e0708130203 61
    0x40032a4003a03d00c840742e41c500100c01600c41d4030f4944007a04040c1603040c185c08001400c0c4031060240004160003e180f10500d080f096542c00480060303081510350b40060151509020180300349400380014201c400401c00051006513034130f501729444441c00303441c0911008a006854940a98000c02458442c00300282c418080001d00075120360082d0068050700e46031980104010486200e405031002041e150007010b501c1e41c044c01a440d91113164001440301d4412100007000d180706502e0510400e05007001001c685140c03800c3c10344c420058100000040c3d82440d590003503918600080c8030303032020030200e0001540c41c47e01100c070340c800c001038201000740700c0c071031250184400402030080e140a000b04010302407a010030444c60000081c2c4055020713205003e030081901c5c082d4808a01e42400500005403900389549060740344d04001142c1c07003281c04401c2c0400c030541004204d5580b000e16055407a12940c10800307000401c0e080076008004120201000501e51054101c002c1c0002d9002000ca500d8038 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 503546016 1250 503544766 503544779
    0xe0d02090915091f0e120f040f05030d080609090a0b0403050a02012d181b1505090915030f0a060203161b020f03160905060a06081303140d0204 63
    0x1910040303081038540a180b80094808030001c07030014005407016540314a20508840c45902074080d52803d40f10502a60741d0284850324264018041a441200c906403201d00d0030400c1031000c16594861802604807407001c1440c40d40c4147c0f081c0d844030044801581c582c4600c4417592030b10840c980c00901c550300310001d0005054100d400f8000381d41007a030080c0000c2440c001641028182117107240c500540c2a201c600c00c0da1560303040b5480c0090240c482040c1144140c03902e488900c281040d03000f082d082d10710300340810501c5c2c0102e00039806907414528540010701c2d0200c0c201a800410034a8050602a410702003541d0030b10100030780d281c1c1001264400d00b05030030020001e5100b981c851010281c2c4002ca900018000c0040b00f04140198800007082c2e8415004c2c800e43d601c100702c400c1e6150003609550405142c0720803039034010f13191881c000945442e000061240343d101540040c018042070104201402c00420401d200d5a945450002842014600404400d0141900c285c01c06070001c200071401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 503547266 1250 503546016 503546023
    0x150d0204080703150903080103170705120703030c050f03040b040c03061e06141503040c0b070c14010309080319110703032702060703030509070909050d0f050414010e0d020909 77
    0x15640543d042e0a45181c1d603018040171508644401400f04910b0001000883c009075410240d503400d04180c60b2418945544050034501005050301c1c2084d0085000d9040c035505104920030303502039042280c5811801c6c210000b07070f80001080101107404007000035041010844010303004503400482030003500000580c1010035540041740c501030618281c0000b600100440740c040300b203c0041c21890f004001a1203d484a5000910948903507907240d6002695003000c1d002001101d0040d60521080c0b414102100d9200752011481030400d41400482d2010a10500851380c0103d0482d191400540681046202070550b00c1103820100c1390100741c100506415420084c0c0089000088031441e014155042e40411442c11010f074000c80306006460000340268081900a210354085400301035588a00e07000b540c41182c0111150f400c040c00410203150403101e4002e07003205500700f09040504051940d0b2900c420864940c3c1081030034142285241c54201e00d0900141d000743c46400e05240203406551b5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 503548516 1250 503547266 503547269
    0x1b0809060d0b090a0c09060c110d030206010f0e060f0112060305071701060b070314220b07060c080105100311070602040b071e08090405060f030106180e070b0702150d02040807 77
    0x305500f00009440a203c0d00c100f51505070140c0b41c0380c0307105080242c100d400e01c406142c201e500b041c0c030100d50350b81ea070340b81c0b03480c81c2c1010711a6002346600d60504d4492080d003103681e88404168030084003840000e075140011519928020300e0001d1030800e0300d9240c60094650b590010749580105840428003075441564100c00c005208001e00503159200d40c0040144140705000d00051504074102411100c10390017803d2070345020540c040007030f60203414145084580d5001d900d140038002095000c1040e03030b0040d0390030021103081000300d80d858040410b445101c03080503101015626203c41070784151680030755490b90b80281c805c64940c1d46620002041d94010641a1042c00d005c45103040710605800074100d10320340c04800c60b41041d048a0900c0701601300540401d600c08103030020203186440906c9244020010f01521203082c004c0178210070225407100001c08869088100c09001d6099440111005645d05030368030700030302d10505543c0a050040e205000403450000400145048002a1500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 503549766 1250 503548516 503548519
    0x902040f05180f041502031302041a090c0c01021e04080105060d11150903010905010c18030317100b040303050430030e060c01091b050405071b0809060d0b 68
    0xa003110345540422241074046601c0800c0c03003091000280080444062040e00b00c1e1003420107010403030a20107668143e030011140e200400651460030340139482c00b401044031500c8840c640110440126012540b1200700500c40001240002443c1c1d40000d000d50490f1807081e407601c040200c4c0032071178800c2c201961151040d82d62540c204000f00c3c2c02490700d99010315100791b10208000444e0209014005155a0003082c1000d01c401481101c0709034500b80942c0c070b45113104600000750030004001c06404880c1d044242c285244c000003050002940049920000d0384004044080310b6490350031290620360709402114039242c010a00104158009000e081960044003540c40c80c04036501c400b810309600c0145a2005140100c844070101c1c0c001c804c00f043c100c401401c0f42c4e01c1c1030a044102c60a68071070000494a661500c4002d4003000c800464880281400319400c1c820f500b0000340c010030030180c0d402c0001c0d01c0c41c00c580e01041000307400000c076000c0e1000640311640ba000c40c6104000180400c42405 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 503551016 1250 503549766 503549789
    0x1005251b080613020607080a0804050f0d0e01032a1206050d0c03080d091b03061a03032203021306080c0f150706110d1d0303060f011215090204 63
    0x4182440c0000d03085025540c18100400075690307081d00203e40022100426600301c0ea0400814001c10704c00703070090913485c0c0d16032a40e0126081920707003075203001c07418a145001900414468204181d22444811100b8802d280201c0e00486504c900004188280b209101f80702c6000c54010440c1d03003020b1094a08022000c2c204481966901403200301c1c0e070701440090010003019070520008114102400759990140c1000800701510754640c03045441210202140f5910144104108085400740e2200f2081d054074485400300701002103952801071105a0348140c180d5242c1c1702d00c585252040d41d00440c2c00601c2c10055402c008440c0c802032600c0d004101d00f500039a1010350300c2d4207041c10060b040a1000e060035800d260404030508c00b039000104100e80254440c410018503125000144c00d25103824240000d58107029820a884041c0d080d090a801350810320810400780d441c0b200307011782c06000307081c203d80b4002795060740e500410a0485c03100c0c00078004200070400880c158090710035600d000130030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 503552266 1250 503551016 503551043
    0x5210304060f1b0f0b0a0b12010209130908090411120f0a180f0803070c0f0602030f0105010c08040506090f03010e0705120109110d0f050604030f0905040c020309100525 74
    0x310300f8034180e6204040c0503004481d844100103040d0149903507010000c0780c40020105030060010f00804510103144216a40100c0e04010341d24180f6840500104001d408000824055560034254000c1501d9075228a42e030f201460008240001260210f034505007807030300380d460000000d00042900352034020302686403d071048080600e1641d11a19030390002181d04040b00c683ea42c07500540d20003021501000303100c000d0040010240400c0b1a0030a04c02c2101685a191120360f510b1107041c16401745041009807940b40021501d0a8100c0b0141c90781510681d03520203603080454460718040e000f2a0f0103602e06400d110002c2c00206110081c1c81d011654a0071000504410310b0994241200280c0151042c070003c00d0140b0b020b50030b0b00d81c02446040302200c02d48003601ca003401c2c104104c50613004030f02c200c8191503c240c0d0040300f49000d80000c49080040f0785948a0080d668040c000989001c0c00030100d40f03403036550269041c0c031b0003a69800700801d42d0341c01140341c03c01180d80c0f940e812075842c01610007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 503553516 1250 503552266 503552297
    0x6061c0215030f0105090705191b0c0e060f0a0e0a090c09020a030f021305190504060303080702060a02040f09150503060c0406030f02030925180218040905060105210304060f 76
    0xc09400347c40b01d0703a035441c00c00c3d03410303440540402c809801238010310101468101d09121032813161710b820343c0511404803030ba40c03a1034140d00000a004120600c90180140207100d070b651001400c0050341c80b000c240201c0b40d500d000b001002000c04000c040c08050343c40704c0004021106400a11660003669004c0c03141c010ba040c109070680c000e00b040d10f64002d80385042840641001404a00d40c0d4281d0400860800d80d19401f24040328444d030401d400080448080100ca0380d01044412f800c210107160451030b0500e81403031070403289481d000d188102a150a240d01000c0106085140541700041c2507942509003079201607800d510034403410010038207000100840768420b03c01d503441030500170042c0c00365507c007030b00244011194280c0c481c111000440041100c25809c8a400141280303181c0c0140d0714803c0c0c080480e0810b41320f00e082c0380314500f1302207440002500403502504664051b1501c1e10351031094158200000c0c07545407030110511002c513001a400d9400b14241e42142c01c140c40d0f8403015411410f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 503554766 1250 503553516 503553529
    0xb04031101020604080d090302010204030b0c031f0806040312021e0309121801141b07061238030303040501020d050903040f030b1003020319020307080f06061c0215030f0105 76
    0x101c0241030001c0a001b51451205103410a2514900c6480018502901d07075031103040780c41040e225a0402800401001050807042c0f251000c00d02844060361030052502a12a03500c88004000808201110b56102d20410b02601076a03102a6200c009a8500b094254200b21940003200d81c0801441483c00b400c50b0410340da421030b00f54000070540f811004030b41000555080c142c00c10b1096585604000302000d91440c00c4d49070742240e5500d005040e419240003c000c1056155520f0301144500d40030070000c514200220b031400424403034901481108071000000c580303151a04441e40c041c00000208406c0203c19801490f0220906404104544402480507a01e0007903000d14580d242441c24284049441000825400350080421245142d12640424140300c0740e281290000e101480c260380452906120820140180b01e00500348960346c044400d0f61020050b00700b03805141c520128030b105502c03010003d650140c0203044d1100880b410801c507001580100c0c0e42e6020142501d0002c1503620f40300 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 503556016 1250 503554766 503554771
    0x340f060b01030e0304050f01051b0f07090513021908070617100e040803040602040b0c0102120c21060d060212100609060e060d0603140d02152701060f0b040311010206 73
    0x51004600300350801b4144000c1c003400b03010340703410300c04188910081d040661003c2c05160405030003804482400f5130015141c00e130345400c0943c0240c2041d08201d945c2d4014104403401d40d4041b0350306503500403501401d04000015411403440f600030050081401c507001540b0322030301c000c1c18190842a5484074400014107003580a9940101c61000201d0080b0346110301860304076014a0f0018074007a0b442000030f0036036000c40b1144809940103d5118085440c402100e0781c08103044985911380410421a0765456601c0d04548000b0250240860001d440e035107803844410380d216400310b590b40600c08000702d00401c101c4810041d011025001f2408c680b01e01c0d42102100c0041d101c00c1240c44c450020000c0c0c9810102c9600c0803103640f80e000001007110000b250480e9048400581082030700000000e00b0240120050841c181d00c807001d101c1d200034040030072086d11040c0c168007014409119400d9002d032085506c01200141520700108056007040010411240b04040450202d001540103a0700c1c0d1a08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 503557266 1250 503556016 503556041
    0x9030503210f0f010b0f0c0102070b060108070929090a06090314030703020d1b0b0f060f03010b090a022d0306011e0c171611030d0203040803340f060b0103 68
    0x400f001002040940c0d03014101d418a410700c071508041c1180f60881c2281c20451042d61b44603005001d0141e296007001c14076401031000d16101d9215400c3c0189100a0a8440106005031241c400050011803c0b0001e0f40c855040080083c3c1c1071565500340200407036114001070754184920745c6900c500d05000412544415072580281c56141d01300007065070311190a810a6030110b0f504205207000420f0318103054880e0301442e410302c945007084800c0c4101c03050400343d02404bd03894502d00d415665504800154071100005003d0795851856491100d10200d007400d44403100b80b030004e91007640e844007026601c101c10a0b680d0039514a01e80c140d502c2118050680c00010a40b50079484012540c45100d129041c00c01c5042c4a203845184030b10394210103103000003918030f2501645030402515080c0240c0d4a108038078802103041c0380c1424261a00d03403081905038002012500c0185141610700004107034800c40e100c1d0790341001c0106040030040d0210400003101c00d20306c0c08000d2801c40d0b0191040d886210340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 503558516 1250 503557266 503557291
    0x60f07291006140d050f10051c080f040308070b1f050d141f05090106080c0a060309060609091b091e091505090304031101031404110109030503210f 65
    0x140c664143c03403400ba111003d444076102004810300100c41c0b4080d5a00480d109034042c01c43c5d2a0100b41c542512076113411403440351019000986000004d9440c01f4040c9811480155540003005106046440b9270740c801840e03008081100c0d0144032507450b400384101e03107411031919001d0368620400d40285150140e25840201d00c90a4000320388541401c0c1102946002100c00a4488240b80d40c206100f40180c944110b441d042005527080003801580000c0c007000c4020581f00c40018000380b8020308a00031941050303582c3d1a0b59050203d01d070001001032415100401c030314011420440192401c0803102500304814400020b51100c151080079034034440449a8050580300c0c900020282c041d0990690715080c04d446c40074040c90051043c2c0b03005200410055036150726520701101c8121015170701905262500c03654120040a076249194890b9129409681201f100c80041c1c0ea100d28035040541648400305175940429012520901c0c102561084114150f44130003032030b802d030b03401180c00c1000c040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 503559766 1250 503558516 503558519
    0x50c040203010b270415080f0f060117030d061d09060105030d030e0109291e010302060d020705060f0612030301050d0b13080a050a0e0f010c0b06060f072910 69
    0x40c1c041c51091a50b03001c148141388481000019003a00c0c0d94040c09607400c402148100980c0004100e00740b060b107d000d003c0c0101c031140d1458980c5a9005120304080c400d08100d071581180024001c95001219212040145c40d0301d49425850f5180081140c0040c0314807400482c24134000004c5840c12904024014031484110b42e9040f405822240c003014040d43d00d4500d1040002d800640e0241c1040200400e114004583c0e0412010803002030304c14402e12402c01686010f00500700c40c0141584e406654080d500c8c103c1000d034034001e205401000d40b40c0e02804c400d0244440d054542d15004020803900782d6028150b10465075102e1001b8810554030481140c520000290104111030744052040f41e500c00328051615280d80e254486142440041c5d000202041c240303411404401d0700d903009a400c007107400c0c002000600081c0c00c00001420403240c0e1000545036030703109422030b0750940f080307241c881d00c0c0c907100c0c600304002040061180c0a1450401c9500f820300c0041c2c03413010301c555105400c076401e45 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 503561016 1250 503559766 503559787
    0xb10051204032615010806011b1b031b030212010e0705040f150b071a0f062202070c03020307080a020d060207020d1a06040b01020304082104091404050c040203010b 72
    0x203542d00c880c0c1012080c800c01250380c04040f542e0446100b400c010440700180404240010005039000302540c0c1845401801c043d55003c1d503084c4000c1265010103400d441c410511816104900140d00c0200140e515075015000c6041100708482224400d0ba100380f207041410303040c242600c1446103031182c41da1190300100310380d06d426040280488140080001c81c0400302c19182003269aa03006901c80c004001911810801424038204c455501c100e600c81d0399060598402030300c0e1201030718061084840c3d510302c04034031144105c004403a291804046654140b83d140061120940d840183e1080c0030b8a40c0c0002c012002003000100554020b010700d00416250362214001e4001030030903038000d003038044640d0010703c0c82e000b40c6510380340c50503039034149151440c200429260820341c0207046410601c410401e0317140010300035140d09890708518140d030703032041c4520700349001300d5221034111802d081100508007200c4800074000d500036025102c1012141045c40180d1100707100e10540b0100400405a40 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 503562266 1250 503561016 503561027
    0xe1305092d03092404151101020f0a050c0c0919060b09090610030b0a0321030c0f03020705120a0c1203020304020a05040b0414100609050f03031b03070804090b1005120403 75
    0x120002c121444c64546030010003c103401540115140319881e1407078024894114800d0200350104070002e5203031912994012000740a001c1c0c40b982400070100d00c0e5407400ca400d02841d500150702500d0b00a0f50300d0510581804081d4840d11480c8081c58040d01141e82048602203451044002c0c0140d038450300c6502c28014041d020a4101080655980e4025020303643e21040350011801988210150751000c042c0d04115407541500b801810326184440742c8081c0c000d90b00561005150500689841050500c2d60030000d40c0d40404039a55000541182d1840c0c004041151050184100031060ba400c11400e0b000c030310055038007a500044080b0104000e05e82508460100d10700508045004602c0358069500b40c01c00340c41015047c410791006209a6901885200c0180001c032101c0d8016452003001c25124414068141584000b6015021403224200700700c4000d00da03c01c0e070032a500c0d582c810b4400000c0c45603140d951310076040c13280c40c204140c4c40390040e00c07803c281d1140e4651440d2140d40d0240d40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 503563516 1250 503562266 503562289
    0x140316030209040f0605070504031101020109050a02091f0305030d2301030204020a140705070305101a06030406110c25080d030e011b0203130f0f060e1305092d0309 72
    0x11000b65101c0e005000580500440d8011022912307501d4030b950135403800e000d03c00c0c0d2040540d41168903104408000c5000045c412080071740540311405140c0341c440408401070030300b0403890020f0108103000010880000000c001ca10900c03407041014424203c002c1c464801d2146d0840065010140144050314165006020305e440b2401c162101c40949100c0d506681c001c1401900c29420403281003040c0402400004200d1110b01c404111603100c0c0c00e5241841c403010341c101402140003100003003c01c8810703401040714072422601c1c29180c110400c2d9240c2e40300da50145d402d070804141c0c803c2c070b465a030307103002124191600712024001c034110a030030840007028480e210356210f40d22410034003a664010440c0603400e285650107544d03141890103844030f0791001c0781d00080c0c0c0c0c0303944650100003100140d41100140c0d481450601042d11030440014803031603030802d40e1b8040034907101c00c0c008400c80000b03008032610003010300e01c000b02e0600010152030000f5241c0850460b04100421140380c83d000d0164072 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 503564766 1250 503563516 503563523
    0x402061b0c040c0c061103132901030b0109060504020a0807051e040603022d04051203040e15120f07090c1701060e031902010504150e1003020414031603020904 70
    0x2822070303400400080c01e60780000f011502084128803030500b480100e0085c0c441072a0800d0700c96145003448010401e07c03114064000d0154030116484040c40070580780c620341c01015443c0d07180c0541d6100e040400c0b0003e800c1c415088010310b843c0340020142490700980e4aa848030fa00d454131155111141561150f000c025403400405148584441c80c002c8040a0800b03040c0382d80d80140c0b1902145014500d0703076030584007003041e68400c4005012034001001114103850703081c0e4241460710311000895141d40915040b1580071882d0b10100031040c0001d100066074990121450003400716492100743d1500140c0c01018900d4014403030612a4011a40107000d80b0703c80f518002d4102044a42c4036240b254080e0442e034001184148540d10a107010041007031101d15030003016481100a5001078000e200e544242e401a6400c140700101480c041c0d40200b5101c50082d20320b14509168140040081d0f00c503000b00f12024100201610305410b00084004201a014465001082c115020040c40140040048 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 503566016 1250 503564766 503564773
    0x8010b0412060914010f061a07020607080d050a0b010f05090a15020a02090408070201080609010e07080c0714210403020303030a0902190f0e0a1b03050603071224050402061b 76
    0x100d00007a10305030344c2c031800d030450800099402d0155601c0002c6e03030110340c480031520b0150303960040c07000c8418040322a515811200c41d039490b452480c195905000310f80007a800a440c0104004003018079402c41e41800c003090340d0b800f45800240c9000c1e20039001d007184207500702c1c0340008180400605400140c40e00d280c07500440b0b1981d100f03a800180c00c1541100d04980c0050701140100855810030802d03034008000300d401041941c100200c10441c0756004060404001c07030480420502012602141c0f0040e41045421f91400d4498600303d96a00190380420303070780e00c030103610b256412504105440903264020301540c41c5844011510001d001040c070180d0b0304c219100c8800a403028004a08002014040e5580c41300780d00d465000c00710403400401a2603482d041c814410150220300c0380000b9140d01609001410b500c0795408a80b51102503003002c210918a0b5120405201d0010f5124a003d50f422110014801c26503521206442040e00c009402c000f041c003041c51b00c0714480078a0301e03044021100b03c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 503567266 1250 503566016 503566031
    0x6090615030903181410110a0605130f030f0f021605132301030506130f141e03090f030a05070b0304080c0307060504023d110d0e1008010b041206 64
    0x703041e8441a6200c1001d92184074030317813620f5080000005e60000c500d4205040c010032405012600c035022031b84000c0c0059501c8000440040440c0c840c20541078002003000b10305411464040c2100b6125200480401c01104851003014030001e861901180e10542c0844000c1ca4481071103145c01c04040595296521001403040929a0840084500004000403411940345040c03840c1026005403a485402e4080c030018000b01c1c0710f4045246546900ca0341e284059848101154203240016014112800c400c0603910003508e000405001502c40c02c88025013410f400740101540c83c42c2111700100755800c0a002041a4694000915400390107145040e140051550f262401c66205900440d40343e60744605120a5013807004042c80c0000394010812444038001000c40c82000428548426038807404c03c0c058402c0b413107107070419200789005044584201020001821442003541054090030020302e202c800300c3e2060383c52a04881c8240d100d00e1400b0b00701210000d0095a40c10b0554416440341c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 503568516 1250 503567266 503567297
    0xc09020708041a07080f03041505070210110c070603021b030d150522240e090606090106050409020a0521010e0c0405090c1602091303020106090615030903 68
    0x140381051045041d03030b0741d076414640e4441c80129290300003141014140329250004012908480390145007414060b1a9580c5240aa204111040818122904060600400701c3d00003030200100850100207000000c0d191600911600624001041e80d80c0499000c1000c540254000e1003480d446030111715080700d002c2941e62840c3d00c00301a03404120765440351580e1844c4256034000c00750000b20b690124030140d00314501d5504001c4481c5d80081c1d03540d10300403685141c0e581e03003005042410382c0c0d400c03a8942e5103075044030f060002141c181120f800340c1d0000600706c1c5040410300f0b0503940991200342c2064180140a4001c1d0881c020b8002809801c00802e50030505103141c102915544031400f001c2503040c03015402004402601c2c9042c2c0344400e000900255489402d129800340c440c13905140c40da5940c0c1401d4030280c40ca500082c0d04800c150040c090341896250030303291014001d8009005065880340000f00321a80d5119a12029165400c4100b80c507100c0d03000108490701a02d04440c14404201 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 503569766 1250 503568516 503568521
    0x6090406030b07050c0106090216122f060a0e06041b0b040e1602030c070b07210215060a05010e01050d0e10020406030b090903030103030513180203250f0c0c09 70
    0x25500c00100d00f002c52003040d994400d01540380a0b105e006c00a41c1421010072021380040200c8400510201ca8900c042c01070900c1a0f24504050cc04002d081d62200025041207107140c1c1400030110041c080d0034001126651180100c01844142c00002c15040d80d458650150b22000c001e440341c2210084803000400700258400780000c0c0c8010481e82809050a071800d1400003a03000d03078042907400034400c2e4100098082803404c102d0340950401c9580350402e00c0d0076070042101101c0650071180c501110f05803142e0004d6942c1008e11440c0244001c0e498603003c100b100681e502c2a0350010b140e400079000302d540704402402901c5c085031408184c1c501d00c16203180c14a4508100c2074901e65012800304642549802810101d50064175403501c10b040521096440b413005001c0034090110000e00405800c9034062214001c0c00741e503500741c00a8900d9070002e000703944203460850806070740c21044c0e509200c042818800c86c08032601d881c250345031603007820f075030ba414400825100c0d07d440d020009040e00702070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 503571016 1250 503569766 503569771
    0x3091c06022b051003020a090209010c020312031905090c0d030512070305070f0305041e0203070e0403031a0418060e03040801090f230a111f030e0106150c0206090406030b 75
    0x94241c4032880424469412a43d0007050121200da0004042001d0f890700c00340319050707071502000565030b002da20b801a10110702e0138400a41510410761310004001d5200c003c1c40c000c00f104071180150110502c52101030b50307002d50f280552604154004002403030100000d001e003034400d0524a040551503c640701164a0850300380000c207403a58200444a580418819410042800d040040d400e040d210010303422400d1200014061000b000007041d942c2c10007a10004180c0c0c009200214a000e1400070040d085000401c46004c080f20101034041c5060b01a0301e1200c80390b07850107034900d4441d840b140c010704418007584209000c100030114184400b130280030442c07406142e8140800c003551604804a8034258540c0b0f08101c0070400c0c0d10034040b0b0200b5035100c15600087d40a140084490008070b42d240c8a41d00c0c410000707000a00b090441f601a084982030402040081080307694400c4128200303141d01030b48034001001c2024150041c544803000e441000300c09840010019101d41d00c495909909 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 503572266 1250 503571016 503571067
    0x30411010516021f091e210b1018061805061f030b13020a0903080309031306030b0a060e21030903010c11191e14030a1d0303091c0602 59
    0x1090003c220341c10600103002440e0404180d4031032440400010f1b00c80003540241134441001403032103030505141004609115422107948201382c10000798a020007405403007980800049020065400189031048008454001e074902c01c00d84040c070400c100030100100190f82c00000c4080100e1413100a82c400e008942d210b413000504030300c0368010085d2000e101200c0480e8103004200d00b4040c2030340100090103d0768051052a240d8441032081800d43c002c40c4d40752a104180c51100081d03882d07054108035034a07078082d901a80003e803a50340403280510f146035004d801000c0c03855a6002e041d40c04243d060105004003d5030300304001c0d480040c1c00c0d10402503411000a40101c0b403d681050240904c0c8010004c6a200d00f03483c0c10165240030558201c0c2c03401000310f000f00d090003000c6c8a281580350742c0000d0181c050303954032491030f1406041d08069030f4a40d00c105590210044d020b0800104175041e904c0024042c41c21504a50794901d100c5203504021602150240726000080f00786180706021101c1c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 503573516 1250 503572266 503572309
    0x303030b041e02250f0b09010e0a0c06110a03051c0b0301111c0903080109090f060501030b1806060306012715030b060405160f0905300303041101051602 67
    0x282c244100130702c560b48074072010411214006000203103402114440c1c0503440400c0e2000c40da514007140b401000c528811500ca4050018202e0400400050b25810384400703072501084500c03c6060349603200341440c4c0003000701d0410402d10750400401d81c5003050801100102149110b02c901c0440e0a60b150700c8252001c484010034020901070780600c020210031000c00041002c0407850300e00500805042c800c89020035501c000143c00e0100c180040c80140b60000c3c0d0512141d41c1d00d1408500c540f45c1200e44000866078014184001107000c103101740030360b20040c01020b03030303908041a0201c2000c0c408081c448126101072030720124041402041c1210301000703003030f017505803644c181034840e120020122403146141070104100300300540030050b512801498040301110801c40180c880d07140cc0d4129950080d80103030015420f00c07100030210701000c20015a2180d0180b01c41706640d89001c01e550003040724083c403001440c40c1d486032010307098540850341d4502c0b51600e1a00800c10600810b4504901d214 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 503574766 1250 503573516 503573527
    0xb0d0506010e0d0308060904020402070f05280b0c0906070c081f0c02100b19080606040f05090703030c0602130303050d0c0f0c14102903060c040303030b041e02 70
    0x1a000000b0742c07503016054803c9040d140e510741e4000d00308640248414814a0b400012805644542c4c0c160340707201da4001e204180303d241c00d052141c4d440150030002441d00303241441c2e07c604007450140c1613040643c040503180d225114900c9640154010040d480e030000000e1100501141c0d8050701c8500034100070020304803284008601c61600d0302c00407000381e005410a4a03e803c244d50009a1080041341c0100004603014444001f584680001001c091103115a00c0301040288011510b14003925044408000707004000040c03501384d030411680412030790800102000441d01521040703405522481005141051120b801005030f8256042540010400320301542140000c1c4191001c03c00903003400d082c8080501d100411400800500803c208009106030014070f500708041101c05c060140148401d44c0d4426010f5001d450f914040485801e1441c0d080400d4100420620700a2442101315454241584c4054002d0719442d4400340d00181da030904001101c00e80c04109011001c406405682c90703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 503576016 1250 503574766 503574769
    0x2030102031f050402120c090310050c1c091a090a0506040305040303020618070b0c1504031e05120a23040506070e0102060c04050d08250201080112050d08060a0b0d0506 74
    0x2d102500024022881040300520b44550704030b04551080100184e95510841302c2c0100b800d003094020400345081c203000c203100d060a152000340c0440306e15240100c0a900c584080e031000d0700e00003140500a151640081a00300f49012003859024030480300700d51010281e0382e01c45203001c0f011182500010804034090040550611070550048148a280c440030300700d0070801902e51a46204040c407200c4005038142c500700c0140208a000d5214240780d00d81c0346032908004d4491100400e280c0c1204044c401511402c5009a0681e44c208040d0f41d906585641c0b003180c07010050008140c003000e62140e000c44014000e11441a10348154803030700180046040c000d4000d0b00141c600c448550554214504022030303240d00c070003070398101d59040b10a6400300303c640c01c01e00040d119a5113400d5803400741c02000000141440946030f2000c1c400e903a0003d940e039170740409102c004010707600202607400c107130354540c0c00600c210100c41c2c220724000d102c00041a0b84580c3c4d041030358401d05028410a40b2750341004840e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 503577266 1250 503576016 503576071
    0x30c0b030f0f1e0601020f031803011b021b060c0615010f03092a0806011e050d0305031302010e041811030c090a050a0b060414042702040e01090203010203 68
    0xc2030151603201d046003046020001030080c3c198a20b142c94241c50300281c810780c800c101e020440f904da041944d07a904c0d4403140080c030080c203010341c45010703600301a24510580300f041500c50100c4880d030702900c0b090300390041c10089070f009801d034241e00600a004255044001b4416140112420a8036400005100b000076004031450605a17003890718000302800841c621040c1851403c81601750b40c1221485d0402a504044445c3c21500d181d03c1400000300d41110f2084100409807240e60701d0503820361707480040049c0d103502d82c60f00900045080c40800e6040b010006000006841410a009406150004074080b0740c0340500c600343c0601070301061418421241c2c030308229044150041c044ac607075200c002c44d1108001a120b180ca0580d5a0300241110300a030744044000d00c4020489641c0d0340d030700c00380c1d5400101d4621403113103c0ea21309118000545940c00890580d00d040c03248005004225400b000020f04540508445554882d240d010041e90284011440385d420f03680307400800d8101c140d06681 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 503578516 1250 503577266 503577271
    0x608060906120c0105130f06090305010e16060e03010902190e09010522050109150c020c03070807060509010e04090c06110d090504091104090302100b010309020a1509030c0b030f 78
    0x2e1003090315594101c20000c20240d49400c000e003030843d40c0f60f1b000f801070710f21408540e00c0303090210700c04140801c03095030007074000707045034050b00007404005c1030b402c18251a44010b401c0480c0140c0752407410041c55000f0b14a480031440d008000188609581e00400d005d038003001401141e1464182e403e0020540d101e82c00360300490703d90000c104131707c0c2c0801186650441580070b681d902800307034004010418250083c84400b03502034038813000c091180203504050aa1362442401600500b00314030240c3c200014240111003411000348991450200281d80d1980000c07078041c100000b00000709403e889034042c0d03503605da22581d5184031340d501e0400c00070108081074541054581000c250340e6005d507484042c8009440c01168005035000c058600702d00c00301c607002d0340d40340c005081c28000b00915030045000301081d01c140205004180004004604a03001e220000754041010241800003d014400704000b02d070b086e04100c2035841d1a40c90305082c010301e036481200400d1000041201810044003400d8 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 503579766 1250 503578516 503578519
    0x90706020c0f0f06160b04021807120213080610061b0803010e190c021c020a0c09020a02032205011808030a080c090a0e0907080a0302060a020a03060f0608060906 71
    0x1070803845440094441a11000014410382c041d48904401d56140c0c01164607400c03009188180c00b2100c2c0c40c0c18086030704201c0d03003030707100b00d042201503403880c0034003034071540300d84031a644180400011030150b00003034005803500707003030100c1ea0a00880d108108002aa000e11072015061201ca40f07000002421051000302d800d108031030101c541d100043d58030f010350b415180b00d0424500203a540c1380f00c200d48068201044001c66040018a250041c0c010800c0841059842802c060705240090181e87c0c9104040005211032460002046902c2c0c0300da01821344c804091040d02c0ca46a420818032540009415141c007914101090801a13903070010032540082660a0004022610b000c0400341ca901a0103164018050b0490001b07035490b00040c09c544013442d00070000c01c0c01940300c6c0b031004807041088564600c42c0c13040e0200400c01c41c1000a0507407510b03525030700900d801e681c4c2d1092a0040d41000030b00703005054071100c0c0030594481e242154030260855685540c1c45181000401c01e40c5000030b4501c5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 503581016 1250 503579766 503579773
    0x70906081e010b010f05090103112a0c030a080702030f060108063403091b0b0c010e060903030121050d0e010f090f091d0a0b01081c0801051002160e09070602 69
    0x19543c5036001000072180c5c0410b810110303200c0410000507005499040d060102600000540100d030300c804e0300c03c030b185070800b000d0b5003200801c6451040ba40d4003c6015440d5055100000440c001040b09000385685840903080c1c901d0350320300c02545803510b8401c1e00b028003150010010002c40c1d401e01000141000e40d17490500d2001e295901032139890340b202c0c1c0f8504003010f40764581070042c401510b9a050355020b12900407100b01c0d0f41d41100a030185c102501402a03542042600c0f4a140c03070000b5420300540c2480c001d94035503444c001c050a022500380418a0380c03085032415000c00b1900500c1800d140f45103e8071203495000c0c982000402c04000c61036214180800d07644c081c000702180d05282d100303448800d040003a0600300c3c054003600c2c94680700341d4035000d0710405441d1001c0160035068a030494280900301c1d288d6105000d00746881c91200f007000000a006100100024602002d141c80076030890700503520161002800301e44400c0140d0003440000303130300170148141880100706610060100b48081d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 503582266 1250 503581016 503581031
    0xd23041406060f011d211225140d030204061103030f0a020903030903030708090a0e0f040206031b0a1e090e0c0f0c0d020c090f06061605070906081e01 66
    0x2080b40500020460402448080300c24107103424175000080d50100410005001203c1050003000020b12008041c031400352182c1b40ca100003031401682c410900303005d80d0b05038841070030780c00030140e00700810113550110011b40000304540d414050740420b81d1181da0b0250f42c0300e040c03003005031082811040d4240c0c1c5500400421481941000003542c000760404030140e940d40041000074514000c49200a81c1400009008803c00410328020501010280ea00032429070303030380ca5005a002c07801c44401d2094254100000c1c01441d101008580c032043c0c07881d2510390030114000f1540700e80c02c220b520b0400301e0100c0b0028074081d0021000c2c49030001c120302d44100603c3c03c2a207100e9101801074841c8500d844081140d40c0400c850340c090f030365100380080c125024110700d0781c0000d65880b030032000c013030050829030042483c5620980205126640c0500900c2c82c0ca07062880740d4000e0002c0100030345560050700f4010900702254000d17080104481c00c001c0c807103030300c1411344032110700f10368580318040d613262001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 503583516 1250 503582266 503582269
    0x91810140102192109090614010f0e0319050303060109140a05190b121602030f07031d060a02010b0102060f1b1e0d0c021e120d2304140606 61
    0x642c110340f078954507821207101c00a840c020007082e441102c0c0d07003040110fa140c4010442d52042080c0100d0f240004140f200b199030740e1007600310400300c010700ca0004126000c16800d482c00307502001d01120025003102c00c088440b810303840b9000030841d003c0710541c2002050103401e6034403920750009004001484c0135051030440c00250380c1041032103447d00034403002d1003140b00c1c1180e0008a000410400c8242c50f03840a0400361010b00d40822a010032806e04a070754503030f40c001e2000003070b1103c0c0303803403244000e103412226103055645001034018076041c00c50420724001d40b0f480e802d0107454030204540012603e070a0090000e030420200230305501d00d01002008002c000c20340103c012089119641100f40c3d90303000368100703030780aa103070711840c01e13503000f001030540e4160311194081c0b01541c0031582074502410300030005285148926101d40503d1740880c201c0d5050310243c00090000307050500001441d80c010340d03408404410b03000044c040d26842c560402041c821104803a0000d065039002030700356440e1420 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 503584766 1250 503583516 503583523
    0x2010e0111041406040302130203041704030c171c02030414010c15050718031b060c050601090e03090a09050601030e0d080705160609051606030605010c060f02091810140102 76
    0x114448812880d0340060f0407645541041398091500640615201825030795107401035401a00e08864000d800e00700c450311600501d094070152940b00040c0c03e0344030320f00409140c65610640b2110918046e800c40500c580618904996900c4400d8024644591401c07000351250584c421041e410b01003200b8905001415007210411301f004682000145034842020444d04107003a08601c401d002c0d2200004400c0c040e841c104546c215909461035841c89480d40000c50b00b468181d00002c02c10f074045001403040241c00d81103110100444c40480e41082407040c0060f40103205640880f00495440084c40019681b500646460003200c0000f07080707074140b00c607000300340c420700516a004014010803440c4082c00c1c4080314070100d5411007401d0008054904005c2c3e00c41e01d8880c020814405c2035500050303410b01038001d2800311401612801039070001a1282e50217400403042681b54650f0030004001c40f6a0340c1d02224210080070101900310f0329041c68071002200301034121030130346007a03001800d001b81c0c0e000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 503586016 1250 503584766 503584769
    0x14071a07210207061e06150c030c020f24090f0a05060a21051e0610020a020d080c1603110319140708031b070f030f080c150c040602010e011104 63
    0x10781c0060b915610380c140000202481d11428000503518194800d440f0313950b400001c10780303086884800d500f0b0b20f03142054135886049180140440d21488401c1d01502d8078050b03000c203140000e045200581800d15a000d1064003000d111390b84014041601c01050401c00600c4c0c410300016120704101034100342c000740307650003624138420407c071070703181410401940400050080054608140f106d800e043d1903907140f00202e104034003840f00c400d1001400c01d141c80481d000e4510103a130080e10244440e1340030b0148210022000b80c8172490100194215000100210103941001400c1561401d0442ca098102b850f00030100500c00d912080018441903640071018080c01c0c0e025103a1003403908042c00090030142203074868407050001080030004115034110203d03180c040c800035510f00f02d484040b00780404149000180c40c84d0140c440004c0010500c0d00288100a40c280c12101e0045a0a1191603045400c0301c00c2d105c00b036004102000345540902031240446500c2000b80071003182900c0030511400745 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 503587266 1250 503586016 503586077
    0xc0c0306131203110403061e06032607050601060903020111070e06010e030c0415090b030105011a2812060603021228090f02120703050a06020a14071a07 67
    0x1c000010403500c2c0030b03501c1070135103040b42c2188645840d07680c1020342c0141662640c1903018803a0100c1400d4802162140a080e283d2040c0c8200301602c02c0b150f810560b1011400603980c110040220201184082100c0ea000341055901c020240342144001001840800e9560340c0c04c0d40151000e008540401d01c5241c1e02c0302d000c0c6406402c0d1201000003c0c0f400301000c58a50300a40ba0083c0f0380f620300c50442c030b54803d03a034002806101d403100d40310615088610910a1196180240b02a07d01030740a40f8000d000b003a40c500709000c0840808a00185001020300300300e004070b40c0d900d500408401c601d00440f0004c03c0c41b8141107080c007040785a070340780220000300307042d154510049510070701d002840550041d60344604403c001490091400018804003031070f00742d2144164a400e00ca6500e800611001039075400030203040c1140341075075400080e42081001d0400d004804040030080e0712400003508005016040d808070245c0c8482c002811414050100e60402042100e0004445084604541104032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 503588516 1250 503587266 503587283
    0xc0312072004090302010c0f0e030303010b130b0c0c040513051506040f020c07080712120c0510050c030f1f180f05010609080607030203060a03020f03070b0c030c0c030613 75
    0x141c886455908105007440d00303900034a0b0040741014954150703c079140321070103904c5540c0132909411058401d01080c424403503056104100501102e1401006841340401e4100c4945200380c58800901154200c610024803540c0840a401d040d40f070700d40103407504a02022180c4400440c02d0301e802e910750454182c03c6030f0006200011800a4540f030784040d000c4425994115162070002140a80720222442011a140f00c2c40744041280380301c840181600d07640c8030706a110038001720b0000342c0341e0540c15030701983c40d8012508120070002041c0a400d2140c1c40d100e43d89662407422024200c40860040c0c20703004e41401d04c801c4110362280001d244010307219445001d08441f141c1e020018013900d050043c402105042a0001039810707007150030394059692850555000f40d445400490490200301c4840740c2c451a5460100090708113114003440040d005000c1e5454140c4507030510206612013140500c4a50002415801c3c01c082842002205401107002e000f45040180b04c1140d211074020001d04900c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 503589766 1250 503588516 503588543
    0x51b0d0203180d020a03020f07060203160c080d210504121404080106030b07020d02030a020703020f063c04301b1a03061e01140c010e0c031207 63
    0x155802c60401031900c9035030450700c8490341400025122140e00104802611801841107014200458804203850f001e0740150304008104c0c0c150800b824407103a0560355070582d41c0c03000c12400300600100f00141c646071035424a951314143c010400307598003c402401c3c2860718050100080040700a810f01c80014900301c24420f000c5081c0b030751140f02c0d9078010320081d80381210000402c411005501c0c482ca100307409075040c0c2c1c441d00d00282c1e20703032103907110000c010b8012100c144014034051610641d1140064409030400d070800540043c001c10070324050581a0520746d0440400e0181d4545100419019810a007040d01d482241100c0f1144006018208040d18030800d4a000d04c4840107080b01d5001186004100d130501104e00a0b242a4011503807800503039000302c04910403980403a4010000a461700340002540b86448490540e5908010f042002c81980740c050f5450340300140c6128a8800000100b0300882e80c1e1680c50129440c41c01c45c000c1e0003030021600324008800a540405421814170000031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 503591016 1250 503589766 503589781
    0x607050a1106040f03020606010518060a090b0d0905010b01090806180109020904080702030d0c32011a0f010206040804090e03070210080403020d0e0d060f0b1c030201051b0d0203 78
    0x10180070408101d52003000e00b000244000c141c3ea0042503802034080d10640d0307c410004440d0751152120300051013501039040b0585080c090000c1100920500c0d0521440741c0b14814180c03264071019182c0c0b6150b1310f540014050082c00c0c4038240ba407503403d0070b0400741c0c07034500034285440e180000c02440340541a400e20003003114081d0887d03201e0303582c020406a0503103041d1514480c40c2d000b915040e404ae00c00c00869030240c0707000300310444101c1d030040004003482d44c83c04e150300540b0100c25082080919100074042441009000d42100d81e01d02d00900b5150200030410700400c6071034030500d50b045610440510000c00c81c608111801d070756004401059103910440228a14800c0d4a4000c1d0170540b43e101808840d5484089180100e01c241e003610260504030001b181c040e007071000f1303640d031089581c0106c0c0001105544a151013035965003010454003140e000240e00004682400081010300c0030342e0b0300c03c250b828031036280d20440219499174114460241000140150b000c0a11416400800716030714 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 503592266 1250 503591016 503591027
    0x50d02070b030723090307030312110f0304020d05100e0717010b09012d14030c0a0b0307030b01020703140d0801060c0302070603111b0334020f1c060b210607050a 71
    0x2d0950240c06c48170082d82e28030b03008111080610319090b410b44bc110040c1d96541d00c08080b10101d2441c40d10b203130b0071a1215001c01c4201d8101000441d0303107101c2c0004071004201306009000000b05410050b10f20103292141c2020071214a1000c0c01d034991421102c0122035551100d004c1c10740b082480c0041110b68241a002507901c10300c102100b980082c2d80000076540041c40710140c000d1002d50503242c22088034000e203c481d8440303000301d910103075062002a2040d071003544a25504001441180c0c083c507629151040c00640e542590b07405a08250900403145410a10060040c61245841d90241000d07481c02900c82031503014820070551034a154148200d0444c081d18580000d0321151071106090018040d9254088034640007000c0c4c0410301c41680c01c00c40e5070100c001030380300043c104506001e9800c201c20400710810850388460702b105074016109611203200b050340c1c800c050019604c21400300308070038150240c1c95414841d0002a118103100030200305c141d00b110050403c2a10ac1e00c0a0109451 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 503593516 1250 503592266 503592277
    0x907030b130519060b090610080a02070b190605150d0c110f070f06030b090103080c1f0f05010e01031505150303070b060f090609010b07060b0d050d02070b030723 71
    0x481c1c85a01d00580c80012035110246401c4d200e0074041100128035428003150240803112164441e40b803032118401741c0e01805400d03920400401c001031808016a0745d200d040c40e8141c1e0024912490a8402d0313480b000707603100302c00142c001220380c800400b41c0184214503a101c5d4400070329604c0d40300c500e40707e10f841c01842c0c1114035155034815a0790202010051030b58816a5200d4042e0101844900190040c00391003886584503001d440c80d50160b0841e1180105035224000c2c0c59818824201f903109080240d1703404c46113503000800f0118003420050491015144180c001c040648001d030010400100070311100b08002058032030208160303480030301251007581442d0401e5007500000580c0c404001101e040750344a414101d5404003010020000d1000315217003143c560750407002110041c05951014005031460a10800307010507882818030200d403606900c1c000c11070307042c1d200325250322141da0148154000380402441079030175032501c6040146105060010904800c070503404038000c01e0301d400103c52 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 503594766 1250 503593516 503593523
    0x5011d0106260c0a09060306260a020a0b0c06010603110909130c12061109060f030c0f072004050919030203070503040312090f030804090b040212070306080f01050907030b13 76
    0xb851883c00e5030304400b0540c010480079000030450a000b1802c40d009101d100c054489204100d1810050207840d0f020050ba494032014480c81001404001a5a92800d100140a600c10f802d130f100e05041c0c4d80b8529020060f04a40300f414101560407005415420984080e4501202c030b190668468807602e820391901c0c04800b40070304106030b2000c0f03000e800b103401d551a0580314001c20480c12411854152080c02481c181c0740e4002410800d046c46001c4210185802030002013003a807070b18903c1740c603070102030744844001c07075488040404e40151074020b20050902900c09507000d1081345014500951100d0546101003c0c41d485000c0312001c1c944200103031030380c04d9802403c881d511a105d081400c010b1101502002c0024281000801c1c0703a0090700400d81100da0003008281800c2c01c0450140140209a44054209a00b8000007060100c0c01a80070702a8050391400180b180c14002c0d85421308806044038030b0790b45e040205000120000040c02c2d001c40707800400126403525100c0740225200c44034003018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 503596016 1250 503594766 503594837
    0x20705010603050102090102070504140612030412051e0313051e13090b2d060607060f140a0204050303180315150f040501080303190612060f05011d0106 67
    0x202c2000415402044201001d808488046588808000582d03500c40d50030700b500155600460428100b841001407801011410ba03070a190b255218024440040507055406504c40c8602003490083d500c030200001202c800514500003040d000707148010901c1c854140079008010390704030400040140d2540320040103006602040c04246e0380d9015040b0494250f071107171525004590883d089100b00100090314850301c87d05440c03031800200f140c0e9401408280c12520070828900003641d50700c122001e141940f04001802d05c8004005c4400100040040001c1d41c4100b2040c0f00d03507a400010f94605414403924918948001c1010030305000807080c550646480060502c4000c08840c4001035043e8000d581c1800c1d800d43d10030400040e60030078030881610750010030104001d01350001c1540f400b400c4941000ca03005646400040d414801208180c881c0c69542c40b803030030740320941e008650040900c0703404a80e030f018600741708038124081845480c0921034144100903100701981500b01d039250803541d94 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 503597122 1106 503596016 503596019
    0x2100c03061805070305060303030613050604063303050609010e070c0b090c0f0303070302032a07032001020105220c0803040b040302180402030a0f060207050106 71
    0x14109074669001158100840b28440080d10394007200080d203103000c8100034200c3c0c201401c154425007041060020580d1100f800c2c95030080005000079494031814005001403105a0091184000301c81c03420b2258518446100ca03030002030804414021003116003202220700403102e181c0d00402c40030051100c0c0c101c00c401c1c00d0f480340d010305050881e00b21589031900407207402ca5165185a001c15911021401c00b6a85030703000200c16001913050ae055035801035240e00401030030700304040300d1a071400841444400080000c4150310162900582c807418601c8918007498405070810030204100c0701d042d4414030901d440344000d480b18049214032940c0b0844c641104c142c043d2403480c0b201c2c0010920000501c001c000500100c224a0b984038554814010b02d21a03800c05049003a0403d000c0001503140414040301c01980181d100c4001202d900c5e041009006140e000b81a40d13203000350 = true := by decide +kernel

theorem cover : BRFrame.Cov 503417266 503597122 := by
  have h0 := BRFrame.cov_init 503417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 503417266 ≤ n) (h2 : n < 503597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
