-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4617
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:11:44.675994+00:00
-- url     : https://prove2.me/submissions/adc309e5-d7a5-4097-8f07-39056e155c55

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 830215827 ≤ n < 830395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 830217077 1250 830215827 830215871
    0x1b0b090f06030a141608010602030a0c1103100510030b010e06031c050702090f1f030201020c0d030e060a02030319020403020d150e01060f060908070e0c0906040b1801030c03 76
    0x40103140c04000f08005440e04d402950794002042c83c0110b2510b4403101d83c040d126040144040007407402070000543c0ea002100b1607120400715507944c0411080c43d2101140c1058008078541c061262580303980300d0380414441c0078000d08038031b480024000c0c5103042c000b500c0401078000100000d842410b01c80705660010701d176050800071490b0080c00000d180c0d0b0030380b054002c0d000302a40000d2104100580501e4081085100e445c440024032450305104101d54502401ca0000a01681c8038010f40306541c03074911045c1005611030b01e09001e80034001d10115078103802c404810009030341f0220501c00300750f00000f42076120340950388045050030f00d15000500483c0d110103000d450007030000103013803d00e0700a4100d07034610550200203200080d614903c4044481c5036110300c0b40055607490012170800804580b807812246141c1c901b8815403240a030f0300d030385617000e8061180d00510801c4009000000b40000d40300b00e21501895200c034940c43d50024042d1034003101c1d0707202050701e0440c00c15880052403200e07031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 830218327 1250 830217077 830217079
    0x405060a1205030d0504080307030509150a0e0708150103020a0e040507050609120a111507200d0b0705091509011e0216080f010e010c21090606031b0b090f 68
    0x699111202d04219056104420301c000006050070204003d00174608000c500940c1695800c01242d541d03400c2e1a500c0381d1200c881d10803607680f0300001c200c3d40304042d080100c41c4c20f0300d80250f03500c06685605131460640b0254901c020210402c00401c1940f401011100c0100040400404145069035609441c3c03419030084c0c521401001c0780c1c8074081e460300707a41d0814078804d030000c5400c0c191340c40c10240402c07642d5900c018814805090180b00700c0001c0e8007940d1a03503030302c4091180d11901c9454820b030a600e03241030454105074203054580104031190f6120780212075684580365150606414030003104031200d5100800442005030441c030341da00c13441154915060121504005501020885c1010318844a03603410205418011070411400f04c0c120750304400100c02002040c51b5a45868261000d20051764041524400b00c107444040005070740480c1403d45d280001d460101d50b8441c01103991980090f603807114445100d000b00351040c0111006800c90080300c60902c0c101ca0009041c04420508007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 830219577 1250 830218327 830218349
    0x10506120a0611090a120209150102030403020f060915030f070906050f1b0d0e03011407020a0f050f0d09060e0409170d0e1e06010f06021203070e0d11010e0405060a 72
    0x10500c10f44a442511035044d0000c041d5400301c0d40e9101540301c40e590b0004c09a20403880e00b004a10340004c0524100409041030300035500701307442c0d6020882d40740110180e10741c000c01d041020401e0b0707545445540c2080391803d040183c8908007442e0005103800c00908410500404250074884140c0003001d03039a00c40b41a91070156a541d40c0c101c054502c0c0c041c000140c1480c8a801030100480e40c00817214807002405074000c12002c00c109421500040c01610480301581100003074401155030029030f400800e0241c0101c842054404031105e03d040c00340e8142ca0002111600e0a102041d03104000c0c0e64603180465050100c0b0385107480e2050000100100101d4070000040e451a041002d40c11039405080045c05039004030350041c12034502c00f007a044015000d4002e103000401d4011003a8003035010b0703607040d5000300080c442403004400c075036102809040600541e403007988007c2c1d8840c260000d071640f040d81507103d158070340300001d400c2e501342030764043c1301d1401d140400c00740b82c0340c2e492220111180807c003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 830220827 1250 830219577 830219591
    0x408030d020f0c010906020c0c090c03070c0f0506040c050a3c0b0d02120606030c0703051b0105130c0609180c0512100806060904050a02100306120311010506120a06 72
    0x1400d0b20342c41440c503001015428441c0710030911105a01525550808205031000180010704118100d0300071a480107600c0c60500220f2000341c414a4082c00e00c900c101d1404003140c6850712203d1500e0412101154202e40c010000d0066003400e1449000400c6031100540705144440f15034141e98800c185c0c1d011030b80000b0000a43c100c3c00e80d261040040000080043d03868041c1d800b4040a580040c1d0001c010425407404603400303090002c2103e1140068140305801d000341a601281c15a20200e42c001c00d1072615042d040140b9000e2180601481c074410004d8100310085ca00044030030743c19070048041c010131110400c1140c0c8022a0003400003010040002c0c4801940740584541c0101c01c0c42990400d0707014100804406c0081d041415505c105080b40c001d59100c204001c14060200c40043c403541002080e40c006040400142181044908021402e0f54031440480073b218040c16080e40040d40d60001c0504244003840340680128050751411400040801099a07402c9290001010709644e0f2032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 830222077 1250 830220827 830220847
    0x21060a09020a1706060f1005070809041b030207050f030a0c0206030a060e0108061012030c03080a060b030c09130c05040b0c0114151002012924071202030408030d02 72
    0x20040000d8542e41c20481c0114000903892580c5020071210300e03000d03815031b803c402035503c0c0c00c01d0507802041c0d20b0f94a0602d0204180c1d1504201d8025038962500035403107074020b141500200c005c402d2024410340d0f00503180e400c0da06200386407030100240e01d0300d540c0040001881e05640f050740300c4095074040e0340e0240c0d45c1c1c6402c80520002e26561307008005a401640012541013408102c06000381c805003d20301010341c031482d20780360b031301d07040b02004020801d034201c060006400303800c0d01c0b6030210941c500010090790710f4a00180680c0111000c065084000036105010f19120a02c6c410807000018100b00071042c110b005000d41c0b04034040c0404035180410007004802094000303660b800a4282d180c2e0481c01c0c85c0012889009004140d00c0c850190262200f0325144141b0030804011340040342c1885041501003000445203951a109800820380820002131031502e154003068001059603403a656140c904000b0b489048041001d01150006c00040204503000070540c1c030902240d040041e503440780c40c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 830223327 1250 830222077 830222089
    0xa0f0f0923010e03010c0c300e0d050d02010c09090b060306210d05031e07020d0e01021504080c060601020706080f070c021f0e2d06040302060d0501030221060a0902 72
    0x18940f10360540c02c021018110742d60146410421521404150000040200e82d00307120984c0c8190106c5001c0102d007494030722502c9229150f4244a0140500f0b0b0b904080380c5900c0e05007a18034240c540540c2d100c03104030a02c103901819010052075400410010182c02034005059880054452803050345500200e203800c85084444114030b00740e8070212a01c503003070002d014285400441e408103622006170140442e8881d490a0541b06102540c098480503a140320b0540c0c1039444c6400c0301d8118450803c0c08203a2005d01074a0070300032401462b00684a0184401e0b1510b007007002002223046402c040000c03c20140c00c1048960000c030819000300160369501d070708950140c40000040c1d440540600f004c915116940548400f40d00760303507a02d03e0890860020701c054250201d1158103070b001800019294082d074251009090a002042c0d036103400d580b9000100c1a80019400b0504030340d45000410852801c0854040c0c01c540103c42c481104007894400c58440500800f00094940c8507a070420455480c0c4c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 830224577 1250 830223327 830223347
    0x9020405370305010504030305070305281b18090b2209290109270611030405030a030b010f0801170106030b0c04081902032805030a0f0f092301 63
    0x520700701c01c900c540e6428654041e080c181d03020340c00700349081c001c41d818034801d0140502c0340c9152150812080a150341782c080c500003000c0145074480c0d441103507060705c1101041c4a00806411307034500035490b0b040e07010841b0084440d4040c2c0d800310314020b01142c8984450b4a20742d1200003c04c0381e2010100c2c80502c0c40d0107410440d400400800514088000b0116400c850180c240c0f03030b058050b4156a04c590011040f1042000d00302024880c0b80700c0000150005800d900025215a9011030b40f03804111162807143c00a44d412545500f0100b81602c1c5142d01d80306d000c0485034246000031082c19040c0c0701504c0104180505801d807103034040d440b41c2c0200b0940121000316881a040072041c500210300c3c004680060081c0000c60040041070324030b010031a4030b104591900280500340c20401001084040f40b11101d80074071724070b000d19551011510500151a41201c19103c00b55004c60000c0e0081821900b03113401d8040c4009140309010101c0d40c14072142560300710702600307041000194010b988042c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 830225827 1250 830224577 830224669
    0x6141e0a0909060f0905030405041d060405060702240a091a010b0315041a010503090a14061905041a0903040f030807050c09040b062e09050a09020405 66
    0x24aa900103940e50080d40701071202030103030601308030f05030141c0c2c802d100fa511881005842a80284810301c132614081d030003400d840d00fa80342c0407216541903d0201e418010b0031201070f541608000708000d00c49070107102207120f0003440d046042d080300341e181d144651140064035400c006541d0350300c03242c10805c0c20608100c18442490381c81c4280d603912100c1046039802280c0742c184c0c9050303103801c1015506040c0160701228140082440c02c4240d520011604da800c01410503030507100e820303a440081083c0c5146d09048000381c00c0a00003d240c0350a40c46c2030055040303017074090b20749040300b00004102000007c1640440c2c512540e016612500801482e600658000c040c2c0e4840f000d00010805c401c2c0c000512206114005851502d05031034208003078018100ca01401000c440c5000801900d00b0046482c6942d280c5501d8510196084212035008003540c1c3c030300000304100600c00c0c003031440c0038074124004041441c010340c40e081c10440820703502048008088034600d0003c0003801c500540d41c0310303c40381d002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 830227077 1250 830225827 830225839
    0xc0d0c080f0c0703020f0117130203070509040302010b031b28210203060f070c0b0702010915020c12130603020d020c0d080a0b0901050d030c050a02060c070f080106141e 74
    0x164260b24a51100024031049115100b04400c8100c15400f95031982c0740c2100140100720b140c1e4503030640a59007168100120391600a0880103d525070350000340600460003a40001001032000c000e15141075550021040d1000140c3c607811200d81c5c803900600074083c0221000010b000e11000203030b03089409a0012170042100000030380618804840351014907000310111240ca8075501034800041d03a040d100b510015403550040400f150300000c610340c0241c41880006082c01b1a61100c0c41d201c11111945002507800240350b00c5102c2c010040780c01d600300c0e42c17403405241c003075180c0b940101030a03503100d40f0040c942c02090a8421107119415035174003040d44401c0d1081c4010f0444000d0004400f2103421070384614003818440ca40c00d00700102410780d60f014010289079005524281c580805d2000b00b240c10784a000d801e100141c481e14040c040030b200810050a085080a4141c081d028154001c111141e15051040020701d0721000300c580d00300c509694109601d481c810303800b10f401c0081c01d51941c05c84 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 830228327 1250 830227077 830227087
    0x30603020901140103051b09011112031e0603060928020a150f0201050702030421061e060509130b090312040c090c03020c060105010e0f0a0f0801110c0d0c080f 70
    0x249102c500080c00f08003d03601040075030b403580c800c2480c1001d262040c2c13000600a0003820100e500400c1c0150100c0100740444003803a01008050750309074401c682c0d0140c0c500000724504501e4901074891500000304501420240c600300d54210703070321415000000034494100d4079081c0d6094580d01442c0000c0d4015080800c0c00e5140c24140758840c0c11402d8201c0000e0014807070f50801031041c810035003d0322095000c3e520303051034880010b84000500300c071a113010981c241c1c160002001c5103e100380f075034002c034910604007842c00000350454440740c1c4000e006502c0c01003004410b030740c10748803125117039808158003200f600da8045243c603501400c0400c041c0f8400700414003044c0890a0308101c1250090441482107015182d4102c05900400d003100040354042c00c01400300d0360181401e4800c18402402500b01d80b070341038002031543d03441c40e070002c405042c4e803100500144c4400e01400c00c401e4407150803145070107003d210040d6603804c080ea143c8100000c0b204820204051401250410741c20704103400d840f6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 830229577 1250 830228327 830228339
    0xa080604030207080d0c06020d02090618150f040e040804150c0b0705040b0d0b061c02040f060309051b04020f030403021c26090a0204050408030114060f04060f030603020901 76
    0x141006035001d5015105001001511800008000c1c600c01d01a580e298840d4009a655001941101015840c241d4080c01401031644600c00540350a4011420072009600340e08148290071460f00c3c55418000010460b228076007030980212021101d4901400312640d13243d080a01003800740340c000c000c141a24940300000e043d4428204000e01e40030301c10501c03068543c0780066881e44511b20900f1300300b80b070034450341161514a07030044600d204003916203443c040d94500211501c28413030f40000e110b55070101d014460054019071040142406007400c004000b2030b9299151b4a0703140c050a076030b1041001098030900d40f20341c0c058550000c3c03070f800c065803a410b003443d01070745540c051400f4070610300161501407d0640309603402488a028411281010702c0e42e000345491a4130020000e410a10034035007600c0047c2c41f00c2c419240b10318056642d0302d8403941801200601001d14030800d6209207018803500d4400c0400400329000ca135100c4c200311141651200e0242d0140000d07078800380d44005600000951 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 830230827 1250 830229577 830229583
    0x2a170307050d0b011b0312090b240d0f02062218051e07030e0307080409150603020906161a0c1b06090c0609060d0501081e0c01080a1a0a08 61
    0x401c1049a024400000810011590492407190842d0312a05c0e01000300f011074003901a41035100030700040421355000640364607405440903503242e04c0c400c0c0b244103441a114262442080401422186051240c0140c1c9410b0a401101c82d00a032040b0000a00030303014884124004040c4e00c030f5071012200b807940e100c0c58001d68120903140c501c03403a0704107800519100014001e01c40450f00041c08550680c0340e03007504500030888050b146000d80b100704802c2001c10754407000783c401030643c290b0109440c0f40c440340d42103000c0410761010043c03500510a00313210f952450180c414001d00880d068a550300c683c00c00d0b403461002d003403001800c002c02d1001d208850140300b00800c2c4402d6820040d082070032116044c20350b941400c4590800c0b5402101705c03031a980c90001c0003022402c0009082c1070900802c01d10001c200c2c1d20a07800f05045601c00021112111f01c40b0b004d040c0c0380c00014018103a216070500010b00055002080c00210755990b00c0c0c075143c4140308151811403a000580301c0c40403070391a1070314966 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 830232077 1250 830230827 830230837
    0x50a091104180b040c082403010902040504080901110a08120a0f020703021b15041809080a0e01140406051b1204061701140d06020f2b0c2a17030705 65
    0x801142030100341c0d1035040c00703041103a000c0c3d12140d90081e019141f03002e1400045104140e0355500d5502d418410001d80e42d203010b1a401140208801c640d00c1c51128000340202e0326104400c40e441e0800b48424001c6400b283c240d403a81d050304880303007800c0c3e601e00d0511402011488a0305030103d2022584000f41507001071140203035481e0044850162591008008041e00b8403048100b46a0f0300300320a0002c40a02c840c496202100040701050301040780d900c040e03d58003c1d01e852000182c11102030300c40f0350f9014682e0303010030484540761440c041c14404010040d11481841000a10388000e609810391b404100d681e001c3c081c41e940c4217850702d4454000501c0b814481c81c00d61655080440041807141c40365006070404e5100401c215218101c5a480d00c02079041031184030ba0a42c0709001d105400d0000405100041c10014106104a1140c000020460390980d9140c010015402004c100040d41405450181c1000700100c8142e410a840c000201c40115907140624032404003c0c0055980c000700540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 830233327 1250 830232077 830232079
    0x130b0d0c03290f03011401080a03020705040b0f01030903020703060c02010605030c1e09101a0715050103032a120203031008030a090b0c0f06091b010207050a091104180b 74
    0x48164260001d108581016440b16808520710680568040d807520089002441501400200c0c0c51071464951714081c810036032180d21030b50803090b104001c1607418006000584400c54003001031110060210b03910030f2900803003905265540382400300307040c02080604021640000d06100880503410028080c00d064401c40380284120304030350304540b4041b074048050307070038400d1301c1c61914072801c1c01c02c42d075044007600c6000304080203100031130b01507444d900890988651040791541c0fa5001c0c030f03105102c0c07910030403c0c042c0c45103800014800a9400810440124404140c02c0446d4130246218001c814598200070107101036400380c03812280d008005548a1000352442c2d010055940898035120301c00c00701e029000644016050185840c0c00c0c2c081e01c58481c0c0b0504070765021b01e107100c2541ca44002070321000f0036540a29082483c80f4401d92840300c03406000e101034490589040d02007102c4141c180141403403203845150200b6071345210000d85004001209020088e014904802401000848111 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 830234577 1250 830233327 830233331
    0xb040207060e1e0309090a150f080d0f1b12020118060c081308040e04080c0a0c0e0a0216140124030215090f130e0703030509090a050417130b0d0c03 65
    0x322000f074501005441404101802190361540c5000001e1700a02400420900d01c03c43d1410200320624840740d100090b202e03640003040c0d501c0c0e800300040d11701780144102c0420025410781c00b090309030350141d2440d03403140c0c0546039040c1c1424440f8160b014156108070101808045094001440801e4102905151007619034004035165a400f000a502c0781003c082c20101e0304000821491440000d03080e4018020301c0b00134142100e8a90441c104415102c040d525803821500c00c0c441040700110303590704811034160852404c100132218680180c082507028180300d4404203002483c040a42003c0c0c52000b1400036044c44071080d4a4040088d48507000c246c2c012100302c1852900711201604840808000618405642c144030080245480c4007045110b0304a46814101120b500101b20541c0910b1003901c1c0c060301d820300401030000c0c9030170003804100141d047c0414000803800b11555210311400c16540a6500c90078444201d082c1403a60b071150011420004604410840903800100441c02d6070f682 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 830235827 1250 830234577 830234623
    0xd03050714160c05101d01021c0302030a2f031f181506090e1003081c11030106050f0f1903020307031b050f0d1113030b10030b0a0b040207060e 63
    0x14405901e00f020345c02000300300d24000294800d11100c80042e9001c40500c101c44921600c5280841c5000a00842d0f90100360080184482c46849008030b000701c2a413102181510281c09128034908400c030f03c0e441c0b1000c0c1000000c43e80e04404081100c0d0412072070f400540070070741c1d10309403401c4035031244000c0784a031490100040405482428180100c07070140d03032021318841c1404032444541e240a0a24000044024800030005500e02c018106100d001c03610000400c00991465003650303000d1841403c0e2003410401440f003140c0003010340721000400c050701929400c0840d01900300c0c1c420b620361707031140c0c10001d42024640b580c1900258881d0159941c10f0040040c40d0b5050802e480c81a414103001c19800d000c4034400900c103d0180c8103800ca0a034000c01c19242d900d1504009a101440701d803c0180004000d0082c00300c21454107405c20008501d14800d01e00d5511070750402d42c0e01a062051207500c82c031327400c9100e80d12501075a41564001c0e408121612104401c581e503030501040c80c401290000107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 830237077 1250 830235827 830235829
    0x2604050a0b122202090c0c010905011a121504020607140d0e032a0409170301060f09080304030303020a0c021c060e0f12160b0a0e100b030d03050714160c05 68
    0x10004140114404043d0360643c20342c20020388410040040c80801000d00490072003500c02d0080e0215035001d180001484c844801030808400e01d01c9000c98011280c8200580107500001201c000c4d0240108020b9400d071950310004006116908025114042e010f02d600009100401ca00d00b0b01161034903150390501b00c2c682419100c000d4030300c40c510404070030741281c41981040035081242080050000403280384990300c986c43c40c4a20510400e50b1107010005000c032607000441c40421200d5800c10500c0e10349040d14140d540c1c0308600000b0105a000300341d0000b41d6000d00c03c16043c590303000f444411226001882c0c4010315a1110301a903183c3d0402c0040a44c8810100d85006d102c0c50000250001c1c03650f10800440a40c0010070798192140400303042d401054100f40764501441d0303441408103402c038120190900e084c80d4914511000f40c0780020360340c1c05580004c0c0611141789681004107085d070710120103481c0d03408070300d0003004040000280348041a602c442c804008600c1103444681c1c240c1c40d14 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 830238327 1250 830237077 830237101
    0x18080a0207090c0e030c1014120a0b030a1e0201051e070302121914090402030906092103040636020a1509122405040506132604050a0b12 60
    0x1044807a016044564000094145400308403020211414140c0d2328109860445550368068170907000b109840f541803040349403035030081d8202c80400310014025800941c891984480d905c0d070011541448141d4200300716402032090303130041d414401444494910406c00428a40d0203100308500500500605041100b49401038900d105000d455040410f80e40c284240c641c6154106107040300c04007485410f042d680d450008501c034400c0f0102506a6040410880d45041e1704100c401904a180c1c01c100e028920000c41038a0344250400000300d50000400020421240100828000da582d0340e08803140010200c2203e0304000e10aa1700000c0381a61001c00800da0707900d40500b01c001625040003000700c02e10000b0100c3c8017078027820029041c0d0540641e0a20000408000782500540383d0003004140001404500e51003014500c180382d2020b41507403040f00201e140d0030710b080315030241d294494074800500c050398042c280161800040300c1c0c6a100c0c4d514582c00c030007940d9150301149400151060801 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 830239577 1250 830238327 830238347
    0xa0f030905130c051909080601080a1b0501051801030e06101505030105030a03141903051e091203150d0503220f090b15030f012309060418080a0207090c 67
    0xa03138500d820852403440e40000641000110820040348060200d5000e2051125078005e00e407100c020944c0a0701f41c41d0510480818039a540500a10071000b000780fa40c2250031501c10b440c0100001381c0c0503401c0da00603001007109130f418078124413880040141403d0448a41400d491505406010301849404101e5852100340a8560103401480200000078041c480704050038a40181850030000c8a17640c144074030100b0b81c1d540d00000d031141d0a1214845540403213220380390759988030628524001c0741c1f40391365440000a070b0602d41d50020000313501400107108211183c00042c1100103003165810010f075243c12032407503c1c0c0d00d04050200c0501c0d1444200c1343c03000700c0300c6112070700c2e4003145050816001403141aa006401080020707501c60a9641500154450004c0724896440c40d4140907200e0008105101560300c500c09099140c00941c0d2602c518681c0104100e44c0480d1101d80c0c0000c2c0050084069801401420f0110f82e42500b2500411184203a81c000141004001d030740f0602100c4810310 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 830240827 1250 830239577 830239601
    0x25060e0616021f140a061401050a0e010818010f021b1c080c091201020d14060f1c05011e27080a410c0c120a0f03090513 53
    0x207180b200c1c0b0040e043d01400010f00384186400140c106620104010840c400c4034041e00d1590307510420702c99003268865808040a0a01c4d056040c110500c0700034007031b11040405a03050111820024001000805c04040c00d2121000248491856000e182010790010300c0e40c554508008003402d18401c8000414181b00c410400641620b0f0350190b00c00e070303881e0002901e4002b85140400903820103032134035641040020b070540001682c801d034008000088411000303c201012594805000d00d5039500e6281c010712900c00c503551900014299004003802e81241341c020210b5003000c0c2110007405070b048000002a11000041c0040d49182c184000e000c0810381c044180f441a000203036011070f1040700540b16461140c240071020160000c1c1c1e01000f09c500d0701c020303d0140031184130300546600d80d1003017042c08806c602d50700e030034800024299503c900303400710400e019001d030f110b0300d50403103000b0040000f00640040071282143c009081c02005c400440c003030709000700075034049118800580d100368414140 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 830242077 1250 830240827 830240833
    0xb0109240603021b030a081605130e010806181b01030f150f090513080a03090512030a11040b090111100203100609050d0b0a0c0207050405011e060504060f0525060e061602 75
    0x680c5582c5000d0b07081e0755408c84002c001c03003840344000b202c108034004405080656884546503160082d22454840024612a000140504241514580086e0300e42c0348298022011810702c140d01c004030024811040e91f00606801d020345204080036406661f0305a840c41d803003e0140d01c1d1242c0b111001e403132058550b2054406014040c9000c100d1380b10240c05510028680407070304000c0740d215180350210303140000308101400814804c07090103d00c1146032000b09420301a00b040d00e0460007006074020703052860f060001440226040401c140048000306030481811502c81c1080001c89845121074058207002c520401804651882c100c61100b100640c004a420b0050340e03a404200083c080c1c00c142c640a62061040c0400d2507900c50003840d0203000241700e020f0594510041034200700ca034135406103050000420043c80a9603101c680083d8040307250034101c2e43c0d13616190700c0341a1310b070b14005c640f81d01407642e911038001c100260700f201044c280d203081241e4244d00c0f80f00221036003070b0305140e0b2000981c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 830243327 1250 830242077 830242081
    0x6031501141612030b01020f0616050f0307050405031501120f030905030a030507020405150a0314031908090106090630140d1b0b0109240603021b030a08 67
    0x9031140780040c4100d034190a0050518030055908201c2c10902c40b01200c002664501d0710a0095051240d40c0c00581e007407000780501d401510040c0d40f6080f015001ca0038402802d4500d000c0680554100c41801d00181d004c66520319000300020116001409190b2290003188490300d580c4540da6041410f840d640c40d2070003c0412180d60b015541400798008400388008407000080c1030740c00340510346405001e9140d0a030fa61481c1d01c108421158000c1110f50070070621071020085884000303903c1d0a403903100407504101c10b0030311041881c600600c8107004180f54080100d0300340c5503000740c0103406550b03c200240311480d118182003082d1071550007120800e09001c00c95418410040345048109034030404848520ba40903214101501207060110790968000c075601000198480e0b661944503514640b20050030605903a0031500c4101031042c1001179403248003c5012400c4068070322801c102d491403060703505945000160103504210004002e0306c00410500340d030300d03402108a078503140b11955000001c1d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 830244577 1250 830243327 830243329
    0x1c0f140f1b1c0f021306090b100503060603070c05030403031d0111031c11030f01030c080f060a0c051201030c0614070b0601050307120905060a0b03030a0905120f010515010e060315 79
    0x5020b100e1010746a018035640c0301d03805a00c2d0300e0308046480c5181000031a07135034100b100170016034120112003802591203900242000e0b80c0700d400e682d08040c0469040e60303282c81d01101114440805400503160380000030f40041016000000324041a910300e02c408441a40000107560500300242c1c440841c0d0410400101403000d4a0203881401061100000380d0a14050310350b01ca0ba0400c8400307041c000110801402406080e038041001003100000405d256104d4000240e100c000186c6018110b03501e5100a0641c0360080003644d060003600c41810500d503035641401c0380b0b5807145224100201e23820000285601030510121035403690810b80e140d20700c2c0c543c000111807503440281800d04002600c14415000801c0340516041240541300510450800644100403268841d01840c0b10303920400986d00102d40140742c2d0401c0380c208450700404050361444881c02c24140e652100f406510b444104981d030b291030581000150001e0b03030341c540c600c0d044005108461006540888038414241e54580303031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 830245827 1250 830244577 830244619
    0xa180f1b080105010f17030f0409050709080d0f0f0906021506010201090818150c0607030c030f0e061006020111190905040507020307020909010b1c0f140f1b 69
    0x2521504030080325045545800c0035084034400e030072020390f040c03818000b04000c4240411080c0c000103a40060361401c0d0000112181034450b611500c400113494200050455000e60503003002081540c0640300003038080b0303100030011496460443d000c0b9444c90800c40b40c0382d2003205080c00307960040c0c0003800c074191045180010140000c1070941150f41b01c8401100180b4041d002d48010b450110000052002c07020821103114080e224145d0078240a120001452030006070003a008203060a000658480c0d621040f00079141d460741c1c8580307150034403100740d41c90b503800a811846400301d0070700720500300e850345001c0f070a075402c03200e2071703000010140542c42850003413502c034041d04041e41c02c1041c0f11702c0e40c4501080584a041f0388c20307000758001080d0f03c0d040d810f0100089500a0301840200420510200000c11102c2d03150a011200400c0846280030080d4480c9500c09403a00510070064214240d094907680300c030081c0301c48480b40162100c10000410210420808000091805461300165048000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 830247077 1250 830245827 830245853
    0xc080705160e0108100203131410020f04061b08040e1906030b01061d0a140f03010e1f050708040f030323070914060a050714060703050a180f 62
    0x3601d004059240708503518000114006050361014565150b1405900905143c10003010001c41c50041040004203280c84212411190f80000d22410110311300c0c80040c600746040e0321200790284001003035030207405d003034000d0004c80748281c1d52483c0d10395000502c00d44280549600a080709820b2000b0302c00b85002490080d8071030340c80060411000a41e00c0c00d80c0c250b5800d6801628107001d0000184502e540c0005d01096803070b074202851a00801032000f20f00c4c1500144034010401c5031540c15040300380d031464800f00d07904000500920607903072015682c507190154107045000e41d00c0000001485100c140c0038036031149a00e51078031512650b03140c561402c0f5602e605001c60070103541d0b00c030741000010055035900f0002d050b030740319524a00c0d00b804040e2030590203400881c241c150320700c600e59483d5585801c407070943c1042c2c58455103030401440c00380c08185490f20310004900030881045040c980c954401446400950802d101d100e5140f032600720884203200300602848020242d1402099030507038030017 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 830248327 1250 830247077 830247083
    0xc03110f1b030d0b041a03100203060613140a1a070201050d0b0d030305010314010e071e0e150913020f0907180e0406110301051e0301020d1107050f030a0c0807 70
    0x1d403050707601009050039075100f07015404205645407160310090825108103ca4058000e611052041603400003030b690700081804240015000000030f400f5840d1038059404100e2203800c01d48034241c47d000c0c0743d02c03004d05100700a03004224154000590540510803039210591001403646060304a4004640303590140b040380907003d0320703141164200d0700c66030399642c15180a50342c0014154194600b44459000003d55900646e040c40003616042d600480d22004490301c0300b1041d0708800f034521179841f900c00d40d60f01001e03600441c0f10800800050504240328000021915914240e40d0452003101d4410a20f80c069003014950710401c10310304100c1030745600a100341c104070b144140c202c40001f0a50317065400c85076804400109000c10030600d400b41d07034011071500d542c0504560414000c40c2241c25201c4125114040c5c1001120342501e0a40c101c032105e00b00d0704001e2162840c5440000e400303030300c11801110544290300c035170701c030000010041c0d0f000c1ea0b107241e0324100c24020f0b13510f914a450f00650410b17 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 830249577 1250 830248327 830248357
    0x43030e0607080a09060f0207090b2e09090207030e0402031008060c0a120203060121060305010212070e0901030c1e080132070906030c0e130b040c03110f 67
    0x12600566441014000c0c0354865000b003030f0b40300c100c00320090008050764010710900041c00070b502851038002c1090b50903203050a80002c0c00e2074a42c4006012092800301e000d80b50380e4040540080c46480c1c656240010303aa40e281c40c54007079030702d003204022881b44403405000604403510798802407170300f03800458220840240d0004a6034030303a940c0780d08025040d10b1009140c50300091580102e0341100151800f822100c20850a514050b80060106c111030103c03e60041c081d20500b120701c0d0034541c800720166030010001c40d103880c800114410b150300c007640c0c3c1c103012480c1502041f91070314021a8860513650f000000300f021500d030000c051451403074441c44028030702c1100d4002c198401d0034881e466948101e180500580301e0305c80000031380304d0310b44104102c003050007200f082a11038104926404881c15840c000825510401c3c040b112006000d644541c001d032010b016043d04992a00808181c07a0704440800010015030070076411514840c3c416000d24405000c4090400607410280150703030011404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 830250827 1250 830249577 830249597
    0x601020f010f0c0e0a080604020108040f050a0c031103030703091a07141506031506090705040306091101090801180807111c05010b0603040b0a09060e030706024303 72
    0x300d182910b2024524048165440310b690381c0c1e450740005906000e000039280c401c811800d002c01e50380c490724001c01c040d060202c02c0010804110101000c4050980c00c4020790340e0841e140d00d49900064034911041d41d035a50001c10a51840ca07001c4121814503030f050f16008900c81c40d003103c260b62015016411a0841c2c41401b603080031800c4500c3c407c0d03246441001401070300403810381d00d5903c0040a0003483c02030b070020004150001120548075006a000c4650b691595504001201c81d84541c1c0c10061a150401081c01b0410480c010801d009076002d80340d440c491600d560049088072421850342c00032640144802000c0f40174030004140d00c6004842501d040c404400209501c202103403a000d1781c42041c1c0d030b80b03401030050a01c59502c1507a0201d448500d07500301034881e8040000058101c46503542d9602c0320304c0811900398090325189000a003583d80b101003d003000c400130b4010100d41e000c00c1c0c4400914045607200c42d404100d0a1041c416400b14000c0000c504001d0b05d51390200031001d200581d10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 830252077 1250 830250827 830250853
    0xd020f03030c1005090a050d0c020f0607150b04051e1b0c1c03050c0414030c09070f181212020705030a12020d0c020a09111605060402011d01080f060102 67
    0xc102c1c0c4031005004101c2440080c600604503080200701440d00e800c5400f081c0e0004101181e100171030081c914000e10f03551503500014031002c0d08160b0080e4084c81c00251002003181c0100748064004140c4001c000381d03500c43c1c0520090707481c03c4900c840e84600074600c0745000f40555005540043c0f0b00340068920281da070b100301086a104100103821035120300000c41c0441c17840391110300c0b0714820340703030510143c100510f000300c03e80036500036101d0b144035003d0412015202080900151100244080c1c414200350301c001c1c0005140d40700b2a0006a0b456007091203900b481440d0008451410324480c01002594031000d10068401c030040301103006018000945507404c00c081d410060098100011840403000080e01e0001d0441480041c41125840d02d005603a5601505040b210111404919241001446000c0d413081d02c4000080000b0070f50b160081c884001001c42c8114401c0c0c813800d8500c030002c0b100c04000b4004400300c1e4000349038403002030000181c03c04102d4016106004480c000c09001c0303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 830253327 1250 830252077 830252083
    0x80907051c0203030408010506090c0a0206060d060f05040b1009060302130c0c060614130b01140d0212040c03060507050c0307030f171306060b09010e04020a20060a05070314060d020f03 81
    0x241c400c803501d0307448d0400e01c000ca1400c0c02c3c1e12500141808045c51421400c180c0203910340100920f40b51181e00084064000c1c4940c1d90046056594403440030041e80c502851b000302100170940381048180b040000104080030548130b50307004c2e6500103005140c2142043c41c02400351030b02080f0141040381904a0500050150203003034080c1501b8022112401890f00521501030002e03e1100042800d144c5003c09a913080000443c01100003030300550344280500200c4068480c240400c42e4944c5480304000038800312000f00070540c0d10500050009132a07400d01212a4020708000001c01d410812104d00040e01800781002f140345641805c0282984030596955680e8048a9040c02c10b0804e645201c2000654404c440c0540b54000307426080080020000309103034003486009028641c001303201c80d545c138001c40c0c0c05010310360445491000350445041098480c00e040c0c4605900d103041001080f09a07010f401a903d24180441c01e1300007994900082045544102c1e42c20b9812003c284100c25007500d081c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 830254577 1250 830253327 830253329
    0xc0f0d0c030c0e0618040212250f0503031903051e07051209010513140c04020715050c0703120b180c0702090f0403231306031b080907051c02030304 65
    0x1e5801c1d0b510091520303445040c003007401414184110000d01c5600100c00221003a260016016500001c0e4006590921460041e03403a0213056000301549070649180c040f900c1c038105484545401c8661540d840d803e055032409402e1447c406c20192800101c42181702e82d000551002c680540c034524407100c240e180307103100c90035520000015400a15074526912a5041941003104031000b04034500e09500b411002562001c402080e00d0200c840f269101ca10411401d035519400900456807004185130481111100b4400003240a09103000504018500c0c2d05642c5c0d100c0d0036407120102c07000390024440081c4000800b480e4070002d0042c0f0846040140c0e201d55200b0f040b44060660395030713000d004021071044000c04e43c207400307d407200800c000640e00c01000009a86c0c1d000c14011104602c0166503040d002d5600302c0f0000320030346203000881c3e59141d00800754000306045e050452403940d8a0480b42c502003180d06c85025405400708000a0501203440c080241d0216042d41d1600c0c91070340003c2c04c550003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 830255827 1250 830254577 830254583
    0x20d050f071205030a0e0f06070f03062d0e19020c031c1a0a21020d24060e0601140a021609020403030e0108070c060b0a050414100f06020c0f0d0c03 65
    0x3000c404c10543c0100707440341c14101e070100c0c4010b141f007078445d880c00d42c0e403450000c00d000c04102d50f035110210840e0007500068040c10075944595019040722446500c0d440381c200f10452401d41c810700000c0c0c7e405808041034000c0c100007009865500504010602a62007550041c949200800ca04a960240900d081804070800040400c9510289a6142400c0c103a02040c1d4030a003030701c08080026401e00e107100a883e00141821250000c1c0c14000151030250641000d80030f0010a03040e01c2e540d1500b003000c0c042581d001c1408205658607039044041c03180040715a640030a84440310f84060720041c00250040701101c0c411150300071401c0b584520a41920f034040711046d6000300e814001c16030040040401d0780000e2808400c14504142e00410110f003400003e448980d0314800d0380c000703403070b03607118000603107000340061040d4104201d01c10ba01c00011036100d540f00005440100308071070101d0340c40003142d11540c014101a0303000c4040001e0003695042c601d6009985604010000f000c0700c17525001580 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 830257077 1250 830255827 830255837
    0x12051503010615050421050303280b010c0212010b130b040608010c0503010e0705090414150102030a023a0908060c07170a110115060e0d03020d050f0712 67
    0x112040900d42074646a8200421200c03003640c2c040c989960001c241c8045410402c04038000505030700c10449a100016406006404000104120f9484001000740d075001c100a03200c014004024400003124034010166000551310f58050307001d450700407000c0e803401d1140c80001400403080c0d00042c1c0001c9510030340300b46403601ca003510000c42c98540b003044003c2c04080e00a01440c40e60b840010420722050203403080120500d00800c460314403460030f43e40901005081000b02400c0c0c1054188891801c840041e929030102401c0d02d059480407096500c00c15036034000b03150410804a0540b8410810290b000700c0030351000344104042e00c41020700c91110700c641c444940035801c00038013a040c004010300c00256000c040041100044902c4000341203418003c0f01951170b03d2031060100c528070704000070007070b03150b0811989201c540d82d00b610810450b0b026440c2c104080c0c0c00074050101c1c0411103003000d80560001d031030220350103010380e00419200302c3c0304984901d081d00c1c070307564840106030282402c00010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 830258327 1250 830257077 830257111
    0x612020c0c10200f0c130902090406050a18150e0a02030a0303021b0f0c1521060102010e010e0c0409021504030809040e03090a09020904021611031911010f1205 70
    0x80146644080d00054071009440c403081040c94042d80ea0400707080c2c840c090401842106c032008015400f14912560040c5003004178109802c24102502c010b90708420114541510101062140154000f80c55441243c03e00004100b400850080590b0581c2110b2802909181c0006940610880c0e030380c148240c400585410b10924880502461350091a0040d4408081c1300c42c0140c000941042c0300d507045500c1c110f0036103002c2e401d241034003400200b00d815907941480c41800b10301003403c0c2803048400303078020001108155012400d0360070071000b96045400c204070504150800d600308000301703030000d0b107083c080308181001703000e480c5d000390300a94986802246102ca245868090307401d0301c0c480324000314101131416000615420492080101140e070004104801d910345406440e40f03502e4241003010702c102942400300009555034815486030041c80244103004645840d02480e894010030600302c4150400010356174079246a03059800e001da007995880055119001ea188281d60f40e00d01e0311489 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 830259577 1250 830258327 830258357
    0xe06010905331011060702011d01090b150f090403030c020d0804050303070e2803020f010519080703090b0421080717040c0b040b040e010504060612020c0c10 69
    0xa101e85003426a01c0500904400005807081c070b06100200031100c0500d40845010280c9540c0c000c42911025800341c0340420002c1034042d032200c1031264003240c03a451410f01700310b030581c209d61270050010141e14059011a001412225800c52010009003541003085040390018156041c01c89044000a0f00c941e812102107505102020450155042c541c0c0c0d00e080075601e40d902d90100030284010001c80b42800300e0b440c1d903400f5400e0580b40e040340310b40c2c1051a0b620700560070b90507580002e0f40101d50501100440e54854421588903101e9242006010b480a0000b1204224041c0004080584900301c0034049010b004401740101d2151b81340c2407100880718289003418011030304403410310107040100542e454202d00c003190f950a82c0391003540d0a903554500580c1c982d2164205800041e0b01040100d405841280140143e940c1300c0c0740d0350a240e030f0b40c00c01c0006940d41d50060b04009035485144d4001e130f40c101d8020f0004069602c00b503500c45141d00c004200303c1c0550461000010700035949448038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 830260827 1250 830259577 830259601
    0x20417030c010e010b010c1103211c050705030403050d060f080102070b0c0306030a03110109240e01450b061507020604051e090702030301061205090c15070c06091d0f060f040e06010905 81
    0x82009500418442840c00dc03001400714000100003134240040022810043c1c4229031240014006c4841c0d41d9031500c1c0c9960906000390400c5c51300b1261b00d5128400705561040e60801d5038030030000100107201314140d81e5012155000b044481290b20741d02c03042d66000140a00c1010039111140d900b03070159000860f0711000585a0704070420156034034000110003070440700b00792588501280c155020441c1c81ca41421b0881034806041030240c4480440310b0340401401070704090080b40101ca110042003141c0c992040030f032140800c000d602c0882000108110305024a000c031005580c1260905076139100b5002c100c0c5c48800700c2e046801a0000801400203640000302030794084480b8804004a140000980b691000410601d901c505060502140d0000141080700d424550185192400715603824024020000c40c0c00f60340380025590344801d02c1c41000300c81d060320803c81c0240500396912501c007480f00b02c621414442d500a40c0741e1510030003280d406c00c00c90b4000c103c10940015a480e00e4490020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 830262077 1250 830260827 830260867
    0x10b0c030c011b09120215130504050c0705060105060a21180f02030106120812040807020d120f030c02031e1b0703060b040608030a12020417030c010e010b010c110321 73
    0x54210104141702c0268444000d000444108446601e945400e100608200c10926a01040d8403030700300020085840380c0c0c40043e210252240e001c076a0903980315010810300340900d0407404001038102020f11800d03000c3c00c00c1c0c0c2404c80d040700b0b0700050b11211000c9401201021001c2612103a42880440301182024031a80d0001d003811480c04000401560702c0214510586410503100403103036020070240103405040760001503005000c51008403052400b0b04220f000c4c089510b01080a840c00082c0060007401622500301e10b55016500d0994030245880040c00301000300700504c007061104030780401c0904240d80460400707800030f110403861858000b0a0340c24010703010780528100281000740c1007000050320201f509504042c0207078030718042e00100034007440d03004150301e0400d031a0402d4100000701c01805408d241c40c00900c100081102d4450a03225880c0c1c0150005041203480c4020446000701120b044500400303a804988204200101e07041c05103502a2081e5000510740c4607030400002864 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 830263327 1250 830262077 830262089
    0x702060609090a030305100b0327030a270305070f0f0803091807031103070309030315051507060e061f0806060102190516060f090801090506010b0c030c011b09 70
    0x40c1da142035810143c42d44040e0200400340750b20b40c804600740300c00707800179038024010315403031591207280c410004500f052a00d00c0d51000d034400d41d0381d2032404040110485601c5202600c507114070000722019000800d0498030303400d01c07018808401200198041c00000c004211203416503034451704208001604c0c0a266100c4942c9910400003505203403a00403103280c082c0088440070540d0f070f480784816405442050f51940f91202c0010070041c0d859010390060708441d0017139804201c0c402851001d09240090380c0503040e408005039020a200d680e00d0340c010101c20f07103d40750115031065142101443d10400b9900100000c0040b0624500f0380340340024074005080443c0141034174142000042c0d00c451490103849202c1803200a124140481003007415118400106094550ba81d548001000401d403107030410001a88541c0005c0c00000500070621483d40040143c0307050b92900380200c0d5998001c00f01c0060502050028000c1e0100c203106c0e400c1030110020080303980c60380d074145c0240000d885810007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 830264577 1250 830263327 830263339
    0x1e10030b03070b07020a2d0801060e070804170307020115030f02180132220f2310030c1806151b03050d020708040f0501450e07020606 59
    0x1480569200000441194108000700b2204501fa044558484401c8081c0d20b00c205110040040c11080c158000c4086070381102c1184802e41f10b58004440e00403095601410042200001031101c3d0410b100558000d1264000066607594801464a00d074260f98402c0e240c40702248218415400e0980c00c1400c912014466048150305010110040c00d84280728114a0907220040618500b04900710411f803e00051444080c0c1c1604108100a401c2914120400d80e0a140715070030044c03041d000da20102d9603548148682408240c0140342000e200510b0b074105004421070004c0131425030000c0380060501082e44070104109100810140c4219922080c2e003003906050347c1c03848983c0300c40140e401000c8108098003003107081c201221309014202c4142c070f02c180300040c800100500301c00200704540c1c107000f886081c40d80d1340005517030f0310391103100d14038089840d45100c0a0800e0400e08901180300c04005900011003090b1100c14048400d40009002440c403106101ca99501040980e0b48241c00f1a52 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 830265827 1250 830264577 830264587
    0x6090513120e090a0510050105190509130e07030b24270c0702011103131205011b270303090b1812030a17010302010507021e10030b03070b 61
    0x8002990580342020704841c075100c26007800988912800c06080c10700800000107420600100e04c028a41501c0d0510f02e11940c08001402e54080e1b015510280b54520b10554908021503003900d090740310350185680aa4009000a04195148142189101403d0082820500b9481d126818a5001c0e1041a00440407182180720b4000d9154282c403020013591322550501855600c1d1295000510003105408141400c000c403500b100005094241d000740d0f10304500642c0341304000c0e2284104040d0181520302d02ea0f041c021148502c0710980e0707403441138000080c80300c0d031184090a09040880058001200c041098520f02c03040901e075051100302114412600d491564041c1a8082d14401c9d0300e40180c0114000d2035004880810400c014030151101442c0c1c07446103c00e07910395004a582c40003144841c02c00c580160207002002d4141c903410707142d8610b45411038080040142814880000303041180301350303010750740300c41e158040e410bc3c5548010440d6040b410030903080081036041690248400d00c6 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 830267077 1250 830265827 830265841
    0xc0303021626160608161119030c080316030b09190f020c0f06010e07050c0304180b030a031701051e0607031707090303080601030204080a03030b2110060905 69
    0x34203207856a00a102c5071081c6400041003d0070000000080b202c9610844000602107410000951040100107281912010807080c00d4581c00c50400c2554610b601505c22496599101d20350843c40364041d0909800c240583c0c1d4a06040758412108002041c040c507442001a41d094011003080500407542e5100c94901061013001c00010003030342060094480c0844484070f08242c0c1181c0903603045005031030440c1e40004001e40d4070321083c440d420742004400c00049805100d4000e550044448002071403400303117404030351351a01810180d0b482555544683d1b00c8019030f0704012400034144070307495400c0640301441d4507500181c0160710460052840c03850511610030008070410503840704841d900d03102c2c8003e04040700c01c00d4001d42003440d00f1080c1024040c2c0c881d001101542103910a81e140d402c940c0d9460b0045080e40900e02c035040c110f50020015a001900a4120003500400038004d04015040c802d00030240300c4a200c00e400b02504032403100100888140914405000789440c20b121070708101c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 830268327 1250 830267077 830267099
    0x3020607030c11060c03030f07170c090102070905090d022a0108041a07050d0b2b030e03100209030f03130302060309012307031b05030c1c02070c03030216 68
    0x300804000d00c03000c600080001000d41c0c080800c401901d003903260344c50072a4442c0d41303070700950350580c40c0c03002c80c40022021807085d000d0342d0705d4915002240c43c0d5601c078883d0b080307031941111a010b41580128600425a42c00505ca071900c02c00c45500242080d01480b5000ba0034840704115086000c42540b01904480300301501c5170200d9a401e01c4c00843c80d44c0c440c14500b052080d03441e00c3d2000206d42c1014022902d40c8100505030420303a0003801c0002803100b0040100000d00c00c40309107181c603504101d80c200324a84c03d0440b40c9641c06070421040029902c40041e091195814001542a601144000b0079040c10810080d22442a40046250411901789003103030b0b44107403000901c142070000c00600d01c144290000340f0b50b028041074880310031268054500150b4400c5032080b002034503040140c5198030b0401021154240c8540311640346884079940040c0076484070302c40441ca120381c000012481c45091005114a5005103501096a1300390314009080c84240300102610505000c0306001c0d0003144 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 830269577 1250 830268327 830268337
    0xe1609060c14250e0402010f030902010e09010b1e0f0d09031707081e153001060f0f140910050d050c030105013318090222030206 57
    0xd07042540000d00341c0e1030085000b0918020b084400c2c000d406090f03d0251000e42105040d06184441800803070f00d440300d40501d520704480180c00075456040b0800d450380a5400407060500625000b00c0f41c0f070380c10700440c8918600380e2183c819a18005501c83c0c40304442c2c2c544014920414070031911b801d03582080d00300740c0e0040c1d80072104081e0b503130454141010300482c4000e00c422150601200c6619000b007006e07155001c100c81c4142d030081d40f400c02c032000c030002180081c441c000b01c103130b1f8401c0340c440e203002e12501405000400900500601d401d0b1880d40d0301c004001401d90180001041042c00c1c0050500c0042d1198000120802101428001903c020b100f2800640050b02c41482540d141103010549440c180d008907040100c0000380000c1c0324000c80c000c024040306900a00c4281d0340c40450608522060b60380d04441e209603c1c491040700841145550a24600c1c0340c91050b0304034440c079250038400190311030162070707a0000308032024100e1801c003190304282030214441510300d541c01081d141c0c400c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 830270827 1250 830269577 830269589
    0x12150115210b0a1703030f0919080c0d0305040201051c0f020c011d030310050d0c0b0f0c060f010e1f03080a0309020109140307060c050f10060e1609 65
    0x10400601199610031008003041003038456100d541400300081e104001c100c5094107a0240c0b00444010a08084507000980c2d0301d01180d00840c1741d5500d007841814502000b9141c03201a00130280081c4001040c90313011003400c0e01500d00c0595814211060900c1c02103843c640d9070525051004000c00740c2c4e000b4041e070b802e24444010200d210b4070360a0030500149010b14001844038804928104494015030000c00482c505036a030804407004600415520f02086030402404e040c545000d102504048442601c6c507441882c2e002401902c0c0c003409035164004804c159100500450702d048140810000a60000000030010b00ba95051101881c6007240042000a15076601615003030400d80340c401c40d60007140c10108141d00d8110f00c8500a001c1c250754103050b400a0038140001c25051500368100000c402c0060003080114580703c03043c3c8a2000a107010749007401410030b050345a00d0305022600c0d01c807100b071500281060900b5286000c008003d0000318007060514061940150007814820030354003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 830272077 1250 830270827 830270849
    0x61e0f0605030c13061e0e090705070218010b03090d03060b0304021c0c06090f0806130b09120d1e090b0601031a1206012904030b060409080304050606121501 69
    0x360b0031034220a0f0b84140b0a0702002d55445440000705141d00030603403403030120311440030681201c0c166001c9802c2c00c9804e26650b848142e04002c0342c42140035030010051148043e0407041c41100c20b6514140e425001d90005400202c000200314010b00203109410440055040401901e07091144200381c0740801030000380520074040e4441804100d02c0f0803002607a9001c010240819141c55000b840710202c0e103c0c44404900c2c62001142c10070340840c01d6889801442c2c1105907040840c1c40e41c803144100139000015074060040022400c0d150f80d002030039002c0c1e5040380880c100c4000e000880d40e100425018411207803410400340c0010701044000c503042002442d02042c03004058145800039815800415884610340100701c1025a001c1a00c504035540c2c03000e415403014071107100031800c0411003d95a1130682c10841440003038180030314190000800f5200058144041c0e54414140c1d00c10740c0d003600c280d0300c06c204001c0289840e84441d80a04240302c05003415000301a03800082000c18050405904 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 830273327 1250 830272077 830272081
    0x71d130201050d0b0402030406090203010f0c050f130e09010902030c01080708040b15060a090509060f010918060906180b010905030c0909010209030610141f0f03060803040801061e0f060503 83
    0x90f42c50b03040340e4803070400100119a642403516081d0020509520b04030b00035401c115030b82003a00340d18482d02400d004540c86003480c3c00400461050705a029102c50000b8000c5510085200400a51914810103d010001034825200d00406103401c2101c124075042100c80e0040cc00d034641e00607a5140c00c00e500024451498a40818040341c0e80c0480340184c1d085100071524034405036001c54108202da40a490300c501d04d841d44418000c00010300b000d02c0e0f000c10440340c4100301ca510381c0328034a4501c81100000252454550500c3ca0a44800d40d1004400b04250724a82505240701c2c420703000169802d082560320946418003080d00d032101040060311401c0b0010020b0104c0d5400c0d0101c4200d04801401d4030701078544980724026509a5005086803031b460544582c0d072600380380d80301c44480c90003000e07051840783c1c90420458402c1d844481170782c10036480d09800a0340400820160028050440020851509092440b404007911500306004035031414010010f80c1e140f8004142a14141e1034882d66075 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 830274577 1250 830273327 830273347
    0x10081b1c050703122a05060c0307030b060f0c0c035104051c0c060b01050c0f01050a18020a09020f040b12040b06060a02150a060b0309071d13020105 65
    0x2c80c69400507107620644020070056aa0140800c03001501034a0b0031038191141031030001d2101e038070b282e0090103a400300c00440da10006039000341d58841203078074011682d80c1c508008101c294110300c018450428003c201d0b11100c0e0424443c61300341c44026801044000842c03e80f06054020315600081d003218403d82ea40c0b201002c0d15001c10308001380440e001c02c20f50011b4090714043d4011a019201e60081d0900407a40640f0300c806151a550241c1c1d40b00894216070725010000d01c0c80a00050510904000003d04503e040c402c0c485402490000000c1c2c1c1d107410007c400580d036002c60116620302e5001001001a035420f80000c065a884100042c2c849280c00d411103510705c00c075000f408207214040b8029004090b0180340740c0c0705a215400601030b80d10b50300d080c01600d0241c4016800583c00125415404c044c200441ca0f90104c0303089400700f91141d032218029159402a02c0138111750300320381c0b01404a42d074440c0f0382e400c0c0789032508810310711858202001d803e1115040002410800001000e840e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 830275827 1250 830274577 830274583
    0x4020f01050309030d0213060201050105060301030b060f0a120c05040e03070309140f0d050c01020c0a05030a06051b040905100816090207080f0c0c150301120f0203010f0510081b1c05 80
    0x3085035170f03000440d581c045000b550100d4541034407aa10056082600110b840d050200903241200d0703001541341ca0359120309040050040f24441c080350060301c4458001794680c10964900c42c4607005140c15240d403400c0105020950300d003d0080201c5610410403200000d9002c00040101c40864440102d6604d1800019401c13100d01079450358083c411401c080103200d00820b407407402002c01d03021541c03402490f0041c0050300805200300c5034990044468040440d416030001c5034003000008100420647c2900b442d540f0790003079000f040703403542e854040104400c0c001d2814806440708000401c1b00e04100210903021200601598024a402044032010011003d040e1030074040036807031941d20342c2402c204841da01c5070411225449030380007208280504403000c040328142c0321000e01c0d0103000300e52a101d12080c0314207072134103c0e050b65942c2035001d08400c042c81054065000b1001400b002850003481c5440c0007440b0005541d000b49500c040710751560340010f20070100340c440102c02e50580c101c3c01d0041c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 830277077 1250 830275827 830275837
    0x90203210307020d180909030e0402131a1213082703010b0111070909031106040309031406010f03020d03110f100606170a110d1109040e010504020f0105030903 70
    0x8512003505000c0080c4218024510940031a401c0300c1d24501001c5044451840001c24011040700a0106022101140d042850001d002c0e050081480d11042e01003402ca1b03001e1140c10200c9d2601c09000d001c0034aa030041203c0e40100e000702d4501b844031401c80c10300c40c1c9002030110140701d4071003508a010440c0c000d058a400b195146155046020014282d42c0d100e070140d550284030354640b184140c00d56005142d4044907503414001040d83d1401c009c9103900070040f4507401c1c1d00707108030b015003950380200401102d03110314400d80d19041c400b41703103141c5005070380d41100c50f44466400c100014070038a20401c02020843e0340482c4c0c1e001c0b0310140f0781030981e1500c1210781c140b001c078099043c00843c404800a040240c040118a00f085440d139100d508555103d2099a08844070380b40c02c0101329000f200381c0001c3c2d41092030aa00030b10740405000078108407070100144020040010401c18801d1a0610914035100d0341c01009110758580b580c0000e184e00450f941d054103005010010501ca2031003001520 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 830278327 1250 830277077 830277103
    0x1309020a0812040510020307031e14070f02010801270c050909070807021c120c02010b1f263903010911090904060e010b1816050a0e04090203 62
    0x28441c5108200003010b580c0c018000c560050b00402c074407440040c800001c8404158141d80c401c0c608441c074480402c546003801e030b031210802c1024550040749040c60780042c08018850350801000010a200242050760164440300583c00b41840c0d030380004c0c0c00c004071050740c49000400000e4603852150b00341c03028000d40c4003a94201c0d5062041201a0390011070190140305990219040c4003051580f035a82404500010800141500c640c131034014110341115020a203140004690607030a138002c80c0382ca40031240003968a10a1f0381c10041000d402c084a4070141c0da00d20058000301840d014100d40103e0301405c809980d1a983d0b4072424041d00c80c2c100c1108008503500307154462403900c3e042c401c16801c00c3c024007a0b07842c54420f96480f5a50650202c500e101d82c050030102c1d00d6a00d0781c0351341c8000c2c008107181210f19502e980b200d0115030ba8103110520030b2010f04081c0d489900b08100c85296600b034410070103042c003608100c801c03d140e0b00f060054011007422580801c8104952000c00e0822540002078 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 830279577 1250 830278327 830278333
    0x40f030b04021c050a05010f15053007062d080711060a09110306070c020d1a1006030f0e100b030106031709030d0f0905120f0607020c0a0902091309020a08 68
    0x43c8003004404a005030544d40124024000d50400c9040d403011503030040d1204034401039201040015081075100001c1c8500310400345400f20106910a049801007650a02c000b608511028001641c00c102454003641f4035115039150380781c0364003142034003182d0030152500340500000003a540f10301c0f4211440e0001d0002065852600b88201c100028111240048500f00140800801e442c100000d02e244128034580d83c00c0c0380c3d110b02c6d40030311182c8070344282c050710030f42c00f40101400440c411b02c030780d1170041400d0340b1041281850903100400307c40107003001d80840d50034214844042d01001401e8001036040c148005114844c0400003401001281c0c03008103a9010007940240a11700c03907001d00450b00c016000e451000311800380840320034220741481d501240345448180424102050600341c012450003c541040075145009841c0c542c1c2110014016030002c5a1040d503420000c184400601c4c010304194101401e8500081e001c581d02c440d12216181c0c0e800d00e071002c4d56039054010000300050b10903 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 830280827 1250 830279577 830279629
    0x30c030d09080724111e0d08090102280c02040f02070605090d0503040b1302120c0112020c061504060b040603020c010b090c0703030c140a031505010203040f030b0402 73
    0x3000d0080708481c07040c4a03150061410000e4a2024800018070341480c6109501805603910300684220481c20200105d520400c1c92000003d41c1c3e11090304000416000240759a01c60131000804c0c01600070204946e5174010300005d010300f04103504a944005c41d0b40c544804042130040c1c110380b0348242c01c2020b5401030600c0341d144644041c5a00801085000300014461a40c0d80020242d45800742300c1402c00182080000401103245d0109440d04070650b0000142468859000210080c0c0300b80c032030b2011a086a05800115038000088480d070041c603090950030002c05522a64540e80000c01c0d503500760304003d007050080e030744562120020308914600503880d6030325108020000e401c500760b180d003107618001c201851031802d1444684228614800189405540d0b50100c02800c0d40d04500b000740f14880350b50812128802c4080c14020350b40d0340d0000f856002c16039462051403525030005040d500100010311000e03410003000700c1540c1d004103001c070341a210740c800300300003800515800e28240c0c500c0f10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 830282077 1250 830280827 830280853
    0x11030d06090605030705010903020306071d0405070e090a180201051c0608030703030c020a020a1e08011a01090e010b0a08100504050103230133090509010b1215070e030c03 75
    0x31010058580644c129240316407108019951070069010282d403507401500010042031140c21214030103580c21000e66202c03103551021505490781512408041400354030102c03868145441c000d503100c20350200c00c3c0619030034201c5504000c030b1214000f90400c0000140303484c01000d40c80d4045101c1c20411010031500b5986c148040d12a044000110000ba041c00100c1e80710030310000d1103032511500142030040d081d207001c20703031624038000d603503c1c003401040d5010001d2408002c0c0f15482801020400b00e1040c10819030004101030110740010b140c042c0039200501000020100380c13080d505880c00d1124640d140d08a002d05184002d070300003507001c3d0808001008000300078488042c0034051030010700d0f940071048000350980c2c80e03042c09900c407401800240e500c0700701700f5006800700130451403505041c2a142d00795481500e4044801392203a0307455036568452810800086014000c400740506081d2600e0000c0d000d00c00030180c407107810845130105603801da030307400e020595040000504482140c0641a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 830283327 1250 830282077 830282081
    0x9060a060e06120708070f08011a0304060e010e06010f0803030408030103060b03031e1903020333041a150f0702240a0801230f0402130f2312060711030d0609 69
    0x35503840002d010f442c0b1511034a40540a039a062b200d00006030180c03502c40086140d0180c100500540d02181c44100ac40304884003841112810b041140c0170b046558100001802001d503158880402680104100f001054141c400d803070540f0740c07046011900301d4440000a285014041005108202102c1c0c4945a4100c403c010110b003590455a600041080c8506504900085640303828500b51a0f03055040c0d105410b0045815107800d50420818880c5940407904445202d421544211403183c5040e07094549030401280f4010003031f0301c0a103062629000081c3c580280b4030300900844820500300d00e031001c0703107150401c1004e454080b9610385000c100c0042c440d00f401c0c0308d80c02c2454800302907240070425090f1044410700c009440b03040381007800400d002c02580480f250140c01c0c50074000114040c201c041020f0010302c860a205001d408800d00d00b20799403041c4100c0b0500c2902c4c03103460308182440218207035912881b6410016440030302000c7c0e05085206100000c9511460000082018609a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 830284577 1250 830283327 830283331
    0x28050304090c0f0807020d0e03031b160905010807090e010902090405060604051f180609020c03071a19050601170703151205210c070f031109060a060e06120708 70
    0x80e0f468031418004480e050301d00800c01c1d00c14070016003000055210f854045c600021030070402408a80c5081040c140540900038004c00180b83d5404c541000c040c0312000003680c1c4007510210608101c154901071400d662000c9904c00d041807607464038070119001100307500003082c880d0003500b13410940c07915140803511800202c4a241c890f0f890304003c20000c0c2010008100b440300c0d4010100318081c105003044015803ea003078103401242e202c8501040b10203090015200c8044010021a1202c0040c40c01444080910000754035a84c116070410580c0d00c08900020140c030303c6d8840000c2c061303c035030f40100c844a207410441000c00510000380500103505a0101074404022852586440d484c0c1c41c409105034903a21004d0202da000d00d80c14003489038540d8480042e0480c000d4618a4950301c0701e041070406d2500d0b402503414400c10741041051001003840b100001070112014489032500d000041c50380a094041e036410031145c0c415040c500c0e2118000c5034009a13203141d005c501442c214000610340307182 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 830285827 1250 830284577 830284601
    0x3040b040312060602030f070c09060f0f150c030e0d02030a210e100503070908101508210d021213121e03110723120c2805030409 57
    0xb42c0038000d920030100344120b400f5209554061843c2810490041990350898601034485103548035000401072514814100100001250000c0079890210410710480c007c0d442992000c0f90700d034103a00050351044101c280a5410b041400030b0070210300c00b05032042c6184100941500c180030303162052010140c061081420021078000c14602d80041c00c0b0380308411100c03090340141134028404803203400b5001541c0c2c02100d80c900745500e20fa5580040303162901c0c580f07003040d15030f03942d518620f0401c4803d02000040c4c044800240380c1c0c3d80d0f814000c0701c0360001c02180c0362034072580451030b102ea07551660100e8030000346420441905081c81442c01d0300c2240f2102d012190800b07203000e0184141d00903a8902890344548204003070100c502c0ea429030240010301c800303501d00c0404000d444000303803c1c80011aa520925113070000103400610000c0e1520000340030f4420116007d100d40210b1440015000c404000075003400d800e2820382401c004600c180e01036008089001c0410042014030b4a54000c0c5181a1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 830287077 1250 830285827 830285837
    0x807080a0801140319020d02040228090f120b0411041d0615090c03040606090c080a0b06030108031b07050d0b0f0601030b0f0d0516060309380c0705010203040b0403 72
    0x1d00c04205a0785d408106100300b201e074064840c2030050b182c41081c0701c10302d50015002520b403840c0346941d407494202c0d4020580304012550104205503a003c0c20010140c01241824443c16050800c99503d564905e41d0003130400e110078000408000c0114229101d28601901c14054404800800d43c0c40001c03150040c001849001d0004c0c0c01c050295994101000c006010322110b0340342d88542594951006100341c560544400300080c4000d02c5105c0c1202000701503070b4200c00da00b00613000c3c10607600d1051006105000c103200621801c0e80100c11286402202d10045030b81c01301103184103003032000d03e5000aa02c1468036182e40140000c1d41c1044d486400c0124140700c0c196078035001076040303034010750910b60041c500d80d88084960070000c0740944081d0180c0d08407407010707a00d600f51100002071500140c00107620b5004800c10424401c085221101c456480405030a03005a00d801c40b41c1c500c080901d6140c2c003c100070645918900301103c0100350880020740d500e25107410104904042075034100c2c0015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 830288327 1250 830287077 830287109
    0xc0615050411040b07080d02042312150612010b030609030a0f080103050d0822050c040e03031e18030f130503160e060109050a03060e0f06150603040807080a0801 71
    0x5100b01e003100c0546a600111500745003030780c1c4900302160404d4036a82401582000b001c038010442c40004000000341d2822044800001c070b06121210350021039000e0940d03c50403202e0b12406c500e80c40603600c0302d0242c480d0752480c256121082d025100c1e400d0215054000c030b005011121001000405040f01d403a180c009205545540032118804240720203000303a0042041c042403030384114203050f0441c140b803502890080703860880c201e982c50403001c12581c9030702035a400c0440e0300b003078051456802d107084090f40c19490402100d89210359901c010501c00c95098000680240101180c400340640d204102c1c1d4903500444500341c00341e0720508014403c0e0340d6480002500d482c00084000c150545c0140035030300d0340d00c1d06104283c4420042d10310303418085104000700d800e442d44d240c1c040c0294020000403070b11002c00d218450402c0c4010030100b5498020204121062403082c89402c14488166040e66883e5160704116815000d4483c005048610004056000d00d6028001c0740c1a9404003074900444 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 830289577 1250 830288327 830288351
    0x112021e030702011d03030103061d0313030b0106180e040c0b12040b0c0a050d0522030513060306051806011806020105070e01052118070312090e0c03060405070c06150504 75
    0x80034100145c0c1c0c0390b038010001400050b03c90307006420300600c0807141c0401c40c0804090541581c008004290701090f48a07002c20178031540d80580c0d401840c403401c0071920323080341c58a4142c0c0c420b00d500510030005002c20100d01084003104500d80102120b0311b8080d00c0e0020901180704c0341d030064400303640c001c0c00c000104444141d01400c840c2d0a0b141c4e41c40701c91500454802c07410181c0310050400f42c50082100da4120b0359504c140c801c0550398400e5440941d80d044040200f500504182c00010030540b500805000356110324803400c10001410848079025603c02004941141c40d400b80c5040400b59498001026601500308038042d403056168040c0f40c055a20045030640611013281100411140140c410448d80c1350099030040c0110340907080e03141900b0340d0b252030034440b0b1b0b00c121003100340456103901440c2d2083e8000c002e0821040d5424a90034400095409030201030f2820f80b00c0da80c0d680c0842c48003405594541f01c1e0f40d0f4040018072060385103420408400c0768500c6941e002c0d40c2081402484 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 830290827 1250 830289577 830289611
    0x30106120b010f050a0e150d02042d1a130b0d0b010206060f0d02061b0f120702130b131409010e010509120a020f061009180f020112021e03070201 64
    0x20b40f43e6165902414424025022981c0d501c0105180d0341002175881d0210308039400358001c0407000c858650240e5190b15101c40203880385195510350b80013115150340030b5008200c00c83d14034215142c2d00e003280380300d904210201c00300e03104805402d0001c50088000081c520420070180102d03140c4800100030f141204001a80c41c1c00d0b0858809070710810500340c42c07605190000800c14840e001030180e50510780510070341120030040301c0361008030f40c1c01100d450780c0320603003003148448441444003a14101100c0c1e50108480078a482c0d4404020380d100c81d60098a6150881c84c8170380404444002d101c0340798105101c0b200c404059951500300c0d401c1c5a148580c0107014090075000780907400041000c52800720008400f42c0100d400c820441c0110040e68808020130070a5134000e0301d607581c3c0c64065a02c0d00d20203004694010740b504124020030b2a001011465401c04035030001e4081c00e1804a101e807030b1030306000030320810007005000d940c1c0c448402d031080200800780d8440c0425800800444c0407805030005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 830292077 1250 830290827 830290847
    0x80a0c1409010504180605150f101d010c1514060a0e180a05060a140a050403020d0806041b090302091305030301060e011709030a08100810020717030106120b01 70
    0x60001ca94030300400141c14180c2c00511003040d20541024a0512580ca207010754806481c20185c050300c1581d1000310f03203003850101070000301c11a080d114102907603202a0402440104030000e00c2581540d2007401e07406480c80340e91440d80080c1200e410105440703603600410300030320030703000130b501141c005165420710a8080c03040d0745c0c44040c9410f540e662083c003040b00300c00d09040c040d154007079182c0041c0094001c0000c580035412051000c11090300364500d004c8000e00c0203111a150724144010700001c80e40110340d10309410028034052110342c4d10306002c14060542024420071014005190703a103010341c00760001d015a8400c84e240710f020b85880051911809003082d014002d80c10400c01003100b94014103210701811f40606010305580e4203520301c55420a011a90100f058100040c19a030b0607601c6003404e035100700c034206c00c4800141020807003640c40500e142495000ba0740001c024003070200c0380c5220403030340c08003c580301d42d6903848150040040e005100c01071101c906200c1036500325030140300005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 830293327 1250 830292077 830292079
    0x60c25060f050f0118020c01020906070804061d0a15090807261b0d1a070302180d1e05010f1104060f020105010803160f050a0803070e0a140d08040807080a0c14 70
    0x904685022175140001e60103480030729115982000905169100c01d00a400458050500c2ca0707122841c2010240070300c901e07417031015240f4001d03c0e03003550940c2e1910108070540b12840300048171084180e600b031701c0300025500014041c2c412100300003050032130719086102040c860b210240100b02e80034921562a843c258020340320301e804c1010b031869428882e20400c141c81c010321100030f841c00440d000201001065903040700090300010b82031802400003414044482d02a108400c0c680801d86805070141e80c5400720340c011031030844000f01400402d40055855030440c0c1070400003422041c2c102022a8000d100381408a00149011040c050061141504861625001d1803600f030b8004402d10306600b10700c20480c0c50301074501d844030104004014020751603100300c8040d65641001c0c880608200450300c4d401c2d11940d0a04800c0c411240704c2405250b000d00c042d18012446080d600d07000030702e40110740000d50244510340d00001d07825000070f2184401fa02a002551300c0c640c5030895204400350b410005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 830294577 1250 830293327 830293349
    0x902030a15200711013501061701140310060e0f0601020615220906141315051e070c0201031a010e0f06040503070b0304140609060c25060f050f01 64
    0x640c0101d09241d05410420303805140c01105d800c09240440300f07800c0300040300b80304481051b641c441d04e0340503540c1d0140906620305081610b58044401a485450140298801d000c1100b1014103070345c408000103400740d49140c4042c0402904d415076010741807000c03201e070003901c03c0c8503011410550010540074012012090702000b01200f260a00922114500741c14000e401c0f00c0703c404010700c80e2032003140a502c0c414a000b1810309504080c00c00003d001800903c0905030096004001481c107900301c2004080710440405c1651751141e08151461400d805001d8040d400e40c01c010310300d64020044008180b007600c0400804501208640c10803e147c01d02c00d0100c2e00c00d4012000c83d14000f0446a05010018207180c5040d450300080f07810f1091580c094041100048180410803003240075401e41c0d2400e00c0c0051010303151071100720341d07035030009000304101400c00038118404c4412541241142090012035a00508040c40e01000034081e0214103101c4c289000c0110305a951401b1840e030495010030b1003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 830295827 1250 830294577 830294587
    0x10b120c041d1908070209160e06041d1b04084218010e011e0513031103041517070908070611010b1201060810021c0f0902030a1520 58
    0xe40e07440305070f00350161414042488441c0050340c0c0c480042d8490890342e000004c0050707034090301612050010000c1840380c0803d0100780101c101d0b0341c1520011a480c02000c000944032804414032034200d050a14621410000b00402c208100207605056500e00002d181c0080f0031281410008080c8503904070768121201520740c804096520030690090210311500462001c800d00c5203084452820718600316075141c20705c824800700d4030300f20082515030703640303040c001880d0180c207110842041075002001c0c0809a507050181000410944010340800c448a41c40f0103000400036145019160400191280c5140050490340c1700b04000421505400c0042c03400394104070041e1803001020b87c42000565071100383c034505030390b590340000c980c0684c1c00c000100c9900301002d00b410650101e543e0990540100b09201c00d0728005c03204e0107034814110f100000c400d100c0c140040080d264100d000b03545449149807040500c0112168403820290711b03103041204410a0442c20240e10b101548c1940920302849 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 830297077 1250 830295827 830295853
    0x120917030612010603030305070e010801030c09020f0706020307170105030307050c060c01020d1b08070f0905040c0c08030708101a07080307020c09090105071206230102010b120c041d 80
    0x8051070300554002e1241028502c01c80d1000d0840d04035900540c0000d4032032081c01802c541050351400c00d00340a00c0e0105066042d03031100311181c0d003940303d9564910750014000303d002e00950203940030301c0d500943c25136581c2400d0a0051541030340c000c600390300b01002000041c091900004540c10a47e02501408041c4402c0c8100101600550244107a0395020040c200040949100d140070904070b0b244482c802e1003004000400600d0010006000e0100780340c034012285820042d003800700d48040354046807040704140102d900d2452a54028080c2901000703104100341c100c44510300c61301030741d4600400c007070340e07840c01c0c017901c40e4080c050a03c4090208001c0c008581000000c40e401aa00d00464060000749000708050034001c45103103509035940c4003030080507540401c041303101c07651014042c000700c1d0418080707103004100e82d040180100850000b00b14946d00030f401500420b0001000c100e40c0c01c035601225522107000c040d68078440c916100c904941c00b40c40c8a00d599244800f6801000401d03401c3c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 830298327 1250 830297077 830297123
    0xf0a0e13022d0d06030501061d090601140d0b01060305160203090a141c08072f01200303010b040317071a0a0e190b161d2407031209 58
    0xe008800c4802c108940142c11415000d101e006602c10000000c06600c3c00e19880d07000c4070b10903428108120090140709413084006111070544882c100301d850350040290010703414800a4000400601305500001441e94040d408a0301c501c0390003007000c12105190f041280c40e03100700ca610b99030201117800c042c0070501442d08041c24151011b0403500b6070804d550380720340342201001d5003103d400130009401c0007005646c10310011140344040d441c409a18070003480d90811180328811034100020500e0495414603820554880078010b03c060b240c0d0303961654000e40b0b080d8014041611004108101165038131030a10465041c3c503000581c40c440480b0b20b5001005001c0d0203090740440603201c041d040101d66040c00084001c1981d01070046250380c41c0d142a10b0300c0a8010704a042403400011140e8003a0b801c2008400e00041640d40048007031082030000f0745051151840352203c42d140503601e247d0724008002014082d0080d10303400310851540300188151015400e004020307800c0080000d00c402044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 830299577 1250 830298327 830298397
    0x17010c0801060e180109200405060f0d1803020f0d090b030a0c111f050f09060408160c0e0103170408030a180b0c07060e06091f050f0a0e1302 62
    0x21304203000290503018100c80e200084e08a208140d40e1546003440c1c3c030040001684882d0381d0b5400b420b003040e103400c0c0010482e00590f84109500000024039003611841d680c080300840c1d91099042e601c00c0d04904009564240b4100b04501034840e0403115405107000b026503008681c502e441c400d1440d901e0844601c0070701420901d0200b880341c4140440e030452014411450755030135941d0348403a1721869454240580e5405080000610118010300c003a030400400d480303620507000552103a544507807000e0014056841e02d80a00700343c0c0307203000c08924464a0f02e607050480307008818482809850b219158814469842000010b62040282011840c05041a0300305e0b00c40c998504440c140d40d54000c00029804010305540c80d410408052008982200c010070080700700b030f180c00e07040c02801c5020070391022003d01c90303503841d43c0480380c01c108642c89402191108000c0048c0c840d00d5900c034142c00342219411101040c451039240c451488401080d101b540d107100741205501020344080d4808924214007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 830300827 1250 830299577 830299579
    0x13020a0308070221010905210901080c0c0d0e030606100f030e1c031d0c01050d27030c03090e0609070e010e030706020f070f050303030403050a0c020405010f17010c0801060e 76
    0x1908609001d0911483c2c132003802c01d4101002080019085c50f01500b000b404001035501c04001c40450031003080303083c068811b94482824201c41d01c2e1515980e0050b2809a9999207409104920b44801c04607801000b0b25001141a01200c5103500d07204104454443c007180d4000c0003034041c130f000c20080c5202c0d070040103400d400d000507242243c0300032003000e1076070000d01c04c554046038561010b00703002d001c0c400b00c080f909044040a001c1280c010300008000303200c2c5000031800f058903007415081c1d020f58820301d40713113840c00ba910703072060302000d881c01130981510303440700f0342c003103140a80b0000e9010782a003050341c0b003024014107404450795000d0054030f00507a09503820b4108400c1d0500c15400380c40801220000d40301a80003800f8480b84441c0d0035103040c1c0d0780d400604421a0102081100ba1400400c0d20381080e403606010761a4103010104640b010b506040180d8418108800012102d04900c0c0000035034040184a045070b500c000201ca082c0d0304d030803410100250996004020681c810146203080e008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 830302077 1250 830300827 830300839
    0x60e0105060c0a0332091306081e030d0603030c1a0c0a1d0a0608090d0c020d110d0c1202090708041109060a0e0a0b03010501060c0b0601140702041b020613020a03080702 74
    0x16411034401e001c1000c50740104404000041c40046c545071036040858400a198005d01602d0b04011030749494070014017000c00b50010001e40368002c09000e0042d1382e40e2042204080100585da81001070007600500b10a803200d400c0513001d002091019044148550300414190746080c07480841140c1c0c600840c07040f13250b030f0b500c9100056415a00c0c04d07801c200406650340c2e2501641824100b05081403c1c0782c10700400d00c0059048040140c440210303a142d035079008072071025052610404214101c0280380004d001b2002003401290b41c3d0307212480c04010074020b60750f00301250340700d00b0141d640507001c0d074001d019004030304000b64683c40c045001c154414005043c50412950301c2c0301000248030150b624070586502d030303814810142024420903005040b83d180c6501c24241d244c5802405800c0a015075040000c40e8102c140c0c500005011a10704540c00303402040642d01007202c000450740700040304c000600842000c00c0000041000810003250000c0085103000e295075105c00180e40f02c08000c0382c01c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 830303327 1250 830302077 830302127
    0x4140d08030f24030a02120c030a0302030703020d080132041508010b010e0a061b1a060405151e12030412030f05040f0b0a14040603060e0105060c0a03 66
    0x1501903805907000b100c0d103856038485030a082c2d40d070f10366401040a42c1c1800550141da1186580d4002070300b1a0f43c86e4042d1040031a1a0036000d03024100042090010f070148030304804001016400001483e050b8002da00381c80404140c0b0700c0480e0018030030f104803105e80c0145110a008100b410b1800f15000d506500c40395626107141010078203652a00940c4c0320039181c01c10003048451420b004c1c64144036405d19282c0c0d000068840054030404032030080c0303410428031098142c50307a01c002103e803400075040b807201001c082c440383c4042c00011044030041d000714203140218182500d90440070300440b0740240180c15030340e80301e80c0d07441d681e00002c01030642c0002010003911017402c040c00200050890f401072541c0c900920b0402030203e19804401800700720042108100a440038481201900e80c000805543c07045040b0044950001c007101c0c003454548000303000035450740c05901180466203603003c0488076a0b600c804100b440e02412080d84101e40188040d0f0700004c0c440c03e00040000100b4810744124 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 830304577 1250 830303327 830303333
    0x7031d070b070501050610392001030606051605030403020a03060606110a02060904090f06050a020a020d0e063906190c231b010501030615060504140d 66
    0xc500594028441c10708002160710034080c0a000350740c1e00903410381d04e50350000d10f000c0c0c0c0240b203260421808040718040a0308009080c0304400c1c2910441c01c2c01e507854a00262508200b0b40001440c0056401313110b400c00540301c5540a402000100c0f40c0944402d0b0400b411900c00b0b8404481c48501100e090004100100041c0e039059800c10245006402c005891801d02c0400340c440d0403903030403c1c00307541e00c00389510005a44080450300c540074180c40c045091603481c41e2826105841000081500d4141000c0000c50109980500402002a4201d43c000400e001d0140c43d400a00e01c101d03600003004000903400341e102200290354022a15100c080f885105200212804504641c0807a440e0450b405003e000489103000d484044d011200c200030100390300070080c1c0000c81c900c081e01ca003040551b1a14610141010540303400608145000c04d843e1590081c0701d009000034000ac580031864100c441051740e40b505202d02c10f070741d40c0380c48007480d1504092940510b9a4840541c2e0f40c0020902036000c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 830305827 1250 830304577 830304583
    0x30d1409030f010905011503150f0e010905010509070512030301090510150c05070e010e070e12100905060a0c090e22060207020a0504020f040603050a0b03060f01150203040e07031d 79
    0x2c04000242a1070145006425141074100920259140030342c1030012680240e010003000c210f150300020082c020b502800090320803a54030003c40e503c3c1144003818800190030840c440c0701281e060300c10040c3c450b030400c1107940200e038040726aa48140014400940c01e07501c400d4001c1c5a085104460942d504442e04c9050420500d07040090041b807101320030003408002c0c120190291141c00041581800c0f14190b0341000204000100580140300039019160b041e4981d80e448209002e4418041000403644040c010340c4e8804c442138840da4000900701007941c850707a8451080c40e520820401e183c03030003940000d1005048002c00d0404101c1031000c1c6c4801c8851040442e104041c0036031101c081e030040004021543c0d00a90060b03004103c1a006002e000085900341d0b00c4504000500b0780700c0315942401411001074041e0184609024082403210100400e41241d401e0344d07021024100d180f50880c0ca0f406a031290b01400303844040884c0949000340c20583c0e003000f940c030090941144103281645 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 830307077 1250 830305827 830305843
    0xf1718031c180807020d030311030108010e070b09090610090806070e090a140a020a03020f04141207030c0b0703120c0905030c0105090d0209040f06060b1201060c02030d140903 77
    0x30404103181c038001070740103040c0100e080c80c100586101c03404003007a454000c490304c00d82100910a19258018008040c02503000390443c031040a0029200d6071101a0b1500130006031882150a1083ca400022101d103550101c2c0c00b01c550141020b11035132201020b0141e60170728010482c05000708070b40040b03a8020f0411015100d843e181e550f2440b0401e01400340011820081c040d4500b86041c41e00c10b411909104c411039400c100c00c46c8005036a500f41c0e04086009000c0c440d40c1200100d0000390000380d154075001d11421402080321903581c44801000d1480c0d551140d03100042c02d500c9a03280411140300d10764040c100311406810102c610107034501c0080216071800c07600001007140345000380300320f00701005010105003080c00d04515062001e000106c110301195002842200e4280000e000c100ca419172960384e0030b900c00401d102117901c41c3e4852299400c042021400086138000008005218501014489030041c1c040c4c0980507070420122201c071250990109100020090516161005c0125070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 830308327 1250 830307077 830307097
    0x8120403050d0e0304060e010c0f03050a0201020717070b0c041d04030c05190507053312090309150f0a0e0402131202090711030d020d1e0b100f171803 66
    0x43e1740721b040100c040c201510300c1c220030f8100702a0681400c0003400c041284010141c0500308540c484d6030308074080f400391042d00c00c000c00203500e103403c0103040307118000a440703400d118800100244c0d4030707001410200d000d6171103080644c403070b050b468140704c0c1c0d0f4140e0100d8000b8040d00d410381081219861705450450750283c0c54030b4200f108210f00041c06400d00140c40a0202240c07980c0c2000c004102e08441003014101c1ea480d440301d80c01040002881c5d4500b1651038039002c1076001d00629042c0e81280e142e8000100050042c0d050107240109000040c04071440c01c041280040d00f040c2c3d5407402112100c43c42c400c0290400e07420011102825280402d060041054900400c5c05605603c14401c0e07142000c1c000700d0a1104034401160365140110035600c0f0b00f804050010b07103581c46108480007910102100c0d2000b50b00070f800594407040075030000c0c0b40c1d80809640d0201c005885440840741c0036016845a000101191150742c40c40c600080b541c1d4102c0a81481040480200c2c5901419a40100c42d02 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 830309577 1250 830308327 830308333
    0x40204050a0320030c060921070b13080c010804060924061802120112081c0e010e0c0a060302090d05030301090b011b020102100e0f0105040c06140708120403050d0e 72
    0x509411000109500040401035020780107000034900480c0890147c1e56804d4428408192801d08200580c840c074141000c140b8116000b07182d4488500886510404481559032203500c0d01151180c0d0001c0c17034505801042e950311003076079160345564008104462007100d130000c0322402c5112201289000c4840070031070304000140f941c50003a4a003248603290700d52040042c010f0182d01808603048034041e04480403c000c091141c0003030718100034a842214601e0348141c0f03000e00b556800003101e5000400002820000300491510088080e5460203c105065401041600140320162190300a00b90554000c0e1401c001d8044941d2031a086400c01d820981c02c1541c0c0313071620f11503980e0056504004c10490403070b003503540c80c050b00000c2d240e81d9a060340e501815101d10ba400b4a005003000110f8400c06d001d03008010604092825100002503481030100103122440386070f041280e82001c4481c125030114000f89051010034260140505c010420340c140881400049140c12641c020422641209809 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 830310827 1250 830309577 830309603
    0x603111b030901120509030405010c050a1203091502071101050901020f1507090b0301030302060408031801090308190e0601140406030f060623010203122d04061b0c11040204050a03 79
    0x18001001403904c50049410070041c41800c0b403000c400c84054810a11781004440d8032420030900e0f05641101c0101000c0c010481e00d1800c40c3c1c90b601010b4440d10598504001c5000344402c203040e4001c4980191032103096481600c6950300440060581450600594001142c04407940e03080a14041e0f40c000b40c10748110401180b10b60000c030305006400d850039007604550450300c00940d0780000034002000d0030000004581400b401d40307101c190345801c0000030710031a101c9280082441d00191b403016000c00070322414100c000e00324003490101c2d402d010000c00c2140e00c1c2c48281c0041081e495505134203d5500d117070103c00b0812104000030018055040400d01e1890b0007105140916220446680307089116200503603681d0200481d070106c8140c4040c08929100c00c0c84002d00003a040c1207020304840c0608501310b40301a44400e4a1103280201401c000c0f44511000c1d03001c6e044940b014800c00549940304840c0050800c0300403070f40050317000c0c2c401820592038401140408131183c00c1515800700e03001e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 830312077 1250 830310827 830310829
    0x1e0e0d2a08040503120c030706020304060212070e0103051006020a300206011701142404020c0f010605030a0f12090f06120f09030905061e0318060c0c070603111b0309 73
    0x8400041200d81505c0345141c45030700800c03240c80f4000c820b0024640c0d40c0003c003082c01d103d8183c045d544020b44071140c604017410a1075001d001c0078036540e10240440c0c03c020000b40318080264080c02120615006090181d006950366242c1704089086000b1040040200750005e0307404141d802030340c0d04241c0040240f5410448002000300c03240400444681c140a000f00100044044440d008115110810311002d05418540e45c40d1242003030554020303101140c107010b10200040c0f0700c0a00505080200109a107490502d030302c840c26500c0181c1500461300c840c0c00000d481c3d0040340c00c6031002d0f141c08540542c56101a0042c4002d950040380090f500311440c10b51203549104007000581c003540100108091543c01074004452846014881c805c0803941c3c3d5003001b00400705001501941594540e60710300012108074054140c1c0040e0824410100000c3c0c0010154080b01d030706054510040c030500d40341020850107044240d02010140c00144400d520700d10401c12810408491b5401075030303d0b80e064074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 830313327 1250 830312077 830312083
    0x91011030415090f080d0503190f0c0908030f0306010e030f060106050706060b030f01051017040c0e0106020f0318120d090305010e01020a0c0f0204021c1e0e0d2a08040503 75
    0x781241041140c0b030b0b40108290800014810050b840506101e51030f582c4035214111840b0040c25035903440ca0038607141c248031901d580d01c881c40be428140c84800700b058480365041e54902401580545900301007000c10b0107503000d030144080d4120010103c03040700400803105400c0c103d007a80940081040440c0c000300f085601d010b0800038225600c0c8640c15483c1c858050f084444040c452207000f02c81001600403460f00ca420181c1038003810000980140c1020700d040c1081090340d03c980b5140c200220300110300c0d90700c04100403070041d10700c800442c1450040120801000c4490110766845a21010580c00101e03040c80707180500f00031070310307014901455414182c0c203445d80b040c00c00340305034410880c0e0b11006030041c80c10200f481d000317031180001190b0307417010030024420800203000a07680201081d1034003110703411180c3d00c5250110704181c0c07030364a042c995094038000d9901c60203d1300852101c1210702d214281d0108050361205244102c80089850004010b281da50140c4440748006001d00c4141820 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 830314577 1250 830313327 830313329
    0x90204060320101d09311e050709020306031903020102030a0b01081e0901110f0a03060603181202210a08010e0c032403011508010c08060609101103041509 68
    0x4e0030000c09204140301c241010380e11340d058152042c041400420300c10418a81c4106140317140b803c031004c0ba00a10746111503540340846d401c661121481d1070724903011042201030000e15500500400703100b802c000b04c900194000418680d0181315a42291440241c183c1040314801d019400040e90390520020b804180c0e662040100d060044240a0014084001c50303407103d1a02841c104040544034080000d001d003003910181c0310300020100d00f4030362185500d00103200b00c0501d52010020035903074640c01e40607074010080c01247e61b440e440d02c00d000b240c0002e028881c09450740c815030b54040264a0107068404013108555080e000210303096081980100c45c15002d03010040e0a800a864059299921440002e01320300051800d81d01c0c5000400c0324000d104540c0400800071720034a685030024010304c070503520400c81c081d800c0400701140075014048860140c88094580703840d00300368409021846403010a10400c000f00c0c10341c0e103424004180050310244c140400100b0007520480801414000f60b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 830315827 1250 830314577 830314609
    0x903100c12050601021906060509010e010510080907050f2d0f01050c0d0e0d05030703021b0f0a1e03060207060c0e011d0d08040305010e0f0d020718090204060320 71
    0xd03002c144007190b03800003000c4159094844c2c0b1608040181d143c004040c090a42c4156081123810002181600030600440e0503240c06603800300c8401980c6c00f044540d12810317100e04035680c001400a125a0901c9a407040000780e002c0c0480200440b04240e200603040610410312003119a4641d484140c58030007504000384809107401414030402408a50b26003120050003002d0100f103100f0300b040da85580800030341c12034018041c2c83c2c44040a0402030340f01d6094116966186c8c034030611000852500c5100c6c2c8003003d4003c0d001540590414200c0388002000d800414211050f00c4000800103031140010071420f482100c0110340b1340013420000d4400c010401126040c4401c5d85a40356070501050038244142c43c0803111050441c03580e0400141310700c10754201401329401c0200e4000039050008441010340003400032a808070651900498440c2214041c07080021060b1901c00c03805811500034500c84c0340002d10004039035035696140c03c007200640100002415862034140c05904e0001d6051143d03581c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 830317077 1250 830315827 830315831
    0x200a0906080c09041a0903070605160503040311010b0307080102190905011d3d02030408030406030e0f030a1e0314010e04030309080d1d071d0405030903100c12 70
    0x1c10410003946641c581c01d0000c3c0264010000681444a483e141000801245d0703100302d003905007200a29120781c8540c1e001e603901c030b061101085083c1c5000002c0710a08440756100c07400c1d900c440c0c1c0d044a015003c891105459034079140510541c0e5005d10580c0024400907000596480241001000300c940f20b034486414003c145400300010f036084100100206924110240001848400a50f04d00e451400b007910f49040c1200d40c2e2807088045070200c401802d81078000078100b1098000f280d4074842c40c062958280c00c288002c0100078041d40202d62a180d058043d110400c04034084e461031074120340504400100c0b81e0003407812042801a502c2800c0400b8a424407400411040d40e1103484410310440c480f205100700010240351103641304450700350303001d10b00700d90386c003d24490600a0b210b00c13200481000c40c900040f4148400000b02d86080f01c21018003107110104410f03402e0314038180204180c031640010030855030299000c7c84080020319840600040c04102031702c000300181c0042c0c40606001d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 830318327 1250 830317077 830317079
    0x40302041b02030f0c0304120602090f0a05130b011e03140f07020307080903030702040f0b0a210f020307090203070519020102070506010b091203041206050702030a0c020906010309200a0906 83
    0xa50203c100c840030b211840c94140c0d148010403002c0c3c6940b0855110201d00c200b6424081b042010030340061144250803600d03445084070001c10480200020311405600403151031000c5a6000305402030301c0b651005041100e0300258000c01d41c0d01d4074540c0c070b1402000075907030041c803e42c4403252413004d030b0003402002d035942175840c25000195980c401c12801030450708002c41e51000c00c0e40c0c1002201d14060b8050700600208502403110700107018103e880c140700e0154401c000c00c00e4002c114075444051120208000c850031592600a000300280708281e0700350107103401c013140d022a54001036006140f13980c0e074583c0c0d40790104140e040b522823100380c2d08216401041004c012660000e0040c3c1540d010112040c1c1c0c07000483c2c0040c64040f0b40320513428013170001007400205402248000f206d0070303014580c1482a980c03070480c200c0c0c0321710a060800c3c010651560f5030101600706041031581c40301040c1800910380d41030341c0b03d030001d42c5c20305004030076098820080740c803060a004c1c0c0305100904010905210003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 830319577 1250 830318327 830318381
    0x60c030509060709291602030118110f0a0506120103110a03021011010e010c0c05060114030d0e1c111504060e04020304060615080708060904032a0b0c04030204 70
    0x4900300e01c200700340c07110081c17a410041d440e0031400d01d002e02001c1d80041e5981400c00002503041d0b40850b4264840c3d403800b07400000411515032180074443d4458080341c918200142041201c601100c0e5943d00075122042c003007002d4441000038548461000d42a060640c5185020700f0700031000301c810390003101240c1c000c00040c1c0310700122545040c140e080820200c4080340380c0070700400c0340c10307802c038515801e2400c279644c2190000d4000030301391302a40560310181c2c2c8554074100e11081039070300c0e0f0760943d120782230181500d8400c5c41030400c0e41000402c9000c03000d85080500ba04529500019110405051a15040d501e0140c403c00c1003002c0f014810382c1842d217801000f070504641d2800150041c0c1d0000009401c01c101c0c2d901c00409040f00102400c4140e2044000400003903040b110080490310355808625a480e204032068403903985540c0b1151601c0c0118218412603003083d007460010b400c0d00403654000b440340b0056901c905050040c0b01d445502d10b0041205441010201c01c605041c0c08255041c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 830320827 1250 830319577 830319587
    0xc050105130f0210031b051c0b03030405090a06091b1d130b0d06020d0b0909070e0a090f05120d1802030c0d0212010c0203090a05041406090c070b0103060c0305090607 73
    0xd43c0485071014656400001540540058280350500c3c0c400e0064004040d40c001c00a012512100c4803c032104c0d4a150075054125008140400e606034000d22040265241400714950301000202c4c0c04903102e5540d8528005880c404124141e14070501848008201e5001d0050580380c00902c0d0340420000700c0402140c1401d0701d6071032012449442d0f5020706040e8072000d944500c410341c050021580c2d5900401000006c00a90014a00c0f5503800c4001c50b03030300c02c070005510040d212141c4002d0400c1d1109507008004110804040702d000c60b503076803940c0c0860018003a20305501110348209984a040740e8005049450802d00820340f002e05080345c10242e200000d07680d030251010350740328089403451f0000440765540a14405403e60a00007101c00183d4084007030082c51209a8082c642d00d6101c008000507511051803030103046503c030000620f14500b03000e010783c0000305044140d02d0094980c58085800c10260410740741c5a48940c1100c590700d6251061682c4003102d0005425903082803840181 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 830322077 1250 830320827 830320853
    0x120501020a080609250c1506030605180d0e13140f180604060209040e06010602070302010e0d1104051506040801050f010f0506030703020a0302040504140601030e1c12090f030c05010513 81
    0x190541803a089a0041760051152003c4182c0201050a03040d41c00d448440c06040d142c00704903401d60600340480c01140040909400c0105030070080c01c2240381118040352a804203a00742e545c081d9041c407100309001794610a901d8008038102c8880d86501e0001d840701d402e00c0e405401e14800c5c010700154840040720201e28550020340c441405a03503200c0c2140001d025220ba4040c2d140c05001308000040d2060b0002040d5089910031b0700c0d481b1120000800b0400c00c40da612001500c030703540f80302100d05e1f80d10b400d50050b9417040f1696411080307038403803901041980d000b54200840c1695076600784000c69005040e00380c018045d2500180c1218202000705078035010140c0014141600820b071110018025019600903000c050010054000d01501800c0c0002054035020301003440c000d214011110041820480500c03c02c41c50fa4042811150031104a03804440142505030744040c824001050040003c50050081d5101c0c1d0340c213111130800ba821605c0260a140501039a240807100090000c400d0031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 830323327 1250 830322077 830322121
    0x705030c0f06091f0210050c121305030a09170d05040e0a0e010c0e041a010905010c05100216120503040506040b040807120f020705030c0a0b030907120501020a080609 73
    0x200702007040424103d010b00d05038a0391002130543d0030b04c20001c03002c1c0120500140c2e0360071201200d0502407084215102604c140002440812044086145044510760441080c11240708005044d0319500d00751342240380702d100040e840380d004000700d1640e020040784012004014007440c6058101c041c3c0303c0e105030b100341c07a56003520200090200d003440d88108510840d01000f400f040c4a1850300170000314526074868030640ca00036640d07801090100424201c440181c480400b41e0741000015100c002040004071110301c1401a020342c828901d0018248008040a4101c1ca44c00c05160030007d2511900b91724080000500c20070001c260000313803054100c0c0c2c100c01c85c9885a00c590400a800c1d00c10700380d0161000d0268089914203176404400c07030043c0c41c115420750784141d031510200354407103081a1555500c9038264806001c092104401150450000400c9540d8a0b9585041c40c01e04070300207400b6100c0da580420b00d07081d0950401d84036940508200c1d81d0107441d10345506980043d0044400017 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 830324577 1250 830323327 830323339
    0x5060414030a050d020d0822110f030f16060c1e03140304050c09010522050c090a0e06100f120f110f1801020105160e15031f06020705030c 61
    0x310880e14280000488242c00a040d1900700b000301038003955982c1d840314003100141341f03d000036004c0142c0440b0396000d2664841003011b0468652142411502c03000491940401d1000035520b00ba0380c200001d21400f808400070f400036219a8642402ca441f0795400307002400007020b41030000030402076141500b15491000702401c10358074101105e5071517402c0c580174090300002007030200f40000018948142c1c0c03412a201036090b0b803600144001d9002980e2076614030094460f840c40b03408141d801c0b0750782c070088540d042410240f0785e80001d1105032183c1d1140004403007030001d01c106410f0a80034510006c0903411300c40d031f00927507103203006020b41a090070415030603650303c0702c04c090724203150803158180c00c0c01d000868480351708544007401c50f0b000c6e4807120b0f0045001c0400000d45d5006002c1c19101e1003181406078510f1850b203034240d8034020012035240e4004480010031905502204c007560248901050004400400d0b00103003a0490740c5d600950255403242604001c0c641c0c000a0701d8680c510300b9550 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 830325827 1250 830324577 830324609
    0xb010c060c0e040603051f0e03092101061d06010201021312020d1515080106030803010e090f0102030406052205060c07061d0c0310050f040f030e0907020313080304050604 75
    0x80362580c1c911050203600c04c0c01c0600000c14400000350700c842200722491080300364802519590211000c000c05200700307800510002102e8075151030400e081c41d002201118541c5114100c2c85e00f1111030b03800c0601d183c814ac1c0c4254102e488210106a03112400380000c40c540f900040701d0207480600b07486400121442082c150045440c0d5040750f03000c855000081444d01d0104c1c903040c20241414000e549010481c1e0000001d202405000d054200c0760071a0207185544d0800007124400c041c01404041c8900c0340c2040e14040e0a002d00c000d61056025490001e540d0800d50300c1e401741c94032940f50092513070750362000002c0070031804070b101038000c900b10b500140c0d5210503260090150120766601c03544a1a27009020001e2040400c41c3e000b1484124144c40307092282002280450360203440c4503a02a05010000d000110510f03010304460b030003801d000307480d0b00090001422401d0100d1304074006030070219480007900411018480a8010200a542024288404102039024600c50943c000c60000c00b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 830327077 1250 830325827 830325851
    0x140103060c021e07140d0b070315120309181506050307090e0f0108210d021e0a0917010e03160c120501020408060c0c0a0303050615040915090b010c06 66
    0xc0040c19084028407030b1403903010303041c3c02c54448400c0c0c03003800300c0d1866542e000940ba203411103864450f1a440031406010352166642100200310410046030003004041d0b0105d0603080c2c505141942e24030960300d1401c002d0410002a4080d8140d0f0380d0500102e007407a012826820200d11a1002d0321050318146489540300c503803ca966180c80d47c00203540203040418464180380310802281603030310040c221822490401d40340b80c04000140f4460000400600086410405c1d43e001000f02c109802031100100c0c254502140d501d0b4040e02144010584101c000c0016000d60000d5298038035103034000300110034640101a4480c0f0900b4915800111078400c82c41c01c20180c031002130043d02d0b8044204c0c811700d0807840c02c68000c0d8043e008001d420310501c070004858a105204980035201e4030b0018101000603035805401900c4050586030340f02000070040c03e4083d40b0308000d000142000786000c181140440760120010303415400c2403455034107002c44403245076041020002c00540c40707013001030345401c221 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 830328327 1250 830327077 830327083
    0x406050604020d090501050a05070207210615080a050d020f03090f0402040f081b041a04020304170a0903060e03070308061302071506050f0f031b010507060f1e140103060c02 76
    0x2152014a403451305030380e02c0c2409015809079205000c86001005942c4a1041c1666503110314403510041c98000c0c06200303100d402100711094040e20448000c0b03440455400c10807668241c2c0d0700548030785c1c1c1c05a807508044c01070030800d590080300540044c012210480c240c142c1c9074030545d44a540104080d00d1491400d4a0310380c1158000c02403c0350940000380c035050300300e4030303460148540303255044900c188019501e420b01c1111a805500c144040c61101c03c0b40c1800041d400003030040d100300761490b0b000ba0030a01002c00901701e104e2142d80b1081468218600344041720150607500000360302c203001d031b1800250003201072604014101c03002c5003003c4028004c0ca01920807260000c0003540301000400811500d030300010141c81086030000d000c2c0200c0b00c1403110841103014080c2e85a44641c4420810080c01401401d6425040c0f6180c5d2030b0041ca42c440c0c00139942075200000b0070560b1099045000052114505600c0c280c00b142405590282556071040d60418007025150981c0c0300000a9018020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 830329577 1250 830328327 830328337
    0x916030b01270504060507080f07091203051303150e190618050106090f0b10021002181203190212040b0f1b0708190b1b041e0503070b12040605060402 66
    0x618802d21107072a06140401c0035040545a81011a923068040784500a104413068440d0041781d07201000145818068010030250407800da00780002002074500501031038491002130345c01800c0b10701c00d0100b01b00030001242e4010700103000c1900414035404440c1e40310105c0710741640d0004404130b50016050398840b03212b005030300020410b40c40d00360300051a500c1500509200700aa40c02040764803e90828403509108846660300144c100b050320410000c071683c0a451071044502c0c1402c0e041030000040b035a05655807841095170760020480c0680180080c850b41c144011343e01c050000d0890340902180640154001c04100d00b0010656030344d0f8069042c2540d490740360f03404001d0b07000603440c4212034a5626038054050217000391900d0750100c00011911420b05a40000681e009685100036003400740750440c1803c03c0b001382088009122a9960922300c0040d2184540300032192401041514000d1541e11501024070b0174809400c1e8911b511884642c015040200803a0036075481e00094024491 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 830330827 1250 830329577 830329649
    0x1812090103020f031003111516062d0606090b0f0a0513180c0503010609030f0f1209061d1e010c020a0f180203061f0e03010507080916030b01 62
    0x441009410f660985004007101c1c0606601c2c07485001c1d200501c030003408c81c000d8800070380c3c1041150540601e1107240c5100e41600441001482d080842c540348a05c40c121805228600303002044c15808004038400c1e00000c0038503042003601c40d031600c8240c520780d0141e04400c0a00b9a4085000b0030103500400890b0145082c1c1c5001c1100a0b442d240d413240c12030002c100c01c00d4094500301485c110300c1d0180049905841042e10b80905240c550f03640c0401c6030128900850700792440e0b0203260002078000c002101100700c142c440002c668241003009149030f40c2c0d503890724121456902c0c20780d070940718a000c4a1a00d07001f80f1241014040f107000580741c10514600094001102d401c00140500c42a90030000f13a8041402c100842107031014007000740d0105860881e440041c5814a02c40001500041f5540814904115007441d12580001c0d007140e200f15040004550aa0204050104188105020003101c51035181046003585c45842c2c2e0000140100c5550543c841482d007020300e21f07840002c1d05560 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 830332077 1250 830330827 830330857
    0x6050406270302210d050301033c05030403051209120a020f060a02011b02030c010e03040803040e060a030812060f0d1a070e120c0f12190201120f090b181209010302 72
    0x620b80390001c042d031f44244420384404030250a01200307000550b442c2c4800745103005400b510f01c0001c1c00c800d219025070100490f00c505c0200030000020748140030550040c4620b100030350701ca080340300500070294400e074440d40242c1c00c82c00c00030f00141d44101e51003614000c00c0d9401500c03480e102105030b00416014000649040d803540e030214240364008010315003003030402e000b80310f0100030107100795a0f03001c1c0380100030b82da4006100910060f82c8240040703502000081c04c4540782680c136212840343e80d008141e8485030b103d154040141d82d0400030800c0e1a841000d80b0840d26a14098a69502031501c1020000310380842c0804600060301c14882c00d21081001040d00d24035072040c0b20700c950744030800d40306203004a2021031240040c0c540203c105083c400000d002d01100303003d002c1940850025054124144803802000a00702107261144000c03541c131602c80010194030078203003e07141c040010700c000204c940301d1010311514100455090364900000c0881503d41ca0304200503000b80c00b0311300c11101100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 830333327 1250 830332077 830332093
    0x503100b0309011d0d140c1501080106050108010f0e0f060f1008041205030103080a0302090102100e06150901080a020603130b04030c1e0812090a08040605040627030221 74
    0x140c0107500189110130031016207060312900500e903649800c00300e00010082078032014075680c0001d0000c0200a0800c4000664200242e20f0000000e181c4003a0800945a95504c0c404d001558000543e140900050405541d02500d001a030058015004020500c207003600c802281e82c1c0e440f500c0c807907000900000c0140d0300710342c507490008068041c100d80c26281c87d40e9a4004401e041c1c0140d0840f4181c0381c0191600c0d1800c2c405030000d401039032055200c0d0741140b19405445903003054030700c40e0200178881403020700400d00300507108184501c00181081c0c401c7e210040108600c1d240050154015a810741d04c440d2603623582e982c00b01408207120303400b42c0500c41c2e11007044105607102e80e08441c85071003030400c0ca00c40f100389030544085841068004094401c200300c801c0c004281e4211259000100c0002c40b4012401907072012080e40140d4006800b00720085000d11000703805c0138010781041032101d1a207012040e45164520b030f00c1030782e21002c1d0040c10034000e00140c480a14800806851784c0b0011a8200307 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 830334577 1250 830333327 830333341
    0x10c0c0515090915030c061b0601060f03140c0d0c050403171e0702030705040515040c1e14040e060d051903081303020c0634020301060b07120503100b03 67
    0x203548030b000614482c1c0381400004845549021108550800140007400c2c1926010244401c5034001c4118450f080303000300c078503901d409003000098040c0841d42d441c40c02942409a0113003c0c1c07042106c400340030841410410070f03c80c095400392000d09170402004102e08034401da06560600c1070b40c0005e454584040e141048080c8542c00610600a0328140103841c03100d0b80884013698040c0303c00003545500048d104000070b1805400c00c80d0881c11403c0e10702c400718066000581100d0380789900c01c1c0454a0300103400760f080f1940161b480c1d602c02506017803001120460b4100c08920481c050002d0900044005c10a951203220001c0c520503400412a2035100c1980b098400c2000c2240e4101d0009118800041180554092605100358075400400c440d88800d020070509402a05825500d0405012001d840401003000c941c0c081002160486251032940189400d403815034111540280e0104080300000ba002c0300d660301c0d1021075107040c0741c49460755624101451110f40c0002b4080c0408000e011070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 830335827 1250 830334577 830334619
    0xc090c0c1603021207031703041707060902030c0a3f1412090609100e0d14060a06030302151308030901050709050a0501020d2001050c0a0906051206010c0c05 69
    0x59a0080b240c04131690380d9007142540d00c031810300004041e40401812804401c0380840915041881014900603d849080c54145190081c400983c2c00a840d00e5031802942000c2c0b044402680094504c00380e114101030444209400100222604000310014040d0050140749a001940703055130b411061800340d414911003901402c20b503140140114448180350070017410444140e60b6000d49040e0038404803408000c0d41040301c2c0f4200d414800300305494042543d0700784084403124030a1110080d07044411344958900341000b409504034500d40300007840401c2e000520a160300700044080d03080d503500c2100b19002980040d8000785010404000c1c8a80500c0642080c0c0c8a10315a554280301d4964940030481ca601b00d80c42440d000d60800303802c8000d558803510414a5400d1044100520f00d100c0034070301c0d804c5510031a580c8040590200303200c19020f41c000c040c3d0707004048a01e456070601982100c1c1001101c0094422414090b81d885d000e020050120414030040000601c8240c462001d4080c3d130300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 830337077 1250 830335827 830335829
    0x1608031021120e210a0308130c050904030e030102040f0e06030d0f0e0d050d0908101a0907120609020904150e0c0705330105120c090c0c16 61
    0x507545000d07400908219600001ca150701c81d0308040b00140d076507548481910180c0c0c01400e101e030410720b02001500881c0c41202c084501c09a00001445850701c80c1c107004240c000080c0004545c00401d02c03040c40411030316003855098510484480c0f10b0780d100d03481e050b00c6c00c04103a52038a4065002040015038829441c0b0550211034005034000707a903035612030030162502a452a1b807800704803038500d1101c1d00c501c04c12010340c003150047c208100740c0b0043d843d110719043c686504480051140c550070701051005106007940011100001e00c01071144601002c1c074094166815800b410505c400203814500c1034a584206040804081001d981c80300540d50280d440321078118096400e040e03000c02101840442034003202d8105241100c2510ac0c1d51000300158800c0c64142c0d003e109201c01140b07910007542c1d00309070091540312003241d0b00201d241d10300d440000c141e001511801c03080b114cc0d0355040300814030131340000048036214402d03543d01203594094012298490150705c0f501e40b410000c0d04400c00408 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 830338327 1250 830337077 830337089
    0xa03020a030807170a110f0d020315010503041203092405090d050c0304140a0503160608060603040b060d06061e0e0f09030f07110d0b04140303090c0616080310 70
    0x480140d80e4400e0940300704420812a443c003d50640016000d403400d40d108211000424482c0d51a180d41c00d01811f2040c1c10041910b0256036000040c0a208030111041c44640d07002800d25901f1485c25441d180d52000c540300d400c0341030640329001801004070301d0050141c0180040b2883c046c1180480041c00103042c200c400d04004e121344c500c1484c43c00e011300262034040c5a5003000b9860310303041c41021800707072803060401030304404641380211702a50103126003105541c04216803040c4510789280104000405017005004000800c1800089180ca003481e070749c090300075568118480841c2c90108020086540001c5145160700b080005a0046486501c03c444499600c080c80d5192a060703010200416514580300b03500410014121100e254054070700c0c140101101c0e03da0103e030002054100161100c21226030005004210801c0350712104541c080f202140110b0031031500c8071040e9620071031411401c0c82440c022a600307604a050317050510415500a0020380c590411044058441089000700 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 830339577 1250 830338327 830338337
    0xa020a02010605150a140c061f12020619200c090f09060112030c0804150219080315040f02040603020c07060806060735040801150b090418050a03020a03 67
    0x52245044415800300c1101c041d130440c03401d02481d00c04d641a012040c0a00b011150a125480000405000d514420402c800198940b00e511a001e81c410b00491781040b0081d1106009400c00758807140e05440340812503080740c00c1e200e81c1c2903005440b08450007a411000030f04818035036a10f4035002c241103020700c3c010354540345542c5503160200c140a000b00c4006040e0350092004100c0310607900c54104c117490080c14088903a00c1c1c07585409600f81d21030b801410244101101c550702071541040710751281c02e1140854116091240d03140c3c540342c4005401050505104c51802c4443d0340d40d0740c40b80502c00800c144c21036490340e480e01d000e0040d40007500d0384801030151541c001082c41c01643d08600c910002003920f403400c2219a525203c144150400130344204a4140c480c0040344c9a82c038428146001055498485107490030302ca00b595001e9005c100d01c2e03001c2c00c03170030000d0324003103c19910081c00880300465810210310010303904841000c030103001c2d8840c1d6400a0103041c3c000c241307845014029515 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 830340827 1250 830339577 830339579
    0x1b020d0e010509060304030309080d050a09020109080a05100e190f1106130905070509030d200d0509041d03040611061b03070f23030f062b02060702090a020a020106 72
    0x10b454500541d245590060340420000d00000e100b648500750b420f20940c2850304100680d0301e00b0b070841d8411a0028003255603140035405560300450140010000b40000300002e003010b0b514152180d02c5055403190207a225041142c1e04602404051f08141142780c1c0142e01400e94100048104011441030320706c03091140c00c02c00d5034200081160b240365401010302603454609011007000f8400100030320304100c001c1c07120f106660350610415061504a80c1c0c0e48101e0081c0b600a084004104428a00d5503405040207894941e0004142d034140c4904480005010000c03800c01d0012070080c003140080d41c08001000f1404c1a041440c482070301d04840e00302d4a00e5034600c00744c0c0c2d401c1c045c0300f04580c491920920015910611441941038400241e24260480040088203003c0da28000500305801c401c0110401c80c0d400500c400c0e881d4041310413180001100352101c917003017089a2080b84d1002075020a075100c07056458042c1211004c03075029120806903d4012102c10094004482e400015424808 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 830342077 1250 830340827 830340829
    0x110a06020d150f120609020411091305010812130b19120203040305070f02030c100f122706020f1908100506090d0302101a21061503011b020d0e 63
    0x10030039050396504400f1092090904c0300008180320780d610100c408039151701c101401a11240140079800500317110342c640720141e00003004250461685030356025841d00004112402001880d150300c3c2e0301c80380f5074070390703800814031403070052200c070741000c4105e03003001851025240401c0b030302c807001044a5982d081012522201172059101c1901c014001401c2032210001080003d54841802880203086500501021001c10a41e18000a1410210b400d5038103c021464000080b0842d00100130300412151001e500281c00201a9188032141001e0b000914802c2000035812038002000800c5900d0311503c24604002a0a110248020020700d403400803c03a405c0341c0000500c20782c4c01c02480d40382010003243c10b100710301355000303815811440b40005418a0b2061442020710110001440d0069180c071202880b0242128030748407180e020440c03001618400020500a42100340704180a24010880300001d0152541d101d40080703280315185800c03181600000c051601c009a5101d211808840d44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 830343327 1250 830342077 830342111
    0x46120210020601140f1c0b01050f04090c060f0203070b0c03040c060215070e032503210c060207020109171f02090d02060d1d0c011b030519110a06020d 66
    0x1300c41d0443c41a51040440c0b020b1400d0004030b5840800607040d81014890003082141518548a0503108162a500180924101a91180d1203490290350600c41d81c540d59032442007001c61840f91804010400084000e018803e0084648181c4c00c41101c0d880f07801c0402840d541c41d802540c04582c10a804100020b95900100e01c09001e03810440500d80076544030501510758070140d01e80310f079260050000381340c403040d0074003202681c3c0c8080840403030085013146840c2c8030020062880b4004100d02822a005c400c0d8400c0800038440c4e032140c1d003d44c5500d0240b00503078101c000740e000040c0e865040222a804000002802000c608007108401030321041c02135070303004911034900d185800291550881c005402c00c04014007a610400400240364486514401c0804001c204080810f402c9211501110341e48070343c50051240c0a004a90250700b0903640107840d0b80704107d1802622442100940a00f1780500d00010045004400380e44154816151002c000d5000c104d407070004d2840d2001200c0c10700b00103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 830344577 1250 830343327 830343329
    0x10140d0c020c120604030c022b0218040b070c02030102190c150513080708090a0308040602060708060a05131b18080a08070b090111070807050c46120210020601 70
    0x148015060b03503110b0b40c40c11111f07508400e400faa0844040600c264090301000641c602d24460b40d89e034580e1384a6180304006061a400450902d08116030040c000031420403080d19400c023829042c040d40402d03941c0702080c0640212034500000b145d4400b01103142a070002e403a6001e081c1705135001107070303a442040d660040365020b41d12402d00a0058000a00040c0301300010928107010740101410220f0540010b000044141c20032a540340e004601041602d804200140d000100c80c01d004030103107002d0000c203684941300c0c820342d0700c20740c3e8106515412404c82c1d803000b041d2400c0c40f801850444407444c4040d0040416680d4545012100341b40003a50b10700c08243e04080e03c0d48480d0841c5080d4543d180c00c000b26038040c0644145550300c3e4050a5040c0c40b0b000101000e0f4481c03180181c480149080c041d05044c240c1040c00d001d498404d14591a00c4800c034084805091030802007440c45441c1507041500f203120545e0209030451490020a22884030f0001c114100d10031502c01d588125044001c0340c42e0402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 830345827 1250 830344577 830344609
    0xa0b030703051902061201060509011205070807031d0106060806031902030604081312050d270b0d0f021c05010b12061c0605071713020603010510140d0c020c 69
    0x202078419041180c0950000d602d2500041101d42440c86c10099604552402e90000f8046480050181ca17156004011280141c0a440040004c5d241412018010040c0103058004265a074030f60814040c08109811680c001c42e10300800040d929080c000d4001902500c0340761013445a906123903009190840c61011140d4090042c029548640d0f4030000385400c6105020100c0100342d1010512248000159052501035001000280380c2120050b000e42114281800c503500c00d0031402002c0a2100120307400c60711019080da03a600307202c16044008006d80141d402d00140000b81058940c1c000b04100040051026003c110503640e13010500218032914101c04c0d05661310300d0008525180507502070710410f40340421014240001d0307450f80c00300d800441d000c170045003000681d90860700d105401d041d40800d194405002ca040250001515030005205240c0b00e501000207802d002441011603003000d4101510650321402400300d420040d1078001c0c0d91030018419121185110b140110107600d540349 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 830347077 1250 830345827 830345833
    0x41b03110d021206070305220308130c050607030e1e0108041b0902031e06190902030c0c0102130e0f06060403060902120d0e0a151b030e1003050a0b03070305 69
    0xc40c100600a034038a91800580e0f1002031103d03030182808003841803900c0345950b5900094689031200c0c0072a03130030340240001c090318a403c186a5001a410422003500490282d00c02c00d1031442030b1400c1440407000303803c41030b001032000c95003508150704a10005080750044170741200c520000f0208491000400c18200e00044181b4082000b049411180c100ea107055190100107154a540400082e80c0c0203446510305a0803041041180c40c000900064020f00101c6003007071200f051501e6a014100c250040490403503000001c81c2c180782c030b9241250f00401801d4002c7d074848450030708070b100035682c1e48280d000680c070727210000704020342010085101c0c1e03d00070011b80c101030440d04c5642c02490740c0c0c7d20407600b18010480f1080b00000400106011600c6640d9107001c901c41ca80604c0880281e030391241d9048180c042d00d19081d1034018900000d41c041c80401d0103a83c00031400d04503600480c84d0b45461b0000101c1040d003580c1640354024178850030207260305000c0040601c0074940c2d1280c81c2e20020344160 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 830348327 1250 830347077 830347103
    0xf0309010801080312180c060325031418010b12070314031e0319060e060319021e130c0e212e050c070b0f01030f080a26041b03 56
    0x1501984880c0309800121003150f40d4200141c000c621590b1080e6003090045c6032011009064040c403604e0105184c1b031528040c000f81e41940f030a9440cc0c5806062103440e8240b00080060840b400d40c000d000c4a076000300300f012000c11400e8940c1d00c900d024041030721194003010480480c480000f04a500d00c41c490951034140c841045400075003600040c21041c014060301c00000022492400b601d40603010901802006040c800c0403d403902c4002d00281d100150804000c40c0565240800000c00d01c2c81d501c40c01c0c0b600b2850500241010505c52130004c07201d803801c04905c1e58a0752120b05d141c0038901c00d440702c0c0000c0308010b0664444041103031200c08140d122500b194044032030380b10316268160307a503910f01310000000820401514401c0724500f00c0040d000c181d0701d05100f4a40c28064004403405030440095046481e0303080301224400300500310190000316540c2051107201e82d02a11711581c3d01e108601052560403154961069400790755907508040901e040e407502841000c112680008103403442 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 830349577 1250 830348327 830348341
    0x80a1e090b0703210f0b0102120702040f0209030f01020301050a0f0305030d0f02090307081510030203100506011704120906050406050409090204020403020406060c03180b22080f0309010801080312 86
    0x580e10100e002c400300b140000401e00082030f000c20413400607010302c40105148111400f40000c403030103a00712904560004400c40c0101700800221404c050301601d001c543d02c2c3c0030780c0628002e44580e07490250940b01d032100d90f0306910019409903050b2801100c00021250352103041c41c01502c0c0c1c0e400701500641040044a158066541c84200c01034040703040903050401400c0061b0402d0042d0307108210341e0700700c000f09541035605000c1042d4000c000080c0c0000c4c007820340d00400d907200b546141982d140c546c2d0384007080340da80c0580d4062081d4503130304082041900d440e01d8100c0140d540b056110300400c501c8100466118001c00568040e541d003a40e416040c240b41414100240c01c0401b01642c0090b420040030015031664080d039400340c98252110305040300c0d5032034010499041c4403c3c0c50045004041e0034460300350500122080c4200c11000c003000902070398845001d8002951100e51740c0d101e0119140c1d182032003c00641142e402c01d1700c580030f181ea42c0b07100941e01c3e1711612501000c4181100005004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 830350827 1250 830349577 830349599
    0x12010f0b07210c080c030c0f0708030a0c03091a09030c04110a0309170c0d11120d02030712140108100b09010b03040311010501140f1914030a060603080a1e09 69
    0x14590345085036810f840c2da107802003030703074080c8460070302c5500b0009aa4039a844100325840e8154410b00040c8981441c1085040e12802550079203400c2044642c0e11009044c41380f4681c0e40500803030103c10300105804001c59400341d11180c5030074001c0c003851a200700185400d11800b400e05c4440c0c01954509004038000301c001b0240d20400320350843c005609002c20404c000c000d45008145800100101040800c000d002012040035003015540042d211599401d1150241c840224103000c0140c1c4a488415098a8004032a170848041c4c80c90402d51a05190b2802c003170ba41214200c10540b000030381c07110b4101050704c6a15480315002032001d801004042600c50045900501901d0140e101501d00c014040c08d4035401c2e400042000702e400c40291b1186004550540d21a000b100c1402403a840030001c949032000d01e1080042007806245401602e440034030000a41c00c5e44003208101d22a180d00d401082e44c2c001c01900c0300051940c046801800b901c0102081080100b030302c6010400386040343c0c1b005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 830352077 1250 830350827 830350883
    0x15160203071407060306051203121302100903110a0b0f090d08030a090c090c1d0301110f1206040c09090c09120b0405011b0e01031109030312010f0b07 66
    0x10451004015100110b03040e201c50342c155a0301000a40310312441d2510050640d001c80d00154442d0301c6d6004920314103080001113071400611410555820799400030f0750503041211a47c040d400a000c000e9030826240d00c600c4040c2582d200d42c041070102d00c2d00c0000d010b6225201c0c0141d2051303a00800c0601031806602002d01000d0000911400c204985551281d825030019201d99400c25102c10a406c03c21940c0100b09000d0441004100010341e03041c0c03402491140c0c600007031281c0703188465020f5242e84080d04803c0c0e16206800b1078079945c0750b41c0075040392075901000f4040c010070803040200b88603203803074016880c86902c95510f500c0d4841c2052140b000034049140714400348420107000141114001d61401d030110302480030f101852505050aa0a442c036410204004d03510440d102407000e034010200e440082d10130310340001c130141c034605840128030440c01e0750b69140c0700204090001c11140c2c04002e050325501048080015a100d5844242d4099168018074460241180344c074808200101d1751 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 830353327 1250 830352077 830352121
    0x30a0209042306180c0109060e0a0305030315010e0d0305041a1204030e040b040c081612110406110105090a11040212011517090a1410050a021b15 64
    0x300c641030103aa0b1401d9000071011800e2003e4010208100c030b041c482165001c0d85030070b10009020040450380000300f802060740140c005025058440c0403450b01c68286580c003459100d4212030f43ca051901401105403444802c017400500c0c0c0e4410840300d0300302924030070708913070f459204c541c102414409440d60096110f6440600c80f1014000c02c44000800c440f92401503000b500d03011810700020083c030050301c00b180002e5010b107041c002c1c01d610030360b4410750255101040340ea400000d81d0b1019403c4030200c0c2540d00301414a801c200351646603c00c0b1400a00448129071596009040d4020342d0314280d840881d050211908214003034800b19400c0d405095600c10000c10051400e01c03425030307060040f002078108110481400b0007503151590080c80301c444090000210010710302c0e1007030007242d0302c0040020043c9120003141c010070340600100016503100d14440d03001d0007546000c80e0408005d402c540010081c58904082440c0c3c83d14000c9841d00c08180d00c00840c0c81290788100481e030b20740102004103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 830354577 1250 830353327 830353343
    0x4080d0e010608070f08061522060e0a05040c0e13210207050d030909050c07140607030f060e0604020d0b0d151a310c09031b180e15070201020c01060b09030a020904 72
    0x1c917003801760880320b421270009490b000403640c1c20138003840c00141005012a52507880c0100740800700d188000150b04459280801092507524600444004102084000c0c806c50400c0141c40b4680d08844403400034903a0703642240c0e0031590701c80800903884140200a008500070300e40034401041f854100300d90084200e043e0300d10740052950307840481c420004a0416a82007141400040c0d503260090001b0745600010a014842c00d18007058115003000e003042d4411940040e14004011040d0486000d4440003040c0d52219a21800c0029484d000803402a080900d8407440721070340c07002024500c2111601070b100c0c04d80c0c20501902034440e451240d441d8284801c0a5220040c480800c3c022142c501802e903480c205000e15600d42a8924030000d214581040000e02050201d101028402000d1010b850404035005070082207060070086c00d002c0c480102c0c00d03454100140c1e5a0150000d10700003041c0d0303000300b10703131035035051000d03518096240000e91507044000c803d009450711664564101e4013039401 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 830355827 1250 830354577 830354599
    0x3040b04110f0a06110709060602031227030d0b030a0c05090901110a0e03010f020c0322051c1505152403040311060903030112080304080d0e010608070f080615 70
    0x8107540360f1903000030001072a400070040d001e482405400700500300044280300043c24000042d440c1d0140e115030829000d000d170300080c80501d6800700381d0346410812a005186203200b8241d15200e500109540e4420b5080c507a41003450700300010002e07040f9810080e28076015080104000342024090041e00e101e64a40d10308092103014200144070080094441e41d8900081c201494256910781e441030300d44a2043c07046244c03501010003254050101c0303880c0b10800010240004c42504040c1c0c00c038580141110380090501c08419071180c41c0c05000c8c195000480c0316240389c0300c4c10b86400711460004521039031004140c41c207250341182500340c0c0d03403007050502540c907244285442e04100c405070005464a074081c010003105108941d00f141d5154003030b43c41e40d030401c81000d0403d400302c00002e244480000016091103503010540740c402c0c04480041c4078494919038920301030807090145506c18080c0c41070000f0001d0f03110411000320384080700640207a6032000421107000018a0049030481ca101c2d076 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 830357077 1250 830355827 830355829
    0x12020d0204060f0f0b1809060109080106060203120108010c0c0b0a0e0f060f1605070f022814030a0b06040504170412120309030c0609050316060204091103040b04110f 73
    0x14100251040040b00c40c4040d284c031404441c40c05039580142050030080100890344001000b03420b40026090f030300110103845900048802d910207a210040075440d220b000f044c89540840106420383d10b410240301e03181d03201d95100d401c0311082e1501038040385108500784000384107141c505501180c7d00c8400248282142c03240ca060682c8404070088a8014070300f0440f1240c2da070800785401a01d03032090840409424000904184074115014146d45e404814440441d034450620f4051340ca1401e503e2034a0b400c0362100a040036060b80500e0348903d202070a880307d01d00340010102c27040c80d003050441d40c4a032290420710005020140041c0c880440b2060407100366100400244010804000c0301d100b041114217004181058400c03c034030415041c8101680403d500c10070b00e2003c03030b8110a00284500c010300d862881c40c0310700c00c04d0441c03004481d001c00040c088154043d0040750000081071200c140014120801c503c011103000300700521200c042008145000c00c0c41c6d6090101070142d1003a400316030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 830358327 1250 830357077 830357081
    0xc0201031d07051e0d2a09021b030310060c110d03110705151207020f0d050d050c0307050724150302031902030d140403080f07020108070801080712020d0204 69
    0x1070004041070b40022400c0026052104415214110201a1009659003800001c00101c030328500500b0501c5140f50b808411500b03504030402c400340c2d40101181e015034941101c80607401102c9a2100702d613480140181c501000b204891040c451290001801070a100d41605c40181540c0c00383d4401c070340c0030890131103621091800d41c0c60500940703030305000001c0005024030713051082e0801400303020400c3e589100d40680380c007510901c8844d80800801c550b10860102e16103d032012650707845120351002c2d0142c443e085001401c01803440310091145a0b15940c809030a44800d03950340000440400c0000302207604d00b04800044409600c12a11042d001031a4800b80c4200c0044006004a50b9004000710310f4100214295045041d11841020301d460f000603031126100092001800548000000d1901d0395408403000303983d12054a58a48020b12480e01454114110490102d282280821003c2c1d004440180c1200d0b40100204405030404154095a81c00346d0b030308a030889003004204006070b82e64 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 830359577 1250 830358327 830358371
    0x170c0a03061d0103170f0304150e010c120f180303200d1a120d030507170109090507050604120f032d090506090105030103020409031b060c03050604110a0c020103 71
    0x2d6203580007650460134900501d100030204d60742500d42c00c0102c21007601c1c01900381c3c1d50050304500c80c0e0b2a0715000c001414041c00002e03040a141d9441d1420002c89950000004041c0f1000580300708a80c2505100080403502c590030442c0c1d45600c10f0b4501000a8802d0308030b8200e1046111107900c0c01d81c074072000881d498001488540049858038042d0240c21410401c148040204032a0401428160003166840c0c24034110074104064448000518460044070001c01e1040c40700c00105003503a40c0e034907000080000180c2103406014021002a16290280540d0156120b030141600070301c40981c0ca183d4002c0c0c0e07014040b418404425178500d50760500c44000c0e06200c01c0742c9044070a1011401008059481c90b40081e8804c01d000d115496882e40e1100907a41503c2d0305841c00100e20030941006c0d5224030000388003200b2a542e00c1c0420041151740d402c4032003200d0054800b8005603c3d04001c200640301c0c19684009114000e01141140c81d11411201e00d8060040c1400240440d0701d01000d03560f4900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 830360827 1250 830359577 830359619
    0x60426031e190c030e010305060a0f030b060f090403020601090f0f051e010608101415190e0f182502010c020c0607081207020c04021810170c0a0306 65
    0x20032004048401140c4480d403002843c540101c4045aa9501030030240c24404100c1c1003565840000d50551640e20540010f010280c00340c0e1681583ca00d40241901c8084411b10700076070440342341c0289030500342d0384280504d9061b00034001e01da003000d07007240041c103420312500e5100340c569982d042e02120b01e01c9110300032000149410b28904030a841e406034031506031b121404102c11041040501c1126290340e20503544001c60003503424403400c0000c0c50540041c404090b02160000f06006283c07142c0000040c00d0f845c98641d0311110441d4410047d026425400a5412420001ca078080025102485036884811071102006460b001d10340304921010f4044040d015130f540d80c0680504940400090014400c02c44541d898006290759586c55800340c05451a240e00008001c603d4082c000d0021801141029004544510701100c0d03000030080500390050003107000c001c10440322885001c102c2c4100b0001522171401c0e49601d0101d42c0c05910850201c2d04169403090702007610000041c2007054040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 830362077 1250 830360827 830360887
    0x1020415050a030c0f020705060a0e03010212061504030b04060216170a1403101703040909060f0c0f09151701090c020f030c0705010c1e0501091106042603 68
    0x625440038045503515013440e014002101810000241d00044c01c00903181c0c2642d10644504a9040641da14100003042507815400031410045005082d411070744519411103815414507010b01e0060382500c41c1d400080c00c001d64580c00640401e03502d40092040c0100a04e8003c454021601c0310440b0551601c500703c25140c00040c2002a0b540c0145c0110240c800c0c103200500d14144441000c0c240c064520402c140d0810840001c480044240b05444c0101044001031001e14028900107004107401d401c01c03008203241214030801c041c1308a0891a1010490f222490240c0c01c1410080c0111130802a990400c04400626003110300e9a20310745000b44190b02004c02e1121a105010381004019070b240003041c1d02c10712003041c01c1080010b14400702c1381c003030810444404c224100590042041c403028003001c20006420f404100c0e056000c00401c90003012596040c0000b00d04101d4a8821441011000141c25040e0390140d05d0242140c0c900c00050b0040300d1038072016100448920b41141c44000700c0365 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 830363327 1250 830362077 830362087
    0x11a040e0414010c0e130507090b0310090c0801030b150604090c11070e041211011107030503070e01080105030c09060301090605040c06080f0f0109020904060e15011409030c09090102041505 83
    0x482e0900070f005400c2042e08106070020704840204100040b0410003860305a140c60225000f41d00070700b4031070081c0c590040003a54902e040140034405e0000c0b8424103442c1480d006640319180e1065005070f0507698441c005034400e865042180050654149400358840c404200c0028641d03140d01c82c1c01c451041e01e0b00c5000c5002c2c0807405d110709200081d400300c104686c0303403400c12001412807846030010180c00d0a09000082c00f29a0040c01000041c603885144800040c4460505030031001a5124032210b03500ca030300240d070300303401124a4a802c0c460182c0662280224090a25110303040c01e038868800350000940b80b01c1c1d61501d405541c01605d0a40c2c559503072003024420340d64000e84940d408031101040c0001c0341031004901401400c14410403040d641d01281c05500ea079a90b80080e80100385420030600542800034006141e00c18190700e00d030200380640200c081c10300060741641c1002500a01801d0301402a80a001c50408005c0c60080c0c15582000003003813028803000000d80b049030940d1065141c0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 830364577 1250 830363327 830363363
    0x6060903020f0a0605071b0e0a1b0f1b03021501031a01091104061d0a08060604150e151503071e08091c09033008040506011a040e04 58
    0xc0801c40c2d154034022603941c2020322034603401030121000300d58403000404290000411001500c84983c1180106041300014440f600d1050f4210103202c2070b0848101415800d03034501a281d41c00d00c01c03001c0000c82e44441c051008040f400754103490f464020300548070140703182e9012400e000402d03001207038030a8402c4e20003010654202940313409001d040070b0800800d4a03000c10001607010354450402000043c4c6506c45a0020764116841048405420110903c2d151324071692144422074a10380140d10741140340c8840d880c4405003108a88015003064041e031601700e2580d855a00005060381c210103c010354100240c41540203511482c515501c0f201c4810701c4510042078541005024810032554109014400c41c0101b2611003210b102950900420402c01090b01c94030143e0780050a4801d080005603600324680720038022900003442c118140102006041c1e0300004152800303000e5500c403100601c404070002c6039459040c10406245420719039070b07080c5901c0c40c9074110f86c01c456140d5800701c1c11545d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 830365827 1250 830364577 830364589
    0x30406060801180f120c0f0308010303180609290705010e19021003050a0e011a0324070f09090216020906030d170415110a1707080105120705040606090302 68
    0x40d404003c0c414600c00c041c60346030a210070351142d1002d04030b4251105030920842c028540d44600075031000920201030031a08018100060074030007940450301015800c901112105290000e841c1d607521356040060500c0c1d0140c485100c040005040c0d000c40c10324810701d8100394805418118810340001c11b029801c0d1a2442c240140311070050901c403002c0800c1c40050ba02d4440c00c84040c3c0480c54001055940c0b490410050680a42d06540c194070b000c1684040440096040409034416001c660403134882c10800c0d904200c907007028002c0d024586010505041c401c07005020180101c1c83c1044400742c40c0c2c184031089034007604052046502030b414031011402c03c0c54600c0e6110000b00c01821044031501c4e40502a40241319100303410030b101e100000c2c204070140403003990a456400c410004800e5503603460310113030305c0b0075020740c0425085040c2079601484002500e100b92a0741d61303040080e07481e0001b0b0195954043e0b0740110903019000000c209504d40b031107a10010181940c1700f100140c654014845 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 830367077 1250 830365827 830365841
    0x507080f0102090a170a02090916050d2f0a0e01241b03030617060702060a0b011b05030705060f071107030203060f1b0c010c0e0306070207031401020f030406060801 72
    0x18080c0d0040c003043c40703956910034140e0101d0710140c20116a00030464103950505a800780029031040c00b6100b4410444000600b03051000c00e520109403203d43c451042048210040400501c1d111074070268107802411a0303104a8407c51103500c070841800300c440050209520b642021007603c403441d004002c580d0355900008000148607602221484503c07000400c40b14101d410800c140784a51032100800d442580b0400041402002e4540e60189030240c190300c0b5142078401c034005100d4600401e9040e6140e124001d00400e05031202c0800d1174100e5800050074000581c02d50b881d000a12042012410500c6010b00c00c08c0b000080ca421890003c0300900680c1300403102c80e602d903000441c00d00041e03c00151158001090180c1c00440d55105413513030942c101c103080401c01d41340c2c0104480c4000e10054001414000041d00c90030b000748a082e090640e17a0303a0440c1d4040059000880c2003000c141008903462100c40c0038000135140803510030010001340d2054404440d00760b0340e40c608000f049420702c80e5038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 830368327 1250 830367077 830367103
    0xf0f050c0307020d0e030c0d0c060f14030118020c101d070e0609040c1e0f0e070f080a06150206090106081615090e0705070501060b04122a03050708 65
    0xd419410000e800030f50350350070707509184140a80300d1100e0303020381d07810001d040081d10b00500c3c07201e10704018034240246000600c140c401080b4603103819000c1e68040c03044448031251306080d00341940e01e0280f00b11140b810410441007960b500b00207005c1480ca007030100b41d010360007503580441e0139004d500071640100b0740000c0c0328041b83c008032003d1005c3c030503002a940c1c110204551700c6585d5212811700b19260241a0711800d600d556014058104640e0b0f04038010032545407080b07401c002a2307034100002801004480c45800030b0695544c0200b032a0090365010340103440581e0000705c291b00d540380303494110717403094660015038401801c00034081c0c024010200502022406028280b540100c44910406940115441e9032500142509030078031504940008204010750b110f082e080c2a50080c1a0341d0040900b83c5155003401e074003180341c0e2b80711340846045500b00007100c00c2001054460920001006c030b841c41c1104d40303032200d91042c00c80d600e1202e00136602401c0500f46007490078a40f40e1400004060036 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 830369577 1250 830368327 830368351
    0x31e0c07090b1807020f0714010507060c03090b0c0409050c0403050c0112020d02030c0703030b030703030f030b031c0302030f0a05040201090e0403021006090b0109062c130f0f05 78
    0x28441010000ca24402100d940580105088040300d00107030101c400e506400701c04011250402c00055800128000354109201c1074070b00032511170a00c482c0e0005510b103094040b503801c11410300011040c2d4440c80780402e161600141201c03003540d500a8199064401202e0000f02140601503030401c2e21a240c1c01900200d00e841c170300761450341c581351105810300100d4140010203076001c0000680b0340468003000300d0301a0031950381c5014002d01c880da81001a095000a01c0e14050074024180052480117994060f1154510301c40059011400b4080003002c06805000f4191017031140310340ca40c0840b00308900d540300544c82e031524400200070300500030301403025642402e05020151f6000701d4030030709641158450328080c1d504c0f07083c10b80c5811244000840800c3c6419000945824142d014000c1400e090340d5618500799030303401c01c40e4010200c2d4410f005804030001c0600821248a2601150020140482e034444c40c80c3d0541c5130861350060f1003031980d1a1180380b2088080038611420754440700c42c90794 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 830370827 1250 830369577 830369587
    0x90b030f010911160302011a062a1005040b040615060c0f1a0f01180e1002072a0e0a090302100509390102061303140d020c031e 56
    0x150005105040c494010115520710b900a10180502d0856a071000c04403500c460f1340700c040c90000d0023080f48030540c041c0440740a00c03001091800300700700c5040380c00d2101c0d4000901c4003c6103000440d03081407407800c01b5215010780c0b807245510a0040c20b00c9035025800001c0107180c1810074200761103249600800f0240341e81000c0c00301d180c100d058482050340103401c20401c40700301c0c6131010680a0000d1104841c03403a10b404c000742ca0500007032242c10780d00f40d503004440c40c0e0107802488080d02c0d1103d080b40c00b039800c121508014044240d0103001f40d64022603101900c16031403083c04d4031031121031909400304a0422803e025140003c5095500950810020081c0e10180e4030029100c01c140f6050500c2d4580ba00003040c07040d2003c11424080104060081201900c242c0120f000d07002c0d03180c150112100e1500c140d0303138158004a103030740c4a0b0682e80e0380c111307552810ba901140c41c4035010306403010181c0b09001c3b40c0c0045030544080d010501c0020001c66440d110f00020007032645410260040b14401000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 830372077 1250 830370827 830370841
    0x20040e07170106210c0e0108030306100203090f09090a0602190e0315040305031b0a0e0f0a06050301030803100902040303030209031b010909020c2b23030103080a031b0201020307090b03 81
    0x24040109000845040c0d16109017858130944a0540354044c14403648600004200640080000c5004034400c40300741ca41c10030760600682e1a806984801903002c0c0c082041c02f846803c2c08803407141c0c06030704c20090712101909941c1e60400c0340c1102060000755410042540e105079049001200340000480003009140302d245506000d20340000c200074200710010000c6102114045e0801500c2219103d116803540402c6130028440614401031500c00e814040350a5040e040c004548015958190f4440d407550b0b085488001c6541c2c0301425241f0740c0c500652001444a103148003030320142d03120b95400b603607030328101c000c26140c00303117008103465a0071540111007d140e0700000a401201c415207005070321000024083d9091000c03584c00c131612118440f10401050500301e400c134980c50345a03180c0e0200002c50110700d42d1070210044141841885c1080180702094480001e000605058a404181a1035192681c1c425543d2202c00001607074010090048464000d140503014000c0c4004071811072038180 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 830373327 1250 830372077 830372099
    0x803030405030f090d0209011401031d0316032703021315050103150e010b090316030312090c1e061d0d0b0606070807050703050c09070c20040e07170106 67
    0xc903c1e4000c2000034480515107422280a085a40062000d4070940e540c1c495110030412107645540081c0c904030381c1c2000c88240000d112401141c84000b94184485008a0100240018800d90500102c500790008a140c03050822920019503030412850750b1861060002c1500d06d403d00d030002905003060f031030318120760310040d10444009103808903203075001010390889210782ea00b00c000112071643c00450700b561001c00414001900f50b0449894240101030b048148000c3c2c040100000c1d03040d08810001612904100f039a503000700e02c00458280d640840460340030f00c1e558040314403600c9504c204078061f040900c041000040e50b4010741d0503840300700007440c002c841c18002000e200100b008540a61101000d84a03146d40c88000c1c030303950b42c02c641001507a800707461000711810321804815031b00e141044462913000c2c04030341d1580c12642000340c1d034560844180c00c8010110a45030140e441d11503a527402510040c94418010340303101d905159842104503818030750810315030705103042004180121 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 830374577 1250 830373327 830373337
    0x110607050a0305370e220203060a090e150c0f031f08071a030a020c030408030c010c020118080a020c190e010b0705030322080f120f01080309010f1e020a050601080303040503 76
    0x151814200194464000a0709400d0f0240300c0344072654481c6c02405000081d600643c0200c5041301c2824800e5601e4200d00c0a0f01c00380703424135116811003000c000d0202d50f004682c1d0703040800201851308100e0201003809480d04112014910b60807004101841031885000807800303051114090b000040c142103607140d40c10130f01d6445000c4000b0000005400328826030540782d1030404d090507255203542c0c035940240e9076007120384610490351900c1610b80701c20380144a220849210400c2900d48007810743c561510f02d8000705404020750184451110311665030310320500c4440c0928062aa055082044c0f11100080507000180451020050840810300000660b6401800c41d500c40001071031000c07400207100e00603007009021031400b15558100820b500c01615601c40c2048002d0312070740c1d4500d01080c2c080e41c02e2040c140740750020441520594480d001641d400d2a0b0782c2050101c03c11414810044144000c103440c00680280a2040030818140051401807410800071406c60520741c8426480c0c0c461 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 830375827 1250 830374577 830374687
    0xf0703030f1a0d0305250b070305090c0f030c0a0b180d08030f100e01080106030b070e0d021302040f0905161722050a03090806010f12110607050a0305 66
    0x1c0f8084000c105032003242110b0441c0404015145006000d080d6000740c030790442c02c100ca41e1001180055075692003803084504c034080c0d142c02408840072500603c04101400030209400d03000302c090f244c42c00c0c1c555400f035000808040c94400d59800c0320003008481c013011032a00391702c1881148600c0c40400d2211080d01c0d000300c8a10f48522094a40e1945602e400c0304540c802c203454042c510002402c1130303044d4454400c0742d0040464400c29642d0100c1141c0e5010180315250344155001c0240e40941002c10310510041c4503414014500360b10fa220212900c100c540c0604011031711001000159100d280c024600f1201e40d092500011030f00c00e40c80885008000c000c07492001040203149010894040390040341e07600714040d80c15511503820003c0407510f280c050104e280c4581d0000042d40c21000020300e044440e41c95500d030f910710306076950440a00700d500c01603610a00c01d00c03800700400d10900c220300e4040d1003034903055a6808507007000451811198900b46001300b00c011000100100200c5044503894 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 830377077 1250 830375827 830375839
    0xf0804060e010603140f060601030605100f05041a0c0f030a05040e100e0403020a0308070e0a0603020c0307120c1e08070f02030f01021303110607120c170f0703030f1a 73
    0x70118224010300341c551016115500c100c5445028140200b0701d855086160016500e05649000055042e2402445443e070024510b4034010003240c40b9004400c009080c5107009072405585091a1100c1005480f02c1030180000084149031032104001f043c48010b80c0401541c1459421403015260b4015482040741418a0b103001600c403004810b002c01c06031500350380c6684582071904000350b40355898a011408104c0d10b80120b10746a006840e208008000242460907403403c2c84400c034042d400800c011103642c030003031103030200003440030806101d6864103540356807031905036040444130790700504244020a0707690300313020010a500008607441240c0100d101102445980302280c904120410001d54651000c900ba1142d80d02c1501450100c0340039000456954001804004561040843c01400c0c030440c106040c1903140101e4480750fa0900607003103540d079101c04002c5083c05900a80d00043c003000c000800104042d010b1141c43c1c1d41010a12080114a11407522204400340942241e0321643c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 830378327 1250 830377077 830377091
    0x150507030507032606090a05090c0f041803050307080a020301050310091a040c0501020c04020309030d0c1106070509130b090601030b04021b0c101b110105040e13030207060f080406 79
    0x1401118240e101c02d0342d0350029041d41080104c2e480901100b6220103100d4201d040100303c20215a00610740200101300281420100b02d6042003408c48003101c8a0360416100c42e0170b22801017843d4402c50ae502e00984640380c3d41e00d0f001d031006029240c000d082c1090b8520500c010301407a03c0c0058400c80f50911180c00040b403000d01d04041c200c140149030002c1c441c1c08980200710810100d03924a5086410a808682420794007004110607800101d44c18039481d4014407504440044580103d01c07481c9190800c0d403461070140c440d690a0500c1240c02c180450300c0000c402c2c02d5428074284d0030350161550342c800c108550201c00080c8007480090102810107071648550300c800d41c0e8550440b85550b140c0035041c014040407210803901c1e58114030119203e400243c0c520840c490145500e08031101c2503c0c42840c00c2800d40c1d0f15605041e51000035141007002c20f02002c520245a140d00902481e19047d07110803400303551030000d05c1c0c80e10f141c0002082107600601601d266821510182d0015400b0744040380d03071 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 830379577 1250 830378327 830378333
    0x51e0d0f03141603110f030f04020409050f0c03070b03270c03070602010504060c0c0c062a201009060e13090c1403060f06060306010207032a150507030507 68
    0x10382010300765982d000e00c480301404440180d08100d81e071024650707241888440304814021119000340620030070410300400004204460403049a030f44284024400613100c0c8842d11594580403804107241c9569029480008081c0f50800495004184250140346145404501d103a06820600008650070140e840e01400c440010310212440140250444110b82d07a50310b0000d0180c20280d9080c1c41c81403515080508407031103401c006490301c1d00003000d502024508101250f4180c000390842a0341a40c4040003010814121346c480004e0f4015041c1111003030341d00c03890b60a54035405d0840c5126188a1841c00612030700103220380e044940340c0c02e10000140c4190081076001482c0341c10101c1451030140100100100b181c6100d080e10054000304075510113100a26a91702400d40c3c401c818444c200c0006000e07132404030001c1d6030280d01071046c1c410565503070795010f1980c14070341305901541e01805404d100c0c10403e0710b42100140031903000e50200076015980071b001441510f0018040080014110040c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 830380827 1250 830379577 830379581
    0x10309030309210e0a030206040e0723120a090b34050c07080f1f3809060f0d1a0106030507090e060307050103020c28051e0d0f03 57
    0x100354000700851603038000d18014110f000c2060b02e01102244142e0380040c040d040000d0407a05890340948003500e4a420041640501880102024104440303180701180d1080b16403071a0168800c1410429240c0c2c540d22058101110002c2005040925051054010034500410150042c04201034165a6103805e412407100c2d40107030700c00c1c82d03080d0400000d910b030246d4000020700c202290340040c4d400f00c0b61100812030310f400b040f030104007442e800010b1290b00d0151482015041000081e40000d50824025280d41e0b262818038107500d900038032a0908001c0c0110000d25281040c045403111030a1030000300290007a00c0c400c02d2607000b91000030b50300041001c0140c030030304c0440c0840b0b610f13102c40d80c1d030381c5008016240071182d14001800301500041c84c0d200c802c640c1c03801040010007600c1c400d428900110b00a41001c0c404009078401c03d0240004409150201e01500302080c000203500d208606150349085604410020348940c031040c2682c00038400310b40d0074291525444d00086011350880c1c1240 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 830382077 1250 830380827 830380841
    0x15051509060705030301210308010317040302030a06060503061e180f0f0d260a0b0f22110306011e0507021203030a050a020a05070615030602070c180b0f0103090303 72
    0x41c00020015109003801000800386040f10721042448a104500c00c904001c00241d0300c1000b00481d601500500024028952511540b60904035039420941d890300001e19100204000707844240e6120030a00090030300b4846560300500208164113030030a41141c0c0018260000c051400c041081c80310904d84070028000c401683c0000c904a03081e80b004201c0e00b944400502d101e08003c141541460b00360440300d0b0803007444c22203403181141c03601e03590780c5241005002e03110a050ba102d08520208401c50342c5101905003010903114000180e208900004401c0380c8c012902c44c07a01500910808c206a80e000c4481d8101d4066220404541520390405481a004100000790300c0220302100011402000020358400c1980d5031041c000c54851000d01400c910840f050070000407800c00c00100410520f03003144403450403611011140399920344810003281c0041c401114003414201007007100a1300c3d50202c0d01c00c0b000107041003106030052000103900c4818004114107068441205c0d40c00d250003903000c14 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 830383327 1250 830382077 830382079
    0xe0a0504060f090c0206040309050f011707030c02120f0306060d020906041203030c18060507020102160f2610051509070e13110703030e07090204121515051509 70
    0x40706941d00c1d580c2d145007001e000d0040b11001c40c80c2480c4849007a100042942c0242e0701034a0b42042d907030901c003d0140c2c210448004a044c404e80202c00c030300e039041d12826030b40304031a1590005003181d26481c000b810079040d089900c40202c0c044c4802c10b00e11910b001160f41242003240e85030341e502c2e103000002001e40144038460b035000201040004868580341003100c5418444e1b5800c01c0404076582d0f050300c2115014101e06001280ba42e0300b40807c501940040001c1401401240c11800c4030490810b22041c05070403482c6443d4160100704a484414115541560241c035410a03405489982071079413003458068403c00b00b42c444010900340e030200ac3c0c540c80d9004d0080c1000c0020718100001500d804009034105015001c940d1000000d601c1354450759490b0811418610724000c46901c048010342034070300d00c0c03a0040c0240b0000142c4182c42d44001c00040c003070100c41842880250510a080300e00c0828400a8541440440d011102d1111540c10a4880444a1030003e0700200400680d5000d450801 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 830384577 1250 830383327 830383331
    0x150a080307082104050a02010e03030909240a061d0f040f06030b0903040302060d0e010b030607090f0e0603060a3b0c0d0807080705010b0a0e040b01051009060e0a0504 73
    0x114003403003003071402050000302c01c0e0b50740c45240912600d8040c41880498014010b50081035086d4019846a000c1803822880182140d00703042100c000038440c40015181c00c10490307074120040340908402300401148440403600b4100c00e41c076000000d40066203418a03110250344d003006100f203a55485110341c100683c040c004118488080190800a12481c0800e4548031503401c0060203c10000040302c0c2629809003920b0306040c0900751101c00381500c8442c50015540b44c0003002c0a54504100e514407030400e5a8800b40e83d5032034544006200c50403501b2103103000d03044004000d056100003c030036800c00301d40c810000d007026280c2061103c220326100c030100b083ca200d4002c0d01002d00781c8406514001064030a80d0f03100c1d80b0200030002401c020420040030b0800c18031010002c10030b41405411010300800c000f082060752200010403140e0039402c142d1805c03500000b03000a05c103180841d1405010240c824941ca00700c8240080c0c607030503aa114110801c2210450901182c0307840400400a00c801307801 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 830385827 1250 830384577 830384587
    0xb01090b0301170715051e0903060c030406050c0a1d01030e060114042a050304150c0c0b0f01030803131e05212d070b1f081203150a0803 60
    0x2007481c40c80d080801880503101d604001314401800c640381c640e500c3c1090f01e640785008105101020641100b02000c4d0007584180252007154505200c65071103000b02e4002f841d40c914003803400e98221400a0400d15600805110503115990000110140d202c402081c0c2c0d000c0101200c0128007418030120004900e0249100001380d00041048000440340c040b01c081c0200d01c038280121a041031561800480107d40300282e10350f8900030002150498002c4801c001c4081100c0341d454183c0d204c00400c00000341d8407000c041c1c00e1000500807039030001484582e403002e80d49142c56900e40b074040a490440c00e480c201881f80b04200800c0c455074040c2d51800110001c041c69420490b4039403400403100344004c41c1c00118178030414070b030743c04a485c50005003009035a03403030f140300e0401c0f18070300f41c07000c3d0120301c20040001001007202c00002038420040c501d008290554040b000f42881602944608410b5221a101143d240c69200c02d5a80c81580c01961121403608200050907814003a84407010b18000052 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 830387077 1250 830385827 830385839
    0x60303090a0e060112150e100806040507060912030804030f020c0405090706180f0b0a1202120103050d11030702040e19031101140613050603012306090601020a0f03030b01090b0301 79
    0xe8164403c8000341c0311020b00c1c03100800420240c0d94903000c0c81c200714504090500c60f000185e488590400030750014504d0183e260f603da40c0c070300754040d14242e07110f84c040a010004154002c45900140a80e00300c00d014000d09590064107040740038100070300f8440702c0c20924560520030400c1c02080080140144200d0030070001d503a07110104c5000315800601511032030405951280c00c204200d94519409120309803030803c0c00c1185420001d000350801c406246165003c030480e001400c174014050032202e255514614215241849141d540317010300c40202c0c01440d06407000b00c15100e220340c059070003007144042845440c1c244114060f080990031405821141410390000401d4000c01c0600001c0005941c610344480e44620116140d943c042030800c480c98814040e6000541c00c2807001e030001c10100c40d41401040500c80e036049000c606a6440100540d910380f0905054000c03400727001400d0940c402e03881310003200701c00d42409410b244c0c850a04c900c5030303403080081d08018132800d8003554495842e05 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 830388327 1250 830387077 830387099
    0x2505040305060702010c021905100609151a07061a0303120406060603052203022b0210181407030609151d28081612140d05060303090a 59
    0x101056407180314181c0002c02da1030052080da02407010640041400041860421002e039140031000c9800c2e02036562500c100307030100e01a0f00084c00348400701042c880e803109800070801e40190300c014115035445500b10f0b960218881140d400075007021010a910420000042c40c480d03440d1030081d058800028041d100801c0518840c0c0076901c02c0c2014044240e90340800c4082d15070617640680784440c45000c601200700f01c1c03001604040d10034010f442d81e040b1a94000c0d0219211201107600c0b03101c1c4280540f010036814441c09c089a407040380104003209080c1c519403900e50140e440200044140d4101d0790006400304103000045a00c0341045c411410503150000e20310110071502d1403030034140300880c0840502450302d1011a02d210008020900101d9882040c2d02400c2541c19104056603080e0404920020020300c0b40e08044a40c0181c86400344c40c040308010300322090b030000c100074001c07081c2201c801402280c4c6000724040c008507907900e0300c000003819445850781c6c03158071803007171540020300904e81c2c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 830389577 1250 830388327 830388329
    0x7030f06151706060f03150411030709050f0c0f0f04090207020a06030e0d0318050a0c150c03021c0e12010b01020705010e0a030b07050c0a0615060e03060f250504 71
    0x40090380c0c0c0181d41d8484114540600040b800b5298218500280b05820640005c4800c1c80c0f0040032241d25014841b60140400c40980c1c0503280c041c4000540e00f090306080041d400200040d54007000789140c070300c50105008402400311101c043c0c00003550355140105a0641c0d400c01d103003010f110350366951148844029030100904a00684c3d54050014032980030303110701200300041101404c020380e002c5804030300401f0803001c0340c2d1030041c3c0d0076160340c04a0000c014189100d80301c1d6202c0c440340c2d0700703000c400f651018000c4005d500704100c081000001a6001c142c10034408031014080b40401500c4500b40c5401c40c1d02c11010780c00100482044510f03403c1504004800703c0f0a030260b440d042d44400044504c82d11009540350090003980c000c2000840f604a410342c003000e249000e504010600c00480c0c18a4464503045e038080e9140c0b12510680100010080018000307401c180c0c0035402d01d200481d0f2181c000401c20130760040a034002595002038011103c82c8a194010410600004204054520341007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 830390827 1250 830389577 830389601
    0x30a0b09010501080705011e0804020a1208031e1b130b0d090b150a0b030928030306122a03050f010f0b0a140603071701032103140106030e07030f06 65
    0x117446400a004d5003c0c1039495007411901502204080030444143d0341b0070b0020700102e0700041a043c000800842000180107000e10401649580382040105290003203942d0a20901d03120219043c801c811814000030030380b84041000702d07030300c80700d01d603410b08494070040e405042d0790003001504244004056010040b07003441031004040a17150b2445404802c1003103a10160054140041404003105200266a1000c0000203c0c0c881080b15100000c24035209a01c000400307081d446680304068060003194050003804031441981e02e01a29040540e47e4500c1c0216008036910201802c410003008a0402941e00241115000441c100c0c50304c1c0207144441212140501e00004a409841c3c02e180e00411074281028003901055600c0400009500103891031086c01015040e5051845125132410300039800350f003000024800b0102441075012001c440d21040600e440c16070b4a80505c2150301c581564598a00000d6104007009110f10f070180c2c2e60400380c040349101c4000410031001d50012100158 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 830392077 1250 830390827 830390833
    0x70503010611060603030a030e1c0903140a170c152701050903090f0112060803041a07050a030e03070314030409060803040b0915040b0304050106050f0f03071202030a0b0901050108 79
    0x304442e0619101c540c181ca46550642007004417109940c82a000320061000c1041503458405c00e002010304545d0240410f180403654104080042c0f00900400002641c20740c005052074900c548d07148214040000c2d11104c51031804242005a00c070b0400000520324001c0c0e103070590f54203000c3d8045502c0b15910b400f6152200203c0280451004107016042c041d061b030500960400d114038007089000f0f20010780c2c16040003c10969095140494000c0400600c4900091944d8078144145a02c1d05840c84030340c034035821010040000002c00004410500a0b014901030141e1042e80d00041c4c00c1500c698000762800c101c0c4501c00c0a0b4a1011005104469080201304049030f0781d801c90030345a011b10302c1401a0180c091150701260b0030864244200c2c0c6054518091900b619400b070800240c1054905507171684d035510041c07019080070f49050b016581e0440d081903099401e44006075685845025148210801200450031500e0070400d05480aa12a051071040c0c80e02c40341c03a6000709024811550700348 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 830393327 1250 830392077 830392097
    0x609130302060a051b280f05091002190c0806150a0b030c07020a0b130e06060403062705060f0c03010e0601051c0608010b0f03030a050304021c0501050705030106 71
    0x25440814226600c0d81500600798541e51415014028400181201c10341564021040c0d018180b4000506200c020100c4800da2240480211403202c50021518418011356100382218203401805507070703010f23608842c500c88100b00141e04a0418a41d00c0c11074100780c400030800800c1108181c1c250040c1c83d4040d003100d9095860015800300d0700307000c0401c1d58000e441d5072070078852400c844000710707840501c1c40f0156141c9003259010540750030f4281d100012201002c40c80396050b0340400c2020005002251510f201401c0c0390703002030518421440004e292503901c84d00860800104803403040c4000000352880c00c25080ca007002600da8400722210070910159000080d401c50123902980d040c2c2c0d400d134034040556034a4400541d05540b1000d80242c066803030a03195083e10102e80500300203800d8100021804200000611800d40581150144a40c200707210600509500c80706072507016170102e480309101c8034144404421142c2601e4060180d509240400070080d8202c40218101e0f48550b179551200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 830394577 1250 830393327 830393341
    0x2040b032e050f0708090a050d090e13020f01110a06090b090f010e0c040b01120606020309010905010207051003110708070f110907090b09031617010e030a09230306040501050609 78
    0x180c008480310348403c454030b40807400f92072144540ba58041403d90032910656069100c072442d241c41038007502d00040340504140243d882d6040300b1600300401070000848101241c0c0002c8682c000c0c2e02586040210a046854601ca030800c0840a50794200314200030005040c240109443d4003201c0e074004c00e10407100d0901082005110351807217082800e01030010301e0000b01c10000589032044545040103400c0c1080e1300082141d200c1c04c80103040c0c0e50011641c0d424881c0015260081c0f5a03c1141550000c0104102ea40c42d10b02c28403018040520f40086c0b18001c801d011384060043c404003403e400c0010881c04200468209501c074154022442c0002d4545680c0811048580888610300003500c140000c128203010440a40800300d4020241d8000c604028480c88101e0359640c0300e2100c6204855980e00303021800c0c07080c00100a402c001540c98180c4d0000090148590740c454007a5919408000803601c2c0d440c1c0d01d440001c42d07401000d45400303040c207060440c00b03032100380d404c030f403242c01d80d48003042c64 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 830395683 1106 830394577 830394581
    0x8030702010e0f0703051005130f0b060a05040e152706010510140406050a020102070b070206070305150d060f0207020301050403090617010e011202040b032e 69
    0x206030900c80c400d900e81043c80c3c03d00303d41d07900a84c00c03d202040000c942c2031949100480c01090075210440101c1803907441c050080c00b821020007002e030400005500441c05018102c440d1107085031100c0402c4200c1e8440102014590b01002c00d1100307034044812090b9000040c021000030032080750200311101e0918800f4482c3d507800c40d000500c0640380644000300c0c1c15682d80380101c8290100c0d0302183c2c0610480c05540306200303000c100416424400d404840381e090703110347e842ca100d05003401d002c3e68481040d50000e02003410540058031120070341c00c407a02c01c0301c3c004100044e040d0080d2144001002602e40908081d03408005030405a00c0034003495002d10700c01d83c0c99180b201e10702140100000e0003000842c0c0c100e480c44004102c3d143e10b104410781510301d425405410b0b82c03e01d100103801417160098050f014024081d0003074641c118101c0701d0034207128aa03240601400f208001d01d00f = true := by decide +kernel

theorem cover : BRFrame.Cov 830215827 830395683 := by
  have h0 := BRFrame.cov_init 830215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 830215827 ≤ n) (h2 : n < 830395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
