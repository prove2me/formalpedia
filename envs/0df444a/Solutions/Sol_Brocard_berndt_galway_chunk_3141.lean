-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3141
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:46:59.492685+00:00
-- url     : https://prove2.me/submissions/a14cb904-3071-48e6-8e3b-1041bbb4a3de

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 564748201 ≤ n < 564928057 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 564749451 1250 564748201 564748207
    0x1902030703081e1501140301060918050702120d0e0601090f0506150406050a030b0a03050d0f0c08030708040f0b0a1506050c03040b070312050103050604140c031e1e03 73
    0x34160031800195003d410341c0d00c0c24091954a10440e2900702c000f0701004060081c03d0550842640140010001440e582000d1a201d603503400f4000c1c8075924901801c546201c00d07a50200e40307200035025244c0610b1441d00503180c1d816009160803040d80080c1041c1c041c041d252183d1011000050100d94040d2075030340d40204100b8049190306e403d5035806800640602224903116440d50784030020740d020b41d00e60340f41060f0fa40d44410821000f40255045241d4089040c4400008100700044c008000e10001c2d1036040d1884e400c03020030b032075104940038003a121080400010388000c0c8500252a0f201d4450025984000c005890308900380004442c2c080d180717036881c402d81c80d069141175081c1000300f81a103070079842c0a03078944a0545a004600c2070400085001c52805c0805006e41c201007907840ea060300c20061584d40c0c3c14110b50713912043c1c034140e0300544a5014a403010b0400308031044860400b40c018403c422450b0f220850340510000300c0c40041c0551180d0150184d150307425440e0100c50032000f551 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 564750701 1250 564749451 564749453
    0x30f070f0606140a0512010204090513060b030a081207140703090e0c2109120f07060506040b0d0f060b030a05070302091315051e01030b042a09050c19020307 69
    0x30485403a43c0202c1140c0300208101c404560b10142d400051701c1303007920015001a05006480d001e40640c2d0404607a4a06103c10051140003402c0f0070380b03000d40211000d0240314001410b1503119201e00c14040c3c05034070104105170040020140c2107401c450a85009804041b80e000303200801c0c0c0001d45d0031000101805003c0081510007a000c07500a842015030b1031424081d40710310342c40c040c020210710142000c0d200001300d100030140100101e0b180000c1485640700ba0081e807413030940e44038120403507000b031601e40840d01d80e08007442402d10103607016220000b5043e10303841d04000802d80d00310071160343c0d480d200440160b4405101020391030384242c0040960038191310400100034402840c1d031b800d007985159090080742000c40c1054401114480000d00c0781c4801c103000c5e001d1081c0b0001c0704402c202e0500000100324001000d2413040740221071516408020741405c4548000e08020f00050350500030040c0031140141d1301c89034010003100c511901c0e2031010900b2203240303035081401d0009070701301040101c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 564751951 1250 564750701 564750713
    0x1090f061d040506181503030703021c031a04023604060915150e03060c0307030e07151d03010f020c1905070308030c07150609060602030f0706020903030f070f 70
    0x40070070388040314244000c0c074046010880300d1080302c40b445222139140001c00e5000c066440250b9840780080d0a49903602824103010b942c441c50035003444403101e103c180142c1114030070700c00c103610a41c0d15142b225007481d054007044085c1d0840065010102e82038540b80f17080c01000c806264200c800010380b14007148510040000300d0b960340e4444c240301402d01e211f810300960800d6031001681d80c00c0740b210200d0401d481084581c07044041c00d96070507205400a00a0304610000654801d00c00c5036824001c407080001c1003a119484c1d807080503454080c00907031180660007050808440400800b02c50201d80582001900b501e0b0307041400c615260f40080c245042c0b18003881000e981c5041c5402032082104150307160b5554640e1131001a0074a440400440e10f01da004000312402d1542003c200c40070907810040e000000d140500c82e82000503d46800010958004000d890402414450302810314120341c4404000c2e620109030710742e05000030449240c0d01840e100150840714021100b1000d035a090385891 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 564753201 1250 564751951 564751997
    0x7060e010302030c030402120a0f0c091d120f0d1404050d09080d0c06020d0c031a0a0608160c0203060f0a060e09030730050c070b040614070201090f06 66
    0x500e04150042007002103c00e409070840342c12960686900c0d8003d500040c8440c00c240d140c190040210000c2094072051103040700144050b1100c0d0401000b008000b90401171032034041681f1030b2011f812102486489031351200161001c007106811580c642a400700c04501240d08a10b107140d5003840c50320903c0107102c010466840b51132070b0b504050100904000f0107d030f481e140c80340a4800c002d8030341456002c001154066a4104030850f41c1842000140d11010303001d0508956100d299a001c03811840752480c01c2001c101c1140c4040e03c401c11a42c50740404c285480c440988804203125100c600c1e103005880810400d4440c00ca0540141081c1c1000c8081c0001d4030900d6012507582542d420a1000c03a850110464484e540d001104007941e5000d0388100c90641d0b0840340c083d8480443c0030b94090003a40000c02401e1000c04d207c191400d0707035290411560140918040d41000888800c005c091507402c0c00020a03a0702e00504000d002566107041c90300b21101c00c3e0300b100c0000746042283c009120000b40c08 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 564754451 1250 564753201 564753227
    0xd060b090d060c020102040e0a0b130221040c08030721050702310203090109061d060115020109050304090c020c030705060306150d060801051906060503040f150e0706 73
    0x4424501548000090541c0c1c181250151080c2e80c0c0d04040d40d90035000354100c0b8001d158800320103a107840d1848020006101551040e8000d00390a19002801e218500c22103910600c00b4983c042c00c4441d41080b21150340340100201c1d000e5840740b401041c03600040000e0000b6500c506012550300102680d201c0402c10010030120034420280b0600d40142d540c00c00000e900044c40b4905034a800040303100000f00340052071860041480002488080345040d003200359043e029001c14824851012001d00413003002030074120080d00401c005000c1c00303416144440d155000c46c400480d004c2c54a072100c0e41954055881551150b80d03551080c00125010b00603200403000450240c0543c502c0d050204025100c010f1816102d03841e1604044104840304080e240509044801000300d19201e4545500912050b11411b05100e0307803003800c1600301254015203082d100140d480a0960322550b81c1d1842d1a0310760441201c411a002c0070b008100143e034840c05202d030030300200803c000c0b403826202411514014071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 564755701 1250 564754451 564754469
    0x91214040608010b0a030f110406090506030606030106030e030712170603010c1d01030f090803040c12050705010c020604051c060c020f060103150209031501030203060c09030c040b1210020d06 84
    0x1004104031a08001e0356030445160100d01c517566000c0f0b00b0101c0c0100030f2086078034100c924050001604800590103031054407119100e0b582165111070801c0307003a01040740c3c0550f0082c410001800610311a0308054035002051080300c2c03d0240a955080302411350403051000110300010f11a060580c101e4110307001001a4004c1040c0a0b1400c0020b01c0710710f00d114010759154036009052060b074840e501211004010980400820140d4a8008550360003541c00b5a80c00c0c0c1e00074804292840240c1101001c82e82c004010450b072880d000054552160202044e42c1c083d07018000056103440351018800c2c04003e203404110100d0340d519202c002c84001d1110b400841d8444454012038081c00118107041d07a801c070342080030440c004480d5001a03c50900302d0303501400b410980310004010403040f5030580384200c00b910074964a100aa40090086054150340341e4421104806035052035070206c8081e900c00707000b203542e141081c0e0229280c10704002000d604154001405d42d8000980d114a402070003c4117 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 564756951 1250 564755701 564755707
    0x1107110f101d06130303031b02030a02060411041508010c0807021c120e16031104050c071410051e01050409171c060b120a0603031d010210091214 64
    0xc08024440e01c1e903240d00c40a00c07514004402c0d459030b582d2003580e281a01e603940036180c00e03859282c0217010380585d00310300e400400c0170b0014003403150020050f22020011540101007541d0790303443d20301d0700120150809410030b0341c0e035202c1044408a0b03010070020b03151f100c0004c80c804219201c000c3c40e8540003880d8008540111507410403040980f203010680b040103144c00140c2041d844682c00c01000426603a100a00c240c2154540079110140020102e0340035a41d0305946c0d04c0410180f1041d60012122070004c54820460b02c0f0014104101e480e01d40e03040217040b15101001c10504104584c01a1040000c0c201c1160035250a40c00380da4035240075000984050000d02000d5503121541c008206000724034100c0880c0103d51002d00b0032003e1441c8018150900c842c43d03540312408010b40c4001e610320700741390140c000504484000e0050038120303a4103a854583c000451464400f420001c018894114010a07200f840d04884030700803a401540a4001c007214141c1601c2c4c09044515041d40e0070003550018 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 564758201 1250 564756951 564756979
    0x30512180d0c0501030e011d0d0801060801060f0c03020c09091f0b0d0209090f061e250f0e06030109021317100f11070c081002041202060a031107110f 66
    0x1980c0d01c0b007261028200401c50880700f02c0101e0240060141c50325030004502d0030782e101d1050000d040c0005004c9602e402d0556601e5032011540f0403400d00882c07000c03039883c03081412260302c03515008014500074815604101080b00000f4640c0200b6034400310f480e44002111400c2e81d0805284003551054131000300280c03450900800c3c074650440030080d00c14040e503c00242441802d0110105035402d0b42c041e90f07000c2c5441d100034800200030902c1d045043c0320701c0c000900941c90b02034a0108034805c0320106160a000b00754112000b4609503620010000c0c00c0c2c40742d01058544102540c040d042000d005030701e800629441d0103d880e4980e000d030f00388901e8031090844804020691a801501d42800403c25000b103869000181034100588982d60000041443c1800a0714041d0001d407402a000d5a4103103006d801d080b0140d000f00c0c001e144503080c40140440040c548440101050270083c00d010803400c071140500440354208807025912400f01c1c3c501d06009141c10303145044200002c0300d1055005d0b40e1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 564759451 1250 564758201 564758213
    0x10c05120411010c05100203220f0f0804180e190b1914010b07050607020c030312090c0a0b07030801060c11120703060f090501050c210a06030512180d 66
    0x406000980000c0e80342c2d402d003515922901941140540010490713070154205482500254030403508050b59441c1041290100c0c5d00b80b866000c54180c11004096074520342e9143c40440c02c1040721304540c01181000000384840300e508020754140e074410000a07040c4007a600003800c00701044019108420540201d000240202441c02e420000340c0d0b03103100c0f07809203000d02900100440c01513810300d0840c200000403007541b018000c2c03525a205000344c501e1511015420380ea907019019003d50316030002d222079120640d4081040f50b100004070111220840d0341800b05171750540d41e8005000741c941c0041d2031000e164101c2003903030040045262041d140c4400da00e401301c140c4a60201e4622845903480342c0f02100404200541c003540d003001d0100700700044032840d540204541a404c035859400c3c480080e9440c0c06140c144d418110540d807042c020f194019020742c2d60079070011b1031040c1c03160b5540004404100108182e01031400403454003035a401816000480e159070030320072184a110540150000109 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 564760701 1250 564759451 564759487
    0xa030602180a090c17040c1206090f080d0b0904031d1807020a03110d09060309020d1a060f011704030305061809030301061e0c20130b0f09070f0e0a08030714010c05 72
    0x110540d4006604448e407910101500100001412140c0048003440501c584903001b4003007103510500400100341d048050201c444800c80f0b001d404203603219401d420380c0c10119045594071400810394981042488858001d9403001da6445005a0194074007004040d004030700d2a4015100100500ca41c5107821b800604010040c090b02041644070b007081000c64031034540c034a28840d484603140d00b140c07403480103154484004a88a62086020883d03601140d405034614900d020841618240544c3e20b90320213602400d8003400f140c1e041101c0c0a20f403030303c1641c2c103a2000e0080c2031031000b40d0b079a5403410000034450306110b0102e01981e049011070030505600b20050300c05095000d42085010700d0844018401e00715926100b40c0c01c80f800d10840d082c3c82c506607100b602480ba084800c010180080c4090115a070350403116500440c03549125024060b00078500200c0302c04005024001c141d45401c0560f05681103108129840444850b0b036107041c0500b800f5850615000b4070309133041450150b000c018008c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 564761951 1250 564760701 564760709
    0x3080409020a110a2013051906060c020312211801051803030a15050319051b012003160b040303060e07020706140c0a2a03020a030602180a090c17040c 66
    0x101c0b0000710030711501c81b000034000c010201030040144c0e00e4040130100400c4402c103010a14140b806a02054040c0920301410305290042d0052081c2d001c0801d4003042c3d58414002c103440503808a8600b00b1400e0300301746103441601039000d00c0081201c5040040d00b99280035246803240600340a050704a0000041540d5200910b000045506070003901c40ba01c0540c0c00d6080a50107000b02c000010924044203205c001c01e910400c200d80303440141c10710000001c906440301c5070000381c0801e000040c1d44440c1c841180c0014002058910f84102e040390100300d100c40d02000c8441c18840810442410740501c43c180c003d02c00103170002d0651070102e80094032968140503805c10f100108961703202442824095540c0f0701010812200c41d41020700f4008400b111980f2a0f141d485554400d80742982c481c60b40c2c1d1000c481e03014040c524000c2c116516400603400000040d070f0311000d1841411150740c0d610740448001c00c40040d001034040e05899000301860a10b1009594000d005401e0200003007a00440d80112 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 564763201 1250 564761951 564761993
    0xf140414060415050915122e0e0d03050405010e06041e0c0f03050106080f0304030c05040e010f091b1d06010e010c050f061009140105130603080409020a110a 69
    0x18000341c81c9080400421340020303400448960801c040c0c05440030400305801401c445071f08000044100e0660b440010b2443e100004680352441c0135942d0000c41081c15600c101c1c1000301d1000f03003203a03840740381c018011000c0700000d03220003c0c401803110070711074164050601006000180703000d45680c0e070100c1c840d6814107440420080c0c40e009004a100c49440548201d54074050340c69580d090280c042c00075400b541d541c43c06400403240c072903400041214100c1742e008102c0310b003443c0703800104030003000c004200d95035654888445010300c8102d84a01da1640d44640c1c0500141521034a4041c0c0345182c1d9001011000c10440640003807000c809030140c0c1c403c00134a02a2640780704080100d580c3d51102400810728410101d65206109000c80e400e44940381594031802555070b2600f03494140c4000c012003403508400c58005220034108074442103180c1c00319207008201141c0d02d41d10018254459840a1200790340400da80008a52000811804182500041803039407425100c0d0101120068881c201e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 564764451 1250 564763201 564763211
    0x1606050f0f0403080c0106051e060721030e070504060e06040b121b010212071524090608010b041506030216080a08103804030803010f1404140604 64
    0x20260480121030003100190314003038032190f07a403070021059000882d1450241d420301802081508140c402c03400d08210b00700e17148801160480a01c252030703112001c292001024041e68010201e50405001c5503101107560000c0c070110004801c0341803001c00d801542c89242458000c00010b0701e10b14086400c15411540020102c40c08400120100700c01d44c0382c0d2426010701450101e16100c800c0164610704002e03020385d0200040300da2035009510130a40d00a0500d20701d10040100d24920b60300c801220302c0c42c80c02400300fa80100e03110410070b942035031005d60a01c2d100c82040c003900e4001c3c0541030502d41c055500b48049100c0034601028480e0034042c2d101003543c045412600c5031a1050f0714041160400500c5548610000004209030300448040540200390b0000261071a41a48403010b42045201040d1040881b00c1d054500070311400130840d00c00c0700621011002c24007100003107000f02180c04d0302d1211076207045905d00440440000c4140300340d02d030110704620100b000038a1075100c00120342c0007030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 564765701 1250 564764451 564764467
    0xa020910060e060c07050a060801080601060e09070c02030c060c030403030e1e0d0602070209010f0302030607110303360708060106050a0c060c05070507091e090c05010c0215030a05070e03160605 85
    0x11030117140740d0005900451441e00003d030f240c0c000d90b105040c0c075404402d41c0e18503070700c0d1181581d4100c864402c580c0c0040210b800217007180d22880181869610007800d542461009800080b0103422440c1c10305038907000060104101a0020204420710105441543c14a02c42e021001c1840c03141010950007007600c1d0301c08104001c2c1d20b0741100c801d07581c02031011605586a80800411482c05c0c08220f010303104500c0480c40b07042c090a0000c0c1e00c038076608025071442c0e85521552201c09a01030740c020054405030840009080440c85420451809400038210180f804500c1e501e0314006030701c001c0611004005001c01d03079500161f0042d070b050300940007003030103040d00b50126039038442c0103000340084c0a004000b20f107054080d02305002e4030038404402c00300304856240f09405c0b20a03544000b0324209042100300b050354081e5039042a010300082000c00e003018448100c41181c0d00489030425095a504108007035980c02080040c4201c04c141c0050031424111a44c1c117446504a0080405210010031504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 564766951 1250 564765701 564765703
    0x1404060207080c060702150f25020703021e150a1e0e1e040c03020909010302040c03110c070f090603050d03050c0903030a120609050603060a0f0902120a020910060e060c 74
    0x40f4100003420403601a0714004400945441901441200c0300e1003650216080d03c0e17a450541d40110790078440078905c2c204408400c94103900840580d420350090f03500000240c0d8a102d100841d0f405022a5550020203031000c01c0004451040e50031603124041c451090b105901c100788080c0c03040e8002e1b50b0800350f201c085050360f1015009564a520401200b002000074851049030042c96100780c40030705c58818040401e03810381c0074490420f504184890010005407400f904120504002c83c10009080501c403800c910440c4e01c596001c00302d0f5800300c40100b0600ca40d01816400130030941404002003415035071000e4940d0302c8400181c00b09034440e00401c800011410445100182c01022070f07644003090070b405402c0b403120079100032000313240c400c000401c5141801064442c11004015001d10768075003d110b401049150170030840f090b80c40500900580f1950900d01d491280d00c0700070118141944104600c00c40000d00203040a400001d0421019070041c08000315480d08891640d102e1004010302 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 564768201 1250 564766951 564766957
    0x103140405010207050d05090f09060612011d090c1f14040f0f15020d08071e0503060f040605240706061e080106030203061819110f04140406020708 65
    0x4015a400058240001c002055008000091058043c0c070b8900d8003056003580c45021351850181c0040409071940302c80d291201c40c250b0300080003030005090030159030811008074000d0700a200e5800c40503490008036100050215444440c1200401002030144081201050000c550000030001081a003d0304d82c014044c2d0040b00681030b07041a1910b5940c1c021081c115002d2041043c0340720320100c0410380728007a22040c41d10071003580042005a80051080f58050001880d00c1c3c10400b801180d11000720103001c2c2450903451580c1c030365807a81808410000c01003012441c0c5481517140c89001c004e65200c2e41c0f5130501103880c0007070024404908a607002418031449900416051600d5004111411071000300d40418005054006101c0c5d29401014201c8509000181d41980804000f498050040048810044080e429919480c120541d02c40c0103c480100c1110b42103032000d07030f0217101c3c1420140300502c2002124184242683c0081a030818100038002602071500000e100b01030094501c11 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 564769451 1250 564768201 564768221
    0x902040902030f0d091403060c1c0c050403110d0b0114060c010203041b051203091e0d0302100e121b0307050d091a03060f0d11150c07050301020f07030302090103 71
    0x103988241043e8450302d40c03500c1c09000ca81d40880c01031000802c0f544142d09030341c034500001078000c14840e15a03240b0124560020f00000f500003500350078061004049008880107400a40c41c0c00c1e484500718580300034174981000080b40218805010500842c590ba080e40341180c801400214400760b41201140c41c0340f05108010714158000401d100c10402e003850111f01040742c288403146090340322010001a41094580d080349580705006800081c41c2000021302c040582030072418a10201e000490607984034800b0980251b00015500b00306002c441c082c0400031612000507240c40c290302c240a600f00d00030300c2c0c0c444d0803511060501c4080da1208004907819990068103e800a0f2140e840c0140124120302410165400c408030240807003804c041520f004a0005000e0104000b0304428000c01100000c400d8501e0003007203d042031943c48a81042400722584040296a1140105038030b01d04446a41b055000782e02c100100301040290030207480005a152501590315900c0320700480103030031000340d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 564770701 1250 564769451 564769453
    0x3201006030507141f030b031c0503090c010912081b0312160e010804020d05011506030c0905090601020703020913021c1b4e1b18090204090203 63
    0x3a0201c00d00200040b01d01c11118002c0343c2c00071401d41c0900780700d048911341002d5880084441e12115505000790809120100054100d41d0302d52608001081c006200300d4046012500010600000b0541071264030542002170030f142465610342011515502e0301610054a242004100f03001226103041c0401807010002044035101c20003555580c64042080c2c82081010244001100e003850103040100c1203c201610b4440240d6126024041c4980c004030301228107550340c1480c08000d00b5103036180d1001d043d03903540000c1e040d4541701015112043d5500050b00c652103400400c0016030340003450740c0c10f9030ba040d102c0018503150f0320b5140e4980c0c40c40c182c00a50041400c045d810700e164803024101c0e1018010114524200c0361034201c054088002d001c1c202885800d0402c1c3e44801e403000a400b401e40700090f00000700c1280049148241880101d84c100500203503468035010310044018444240071070343c403100151490700c6400320089024400c00c0454a8645954005550700c940c4400186070b0054 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 564771951 1250 564770701 564770711
    0x6030e0709021201080d08040f02060c010b0a0f0501091706131e08030f13020a1401021603080c0111160609150c0801030b09010e030f1608070503031b07032010 70
    0x5040040110424080c0c0035441c415815610403041c4501f5045000c2c940100668400440b15000d020456120f208482507030340d200c950f0081d081e1600b038203040c0281900c0c1301c0c1001c4542450001408584146d2003014218140030107125003c00109540e034000e20000c0c0a042000ca4619041401c8100302c051948205207000b11182840131070401944503002d2040000402c0c0d940c0d101c0380a81b04c060032070294100c1c0b030500081c04401d003041e0381c402001d50140100c542c00d196041c4c4c07508000042d80c000b140c500c1e5000c20310240a03c82401417054400c04d403e907990030100440d000c29561a4070490242c601c0e5141ca00030000e03c2642c4190010106500030140100c422914020b0505107003840202c0f00e16000c0ea000ad41c4503107041c4204c1108084100c040c514000c000e404001c802d07000266030400c01d661041d1034100003000c140003054030304c4c030442c00f03036440340b80042c280c0c0a91980c04050a0f0a85410020f02c00029400028603400700085a0f481041c010180031f07591800849410340c031550ba20304 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 564773201 1250 564771951 564771967
    0x3090913080414040506011416021c050c0405131713171e06090304032009040506090c1804020607050708160801060f1a0304050c060a090e070c0b0106030e070902 71
    0x141190310f0100c0252020700c00c4da101c00004440e02c145030031001c199201d080c0b11110585808140500c4202d000034001103a03d040e0128840361030340105c0041301c61f5800080017103850b0400b4060107a125244122010304c0d0131103525062420b00e1400e90807141c086000400d802009070108241c0064070312950040c5c1007100040e8120340d100803402010300c0003a10f00b1401a43c100d000204c081c1b00d00150f00c061401c0514582d40ca906c1c44a01c1003150044403800303003c8030110384407000c490380300760301800082c0f4880c201707408002e0138022110030141c0580050300c40400c80c01c040740082030300107034107441e031542c1d421240c1020341c03c0c103c55800521940c0200a012019200e80b0002001540c130068000c1014580d50301441010005510840f451106030621208042940001840e0321a00a0050791240c52000c070010f90f4552000b01070001140350140e040c002c406100090a511a155003080400e02405031515001d1080510403e81015150301d06480080b00501c92000106412941507440e0310117 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 564774451 1250 564773201 564773219
    0x41a0d0f1a060102060615041401030906090605190c090e06030c030a150c050306092701050103300c080307020106030c03060c180b040504020f070813050a140102030909130804 77
    0x800c1d40e400f40103208a001141c041c0ca0a12048090030b600d0401080c80e2a103000190009001e000542030306265550240ca004298640900303140103124000001d201d00d082d51005103c0404c3c5159914850310340f1440326103554010703c012080d19046181601c20b513442100003807403c040d442a140d0180035120891041020341c410605c4c24101c0030038140b0083e203010380125002d000403a4426403000c000400315201c901070b404009890031201d1204280c00040800003800d41c0e800380d004695101c0d186503111841c40400c4440307855178240240c0361015001030301000f89102e0b40c0b4000500701c1600000400e55050003540054011640500d2101c00c45030703282032860080100004020108112241000106206c1e807103580c181c075260b429a6007800d0401051100940160032080942c1000b0406800400d003248050422440e0544000d00620f060a06020340c881655000d000320182001c0300c282141e8012056441c1802c0603580e0351410358416014182541d51807034060710740d0a00003008524281 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 564775701 1250 564774451 564774503
    0xa0e0d0e03010e030c061306061a03010503160302012319030203062b120201020f07060b030f160e04022b0b1f0308031f0807090b041a0d0f 61
    0x103088008014101e402e00102e0f0b1a0b22400421503190782221000900b0000350200d4011040d019a0001034801c0d19141044580b0051807591110254084010000e51a080100444910300440d01d111312234650350000e8a032030b251055401c1ca100101d00c40c2d0558180034000d50f0144549140c00d02c0300341901000c0500250b009480e00e83c01091032080c2c404000369010044605c2c80c1164804141d00c07809d40e169441c2103011001501c0840d5003c000c8000b00d0541100a08985801070700009002c1001c242010714029006a001031582c02c0200f19400d034940309a58041261303242c0351031003090740d0745200042d0150241c14082503180100c0e1403501c01c7c0c1c101c09074450b101911034500e028054840c0c01303070942d28004160719580c0500f89110203000003000f8402464114290007140e42d01640d17104017210700c400d074a8209440719407154900700300102d042e00808054030406d507010003110300718164a0750001d8445005030300401d500ca405c3c9041118000010000b242c220b45e59229040c020062101006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 564776951 1250 564775701 564775727
    0x20319020a0f0501022505031501081b0f06090102120f0301031b12080a020114070305070f09051c0201020a08070f0201090603021201030311030c1b120f030d050a0e0d 73
    0xa094040110b0540780c01c420b81400c1e540c05800405d00d4804a140345034001c240c15106480100000e580000d032520100041410a00380c0d46003086e10358107200e41c9074a01100c81c2c1014007044003009016005850f000d16445c00601c040c2c130304035900c03400308005074075142c2c01a030309842c0058001550720312018103801035030507284a08060b0106691790308404158103024000c03410b4042e400c11401d00000c2450000b004901001e00000c146940342c0f240c0301104080c11219100031944070010801c0d025440744040324580c41700e0030300f5102e00781840b000c507801c05611200751810f140180c905200b9a03001b005800170240c0d20071011940c8059610f80b0400d8051103010407030124283c0f080202c0c0c0140030b8020341d8000102c0c000401c0050b8a5603c4c11107820905114914590104108240d21100f0900c41c116224000040c4251750780c190300305001c032084c12076420201541146080d20010407011048600c20034480c10041010384030b40380d00100920581c2c0945e4002c0c4540c062100031b55801186e008925 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 564778201 1250 564776951 564776959
    0x3261303020f06160302090a24030c03110306150f040b093a0809100201050f100e1503013c0b06161502040303020f0715171302031902 59
    0x1c58142d0841591043d00b9601c031050030400300070501c6050b219034003a0400350340040056908a07940c00200c50f00c081c40301203106030701c4115810050f00c1a05800395004541c06460b0400c00701021080024940c000500300510855005e10b01241003440c000030707201c138107180148842c1e445656900b040500c0c0e0001e00d2145c0510401d04580407049150768174112040064140c5250710001c41148a166000c2000304490940d814000c2c0300c0f04d52030b182e6480781480403036000041c15040c1029121001400201604140132042000f0301220f00011056030f00030740c2000c015416070144800213409040380017003641c50010b101c0584c44101c4030030894a41021119001c0310a80c4208248040980350f00102d03c070b400540800c0140c00c049024000079003994000c2544402c408041d4000e0700590b03002e607000380d0059100700070440411105120640c0100030380078507100915844100640200c4034224003d914600308000220403c1074007460008040e03000f0190307580d10111541441986022030030076401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 564779451 1250 564778201 564778213
    0x405010f08070f06090b0705070b0d0614030c030d0507051f0c080a09200609060c01020304050d0c02030604030c0f153c15090c050a1b0b040326130302 66
    0x72000d803083c2c490070f4070030079941c02003a076040a204201d00d40c454002240c0512500c40b0006402241030003601c0011000f940220310103207080034416104a404864a100c1d4220300c1c00d4a902d1303500060b90000d0b01419007041038461185040407070070201c80c01c44003c0090000519081510f0741036000424158583e01c1301c4e030303541e29142c4d410780448460035401403109041030380f0301165091903100024081e0008000a1901c40d5074404140c4035009100e804850742e4000c02130004000b024410041029494a003241c00e80456400090b038500000e00064240182034101d98188140c2c3d082c0b01c508203400090001076451903100a80c0203026042030220220101144100201103010ba0780d40000040c1601c1414182c1305111000100000c5822652880b80e16a00142988403030040e94104d034010b440740d948607402040098a2441101e40000d6425000e00c50440080c640030002500242c1600d0905140c085180404074a42c0c81001103043e0801444104202d00c1001840c144100b440f0743c1c00d8501c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 564780701 1250 564779451 564779459
    0x80c060412031a04020f09041b02010b100e06030736060509030604080c0f0a0602040e1323251701050702060f0901020702220b1f0c020d020405010f0807 67
    0x811141c3c000680724000c104900e41c100310f403a0940242c100100c4034002c891030010340760001001c44000c4000e43c0c41881d5500440c100c11502071041e007030545000c0c1e40c00408080850001000d01080c410500d100740d07030110201e88080d00c40d944000815410f0380320341880c010221803540403103020850414130000c0003100803507031078032460a0700c94556004c4c000700559140e998505207150450b07441c2e01c07118480c0080e030110071034081000d440c125001e803900683e2541060f0401012500003001020b4082e52440b06000003007080822003410b2410060140f0700c40c412000c0c0a003419200c0b023009051485903030010105d0b40c0041c07281c4c13040318034070380c80d80050003080c04c190760907140100e07401e03009030700124005003c0340f81c0c20703440a9204c29000f000616040860b80060800400440c00566580d980c0c0b542e00c400c43d440f44038502074082c048a41c91b0f400341c0c8042402412584018148080140d08e00754482151500c600c4280d02940c020803d00c207d40c2c42d8190340b9100e441c90b11440035640b00d0140000f0f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 564781951 1250 564780701 564780707
    0xd0c0509030709180308060f0a0612050606040302100302031003210806030a260d05150f0f1c080f041403190b070e01120c080105040f061409090a080c060412 69
    0x180c92200300307164890042182d4170f06a84521000340350355000b10300d0340303501984c50f51582c1e2100050034803900e56060400d00a00540b04a403c02007055000e03650130007041c00582d030b8a0b1074100103111203240150340c90740c074145142d04408003948018a041c2d908500d180750840c0c0c2d1055103141076401c0d40da03c00540d0341c041c200342e9106082c030400703019403802c0b845080c407c0c07585c41c0d8038180400204245a00d0214200071000441d081117800d8003118281c90b030820b656107002c100c9a42031850440d250301c0c0410142c00043c1d002c003c00c1030f00140c1600a00d50030400c2200c86402d9500007180030130965103032542d4180c00180c081110070414441c0c010b0700e01c20040e01d82020060802c1a40001e900c41c0295150201039801007888500e41d410711030881d00c024000b120034040d07440f46808560710110594588010b110030f84000507480d6502d641800020300c0b0910810602c504038050031a0010400d0f103e00e03c2260030000c00081c060501000080c040310641000242540114840c0c0820342c000e0301840021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 564783201 1250 564781951 564781961
    0x602010f060b0f1b0a110108010e1918020d0c052106010306180f060b0f0303040605160201030b090a0c090b04050d0b09030c0115030b2a0f0d0c0509030709 68
    0xc0a8800c0c0c148400141c0c240c4070303005015410a00c01c013a500d1614441a460b103025207082040321a07003202c008108440d6030064526006004040b0080b00c14140301080d41d44100b1569064140203a95810500b150f03034155141741d01c0c858002e00003442e1a01141000e010301c01d83d60003064061400710300f111074144180a243e084042c4175034042c040a9007141d0f541400307070400710400601c0c1841d410302c038404600000d8880300d01c030348140800100c005213902401403d42110014038441c5e08180010400701d60080111425692000110300c0504114401039000b0003001c094217401100d070305c0c100f044290031540700c0c0b80441c5440d21031414882e0f81e82c81002031480b45000f00da0300700300c800040f24001200d038484241c20000d000207507400c040201d44503030b007100c03100032880b4041401c800040042c0700341d038000300b40c004044410302e0034410780317001390384403050808081020060000110840b9080501d01944d41107509200305000d1410010310003042904465926482400351090008103410a40b0035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 564784451 1250 564783201 564783209
    0x60112030507080309120d02030a11090a0504230c030a1b14132304050a0b18070903060218010e041e090c090612050f010501031a04030e040509070602010f06 69
    0x58502e4824243e4505420350805031034890940306005907070001900c01009840320002e04000140c5038601174044c001565a6401007281120042010008680321004500143d5000b5200400d10115018862661540f5614481d003540803c40c01e10040101000c011030107000c41c10343c00c1c0600500e40f120b82c0100e0504040c2a4040b0b8412000c06001c5600c0c44040c050281300035040c0800941d0b10112400701c000d40820300b002001c8060f494510f9842e003032044079000a4003071401c000803454000411401c5282000d58016951071000180368288200c0c9a10b0146030300171410344d204d4010328081d64034090070f401c245000c2115000192200d06052041100d60540b007020502c000501e0b01c03005000b4104400107a401c10801500424010054000d44008000e40e14460528000b070307041c0300342040d07103401803414541d040c20010400315810440c00040b44c030003c01009002c2d11185000e4500090034070071240c01500705030030082c1c01d0700040303800b5007201e18540091120840000d503400880d07005000e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 564785701 1250 564784451 564784457
    0xa05150708032d010b3c0903011d06010b0306030a122109051002030a020d020f1e070503030606090103090f0b01030b0a151401020312250905090a0b03250806011203 72
    0x114007114819400700d044000d200141ca55260004130b0307107106e49250310016140421082c005841c420504091060008440e27105c0c80c440f840c2c202000c0c00300d03100e5006100700d202c1c0c241c011020400e6a50140105100c081e4041c0e80081d00d600d002e100600b80e0481d10f2a50700440340001004402c80e5018043d078464285d2060241150350111405440250400780605a1480d42800003c1043d101403008059030014400520740700e440c4101d403002441d2844480f040501c3d0144884400a50f00205a0750410070032610952a070204400483c0142a0003101503c03e914601042c4280700c0100302c030718181ca0203000550602c1c1c0d03c4142480686070285c20000c240c45400b072080101044c100e5410000f403205105603407070310a14541c030001c2d194055070102011048403c0c549161f200c42c40381e0b240c2e41d46090503e5040c0b10310b04000540c1d450002802e44154503220309200c0c0a80c1c4c0c0a200e55041480300e01d400c019030703220150842e56041000c1c000e1000d1481108004221003107001c0c8000c81c40d9505039 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 564786951 1250 564785701 564785707
    0x309030703032d02030a0c050f07060207060902151216090b070204150e07031b050304080315100c03110106080309060706060e07030b1009050a05150708032d010b 71
    0x35078114010041c1410f03074200854400c401c680c94180519015410318404000541c80c0e0900044032004c503410454085e0074060208048501c0d19002e0302580c031030903040000141c07940c14605288001e44103008000758011051400c200d81d0419040140078952a110b01c2c4400030b079107002c0b817001d4102d0012030039008a009000704011803241d9400603c0d0661010b0710118208103901c5000c51108000e40100d0103684012080040307250b803501c034030840e044d00d0070030541008280c0b100c054070510015002420200300000020005007103014058034040000e40070007021081154020021407c101044001500041c0544103000050068000703a41c10040558501500c10007044100c2c5d0160401b12100ba4030340714000341050f01404410f01c00c02894402041110001080005481c0120034920500420800c20b01c00394850f140300b0020b54206a400010981d1444128515405800b00c001c0c46030340d0000030000115103000003032400076044140c0d06548042a442107040407824046c40d0b48040041c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 564788201 1250 564786951 564786953
    0x9120305010803090d11040e01061505070b06270702030d0b0a0506040b07020a03050a030513060201020a140a0c02090c04050a05010c030507030c030c0b040b0f06060a09150e06030123040203090307 86
    0x10b41c02800ba114410ba992900168006c0081801d0710103100314408641d48d079100800c011007915007140150010751a002e807609125598a403004031001c1c1c031140c05035000401568501d2120201d550404ca01120250175618040400070760703130350041c020b04103051f081c01201c40d85070400844034019284010542810981807e0f00c42c403d5030801e0f00c2c01c2c1e0340064420b0001022410610240200c00d01a541e07545c4d56103c004501c455a0b6010342c05441160310400c40d109000394003c80a04c40c4650a40c40c495603289040412502d02e04a01c1740a90700c094000144420f09146130010000c0ba8403d03035025114030f44c1d8500540702c024501901401144042021070700003441030205000c140e12a0034590511540e1391280404000215402c43e00e596000d0f050180784808205000da11280c03c880d050b141c130646210042c100c650910410f0340e071841c45961100042e0080024416440000c2d02d115280c0d13035680311449076420004d0303101e81d1181e50720074100b0b0142050b000312445260380d60002c43c0b5020007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 564789451 1250 564788201 564788209
    0x11030403021c020f13050f060a0302011d0a09141b27030a0f030e030f0609030930072c0402120708030a05072d170f0403060912030501080309 62
    0x180b100203d034801c82440d00701040b42d680041817001e801806000044626160007090300b0081e0141419103d108000740410050380d018000724981100e55554060a00c81d480c003046032000301d50010300d41c13a420604072030852a444c1600d94880c81c0c42074199811015200600901482141c10410301c0181e06a0f12010280e4192120700a80001508545840400742c454400c03510a981003280050074034003543d092846d00b0003014961039482c50203044203083c0080f040741da03071003000c0ca217a00403041c6140010301140350601c009401115940c00c81d900c1d040951003581c840c0700034012020704444450454900102144213001c500401034845600d586075038003041113007003295045141500c295400810300d000103001030328003805961501da45615980c43d09602c4c085200306414080d6404804100d0324220040015103903640015586210031420200b0303160b1407044a5440341c2d0003038006000800c105140d8410b1040b240120207080d8801400c0c201101540c0d000c3c401c00615a0080c0011101854 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 564790701 1250 564789451 564789499
    0x915021e070509191505010503160201020c01090807050708010b060301060e120d09151715030a0803130c140d0308060118030b01060801061404031b05031605011103040302 75
    0xc04035044a054940d1078001411103082103c0c607142504841c0145114000d0343d001e100c01d228422101c048042c3c2c1020b0000304203001c000e02c140344c2095250702c07145041e4001e50403661096000c00091003081c50303a09040201d0340c85010211007038419841c0006903a4410701c10300b6560800100001d203580d00e092012501449403001070390748184540140011800704011980700d04120347c0f1600c0d0b485203000e50000110226102c01c43c02e0002e60080c003101020300f030f8072266001443d00304816203404c00b00d0209140c80703e643e0006024500001c01c0c40541a07110141c060f000f0f1103480591401c58031000c40ca030311302c07045044540d000280320911000080c0600443d5900c500185410846c119000605d00c0f0040c24591098405409440041c06580e91202c030042c090708840c10b000ea0100c0410345410402d100f41d200c0035103040d4001004003006041c401140009000040444403d400c40d0b0710b0311070b0300454070320521740840c07040306200811100120a880440f034000303003c81d0042214075036070480a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 564791951 1250 564790701 564790753
    0x11101b0f141b1302070309030212031b2a1807031e0213080303060d0b15221436011b0f03110307120b03061501091502 52
    0x1e407407040d0400205100304030000701c00010342144140c020010040c03200440012219031070a500401080d008a03400038140310840b541595010703030014001e14564214010001c0c241d00031040e40e110084038080014144042590b880402c028413000300d41c0d000000c0b503810810071380080d6101e003aa4071911120070074580c003900fa42000300d00d04001004100180c80c3d400c20305004240e0200788200d50311071414030000541600700040d072941c00e229000544510360750300000d10325000b40300000c240c420030b4460041007000203404c10200c0072118603000400f155101c80036101519000400310b0907003003005024054130410240b1521443d086400d011645070141942c030403144180300f03000c06003509100b982590700300e10401e2811444082d40081104c07a4007030003e800c2504003100c80305c008201e4000c9a0b00000d6601b480b0526582c409001c201501d800900c02c0d0b0705004040030801009008201612084026600c40c0451a21a407841c0141b518074202000181d0205052020305101240c110b0b05103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 564793201 1250 564791951 564791963
    0x112030e060307230d060b040e13170d0603020f0a0315021e0703030504120c0809060c0a0204050c0301080c03061e1315060501030b01170402060306150711101b0f 71
    0x2d44500d000c8452a445900c500c44c904d030304c00540506606201d200e1440a070460200d824a001d140440104045401400413040d010b42e2001c40402c100c001c20b1404400c0d0420240c6503120f8007a0744c07084008203501c1c1f2090f80211803c60454800c0e10f01015030b8003e40382c0c04101444405a0b81b94000c009410843d060490038060101d518071a0b22001d0241c030001c1e00c00d84c0c1c04100c510306481c3c60050340c40000c05000034425081c51403000a450b04043e14a90482510142c0d2182284c3c03204a1a0001c0c5d102c001e50064940014001187c429400840c140c4098004031980e800c0b10f9428140d480d0400ca40400c48080c040c2e808440c210300c1010056080f0450342ca03294074805654070b5000094003860302c0e004401d40c9e00c040400055815014444100c4c4007400c0090306004c0c0510090110707000100000e10820f000000200c00360340d001000130300042c000b040b2544800b0145820f52410081140c10f52096410b5820100607510030b5403c640c1ca0342210a0410000e0601d42e91443c07440c4035070f401100c0c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 564794451 1250 564793201 564793217
    0x20d0e030f0709021803070621060e0a090b06030c0109030b04080f0c0706020c0f030a170f040603060906050a1d040f02100816050c030a0503060d0614010e0112030e060307 75
    0x1d14400c024101c0a00f010b90070050342c480e0140e01011110031441e0300301c0d01030f410241c410850b16800140c4c1c560410384030302d0185c0403010840b4541c401804241c1010005400b80011302696a0b415486803600c03a201c0ca9030080903855007001c241d521094032940a00103030120320140002800c1c1107030645c1081c0303c0c20b4a9410401142c0610702c00f50045040f004d03032a03000080810600341c0c108010018031105441143c0e80d02c491001080e12001c0c4640090289a0848100c801500d5030608480c058403a003000e082d183d0751203d0008010b400780d4403d50140d01d05000c0f011589160400414040f42c0c2582c06009416002c0c00710107020000041054403002000e054020140c2c0340c01080d00d000000a0303696091070700c0e111b441c40b59507900740c200010400406001c540d40c0c3c450300208890410007907042164582d5250400200c500d0b0405c0c9005100c10f0a1803180000c04841020040c189c1d901403401903070b20f03a01c41103100480d1155450180004000000c000040d0401000554001c4014984a01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 564795701 1250 564794451 564794473
    0xf011811120102071b090506010804080a0905030d0908060105060408030a08040302030f07060b03060a0903080105010e0a1a03061c0201020a08070807020904051c050309060c0a0c05060c0a0e01030903020d0e03 91
    0xb0880e04020307825030f28000100950b00c07214601880032000303041240020040d43c140403000a000b0740c0014402080c600c0000741c803282c03003401541c1100003080c0003001c9411440030120000e085516602c07072003915124501c0086002d02c0c3c200e09980645601800660a16040301e1040712085130190098003540020801d00c0c0c400316a5000902085018120124458140e0000d0500e01040103128845c3e480c40e005009000981c80f1503183d04548007445e02500c0740b540c840006641500b40e81c4400e04440c038045040c040e440009018600ca07031021900b00440260070302041100d0407101c00005e005070020580800041c0c54400640001401020540e041581c55408144c5449040da016501680b10714050209d000c900c1420200d0b0042d40e00d0810300b5410800911560341c40003070315480c5400c0380032555280d8540300f4498030010642207401c844d42030600450300b64045d4802124030b400500660b0344105d4079402800f13241185a456401040c401d03603070400441f03c092007106116030500034818051 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 564796951 1250 564795701 564795703
    0x31103031e01050121020f0c0f06061906140a0c050102070510181a181603170406050d0905100c08190608070909060207060507050901020f01181112 65
    0x600c205002005080055080d98544840d07410580c4403904124002c005408118241c10003034035648001e003005a01d40030b1400780301d01c03140580d218002d01c030300c035444014003a0b120025400f400750710140e404a402600d40300201e5004545030040001069805907024501103080006002c08003080c03030440d0722032030166503c4d400c1e684007010607605580070380181603006006214002070700c1c0c40044000001d600e5591424503c4101c3c44585c0f1401210b60006800100030a032090600e00d2000180c540e0300e092000a95031009072800251540b03984035a039071801c0d00240f02100d06031046602ca40d401e004a80d120312001d07204081c811900c500a00a44102941d424000d40300034003215100c00e0300e01e280205411220031107220200e030f4900e051410800040c4d0780490200305840b901c690104171011681444800313841a044010a81450503003001900d6038004080c01c03449900368281e580701e00c410031070b45080c0c41144d00411820780000c0c003000001036400f8030075420000d01608110050882030442 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 564798201 1250 564796951 564796957
    0x7090e0702031308030c15040602040f030c090f05102306040b04170a0b041e02030a0305030717061e0d0b01060509010f03050c1804021209010c0f030e03070f031103 72
    0x1a030090303800800d04000507001800010084c05081c40110308240704100d400366260f40c0d04440c00b24002c07000d8081003d100094040700c1c05070840c0c0d80d202d05902c4d52490b121007810700d1b611a00031068a01003020007021b000e4051140148070a5140d45400350034122854480b00c0c440351800302c980e1403004520000e488401c0500b000f031402c0700007251903900d4441034241c1c030303040501000301036080701d12144001415040100e03009a084604240400c003940c284041128103260042d44c10312032409518101584807001714440d08055461140d03210400c201008001000c0e01c21682c8425a0380c4c00c8655090138140d5204861001002040c01305503076202c1c4850113201713070445000503c00245552007541c0040000420210710300d0b081040745000410f1130b5190050903040100307010640c1c080c565940d41e54050743c0310180e010f00f0140d168203044422034020143c80b544000407496040c00424042d001e40705014210110382c2c0130703502d009120760710244640d06114003203090010300440ca550100e410406 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 564799451 1250 564798201 564798211
    0x10c082503080115110304152106050f0f0d060f11030a0501050a0608190f0e030319061205070302091e0405030306310b0f040f05040212010b1807090e 66
    0x6155000e5051002e0304640134102c103403000502040101c0024107001c000202c80c01c94aa02d401030300011420308041307524240d0301418065403031030752114880081d8203903c44021070f0b03c00c480d01a0740110400600c520344003004286035100000b419100003043c3c10790400b0088103420380000a04421011107041c00307400944942c0b10031540c1c1c100620450a2880b07190000d0075242c1059070b024903024524001040d542884c41c500652504208000e088aa4020200014183c01542e4903403030801c0c2c4181004a078000308004040c140030700094451568910308080c80d802030050407443d4256001d1090144000c0c02071008503224139551030f000142c040c219405030f0310900140d60303241882420480c544c2c100010310f800d01b035007001164005000b000490203000b1256000403940c0c01801d40090400d44610049641040c18807013210301c074200680c4003030701c900d208540f050303002109406801c1c01c8601c03502280c0e4110000c4442c41081400d048281341d8441d65034500074202a488131003043d1400800d40e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 564800701 1250 564799451 564799457
    0x1508010905010b0f060415050d050118060f080a02090c0d09080a02010b0108010501091401140f04030c0e042d06061d160909110c010c05041a040302010c082503 70
    0xc0040000030b00a10b200b8000442ea61803015840c0e000250942c45075114903101300759080c4503140490302030015a1200340040703404002c00c0d0381d02d0351b02c150740c84400300700518110302e0048041a44601911510141d540e680003c00f0282c40c00d609206100c034015040c504890b5050044910004160040741101e03841a080700f07484d103040d14406401d40e45141003c506100503030005020303e076404203054003204d5582c10007c01c035284850040c0d038041c0c1c1a0224101c00c0758001403520a11105100410031244114034541038566181013030030681c0c0342550b000f1300464201110b07029140c108000c802c007400100039404800388003951814101d42c02a44590502003496042c084a03800031346c003059000013002c41380e2142800b8003030024541c5480b0302030948030596440903000e889010006868464480c1e0000f001441e1048102600981252045049035001c501d60700500352480c0040d10120380e41a12490000003d40c0e50700000ca4125484022844c01924024000c0342c01c980c580309210350180e2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 564801951 1250 564800701 564800711
    0x90609050d05120f150301060806060120030d0e070806040c050a05060c06070f02010e01060e0103050d140307391106070f0f030201060308040b1c050c0d0f150801 71
    0x403500c5428005a400745209100041c0110000900d240403a59801000001410360564492a040d4044840c40589a80541c0b80c003d010680342070004100f402500709032251100034400c4460904c2d002c0c0200d0001e0701e25003040c0032200604203e40c001c0100c070004c40781076506054455198915000f0101c0b800d46101243c1c0b0b1007049181014080b10015000980e101403601d400d541c9003d9607860f001c0c08a800b006100c903140100d2034401c1d071103951003401d020001d00c01a907884044c0d005160084c0800d84280c000c1c0c5400d944014001c90700460189900c14446095949001003076900d20b2400d07084520440340348251441d06600c20f980807810141c00c1c10782d0a030715001402c03c151058a030309403031806a2001c00481021401100e03030482025030081217a040d035841c9207022405006140d100800d440300206002c2a205070702005400e09200001d0000025803540c034600098410669400e4150700d420400703620006915000032a064070352550114001e05007240d00c1000705c0e01540850041e035951 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 564803201 1250 564801951 564801953
    0x909021c080307120b010c020d0c1a1e19050a090f0806091b0a0509040f0f080304061a0906040f1d010b010809010b0f09040c0b0711010206100803032206090609 70
    0x2107201d130103072110700e100100601801500042c00c080c0c4d02120117481800944186d500300f040a460b0000038200c403840480110f914406441410341101d2021400d00540b8400e890084003160203445405004a200760808207001c0000c2d80c66604c00340034a0100000c81102145071240108507030000e11000c0000e021070b2505030000380c1840348e54602d0400412002c2d96454a603a1503441c603800b07994049504030101e440d1842d00009840310500020200c580c0d0506803030a00582c04051803042c0c0c003921085c05105414508518003403203e042280d4040030013030201f034480c106036006030300e11410000300160701c03c010141004d103400d017080351050a030345416150746a942e0003030f00141c0008440000f0b2112580100005904000184100780182d810030002018071142c3d21401000300704035116280e4401c09414407144200c000755849001d88145c80104941403030714001e040c121074100001d9401c42c2c40d96164400504070200e0030709941c55020a40c0b1004c12014425890043d2084031300007442101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 564804451 1250 564803201 564803207
    0x5031201061e08010e010b0a02010e07060309030917060a0903020f060c04060311130302010513150503160c03080f0703110f1206030321100914060a0503030a05040909021c080307 78
    0x8442e44008100007000108000341c41c50403030505403500c524607070381c446c100810100d005004078100746c130a41c403e04100050701c0741c0541c4803903a600d00960343c070401140c4901c500078a042d4100c038410a035900141c00103400f8245a44150490b0b403091060b40c1e82c0c2c10040fa1003500e400810b4944800204000030100100b80d010301c0740790140503840e4034150601801042e1038011a41920010f41030080c00150018120602d1030403402030411250248481c011000000f0101d03081113580b038611800341200118100d0140140504c110340c156142082035a5103100c0d040798240203440d00c0305040d102c03c8042040102c0b82d01501c100880e060700c290b02c0715800038248103101d001412090098000300902d0400c0740b5070b50380348111b800c580c4250418580350906070401d440341315030203100c8241c40c1254058081c00b00c0103030741e406002c0481c0c540e001079840d04101502c03441050030341c1021810801c000c200b04029508501d211500003040e82180c000e64034543c120040211404540c5d80d0400030030040090b0f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 564805701 1250 564804451 564804497
    0x4030c021f1e030b03061f1d10061403070c050c2706010806180403090b0403080a030f05131106071e0512070c0315060504020c010603020f0414010608040503120106 72
    0x4003d1405015001240002c42e44410000e041d140d0308203c0e003100ca03d003550b010740c00c640040102e036202080e554000500d4000c145d40a0350480381e210b41011001840703600c903030703844d070401c0340f10040c003c0c03942d141e9031300540d0340302d10103071003100c10340903011040440da518804181c103003420480742c26410b08202c0c83c3c91201204028041c40c144184030013400710a0312040d01e880d00342c1c51161b5440d9002c1d1218141680c0f406c0484e80821001000000c000c0200401c0e01d015100403521618140328180100d0504425610215a1080720500c20360241c00404c181704154011907401400321450130359107864001e0304c0882c002c107000303480c0d01c010b030080c040000410444007610101c640301414010240d4520800c80c49602c40984800380b052200754070b41d0556031116000301030042c4119540c01081454034003a021901c003d910562103040c0003072181c1014042c11074041840711016060360b0030202c054070802406042074865120074003040e0003420100e00414080c02050702c0701e00d8540700454a28039420 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 564806951 1250 564805701 564805757
    0x50303070308040f030c02030d0509040f0e0c010c0206130f05090903040302060a120e07151205060a05040207030504181413050706030506060c10061a07080304030c021f 74
    0x2a004010850200b5488207081e5000b80e07210350403100e8400c850400f150110600c3e00040d41c58020b114900d607126401000a100d203441c2130f1000e1100c0325411103544101d8000092105094025840c0c0c0d403070561042800c0c1c0510391000382480c4c01c088101048110b11402e5412038155003401c03c005000c02e190918005074003880315001185480e055a01203042030080e11201414407003a004d0380950b01c03102d50404450310950100302c40c16284d45800b43c51060241c1214840072440130010314103c183d0038003513a0310a080c0904240700d03035403614080c00000c0d40030300c0099003007090600c004182c9003814848411414503104000c1100082c4020000c2c680f04042c1c40d081107980d00d00b207040001480032403010101c0d18941000203483d555030000c16800e00c00c4e03800e1445c00d8000d120440c0d440b10000d90109094035503000b085501049000b250407040c1c801c0c04d034047c0190700280b001500103441000c2d20b180152001c0c8c000c2818100c00c00d08021600e0303200c0c9000d4040f528007204541d03c6c1204080882001d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 564808201 1250 564806951 564806953
    0x8030c0d03110c0c0d0f060903020109020906042003100f030f03020106060305040b04060905070b070309170a03090b0c1911010f05190503060d0804030b011d0c2a1f05010503 76
    0x20500c00f86482d55034070b5034259220300a4144a0300c9005214403104ea005031560800e805000851131890024004c01c5840c1d0100d00c00c9290b1781c040340b4182880d110320078a1038800c4400340340c14000100041c4a540001340100240c0d1062000418071950f00202d402c0103500c90030121014100304d00e0080c0c03c0d141c1d56004001054a01010080495204001150040e410550002e900d0f03502c0e007401d508000c0680c0082600060000c1c00c5020951700490100403159907080c03001c0514038045903652138442e40030300680022003080051211015541c020404135541404a410208400d800f60744c0801c0904410356a01e80d840603000e8455801541c070382c01d1748a00b4602140380c200b10b0420340d10113050580720f800c104040480000e0302e81e01c2e0030070040340440e000100c00f43c40c5c0d030303803884c2203c0c84000c00d0140b4980741c814124a103412602204500340141c003450301040c104480d002c03080c00c402d00c6014040e551003c400d020340b82c0088007404032594110a20f0001010ba00f904824002540c1c01a4015030003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 564809451 1250 564808201 564808207
    0xd08030a1a060a050d0e01061202040614090402100905090f040318060f050d060914100b030c1213060920030f060a0b06070605070f0e032a040608030c0d0311 69
    0x1da40d80600300c0c1d045980720308040307444026405d84400100301c00e00706000e2543ca050030129030124200318000449108590a004090725240b0a0480c158680103c80d0040c1c000c80200d001850445403902c43c2c0070061030703ca04010358800c00506250b9055440405217141c101c240000e050b03101c510031031100382a1045600f150b10b0110010300c195003c4495400f08400403c0323035014a480c6401c08001000b106030140308034114071456844012090340c11407981200d02100084102100c400c0d40d104e20b454140c0c1c1e03818040341c02d8403d845034400500c40c03101031a100012000186240c45102c08250040b07143d907484a00800800500707030b0b2003682141c480c2e0b101d401d121800d440b0020340746034000341d00c06000c42c100c0300d81e001140550081d00303401000c49e4144410414040c1d4041011840040380780c5e5410101c85d4018281501d605190b4000f081c21441180c40b941c21113100240d058400c480036000240c03081d03480c18000c1c1036400000400109800c41a039a002d0954540103c6940700942090707146 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 564810701 1250 564809451 564809501
    0xb04060e0403090603110c0109060212090703080f070305041503050610023415030e10020c1b03030c0f0c0901060f0816020c10020a26070204090507050d08030a 70
    0x3c0210824800c1c0400c05481c1c82400c0340d05410b810075117000145d000000d1140f88418680f03000a5045480150480c25007400060640000010243e040782d400080151601380c04005240156020143c1a010700c00c08100000e080c0f07682c8a21040301c85425034000400d400d0610810080d052203580c598115403025a0301d40000c103800c0101944020400c091828601202c0003542d0301d00d06607800525960b04a0081801064041c0c0095802040301d4042e0303008214051601d00c12801441e015004a40c8156003400101c2c114042e04205900c0003000c917400c20340804912031a101c0d151844e02030f81e0700000310742da000b800c000000e5070141600d130800360100070410800401030100208a0680d44000e2079040040b84c0c024844030800360030241510b0800c50600d90041e580e100101c0080b1461a5070b48020844c800c00411800c1400300c005800510300402074081101500c10484141c445005008000030540d8a00c0f84080c611885000e003e603c1e850074009043c119a904000504001c8410f02258 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 564811951 1250 564810701 564810707
    0x1005180a08150a090506042103060b070602070609081903060801020a0c030f050f0307031d280c080d0908100506030d050708120705030a0c050c07050d080f07060b04060e0403 76
    0x1602d42c00d10300104844668850507003001910744c1303007006049406801d080c00240320304000c0d1000c15500c2c4065508042c41d010000701c4c00c88001e489181c20300b840610a074000a8074075001041c41a0003454041107100b865101d0041582c080c904036105508541070000289805025032401494814000c60404c102c4a001038201020075500604000a904540c50740c94021401c0da0740c0490440405522847c01210140082c400341c04a64410850b5886900c0c0d840d070001983e1b036440030203d0498000c00340181c0c1210040042e8041210070034114040818510b100f08140c021008595171030880382844c0240d401d0031303c50342008020015007424200a01c0fa00c0000c0c0c803c10310780d07040c0351403959440182441c070100e014400b051184441c0c0c610601214540c0440910b0044500d4002000b680da07107240262110b2191340c0f40e15980c0e81200034108090700c0c21600060304a4040c0510900e030081038012806c895001c660100c40c0641d940c8200c41e980c0c00c00303100c0d9401809107041d07624071504242e1006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 564813201 1250 564811951 564811963
    0x40b150f0c101a0406080609070b0c010b0312070b010f081b040b040524010201021e070c0312180b0405180403030e0f1f051b0a0e1005180a08 62
    0x8500c68600020305082107070020062030000702d44140d420400144001110031062807500c001c00d205904000c2c02042d05039000c10402c0c0502c881400418103146041c4410425070001e0800300002c0d50391304081241501c06020300c1314401c0021017441d0383c0c0e40d128070303004200c2001038214003440d080002052049210018075021504840300b20f041d210482440010080c0400c5209190080d04040c01d0102090340503a480c8030700324200c0426202c060711031004a0807030040103030740381d001600c00c140c1e0301e0b5202c1100000e00c135440c0100b5100b20841d0303c1f134485044074006003205900217032402000d4600350442e602120041d1400c805440d03c0c085c40c0c080083e9038007001c192000c403070114290200d0109030007503108110680880c0c060310440c0c4003195209407689084400300c42064600c1e054510701c203105100702489006040c9100e848003c0221501d109600400d000078240b0a1442130104e00795140d01900c090601203a44003580c51154801a500684801c5030085c0100040881800100400706d84 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 564814451 1250 564813201 564813217
    0x80f0a1209060f0e0d1e1a070504050d140d0f02060109140408090a030204060f030213020405010c0b1b03010b0301180605010e0415120b07022a01032315040b15 70
    0x2006007000907200244591178030304c0c402004543c0714003039030380c0f640c82881c00d075091b86000d64203019015103106641c00380c2c0d00085445000040041206000b0791070004441c051040c029065841400b0080500c6440c1050050803100810501603900034074641c100302d440d02502c1484828441d21200c50320310f5079210b0018100804040c800b095044a903200d880c06540110740040003840400c0d070b01c904480c030688107400240d000d851016402110300c4041c0c02103804640043c2e441c000c40100584940725405000751121400511907100030354640302e00d4000e90f003c2c28800c1002d50b60395160441400301e01c43c4d110f00c40c00c1360034188241004180e8214582d0560704034107842c089403d00c4c4845107079807c0905508041d40c5000d0510808041c07220008801e88140d082c2d07000c407a86101c1e00403d101c00080c03950744805c01e01449001c581c615500c070350072a044106000c411060640459446000070342c008445000c840509044004d01524090043d040c8405090729001c0d1150041c40c0412800e10a19031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 564815701 1250 564814451 564814457
    0xa080f060a0b06070215031b120a0b1c0c050a05090f0a0b030c0301090807060b03061012210c0308071103070609111305010e0a05011202040b0307080f0a1209060f 71
    0x1400700702c0303920b83c14100d900055000b03101c0310400038840d1104031303180c1040d20612004501410381d6600c1d00400c03400c4600840507480442610390301c809440000d45502c0c203255070440c40c2440d09030110001c41c2d4240381c20a00c00c2c0c804a5032035040c00144404500305922041c8a00c61040511441c504942181ca400012540f0b011030081e0300d00000c2807508181a0507550558030f03001e10030b070901c688500034209541c420a020320020030b880301015581d00c400d482840c0c02451044042006898200140150b0703072040c42d454103001d49070403101d065548a001d10001107283c0741600b0b02010351106038568000380a003444e00d9120386203103025540f07000c1c11300c0041285649940c03403014031403c406080321120009241c1080c817021460010701820080c440d0040050210700403511070300041c05010305950361103501820680443e000c100203009003450154140c0100c030400b19205505100c03002d84000d9650081caaa0031407454545080107030300315810b08010801d01c0500081e68081100924800649 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 564816951 1250 564815701 564815711
    0x14010e101d0a080f010f06050f01050d180204050114010216120b060d0503042306030c090d020d06050a0209010e03060601021504030306080316030f080c0f0706020f0c03090a080f060a 80
    0x300c040b4545070090b0300310201d40c0c842c032204410740000540160000400003413042c44075503910340034450000f5903070720558007250051183c50b0b184001ca50101c032031000200c40d4141e805c41c007500403504952003a00580c204108417a0300ca48a0b50b010031112044030300c12451a01402d28004807030550182001000742006502404600300d40d40380413440b00040d80040075a0717501c0d9a1404050584801815511b0b204284112040c031280f4005090f00d01c201c1c8080c500e189004400030420100c1c40c40c48008030b90004201d001100810707418410140700e07402d640001681d9125910025003c000d080304031500c6544036078100040c0e43d85c0815540f040340d01c03807800801319427207030310301540a40304039000f1a84910001c24150b0780c40031021151281c840c0031b5180c1c08960458540c04607411031080b00c40d600d85175010415544541c1e0014000c040c80360203050010b0070100540341c1e000c0e1503406500b402c030060b8000300b4810b0a6250680201d4020174510004286012659560a498850003042d00207195999 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 564818201 1250 564816951 564817007
    0x20a180f1211100816020d080106050d0f050702100609060b04030201080c160f1211060705180d230703050a1b05060d05071b030c0b09011514010e10 65
    0x100700c1c240c2c00548018040003100b000d119000f031104a0440b1408111000c0c481d00424041c00840e2130f108000c605d41c0d41c1c020300e03801d06200b510254003003804100f1060b521080070346060441d102c2c46004541c15400b40010f1802c041c101c00a0755644d13040031620602e4032800308041c0e400c00d811036089903820b08140200741e8862004074214010000b81c2c1e021091100124020002000c00d130070b6a5500c3f030140d40d01c0800404004030350a0130084420000382d8441d07004542403a004c0c402070440c1b514455404078103201d480004c2144040a0401101d80d18014a5444e81020840d6642c0020b200d900006101e00d5103161207680c2d440b504000c0280c0089a141d00b0f60b10418a2504008094100608401c0d59091007081e000002c20044405c071001848464100708954500d100541625400d9511042e1444150300c1e00c0b83e11641c0900041002d65a80c5030380b014865410b1640d90003041c030400c640c03420f5001c0c000090000d103640c11101d8030408414001d1b1241c160018410045184194038078100c070508 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 564819451 1250 564818201 564818213
    0x809060c160b18100203010303181230081e07120e0c0405090c040b040b0303070b150d0804031406010506070605040201410a02120a0509040906020a180f12 68
    0x58181d050000c0c084d82d900c0e00601032680d0010760403a07200e5903405021489011030300364001454015104480c0d8201c00c00300c045810074200c80c0c1c0f142000380c03046000c42001b40303810852a41111034200031030000c20420100c14005000c0c0d05904440c54070050480c40c0481c40142101c01c407041d180c40480e6680250f00ca400c20130010303100e04a10150080045080c95050745640d140d918226910807030416249801608240c0569040124080c0055081680c1d40d51001c1011500038000d44104040160100b580d583e070752050981907000310400387c3d45600314182060b1513800350700c010b0042c0d40610010440394861004603081c1c1d580240700090552100d1004132100140341881c1004070281c11051aa00345610100d10030700005110094031685a41d9002d01d12409042e44460158102400003500c01000c200200250490b62828620744161540084c04071002c046043c1d0301c00343e001c00c1310b0781250340004000c1040614210403c0060740f074480c0c410340c0c0da041c0b806190586440300341080c040010b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 564820701 1250 564819451 564819481
    0x60109230a090503030a1d01110d0e030d05040305042301090611010216030305160206060630090a150b0307050f060f030405030903010b01110c0409080d09030809060c160b 75
    0x5403060940382d4a0800301b07000b0016200e01c400d6600f200b402104520341b03400c8148140348101103095146810040c0701c0c00078000928000402c000303180410000050030130018801d0a1240d440b076151207450302e04001d8004602401c6440c1c1c010810706218844449a801040113021282e45180290b598450031042a002e030040703a451480380310000989404154141c0c129a109005a8050001c40401008100e035288000e4032004d400400400c181820004090340c40300c0c1444070b1140181641c051180e400da00030340229000a000d8019031410405c0140038103801c04145001002804100d410304e000030307221100c91007a01d01c10000b60b90000400d44480064800d140300d14a402502d81c500780c100292070354000e502da14820f52030f0020505c440e40c000d09036456641c91000061a4508074071042c403008240d8220140c1d445101406a101508254000d61910034030a50343d07000242002d181182c0b4059019000c0081072005000e658403004c22208007480890f0002101c3c111034a4100c2d102c1c01070340e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 564821951 1250 564820701 564820703
    0x50906041103160e0109062c030f01021215030607121d03070605010e040c0b0c1018030f1e03180212030301060e060711120c04060603060305060109230a09 68
    0x940080100558121900c01a120200f80c07521482c2c40101c14900448022004d40104004909108008860130030011440341a0f21481c06049041d101c43c5000a8904140046018490780d000a0340d201c03195080c10070344d034100b407180c0c24000d03c0c1c2c0011800245c031010000d180c1820044005c80200c07c5074066003003140048038940201e0200c00809070071030307126440f0403416139049003008000111310100490251003190042842121107091032110010740d80f225211745103510441104032105000d41c8280c02c400490b44210151080c101d16015103d40c121561080a0000d2102c5e37001d1081204060210f40d50b400e0325001a07403002d4545c80d10014500004041d41004001e5004100b071b42e40007008505880b010303218511910722810030000d0340c1c411030320010403180714840020100d06102c00682018241c03030042d030f071069800710081421112541d12400000fa190fa00030000d1160600130b2a0140503114000d000c086d46e10050b0748c1c4250303402d01041c100f40401310009240c0d003009500480c0d0720f03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 564823201 1250 564821951 564821981
    0x807150c201e030c0111040e0412020c0402030c0d0e0109020105160c0b030a0207031710150c150510050312120601050d1e0c02030a14030c1612020c0d05060105090604 73
    0x840042e9002580c0c84e000204012010f61038054150f540091a41c1030700c044030302d22401e500311a900c0303544000542100220301415442075009003400303541e0700c0c0040c40c8550395035100d550b1a5107113620b82409440980c2444001e43e4544144c040c00340c0d031720101b140d6040b139410540694000d8a481c141c06c0c0c00340c42e540031152001c0b002c0103200340008250010003849002e992090414460015034400082c400d0f107030031400c070920250821280021013281f14051150342480c900812080d06d03000d000c281e105019210807641d80e4204000700f4010744000020340001e034028905980512242c1c0c60742d115100c1e8441080071070000003031003688035104480c48920900d13000c0c070825590b01c05a0b0315110380c0314407000182e418010b18013034261000046e1500940640c0da0840010041d031701060242d8001b41908140010800506440e00c0c0c426140e00120740c41b9000041d44583c0ca0f00009040c24170b0305012601c1816007015440202e40001115419a40c0071100145252200000500180000c902d50040c3e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 564824451 1250 564823201 564823243
    0x6110f030103050d08010f080607080a06080105070315080d081807080a1b05090c0d1d0109030801081509061503100e0d020607091a0313020a030807150c20 68
    0x100301004c9240d000f00c0e109515010002e90300c441c03401400c1c0d030850060401c96030204e40010511072241c801d181d0007460942c40010202d44907820b0500b5503400302c50010100340c45900401c420480f0584a81c000d060784009004003041c081c600600461002d051140d43c224260303004a001d00041c014a0000c0101004a8460b10000d01c0d001d441c500c40d43c0c420f0354002240c00c800091501740500524480d001605e40309140c1b01c505107418004080000d0b80c0800c9201c160b0f04503001c06000d20076010740341d0098030f840344a50716016005140c5400d806000028081480602916050018145400c00219042d802d45450b0034004a8a0031a900c02e403e101141071166030300c040603000c605400030710302943c2510101d6075510401e40c3d50105900c5005640d0007025a5510014148806985c00c050601100806c3d5021a000510803060940003515001c000091502c2001100c030300882c4410602c1c0c0052280e5840d81c040680b0003164808680c048121058641e607990707900b80648069602c404200503a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 564825701 1250 564824451 564824453
    0x3190e12040e100803070210030c0c0c1716080307020904080d060f090c020d08150f060a030204180c051e0d09151107110f0102031201080a060f150306110f030103 71
    0x140d0b190aa070340c01200004048045a40c600100858004a401805400f030511485e20110020b000902ca888100109100417a0010300c0d000d03804030040400000d00304006085801032424216150381c941084180f2940c1088001c50102c10b0300d900da501100c12a6a079507542c1410300c164420040e0308200c12340f8003440854905140b0603030005441421004128186108605a9440000c6030045010a01440016042c1c4c010445803000d0b444d07000d005010b07194101404035406030405c600c0300c5c01207600401c051003456403030f424a041d0a10340400501100780007100c0509144200d0300b40c04038031240b100e031004144829404440c3c84001d00704040014410030305042d80000385902103078144a0800403048000d0300082e064a271003641045010400c96880e5003002400c148018405040d8082482819000c0500d42103072030080c0040805884086c0040c504102201c0030302101480b9189094a10f0405191201804081c0c951011000500705090704205501d070180b002a10b04c0c0000000001c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 564826951 1250 564825701 564825719
    0x11a1b0106090c0201050f011a041a0904050f0118110c030711010807090305030d090302010e060916050406031509030e03010e0114010e09060712180302030903100203190e1204 77
    0x400329505002d0801c440300503c28101d00340c3d10180d5071001407034505001480403000c8080048101c0041001c0303985000c1d0380740740102100c84040a480071861000c2601401ea050501030154001041e9030400c020303604104400d800c20031511180b040d02c0340e8034481181e04980c2901182d0040440300704132070311501c2c0c61a151000d500040b01840c001070100c40826042c0b80208035070070035203910501031410080007401c144020141400164110341d00c0d0940b401c1c4500003400340d1030050f03d010340070700000b100103000c03c0c8110070668401d81c0658030305241040413980e4036000030308400786640301062003079144c05c3c112102001030041550551170b20f070204958110550064101c080344a00364110b03a80da40420004038601150400c10a40044001400300b9100355408805e100588800003050b0750006400c002e55140f03000e080380036030b00000301d4102d1403404104051040300c100605516514190031040365040b41842d207040d00f15100c03801070104030000e00c4111202d40580d0b9141c0e4480750794040790 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 564828201 1250 564826951 564826961
    0x1e0c0c09090a060b01300b03010b010905011101061a0d110901050901032316080603010908030f0a110a0504050306250f0201090b27010606090308220b090a120b011a1b01 74
    0x210301c6c0d80d00e4a148603850b82010702814428607416150440b4440c0340000640e503030404644801207555aa483c080f45054104840c10144104051280c0d100c0c3c15081e2420100c03400340c3c0c60100c85460030b201060313082e80d015003100c024030000c2c81c0208014200365510340307070401c52030180840000076600700200c02001540407201035859030340d418465211281414201c0d0300407030024240031000c100003094515403c2c1d00c641c2041f8039038000140000e01c03100e090202d030080801e100008800180c10003051804100711900304c0710310041e600e000e107209244181465816158042404030420700f0200081c002c1d44030728011600111000c142e4904202e540c0c88250200c000030907000f003543d000311040001407142c0000c0e1115500c40d01805819131b00c0d601d2154000001545c000043c001100110a03100388a01c0c0c02020741c00001c1e0303203a0200208100000e02640c002161542c46801210045024a01c500e811242501c541040c040140f04030703020700e8410340103441e403415800781007110141015401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 564829451 1250 564828201 564828287
    0x150c1502091806060f0f07050d020105060915030c040b040f0f09020a1205030906090a0b0a0801090501150215060d1a040302060f0f0414031e0c0c09090a060b01 70
    0x40305080200d103848282c2e40c1c080540e40150030810030b10507010034094600c01440200705a1140d50f007411819034545213080701c080c03401c60060351600140702903810701080d12500904901c0142440700020008a0340d40e001c0c1000c2544116103c90f103407201c40e00c0b580d1000761560303018001400b8182c1500c0c1c51002806030160b0880c083c4811032070001d44c024010309080400307944a400345181070100381c2000000d070041d44150307612030740d000703800a8950000b0b03004205903000c03500c40761039643c9804944412188141c0c03044100e44092075003004460b42c007141041e2002246102c42030345894440105180300c200800c0100f4184000018690070100094454810b80c0709500300d98543d80c0310001410b00460554124440d2050000880c000903803903000b64002c200c100c03046a043c20100c01200480103405a01003c48200006d1001d01030001441003818847c41034480050a00f000c810325542e4548a40000d4211580c9070201e4000d68840d9080081c141000e100712501c400002c802c0c048403c40c0001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 564830701 1250 564829451 564829459
    0x2210411120f120c0709200301080d03150b0a03091104060338040b06010c060f020403020f040b01080601050c010b04062303060103080306130f05090c1c020901150c150209 75
    0x804002e02d00710314102d0b200c09503000080c0c101c480c46d20040c400a807401200c00383d040b0b41c4080a12140c610003001542c024004500245004514540050221608488000c90030a1401030078050031700b4120498015000d80d00e0001250300480c10300c82112204081ca0b503a00904141c000414030810380c081050692582150465281c1840b10b18a216042302c1164840b69080c00001000f0802c04048035900c103506040c0907100014694510044a21003840d03050002ea002c9010300940c00d00b519104507200080d1010443c0551950028000c05401090b142c104040042c0302000131800b0742103041c0084006d03009224081c0c032130b21030b001c0784804005039800704000009a00f00d80e10b00018058102d0340c000f01300d145141c84490500032004081004110b20385d855441d1040d0b045814450203108242d894060240f642100c41040502c090950121100145810b548009a03682c5241350f411207200c032102034103140d080803040ea62074034102000b44c905081029a425035001c2900200b00da0b0400311 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 564831951 1250 564830701 564830713
    0x80c0d060b1303170c060c0307050705010e061603060308032208360d060c03020408070e0f07170c0a0c05060708061f080606180a03031101060902210411120f 69
    0xc4c030a2907a80542c0201d40090f43c4280d000c524a00d80714802142c1100451906d04d19084482d04e07924299030b045800e400a41d8800000c114a00e105002650070380007181c42d082c4002491a100c0d039090b0301024010f880440314045510501d54240d850011300c0740d5001c6001912072030720150071f058502070a84440c0e100c440129041c00f505420003010001004018100c1d25070382e0150301d48900070700c000d036500b1003031542c00c10000c00c00c44000c004442c000c00e03001100158174584102c100b803c4050180008003070045040916403803540c00c081540c0e2100c034155010303446004041d402c49040301c4040018080d400f5800600016541c4988800e210f40c9007030341d035284660700300681035009082c1d003505640040c0240e00401c600745008001007014000710780d1181040505080010b0410100d80d0040300419102d54415651920a000c0d840c000c1882c05000c50919030740b00311503c03010301e080c2174802c44081400d00050421000202030060442c0141c507009428030341402e602da480c1c07144008000c0c40e00c601 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 564833201 1250 564831951 564831983
    0xc070b0c190c0b04030305040611040f150f02060103170f1c1406030c04050a0e01050f040506090601142103040f0e091915090204111b060106080c0d060b1303 69
    0x1c0d003480005641d10400002080d84d5580f406c030010040034004507221500c0380180c156943c1d84001400c0504050080803440e24508100107180d0140300f07658405200d00200c889031350b240c0215505045035000848031501d0821040203064038032692602152422000c64060354064180000300701110782041c003001b08040c03a814281040701e003201c0881d8194002d003142a45801c203a0040d641250700c04802184201b4a08070982c292001202e040b624000280c04000c14070800304440b80e080848407001e40019414800e003070040315100c0603100e0080c520703007004038550a14810010348480c03451060300c0d140e039290302d90019000ca03603118554030706142d040841d4223104045800440b0582000000300300784076564400f2823681e00f60a0000303103156656034060140e1120700940c405181d66000060380d0703100b0680a628000c0e04011021071581c8441c0042c403080d03801c0034030650050404914a0b803100c0e03910400c0c1018050a4100030000c04c0c0219041035082088440716064038411112080707a810340c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 564834451 1250 564833201 564833207
    0x1706310b010602100905071203020c09090c01080a09030504090b0d050a030207060f0302030f1b120c07140c031e0109210f110a030c03090b0c060108070902070b0a050c070b0c19 77
    0x171300ca03010300303650007119080142d044a000044001e42c81303401a02c0c09410004002210010126045031030b40d00300ca80402c10320340c0e0111019903c0313011160200030758000c1e51001801c5000328081c4402403603850324501c03c641d0720003090742042c42d0321408848004d0950b1034000d4840e4101d00c6001c0118907014000f040701d41c000d0095900c104600d010442c074503641c41c0340c13049854070441a0034000324000c106070551250b0407544e5920848001075007035502c000a1416040071610641c85d83c072a5000720301c500c0480d83d404205010003c80079598030348544500b16815006103130700000201849400001107c18908555412040e9101d40d00e401091184025040e0b03810701c54040000542d0b005500030000103801002c02d419002c0c02482c0c14072101e500c508151515070700803031503168107600450040202420402411000e00915081035007841c500341d6664004980c050b0003520000d440c0c1000030311500d190000e44115a80103101083e003801c0850f00e00308903501890810041d4090400503c0180380 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 564835701 1250 564834451 564834461
    0x20105070818010e0d020f15040b1219060806070c0203240402100311120910021c0510060e04020f0f2206021f05071215050a1706310b01060210 63
    0x14010701418900301f041000c21200035070107200790900340c200f1311000c160202d8900240c80c006044050003e4103042100c4010718800314200c5840e803aa0900f42c0c1403058000103c0c00315040927030750808020303078582031000a0070200f01c0d4008030b0381000c4400391800c1c0000304141d510300450080c0c44a0001e445444000c82c02e40d078002c2c8540400840c01c020f01c1c1c20800200032566440040081a01d1414000e0319801003a6130102104d02801d03c12102d0109044c03c0c540720307071a081404414586102450030b07002402801501c5840c80c441ca0740030403904010024002241c9000040740c501990b01c0c1200c2d81c00000c0503500c1d40c580c0c20741d607002c00c0010603614000110b038048591030a4050541e035206041c1c2c1c40c05010000c00c11400c01551001307184032076520340280b904080c07101002808480c04c0c2010b000703044040780d100c04030104032140a000c01d960041003c42e00a01e5a008610300440e2145052100001a8502d55004c04618030030b03c040c0b1040ac0c80380c6050354103d03401c0d90700d181e003a0303242101618 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 564836951 1250 564835701 564835703
    0x30a09120f12020a060c08091b0a0504020a09050a030614151c05010b221a0d020108040c031b050a081f0506031e01140105010f080601050304020105070818010e0d 71
    0x703800060103011a9411488400003a11481142d03481e2203190f03035030f506840c5214211004a0206418000d18210030b01100a040605000010305605203c002591010b43c910800e405076500180c0445014420100396014040107000c0c01509662454000010000d08400d40003503d8030401045080b21a80200e1003025001411140f91110a101158007007030014021038180d0341e1950003103040c2d00c0b03844601c1c01500113200c8a8500803500403d01090f1000300840000d00d1840010b070f10280e5442200d07600d01c894084ca80500c8540e0b0b549071010b018001904040c142019a503200c0c801a4501650f0806441080d41e0a0103060703542c84115a40b003109040f0350280344008103883e5200030088c0d01580e8403a000404903849060005424404104514610440c03651508003040c01c1e112030900f040c0c0140001e1a00d40c00198030b5207030081110401034403150410078004003060941e8881d00a84840f2504100f8150780e4280c848c1c1418449aa64078402e404540d03845101c4005141010080e02e1407 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 564838201 1250 564836951 564836963
    0x10c081006080c09040507030e0714011b111c020a060807050d09031e0503060414091507090f0b0315040e0d0302030606211008120f0c011b02030a0912 66
    0x310708200d0140d581420052500d01072400900c090a030b1030380c0340c0c000d95005414540b000994284800c50702801c24145030812100c20030151a2039040383d901400c5400b0803e00c00f5240080030201c0d2411441e40400348100c6a800515409144880200406c40f985030790310880310a000150b641100703031600e400c02c44404001c108184280020110160488a031030b601c00e1510507011420407050346001c041c0328200500003a0007004014080c181031150403014103a0308155005403601705c072120b580300180300c1d4485007002e011006c80c001318012004203000c1c01030010314940c240d8036880348580303e42003103542110b1441031800f201e0080c1001d210760b001071003014028200700380540794142c0c0a98409800c140d00702204025900d00c14841e0303040404002c29806214070181084921407007900d002c1d401c90542034004c1c000c50700d0f0320040300007200d0005010b00b51540e1900320381c42c1c10702c1c010300d00304446800381d18040c01d0110085a020005140144541e00d07050880354a51045131203107051203c0003010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 564839451 1250 564838201 564838231
    0x602070e0103020d0f17040f140d030c051f020a02010b0d080406030b0a09060801050402121906090206090a0902040501031a24210f0601020115170313120203010c08 72
    0x5404c0118402080d18001c85c07920003607a48540e1201c1402840303502030441404040b50a00c040003103064035800400c410051221800c1046c0005172001c2c0108030020140800c0c1044081000000d00200040301ca100d200d402c0f2499402820601a50100b0304860040d4604619404540703000d10b8000031143e0018003880c1001d0404509400811401521585c4a0220f90380010300c02c1103801801c01800844002140324101881448034101200f2101c52442d0011014218a15609141201140d41001c2d0105110310741c1d001261482c8a4110000d030814459000801c0740c460640040048410030398040004411704080c20042d00c001c90100f0780e00410019a11404400c45101072030300b0742c0e900388401e14154814070084d10045010300100c141802d40400c20034210b1403105950303032140d001c0c002480455a040b0301c0840b0052103003e1001081801c007000304100d0300400035119407a00d4000400c07601500c9032030328110707855654004c910075030070582c4034401d00b40704150290150350003d10303040c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 564840701 1250 564839451 564839453
    0x907020d091e081e190305071203020705010509010504050c0d0b0c0a02010b10021b0105212e03050601060f02031213061e1116150e0a050f01060602070e0103 69
    0x4074601007515502e0100b0500c2008958800c0a01a44401c840622030400180c440c1c0d213000c50030007400c400460ba503500090b0b10380d03001c02e0f002070484940ba0f5000444040301004170600360024050700c031001d4900e40c40e240070000c007100705520540c01346026104032050500c40c8000c108404a140d1401080e03900c42c1c0c1c000ca0f10180200010f00380b51a10f07400041782c003140060201e440130a404582c94010b030304c404a80700c0007419141148030607038400e18100346064200000040c18a44201701e09226030640000141c086052181d1000354403501c2021406602028612403170390b00c0e65000c16111070045000004000d4015522a0304d1802c1c26006982000b07841c020800301e41000a24a545582070303100080006406441022901c4120343c180b60724054241040f9401c6542030304550b00030350002c00840300e034451608034180050ba0b2002c10714480040c41c0211030082d02c50321812803900c0c4075119940c0704000e03001c12100315291403800200a0641e450314202d0f0768908602c6019043d00100d00140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 564841951 1250 564840701 564840719
    0x510150c0209150603070504090506040510030201120b15040906120b01050d5714010c060c02030406020f060f07050a021c050a09060518090405100501080c0907020d09 73
    0xa510043da5801d01d650340b48101c0205a0980c811a219030014000160520aa064510503190048400c0c0c500f00102d20340714600d0b00c0c0e000d28500000e414000c20151000a090480d082021609000303040e1240c2898044441102c0d50024010f42e210389090a501081d00e4084100c0d1004964221a4220190b442c25051100c503480322081a40c034103480b50f103c040c098000005220602480c042d48171880c6040011014503900c0080c1c284148056004a1241c03820002000d4400d13150384840c10450f910f02140140c46225100384020405414000c0c0c0340216178000c00039200b1940300d43c0a442d480742020841a4076583c040b5031545028508501080c0c0c0d0394400c00190101243d21b00443d00781010b003111204045240d6800e0302d000980001d541d1400e6903002c0d9000b0020143c2d42885800c1450303110045082c010700300c001074003400380e0380000b50501404002154030601001010000c0b961125800c0c0c3e250b40304502014000c00c0034102081c0c840784002003140e5070074000d5a1b4000090300f454a00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 564843201 1250 564841951 564841969
    0x1021207110102101b09050d030c060209030f0109050105040506010b0f030708060d02030118020a0b070521040e0a0c0311040e18100e1c030b0a09020f0403150510150c02 74
    0x1071411486452a40914640584241c4446850000b9001481c05007120000e290408a4021074020030701c01317080c0c100007508900e112401c240c3c010b0015884503d5000420724207841e074002c0102c90b6080c01407800a014066200138003542c003400a540c200c0c0e0b00c0310042d200a01c00c3c0e2501d04104441000040c0c1e8051140c55440c0e040300d4000d05003d502041500001d0940384600140c41125000040500440c5000c458400042c07038a00801414030342c194441540f14901d46c90303c40d0440f8600e15446004903141c10864010304080c295008490910007400b1006189510101c0c3c042494100880c20102a18094808503002e5411510b400d0350f41090010021408003020038852241407000307a0313420310034000c03292300800e400014581c09035010b80c00c46200e412085a0b0081c145009190180e580329401c06006958000034050b96800c80340c103c2510602c034aa00150201189040340d183d0001140c020038043c1c1485040c0d50070040c0c0301c4032441130320440d40c80c0407400305118080c0307c4010b041440e0a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 564844451 1250 564843201 564843233
    0x108100501052101020f03040503030f01170a061a0a0f090b01020c13090303060510020a11040b0906090702070806190b0a0602100b0f03030403061b11070b0d0e121801021207 76
    0x150400c0c1e1b010070255901d8009072030440c3c0d650004810014504001124036004040c0c0c41c440305c0c2030040106505032a4200d00d40050302da180c4501e01020020200c4004164295016041640c0d16070744000300d0714403000c14001ca04080341020301e6140c0380e40c8001148030003000c0c000d0040324199a030702208401000d42030411014552200c00000d60345c0e0304e1400e005800c9119402038040383c2d01910344152a40d5540401601c900d15103605c450050300c40c040c2c01503100c0300640d0321110035250f959013a4504512940940c0ea607101d000d08101c92050403107207007404045c80070740520405107190b04200400c0528003c81300181d02415201903420080c0c0c00c00852810f0280c0450200e0326210003107402d60b480f5030820354060391125000c120101521901c80c1c42d046842c5482c03907000c440095003548a028610440000301c0c0003150690203601e440c4e100402c4d5044070422500810703103130b0840d40c2c40f9406c0100604d940e207100070251182075001040c5505851712031070402e86042e0b0a07a407211030f01030b95200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 564845701 1250 564844451 564844453
    0x1a070210020c120a2324011401110616021c3516120501090c170103030815040b0414040b01060302040e040206220b0405030d050702030c0108070216060801081005010521 74
    0x1d540344030103005280703034486d100e0720207011010341c18000c44c101504551500325042181c004421f81310700e50302068154100b914041d503d0010600e042013246070a04e0301a4181c00780d403030710011580300c60f0043c1180056220310003042121048c246441d031300805001115000782c1040b40b00151145110786101c2603544c1c251706105840c0e101e80819101102c100340c0085202a0740c1e0302900c6002904501100204418403258011a60554ac2c00030f01c600c001800d100a411000b00f458a517941d20b5070040142c404010b0b100b007101012048a00000c46400e48068402c18010790011410740c1c0711f8005c54064803a01c01580d1450380340c071390030320445d90b105455a004403030b5600ba0120308906011204c1e401860390003080c0b501c60b42804105800d2485040b500e4050102c10400000162400b244020034400300b401c080d07005580f4000b00307900f0b00c0d00000751451000e0101501203803589e0841d03c69070580b803121046820000420000034202e680c2030040303c1d81b0000300d507403044008a45055482ca2092020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 564846951 1250 564845701 564845713
    0x11a030a0210140d0b121903180b030408070b0702030309120702190b0d06090903080a050a20070b0108012f04092c0105040201091a070210020c120a23 66
    0x1550310042d42001c1d20020f64191a546421040d240c0014100c00203902e440107003404041c0c1c40307d03240c0302c00c0d04400c000b1309000c0ca0204010340355007444480030040400c0141c0303658a00d8680380c002d803694031906080b03031100442004035489610000c19644501100e00051034181c1c10501d071054982c002c240700302e92084041c0c82188030b40049460700b800400715070400c207032a02d014451580a5551b00c2d0410b02c00070f4a003031407500c08254800e41d06901310040110000e40c5445419045c1d0203010510503851440c21501019401c941c8140020000c031401134401c4159070b600c8100490990f40c0e4000800f4000507408134030800406044c13080111019900000c2e460a40d030b606580c0180d400018101601614140ea80c0309800c0300781c2c503480306200d0508001c02c03517440d00f071740042c2100300030f4096684818083c0c100c50a040c41014100c4991580003469030000e5205444001e5582e4040c0c4035480c0030b084045040c2c5c1990300009034414405074020718000640020002080d1008202603140200303100f00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 564848201 1250 564846951 564846977
    0xb1207021e10090f12020606030f03030c03070c021c050d0e040209280e0c03043e0307030215030604110715020306220c020c06040b3117011a030a0210 66
    0x20212100b0080646c010340054a841020541401c00c00980880c4a030030400421414400d01001c607948550a414560103000c503500102d12041803d010f0494401049090401402000591080341464643e0341101c25100041808241c1c0100300085810115140c0785071440321300d5039a500d00e038040c0580c0c2354950b0ba50fa00e09044201c0419142600621000001c0c0300074030101c804864458060042c03020145410a1988102600c0d0085640800e00e45001050400d503410f110b0304004580091004201c101c003140260120b6005845041c800c520b011906808124076409a8400a4004081807030054035582d90001a500051540354061101c0d0004c100e410340848640f00d0b01c60081c1d1001414071500c2001924200450b50702501c206414030040000340c0082044442c00780c8000715400f1458403116003001040700a040d01900c22182003404103041c0d100561041c2c02480f034070000e101501c51020746060000d14400080e825800030750291002d4144505100600a26032800c5407001e201 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 564849451 1250 564848201 564848213
    0x70b061512010b0705011508060403080916080102130602060903030a090203010b090a0e07240c0c050a2d0b2215120e03090321040b1207021e10090f 65
    0x343c020800c0760340d01158100500009100e0b030411088603244400325242041c5038295100301c000d0004042001c4500051801e441c140304403603081070134050800c803254a5410440c003170b421143c2d041e45480020311000810380d00c001080d501407400b940c0070710f1446d224031907080050501310000760b8040d900c0300c03405c4d441902c5200700c4501c500e8101c100015600c14640c5080d003054402d0380f140001c000107a0340207410789841c036598a00c485090a2a0210b50142d192208510001d6408150301c0100d07804006100b001c0b541d62108003c03103400c2d110100200a000c8030000c54144c0c01010040c40c424851100b801c80350951032070a15203009854101d035503035568442185003c0d0544180000d4410a403e068240e06014032903020307000e00e01641c201103600300801d0381c83c4103020020500c80c48650080754040300f0901164007030034140303040396900e80f05000c160410351030030707a00c990040c400d00460940d003030125582040702c4c5d00c07445c014192031004950654050079108106584540008181c0c40000b20 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 564850701 1250 564849451 564849487
    0x3030e0a030903141b0f0409051b010f0f0203040b071b090e0c03060613052805070905190303030e12071104050903030c092b05011a0402070b0615 64
    0x840303079444034252415071030181400013070038185031100e51041d07110b41c28504200301c407450440003e5a0054500c11402c0010b0040e01c1d00c0207000d0414001c50002240022441c95107091000c1c0a032070340e1404840c444421501c1d00c840720540801038200340b00078060382041c040204001809109010064040a1884005100c43c0e40c0300c0c0005540e81c0e03407050491003003881440c0c604c000807000381c0014a414401f05010b0300040c0a89c2007035547e1840000e6965401d60a203010601200c1c8640e02d80150b606101c5004160070340f107500100b01040d000042c00e2074285501c030b54100001202c403d00c030386580d50a030090440f50007250012b00840c122482d5103070780c0d9006440e04074051010040b07109000e8007030104481000d060301c560342d0001c00030000504103500071110740b0101540c0c0202655581c11010a03400901070108020812203004041030040540103210804a0603810b43d000c8070600d810003080f0311400340010120301c1441d00040301454900e40000a6001c201520351030710400d000d801c01c0d03407030b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 564851951 1250 564850701 564850703
    0x170a0e01020d0902040615081308070c03050d080609011d07110313180501031e11210c060a020d110304080f0303070e09010e0402060c010f1505090609070906080403030e0a 75
    0x140c3d10640442540762902940004016050500943d071400725401800200010000c0003425614000741c2d00f04050101101c400c19007103091950f5043c0c0700d180098640d042c406410b4009524500414118903025902d1303030481d500643d0400c00f02d40000e8510f480702d00001e0200041c0300801c020300c0b402c0501803004200c41081240c004100d1410300d030140c1c80c449400c20128141501c0d05c8010300008007200110f41713410713281d00002c4045094a00d8040d400d2150b06201d55007028083c90f1107416115000d030415441c42c00303102540c040100384020300c40d941c000c0012a00060384400c0308511514000d108501c50030240c14140d0b8a85610343d4011460450519141c01180d03100004000d40381d0740c401142d0a00c810200da925070355514206096045820141c0081e110321070002e0440c410001c2503000300d269003c1b01805004a90744d131840000450a00d220305405403041500140300b40c80d181c207030342c0d2007400951100419182030000403286500c00500450a143d900e00c4100211641080124012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 564853201 1250 564851951 564851977
    0x3171c0e210c011d0a17070807080711120c010f030e0a080408060703060303020a060b06071a0108010b0904080a1b0b011806060c020d0b06130501080d0f050406170a0e0102 75
    0x1d00c0c0d010450600719551609135104074050ba2200c0c1c191424007154072524660407000350146181680b1aa10b801e1084460081461200164400410083c3c001414031207000d00d103d50503004482051046491803620120859001903005100a41c09808103102c844041c1c940040e5101c80c640041d490031900d8072040e41c4803c17020604000c102c400300406a0300c24028070302449840c0c9190b40181d92a0200f140c000d003040c0d02d503a92441551118000d948505402030102c400700060120f5000313080300280184540c0d0350900c00030684c0703414000b1401d40941d5110030340b01e1806c0c0414008541d0340f1703114603011410500719410310003c2130444000305c1c082c2401c0d01200842841003d054001c83c1c006034812400d01c0b00410000016035074050142086a800c120008650b988442c00240c0b00c4801502401180e49003200200b174100d8001032212100403140c9a0221004a8040a494034010351050100180384510382101d00d42001100c0c581120504801085170740d0003110f100d003680c100d041e0b21299 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 564854451 1250 564853201 564853207
    0xe0c0310230c070c051002060c0711030d030c091406041a0f0d0204060e0d120809070b04030303150509090a0326010303080609060411091e030d05030103171c0e21 71
    0x6010704c1812960051400326600e43c0d0f00c809006000c0c0d180e0000422030b9800e0070340400c045081c0031400a02d054582c03001400c0d5000f484a15801400800000149200181c140704011036140402c424030180b0307490042c60b150500d482c1c1002000120311209a0407083d07482440140c1601120783d0190618071201400540c5550034282e005005c40d00c000e601c2803281c14020b4060012423608003c0c81d0070000107107801a100e50780c01c036400380b40680603800000310a80c005000802c0c154940d0102c0c400440b80203e07d58496030b28030402005010584040290340c0003044002c0000c0d0141d90351f80310901e44110042074414282064030140d2509034400d402160600c0d0400c1a00c0c5004c950583e4003c004890400460841d40d901c0c01507401802215401455650100c6500500c40780c100e01c41d0b034034010120b42c3c0361505068010081e400a100407280b20100c1466010020500030507200c42004001c0326144250070107050101400000e00040150301030012107102058140380c1e00c582c00800685502c0d5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 564855701 1250 564854451 564854453
    0x30203312904260303010e22140304091514010807020c04090c060f031e0e07050a0b1b010204061209060f0e0106171504030c15020307080106030e0c0310230c07 70
    0x9609150004442c0f003a0400c0006000b02c0c90000f10071a0070500103481d00c40c658154a46929841441d02070191800509900210300310034000001c00070750b84004414440000b1404d074092a401e03482c000c60052940781c411056003035100d00d54103640454184125999100154080f9003104c1201006a0f0007400c2208107101c2240c100c030380b203030000340c3c50715041007030807a0b00031503024a1035401c0070f40d40002d0b03c40748440c0c0c1e075540410031480a881d0040008074050b5881c3c10900701507201c0640c80d180c11140e4541c41508c000c041c82910101d42d80368403880f40106105540720000d04140070201c9030141c2d113103034403040a0760030720070300c0f100014000c000a01107050000c1c2d262002161180190305521004030048250074121840f9000b55060411210385e075045e1410a2072411240d6424207000c0c4007000f003103815540711043c14100d8260752010809508400d60740ca031111940303a09a82c060344000503004814180d85c1c4051075026018944070a4102c8ac3c20a0707480380102501c00c00c0c542440030500328 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 564856951 1250 564855701 564855749
    0x1050c16140406210209090a150608121c020313060e010e12040302030c060c250e060d080a140d14060a05060307140306040b040504030203312904 64
    0x4809002203035000c141c2c07100c02540d5013060381c00d2900000d0003003040e10701050300c003034041003400b807100e41c02000409002070503110100103160070310804110f44070f500c25164003a48054103c1e180140520004180301088503036440c00ba50001d0000070584d402c40c50300d940420000e12400c0a010601d0001090449800c02500d00e08000c0280100f1483c100b00007c100580d0001070103040da940664500e6141c00000d2000750502d070392011941040046e10020340c143c0d5280c1c242c0d190a0b1135212490325003988443c03061200201c10410700815811082200700b01c020702074040740c0f18441d0340e41c80c1e8500d00010301d11400f00b90740310b10b4202500050740005020701494140d840c24090b013130503035060b41185440b510040c40c0780ca40c4040c0780c112160002c04a1004e480303030340040b00c0000001e00140414141407800a40d40d03031005141c40b40064440d496040000f40c00207011200c11040d5030440d6205080c241e5581d540040044035400c101841e10240c00084c00000c0904000d0103101c100c0e08069003502184 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 564858201 1250 564856951 564856961
    0x30218100602030f0d05041704080a150203190b1f02010605041b0807080711030403082104031e03231e090601061101021c2301050f01050c161404 64
    0x70070554005200d48032030808014240c80b851212403901082c00d49841c00c0071807000c00c502e101c002d60402c00240204129100042a01c5150300c20114007001ca0345070b0701610304034003081d41e003401c0c20038186540d40ca0780c811540140341c01d07410051404440c0c0340b0480302901c803540f201c4e0300040542d4480f5010040b82c80d0610400741c0014001c220b40040f480c2d001c400600b9208010a080144001d0401007102d0074410305240030075440800480380c4c0c49840303003055207098000607102c1c003280c0a61030001840f640f107120044d000704d038103441d036030076141000a400741d000c041c103950b01c0c04240c2c6c2d07001603000508400c0203c4500c40e0300041c80076080c2c02d000c0003100f0706ea01049041c001040081e800d102050703000040e003c2c110b0b03483d4501004e80440002c0024003900c14800074900c401e45d6080d20060b202655886004030500d0364280000628090070030b0340b03202c40709208075070b405980e66070200e40d2540184010300614200c0c2c0c0a841174160414100180514280c21140d1690312900c0c04070039600300f61043c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 564859451 1250 564858201 564858209
    0xa12020f0a05060117100c170601171605070c03110a1a03011a04090e0714030a020607080f13120209070e030a060f110d09060515011b020a03021810 65
    0x1e0204598140c0710950359001c10300c1074035411884911100740b4544240309003400442d0255003404058213440000300b4601c000b0055900c03075021100410159030140c0b07010204034000c400e41d0f139015640e4540a20448035107500f07850a1100c10010340b000030b42c6d00614200654480d03003000c02a8000c04090200382c401c0b64021428282c2801441e20340712481d11309403411a5036039594280c1d0b00c0d2020b020030842c0e0140c3d45c05010050b041001145081e03902207000002e8aa40c440d1204100f00608100f559500c403001000e900b01d0002c009030004101804002d0000078030012441b850300f51484c1212000101c00d41c08034040307042115001d030031458811511500007038203260040480c00c1080020b603c80886280042459550b41d405200015054200c2040f6030880000c1c191a509c1203141800604110941124054a4400040e4203041504585c08440303c06a44821140c4c4001044211051940c4800e903401580c0317900003c01641c888415400640c91107070590b020f410402d10f81620307602d10f604 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 564860701 1250 564859451 564859453
    0x310080303070507060b03070b070b06120111041e0f060c050607090f0e06180a0b0102010b150a08100801230601090303050306040c050c0109030c020307060309020d230a12020f 77
    0xc10b11900c00e50100030358a4494000100080c508005c000092610140b0352081091520100c2c080090013a1162900e206440a940442000500c1076041d800c0b144040901450b0110038401480151b510703104c10060000c944409031900b030340b145040000e031289640080d000905190030301d8200b10041c0481c5400031410f04010342d02034107108030300044403800d000b9202e4040e540000074406a5548913900782d0510b10001c182078030f080c03035102c0f20083c0c4484820140550700300010510681030142228008640c4084590708141410200300e810200150030500600700400c400704440ba8284100b14440405460b008a4901d05013091480da8000416242c1806140f41040011a401a0840c2d46c00f2070115070021341c40c071401c2c000b82c82c0750007000d0307480603658645001c11003015001071400c80154002c41c11104044d5550b4003c03800d0f124201d1000350072600b18848140003440100103490340c000c04000c0f084a403000b904d6401e00d0409101c00690743c650080c071500c444d10340c040c0100644000814 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 564861951 1250 564860701 564860707
    0x20a0e071404030206030a0504080d0c030b030706020604050304060e1f09030611030708040b071b12140324010c0b071701080a081603261021121b0803100803 69
    0x44c002504601000708105285904c0b88002010440d1b0740c4211101c044e51580100301d840760504000f00100f203032a070034a001740701342c09020820600000b0801d205652140c000c41c074150629030115800f00800c40c41c640c0000a910440d902c0b00004506801d11130344680c6c0f0035124614509000050301c1041081d050b4000c030402c248039402ea4410390241d40160881d021a030151202182104d03a00700c9a400c03105409450315010007004610300000c082c244d02940c0c0c0d001d6001186070f10541522042e98055141c0c1120310002d201c550402d100b91040c0d1105041c56000c2c4404e40d2180358052004a8400380080d0b070100d01001c000741d020710340602408032003005040c8882185d840c56468410071089106070345040030242d040600c2103091814251580282c5403c008031200c2101741c0303810035100100860004800440d040b8050003c60108100b41102c5242254064440502400d0f040f0501030810046000c100e01003001e24900e40e41c0d8600c5034540903602d103440d00b44400000625003008060390010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 564863201 1250 564861951 564861953
    0xf0903050a180f0902030a050c0301050904111302040905070207081b09041401090f151109060a022a041a061c29010305090706200a020a0e07140403 65
    0x31505407000c1480300e0400c2d03200c0320480e50034594018860b0f48490f07048403101ca80811000030980146000d4003144a043c84691602101242140024081c0e140c011444030001000700f07001c502103680c004406010007406014140440b0180d03031054024007001c036115414071540944c10800840100040d201500031070750303452841c0b100403425a80952068843c0300c041420b020350007001c00741c00c03d01c12000b009450000d21f02520481c0c40500292440030400511342c103510001d000740140719880e140e60924010303540042041ea60880c42c1001d04600c1400526160070f403078140940410760f0301348000c0090a18020401c020340e0241800105450120503c44040782c030b41009650541220000304034841103c80200801414008541542040e0b0840b00340c4400c007000c3c8100c01a000e007a6424412641d030409895500d80b042e03c1108006100c40d06240022920040005090340d210700c19034400c5080768000400e00446d41c0c000c9a0400000d2062102a81d0094084505040b200c900035040c2459 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 564864451 1250 564863201 564863207
    0x7020601060e150f0403060603031b0b160201020d06060203030612010212010605070f0614011d070e09100b070b160c170906070f0501060e060102010e100e0703080403080d0f0903 78
    0x60701407014021107035800d01102c403041d0f19003680c8482c010700390304688595a80c10288050708407031206402240784055000d4126080c03c50301e00307880390060350880071915002201c2100c40030348404001155800c0c88908542c000b00c0c0203102c01000140c2c01981c80703050410030410078590111120410380e20402c004d40e4070f41290310f03105046070346030b04215441c1d82c0c26052012440b4502c4800420052414000c4d0704040f000320942410390329591010380c6d6220360070310a80c4504005442d414003044500d5140745851400b81c1c03209030301461841c94046516030f00c00c05844542c000800480359a18000208030881044c0e00f001d403c0441e0074900384071442030a8480d110b001030790701c2c0341072101040080c480407640c460808031022554040031080c0d500e40d039410007d000700050300421103a8042000400c40943c814003811301400c03040c0e4064180196244444401400e02c054003e20500820b5400400710301d210015100541c0607840b0140e40c0c020060b02c03842140c0c5640005140ca524200d108404039074 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 564865701 1250 564864451 564864467
    0x180209070e030a110103020c060106021f0203040503160804080a061b1b06051b030c0715290d02120604030212071a0702070302030718140105030a03050d0b091005090702060106 77
    0xc0c200c4250442070044c2c030012406840307a10760b4049541316034800010400e03400243c10100c020541151407114501c0041c2c401a13200903100500164030a10080c1c5c031001060a103004070718810040949029036445009040000340741e425034102d50354420b02201c0390407841e14035160700034070701e0000d84118007031180d588403905a20000d0300a03503031800081c40411070140040150494042410340368070340007450388080e600092040f01e044400c032484401240c070038056041084402442c40e5a003010040c0c3c007190140c0001c015550194025034050013607141c0100001c41c4c442c1503009845249403500f0080d28008042d82c0b0300441c00020018100070880780c900700901011440011421511405402c0b8a40400e5801c0694503004107000044c203041c440d02e20000c01c00006405101000402c15002e01d650024030a243e0560010903581002a2003600140038401d22060700040d24110100482c00c04082201c0a4509a207070410610040c0340488080e40c1c8203404d88000c0030158100304004011301 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 564866951 1250 564865701 564865703
    0x306060a06050a0201061a280f0509150a180e090d081302030f160906030c1401120603081b01091a090a2f010207060e011809180209070e030a 62
    0x1140110b0b80c0307201c0d0b600c00e402c444024000c0c981499895400703860101c035145d002c2300c2214008141c42061000c0b4003140d0a403804036103515201c040402c840b00c1001e4a61354031068103a58081c1c4124210000c2079414009081ca0b0405a51100303607070000d4043c440c8250019401415800c211a8104440c0400018422034842054a0642002d0b213a550030650f4001045030025030502070f02401242c010000600c62840c000005005404281d03140f0aa00486850b8000600402c1445400303001030b000c000c09030140e0400614084940700d20034000d01c4101d038a541c00841f004100001c680e02185c65800d036070507504401d030000308a1a003490750b441d240c0702001084181b0101100c00040e101d81c00c01c2c402440c035036070401e4004414034450340d4000c40e40c1e00e0310403043d0090303000d11440420300d500c005150801d4946513120038800e104404010344000440824901d4110800b28001c40c0f030800a011702d1030701c050800a0041c840360584100a035002c40103040c5010030400f41c0a21815035000100c4228403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 564868201 1250 564866951 564866957
    0x6020f0c010e12060405010903020c0f13091e0302010905011401060503040f0c090e0609010509120301090b0f0a06230c0c040509010f0c0c0b0912180d120c030e0306060a06 75
    0xc1e001120205451010190f07010001d40100d90070041400340642009071124070940c2940d00d1000404200000d01c800140010707041400304940c02110b1000d68442101d682c0070302ca00000c6409681d801140c1500b0400040340140d450307511060800000340916041c00134596103681d055810003100a22a0000800103012510780d0965130301400601035102c5c0140c0584681802411140480da075503541050340c0c80e0302d156182600080c0400c0000c501d1851081d41ba00701c19145901c0c0030078107005054220300140c0c0c8410270140080d20707540c4008172200102100d40b500c8a42c0c035038000140c045800b5550a141c0b01e80020081c4d64a01d202c0030420030906502104c0c0000c140c2c4800300d03002d0040c021103011901c41460481d00b41c0034260448543e00c0c0e094443ea030400801d40c2c65036001c03034442d484954012400c550600810400e010072644a98182501902d0030101034110b17110340303807080b480040c000b0216000e100680181079200740003081580080e40204a10700304138022410345042c40c881e070010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 564869451 1250 564868201 564868217
    0x80903030112151e150807030f0807030306050a1206050f04030f1202090918060702032502030f121909050310050615030103051c081510020f01140103050706020f0c01 73
    0x6900c2903400800c1075129200070201d104107103070f40e404c010202c1494401035001072000000f1604400510081980c0c0c1c06051f0095641a079950146903800c1004100c0c00c0c19162200842d0300d464070307030040009000c0c02956030701c0307440f440c00c10000300e40d805810951440f45050400c00803a4002c1000c50240300765160407064050b28800c0c11000b0b000c3c0b103020943c003a6052090003001c01a441808420801d10000e460240c0c61388001641d5a1007000042501c400303503c6500c080d4080361210581d803a80c00030b01600c1340c0d003818148141c100781c0c00703400e03001c90900c1c040740812030211003100d04c400084107402c052a055040c107000130b5466590301e901000080c3ca45001910540702c0d02c0c0c8909540a1060300bc03922035031646020f5407a400d8002a0101c3e407402008a0002c0e140b02e1034100e030040d60380c6400e24603a21400c070305018001c584c000d90b440c00d5110b45050540500805d1150240e8040c19031501e0b1010b50540c44c03d9402d1207001c0d800748046500c040c2c0400900440840c030490040300901f42096 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 564870701 1250 564869451 564869483
    0x9052a12010e061b040b0d0213150905060d180507031b0605041701061701020306010201050f060d122604020a05011812170a0509010306090225050a0606060f080903030112 75
    0x136903116582203c6403544002c95032042c5e00c0b019402a000c07910b036404101070f4060311940c2451090503a00c4c0440c0c0041c4c1d14510401060800320020030301415038990200f04100700c0da40d16880b400c1041011145540710010802c10300c002c0c4c1169146080301a03604540e80b600d000e2008200340102d0045001906805800340102c0d4001d600000042030807038154440766205894103030003500201c0b0300601550804c030016002030802d5410070701c1081c000308541c0e000398050710384800c2c4122400e054824401102920130506090009500c44050351910448851030648103100000b000c2c1d61100d41804252100840e44207000c000120550304032a268140c4d280306070800c04582d07425400310199110000030080300d929401001040706110a032814081c0c00e60b21040c2d40104c0c880c009420300c448408480e141c00d501803000000703e445005030200c40140d41d0384e4407648102c51040d4008408242e0a994011a46400902480d071200c0364001460440d0301d041841c01c0c04010102c0000d019001c1180001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 564871951 1250 564870701 564870751
    0x1e10031a0f0d0f200a05060403080a1419030e0c0a03020907020313143109020604090f06030212070602120f0723010b0a080c010309052a12010e06 64
    0x103a0040e030070a003000d05003096400c055044669100c8031510b0319054035860212400c08075000805c07146d010788441d2a240c5151544045504001011810083d41010180b0048003600140c510084550318211840b546400c1c00f030100d9450100040c559040740e6042c070195030f10280040c040740e4050f206496240d0f1804822425480b65a0b44c1034180b44000b48041082807010b00300905000c010b842c03101c0712040f01051318040c41d840381c1c0d0340d510469030f081244046829542000103807520251005090540700c800440c00e42e0508141e090306a50360b8601001989070260011141e9800c00c0041c1003230905105009480309030004444140e40e100041e40d5410100c1d08040361006a041289c4d03014030300b190121a10014030130016441c5a40c01c1a00001c01494240003001c12208108018008040904010b4024212001040d110b60184c0722213040d1024080032503000e600d00002070000c440350b1a40070403140400b541c500001c1da80c5002075940e40e4210000702960000080c40d41150680c0841001d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 564873201 1250 564871951 564871969
    0x90e042a030512070317091b0411072009150d022b050c010201020f0909070903050607021f0e1b13111306021204031209051e10031a0f 59
    0x520700d110f0840f1403190355040340042d0a10500c84c0d903818a8000e0600c2d80b000d140d040540d01e007500c0d50010f080200307040c152040f00105030307080030b040824515449002d081c080d810010041d20103003c20301e804c0340c000e0300c882140003507803008a030090b84a04110f00008250394000c002980104a02c030701700004d5550301030945945801c0ca48800040d070180c0b082140e55401850400c4407180315200110a1035801802540d071708203a03455907141800400b41c1002407801000e404101446801800400410002c0c0b0003648039130110340040043c52020342040607071980c0400c1c2d402015180015041c9000c001013801c03110b907514038910103012540600050364004090188515407031500f440307004108081c0020b88040c03120003040540450b6610310a03a2214070126028400c1041007000b0301c0000d510780120010381e5407915201a0703c985480100f100301c00525214200301c60031080b1141145000000b01003185c41626060040c007018600720240c5035450503000b0b20400e40f0300142d030040e4031000c0c06 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 564874451 1250 564873201 564873203
    0x30a1103011d04060b060403120306091b0e0a0909141b010905060307140406030b09180606060c070807090e010f06030c05130902060a0c0b010f180f0b090a020a090e042a03 75
    0x1d81c980e915964a0b12881c150f02d0f000292010032f007841c00000d01130000e403046198100aa54910b0343d11942c0e0350b800c43d00500c610700c1540e0f20040d00b440114522034a407065800790b511401d0703402d00d000ea001c500245409101c181c0e4003040c50380c1030241000359900c1060b00c0304840782a1030507900c941310300d94180ca1881607210030700400074001c600003171602d03810381150b40c03c05020349142c4101d8884654010314240003c02a40060780500042501401d01c40001c001c1018000156501d80c1c0d118840740e410410b8ae41d03c240311081d164a03c4100c400340078458400c01d02000c4000f001b940b455990740ca00b103800907100d0300d481200c0030000c404650031a074000b40406c5500500d50340d44d513030080b03801400003142c07030805580c04c14040c0004038048101d14481410ba0b50104041c1002a225000c01c0014003820004044900d44650301c1c1c001e0ba440e10701e130040c06444001c00140e2a5001c003140100781080a91107a02c0c0000311009110100b000700d4100080d118155280414240d402c0f0a400c58035030a5600c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 564875701 1250 564874451 564874459
    0x1b10030203091c12060e040b0f19020403060506150712110304080114040308090a0c1a09120718060b09060f0f0d02120106080f060f1c0305030a1103011d04060b 70
    0x1d910303c4143da028012005030040040100a559240ca0880000c883c088800501c4950042e010031aa94141c0002c15400b469100300c0462224030a444402a40c10950089849031344034000d004e05450720300e013404424881c00481e241049a81c1c0c64150359510100c4401c0244140310041140c03158082c412034019200600003840300d10846144160140000c441c16400502030001161400c60041941004160010403104c9500c0c00e0041e0382030303140d69000d040e00702c0c80002c12801d41c26482e42608241808079400152a81c140790901d01c07a442144000d100885900c0d20b0341c10300c0300000d0309050781c002035410f49440d500d90180b40801c8050b4441c110003001103001c0400c003401c10101da90001d0905e5007200b03503020400c0e6a5004c09441c519001e40e10440c1a619080010300782e82031101d41840104402172020f510711140b10b030305280210803104150002030340041007010142c600d020b8004510801c884c114a55803401ca524040b400d1b440e980b070400002d8110102c2c0078040c15400c0102c18003c010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 564876951 1250 564875701 564875743
    0xf1b0d061a04140604060501020a030807080c0405120a0210020c031f090501022b0606050a0c060b041805011407020303190b1302070515010e060d02150a0e01021b1003020309 76
    0x3c410b42221410840b6160f00c200d0a2000225030f035440401e00f03289940d41500c583c4061b0b103442000380c60480c4000d107422418001480300040645d2000c02d48c4104125440182020881c1c900600c00542000d00302c001c10741d800f019a038402074400240c4a0202d6500045407a05540d20406440c007074011301e9006001c640c00480c40903601405010034031845112000f0150094a2480360202030312458030036400410360a100c5c01840d40d0081c0b90802e5928440c03480050500030b4040010222143c40c14004c0c2e007498200c031401c0410009109281d4189607041c814859440d144070020b64a10000700400b006c2e42000c00000d030440055001081c444800410340110400c3e050000c0303001790441c0c101a1100d1141581010380e036521801160b040e0342449904004590f40c41043c02140501e002c0120380096400252555036030012010345044c6505580394030007101c07080d000928001c00c2c1d0101710440784000d0070128a65441200c4d101895045080160300c0341c0e1030070001e500b030246401f00300e82c280c0071003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 564878201 1250 564876951 564876971
    0xd0c1107061e08011406030901020d0609050619050d02060903070305060c0a0f08090606100c0206070f1a0c0d09031e17090c03031204020f060c0f1b0d061a04 69
    0x2090b002100103000655103240d091508100e41981080c8618805144240c041d0300141c20010300569021103184000f500e00149034000f60100c50446c0c0c0030413192a555400e210881c43e2400c4441044c202c0d414034000c4403070600e0009445112023981c02032040100052004c601d41701413056000a6401c601510746500e4402c0325030140780e115004140c0003030303008003402c1c40322801240114042d11212009041d1a50303480140845a00001e08100a02004225142c0160303103242c020500e2a02c10051048802c00360b01c0c0141d150755100300c0300300c9081170800400101400b0501a282d55841c0b2204c086080d0a03d800c06450b400d4004006034054200c048140fa51580c1180c3c0b49000c485456010007040d981c3d080080da110540b490800e9810f0300100801c200d22000132110f00c0e00540003d00c603071452a401c0700020796540c85601c0340d44071600402c0c0e140607034074003d00c09196003112040c01700e40c1080010f00010041151706030010442aa1058940c0c91001c1403400100d01c0c58000d44100902504 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 564879451 1250 564878201 564878207
    0x506091309020d0503090f040203011d06011404060309140c01170408130608091608070303230703020709060501050703090306022109070e010f0b03070819021615060305030d0c110706 80
    0x80c6c95124051440e10100d812a41064802c0b00e040355544176501c2c00e800800d10808403103800c06001e55040216409101e00d408442000810090081c0d8a000440f045680743c03911039003281404000098201941c03d00550340c111807546800a02d042c03490f41c0c907a40e9440e100310a03000d5000f1680644a41840c0480c4003900a608a40528800c20482c0c034201d1441d4101030300b26007d40668803494101d00810400a4000c01c100e441c15002c2070b4034544100c090140140268110700c10580040c2e0002000300800c050310310440018000a1034031034a421000c1c2c82c05000202244001052140e000591000c0000c07982c0e420750303107a08040903900007428280c0640c0da5a15140c0580030384401d212000042c413034548140d0004440c0060300f0f80703066640f02d00060b124034034000c141005042c282089600502c2192004001345d1042c103100410903910340c18141c040341d81c805480340c9502d01c0c014044c0301150000068418803205800d0204d000d46000c0302c201ca144900300c144081521811401050b144e030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 564880701 1250 564879451 564879457
    0xa050304150501182c1e030a14161a011d01240c0503070b0a0c02030309332401050703080f040f24150506091309020d0503 54
    0x20041e036450a62030000458142156020300c242d00c1e050803a11031304040542d803500000c00030416103004c00c201d07501c03030b0043d103541d4a4881c0c455031003500004c80c2030061030712125040301c1c0c094821004500f0000000300150100204030705a40c8080b1001c1010600c14192031505c0da000341e440070f40043c2241d868190a415100301303010700c00143d40d44071085103200d220250b50368100e80303250621125111001a038141503401c91082e440821403040360b80c01c0031031000c0000300462481507611000710702e01960a1000c03038071003045441c11074204001780b00c10140c0002d41d050441d00e00da0250b01c0c1080034450a20411000c0b407140c00420129a01040f0800011101101c03ca050300041415598407480c011191407042e800010007041e85035020544c0c50f524003000c998010310610007241115125182c555030030f1a80305848408a0780c00030f030482c0028042c0030322904505200010444035042000040d10340c010f410049000c0c3e0606c41c0f901401c0290350b001111a0394018128206106060a109850358 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 564881951 1250 564880701 564880703
    0xc020604021512040b0c0405030f0d030c0c08030406110d090c090b1c06020a171302030c1207031106090a0807031109061003020a1709010c080901020a020601060f140a050304 76
    0xc81e100c0c0881da00d0400b14125141d4503102d2050000b1580d540e41c8808100f28003034030068250714144808546504c0800601541d49090401410101c4280400030709448032354203c40c082001d103100c080002520401a0fa400951009000c00c80007418000c198082c0075034001044003a043c0b801c45000d20005c5c00141c02036401c006400e108036980d0809000756000da4240300038140768219500404100e0540c050008a4403d1a1000d0600b40d00180044030783c10a680c220804221424a8411031401700b1060403695425a0040004000942c489440c2d213100d100190000000c400c04400a075200812600a010020700032400c00d07855150b070507501c0b82940030881d015914603801c0d504074607180102e40d02c50000104a4038590000e058110041d4000880c0300052100c03000c07620703010000200b405442035030f141d000094aa40c170b0400c000c2803200050b0072098140d204008100c5015408914141034500600f002440700b003030b03107074200ca2074400700c1d000540003140450b040d0301d501e50101c0294021 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 564883201 1250 564881951 564881959
    0x705040905150307171002040b1b010c08150a0b030703060e07030504021e04020d09080a021219180e01030602030a05070f090501030c0c0c09020307031410060804080d0c02060402 78
    0x70342d8420800c030302c03452110500d440d4158000c07201004126120182070704208002d405461000148141c100c040c0d803c2900a000460703008114400f000034400c081072100034000740284003101052201400e0044050104000007030038590180d07450301c992402c1002010301d014041e43e01c1c980040010020880750040400d500d5501c000704100e140b0030b02805000fa500100510b40e013058281502c000c560484c0c01c0c0e150407607000e00c08074006000c0b0344101c041e0180035100890781d03040c003d032009080250011411220800500060300c00c410b4002803a8454129410050b55503219420102d0380e01d02d0030303401410300c250002d001108014503500a503010766200507003806291100b081c20b813403020b01c0c11708020005010460070000340d842a04030000700345281c141452158883d8641c440403a04a0304080c3ca00c58000050100955041c81603003070704402e120100d8903a0508034104142c0085074410315042140090105082c0001030044429601c00b400c0c0c04c129010f010034029489000c01c0340c00380e100d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 564884451 1250 564883201 564883211
    0x120212090f2a060711030303070f030c021203060d061b032415080a27120306030206030a020f1611121609110705120d050603010209100815030607050409 67
    0xb007402d505814840d40c202d01a0800c0080309034405000141d044200c0c00d0301c074407441c801180d955460510045000c0c0d00c1c10703692660207110201014040e540c02c503900030119031140642c5807003007a00c1419680c01580031100707040d000003103003440d10181400d05801c2412842d41c211541400c4c0d01544800b02d030740b8011030103c0c0d00c0d41c043c40545050032210710075039181c070303504c0405044028421556941d001805050018400c0e031000c12081e851012440005c442900a0307a914050243d00c01c1d00c0d02d941d200340e103001d2060354150360101c0c0403400050440141c50740c012504000002c00c000940350800088046101100c1c02410002d02d000044c2412601664078050a000000300200b8110103020300c00718889035007407404030340c01c0007800c961810301c07044401400108006081030000101500600700703019144c440c400c50000c1120405420280310368410002d0000301e0300d480140c440c52882606001200f03503680350f8280115040c10034850b5040c09800701704498075402801401c1664107400d41044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 564885701 1250 564884451 564884473
    0x6050312070b071107060507110a0b0915040315060504140c04060c0f0c0f08190203100c0314040b07021009260c030406020a0215090d0201120212090f 66
    0x284446108096503040501040384a02081c402440035800410364501803003050124a00941040c803190400c100041c00062801c080c41000303403012001c52000c88084441c0c0d4074046427050280b10b04660203000e2800d00380028541d0210074299030080d50010040c4a10401002451001300018040c2600c2186489d440031903488000b090b2034412a1400542d9251600300301c016075880800540c00c81d558498900508001480402071000500580008605060501e01f0181c1416800d03044015201e10001452000d607400055114141c01d10303e03000204001d071a00100d01400504240045076500c00080c4420030940000f8144a80490307801d035081041c00c043c00509079044084040c0c0300c614185c03814400496050364001102e40340400b9680782c034000c00703034881c20f64119070700c01c002503000a0016015400c1c01a02c40721131490015402c1d00c2c0c21107041c00610500b4507400301030304004081040c0d803109804c96044078012401d10001149601d46650081e5403101d80351072903407060080e01c010328 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 564886951 1250 564885701 564885703
    0x8040b0d14010e04020d14010f0e060103030e090c0a031a03031b070f0503100b181639020a05130b130606140307090e01170708061302210d0909060503 66
    0x740c00b450380140814840310349a01c0340c0d1905141c0181f800700a550341c202d61010001c40d4460601a11400d002822140d0700d1801d018216558000105014004072010008142030040450308807589a080c001003482a038400c256040d04101a4607401d44800108404801c450500051000c4000012515100e03192400501d14031840d01c21103400da486462402041031094004800901002d00381800c800300004c0400903aa1040c1d400070a01c111200c0652003803075210091610b205250940c085143c1c0c0c412500010081c2c200842400d56110095294119610100786100400008165907022254080d03030374001d00702a802030b8810030b80c86211205601640c000d61080301c0083d2a0710b0f04060b80c130301c0c3c0c0c0b00e40d660000b8550001c100c43d05502042401101041a001c0c00180e00b2500d400d990340442240b421000d07070001e440a621160421000182c184801003e26506032604425200b64140001d003640c80300e42c4184650045940004002e135200200c1c000b1110400c0f03051042e075555200b41 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 564888201 1250 564886951 564886979
    0x180c13150609050130020f040f0e1302090405070506031e060a05010206010302060d02040f140315220c0306110910260c090307090203070e15041208040b0d1401 70
    0xb400310381c801d01051780ba079031038a09515194550131607076034001002c00d14170402c0b40d02c000782c0c00010710f00105080c0900c07113510050320b0182c040d8560459150500101180455203000002071081a4801c000b078100716003803191800a020141c0a99243d050800c200c03d260100e200382c1d041920381c88000143c0710301c0c00035a070804507601a00a081c8590a54007444035545c040c3c02c20700780c919020480007a200140015035001044604400321000d40c801040600780260901c4070b05403000c800c01405440b811240800d8192030041008103001080d41c034060b8403010040d070000c0d10340e46c903110703821040320841c00c000c110315601102c140c55144070300741c07065445004a803680035280da0444000c07903088458100241c0c101d450142c04a0810f46030000291808a8541024942c0c03034020046c092190742190840223408011244000c910280060010450050740300c0ea80945001c20024014032902c14100c9015000c21014141e40b00140d2041001410324030f24229a02051072000003042d020313401c0c00c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 564889451 1250 564888201 564888209
    0x1020118230c09010b1b0d020307030305060d1205030a0b0a170f070812030c16110411180d080702100203030402210c040b03030f070b15010c0506180c13150609 70
    0x10b143d040d900300b4160440b01c5d0000400743c218912455642d045494040084074441d021590046995483c6460b000341640e102034000c0e0b0144d800d12400c0400254036200c554056051454040c4e02c9549074030541c00540003103210941c0100080c03101180301440710004548d8a1510300468034120704107a007403540e0b007965104009203030b003203068111890300c0392200139504000c400103001e0810000d401d081c94281a5035001b2200140c1c1c42d0100390f81c0b401c042c06940f285016070508182401c0302d2620001c036403041910201d105201d254010700820080100340d42c00290042c04890042da4005c201030364075407080c1e805a01c100c000302c1200000c1141d16080c00c0f20b146522015042a004010500010b05016411141d050009001048003c01443e024004003809441111502e05164250070701c6410f50991443c10170a075a202e14001c244001840c1d9000225000f10240d210300311801582402102d2a80c945d00100d01d0f80b9900c021080c2e070f000000844540c0030021000c07580c0300d0341550380e4400740c46 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 564890701 1250 564889451 564889459
    0x14010c080a0c02010c080d0c020601081605011b0602070506040605060f15070302010608010e0102090f0f06041a04030209010312020c010809071707050a09020c060f0103020a050405040201020118230c 87
    0x1025108040c4a4042d42c24900e20605024240500c0756441c042a9042000312030000da580b02035002c4426410040140182043d202810090f1060014041c5c200d513203008407410310070350403900102d03c000700580100f00390700240210340b501d00c10300c0e01540391075054505560481c10700002c207030107180c03e0050307010003070001f020b00002d40b2288000f045150400714007a000d5541c0c2e094000740c0da4000f80160305e01031f03900100050f80e42c21054200301070070a0b0282c449000e5000c9030516206034984030700310340640e80340500e42012800d000054134402d2144da000250440c011400020802042d8a50b0342c40c0348030300d5020703a11050036034001144c50700c1040301c0c03c030016800341c0710820182c0c58242d00460f40c0005041138542c52503c640201d110700d242540605076150740010201484034003849a15080360300003c200d0340c0780d4550740004415201d98003d080c4070b1580c80d03000c90110382c001d611800c0310360802610750080920314204021002c001c1e07a101181c0a101c00c81900381100040f81c41d40c11703c18014 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 564891951 1250 564890701 564890707
    0xc0e010503150f1315050403020c1009030b0f04150903021006080f15060109080f0f07080d02120d090203060f100504020c030f0a17040f0318050f04091e0c14010c08 72
    0x10070500410980c04020fa890084c2171440c03d0720101c4900520784101e000e5002010006220400c0c01034a05404281001f0004042001c1c400541c1003c58150005454105001c1d140c41d9410440294840488454505441d21100340c04040d0013042d20035484408400c00c0005a41c1d07040301c030380c550b0f05420b0f400200d5003142c2d5000c4064610804055040b140615041c2d541c40c1e00c40d0181860200d2030034002c42d69600a402802507014200040300140c030140c0040d0061014a03003000c2d40c2c4003418036008a800d5004194481e2542090b4001c640d03558008045800a0510a0f11000c2c0c0fa032050b13030011a00b00e1401404582403d081c021500a081d5142c021032510783d5005d0f480d040c0e82c11842c619070030400340d140c080603070217050301c04035000d00e01400740f1b00903642081c034019156039080d42040350fa940c2450001c11055448140c0f62807a4081614040340c100c460340740c407a40c0c0da0461031802a004046000d10300901118590702c3c1c007920541524603148412400040d5001101c00000508580d810 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 564893201 1250 564891951 564891961
    0x8120403081614030c0a051b100f030f0f0c14030c040b0903032109100908121005090a0902010206060a0302060913110a0302190c03120c0c0c0e010503150f 68
    0x12880140c003902030559010340c1043d5950031415a4000030010781c181c1e000d0074007042445001c0c00448544500118000144d07602d54000c6091002c9517181003003800150000c44514900179002101081c0020b2020018400803150400040442c24800300c00200c0402d80f41c00844000005c03680242c1e2098a182d007468a071540124083c0e01920405405000c01c0c890409882801c0480380c0010b20084501c0c0e1152401c45006440c11602118182079181420030202c00714414a0448880304458041038110341e42c0c0648c00014445258072030764000c0c820000300850395400d6840040114403d80c240c486076182c1d4070412a2050080c00065400311040049050501d4203006180c10082c440c4c50206803031005003082c00721900840b1610340800d40009010a200101e00815007280080d42043d004500668030010300074041e4840000740150784420342c800b40ca0092942030592a8440f18000d10107448000c4854111020710440d0f020b4070900a510100610740030030300d441005491005c01c425a18 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 564894451 1250 564893201 564893227
    0xf011a040902060403050a05010621110d08070b0c0a030f05010b030601030e0703050624060c10020c1e100510060f03090f0f0b01060e03010e060a0509250812040308 72
    0x1182404903030090f07041000000180080c80b012800364082c400004115241c04801c010450a040100b2581d0489007402000030307a5111000500c200243c6a50042c11000d180508007442515400f41035404401c0c02c0000086044005110300d00a9940a021015100c0b0741c10050310801c1c002c8280f01c200c01e000052241d4070a602c030785c00f43d010100032075401c17039034903150300c2c1c1040400d4401d89035020080100c00d03080b8600600a40030503c0030340f4500d28224038002d1081d103400141d009120600d8000402880c200702c2007004040c01545803600105503103541d62200c0e51001e0b20120010040c0c100070002e80c1410f880780c2c1c00350448207941c4a550348000350210840040c6071810007142d02c4a0807001030004a0000200004214410184c020040d4100356000d40070f40031032020540f10785c1c1045100305201c1000300b00d464008000050100c1e454880c07000b49414a0800e80c9040518243e1041a07429a00ca0440c4039045510400c20781c1e01c141030584800e18a44150b0001510384001000b200b000491 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 564895701 1250 564894451 564894461
    0xc0c0513090c06020d02071703030604090203010e0318031b100323010303030b030f010506011b0203070512060a05010e3d0902040513090b010e07030209030304170f011a04 75
    0x805000041c407400103580d2400510500e030001001a0300c82a92100702580421401024041c0c189400850b00b0380c900640e50f03248001484e25000341d0300d5244500864800350410892689860150f030b803541c0c018903910b01180c3c1ba0450607031080c0703d00c0030f1119a181c00d18040e08040300c0050704d03a00011901d0f18007035020740000658034128111421004981040040303009020b1813299a01184d03030520b0000b01480d0140d07942c140c00184e45003a06002e002d0782c1200b1401c0491091994010001e440d50002a06080e060743c0419080f412120036071100c02000300340c4a109807480f0785e0411480c1d80ba031004007801c1c481140d01c0c950b40d00c20a4841d1124240c12208140052402141c1c13004000c0742404d41d04005001b6440300134403907000b1501340800e10342411349a2020032540802c200b28100d0f40c03107000000d54184624618a410040070174011031107501200c85103000076003200d079110b680780d510083c080504000e5007103602521a050824180600400c00010020010000301410190030000101 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 564896951 1250 564895701 564895729
    0x20a02010c03051908010302090f01140f040f02030103060e06070804050c0108150a080d030e030918070c14060a0b1008010603150906080c04110a0203040e280603020f010c0c05 77
    0x5100000384d003050b81d00c0d18040e0000b1035464a040f03524500c1401440c0001400340411036116000611080300c8c526481d50b181142125000085580750010800800e446284410301c0b42c0004004818822a80c000f01501c680d20307000c441003030f55581d01c01c07280308a0035100240b440e04400f10303191042d0301c141c1010b9004804030416016003c64800003403200c100c10b0b40020180d0f040009000100341d018030801d402e518206e0040d524100310700001a03142440610351496101c8404081800b042c4201d40c4016001d501152901b00505542d9080703a5a44040310103800c407506110203120641000c400c184400c250548650409908042d01038016103138410448008000718080050300644e98040e14005003144009001d07003040b640f052000307a078161040320320b00200401030300721215400002c076400c03188044a11102500c81601c0c1017100b81211400c560224580000703680f80d41c181e64401c80032244200d4030561590044001512890454140904800c010481c00c000a09140012403154 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 564898201 1250 564896951 564896957
    0x9020d0605030f0a0309050d0305031b0c030d02041e14040b03030c120d0b0a05031c0302070807050102030a14060d06091a042001050415230a021b10020a02010c03 71
    0x400d4441001c6841d2603412004940c00e9413144075408280b5030840400f602403c4240c94119030b401c816200a03109120240c00ba2440b406140842000361030606c0c25104e1554024080d640d40d14280c00100d00a500240a00d8807810141c001400200402c031078100c04035601c0b008090707040c003071140400000b40900d000d415014082040501008c1c4014000024514490142103880300d0300303050403200710f50700c0b03402c0c0b00d003d8152000140420b603070008440007541042c90b440b40c04170020300e41c110064015042c0003008250b000c6004e504004064000d5132041024000c2000003120703029042000d42c606071015908541b554607183d012038890340200390940e000e545c4050391404071010004808a003140c09031104108600141000c0b0700c00701803c0c071110000d1902c0d0b410300f070a00c518050341c450324420480c24446910107001b115015450201051043c61120f035031a1501d00350041c0d185c03003c403001c00b03c07050b102d90340c81100f9207040c0080c0c4c1600702160303004100c4c5c00d019034011754a40c1d400d03440070303024 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 564899451 1250 564898201 564898211
    0x105070804140c040c0504081002161b03050613120306032609090c12010b0f0307030b0f1504170a0c1e080706030207030f020a050a02060d021309060f060c0c09020d 72
    0x71134075036003d6402d000a1035561259903624058210303007401202c0207200c0c0e40c640100411201100c111a40400654206403003480203005104003191100d059840100075018000801c9400c6170162411111103000c0c07924503060080c3d6450846c2224030b1404024800d1304c2c0724403007014071000100c10452807040301046138070f4002600d00080410300112102000c42d50006807a0815100d4050014010705c0b0024a15041c041284510708180c00010000c004159a41000201c5c1c0c2e03a90100843d11140b0140401002c100090071850969000b4000c410024816105040c0701100014204409541120220340654103003102c08816840d514403d2036008040e20000c12205d409102040041909440c016604c92180c50302500c2041300f007050b5015074100d80401d101003000440c1c5101200d90480e2011b076509100c01c913a00c001e001740785a81c8884c041e03100002c00c4c0c040365640070030b0603520541034600d040780e61100111208680290020204001ba110402030f42d5031039000307864903c008043c00300e6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 564900701 1250 564899451 564899473
    0xa0b25050c190f0c061b081309020a0801050102160f14040b03030c0a05150f040204050403120c09080c0316170109080a05070b010510050f070c1d040302010509010507080414 76
    0x41400ca0301405440c100d444082d44000c10643c0144e0740d000302080c0c00c0c8100c00f000301d00224120b1110103640908000d0002420061118248450320050000d1240454075480409002082d00009010385d502504c00c11b844000e000100c07020810403510700782c2482c02124180303225000c0341c8040c1810690030680740c1c8429043c6030f409001a00680c01b003003000388031050083c100746260012103e0b034402c111001d130742130003003071079402c9401c60b072090b019903010440b40c9461404517580f84030810b007400c410703242200c0c54000310f038400c400303004441c40c0000b190b640c81d8000301010b40b910701040d082800f03540100810004600039070b030120500802d0400020700a141900d42c43c1141c2e219181d8500082d0000540104200801c01154054101564186007050442d4070241440c495803040c0c0844080c081100300801001c1442c040103800c0040350706800411285c1090504e01d01a01c00710099424800010145036052017510700c200d1181c0d03100201a1a640c560704802c111000a6510500986601c0c1c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 564901951 1250 564900701 564900733
    0x3030f0d0914120717030105010e06130e0112050106090509031b1f05070f03110f07060912090305060f0f01030b09010e0d0503060f091e13140a0b25050c 67
    0x20400010300e043d41d5403503809242200c036440b0107400340e612500c8248010700050743d1140c0015001d00c0b041c3c901e070384e0300c6140da0b9403802e0840c2150311084520703a0b2a4008502402c4100c58000ca09100f10b00a20407152075405183c00e6400450741410140e1003480414090f03071201202401d495905005e44080441c0c1c07103182891007550030040c2490b59150814401c0b01588982c3c82505003505180820516050005810301c1e03200b041100000380c0320124042003481a50ba21071226603078003e181d020035910810740079089440b81c0c0b01c01c0d2540c1c00f4050028664440d8040d40c3e520406a01e014005180e00315529401c69502c0075000d420159078802c0c0b54120741c402006426012a06600e0321038892a01c4010404404191030010780941e119000b48007201402c5841445900340190380da0440c1c1d52446040700c10b400c1e9810010f02050414002e9008000001c60340b040602e005141202040d9104400010b000b050850f00c08060760f02030074000c40d840e00c22805054181240741c181c0d42400b55070754600c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 564903201 1250 564901951 564901963
    0x324190510170c2d18040308130b161e020c0f180a110906030a02040f140d060e0c041a04150b160c05100c06060503030f0d0914 56
    0x544540700400140a440e01031076140c420120103400400e0340d2250100450701c0004410420401c02110400300709011203050301032641418080d182c40c0b030101764140841d004240c180c5003903002c41c5241d0041007034441e051b1032401800341c0002c2c40803219102c0300b1204601c4414040f80c0700400c40c9030b04800b42100c100701162443c0102682c0180400d9101c07400b0005001ea0401e48203120364119400341081d1140b50100d980d0140d00b0540006080740c41071007411052085051255011500104008201070654080c2064503408102d00c0c944070303211040244581d54011505611250759108080003a01a41150150421410548001c12b008001042c1691001d02d030b0004011b869403110082405d05118400c80300c4440359604100625000c44803150703100d00030803841030140c9000440140503003001c0035001042d01411440e0070752202d02c7e001b80014140c10040b900c0c0e504104e00010989400030542d520002c482c003038a89040400e041c1c082c0100304c44042169511501c0c2d8115031100014824 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 564904451 1250 564903201 564903211
    0x90a030b07020106180911030d0c030e030a08030907060207050303091e010e040c0c14030306010e0613081207121d060706110403050604020a0e0106050f0c1f0b0f03241905 75
    0x2003c00c0a551b03d03d84240c00003100340031540680d014860700240039902c0300c07007068110b4050074280c14002405011904040400c00040d0569000000b4000c20040c0081c46108a403000e609071104207440b00700301926481540740846d032150003040140305012186801d46140343c014102031410341030050128054071300d69030214000c2107016150070b090004c040709007501c41d404080507510314500480003900041c0034041d404e010b0140030548040d8a144c40e01032502504200c3c04880c60b4104602d0f000220368491003044404035182134541400318041c0b2061844540c00c042a000406c0d101000c0c00001c0d00a8002540c015864100501c20b0000200090000d035024001420042c540b500500042c0704842d070090f59550510740040041a51100a035000384001201d016502d01c07000d04524508003504280d0410351082901c0c1c06c002507996423002c01c204109581403243c2003c41c10403d922501c2910090000c046000740310301e902d1140c0707078505a001142c0480798140f80d0044100d6402c50b04202c030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 564905701 1250 564904451 564904499
    0x712030813061e0b01260402060706091b0503153603090a1a1e0c0f060604230402120102041d01140402040602033702061b090a030b07020106 62
    0xf91104100d480340c0a0780034803580a0030f00400c3c216091700741c00052106001b800c5100324814001c18119558203003290705207a0880e00900c40500241003541c29007110045080c600546010005142c0c103000c10008100c80203144003162594500c4081c803212400d40c40f01040351005000341000d42c1114607883c0e10508010401542c59000b0382c0103200c1c00d03d0030380d003260542d90b0455182c50340401b201000c4440748800080f07031900c09400c5405200d081d0040c2148101640604008810b840c100041c0c107034030501c0d080320140510091a00c040140a4079032420606141805000034054204050580b42040c110000117203400d50f11a01103468260380c0d51761240d0400e00d200100f000c00302050740408404011101180740c40c3c50040060750783c0c0301e0050043d00442407002c8002034403061101d00318030045c44ca03029030b15410680b000203441d4882111741d01203080c0060402d1062902c40002d41d240940058040408039080d03031103064070b69400502d000119074903204086a1049582c081da208500506 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 564906951 1250 564905701 564905741
    0xa0804140a060515060c030f0721170f060f010e0a03080310060906090f03020f04110315031c30110c0105060f06031602030c060903030906010602071203081306 70
    0x40c0505482040e041c4805100d07000074400501c8040d030102c108c03135155185410107075403129240f4081d006401c007115000c10f0910030f4002d0303210300f039001311210030803801c64005280c0c42c1e41c9145001000880642e64a80c10240044c03c1c0c2d1201e5008945034000550002d102404450741ca66405403103600460780401c02041d0900300304145904094100c2c080d0256041005220b030030b045401d68030035010b11000c1c0c801c0707007191101c04090b150361707218400900540d940f559507483c0800c145240d800c140c01e0721500074800d0034150400c1c030892066610103050180c1c0c07408900c140b0072108200c114214030f000361841a100744104008855407242c000d2185503c0b500c6520742511000d0309085500040003680180d040f0000e5000c25a21081180d030b001000c2e448510f00c1541030740089181d4055130300700340068803a80c410b110000303900101543c071a0403a14102c5580b03a803190f8081740c4524103403196003030601d040280381c00000d004144059000c080311800c44401d60071030b10344005451441c1c55025101a00c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 564908201 1250 564906951 564906961
    0x51b0f130603030206010608010810020918010320040b0a030f0507080d0c0204050703022b061e05030105091b041d0a121d0a0504090809060f030a1406060a0804140a0605 74
    0x6010086c01040d2601308550780303602d821003064480b00d02c68004041c40b54005108c1029a880044100301c1c1034040c43e40304100c1da10f81c82c181e41c0700c41020030448035801c4028262a2540360034001c007100c040c0b0152008442510b580c0d54007038903460007078048540e406694070120f603111040012008801450781c0320444481c040c01071008494014044408050042011003044c18045581040b1011111541c042400c0060b0551004100d03d40046603040040d06c8140600301c1c05a02140c2640c3d0110001c020944030225016a0b403c46284106118020039004084502c0c1961220130105030742d5412061402c180511282891410343d011240940350748148400c251b0b0251840c1c6100b682d07040b403d0891000d00000481c24242e80c420148510f41b6052040e0400262400303031801128007501e107070b456034640400c18184e80c2044618218440c40e212840c1100160240c1c002d00902010b4500c1e4902240e01b60700322400e8000600c15103681b020502c819a08500c1000341e0206280075a00c0000c0900301 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 564909451 1250 564908201 564908203
    0x210507030c05030609060d060e030d020c01110301030c1a0d021603030b0f010512091509070801140c031311151803211b010f27051b0f1306030302 64
    0x458a24441000002d0013040341588031a006240c200e0411540381322115040c3c0b4000014048520040c5428000440c004080444c1034018040c060000c4000f40420903011000503040e000c240300c00742c0411041c0c0c2040041008810f1031410380314200d920342d40340c03040107017010f030030303039001040246242c1c101030201014194103100381c5c3c50a12080b6104c100c0c0203c00c900081035401600d40020056001d800418030541701001310301000740000b920150680381242030a40c40f540944144040b6500f4062180c0181044080d000c1c4078441c03000c002421a00c4014410503007400180040340d803803182c921078840d40c1da914032202d86802c9280c250295500b4450394084040645160b00d5400b175407160080c02280103050a2000c0c100c52100150340c2c030350020b101040010800801024201d520f4040c08106043c0d0640200c2011a00c48252120382c004248110011010010001d00071750844100030184142103c414052002c00811a0440d048508006012440900342d8044143d9a80c4010820035030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 564910701 1250 564909451 564909461
    0x60d0b060a0f1707051c060302040c020309120106060219080702040609020414030f030d02210403020a06110a120203060102010f06080c030f0a050607141c0605040501151e21050703 79
    0x42c0f0391090300d150a00071805001c502588042c102e400410080301004d02e0001c0d0701c5130b001190000c0c41408040030b4000060744aa00c1400120b004070102c60030780e03c000d54140995021030b2100d5004002c481000411405941040c00003260003c104002030800340e541d038001c0c1c0001d003501820060b500d61500e000da44207000c032000d180780a0f421100a0b1912048040240c91100c02c25010242e50b80c40300384007a8403c120600d4023a240000442c05000c00c2c15800a24116103601c140d00c20030046901c0d0b0595161809041605000a92085071140c01c02c4040e401450304440180000710300c0700d00003800170f0280c41058100800d290b0003150002014a410805010301d210300802405c110302c90f54968540707444005196006020100552542c207600800031039103503d080f0300a147d5101011011100503100c90300c00e00d807090b0709101c000f0ad8411103f4013181407111302a1141d41d03c52814001015003100c03040c40c42c406012101700d41c44108241d030204960078594450001880e441c103407030058100ca07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 564911951 1250 564910701 564910727
    0x30307090807050a060507060902030c03060403050706060509060913080c03040314060109020a05030c030403210b03010e1c080a0e01091208010b040b12090c0402040f03031b11060d0b060a0f 83
    0x8003441d5041000d55040f10461f0140c1d90424000304561000d8000310f0f2810344101d919540510450040106140d444409172401c070748900d03020b1140d6950b071420051146c1055070200e90207411100415070b01041000c00e800035a20a1b11854101600c4070411402c540041e0300c1030f03c502d451994170003d840414481d030ba01400340756904604100c8064402801c6000c02880641da9142c000007150038107004102c944003908010b6490a07a1242464402000d0040d46900c2402503080100d2a0360072200070030003043c1907540344806000104040c4040325120b9000c0d1070300c601507036216070300c008205081c05441891402480400c891203410b00000b0b01c0510141d0001c07900100901050102100b100c0840704000c1141c0480003568070344c044210304040c90307100c4160740300b40700140c0010b0300701c40c10791581c2c116402602c0304e01440324400328614618520030401005603a448110f6a001e14021001d8194801e501c0e000040440000d00401c950798808420781020500c180c600748070712070340710800000e82 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 564913201 1250 564911951 564911959
    0x91f09061401140a0b0f2209150e16051602040902090406090c080109110f0f0d0b0a0c023c06010e01050f01050703021002030612030706050103060b0105040303080610030204030503030709080705 85
    0x2d44203006c103441c9400b8003400b0640003007602c103000c42880124680d040203469860300070040c000701000c416500460500c034400d4500c8103200041c502e900c48490ba40e12010007503e91034500f02c800c08982d0b82d09401100c04a0703200d580c03001c0c114050380725450003520071845070f10700203020022401d040400c0c10803580b22400680c10001f0013400140340030380480710420180c50301130861714a017000801c0190003094590300f12010001ca1418000d070500036600034110b0204c1000728408280d8100e03140c0c85440e0413840346004117180700042c12a0fa1000b4030303122110300c01c07030030f68031081103261800d202080e4400c4440c200c01100600040c58180c000a00714802401c05500d06151550701031345803044d8030303035900310f107030703001c000503085444400700c0d0b0480e03c03031300310070761b5640c001602c2e00b40018482800142e440503c0c02120401c2d81d4080c004950039607406443d0b100007503860034104022080c00310306034000c05400380000030006401308061800b600c2c07151503420ba028181010031349000080da200500c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 564914451 1250 564913201 564913207
    0x501080114160207030f03030212130219060815030c0d111503040f230a060204080607031104121104020c0a170a0509010809250e091f09061401140a0b 66
    0x42c150005082c40c100c1c0d42c400411410300c44681402d500900609801e2429090400100005200301d8081884540d10860703161240d07040d1441844410103841c09524085514100170070854024842c0e10313010044024100c842e10b102c240045100c0400148085030007907161440f03455146804032184038083d090303541d11070030741c601a141c000b0340010801002e0610201d18000300510f11406001003d101004002c07202120740d02d00d0001c000f940244683d5415025103008103224074440d00504030412166440c083c182424882c2c03206014118500440c4c40e40b0744841407007195110744c0040c22000401c0c4000d84001c400900700741d0040e5140c4100e607010b0b40e50400c00c4daa0700340d0b00082951a0031000f0310302400c850781d50711410307441c1100d542159451100b8a84490940b1212103000c1800d8a21a42c080105500e07243d68083e82d4502d5204025a00101c240c95414880401d40c00380e00d034180111070204410f240310940c643c1e441002c0c1c0020701c11045042c3d05881c14101501110b00070301000301807620f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 564915701 1250 564914451 564914491
    0x5120304150507081603060e09030a080105040903090e072c040b01020c030715050c011d0d030b060a0c02062101090b0603040f24060f0f0b0307021213090501080114 72
    0x4001301000384080840004803088041080c4264403c0e00900806d4294815034188455541d50303d810400c0d00c00000381b0302900202c1c3e0b5060900844040d5035040d290b008101c0c1c2800584440c42600824803c1000f501a141300784114034000e80000e2044186604e4503120300141c02d010a481450681d14190740c0300c041c0c1c40d096601c001494004440191808205a003c21a401c40e090b1042525118040d82043d01c007190500c008003401c1020fa5240040b20304940d40154160140ca20308440070707500481c10b00c440f4140074001c7d6200c241c0548001c2c800351a12480141d880000440607c100c4191b81400006000440781c0340703e08440030200310345036825032420755200640103c0c00d00000701384000c0786204007141c00144008010014200e4024070429071100724400c042c8415100c0e030003240c8420100058900110b000b20390040030940c1c0035014001c00000d8082c3d085d80034000403960301001e0180040d0b11800c40c8103242c0600f441c000040386980313041009011595000c1d00e021800380b00d03980011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 564916951 1250 564915701 564915707
    0x109050613020a1b1505180601060509010507080a020105010821071101020c100f080a1a0d1e0507140a150c08040e1501030606080108030a03150305120304150507 71
    0x14501c10070070402690781e00c8020002c0362107072030200c080c40580740b51809000410001c00c0c40c1540040807202c08001543e00e0364044404560419202401c1b41c01410050003003603c00c0c0000e01c00004c060400b40c0c504110390b50341030310550050303000100607552200144007401c01800b08081381000c03081045003144103a542c00c4090300c503546008150713602c050501d10059009000d081414000244a0307080c074403141d00040c02051000d800d00b400610401c0004610303902c03905c01e81818024920344111229242400c1c8052100034107030980d085010560000085103201240b140c8641c40359000d06000e0f03140a0003c422000d00e5007800307206058064091080300903102c0d81d644044501c0c40c200302002040d00388500d5503c1a03411121111820104001240c0640c0d1a020180711003a41c0c10007526540700003c450300b100a00440200341c004001c08070540e03100317030485514008000d4000280703d40e00d50780e492800f4040c030b550b954095000310401003440b10200e8030a000080c0c1c084144200d1400510007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 564918201 1250 564916951 564916969
    0x30102130b030a0b091305060c0a08130f050106092009060703121503030e090601090609050f0102030c010501080c191203111515040f0908040e09031e090901090506 72
    0x1403804140d000c00050f1020035250450020440080c041c10414140702e280420031030852041900c2e68450407021a880403005c0c1d04607461106656500101a20303003288007a481894100e080c0e0304c3d00da0400c808004079100784186402007031401c00c0010340c41140108815940111701940b0b1009905001d001c8003600c80101700c0319a81c0d81440c00440030302e40800b44900a100000c20b949031404642004020190081804500d0b201d00f01c03040c1d80281d6526004481a11041c066940021100d04003044541001074050580000500680c1d040540242c09542100c20980c0301d800f165215000000d400d007071607592504401c00c8814444145420f00c54213440a03040d00e603005041040070b020708070b5000c4091240c403e60240c48459481141008040e161940300402c005510440c644a2075150501039445505030140d4072501890a05160204504880d03000600d03000d0305020400c030b0071032103001ba19105152030020500c10798580490905120345428142c201508007490704c400d00806954200307413 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 564919451 1250 564918201 564918209
    0x1020c010c02030a230313050a0902191407060f05010314030f0301151e030c030e0307051231030302060708070219034802010f03091106070f06050603010213 69
    0x2a90f8885c4d41c0f50308018401041c2d086a8030300003c1078610104802c1c4030010200c40080310140401c54440c01800700701d2141400c800d000b152a90704401000340100400010003918210315403c1182588441069070140d061125045603540c00600810204100c0c070300415800d00000c40c20070b440c221a80d0f00512041c080c00120700c4480642c0c0342e00764400c10000d5425071050b2001c141c602080b03580500900099541880402d0501000040d820b00c000b054801e8640c0020051070381c4401d0600100f0294040715040c441d1400021039414038500056414031401c03100e1079101100e900c1d5040003400c0c444007030155820021680709120f8256030000d030000b20b0482e4003d40d01c100e024617103016120200361001d41200111444031031111503010143c441d42d05030130414910f00802c0e1a2940c240c490200c12402400309403286844484540310350300450382588683c1d48880e69590120000d02150001c290031101660488040d104102050140130f41080d0190025810300101d8a00c0506c65102401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 564920701 1250 564919451 564919463
    0x6010b0c0d140d0905011505190605090607020301050907090b0108040c050613030c0f0812040303081801060e0a020304060c0206090303310521040302012307061a01020c010c02030a 79
    0x107403010802c16600b00310b5024920805007080035a2442c0781c41400381101d003808802a00039054001818103000d50070102444183d00380103945820608156015000030004542141003441501c006840074414103026251800003040002d1903c900d04041d0340c183c50802c2d0400c8180c6d403d010019010454002c1512000c843c40307a01e40d4014140c0c010a000710794005000007807261400101c1d0003014900105a40700101901d03109000519000090b210720f1100400040001c00096034200503040c0f000041092900045810f60350b42c4144003580f039064030400d409660001c184070804c00030b84100002c0340d15a0001d02001d181c010841a100d000c024280340151411012143c003e01d04000c00c0752600d00c07040b0821248030143e0520540d83c04507481c0701c2c00c0c030808481d4803d605400c06015541100e6050392076039103018034034956045001c642010013003100018048140090941d00600c60420010001841c1501210b4002441c02c02d00c040001c0c1401810800c11003d81c1f004510059442c1d0481 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 564921951 1250 564920701 564920717
    0x913020604140409020907030c021908040605030c04090207150501050f09010911071b0f0f0b09010f0306120f0b06010507050c1917030304150b030d0c05071a040806010b0c0d 76
    0x1000c5409048183c0b0020b50001085003048051f0f074040d4085180305180c2d500300d0b219070344a46070340e05400d441464082c2c900401400104a460b10030030045a210b1080c60a0600301a614500c1c2c205a0b000380303400f15404464420806e82ca16114490741e801032074204c5411084c04114004036120340c5043c024113030159100d001b000e6903a072a1034203d50000340e000790266201e48021607000f0485290b809000760b00040d04600040382d02204510300c00f508d0b50740150500e8a8100001520010a40b403001410316032110740000e04460800c1c05440305c5405011030a0359080c2a1504100e601401041c10b8103020060001402140340002c0d01c4200c44002d0303a2800e503204036100710244c80310a6500482003141c007940d0300780c4141800f101440c0914440d00d48849507202c041803a000b0380b012800c00542642c006100c41c40264810310801001c1401102941c895940b100340b581000c40840c202401c043c480080c0c200900d18040200a0041c80304d40501402e0913005c0f5407003074460301c0c04103089080080d04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 564923201 1250 564921951 564921989
    0xe04090c12030c02030105060a0302100813080c030901200a02060706140c180d0b040b0417030901060501110309060301231e120c01081603020405031504020913020604 73
    0x21031818001c0c00540200c503408284516004103510020a0124041d500340b02c0402c0c0c85080078140700042c1c0c0d50003803018949a000b03403000c5942e001c0040007141007000c03400da13520100c0c0104000301705203889000a5691204004000362607182c291180344025814400c040000c014082250240c0e00c0e4102d070101e6403200c450604002030300e000030503080c3d11180041401072406c3e00000410581f00d01441d010200f803611000c010095640785400b90800c44860700280001e030001d459194020700c1174002c11841106081c0c10180e03900120b42598080e0356803407040c0103d40cbc100a80b0a4854030700f9004514044210000c22443d00041c8039810041e0000204801070300d604982001a1040c00303045040c5004000c044405481c07040d0801900070fa011044e4101e401001103008030310000181c41e206600c0e115542080d215141c060560010582c0c00d200106895500b400003038499075a04428034840d0a00e8010407040400140461041119035040e0070b0050b22540c3c10f60341118100d11101381600d2035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 564924451 1250 564923201 564923213
    0x180b06090c0906130e0109050f090c03030a050a1709030c070806060609041e110403110f011d122401150918060905090d030c18030f020a1e1806060e0409 67
    0x2540c00c40c0d4179080c1d409001040d85240b0b070380414825071040d106122940ca5001701a41c03128550390386560990000c02800c400103000358010101c4100900d41003c0302c0d000015024200d820075a03102d402c2e134100261342000344a08101031000f40944034081c01160400c03400040551092151180c01680c1398061038901080904000342150b03aa00020b00205458014056580d071280c0000c40d052200707400c169038942403440d0081000e00301a103a1000d807544079000810144202040c00c4e502421485c0082c01c3c05030280040003c0580c510b40c240220414485000c800a6050b002104190310000c603e03002c0c1a4441e030035800b260340c0c4154401c00303e01c0d0001c0c131002900c1d40317400610a0324180b82c10720854100004041c29810a1070342c0c02c2196080d55001183e240c3c0c8500e0703d17880d40a01c40d44081c0041510b08a8010a03644020308159803660b580410104d8000300303101401c10120560300400103a4101d1130082c551441c81c3c24101310f09400c5c000d01a19400e42503501c28002d0383d4404040f810495 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 564925701 1250 564924451 564924487
    0x20405031e1c02012c0d030902030f070605070b0105010c050a080d0b0901080a0308010f32030d080901180b22080418180c0303050a0c0204180b06090c0906 68
    0x2910040000e460b605804042e01030151104403040030900b62031000400c03d1410090142512414060031040040c2c160440140450400903641409840000c85070786c0000c0118000801480d228140c40c1d483c2810168802c0da4141d001e2418400101e6010001541c0455030a11080d400480da5445403048103840e4003c221a0b041c01e038200c80040d0020902000001c0c503011841c7c440d690340b4180e82e03200c215054035007050b8270900c00031079a0903175000300c1034900c035008210585034080119621050900080d18041383e1003040c4003c90400014803100704e00a00482103503640c010307900c0345400016602e00f4080c070fa004182074412550f003141d28814502583c07050010f80c0c1c01814050301c5030703203841c2ca94000074808958240d00034508106180010175801c04041555000003050903010308d581c0b810746065121102030400c0101c1640a880180c3e01c501c105184180a103446c004210850b14088140e2200580350500c01c99011003003007000e40e00441210011403003a200680c03036000c10b580713030a1104 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 564926951 1250 564925701 564925723
    0x1d041401050f0103061a01020c06071b14030706021b010f0c02030f2a060f0708130905010e0901020c100e1e0c0a050a18090314030403030606080901020405031e 70
    0x150030710040c40a11850888a10305a0b4000c400802c040d501a00c00702c08030450810740280580c018041410b400d02d800c5004c0c0820b140100c2c4121088002d8241c0c840c514903164204441740003a072040030461341410041e12000c1c200e00d0000300340302c1a22a00c0b551440074103010b10750400c40140710301703282036108514841001e039000c0d0485802038000200030342c1340c5100c441501e20049815159100402200c81700c00602000a0030040c50024180c1c07401140c0d074051582620311080400400081da004085400004c1c41d00240c005165410042e001828031009002011a68018800041d401201080f55131003410241c00008020880c450994107100b2514902e80385804060504010041c000c115007440304d034101d400301c560b280c03140d04004042c035460080324640400f01d941d0586407103840d405109800c1c040d04081915484103010300016601c12201100040d85445041101540100c800c0380c1217040280254146170410002c2239035407500061000c0c41c010030b00700060429005000080000c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 564928057 1106 564926951 564926953
    0x903030c0201051e0c031e010308090a0f230a17010203220302060411031c0509130209030c1c080c0f0d0302040e070c03300b0a1d0414 59
    0x140c00c014071146400c440407e014503000006190180214803030110300c0d9030340031864144614003016501884c0703035045129041c003da91044000e094019005042c03510542600701c006150315500d076201d80f2a4190b1800c1d880320054042d0010741c825014090941c0d100c000c6903200c0490356100c8a40640140c000c1800b24000400c0000a001c903401c0c0141100c0c0091001c2000706443c0c50f0710300680e00840c6000400d1641d908007112100310300c44601c0d41c01c608298124001c0382e20317400780c51040ca100e00d45600024416201c040043c1e5191a0400e028603100e84100f0179040c0c1c3c2d003001351003141440c071900070300e6010180f09000700e9094030110100840b5a407200e09040d20b61100c40742044003031000c11151074911455a4601481840701c0129010340c2524000c0710700200c800c0e40714241d00881d5084028447c07416500460701e0319541200c030003a1203585134109031f030010000c19065001 = true := by decide +kernel

theorem cover : BRFrame.Cov 564748201 564928057 := by
  have h0 := BRFrame.cov_init 564748201
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564748201 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 564748201 ≤ n) (h2 : n < 564928057) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
