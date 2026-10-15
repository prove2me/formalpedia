-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5010
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:27:06.438196+00:00
-- url     : https://prove2.me/submissions/538640ba-4283-4bf6-96a2-ec4bdeae178c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 900899280 ≤ n < 901079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 900900530 1250 900899280 900899287
    0x20309060304030f1806030e070e060a0b18130501140d05120703030e0601031a0a050c0a0509040e07031103251a22030204140f06120a210e010807020c06 67
    0x4135401044049002e082c40704054406503284d840180290480b40c46c1403c99200d0f040300002c0050480e5040c50064600600c0c8400142c90090384040581040818030310b010000d8141c0c0307425039103a0390400c050221120300400d20b585810314101c2072449802e2580d005850004450b80001d10100f071030381e1440d0f00281c02645402e01ca0070304400400340350b13200c070880c1e1050100100a00200024807503417850b041011070081d942c0e541e80e55040c2c5205903160b00c82e0220a10502000c1070180d40900f10070f0340051320004200032400003140c83c04c0311725881500c2e8244403c0d10142c103410203009c1071503000b440c0454841c440c40200c9444c0b5941c20316100703641d0040d805180115061130700314101c544031850b400125070f40461618400101c0c4000788402c81c491860601444c3c1c0c008003900359148a0203504000780903036500d0314244240a420b01070b01d407040e030050104510009040300c2c9420350380c071002d044080c001c81540401034000c51060500c513061001e000c00f00b0226983c0040e01c1c0c002c4003426140c40743c6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 900901780 1250 900900530 900900557
    0x1e0109170c0a03211508070609120201030207031b150e0f0a020609040e0708012304020d0204050a021306030509060f2208040f15020c040c09050d0203070e042102030906030403 77
    0x107804c100340d820311480c246030708500514000d00e034820554002c0416501d1640d665403041c3c400201902c9881600b03c45502d00e540998025400f03803150764000e040c0080580807000240588569020303040f01c3d12500c1100c6640840c101d441490101007400e00142500c6030640025940c1d4285000004c1c4103c0f4002510481a00e50340c101c4522016a0421075051031740740c0040d5806092142c040e080100c2284800d1482840c00c003031076500a64003d4030000b1907426640034003025100041030342010580800c5400406500410700e40000e003900c0d41d0005140c1040303861181000e8000c0c102c10580c00f8070909000601f0380300703101070016010f4044060045422880c7c2501d0b2405180e00c51400044c080000041c140c0d0b04030b00c0b00a401c1080c0e42524030b0319140004110440f110752000f400003a034100c0c0280094240084404600e40c0001c0407510640d40c3c1d0514011981c10171103044412040d07850380301c401245110715500000303a01c0d0028505020070400440c03202d0000800280400810190042 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 900903030 1250 900901780 900901817
    0x40c050f0a052101020a110c090705091c0b0901060303080c1305060d0609140f100609090b030715110d0201051605030601032a0f08090d0f021e0109170c0a03 69
    0x11043c11081c02951074840e03420010f08400c03800d0900800c98003030042c01d0605898100c82c45407080929448060420100c0350501c1501400398541c03400c0c03d8120303141013000c5a2009a403500c1008000004910fa0f4154035009002ca400038006003028030041c8a00c10004101880726003e07a0019982207448150302c0c80400d001d0003403a8801c424007440c01841c0c07141e90310000122803103082d401d0803034162900d03450f07107a0045c5050745c0718040c00513000190601c41c1d0001074000c031315401700003011519503c0e01c40b01c0341440180d001e544200421543c0901c1c80e6640e038280034030700030391400c0c3c0020016442c00d9020a05220184d020107005c0040001c00100345070701036031105590b050090f2441e00324040c44000182180e60800001002c1904011203450382440f42c00e00c54810b442050251140300030a440540e0506154240705041d4006c1c60709038200314004101d03d00051000000100d0304d01c505007401401c40020841c0c1d42c0c0451405c000405084000080d961031f05074ec10300d4541c030074078481407182 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 900904280 1250 900903030 900903079
    0x70504090f150b040b01020a02030d051c0e030c0c010206040b011806090207030e0a170717010617100f02090108060907020f0f030d063602071a040c050f0a05 69
    0x2c101c01000c60403032101c481c9a600c4018400c400740e40c100102d00b00e403001a03036a10103003080294180c0c04824880f001b10711440140c03407640c8410515500108022115000381c4604da081c2d01c5030340d440803420741d2000c0c001300588400b440003800507006c0c0d420151206c00c0142c80500070500c10b040c85511204c0b0103c00c92780120005e00d050503086444020b14900140102640f030503403840385c840c0c11000b081841c0b201409800f000503000043c02203900d400318800307020345540191851075603038200c00a00865000895540f04081402030121048141c01020072140c0302c2103285034071803050100311002c0c1d81001c03c6c1908180100c1d00c0403a00c2c3c1e1802c030100c0c03520791007c503034000600600301c50304004240000a400f007000001ca003800165124098080300385211645445112a440c0031854881e08802c8080191030b84100094540080e03034490600d0000412000c0b000c1e84640010041032041c0855000e000d064122070b81062910f1103030000309501d515019181c13107064100c400c0b12080c0c2084120 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 900905530 1250 900904280 900904283
    0x8070504061b0b0106080f090606011d0604270e0d0e120106080d0903140c033310090b03070303050406030f0213080604020a15080f1806010306020d0f0905070504090f 73
    0x5000f070a6845510040c290340040d204000030355806004540350b0000855600d02c240c006940d81e6500303c140412101b2510480060300d81c01c84001c01c0041450040c10f000444115401e00c019079076410f000b0141c50841c0ca14144440c055005a58810358141c4c0c40b4220400300c2d402101c3d40824890140c1072680144030300d902410561050f1800b0f07a11842d00700e8508400c0341d00130340c40b483e11020040c4c1d21a0300c0d4209007522590540290580611854412541203000b1088840241d260744690001c114560b000307450b0001c0040c100d580800070014980149075103402d040c1e015110a0b40345a030701070414000d81c01200181600c592044c41c0d41200e90f0b055074000d0090b41501121140d40340541500c8a909a9082c0d0040c05140e0300494050000c00c0d01403502c5d10180e45503105940c1e104a10340c860304010382a000c080390100c4401d40d40c1c100400260780170f18050000180d40d00740e802d007040200c847d4101454902c0e030a22401c440030800208001e400c075074080c1e80211328030020b0301d041e20004d00100300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 900906780 1250 900905530 900905543
    0x30813032106060f02071505071407030f020405160c021311031e0c03040c0b0703031419050108072607210521070f11030118021008070504061b 63
    0x1254500564241c02c4602140c10507107640a401d02c0e070482c102d880c0c551130300481c1c00510040781c1040005214034000c1c8030290040121240c02066081c0050500520341e1003614244d1100098406500d4076100d01c50708421804000d06401d54003002c05841e4900049020303115122a070340e04200c04a03682c00c1040220000002540c1e00e10384840e07950b0200c400d24005034840d0f12180c0c00a0142c6184c00110780c090f40c0c0080e02002e109140c0800441a90700c19602101055141c1d01c4481d07070710b541c1c455090b0140c09000c06e21459840c007983c0800031190164050350003540320a0041085081c002b03241300500e14510b9440c0e14032403038401c015241801e581e00500c8200c6d10038110301d003d04080401801c0b603034800c074191034127400c240029180c4400c802c100c070740e8040810010180080c036408071803001c603032003441c280521b0821080042d084070300740004200d500c801001c0800c110b03c2c04010076141c8412070705107032403241021000207255000d5401040240210788000040c8034803800c0700a414180d1081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 900908030 1250 900906780 900906827
    0x80603031b03030a0f050c180a0b030a02180a0513020912070618080c010504051002010b090c09093103210209030f0a1716050f0d1b03081303 62
    0x207040316900e6004907000400c261902400300d506401d140510f6008040f066181400e02c14400740151030400510000d07640030018480c00100c01c0000800b862046d1480900181c4031451030300e400c010039168000c0c00b482080340003828081580c1e000380b64140d512018000603100c104d4880812101e42c0e04481e842d07a81d20400e2400600e03550b0001ca540034140700d0150311444240e540345129030340c1ca100101070380810420b02c030601880c03e014140506204032417001081d030f4032003440070805410341a00c02d007002c04000205c02030181000f4120310307001141c03034a510415080c03080c950402e210340c00c0314001e80106c004420b6402d051003441449105d0020b061003541841020408400030750103517000340d020780581e0140103000724000c150081030304d8100461a480702e0044604000170b610130804101803000c04040c030b80104200b04008c14420212000600701181d0818000d40645c0c440d59040c0300000b40702d820000040d5004a00c035401844c40f01194142d00303600d1900390354000040310b00d80140031429 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 900909280 1250 900908030 900908077
    0x20040f0608010e0708011b0f3c0203070f060b0109030b1e09030702031f06232e080403030e0d030b01080a02130b090409050a0c050405010f0e0708060303 67
    0x190700c01c003d080e803801d081300c150307550b41d0804509a9030200c440806c0c131050365800400302c2d40a05400194484c047c68280e03000c0000d0802605034261200e4040440e66032400f01d082c50543d2034140c45c1c81131829000075403c10405a85418860340c0049000707181c152a00070110f00781e40a101c54102465129050010700e16000400341c0b03000e803212240141000c009008280a2000402240c000c4e54000e4090b00064a5032000107440703070051101085006e40d103003400204182d00300c02c24041d081e01401c41c5582d0320030b41c03030410820b0a07414820300121440407000c0d812443d003024120026048900b0700e02c9499a880c20241c0061080b144600d00030700801404407a41545a0310080d400d80e000d0725000c0350303522540701c00812809100e900c50b0803c074004609014103202e42c0c01034030301ca44000b08046031707149a036602c6500f084031242048804260540c3d083c015803905001d12805080080745000403185232082c0c0c54801b0002070142424803070100e000c64983c1d1418400c81e01c1d1f62602402c0c041d031a6802 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 900910530 1250 900909280 900909283
    0x13020c0303040818100816033308030a09151404061103041716060224063705010e090705070c05040e03041a0430170301060e03060420040f0608 63
    0x81740e503003100348140c800700c8080d10300900c62000040343c3c00c0010424030305400018040582582c2d402c0945009c0107c002422036002c00080503040f0f007568171440c803989000304100005c1030b099802c800b80240001c56030f170406268800d0f1400c4403142c3c039000740241010143d850031489030703411205640001001c1c5c00c0d42c5200004000192200ea441c2d202c010550300c601c120786811a0900415544250300744040e2071115039043c3e25040b04000701a02c40d8001e001c00c2d102c680c0c4061421154130007803043c1e901100c3c06c40048100008003404e0800e82c2c60758403c4000614003c1d0014500b1007030110114480042c84224034100c0e02508010303008100242e000b11643e50342e50014030800300c003030310403801e4990184950010340b0125020204404206a140c0c8241c520440030709001503034040340c60081101182c040c18450000c80e0516003a1079495040c01c1d001854024030100c1140079510039824040000c14040300490400c404600344c006d802242d20018010301000944460800d0905c0c4000c03451410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 900911780 1250 900910530 900910547
    0x402240a0c03021603030504140a050d0606050108070809150a0920040b04020c030a0807050f07060621171e040803090918060402060f04032013020c030304081810 71
    0x83d002c5a00300054811003461030030031400b0080009506000070407100c2078400310b5248000d80146200081c584132004900704040031002940e1880d222f010410065820035421508140700385420364040c50080d0050765940b890a0603030964039111700c00507400c0040b550052184c130341e01040f00700304101e0001c61130031105032060305544180d2070107050706018686882110007050b0b40070003950424502c24001d50b10104000d0141e014000c08014495100341d62000a00800b4071848000400a083c0b022780415007030f903440215420b1680301010008100c4c013403441001c0c110310704656a0b13900940080d04041013100d51001d1400d103804031f8082042000070003c2c00005c1c00503030741e4862581c1da50356124020b0001094181094100c0c4010401600300300c1300401414015840d1145003503940e030f5620700c0c09c3d9003207400d110081c10000548459481c014056440c031043e416425410002845420b0b9124800500000e003150700020b5070502580c086651051824030090090810482002000d0040c0e007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 900913030 1250 900911780 900911783
    0x30605030a0b090706020a1e1a09010218040b01080430021f0b0907050304081315030c020606220609060f06020c011d010305061207060c15060b030402240a0c 69
    0x4204c804a00b0610000742c114074550000050303103400403c02100c0c42869554030003034a06070b4070020a0000c0800740b07403819001e0901c9000060f518100c0800c10001d901c0040704462150741045034a074941da921405680c1c1290300454181c002c5240c49811071100c4844040c0402c4070f0b408034038803203070f42034000c03a501c2c00c07500203c41d20301d2030b01c20303415460030450750388105403030380280001c0100b08a80d03c141c028580c400c1c41070311b00f49d00d841c00d1244a1100034402e5488031380071a800c0900e0a11f9035501d8001e404016016000130706203820400001242c05070024485800d80043c180c40700d8044076141c10040c000c1c0442c11003048400e8441c05c035803602601c50b00480016104034040b01c61554400c41041409802900c40810b20182c80d100441c00f400000d042158481342c040e000312186241440158002c010b15241c0c80d01445c500c0c9804641308640900c8688810720b01a03040014551000460360f100360304481070380300e002d045258100c0d035030740c408040f00d081d040c04210b982a04e500107d01c40c4846 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 900914280 1250 900913030 900913033
    0xb041806060f0e1e040c230405100f0e03010207150b01090b0409180204020408064f140304050f090f040305071e0f1a1005100c020411130b0c1507030605030a0b09 71
    0x344487c00410142c4618403495070064414140c801e0164818204100304030b016182c0f204925079204006800c3e41c0100c1002c0d600f40c20109072816160342d0354071824000400a0800c4401c90b0301d4114041c01500680c801c0010103500c6544020092800c1c03101c800a80c1e80c000c10840d00c40742c480d400c5581d50501114200700302c07901100c003010141c84003030300194940c005070070b4994510444550b40e0844200980c10244181100c0542030010361015002240190400700440d2501d01d00420000400341c035410031070041d03807100248602c032100b101c030443d80103425040c17181ea40c061500e0301d59001c01c0454106844012152002400c114000f034500349400d00405c1d01c6100c00e07412104142d8014000da4104005c9500190100100c0c04d0444070f400301c020b05410440b81621054020500342da21241d24201c60290010340d500c66410500c16107409041c501060506011300c00c45010390f101d10800f0018482c5075510700240f82d9602c40d4011201414011f03090b6594884180380411344068196581800d5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 900915530 1250 900914280 900914327
    0x10b040207080706060503030316030c0e1f09120308010e0c090d0807050d030501050913080d020f0c100c0c060b03070b0a02030a090806100314070b041806060f0e1e040c 74
    0x59203400009e0341d0152003401528440d10401345020742c010284540e094080c0b010b1340e03080035003039561903200c0100c2418149044600c803040303800040600c8129085144405100e800440209511652032815903046032010350881e29405d40c560058081c1c10305965000c903260b814030007045121009000540c1c4500c04486a1415140c801d0701694824064940c121001000040c0f0501e101e15022201a0090030301d185850b5040e10150700b40e0b448400440ca070004001085004032200300300c1c9007040400e0040412014294140c000c2281040071005403201d03440c0c1030028003c0c0d4007485550300424213249c901d9075074061801e019440350000d04006001c13500501001a020300d000c00d070903200703a000c119090000e90a650310004444030018071030ad03003842042d0300800d403c0d581b8401000138140b2052001a900a100c06840a60707103948c02a408100d031002d00304e15016080610035a008401300e030102c240848101500d00c0c0758540014240e07010323040c21458094107800c100310802c20f20504507007055 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 900916780 1250 900915530 900915539
    0x210b0607290f0105130f0f150314010e060712060f06031e0b13020a02030c0712020907050a09120516140f041b0507031106010801150602210c010b04020708070606 71
    0x10541004d00c611900500020070b800a03c0700f080c1d11484404a29450001c0c031901119100000c45890020b00007103102c80540034410702c1003e041d919a010230600c002d0006556020420784c9818001c2d12203400e1000c203400300006200103030004c1c40540140b0a00c108401e40d6401b0050140c04900c1191880a90066410313000000b1405074040f01440a1b02c040d640703103604840e9800a52080c5469011800b00b4003540a51001c140034503001004070008216480b0811300400c10390703400140520081c041c040050394000c03904180303920101d0301c2140006104c043c2030b040c01810301c0400000054803074403070107020402840360510f01d1072443c000e840121842d00c5d440e0a00c4211080d950100518522010003041e07000d110b0710080280900c24584160500000b05000307190074070a810001c050303511411032910700d824030300740800140900d10081061010002402409001c24030340031508180c00900341e1309580d025044a02e009001500456884c2030909010701c094000240889035141010400103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 900918030 1250 900916780 900916801
    0x302131403070506030703090b161106011202190b030a0504031d0625050316030f0801140409052a1323060406030204020721210b060729 60
    0x640380c110140040c00090b04020800030180c0008040d1010540c03107140f00400140c2c5081a580152544a0106081942850040c1a601d10600e1104040d070104c001088181e004c020b440a05075010341d102e500315550502a4411a0002e0f000440b5800000090001ca409143d000c94401d600a65a01c2d001c920020408089140b035003400b1544001c0a01c400040f583c10041c0d10101c040059040300d5992081d40d4415065420075070701c90740324400c904840003e158000418080d035484600c0c00141a604004000b240c1c0c0ca500c242c5076000301e0b5916021001c10800f08056154003003490480b401e050700c075910340a081c8081940680c058080010304d0314107184035000d0020300301d480500e0340d01c40c41280750028180001c003c2070035501c552104030007c003507210781c4000c2c52924001d004803d03403080c6440d0010301e60f90031502c13810200407203880300b13129804007613aa0b9250295400c101140e8049a080013a0701405800d00c00f8084001ca90302c0d48070003e025120036004002d400083c0d4000f560303003400030b5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 900919280 1250 900918030 900918059
    0x40501031128060503130f080a14070c030f020a1a2d030c070312060611060709031e02030a080c0601321315030537110619030213 57
    0x5a804a0881d02c28003529001d0f1002d142c0c0040001c5101c03a078140c1c0c6450710344888200308401c1c1c4151000142420312282d014540f101c1d80080030080070b26050307550ba6107401403110791001419508030a0100811035071005c2e83c102c000c000b02c0d00d010506d09400d50041286a0210440d0940303502c00450078003144400c2c0902c0790310f2035414607040c1d06554031412039094980c442d241c200c0130002c0c05880050b10801070321801029114503607814428000090013a89007050241030f80d0144043c2040800004411420400b40421104807080400e512840801d140009040c4000c0c030341304002c181c9050442000a41138100d5039868050004032201e00c81070170904140f03055102c074104103c400f40326a400e00e1900102070300d44440000034910b0451401054003880d50300101c5042d0800c00c041042001c0c9101d5100c01ca2103280c0d41d18000c0c0040b04d02c155021451000000d0403414601182140c5503610005c6c5c0b8900045c480340c0c403030802108074008000354010b600489414130300750400700791000004080c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 900920530 1250 900919280 900919339
    0xc1006091a0a0605130806070f03242102040212090601170d030c1e110601081617030c030a0e01090e09060403080a020c010903050d060e0c0406030b040b0405010311 72
    0xba8500141004012a50f907030090340115141c000a2000080320802081290700c100726680d1f0703000044160341d200070140c40c00401e40c3c1700c07030442c00c4003092110303a00002d100d0102e0704180442081c0050402980300c4251000c070f4040d51051001c01c10343d4040001e20f1910b4801c00c1d0712010358405a80314550100c41d501000e202103141e07442041a4541d031030195010301807104050a021081c2480d196084009000e041e84080014003101d00941d082e140421986015042c00f0002d4003840303140154803e21000a0311810051013104a0100080b0800344215501d04031000d0030780343c0d01c128140e4080c1500b090070100500245c0d4a240010307032059003118040c012001d800103404140c071545c07002c60389424003414442d16280d08001c1c541084409100d84503e10344644c403099102d11300d8810007000c413103459010882c00d094030300030090701e98989000c41e0241c07001800c00141022110001c500108981c03900ba941045c0703002c0010050140100080c01504400c031030040134030941c03801d08070701040c2c00500f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 900921780 1250 900920530 900920539
    0x5060102420c191b080d050f0106021b06070506010f0807060215130c051002280c27090b06120127030203120c220e130204020c1006091a 60
    0x14030034901880440100700f0f42c0b280c540803082c0c414112181c0c40801d00c11104851445000466062000e958059170740e05c40030714100041c0e01c4d03140c400040d460300001c09400004070000140c0e504566944c6064402c01c1d0780140403100c071580c50b0a02c0c44500086402003990900c540c03940020020300c0000c5801401c20281900b0f40b01c0e460300110101071100240045031180c2100201207880d84441c10004801805607004100b1030b403584c002c1c800c0350385118019000640d070044074680810500e0503801e04559600389801010444110200c850f400c0c410614000a81811624070600001e904010700a00d4210703405c9642c4d1015408150881c2c400403042d0b100b003281503250a10061410480d0f509c982e0103401520300d418802c8001c106a240304a07030b015500745c400b140b40200c2940c0d0244941f003070400c001178140058100343c81d003545c3e44801041e00b1a80e1942c180d8480454950f42c0603141e900280c1001c41c0ca000010b1544807014103901c2c0160081c040ca850004400300c420040c40c887c59010150 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 900923030 1250 900921780 900921787
    0xc040602101e0e0f0f0607030c0c0209070c080f0304061409010c0e061e0d090b070810210204090b0f07090e0a09021504060c030206060a031505060102420c 68
    0x120504050f00c40c5400c1d0040e18000e203c0f00111800d0f0a02c2400c00052158010b418030780751000028049a07100403414003000013112045005803900d04429400088506251044251610b4880000e00c1a44403081c01d500703022051104014240d081a00480c01040406603a0b82e251513505080b070302d8082031100040c0c806800c02c43c0038100717600204590ba40c040130403000d0380b40e0311503500702d20391000c50075802a60b5100b0b411018440100c0c201238010000340740c040c10340c0c20001c824081501d8507014204060514034540d640201c85002c0002c0001e6003d007080c00900401d00300100c0e110070840701149298030300c02c00994607d225400200c203580d0300c0e02d1041800d44408150000419281c0b5040780c003c1c040351000e429880030000031700000d104a503030360a100201461300901300325000c1d040300e01038602818103200050f9a0031540c101540b01200014556554900403072030800e440b22242c152a030740d01d00180c0000540c003440c1e010750302054404030b950751000d00c00055000d4101c1d40c3c0b40c0c82ca003050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 900924280 1250 900923030 900923081
    0x6030a060f06090908030f1602100b01091505030a0b0103050106050a030513021c1205091315150203091203040b0703080a0902060d27021f05070b0c04060210 69
    0x5a1000300c0401c1444400615242c44080b03d01c21142e0000d020795a0901c040b08000034409020311213540321028100c118000b440500000e50765031403104500710090345070800c5400a920885c4900010122203890545035440e48101901d954400e03109500c2c02428030700c16110340d50207130103002c0c12038056645013441d06145c403000700c00602c0c02600364400384898071071500240c2c0c2c92003540c1d51003661742c840400354145a850a0340c2d0344010407030704800b070003002d00281c54a030351032400c0e401842c181c130400072400a4085c040000d1031009034222420482981013003c558580c0080908107078202915881c600d180c0918400d0381d60301a5100b404601c403010019040003078424110707140c00040248012400c001690300040e40b1381c105103045850b095aa50780180410b81280461601c07804a00c00c04101a0722500851410040c0d42400c64080580300444180540300d801205c040c1e9800613105100b5060482d45442c848d440f501ca8a0010b01c06d941c0e000d8110883c41c8a4844a069040046a682c3c84c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 900925530 1250 900924280 900924293
    0x402131119090b030414060a0b01140d0e0a080d061d010312111002090a0603020c0703030f1209050d081b091306150c02150c070b1812060601080f06030a 67
    0x1842044020819032440003e090745030100554000c2d07120786000c101186c03210311402d103400f074001d08521074542000800c030a0350360800c2c3c050700190008140160340b510186090006807402130541180391046200711000d03c07005d440544281c0d40403050034060180e48010020300d1581d00309540e801c1c402400010400540e119414401000150400154a0074203c0183e82000c0410010207036041c1c00180c004031614000084a000e030146040460406032a02d0b0660340d294114080101881860200341c8402405225a103219400d101401d11007112a0702c0c149441e800030300700c40da01040c1601c0101d90311600d2001140c1050403109a01c0c0d04107074060081001150308a10128800d43ea03e0f0400700702001805444d030304a050548583c0307440c5400c2d00c1803140200d140c80140e10710020601410041c11000300303010045880c004401a101c000505d00340041413084080070b540040d20101308a031165000c40c00900c240c80c241c03120300c02a641c0c01141c000360b40c41115000c0c2d0682022030003600080c0c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 900926780 1250 900925530 900925567
    0xa0e06030a05013b0702010b0a06051903060803070f111e030106150c030e0f06070302061f151d18040506090d090e04050f0601060203091f08041e150504021311 70
    0x110f480042390034110400480da40d00b0091700664005200083c10381d851048004c510311514000f031804100840c9082c10082e01d0b8041c0100c000c20444071074900005000321225030380801c440c0104a903d040c00c0f42c0c80c4540c0c00541501001b4080d5007080400581d041944207101c0c0146010303208c0c0004141603950485454011607121544600340e8030400c01d030358407040054500d03588070380c00920301c13420701000495038021401d4140b001c961950009004448007081105612046814a1140350a50610884490190101c1241c10031903900381011808111800940124000c80699003103884549480e9111082030600c0000b1941c007440c1007141d403003003134101c90b4001d020b00182d40c418a1a0603030305040c1fa800f030f848240168408254180d03d803510f450220089902d40b1000007441c09040005031510714000d00c050101040004510300c040c000040142217907038030200b003101070050320b81840020710085d20241c2c001c000c64a10300203440c0c0341c1d105180b07001605000362170511503001c4e10032080347e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 900928030 1250 900926780 900926791
    0x308060907090306320402011d030c030a0803040209010b03060907050f070b101503091211100c030614030a021f02070806010807080d08010b0a050a0e06030a05013b 72
    0x3150800008280c143c0b14501058220001c0640c03040310702e10561510794010f00180c1c0d1525014011b202c0141c0c1c00c000000016151a001045005500400a81015028620a1f4250140d0300c100d40400c00324100441c40b8920072520320800d81d0300c80d40c002c0c0e00b500080384c0c03207900183c0220110700a20702440150020412400207280f400100785d803408841d80059807858030010000c070b0148400c8082e034407441e6001c9107038581085200c0007034681080102444103801c003800740c5602c0c2c8507080e103000d0081d42d8100704504420300c190b40c0311020080051100d44104031a00e5211031030f100e490f28012443e0700f41190014200c000b84060010006030440026036901c1c00d51040c00c02c00038100340b09100315402040442c0140081501e0b00e43c1280c1003051440c64141005001c20042c0212070070a8180c0b180500189041c0c1d4440341414400d4426142c1d03c0c04595010502004010009840d5004241691070f4005080c150f0161040b8900160340d031900c00c0d0a41c030002c3d5008980c490707511540d01744d000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 900929280 1250 900928030 900928037
    0xc040504020607080d06060905100804140f0d090e060d0312050c0d06060503090114011a0901120203010b03090f0d02030405010c15050108030307110703031407031106010b0a02070b070308060907 85
    0x603e643e5a95860f07600c0003140b8084192520f40810490340c114a1010041009480c40108484054030041c68950700410040408000c54a506103d8004000380c04043d0f8403041140c00700c0700140409802a613461003000032601131007002401c2402c1510940c6d0000c0ea00d03840380003900c8034030750ba10300c0940320040025000300020b00011003204120700400005180c0e0b62034140d40c0b4104420880d0950700e40c00000005030f94403800401494a588048040c50003560340d0080c0c5481600c0012200c1c59224030421074032900200010510381c0300e08000314006c19102c000c84000e514140c2c0c2d12034880c800120000c1c05600180010006940101c100301c450a200b81542e9130000c81c8205060100c41d020303017181c1d840d03034804000c00400701d400039441501c5c4819003004000700d07441c5990040a141c1d8400740c0203c44000480c0310300815004990480740d5001a034140c4046603112a21003c094024000100042c814410001980800c80c01240d841c40d42690307a181880d51040280034107000090828002c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 900930530 1250 900929280 900929287
    0xb07150e100906141612090204090b0609060d05100c0521071103070209011511070612060e060d020d0312091b0518072604050a0b07110c0405040206 65
    0x180c40038407000d401c03841c881d0800503200507141000c40459041c090503000c4080c1e00d81c00d210fa00321000301400302010040c58101881200d0030100c0c40a0b007a1690001c0d00581031062500c00c1084809466104480c2a5045401542c4070410001c0c468160a000390654010720381b40070301b0100a0b005900b83e036116042c69882c00c902074a0b01c88903154500103070a20105940d0501840320392041d000b50030028a4401141000c220b42c0001d41042018800c48215104183c0450031250040c0341c6c40042002c06000c2c0c4070f506603141e00251904103091100355910389441404aa610ba015003413070f001d0324020f090b00700d03c010142e0a000e111a184c020507414080310700c0074481702402c280a008107148c441c004a00000c030301c41c5081042442c207900b01500c2010407116822000758280b06590f403180403403800028210030036180c010b4001c01c14100b04040c64128040005100300000c54002480c800c2c0441c00c05541c4d1408116980002e200c0214200c1d00003400c00e645c0c51502e90030040d00300d800108021324 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 900931780 1250 900930530 900930551
    0x90d0e1c0c090507020c0612010509040606032f060a17182b05090303031306021b1e01180b090c120a0c090614060309100e0304030b0702070b0715 64
    0xc0a07115031002c10015125000c10800981c144a5622800c0c5d054075024244040c40b510b50341001c50502585028090b440009414001141c120b00000c6811401d00c02c002c0e0036070307a18051200e21500201ca00f01c040700108103a113082100c12154100e20a070784c0c0c200740482d05042400242c41c05443d00180002014400120362403c2c040c890307400342ea01c000b495104511700103040c0c0000102601c0c00522200384a80c907803646010040b40d0b802804c4c0404418102d1142c607009001780200d14000c2c1030100450f042d07076611800001e22203034911307030300c807d1401080c0c020801c6800c0c1d500002007920561901d192100002d440305031042c2d040740e0b882d0160390741c1e06140030215042e02150400710051b940100c0030342c814000e0700e984400141642000c02c0c023a4034204070414000042010407039004000000c00138101d14014400310510780306200313050150008040301d44d83d80383c1180c003095500050400c007103030109000042c40f0048421042c3c1d040e0401040d5114250101a502c400c01811360701c82c2030441 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 900933030 1250 900931780 900931793
    0xf03011d06060901030c06050721020c04060b130b0d0f050f01061112030c0906040b2107081501050c210301060f02010b03030f03280207020405090d0e1c 67
    0x46840403580410104001080d80545001805000d0741d004444803c014400b06004400001c240e5009082442e0355122618100380c50b01c1c0c03017441d007000c52000028001040c540c04103100c81410b400b103030144641a10340945080d98858000401c0d00d032105c04004100911011010704443c60310791000081c4514810300d18070503103404a810204040c0d0510040c4602038010341e440500415100c001e2125142445a03410b00b84006064850600c80204d81d40b01aa80c8610884e0060841c4415540d16816408500f0680b04500004a02e80c100c00b10300084110307100e01c162a1140d04e0f45030500414200590042d2201d40c40240100c14034003540740d80707074030402d022180342c41ea400c410481c9540e6585402402004015208400070031a414400109281d42e03002080c1c03204040000000d44d503d071181070600c83c240103406040b203055080e41016102c00300d450f5002d801003500940e4284015030300c54440d20b8031342c2103c00c0324401160b40c201d400b803c1401c1c603941d40c001d43d09076080c07000780d428010303240d01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 900934280 1250 900933030 900933041
    0xd200a0c0303080718031b0b04090c0e0d0803070513091406030f1906020a02010b031006050907050a0804060b03012306120606010801031401061211090121020105090f0301 75
    0x1034a0942044404108040d030149025600c8500351920f414140c510103000c0712200312a00c8068810380ba4940c04207040020560503000510315080001e135907640c0d4400c540080c2940c0c90304080419542140d20760682440700c10f611506601410213459a030310382005450580203541c48002d0500800001300780201c507440ad109070000042d60030307005841c204041528009007640540c41c2501306906442545150303803d04040507501c0b41d000350300d5014007081280145501c050041d4035105820450b0103403041da901807001c2e6001914842e40301c1d61088802e454511801d01c0c200700092003480001e021402e00e034811804030000600100d084980c0703200d07000d00c5003c0034103054a40c0e2190418000c162611020009540007444003802c07580ca001c0f400078010944c14400030301116848084e40769003140a5104c100a02500002c50410640c1c40c2030500b4001084d5084500651640001007003032001440940785007481884410810072499004480d107411002e413072600401c0310300c00403400340e4003030050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 900935530 1250 900934280 900934283
    0x50c070906091406040c020304090b06070204180c231207080313090b150708071113091e2d0b090307050d110303010302011b02090901051b0c0d200a 65
    0x200750b601000f0349207940820083c140b44d11031882d04001051241d004003d90341100c81801e800284070525001103076052040c941d0007544540380400d06403609542c00c1e4225065402800c01d102403946805c034080e07107281628000c080a95001d0788002c49442d0002d100c1040032980802c0d13030343c21030f9100515481c6801000d0401841d60306800180120341103440350b842c26040c00c0f141d00402d42035000a80810f4498a107000e410360b18001200b40c01e002d400f1114900c4044040c1a20032651440d03146c0c00c0040960f20011980744a0205a0942500f03581d01c01c980c455401c40c0366000c0e4141c0ca440a44440d44201440000324490400e00202052112070417901c107610b0040656900e01e050314042c0e003026401404101070258100c055448000d0000c1564192642824880c0c06e50131040d075503950358002508000d41c481b9151040000452040d000340b4000d519806608030101a981d603082c000e0f016044004200340d21610000806601c42c04000000c82940c035034243e81250b4200d007860500444040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 900936780 1250 900935530 900935549
    0x10e270d0215010e01092708190c02311e11070305040510090b0c1606140f090a0305100506090703021c0504150204080f0d050c03030106050c070906 65
    0x840c2403a8060119984031009048200019030400c0b80903c0c2d0040f0601403100c000d0344d1807441d28805801040c6000c650040700140d501035200c0e80c030341291280e00510205500988203001c011626000c3e0600071030301d56000f011030140c8e1042510440c90540c803402d144280d40e60b03c60448540780031034410740320807a865100c618901d01013200200250741c1200c1c09019054010800100440e0340036054800b6100c0843707901c82c981d1030456080f00d01d980c1c2c1da00491282040043c1d421300100001903248929891b04103240702d019a601810745401c40c43c0345030642c07000000c01018000b41040001003203803400041518211035180c1c0c40e40ea03c3c01004001741070070301d42d840007071200c0307860b062910356405040c038901903140115145001030300240340c140051030162a10040303020800310503040d503401c07800e041003107440d1660b600e1002e80e43c201040c0700341c01600808100e10740451250013180d5555803a24025407450340fa1034000c5485a00a01c1c143c1c0281c003604c00e0110b62221240038444c002c00d003007113 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 900938030 1250 900936780 900936793
    0x30e040f111306020705030601030f0201050405041107020a090204060c030e1f020604031d0a03060b040f02031f050303030601200c100503180c0f0d080705030d0507120b09010e27 78
    0x399034003220b03505030010000c0d50b101c2402004241e030f000441d207041d60f510560714402001103100507100da01841c0c0015a0080c10211a204a0034440b4041e00c20030b070085030601e501c80e0790b4521050403032156008110002d6240e00280340424007450f40c03020b0144024014034050404228086000883c0081a0f0010780001c8140814150b0090081900031580e024800707104080c8000a0040304481c840141140e856818141c2c2035600c84e0700c864032081c2e43d003109550780d180c80c4400c0e26582044a00145840e9450003000c20b42b802c0000036030780b00d03900c107071030b8405072251a1140000c0c04107213681c81119072003003038015031068469114040c02c8128a0300c0d000d0f241d0a042c818090007034100210b48605500c90a014212650791520100d01c0d0042514030b004155280d05104000c0d204060002d00781e0300c000078500003450016480984100c080e43d031600030f0510001c00c44c0058494610009500c58007010040c007407207855088450300046a030202200c2d4440181150311104000380d1100010b8200c074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 900939280 1250 900938030 900938047
    0xe060d090524070f08091606051908100b030c0d0c1d09090d08070221190507050c0f040207050f070509070201021c0f0209060c0a1e050a030e040f11 65
    0x151400702c2c0070080202181d014507114600401d01d40d15074502d4000c002c84000810713500201408401c00c8560b1280805442c3ca482c0c82001d046a8042c1407001c040b035228100741c031042445104d026001e02424003c0ba0320f100d00d0000c96614903003002e850040d48400800c203101c0746801c9441003000902e040e4882e4040710090900702a010259401841d000304045801c1000d001001f24940503901881c4c02e00381c409868081c8120b140c0080802c899000800d95038441d5201c407200c2003d440e280c10105001030454040440071100c40c021641c006005030b001d0041c0c1e502c94a4107146202040e000504010705240c0e058031041e25200400141d00101d4121000c00e00c00e504020300c40c10344c00721081c00258586a02c011142c110000c031f40817035078116580c8030341180c0c210f07519404480b00c40300010040c0f5103440b008905951180340d600011641601c0203505014001e6141700c0011840750050050022003045880649104948000d2030741d205960f00322400b42d07082d4902c02ca1790150301c0200101e4549898 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 900940530 1250 900939280 900939313
    0x902040501090902010c0b040c08030408100c0906050d0209030a020a090c08162a020901030b250804080901120c020708061003050a0f05011e0912080411010e060d0905 73
    0x10b0304460345482c1007003070050243c5d801c4040b0a05080e803010856200ea40d40d824085808000398008411a02000600085082001030001404141520100100200c542c0c080d00d6800c041e10944000c06c006000140d008040c81d8060a01410090241e0321855602d0780010480407080d0042034465a5071076079042903990040c281079004d0307401c2c2490020f100002c03034090245101c007a411655600d400c02981038007904041102d20380d43d80a004450196120b103498900c0c5142225076022010802500d6503403d00310010507007044540c6c0d01c3c0d8805580b6284c80e8011242e1198607103e0502c51a44085a00c407115445041800c1280c1d0b4007402d140e030308204079607081c044081c103402c44901081c5070074404194007140c9101c8403940440c0d481041d0400b0301c0c1c06805820746401c40607125414000610b14840160880c4402c0c503c40d651a6002d000c03003100076a41001c080e01c01400c0d000c4c503282a00240e5020f03081e607180328207008007a6801e10517450007003800e4800c00c1070112a141c200c0034869070307502c40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 900941780 1250 900940530 900940541
    0x40b0703020f07180c030905060a020304021005030615030c0c0d050904060e0c0d2004030320060405070501050c0f100b0a080703200609040513032a0f03050f03010306090204 76
    0x14114060000f0f18a4800c1c01e802a030344000141c402c041e0303034190111300c080c0031b40e00c502081036125042e58424501030901c0c40003500202e0302680200e0340b901c0c041e00042d2003402200d1003101c00810965440282a00c4170f5420f400c02806454004010022031900c03c40410250001c00200d54503140d45506540610090b0740e110b5100071100c480c984d0505c14090f6550060b0344035a144020002502e05a88521601e800c0c00503040d6960f007480050b0101c00d0550081900907a106c103403045120f40e20b40c4c8210300341d40e640101c0b00a00182c003c60300c20b11180d88030700000d00483d01501c00311103651740c7c4030078442d0408003040d43e2405050341c1c1e404101d08600b04424044010b0103224041c0000c42c0ca182c86951440401e4540300c6c10086501d0a0507000340e9442d403c0e921200c002130400c0156281c2039668000b5130a04000a4021401c00780010300c59a81a01c41e0210301402100d00c411500295603900d4441c0c81040c104805100040c05030005401001740598020360080001180100042c0103000c1101d5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 900943030 1250 900941780 900941803
    0x28140718060b070b060301060e01080105010602010c14160309050402180a06020a03021b01030612030203180301020922060306050702100b060901050a1b08270a030308060d05030c03040b070302 84
    0x741000700810900c007442081d80d440c507070010022030550303445c0c4000a004001d15001002c0d0904101e0010854603015840309050700c11640080101c0811003070b0665105000c0d4280c0038040804000d8400f10404002c4210f0701e4074841e042042c01d40761190002016604a620504c83c0c25446035a500036a151104209004007014009060424020b40700252100b0b807001e03c0fa1b5040c0c0c407080b81210f059210350b10420040042c81c40118aa20840c90029169800303c0c0e540040301200070104940b928040c421104415002000044240204040006c1c040c160328000d810042d524000003000c102a40a414400c5180354081d0a00301401904001110729151b1214042c100901c81c00545903009400c680c240e40d07050070003c8400c0c2006441c011225640e10000b060144045015050200d08040485039540e20804180b90422140240031075400348c1d11002e0300150080e00030445c2030420810710400a0b0145099900c1d100700401035910759480f59021084d201070001d103100500d54140045807070507 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 900944280 1250 900943030 900943079
    0x11060703200c1504030309230411070219050a171608010c0206010f031101050f07020a030308061c02030303010b031009090c05011d010806010f02030c1006050a1205281407 75
    0xd82186c4000b0000c100354050410680d40101c02240c0b108103803800140c480100170300c00c1c899403046100110140d00010022070081307a1006008600e1002600d082c4250359024081e28010351410306c8062100d89038051403152802250000e03160702400800b0003010303042540002c9881502004000d2500c90140d01200c5014081c510620000d2024480807007140401d107005521400c2d001c1a80a0074400c9020095000c036402900004050304500201d204034821114900d504606005401480c850f598009516410400051002d003500102640d0448500940362010307d4031160306070211002c0351801da0344940084c00c100010f6034011200a2150f0040003413800c03010a54001820b9100080c000d24103000f40c8204020b0f02070b100308181c0d0303074418180d0200d440400703000350b20400070700c11030280601503410450041400809400020041588400200500f003400180313003612107a040c03140800d48040f091075102081e210075101050070310100160a10b1450b11109524461000e61141c909 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 900945530 1250 900944280 900944287
    0x9020c0105040b45010e070609061404300c05100e100c050f030f0403061409100504170423030c0307030213060906180c02030711060703200c15 63
    0x500c61000c1000c202d882c440c2c402c200200f0358000583e800b03400d00c2d03504d908990b182a0040c1001d400001e501e804480c0c454840380101911a50304076510103003140700140340b02c400c220400036070103401e50f100380c0c5041580910141c003240700300e81c00c22a14440750540c2c0e10803e201c0c05000c1d030310380f440f6421384164150070900708106501011400f030303400b1074030568144041e02c100b2505100090010922090100007a25030321400d191504140d908940400d48005260502c02e00c40c3d11700410400b0b024400c101c005104105400c282c0c00068180184125510000d2401400480c8032000c05840a0f100840000700004200300c220341d0018000d8482c0d52082c1e0046100c52102d480214641003943c1d0103503120121045541c2200010b0081a03010004142c80c21100040504608224070801e9203220000d106ca0780312800300303d03600d02400b0b40180078401c00e42d5040400b8903004000302025840390070103203190a900042011901c10000750400d4542000c90268500c0c40c10503811001c11045041c02ca0a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 900946780 1250 900945530 900945571
    0xb13080c1f0f0c060509070311060a170a020403020405071214240102151314070b030a020a0c05010f0e210f160f050a1a06010e010f0909020c0105040b 66
    0xc1c44030341211030205200151540812181c0b2490302034000d40e030084400d10407400c2924056581c0c160790311041c1d60749010078a9010403417902908492007007950b5074500b01c2d06082446288144030000d42004400c0750b08100000040c0c4a50040611072000c0b074071607290003104110300005031200d940400c02d000224004200c20540d0554203040540b980d58008a01d003032007900140e2424840f4800300c004294440c0801c50310f500d180c807002400c0f612543c1e022012001071a4031550301c1402c0e000c0e03c0840201440059120450359019100103c45480d1204040c1d20035203030707c1d007101c400c1c04c1840c17811074560324180302c0e0450030400498980f42000094010005c40440552a40201c85480d40f0b003030800942569a241700c3c41020070020b03040024411202000d18000b0b540707242400701203424190203500e8505505141e0002d511445040c0c407546917200081d40115110b0440c001e100301407048102003c51005050300c0075150409030400002418105407c003901c2d20800100f80146100c510f0b2010751 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 900948030 1250 900946780 900946819
    0x6090310050601120608032101150f0302070b0723040b1209010617011a040509060403031116030c060f060303092903130b06032a06040b13080c 63
    0x3032011540000145030300e60000495402c0441c0d2a00c220580c00d028010902c0b01b8080001c2100300304002000300004005144c0030100c600c01d100d42d10341080c0c9020340b240310b01e01030625001540000e1071b00501d0103209546403c001403040e42d414000848400162110540304030104083c4c000324020b0301d040914029a01100d44522514864603401c004c01140c212803017500504090503010306280012040b84402500800c071620404022020740ea0440e101e50500740b10f110b00456298001c0c003d01e982d19141900940040d031405150740d2020400050300d189000ea52541c8240f103070381d4000e080d03401030404034142c9040c424009100b52805104200094105090342c0c111821100c0c1005000c05810042c0e030007900da001c020f0411400003040000240300120b611007600d1140c00728403500e89400c410715584031084064035024161801083d4502a148405d44a400b00d00a1180e49481d403103071b1854140303411800010b60005445101485404000c2c0700046104d502030700c02c40d102921092500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 900949280 1250 900948030 900948043
    0x9031b0609121c020706020f070515010b07020108040210091a0a0311090d12050408030706020d051302030d0c02031f090309090e030a12090209010e19050903070204050601110a0602031005060903 85
    0x1103a50544c00980b030401c2051580585808111411400342c4a1f18a030401645441c80c0904e0f1004003a102c00c00416101c40e0401034402e0650107964541c000e03680c5600744010f40320181041000d114142100048030b2150342c0070414221030039918551100c0c10b05a0140c140c885441c09552560800d0004130004e454821143e50a180c018040910301c0300c4917001950710744a580c00c007130722900000030300005111840c0c000303042c0892031810400066451070881045070b85408402981074226113480c1040601c03401341c5006141c0010f013900d403110300d0500880c0c02181c001c12880e10090719614160145500991804000e1888590510190b1b84c0c18040b2a1644680791400c800d01500c1c0180e4000c060440d0311802a046d4081d0024980b56151003040e045a0000c4070100c100d801c45800ca100c650140c3e02400307004940c0d5400031410180c440e401c001c0601402031200341000815100d10a5050302040071844181c0a9880160f503810500f1192113400c0f541e401850045508100300e086503200007412 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 900950530 1250 900949280 900949327
    0x13022d1c03051e04060504030c061d0114090301020414040c18030f080d05040c090507050f0f09010c05030304030e031e061f0518011503140f09031b060912 68
    0x5544055520002c40b005003508030720883d5503804140490325640040c0240182d0b070181c00228011540c50751300302c400c80c030b95500e4000c2901250700d034182c5550141845101c100400090076040c041a80082422a000369000c020346c244601c1640c42c150829102c1c51b0114201890000c1a4074203102c0306513802509448010f0440400c107001c9400c1c00902d2040c1d41e4400c49026003809541480e0615003040b81140c09841e003001d16060115100c40d002d001140e481484804a075410700840101c41040b030f411111000e418800880c1d581e4000860910046210314800e481e17007200300401c80181894554a2004911003039160100e084170008001b0704140d001c5403401e40c10b10b41c2600c0c02200409000c03075074006a080840c01c1000401000300c050518180c2c2c0234030400d503480d000d041c401181552862a943c1c0b01c50001d80c40862012131800340010b0b4015001400c03203290004000c08030400128405152556400c11801d014210509002d00309410443c010540c0c24548901b0710724803c6100c8504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 900951780 1250 900950530 900950537
    0xb0109120503070b010e060a0e16030905030d0603080c0609031606090201031113030308090a0f1716060506090708040b06040b0a0314030c0610030b040b13022d1c03 72
    0x458030400804200303d862184d0b0282c211a5656507920400c50302c2442a1911380c4910904800406d202042ca00503d21440e088200940b0f11041c50710143d0092144a03000c0d10355001c1000311011406585c0505001035200714440c650b121504004c0d40e0900ea00070b064200a0b0704100100044500ae4102030140355070040000280314405100681c0145481c2650011441000c41c42e104900c0c1403a000400b228002e441d600302d1550b8a40000d0f0706d8244046004141a03100101c00001c5541c046207410b908210a00407441c02040582542c0c4002c0101e10864829440c1d008014842c10000c8000d0342050880c2804001810155a100500b030002040035006a03640c3c1480942c50355092505001075400203442c14041515900341c94580e84400741c050b0461180c000031842d58066199442c040700d81103e03c0000c2c0d03407120350b1128462400a07002e55440e209168440016030b41e44da060f00e100d041d10b00c081c0c200a0303480b0240040070ba41c3d1220110300c070303100c202000c1c0710280c9000a603a030490361514 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 900953030 1250 900951780 900951809
    0x90a0f15081f060e01031a030d050a0512010b0414040b010818011d070e01150f0e0402041e08100216080a1b060b0a090c1b0809032406040b0109 63
    0x40000070160454002e02d403030b41480c0090055004404181551801c0c3d8040c04000301c4100d614601d07207024421543c1540c0910100315040d4410406040010141c0c90198038214540300d00d01082c80080c0c100ca00d00b4840083d0030807244042d020904031000081e034080c41150352020003e408214010085459001c441041d40c0b220b020039405000c409400c10448041442c240c529540c1c0c8144d14055044051203481c00480c3c0a2422500c801d40303c5410b603210b540f407144071201240e03010b081c119150b400c02c2d02440701143d0307260705070a1400e80000e07540c11482031900d0301e094245852050405190468410050340400880820014442c2038020721015a100c10040b021507240d503410300c241248003c3c5000d003408002040c1c21004080c401110740a440d191100844421100800403038000b04c0c07007070725150700e17210301e09620b030000c5a02508030141818842e0340800c0c04c0a0300d401032100c4003241e051003820701a801c0c41c03c46400540903102004030300e084a001a00712012401080000407188 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 900954280 1250 900953030 900953041
    0x218280b030d210c030e0d020118080c4801090605090f04060308030a0b101e1413050a120512031f1401030c1d13090c0803090a0f1508 59
    0x200340000f20f400f22030410480300390030160080043c511214002c1042c0071f401c407004001481402010340900c0150305c55105a5401d07070307d460b915806041d000c819401000441000801041202a05070420440034280624202d4086142e911380c100c040d80c5410a0b01e40441069901c10303000c0d01a82c111341080b80d03442a813200012028109050955070050401c0d8000c010005800040c50040c8007441e0140000041141040790070f02c00c01c20f0130b40c00a4410310340300c503d130301d0071800f4810502410706114400c00d24010700a14558480d8000c00086004030408100c01d042584048000700b4294410103050311695959540311114a88a55150300c0d021000c180c21124103091080e688a07600340107202d09550b5001c82452450140c64540480c1c544a0040061809130711400c801c80ac922161341c0c194405c120810414205d01c241b800d000aa943d002c050014003002641d10140604600640d02d0b00c1d4010200110600d580d04541e50071001c044040091140300440041c0e5040582401442541d80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 900955530 1250 900954280 900954317
    0x2d0e01090f020f1b1903170703180b01061404150f200d0f08040b0610110f0115051f120207020402070318080a030e06070218280b030d 59
    0x40d10f003284000000042d800444101000b082c075000c40c0d00b0400e8440c100c050030811642c2e0646803d01401040c4070a00707000400104030003003a440356003402e0002c3ca80d1502200d4001480c40c2813030845025192030700520040f41c2141c480d40050710b40d10b8041b45010304094002051718083c101c0310043c42652000500d84501801805050312015420800102e50700d480c220350f03400440c0e24602c0815800785041d650a442814050b01ca0703604600c00340c5094645d001400844015071100104100c020144071002503014004420010888000820002556143d80e8041c00240c0c1c040d5110307001d50141140b50300c81d1612044c1081c80c0398200783d00540b03003141c2440064410404000d50080c80000d20204258003c44109a204610f0310030702c82040c0c481150382d64a16140030041c0100f41110042c0d07916140c10001001c10501c00307040500c440c42d007200c2000001006648600100080d541c1125601420300382091000c0d0a40c0002e101e102c011202003a210004224080c0c20420100d0819008001d0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 900956780 1250 900955530 900955537
    0x120601110a0308042102030915040b1215031504060b061204061b03060807050607062025020108011e08060c0903120f0f0d09050105012d0e01090f02 65
    0x4000050301d000103218a4001c200d001d084400f150092502072488001605010f1000e03604441d9030000c602e07190500c0104011a0f000100c0c400001608000102d11000c4082c040c1c800c6261081124000e400c2040d1060400504810640d0080e030040e0410700c08085070305121078101b40c2041d4005840805000800c905200d50300041c112103103540e060104008031540420b9000c2480d481c0b602d10412240310441c241c035041d204030b0190303074402c84003031001d0f16042c0c0041204a10406000401c00074402d02c2200f0036401c0416541e40c80c0020801c200d140320301da0f90800118034902c80045192201d9800a800c10f030041c060b060401d050b82d9076111007200281100006010402e085907000c1c98000351201543d40241c00d0b442c040d004072951117020100740b80903100c41d002c5100860b402e18045400826550300000e030b03032007989a01c400102003c1002845254080c00542412520032140c04260601140c401c0040d11080d0340d5503281045070071002e0350303018156140c880d0089003844224405030040d00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 900958030 1250 900956780 900956807
    0x141b090d140109080a110a020306190219050a02071e1401030f0504060b1014030105010c0c0902030c0d05061c14071e080106080303010f060e040e0607030b040e030906120601 76
    0x43c0307440b06900501c04c9a002509052401c3d0b6500048a06200150b035180da05084c0000d4141d801403004c120001c101001400b0000c040840c0141404008106501500c245c03025103004581c002800d00700c015410300c0143d0141415074030b10410712050403242d41208203184140c12026801481d901c200c0d80c460b420444403a001400c05001c80d003002e04110000300210000c00f889004041c04550403e8020740070800c10400d910a02c9017168a0900150340a0b180401d0032510500c400d040071441030709070b102550003800c0e010311030345c1c0340c0700d250b402401221006000a8130800303520810300060201c0190f000e9000da0300c034450414407051300c24660f00d0440c2e503400000000140001c00c0c40041455800303181200c1408009009040e60340007016224402030007525017501e00a00e050004500688202400d5400076000045c09101060650b051401c2600c010002940b41c404908591406001d20082141e101000c0d5242450b441c00041e8581301d16007103060f491120b0400600981c0c05041c0004450 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 900959280 1250 900958030 900958033
    0x40c090f09020415062015040f08030117010c110303070c0201110123060f012052051e03060103030819050403050a080a0b0301020d141b090d14 63
    0x14a051001035040319500d02800c00050406060300d140403000d55200c0c48444802c6000c0c007d2110b00d841b02c0b4044450080082e25060a904e082000082083d0000c5000b0410242040794528064940a0940c2c0020344e50310b08204075894804c04000d000b2048a0300402d07107041100b03003401d80303100580301060401c03000c1805510300052910105d02d1200901c02d42030400032401140e6441e94104203441c40703803c0d50f1500050071000300d0100040c801c049603500b40020801c0381e032100140c042c1d0b034028007661002c2200c40a030703241c1800720000310329441e5101030701032003070b5000c2e2080980d0804907800c2d061301c59288640300c3e0503000645546001e0580226620140c20b40d0f08941e100d0030041d01c0341c001500c861200040300c003223000d41c05205100c1d90380215031542c0c030149003c01c16001101c01180c040c012000843e604c040da50a0743d5824401414060100d2002003101c00d64800c0380c041c20307034004040c2001d145185c0d00b240c4030000319908540a84a044562100240442c1014858070703c514031b803013009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 900960530 1250 900959280 900959291
    0x20106050402040815130519110406060e12060f0a09030c0b010f180e0c0402180306090d030c0e0d03050a050705070e040c090b01021e010917070b060603040c090f090204 74
    0x3522001c90126440e01100341d100d1843d03111860070710045102100c007d0036a40182407400e808101c0700c0041c03191a806030140241007442180001c040350301d19070003480410351701068400c01d404d00405000c580b0f048480603040520780300000d245001e400402044003180e64544080c1014000c0c00c0c80c50003250028200c00c01583c55075460200e04c0818021000c001c018013810011086040c0940140caa2401c005000003840b694107000c0a500042d07005101c58804000070302282d101004024842d80f0002c00401c00c4c280101ca0280880d000b128070482000400c000c00708990f11102040d2030055454902140d5900c1d42a10460745401042402031031030090038000a500c0740d846003000d024070f00441c0d55100031030356020724100300c64a941c822805038221180348403206142007541061191304000200c0c400c800c0d40e440352005203403203280800090300803c46c0700a00209940c0e09078400d00030746000e89182400e440b860405c040038400c1c0461181c450343c0740d02c0320301c0058001050050f40508148103 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 900961780 1250 900960530 900960539
    0xb10090207050309040e0d0c0602090f0301050a050420010e1314010618060908150603030f070b220f0605040302030d0603030e03060609010f12080405030303040308070315050105030c0a02010605040204 88
    0x1200d900c4907100b244030750b0400343d00300043c070008201e64404080c283ca514039025416500d8501940203e540c865110801e9001c0344070cd601c083c05414400c0c080381400041034074062901c04c0425081c40000782000e4150340c0801007a0741c00c00c880c012540b80c11500607601240401d00b502c058043c12514800040803000002007640c3c004641c3c0325220801d038040710800b0b4965804540d6030609100d042110750110300200402c28004200319084040901620700c1c2035000c1084120a078014030084400341d11400800c0800c11009814942c0d241c98101105468a015103d00d940ca1500b07402c0540015640c502140400d0b008204403520811000c0c2c052240c140d0780c1c10050070300500008490302a01541c00001c503649041100b05040c0c885e001c0551500504042c5031400207009441c0844a4913810880400d0a54003000558840c0e88255221800340c90304c0e080007819115007240b541c000c1c45010700b0502840c3e0b00320007580e07403040d41d015509443c0c3c0340d400001c034090b00d1145c0c8100e800c00c2c40000c2c01305 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 900963030 1250 900961780 900961783
    0x515030f07060801050312030a05040507030b070909140705120705071a0a0c020105071b050a0203032808011401030e190b010603110705210f030a0204090b18040b1009020705 76
    0x200310b40700d81d250318010fa82d81d4024103441c1d03c0114045052840308000140f04a01a544016001405041180d030182d031030381d503003d24500042d11150b02196262000300f0010003c0d00450000345425009101d45040114001e4401e00642ca149001c09000400107800e4078856010f60784003035042049200313200c3d0010280403a044064940300d40041c10300928004403030050052602641e0710341d03100f0011402c02c03000100710030002003049a40740501c40e428009690104040c1501c04908021540c480c00d0319041d0381c03440c5c800e0b07207085010700c141c103001040040c8180c186c841c1035040038200803903c0030f0701c8482c1070304010210340c9030f0141d0601030b80403030207200ea43c40c0400d0588803a61410404a40500d0182c04e460142c0440101160f201c603a00480c3c4c64a00c084031182802e0300c40001d41413003101b11818010740c0007110000889540450104900c084030f01500609034400e8418000990803406540299040140060070303d51000000c6034030040d020703080310024110080300315183d4140d490480d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 900964280 1250 900963030 900963043
    0x210f19051e0a03050c03060d030f090323010b0a06020c1e04090b07020d02161e08250b0304030e0909120c0703200607150f0204091b0806130515030f 65
    0x41d15000008601000080c03c51f40034140c0104109080342c0d0341d5404461240c840c10544042214210000000891071211401c00e44441c07814802030403041301c001c03403c54505564192203138074035080c20030003141c010920000a5000b0741e114a0082141d2040d5030740140f40880150300903207405444410b1011921f40c25000708115400c0d140912003c2da4101ea454010110a00d0320196040080256a006000c0d030030382074641e4002403035070300e60300c221321810200202e200c8004d07504140405160f081c440d4100d030000c0d01d0b69525080c19420551401000c115080302028003450105001c00e0240d002003081d10358007070b18214166030354684c650086c2d44540e120b100c1107801c010030070415004640030440706000800007a00d489c1c1094025103420320401c8003090000c0002d690381c24010002c0c030160004101600541d06c010a600f03a410f103d0712081c06407000e100041048034014005583d690200211540e140a00701040c16242c41201c044050b0300403c517560316128002d041d00340a200800c58 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 900965530 1250 900964280 900964297
    0xb061602010801140f060c070312090905070302040e0c07050718060e0a05040f0206160b10080d0306050102120c03270117060901050114091002210f19051e 68
    0x70303002142d03618005074130602d0301c55810300c2d03009040c0d0800c440705041c004050700d08001442c0803242115601d4503241884807030b103008a40010201101404901c2c0e00d8003c43c3c0e001203561408520342440c046100d082148041c001803c00b0400003030050a1140400028000e050030703010302c80120b503544540600400f66445005810500800059080f0000b4440c69102c1e541124444031152203d41c20091950310980b120f01143c2d8061448a020413102403440d8441c071900d40c4200ca03d5402c1c601803e14190080c00d82c10105401c20310f0500135664085160600a8540e102c0251142c040c1d50109040d07000702c0076806030740d001030100303c0c8a0b0395072007212a0742e0346d80030388900341a8200366207040c185400440e47c19803c5050500104031135441341e0b0008010187c5040154200200c070000038210285900044006074880d540c00942c0c03e003800525054402d00080062a02100d10098022406064020800ea409140c4642c0501b80503200310b0303503019820f1802081d91042030501c06040e400044e0b4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 900966780 1250 900965530 900965537
    0x70e16030f0e2a09060103091a0403030902040509012f1e2d0708030c07050a060e060705090108010e07020c0a09021206090c0d09060b04020c0606030d09061d040b06160201 75
    0xb140a00f91065074562080e00001802200c0b00c1d5413a0710040d4003600404400320f94405180c00001a4420b442101c54001c51080e036010401c2d04880c01044182c0381c1c0500700d00000d0749800405110a44000982d07006041a001d4508000b00500f004900074010041c09070b860070340001c43c4048142d000310040c040c0354142c0c01104030740d98a94480d5045030b1100701d029802500c04000c90f00c04914800040c2d0b91040030b07000000d25100081d82d07510704040c18200100c0c0c551b500e031400c02011200034018075a00c22214075100d42461100e01c002492803e0620510304042011404a9030040c03090104054890002c0c2103240307503d40d40c0b102c02000358070035441845542c900d00b0101e201490150051340c01003120404482c10702c0740c0a142900245001002143d41a6803416550b2407511a0f001400361010a0405804a86403d0085c14140010450301030300704075203001d0601c0a140c2212120501c075441640f50100c016040e000f1400a01c40a41d1003070380210b0102e06045440002035a4404440c802c2c1d8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 900968030 1250 900966780 900966823
    0x8011a13020405010815040b0a0b0c0d020c15030402040603230d0f0509040515040e0106090f0903051e0f0f0a0e0301110906160b01080102071202070e16030f0e 70
    0x40d04000301c1c0a5405080c0c00600041c001c52a210404c40e440c3c0c80c010001003000490340f140d80c000864000050380071140810000c00c9209540006100388c4100180340d00103400310032420800201e140c0c08150004258842c0072001c00d040d0740791a4880e0000c0c40e80154440b1420b0311414404002240c10101c1c220640714140019400034880d220400003074481da00c5540c20625407400f00030180c03000400c505403c0d00f5016401d45d107a80c4c1c1d4014035007100000400094150300b40680001940c07912080c842e4024146440760000a40c0007040b81d486002d810084101050a4110317001640300707031308200034400d00c085220502105584d00408100e2400c0d1280602c0c3c450032800e15003a51403c100d55040100c0030300040c0b0b0fa034182a002802505c6a01000d08a085810b5503a112281e40a81004055a6012540d102000840401807040700c0300e03400200b000c107244c005106900a40180000380c081001031809104901a07002081284180c01041c0003480c3c1c5402040d0f5100210810403003c0c81e68003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 900969280 1250 900968030 900968059
    0xf0a020a12050c1e0d060c020c091003020609221a0102160303030e0a0203010608010e013606270c0b0703021005070516030503060901140904020f0a08011a 68
    0x402406158008050b01c940e4603e00c080003034406203100e282c418841d030800502d0b500d9880350030000e2032a110744400600b1003074400e0000c0c41c04e101c0c003981900401e105010702c800c00d0b5103801048100c0e9811150300e0741e202c0c19000840c841c000c0f0701d20020400c2c4c103286081070030820a90854840c4c40b1203000c0318110f11340b40d0001240d503490580181c000d9003660034418030100e4402d41203510701d240d1400495a80001c07030380c08a42100c00640c00500665922044000360020a001c3c09001c803840001c0e03902c43e00c10301c0e00700003400200344400c0c400c1460390300c0f040001c1080c541c00a204001c1134050880030542c8000306c1100b504003c0104444403d400382011400b141d4040c141e0b00c41d00e8040e0b00400000388440f182c80000c20700030f083c6c03a05000c0148071210b4070280c4411001c030424400c3d61070359120706058050003074105040c0c01018103280c0a41480040341c49120615901c59011103401100c9540200070030310600c0c091700705c010380d135090202c488903a8003d224103420a07a001d503040200c0a062 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 900970530 1250 900969280 900969299
    0x1150b031b0703270512100f0e0d0f021203040b0402010201050c0c0a1403090303070c0f0609060804060c210b13020313120201061d061903020f01050d0e0f0a020a 71
    0x40480080204000c030340c8070082c40d40741840e012004010460340240040d01ca07400180100306909031b503c043e602503001c01406c28a1030049800184c040310043c01020308040803262a0340c00071101d80b0170009000c407400007451007000000d08070485140e00c16602e09080c20054952642114140c1c007540c245004500c00080b0b84080365145000303c005009150b00b2a610601c5420105000f442544024003614030103680910007082c1c800d100b4681c2ea203105181008009440d00703550701510034003045010821030709030400b0b58150b04c55403000300000c0ca0707c03483c44c09650780152481c0d000044c1c2200c18081448903802c1d848402c485204440051240c0f1403e6111000e070310040707500341c03400c0c41420304120008510b00071441d14900540004100f031915111003040201d01c10200c03001a11200d8107000d02401c113180d1840c501242d0400b1100300320f00f5900800c03500301e00603001d14104200012400b182c05840d1341b10030001100f400540c0c41c5c5203000c03a1041e580f00d101100a038450506d551000508005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 900971780 1250 900970530 900970537
    0x2b0c0f08040c180b03030a030b180403170603010e0a060b0424141804110a0b0310150315141c0507061b060c0909050a0b030a020d0501150b031b 63
    0x6020100481c25810a201001400c120b55a04183c0396103c00342100c89503014000342034850070303a030340001e680c1e4406410000480b860744070f40d902c0411500284004681e01c4a14001224440384d03040065844007404a40104240e12400c01d45001b80d02c203c0d4100b101c560400c180c0e80c20304840c24001141031214150510b914420890114003a400c41000301d0303901c190450140c018010b00c00c09030055200c03500040307a04100c404592000d400d2001110360300e006d00d405409002041142411413408168610781c0031040d00408002614106400082d07a119030030000841d104140ca041101360303103825441820104011552041000300c0070314083c03020b082d0b12815001d801500a204c154503004003074584407002e0b81155012144404900c2c01304096000b11b4800d000c1684c1d840a26501e482d14010889001800c403d501c14140004602181e03400651030110a80488095070465480d28115005100e6020400c00b42c2800700000600c0364040c90103184604186064000e11122041c0c0d00e03280c521 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 900973030 1250 900971780 900971783
    0x307240c0e040b0301150b0d0c05190e1507030201020c0709140c0906090d0b18031e03060604030c0803030103120f12050a2702041a03070b2b0c0f0804 66
    0x1440560901c0207898581c0207038030200070240c0005803031000003403860031482d800e41044040c0c40c000103154184401900c03400714210070501c0c00501740b40909d06440100700225002d00c0401c0000103640440b80d407401d05002101d02070b0030565a96603402d01e4040d001c0d410480060a0f01e006000780003886882078003c80c0300307021107120020015512594004060f8001c03203040d41c0c000a080c416030700d6986a004403681e07080e01400030750f079051034040c0c00400c2c1640940c0d03003513100d038000f4009800c40006c60131102a0100b030b00200ba503100c1d90740c20003041c454002c960000e0b040700c1d034a210010384100e0220045050320b006040c030700022040c1c80c200340e80002114500300f0003c2c0c101f51514403003401c240d1000d9006a1000400300c3c002030106007508815030190410380c5d081c104609580c045150030722808071281c07006c0c50074000c00c0811a0010761681164841c0d41001840004c050b02580c0d0680000c00883d00c5442d00304d200c000307944203040300600800b803c0c0000319010203144030324203004007011403055 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 900974280 1250 900973030 900973037
    0xf19270506061203071b09091a060a0509011403010902031507020f06011401030b03030d0504031805031c05030601020a0605130b011409071404210b130f02040510080307240c 76
    0x802e541d41c52074005c0790721906c00545402001004500c0311194099a015640108403042804550144010105502624891041420190800040d140c0502c000d0449500e84029507400c9540710110307004d0041440004d6142c0140600141c0a490705a00d56005084944c215049194400030b110b503039460038000d0b4403000403916020809584290080034445001900760b90400800e1152f510541d501554110003050010504454844202c041040103000890040c1034a0001a81d086018171300d0113012000c000703000001811590081259401c0b0030780c400e40402c240c0c9408400da510100c4654000c13640103074110000240c071000120001005000102038101c2a250604141c1c0e085050a542d051010014040080d250301c002111020361401d42c801e25160340c5141c40e0019190340000e004041004c088120310340030a02042e00500e080741c2c1036500045035101c40d4150303546080d15500c40040e91000050503020890803001c18840540c0d150341c40c030601800e03c0301c80003e4a011411480c000b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 900975530 1250 900974280 900974287
    0x5042c0d080c0c15130f050f0d020703030507021c0c180c0e09070c06060f17010e0114041b0e07020307020f010f170c0d0507090303170f19270506061203 67
    0x40502c94103a1303074001c03d403100c254080c0c1d030903580c44243c03449104505491a0300407010b2650551024480e0a0403010b203403000d862440d0031170360003602c01d0085010180c004c081e0321080262540b501d1500c00703400e540103101c13288202c1d506e48090050a001c55108001c4500304500442d0190144803884c60700c400081c4125050350f81c500049a0303412000304140c500c240c940000040000710781d00c1c224040e05645031580e004001d940d8441e4207403070300026030100c01e03858400d1038014511030001103900144d20614103810946032034003040c200d500e15013052140d020410140101c150300003008060a40c4242d810302c1d08a2400350041d14480455800c50012911210501411807507800a0951295a2000b4682400d0180894000301d4030121004c5001c40d020a4052003456080300e4280e43c94110b0440106407481c24074031a070034900000e0160705e844400884070080b0040c040d00110241c140841005640310048803642c521103c00c180b082c0c0c0c0600038100420902d08180700310503e10020100203515 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 900976780 1250 900975530 900975553
    0x30515061e0f10030c231b0c0303190e09070f0f0c06140105150a091202040b031501140307030812060d151d01020702010905042c0d080c0c 61
    0x84903010700c0541030b80114210020480750380c81000366030403c0c81c2a5000690001c8585001d03241e0084800c0d5000c0040110b6807402c0c0c900c651004031600e840c90100d207034040b5603e2011040c604102007d841d94980000b05840c022035895a907a212444102d9461803028103140092221500096841d140002c541d0340140c50a10301030040e510031004c00d458910345100803038450200700c0c0c441d03401001200303a0319801040a0f2600702c100900354100110501d142c040020b1011344400554840c01e0100981e0010100940d0394950001c3c10701030028060350400740d160019030b004450240906c080641e10340c54400d015040005400e01500e51000170743d4580488481601c0b2000001071186510041c414206000140e0840c1405043c800c20340000c1503070080002c8061b003c03100e0b002262540c3e8418803580001d40c0c0e0110682c0b00301e51050303d00240041c1d104461603e141e844013190080e03002c0102d903503e10300c1d0002a1401400300c142e0340744007441c0c0703030001c2c401001d215410401a035580441c14000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 900978030 1250 900976780 900976819
    0x6040f0e0c01052a0d021c0807080402060418090212030f030c0705010905190c06030b060313210903150b06030103080901051603020c040510060c060b04060305150103051506 76
    0x35003200345501801802c10074000c3d04010441c12040c0700c501d80000c4556a181768042040d442105403003050310314403000412005145c08001080481005104000f0405544800d012603011700454605003000d8042e0582c038101038403032000100c0c020422410144010301c008020b40c0c45241c0c04210080c07a548501d11061155000b1040545113550b07900d0285000030f0080000204c000b0340312100c10850080d50030f043c40d0f0007882c2c0d84010103060810481c64841d68584045940c41b03200400d000c0310507071131401c18000c01c803009400076200c5036007a491180401c0d00409080100d034443e615118190201c0310b00e441c1551000c10300c440d00024203100520028050318080c0a01790411700d0440c0c2013071250050181e00042c0501d00b40c000d41c0003207a08411a00305070142c1741d0701c40b01c034194040070130f0f24051004004d2a046071001c1d000fa6601c0040100541c2e858004e0300007036801c03a08a0315000b801041d141c045c074400303100850300c2d4411116052400007400d04000c1c4139a800500c5e10181ca0645c0f038622 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 900979280 1250 900978030 900978037
    0x70e0f0a0b120415140109060f0e010306050901150b0c062a07030302070206030f061807140c0a080a03050906010e040f08071e05030903010b01020606030a12140d0506040f0e0c0105 79
    0x3104d45980c00071070201d90070714034814078145191000300d00e41c140d450b20f40400d0455420f034000070002141c00c11309103c1e080281109a0450794030010004181d60b4a84803140101000002c2c500c0300820040b0001c2d04044241c05815101160001e5a0301e645603041c50301c010f17400c40ba601c1804501c040e403002e0445900341000d00700d02070003403c02601d0700415500158150344112540880701c03040009102d09414582c10755440e0300c034803180002c0b07a8144444050b000f6015050807400c1090005401642c0c0720040c0541039032a85e000c3d10f4144c0300c49101c00086d01605048601d4881441140000a5082001ca90b407501032500000d005100d4400d0781c540480a512a40301520441070314101c082c0c1d400c0d8080480d4032018025000385460700081e90815080d50062124981190710800500c88180e601040d11010960b001c103503884042110360b810340b82142c41c04c0313048015000110765460030a00c030340c0200b403207500200c0e010070000c1c4010502808440d02d80c41c4001d00d552000040041c40c0d406400203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 900980530 1250 900979280 900979283
    0x310b2d0109080708100c020105070909051b0f03060102060f16050703200c0f1008010e0a090b0c070203070e040b042a091a09090a030c080d05070e0f0a0b1204 69
    0x4207034010b4861503880d20308049a84182c44950204410401d0611940314040400e441031009100c2e80c01e101c4001400c05071140900c40c0313107030f5440e000720707040b4044030344459840c00841d030840e51540340c2d19520000ca41c00c1291400e015000c0c40d000204866900560188136883c005422407402d907100c1c0341220a078000304000c13408e0200e4403841e1000302e1600407045007155201801000600c20740003d000c070304074640840d0790196a070704540055050300300041605444104020140c955600021030000d000e280001800c09204c034028410410002c2e401071100364000d80440c1c0c4980c0d624994884040c400716000b41c06c54082d8004900043d903104507203050361071a00c030b030001d440c06484580c5094492551111122554501940d00072640c0c91542540240e0202e41120480c500700d05c0154507070744c41a1004080020002441041001301c038103858a484968408201e1440d0200c00908998284042c03580b003240d01c6909800b9520300041030105442403062400d05200011040ea01d902101400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 900981780 1250 900980530 900980537
    0xb070905041103090106060201051b07290f06010509090a090203011401080a1b0506070f1b090f050609090d0f02030c0d23090306070e310b2d01 63
    0x400240e40d0703100d00412000c0c19120112960b03d060481c50107003128001d902002c1564185420402e0291071083e409030713284c00328901c0f1580c030111854140e80d89422002c0300b40400d081314600d809060825a221352040c90701d803c80084540710040191603500034014100d038002207840000c1c0d00c0c0315098010610f000d10281c00860305e007040c50001c03541c4001c240c0040090340d02000c007070b4050201c10b2603403440d04400c04404200180c20030340429034900c2000d00113007800c0100001d907000c0001c0074540b5003440b406203040002d0b894071404c0080281240034900140c1e54208404600146001641035025803865001000d001102c0e841c280c9030500b070000781c1030640c0800e00c01241e00c0b80342481207201050260390303600c0c0e00320355045868808032030103d01d074244000c0600c40c00450703031000a00c4c15001982070900628804140c0006410424640404156401d01b1810800101051241c19040da900c0320014400b42c0d2010b01800803806054207200710380c0045081148880c910101d48005440040c903 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 900983030 1250 900981780 900981797
    0x50613020403230c0d0b090c0a050603011703120109060303031b080a0f0f090507030317072309030a03090f0614090f0303070203031813020751060b03060d0b07 70
    0x14002205c3c955451001d8070221588810460070070341c01d00c40214580c000311a07200303c442c14007000c1005404140142c1e655508100455a40b40c0c00400c140c1d03511080c0304203100300c5981c58007550320240159200c00c4001c41d0401850440c484d911080341c0310038080695888100303503034502480002d0300720255000401655124548024901801059201d40c010402009868a14500180700103000811000e01504900920944a90110440101041c00c031030b850744103500b00300b941c10070b4413034104840d6240c0708a80c1c8000400d44c0000000e0101c8d4644021171516a64410b4286d039001128840c410950108200c0842da42c41d042c0148942034101400300c9040070440d0780031038510307409a100ba40d1002001c1c00c083c8628074181200700103e581802d000c1d401e16143ea0742e9110f800c0100790500139075030410b200c0750000624000c49940400504840610b01030410b010054850703244460303069500d410802d002c603500d1b0781402181c0c00389030003802d007890082d40303501d80c0c620b10100908054100049030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 900984280 1250 900983030 900983053
    0x30e041107060e0d050301050112021305061902010e0f0312040602121306110a050a08041412040e0c0705060f1302030102030c0423090105131b0305061302040323 71
    0x10107480325500c218000612440210400c52510594003210300802c03a040006100c00d0344c1c41004500c1a483c00348000d80c40fa131750710300b40e5496040160031a642088010514000140000004003001040d0390020003405103600d5005450f001c5e10014207138240c2c01007003075510b403015809070740e640107006904c018141505d803044648122000c0c5c4040040c07040d0740c042c400500c507940c480e500d01030495500b451700d0468605805000b5001c0c1c2d441140500c0b10360000201031090301c1a8a46500c0050016075000b40c1a181100c9815001802198000c00e2020300164040001808031140b0b01d4002c0004c0c0380035500e89042caa840800108a6060004210500001038409001540c0100904402d40e5102c6041405080580c0702c03084d0b05528100302001848a01d4031051000d40c19141c0030351b090140c00142035502006044503080c0005a2101035401140c6030b85d042d0302050081030115940c0f4149160907414a0607070049000c09015074085100401d8000200d02c1030850984040b419243c140510 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 900985530 1250 900984280 900984311
    0x270303061201061502010c08010f05091b1b030406090b030f27010e030d180b041101030221010e01060c0503032403030a0917070305060406330608010b16030e04 70
    0x140c43c0b020050307034441e40d40a041f035410140b01d901500410701142000c40c54080040c25140010304001482c0039011141d46000e090072045500096200800750002c118010525950740c5c414881c3c4d00006502200226242a4a4044038081c070701c886107000709500e5a520655107101c0c4401803040101110108001015083c001c0e40040c0d80c04001840c5c641094040c15000d444c10040010101c2d003004100c50001038144500940040d0801609001605c1c00c1c00141d00a101d00c01b04031180d05d691030a803003c41c080c3c01c14414103a8200c5031400300517903078881d000e40e52003030364860060032030708248001000340204d101d000c1401c4420b04034000f140c14480010904650000190200080107040309010700c01004103600a503e0520000b030034941d00e107890703c03501d90002500c02850941c4401e4810b012070b00a5000d07210003c1c182a12603958050354144914501d107502c11580419403010000a01da44007400b03481c60407111140da904c030030010703a4003212056043c1d6011540b0030f41d100c400540304201c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 900986780 1250 900985530 900985559
    0x301140a020a0c140a0537030207050a08010203010518160813150e01063f060c020f19020904030507030210020a0306031703011208031005030303040b27030306120106 73
    0x41c5405880003407541d013440c5090603002110a1001e4800002c102d035007101541c900541f00349800a0611000f41b0307460101d08000316a400540d00ca410040c01003403481c0c0c103600a40c101c41c3e003180c8c003d119041c030004520154200302ca0920745010210607546060340180101940700031031140b08000c0382050380d0780c59404a90071550b030005640d15549a440450244164005009915031150411440580c0001c403d000c1c0050207606501400f03403250b08610149503001899484802405104078811009644541080c1b007803005100d0700e0418160000365032140c0700c1103a0080c1c07008c4019602d80d1020b8500d0b6010000031000c600c12044081111a501d101400400046580209a81d0300e1824040e5190700124004c01484a042004000b00d5038010000360060b54804040c82c3c4903030b140c40807142d14030a1580040d426000000402c0100000d42a01c00d1141120b407410001d40120800050508000703c42e84c4241944104040703141c40c90018508030303002c00aa0000b046090301d41600da0070308230 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 900988030 1250 900986780 900986813
    0x100e0303030f16091505181512011e0608220b0912032202030f0102030103121704021818190209240418120801050f0301140a020a0c 58
    0x80412050020440c2100c0e480903000019241c2070b40d0352414089142c21042001204605000c00003400110380c082560075000c0c810350080248000114008090641e41c2c040c0c3c6030205000700000001c0782c10400a032254201400200cbc40d10704450401006852080f006040705400e4401010f0303880110b4480781040c0702c298800e44000f101e6040852007181340807400d45401c020140117008120b1039032507000d0910003400c11343c6403084c2003c0883c00030a081a0201c40300c01c807154000800402405000000b0003280951681d4062102c0320719542144080d4080d00c3c029440755603032044a0720f40545040c0650230400c0c0c3d51070905980500d2055a1410301110054140c450034500c41600b549410315409030f20011891a118076040c400301880c1c1c6000312403510510441d0382e05520019000c0c110140307802d0343d600c140740d68a003424048020300079240911074039100384a0b803460072a0341d00781800744450304a5003030014441526807410050103900030000c46d070704020b503090a410204100010300544030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 900989280 1250 900988030 900988051
    0x90306020d0f1e05070309030e0f0f1f09060f0c0f0312020706050a0f0e07060522060c05010e0f030d0207060f1e0f090f02010f030e01020d0606090f0f0302100e030303 73
    0x408030740600c5401d07918018000406e140c603018076203021130341011f0710f08072244003140c008031505203007030010f02c0c10329aa10760f59400c40e00117005007600c074840c0004112440c03050744461040544e5203070220f5500c4c20056a140001742d2001c500800100c0c0e0610003401c8500c80c1c1451324143e0008107180c4100d0300840c10507110300382c0b12400d0003400b15403441489180800c0240030701c0052111815540d445071188035410810500240b41d9040306881122014041c1e54100316518140c0c1c1c442d0002d000e00c40410381074586528000103441114400200d02130760f410324a0186003464601a59100203400010303064411903158024221144001c0c86200308042c2074503081400d66000d419001c080365890118902020301d08603018020819980514082e180d0928026240020f070035402c03400791580e11701c0d400440d800440d05900e401c030a03400041c1a24100d90303840ca000c80d40d4030300402003071440303100312a00b5090103001880942010030403039090503a9401c6c40da851450b0000403a02c0d50b030045030003000b813 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 900990530 1250 900989280 900989321
    0x7021219080105041506051602040c0c020f0102010614040e07030f0c0e090604021516020a0e2d01170a05070603060311030c100509030a051204091803090306020d0f 72
    0xc0c03500424610301618003980c04000180a014141460106a024640503c40c000c180c0f51903400344000c2c202400381d40603105002001c040780340a8000300c404002244119100002511194070511450080b1950341c202000800c9210381800000c103902c4c442c00e55540a0a2004404285601e46842e0b62500c10002c5600180ca0292800d07000308014040300840c0c0c10107818000986d83e0f06c0007080380803d1217514580c0c1c03141d070441c180649291040000350011034109001485002956180b8410354400d0a210281d24060b08445e0002c89645405000510a040148441074018200b0481050303018200c0e022070845490b0503160480c0c913406a400241c441100707000300910601e180620300d006a00030700e04015050001005440340f19502d00800501080d030240554040000da00c0c0303580c102058642c0031800c80722000c07082c2e005004404c246803d00e003064a00b091020040d807142905580c50014460845d40c884000c0c0d8000d880001406032a030340051020407440c410b9103c00d0044000c441d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 900991780 1250 900990530 900990577
    0x9130b03151627061d090f0f0601030b090117033606030106020a111f08060405070f09030b1f060518010815090c0408031204050c0d1a070212 62
    0x400304603c2c01070714031039a401e60030305050302502c050000b42d4245003459610404a1000f2000445620309a1a80b02105a061180c070803602d0b42154001d14941c0610444c50b601d8400540a40d40380100e81a088104031004100840101e089075000509038800e0364581f070040341d2840100d00200d0100c00c031070443d80d440e41ca00e010204d100c5c411100c0068811030308561400c1c4002c0d4075074840000140c450400b0180541c0b45a030f40002d01c0007503004000c1940c00d01c60402a00903c5c2481c02c4074002e009510701004540050f000e0040e4a5900c0e586a81d0941494115640d203d181d00d80503000c8020403003003000c00c0d00c0c4030200d41c21000140c9203035900d050721446045145801e121f07003d1410381c1480b400030306020020008000d0058519002c3d2194203075915101445082841650b1050800d07000100301403a00c000d0000c005805940a02d0858250340c4500d4204110181001d10042c1801c07000d150340d5012a400c070035025800410303401510b9400360b00c0c1500c0c0860342e00c0300d001c01180b5183c0245508 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 900993030 1250 900991780 900991787
    0x70501022209091703070e031006051504050604171603080306030124270203070503091506060a030c0e0909030408070902030606090402031909230309130b031516 71
    0xc00501d594070701030160160381c0d201c110308512813421030b0246a00000004034624082c03031400c8616400030301229080701e6182003800c01440300e03020300d03445a9520581c88038030700d0b81d0300191010b46030020f048034a882e20380b54500c3c400021940c4410124054150f044e940341c407507005000300960003442640c1d520300d4121304050866500c914805100c4440181140001803107414020030f40b921116001003040741041f909603007094240311440214000420020f9440d0f20202541c040d184690494980d5062003404500156044805503001030781800404200c5200f500041410511820521384e040685000719060000440d40d0b4401540001020059130701c0810180008045400301103007581041c0000895510521006078411078000c0049a80380041c00c4070b601c00c64105039010001c48489180291b04152040303591400039846030444038030f4400210031030f90002001881e00d41e0800c0605039040003400421a040d40500c11000800c03203081c81404814020140700d80c020403419950700d00203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 900994280 1250 900993030 900993097
    0x60804150204032618210f012406080a02090f031c090602150a0c0e0a060f1e08040b04060b120a0b0105150304062f07021008010b0d0203040807050102 66
    0xca0031110401a22021005c80d04401501c0481241d1405000900c820300c84a0b1015843d0500e065020744000010b0f14041581714a0035148112a8160946210102e461031514140301d1500894003000c00110040b103254014009500000d018511050304000424604600c80d10704d5046200760350200441190000d88040040040d440100722074040c03445000d08625024040658007a10b41103c802094003c0329440c4480b18003074030004a00da03a07894000e100314408810900416514507030b0344082e05e601c8803041d6010800c3d0301c0d002625140d980e43d00f10840300041c01659081c0d507170302c0d0718170413941d07100038030244ac26800700140740c4001507040c1211001c1c4103030f100031300c99800c10026072030a0150105803a400b07504400001a84c88000c014400e804940310b9207601456508110040c403801d2503005800242c0c000e0740e03104444652510299250342003805003044180f02400031003800b10072034004541c01481000320905044941da035407800d80c1c200050306000c5035100c0c040300c1213004007103804 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 900995530 1250 900994280 900994343
    0x12060906060c0304120606080118032c0d02040b03010216060b0409020f010507030306030507090c02010c03200d06050603100e0708070f0c03050909100f0801021306080415020403 78
    0x240e454000006920b954038411032240c141e181801041700d4007804540d1384400300400e103120003846600780007500c4100c500082082100440d441e2072209020309045420300c0c00ca034442c9100e6644a80b82c01c0100442100a928100e0f070054550300084090340f0700703001500b0000d80802c0d0340c080350444c030300d0490142c130382c0f0400c800d009600d4a0240e601598607076008221492007070800c19514202420207e01401d0301d5000509a032291000001f04c0b41c04507489015008200e500800c215011008202d0583d01c074582036114101d480b070341030303d64010310100901100131b5080340000c806a0320390208500d0340049034141c03003440000e02d0170040b2001040845910441519040d1200d2400380700190079084111b0328402040883d1400c802050f00545c04c0380c03100b410042080d04946802d1908100c0302d1020300a510041100f142c0c00290340005001f99501c6020315003612212500307241c821515004000c1003134803d503c41003104403070091184018000340d4000e0900440e070300040c5940d0304450300c0000742c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 900996780 1250 900995530 900995539
    0x60a0909021c0512070b060a14030d030c170c0903061b071506030503030906040618050a0b060105090d210903021305360709060617090a0812060906 65
    0x4000d40140d40d00c041188540d4042403100c0788034507250900c18079000401200024002000841c0001e10000780b11a40c442c48003142c80240d611b03114500d240d02c052911205607015400f45182c091018025001080906400e01d44040c0c40d070070b0420200d91a1b00c0948142030f01c000001250066810f06001d02584000d003c0360300300780f0b00260300c075038910ba204400740640041c80c07104d07402c41e04544030342050000f56086022a602c0e410002c00c4662150000d503000c4842c140342440903c04030180442d41030b8940d4006024019000380c503110b5078150540144800d04000302003205012580c0c5000408103c1d501a8207640003c2c2c87d00754001c41c00c2501002102c05021548004100594a411a00c006400480404205615105036481e621003828007015a035440c114070380c41c3ca030000d800300c002c0b41a640800301c65625594410701d40848200e0300826000442004818000045210450b500592460100c402c1c00c2c40d81e81b221030498000300c6040107649444001d03c02d80d171400100c2690420001c68 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 900998030 1250 900996780 900996791
    0x301150513150308090a0504240608010812030402040b06030c0301081203270106171609020c03070f03050c07030b07020d0f09140a0b0d060e0a021206010e0607050114060a09 76
    0x10b01000480014403000f000041c0000b41c1e026180c503007210040c01060064000c1c80084510303e5180c07003030301d000904148000048680082d000d84075000c00342c101c942100103840301256001d0810900da0004005a0300310345c0b918040042519400025441200729104458a0f075050507071030b908046540701c21403041003040c0141300000454409281201d642105000b0407549980c48082c098901940400d03e48000d4110313003591040081005410050880e021041c11a2a4010b080880c0a0700e01d04900c994020700c2000001628180f1050249001e07062850602000042c280d02d850070319001219103954000c140100b507501000b03039000424241c02d05c40020440c1050050450255100c2c002c2101201d094601c105c0d22403900420150031301c0c05030300e55202e6107080703240d01902d41c82c86004901001c40c400100790407035500c01d407140701003400041001611241c00450740205503c80c1d05a02c0402040500c00040003403141032032485441c02202c610b031619100f0030290381c10551001080e40c1c00d20 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 900999280 1250 900998030 900998051
    0x31106100b030f1503060109020901030605011b080c03250303230712021c0c260a0507050d0903170a060b030f071403040302011505040c050d05150301150513 69
    0x42d20351103800018901c41c0760759214056101d01035150300d0190140603100001c10508a950010407164000703803014801a59110011564804410b2001d00300d032002416240009984000411403c2303e290708481c05c1400c08814502800300c0820000183d41c40669107001f01074041c02491038030a45c85280c101c000003185607015800d08001c0c001e00821180b010041c3d01d400150b81501c042c6080c0308035204060160300440001031403016840d1021a10009030642000c075021b03a01900704100f00b05404564864615442c040c010282208051110601c407000446465101d101c204900a5803910302540d0714082c080401c0704080e010b011401d081c00c1051050340804000c8070340000d002d04000e0219034810908a88a100303010390203105001c000103100a0541c1504150004030004a45141e0160780318104401c844070345400e2000306006102060060001f5800958442601c089030511840d81c8000603085a10b01c070840c001c1301d034000034184110b00300001c0101503018151804c0002e813003417 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 901000530 1250 900999280 900999299
    0xd06120b0a0c11031204110409020d03030b0f090f04120806030c010e13090803010806100f14010309060e0a03030b0d2d1208040318062309030a03110610 67
    0x1041e07001090385845020348040d20035940000c05059070015241c56250b20204051146415a0103070b5400002e042034039040e02e810f00c6406400c0381d000f000154010b00e90b0b60242c0142200f0320050382c0c4081d082c011184662910151030f88115201070000d1600d03d414a80165140d540d4090081000714000401c5880d450010b40303180800800d080c00c111304e200d000c0000301e8550304040d0194880382046005005c2244081c065030503210040203403003095654505100c030105051082240c8407620043c200034404161202c0c0824203411715010400b582143c07078010641d00500d0040c80305c0d5020201702c1c014903034544592480c16800310345000940c40c882c2c4a001100d00002040c1120a0300360000030420907224103860200788d806070201c41c100702c003040040d200b0b060441d0280e0106801209081010741c60342d20b01c40540340140c4503140d19443c009c03601c45580310105051000c0d40c0c802c0114511a642c10003180c1c000b64480d960300800e92811720398450170300402a10b01d03c500d694060003449007002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 901001780 1250 901000530 901000553
    0xf060813170d02070204110307020f0309010207090f0b0d0c09061403060a020c10090506070806090f0118021309020301060e03030c0d080c04120c0305010e0706020307140703170d0612 80
    0x31a01e48498035110394140d008024820003c00175446490801098800c00000001d14410710b0b1540a880001500080c6e440e10b038425a4109030041e0440003003400040d0700e6520000414036100000074440303a94802103042c0e0140c11006a0f41c0341c1f4500b00800480c02d0501400c0c01a04948006580845104011030740e00c06001e00710506068002c180100d2241080010251403462580300303200140a6040113925807500344c4000000031031401c005105c42c2400c00b901c6000308000d81c901025a860300b4205440960f0709951a040180c01f04405022400c846000c0700c05084510707001640e9515052002e000c8900d1030300101d000b50410310042c0703d00040410064582d01c0316007440d843c107994110582001d8401d940086445c110080712100a00c00d00c049035000b524421402040030000360390070385a8510091003080d0042e4000c10001c40004c502550103401603030782100b107900854482d91034164080f003c01d8030310721207070020683e000c0094460080380000c048421191040e94a5900c41c6003c104 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 901003030 1250 901001780 901001813
    0x40303020c04270f020102010605010806061207021f05190605010507110d0206030115020c0915150d0c0203071b120803060f09070f180e040f0602040803040f060813 72
    0x607603a4014481600100283c809600c8070b0340b950118211951401d00480c4d8801d0710280e00543c81d1110100c1c441d40580e0465009100013080c1504015035102d151608210003802e000441c02504248032400b00b0300c0d41d234070250315030204010403640380108040c04010602e8609046c2182404410010751360440211000d41f078008034050b400d404207802248002c109800025000180000002490b8010f54580c0021340c0f41a82501c084c4081c140800c01001c4040c0c07180c8000241c401c800c4c1c03960385400d283e020284a4561500d40c00c01ca05441054110385840c1c01c01c10268000044620401c002545800f40c0540d0480b500700545007001030300e8042103400d100040c80e00c41c0c0003002c92610b541d60444c80100c404002e2000030340b1318200e0001007065204c4402d40003c202e508003c200c194980c1c040401c02d07074a00006410007a5038585840342050342140068078807a500304030200f2001030074401000548072140f1042a010301d03045000b03000d558010880044041d40e00e0450300015198600fa100d00c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 901004280 1250 901003030 901003039
    0xa08150a061d0d0c080118050303060f1201050f01080d11070b030901150303030f27060c0504080105010b040e011e03031107080a0f0b070507080304060f0e0f07090b0402040303020c 79
    0x4205076951641404081144540e001482800c540c0400003501401c0302945c9070381c002484589104c18046a480c104948024102d400510000c5c1d07403800d20415400741e88800038243c043d00121355403c0e5003180e0059031200100c11052005024140c1c0801c0000042811850301e12489030354941d0340303500c0b50102d0107010700100002011403040f20742500411241881441850314450703407441c000c0c2c02407600c1110041300908125141c082e004129401000c0a060300403800d070000c0391582c2c1c13030009101c1107018070300b44041848042903403402403054601a10010030510b940781d041c010050040d07041648040c442003a003214040001d0b080031a50300c12203900d420400c1d845650002181c2c100440303a00300702e080740b1a0003101024062003040d40e0380310700d004004181c2541c45042c006c031401d2140d00005060030004101150000d01e09078003a0401640e1400000350401002c05a1420034003010348074205980030b05410b0080c2070039441030b400060022181145020f20b10f99019444032007580d002c2d8401c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 901005530 1250 901004280 901004297
    0x1170c040e070e10080603240a02030727030605062d030f0d020102220521160b0304050705040c1b0c08011b0e030304121b0801050703020a08150a06 65
    0xc1d24060318288003058070003440c9043c800800135000300740d100b04560661180c440d07071140f550040e4142007168142c3c0c0d5104a464643d940d43c0070030002952020304010204140318054030100080c480485c0320101c00f070340420080501c0c600341743d402ea481c081c01c00e81c412203820f01c0b0384c003050001e001e541c1c1c01030601d4004100306a11201c0042e0820070380810415190085108c0c01442582c1980108103180f640742c49480042440403240d6500310060240c503400111118502e00101110035070b40141c0d1006030215080c16040c0e08150006451582c46003411150100520040000902002011b440d09580810a01c440c00500402121004090b05208202400d151052085449040c40580b0040000b4003110218182041660180c0c0c0024000a40c07c50303c1c84441d0b140c04421134040f50741800d40d06240c0840354880700d0f17803411400100101000106e2002812060a0041c07601c241240d03140183c89003404100500031110040c0840700e40f10407030042c0307016a13848403050829a0200c0c80c142d0744 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 901006780 1250 901005530 901005541
    0x5150f010504050f0f0a1b181203020c0112321312050d06080604051e0304060507030e01111e0f060c1b190f030f081003020402030709030c120201170c040e 68
    0x1c0842410302424a04c7d00c190300902c240d0041c01600c0030a15238100c0014207640c541d5000e402c1028a100100141c0000b05078401640c400c40b80c00e4007401040d1000910952405681c00c40c425081100d15600b10011180200f6140c2e1403596541c05102075180c41071070166a41c4130841860090000b10a000010030a03d01d0503580398040c60240040350b007100c44900b01810007660341c0c80d00643c49516901d6803288100e2200c1c0c048185c07000c80d109506d4050805e443e90ba81074419078490dc40351410424840c00725124040104907100944000e0000380c24070214000e03031030303060500328002d500d4158819801e00c940e81e09584219400c5000c1e10021200241d2014200c030f04201250a0020300c0c5030040d01407005000b59101802442480782c3c40790304c1007d2907001c003503881e05002ca402c501c0c00010207030208094202038000355408845403818007802a00c83e5240035490725940c11a401824007150240e04558101c4900da251400791a805256440e2080a503d81c40c0f00703a00642103882d00380404201c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 901008030 1250 901006780 901006801
    0x10c090b1606090c05100c0c06050f0d14040c0801020a090513090f050c0a060c11011206090204080a02090a02070f1205211f0503032505150f010504050f0f 68
    0x1107100e91016040c090001281041200740803140625403290314940c4641240e240240b41015006503c2101c407110540b82c40029140c60304405040110640200700c07040840425105500d00f03107042a41c21400350406003051402031145070060351690380704004200070150852400c1c01207a5040b0f03039460084003005400c00103000e00500090401c0090790240041041c0882c10f104030074400d81e00b07905000c0d40c43c1703401ca42d1183c044034013410005005580700755551140e40040c425202010012070500d40e41e1201008036840b992000580b6000b0440c004214a0a50b150a4010340c0d010307801c0d410030095448507524480581801454403040500352031205006900740c0358684a0710400850601c8002140040603600302c6e9444081e40781290f5900d24041a074020500341d6801400031402c0500349441906a2001000c5440541d01c00c034060380e0000f901000314500144003142886d55a081041e03600c00381c8201a00010b210320b00b802d00300040d107503108250f01d90249860a0000311034881c0303180c50 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 901009280 1250 901008030 901008067
    0x906040e0105090d0e0405060a09020307021c0e011e0e100c0c0603020403061422140613140712080d1e151e06080709080304030b010e0702010c090b 65
    0x100100d5082c503003045861180840c401408010310380391000c0700805d140c1040126401190304507801980703420140700d6a00141e02a582c00b9000307004503203c83c89004076594000c0ca0705e41c0d0181c0042c464a8640803a0f50703014121042d03141e00401101200082c85078090506100a081107008085603001310341e215208001030800c0b00d0b003000d070908415498a40003400b9622600045d200c490402e1034044088039010289032017002400e480325000b40d0103000405104080c44001d8803107008502e0100f1200100380801c1d8011001d008001600c0800361800d0500e07074400c8182410150044a020005861004131020b01a40e12101160784e4240614847c0010003e8845c00b0160f00350000e8004004941603021310800260307400c02c150308542c0d8803c5a010070b1020a0350003080090304a00304180390182d00306641040c06401e00240343c0340c0f9505481d185401c15031084e900399940e080104031003100030900c1d0342c01030241c0c4024498a0003441e00644050312500c00e000b803030080011000e03101e400b0310348003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 901010530 1250 901009280 901009301
    0x8060c13030b0c09040b01050304052503080c0102090a0501020a03020d0807090b0a0e013b03030f070f03030b063a02130305070b130e06011407050616050c0309090604 73
    0x4254060030500c02d42040b81c4c01c4110118000d40c0b608103003c5c6075601800607280700d45d07400b40042180b00344900303035501805030180030b448103d02d0b907038404000909010090032520058031300040c0c4680d0700208100322010b00d0f03440030381550048a000340c041307079010032188100c2440303003091813443c0c41b51001100c01d064540d103e000b840710040b0341d00c95003a40c070403a10702c1040000d907103101482ca103d0101c1a00d145440d11101020542c084011402c141c403100809800710004054a04007441c03250001c0f00c0c0d9000f80c000b1100f01240000001c201a05840780c6140c1c003006403000c1d810015001e9003500040c040e200400c9a2a80b580114024480032031011880c44c3e00000b400e6480310210001154283c200b400112000c4c0148400800d80b00390100039106805140502030300007524116500c0001b08018080c0342c10401d50180301c0720003e4135540106000791050006000328a800070448105101d0b11280c0d0082000421521602135030000a4a40b40310080b1031004064880c40b00242c02070071421071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 901011780 1250 901010530 901010543
    0x60d0216020d05060405010606050310050f0f090106051c0c0e0906030106170d02060109020a0203041701090b1e0a050f0601110304030f060e060a090804060e120106080609010f0608060c1303 83
    0x10202d04005003c1001d50080f0700ca0b400070301c44183c86034004c2d0f031344c2c0c04115200300311081021810406490190213419021381e014082010b03240c0e01e50b002c5204028241c0041c80403c8000400c00f41c0000240a000c4ea043c0050504000342508120300414010b02054075034480c1c1039260218416030340a60042008202442a0f03818801201c8010360711a900c410000d07001d4001c00d0700001e19800c41d4001c98907040345c1b83c0d000e03600d0141410354400c80d00300b0350800a4080d66a40b440b540009800d149a5405001d5401048442072880420a541800d00405903400b9508180c144070309100d501d04220303007040e801d0800e001c8040015940324550b009640c800340c000c068071200326040c0405640402592400e40c400c0d9912542c85881c40700c256419104000c003120010041004894400c0c20480020740c0c0c01081d240e000c41c85186003d09442072a004500c941d0024000d01031014002d00c0750441003c5e004405110700d92804481a460f0140106000048140000e0200030305c2d0700c1d14041c801035035110700c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 901013030 1250 901011780 901011799
    0xa0627051f1a190f06120b01020c0a0306050903070503120601020f030304210509060711040c0c020d121b1101080106111c020c04020c2505060d021602 66
    0x6199503219421420310340d000c45800a0340600020034000c804094080d1100c2c0e12400382c1e600c003444001c140c02e510360380c0a19060301c00820440114603070040100a01d984451115402d00110b508803020103e0345410f550003569164900e4550b4002501203942042001880340d882080047c1144a2490000c0a5020000e981041d1010060031240107402c203900315000076070002e411580d02c1c0310a98001d4141d90011041425101ca1a404150081400d10f0304a00780b411000200c8e02d40c0d00940d0302201c40d520000c10381d51060809208100c0035141d50b14041d0f01d501303199008201036000410000d44541001c100400100317004c0c83c00101e404100c2c00e80714900003e2410309262410908600030300080100e000007a40314810b03160003080016104c090b045880b1010194003018101e00400d030300b540119080904140e0340c030300c060700704445a04080e10740c01300c00840062483e005100124020908070805105a8503254291604a81c4200005950310950b01c046240e0140e84140290300c6034070300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 901014280 1250 901013030 901013033
    0x20c030f030f0108070b0708090a050604090e16051c0602130b030a0b010212030718080d0e030709020a0f0c11041e15030506070e0d0b0c040f0e090a0627 67
    0x1100154030490079007400c440741d641c0320b10304251104024403800c3d076104007e01c1141c002c02d01180c001c020a04000302101f005599810114826030001d44c0903003c020b03991040c4060000091141741e10021200556070545400c110010303404c00398000c823040a00c90750300034042c200040345d411919209081c11542e440f00d695400c041400394411a9240c1d41076013491508036640d40000f501d400b0307041424403014116924081c1c2215602440601000c401d2424000083c4d840c200340001c41d00070281d0303a2001001fa00c0401454030b03005241d40101d160520401c48080515403040c84941d060340c40e40740500c01c1080c4c90a095001c1ca03502d45030681c2c41450281b00c17140d0300400c02c03000c0a80b00e2060200788105c117000701038003487d03c40b5844060540c0d00321030005545144030b030504c0250340d00d00501651601c1c0b5a500c6038100c2a42c101c0b2440540c1000050501010000c00c0c1c0007030040c50390b04000b030298682020700c2c0e43c50b00180c4030010101a200c4041c035210300540e20018001603039640781c034450040c45 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 901015530 1250 901014280 901014307
    0xc0307030f0203120702010c080903010f1104090e060408041403030c010f0902040507030b0d060e01090b09010605090108030c030405100507060f06060816140901090e091005070807080712020c03 85
    0x1c0380d04030b100c0c0c413038080340c800c4403108042038a138503540585460100c0c10042c6c8680140d80e00025543c0d03810355031010aa100d0780e10900c1496100003a0602c4280c07118103103202c000807690b00404039000c60b40f0110420000800c00021a030a5a100498000100602c04046499030141280244895080c580d201c030701d0700b0041c1e015924043c02214240502c0d00c80d98001d070b0860ba0300b201c0064028100342d5400c4042011a003029003003176103100000529030001d40302c2c1010340c94242c603a040ca694440c0d504014520341244000d0142a102014524085441d0505e660301d208500c54a401100401d0200038120f0040341070707400b81900400240200020464540000c100b280900d0001c210610301064110f003642207403000100468451107248640c0440506150708800c005504203d032002c00407a4019803d05003030b0103540410001c00c84101681025400e07203800400140410050b0b10821000c1c0d5405822030f41c0041d0b1506000c032010500400100180c418015040c0251000080340c2959448 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 901016780 1250 901015530 901015553
    0x610030204081b0d2102060604181106040b0c0102040509010b0c03030a15050907030e0d18141203071a070305100308070317011e080a2303091e030105060102062203020c030703 77
    0x1171780d0a94110780e80e5001080708a516481e01141340c0a40c0034500c0000443c180803101060a00a0155081a54580c2e1510f483c0e403080c5030b090700c1650041010401410304c01c48050152298150490400702d400100954a00004100c038402c1d0341c4036010160101030b11050303071028040160100140345420100500076240039000c21103540b0a001040464500c60410301501e032614510380c90b0703118175102205d003040050301c848552040b1450100c29201c2d600700f005122083c800c0d40c034403850f0400540e50241a41000300820305060a000030064501c101ea0300c50070540c2d03400101542c0314081401c0880f0000e824600c005080100c0c0000880c2c0b00a50b041864a100c05440107825607540f110b440ca0b441d8148450000c003109290000c2a54034200c2c070041184c1024264202c9013020042c100090b07002c00d03102c110090071070030f10040e0b2a207402e00303006069210300c007030008150505202c1415611901501020f40c40060710002c103000700741c42070140014990004003203c9641c1c1e140d060107852035a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 901018030 1250 901016780 901016843
    0x51506091303080c09010318121419081504052502070803180d0510020403021f090611010f09120f09080a062706050610030204081b0d 59
    0x1040e0009005081607240316021541d140c3c0d80c200c240c2e01c484440a030643c00040b02a4103068450810400320720004601c1141c99010b03513048104101a0304c0003030104400040564641d03202007121141c00d007807440145690000c5880d00740d42e6941c403201108903141a01000036801810641405009102c007540c000c4c440e12065245d44000356000400c0e1b90b9601c8a1158514030b400520801440b41500b1080e81180d01010303104c10010b03c0155955410600d114003d4501958003103400d0095007068070102e00b03c8450b079078115070000c01016014107c1080d03442644100007020421909074802034110303000c01c00c2034210a02004040745050407004814505440001d458114018403d6118090031000c0702d800b28050503411140d9182d01d00034000d540c0060030340102c6174202100e0000301c242d0241d511070281c4400201410900c3c100031000c88240d850008241c010300090050b0300c0082a40d220b008400b650400f010b1485d240407403010340d0200000351442c80c40101403090728841a4005040742c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 901019280 1250 901018030 901018039
    0x904110418050c03150a1d0f010203071202160f0809030d09031202031303030807021c0201020316030b060901030f0b040608030c071a0f0d0f0f020702090105030c0d120903051506 78
    0xb603c3d42895034903611400c68811001c0d40c80d010030030f000400d600c02407500c0e550080307000210f0fa504040d03030300d040da0784070100041d80e50000c100050030f503100d80501c040046c001001d40ca00314404424401d0790100150192407011000b01c1c100030032543d03c0403217940b060003031300782c4404140e441000b40402900c0d110645440c0c2509004001c1e41c0e2002c02110a40e0548a269200460840d10111003851008143e04107512440350145028076107036550403524861a40050380c1e03032520303241c032001201e00701d00001c06050801111159a81d140400d9030400701c820301e80011340f5031013080c883d0040d16200052540091900c00042041c010100080940c0b13000f031022143d071903a5540c00a4210108142c40e005242028040801f072402d41e540200950124030320007040185401841504444201180b401d141e41c0c0003880b00110300f081d0000c0d6004090032405400f003001c080300400c40e0000504401800c0300d200c50003c0f407005000e460484061074102e0308882000204a00c4d01d00303800c2080e01d005215 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 901020530 1250 901019280 901019293
    0x1a130c2a0c17210c07090c0e040c0f0309020609040c2003040b1b0c030717070b1c11042c0903090d08030627040c0b03010303020a02090411041805 64
    0x5071580c0c444100c608000d042c010040e50b64103400c03c07107032104142d440040382d1004000802e10004c00704105006408080c4c00011b00410061001c1d002c520710348076a03070141e0304140c081155650015005000c01c10360703080100d5103565a00c0010b441d40f098100050740303786440440c0c601c00f0740c0018040010005008880b007005401c2e103d10b6628000c0340324035054003008000f0800321214030392a544a0080741022103d01100d2500020b081c050550068440c2240c2d000f00300c0d05010701041349400910303030178203c03502c1e1124900b644901d0354820740a9080c10340d10b8070001c102c50004134007224000d050408030380c204900040c00c030010402881d14015a20300c0a40e003c20850b14020040741c0c1d00090003450050a00846e03903421100360001015030f07a0000880c0301014241000403070b00e0078000700c5103225030300740c2c5000d01d0701003104890303a0845c0000220500050000a40000e96103814a030120303005401c07551140b82c0b0f4800c40d4054503a554000c0c1c10500744d02400a82e006a282c1d0880c0b0402c20380e8031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 901021780 1250 901020530 901020539
    0x3090d170604090f0f110f060405090c03062805030d0813020918070608040605090a020109030b040c150509040b0301021e030417030c07061a130c2a0c 66
    0x8040400c40480c500010040011501d1032416502c0f85110f18441c1d81114004400c075103a011a1500c51142529880320340c544400392442d001c1d5501c000020100c1d04182043d0900c8041945c881d030007040e070506070f40000b0202c0d8481e43d032400f4100c081c00b51b21142038104604c41c101440c0c41307003241c410540240b04102c0d107814010700403c1c440b403042d40e02d070140310605c40d400d0f02001320301880944030003120403e00460100406040c010400680290b40b6000800e080501d4000708480c0000d1150a00380c02c00030f94940142c0c0d1140c4011304070f90300b044410701641c460741415020703404154800d10a80c6902e40a40703206c00c0c0c1080c050304102e50111010808a0911401d0609038072600080c41a01010858a4940da95010000c0c1d50442d000c0c070381c000d00e8400c1d0440b000c1141d03882500c5540002170045428000c00c1000c4c01103800d0301d0f4841900b10003004a0344040b481c10350b1606141d00f800c50700c1d905800d5000c0c4c03250000c42481142c1d400d4001e0100e100050790341c3c08111121050714018290340000c036 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 901023030 1250 901021780 901021787
    0x20a050423090a0c1d13080a050307030e0609160e06100c03031b0806180f070c030302210118020708090d02010c0203070e1f050612061302030f0610020a1505090f030d0203090d 77
    0x2d071b154010650615001e5680801c49007684018880c80030715988000300b00100c4410001c0502c80d820440c002e1034103881035201c540700e04a0399407200c102100c4981c00c10202d51035281c0038041500300d41c1040030a145e400c0c6401d4001e041c2c1c08501d5844403001e034400324101580801120700810040c3e0b0400303070407140303052160311094080b40d01c4440ca03248000071500040c401d030107042801d07000345401420174001d15041d8404070540044100b0b003000000051158407c02c1440c841040c0f201c0c1801c601d88100742e540c07540745020340d61003d07110301c1180b110740c0c041d640100440326a00758001c0a481e02192030714039580c400380c415241e150034650300c401c0181302329001407401d1055460040c6007130704001e41856004081c810081146030070150200c201c0140e20f019002440c000d507200d0b211040c017484c1c0003085c4507180d180101f2881c1158007441c60303a0041540d8550070310415003016008200e581d41d40c4035881c40c05100000e9994144070002d804d0540094642c0998060f416007420360314150154103048 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 901024280 1250 901023030 901023061
    0x11209050a03050a030e1207031106010303080a020d06030b13060614030c04090819020a05010b0a030b0f06061c060515090631060c020a050423090a0c1d 67
    0x410a41c031852212000c2406600500300b605101d280109000300140003490410036005011310900d00041140070403d03030000a20400b14840000a010641c590780340105003140180080c108640e0001d80b04405d41841d40001d80610340112450071036007014000011210510390054030160324040c80884c8494402d00603c0c851034005000b0948030003000204002845680e200b01d900000401c88603900d4036281100582005660b00640b4104060342402800c0d2160412058443c004104050000465500203e031f08000410410f0110707540b26004070340140301d440d0420f00d5502020840c641040807680124040c1d40060b1848401800c03502175807507041c040c0201482c0d00c540c0600c0180c40d070704000401030020b030320100e900f900031400d1041c0541c69044140c00480005010307a06400030341c20041c195600401d401d80b400c1003004500d100c0c80741c11341c4101090303100c1c4401c40000311354501c0c1d00b004103154194201c1402086181e0722140d114002d51041c41500d459500c00300003520b01c000e01e5903507 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 901025530 1250 901024280 901024283
    0xf030a0501231e0901091a2505070b09150405150a06050a03110d08040b0c070e0103031b0642051e04060504020301380706110d0501030501020a020111040f150912050a02011209 77
    0x4060402110b0f40c0cbc1d0002020000b030218034030748a02810010000302051002d40281e0186010b07110303118401c00000310041c2e004000322420b504151042080351500030921048070f40214005000c10030450008008200c19840904136060100d0003240440d041c03c010505a41c00342c0449040e50360712450511000001d00c00138001c50080849118052094028804a40d00c41c2200055a21140415959181d003180b54110000d8594900403020a40540c00c082c01d41050300810019502e064001201482c002032921340c491001d110001003074903960081005003100070819900c1c4d43e1a460204149045058000c0c000400102c0a041390044100b000741595502e58a86280c85450b89800d00646a10603c5942c011030401410114650320300c280b90282d4400c0002503035070b5000b007400a0944400029410f04034800f04400c010481803141403134111070b0044050444103000080030b4414041ea43d002c1c02860b61041c110400b017100114070000d03a24800d03210403002d4016420b00f003007290b110700c10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 901026780 1250 901025530 901025537
    0x60d2901170f0115140303040305070b090a141018122001050304200d08120411030c01091503180507080d030515010e0f030a0501231e0901091a25 64
    0x2884004c1c1d0303403a11a07045c11009421285400c0e07599039842e240100300d900242c1b0101001c24200c040d46400c100010041111041c80340300c0c0e02d60000021a0b0016005070b21050003884070110700703000501c00140c3c000740b54200160807000c1c61030a142800d19404403000100c0c00c0074116002d013540c01981030341c1c02240c1010481081d55454a0b0341070078181c401c080c0315888ac1400c801d000000d540300008100240c40d80407410b03103134100b91a000f400c000091215501c6500042c90288040e640034005a080340c5040c40001a07a020900c3d0035801010200ea407405400c42c020002c00038004002100801c803040c00007200c00303049480c40c2c00c408172401900d8003581c468920130620703000e40c81100842d0300c1820060400754201c2966001a2804400d01c0f002c941c00e94480400c1302042c11001e170340c404510307000c81c02c8044c1c44c586410710303500007003070102c0c07030014a0a480c02050302c0d02000d41c015650540c1c40400c9a80ca51150410444411002c581d400c0103c240096100c007510f81100e6440034401c101d45 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 901028030 1250 901026780 901026821
    0xa08010203010e190603060203011412011a28030f03120b010909020d110c010e0f0c0d030819110c0f07080303011202120d03021908060d2901170f01 65
    0xb103060000d40c03101c80074201075179180d48020000c12011320042d0700030003003c1401203408480005210864000f02800452039143c240750345140d9446100500c0d807038004840410281c80748803080055492a074100c100500c0c07401d11301008100506442160040c0a43c032041003d80000c0c1d6031100795103d0303051480c009000e4100400513502643c02a140c3c21120b4000800c0315104201495210340114007482401d07034507180b500104203402e01014165403c4880030b40700681150300410640081802d0003000c00100c04002006880706a98040b45d02c40c680030300344150a92010205000d40110b04980303007a0058605038007560800003100c804550a8102031801c5078038007500260b800256180aa0b0403072030413140745204030310a1103603800d13012281d1001616610b0740030417a00307140c0358105004144100c51050156580d01c00d1034030b59180b40c2c0440507a00e0010310401d845036150f402c10009054030f10000004c9942c03210026078511180110b03003202c5418148040060980301041501058003d022 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 901029280 1250 901028030 901028041
    0x5340c03050d020d0507021c0203041a0f0c010e0321040c060e0a030c0b0d05070c05191a090c011202071121190b0a050f06130b15090a08010203010e 65
    0x50000d441e11188944005013050304801503181910340c1100d48400503040000c4040c068003030b0701141c0982c413160f48011820241802da404e0105400c80380d1031007045201080d007501280011080301c1a80031084000c5c0003401d601100315603650860100c070b500b110701e0180c20403550f87c0741d82d50785c038801e54101d000c21841600d030000035141100e000055036042068108088007003034410400c2401081d0380446543c0d0b440700002c9503021104040d24020402204003101c002084000404070341c91501903880b81c20602c0c252030444141d602c1241000301e1000c9e170f0000c1021481c2c000c5210003100d5001e0301c07071600f00100e08101d00700f24481c08400800e0015201d01541044c101001c0e604581803c201e00300351500d0786c0070303503091406100005000f5000030303607011780d810040d5071042c44e504244144004d00580c00c0c02c40116061940c010b0005001b00b005009905590840d900051051f07074000d402e2203034082d070312140b9001ca40d209440d4680a00712055001403042414422a4120340b0304002c80e02e1140c41d107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 901030530 1250 901029280 901029287
    0x9060b1b070f17101811011b03020604052104060f0228020406050910090e0c0619180e07050304060f0c27150f120216060c03050c0f07021305340c03 65
    0x10003030580c0c10454000034400b140b07829030751320103a9640681c00805403440c11745003030ba207000d0076182c039000301142c41011410004224423f98042d50860306040e1f50300850050100d150a46044900210002e40c603100082c0540c110040072480b80203441c103101c02c903128401d100305d070b540030303140301007040d041240401c000d030000da02201e00c11601e00c05441c04401d071400080c0c01a0040803802114449942410b03040c107410400ea2582045a070000620305480c0804c003504800005060000740b1000000040c10820305038840e1072841410300f0100715124100b02e00402c21100e10000810102642c00041081d2009421403000c032201c0071700700c000001802c041100c00300700390174000007400440080120500c10b14000362584075500030070134818021504003c01640e02c0c0030404070615282000b881090b4010700c0480c0ca48a85a82c0915aa045503102092007903402080c0c85441c175140c007040c8801d18450200084045680c03049002d001c2500f03900000040c0c0b8403d801d40c003c03c040401c0030740001e00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 901031780 1250 901030530 901030553
    0x70311040b0f0907050337020307030213030803011508091b2b020a05060c0d11030708030a020301030b010b03190f1b0804030909060b1b070f171018 65
    0xc042c1034410400c4105000c50440941950a5000301d0b101108011240e0f00d0144030844030481d11441d0094041413010b480b84441e00c03808520282c80d000400120750501030f80450701c64810b0558103611503036a90401c846107810070b0040401c120854659100c81911075403c40d800b03130080d4805080e0402071b51021f4000a00303040c901d1904051408400810300d0581100d007a03400c001080c058546a4007881000b00d10701c00c3d900710511030541070040310103115001419142080e90b905140d100c402c201196213245001d0880024a0014000200f00b022040381d00598103ea108a0404400d0b0b6240c007070480c46c0d0301084848404035002c0701f512045152054100d82000750007560002000200703074150000301e110301e00340800410701c05000e020406500140400040034408420441582412400707944e44c403411034400d200071076200c10303200f00341014000c4400418580d41d816440d80c1d95403641a0b100c2d002030980c09028065904a61010082c2d80079483c07914000c2d00c1e243d106007903180e0b100f0ba0100d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 901033030 1250 901031780 901031801
    0x30608120a1808060702150411012d05281202090604030b0406090b060907020d050f0c2a01081b1e0a02010f05090a020102120a02161202040b0307031104 67
    0xe2042c0d099602c1c12000c100c007400b400c80d0b2405007045140070a0041c1c42e1124038188440103540401c100000f1401940121410709000d02e001c800d41c0f50801204000303003e0158007030000742813001c2c441d211160000000c12524505111107030143e5200c10480024002c140c006ea404541e4001480c2961039007640105480180140b226082c80d80380d440d40300f4040b004440c110b50281c0d56410400500211240c640d0f8004000c940000d651321340b05400a4454100c44d54900a001011802080b41450705003036030006011300c002ca89071042d41040607031516040004129110b0705020040901e540314090061140e0f080a00000ca03901541040f14035907800b4112195044e00008d40c00c4040b900004020301c510b26a5600108280006071000002c485029040c4100c5601000081005036008101ca6904482c012001c2c0d40b030301c6141c0d00076030615401c54a48c000a0083c000045039281010301141e40e414020b89040080500650078980d862180f40006011002ca0880e512401d1a0503000106000d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 901034280 1250 901033030 901033037
    0x304030b090a080a09050405060a05060a05210a050f0c030709051c023c0a0302010804031b0506072a02120a0206160209060a03150207021f110c01030608120a 69
    0x904580c842d03c840350811140b80001402c0034104000d10300c0c0500a040d04018101c0d000c41c4138a00e48070010302940320b507000d600140400810042c1042501d540403181c0501c410700707480000d00d000e06000300104011602d060032021072101203070380101e460301074a114404276150207001c1d44c1090f040018011168581040314000183c0810051300c0d0341410224885030964000f806800d110300c0340d4088030a40000c45a00103600c1000c42d11580d821a554088980a09200d14203131a5402e0444114074100c445c1e039180c00c0041541400c203e800074180d48540d800c0e41d43c032000001c000007814001d00001540b81d1600d1f6000511178054035101c10300c1d40c03e1020394421601003680c29804510641c020000c0c00392002c4803401c40d0015401c05540c02940820b044032110f01c0141559180c0700d040c00d071411944080f035408104001152251000d40c2c021003c240d9a003584411003e9006203000d0300440b02d10b815001d0500f0040799940039015074402e8030341e40e0002c2e0420504241d40004a5000420402e041 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 901035530 1250 901034280 901034293
    0x606030601120804030b1b1b0c040c0504050d0204180f0519050c092e171c0503090a080c01052e03020d0602040b0313120f08040204050a0915060501020118050304030b09 74
    0x22241c400c00818440d0644038809102e02c1105030041d049c00440002140280d0034810384d035240703a502900301c130b00341c440072104510111000d0003c41e00030480c80c9031144d015460180d4510a001001d4400c0c0c1c0d141c9d11644c2140e101c500c98408040740300c1e10030700c002007803940441ca00506a20f4510381040d80002c041c0390030305445145505000a16554000e142e049140303411091042000901100d0030108411004100702c1e4010180300c0003043c9030511080c02c120010000c5481010103002e000012600b0880954540d450f0044407802090141c4400f0340042e402032221030302e808043e0f04803240050107200d03404414a180c0034130161070214a4104c82c8980c3c20840450710311540030166000c0d5200501c008150070b6286029684038807421490740070b00420006080300c003640421034560080d815070b40440c1c01d4071080002d8010700703a000720040840c0c0100d11460b00412040e40040220781c2c090f40240041d4004120241c4105000c10019095800030441440801c00e81d81007141c0100240b0200c481 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 901036780 1250 901035530 901035571
    0x1a092d0f1008091615090812040b1b0106030312051609060e0f10021606020f070303030f0f0f1b080f16020f0a0506041101031b0809031b0606030601120804030b 70
    0x180a181038010400d08042e4945017001150301408070b00161100c0c2c001041440e80720b55105505020b0b0340300350209802c00081c44da1007501111003014410080c04028041d10b038030307442c1c040c2418200c41c0380c001410b8034040016429400000e2440c20303d07030154842ea821207090103000c9900080303c0c4009a081100e03010f803064036490f81d41e806401c0001c030360301034016055204403041c0e241096a200200b15440341082c4a81e0391030200300481120381c541400941028807548204c09850105141d0569500d000744041d08501550401080c1824600d62400e071110702c0d10b41642c246006440380705424bd403140c0054142000401c0120305207205004640446000e20001e074580140300720200d9040d0803e506200800240342070205a12030242024002c1c851201d40043c2400c4101c400c032001c0180b41c9011455000062003100c01d00345602c410b00880410b4528180c1e9612800d5681900905c5244000030301c5440f102e05180d0b550b60300003103140c541880c41d2902a04c0000207442e1080400c44005041e9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 901038030 1250 901036780 901036813
    0xc1f090302060c0703060b0d3206071d0114120c04030819020106050411070b071209030c0203060705072406091a01020c191a092d0f100809 61
    0x103c1c281480020a1500d06514080094400700c15001c0d000c7c6410841c07a0780024130b02c5488a900784044103100144550110450280300c80b81d0801066601841041c05103695111019407201a00450400b030b60800c91001111130142d944151200c483e01400300d40305100701d12606c1394108003900c0c88079007090f031283c6440c4c400307030310181807494003d5220700c00c19901902030241800409040320200038441d0300240c04110342c452500300030041d02070030000030380990084e8041c3c07401d04505282040f641d050340c60b01034000c2c2a0079009a11903c185800205a54420030403a15070071740c0400e40403007010f038224080d080d0000445120195507164440410340c00524481c03c41074201390000b0340c07041a805400a814a985411918040c28003e00c2d01c4080348407030f41d41c80c411144414080d0b480b050000d14414001d0240c13582a80e40b000e14142c4040450041d072034010750100c0c2035420085006074032401c10000c1301d01030100b80c1c0c221051803011400d10780a080380c0d40e4000250307015a50201902c41c00c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 901039280 1250 901038030 901038037
    0xc0409170307050d050108071d0601020f060c0901182940030b180c0612010f2408190f1505010203121303020f0102030108011b020c1f09030206 63
    0x2c03070000b88082900e40010f00b06025813401880305c0d6010b4100d09040071030000c103581c240020150501d944001040c503507442080781015201d100002c0d03a030300d0700340300e840310f1540d0380150521400a0112031107807290360a41100c0e00102c3e1104140030f00303030900c01800d074440d41c0410414260303030220a01144e01e020640c400d00769212000c0f4803166203413a0f00240e5441c1ea01c40340e924990041c01d1060824030000700280a220340041952018021011000901c1440d16000100b1603402c110b0224158440451213130200e1305a030301514075624000d490b0444c9418541280c003491b02c807000d01e000444102e41c021a601900007003400300c4504022286010b1030180c454000902072099a01c9074441c404e41d80c81d940c20006884244051442c0144018214020543c0a00242404035610400c4401c040c000c0040c2c0c01c02041580003036481e5a50303213070084d0090030700c072040500c5141e40e4005000b0252000c54483c02c8a40d004111041c01d40b0072400b40146c9540403424082842694017022000d42d030b500029 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 901040530 1250 901039280 901039291
    0x102030106030506040f02031017030d023f01031b080a0f17070209060411070b0f04060606050a020d0f1209060b130501032d151b050c0c04091703 64
    0x864913051203028003040f600904580580d1170310600c140118041d085060f40100c540d80c4001c0f4031050806048942140305603913040c4900c07840003680007030410384a604c0e403a81072035010781d180d042d15000d00304200c0f19010a2840d60185540e00043c030000d44001c03100d00da14201150350903911612040464a40000c1c00c2c0f0a40d11401da0340942d504016154080c1c404400602010606000050f4040740c03c4c0c580203400309110366140c180c20302881c0d10705001d648089802101c840d120f81401e5814003c0d0020a950a90380203003440380120b2002d0040080701e440b003a0301e07402044214014503046400d50b00e01c00c0001c040101d07040302c942c4250340d40d008041e40c1c9401000300241e014208410442d6140a80c42c022250070300780801000030424003000e100c40b0071313015034081580000882c000304000729203440050900c5d44ea040d05c0908118141d2005002090b040d07680c08910420040c192000e0098200761000c43d0701c4070709580524100342d040080554421452410007080104824a058000700d07903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 901041780 1250 901040530 901040537
    0x7150c0b0f0907080c030c01140d052e1505162103150821041e05090603010908030a0b0d0204020a0f020610030c030201140c0109080405210703030c03110102030106 72
    0x1d0090342c840c1880030b01c1c02407003514020201d04000e800807075155048102080d050104001c464900304110408507040b03980c03400020405807510350400815000b1f1030401280d0039041c00c0750304a014a50030583c0342607840c41c2e4801070882c560100110f42ca0f90151042c0e007608507400c3c81601c0040c0c00000302c240090300b5010300d040507000b500402800c0b22945411510250b1040c1c00c02c008010700407402c06d02c101c002c0a090749060364211816800ca100d96400b0b5401007003900004003d01d001d444070075050f51411101440b2030b40300e074810582642c0c4000405005c0701810408100c0542e83c41d80050840580075103a00019281074000074202d8008840704404079800b641c1d40808968182302c11640440c281c0e20140c482030450300c0e1084540c03c2d42c000241404510042c407440f1020b1481600d0095420314000d000c14a450b150584c89a002481420f001c0c0000100c400102d0407004910b210411404005050907443c54030110ac0da46030302e80d002d07801d10170180c51041114100b0300066020700800d88 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 901043030 1250 901041780 901041811
    0x1e070b070203181912230102040614120609060111030c0d030516170705160f050c04200304060e0f0a05070b0a1e050408030c0a17030907150c0b 63
    0xe95683c1d416106035150751082e020f000340414640308940150065503040c0200c50501025031500c400400c802981038140e070000b000b01c00c00312801c1500140144c62003a56408050580701000740e07902d00402c001d1143c00c00140300000e90904190845541c0b050052400d2841132407122005415a4402c83d170040c101c0d000f42d400c020130940c16009051300701d5084080b07020205c0004500900640d15805111040040c00d808200010721503c1030f203070001179418052944580d07030b203000ea95000c6511011111809590b621070050711b0184502094651584d0b0104030031801c01d00e401d031443e0b00051045a006960714210380052000b001a5006e0251074001458030485a080003407411147d940038510306a0200040c4c0e0f01198061203021981203900c08610501810389001e80b01c03401141c03c000440d10002c201a0003610000501c0450741d0300804110040030022020725a880c4011602400c0b15031000d0f0042220346c0c1550300381503501c1c4661900303404021f443d550b0705d010359005030b41d101e64070b03012803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 901044280 1250 901043030 901043047
    0x71b05031e1207080702120d110301060c060f0b0a090902151303030206010b0f121005030105190f060f2702030403030617011a01180902030702070305100c051e070b070203 75
    0x2804043c0c101a00382450203c615040340000e50b0795242c410345081c200d0012403005d21070741b81900080c2c01c04100c4002503461b90b0f103445004040500c2002d0503078885003003488040020b90700d4410a481d5071006030802c205181003140641c06081441c0080b601f0807488858411602104405070143d03e401c0d0300d0284581d859810000c0ca4014184c001002c80001044800d4007140070504071191001d5841c083c1200350707039040b03107140860100d40c04540c1550a0a0802c0125000c0c205243c5080400075410440c20100d94008001c495050007a00b0800c025501c00b4030810310342c00d480071040901d50360300c12031004000b55110305a800c15142107010a807129828801200c103a0758440c6902e641d1002008201d40200d10341c0d0703d4841c042030083c14450007054482c914200011590701504092805560b2030500903002503a0707414620003510180a00361961301c003c5064050444081c160340d54030340c2080309a035800b454019185410a41c000003c10404001480c10220103100755009e80246881c7c2109 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 901045530 1250 901044280 901044307
    0x81603120305010509060f13112101080a030311071403030609060105030405100509010f0912080717011e03150623010801210b0c031e071b05031e 64
    0x3051040018981410010701098607200e4180364031810440b810581c500c040000304071103034131502481003041e003042d0b168000841e00000030440942a503040781002540030ba11021520780a0140c40740c150015560003021a00c00c0d0080c01c1040b003080781c402c0c5040c0059480c01c9162080201000c2560008010407c40b80b03403041a0a501100070b007089480e503e006e9842c0307515442802c5107000141c3e51500404d549060951005c1e801a510f4401001102c1c001c0c00c000c440e0b608201c515000007084100010b100d184a00414204920580c02000159090a00f524003520258504095525018500001040ca04013090f440b025048800141c11030414a24100c0961081025401070701308000101079641e00561282c11079266900048a04074061116034840410000180c03041511205011005070080e00a40c0114407501c2026420b0400b0704643c109a2022101d080c00304200c40c4d840804200401180403045d4031510560f80340202000e89440c04142c030180f507540080300403445200903e81e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 901046780 1250 901045530 901045553
    0x31f0e0303040c0612061404151707030b01050f0108150f060d0c020607090b22030204060303081608071d0409050304061112091c0804050405010b0c0d09060509010513081603 76
    0x30381003091000c0d031f00b02000c1c01480484441c440340a1503403801021074000810a080d0041c0c03451140f02c001640e035174800c00c0c0c0d5440700d600040c0e82c00682d0310000141454140e0708800f40c2c0b181070316402d07129503a40d2940b496038100e00c96416042540e40d40340442a80d115401485160400c400001d04002a00d000a203040001003080d403d01410540910080c0b20740001d03503d240124003001d5016010f04040c01c2c4550310a0b6200940190403d1004010590024030071449400f0b0050035a1b40c0c0400f1000441340b00c2c01c10f40300751010034110102158640d800c4580d8000c0580b000c0d101240001c40c1e41e40c4d8510759800784d40f20358006540380a00b981691070912081081c0244002d016081c0310700c02c0c000441440c0d01307808800300d1340c1e03010355442c08100e4a403003520024000208100308541c0d488107406459404403000070b8050207482c60010256009091840030b8500aa540a08200c80c000054900e0b50210400301815028408005440c02e0104404080103100106805d41d1920754645030300040c6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 901048030 1250 901046780 901046807
    0x8163501060f08032b0b0907080a051807090c0e0303040b03090d0504050915030c0d034803090f030c2105101509060b0a140c0a030309021c031701050d02031f0e0303040c06 75
    0x1102c05200d334508100008170401a40d000702c400150009840000341c0b10004600e11103505030002180001d07280b03400a014520441120f4242c583c04c220100302207450303100d1409030a038820544004079401505029544000c08030141c2250305002c2c4030130000d000c1c0201060201c0009401c09010310ba000c1c0100380d40019090404810507800143e800c0e0031124815070100340c22988060600f800c1413610400e00300340204002e9445056481d201e0900700034a05503406001c0080c4022440d18088038003680c00301c1e070309540040c060040e402d08030482401812406031020800c2c0c040f10004034045c0040c4c810007000f446080c56085e0b680001080140016650f41000000c00e6401d02200801000100300b00d042c8a41c1403800141441f824400100308450900d031403810640d8104100d810150441e10850000005c090f4681313442c3c0c0e076401002096900c40360003d405412a5404001c40b4907100755a5038151b01203000402c5148541e04810b2a41c0c10480e0309440385c012480301000a10741006100c030401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 901049280 1250 901048030 901048051
    0x50a0912110328110307230915010e041a03070905090d0f0206040b0a02041d090c04020f0a0c080f1603080108163501060f08032b0b0907080a05 63
    0x2d640c542140e90048001d001c004c0c0ca03040788140c11180f9968144a04405030421746581600040f452104141d16842c018603107029210003000300302401d18101420000703000c165541e400382090441400080d144050708448000a9080d2020740c0340e60500c8140060124900002010700c0c000e040d0320300e450050010082030001e51880440f945602107100e41d40300b03801c002038161603102c500c40c1c40e000348504c0e0301c032a0f03003140782080c01d41700d2500f0200da281c0075910420440b196131a040c020070040384224440712405110170000418000e00a405d5101c5450003070003000e081c051040940003942d80007040d09220a0980e0303112030109500004050b0140000300000c2482d134a80100c0404051594012400c03801e00f900d03042c0a00340f50150364254013401c900780c12a0b6604841e50024082d0401d40100300811458031030100c0c01220000903174014489030200c1051182e10000c81e04d58000c005041881040d48900381c00e43c8035103d42d1080c0340143e10325954980d641c078060842d00100e900c0644000e00c0c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 901050530 1250 901049280 901049323
    0x1c0204350606060a050f161218050d03170403050301030c0b0423210d2705010c140105040b04060b03030a08150406030f080307030606080c0a050a09121103 68
    0x100e820000382968401d01c2a140700341e654080040035140c2d405034100850802d03200050b98020000342c2c44400b514144a88422048000d01c194180c0741707a032420180f569852a086000c104903c1c0c41281101c6c0035010b820301d01001c040e05c0100f400200412203041d03000c10800001001048840071101c802007401c0c0721032508050030711001c0704c41c44c2c41040d0240011343c2000e04400070707070391801c00302884040880394000c0c4016030100d07095110034541c591603011070014004041d08600c02c0410901500164804850341d908260042d100d008440900780d0307000e1040d44100000310070905c02e0501940c003c0130681240d20b00351401405640515522502940060281b10240b9821080c1c0940100071000446d0102a841300802d006140c0b03030b4005413900d408070103513105004e50440114025032080c0c0c0c05000003074076020165240007082e6942880c5510030403001042d6881007018041c51415460f010302c6190752101b00d8684038441c5c00081c0d4a1103210342e0b0720010761500b00801e80f02411501121400d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 901051780 1250 901050530 901050629
    0x10b0907051e0304151b020105060109030c150314100f0510080a051b0a110f010504021f021204030302030d0c0311070204091a09030d0e03040f0b1c0204 67
    0x184901d01c2e011680c0d120740d020001c503040000d129a24004400711034810894003038403046003040c002500c400360002d54031300340101307140e075204000c52026a500300070501d403803a00d003140558545454548240800d65a50b800721840502d036030b0b0403405085102d5065640703601707003d070070030307500005611142c80380300032222103035009422070080c40e0320111030300c2c00041c40e564081180003440c41282081a6102000411544060300300500394840320f10348d02119800f90440700300342e080701c009582c041c2d482084100061090400c8081c0c0c130303140e4144d0344180c903034010381901829510b401942007140076030804542d04240e14614424100740901502d000e02c0102c07240380d013180340c0c1c3c0308030305001e40900c1e200c103401800e01000d224407800b8008002d07194102403070048030305900c0380c204101c0e44442030b081c00342c14001d0503400011345090f038510000010b0901e1920b0b40003241584084004010108005114241d14040e48003600060940801181c1003a695000d2800031500380c1e00040b8154051522490 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 901053030 1250 901051780 901051807
    0xa0f1b290307120203041103010c180503030a0c15150e06010f02060f070e030c18010e010b0301050f0d060e0d030e0706080c090f010c0f0f171c051302060408010b090705 74
    0x40c5003400f103040059683d00c0b00d040160501c0c26103103419805600340558501002d42c09220400c070344044800c814580c80e02d4004158513845000c40240019070696550b0340031070115100d081440c04c2c1c10200190b00c5200544c88043e5030710030792240c010b500090080180310758000c40d83d031010440c144050502494144a80080507001400980821001102e1002a91810454850007801c01807850503a0041000b0300c5000342e41c00d000351031400040100001c1c0c000400300179a8180c1c0d40040090a5082485c000c1c403600304c009600c1030742e5964031400f08090018090110454001c050740d000b148110a2144036803078050f42d54000030411080504204e100250038094580101d002ca0b1020703420201e50004862184d403030309000d401459003510400410140f49440d01129101301405448452013030644601802072401012020058901c4c540c0042d580d903010541c0104529501d01181c02a6004901c040c6c005812210030b9030355a000421035460500031650303000f0308502d00940b82c00e03c07030b00015 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 901054280 1250 901053030 901053047
    0x4050702030a14030c070b01240504080a0b06041d06040308060a08060c07050c0613082e0b040f0c02030903150610180302060f0703030f020c0a0f1b290307 68
    0x8841030500400445c145c0c10f8a541201c50f030b03d802c03980d01c01065864414500101100d04003501541d150b8010990406000d0420f0f1012a5000741c007901c0c410050f07071182c110407600104002d50180e45d85210081c1c0f20180c28140000d0300003180185100c0c501450043c00380000175049620401c055442003001910000700140e0100301a00e030f01c2d4880c0728030320303100d484c4c007080b8039409910403004916510501c3d5030f480400211440c0c0c00469030010003803402500c0d511503102c982d512032040b5912280c00c01165800058144502400001d03441150403640070866031810112030050f000041c03c07141d145010400d41d0080c10880c446120141040300000d200d007040d138880c1c081070000200c9494003c1d4040350040005540140a443e1b80340c031110040e0700300b270748003071021408240342120781e40b01c22a451080c0c03244000103d0040450100c0740c0c07641c02d418034402008490042040e01d040002c44d611101100090000d140102d00f04121802750303507210300040e084041014018010800b10640c405005c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 901055530 1250 901054280 901054307
    0x60703030209040b0a060c150506010807030e250515040b120a0e150103031b020a1a1e0901300b06091207061107080312100306060b070204050702030a 66
    0x10303590b5156070702040140030800007041d0f01c041281000628507812117603134a82c26102e03401c0c0d880c01180d0030400000f119400d0300c041e40003c40440010b40134070b0090740003da19404507811651800d008161412035410000700352403030441da02d1010001410507040703640c0701e1000102800d0800d400c0030780809a50103400e842c0b441c01451100800c018401c59403094500a0242055480415000f0f4a6900d501c07030a00c0104c0020380c6200480801f034902601d00071600c0d40c01803034400d20310315008600400b10031151251503082e108100680541d50f00090100c46000440400d0f5192000d0200141c98540c03580481c010a90001c6440403d402c17a0784c1c0e54032120724130f0718000108240c060022526601422141940140600d09096004140082c0d202c003210b43e02d0361100d04407088016000e4958010b442441d115070b005200140480d03521039500e9038445c09a80e0540d01160303a0751954025601280e100130340305100020701c0c006508203409101d900089a0005501c4d026523032070b005141c0d2255810 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 901056780 1250 901055530 901055537
    0x405060f0d020a03080a051306020a0b0c0a05040b070507050f030a08030a0207060e0a050705041b0c081e040f080d0c0b1503010b271b03072607020d0905040b060703 72
    0x1000030440d076030083c0c030001440d007111446072034560f0780402070f200781d014140d1007000da1190540011498400900541c0e00c507401641700fa2a9150205c45082680100007100180142800045050001c40000d030034801e000344010b1080d1880c2000f402420715112841a000e500220401000300303010204903500a81c1c034804c0103a451600e8108080100145100c26109000325481101032080026207141a04e1080790100041c46007401100c0160050341d0720310307000c200501c041d0004510f640c0003421081541010700710020303200c094901020781c400c0c0c03c040c2041403c041c0c1401170541c00c02c20114407450301c1c189099140b54a4880b24984900142141c3d040e01400c605c3e240c43d600d0a40010400c4140a4206002e0f4440c400b00c4048003010141051004040344c1e0000354510040e19598003405140001a495a11496011034030a040d201049031383c0000b0a48602420a02c41ca01c244a400c40741c1c00b603c3c2c090140711008003100c0c41640064880c078141846a5620f65400084490341c650505 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 901058030 1250 901056780 901056799
    0x509100f0f0f1b0303050603010e0c0f04020c15010303050408011505011d0d140304051201050f060d05240105040b0f0102191b0311011206060206010302131b031a0405060f 75
    0x20040b95080c15203d10144146110407001c030130160550080c1c2e0150004400911040d010901d5169840c0310030726a03544d21940c00750b00c1c00d4a40c28907074000c09807a9180d60070f56500518210000101500a9104400003100010100410321081c8030b41186076402040c0c810459260100080120240e00500142040c0001a1000e6503030f40020703607580c0591180480d070b56034160b0405561250410b205581c01181c080300c00000c4200107116061081000c035050350250348500c410300102d12000381c0101c4142c41613419500c0740040d1510440301000da0020700840e50343c1000d05000c00d681d139041e03000d8001d1006890f0741e0a80d0381c01051030010b1280500b0825550081070a000c00d200b900040d1801c17190720301340004014080000d01100c40c446081c1c03901e01110400e80003040c11241e1510410006800a90051005250844000c402c6001c3c41001150340c9400748e0324000000300d011408008640d5444070900303110510b10584484100460f402c104c0c6180c03500100e01c8118200010740e02c40d10024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 901059280 1250 901058030 901058057
    0x907170604031409090103050d0311093f0a0309051212030a0b0a0e0108070509090c0f0414070305060a050337080301030303020918071d0a080d0509100f0f 68
    0x1404e0782c03901c4400a11400c00355960f404d0081c4c94004070001000000d003005280580d82000ca801c0701ca2405000d40100f03907400c007144603120002c1d40700d001503080d40036002c000c00300021080c0200d00208d40e690040c4c14102428507000d0614421076102c24001c005e038070703414010142d000c9001d04030b0101903050580d40342e4400c04584001c110b41072101c0d5008110900210303c004a030244141039911007800c0700c43d0180c8407000c111140e001141d81203525404400100c04504140740201d41030075010348046260558001c140e210503804540050019540d2410001103240a0040000408081d0081c2056000b07091349030072501101c84a0341b08091130320322190035840c00811151813549d08950040d440b0350716841c0044c0a0352000030458440e0741a861240404074465180340d00880c17035929500803c0110201c1c1c00c580c4520707020026401405002c0004e4880001d000e8205c1d802126511159500c01400400866500a007034603000c02c69040c07142c030303122a004440ea007101c0885050441101d05003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 901060530 1250 901059280 901059317
    0x2031518030409050f0c04080a17040512010b100f0905041104030204051602010e0c0603040b130803280213050d24020d0b0906090a180f030503090717060403 69
    0x2600c21201007032000140000d02d10316258442801246440c02c0c5a840f0389540d0008191070043d401111050381110040d100020072030440302150380c00d101c03400d500742540e82001420020502c2d08000c8140d4458030320b2100b41c5001b40000381f40400310308190f0b04034050031400900e00405801401c1c0110b944100802c1111031880559000356401481071040d442d081290110003090090140055828006070b03105200003c1481110f1040245c089411940c6035124142c0214025182480200324070303c881b000308460701c1c015407042d1890280c4009036452440c2c00e901c032040d68000c4841052050240307c2498015443d04c070108e80c0200c981c13001c8000b050a000c90440c0c034064022202600913907005029500d15009000180d05070102008030204150074007020b0074089621640c440180ca0018480081962281c41c8040e4071032841841150a075845030f91300200d08070700340c0c00300f0700c00b004000c4220400c01104024182c401010340342409030300082582e40304040c20080034440180c3c6d080300b100703c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 901061780 1250 901060530 901060561
    0xf0e1b0910141303050712080f09120d05180a0803070201230a02061504230c070b0c031008150a1d0109030e03071d040f02030a050703080409050a0504020315 69
    0x501c0c1803450756403e104020700303c2d81156488200c17628000c0043c00a0f2080202c0f02d90ba1119401c06640d601d0b101828905514503170141881c540d000208407030315544407904105552000156482e010303500c00c1c420700401410440e10489074400c000164040c400c0702d078007100740e0b000590b0a0905c0d086001c1107500700f91000d0886808550b8025011401619403540042c240d03014280e003203c209001c049040074823054488440c00da040510480040108510264005643c02081d0400340303404c004065984908140040e82c1880308010084140001744800090f144014040c2200814001201100c0e40344154030080214480f503580741c0300c3e008420b942281c42e010307441210340200400740542c039020301030402081200c0d000b8802c18001181c2034030360154a050485241c44070001c40d50b2180e40f4143c00e5108050102d07098094040814001801041a0806540b042010986690905580108a84004100c0000c2900701002d02000da10041400c002c0c100c80000708689031750700d0310b506441409 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 901063030 1250 901061780 901061807
    0x2011e020c120106031a04020906120304170c04050a060f0b090f0a0905070806011b08090d060216030e0103021905072105070501050f040c06080702010b0405010f0e1b0910 75
    0x28900740802c6006511160075a4814000e0018006103d80c68451320030701102d0094200c0321240104500f4075001000c08043c011900031240b0f820348510402c4006801440d40c0810383d4011401c254440c6490b01030300f45d00622000c1c040006500c0c04240d0a80d81341c89200740c046d118000035604400d80c403540e001000c440c00240800d03c41030394440103500180341c1242d0001c00100c141d40030415a44c0b0407400355a1130402c20700c003002001a9070703c5106941d44041a17595003c40c42c2e2240c07800184c42400170702480030759940d0000c0714030038504010b08050800b80c2d10710f040510402c040c203c048081400c1483d09010752820546481951418006840341000341030500c1012040d0303104131079800720040c003406110303074002d0003e40c4503400341144000b81a20010326078a80380009101d1203205501c216403151b260b100101d84803503407a01080844400fa00318a03d08003140e8018001035000b02c20054001ca040e101014040800141c00d4405020b644032081c840e046540076142024480c180625510 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 901064280 1250 901063030 901063039
    0x903210714070b0703080702010f2a0e040c1808030403080f0906210106030f14010506030405100e0607142701030207080d050f0f09030d2c071e0302011e020c 69
    0x70704d020b08015000050894801006600f02030700c414070742c03c00780198503038060035600100c1802c50500f40e00b0700d800780c282d0640d810040141d00800c100e40c1c4501440015400f6a100e045414949840c010303e030541c5034008410940c0b041008100183c801412a402040d036485141d881c2c0c10248000b9501c1c1c810031560584105812440200700d904400541c3e04985040c1c40410111402e40300d594290b50418070111005044640108281e080000081d58071610070026949400703040ca07490300845015034680b0783c1c80e60001c0200079003d07030000e4020440c1c04142d20002c0c03c184c03001012000c04050801c9c0803070f910b80200c00055007030340030340c05480c2c4495001d00b03c90b031161070502820303004050860700502071404140105040068401c0c40b14041e0803441c004e1450014910010006000c0c80c51100c038840e644030003032502d1068031040d8139082c074040c03201501c81c02c0c0c0b81c0310b004268441701c00040b0381c2c190708010342000180e0304441c000001c030001d0f407140e400b1140003032030a9060001c0300700030342d800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 901065530 1250 901064280 901064287
    0x6010e130f06060602240406090c15030e0d091511101103220c0306052220030c030a0b09070b0a0504080622060923030903210714070b 59
    0x304402c6400440a131030843d4200e40399201542c0700c55800b9540f50700030801700f0030800040307004170f4000d0b0000400f16020b0520310301110341c0e0f12009813a1501282c400c44c002075969a2074444440d05109202d1148000d2074006000c1d41040c4080c00c00b201100c09040a1110221810300d54a00a11145100104440e000c00c52103020900348480c6500c12101204001c900042101040107401d112002183e04050b1040446056a940302c00908002d850340e001c0980420413180c141084800c0c0c086424800e01808000c1c040451000b5403030034118282e1803094000c0318412505032800110680669000318900c4503c0e107a40615074108910b503000310280040009180303d0f003642110040045414400071104940c1d82c405010003420240744100400e8040044000c020441d0741c1c10503501709000b00e14903045462410040200f6440c4410102d010b0380022070502c0741403405010f2070072a100c0c40c05110000c405442c403101c40354441d8540081181c800c281d0700110110081100b030025003410f107416030380c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 901066780 1250 901065530 901065533
    0xa090e0c10032315130e030a030c0806120c01050d02070605011d0a150b0c031306090f0608130201030c170109060312030b0a090c050d05010f06110f06010e130f 70
    0xe4a00841803000e59901000040d0b02c1103e00322100d841001d12454140d103494240703040007081041c140401850303a44a4000c43d182d42401d00050408d010a0344000401e2500d5102c0540358050043c00e17607209000c00c82003825510b00c08191a800f006003440c00a587d5001c0360002c000a0056240140c525841d1000200700105110280101000d0f180c1d2440312a81d0313020301c03220a46a4540c814110204000010014482d40c0005041e41c00061400d41c1d0400707544080b07641301c2c211107503c440000303078281c4400c01003003a442c0000c8001d40613501c1d20010901c1c4c000403208124802820080c1007603580c9680f0000c05101e0034480520300300100740520b895030f441e600c0c14058800703800b00382e421084d00c2c1d0611011a00034810202e0440003e4062411309151505140042051007040300600000b0000340214031128403445020b0183c100e92004203d00b4403200820103880c2603504065a03122007140050028001107642c11150000300e050780554032180e2690141c1030380c01004000d181082c0e00b080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 901068030 1250 901066780 901066787
    0x306050c07052b0e01030f0203100f0b0a050f21040602030609061c02040c122d020322060603140307140304120308150d0c03030305070302090a090e0c10 67
    0x28414050001c80300c0034422501441c490480c0b040300070f051420084800000300f405a0381e0350310710000504000030800a42c043c0c51080e64012214600c9040c0e4200041c007480018040500290040543c1581020360994018081d44211180c4002b00c21021800075400c488031104003140c415502541201801c2078a0000c0194000307440141c40382801034006942818884002000c002a100301400c2c0d80900f41c09004c020514815024100848407130010042d45590285841c00c1e034400300490380341140000b012911445805409010740c0c010410301c00e054202e280c44804640030400c0000701845c4a03e4000010b0140354401070003032002d060321100044012020b0f04a190140c0a405014419484a40e4070303803144e4000e00f4a80d51003a0144800310748100c6e1443d601004507071032560f405030716100244403808512030484440185c481d003802003503414080c445d005802400d0540c00d00b043d40c3c0006072031284500811011940d00c03140e50848080c10410980c00d83c0700503201d403002c0c80690000a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 901069280 1250 901068030 901068037
    0x70c0803070b15090f011403010e1209090c132304150810090b0a020a09030b01090c11030703200a0b090304170a0c0324060605130603181b0306050c 65
    0x24070120b80200340e0342d034560804c0c01c0010700c55094122000e030700d0b81c24203030045810282e42102540542d640c1c140710501070f004103c098824080c800c0d000c0d03150b0841d9000c10252207001072005400c07010901c801d502c90300b8042c01e500e050381d02e030207504012524840002c4454800162142c0c0e80142818240c1c503c80130801c0010003a1450642502c0b60030240d4060380c0292692070400904041e01d800018a03844e4160b4050310a040c42490200b018a80d0b80c3c0354078035518001c0c1c101e043e081ba5a800c03042c207600d4020341e00c2b140036020a0090350410100b602d000e8140003403c508000750b010144d50107002075005014440d04d040d0f210782e4100d00350401080341540ca40103070041411210701c905c3c6101c043d5600040c10380f074031035005500185036030640d65101c5861210080e1041d04946140360050b03a40914046c00e00a000f0301e41d42c4589a81e4554404c03240c1e00da1030360044061624201c442e001d0303085070004000c101508689803403001011140c1841d003075040d90340080c0c100c034608818407600701c254070000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 901070530 1250 901069280 901069291
    0x5040e0a0f0b1b0f03071209030c0201030e07090623100807080a06080a050f190c03020f06120711060f0c031501110d110105011e060e03030d090b0712020a14070c0803070b 75
    0x18040e01c7c2c01460403d8007150174055001e804550715288101c015886500600d035010807200988428070303921080783c01030b60b006405c05030500102440301c654500d811080d0620b070000443c0c01407880c00807480040d01110010380501c0401900d28000380844086070020001001e86004a80c20341c01e40b420b00903201c02c1d00f00c0c14501280506400740d1400100a1040d100d600c1d00041d22400140c555401c01c615181c502c8080d9810803800c3c007130380b2806008804068403c1c13809884a2645c80d4400d5109800c11000803c1010a004800180b020401181054a9100c982116907102240440006958840d00c0d03100c244a0351041c60f0026400c1036000079070704c2050386401d00130301c840d90b21020603900c1c0c1443c00e00d0004110794a0300c0c04000040c0b1078030307120007031010240c1540e04c1c02c045030301c043c1c1c1500c581c072405680403516102480350041d03005410152003004039201b141800c080540041c040700e105850b05d0402140420401c0c2413101d040c0500c0010803000d01203d07901e41c6a840e0410100c0c604652 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 901071780 1250 901070530 901070537
    0x204230102060108122a01091a010b0403031e0905060301170708030903030708031b031303120b01020303130218070216080109030f0804030512070905040e0a0f0b1b0f0307 75
    0x80546001541c0074178114189007090425070221410707000c40c04007500d00b201420311000d40e10f4801000b8401d144110b40259402e0003c40307419002c100c0b5a903410380c0300c203035500020041080440c0e802006002c65010440f50000060b1509100f155064229040140c1c0044000000900c145544103c0d070762080009080c0ca0065079200c174080d840e4010401c001e41c141d0810865140010801d00003542e0080a4085002680544081025803504111a864031700703003d40300c840040c1500944000c0701040c039020305100384150803000070740301d01026040210510703044010108550b0344c200380b445c4104050440300494030b00804025620b007200414400c00106100340070035148018061610510b405842c0c0711080c1090034021226040e00500542c00c01405018003603000083c10003050040502daa610450181004200012100d2040c120443caa0044001c4d9000079800c0345400e16003078100740b050100381d035021401c3c920f414111004485010700046e83c0300000c00d0f20703400796000f03102d5a41c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 901073030 1250 901071780 901071793
    0xa0504081e09100c2a0b0d0c0e090411041a031006060915140a14070b0901050c070b06042307020105010e0f040317190c021e03070206120a0204230102 66
    0x207405480b9548804000b81c0004061007082c684000c501051405c40703c2c40442c840c4481da9140c0f500c20b5036070484003c0351501da40f18109841003d50290007540d140c40c00716020001030030180c0d54154500700c440700d102c2c000c43c1c603100f242000c0001c488660707001da6800707030035210724a11580f050b80003000035000d5540440c04400000c1241c04810400340d210b41030b140c40d05c1c04500f00b48031540326550003c122840c1001052005003008981e08400b40000314403440801c055070070084d1041d42501c0000b0301e407444440342400030402056005440c40d80044c4150384c0041da68600f002c581824446402d07100c14085070381c100348086554150310035070491b407078813034501d405844124150300340342d000b03440240c0011691421042d12440c40803940e50070100384803a94001c0039507294104140c0301483c1402c2e0160700902c4c00200481e02910700c1c246210019000341d803800c0d40c0e0342c0c0007a0f000d024001c0360806491020001070002c042650484000d0607240c1413900440041004180b5003184d01d0343c510f070041c090078 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 901074280 1250 901073030 901073059
    0x70506070311070b09010902060d050a0c050c030d0e03040302060c0708100921020a05061023030703031d030a2907090605070303110c0c01140a0203030a0504081e09 72
    0x240328840b2050302c0030400a10f0220240c50780e40000801410100565613511392030001a40d4505c014082d0b015409000305a41c500b580000c1c003141c4400c1d2851062040801c003080c03011101000310381385840315490004030032904203100340c81e500450300000e4001e0000110050004400154041100c105408540c091550801034005454415000500e8111506180406503510260311040800c9900c116140b0542644a2910300141078035025205203044206010106100440d40c103c64581c140031054072040c0d0000c0383e030b10f05940c8800760070441c0100154040d41041ca00e04801030074010100c5100c100e440c05e04118841520b09c6c00d075002c2100b02210b405c0c1452070481244500781c1e41d15810710540c601041580c003a40032200071070816a41d001c2106482e1403810240c8503089065005180c0d03450404009088600c0f81101d1140c050028003640b01881d03400001c0301e42c03140e4401804501c41d00e661820300650f00900051320150040100d0158480540c60b0107824446d004030740710b07080750002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 901075530 1250 901074280 901074287
    0x312070905060912011404060510050f06120907030f0303020409060603150501080a0902060c060714030108030a0f1403090604060b0d080d0903052a011a0906010c050106050d0807050607 81
    0x55201d4540c00100611681c4050f1901858200d8442242c6002241d0452008411a5410011a01211038035607c4062158424503a455240035010540301e4160080710200080c4483c0035810074a80d1141101001615807002808100000e40e44400b000c50400c81e1443c01070082d40240c052201c400c0c1c50410300140c043c0c807900814030315003a81c841c2e1940c1181850011030307510740014103188004d0303200d0401c0001610380340000d201c2c0b1040c1901614041c244810020b00328014000c014118007814001030050101c0030040303c1901810741400750401c02d00f920242c3e01046900a21001480003200f0010782880c0817803c184154440e220401c84140404108600d90200e16009407814006100940110f0074a03400040c40d207000e41009803c0c0380300c200446558059198403684059501200b00d11140d40074020046034044040c401c00c001801c00010070a184002014541044008000700043c080300394004809407030060f286c41010038441c2401d80850b40010f004030340a01c6000d0008800750b10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 901076780 1250 901075530 901075547
    0xf06030c0f1b02152505060a05041a07120903030509121c24030f0b090a02090705070309080d03062c0408250b070e0111030904020d021902031207 64
    0x401402c82100b4100d03d4003480301201c041082c00319106010040c405a00d1060800c001d0005642441340610120914006041240240282301382d982407509010000d8417480c14903034410218882c178040ca9441c58011100742c007010f1841200c2e6490a401c0d0000c1c184d264000c80c4c031030720f5950100c070580e0158151b500903601c21203003400804180703039142c25040440c0360002c80c400c5116481031658942e00080960344141c0e143d0042301e801090341c00321010055461601c0d940004440040c00c8aa6100d4020801080008040c0c60811500080c1101018081c0180c0e0000c0d0101a045030980120140044d00038809401100321104420b90000e001c010307030003116910790f0304004142c41140c40c1d0b541e400c0304070b0b00562060400212101140c0c0700000401c10400c1205000c0c1c4152445420300002c040e18000200c07203d40c0c10418001d0300d0340b030045d8000040341d248980540b00181d9608200703401c50002c1c01030001030380310013440690140440d03900001811600740700d012849010b03141c4c0c3c00203848034031 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 901078030 1250 901076780 901076807
    0x2904031e090f1502070504180519020303030f07120e0717031c0e0a060f15090c0c1101110a050a05010c1110090305070516080c0102070501020a1203060f06030c0f 71
    0x100108003d1100981d05250620301c80036900440e0081500d50f000501610040341d12102c01e414042200030a0107800c100382e14079803002c0580b401c0c1408694010a460b448000d24402c0d0458800c0003180416100d0a0361014203c13072031000308078622600149540340d4080384160705250051243c60075540501200721180740c038810302d1b1901800d90401008002d01095251801c090081851580100303009000c2d2100107503148500288141c070001c04078803000c1150b0081101d542c42c280b502d180da9031b08188581c1c41143c011642d07aa4031590480100ca181911600c00503040c0503000e40e101c100400003c840340114070460003030000000380c0c0d40840c0e60803549a02c5040c00c0c0d100d0240d803110328000d41d0103030400314000d2400034035004840c0c9546203000f204454130b40d8601c0d640c8808026856082c050300c5181e107001d00c058111030b403400f00001d41d25035105034082c1c07103d0048680031451501030b500080c000d10440000c040500e94400016000f070000c0204d800119441450801015104004080c2c503034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 901079136 1106 901078030 901078049
    0x5060301031104050c0c0d080a1b0302090f010201090c060c0c1508041a0c0a1202070203060106180e0c030c03100f0902090a0e01122904031e09 63
    0x41c1c0c0000c0000c201c40d40705020f4407031b00540200d80160340c41d9403850880c4207500e48050000081c84031130121100803800c030308180255905500a010f108400b22140120400108016420f9032403461000307150940086090120501072504250743e64000e0131b8060190307850717000c242c40c010325041117030300490b455404003c204030040c501400e04c0035504520740d116041404030742c042c40c02541610000e01100510740008842543c3c1036520260700101114010350b5210381c09068000c0c0004400c00841801e400810000189480540540895080d0314550340d21080e50403400c0d000902444140d400807040002c03944150203c1d00d0142c0742e60b4000503a108555030400c007000b0b80c607610050400d00980700401490760b07200700610015401900d95000d1020401c040006c0711641c412010f95a02510140400d255201d0003480300084404c2410100082001c0165490305c0b80d4450084c80c1c = true := by decide +kernel

theorem cover : BRFrame.Cov 900899280 901079136 := by
  have h0 := BRFrame.cov_init 900899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 900899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 900899280 ≤ n) (h2 : n < 901079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
