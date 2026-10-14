-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3450
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:42:10.102084+00:00
-- url     : https://prove2.me/submissions/6392f0aa-e58f-4c97-81bb-58b7729a51fe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 620323741 ≤ n < 620503597 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 620324991 1250 620323741 620323751
    0x204050924030a0c05010f0503040b1b041203080a05130c1403030d0608010e0d020a2012031206010801080a031e1b030210110c0309010c020f03070306020903010f140406 74
    0x700786010780c00c0108601030345849580c40e40310511600d4484002110b10988890001114622055500d070104840103440110b080000620380c1c662044941692642d00d0001480c1a841e075486519101d41c01000345d0000f00003504114440615101c1c00b60031400d2402a085049040d5580c900c4a6206000c1c8041c068182e440404990301c040042d201d1099065005003e800d80350560300c0d0003818110803034281d41c0302c1e1508050b01c1c5030003c0b41020000e504500064102d000104c03030762202c000c90328001d5410840f03010b14140400014006004625180441250314ac1400c0c00014424801030b0001602600041000340020750402817800d02008080c403030810f2100400808d45440000d001e10540d0208003054200c101903001c41c1700345405d47e91103400c114051041c0c8080d8218020541c0b51500c0ea44100144041580151034000c0c813140300901c52911140703494003003800c0c903207281d1045600f19008100394546160030f0140c95038078031007134404002c500910080103184600103040680030694138 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 620326241 1250 620324991 620325031
    0x3070e041a0d1b0915090b030d081f0b0a020706030e0d120b040504051e010b0a141207180e03161e0b07052706091203040906090c0207080102040509 65
    0x840f42001c2c2e1040c88110724180d40340c4c0c8a088901402d010b80070314040039100500410070180a1217802d1450f48058020b183e0301c1c503518030550340c6060181c00540d0100710800700050454400c508900948081d00c0c889448014010000c1d15294017a0008414141818000005140c0018a0010103491494412008400340032000c000b4400c116160342c015050904110030311500141e01c0c10320024036100780f09a03682040c220ae08031005007800e41e90040603d0010010201381080b02c0d070507540002d0a40b42d03101600900d003890003d4039400040c0c4451400b012100c0607801d03110321441802504061031411090000010110001000c020607820408010148100070144015040d0350700c201c0104403410469005001504a40e07041101111108070f054500c140c2c030703c0c0c6039603500d102800351400c08000c40108410b036050b800310340f10144414130000031143c2090103007000030040000300103002c8901510007420000142c00900e95603004100c01c1000da103070b1030b1a440d403040e01d240180000c40c4c04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 620327491 1250 620326241 620326253
    0xb010216180213180e1014130203030904050103050d020c1e060c0f0d05180d0506010e0a090b04150c080c0901140f0711210a020d03090509010b03070e041a0d 69
    0x1aa0013101555510480341900b0b00c2c0381c0d9104820007040c00046401c81c11101c017504050342d840120300d5141244510115280d0114446103006281c402001d40381007a440c1c5e00480c1c21904268130a54140d849100380d01161601030100103290102980c83c4405802142940d2030819090140d10b40102800141b491644100344040b1440840040070364103444410b80d801095900558000c0f44c01c121644964243da01e0700c98200c8011541c000043c119a80ca4081c031344400320300041039040b0f0141c0f16211000002ca07140c41a038400c0d445440f94100d082c2400842c8822180307011402c0003400002e009103c02549988161182d008003480c1225130381c4500003207010380f4010024503050401021075118100203107440c40d11500f10703042ea005100180124407500d2075800c000700b0410345421650480d800343c100280300040c418041d040ca041c07440e6803103020420006c1c0980c414140f080010090000c0258886103510340900300300c030280080035143e4024014184110007042c401c848100d01d40040243d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 620328741 1250 620327491 620327527
    0x61505210c07050604080d060504290103020412031d0301090201140c0a080a031a0402040b0d0203180303010e0406050f040c33030e0105010801050c0f07030e03100b0102161802 77
    0x40c3c4102543c40905140c81c005550782c00100d20348080c2810b008010900f8100307032081380d40c0b5620910010102d040405107510f041514034403a10f040540801c0041041c184003100900e1141c460303a580700c02d601440e1030120205644902c8144640d0610fa40c420150380e12440c026201d6002d50b001a55403070fa0403b40901d001c0b0b8180c4020304c61440403caa446407038141d4000181454000c801c4018071300d8100c100012032059000d0381d06111002c0c003550000340300c02c1e800346500a00781c40c14041500500740c102841c41c0c000741d1000301001042c208104c02c010540c0600b64101d031070311403045080d040c581d0b9613540c0303001c45004e6403403440c4400007040300000e0700800c80301141a410000c4440c454480303030b0040180110448141180d820200005414081441a0ba2154211403205800d14560380f8134420f0540c810b100a07010003550303031184503440e641803103666000e042160700041c00c80810000603042907011701100403400810750b404c0201a25600c1741c10616010384c4001a9a404140340010002c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 620329991 1250 620328741 620328743
    0x51c170d15030f021009081902040e0114061206090c01110102070c031412040e1305101103100510023d0204030303060816140a030b0406061505210c07 66
    0x4080407000014080120741030106a8025178039841c20441d8864140c0d40e4038183d1103100c0056001c1c05502c1e15800525810400b907900c01800030464000e80e20045003900c4258510215000d0000c081c0100b81c54010074042c006a400f02c058900303454440d80d460b480700301d0f50304507505101920003c980010801c0d03044800d0380764001591071041c2d403681050f104035038407907212008901c1206205c03819840e0324400d44084901e5840740149594641282d0355004c0c0910b42c04840d1407180340264000074046004400e11f09805081c10742c0c5074540314003401140070301588410b00540c2021400013040d0ba012440001da031000658881f20404006907120030620011098800d40d44c5245140a0003220387d001002224001e640611806844104440e1650000c10407213600c2c1c0703100c00302081071805060541d004031400801150507141d80c0c0d20707808059030044404a80040e5a128180003120301007089410342c030b50901d0524142004000f2480380720440c1c02021102c000b0b10000a050b000a041c01c8070001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 620331241 1250 620329991 620330021
    0x51003021002010504060e15041403040312021f05010b180a0506071406011d0f0a1514090703050118050414250b03100b0306010e0316051c170d 63
    0x407201c2514024000d0106480484016081013030760101903000260090900d1055211904280c07515990b6101c0142001e000a2860006100c00008603101c0da0585401c038080380c02511001100c9511a80c0b881c62800b8011826482c200047c0090302180b401c0d1111105a2001c8071000740307120740000d068039440d500543d440035000400100b0416504081220f5200701c0b000c480fa5640c171080003c0b00031206496940318a18003100003840d03900d810004076044004003071f002800b2074014141030441e047c55006a01702c0c100c901c0741d01c0e440e802e00d0304400d40e100c0344c18a8100174a5040c040003800e0304d140c401c0b82c0d02d202502c039000300301070080200e04402070040d0f160490b1090042d651800c41d0004d41190064002c611180e0002071001c205c07021284039941017a0b01250450030000c00342403940014050604011405036200c0c8551000c0025001202c00003050a407154902000c10503074a10303540d2a03010720058140031b01c0000f02a2003003201e2032412a2466501c80c007000b0040c80060018004d0490300b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 620332491 1250 620331241 620331259
    0x1002010b03030c01020405040605030c0919021e0405090703060b0307031a09040c050a1a090d0519081905070c03170f0f09011103091f12230615090405100302 69
    0x10030f0055004004a400640c7c092007010341c1ca170200343e10380d09400c5145402116400c009040c0055604840e4100440300302c0060a241040e101c01e4040f100314005d03032480441c00074003880a0f103001010103910400524040c0100390034211a260b090001800706403e00d034444900b4071010000040901c0103d00203408000725251508044d01da0310014401c0c28041e481107032000c1a201e642c844240007040f100007551f85040d03c0f42041c01a1040030074400d030340c940299800803240488043d41c2d660079a000742402520740b5a410000680b440110001206000c42005540d0000c0c6c100003141c03040703c0d041601428142c180d508081c50601c5101000889003030006032014264894901030508001c0a9036000440a10442180d170340e0b209002220394009074980140d4400c3c1d4020566990009807442c1105402c0310403062a02501c0d13401a90502c02c80005480d41000540354002aa014408031014070308440311030340b10380d1075118000c84036000e0b0b61140c00140847d1a0f4203060002150302404e82d4131707 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 620333741 1250 620332491 620332507
    0x210207080f0c040c0f050a1809050a05073002070303020c0f0304031109070e0d05030432010f05070b0a1116060f0b0303040506071a0f010e070207141002010b0303 71
    0x246407001c01e0403091040c0d107040442d0030b0062050017414071a07417880d20b45520308150034405455201c1190113070780072000e02180210702030440e0b0041d103020b410f00d1900481e00e420b01142c00f0304500708014a01030a0902050b8000341d09144807030184a49884c6000140c1c1e42c2406e04084010f40304201e650038152240e48008a0002c40000040081764028203039520f221905074100900d02034241c800348001110000c18a2252400740902004d01d80300790100c0f480c041da1071a070007412800c280c4003031982074140314100038107488031300040b40c40150900c2c00040215000101074013034020b2007005000da59003100001e03035072070383c13640240080c01c0242205620740b640f01d00000802c040c0c0341801c8500310f08101607e500d01e0380a006030701c54a076009014504040c1008203000140c0c010030800e44500610038004d140e80405c03118401d0007000d9203521800590705242112000c0c01d005092442154032080b420000c8480410307a82d2490081103844080304180c54100300d015000701031030b40380e04d800f000034019 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 620334991 1250 620333741 620333743
    0xf060c15090f01020a080601051303061d0105010905010b070b07180e070f0206041203020c03070b090a1e0503030402010f120e0c210a0219150822210207080f 69
    0x5118001200c1140c000c0c00510502d2420b030302828a00e032010070703a13a00106010358000c00150200310000d184c00c000c1d1550f05c0c0c070307203030300380d0360807000c3c1100c09003000c1560404100c080c01840c3c05403608d41000d000d2035151045011107841030741d2015044035003031800320750300320701c1848515480f4007001e00340c4140544540d4144004001074444070089044811a0503125002040440c07007290024a914100029140250041d5110b130303542000a000410044001600401d0418010528100202503c503d01d00e00780e403688191865642199403106c080200081d07001003100e501950a10344151880088607054440715401e0001d5405942031a01144a0400000340030b06883c4085940080d003076041804000152200310324a5000c3d00f040800801604100e00c1c5002d02c0d04040a104800d1070303070703003882480403203a2035255000035082c141070003044407000d88001c0720b8040c138001e4a19606126aa8029880d4100d40d40da6030240c5da010841c0a003500910044005080d40800c0c0d80414814203080c07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 620336241 1250 620334991 620335033
    0x903070f1e090c0c0b100932010b03010320060c010e06011502060f1f030605041703090d0c020102120d0605031608101a13090b091b0f060c 61
    0xd11003030a1080c200140c9100c440c0a5508201c12540b42c403485011039440b1205c010a00030038401c100103402000064014a621828000c042824a000c1c09543d131040702d00b550069030744081c40c00503800001030020880c6202100d0450b40e0100d58542c5088070914046501e0040a00c069444500483c040c000da10064008030500c0e000e144c241c03400d0b42c0e2520004080781c03030041070070760041c1e00c59000100b452070001c003800d030020b0f0400700140340f400007200c40d140f03603481c160011581592214240010881c0384500d0f0392500884a02d0136086161070448290703181c1e001600d840402c042d0026000030340e4024000c1c002d540c07140940035550390070b030591014085d0117540b05031402807044540c1240581c81d26841842941c081e40003410317260b00412801c8002e015440e1a20300030f510700f83d40d0b00000ea66041600e502c640102400440c0f000080d05001d400d0040003070201d801604000394900c0803582201002442c0c2a0803940c01d080d2201d6040800c0607400307000103036992440b481100c45010b58001440d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 620337491 1250 620336241 620336279
    0x4090602030732091915020706080c03010b180a2d09022811010518010b0f010e0114040806041113090b06060a0c06060902090406060c0c09020903070f 66
    0x2011408012a01020040901c0100640c2112109100048413031500c0f51116802003203858407220310340c0d100c0940b4601a10750300030b00e1b00980d00401003085440d4102035060303444116043d0403411580341000e080110700c00c003900100201266128404241d03135914030b40000c4d01c40c0c3d51804400c9040c4002e0b20140c0c2010210503107889001c2030001031100da1038002c403001c5000c2c00a00c0f054041d070007548403d6942e421f0360114240216030b0783d480d2080c9000d03c12588107280d000e61240c14040d00e56021400c441c0c402203001d0198000d000c0c404042d0340c00c1403c0c00804002868603540410a00b241d04007580180c0e0081c241c20b00803d0140402d00000150b0906901e1b81190f860021010722040300040701c003042002080b00380c1240000d2698640b9901400c1000303120f003440d0842c1c02041e90707880102c5205030080020035a02061501441c101842114040c05860800103503004d40d40d1a0282030786035510688912540000d401180c68800b449440002c00d90542001100f94690004400704111201 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 620338741 1250 620337491 620337527
    0xf1612020f06010f03020409020105120712050618010e0c070503070804030b0601050c2e0c020a0308090f1f09020901030503070213020f0304020114041a040302030f0607020714040906020307 83
    0x321070803840d4400702e001412120108180414289168240406401011000e0b41031240a03c000411176081520441c03050b0701b665910344c0207070304c044042000c4440243c03d450003411300d00d4000c170040c89555540c505481512030071115070f80c0c03448a89204c0b84a02c3c40700521760301000c202c00341007007101c00181050360b11603017607404940e842100440d4540241d845e0130005601c25003200f4202070500c07414a00c03c007442121055140d20b03074441d0030255100501c20780016030004032580e0906a1181300c080e0003940c62009800b10031060100b00340d1b92180e41074825143d01000d1600030004209a000c00d07020740d80036295140c03560352410b125440c2c0e000340e8026805030048114204030241d551007260440640c40050606640312500112088080ca0500c2c0000510030400403c0451021a00c8080c040501c08029074070307810b40c030506040c20200c0800e02e00c00e40c820f0f8180720075260046000c400340c61440c2c040038006a14240000c0182101c0d140283c010351000090010441d8403151002c0407145c104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 620339991 1250 620338741 620338753
    0x510050f09030403060c0e120d020f01112703010504050303182404020a030501020301150e03071a0307021609091e0206030a0905010905100b030d020c010e060f161202 73
    0x1803502500d520100c52200503504100020700000d41c19030300c04a400c04072403074640b001c00542404120b0480f4401c07201034180d4020205058250390400010540e000504001d0284460300c100030401406407102c0c120304506405c400d459041044042c07480700c075078010001c1c0098209418266245d0b402900c522104d601803122a0110b810300145610000074501b90038035652b00c031060000e122800181c0b00701d920800300c80700007020034000d0000d14082d0000c0003140015104000f0042d00075465444200e010b508840f804100602c41e1604841c0d0415003442015070725a07904000320300f4155a4014420094100c0320003144d4900a03500000c4070781d21480307085140916003950284540c0300070100940c410703030400010350001c07982d8100f480384921510022510059a0390f0759428000210009645160354650311042c42c0b40c200500b84040b10507001030045000c05100023070a04040e4001e05008441c0004c00784818040c83c0f04035a01d0345d41028405901c0b801520744244c0c90010030600b440188120 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 620341241 1250 620339991 620340001
    0x120f020c130507020a051509070609140913050a050d08010b31032015040303020307060203060109031b05031006210c05180105030d030603201c051005 66
    0x1801038200500412181c0528805000030000c0c0400078100c6045003c2e504412000078000c0010021f001c03292450701c0b03010720303002c001d40780b40055a038462410003040c00406c020780c03003c0340842030b00d150b0305441e001290b64584511440c4444010b1000f0864881c0c1e881603400e205002ca000d0295084565a100d502c1e680c40007501198099441014110318a4012482400c803006181058560100d10300c002c455640380c40306030b409040c1d01c1c20f0700310200f8050007010302403a06c214828940034054100e40d04141c1540c900035564003649000511031580040462142da0040301504c0c01107500ca0304005180d9503d216013010030b0030324440d89000744111003580c60748110700e004242c00c1d00d445085e1800c10110f105480455641182d401382d0752102e02c2100840c2e1901d40322845020f101850316101065403410050502d010b401e02610070402d0700d0100e00f4000124203403401c0e8558048240c10400c04408440011034880da101405680000c0791304040080000120380b2071511041c40000f00855920 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 620342491 1250 620341241 620341243
    0x10b27070e010e010807020c030a05070f0503031e0d020d02040b09130515130908040b0406020f030a0e010507020f101d0406030c030206030907230f0f011409011b120f02 74
    0x1011007030104921043d00b800d15440b9600080d0b0000103881141e00582207034000c281000340c68103050f00d280d04600c2080c0991000d201d1008002e1000b80d0095103080243d5042c44400036103201070740e00071078001518103011801307501074031045000c404046680366507500d1004a207500918207540a04095240841500d4a9106462094002c0c03107503910b0300305c8130b10304202c0c00c00640040000c0c0307550b0f1010070b00041150000034001524042050715030b141c1c1440c0d4003a10300700c0707001100000707540200456222158801c0603100d80c0d035400e00b01143ca4445030301c00070b4241461001120740182010840c0300d0003d0348446258006504070700d00002810010080c0070a8403020301000c1d260b080421010001030810304001c65112114000341c80e00d054980c1303000501c1c1840d242032010f804184100d0404985403100c1d001403d001c0844418070407403005000a4a40c01d03c400c81401198004140c070084d03079001c2c2e691000e90368500b030030168114085241296060b008c1040707260000fa58011103584141c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 620343741 1250 620342491 620342507
    0xf0e0f0711060a090201050f03090703150903090605090301020c011e0f02040f1502030c060405160636030503030a1d06090a06090c0509130b13080d0905010b2707 71
    0x10840064401541d0703000e007003c054448010101e040000400103600d02c2d08603540a50b01491503800903024403491824003400c2c1496007800c501840c1e2900788040c00194000248a003164100d08140b9119144d441c0000d009009a980c0d0076159400e040d4030b480705a00c1540c0c6400303031031030001082000d0040a16450202d00540c040c500044020080510045101629112034a902841142e10740906048018100071059601b21001c2c1c1c0000e50301125410304403d103030054481440c000500d40315010780e0510000d94003942c442e0705084485520f001520483c9141c0145400008070fa85d41d06000744208010b0000b001c418142d402d40e200300100c8020041003050081c0e0014000340790310321968030761a000f0403004200301e8603001e450030005882d844104200d485421051500f00c4622013504040b1340841300280080c020441006c801800540003400b5a500041c1447e03000502004a1a180b401490701c0304c1e4541d80b00307a4ac842c840420b40c1d603440701c00ca03411407003402084142e2244482030310136130 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 620344991 1250 620343741 620343767
    0xb1c1112150613110a090608061021110a0801050f010311031504060f0902120108061e040c051f02102a0909050901020d1b0f180f0e0f07 60
    0x14002000c2145490f20610402c89005282e1002440e8440e4500c0e04401e6405642c1810104a5103201042508e0b000b40a1650000d02503400314030358000a0002080340702000039000190101e80000707060401c50f40e03c000d1941000601c902d075151810301c805040004240300340c901c03450b90185800c1132540b2902541c29880c0b04030540c1421506d41ca40d1200c8014440503030fa5400a40d40c1b0f01c00240400d0316095440200a03041006030749040040c03402d0004401600100240d030301074001e014070340103042c00e9803507040304103e103a0402ea20f0f98035180103c2d4595a0005030310903401c0301807200b44554110716881d041810f40032256003818280c20001074405401c566a1681180425108460310211400c0303c21380561405074000f688410241c1d0458105541100715a9408034207030905034550f00c43c440d02e076003040544007c180b04a12000701108078520040c41005210800c101200040800000283c101003503000c0c1c5060304c2c0c0c5407210400c0001c54081d128100580c000c11081c1b8041e5180017032038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 620346241 1250 620344991 620345023
    0x250e0307050d080a05030a0b04050a050a2f0d02041a03010f08070602070611150708060a050406030206190c0c0603141f0b09010509090f010602060f090307060b1c1112 73
    0xb5840701c40654031780d04010310300901c10b41c40380c032003000507070b140e00c0346c0c501c90014050001420700b4480d46280499090008030050311019107042c0c40c807200b00c1c450054be280ca255050700d07511412608804080d004a921400c0a05a90034582031100120300107541690fa800d4601c1c0c800654480d06035a84401c2c070b00c503020150b00300c04001d116046c410040981c0b0007a02000b200c01042c0f014420b46c41d0404129001e4002903000f405029452804001920086c40220360901503503045400280440c0309a030802940105042c105010701401541e42205d12608121800d444682d40d010180c044e0a002e44210381981c280c41c00104040c03003003000a00c032607070801042045241003462249081c2e11100005040c4801448409410358071115924400c0c03407910501da442e035141c094040d1412a0203494400c00c164600700300004918004203031012503401500100d092184c0d44086000405000724103000d1101070100c85003408032101408a0001d001e41e0a4998442241c10198590910702c04c840b00d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 620347491 1250 620346241 620346247
    0x5070302041d120703110a0c120609050f0f0c0103020c0c0f120601080d08130b070c0c05060406030905070e0f15150d020901020f03040f06031a19060324090203250e0307050d08 77
    0x141c41900c2741eaa141512a003000190100c40b503d0300e84c9004c54048140c185503000c2d032500e660030001488041018502800c1c10760410019456254840c400400d020f0b028024622012826175660000c030000816440181c4001d540c5548402e40c030303415620505000b0500600214a40032100c41c00c03040c40d02d030440d400f8000c079118640226074104c0f41310b0b415220214000d202043c0d640d034030320041c0028191504c000803080c0040c500142031000301d41c0320748010b00500c0d04019a8180e00741c44554030601384071907860045051000690101d018030000c1d400310038040f45d80210f01903d5801051082c200740c084400402c1d211803415524071840c01000c091010100c02040410301a4102001105000c0c0c4400c51450151020031035400e00c07039190034103140c02c0320300c00c00945416204a0215050f90a0180d100f0303082e2618043c51903125100310014564000009800da6043e09416400c1403481014486a19a0a4001050000d010b00614800c0c0610400000c80746454404410300c2079200c0b400c981 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 620348741 1250 620347491 620347499
    0x30b0609090703140a06050901061212030e0d050301051228140d05131410050c1603050102042102030615030f0307051f020705070302041d120703110a0c 67
    0x10080001a107024114824002c01100055031110340c0c510350301e56240104452240c6003030400c05c0c6e8a01800c1107800c2d0f490f0090500881181010110312190011035070103a4411904084000b4483d5090307074141030103902d07140c10140c1d9202d0011812140c003111035210310420920a181c50354020340e0300f421300c1000303c1144c4000c01c0010701684c000781c0c003c82103500120101c181c12410318071601c0c444c80009a0000c4c00c03408048103e00d00c540a000b800e441c03001412a1400400c40c42040d81042005204c0003042442e4a62020003c2d48883d10001c4407102c007055a0b490842e010b0741040c00784202e02403002660328200c3d0800180c90420f1ba40040003412507072501d455416050039401d6906401d0f000e010210048058200020900b0300c1c442c03401455a85241032010090700c1210682c01c01c001d00401406008ca08002645000c0da60110780008202d8a420541e0207a5506c2c80c00b000c00c02c0c000d81c0b081441c0103135130402030084503019171035010701c4061140f802c544480318008001d0a90075a031500388 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 620349991 1250 620348741 620348749
    0xa0b090304090b300a1e020a06080412080a1811030d030b0a050f040605060703020709150806040303050a02091809191a07050d020d0504050c031216021305070504060e0901030b06 78
    0x4003100e04130400381c0d00141d885071107044009003509925101c2030407010fa01001c508100200000800715450103030128282940d03080c1010341880084000c01688101080d114074807075200134503418007240203d00709945c900c0c21007980c90502c40c4151080c003840a034002c0e00d0340a8090350515080c020412805281403000300800c01c0002c003100c0d600140e0740c10001c00e2070b8980a00400d00240a50020300051303242c00d0400d003d03201c03c2d0445020010031031030100b00445002500c2904541d044c00c0100d25691204803030f0b0f000f8001c801c49a41c2c0039074010b49850745e050865a2050240fa522026103401d900e050001003641c3c25240340051200c0c42c891040c0804840e5802c03c29044100c032325000e490b003c641d40945050f60007108152020070380d14401e1008007d402c008400c06072500f64003502d002d0344480300401250042d4900103501e003c41d1045401103540f2604500c4404100c20340402542c20441001401034109009603008543c8000c040203c9185c1100c0c03840c101d0313502000e5811030b40c4c0c600040c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 620351241 1250 620349991 620350069
    0x8060112110a1203030c090819060e0106170c03030906030f0a09050d09031a0402060f03190504110f0301050402010905101428091401032307020d03151d0403020a0b090304090b 77
    0xa50300e00c2e558030b01500cbd0401c1d0a00500380102440e080032140c0c20401c200310f9040c940d200d904944a0750003084a00b603152104001d40e0703800980c42070f0300091381e0703246201140903000d50740008005014842e90458020b07081042030043d03038001c941d000a0f81c180b03060703402c5140000b9180a5400034040c81501400c1c00660010740d0300811418200900c010038629102c03c0c1c1d20141c608480420801034620f01078141000c8000e103030303602100203021a040580019085280c81e000d010f0080d1107a200b10a5000d001d54000803c400c9002e1403903955801211b0402241080d414440031030703590608070840061312a1000c80c0c150750039500f80c00c04065001d001035004101981d550500d201844140c011015903000001c1d2040000c0c1e0007800c0c0510444d20024200c1e15146020ba40c211030022051240c0d491101c01640001c0e01d1540bc50181c0c0c07580d00302640341c0850000300500105182d42000102c40d00071010300100e4070304d0711090006922940c204074070f0107800d802401250b040d029924408a2501140b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 620352491 1250 620351241 620351243
    0x2160806220309090c0210050f0f010b030603070e04120e01020708070b0a1b0b040b01120506040f02030c03061807060c05060f0411030d2003030108060112110a1203030c090819 77
    0x298080c44d82c0e60383c40c4002d803a404525078015030400310380c5080602d00d42c001c0f02d91000004054100c2e074500f00090341e502d160b0601070100102c1020000403601e84081010310003905030b42070040310b2813409290503c030000f6040408000144500305100495000145020507141e0104c0540221828040900e59075048001c0c10300801082d86440d00b44456071503041d0364018056521011540f4003404d1181400304180d000000c08441a80c0480201d03802042c51078001d94003039100110309641e40000303890213242181c0a80c0c580030701c02c00d00c9803502000c000500b45490b00c07429034203260350703802080d10b090491000c040c04607045800007ca80c00a07040d407540d8418803400d80c1c044c1d2414100046071514080792a60004249004410800e55211198040d03105046c440118955810301c11141e4480d00b06105821400d00b2110148081044c8100c2e14603542401601401c003165503040085003040100b13409a000c40c2c039049510480c1441100f8a070282c55001b00101200540d101099a4146064078 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 620353741 1250 620352491 620352497
    0x5031801180602030d0b0109050604061b021c030e1f0807021005010f17030a0905010507140a0c03034806150602070905060d0204090f0f03021608062203 67
    0x2111001e00000030a07844003401050740250b4880c880281d070601152405400c036410701030942020410740c0c2d00e0b2812201039816518060f038148041c8070f0500b00c09000703542c00a40c03000004441d40400500d0038408011705029503104d202c440c12003018001c01c01050031400c011810401e2101850320302a164040e009001c52040740d0315480341041f030b1011110207802251fa0b001d0607000c10000c0c0d101d0345440c4203243e005400a10f203416800c1c1800b030103555040c805d40e41400008501c410034081400411180902c801055034803c4200307103002000001140011404541009008580e404045414240085012032074494404000c42c0c41b914035100d040c45a000041448802030004035540550b03903421200f421920f1440741031080190030441c2c1038000960071460001046070650b5061107850020340c05640009414049081090000413000e80203044103140c1107000081541c000b4403e010343e40140008a5019210b1440300c0c0c442a0a07200250082403201c40d44a4902c22055000c882034800c0c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 620354991 1250 620353741 620353757
    0x40f110d150203090c010905280b07050c131509050a02130e0f0f07050a0315080a0c0906140d02060a09030c06050703090e071d0102010b04090b01031e05031801 70
    0x20790342580300c401c00c900c0075085940100c14090500c808000d000c52114007420003403005410040815501c0710361000d41016813003181d280404020040840c200903000c010140c40e82c80c0c1182c1859580d40000070760860040344000320440c400b0223940704058480e548404107211440c6010840c60160001170f0000c3c0d540390b800c10201504d40036260b40e403801401848400314032450150550075514100030706000d0005d052401300012280d01404880050840d03080015940020b4030240541006a0b042032481b48114504c0006104a1254000403510010000e002c142d40b106900c02e49016104881900152018503880051600402a11003040d0507c2d06e60801aa240c84980f03040905910240100d4000110a010305521410040c00b43c0341c404081c0101341807480000f0b1407100507440021408501c0c1e603981c4040c0c0e00c00e410858042d44002c000340030201c0c3c18140510105000e200403245e55140d081d64419024070000d451400a40140c05142003000803401c4d42c44c81520842202e0400c01d400d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 620356241 1250 620354991 620354993
    0x1080a110d0b13180609050316060209121b130b0603040c080c011716030603080a02030a110105060105030f130c03061a18060103020a02031204060c1403040f110d 71
    0x40009880401801540401c036400400c0c00d02c07264001c405110300d4003034105000c0414034511441402a13241c1e01c148002111041c1d428250f045005050f030440f40c0c86a0360b00c8178010300c40c154003e01502241204d460482c420028551a035031003030224407907404029182c07400702614180001c0ea141811260011406044200020340340798402c0f142101c010040c030b00140040030041000042070042070038501e0b4000300c14011184008030042a511000d07031048801c0010a119030081c0e00116800500d042c0ca620041c00041d45982110180c200014001711151180d13110500400f07014020607101c441c5035890301c091030003011200910541070075201c0e9400700c00040b4507102c80c10043d4007580c0001020f40d040160074180601c803050b042c0c030805103168a01c3c1d8200d1208400368014109090050f40d8860981059080d805010305510a44007488104414007440750080c4503842001e40d1044400c00502182c58901e0109441c0074182883ea440e258000400d1032106e2030704080024840c1030070b509a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 620357491 1250 620356241 620356271
    0xe0a1401140d1e15030f03030906060306061a0310060f2106050f0f0310020901090302041d0601150203070f0201110a1b060e01020a080304060e03120f0609060f01080a 73
    0x2055a5242c1e10400880c5005041c40b400a10604440042c428500180410103400300c2170b000140804141c4a40142094000d9210b451302d9a030004085c0103040c1d403401d055004140904c540d415401c003c81c09511001581001c50340710300c4220a4400b10300c0d041050446000851780c4580c3d081c481c2c40100d03161315004604a0036222801ea07030002c20760704e08100500c1101081156150302a4100b883d10401d665404602c85100c9007280e0720040c1c4806451004030b80368610350380007940151610030640388a0301000e49481c0398201203400c4035000d0741e0320310094298041c03842c5514016041400b48500107900c01846e40c1d4914014949040c81c3d04070104043d05117444c0798421a054103800e40c1c4102000d000e606680c00806543c102010303016030307000007c2d4440510b00300c0140340b0750303000000404124a13036201d064400c008400300ca4031042c4041d1090a40b00055443c030b4144506d41d4005002440d00d400c0d0a8032400c2e000c2c188045040300c020054403910405841c04800688541922130745280e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 620358741 1250 620357491 620357497
    0x43201020a02100c05030708061507031d010903020102071208071a06040c020304080d0c08040b030705030a05160c020d11060c030a08100303050913061a040e070e0a140114 75
    0x4410005030384001072800649040000040d1203502800d18558010481e002801e99520000301e00700140e0310358a00000a4004150791a844807001c40820101305055114104c26045c4240c6100282007000e014010365030181c0c036120081c010b078000701c01404856180c440c5401c0c040c1c80b80082c2802c10145e60b403000140d178807040b0107011415020003000070a19044c0924845214030b4005185424100b507101511211201424024400c0d400450010440507408403402020501d5a031034590030040d0004000c3c1e0b009442111446081c0800321b03d181402d0500561068041d4030742c0c0603443d11503070078080080900742007900c5080f46455a45201d8035030707200800008c4081c501460b0755810700c1001800055004e410000706180c00d080c00d00010b81c1090446034880400c40e0200300c00443d9641c2207025000340c1d000303054030310345070a291240100d0100c00b403c146d4440c140c48202e03070b90b1100d00032030305a00c140c3c0c0404d03407010f8030300303010001c540c06900c15001e0840706151081c656100150180d0b17607a8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 620359991 1250 620358741 620358833
    0xb2202061605060615030c09060418050106090e07050304060b0f04050405070501020d030e100e1f0603060e031207180e0c07051c09090f020d14060906040b0904 70
    0x200301d8101c19010000180180c0d41c0c0200308513203105d0800500000304103d030000900254030000d001401160f143e44000a85004051a01900d46000f0340c018040c0d024020030b114510110320782c0b080c04901407000321360440c030a145981d1814107542d520b4172640c0c090040c2440054200e0b008940040c100d884500800f4482d0b800b4a00504645150400091414000c030080d20101071030300f4040c2c070a901003c60001002040c106000c18041c1d440311106080203100310486a55400112001c128241182c0002c01180c0c080e0204012030314070a01c00239240e2203825640b0b4484105480060722036405140306920710488000d04450a503242c0e90514040d020035600c1a40000001c640103040000802010043c45042405c25120350307144000608107000500400d44403d4503270103000d01030384c00e035815107940c0c040c420014400301160f18102038170008165407090003028414005007050406020701c5102040250102c01c1d950303229120249072140458070b40030858040440c5a242d020081d100143c42 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 620361241 1250 620359991 620360017
    0xc0210120c02340e0408190c171207030e071206022d0301030312111902070503160306050a092102060105030601270b060a111203040b220206 62
    0x40903e0408000c0c4007580c5025161150b59180a2686400101c80c2c405085841c10400101c0300c2d16240340558442c052402283d031058144090750480c1680060040910781c0070310030b10320078480001c6509646200304070010001808480c0402c4840e442035100702c0300801e080d801e660b0300c00c1e12901f20070f00c5201b100c403095514507004600d03090700038442e000f01404030852404098106804503100341c01d5010501c07029091024444082010b61401e801940c0c2c1e80100722840c42d50340a2680200c1400d400580c84e0400600c181880030549040004a02c2c15001d03178080084101c40c50b50b03580b9000380c1300051507400504d84421510000690801c00900e191040d000000c10704102ea04000b483c04c2c5059015921a511500c0100544018100c07010b004600107108100c240b650114040060318146821302d4100000044440c2c81135800413034100f4a950b40d070141d51112080d80c610f810207000c20782c1c000c0c5c20125000e01040c0380700420249842600e40d0411844418001900000c071582c2090301c0010b52 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 620362491 1250 620361241 620361253
    0x150f060310030b06100f14210f090105060603010b0a020a060c05070b0a06060c0807060b1503100603110405060a0c0f050304031e051c2c010e03030403030c0210120c02 73
    0x10800709100c1180d0040054030101c0c5d400e50700c924010185052040c640c000d00c8803a240031028400700404803000c1d04070301048601b088920401051803c00300700d440240d400c04400200d0f50305034040c0035044c01401c00400f06401d503428904440f4a5510540e8036030203620803080f444c00028010702459013255040d03241e030394960f101420400f0040000500311500b4034a0a0424013000d50001d0f2400d0b9869041407006032280c180345001c1700180400396140394080329203146181d44500b030030021403123490a134801e030f000c2070341c1c0e40700640603148981a04066a00c05200500c0302e810044050000980f00e40303030041e00b070403254031030940c80c4210980613107860708000707130074070510044480d01c6580382c8101000a078040040c0c1c807455110441e1070040b02c40000ba030705458005921900400b90f0701c48802d801c44031040c01401458001c280150680e0380072541009549140f803a011081e1000c503a0075443c0e10b43e084206508200411060740c680c3c40a000c0e00b5680209020783c64400c00301d00718001c1e001042c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 620363741 1250 620362491 620362493
    0x3010302041805060c25060902040e01140105090a0213080d020106230409210206150f22020d0207060506090105040614090606190f120c08150f06031003 67
    0xe03181c5101600c440440c2c01c0c440350000a20000303840c0d5008004c1c0301d0040c0c0310301602d05202490280e081d044010343c201c1c2082d08092107c0340d1f201014052084404100b982c00c414625426252002c40070700410152000410950506107441a440402c05038014900603081c00380426407181904440e0555010355040d01072550244110000f800d00c0c05071000301d00340311200b10699181003007d5140901d8580c50080304022200c00030140e802419814030f01c0e00740038110029990a4201e900c1048000c00114070780c22410601c01310401c090000d0925140c0b5110301008106c14000e03010841e1545500b000702d071407588050700c058180c551080e50f0200301e9042c110304100000300180c02062040c0c2c601602000500d12044a281c0e07030906c01e546862040d900d000010322a03000c2e110391a400303901001d60890f0a2903100c1c0c507000701445241c46071304d00c00c290b548501080303e0748e05511101042c81440032540c03500030602003440900e002044081d8114100021840039041079890b4054009410400c3c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 620364991 1250 620363741 620363749
    0x30c0a08101109090105040e0a05120705010b0a081504031403160f020105150f041d01060501140c07170f0d03151202030d050f040f14010e0f030a1203021e03010302 72
    0x10b0701c01d44816944038240200c040010712407260611985101d41da03030b202c0041800c542030100d940d440c3d4008094800107030200c003000e0b80c50f80c08803c0c102c80c2940f0305802d04000d482d102c85468260b070b10340001080c29102c030038082954100f0180c800e030240300078008201228090100218410311060b2407404689640cc175014000c00011034a010175a41003c0c200607802441d4000b0100c0303040200c908004003441040450000c0001c07032240d8010040d481035408002e01e05401c903004458081e0f80385a02e03a124019450700318080c060b034804803900304540c1081544e16180300c01440d00510010340e403640c030700c1c5e886c2c19140041120385140440e80300c02c00a913203c0300911540c0000c20045031842e003138840a50019403942c150803078413028071501042e0042d07010304480644014082d001174a1200c40c3e2100c0420340d5805410041c86c1c00510043c00164450402d000b000b1682400500105542e40f0b4942e5143d104901c0d01d0041400c145c3d00344026100304800107601c40e0240340c10030200d90b0340d5040d80180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 620366241 1250 620364991 620365001
    0x90712060212010509040f03050f0d02180906090112170910081f061e0c050703060e0705220b060c0106030303230c0f180a0e0720100b030c0a0810 64
    0x15902c1394840c05c0401000c03800642c00c28001c140e051403c59583c0700c9042d20380301240995003841212920104401195a142031281075000c50102d52940c80740c1e586804005524200740540d4640148240a44001500005c1c1d11540d0081d400ca01ca801d10340424086258401002d0300308000900350001c0c08800340b07842c080b00c850b054011100610301030a00401500f440c000556810521916254a02c1d8140c803c080f15100e441e0300c1700030f0300c2c49640d4904012000c0c02d01404101d010703000b0340400060510780b9807450301c801a0075444400800200e588648004e02041c401190080003c101d80c0f000180c0a01c50240911700c0394500048801d1050101080d20418400702c04081100c1c0c401d01008454100a44009803c80001c89030703148011540d1034401028001c05030f81007000580003007040034201d0001d030300c595100c0d640c00c2280d0268100300c43c4001500e504521070754200000119607144650003410f00f03901d0250480740c20680c00804144060510350000100d604075001280e10f1203028011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 620367491 1250 620366241 620366249
    0x204051006021b0312030c030403020601050619080405101d0f0d05040e130615060f0c0c060c0c0f06021e06010e070806030115090f0e0118080309071206021201 70
    0x14042240c102032000e552601c6250307864500741c41e80b07181c02d089661304001d0446860310840030b00d82c07617003400341c40150141c100380d504070050700500f00045294107101c4141c94140210126160341c0c802c00d50300039600c07484090419150307030049d80c481c440000c00c1d03030140c0c1ca403803058200056902920b61f6125400c1c46d1318034601c01c01c260030200c280e0414aa202007542c00340e94440c0c0705040307940c55103518009460801781008007418200030b001e40803151100540030031030b003c2c2c1c0c40703104064104600480e00c000e20204002c080b042007401c01d00c1801d1040b4000700c080c0d0310580d145910300c3e40310381103c200d8101c03941c40600103901c00d21204110307060f104410031078030114900601d01541420025611200c0c024048002c0104401c0003c08550b403d40050100d05a0071542d851b403142c8900c2c81002070040d900c0c00c440e0490a05182078419603051040724110094003c5a084550041c0c1e92001c80740c0c030107808000c040c404c4400210b0b21071024411441080d20607107005940d080350001e1031110030380c141c1c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 620368741 1250 620367491 620367511
    0xf0411031c0e060301031109061215010302010305090a03120b030a0203100c090e1003060c0c06021b060603150a0903020a0b0106210506030607030903020316031106011a0403080d020403020405040f020405 89
    0x40101b00040084200514078081100c00718920381d0f801000c03031030040b15503200040760720a4119070451014100840c80c1a0ba000381d070700344080da488203a0740c2e035500560240140054001c0e04c803500350307400e59071000c1c0541c480202954507074070f010b0b00068548036642c9004c510943d0782d900e02d5404582c004c1200c0f4000e1207244000111841c2044009199400c184005060f25480e814403c400d20310441d00c801003903905c02c02c2151580c0c01042010401c5580c0d24494103a40b08982c080381232458000f403141034014008802b0b840607566811510f0207452a14000c4065204075102080001e03402d81203603018044903034800c004800403a803001400c801d14140f002890b031811062085603180402d40c103610181c1400c022030b024903030f0310b02242781d44580300c0707881c010805a208800816900c690401c1c514840d074021980203989562070200c010381340350306001d03550030108402c200180321480544200d038014030005080caa40da4000c42c00740c0c0c0f000c80c1c08030707091150b644132801145898400d2a0f00040001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 620369991 1250 620368741 620368747
    0x30213060320030a020d05010e09060702011802150702041d010b01050a0e04020306011718011104050a0608130501050f091504111c050a0f0201260f0411031c0e06 71
    0x19551106064220b826403002100001c00110011102d8040b00c02413a034514041002d9030f0b650110003c3d10106552099160041d44049400540305021350034101c554540052004a41c0d039007080752228107041200a42035050194202582d207a02c00d0034211403100002015005145448a0071241400421b9052000c14011741501740e0340701e04009644002034800698a4031072000680c2c801d0031405060300d41c2e500400820601aa850300b45046603503602c40284070744086003011480d207000d91301540c0c0c2c00c40440c2c041006558031814007250000c5520b82020300030855078540e182903400860703540c0501900c260034400a00d07401c1008051102103c20044024205603440000c80c038980131509128101c1e00810301202c0e9a01d201070720009600c0012244148214504080c9030000380c0802e0340460032623143c01000c032000c1c3e9880d507481003011b0091a110340d5424015800c050000d0010784500c02c11042070081604c04000b03001035120307a4a0324100d00e41c0b240c0f40c018100d030803200011740546028 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 620371241 1250 620369991 620370011
    0x1a01142a013216030f110a090e040f030e120102030703090c060804030806060903030d050a0603110625060b0415170f030706020f070b04030504050301050609010b030604050a15060302130603 83
    0x2821502c0c0d0007048100d841c28490307012802c12400740c00d0003104014131625054044103043c1a0030000c2c200384005880d403d14040c0c0e07488010b62580401c41d4040c2c03000c00100039050000c0d20030030101e10b40401c0280310148172640703640c10608980007140d101010075910f02085050040c12001d24001307091520308200310346019074000f05892000b5090314010040840c1030400c690301401075a10107940d060041108d46020302e41e140150001e0302c002d0f80c4200c0a07094260450800c0c1c02101e01d6000140c0544403415003c011902c04010701541c00d030781030340c1d54601e1540c2c01d035114062074007030200401d403034440207041c09001050308200c90307503040b00c0b640481c040340003112002c400d0740c40340d80d0400f8005031034541c40040e01c41c2c0b501c00c20000034032116100040000b09500034014000b40c4006800070000ca13a81c40d0309010254000303024102290030284005070305454a50003066100c03028943c0440ea0105103440c980e810380858003c2000b20f50042017084160250b0f21007000102014a014000d88001c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 620372491 1250 620371241 620371331
    0xb030c0f1803013b12180a050f0108041203090b040602030406050a0c0c081308011104060e04020a1b050c130b010e0414010b0d0605030d030f1a01142a01 67
    0x1011121101c00220883c01300903071205105841c0380300a5a42015601ea1704a84d080003072800c00d4500e248125200300001c50181420a1808070041043c0c4070071841d5203c50312820503010070020700c142016282c0351540c0026101c1c20b5650302607072280c9809616401c0514001041d00da00a00c02c0b40e0107450240d13120560f076405a1580c01d46600300038450f6490000503032407040c8152170340212030b06609020003040031600c0b21008204450f03013556200000c0759081c3c10071041c4c0c03081e080c083c400140311958419204040421034403085102e40d0454541e0b01e44072020440c0c0052600d82000d0103980c4904855031941c0060492a07414422502084441c20115900790f490a060040c68080040861042d998007250782c000409018014215540301c2c5402d08018042d1000c0021800514200b000c50800340b100f41c6001c1d90980740507191268401c40b030808500341c0d50020354110740031103002d0f26110b150484040c100ca40d4407000c40000b054140048041c41c010801600b01e442e0461407140e8039240c8100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 620373741 1250 620372491 620372561
    0x60717010612020909010f0e07050703050f0306031e010506010e040603150903110106120c0e1003120e040f05011712070809040e0d0f0207090606090b030c0f180301 72
    0x58107040071400b407441d0700d110000074040c0b0f00704180c120707120302c00115501c01c0c00d080c8001120300c0603100011a548000c02114180200301008010030428082c00f80c900c810074018581c03103400a0100d54030554503501d022103010780440004a10b0759030b902030107010359100e60045000c040a59041c02100d1460351603da0310090882e039503c52070340c1c0e6078000c1d041510800c0910851210310b4000d104e069161180400601c010200c1290350001400b000200d0400d48204544070300111032844400c0c514584810740c1d0001126050030400105218100b5195203a1180c584402d0346a84006102d42c18401803014505907038010601c45c0d44104443c5102490020031941082da1121038107495200c02c4d004070b0b0140c601c28124092074040d141ea606140daa000d0801c928a00080d42100d118a0790340c02c07034104075503142c003030384c0002401d4220a100d14101d8400443e000b804090040d40b81242c1007084181503001030001040403c03a20000c0201407a0900a1046240716213060000c809844841e01311420 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 620374991 1250 620373741 620373749
    0xe010c090f09090602120703140703050708060d0501020d06090603060b0111100b040b09040b070f0f091a0906071407080705090a1d010c05071a040b07050c0a020a030f0506071701 78
    0xc0d0715034000c03c00f000099019117000d402c00e1001d07500141441400640501a0111005000a020400900c40e18400c0c000c4c0360044074280c41d110090341303600042c04070a01140b54143c0301903400700701402c50440248109002000c2064000a4081c19490400c2c00d03900d406007124100440c0300001400d06402040303807090420030300d41c001184540c0d903003c40c01505510310215800109402044148400a0003461042c52556185040082c2010080e103400c10444028000907891074424030040341800802c61040f15810025820041d540700000e18540c40014102e4010540e86103a1280880421403c0c1c00f4261040240140d00d0801c00803c47d0168010a05402c0c581c4035945509844c40b402160810700a881740240154584510060300c0c40d404108111000c09807030800c0c00c0d554546041d80c82c095a4032a11708826500c40d414112507603005420300c01000d000ba1940c00740140d88100c050b0004501c1b440820400320f84030b003022800e0400050280090040e046004000000095000c1c1d047d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 620376241 1250 620374991 620375009
    0x1514130c1707110307080703031d030a1b0f0309060801090b03030304110111010f05011502061b070201211b08090d14040e0405010b04050601140a08280e010c090f 71
    0x1507484600445451a0703c425040d031034003000070102c00307110700c1e00b0041a002c1d0003a00c00340100da02a800000402850201c140703010303041449402041d030b00ca100b850742a00104042c00740821115110812601e8030341d001100404c58000c0100405500060210300500124408100111407a40800d441c0e1100420050114020b0480e0205681c003c1c100c140100d00f490008210210061000e0700050000303018120260056030304d0140300c84c0c130005119205100c1107843d000100c42c12162504603801602089040c0402034690b000340544055000c2c00902c40e0303001c0419100d43c00100301150218545100c005c2103051000c0090107240080e0701b1a08441610341060600d141c102e40500ca40a42d80106140d03041c048140010f101054011080070076044408001d262100c2d80192000403150042880342d120510116030000d015440c09944040d05460540d81192209180284020300020507140306035501040b003646107003445914074040841c00c4c801400ca0a02503008442101031051000c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 620377491 1250 620376241 620376287
    0x3071a25020615040c05180d1202030d05070c0503091002010204081002090325090f1b030e06060109121e0f05060f100f0308030a1514130c 61
    0x440c084600095100d0889040c0034000d1540c0010020b49521060b10b034402910091000c0190078605485980c0a003401a240e2526104403088094028000344040d9588032900c031a080010990b00100e00000b40721590155668410204010040322406040c1c48100710210303180c500014800811a490120119482103822200c9c660072806441503810125031340c00f42442010740f031565034014000f840c500b1002d66080d6074000507215102a61803020001e45031b64441c08103c05402903201088144c3c81c0c00b80800c400148103035103512408003810314000070365200039504025000307100b0650064003d1820340700031460304800745482141e058000d042d0200c42c1e8518140c444500c03d03412035055200360350b41c0000c0d0f541d044c02038540c1c0040701c0000b103000d0000005050b540203c0d5035401501c00100c400501d450940c0c41d143c1c400d0b00001c14800c88990355216508030003900488020041c90342401c12005842c080c02409581c180f101c20801c4603d04080c4014141500400c0c1003003507107019100300b60 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 620378741 1250 620377491 620377501
    0x90e15040e0f0106170721030c03020c06030709090b09070e04020c15010e180a170307120e0d0e01020609060a0e032206030501080a0f02130f18020306070203071a 71
    0x30074150400e02e0002950b1900c0000108100090030038130b5001a410251880303141d451403034940a100d43c03003114401041c100240c400080c01401110012030091044800c2410781902240b45076105807408000700b8018081003041050600442060340c5098800c0007142c141007202070910b07803501c0c10651103240c020410814400c01004900c0418000142241c0c40b565201c29a804a14042d140c0d84d1281003e00e11814400c034000071070072016540404090781950104440c2c200760380004d890341c001c1044645400c1c11401807070103a6804031103058007a10000d01d280c04d01421204d8000009410754201c0c0040000d035035004070754035901404010000c9a40203807407032141d0039449400c440501c1c49401c4540d065030b034440301440c103041ea04282c0341042140d072901251603a8500f150300003400e00200784146001410b01c1134111040481d1369802060003038440103810141c6d0030542c04a14480300110081c02540707002c01c101070b00580d01d03001840c9400c03c079132076444030380c0c0c07800d41580d803040c00d2103001c24 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 620379991 1250 620378741 620378743
    0x10206041e061e06120305031614190905150f0313050303070203090319080304060e010f060e19020702130902011206120b0f150103110d0912090e15040e 67
    0x8040c099104070200041c000541142840d900101010340e403040c03410802080e01c10b0641180b00510b40c151f22480e0850383c6001c246d4418490440a00301013007106910408900303083c5010308480b0400c5182c840e003400c07001c8070041405203954881da00c40c1000314007060380c16800000310740b40ca000009265a890b0756113450b03d00780b8165180c008080344030000400c0b40b00d87d4040003030000e0844c21000e646c050008055000040d45204201414060f810804100003503803992091498a201d400041741c1e00108080040403a00035034407521205001c401040004c1c031045c09260b11200005c0b000314141101c80d004907401e218000407170280d071581c0f11800001d6a0281c62a4800b00d0307100795061081544a400070804450500303000c8501c28110408a07985c6004996654400c030000e09840c00150300403001140601052887c20781581c400300507912000d0014020712502e42c0c02018455205512600d0040031446c1e83e41c0310580c5005c50300d0034001d58030740d402c901d8108910200c4c1c0c04141302c0140013800b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 620381241 1250 620379991 620380043
    0x3021216030813050d030e060310030c080102072d02010c05120304150c170703180515010e180319030213030506011a040e070c0314130504061401020604 67
    0x120000c0180a4000000c1020420082107481c1004103801d02e0b140c1c1d10340c248010444420001000301c1c92616951004c0c0c01c0c60005140c1c00790308100e08100b820343c0c949945181c81400c1d00103c883d65000504041070005582d40c031214405800b990941c0c0500c141444842841d0710ba100a0420143c820000207001d010405c2589849201d404a6901d05013442e2090b00c1c4006050002c0c0307070b1811302d0f250710001801607000070040642045078060682e100c079400ca0007010f91865400b0b6145a20f03480c00301041c0304110200c001740e0241c83e101e00d1541052240ca81c0b41500404c1c0140040450024420b4280e010080d41c900481100219000b508a0b00d410b2b0b01a02810032101040079495100006100001680707034104d5119858401221650211440d040e118901642081d0b280041c00700780818840c0c2d41d00c06003180a0f203484940b407480001c1c2041d083e4040349160340c3c00000321030140100d16041c824600204000c2c41100103191036440041d458450080001d45151525141131240120201c40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 620382491 1250 620381241 620381263
    0xd0f18050d150c030f0608150a0f020c03070807260d020a0c021206061003180209061503040b0106020606091513020c03120f0f0910020c0309090711060a0b0109030212 73
    0x82400f08403910800180103110a08903125454207003200050b90000c00328641d61014a01e424010f525665001d1100c007070039901064010a039800c000d44c0c00c0030103080c4080c04929100740000c590700c4101d030400b0403090304101081c001303001c1ea61880200510007001280c454210704480581ca4090f00242a500028ec0b01800b03500b042c90307207035090188075004c50114803030503040719100e562043c0f46a0442c12501e135035401c5244800c0e0820740002614014110b16442500248082465030000010a6594105403411288500340b03600601241e0340610072a64400d4069030a0a0f85140c404105840d02c0261513000c0d01880304041040c0002011380c0495145041180840355900c44242c0d00310b400744011114208030110360fa02082c56015030103003841c01200c0c900c2c010701030407101640c0c440081d07000c000a45a2072004200c040d0440d01e400f6407143c0b1034011900c2e40090599500c10003800c0010003000c031800340d45455030442d01aa0088640d00989405440380c1c2001440c45600500c4c090b28040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 620383741 1250 620382491 620382533
    0x30403260702150108030c030901080a090606080a031e1b020d020406270b060427110910030b100c060f02031003020a0602010c0801120203010b0907020d0f18050d 71
    0xc01c12207035000036445010303801940740140d0030380c1c1c2c5900c416100e000706c00c1d66a400e0b07003040181e42095072213448038507003140c0c40440000c1d03500126502c060031220782d540460300d6038103c00c025200703140e0000629210424800c0c3d80d16483c98114500a002c0010f0000a0200c03954000c0900150740b151000302c21042c0d0301034010061903845a119400d80c00304000741d000004e40031400040c541d4a9030190f17107500040604442d081070304002061038005e042411b1490300c0c02e40c100c445051341d42c00d4020f0f80d5206140c030a1b0195200100f00a224040041004d2a818541410f816001c42d07101c404407400750781c2c2c00d40307048a01c1ca00c0c41c1c6000b8000c0c080c6840300f03030b00e43d5001000307100c03041c0c0c0583d0031041100d2017100e1071700ca01e035600c0000343c4c20380312401c800380041404000100162084c0c601c0c40be4050748001c0000416600303420001e00030f0401501c0220040e03111b580300211217038001001544c03851003410f002076041907030101e040c0100e985000c2c0c240941181e004442c200092080c5540d9010f50740c103 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 620384991 1250 620383741 620383817
    0x90306050a0e0d021e12030a0b010c0f03051305041b0e0d052d06040302061513020c071e030b010b0a02070f0b03040203150705032e0605070c0e0c030403 67
    0x54001e55171415107440e60044051904030401c5240300243c891600d901802510b4210b07642c0c44018001440050f8003903050060107044000001c103020140661a03210b91a100e40790100d601046602401d150001e50141c5c0c64665a081041d401c3c01c5500060001841c04000d28000e46022608000010b00000e005214000740c904121100140c080c52081a01001e0285040c03004038030303981c81c071041d100070b40540c10590105402c0807180710501180b42d009040102000944160b001c102d90190007403a82c182c020b0741c010300030205900d03403209290030071550085000e401c544800401d21410300c20b5005191000410f68009402400504010f1407150700304502195100902d56040e40200c600b28420302510542c0070900c60100704a070700680c166a0781600316580c00c14443c584030110039100080c041c0607641458891104d11003103014150b1542d0349600d80b8520b10b040315091200d034100b00e607200f11400400070018608400e982d4015014503201e20084410510814040c0b22101c649005440b62 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 620386241 1250 620384991 620385013
    0x120f110c06092b08040c2d0609150e0a0e04030908010b040203010e0f1305060a0b240a180306050114100c0206160305092e0206010501090306050a0e 65
    0x10403110b20440307401c41030368682000c11203a2030600004540c0c00000075210b40c5aa0069441440890352041c4a0b680c020001500d5000c40c41c40015160720305844c54581080c01d5905e9808150314500518450401c022a1401d000413050030851111040080000410015140d540c1d00c3c414034008000c08841c1306924200f5081c010120280c0d4025400650308215112445041c80c1c4220381c103c515011003510710792944107100000700409404456214506144940400e6040c0035183c05940107c0d80001c156030a802030001c003446d241e0800f0443d44890340c5031081c040c0c44404403075002200e49440307010703554401e0a402c42010076410103050589424000304020249809984d101c0c6800c850106154505030f004485445002d00000d411450070f001000300302420010301d024440c46414000c1c1400c5660700030960208008c0c03010604403203513800e80301501c685d01c9080c1420401510180c40d0640c10100007030601c2c44030b40710082a0980e41c4001410703950700366015084144506080c0c44c001010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 620387491 1250 620386241 620386243
    0x30c030b040209071b081b010608250803180d140c04060b2704060e0f160206100b0f1620030309010e10020a05070e0f0604020703120f110c 61
    0xc1118200e0040c4070000c013240340e450248240c001d10420b00c5c3c030090346558103551691042e4005044c50380c1850503d0540c2083c0b08003c0c000c50028041030001025540030310341030080200941544640c40202c81d502c180000b040110442c0c2c0f40b440101002640340014101240310f03132410050241c101c2c0f07140e40903070360b0710071022507084020101282c0c207012054503807001000c44d2042c500121000700002c4d0407007080103909560000c42d03403401800042d42999950401d40d20b660704451686543c1c1040081107442c074420a40c0ca40305020f01d1000b1b000d1840c040680c03052141c81d50042507801c0d98045042c2054005480031200a11118404012900701e00c0c0780c403110203c03c0100c043c0d01c004003040b6090311420000142c40d82800c050b56000c23000c074644400d0142d00007404001504502070814081d011a90402c040e20052014241c8800c0305e00d8028410740d00380c54083c01e05841107004210501c00310b54861105c80c2d5082040320009040c14800704100d00510000800000412010640f6201010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 620388741 1250 620387491 620387513
    0x420190207120c05012a152729010e0402040609020a030f0f020a020c0603060d0c0e0403020f060c0301030b090c191a120c0d1404080903150702070b090a030c03 70
    0x402c1e20750100c40c00d0000003005500900d44140140340605c40881404100c034804149030500403400002841c2d000031030030020810324500940d03d0000030b40b54000821201041030361030301042d03483c070f880400a0051850702711038041c40344140d8000e030716020601350b50360340c0e00000040107940e100b11340d190b04055000c0c01408000c40071440440c0341c0107000c051300303800b070003122031138046d541c042c0002101d1170082014942018140a800c5500c490b5050002901d9500140c0544100b100c068a1460180f4000b494080c5005003007a40c0c0d00000b042c0040418036006807419641d1001c01900203135600031429140903118130887e03902c01d4800011140a0560314002400d8840040b940d00310f4241c1c203c1049a00e2003585021424128100001480748066001038240d1300b14030800810850030728420400c1c0b0300020394042c3c404c0b03c0c000911396200d10342001180c810460028a148a901d8800380280d2610228421001c02c2500010848a84c0e40c0d0904803201856000e2000500c0d65100d04215840311 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 620389991 1250 620388741 620388749
    0x100302010f08090616030212010603060e090a110d030c0512220b041e1e090506030c030a03081005030307050607020106320d06050f060420190207120c 66
    0x20841080c0740750080c80740c0941c074460b06002c401043c40c1e0710380e007808100c40003000d180ca004042d402c0c002d01c1340107180c04c4245802003400e994007240e01c50a003060f018140c0400b60004400d42e200c12180d600080003191580c003a454111422481c441240c01c1c25645c41801e5140100b05014645400b0302c4514003202410307482005d13880f0b01c002e13201035000841042400c3c1c05003081100041c002007000110b0050101e45507a000c20003400015030302d003001006a242d05400080c0c0c950401c5081c41080380c1803141c1c9174801e40440003010312030848000b0a8851183c0003000c0c0420800300c0014041030101c1103002c00030440503048a40c4c61225060007a210082174030a440154201100000d50f01400030061000000c0005442d2041d01c1d180041c80050034442100c981151252900c034011402d203200721441900340800c2002c6c1840c2030410801100e10340c4540440127502d08207040302202c111016a0700e03586403001504c403c41190340c000c0c1d00e407580e079502c01004460b15180010401c421001200122 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 620391241 1250 620389991 620389997
    0x5090105090f0c0a051002150117010c050304241b03020c06070e0a0b0d060e0901090501150617040f020303340b160e190302030c090615180910030201 66
    0x24002c21558691122401a8800da10110091040c402031900000c425002c0503a40101d40000290200e8a100d11100368801070511000c2d0341c0012040c2000e010343c1104918501e811441c51034a40c2e1005280b0080c408101c101c4811241e04481c07001c040d921040f400103160300030324280134002e0b20040c0690701c046040d0190f07008603c0420040c0d8000c03d500b004416000301112030b9503082c41c4c14900c4e6600103649840c6607546540d00010090001000c00d4000d0010000109203440982042801e46444480740d925036250501c04101c002e40c000d07a407079103080d5090484103241d1621f0900e4031000801242c041d5040c0000140c80544a040c400d01280e0100441c4a1950304500303000d40b0380c0d02c181c41e1003000d080d140450780003512082040411402010700360030000002405400447c8588442140e4036404105545080c015071800304018281a882200c0e018514500300e00807500345214020510308054010407684204941c7da03284800302c0c0d5001c1d240314503514211402d484036074018441030f404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 620392491 1250 620391241 620391253
    0x118060801020406090b03040302160609240e01050703020309060a03051806190203130c0308030a0b04050c070609031205040609021002150624040f0602060c0403030c0206090109090509010509 84
    0x51000e041c02a1401c54515807503501840c0d1801c501c5071a07079400148200d046008100080102980c511180c078081d01e042c2d5142600c46d41000300303100b0442100b2000020342d0302441511042c066004403200301c40f101c2884c0254a444140c03030140d245004408407154454400318900c0d0440d50b06502040c85080781d540440446a54004000c0d14dc03032064503d03140c414003402481c0e0710f049a40c2c0040d80c200251240500030700c80316407107100780390815800c112048000041030003409a628010070a04141c116030130480b5040810400b0310074496180000d04654440c400041454020600034401c0003000313405100a02d00b500d0810000c18a00c01308920071101c40400c1340d041c3e48000f8503030b8075804c0039881052068641000300554031168061034074000e601a0644910402140c024200408113030390f549401e681070920103814038500403c0001c00078028401000884d61100d45090302c55010b490360341e0f580c852440103d40001068000586880c104410701000703401c15400603216031208000e60700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 620393741 1250 620392491 620392499
    0x20709110a140a02060708060f04140411010306081015080d030c02060714030402041a03030703050d0e030928030c0305030705070603020408120904500c1b06011806 72
    0x10b06004100030b10b03005034000380008a0080c01021001e030400002000d40c5030310003800700000c00b9201940d0000c01d8090032a41031108111407004803c1862000742030030f110142c02d2414103913989084032042c80e4035948540f5039086070450090124050009441520381c0d05500e0b98000d806020040c41800042c4503010000c3d136450310542c400500741b07255841e0740e80386448035001c0101400c2107549040c50003504407054151a03500b0001002d045200fa1100341d251005035100304101c812009282280b6081040b1540d5036070b45880b84407107050000341220483c2d0703044045118030800d00740c00041407a00742d00c2d00402407100000160550502c03d074101d4100700d48a800841c00d0b800385100c0c02015500a8240c107000940d0940a42501301c8003030030000c1c52240d0399428282100303459a0305140c598218980c801000c1711203009420195180300c003d140c0c102011011218030b07030001c051003080c2e0b0000c288103082490030002a40181c0c505011294656103071032140c030320605114106080140752806c001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 620394991 1250 620393741 620393777
    0xb0102032b0504050a0c0801110414031606030b0909010b060703120e100e0606010903111509280b0c0303070807111507030f0b0603150d1709010e010c170a020709110a 73
    0x30b40311501c107482c1e2b003814a4a0880745d080101103a4007640740c065812078511903c10300d130251000780000d55000c100c41c107986043c802c1d10307030300030740300203140e9050241d07500b1305880c0c500860340500d61500d04100710f90f0705004c02400601445001904074003c115003c2c10b00029a000542a501680d0561307480d5242c000043d180c242d11803000400c0701044401d01c541514204d24640c0ca100c0355011110324046802c400100341e8061301d201d1031140005056400e812141c000c02e600054051000c1e918038114682c14840e542c1d0100421540800c0b24080c006442d0f14842c038502680b0743d18110407106840d08000c449160350008442c07460000389043d0f0f482003480054003412101030780103020149140c454001160010304c525844603089844100c010700051120f5130010620080d41506607156420103000410404814483d941007100807926800858175030560700d003019054400d51991070b80e4420080c0c3c01c280c41030380814189840c122030f04280c18014002001842001e682e0000c400c4031b00100d071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 620396241 1250 620394991 620395001
    0x22060e1e0d03050f0d020403081216090e041514060405330103021303060b010905150d0f0b100e1003020a050406030b0105040e0c0901030e010b0102032b0504050a0c0801 74
    0x610750081e1580c109070042405400200720414244c2c001e01d143c084108a00016070744982d000301c50341800065030b005544140c0e0b070303019002091001d544500e00030b8188014000051801a0b034442c080c4480840c041161050854441d043c0710001408401c611a521846007041102d50601440c1010005100d44000b032004114070000b412180c0c40000c2c0d1951a81e44074821000c0090616500700706152029820310080b1004510031100800c0700c0101d039000428040a41d441240107076000482c00a90b2500701003558402108074000240700c3c1200d0344084050850503ea043e000a42d0740c2d1645c0159501c00b0342410003500680c2c810981c034943c010f04034124810f0744c3c06a000560240000d100c0b5034071031340140c0404901450403500b042d0302c1c0c002c407201940701921422801000015803541550301070244500e000c2d0041e0080010b2008800040d480c1e00c9544034501903012100118400103680c0e080859044408030010046131800303280c07082d61940405416241b5040314500014411070500034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 620397491 1250 620396241 620396299
    0x7080c010f030f060e10180612020103150f09020d1409030901110703060617013c0905060f010e180d0c020103021b03041401020102160822060e 63
    0x541c40302441d039094110020255480c0d02a091921004001429040c2002640c0203039540600201d001d0302d00129102d900d40340f00351140c01282001c0040103400803040c40020300c00d80a09001c1038004e50614400c00641d070641086200300180c20740807c0264545d4007800007814a82c004020624006000203803c000c1100c60022540c003c200c0703520340d54420b080719654042120b00302c5083d2500d907078030403041c3c41d52500200c0700c10000c6900242d105000b40542d00140441000c43c0302c07480145a6805900d403d0701e03d00f00d80d5074181802e00c140301d5041d58400881300781c02c0400c0d180380742051070b5441003003403080c442d00003004012404664208190817540b415451340100500c00c4100780c1800761101558110f050303050541c203014089009000ca0300c4940c2903510280550380d69418081c1c03455002c2296403183d0304582c030500414000700c120041030300156403c040c40584803082020b25a410390150000c0000e481e07a4403900161183e0081c0ca4406810710032100780042075041d405100d403040d0b9a2a03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 620398741 1250 620397491 620397497
    0x70b0a0f170c0f070807051b101d0d0606080303013204051302180f1e180a080c0114010909030c0b040c0521060108060925030c12020307080c01 63
    0xc6500b1140c008000d090302c400c0544414102181c5450380c0196400003c019192508a102d161094038054044100400b50031940c3e50703001845654018802070000410041d000c855205502c2d280d902c1000048481e58440f005000140c0c0b03a10910b5200e401c00c0c45540000780043c0301d090348005184451311885000c0050314900001ca003810400a0800680031145040059001c000580c84100300342851040b0b08803e006141095100004030940050203002c0100c80500c0c5492600008204150008120301e00c0b100c41441500082d400c00d00050030041806070000b0308d441c001f407810740024070b05002000c1c02c500183c2e07031180c1d81400c0d0b600104005001030001410302002035601030140703400500400c5c2d00f501494451001c1200071203e248800a0003502003d480780c001030402525000d0080d038400f91030740303007841c02c0c1007075840201041740e291000c006100e242e10b03040c21450010003143c0019581002e10b940b0081021344121140d01030b0700901407250f01044c00c140c000f07000c110890040c0c0d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 620399991 1250 620398741 620398787
    0x15050c09060d020a090e0103060e1213030314041e08010507051305060703270302041d0d050a03020708030a051807150e0f10031b030c0503011214070b0a0f 68
    0x1072001002580040c0044c014444000030209101e080c800180707001c1c600c202c40004102c43c09210040c07406545600d0700d40043c2c0c00700011400195214035441c00c0b40d516040100801124826151041c01541c0245040440c03000f6490101c80400007c00110f81300400200080d444281e4200d1300c0b417083c560446c4c4845000b078020051410030400604800b402813404a51914452803580003d4407261007402c002210701d9414015843c044c450b002c05000103c143c82a003905000c040e070346902200071084188403010070100e005138041c1d0100e0701582c1e40300021035a2071600410140c002e00c0c0944490703204602409980c6e203980b000003491006e441702001d108031000c80c04081150102591816039802080040400c0c445481d42c03a4071400008ec0303500c0108030f5800800c85c4840008001101c2002c060a0869617420f403900070302141e05607120515800010b03103003410003280b00c403501c1e0344c0d1150314864028001981d49494000d86904040340c2c0d10315050550250301241c1c0d0750003141c20240c260401c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 620401241 1250 620399991 620400007
    0xa0503010c031d1603240608011a011707050c0312090d090b0c060a020d06080f03070209130b0c0702010306080f0f0609070e060f03010908120906010b1603030c11070315050c0906 78
    0x140d84800c081d042d8081d0003031b242c1c110f0a04001d0f00c403558885c4115079103038101000d03400032150304080150400e03c1c01c040011b109041d00c90505c00060401003d10800103400e0a001b917090080322281c004900f82c584250800805455949071030035400d03000180314401c0400c101705c2d600110380600c59048000d0009890341241c0c03d00039800300e0303d1803080700d0fa2020700040d40b8206000501000550b0301c041e58442c41503005010354100c0c01001040d003807501343c070104000380d442c0b000309802a10100040f5103403a040d2005900910183d00300144030310944c04a8120721000140902002e0b0400080d210203440d102082c1d541c4418602601038034819100014a40f41041d0020740a6104020000701d2041000c2e100c08606511100350b14a044152074204501c01600300b01250040ca03080141c1d0f4544448680da2145000c000d14000b010581c403801c80c261070303034850b07516070345807813526416a0403030b0f5903900c1c0c05200a2402d2800c0c2c2003803230034400050f00a03910310003039450560002c0c01240c540b07050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 620402491 1250 620401241 620401253
    0x7050318060c010606022a09010e13080412050f010204080a0305091f0c1a010303080c030a0b040c02030d05130519140105010902040e0f0714090a0503010c031d1603 72
    0x12035030603660414000c0c411008069024020f81e00101280e8014040c0800000c025280d01504c041c03013070289203240142051151150104c2604680150f41ea05a05803901c0440114000080902500c0030341d0101e0f01281802c1d000c44461f0040b445482201c0b004010031814900341e0007903110310100c2c0d030003002003c000700740100d000713100c2020010011081084401e080c14400c40000380b0b8003000400b40300c01541000f0802d400800031052844200741c60350301d10ba4000300407400017040d0307070407040300030021802042d0990409075003d00000c0c814841e030a85400b00964a404c1011440007050402c40030406040100c614484810b070010050001a415481400752960304107608035508020030010302d48500c0284102400b80c00091005a5150320b000790038114a0005400305001815840c140300740c2e00c2c0c00201030b01c00e00c403c1d03c280035107070510b0b00300140c501f103243e920887c0c0550030240c402504e40c3d4168004244003100a50556070790480c3c00c00190788031000b8542c840300440c140e6050000ca16 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 620403741 1250 620402491 620402527
    0x1302180904020a090c050d02030405241006031a12010c1d0306010608041416030c08010b370321050307080a0513051006060e06090604090b0d0c08030408070902070503 73
    0xa806d09017a40f03044071030b802d400101d80c0110381c261015040b1011301d5146e003056420540c610b0181181040c214100041070700c0352400d06110b000241561604903c08203100c031040d00e0004503005100c06c07003a0b008101454007030b1200720075442c0040c1241481080301092103007010041030002c0e004020340e81c20500251103948005d00203070b90404410902c1004d80c02c0410030f26000610480001031980c4c5180f8005070000c403103800503092039040c2191a101511000540000c00c0410000e40d00b464600b03440080303a4509041c1c01a45031002034201005014001e00490504400803509580d0034807030640485040c001600d001001407828400311b410407415401540d0000072381209145004001c0d1344080c54503240c00e4442040b2921541b0070091160000080c14a800080c1d5406280c104007000040302d42c171950189040c46560342940400e25100c00c40315000b002d60100348401c56039201c43d005582d0344c003c0d200e122828400c0d2480460380c90924002d0300c0801f61710500450600303005000354250f450b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 620404991 1250 620403741 620403761
    0x703030516020d020303030408190503090a0f060e1207020a060819020c01110a170a050118090804090905070e0c12060f220914060f1b04051302180904020a09 69
    0x14114080380e0f00560b5003400110700882c0b05403880d80d039850705035140000b44418031845000780b1105100b000b103494004140008019804045031000040c585403030b0340100a4002c0e5101144100841e588250350f0303002c0200340f1513000322980041e00e07607500012030341001c04a442d1076a01c1d24644048403503095070f8000d0550095500004601c8100da03e144041c16001040c1110014820b100c030401d000341c284608603000321095a00340701c5036051006100c1c18080344583c190b441c0c0e03a50303100f24007400a04000c0c1c4019001d800c00503c0241824200259604101e0103224541c1c9440c0c400714040381c09038003c0350f03a14043c125090509589035002c000c81803501c80c01550f082150784003081c0150000d00c226140e550030034080019014000d08110982d0b0190007801d0003250321000500c086900021402c030303800711520792151b01090110036000c0e41400340d680500c1d0081c54620048802010a402520000224141690000d4040030401050342c1c020745010b0f410480203c420700018150307030006034600e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 620406241 1250 620404991 620404999
    0xd03020304030f0c060806030708031e042303100c020c0111010906050705031501020102070f020f190b030411100f1101090f06050a1803272c09070303051602 69
    0x20a940e0f80321040920b211040449080d03584480610001d90802c4000b500070304280c0040c0380850400c1e43c0c0c01c1e640e103c0d0704020b9048100310345080140800b0b0138201c8000d00800100d100c4003007201020814800071650310781e0b1107400355060321b1208188900c986002c00081d64020061001c2c0a00103582c01041d01003045425500c0303c0501001c190980181c0b40140040c1d07440790341e81d152550024600305481d1902e10b04590041224102080c005072100010640440c2d08240309000400000e0250007180e10002103110003210010f16400c0d0b8002651040b030054240c0c2003140300c1c0340204000a0000c003140c10201c1d04151000d0340c214420140da10544d440303500001030824060300c4c2d01c0c90341106000c044401a0302d50003045109051401102076440307034140389000303a1f107a59401030216000825050f08242c000507041000c070700c1210a03940105554004007040c01c910405860300d22580002070a60301c580b40c404165141c0340000c0c0a01200c1c0c0659405081141d41c50083d040c1104a880907a40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 620407491 1250 620406241 620406247
    0x9060f04030c06330b13051908071404051b030f0c162003150109020c03070b07031a011e030509070503030c030a02010b0f0a0612090602030901140f04110d030203 71
    0x1040c05030b1080c07034941c8010b81c1013403c04510303000341002a801d850380052140100c00e0081029010342c4070080800d03584200c400140380d0340c038038a480580c09091b6014180038820707804009108122051460003552042d0b409210958030404d951002032a52000340c00301e001b0800000e00340103c01007115420401c51604249401d50241c040301f80304104440c143d8294100ea40249551501c07846201190f10f416005003140c01f0420480001c0c0b03c0c4144142030781103070009044004140c0038001c5810541e4885030b144424141004001c0081c410034042c0c0715000c40490b43c0100640c0034507a003103a081d1084501140c12240002c088000c0c0ca0040d00700c020a05c03504902080c190f60900207412a070004000540d110005e0020003829070700702d09420b602540551900081d69110514444155491820041d04d540318440150004081d0b041020341030b03602c08824800302d0340d010740005594050480319801d072603c03410b10381408c0140680d0003c0034200c1c0682c076044c0780e08110307102c0b0030203c0c040d00549007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 620408741 1250 620407491 620407511
    0x708011202040914070509010f0803161704180507031e0b0d0f0311070608040203070b0c2b030606111b12060103060c110a030c110a0503030408030c0609060f04030c06 73
    0x30361300c0c00c003100380201d0380028106100a041c540580c2c1c1c01089200755800a09290014084d141d02c1613082a60300c5614402850050094100d80c5040d204540015540d4840ea00da8114455085d50f6521403030341f504020129400c203200340200084003a800215000e55006041c140303000300103100c4001d4000121034100710108000706032440d6514001c0d11811100d5008036151f90820880d50410000d01c181c1d10305100140c0c030001400ca05454104d121682c4e509002458286003c031034400c10300c501c04000344804222001d480da00000000c0503107083c801c4030b0b100c00040d526420b406089d00740071707400210708180d007044540e005a01540702505601c2c441c0d10103000141403410036081030750710302d4440c442d1130350484d440f107080c0c500e941031600035103100002036400a18202d0701700c00c00340041850120300103480d0380d2402000c0c01004004d040707a41d40c40d6113a00322903c0303410003809102e82e40600c0d80041c81d280004141d071032151000020b004216602ca40d01036400003480b050039207910303a95a00c00d0f4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 620409991 1250 620408741 620408753
    0x606010305060f1c020420031b04120f02010e010203070803040210110a06090b130f110609040e10050c040b03040303020c0a06180506091204062d050301030606050907080112020409 79
    0x140139041c41800503080410b16005000a445c0411001d00884c00340404c0000c0c04803442c002e50350410301046c20040709010920314520980116005162800f000403035440400040c901d400812a1007a22100c1401074bd620041e602ca005900c40517108440400010340180352a003101c8020314041d0608106002921100c1e40c60440401401c42d4010340d9100200d05102c182c4c0111179114604048066078540c4a50303c202c00035686201c010241c111814100e481c41e6100c4056410311507000c0c0c000c200150141d9401542d031069030302e0b04201c2c0c40c60540400d1142c4848002c680540380a040090724645a65074201d000758030040c8945200e0003444c1700ca00000701c2c1c41c020f44018840218420480450605007941800740151107000242c2c450701a0303034454880751091b42c01f00c5055081118194070940c402d00c10701c0c02c2080100c0001c140031490326440507042000703103058a0060030204035080c0c554050001c00c2c5015220600405d50b0103004000c00b200043d1007415085c4041c0010585825a80e9a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 620411241 1250 620409991 620410009
    0x11a0f0d060f090f1e0e0705090a0903090503120405010c031b1101080f0712090507031221090b160c05060f0a0c03200c1c02060411120606010305060f 66
    0x12a184802009003002580034134050390b2104145510b0070080b003003400c0701c421310008110a0000c107968454407080520f100070312200f001010040c1049180b813a210750a603000308035220085010540f10800420517060014041486010380c0c0005403820f030500c0e006591a001d1050211704110080303065581840e200114505903074450100303078000b0196500050402d60009180d4a49140c0342c00c1003041656102c842c414004111707250000d1425920b08100e801e0800039040079064090041d000b04100e58000b400380820410300f1021800c22001d14404d000b543c2c840744010307040300c0551021804050b01c0300c5448004520505000c254407410b80c0d01c0c6400c1c00f800300d41c005024508402000118156406a00304440b2145010804454860107000c3c24484aa1641c0140a40401d81d0750400c41d00708030804200030b00da03e100108a91200000303503560b80c115011a803403071011411102d107080c0141c0b00090300060038081c2c80f150342d400004400170300c4000c15695100d070303c0d1922501d060300c1d10170003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 620412491 1250 620411241 620411249
    0x712050a1b170c0a050103051308181f02010507050331050d0806010f050903121e0301030501050106020c0a060f0f0509040612022b060c051201080a0c090203011a0f0d06 74
    0x2c3e14a00d20b40e0070810032a4000d660203941414208020808015a80301d030890030140d20000381a151901090100d0400215030200b603007010030030002c4a00c0d140300c021070307420031010356000380441da5801d082100c20b40000c2d9010f045280603000c1071800320300605036001e0fa12022181c1250011410385616290945903220000072445000500c000e40d44c0c0030391224041c55450820354600440200030039031f00e050414003c0002c0d140030034401c0d1140c0b005c0e41045070507010305010685a5840c0e0800b54024a82841100050f118400c00c030040c0d414184911804c90302992118a1645801c000a444443d20080b000e41040030030000c01e0001e9981e0721440020701a2040c0400d824440352050101c000c41c0c1800401c06249026141c4181c1d503102c9180f602c000b0351040011906500042040d01c20f030080e2044085960050000415017141c00034142500e6402440c18411941c0c0d903e001c2d400702d100c00e0049208400b5498110b02c51000320704001d00d806001d14054030701d80414250010201d40d0f482d04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 620413741 1250 620412491 620412493
    0x8031506190801080d0c0807080f03040506091005060a0303031a03031308060912030103020d1b09020304050115030203120c070b030702070611150703180609140712050a1b17 76
    0x1e4640902603004410038098208200140001c110310f040181a003081180020811540040c112003040240d10a440c403003084020140e03106d04082c41c0150725444216000070140c0300e440100c07903100e00203002d80350140401034030802203142142c81c110060070481618240d60907501110f050591000c10080041011603e00040c1480c148440c240c1003000c013908100c03043c0d21000c7d114000d41040011241105d40c101e44454840456184ca40c424030080350404010041010001030880115002103200300d1141e4000c020104054028544000017400042c0d015800000e01d0b0500e0084500100701c45104032003120041035654201822603030048602c00d005070017002041107a5a0403103c040c10240c0b5140207810003d40e060032161058030020807001c10540c0310440c42d07101c01c0302400d01d258125042070080c0080306050401110003024203009040d940305038100000e4541c040d0101c0c4200f2548400a014101c041d602c81810144c1c0c441421140e0001100c0c0001c0c403a4407007501c0445034000d800c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 620414991 1250 620413741 620413777
    0x307030905100b040b09160e010c060e1f05040c050909011416080c07080904110d0c09050a1e0e10081b13110306040c03020d060e010e06100c08031506 66
    0x981808285d075460300f2510b01910039481030004a421070f102421440015242c0f03003081c0501c0f500100c5450700c117003401400c0e041c50308003916a81c140c00329503524020700c9201001919003807103201c1004c4171000c40b0301030180c040012013030000c9e02e8805000b9070450f441d4000411050807111a11552030801e8840c44181e5100400c02902c01e0341080186a00441441c090740c2048950303152818203104000d034462103039a46030b100c21526a120b206803240c0040b0a01c040006034015040a4200d505a0286911500c8827082c0000e803581c07149071040301100e092040c001c0181c64228140c1181c1d201500150f0280074a00000c84d0940007006466003c00c13240149080c03020110080c010055100c0710344034143d604081161850342080c1c2c00f100d0704440c0503640010400c0240744103c00902078074440c454070301c1c00c0c400006060b0f068110010b0684909030096a941d450304c1e001c01a918080301c00d4200800c040a440e180400d0f0003102440e4440c10020800c0000240c40e00002d41d01d034003003c4a1407082e1021 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 620416241 1250 620414991 620415011
    0x20c0c030606030a030c0321020409021c0e03040608040c03080f1c091e140105090a0203100207050a260316110a02030606040e01020405041b0f0e15030703090510 71
    0x104031058100c2c800754060300264850741c0b402400a60003241c01b0b002d20141140141524100091807010001c1b0070000315141c40e1200340c000040d52107006600d000841a64000101c280240300d955541c01e004030066240c20310b0620182c503a442c0c014403e40351012403000010104001ca001000c5540e010000705a403018007580315036004202800c42c240342843e02e0154400140c0303002ca1880550b0888107404564041741c43c0c01100b40e5801c5400d402c51354202003c1c408030120018010081520031029914103c1d02c1d940e08104a00034244081e0075a0700c42005000820400131042034080020403030140c4420480c41e501c8981e0f481980d002003500030500c030000380258441206485d1441c9200034049000068001903590a00945010311513aa280c0e4001c00e00d500c00d6044400414005d0002d009407a404945129428500102c0401003544103125244007441001486c03011080104518408950121400c8042d00028400e4040c555150b81c400c0200d4420400214400c841400100b002822 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 620417491 1250 620416241 620416243
    0x5190207050d1a0c0324040b0a03030e030c0910121e030203131e031410090507030309060504060c1b0503161e182a0f090b040518060a09020c0c03 64
    0x300070602074604e0070a009100c0d01103c0640d000d40300003004032000c9056942c5a0000340100f60240c41140d0000451400008240d004030304844684021029a518446400248280610111121484880c80603000e00140c900c918542c486607000b80820340d81d48800111222700103042d180306901603031001c214604a940990b0b0800003401c111046407000c071510980404244040e800014000318801e080400c461500301302e0b240c900788a0700001e00c00b0046a04000e52101e805000a6000640b02800403619602032800c1f5402c0310701c3c2d999078614003940c548a9420b9100c004191007040c7d0b200410020346540e0070055503507200c24043d40c5881c03107407038500c030b06040c44031044066801440480b020018605008602e07030305074080001c085883ea201c0c804000c060754801d078540000c80c98081d0304981b40ea901c0350178581e2250241e240d10000325126824036089000b90310542e41d01011602c16000c1e040352070351025400c0100900307491071340f0b0f0700c0f00c0154090784c114072103082aa9004010744025854 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 620418741 1250 620417491 620417543
    0x1605120c3106050105030703110903030d09020f090103050622060203010b030a060e070c1b030b09060403020709051009021b070602100f0b011403071704140105060102060705190207050d 81
    0x14a00070704111852800700080d00d075001c001c10460074182c0d03c8449150040c04a4200c541001c0010700b5a980d030300002c48120003c0160b084142e01401c2c1c40803244240d402c10400c1c95040c0c07078002c002080c5c159101d00039112488013210f4000100440025414005540740c00990b010b01640b0003000d49910340003006030101c0782194040c07500c8412a00920140541111040300302c0c1e0b4011328914a40f00480da0f40e0300101c08182d00040c1781000b41e42c00c012200340040381f8907009520035400e03035455940e00c141c860260b843c00d441d44080c42c040d81c081005580c0081e8020b1a10311545040100c41518141e412070804c051644140b0168112042c000c1510841e803042e80500b5440c54002c0100752050750000b8200d10044d05050300d002000004610700e18020040310090380f4905001c014186000c1c81c041e0001c55403142e42074101d41c20203000c1a0158000706003244122841d56409003000003500143c5100f5010107030384402c2d400b030040040341e5030b29446150700f810350091030b000c1c2d6019492018034051403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 620419991 1250 620418741 620418829
    0x90411010806030115090209060c0d02010b1f080627070816030e1c11030a09091d0c090a0b060f0712110c040c0909050f060102010606021605120c 64
    0x64900801443d9406030080b04400361140d548005882310440c202156075031040200c5180140f00320301001030031990540000e2820003040c0d4841000c46041ca8128032100200c0350188045904000001e0482c02c0040404c1804114050315250750b1300606e9807240d880318156520320006060100b003249103140302d900c20b9583c3c40d03140783c1046031048241c03825480c0c1c3d801903011b50700304501911048040c1d105102c5003042c285e030401901e5403058903001c0508030780300c240300e240501418245c0c4001c88410384640e080711510b10001a2600002040070001807200040231442c2c015070710501ca02950715480040e086010304c0c01040f999401c03090511100c11a9000401c0c803c10415a040501d14000400c0c004c944c03038410381c0e011440c03003407100c0d00351244070b480c3d08501980b915003c00c2241c001c41d4542e070a40102c0c000c0e0000c00c070071a1035032412621221480101c020011101e03108000c0e03814507070308919000b0110303000d4031b000803012070010351950404503e0180351560f860740d0159424904810301081 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 620421241 1250 620419991 620419993
    0x607050109050d1106010e0603070f09060f0e1314030c031b16060f030911040f0b011706060f1c020f0c070b03250c050f0706020105060a05151809041101080603 70
    0x8200c81242d1303281d5805050094050400100000c01da083d101040214040c0c00804401c2c060f00740c458000070001e100501c100048500c1415000540c0c88031310215078014030040c82810441100b41c3c69012007070b00311021914162004010030703a0465070a102525103500c5802140000b00d000e00101850565205c50b20042c9441980c030400c1150b411034400c1404800605021a811405040088807111407020454000d8280b450341c2c034110b0070b40ea00a06007510240c2300c01d01c1c844210403a000d11101c00303d4499411403010440e00c8402102c0704040c0500408108034a607070301e110301714818260382000e00c100d00542c4000c9040e980301c0c0801c1c013542c405450041005800c5107440c1d81c001581c003200c5140b6490014036400c800398003a114084c0308e82c0240e08002202c1c410070462602950341c00c030504c0b40100651a200c04190189015800304045a40c020900e02c10032048080c0240d4583c0042c00303070800c03003400a03000d900c90b444900b1050710440c02805112881400080003414402e0001c0c021442 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 620422491 1250 620421241 620421257
    0x603021309020f09130f0c05030612010638070b01051302180d02010e0306160e1c031119050102030403030c0c0f1106130b04080c030d0c0b13020607050109050d 70
    0x402d106460940b0b84e0b5400071504081d409000a00c1c1c00300030241c00c1c1d00b021170142080003401c140c41e00130b00158040c400c04d07510b007a40340d09100840d0b822140c031400354800602d040e00c8101e004d4003515101b401c442c3d4200e200b603485000c1c0c094551142c0d601240f0212151410718004004a180c0041134245a015141095241044017404c200071540315211180c0701d035418660788002d42e4812803080180200240c2120003030304000c2c00c0400f090312a81e40400004840514004c002d05014191040290100b0103400707041050382d1f41a10440d5407541e8141c40751050005a01540c82c482258085641c001c000059036401e05040040550340090b11070f106121b60b04c442c250005025442c42801c803608840741e1041d140341c0d1400503c0a10035008031010901c5405000300d0007000080041003281c01140460741c40c0e0740d02ca0300703040c3c4035100804100081080d034150680420341c9a40000d03404080d850700f801056519900003007254100c5041a102a07640704180e404005040000580c1e1032524142005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 620423741 1250 620422491 620422507
    0x170901091a010602102c01050610020f07053312010e0c03060d030e04020f0301051c050d110106030614060114160f060f05130b0f100b0306120304060302130902 70
    0x59500701c011702c20481156184003206012080318408144620341d001a4280500030340200f901070300d41900c0240c4688504a0070002d420f00001e60f1052500e810405044000d180600300310010480c1c000c03903080030030904a480408006011500058071198540f2525500e03642010110503a0580086181021410a011800540005880d40728804944c0304490407201d160454145142e1520243c0060020549071440d1688501035816110107440c080b06501d8a00498492902941c002902a4202e0009813255074403500c55003a15983d00c400204540f540c07552554225501d004010a82e140e03000c0a0121942c2c2c40001d0a140c068034100a80c10035000000203880503c501c02d00400d041e200380300903c1045440e801c0f40b103042c43c041d101001907143c171143c9000314045910040300d10a9004001440754a50b50300d4641c0503107035000b0603075105820001000483da0000d00348070750069042c140b110322900c0410007000500690341c1c0c05070b02d03020310910041504030241c102091080c01440b11031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 620424991 1250 620423741 620423743
    0x20913030f0810140118170c043602030610060e01090b0d090203160b03010510050304030806210a03090611030418050c0409020d0203040209091603030f170901091a010602 75
    0x10f800d8401c07410101010720703502001640d12601c08207143c9400390080c1000107040001e1590240200310071020746654014004c104004c8074420b8031809100800500300e03049a0040c02c1c00c0c8200143d200d480c0f440801c20540000349084000c0b01c65040c029040c3d131041c41010780c0580721614801e800c0c200b543c010b5043c280200e201d4024901003441d250f6540c44604150759040248140400070307549010409a1100d41644540c2d10900410317009460b4048110313000c51143c2c0c00c0301e10440e0540d6072090181c40702c0d02005403440700c07586c000203000c116011070843d0241c180402441e4900c25250203903420710300080684203015400b004c1d01582c00070303c0100052488810704640703040d58060005040c0c1d4038902d82e81e6580c01180c1000007043d02c00b10720b50151684560085015600880d01d9512070380d6844d0981d50b40d4000b005200c00d106107000000c0001138000c2c48020f088004606014159410981506892010846420341070f69100c512200c180600d8846641c601c01d0706000301e075019070601e07e001e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 620426241 1250 620424991 620425021
    0x318010b0d021020010204080c15030a050c040905100f0f180c051c020d0b0a0b091005091201051806010807060e1c0302060a0f021c18020913030f08 65
    0xc0d005054943d0303042440c13481141490684a0300d0015201c0000d007109440303000b504070303000d92101442080a0200700c2e250004041d030b91810604a014910341e50040c00b00301415003e00100420f03075081c070000c1035a41841c01070902c94101c00c084070919514025086015a0182c0c1c0f00c510820f403031401c01d000d2103d0065411480c40c3c0354040c00724064180c118201c92a00c500c20614104501e080e0904104011940042514904140c1c0a01c01b900000080154200c0035125002084004000408207810284284010003002e0300f4030350308040c00403020844052074484080e26a9540700c0420030b039642c0150012044004040081c0300e15030415040b6030740c0d07901601483c814400c0c0c400741c0303869a5071450740609000a44242001407000b6615002c2d5039134206881100c825802e080c51082c42191034800d880c01c0b50621b44058543e8003a400e101c1000380b1040c844008441c1405c609c88001d030b2a001e5419000d5000448801e15100c0d042c00d005284082c4070484104100c09902485a140044140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 620427491 1250 620426241 620426243
    0x1505040515011b0f0f030f0201020a0906030509010f020c0307030305090a0c0608090703050a03050315030a08030604020f04031a061801050d02013f060905040c140d0501110318010b0d 80
    0x10401e00e00a5041c0015220340680f00925001200c0c49800802a0841c0c088410701e2180c0c480c10304503d040103084c1e00340c1c000c40e58100c0c0001c2c8485001c000d4940f10b42c1106801070211000040c146490060301030a0764400d00c00041c85171700c0000c00c0020594184101640417075000003501507048035035510340d080070710f5104050810203010041102c0e9081400312100540e401011610307805150328024086810403103074040d40007007102d00013229050108940181e01c2e400500640f8640e90a0104402900f10b03031402d10304e1203000d01c80400054132035400c0b203100c1002840070915a241130410816002580843e290740e60301a100104110380b1380c40c0c01d0031945982424518140e00c01d004a403d24405000d4141000410005448200703020900c036000140e001c4076414400a6124000242030312001c1c0c40050100b481c19008000c100028220000c00000013001d6001401301340d00d426003503407415003044860f00d400000b8482d80328050301050001c44115002800207000701c1d00041d01002d04094 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 620428741 1250 620427491 620427497
    0x16200604261c051e041b050105030603060c030a0908070515131509060906022803090c0e180a0b15090f16121e050c130b0f09040609150504051501 64
    0x404100b0385000e40d81041d000b10724000c0100f0031450207040841c980c1c0d1b003500d407241c01e02c02000c001003440c1d48610103ea2154402500510440d160580c100c030a81c2d000800c0303185155034915283c40020000c80c000c140260040009104800f0401c880c0e8564a001815000d840105e80d052400010501703402004494032070300c40082c103500c1900342103000d8180d0a000404541c40000c400440e80c000c07204151718074004500c1c10360320100d050410381c05c071102050040d1409010102c200900101002050380c04684591b46100e000010040c1c246407802040084803014910000c2080184480c4045031201c002100ca01c60103080150340c3c10300c00304020780700311090780c0c01c1100581c0240c090210a01b10343c4456808208024803132601d10f0100409031980160329007480d0108400c6a40718064524080e100c504008017a407a102c44150f40b03070301c0b48a49030001001070100f02920b990340d202d0f0300006c0c810b004000c201c0c41c00c00007410541c06d2141d04102c0c03080d440c10060002c485640c140d0000d40f40c90a007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 620429991 1250 620428741 620428751
    0x1e0e06040924030c36140609130b0411100504090b060a0e240309030915041512061e0510080712090503300f16200604261c 54
    0x4a01700c28181c82d01c0742d01040714181401804156030b85548001040c0a034030300c040556032218004c02c0303070004007501d00042603680c8a82c000c0c0442d070448021600644200000b298840800c4082011804091402404a0404a41044034000314000d00320040c0c81101c01134608a10710001401e094544c00317099005858403440d90704003c00281c2c180c120030b0341e0303d00280c1d16072501c3c8590b42e5480d4000c00c2070900440f44480c45004c9070140d5810b07681030f0b400300b40085207a40c400e0b0b4400c480c0715903144256100c543d10f4210025160a0341c4c0302c2090000110045500080d091000340072803011455401004c10140408206145034403092050b400d101101012455a1131400d10610754081e41000d0398184223001040c914040c480e9407003001082d4013507503481c016600c54000340000b92003180d4400c10445202e2040c002c2500c1030102d100f0714010040c03c1a02503021000c00e07403600200f102c0480303200551078031152038104003c000414080c040c2040e289841c0d1007400000c6c0d08210301d941404065225 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 620431241 1250 620429991 620430029
    0x1060516050106090203010f0501030905120c030706061202010e0102150a0506040b090a020304020a1502060f19090c0e1503070302100512070302030f01060f1e0e06040924030c 77
    0x210042550380d50024001d21400d515030a80703a000354000c1c842c400844602c1c1e44009815402401170081850300400a001055010808805150302c40c40c9201141e000412124002500a115800103445585c2c041403511b042c0c0e200140000100c092964103542c050031040b003280700980c078881d0303200d0345100b000714160700c1c0e00d004075014084919030b49a01460b20b10407c0342000e2154041c520a034001c0782d03e50b96850341c803000240c1490a041100e001a000040002c41580c80c2c2407045800010f0107032041140d0030040103110443d100307a9021101510b20440c02c000003c800e141090f009070500b240c2a50700114000040c0d500d60140c0b000a001d15810710008502c140070354103907448000780d80c840c07011610701088024000e610844d20740625151f00c2002003001441118101d80c14a02c640720011600c405100590701e610007000c0c42800c002482400a02640b41c1c1d2001e08010b0041030340128446000c90101d11b00b228a5510f01680b444030240e041000c0b9400e40a07030b03021100e071700c510502c4140c04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 620432491 1250 620431241 620431267
    0xa061404020309030a030914150a05010f050901031101051e090f10020a1502041d10080a08040b090d0204020a120b031b010c051c0e030f0c24160f0b0f040b010605 71
    0x170242d50710323030140210700074400717012404501e0511403200100c080003240c0c0c03a0006170b0641c0751980141d030b0b00b005294005000148111500e8410302d5814100542014030035142850380c2c9601c0b01078491051030104800582e820150f0316218594011a840b810031400d00c00002e5851480b108042c000704a04500796101004c00d81c102ca000c1d01e10702c4d0384010000c8841c150800f00020541d810505e00098000000d243c903000f18820201580c81494549000c1c5004912407031600212a220f03403060424000400680e2240700a284502858940d815054402d4003504115280d503c82035020b07400451001c4000c5c03054005401355a2400d0130072043d101481e061203480c0951840445890f44604000b83d41441d81182c1e0166080e1421006c8584e8410a0500f8688802c401e2000340d0704914454461100641418100006914501800c40c100807010310724035250800c1307200945400980c000041c09020070020110386c04003944042c4c2c1ca1034106651460001c550501c0703020704200b400315042003002c0c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 620433741 1250 620432491 620432513
    0x51906020906041710020415050c0f01090623010f2c040b010521061b13031a0105010f0f0c02012607110705010c080c01090b0a061404020309030a0309 66
    0x251150f600c83d0f8a5840c000503084c1c603501a0b00c030314400d80920105035000c42c0200d6003540c0c6201c0c08001d24036000c4000fa0b4041c1c1001c40a0080390145440f41e5102990902c07a580d4602d000300c1020480e60031480c42c0d02c10716070a40011100c0d803417803107006100b90b201481c610021154004d403210300c150b285c040c0b44100c800000d0552042101c00c8801c1c04107200c0d08a5445040e503100b104c0c001c01040030075209010540c1a0400001c05130407c8000480c510454514114000443c0e0440703441d060503003c500d5032a07040c17508202d5a031a038000550080c3d0350f08942d01409400c0a08040484850055019083c1004410441d0420600c01c586004591140f484642c4000100c40310101c1c032050b00540d00e0000310101c40c0c41e0001070381620020102c44000404c901240c02c182c5503c4c100030b50702d4a9090240c2e0040201c00301030364950f1044800109940301080c4985421000011001d0520340315220780c13440400c010344118014000d00100c0d200c08804ca036581d195074180001e003c5078a150800e00c00b4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 620434991 1250 620433741 620433757
    0x11202060918190207020d030c0516060503100602030a02030d0b06090d1202100c0c0b150a030302070905010803040302211507020102070c050a0b1b1213031208010305190602 76
    0x221007603141402e5001000400380241c4060105666010001800e10200c3c0140792002e540651640300043c0070034051030780c016190b4000c005407081c2c900b90502000c0f05001650207400014030010401c10700e10602c00c0b20001401480c80558544146184001d42d68000d00c501c00c000c842d5507110b107550a80c3d0f91411262010805450400c5903606828003228030700d500082c2401501a9650f813444c103440602c1041c403108900d44907010059150f032071700c00d08040001d20402810a5031129400c4554a2a6150307008501c00da0040600e030f81440c4040d010341e8010380c07046400350b105000034001640d95039820064881905481170504840400d46894941c820038210310f403c602c1d40a11050f00c1d0b06400800b205409100002040c580c4c60050013410045807240901240301030150b070010b002d01395030342c0e4504110082200c1034819142c806469507400000c0c0c540300086159000c1041104228018614031007905007841c403503245449282d112008060a102482400c1344e81404002d2158151519a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 620436241 1250 620434991 620434999
    0x40510050d0c032309100915110304150b090115360b0c0a080714030a021e03090a05040f1103040b0108070b03130f0c2c0705070b0112020609 62
    0x4140d50441c00380051022852008608400c0e00200303901c0e6100d50002c9005d00d1401c0c000b0007140500304040c2000303000424080300c91010402c10701c2807041e8240980c40341510b01045640c1da0f030074940b425483c4004041200d09a29060100705405951005645411504281014100c03040c5411007222034041400c900300c951240c0c220300018500b007441c119103001160314014031005e604c1d20710508480c0519020411581d000805100011b484000680016031041d00080408440d406503d42075800110b4842c0060380141c5140000c8400b0810242110aa01010b10703c1d208008002c9a45882d00e4081e00c0e004c0c98803074407560080c895070340c01807420f03914a032045038503400c0030314001402e0002885881058800c1c5040840d84994000440740200b00100040702c8500300c5585481d2080c000316004c0d181840030b6040042c02c2c0e009480e0440131a0741c11410201c020116590300e07540d820001e0f00c01400c111080c0101f1000442e64440d40e4156084020f0721252110303188001022803154800c50340e08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 620437491 1250 620436241 620436251
    0x20d090509063c120a02060d09050d02060601030c030b010f08100506040305010e060c0a080f040c0905040501020304050d05030105010225051801030c0603050c16020d080c0c12030f040510050d 84
    0x1c4000d288010600b103c0542c1e008103589400d041006910811401c81c41016008a51602d00500d080001401000c06040b40414001c03100d032515820503500d4902a80942c11a80070000a903916129499441d80342d0f003000c10654526000080c0220400080d240074400c100300811f00d94056110044010100103000c1c0b40e80f103841e032600d14040d01131070403512081d114200204200c0050b080030754070b44800036502c5141f1940c650130041000c0c440544140c407403e018620100342280c0754040d07540300d607025074005070366400c02d45845440c000c0310140c568108082480180881c6e030340415000c03150304201ca62901a480c0e030012031400d4400c80da014a41c00060500d14018100306400302d1812a4011140e0b079000d030350f03642030950580c2c0088034480c0c80420200710710700700304004201018403d40058030381303000c2c08a1036450188683c4905a0700c1150b0340820000f01d810720b014031002c4044641b02000e1800d0203131000000b010303801180601441650700d0300e5100d038441d00c241e0940340b600e0001c2d441401 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 620438741 1250 620437491 620437549
    0x4051210060b0a021203090c012604060b13090201050a030c140a0f0908061608040305070b0a020d0b0609060714150a0209120c1f0504090921020d09050906 68
    0x103070030f40c4010311060150241007040040710b581c90007a46d12965601c800f900c041000750004640c10f0148141c0c10012112a180c04460102110b04280c031880c0f00e0301000500398041c1c1c0c100804014100d080030030719818038274043c00503644641a41d456454600300850004018541910351110041071382807032000104c1e8014440b68001040500c1e0031180e241c14100c1910303414070384d0b120741c0121121980e2054200341e80e031a0724402c1e58010f6029009180083c03c1c001c1c555141410400d042d44c69098aa40210f40703d5259810743c460402c03a0282180e1407403a0108900c0030611a0242c1d2501410251800000b6001804144808080070245581400251402240da07000a41040000d64003515060001c04104100058011085e002c01000407002c0d030015081441240241e5040078100030040c0030000704800d0034002c11031100d00c00d400e640013010f03216400080f29407140e000c0d2400c42d4010000546829000705548090b1402038502866a036180c2001c5801c18940c01100381c0b4441540010705 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 620439991 1250 620438741 620438759
    0x206030a0c1b0b040314220602070b0a0c02040b061c0905010501050609030604110a0b0f070b2a03041e050f0d0f020d0c05010b0a06081009060b0405121006 68
    0xc1001258079203000c6141034000b07104011842c0307040103200f501c010001c100400c2c020110102200400301b203c603d40311041004044503081c100c59000f1003500c0300070a00c03581c1d8041c40240302810180031000d0814241e284000d020780f13201e010182c041c550f2000b10000c551a00811035152100200390b426001558000070710003045400300035541540b0307007400810702c0e1a000b011240c50900050040640b030f19261540302400000c03031101da80c04041e03e000041c2d00c05042000e40118500c060f001c907220009402c00c060006401801000d100600304d0b50500c210600420b44940401d181100a03180d030f41d41d01d0a42a03528110324130f120004402d49803101008000210341060054178801c1d00c6182d07043d41c41c25140124816200c00141c0c011a032078810007441403904002c0240203400104070f111094010600300300b519041500002c0b001002c100201d2007141d8031303400510380480100240c61804011080600940c02800e10403040c20025012541007007003440d5160444000070041c06640d043c00c0c0e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 620441241 1250 620439991 620440001
    0x310060f03200f01032f071b03031e050403060510090c030c05041712071109010f0b070b040602120906070e03060421050d06062c010f080603010204030206030a 70
    0x49415900e15100c1c262600c012502c907848644000e0481d82d28141c244005401402c0b072146107a0100d2286952100d20000e1030f9040300400b61040d044030f81d219032905242001c008000b4191440b0070703c0d0034080002030b620611510800d18119034401404400c040c00b1a2540b280e940003818040c10281881104000010000c3c1103690341d40b4204440603142c0d10680c00d4030340c0d03540640302054051000700400c40be02c0d0000c14548000e0015501c40c49081440c0c94200c3c1c100c401c0590380ca0481901114242c00c00d5854180580021400c0f030303000b149010000c4403148100c5074001e2001c10b0613004a0100020764065494501301130540c80c403a0300e4000380490b50b403078046441c0400903218025998060801090041c0030303541001100c0000e0070328908540708498005400010007908000d0780004140500c5180058202580c072010170031600885400e4183d801c01d0314103a1803e0402c10000a41e030010312200301101c007402c2156503079807802e00090081c000c40d40040d411060010402c190700c0103507481 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 620442491 1250 620441241 620441243
    0xd050c0c01020703090e061c0209070e04020715050c0c0d03020f09030a03030903031808070f020d150b131b0311041a040512030a1403101a0306030d02010e0705010e0310060f03 77
    0x83d8000d50b66844d0800c45140e03050601c81ea41c144500f060040581000b101c407072f81c005e1042c100342d10000382c418041412640203d4040d80c150100d9406001c3d10540c81c000c09170041c0030f15180600703004880c00c0d0103459600164800c0c0c10b0603400100e000c070b00070480d41900d0000310000d003034404e075245609020700070707103d50b1004400107072400810b1180c0440c501030300c1003a01c4e00010350505121160b541c8108415040ba026a80f02021100c034400003032500c0c00c0e000c0118401100454144a00c40504c00c0c550f1824580700a080d0a0102c500c1104030070b42100c43d282d004601d0086511002120a40407038400c9401807031000e0031103480114000b51b80c400400c101d0304150350300d8465048003055a41c80340a8050138074005a4001c0010885400010140d40c0180d0055200c00000b0740c3e0b06c441c1050903003030500180f4104008401c11202d8036047c0b00c000089000341c0001c0c403625403c24030294a448480c080c4038140300070003000005c681c904204000018158203020000c2544940b40107040c041603201c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 620443741 1250 620442491 620442509
    0x70b070f060608060106050a110106050a03050a110303030f041209030210092912070905090411030f0a0b0c0a09090c050c0d0302091804240c09080a080d050c0c0102070309 75
    0x280009510b00d00191245c102c0d9095602c0504008040c2c8045403404401c01e40b1401c2c41d901d4030310200d80c0b651003260110080d80b09500030a20b280c0d581c03515134203041c03940070b515100b90818401c00040e113040f4070780d042e4440d5000c5e48440000c803140d801601d116a16800c0039401251101031541d8503600081c2002c1561161042110311040d4a1544604002806408200c4c03080a2082e88002d04400c16029005041801c1c031444241d1114013044508100700c409480303280d6010080008c81c14144031000903214004003030141c540903601e030300001010290581c02c0f01000010250290f40c031035240d80000c2d20701d106042c88074401c0420010040c1d0069400500e17140944d444202905019108848a4240c003900190701100941c00411b00520002c10603501c040d540c55001d58801c0d0700754100d2a0424074107100080094011000a04550341604102c186600610000000ca40035106491382c0c52110b401c046801ea80c0e00c0b108600c907014840d10746c0080c0d0300101d00c0c5c404041d00081d400c0144ca0b8418 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 620444991 1250 620443741 620443751
    0x30319050a030b030a0f081605100b0f01170612011d01050609060105130e040201030f09030f120c0503040f02120703081207031e0c05190507020307300302070b070f06 73
    0xc0540326000758100900061103150041c0005143c00003030710f0b41618000a2120042c1c4c85e0301c69030305202c04107030b070b09180b4bc0d03036501c400220b8680145140014042807900d1040101403002e00010300d00083c0c80c4134401d04c6c400a41d0326680b4801d4206400700d0a2651445216002003900c0501030701c4103458561240740005c0000b003882d41b19805540c00c00d101c00c06440081803400c4644d41d8007450181080c1d041540303911207109840810300034203060300c4c402d03030760075840c12001c5400811880200c03854880031410310104c8030300a0381c003809a81d0040d80104c00001040000d10000b280140840001001405440c400100344182c10024003846c3c40c1241d4201c0a41e55120000c0b01102c0c0401000c005020030920001c11455990b030003040b006485040561600312034082c0c480000801c1d40d03d10000030030008140d011824144111001802d0f4880600710540224102841c841ca041031003810340900344074444e050600c00c04c4a100145503180e07540e9550b6020b4107111648030300c0d01405840702c074200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 620446241 1250 620444991 620445011
    0xa02160f1208040201050a0f140414091005030c090c0c01050106080a050709060c0b060d2001090b0a0806061c0207060f0507020a0804170f0106060c0b070c0804050609030319050a03 79
    0x29844040c803c941c142c0d41d4516041d0b00e002c0542d550001016500c04002e109106007105081d034500820181282d050750b4141c0b000c05804102440300700030540c1c001c044040404101640b800962a500350000b1140c800580c2e5440035070190310b000d6945039480542c240000050960f40040d200c43c040e108014091082d956440c1c2c080c0c41d07000380c622070200010140344021006c106501c03030864108000030000c1c1c0c581040741d11094002400c0b048000741c40b040c000741080d40b660704980c00c040244203041c01d043c03c0c140b40c003002400341000200307460301440002503840b2100940405a442c020000d13030085485807440e00b043c0000b004050318034020705140c000880da401c1c4c00000c50000340f95219000340e280c2400e0001401c107605c102c5485117045d1090744100346c0012000c0c051365026007041d545281200e54241001c0383c4c1401c01a080206215010143d080031549090442c1c050b102c090340c5042c0d0b100e802d81d000c82c1c030358071960411202d05c86400a5040f1104e038000002d150a1000f41d809000c02e8500c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 620447491 1250 620446241 620446247
    0x4020a090203040803010603020a03021201062106180b0a080a051006140307090c1119060615050a030c0e031009150236030d17100501020d080a02160f12 67
    0x60f03402400c841c10610040180c2803180e0020411480149000741c01e043d407511a00c103c3c0802a0041c0c40850325911240010500000c40c6410040c4145000d10100d85040f10041d080c480e00340d810000d003921044030800e961100c2e241840105035a004903090000c26041c05034a610844020302d40c1d039400c0490001c0c00400740c1d50502c40a140c0100580744840c6454088401030501c2c60140080c44003260480700012024440c440644100c0f82031590f400320170f4038007001100e080d6002800d840e1180c9605c105915444025102c0c1d888060400150443d9508002e6a00301c9501d200c0982c58414920020700c015401d0300a04520b510512152106181849010040c0d010f40c84a0000c045003520500c40c6e041c10382c20300b00348080c015807151151800300402013401d1500082010001c00c2203901003a01600c00156495400f000d20104070303841504180c0001d455040d4061070004125102c070104008448c42d0381202d60640141c258a0740d000c030185040d060400c4a00b4007942c0d2052254101c101380340c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 620448741 1250 620447491 620447497
    0x903050615190b090d02130c03020403120f090311031c0f1119081303051e070906030209161107290909040b190c08040203010e0c013204060804020a0902 67
    0x41c0800030542003907a80d83c18000b40c4850b918007a641f054824560f02078902480c425140c0165007507a026941e641181841409046040f00013810880c0003401402c8a613800f54844040e0b1b907004c051781540198060000c1e1400e4000924004251030125903014800c0e0007940105080c1840d890381d80c0801109155581c8544c000491400103880c0c4000560000f00341c1030040005502071680c034004079440e038031200e28003540501c0190000002540d0b62402c003c003000010000c004000e011b200150a65012501880010f06104a441c00a08803480d5050042f0350403000c9001c503404880c110340c2d4450b11040b06007032150400d03039084020f00200c10242c4960742195010200540052882d403100c2c0c1c1c420125050007400490500e442400320400e0f50000c1c0038038801092140d5134a4030a0515004241c2100c0180d8210203040d40088050301c0b569810075900108008011060210620285d18602199030a800740d0480c02000080114516070085ca015004074025280217000540b18078902d0220301c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 620449991 1250 620448741 620448749
    0xc1103010509032203080a1808060705270d150c020111071205040b030403050d0e0604030c0b06150c010f0e0307080405130b1c030f1716090305061519 66
    0x740041003032250701130741c080d41c50404c01002c4c103620311440c0c1d0300d48500d802e07a0000800500021098446418440740c1c9580303800c0030341040b038043d2107107040202e0040c6c918031031405610308070b0300014520401d26980b0184403607286c0c006496600046001c0c54001d00c500140f14010414a1610005924241c03051081ea000544900802840c0c180729844928454039807543c54000c100c01000042800c010341c4010f18007851080c0c0f105516030000300c49940c1501d030786143ea95600e40c0030300f0401c004280d102201120440d00846400402d031110004507403d416001204640101c0c0020350b242050300540c000582d00402c0241000b00e520f500c100507407203105058015001c00ca0038481404145410414201004000d450028440317240002113417152a441c2000709003594040c880c1070905401c03c0f050f20300c941e298600741c01034281b078102702241814082c1050304050510600242c100340688503a0021303503080703400c0728200c0c44d1214681e1081403018403400c0c051060b115040704010f89403650841a2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 620451241 1250 620449991 620449993
    0x3060f0415091a04170d0605011e02060a1a030a1b1202090a11041802070b09010b01050f0d020705030c030d0b0a0b0a0305071e02150f0907030210140a0c1103010509 72
    0x3d00440d40b03201a0904028000b40c42c80e0080207074003072910180c00000e2181d602d40c0d01c40402c0d5940b8210002d080300d00203144c0b64542090f0501c440b0841c0341d0100e01d06610407401c0707100040305c19415244840303080e01010700a8151103424400c50a000484c1030581120b0309181261030071a80750b018401a14a2502c80203400c01c0140c8041a0f4101446c0c0100340c011068001140c10550f0b940d221005071140041d00c00002540020407809000d204040b040d07015242000030b111542c2c41c07600092040c45141406011442c0100f1000380c214000e404a910f2150004201d94071507904010b000c0c1c40303074040038590212504d04030f80d000c810b040003c1e2010480701d480886604003c9086800d40c050300c4001d010004104280a40341e8880c50030101041d90b004460b8010802509800346105a40001500d00101140103200304640c2200c002494001d0380e5041c1c5844207103004e84801500c0a09010760326012411f400314081c0d602c00d40c4030b4420507000b4055040d040075040e099090600700c03402a1407a0000d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 620452491 1250 620451241 620451263
    0x109020705060609090a0507030803040308072c0a09020409062102093103051306080112030e0d1a04060516120e07090906020409050714090d0c0503060f041509 70
    0x39140000401d98018005d905440814680382e94803400c0c001c0f240c004655444010080c0300c24550301c1644181d02a6050401d8100311105400080765409106000d689407216040704110700d46a40d98041c0052101d200159156911007a01001815482c014807603400001e0408007940702030700344854a0300380c019000d00e040f901d030034014000e414403036000c010058050603410045451444410600076000c2da031855201c0b401503008111444141d403011040200c0e800c0140145820140c2d1107000380c2e07160034401100a0b5050124a022400c0400981000d04003118000003e50650045206070b00c43d034402c00966945070301a84108115440c00d400103a5049500400000740d40c1c001e04081403600120342c101550b035a00d85094a01001c82101c0854001c1800c02041203280110340d0810702605010308984040e5080300101d005030000d0903c1004401c0c0c0c810144000d01d603802015000150580f541454000fa10b80c081d002d09540840c3e80b4081201c1009031008140b0407003038902c0e840204200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 620453741 1250 620452491 620452501
    0x40326030a0f0212090a0c1d010b1809040606030b0f04210909020703090305061303170c040b0c0f12041203030f0b040912020f011b111c0309020405010902070506 71
    0x1d1001e034486202035a400c100c0c40020f181310001c2184560f6070f00004045d4810b1510340f0baa02c1469a911004024109076668032803080c100b000d8506403525054816110b0100d103076404200d10141c0040c0e50045400403e1001303000160300f149041d640200c9001101c0e86810881c000c401802b1540640441d114002007550200001c00310702e6085140c1c83c201d040541c60b042c40e5000c0780c0c000d9500303c010074180c101c20000c000b414411580c0c06a041e100f07427601a200303030710081e1201d0359010480070350b1a08040001c400307170100300070742d0041c048000d80c09864012020500351b446d581030064100c01d2107601c82c00140401050101c90030785000e06240e580d1011603580540107044c0c498515080c49442e042800d0040d145c500c103001009000d0554640d0039094000d0203401c1c0f00000c0210748081e41880d00c8490441c100c2821002c60500e5480d00c4034404900510150509441c14a2130080c03032080300080c0000e0b80d1680020541c2802140c00300202d99840c03160200300d100c1d660700208982c00842c0014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 620454991 1250 620453741 620453761
    0x4151509080325030c0b0a0902030c030304030308160c120309050c0a0501020c130603020d0c050909030f0a08060102030c010f0c18080a02010507031707200307050a110d05030c0304032603 82
    0x32000f6442420f20190250340c69031222a4240304a43e101141c540d1004108198941000704042c800c005801031450182180c0b8001d0001344020116a6041d02003440100d419200340d031803000c0580c001c050300c030644000c2c0c0070040c0949403218080e9524450040001e89030304d4180d81c20030480d07005030010301024400d8801d105002446a102c03451150355104000701584500c4c0c00c00108030f204d80e014440040c2444d0400c13034011005415100349500510820350040d032000119141907050342000c08a55070b8141c0100d00e148920504100c26508040e021038941341d030740e0061102c2e10810703110485022a50004102091014826100381e68045600d0b400503500410003030001501a281002000021082c5910200e1090703070040001004000700e500442c4000f108005000e15820107503140c103031507450340741d619202d8140142c503404881c82000c0305c590312009440d4180354090166920380e200d240030346440c0c0d04140710a665500442c0c1126102d04101c0c041200c0ca5103074550418110b4940301c841e1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 620456241 1250 620454991 620455057
    0x11060709170f010207060e190c1e030213050402010e060906030c0c031b07060e0607050c12030c01060f030507060309030503070806040906020309101a010509060702041515090803 78
    0x40740034011291800c40040c4207000800c40c0782d016080210318090300c610301c00d180c003200c0d032800005040d41c6000c0c100081c3ca0702d28100d003181c850b881440c02414024820040c0e52001d80d0000b544009000407a13040c441c520b40003148260f000743c03038424241d0b000c9014044544a10820703d80d00107010000182c10551040241c0000300401c4112420010800702c3c1e40d20141c0250748608455000c40030030010950b01040da21229801910704500303000c01551010307510560710300d0282c40b582c0d15038241c010f00b410420035618201440c00080c06102d80e107108405110a107800259824003521801152580c0039008d240780300c2c0d60550b602c5140d5902d044044a1808014058a5115880304101d40100b00e1500286015002d0348005c0c2020349001d444090880c1c1411441c032120800702103000c04240c1e00702050743c03000d4600b503c0440d521501440040c00401003510301c0c0c0b081c1d03040100c0c0402c2d02d01c00c00d0059040a802030b1204070320302c0d484681c00e03545d9019803204034500000702608211114000b80003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 620457491 1250 620456241 620456279
    0x50f09070e092503050f07090e0118030305060d020415080f010e0304151106010f08010c0e0102100902011e030507020d0e0d03050901032003150a050a060c1505070206060111060709 79
    0x30390b00c040e105c5d600c0a05000e42c945c50102c0983c080300041c4005061482801692030505001b0031048250b1b2062410310400740380c0240c241555500090142d4440b02a4602e64a03401070040104580f12802c0c02804200c0c0e0103110302d01e206400d280c0348042030520942c0e8040000800450916142c1040444425892907901041041003003c801c4a0802008050b0181c83c0c5484a82c10440c100b510582c215a0308620400410400d4000d040342c507600891045580300c2d21b8680414641681c0c00142c9403202c41d41625049440f560811000040e819844a03010340403e500f80c0f4000c96010000300c03084425603080e558040c1d81c050b904800240158000c1c20843c0041c100410f2520f5484000c500c0140004908140708000008020009098010100790080c04881144256080c403006c120201940d020b10014400401c500c1f4051005420300c2410000001c0d2041c881440d24910081d15040b054074450b000c0340141c440d845e200440414803504c20701c402e64690300090700c0d0608107142d070060011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 620458741 1250 620457491 620457553
    0x91413050307050f030306011b1a0a06051203220b09040b15121015020705040203070908060405030904320402011812020901090506010f03020c10050f09070e09 70
    0x10070880090001c1c0b280c013066594140240d07440b0300e8200c001402030b44a000c0700000c1e8845402d80600007841c4c08810440c008000b00c5008020798034140c4000050407140c0081e07500c591200c40c0b81d070941400100521003401c030055007210511000c40306020070300725402a4400400c06004101440c186a440f400e80305e44014400c440e0b0300d26132000d00100e83d1240340314910f82c248074070810080341046010300000304681100c0751130311f00302688001e46034850b07802034600c6907400001142da01c40c4500450030103040d02c5420794245041510b00035a403a8403502c0e185014a040550482540001d481401d0340c07485400b0b010403012040081c090310030100240120305212242410a55040c1d22201d214003030400c030300003541b00e0b61480c0104126048140c2c8032032080b90030101017110f00c2c0d902c00084508181c4600b03000da215503401c0e580303500745502c06208580147c82c040421880f14101455140609080c0090345c0030503444149841d103003181120101c5240d8003007000b03402601109011810094901300b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 620459991 1250 620458741 620458747
    0x60112082b0903030b030303270a05030a0914100801030615170d0e0301021306180308120105011e080c0d020c07120c0f030c0e07020f0a1b0914130503 66
    0x1c10080041404400189441c568481d20042019094482d150003074500310f0085003145012008008071900c0301e030b0000b110f145030400501580c602086180009540031069a07141d03400d03100001e2182020b032140400c2d1814031026100350703003010322a02103080d00755901c2d805a41e0071502c8880140c004800a0342d40c140007104001007002084603450240682003028112900d0141001045607042954051082e4410003d0070f0801d21b800d0b0884080700d1460501a1074515a004919403004031a070028010400014030401c0c0300320300c0284035059903400d1701c1d207144180304007684558840390303407400101184110001c1540d007800e07e0081e1a240c0c078120000b41c0b518005081c55800d00c403141d840020027840f00b909680030000078030200009004c003449a20442172540c1c480d054001110300c13802c00c45103118400305040714803d1115007851111a011280104002d14007580c048103d41007600c03e0500f2144041041d000900401c81e02103140c00c1c240b100c035152000c100408011558003101e140c4410 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 620461241 1250 620459991 620460037
    0x50c030f0f13060801080d09081b0d0533041a060301110f0a140343080702060c0f04050f06190507020a0f080a060e0c03030408010f0e06011208 63
    0x1d01411003d040f56a4442d405540b403c0321440c50015490030007000d0107543c0d001072100c0c81c00001d000c20304015811149001020031004112850749454000d00540241c11074981200000545204cc28685a401d214a003011446804c6441403d4070b00910044240c204118040031041901d60060801400018100325581000003903a0013504280805d40c004102c1078012030b00a14101c42100240c030041d403441c42d0800c005503081c8c80703122140003074240400035154000e0002c00c056100d4640b4250301d80c1c244a09103405801258211101c2c0014400c4a001400d26115801900d00e103058040103281414204801c00000d02c480c40c22060300446c0c18461303600c850184080640c401015602d5055a8580f580140300c081d002580050068902c420070411030a40002010400d95810590014620b035003060380c1403c0665a0704c100f44d0510001c20b000c184e400040d480041031004a11041140f4040f042c00345407070b2102481404036000440224401003161a80144000509005400c4040280c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 620462491 1250 620461241 620461267
    0x7031104081b03010c090303050703080c1b0120040807060804060e150405010b19030219030804060e1206090c0105070510020a0509042f0706020d0905060f0106050c030f0f 75
    0x4850002e01d16008590540d140c904081c4036800d2445850314101d92003c1c1141c401602c107200c0d40304001c08000d64900010b1035006054181c8407159030380c4d102412200528502c02d0301030400d140c10540c8403035009c4c40b000480010b410841703046460000150040030b10300354042e03034900b200810613941151a1240c59036107030302c1406980f402009003a00c2e100c60b81054240300b030855a80f010114080c40c0180003c0c4101603d851840303086a5045600b101049200d00c62218242c01c1d6610042640c2c1021401045103504030791041c001d08415229101200803610181d541d81c10140c6403800640c1040165404651050005040b40d9014500b102c03941002242224200da00c0440d1860004001144c080000c0c509401501c803900c4d4622002c2d50b56103565102c0e1040041c0f829402512260005120310402403260161488480c03480000c002101290034000d85642c01100c030707034045010007030000c03408034081c1d410b5a2034488044000c40c14001c0700c880220560707201c0c04070490300000c10310907a210808 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 620463741 1250 620462491 620462503
    0x10f14031903021e07030c0b0a03020913060929010f18290a020d03020a020c03011505030105060d080d02030a0b09280209010518040908030903070b01050909060703110408 75
    0xc4241c0c000c21000000e00d4082c00c0501d04d4603c80c1c84185c11400b810000b14403800c007490305551000404680d502c5001409400138812203450326080070521000b119100040d9000104a900b0183c3c244139013242d4107407291010485c020b0410f000685007144070310340d5120740c448124445890916620702c400c600105402030415030300c0745242800c0b400d118441c03081d900c908410a0400e0741c1d4101c0c00c0c007070605400fa450f203681b40101010545d01080701c0350b60030b100f04840c60701c0400140080058071442810204036405038001c0714080d60801011030381509100214030038968104240d5410200c0d4070b02648065070001d411b00740e030a074a4817000c01c07056070781c0c2e20380c43d02072512504901400c000100722241c8119900c2d4070050075510501c55150780340d802008072003a42e038141d1907411500200b43c0018000307201e01840a004c901c1c002c000c00100000010003003049501805040505a0340c9908000c000e4034210748a4a040d00036601185000f8002d4024103886207400c20014245901c6516040c5441 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 620464991 1250 620463741 620463743
    0x801020307030b060301080a0f061e0203160f08010603051302100201020901020c04180308090708070824070507420b100f1d150301031208010f140319 66
    0x1950000600c0304140d010f00c190800c400782501c91604661426010b5a201c6581480103045801420850020004241c0c400d402c1c28510461060507604050030020094100303c0b00d004513010b2071030660004038000c1c2d1110b2601c0250341d40341ca680d85e00f404421005401c02030401000b42a003410200c00680e282c031700d20610010b0f15400180c48500d02000240740c06680c0c3c0750203018600c1c000e140b444900400c0441d400164040c201280103441c0c4c20766440c60014294042d80300c40c0520080422204c90219049036603196607010b5100034030100040e41201c0001b95000c1002c00c008000c04000608603010528007040c0650020301c18041007802d242d80e602c942c45060070201503454002d00f01a080b40314010303031000181d510200d42d004030507020305091408240f010500448200b04100c480380810444062840680304011000c00c03510700d16081d41080c04111140c1c1c4003503a05038280d5104140903412a083c8035444070703030586848007200c112500070b2001034050081c407901c10503026012120854207 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 620466241 1250 620464991 620464993
    0x1a1323041104060506030a0207050f070303051e03010524090405010e01090c1b08220312090503060709051903060216061b0207150504030f150e12030f070509030708 72
    0x1031800346041c0400c8011990918416840c003c828000da4413204103403503201b10102d800590b240418102103192041741000e0000d2403144c070401204260380075018180d071034000c10344601100030354440c0c0c42607800240030b9950404840c140c48901e10828a100c000b14407110344c4060303c2c0182c404003060603150309030015080000724034010015500d66210308a12100700b86090303612140302090150108030600c0000d059a0004602e41d0100c5403e4000c44030300346030004005d00000e5a03882d1403030181900070078200110b007503050006001d08010401d0f500c1140f248d0781e040350883c00c1034104600c40e280901e00c5201d00001d144080700161040c801414440c1c169081d180390540a440c10b18252102e0f00310302c9000b04010704441e80100d03000a002c2c4255401c00c52100b041054000007180c550103198400303000411010f04040c1031003581345141501e00f1180c2d1060140b00d0048100980d41e0300b054072182d10200080000402c10240324061542011040c600b1510700020b003070002c3c0c540035180d0800849c0d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 620467491 1250 620466241 620466311
    0x906090b1806190e150f0409020a0513020c06040609020a0f05010e1002100908130503070303051209100908030403180609031b08070305032d09042003070c11041a13 72
    0x2e5403820390b00000040d2000c40e802c0c46030f04822750210381c66240901c2128068440459800d00780340640d01034942c41c4205100b210300a00d020305000025003014001a809144003d41c04200d0024181c405c41c02e681041c0c440e8070b0f25186e45d030140100042089420300441c01214401d190303da460780240081140140303034450701c40144840300d20459483c0c2d40036600ca684130320010000260003c060710401050100d0b01c0c4915604c403a90541004214405012104d15140100e010012060007450107940643e036265108501240c288007514514040c0c4000b24503030640800001d0310001c11a10b802a03504580c3c01c403c4d994a42d098680350340c0e0b4000701d40503000810480200e66441c0301605001040304d190860101c6c00010950062240b1b10109025a4031041d0b14841100022a03c443c0024502c1425940345050240284130b109850001c48d941404800b15001520341801a100000213000fa400d03c0c450b008000c010030202400b0711419030686419419818503280c01075000302c42400c1e901995 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 620468741 1250 620467491 620467531
    0x30a0207080304120f0507050301050c1908010303020303190608030f0a1b03120e011d0c10020a0b1501020a0c24050c1023010906090b1806190e 63
    0x820040d06811405159000b40030801c52200b03207940aa2000d500480c92078140e0059080c41410403c0c6500641c1d0950308000078003000010040040611110307001c03462401d00b040340412101d1000a00c4094010791042c40401d0b410040122003010100c0c0d2002d0025425517075480e041e00719002406951880380002c584176100760b42180c5401d00c0060f0b0040f039031039003c44130b95000d4000310014002d000c070325a581e2239000d40d240d025408056483c503d5240c110745c040140c03121a40d54200c3c000024045e10100050b0310b403840c00040c00010265004a0262056a031003590024050b51a1012030441c0f05105104010485081065029000100d80c40806d0704040d04131100b90305408170004100301040001d070142c00000f051411409140c25000f0802040b0341c03507140d00341010340b4520b040c110124000040c68800b41c1c1d10013001c4407071000c828462040040100b01149100d0488a280ca442c188009404c500c5c10803406031008030080f002d5020f40e51584021040361400712840c502c441e808500baa8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 620469991 1250 620468741 620468743
    0x111031c050612070e0c0d1119020f1b090601030b0d060501210f0b06010509040c0915030603020a060f0c060204270e03090607020a03060c0206041b05011e09080708030a02 75
    0xf503c400741c4500401c4d240e0702d0210b6085010304010000560f080c0003042500c41d001036504080f80b59000d42d48413070745840c0b0066018036091210311030440580300d01616841c0c800380100b4021a039981d111446070450324550244165039000401481c10980d50711300e01c3c1f4069480422414103940940b100041b036604001290940c00c001c6010f44c0c1040c110b516046001400d16415140d80540c0240d50b14050740346c14005854500410865941c00781c200440c400f0100e5220584100721072240301074a180000056040d0200d402a02020390001e180400a100c0700b401042442e55100840c40c1048202c10141c403444100d07081500320501408915145004600f01800e1003c15803024040030400959114030f000c0d0340e44680c2000314014100031480708250b42d0b402400d200290f0300302c2d0003800b0704440400020340380e240444085070580d10245007061425580c5000300280c800607192800041c0036000300c407240c1d201003080e1004200c55514040760b6990207001e41c800510800f0020340d100e05a0240213 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 620471241 1250 620469991 620470009
    0x3110607081312020133050406060e060a0203040e0f07080f0708060f0f090f0f0a0b0901140d05010908040512010212060d0201111b040b04140103020111031c0506 71
    0x801c0100c03a8040c031802064218982c144968050004518100040d10a84c00351090480380c408816515100c1000d41702c0d440c0e601003c11080c000c0c00b07401d0070f03110010041161590300408000034201c07074045802d804c009000b020311000a004580c201541c81c840c40742010001c036540380f400003001d0300348088075411059458001c40204608101c0c0d14141c3c000511030040200400e05c141a404000c6c850b42c0c9450601120600340602561010b1410500d803446a05003544c028400c00340d004009415000c079842105820400204046101d910306280d104034040414012540142410503100c0001c07801d110f04004107104405007601d862070801003001c803c400c0c00128465034010000d0102e85109107003151341c08142151000d0780e4041314001220095551103040d00c03140300d10840b8100c7d041e900da00c001c51100e81200d081c41180280c40500064030380c43ca04e4025203050480c01400158003c40c00410031113070711000c40303040034400d929a00d02c1d01d564040781c11035295070300140f0070941031080710 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 620472491 1250 620471241 620471251
    0x60221102103081b040803030f15010206010803070602030a0605180a050a02090a120809091f090903050a0c02031c080a0605030609100b0a09050702100c080c180418031106 75
    0x10116001d007192400b0f0019000141040050300720f112403100c0000000b41601e0107410b0000480c1c1d128a407001201082110030346102e40b0b04641c50021003000d603c0052494181e07081d16010718184001585d45501075000607194082c001d8aa00000c030741a02c0d140790f07071804485032070b588012604015041004803200901882c0c2114010440440d85454005200c4212624403001514128050516000c207024581f4901d0340032280d2014000483c85c2030f404445040083d03c44150703040d590342c00040460303d60750380042c0803c4d03040c003070041320900413039808480500280c295402c40c260540454002e0b4042a05d000229085209214a030400b61254802401c0145c0045c0540e080c620317103403560340074070780c03180b0f04002d03241c402c82d92283c5c0350005080700a00c402c81f000d000c681814200a0740b210540112a0707003140c50b0071114400940f18040300790059044814051070602410583c101d10207840c0c0300e503500551a240c0c0401c0c0399541c12013048400d0b004c4d6440c0f90b005811490203d00744400501 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 620473741 1250 620472491 620472539
    0x60d2f121e0c0102030f072d0b0c13030b1f08010e07080c0a27141f032012072c060603070503040203010e0d0e010f031806022110 57
    0x80c42040ba0740c0001c103c40318140740003070681d100c40d458500007140d10030350741c0342542c1c040c4000b56150b203004201140140743c078880e0114018541d80c001044601e030140ca442002051000c000c1000480ea00c100380710b41104404151000c1f10405501814420805500010340c90395110302c5035012000030b10115002d045800040c00c480707902400040d68581e251302552542440661581150f0a05004858001d4000340c5051240c19034004692848075400c484011710300e0b82280108145101c0d41040310b040c0d9134451028000081c0044c9400341da00c1140c0c0f01d080e040707401009910007610b400c0140c41c000740040a50125102090707800c0c100c0b4140c15600c545c1c174000071081400442d80e03e070b03001e483e80641649407864903591580002405001712070b68910b0940624403074019100d90190705841c80d00001e03200d1400100c2d142100310200d0320700e81c0e00010360500422001c000070b21140c0040910302d402c1010403003109080e0b00b80c10b000010a598a65194600c000c0c108618101085041c04880700b0035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 620474991 1250 620473741 620473753
    0xf0106050a081b0a030c0e15040504020d0b130b04141203070f05030618100609080a0201080a0504031e180b0a08041502130b0304050105060d2f121e 65
    0x440595078450500d110403c1d0510a0124240701d51200d04003d0002c54102c41110700880c3d482c802407900200030b0710350b1418000c0b417850b18065030900d400f0751030050354082c2c15000d03046a2500c035075525034406022104443d82009403480440d20034090709010ba40161410389038035000d41d81032841d01c2020020040200300174001c001440e40c0101d15100240d0260030f05035642c0e6640c00014001d40c0c240140d80854403c0c00303040c00340e1407000f20114000d17560380742ca400400c25150184e003683d4060142c0300900242503080011440e548540015800c40e12a00700100c1036030b0200841412030711200286000101c1700807031030200341140e1900e0b5008000c80d94100340f500c0c0d05014018003e6200900107082108038076080360855160398100d0301c03540c82404202c541e0b1920b074004070744182d00a56023503c40c2c1d03003481d0119082d440d16110f0800b18a9010441c100ca0f220036102018041e0398049000e14500380c01080352050b515075a01c51009591820050101d074840d25600d008800e00005400d4a20303400a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 620476241 1250 620474991 620474999
    0x50a050f13020604030206040623090a051903060203070503090c06041d060a0305030d0204050a0806010e01050d051002030a02030f0a0903020c010309141002040e3102030c0d050f0106050a 82
    0x10864003070300705a0308661040382205600210702548103d6200a4001e140000e00141881e44083c0070142d00950214040d0000c0404e2a0b0400900900c078400b030b8040401c131810030180c900039081c0040441720355480300004d50f8a40398402240c00403200c43c0c001c80d10000401120810610400030600d03403c6550700d04003414480905079411001d40300c00c42c01c011070404071340c1c107990b05004500210703408000c80c0d648005d452040b00c065003007845510700a130100200861002e90204000341a01d0002a02d1040d80e842c1604010030307800c01540584040c0a00c69000c07140c0c01f95800214424504150096920708015402c8540c90000800d032607006450501d031600000e50105468400b16000d18011900e1035090802c4451040c485181d50340c9440398940001d021038150b00500200e41805100c0030456459602c001072210a03028800ca07110901c0e80440e4091400b10004281e560001d004c441500e01d403070000c10603051142c1c03030558550b4060b1091046a100034012030004d00b03010307a1b0300c070001403030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 620477491 1250 620476241 620476261
    0x60717010302061c0c030e210d0213030c090c110c031b012d17011212050d0c080412031a04050402031504080408010c110307031110020708030a050a05 66
    0x60000921508000404520144d540c0b01c241c04075211400c0100509159001d0280040001c03681c058040d01484c8400c1641e000079140912200c81d184a0184ca010b6441010720000d50041e1010454030f411a20080049180311061300c0c0541544000044e9501e5800e1015040711000e04040085078081d0400068540700800c0d080041c034205d9600c0c000c00030b2a040140c4890841c0780c008050300311044203203403000020801800301c40c56580c03a10202406005203620b101c450034040c400318035181441c0c080000d00d2040d030044002c07102d0714006040910500140c03094030700d141d8465001500410601c014032219490b82c102c1c020550800308980c005418801e260228105403a0344180c1ea14000602075440500c12242803544070ba40b41102c0c0e00d440d05e44082150441e0040c21225841c0050040700c0c00e01403071380307840403d000b45c0c0103500b45001c43c3ea088030050380175443c2c40880c0c014034440d2400e100c00d0340060400e0714410503002c1e44901d0200d0b88082101e40040c102d01c0058100024454040c403 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 620478741 1250 620477491 620477537
    0x40b0a030f0b1008030c0a140705030a030e150a030b0406210f110307061701051009090509071809060b030a1e030507170a1e2a0204060e0106020607 65
    0x2621501c6224150f94818544a000f0159070100540c2d000000d11200030700c05c042000040e00384a07122416007410700c0188a607540b00c05020f81034040e4800c0c80308501082c000c6103502c0c0180d0005005c021400c10321004524103070040351905002c6a12801c0c01c84551600740100e2001e4090480c14403124000d105490b96816070010014004440c4414017409200416010341c10480002d001c4550311581c400c8014000701065119018030b08048d4004186850659000c480320b40c880d5031b94030384042c2820000310061501400651151043c58800203aa40b0b01d1115a0f10320070016400180a090f182000d0040d1800480103038401d800100181d00061558407501c400102c0303c01d481c0844a6480c43c0c141d90031300c18800048e16060958010b2040044804010003003060203a80d0340e420b00000c00c0c415110361900217502c001007605d00c08819603620050b40c55900d03a001d20718060829000a8011404480761034001c1344150b81ca40d0300502c02260100515508640180ba10480018601c100011200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 620479991 1250 620478741 620478743
    0x60e0d0c0b01150e0d0b060a0801020403080301030816020915040f110f0a050d0501180e0d1413050607080d0c0f05191223010504020c030415200c040b0a030f 69
    0x21403540c00f072003919100307040030355602d8809001e04201c642d503810008440d00040300d110348160301d10000440c803014180280c030308890740004020300b0350742541d8a070490740d081541d0780780c1c0f1f80c205100410023507030711510703500c4c01030b28849045090b90850100780801e403500d0610301c112203814440301100300c81205040b0746441c1c11007c00c0d0782c0c0b01c0b41203d4085916105407408a20805d0401c1c00118000c030104900034042149c19a00304000d01403002c03c0368484603d80300841c04214076000c80a2801f10180c02000742002c2081302500054442c03000401c2c03500b00b01d900346c4030900003240581c201641440382c208007258908002c0752545203040000d2282c454044050000400060400d0a481c000d801851030429000424800070300d04400c5000c0300440c079014501040500400081c80341040d10858000c51441c80c055450030f410080300c181d02208400c01a030810040382a2410320641d001c03a00414600200060070310100340c9001c000c1603a1000c1c02d814460300c1c80160800011b900761001c40303001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 620481241 1250 620479991 620480009
    0xf02070c17030c160602010b0909030304060902060c0a031119020d140304090905010f0b100c06021b0102070c060f1b1101120c17360c0d060e0d0c0b01 66
    0x100c9000c08042c1c11801511800f1210348680302c01041500c1c5080032020035504190300800000000000f00b09001d0000d50340c05920350010800b007070104920b90401350f14140080e000a180090300704080786410040e59041d8006000102c109095a03c00c5c06200c0c440840055100c811800640024100903002c8800820000454501300740b90603050043d10b0090008240401c101a0300c1d00300300b800707000710100b8914420314003140164980b40c514450b01115000d0b80e907007555000141ea072603000b584802d1007090720400112484112000c01d00050140900c0b90070448641440c1400103007204400c0d44441043c040307082905005072100d6019200269000500c94285030395000c0140e0310450386502d0007203490b00b130281e51000d031074100d28801e010400c2506221400e82d203c0d490a00c6010000700152441c1807800281c01404030200d28015400940009540c030032021a000a0351185614100b00e0715151103840a103c064400c0c4100104444d040c103110384403841d541e4854061070300500580c070304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 620482491 1250 620481241 620481269
    0x312010b0c03031f0e04110306090609030a0c060f061d100b1603110d1d03061005040b0a0b030f01031e1505090c1809061008070302010f030b040504060605040f02070c 73
    0x81d80c11340c88620f0f001002513040040c640c0c02d007414521114010101424028496040440c0001c480019400e20455165018604210f5058822601c051003160180d460a44402d038080701401144150030080004543c040384e01003050300c1c0740c10bc1c81c000801c0200c10301450102048004541c400300c40304c4004900d010480c0f851640350642e000028002c60907120b00c035018180c4940364010540c03403a22108109249000c0101d0790400d90741c1c1c002120050a101d041c402d0812482c20140c0040d500b50700002c0c031b50007140341c40d1031959195810441e0108a02502d010042051180511080d044d411901e03401d0301d0000240c2c0c0f12016032499a070780034140c8030ba882c070000710103041c20b01c14141504d00040034480e440b00e40310449600c20400b81c840007182e01480c004150000003801a000c12144420060840c5074503640054035a8042104e0b40d00600d9102e500c086803940d564820781c1e100300d100b03c0c5d00040746800c10381840f080f21901c525004d41e00703104103c0e07040800c0d0700a100c14115000c500d008a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 620483741 1250 620482491 620482531
    0x1803090311120105180105100f03080a0e0d05030706320c0408030f0904060609151b020a030b240310050a090609050d0f0302040b03061314090312010b0c0303 69
    0x50b190503504071200d980d518007424840c1c40d03030040a4131078503281554020701281d159440c201003107401c244942007502c10051410000100c40c01c0c007034980c050741818240b00c0072504001041202142940c210307801c3e040050f0301d50802c00a482130340030b081c01a80d40b450025010100948500040da0075481640403000d0019504094040c201c401030050542600d44441c0405c0c00e1403407076006654814455800d100021400301d200c2c103450403c4401d42500b10014064405041d203070720100720040c1002d00380926000015845200e0544003c40c451181502545080038007204201e140408a03e2110074001403035115540001d4401030300c035034010000a164880c2c010500c0280040b5100074030302341c103166480c4c0903c02d0108046051012513156201c1000b00144111700324455805a074541742c00034004903105041042e460300d243c5074898000a108518400c15984500c411244480207600000ea086514003561103040d004280300d6090785d0a011003001e005d91a404003c04168643d0b40302c0761820 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 620484991 1250 620483741 620483749
    0x1912062d020d1b030e0105150f0d06090503040e01080c040e0d050903071703040e070507050303011424090f060408150601051c0630150e0106090b03011803090311 71
    0x44501c15402010b845142e0f28014010304000110b884003540380c50300181003069081d9045402503401400031003001c00701010400710b92580081075038426a200c0000b40050000c00003030020f0119881c0342001c035031505140c5840c0100c46102d0601840c00c000c03284801c610000398514140c07006083c41e80e155180b240119107401c1c844d60200c42c0c00b6010200c1d0682c902404030040c0256052401012501d0740c0302a02a2480c0c032500e64000c01c16402000100000c41266084c4450f484000f04103800d80800b100c100008100143ca04201031680013a010603203140941c4203042081060350701c9424586040a01c07600c642004580869100310100010303030b1a88104101ea80880c802d4aa80c410600b604001e0300080203207016030311522142135408107c40d00296182a40324201e000c041510002640c0e4000c0c0c00c810b0340300004801500d80801c0100d0800c00c4c001d01c00900400d0324006aa0340c0d00700c0c201400d42d00300c11210303600c095448881002180d072000da984140e07a0800120b0001c1d80e0000041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 620486241 1250 620484991 620485001
    0x1503020904050a021201051801030219030f0614090c03030706020c031e1c110a0e030c10021605010305070f08090709110d051006020c09061912062d020d 67
    0x180d02514050412440c96800d5026040000340301c505e039505a80ca9030107101c9900c400101780345a8001c2c00b401040180f4145a04c0d100382c000690003804100d50300d030f60700f09221800c441c046070035a80341c45002e6171440207032004d6503000c5075220040409032003041c04640c4a10070043c001c4c0100341c0004200481038410000c030f811000210807012409054150b000c11241c004e03900200c13800100c8201c8195100c554007640101c1183c84801e2460714543c0c00c02a00d8090703040c503041d600750060340c4015919558040c914418040c8640203440109903001d082c000c8030015400544c18145010203200030180c0c040c030340990440303003401d201069850f0450700d1403510801d82e000d03240203410b043e002c0b00341d6000c001c003420359030310041020300641e200e1a040e9905600103024840050b40481c00c460074505c1d03c041c81c182c0001c030260007101d8429001c614640c410286030815180e40c0c210041003400c11880d8814002080800d40801c0010121070803071502c44100d081b1041e5641e0740202c3c1500c01c0071106d03480 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 620487491 1250 620486241 620486257
    0x1090b03060a2c0f031c050f061e0d06060807050a0915050904260a110c01120b04140901020c1203041101120e0d0f12060312140d1a101107150302 64
    0x1203944807040c41c1b9006034030000100305e40c1a00e60a010200b905a4010311f80180150001072003880e40d004400761503001c4180400d08540e01c04c045a20f00070100d441807040c080031b0804c55015110b02400c160501c1110001507002d010b08500c0c102c1100301c1084042400c0058072421541c4586686690a04040c1800d5034007000e501c032a58004c0702581c0301081001001c2ca651070b6110b9001c03005080b146151500f04113403040c0d01143c000203043c0c0c1c10303210941c050051f484009100042e4030446c071910001c4403d040b80d080800780e50009101c001e440301081001d07e040c10b1303030351541e10710316003a9034020380d16081002060502c60440800b12030f0b40301e280c010550f052044000c03038149601142d4010722070014003600ca400f04801610f9514000c8480c000c940981c1d80040c01c1002c41c0342403140c00c48a03011100034609814070f0074030900020075510b001e0020f10b207070003240c11015030300010104918064541422818403100c4000780d0322802c40481c10000722000c079550103800310381c400400c2d4040d10138240 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 620488741 1250 620487491 620487493
    0xf0306021c05100303140306010f030b031e0106050901050603010b07060207170c0601030c120302120912070e0106081006020a03080406150b070501230114030a080301090b03060a2c0f 80
    0x300110f5400d0300c01c22038100ca0181e5202076541c401416030065521060b200213002825082c01c02000b03900a4010301500c0c0000342c00c80d10074103400d9a40c10074421040c0a4201143d458400410580c64103241c1603001d001b00b222028070f59454266819050f1048460051005401144c01c03400d01a4400c840610100c6541426944100c61504191551000d0008641609182e000842d030306400c1c2c405c45089a5040c1c00826540491211000e0681c00c001e4407683e000c8103443d00507d58480c28001350b002090655502ca0940d414500c014180e0b100088c1500c0d5149440d80c800c0069590000d000e0700700c1601420a03403a03988890400d8409030860390900c020f640c802990000c0c4a80341c10b070007010b10501601c002c1000682c4010103d001d01c0600c20140300b40102a0018000d0302c0c4c94400b40c038a00b040042c111078095034075079210003c4c0d801c00d80c4045642a07440803003580504041c0082940100341c003008100b80b0140b00a281403c104604030818890100038000d0401c2d01c040080b6059508050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 620489991 1250 620488741 620488751
    0x306120506100b091e0607060e1506040c050904050720030406020c0d0f03050307020a06060f031109090318151b0f0105090307030f0e1f0e06040f0306021c 68
    0x2041040d034408055a680c5840c1445400014584212105441c09104011700340c81511680c2c04a0440d40d0f0aa26141a03020307000f00100301c002140c5100341d40d07618000b00054640ca00d40e041c2c0c0369180710002000e080c050b504004001c4407541d4413000311121410120340000382c07621104403c4685038003030158010300b40321740b136105007101a0020152040b00d002e40c0c00c036044940c1c11400c0c40002414810002c0c80c10048410610009000394065513200c84940b046070b50b04160750300c4a100f9904d00c2e0340024aa032410160a000340203a21010800700d0406454003030031800c00ca0341c1c0e15600d01c00c18228809001021a80038001c1e543c0c1d0070490158202440816210014140e468146a049808483c1188542070346010103000c180101031244a125012714103194183c1c6068a24865000c90b0324200003140014075050303034a11001da40800c03210010110102404040580b503c03240403859131044c0350501081140d01d64142d0404c0541e0791100000d03898580c548604401c3d11403103000e403c0001d00300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 620491241 1250 620489991 620489993
    0x705100203010807060905030c06071b0f032a06031802030a1112060f0402010807260402150c070315060506030408071203050106171b040e04110103050c0a030903030612 74
    0x10350061416500381c0f50070380d18156981c040944401ca014480d01d50180c000d41c02c0001c00b407912001420b007060040340060030509456581d090b41c108550400503003011b85c0d03402401400302c040c5910b10f41219040f0f00340000319072030003210405401489050205600c4000c5070f400a00d680000e221030b19800350840b241040c041c58061620f01d0038005582c0101c0c101c2080f4040044c2c00030740140202c0d481803400905482c0c9070011150340b98010204414007141c41030f418055240e030014243d29403005980d00c07956050601c1040003101c600c1c040c04207032840c1440b030360644480104021017200c3e0700015a006088035500d850b800b0f412140d021503440a008420082403050b940b0080042a120303603003107030104900712002c1d01158001e0098100049040c041e6841125030100c0007a002206803c200034801c50f07602e42c81c0a2503100d6000984400700700030600080141829034040f1250742400e0900182c0f9003440340520300d0254160340820035440346400300c00d0500a60029001d09030303021880d0100030341 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 620492491 1250 620491241 620491273
    0xf04090c081002130612060f03030507030e270a150620030301120b10030507120302100c050f0304080c060c070203061003020a050607150513030807050c210705 70
    0x15074071039884140154010200000081d100725280003c80b0b1848403c0c0a007040d008980040041c0602c0071241d81d01c8001040c2d603050f110075540110721070f680d4541c0d40c0c0060301c0d00a000c48a41e00015003d07540c481000b500505000900c511606051015210300340d84a400c10790161190180d8885c1d0740b8500c2202103400c603840f04003c10110140501030703600e02c2140202d960343c1c0c8024031a0b450070012200c000400100015401030f04200c2c2c00e0300c5035195030f13280e8941c14208116603010461403403200074260304058040c02005440c501010042007880901c940203003413482949001a440700d000400141080401d000765080b040400d02182c51504d411800c031017107680f181d030059100b03100e0180080c07051490040e115054030f07030103051140342c645008140a0680c000b034004454903209544074002d000d1b5540300381885078200780c46062240c5298100030304000300181140003000401c0009800ca10000140440c070701010f0010808080a0f012845140b4000c451009155004441011005283d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 620493741 1250 620492491 620492513
    0xf0d18020901080727021e04051809030301050f011101050c03042a05010e0607061802210d0806040612060f060803160b060d0206160606060305060603060f0f0409 71
    0xc4240c44201840e40c90380031040d90340900c0c0c42070390450a103d820300d81e020043c20010b206840900d0502504228280d40e0805141a400180080b0040c000c00c1c100320915281c0d9400c4c0998001075040340c81410550101e40c0c40c0d20050048078050004508000403e922410491901411001c003c00a03802d100d02c05440590050b0f0b4159500301502c8520070701141c444204001e4108000c00b035100a0f458880195003003000401e1181d4849814401200881c43e0790040400b0340150f02c0000261003a20b10400550520725a8500b0144030450329040c880180010381012500041c2064815a6905000200030307040c0ca81001030095078000d086000c118203a004610400f0040d0303410b111242d15a4001ea90717901a60005071070700320345c6542180c00300c1e20380d010b25a00948040c0200c01c400c005a004038000d0340c0728607280b0040d80101c88109040c0210361040c07030045c0c06070303142c00d2080c1d00b0000d0019845000280c0158860051002041030960f111b805040718800c01900510691f030079810200d40803d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 620494991 1250 620493741 620493743
    0xc0304020108070509010e0909160e04021003090804030f0219030f110405090a030c081b030c0f0601060507240516030b06090102060f07030608030708221a0f0d18 71
    0x19420102084403513000d4400e5445500041e594410b00011040402051481c0602017240c0c170300840c8482c0518400485e01100608402003800c4020b04292050003009940c0038198010185010084000151840215400c0340d400903c10312004607580001186400f00c80f8044003400b46c503400020401403000d04112101c1e000300c204034a001c1c4aa42400305855045410b4800b0390015102d280021f0301983c0720300003e50294091034180310f00000036442c0b00f0b600c0102c0c00d0a5510200da46030103d00200503429049007040007424155141a0f0094454050000300030002e8841a180507110030f8540089014240b0741c031024002030800e00c00002e226804000c40c6000a420502034130204e080c00ca0480d003080406030b00504c49940e0b1588e1441100f00003400c02030401d5141c0500144204040014003e0580555203243c0d9510031040649038a0656069107101051296003c00c0aa00c040b90203401d018000d409542da03c0700d04501a00b098401c4071180f90321903182c554800d501c0e008200c443c0f40c0c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 620496241 1250 620494991 620494997
    0x221a07090512060606090d0c050d0305040510111e010e0a0312060b031303050c0f0303010305060f0a090224090d050d141c0b011106070f030507030204060503060d0f02090c03040201 79
    0x401c2c84000c00d51114021035815401140c10480c1d00c0540c100702400020550180740034001c065180d00020b507003004003440550000310302041c11b120b1840c10140d56042c1101608080020398501c030032040d1103004001303c1010344011351078030680800d03007074001d0882c0010b110b094a44109181c074015007010034010040c0045840e000020030070028800c100d9003c1c44401c0c0d0380324031102040d60110344035804045461400c5c011605005100380d0108040e6001e5403040c00505030030714101e6140700a100004003d425030b00e080426071005030b1a000c0c014142444c2004480b0000e42e555480704044d031285015080e040300131600c02009002021800b600000d0607941d0703070300d01d206218220b08914043c8860488512000c4607551030101820360115000c220181007001408a14006990900310219002e9000c51401091590b0442d0315104296010041d81000c41c14103040c148000c20a0000810040c082c03003481d103080c1d00340101342d44503000041c1c1c000c04070445441c0100800440790000d860481c04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 620497491 1250 620496241 620496259
    0x30c090602010204081509070b040311030105101202010305220c0504180201120c0e120307060c0801120b0c0702030f100b041803080402040b190f0509221a070905 71
    0x40391040c0215000c0310803010040501c858945220240d000018100080c184500300000603074044070400750004501070540c51151200420501d800d4410040c040b00303003009400014040c00f0130800b015102e8a80a00c2c000405588003080c2c45000810080e9524603180b5641010042004850744e00041d240150380c140004d0364001010300c15030981040090108080c07480b84aa004550380c03022041d507800307182400c420048030001c610624070300ca180c3c00e0305800c0000e640e028031070309020f050280040c91410300d90b250324041072050140c0e241c6070014040700003031000c42d41045811055900301e90300242602c06240c2c40013000b07942d80494207644400755040018103001c03841c10f0300c5010240213111440070500070b603594048a01500040049034819610b8040c02142e460380c0741c0c9078040d55010761008001d1070600b2051b11030071804e030303112602c43d228000800c400000075029034400344850b018403180c3c0b0b0400749004510740c0c0484843c5101e030b6501d441081185a44020050b017111825103050304 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 620498741 1250 620497491 620497499
    0xe0601022a0111030a08060d08040e10080c0109030809120109080f3103060c20031c0513030c03020715020c120c0f0f0a03020402030a0b0909061e070507060507030c09 73
    0x2131070380500140d10010178400320001d041810183c0d0407000f0603204d100d001c2d00d03040e01ea104136402600181d0f40010600d440106c00d212064082280c0036201c0401d0903c40c0400e881c541d10fa5009100340280c03107010b40c42d0342554403c004800d401c000300302a40080c050340c850010100240c46a041800800b0080c140004802c1807141075208828a0603440b800e50900c01d401c588807078014140c3c0b803088004001542906d00b040a0440d000e0b05141140320300915030f50072102110030304101c4a234581c8882030340b0f00002e100f104000c504032805042e41c182000a00000c4909003a41040d205030b20050b00350040001c81c1131055808030304c0400107072007207540c04040f40410552950f1100700078541e540011400340d00c0200391070b1808d40902c4905008100200f0540c4a0340450242e800a17240c88845503202c02480301c0134a42034103103d80c4040e1000017440c0901d4560f4462a1401401010248440b0242d02041280307100310201c1e401c0c00d0308001c3c148040d040c0b11500900070314410102130001009a64042 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 620499991 1250 620498741 620498743
    0x622061a0906120d0c11060d09030207050f2103160623090307140705030a050102130618030f06020f03011409091c05090a09090c0e010b130e0601022a0111 68
    0x8a1600340107401421010a650341c20b40305d00c180403a0075141c00b0034940f030b245102ea070703000001c240c6250410380200c1c0321015450040d01c0d03d16240c10061088018645074041600c480c034030340c02c4411800c80c0d051245242c44407594290700c10891401010384020010030f0a0006d2031300b140b08c181141281c0f0503d41a1035440d41005400f0030ba4807040c15420030421000881d1200402411002c00c40c1c09440c0d04c241da0354000307480c040c046401111540d40100e07050f00c180c0c41350744040c0003c0c440c3e400c1c11140038510014003107041d90640001480c400c16a00d15034144802981524800361100b10040da130303940c55420004885002e111200c0c8140c5074100090403e038008598820106091301c0d20000c440001601a20700c0e070405044a5040950050006904902c1e4024422107a000d400c40648031410418100d4400905801c600c0020400300441e0b14030490320503001003229086c0c9900903443d190540100d04003860210a4081059010400da803100540d41000b03a05c00c00980316884804030800c0c4071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 620501241 1250 620499991 620500009
    0x310050109031523160212030105060405120c06160b1b03060d1b0b0a120e0601060e1f02011a01030501030506040209060109031a0123030622061a0906 66
    0x1450340e070340c42e1440300c900400f5801490f0440144124108600c000c001400d90364842107949810003d221600781c56007940512165040030418407030540303550b04003404640d843c4110320820380500c0040c5a4840e81040c14044031b505c6000060040399500d4000021749c41c0560850030a68a00c0c080101040c03c89841c0d141c3c000a200d008207a0780d08590b81c5108021880c104048259000e0703034400c900d01c00c0000800c0801014140740001c0035110440b801009210000c109800c0c032885141a20f4a04000c01c0051590b04440451510710859042440854040303050f291a190840d40b0030400446050b070190411409444005000a10200d181c0011000c3d10b4003840042c080b40c0011020502608010060700e0b403110040c1042c81000d40d40740e4405003c20000004241c1a092800051000d540c031031100e400180201003032104e0900c482d80000741c4032030018000404201d0b420b130840d1482030254104581080c0c2042c82044030081c5642000504c51200752110720850344030380081c5c2d03149001121 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 620502491 1250 620501241 620501243
    0x905180a0518060907031a090721120e0f0f1f1803030c022d2107080a060b0a030b0a0e01060e1e100b0a120e010c05031005010903 57
    0x10a8640003200001880090800802485a20790662012400308899805140010020b1001c0751840c1040121228520855511158140140603070001c2c000752070b00079507520444ac0c3c850120301c00d081c0d00443d014100d00401d101408100030030110780007003240c00994001c4d5000300c1400100c108001d0b03032950b625504c03644070024400c45502d04d9601021b0503103400203070a10040c4030501c2c9103026200e112030384c0102c000607226542201181044418101c081d5107807409460300840b42c0a04411100f001e6454900136114050350355010128031020400603064501941c4d039040e29207600c16200c0c5010b0f50240c503600e040201d03880390303400d00d0780300141100c0d00003682e40762035100c03034000b0f00141050019901c00c541d01ca0501180c030209140341c00703014110501071042000d0340c1c001041503040c401002c54814582002c003c001142ea07480880d107018805c2d1411084500744810340c0002040d028062484940c60510000e46140d003080045000c2c08845940c986c6c45942d80d00116400400d03400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 620503597 1106 620502491 620502529
    0x402060d090c06115803050615070b15040203010902071406060109060c020a0b0412051603120305060d020d051b040603080702010804080f1602010905 66
    0x541c1c846610050070250000400a2008030034110181501444200c1400c0203010107017681910105000d0888821003010810b80c1d2411048030001c0c42c64402103881d1402082c024540f0f01c80b070300e04090b141c0d240309241615a03a165200360074080e200140101d29a00c6081d40781d511742c005540a0424480c0040c0c5072403d07401c2603040302003500f00c09038064000c1024882240d83c810360354420b81b52a41442c1c0e041810900c0840c1c880c0720300307501026201101007808500305800d0340d0300d50b0046004400b03c0e0301c0e00c081060310103104d4680c1c0c0300c0101200701e01d010a404080c0030b90000e41d8030550040011031100b00603004280964200f86c0103c03410741203c440d084800c22040440464880f003640c0c100f0280b030031a03580740c1040c414ac210180c1480101400281008030140072100b070304410302101511491585200f852520305001e00300d0114440000c00705290074011040c01c60f04410398 = true := by decide +kernel

theorem cover : BRFrame.Cov 620323741 620503597 := by
  have h0 := BRFrame.cov_init 620323741
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 620323741 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 620323741 ≤ n) (h2 : n < 620503597) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
