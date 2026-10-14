-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2838
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:53:33.278129+00:00
-- url     : https://prove2.me/submissions/c1abdd94-1a3b-451a-8b56-a20c790e1303

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 510251798 ≤ n < 510431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 510253048 1250 510251798 510251809
    0x30c0f0103090c0b09031c0c03031d0d080f0a09054603080a0506090a09020f030a080d060605090a21020406030b07080c16030e12010e0307031101021e0702 68
    0x586004107443d01d0400c000813283e407048041d0001c80e9080301500c00024514170070505903012035503200001407040700700601090081e4841034001d000c1110070b500558810800d00e183c415444800800694a0020001c0401020036015001022094180028070250301c07030941e11004505000441941200900d6140010000a08013000c101d141a040c0c1010306c20106403d04c000a0f0039004146100c00042c0c0c0c140721071040c58800c15008241c5120703622a00c1040e40103001888040b81c02880f401401203803990108103c4420900c901001d668071b20108820350700340c943c0b641c01002840001d00c00380100d5611081030406803940204003160510104d03000b01449000010040e4125103080d0003c0140551801202d00c103129a40701d040c105e44031085140024450b5180030040d007200e541c44000001d101e42060121100001c06d0812686040c145040c2102c10355805062243d2000070100c0405d03230014404020214000002c40c01c088480c02142c80644000801c0d00102100113001421561360 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 510254298 1250 510253048 510253061
    0xf0e130209030604080a020d0503011211030c060c010902011106041208090c1c050d14090f0303070203150115050408071403010216030905040b0d0206090f120a12080f06030c0f0103 79
    0x2402c8458905090401101c0c5d580308414034001802201900205540035004480c12070324000c03080d45544046441c0d0f2440945920070850740350050700c181080545d6078030f0142c19041c000c2d4000189809591002505c1503e00c0031880303249030409010000483da000000c650044024100b04545542e85545141881044800c03150322540e0242d90303400b1345044c128120406440345084526000d00c20009903008030845104d20751040042009445500f840d800b47e50a80101404480c10442c050740000d080c9200e040d0300c505040049001040307a2034480e142540100042d041003441e06003801da81d03580702c1000340500f01458030078007022030700d540f42541202c502c050381104507214071501d07140c010b041980510540b4032960a01020440500e0200811500141c0c0100294030700010081030001d4040740e001102d0b030200b42140d9154110000f400040c070b0a520843c0c03e161036003c03241e806400c1d10780c090010960310140a0810001c1e40300000c1d5104910011602ca0855204100c0100c029012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 510255548 1250 510254298 510254317
    0xa05090a080a0f0303060801021804020d0906020d450c0e0708191103220b07030902030607030608301602040f090807031409060301030b0a0c0f0e1302 66
    0x9910b16107050281c16030a500c0ca66100380e4050110741c0d43c4220300c0d8281d0203001141c000701c55426801a4071864294018424100382c1003020401c03043e56203540d030807a00490019040755803a12800c5000000070380385820207041c106030100071000d107a03601141880c0f030721034855041c52103400d00205102684d800a4020038aa84120002c1e1600480007002c0e00d00941c1e41c0d5000c4aa0407860016120700b5004140505003074031115400e650b102094181c010250402c2c103d40c199035000e62002140c0484142881080d141c0c401040072030721407060600c0c0440c01401e000403d80791120901140001040001101300503402c14144400080e8580c10303540c0035014201d4025000081e0403011040b440072640005008032000c110910901034084150f03280617900900d001000c01114000a00030300c062200100e4044d00b0600b0408100701040c01588284c1051760341440580401c0001c1c0d1060140e0006810140303050f565840103401c000e00011044c20145100301602003044407040642d85c1600c1800a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 510256798 1250 510255548 510255553
    0x106030f050d08070f0512060d060204030f0515010b070b0402013e03120c0703030608101e1515110105011440151410080603030a05090a08 61
    0x12410724186075101c0c0c281030100081107403600090090703401110344070340e1361107541c403a90310f4414145942c00d0840402000140d100d80004508404205a40701034000b461040005041085007418603030701c0c10000d2000c055004420703500501000345508195503009501070403c0d00d40f9140c910068900504981d0040e45000351024150b0b2140b44104031010000c0c45a102e4100042030600b88a4a03846245402c5010310700f8440802d01d01084040105900fa002c0e16000480039142c003202c60901c240081d01c051859159024060f00100e10f41300c4444d0304420701020031040000c0a00e48000000d1840342074907955100480904c1940903480184203000c0c0b0740000c122560310b90f01110902207842000034054080040301500c0d0900d014120025107011001c1e00e502c0c20114a00e489007a280000c900403d1038440c10f45051000e038100c0b00b40060154220456072910500007440030781c0c004482c01e1010801c1017030501100d501c0110446450000f10f1030700359a644051f60115908401c59400201c003031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 510258048 1250 510256798 510256823
    0x3070b0f1e03070e1219020a0e01030605010609050d0f0b0c0f070b090f030403032f01020c010501060e1e151c270209070315381606020c010603 63
    0x241d80e00c40045200e000300d503da00a6880d0208144160070141109010050307100d0080714555a04090702901e10510040c00750b0500c036100c40ba0088c4869003a8000c0707982585450042c000190090740c0d140240c501921104070314a069250703081c980b402140b01824002e42c03040414101c43e418802c403088901107900ca903a464a0900d407070706aa14084600750545e0050000301c21100401004075002c481d090f655005000076031310400d10b04071042e100b0800313103100c9051201c0d144020070700150094450401c00020345616180002d03000e042c001e020540300f400e0051703000328a0300d501110398464100c180d0f907901c5030810380120884140b2440103589101e1212100c411031481d951b800260340030301200c00d075541700d41094140341140340c0300c5a80254080391000c00140454801e41c0310849404104d10012a0070b50f40d0020407186425820550882e00601160b501d208021445c08448030100a10110320700001e811010039141c42c0440700501c86500000e81c045c2021003500600007a60b044142203002c1e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 510259298 1250 510258048 510258097
    0x80a080c0c070314010507211e0501121406011a0c0708030c0304181107060b040f1e11040b07021c020a06050702040b03070608070f0c0c030c06170603070b0f 69
    0x40c4402d0a26960030600040d2091703109480d170200d2521000e1201042c560144c1140c0c010b0440d42c0002750014041c415412104411402124000e000010f0007011108240c240103081c9011031a02e01c02a92140004103c4111103046170107408900c8640251241c1031009000c2c1420542d500c003074000d110104031118808408401401101c007000c5508100700c0f051100f190603504a0005540f038840705211001c0480c100da00f06840c0d800e0000c00c00142094a0310f010f03012110f14142c1c1d0810340306400d545181d41c0800c0d1040c000c030300055051060a06c0d240880134040380c880d070440207020345004080d0071522102c5211100c2c00960050001c0c96190700c3d04801041904000001d0344180d0400c00b0f5080c45040c08500310040c1c84036a40c0d2549542d88001064035886c200881070010042e80c40c000102241d0403008900107503100d444c0c92401a813030700c03100911224405400302c124103481000e20819983c005038200444501c510b075140c56008031702c4032000700e00807800006c50b00c1c41400010340c40d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 510260548 1250 510259298 510259313
    0xc15020601080d0e09040b0720010605180402030d0516060c0507020f0108040302070303031e02040306052d06010f3608010908030f04020f060d090519080a080c0c0703 73
    0x5031000c0c50b084800440d0440021950300c8015075685400c601c0c4100441c4c0072400c16188640d201ea81070500c0700000008540d42d286841e45175260150a955a2400f072219240840d1103940d0010001090402402d0540000380c90768000550171050120001b0340040c04100c42d1800c900c2550403d000304048071a003003006c1d000d030340009801c0303202d005c800c110358100c1c2d80039030009801180c050b801071503d0350030350740c003030b03008107000c80b100010313910341c1300710b603550044580002c0002c0e41c1b0a03940450607003842c241c007019204628602100d03000071101505e81070f4000042c1203a000100746454805440f4000043c2d500b801d42e4018800d11010828400c6c61245c508864600f038800020b120100455680140c1400c89520702c0300204440c2c070400128600444101c00d050f0040c1c001020080c010103242c0001c2c0140d4042000c4200c1c20f80c89020f00da0a200090001f0050521132882000d0061b10f19500c900b114402c0c2c02d61a418014100040703000114000b080d1009012a0001c0780c88071622070402d8031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 510261798 1250 510260548 510260551
    0x101d070c0b07020c091803031b04050d0c0e1302281502150c13061115040b0103060b0609060f0714030a0c0501060b041208180d0803010302031009020906010c0c150206 73
    0xc5c0114915804284021000c985945103c58050051400c44d260320791500c003507691071700382d804060b01d0620000c1745a0f5103903080c5203034039481502c0b80c1948a242000c04041000020f05c0040c480229006003000358491036941101010043e08600d400702d0120716a09418003950801440741080d0a95944803a40010704180c3d00300e01001060074075036072000d00410f140701c0d0100c0c0c036008a80c6041e0400c0700b01d0180000311404d1102c0001e43e203070300308031010140c0069070483d01915403d41940040040c409288645010f0080030744901c0d184c0114000400c4017840303071a11600c90004006450b01c00e110030b0b06620030001000d541a25910b620a0703400034024484460240d4042d482c20500041032034070350003107508076650f01440d0607403803103203807100001c1380c1107203c00e0a1500b8810b2944411591029855011144940421504d075411070040c14603000e600280303013040900e06000200035aa0700d54110354080c2d42441c054910007043e2134000b514401644c0403416090040f061200206c1e008a9001d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 510263048 1250 510261798 510261823
    0x5040801140405150411060d0e06161805030a0f0f1719031a040c110d09030b090d0e10050c0a05010501050324220524101d070c0b0702 59
    0x8402c440c950139040480160182e900409803122014071b8145410181c0161400d0020400002002902c407009a401c3c0384c4100d82075062401c1506943c8030344c1e6002100c48558446d019040c040e00b50420010030394401307076400b0290404015890003c00c00c00315642d41c0c0c3c41c05500034072204946401c10320b00d94468001d2121140c0c440a43c0024003c03252082c405c804010850050f89400091a001840b00610324150403200304030b00720100b00d10b0340500704001103c913403850b9a00e6001c540707103062181d42c403100070700036051982014000e00a040d51284027180b0800c5e085501041d040600d081c1600c4912400d11241381c3c2d4001d9040d4901403000660069040f104141e040d5071140484004108550a4070715808032a03400b444085989030241c241d00e92080c2d42005480040f84415854103450070032641501c40a04500300c10601000c80d06030000c41d00030b641d990118416909000c0d0903814a04070f900c1483c040600940040c0d140d511070390010b4409a000740300708806040451009464250200c141d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 510264298 1250 510263048 510263053
    0x102d0b090c0705060f040f1704050901091b140c0106030b060a08070819110909010f060905150f0409060204171c050702010c151e0617061605040801140405 68
    0x200703100c01410442d203019a102e0007500403540c3e5601c2c030740340b1050050000d842e001024040c100000d10200324807485540300c0c102040d05c40346088100013910b10b05030050203910741032061890031011a40210201140e040c2400d485104608076030344154080d000703c0b40300c1582070020020a0041403400a8041c1c041030b2400506c2c40e4882840e1030341d429081c0315100d84d580c45800c010001002540c084402a032080254443c80c8040400240c400407080c1c07042c5466941d205400c0485501601c84c000041415410a10203450b052140780c1c681d0040c8203405005030260303864260306582e280c2c09103d243d984000115103817a1198040a0300640e107e0840049111300c000c80c89800350082d072000064400c81d80d41c6490100150b0044450b14603000c002c41c0c070281c1d42d1211302142d007000d002e50305a400111701765500404d07002c08140190790143c3e1200e144a2308035114131020070030100f8180c2c2c0c8404002100c00b5091081941103510744950b83c0b000c4800d510f0132049946001c002c401c40341c0a0b5005104 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 510265548 1250 510264298 510264301
    0x18120212040f051801540b01020f07090e01110301120302070b0304240e100b040b061c05180d02060a0b1c03110a0602040f03020108100305102d0b09 65
    0x54908140c44c203000d00d13150450107881407500800702c0307600c0a6864448900a035484100041100c41e000010150b0b49a1010b401a038000b85031494800d40c3d81c084400d20003810b410400c01a2103890b0b20480c041c44c0501034030323800b000700d100c2025084101c0201400710484d9072503030340d8901054414160707202280103009520000800c584034405030303405150410040001d04822040355920180c90341214804030f904c0702250030706240180b00981d0218900300010505c04a902c0c2004100c8030b50f490b40d14820b405c2440110500509090000018090072000040584407020300b00200820303148489100e102d4241d450340341d0759001c5103540c0260841d080502c07103003011004001d1603809503400c00c0d082910403014440803030322a04400d007540d0800c109071050840745032035000503640641c00846003103224140400440d40e02c41a6158015107401c51103810074110760b078031030300c85420950100c10360384c0b6504c12000740314907200c514440c10240c4a100c2011580e041504000d070440307440e8903120b03106500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 510266798 1250 510265548 510265579
    0x1005010e120f0321070e06070c0803280f0509100c05060c1305150a080a0213030c03020a05011107030303090302070e07030507090602011802132301080105090118120212040f05 77
    0x1d0740d40c000c00140c6c0741c17600101c4038501400100d030403024041c3d454203403103400052210003d00060010741c181c032508045040400b81880545006d900002c0c040049202c1754043c550b900001380c4075150011100640481030a031800c42c2c5001452201810901400e0240722000080b0701c02848004c54254000344031a58480400410700c0c00d44446200c0e620041100c0f0804a10400c0d05e140d2041c0d841c440181000c03512162040310072050b810032200c0c6401c8010a0081d45000d90305140180400d10b42400031101010b00c0d651201080d01c80141455150001d00042500a2000201501010005119174509800001c02410054500d03001082c0c0b80d01000c54a6441030140c110069030201d040c29104040c0e60034046962196040c03400c496541e40788142442c07000200c0f000f581c980010094000d94185102c2d2403c41f10050300040752685031542a12501c130b5600301d0040e1564204005201d00c02200700d06908080c91541e10405815000501081006603101900d01f920419542000b100d034811 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 510268048 1250 510266798 510266857
    0xa230306070906180f0605090f030a030912060209060307080604051b1812010c020a0201080a0e070b03180a0c14040213051023030f0f1005010e120f03 66
    0x540381803000070904941840f08600440c560750b079000ca1501080700c01c40c2d44040600922280e81c01c40000a1400a190101d034075100c1b01100300910200c01800f481e01e0582e8000d041d10015100301d036414641d04d00d41c0410f100c4298103589203014042d008942d42d10300720500418061048680922a52810010820491004600403166007500005601c2c040209000c030503007440c0350b1903c540c801c144801044007003c00303001d1401a03104540042c43c083e103107840050130f035140051140c4226440c1140001104100280e0340080354140c07039210741c0c0e81d12842c1d0000205079100c401000b00d4810480744008000d102c0c5012800c4072085000c4050307a0000d601000b050b0310031421314606856014a052210389400440703242c0801e500c1c01c10251250307428028071501006503400158241006c820007145112007a074140d40200301c1203490b80f96152101c60300e07054040d20f0203024100010a00041925101c2440040800016000300c0d10141003000c000e6660b03501c07940109448029442c0d1261405440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 510269298 1250 510268048 510268051
    0x40507030b03060f2e030303140c0f090105040e1302030106062c0a03050a060c09050a03020d032118050f07060815010201200a02010605030c1309110a230306 69
    0x100034103c140c5906082c05416070780036140700e440b6482940c1ca4240c1800a0700c0500c0754480c030b0350114034014590b0801400300c81c41c1401c4903200720001410092890b0071601111804902414455258520a00121114091508405416100e4406120070100c261714140d0026108030000e10640380c13a120211000c1c1c0f240080144850410804400b1100410402248080c03010b07004002c030640c1da4031801c1c5080131020b01620307410390310481c1480099000300303108003400d410b4440d00d24203840e613070114100c10703c00f030b4020302084855424505030340da26440c0300140342c24207002840410301c400d5007001c400b24080f2080701c96100d000c49400e40014081180000c030b8001d030b16140720319030301e080140030000c001440342c034110f542c9c900d10140701442001c0f1210f480c591088103182c035140d143c40040d08668580c0c00143c401e50200e170304102d040d55050020320030310b00d202c800401d0340507291408e1107913031041e003d103240d1003683d024010410a171011818100d92190f2440c0480c51081d80c000d1580781c1c0c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 510270548 1250 510269298 510269321
    0xe06090111160f0210080f01060c03082e06030608070e040804060c080903010c0806010f0c0809040902061209010b1f020c1c0218090d0e031b030312100504050703 71
    0x144600305190ba041c05001e1a080d02034014460b020b019640003c0841100413403500104000d0020f20410309100440c041c05481c0380c3c1007400c850901a10068424a4010b18003500081034cc02075030102400005480c400040030000d00040325216000a40501014000c8040500c6000b0740052103440b0494900d0180d90080c041c0c2e450181800011654801c488005444c0900208000e6400745c0f401d108118006002ea900e9038020300b0700318001400344105a40d2541003081d02d1800ca030101300c1e180b00700c40404004a400088000c124070100f18a40105005801c2c80d035928010440020419000000802c0381100c00c14802e13150b40c105850040c107504c2c92140140d00c00e91035044076040c43c8945009120070381400d040c044000c0d5001410104805290044500c650014000b6854081101c0c0050300030a040900103041c0400c080b903903640401c04032000592010020274415182402141c81100e500386803018645010b5109121214107481030b180991f00c2c080010307078414480d101e080140318 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 510271798 1250 510270548 510270581
    0xf03260106181202060702150415140c100b010c140c0103110408060105041505130c08090a0b2707091505010f050a08040212030a26040201090e041106030405010e060901 74
    0x1c3c16070207000320758100c600100e0304004012889940c480000307014000811520125500c0450703000c40052040c180b0140001d0f00c0701d410301c000307100c1c000e0105401e0540700c640c01c000104c06481f940100c90b040c81d8450050030f0a0009008c0c858000f5012410b03002840084e00d041c01900302c41e85880c1b40c03611a034800c861448d080344e00103100d2840d0075000408a0200040000300d0705032a82c0014211664a0a10900003992040c131020340344c0d00001c0709980208501c01a01214038541c40704415014002c0c179004004115980d02080c1c440d07440d00f042d40d41c02c50141150030b2141c84001420003044680b0b01f088100940e07a030700103015846903011030364138121680d41504090500a041da4088000342040364005e03200104a07013444001c0000d800044000e80d6691311245104000c200205500750442900c1c1c07000400300801741c2d0f0400b15800c101c405a0800d8100d0350b5a0b41020100944036030b5041d50710003030010500c0b06210054014003e50500002910755503118221503c0c2200c0382454280f0621 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 510273048 1250 510271798 510271829
    0x80316060b0301020d021612081b0304140f0a210519030920040b0d030e1002031908010503060a0b0a180204051309051501120f0326010618 61
    0x800580044914000182c005401d10080f001c058050741c00c450450305071410b02c4180340051100c501c0444a940313685041580e1359082100c1c564480c2898440c10300114000000031904100a242201011000b24000c0e00e02001381c0c2052643c42d901c4466095620780c0b20144004160840484070a001340e807140c807001c1ca841140d100055000e508420088141580c0315103490124000d240c481114502c250340c4030b02c05580040420088440c1c40c90164001c80d40074045200092700000b0a004c000c0080303480540100341d101040307103035200b25248544a4207050140807421500490024140c2e00201c01f038034110380c0c8824075001254051849240d004031550010459500700300755030310404076910f0340549131075101d601207440c409224503550700b80c07903070b95454009100c802c2c0290071000117007900301415540760400716003c40080501c081c0071218464200700130140900da82d41600c040550030945802c1a100010015117400d22408000c01c440306018840d103040d21362080140d1b017110350400700e01c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 510274298 1250 510273048 510273053
    0xc030c0b0a0e0d0326011a090d0201051317031c290a030b09060103030f0815090c0412050f0c030a05030f0a0e090405010f1a0616020f060d021201080316 67
    0x41c07420f41c6806a050149400c00c07008a0803546001d00344a58148140320700e00d500d01000c10200d51180b10034646284014820744040f6a0303003940c5281e0460302464100c3d151018001030150b50301142d4401c400e500380c04032140244500c0031002d00a0b01c1080148584003ca032840c0c4502550058072064601410000240d08001210180041c1075000030307200e01c0c040c0d52079680b01001110b0541c0c072440705030320420041003010ba20021070000b0030050b20f00514181411b8003217072413260300d0141c017a10609035840003074840c00c0d14605803401483c406100c405011748a00305540c54008900d07141145029020102e283e41c20002202d401e816400b40045140c2880c030302e1800c0050f08038914102c00c1042891603e062a6a0840814000c601941c00040c0c2001415002c408888076910f04007031600960f100c0302d081d0f076550b8040d25940303142a013a1310f00c0d031005440040c400c22000340040b644444003261502182e801d582c00b4004102e2804002d07801640c882015543e6400b403040c44800044001584100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 510275548 1250 510274298 510274309
    0x20c09040224210907080111190507170a031d030a0521010605030a150f090b040b040203010603020c0c030114181507030c0e0f030304050d05190c030c0b0a0e 69
    0x50390040305118038100003124034140f0318041c04124204600d10032100380000c462040c08020003c000c3c1d10001c02aa81e24550a0341c400e000e84014a0849901041402051401507040f1556164080c0000511030401100085540c100404450000c0e147c080100655038000706001c500c00300c0c04005606105d0f580200b01c1c1c0b25070010b800f40390140d8a8149030032168802c11841030190a0545800d61a807818011b0b00003160840080d0403a2102c03410701c104043d540e400c840300140c9030106000304045907030b00c021034090090256043d411034400400050b84980c0359000c0d200e0302c200d180c165001240090205801d950040c01c2d000d11000300d60000c0b5016038a040c3d00401c12840c80d03029074064625580c814000010112901d030086902c075240703405410b0b070100c5419070b0343d4000c4404992501c80500440e613640600e0050030b0140180741401d00170b10804109407036101040c0000d0a5111425151031003c11040d440201d440c0e98542c500841c903440c000099079010a4290741310102d40b40390504114 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 510276798 1250 510275548 510275599
    0xe19020f040c020d08070c0b06010e01052703010e0a020a05091008070308132108030705040b03151f050f03040305040504050f0709050f0a1a04170607020c090402 71
    0x99128400d00305484a6899034000d02504a216801900e003a03c0d4001000d03008501c02020201040020941040001c80707a140719900001d003860580c41d01034400c401681c5030310030080340028100c9a0010032140800710018182032040a800901c5042e900040c01c90b40e529240c48000d505c40001202404281001d1035442d5000540a0003070074407a503075101490500c980381e0015515804001640b0a20640a203200c17001403110000c4080012100e40080c40ca503850100002d101c208000040b581c620310034402d990161040011a40c0d5030308050031031888c8194017601c5c546c043e85608108242032074102c8420440c0044940b101031400800b2501620725502c020f0003103091000512011903940c50b01d110380c0e803107002e948013841e00c14101b0f094042c00ca04000c3d44407e114940a200920180d2100f490384001c4440300440e154030041005d010806a02030b5070000e050f21010f019a800e2110030024902d4000c01954082d00c1c8111504828840340381e4084070f010b500000e41e0903090741000d03040390950 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 510278048 1250 510276798 510276803
    0x3070201020f0f04030b0f04050309010c1110180b0a140d0f0f230106020a110a0e070c03030b01081e0a060b0c0f0705100206060d08130905070e040e19 66
    0x1440c200b0200203104094000490303003078002c00082810b0080000102c07a090b0040503454880700246405d03038074940d81e407060340143c604103c0005509420881d031100220840400101040c960702035100f802001031070f989030141d8251008844c000703042040f50341203d9420b6400c1d902d820354100321802401059021118800d01c23a6070311003500d550110b10344203000e00f1100000b0301141103c20b04203550181d001c100c207020707228a001801000204d400050520095900019410b6071000ca800040d0182100741e000b0038000320340d0070800810395880100754100e18440d4600b0000c0c40201001103d0001c41199403441c100c3d41d40b0304030441106065640c580c031034040500800c1c51916042c400700160051001810b00b0f030b010320303115000364405129030300c003900c01500d020340e0300c2d50301d08002940c941001d8425400740c0c0e0610300d03500c00d01c260743e0211880780075411341440300365982c1c400364001804201e4440740051503c6400c03040f241b40c50300441d13046804034002451580e8090106582d80258403004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 510279298 1250 510278048 510278051
    0x50f040b120103050d0f0207061d1513150f03110d09031e021902040b06070b072c03100b040f0608010906150b07120540140603070201 59
    0x115810360500910301d200a008805106501d18a885441d150100c0714600900040041ca4954030307070b00107960801c540d0ba03803a000100075081194241c101452840c00c03500035504498142c08005040e00600800400c02e00e0191203590380d5400a501398000040340300000c00302d40f0030302c0e0344138401d8005007448904041c0e01841d107c3c02c0801c000c11100e099008030003143c2030204003d00700d00c040501210800207400a400c1a0900d02d074003410b03d00072218000d01c2155540c509440c01d803601c2054440483c0e218005003450f0a18001c0075040d0a89200312094402c4072001e00a407060200c15490324204016006180d03840000c11018007401a1041954120b551860301201d80343c0349010360f40040060100028007140103041040541e003030201a242d05014004c41000083c0702c40084544540d000138881803203e9641d10210f51a10454107400718032046a40c40d00c02e21109084054004c07800e40030b00806901e51848480307130780480c40c85510034030003804420304400d0402c11300031544100103100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 510280548 1250 510279298 510279307
    0xc03020408061315021309020d060803040e150d030219050c0310090506011703040e04050a08030c0901030b04050709031b15080702010b0d080d09020a0f2705090c01050f 74
    0x120520780242194101d0904820703c505a09011044d5103c03034405100c03100c00e61400c1e42130307001c00b20340030380c148100124654001011001408a13034805d0f4050080756094954440d96803801c440c2094003680d8010003c0c0d203240c01f42c031141c50030b04c1c200019141c0c11f4002d422002d4044046248a0711010303001c2e581e40c0a010100700241e50207003d1200d81010b1000c000440340454100a0301e014016009106201c0118522403015600001a2000c0300c5c43d4280d031481c20b94403450100d0034041000d41c0180442800300601a40000420250001d004d0a03607040080c08c01020401c015941c0c1944e8050100b20960010310126044000309020030780815003001c0c0329507503026101d800081804c42c0c0b8001071004024010320550a000321842d08100315400e0705500c41c4e070b40710702c1083c0c420741c4142c0300103903540c142c2078003152a0034841e1b03001014081d0440c9009d5a5810141c2410804e0400a030104074260900d1641105248101c42c0180f030220003c012030440b00300195110341c0903801500001c0d20600 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 510281798 1250 510280548 510280559
    0x9100203180f010c02031b0c0a06031b090f0b2808070215040308012d0e10060903170304140d02010b0f1f0f12090804031704080c040c030204 62
    0x19806804010080c9841415000c851420302054282c00b000030f0341401d84540e14181e00009441d1303030000c541e84c0003040d680c0214489181880000d011b17600711703011080001d0300d19010b41c007002c0c6c2281000e0120800b03c03051030044542c04030600582d0302810840c481488005500070203045c191424501103400b03c00307000c0c80f60041c5003000c140040010f810130704000a0940c1400302281003000c5a0590107613040641d405031481e84140200742803038a00200d540740c00c98110740100c3c01c3c0202440105011030300c1e81c51410351000c04807a00440400d51a10029040f4401d14811045139002205030288008000c0040215803000c0c00640d10f065801a408241140c14464860000b01c1c80d0000100122003100340808203145210842c4100c2e8082e28000000501180c0303180526000c0c5858400800714401c2640d00c8179075a00c144820f546804032030800c010051006109403406856403e940e4030004030b00b170071244101e0082c4649038000c446104c045042030f0708040d120005a0401605182c2c482 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 510283048 1250 510281798 510281801
    0x12714190b2107050618042a0201091101180905040614090d020c0402070206030a0504081b0601050a0801060803040e1003020907020c0108060103051006111c0507050c18040204050910 80
    0x5050000482510b61400c681e030140402c0740d100244002d6450700d09101d50f4402041c0280c0d030041030b19000c0e42d00c0b0b90041d0035400c5402c201c13040f40c1c8080036081240f1505884002c1c020040101c040b2050340080720300d00040c0d0301400d001058010b00d9410000d0403401e100044024080c00b070001c868181d1a403680e1500c08141c820414030072000d100050401c00e01c0504002e21b810080c41c00d0f2401944104000e0002d41c50b0401280d90101103c003000c0341d2900c640c54411081d1041d03061818400d0035508a40407a4030010a0860481e0822a501c5100b107031201006800c0b180d41c4d11034007166500820040095406c1c9450440d40180c1c0e644040111a80c3ca8011038075a0404440100068208464543e81c40d83c00041c050341141c0b080c03904210030320307244240048116840c01500140101d0140c1031000e03020401540c4881c05121081c0d0b107800f48812401341403034121460403a001e0150103800c4c105820840b0401c6051008100b0100d095140c680910004140c0034040070b103940118014644c54410783d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 510284298 1250 510283048 510283069
    0x30a0c0e063c1206041406060304050c031207020a151e02030f04090c170402030618010b03010c030c080a020c280b0108031b1507110f06012714190b 65
    0x101c074610f540e040f5040303036003016000040100d88180e144c0300000e040c8810010203681d04c010181da14a03a81d0701e40f41001842e060011b640a41d05224503a140300c0285207101c064190148291280000a03445001400402e210080c0002c0011101c800b02c200350303903004008a44800042c0182d900c0d05800c40144200c0d5030254210000d2161268040c42d0115403128802d0844000b4616001c03141c1090f9000940700e050203010401601c8007500b1004507103000703502c8034a03101d0000b002040b03000400c401c0980a0f0840742040700214004200007110740c40d19000703d49103103100388054031198100711031002c8243d03511101d00301b00681012501d000140c140316181d010b4100c3d2001184c48201c5164002c0b0210189142541c56400000301d20045403044070b50260031440c58140392494041020805143c130580032494206440349500000707218003048503e50600030609107020318001b604404109aa2021021598491404c00000c4002600030a603603031001040d00e010500f02c40710400203c26481 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 510285548 1250 510284298 510284407
    0x150c0c030f1a070c1709040f150501080f1312091508090601060c05030313020111100501150305090c1002120c01050a060501080403050d02160f08030a0c0e06 69
    0x801e90610040c40e445502d40c16480f2031a440c01560884040d6a42030314950100448001c2c03400204a00415980d9900920b9105000d08420404051006c54079800c0c15190302c540ca010940010120b50041c011090300e034414034140d105450340c400a07030b4032a070708160040e40e103004001e880a000319151815550145000b08955103460007414181c000b035050810603482601840104104180066808015a517100e402e941c0160074058082c00141c4035040704c200e4085050061030101441d2440701d0344554182e403000680a000382d5400c12055081710790550f410300d1150300c01c1c8000c030034901c3d1030284101c04a81c2c0f80705680625042190110094100d8949a0b089035141d00070044203415521501c00204401d1901907581d0409440c041d05c644900b901b103480168000448d00e001001d103800c94490a03621171000c22025440f41007441003504182c815404442c2040c0c840c00145100d0303051401d119400501c21860013100c504c05060000404a03c1c00c1d010f040c515101240000c1d161b07a4145a04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 510286798 1250 510285548 510285563
    0x9100614160816030e0105031b031b042706120f02030c100f17041a0403050f0403030305012909040e071502151614160c06051b07150c0c030f 62
    0x503d924004c0c00c4851029604c0b0b040000c21b1080040b0f0040003695034000f1400007103000d07929100d0360100b0304554880c448103116403000207400201040903030004c0b400300b450000f001c800e81c81044444026a180c82c0f00d610311103110142d011011400c2c4150400c61944001d04030f40040d0450380c049409002c5e01454040407610b030080c021201030300a1186101e640740450740400300d1905981d03d81ca011101c29140c030117038045100103020580618200c50b020780780b0030310341034a0302d43da450010081c0c4024000d4600c00341c00301900911400485c103880e4051410f1030111410b08149805020050405410301102440340d00000175001090a04070a142089507001d00702c1400003a0100d445860081e141030a81c0e0460144034507016442114001040d0800c41c0195441000b800740c241115100000600707418000d00c40080e00903000001045954400c11100f40703100b00400a5a4503044640b140d44040c0c00c60300607000c0c1540c8507640903030145104110320705500d5225150340c0c07901c0c0c425440486914 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 510288048 1250 510286798 510286837
    0x16061a010e0f030d03090804030813050f0607020108061003020f030103120f050c0703020105070c0801150303030e01090206090f06040b07060c0e041109010c0809120a02091006141608 80
    0x30359010303000510000007529182c141c0d80001021907601d00c07015800300c0030581c2e9400310208105d042d2080b10300864000c51029218220300c02180020003261060034850048081142e800e41444010b071001e00e50141c40700500c5d80d403002d051020fa0303008522003904155081000e031405007000c00c05140a5402941000c00c1c05910382405003c407900e411011051201c103000c0c1c101c02d40c10000d85402500c1c2c0c280380080d112140c030316001c0004460368028040039400d003201c1c2034408003145c0c1c0f1070003140d002e65014081c0003007101e03030f403800c840c6484c00103900020101301c0c80820381030080003520740407009454145030640d107403030018640d0000382d422030302d454413141645032865015002510420049804001040c40c22080040b80d01c0340c0c10400d414441952421400d10401c0c40a41300c0303061000c0d0064054a82c10140107440d1072031460205e1144800c0c401044000c094400c0309002c2e100541c6441c103422680345628030305078012641842e5940380b00c400710030002c2d13040400f5041716070b078806105a04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 510289298 1250 510288048 510288101
    0x50705090a090b0c0c010b041803140a12020912030c0714031f0b010c02030610180203070c0305070c0306020708032706190608030406051b0105040510021606 69
    0xc110251000081600707141c004004200c40a6102e60030107038003280e150b82c401c04803103240d0150401742c0d03419504c94a800001110f9024010300103c526100307583c2c02d0503401000308a1001401046140b50015004c68036444020841e40e0040000780801031511401411003020946558001c0c1070a203440d030802c28042201c5103544000c9649004201e000e0724020b0021019480c0246000314010121612a1090003081e40908000d80301d0300e0300a02a59100d04d0902c0058042c000240314600a030300818420f90306085c007a20035240616480d603603c4c0304030038160302c0c200c0b403503081614140c5019445000000018000f0301c010300031588222200c81c0c036490b1080410310455030321201e142811880c011309482e008004242540d202140340c209184d01a149950780b8002c000c0ea4000d0314151100080100781d40b42c1000140c502c1010701010240a5908100854240e03002a28001d00503400220528804000c58028114203055141800d80c0e01c0b03803076140c2206640018207800d82e40452120003d0a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 510290548 1250 510289298 510289309
    0x4061514060d0506010c0b01090614030309090c07080c03040e04030906031503032f030909061210020304030e100306082103060d05010605130608011b17070207050a03050705 76
    0x40040039540c9403144014004946a48151012141010782ea10005062680104441085282c04c0040c200c85507031201c1c880801410b00d40100d00503054407403c0700d140391600004aa22924018144000340d498204540c02a82c2224000710351100d0300780541c21080314100058401024070200d814420304007810003500300c01c1603400000400d070510f900c1700b244500041c40031044076803510f4030301002c04280b003140d003020009030f861000003001140984400750000024041c1c080040310310503520b8580008014204142c41c0344112a23403c9000b4155070400300380d0266900038000d040488109040340300103030302c500c114840c0d800480e580c0d26083c82500c1d8108000080380e03080b80700c82c40514003601d040204902008000d64414032011a00801700502900110300801000e0440403143c0c040e0030000001d06802d0184c02c03500d6280101c0e884890345400003401c110a0140c0302c060300c810844034003510302d010003040b6000f076110360a0000740c192102810400110b00810113000d046052404008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 510291798 1250 510290548 510290591
    0x130e04140d0e150f092110020d0f02070c1a1605100e0712020418020402031e0c090603070f02160603090b060f06040e07020106030f0c171507140c0102030406 69
    0x514004082c04881c4c1203007000b20864400100c2203d1826082a0345545a89100c3c2c0380c0310421003e00860f86031140842190f00070b040c014244503020320100c0f8403400014201e004940d0050300000203d8010000000740c5403044002d070000380d168500d40700fa24281e4103040221044200c80650200d00e03181c00043d248c2c414000f42680180241c41c1c51460180c42500701d800c14400a07100340c0d5a02c0c9a4079001800c0046000915405003041d900c80c03404041c0c40c0801d0381c0704600c2d01d041903e003000045543c0281012140404401009181540c40b0b07501c0469000e0380c01000030003548251000d9581124261156000504480c0e80100345208685041440b48401920483c010880d0006501c510394505058400703650009070b212007507a4031204120b000d07002503480503091303000120a8030140301e40e600070300303094401c04c0c0c0846103040c43c05403003550781d4011141c0b56040b019a0b1000b181c110b52055401c00c0450140e020f1582c10b281200c00007a003240d0081d42d01b114070550b15265807200049014000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 510293048 1250 510291798 510291829
    0x10614090604150e3718020403150509030d020903011d0610090e030a14040b040f140d020d060f02040b1c06050a08060106030c0c150f050a02130e04140d0e 68
    0x80c640611888081c5a01001141c0c1e60011a103448560880100160395503100030032806e41c100c0303c0d04450032443c40003540180001e40f101f011041c07219125040b02d0160314065101400158900507200062000a41281203515810354903907596480715000d000c6540b030800e0360700000d0049414140c1c545004d60030380f640318020060600354081214072010040d03420440040c101103c6010090035107201d50700c80c540010b000d4050101d408108061010807100589020900300c000708038203601005070810a4010080d030107904200b281d00010156000b040c8002c16040e005414541c81d2207075020b09401c1654048000104620881800f102601a6030002d142c166105424641010840d070f0715050140a03290034541c0350140310301998800e030000d0020541207059283c40c4000c2d040800041c005080c40e2038003150608011440d084481c0c800c0b202d0411009c01c502c0c54403840c000303c0c3d41c00d15800400031741d0b120090902c006000281030103819081d80c856550300105404090812152044c80f8900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 510294298 1250 510293048 510293059
    0xa051f030203030d0207050307020d0c0303020d090506070f02030c1806030118120e0d1e120305010807030b0a11030c21070f0e0f130c081e010614090604150e 69
    0x1000542c502004a811401401e43c000d80d0b01c2c50b0501b0000c1c80c510a50800a400844400402051000d10030003042601d00c00ea00340ca001c0021014111405510381c010103502a00c208182800a041103900a40052026050f154001c800100080c4204542c1440700c5040d4005010040503290a2240c400e050600c04172400c084450b581700c100c40000c80c1c018660901442c81c003100c409035a40c0c0c00101a641d80329500b42e10014250384212004d81046c04201c1e4295464134444400500900845060b5400d0300001d151840c1380d51901d60b4040409000005102d9a9081845402c02d00600035440f6402032840780703584010b144e0480010100f2000c11055950041041c004000d91111a00ca06114140f40c44003141141ca0001050720301680c1c0d07200d034480c00c80300c140110700711550001e02c0c003201c19499449050f074800e11a903a641b030040150011311200003006000c7c0d503000301c8001048420f0400100d04109000300440d80b1513106800c0070002c031100e20025502240c0c4640380701c0c4001c00a484 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 510295548 1250 510294298 510294361
    0xb040b090a0803250c09020a050c010c030c080c0f040801020c250e0105150c010507020d020f0a02060d0e0a1416090e0a03120207050102270306091b0f0301050a05 71
    0x120341d8010a13414104184e1030100075624240301801000d02c0c040c202e0801c04541d900c81e440000b800b26880110030806550801d81482100c40c00707480760500c2c4010396100c48045648880050300258410115007030340d64014400401d40384000d10142c2030b2074a0700e1008000c0400b20401c800a01d0081010402402030755030001e20000c00c510000344c0c1124416541304845040a5940904034010380038400340c10747c81c0c90308002026900094108111000f40c00ba01c1c05650310700c10440d1180c0300b0090180d08030a08000c04855442c091b0701070a04940040183d03015410345030380750085000d100d91040d10b9640004500300da07084102c20210014a0f01200803c00c41105141490b103c1c8030000002d01401480307106080b51004a4040b0b502031507105008641c0d44050340104451008401038031070280e810790081c510581000500d0078003840174500105081c0b400c2030341c68600c4502d0300c500c1035008446400035a405440c24011640103051424012a01d03162503400322180c4440107003134400c8041c81c0c45 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 510296798 1250 510295548 510295567
    0x307080714060a110307030801030c0b0703020606091003050607020601030512030103030e0d05031b0f0f0a050a121403040305030708060307052d0d051f0207110f0a0b040b090a0803 79
    0x9126030920040d07840e0ba4072100e141c8010703142440140c0c64800e0b2800000b03000420141e1010b44d4a060380d11076854051803039100d07040c1581e00d00440d200280540d011201041c0a890100c60583c0e01070542851981626141c1d500c190500f002a0341c501e02603489032005208002082c40101d8000d006945001c3c115032468500901a0505002150042d044007101d003040c86818800c40701054a500d600740c01031000890b4450351118020036500050060405002e080d52012a49041c43d079000340044c540d403007054841200856149405d1420721103007a14106940c1c01d03035005580715900948419860340741007100500104170081c0702c039100c2d42228406109698074162400c40c0d09507600400a03441110000e480801c0d003001465542c004041440482000701c0000e40d450840c11001c0021000214203200900368050004001c2120901a03942020342c14180b00d0b441604400401010303031030742e903a100500325038000e4109c80304c490000151901d140c10401060301c020444080110320740030001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 510298048 1250 510296798 510296819
    0xb1f030c0804082209180204052a0d2d05070f020304060f020a020607050609121e0904090b040c1e0311040203040503040801061805090c030a1211060906040203070807 73
    0x14018800c4110480130036610300e01076040b0b025061003001040202d190158507007900a11400892180d03080c000000c0e0b11145141000d046c02400c0050a51a80a101d03030540b0540c11405c3d016502a07990504c865100c02c0500083d44c03812001e42c030308e121a010340c49c540720a44000030f154000344410b074140c0040c0700354000129805c1b80d11511b0000703111014000120704008107502c3c06503100001090b11800c2c09070204035079004a00c01e50480707030807000141c181801401400c4c018040042c10b24450409250303014020300c40900300500c0021001d4003a911071032803100603601680c041e5144002031050015005054440d4026a01c0d10101240f450356480040709141c1c1d000b038011500400441e04101c800c00583c0c010388540c0c8001c0c4001515511501d9500c2e01c06c0c1e0788548402d00b00008a40840030119611070141c0300603010340f181001c1902c3c0c48501c05400e90542003045003840407403141480503c80c00d400f80c003000740a40078900701801090300d0304880383c22071091a000407004114143e001d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 510299298 1250 510298048 510298057
    0x120507020310050a150305030c0106080703171309050a090501060602150109090206070b01330516150204031a0604020c0a030f0302130b03160807050901050d0b1f030c080408 76
    0x2e5040114460755070244c01c002911000c445290020783e810030100030410048003801880d00418020032240740d0300c0e00c0a6603a0f03011840040d0049400e40c1b880d1040381214402040118811018803040c5903441c1004e40440f1011a1561a423079511103542d4100030702801450b0003480c2ca072008141e0481c50b4140a00b00908c184294440a40d8442600d01151070300002d443d08244c0059025820b5a5a440380d000c405c062100300c000e10080c5c074100480d002419034104013810550365a411704186d0b4202180c039800c03448140940b107aa4403c1040741002e0094001071000e903100f00c0320380c10640c56006503001589005001a407140b030042c420300d003182400003503680015405280c0903c40300038071304d070580c024400c9400c8000c49070b00702100480c402800c900258000c0c21007010007100d80d0030400c82103a080d2400c0c0d0301310300000c00c01c200390101c075881034014112150440c20300160b0000c564002078000001000b01c1000d804200800348041500340c030440d08480201d0400c500315150507a943c034168401d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 510300548 1250 510299298 510299323
    0x10f09020702040905030309060106030b03191e02041113050d0f02010c030e10080103030806010207060f0c08090a060c1502070b04170d2d180602070206120109091205070203 76
    0x140881e8850030b65440b9005031000d1900030301900d0340c034100f814805072605001d00034007001c24103021600105050000b108a506d01a508610000e0b1520baa2110906400114144144d00c0c202c070584026a98030720446016038200c03460607070356084501c41d118440c0c0c0c0300d5101500c10001000e50101080d02c00314004030f00c40d424a008002400e00d0324090f0f030f5101c0b0643c0040e421819421950385819004904030b81600d0281e180d440056071000012030344e0714801c0c0a00703000a4222215050b0090040c55103016003842802102d040c040c032900801c490001582c484000150748074200e00074001c1c814181d01c02d01c0c210540942c5401900c1d1103007030f51154042e200404059000c0f6002c0c41c070807030b040d05a60344035040c80000c0c046003102e40d0000148a14001032008001529002054000018890000b450203500c4400b10181000d1721002c0c020b4004210581e0003043c10485c1410200d03074554000d01805003600c00140460342c609240032140320f0403c40005200c000c003e00700150b030303001403503518010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 510301798 1250 510300548 510300551
    0x301090206190c06020d020307030e16140d020414150a03050703031b080309070305010b010302040509180307050607020106090b0f18090c040603151401050105040320060d090201080f010f09 83
    0x2c0320a402110001c84009001c0c1140e0310201c0d99810b40000c1d90010b502800c1259024420a90101c096584410088600c8602c41c200380c00d04201d1198000b40c40d061411008281094841880e00440d01761600c80c40c0000c0d4841a007004c00985040030210403036188800e55003500e40b1415543c0e1950342e42c0040c08045e00f44007100c00d50000b03414400c2c00f000f003055030000816440b4103200508543d0b03010940002c4900794280a00a0b4541d4401e20075101154030050030020075880e41e481d007440b02ca18151380d10800f80010071021011980c1000f6142c020302c1c131a0700000c0c05a180c00c09100c1100ca080c0f4585d88900154000412a5500c0c0304000300b0418070000700b281e0940303503140801e1510000d5003070704e41c001d0b040034800403d200c040820b42c02140c4115009110441070300c1802d60145c1002d01030980030036424001440407079161005032100e04d80303a00814640015640010b01d66400c8040ca4841c6252170b10b400d0011075a004800a80000002e0b03440269541088184901c1e08407600484210740d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 510303048 1250 510301798 510301837
    0x706080603010b0a0e04170306130e030f040e07020f120324040609140130030327060c0201060b0409020703141206090708090c0409062004140301090206 67
    0xc1e942903115000ba120020969010260340d83c80c1c80405800880742503601180074150301d0515405d4508803445040010804a88418101c5039000144941c80221020b44420f100c40e004801e2100c0080c0003505c0152004e071020f15108500038505800840d40e41210f070080d51205400001420035280c111008000c42d03c5011f01c5003403009014035003000c0729541309041000000d40101d030356000c00408000f19903001010782e02e070445800c0310030400c002249550b404420060490703880500c0025030030700c2858081141c0d102c5240340c441c0620221610030307020b00d03c84051400c1182d103105008602d005800203101013803526400284a01851140700103842d00040c100c0c041612a403010043d0071041641291203442e0000c0729542c030b880858180307002e1100c00010034005d40c09403030000e21a4219000900b40400e2410602000d0843c45e081124104d03241c003030310f6030414204e810349800c034880c05031003580307070303481d1641034410640c401003540d0081c2d24060304070000d038503620111361400180e01e8070321016 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 510304298 1250 510303048 510303061
    0x312210b010e0d0b01090c020f0606040207150609020301050111010c080f0c0c0f010c020111030f01030615081509060a0b03061308120c04030210050412110103180503030f18070608 79
    0x10880641840c95001851400f40c80400c03400719101c0c0d0594502c041c0400600c240d0050a0740d883c1100120074406034002000507180c1e03c2d00e6001000502d01c540b40003c5a09010b4420301c040d1076180d0895420a5000310040c0200c2d6408003180c80e90300110340c0203000f01111040301520100c4064000300700c91078004000b40041201e10211000c0300131410444645080d043c01c098000c1c40c001d9039800055003054106426100f61500352801340c1c1e52002c0c100c00e940d103513030b071030340002c0424010000c082c0420403070020f0091424400c80f6920620f980725103100f80f41c030404036410014001d040360600c0b071404403000c00c10741b00010328681c04500e008004e0600c001c079081030101c034000c11000404281c120002c20116200180281c0200c03482959a608040c00340d0805071410f00950007404180e01c407901141001c5031100c03208600784003040c10300050280105500b948116a0b0740e2080d212544000144606101e0b4000c1d9554049609032100403074140740a03100780c0300e141d54131950041103812008a84c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 510305548 1250 510304298 510304307
    0x40b040b0a1503050604020a050607030f270608150301111b2e060e011404094107060206240d12030f0902011209050a0b0408040312210b01 61
    0x101d002d400b14000c550541d4902d0010ba8801c8111400c0340074000c2d41d2030000305401e1190130394905a92644514040100c038680444210100d14901480c440948070104051021400044042c18141e52828802d203440324603c0080c034641d5100e18040c0c0c0c501403100a610455070290b40c44c0400c81d550b2040341d0301510003039602d0600c08d54500500704640c9284404003a102480210200349085414801c0954603100a80d59040900c00c003401c400c0c0018000019207080d50002201510514546a080c17594040310f0040d112900240e0b00c03d9200c80501059090140000d11148a444802084054144a002900c40c00003403d00100c86c144540480240700d85020202c40c50803003d4000340004000303040003502c00300c6100c020310102e494800011600d451902804c11040d0701078544482c0b40114080c403800170252844181d810307004038018800051b400c048900d02650058943e070f41c9490a50a246a5001c065107211040c00cd08101c210004c00c43c2000c1140c2c40c0410b07820000d11014840d00589 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 510306798 1250 510305548 510305561
    0x50705010c02060612061b092206180504080d0e12030c21090d0f03110712110303010e0c0f0702120115060e0622050a08030909060603040b040b0a 64
    0xa02039400d1925014000358006011071040c002110443e00c0310001c1e09801d40c41d000161005d440b814030403c0d144c140e17205c1c503a0003440802030140c000112011000e070320380c08260307045021041281d2a1101003041100c0769059150641d0300c107808000a04207a5940b009031720944ca100f103400d03501d8107910300515606000884414540c0302007d581c03032400314441401640041e4543c0ca42c1c01440203040c0103610106012417282d41410003c01505400070410b440820702c1c142a4410140c540c50758000102d08e230005403501500c01d01c8842c468076080e02018205400e032501100c0c0c0e950043c0010450502c25541803038200116004060b030300c403040303a04496180311790b2201039042440c2c600c0c05047c00030154004a944a0740e5200940c2d01c2c0c2e01c916046816400d01c810503a802203084c030503441c1c10f408004000240008078001040115558400308000c080590720424942e0008500702c0315a041c04404141e001e942183c50614600e00307a41c800011007000b83c40504034003d868006616070081d6030110 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 510308048 1250 510306798 510306803
    0x1504030507090c08130305070605100801060303080108070b090102120901050f0f12010504020f0d0213030218010e010905011203032301080a020f040902010927110d1802010509010509010507 83
    0x1030701c1080e20746030100c02410500600b04005020080028540c0850322038481c007150381641c2e05403410b00c268643c01e01801c8050505044c80509140000c0d00c0d043c03d10a0300b0040d40709407207461066261811681c02c04045902a20207000204803500e22682d0206000f0884d2250340180c3e80c0310015135004036001e0050b500400d84960340042c804546150311000380c03070301c81e07010700400c13245a032140300348026030080c0d0700180013045090025618244454000e02180313103044000c600c0c03141e034a400081071b0203104511140718940800040c04a070803050301c1f0501404c881c40e0f046c066540b410700b00f1000b500d0b10718800b4040580d64040c40d014021450200c0c84800e04d2061000300329610350440c941c813143d0b04502244200301540c1002030a04140c000c800c00150142c507441c402c90312b4031400361448043da002d0300c00011145003115001c2d00080c41040924901c10a005840e800b024020104440090b18080c0760f016001c4e20701c600603a072110444003603072003e01c0d00f00c0c1c583c3e003414010f071014001c3c004c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 510309298 1250 510308048 510308053
    0x509090f0102030106080412090333060e040b24040903021f06080f011a0d030c06050c07020f06090a03030f050c1b0114040e0c07230d0807180515040305 67
    0x6103ca0340208402d02031400f4104140e2100e0301010160b4210003279100c024542c20504458180e0203168640100c43c0340c9206c0c9210910540b00f0189500300d80094110411894011062006008490046652280000c1d500c0304d1100300f0741410143d0400c0c0c0d02d03800ca10460b1543d10a0040510a1120300121403a00e4059000301c040358407118041c3c0441e0280349aa48109520007140c0b081c1405130100c243c4410100807860000703002801700910504900713078140600d20380310f10001101d41c440c1610441c0741d01341c07058982c41a8810020944031440d862031003054240044109651908220f100302c0342e00d420039041d40321415400752164040c40e10214030501441d6220a1b5204106903910041102640c0b140c090104040180107a40501c0c011000c0359020764001401c658002c0b4000c0440d00c0c041d41402c04160307803003040c0501c0c81507090380b0980d503a000310a0700682950000c0c1029001207071b41c03c202d0f07104062406440d0004140b4440e081c41420032a1140340071980c440c0c110ba004d16009400e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 510310548 1250 510309298 510309301
    0x21504020402091f0f0306050d1101050f03040308151e0d060b03120408060a060305030406050304030903150b01080f07020d0c21050c070909030c0813080303070c0614010f0509090f010203 82
    0x41c4e06484507040c1c450101c0c444040c410100340c824030680b026100001c01c0072090300c1840e21000502400d9561840c14081d082200c28011080000614807a52280c0e8030300c80c1070303e044140c0d50431801200076054002e04419641e40d25503150000308020b010301c00d40c0c00c00710000703640c1042030103480111078140c0c250007003a20b5100d181c0f01c81c10080040c1e40e1102c04480320fa445450b40d4908407001e5100c082e019402c188030901210744240025608a8064640764054a480f5100d0724002d1040440e0342c0c0b501d559403045280d455070091401540301106884402043c5443d03180691145054040c2e0000c02c4441c005443c1000b002402007110f66880c005402207030109240c000d0082d5002c0302c41410a8841c060000440328181d00076a40034541c1a660540c8000260f074aa00c4030790801d01021100006038500800c800204002940c45454150384080e20030440e030500b001200d0102001d0017920700d12030010710011400c8560ba104648040d201304205a5404c0030301814800241c0c03002205500000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 510311798 1250 510310548 510310579
    0x12030318021e030f1c0f02010e0102030c0a021b150a120207110a0f031703060d05100204050a12020f0907050d090f02010f0305191a1206010608130302150402040209 72
    0x2e60300e900400050302103800314103044480756614420105901d0710640442c100b40440e0f403041103408240c120900000c5082e6000c1c010342c40c2607070000c0304e049900c2440403581140b031a5040100b205818281c1d02610b047c0d181c554049440a4405982e804e210b560010300d440031240f041c107044d0344110500104644a1180d031601c0c40901c590384011034802e020f6088081444d041400c400001c407948140414208010003c814040c1d800080c40c89078024146002480412001c2c80055114000c9040061b40c03203061004100d0b0841554114618000306140000c0050b00e4454008038075050440340c4159030341e5000c8046480e031013103600d081103150500c442442005078800c1103083c0140300f602d5400300c015a0311800c404503041290000c0446404a4044030450f0729a0b00028003c01c101c0c90001d100b101c01008143c07081000305450606a2000c4010000325501454158000120703203002042c09403552402503035600c8000c1e02d100ca4040c040042821507455030304641c00543d0161182c0580751b8450b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 510313048 1250 510311798 510311839
    0xe061308070b0408012d0906090506130302120a0522031a0106030501050607030206061002070b1308070512060a1104030f03030c02010b0f1005131a071b1203031802 72
    0x1303100d20f4500c0d60030180d1450010001403000d004407403034448480030300c1c0c4c02d0b901c0c0c0401421400390f058603c60303624400d1402090060103841d200f5081007140c804079a04501e802807903e05901011550307034400b40400e00041e90b100044900d010b04680160078104850401100340d90403581c001003070410f01c03140025520340f809407102e04030340a5407001c00c02603985100f41302c8580703e2131030028016040140000c26034948040c0c0e98280031030703920440d0401d9072201c001150641c007406a501803c42011001c000042c402c001d800041c03c5c05903604210042801176642d51021f014080c2c03252151070342030b0070f4010071107441603a0080d9000b0604248014503410301030000c04418619030b00650078203243e6000c9080c42170124890800203041114648005081100c80d50410190f80003481d840c20700010340d103454601034400020240203001e5031004140f400350001108000c44804105044508101c07000041c500982040c0e014100802c0070b50020560700c0b075120142800a6001c800c14260740a4060310 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 510314298 1250 510313048 510313057
    0x91a09090c0c07060c1707030e060309010b101101050c0c060c0a1e030903170105090601030b280e011d060607030201090b07020102032a0a0f1106040f02090a05070e061308070b 77
    0x565809600c000b550030406c0007481110809000309502c40380e44081414501e000b9580b1151410000814107445000108080040c0200b01e0005c3c83c48c8200d5030302c00380203100d00d5800181d6080e03002d01c2c04091058481e2103040040414a4144002c00d4049016016840e40504100c14006200c001c00b01442c0190040c010b04006400080c0a54039000b00040c040e0f200c0c074181c902c0140388402c3ca0799080700440203000b101400907000603141000c080c00c902e00e40e4a16020507132a48080c5c0701c60b030514541c9102c0e000c059021071111128200c40880c0c030070403c036069400010a0b02c07403030f80d550240e04069015058142c4014544510b4a081100c0241c1c19409140542d1031b0082102d003140345001d8069000c16540c1505e500720300104010f001442c094008481210454102510b00901d103994042c24800120f4040d128225602c8a40c011071810440301e40c0d0101c0c03100c0c81003080b414a850000d14544d4040641409600d0000c0c1c014103250040e580c01d070003400d4030700031115480c1c0c0b105c403020602d800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 510315548 1250 510314298 510314303
    0x403080a090e19051314010e010c050f22081b0909030405010203120a1d060a05070903200103022a070b0a12050606090a0312091a09090c0c07060c 64
    0x2000c1044003215007114042d5071203c9140643d5500055200010003001d02461400078212002c80d0000b0403030400310546042e01400043c007102c009144900303540d100010101003000801c83c2caa4503030f050000303030f0f8015500c605c5160701401c1c0c142020041128240c0240026214510310003048512100d2040c0703070114107a030340314041e8448210840c1e0b01d010741c1c051a03016030414000c40103420071502d400b607884900c46601080c00c81c0140307452105015400d64002c0c0c20b8020600708886681035005a0b40c200e8514500042c2240c5141c8078020000c05213205604c440d0a02100320056030301c0398040d0380190030102c1d1040c0c014607a240c1c20f0702e450a10b440d0580003a008850300000d080c000d0000b0780344402c0d07060302c44000d4000001104001014000d1065501070030074000103d845c3c5400030700c0d0028500c110740603001e1400301b000281c01d0f003080303030301030304499038401581e5080c2510001512448802550500e03550384131900c03410414080c4020310502449012000035105900c50348800d640d50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 510316798 1250 510315548 510315557
    0xf020a031b05042102041d07050f0a061211040f1701020705120c030c0102040308040501030f0b031f0b0301050c030f07050c0712020f0910080f0304080a02040c090b0403080a 76
    0x88000c000e01a0740d003803001e00c1d0004114240320401101e244407048148009100c0d407040740e01e000d00d900080440750600c2d00e841412a90711041d42c045101000f81d44044d09044800244500b50f100c006002e40000b0b00481e401c018444220401e07861407900241c20304d41c21a00c02944540c2c49941d000c502c4411841111407504100d070104172070103410300c2180d0302550050042c01006843c0018206550700001402c123a030b00c41000b440703101102c20300c064070165204141280d5250701e424001800c0c0c6005802c0c55003224034000041c5521b540018001c0001011000030600c1c2020522524009120a892050f0154202020044001166801035100f14040400e0a0b00ca8a03642d10848d41806200c241a246500401d8280b01c1e80121000d9905924801000c01d802d000d60a00441e600302c0e000da070061026084204240280c5505200b0200c02038101c0e0000c5050500d443d1800740d0f0f07032040321000b0303000d1075907030820441e00c40c0326156003000b030055020150303560344c1d80c0d1400111541c044d104010005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 510318048 1250 510316798 510316811
    0x7020a09050a0f0213030308071106010905150f0d06230f0403030516080c03061201020c01060311040b0d1106040b030f160e01080f0c0d0905010f1401061d0109090f020a03 75
    0x8010510a82c1c944110311207042d4581707800d59500365a40f80c1c024000d1800e0141e4401210400032080110341e004e02500100811541841e45014840800c11008284070708203080b2b1807071490712420a460310301c0d604072402096002150701018801002d240382e0107210b41040e410800c2d1030203040f03080c90155209a804028560300c1c540c40ca400d4041d03500312080013407204c00105502e620440041c40d001100142032080720803036109a1822a031101c42c800364542d4441c003041040c040b50905404541c00c050703405100d4808590b0019585003194000141400d211459a16540e110b28098401a1030504030070f81d0390303050940500100c614200d40c80c00a898840c000070464034883e400034440c4c1101a190100c10341c80321518000d60450080c07520301c030380c0c0c0e0500400360000c0e228041c804180b402100000354140307140c040340003503501e2415203201030b9001e80c0c01041a2a4003402e940301c51900c1107030b038910f0201c0e404012a01041207a01c107004141c202070040c00f56040c0c2c1d80c007c00c003507245038404011a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 510319298 1250 510318048 510318071
    0x16061e2a0305010b1801030f1d0c0a060909020d0e0d1d060a090e04020d121115010b1c021e09180103030e0f12030705210403080a0c030507020a09050a 66
    0x2911001d0140d21240c004c184081c440c20000700540000c00d100c14100410138104900c980c03000c4034440303440744004000c070a0a2401100d0207200d01c40c44410241d0340000c01a091031000351a1012a02c20300c018241c0c0047d00404285640c0d003e80d080d0705102090750b1034644a880c0007020070303811001030340c0c100400043c00702c1d0528040040b50981324168913059807407450f103030158205042c010804d98000440000d5040040d0b69501c00d81c244541c0d54441e5100c0b000b0036100c20b803412680c49404c9400c5a800001404001034600c166200007001c950103501103400092442c010b030081c0d8160840c01241e11040504500308030010340400c03042640da150a10042080b10003140301c00780b10140115200d1000003150b818843e042100110000c0e1400d0f0520503180e070341c903285503c403801c2500c1d02e41015034090120003407010400c0090f4202d08030760f8102400c6440b001e0151040d0080703003061000d40c0b05c40c081014051029504e0f00c41d001441e801081c2d603900140009098111000e0740b1291030100b07481070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 510320548 1250 510319298 510319301
    0xa0b0a020301150f021203070315080d020f03030f010506030c0f0a08190902090a23010e07080f1b07110402160212070308042c10030506070516061e2a03 67
    0x4080b2001c2d8000c040c646c103044181c811607030000d04120200354845646818080754500d02c100107109100041c4032400080300b0090401d109411166036940042080c80400c4200c5990b00341901c4007100e1241d1b490b100c0800a00c814403401840c2e42d0a4032021444074a81030300701e000b052280c40e170181070543c000039111040b0211144000029800ba081c0b2000c5048106154070941101a0050741070301300c141074081940c54038009030320032505055408104844150310486890b008042007810301c2950074030420841e0710804104143c2800c400100d980414040208842a40440041c104540c0c0d42138241c800001580d000c0300c00d038014400a502030034808030004d043c10860790000a180d00340b5003803c0041c61550161154036980300c00c3c951000a070603e0300c455090246040c110b0070b1101610710b14206042001c0200100c0078030005000d2140071168000300c0c00441c90388420001007200040b50031b480c60170398615004980515245a6101c904611024660100d00c02514a0201016080201c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 510321798 1250 510320548 510320567
    0x9090c030c0d1509030203040b0f07061113060c03021501120b0c0f040b0f040306050f01170309010806060a02150903040e01150e0d050a02090a02031510080601110a0b0a02030115 78
    0x24183c405000d0b164200043c5544010741c518880e206980c0b42a50b1356624203102e13004001041c4544000092103020000c00e0320550084020f00300f54181000c0c004107103400c00d8400c07481903005006642c2da4035000c041c03080c40301c01c00202415011060550311180440f402e100c1018088500d4558070380410b01e031046c0e00083d11102c1c02e000c1c4102d40b5050030003040403c16000007400f0000400203000c040300190441c0186882001101c00740340c2990702d40071081044000000f460846504100240c0340c151b640076050650011007a21141c2e074400c0b4aa00032841c0840e5800380c4680a03c0030014480d944c6000710040088840c5200c00107040e0340c9500600b0708a0308a02c0c0d40d800843c01d003a59150450a040601260f828065000e86803009003940200b100d8031b0080300c01d060403070f45c0001002140c1c84d00502c0c109964005076101d0401c103884034405004903402401c03c40c140040d001c0c1c0811400c5003003185a6000c1d500840a4005090012054000c0c0d0828051024030381d6440780c940004174415450306 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 510323048 1250 510321798 510321803
    0xc0e0a0c0f02151807030b090105041203051003020103180b0703020c0c0406050901090509030c1609051e0a110d0212040309051504060302130b120a050711060103060b0f09090c030c0d 80
    0x900040d212840c04e12844800da4061384031500540c4000000300f82d003450040d210310020300c008510707440d162a10400741e40c00c0c1c01801c4103143c94101800988548040350000752a070a00303000a814144409044600d040b40c20007e04103043c0800f000744156050f0040c00d100b101c40011500e0408850081106031401d6005007030700460510700400c06a50540c22090f009009d080c00d0300d2424250a260905000585041c01e202c2e5070410020000d81d0480c1c450035a100151107088950b0104100341c825884002618201015484110120135050260101e412060301c0340421540d81d1900c900354a00c40204580c00d42c046001c5450024080c00c007a101c110f515100d00150525207803e10900742d0080d0407201440650b2403030b0700300110301c1c5e0708103000400c084580c4801250562030842c11500071340314000d0544040184440704c040d03081000181c0c4034103403540040042031558020b400300c1d139801100500d80341e10609200902c81006400709480700440c038150280d907410f00500741440803020404600 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 510324298 1250 510323048 510323083
    0xc0b010b040308070b0c070c0b030108161202190f140f060a080c030714160c1403210f160b070c02010806010810091a01110d0804020d0c0e0a0c0f02 65
    0x202d0005c034072903004c6080e10300c050501255843e1a03440e440b254200340000e020000040c88544420400d410312410840141d588071400c05100e05810103420708001d0081340d88014900380c50f1992203074880a4199010140080761755401100c0c421180a60700034000d0380042e0384030180f82404000c413484c0b079406844c0c4071503d80300c0c1c104440c071540c4020f200d8410440410860000c42100c00c0040900850300283c0b01901409802c10303005094280e0f00400a102c03c1d2090000b143c4c0f000f1840b10340c43c0340140d0a1581116102d101d180d9244a285521545150001081441e4694500e4170010b00c41c0942880038070b80e0346617001907504514241010340840c00007070005803190320420006900c00588400342d1041550380c0040c1095400c0d4400e218003200745e5900c840242d513032003290000d0440d032040041c90180b46440c0080e007020703c0600080d000c0c160401600080c0100c052407140200324106c1a0740341440c04100010041c200000c0c60300000e0750500103424107510010722004c034001d51106 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 510325548 1250 510324298 510324307
    0x8070e010b0705030d1a130b010e130213030c0303021203010b030604050403120e030d0e0601050a034e170604050901091a011509060207060f120207030c0b010b040308 73
    0x540580c240c2003404110380b1032104005480320b440031030080d417202591b40d8048100d400b007030b2070800c02c0d840060704d08140e000e85006001c0515030380c4021010010082554151482401492840301034407401a079410b100b88450301c00800c11407030f40e10705400c0301e000b942a10b600b16030f1040303844010302c028424052400c200f803010603ea4640380d8410b540203840790902c03203090210407254900742c9604000510442c0c001203005600d6a40c3c0e40100400a442c1b0805040250705260009040119900000d401c0103920340303062004241100e0000740e1102074030340d401041c00b03494400b000480c08240451505031010700340000e19601900700c03400c48030340000101c0e115030390b00d1007400000c01000302210060f6494004c00804900702e0907100d40c040262115800181d13052500380f8400442e03c46400d010001c03042c00405c2180e0307010400702d00740c5035107241803804200704441c1206c40c50100000c004408d40b00007080c01c10550072225150025101d66552a500d0303a8440e06005240964403020307060070030400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 510326798 1250 510325548 510325559
    0xa180e0114010c0204050a091202120d0b0312030a0603032d1110021c06051504093209010518070513021201060c05161a0a090905090102040302040608070e01 69
    0x416512194406241c00f400520442d00090140d41d021350361000340a030703181c8154084c050b4060000413810013a00027029400340381240d035507a501c02c00d100349611603541d118403100c540e424040035104220b081310039901c038280300c0000710003405188001c0340171a41100c0500d00c400c41c0b0199000c1e4062419216000e02210ba400c151140310181d01801c03818095400310520700c0001d0b00c043c00c0506644001c0c5800d11000c545460301300c5446030409031203050005a60001c240c100800c9a06076000f00030042090008205002076440c50040024200400300c40f8000030060015100e910890080b0002c0c001600c0754044001500703200010780e86543c01c081c0e42400181401c002c41313015251510801890308242d46640039030f5100070317040100082c00d40c441c1e120500604005c1580d445004800010b6007074600100b4400701d9159207000da03c42c003000300b05213855a020b4011038000740017102007440145407100d0103034000e62190200700e2089140c108007081c403c0c00012000203941c981d01005000d43d0806 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 510328048 1250 510326798 510326819
    0xc0a061b020f0c0f01200d030902040b0d170c07030f0b0906150a0b0a090504020a050307021b0307031e051c02120304080a211b080a0219030b04060801110a180e01 71
    0xb1001c5005031b031104810103107906030400001e03046840c1550b000801d02036620400c406d581c45214540e10400451100402248c11211012100002070b00e10395902d80440d44150705100c1c403503001070050584c090b40320302407101400c1c000b44107101071015105140d4400944504100c0441c2d500e5400c200c10440c244860103209005220105003070070103c0e45c0954440000d01a0b901c440071540003e9808028030012070b0301001001d6060b0b1080002905444440000c26035030100c0d48030242441c40b510481c070540c0c003180d80328200f007540c00c4819103900b11494403006880c04d0306450000700601c201c000d640030034220101920300855010002c0745c0f406000060807198018260402041c20f51032140110403108644030b61724403002805203d2034951817402c006469180024401041035004106411921070101d6060304040042c0c28001403a40c16100030030003c0a50b038116849075864845082c020b403000501401c2040a5540d450000f8400c0c0c40d201031881e11725200e407140300b40c401c0b4014007006010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 510329298 1250 510328048 510328067
    0xa0519060c020f120306011103030a0c031d1906020d0f1406030a3203040303080a06060918090c050d0309050f0609030a150f05010e1510140c0a061b020f0c0f01 70
    0x500d403a10a0752340d81407107241180c3c41941d81c480c03801d9541c20702c0f091680c0c00d07001d07132010300000429803034140e118282c8483d211a40030510491800b803000d00203080204980c143c1d5000380c1c0b092001c010001c44e409912000b0000c0e504d1107030b5480360b800c00250851a000940300030070b603130280c1c10103074a8500c01051110301c3c0d15103614503014100d07a9060582000e0810180c070042d40260340720356207401e054042404403003458000d13100300300840a040c00019014404485c50481c4644005007907441070800c0718a00f0340e2600103d03881074101104038103144c1c2c450300c248203545084078288032144000c010030903544140100640c054001d100800086103c000114010b080000740208000e481400a00102c0d14240c0140d402e04100c0814030405941c07140781a00010000e40d880030181001c00b40c0a0040d41c403142d1007503100d002c0041e51400584080c40b1059003141e00500500c612201070007121221204402c42c0b5005101d1903649046010340080d91a0803c4006442e030032404400c44011600d2041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 510330548 1250 510329298 510329311
    0x60d0605090109050604120f080103020d150b040c0c061404020306070809010b060a090e180601051002010608030a03021b010b150304062a02010c020303090303011401020a0519060c020f1203 83
    0x40c3c900591002c1041800135522892180f400007580d0944010301803c0707007440d440d0240c100300b5550018001625141407182034a508400207030a83d24610f480b02010746100e0460381d41044c01c2805400c1c201c2e81000b160420f6512401090100302d40d290108000c00c54101c03000381d85940302c0b0011543d80f0740130340000c90300003111b6000030984500e4603000c114242d0040c040000040c03814403041000003425914590441100001603060210b01c4031181e590384010700505200324190301c10506d41c40e00035802400108410016a510f0b6038244102400941125503421440b42281d84007101607141803085555006004044098032a03075091100c141d900003d000b02e45c2c1a940300c05046280e60304412075000c014890b50004000701080d1402403d40b504c1c0405541558824030520105a40c040140c80c10340d81850b4522003141e1500c80102d2400003d40c0001d040c50041e4000d445120035051403017171a42c0e008001c24400c080701c1441c1207035140c1d40681500ca00343c2001042d0300300481c03903400440d008007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 510331798 1250 510330548 510330551
    0x31090b0301110f0a051213020f040e0d032705150c120403030911040e0f0f0a0c05091b040e040302010b06040503150406022a070501570c0b03060d06050901 68
    0x16070780140301b44901810760b01c00c1c4500107200400d80445ca01030780724070400d0000f503a09015004580c8007096999204603d500d0034541c80e0440400020b0310740e1503405440c1c40c003c0e81450340100c40d040140d101e16031501701500d045c12032000601515120802c81c2c000550082c00729146a4642c0c400704c2c010f25581c94200c0c2c100c800300108101c90f640f24055801000300c3c84e005006031140301903d0501d003804082d0020441d42001c00554007103907203428060100e0300244c640400e01c0d0394902465603142021901c00940c0280800c0100e0500400340200780b06506c070341c00810a0360304510030000c560080348241c541c036034086d0741881c0c030341d04071032070104e0b00a441240d0160034645290304e05d001030070001c182820a441814a8402c00c054108408801000b00b0309182c16469040e0210548040c0040d401c0d022001c40c0c660b9003100c2100d01c03115100303013125074030f00110702d0150490000080c00341c0301e41c00e88221071183c0003c1040400401164010b4030000d101107051800c1d0b0303407018003810004021341143d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 510333048 1250 510331798 510331807
    0x503090d030c09051003020c0c01300e1c1115131104050705070201080a060303080103020613080a03170f10150e030a060b1f1431090b0301110f0a05 65
    0x1900c50780224110000552405619080c05005a0380b50588600e012810008150200c2c602e210460103c4000c003086410341980c00b2504072f1815018200368034442c069482003580d0441020680c03015803110081c65603803030401c0702c1780c14106c1d07580b0040c850601900142c0341001c6107441d807190003070319490b83c807508541000c8100800050b0032140101c810b0302c0401c0c00003072107401310b607131140c01c0303583c0022040400c00c011030035a00d00821324041400003d01607040014480003820b282490140142280d000300d07101c42c2d22034600280b80307401105150f016010040040f400e084132644090748200d807807103800200e06141c416901401c04096a80350140310b50320396100340c1ca1701d00b405811046400741030003040e0102000e081c0940c5224007049500d00d804008ca44004281d0b015444032800990605017a85410144030f104504143e9035103604081c282d4a4000c01901a02444400c100c680d40b440c1000300b000800281800c2c0d410301004121094020001c001c4c09040907405400200428030703126040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 510334298 1250 510333048 510333059
    0x30210060e01090b01170610051308010f0e1c0e280f050a03081c02040909060905100608060408030705040b0c03090301050114061903180303050411010503090d030c09 73
    0x8503040c58104041181c0341800501c5500c1d92070090340304803042843c05410103136602d09510b43d910005802d407442080c0402c5102c0117103101c1d505451503000b101c3d481e08031050381d900721240288413440300455124104402280802804624044c142031444080700c15511030b620111051000b5140031a44031480500c2443d050400c849009019004003411803101420084414140802540124402c039458407040c00001e4141043d20855220f46100d041c0d100356100c16031000c1c1c00b55401840169181403802e600b481017517005600c01d140180c040d910051040f201402c2982d01a01074503a5550044000c50000b5a0340e200850f0f00060b603181c42d9007003540303600d2100030692214108405a1b80040307403074051b40c5401e20405004010846445140400034004a400d60252074011400c51400e40c102c1075030349020350041c01c20744200140f03803901000c4501e4080c000700720030344041d5080c1100486a220650080048030f01030399040000b0700380c0400c14082100948030015800d01081b2070003200040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 510335548 1250 510334298 510334301
    0x70f020303250203060105040e100506040603060f020a09090b0d020609040e06010e09011a150d2c070801060518070207050904060218041505190f15110c130504030210 73
    0x4140c0b03600e0a000360610050040600d09901a04103d100f1032401070010303801840040c1901059202c01e43c08a0380e03a4034240020b0007172400344c0c40a00381d282402000384415a4903401482c80e00c503151034484480307484258440072609441c10190300a01c245c0388140c0545005005041e0301c1c50014004076035504506909030500c072003070b44a10f80308488802880a800020300030301c9100c0c01a40d06103070a0b00004c50015660031400d49034007017401c0c030000700480004903540001d40c1c0e68200d020a001c0c005400c0307a40505400c0200700f20003107401924000300f080501800368001321030006000c00070080d54030309034152241020f00b0b010154413451400140350344407050007510507400380d400180c032500503148015000644d000c042d13105a2624120700c10304421061504140ca5013a0b41e01510001d8640f52124203000f141c0000050f00201500000c2c01c07031034900c001d076001c3c0060b0744200c540001007400c5644c8800400f400790b0300020000c411080340103264440307a40140079104a40720140d41d04208030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 510336798 1250 510335548 510335587
    0x50d06031509150b010c03050705010905012a05031b0913050c091e03070e0901020d0f06171908090a1d04060e0a03020703080903031b0c0f060f070f020303 68
    0xc0d02642c40c1c02140052014000101c19030750320b281c20134072498945000007842006929001410f000002c10918188a401d521070003141d5031010007080420740204242c4443e040b0b900303180e54044110010200802d1044042e64000c001d00f0034074a407480041d040101941d0000c00920b60003881c0c080c0500003229071401900c3c000d4060203070300c40d5100c1c900003d00005240c41240d004940b009800d8005494600141c614201c1d6009101038a42d900e480600078068801c901031600c02500340366001038541c503542e00c104210b9034000c154400241960000700d40b210700d4031400c041e40480b5000980080340d00344004003008003004295860341601e450b8006081100c11500c032103010014000c20040103501c1c482c000b20901101d0003481d00813840d0b540203599840c80e006c001d0039000d02160700c0d203982d2001c000742c501500b8007062142111091421060740c416400003000c2c0b2420703030480411480d00b8450210b030121604038100500e070407800c0e00e604904003900b94040341c15220401460701c40754600e040c0e00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 510338048 1250 510336798 510336833
    0xf070b010905011e0315111b0601050405100b071103030f04030f1502192d21150302040c0c0b0a06080609030f03040b04050a02060a030c2706050d0603 66
    0x20b11941030000601c03c44800b800d80c0c95481e0307141c4074144081044242079081c949142c0c070011440401130b450304900750080904850b103a805200510010f00c0020640b14145e48081c2d404211a0340c401c01c40204418061044070078003601042180b0101c0c105400f08817078008050b040700d180010715140300c28954402d50043d00d41000d0580c0110810907800c0d100746001c1e10350700081d070030030712108801c0c011341049181c84070074080342c1a0340c103401480300180c3d0f00c02c42800303c480c40340521400c28041c0128100d13509025003405499184401a03003184140d5925038084d0501700c014505540c24000140341d00100d810600c80030680c1c0d1710004000041d40c0344249200d5101243d0303145840300740c91402c240a410011140c009100412084602500760390f4402c2d082440500c00c1e03111428400d00b48a070031138010750003c2c0005030306000c60f43c040c3c201d40b0034035010359183c07090f601400c40e40d1950b29162000d0b4100d04541c2c02001c114880c0f041018000d0003140c1c24002940660742c1e550558007000000b0038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 510339298 1250 510338048 510338051
    0x17070302040303021c050d0b0a0e010b0a020712170d0e0f0309011d060723060c030609060f0109031106040b040f211e0f05150f1006090b0f070b0109 65
    0x6000301a8180f100c440c000401031900005c21150320700c0071740640a209840741c10165200b0030300c5256502c0c60719050003080c040c4001829540c50b680d41c9002070380106040b00140c030800500094094028038040c640603041304044041040511400d03d01340d00a202e0300c0d20154680840422240d01405400d1035102214002c1d9564a503050002d851110901412141130b07a02010303c01980c1ca41c441115000b0380c2c00a412021001c0c560035443c01c03615451400f902e030740b099404000c0d00340b004c00000d60142600f140ca004a5590b8102003010551556442600203622014200005103004100d1030b80741c00010030b002e06290b01e400e005881d54000ea4064a9078845118003002403441c010b684086030141e52086a03903404090300d072401003601e04003484e07940046500c0a44240041c00710080c174110b502c8015109020b0800504100072401580c0c092490075400010550380030300d4042c20800c03a8515100c8140003480c082081349035400402d000302032540c003041241c00082510041f5406048980700 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 510340548 1250 510339298 510339307
    0xf131a03060a0c080c0703050c07030318051509103501050102030306010f052d070b01052d060d020408161208040302040222090207031b0f0f0317070302 67
    0x301450034030050078840d0b500c0c0c03416212200c103da20204040d0311194001e0030981e01c80840c6421141c070300c40c0b51800202c81c000c0c1c0d10007000b0954003079459490145400032443d56030b9101c00400c050300085031586460201c040020500500703140344d5440880d4171900f0240040d0000071000d6134800310410b10984402100c40c0c614070940101e140c2c96014080a1004504624240001a150300b00c3c10240000384480031420301164005203c440d442140c0d4a4888240e10b503e00c1484d450f42c4d00008401c403423043d5403800100c4c4174103100f2206d5804030215100311040d4000e03400c0080204214046142d0011130801c001c41c054140c0d40020002403c06400400c43d4444644000000c180150040a00208040c2d02100411040700684054a8044800681d10b160b00402120300340d1084c100d50300040507600c00022200e059502400d0720900a45910f080807841a03045049481905402440a00c080b003100c1e010618201030440c00074803a00308150318580d4460210828102110440006500000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 510341798 1250 510340548 510340601
    0x60803040b12150603131e0f02030c010807051c090501050f040b0f01080d0f020309030109051b0a05061b12130f0501210b030c06030a0203010501111b0f13 68
    0x40c0881d8000b1883c043c00b00c034141c008000401c148800703401c0a24a0035028044010f002c800030f13091140b400e4610f0035144103165407a1001905240710000d92003070140d20b090b404035501580b2101c0c82400c007991014a40b01c00c00d20801200d07800d050b5100b41b02950f501c200000038000344a080d028140810011405151528200f104580024807117240001c01030010405030000140c1034221303040c00d0130840b00c099503441c8101e2540c0101e48420758103600304071351a8140f10300890410418a00c3d030201c43c440785030580a00146601e144501c1c0d8104200300420b58a00303030f070700070f4624272021500151202c00001501d500950b8101c0c1055601d05079228604004c1402e41c0080d0000600082c20004040b0b40c11b804020407818482f42d20940c031903160007500f01603541c240207412110000901044d12401c04034085070080d042405100d01084802607109000c140004441c6186d00f01000c040b919079803800240090050307501c20450b000381d802903400c00c42c49660300401892001c91507040c24401280d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 510343048 1250 510341798 510341827
    0xc02040213080616050307031a03060f0a181502130506070b0106090603140402010e0307180b1e31020a08060f060414153c0906040e0604060803040b 65
    0x1030724414501e0301300e40700c3c444525006010340307038424800d0400045001070f40e17500c03800c50320320f00d050260b15001d80c000701704841c108039024901030f5000c03003410864290799906001c02d8424111000d0400c1c1b04885004c0e030f094a5540050184081c0584d0358403c03680d96001260341350304142e10842e581640040103000c45907200800100914140c80c05000380300b1079054610a0f460302400290402c21208504070040e02d0400c04200100002e5015160184050300514002c1244c070401500c955500450700b41803002d641c4088902e044011320528aa858580d8035078190f525200811442118880c8824841126817028041e8a00c044d207600c02d10740b800504109034107509402c00e6103c0d11041c0001d00500d02503488e5101d100030161900d1004418038200c0c194640150104940c80c0118050221802050107181382c0145660302d2803c4240440e00715140582d0080c4001c841d04044188000c00c0480e031502c400c1c035002030018000081c642d0310b8044103802c0d0f034481d8000c040b2820000a82c0500040340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 510344298 1250 510343048 510343051
    0x10b0702220908072a031202010e0d0201020909010506041a1b030d09050c1815030a050a0f02120706140a030209030d0206070905031501030f03170f04021810090c0c020402130806 78
    0x151005c2e41c0c800c041903c2d8104011300304d01002c0d150340c1040500b020001c2c003d40c09209100c4c1704100311281c048480c90028082c0d403062900601400e5000000180d43c10a201540d042d900d90346402c007902003540e1714904050708100c80040d00580840c10fa520051000c6c002004800816000460740c4482800e0441c50420304803089401031707003040011400c8000c3c0c809056000400829000a03500207040003a00c0c0440150000d00107000d4030703001001b080305030311051649a20948035414490914a082521703821203102c3d031030203e070142c3d850101d03030b0444000401000205080042c103180403070006c40d00c0c107240784144e0b801603405a4180700c241ca405c02c0710040184021001480d046c060000b48010920341031000422010001141004041c014105c0010b044d00d200030503a46490198080103500c0320544090380a600783e040c21304640c100d01c0002c140b103100320000c4100c07103d00d030555007401420306502c00d10821044440100c01a51140000c0000c0c2981d035500411260500c10f406080140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 510345548 1250 510344298 510344333
    0x90b070308180d1d0a050a0e0f010e042a0b03091e0318101b210806030a020d0302010e030f040906081c030e0703121d09010b070222090807 61
    0x1500c3c0203d2050b50181c5510130103a51240c6882c07021001c0e02c041840101c09400a541c841c50316000440d0b6141254425485030410000c1c0c0c251590741e5403540003003500d007a50041d104594014140081c41e047c0040380074202e4115901285041c0d542c0140300498009944003002034200c074204003041011150815028500b4002a51800700d1040c043e4000e81c010542d404e00458815004005840c0214013107624164001886028142c0702d00c0c1c82d00e51021802c410084030250140e0f03002c034551050f81103902c207010140082c84c4220300794081004440c100c0c04200d003150b40f5100848505402800270700302d103019144507680c9950a141c01c1e1810748009030420101a407000710134a03500340c1c0c1140c50b800041c006090019525265220150500e10b041d08094003002041c848080019400344071030109815881c031038293f804d580c01c03c01890180130710644009900c00d0004401620b4030171484480a101001600a5244130020300700c165110490203075441500400c13010140060b500d1a11000d00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 510346798 1250 510345548 510345553
    0x2130902011404120303050606040b07051c03020f0a0302071b06021537020d0203011202090a0c0e1018030807032006041e2301060e040803060f01090b07030818 70
    0x142484203030b10130201806006002c15071a18040382c400e403900012207005d06035040074a035407100c040c1050f942c1c40e002c807a04e00d044519003248506d000762080c0b090702d403d0000005042d250500351071040f00650810002550100c80d020540400c0402c1c210382d01000300300307503009000f40520b050074049400c04010200703081c3d9610b80d622500c0440740d41d500484050f0480244503e55140d402020300240503649c0300c410441e200000204940078004980540c152085a9523801035640038200c01c01c0d6020040610041440300740420b19a1a0428210800107070302d00d0701080d0380741c0c0f0b4012000880d0700c42c3d0041d54400f0001901c00213140c0d08c00b0200300400380c002d002c0903203602d000b00040e0340c035030000300040c04840c0f4005100c140c41140c600c1d10580b694110758902c54000c01d80d06455441c00c645d180140b015031030401c0000f80a041b0341d41d4a881035400401c1142141e03910024040c0b61b4450910a604002c80760402141200c03c2a02400f0028000d0f550700c0c10600c0c1c492021102d0050308400c00d038440c0e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 510348048 1250 510346798 510346807
    0x9050a0b180402011404080d0302040e0c07050d08130506010b0a02010506090f04261b0f160905060d0f0305030a05310804050406080a0501061413050601020a021309020114 75
    0x124588281d16820960a00c1c24030f110b401e06140c0050b4600658106030b03114010b15080c1000558581c01030400d0318410600301c052510f5038800d0b203016120b040401045600161140422130340504200c6510035003668040454050302d03960136080c288241c105010703040001c00c000c0b00c4158248106644007600b600c0054640c00d2011031a0303001c00000b4402044420142200343c003c902d2000500c4155414040f0706444014a20701501c4c0107180341c060115500c05c4400c80320032108002003140038104491900b4480504007422440609002040d03282c10510305c00e4810000755100c0000d081c114003980d109030b22400c2c40ca8909041e210050011031959a00102c100541010203040704a044c941100c2502203602c2c924002000b40641d6202640c020300d00180028404004110380301a02d100d44020402d080e2208158409020140d1880381c001820030000c4001560170341c4850340112050044440c111141da000401c04240c2c1c4a03460681c94541030034404558020054440c0000a005400d040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 510349298 1250 510348048 510348079
    0x915030206040b030705070b04111014040b07021824061c24080c040e210c0a0b0709081b03060a15080f030a080a0204030c03020d05010b0a09050a0b 65
    0x30b40903500941c0d078460000800310300002e000307504580b1529484502d121a07807509007081c241c034000c43c1102d00d0081c002101610000391049803e00340010b4000d100508050416050701c0c45900000c1080f80c00c02c0300078204001ca0040541a58412048a0180030405030216a4400040ca55860250090409015160b040091000d102d60610a4540d00140c422104004000a28240d0301354a450000c4030101066490002c038a001c1101c00035102404020080340341e4694880c16100c80c494003001c07005812444191850040400300e5031001224007080581d124a010b44806840c0304000c28404803080203500f50601c1910f02c0100010085410700e10500003298403001c0007442140c0881d500c901441d9461501c1d100d01000e0700d1110f084480c0c24010309030315070303480d4401d0944e000403a04050008054617000c0c02190160795120082504a80c950f83c00e02000c0c0403018070494155480c3c0c5c3d41c40089403038001901d40204000200850b442c10280c0440c8211424110301d140144c64280314043d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 510350548 1250 510349298 510349309
    0x20405150c0c060d0f0e0309180f04140f01020a091d070c08210a050402010809120901030218100c060e010c140f160f051608060411120703080409150302 67
    0x1101c2e581510320301d658411640d0340d24010400c0920741c0040c00e1402c20640a1030000101811351404184c950712082100c0d01000c001d1403000300ca000c030254900720f0018001030b81305601c1940e03c2018100711000010304440841c20b98101c00b040400107441400c04100d1504c02c500e900007640301305004042c850510040c000c0000c81c502c980502001800503803919504448040418400600d10714000141000c0761070001a0000341c0303060307001900308000b15114003800314404c0840c0110010451403e82d0ba00015400394104035030000590800300c0500c0e010b41c42d407d8010300c566400c0e50740d80360744500310b162920485050010754241680b401c403e210000385c2103800c2510801b50325000703940724403d0030102460f500c113080e200d1804c440181802401c01c411406071a40941c441c100b50b5041107500558007030080d00901c51142d00d580010041804a402c8035030b024880000070f45402c481545031020f03a807400f00c480d881124a400006010803410703129105402c6141c8100095408880c40c5400054 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 510351798 1250 510350548 510350563
    0xf0a060b180a0b04060201020301030b090d05031f0e090312010905090703030e0406050a06050415050a0c1203140108100509010209010905090703020d18021008040210030e07090f020405150c 83
    0xc1c80c03081e0140d14406a544250014008000c1040c00d1503840e500c90b0b000034040e400038801190340340c2c00100464804c45000c14500f01c05c1246588442c2965200124444018200d280742e06c01c00ca600400450424810504d10380300e690390f030700115078804880940c200c8019050b0711002714140b44c00240070403103a010030100c085a400d841c02c0c0e0600302c180700c0060010301040c1c1c40350350b1004103ca030021b5581e4101006d0300c00c94144241140d4020342c0c2c0003040d100c51154140001c0050104032243c0d0014030007846a083e101c2d81d501d4002801c1240440c90b2403030030740c20380000350541e101022611002d002401055404501c0c0c00c02581044281400689501d545000d040c2c0310340c54140001e1541d0b4440d5054a07040442e070402800103d100914941004004030400e900910301001035102c02405140c0e000d0003694054160720148110320070440041c011449500c00e01c0c090b0940008841601e8050300d600d004061034016601ca00d007404000d007100614661010020b01404440d022410114070310 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 510353048 1250 510351798 510351817
    0x170f060106050703050c060a091704050303040905041e06020c10140705030702100903030c090e07080615070501020f040618030317070e030312010501080c0412080c0a020d0b0f0a060b 80
    0x16103e07071192409850502442c00c103501c2a200d0002084003800083e0400c0c6010b40c02000d601c022040c041644442ca44114020346806602c1048104032001c0d09902082e40640103005200003044195194021074a4124080d1180b903004241402c03070036006c2c400360b0303040e0380130700420060705e0040610740c3c84008006054000713002c0c02100080501d40244056084000190800c00c41c101003458040c00401640341c4034800100c1511010070f002000d44291809160640c5400d1119580e00341004a00d00700c0d1354a032954100d040c4030340c000140090000d00700b44042d58494545850800c080201200c0d1000c0e00c90a4510120b0f6041011941124a5801120300d400c10300301507a580000c2500c1d0310355250600da801d48030014844805092810b0050f043e28001d9031281d14039100d00052545078019401491401d00c5491101c90006816000030450f03401401c0a8900c4055107800080c0c171034955032001d4401b41c1c140303420414110b46c2445015840312046204010903420301030520903501492220 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 510354298 1250 510353048 510353057
    0x5040605130c0509030a0302210406021e0c0a0608060f0604030b13020d1e0c0f1805090709050415050702060f07111204080f0c101e05040801060906170f060106 70
    0xd41e0000ca2090f001c46456401c040c0403142c20815a01d0020740d1114000f0340480b030540005803014290000200b202c0494260341e008003040c88281a10162080c4207410a805611a0302ca230404603489030344c0b11900810403600c41080d41d01d00001404046c9809101407480342c10200402d000003501464400c0d0000c024401070007401030a0710104562400c5004082d0080c0003400c01403442c03807200107515840340e00c10030707108401e075030f98a9440e420204a409280051503d04030f5021950380140d018982c003650380001c0f00e10040ea148400c8003110010354054400c0c810122422692075040d0068a800c4600ea1005242c24501084040e1060724080d182604000c1186c0040c1c8203a98200000c45039480d0060016030744036a200e0100d5911603034008048803070f0141c0c2c0c0d20105245007558682c0d6080501e82c9507a100080c507100b00d01c020050b0340e5109000d0250902010030b03852424402c3c01c0c061320800c0760004190303040641000d940d84e1101001c8101e50300c0352000e280c40010100d90941102c3c0242071 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 510355548 1250 510354298 510354311
    0x1050105150708040e04230606010f0507230708060106020a020a090b01020c040509010f06060507050d050f0706060303030c090b130303080606091801061b050d120b03250504060513 79
    0x100b51000e8407075a0701190200c05210184014032540030741d87c3c80b120701280f844030145034041d2002d580303d05040703d00720702144500182a40d11030090008111461160403011a81458021b1141c84032094000c0c845103944083c2040c4100c0d04200301c60f40c054580341c0005d01112003140d0002d0302c4000c0394010044040d48800d02000264020811480d01e41c40082c414012450721440b6103000700589150030407034a081020000301d0a00600448400136040750140560058404013503d20354130880a43c03002100402800001c18124810000614443c0e500852003207241c8e14020803c900c035420985a2420400c61000441101c0075114110b0f540340c14402c031565110000540c550086030600340d04401000c0c45103880c010341035810350583d40c02d9103070032490a07006403405498500f0702a0003400366015001d04880750340640c09102d04450b45d00300100704003109402180c03e102ca1100345038200301295640f10a5071265641c21000b50005480400c9114500720000c4c541001031490300741c0e9140e503001c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 510356798 1250 510355548 510355553
    0x1501050118092406030b0922050f0a0c1505092404300812270606031002160209060d050102040609080d2d2007050102070503010501051507 61
    0x940460007090350b00010802d859480003d15000c0d42c2003428810240d00845001c1031881c006e1144c3d524041d005408a01d00e075550074080544a04008251243da584c0c03114806c0015504021182c4100c4208010b424600b242d868805405911900400141219070200e000095840802c0d5400c0340c4040750215105030440301d06c1790f180025202410b1a10200280c0072402d001348809414441c8801322407811140005040b29000c4250780340028981c2404020b001051134074100caa80d08840c0b000181849206600100c195010016000e0060340d00a00304102c1540780502050070714609000f02546881e0358440168000c18000381c009200309076200224000391680401e61707903407a5004002315034980c0c807001e002c0d054290070b1044010603c03c0b86550010f01d40702d1004140300501804801198054a42c515481070790310030f0800040040e01214035916882c80c00220ba0003c1921000d8010740d81030100081c241800d6402a6019038109401000507496842305407010420118905440e1580391 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 510358048 1250 510356798 510356837
    0x60108160f171807090510051014130806090708060c0a031b08040506100b0403030f111510091104050f0a2c0f040515060f0a080a05060915010501 64
    0x5402d0a04801001d40803c003415440a009845000c82d010864003a5a0390b481c03190141c94080320380c01e0541890b10810040ca040c00180011540000c1c00d200381d140007005902c0e0060b4001403450003004072200c1c41008107600078418242c1103c2c002c0c010b0107070603081105007951190043e01d0801c440000041854516110340c2c0500a004080b80c8522960100d10100400e03401c0103032815034917400f0f91404141c45069250311030013200c108040f16401c191551b201039030611821076007803080c08440c06105507002c0c01072100700d5014407108180c664030b041070800c0d80e1004a2a400072107030140381400244071085032005984c00c450088691409464042c4045064207103281c0c400050382d05003402000d4845502404403018400c0c0d00030116080d503da000704400343c4815079026045400c141c10b1130150520096007640c3c0300e00e029043c0701d464403980c000f00c0d081c4c00055000120a4101506010800c1002d000998120744175070010162030008080388914110103110f45814400c1300e160081c2c040d0043c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 510359298 1250 510358048 510358067
    0x929100306050d1202070e0403020a02040c0306320103090206031803120c0d0f021206010c02010504050d030203040e0f0405060c09030a0b01140102100e0a170f07051005060108160f 79
    0xa80a103403e90f140e440c0ca0f0310b482030301841420140c0200000481c0d80700d541003405104940590040031050100d400340b10040110700c845008240e217840010030108480c00e07038a00c04075103940c0d11866100300c032159441056590258181058148a0740d0805a0740d02000e5941003200007000a10708a00c2030100341c658451141c03401c0107078001404000b659034400c0040c2c42e0003889043c00307101402d02d80d00054201d10944500c070482907000004142194404d07124a4401c80c418105a483c1a40310400205d80440400c001c4005900000742401400c11104c0c06680208500204d40103e017010364405468500c020844000c14030045030000541e901048880007440c0c03c131070090500d50b12041180000c41d00511150302600c5072200003014005280700301594079101c0000b41c00c500d601c5940b1400180030000c0c25a0900343c1c03e0020325854003c400052030710510940003400c1c11010596104141c0340300905d02d60500902c04100700c1d02146410080311181081c0c82d00c082008100441030342c02d40e17030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 510360548 1250 510359298 510359309
    0x60e0702060108010506190303050319060b070c120b0c031312030e0c010c0b062205070905180405031204020d0b04030f11010e030f0f0c0105040803010929100306 71
    0x1110018010040d4022403510305030b9400350001e00aa036603407418040d8042d204c604c10b0f50f4030403030400d040000c68403a0b00a9038110b0316a840d40ca0a6807202002001556900d421081246000040b43d000700101d100003400106504030450507001140e88507800749070700041080507602000800981001040301055a9041c0d000810406c1030154000080040c94086181d0311603104c1d03195006280d6000c1c012030f1191562291204115030f81e4030081c03142c03110156030700d016a030b0301d203402c00682c03200903003c0c19104085a90700c0301c18682c908010851b00050011000b50004d0f207076010300011910100458403c0c048040018115440314400b090490b102e60380041e050316003081c1400308155004003e1703400c10b040c55441a100068010456080314003001da080c001c2e60040000c24421035100010701201071006072910b0404620f820903d0a40b9400c90382115000c000200500500394240b0410b006d41c20403030290396025129004010f006003c050f04180b05000324610120043d100c0e4014074054171 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 510361798 1250 510360548 510360569
    0x31e0a0b01080109200f04150f03060b090c07030212210405070e070207050f0f0325030203150609070c061512050d0c0305030c0309031201180c0513170106 68
    0x181d440b69501e00908010008661504800006003461300c14052490502d800042854194020305010403000340384107444010303113a00d5054001050b1349800200ca00039802132001241000c2d01d2070412000b40002000a0101d00e170070321000e804030380d000614040b0450b1103039285a43e50100f9050054802e080c0458000c0800044100800c000700171900e0130440d1203031001c0d407006440300c5400fa80c65003028021107030403409100d40844c442c50200d0745840c03001300142c1514001c0c400c540d0300038000e00303c800308034036205030380d030010811800d04128082c10110810080085414403000140e9290b202602000401103c02480001d0104031ba0004025016921381c00b91100d584440c59008a131070414150794034010354620700d251a00990381845450703850f07500c0700c0c84c642d5000c840b04010341021784522124071040c0001190a1120910140031307005840d03039084104c800c510400700323581c10540d000007085401d10040c4c1c6480082504075040d03031007502c800f01131140300181c0d642c0180441d80c0f1495218 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 510363048 1250 510361798 510361801
    0x140901050d1109040c0509101d1c0c060206040308070c05010608072607080a0219080105010b0d1d0d110a020301150509150d030302070f0c03150e060105031e0a0b 71
    0x10141c0b000100000e0100b43d0301801000007246040e07519006000713115400460000ba180300d0355100302d215120051142255085409900000c146200a0710940c0c029200c18600c580082c0b101d22001200145030510040100d4a415034006001b54400307452402842401031280d8100070b0207401802c0075140510840c0e0b4044e0f65803070702c0c0907032500c890391a5007940e01121111117120b0001c1003002c09d0780c45940023000840495801d118003000348503918148090080404102c200b028008c0600074006001c40c90f03150044621207800715484006d5400c0444000703105603407130b500d02103030307840143d42c490030041c03441708070380712042c1c20326083d042c00031740c9940790004201307001d0350404001041d00c1050307845107055504c1400c4900c1da103140540c17060348004683c6060000900c03c0d0010050248079400c1d4201c1c0e103090340c2e1201c944101a07001203c41020a800c11644080f01d0702c6290024010340c4010140307549040c0110b600c0d120611042901000c0c41c0d40350418103401000b40c00303d400c3e808524441903 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 510364298 1250 510363048 510363071
    0x7050109030f0e180c0304080d060306021c020a3002160c080601030503030a1805010e0a020f0a030804180b0603040303020901170601080f070e0303070b0421140901050d 74
    0x242c1680072040403508596080c56035051516441020b0342c10700884011545841d00c00c6406a000103100702c5662004005101c0b01c401d90b0300801c0000c0d81304601c05078507440d9003440d4048201201d000d40f10b0052046c00004a401d50080440c044580540700d5140f4000304441c07200a140807003031280b03058500010f6501055642c0135008032420f40141c0000d1b01c40703520b43c00d0141e01d48400b0308c0050244d51042c404650303440380e503a101e0311109036039031800001c03103245945050075a44040084038482c0c0107440c1040c25030810554401000c4011100c1c0a100760640d500c80015000358090f1003034404030300c80751003c580c00e02e600c1502e05101c01400c86890f441e20345070040181d07012500842c0002c66240c001982510062499030140e6016100e0b442d0380c1d0303030303181c2148a040700040c030020401800305800c400c41d8070144000c203103041c00b0b00801c6040e441e16003000741c505040ca489041c940400f080125090365800907401158414425400303a82d0070031500129150f00490845c5022a0301d0883c41860 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 510365548 1250 510364298 510364307
    0x100207050c09060102070614090d150506090603341e29040302010507060f02030106090806010509041109070c0b010f031a06010e040c0306180e101e0c050705010903 72
    0x1d407038004a070720361250b566a03001281c64407520320038600810410403203100c4500c030800207084188005001c8840d59020f43e00c4174281c50842404011080383c0d100b0521902c3c1c02d000000c04d42c03000c81500280030741c0410000c6400501030340801400740f05404c3c00d440307818101100029006084024466601c0407001140e006100b5540c4228031410341c400025803c4002c40007252509039410200e2030742040d2443c4c0064401c1e52009408480c07203940e46158140610041c4061800b0700351941c2d54100203410044050700e80340060300005e210314980380c10032000540525403084140300c143c4e5040c2c1c150712860b800b92222002d44d50000c1c01c0360550000890411400c1540804490007010882c2d10130886c20101c83d4195015a901e500154860b0340c03019080c217003a006845d24880b1031900251075552144a805400d820b2564110305984030200d00c01403070802c00903503140706803071f46003040f9242903440080900d100c0c451920540e6912401c01121690181c0152849603030030900a002180083ca030082 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 510366798 1250 510365548 510365563
    0xb0915030f19022809020301060f02060103050309060705030d0c0c0201030b0111060a1e0501090207021815041109060a080901060803161b0b0a0305010501090501170f0910020705 78
    0xc0c00380c41081c00c1c1c04002400018660700c2c141400086558495954007440b481c02403e541d2020703e60400c07221001800c210a1020004040d06100140c8035410310704020010081690301004561060006201140c07001c821110080000c840076962b0b80014a822411401010dd142d05814684a5440c40c8103803c45a4103031218402d80c0c0030014440340c02c00541d096241441200000d41c040000101000350b5648071045401c80c00d0801c0c2d540102504c080d40c180ca1098211042890b0003060450450810170510100c0c020700312419200380c034083c3c0c4802003404a0f040f10512480e00c0e0103207003d150000380c0c2103408060014140d555181052400546035079015505d41e00c080d80f800f000020403140110a54844d540203116485c0406c2031a200c0038090402045100c0c1450791402c00011190f00c0c060040c004c040e40f545021030690304d0b1000140072040564403542c10301010305000846032102a9071503a0101c41c10b000510151529884039151400e00603400480c0c620004540091020008099 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 510368048 1250 510366798 510366841
    0xd0309090b190603021c020a0f0e030313030c09050a021213110a120b010b0405030a032d0917010c14130306020c0f0111160b0c0c0115050301050901060501210b09 71
    0x60071050241d00182089121b40711043d000142941c148100312440ac15901d47c0540b40102200d08003c01684e000d900314041c2d500032034102201080400c4200014001c0c10f0340019181c00840c02c1c0b1a100c448220500c0b40100368610018003a04185e0070458000745400c0a06806001421110b8a6000940c10245005010303544070306046c00016071120504211000c5e12005400341100d4602d0b030740d0668480d0700707040070f0740c100030701e4102503500c80115000b01c104000b2490f51000b58482c642503003048420780700c0c181401280d060200d4000b0003500081c0941055000d00c103055900d106610f40d10354a5401500018001e900002c2d02c2001028006460380304401c40400030088803194140004062081800321212501c0170104c990215201020155000140403035961601c3d0700c4090715421500500e15200c0000c1189500f480281024405d0561142c02031000308030b0b890400c000a001c8400254680c001c24041c07246041c881501c541042d410004064401c02590810300b00ba6662900355213540d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 510369298 1250 510368048 510368077
    0x17041d0a020c34050604060311160f020907020d020304030b0a0e0a050d020c0d020a0b070c09050a0911030d0c080a02010b060706090203060c160b0717090d0e0d0309090b19060302 78
    0x1045003d2107107000002160001421a860b1601d0101d058015001207690303a8a01c0b4002e0140740b104044412102807034910030040b000208200d8410822140c10251240c411544152103004420360004111001da030340043c038404650ba60411080c010b007103249c0f01d000f103a0050030a05401c0010016140709501c40c10340030782d000310354250103000d43c0030201c1c6400b80d4001c5d142d007070810030015000c0090034814051000c070901070f41c0318504031055440540f801601a83c0d02c4421320188507103400030044121081b03025200b007030b031880402000311442490180a88130000b0b00803c07030070b0007580720211000300034004544500540c00c1503002400c24038004c5e40a4082c01c1c000443c1c400c141070440d141c00c90031410500c0340c8061910780d040b005900900181c14000900650f82c4561284400280b08840680013402c0c0031a51503030041000b0b80b400010340c0a09c5000d4041400240c12541b0b64040c2c0360358000008001c80d038030001a445040381010750b03030a0240e04d00d01140e640e074980c005000d0a0b05ca0a00d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 510370548 1250 510369298 510369373
    0x2409031808010e121821010b0d020306040b060f1201020301090e0106080709050901020f04120c05010302032a04030828020706050702100309080a02070317041d0a020c 73
    0x7155800d0300c1d80003240902036002840b14801d10440800039004d8002900c03d42201d1815200105442c0090810443d1318201003554251180009020b0321b10b81000540700d0112002c0246e01280e078854003c2c00040a400003800042c415444880394207100000c010701c000d00160003014110f000b54001c0c05440c0302c150410f07070003440d914014010401180d03104401000303d145400e903c040100743c003810750003065400f04003420040d1418005000942048465905141550318000130f1040c060791250341851300500070007000030807100c00243d203140340c603030f01140d0349000b0001c100f018800c80e00010a10280811042800a061140700900540003a046103200032040030070780e62034450b0305c6050005101000340c00010309007040011481c15240c14041000300c004c1e0350b6802140c01c440081300041e44080d02c10020300060030103240740c2002003030905107414140511000c00c07240b011091180d071019880428500300c41c44d030403281c03c0800102a030350300c002e152900c8200800d0f01c04209245003085403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 510371798 1250 510370548 510370559
    0x605030106050105070f0507120602040611060c0412080c0a0305030f2a280e10090509150319051c03141503100f020d06150c24090318 59
    0x418a001c0d208140c4590742000c05603650002c0d4100c062a040311f107802011000203443c50b15255101203188500c1c005a11103040010082141c3e01c5c0d4082c5001c907611100600c01c80b98103043c00c0320140c0f4551002101c5100c01e43c202980e0500c511503050100c0e00c200344081091541c080c01842c0514420b4900f0002c1d43c65144580d40004c0385010035040105503d2158110020301c0401400c00c1c0911003c0342072105130440c5200c4c64804105c0010340841c3e410520380100d4070f0240074000300700360b260070844581030910020a041480041c0f024150000300506141079560400c0700c0c114042980c0b1001442d12410303e03100d83c60f03094100c0410100b900c0e020035002803a000e8003441105050070210412556103032451000742084003500705401d8020f5501c500003c040d540034410040565510142e0384120f011074040460f800c603804200510000048042c22540c4103403070b03494140d0000c41c2903444910b8405441c01a9401000c21010b90345843e40031020180c002e001e550000e62240c45a030000fa80d40e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 510373048 1250 510371798 510371801
    0x3110a3311031602040b100807021608100c02010902120c0a0626071b06140c0a0c030f1403040b06030615010903020d0c0b0a05030a0c0f1d040e0111090406050301 71
    0x10619681c650308144141d51900450310016050780e800148041010801c140c003041115010321201e10010312640e00f0404280d40420203c07480115021121170210328020345581c513641010880003040d03803a8014100c40c2403003500040031407034000b8130301e03901a0714100c5031a940301910fa21701380c00740b1414100007600d2401a07506c0d28540652011408404208408010060b40018105c03002d0145c0314103554882c020128070080030310b00c282400602c400042c441c0b100512030081140704203030820440c100e48103074800c2c1c1c0d00085650500b02055000b4495000342d418207070300841d00030090008001c1005008030810081c0c0142c3c0d01f50181c544070344410191004c480c4c05020498082541d1500401c0103003045410961014003800c603030300c5010b84401d4203110541c0141c1c6410009000807003403241140d0188621420030401d410000349640c0c00c0c9202a024280802d141c3e042141603d40c244260f03211500031041012001000300580700d5171042c51041038102580180c0503a15154000c00e0720f0905 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 510374298 1250 510373048 510373067
    0xc0512031309090b01150201090503130603140108032a120706050a09080405101106012606090d080a2003011e2102030f060c040302130c0903110a33 65
    0x4041040d13816070a01e18000310603203010b8508402c640da80c400007400300c0d109202401070403039040c640b035594902c2c294005043d240c20810107401d25924034010003129400104440000801440e0b44200180e03089007400044c3c118040c048090194108000503680c4050080443c1d41c4180c80130415502c0308114401251001d241c018a40007040000f4889407401e1065003280e25a2480c08440341c2c0c0040d40400e00b4035100f039002020180c240030000102c5000790719011513442d52000181210b10300200c0650751080d40d580304c20244000300f0041072980303075240c010300c016089072203114424549680400316140d00911440210b01d41d00c00c100d014013203455810f1400ca40c544103181140480050700300c50341c0c0d05a250100c0c1c0c1032044400c616020b080c01d20940c0d10481408036115110313032560052000c4a146030245d5259507140901d030f0b01002e90440b030810141c9402c802481070401c14540400c403031070b285400c502c00100424942c25410302d0071510324ac1914440f5686c03101c0c2d0b07400c04130041d00d45442 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 510375548 1250 510374298 510374303
    0x807060309031b020a0b0f091905041b05040e15030114060907020a0302060f060d02031b010e0a03050d081017011a030d0f080603010f0e010203040c08160b070c051203130909 76
    0x4680c0010880310b40300a0147c51500f003e44040c51404800e00300094000391807491390344c00b21148040c00c100f45c1c07426119008016108d0f51951b10685100800200148200e0084c1002a00340401003203480440c0142c0e0941c2100103802040203c483e03c8001c0007120045810070301c6034142600041c0b0701d62012610300d000961580003442103480ba100c0c440d80000005200c01d411440c0c40c50300c0343c096a020807801d03001d80c2c0c01d91015a204d1810030f000500e480c001000d00c50148442090410001d980010000030190070340c58008250f0720f8a0354001d001840c1940032544400c0c1610100c030300110198842070701030115581d07804100000206060300c1301d882e00c2e0b1034408504100040140c03030340103990351544040000c00001d015500000ca94044440c0c413070181545a40c08001c010400004445100c05020b0304001822915006c40d40c40300180010f001e09000d40e81d004c9408030404c48071200c40c5001d0000280101010a11184040d45d2500304414090703510340c182e080007d0041461144244603038 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 510376798 1250 510375548 510375559
    0xb09060a0e1f0e0309031203010801141509090a0b1608010515030c031909030c0b0a05010803030a0c1107270513020418020306070801050f0102010501080d0305040c0807060309031b02 80
    0xc002c1c450140102501c9190b05014082002420380540d070600c280e058440000c80420b0701da50404480a003180c0032002c03081000c420100500124a1015a002e000210204c5091a00b566010701c800d05044103001c2c0140100f400c071003441046804402e048140035070903a00c00405a0f41d901c10400b6038810110b403e01500360820201d0404000d05008550006040010810340d40b0b004035000c0858240080c10350000c3c459030004410861181c0c01c60390130101118082c070041d410407030b1098907440090300c92440252385aa1801049001d20701c0e10104041c0e180540e40a40c1da140c60440c810840001c0c2e5480300980c1044000039840c0d01e105150056600c00c548010b8401d03580e0078400200b18406548101414412407040141e5003002120300c10080d6075a284002d505d007405100d660001a807804e03055904140050202000028102303001000601d00800c2d00d07151810314006d101c105400c000303800c0c00358400c0840c002c2c1c0c040d041000650320039950002e001d400d4400c11038218149940095102 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 510378048 1250 510376798 510376843
    0x60e060f0301050408040306180b070e040b1e0f010309050303010b09030d0f0c020f042c0c0d030e060706150e041e1211010f021605120304170a09030b09060a0e 70
    0x71180e074051403c4089d4451050703d5000725807540c046000c0e00321101c800091046e0250380b6103050900821030a2401900e845089042144030006150200b812103401a004040a210030740c0c401d4020a80031600b10059a60784c4d6115850071800b54090582c1a01900c07d0390b240000d5184124a07200307851020b5034070300010008603400c20801c06c40860b081f0740d000740c07030f0708542c90071602c007800804074002d080300845800c5184104941c100071620344140c3c82002c41d600c00402083e000100b840812000b111800e5940c1a5440d041008090b08040c8000f403000e031080204084c0704002d40c840c051800b5940c0702000300094600501e11070001034000380b2103181040c1103815140500e087c42c1045a03004c0010810004000d0607000300e80144031200c1482c141340d48000c00340700080c481501c2d919a9021024a145419180d8180081323002402c0c001306940014075161251050002501450780090016800d00705550031945c0c4078004d0f5008450076141003064500c8010005a0700302d180c851003130b110b010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 510379298 1250 510378048 510378053
    0xf06060e0412050d1b0f1701080c010e13140f010b04140d030207051c020114040609270c080f071e05160b040804031403090d061e060e060f03010504080403 68
    0x440e048030204001142c0c950082091803a810482c07681410704540c0ca00e4501103039407000811101c034104507401f000903880010f2103e00c40104801c482c00c1e00c00c1c242140098100300200d14074403441c1b02c01c10342d02c52a01c441a41c5403c1c401c407140303010f54043c2c0c80452450340c03030392108180c61056124200c03210382c41c7c484c4c1d0500c90038940700d030001143c0240152002c0035135a03004549100c11140400c001781c00d5807c6c0c0c100440d03802005800045c1320f0340b90340c542024185000070b00707803510318020368484994100e22001d00024207000c4c548083d5244009005000340206c01900e003031000e4602c054000d01c041c000030b60301841405c0b480403030b00040e40da00c502c185c14080d0650300c552000c00d408800840544030303100428120100301d80202c0c49410f04540d598594200804401640c80d400b00407030f0410002e18071340b65a11410381e54541d03003100c0001501c03078600a6100329450740c1403140c507509013451340005012400c440c00510415050b505042d0100d115801c15081300c801301c2c1c00404045050205102 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 510380548 1250 510379298 510379307
    0x260706120506040f050a0f0c03060320060c01180309170717010f11030709060c0506010e19050709050405061c080a0c0b04050c0406120203060a0e070b070f06060e0412 73
    0x400620241001500d004e06081110940717204032071991500d5158005035540148a126000d01c441d842d250402241c0d04640c0c0b05403852107400f40180380240d48844200140d81c0d200221042c007540b0340e008010400c0310907480410b080c1c5518040c4c1c08151601030000303545041e14207d00c0108540e07030280004508082c50801400798010000c0c600d9944c415400d20203080600c1900c2c101c08920001c00c0d00d80c5031460004103540c060303030403070801c01011840810010340001031042c1940e509045070640f543c6c07500d03400b000014604022184450600b01880300300d5070031180040503a10182d800b4446035840d0424805001c0000328050070040d244e848000200d50440c0180000c10b94615040084134010b480e00460401c1c280c4051300c00c1d41100724554024a01403090800038004ca94038003103580880d0300000e44820b001040903810f162600c0d002c00340c902c000c2c40071501a0404c0c010b841e88800541c2032045c0e900f06140000c0301c40501e05100400d51000c9180500c0c4501c1c2e024a01d540c0d140940f0344104c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 510381798 1250 510380548 510380551
    0x606041a12120c010501230105070624030803040c15140715050414010e010605010c03050306030c061b0c040e03091009030204092d080a140906042607061205 69
    0x41c107900407481000054012840200004140640042640d50422102d0107042a040c445071340301402d0040c00034641d076007200c291240c06410000004256480741110a8400243c50074030440c010b550301c01004200c4168041d5000b14055441d400c001070311610003144021a42c64182c01084082c0541007035400300b04c0c010240203109100d0000042400c8111100341c40c010350b42125442194000d0b1810b50000f4407c0351f40c54104100244081840d000029221010581c009801c203c400000203541344c07070801c86100d09440103009943e41e04407e410000600030340c2e4017042801d00482c850000c0703a00d014002c02c0030091004010703520f410358807403c22102810000000081c01451900000980d68030311807201a14040c0744d012951500c051038800b503100180400d6003201058860603c04a1002c0c010342c0c1e408509400c18901400082d40002050700030745000b1580003000081c040342d1001c2149207406600b504030310440e65101c0c214195900d0b95028020310780015500c0d138104c0c128100c5500110f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 510383048 1250 510381798 510381829
    0x16020c0f031018121e0e030f0d050a020d020601030c0e190213050a05060313020906060405061b0607050a08040b060105251104060e13060b0d05060106020606041a 71
    0x80e41c01d6090baa0600c01a1103048100d005048a02d4100340240913070049031440742d46591610b42c1a518280d116200b032406000180402c0140c0b2080010007a02c0070040c1d0560786000c50b04503005140c10342c0009001e94041008000107000c0c4100d4070440c0d42c00062600c0c140ca50010040448504005404004040003040e1a8070701280304544803e2884920041181c1505040c901d444141440d040c000d440ba519840640030340000c0003040b814002c81348035400c4065044031014040d88400d4005482c40c080c07508180d500030000140c0305112401070004140c292400360540f08075549819003a1454010000c412001c90707081c90028000980d11076409502110505207a030424000310403182d4a5030309858011000f40d211000a0140000160700400d80c5c01b040701d06100c65030806446118a01001d02181007130b0003400c0e07100b003c101058005510400000d080307403000b0481420120750758a400e110703100250083d04042245420580070340c4079105e032683d0740308610455a00501006546a1190 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 510384298 1250 510383048 510383053
    0x30b061c0b04081e0a02061504060803040902130605090d03110a0b07052710141b03040e06041104060c030e030f030414270a060e0a060303020616020c0f03 68
    0xa90005601c0c2802a4042c5024044541e224800b00240001c1c4c40611140385264220900040185c19800199150310003618030000c00b5030900e01000c80d001e003003141c00c04001c0d40030204002c03400851aa0151050003a140314070500300c1d94550741600e013442000012604400030841c550040303405421403c10841c60781c0d040f01c142402c00c1d194400305a4007a100d20000800005000003440c0d1411a4119500312101c4094090005800000c1c8454580c0b0071800c00c0c41800520684c03504a40b1007603074200c88c0c080010b40300401154801e207440c3d07400760140d48021100e0f400401c050341414400c402d480e01da0012118500b6080903419140101c4d0864201c04115003070f101c4040c02c0d24103000ba00c06010030780340190b0701c590904030396003000c80b405191710313004618000c0601450301c8103414254808070b841300040d003a52550110791010f0301007500405400c07089001270069600c03655100e60200c1c1d000342d0a17943c0d0b035200c403290341c40c00c0c2202141c40c00050340076401c1c3e40a2407800b030781c02c68101c8400604 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 510385548 1250 510384298 510384349
    0xa021501060e011b2102010f1506180906060e0a092d0b12010b031504050d050c030c010e150106050921010f050a0b0f0105040b030a090614090a020a0f030b06 69
    0x2544034101c0d0016810301072880360004900717402c5030240541051402540303004c1c8000b4002055948010780d00780704541c10401d40d8507100046444070141c2001501d20403c080c00300e9512004064000301d07a00203800e005500701100090300e000c10740b041701c400011402d40c0d00c1d10000c202d414400c0400c520f80c040c4c1c000c00d80e24992a0501d6a1702105540480900000030a00303840b0740f0101810300e16500c507904e006400368010040082d50214089000407603505000d070f01c0303207122480245180120303c4510810340ca00300f003041d2900d50000d148040810720b1640c1400e50ba80b80c2000303c1d21800b8003a061a00704008500f01c02054403d56100c0e9041c1ca0b4041c000a0f900e07440a8030a0282c90741030314140c442039500c462451030350800481108540c0403c1c200646824a480149103441c40024002206180c1c5c45907040c00b0044036400c0030214603081c1226080300c0c14035400e030646803007540034100d118038210040003e4101583c0b00041c100ca800850f840075175980d150510010511034594940500c0a112 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 510386798 1250 510385548 510385553
    0xf02120406031d0d0c020901080307030e0603130512031006030903050703030b031908070b0906041509080904060b131a12150607030c03020c03010204030f030c020a1503020a021501060e011b 83
    0x404d405000100343c0d5042d01048060050004680060300009010740003040003c0100c1e4002086131041842031f201503550356500409102c03590005500204540509000000b01c404001e000d140186028400c2d21080380d9900d00507002c80c1e03c54540200429401e108c41400300b4042c1d880384004071009030a464109200c500e44003500500070204642007a804141c580a00100034002507002c3c80c81e4004000c03c0c101529844800070403039441c01d440640310790400c420080010151224041b02400a120480e03d40b2102002500600804080d010340c10100080190300075900da120708542403201ca03e070505840c1d1118400f640140010800040d0500501e038640361440107001c0d0900a07514148100703064900203003002600010288a40c1c01440305101081e103003100e4108056260800c60000c1117144042400b0740f086501c04c99408140400c604801c2d40c0540040c2810b4040c0d50039a07140c24251101d18845180c2030052500144000c2e0074901d0550160030f0501000c00c0d84000782c01100401c1d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 510388048 1250 510386798 510386803
    0x40b0609251116060e0a050a0e0408040302030102030c03010e160f050c0a0c0f290d0f1b031a040207051b010c05030708040e1311010e01090f0b0403030f02120406031d 73
    0x100c3e180c003c4030403900c1000240c2c1d104002465803e000c54459294a15000004420001a01410743d440040e500403d003045400c80c225002941c0c090000c0d5141e00d0031403500c0160390024812080d10f08a01800280b141101400d445e80400d0207407241e113441c6d032010b0003c4442e50040120425a13108040c031041c0881c25130000c95008200880491080b2410150326050445142d020721403240a0348441d9100c5031030038001d4400034142e81034006040000380303212401400c290601d2139010644842c20008943d40764029030440328420a2100100440b0800c0c44200d1243e0400584030ba0007041c403400c8084c0c55111284070482c4140340241c00c4045603101c15080d948160000c9545140014007042401c90400c1d000742d1081010000c1040050700d40c5988000700d42c2003070014100800841002c00903070207101500054111a60382007042500c030940c440340d540c070078002a400310f0641c404000b0023507c001810707040c0c006601055400c092802400b5809420f410300c030020b0b141c10305c0e0044c034041c5408 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 510389298 1250 510388048 510388063
    0x1030504122a06020c010c0f020705040f060b0705100b0d150b06040b0c0607082503090201030f09030504051306120b0406060b0c031e0c0c01120906020301030506040b06092511 77
    0x4080c01031707540114044042c00c41d56405204001e1204030800d01501c940c02043c48021100c0139200460445c101210b140700500454004103401140854603a0030302a00054180000c41840020404103120008002032152020b4000b4005c801021080210404917001300d003050401528490030280c8410b000c003010b4100d0015900564001c00812000c103901c80030447d000a81421100e1481e0355241c0c486007209524402d0700245601c5000c10340c21648203520088084c90102c40400142c006440c0080a0340d000b4071540d8814030065000d80401c01135881030704222a85c202030a01715030417680d00c010b5a40b000070700c03d8410580d1410005040d141200042c00104903140240d0398501c082030b5903403440c8019041103681e280701400704401c609030028483e2010f080c01d01b01185071401c0c1c51603c00141000d65801004507002000002c1000800100203002e644076014107041075441d00103000782e150049443c81d03141e4215054150b0580e490b0f1075100c00250261406070138074298154082d00c0c0201 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 510390548 1250 510389298 510389303
    0x4020c0a170a0e1005030103110f0604090606080a02030f011a0c07060306171b040f060510020a02090903181e09090d0923010f022a0f01030504122a 65
    0x14000b4008484030b40c0f01d0401c0704192001c41d22240c1c80070007400b0040060105000c020302080c1449a00c12103035580c150704000140c001040c4541d2540c4809801010300305c10b11501c0c001c0b500d1140880c891010f54000c1c0e900c40c0780c0300d00c941c050b6a0300c0c003040c04000c3c503004d00c680300c20500c041148444075031051000c100540081c0e100800d0140c03400c0c41c1c4014040801c0030000158000c11031110030841906110680301508036408a82607072000103140041006901203548400a90540079403d5004522402c005000700e40e00081a60b50000fa05d40301d10620300b54050044c0d42c0c0740c2c4041149081d01000140d4583d0036203001418101c8008100e10b0801510a10041c1e400035903104801e513804034000300a0465004400800380d02c11401110760303042c500c1c5a40c1400340303550480d0061072007001200d08001011304040d2058183c0c00640c500c00980c110414060400c2592842c400d5019004079401a58070041102090780d00e890112400b09003685214030031005030117068280d01014a45903140c60 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 510391798 1250 510390548 510390593
    0x4120e010c201512011401090e16091d0105130204080a03110c0d021e150301120201090608010e04020d05010e0304090e010606090806182b02010c140904020c0a 70
    0xc0751841001980c0c041207014400114082280d00d04c8031542c4030007541100c00100c4e101030345c84403080058810b240b032074012004101c00b1404104c41d0b003503000d103c00c0d005a80c44e210441d005449003e0700f10900449100100d850300da60b00100040d01304160701780e00d4007203404001400c1a894000c210704002e442c607000d900140d604691050404014425640c48860489028485003001da000c940f0140c1102c3c0101c41480411505030480c0e110f82201005d0b1080158010f640c9607156110840c0c0d00c2c1c40f107030381640000c4440001050300342c01241910705a82030b9281d04201035407640c1c01c002c1070b00c80e031b01d50444855480380c40d4400081030810180c0040d01741d010002c82c59000c01d13100c1900f15165030740b110082000d2403508000c820000b03e80f0701c2e0001d40715490515410310072002d1034548004448a45519015520b4011144c0d000e48000354070a1b225500030300441842040484d800c48404444658160080150f03d18601d0305034004c04140402d07605840d42c0f40300d16281c22014003c0349410881c0c44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 510393048 1250 510391798 510391853
    0x12010902040b091605031906031406091203010504021e0c01090201030e07050a06051b190218060102060a0f0e0604080705070f08030f030a1b05130e04120e010c 70
    0x14601030044490040007520000101d04c1c180140c8031500d80340181d041c05100300080032403a03224001810b041c401c0071801080c00644d682e803900400090310181c1481440c024680459072085000c61450852602d9407020340c1144d080004000c029800203408008a03c02d0105684085804101401c503c24a0900009051484c0d00000d81560751a8001c4034003500036202c280855603c1409141c26605030f031401c5500d4040c0c40d21444181c61491005010074420581444038141300740c030200540360b1081e02e20455501c1e00394072003001c0d21000d0314403a026030002d4001070f50300c0e0025071085610350140b1002040d00740c5080364560410a01b62801c1d9825580001c00d04d051040401807500205030308050055124a008a003541307038001c80100c0300107843c0c0003011400f000c00c19000500c0d07071055602141c500b0000d1880181603603001205040701001d00c05000201e405080c034203544107907001460b10440c4091840121803011102c0c42c0c0a0501c04210464808501c440c410311800c0001c07142000b20b003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 510394298 1250 510393048 510393053
    0x9030e04051e04050f2103072003130504110306012003121006020f03070f030309060207060516020105010609031e05031306020102040e0f04031b170708090a0806010f0b0d0902120109 80
    0x401003408a1210414081d803c0e54800e220520100c9501013489e00d48941c05140305940076101d20714a5074078040d10705c0042080c8021140000540080742d134225010010304412040c40181070004880d55408036554070b1030502007542941758142c0840208017507928103d2200ca04220200303042e00c400c810310001000c117000742030301004101c6c07a058040000b0340c00c0050540da0002124a44d074070007801c00d5115000001045069015200c070a94015014410b40c904030078240c80d01c0301d030100c0103c01907003403400004a0b54002c0d0620020380381c020507044640d00b64803d5032204207466030400c071051300c010000001c3c12545c0192540c0500026400503a8a901d0300022140d0703c1c0000d0b0401050706940c00a1000207034200c0003449004241c11241504003059042408500b1468480030050f58000a910001c21100400078072034403004468412034141c640422540e40c5100b4080c030a0742c035800003018001c048100001d0001c817168588081412030305a40850300d105280e1400030308070380d10b8002a404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 510395548 1250 510394298 510394303
    0x1110d080105150c0318040f05090c0a050f0f15040f080607021c0801050d03020111031e13030e1c050a0b0f0f0c0a051e0f0304120309030e04051e04050f 67
    0x148201108607103411300d110404801c1d01d920807202c2c1e40320412122410002241c803650014044240f190303000300f00e0392900c03410301c1b0f40b100e40540e04036100d12241c1e80046100d01c2c2555060031013000141c8040109000003003403040d803548428003850700142c10700c070000d44100b2044403000501100006040c0c1806c0041000c0d18100020b0381441c01034010105950f42d0941c0554540e045850448035a45005031506059006045410840403086400000c001100c1000c020384000041540c115081a641e4010034501801e00850010001800b0141c43d8070035181003280d032a03078411a0f0300f12955960495441c2840c120010804582501065080001040a0764403480d404080840200c045d8a00800103120034482e02d01703c00c0c207108005c100f18840c54044042c02c03020900708400255268207480d030324880b070b4100719012a0002c02603200c04801603c02c0c09080f12203a03140c2c0721440e01220040820003e8070005045075030900030a031b04c5052300c64014851030b00550095001d403c0d0b07482c0c2295400d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 510396798 1250 510395548 510395569
    0x230d0f0606270303212405030d02011a090618072604051f060b04170609070f091e02121501020c030a06050c0c071d010f2301110d080105 60
    0x6840360002201000420f8002c038a215170690f080e914036802e20314504441004105000e02125131038483d038100380004404c403076860143c40b01181118590701020300b04034261801c5440f075240504406440c4411403c20072032107038011100622078030038044600c2c000c1302148811189a0000303280e50040c400e0a224080d042541c01d290008003502c5482c05895195460f2000c045901c01c18641561401d54001c107070f4003003c050070714941890368980c0d44000300f41c4100d03640d004454013070089001107041d007507000481600303c1c1e1209000703d102520384041900140b1141e000000c8110906a2841601c580d83c801050401180c5500210a0400c0910b80b16804440060581594444644881140e80c0060154002c42d0b009a0105540c0c0d650f4a641c501c03405506451f080503c5407500200f082c04610a042c000c443c40314402440581e642c0d03120105130002445002401c401902e4074030300e40fa0311841120103614041c1003501526002c8030843d494202d003003414000142c0301000620092404c844500c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 510398048 1250 510396798 510396857
    0x3030a110403020913050705030f0c03010606090503070b0711090a020d0c1b08090a170d02190809132c010513020f1002150114010f230d0f0606 63
    0x142000e042d0b03404654007003070240c49101c002c040a4455400c012003000b00d0b00180c58042d05542d900c65206a0036541c408100f10054425400c042e00411554424010441141c0d00140146480d5180c0820b000813544400400d41d149030010a988085454085031207014541c1030030010303915110307502204200c0d51800307410390400c000207140840c00c0743c201e08644601d5800c80c4d1101d541b082103000113a07000d02254840000002180741d030700d000e078a01246440c0003d0883d020380d03105403403040d5052034140c0c40c02c2c4006c012080c02c1c003c820250501c10308900303554000e84400501c1200b240709010280b14215101c0d210301008034034a000460080c000c10350840c003050b0380b031072040b4111307400185005050004107010318a03074116541424400c0000c408010808161144031713503102c0c0596000d1100024401780030910900e4000c02e0f151081c50041c142464814032884261b55901141700d140d8801c614a05140b6262030b201144403415110300c0005000c191610140500d1004071070148100070380c0003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 510399298 1250 510398048 510398081
    0x90d0507030504090623090606031f03150e0d0f08131a0c1b070b120408071401021806031b0a050d1d060c0c030304030c15150608090304060504120f021203030a 70
    0x14046235885403002c1e01c0e0880d0900409a60440d800044903d01002c140e02c00b13000031b41d0800400400c40030940c01050b100b803008065502c4580299810b641c52030b003106191000900060024a11400b07038030080441c1c901c9503420790004c10889410404503081558902c0110400141c0c0c078840840c0010082440303003400c8050450030745050014101405013014901100b8030010004080101503801c940504d944032a01c408034060f03200b0b100317000390007d60720310700710aa001d80d040d80c0ea0f181c4202070340e1240740b420300951681168008654280d8110804600c10b11506010400c01d206150048007540d10b0400810205c3d0a07941d04103d25100f4081d0031114540c904201400c40c0d49000300440e60301c50381605000d050285985401900c0551141040035401d1500341d0740c20038003c0c4900d040d0b08031801550740368004d032284000036880c0d2080d48a0b440120f1010801044124455100c3c04421401203200480b0b030f43c03454000c660240c2d00001d030740107135030000010002c2c042414440c604030ba0072803204 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 510400548 1250 510399298 510399301
    0x30207060e060403270f050f030a08130317090f3f0d0f170c090a0801050612031602040e1002030c0a12021903022208010e15090d050703050409062309 66
    0x20555007840841c0247c0340903e44a41d202c541c507450070041580a9544400c0050f46c60300da004000d010121140021146440300c00403400080810b034042d201940001090b45451605031400c0202c80c940c100b61040f852801540c01d16181d040c900c07038004c00d854009485600501c00390b0f03506424010400d007030380d00340a582c1850081c1d46510a032008003085220303090b0490b546840030480850300030041c1c5198040310700c45c0042144d06042d0000d500a40c000e0b2138070340384a1407405031b0984034020788002c850345000c00303807103400903103080d8000e418801a02c80c143c96280046d005d020050380d0048840154207500010302034281a031101400d60308841c072840450610000b1080c01e1801c12842d00702038109500490b180442c0c9c1036544054191443c0d071800201c080d56902a00c0d070290115011016440c0261601013074429200d1818500c208681c0d030140000d540f650805581c1c9403ca040c083d42000000c0c800400e1240307a40c13084101510203002003c07840407a06e01242c0300b002819100c117001e540c4100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 510401798 1250 510400548 510400559
    0x8160504091e062a0e010c200a0302090f070f0801030b18030912010b0a17030a0311071a0103020907050a0906080a0b03030304120305060a06050901030207060e06040327 74
    0x30100324010101221440c91800e414800050116004c103010120b11a9900c4664521024440005039060351a0700c0c50100e9030200540d4001c0715502d01601c0441200d07940100d0081100705c0c03904005c4000d020490203074032a0082450102c1c220785220442d10440203100e5840d802051411a080c1c00349050707107896046a841c0e02a02c00f000c1d0541c904046203441504a1013410700584114803000f800c64507510481801c414060110b0038226030151700e07020301c0810081440c3c00e03841d40c48284e2000035841e2141c01941100208050000982501e10a11004000078031101c400140c0c0e170307030020103000c0c1c41d411401041100304000d042001842020008494003540001d00703007089030060304001106545190092003d04496401180d041c00000100000c01082440c0d940300c4003034555007001260341c0d020500c0098411801140b011410520a0780b016620940080644611504020030f0303041552a41928040064500320701003400e2810044040c0c1b1341c840c0c2d0b242400100341c22640f0103031400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 510403048 1250 510401798 510401813
    0xf09060203010e100e07120b0d14061501050403020a0e0a061d09010501330e04020403060e07060f0503040602030a0204030f0809031c090512030f0301150e0a1d1f0816050409 76
    0x95010703c0070780d42c403036400300d0055507162460709c490741e0000f040c02c041c84d00702ca81c00741e01c0b40310403540340e07030540c201568002081d4450415038055070f6014060b4031801e81404201d0380343d800d00828402d44a174685d400460085119445010180381d404070941480c2028100d0909440303050b0000108822010000e2410356400d005800340f406132408070710b0340b181c520a402c5400008119103641c0140c00020000104015640003000780352202c002e84080645030001283c1703540754203903410300040b0148041000b01c5d00c90f500a68100700042e00040c6010f80e641e0b0703a4111942c00c4802518074040210f40c040c803e060900c1140710707810080e030800620030070564001d44440c10f50b02070240904501c00c4100301a9008200700d030602013a03100d04607220741e9a031803140742c060b140002d00e20004001d07030306906481c14410741420039241680304243c1c011500b0805400c0c0b10900030b00071283b011002084010a094508031a40906143e4029000d000340348442c02c081101c003a40a14042c5151064072000f05008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 510404298 1250 510403048 510403067
    0xd06240608070c11060d2903011506090e0a020d150602100b0a14010c0203030d1d1c08090a0212010b210604020d1511030103020103061d0a0f09060203010e100e07 71
    0x1180e10b20b0b142c411100c4000300074081d10301042071842c46007017640c60803856503a200030441f078101c0c024090107074001d841440c109058400e40c0c1c0400e0001c041070140c6009030f000c0765801400361100504100c2e17481132200c01d4803d050402d10200c0c1c982401400050b070305204c0700280500b40319040c0002c9408402285201c1c55070f101e03a2500d81c0100042300c01c103a100310b4207100340d5a00107040300c0d2640e240018002c014003022482002c1c803451500032601ea10404910681118690b408103a2180d004280540e507588004040500501417003070b1160042e510008074003459508000006203d04d000c0003486850440200391082d98041070140310920000003607404d602ca40c0c1665058261049807810f40a00344c00101c81002d15030030000700b2014594140040c0d4100e90003640c00f8401196035082c40210380546102c20403a04c115400042c50280e4250400040c070b9014201c0000d507902991201c0c0120303082038120307524440003c401e1103860740880500704098001ea02e0f1034100c60502401c050148181e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 510405548 1250 510404298 510404333
    0x30c0105030c04030807060218031911150307080a06050f030307020f0d05061e0604091e0c0b04081b0306060d290103032105090c0d06240608070c 64
    0x1c0020b00d11141582550b00941d4080c0129807100a6444c007040a50404140000303003008401041c5140e00d000900340140c400401c00b4a840581c42e61124154503200d9180780f80c11208401d41d414140358090f00542c801c005555130840c450a124401400741e40b40c07940424440c145001c2c103402c5981d0084119003ea9a04031500c18940c80c00401045030f1074411a009001401a4010401100d40000344400480c0c8115544900c50f696003080200b100c0144202801c07443d01c90503122440301045220740815409401e858144070ba0390135101d40e881c0d0003a0025603542d0445034080c0a20a441c1404224007002140601654034100c4003260b6101c00c81d11001e00fa4841944d5003404a501800d425400341c04a003041c0440d0350b07100d06014003100e0003a20508488039040b4807000d4502100d01ca51401241120090b02d0302c415424108240045030305400c2d2005681c801c084480d801c9070059502c680a028050509480d207445009021070100400fa08103000c0d05d400e59000041c80006200e10f15070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 510406798 1250 510405548 510405557
    0x60e06041e030606150f1704030f0c1421030708060105030a0b040501060e01110c01051605010b18040c060305010b0403170c0703060b040c051801050318030f0301030309050906030c01 80
    0x500300e80c500148020194005444140b41800c045017100450b212240740c20031030349aa5285803030505044070001c0252a203040b11135483c20120b000684100024064561030703140401100c80152214210a1003031880c015503079110700c20054560040b0b40302d481d00748414200450451400e694040c0142100610540c100400000041d044000740da00c03440030107030058400c0140e507071680b0010f000e00085100040c08102c00c18400d4500e081d0002d02e8000b40c40b410b80d90641000c00c1c2805e003042c010082a000c4406548441d41c004641d240d00c1c403000d80c03000e540004d07040c0e5800c260800001e440026000681010306000041c4a404400c00031102265805900154620100500316105000301c0500d052a402803078400400d000098100f008414400c036001c112100c2c200e203040e2403c4c40b540b0541c196800000c40868519800f5502540c2d04c420308280300340c1040c00d034500301c40c11035100300100400c10901000500030326500c408544c01404d000d4440c51103074140040000e0342c9a0740b8011403810070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 510408048 1250 510406798 510406829
    0x2030c040905040206070501060608071b170a111209040b0901030c060e060705100c030e0d1b060b030703060f0b220c0e0a030c090c0512010b03150603090313060e0604 73
    0x1034541744122416107800c42c0003000f00e60f80380c600052403003206a4824000403031403125074000c1700b0500400819142d00c1807084020218084d80454140c22408003a014045c2036803051156074824414000e6220350b01c081d540e6070f100b820042008860f031905601c1e0140a81d40f00500000f00310000c1c02c01558450b09000c00460441d000041051090020082c03040c0078049000114440703d40215160f03030503a4805000d01d900380040140e440320781e2000741c2e0006484910303891810b00303401c94040ca1203019410105a00706a040461724000460b0310440d4429a100881804024a4031880d81404401c40d002030880d005043c0d2030749142103120707110741d2807503980700341c09040d60095800d449a03c401070680900c06a981c184802550228818038041a01300070003065424031a008031080c950040030070344e000d03074200366070b071105a0402000c4100070314080c6d014101947d42c2d980034501c0f889000000f076990340d4100c0386900301c18605a20810034081081d104c0706c034982c0d9000940b0305481c01c0c0916403000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 510409298 1250 510408048 510408053
    0x30709051611121206030606090c1c02092d040b06040603020c10110a020601080d09150c0203010921030b060d020705010912110d05030601020307030309022106180102030c04090504 79
    0x7000880759011040c40400960304002d07020313001829214100480c1642c00c43c0e40c0e003000340120350070200c0b40348072452001c004403a4110030f4102d0800740d100a500005003030900f01c001084000004c0b03150501171602110403040c2c0001416800706000364151800d2050f00030100202c0d200d4051030044509158020501c84161b410030406420204184481805040000c0d510803000358003a1031140c006008080c00070070030240015804481c03100559429042510f040a1440f2040951079850308001c04041c3e00405a03809000b4080418010a1408500090035050074039103100d12151500780742c1080784600c141d6403641e00303540006902c0d400250344d58031140f03030182c0184a2282d004040304005803030200071030703880030404217260307900030444021102c401415155030104651740e0780160f0081000d00c0001740310f5006411483c2c0301030007011446414401c8418421800a0341052036480079041004952540080041d40c2e00c04038004c601d0743c186200d00305000c0c41a40119012152180f0101c1c04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 510410548 1250 510409298 510409303
    0xf2b1209060219030b100e0307031704090203090304050a150c1403070b0103060b042007061508030304030e010f1b0b04051212060a05090106021c030f060308040302030709051611 78
    0x1143d40e034803000c0c50a40703091043d014001703000481c0c445004180e401800e402540c0a51038000100100074010114945107941d04d529240c8800403020701d600041c800010010700c5400910700442504010b5616103040c40b007131201300c905551101e01c03640c688001e03009485030802d0540b949950041c0c0606456111091f04500d140314841c00144450280b40000092007405d17488095071107011101071005c81001c0482c42c4200f0180d650702003245108218000000b903040d072041141c441300c414004000c654070740c01c060868104a03070030390100f034196402044030340c0e100044503c2d9a000342804844030000c000c1d00300c018800d2207001007480c5503c2020400f40102000901c0b505080c1d4080c143e80c50a00345441e000d55a000d603021402038003083c201040503d440c40f10281a502d981d401409101000b003c4000c80900305402c42040c15919500502945e98501415010314024044145e440d413071072052514205903640903038146854a800c1c00002c4200501c0040002d60900d40741c3c083c940c00318562070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 510411798 1250 510410548 510410557
    0x504060b0a060801050f0301020c03031303020a0204090f06050c0c07030f020a09020703110723040b12060106020a05120a050f0a091d0114040c0509010c030e030f2b12090602 76
    0x1079108003000300000b5040e80c008490b0341695429070390480c0d40031900042c5800e171302480f80705442c2ea410500004d06a900c507000e00c42c0030303d4000c1c4103d42c440c10309078010a08440c40010f00f44d401030010304103c010710041c1d000700e07900314440f000800d00d814860a0400d40321003807800020a02d0190f40b00500a40d682d8640c0040504040d0314215540c000d0703490040d2200d020542041c000f8004d0000c0000c1c0140c242002080303e1f441092107080d110b01c084100001030460910042c1d00131514405404465130410000380604610340040c10284864106686006021590900b10358805c0140c8540075500c00d0541c0c45201500301015100c0b04004800c1d205262240c20006003100e0595082441c800700018043c121010000513a540000c080d00344800d0b1201c003948100800ca0030002c82d01e040d4070a0385981c900c180607140008098111074000f07410030141c903454204940c08124501c4e8445204a038200191155009145240c995050040c1000380001101c46181d581c03521a802400b0042e01102c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 510413048 1250 510411798 510411821
    0x30c0a050f011e0c260406140d051906140f060c031b101b1e090504020309060a0c050a09090c050d2301050409020a09050705070f1214030118050406 65
    0x79461403640850007010b110b810b00080e205e0032035800300b1068800301003c1011000c030314000c07082d240909000c2c00b0f840f1003c04210010140104000c10105402144106070181306540d07500342c80540e00c01064025981d00740c001c0714804036050029407003a521b443d01074103135060a4030300f140c40e100c209041ca415401100700c0c41c8210a11041501800d100104600345031482c00c9500304250b002100759054030318075544a840104802c948000440c1c0c05200c04807a0204607443d244604507100d5012070180d030410384110b81c150303000c10280280c91140c0e0160b20442c10003403404a080005001c0014011243c0d8400c040318582d4840e002d8070180c0c440c0c01107410b41d0703c0280080c0309108040144102c0d6140b80500d5101042c25800007158900d41070003083c1c1010380080c02c10912070300300310700c1900514024049100b440010002d250006284a1014a040e4083d00315215184611003004c4c0424030342030010a0100320400050082200c24007a02800c9201540d00081ca9a00c1d450b1850040c10b0504030f1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 510414298 1250 510413048 510413087
    0x15040231030f11031203070c17090a03060204090c020d02060408251a060102070b0a11010f05011805010e19050702070e0a0c03110c07380315030c0a050f01 68
    0x307600a02030415403c0041003010340899141e081c0f118095600b82c0800d40c1c1580006040204c4880881c0d00400441d95400d501420b2504d014101340020b46c60340131583c001c4030340a0b0040381c20040c007402841071562540d1745001400c13a60a034864001d403103c0000300014494200810185d43e402910155109030440c66842100c03082d0003410920070741b201c2102e070721804c07002500c0040d6203544003040b440201d81c0040b1401d801d188036264180c8514243c1c00b420a01e0350b5036059404100341c241e00905000300380d0f03000180c140c45076a800d001b040c5e0354143c01504102078002e040c480e06040350320700005400c0701050002000e072916807049081404603480014140004400c1c0040101e4541c8600c0340c40074252002c105c2c8070042c80d0b60703409500030f03500013181c59040f4200c01c02c00100302030185201c0b4000d10140d40d07402e003003a504184c2c1c10300d810000341402503000710401801da1403200c5401c0308204100c000348120031040300000e071454405c1c040c0380d00070400922030000e164061300c462401a02460030303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 510415548 1250 510414298 510414323
    0x504181e0b040f05010e0f070b0a1106070906120c0e04050a02070b0403180f03020a090c021204030f03080112110103020c030706060e04030e061c020318030c061504023103 75
    0xf82854000700605080d255546880205209000e0014459019070790100c01b41c00c00c0352600c20003440c10742048480313409200603030b06c800030710502c1401802e00c80c50090312081106030a01d8030050151082560880059143c61100405590008802c202100301141c004c0784643e1707400c092901030300a49a00400e4041c945042c0801c254100001241c00315882e8a41da454565461010058181c1440040d4101e0301588080c0180c58064100d0494042c1e0390048602480c910f101c1d4540a60113a4025603c0130303000c0913264200740c1d20a50090043c00400c003140c1d000c8491b525800b0304074130740c030b51141e0500d07a000401c102581418000c2c1c0720791303e0300260200040396444590740200c030401c440840026114115101c8140b81c01e00a543e00d0100700090280f1894200c005a00254005880b9040d07a801303c900c20003040b0300401c01040481810b00180c84c060800d004280c0898240c0040340d44124014003e0010904496000e10300c2200f4509074200369450311003250b19400070b04d81014120008201 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 510416798 1250 510415548 510415553
    0x60b03031b060702030702090609100305071203020c0f100c061d0f19030c03030902150423040c0e0607020a080d050315010507020913050f0d09030c0504181e0b04 71
    0x6010018850491082d20032039510264126240d2054050080d03100c1e12400100d8414140701c40c44540c0452020340741104d0b01e4032900d6072850a01603034801c01040e0090000b00013016130500c0030602c03a01e4241c584a001d07041c0e000010f4804c03050500d078a0104100b50520340284007207508103600d00c124518100d22442031141c0004d4884050140d90b00141c85800200c0c2d402c5580c080410349895007540c0c170040c0041d020396085001d0200081706a03804007031b03004a034504040303090060008000444800800c0b248100c144985192500105407181d490880171006c540d0300300f42c00390b83d99982210880da50741100e20005041d940c940d00400601d01c140819201e0041d00300c0011801a00a8104429590102001115188286a002504142d5810204d01c0044d801c454510032240b082c0c3c240c1c4c4402c4100c0e2541450403980618050000c0e40c403080400500c8001070140000d0107080e907082c480b2000340c0103a0101364445030b00003040030320010f6240e8080210070210008140d4042c51181c201d04050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 510418048 1250 510416798 510416827
    0xe1006120605130b1b09130209030c010801050603070302130b040902040e2a0c0a0b040b01050f0102160b0f0c0106080304030c050603190b0d0506090f01150b03040f060b0303 76
    0x85812a1802c0040750041c42980082080907074099a01c4c1110342e03950000000061440010280c1c440003880300a45a58900d0201d4106c094045801a11008244205450810341c075618034140001c0000610003622520b00320b03075000b03585040c0940d481d8400285500003c11985c081061590b0100340403039240c003150010000c60306001719a4515446060f0100320f0b00c6644403e05c0c0040b101c07506040c5255003648054515880008145c0f5040000358035003100070b210440b41241c00300000070040c03100d860700c0740920142150a20050151050b40d0f000350040304014000c90922070004244c170000f8141810455800c045a00d00a110746507440758029540c0d0001c1c041251001030040010401c0d0074440282e910a1050410a284411200842c0b41c0100101c51880390806858038424000c100200040c40c003070581d4000030a4841da8102080342120040c40400ca9046803103c41005061020303000e03680c001e0b030403415882d01c80c9514a0524010000d01500365014040400c0c0405402c154 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 510419298 1250 510418048 510418079
    0x114210733020f1506060702120a030f030b0616080403020612010806060d0317180d051206040615080a0f1107020a0b0322080c0105041209150f030e1006 67
    0x50450240c00506440050380c5030b40312a5690f51180d440a07081c58460310140c00f2542e0020f502170011854101c044d00419003000c00b283c0301101c141c1c00109944101503010308451381a4401e89801c002d400010030010304180318580c0c0751264405000842004d101c080c808640040d81c0c001c000d01d1b9951051015500c0a43d02449035040a004210002e203850601c42581310005600d695442c9589040707440f00110403002920800710400440c07184044140b04022510800a10b920f80c60f0b1500d4081c41c01c100524001030a0314003550800f40b00304521070900e08860740d19061030905c800c140ea0303070044400044c103101c1e000024050801c08201d86056089000f041406d00a55a0601032501c54202d0b8a540c4000d8404c02d81c2c0183c240c50806a400c00c40d54480750306c0780b00d0b00580b4a8a9080101350b030a40b0400c5d10140d612240c00700741076000c0d542000b800b0000b02000600140d10f4040d45002920922480410409143e2514418007076000240192210307188003003000c00c401d0f41c580c1415001c1162 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 510420548 1250 510419298 510419369
    0x130e041202011b0f050a021e2503020319061803110d08010e06040905030405060a0f0801081903050304020f19150207050310090305040f180501142107 66
    0x1800b030f000034070002c0d0b541580400b00b555480f8410b2000d132102c01245e40f40e0004407641c1c11405001c090400a031202c1020318400d410480040001003009031740348294840b843d00f254619504510100016280850115801900c0700c102c5440462503042c0200030b001da01da222440d5501c503000a8081640040c1c107105146171480464541c01901802915214400c0c0101e241110751800014654601500004003691040084d64105651000403501c250030140c40c0c48040360390904003001d05644140ea01d401060280c00a141c1081d0f110410045884640e03805410442c001001406648a5460840d41003801401c2030280e6201c4250301301e40441d060240300501880c0c2c0309070300c00341440050b0300415200e004000c0c1c150441003034403a000a00807003108505002042c400003486800c4100150002c088660001840c508480103510407250140c0094000940202800b402901d030a15510720030035456501c41d0458100b440207914041040c1d000703144058021980b400380e40580c0003650103c12 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 510421798 1250 510420548 510420551
    0x182c01090309081b090903040b040927080702060304110d03030e010506060a1b020312040b09040b040204081015150e240313030e090a090c060503010b0f130e04120201 73
    0x80e11516204d40b101c440140b40348604441e0090030102e450250402600031002c00e0451703140641c1d41102107165000750744918821a50b4443c0402440d5000144030803e42ea071449040300c41425a450b00707240d009803070001e070040740044000380800040c100d14261445001f44000c000352664a00140030300381034180580c06508040c0461514100390055809000c1c2548508529075548c0000e44180150301c9000d1368544610703d61481c0d8200b8000040010384100780101d80c0c0c41c5a01c1c03007030006440b03070100740500a51040008001144000ca80e4100000040c440443c0c1c0203401c007230000c5040c041d40c0110024120780b03460f600c08140c00c42d40eaa44140f200b030b1a10b041c0c0f645608800710b041c2440c109080c0c00208104001042c84905500b001501741c4203007000c403a4900241c01088001e00106c92060403180e5902d000710a01c102c040c07000c0c00804540c5042c914560500441a020380030f80c2d503a0310384011001c1500d0051a80c40003921019015840110029103043e041002244001032070031030255 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 510423048 1250 510421798 510421817
    0x112021b1002031014030a2f0109030816020406090618061a0301030803071b03080402011205160e040b040f14100305030712030b0d03050a090b04182c010903 69
    0xc00350700076a0701c1501102c040c52501d5241140b5170543d04100c0c2c0c4001c1d0301d8080d0701150000500d003240441096402803071400c0c0c4074009001c07400010440200135034184007044c4c90070000560355070115100d201085000340160340c100d00c04100a00780d00d801c0207414034140180480d4075088881403260401c0024820321110381d0311418020308101400f50014503031800c000610101c0d40400003990004254940032801001c0c0d9100c0503240b10f13030a0401c4000030000803d0106540e80aa035032120107140305010862810140041c00124020790840307020b00080300803d21032565035078011035010a002d0403e018004284020394004e00c03249850800a80d5a2004030300c00071903044000058071b034490015803610400c2c0e15003e4103001d20120030010140c490100b0801c0d500c60851420011f48251110354840c180321602074520320f80d07500a025020001d0004110502e24400c00d24049112000002549174082d00070128200410a680314007218120301016009415804091554060340e24044c15 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 510424298 1250 510423048 510423073
    0x506090103240507050c0c01030b090103030302071b0e07030c0503130236160504080604021306120308060f04091a101a04050a1a030411010306080f010f1409030a0e0112021b 76
    0x1100d001c0656107802203052f9005200090003a401810410f0003800400a441c2c5814203600e21564580c11407100d809144040c441e9498050051070a20072050801e1400c601d08010320f01d074890070301000a0701c22010040e50702190440345178001140c00710f1510880d0038003400f21a0080e00d410558009466800c10481000e40522400035182611050030181503103031034540800c0011100e0b046c4551090741c1d58840014030030714107400f000f0280d210b5215021140381c90000c2003524003603441c500d0700450600f4688000240d0705031604030078800034030050320307951541c0c0030301d4a628440e60020305000044410341e203c072440203c0034100b100e00844224644540350500c810420307452280b0181c2000c024804a00000c29242d004070400c201072400141059880e403505240c151006a070104d2a55070340e0a03a0b940d01b1050154448101d2240144d09a50502c29100d03540c1e481001106020000700410101081e0320034141483c0e01c90143c8411364466984410300185d8060509000c00a072198500035400e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 510425548 1250 510424298 510424301
    0x50108102a0224071b02012a0212061302010c0f0c030c090501091a04020c100501090e0f070602250b04030303021b0d0e0112060308040b0912010506090103240507050c0c0103 76
    0x10070200c580e45c0a0880102000e00c01d10f45081c030004074140501504550361b50100081f00c0c4894205200300302040f4207160050141d02c6601c441000602e030005c00802201c1c43c007400d0702100160b42840c1241c59a4072030f040034528414000c0005200d440c108000006000c20815080281c2c0d243c07410402840e40e071840c40804031400c03200858100c111b079040030101840c0c298082c000c0c0d030241005454102c0c14940710201203880980048425a42d1448100141c6200b04041862149520001c06440d42041e5000c3c0d03035034070782e0b5450031040e103034419202c03880c1d11607803000500410012012130385031500c0e0f18010780a074016184440401003041c20140010000040b64812600c5075100c1030800c848100045554040042c600f00c0060f40300c600000008a00740020401800c0a6090b181c450013400e04100c42540205c0c030b240e0950307050201b4048141d41c0c0c0d245140c11a0750005030950901100201415000544c0303c141c80800d1900c010800f0b0b454110000b40300c5520040241c0b441070700c10344010350 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 510426798 1250 510425548 510425551
    0xf050903070510170c03150301060b0d18140102031602010b0d0602030c09030a080403060e160905041e051006080d080a0f06050a03030c0203010c03050108102a0224 72
    0x2603259021060410090400102112040d1600d00e001640c4844840e0b03240d00c500016a00d40c5401d000000802c54000c29211800282c41d10032002403056514203030700340107140580b07800c421006950341d9207000144149003005100b00c0d4052101c04a0f02031000e42c16000390022076004100700c1b0000941110644184030702e2901440041044131000d070315441d080300a4100904c1071045c1c1c04104000700241e035041184008152060688540d1282545050015112281d005403a01d5206a0102400d13090506042040d036a1500000907140d98904110702d200070002c5180b81d02e526070300d164606124020a00304c0150f030f6802028080107650300c0f0701a5440c010010034400217080c08000c0351144086030030035040302c12b02c1c00001c80c2080d03c0c1c000003152000d10b036001b1000b003000010721504604007030085400e2504181800c021941c58030801c141c41d07c03441c0d412060481c0e962500500c040030361030040c0340c144401e1201643c24482d540006566210340c103503240010383c0d421808503654401003c0700d6 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 510428048 1250 510426798 510426817
    0x40311040603080d0c0207050a0e01081509060103080a030f1a030609120f0717042304060b0702060a180b071707030f081305160603180b150112090b04030f05 69
    0x441c644031035210004002c0524945171003c60040070000685580e9003402c01010705200e5011403119450100b00528001040400c82d44400143d81005a55180410a04d0460b070700401c526568202d014800c4005210b928521801d6034507280c40550307240801c22810304110002c0d000c540c0c998030707074800702030796048824200b0724400003c10088405c101c07480c01406045d4401d01e900044411040c6046400d50081d0300002b00313801d0424042401d1010400c2d946081c0542a1010000107080c81e14050141c461100b0203070191200007902c3e2403040c405d580700c41c95401038140000742c494542e0000f8002d507209420942d9070301c91a204151385c0c108100201d45096a0540310201d620700103e0742914024001012100040e440b40c3d00c0a001c21000d00802210b0098421030f940d0703882c2001009411075800421880c0000f01d100311800000c2c080c20708403a000003810850500030400240122504021070890411a900b0403040303000b0840000170720b902a601c0380c0c40c0e0310081080b210084600b4007498054 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 510429298 1250 510428048 510428063
    0x8010e01050412050705150f0907120c060f110a0c080c0303090604030f02030a0f030503010303031404151d0f0a2303030109021e07050f10020406020c06160512040311040603 76
    0x124103855004100405c18a845441aa4200c07032082600c003c403040100c9010a45c0a110010490390850a000c10b101800b03003901c2d8912110740d143c0391501903080d43e000300414000090400100c01c1e014058140201354a001226848506403409490642c1603101d014000e229181c2ca0100034a0080280c4448020207040c403400e103465901d9030483d1150840c802e90b01030103812402404614030b180240d04007406a190315a880d4503620700241114054083c2d007031007418800c14800017600d81c40600c01c2d0707110030601c086002d40d1201c115400440d01042141014422600c2d010104a004a00142414060b44d0041c000b144da600245105801814449070590810001800b00d59900e50107850000fa25400d20a0645440034010500c0cac3d010b032005440580c040c0740c0f54005c1c00020006040006241041541840d14051000e5038a42c00e03030b4081845100b01281c29a40c404801c1c440e150310540280c122590010200c45907640c0340c0c800c0c0000e503030018007103201c0d07400c40c24140918011694002e54 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 510430548 1250 510429298 510429323
    0x111010b0915060f03040803041509030815030f0304090f050f011d0a0b0d08030a0507030b061e09030a0c080c01090506190c20120a02090c0309011e0608010e010504 72
    0x5000910410059400c2d4014800c4c041c14510700e00d10800f45d0b00c1280304d01c450755541c0c03d0074140702c2d09021080351405509814203180200003035012030460740016201100b41104902d4200081c03c00758070580100151101040024001019411059026204400822254440020144040100b40030310603000c420681c041d2062103460421342d0340001d02e203500290301c109403c00a05541c1d80d5810548162a010041c000444024494150404200d0800b0007140b03c2d6940800d2842c0104000141072088031400c1c3d150030004101201c030340c140c0041c01d84540020f1843e108080c1c0b07010703005103046881035040d81151075000c0c2040c401541e1004014a080031841054929401c62041c1c0740f0b070410800f940b100e00020710020554160258800e0821400c600940a000c0072148114000303401d42c0c041554040561120307042c45030401400a8010340e01d6a51445540c094140004580444c2464501c015000055a80480140e81002000340282200400100c0c01d8440581d8050540f844c2d400c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 510431654 1106 510430548 510430561
    0x912180310091e02030f0a0302070812040303120b010216030b0106140f07020f21010933020a0c02090f060a080f031909080d0c020111010b09 62
    0x2008002c4011940c07907001195002c0d081203a20b45031015800710139510103101c2024050250350031140550701d00d00c0e0003955000b440c480d00213640a07a44c00004400c5c0c401c01290200c81c0c06a86440642c095140304400900005c8107a605520410440f400641900c141210045000d0035028a241d858014040c0c01c0e1000071406402d603080c00c2065551866182c001e4401054040e240407801c4038070203011170130352040b2105000c0d501c0f00d06000c05c4000c9105401c0042d0b2103125000c40354600c5c1c1d001241c4036001011010744030000406100007910741c600c035405045401040e10740030308100e440c4e40110310003000942d501b4490322950410005941840342c801401489580000c140c69810048025102d00589414015600881c1e5410340024410540710700500316900c11703103400307400c0014060540180303040100e000c174501c0390340c0e2108848188100030300f185024040401550303c0b41c = true := by decide +kernel

theorem cover : BRFrame.Cov 510251798 510431654 := by
  have h0 := BRFrame.cov_init 510251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 510251798 ≤ n) (h2 : n < 510431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
