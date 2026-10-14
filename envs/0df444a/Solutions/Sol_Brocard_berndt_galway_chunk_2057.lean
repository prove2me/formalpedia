-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2057
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:33:04.894558+00:00
-- url     : https://prove2.me/submissions/23c60fa6-4145-41d6-95cd-c0ba92b07254

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 369784172 ≤ n < 369964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 369785422 1250 369784172 369784199
    0x50f160c090e03030f1602120c03041406040506030402011b150207050114070801051e03010e010b10170414031204030203090102010c0c080414130c050a08060913060506120106030c 79
    0xb1052001d18a5483c108224080d0840040d107017407060f010009403507016500c00d00c44c100700c403041c100f29a6915001001c0151303803500640500a010b1010100c003a80340d1520b4001c942c22500040e000703d00b140d07030319001901c0c01503604400a20940d4094032510009445000f004044000308900607115032113402c2039421200f8502c45144080d800605100042c1d800c1142181144c0041700e851014640c064200880110881a200d4156007004111795200702c06400651030548207172a80300c907030102e804003290700124540c600d017000400c00c00800d011414589c101401d01c028030003100e1501940002807590502e044409030016040424501079640c2d0a01441c1c2c0304065a18003140907101c1070700c400e07403d0301c40c1d80718104001012000c0e00d8402c0d1190585201c41000c130102c104200d0041d924084c1069002d003041030002110356000071403900d4040c500c10301900102e0381c0d0440c145d40ca95a10030081c4006003080b0303405404509105103441c402d0207148055445000b540d00c03017501d424250789005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 369786672 1250 369785422 369785441
    0x4121803150c08180715030b04111b030307210b1903140a02130f0e03030a06090f0c020d230d0f050604090f0308040227090f0319050f160c09 62
    0x49581e0020044140d01c002030301e40c1a104682e03054a901284a0411f03070050a0a182094115043c480c054008203040c20190080c8107950094200d40a0800e160030388a01c0102c841c140454080c803582c80000710428000070943c090b0801c000723018484007000920550a4014072507140107600b4051040040c01003400c506850100c00a20360440c0d16400140040480a00319a00940d121014480307450301c0d42040010016140603030b6941e042c40b1040e0005440c15000d09507003a41031141c5402d1010442c85040144480c950140c80703400d0b50707010101c0702c50f20001501806880b60710030b240c4048942000400048082001c0000d4140700c0c2040c01381981c1d00180f04500c5185442711004c08100c0b5101c172401070315494a05038120b540c43e440040c5040c0d03041805480700d02a41c07511200c40c80c0d00ca4100300c2c00381e0301407011a40f6000000500030f0348c03449814031200b803050041d411400319500680180c1801e024000d051810305151040c444518020034000b03880c6100303103190402c035180180c418501074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 369787922 1250 369786672 369786691
    0xe06100509070c0f020a0e010e160f0e0d060605041109010305010905060604031209080111070201030b0d1709130e010b0a0b030402090f0403050702090103050c0a090504121803150c08 80
    0x1c61802c0d0101604500c000701c005050719444003121400c556031440801c01902150b2054205941c41e10070518200c941240c8100d80202e01d82c1c01f20340501d00030b002e12409681d05076181489070400005112031016050008c90f102503c2d8500030a5503910b030701401101c4001140096105c0c003601000400352241070703001950311440c0000344a215154a011282604c2c0c0250140c3c400030780c0303e10200c6088030a5440b4108030f501c0d040c80301c004a0400001064124000d0380c003440440328413020070001400c4490010008030b20b2014024022000001030440420020103071100c4541412000381662910001c5251304d954400c0704514a08d000301d070040180900b00b00090540c83e251740482d01e01036010340202440b0354414005000c0502c540c0031604039690160020105594a1138201d55854810b9003031442605124030104402005220340741c807658105240c82d89001440b81c0903140d44030207500d41d24040007404000b1001c100d10300c21201c043c0342081c40001d10f255880d140100321040c082c0c070b0f000b031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 369789172 1250 369787922 369787939
    0x3160509060d0903021c030603060e0c0d0308060411191b0804030b1012050a03020c0303072607020d03050c010c030b130b0f0d0308090c0402040620030d0e061005 71
    0x111034039018256842c1a03241c1c1e00c0000d440f440d80c141a882c0074a86018800c80d8a0340c241c2c41d0f288507905401c9142124802c40c01400b040b6405984961540a28040307590850826420a030204c1d12400b0240d0700007901820004106841807000c00103580004005c401c131081d0711014480e82c036400402c0403200ca1001545003511980340c0d540c0509481244405000c0e10355400200b52440d034000c442c003005152500c0c400d030143d0300c0e900e88191a0111480c6c15400b600030b005600c01c030b90030088200d81000e64031921050408103a113900000d0140300310f4603450b070300c81d05100000042c2c4034a180030301c1003030103903e41507160241181c0040c00d5500303007030348001014100121031090b621151401740700000e5400d000b0503841910b102140042e0505040f480d8440b6040c00f1310402d054208a096000307500e81000d0b2090043c80070240700c1640b00720f1081000181580d0101a1741c110364800b035440440d540d40981c3d203020440b080b003800f0340b044154942c01da1340100c1d0602c0f02c2c00c00040503560003040c0c142e0ba03200c4c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 369790422 1250 369789172 369789187
    0x60c020906030109051903021e150108160b0d0902062a072709080d0c0225030b040f0b010f1701050705040b0c070509040f170304110607051c05031605 66
    0x16201c0c03601b18200400d0084104020341014000c0c07109a1140d00700200394860a07070035841d196900c180b1004e0580b81045c042c00017041545000c42c40d0b01c5081203c850400c1103138501210703200c840e407190019000c425a60032001006950303610041c04140b280c104000a02c200c5100400600706081901403595031007100c0070441c0f941c1000d080c2107804405401c061420142d69040c44c043e144221008040c5100050807511100180e400b5602c031003015400c481d071190702c9450340301203040c0406416103244014003041001580c0003c5e0564414030171708c1a544618110740d1a603680310070a03040380d0780b00440c038a800c1c000c2030445180c0f486005082c4001b40600d0804240c0075209100d03a0007a0200600001840f0031405d074108149402045d0140883d43c8500e040d04000c1c413490341112040301c6142e6041c10513040081c14000342c9004517000034000884100e07400800200e80d010310021910740c0544001081e82c0401e42168081c0108030380c44031940c9290400c071f201b02e801d11544200c01445018010300307 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 369791672 1250 369790422 369790433
    0x20f060403030518160602070f0f03020f060f03010f1a18040e150c09010206070207060806091b07140c0414010b090406030c060f02120304050d14090a060c020906030109 74
    0x2140c0064050400040948a00c40c5040c2e042c00110034000303e500c00c00da490f02d03504502c1105401220b54960a886600742c0300e800c00300101c100e0f0b00c103510354407403841c205001500d0200d600030312031703c0004c0480d0702e41103032015501c0307082d08241d02003601d400003c0410400c2d80d0140c65903010780205100c24903d850340a4001001c85107800d0700b070390300031666202c0100503d9820844c01061411042d45401a442c24000c0382c501c55000c52445401405402e000c603c44da400090400f050300d2580d2207032883c81d0b8506090000c000001800c00491000304100c14040742c104030300500000e40104010404080c08001351850020801c1015018a1400240d8090100050305050658420450584c0c2e00c07116030002a0142c4419040645807400d000400100560042009800c2002d0703502981d044810040050006002c00c4070f029205400035000c80c0307022486001c2c1d0010b4008074003001420462004c000c00c14040082d0000f0010424007520074080d0714040042643c4060118000d11204182d951203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 369792922 1250 369791672 369791683
    0x20f15070b07110318030114040309090c0302130312141305060903240f0609010e010905040303091b03030806030604050a080f0c0109030f120c051c060e04060504020a06020f 76
    0x509050902000302d950180300f00c2c000340c0c41c401d030b28040369244c0000c0d0141031010b9924404151180d0301c1d001041e20440407140c04244500e0301511400c2106240444d200c0182c103042e0002c1040503400c01c02c0c0c841e0100c0044158000d503008944c00003803407082103c050031740e442c40a51030b040610706200040100150000100035a041902c0403030303d92400c100400c0c9030007000030320766864000100039020448000c0f11510b205a40c12200a2441e84440040c40754015003802890f207001001c10040c440591a9040310303800c94070920b00003512410607140c2904460b82a000b0001c40c074000c10080003032503440400340d6040354044001c0c000a041542c2c0e442d07610600c55200901c50320780800d800c010100c41000f945c1e4005034020080c04031040618000f0100799a01c10150003050150315040c0700e0640912a2140c546915154980350020321911810f080d40200344076017005480385000b02d0702c03000e0601810700551040c3c00106103420a8410400091044c2d00020210340c00700301d1a81d0000d400066 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 369794172 1250 369792922 369792937
    0x20604050c0d060f051321080f040f02090a0501050109080114060d080c10141807060e04060b0c0609120c0303060103090f050102031608070207050102100c0e0d030903020f15 76
    0x1010b4114003810f2078084060450760a0550030300c0d141c1420002c803040e16020441000f846100407100f17550070400c1d03800d83c02c2080e0702010001480e200c00a1040b40e1011403158001e801f82441b2022401c80d64001030010100307d80c1400d1854a820041026581040c540c034094903500f0001d1001500020020a011340d0040145d44205c070701107030030414095910100e07813980c082c8e48141c42d02c40c00524080780c0075104141350450320500d00c0c000110310136514008070840c0f041d0039015003619454107400715042088480c0e0140d006658400000314900008010088185004c0107011103181095005003010b400c1600c2c400310100400c00b405034404e020080369809071017403d0001e45418241410740e0f100c1d80448008050b5807002041c040000b07a564240ba0814030581d072444055a03e08004a0b2101030520410740960b0105400341c0702550190081400e01c543c600e0300740751030031031b12000408888040d0420390124200303c40034825820400309071561003009680015200d4000144818a8802c411 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 369795422 1250 369794172 369794179
    0x1a150a0203031b0f0d020909060d11040b1201091a070306062129090c0405010909090212010606051c1418100614040f1404020904030c0b070507050d020604050c 70
    0x12440840e2051802034620403008882884e03181d4801d03803004802540700d0020315226808c402d0008510b440c0031900222841d5000803c141d040303452005200140a0076a10705620000c038114050b413100c42481030080d514041d040b400400019140f00003245c66001d44628101410b00400344412a00321100c06405450300012142035010010900000e008849001c01903e8007000c1003208034480b80c260036515942100d020b00c503a21188880e003003522a41c402c1e94081000d002c0b0800032040031744d001d03012190020f02048544610014000e0071100e06411201c04100d0110b1107108040080303401a134504c0e43c0e41c004009030340800c002603035010401030207003000035050411004000c0c000d1100074000c44103107030700b032090940f200c1000c02001c40400c0d1160151346040041c08140040e8040d00d142c40b20f044041c400359845603000c6c0120010300030403e07014000d00e6080140080c400720b01e007612500503540c5440d1a80440d1403d10f041840c2d00d21000110741c001e07800c0c440030640112b05c45035202f000300c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 369796672 1250 369795422 369795451
    0xa170a03110c0a1b0e01060807030b0f090a020913060f060f030b15071a0a0608010c09050a06030513080c01020307033b0106120507060305060102030a0c170c011a150a020303 76
    0x141490340e250550f80c5c000c075411140c00d000002e092600008150f001d0304190728207000c001d00090034000801d47e03403050f0316486059480425801c000d03550040a20080c013411602e1007a2040200e00d05441d6554004401e102d001c0ca002c03c2440e5010506d00110300b401d00c0c003440104000c100081c602200e04071140703001c0c04009503c1007082a41560140003928115912105d031605440e200300804061007020340079400d00108c103503000d00c18280e20041e41d0009150b181c807d414648110000d200003444014a001c8503220f500c042590135026040704401031002598034503100800a00780e59403003070400c03d01d417044910008400d182011201800d442265402c0106009004140c05000aa1b00c40002e060b11800041d0a000c2d01080001c2501c1d0140c0f0f003400395440c0d240049030b480c4110410748001995070101c90002603210040058860240c81c2d20714200800800c5043c02c4403580058075410500d50310020889092084070303400f480c0b0141d450b480c103066000c100a500c07440000c00405458084 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 369797922 1250 369796672 369796703
    0xc2a2c0606070b04050106050f030f1c020705030708101506021b0f040608070e09190807031205070302030414030316180e07050c0c031902090601020a170a03110c0a 72
    0x2003400b0764078225004001401c040c00c2c20b040c214002d00c41400750500849030312075504618100010034030644282100140f2011540440e4840c003003145030650302c1103000362a00021159000c010310400ba00302880034000c90764080e9184012980750b080d11800383c0301019010001c2c0d64001c600300e4a4103071340a07003d20030424841c0000b5420220748050030352103450508045100761000444105a9516000c20025a22100c0c5440d40d00c92802e1032204262200026800c0094030000140a0030740c0301c1e0800e0035111680001c1c1c081628411100351001960202c2080103102400c03412040004252002d1491030602ca1080a1180000e21882c000c0c4140d54031401c041c1c0580b1031020307006001003801041942801c02d4020903940c0f20784041003082c8610400d50003140b0f008200071644180e50040460002c1082e402e0240ca104000c0c0210305500030488a4404241c244416040400450007916555584918087c04071800d201d0600030700c030703c09e0000d200b9041c00082c41041250300a5100500e00d110b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 369799172 1250 369797922 369797929
    0xa050709030314161520070b040201050c0a08030a0b030c010309020604050402091207060201020a17070207270507270e0402060f0418020a1b050703030f0c2a2c06 71
    0x3913404001c000e07815400100048081c3d95001951144c03152140c4011031200485410707240c041d007e070203405508040089001980180700910514235450141d4690384065141c40c91180c0040768507140d2181ca5158000d403919003171203d00b802402c242001c2003400c45940116085006600a142c025540000c00d0903590b510b014803038107682c59001c02c8800464480800134041c0d00312100280c080b070040540600f0072065900200d02c50021640180356a5140000f5200c070b4200b640410500c8070a90304100c070700803240d4001c3e644101c0940d00c070f80403030440d104e0301c0c0c0c0d08507880c16503100c003c01c01c40401805108081c4c40072981044c2c0481c0e642780c5842d09440040c40c903105680c0122011032011000581204c101c0e009000300300710b80d4490304508061a1000c0c0d030744842d000c10003866500260000c0c8006401803a0b200e00b24007640c079220681380c030701d0750342d0700c0c6600311b94040d01e01008914005a01000c01d9001440007800c2d40803215036004054088062210101030300b4244002c0c003110009960b5103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 369800422 1250 369799172 369799207
    0x50d20120a05070e0c04211406070c02092a181e030106121110021c0917030a09030305030604090c0b0702030715090501030b0f0303120a050709030314 66
    0x140e030505a6001d0750342864401e580d03844034815490801e840b680050307000512601501c0c1117034004032015560800a0480f1407001d07203152422211004a070140d9a0714030b03420041640310308143c4e254420b254080380100501c40c0401802c1854001c0407503261012140900f47c035400d50000c0d00e035226140c9000c0343c07102c142d034901c40c3c0029401441d031010789000909800c0c1c1c071b890078180a5000b002501d4072001810010084200b010f800488888403090303043c140170022080d01d40c2c2500c1030781d01a4100403005541e070061030031540300241c4909014054003000955001965508000071483d01c4c000e00c0300a00344a20610000d01030140200000b552525070760046120168400700442085032a9440c0c00f01c40d03000030700141e02911512501059510410280540f2134a81740c4505130b14030701e82001100036100030000310303802207e1014580a161030800103040100c00d140104d1040d0f2400070342120485500510100401103030703050405c0440e4000721681c0c1240311514205070380788a4042c1c40318624 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 369801672 1250 369800422 369800449
    0x918060b0a0503040606050108060f130605031f0b030a02090c0a050903010507120b1e130207050115030314030c0a050c011d0619020909070f1106040c0e01050d20 71
    0x800150312041e10364008002d40c41a0710504080004684541c01102c1e1607608551003608007480c500c24403041c0c642035441a140d014841c4001c142e00307440744003007810b02d07040c110440349e0422074001101440886002d0301d18080401d5004219500e41c0340c0001d080e03600045d100700c0202c0000120100c0c014860000caa042900c003900074419428201c4004110304050702440540a14240758048107240c260b141d20101c18040032174822040010040016203900a40d081c44920350801c5010f00180302070043c3d011643c81c030251240380605e14180a05001052820503a9041c0100104900c001015050f40c034044403600e4880d07201c0075010f048a00422002d441030803441e50f5114442c9000c107000440d03030b1048000504c03075402c024802400000364000c40021a034001500c000040c01d142c8034099110040c100e5281030185070516082013420802c041d2000e55a8840d00c000c203001c59541700400358014074094131050840c40054564048410800e8100600c09030281c080f140307150f4401090b140e82 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 369802922 1250 369801672 369801689
    0x3110705070e1006030c0c03030b0d1e060e150415110d241a0a18140f090c1b030405043603020a0611120c1216091806 52
    0x210751900402c1480c58001c036601020351048190200e2914440c0c003803142c400d1001d4a403401100065a020350280154001c00b80d0003a6000b1203c8020030758500b0710707815460002440150301800c0c0c0c104401070f01c818640004480d4842d0640e0230310741c3c02d203a8010360700581008000c03103504c00c912030100242001d2503070003510b8500413a41c010340644c1903001413582083c00d4825142c0554400d6403c7c0042c086201c1c0790a090840031206c803040ca041002000038400c2403500c41500c81650104070161030880c1c20a120818602d070426070b5a04001d0703240c290160041381c015800780707004e44000a152141c0e0240c4607125006515606444400f002644c02500000b44140890314005201a1036103440103007226901c6030207145081e903204a81c0c95401a282c15501620910000352101000380281103889802500c08201c4889138540c9224882d006205d0181456540c0c4003082604400031005450305482c2800106241c40c203507000707221941100c103070000000c6000c0f5014220707401402c540d03101004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 369804172 1250 369802922 369802933
    0x15100b030c0316140406030e100507050403060e011e1a0303180103050c0c0312100906090606030f060819050309060c01090b0c120109090615090209010e041b03110705 73
    0x1003103000310061807007001408850603402800900441c0c004e07401618200d800c200030130041c0445880381d0031520350b041840c1d00302c808100500189108484049a0460000c2ca002c00e05104100543c0506c1404110440081c4401041c040015001981c0104600700d00d076a1800b0400041d102c54001d00c4140000600f82d079214803c845966440303505443c03603940020b2030180001d1002e00e000080d546645907140c029401d11b214140744104011010382074410310700c0d950310001880182c6005001c060b0111403c0415070034501500601900d0740c030141c83c03c4541c1840c00600212100003180300d0040d00d88000480d40290b1380c10705071700354801d4500054103c0c1e00002d102881d17200540119080c90b1003020200401d0f0f407200c11007503841c0941000800c0710140200100001c028035042204598001e16000904511050451f040c6d034034254445000c064020034030000c03035030700030076103100c2c100041d03409000c0c00c240b0202c04658031148040030002c0c0741e0ba0b22041ca036400550015140d0070ba030311404890 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 369805422 1250 369804172 369804181
    0x1302090d1a01081212070807140d1a060a12020a030b0613290a0c110409050c03070605070807020603070504030c03050606090c09010804020d03050c030a03020301170f15100b03 77
    0x203001c040900030700e142c0b44281c890802c1d03039a80782402c6600d103100341c2502244e5910780c1481111001c0c005040d12003088910030072001075125201c000c00d0708100c100c00000d0002e540c00c507030081da17402000090348120002d00800705c1e0b072034001103481884c100032400181d030b48041507410b400412a540100d07030082d00c04201c9103140f0890002c4101960712b031074405400f80c1c0461700000d004420a04035205200c5041c0600300006004186c40540c1621035020b800b040c07802000880c08986100b04103481551109665068038241030245c00050030340d5103006890500f454803802c0c900c0c420100006d0281e00004000f44a4a1041003624069a889020400041d40e00e08059580340300a580140c894004000814002d0882400329400b201e010f86555240d40e0310340e003c104000342c0c2c0c54030a6090100c04c000c4075640d00c01c10b000519480038207490058070b0354108a0400303030f402c95050100b002c5500912044212210014055060820409101e052940d8100071400003494990105421400100510 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 369806672 1250 369805422 369805463
    0x91f0303050d060504020f07060911060703020d0305060909031b16030302030a080601030506210c060c010c11010c05030f09010f0903030203060108090d1b020307051009150302091302090d 82
    0x8064440a6020030f10081c2d49410030002244038100040351800c2003080a0800102e85801c0750090038084c240d540300c0100c0304804034410782d0108208400503003000f410500415018071440750803d00c1a116a00c242c40c201940036a20b1148980840c190310600c0c11201e0060020451455810581c10200c500035039a0302e4007070b60b81d0f0000c10100f40070817020341c00075246502c64400c0c2d501c10030009250300002100e9140060016030180d0314801c0318001d00c500d070201510ba0000401c0704800c59400020015540180207100e0100081c40d00400d0b4145000d02410b15403000540c0d400c01c40b0254030048030340312101403500408440c200d0844103401c2400103002d254259025600ca07410030307200d140c41f83d6501c40c145902c0f002c8410468011510415808402d03104400c40e07078050354806401c0341d03117a5445000182040c0b444011500000b01441400d0001c070f000e0080720403600402e81020f509040c0c880c800070700718491001002d40aa94049000c0e4042c3ea46c481458841503081540c545607405400f40c0d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 369807922 1250 369806672 369806677
    0x21305180f0903070c0501031e0515040c17062701030305040504061e060509121009060b01180b07020406210c1505090d050304051201051f030b06091f030305 69
    0x54100c0361001200203000b80a010040f1110300d40c3c4007a215410b5801c1c4001940100402d80b21704070131034000c0c501c40c04280b580f8840c442c0180b00107001d800d5440780c00c40c10132042d0341c0140942400c0180300c1950381c5090781c0d2807202071382100c0d08407402040e4066106007010545142c055000e0080000ca00000c141038200c0020000d4540c04c0c0c800f44201c50701d0301c60041ca1140c0340b448141c06041101d038100480c0e8030980251102980c02000a0801c1c0007d000b554900040c034423440c2c040c41d9543c1007450400100703226801d6500000c0c20108140505810b660740039191a01c100c019042000a0840866440742d201d600600140054544400b000030148072043c443c41b4000c80b40d607035019030089000382448030240c030000071a950f818a0003081009201c1ca650b503548046507103220600001c00c05540e4080d401d40380403035000000601d0b280c1040201e488003810b041c10201c0c05211101400071812074003240f40d10260079203050265484854100002c032182600183c2003040c28207000c410154030900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 369809172 1250 369807922 369807931
    0x8030a05040206120c0705010c1707030c0519021c080c0f281107060908071a040812070c0905010501090512100e0706080c0412030f0c05031206040c030c050a0302130518 74
    0x300142da190610a540804150b185480ac403e894000201c000d40710343c110480900307c62422a06094070340c018420b04010b540700c848050b81000c51001005451740c80c14480d009998a00035040d800e0001482c03074203125440c10100089070001b55000403150108110300994542680801c0b4004421002894030340c40724003034080340c01400400600e2620a200c094269110000500700070307440d080c065030328090880511601043d061200103000b01c010f1204e6806902c01240d450361f05e2001d4500040c1c0401d8075045030f10b01e00d10f0000140120790313000d038201041da03c6c01e407070a501e04020f4407011442d1a034401403284641342840400d100400011506004841d10350700d1b42107054a5044640b81540504c0c010055080c0590117240040fa1040700840b0382400380381000307019002240c4801e400c40e0f110503824000e80301c0c0b81e024010582024810700075410703002c0c5401c000072405184010247d101750307101002019000310303901020382d5001209000501d0b00030b01003010003a4042040c521010100e9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 369810422 1250 369809172 369809183
    0x82809030318020307150c15060e0108070e07030c031b0f170405061506040e07020105220c0e100b0d0504050106050a0305030708030c120a0e0606030a08030a05040206120c07 76
    0x4103602c24030251851101c1255a00a01600d0301030b0800e140301d040100480103050402084801c0c180c007203400c1080300240251440004a03941c0d00f0240c0500301d810042c0c0c4603c00b56401280100f05400040c0c0c125500700f0000d140c003055114000308114040d162024860b15003902c240005002141c0009031300b141580a61696560b008200300c514020020455002c0d10715044040040e5565103090142c404400c80240b081e41019103035805019000c0301242c1c00f8002d41e64078014804001000441001e0302c03d60300400e000d5003181a03843c0c1d042c107009803059001603040c000c0401d48418012681001414bd07090303202c1d4955150281c04e8001e008150303419610365207400c60118031818030081d040203481c1c202c8000c1d0701d04004c03651a6890340c0d2005200c54809a418005101209219103501c1d01644210302c0101700004840e0000d0b0a042004e0304d00d5100e80d000c1703501d60000503400300c04e481c2e0017110024000781a0fa070310700100f405031107140c0340c1d0580398a051040110840305000504281070041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 369811672 1250 369810422 369810431
    0x5010e010302090a14010c05030d05010602120301260f101d0115060503040204020405120a20130f0e0313030b07030c0509061605060709030b0c07020604060828090303 73
    0x10341c00c0307110300088650400c4040200f8409480506030030b5084c0c11043c548101500c2c00741c0c40741400d42d04088400c5414948440040000940c10090740307203207e00315940c2c185154508107010045441c804080803c002d01c0380050360104d81c06000101c1d42c0003260381580d10041500d005070005084a0075000004000885441d01c031400505c03030510001c12040400095604100e81990541c00c0180100d9115800300408503842d101c2800c0603800020f214010070b1007541910b00345000030b922440c5840840145540116140d07508420104c0449032103100180d58101c3e000f125001c0c1c040c1c007010013a54800052196810740d04e69155004490203001e5640c01904c6407801141503800035501800044c0381400001c085240c000c0041c80040e4110006000b2081c2c4c9a440e42c0c140030045035100003040341040f0410a10200700c003103651000100c00c045203031441d10fa000910301c0c02103004400070803400348005420314883c010031188680c1c1c85100c0c45510304100e0a0782000e0306450104900080c2031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 369812922 1250 369811672 369811697
    0xc0f0908010e0303010618080a0b01031a070f0c0302010e0d0503010f0e0106020304330f0f020705180c0c0304030c03020112140a050907120c0317030c030a0b060408030d05010501 78
    0x40c400c0704006555000991300d5646410401c03603050000c00c404004c00c8228490000d2203400400c0700c500c94500c520055589589941465140706207040c0d841c010a8070818108540554410410400c100c00c0d030400d8010b80c082170408070300602010401c3e04403132240140f4802c3e0f2907000005541203410280d941032820f5260400c49031070b02000c4c8241c0004d81d105001c140904400c060b0401520001042040d890319002007070103180001d0100c0348004941c1d200400c1d800641c0c00aa05140c006090006140940ca4040030841060295141a46500181000c074414019000441d03843c40010710803680c440d6201c1c140503402c03500301d100482c0032940c409000101264640946003401e0041d40894500ba5281e8031401c0203048020403500c480e002e42e88000c1511828140c5503103009000d204100081400c607e000040b0034940070a05400b0074040c0100280c041e1010116076020b226004007260234540a0080388a80c041d581041c40c142c04042000e032000c800c150701080c103c8400340d8a0305a8100d8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 369814172 1250 369812922 369812939
    0x1b03180307060e071217180306070c0c050a080a0b0a0207020d08030604360501020906040611060f09120901170403021506040501360501080609070501050a2a060c0f09 73
    0xc0d07500021b001e4000b040301d0700c0c445000000905a02c040c075022400c1109072140002e424607074129001004030704c8a150f42010b02c44e09240c2c3d00c01522302911180b00ea50b00b0301440703a0b5206500917006010501178000905648031680544142650182c1620a00701003864400d0003500110703501409145061441680c45428000300310780c0e2140203d54502050098881048101c4e02c00810380f40d9640820144013152200c000902c014641e0707035180801d60030f02403a82420800d010b0b000704210718021050081006011404000c40c0f2200c10105a64006040050f2403a020125150400c0c00400f070401041c9500403d46d4900c0d000000021a0715960358407c1200300e501c2030086250724142440d071940d010710200800d1012100c98801c2004001c5a0040e2600713070303642604444110340045080c000740410800c812800380500342001800c1840308000103064010003011a000044030050414094405000800450350030802c2880341c0d60b0740b114083d086d2100010810b0000c0c4090f640050b41c3c20 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 369815422 1250 369814172 369814199
    0x812220501080f180f03070606050f01080c1b0d0309030806040c08010501031127090f0c03040204021b010911010e0901180c14070303060303030c081b03180307060e07 73
    0x81058442c5052610b4000303040c03c1c003640c01405078140801e415080685101e08100707a46400700010f00559884016140850503280613500080c024001840600e220741e07080403411740d10440e0480c00301e440716001d42c1c041ca02c01c0000718418200380281c2d12480400ca9040e004660b00d14081d403140045a1108000e00003200c54200e845000650100014820340d0720036003004184103005c0c80c88504041c1d40004c0c080c035800281d00c01000340d64811300010f402d401d18801c855849181c4445544091a02c00c040210314400188020303c07542c0d0000361600fa2036042064410004882c0380200314002031444c08250a8240c1c4502c10b02142507281c1d00b00003440d040c070b44a81a11000d01f0b61a4426491031184e102906a803903440f01449004050f2900c0c2005901c0508030321802a40c0c04075616186080140c100c1e400c403c0300200b003264140810a1480c0303c514913440810790b20703c5007903807640c0309412028042c801c4031101200c4c1c007000510311700344150782c2c1004a5413000700003542e42050b0303144a01003030f22 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 369816672 1250 369815422 369815429
    0x1030b1c0f06050c18010e040905010e060f010f1a0703030204080d0e0307092007020109030b07050d0c0c03020d08090c0a09050411030c010914060405040504140c04110f0d06081222 79
    0x8000c80c5c4021705595210703945038800248041c1c0046891092a80c0e520b0948008040c0c1c1201da9200c10100030100680090752401000b00f111580501800d0220ba50f0f0076030408000c601100d04001903d07030425119034100c8006000c0d00040d0744142814200080c040046a8040342c82032152100100b071511041c802c0f00b03515a1323184039111110000c1e40318034000b9000301c0c0d0b0603418800c1c07004000011424100a9034480e40f03a9a40d02c503a90581e080403502101c200103401700810000d010018002600000c00c039072031604500703000c5210354519100d140b502c00c03100c14840d00f1020184001030040d0302a007010740294402e01810720301840b120281550380c5907100040d800603058080400485000080020388688040e02c09843e044e1500085001e58105680485040707038107901c1104118018010250b410b1001c4605100c407042e00d4541483c00c0c01016440100903070002035000c003140d803c2c2c6c042b0700180b098000746c0780c00c9085400f0302d01282d004217071081800700148020351403000c0c0108424054 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 369817922 1250 369816672 369816697
    0xe070206150334030822091b0815130207020901050306130b090a0f0b0f130321020408010f090c0b0f03010b1b07080706020d0302130501030b1c0f06050c 67
    0x416510740f0341000305028690310004548010507010003c20b014200401410000b12558801d01480704c415240310141c40d07011141e01031a18543e000052802c1e010106001c003e49411b100e00d0300c1c1d82c0c01404d049030165501c26400080b00402c01054001500a050414022260340840d6030782e417014541c46600031150706101402d111422000180c0c1e100b1940d0b00403000c00708440d40101656543c005d070000159040c0d4603502940208000c1c1905810110341c00880a030401015505903034002d05280d4141035481c404c2400207140a0411100f9030507a4010303d0380d40020b0003194514000c1d0740040c49031680c2035914042c411404200c6030707014400c07180c2500c01a05a20304e07503882c11143c0c1c400c86c4c018294a452450142040f400e01403020170190015010046c06004035a2804401070315241d218440c0c40f00785401401803030b0b03203a10741103030880840b502801c1c0441d07400e100400140001a910172400c500e803160000d803506000100304042a5640320300c20811198131160180b0105002c2c1c0d2410611 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 369819172 1250 369817922 369817963
    0x1104060b040b04091e060e0f0a02070209070302090f0a0905010303091703070f06060b0c100b0d050319360515090d08090d0f06050a0212040f0201090e0702061503 71
    0x1c001025400401d5030420540041c45d0b881c5100f0b07004059464692200903020140c00a00083c004508601600907502040c1140b4108a544c003151a8002c001c0c4101c0c24164040b40044042c0c580713408016031000700a00c18140345841d04030b48401004280801e400082903108003085102110542c40030403c0e8000c003d41c104002541c80d808081d5a400040ba00780d5280e010010700301d1300c0b0f080540311400e00303917020340007141d9020740100482d210402441d04c03803060784040c000403840200231070304149a5401100e004895003c03040c0c859140450313201c9280119400c1c03c2038050402c2480e1581d07030250404540440d6a188104003410070b44d05096a01200c0400c07819000786044031b904440144940252800d191f16900020403595403500c00b510001066245001041f146105240d4000442001142881000c4500031035420b4020001451102c88804000075680a030720b5900080011101e285141d01c2d0007070000313456180581320040840303116640460545000300300346104420b015030031003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 369820422 1250 369819172 369819179
    0xa0b03190308040b0f0601020a1515150e0a0f051201060b0a092405030f090a0210020c0a23010f021006090e0f120324030303010605090a0b070309030b180a1104060b040b04 75
    0x90460304100342003408d03d50341c2d62f6019410800c140a0314001c0041107242c1e0145060b01e43d026100040c601c10700b0b4400c1d00e15282c00e0142441001140381030380e5083c0c801440f0507541e074200da40140602c1e08058804000030540e89801036111002c801650006039200d5050a00c42c503803c0044420120b44e0b00104c0d400740005074480c400c10b08016484580c482c00c4464200da07503008240d504001c0c01c90a401a003041d2244925410808207041c014039008402d0005100b45039824105440b800b0802030400ca09045c0701c060880c820468000701c0114400c0401006070b0b1650080001d04412041c1d110354020030000c1702c420f100100c0c014440c80b019000e941d1459071003860000c541c1c1903544410814035403d11a202c0c0c2614108043d40c0038000541b6495624031190003000f0010310039074881f001d024410418240000d0b40210810102ca502c412018070940382d2202c0e00f5820000c9183c403090034800d0a400906200c402c0700520103034a0180e40400000e03444401c1c401003403103940a080e610450402040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 369821672 1250 369820422 369820433
    0xb13080105011508090a1203061403120a0305070923090903090f100207120605010608061e010c080f07032d0e0f0102070b1303030e0a06080a0b03190308040b0f0601020a 74
    0x46910418400980c1e01a00300c41e42d13009243c1c1c540c00c08440000e275951400340200140300f4500140800704800400003c400078007405014412100588101030700c46022480d0b03a80200b0f07071000a05850540402020400d81421b003524126000f034900c540f400002250800d90080704407289810050641c20b04000c403407041c4014008002c2d50041184a516800038003c03500c2c002800650744100c9012440e9450090004c10200010f05058490703002d802e5488121300c501800582080c10a0805200c468102d0801001740c0c026051f102841c14800501c0ca800c040d407281c1088aa00e0b092184129491303403804407603180407415030824001c00c14614460072245801d85c8420000001441141e100350b484a0700182030350403900003d081114001c405208254000c1c029065032074080d603803602040d01d8010010144000500034400b07940e0f460381650955103041c005d400118280d03007605e2848010914005105400c201ca00f034035020708041c0404c52100c1401c0610f401504141d00425144440307407903030b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 369822922 1250 369821672 369821687
    0xb10050d061505150315100503010612021e070303050a0209030a03031a1f0f081504090f02060307201506120109021009080d020c03031603030b0a0b130801050115 71
    0x300b41000d03042c0000200f80d542c000c042804d449030914010780701c0c105580c820511109051907030740b0421040e282c49402da03610100380c904403011450070440c044905c8404200030710881e26400e1030f0800800891b100c0a06507c01010420702c26501040310b82d5500d10b101c4120300503100070782da1607041410030750003107072003034000002406046000c402400300e840001140c0d40d5040b034003151003009102c050100d8541003901c070010103019040038911494120381c6001c1d4070310012400707840340e40c0e60031101d401d00c84100c07503003001603901805841d6a4103110030054400125000c2c145400c0c0c0d8810725403901108007003002c00101900d441c61089640326101044004090901d00020941d070300d04200c409a501d00499940d0b07100c40c0e0301d403060782c0d500f01218542000e01c00d907200419035001c4030484c0b140e81c13000030480710300c00b0300201c0032481140d03c1d150860103040402c80e0140d20181e40740012038092441c800614440380560b8501c0011540c50519900380e403001d1181d0900010000c810014442c0181107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 369824172 1250 369822922 369822941
    0x603170708091903050d05030f0106080408220515040b0703200604080405010e011d011809020c03040f0609080606010302070212100b0102071d0c07060b03060903070b10050d06 77
    0x81007401c080c0da0b0808030304401e40ca1400ea004009200004005111081c0308000c0f1002c51840c3c210300c5c51401b0802c20900d0710043c401e4104102091000030181f042c0f44040c1c0350a105862448240050800d8a442c1c030203483d80203891203002c10220f414107a040d070000311012503418810840c00e280300c544040d12150104080d07880198140e0605c0d80078020700748295442a4800c21500b81c40b541014001015500108002c5040c4916201f44c0e28144c2c0194a07180403049017460030400a049030108180c1a8408d54022400280045180140b40901102400c16101c0002d288584030307545036011500103126200c0c202c0e4039040a00810b903039501c00d0300103148190000d07003480c508010603007500e0320381485103802241d000d0b51100701c9240b030b40e810312041000303084c00c10140708003400155000c001c0b00000740940200c200009028010003810790003c1c100020020155000c1e071404042958480d401301000f160320103284000075041c685400362030410b4500180203c040f804581da20200101050603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 369825422 1250 369824172 369824183
    0x70e0603071a0c0705030d0903030807170a0e010b1017060102030304080a050315060406031e02030c090d020f03010c0c05150f06010309020d080f130905040305070b04240507021006031707 82
    0x70340c0851551000c000d4510b047e00b031a6581030b106807941c20300070b28140014051900b04041c401c0d0078403081c01c2d01c0350480d0300315100440004100311440140340c010008bd104e450341004404244446094000c0c9503401c40d0700100c0489410360743e0300b0004986a10080340c0092184000b40301526500f4421405940c0c008031254180030103450a80014100ea00a603018a0009848412400c51051083d03000d00441c80f078100c082d800c5040090b03004800340514083c05018000141c404001d6603203409115800600250003000901029000100b14030750b180030549445c030901a5102603c2401e0709000d00c0303688645007140f15a00e5001c0118094021074206a03882030061800c0c40c0411403010081c510100303445049503540c2c180000709101c5404680c000054149003a04010100390468100c0e13410561000150090b41da407860301904a4550494a0061018405440300a40c0b8a54070060140c400c40e0200d924084d00c222075401580c10320b001c002d0001025454440381401ea2101601140d485035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 369826672 1250 369825422 369825433
    0x507031107030f11030d0c08180d020603010806071808060c0d2003010504060902040b030c07080403060e0c0a091a01030c0e060d020d0b15040311150c070e0603071a0c 73
    0xb0b4503043c00c01c0500040545424005480143c00c900e4108021100b40b030180c180041c408005481d00c600500518516000c80e000740742c0e0001040d562607480c001300e40d50080100e9140c1d41c64841581d1b58800c11980d0341e0110b0000f640382c021a84030325802c3c01c200c64140c0f0041c16240c0e18490a04d0aa800c919200e081d115180c40740512003d101e03a40d0060004542e4104503140c2d0701d007100704030580c0c0c1c0035031000203000c0c81040240581c07000310301100d6108941408a5a4940f623714240040e4800c50344090b0ad641d2400d41d4103c1440000728180d4900c50f001c07110103030b0307030340d110106030085903212a611211506175400450280d4000e030040d0048100504201042d04a40f10100d1055444035500721021540000d1f5120520038902c01c3e2484040151001d402002e020201ca01503845035001c003a210342004100c007002a46e82d180c40c40891403022402c0e43d141d42c41410380a9603100c0d64040c0e4001200650001003050030002000350403140d4908141751a42014001081c13264029600c85509000d107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 369827922 1250 369826672 369826679
    0xc0b0901050d020c01050709120b010504020a020f0706030614040507120f0f1404200310020913020d05060306160e0607020315130c0b09010903021201090605090102090111030a0507031107 82
    0x200c3c40a401408016000400c00d031828800040c0b01030900d4000303082103141450110080303140d5a403d075054882c02d440060340c8130864030040e0b1a10611444e01000c5114030707000800c21b81c3c1d058000104a4a440312620301c64000c1e08200410f548089400100041010340718200f590301e02e40000401d040080c000189a01d0112605802d640f03800d007000da0141d0740075083c4002c10801107121544d0001c600b0355148640905070000c1d0b12040e46076078186180c0c1e00480c0807a480d07aa40280307040f031038011035021560385d0452510100501800c0f0b482600c00d0007031f4000a202c0c074440702c92a0140300410340d103c0d10040800d608000b9a900144810b03070701441442015a48014030441701e0b402261450b07103c0030016070030314010039140c103540c1010000c0311081c0540300c03d503600010358400381c0394102d0b803d10300c07080c66405075801015072000142c1300d1400d01c024458036150660040c00219020b90390084503d106500b0150740344100003207140040d80401034500401d10802000040420036815250400da4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 369829172 1250 369827922 369827947
    0x9010216020907121107052b0807021015060e0103050f240306040308101a03011703130314070b030c120601021e03031501020d140f0c0307140c0a030c0b090105 70
    0x200d024108420400004101e4284041000b2101a07149428880ca011000107820345a08c1c080c00341c10ba00500c04500085492036000b03010702c40035a05041c00400c100d998440b0707904000705441c811030b0041210125154495403281c0111889100d0b0350352030500c02d850703034112500031030310035802d000c1c00c003c0100b00c81d000c2e42c3e0300b4041c541c007940c020364035090142090400f00d50403081c280d01810050402104440c1c8040b030030010303a41100c00c1a01c0d00010381c0064920030f82584906100d000d8541085031000c0200a401c810502c1c0c50300c8250121241e194644c41080e0040c44140c488400b1300c8000c3c0611071001c104100d0070f40d4010410700c1940d03e0010000400250f0305c5141140c42d2241d00302008100a0045c2c00f50300f21900242440144840c0881500140030307400354000300030410752300041001021000004271441d04514030b045a980e4400d504002c40c003245d100848240e14092070984440d40d15001d2002801d4a030041d0f0480e10580c500b204010b00740c1c2c0640c05031414000c003400400341944 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 369830422 1250 369829172 369829181
    0xa06050a060c12260a020904050108030a020a031d030a0f050d050906030604180c060903064205061309060806041a0604090c0b0306150316180b0309150901021602090712 74
    0x3000d0702c0c0903841f840d09004000580b20160828013880d40103000100046500158100843c1d4060500ca03104c000704086180e0440303000c0106a40500c21441510100311400e99038110b0140a0f100340c031442d5034400c070100d546100c1d200301e1603031054003031002c01e040c1d00e403e03441404608072110075180450441c0d500c1e845082e445501140c0810210318041042c000540224032403002250380c0a150045491520304990111085a980b0f0b0001600c4403840c40c00c3c80001e0501a00005103070680350801110380c0b01100840e07000f050300007801d0040c002040e45000460601441c2e1201c12a034910007034140c5811401c40091a8070b030b1203500d07000100c0c080b8183d40c0380c00e8098041030b18090356a141100a02100c50090078284080750001c000f009954a0181c1c02003104515601d4814002c0c01e1b8040704840d17041890300100310f4003000006102c01d241c0000340244c2e44c01401052a016030342e0f841c00c12400c030b010381010780303992450607a5054010701c2c286200342ea10980740d040410459030f5090601c0201e8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 369831672 1250 369830422 369830431
    0x311130c05070c0510090b070f02060c100617120c0309040f09120c03050409020c010f05070206090601060e012003270a050909030703030e03070b0a06050a060c1226 72
    0x104001299824403d4041075200900000e54a81028101c00b0000802d41040da2040301d1494001261080800124880307024085800a00748c5849640b00d6a100c0d48880d50101d1002c80145000b400080c103501c440c0c80b03108a02d100001070100a0800030f800c032070711b0b402503c5500303ea000400440f211030341d03203204000340e001000300c0c000b40b071410520f40740d40b10b5038030000782100340440014407031300095001003110242c0b0424200980c0750307159107a205014003000d030351040b100f40c148010094065070000d0f90310311595408040b98810b99a480d0180c44d0110401300b03141c0051490841d031480754482164940d982441a81207929140301401c3c00d50b2110700a000c0d00d01e4000c02c0c1682c0044034a881504e60340500400c451987c05800c0c0800c9950303581c420b0003c01014151a1941d2200d07140c01031056440007a0014485411407916107508001801e00340283d40c400d03102c15202203038142c421110340818950145111580c1000172000359020841181106264428080002c0c4041c0c080740085004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 369832922 1250 369831672 369831677
    0x2151905030a0c05090a15210b030d0c170a09080f0d02060a060f090903021204080709050a090210110f030d0f0e0d0f051323030111130311130c 63
    0x40b810001c19070000c0d2211440d80a0801006110701d0b10281d80d0440b1901c1292140c0180e00740c4140594015200146201d008074058204008001c104a825070090104100c1c1282980c40300d06003010300b585c000445070406880200d40e80c112070f05c4082c00d035000304410002d90811220300b581c1c40c00c1e080d1070112104440861604040e002460303032071701049a541c028a00340e406100701410f005081010409a01c90500307540c0e1200807900c2030600904c840d0703105003548640e20380d40b10b13124070740141d075020305101c1c3d2a001d40c602400100c820798288580c10145500800c0f03054540b031105d00484144407420100000350144d41444d002c440001c10040003124108000810302d1000d40069078201d5030b800c0302601240c2c024040744600b0a5120003103605400407400c00e035440b6200c05061b071a102c03d10350841c00c2420104400840380550004110529403402c800a000d085001e440088490040541d540842c80340f0307060500015144510035202e0900c06041d040705003015883c10021b079440f4040c01c0c0301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 369834172 1250 369832922 369832927
    0x6050a09090605012103180905090d02060109060b0f1305100f09050603010e2710022d0f1c020301120201020d03090312020c0a06060f0626010302151905 67
    0x400c00c85004560051440f0080030850900000181d84020b5805c2002010000b461041c0311228820b01b141402500303070101d00300001e04d05000700d10786d6800c520404a015114507800054a40f07403d0140800303560b01c4040ca50f0030011000d225072000d800140149542ea210b061001c1080d8441210341c409496107984c076406007441e04c4001600b80700c00d6420080c0071310002c000502c0610441800c4640160707065800c501000c46400b510320210301400d2a5101c0d50045035044805020079802900000148036040c1d911070304807003804458841d40ca03290700d54404081c0001800140c5200291140c15122940d040034442035150b83c6007240d200742c1144007605c04205175101507503810040d400d0700900b1810204803003491624007074070551410303203000c03c0c0c15000210000030b09c1c401d11540302d075683e11903001c3c0a442d441c3c2035001800d00542c015200007628107046400000811021121000464810303000164219006d22041001040c1510a0700d1010000511903518080f40002070720f45980c1d83c0794 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 369835422 1250 369834172 369834191
    0xd05150a060804020904030f11190b0a2903030d091412270f10030b030f01020f0f0702061204030207050f0d051b040f1a19030305071506050a09 63
    0x100c0501500001c0400080304200401a120600016042074250508281c8141355000440d883e440c40703600d101c41d90040110200303d0100d00482005410b11841d0345503440c1c0da80030307401812280b249103600829041a0400a900140c0c48040554a1000343c02d807842d0140609201090307801824085a4101a45000c1c0001035000c1c000152581103003000c245c603000710304829400c1120b0344c140f0244001200c9840c441c460f5980c10181d005100c000d0090403d40542880c045c0c02404070400c018040d018032030611a05480602c00c6410464440c502c480c140302c800c030402801781d08030310030480c1c1201c0108074003000340d421110064801c910036030051000d241000701f07020040486902d8680169281541540003503000b203200c4840b019030350343e050311003801880020042d002d06009445441c2ca08000d401000c1008007c04045c020140c402c04040901c6241d031502c1c111301440007400042c02441142c0000c0c042200c0d00704024802d801c0401e441d91101c001503584a1a0343c00844059038928800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 369836672 1250 369835422 369835429
    0x50304050901050a03080d0c09210308150a090e070b0f030a180c051002010f0c03150e0c030c220e0402121f0c030f050106051c050907060e060d0515 65
    0x1d0b002d4102500d00009181c615502e540306170082c0e03550300c82580d440d003020884003032003006100000c240c800149020003100083c0003000c241d01d100c0540001e40a080090031207407019415a031800c1c80500060002480d10304803d0040c403401d01c08191a00410400103281484080030341220a0312503805503690422285050848038001806c100d03400d00a0380d80f0010031500840701c004c8580c1500d03151302442c03070392404a004146006002440d10704e00300c183e014540e416400320000001e00080400c440f600d44411003498030085a1038800400200700007072192007440c014060726000f540141c0301e80f1085403002d21280f400b41d00608000d6030058100302c15860f141c44410102400391010b03000481411a07503100d0502800050021107448070040f4203068401e130302c2801c910311000802c124030b507114100249550b00210b0a03903851040d1440d0741540c0c0c00310b032040074001c0191000601c40b051170030005841d001200c0412035030140d0301340030383c64407145c9500a152088507405030740c90b04402e500040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 369837922 1250 369836672 369836689
    0xe0906160c0f0302240912070b072a05150c090102120310050301090f0b1006090e07030915050405010c09080c0603090106080d0807120c08070c050708030705030405 72
    0x140000040c0c0318100c40c50140c11090101c100c54120740c9a051082c0542426850400c00d90440380c850b44a00154240801003000b5280c0a0080482543c10311400c203035441d0b6039401000c102a000642c00d03404289200e000b04075400c03400b400c00c0315250101c101014240c4041c040f80e1030640c0e658004144064100c0400ba0740d156001074100c82850070114540700003542d0311941c612001140900101050728040503120800050030001d009104100803882c004d0714220212000f140c45054403408244421941800d01c2d003a80c405960750a0300c0c0c5d00e80102c0300d204503000741065052643d114110740114400c803840c2d205814800310049050f003403500d040d0f400c45052004a1080001120003441412008151040314050031158192240c80380c00d07516005014030b03841101c0510a10059040050300300f64a11b2055003251504086a8081110001a5194010080c0010b8500700000b02054000d00011240900440440d40c10070323120f00d0030300d00d1940b1071b1000f81d07055840441c0070800c07482c19100c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 369839172 1250 369837922 369837931
    0xa08030a1a010507051005191806060501171302060f030906061503010f2702070302070303080105030706051215100522050f12031e0d0f0902060913090503040e0906 72
    0x2040f07494400e4544525455901c00c0c442d040c1207035101c1000c5190341c503e80a041c1040390b0070f404100300286200c914000140c4504c042100d400741001c40014496000341150500301400b6000000e0300d968801010900e041d0440c4104e034000d1003480181620711015014512030b01c0c18000400403428420304116132301404045002041000700010f2003000c1041180c1e008507050507554808074080000c00400c1486518600c000e060b02c0403440303100781540000c020044074029184d0050f242d8891040c90380340c400383d001e4000130540800c8850fa50046900803d58485000c8240e8582c0c40720b80c800048054075200500b4001410210381200e400400e05641c0e00213800c00d04425511030301c0d05000c10000711918080a11a245900c8525803222062044403030070300111064000d1800369015001240c0c200c0090801c64526002d6800c18a0b60584a03548900340c000308180d00742120340c0100a284c4942075814001c3c49d840b514207900240040000d44042c000402281c18203180003040507280090041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 369840422 1250 369839172 369839177
    0xd060b1225020316050c12150a1401030206090d0219060f0504030507033002070f0b0309070504110408070b07020f1008010e18030304060b0312070b0a0902030a08030a1a01 75
    0x290707480c1c8954001086907094283e054440700d80c16030030b00385141000d0200c43c2c03403038100c0405513011407242c0700030402500d0b9140c91f41f9006050b895144850307040b20581c142242100154000600151403c0006400d17081c40081207492103620a074042980d00e034400460214025001c107060189a411032004101c5404600d025810507145448880da100c03078a12029107080130190030340c100705800401012414000740b40450800e07010300c070000d40e6401c4500c181d01b840103400f800896050f2040044a01420701500140f5882e8181760420009241c00012107070380c140308010000d03241001380080e0000f00300c5515419150a4580103005c04146d0314010035108032802c044984009801200550544103004d45184217580c07544000d00581d80340c03a001d17107802d10001c0108001c2101c15000740d4012601036040d5000800100044c00c11130140000007003904401c02d0001d000b00403994048648035000a0441e42c901e0310a45520506074000d031003080c0072980303a9004c81424a80c086114808890a1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 369841672 1250 369840422 369840481
    0x9020711091b1c090503032d091c1806092303070303030b0d242009010c291806060d0b07211a090c0406050d060b12 51
    0x10010074500c01d454050f411441200d08102c90954607501c100101644002100da407400c103190002c0307480e40b100d2100760415100180c5440c48075100a0103a01071044800142054000b00302d4038400102c001805a0800407070322000d801c1013042d24001d6004261546440c9030140c1412001d117102203550103000200756503081403084640b000644001120341616001234011003610020312068644800904545103280910314140c032400c048d1b644003010700d030080005469280300307601c83c0004810792000c1800240429000c0303500900165110501c51400c2c401112031885502201112485000c400b13401903108100c0750301c070442088440c143d510f0b0300400c070900e4040001048042c81040c000e090f44840c1020a2040d40101d490b485118501e1004440c0741020010b050010401d40440c4020305880b03080f400d2640c2000410369000e41c090703450303d034a454240002035480c0d41c440c1c0079006902c6d56031440000c0c07106015000e0040e019003d01c003000b250030515003072001d00c80d40c3c2494144c5418070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 369842922 1250 369841672 369841711
    0xc0409020a030f0309030204090317090a022101150b0a27060c020f03010507020102130e0402180408040f080307030801050414150a0504050a02040501180303080f060a0902071109 78
    0x801d100300040b20740c060540040103055180483d41010103600084d005810a010b110815800811081860382c1e00b60200b007080d6100460140d4aa540381d02c003039080505504114003100300c9643e44c1e0b41495400f0008201500101c080100c42440c43d40404814a40460914107695001081440e82c0003012440f10450300600da4824002c01d8901c20242484090300c40c0504644481c4c200c103009a40080080002d80b9004001074040d600131825403039811000300c4041a82d03180c00c0781c2d80340681d2700505124514290780d41d801a040d000908295440f031800d0000240e1036039081407100180c580c06003e0364461940c1e150242001c007041e00440d11540c20120707844147c0980f04000c07070b0f101600008044104101f00c2c086210801e00c0d40100341c01500385400c100402203039030000c0044a42c00e0741c5620742468081180200316005d4007009000403002d202240030301c154030101640051009000f9000300e0b94905c081800c903030107444100c8200403841e40406840c03401d030001503400b45503e0b1f10600c02d0320301c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 369844172 1250 369842922 369842929
    0xc0512060f0a0f0e0a0c0905310503090d1109010902040806040f0206130608150103050405060f0618090607020106090204050d0303020d090b09070305010c020c010f03050601020c0a170c040902 84
    0x40108101d400c41e0752044072501440454102c0404800c032207017660807415650501100c02910f90241d49410b50a10340410b10080c607025402c0350446c04134a928900c0c041d40d141140b4040116070040d40c0314402881150115030710410f4041d203652041001d14410b03080ca40034031824480503404401d01c01c0c41403108000d1502c001c01c807594000c0e846143d80d45094914800914640142d51361001c1d0f5002519010848581107450342e0702610700410348400105444004406840b822207009200740c22120110303103c01c40c3c100e12281c000d07500526000c8140000d02e800070801c0c0f4110390000b8103500100034002065020301c0b40d0400f4000210080d85024203041c0410101080d500000b01003503400100c18840416550294a03400d511005103242c4e07041a011a0780d440c4101e0000362819441d1950505420313000180a400c0000d040e1540d0b140740b4854030041e001004002d103018198043c00c20024110f40d40c85c007a0300f02a1a4000e200080703c80840c0150f85400a0380403514001c0b031500d06400096134 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 369845422 1250 369844172 369844201
    0x102011802010813081305040b0a0b07080309010e0a06051e0c0307050c01060f0b0418021c022802030d060f0f0b16080a080402100305060906040b1c0c051206 69
    0x7074080c02d0494040d00c6030b038151080041c611401a04002011400403131240803015000d0449004517000d220103240f146c10040d181e0554841c4045445040210000040c5003030051940b101c04c510002a4107905000020304040b40d0440496842e980d4101f000965a04003080c003034070340030b000c18218a070300e008980b41d04240700203081c4070140036011825100520094110314094021040a05202c0e90f03142642041c5412500032a804000664040d041c0072506200b030b40c0c100302031000b2659091018960704402507200c22201d0a24030540d0810054030ba1003240202c680c10500c3d80299076a160b507100c21000c446881d00120504100280c2c200902c41050943c90142d8000b8581255145500d100c08582c4082e0900014008180820124500d0303030413500c0c2911550007621480c1c88801d03c000c049045070811030b01e096100d4040303008545142466488403000520243c1004801082070800c1050044603000465003481c91010902290070503106000d4980803e038011306a50400500d00c10091 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 369846672 1250 369845422 369845471
    0x10311131e0510030f050c01091d060f120d120b06072102070f0303121802031f0f02130314010b060307030e031b0606090115090501140c06010b0414010201 68
    0x42d221404201200b000308464401107034020440304500403140780940d100e208900103a8041002958006122120354480e24980011409404407030740c2c034101084600b005540340c154020384040485460b00100700165490400c00f512182580304480544805580c08c12a5890140c1d00600081c1f00151040f241d503a441d00000300044242c2c18200d9007240f400c08541e210004680401c0000018160000d000705032003407005900b440792400001000341c0c0e00703402e010003e400d41c2c00191680510740b51141c00c1e4410b84205800420355003c0c1c0f6401a05130382200200c40212560000c0c04c00801202044620700c000e00b10340280030300140c840c002107850000814560600d44c4940000c00700420510444c1c83d0740d01c80038101c01080f42e489000c25a43c0d0307801c45602e40100c005100200340d03000c1125417035103108003d0f41c0b440c01007424030004440400010b081c080d884081030115005a140500005000c3d14065011716103131460444c00b00140048000c102e415a45002c0480003400700d0307600c1d200c400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 369847922 1250 369846672 369846731
    0x21b0f0a0f080904020a051b0105010e06060706060812040501091517040305161a07110303150a050a08010504030f09030519110907110c15120612010501031113 70
    0x400c40e81e410040b61900c01c03601155406480000d40500068004000e004c402c02d0503521503950400d049125400c80e40227015900741a25200f0000f01e90b86401c074000c00b2000e100300c4010610660760312404d0320f0603010081d045d0541ca00442e082c0215680516520010912030b80309500d51115035401500c003c40d14040d03503072500e01e07107000502418018821226842c0280222001600c0e0600780101a03003040c501045c4940d00d42c01c00325244500c00d211354000c9000c49806035103161580c45080664146a4144907000a18180700040d140e82d2822000001e11902001158615003450005e000901030740810040c04109d00341030010610000b000c200c41810030005001d614200e050406001082d00540c82e80720607110100002540d010f07072201035142080c8200e5101c3c0c0124403c00a0401d80b020303542c0c3c00f604090042141c501d1000441580041c00541400001c03071303103e28004c0c00e540090700140c44421000712903804034102030514003142c0c003042004002c1c10b41d041d030140d0861802c80030a07030030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 369849172 1250 369847922 369847943
    0x5012a050301150f11060c0301030b06060a021b0427170f0702091306050915070e01120902010912050c09060d0b150109050a06080a1406090403080a0f050703021b0f0a 73
    0x1070130790181e61201004a400400c88601d45440d540301d0f60580d10074082101e281d403009003c00c0450918005540e61414284c001e450071501c030864101076003103035420030380d40281c8502240582040c050368541f002c00c8802c0d0104050501410b150f0100400c03003000c401c13a444100b22401c66403190030241d85500c1d1741243c1c14155030b1290780030114008200712000c0e046070320300006c0c055052400600c0201080350094813001307a56800600750b84040c2071100c00b038042141c5000f0281c518403540d00482e10148141401450305450b04006071801074503450841303003580825040002031400c210500da024008640800300d1603613540d03038421500c00140c4160041c0107185420507a0ba0300501142d400307071101426103a412a950840208006014bc80c607039000e0b4944040c0310022904400a0307403007800003410050250701c650b9012144210010100c4801c030740c1c0c9051030481748080b07000b410f010301e6140d0340150721440d0030345080428201300450080d05900103c11003150010200b815030680e5004002140c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 369850422 1250 369849172 369849197
    0x507080408030a050a0b12030d05010503012d140708010609050f0a0b0a030615030623031e12130e0f04030912020d0204050c04031b0f05090703020705012a05030115 72
    0x20380340c9015010307440080c00f4040b11f80e030040000640590701200748180000e903603450606007245d08414a008000e41c84d000c01400d00007020b00742d4051030b440003000080016104880040c1070b84c040c7c400074000b628003c0101302095101820030302900045071005a4080c4000020304031040790701c03d001184201041e10100706000ea401180100300600081003640c00b038600040041810380030302e00007038030005801d4440f041500c1460303c4281c0301400400030000d48d015a00c1c0c424107681d500e0034840c03094a40c2d2041d04642c40b00030307010480048002021103800c0006500c00d00070005c00048103088480108030200b98841c40c001c0c00c5901c01d440c0e03101ca0712030b5400400c1100f08980c1c4080c2d009801d24060009003208500148112400707811040004402c0c40242003115a16128980351f0314406503091050746000040c054025019080042c42d003001950b62a00b500c40444201d0078240b002074031088014611002006c0d54001898900d20715070401294404c1a031804c0c4441d01004204815a07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 369851672 1250 369850422 369850441
    0x61905220b090916080c0310050c04030606030804050406090203060a09050c1e0a111b04020f040302040504050a020103050a18080f04030c090501061b080702010806030c0d03030f0507080408030a05 86
    0x80d0720310710020306014568600068815950f4140700301e41215200c04440000c1e0311240407a0444464030001c014001d030b54025284c110181c24013400200440500b00310000004200303109000003144101c0e80319444038500000c0108459540d401103480a0040041242584e41c517a10362013179401030003000445407182001442c2601031780d02e904da141280701360584100c025420240018020682c1c0340420100c503400d00035100e080b4409104038000b2403d84030107007490aa0094001030911492050500c0c2c4d8940010341600c60540d41680d154100414130019543c3c0f40c000d559006a91950500c402e02c4000040080010070b0b1401409130a404200140070740c00d018104c600a580100783d00140684032003807840100001c0c0715050204e8400300240b000c0b9444e08440030b0000742c0049034641081c1d000d0700195400071001704940d50501580b4030241480c0da4441d000c1655a0203550b000450350941c0020404842c40a015202408040740403c80003d440d00100c90b8070135501d1401280030344810004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 369852922 1250 369851672 369851681
    0x30c090501300312110c071a03040816061a01021015031401020d02040303110f07060801140409060c050414090907050d0f1a04061505030607030c020307020d03030506190522 76
    0x1303c492090824003181d609000385d5000d41000e1041300117940c0c18541c0d420355400c0e10f240d01c1984040380c0405100080124010308013914428200c60101d542c560104d6540101300c540e0800c50480b2070048000002440d64108890402c80c946424100310b03102c0c29011811440715144001807000701c0d1107800d080c2890007034040d6020050089000e6494036103c0c074003d4000f9444040d0241180b24003500c0342040000054040c0c11070301341c0d0f1a1b0103036903400e1250702c0a82c40c21f00c1004a400ca61150001c00010300244200d20b00d01c0c18580d9030700d448500b404000314800d08101d076014411307a1010240642100e000c0b0700003040300c50440300440b201d01c052600000841105038064490b0910708401620800ea02c1c888500c00c51103900c0402c8003c00c0e444128120040314041c883d0954400d4001600b807030b0199018164000796030044906040c010ba00044211014900c203c0c0081d45407018031280c1c0c1840c41c1c0c074246520040204c00c6031582403c010544c1940c0c4144141d45105c40c1004000602107250300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 369854172 1250 369852922 369852947
    0x60e040e0c12070e1f0501110c210d0201110d0507480c0512030c16150206010308070213060510080f070219020603040615030c0905013003 61
    0x55140200b000500a468088611413800320020200000e00d81072040411408a0340c82000c004030300f603003807000440d4000b482d91044407461103000560000c80da1800c15255281c1070b4000408030401c480c031103050402105003108401d5a0600b140f1f804040043d10595822480070000010155140d40089451800c5486d01700569100300d040005120400c2821b80d25145650491103000c6034180c041103010424803a0281907003604260620a925120f0700ca0421040700c0800c5905101900356540e0524000d040313505604050304004001d001200700c0c4030030100b183c034000342c071045d0b2440e1509005440741c03400080c8100c10301c2c0950700da0700c900ba0788030901074034003c0c2c03400244400312440074001d907000365070b003500011400d070000340c19910010342145c1e001c008218888845565600740883d82e000a0000c44406840f1005922000341c01104272008601440f4400e031032925140500e8125003060304144c0b01c5009082c403c042c2c5558501d003500b0a24449000d10345011006d0404440c1c40c45a01e1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 369855422 1250 369854172 369854179
    0x30d0506010507021206090d0801050f010807030e031b100e06310503070309050402040f060c15090b011701060501050702120c03010f0f06080a0f031101090203030412120207060e040e0c 81
    0x83c030301c0211000000e801f4403444507442107903030540c541d4609940d0321009100f915402149003035440001e511034042c09801c010303981070204d400c419010719181503420a04a1582c5d895148100d80302880041040c1c10002504100401034051320310001510703160018a181d4110315003110b082044224a80d08002a0900c00c410840300e000615141c0d86903841001c00b50000b404892020031140383c03130700c215021a01205440f80205140600a58034020140010345130300358100543c035910143c50249a41592103645040c1240d814402450280902a6a144107581c074102c42444181d0b000811500d6441d01290900341e50f41c109215589009e401405603030701035092a030309000b03014040e0495110014518414840d550722803e80d60b545038020000174000500d03440010300843d0140d0444101e854400e0000700c0d0030001d9402281c995800f641c4505480d22003103210354240002550902c1540960b8030243c50030300d00d490030080032440d2503440300d8851a5109030121390f60300100072a07083c102015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 369856672 1250 369855422 369855439
    0x1080711030706052401080106032c0309100201020c060105060c0a150b030d0503040b01061404151806030b0901030303021c0510291c06050405090f0717030d050601050702 75
    0xd00d45403000d8407058403520840d4558417071641025022100030b02c5150010395420143d6840c0020880181c0b61807000c2e90700e41000350284901c0114a013454003c400200c4000315907c1c00720360300344605500c8000314070301164810702c6070f82c0e031207500400c00c1411074104656890b110001092054244910410018500102c511003008205101d800c20035582c0c9086080e580c51242c2428180c600d03100840d0018140c1c40040018058a4043c000000c2841e43d100c40d21810181c41d40601c1c4200d600e80c1244002041c2c500c00380b242030304001c161a1000c0d04da280b5083c003013131480002140042d1f030180001414140c003c40c0c045c2104240c20484a0b1480f030400d000d210f2420701c80818035a400303042c0602008107401c3d070910289604011300c41031140340030203a210b28001c2c00c1012801800e0082c2e0310205401e440315030015607591980221800351610501504902039185100e524100f480c0c3d00c400c1845030f58080c4412158008000d691002e0198000803d0305e9583c000101c60038403070604000c2d8080703001d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 369857922 1250 369856672 369856687
    0x53c01050c1c020607030e150702070e0403020307060b04090506040b04050f191a0601091401090b0a080901050a0c05070206070611030c190e06070303020c073b06010e0108071103 78
    0x56000c160011140d0740c003075500c9905e40a0b011820394005803c01d9002e6482040114905025401c42d5540102544140c400460702e40d968030295000c140d806070016400484da02c41800003500c6059403183d030803282080503029a80c2d0300ba840d450001c00c0600740f00380040004050200c28021000f06649900075202024003007014070203203643c0d110085e604060ba113211b107645195503651141c018003050311101c1e80c2d00d1a20b11800d0400100803000c40c100031202c54001001e50108014040700c2806803500025480c06203074007400c4403402004052020304000310300c1501c41d081002c84450703d406a5010342e4a94044c14540c0141408020403811598004104504810304901030b218180c4c03018003983c19100c1c05003007111a01c9150101c180e218404000500000e40030780e0080918ac0300c00000e8a030320f00e1791801072001c4d40445480100e05011044407502010000001c00c81030100c8450411070076080c490002440025081012414000c40f2030105003124003c07581c00646900c46803c499903001c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 369859172 1250 369857922 369857953
    0x3030e031605011b1709010905010617010f0504080306060702040e0a0303090219050a0b030a0b0a080d03060f1412030d02070807020109080c220b0a03050304053c01050c 74
    0x41c400000c0c0c400e0351801c203030000030407611302d064610154035640309924010904810901694040c06456566596808080000c0e1013801040c004129264010000360340300c807009800c1d00c40a201400c5c00302e1914003000b0008880744103407604180c090f2251610742036144045001010212041c039030510501180000b01541504144030161003556100782d80488a1f04000200c24603000d0154170815102040c083d1818241c0070f140d01c80c500410200741d0041c49804a0541d03841358020207a581c01c04801059610341500856008041d00c41c850201e1503e044000080303511141d405034400c03036003a5444112427004206a517494200d03031404543d17805061030f181d11180c0c4103403070490100f048003030700140490010558080855000d855072900401092851010b45080440c40307811607074030501000d480d1102400000a18403d8000b56034030703810b05003042240e105a00806000d001200d18600c104049400d0701e00d1490f05807030103614103541420041c0c07080d00030880304e42028420001003115011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 369860422 1250 369859172 369859207
    0x2003091009200a0303021513062315010c0807050703080a030203010801050609010e04030c29010806060303030c0d0e0c060d0207030f110c010e06040e09070f0603141303030e03 77
    0x341000012122880c20405001c281503d030321020b000740c4c21a01e00c134145070f80803501c00c50317000c1d501d49070100350301940f90f86d803808454200c030024440752a0160b44101e02c40b4a001c0c4e198003e403c2c00c1d20308038400850b100003040055200e60082c840c1d8408940142003240801c0440d010b10b901100058881e1402d41006000350400d02c120181507082c100401d6aa051044850341a1079104031401368650300c54405640ca070703100d07410442e204c20140c6581000303da208107401c2c4910704100c030141e4255140001d80c034604040940018449e400070000d1140c3d08150b9411a84600c08008000c20348180120311f060601415504003a00311000003401141c501c032030b0340100103544c401d0321039450007007501e40c04540201c0307000b454046d107921040c004038a640c0503588003007690078010029460541c4070031070010583d8098401d10025440318405018105030006444041c00c220315081003108a07181c2440c40501d4080d1450440c001c07842d034004203051094004a0080b01d014044960315007410a402d030114 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 369861672 1250 369860422 369860453
    0x110c01180e090d17010b0a050c070e1807050906060919051c0204050703060506091201091b0812090d0602030a1508070503010c110307080a1b030804152003091009 71
    0x200c3c031110398411340e00d00307614a40c1660032071078126051208550301035410782e110b203c0c400d40c644640710300000c9000b205030343c01e4818019a101c0c2c1034114400d04849180c2641500801e2207905c0003000c204191312040160340b20351004540c4024804a00f81c80c0752055502d0343c0065400100c0b8548520048403001c4030403080034801d6604020316962030700c0c01c6040310441c0c0290341c0c1c406810400e8801030b01d480003990420340e403040c00024040009648200003858072103012060420b0544041103c03100520140880703449820394149407000c07400000f0b2544459800041410ba80800841c031041c0d1180d00101c0381444061801380d03140d0325803460561700d012901c9224402c0d824580b9000000d4826003407111075464210045088c41040e0f0360b61030458004080312820044a08003421030300301c50803204000140030b0f40720002c190804d400c00903180411028903000c59801c068108441c0c2030100d1a40241d01e52040c2d0060b200d8a4a00e401da060224250342561030070b007098100400d0241c41e10804000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 369862922 1250 369861672 369861677
    0x61303080306010801080d140a02150f0114060406050a03020d090506040606090e0f0c1e0a0306090210050a0519180b090f18070305041704060804050c01110c01180e090d 74
    0x2280e1341c1d06d203407580d503580390310085001512a4400c00d180000b0f55028149004943c0151042041c03180420800c0400c12100072000c0d2440c80e00410a4079000a282440d443c0c0650740c0d185000c2c10a074014200d40300e00f00c40101050350000301c00d800c0d07541651059900c164044140e810703505150405c5000f424203802440145881c150041441050006540014000b110003402c040e4160008000c680b0807689603039100752440301d81543c40d035500c20380b203040a9072085000041c1c80c1018010720505091030029941400801c100340300342c2c00c1d0024145c9803540c60201d1084194021800102c0e602d1085030032001201049200208000b400a0b000c2d0599200580341101d040205408100c4440c1c0d01c07003400240e045da2000494549031294001c1175002d4010000050500d1074030801c080c4c1c0b90f000780d201c000013584d110305201c01c0010a00c40110008005d181049100280c1e1400c00c0d01c5002c204407403814000384440d00c144207a4240c441c20002d0071020012069441c00341691a110391030051f14000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 369864172 1250 369862922 369862937
    0x3050d060503070602070611030405030a14010c02030702011713121106060f1f02070f09020406030513150207150501030b070f0807090905090c1e0f0307050f010e06130308030601 78
    0xc4a0400045403011181194010705909117087c20035075040c450211030aa1034082040b011039a40c03000c114600c4030f140309401e84100e101d980d42d46c07582103980f10072049086410030801d07800580e0f0302c054002e8a000d0320500040040c0c1301c410f005003680e00444801404034038102d030015a0990005034034004078420790141c400316500d0800b0440c8600f000e40003554490300c0043c41007034000440100c04222222401150407558942c0080c12076030b90290302c61604580c00142c180f00c105c0e45401201d40000c0b20040d56140d00e001036880407511074945103812071055022520400307000c5101c0350003c40400c210300401295071242411100320408a508001103684001282203561003822568810320880c0c0d11940f0b050304103031035200074100c00740c103690f85c0f40b01e03019412070150b0b11030f6100c4150540c5221180500c00e800c000b4021401a41400107101c3d4002180070491911494941c61440300c007464282202545000001d1050050411400c0f40035604d10000c02004180401140100002d0700d5040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 369865422 1250 369864172 369864179
    0x40809030d210c0c0503030a050a0b04020307020a0611040504060e010609080307080409050c0c010f050603070501050405060414180a0b03060f1e25081803031e04061803050d06 77
    0x181c21548100b08107449000044601c0340c2c404103070303202e94010462894000d0000c4403588445285800c252181280642c3d1034080c0100440240302d40b00d50050250b6055080d8600789902a4441003180720147c0700d00e07107841481147c161710008840c05450024402c1048507294000c803580007000740500400300786031082c04280d4140000c1940c429607802104245041e041c115404040c2601801c203018000051180300d22025081c007800c0403030382030702800260501d00300d03041501d003030601d501545c18000100410300c03403500d6030741c100c4095541e02080d4134002d140f41e00100c1c03403210903000440c5882d2030760740902240600d00d8124601100084040b0b0b4500d49541e14075005140341902d03044040405850003c0b401c031002e40c1ca8560009a152207180529640d8480010414100c240307500021507540422081d4841160750070b030096182c0d00150300b10b18095244540e07260981c80d0484e180d043e02c01c001000c00403150012079171600d0034070316485511950300d005482a082440c058162504001022 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 369866672 1250 369865422 369865427
    0xb0429090a18020712020a03021e0d03050612030c0610050108010b0403020409050c060c0f070b040b040509041511030403030b1e060702010c02090103030216060810180b09040809030d 80
    0x860040c8401004020703807616040081d010725800000701001c40e9028440d581c00305201e00460f5030b2181594015000010b01c81c80c0c02400c102c100680c050000c031101092a6103040009484031942501d401d000540b5103403480041d0310080ca2003403a004911000500320b100c6000460020700a586c1010501c40e0aa140e00056903000f8090042d0170110005001c1040949000e0704580420350184090b1210205041c2c0854101e5118a000708802c1d0300540c1d403140c0603001045440c000301041540241410700b00202c42540d07100d10700c602407140b551000402c01340418110100d11884002004010a0071081d01051003900119020f501007032030254500b00605000c1408500c40c1000003000961402c01c10400c859034004003c20303410081c03c400b0150040c1c80d00f18059029600a800900407041400400c017101007181d00120100703d91001489540e40d219200c1406803452403811200300c004501d294001809402c0c821540440170805200c107005041c002002c1c400300607070503590340c800850b10a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 369867922 1250 369866672 369866677
    0xa02030c07121b080c070806090c24120a0605100c08030a09020a03050309270f04032106031e030503130c030b010e070f030603110d0c0b0429 62
    0x100c030152041000100160180e0b04044541289080a0025444452940c16420506a821141503c001501000184040114000a102150080005240500c60151228801040300380150f42c1021688062804500b440300b00c4607440c42150340314485a230196100c0401030f1006000070f4501180031401c0d04200c02640c00984c100e80710344e0902075803566801c4d460fa000500a0a000750394040712001030f55101428001035019000440c0c441e8002d0080040071600c0c80d122800100e400009507040d1590200e040780d012a10314040d00055841d41800d5500800241d2065002c00c581190303034070780309e440b81d0051080e20300604501c0c084071142160158900c0388014040d02048007031000890070522813205d41c54551107400304042d140c4da241d8400780399038001c1c4c00c0302c0604440c1400300492180d002d5011200c25005203401c0c0b00340c03071560301c441501c2402045814041d100d2690500244003152140b0401000181e00c901c3d652951401c4c101001c0200d6a820030402c6441801ca9038402c0c001400e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 369869172 1250 369867922 369867931
    0x12020c0f090721150f081e100c020a0b130c0e0c0405120a02040e0709180803011203200f070902120117011e06050306100602120a020109051606080a0203 67
    0x203803803c803180e8810035103596815001e0058561a100d84490548141c88802100180b00120000050a043c1885a4182611030000700e9aa00c0c41c0c0c0040c5140d0f030340004502d00c6040d00e40500062200002c1c00407800c0074003284024101c60303108401c5c03021071584c1500048040f800b440f2440d0350a9202c0d094403540ca4825161b4030000ea5061006001c1490b15844540380480307100b0807a410184142c2c041000e03a22040c16820b40364001000402c2a240c1a00420803a00c850540c5510072503810394440d42da0740418080c0d503800c8889504020f0825010f407c6025003044142044031080040040c010703aa064018002c107014000c0712000a2130030464001d44608000c203d1003022583e0810491040746c043d076040761340d2103641760304500c2031502c0d01c0b0340d13a01d51401c083c400120f20303a8286810301d482d004000c0c0500c000b04489480410100790b0201300c0081240500008580d5085500b45c106e001d8008614083d1003070290b420408000b444079020b04040360510b85031502c45681e4079442c03a04900003182c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 369870422 1250 369869172 369869177
    0x30d050406050f12130209070e031e0c100e010f031808250b06030f070f051c080c0102090f12120906090915030607020a03080f040309120302100b1c080a03060312020c0f0907 76
    0x80415002c03400018840c80bd502034a010ac50102d802d10b0001410402000c0054002c10181030381d01406591208102c0384141540c10184008450500d00d04c002c8100c00c0d40181440f640803030300c010f000c007481c00031285400c10340b24240a00c800740e09100c00121000d8030214807a01c98032900b0b40c031820000c58580300700c4008070441603032580b416060080f1100195000c9800c0207480c010540014409405040c400030702000050721244860144003031103120106581c0b103260172141400d0784d01000244505100c0c051002561280224004601c0c2405030006d515881142402046200c00880852044401c0d00310125491511140c9042c4c0e100d441e400d002a0014a5080000c2d1051401c0000c0d66040340c86490b1401f41281d43c2c80d1310075211070185408a00507040182017100b0940741d4014030482ca0300840341e066119a54890312001e00c048400700500301030b0045075514800e0b00a512181c000d41d044000c0300007200c4420320094807141d800c0b00b100d1003810400408909400c0503808280300e02c007070f034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 369871672 1250 369870422 369870433
    0x6010f0506070f02120a0b0106020d03111e09060d0209040612021804050c040501320a06030b030307060c08091c05030c16081306080105030d050406050f12130209070e03 74
    0xba100c031051101c2030141130341c0110103481440140042044401c200da406035246180039414050004d042902c191840c40400d07040c052514070a400700412601c10042154944040d05404030006d119401424926580914040360b0104804030b150010000c2d040102d80401c5a90740b03401c0410080d03041c0701c0010b90070400c014080d0a10b0318900c4402500075002d43c08a840120801c0c1c0040c06a0740240c02500d040c2c141e03e08060440c1015005050440041070300ca6500800c0e4240821035048080c402e000406845038440013042d00c06104550a51390000400c2c8000703601000040d020042c1602c00300d280c0c1c80f0b10124803800109424030800082c41c0c66480514544a0f241ca01c0521f4110f4100000051030b582040f8001038956001004410141381440c021203207844000307000408141d0000340603810051188101c00e500104890a40f159410555210746aa19908a260280142c405030030b5940c04e050081c0d075014514001d90840c0b003110301c3d00d00c81d52200800c854003015030190a4069015 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 369872922 1250 369871672 369871687
    0x220c140c0a0f08041a07050c01021b130908190f080606070308061c0b0a1d0a080a050417100605300a06140103020a061103190c050a1406010f0506 64
    0x1c0c40542d645507000ea100281003075100c0e01d41d13050007031002c405c9219901c00000c0d50000c1100502400c1c030b108009001600c003a0140500d6800c0103103c200360140300c0d41a100d0702c81c0c040103480d80503075180c90300018116211608185220f0342c425042c004c41021440720743c00326024a11881c0e101c8c1c070a400c050a12800c280c40303580d081d1400e2402620250b07000c81150140041c05520300828902d9038000d0814a2442c14810008030465030802d020007488903100303401c80e028520001d401d00b0b0155208442d02d984180da00c004440502480e0003882105213032110484500c100000c001c40000861f440030020150741c1e0040003154060041c00d1a0100740a0507a2000141c6202118000b8254078050360404000d03950b81c0d508440c00c004000b28403000c064010700c19801c1140c0360b00301902890070602c2c50040035000702c1e0758901030592311450710040e02c103829036594420300d4081c02c0350342e1260842d40717491071515042c0c030716407620841309546210751000003510691003030f130305000c82714060910740c581000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 369874172 1250 369872922 369872933
    0xb011e020c0114041d0a2f07020a0515030405071409061323180a0515060102160801050f10060507030809010b0607050d02120702100e220c140c0a 64
    0x228602030010141c007880b0011300203950010800640d90f01c00c200c05640c1c50443d000321b0803280c0c0114100480c102a01d10b280144030301d8860001c403010406107242d100c0070340b840040d01c08501900229004090003003d080051842d501850190b8030400070b441c01152202e801505040000c0360f82588030070303c08080703040d9041c292007200d9004485840842c49100007084840c8180710700001c80940c2070000c04201f1502c94000b9101454450340340600704075441c42d2240c56407542c0d83c049014151b01b0442c08105140e008001c180c2410b4140d40d0b8585100780c0c2c3d02846030080c5400c0340d0b5000000145800240105c843c038818505844203070307c8186c1801e0054030f040344e429000503c40c500542d41c820724440765988001c0985520380c45500100b1000701c0241c0300a080c40400d00040110980034811807005954802401444071070518204080c124194009060242000408801241421000d040c40c0d500c1d0781002e442008540c4490700385051008107240303d4450074001c058160420f01d043c400150 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 369875422 1250 369874172 369874187
    0x90106050d060915030302160b040303080c0c19060e01200c030412060b0a14060d0207050c120706020f160902090607050106080307171204030e13060305010b011e020c01 74
    0xd003020300040380e585035040e030021958152000c41006488803000c0040507810005030b00c0e2043c021142c40411031504100d10014000cad03000003024401c0000000301400030b070341c080d02c0c40c3c020079800700c407032141c1c60a2081000d001c10303400035501c09003480820108110305025425040c2e88a8426180407009044040c086400055009205001c200000070703100740c83d544003107900350084c003000405035112010004201c6065000d0300606003040c0d0f05a10668800c2c00382d945070807507000c015a403808585405030a00b24241c4215a20002c503004141c5200d200003401c030191174894084604d42114540059a03c001440100045035021602800207810b9600646841c0314040c02007428281c40c2c0d50342509640447e040210b59600128440090000b4a02c507030b100c44c41c400011078904100007141400d4800b00078000b80500c50007003552035480d2603102c010020004101c00c200310581c1c803880c00038060602804407600103200103c49200b145a0b2100754280068590001c00c64811450019960103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 369876672 1250 369875422 369875437
    0xb0108010e0703141905010e10092003040b09160509060607050f03071202120a021005040203190f1511180607080409020a030501080723041113090e0c09010605 70
    0x1d0b4451420991155a411909000c5c3d0910403d0002d202d450740e100c42c007102c1050303001081900c039120a01c0541e004030079043e07003540d043e0b02c000301d4010303c181c0c5120403042c01c05450140c120000001c00043c8880c81500301e0150041e803080e00e18290380800006020f150a00449502c200a200890403030715010009103d000c1c464415200344000c40c00e510303406e642000c40291510341d12500320715101541442a004894140d8403400d00705100507500950b510255500d07503103101d075117002003810741d83d04000c07080f19007148001405031404945005913091158100c100d40214885482c3c0f2a030380303400d02403502c500340e144020608040c0b0031161121010103c4011300e810440030008103001c16644401040508500c41016a4903039038900004e040700c4059008c60007a40100c1d00c18001e40c8008079071020400c135400341d0900b20300c002c417000400a00c204130030540035840006001c0d412080c0020502c040360300b11002004002081c00b02d66482c3d03079280c0c13151035002802a005002607409200641401c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 369877922 1250 369876672 369876677
    0x40b09090a0f0c0c0c06020604080901050a020c0415030b0c0a140d0204050607143a050f040303090612050f01120807020d0506150d081602120a0c05130b0108010e07 72
    0xc40348006548003c44070100011400a80041e50580034002e0164450300200000c0c0700402d0f892819881e03c1010b40200d107505410400006036007480c1501c01c00460b21002e800030400c001c00c001ea00f1815009040a20044406486000c0082c1c0305010704010789240f02613588a001c918818144800c516900840c02c0006640c0d003071001283c02d0302c0e64000f800b041072040394440840c0e520381e05480d15100c00c80d4a10800d26804580c1d181c2c24000e0b54084810a01108003501018451940e0a891501906441401402010900000785070340445e82000f110f0540c0c4802e2a846100100321f41a91002c5031101c1c00400c2041c010040c241c441175001c05400d004621081c10003009900190300045d40881c2030b0f400d6403101007484920269a14003801340315040b0b421011103802076a900c8490f000e0300514107c0030944041041c2503443d112080340d2030300380607000d4485045a5180541803014540100303070007004019202170014546100b9001c1ca0401619110341607032814602441031038001300754408 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 369879172 1250 369877922 369877931
    0x51c0218040908040e0a061a07051209030f0f0d140a051606240312020a0c090510050306010f08120405011e1101020408031809040308010e1f0608100b040b09090a 71
    0x1001450f07408617a001e1400886c000c281c561401c07403592001a4001240440403d0401c0703480d000a5000501500d4030080400154a510303200c0000b82c00c11400150354005405184000f083c050004195402e801040e074641c401000c1c0e18901580240c040d80c8800e2020840800c41c0b1110503080082c60010184500d102040600301c0952040c00025040014201445a014180104408049042c01801191000784200941900c440e1000e1030030388210392086603a80d0115015003100d0480b0400f41a02604980a030350b51004a403200385103d128803001d0f03000301407800d159000e03d035044800700c03001659040152004a00e81d14000f0405900f82020b00003801d03c903040382d201c2800640008c1c1140c0f0040d603107a1015000c14115080b01e002480c0c03140f0441c1c010800025000441141500d40300c0c4000c03030103642c0341902c900b00140d80002c1000f90811110703001480e00e80c0084924030688a281001c03000e50f03550380d004035150103a4000c500300101c05020114007810b16031a0399902403818180402c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 369880422 1250 369879172 369879179
    0x307031812080d0e03090f131805060f060f010c1e0615030302160f060813020307030b090f0105010b09060a05090402030a02090909030a0806041a040507051c021804090804 75
    0xe0045110031000c9803100e80200324060318083c0b51040600c6180d8083c051440d256400340001c080d03c0449141c0c52140940300121a00301c00244c0c040c00c210b45038644912050f22240c14440d90310700d800c82c0c911209a1441703000070807900b040c02c094408844103844070707800200a86e54050703200d40b08440c10519021070001210208406002c0d40c503102c0c40a4198032000e03410341c05d000b42090128001161080480034003000411504a1884202c40301813414040c00e44590800c00c210100c51207002c0d50501c141c0740f0100500100c440d80e280690030403401c0712000440485110300740c0e4002d20800103846410f12441d1a5400c1150090403410400d00d4820f18004c241400503040742c000b62034a281032a0b0201d10202503051288803030b500004032100441c1490306640000b854050020406809161150071500c82070503030300121031907902d00500903c12480d1040004241e03410105090071140c8900c0d090b00c02c01c2c3c10034422215102880507440380e0f1015141e061101406c0504001c45041e0340422002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 369881672 1250 369880422 369880439
    0x303080606071b03060c030605042901021f1a030607020a12020309030f060a050916091a060304060c0318020a050909030c060109050601020d03060815090f12030919030203070318 78
    0x59004c2d602c00c0304002080c26120100404496150300400c0c080e5162a410840745048202c03000c2e01c416a4540b0310000100c030a0040782401e6030041e04074520341d0b0540c9050a41c0c850741c0c028a4011b9074004610b02d10002c94020195501000e41d4400007513003103071440d41c010a00314811403040003540d00480c1e00d00520355001c02c3c5081c0350f4114036a501d80012041c00f59144c1c0c0c03409025040300b1108018140030780d010b05040d405080d2403090842d00340c0c0d02d000c460041e0802d00e50f60400c2c428020240e0ba00d038030f02410158007400080c0c000000091034081c5141001c000b015180c00c0168020b421842c0716800d1405006203540c01a01500c49440309200f80d140713503c0d041003851702800d40c0c00f0002c960343c01c0580c00a45464800d002c00c005050400600703102d5001d0014290042d01c0c440c19024455845004016007002003031003851113180682400140c3c4607a031900254081d818060440740c10340c2c20581e8040800030b0f001401401a00200019008284102e500404054030240301100c3c1c0c95407444034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 369882922 1250 369881672 369881723
    0xe010204170109051c05030f0a0908070b04030906031b0305090a060606020703050705060421020103090210230c060105060a020f06010303080702100b030c010f050409180209010609030308060607 85
    0x20040b41c1d168400001040424010a40c9040c462401281c4440c0720520140042c000208019209061040011039407095034101052146d000f00e00940c1e80c09090511724544903040314154041142220000741c2d41d80309200d0002600c4900e00710101544070701c0d03001c0b4050200034051802a01c40d2451000101d1020301c180c40060803242c0051003c9881e40c03070001c0c18044280d001c1031180000340801c00038042303900c05503011210024080701c82081140b0041c0c0052600da0006500030501c2c03500e40401c103400c9500c11052070340c1b00171440c4a822210604107050b10a43c2c9042d10182c00c02001081181060006441e8108003401560701c8400a140d4051810800364815000a100c0d2002d1102c02a010b000d1644540e010007414012504101c002c42d58588522550604100c4aa80f003411418821016035024000451007802441a40b114000c245d444540c811392260b4081c0c4000580940500414800c50740d042c2c82d2054580c0e035000820015400201041c2c4440011031300b12030400c40398000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 369884172 1250 369882922 369882959
    0xf060902120115120e0a0b040303020c10020702060412020d172709040215041d0103170309071e05060c0d020d0903020f150903060a1e060501050d0e010204 68
    0x40058031200140e014840650703041c0d10640c1010800c41e5080c00440d0301c820b280454260a503004201900c080c0c0c5000e16000b48a0b101410500040c0c0910080540c0340e001499030402c51403c0b2401c0000c10500341080380701d03089000b54000420001005502c1481000080450000b0000203a101c2680c03900a1400d0003440030715103000300099922440840894503114416614240d40f40324105540461107210021784040d100b0282440c8054492051504407005000b80000d01d01c161070700c008240303071503480a005c1180c1c0d501528015a0302c03c44628140c0e80f09440d19801001603500d01001c000c206880106408c0d400c4002e1940806c56450304c400601442401300014145558a0349000341070a212446d15010070103002c6003000542c0d140c202d034828a42d0103c038502007840001004014610455500c96014003c5804125038100c442d07100d9803e41001100300300440d1400912002120325174016140860310902810702030844c181c0c00300c0410800d00f0001850507031a10341030407201550341c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 369885422 1250 369884172 369884189
    0x923100306030b010b070f06050a3b010903081305071706040c0f0b04090506030307060e06011a03070f05211504180f0b0702011b2609120702040f06 65
    0x81c1c0c200100902040b0640c01011180d11440c2099140e5445a56048003c0070291030350703846001203554482940d01c40c1000c0503c01401c0c00b4410402c0394015102001d1209504401701c201000e46090030b0b060080c5140c0341d90523174403851540d540a03441c1c0b4885140c500e041c0d421b803248074000f2903080c1d485003240809822020013044585494580540c01d5042604280031408a1041c100100480f40e000e450603644d040d0700100301540c4d441c2c0030078514041e118004d8030242c2401480d9055545c0030420340e051701c0301c05d6106081da080108030f0051a00c07094130085d0000380000d560311626882403001c2c0240c4554400c01c2d40d000700303014000c540241e60950300c440072441d0041c1c00d4011443e140c41051900c2110300c5031007070f440406840c7c440285100c82d80c05840341917507000040080f07100707520042c1c044808640a0080c003000c0180204840d00aa884025084003064603404400c03154008501c136920030801456001c50049a45807503400c21881240c000391100d15030b40410215000c0c040261040a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 369886672 1250 369885422 369885431
    0x61e0c0d02040905180a0305032a0a050a1205150d0f050609060a0b01170106050f0f1903050106032a051b0a11010c030e040b0a0b03040f0201030506010f09231003 71
    0x414032000351401880000b0305c00d9000c411a040082c0e044800d40380d04c1008403044241d050606038079039102d9001c20965101610000585042080e00a00500202040c4d5560580b14094000c2120201c072010f030358075480e02111004500541c50041e903e60b2081f0f1040b9000300c1407002c6945c0d107501c0d0000c00d07100200e16420003410010040054410b00760040024a4600c401c0034010060f207140c0701e1b06004c0c80e03041140000d0b40d40d41e04200102100d1281142001e400d68070f0700b54964603811007100b04522000a070514000007042c511030b004802c00038403140320805200510040f40c84058200002e00ba00f4004203002d10014283c01c00052910100040c002e018180320520780800025002c20a00e41804881c02c4d207400842e910085580889000760f8001620750b00210014464141c0c5620042c22502c00000300010030440d502075200c0f0600c02e03203041c007564032000015078444402c2d104920008822076401c2004440d14814003c002074842140d44074042c4003c0400d210300c020090040220f51103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 369887922 1250 369886672 369886681
    0x1101050f061212160203120c030310090b0108151c03080a052a09010e09070c02041d0a0b041b0f180c050901030e0705041a0909061e0c0d02040905 64
    0x2c01c68010100d1018000b5204a010300da85140145100d600005415440000454504000201045490781e500f90f4507a0300c14034200c1c0d56940301f129400c0b04a603034180000b4580e5018059035038420816156100c0303940e54810b201c0800c2c4141d030b410681c020580c00300b10b050042c0c0c0c00390034601d89029540f014450b2901246002c01d0b9440605041c2c0364241880307003510002089480750003010a11500180d0791115400122080c0214070021640851000140012107810401c903105051003901d080c0090340c200302d0b5007121040000801c091a41100d600c00c0005125440241d50040c8220b881c0c0002c8208160000303284005a04050481203488106114113004000620082c0480d03500034058080d8a40d4000c020703005111180c1c0c141030311156140011202403152401420b005402008041910071503024400b1000362024080c1c3d00c03640114040f40000f25415120344078110b2000080c9901c00e1005401d40002891b20035810420300900100403840d00040c4018588400080350b182070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 369889172 1250 369887922 369887929
    0x714160201030b030c0a0501080c0d1401090c0903031b06020706060303020c031515010309030e030f030d0c090e06190306090807060506010c0209010306020d02041d150d0c05101101050f06 82
    0x40f40c0034040d200e6880000750240b156a0240d401c0242c40080c039000d8296250007680032a94010380d1807007005c10741045207000c102e2803041c090904846141e213040c0820001c4001c20364600205000c0500040c024802440e442800d5961402c0044d1203014014a4520251201c03c211042c542080f00140c0019410229030300d02003140b2038080c05003c0c04130b481824103c0c401c0345400440400c0605060719000b001c41414007564401803074000140644514404092156440790b00006400580529041c20440741602c909402c209582c1002c4040c0701944904003004005090000c280400311080d003000310018030300c3c1c050b01034602e00c200f5069403180a00d103048010f40700c00904060410011906800250740d482c600b2604407604984010390384c00700116207030081d02c00c45d00103007944c1c241558041c0011007100c4840303100b0070380b110042140120481c100880e44802c5007000d015050300a00a00544c43c0044c4603505030012820000d4590322018105070130b6901c12261101e9903036286041140c10304 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 369890422 1250 369889172 369889181
    0x20306090309041b020a02090a0906051302040606020f192d0c060c080a03050a0b030d0203030108010e2b0504030f0614010509100e041a01080f0c03030f090405071416020103 76
    0x40c040003134049a00c003c038000e54900c1280b030080d04c01d00700200481c200b0201688585030b105d070004801d1105291881045200040e2048100d02031450103000141c1140f0214040c3c00c0000c007030015041c00d410f031551800c0ca8404010301a5200b98a0300d45d41c40e42c10b40e003200da80d501c14038182d81a0700100c1d01d905210311803645a0b4096004c1c011850400c00000c0c00f00022551500094280082c45403101071400300284504116590584118100c0c1c01c8030680000c05581203641c0c5000034040c01440554140d220198403c280d00f41c07806a02802a40d4101c203101035107802d040d4604203091a41c0c0e40c40d1581001d03103214044d40d4040d0b071141e120340001c1d6015140340c09442c064516494a0400c40c0c1c2c40550040b140c800c0300101040c2e1800300301000014803500e00e456010f0b100108240d61500c0c400c903150203544400301c40e02c0c41043da5503003c078100070090301d19800300c2c218064140740c401010702020301001031820f8204400a07180160380302880d0041c00c0d04402d0b407004500e008107544005000c95 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 369891672 1250 369890422 369890441
    0x110705040c081801140a090b1312050703051614011401030b151c080301051c03020715020a060603060c092106020a12090b04021c050606060c030702030609030904 71
    0x3203081c421036410050300000d0480d000300c1e8100c0030802c041000700407640100790f41d034034076075161740540700307020660396a90002c01d40903000c0d5140304407544880c45000000c0d000d10400a2001c0d00d110003502d1594011030180c9030b0b40c2d00900b0644c1c81d100e04200d0710500700455900c100c074131030740b030012010702c050b001d200c0c91020701c001c0000f06025505503106c010301004000d04501540c2c1d482c0ba801c0700203454515401c103600144c00c11101c8001d14518002d01950424000d1038003c040d1260000b00c4007000e0001c1d0168190541c02401405050a8034003909540e8142c00d42d0130b621440d405440000c007070340310300401035001e04000107025940304c50003001e2800b650f01c0000201c04034403012541e1800901c0a51815620020041e982ca0403038505840070000400d50f04070700c500c0d140e185c0c0700780b02409481c5480395200b01c5150b10b084190742c49003800741c1c00c10500a8030700d502001c000340d000d003481c100801440c09034908981c104407070350740061b1510b2421100c00c0c0041d080401e1640e010306007801100c1c00c0c0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 369892922 1250 369891672 369891679
    0xc030309151e02010605030a140f0303070e01030209010e0d030206070201051005130c1701030818090c07021203090303070804080d0306060c1113060311030609010203011a031009020307110705 84
    0x81c06048014101585500c40300d2a1041c03420348030070258000d51088000780300140c16610015482e0409144801c80717501c01c65098094004850120704010046a102e5203458945542d5031550b600118002d401c200e00e40b42c103011603040c9205070f60b95030001460314144242c2c020803680c94040030003030030b4503405001401e08100d2480c0511559544403041c5004040613000014440720090040340d400c4c05015051506403401c0b07001005020150000701682d8070b49a62b03164610041318280046001d08036005000d9080500c004001407406901e03041c0c40a400b0001c403800d00d6030010019085520080048031034a000050030040c00c0301c18403503180703800d08038202000100c0c5081d00c0948840c42c0300301c000303050f010008070241c00e940c1e60343c4104242c1600048100f01e00c81d104e00d072401403000d00e4048103210703108150004203d14414002c60f03042c0d0b80c01120b119210000b540740549142c10213001c900400200f8240810020007520185110f4001036440c410504410b40da0903003003680c290001400b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 369894172 1250 369892922 369892949
    0x103050903040603051f12060501060c08070210021510140f03030a1101090606060306030521090d06020705030711090f091b040b030601032f030a031412040c030309 72
    0x2203001009440c2215610b00300072845a644160203400080041d600d45d2407000e14400101703001e81e420b2848000e50344100d81c1001326076201c0304203440c101c0706520010070710102040f8035001800d1004c2d2208000300603004841c03c0301e0301d14030640f4a201045070082021003002c0400c11451600340720b04494140d003034842214002002c03003c6500c0f842030707800c000240300d800583c008a4120950051130001e070070000c100151601e48100a001d09080d100c25201e510039030f02d80300300104508074400010884c200c500d030b140c07428420074403c0791484400c040c1d9131780f9070178003200c07004c90810320040c409940300704d441c018200007103400c02c014818050a0100070895080c100f0203074810000340b43c80014943c032a072311312151305000060007500c1d14064598241c00380c0000001046080e080c031a055083e6a14860440125807001c2c5100e20303410814203074541e101c5005e080219008005180c401165114a40d140566649501b03281c02d105840403035550508440070410305034802c40300d0f0040c0692004015 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 369895422 1250 369894172 369894181
    0x303020c0d210203102d0803091f0903060906050907240c0c031a1014060301090c050405090103050d0f05040e280e0115050102010b090f0c07020a0b1305010305 70
    0x800450075001c0d0180e481d07000000c1107524041c4040d103801003901e41c41e4900c80c01781c4c6c501600715000200c030300c000440b400c403600425880342c00f000b80c1c0d2a100d809030042244540544585035075480c0720800005120401320084045602401800181400f60708080b849050452030035180c081c60758001148103103d0400240803041c4594108194003591520807500d8800d42001c200c89191580000c1601d080010218000b82800e04d03281d2042201c4d1000606d0141e40790004028241850032090b401201000140040c407646d500212102040e440e000b82825154404034408240a0700256940d03070065040e030100b10b07403107030301c0e8085009503152690a0070703c4c2030324110340210058140504220f01c40700c1c2c0c0c01118503079003164041d28a003034424020380c00c542800071300070403010f0303903003600c01d12082d0700410f655005004031888410050000c13121030741c403039409a9502002504411007048204911000b60382ca00724001c020f800c000002d0395444290b401e003071b04034100035800207043c1801c1c0001c10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 369896672 1250 369895422 369895457
    0x100c03060b0a260c0412240504110111150a090804180f0b130507110102040609050111030309071214010501090b01031a15090105130f030209010803030f0a02070503160303020c0d 78
    0x580840d0420342001442c0021b516000c4c0c028070103100340c0a10504a41038034410b480c15900300754091800307198100101d0a03003070011903c4800c1da8184c910244d0004d491851a4175a444809500c101d820000041c40300b0290b4440072203a105501c0f8200e01901014100281c01c4c41e403240c400c01040000080085e07408480120b40031402180701422650350f10400504041d0281d002c14810041600003150b49a4a654015080c0e480ca40500f500068031200b4421100c500041124010380c641402005158078048074159283d0000208482244000c5c510100c407003024001e448c007030200c1480c003140820b0820001400c4074442201c0c080c1404120045105949403500303044900e545d4900540da0701d03400c100050311070b841f801e001c001c210002100b00003440c500c079210100580340f0845140809980e1560103039581d02040c0e942c10750289248010450043c03d960080000c3d92140302540d0425603001710b81c10425401101c15000320760001012840c0310400c0c0b204180c040d02a0428446603544400385 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 369897922 1250 369896672 369896677
    0x90f050d080a0c1a0a060905040506060d17030103080405012606130908030901050f0705070309062115061103070c050405090a0f050102070b010611100c03060b0a260c 73
    0x240c0701e81d00010318a5103061103526001d42c03860700070740c4440b80c1c01c120390441403054008940d00a035640c030b0054041515800c03405158050354010000300383c00d40f100000c10801d4103070301701c00325a00ca40ba441d01c102c1c0803100b8800384d13008600480080e034a41d4500300001d401c2414013009070050030a0040e060144004040c106500080f00b51001125a200c41100000510013803d002d044054040100b04034400150081032060042002104040d03c60b058240c42c00c1c09540381c000d000c240001400e20003a403184260304039106c4004400d8041080300f148000454000024180c0307000404203051060541025500b4410400e901c001d600d090590344880d0307054801402950700c180d8449005c074034014010025886501d03041b840001a010581c50181d000390300c000e50841b01c00da203001c000513916000d070000010940c41e041c0036201540c0c071107c0020040c80c85144000c1459a10b09021491f4465040580700d809000e072100c82181c82d45540c0601d60b210803c01c0140140c0000d400c010f00c60445506 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 369899172 1250 369897922 369897949
    0x31a1b07052505120a0501150e071d040f0506100f0917010f181a1b03040c17030d05100f03030f0c050a03090905150906120c09090d090f05 61
    0x1004500003035069002410710b18642d102d9540a118441c01c02c040c2a00890200c2010380b14100800c451402d9600001000500e0f100c5c42c0704d01004c07613002408450280e45c0c6100c50f01603c3c91101040000b030400034040752040343ca00e4074102d59a0080008c141060000c3c14044d1016091940080031030303500090820303050380103500f03145071210440307000c0070825041751064411764101844102040b8041a40541d6074a400fa905010320381851402017141104a80c0104100d20711410141580c040766189680301038801c481ca29600d640005140b150005820884407044025542e15541e80901d00241d0f0b4003d81b2100d13054800c8034041151401045d01e4004403039050620035021070f02007000f501c10440c10703000649107003d802041010103901901080580720075000800c1603444600d0001820000b00d403681d900117044801062081c50005c0300130358015076513070072104024500c60218158440c2911402c12661106003000740d07240e085442071018040e040c0c54040d2842c130700320001d600080c4010 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 369900422 1250 369899172 369899203
    0x50103090c0e0403020f10060803040918020d0b15040209030a12050c0601060c02040c030c0c11121f0e0604030f050f0d020a0f020f1204030605060406031a1b0705 71
    0x4800008020300740a2290080c003410040c1c2450b0300d41800c001c1c0d00d030b0301040c40c400014021a00a0440c1600034822082079030107000086007443e042c1410354000740518103001e0241808a00c1450040e601c0c07085c100140c03482105405041d040991502c9040c4104102c0c075440f0302d0044c07248450580740056140381d659006104407c50604501c029101ca205402c9200b40d03a0113088000b04609810a07445080507100b91000c12204c120404110125261442d505d00062400c00d008004a0180c071440501440700070951041010314060440c07410b00303502c44540034001d5040100d0018400c61142c9001100000040c00b60762a0031f95004200d0407611007480240000400c0c1ca082050f414825503003422141c1c1c0b07045541d403030050070240c0340910f01c203020f03401442030202c802c0c643c03075021502140580d01d045080e410281941e0b242c0003d403d00601031908542d4400d4004003143c44064a080100040103403510103042c1140049000d000c591000e41200c0705c100001d0002500000341c82c0340c00030016 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 369901672 1250 369900422 369900431
    0x51306050a090935040305061006030e1506060f07060504060e0c01120f0b04061d090106060f0c17031e0105061c0213050a09020d0608070f0312020106180504060b19050103 75
    0x1000750561309040e000110f100d80704c08a00030042010000e1640e000d81d20030101418604d035a00d40c00c40a40340c400303000a6041d003100d000448400401c6204a411101c01002e05040860209051095800a0f0300580304c0c5138a507014002071011910840c01030b170050402070200694042c00103820580da450800701c0da965100d0b42420340900c1c6510204d54014014401c0c480350760f4891544848842d880c03480f003d050f0407030f00450081d10051050300100c42c22515069080061400b05039400312040030300303640c0310600c3c01280c0320b0f0200c41c80003184a01210b02004199450920031000180d60580210703014020801007062080104252090440454000903030303500b0485101c180242e20360750043c0d40103072440b0b5020030310035402d8000e054000f80dd95000c2014030707a00c51500d0340d11481c1d80b04d1642c088882c204140003142182d003200c14450194000840d0a0380c0e9060070038408950003042c0e0740d1051303480062000b0400305000d030041c0140100e4801c0b00d58076809403010401c2000e4401c090515545 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 369902922 1250 369901672 369901733
    0x20105040e04140a08120907030c060c050a06060923040506040209090c1201020a0e0103090b010303111e0d090603090b01090507020c03100204030b0c0c03030c13051306050a0909 78
    0x1054501a221601036058852040a170329103101d45410000b00b1000408070040002e69000001903e201100d400020646000c2e00d84001502d1650900790700b52060301821400e00040740c3c490242c44000c0c10030800c0040e03412039454100d8a01da4a080c900314945611505000105100007601c80e00030b13404035542280740e140d248001c0e00e0280b02c0c03e5019003041d084080303d00110ba040d40500325100e11030700d42110046c1580700440445000c444014011a090750050002c240326180c400c0c11041a00b04031408888500b103007004170b50203400800c12070b038030015106100341d42c418811402804203040c117101c2c400c5556601200c506d014000c07060341658483c00100d02d00e1082005000b0312901506441c5060800ca602c08003a50150109440d20140e0101140119a0100480d594248240083c40c11900e50104864583c0c2c0041c980c0d0b4441e01e41010086450b54034003e1a4160390202c800000c3d0342c40c45c00f0107101c080302c4950302440c3d0541c038100d8100049141490110342920240b500355134030154 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 369904172 1250 369902922 369902933
    0x90f060305012405060903060a09080705250e01180b0105091003140105090601121a1804050d020c031222080304030b010b09130b032a090c0403020105040e04 69
    0x101640090070039800d100780d10078480304540500300886a030308010000c1540f25800e000f2103201e0150b9054150f4009400075543e004558041c119a40c03054002d10320781007070b40c2c603554541040d00c10109109031004a0741150412700c0c4824500800c01e402542005601d455082900e40c82d011070346c00b8145885a0a542a50b0720803003c484c4544401421030803071803140d41005000380a41c1c4035002412031500000700301407420320000e40c42501c0503034564004103030510542000e030542e00c2240c1c1c0c0d40403541042c00340651318804000302094019107501c01500d4141401131070701c1c40b070510b040c044d50002e51041942e40c80124000010076030003041c0b07541c1c0c1c0d2540340088070060340d20071540d03051200304100443c00710404401401182e029034820001642c07100d426524070700c04c0d00b9046c0d5201104c0342c2d05e200c00c0c214640040062090060980e032160600d140c045001201042c6403600200d005420303030f2554134205941c0b0fa040180d20740c1d00c9003440e00b181c0c00602240301d10300440040c0a5624001400c025 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 369905422 1250 369904172 369904181
    0x1e0408030403180803090a231c02040606120b2e090b040b0406110c0f0d1406041101030c020303060d03051b1204051003020909040822120c0b0f04090f 66
    0x21020304443e582980c03684440c0d181d40190504512401e0920340020302519004080310994542d00203114a6100410070455600030608031307121300444046080001d0790340ca02c2044001c0c100768a40c02e8030b5040150240c41201da81341880c61140700c2c141d411498240b0f0311181038003880d2012044003500403146900350380700019984994000752001070702148482c6c401006c2d108a59a588546401c03199140c51103449000160000c5d800c9150a48401c2103850300d020590402400f46a0100001c05081e0080341000811101610b1802c00b80d10f010281c0d5030b143c46a504a900d8500c099401c50922000141940d80d1042014081040100e80d07074032803501141700c0d609000d68020880301410810559002c0d10b4105104503440b4000200010b2240c0340240211011501c00030161511540c45696548080e040142c032043e0b44032058a50300b0382402505510341c017408400181021500c0580b610b035003d20f001c0c3c2c000c0086048180000f50214451200355001d84258407004224441c0d40101d04c1e0081 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 369906672 1250 369905422 369905447
    0x906050306040b030111090123071104020409020a0309021003020c03090f030c0d030306060315050d0624030803040b060103020f07030f021005180f0c03030708070c0e0c030f1e0408030403 82
    0x42d460b0255806e142d80c213105c003d1450072000c2e00e480520018400302ca404154012145490142c8100822000514007030100d180441c00104010300340f58032200801c0403a00225003000c082550b07407160a055103002220381c43d5201c864a010342ca4510711943c2c558030381c000c4407041401280e051400c05290303a02442040320490001d4000c002203505030500901801e017912031000442d01c0c10004a0001c0ea100d0802c2050b950060204004040e0703940d00c807401403064151800c13801100140051010030300340790354001107000b900c0c020384a05141c05c001d0705200c4003914850602d4810007805000200c00020340b0b140b142c01d82001d06031100d45100c00c0c0c3c1082c1d2800241c12005262200f0454105250403503070f07110b080044100c811007052402c40c10f5590505042c1c10b0780c107510603c81000028241c03c01001c019100c0c00c103a04081d9995a01c01941e80303810303103400e40c060001000b0001d58140c688249540080654850544603160b03e426031003249015101400b80c02d80000040c09250003009a105d46 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 369907922 1250 369906672 369906679
    0xc01030f0902090f04110f0d330b04050a0614060d0e0307061d0d020304142e121107030e030109020a031211010218060705071203020115080a030906050306040b 70
    0x20b500e00300e40405258142210206c030300130305110404405080c04081e0031034111014280d901c2886841c4c86e00240517020103248c0c801c00c0300000c5149000241c65600f91640103d9440105845ca0410104010b482d0010025000140b501c0000c10008117650b40007032207520305898080d60b44260600c0c0001910440300c41c2e002c1031200041c0c4904200035944450040140202c1c0f04042d4401c48080c181c0342c0406083d041c0040c0d00601c4140803032800388588130400f040c000e01c81c04900c0c0902d00b4810f54017480384842c080c0c903840d801c400200c49400c5007140880c02c000000400800d00c1c080242403ca02503000040c00300000140a03100704d480c02d601c1200d04c26002000c601c03019603203207840c424080e1194410300020b02007159405042c4014000c0c1c41410300e901d070008521a80101c103010060708200029600c1e44100400002c80a8240391b11540d00b50090b40082200b00c0c4c4400b100b208000769034401c0103031794443d04840c4c002c2640030345180207607075841c070302207699031030340340000d0090420072021950 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 369909172 1250 369907922 369907939
    0x6030705041d15011a0c100216020918060705030103081c271118060d02010905061b01230703050a1b0c0b070314151324080f0c01030f0902 61
    0x1030103414120203034100d03807240083c0281c0c08a18105442c0f20b02072401d040c911b5501c4580410a90f2001d0340242514883e540880049200d0035000a040018140c0b1a8102041d001840e01d42c902014006194442400c2c00c00900d50352569513181c03001c0c410b482d000891501050a00440300d0500c3c0c010400c82240484180000601428112420808440122442102c0f517a24001c00c1c00c200c0203182000c055100300d00110340e545018080c3d0b0648100e401c034100301c2880c1c0046810f960b9800a400c27014440a00800030176024900c2e1800c641504800202d495002101c0781c0001c030035002c405a002c801864007040544809101a0192031400d0240070103004070f030b500c6100c5903480000d500807180940145900e98030340300d00a4040b152005c4002510307003c1c40d0000380348201584420b855a200c00383c001c081d030318185000c0c1003c880d00c0860406030078500c0014160400c81400400000d0103048003e0701c41201d01903031080e0740c0c02c19a00726506054035420030f8201d4240550000e00c00c282c0290000c0b4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 369910422 1250 369909172 369909193
    0x80d020406030c1d0a030b0a110a050a080c1207050c010e030c0a06050a1406090c07061a0108090d0f0c02030a02040f06050111030f070305030a1803050c100506030705041d 75
    0x7806840c5070a000c0780050304c2c0e032022a0046200151070180d10350094411032240d800c40d1100640000e000b022071160795140c074041003600140b84000c0020055964455459980c4400700406204000c0c220303001c06441844030b241444c1402c0302a40d04103185040450399021f00150840c05401e001d0560001ca00010441030720b03204001c540410428421030007004141e98603040c800417656502d90150255031701d4800106603003040b04984c6d030020042c850b0181095116500d820a4034030448400380175401ca00b80e80b1100d0f580001040d0341008440002c1c1c01c4500e1003070401403030740d01c6111040301041202c410110035903d0078003086410780d802901c2804803520300c4914401174000c500c1040d0020b0034400285001038000f10940704ca2498001000b842c10b0055142260320382c10180100c031030030f640c5900710a030b105603a0302e1007030301507120303403a540e44581141c1455820062443c031300b090b40d141040100711040d43d02244000c00e4540071180020020300324000203114401039500c4e0340c0648551101903 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 369911672 1250 369910422 369910427
    0x1030804060e09010b040b07230a06110304050c04110403020607230a050601060804080d0f060501030e01020903070b0703031506022b1d0f0612040b160c0b04080d020406 74
    0x140180d0780e09071034580c8440400814003500d95000d12410003040360502042c807140c550720008090141c0240111080106a0054202000b40e00d8220b0310307050b0320250300082004014044c1000d11000c2031300b098114540f84c0c4a440e20b03801d0442e205449a65a505400c44080c40e00040ea0041e40d0058140c986941451510180c3d100e175a01000c810207603601c0c5902c03030304c5900107568100580d201c3e0181c48580d1801c2000c0da030310740015200300d495200a004641c524020342c81081c0d84030940d9040410707075a02c0d040014040b6070b08171007402c1c800c0e401080085c5441e01c0010302e403c1160340c8559056542c00c0c1d682012801403c00d051a80d05006840a0001e40164001001a200682c0304d003030410700c011001c0180001b00148540101250340302c450002c020030110b64552032080090044a4107402d120300081c1d00d64081d00c004c5031024441d02c180414804a900956413100d10b44451944c4075844000203054039408030790003400c1d0b0042d00c00250030400d1001c00d54003810000c150030b544641e240e4201 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 369912922 1250 369911672 369911677
    0x10f0e06040b0108070503030d2c061f0b1c0f02121b032202010c0602031f050402040501050304170403060c0905010210050f0601030c0215010609031a04050d0302070515010308 77
    0x1a10724030a05400032506000c0031821004540c2c0040c02140f0380514882d1103005402d4072070480010040030604032145080c84e61603030902071200ac0180041e407524003c5801e45a04070b95001c09506c0d0001c00c24400c2841c4141161024024091030000f5503401800d10300c040c0891a008001d464004980c0c8404043d9106101740119000842044040041c003081503050004070b840c4500400d0910b2400030032038202000c1c2e948540185232805503001d040d121001a64000e5916811244070700c100000804942c42c12140500400c40301035141610f0800020003030b00000c0c00c0030341010501e1182c60546410750003150002c3d98046420320101100c0781000c0c00c50b034070324441e090142c020002007520000181c42914400c082890700c44072103131900c400460041509102c007105501c54074401c03408000001d40480d000b44810303038601e82d0315402c601c3d00e1252145402c0a04907184042c005010024001040102c0d1400d6230740390050311034030582003840c5040d0714005000340d0440203074008410302020400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 369914172 1250 369912922 369912931
    0x70c1509151802090106020d050405040c110703030503070912050a0305030712050108151e19110c03030105040e03070c0e130f030c0629061810030f0b04090803040b09010f0e06 77
    0xc1010384d40c0c4c0d071031205a803540380124042000400c02c1005021500d401e600405108502c0e10300505554919400540390901d150401d501080340030040203101740d4004072110241c004410386003001d1603540e079a159201003603030300102401804070009040c42d100301c0079104070344c00c0034001340f145594a00806032580d00e00140e070a040101040054005254130403200c891040f052034459142c0c2d2080c0c0c13030b1000490344d070440c80c06150300c5640d02000c0003099402f80150745002c001456a0b9454030f000c000c1101c0c1c0500415071150010b000610100300821400012038480f6844104c0a58841c1c000108a1110040041c4100f80300e0300904141548445200011441008100100d51703094041c4440d442a0300c240241144408205103880d040100c0680400721400781d0701c04010f0035080010741c083d81d06134940c80c00a507588110403032140650040243d071005c02e4804101083d025200c0c03009a1000600c0600148480c20100b10030135002d511880814041030320070022000c20244580e1160400d44 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 369915422 1250 369914172 369914179
    0x1b0c1c060b0409050a020f19080c0913031b020a03080c1e070503031c090b0f1911031303020a0c060504031502041d0a0b030706110105070c1509151802 66
    0x222151040d040521503d1100f541020080c405041e4650030401d62843c401d51440e00403407920019403210310b007540650003500ca6900681300420700703c400c0c4008000300070012005080d1014902011a42020a03100c40103401c04203d80c907000c46001092201c13441d81e10042500000003a440082000410360510054021154540284203100c1c60784c0d40f44103034001c45034140c00c01c101d4100510b9150030594226600c0304404138101c502900d680d011510215a03041c113040a50040004002c0804144446040c0b0f080e01004401c0103680c6c891800d000c02007030044020f002400400c00e050007005200e00c1c103580244d0000c046074072400010b1071600b00b40710071100e10041141b0703d01d06202600945040d2a00196000c0b540c022041c0d0304010420090f001c940315903550f1010403059141440158040c0c043c6882e51a080011081141d003114001008901004080030000c8006040c0c18001e07580c2004082010400203481c0c205401085522903494114500d41017000810081603244c1400700345c003c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 369916672 1250 369915422 369915431
    0xf0812010f0501030f0e0c060912010203070801080607030905060402090c1e1c050402060d0504080c0a050d0809010c090314070b0d09030e01021f09031202120604061203051b0c1c06 79
    0x10b81804261940c1806c0d90b84183c00142c030002e1a82001c80107080d0b103000c002c0c014880071011880c03103402c990050f241b003800182050010b100a070020000325401c11a1454100400801e0f921100c0e25802e001d40020703c030b503012401080385100d041d02564841c145211601c501c404040900640c10380c040350514080095044c03200c0101c8400e0304c1124411900607143c10719144009140c13030014813004004903104241401020030350700c0200524241c507031041c0014511042d806001628400f8000c01480c81a07050009800303110798400c040310116a403080c0f9582480d02540c220508040141c0c020321100c3c02c0101c2c01c22002a60341d00b02002940c02a194844820600320049840ea401c9500c055807400c1401c07640d500510907503011482d1580640780c01080c0514a00800050f40d000e801d40040d84407055040c400c071443c1034800d110082c40c4c0e06448013000c02107564040c00d14065030003004484120003801450040c410f020000511303000400404482c041825402a030031810202aa600c9160 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 369917922 1250 369916672 369916691
    0x1409150603030705071206090c0f090b1e0d051903231306050d0f050a0f0501052715030f0609060718031b0e090d08060303070309030f0812010f050103 66
    0x4401c03243d100da003010182600504000602819901e030000403611300c4d81e10551400800e0380441ea0318050050342c805400c0b000d01d0001141d040d5100d071a140e61003500f81020003104281c0c41401c035940e491099401c140340900074100303079041c075004002da000100347c0a0031140415600024111810043d0751000410800a20008106000b14070555582200b18007081c0000f600620103002d080405440218090f106010003805440b4141ca000345440e49880c0b44a03180d04480c010745001d420240c56132403022000000745102c4a075000b10a208070b481200200703000d10700891445d8856a805400c036500341c1d1001141e40e0707407010200c603118814001c8001082680303209007030311145048061215184c090860716074082202400d0001c180c2100e100d0750000b40c00140000c034a100c5c8109101420310300d400f034000a82082e80090606100790010010040002e800010070010350341c0012031100e40c0203440c50982c0c0f0510030032120942074414a4000100e880c1c844c0e400c2001c0d10380a0f41d09100300d80c407 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 369919172 1250 369917922 369917929
    0x80c01020f0a11130609020f0418090222140408220f0302060c010e06070504080f06010b030406050402120a0804170f07090e0a0c03061401061412070314091506 70
    0x142c1c154000c0000800150148140c50b0862030f0920610320310a00040480c0d0710410042203a02070038207500000d101040c1041040e42811600380b40c0788050304144642401c541c0001c07160b01c100e1341c4030f41c03a1014082da04001da00f800d90040e401c070b228400c90000303203081ca800c0c0f101054000c02d8180d1031660040400c522a800200429030884800c4114200f24506584c00c00441e07820192210050b136580706080723040c02c5820800540201126155180d440d801c181d40282840b003c041c0000b01c660000c1c0041068089210490354803070740140e400211030b02c80d0300c00186018031000c00e45046120b0340c101ca1003400040c200400032120140c07001c0080b81c421040340c40e100c4102c40152419030300008004c0216110540190304041707017100c10b441c602209940c4000d040a40b41d0411b4400070303510034501c80031141c90400e0a015050a0402e03038005410b01042e55440d00c1000c491402c0d006070003003c25412030003034100400b060145481071180f450522036803a5a51100344512081e84074507070100c3c0a605 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 369920422 1250 369919172 369919183
    0xa0b0c0d150b09010806180f0a050c0901020a060f06120c0503070f032a05060d0618050c070f0203030405040203161d010507020d02121e1b09011509030606080c01020f 73
    0x4068800050800070883d0054405d003c0051005170411810000340e000c1c0d24a0603081880340b40310300340d007800c01e080043e250802c80b00001c0c00080c10301c1e02005060300c0c40c1e8001a0100089500c00703400300e50082e04a00800181070310350300014a48104200750402c02c01135021000560b00e05408450080380d80d020500780c4000b0034407010304409d0b074070641450b0003450303400c480e03070045800e01d8102003065903803000c00e0090740410520041c503039994000740414412f4402015240420750b0702400641040d20f6a9065442611001444202d49040300703030864500b801554000c100043c021500c915044c49002d000c902902c505200141c40c1d803a550401603014440f8180324001a91441c2c2010000d0742441540d100c842c8059034068030714207503540b8800c8100311110442240c00e00c103094030614100101c0c0307050900004403d8600c42d12102d03821644500310381c1c42c11642c0140f14018480c24040060710500c0003504050800b5007006004a901c1d6000500d1030307010a802c0c1c2c211381101518103140c03a101e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 369921672 1250 369920422 369920429
    0x30c09060c08090415090c0e030d050307050304051c090302030f072d0803070507060f02060118022206032304120e061308160501110606120a0b0c0d15 66
    0x94000d607035107022802c58000b806100d60f02410000d9070210041c100450005180c1c0884044c0e51564500c0780c2140c2d000d020701107003450580c001c2c800003101c04005400d9020040c0480c0800c036003c4001818050304102d0300700c41c8020b540310030203c07070540c0400404c1d0500c0741c001680648500303200c13182e180c000004c11604a503a0755070300c51010010b01c0b582d4121103e50b4040e080c4541e00d401c4011481c503400344003e0280c1403140c0001c006103440c005002c2d00110802000740d0a5401c501c0040103201c0302101100e000c801040030040e40e80b243c0c0c40c46060f480030244114039140b4070702440818256010f9210b00c141c00090301030b00d020500500000c1500c41e40445004061444502da050a01c0340241e626900c48400100641c1c14104911896403000000782e00207801584014a6188001034680348070018140070f1074600000fa07648000c0700d5a948001c1c0500b800b4902c5291110001c1c1414810b00c0c00240e4013041303103c845d0a00b100b50341941d4000c42042d051030f501e088ae40c510481c200204c0f00045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 369922922 1250 369921672 369921677
    0x2e050903090a26060c210f0a0203040f081303030206100302030c041a0d050106051509010e0d0302030d111909080a06050703020f0c0d02120301050a03080309150c0a030c0906 76
    0x66504180580c1c2030b20021908003000c0c5005855110a14442070050b03600c82c60b085805c0700c0d26500c80c404825400c007a1041200003101c268824820741150503000c00394054a00d400240c0d83c1e03100ca182107402c1d01c1e00141d002e00884001701d01c00c0c6007000000d50010072240a07500302c42054892150803c20451680b03c020340c9940f0001c103010705420140c00c0f180d014060000b10401242400c07010074003003880071408030f502c1d95440c00103110910740000c440c1e01110300307038070000d003441c2e02440046c01c21440880100d10803102000d0a60406200700f0484000640e580340c10b1011000d28074121000790421080002030f141c0c01100d00030107501c81d02170342e421205030000500b000c01407922a00000c2c50040d01c0c6034100740c0c08104541c03550300782400910700488000d00504030002031b194000e0802c810407000c40c994001c01c100410499441e070301c0c0134084e2600515032658a44407620950320388440558a481d8031404401005400d10082c3e000d403c91000a071414403400705440000c90704030b5000c1c0140c101 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 369924172 1250 369922922 369922939
    0x6030105090a0f050304050a0602070806090a020f1306031709030609120f0f22030b10180f0b0301150f060528050912030310170601060509032e05090309 67
    0x41524144014070f200c0c00307181642d103441e89440206100b516645c01c2000540e00c030010130844400108509544202200042e220340c405590014182400e4404494842c0d0340300982440d00010a9112030002d55108400f0901e0074120824010070ba0000544503100340102c000050741e01038003046050160002002c2c003440c0402043c4010f041d03030072142c100c00c903070401031051256070944c070051400514111000c2041161844c40c0143d078200c80103025607403203014000100071800b02032281c2c03660720b040b01001150390801141100000c048880042da071560824a00d00410144040c55406446d03608504a040a48900040d10340c1c5c407903c3d040010710621085149202d03020302c150f40c038103140c08e460540e2414080c500010800c40f4920303d001059000002401402c0d1500c5210340003e021240c20130a1801d01400d107592140e4051060300140301d4001801c41595034280144003000e8442008900c1401d14405183c0c03000d484180e1042e0981d00d0240815881200041500c003441d600421040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 369925422 1250 369924172 369924193
    0x90108120c150106020133062a060e060601080405060106140c03031608071416020423070f090e070e150a12150e011a07060207030f0201050603010509 66
    0x3a05500c01441500240920700c030440814880551803402000c15500203d86010301102c0c41201c84501c0e0303500121245101000c034600089210210202d41407810b1001910781002000c00e5111040050701d074800800001034820800e2581c05520110084008c07241d1980e540401901c4201d0141c41c06000d036070141e401044994460758412a04a002c0c015007808d0400303180303000b8955002900c4280c190052010110462913008541d103900542074035100340d18901d0002c00d00c56902c100c0c6480c0420a00740708003c8159103c50300441802e00c20fa0f00c545011100d41c805c100c0b01403005941c03080000c2d05081c2e4000800380720b400d4040564007a50060503981e11071010075640000301c0c40381e02d81c01c08450380d181681038645034090203401d2850344406441c03c00303410b41042103c8440385003280d040c0b80540c00744082d00d144003095041d262900000c080b4007100083c80c1000d4050b0040c000c2c000343c0005000300400d40d00c10f805107040d200da0313002400707503884110070542600c0b8202c450301c8140c3e210001c0310 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 369926672 1250 369925422 369925453
    0x50705040509040b0714160201140a0c081b0a0c06020709050103080421050d180f030812070e030a081804110a0c020a0302040c020f070f05090a0903050d05071d090108 73
    0x42d9005003172400c1c4003d40c3c1c5079a080c100980d810100590008810001c6000103550300b011515152144040a4501d042d43c1a00064005020008050116000450110320284403010000e0312001c1d01c030219080100c0d04c0c0382051900d080d40c0950401800f1740c5000044000c480c0c010030341a030ba481a1000e04190030903e5047c01e9105ca9402214000240d41d02e84011481c20300040c001410310b903981218420787c00342d1071102c0340c0341c0e60f0207580010303604401080840c104806465080b000390400800c151038006040314041324512400b80c0c1800b03440c0b072a00c20010381c08010a424542c0826040d814000d001c200022502081485810f0703030f20030031881840510840000d0240340c401829140d006807030750049400c662280380341a0250303010910201d0100020000c1d40008c4c5000e108900545040c8804070346008009083c20104586844044003014041e505680518049080411091900c42001050001031034a8010a058000c2d1841ea4070b007406034015060b02d0401e0010102250b106020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 369927922 1250 369926672 369926693
    0x90801150506030402040b0a170f06040c0e0606040905010807090b03030748080105090a0c050f21070f0f1d0604020c0a140105060103060810050709080106170105070504050904 77
    0x81364425650101705403550f60718a65100a0442400c9e0815903141c0c10200620340364540c0c4288400b0303031003a010440020511400c0d00c05851112400c0840c64035944080381250089810404034281007100208080354001000421100b0003501400309413003010525449129002006d8040c200d03510010354200301c00f0340300b2011050070514444188811441c1111103039601c60750310000d4207040c5410045040240203598001c81031201408080340c0315138444980060b40e2240c079014240741503046030903030756581720300a26040607115005984a01008980c4610b09401400b818031092100070442d0800701d482c14041c0d80310303502009841c1e405602c03001c407003040051a15601c10b400b0008920b1843c402e02c50b01048900c140b1107241c40598100030701c1c1c203494006098504151400c041005074500000b4411100d018041000840f0346a130304003190b201950342c1065200d0344c280341c8001003206c0900305000e0034690700c0c80204450340311074008840c284158400c15501001c00c07000300d00031441c41d0a6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 369929172 1250 369927922 369927931
    0x408251505270319020f04020421021306080f1e070902030c0714240c0d020c0106080616120c051b1504030c020306151c020f03030c060709080115050603 67
    0x651010101c00080060710b4418100c4003010102c1c41c0d02150130840c10150380303148070504115800d50800703042c400c500c910000c43d0125100c0c0b200d4600980030542d12410301c08030240e81610402e008c1140c403510210b580742030409408803141315044090014040c0803040703181290441b0040c198007413074440000d020790000341c402c0900f0320701002114006840000c444000c009800301130046070210782d41a04c2c1c00140c100b24000702c00102c1d010810b002c0c0303e010868003048032451005840e0713800c810080d8010401038001404031b1080c0810701c910080074403400412145240c2c0c40120401800b0301140c02d0382e8221188801041c82405034604008141e403503a00c02d22506070840f540122040c0b5821440c4806490640108030410711000c03e509051100c02e84c03002c12101d400303a007010408041084e1060480203040c29122481440046540d040c405201041d07005046075120b030326118915454072001d641c2507011460f02c0d60700007100f0406009842e1054110040111620702c0c180038090309600040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 369930422 1250 369929172 369929227
    0x70c03080a0902060d0203010f051f020d0f0c020a180b0402091c08070b070507120809120d0207080c0d080906010b0901081902030a09020108070518060904020408251505 74
    0x205d0494070340f000744051402002e42c015044030760780c42e00d801e01c15060034045000d481c0d1004140c2c1c0e030700e03a6070700018455440c0c0c1503032800748c40e01c03c1c00c00c10171503450800e0400298481c42d084070014a81500d004401920b03c2141070402031380e804001007000b00d200310301c407042c1c01c50420449041041240c07001445c1c0036016242072440c190301c41d90b8941800b20110348030804620042051340506c46444011407008629080039581ca042070041c003a503500c00d4610b6880c0c8404005029800649650182c4520340e80c00640740352541c44400b41e05032607404503145003000402090004050610015603107048421402c1000e00c6c2030861801100c41c48002440000702e90503041d1007069080c214401035104d09522000091481068800184a61005880038007006820302c408d504030a44007001d800e003918100c0381d444e6a50b510704080703000307405254407001075805802404c48211711514002da0000c025000540e03515601da0072103c4400600400b00b800242041c000403501e000642d0340110303500c601c2c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 369931672 1250 369930422 369930427
    0x60f060c07210203060a05010311040624090b0c030d0e06160302161406060301050c030603032205060f1801020703081917010b180301050402150a05070b130209070c03080a090206 78
    0x2034020905d420003d90741a51101e03038884c010000c2c00411841007039040ca045405102030b038507200b407000802141e95942e004905464620407100ca0041102d075000f0b04d01c410001e515041540041500c80d0400c0c0c1c4100441414009054400500071030f0640c49844070100c00c9103a6040c041c8110000c0d004003514008003120b03441c182010410451018848070034240c028911480c1c88005d0600b9510058401c14074030b803081c018054169808810f5070202c20149001203000c00c1d140c1c080854031035003580540c0d008400000c0c0003034114002001000941d0300601c101d110a07200c2401243e44031054800584a000d041c46030346c1000047c240c40456400c280e00d0004c0c918400c101c01004450300a0b0b000c002022000290b501ca940d404039940481004103c008214600c1c00390081220b680341d6190380c0341424400101c0c5810300e030060741601c0d0138503040345280c0703100c0c07030503a002240c0d220700150700303a02c2181000000349030740344143c400741005981a640c40c041a1102140c51014100407803040343c1c0030109 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 369932922 1250 369931672 369931739
    0x1e070c030908030f030916050f150d05182811030a1202010209100905030303010303140408030a02160b03190209010c150605091f03031d030d0305060f060c07 69
    0x200041c000703218103400d10310743c1c90901c2100581b810003039208000341c1103803a20341007025545040e44600f0b0149c007070341c5010445c07210800124071445541c910b09000341c40c04081c0040154418070350030441100800700c4d40e40002035200e075101b11060000c161698591a03103160006102c1c800c0d0030743d00c01d0025080328616015660b9408031107a4030440c5100507980480e401d1240d1800d808162141e1290307043c5580182d0410012903180e100500000d4103214800d10303e106001d0a403822940181011400d5a40b204000a0020344608002404991140d952240070404d008030904480c0a640c0e9100c0c5040321400d003c0c07001001c0d4010500090500c0f00550010b00412000c0203070108a031030184000800f07509000c2040190000504070481400101c800c02c05420341520406050303a4060808401640707245118032070781403a040c1d450740c06010b0566201443c2d034058000601440c000c48072140d02618504c1401420700512040316515804410108a03a81c034000c2900c0104541000c0c10002e10740 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 369934172 1250 369932922 369932939
    0x1005010f0c060e0114060616120e1807090617041b0f0605030901050106030b010c1e0f03050703020c010503100e042603010905061c0605270c091e070c0309 68
    0x22003040043c0740d0f94554000e4586840000210f541c0840101e860500340b610b264282d51080b5200c0800919441d60240c48090450098401081180002f4020290b85100c84040b002021301500c2400101c0c0c009a808101e090041002d1104c010b0541c034000310720742e83e030303140d00000a00080c0010303902d84440c0703804140070700740400001c09081c2d285c0342d140d601e05256210f2800c46005070710200400d8070340140d440140e80c1c05040d00e60b4803034118146c150b019001c0d07400d08020702400200106404054100c0004050308400a042028000e409032203407900140b0041d0742e1880111416040c00d100e42c1414011718081d6483c0780e41280c0248410121401c2440201c3c0b03030303854a00c49900341ca041c00710040005200c1d5008203035000109079110b84031885402c150a18214000800030035070b40d03c810014421081140400e6407040d0f080c2041c0b0305003519032501d030707454243c014000350007140c144000940000121101001140d0b624010b4000d0b650795010840701315161500031410464942000142100d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 369935422 1250 369934172 369934181
    0x6030b0a0801290303190e13020406020a031d0d021509040f0e0609070e0606130504091a01060c0c0b160f080d0b09010f0b09130609021305042c010e010609091a1005010f0c06 76
    0x3e41e933001024908080e0402038800c58101d200c0003030020140c515901c403034a4000289061a41c181c64000707212240c3c1d104030f209030255014664010b450101e903c0828541904440b242034081410b417080d54456412140d1a075404d8010303019156680302c041116814020b0083ca15031400b100400001038031080042c050340d203a10360580e908210b21400d1010900780d40300b01d60041145040a4044400503580d9200c400400e1181e101d60030380110740319030b8019940030f540c55200d50003411030403001d070a0301d0f20024070b0b0400d981100d44189404c4d0140300608003107100505907040080c02c14006032620074a14650b03400381c03017440d4100b0354150022044203402d0103503002920881d40e000d6200c80f0342e8075410b84403102951150b8810f0b400d080c110b025106c2184040b03d0440103005812411b5016841c1721409440414030286a40d0300c1c041b000541c2c0c031019400111164070403001e070102048142c046a082c07403400e8030b5024032521007010070485076005001c41c40c0d0380c805600385441004041e44440c1c6c1200c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 369936672 1250 369935422 369935429
    0x3060501120c06020f1b1f2d02150604090512030106080a061211030309060f040f0618170a0206041401030501051906030b0a0801290303190e130204 65
    0xd001e60740010041084124a84014000a1009007000d00302c07050a071b9584d0140c10303100f4a6420400d0b507407080f0380e2580310b51078207042110140c18003c07482c58480245480c0341a03400c40314081c2601e07205144100b10391100094005194014884101780d401070000f02e00b005404290311580d114408800100107005403c1000c0821400985a40c900300c40074141c4c1e90014500c070303400b0345005028003510f01c161a000c0d008581202c4480304202030000442c1c13840c070aa50038507520000100c0c1424901e1124001842030300c005103035104180d5511842510484803201c45013810418524081c04005030440207105807480d00744c21900c0201040d004102d00d9880340d04088821056026000c00c10b507003600640b401008150f51012004d000d02030103203032852003405001c04064882144901d030369213022000d000303801c00f807000b0485404030440349070804680b0381030400b001d01012680070240c5404003d076840c0d508070350500e007018860724400707c44403d92580070a83c4000344c0e0410740c850085510140018 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 369937922 1250 369936672 369936689
    0x70816050a0f18080a2414070302030a0f06120203010605040b180703060306090c08010c090b04180e1905060106051c0b04021201060e010e12030a0305090a05060c1b0d020a020f010903060501 83
    0x41d041b400e90701ba60301c000780c04142e85140e00f0407100c03d05503188460f031a40d001c0250320780180c5030380740d101020f8040d28010100b01c003020700b040c901090017440d03d079059030701c107208600800c407803a61102400309440320300e0300701d035440007010074045050750345480501d500000c3c1d0301d000100b031500c960302c4100300c600c05401a00c1146641c0d409212803007007441401440c00c42c90804804641ca028040c0b0424400c6000d40400417011140c007100400c02c603000002152007400c10b586000f4a04503a180441202c08811303034180c441e50000280c0c26010310126022085010351070328800003038980034400343c48603900007034000c4d03401c009080074081860b90090103030145a441050403844030000605a2110201c25407003017681200340d9454120000840c1c030281102c0c11f001c105559a1021036080051078080500240514401c0041501d40100200401c098000c42c000000082e05150340e44c851072a908030b00540d10030300341e4070054903181800c042c4103201450a903038000c0d102c0e40c4600070b0762000e901601d107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 369939172 1250 369937922 369937943
    0x4090b181515070f02010f02010e0303011829090408090d120206090c010c060504030e1e01020601090c0c0303051918050c04090c06140d05070816050a0f18080a 70
    0x101494042c2d0b80c155200407824206007461010b80b0343c2d002040348001d000341440f0810810a0099000390003640c0c60000e000c050f0b81d180d41c2d6449503070103620a200202d5488902c2d04c031040c41020024032201603c102c0e0756010203c424030240c103220b5002c80141c016510074000340004041560b40801e5a844584100801200448240e00281c9021805001005950804c10303004c42140d074886002056150000008141c948a5040542d965034100d05000e803c40001c01038400480040d9412000d005000c0e821104107a907684844003c40c0d08903900341000820451102e07002ca4840d400a075000001e03414000c1800c0c0581d010703101203d1440f00103483c0c0302d060444038000d005040c4180d511556043d01c06124000e0a903641016150480c081c0b5030501964040e031100300001e40e000d81d09407a54042c000c001a040680014101c0380d0225103144c000e1061260312041d1604ca0003d0300c90f203049544414680c16005041603e502e10000c1d01d10051404441000405040c10405c1848047c010054103c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 369940422 1250 369939172 369939211
    0x8011a0333030607050f071e05060f01060f0203040f17120418050112050c1e100305012c2403030724060f032d03120c110304090b18 58
    0x5050a40040131142402804e20543d011030f41c0c100115000650702885070300d12043c0c0c01c6030801d29400000310183c0740744a035404003c0f10507003030400076050310650345803046d5010780c2a1341244e0300e2245003d2070b46401c22802c02001103080c0400c104102c0000300c01560100c0d40154102c0d880d5402503444102802c1c0c044414106c1c4142500c6054050503d604125546c403c0e591a22550f5070030b00100540141c9048031703000c100b0000a29100240d80c0018031000c0b40b40c0e03001000501422003030158000c8001ca42d03210b00e07800c04a8040d908070481e00c4c8001c07001e4580e80d0716800c59600c180b15980c40f142065800c880100c41d5414401232000c0e52082010300b80380700490310305600c1160601d0400301c01514107481401000001a042000c0742ea0142d01d0140d1090243c011819440a03500c0345588034a0602c1d01c1c0040580042411403940e401200801038150740344030032681d0b100c000c0414041500308000034407100100780c03c12004036401030103840c680c04010100d4a0311800403203407807040240c1b265415 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 369941672 1250 369940422 369940429
    0x108270d0306050d02060f030c0f0409020301140409031d0109030c03050f010513110907050403060507080106080a0612080702030f060c03070207050a03080904150b0a11010c08011a0333 81
    0x1031010f4002607580300d036003007242c0c1c0c0403034007034481d150111494443c08000a2280a4030700e003240c1c4500d12282c005074a45995900000180d04280101c2d174089000c4003030b50b1551300f003074070601c0801c64250396150050504900e40110854440c41458100800e181c404004200030002e68002140300310000d010412440400500310341c0060014200c002080a840022071800c440f0f526001c03d00312042c10850b2036502017139909100d40c1c1c0c0010440c40c1001c1c20001e038079810500c071604884454070f80002c40d6450b10884070445e0041d00810f0840d08030003403607002054140000c3e0007040d00c007504482c07401c1402c8601c1c902d0070f402140c181c06205400010090b241d81c3c14444440109019a420081941103582d0320156005c0c961070359001b1075940d21a06000701700740720005c00401194800a644490101c801042072182c95082800c66003050305c05011148903200c03030340c100c030351610842500f4550b0910702039003644042c04c1c13810140c2d6140d4562009500510180702c17680089905203400880d40b00a1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 369942922 1250 369941672 369941681
    0x31506030706050a14181809070b040f0b0918090d2c04090219060302070b0903030103031e0201020d0c09090507170601030c091809140105090307020108270d03 70
    0x42c0800c24184000440b958000744e801c0070701d804060013151510b50b00c1c0c0304145d40003600450668400a80d140d14282520304540ca03601500d00b160076101c02c1619441082090b00c0745100e00c0e0340400150700c08020303080e8041c000c0c010144005000840d00d00003c51341d5030810b402035034410525044010030a01403500b1940310b4a0080c40048114910300861101429101041d8400e901072a1501c1c100000c43d0f540c03400c1d00500441305170074101019290103000380250001042124041c5102c1c010600c41c80b000000d0b00d041b80d0389a40c6e08046a48154040030031103c03641200c0c0155902441030b054803036418080e0400d100100d0352207150041c5400255015075102404003424000c0c40042e01c40d6200c44075810310f41c42802803d0200d000b6003000e4040b1032290803648031404061401000c2418091a5009140110701a48500301658015a41c5600700c1d14140e40c5000141d0080103894010f50191125682c00001000034940801c0740102d40d2404c5640345c0009505500700d2100b150f0b046405210303 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 369944172 1250 369942922 369942929
    0x4030809100305042f101d0a05030d0c020a0902030a0b0108060f01140901121d012d1d0604060f0c0c05060406020d02040b071b0b0f120405010b0315060307 68
    0x406003d2070a090301c540f4600f64220840b0b603140f4030032965000c80c802c07840043c60340490003e400c0f8075442002c1c40c8004c00c11800521805260004040c0c101e90034038090120405132a401000f80c11001042c01003503892051122080741c11442c2000c0c0020710030001e08c040c51261020384404140140804001448154020102072144400308840d0311030366489204500a902100300c019510321036000140c1d0a00640c59001c510701b030801381e0410180104002040b0607808110007400002240300003550041002041180a80c8080c801c1d00b01500481c1c102c2140d515030100c0303645201403c020b5050420f0070864041e00c031b103900e03a510f2030010051480f40d1082c2402500e01841900401d9a40e5916007101800207090146c007c20512040051541100c009040280e0907075a0741c91079140101c003c0c2682000e10714184840240041c42c09400c604892030625952803551600e113019414050502014000703480d40e41d42e42074070034100c2d01d0400281c030100704540e000000710301d005010140390110540 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 369945422 1250 369944172 369944177
    0x3020c0105030c0901080a1508070513110f031306060e06011106070905010309050c0d050a06060b0f07020d0f05120903010e010b030303040b041a161e05041e03080403080910 76
    0x2c200100f59008400391100c00d007007480c048039a070300c1d24041c800280c6000426032a2116204030006a031400025020048a40681c6d1030104500c02c01c9444040310040d1090344c40d0102c0421442800701c2c0c480c001190b1283d2405607609228081c1d4407203100711481a00a03203c00803007941448443c1d0b8010349500070240b0140c2c000c02030b82c600624000d007284880d11030300d410716454a0244080040c10300c0b0450300104003500c603000811403420704075a2444080e5042c2c90703151800c040401d480c1004c004551030200c11808040c51320210398244603116403100c10694005240d020316400094042c8400e04109441c5c51030f050701d034400d5000f05802c40e10101c198038600d03890132100100d25140802900c1c0c2c803540100300210140d031a070a2104c070000452000913581c01d801800c02204404004c0142a01c0c83c0d04c3d0350b44070102d100b440c42041000c1c10000340c440411000d0204005c550340180402803290f020040d600c0d141c560b41ea5840c8030580168004a682000c007040410103414907180190907a8000e2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 369946672 1250 369945422 369945427
    0xc0715080a0615050703030e0d021e0102090d020906130f0e0c041503030c05120c06071706010e041113080a0311070e01031704080d030603020f032b020c1201050403020c0105 76
    0x484880c0c0f800116100020900c900400c210003894040d501c1b6070040c079801340c152515100ca041d00203481c2c1080c100444c00e04c1442291101c0042c0701442510b0f500440500002c00004258081224407a40101003c2e8001c0050030240d8120384980a00c0c20320031203010011030040707003002c801820001c00c0c0c0b9056005d68075144119412075401b4650608403a010b08092660f1051410814102445800c555242c1c42c0002b411013043c240c000f0301144610041d40d201c1c425508495000108450f0554105000510103842c05105107802c2d80866812404050500e2400d8030001e202003d9404540c0480300710b402a9810b402419000141c01075a0340c10311b0080e1030042e0074060ba5072010001808050072810801d4090205151b0300001c8502500c0b620080784c0c0f98101c242030003805010580000c034050503040305e541380c2c20300300019034403541500c0b0b2051544560071001d8901c01c804210344140e0840c425400c0c0380082d91129982081d01c0046a40042514502403c01a2030800e810080a041017000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 369947922 1250 369946672 369946679
    0x162001090611060114150a0c0615060f0305090705030706080402040f0b03060c0906091e12010c0e0d0204061e0303090609030206160201020106031704060806120607140c0715080a06 79
    0x81403a90568241044084900d4490300100d0303080226004100e115806c00203012103011342244000d400ca41c42000c040c8903444003085031903407074550b610454000c40c12202c00703244154040d0b0042c9520070510000c0702e284c81c5d6074800003482c00449500a8000c0b82403981400158140b030f025181d0b6000038024180819a40ba0010030b5030f4600050001514080100d035200450343c1d0b01017201c040c0b090003407148014007840500c1d21035030b0515901e214070078290800b4641c260241802040914942a12132510801414007408001602458126401659800c01050603100003c400d080c0d5183d921003a00c85a003940b401800c2105140c10103018030101d01020001a0b4507801110100c1c00c0d983d030582d4045541d403006038007410250300000c0c100c0d00b0307080c0302d00790007005440070340f0440307000d40d40741442c580b144402c0c442c03101d00e800000903c3d074005000007612540a20300c4621981c0749074421074600122901803506003200c2c0e4108099150340d2091104003580c1c040011074000c4002881040341703929 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 369949172 1250 369947922 369947957
    0x1a040f0219110a05010f060503010e01110412020303070c120b01080f0606060d020d091119140402030403110109050a11011e080714040e010603060f0305121620010906 73
    0x148010070504208032051010404a018090314807010b5004d0001d0101c90a1300310014060503290103078600941c41d024034004510360500440740c1c0b030300b8081911303450942090031005201d103c03480c040e03030144010084140050034100d800d0005283c0000d45002d503020ba440c00d0030082e0320607801888154441c48142c600701002040180d001a03080342d00355924413500d000c0c540039000b194150341d4038610706044135050214424135040c050380d0484010908d08100c0c48401e090309028040c041240820841502081c1400d500440d0064001d040004502118407800c900f50780700c4120845a5410286401003000300d03d41c8004003500c400d0820f02014100242400d00d0000302d91421010426890003203003d56014882981481c1c2c1140d190f50354494480c05045802d14003031280a0000e40782c6040020400241070141d81582d501c00050f0207108c0e0f00011038821504007002140a000c1c0c0b08141400103031442443c82c00e140c400c440d4181c20070082038009041c00f506507203c8000d0205c00c000318a40b910 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 369950422 1250 369949172 369949207
    0x708060a0f091802040e100e011103041502070813050a05060c0a020103240e1f030807033b030606010e0d030c05030f0f0d060f0308091c05011a040f02 66
    0x450b045000126072002e0040034003402c68108010350042d01c3c1449030b103c101008a100e07260300700300314002d101c02c501d042c1d0541d080b07a130140d08100100350284041070001d961440c074000700f0083c030369001d41000d0710754a1752401e640c007207402601d800883c40000c12a40c2003080e0090020482100c0c02030400e101045541d0b00c412182000034105a034440118401c103e0b10b01180c89000d84400c4900c1180d900e07a020b8000040041c3c840d107206240703600800007018403110400c1c058942c4110801e003811015902544e030310f640d58024080944a0047c16500c0324101900500455020760504600c0024070013418200240a404a030404c51226031fa000ca545070700581071106a410728022080b49c400341002411402490815084245c002506414001c0700e8000b0700030810072558200180c555070001d69080c0000351100405c0c4c1801880a02c1d03462400c11511048403840504e5801c00d6050303583d03042c2c21901150407003046801003028020070340c01c00b84a03c664200e0502c3c4118038005440003526010b8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 369951672 1250 369950422 369950429
    0x1a0d1112180a0606080102070308010f0609030807060b040c1d090c040b0f040306020a020606010207060c390803041401141e12090d0e1f0807090305060c030708060a0f 73
    0x25000c841007504990020440c525005402200401010343c603004000d01035842080c0030740002c0c01d05c00010481c020256100c504550380d079220704805a00c0c0da40d0300c09140e080803030300795400360350b5a100400d641c40d0750094a9480c070b800da81c1c0c603141d07840d2040716040002d90040c1150240e01520b040180241b50383e0210ba0a070307140303006a0303038403040541c40210051281c0c5e000108894000301d034201c035a94001903c40c0c001d0009800ba01c2990b0740b150411121511403c01c040d0242d0a40800e500126100b006403070592a02100da07001c0401c0c0c145d0720007a15408030381c04500c1d01d6000042c02c0103107245031a406040b000091804441f415420000255540240420b00300d001c91140e49091102c50000c04541c80d85040c201c4004141c40c1c0640e01503280c26513030484201051241d00300c4141c0b0300d807028184102451640600c861408240e400700c2c1c480c44010301c41c2c000d0164514000c000301b9001c02c03640d403041600d80c0e4043e0f030340d00d0004030061043e4002341c903540c083c200d074540601c500c241d600280c100b034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 369952922 1250 369951672 369951691
    0x3100605090301020408122802030d090309171e070513051012050106030c1505030414030f0721030608031602063f0106020a03050f041a0d1112 63
    0x607070741c0e10000a4024400c55000362068840c05140700d0882013803002401c0a400d80070b0001b40c514035102010b2945580200860303006800070000d000030442c6139480030590314003030310b40740b000580c8810400141c40720400f85c4100c640c0c80a0b0148a6555102c7c540040b11b4840360054078545284c003000c10031849401c2d42c000c003080d841e03100066410b6080140100141440001010483d1003800c2c030b01d008118a00040e41d0019400d0740214400703800248140070540150b071014036580d25a2101c80005964100340c202c0b42c0410001e881a184098000d40700f41805050218042c40d200600f6828810404001000341800c10400700a56400031050b208050318070805208500b00034030001c1d10620619651150100a00f029441003180c21800840c00c40901140904c8901212242194200091056000603030050010000203481500603100d016000183c443c20651290f21a124002d8102c00100c044034002c40c4018100030b090282502e4904d5160384d1034541019441c0e001181c140040c010b00d01c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 369954172 1250 369952922 369952927
    0x605041506080a180c090b040b0607020405150303030c0406021608031b01020702130504060c2a020303070c0e0718080d11031207080a14160318240509010203100605 72
    0x260f00c2407504070b0240d29800300c400604d840300301e16080000000c80c0c05602c800c2e9160110300340305401c180c8581103000500601d80750800d9140d60810010300001402c80820030582040040740d9101040694002d41c0c1e04040951180c0c1021780c000c7c82c05241d90300407186000c041204204a10001c01200d40040c4409000101011100c0440f030180c400c2d0038000790400c039500881901c09145600c854000c0d44501d00600c45800d51820840b041c00070248008500d400c0310012503008540500341031500c0d031000d4240da0802c12251030f084c2c2c0d094019400b032490303100c8100c200008160f1000d0b5424000c0b101c0c0f4803221909080412140e5941c46480b0010140002c401c100148882c08108ad9190491030102c0b4281624000000030a009410b540c0703ca440382c10300fa501c12041421402c06486105400250281c40c181500118040c0070380c641c040c82c0b10004145a4000700e1401c2c1e00759030031089651410351111241038000b0b42114001002d040c1540d206000340840c03000e0100c1c07010121070b014070b0f01e10f8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 369955422 1250 369954172 369954181
    0xa110f07080a090b0f2701140901091d04050106060807021b060c0a060c030b10050f03040309080d020319080609191508060118050405030d09050a08030a02070501060504150608 77
    0x26818482c94010700c00c1c9943c0412198801d8940000030911995206806d40400b4040404000310f843d070048100d010804050740d0400034011a40580a600c1c8145420883e01e0707503461440c040e041990302e1031150140c40d2030410040c45000d00420005100901c2c0003203081c905030307400035240c141c03140ea0005108071a81da18105555a0029101102c5401080e42d2240007645410401800280c540704046403c1581c04049440c0280c560313010360345640c03a8946800c260f869210201da1000b4070484c14403411110100e0b052400f000b40d401c0f503145507001103030740b1960b03a4140072807081114034090400c0109001c01c80aa168908610f4201f9840f041d10031040c038036184654058400b04d0880140c480210000059001c00060900e0499101c60403a00e02d41040c80c014801f0f44000322400b50542e40f00f040f02c50f030003e4041d8000042ca038014403d4441c0b001d050382d2110070781d902c160351022a480e000705907035041c0b08080c49510001d110071501040002c14240d4080380d000c005118100621041c0d00028 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 369956672 1250 369955422 369955427
    0x2090406110904050901020a02010b0901050109090e010f020c060a050f040c050405190e1e120301121104150e06100e010e13060e10170601031e020d03080a110f07080a 73
    0x8501040c40200140000d1a1178950b4a0003500072081c04e800540c03c04d2000c0c1e2845c2044070544d070689006035140382c029800d1420f88406816203401c140d82c40c0d03507184c90114440000348060800c420b00880a07007924204007464005850000c3c01070100700070003005120014a1905504003101d800b41d8021602c1d46d45e40f20700c4035000072401c988107505424074891030684400411034161000100040d1050040340889a0307580b128031070327482001d1070b0080006020702200f0312083c07480c0c64418180d00092042c141e011030306941c42071400c000c4140c000c00c010f000f03110301030340345035808002900e01d115040b48100f0002c0c81c402446503000d0520542d00f42c1007905403525040780f42c07051481c1c0d4003400481d5664459664062040390004401070801d10046005050050400b1003400c0c2c5070001e004603402c40d00c0d410303854051080e0710761b10100340c0940c0100503282d1103801030499020fa240e000300d07860912402800e0f0b0b9102401007079111810011092022011000d8454898128600581b074010b1740740203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 369957922 1250 369956672 369956677
    0xc02100e15030a060602031314030a1403030f25120f05090307060b010906020601140a031e06060b093304030f02040b0f1021090c080c0603040209040611 67
    0x55034002510311030711403505408400a50040f5090201044401c0c0d82e094101d0302c074001d42c0d200c40340d800c2a8002c01c01046034044100b24005000509076411940d9964038203040300c019140950240d04003104100cac07120001620b441d807111100c100d4540402c11101040b10705a1f074151282d06120550311183c0b070304030407580110240036200e50204040d04000510301e54030f80285608845d0302e8102920888207500c155801c0d011a00150018601a4203040580d140400d0103040700d44c01544900000003c41c0c1c3c05a5001c0d040c3c803d07002c5501c4410001d00340002a1202500200032802040048d200785446411f5554503404050403130f500410060320f20701121038107005088071050070214010081c4201c1c102011030340d0340308a1701013103d04248000c0c020700c03912540c044c81c1d101003110640d2041c1030003080c85903001131400003a581850440800c13041140c0600e141910349420441c024801307508100400c2449080403107501d4154070f041c1c2d0000d0900d100c01400101581e803144c441107100c4040c1d03401d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 369959172 1250 369957922 369957947
    0x5030403080a180321021c0509032802060703111602180115030b0405130b04020d0203071502210a11010b0405010b2505062a040816060801060c0210 65
    0x800d9041c0429030034010f22080c1618603085600c1c0c2145c1c00070384404094421076011101c1d4414440800402c80e480d0801420000c1405c1901e020420140030940040c2c0140340f41d000d00e44201d00f656000c100c00081c07804074020184400e2600d40a00284600c01d00340980704018561052040d030000795201003201038110300052081c1000c5c1000200d00d082415400801021042c1c1c2d040040014541c10002036800a84c5c01e1031443c00140c001401085c40130400a0744036001400c9107010203c1903010910305510b90b4080082020320300c0d0b4203003a15605004002c00440080006d00400140d00850207031031051103844420311070803100f81400e11800b901b0042022100800c108403075a511403030404907030f00c101e4161440342783c03018858000250000550341010b4008005280170340d20910500d05207001c02c110404070f45151000080401c450340d0040c00900100c102519203c074a000000d9400319040d000b00d000e015120b0018072001d030780400c5003410550100c91a481c00d14070204162400c901105 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 369960422 1250 369959172 369959201
    0x90902030705060307080619030b0a0f1503080a0311030f0c090a0306020f03010f120323070209130201030b12060705211501020601090b01090b0c151005100c0305030403080a 76
    0x20401505c541c0100703c141c401c6006031611180380b01f80d10300d402601109408000d208280141c04692070081c3c2d5409800c0001900c44009400d00070480700c2c3c05040103550080b500d07010f0020300c181c40594940036000d81c0381c200130002030440c105456401e6000100900030b00c0e008102045544980c0d59500c8404000c5030090b204660b280c0c0d4103000740100c0e81c424091081107c41403a400205840e40c813200448554155440c860808460181417030103481d55482d000d0081024005100540d40b8416070074000c10403004c40500040ea54400581980c3e004034207148a000c82d10f640d4144820045032803903002c8842d20300346581c3c0111440b21452818050140424256170764108030115004c0c40006101c8903090302112101d80c1d0b2040414160346025958a00141c8111002c0020340319103005000d03103401007025141c11900b440c003c0112500101c4040032000f000100c10425030520f4441a0b0111000d4600300490080b039440c0600381d803201510003000c21115900041c1c805100e50f100d01c10b840c40d0701 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 369961672 1250 369960422 369960427
    0x2090d0b04032006060901060c030f120605040c0201050a0506040c0503040b040302011d0c13020306101b06091a070302032707080303070309050f0f07231f0e0102010c0909090203070506 81
    0x11811076407814105c0d0694014070050001085480c0290380c8001840c0d8183e030b50780f144401d001011110000c1022045003450b4032040c1c0410710b55540d002c0d0002254150b400020503182411454060711800784c003860042e4648240041c01507070010490364025002103074098182c5480c54200c0c01000355501c00d4074944168007420101900110f01048120300484809230340c013000400e030f034040b807100350fa10302e50200b0440000d01142e070080c141e80303003070b00c0d848103031191240c3d13541d2a2281a1004500101c2d500d82105d46031103960358140140d103800101529003141035103080c3c0d4140179801d1a120f030402c0409020001024112402c0116202404030380301902d442c1e0070881c2c0c0260142c00010b84c101d40318010416441c4001c9800568000d00e0904400109103180c03074121000e03000c0500144501070304980c3c541030036407615000803250400e0016170456030001c4602c1c100401080c0401245030440e4140519030f04942d900c1118582920781c40c51002840c203030b0724400607280c107405a100d1034011a01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 369962922 1250 369961672 369961727
    0x604022112031501030605010815011715150306100e0310090506090f01110406230f250b011a07020424060f0207150c1b05040c0302090d0b0403 63
    0x9400518003030700c8841011043d440000c001034050310450300410780000c5540002a2140040303021513028440c0c10b042c419590301c40b40000b00e01c400004c1300c1c9c40c25040501d03410180d0030300b0704403580d44c1000c2000c6401811070505000007802441d807110090304000c0090304207006503605000045848049a4040205040038135006071a900101c0d52401c460244691441041c0d4041c01006404020910814900360900d03000b62020000c1021540340c0c40158100d540d01414040000c25048459000300d0784c03034016030b440719070122902c424403900d104c41811190002034200c0440d98196040c00b000d2042d01c0c1003181d07801d8a01d01500320040e42c4141815080a07140a901900745070960100101c0c031402501d90105541d400101448a030050340054010098140001c00340c0440200d689403c581b02c240c01d46456007075a0210000c0706441101d81030070070661030180700e02c1400c04a0f60405500308012040090555244451301808400701d9000080805224032240c001010034400d451030012903 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 369964028 1106 369962922 369962953
    0x307030213020a1b0503030916060e130b04060306050603120a050304030815060f0c0606030115120804050a120302100908040302010e180c1c0207030206040221 70
    0x244101d018101800300c043c081c04c00b034010001103459051401c07089040c400f507036860511811200c1420450590403120000c12007608440303010207900c0c401801c07030251500c044666070241c5412004810044035501441c010041607007115038500306600306803054800c9002d1200410320500c00580064459810319a00081c8410391088141c2d20ba00800c1c440d03007141c040d075082d00c000070031000c821440400010754404400c0703000344050701c1482e1000e40c1400b0350303000d12381c488540f05452409001d40c02d012a8000c2c1030181605541650380c0800c1c10300c25a000004a0041c040e02400c202030a1aa00840400703d410401c21441c051441d4015542d42c1c4600d078001d5001031902c5420744c04080f04503403051042040d031040300e0380c900898100b4405203201403000d08a89206000010110751300140e000d42c4503506954038155044c0e1305401c04c0c803182d20580c053f092841082040e04900c0c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 369784172 369964028 := by
  have h0 := BRFrame.cov_init 369784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 369784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 369784172 ≤ n) (h2 : n < 369964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
