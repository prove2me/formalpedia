-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1946
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:15:35.488475+00:00
-- url     : https://prove2.me/submissions/bc224a4e-09fa-4c16-8f4b-0332e713d834

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 349820143 ≤ n < 350000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 349821393 1250 349820143 349820197
    0x2070c0915090615110d0e0f1903080a080c1603030b0d0b0703060e06042d0e030301080a0204140403020a020d3807020d02151e0c1b01020306060d02030c 67
    0x548190401d0303480300e00b2a0301d00c0340702954a41240c0e103103280002c4c1f56100302e4022481c281c034034024a10030180a4029590100003014201c2615400a46081a0204840740d51580c00b080031039110318520305190078201d80d1080315030b181d59080e41c02401e150311200b13448890307294040c00e42c0c015034000d6490191410228000340081000d8013400c0c1681c0c0046000840750709150003a1004080d0707011411388407001440014180048000d04400c0e41612812a4031802600300f0165020381641000b510303840c059441080212420710301025281c01e4280c0030000429000314103a106283c040c0e6210324580390b81d03e80300c5d180180041d0792010070009001c415011007030003204c0850284504595028070303150083d040e6550015000c0090050f404400140c04640c0c8030400709400c80070014448003251440f2008104148040342d111004034000301c0c540d0b8a40480c152075402d03003034030000210700d1420030700045041c0340300c2d082402c03c4c110340010111344034403402c00440e2040740001005880586001c210 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 349822643 1250 349821393 349821419
    0xe01031e080a110d11100b04090f12020601060206070f1107091503030806040203010b160309050a030312230106140c1203092404030c110a030507060f0302070c09150906 74
    0x948025032084a040c413445500640318084082d0982c00203291041002e11004058200030403415002902d82c10308200298803181e03002d2215210b1042c080c4200c0031204000e141c900d059201204551002c4140301049402c141c2c0b00c0e100e0032003841e003014aa47c00503051841c01d1140d42c415220700745407209880c2c01c038110010f8030054910039520101252140c00820060f03010038020103c10709020082c0003001004048001e080310f1290a12200044c0e6075800120340362a1607004ad00030400880460301400c00034414274105103e40f034640c0d10007541810650140d200140144401e03c0711f54650b009000710220291038803043d012084130228840705180e07050030341007515030b000d15108404600b0a010050540740341c801c4030030040c501055550b9107041b948030303203500703010b032202c51440040102da91920b100100185000784004c01030b262400c20300414004000340c8910406106120f8030380041c0f5010524009c8600c0001d01103109003d10011f00c06080c1d007541704c45600d620b042c5002800710005e00c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 349823893 1250 349822643 349822667
    0xf020d0e010f021e16171b010c050708010902040c0309030f1b21170103080913020c2a030708060c0f090a06090603060e070c0b070e100314060a0e01031e080a 69
    0x400c05034581c1e20a0b83c8401d003500380304400003c0d001f1803190b609003890000304541000c414541140c0040c260746540342410001c5d085504145d445002c15410340c2004d02504110700d00a1804011110064500610602c1c0e0148030000300000c10030f1103800240500803140d000c5d074010b2840e6008001d070703190a001c100500302030781c004260303100400318240150100060489e07030441e4002e841e0542003010050070b0000000c442284950a002110b00c541003001030682546031000703022100c21104c0d02c0c0340c42d003200c000d064a00c00d034425201401000d02c0407400ca90400c0761070442a48805056232134600b54050020081e40203490070400007051940310070900d0403540c00d03440070080140c8800c00890368101c03c840050204001d44a61800600340c2107186520070482d00d8408034212030100002c0030711078580d05500000780c60703c0c401c8200641c8142003507040581141c1c6100340c58a890a039440c4900148009040c20961440f06103040000310704228405c0c0d0310211090341c1d480900c0d0003400c01d248400d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 349825143 1250 349823893 349823923
    0x31506030506030d020a031b020d0c0b0304032c06180d081b010605060306014d0c01020d05280903120305010b09060a020a02040515010f020d0e010f021e 67
    0x34070451321007400410440800c40d00766950400220307c3e1900c3c0c07a4912803d690407600401440c01510204900b00302c000080c200b000250360340c80c100703421b000b0042800d60312810002c000110020303140c40b4885800300c0030394406136280e40d00c0741156004e040e800c4442075040380e004690300744158204110000140202280b8100d01c1c1000c440c06c000070ba0888860b4001c0e44e4100c9070810110358290700030304070030503000c882189103010800383c0f0820f041c0d4031103000309200e0314804076242201d050750f030310700e40042003404074005002041001c030000703507240c00051074a000d0042c0040d4407040d895403040c48031100d00704803040d00313150703e41d03140e00801c5a00c151205030340c90507000c1c4041d40c2c43d07442405514122a512a120f5050400001c10807006a01c140d0340b5030103512a00c800400181c4890042e1441541040c906905280014002401c06494501c001045400a501a85555030001c507081110b45007842d00c6050030000401c140c3c50158152540c004510564502c84510030300044c005d80c102200d6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 349826393 1250 349825143 349825153
    0x60d06150e150d090501060f0f05041103070302070c081b040b030c03060604110903060c0d052208130909060621150b0103180b010302041107020f090703150603050603 73
    0x121084580c1001500700e642d01002c000204900c0007201c80141c60400b150340c100240600f219512142103442e00c0c0d004407074a42444a0800480e91062032650040c00c0c01c0c0c030107100e0203101760701d0140b06110050010043c540d02290490510448240c188054050310f012a450804038101844803e01c003604224800c42c18060005c0d441d0030040b40d601c5480034042c00808091311151b0800c005040c8005038141205c01c2441010140d68040209a000d510880022a500c1034101d1203681a110000d0200300b00c615012665565100d011000b404940e41105046840b40d11100c600706420071980d020701002030078904003c0611650350b20200464200460f03140d0403031250b10314007000c03005600b805040721045007048111103085402070880e03108145000104010008a100031640401c0c030281c409501c00030040c005c6041070300c82c0f1080100154041d0741400c5203540001e01340310050155901580e91840403a1130030b4080d4100c0201c104100000c540c0b100e0321140020002d2100b224603e210f0b00c60 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 349827643 1250 349826393 349826429
    0x30501050406150f201509060a02090a031209031a15220504050a080c031806031603020d1e0207020108060f01050318210a031a090a0902040605060d06 66
    0xf84000c0030303400009440745080300205080a40d0a00340c00c1540c03824081c13079802c1a101c40c80b010b0210624001c089003503843e05041280410b460000010b1a048540703104012404031540d0b1003a4900450740d106a00c031202601450085803910140c0c0d10040c90070503028183c07218680045441b9200341e1030704046080403a503545c02c000b174446450f170003c0301c0c04100718015641b614864110b40c5d40180110102c0c0c200e5100c036a980c020710307840740d0040e02072a000030403104041c081c101030390100b01c10119005030943c241500103016002c05c80c02030406150f800602d01809010301d130000c1011084c415040c4001040c12202013001e503002080490000b025203000480b07074600700381c00302020075041c0e403054110340c0da4010164890b585110b440495100d5209103ca0a08401c26044a0b902e080c4840ba07446038030070000901600c0b030302d1041c0c1c0199010140c0c641c40503100c010a0b140c1c05402c200c004181c044150005c24018202c5800c010b8028400090802003003401d0342000c000c492144d900040340000c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 349828893 1250 349827643 349827659
    0x40501120605100c060605060a0f021516030905100e07060f1b0b09031605010212130f08030703090516030c1a030c07080d0207050c030709020a050306060a020a080a030501050406 78
    0x1428010b0aa01080120545400c03501c5050a440d1039881004002885034907400003450b20b4200811b103000040520380060311035981400900b9a0310100d4003505903e0811481e10905540c42855083c10190390b9440780e400d1010402000c10b0003000e00c00c0411110080350910354698031280a10408640708854042c42c85105060f8980c4c030039201c4a07081c0440301941d95000c0044000790104040d44400c0c40000360003440c070940345c0c00350b070312403000180c0c4e9503c000040c0700045001045180d4240010701c00001040c004040f03200616440110280c2da940e401c24194018000c122000e82076200c1c22240074111481c2080c86400d0702e01840c031245002c2d070303903825a4415064202d008100600248007207200750030304102901c0b0451080c0071041c1000030281c0d210b0201c1e080120709581d40d60080d0100c1040c2d05080c88418040e0a40110a52503c2c09d0004050050311014040c40d00642c00000e983e01c0c0b003031080c04084119648044c050355034980710302004020701001e004041c482c520709400022000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 349830143 1250 349828893 349828901
    0x12140403031b0804140a0203060703022a0c040b0a0b0c3a0311120a15060201020c03070308040f0606030b0108010e03090a0501180f0b1818040b07020111040b04050112 73
    0xc4850fa0b07400815912542c1c0d1145d0110040d00b00c4110340703d2030a0030350040c0d4090152602c103004a40c0c00584940c02c44200c1d80f8000c074080c030140908140d0101c1e4140310305001c03a03e0062010281d074007044840304031000c18450f00c0d495000c1d00c4011000710301500d1540010401c01c2100c60320880d19681c03c1508102074014000300c11449803098214080150303001c0c0260008224020031880107410502c0d00d01c03010803260801c652511050350707602094100461b0b1194400c0140045100031410507840c4061a91f89103e1100050140401c0c140020100032204102c000041d03030244052214541d04e1804c1c2204490a000301d041650812180c40290b40c400401d40b00150301c02844a10400d01e0000151a02000b4441c10b442000d007108000c03d065014140d11300c010404141101d030380f20241100c08040d0300c949040c191244040388020f41c0d01c4c41d020401e6942264100311245181d481e01c150682c014030b00c0920b41c0b0a049404680000c42801d408090001c884003a22030034011400240741070111 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 349831393 1250 349830143 349830191
    0x50a06060806010804080c030a05040603180b130507030f03050c24040605150d051c0e09010b2109160602060702100509030f0f0325080114011214040303 67
    0x1d081040015403e62042c404c0e950410701507180c491410090540480c20341c1d100942500c00b0800000c1c0400c40c00d40c4c188129140110700518450300380c001582c07078041802c0701070508589181c174003d0504c180041408040000c5500041da1240c0c0c2040e0320300500190002c01d80070200e0700440440c80301d000b00640c500d0320790512401154100b6900d40d622940208405885442c503008103002c00b101c03a440c1c5010851066000718001e10032110620070381c00380110718080301400c10440520060345610740c800c4480c107541e401080a80c654901d0400c00d5090480c110110001c59010401e0050751500400c821980241c14415442c0c0103882e01c10a84e606c41060341c1e44030040e4044414425440f103250b010079086001e0006491401c03011022101f00c9e6000341516040070b020000a1002c006100e001600c0158100042d07042980c1090001815001d41446807012513040030040c12071503880b90240c40941c4420000170840c5ea1840480f1600254044404802003880e0855480300050400790784600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 349832643 1250 349831393 349831397
    0xf0501020303070f080a090f051b0f0a0e13080d02030106030b0603040b0a0c050c010f0b09090c01020d2303071707050c071403070b030c0c21120907091806050a0606 72
    0x10184d00e9050440300d600000b0308111100d56904041c0c000604d025240290650190005010b1b08855045903c0d107452150310321840742c09080c2c0081c0307840d101c0c641c4920441e880ea50300602542d50390b02c01d000d103408900c3c200a00351100040c0c40511506240c3c040e42c181d460980c0e041101e40c0c450400e10125100035500038003945100000200d01d4249038001c0e6040081601d49036060200315590182510707814842c2080041d1100c01010150a050220f681e0241c09500203001c0c07a0742080020f9261214900d140d010048102080d0340b1510480c030030f0045094100d0309088e0380e46003024009007614045102c40c003031072468a02048005118805988280b02c1840280031110314110702216401c0d00309540c07e8160207503410014548660401a52040903900182c5540e103031103250075824450b14130124600e10456080320f0f440d40701c1c500c2c02d42e11001c3e00071f1038400d03041d00d401022601c1c11101c3c0d4040072080342490b90440904090150004030307a4800c0b90148982e440390704001e02600c0c90b6000e0300780 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 349833893 1250 349832643 349832657
    0x1c0b01050403080a0905040203090a0b0c070b0f151302030901050a0509030d2301080d090614030c0903010e0601140114030408091012090f0b160903061d060a060f050102030307 77
    0x115410f18002c0003d07415608010000694502c0890143d8200f265038822513004031300c00c54203001c40aa8907a03444050445501d10300300003582c64420140000e01000c5452000340f0009400e03030440a11825a0340300149444000c8140412000c0658401c8400309810750030200480d2583ca528020381d4040c3c18454003440c2003051300c100200040c025a01c0300200a100c14450440c0b60440c140e070540a04a00409071080031803040010744902c01e01d81c00a01007208521020030b0081c0d01c0d030b0640350040401d54286540706c05660000b0301410303180142200314000c501c000030ba0102543c0020794101420707264444017203000600b00005000440c0e0113005c8150400180780c07a450301682c4507011100505091404044100c0a00121052400202e411400f244600d2051200b898103507903001e040048040d4075400180802401514036200062407551034081544018540c071040d00c0c000f0801c2c204442091034600030210261449202e03109214020746004180c5520100803244900f0064403110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 349835143 1250 349833893 349833899
    0xf0a0c080c0d08090a0f09020903010b0907080103030c0f05030a0e130b0102070b031e090604060b090601170403031e0605040606080405071710020a0c050c1f0302030c040b0f1c0b010504 81
    0x84950b600c200a130b02e9103c10151070104d00150032801c200054902c0b614010384910941e0103160031144001c0c1d105210b41002c20030070280680c0301003210305407a8180b420681d0b000f19494a0000e1841c0d164006050340000704d00c160805074407940701c06000004442056507424032900000c102d4200912031401600207400c180040203004004541010480003062607881400e21100c2c00c1e142d094501d80901d03001041804103002441c082c6524018084842082500780140040c0c01c6c0741005180240f402c40359030000d810b040c007907400000315501780d50000295074120810040109424011648900d24100c40403810610a006135841241c0c0240103008070380c1002480c80280c029107804c21510300c9101e00c1002501d050340040c00a800b800c1d100c005206080e49800f82c1000600c0d0020381c0078541c5006203203000440c2a40c6100d00e07040038100182d6a45416111841a02c110b40100e07030510000640207e141e011301d4010300c02c10a01c00004110b0860895040d426500c0452949001640c180418 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 349836393 1250 349835143 349835153
    0x50a05010909201303030e0616060b0102010902030d180812030f28020403031b0c14060909010323060c0904021c1505030c03070e0403051303050f0a0c080c0d 69
    0x1c00503d07140010400c0101c100140301c40480e600001c04049040e020348030030010160482540708020100f03c425a050005c051424000340e268400b02801da162100302100e80c0b0790013984800c160503000340c00e9905002d9051806851500720641c80504040c1403980058103640102d0b408240d118100003a610319103401c00c50072007402024040008008986250a07089052820b544c4545a9400c0026072075902d5400d014180342050308000801610601c100c20025088070051000c2d40d42c40103c7c502031a000c600894554010300360148d400404000001c410b000d240e15900403107490207040010701c12554800152100416514445480d406020020403880d091300907208040d0881138000491031249005015201e0707176a10740b9008100c01d00c0c24085070805121103030b1100d00036002000c044d40b6144075840550001000501001004500303d407500f00c885800d01c00540d002000c840c0c040d4030080d80b454a03140c43c10710486442c00c0300c00c0d001510f0903001c0307030003000740710000c000e00c8445141f5295 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 349837643 1250 349836393 349836401
    0x7090e0402030a0b1902040f0e01080a03020d1404090e0715020d021506041b0e030c0f06040e100302030f0c03150903070f060e03040305010b03010e121e160f020a050a05010909 77
    0x1200c010305d001c10310034100d138540038800f50000b000b030382d00001c03d00d07031404106102040c4181c010340d1150300300c00400c10110b600003501114840c4c9503d0840b080504020403610f06005a8205255580c2040f58100c501280007aa050644075030313010f103081c0500203900030b99407011849017007009600240c050250540003004582d6115001500114019450100810354031080e002b10171b002c00c00031402c103c0c1509040000c0da560711010740c1c82d401c1840e45040001c035280507910030400d080101200082014030001e0b4110011607001e01200c0d003400107003070f005844002c120200c5000344100060341c01d10403960201e85020725500b0021b5840c201035030719441c2201140110a980e0185c8402d8840c031107d00c200001c0000714066000020340c1c0c02e8460405082d075204802e078544607480070300084400390044c0d003160428940300600003079071010303104d400c40b282c050201d004d01d4495407490103106200c10002c1e40c943c0740703100f101c881c2a543e440701e082240c840d405000303950014000303c809000002d0b0584c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 349838893 1250 349837643 349837651
    0xa0306142205070201110c01240f1205010f05010e0a05060d0b060409061d0304060314060901050d210507060c0c0b150a0803033111010c080d0501030b07090e0402030a0b 74
    0xc00451543d031b5151040c10715501074014600f00303a543d150b924620081c604e488841c04000c4c810001c5416103001c00f140c0445c400d03405030b020032009100d0301c6001c06ca001d6010b0000b40c00c8900040c041c5694070b0400c0b04041000f02d6605003903034280b100040040c030303160701002210740c0d1003406400943c950206020007025042011501b180d682d1080d107500b2403c802841809600183c01580e84a041590040c1618444070f003401c02c684201c4103110307003542c8440220f41910001e550440e58551141007610f0540000c3c0d0b40c1c0150a100300105454242d409401032202501459041c01041000c0c0c03c00c07240b00c12141000f1f0320140480020548491000d4511290303690001c1060310000d4a448545065074410f86802e9200610a28551300111084401c0c420004078180c0710415400903071100c4001040380800e082c10010758404000420680d8401c3e5070b50600c0c407440c00c0116686078504050040c0080c5c6801012601040002446604a508a40c440c1e5130250142400625036960070b03d83d148084c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 349840143 1250 349838893 349838897
    0x20c031c020c0715030b1c020603040510050a0603111914061c020d150605070b1909050d03050a150302151b0a060b01050c030a11120a030614220507 65
    0x2c401407002d401008140040c04102c40307603010404404102804860803040090b0260120710f800c81520121103001c0b042864040e40c81656942d01ca00d051030501d5042c0949a01346072608090100d4022198000000c0d240b00303000d200c3c0c09820001c00c01525160324100c0c24a2080461414082409800c1401d0503c4101511540c240420b00000009860600c0603520585a01141806c00a80c3c4c0380650b4200c4000e20461428060410100405074401c1034406050252044085040b104000000800114001004200302c08540c504151a100d1920070000000e04010100d001c0c42d00a2160501c40c01103001d030a00341620315070034081e01c1c134170340b03030010400b180c0c140410000c404061403802091401c80e00585500442440e150003201c41e070501f41d5040020922050300b015000208482980c2c84074280481782400045080389000c0c1200c0c078461403804007140c955070383c41e09500b00d902941c240e00d0400e116003101d80244202328441c05012542801c141010b00d00b0601207511103074101d102c0d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 349841393 1250 349840143 349840147
    0x7110d0c08070311040f06081504020102030d111b1209043308150c03070804020d120903060608030906070b09010f06030812071809330e0703020c031c02 67
    0x2480c038071400c0030342543c4281c91040b40c500f0b031000640f6107031144094041c28980c1c00c100842c01c2504165581c59504d20301100510031030b000c1001d5a00800c2a207a1580c102c440601082200030210441034000349240301d8454180d4020328022440030881500c02502041c1281c180060b0b1020030018100304c2c0541c032203081c008030401801541e500840e0382c00c2c6c02025560b0451510f03015406140c4100304c0707840b6003201d000c841800b10340300c5d407001165002340045c81d0038015900d8078000500703010905400105805c0c0d00d404020041c60300003076000d084a02955013048502e50300d050040e180c3c815645503c1d4402010030502000501f0110307416049074000000041e051600040700c1c003102c030507030400d0b98a802c0105090080104d03032050700d90f00882524000c40841d203001c55150500001d03014080090b61212450403043d4400302100519540c00d80031103441314000b0094410480007030245030711110306903002400480c00b90080300d5901400c980118034084514040307500159211808402d03294007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 349842643 1250 349841393 349841399
    0x9160509130c11070801020901050409050a150602010b0102070806061008040c180b0f04090b0a2d0b180c0403110111031c0614060904020a05120103030f09090207110d0c 74
    0x205100e0320741600142e44070b0320844500d0a000a1138401568030540d0180e00400c40180f40e81d030701c40186c038206d07030740c8181c04617460f2107803240c81d0050541110300e01008400303030700c000a20f586d05400c01c0c0300c042400c2e001e8411054840103800d80715a022940d1607000071800403145c581900c104c01c4150320501030944800c8464486a00901c205940044800441e4071000064000d00d46000c4000c7e031602c04580c2040fa0101c969940f90420100804c0f50703504d2503660009100031140b428490b4844038001203c100c1d422642503051004140385031005000d00720524071500e50300601d14085010301d180c0c020450510345140d40305558800c040000760304201515a21100e091000c102800001c101c11038a00301c80306032802c0d003004480c40caa205504520480b02c52400395152001112110344042e50301503500c012524042d5503501c41c0011219440404000000070f15602c40030b000202589992450308084d51840c4100607030080900152500002480c0110f140ca00540240490392040341d0210b20250703 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 349843893 1250 349842643 349842679
    0x181d0a060321031413030e0103060902070609050c1014030604152904050a090e0c06040308210709140d060f06060908070609151209060204050f09160509 67
    0x101c0019007a0038210302d0b080c6080540c050048010110032140700741028074044281c1012541030240150038011400280e00c1c89901c00d8100ca4060804160195982c0700646090801001051015126402010611041e0746408000981c2c004001d0365a9003e900071003450110f41d5101401c40359119540725403000d115200e21201d0001040f0100c0b142403079807022455142c0d4174603d5080c2c05000e00f01008144110707030303d0702145003d0b2151000000307001001c41401c103141c64180303c0300070381c00200850000204150782008080c2046240481082c0045580c011002200240c031031030f0104d500e80000740802d01c0c1200b1200765403600142540c480b03c089032280012100c241c2d40f14400251502d4050020f00d40100380c03040209026001000b0842c5050300042c5040b0003401895400340c1c0828103901500d109800009010100c0d0340c3c00c101c00610341c6010b20003580b00d481018042c4540e18204030b00c0e480d046850034840c1007241400808101d080200310b840354080703401c10368898200460220514 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 349845143 1250 349843893 349843913
    0x13060305060a0506130501060503011a1204110114070f02060903010209130f0605030703050d140f120f060613060f0302160501050103170c0c0616050616181d0a0603 72
    0x2e28010001d824100306003480b5881c83e0f80c20300100c0003410240108a603d40c404103ca0450f283d400e02042c106400c000f800741548140f030300200703184c1c4010b828070060044e110f001510b950400d884903465139040c500d503141140500134016012a00040383c003000f40c145000100640306d0300a000501e08556140003031900c945240305000d00790340d2180d0020342c1c0c1c0c4891090300040d01c0c1c118000c2910301c0c91540c850f81e03a165a202e400007000418000f40d4001000402528814102e000c110380e00e07440b504910b80d4081c8400c5078010021210800843c1c1030b03041443c1164141030240100d4001141807600545401d0106179101d01095030803c03280400090a014000095102d000082803952641c10400710142a20900600343d400402c0800c0c02c2c80c0303001401544a5038296a860f8442000688246008404050140c92802902e0800803021158a07035001c0c4031150b511800c00c1c40000d0818150382486600406251018102c140340074142408030241e4006452207000c41c41d1900e03030740c03155108 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 349846393 1250 349845143 349845151
    0xf0903010f050a0b010504120212010b0a0e070909060602031902030d15050a1502030316120603060f0f0b010c02090a0e070314010515010804020d020a0f080d020c0303040308091306030506 82
    0x56582c80a0000c5400c0070301850200b200300f483c0003801c01d8100303400c0c4640c240c03504c000288039440c0c4007022600034000790061103921400030245482c80e955070a60030141d403012605000069580c400115181c0c2e07080c07040e01c0a0751013960007941401c2c0342c0b451080410140c1101081940f00c01d11054800604501595928004014900010910348018410480802d401642ea09080016401d039040c5d070000a40740d20020f4680c46201c2940c0c08102511100ca49100d0940c1b03007414100e012040c030000e6000b47e80b01c81c1c0c403031004200010601c1030500440e00344d649482c0c0060861a6410050714010341070980000540308002010081c00c4d1a040c035101c415801241c4408400c070300380600810a115a07540020300c0001c00a074007801c000000c01100c401080280301d10121024141035407140c1c9000380107809010598220b0303580310030540750b6803e0900d0103600141705005500d1031500303001c0b09807000c41c0d0f030040400d420103401400b00480f5100d081c051103800c954880300000820420080b040c06 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 349847643 1250 349846393 349846421
    0x803131a07110105090102030127021611011706030d12021606050906010618030803180105101403030c060a0914010203040b10320a0306060305100606110705060f090301 74
    0x885035610b250703900f50340008012102c564410302c010032144801240c603c902082d1141c1c4540c0d0142c0b0070715640001d0064401d031802c1005540c031194100481c00c0000c4500d242d0036203518800c40c48200c00000050421912250103070400e032502c41005004041c0603040070070866000d4140061954604003810b8912800c2d1002603c40080c0300d000e11040c00814003400041c94010420000401481c40d40310903840010a0307820000300040400f00219030b2203045203480710003031010b81042070050182100b907000391201c041d01c072260700500346400070403512030309062005003565070381325900781c1c0040c03071780043c140d44014210307a00c082d08103001c2c80158401c0e0701c0707021120014200150040c4c2c2d030207181c0d08080003c20194042015120350090450340c050500060079a1580078040803c0d81c130011603100406281c2815408820800c010954207424540700004129880d40c1c3c050855010071000c480541e1a00480720900190400800070001600e90f5210300d0b00d00003105001c20b0860b8010402100 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 349848893 1250 349847643 349847657
    0x5030a060e090d0908070602070b03040f32010903090e04110901030302070e130b04150608151602061003080a1404061d040608100e15040311010b09040803131a07 71
    0x6000350304241342c1c20182c100c10000340325043c286030001c0d540b0102c41c003d80842400c08030010f030030442c00100c14101e003a40100d038560403000280c0d88210a05402613004142241e10903042c980b9041403007690145034059442001103460002e404a100001400c1628800d0703850811070740302d48a41c807405008501c240d00034146c09152801800100c280903101283d1030711741505000114000c5030305140c2040d0080c1400308841c050210041c01045250301c4055030380250314414032901540c02d02c9611a04080d03040300300c000d0081d88103e0f202e54045071002c8a690240400f4000f0425030070182120000c00c0c00d002c2d0200702858050031b1207030000d5100000007030301c16074004070542c070410341c4510003441136506000944c1031004440d00d03240ca40310095402ea54a188000706a0001c1214420302a80341000c4821400c250800400c801038144800c9850340c00c00c84101000d0501408603403050350000c4000d070450300d45260704400040d240c2c4055404000b48001100488210078106000d40d1540d21804 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 349850143 1250 349848893 349848913
    0xe030703080a051b0406030e071505040810050f2d16120c050a050a0c06090b100e060a060c030309020a141306140f130501260309010c0305030a060e09 66
    0xb03007a01c200030a00304c1c507007210702d01c0b84080d02c1101040d64162030180c2400b103428180074110711f180c265245e20800306103203442100c0c2500c9800800400507540c902054030303e42200e00391700c00144c4405856921201a4040015001d25401e010b000b10505204c0da9000d030124010400300300c40c1409850210303032440010048140300340c11504807900c902d02c00c5401c3c0705507092418041c00900503c006034040c400000781f600403c0d8403a4081c4c95040782c5c0302e04100101020303401d10310740c3c00c0350485200c0d80ea40c40100c3d02250032244c006505100c1d40004000442e0a400c2640807118016503100c00c6007407640765070082e80180d80c0c41002c80c0280c00c0046046d01120b03825400c001000340740a500450301480d06409104140c80306461680c1d0300d030141d07900480b40e21f8000201c1c0072641e400403048a4141b40070004940200e402c1410030918907040400c1aa0540843d882a168440c10003854003041904d041c0c040024041c5026540c003644010000500940d2406040d85600040303070b4100e8a900541108 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 349851393 1250 349850143 349850161
    0x312101401082e080a05030c241b16030e041a010206181f020d1d0d11030d09030e0a080d08011205031c0b130218060705010e03070308 59
    0x1280d242400d2906008904107a5003c042481802403503071102c0c642c4008000402c0c140690310401404800308a4100b003649041c8152603030429082004540a400340410f19a2014104003015100c56a540111902c0f000360348290f03200000340b2000b0f084000e0002040c5119031000500750303030b1701a45844400302c1c01401000111424a14044440c12310503040f40c080ba64000303920765000011940c1e141c500b1250707040c190310b446408224214000e441c8006403410412035000b0708004041113900303120116a200c800340e0b100c0c01d100282c00319640030000e00f41d81784e4405c162254101c10500d003581c0c0781003010007041d419070701c030302d0401e501045065611921508103140c1c81c800904071000500f00102d103001d0f00611906040c81402001c5841402400c04d109040c0116038401041c4802000c0c3d591914004a02a1100d01d08c2144101c1c2c0031905010140001c0c000c4403d00aa00300c0e0b404a004210001c014071900070071000e0310250f5039004609100715080006100b101e000340c0760315030207180924003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 349852643 1250 349851393 349851419
    0xb01080708010b040512100c170901050106080f0717070e12070524040f12050d030c080a09080f030c1315140705010e10020301140306160809031210 65
    0x390410400000010030000d2490001d5030f0584900300c0f40d680c00040b0590740e4034605600c00100283e03443c41c1c4510502042e4206401200c050003003807803001c50399644030031b440c2220002d1082c00027240b05080081c400856104400b85d1199290508400010500000c1c1010400c01c43c4c0c5036011820707102c0c1440300b500c1c00b100c103001010135180040c040c1e07505080c00f103004911100c0fa5096900e5104101c504809501c1040e18098294140c0001103180c0d90182000f00e0918a85c1c1501c0740d004043c007440c1ea051090007026000901900c0c2c403a0103454103950031004288884007a100004244441300c004106100150701030030b44410300c2e5854000111241811404036442880c1c000801ca86503649aa04800c0001d000d2802c680e50a0700c0300000c0c01d002d80584140c6c002d07502d00d03008100d0700340407a04071a406181aa804007680207194881d59060640d202d0069800c5081d9181c46143e4213109403241c0f10180e0700034203200c240c83c2000c035150400c11030300d80103503003410000400e54800c1c4102855982c5c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 349853893 1250 349852643 349852651
    0x18080c0f0d0210050702010504150207031502070b07052d03090f0304030515150402071b05030109033e01020c0c010c0f020d02010339090303080c03130206070302010b0108 75
    0xc1285a0a600d50b0000310300000080080c402d02c1000f15050040d0ba0203141610020441c00910b4a01068a010000d4546002d4001140e0f010f01c90325030030500305900e100f610140b96104850720a5074070f540c1c1d801d130344981221410f8644480441080e0f940803003441110900e0080001e030450302d034108102c0542c00e04c00250010b18140c0e00a100420129000041a1a0200c141141e0080d591a0403201c083d0104078808100c1d0006c0c00010450b0401032110f41c1c04620503000d403080c00040c0d445d0010182681e034020000f400041446000c046004c00e8800311880000c11400100c001e0802140d40c24001c404134000c249407070358042100c49040800740300340c091541c070074030741100402c2d51642d41c0d00020352940341c040d0003002e40d076404108590083e40810302c0c400342c1181c01c0caa10020b295010f6250501e04000307198403000c1d1040c076414680603625030b006072070b03064075242a281c1d5015030046250b04002e01189214004800031303005a12190010040035010341e00210700025448000750179004094 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 349855143 1250 349853893 349853899
    0x320402210708040804170111070302030304230705120c04090c03061a010f0e0a1e0305010615080c0c071a030f0609070905010f0302040b21090c0901140118080c0f 71
    0x2c0104400104642d0403134007510703490180c090703804880c04a43c90042480841d90214541c0018000d02890340000285120b03e1090420008580070110140c3e0503107001510400f0a80c041031091046151841d100ea00c0d608421080382c03104800c2200140a91345840c0c030588502c00c04a0302803040c46028001c1c006840501c182c078507914549000020203103500180150f040007404100c02b03090340d80702202c41d0024000140303252600d04d58404908042031051204489962038200001000030600c0d081c840e051590781c6628910346d50320300e0344000035030001700710030180c0c040d1400100c0c08542ca20035074070150340d4000c92140c0300e1030700c0d50301d8001152000e060142b28103982d0081000c0c01c0d0384030351040280d5000f860840034088800340242d0283c0295000300c900301c0c2020944200d42c65404841d150244041c020b4401b40780c035500b40040e12810820401074003e180131005003c0c03145640500c444110040c03400300520144418900d140403c590006007440d0420f89518609142680000e400d1507011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 349856393 1250 349855143 349855157
    0x616060e062a0306030a0b04050f060f0709060e0d08091801150905040506030c0618040f0906060605070b06060319090c030c06090501050d0b03030405030a06140a063204022107 77
    0x1a20003c0c1d6209946c1c0001401c201c0c180b40054200081440201240001402125150b0410b41c02c01c0c1900c8030100d65000001d82e010a00040c85481040440108200505514518416a110125581e022007116a044074500040c011a200d54085e60f03802417a4040790442a04540e10000b002e19003144d201c0c0b4461814181802403640c0c01091402414104803125030362907104528229200714600c2030325520519290041e4840c0040e50451042a84941030811407103440700b0080d41c460040034000341413500030000050240c02c003030006503005200d445803584100b03100e007441c200b40c980440d0219510f60b0900c50030030400510700720b1070b0003400907070401288580c2003400080140c014a01d245482b035486404244481d181071089601034040a001d662501096051038805401d007440444107900c02e0100017540f10743c0a22800d8165240c55400c0100030542d1070607810954a400c2100b101500d190840c50142d55aa1008040c030320041d240555610903000081c1030744d04402400c4006100e04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 349857643 1250 349856393 349856401
    0x90c0901170d0c060b1002030318030f04060513050a0b0d05060406320306010e071805010e09040c09051008070812040e09100207060209030f0c0616060e062a03 70
    0x802e00410440040c90880a1400103042c07050107459074103035854201410080c45038500b54044021442141035010f1140e0340c40405d41500c0e528400d5090700c0d400030005000511a46205034002c0529041480c030040109413100000f506829036540588650340002030701c05601c80c07450052550001d0b003242c0810001385031aa04003140000044a1001c5404145284031030420305800b909201001804841c40b940c0c683e0111021042c00381d401d40f0206040f800001c2151241601c890265207041e901c14800d10445010710401420284c421a03980c54032407004141020244600c61281801200041081d46061182030910702942c00401050300680301392921a9845422103044525844089420381c1da401141800c01d0080c405040c811400010041c0c24041c1c03640180207000c400314107441c441c460703601d10b56030340f10760880000360055014040803800301440c05040d42d65502440d40880c49078600700c5414203045045031480e40c600740441d85051009441400c00561282c4090071030f181d824 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 349858893 1250 349857643 349857689
    0x250306080d0507060603060c0c0507090603050a0303050702010e011e0b040203040b16020307080d020a0305060102190b070309020307093e090d02030a0f020118032a0806090c0901 78
    0x5070401c040d00744940000c0c0d0b80100441c0b90310480003140c2141d000c10041c290014000c1c5120300340601074940e44140d48010401c0c0c1c0c07451040c901243c1d40a401032884070780380e03a4194060b040c010451402c2d55a58a4001c0c001c810a000d20700d49007074012110020701103404003d0045461000300d45005501c10b00400000a000361000341d008a2a500d608400038003202c02285107110350b40c0b00400441c030214403107a128031190003401d1035100c1038138280003903650580126660b0507003900315500400d0f03040c3c2c0c8030b0214217031100c07654001c1c1d45441c001c20010000d8000c03c4c41c00c41c4a0b803003544c00710b44c1d8008003c960160300072107013440c0c03000341e0040d0004031812000401c07030b11020000070610480001c811406540c0c00e2682c02e14a0707405015100c4c00d80903403d081d404000c1049060780440c92303507d4031000d0017512000f10f400f075136032001400c107020400c2040c0f0524610146465000c641c0c09540104500d0403c0010074420b020700700c000c107214803c04040c0098810182d0100810b000104a1240585 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 349860143 1250 349858893 349858903
    0x1406040209010906211403040603020c0c090601050a032c160b040602030a08060d0b0a0905010609050717150405010e16050f0a120603080a05040914011d0c04090525030608 75
    0x2681e401c0c03a401e100e51410146c00e80030b007810070201c682c440001c0005940d40c040e005048030303e005500796200700e040c1c034084c00784500d0200c4074140010304c2008124000380c082c0d80300340c80201111002802a9104d0b0100c005a040c14404910503a8000c0303142e10381d031800c04032080340a0441c100e402e9080518044010755240540f0000b041407242c9600000e8a40d2160002c40520039040140b00700b1031b04020382e020000b09640f40007615154205500401d000b41103000300390040840f1380d91280d1000300c01c1030a607600300000c0c00580d80260f0308030011409542c0c0e80a114080e00145800c041c980c00d1401500700f410b800440301400b4040d082c40011a806036800550341e001185090072007000c00016820002414640c03c01000f00390089003090a49a0003805401954008070040290019034001c001108409210708210f84140721940905038141c0b20146410038400248203041c070382c6900c80c000907140215010b020360b00240f03100c00c04281c01a030800d103100c440381c1010046a03040c901ca81e40c0315 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 349861393 1250 349860143 349860179
    0x604060f0509040f090b07020a020a09020703021905030a08090607120513020409050102180105030f010308090d0501060603140c0309072309100302042702090c04031406040209010906 80
    0x8041041140030240340900700301d4200800003002004440f80420400c1c00801d82114141c82e407039003a80018202e28000100781c0003c54001740609042c62400d0100c00103580440700840440c051340100d055404110f80241d901984100041c5443d07a00303c3c8001403110000074136a032180d50006e81401143c0740c10540740e40010f600e0050200f010f0ba2444101d40203801d03410301c0250031915112071a0107002040d4081d091085109600314805646000112400d000070788001c10020790b00401000002d0181c2c004024074040070f0200311004c40c158940600f140d0030341e40004042519800b1048191410240f000c0d0710400300040d5509500340045803136a54825801605a00c2c01140f4100c801501c1a00343d03507003940b00c018680481031801c8100c21407031030514801240120308084d2030041c110280400514110112030340d4010f82e40c00c3d0740070041051405405000252410000400803030b00d21400c26040200321740003003103a41020300c10b02c030f05800143c6c86162001e01d064405c5c007040344c0441044081e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 349862643 1250 349861393 349861397
    0x30411061206010e0a0b07050610050a03030207051903081201060905010c110108040503040504020f0408010b0303041206051f0b091503071b02061b06040c0603090c030201030515060f0c100902060406 87
    0xa03442c000080f50a0920341c1c0c0160b14600c00224a140c02c002c1d002130f00c1413040420704052b001903985d0b0028001da00e41c90313000050150300403880622076800c005600d1020350081c02d030b2940c003440c2e80e0b440b10303d000d61000041d0184d01900d50700510400d504141041e0080c0020320380382955440c80e0311024018400039007251304000c0035001280a1000070005d403406407000400855a03030715102c030220a90b500501c0740198550030b0454804051401005503000c441c0200b4000040070015580c2c07000604000b0060048524014018510104108441e00103071001000d000c2d41e0750002c8041080e503003400100c0c2c4074a0981082007040242e8030922a00300ba002c02100d000c6450b00a200007115409081c16040c11b440c00c1c0340108500d100d00283c000e0080340074180a0080540f540b170101d0546044e881c024220810b41401007006511940c4815031250030401c02911500d2412b00046441c0c1c00080448944d4001040e003030710491081c4082203210014680c01c10401005501240542c003d40c403800007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 349863893 1250 349862643 349862657
    0x130b07062009060904090602161a09030301170708010f02070203010b0904080d0b030102070506040b1e01030302030406120914060a0617070902070f0b070527033f03041106120601 78
    0x815170719144c000542c6c0642c0b021096440d640429011601e007010408195003c036100140c107401000c810060902541c0141c01861550b0b0a000d0001949060403110350000c3c071407640001007590082c810240c003200e00c5500581d56001310300405003560581400984a80c0100092000044500e4104c82d12400c0d05080030a03101d0301e5100103070090080c40700c0542103025010401003080500c0842d18800c3c101203c0b2080000b802810501001c9424000103025900804c42400900c0c000c4c4010280010f1881c40070880c4845581d8250003140c29030300850440c0e2242c8140003d821240c05a00094004050f0006820034141851991407109120f18449503038005004414009141c0c8039805e400e0b04800c4c44001c41c209024001c00b43ea001c16120f0300b000d54042e045454011007440c00700e80070400100103043c1b50001c00654104c0400203900001050090600d0502c4685940107641080c4014035140c4d82303a00d0a4144200a02c20b034592461080b101007101c018000780c1783d40c6c41e540002003071038541 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 349865143 1250 349863893 349863907
    0x40e1b030a0c0311010206090303070e010e0604090f0507021b0f04090f0c0b0403021e0117180d0513060201020c06010905040f0c12032003070204090503130b0706200906 74
    0xe4208004040060060000888040140400c0c00a440c10154003a4200c13031079540e404030010b440f4001503a01000140500f1040d041b5580700316107003000203070010301440c9002c2d03640a2003000c41b0400100c0242040e19a0104040a501840001648083c4d04000c14421100e0000920540b185d9003800c0d200340e0742c8a0030141800030b44000e00c0e406a50050806000359241d50059186030460720003203100d469000c603420761841040300e01401c0701c807060b10f031a07460040074202e6100c03c440c014064480003100c1d23080c1e800c130300c40100710100414030725855032642c905941082c846c004c00745412080c103581c0100201101444c002500c40e0444801010000c0d060b200e9242544c0e2004452a000d484241c191a0120b559928204103c2c840c1c1e1103a1a48540b888100300035010911010580b181d9580051090b02d026003400e4000c804268814010350340f9010b844183e1f01840801904210380e001e90200d46034042000f14403448039402c08070819040c280034001d8110b0910702c501c10082d030081d02c000c84c2c86 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 349866393 1250 349865143 349865149
    0x1608030f0f04050324060f0f011b151e06030c12050c03010609021c0903050405010e040b0d082d03131407060e040c03060b0a1b0b24040e1b 61
    0x350b005030078000c059800000b4107425064039109215402c001005040012036414500840f54451300900a00699001c0b0516801550506000d0800a1401c215044c2034070000302d0740075030340c81240303554000003c0040095650050346102080c6c0b03000d07078916000c000c1c4042007144024100b102c0038120850190203551074203074288000301d0301c07070358166083c00b40205c0c130160340344c014084001c0741170123400802d4103c030030890581d602e03500080d0105408110911195108402c1d521400102400210304004854041985d0300360118042c0d50343e05010460b41c40c0c0b0306c0d40c408206045040c1d074420064009a0406a03241d61001804003c920003120501904220000c10303201c14001d112015500085e0740d440c005468030103000c0141d8450707494180c0b50750360103000b0b109034030994011043c0c1c24180749201c44141c6210050380b0364003510116000741e4400041102e1011442010310b40c61501917205581080c0e10b4103410035980c80c0c030560074003034440074203400013850103075840001140c2d80b5004401c0002c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 349867643 1250 349866393 349866397
    0x1b030604080301030f0213050403080118150605030606040b0301121217150109080d03090c05010c0f06020702030c030a12030c030b030a0b070e0303070501140114010519030f0e0606031608030f0f 85
    0x80f41e23410841040181604500000d040340c0a020000e4034042c0300490010840f03180304031001540641038800d210440c8210003541d400740000e8032b0702d4036045d00c0d000c58071441c1d0400d9005010041041590000700803500119408881c020304000001d84d135412001060840300030030071606c208108800c1001030380306440090040c0005400d8078090051158000c0240c4042c80c003c0c2e90703100b0b1000b80040c0f0355110714858003440342c0000a0075820079156640781e0103584896402c3c0d034075109130030112190303903002d001e05003e052180b0301325401100040c10117001e5540d40910351042c0351078000d1443c080e84000c520b1803800740c5e124140b511150703a000000e642160080190381e415201c0890810100701d0b0552102e490112820102201680d03101d01c802c90f0100100d00090004034284580340311901d580080301c400c82c07894100454a450400c0f1403800311175040c01d6042c1154080c0c01485120304040c0108da4070b04015440740541e00d0308201b1803503600d100304200340141c000d0000703810500f0299001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 349868893 1250 349867643 349867669
    0x3020f070b090604050c03030c12070615060f09080105060a090e010e01060b0a080f01060221070b0406091b030206190e100302070b0f0106121e0e1b030604080301030f02 74
    0x908100340c2400b2520907a5018120b130110b625103d810007005a0786000003d440d01401518014040304148480e1500c483d002100c0456246444100c1d90304800700d010000c401801940d83d032990242014203005013020781652103106540d14040034418039071a10400d00003503400c1840049084103041d407103a07005000801e40e200c0700e0b5207002004100400e0141c01030081c924599030341411516240c1e5600c98000080c0b2030800543d10200e4101450b00700750040c1c41d588800f448015081802c5a03c3e40c030b00c0018200c5d42155983d6030341c0e5502c010451001658451142c0e44180540e00d5425980443e03a030344150f00c442e1224100140111840602c150820200d00c48043d0030302e145003900400180180d04075003000c1301c00c9000c1000051820070014140f030304030b48091396416072000080320110001c0050030a0780c0d5403400b541d04841c01c0740f81a40140510524a01d00070040642c01c0101d11712042c040d07503800c0340b05c1d4024109003c045029082600d040d2500800383c02d05400d0a4070000d01510320383c903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 349870143 1250 349868893 349868903
    0x3280c030605160809212106150a0e01030e1216060b0114040317040510020706030614180a06080a350d0b060412050a1505100603020f07 60
    0x110011007044401d40002c0e00803540740d01c15160304040c0080c143c44446080740c0710081c6510a511500d022541d00c422100f00c1c850894000740341c602c5110440702d800c001d80308034482c5611200180701840c144070000c18040c1a24800a60030082803480080c10b440d000b80c26281019203810307081985150a06c034900d00740000140160327a032810f40c243c9501c44174070700c60281c80c01850511101c0c2c0c6e80d406015415036000c0400e00092400d81107a81d000e0b00040340030905070048205010214168413a03651000c4010900d80080031091b1400d100282a1800d0740c100080541c03000c03090071300c079071192012100c00c008022002007032940d84612400c01010316910501d1070740b10b001e81c2402805000030000780d4101c1910550701d200141e21080850420840c02d071109201c008100464100181c2d600c0303ca00604000c040610b007541c2c8407041004240d002c80e003601c040d0001461542000151100c62000d000008814000f52500540189500c40b462052405058000032881071440070b020403908020f03840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 349871393 1250 349870143 349870163
    0x509030412060b040e07050303070b09030909130b1807030201050903011103040b0412031e0507090503060a1a040902030c010c0501110f1215031b0d021f090b0403020328 74
    0x41c01c1240140a100c2005400356145c024140364110020a402c0305442024000358640004c95441c4901000002c4c101074880c0010712000348255140b151071801880c591180c5589189113007000481c811700a03044403a25809141c4130750501342c001c0385c4102220340900306130307885003040c40101e03003d170691000c811007400e000410801004840c1c01218010341c0100d0300746a081310511415012a80b820b0208484101c0100301442d816115402880e4815018500b40024035030314000309250000903204d4000050300d840c241e1a0b0f01c0a10600056a20403c039810b10060940350046904c4102c030800c0b15041011124259040c0042504841101070850381001d40d04c009110283c000c5801034800803404000d0540402c1003d0340d001d10b51540e00f14002c01400000110101070030070303050408640c0740c000d4018541c031005070b91000390007800c03c8000c11485c4a030012030140104024a42d40044481c603500b03020034400340c0c40c0090140202c0b40591402c00017501a00c100c0240c1c00c09002e40200490030b4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 349872643 1250 349871393 349871429
    0x1803050d03230c040e0606090a0602061501020c0927060a0207021c02180601030e010f09110307030b0403080c0f1c0b0d17030408070c0603050f07050c1005090304 71
    0x20560156400c64a010700c00801d0040b8070803952040001a100f60100b240244020300203a4600300d101600003000034140c602e00b50010020580c5807002e80c0c808070251f00640c04002040030b0384003003001415424800742c0424034110380026103d0070091316542100900400503050746a40340040c3c48580120780c12103801e86800002803001c0c3d0700c000e40032809030080038040c1c6420300e0282d00e00840c40d0350050200084d106982c0c0294054500140b606040503203c40c01010400f03000c0c400c009440c13200b01804100b00d24a400c007440043e2441c62030360b0180e07210307078401c1010541520002c0c0d001549450030368200d07180d00044882030b0203104c48041c20200005210b02c030340b003107001700410ae41c1d6040c1014840100c15400b0000c80038501600a040c00c82b00e14282c002c50250b0340700850784180300b2a4081c1c2040215100d00903001c405800c8400841e956a0038060740b000c43c00b4100747d201c0d0301860321034a800b0b401c250840e05d4600f943c001c035061f9625100440d028540c20300560b000340c00e19060410240130 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 349873893 1250 349872643 349872647
    0x4060c120e030318190b1902030606091513090e0705100f0302070f21020601060302030610050d060e04050312011509060c0f15140a0c0c0b070c0b0c07110102061005011803050d 77
    0x44155440c1614030281f990b100d0014841c0e001340c0c2d100f99001070003941400b40910620511003101454840102020080d000c40c4010b0080407078058910003034002a102121516280781c910f068000c2c9110b40c4815039504c901c40e920502d081e400f501d09250140c0c0310103007483c014030519840c0700d000f4003200a440e03013505588188002c0350303941501942110f040341d0340c981d0154220710041d5552500084a8085118043d024000800c3c07420116803001402036034401184020003001e80c1c0c00c85458200003010100034456030340f40c03409011101d00c142074049007102d01412802035481100140103101c810301090021801602c22101d801400c40910780b618006035400411000d44140660300d80c000c0411190101d03440b44c01c0e0103481989401c4050405600c80031840e07040240400300700700418403e2310001d0200f22005009507518003103241c03584840e28100e00a402c4c0d86c440d0718110750014007081410303184c80391002d04845e000c0c00c05690280c07107001048007640d81c1e40c001034618030890407000039050b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 349875143 1250 349873893 349873913
    0x3030203041a0f06040e100c02010606140906030a0902030123070f0c0c03111203041202090708060a15020109050102070525031a07120504060c120e03031819 69
    0x24402d281c500c0c1c401d41040c8900a41e110141e8184800381140d03000201142480d034403448001d04104100d4584012150f03088065590190f6402c0050f5180d503001c00819800c0403504201d400302c45a01d40c01d2120800124145000c010990000079844460004c250f40313080d03104501c7d001c01008043c000802c0520700c40c65000080d65600006440d02c1a2450703400d2045943c0780c030480d400b499803c00141740da22003658507012288190b40c41000354110031000e20701080100f00500c61201c5111007051140108210340000501c1e03070040c8a03000041005680d10b40c281001542c20a40d45256910381800041f4010003621400825a41c40021842c0c00e01030000740d2900710204040341c55406901c980c0642c600d104030341c40000c0481140701c940d400341152014480364001c031645042a0034000e04070000055540549041c3c4085030789114551005030710a0542c46100d8070300c4400d12881c100c1c0d8055540d00e20000300308030720103001026417507003800301070240c1c564030541c61050326980706180c10040c41070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 349876393 1250 349875143 349875151
    0xd0b011101051f050409050303160219140601050a050310050c1b1507030c120c0c21030b03010c0509150c060405030301081c1706150a09140a05090711070f0303030203 73
    0x40f100c4800000f60034a0280100c00d0029800005141107844849010304101c031140e19000941c0941c004c80b0b50030b40da03d10070301d041003801010f4107205511440d601c1400c109068000c10b0107004042c100780103d40300012441c10948a55100060035030f180054841d10b03001d4003580d4501080140007c110807080026144940440302000f02540d88489000340d040328034818950000c12400710030000303440c6281c1d00c80c07030700d45003181054001d5000941c3c911401c10244070a03142c00c441450b0340684d2890341440343c406040000d4000304070103002c07140041c0c02d5025841c134041c0301d0a83d21010310281540700041d590003031828011111281801d15101751a0f4009018200303041c400c07401018100842c1c1c0d031009060040c02c2c3c03207001c2e00c1c418102420030a408002e0400b900301e103078a13450060348030100000300803040040da1004e94290074000b0341c1c41c05403003c0c485548130b28071f2240c0503c0f0642e2031202d0b103074201109083c80609000301880080c20400076034042800040c4c0030710000149505a0015486 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 349877643 1250 349876393 349876441
    0x302150a0c1407020d2003150a140601020615042301180b0603070804050c10110d0302041520060c0703110303040b07050c03040306060b120702030f0d0b01110105 71
    0xd408a82c1208081c0381c0524403000e548107a001e50b5040110f0000302c2d102031040321140c005808080350201203423801c0701004920a5965508007006881d201c0c6100b0112125a5120303001154108500000d5450034090b0108109040d2002030f84202e40d02c0b5808003007c0b504403020142c180c0c0e115010a804050248290412021600d003403030702c0c43c81c0510810301203150003800503095496480301150004402002200c0d144107440d00c0b180319a42e40c440360040020140e039030764000c1c90f8044600c1e0400c01440d19501c141801448240050030b100103a50445080c6403601c56101c13008040700c0d0819401c042014001805050180300b1304407205402050340500039194440c2c00c203170800070255248012100540440d156031701084803a8420b50003801d0b8441e1400c100d81c101a161340300c00003211969444148a01000100c1032614100c415480e5400502800998280704036104980c03001d218000a08826540d100016110f0f40c0c0035003416100180700600820640c03a00540c03071f41c2118020781032003003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 349878893 1250 349877643 349877657
    0x3030a0608031315091d04060c050a020304050d02030a2001140f1e19170a0608060103030f030618020306010e030d0203040303030b0a05040c17010509220302150a0c 72
    0xd4038840000c101c80c541e2910381c14182e0070074903141010200110034000d090170050395034000220200400320841d0075465103c0551a541071515020044580404403001485070501c91442800d4010043d1001c0721070546a0700700c07640d2180700003404d004c0703c040b004141520390171580e482495230020080810b0402e0f01c880d0514440d48200c4809800b43c0b100076003181c03504002d00301003d0081d1880c0780d0103003030440c5540e003403070f105c000f0164002c100014090009501e00111700350440e80b142c0c4140d0004980c3c001003122030701744007000c3c2c1c41d81c005010140c02d1064180440c0604d81c402c0e80280c0060450100c4c81e6020748100b61002c01035441030300c81034001080300d10800194500466100400c072040c1d001107144c54503607078066018120344009190702000110002a081c0c45601450a0501c019500d4600039004007030300605250040e00300c24000c1e0011801c004d060700c450700159075102c16035001c0c125088214a012031900100456000405811000348512982c041e0070a8102e000d641d16980 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 349880143 1250 349878893 349878899
    0x6270603091c02072709120201090b06090903071403130603060314070b1902010603050f210304020303070303050c09030106030c08010e031804090311010603080d0605030309030c3003030a06 83
    0xa9694070140282e00b03408103400c0d5206500c40150f4a102c0005c0380180005c030b00003c45440320b421880c401003600380944d44a02558041009018415511a204560741707002d9003041040701d0340e02d0042c1c06c4c00030b12540721501c414003556000c100f076842102007000303040c010507142c0300000d0252060388402ca80101107803807107900c40c200c0451400e0a5070440896103041800700c500e4102c0c0413408803003807000d55607580030200100d201401412030541d088001005101401c500f00c84080420243d8030310020810700900005170b6022044944039601894041915200c40f50132103000c2c80382c064059415131034540000304000b65240d0307500c102c0d00040020005440e010064a881c1c2c812a040826441e0000080e0142440c241d4804801d180c041d181501d90100c07050021421618140c109031140000400c902c40c6d581c1007400307a00060315041e0b0185080c0000d04000c0303642d680201c81c803d8401c11280e07134038040b01c01c443d0200003002c4948040c0000584d4000010fa074403584103075611140d0606140e008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 349881393 1250 349880143 349880147
    0x1f0803070c12050c010e0f04020c06071803051f0605030114090c01050909130c08060705071104060501080703050a290418030c0605041707050d0806010e06270603091c 73
    0x100c241030b0f0000050140104200d0044500200095003242d00c8441100e0b41092902c46201420f5840340101c020036203030400d0715000e44130284101c83c420304182c06007c1032002070404030b080080005040100e41001e5000d03a000b101030a00c81e044550158079021040b001c0b5003003280c00341c0c050312441c01501e02100401c0e004650600c9000405038100c1d2031a070104811206034030507014014004e00015090310713290740d01c280c1032080c16070341c01c1d000480204200d01845041800d200c41c031081100c2c1044580c1c034140001e44a204001c00a00616a503500004c0c00c11031039411002206850b00900c803030300d4400e61070760301c000041c401d8541c2c0241c1c94080c08800d10f2807000700c01500150103442d12010048250344100c042d10000b40112084c200224000d06151450750142c00802c0c0b00c1c0707010b0880c0b50395692004061020052400b81000840f40c101c0d43d10340c0f607450454000d0b9424039925040d0440b403000010002d000c2c030100b1504104c00104110000308041550040c510000040c240d01040500003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 349882643 1250 349881393 349881419
    0x17010207020a06111905010f020a0804031e1403090705060406090f0803130b070f0606030b09010e0606060f130e04060905100902360109020c0d02011506081f0803070c 73
    0x84c400c20360002d440e01c00710342001c070071049855200e280003040384004a5081000d0b030f00a4400031000c145041e0500041603002549920121415607900345051411040180703001880c500c186070761030780007011601140007400000042e0002130b2219a03074682e140c1d00184862011310940e1201e01e00c12101103414000801100d156841c0a8042e09025051291041e4294004502151821040916000002c0c160300990000f14060141c170304e240d02c1d2a822040c00c2d90003403d0121000c0d0021000c00c00190359031001c1c0c500340c0b5404100241c40d813030302d4035094420082980101c020904c0e0481000300f00080f50300445c0d8598810020340e0301d1070414507600d00c151022100c00070350218900000901d40c0002c1c1c146c007082c2d00d0091003d01004003004010407000042a00400c0409400081140791288100240c0d03c0f28100c0707200030402103032600616402040d540c042c0c001000b5204000ca00c0b861100b80b580842c05600304402001569207922a6a59034402c4000301c0e00d220340780000186518943c49 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 349883893 1250 349882643 349882667
    0x7090504092607060606020102041703070f0b0a060b16060e06010315050a02040b0a020f06090c060f07061103070c030215060603061504090c050c010b09010f03061517010207020a06 79
    0xc0e00070b0341001c0800e49080c400b28030399454401c0c00d40078811540850100d008035030042809400040e666030401a10224050507140c40020381e0380208040c400143c0007150900036241c01c0042c020481c0c4030010b07804007402c41607102091840d40410414854070f0b19110700b1801501ca170004001620f40c0d40b40454030741409100160116682c0080f0503088101074008560264110000500c2d01d6100c115001d100d8004519980040e4084d8100f01c1c0034042c2001100c0d00b003202d12004090101e0400006241da11403094007040071480420900d0800c91950081c0d9480c800c0102d1040d100e20300345400500709568118150014812000720010060088040034007e11014100c90710350303600d01007441040001042075000e071700303410400001c11560603c80c0c4030800e40f407a0345484da00c600615443d4255207205030283e21801450380100882c04181035010b0480f58821400f040d0045550020740540130719510412001c0701c4040740c0d030240c0340103500030807440d44200d41e02207070039455000132103036201840 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 349885143 1250 349883893 349883903
    0x7030606090b0a031409010f0501050915040906090f03210c050406050c120f0904050609250e06070c060f0201150603020c0c0d0b07080108120306090624030709050409 73
    0x1560a0081418500003410799441d6400d02140c01004200b98803c2c6020451b80341c2030b1650740d20784d00b03d0f991159005060040008407082016424034400805d03c0604c41c0903158440c1c0da84421311020050143c0050303504030b4102c178404c40d25240d0b40c100540170032410900c40740d02000d020500019040d6602c00d64034203501c55600d01d2305041c1060801e503243e61101e0600c00c214855600790380044d084101c000c060200541c0f407915110345900c0c00780000d44070043c1c02288100300c1041040440c1c0065000b210258440c84a2111040800b400507030341941261421608500b00249000c11711075416000c0c011521507540750920807500c500b003207017203c040700400308400f40c1f604000c1103041d10035000340610541c00700503a0000039078075001034615003485d10f08071080039000701040380250300041a40c0c010000440038004a040300040d8190034400144150b11800410340031a01d182c840250484415084ea075440401d840790f04c0350325001c3c0c2c1048400070700240c072401c804030b180c2c01c0c180034500085a0203 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 349886393 1250 349885143 349885157
    0xd030203090c090603031b0717060f0c030606160f0c090c080f0711190201080105182409090609060702030a090b0f0f070b06101707080a1e06080607030606 68
    0x30310802000f52005002d15a052100344490416031001000c641c1e8028141d6004094062800c1f88209801d0919960588950420b1040001000a040f02241c1c480c480c2c0521a0b52962180000754442c0110301036145c81800401c502d00400040c14400d81d1010701602d0016102640c40380050156680c95081000088004020a000211100c00d4035041090303820900b451341c12802000d417400000704c1032500c04414601401c02556042414a809001c00380c1d030980300d1496442010201482c0a0301a500b113820240745030070f400e80000e582d04000c0d1802051940d442c140b81d4000d40e601d0b0130950710107809010348404100b401e0300000803145100c2194413182e1000d0301c1c010806480da00203104030324285000300580c000505c400e20003000c0b914850601440c60342050000d00a6039500a0012428400d182c110786c501c0f20b4107a214594412580d2078402002e0703840b0000c010280c19140e070300f50241076030b0946000110415400c20785c00d03903103001c0c03c407806642c07610000c42c146c0340c0520944000c0350103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 349887643 1250 349886393 349886413
    0x10e04030c0b0411030f3007080c0a0204020d0f05090607120e070e0c040306060803031302062a0102370c05190c0e160207050d02041113080d03020309 66
    0x10b82c1d030b12684540540135890000d1510400f090920008021a10940c0c01030018501003038003003064004141c00741d000c0c00004440c0b0f038600080700e12648001a049030b40c0440d0140b091003041150145180c2e02a100f0354a841144503c0000b4000c07849450000a0900001032003000000420a02c903581c0e036039440c01d01444154200c1e004001c0e40701000301074040c0701341c081000712038180981d00852420031841d5446145060441c1200c880f5000800c40da00100140700c3c07598040b05010315826011119190b603020403031502400e4150317220200d04101071103026000a07010641c083c20900c2c040700741e044500c91700c181003900c000c500c6114800011b60075a00301c1d22854412040b840445108100311100c0c0302140140c2288000a4081181e60718203103402400724440ba04103039a00050890711400d142c000c1c40101945a403440d004a50003443e001e80707110150343c0c40342c100812521111100c030f50b881186009002d5014084e008540041c030440c203043e0b0b1814071030710880303104801400c0600002a1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 349888893 1250 349887643 349887653
    0x9010e0301290a03060501080c0306070309151112100915030c090e10090803061f020a0b0a1503050607080606040830030f01052d06070f0b09030a08010e04030c 70
    0x2030101d400c1001c124004c00041c22500c901d5000e004004010064410814101882c0c104020403000400d41003004460000341c480c000d911941c000c901010801450400740102c0600a02030280d07800502101404103507444000c2000541d9190003050040840303100c00c1d5005ca408502c030080121800740e03410040020395501042003290300343d058070b150800c0e2410030400e03960407401c143c549420000600500b460000b1191403002c1100f860f600d1500248031002c0c6d00c42851020180080200c6800140300b20000c1d40441e0340910369068241c0d0443e107901f0841d42c0c0f14011201c80000c00c0d65500443c1c03692800400f51011175400b5030007410001711000041c1e04541c07804e2180c44124141210450a103e240b40281d03209080f8041076000643c5000300301701012402c81880280c4012403840f48180c4004510040c52011080c2c0e0078643e20f00307051809244090365642c01404c0a02000c1c00e0281003075011005040c3c0f0311703d0b6510301000c1c2c1d8803044064061481a24020046a011196080050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 349890143 1250 349888893 349888961
    0xf060109091a01090f150303021b0a0b070503030a060e0103051b130f0b040605060a0c020108040804031a070f0201021303030f120e031e0c0c120a060c030209010e0301 73
    0x2510070b00c10b07805281004070380441d00140c20382003452160b8480800c0346802040e4490800c0006481c11100c403082d02e940c4001c0d451303e07451500007291407881204014a6140c40c1c25501c005e01c04201065034654040c00c02035200d030030549a00000da42484000900c04101040070341c140e1341c004014145902080b20007040c0650b0480c1030310b801507070051141c018019103100c4d610f003c00b1810390101e13400302014100012100c140d04290b00c1003130240006058264040f480201d0340c5c0d82802e0400c0c2c20703112403c0c140303440e00640c0e01c0200a03002c007071000e0000d045428803160107002d1075103d103c00c0b4440007000760b082c0d00522603640c1090701101000c01c0828450160590540c1e1030b81400c6141c2c031050381c42d100903140801c0c00c10403285e100290424900c2d480d81e250140c1c0108d1050358605003c034040342c030f40c0c070b1305098011184558008041c0380819503051051151055006004000c0c00e40d40c04006000307900121343c2c10b03000c528901c038007590324103060060040e0303244440d46525074038502075a0500c07a8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 349891393 1250 349890143 349890161
    0x40b0a03030509011d03010204030f0b0928170c0d0f0509031b011806081005061201060f120213060e0103051009110f0f040e0610021207060902100807020f0f060109 72
    0x742135501455171503c0a100910240d0f018880340d0041e02403900301511201e102401b04205640480c20441403200410b0840c0c14401d49101a41620f00c2d00d401c1c040d4081c140e0807a038444040b00000ca0101e4041c001a9949100b4941d0f00d4440400100902c151014040c0c030710956050340101005600109501c4045c0c048410141091806100c0c1c05070705098a003038603040280452603a40070300c8443c90002059000401d0202c910510300100e034003c5040c1c8480601c41e500038000f08030500550103008084509401c205140115141d084040002041006c18407401000c11018001c2c120b05501c20b00a00b88600030071f0b060328500900e400752100007030400c40c08800101c0c0c02404803590030140c2030b0050070320400422013980c0301c1f400c00804482c20500501000c0c440c8003842071141348140c0100f03003141240500342c0c07495168001801c08101420070003000943c0070002c1c258460300d95400c02c2c0300d070780030304a65400c41c4c607803108078801d103541e440c00d500200c101a4442801005805c0d4190469201 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 349892643 1250 349891393 349891427
    0x6120a050a09081605070801020702133615050403020303060108180d091401050403020a030b06190e0f070f17100f0b07030212030c040b1e0f0702040b0a0303050901 72
    0x224100c50300c45140f142c100090600818100c2094030b0103220041143c400907003a16402107181001c05d50000e6402c9228080c000c81c4d058844c0741942080d00c0003d254045e003139108540070031010010f4070307030415083c000f602140d0843c00ca44003098108564400d0900c5643c2c5a002146191100801520601002020172520020450315009041014409802401501d88070800040d003000031241e11480011019810407005202c1000560745442030581102d421080c1c8031055101d040c0850800440d090008000f058402400608a800d044103944036140c0c144005140c1c0e26480001c441c16541218010009182d044122120120460600350040384652036002c43d0341d510f02e48150303260301d65401380c1030381400400c40c0e000b0f01d501130289540c00d010340c040c0d603490341c54081108003545c019401110303100030001c51502552060020030142c001c405500d030549401d03c4607a4040107602048089003e10304200103420241045000d207030660758192500390502d04920011100c50004040d2401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 349893893 1250 349892643 349892651
    0x2130e0a0b2d1e030712120f020327090703110901050d0b040c030603031b0b010e06040905011407030b061c090c1502160803030714161e02090606120a050a 68
    0x140e9603a0f6040455026141c0726810120752103040300301800d0014960000940c410385142c0030740000c0c160f06501c03000c0d010a0070007068002d4402d82c01c910310700034607c0064103c8801d480c031041019824001030052001151000e500f55610074080b02a81d40380c0380036880d080400d0140410540c000d40180c00f01d4a608036000410046500c00a002da13416002c1c428003181d5614014010301d9031140307564022103d8030012425180d2140c1d126400b0380014420680007040c010f0201f0100c2e640c0b40c0050708415040002405600e0406080818003d825241e00022030300d441e4441c0c040f41030040c1501e420240960304034000301c01c522010300c060b0600c54001c40ea0b646611002181044e413803800c82001e45400c1d0700910b01e0444503035008020444503008041c00794410b10401241d10b60141c00c20f005001501c00c029100d81c41c400e800e9800850a210080c01214130243c4c0c0c03504282e14140420f000c9008649100c03103034030b8060602c20b0610400b100c080f0006000f5000800141140c2c101503004621010001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 349895143 1250 349893893 349893979
    0x7180e07050909010e01080d0f0206011203090806070807020d11060a020313140a030e0105090d02010e0102030c0316110402160605061c03110f010b10030504060f02130e0a0b 76
    0x40d02d1100260480031000c50742c0b80047c400182e040001e10140b01650610016030460044080c0d0342c0e150500c0f503803031040074000303a00081501c141c1c000c80c01800790344212045810b1498000d0f01c0000c04894440c018490061005101c0344240c41e001161503024014000c0ba48800c41c40c14040d40c001850f031022007003800c17007083c0000e0700000034160b0701c83c00401508040400f4640184050260661203041010900030303065a42d0700c640340480d1051f82400e0508020f95844010703400c600441301c850300c25010104a500c0400cc504800050507807054000641045c00349080000b20300030074000040101c0c1020070704001440d00d900040e0042c0d00180700303a1030441600744d09044019410b40480000320303e8107055000700010485907001c0c00a031380080c80440a0f402c0858128580c242d403140401da203900c0494248205a030001c9080d2000c6401555501a0740504080000b46882410201c000480c0054110b081030f00c5081c0040d44000d0808925290404003035079007040c01000b155a418200d1814 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 349896393 1250 349895143 349895149
    0x3010b0a110f190b100b04121a0717090a051213031502182202092d0a0b0c0a03271e0803090d1e0f0302100507180e070509 54
    0x10708041d4002d075884001034250746000e440007070700a01300d00a203640d9017a081c800307000204141d07819142e002400814405060a00c40e500c42c4202c0f40a1179100311580a1241c2e2075409001c80740258411640160a91100c1800b240c1d01c2c00301c40c401821503003103c03c42c48441c002c501c00a0109100a1480384c0344551281c40e00c200203200c8540c104001c07540000c0c89404a11000a102c204120032a121708842901c0034a1030f5000300d076149804007035a4001100c20103a03035002402000001d05902c0b40c0b4004824040703015400030310003e52841000c9004001034039011143c116440d44407030001034043e1030b14607501603412203c060784a030304c10000300403050300440048003450010480e041542480d076221290f01c44004036683c10114a5400c2003050051980700c00c41200760442d400b0146000820010300382406100c1110030044c1504a001d41c9582415030001c0c0d0030820012405080141e1344030b500043c2c03031740301070414803000c2140c00d0007042100140c1503242d5031303020006003042d0f45802051000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 349897643 1250 349896393 349896403
    0x30304111f09050907030b0d0602030c0c030c070602120721140d0b1c020109140402090306070305040507060c030c03030c020f0d050403150c0c080c010f0207030512090303010b0a110f 80
    0x10031070026241e4803080040b842d200c03150507000412420100011038120010454100107034501401c0c442d0000003103201032062808031201c0001c4241641d4652001c041004d449061511911005115251440e180e1079051011210881d9000c04590b1034054565109901c01040400e150280039820f8824000030a401e401402d401c54a003100013001d441c040100585085c040b10f0114019a03d0201c02c4010b0f6040021030050320b00e0312000c914040910400100613100311500d054050190b013003805a02e580540116010b00e125070305a45a0382d444070000c5800c2501d600d4044c0000380c403038010303601003802940134200020030b41c4141e421880d000c41c00c1c1450b08032500e65080c001200018104103101d00740041000079a20990144501d00030307920000d0031601c070b400015005007000a00d1201044096100105001c201a015500c1d04424107010f8003580008050003451f4000e2400a0b4841e14048212810383e450544054100650030b0001ca5034070018020030300700740c42041e40e0b2010ba5641001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 349898893 1250 349897643 349897699
    0xa0b070e0d050a12030c0207050d02040f09050d1d0609100c170c070b030c03040221070e1e06011e0201060503030d06180504020a0e090c09040b0105011403060303030411 74
    0x2006008844661501c81382c60071914110784201881d1034003e08805502081040880da400c813240300c900c0000b8000100104003000c6401402c9103403044030010811f0102d43c1016500690701c8040041842066444c40c0010040c00c0690004041004c04940e1411022400c548a1b02d440c003900142c003550303280c580f01501220b20155402010503844152402008907901406491210324291309007140380c1340d601d00010f800244120500e010300c13561070350040800c41140200da0110f482c0700743da132005c010381c1030303415101042014009407c691002102d1072040380504c0044e0744450311981c04259144242d602488404115500e643d0005407640d41000940b210a170344601c0010f055107881c2400c2c001070b0740789910054a0342001c0c200320141e50343c40b0326581210320b809440310b100d942c0c510b281d0341400500c080c0141d00108407010301050202142d01ca5042c0d91080c4c8038456100740c0c0504440315400308840041d8140d1080000a0008000345000884140050f08041d0014186014031106e401381e01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 349900143 1250 349898893 349898903
    0x5030405030c010914210709020307030c030509060c030901060e04080a08061903170d090c0503071a09060a14030901050a1a01050a030b011808070e010b0306030a0b070e0d 75
    0x814180424503062107021610703a402d003010902c1d10f1824107004102028041c60512800d4000c4442c00c080380081c44282603e00210107803100c00380c58111082c0203400a03541100002c3c94140260080c034028820395000700c2200300107051540d07420305030f1320b1941e00003086014103540382d0400041d00d00d010b0b4181401544201201c5846907004a0020715200d00100018414009580400001c8500c0b43b0720300181c03038000e100000b04546a034403078a56441560a400f42e207915100c580014402a41e5030b480a0310005c505403028a0303070742e910312442542030311300c2c10210304070030800c8090714503100f001803621102c07905040b42c4c10062005c45107286d40003186c180b031143c1d4440d0100b0401300350500c00c01c040200c1d1000380321042e0140800080503401628004030a0543e5064007525036030040d15480780c40c400184603100215140c4803d2600c0741d2051003041c9a988a0f1301c00805e80c2c848940599129a402900922007030301d142c1c91f84204007102625840032703c0200310010440f82c6a403c84042d40074011 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 349901393 1250 349900143 349900147
    0x207050619090b0406020c01270501060602010c050d0f0605030a1401060504020a120b180a0911090417031026060915180f032a0c010804060f180503 65
    0x22440d1600d07400010700099151480c155409000503c00b128031034110350400001030711000107826840c01407015041d10800e141c2400301d100000320300408850b96081c816002030001507a581c500383d0a0720510040d0340c010810034007080501a040303500c0b0b650841c036a40f1001c248256075801007401d10000d41020355074901d091001b5078500200340241d0000300020741c0c0031450302c0300d00b603c01000a4061240d012006444020720003140d520003d5818074001429000710250400001044c01800400b20071200c0340000c3c1103250140c035000380d01d00c0c400d0703801c4a07009044402c84074800c00294002015000584e600c00390102c0d030040e100f0511001c20f154080a4941062180d20461078140004e054104603031200340d600101c161040806908241c00b5800d1020034066002c0b42800c00307811544403c030501c0003040504c200b500101071054851100360007058800118002541c646503101c0c900b601160a40e008203001034600c0c0d0041d00c02c007400900c000303049450300007048403004032807900303403419400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 349902643 1250 349901393 349901401
    0x5070306080706080403020a02060702031606050d06050307030809091009020a03150504090c0e09010204030218071103030103030512070e0d0c06090b04030b010323030406020604030806010c050312071202070506 92
    0x3080240a02a100300c0c01c01c90442c1c50250b0340295030700319034032303009000f100c0c042551800c54404102212820a481e80c9210445443d140c0041281c1c1008100020060409a00045d181004a440c4050341d400004c042d280c45422011711680c2c60005c0c4c815200041c0080e00041d6581c0d05101030102c103892a42e001c102001d20202040c1803034400d4215620442c50001c69100045903d43c0e841d0454a09010f0a941070b07540c4081c00d8021b0007142e01c0a9004182541c60110905040207900c2c41141c3c5920354003900f55103450050340da40024000140442d0b020004100d0a4589041540d0302003814600041208441c00104128003403030764088840d103046800510020350403070040e4001c0c01e102c95080c0e08003813545e1282e14038008103210150034003507042c40c000d501190341d81070401910300b594220b9036150b0743c07000020b40d40d020449041d0f002503c2c0e003002c10384540c40b0380c0c81c2404c05a000001142070a900856410301a04080d144006104034000801100100350018101450054000d0151860 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 349903893 1250 349902643 349902659
    0x4060c0c170301080123070c08090d1b0b0a0c030503100f03150c0302031b0d0f0207121b082226072907060e070e012c0105060d0f05070306 61
    0x820541c1e040b4000300302c2c0d042d136448441b07814401503000c1c0782450450007801d40d03820710301064800d0b0300a85800031641c810742c00030300071804084056841340380194407031541d07900007503220750081c808000d000569081d04a0040b0f03100d08082c64010001d2800700c1c900c60760f1141c1c1540203031080d9004036a20710400d100070101020520800014501c1d0781400d40c42c43c5401003c420f500c10165541c80d6622802017860101080f41d94402c0d03921035a0761604564814003400c0100d103a250604141c400100c0160b402d007025040600c015070a00c1c1e00c0161107040010071041d801914810380d840b010420b156000004810541200710f1140a80c00ea1000100c4442c650302c0500b0143c07143c2298015100020524060b40e501440085031543c007902001d4440c1c400d4a03210000e084094001082072050003c081040300706039001034101e03401c14428500b030528101c0c0755207a03545c90001050400c041600104102d0901c0720040c4511248000001000c814031640750048590a448800c000390381c3d050107022140d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 349905143 1250 349903893 349903901
    0x70218092a040204270902030d0c05152e0e0a0216020916021b0307030605060a12050c1809100b0d02040203040b01050108090a111014210c070b04060c0c1703010801 72
    0xb02c80c17004d05014a4020380c0100740d403010300906a90811007160780c00401d0010a02caa0055048044901c0300142070941100c2403445620280c183d1080034061965452521005c01c001214803c0c54141000d68640201400940089500c2a50706505c21008001659042c500620401031092a02850515020300a15242241e0031025040d00307520100c0d001c1e07680001d10001142d600ca4008601550f4510124404d8030955000c1d5080c030b03c400b10810204040401d051540e02d00c00ea580c90851102c404010030040700540c1c01c819590030030316203003d00e100d00d03400040d1030420143c101c40d60b030340165004c0f80480c0c0c01105c065580b10038110050002d03681c04070b00c242e0484240001400a201070f80c035605100c8142c81d5a142c8150221480e0344060f90103591200303064112911a6922800315005108003400d0000f01c000c0c01640040c0019040c62a00c0190390009030080700d40e01e070340e985681c2c605006081c0038007280b0500a020b050301c0e00203002d25014451071449034400a86a51400054909413 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 349906393 1250 349905143 349905209
    0xf260610030c06030c0c080a020a050f0d0810120b0402011b0602120105030a021305070e0d0510061502190602040b070804031a041e020103060b0c03070218092a040204 73
    0x504181305500c1c017650000c5110740160700000303000da890f0640d400980c40c16400c010f008045008141c501c01c04020042216038207602c03141c135017640b560313208100224512181d00400584031112003004021880d80c01480354081d1060401d034081000e10224035071002c8000c102255049d4001a0420f200d007015a510380c0146000c2c0c0082034000c60316030000300030500540c130418550755540c000983c0684103600141000074040c1280e00f4410751402c02e140c40b403030000130301110f650030b00700d0028034490070f0b591038250030400c0c1c0d019141c18401ea404140301d004980d50700b0707100c46d5000d10002c0b42d28140035000f802400d114500e040e50b5a440d51400c124030781d000800720615010340d6020400421b03025418002c0400c9581e8883c40c9403185440143c0c02007015820003910240c2c04a10007003280b0000004000a0740201c80141c001d014803640f920412000f156000d4403908510150b40b0307004010300d070885000348409104100c06d1929004182241c1280c0d005a80c65034040d0003407a8069281c0b2828481 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 349907643 1250 349906393 349906397
    0x501121b0e04020d050a0b071106060307182409090317040f0f1e0506090f07030c0501030908070f060b0a08010b0312090109080111070b0106090f260610030c06 70
    0x90391030300c01c0c01d10305000c00a101030b0150319240c40300020804103100c083c2030b05500c04045805810400d40003483c4c0600e07440126603e2246202042591800080c07041c111a0040f04100003080b207030203034001a01001c2c0021804800c0b88a0b110301d43c00900c61201c0c09081002c90004171032959050042010011103020131075181c0f220709004c08100801540110302d9044640031104c9046441d00e000e42e14008610b21031400c00c901d41e078204200d00840e403503024950342011070700500801b21081d9107402c0c1c0c500c0000e01980c14100c08004a5000760885804640982041410200d00d03072a1404c040701e0302c0004540e443d9440007003206a01d02a0400805000d843c0005c000881100c2e000c0b0359941040ba207180000040469542da80781c0c41241c0b030f01d01510743c10000740320502c040c1d080b010700b6400030325003140c288010790b00104100c1e114008100c2260b4240b10301c2074805e85406da03081b031500d5410707030301c404981e00e0801c402409140030808180908092803041c1d8905185007003203d8200391035040201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 349908893 1250 349907643 349907693
    0x60f031f050a0c1809020906090405160e041505040b060c0f07050a0f15140f040602010b040e06060a03140312090606040b010806060405040216171306020a0215030a0f050112 76
    0x440d04e8420a07041c1c64981c040140d03199541c2d40040d82c2d500070ba01605502038180000c21120601f204140e80c0340b2801525003841c2628210204002d40700c121030030380c0590400072002c00c164506a005154040c002500080c40c000c1d40c1d0368401d08140031104180980c5d03012090411541c10700000c1e01000304030421100c0502400e20212a45641c13021515204101143d100281c040d104a0308403a0740c0211940301a550301d9603094041e0290a200104074800d80c07400426026032100810003d1047c10018894010b1504541d14450a0320460f40c48144e44d200610a0440312100c03041d409000e100d82c01c004200c0c5251280800c03080d903110241c102c1c1002401014840140c485a0548055807000c43d0050707190044135000c4140740c05c85110280103c3c0c111100c1400840361040100304110a580300305014903100e85050f66a082c160100035001041c4903692040d020480d0040d503040703007080d00045642c0314030680c1d2006880007a04104000c44000000b0b1042000b0080c952503c0040d8400c007807 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 349910143 1250 349908893 349908917
    0x1106040b07050a14160501110c060705032d010513061a0a0e03010c080414010203100b0d0902030105010305031908010e010b0a020a05031309051806060f031f050a0c 72
    0x505948800740c104400d218000c141c501490340200819400c01380d1814140e602c620080030160030a100005040d0b4203075103044218083c025401085421101c84a80107007256140d100045a46034170050445102d0514500ba003080e0100d207040c000c11071810030000b14069410881000010700c1d61400d5442840d241c8030b010004050302ea00903040d4031612454840c2c0b5a000b230030054031a100700c2445545d141d440c16280c09038003034211800328001c3e4007a42070032040859080501c0d080b4441503440c070100c00081c00040014080190040c6520b81608a02003044400b95010901b581c17020303082240d1507080450350640103c0c10008240a0104130304d04840c05500d000c0a06040c2001030241c4100410b0003c1c0d405445402000914640c6a02008403580c510803c404010300c00042e00039003000609050200303e0782540d280b8403d100f049204041d09858030350a04215040c1d580481132034060141c80c603035111461220600d421084070500011072a031402e070860300120740800c443c100c2404a1059030f8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 349911393 1250 349910143 349910153
    0x10c020109031721011502070e15060705010c090608060d02150d0e0d02070305120a080708101d0a0b09070f080901290102011116023d110604 62
    0x12002c0302e4100001c09000d46050745500507910828001c2060407410f0340c0c02841089103080120b040301e090200746002c2d5207a55900b03d03140d001511a80c1040090701000c0f4003404080030b4040410b0000504662400109985035400e49125844000102d20301c40c8080208c2604410300960086007290824103100540c0d00040780c68003002e02403a030002d004581035203943c16940c4134401c100e404604450348a039060400941e50b1403c0e00080306c1501503c8031170040c2c0b007059011340340c001089446080c01c0d40d40d030303400464802c000140b80000c0c8504c54540015001d07001415100c6201041d104d241191401405030806d80e0002e43e080750145040c0c50030001103a80c0490182d009011a143c18410b503141c410189002d01451031264201202c224891240b907480d54040582c0340100b83c0090148001074050440c07103002d41c42030b61101d240500750040062918445041150151016150302c2d44901800d50350755a4901c89101c001040030522460b04a40220740840c584207140c00802452902ea078032 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 349912643 1250 349911393 349911407
    0x20601090b180606160c0f0605030c0901110a060501080709050c04030f140120042c0a090201030905070b0403020a0f0503030715330b0304051b0d06020f1305010c0201 73
    0x150b00307010101c590220710141d40740300469a1040e080c0c44221000c403070742e00b064582401c0394800c82030440c081ca240000c1c8240280c1c1036034801d078850312280d03003403249080041d101004116040d18050180040780000070380036218841c046d00c40d40005101c0107060140c0c50b4219103010700584600c800078003040000800300342e00504002d6001201d220380c070445805880c0909084440c518040507013619034200c01a200340036100b114120b04280c5d414040c021003168002d41109014082101404d0000c0c02c01d81590304010303070951040c03400040124581d1a60b90400750306d0380104501380000039003041503240c0b228011019080300d4501103042403078000040c0e0749201fa900000c1041416101c09040800c540d40a02d10304180c8500d042844040a8600e00e0886d5910100c0010005c1e01e65001c141c40b146182940d200d180c0c003800500020390550600c0c1100d181582130a80c6c4410b0100194000800d540080d14403074840c11006074480300c1a46a180f03011201d0b0700500d040019064415004d81e034080c1e9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 349913893 1250 349912643 349912669
    0x30109020d1106040b03040f0b0a14040201051e0301140406050919090f0204020307020c0a140f0603091204120b070309320111030a06060905010503010e0c0415050901020601090b 78
    0x9000040b01e4950000c0740b0a80990760100c90000d102008200501080b0194a420240300d040d100f107082e5103141c082c45c110b0b03851a102ea032408541c10005001540210f00804d0040c0d003140300c800e000d079a00c01c0c2d09049035209820408908240010180d01410140101d40103040e048620048901d01101c00409103652010040982d0751104028400e1041010701107842c01d802410075952451300300c6010356520040f0b514207000d0205008005524449840c50381d41c040001800702d4114180c0508101c0290005001640e1600644a00380701101d007550082000b044030080d0725540241a041c5108a0b0200410348000d0500b000148000500b00750341c00e00c001355200900355004901c050780042d103035641141c046015032800e000d03080c5911021000c0c600c90328403050305108a644900044826540d18480c0700e012480510044c000c061102012683c001008200d40781801e41d2441480031607003d0f02551008140d0000709440a964188030890142a6408003032150300c9158000c1540503104e10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 349915143 1250 349913893 349913903
    0x8090303070f050f040b070b010b0301050a1404180507151d010309050f0d090513110901080a09080a080103211209320d02060f01140607150203070e030109020d 70
    0x101580b19078003410607a10703158049071940f9100ca855070b2907004187d11414041d031705502600f000064803101c072008ca034181e81001d4215400103180c00035481ca4400c12200c0e80754090b45640801c030081d01d411440030140da0081d0700070101c103407800c01c0030107602801c020844104441031000d900c5942c40c00c400186d42400c00e1900250780300640c14264245076601c040307101c040c040c100d100300d051540000b491040c0c41c03003243c500700e000106907214400c0358090038220306865001d0010460541c012003005600c03841140c40450020215900e01000358440040c1d0404200504014800d0103400039032000c01c44044204015510100d00c8050007812120040301003158a40c0520010000e8041c40c01c0000480410380b015500f0310007004040c0d07040904030040c080d01c241d01c854400c55100181041c0140c1001044080903420149443c02e01e04514024640003201006010001142031120b10420304103c1401070700e03414600401095481d46894851203603040a45c450056600d50f200440d1455000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 349916393 1250 349915143 349915157
    0x408061602010e12031902040510110307080c0303072c1e0319050d1d0f0103061e050907050f03010b0a110a050a170c03120a0b06040303030b0906010809030307 70
    0xd110490241c510300034880714602a9041900c2d04c8240c0c1800b46005000c80c03c0a01a000d118203224000c038041c40c41000d034403111101c10399a8150040407505102c15281081d24980281ca4903150303450f5205400c40a220f0344000308005645500140f1000781b00401000b0001c840c40c65882008014001030300b2074459800c2210812200101c5074815091a6024058803503001c0701c402240c5042031a00c03000e4945014420100d40042d02c81d0f003807c1c9003401d07854410414640f0140c248019101110201c505041d501e28010400c903a41c0e00070200b4415150080301c1c0803a081100f130051105001e0274100c00e201050040051203d0b4031004d803415030b4020001c0d90303111a20000e0403101410004d04281c2c1d5800303881c0500d401c0c018045404410140600c5c144405880a040a10080c1c411301521200c1500180100c2d164490b01c0750a46812400c1d041c0007040b0040d0520002d1031940c8603600031001320ba40c1718401d0340242002c4000c44da120000b42041d02c003602d00386422548038800202072100308400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 349917643 1250 349916393 349916431
    0x40b030a1512050717030a050f0904060e0103240c1709010b0a03050604050c0a1a09010207030c0816092313080708030702060a090314090604050d0501060614040806 72
    0x254854000c01490444141e0300c0802da6424440d894001c5805900007074500300c0003288003d4000012681c0402440c0c0c0d9046c508007500c0b50b61074aa0b0002c0da01d8070351150300c07508005000c0c1c50400031680a1402410500701290801c0c8181c2c0644011141000d116400d1824190b42300c2c1d00501405810121403e00250580c2c030040d040c0e00400703804844030340c0000910701c08410300400051245c81507104000319040d9440b04404c0210101c3c852195083c050001071159001d801d82e00007030480703240180104da02080d02e0b81d0b80d104240101750030030069907000b58040768411684c001c0310001022038081c1086450321464014103c80024400041e4101e214400b181d1000264001e1000181e00305100680320500d62a1440b56580161b4203403006110301c034003141001509200c0d458403503a16485000704954a00d0041400b90024030b83d842e4016014040020948c42c0c003901240d290784150300001d9040e00b001c0d005803800d103035803407900700341e240500c8240030440f400110b240d040070f1200c00075503a0f01c1c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 349918893 1250 349917643 349917671
    0x7050c010b0910360c090e22050114040305090a060513030f0c0801140106140c15060409020414010e22020d06020702130b01090504020f180303040f03050d0311040b030a 74
    0x1500c0e0402034101c2e1002c409004801c1217540200a0030f545d9a41360218140e90703501100c00c44506680e280300c007118485c841c084c4910141016100e0a20a02c0046403c101c0c28000c1c040d03581e001c40782540800c03000581c1c0f04c014585513000c0c60190403607003455803c02004205050b458401c82c08002c00500c02444402c05104143d80705900800000009120540e40b00002c076098904c288583c00100e8a4154100d4043e044a000e50342820140001400707021800010b800039004040c0c1000c0c0c0040e625070180380540c0b500d001d048401d90f030002c581d40017545000c240d540100300003412031151a201092604c1500407002020b9803040d0100d600d2900b81c025420800000e1142900c0203500c0f002001000c260724a081c4c0005ca1184026214800c0c190307510000d210a038402e0340d003c1030140408205090742075010344072400f098603016048134100b07034a40f03c1070170325407903542c00075227003035000c00440b074106030381030043c072851403a00800141041d260040107181c60001038814403020b41c03034a009800c090 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 349920143 1250 349918893 349918949
    0x80304080a0f21030204030c0501030209032a0612091e0316050c040e240907170a05340303050a1d0603070c03020615030703120c060507050c010b0910 66
    0x11a82e0300d44440309141c3c40724068000d40c418803080369a00355520740000d8540c040d100b81e81001c540503000e84681e954104091014071046484040c142003520144038084e1940b9010b0082c00c0c0d250035504d83c480c20102c8165142060840102941c410241313903032051408080191118490070a0300e0020030070301841c1550603c6204490180c100c0d29100c2001c05200c000150340208907142e000324074240101c1c1c20500000d0100310b6203598103503c007690822200410507021980c841e0000252444080656501c50800d00030610204200c4030344010a2003011f090551001d07840700d1581102d01d0180b440e58042d1641c0102404030041c01204275019580c1800c5000e0004289001400950769250140d4050904081c0c02d00950052080700c0001740300820705550440c1d4140010010280c1a1941da00d00c150010240e04007020401a40f0859002071064002d0500400080d04c80c15150100c4070740e114215a81007a401b031107500c24000740711045010480380016540801c612801c442e1890020111103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 349921393 1250 349920143 349920173
    0xa050a031d0d0602041706010e18030405190303020f0c1005091906110705010306050f040507170906013206030c1c060603050c030103030503130204181a01080304080a0f 74
    0x110990b0002c4a080060b60741c020300c1642d40b03a03103c95841480000d40b056035032909002e440301e8030223504041b0791480c0d07205440f021050542002c0701d192a032030b007001c05d00e9640c0c507500c10314841e1082c04040c810150144118806022410f0003402d080844800081407032481e500044103004000400c07801d10348640c2c090325500d00040e00217a42581d5141401060724100d0769036002113004101c4d01255130340c882d020300000c44800400c20030015111100700002800041c001c4014485144c0252031764881441526200d07403055005030801d0b43c5050700e404072030500140c0c500710420321034680b040c00806000481d100d102c004d6410720344a58400c8410203442c891503444182031446084040440d003580c1d0040010355115036010300407615294003c0305503000030f02004000c50001d0002407211440d6a03064070303850b4002880403440c03a2400402c118604042c50050b58001c581b66007100d03454031610354160040c80c103403008500e454500100b4a40300c003000c4034010182070045048806204090b1008002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 349922643 1250 349921393 349921399
    0x706020306150c070602060a0b13050a090f0b01031505061e0f03070323030c07270c03050f060604060c1410020a020f0f06150d050709021801110a050a031d 68
    0x38400950721507030780d84c055510a0b00018410000016920011406542580380010300f000b4140c041078001c000c040e240c010180c1c10303950303a25000c0c0750208641421146400780603000c0d0610650550802c0128401c07008030024165007024180b01003516201244c05010800220310440e43d070311100001d803100f40000c419075251080c0f000c04002d0051114890400020303030b072780c41d100d41440400856201c4c042c4501841040d0000d050400103c080c1041e59015020810001481e14801846100449040c0c5031120700007035542042183e000984946542c01c60801c4488604061411a008100c207040a6000f4440c000320440e841900500308031040101140317400540d25800030031002076851260b000e10052030f201d0b01c40004220302012501d9400341c141c0103640c1c040308240c00305100c0402e0170306000b100c1502c1a01800148805a0b10107400b07280d00450044908110310800140545507804c0c03a0310207600600210000590006031032408140d140c241400b04a40c02c0351150702d03481c2c1141c14650 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 349923893 1250 349922643 349922647
    0x30506070e03061506120c040b07032111041206181a01060f02120f090405041119080304030f020117070206010f170a03030f06031a010f0b0f070602030615 68
    0x30141c0e0801c1188600c00d1003541115002d50310700080a0354a008942003640000301080401c2169555516240c4e00458620f5000c2c13419948605c00e24484d80076442c1500040e003101108121181403040d540c9149111010511032160141e841c505648030302c0c410742c5090002070b0700c2c000c10001942c008103511f03160a2410300140044c0c2c24910f100605142618000c8041c9100204074140206c1c2c4915034108140e004000ca000c135140394203c1031744074040d07510922100340803001c03240d1b0300e50103078510442c031882074000d503c1c1102003031101602c03030400580407200c103440041c08210400401d0ba42200c2d00030196040000d800e00060f40c4844203c090441320a4150301000440da4000a8450488640595041d495503680020710009070f011044004031350814540900400c2c440d4203c43d00300c2c2c000c0303800080c5165407a904c225030007c84d40b07120a01801c814004006001c1d29140c001c00074001020054a800061104440c29105c0c00c000240029808408a0070949440d1200d1000311841c00410b6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 349925143 1250 349923893 349923901
    0x306020d0204090c020d0813021804150b01030204061b0602040f080c1302090d140f0d0e0f100c031101020708030103151a030703080d021e190306050d021306030506 72
    0x40069405400340c01040ca0604c07250b0f15040b44005400d00220005990305200e42d1100c455210b01c1d116090000e0364444410040a0643d4002c5124580580e200e40c684804d05a0701420b11030540d800111628145032040c0401c0007529041006181e0062444a070290b60071403600e01880240512303003101c00071512005011400240008090b00850000c9600c8694180c0209071201030b4450342c400c29030004140303e101c1e00080c0f4400c200340f010055a00c03d5504810032407202030301d07080315800c40c0c1001074038040d0001d076941043d03030f03038a007440303d042d60080c50b14070b00390b0400341018141440042c1004091448040261400e43c1560b404c1d80d4010015580c03540d50f42403150031500040c400b90902441d01000745072007410b801242d030750681c028019017861840c64854207055049003060101c00c85d020003600c030141418042141c0741e4801c41c0304164079000e0040050812200030948901858508a42845641e58420f140c8040981c110f847c00c0d952035103441c64401520840e403000f001071080754140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 349926393 1250 349925143 349925167
    0x1e14030307080a020304201315060908160e09030702030303040f031209020a061803020406120302060907080c0d11040c260613180803010305010f05131505060a030602 73
    0x158040c1d80c0c1540c6040c807545441e04401d04901c01910010010400c5120f82c581e18a440000303e07640c140003e1076050842c80d08820b50b001c1c0c440c2c8030b40944048a55943c14458560001d0984010b0106800240b4941c4040c900001040400d40902c01c8050100c5000400b1340e2000c00889007070030f60142c2a20707160308091500041d509501d6104a022420003124010008000d11401d140c241c0c000304190341070f61800380151465058042c0d540c2c0746030341c400700210140e144c2c0e000d140000c10805400800040050400905080c1d003e0702d44d1440341c1200314100118900001d02c9410b24104903440000200c440c1307030180040014400c0c15070041d08000b50308407400c3d08000c042008003c00204110328070b4074880c003048a01000c950065110320b01440ca030342c818815911610310702d0400240c0e5800942941c43c1e0507102d4009034011146691101d648a6000481d0b014140e00005104282c1c20000e202d5603c2d010003020394201041482c1c0d035800044d000d0380c1c5512135000195000b180441d9904109440c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 349927643 1250 349926393 349926397
    0x309121b1410051e041509050712050d0207033f0e01030b0303090108010b03130816030201140114090405030904060807050a050a05010c080904090803090609160609031e1403 76
    0x40140d068a0000001d20400078010b42e43c1e6520610307581244d01c1d50b1590390f8401c000d0700e07050300c40071602d0307441410400040e010070180d801303012550440703440c170410340c0740c8149401d21004a8100315003002c541000041c400c0e0290600740b10309064140078005001401c1c4401e00c400e503d2001d041c045018107032080300e42002c542c150801080ea02402215051428185d076407040300545400240d4900040081c1c2c10064080e41e0040540c44900040c0c000c2c0d0b44610307003681c11010385c400c400c0101c21151803c040d02486148601180020b05541561410200a03082c1412044503409485004d00080401005000303c4411260080c020040c198440001680c0c440d254003819026140d14007000ca0113242071052082143c2d03051b51507001c404425907601503035400012840f03070030a40301d1075010005544c0c0703805144110865002000300345003650006140482d64448040e241590a4050049646c400000000d403a000b64440e03042c2003204e80c22100d41c6100c440c01424001811258004001c00400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 349928893 1250 349927643 349927663
    0x42901090e1606080906090102041d0408070f0c0e06031501031e0506090a050609012711040906020715060312111f090c060810060305280203160309121b14 68
    0x812501e1a550380c0b4989402c0703200782e0140f40350010b103c80500083e4007218bd11140d2052241d00c10074200009991103032100b0202e24811101004030140074005407103054126036200c2c4089004000c91000e03d0a84440040107000160181e042c041a16400380300c4118110758040d8400112111817810104840d12450002e808403424000c40c80410706922050184001214191403414070341c20a40078001d0cd441500d903001c49101500c03510401840d51640704012405014030005603681c5068a0882c40c4880c41c0d000080060385805424404142e4684044e440c041c09030404014000d0002500d6203016201c10302c981081c02c0c115502c1c40805078542001140300e208403008000e1985078403041d900c0c058100c501c0c1d10051900442001007074442e411203034215000000c002449020340722500114450b0380e941c02c408503000802d02c0840e4040b60020890500b031407804010340030b22540d844080c03041d16510502082401c201c0c0c4441480d041004c03030749655000da0003400b40240000507584900d40704c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 349930143 1250 349928893 349928911
    0xc020a062f06070c0f0b15040606020303090d03050c070b0103060b010905030f121305030f01060302010801050402120103021005220f060507021f02010209030a0506042901090e160608 80
    0x2111418071240aa003a00a240003681c002d01403503500d80d40b08540d40c1e074102c5815074070402c01d20701200109a07a00032844c024403d582401d28114031002c00c4c44240c8030300e5804a411580100100201c480010540da0110f144901c1e01103400d454040c44140c4034050804080c2c1240c03d50000041005030a40c0f00190308a004e0729600ca21507564400c041e140c3d1840caa0003e825007042d510450b0121030600107101c00103600018180094403200030902d440050a4860880d0795140d44c10f0007507607004030b0403600501c0d0031102545803100c1004144410303001840b0081c021503100340c0030400a8051420745100e07004841e41140c4807200860400b0b10400f2034420030411404098010408602c01c80444801070303005011341601d0304072615900c200010203241582155403c0c8107624030307950280300354010140180020042030800c0d040100605440c1840070142d050100500803041c0c610460450446181e0a4001502181016020709000a01100d034444081d00840860710a400911240c0503407148 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 349931393 1250 349930143 349930187
    0x3040b060d020a030611041d06010216060c081608120411010e09041509170a03060b030601020c060703020703020910261c021203101502010b0d0609030c020a06 70
    0x101003407000900c01c0d8940a500301402c50000c1c0701052041c0c0150304104442e14002c1c1c5000d607100381034645010400d016010600125042c03040d55a410441003010068a03c000d03c02e041ca031440c017400d000003400c03009103280030106900502151384003a4001d256086010281d4a5101110880c04070000311812a507101c0d50125448203540b00700340e1090003140142c81c050640c1c0b265101d003032080440d4010103600316101c204000000742505c036001c3c030820318116660749030030317030b021028064034500d4000d4640030600340704100f0140c2e400507526070711020582d00d042d9590900d0500300d080140c2500043d4000c409442030100e0800240e5110040b2201c407080100304d1201d80310344860340306481c841c0c1e0000f54000384020b50180c4440000465031800c90044486e00c002e10320307505c00c850704215942038000544050400c807440d81181000034501e0305d4402003040011501c0000d412404002c406004140c0c1d5104030000c2501484803050b0480d0000c0c0b0400d650b5650342e42c01020006a0a0608266010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 349932643 1250 349931393 349931401
    0x203040518040b190905010908090a050d08092407031e0c0b06060c0c120a02030613050d050d0605130f150315020a0302070c0602010b1c0b0f1b0c0303040b 68
    0x11440358140101c0e070190050f4000c3d190720300440c43d00e54800c085040f07840c0e80d42501d600081c0d024030503c02c0c2c4922519840e901c8494420070000360346599407107540641b0411414000280c01c03482101c0c065074044603900154609444101030307821408940385440e84001648100b03050308000f40c0b90076241012020b4042e2072408004482c1601c040d003000704a454408049040e40c5081030140194000d481c044502991a040014803000c0441840c035a59402440c010015070074203020807070348401d404200c4041c502240d9505507941d031060302d0803001c201010609480c0c1d0303d2030346c12540040c10010030103984a01560300c200000c00a10941102c0503181401441e100b2041112560481e0b801141040820b00800d51040196005290074000c0550130024000001c1116000501a1000d0b03400001c4084404c4240300b0300034102c000d0840350041e62007080380010000b210301940106801d07406100317611a48040000103000c0c0000c1c068010700030940801e640d90000180d4031403401204441d01c6522 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 349933893 1250 349932643 349932679
    0x21303110a331202040b030406050f0c0315043309180f060603060501240806100c031814030705060c061b0d050f09010b0306060f0d0201030608060702030405 69
    0x541003507001c012002040b841402e1180401001224080a042500c0c03510002d0002000700d0740250400800c41201205120034001a4455149d0100c1d02c40540741c80c60402c03051652407404000e0032500c211001c10920710854480e5000803541c4d140c0e8518151518400401c14091040c040000c08000e007035081d40060041c031140103c25039000f0086410580e602d09444400c440c2c20f03240f605841c100c0e111a030010003d40d484c0702d000d00a00d03032207102c080304240c0035444110100c0d00384640c07004c00c10081c0900001c0d5a800c5c1c54613004c100c507828000581c45080c503040c0c80544401480401000543c40000f82d121500600c00c403840c0001c400380c42d001c50b102c00401c0340d42e01072542616850391000d000900a41c40b4410340141800301558007138140041c107080d50007500d81c211400305101c0001c0007444038010b024011150380c1c0100302c001c0c003078a18105021a54030900540b940344601720017070b501710959020b94060340152040100b561080e151092029549500c00d1107803034000c1040d4a500c207032901c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 349935143 1250 349933893 349933919
    0x61b02060f0f0105011d0306012903072c09070f02070602030f18030f01020a0c0b07030504020d1e05031b0f0706050405040c120903090905060d020102060a020c01021303110a 76
    0x70b2000c8826000716424100111652400c005805000780e812203441c000980d4200035641c000e0541c203005007050400c16000b8080e20113030300c07418510440e0a00034444016002440148080307205121048406030368a200f95052100003d9560003255140a2000841e401422900c0d00d103400d4080741c08032035903000c00b203030b03288580303107182084040034030a8400003048482c0440941c00c0040c2180d44210f40050302c1800c9910043da01070203c0d01060040c0100203024001c5a0310074a00c1c10200814501034000c03c1241c074031000014032188141440322422a004890054000c0e00078044035241c0341280e160724540804201c450200d44140c1002c0181c04000180c0941a64415a1404d00300b501c0d14080c040604807480b204800c0c0f000010b9500f60400c55440307400c4126000366209000384e4130b0101140200c1700f0243c20311307029a07110701040000d80d80024240e600041716540040e61065001d410701c0c0240260306040c102e010211034000284041d001180242d00d030704442004030581d0703c1180308001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 349936393 1250 349935143 349935151
    0x6050906011b12020f07080607031d100e120c0304090e030306100806060712020102090f01031a010c0f0b0103050d030f0c08070c0c0f06021b04020c070314030403061b02060f 76
    0x3045402d803403a00043c0b00120403a80d00700c054011a4201456101100d042c04142d41000300c0c581d014904020700a0b03130501070008103400388510348d50220701380c07500c06490300c80000b2000740300c644a041c60317142c040081101440050943c076401e925200c03011520303501c07a400380c031842d410307141040c0440e1040d0002004072405154020015071100c003482106031000b003402070040b684850141b118070041111203d10902882481d800140c2c5c6045000400c4001540381c2400b40c1050f103080d00819014404609002d1450000d0901c48102a414a442405001c143c9801440510b100b0000400c12000289002d085030058034240081e14955a6078006c494031402c5140c00600f041300400e5807507000d400d50b4081a0f0103410706200d8180c4078800700844c003000f40c1c040401680442034841d07802c80d1b15115400000c40844040d842c1c41c0c442c440e182c1e596846404040e1a204078882d0702d40100c50104100e50096a22280a0144911a0103070480040400500e200540102000204a50600000c4501c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 349937643 1250 349936393 349936427
    0x708010606051c0e03030f180d0f0513030501060b12130803060904020d1a1504090b0c0306060c0f0109030311030f01150309050a0507080d050307020d0c21030605090601 74
    0x20400000c004860100301400703100c50703c5a5641c0b0032059481c0c140300461203102e5107130f1401c00c20304140c40581c0010900d110420307190b401c41d00301429150341c8181d1108424881d4900b142d264076483c1008680d24070942c4c0024840e602e48040002c05036034100160441191070701d0032420030356032913100141803c2c44a01c0180f84d12400c2001500a1410851043d00640043d22040070450b0950381c003c4a40080000c0c03020301c4290304108103040c0130000c12090a12015036041c03040011075074545000c02c00140c001040e40310f0110001d0030035125401540c648010349801c60303400000078201c0354000c4c042c0c0351303003a40002d08040810050001035821240101c1c014458291b0581c68540101209000300d40b9540416455601c004040b80b410000e00265a02940242034000d181041c402d01c0c0080c00310070002030140070f0041013580d5401007030034140161a414130b200101001d190891503054510440b018410306200c03075011180c2c0c5a404078040c1c07001a601c070907017034882d80010b6440c92002d01607200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 349938893 1250 349937643 349937647
    0x60a0c0b0a020d0504110a14060706051b070303022d07020910090e03211b0a0c06290102031303080708090a060f020c090c040e040c05030708030705070801060605 71
    0x1000810318108554414250000141018100e4014805942040c0d40c02d903010401170b02c414000c2c5c0b5141400100800303145500c07855480218010070841d000701c41c0c1c090b00080e900c500180c01c1340310b50741113511395604103460b0565440803854050002c0d00203038000c00000d600400e03270500081c400c01c0380841000a0b213142038144200c543c00c101005600030030030340345c0c0c1c0f01a00c0002030a26240c094030f401d0103001d601454541c0740c0c1001c885820000e6804150b2803e84400602525000c030680c00000c1102e010200c0b5030301c0340240000d940694000e817004010901d801210701030004000024084043ca02d208091540b000400490381da0059045004044075994000c00014203500010850b0500c48c4c20814106041c410008540c44050350003440482e00324814004019030501082000c10811030300c5084606014202807080d01850243d07007042c412050218041c440892551001400018111580345455071f065a4903500000d02c112524800c071640850060010700558054400301da580c64 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 349940143 1250 349938893 349938917
    0x13030e06090109031e050d0908061f0b03091c09210302060c09030c0603070801050909150103080d2904060902181011010c0c0b070c050d0323041a06060a 67
    0x101701800c100049132140d8112a1031400042d0090051409400301d948602a1441c42c1c18030440c140340004148803000f465950246502d5130207600a601034900103007035a5100e50358060251310700f23042c100000c0310b403500c0c81054801d083d030310600380010fa9103064404544901500c58060000144410040258000d01c3c0000c0c6464105405010b80340f000404441c40341740c004020510540c0150340c21303000249800300501407410082007694106e0402002005420181e000301c4122203010302004143d80000924801103090036003220031061100500408107007120002104c2001a10034014082d07800c11000180013400e62090b500861080018038015103005030800907100001c8180340c007440084220200c1070b079024402c04980c0502c0782c50f81001c0d6040c904100140c280b0003043c5104200f800006200061008202c4000b800720a003400b01e041074541d810080b000c084100d08042c0e00d007000c402c110612100c0320903e00b29107030004400c007158450701305100c0341d48030b414041e8000c501c44600c80c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 349941393 1250 349940143 349940153
    0x1a0306042306091005060f0c01061d040813030614071101060303021b06040f081f0204060e040515100302131a0f030c040b03090d0210060513050603120313030e0609010903 75
    0x1d144d0140f0800b010b22403140e11200040c116030480c00902420314000b1a07480a041c80910900d400343c0102010503a4006014508038240080188001c01800340401c6103e00400d0280640780510b5220300c0500034805400480802c42404480d000d00046000c0644070080344188100d1f0300342c80c2c155000c1c0240e665280e044001d0718446d2426a50004002c01c000580c06211045840103805150050b24404040802075480e1050b50103284a03003c2c410481004060781104c0100340d0342034150b40c080303401da5404440e4508041421040c0d60000100e0b51a6a24aa8141e00412508400c0714844007800d49a410040d80400d601d1f00d500446e510803c81050040f140e0000741d64048000210b42d840e15480340400302e03003a0003d0b240c4d84880d0740b149114165541d01030007180d03514662050108038140ca4580012091101120b0b10002e5550303c001007101c50303c043c80300d401c6008003d140c46599080c11010b00380d008005440c25000150314040749031841c6042000c8031603000c016500c8011032411038843d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 349942643 1250 349941393 349941409
    0x605030c062104030f091e0e070c0b070c0c0801060302060708031801090b090616080112030e0a291603050c0f070b030717010f0b131a0306042306 64
    0x2500300103020500a01c400014401d80183c4030324480d07a11449548004c5070054039100b041e810070048294408020102c0150b0200b0480031114501d07080b000d9038a99240036207400d000e61001178404001c050411032415000224810741c14032641c0400c042c0741c0c1d580c81d02402c803506804000d61113407042003050040303600e030f80c0690b40284521900342028801071038024215101c0302c1c01258104050400c0241441040c0003055111500c800065607a03140303a42d0040c1100b10502503841c92082e0a00c1d440709144c418800c502080002619a544007500da5048841ca03800c000028000120b1406036a0904d0f050b03403040e1134110031842d400000c102059075054406801452202d0028440c5000b80c0c1c1c06060204100b400905101e80c0c602c0c1e507030a081900071319641c50203582c003d08031240d10040141642c1d98400900310303410b040455803111084040414015419030110780c00c1e0281c5071251408103424070086020347e070104ca0800401c1c1c0501010b480c01040c0541c1c2d40d03038031070fa4040050401d041c0301d40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 349943893 1250 349942643 349942657
    0xe04020f03010902130b0415110a1106030a090812060a080708030f030414030d050f06010c0f1214072009060609090403120c03060815010b041e030f0b0601120605030c06 74
    0xc0402e1701d44e120070311040f40d604103034840c0b504007940303c031402c040726007080071151103640d188003410407504151940b41c0710288014103580500000000143c20218682c040064030b0350018100380e0b140315841e4140440300c41907440d14030401450800103090500000e480044410143c05181000c2c41115050041d420041c82510031030b0081c0d0300602c0c441c1051006080d140c850701d070005510b040001000021690050080341030107600c00c0707a03101090101580440c03690340540c000a01101c15036003201c04278401e40f0703070900000303022401c88104088868070702e5100d4110944050ba941009080041246007076a015411030020050568103092120101d6072081c002d040817000300000c50400002c455803030f030a400009960782000e0292640c20f1210100310003080c28608003a5042407510011446640704400710051014803d08801e0480c420b0f94009581280b000c40d811929130904c0c0340e070031400316030007400980040403841124040b841024180c6202400401c40c10310828288100d5500031300c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 349945143 1250 349943893 349943917
    0x615010306030605090a1104020901022104030501110d0e0616030c020a051015050402030105030303060d0c030503031602010f0c0504120f0b04050a02181627080d0e04020f03010902 79
    0x1010102c0800c607240034450180140000621564031142000c0d009460314103c5a84100d004000d43c111a03a4002035030074030810351000c0031490480340c6c3d844001078810f03680003d0040d400e02011101b44414000a030100b0102d0450502207a480703211202c1d00d130741c0211000c15502015800704064580300e540240078651050044900800c01078aa00d440c00554024901070316849201c4e4130941c11122030024010501661b0550075941410002602d0340001001c16002d0140005a0014465446d031000021034102058a90702d082468140b0380c1416480102e001540c00d00c00f500320854221b129540d03400c0c40583e074160505041401d03891484003040341c00c1d2142090940c4c00c0740414821424540154400e4000300903001d101c4c81400800c2d07095010062107407020030b040041200e80c010062010400600d01400d0f080c03600c00700124003600705014031400d21800c801c042a00080024010060780381510394082e03404200c01000103a20650048103e4801c0500040103d0340d40c50300541417980b80d403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 349946393 1250 349945143 349945151
    0x6020a080c150c04060f0c080322140d081602060406020c071e0303020f06070816090801090308040b06060705030714011e1509140708070e0d060b0901060504060206150103 75
    0x41c11100122402c161610b008000c0002030400641d078011540c1e81c1001c81c0c03400e00403c8001da40d19132040b980801041a1050b510905500401001a090340740c6410f0b4091b00b103c442e4002d5902081d5211004c0100101040d0b503030010807240c1580340c0c1c031074814080300d6004050a40d510f9072205d0180d0480c07145005036104140e4046071460200303110928142e0f0340d6a40402d8107295090091810300b94000e8044a90010020f2101a5038000b481503800702d45440b140321404074a0004a600c001c807a4400d8a095203840344040415900c001500e01030383c011406000551038000c00c00100707100b0214000e225034401c111002c005650440a042250b500800008500408010800d100745115503042d01003552036982604101e2601813500c00341c0800901001006801c0200404040c000350a050610850f0310006220038820380c243c200e500000703095031025000d1450210080c0948018482c4200794050000c10b13030301d1040054600305d0703030664020441611008070380c80c401000d81a07207034105615 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 349947643 1250 349946393 349946413
    0xb0a05040606020309040f0501080a110f0d1506060203090627100f0f030506010c03080402030c1f200c01140906030411120706050301051011010908030405150106020a080c 75
    0x1403803003000010b15650b0040c2da5500501c0e03003008200c030700342c0356a000b0707592402d4010300c094040019501c01c125803103500d45a01c070b05807100282d01580004a4240d21080c040c4400e03017045030700c404801005101020500400340c994805030703160702a1034540b6400803010b010011244000407450814400c029070f02c100203030744440109070501805208400855801c10320032442c19031058040e8205541c914040000f82000000204140346031800501040301d0080400d06540d000c2c00b20750303403003900200f904c2d5440d14501d10109495501000d0b50000c1140504495601c01108801d602c00d804c210000e481c0710030b540001034030013030307000071164041c400284406090780c4c650301c004500450081c1803400b0400905410041c68680b080d04078500c6820100c8100501781c3c101003503e05403072048941500000450340122070320600c00602d00e903590300344403280741031007801001503010b07600401c10340b2894003803180184c104c100280700d00c000503840000d100000c101190041d00b4458a20b4007541d541001c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 349948893 1250 349947643 349947649
    0xf2814010509010504150605061204140a0c050a06171308040305160f06020c030604031202070507030f02010318050606040f090b0a0501060e010311090d23060a05060d0b0a0b0a05 78
    0x7012103154200e0b03907586042c0030501846107000001c020910f02c0038000141400302050701400b40740f44105c140c55981c808202004000200c00380c001b2036600c2183d003580b000342061000a203c40c42850700903012410b000c0342a522403100600100c40160982150340c45000b05030304045003d0b0b0040d142140d0600c4088000b40050211901680080840051085c200715143c507410560340e2000c0305541c0301d0303104240c0b29100803d00c244e125806081010f5003039034071410b11010b8495040001c025015841d808000c0000384486d20901d14002c0e80d08003c20f0030b04050350b95500750401130292440c0d200da00061403d1801d40c03c4868000c0c200c1d600030814280c540d030313542e89200058500000d050786810050100e29070050756000c0744202442d00340060140380e08481034505c94644218040d400101e0440700340f10005643c407449100006c80740c0c000c03c68004401d929584295001c0f00c103141400080380c028941140300000c8280c221482102d0350701c0b0b07105080010105281503a400c50342508000449a03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 349950143 1250 349948893 349948901
    0xa02060703030203010e010603050f0406092a09050f0103020a1403070f09020304020102062229070206010f050d3203030a06051c0506041502040305100606020f281401 73
    0x141c841d480c0582c59504060220700c0d0b4100c143c00c03000406180004000d010030b00a484c0380d82254100d000000c07450241d0a01c0d030f03200340f17100407000558040b4450480700d10f81455058001c413407440c00708100584401c2c42940f0310203005c0c8406944134600c00403d00814030452044203c49a00400312041c1c282d4603900c0d86080314544e4030554240b50301004000c00d40d6010320046501140035901c4035461140398100c03001e486200b85c006030000030304440012411407003a000f088410325016100d812880c014034025030702e80d0240070f02803852846c7d000020340d41c2045440c8885880d8000645c020350b500344d0240f0105801c2c0051090b4519540045da25030300c1c10305000550003040070301004546982441c00388075072002e074400a07500e1014104c038401c01203000800c1039504550b110b088612a8191030854201900a6401c05001d40c010741c90541202e01c02a1301c000c08444c038a400b41c5004044184495071100b0200071248900452000c1000648207580d04004085104041315822903603441d101c01e08407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 349951393 1250 349950143 349950157
    0x111b0c0306070917070b0d0b0d050f010e150105100305070e1f09050d0c0e040302030c070f052e0809010e0303041101030b090115080703020c0f0a02010815011409030a0206 75
    0x4540e00039000d005030031900241c04c10355002840100380c102d180c0500401c103841103110b0201c0c01540c4002c540556598500865055a00081106d0908001c4400c241c02000498003401d054811981012801000a00313118100c0d1401452031001e415080003c1e005400f008124400304947d03089e407070005668520011850300301c9900d0400100360446400b0b00910703415002188598049200c04000420101400d400d554171000042c000341c8881ca130982c83d50217102806a25030203254400728034ad078400a19407040340c404079a0306c9103c6804994a00d4401010309400040360b038413103500006180545407198002d058900005001a81c85418078110b800c1039804642109401401c0b40c0303590303414061001c5108044503090354a516116000031001d03200b14050b01800769910004440900136410340f00d00c1c0210f181613030121030204c1d9000382c44140260b8104e0206141c4808603810401642c0e1403401480181c4a20601e210200e0510081d50801d02401d5414450070003031344d0058560740701070210 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 349952643 1250 349951393 349951397
    0x90e241206070809070803070f060612060f0c0e01020c040507050c0f07090f06080304092c06070f091203050306040e1204170607050702041e0c020a15111b0c030607 72
    0xc500b400304008008607005419006983d01c090014000c07100040120b50780c2c29031040303111031189018544000504681c1d41b20030011101158281c06016064112400c840c4224400b006030082ca4001a1044090000c0181c0180d00030f50394124542015806690040702d00c1c01c0060030010005402454052040d01c03451407500701241c10402511136010b00f80c7d050b01041018012142440d89080d0b803801103104030860709455a00302284200075040c2192540031000c3d40350425502c450055990310405e441d03100c0010720107440010410310a9061905407029a1820400081952411903c64001030140350340f040d070315044003034804400c2240d05010700c055091a034445152079401d50400d4081c00701240c96801c170008101aa40e406021214000c2d4100d0740080c22602d068101c803903900003100e05000c500e2a1503000c2d440280c001510001a9100c0d01c584502c13412194122070580c0e80702d5400e2040400e040c030420341e191000591101e00a81841d080399a448504000a807030903a041d151440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 349953893 1250 349952643 349952653
    0x40f06030302060c030708041709150c060a1a040c021c0c151b120209040e030306270604050601020a0f0f0b16080711010f0525090e2412 60
    0x10103405003d995807140e80890f9590551610300b1028000d5400280b009003402d503100e940034107100c41030701592010000079100200000180611080340d52008620103814804c080028950b4102d41c0195400b4071342802003004081180014080078107807a001c8c1e08198002d01e60113541b8110508000135408403140e468640d09603450505c004e000720b0301000802c0441c103100c0d18170350500701c103e02d68100181614041100300841d40d4020000d000c2e600510b5880360a00b5000401c08000001540c05454110ba803038103500c000e00c00c912208070302c150441d107100004200140807841c2650200350722003810300544088600d20303607030740c0c0c083c1c0d140c407030b0072188401540d801c0400d1005a004456202282562410350060000000ba10240f801840c41c800c02400380d6064036550800c0d0459070007040d22704018455400c0c28001080490002d00c012030707040d0003140849000c0f501c101d0720041103442d252a01105900d40f00c405039500f5074000c110210180e2071546a0900703440d403100d004150342c50040544 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 349955143 1250 349953893 349953899
    0x60e07170106060e100206061504050d1a070c0c0b0a0509090a1b0822051f0501140904020105040b030a0908030403050c01060f0b0f0c0f1606030605090f0406020a02010b040f06 77
    0xa049008241d01c031502070000801600a000c6e000144290091390850300c0b1206030b5070032031802c5d0345841550851600001006842c2c404c03c034003401d0010120340380c081c109525546071402280c1a650400028120f0910503000300305103507e00000b006901c10070700d0240e28003a0000b010a08501060360707941100c030398801c140c418100c25103940b00482005807034030031440d080c81c5c0d940300c100600704180800340440c103049070010844200804071403840a00960b0032615806600d680082000b4800d101d40010500e000440d02e103841f00080d441154161266410b1905200450b41140c0005007407a8103a03a41710034000101e4401c0018500c00e40c860754072595503001560000e030035900c5503484000081081d0303100f030103107c512070144c401003055002c0e2581c5403402c1250f15440c10100c8900a28903029034010345103d5103003c4c885405803003180d101440740700d076104103200600b801105c5000f041c3d442c2c034000c00c0c0007840039001000384c0b541c28030000c903c032022030001404a480c5d0092031401c05030303249020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 349956393 1250 349955143 349955147
    0x70602130e07090e06090601020109060606170a0204080d05030405010b030304030803240619090e0c0702190b251709030d1d0d03020f1609050604020703020a060e0717010606 76
    0x303154020000d03e40b56000c1441d2281c03c1003100c201a2281e44141d00420004020303034800d41c0040a00c0b5000306007070003d01d6480070003801a081040c20b40401c80d903a40c0c0065400c00d0036008803022a1040c030028001a440c1001c201d46c6c540015000712959525260307503c4c400d82d0104050f0000d58080e4001070b41c1c0c0d09105400301c075403c3d2010810120144140081203a5648080c2524105010080036100f003e40d04201160f1400d2241c0056411130100800d00c6161051040900902842500d40b01c3c90903c0c5c0d40010045c000d250300c81c4844851042218040c0300100c00d4444e0885154503c0c0903c2c1040260742e4000f442140303031074101c245c0c0f80210b40100340346410032040d000c51110f801d10400c1c02c0803404000b10300144482c1c0d0240603030101c103401020075100700b2500030b0b144075400039964000c000601c110f14000d050702c244901c09050070041030355071a2902c211805103601d07800030094080c4503a40e19001c0c000c0103034880410701695000180590082c1d40350841c2e121030074000601c0600341040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 349957643 1250 349956393 349956419
    0x212030c090f030f0a0213150f061403131104021b0c03120715050612070e0a1a0108070815041a0a0f0506040b091c030507140610060503090307060213 66
    0x901440f0303501c10050080d102d0300c04200c000816406846000e012801300c1c000318060200845810f4a26081c050009040140e088406065504a54820380c12094142c0d44080c1804181d65294a080c05040c1160001e0400050401800000b42c8054106120100c0500d05041c10280505181c1c0082420b150b5501e0207020702160b1542400c03a040c1007814540b14199400841c0c030900c260b075980e850100d401941e44200c0c28003001c8d0007404955030640c480040320a5914241c41c0c0c01745203818541c414080c10035605041008801c180e5800c1466075400320200e84001d0054442d0400c0d80791070b006092552254081d017100034022003901c001814150341449200d00d001d034030000001c42242000e20a950b601005c40c3c046501141e8402c0d15050080300041c0d0720144801e18035a0f9000b6046000d041582180c050040341c0d0003070b91042186422202a1612a901103c0310b01d9000e003024400d1240c640120050354000c0341e5007088030b04040c055540c90080745e1061125036502c0c0300b21708041200351001c40e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 349958893 1250 349957643 349957669
    0x3040501050708090304062003040e090d030e01060e0f0402180c04030b0a0b0f060705030d02041202040e0c090c160210230703020a1e0b0c0c07050405040c1202010212030c09 76
    0xb0346c5094a0008001c1202026000d83c4460600b8050513441180c3c1c10400e03103002c0c0200c20798108181c107101c11021b6a500300202c817200800d0811078410000b140610030312049450000190030f00349d070f641e00c1720700300914003d0040ba0300003002c514040442c01800d207030034030441d10590110b5446d401d50415900b8020020b1004800b44d040400c00b0030317241c54114800080301d1042d43c0441d1604051314102e0300b5401114541940d2510100c1c1c0096040c10303600e880752809000341c4040028050002c8d80d1910740301c0419541382c11801031004034080204850041c29943c040c080540f0404010b42d0000313010901d119589000111810242e0168500305220300d03801c0641d0040c514a000340c40d543c080d488008602c0f0241070030304068000c0d055a96405546004980e0000c0100030303a140c000c05006464004035210b401501c00d4010104031400c1038400c45001d1504500c0b242456441c199164085902c0007000728114010341c0000d0400d100780710040d41c0201c848584154458100b1000e015500d00040307 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 349960143 1250 349958893 349958911
    0xa030207140306060a15020703080c0102031b03090c06130302040e0f011409061f151224031106040b07200907050d0e0c060a0804021003380603040501050708 69
    0x814056145d6070510713264100e0301007440c0503004c0c120f03081040c4d0410b0141d6002034400e0000050800c2803400c194000d500ca00e0740d00d040058408440c50704c1f0901030008a070031400d140e004203041c4c4c48516108028240c042c00c89040629580e03100c0d404501580d00f22545c848160344404100103040c0020b00890190980ea0505450340c0c0c074010170919910306025102c810003503001440c001c01080130946001c094000d0100340400c110004900424800030f0007520b0b050715241513181180304048001300685c1c00c61554130010040e0868540080651301617101691100003000001034912699010f458490300030407d00d03003039446c1c443e665603100080c506400e01c500b001c3c50400030760380d80140c00e40c2d0345804510f200150b00000328600d9441c0003180c26260b60b11010101d10a11a107038041d141910982c42655410380c060500442030702038a0000403400c90803281c00003c8545802030047e145a08440401010103440480010940c26402603134161740c1a5100c03001c002c0e840350001c054a0b080b40e400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 349961393 1250 349960143 349960153
    0x2030114060c100203040206041505090102060919020609040b040519050a020403030512090708100903030f18200a0b0a1e09060c0f02100504180b010f030c110a0302071403 75
    0x380400c070b40f201c140c000d0000c49164088041000c1d9150603003610040c2000840740d080c001c0949001628642100d0801030052041d180001d080103004256080c80300207500c00103007aa0340590801c0281e811654031a5080741d52500c8009140d80c2d640a824007850b100e0221a0a0070401c003a21800d4607070060114604a004000c00c10000e40d01004981030103900703141501054682d003401a0400300c0c42e520a4006106407200041d035048160b0014285500c070761801c115032040e10402d44140d5089686041c0020b40814040c4045005000300d925000c684104000c6503008640010b100042250040052494007003a170104058002070b82c1c1e500382940d000f85005002030580010844c6585006250030046144018800c0000810604441d42d500404040c1c1c1035401010003080d0f500700b44140405696200410610001c41d80304103001001c0c10394480341500f01048040d000381448004c50001c2040d42014505c01130014041141118031070750203000058034000c880002080100c003c24466084 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 349962643 1250 349961393 349961407
    0xb01020307020f04140a0b0103140103080403030507080d0510030b010501050315040c02070302030f03030f180d0e010c02040c0f090b0c10090212030c0705010801090e2e020d0203011406 81
    0xe80c0c1d50541e0482c2c01d40e0380e030460300000c50003502440012101112455060004041254206e091704101c281c1c1c04000d200d000b90180030ba040c4080c8006488010304200600100e8400c0d07000302601c2d030207001050300d0600c02405090440308211506015240c00d04c4080c41000009000107004010900e41142903080880644911801d0360111500c01e03a551100c0399002802401404000e680047c16990401120304019480381d000b16490703032001c20040b0010704061221a54041071407002e03002132905a14041d410f581006060011130706000c21440c496005030360b140902a4100403a81e2002c02c1c402000c0c0c2c001e410840c3c0764122090280c020b00c03503403807004000140d15202c600c0340c1801080c4403020b400460b40034256407420600320b0000040006088a0009041c41140c4c0203a880d25416030345d8540c1c41c4101c49514030f280c00f42c1e8020a441030000c4c8a8000c1800015030710703942417120f1000511284041764802200c0108064001c001000a90200d520b07052140d1401d450051070244 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 349963893 1250 349962643 349962647
    0x3030207050405250e0a08030a0302041d091b04110708070510020408030f4605030705041e080f010b040e01020903070b030714070c080c100e01360302130b01 69
    0x40e02e000604c0c00c01c140890740100507510f00b0030480081040348190ba64440070341c200100a5403050240c02d0700c440d2001780c4041ca44880382e00d105d224a60355405800c40782000401003d00007c2c440e5040d0b40a5104da86800d40c0c0c8044000400d1410300c00c9500300d035115590300c0c3c0302c2c0c10402802904581c943c41480200500c0b40040104c070300c080c08040b0b07015543c00940c1250ba030f810320120040041200c80c03024595440031030841b695848455030001aa2624042d102114184000c4504100050007880100040c1034058002141400e00843c3c5c041e0700c5e80c46100d404c0c07030407007410340390107540e0f4442e08101001d090038400d80c810a10705000a6241c0440140480d070b480040d8800c0a090700da0004c0024801c0713106001031642c8071034036090b1980d2a1180c0c200f00c03c48201e1405904100e004140a1844502d01a17541c0c0b0620700c8162103c0b50799601050041d51100000451f40064180620f101801d548030140c60489060901c0080c0c0c00c0d6a0550040c48550308100d00240380c0c039450901d4841d8982c1e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 349965143 1250 349963893 349963951
    0x50609070c230f03031005090c040b0412031101091104140f04030e01050c0307030509011b0b0612010902030708010c0806010507030509040b010c0f03030605091b030105190f03030207050405 83
    0x4500d420b401c541d594481c1109203400003089800386140008000e0107080050401000200c6404803170603600b0385c07620140c0800d544038910445401420400c003c018403042a11103040700c502130305014500c01241044c080c00c2d10044001101e043c201e200301291946441d1060b190041a00088181f640c5004c454161840f40050700140900c0b140741944030311603100c1c0c022540c40c0c4c03140f001070302d803640f0f02e80c82d002d0300603048510383c01d011070750301080041003141c0c01c803038400c5164101e03003003240d01d0320342005000078131100340c4440c4ad455403a070882130f0141e14104031074002800c816000282e204d6009000514900707000c3c04072410000104644008a94040c05503402c04d2411540041c00d0009500103076030300c2c50075401c020207403407e0b042c9048c103054040c0c1c1300074200c0340e080c2d07100415942c0301244520090081030354002d02440c107000500071410701e1071010a00c0c401c6200310f090b405842d6001c1440c10f611a038004ca0042e40108024030550809000d030350b4014110003c84000c000c40a00012903603 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 349966393 1250 349965143 349965173
    0xf030305030a09060908040b0d0b01050a020a020f010302040b0408100b19210227010902090604030b04021215010315090c030305090102070b030709050f0609031906140109050609070c 80
    0x2181d00c40c3c3c004014400c1690162506a510562007540c4036514440e1401d20b81002805402841c80c1011010340307540a02d04841188281d41d016020805051f4200001d5159920b20300e4109a800d1001250101a407001400036100000091442041820020b810360700241126400380c2488503210025024001c00030007a5075560f00400710f8204169840002c01d9a2548065130040840d06040964403801c015481c00f4001511031100b10313a00c8480c4003051b803151265031500308204000410104410307007900303908944018880c5081100c0340c090280b6200500368102800300b040740c0100f080094200040600182c00c0e030007030184501ca611440544170662001906004001408400c40c0e071003484942c0203820301400c030a84a05081d0307030080c441d298502540d4020300c0e6800034035040703107060001d46440e280d00900170030352251703d14150700040c555200c0448815842c1c540f440810350008401502030000d0340000542850244200490403c010703003a0700911409002e00400f16000244000302 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 349967643 1250 349966393 349966411
    0x5130209131109042117070c03021b1201062409080706030b01020c0901080105011401090b0426060a15150c08030603070806040b10060206010f031509020418020a0f03030503 76
    0x2d50f80314209171800c401c0c03590100c0160720788808920b0078140c024104aa0369400050720303140d10b07900c00c041540c009099200180140e48101903000c50454450b090460000000c0c0641007902a008171903420b44205401c01181d041d41c4100b4440c034a40e8501e0314000d009150300d0841c05075450076110300c0e240c0c2d1a82c0158010542c031004080e201e40d000300080f40d900040504030743c1c450341e075078410603000784402c0c040e82c040050b0440b000100d40d817040f001c0784144d403107000110385010720700855001791400340900018600041c1c0014048040309000c428481c0040041c08074203030110720000582d110031a0007909001d289507098501556000c1c4540162070b41c05001c560366038841800207807a160041e8007840d614413820082208000300300b2000c500910810390b015019545030801070b44c440000b4014045145440e0004201148592418145d4aa406c0b280040c420f4036540101c0d09554400280f564882610740c4034a08508000c00c03110010684030010a41703007070444d40c0051240c407024080d9a0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 349968893 1250 349967643 349967659
    0x11040b030a151113061b140c0f04021809040507030c17070609080a1104021303060615020c0d171c090c080d0e060304081605061909080405060c070504051302091311 72
    0x9042e01011840090542c100c010110100c071001f5405a4502000d801c40e400fa14040c280d84940741000d00a4403200808122070364550304c0700c40103000015100a100303485030303c500400003011034032464006020740001488602d52030540703400746184c048164001010401c444c0306c20412000c020076010815070303012030740c62822403415001401a0080041410320078092240001c00c0081c83d07800313070741200c03040360106441001c0c10400340e86900d025417160741c2010303850b4040000952884038481011900304942c5040c408105000350509107070700c07040383c0026070ba410b40409000e100210240280034030700051600784d0210100030300841012440500580b001b00105003000100819a19040600d20860140910303a06020b9a118019103180e07131715400d894000b50b840d10080c0114090035400c200070919041ca071105020301b5500c141003401d818096a000406c040d5588d005240c01050b1084000308019002c0c0100000c0c140c0251030740982461100640c8001113100803a5091020200c0c0c0d000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 349970143 1250 349968893 349968917
    0x906061302090411180a05040204030b010608090a051c020f0d050d0b0d0204050c040e0f091c050909180d02011401050f0d08070303091401090f11040b030a15111306 72
    0x200a030622904501804d4804075110000c00000a54104410011a000030340555280d00340700480c42540406030050343d60b00018090300340a4035000b90004940c2080b5052240c80b82c0791070303050080b413440c0020300d20110100d04408a604018403c80100c14101074021010000c402800510841065401c040c1c0c407290303100403c1d581c000c080c03685d8a07000b500c20300062601d1040d11480754003500960300340054001c04520a42d510808003072241440000401d6032405440503910b41c01c21014030722080080400001c0029102d4451842c018025100c0007410410000704807405c000c2d5807203050085a141081040e001100b041d14241144c0303007500d40340780009410b00850541110484d014080c07220001d040c40406034550b00c0b8000590041590401d5002c10001c0e4601340d820541c0e01506080581e050003000c602c0c400402c2085110040000417010715250100781046031340002179074070401700c44110105030454040ea654942d1151000b0386450b40b54907507914012a64020b11040080404d014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 349971393 1250 349970143 349970149
    0x40506090f07181d061c12080a0603080c0a03110d090e060411040f030309060c030818010204080d0e030d03062d1a1c0605010509130f050903070506090606130209 71
    0x20718040d2046060944526502000003000100c2c10740d811030050340320140c6000c6d401100301d1240c090650049940c0503585c903107001100ca0b034901400040035603a451100100080300d48008146400f8410f014040c840310034100039000d02c90744480c00a440d04030780a08010030b64030030250400d80b5242007100140c0c1c0c640f4004100209080e401c4640f88000026001c1003c0308001444000c6903c60f5035070b92200f42e03c0c0c40c13088509641414004021071102008911011a0820100105041103000504066903054842c2c0b4140c0e140d5030034004210b00e04014085418107100031859002e0030308003030055916064041c21480c1c4040511051912000102c1000d44c40001141e00180700707009960400c075900d4040040541d10960107092030412002c44007041414900a9400f2150161075450410500e0010320000fa0421110700001c42d54a45074a0100d128a1280b00d024252210047d51194610700c1c12500d0081c014107084d010394003180070400113596a07464401d0b6504500005a1500602808 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 349972643 1250 349971393 349971437
    0x406050304140102070f0c08030f16051c0f1403062b0b04080406030c020706090b0a02010b0306040807020306010e0105100c060e060109020307090e011a031003060e010902040506090f07 81
    0x510b01540009249001d1140c0c5180869801d4084e200316501c41d80d0700c01102d41d985c0f080352820081c0c00d074140480212a40e114094818617405881a58111122203580f403050014074440300c4c1c0400c000c034001c0110154071800b41015a40c071011024a50300700360300000e02a403000341da0444604e241c820381404400c11200c14a00141d0711110039103260900e8030703010485421900980f80040d28091030b40001c40e2001510300304450302c94540520490505500d030a003a80009001d80c155926010201c4103906c00308000c074031507070081000c283c07540b803075104243c01c0045c10307071007400c40d0b6062a005000e0303561440c0450080c610503007081740c03c0a00b94a0064094210045030340c200740108000022840002d8004521411140c2e559018654541c1e800d0040b03000c00707024090000d00e00c44e014541d0751003000300954101c01151294120103607203584850655221008407813071a51510340207011070400e80a82a00a10308450050b01e070301d000c00c0305a8036905c0c000c2c450810030440901400140c210f40003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 349973893 1250 349972643 349972673
    0x4030c0804060c060c02010506150f040b03010b0307020c030708190611071523060d0c1206061d010612110c1219020f0d030e0c0d030806090c03010b0406050304 70
    0x1494036a42d40da038025100594400080d21042d0405c0c18044804d407061066902c140401010410348607618000030fa4560030000c10f080048034104804a000c100c2c50f405103008100780c1d00c1c419560b15141c0710003030070310408000890296010310b0052090f9500400c4e40d40c00070300c2c518900c220000090819201070003141945404011001400c2c00a01008100080800880e200c2c188103504039404a4820700c041d00f150259151181008900140340100e443e125003401000011556a1110440c2070680348815080318015501c480803c140c0340d0701c2880100e8100c00d940140c105603d0700ca80038214140c4140c0640e44141d0b20180000801e01a5040e01e1070740c5011001c84060503003c00030307540168080c5108a40c605c0d0840c8400c0a114400a902c103044807812029092503412114103802925541b0400809400384040c440d01030b03121000300054060081c0e543c19101e081c0103090007103500014240d0000b545023040117020407407881080302c1c2210034905c0c0030340d640d944d24245a401c0e95007000b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 349975143 1250 349973893 349973903
    0xe0309130507080f01080a020103020705070503010507020f1b01050403060207060f02130906090b031c091a03010608060a030203120c0a06020310050a0b0a0806041113151101090b060904030c 83
    0x4268040550380741d1000d48941881d40350312201d51100b2510030707243c6030700744a824000e51201c1010401540b09801414102c0e201d00200da20721030326100041d017543e408132411030043c0e006c101d204010301d20410403041000310702000c03201c8245c01c0390002007051103607000c050800c6400081d61402c20440d07500050311403811030720841d00c1d5400354130490040e60580c850350144904180c0045005a864813500c1d01020b0010000d140445040591141071502380c2d031108140082d80c440094503866240a00d2810516210a141d81c0c2d81071030000f50082c1c501402c400d02034030010406000503100007800700014148903555648542c44200040d2a15121000091070a030021003031040d80f400c95007041081c0d5400311150f04099480703a055889500070601000c001652200c042a101e041c140d00c03001411100e11502890000b14a00501080d09190300c25560310000d5a01c040e02990b10005404142907020b0080c080003066444030140080080c001070311680703044c40030808150040d00383c0c0300316644c40b0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 349976393 1250 349975143 349975159
    0x5090103291f0806060306010311121b0901080607230c0708010c03061d0406090609062903121e190302090102070609030b0712150807031a040c06030e0309 68
    0x312014000d1003045000d51166960b00300007184a60010074120f03c20314026004182503880d644804011440400b1420380100c54051289030140f018001740c0e617101c06074140348000400d4a024000b500700141d100b060036400c2102800109640281103c0c20303507075442d020180796410b10b100c1c1101c6104071007c1035241c2c4288403001480b1034040d0810140103010352420403646540b10514041080a0003240c0c0441c0342d802c0010300007458541c4503100150240400103103110740c59a81c00b04544802010494070120a0303443e00ba004807840f00004820001d5029001021190f11010000d0089a1410980c044013402001600481d030081ea80c00700246030000006440081019000b503000602c05401030250000128403e03024000c05d100702d070f5100001c15280d50314800104d41c140c1400050003642900d86070301d800c200200c110040081c104d44030260010b107186213000230700401c800030342c04860f03e1400304200c042010010100f04942081c1004a00000d0110343c0e10300710320a44088523480044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 349977643 1250 349976393 349976401
    0x90903020708060f0f180111030a02090f01030e10180b010b1905040522060b1902010e0d020303070f020c030111030a151802070303020d180b0a060509010329 69
    0x300003101c000710b404a0003500d4642d1a80307094080035a004031910740c402040103000c0f41c01d05c4982540256569190000006e181050803040f40550344107a50000342c1c141c000c01d403465181341444850081c14405d00b810000180b41c6100d0546905407011407000e050f44d54102205200308841203001c2113584000c4001d8190b031a6404034103160020015500c0d02e0319194180d00c2464010021102902e000401041c1c00301d945013960711030245510200b081c282e8480d00001400d00e00e000c0500803164071103c0184620108a200900311501c0352003e82460740013090304c06000b80c0110403250442030601d01444030207460041a45880c1402151a030550b283c4000d04a04008080c040e6000d4290f0100a2000018be441003008003425401401c2c003402c4240c9004090022503030040c000707984242009402e002184030800c1c112010a003100070480700080100d810082402140d991001d003800007005400c1c10301c030109103800414040201700d4107403030781c50044130511551707403520030840c1072040059850 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 349978893 1250 349977643 349977647
    0x901020a08130305030402040f0e100204050414150613122118060509210c0f011b170c0a1109010603090b0606090a050a030f0c0902030103030f0f020304090903 70
    0x44001030000025001c040407964451544070241111605540e503d42151655001c100007810500c6580c80859620000c0d00c42101003408918010740c0700d42401a101c610b0303c01800141e030260001c0681001c8000208128078001800140b1440c60584242d45c4500d0380d103800001114481d00198400b070701d482544800c0080d0306400c9222180886400104484042c1065800b008507803409284010310003014003545214801404c55800f00400a08140400090f02603600038110340151241d04521003182ca2414851826440c1560078070301032100d101084400400c0c4010504020490f07010854001c180c1640c02080e0b64031011941e040d20b1201c80350380350088240300c0c0c40340351a020f00400c4000040c080d019200d400c0b005030700402139034600c1d6504402c000d030507070140c05140d42c401144800469a600c1c2c1229000280d4401c1884188208040c2031545210001c0c1c2e108140c0e0900400040c80020b42c400103001d1510b06a0920700282400e4150130b9085010f103800c0411a80d241540d030340b080c1740d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 349980143 1250 349978893 349978897
    0x1c0902033403120c030905100203040e070504030804030308150402030a0f050f070203160c030b16030b0625020d0206030c0d0b10140307140406080a1a10050903010b09090102 76
    0x95400d00a1603a004000030140c1d000d1010310003d8007000a0101900d400b0780a9902c24100070300c80c0c40c1405650392a0400201d440c0390105840005030b001150502c440040c210900d078200c8540c1c1401420710385541e82e680280d1113240402402c000c0321b03070049060a4018401d071866224000c100795201d1a0a181d4680140030255441d10540d0602c1d01046120420100450141035213030b010f140b81018a103008111840c20300340803256424211000004680aa00501d00401c40e07861074680d51454140c008055035007a10801e485107030208040500c1004002d45040d0400c0c0200d26007107525268000210340c5044014069044400001080407000030707440200340c08a605001000f107403070044180102d600c0e1940c4900089609850f4114804102c40091a4000154074102140d170341d05409045c070580241d800b07000444c4049090200107000360080202030000102c803d4600314103440003903c050080304440e414884001901100d945080d0070540204201500e500d010b030400c80250341c001c2d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 349981393 1250 349980143 349980193
    0x9060301090906051e01090b0109030b09010b10020328110f060a11120c090d061b0e01052a0a0c03051b0d0503070602130503062502121c090203 63
    0x20f900e00000989a10034140c90001503500742c000e003207039903820a8401001080720104003030500a03240310000014404d43c6d5168070603c050000401c803500300030103208401c4e0f83d00d6850415034205000d015001c074035a0340151140d542c0340002540c4104015000e6803200364600000645000d44c01d07042c005240300060240c0603040000c0c5c04c005424a4100f02c200c140544c0030904c82715213802c0e0124001d030941402400c4200b10040c010700b0041001c0c0d60304004c4a82c0140010141030803408000849500420902800c1c8400e0030b1091400e8100c0342801005003820307c910a00c16034100100c2001c0d1000c1007101982d51340b000c00710185945038281569102c00c800345403c100601540c85500600700012440003481d07200e80154202580d641d07803070001e90800c3e465150003080360900050030b40e0302005203034041c0e100c22018614000040c007a600207e0f500d1b141c42002e550020555030502e209800c11600f41141900c40c0c52060008142e800d800342c4400c0c01c004c1e42c540b050f01c0010402201c80d00181c282e03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 349982643 1250 349981393 349981403
    0x815010f0501051602060a0e0603130201090b07020105070f0804090e07080d050403050318130f02180102010605030a02090910050c0d06050a0605030a23090d09050a0e130305090603010909 82
    0x29140d41c410046441c1d105a8036802c500d000e00c152900d0040c10103401603da4980079003854116503039898046281d03504121012170301090240300080640d60018218409009284840c51500d0665000600680300701200201000350110b0000280041e102c1654050825001d050000340f02e03002000e9074038509401804d20341d0181c2003010000600600854007140c3e03100e800b03141070450400c2500000c2e05080c0149800082800b01c480d490035161240503400f100c0054010780b070b40c1c3e28502c8040da010000d09140d0541e032405800f40b03d95a80010b000201039412140e1800b107580b207600c1340e07051082c3d5440303c0039102e05020510801081c041d02400044030b005074100402d0340e89801f08468001d4070700c904008960104081603495095030880301c08549880e210080c40f5407081c0040f003005c2002c6a8202c4950410090000e10b194407260300d01c010141111078640541c03c098850440700400b4002e040c01c4d00b50001c4900c201030064041c5d41204d6801003180d0345a60b51040f4039809080d4038081261 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 349983893 1250 349982643 349982669
    0x6030910180b0c0a020a080d0204091503020f0d0303090803091c080103081e19091703030c043f06051602070515220f060507030c06020a09081501 64
    0x820311200141c0120a0b400c081030401d1601e8220800b00385074042e00b8100214083d0582d44804180104010007440c00e9914005998a14142024048034140488a11055501e480800240e55041c071942144c503001c035a01c0085aa00d8030b0240c000705880a801006d000c008010441d0445d00801c820410303820f00304a0242d001c114400407130354100c0c2400020409541403250030321984407150380805a00c10106000d28100c00c208500c2c081000c030303500110005000d240d050210608501c0f843c52200d041d80015070239402c10086005560046000304c141041403010311002c14031100e059100b43e0301c1e58241581011112510116a2611500b020341d0a0350902011400c0e07528402582050145190301030a1154140410400480f41c2209910782541342480b00d00040807011907141c1070100301a254540041c07900360b2007600c10740d4551020041c08400e000120100b904500c0703c03d806d1394414001651411840d00581d09241c040d00010002e2084080300945442082101070503a000a04560 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 349985143 1250 349983893 349983911
    0x3f020307170705070f02180405210406080606030a0b0a061e051215120f06041a0f011a190f030e0106050a050112020c030a020a03030506010311090603040c0506030910 73
    0x1001149080c2c0b0418002071007000781e0000708101441c44060184010030307540030110444900440c0c110301b5241a60302e0341051200c89000300c500038132000e51200c00b800c0c45003010b01d85940900a0880100703070a0040c507001002814000e2150300c8108a402c2c000c003541229a1101d100400f080c92070a103001c90452405032101440f4020300a542130b03043c03000c4421700141d690b0315100c000000c0e6064016001801c800e601150910240a03118007a480b000042c0500d15060030140c01d00d16450000f40300070382514050001d8071319034150443c1941c84005100d03240d2404060a40c44c2441802d115004401a02c4810300303c45a100c19107a840c0050f980d014000003802024032401c883d5903104035a030100070207100b0040e5500402c1c00d5a031100b1407080042c1003a070150700700c0e41968810290f1500580220200e181015014402c0f15048002841c0030003401206000307051709032142203400f81c402c0c1804000102000400c0300120050b01029240a86900300003000c0750b507035400b01040300c10403800d010400b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 349986393 1250 349985143 349985177
    0x1005100f0206010f150c140d020a0209100f0e070e06040608190515010c03020a06110309060901050112140a06060b0306040b040b1003021e0310030308163f020307 71
    0xc81c0c180c0f00852588641d400040a041d81e280d4902c9101f01c0f9444403c14090590788020700c082d2103560280e07000703003003220740034410400c0010b0014240214000314401c10b101d0307860041c2d0302e03009680794800b03018401e0311340c001c05076103242e59110710a0f48160001004202c2a6008000d40e008441c80044044018030545c400400d4840448070068441c0c410300072030605612810051100c14020700549011710126120f1806480c0b500080d440b02120010900c5402c11040008030307880040d110003000703d9414000c2d444e240f413688120250a51040703800170b9402200070311122900b1035005a04212156840421072056001146c1c160302c02c6240101c40445818903000360006480028030450607c840a0f4080d0029004452101209620003100e00140140f540056014003031a40c1132201c12071075854001e101c00d070700800c91034410010512115150750442c150191700381a14449001c044039104444001d100c1820a0007500105400300541c1030000c3c0d802140100706503030b41e0310301d445640484 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 349987643 1250 349986393 349986419
    0x70c0b071707030c020c010315030209100303110a170a03111201080706050901050418021b011e1a01030e031306031d03040b0f09040902060a030507200a06051005100f020601 76
    0x13805600002030700229584681d000c2070036028001c0c29441d995440740c0105003800c00032100080d10602d035072020300a158210b4420310402500c080241200034066889200100402860070070011010400080c118000d800c4008503120588025032545814409522413450170721404000b030040b120081116845481100c15281040e194246843d04d04060383c0c0041c0510038490a20300e5092110444007440403503841708403100b660010820f11944a40c8441c80403d4803242604145041c4018900b403442d69107505a04609080c0001d4501c08a0511130551003814000d42c65400c02c542e001c0b4070741c4e0301640034804440e548118030a910288800b41c0e43d6901c1113000d54642c800c0306005200c90b020310b010040004010182002c1f03221041a400300d40e16410619801c3e021a40b83d00c10080035a030300c0704841c0e003021000d0b0100c1d00e91189000760750340c6480d440c010103044141c94200040522600c40f401070700528004d44501c1c41a000a40020944e05400d050040140110307000004e402c178207494 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 349988893 1250 349987643 349987661
    0x50a02070519030c0303020a0b060306040b071101090203072c06030307150603060906020409050f0121170a0f1407033924140f070c0b07170703 63
    0x2803820324240710820003071540c00312a15001c6480d41c14048001049029407400840c40b98005000b2207009240c41b4a2144004010714001d90100b403c01001c9610104100c0e00322500e81407815070396070464065409083c4a81c4080d40510541d03e0024400c440e448114103880c4060405401241d51640810351101003941c0080c0e0560081c880140030501e80b240c109040200002c000500c20303920360303580e0f007a691b18050607511154041010403280320b43e401120703030100031601251001d60620755212549440c2801030300401c140405500d08002c0300c6c050b07010610702480c00560321400d84500044c20b0090048405001415841c2d034800c4002d10401510491945522070409240c0d8101d00910f150810700d00411603a160180105220520041000e07860f80c01144240c084908103100421400003140410600d9850046020348015604103040e400c581050705003001512540030449110554003000341800c1d0004007803111098008001450707907455004102015a02c0c042c041d812901445 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 349990143 1250 349988893 349988897
    0x7080d030911190306060608070e061c0510050303030103060f0b3c04021b07051e120c031606080708040f170d060b0327031e090409060b0f01050a 64
    0x1403040c0003443c068034441048003c11103c0704841e0795a4980100390380150703009401040080381031000c1644e0000c008205054140c51051620000703001c0e180c0b42c03200c3e8160b00e031507407075440010403a03080e15041800010000201243d440e940c481c20306000414646204211003460808081c0d094100301001c95a001070791401c2c1131b500d440380034442084840101c41000c0c011408200609295500d20180c090301202d000700142c0c0d03c070a424482d1603c2585d407c800c0c420308696082e040d5440314001c01c1e280107481a62611030644042507841d141510754841c40d0361601581085540d014001085401241c17025920041e490310307003800568070000240c401401a07000b4004c0240800e11a43c8080a1141b403d454685003107132006d026002c0b108207400000e0305030000014071491540b045502c141009189100c041c1000a141440c0e41c1d0f4424805148500c03400c1410045440c0300326015600c14070005807050040c000c1a1520780010900790031028410307081c000364900503522880035074441440396 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 349991393 1250 349990143 349990163
    0xe01050108120c03040905010308090307090e031b0a050303131208160c14030a02030406020f07060e01110a0209040606080f0c0307050f12010c050a090b130b0307050c0f07080d0309 79
    0xb001c954031039480041078401900c000c21002444805901c60f4900950151902545943d404010141041e040b030748400002820130090213a0350002204a824513800100d005044601040005080c0b000d000303c003500e90701010040180388241071750040c0b007840c420710b26256000d03559003003540c464034159403501d45500c00e1040000003074041e07488000c0150240c08542e990315104803841d03140da40070080542c0180c0000c5800c105c0c20f9010050300500c0201301001d40300c007070b0030004010715038024a200e80303041185040401d0340f004020301c94a4001d07034000c0d008011919060030118050300080c070500c03007a4840c81510000c0c1c1400030448998a110040c09030500030f1510f4200007200d0555101130354040b00c25000004484001d00c1071611103455034035085d8850001d02c001a20a910302d0303204000000c020030140c0309100c0700b0840031b0155400b180702076403a40c4503050104d40d6400f0380c0340305803614418921a00c0050800080100403158142c040350440b902070b072001c600b42c03080080000c0883c241 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 349992643 1250 349991393 349991413
    0x100201061202090c0d05091e0a050606061b19110f1809030d05041505010b0403030507030311040506180901170604020907020f0714030606220f0204090905030d0e01050108 75
    0x1007507003560400c950360f181307038201342903c00c00c8012a581901c0301507040d07001440750020560812140e01c149600c000280081d90010788581307032101001080380d40b00d80d20005040404610304a0780d491b081079007200716080700c00356260012640c48207030020780d091800031000003114909012010410900a003048e11441000781d400d03105203901a050031000c1c0024171220b40d5680d902d219151142d4000c1001001d8012100b40e803000300c54060308404002c0030100010f10200c0c0d0440100c801740c075418a400a5404006c000c80c0156010b0780d040141c0c0054009000104807030203001a0640d034800315140811a640e0300c0d2843c50741e4039400d000b0321580d0400c0c000540549000f0000a80c040d00d1401514025004091124181603040c0c1240c143c030540c0b500da0b00e055082c100030080e8403250944509a40c00009000e14141d200030626071010300f03403154109500030643d6010707240140310208051104010740d2400e5601c81e085103800f5201646451000340b1a0441405000d04031510388003d0b2811301c070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 349993893 1250 349992643 349992649
    0x10020f07270204081e0c130f050105060f0f07020f0d08030f090f0a1104140108100b010c0309090911030f01290916091806050108060a0e060d02240702100201061202 72
    0xb80b0402d413040030700804c0001322054403500d47c40d0401900f24040054002d1350841c400c0300300c0380306802403070040c0700a0007042e65400d01102142e0701c0c00038454103191a421140300007802080041d040a4010035086008000c02c8040300c0a9070044002d800341d01c0300359880c101c00650f00c05103440c00502c150705c26500c2c1404154005101901c41e04058404a800c1c5507070720780007100d50400e07446026158856600b031148600c103441009030480003460300000c19603942c1c03002081113080c1e0090741c40b401d695034010800c00410182d41c0a0a02015082d65120120503200500910f48202c0003c00c0140700000a20aa280c1c8159914500c4c0c0c02170810780d10f600e5080c0540e001c0c0103100e051005003d40316030b0129206a20320321080000e001e190002c6403090404c000100043c001070301590081684240130300203501c030000e1503580140c007515140100d82a50002801800c441b0450005040c40f0307240c840c050480c0320006040e510b000740d6808a40342030280c8201d0032101584a920400080901000300610b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 349995143 1250 349993893 349993933
    0x507050405060a03060e04030207051c02060930060702010b01170718080a08040906061b030e15031806073f02030708070e040204080c10020f0727020408 67
    0x90211314000076010b4541040700c03101501075500b5409607000a60410180c0340940442a001180c0c4101060a01007079000c80c245002e0b07451014480c13202e00c0107100381d8400341103c1019100c2884c180b034003100c10a059054403400c007611640b00650034400c0d440040d500481da24821004075030403510095842100451b55510340c0303c502c3c18504604040065101001c01200c1300290103407414941c0e40b803a08140e1021039400f58080030130b020700c0050000c0546895108494200d805042c84800d00f980000000e01205c0011104010690088180b140c844002c90b0704400c075060020844032140c0707600c4800d440350007550b02844903a24205c80c0088000003e24144900003000e031107280030f82e5982c0c07400380c8207a0700111040c1c2c001481d41004c1044017a0301042d41c100409054808524060802c0d1040d0307190140c03074242500540700705241d07081543c400c02a051440410f4015500c440b40c03a010f40041c4c0d0010b5078880c0c4c44014045103000c003c10b04910071942156051801815000c0141e54000c1c056 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 349996393 1250 349995143 349995157
    0x302062707031a06010c0201021b030102091503010e18060414070b03040803061e1507020a082b031a090a2c0f06010b04050607050c06161203050705040506 68
    0x6200040e110122810441d44026510a01c0181e0089504400342c190891000345a40d0401c607420440c02c0160340c010401c1440c00740c64000c051821650f520101c3c0c060300c07604800c035401284005e65001c9a0003402c0103141a1020b21118450307039118074001c0ca0035408105006002500304101140c000b40702d688400c003100f940b4000340c82940385d80309012a440d401c11141545c040000008201942c0b6100a600d203803c140803000d4000640c01c1302c00703d00d104982d64182c070a40700c00003403214295601d40d800d03000184240740c11504094242100700324240c4002000390401c15005e065070103010b01034000e018030101000728048440542c54104030140c40040c0403034106a54441d02c03820341900030309041c038091348403003010210484ca10540626003034004186107200c3c0c0142c001441601c1c90340d0300701c4044610890f44181c55014a06200d8101440080501da0000380010411240c1101024100c1203601800302c00c40b218207041c0e415002c0c0d45080720310100040d8204400d10051800c0d002900074 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 349997643 1250 349996393 349996441
    0x30c040b0c070909060c031401080d12110a09030b15030d030b06130303180e1006210f090c14030c040507020a051b031c050a03020a05070f11030d050403030206 70
    0xc2c01c0e074603596441215440034042d00e0581d143c1181c1c034a03444d0036000310800d60905c8101c0e01c000d58540402c040d15021090560000c0104101261031320071200d0b02704c1c01c5203001003039484e80d80b08a05071000d080c44000384403c4407080c0004d00040c44400c0c0280404a4105001d40540f55050000c181140108102006243e108405118145101045c020a840034502c6911806511401283d0448038400309038080311841d0b101d0f1041055a403c803020910889a00d400c2505441c140071a42e22011100e800070350400c1c902d0038481c8000d07050b0301c0e00500c41c524040c0765542c5c0c4140c2c03901c150706122050000b500d60903500c400d98109140c1025403005a0100d050f02c151803003039416a03281c9090007980741050380a2076074803603500010b140502c1004500d00043c080d80507031580c03413a0060018082c0e040719005051380400d00c166842c0c0114122400301e6440582c1c500e00c03004034a0144040c1001e800b240c1d0092249040d0521000d008408980607139805030001c0510796901005c01c94240c40c50320060708 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 349998893 1250 349997643 349997653
    0x50702060a0314160815030a0609210806010905040c170a0b040c0e1c03020d0e131b2705060f0c01020f0a02010b010903030e0405090f0616021002030c040b0c 69
    0xf003090321410665019041d10b040300041030180c05001031403814042d06051200e1101000070040d40d90002d02e5007540f07540142d0100d091501c40c20183c10b005003080c0d030071a88030707401c560410300e0aa1182d4064801c1c542600e4900c501c0c0e845d013003032008075401c4468080224000c4412540d901d000e10795103903805088458080b07840c5d03454102103016120300c200891f012032485003a4100a103003400700441d0917001070302ca208084c401d0351402076490b04645c070450203104e400500038185448070550610071000041e001d01010070380c10b60140d21440401101d50004041070b80b42e00d11002043c070140004060314001c00340d024140b004211702503016600c1021303010010010103103045130a001a000c1c841341034031074a072524a5460040d094823014880e00d410011342d40d07070030b00010b5001910015414170036200014581c1d0780c0200c05150101d10841c2c00303003520880d030800c038140b0140003030b000210503543d083c1d440c000c0c14400550180c1c0810380b4480030600043c00309001c100380c1d01c405020380d4000141118 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 350000000 1107 349998893 349998911
    0x1030501050915060711180601080709080601050103022a01090309081c0e0105070b090304080f1603020d1e03081005010804020f0906030a08040e01090c020607050702060a03 76
    0x3d4451000401c07142c09005100d00000003200c00a4003085003120810041154507200702d58950000313098000241d54144240c024008480c40d00340207100c10390030310005501940100c1c100b105094440c050f0642c1e8031260b0030150b44a280400000504540c0900f4000c003070400c180c2000040d5400086603034020b5255020358841100c59181181c03d81c1c0701388004039102d109580c40981290424024402c5002020008000312640d80f4103d81202c6c0700c0600e0151034020544260191440698040000d800c28058091646105c0c40d440c021111601c82c1c407400e85030f9031200960000d081700c0c003000074810f6410307a82c201030002420810124909075000a4090401581d13140c0180e06a5000c40c0c0180c808101d00991258001850742c1c07503a0700c484c5015403003c424841c4003021418545220400d60001c03480c24001c07a03090345c800d45040b01c2a000e0060a0340069606420959111009 = true := by decide +kernel

theorem cover : BRFrame.Cov 349820143 350000000 := by
  have h0 := BRFrame.cov_init 349820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 349820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 349820143 ≤ n) (h2 : n < 350000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
