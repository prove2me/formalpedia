-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1752
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:33:04.621117+00:00
-- url     : https://prove2.me/submissions/4bb7d3d0-5d80-4f3b-bf9c-4ad6ba80d727

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 314928057 ≤ n < 315107913 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 314929307 1250 314928057 314928079
    0x60a030f0204050a12031103030606031b1e03160c05030f0318010501180b01170c0901031e0213051008010303031523010806030a031b05190309050306061e0906 70
    0x810703509003c0c2d030080c0e405c840303803991848201035006800103640304030700d4007660031810600d0201740d19010103040c000340c9a03884050301580303d200c2000c0d2405800880082420030605260801e003690050312890007240000b81020055801920003c969951007001503251820381c803101220b641000d03103000351313040c52100c514600e40001d0081034040c042003441d0141c01c01c0d048414000303d03400065a903040c08501407c80d0004285040c0f042d6010042c00303c403540d0b68002c900128000c054803041400d1640c071103a1042c15440541d0302401001061840c1464126111001c100c042e0f40704034031020024006100610000340f01c0c2d081180f2104d200102d0880301c41d110700445141e00ca03000c001c0450420052401409503900030582d94100001740c01034520f1000301d4034000c20b110400c100d42c081c034901e49044d203020084100324030030000c0c0748841d0100c44494a03140081820006100d018800d204003404240c403031806200800c3c1020110801c071016840311800c0c00409100200304661001c14404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 314930557 1250 314929307 314929309
    0xb06070c03030203180f031e010b0316050a0621020702010224070905100e04021c060e0703050108010515120705030303070306180203160804051f020a0305090c060a030f020405 77
    0x803841000e544070790051600c0d000e481410505520b91103d109110f502c6d0059240b9258901003050925194000204141c0c050810000343c05442c2c0c682003541c051044a0703003c00c9000e141c881c90000d0790310840700c4041c00c0c0d0342c0b807a048a220107078180d0400207840769400216000100d6008040040c4180181c0e40c00c5071001090a60610380c2402e04030180700d0b050208009030b68054041030203420700f122b4403030606941c103600500e018001210680115400510115940d8510f680c400308440d048074148102601c40c40104499072080d40c0340c5011a00302000450a40c006020f03481c407030340301e50074854059400941000030100c8803006842c603a0284c42c001051584060000f907109002e2900c02040052401026030070300220010b4110b9900d1041c81800141d164045002d1409201803034060310544850804900700003122b04229482d04404111502a08458011380b0303c00000d51401c00044d030700c003c1603644032a90181d00c0345d40a0001c0244c1003e640c007139400720000c070840b00801814a82c030b0348 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 314931807 1250 314930557 314930573
    0x5090d050f070b0a030f0e1906090602030702011e181e15050114030f03090906180f0415150603020f040b0d14131a040218130c0b0405130b0607 63
    0x3030003c1c0003009000807240043c40d050b000320542c0940d422400c000d0000320002a6440b41d4500f020104100d60101c1c228042c40150f030070514140d84c009208666074106140040e00a082e0280b0921500003410444604070426128008941802d016078042002e11a038a2a0f800f45065100c22184140d0280341d402161040e8800c400007080c0f4a030000700ca504080101544801050780113120350700100b540355003a1030200944d40c15000c192282d84490b16070400041d250480200103405200c0300008001ea0810f0010020340514046e0030152001c0c400403c440c2c0540c3c51001c1ca4440701110000c0c10800c5910990003810900300002070f00c2e040c5916034a0b030880b40d0744000d0748668501d8460301c3c2c0b095490391891142e070b0084a200b186504841c034642d00c4a40d2120690b00903080444004001815500e402c54a10311440c29403407a8041d0f880c00c1203103602a88007109054680843c00d10022030540000011241a10002042540f81e150070401540c080c120803019135030070a200307100d0000018184 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 314933057 1250 314931807 314931809
    0x11070503031303091a0f0912060f010f090c05031503070f031b060e150c0c0d0305030906070905010c140c060c030d050907030809010f0329040b040c05090d050f07 71
    0x1842d007290180e81002401e095280d04035448040b00c1141c03401603004d900d411603601d01a40c883c0503440b004446c00140121802040c03c3c1030314051341c801c002c444c804150b44503068420820780c40716465110b015203400c44040d1020b010103d41d00304007107042c4900304803100181e500002c084462940d00c0b22420340d9240440d0344110785a0f14983d45070105941030807087c1000e000c04d0b25102d481aa003400004a05003907014160310b211000240003003140400340254540c2c08009400c80120909034a00145280d000300d480000501405011070107040c4308220410442c0c00595581d50b402143e0385450784850402040100300f0302c550404801e04e91503142c0903006a0f104a000b8640724a41e08010038107403400208000307207940042c0014400513003e4401c1c0d40c00b60000b07280440c1030b00d0070400168000c0041804000960702000c40601c40b0b0190031080e904a880c0c00d43c0d01b40030140f410300c2400b064410381c84500022130341c10312040145040421450000f540103108440344c0040c140d03c518200021 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 314934307 1250 314933057 314933071
    0x3060c020a020414040c050603040305040306021303150501030203121c0603050c0913052a1e0a060302250309030602030a02252004020c1f06170a02041107050303 71
    0x4038199100354030f010701c5210001007101c001d10501e441e06684010142c4620b00515115000100206080c03510810a46028540c0030004550320007191115001c0b40d02103110032148103851070401c0030f0340125401900c2c100d0740d01130010310b550794106500075080d400500800d2000142c07107400c00304064503070003940000d50080000d001d49412441c1404505c1d23a0003803451000418040c0800001000004ca1810301041082e02a203084600c1a00c01c4034004aca691042e444a1100201c041c034a0b036204c445d20b00305100b00c40280d4803a58415041e0245e000318803411a101100c40389070a03604400045c41c0344058442c0c030307140b42c040e40c8036502c070002c9130410f90701d1806207980801c3c0d20002045448018020181c85c200f01103124119540d4065681c48a4042e068140d0001290500319106d640541e20083c451105a03894852000c040f4500007810030f03404082e01e42414070004841d21009001c00c03042d5921707806400c0c004559006c8c840034101020444a004408024440202d14184055405020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 314935557 1250 314934307 314934313
    0x5042f0f04090b010908070b0306011812120f03060e010b0f0708030408030613060b0703030c091203020a1b12141006090f060e07050a0c020f030312161b020f0a03060c02 74
    0x15050f40011700c650101d801c03405856109145c00d10103c1500005d4903408542460840c2000a03810040207240016a002050b100030300c2c0301010403ca80e4000e0243c55075415940c6603103013500e076001101a18401c5c1b0900c1d030405990b100500014120000800d10038002159162420300190750300302c215807041394152002c62000c000d01400e482e2901c8400506481c040090282e1810961800c146214407040101031580d900d020701003c9000c0e010280042080d05550710112115040c0691540b00c0100c086800b42c1300740168000c1050a154081e0907034000c2e14a0a40300c800543d1022110000c41d400b022061140c3c0e2194440e00d440380c001c030409800e04c0398001c546c1045c10b40c20070041d112a41c01880c400c002000401003415801001d5590f80f800a20384003030808030b1400860071300004600040d070140030028071240c860440780c110a00034507405804803903403983e840f4110b400e5407140b20704401c0140d18102c201c000d842e040c04444e1340f00c0401012603612543d070390740303c1b03080b40c040242000141e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 314936807 1250 314935557 314935571
    0xc2a1419030905042c0a0209070c30050f0f03130209091f0f060e04080c121603120f0603060c030b010914040c1107030c0f05042f0f0409 60
    0x140e20600090040100703076802e01a82200740c1c02911701d207140443c25808070003d030003a8808501d0401502d031039203401415500480c1490740004007404008e500c1a1100c5c078466010b041610444031030003c0d0491610050709000d034540760101c4280d4040c02ca20400c0c1d101c00d1003038600c4034410b540194090780c00c0300760714224405280f0501c1113410b0028069a180d030030a0560f81c2800101140a0b000800c55100000b0750359003800c4041c0051445810560b034107000c43d41084100300031400149004000c180849030300c60041e0fa481000d40c440d047c0c29000459100c200c0800003070084140fa41c0a003120316020514140c81e48a80d0210707909584140c4600d41c03a07998174900c840e01889116a0743c0401e03e03203400058180722024035080c4540da5603a0240d541c500c984080c441c4a0403421000c29441130070360f03100c203a0340e00f40011008a80e000d0300c02c14895a03000003d80f0b1405100e80c6468a101c2d41038510300000710000c40d0b41640758103072011000a001c100007650604510028070141480680015140c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 314938057 1250 314936807 314936813
    0x4090608030405090115200a0501110309120a1d040e03070606030c0501020c030312040309051e040506060304050d0309030504120503040e01060f0206010317120703020d0c2a1419 78
    0xf94040c0c6c0000d90f1003495111111403594441d03180c040b04840f80706151184052031000c146804241c81020b4515403800c034141451240c09001103025481d1041100c002808100058600348a103100540215848a580080c04802c0c5c0040041405004000241c0c11181d201002d081d903105000440b0100d65030401402000702c2800603e018140038401003407000a0500883d5580c861004414441e020f054001000c05116040b0180030308805000d160f960680380c0d40a06c0884a01c0000071700c03944c00c20000540ea82450010b03248034980000080039807600019083d4000c0c20401c90642c104681040701080003070340d96007002107881c815801565658908003c14050f51411b03000300b0304001c4040302e600c4c1c0b610740c000360030390550381c0050002081d80303203c400201c0e59124404600c3c1e0880c40c07100400c10b00c2c6070140c0c003603d80c002c02e4460074041c164840c1c3c1c0448040d040c0030300002d010030108844d10814003007000c0d907003101c038418094100c0b101680804a85017091504c0c40f001c0032080e00e0104020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 314939307 1250 314938057 314938069
    0x307050d141e0a06050613031a13060c020703120207091109010206010612091a0a15030503030a020c160306050105031606020d080403021c05031f030b0c0a020304090608030405 77
    0x129100d540240d0506250980c40b44900100088000c90000340d004108000301c1588040020711004185942d603840d00100d01481001501c82660500c0c05904818160b41c07541c80100d101ea4085c000c01111281255241d00050103180304100840c890f000d000310011300c0c50003581c5108a0150001e204691401350010150303801080c40b5004140c09012407190b80e600011300e58151090b07400c0400300c0208120090006204c050780180c42241102d0030010120340c08401c1e18000c00800d02c003849400c144010400d0050518403004005034020400900c884d5605c0d4041c211401010f0191000a41c14441e014214044c43c0c0080c0c0f801c582d40e100400807485c04015507241d140090201d000c0c8140780c20300182d1030740b001180f50014803121400044c1014424060805c174070150755080c3c4030060300504000c0c055081100e078400120310b0b0a80c004032f00d20a1005040441e988142900602e035140c031590000c5402c68007038039003540320074000070800480074000e07800900304010055440b9844c040030004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 314940557 1250 314939307 314939321
    0xc0c180e030403020d060e0a0503130f170a110406170f0c010f0c060b0609030a0606061218080703030212071d040b030c19090c030209031b031009060906020307050d 72
    0x300c03030703004000410058a43d407410718040c3ea0040e000180120706981c046050010740352005005010007e620b141c6000140304103400d491001c1c0c3c1030a001e5484a00c091216101c4840c044802c3d40100d03060b0001441c203c03001c50415101034030228600ba5074034102c0342011460012007200d504203a02c4000b5030b030010051400b0012092804940300461414003421500c40d1031000781c41c1507111500c1c02c0098941504896410f1406030454501050320308000c00240018022000050b9519218980d6a00e05000b4912260320711b444065400c80942c0c0c440c0d00d03e0748151011406e05409012151004d0001e84a191082c401d507103c0c404d00e041c00c107004003003030100c41c810248500d141081070303c400d481c00903804102040a1300c1284407501480f040341c00700c0c10b60360f001003943c070b0500340b0941d0072a40c95005400005019012103500e43c82104402c81d404400b01402c0390503500803030240ca90840e82e5040b11b280a40581c0b80011001c807191100010303030303000715210404030710f00145040300800c20307214443c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 314941807 1250 314940557 314940581
    0x12090f04020306090a0c050f0307030e011b0207141c0308071202041a0d0f050a06032907050706020d05070e12060103030e0f03070f0f15020c01020309040c0c0c18 71
    0x10b1461400360002012564040d201c1410140c6d03c02c0d07450400c40c002d004964600b070740301d50540c0e1a4602244000c005cbd01100741c41010650074030120f44840c00341c0c0d190212064419401401455060070b400b1442810407600760395200180303120004110340807240d0451503501035641c0018030303d0712031005070800c002d42c59043d100f1031040004020b24209800d803200c150340102c4589030f0750508240d07a00082c140b851241304c5514038000510030480c1d403e512150403070f80714043d4290b04280c0861220820702c0c100c2c038943c50002007000091303c6c0c6485800140300740740c0304070801403c05c6181d146504c1298401c50340300c40401c40541100500f032a1141e1240d00c0b810741407004241560540e80c0050000441384a00d500618006031700d94a030360b6040c4081c0c800f03032402e0307e806810503944490180b2541842d20840c4111074811500c840501d20104000c00c0070034043c1c004600e0002244244402403004000110802004410300e40005518092040040003d411a03401000040c030700b140c00c0328036082000d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 314943057 1250 314941807 314941811
    0x30a021e07020a0302150909240315070c03120204090606090b0721090812031b040e01030209060d060e0d09120c030602090409140303070206070c030203071b0812090f04 74
    0x80040c3c1d19020f0f00015258151124980c141b0401c421410764000e041001d0b5001e07030220108002c041c0a091001030f0380304036000c2c0781004c240c031200749501d079000803142012840300d0200040003103015030000b000d2503102c1d182c8181c0c00d0403943d90141c100e13002600840000303900c2d043c0800039a41c0c8100584d024000800e201440e00d5083c0d500d500c1c11403080d03c0c805140c1d81c8038501c10000c8034040c0d0b111400030054081a181000039101081c00280d01c1198400722032844101404c100c0280c1c00107071800d80715484003582c450703401d5070204454180024006680840311860010015045000c0e10101c007000c0c000602d203d401103d00948040340e250400700d8002c9131220000c1c0030900018480003201e40103180140e0355000340c8042000f0303002112028202c100858000d800390400000218440c0c1e04640c203480d0182c07150001201c007411540400707401a8004d00280307000c20740d0084000d408030724001001c0300d443d60303c0302c031036050110b43d945070100c214011511107210704015810340c112030707411181 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 314944307 1250 314943057 314943067
    0x10806060405031b060903030a0512070903080d1a0d03080612060912030c1b0a0605060a0e0c0309070509070f0809010b01050712021501090f0e070b1c060b030a021e 72
    0x40f9690700c02103400c00c840120114a0024581c0329281141c0082c440982502d903649180000070380707654450b00100f85550101c0c4002140548180140e90540b0b60010701c25252180440180001c1c0c0b100c00e444505400700049010003e503103403000180030911a40340c2c560b444ca4180d0820011151a0840b03010300e400441c1040664000400d40040310111002c0041d00d03501c07a10410400c0740695680d1180c0c035080081c50304003081d0001404101640701300e905100b59581d10050105140703243c0f0500090f0000480440e0104032200090740d030040401c02141e050550711400144281025140e08001c42c42c402c0000c00fa15501c84c15080e03110400400902154415100007003031032103100c80150150404840b00c0056030300c02e000c0c0d05a400c0e61a600d03440156141d8034042c0090603254904101c0c1d41ca80754580300d59007408a15a8100d4121412090800c00210800b8660303a080255049103e60398a00100c4c568400d8805540200c850281c0141c441c0c186c006403039915000300490f401d40d0f460500c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 314945557 1250 314944307 314944309
    0x302150f030a0b1215011a0408010906020903240103081809100602100911060715020c1e010b01020a0219180507030e0f0c040f2705070f0308030f060d051506010806060405 75
    0x560941140c41c1c2110421f103d007420b0600c242c01c0d006036081583c281d401d008004c024440e40b50041c0c914690110240c032141d41240020840303400d0614400d10746c0b200c40c00f004002040b076217006080c002040c1781c042404010120000340742604101c40039120a580c400c1c050028640c10465100720380c8417843c08000400140c0c48100c40d03800701a099610502000403060108544d400f080900140088800c0d91034023440c40b22503868101008441c3d00c09003010310605885c9405000c0d4100c24041a000f60501038416024400d14046059078201032240240d40050307108c1400b60441c2803011142c0c400100c5050143c8010b0645000680e901402d9020300401c04081e04003107400110b500b030407030380094042080c958400c045c0c205a00c0001d2078a6014901d8800c6aa525080b590b200c0e110302c0582e00d00c42d840f00c8400681031014080907250460a000083c0da444540180a4002000610060f510f115540d10f13a03141425101091340d04220080a0019030350f04003403540d40100044603d141040c0c2010 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 314946807 1250 314945557 314945593
    0xc11161e0f0e04060b0303041211010c1e02040b0a031b0509010b16050109140a0203010f0501060f031e06030311060f010608040f0c17030406090b0901090302150f030a0b12 75
    0x10240001d910702d100082010070159601c40c49404502400b984d0f00d4994a907242d000511070307100213071a10190107410030484c0d03200b4641d007005658800c01042e48402440031000308080050710881e0000e94400500c9010f55521000c4801580f0500210f14175098006c600856424188c1c8510b014040000052242d8803d00050340e04409102c95016000300c0700381419405044480c1000d811502020441041ca40340400c01c032a41d18020390091061306003045040040700d00912500c0009070011900d841103a10079041112600d4010304030405007203060051b0030451305564412008103410380513443c00482c1c02e02090340d01c607624040322025989864400781c401080104014540c030307003d0040034100109841040c0c040e2610081180183c0380503211160b0700d90190103840d0100c0c2c0031900000e0b500320f611044402c210b60607512221820314650a0004003440480b50403050501400480d01e02000034001d0340c8540014040816800f05050034003000280b502c41045003500681c43e0741100b002e05c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 314948057 1250 314946807 314946809
    0xc010612021f030b04050a0506040e1506122506090b04140d06020c060a020c071a07080703050409020c07150201051e28090b0106020607120c11161e0f 66
    0x4010881e40d0041c0340d4000f2002450100000c662241c50402809800a025404280720f02401c0da8100300d5042100d02c0702d9501d4100c0740e0654124406400080d0a6081030810a001480020101c4001e01480004a20b00b424101030f0321143d44100c40007041003591103000c1c500208028042c8a20f0300f03041410343d00d00c0b44002d03941c00c0d0190014004440070044640d048035100b05000082d40c0c00c504200036180065402070701c0207820340c82a91008200541502500140d40444005561400910356604003613038001030815014000c05101c00100611180010007690403070350040c020380b900b420039141e8001c54a00090085a15090805c8a03608095400c020300100f0301182c210150754602d4550780120056503410140c04c070001807130290070101d8201e40747c4144221011b02030f982c0c0301e841c102d80d620390844294001847d0104400340304442984880071040041c5000c0428034203040d15103240004552f6005c9512003011800c02050b203004100c43e404440902901580c90303e070103c0a100c03a0b410f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 314949307 1250 314948057 314948089
    0x6100602030a0e0a0806040b151509090c04030c0305060405010606080609130611040b121602061501090509010b07030e030304180b0d06060b03010f0605030c160c030204050c0c01061202 81
    0x10b400180000f643c2e910000100522940040f1802d501e0140382084480348180e500b11138a50580c00713152141d00e801c90041c11940f50f5090319904210741c0c90100702c8010000380003040003100411011001c00d00c13180c0180080c43c0a003001380054102807130a94210b0700164820010000c5032010320265a590000a07504140e04034400c25400980e41014001040c0c4135041d020b601ca4005030004481400c0405403040f03141e4142010013030790325041c04d0890710f0110a0130780c0040c0c10a5001600c050361000f51502c0460041c50260b0f5103603100c50101d151642c00f82c00c2034441000c003003030324030401d980410151a0820154082e42c21703e4035203010085850030641d0192030a030388800c4407240c40e031500c3c040d0325003850700520b051140f255240507100743d80d8428021014811308481d0003054913030180040f24029070180169526040f0400c14080f5061143d05084840e00c01e000c20010141e50b032806814003800400c214956540801542d850841d03a055211909880800458501590310601104c040d106 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 314950557 1250 314949307 314949317
    0x20606091003020d03090902041203090f0b07020d05150403050d1812140c03030115020f0304140d021f0905010e1906140403061505011b0f1709090103060506010206100602030a 77
    0xe414070b006d9501c898590030080c4298804100090005000d1a82c16070181c0030b500c4560707441c3d80740c1201c10140c182c0c40c0240111072800700072441c01410402030304c09100340603170160303040d1149030041303042203c0003918154001038002c60030f050001803a00c035104840b054052a00c024035110340d40c00003e24640c05070201030255042c0070700c000400b00800c503080b114113082600d03625070b1030300001210400c982030903200612448001070b8244200104450075185908072515500c010b44d420810740c90341d050005c9030032040d031101c003110041414076004200c001c180c8a085c41c4a0401c000108684040340c1450702c511160710000c400f0724500b07451101a035440c0d00d080b0304000d01c0003001c0200c42c4115031009051919010300d0301c0005810711810801c0c0c4100b681c80c402014041c001610240200c03e0019007a00368000003680000e0a05011960703c2504240040c1017020032000a00d140701c00740e006503680ce840e042000f14541c1c3c10b11145074803615411140d00c1482c10000020341d41c0c01124070002c1403003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 314951807 1250 314950557 314950579
    0x1a09010501080a0b03150108070e0c160c05031501170c010c140705060a020304090b0405090c090709051908060705070c03030f05070602030411030607020106211e050d02060609100302 80
    0x140c3da0007001c1e24510140448085800c0b00c040e100f406030003440b610445c5d009502c4085001030351038100c0360081e00000e01c1c5500740034000c0800e02464000c01c070200e03034104801d640001c154034140306271440400189a40503442d890a14803c01030124850010305a801c40450440d9580c5c0082905201c5a000382154040010480801d4a020f06035080705510500101e5070f00c114560000050044e500081c409000080710306080c0000d980d02a124040c00781c0002620940714208001c87e294031107107a19100e411190780c1c0001c51001000541d1440603414040021300241a04200a0760045500d1914518002c0c031034031524070000c25070100604101e2001020b10b9900d20030f02c241d69400c2e800c51030466907401c01d803901550720020b480400d4080d009820000745c0c62070040c0b151a0403101c2da510041c4d0301e0300310800945420074200038100e039a050b1318540c070002c0b0450092144071107480703440104001e140864020b498184003c2a0b54880d060281c1003001e06805610844d00f2a9410703500c8070151 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 314953057 1250 314951807 314951821
    0x140c1602040209120a0c0f0506040303050c12030a0e070f05010819020c15042a0b0a020a06060602070f0f050616020d060e010c0e01030908190c1b05041a0901050108 72
    0x83c1c41207428450780402c0711601150f6842c80400c4c4044414403c82410031740650310744422038804520302c5840e034040805e0100b003011a008200500c03201b01e0000a913541c501801041c81d806810944824000f250713502c14014003c0d40070404080508004520410214a00740000708150001400d400a104420280e00030110740f54045d0b580d4804031000b916000706102440715100042114143c51440c1d449440720200c00344802d40b00605080752408a034500d0030007085e00000e5002010100c2180301d140e40c80001318070184652009402e1a5028200d190303d801ca26050388045070f0040510034001c05001c100f2943e5860403907143c0c103641c0145a2030341080e4000560b40030349410001e440780d424440c08031680541940600c0010340107480d4894042070b00c4004400700e40c1030f070b28028020302042103602e03c11444003202c1c81c0c6ca6080341c0f6243c5480004ca40c2c0b02e40d0b840c24908520070190b0b1a200041c4180d15080c000e040032541c0300b1a90380d5410b020800041c4103507006100d610705106042010800d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 314954307 1250 314953057 314953061
    0x20d03110304081b0303071d040c020c010f09030b1003140d05070f080d021305040c020a050c091f030c0602060105181314120309150403081f15050c01140c160204 71
    0x3401c4100b805694587c600420701900c072800c280300325400810308104003201da1505105d10050180c1a5009010702442100151010b4842d40c007110103005a06a002000411040026100f80341c0a922140d0191451821320000040d003034240f483c0b50070000e00d4a07852030744401a00e1605401030324201c2c081d40e4604050000e0701c01d0309010344d011400014582484015102c42000b102c1081e1000c000405602100300e0315030089003001000358000080b08000303454080701481d0011801d11255032543c8540c000c103a00510107070710407a840c0c0543c0d64200003c40c1c0610480340182400d0300e1055400800c034940c0a503040b001490200002c540280c4841400307004515928004400f40455051004101300d005242d0001c680700d1441d4840c3c0203000704400006428240156415211002c064032260b04400700f1050400c895201113a500c0780014a5003011920a44012001c1d00c03040e580d508403a2200d07003501c0700e04080428004860003840a0301002c001214022521800343c0e140701980c620000b00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 314955557 1250 314954307 314954347
    0x712090902040b090109050906060d021e0c1506030604031709010908040906030b01090e1f090218010e0a09080315040603060e0105010608010e0103020906060307120507050a020d0311030408 83
    0x81501e00c00310700070800b0110f03400100131949098a4054285a4640c1000600e06040718042d070480010702840c2c4d0512110b030050540a03004440030018545052103e04298000d03c841d107296030b01c2405e200d003002070000a05038214101350080e0213546442d1300c1c05008001038040200903800c00c5000540f0300c907000c2d407040d81c0300d6500000c0556107075034070010040942941d001c140e1f4a001c0c0c0100000d06420588035041038010950041d22000c480a104884201d03410850804407944603071000c00141d451482c19840e9040c280900c8600c3d50500440d50b9110364001c00d1111510320380f080700c501113002002075070f40c0b000c005203410400c524160b000c100a00f50980c401084107040c5070041d07084000641080303041e12404d90306c11030984c1e6640c80c0419454000c0c40060340000401d00843e00c5801d01e0703801554080c80320300b046e414086460902008454045444100003000884d2085071b4550500020803042d4042c5001e0040d2110001d00c0e12a522014000a0184000040f000071710f000c000803040c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 314956807 1250 314955557 314955569
    0x609090f060c03070f02030c07050103232818020f01020703140f0c030a0312090f051027030e0907021e0105060a09060e0621030a0c022103071209 64
    0x14549051503049502182c1040d04c002d004180c1c1912130451a500c0003056401c034038440c1000300292890100154000e1642c41c601c990780801004680c0004210110810f018509140b941c0f17021412800740ca10350942080041042c0d20305142008440341000f4010703125090b011101c0790022250140141c2c0b9008090b03000508e05600800c031013111041c00700344182da03984401e0945151320313644401c0688480200034010b0205084c0c16040c84049517030b91008d03071014030884100d5078941d803948507285446801d9813a0f00d003590b1902050510f80c0b4802006400c8108070103803001100800c0e43c0c01900c03c103d0400164060b8644d100000c055038820841002420505451440b521f0382c3c550503907029100881d0094000e0502c80c0c000030701e01449100301001c03154050303054015615560108070080c52105600c903440344801e800406100320600083c1030f250200e481d441401403951050100406c4001e0000804440c0d00e02c000400c40f0000c000c0382e4400741e110031000304000001009442c030b054290045 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 314958057 1250 314956807 314956813
    0x90112080304060e0f01150807060906020304140a0f080d120509100b03010f020a08010602161a0912101a09010e1603150e04031205060f060703050d0903080f0702060f0609090f 77
    0xc40c451f9840300c08584142c4080c40d040c0c0750503907101d090640d0316011610801005a00800003006280500011010340c3c010080481e000c01e0754410160320141d50380e07040450130350441c00034024100d420034400c94444a071000309000c0b524055220f940ca500c2251068910b05440348002c011503034080d884ce000c402c8490004545416951000400100d030074059100548180805101c1540840304810202c0b01e003100c50000d10050094415210b802c50004190090725051001001380340070b020b40d42e090f0301d01c0b40000915800007054110000c0e04c08070014000d1150390014000380800da40000d500500c10f54012020795503114040340240f05d0002100c0328822007400100c2e200e0300100341d06018038004c0e41d401d600c0d00e00e002c036954103c07075061ba5001d902c60741d501c01c00e0b03506041c010090182c01e402030506609001803240b0410a445132200c085002a4203401001900307410761400e2508942c291000b4005032808a10301c040e440c201400300752060045070001642c2010400c810024100d0150039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 314959307 1250 314958057 314958071
    0x11d0405040f0b010801020c0604170c0106080f07060c080405100c0c0806040b1e070806010314270d020a02040218062701020c010c120e0306090c090112080304060e0f01 74
    0x22000403108501c0048a2034100300f000001c140308140240ea01900c050406405151180d554901c0c1d0f5184104501d913401c24180004100f0b0f400a202e008010040d81c1c000d8003d04c0c01183c449420074085030040001d1003104c1e16010086035a59041e038084e6203080d01e0071746002c828107401f61020525070f40010000c0108000200c2c04240100c1e006001d58400d250b030300074540701c0c8949580b028111340300401c42c0000c080000380b41c1502c504800c0d90800010f050004441240ca0145108400c0480d0000c03260f2030300307000201400400440b40a0300c601214080e10004600c0070000f9190f021181e006171045030007081c1141c2001c0c02c41d004a0503040010a04e0f65200b080310070908407040c040d0540740c0400c5140e4200180c6500100e500700c00200d05a40720703601d401460791070780c58000c80c0c0740c401c0742004500149010740323071810445180100700f03480c0144000c01c1104100322a1540582120002484d140005400564860156038100354080404200000256089403418215503c10301d519030800003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 314960557 1250 314959307 314959313
    0x150321110d0c06060e0f0708060f0d1a09120f03060402131409090304050f01081e0403020a2d02040903030e030a05070b0c090d03120608120a1106010311011d040504 72
    0x850b55081d881010184803507a0784039031103224503400700c0300382820441030750014208074420788100350700110042045541c810000041004007c0d5504115020002e0903810352040c0301c05040e10394494030002c01000119203403501c2c00204e0007400c810310460400880410352940d11501920003144c1c2c0540c40300c61050b61041c24444010403501d01d5402010501d002c100fa948005c0201da00755030300079040341c01030306888004480d0b000d4010310f610340e08820300185c07072031b01012142b07941c0c0501d002c0c1d401803003c4441400c2100c2340074980b100d088121039980c92052030840a01c04400c58050b0100d030000340074400c604054021700342081c42c0062902000030003e140c81c0c2c01c0405440c0d114083c1000002c996941c40492046110b0b0050075907108500700313039450000784142094003081081107070100300c1540d5408030900e03284441e45a091040320100ba403500ca1903024545070f103220310100042030076515540701c1e65156814402154100804070100d030202d03404034030307881c282120058420085442e00b41 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 314961807 1250 314960557 314960567
    0xd0203010e090106050a050d0c03060f0902011116060804021f080a060b070b06040e1207080a030c020a02010f0f1704060c031b080604020913020c0d03150321110d 71
    0x10007801649040800403405034441445400c068440150141d1801c500308400c0180340040303103c0c121010000400040300040040c040c103071607103810310400300e07943c40c00d407001510b508134000c00c004aa601102d03400760858100e92040003110b106040c501120740312400807509004002041100c000400034554070201c1e840103559105250944c010070a003030315400319084e14803030714038050010100f4002060152030590700c0001880f46040840700c5140605003180d811f43c00030801035410380004910850019014020080c158400307202a24001d01141d0000e4008200701d0340b144100700c6080142c51030140103d18000840902c030011003928589890a5001b6100b05189500083c0c10403450102c0745e002e128411801c6a420346407217a103951090706000c029008580b0315540600d000100e40d5041d0550b2005194111012001e0600c58003080005406d40d0040c241d80c110700482a00200042442d0501480c0c0f5090480042c401c5100904d0080313515051802145255000700324142e0a299000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 314963057 1250 314961807 314961809
    0x9130b070e0306241009080d03090201031b051e1b030c01110909130507050a0b0309010c080c0d02031003020619030c0c170706090606120507080d02070323030d020301 73
    0x102d007111280d90790000c03484c2a203d00b11108142102ca4800b00d00b10a00c1c02aa0b842454142d502e000a1140c0d540c0740101e140001b101c85401c04240c0e955440e80640d6858041e0399201031500f9078224604003402001000340c40790b02c140d0300c3c9005109040307000e84c441d090100c8040114000c01d8002420148003a240c80f9480003c0c0607602d0340c0b0305401400382c2c0342c030710741a110000c07001000c0119a17078411110003402d480f6031f28129042d0050a9006c942070b59140803050140643c3d40540c0d03141c2c5421004903084030008003005051007244000c111680c4500c0c802c441c01020340000c05a144d84a140141d040068180c2009502190100d204620083d2039180001d410f0030700c1d5011b001c010000360341036491030800c5d48040d00000107601d119150406ca0001440e0040c40348a000034409059141d29040b2070a0b40c10485102010301c81c11800d01000700182c030082d05070f0308c0280030640092007019640341c03824440240340c00c800740913041e0301150001303c50030301c1c00d0342e041543d66600c02c12440030b000b5842 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 314964307 1250 314963057 314963059
    0x70807020309010c080d3210140d0c08011107060b18012d0b030415060506030106110c0d240b090f06030f030a09030309080f0d0516020409050106050a0608130209130b070e 75
    0x1110000400c5030003024981e03002c542c510880640001d275980140013019403c081e0641d00000c41800000e60041c00b4815140114170107031206845110510b051804d0b141c20011961088000f0760100130f201c0950000141111107130718064222038102c1032000841c001014805445040d10340c5e002401a04000c0290320851003200030382840f00c0c11020480c11240c49024141c4c00610610050100d45c1c041c55a1902c0c580c0c1002c110382d41c43c101c1100040001e43c800d8070841d01c20034213003507002c41960603c2c41d8810074405004280031980c9030401107404600018118903800d8105004191552400c0c03282c0d9400d100d0703010581e6074482d41d0034000340014909102c1180044c0e6025800a00200081034030402081440c000e0301003041c1c840c100301c03455044034514a04401c25040d059005a441d071240200303240c842c03000483c8039071408080248180d1954002c006201030b090070000c400c08003002c0003805070360444501100d51108549414070b401c00c0507005200031181414130110681100e0710f24a4a04c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 314965557 1250 314964307 314964401
    0x2040f0b030702100903050d1e05100e060607020103020c07030c0e01090b0105030f1f09050a050f040206040b030a0207061a12031305092d070807020309010c080d 71
    0x903548414144620048420100503002038054000324881a00143c0e10f46029281080c20000c1a2000004a80580805070f6074a101040d03242d04423900c80c006e03103502803c204d42640c0c1203071070b019140c48a00d01c000c000b94840c4c0000200c0c1c1003160b010307906170780600000d0b07421540e00c0ea80700d01d0300540a0099020382c3c20350304c0e1004000a0032462901508000d4076041c0d489505540300c10750000102c0d00060500c61208551011150000d2340320603415008000da8a0045010b090485640c821550003a0240703640e54000c40403c0b002d41c940d00c007254100e501e4101015500d503605c9403500001e014940b030051200341040c61701014210050611002840c0c101e610000d5030340c08002c03095072072160b0500d500c5031000c814010415031402c0c0c3c506030341c0030b207980003014400035019004610000e280040b002c4e4001e034032814800210303400707803595900040d030380011481c00c104c000000e009411100d100810300000046c11103400810f540180700303042c111104130040c0014000e0382000607444481c40c250380107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 314966807 1250 314965557 314965559
    0x7140c0124140418030c020f03121312020f010c03030609020703031d011401090b010c06090f17090117070c050d050913230627070e0117010b0a020a08030a02040f 71
    0x12400c1e00c1144030f10580791a00c03158000c4c00365003e83d414841036134184e91101c0100c660440ca0f46061002e6a25541d802201c03030303074803481000c1c1142c0081c19500f01c1080c0340c0c0b03840700b004010703100c20004000ca00301c242005a00c0301c0003171034114040d002e00d401c0900c0745030000c2456420076030980c000855030120b5800503011004880c80039400c980b000c1e00e911803401e010750010048032426900036100d000c010325044004d0113a545800c0203498100004a5a600681424806009001c404404040c0c000c444541c50030344d00074002400030703090b0001001c0044030203011800e0540249050240198090300780c0e61a1001004d010384190880140e05d4001c1d856040d0f094680d03999031041300d099515203a000100c98184058102600100802468005440c1c0100109842a6080d6013903520001440b0220b14600140300402c040382007100c6606005007098210010042a4001410345811414440e2640d0800078100d18260312424060000c2c0c0000040c48000c3c01d081d0010015200300095035000c0c1d03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 314968057 1250 314966807 314966809
    0x3071a12010b091e1203030c070615030f03051305120d09090e030706020703022416110d180b0705010e010b0a0614030601050706020d0902100807140c012414 69
    0x30312503842e445a00c42c0501c0b040e035a4039100c52804c0c000ca0f0a0203420310032500d000303803002840d65000b03440c800000e800226640007008212700410809010385000d807071149142d9580e1402d90081f07490014107011001c44e88080d4400b9203400000140f40042c040e00310309041c401c3d100d407507940c4c040e920300018090050200b680d0525005a072600340311640158582001501c602000350050071044045008182c1d032050fa002c00700711185810780c6203025948042c102500c64901e004030081100003401800f04503080740c600003007040b8520003880d040401005581404c05000c1a00c10b41090303000100100d550310600c20154051615484640001c00050419104200d0400b450340b1980002500309083ca00d9201560000f82d80c0052040c18480d0500381a0740d1444c00b82d030480c040a0168a075034030b82c03080540c80c00750030704e1041b401d0505200f46181088072008140301190384540b8103408000840c0951106c095200c1c9039a20085000c0080800916a5094a41c00d00b0b00c140740ba1194085140412 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 314969307 1250 314968057 314968079
    0x30509011503030c05030405040501081f1401150c1205120907030203061b0d061403210a030207030c0f241103061005090301060605030106121107080903071a1201 71
    0x801d0301c031140c0d003554203155640c111601c1500c4035048503140001c2c0000103c60301c990050380d020741a03401c0540400c041d200048240c1903040c44003032503400d0a010b0013100284880035002d055502c0d4820f400b0360038a40280c1510401d0f08644000c105040c1d181851495070761040103085140d0075507104074655265070307002c541da41c951800069416040800072400c01440320307140149c0c04103000c0c8100d05144c0f40b00400b5044a030554020b03080d0030001e12140200e8a002d0020f44000740e40412080c103542c0c81601c0c0c0d02282c1c00351445001c103242c7e0009400c4140741c028192861401e5100400d404c50071405c1c5400c454501f0046c1ea2404500340c0280f031002a400c5038090342001e0586003000030b00316503d180030402d0301031088071030005202080203005031a84081c01814058800d6446182d903952500c5401044858285000c1c0b03002c51034070700c004210701008801c69030741030340204115880e0318249000a040c07000d03541c00150412040002d02e501c601c1c1c07a4006d844400c0380d01403440f249a83e280c0003109 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 314970557 1250 314969307 314969321
    0x5060f24101b080d020d110a02101815060801110c03070209190203150f06040807030f0201050c07060809100207030f0c08041d0910020f0a050c1006120303050901 71
    0x76101c1280004004500d12800c18a468162800303401c2c4601035842c0c4a40724141e01c0030b404042d20f9500001d0400f050701c0d05008010381d00303c0003d141351030103c504000a4865074501016942d03140c503125890402c108081c0e100303041da07800c4640d107032000005208600003404a0700c500d034065403c00400008010080007551a004040c10240d40303800c0c026420041200801044049140e0a8031403100c3c5589103440a18421503015046414542c01c400800c00c2100041241501ca6401000144440c00c2c010492000720703076000c000390625070304920040e0f03814010a98140558400c5020000e2056808001d0318054540300d4107941000c1c0c1e028107008280d20400c5805008140031104011038a0f00c10304003000c440c2d001d2890641065110814200061000b40802421640b54070a0124010040c01a0170300d0400a00c000c61802d20104500c903c14003680c100700061040c04501000d4410b01031013040c40c8104107400802600c4e484801207042054048000e0700028607242c00202414414031440c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 314971807 1250 314970557 314970559
    0xe130b0312180301061d040501330f0f181d030406031406090601080601021204060f080901020a080c0310090908070b060306010609050609061603080f0705181002010905060f24 77
    0xc0a40400740341000c0d2281c0007d0800c85640d9a241c1038403810350103884006c45950b15802c50407011031840981504602c42d00e80102e04071040c9101c0400501c0b03000350801080360f0380905a52801d118103000d8400406008140c04c20b080c1d510400228190710200041003650156101084402000b0702d00d080c020f4001ca46e91900400301d134021074030943c01287c043d58400d0051040b200301343c001007804800e50300250301c42030216450090421129030088035462b40860804001c40c180f80007070b0300092040e940500400004040000440c00b0058141140809400e1801d01840510a41e01d025002544900d00c103581c01a400408107003a0f02c1d01188680c12101c03580c1d40d080300182032108009082d4041c0c03e413268007503010403480d1103418456a03d144000d0003525120703282c3c50b1103062414030f4400188010200001000130341d21111071215000d909600c140c80b4a9449120904180d0040410501c041c01070b02c150020445e18290b4204074034071945000e81d000d403000d110110070078481d154014001d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 314973057 1250 314971807 314971829
    0x917030c060a180609081b0718090b1f0f08070f060c0203070501081503060a1a03071203050a140c071712030a02030a110412020a0e070e130b031218030106 68
    0x10300c0400c03020b80049040381c0c0264951840c050118207e00c1d01e403103110f2502e403295040000700300000b002090800304580c0e4080000c0c016440c09646445038074038010140480710418554401d0021040e03e501c001802003210320058103501d074407000c0e558041d035105401d03c01c0710360b060103d59148110074041499a01500429140b030400005441c01341c0010201d480c00f00844003441d0165404001c6503000d000c0c110000510580314100b1510080c9038242501e0083e4410320f0101300c40101d0440144d031440d050301d0001d4072000340c07040880720380394190424001e111010032660380846010416504403014003e0801403c40041c5400e51628080c2e040254040c605000240310740c00c0302c4d0011a4008802c0c48002405075041e400d40040d900036400c1442e00400d01a0420114200b1000c070384080c01d26080c40c180c1c7c80c43c104000900d900e040e6034006019803040b0603030901c21951b9801c8528645130090a50b010b555145800e02120f82015584201d141c413283c8005510b810103204200c1500c03008600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 314974307 1250 314973057 314973101
    0x1006110604060f0e01020703030501180b03060117031b0606100908071809020a0b041d0126010b10052808010b0f0708030103030c0221030a0f0917030c060a 68
    0x924001000707481c101e03145407520340c013041e00850300a10007481154440d440c00212541031051614900d00303056460139401d8a40000c1031015035000904904440d80c03c21001c0010458500141c154002d2010382480002c2101c0d15000246010a8851284400391000c0c9071004c99104111008003040c0705603610b90700614030900c80d0072a4900c0d00815900060070105140d1829400b00d50002c45540c00011100c80104007031040c2000c0888a100749141c03000d1302c280650500702ca11540503201141c24502c240004004c1d00420800c0d041822580801030034180d405405000181890348040600741000101101e90f007000032075039100c00041c2c4029620480207030b083c000c00010a620100310172200280a104030400100c090000718007862180d80d405d401c0f03861910610000e14481e2003102c1c07100908403070300307a05c40100101b035490461403442c01000c042890003094034814001e4114109411440340c0e1030114120000080401c0c2c40d5003000c44505994140c4440c0464581d00000002071900c02c42d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 314975557 1250 314974307 314974313
    0x7150c0804120f0207080d0908100b1c020f090405010204080d09080c062a010207020a05040c17060d0203190212070303080609100e10060f02070f0504090c1503051006110604 76
    0x20f0034609280a0340100d0b154941c0364209203240403029088040051701609003400405011f01400c64005c0a2000520030041050000303840b00c0e88060b0b8080004444004031002e650310240c0c84012034001800000c02418141030940c040d62040c010400184142c0c12200301840c0710340c1c0c0c0d0401300c1d8459006018400402c0e41085150f50240d144403a114a4400034008104101c1f8961224156140300040c4d64020074414045404016440188154a007480c02c880c4030342c20001d240d8010074600d202c0c20495a45200141890034a001c01940504c50300601b4100d15141500240b486402100e4000e000e00d50045403d6961001d400001c00040d4950003040050070f0039444140c00080e20b02d0018045511039007400800c0c48115200c080051201e0340030802140c101e0700150410304544080d04200d1b0070200442d00403507440c0324103401030381c0d00c424401c180180400380030040c00000b40d48018212811070300401a01094402006003220f05000281b0640142c0240510310700d408050655591151 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 314976807 1250 314975557 314975567
    0x303010b03070c020a170610030b060904050327040e0a0f060b0a0509250206060d031808010504031706040216030c0f02100f080a02041d090a0807150c080412 69
    0x41c0990b000e2010b820348580042c0c0e40c0c1080300015002440300044000700c2041e0092074a00c01901c0603d0016241d44240041104507205030391243c400c3e070b910f01c010f49586c50254510f1040b032041603004444120800003411841c41c0100103100b04607002d0003005407001e20fa50b102c0c80c809030005c0c40104000110000216141c00078460040700030881e0091030354650100f03000034422190707000c003141015080000644400c00e0850100000d10080c030081c5084e401090800f8a4840007070288001d04001c071140c2520200104040d001501c0240082c0c10300c1cac5800f45c1240720060f9800c8004054a0000b83c1d5070070305200351403441c4008500c18044e072441d40ca0690f200b41200380c040d10004401c45091015840c0c10107642c0d075180385a5504498145920801000d00c42c01614200d9140d004000c20000b4244911442d942840440c01a03101d641f03035030941a01d0450a00c000500300301b00840c02c078007440700711505049410004041440314030030170f90084903940c000300c40050080b41c48020101c0514455 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 314978057 1250 314976807 314976811
    0x30c0406140108131704080d0c20030307081201062601030b0a0e070b1908103303060e0a33080f01090507060c050a06020a0509040c020105040507170303010b03 70
    0x1250860880000980755049407480b00c49900480c400c0024081105000410012381d200402c2e01e030003510b80c0c0700f83d40e0b0b03007001069040c1c1203801c1c030f44505101c1d81c550b0303400c1c030850310b950354081c00d0299030701d00344a130740c01500340d0904c90b940101d40c6912480301c42ca1410010415841604c401c0519161f0942d920014540700182003001e010b40d64040c01c3c400e1030403c00c8030001038000011690b4403401840104103003004111140000c20800f030007800003d0000a880100f0303111034824000b0000455444880700951901c080b4584403001c07080000c034180c03d40e004805071030000600f000d10b5030f14040080700b500e01d02c42241c0400d245084030a03608800300c0500c0109000d028501825695841d0102890103e000001d1038141c1d64035104001004030800210340140b0321804c120b41c03000e0303054540c15200c0301409409010a42c00007400e03401d142c483e00445d401203c001380b081082c955002ea009008042c04c580403078151207568000328400b4200c0362558002409480111300d541e08000061119402c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 314979307 1250 314978057 314978071
    0x1507080f0a060e100311040c052a15040b0703050105012c030102040303081608071d040b0d12090e06130f02041205100f050c1602030a050615030c0406140108 69
    0x2c2e808000c150010040c1c03505000d140d504911044240c250708045862a244840c9288614070f068100300b44d03550403c05980102c002c40d01010341c60b04004040c001002d01c0c2d601120440c3c052a4003e2035504420a400d5015078041c0089010300e40c0d07180000d604039002800f070755020840d01500c1c0050309248102c08130110440d00c101040055180010030700703a8016810860105940c07a00704407034140e010051280d6200c00d07190a0501e0300300014003800c000300d4543c00071f11420f00000c07011940c2d00c543d0000800441d01400040818849043c6004480d6040c00b040c00014003000380051075105000d061400f81900420004900e0a240a20402000f0130030041009a400380400113000b0944e01c81000f500e401007010b004d07103002e900c0b260011100061041e8103035078a4981803142e00084c5e48140c0d01581d45e8278100a2461a242c00040d2078888000001003991040104010301c0803a180d02550b0800350681c212009c0104060401055603240e004000401d0603855145426600c5400d4483d00160 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 314980557 1250 314979307 314979311
    0x20405090c09120706050c0c042f1215100809120c0c04110a08070801030f0f020d02040e030a0f020a021008070903080721030213030204020f0c010216051507080f0a 72
    0x10f0140d071050410301150311020200e1b0000c244420a02402e215440c00030700101d80411080d804007000f1400780200e440300800f140031013410070048039540c502b100c01d02c100903858051280b4104d840007060000c0343e07409038002e0210005268040e07010308c4d102409140d881c00a07101c841c0403540f40c6d0303080390400c1c024135400d80f04119000e0016161441926891b1035980c0c1442d81da8000344001074050071010301004200a2450010004a04030700700e2115a16404107125441507102e000080030032240010180d0b105103008541080c2020001c0280141d40c01074a0710484d41400704010398803070078910300184d006114541c003500141c0c03051303420a034400d4141c201000e51607283d45490050340c010f00401c58200d00032404d000c98a211043c0000854001403609500d802c1c600a881c004124141c480240159000314006400e005800d0607541000003d40c001c41d156034401c440d1030081d0444e80b02c02c0e54640541e00c240d0084d4180486002d01c203440648809180e80c075201203016080384001d140a0800b5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 314981807 1250 314980557 314980579
    0x314040507092f030915010e040204020711060a0c0501050a02121f0b0318150c07020112020d150513050f01150c0c06030b120c01090308090a08120c10020405090c09 72
    0x160002080030114100d018074180c582c50700941c02407400d4000149501b90140c0d850041011400d590b00269115506650268840318145007564901c856000425449100401d400d4000d984c032842c006007143c041c1d80280000e072200003220080303101e07401218003a40c1100000942c0c4070700041d48005449a04c55500020a070f0300c0c0c081042c10341040e1000c544450914004207040702080240c000381e00d82c5c2c15281800360601c114601102d100e4958001d050096500140080c21165810f582c64030980810900c400307107035001400c0c1845103500446210741c2c10144030007003c00c0144100e920507001c010003550143d003046030302e00c19450452130410400541208560008143c9000e0100030401070b14040703020b08481e01000754400600301005059400b4940d07900c0b45a0f030015080c4120ba40085c540c59441c0418008103000c3c40c02600180a94404c4140d401045440c0500600d030a049610603103168104018000d0141c1c4180e03c100703035000b51301d000403804618a0388014070a4040c01400c1519030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 314983057 1250 314981807 314981861
    0x32a031b090d0501111b0d050703200607030b0913080301030f060b1f110c0307060e031608070503070e01080607030b04140702010b0f1504150909021306031404050709 73
    0x52902d0181c0042c02440100e007155a01b109415541c00886030f0030060480042c4202c0700030901d00550001808016102c18410724001d4101c502d00100d1440509446040c501404081c01820103204010700450524000500717240700c6107520448aa070100039945540d2854407042e10040c0c040e40309440c0c05554041003001e560b542503020b40d440450589800c2404010b81015001e1010310b560a0f156810140b02e0b68884d5402091003002e03581d5600f400d03880c0c1018200400d01e007002c2405e00c1005014a02c1d0b0102c0c405000207110000c8401c100c0840700c8090702d8460880043c80d00317214800c01ca604c404045251036006e5044401d48072400b6000180941859441441d10b420980d040c8000d40d64802d020100d60401100d09100d0640c00d642c0407402d040c140ca14070b940d81c811845010001d03052028841003062143c5000030040213000029511074500038041034907101c02d4400c07003010a00d0007a0030708400850030000c52045400c0380c050000c9074580749480d00900880d620b290a49900c02c0402440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 314984307 1250 314983057 314983061
    0x4020d1a0109050f0105060705060f2a041403070f050d440703020a0b041406010e0a0f0e030a12150b03011e080d180b032a031b090d0501 60
    0x8100030b40010506041c8044100c003040c5060708143d00410040000401051000074004d41010301884501002e5403004688600b0701075002d10b1406662a00c4014440c5c480300b01c01800c10b84050b0040700180070010b40402d40d5549039440703501541e01c00c03040100007a240c0751910800440c01456404000c4032604164003458564288030202681d01510801c44c45482511602e280c500c1a03511614190b1181c4001c0c0d5661000308000303006280b0b80000504018890b4100c00c0e110164108442165031031f0200030600000c120352a40040c0d15100c10ad10059103d40a0183c03e88001d101030b51501c0b81c202c00898080e42401c0069294a46078241c888e40302a44491143c01456604001034580d410442190151800000d07600401d501040701407040c800f0100e034641d460b245900f0000405501c0b006440c01403481d544c81403404083c04002c01070400746403592101d0341420340c0c2c6461000c3c070800040700d1f10f41c001030710603401c0703281c5034401c41c07902d2940d18004000840e0000d0a040b0750b0781090b564682 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 314985557 1250 314984307 314984309
    0x10818011803170604061d060609030105090d0305060306131407051002070806010b0702310c090312180b0c0a1524031115070f0b06011103030f04020d1a01 68
    0x381044803c0f0b00b20501d54500160801d400b22030a1015600e07042520042800804081585040c0c40c0049901540e68004842025201070001e21503446c00c18041d540728043e00d030364080420b0070200095900e2801086103071186044020380403212080ea1a8405091420f0018014034828400c3c0850699100344603000c10344207a5004004240c20001e803d802c2500603809002040340512030600140d60315182008881810161050850540b205200d40b40702c800095500c26894410408410755201d06198162800f5602040f0b191b400c3c2e9104803041d00321044d100502c60581c80307051011a160354010440d81c0f51003002c640d01550303a6201c510b142485508125509941e0f520070076458085049040c07240b54a50507030320b02031403940d110190000c16048042e485002040e40c625401c44038641903c03440f0fa005040114142c2192a100421181c16600980030907000c03103044030810742c00800c583c8920b00c0900e501c8480e8a80f503091141301140490304680040c1a42c40440c882c89944048078 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 314986807 1250 314985557 314985563
    0x180308092b0f050f0901080c070f0c030b0705030f010e270106090606050a141c02030f01030201081021020604080d0903020406050d0b0615090604230d020108180118 72
    0x29035606103501d02412141407055a0828400b041c4a080c0101e0a0030702901c0d08002c1c20300f4180220760b210008201244200301c402411003400d41c0210b403c0c0800d200c00d460a0724460a4032803039a0321803000a48070750000b1215080c40c844e01200500c05407404004090f00581c8412140381c407403d174030380e1400400e80703260003100807a1741d1002c041281040c14065040200594281b0a19150f40107000800103c018440041c20381d00000f072050203082031140e07a441005e50071038219244e007403034810380040728000e1000340d000a4103d008524204142240b08040360321402e081a9000580014081d66038001e1000303a03800003007072100040100c018031051100c5030786643e030001b196055104010407200150000313405003406150010010b50160415a044a012123815900c20658600c9040320300ca21a2442d0304510b000c513000407003105188503150032640903030071640701d00c540c1414881d0141d40c0404c060700040150011400c01034015402c42c140103003110020500c0e10b10021281a000302001040b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 314988057 1250 314986807 314986873
    0x10209030d020f120a051801020a062d1104090f18030c1703011508151002100e010e0a080705010b09150405070207060503060f0a0e01170f0118030809 66
    0x2001c42c2c2031081c004d032400f6500400209060648a0310014424000d94288480b00c2e040b1140c07501c1141c1c020040242c0d0780303500000c00e00c6544817200c2040c03e042e180c0400c4000c2d0b040c4503098840841d8850140e4600c5030091940170782400c0c64810608044c0c60300c0d042d52002c140d6690085a00c028003010105041170207601e86007c00c20b52454215140850800b540d0b0303181030203000502001d01c510f01c01880306032061405108584448407000e940c29100c80daa16170001002960025064000ca410010300f104442f0070420301c03108601407400e8443d0a54155004e400040c5c00b0400500503401034000c0d01c0c001e100004070746250801040940d18103031100c4240e5040e406400220b40303401d028050340055a840507150302d501c2c0c080b02901c40e00001d8242c07485580703001c110148030b858480a0307100030444104040780c0d0f560364030040d0703403000f81041a0120368026403c6480e000785050040c08552030070b201d100c0c110304641340c0b001c45002d04044c100f180c0600a894441c28240040d01151825841c69420 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 314989307 1250 314988057 314988073
    0x120a170117060c03070e0409140a060506040b12060601030c051b03040e0703091208060316120201030c050a080a020306060d0c020606090a091707081204081c110318010209030d02 78
    0x220b4a0010b0040c60036040910401c100503503194044016418200103550110b11480b00e45024040c07000110300072003461144032644d005110941e0069802504191000c0240340e28100a010520010486410b0180c0c00398010134843c0d4480c3d0301a44000f000f6160440c1803080c0080c40d45000c006a0800b03c0b0b640c5d1000c40c080c050b20000080c429004000b505081040d1580380d902c446100366858904810700c000c010011700d084d1000c0c020040c00350408141d400120341c540025034042c0000c0b400980c00286461403100c80c0a0258044507141c5d0001e0304d0322a561360350300d110b80000e03501c0144020340218007401200c20504090240c9055000719030003920380d80c80e0a100b031040c2860001d008404082c10200200702188500011314041b10311505465525003141c01d099800c0d1003000d08140801d96144200001c0c0401e881c05494803c03c1c0007030516008500e02488025284004a080e903803882c2003010546103800105c140076921800f400250800107400c3c0000d040003566000c0d0009600b00b419 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 314990557 1250 314989307 314989349
    0x80f03030106020c060c0a020d03020c060a080103110102070e0a090501060504020a21020a0f0302070204020c070e01060306090c090b180301150e0105040203010311010f02070816030b130302120a1701 87
    0x9041031406007900c80341c5c06c0c2404140030a90320181d401010340101041d00340141814400c0c00740e14031400010713004d155245100900101643c5003403100713584141c2940c030040c0c0075600c00b280e000e0884d194102c840c126a100c0da08120001d184c08070040701d941d907a030080000c07503848600240c018076105e134071340050800281d01041c0c030f030300c103215101c8014034810401005002d03044600da00c2c5039409442c0c0140c0351290792001c0f030020711541000c01c2c481d100d010400907216014526550681d4403c0d0340520585a0b1980c0e240d00b9550624075140202d0800300050003600013180c0503182c1480d242036608040010314001ca421500000400c0c03194820481c4203205c1000300002407801040300752021440c561454850170503400d1010b1189041220740400c414503a4070801603103016020803003c3d6060b0911010488402c0c041c144411104506c0a400107128600c40c1c550519950342c25070003401410030501d254807030642c0b0120801003481b0301746080070709030465032025601070701c1c030070a440c0280d5010785 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 314991807 1250 314990557 314990563
    0x30d0c02270103150b12030301091d120319020c07150c0b01060206060a05120613020d2112140118020c010e10050c04060e0603100305010f0f05060303072307080f0303010602 76
    0xc81c289006015241d1404106c000006c03c80307045603e43d4130009106101c00780c5031229412000029501480b84055085001d04201c0085011f0000290941d034848600044641640980007020105030064941006201d61442205460006a20f0000c6203a40345540d0100d0040f001e8002e40300592080c0108061802c00c0781c0070f4409000c003190b1803000d1200002d0103070360311000144042d0707005102d1a4854119210002c4003221540e00104403880c012613464425542080005240000780c074038458020911491312803c151941d407942a000703d6803d00c2c240080703118080d14045075481d0708001442c520102031007403130b06d8004000081c0140a2446c2c9058060342c0d4090104146504c0420080004c41d4120038114a00b00c0155151900c0380c6c3d9001514072083c0e000d50014241d5400c00502d0414400c6d10351002002e4801003c041000351118001c1c50b40c4c90040c400014807210006000d07a080d81d180c2030340d5610700c0418500b11407a854407880d05c24200351641582001c81d41c000300050059503014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 314993057 1250 314991807 314991821
    0x30207050117011809080a021501150c020111033a0c0207090c050d061d070302090f01050304020a030f05031b0c0604210c150e030d0c0227010315 64
    0xd20340025004502d014407018a9818480e10f900940031200400184449801c208403041e08a8095502d5000801d8041d441c1e098611001143c407007420b001042130740041041c0c1c6040c02c03596950003030418481e801554420308218402c10213120601010172900c1d0b40e10160320140f43c410454001c5903108840505420450385203102d5058100840c1c40c1c0980e6000940204807401c035400840d84404100b07081e00c2d5442003845840320b560404c00c010901410100e501b0200c42c81110f107000c403940d1802411022170280401c203a03484040741400c10350035846400550303003007400200804401c0c6d5496503805104e02111b4421500c0d03030408202c036001d0368a140c0c0800d5203569114054001d081490f000200c02c0c1c030490041400c1c8407810000c40c90003c078083d071104a040e9100101c09a000d40703c07d081c0a00e001d000400c03d00007035911502d00300504000c42c802d4030014a94441038541c3c1204d908200e44005070000c14104e10b00004024076404502c081054001c0d80a400c030741c64451102001e0034155820 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 314994307 1250 314993057 314993059
    0x18020414030d0f0c0f06050a0608150108030d0b03011b0c0330020a021c1101060609050904300c02040506120a06020f041a0a020c120304030201200f010903020705 71
    0x20b5003403400d00d40000710b1203011003291503c003001c08014a00b2005001e000e130070242580c1c0ca44400c200c4403a249034484820b175403c3c02c0c00c41d01400d41010f074500300d1303900c01d02a805598201340701020302c0b148550081000d440c2c0040c00416103007609590707081c04081d840000000a5840e041c00703400c3c560031112103001a04255241421415414042088007190208021540b6800502c1d103c85910034440e0510402801c2006850034881490050008400d440051010f504c4c1c1800002c140303014160300d030100e401c00703440e070000355440c0d440301c200c48400d6900e6041c00103e00f056081140380f05445035010390245458001640b01540103000898500400c3c4c240101541100e030b03c1c042400080f00d007030040e44184050b940d0304140c8888211030040d6400400e01c3c01c00c00341c8030410222000060700e0180307441d90840340540300007410002400a0b10850f000a0b4004010038070155210700c1d03c1c2e1416110500a1185a0100030502c078036000d10146410305503550355800e4020154103001c04c00013040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 314995557 1250 314994307 314994313
    0xa0b0906040c140d1202070f271a2110051320060a02060405011a221413060e01110919030f050607030606020712020f01091802041403 59
    0x7030541d507030002a0155010b144400750b00e0444031036035aa0784a00c8100c40c150701c150140c03010740300c40d24082d42d200c02c1070084803407460a0720700c0403801070b41d510801c01e50300401003101e0a0560681607e14020101074080004440c100040400242c903095400f80300204032140b600c96400000c02c180f41011040c10502082d01d00740001d00c04507500d03d4008561458100000c60030018840c501943e130803100b0020240c001d400402c501c80b00c280c012030311a10403405000244620b0044403802d40d1007500041507690f001d1101e030380030907544c8590075017030709902d140010008100d4410101607019444c121442000e007502c84c0b107802c08100b5140100d98291070640001c0c0401d01c41d980d40700c04203000341e0f0340d098011400030003844804e800000d040c5005541061035021160814185580c8070030085603003a000c030f4100940041d084ac0300050220880e2041c810641811100c3e1b420080440d074180e40d85030412072178403808030744124965040c3d85000c0c118540180c0d11443d28052512460116001502ca50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 314996807 1250 314995557 314995561
    0x3030403090306020306030c0301180c0f03030f120b0406031203140c04180612030f090e0c1e27030d05040509040605041a010906060908030a020d050d06080f0a0b0906 73
    0x280c01c00c4404065075440140582c8035524000428035146a55000c541c2c10360074451803501951190003003d14441c0103401950925850303014003032240d4038600c0007d0000b4078048160508501c20301c502c2080c248110808503c40701800700140035690782d90030076141c110346079000310607458141c854002c094144451001851400035060400c070b000f1403243d450744660000d800780d0224100c0d0b0240001e8502000e08200802160400900d01c9900c5850302c0081507607240d0108129140900352407151b8440c112a03403030861200da0307080991809606081e561041884104108031407100301000c1400c06860f0800150101d008043c64213420940003424840100000c0c0703c55152a1070543c0c0c002d41102d80490f81c0d466526109035030350a0141c003059110304c80000410008040c0d00248101d441e181d655200503522181d031b9644038880c40e40b4040140e8003a800071a4142d01640c0601071900800074006412230303640d0301c51402d00001c1e03000d00c2c0d22500400c0c48141042003502030940c0200d44980180494 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 314998057 1250 314996807 314996813
    0x60609070f08160513032009040b0c070212030c0d0e04020a2a1e02031002032403160801022206090303030f1523040506010903020d06060806011e08030304 68
    0x50b10151262442d458400700e10001c2c0c50240e0129a85030082094040caa03941c0c0781410922107400180016480e0f54144d00c4021514000442e903002d150041c803841c200341c8518020034215444860101d0b048500340a08a181001c07c1c0007902c08030702014003070b00130101c0c40900100141e0024180318841c034412701916581650062868203590343d030f00102104c0d00b5088026441c40744080c00c0080038803614130303c1c0b1100700e00001c40300c01c8020710036000c5500300030800308480141c1c002228000300c081800100b00b501d000c0c250040b07506030b9101600b56482c0dc4a102051201111290007019442c3c0d000a04503c043c0c00110364042c5104003807a003441c1d541d060144c020310040d000d05c1701a04154031070030b580781851040e50004040748007402e0045c102e2544c54064940796120100403103010184004424003e044c10700807140720b240f0503500c40c60010b00b56800c00034031405805065402c1136441201041d0f500301007203142c0c06000c802c0e0600d880c00c1104900c0860030a05900581910b4205000748800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 314999307 1250 314998057 314998067
    0x1091517030a050c1501060c050d030c080606030703060902030709030c050603060d120e040204060e09070c1e050111031314030a1b06090501110d0b041104050121050702060609070f 79
    0x2102e40940b414995030f190311180705140100d40165200000c02c1c003000083d00681005040c002d141c40303807043d14407032002d9010030f03422626010100000311303003100000b84c0c00f4944100215031140181c200011101d481d002c51800300d800841b1000c002c14250441403050015485584006200888142d0324520700107020810381c5100480081240e145aa1140a00c6010b4a04881400300c083c0007192203035a103c1005100d907003050780041c0559400c00c041030b00280b0031715a0003001504001030008550703010700020207031150b41000b80c07041e541c1d410002c4c01c072010281c019801200c441c03107180ca06590904040036032071011400a0000d600c1048440181a0455500200040f11341ca06078081d05d06800d02c000a080303201c100030b000e54030300000c040104480c60050b01055841102c1000b100c40c921050104951f05244d1345941c42d50305000030066588140084d2010105190b07103c0121f41b44a03018205a407419100c08025810010400c0302d0303030a0500d5120f81c489543d103804c410107004181c000d02 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 315000557 1250 314999307 314999317
    0x31b09090210051308060406020304061103060d030f0e1f090608041505060f0603100801060515271c02040b06070b060d0819090312020303040206040e0901060e0109151703 75
    0x401d01002044e400001c2c0d0107503001200816500c0140c85041c605440d09000070b52007110204d41d02440c100380e4803081001d0f582902c2c4101d501030503841d840380703054500362004176034044408108500100040200c2d00d40992488840c10714291200404e01460b4020f0031041603038016200308203101e400c01c40410b42264070201c100c040d03000d0006c3d00303032280808070b404844401d00c806e400503c0042805070b107900c0c03108104125800741000704982c60301c1d84100445103048a2200504903000d02c2144483c0920748141d100c11500302d070340c04401c2d81e100800f00d1a40611042094410202c80d506402581000d02504001910803584180341070a180c0e0b41080c4001c001e0b285d14007030208c10700e85408110310f00c012164a80d1500506111002d17141d58010181002130100300c07031070400180342d1901c03203000105484c0121f50040c042800c060800caa242c0701c1c1900100240015900d0703001c001240c00c06911703503a01030701c0014004944411001c00d00b1404000c1c0b603000051070032201d00c074040f0095021050311 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 315001807 1250 315000557 315000589
    0x50603040305251202030d060605160b0919121b0210110a02131d060906130602090411030601030b1905042427020406020304030f020d0c031b090902 65
    0x41c40d120001411203e210009500a180c01454003001006035000800b03082d070b12480394010301c60b03907458030011a02341c01880c010481d03040350599038600141c5142c602a50044500c07040f900070800c00481320000d4806603030f0556022a242c280c018400b640300000318450326004c074243c0300d10070700e5138046a0500070080b00e503020405103c1040000311014400c0c0140c0d0703900109a2a0400f03145507030000207041d042c1c0a00071413018048400d004481c042800b500c5014544c02504d010f40da01c00c0d800700f080c1442c010031190b06a01b0081c2c9059540c0c0c0b48079141784c500c0040c032519101d00d00000058121840319a48620030513602c1c0948034041d428244a0007580c40694006c108020400704c0c04401c05e45100802c44944c810000c00725a41001000411032148889008000c58209613142d000300c0c46240118030040e0020442440032450301d10b401c4041a05c060300340c070034600c142c0d15243d01c2142a60011a10384040010b05580c4070241841e210241503105010000f03504c11740c1c0010807540c4016402 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 315003057 1250 315001807 315001837
    0x403031202040b0a0503091e0f07060e030c040b0a0e310f03030c0504050a0e1e041101140d050a05090d05040e040f0507050607080703020d080402181812040f050603040305 75
    0x40c28410b003444801408c280310b88080341d20401100d2888d496284000380f400d0389101e00500020068030500810842d894064080d282043d001002d00029081e0711003219000354613808005034084443c260755104500c582d150103d8100c070301c412001c4003081030026161008032111700c500403400c0340310340d01281d03503260074006045082d000e000e0311203010340d502c03407a8840d1385440000380c100c000240851185900e10792810350300034000080c10f841202690301808899070385007440900e5000300348044220400003200c0c0d040011112042c8162170040711842a410b840e08240000030400f0844404900c5e414105a8100307810322440d041c01001c0180064400c602d6258440180325040c00300101404000d0182035440f4100d0900103081c1c1d216030802c07001032161400380c00206204002e014040c3e5402000c3c0121810341c50120080030030701a00e0701e20000c0041c000030401d000c080180020714404d459541c1d4641d498848001d80c03041066200038014141041040f0020380e0000032100035042c3c4200c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 315004307 1250 315003057 315003061
    0x20f010f120b040618050603101e0b0613062105012702090612011406090901050904060e190212011407050a091503020304060c0c1104090f020d080403031202040b0a0503 74
    0x14010306110b80c03008022071754950805500701a0341d0007031440340c8020340464104086a60170b0000300c0b0b591030544000c890003400c0c1284038045079042510721001c001d041505108e812002c1c545a1800c40d445040403070700ac20600c1d10b50a08076007001c0c0e100700c0800c2c4200204c0d03142c44046100100c900201c2c448800040700c50301d00840b0140c1c191a400311015200075107840781210111041d050070702072121030041d000d1411105180c140f045030700684026004008903460202408041d1001030801c80304140c6034804055054000c0020011124012410703400c0c2401d01e00501a01da00420000c106a9040c01048880f0017400e1801c2908242030b40f0f0210341d5941403903801c841207100d98011450041c50400102401503240e00030f1401035008170010003880220324800d580011001c03070010409640c24912003294586680560f190034040c0100d0515010142d000601000261208036a4840082014001e259000c86081c8e5000d4800c1d100310b24003424404586418081c50000341c08000c00000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 315005557 1250 315004307 315004309
    0x606041508030a050408070f060906030203040809030a080d15030b1b12090106030c05010503060d032001050a0912020d08010905071209060b0102061506040b0f0408100207020f010f120b 81
    0x190420050800c01d055a44074112140010f0642e8024424041144914000460500c08119046d8200c0d5425101d00d07240e50302d400c1c8140e000c0e410080007a625104140714885440d10103022490045101d495103d948500540d04003040340c030020f9030b003818021000720902c00580302c1001c0c10340081d1f008510611400301c004c0c807118148151811034032a05082c0d018480900d030150003160990703125281c107482894499004407402d0004850040d40b0198032688800400c0c01400521140740301020380701100100030301980d00b5038105440c2108160b6031a2680d0007800032040300c80400b0345035480a00000d210f2040010500103040c0078010070699654040360f0b0304d0b40a01d841b210202d900396070a004140710b50602c00010880d0001c01030140c0075140006658003040304400c600c004004161504040c14002e980d817160f003003480035491890041201140d12082040410082940c1d03840241c3d682c074403481808a60514062102c2c14484400d50364040550440142c452000c17aa8500107074401001c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 315006807 1250 315005557 315005591
    0x4009061b18050618030d03060509070309051b0a0f0303020a1e0804030303152301090f0b07030c050708060408031603060608060405091501260d0e0909121801030e060405060604 77
    0xd50034a40c1072243c6c0b8682c070505601a00000100c450403500669540e1710542c0540581c0c3e403016000303000760824505100b61a00a11500c0f501140c00341400440a4a43d800801841100d40054015038840350803401003026002400d4414400317014507040ca82029520744405004034080141490b89881320b03044800c0e21007002c0e00042000d8024520342940141d1907010044100315468000b80c400c15011840e24240c807a924111442004503900e8a401524103c3da480000d140880d100d00900c800000c0301541048298010b074052a40c850381e07400c01100441c2d04e10841c0f141441070500f070503000c20640b0b07080400356601020658012500366210742d84541001c4c203072824164008500400410400064603440589200710404410741c8044049201e07602c544000e000c00008110003011a094281090701c1c5800c01e09501c00c0707481002c01203044001c5900201d454581c20042145064850361b4035001c1d107225901c0340f101400041c00c1545a803521510b006200d28020350300c070046812281401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 315008057 1250 315006807 315006847
    0xb0307080c09090103080403020315060a060c06020f04060807110604020f04020c01090209010314010e1c210204080109020405012102090c120a0903020c4009061b180506 74
    0x41143c500d66850b403400e03a207540c05c13a02040e4040d10540d00150400107003540b09600506000b0240c982d003a250003002c8071503c04004044541d141c09001d004260301c030780d0b400b43c0f000c0c0109446030a024a0b0135030005041810404015070039500400900c000b60b19501c0c2020714611040c0e07409650380708080c81d1a805441103000003500184160000010f00298400820320100301708000d0040b080d25585c002d949240c2c40110780d4441c0718001070b0704c00d49401881108a011a80d11051079154400c600000c100d810541c40301d0400c4e51100e140004501d05031080078094680ca82180003000072000356440200c1d50360400030b00680c5440701080c5020040000e503401e800092012b1200e03481c1092070070015041c1e965080b4054030640c11000c0d11450205141c0311070341c107120343e0705042d0701d41240d482d0341580010182c007004441c504114001038066000b500803d07401148d0101d0641c541c5c800c0100c94484462400c010024040072101c03904110298074422a0300494429454102c40202190f02c100d07c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 315009307 1250 315008057 315008059
    0x90303071d01171608100503032215050307021e030901031e06060c05010c020703170a0c0f2a0503030901030b04150e100506070b13030903171201080102040b0307080c09 74
    0x3c02002c1100c000c0c0300c0b500e4030207542c03e10740d55003c098907081300d00100a103d070b0240b0307075040e08140410484000044c070b14114501c048090714980543c0c400706410046403c0d150310000420000810001c1a0100000c2000c20000704054250b600c40c41c41c40d80e100c0c0100040a410961681c00d0540c40306610040101940038004041204659508005d4404060b12000322029400d007001d00404500108610040301d8014030402a100c24802e481c12031a40940303544020300190030350b40408290b44002501002c5d10810b00c084024018000100c1d03102c406c04100301c40b0140034070061226807804400e45100a500f820045811102034000401800350f20380041c0411640740030000e14007000100040c001c40c00109488582a01d41c018087d0a21640c48081d000312803c101280030103000c001d0b0070202c03c2c020b03d46180d40e81c0d03d80c0e070f84102d1601d003041040c0742100045a494580060307041c040f80100344d80d100852400345450001d00440c00001d00d1a82840455000920324088140c116004514 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 315010557 1250 315009307 315009347
    0x10e061009030c08030a02120304230307060504060f14010f0504020c0c06030408070c0b07030804140a0f051b010224090307050f0318041a120a05010203010e060108090303071d01 78
    0x900c400b04166260040c202c80001440f589025038004508101201e01640d0421940b503c1d03c00c0c006241e4410403004bc0384403030544020003070100841d841d4483c1c58019840344001040550f074071000d09056600e1410b240343e10b00d08140c01004040341c40040c0c1001c448003034a0243c1c907200741a0070141030210ba0420365030054000000c00080000e814028456a803003a0400310710035846104c41e0700b050040420041c08074003000041404203900701b040c8002c0702141022070b900c1d4600c50307540c44520000140112103076400b204035009560700b079031602c100d030384403c1c03004080e03010341c0744000c0c820810907c0c007a140c03102d01040450074228051048580161304a800c46086200206ca507551b00d90ac210420307484900c038205c2e00c1082d0320b8140a072000703c0014949101010066604218014211224820305841005442c200182d4280061402003030701000c01010752524200140c401e18004109100ea81c0081081007030b055000a10040220100060510b0805171a030045e510329440c9003c82d0840c01b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 315011807 1250 315010557 315010559
    0x50702060610031d250f1a0708130807060203160803040609050303011203020705010e010c0201030509070518061809070e101d1005060901300c020706020c0603010e061009030c 77
    0x3c0000603d649907894192100da5022207421044031440d030180981b0700800041001000364003001038003600d440f6444180e00340b078000709680d604601d038081401d101e1417502d084010481900c0601a100081065002071072030200c8115055110104506d0000c05c2d01d440407001c581484250303070019503c5c03503021003225500c0d6120350b41030300400040380c01100107114029010030554401c0134040b020b0401038503007035140301c0541d00642c0076042c0140600d00ca03116035a03000400d0780d201c1510002c04020050074110906000b424020f0ba0107660000a08281070081031000003030300090541c2c00c0b1410784007060626292100d18501c018550f0303000122003d0314012940d120303540c0e1180140110207100709400081c0d900c00c240b007054040c09804a000c55540b80c1242c9a106044005800850039484009000c4450403035032022241c0c00030148005900c00c2c90300f8045540c04010040b841030040f80c1c4e03241036601d04410400040c20080656007c0c00300d107903200c650140141c0386c50028550040c5040f021f5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 315013057 1250 315011807 315011861
    0x51b010504051f090f030c1b090e061005010504120305040302033406050a050d0b03071512050609040210201b060c06010b070f06020a0201060e0a05070206061003 71
    0x7000305003483c80c81c0f9080c100e4000702c6500300b4412002001e91010074a044110142c5040e02d60040c48641500d00c00417008144810a40301c0d503800c00606142c20000541e6550a415140340010040034141d20a10a010074000c0ba0380160580b0100c0e085030f11902c4000b02e07a072a0031a890300556000941502c5000542c1800c030a64080282e4100f085c00c1528280c09041007003202d45820910a090200d04100708407081180701e003004019800990101250040d2080d01081c54421603901011242c51342c0210b1071301c3c20f940034900d1002403020000500181c10309100080031036102510081c801d000030340c0c847c0c0b54035000d58440e405040c00001840d008840071045692a04881e24503107411480605888030280307482d2040d51a402107050013481c00381e003040117030300e030690103a102695100c6200303115a001075040c0c00100351440d955030000c902103107001d141028070607018116000c5141031804000605a0020752154051070071109501c0420f00d0b08800c1e001011072208000c00d20426940903220 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 315014307 1250 315013057 315013063
    0x323060a0524090a0b2103070b07051309091e0b0106021009110f0a050607200607030c2301090609020f0103060305120708041701050406060e0105010f051b01050405 72
    0x810418007004482c003080300440301d682c941c45290001e5202900340080780d056481e80c0d120b111504000380004061466404200481d54004003406050354000a00b403c00c010f0142d840315000511410518140005012446121170050142c01c2c01c07141d4a0b922902441004406070b484540c01d1115190f40c100e6604050180a500340a45400341c0300b010780e46144503c2910494030b0194019100d03e0204001d00100281041c0815000d80d100f0b004440101c0e0a81e5040c0080c0510340c0f06d0014000c141c5052501c1419001034040124420070b814001c3c41d000c01d4212280c0d5a001e5031004c00c06000400388615182070115455038220198680f580b408100199980704407083c50080381c880187d0f08103030300110255007041c040144030b0b400004d02c2240c01d40d10392020303251141c03160598605181d11014140d90054030344d101908182c3d15602400140304052007200080c00c3c14040d072000643c10940041c00a00711a4201410407400040c00714800c110501800104103401c0001d00c400e040a06009a07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 315015557 1250 315014307 315014311
    0x303062606091b0d0606030501140702071208030a020a120c030212061203040308030a0902131b020a0302030a0e030c1e120102130e0702190302071502160323060a05 72
    0x60501c241c902084485030001111505010400c4404114000c00d8003400000301400404440d6552528030100004100303000d1400205603001d861103a5241c01c2c00c1c02864080103600c0050440003518000012403201012240c1c020f0382c20038007580e07860078040100ca1280d4908002119a843c3c403a0341e048030b03640764004100104021301030324440d03250101000108c00908011268652080204100040c00030f00a958041c003400c000050500603030300030590b1b00c540424000b01640d038912482c0c8140b40b03400c10090607100548014180a181a07801039607a1140c440c2c09014810204424041c656003003101079000b99020700300765021000740c003c00e40015403405841e449030301000c244100c803010520039a0b0046041c44820350320f461078000c55406030080036007070034114010402c02d0030790310300381c400500b02c0d4910a40c0100500c1d4680700d03c807580c0f102000c541c00210340210012202c0c0f60140e022040c140c2c0e411103804180244a004000c1c05500c4a00360302c00640280d10801c00c3c5c000c030507840a8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 315016807 1250 315015557 315015629
    0x9280b0d0c080c07020121050f010905090c03152703030a05130b01120f2f0f150c0312090708120307020303070815032b020109050a0609030306 63
    0x20203a0070020405450019085510076485142448014090742c810031128200609200801e00200721079a50702c02079400c1107030590000040040104220300440c448c4903888042d10011709900408134001940f03a044c0070b401d00161914841c0440d1020141440f8948001101003448a03401c1e08112100e8a9406c2201c40d140750728540f20000d200f450001c0d00445a00da030140d600348541c0c0c00c010704e0000c0b40d07036003407401c5e241740c28080f0901000584403002840040c040c09043c510f1500110342c11161b224031035012501074031f007041c1c440ba003a4860042000b1300e900ca9400ea035468078030341311380146103004a11107030010b040500c0a0180180740400c44070282c070007031008d035148100741c01220386440c84162a2103005a00420000300c18502c288880c41d000003140e080031950f00d0401000905d0202d00d0b450b4200030240d0000010b8405a01d40441c0c0280507490000340110142e0b52141901c914120402412060719064200201480b0b170780800080c024842d500d050065401408500b41d0250284c65 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 315018057 1250 315016807 315016811
    0x60c0a020f0901030f14030d0e0a050c1504031e06020712020708011415010210110901080907031703040510060e0103060f0e12130807090207150b030309280b0d 70
    0x4074000d040c80101241a241c0012441000011a41c0c51103a50410b10910b183c10340001e02c100112105180984a24482c00c40020f020000c080d003132203400e00315281222032290400f0420185800880300540e0300301d03a0418803070540400c2000d007588103c4030020300241640e20003d80c1070b041081203c2c81c40381090140d030848100700e4031145c0c450f088421138603418800c14100000510f01d040ea07104200c01d480b8040c4161615071300e50300510070079203c1a041c4e580201d980410307140444c0d41e00186041c3c3c4003001178000d01c01246103840d40d00030401c52b044440c85403640000007a080c03100c1045800010b440380c1e01d0812055030b0303070710418661103c03e00040700c50a080002c0030290000074003030540c02c421200094400d002e40801209803e501c1426103060030740960100040919051007a200101845100581e072100756182080303d50100005c40701400b4904030b500c200c02d840c000140c4400791025240c921b5004100c1800302c0400788001c1c01e1281084c091403000c517550745020081c0084131911001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 315019307 1250 315018057 315018079
    0x21201090504110d0819030606020f16120206070b0411040b031c080613020301080c010e060406021506060c06250c080708030c19051e04050105120a0605060c0a02 71
    0x800d400d036081074801070150004a03440700b07500d1400c2185410100e00c20f04641c0d24220800749030401003120442201d0102c0d660711710800103242c040c8141c60351800311601422050041c00031030401e0283d64010320f84040c1008255004644a440403191040c0e00320b0018a90b9280078a42540d58400c000f4150b40128201405400b050a00040800101500700112995600b08400807030ba1902e00800090b4081c22515220303001d284039100440c044e0004002528207844654009071801e942c00074514001c0408100030401d099001c12022603600122009041503102e0320000b404034080c0c03940c5444580a14020322103d40e4424110211442a54001941222101c441640c0580c2d4031203010f0958242044060700141030500150f41c0503195035502400e20100040030700c1d2042c04800c010380450360000305018a1404a1802c046c003085002c00140350600740b8000030300a00540c942841c64410510110b01040026000440079010140400e500d443c0c0d245d1714142d482c51003150a03402290040c0e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 315020557 1250 315019307 315019319
    0x70f120201020d03060e0f0901023c0310090c02070b0301080d080a0b0a0308160f0f03080c0a211407030b040e150601050a0212040303050c0c090412030f0204050402030109021201 78
    0x590340889a17481c031b0708101e540d500c244c0075003103400051400541c1e56007000001043c13125186490180b8400707941e02c00b030140b40c41c41004108030300c2003412181e43c90700340100503600ca4201c01036009e0f42c08107000422801e988540507450100c1315041031248250120020591810006003144030051640d90b1501646800400e0030403210241e0f41d403504503d20002c140003045c0750b20020a48400c000e02958008540e5848420704100140d904440300100c0c00040420b05a00c04102d54018441d4016240342a40212004d000101720440200403e075001519480100b41a80000012030050950600d50314200d00000c3c000c003105060580b18624000d00010781c601c0c0014074050040084d081c40c0840d48448006441076004003494a0441c0716403400e22071100c01e1f00002e44011440703511415221410503252a0800c8070009140e070040b81d1280030040030500b840c115110011040c1000a4140101d0080f20080d1260b0b0b0026500680000000652003245900030700c050500306201e100340b80d807540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 315021807 1250 315020557 315020561
    0xa0c03240c02101e0e060601110624010c0506010f050a1d1f090c050715140a020c0309150703020d0f080417040509160212090108041202070f120201020d03 68
    0x4003122006900c440e100390004900c030350000d0700c0241844013112001d84291021803d403450035003407201c50f802210600090303580050802c0003200604000e0407a600e403800e046111403611580000a981c4074020100c5585d0241d403060304160741020683d1030075130f124421801c11070715030722034a402900070784c0f4005441601c06034240441c070000103180070a07440f00c44090300030890800d1100380710040724a0014528134503100c1c480c82d01c0138540700c0940b600c8242c00e00a543d4140081d1020f102818004c901d05401801042141e0040701808010b807604060b10060785907015140c1100d800480b4080c40d80380703018281025050031846507080340c19500e00e04a00303d58010303445203c0408102100003050000e4803010f00100280401c030303103c60034160794a002400029040e100b084004281210f00c3c4021079042c4071080060078410342261800d004200020b080b080002c4c4081c1080c400044040d000d2403080c803c020050180d1200c0c06c0e101502d81c9003030030641721035240480c05807054800c0c0340000350180c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 315023057 1250 315021807 315021821
    0x5030307030206061009080601230913020111010204170631030c050a02060703050d0501051e01110c060705030a09052d0d0b10050a05060702030c01110a0c0324 70
    0x55406410f07640c441100b4010801034288410084c40385001c07011038850000c0040d6030082c82c0d08030b10b000c1c100c241d11984100300c0c240d03184102e01444140d020080e0000841010b054990b9080c82c0c03499a0801294a180c028021600101c0103d0300010081c2481000041d00f0740c05010803488120030441c040e904c00140365091417034109102020307584100802c0c0640e000d80325281c051020342d4800e2081e980000e4a0340e000800840208001245002d0010054451503001d05803c1d19008010016400c40180c0e80e9500a20f180c10840213003070800702e84200340f000c03603001c010140c007554486110349001ea8a0b60440d45600000a0383c890380080c01b031403c4042d5041c580c0080020941d4802404504c1142d144541549a08503092001400c0010b2005482a00ca41703404902000311034141400c110040d07515603c5540b00301001d00043c000350342c001c80c0070511400f003400c1a10100029a2440f410305103070781c00181201c20312003c0017041c40b0b600d04250034481c1c1000d080280b510181d4100300121800 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 315024307 1250 315023057 315023063
    0x190501090501050a0302070b0f040302150105220b090403020c130504020a2d091b0203030c04050928020306040c05161509020307090b0f0d080f0a0e091f05030307 71
    0x1903200104401d501540c0241402c1c074240c0307805031501950761184600e20406443d04414640c01070104001d040d41442480c0115244407803203165545008001801000c82045908500005078111003002d589503120090004001d00b8402d518a41420f01940b07174401040342c00d00841c4103120071070841c101c2d0300c00c8611996004011030502410510b9401009203115982c180d090180143d2810101081441200801d00e0517030104120b0800804d1400c07954190302c0200c255801030003400100b10070002520255030b4207855215555845103c40c400e02200501001700550904d40c41c80b805500c25001507100d40780c203442c10300c69000202030464071031044589800a0810b8000040300062009001119507404160013051400c4a5000a82401560342c004a50316996100341100c82c01c164085d0090b07500102c2d07103149004c20700c1d21071001622902c101603034003d00c0042c00004040c05040030a560640203400c580032440d144440f042c00104d101c119282010442c0340002d807603d00002150039881d4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 315025557 1250 315024307 315024317
    0x2070608040804030519021201021e09030c0a0f08010b09011512150b03010f121a07030216050a0b1f09090f0204140f0a02070c0506030a0f0e0a02190501 67
    0x49464411110100041e204444941040000102081042140f808003410f901200d50000006104004800541c2e04544456034014080100c0800c180340304104003404040c5034694407201100020b0520700d4a800c4203621a1880c1c4000c42c00aa003da500000d80d0310720740007042103500d028108100c1403024410820080d03043c070240c0ba8018031400380012034501709400400c0404041c0b60380345683d54030345c205a1400030044010842070147c02004001044800340004408400d40c60713501e40c0c0744450f04030075100d507000b102240741e07a0f110360b04032003140fa002c02200d1a5440e0910300740340c54030301c954810b859012110010030903400300a003800030423951400400306150719050f4140040c110b442e600703540c03c0d21540711200158442d0f000d01c501c2400c441c1c810303803803601d002168100490701c0904142449481070100c1800210441c00e204260382040702c0140e1660b840c000910013a0142481111700607041400a4135142e0001a41e40703d464400c4a104140318400200302200c50024030489002503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 315026807 1250 315025557 315025559
    0xa0b030601180e1e0a021f080721060b04231309030909180302120a0518040e0114091e0601030308061809161d010b03070207031b0e010b07030207 64
    0x1c00d0b50b032240c4100410a41501c248440201d40340b10f40c4409560980c0141d04035006200441c40c0c000040a03144e4403a10526019121800000345801c00040c841018400c14540c00300400040810708035110221010921035503442d0702810903140c000b0b1251008442c00000e200f00303105000c103044040d501c000b0344034201080403032401c100136003031100b07041e800d2000429010540320201e0058000b8030307090308404800310289140080c503103580085900c1d0169000c0c08101590b40e400000c0390440c2c009820b08050180b06a00054003d00050345104015071900141003809042042c44a01c20503030b48064500020124405078500ca40c02028800b140d0000c400500000b8000c4a1080e0008070107041841095455030802068400c281d130f1111490748000c0705a00034150095400019055844450500c0b82554409104410060090342c590203808800200002d01c02c1061800441e041040458042d00f500110070316030200c1d0141d080148002c500105400c0d20803821150240c1c0d06030300800301d107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 315028057 1250 315026807 315026849
    0x80a0506010212090d06020d0b0901080348070608060a050127030f05060402031b030c090601050910120f0c17060d08180306071b080702061207080a0b030601 69
    0x5035003c1c0340a254402c9800d6024170200707241c0d101a00d0203070140340b4001f0f110900b007030030400220016031107807030345510400c014410b881440b50490800c070502ea00301c04044d0403600105901d9103690b2018800e41c110300c902403d002400150b10412030b11640c035000c019468000070302c0b00d02c0c1880d0044502148040d00c192010703c0070414116135646d180c4540d110701e29200e560b0b000e15118002c3c0241c07650741c4940184001e41c5424464400180806080c82420382c8420001c00c4c0c9a20b00805568814800d580001c1c2d050f034051000c98810002c002c1043c8041c0c0c12070310b8040c0c0003200003001c0031105454a001082c15510724420700244007013640302d141c881c44454181d4880f034013000b403c1b65000b13038082c40900d00142d104006098a210a112070070010042602403514220b80105038404020a6042c0392450744c460802c0f4240e4640c10180c2c0c07035610000d03800842c1c110320a98a005000221400401c00682d40c461101800340710194810720200800904041d038420703080c014000348082d803a02401c00d07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 315029307 1250 315028057 315028093
    0x901080703080714030412031b02011b020312031003030809030325050c100e3703021f0501050913030e0d0f020d08091306030b06060310080d05070201080a05060102 72
    0x420f208246001105260401450031a00176920910008202d001d200082540104900b81c1a507421005c0201049c06900002d0094202c0c0640407001a468040070003552010300510800d00380001c0d0306a520f04144117105845901c038402034000460034004206012008001c0f03902590b003080041c0504030380c42c0c03100a5150303002c540207424000e00300f1121b000c502d424082d11900802614002a010000703845e00c80c10034000c800e1a030101c500c3c14403942c4140252100045c8030510801418024100ac1d20b000d034605021002000ea0005401d006501224039681001d4180d40054130f008800392a84d541403030141403095402400305914802164440c10205107070054076006003403100c0324185a4000c2022203a28075030588070701a00044060190508852072502e00d01181800c204480c955200c00104900147c08284120b2000000c1030000c40041d00070400b03040c03468281c03180f01e1010500070305654003e0200301d003c100c0e8940050801c00e110301c42c0620994068024186034240700e81e21401c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 315030557 1250 315029307 315029317
    0x90b0415200d0c2003030a142e0b04080607200d08070905061227062a04081b0a030b04021908031803010b030309030a06050406061203030b01030506090108070308 71
    0x10843d80240001008107030184e890726050401d0091035a80c140a0b82042c1510031030202903038044854002d00154800341c40074019001c08080b03d1000c100e19802c2c02564042043e40068074808011801141c03404011a580f80501c0c069150200c02502d490181d81c1d40d160140701c09021500144400142640984106540311950b8544030030040e0700d403000600313582c01c2040d803031460070001002c10000e0814404c03042240c11740703840040070385440c41410365070300c4800401402c00b0607460501503142c0f800072442c040c507140c54010034035107032901c1f281103695500f031038400d09a03034211030243d8080030309124240740c0a40340c11800802b02c9a0b07940d000d00c04140c015103200040350080b0500065030700003d00280400d4800890605c075141c41c070070300b09401d50b103030a28406c0c400c0c1c00c100842c0215503000a19424001c0d44a400415599504e04041005012a500501412805440520415905512000341c01c00300741c904000076150b0000b0300101d200d0900403c1034940c04110140080b0711342c1d5010701 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 315031807 1250 315030557 315030581
    0x20a08070b07211409030301080a1e140610050105070803010e0618070e030610210501061a12101406090d0f030e0a0e09070b0a03090b0415200d 63
    0x4801a03105141115443c45021000c039069a600e01580e100c0000510190402d000500450855041000c82615403501076001004040c00042e107404050342030242190742508404600221280304220381d8403540b04441e03040d4000741e0040c0c003041940c010700c191561340b6040446203003141c0c00c00e50458000c51019113903a9000150192050760a021503110313a10903885c6913141005e0306030480915140c0b145c0500030001c1001d011205120000c110341113030f051200d0303400c403a48244042c0c0c1083d90042203130350800800c200748030f2245c001450728040104501c02c3c2203410044181e607490400804503502d8090100d42c80c03000e807101d00e12072401c2d5001c0c00391500020700490000840c0d90300e0300c15a1805050841c08112012001680c52504e039071148001d00c0031500390782c51071415401c0703161104018042c00030b20701c60201f96140810301c02c1d8408901641e200c01d00c003086082504010590380706503800c40419034280070b07600d1125036007424420107103015001e42ea4105620254008044c2c980f422802c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 315033057 1250 315031807 315031817
    0x19030b010e040912020706030506100c03052101051c0209010608070504050402130608070507030912060f0e21090109050913050d0509090f010e0a09150c0519020a08070b07 75
    0x7440042da41c62203014115882002410241c4c5021207020303007400045ea10a0f4149032400302000581e4a510250020021880c80d1110a4038610302c0c06407118096a003480300c503145600324070f1106a8068005030b05986045842e00040c0055408a0311684000031b4001d410488050041101d103008421042d000301c1103080090616441d900490200d8004107000d600c89c0316011420401c107608036031400e404c8131013444e100d0b1074601240c8010b818409548501000105403075841d00c10b2210a910200340104040300901c101d071511902c09a440d41616198100700d03040b48050581d00e41c0d00021117280781c006031200b11a0b1860702d820086098002095420310702801c0007030b803000580522210751513940715103072682c40c0e0500340140001048000c00d81802c1740b40034801482a214800030b020360100c00a0340114000e0301d980781401d164800b0000142456003403144c0300460940050250050b8a00c100600100044036101241d8428049101806c2c1860401198010550070341c91203500030828101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 315034307 1250 315033057 315033077
    0xc04051806120d080604201617030a0e07050108100b0d0f0e25051507050a061e050a0605010905190506040e090c030d020607030b220e100219030b01 65
    0x1850801040420f11400244248100801031829100303100400b496020020904010030b1004c200c1743c030801942c14024a4a4080001089860781d0100e0741e10700b0b81142c0540383c0c1000d00c003140c060009659154482d005285003c50b4551145140034420858480d081703e05514041550504c0d6100416100020741c41c0c5400d1a9010441d00030715142c110210002d000182e4000700482c41c95004c840070450f40c4101c250100030640e50781c8203180000040c04086540c948003841e085240602c49940205070504102d864281d076452032014052401440d101400140c3d680f5804204403900c81c007455000c02c0300500300348500e042c0340c103403507907a90600d030201060300e5190030010f40181c000754440200030545000b00802e0410900240c0c07207101068005026142c44c03900c0194031348000800c3c0f00c0801d5901c0c00515240d68581100c0e5410541e042c0b0840c2d08000d924101d0409040780e48032884051184844072072000b00c0c50310071540d040304800e8000d07010071420751084010b4660804158100201081 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 315035557 1250 315034307 315034339
    0x20703020d0b011e08030901030b18070906031a0d0b040c0b040f060311120106050309070e010b090f10170c19030b10090509011502030f0a0201140c04051806 69
    0x811000850080c00150441e40c540f01340380c072410400704407082da0119540c00401050384000709440c4610024240450300441c44c0011403401481450f070800ba40480b80240845c3c2da0b044201c00043d11400d55061050319440d44c0e101d200320190354840346d0412407482401000c0344c5450384054200c2e100d50101e00300555070316006461a04590088030b0059025202000aa0340601c10381f880c002c0f1050815081500ca00401c00701e14405100c4d00c420700c1800800600214024032108001e09a000279141c203a5031110755070310f819004410010701502c02112542e0043c82c1ca8400c541c3e6290311a40c41343c407440025090748600e0340300070b4003400215005102083c000d1400c0541e801c0224999907001801400d441c0802000050000b240c0c0180490102e0a00140e202c0c84841c0d415259404041d0702c01100104040b4a94401d00f0b003c000007210100d0704825185d03040d0400c1c6407000c06003560141549803426070081c00c1c81036104d180d510031410854180040300c81045694003810003002d500409000074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 315036807 1250 315035557 315035569
    0xb0c071404022101080613111003020f16061d0607030f06030f05150106030218010c08040e130c0605040b0703110c0307090603170c0a030c05010b13021b1501051002070302 75
    0x10f2000d8828480303030005201d4003804014450b0302c00755590415003090f20a03214200500c031304044a5020b034110b96840e17140301e4042d030116800c9445601c3c0c00c6984002d01c04941a041942002c11a555418400380101883c0c00b180e1600d038180401026010326180c41d03406400504201c00c0203052661586000008a4a1040c030524040d01990103081d0403c8425405082d07c48140c20003030500d4814021542195141402d40c840e114080c01d11000c40082030400315401d01aa0780100c40001c4a03000300020f5009124140310124490743d04884a2b036121003064030580602c3c000c1d8000e00b4828880704000c24402c00200f0b0000c12458140c646110654001c00c0c1090b0301c5820000d4030740c0d1a100c08104008071100181050240080a6400c01e000689240c0d2036514410000d405c100d84a0100c00034000700b940412a010b0b4000c0903040850308200036076020350080e041d80e015005000003c602e1080012500d900301700c0a80d00c2000003030303082608220340008148820b40461251540100068503a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 315038057 1250 315036807 315036847
    0xc0503030403080604150e01150908030a0519021209090a021b01020901021504020f040c170103122a08030915040c30080a030b0612070305010b0c07140402 68
    0x2562024150f1030113105120545013030404c5504c0140300c19904201203020070309540e0545030300c5000705401d00c4d49800b0480d0b00c5050364218181ea4080042c00c2241c0300c2e0004010200084003007032060381d007041ca1005170f842d03030354500f644101103004012607102441c0000425038884a0341c4801410814410070362903944007604130300060781e036001a00c644517603010040c5084401c0003100311482c500d459404106d101c06214402c40c040d5442c1d019054001c1c0c09102d460a41a543d050030303494039a903a0500a0500e060721849401150100c0400920241c521609041c1080c500c20300a602440716070703ca104690009220341c8041c0510402c00c1e400840c0e84507064026809801a030140f1818070702070300b01003c14400022141c00704034071800c142408440c1940d42c015003148445403280b410308402d90207801c1c030081513a41310f0340004001480300c1c81c1d501701e5805404142d5080245070380b0f44042c0d1500b8442e20304c0f1034109600121080000782454032001c02c0681000e4000344c03c1c4010b0f800c00050b0744683d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 315039307 1250 315038057 315038063
    0xc080a02070e01050d23010b220c0525110406030b010806130f080c0109020d060504061a13110d0207080403120c08031501020a0c06030e12091804030c05030304 70
    0x4841c0811101120b0301200d030140c802120f504a0005260b601d01060075850300304c03100c07541610a60a0310b03400080d800b0107200c04000d40940c0445161800c020702d180c2c1102d0854110300d251081c1441300b039204801b17940d090024007080003541c41e0070f00100034040101e004c0c100c444603000302c0c1c01100c03615603018103001103205582c015015410003d4040c10950001c0000d8002e0403903040e440d012441a21200c01c441d0342104a0310740c0d1b6811001e5041c0540740000002c0e40100320070900400b081060392019120702c0c0954400c200c03c44503000316034910300c1042d1802c0c0e40219580c9031140c0341249680321040d40c440c4180c0d00f07071900d800c50324030f4420398100380e00c140e0f034018012a0400030b1055461401d00112040c1c0340c4001c0385c1e101030351010312500016004004140b4200048005070740200048101d00c1e400121100e8425624a0000c000d0012001d010000740940091640c1c016520000c0d41d000d81001015110a00818905501c071620001c20980c2044022007404020402c144000d42c0205c0c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 315040557 1250 315039307 315039313
    0x60f18031407060912080a1d09070c11010305010513150801050a0204081507050d111b10061d041113090b040b0105060304020d030f0e130e0601061e0f0c080a02 70
    0x700e010f00141c042c140603481a5503528007041020002031046084480503107290420242e00380c2c01c5285101d5030342c288016640c204074803505114440f07410044c585840d03840741524240309840f00c40110300303841084c480c25400940008101030300464070382149040a20346508071603880e507158051400d4800c10b0f41d50ba0040350303000800780304501043c042c122454075640d030020350a04001d080285203116041c80440b1040e550f40420b001c0303207a8071044403081c04480d145030240a15110803039880c0c5507203149a6500d82d2070f0580006204d83e00d8071000100c1000d104107401c0d207a89545401180104001c03460b64848081d001c00b0004420510400da0000d0191100000c10314140c6030149070700d0381c182c02544c820402802040011f96a8401650707002d50305280600e011100305600341c5d5031070031440c152640504074a4084c809500282d100460200b446000c44200b41d9940000750ba840342502c0c2c070003684c4140d0350802400103002c1c0e02028201061880c00040d034020300d0301c032032020b60050102030005070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 315041807 1250 315040557 315040559
    0x6091c0b0a0606051201090c03021c0f0c0e010c14070503061602060a050108100c1206080328050406030c090b0a0f02010c020309010f1d0406030804030308070801060f18031407 77
    0x512880b550010388002d0a140c0d207400340c8030b03400a41003241440350b031400340d442e80040c0c06c1c3c0c2c511a0b0142c405c86480c00f2030311203600782c03620366101c003070200883c5014904c0d02d0300080d41c1c0410701c10020042c06031010b8482003003642c0507480c3d640c81409a00124100b900c07980600003403070b840070085070303101e1819407480304150700190700c0007410300c240030740700503505401c0c07500501c030040001c100240003403616800060300480d504e4094503003464280c100744045203010400902c1460100042891143d11882205015100c8c121032030301540c548aa60001a01880107000b5517000c2d5000442c00d9106042400340c5c01d5075070f010074980341d0191440900051a03044996625602405001161034590001c0c41c104a40000000c121124400c0e05204020107056020b0b241c0c4422600d113600804044d10512240ea16414117018642c81440100e000421520000300014420318490b410399605945600403e04040021a111102c50708101c40c0a94501000400241003841c800300c0c00c040352010345045 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 315043057 1250 315041807 315041821
    0xd020c010e010507260d0b0a061b05010e0708030c0601120309030b070201020f1315080403020d0e0d0203150108161a2b0c020f070806060103020c070e04030207051c020f06091c0b 78
    0xe22010302d0028050321600e0b809004940c0c01402b0395102611030740c440341d0712049609190b809402c5040d500c1a40f801856004101d2520220091002c4420310701101d820740d0703079010721142402c100c070000340004140c0716003440020b28215095070007941620002d82022035646101901e94008266010a82e0941c1f000300000210490880700d40070650501540514154030041c0d1101b8035804c600c0308002c1e20214101550362148040c6041d280c0113800c440f0040790a228540c80f441d8280140f181c1841000e1040490751000541041030719040d0381e04040f42001150703030340d020340c02c00f0905c030a144151020b5410304c00003000c618120800320314404070707400c0c100580290a0082401c00011a40c00041082c07195000010320300c2d03000042884c00503503036006c1d80c1c05a800d00c1006d4111910920f81e40c002e0005255000568000b47da0b422070309218000b8800c00e902013410718900c1c0080d0052001d0121800e18074001000e0301c24100e01920694807140090341d49000c1c6050141c0440d4102c1c44c01042c0180 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 315044307 1250 315043057 315043061
    0x180d17090a05030c01270e0f151005070213092f030a0b040b0c0708030901320f0a1107051506030a0203061302030a1e0201020d020c010e010507260d 65
    0x2002c0a5024011200f51840024a0310350400c010004840b81d002c8900028500b01c07102800034020401c8030141402e1060b500c140c482c1003610910000f9028480c40d080300e00d40024200805542521001e1401c1c0e07052782441040e6400016500351541e84010306004030b008100300100e66044000e00d0101c07400460041000d2821241219000c4e03408490004005417402c0300960300141c10683e510b03425980d0710a1812036124184005001c00008400d002c0c1d05441504840c2c1c02c2070888582d50070764240740d00c22424020542034003041200c40b10700814402c4543d01c2d07546070004081100410070143d003030f01c00e004a80c0040c0046607503030b002d400903800b400e88181d00c041d0801800c0f4007a140e031030203a40021b903503180b002e0f0031101c0080c900e00801045503030802088601c1035021102508440148101408108010f0401d038098015801c1c0c800407540b02183d0008100d0f01610340e1451640c0010044900d80c00c01607080705c20040750344445009015007100e81943c40703d12001240d41d07146035030310001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 315045557 1250 315044307 315044309
    0x601090c1b0311060901060f0b031005040c050711011b1b170304050112110702120f060414061303140f0403050a080a12021e070302160806011502030906180d17090a 72
    0x50991600310103000342c019a88c0e406c411900c3c3d031140903440340c8854070710b18440b20140d84041da02a20f00b04800700d40344c1e001406012214040d42c12410140b038088019200030b03540d907030801c02c40645082c0c444000b030780003a60310988042400e5180700003a100d8010b0306421240440002c2e07150300208081240b0b42c0d001540796075440c0102420f0200350640c051303501a41c001c584009100b0320070b241c1040012103040180b803281400c07a408491490600c0e082c292002520310344001d07200c0c001d84000807694800300f021404229890359030525030910071002c642940c1c01041c0d043d02d08680400001010803010400d00318000c0c0100405581c5814070b840c06030840c3c00e2220a4a5060300502140998100301c0310603071a440d031200401942c8403102c0c50100e00300010101441c118003c076090100d000d54001440d20b0584074140d86204442942180682e903901400b85c8040d03001c00c003000f240020031a074803113241c400d00c805081800d6461a694072600900480d8000380408180456486c1c2145000c8400c40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 315046807 1250 315045557 315045571
    0x2031906080a02040e1603060623010f0311120a0204060806030d0e060a030605060c0c0f031b0d03020a14010516030603050a0f02030304090e0319030b030601090c1b031106 75
    0x318903450003040948428648601910482c1e0b280c082d100c0b15081803196001d4030000c10860010366480e45820b00044c1400d008000030010b80301e5411200601e401c00542c41010142c6841c0c1004c080f20f1003c6000d00458090629404401d12001020401c0c00a00b240105220781380540c030303181041e0b001401e01100400146c03082d07004141a01049801180b400b46000c025a421641c940c4070380e00c26000361600d6405190401e20004049503101804140c18003480d004030343e6503c0074141e00081540d502c00b900b42d10186510680000f0001d480c1c06120344403001e04c079005a60042810307440300440c6c15120241146103944660400041c000c0da442c80e0703404224507040070403600c1e080d40c56080e5100c1c6c44080003022140291002c40a540c2c04009440080483d05001c0c050140c800010070b0b00d230b80044050b44500302d0b2003a04d14034550300030b000e440b20301200076000f0105030f0b190211143c050980c403c031240500850500c021001c800b20342d41180220b0003a212640c0c501c941411851034400000c081e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 315048057 1250 315046807 315046811
    0x10609060b030f041118010e0903070812091608030a090f0503030d090f02030d080412080c0d1505100e0a050306013c060923100e01210e100c0c030507030c02090703020319 75
    0x982cbc00075039070805540c5070007400b061b20001962a23000c114500342c4180802e18503035180345000649404008020308980c60185d850840b039a688400f60f000c0800745010b055419001449900074042c0c0030307800880098001c442c208041c0c2c0c110b4000ca801c1c440c450480b8000aa0240d08001c20b000801118400c011800c1c5800c0426141ca002c00707043c0c2c1c2c09101c0308049010f459800b1a9084600820748001500e4010000458030003448000b50401c0001c601c15401555041d90015051a000c114141254002d0b41c16648100001c2000e110315818080c0112000c2e0f6005551081c1410050801025101584800314428140f429401a04540d0074440300704125500e404840c41d16200e85851a1305000d043c00418051010016159021a03040c140c000c805690f480c0c5004510f90340151080c0034003803007500c08504580080906030b4500740c100d1004203a1561049000078450070052910b240245800d0901080c1c1e580042c882120586400d0002600882401030381307040000c0100740c01a06000c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 315049307 1250 315048057 315048067
    0x1207020a080a141b010c1101060312032406020106230a030b060604080f0304060908070b07030503041403070b060906010f020705091e090a0302010609060b030f041118010e0903 77
    0xc4007180c1c0b00d07114a40080101101801c03042d18120030a50f00300c054035038180903840c070b86590003500a100d1480c01800099500e0282c140c00700044c4940000d42c0d4014039001d1903565002c0d42a0040c0c841408800081c4035600c1c87c51203180fa041500310050403c1e903002041492401c061050644410001c249080c650918100226511511140d0482c4d6008582c429140d4034500000e0580c0103603030011405009001039900303198030100007441038404a40f641c09055071202d401c00e5032002180604802e0140400402000c64007071805107074050320601c02c4500410141c10214103581200c1d108840070402c44c01409990720300201100e03400036080c178040007101c03d80c030340080d501c41e100d01c81d05014403288404958950300403000d0100c170f020f030400c82c4d05480c2060000366965400d0f500041d0b0040d440c259011132401c0103401048215030b60050954203585990100d100385031000750080760007071001c1d1103c0540761184400c0c0ca034504500d1205c52a19890030001c6440080c000b030030098540c000f040f07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 315050557 1250 315049307 315049313
    0x1418030a0804020102190c030b01060503010303090b1e04090917130302040b040902030609060a14070507020105160c0f0e01050301140f040521180a06020c0d060b0d06021207020a 78
    0x10554103046401e103007800307081d102ca00050713041c032100000c40110080c4808a11051101400c000c0040341e1140f085481c0c83da982e400700703c2d420b0200380001000110928401c100011040001c1d00403618090b404107404040c00f100718049a10030781c09800a152107030712400074800c03583d0040203c12422480e00d450f100381d1410245509142d408000d2003546c0e50710b03404003075440d01c4c0e00503481c4030750190450700c0f207041c0700b2020360362024111890301c45c03541044603c080c0d546034120300e0f5000c0d00d11a00d40c07505055169006450680001c0c003070812000c0d030348102c00e000c2070118003018001c3c900032002d24040340c180740403281d00c204140c2110f4020303030400202c8041803260b00406540601e04c681da040701916a4070340302c0d050001c0e84020034001d00a10440c1035040b08088010080c00c3c403400101c03099803411500380840000d00348100c1c1c0140c1c000b40c1030b11130141400340e41002102d00c9540000344c8500e03050300103414804030610540d80d150340458a007101c140c07984070140e04090140010809000750750307 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 315051807 1250 315050557 315050563
    0x2010b0409051911030703052505030606120a0c090605011b050606040b0a030b0a050f06010201090506040620072306010e2409040f02040c0513031419061418 69
    0x22000c1c0614451031900c2c0d018840108400b2144c01e0340203082d510741956a01b0240d6603025510091161540740400d840034a10109815030101c0d540a400f901d4070303030350300e00070031618140000100c40c01303020307900300007000039a010002405003061040020700079040100042826003080400785811641804090200c0d0380003851a40c8501e0440b00031845213001d001180d400c00b5140e0009040126000500c862010246c1120348500407500d00103409076940c1004a00382d0b5075451003d06980c1151022802041041c1c001c1c020f14070f1030b80b04a04d0183c01401c0042504d903c400020398203045400d480030140c0d00310003110501c0142e0040100b40c41d50400101c5980e40101410484110110b8141c114141491411404803140c000388045140e2a0501782360601011a440c100d1142d841c041c003044182c2e0081054520030001c00c105d054196003142d851001302001f8015890700c0d417003800342c03044081e045003010568803846048080388005006100401c0800041d0951400e80e125032909100b0031000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 315053057 1250 315051807 315051823
    0x91a040b0d0b030111030c0301030201030b0d030e01080c1308030306190602030423040203130203100204080d120e0a0524070e0f2e08060d0308062101150602010b040905 74
    0x1074070300052040c05280009005108160006a00f5040401005507109104000d50304a034000e8034148a100e03000c10402480e0364820000602203041101d102200354490000640e1001c01c51411503d881d80d50348114040b020035a2103911150700c00020050141400d0001d40e00304a0848100d011250030104003940701c2c0201d0054940204000d804112403452070125420410400b070f1085590b41451100e990b201c402d813507010303806841452244030350304031148212412200c01c3c0d00580079407111103000701d4058415082071600c0c944c031041c194211103014480580403620602c01800d502c910740101c8112140081d68176081c041a0740c0401c1003030390308000607044c0030100301c034180c01e0021128009044000800e646215440281d06060309090716030b00444004180c645403003407107a450008010000c080110010001280180410755a04200e4200311110000c045428240c0c0d4100040a0856038001d4200d2105001242c00b040b1464081c40b80411400040c1d5081c030400b402c1e6201d0360342d91322038 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 315054307 1250 315053057 315053077
    0xe030a180807030f0c0b0307030b010e091b0c0705031207150615030f0e0a05030a0306210b190c0306060806091b1c02040e090705091b03070c02030d091a040b 69
    0x8003501184c03c01ca0840c5c070348406055070f4104a9201d06003072a00134001c0081d07030360207804103100941ca8041841e00c5c1b82c14a1103071680d100c8465184501041a840f16004440061458401c1e1700007c121507506010080d00b0741a41e405d076940300d40c62403c000b03450b60b0540b4104c50006141000a0110321816a84c80022505c142004903422500e410017900405c13000c03880d0846801a03071004010000003200600026106036014030085840740ca42c0e00e000318079086000005038054116030b0005000e05440381d4880040e800c1e030080001d0320000c8009442c027914407100001c1e5101024006643c0188032140c00c10000c0c0c50031401440c1031108110b988400039640083d2100100c0c2d01010801008640c248207147c0c02c0c01991625900c9000142c0c000c2c096076403450038041d40d01c01040038100111014801c4401c1e050080b815140044080305980c809071200e006c000c2907443c04009a03d04005401d24598560340d034a11081ca070000c440c2c080081800b80b0400c500301080200008410402a90381d0440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 315055557 1250 315054307 315054323
    0x1a04060e0c0301050d030e090405070312090e0a0f090c0e040203070f050303070308270601090e030a0518010507060212100602060c07230d0f0f051201060804030c060e030a18080703 79
    0x16506047d1401441c262030154040300b120200b10810501150200840c3d11584038004086d8080300243e0314611180204040842c1160010301c440c001d6801041c1460b929000028220f0f0707494480c520310103860b811200722050400280403c43c1810015a00203210456030b503210345003803800190300c1c1c0c41102000f6081021200102c0e40c540c40c0509a500d00b07005040780002c80f240b0462445803954000d1003094002803806504000d4a4004011034182801c40c0e600d0341e242690b140c1e8a0302500e29100d5070a07042003c1809148000f030014401010000007039096681e26140144006000004680012045421800c00d012403800503609451480da0b1003e25004020100c006030a51510b00f043d220745203100f0200302c030648070381214804201c3c0c9001c0e52281800801c200e400d403240c0c402c0a0100105407600401000035502c24100c85412034400d10b0b00a405e4030603a219542038038103040485800e6000014a00c450329040381d80403080c091000c0e0402d142c0c81ca08005a034460700700d8400541402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 315056807 1250 315055557 315055579
    0x17010605090a091a040e06060a0e190f09060b0a060503150d150b030607020a030c03120e1b030c041b0818100b010f0804230a02041a04060e0c030105 65
    0x10b61000c0a8001038441c0020403c80302480c12112101c00d2003401d400c83c00349150801c1000302034804240c2a100d2134001d09079205641ca0041010b14050005081c3d15034051a00c1004a40500764042c07007500d88103541010a600920703042440483c0c0b00c00d500d4900c00d46100c0410000d85401078260317580860b004a8500c050303c12079020a070008030342d0701c004250303d285d448440745e000e50a07444000070380360980454280360780e4003e069998100340c2e00040c002c90000c00040c00082c0c40307410b502d55450602034002c18031002880c0403074a003500c01400d4180c045225400d00c01c0c02c0c1002c002c0d03500d0896044800740003000015810700d41d00011001d00301c080100d05800100241c41c410715000c506003044007240c802c109210910001032122182850000daa0418003100c1d061240610720702854001003a04806224003d0102a03a000d56816002c54042d40d06180e002d0307500da10851002e90030895001c0c0300c2c40218020003040307891941207000d1054091090008a103e0102907905407041a1341c150005 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 315058057 1250 315056807 315056809
    0x90c05192610140603090604080327100e1b0411071709040c080402130b0112110414100804060902060706020c0a0215031b0904240609061701060509 65
    0x200d9000341070070140e800410a2000102116034484120340c46a82070303034550a040c1c2c1c10860203100c1512030091961040000c503000c01c903510015a0800c801065100615030140d0034201c8181003603880036515085600c0200300124940103061a55001d4000340007035074203000c040c4010b061809002d43c0203030b0f903c080d151560300088044420180d081601c28032210510760b03591286900054002c1d01681c104a4a644500d0080744640d0045034018020b083d4009a117810400504140410300d0402c16884c07205003d00070702e40b060385400d0010719102540e039410142040d81c0910b50340100ea000703200304408680e05540c00a10340307400c10741c84080884c945102d070000840d54000d040c0090300452001950b4000003000044018480d0310980755031010800f9540c05000c00d020481d12000c0400c140215059102072840003820040b000410004a8a010f03800070445001c8400c100014508503600c2070050503005901300004120500c0c240c0c1d80b034400101d82001c2804103200740024084085000405 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 315059307 1250 315058057 315058097
    0x10350f1b0307290f07111012050a0617010e0f0a2a0b0a08060f04050c0a0e041d0d120501080705010c150f1a15070f020109080a0302030301090c0519 65
    0x145240d000c2140f900c030140401c0c2c4d030b081c0e40d00c484000ca6640200b184011380074208200405d0248041d030312144914088040c0700c00c00307403030010070b800101ca507101404244880050522922030b01c5860000401503a1002d05510784201990380c0280c0381c1c884200500022040352014101ca0040400b24540100b0020f020403405a00d81209600d00c0012074250482c80d40014001c0c80390030201c5810350103116940038001101d40c15600d06862510810280c2c2c1074601801115040100c0540001980e84120070300f1000b80d8a5040c001c0c03183d8106480c0c984401754080f10450b60300b100d00c40204a9545000d42007540e400c4103101765410f201080038030406101c0b21400c81c140214404006010200c0000d40031002080081d80108483d512842000010304084840c80c4e02124940c0c0018078003140b9480b00c0f0b01691460408a041007045880851141000d0241d00f00081c0f183d0019a12941403400160544e140008104104081841003c07840b14850050405c049500c1c100b404000c0c0a42400e002c07 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 315060557 1250 315059307 315059369
    0x90207080a0522090f0b12070b0a05070212060403020d02030310050409020f1201050603210306090c040f0906081014160225150810350f1b0307 63
    0xc030794411400003135800c0d80b500f265180708030614040061080b403004005c0300c0a545e83c0410415032001c0c0c014842e040a030790042c8402059414841d0400c00b8641c0010419640160301c4001c42d00b140701440101901000740042d0740800d40055800c601e011030a42912209034401c2c2d0780700b40d86480100d400d545032292009031208002d0030b1621042c0d091800a030103068240d803030a00030b1069128819066160f6004440010040c104a40c41d5450302d40c1001003140300900070407940340003044001000403105003500001c0c54200b0001c00c0d203c1c41e03e10034600b0040300c43d010442040c1442103090100c10a9000a54811084c11840c0c0100b030524004038070300703801900841c2d90006240101680c0c80b04101000d000c440c48000c20480503400300317004582083c03059a0703c1c400302446e42c506000b48056200b203000041ea40401c0d0b0340110b05041d0b00500703a5400c110030300115800007a0503104540e000c2c0081103040a020700956020018940440c5d9a21118440c006034542d41c00d21142046180c0c0303010300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 315061807 1250 315060557 315060607
    0x60c05070b07020d0e190306021c0e0d0e01080f0708071806031409030f0f03040305070204060b1b0a08090105070804091401150f0801030602091903031107090207080a05 74
    0x306291a00010113503803280240092008541d00401e11051440d0104040900054140b03001c1c00d035a103580e0700c42c0060341010201391182c0401c11f2510016800038821340f0300c2404040300424608052071805809940020701d840e040211840412090590100705560403211350f2038001103642e1104401c4070a083c5120700301c01091401d2000103595640354000ba000c000e0401411109a2556403815a491113210b01e62100310205126140b2002d40c0d40010350350140c028202245021480d50010b01120402c1c0c0154101d1500421214014800d0610464500c600701780104403406a0b500d034406207000701065503040240c009500300400c1002001d66000384128070061090703881266854445000c01d0141041c1c4201543c202d01d41c61303119450b40d40c40c03e071650b11024480d908540307600001e0750240c40099005903030350028075207510078041040001c40c0207035a40c00e01d00207c244650300f0208241c3c0141e00c002d005011800c041400541140c1c1c90b440340b400e00c1640c440d1010300c00102c10368030340105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 315063057 1250 315061807 315061823
    0x20117041b03060b0a0b030f01030b040312020715050105010e010e06090a080a0f12090f0b070c0305060906151e090a0902060403050123010e061002070510030f0c05030402010c060c0507 81
    0xf003201c1034101c401848021524641c003c0d0322001341816a0100300c1d910741d440c56190004001040c07200d18140e410600070b29000c01d690490300c4041099900186084a00401c08103422002040a00c582405007034240307400da07506d44040f0002001104001c1340c02e4402c8000041e4007140341e40d00e044407401440400c0c182c890410160400f50140d0084801c152080e4a602019802c0349119034509816111540c0c00d04041a0600d8003d1040e50400304003203c0d40c2c50102d40101c08280c040100910503680075008280c2442e022915181414130340f41e0b028040c0c4412850380c804400d81c455054240401690021030642d10300c0910740181c00059406504002d00081c040180001074000480c0d09421820305200148403011500300b0070703024860ba1642c1c0300d451010607468034104d210207145142c3c41c030440758401d0303d441c0042c229101c07003c100808030f070360f44c0100c000c8144a401000001d41d11420490b00758980358001030855a207400000341102d030380d2040003a0013405039003911040703038001c480c1d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 315064307 1250 315063057 315063059
    0x10091107032c0a0b07060506190603020903011d1f020301060f0318060606020a060e0606090f090114070c03200307170c030f0c0c0f030d030c02150f040b010e0103020117041b 76
    0x720512617101c0750701a5501814140007400e10704000c1140320140a101030301041c40b034a40242200250800140035600d5501d90101310b51203200821040d0903111108003400782601c0c500d0407209808a14615400710500500c0104621608030442c03061203160341c100465401c00c44c1e4001102d80c0c40000c401460289800c0700030a000d5070024144145501c01d00381001840c002c102c0655070341310100c03400e41d0300424510004858520400c0100e80101010f4004501101c0510105140c0041101d000700003504034224907050691060100b5481c1c070000c01840421000300d090b4603124411500c0242000010800c40201c855001c01160b0f01444400c0076a92140072000d03403000f85500c100d205205074413502c0d1080b5058030b0207550721850104010014020141d25207010340123020705038200300641c01a520311001d01d004070740718030744528840000030318145410b24108203409011780040c8144401c800c018030050741c224a011600c0c20005da0080440c0e074807440c10841c103460035103204403083c0180174 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 315065557 1250 315064307 315064319
    0x31109090105150d29090610080607030b0f15031603020304120e03120301060201060303091d1906050d1208130308040b1005060a121b050d0507031410091107032c0a 72
    0x162071b02400303c0e8016103000752100100b0b15001b030004d008007a0540c00170000f017020700f4040c2d407001c06810000b405031020004114001032140b035904160a80e6032500004111401c244070bc000c8980c0e282d41c0c1011400d40c2170988070880030341c0401d4124010f01680403c2e620340d65034100300e1501d2001030461742603525030312908024082c2c43d052100b140130961100d008245031000150b5016800e10040449006588184000e90540c40101c1e03820041a50380c5d2000c1003648031800415201d50141041154561001d0710080074004020810381c890a41c50b190310000903804940590800d811a9011049448071025400e40c440c40f54001d6500080c0011800b16642d0085800d4018403540c1341c0c20403941c6038288818040c20a8202540700180d010021001020401c5c3d00540d04000c09203800100701b030381608080038486064642008071075a10200b000b500a660040e44070b1140b070895000d00b0481250341c081e12650183c0300d00f0790350f4044500805007015802c072003e001000010207003840143c0e252 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 315066807 1250 315065557 315065633
    0x6040305070509010902031621020d061d0108060f090c090412030c020303010b07080d020903031605070f05061204030c0803100e06040b01140f040906031109090105150d 74
    0x201c0b91500a450440000a203900580700340e0340b08281103401000c035484081801c03205500031800e100e1080704151681c20148160384050100440006400070345681003603280c044c4a41a170a007012a0420301005000da508046515500304200100042d029261a0740d5242003480b071800042c0c11080f800200001e000d40d005082c0210482d644082181c4003201130f0032a2a44424003904a80400401c8202d00207020170006215003150094014203000d861400241145d11401d2100c100f41044181101404404d104000003014a610703003485083c0381c54003103110b9000c0e0a00798a05442c0d0107001600b4140102c8184400d070f82d0104442e50f480c50411154282000280905036007002c00800050303240c2000e01c61440301c00c50585401c8490a003d0340c8140e0f00b5403000d07183d000b2820061200144008460107032801541c450300903031144901d000c09104c1c4801004102c8103140c0e040000b40305006010101c00c01091100f81c4100d802c80c81c0c5030500f2101c4045403107441c0030f200003006616401d143c41d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 315068057 1250 315066807 315066809
    0xd090308090606011d150301060201060f120c030f052b0e030f0a170c06040809120c1e03010917090406050a060f03020a031b090807050a031a04020d020604030507 71
    0x25214400300307440e5020080d40e2014202c90040c0401d40c01030100f045110118064102c0740310041ca41113406048203110340907038200307901c8240581c0d104d0000b4801a60250b0764072000c1c0102080102c2d40b400d0781e44404248458611000e449044003131214410b00c1800d00400c400c0904100e00c403024925044004150300c2c1e841d000c0100007a925580c0e040c000d103008110807621401000050110b07009523100d41e00c03029603102080c80030140402010150100510100d403145025284c0341d0341340e61820741881254420412030011b550001d00900242c1c0e03440e03041010314005841000d03141e0f00844400f00f40149940c25001d03101c030584401002d01440c66400506030064283c0301807110950b5201402142d001d0390140002103002e041614005500c01d80c094030040b440c9280120358510329285520340c1c00c0440c1d440ba00000c4980f00c06020b104400c03c0350100409055404891452543d2200c05900c11115503c509400c20740e0b0125065540d40b070f0320003040350b4000303040e40d54a903620302d03000d642c07641c107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 315069307 1250 315068057 315068063
    0x70c0315061206020c07080715120e03030a0c050903010f02130605030f19060302062d1e0702030703021c0537020a08060106030e01111303020904080f0d09 68
    0x1541100031810031240a1402118120a80321290189541d0340901035001100d58210520400c480041c0c1540e04000e841d00038801036215110306810144000c02c01681d49800e91011402e000c0c0e41101d402001084951116080c10009000b0300100700458961103010003440c1c1c1582415664948002c4581c0202850224104480c841a50f10340040d0303940c4c0001c8a81e80c48801c00000059403514018480c03607100818601c00246054403030380011080c3d0090b52030044d800c1e0341c0e00040d4454003003080c3c2c003000e202c04021145080844d80d4190108808135000c2c100719103030340861214110344080100c6d601540e402401c07102c20908500d00d200c2004401e440c02e0340c0340c0c445c001809541d1342440038950841e084c1c940084881e451210090490a24019422070300302c500030100051b03400c803d20946010b01160703640410b03c05450103009003511448a03032500195810400c0d49881c005081408040b6541500c0303412147d501c1d0308103042c0f14000c440210f00d500c140051416290155507101041c0c0c030344 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 315070557 1250 315069307 315069323
    0xe010501060e0f030d020a030c060212040305180f0f2704050d02101109100c210207060504081b060c01060308030703141513020c0115060906050c0606010c0204020d02070c03 76
    0x10048041540e00d18520708407070096081f0321115404244501242d9490030300a000146c6030480e59040401d40020403a419800100d012401546990b06413a8501c40c944088817100340b070341440000591300c1c80c0400440e621031480401c0d19010080358105280c035000550904454030302c0d00d13050807034840215028038401801400f411000061b04c521030079a4102d04407002d541001d051100740540041107421300003d02410317516a80001780e01044134116014100c29a8090400811000e4541111134002c5414000240f10a006000002418441441961600400c03401880c804500c1ea481090301c816401d500340400401800301d03c400440c050b80c540d0f5410003145425035203080014805803402c6d600304054070469400c0703113046a0150007100110b4001450000000003042c216005240104003a0000202c100030301600001d054008100c2c44c10b1580c0342041c4030000d25110500209098180040c119100007552920350540b4810310061804640e141c510f4203164011401512044036011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 315071807 1250 315070557 315070579
    0x5160f0c1a0a02030405220c030b0a1502280203060702031206041802091902040f030c1203021e070302100509120102180114070b0106080f130309060806040e010501060e 74
    0x1196030701221003409541c1d000d5400c080c240420041001070303060805190f9004010301c80800c001610a103c0840c03856100081c611601030706020000c902c0e580103c0c0071072881c0c3c2c8044170342500030407081d8401810a000c0c1c01e011842c6100c404001d5040311002c2e406200311020003503e10380003c0105280c0190201c02c050720341c0c5403030402096420103400c000203084845110300050500c008510741001c2c43e20f01607150741551019180481e045a842620003d02568041040c0b051140441000d001085140400802c4948000c1d5070f4651070301601c0204800f0014a4003000c2e000e01c004005540d004054070750381c020392030004145030415040e00303104229092080000d098140308490848441021110180003100c00540d0118240c05d0300c020711903800c005510009030128800c0340a04815141c17940c1038101482e600c04c401ca0018074400130381c40b50344441004039820907441000c4034161712b0058010365600380840c002d881c1d184e08015480d800c000c008603800d900441c2022042c1302c241c644071042d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 315073057 1250 315071807 315071849
    0x20071a040503071e210201060e10090b030102030f06060a030603150504060c1716090515040323070b0f13091a0612011403070305030a03050708010902070c050105160f0c 74
    0x13281032003200030002500342000140c44a80e07004401426412030000007801c0740c1e9006051961042184d404051192802c0148000046481352901c000400e4008505601c4c18001c00c0c0d159039001b4110b180b240b2808203a5580540c8641c221901440e8443c007610f8200b2800d030301c1140138100c10b440c100c0c0e60318200312404121a1080b000d5407188601e1180c4101927031241c1415540200305410090100305046c0301c00300e890f445014513080d0102c000300c8080d82e964918184081c4030000458118446401103000281a02c40000c0b4030050741c0d180100c0e41c0d5512a605810641480b41020b1000b03070841585000a1404032544400d0220000a203800c000001d03070030801410b84502041c01290400400c014004542e031100f1001c1042006000c4903229500c80e100d40e80f454101440d000b0000b074548003001480c944c02541580108918681981814959620803020701c045004250400101040f86504692012980c00c41182c2014586030902c98a040014900705a4014407103400e11940202c0c000b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 315074307 1250 315073057 315073103
    0xc0b0c0606040b04091e0302160807031e060e011e020c06010909020307170c04150b090f01211a030c0108040f0206130608160320071a04050307 63
    0x68124980050310803592030324104001002c2e1034051641080d43c5034112400206291014002030709801036141d4181d1241c03400034039212800300301c00075502c0200c0d03007001024030001d281c80550307a104940025000b960001c1ca820541d189030054040c6091080d044140101035100d40d42440752540c0c0700c110300d44084100000da12900d29000c19540c4281d004000a140740c0d4000c84440b8802070903101c2d96a07440344c8072a03e500c2490382c280d005411521a103141032600384034040480170924034526409140c1b042000141c00307556886400785004802c9040d2584c46000145101b40f089000e64015080c180c2465004050f203a01ca250381c5403102c9950101c6150006003200d00d560305a5540c074030b81da07030741d62410801d208528007203801c02c200344030301501d503482000044050107856580d0f803614031745a01d00e00c603503c8884500b04180741c600100c200409003090030349400600c070340001c0c6aa03550b6614080c0080e500201c0340c0c440498441080c40100712000c001880b20b07034080c000c5c005062400c0307801400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 315075557 1250 315074307 315074317
    0x8070f05070b100506130807060816031d240f0906070c110d0f0b0a052a0702060706020909010b0408030901080601020a0204090b0a0e0c0307061b0c03030c0c0b 70
    0x218a003440180000341286025690090062140c88122a0f413034010070850340105440e0b18128000d0307070091040d03d0007088204010b00243c0382c0040113040c440420345a921100140004145d281c141040d46114500d4a041640000c07031700b02e80f2403144e00383c00d1003a2012288001320071020101b02040c02c00c610307a04001d0044d0700c003602074143c944500105882c410700c1c0e880100c9a07440300d2a035003c40c07507407007098042000740114500c840030304962400025a50004041c18600d03444e100130f004074800280701c0a01046401c1a101040c26040c0c1c0d0066003038091040004c2d80054002100800c20074207401503c00420182c0300010300d662100b45e491410700807401682902e620511114499603c03603401395070005018010f46000606a402060545400c2c04041d81c2e20021103050100442d21032003014a1502c1d440090103800300e80e400040e441c0c06c4035120b01020003102c116601d0501803000d07003c012550f4052400a480d80d56031601510314218410300b901d2084000900069180c0c40b40308981e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 315076807 1250 315075557 315075587
    0xf23100b0303070c050d0c231002010527030d09150606050403030e150c01140702060a0207020120011d07060909020c030a11010605030304081b030d020d080702160909030807 76
    0x82c3d041741000300b0302108200350030701519002414200060000000c0d00060194804041600800c0f22044188095200042004421603140c01c04110180981c16840c8203000168060303603040440c0c1d091468a10702400c141c2c03400c1d480c5420840e40c100108000c00c0030700307140420024014030366258420b6076240038074807014002c1401d07484690100e140500b1150500d08050a10506001030035610600b1035a0800d0030350084550744080c00071407501040f900e42c1c4101080d07410b600d080101d074002403014010100c0041081f2880343c62061030341c4290040400204130600010602c01820b00b5a03030744544601c41c50011942e5102c0201c0d031910070340200e40c614588400110f18100451400310344903120002d2001a0703542c1c0b54004901603809000070310051042e10000d105290a1340200c5400d1010310159520039402494601140b0303130041034840400609040501d0f455031060005e80c10400d40d82080c040b0b8040030003010951006590001441500a6a4484180d40d507028280c80c0791102180381c0c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 315078057 1250 315076807 315076823
    0x109060206010303050310090c11060c0c120c030c0109030f080106021204050f0114181507020a030816050607170907051e030a08040306022502010c0f23100b030307 72
    0x5001085c007800c01150022261030b10f80c000550b0740e0501400f00c40342a8050000102e14480203441004100000e58120411090360b91500c841c9035803059485810441e0350429030310100b6401e69145040c4244d4829480b07450003032011002a01e0300a1000e811744003203001051004d8008950b081c800640701c42054200a206032074035080c4410800465801c14241d4100480111003074000c00311072003d0a02c070500307522811800c4e00c5c0c4804012812044d0011403140c03035028480e04003d680d44052840442e500551259590481108504c0410b0703641003001d0f00071f1007150144811b10b64003105249180b6001030100c00b1a80380c0000352600e81195118503a84000c845500703440e00000590039981019000782112491041c0365a036105581103a4000d88000381d0101d0600c88003000c0d584400762880700641056000c9446034000703003074542c0041e0043d145a240d202c400c010072a4140103a00140f0540380080208500750354107035500d03680c900b400c903291070504011940c43e0070000103441403540e00442c070b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 315079307 1250 315078057 315078059
    0x803030915090309100923180415020307080402010311190809071a090a0509130b150301090b0601030e010612020409030504050d050307060506150706090201210b0f010906020601 78
    0x1880c0c81c2502400b001c0090004100820741036955407141440101c0d141c81d40315010f450402e541d102c24520b1080008a03c481312815000c658800180185001c0343e440001d40c40c0d165420034403410403101851088a602c00002d02c0300494008174000c2c0309034402d0303a00344914110303006d540a10307008000a800a191010b41c0701000c0501a0380d031103038400314510031100c000360b584c42116140442c2143c802480d1030300180c0711004d4148900320034054801030b81e001c1101d0404841e805807018403943d01400d080c00140c003080c100403907000e983c146110010000d010340b1242d8288542024400e4840382d0201e4a840d03014500003106014001c219006d130a840300c0190f501d5000c2c000a006004001c6081100401012849035105440790030206d0145008644524031361501e1300c1124030142c0711714410030350a80d083e85090740d00403c83d040c89611100c040b403140080c2c801a215120203010301c07106007141d0040c1c144080440c0d4082e07402d001048540d20010740b40075005581800060050400503000000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 315080557 1250 315079307 315079333
    0x9120e030303270106090501080d03020c03041215050903030604061a0f0c0c0418120201060e010618050301110c060c040608070f1416140606031c0201020702150a020708030309 77
    0x8500c441050000403c680f201501040d0300f15071171904100d28891f030350b1006029006041200c5d03503200e030050908626003c8851007044d507a0180d44074a0031a54011b0121904210b0768410b00b03419058444414002410020171030b64503030304200d41d0329002f40d10b0b0040000b80031720f84840700c81281c001e041c03da910302202d0783c003c000c0e43d81c004064411140b051b030722a200d41d9211846043c4c001d8110280f40c00c1031154078a4001101d1410320406011a81801760501185900c00b01050441d00241800600b90302f21000e14400340741d0f41d911481d419464034910380e110004100040c83c0d0700b04a201039030340c150303141d03400c0e225280924016180016060000511003d0058403803054041c0d00c1e04205074450000c003459100d43d40281a06a1a2070a0340500c1003040301100003144184456030240480c6e00c2d080020aa850030300018001c0c103181c81e1728040f643c5c40d000307504896002e50040d01c901110940321040040541c00070f09403000600c04c0c0d020000b100354020080d60300070b044c2c6602914200c24414 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 315081807 1250 315080557 315080581
    0x30105131203022a070e0a020c0c1c15020a02071d010b090607060906092d0611090d0812010b040e0a0207080c0d02060f011703220302030a030309120e030303 69
    0x1d80b11303130030000302002180005503000c464540d06050280090901900344490200404000707420700c401d0324018071801da001d40c0040b820211402e07094403400c0b400d092010030701c0300c4c0c14200d0030050701c0c1c03031304050703107070301c0c803203a950020480c1c012107070200d0300c2007030f5102020307121280800c19865142c0440703001270100c603c50900800841c4002014181416099125581114809181200c1e0150707298003210401c080014601031803821038240b22204103850000c20898141d4030300040000b41d030f50072410000034580c0155500250003404c01000803109180101907944405401600001e00000001300422001d045405070348030743c0c4d00030340305445100024010f500000b60407603e00c1f0083c811201a20070410503001c0c080d40c940c1c014a22410244000109500b043c1c0203507211414058280721540c0c0d0000888140f07001c1100000e80030381da250f4511074480000d4200a40c075002c0c5810340b034145607150304004c840c90700450003986410701609041c1d40e07002000d6803482d095002400054102c913006 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 315083057 1250 315081807 315081817
    0x1f03050c120a02060f040513022719290306010210020a0207180b12010c020a0f020f0d03020601080105010f0f06030504060b060415021c080f1b07030e03010513120302 73
    0xd0700c220365800015070300050b41500310000c03200c440072021408000c0c91810240965184040040443ca8036051000220034849012204d036896002c0c10200e042a0b1910542d10341c10114a41c10f0f103540079250000180010304420402d0f5504030340c1e001e10780c400801070080340c0c000e0005800601000700841407204c0690001418281035008041c80040c40c00c1c07400050316100c0b00e80d00e00001b80c1070400360070081201c0d41034290548076232400030f146034400c3e000241080300507003181121580b0142440020401d2a032252101d4004541903496020140c002881034140c0d5140710087c401c50f0b80795456003050040320301c282c902a16510404204150003940043c0c1c019014480220344480d0722004120940d2166020300303480c08164108a81c02136060045000c5854810a0401900346c0c0c00710081070013002400410a085007200847c913042c116031071320104800400d8070aa112112400d028020140c00c400540c081c1d402c001c000380e907840c01c040c060003010341d2101c101a890140380004600039080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 315084307 1250 315083057 315083089
    0x215040c0801050a020304050d14040b07080409020d020a110f031c0f050c09010306050603190509100905060f070c0c2607080f07050a081f0908121f03050c 68
    0xc080000c07400308800c0c059a4821030400c240036943e410185416071900d251994144100031a900360076880c0304444084908503031900b141c4580b21405802c040100c0d110380d90000300c0e903502c00181562603904940182c004c03207119848408010b075186003103646482c15801f00d418242c20400003005544091251882ea0110200e00000c2c01d9100e01a45811284283d40409411001243c480b81941e4540501000340c6401d844050460405d004895140340a4080290b12181c0703600004030780d01d104200407465503e412505100d9800c07103003000c036164407054625180040030b580014401c40e0080894101c09a8007030440d400c0a0f280c90384010204204603060040e0038042420340c06201000c00031540030307200740340203441c40400b0050313040c1c0740060342c2e800b4038060400ca0030300700400500421900801c0140324244e4403000c002c00c500a00420401e40000d08000c1d000c01c6c02a1510940400d0520598400340498100c2d00c0858841c0c0704154207100042880d0700c041410441420007640d44140091 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 315085557 1250 315084307 315084323
    0x190e010b1c0c080a06080d020a020607052505031b2107050a03030215011a0a0509060d0f05072a061e0509060901150312081807080d140406021504 64
    0x94241201000d48110410301c02c005840002840b80e8150a84100801072056400030400e24880c0800a034a507000c0c4030002e4824072000c582c8105003d01480080c00700c0a41030515000000c0c2419034444181c05401a64003910400750110b008002c2240520300c80da1004103110f002681680d85d081030441c818502000ca4060705000140c60b444011092001d18440d8000e8441e83d05488a021016041603104042c264001c05c0f08071040c011a808035000c0c10380500d45960740d18098000300c1c1d054810b18000181d40c602d841c2456410505a0340500d0007442a0754600384180040040e01ca13540300000b40c0020020303000b080001c0005d9440d030103181080c0131a600d0104946417800d68104850302150240c8a68109500704170b80100d0a200c3c1c030580807400c8510f03000f5281162585040b5a042000130401d00150002040d440440c80450592640e43d034800c0360500740d16150f01903214103001c01300001003080482d991100d1902c070010780b02520100e60051800000ea024441c90341d040160003559210 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 315086807 1250 315085557 315085597
    0x703090513060317071a060d03081e0709180606090909030c0203030d1b08040b010303050f070204060f0f06081302010509011709010c0e101e03021209060105190e010b 73
    0x82d5051020710104c2e401820303050b2034003100d00b40134240e010070b4003c4070f00700000e070070070440c0300c3d0b450445070b100e42505803030644019030300c10045491719051400a009440a400308001c80340d540000aa01a0f0b0420750942c544101c0106202c0241c8030103000b1180455403044051040d2400c95000308001400307441d08096034001070300864250f034420880c846401d0340b07030f00c0a406000c2e48905c80380c1509105107842d0b0020700d040e07168115410350601006013002000030311000d048010400350b0b000e0302c1d0003d004201c01d81ea10400c0e28000049031041c01a00c20201500061450180242c14444c100c03000307070710621a013150b004448680c41041ca59042c003007405c14503060302c1010102180314079041d42c000640900d584402400002c035034207403d03108000034010389034025845110f800201c1203040313080060380520b074401c0d0007074040c644443c66041d444004000c041d800004400e8100d40c001d40300c52010050100e0400341c171500b18014001c40e40024001001858100001049440d0742c0e020000c0c43c0c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 315088057 1250 315086807 315086813
    0xa03060b030c19021b01181809060e01060302130c200303100506030717150612160207120b1005040203011409060f1e0303040f0807060306090207030905130603 70
    0x26007003900c1e015030103a00030450b07150420340304440307032101d0100740014105003101c2101c0701051244c140700f031410000d264540c00b00822035401c3c1a8064004c0041501000482e01d1043c401444100300030740c0c8860034034404524042040c480c2000b07a80d0094140404503403043c0105000d131440c00040010806100049040609400801c480380040d48002d1952800c0407048080e1a0b25550081c5105980030814003d6140c3c01000004141070543d011904c140c5d50480d11042d445084a0340c07079085400000d140e602c05920100081c800c51038510400001c0138191000c0b80e031070a00e805004026802480408041802d241555500007464000e04d040c06484030007140503600207900c410400341c8422010b442c5440d0030003060754001c81c2900c46604007041800000c80710841c0b40d00c03044042108221a02c0b1684051089034054804810703c010410760b254001c81d60354000e4410140060728205000c25081e5860007103511298160350b82c00815400c0c081001955009045505007213a0340b18000000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 315089307 1250 315088057 315088079
    0x3090c060f040f0803030c0403110d020301020c0703030801080303010608182803021005040203030d3603111b0105031305070828020a0b07150e0604061406150a0306 72
    0xd2090800c00c0d988039464088103030f5004645030410440d40c0c205004100100d402d92045e00c2c101c941090f002405140030901007200c4a1340c00c040030790103500008080c98110000144802180d109a8403017415030f0360b0f0100c4940302c1c0002e008400004001c8000702388034040030500b215124084500707864500d0112102014500a0031580b0513006c02501c1e5a8404d0540500c400f031442c130501001404a8900340d0300194480c032807903c01804066490b050380c0c1c00020001e090002c089500d4003550102d05500810010a02c1d02e24821800120881114009410045145201401d910705a0420318107640300540f01a00001d1241c03071085280c000c0803011407400c0040714002c03d400005014a20516684c40501c4180000c002c8101080d800048006031130b280d107040210303408180a107071160464a042d45509902031029005541000c55030304103c0c4010405501032442028100540709400380440300c80d202c00c591a41d0b009034801c444281e50406440100048241c510300024030079141c0c0d00080d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 315090557 1250 315089307 315089317
    0x3020c12030910110a02150a0902090f011a1602040506120a11190f0b0307030905030c0705030606010e09040f06060f0b0415030b0607060b040f0c02010c030b0a180203090c06 76
    0x1c0b154400742c640440510a031040d02c041400c3d40c0052841d0000e40800650303a004600302c40c81d07076080c0740d500181c0c4460f56030b48801007080d401818803c0c03074200303c04101103ca80c20f010707924a400101403002012403c0608031408a21400624003070399156400704001040002d019580118480c0c1c8104813815040c040003c80303038801c1c2c0c48140e419040f20140084061508105412100b46503000d03ca403280d01190711f000c03240d24181315a50f035625030370110054020301c1c50082481c84049400481054041410400e94600750111501b550ba00c40044509154060440f600410b400000c0360115440008052140340510004103215030b4614030b2002446450f400424920001310b001c0c403000200301c800d408824510300d010302007941c01e00d0004003103104000004003042d030344080d01c06603515542c008039113142d020003080008111130103001c3d010b003034a00f80c0030002038682001c503683d520300300c0405801e0300c0701b40c80c2d601c174031000c0007070903000a52001d4642000784c4a24810802e040d075034940189 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 315091807 1250 315090557 315090571
    0x50a09060608040b13060c2d210b03030f030a11030c03010b0703031e150803040311090a0e03040608061c0803070c0c050d08040302030706140906072405100608090d03020c1203 77
    0x1104d000323204241c0010803060302800e4441401e180c0d06814035540461350000e0712001951203c01c0007510b01c007200c002e2860300d00b8190980000314003040c9411160020b51300c61000c08606203c51006aa40c4020a01c802c803440c1c050403134140014440c0e0481c01010b00b80440c441d0600044564051035220300c929603002141d4895030311f402c2c4501401e120100701900038036480c00150300381781c1181c1d10209141803914840340542e08200018080c014143c001035140400c842c1529aa1621004000d014030400c45000e40940c0584112214114240b080c1c04411a00141110306680740e040084540c0341c00000b0aa8615001d044081441c1d521422045101d62240d040c1c80d07a030307500d0351050600f4002c8941c007000c107210807100d01e031212100110032240000e0f0704440c1513075100700700d2804021411810710280e1180700251a105407103407207a44110301650002c0c09844131103a07180300840e0b100740115400100350300980214401a400398003d016558451019100348003603403210344102ea00111405 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 315093057 1250 315091807 315091817
    0x3051b01052107031a0916180306020a0806030a150209010903050102040f17150610091701050106110109200609121006060e060306090901060906030606050a09060608040b13060c 78
    0x200040c0e580500c1034655180c5440442e9017034000000024011170002442844d2002c08031222050542c0700b64084ca03038258a185000d00c0c10b6803070b410f10380005d4002c42040804155081c021908500d030010b0303440303499580014210b060701403000e4400083c1d0025664a030600c08280c102000060382030003d0805002d12142e007c20840c60100325000d80c141d418086007454104c64805a400c81000900f05d40c040802ea03840002924020000c9498007450b5000748980c8418100c0c0b0081c181d4103400090481e240795442181000c071110041d400c0b03400c441401028a0030551441f84d042c8000c0c0e0401c80c0a03140240340e44d04120900d004513002c012010084903658010319505503502115114000c007030503862034443c451001c100003141c914800501114824181c0b03000082d80540c094120402800b030701030042c000290340c0d00d030680203004103000e9103104292030714000c10b041e2128440c14003101c1c100d0303898034500d440b552909400b001002c0d000c00c1001914807800c02c082070040c010403201c020310750b5403 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 315094307 1250 315093057 315093061
    0x60438040b010f08061b0708030702210c150a11030702060a11090f01180f12030207080625180311040509060702100b0414010b0307170103051b010521 66
    0x2040004405811070446842d0fa20b009000c1c40c0c8000402d203174003880101c2c505211180c0c914505599000300700004060311400000c111019902003960f50040496040d444025080001030603443d0043d42c0a80019034080c10b401d40f011642030302002c2d0008048003000030044c906141c480c11650048414402680c0000c0a2120003401031158121a08c1020005420f0082840004110303061212000b4100400301401480000d0400c0dc500c00a020b8031a82c0d4850310b50f910101d1aa40008000070360150254070300002c5d4100b400701c0d80b02d102e0160140114031500702c1b140000d4801c4070140c8030004000c172580c0d4656450040c40c0c101005140104007042d019401030b4100030603a9001459a61282c000030140040c007a00003038042c0361601d80702408240ba01c400c40126004140003e41420740342404400010741c0002d81000718000c280b95034800b04030420b1914080c1d400107081c07200914036407113102c1140100d051342003c403007000d00500d086498440d22442d41400e407540030b81136440e000d00d1801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 315095557 1250 315094307 315094313
    0x200c0102040e0109090c06200609010b040b1806010507080c030a052503170604140a0b180f24030615031006060e0411041502060601180806043804 64
    0x2502c0c41c0140750311101404184815074500f00e01202c280300d540140314210340740d803040c880a00d50800700c144900e8200d428516107060082c1c0070304849000d440c01240342080071034a905029407a0403100c59845c08100d02510b030300004482940c0200010b440042c82401648031080c4144000c11070080c450761210b444201103072100080281080041c10300240c00c940600019800100c10645c20540c5441d0002d0303555404081000303802607010b005506456a4100480107a487e44001084002030720f400c4034004240112181d084d0080e1120b003d0f000d09180001c07881c41c212070000c10b4464600c09070141d44000440800c1c41c0080540b10341800700b481b40c0103150307182400c1101c9443c03803160701d005204180c94600098101c4d80000f00f8180035507203880324200069040c100305c4000380500d10300005418010342d0000d40b69001996020b000482d805502e03c0c2c404c031240b10307032010b883c400406448144c030380340c0d240182d0307007003510420203000540544030842801c440f0100c101790300c403142c400c1c0d4245440e01d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 315096807 1250 315095557 315095579
    0x4030f03022a04050a020d02070803041407030209011215050903030712110d0e2e14011d090f0f0a0311070803040e0c0906030a020c0d020a0510200c010204 68
    0x80c4001c9402c1e440c0c8030090495410101d4041502c8015680011305880d01208413019201e031030310400c0d42c140001685420403e00720019803086028002a6041c8203001e000681c51f0005131001070350100c09040180090040303644000d50840c0b0500d040802001d2112380501503d200b1106013415800100402001c40e40000c04801f03031801c00442001007030400c111a443c90700540880c4103949994511800c2c0c40c03c0d04000c501c086204001c54095540e590380e04840341c480c813a001c1050311a0510300c5810104081101d118180d4040c2001da4101041c01d038040086006c3c01001c021003403060120741c2c0685442032006200c4070000c0ca002e0040c0940500b070252407115030542032156079101c08810415a800402640c099600c8404c0b12407250f100c0e090101880d0042030401c6500407000401c0c000c1c4216168010041c105c04a41a9402d00115003020780c1c030740d90541c2025049400440e40f100d0140302c0303680200303170124a04031900c80c071001013890400744e500003014455461790300003000c2c004811a1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 315098057 1250 315096807 315096823
    0xe070509041a1c0f0b090d120510090905030d0e030327031605100c030f110702090f09030d0f09060e030301060923060c280b0c07080f04030f0302 64
    0x19000c03801030944004042501d802c0064003d1880c4a07103144000c04200e02d6110701c060781500300d04000d01c5410a5010240c4420400a800c0c0205500c3c0b50f5440ba0500c07140036941c85102166107150640746000321000c05041e0410b401c8486000030071420704400c00302d01c1400240b02e4900c000310740b01c0c58103a1040803010000e1004000c3d011020302c42c6240c11100104644409103010901031019019103012883e0041d08004144038a040807a08100036a05610102552100c00800e0206c2240d0301d2400314280f081c81c10180d040f8142d0380000d00c42c08181d0190980000b202d00450f8a4406a0340c1500e040b10402c2038801000c0c0d444030262000d1014a004100708908240c01071440e6501d044000740807035080340310781e1441614000400324025249010042801c0d009043c1c25903800130340b8070385074444481004e642d000c0a201e0b109420382000c400c582c0d00c8000d50040180d0010303154101810b19981000f03c0807600800704022228001d001500600004c43c401c43c200403070003106280290070040300d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 315099307 1250 315098057 315098081
    0x3130c0b07051f1e11040321080a0c020d0e032a04060b0a1704020103090b040605100603020a0507110d290604020f0d0915050108071403030c03091003060e07050904 72
    0x400090300d500001482c1c0c00a901520010f00040b013009182a00c03c1781d00880d400905400348030981c0c131240d44012210200700c211a552203c01035034034101d01004a4541c0090900160302c40c080110360207000702400101c041004080f500f114024580b808000100411a0000c0c01d8030a1200710761070406004010151030610302450500f503141100401c81468848290750010440d000300e425a4040d6200c0092141c001c03804000514003030500d6406408151200401d8014145001510a2081c8282c0f10300240030b503903c900d08000c0b40c64000f0718042800215500915011030b040c0000c54070103c401d02034400308020040240b6800e142c82c0091001003000d801103004202e00100074402c14110345a54026000000f40d2000c60306006c2a0711425800100d44a440c0800228140800107110740485041c0310600c2c0c90542200141501ea001e07070104a042d0354014880b40d003242c54284841030a103801440d000842c59901c01510214440c1681d245001c2407000601300590b0602e8000c000c65021 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 315100557 1250 315099307 315099311
    0x80d030f111e07060603080c0c030f031b010b03010c0e09010b0721020a020405070206010503070506040b041403100204030615061704021e0a24020a0803130c0b07051f 73
    0x5010000240140b0805071150340082d00240511545079100e001d540403140c00c1101042410340342c1c80c01c01032944c0008807030315062041c0d5110054038900000d2001c8000c4007400a107083c0303210b44050f03c03112240c00d00800da0ba5500c451842d005510248502c03a10410140c1d1403000150300541407000842068200c0700c1219400c108a07004101d07541200711042c459020080082001210100d080140e82c1200a505c01e0a200910200350360000b03000b81a10012420303960300c1c40d42c0703108000c0a4482c038480c08401410600042100d0300c2c8005001e545580c015007038030f82036181c444141c1c0807680a6042280d03125554250010000d036401c0b0000c2c09801c03d410003a9414000c05031952070715000800080c4a01c480e813074095100000300010b400706034009000e640300262100e0040c2030000643c204010801c055244000600c2c0c030004000000b240c0020001c0d1a540320310780c15800640010205480c0140c09440018440d840b150041c5942d03402900500310103030780d000a040240266040c5d102646e4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 315101807 1250 315100557 315100571
    0x150d120315210c350c010206040602070311031314060301030f1b1d0a0506090c030703050c120717010b091302132402010506030d09030b1807080d030f 66
    0x1450301d00030503661034500c011000c05220b1440c00c020141040c0d0045a90728042018981d9007030501d0316032400640c11010382c405542103400e00903503070380c088029540c01680034401090110f60785074001c18100340a850410010700388030302e1140c5035922a485224003020501802c0010b003051540c0d0a620480442d1103a24552541e02c40030700a041c0c020b0003074855183c4a00340310052801400c02d4004000480300c0d000b411002c1c0c2030b01c410024040354100c01840c104400200302d40703000000b40d44100d0b21812064116280c2e440d045004101c010861945501c080081d845050720510000d481100746070345880008215035102d011943d01a0702c182000780b0305100300000b42e626541c06a51440100a0040e01c41e003d03c034440b001c0310354542c1f002d0503404901d148001c010244800c03004000d811034000f409280c5600042c1591410310b01c6140002030000385e01400082c0000c407060f03412600410400540f01d40222415051210a030700400550340000f03540c810b401c0d094003403c1003010414400700080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 315103057 1250 315101807 315101819
    0x2030d0509070e040201121b05040503011803300f0203090c030a05071703070f0f02151303110112140115020a0c050f1219021206130605150d120315 65
    0x3e240240c002418400004040d03110310b01a41e000175090400c005660141d0a0340c1c0e0805096a40a40202c274020750034010707c03041403400509080f0281c0e506554400701c0000070382c07084006000000200100003140182542c42a02d940101c0c184c00400070030042c0d481c2801c003500c9141c4500643c01c140280c02c02d0802c0d4001c500049040d004545880081e1340c40845000d0319241148103002c002000d06032071705c105205007c096203048510358400d07107131000c0810b03250054400a0160300f80c0c01102892104040c400504000440704c1021010304001c9040c005c107040c1501519016084c00d80104080801000700101260442c40d1082081c00540001102500c0c1e44a59081d0307401400d024a14100c0c41000c00d0b2156400456641192000d40e01103a900340f1145900c601d1010040c0e101e44500b249074403108401154160085001c4842e00070051000c0d03441b000038041c014441207000030302040780e05494072058456092644181108140c40c000403001034115080302d07070319103805000307807405101c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 315104307 1250 315103057 315103079
    0x2010f113901020d030209180921070f06020724051b0906161b0f05271515070804051e0120030f0406020f0705031b0d0c0e0702030d050907 61
    0x41034105103005647c07080072102140446184545058400070030004002c5005000716003080440440d0000c200443d2103035a140540c2c1c040c03500090b0610500030444000103240e41c0c01030024504c55030744104c03441028007240351000c440e944034004481d2200c0030072807488029041d0007078040702010700c0c5090040c4107000c505540549181120340b0072104100f44203101a0504501080815041d02e84d0140c0d268082012560f05602c54140607400325603030110302074410604058095501d40309030480c1c2ea201000124008100550241c00490b104440044409548014441c45000f800e07100c2d030f034501d44410300c4480c07448000c031101914401c0c4002c10580c4e07400601d5119070b01180c10303a41080f0001546160440c46096146c0903168000280000c1d01c03170700846c481220340f14520584000311741e0b0700217144d11400580b40456110082d8104602c081c81e1801d41d401000d8007400180c01c1d604d45407120040296020740b2a90f0140e440898a0011600315000e90740d404500c5030090600180f0300204022 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 315105557 1250 315104307 315104323
    0x7091107020d0206040503010921020601030b0703020a03090804062102030906070507170409050402190e0a0c0e1503042102070e15090f01050a0602011802010f11390102 74
    0x1100304032440c41c1d4815980c0340805c3d6400340100a008105802040c5040030034182200c0c81001600b03c03100e8205401800850aa070489400000c014900c1d583c1e10022070096101044440516a44002e00c002207409000604082d08241d124414030015000c5000520025007805891103801042040300404c1c005c01d8060f0010440d00340f0607141c10180c540900c0c480c0200442500c2e451012500054100d402c1d040030340107900070f5980e00c0c0304000082502080703503400d014445039601c110b004917291700c0310780c0c3c4818000078052901c240100525400545451000510b0032280b41003c0144401c1c040b0740f405000602d107581b081000401456900030b900c0e0300c1306210f071540b480b480344006103100c80b05010b800244040181030f10349a02d4442c1041031a440280640ca0140c0258600410214014410069024021404649000c204e0b82c011a608041095500c081040d180080c808102c41000300c448010701c6503205542c00c5070807110410401e00384148002d050780d80010440c03090398021503c40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 315106807 1250 315105557 315105559
    0x603090a0b041a0c07021018170a0c0305010501140102150601050a170405010c1803051c03060b040803071b0506071b051809100c08072106170709110702 67
    0x10503240d41d00e040500443c05402001100418103030700300012424030100411080d071085942c031050b040000303401c446040c20f2650007003003540001c0c030a0013090401c1c44180801800442103030138140b400e41e114420302e4480c0e441111217139110401808604008a1180c010007428801011450102420049903107000ba00d2981800380c00900c00142c0c1d4820700043c5c10842034030409034601c1c18140742160007044d20040640029aa0812075100080001900001c484e0000c00400c401e0800340d8400c5101c1703290219000a06940b102c3c0014003407a003102605c0181036120103183c4075004d908240d8131140204107058001c550020081c03100e42d90b080282c40b01e194000c41c0030030444600140c14888404580c0205510000350b03078800810b40301c010750701807058080c00141e03580c9040829094054170800d00c03603c800b04494a000580a038403881031821600c0301a0214400b01c0078240070302084559507006a031300030220f0381d003000382a44104601402000480401c202034240f030607449000e801003080013 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 315107913 1106 315106807 315106823
    0x20c03060c0f0406030e0a0519050f1203010608180613020a0902030106090e0405150403080103032705060c0a1a090f0d0807030f18050106140603090a 66
    0x91102c1d4000c0e40c2d01e85003001d04010064014208030680c000d518410310a14401090080180c040c9003485040c403041183e45900703200d42840f47c1441d2801482d40023006140300e40d001601100e0454555181020154490461040c404cbc440060b8011003441034105021084821207000450544211194403600341c0e0307026140143d010034403d1001180c0c907590700700440d01c00b00030382e581e0161241040c0c1382090b844454000e00b140d001e841c05c1c1d0025076007000620030035402000a10001c500c61040d42d4101e4402000e900508a0500410740990710118542041d50340c100715001d842584080c41c20f0240c55406052001d03040121541070365849108080001c0e594003103500400f411156072080e41c2c0317a0b01c4c0032055001c0c00e0302c540100c50840da2840b40e4a48100b0700c0040034401d900c80c0c0004115646461460511401d032140c2c042c0c8100b01c1041849242c1c140082e9118500d41d2201807 = true := by decide +kernel

theorem cover : BRFrame.Cov 314928057 315107913 := by
  have h0 := BRFrame.cov_init 314928057
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 314928057 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 314928057 ≤ n) (h2 : n < 315107913) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
