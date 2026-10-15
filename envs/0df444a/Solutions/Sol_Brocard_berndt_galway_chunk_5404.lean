-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5404
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:45:49.251787+00:00
-- url     : https://prove2.me/submissions/b1f9cfad-d137-45ae-97cf-53806a0fbfd4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 971762589 ≤ n < 971942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 971763839 1250 971762589 971762591
    0x1501020f03090f120102090d0605060a06020105011a0c2b0305092d0a1410060503120a0302090112090501140c0915031503061003020102100c020d08040c08010204030c18 74
    0x601c2110001d00706100c4443c0d058040d98510b90b0030007840000b503040310101d800040440a07051110300d03120001c0c2100301e82c85070161500c01310026500b4014005c05040e0703600141025100b081040f91100990080202082c140c400d06148400292078040001c8014442d061480104131076004050b054440c05802500280d1143d46c1030141c03000c10790b00364003601d8086e82d0142481c1d6140c1c1c0300d0520384050700c40003501400c10101b41005c540b40009501882e100f0360a000e1107016510010503450310075051021100030000c1240d041d00e40e11035401090b440c0b105040550000e07141442003c11104100400c8819070354071500c2c505d0498024284075480104407044500c0c20b030740c60000c42c460302c24407900c9200c00300010022a021282c0741c00e1700c0c1030105015044403098540624404602c0c800c0d8801a4058014604030f01c4203e601801400344140d01d9400404414600c041c041703034103400c01801510003010155010444238000c1c0020401180a03100540801b414000500b6008004000800c181b03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 971765089 1250 971763839 971763847
    0xf0605120c040e070f030609060b03060a0909080a030b030118141c0f110124061d0625050709020a030e0138130203070f0806090c211501020f03 63
    0x342c40c50001e4213602c2006071a185003911551581035001d08915004940e50394200303440418000b10302400745104460440304043d000f550b80509008a40600001600000d001c002d200341c024040d810220860308081d0000a101d4086038522081d1200b030f400c2101d003030409080c034043c203140c10818201008001000d0000b4040030841c0a0301c0a514030550400b4081c04000d81e03031070b040f0294468607011155403140601510001002c029230345260040d5004079100c16032007662a040c00041c400103800103081c0918154501c1e0744003d015203030080701e00c400350380301080100041081c00035100030b02e000040940c81e1460441c026068515246541e44280c0c03420751f00c452080d03400051007003001e01d140c0d80c1040f00050f5003046078110500c000d80c04d4003c21140076442c410300300c0f90300075440780c15036640342e41148403640741c1140e2070b2601f61045640301200e1004908200a01c800500c5c40c0c1c031801d0740c103480c4141d50440342c900301c01003110011100404410711105658040c000010f681e03107100d01842c94 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 971766339 1250 971765089 971765099
    0x60b04262e140c0904110904020a0504030519020609091909080c12070b150102030c010e06040303141003030503181006060f050c071229061f08041b0f0605120c04 71
    0x780c099840421311564640e41e03000802c6c07240a00711420480054002d542e10300700c00001034840d91041c84119030300e2003248540700071445c0030384a900580b58003d0802d4501000c4004014040d900501000080381081107203041d40425841500d4a00d84500390807900c0300040d02005040841001e0307020221501044040700007540c040c01c4036842a00302c01c9040c51880f0b8040102d10318061000080102c0d860007103410b5881c207001509034416442580e0501c02e07456560700c02c0d400f458003a18a00c8480c8940302040c40047c1c040c0000d95484400c1ca49011003c100c0d0000980c03506424450800703071242c0d2032005222155000d42c4003c810692424564a0100300d441c80c242d55002900c0b03051031814843c825807042140c50300400c15048aa800700454002d01c5820302d6103003d905580d124072403004038800d07035032004080e03085c9102c1e48001e444811540c0e0343c1d5210416070b41c800c002e500e8a4103042c5080400d40603410500d10b000703806a03640703842d11004140800400140f018280900006081c041081 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 971767589 1250 971766339 971766361
    0xf031b04090c12111e070507030c03081e19030b0f0a030809040e150103060c0909060602030c3d06120308010e0a0b09010311040905010e030706060b04262e14 69
    0x107101803540002e2076580c9041c7c10058140702d13240e04000c02c0c0d08843e52002050042c144082c001660601084404000c0d514802c0c10380d500c01c0300c140701c1c40342c140c4000201e02103000794440145002c02401c4460020f6004002644a090680089849c0c010205504000f0706152146500e09000301d4010300c41c220710003251003104081484010246500d4050a080c080d1241c0000c0d0300805065109004503521000d02035200d401403400f0013000c0c4a10001c0e5040c41005860310341074a8600c0c0401c001c1200c04100501c5814284461401140d441d80000604201a48146154a40690f4481640f54100741940c00c26040280c00000798600b4440204d5003540d5860400e41100c3c1e011a4611040c0b05080c04103010700103101d40a004c9500e000f204100d5004048010016244556010040c194660b00c0a903400d016a020b036174540b41c98110300348a0b108003004404400c442c0c00c8200c403000c2450040c642c0040504205200042c10080d5540c3c1c1c40b0040d1b402603480c0d44103640c20041440c603054042003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 971768839 1250 971767589 971767627
    0x1006050a170307020d1202010b0f06040b0f071b32010309030e0a080f0c040203010b04052707020309091302090705030703180506100b0f031b04090c1211 67
    0x1012140d882903092203400420801c40c0c8100c1d1380a01070030754840150401203541c02561078004055401c00c2c03503601d20303480c101c1c40c0035007040b03002400542004d00b031100012071504000382d047d88134582000088080b412051040c007000100301c01a0402900345003241c504000d0300130f00403040c8800b812a82c003003c501551040d510750000c0c60001a0020a81021182c0c00b50030701d41c0076041040400d01040c01280030814050002c2e892048604500142083c84200c0c80f09100700b81c4500d10a2000340200e1411007070f1111a0004074002103100c02c03809042c0500c1304070030ba0342500541c1c0b00190503031241c01c00001c1d496012600e2451151486640c0d0042000a440109280100b0100000041409000394041c2d581d0714698400120910f90500d0426a0380704152040303400031009900c0052400722660407035214144045000d03040d0b480f030f801c030301000c2102a55112244002800b01040c0c4294510a01111105940d601c0c255400401d810504441c456500005400c0701000301c0450318081001d55 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 971770089 1250 971768839 971768849
    0x3051b093102131b0e010206060d29070f03091a040303020f0a0c11190b0a121b1206050607081e0403050a060e0d0f052a0a051006050a 59
    0x1600806625801c0c00c080c20010380340080d4825503008030781c000c90b40d80e44e200182004d0065410380c2c40c0030a445003075484a0740d01c80f280e40140c0c460030000e003d60504031610a0101d1007404030804680d1403c1e242107541c0c104540383c0e45c00d00d40110400c040603901150f1201d0707400440c01c2c10064126107072960f82d800541842c6103812400d03a40c001c141054801c4c0d049480741030008502d035856200c42c1000a1072101c40e20029070380d12000044000311031814400100c6c054980e40c4001211910b8a07210b4101740c1c100030740000600040d0744c104101c90499000d5001c00d11611421503078000000300000c3d148e2559490030424851130070303030180880d441e03100454885941150f00705071142440020740c00c04a118481c40c41c408a80800d00000f080800140105182d21400090185a242c0304c44e45aa0301c070542c0180002510030400b540595010781c1c000c100d00d81c48545d0300d2222290384040d608040c0c480d42da840c519036011400c103109014041c044842c460700c1e442018450301c0d251000240c190b034075074011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 971771339 1250 971770089 971770141
    0xf130f060b0a0b0406022d0726030a09080f120306010e040b03011a09090f100c02010e01060e09010e032701050d0906090209150d150b0a03051b09 64
    0x3104003582c0396000702c8001c20074440401c1e907441c1c65038802500c80c91490040c070102a80b420b12070600d10407890050741440e000c00000c1181d81c2c981003010349010b00021008540c80c0c034100307180c03902c00d60504c010095140c0e5915104461031401041d07910300342c0070540d248541d0300080c020125400c2102c0c02c4a80114003440c00c0035010604400040003040390444165141d032900c3c80492420000115080c013941048603003041c03594070415019240d40c2c00020420711501b000b500401411301c1940035003090203080c400010145151503207142100c1c203507040818041300303010400410b031501340103204400f11108050f5003080103210000c0c40325808c401c00401304031501004c0d12807591064040d0303090026141018041e6002e10305040004001c4140281d01910045000034600b0002c0c0d02c40c00e2030224040c1190344c0001d01921500802062401e000c0d1440303441d407020540c540e0310000c00c031000c0e5018002628405011006007518020019002070003404d80b90704000c0c560204d21321400e403115510b20 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 971772589 1250 971771339 971771351
    0x615010f020f1606020f070f18020d020703081f0e06060c010e06131a0609040221031c0c0e181f090b040e06100302060706090501140f130f06 62
    0x80c00764141111844400a14490004102d018980c10024181154555025a0138000c0b02e41c1160344c075000203018a0080e8441003d080080918014001320b40700000a00142400342103807600e01642d02003603054001640e0b04c0103000740e1132991049802e08152031030145400c2450705410b10b001c03030780062a59110300000315030036603211029044502e40d03040000960b1140d191004141c40394071500c50041d6200c200100d0400008003010000074020080101a4041c41c1c0c1d440e801c000f4081c0c00031a0080c40f0140303229034a80d40d80000c1000e04000c1c555514546c40704002440f2031011180506410342c204841d0044c40503494650410a150744021441855642e0f99020b080050b40c003000c16030305029681903000010014140e42c040f03900346038100d07070074803141a070001da042d42d503881590f00c0c4541401c090020801458204000d01c6064860040800d900c02d003070700c0f1142140c001a0390011500140c0741084244040785c00e40c0303544180540301840703a20712a0f03104d05010847c2180e0007014540e03520 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 971773839 1250 971772589 971772617
    0x503100504170307020a0b06060f030c031003080c010903030f02120402060705012d05161224030b09070609060c15090210020102130b031902220305070302010e0102061501 75
    0x80710b2840c4218107080040e66800d160340025606d0003c0c04099500840d150041203241c0b50607002c41d510110034117503090035902c403140c9015040d031000d0030030f11074110301c034500000040154010382203080f4184000a8040624140a010b4440c04038210840c00d03c10042100c4003100c290138103411640542e100e548846451602c0c074018081c0b9a000c1010307034184808860301400e00c00816911004036107040c081500d80c00c3d4000d0303201300100ca42d17102241941c000380610488952040c41407254222450310344140345400e451503100107400c01e403814040b200c20071030824420440c7c90014079007440c1c10030802d4901400180100f18441c801000901da80008241f80000f80c0c00c0080401d4008140c64a24003149030081c0c001d50064182ca41ca801c510040015011602e20a40307108545040601071304106007204803000754448001c620a260f4100789007203540c110428107001075440348001b006e0440c11070002619034040600c0c15070465100d0002c1242c4600344442c0c01e00140303428203001c5180c481e40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 971775089 1250 971773839 971773853
    0x50912070b16090e090c1203090a2702040906060f0c0c050d060f140711012a110609010903170c090f030f0d0306030b100609032d050a020112060503100504 68
    0x250f04c030a000e10b078a14207011542c1c0010840354640c840481d10000882d0103500e0068890007000c495940c000c1810070108101c01c00100b40d0070032810311241e8030881007011607810041b40c106030482c0c695281c0e180014446039800141c040e40d00c506030300b0030090744103096035041d0b1416611f00400b030003038801405a004000c02500074800c04c1c00d42d07000034060146401f040b810b2451049845000080c1c60f51207610640c10103100d200700220190f400217140f0105209030f10304000c002c02c0d0701c004120698000602e89102803180034010703400302c0e00200e04030b00e1900700248010f0a404400185890000074000c00b680c210040310407450055602194501ca481c0020b0304100c503a9000d9141405154040000d80b507042d404030082d644188a400020745400314054940342c068007600c030206500400038000300b648400c0481240b000b190080018081115000c40d0181c407059007150141e0040c80140d0441d81c000800b0040e4044680302080114a010000384d600c80000304840e500300c1da1000464280181 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 971776339 1250 971775089 971775107
    0x90807020a0b0915030907090b030a050105192306120a060c0e09090a020f062b0c110109120f020a06090b040c0b090307090b031f050912070b16 63
    0x14480103260382d6940b10000d441d8000c08280e48201d50070301207641d08800307000549008907a204001c020301400c0042c54001070a56050460340f5114403605000003074024060244070702070305500c801a0406090758902968500300e48036101e150b180031a10359003000d5805403517002c0402c4071210056403844940900f8030380018000780a042c00c101c0c082241a820000144020400362058900790b40c412040980f54a032001000b54883c001505196407841c0130006040c8808140260b604115107102d84004805c2402c0745020343d4a4a461402c04203d03007004400d103402c090000240309801003a5130760f2021203d059034140620604e03511804a2a208200000f800c5070300400c10005006503091043e10042d00b1141140c14404440000c5120030208003074a0081c080030b0024083d190030414400050440c02c0c0c0410380610840c1485001903ca082c1008030606034094002098149604001c0c10201c40c20302c2c0c0e0104000c1000034800140710340109940c40000b800e54031088221180c03048801e450 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 971777589 1250 971776339 971776343
    0x3170105093c060118050d0b09070e0702010f0b09091024080f010608150c0906070b07030e012f030a2c2803080601050d0903270b030109090807 63
    0x14031541c001065240c00344002e07014034400d80702c88900060250082c00e04400b203004007a00109021881d50009141d6000c480c0c0000240042d02ca07120f031110b07080040300c403013180d050300180c1d101c141c1c03035489940e42d01c0b8a51005034140d803074800c1460000051541e98002d642e10000c0c0b140d46912103500310320520310080190303044802c810409aa00e150503551441a0428004194030b0b01400240854000400f0307004d084850076000d00540c1c80302002007080d080144050380000e02004041d00045240c1d040b13912480711924000b55200a07201c440e4211240c05900301c0308041c0b50200c00fa0241c00c03d071134045034008510840d03552039a854034854007601c180306944803101511010324410100d401c0c0d010a0645105044a81a10040f208543c1180a8107a41083c100341c100c079810110744a4154144c2c011410b0500354941100118140304a0321030301c1090300085c00c2100c0403c01c0c1640b0340041d003040101c41451030759290030710740c820039140300c1845010300c8150780ba04560100704201c0f0588801039 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 971778839 1250 971777589 971777671
    0xd140403300603030203040504140106140a02100203130501050105030106061713120c17030c0d0203070207030c0f08150603030a180e0109020a0f0f05180402070c0b070317010509 78
    0x60743c0385006580c17900700d401100d210714142800c091000241c441c4d0a412200f2a030354244000280750250b40e02a400201200114002d5001c010500c0c030341d50008500030b4124009040300e0100900700503084a2047e00054402e0341800c8003004450382c41036402410b1800700a0144c06601d0340c201200780c071800d40100030706121003900000c05450300700340782c0000e003401803c03036207200102c01c0021840703480110b0750000142c10a20100901d6020b50303010b154040c04600494070380503201e80325441180b80e544c5c40038441c0d142d00e00007032040309410b111078a40e60585140881031402e020b40006d40300e015101c4040100900c151880d2044a41310510a0007401510341112441d41c5440626010f5400701c206800400c1541140100c2180301d265a820402c032550b5410342000e0108001c140511030f88800c855005800344203c00c089078440c0644d0300240018200c86030b680342c883c0b0b00070b023242c204200000d1035a00000d00421594440041e03c560003184d800c0c0c420818001288002d0742541e081507041040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 971780089 1250 971778839 971778851
    0x80c21070e0108010e1b0c01020c0f0f0106080a1e030c06110d05071106420102070b0712030b0d0b070905031c022a090703020d14040330 60
    0x2094000c500086503110030380c0c0c0c03685180e8880340c8103801d0910907594000f1b0740b401030842d28070032001c11016021000300e50001500c0d181410440c64a800c40105441e0400e400070710b00030000e02070902c109030003881c402002d403d802149131100118180740039091307e00600c0c030200b00c404240c41032080880160740110108130000508200c40702940100114a160030300d0715000c035244601820382610880c205130003c2080f0b0f640c805210a05092682c140301840c0b20366070004500725940030f6803a43e194170700b00c1003110505000d0002442c040140d0300011588104010100c041004034101d000103525500b00814140340110100f00d82d040880c402600c86d00d03105c4280440c0030750080f5a6001c8503412022580c00d0b4465611111405080c29031040141c4d000c2ca141c0041d141d8904c21024140e03a9440407840803c6251020405c1803000300c0d00c0c040085c0d0300098210001c0c01d94030909004079698103a0124604c5c00d6a4003604a11410012a1007800c0c001464030589141803829804158850801d002e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 971781339 1250 971780089 971780101
    0x14120f03040b07050d030603080306010f21020d0501050a03170c0c0a031a09060702030d05091e0616030c0801060c15061502010506030307020d0206030718230907080c21 74
    0x803a00408021030b12402540c1c20510006e03c6030207003005494000170058a592120340041d03514054041e4000140000c81141300044007a8080c3d0035000e01c00602c1c007503a030300101d40d82c880032240141c004501c58403c500341030001c5240220415501b0300075294590350f84401d01407841c83c100c8115015584641a59404410440c1d04101c503c00500c4c207070405a05500e88905003034851074103c03090001a4014080a2030400d001d4000380d410141301d90075941c1c81c0d041e034010790320500790048101d1102d074800c1081c0300782130000d01070303450841540d85000c03c0154036009000300b65a1040c4102c00810824510031018000043d51000c04c4901005040010a541c1c081c101c0c000740e07e8242d110095403030240022454140841202d117616401001d01d0b641403a02c0c1d00300700e01904060030000070803401c840c032803032200301c603489580c041c00b03500c980303880d444042061060910400c80001800307102c40300c00744010680c02480007500003502503401519074103188101d1454402d90f04000751305540d10b00174059 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 971782589 1250 971781339 971781359
    0x20310080105060d031b0201090905181b0a0e060102101a0a0506030408120c0f0412230c01080a230a06080303041e030324060801090614120f0304 64
    0x1003128003040c000d200664a41d010030078280303d080000707030100d038010040c4c501c54081e15030700e50780c50780c070504004104588488042084540450303c080600425142400d010a030400008540030006001075100000c454081140c4221504c60940d00031540804958281c0c02404100071112900400308000e80c0324072440a1107600c00c582c5140207098000000c1075908001e030803248202c1c0c118580518150000401c400c10050040c41d0301e02003c0300f4404031107110740140040c0f0081c00c10a2364498641080e0a1461501050100c050390165803a80028280c05004c502003d24074024200f4540c156038001410014000d4070b1a0510703000c01c007040b086800c0103000e49060049000c0c2400300400c41d03c134030410381c5d240320558015104800317603001410f070030700c1840c00c03003000610914010030305031582110507030030161a50000d01024510542488155032020f07040d4014495104213011640c42e0507070381c4880c2034004071940c0c0154220b10b44001903603030400c06138000022080c01c6988d113582e2030b00410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 971783839 1250 971782589 971782621
    0x7051b310506030d09140f1206010602011103040b150f0a03080c01060b040b03160e270606090a060c02031e1b01030b062215030903081303300203 64
    0x3004a8a0304000c00c020b8100029003103400b06090b11004415402d0170714800340800381800d540e5100c40c1c0c510103a0143d44030305180b421807100f090000e00155051a201900b500e8000e41c032510703181c0e8203104100119107031420702c4c0c0e0409440030384018500c150401056124026081541d0800da05500000800000400402d0b141d00b101c1e00030800d00d903d0f82c5d12005584030754407a41d100b1100600c0826020034642115005014584c10b1105c1c40d5451704011490f420a0b0309981c2c400300078000c1020610003e003401a80c2d00c110304441d1a89000141ea0001c0c510501d18010481040290301682c0d00f1501d04001c9544003054440504042a4505622075510030100c0d80000f440c0760415180c1801d0750080c001c0599540d00104603a0420282c0120051404100324071100d404440700c40008580e1030f500b1a00d03002d14481e60b00807980301101d09020313011700b80251041c50740e4071840d00c070ba00210350b22500f16040b00941c0e064881d0480c44d156100c11300341d407c07451505403003031000003403100114006801c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 971785089 1250 971783839 971783929
    0x4150b190608060307290415112b030e030f07060c12050c0301050103050703090b0907140613090b011701080a0c0b0a02060a020d06090914060c07051b 66
    0x2840503943d415040c103072039018600c00d4a1300b25918500a420958030340d03009680540f4031408840c20070381c0e2031108414240420883d2004a10314200d03245000206002c4040743c18405610619122940440503002101e540c0708481050382d100c0396030300c1c900014421145c812900d240074030b89a02c20340c20f042008000f5075910401282e110005101e544550b80910b91040d8a40c0b0541825686404010f50103000010140d0741096642c042c024006a80321401500619000d001001c000d400d00d100d200110344150007952050b0021300100c07113482d901000000c1a965115004901c00000b03900682d0b80d8120b030003182840d00d44841c00455048030010b42c0c070b004a070250242c98030843d541d0300385042c81e10500021500503040358000a61102d0075400801090944260015001d5500c2d1846801c07268030070812100750b54500e0100d522040104009900180d41426140ca400d0f07640d42c410780e54100403001105010402c030130080b40e642e00c9c1c20003001886000505001a2407044144a500182c50451 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 971786339 1250 971785089 971785097
    0x8030c060f15040504020a12051605011403190605030601090f0f1a0d03120c0e2b2a0306020309010608070f0504111b0a0b07140304150b1906 62
    0xd242a02051038150103582201e04040300c40031010240f20203484024016600308440b14000540c8081481c1c0360203900f40500c0c040d050700d040403920240c0e9001960701642c10404198140070f2800c000c202241d402c181981500003014030100114005482681d10140d49400780b00c00005017251a40c00602c1c000b1001d40e41008043c2110313449000b02d400b8141c014035514034114816601d802d14203044001503010381450f242d6000c503896001d080c0d13902e20400e400040c042d40380703c00c49070034041c140042421b190700d0050001c3d802c0c0541000300c400e2454003d02103441c0300c142d10408900000e0702c6460240444007180481e500d03801c207040694001d507100c940940ca000000640c40310007203158020b81e0000c2440021241c40c1c44104030140c4829149171110000c100480031104007109001d0301e07140109000303003508982504050490320f0000b0f00f00020302c4001c1048a850181c00011039520070f0b03014105240b104c0c034000915004120700000907030000101881075400424850101701112120b5031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 971787589 1250 971786339 971786341
    0x7091d030f1e2a010b090a0e0606030a031b0f0f060c17010b031b0d1409210d02070f060606031e0209090a0203091609020a031805120a12050108030c06 66
    0x2940d00403031140c2c0a1240c661104220b0b0001a80c0000c045241e074035101c3c0b00045103600d83c1d80001200c0c100190740071020141c2c0d542c00500c01403414480c890340500c04801411028a071501d020b007083d4204916822002175070001001002541c088080080303030006492000003820b40761403001800c41c0d01d046004a965034102c00c0c81441d031492100d0581b600010864210345038a072502607525040e0601101c540400c0c00440d42480c1035202d01c40c4546840800480642000010301e404c1c8401111040b20310301440c140d034401000b8100455100f61544c180c01a59124103043c4080441c00c040d4005000c07030f0031f0420000fa2a6415003100f80701d8050142c0e403104c41100340054204a11400707a2040d04064030314000b4182542030350142d80d00690340416103003647e0300385440c01811000c640001c031216901103140361301c0a600d41702d2054280c4100058102c1d86500b07817030382c55459645d4400c003031010300c0000c1c11801680c032411000b00c40c20030481c1c05010035611801c8498903a08542c500521501c2010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 971788839 1250 971787589 971787637
    0x50a0510062301030b21060703110c120703090801051906050a0e0411030f06040303020a0e180412021207031e0e010c111f02060601020706050c07091d030f 68
    0x200140010801802d90b07800c90340e11040154050700b0302141c40c562101000c0300da60401d80310280304a034030210b01001303403c0c60700d4020409411603400404880100304203125124400c04001150a2020000a11540c40d4074180c94211f4004403036030044d0845508200505c0f1a50080e201192800d40f034401c000d004007a2a0010310074080028071800860071400c4020501055030540e10300c00110022302500e03092000c0200d80303440d001e002d90b4100c00003940050a111050391044400b6000702088501804030802c2491600c0c1900c40540003400300058501c1c1c0c08501c0340200500c01074001c3d20384401d40c0301c0506040c05070400046090400c12100e03890414283d1612804011b8160b2405860b0001c4550130303500d50843d410030441240e0703002200d840b613400120b40200307003140507400c19074000e1404c0d282000009003001015844001404020f01811020420104d1820300b030702c104540009800c3c0d003140810400b540218100045400300145247c00d0040d4400240115404202c003400c00d02440 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 971790089 1250 971788839 971788859
    0x1202040f2d0e0c010305060a0b040f0e060a1511012d110a0f0516080f030610090e061c12020a0b0112080f091908030408010f05161b050a051006 63
    0x1500b581105402c80010400320350301030350100740c0040016180400c256121007180e1541e030b005402c082c244c01ca2400e81000201000c98403c3d0340000e05a50080c6031a00e40b8240004002d1141c044405004481000c0e240a050952007050300003800900151403900c0d80c00c494030100d00b200c0084080c10b041828001c40304445a0844801a9580d42c0301140c1c800c440d0b0040f600c98005000d800c40c0194000460000314a48001900500b160307000c0065a905104041150903250a201d403004d00074a04d00c01c02c0701130100070406500020960701c12204680c2c1c1e0140c001d900b2140240100707500b1980164003035443e80040c0b2000b90078400c01603000741e641c80d00d100300710900002400805568082100b1030b427841410020b40b04464010f0403c0e010000800c407a0308000d40380d9000100160300200d001c0194050901074045622003981c002c00031414140d00300c0b503280e0003490080086c440c2c2c680510b1902025151605915038020040d10182c030b00d245451a241e01e14003948040c41420b0110110b40c160f20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 971791339 1250 971790089 971790101
    0x1030509070b0307110106270903021e10020313050c030a050a1217070c02010201110901080a1815020a0932010e030106080c15070c1202040f2d 63
    0x140030000c140e003519081c801c041c15400103000c24100100500200a41c580c00d008040c0030f04100310521031240380a012810810000120401c1d04078109451036001c20703000b14040844461003942c50300c1d9001011035040c40c0c404248046000342d48000200581c00b4428801515118030440c01c0d81c20303200300c0c1800c0547d900c1007d40f0140003600b0410840c0d00255114211821103011030074900c80a482d02142034105210850301c0c00085900d1026010440da070a1240c8480a007000b0016800c0941c1003000030f00d41e02d1300a002c0c00280d590b5041d4114460103850f452440c240d80701619802c0c804905001c2e401035002414a0320224207110004900d031902130984000d030b081d505507007e07061008240208164a007200c032490501414a0b03330b000c2540c031300b03005036006041070000401c0041710300c0003880398083c01c081c021100001c00740140f400041c900c0d03209204031a02d081c0d07281c014500034000100200004140e400c1da00b490040301181c02e501d1010b4006400e8032301910040c201041d00518020342c0e10b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 971792589 1250 971791339 971791351
    0x90a030b060f0d03020d2106080d0807020601060f201f060b0f1c1b0309030816091206111306030e010b0a091a040e1606110a0605070c020a180b010305 66
    0x44880b040100c248103804405101c0041084000c0407d440c20754041154440c0e00a460540c1121200f00e0185400c59205a080744c4030348018082e540c504a002008152a42966030401001c40300c80d6002070f004509500744107043c58281c40c0890400d8802035030303141200130b5050070181800000203554500310143d80520048a0341c1e90303c2c00d8100d6200743e0240300d02402403030350182e840c40040d0f40682020b50640b540301082d140010b226410b410003401c0f8180040c0000f0300388452083d0711034290791120100c03045403021901039181100340d140c1a0050200340316542c0e0000c4010034401a010b440629400844115440401074001c007072201a0985d45a6407242c0d0f04081c0001c01008502820751099035503040813841d5100b8256800001016182c0702000385c034030b503801903000a180044420303041000705040c1c144850140003546002d078035030020443c080c0906030341d000043c0082340681c1240510642c002c00400c0843d49aa62582100c21201c20400900740b404803400da081d4028810580181 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 971793839 1250 971792589 971792593
    0x11401020f030408061b13090203071d030d08180f0a0201080702011802060307020c030f010b0406150206041704050402071a011a04050d030c3003230606090a030b060f0d0302 76
    0x20380e450494038182089074284514001c0d0412140ba5121810b03e541c8020300003442c230250390707410000002090326042100203000342d1090304c040640d0f541c002074a044080e81c2818020400d50782c2070700c03200342d02048042e0ba0140b070051003c106951640401c4141455100740c9401c009038407004000c86c201c8400e42901c0e083d880c2000107040152401c00c0207154000d1aa01c12255090b480302d01090410f070b03681c0584032080e03460380c0d0b5140ba40d01d024000c84010b401705131000545182c40c0070000b50703036440180014021449a43c0f2130740384c4480c0700084a010300001f40065507110001e281001d803c0e4494251130780c4200c03252001240303d203540b042860208869196036400c0034140b10070403510f18003041c801ca092210040c03120001509c444200040100b03401090724012000792801ca0541c40b00e0995101054036001d55882d2441140d6008150041070842009031540d0f59004101e00b4490245415488448a0380000401c500c1e503c01d42d00c1500151407518106041d14240148031004010050140e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 971795089 1250 971793839 971793841
    0x15021501030813440a061b050309060f040309030c0e071d0303071b05040603050601140d021e2e0909060303210219030501080c090103170c0312011401020f03040806 72
    0x44c0c00a03d403801c400649801c2d6440c01c10444810a480d00b00b0155044510741c0d220fa034000a102c009072003005031001c860410138958507018000c95218000200a0788001d00c840c40403c003031510401d10341015603071182080c680903848510341007010300e0407518000050790600007001041100b0b07071040448100a40110b050494903601d176070f907c0e902c00200e0303c20110320030800070b0155224098940214000c2d400f5000550411000070345001da0404264002c2616003801c8d0b0041c0c03680d07801c40c255206c284000c094000101300010b0540903241c60003410906140300c0070030307480c100360140311600005620741300b151960f00c0c8560741c1036541e6488042e0100307032200e0300d20307244512500140403880301c3c0a00040c9000030300134003419203080e129003005c0040c0d81c810050250100401000c0c840403000c40e280c41c003540c51a51485205050700b001442d0700500450603d400d2001042a60386080a50b0034109075580c440c03000c0c503040251045960300611500d03065050b81c100c041704680586443d00050402 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 971796339 1250 971795089 971795159
    0x91b0e012706120c081f09060f0c050d1406031002160804180507180b0a0521100b03040c090b01090801330b030115021501030813 57
    0x204940c41e000c03100451007500880101081030b1250310054400d055444610010900f0940341400403a000392910746d0110b52030001c0f12101010f140f84181c0044800700b1081d07554034000000e0720315852403071040c1e420f003950514415008005804a2404c15000308040708401100d14400c0c1d009031035898050700400c0d10310303c015810b500182088403001c0c01501070f049055882802c194000e0b441001c683c0ba0001c036a542280040c054660841e05600d8042c80400090907001711080d01e07403107510b016140008039054030602903410b80b5160201d041000f190040c45005200c14040211221800710078000b030080b5110b503540040d64050f98000080804050a001c0303803200820400d1159414803a901c0c000140e0f103031090207074a010020400d001c01b0b990a01c101075410415121015030010b40c40203106110f0545141c05036811101031403c1702d0a420303040700f010303410200c40c11043d12144485100210030f001700c04004240c00309c140312900074000c3e5a00e1800c22001d4007952401156240b040603c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 971797589 1250 971796339 971796359
    0x10021b0d0f050715020c06040503030a03051b0c070e130302150603030d05010b0a02070603110906030c2a06060108070906110f0105161b0c030b19050a091b0e01 70
    0x1066900c50801010711416584800345052210b41c800d40344a82c014940e944070a60500c50b41404000036a411401d2070f04190000e910b9000d14854002010344e201c001034842d04500300c0c481c800703500012036650340d81c5418030b015490b40c013540a1106400c1c3c03120042030034041298102442190554041c0c02c0c24400200c071f0503130410020700340356810b100501403074031044840c1c41070500030680017020079070701d001404001e410186a5445007050600d010420140e110f521011128214011101190b03a81d0350000d0405660103034085501d05454981c41c216070045942d010081030741760090445002d9580c52004464002040f02e2140001e454010104540c90140c0010680c106c900d00a43d41d0426140ba03501d4212801225000d0844240c1751401d448550413041d025a02007501c0411000070703200c0d44072010340f01810310008000502480c0081d4110600030740248084003184818003043c02c03ca0b60401c05821800070541701200071161000504140111100407100840d145419aa1030500036030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 971798839 1250 971797589 971797609
    0xd0c2c0c16081815041d01150302091c0c06080a0e070b09010c02030a0b1603020f090904051204060f30052a04030302060919060c0c05010207030e10021b 67
    0x3101c000c40d02e000d0f884141d9905034040140240c910080c80d210f40c94002200b0070751440c0201c03641080c8140300140311684e840304002d80300c1c0c001420702607502e46c2c0c41740104070300007003442003080f00380800b86c1600204800d10942c00c04482d01035031001655200c81002c00200c5000d09041040c03513215180c10001800320b10068007460505042403824030f44e03241c000c2820700781014011a080e14158041140c6018489a4a101c401c2c8070300e01141080c46258010103640f081c0e11125128000e000700150402c032080000160b80080004619240c0380d075042c01401041e54810110040b0341c0d41120511856400700ca40900f5800d01070501e0000580c9082003c0102005440440ca00e0341124140d4122180e00d0341c0001160310b07424045640d1469410004d0a005014089036200e42014004414103015000e19140142c3c00007400910203800f80c00c1951081c40c00c4200819a50003c15420141034116407c020f41c20400d440c0d00422030b00c40c00c030490f1240c02c0c00b441103500c0314120240290300e00301030a1003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 971800089 1250 971798839 971798857
    0x160807050a0807120f050610030e0c1507050307030e0a05040c0203030a0c1b031d060702031509150f04020f040203011206090c03080313060f050708060d0c2c0c1608 72
    0x188507810081d0004c0030545902507600d1540c592200103000440c00c100d84004101941803404001d40c00c07602e401e241d201c0c01c040590034032442c0018422450a0040d100b1100c1255115080317965a1001c0d280c007420303205417045a80e2094841c9800000d440c10a40510a1494420307809145140d0303400c8000001490140e4502e4204039407030560300300c25090380c0845980d03517001341c5a0a6003044c1030400c06500100600c515170146100388014001a280080c001c400c1c508030b02e000d84015a00c070702c00146802a919451000041340d0b905001800d1254408503001c3c500942c0c4004020584030140801d030300c028881d84035201840d80c10140410115801102014421122280000e5480d00c0d0340070141c10036100c80d001c0740d0004603c0c0e0300300401841040592a0390304411b0002c0d1415150241c02c41d10014002c0e801500e49900280401142c11440b03800f800e95880300340307003c0104113110342d00b50460500c07600100d101c0c20041507448840400b07550100c803d0f2103035078032102003541d24030180342c02c0344a503 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 971801339 1250 971800089 971800097
    0x1c0e010c0909050105042f07060c0c021002070602030906131703093c0301180506010510081b0c0f0105040b160c050607110703020306040506160807050a0807 69
    0x1105044000038010403862a00c169900440c07603080001d03000840b50183e2155204601d00310b00f111342c080c0d007032201100342d40076028050030040c00402c002940e84108000203241900c0e00d5000900540c00441201d45c2c2802964011b1011021100507a45c0310300710b025290140c0d109204807440342c40c041009041403078054030a10031065580c0a00701c0080e0b031101c1d440109030004141d000c0a8200386044803590100484010303d000c0d0b808a00c074154a400380c0b06e15003080d049038041100340d2001d4120b222444030303c2240200b520000d04129403600b80230f0103600d2140d00e8150881402c03510482d1118016080024a0700c00c483c01450700000c2a8005901417100c0c1c01840f2140b00e05a00038031566200c0e90207680c01000c00e00e0030b20800500902c070b0b5103000d414030040601003000301d9000110340c1e43c481c096051804403084c003110342030301c2c1c4916913000961620030041044104000446d003180034800d80c1e914400600c143c0308042d134100c0021101d06001550a0000303042d40b41c402c3c0303840c9820081c3c03030030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 971802589 1250 971801339 971801351
    0x60f0c02010c1106070b04080a111b010c06020417010b01030b04060501080c090d0c08060103020a090c0503062101090f0b070c02010507060515042405030303073203070c0501150b1c 79
    0x3403124400c40c01124103503a03034500401c0c62710606400075403c0c0001841c9001504120650f01d408940341454184006d04210001c3d01440400c00700d039049074040c220011905407050149071000d4041c0120300c40ea2800641002e603000c4550038240680419100140c60388121950b0b400c0b244005070300042a040d5000b5183e0701010007140729510400054900300002e0042581180180213008026034080500c4a203840b194a010952000681c1e804c40021262210b00c20b072011030000c1d00d0030600c081407420354a010440710400c1140583c8002580c40340d4000030130741d524580240d40c4032082e0b050103804504108200c00010344923502180d404240601250f40c01d00c500030202e42250244d1000581c200f80310070a201244840007510360080804400562441c581008002c00d03452111240c4c481c114400b412980640d0f1142d0741100c0740500030062070b5128601000020602000540c080e50207510f0300341240050000542d0b801c0c00e503881903200354070307142d400c141410b400c0750341e116445d028076501c074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 971803839 1250 971802589 971802593
    0x306100521070f14071119080f0c13060302090103020904080408120301030302100e030f1e12041506030803190b0a090501091a1c0309031704060f0c02010c110607 71
    0x6a00500400d925a10082c801c106104050583c48019901d11810302017404403800044881151041d00d0605035001c1001e1121030304118040652a00b0810b07060180212a484c41c19000802c481512130451350303200c1c0703002c241d071040040324454007019402603817000040c8054100307075000360b4010740724010441c501a914528a41071000010004400c408004010001d169041265032088920328100b0400c6003158444160759109505920880c08004241c0c1d140b1a0f00c1c510810b4803000030700b01ca1030f90360b24064003032040909003160100c581030b10310040680b1a030207903c102d000342ca6101c0000c914580b100c0200c900c40640c1a001180d0007034554515000079250700950400030300c2c8400c03001c5407950502e40c1d43c4060f9000041d003e0340d0002401d0b840680c50381da044141c86000c100402c5032220140c4c0b41411909211150030242095a101e04860700e6440004020811614299203482c0381c030491503412034206900980281c001100310000030042040c000c0840900d40000b045280741c00e04035 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 971805089 1250 971803839 971803897
    0xa02041e06090605011101021215041d06061032070501090308060108130201050d0905070f06020319050f18041d0105010f150203250f0609150203061005 67
    0x16040b0b015426141c41041181c4d517040702100c1d032030b514400003c2d81032005004115806803c0105002846480402c030106a03444660280a00001001a0802c00710950308902d950301d8040e1580d50045c440042e801c0b06440c8a4503401c011030000f200019110340e104418245085044400024152010000003001420034491412268840d484845071894443c002400c2d031032009000a1054110504408c0140e900500b228090094008000740c0aa52410a40d1806e44140c00840c00e40030a00c0000c10000c0d00013003c0e00224100c446c44008203001c1200484e41401200c11810305c91074140160111000c03c403815505819015000003442802010811052821210305405996440c00180441d02d59139030306c94090010684000200a00341000960368850b0582840e4030a5003c0340d52005910549107030b280b030503005081180101d0142c280b620050610000c12564180c0f0502c1c0c4665004d40d80c0203880c07043c1030051242d04200302a1501340e608c1d900c261140600303202200a181c03064484 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 971806339 1250 971805089 971805101
    0x20115060c0c151d0603060a0e091005070503010f0f0f0501050706200c01110906031303140703080a0e0115052b060c09090203060a03020d02060c0601061e0e030a02041e 74
    0x150740d01c240106a8881c01e05002c44004c50340140680410020001c0544581546404440c02c600004100740e03541d1100c2c501780301803582034035905410320003880041c5502030017660507550701c840c08481d5296207882102c43d0140c036105070240d51100d00001c0046600071800380c11814000e05000c68206580c080c0303c08d1040041121600400d00816030241c045000d00c9850354501c80c000c585460000e411000800c180001001c8044100260004d041054882c402c140b54060300180806c2d00d510007840c010b8400302d012505146000d291158000009005020303c900380100441c0400e01181000280311401d41c0001c96242201c40311580100c080ca034214620656902441d00000c44680b2101d004140342c0580e80b14010740f4bc0140180102981c6000b02101181c4d4119040c0c1607186007031020a600d400380c2c8032807150b140a140000103042e600306c0c0d6651780c0c1030f2500c00c421a181071448030079210b030208a0b04071070305688920403070030060516510840200b66140c801422001198140d0320540354 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 971807589 1250 971806339 971806379
    0x515060d1505150906030703060b030f030f270a031b051203090307121709040b060a090303020c150301090f11071a0a05040807331506020115060c0c 65
    0x541c500401180706a0140b071103507410400c84a0000c28217000000a545003024080604521f5444042200c9580c0c20040c070070403000040140da07126025400c0342544c070b4010018003a019804041914074124802c070401000f818010158150309082d500e80e1b41360041c4411104a0074401104082550f540d80018503409c2e800090003150355400400a040c2003445a90154500a814070f606000066104d5100d51490442c0d100c000d84541c2d0b0340340010080c0c501c04110503000140060650744e1a0780c40440c96007a640a5001c0300c1608400c0001d0041e4000c0341c2c180468141418001484040d82079000794142c82900040407401840c00f500102c000d6000788821103214410079444041641c5040c0d00302d520443d440801c22a519068483d071a45210340300d0f0051000d41d07100d03180445c840e0350108004444449482d440081e020140c40c0340014200c000011030303141021440095124414004e440f0300b1020f250140d00f643e441e010080c0c0302007152103402c480d0b2038002040820703030114013054045082 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 971808839 1250 971807589 971807591
    0x1060f0f03021008271006030f061518020714030f03040506010509010b040b03270106240c020108041a0705030a1a010509060a0c05070305060f10030515060d15 70
    0x41c0c5544100704034418000c2281c402e004500041203c0740301c075116036008090959070fa010040703045500c541d0410902608500d280c62826034003005201e004030224008a00c201c01c200903980d85000d030130800800c2c1c0c1c45000500e4510304011058202031780c02404e82d1510810010702101146208070f811900030000b5003000701000301c10807003030003420091580113200c10384282c0801d504203490440d0318400d0f400790041c020400000708104006440804940107900080c2c0e1841c04005101d442c00780c662441290403402000c0446c04528802103500181c0040e580c0b1225079090700307a07005540400d4000c2094804020714614552117101c01481d00d80b04010070b03074805640740b600242e14400c5038441d18184212100300d40145c022070340c0100485c1d410140844026403280e480368421584400301d904020b280e40101c0000200f0403d000802d2030248440c800002001d5490400c06002000107100242550344985a00045140300702e0890750044070180c5908902e10a40d00e540d450943c990b0340a207011 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 971810089 1250 971808839 971808869
    0x91f050402032809080306010c0510111308031c0e21040f120f2d0c060f08090a03050f090306180613150c09030b0c07020414071e0201060f 61
    0x20418107032880c0d4803800e150740104132039441c0b6195400301d40001400c1505000703e800080c02030000810000b5080d10100c2c400748080c0e100303421000d415401208186003d490000b0b8003046402c400710980b120b4040c0e41e061252410f0080a40314050042601280800e0092510540464111203811003218800c840d14030343d1507140960510420b8a140e000d903884c848100c0365400020500d01110081c0340d04070305500941b02c0c01c10140345403c45400301141240000100c2a403c0081c540710306001c41e6081e4641c00440402c2550540f10314a046a040040d50030156080c00040d0181c1d020780304644d00312001d24200762a03000481d103000400d0302c180c1d103114000181c94a040ca01000410f902000e000c1c903900007036503295a40904200161001900291501d034402c54091081001000a68110401501c2420000c44c0f0701d01c5d607401450242e000c0c1e41041c03208610b002c02c400800c2d005e01900d94515119042c1d2a03c403800310103510300b02d40d046540703410000980700e55034108200030b460040189241 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 971811339 1250 971810089 971810131
    0x1060306030c0f0b030a0510120f0b0a020c030d0c020709020c010e0d0315051e0d03050c0d0f08010b0d060b0301081f0c0e270106050a1101050402091f05040203 70
    0x4034500707030f120442081d48142d05115001110f02941d0304001c1101c00460035407612186084080710390703003000780c480c01940094410b101c03002c4181c001440c0140c0403102141c40f4180204164410b000810100341d00c200004a08604140d000d5252030300c0e43c0c03054078052529481c8041c16a803201c403003081140c0d180d1800b44a40300d020710908402c1346540c1030030400d08070101400c10081d40e113481001d10036903456041e4010003d411814401802c00241a01000d10302c27854040d01541019410700201d2244c814440c44a500178a440c9915211540b1134906a80c80d00001911907070140d940410890748406000a00420080145000c0d1072003401600d0b0305c000c407180c194103e011343c1c100b075500c080c10180005040c2c0d4100030601d001e0401521070b940c0302014034a540418003101c1c04060240d0038110b000007401e961100240c41224016030341d500e42e004903440440d090f0340d0143c8010303601c200450003044002d001100b070648690800d0a4814200c2d88d10b600040490300102c0b0400c81003242d1a480c2c02d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 971812589 1250 971811339 971811353
    0x51b2505100e150d060b03101d3102150903010f060b09010c0f080a0f080708070207060f02100e06061f0c060f021b1501090c120c05120106030603 64
    0x500307a0300751801c03500203030604000030360420303650601820309480000d80d80c0c050100e076080344000c0c2c40030f40c2001c4e80e41e04015443c05440b40307552060b00c20500b002ca81f040c10300d840e030541c0a4018000a03408440008113011405d00c40f03101111200200009400300400688407082c1000500300710250640d00c030000c101c281420741d1144073308220302c4dd180c00800e00c8204091419a40c3c280000e10342652130341c3c040c1c5008801d03070b025100c000d0030700b40d4003051144181d5840700c9041800031b519540c50155403140c5c0c200f0b44081909889040150b00500001e2021900c5269130400200003441115904200c660f6920211001c4084031341d0305820543c01c01c041c5042510700b00e86031704910001900d0720740c40c80f00002d21031702040c0c200500042d100c9900d400d41d04a1901525030705540e40070700381100300f4402416662240d1102d00c0d041003c40702c00c00010100c1180c0b140e03c400c01e509440301071813108603c0d06500100114007190307040c05030520900100100180d4101c0c041c01c8035071000280d943c114201745d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 971813839 1250 971812589 971812609
    0x72a02120f060a09150e0a0b100f1703070201030e030f0f0d06050d0804030f1112030901020c0901050f0d17161104200904110a0e0406080d051b2505 65
    0x120514100042480042d011010394101c03a0691368002850300e40703000141d801d040c12550003412348030824041c0402801c0b034489100c1100d0442809404050745d41c1408446007207402d860000341e820605c903003000b650191b000414041c6904080d02e15003c211101064031703400003903414080d42e00c0032030740b0543c0ca40e0610441c0c1c090b0004070b500108010706590343c901c042c41607010050210001141c00720803c0071859082000d14402045082c1014880501c965a5008100c4190061040f0450705200d41172030420141a6000544941f0030b601c4120148030841d011982c049604090a040847c2c007c1880301c007407c13031410390b148541c00590700c3c0e003402d54109010300340051103241740c4400c502c1188080b14180864281d01c07800161258460340000b001041030440a018110380041c405402a510840ca141d50200480703042054a441d1000c4555815841510300040360081004800448580043c0c038901070407070f01100e200300f011002e00030415500ca22b1303103ca40495500144081d1070280407036 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 971815089 1250 971813839 971813851
    0x70203010513121103040f0b090348090916090204080c0f1309050303060a140307050616050a0f02091e0103110a090216050d08072a02120f06 62
    0x124030201e294403651030f4400780c0d407038000c103004190740c180b81d00782d00c04d005440c010302c1c0b0345150f2885903070707034091400d81c1c0d51210301100d210740521310742504009e0311590031040703141c07815072a800301d10201c10401c1428101d181650344c0c0f00344c14142d446041c1d82d5241c1c8040c480c00f014806011940000041c42d81102c2c51500250301d401d00601040c0b1400c4400200441248012240078544002c03003000308103117034111001c0032a0b050030045000c060000000056005000c19a500c1d06525900c0c104000006c40e540c90180c0e040d00460030400c80f0340340c910302070541c544101d409512455410360340e0520f000711490044540a11002440703065103002910940d01500d004030346200071510b8030780300f543d040050200418004110301403c4254a4040c01d08028208100b0b00315500c41c58a02c0003101c106418908440a208010070448541d10414400e0f014924070f0321900254418081203058040409407050b1503100780089000141e55680a031111300c4001360007614140e0314440081c0d0a15800601d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 971816339 1250 971815089 971815111
    0x9011401090912050703022508150115110703020f12030316032306010804050f0d050d0b04020708030c0d11040b0a0305010509090d05030903130b04090b01030903050720040e030702030105 82
    0x1740d48007103500440d9601d50707000340140d801d2404401030414440b080d001e4211b100710303100b1b490700411071143c401001c90603240030340c42d810b00041f8801d40032540b200356500d04802d03a4111440800041c00d0900c80c4070142d1400816038484c40e0b0351240c040d442c58008807965100d0030118519440b01542605c144060300800a1003105059000f06c0003480f00080505000e040084c41030014060103014000c60440c040181c05507083d0019402c5c00a206030412814441100c3c50071510000c5c924041c401c60300005e038020702190455507446080d517501d07007281540d2880c094542d140804c00903404030041001d40303003085502d622040941c40060850748160489802003001106111030008001900303400100c82c0d10b4415600d036285003a80c0d0641c024592006801a40020b011070103d040c0c00140040d1080101d0800c244200310b001102660031407079020700494010003c00c1e02040c0182d0580c07046007062000f00c0c003402000070104003261450341c80308085400201e0003004600d0203000313250700030b0321440d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 971817589 1250 971816339 971816347
    0x30a122003061c02031c080c040e0c07080f0301090501060810080c0d0c0e10060f181502030702220f0905120a0c0f3c0b0901140109091205 61
    0x2500d21200d1002410042c803c0c0050f85001c107000c226004012500b81e40902550450f0040b2011072084000910078200030482c120009510071081c003082e60308581491030607001d680c48040c500c00496018100580344107100b0401803160440400c001d40c02403210410010b40c0c0d40c500346000307140c09009040381b604612401c01c00c01000000254288040d0340840d45c140a15010789404450001207900807104000c00f5001c100e207a030342e0a007094003100c0054480b100e903101c2d202001c507100c0100245c121880c1d81c60641c20701400c910001c4c074000490f035034012246003c040d600003a400c8160394480c1c100d40720030b003064400f8030080c40c0500c001034400c42e901031080030303001e5480e5503e0700d00902010301c41e40804aa00729150b0320032809045a6600003d40040201c81800c01116405140c00c0103103820803c44444419001c0c0710701307601700201d0102e40b0562204055510454122000340034200700359200c61400c81603849507a8464001d00b01c0c40300001d411549480c05840ca65607020048081c844140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 971818839 1250 971817589 971817641
    0x30f06010303030b040f110714030a081902281803030504050d0f0c031406071e030e120c071505040501090e0421020a0b0c0a051812030a12 61
    0x6065419658581400700e8941541d0003c01c00505041c1401e0091500780900c0310804a0070400a0000a0007413060032550410105200d0f6603215000030700300099002d00006140c007044a0f00d03074103120241c032009450b14410040c82c4605009104c4817102e25509900c00120590300301b4003a44008500078044d800591460f00c0140c4135006900c02c440c018400049007204210329848000d001d107034040172140025032a42807103001422202e071840b03240c2c0b040c400803030b80c21070080344028220102c1402416a24649107421400340c8140c0e40d1001c0d0f940700d00508904512001400307046856015401006141d1505a402c081c004002940b0b60904c04100030501459900c260000150ba014004000003516689402ca403040070744074800903202819070700c40d8882ca070302141204490380181c404840c1501d07049a61096845640360b1240495020040813081c08420340e0130059420000b065144c41c542050003640c21684203285050000b15a0803582543e000240700f01d840f0100c0052541d00004102 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 971820089 1250 971818839 971818843
    0x9111801061b2a0e01050411030a0b030115060c020310060609050d030509060409020903010b0a180b0414070504030c0b2d090a03080307110a410c0f030f 67
    0x4024286524180c608552041c0200c4107455601005031510030b00325a000541180c083c003c4901a400780f2030254000000c444c5800e016244001036255809407541d12a65813801c001c1c086820901c3c5c055480b007907106042e0b0b240f400040010821900d80000c003803243c0c0704040c10510f552a061000702e217050790500070140c0c040c40b0700c02911000d4820018900031800c0c10f0b00c40e4050038045981c801d40000380480d1001860b009400444001c3e80207000c40c050a10410402030170500034000507480000320250386100c90340041f0b1103607801400c00202100c07080f001c6075100320112507a10108000240030010440380e200c91800404400200a00f0150311000d2011200844110724440854900140d85144950003c89241d0000282040b080d680e4071f1800708156003088510b00045640d000c2040b42d42c503000f10701040c6e680e41c0804501d01991881d15110a008040852401140e01c26845420303004401034100d81180e903410010200c0004901c00c00104d0350107015003038025002a24062205600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 971821339 1250 971820089 971820107
    0xc11190209060d06020301091a03011a09151c020a050a0b0307080a060504020d091e0c05040c0917010e0c010c02060a0e011101090b0108060c1608090f040911180106 72
    0x8125680082920b45600180c6508000a03000e8081840003000080d0f0400d15400220005014400d032a003a8116408060886132107240c3e5110b5000c0c040342e601018500040e180758072111410042c1700098044000c1060341903503011301d040208001014405503d003030800440286004c8035162003850030460401254000035000b0002c2c8860080030800e49009600800081c18001c2d00440d2a141f4680800d40035002c24402a2102ca8603044c0000c0c3d54000302a00b8003415070440c8c0000c089900d04028880103210703d4030040d0400210311000310b8500310714215100301c02c0e169030011a04100200a036401c14160000390360500003981d846200584800040d80c41c080c0441c142010440c441d400142c030300034140800d0386565440c0410030002c001001a0309416501ca040444150f0b659600f4a040c0d40e1142c0c401c0030300100c450300ca4807000260741800401c4031a0303002d81000500c07610440403800740c45954800301e9030f500d0b10904a01c1d2508003208445003040400c10410400e5162550103400800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 971822589 1250 971821339 971821343
    0x13080708070f0f080306100e030705060904020915070b01080d080601050c011b03230106200a1b0e1b04091802090a0c1107050a230d05010c1119 63
    0x11000c40c000042c4100c040c41681c5954100c0b1005407100c42c0c528090445900c00c4a04038403a00301c45004081c500d106424503c9260ba001c2e0040a0007402d003000c0143c203801c06540700303134056020440b045882d00c514030300101c001e9518085945079601894401403002058120b84002e600a140d010b04455010382110381010003030a0195071074504000440c05040282c1c0356007008a8072948010000390301d0343c88191525600c1951200c0500c0c185400e01e00840c080c8130b0800010440c100000346c4501034038010030101008812541658165030f01c641e00d03060b14100044003400080d0042001e0641074501e281e00030031590782c00019440d588203c66860055000e2486040e949400400c002c84102d0030f006001c80d00100b0501c1c1502d004981d5002400504050074005041d41c0004940681c000604ca4107507040140015a05070611542d982c01d0500e8101c440010411030b010322140741c031004890003c081c001c1002060403501000050205040300ca07201c0c80992186c1c21040c00550020b4100403030325 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 971823839 1250 971822589 971822603
    0x21c030b0f120a0609050c0f0901050604092d0c1101020310030b0702010e03030406050103060e060709060f1b0302010608190c030f0201050c060708070e10050d0906110d05010e130807 80
    0x2028044a140c10f6418400814080c07070f01c042d000c10310000041c01d4903c803100b00c4079445000018806d02444400a100d01600721409200074440802190045552440305e0034035a0170542c00980c2d110a19610403800040709aa070b440841c0c44142d0015000b0f450f5a44040203500c0c60400ca00701001905103440081d164031108000714950394801e4000311080742480341107949a046c1410035a0080c2420b1104a0b505460200da000022901065885c031031203807901e964001c17616094080c0c0f414012904103038100b102403201481c0d030700c0c0fa09160201c1d6a003e1b900019095050039401ca140101e4400501c07100100c404508000400d4020348505880c1e101491f049503042c28401aa41030044200360100e6001d023004200710b45a01900d118418107090b0344140c0c10030660320601c00140500519a00001d0b230030000009000400d4210524440c41484006840c0c040d0f540820020340160f40aa03d2050b140d00040240006804009420041c4444d0840e40f0384196a50702d80079200d030290003070802c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 971825089 1250 971823839 971823859
    0x507030c05011b0305100602060124030b101805010306050a170106030606030b190203040b0f0702071701150b04050d1203020405040212340e1f021c030b0f 68
    0xc1801c1d00140c01c060030103d60100b0450314814007601600007140c42e8445281caa0b82c0002c3c001c1c2c030000c3c041741282d9840008241148820300308145125110b440070b4241911685003100ca51925488580c00c2d2845036510343d00800c40713440e40c0c0391282403580300700c0c10141001c42c04e03c1550780b02001c2c41c0c00c0b1a2910351826950152060443c05082160710140045103000c500109000a20403c52720501607000c06c00b00c0b4869100c0104104d010640c0c020305511505000652071004250300f6a4218609004803401d6940d14040c3d0040c050301d01e6510003d0b41d4546900d90f9401d44112400006400d951441906145c20076012490f1041c4171500580704841400c0c40400f400c0c0a0350442d4060003000e0300a5556503011014004806026605569182c080f652082020010850700c0140b801005054015002d52004112031103a07001a9841d400703942550075805c90090000700b001030f4407494005c3c004403045a0343c035803424030034403240398189800e00301e4180d0203076506903208a103860121103401d80 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 971826339 1250 971825089 971825093
    0x303050c010b220b150f1c06090212240d0317101719170708040b1801030e07030b06210c1c05030f0a09030f0c030605060a0b0405040209010c02030d05040603050f06010507030c 77
    0x1f00c01d040c51784c00c00e02c140303000004143c44c01c00360002d001804d0740c0305041740356482c2c03078440041c1c000760740f04144200982400124602c1c68203140008003607000e4a03007151219105801c2490440d401d4901405120103040d0404c1b0480000c8070b920804060b1501401400c04210319103003000001c003500410078480d030249640e0700c56412040e81c9000d50803100841d00c468592216020941c8032075a01d28138070062ba00d1043c1d1940c864003800d00031268072005080707017034599940c00380e240c14080c101131b91003040700d400b1640c5003291205414110340d120f401803d06005010034855400544003084122003003101500000c18000001c50703080d504400201d83e942c03039608604171078131002504014110460401102c0034850f1442200007541c0c00b13030304200880c1d1901e108103c504405481600340f0340200340b208105910b000e40c050721000c0d03010304240041407120360000b401c02c0d0310b4000f81c2000c103502090a0084079494400d559115541c0142e8444c0380c14007400103000303030141460041c01c20010003d4201 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 971827589 1250 971826339 971826367
    0x609090703080c030309010b121504031416060605030105070912030905060d0e060108010216290f09060c030709031b0b0f0a0215040209010303050c010b220b150f 71
    0x950b04540e0260700c500c20949003a881c0e40c8180d94611866080c04103400551504000c14000c0740d4400004011286e10140c206480290050003503061015940b105502e00399100c000700b1040f41080081d002d030000380d01d0500102e42c8960000d5019a151804001505800c40e1245056680d82403240307880c00e44519044403844a1500324980080e00841d4688502c55a0b421840c2c20043c0401034031a50380e26280044d08078020a072081d24064000a000b0000c140c0d041c040300b002e0b00d04a01d1044040c405040c20401c80681652030582c4030424200304904004240080c5400a40c42c00802d4070710704064038000e001c1800750102400d8900700d00d540d04d000d081c1c0c01020800520003c946070b1b450300150b0000c40580c1d00038403440381c058002d0559100c6040740000e1040d124540c0241100309590031900c08480b01c5d00007504010703d540da9441e442a05640c1d00c8110709a000c5001c403803c1e0040c14103050201682d4252181600820150021003072860050341030310204070100b00c5503a00e80205001c164 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 971828839 1250 971827589 971827603
    0x26040b0c071e0305042310120b1f080f01030507330f09060809030a0c03090f0b0d06050f100503060307121101090e09060c0906040306140117010b010503060909 70
    0x10b000d9214004442c01010741000150045880c2010980003510f040c888000041c502e00d1140b6500c400d0b5080b622070b0040c014500c0a040402500c00003c2d070340495004105681c501d0848061a650403000840c01c180e880b54529a12141c140c0074902a0352440e5100da903911814013421303003051010075250050300034104080d00060062130101096588103032005d04211b40800a4400141d83c0d0000400d9880c050601180507003171040042d032510409000407151182509002c40c10064146000642c0707200701540d01000e081045030242e900c5a140c01c511f0b08451059004d103008800c200003468643da542105030248242509043e6940e40e03d68000030708156558010b40b4405d144094507405200841412120711f1000380ca03001c07885526582c40550315001100d40c1e281a40c068000140e0142107a0701902400401511842c03c2070303182e45e40c0d2410368803500c0380c2d07108500669004120200d0005035800c0040d00f0175008101030a80705c00000d08170711000300b80300d000d0020007000c41d0410720108090 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 971830089 1250 971828839 971828873
    0x1106030a02160f02090c16060504170403050c09160804022206060504050f0118210b0901020304020f010e03070b1c050f1503060118090c0e0726040b0c07 67
    0x442d056900901e800160009a540140d0007800fa29000414018010003200e000809400010107030000da80e80350381c068440200100c43e60343d000c40c07460a5041540c000783c0080c40c0b0400251081d401d0308020f004202c14000c008100c03101488104e0b8528540003139555401c25010f5507902c0800c60303459011640701c5610902c0a001c2d41c640f080000b841c0354010003900130f48100300d91041666250000468a041d0382001d060858590043d00b0021100b0500e40c2240e0810804422800e096107500d54200304001144c503200c480c0d4000042008500d4000800c00c101d01090800c1c401132103c14000c40e030740d0105030198580342540060108200b06000c004010000501e40c03040c00140b500c1c010304034590304203030303a145450f0342c400803009494a4040350041c181e500c00718403a2a110150384002c0040c110f01d100c20743d0a06041c030b40100301c52803412440c80c130840c040c2d100d405544450000e200e00d41c0001c01100c01503ea414018840040c89511030aa0410101c0f0711072601c03031a00341080300741c00b0020921 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 971831339 1250 971830089 971830117
    0xc0c02030d0f08010b0304080316110307230703050c060c030d05070f1202090d0803070c05070609051203031311012c121b01031a03060c22031106030a02 67
    0x2a040c2036101241d000104810b40c0c0e03480031070341d0320400070300c080c08107403001041c48c1401c0c00011002c820000000710b00c140e462901d00c41a010800b01e0a04592100b07009581104600800d1a04003070000f070181e55034581c92004002051454440644903411400414800c07000091100c45e4404100140e03041d010540100700440c0c1843c00c4080c9c000f01740503c1400108000c14007101460035030f40f086d51200c10300030f84070a6925801c1da0310031103913510040c01241407102d00805034010441c100300d490058582d503180c0304030003410002000000c1d0716100035950035a00801c10090220741409a004010707500561a041c0000200016650003002245944510310030a28414100403c640340202030a402d0b20b40001302c070403606c0b0f00740d11014590540445c02c0036051100d02e40b9417103607201420134124600c0d40c10311022501c000a0802c00c0c2501c40c01e0034444041007aa04003101d110351070180308030780c0c60300411030761071551740204000c1c0070107030300e84148004000290031640715012a40705001c0c20078 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 971832589 1250 971831339 971831353
    0x30708030d05061c030203030105010c0327062a110d050312150625261c09120521070c0b060906061209030409090b072706030c0c0203 59
    0x307a0200030074040b03c0311440740b00200c0c00003400c6488140e18958894050b8043c41c136680c01c04c401034442d140c1e281c004408005114100c0d09441f8030443c25105a000310221003980380785000c50040c290f80002424000d00003030300e034a9036036014080003111000c81c0e10040f041c0305620114002014244442400313801808000b908501800700304900601c42c1c00d090181021000281c028004140110a404012030b4548611002c200e00c2001c03030299207510410b0b164860380114600080b0620032070445510400340413404803000c29203a4498031084800c3c08041046040a86800d4550b6480b50892001c1c0030340010030a01c458041001403d0540413242c07481c0140c00c0c9102e000701700c00c80c1c0c5001550a0b00500000c9040342c548440d01c1c60095400501e0303542008003003d506040210080c00d0302105100c20171001940c40600d0281003039040c05000c0004c545d18200001800c001254024820021007440b0b48244003450401c110302650010301c0c0000e6411100e6500313692414150801960500c00c0701 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 971833839 1250 971832589 971832607
    0x70509090c0a08160e04030801090e0109060e03090f030109021f0201150f080609070f090c0903120c1a0c0f2a0d0f0201060f0e060319060b0a0501111b03070803 70
    0x4501510342d00e0f084021516585e181070261204000351740c000d0000f9205001082150b004d90003c80007284000d0000403103030b01c01d0340d44200319100d03600048260341002c2143c4040703150669404180c10000e40081c441004142d002880c040008142100c08900c843c1c01c00e06101e00c00d600c50304011050140c0c0d03400450b00e550400801688901c103050662103a000000c01c1010003045017802c03162210902c0d1446801c1c00e01c2840035107400d072640400c004018200001044184500c0d1201034155165010b559000741420043c4140850b4041000100c1c04113001c180b074103240840b0401d20201e10000e80741c40e814600251807c1800c221215441c0a08140000060001c0341800ea003842030384640042e000340c1030701a0709a130390030300c0364841094480804004230b010b0540000c0e4080300c0101034a140512005058014618410082d179003c3e9454141d1100d0b82841c01034000501024248180940007807140182d444007080c00300000700510030f5850005840c1000b400c805048440c042d00d449030010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 971835089 1250 971833839 971833843
    0x3110a0b0a180b0601270902041d0705030103060b041805010e0d1409120304080610090b0132041805040501230c0307050f2b0e070509090c0a08 63
    0x40c0e40090702146411681072031805810461076406a111140c10115501c4500554444008520020950040740205c150424514800101420031004010384407400c154810a43d60702d05011006401c0400083c094003036000b505490443e07038800c00101f141c1441501090180c6240a1041139140140c800780c0308004041d0440c1502041440468006500403c001c542c4034582500c0410b5506040000c8640340c00c142c00700e1068821050b08503881d15513243c56061a0000413190000000f054110074440d070100e6005e090314512007440c055550501d0841c080001600a0045014040000400c491440030940980340103202c8540011000c03050070041001401d41101d003107400c0e51a11184000644054401c04050890460a2142551056840101688040e101c5424081c00f44100d40942001c0d40c0140100b100020400141b0124525a402c0e0f1803045250b020481b0b04014030400020f000240d840c0480340d0071204215143c0b504120b1070304103681204a1500810201030100c0c0c000341c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 971836339 1250 971835089 971835091
    0x80703030212060306061008040c0819060609140c281107090c0203030c0c0a050307120807030b06090d08070f0c1a130608090f0601030c050102162103110a0b 69
    0x1c810b40345250380c6a100b0036490303100c11030320142d00844140c2c00104651048081c507500a00c42c01c00311030742e00e0301e610085107083c04482200305d110000c080c0000800c00d817406554010145d101083c403120800120480c00307803900030440348954a0104101b4410001c035400c4410584401c00b141a111510000c000c00310301010440c1d1200344500e03030f400900300400b07110300207680c022030f80070f1030030b5813503561621185034000e807040c20851003220a6180444c6e424001016068450048400e401c80700000240040307000030244d4041c0352400b810080203481c0d5104480204504a40c510302c050068508400240070f00007000d818070b035403040d12104200c4200040d84c1602c0c0c6203010103810f00c0b41d002c0d84005900ca203030071082111044110400509005584640e00b004030041078483d68150b03070210380e142034400d03030056500b8403648104201e02e580500204c117180d03000a066508003400c0c0312074000c00540c4480d180c0c01d4030010010700320905208583c08102944040141e58800c00743c2d0030301c0501c01d04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 971837589 1250 971836339 971836357
    0xa02130e0604150b04030204020f0f030106020c01082203050d0f0501170105010e010605092416170705030f0c07050a0306050114040e0d08190612140a17160807030302 73
    0x720300f00c0354a601d5410341c0b601c2e800303c1d85080d032250700c1c0600715400d0102a40040040400c1d0105c10b0005d80c0504510802032f41c0607001581c010706607074141000040124a020b00924801032500307900440284001103000001d43e05818026901c50000c5085030040c500c17640c2c2c1c1811289044004200f40888011001041d940348000b4031090741c89201341c0e0342401080c4940d0740400c40400085456050140f400e0807031001624040340764078111241503c0552110361007003090488821404204040701c580a032009400c1c44549050180660340c0f140e40b40706038022085001300c04a10121359660401800014120140c049141584d6070314058004d0003080c0140803500690350750a294500b0b252051000048403c401081e07503c245000a5445c650042c0c242d90f941d4004008100213035040b0300514004246211f00541040014101074180d0410030304c0c0d120243e0007544071a004610660740c24259884002d1040b90b03180c0c00b0745480344042a48500080845001188207000d254055024000000c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 971838839 1250 971837589 971837591
    0x24041a040e010203070c03030b27040213110714160f08010501080c0f010c022d0f0303030f0402011407021509121606260103050d021219080a02130e0604 67
    0x1c0180030045090b40021507070500000c000c00300d13010100c0d12a4000011080c0090131500c010a41206100c01c41d5032305c0a10014a10042c03004d00007182088107000750000305039081009450450350f400c00b070314403d850000d45502000c82c40300320707503060610a00c0d004945082034016030070790b03614044401c0c081620841c1e410b5482c00d400001c004030041482c15002a00030700c92250420800010b44501c01c5401080c2e80110a515030f6110000140d980f01410f0207488080380c11703a0a2620405c0112919004001c0c000e800500034004105504600c8980055090a100d804d440c00080d40340b44900440708040e40c0b03d0601c1007441d005213000b01c0101528031090303403503007080c1c9610042d56a58107403013440c46942c00d0014000f000f005208000014000307007503000380c4611558034414445680030a802c242c510790080d5201890494041200c0d189580301c4089040c10040e503410707400c0101d19840070450500028400080040f0300b03d5040340c034100c050982214140e900d0340c070030405a01c070494059001e1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 971840089 1250 971838839 971838851
    0x601030b1f0f0906030605010e130e010f02180a050d11120a1104060e1902090301020405040617060709080a021e041a090604090c0b0901050f070b040c0b07080324041a04 74
    0x52442801040143c2c0c0f4181c4840034020003842c00d2009010803403850f41e00035a40c1e600444a08034003370155482c501025000580c40307110113498100c0c190100303485148203203040c0004001a84074500308003032281c4c010f410303500204441008125041101e54141d092806540400c01c10003204c03604c400303202c1401383c6007000450b4132068580002c0200f6586810070000080e0a00450026034006088064005d800136040654030b50116040c0d1b900e6130011140210300c1031030451081c0381042403d50040c06490300e200e105283c02c648a403209446c1070041e018544440d48813252200806410044610140040007084030f0b900785280840019040c00b031103940d0782e402241080c900341c0690300c060340c4c0141543c06824582503140391170390301c0400c0143c14084144001c480c01e003545030280420038042c0300d03050000c2c60107140007a140750b2150092001404148810004203a0241c29258008d4542048a001c2144103064042904661103229405414000400d5801156140441c20100265414821 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 971841339 1250 971840089 971840099
    0xb0a030501080d1407060b0f0604060302031806130602030402011b062322110415170a080904020a0c140c03120c191a0106030603110f090601030b1f0f09 67
    0x50100401c46413007181c0428400c000120301c0681c1701103241d02e07000b0302184201000001280700d41d08075500400202e9808010071001d0081d412568a42e080e003207015000742d203031515403040449800317138004c0c2280c0e60102c005030459004021500030245107a40740004050180f6010f0094281204840c886c2c84414514a03100341d0b091301d01074080c04581d0320510222150b142007145160390207800762179024044800368041d80f614485c2080c503082c140d4005150a0a00e050044050f013500201025540a02110303c04104a041a200b000f1030894016903030303040d40c1504840911294201400604040d03d000600340400544900800300640c151441150092100c81c80c90151888000711034208950740d481112000300141c140303c2c400c0c82144148007007100e803c0e40740c940903004540401d0341c440007441071084058180c5124007044856151090b407200c04641c022a003d404c0701d051685a800542565407035100150712441c0a01950301482500300700104902407410020011070511180482c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 971842589 1250 971841339 971841347
    0x3041502040b0a270504090602090904081e09130b010c060f0c090617010506160b010e070e090403020d110a05010f060e0f0103050303130f12021509010b030a0f03090b0a030501080d 79
    0x2d01a050100e1444d2418502000d10018000501044802035820455202d2a580b0052a680070314042c51080b41c440090940c3d13408081751030401e10f0040d010a000034101380c1c2e00c4a0100c0380c420341e107240128074215924016108000040030003803d4500b044003000100a040d80013a51103c4603a68041e401d65a1740403c0c1c82418000744480000211800103001500740302000b003a2000d00440e80038807002c610745034030500318000c3e0070812104001006010100340d00c035021800c0271208441c030210320309040d031b40a543c1c0d803103d41c0f0030014408401503008925805105200d0400d070803100030301842035800e0011004161a00800c0345c04c1d403281c00030810520402d10047d060740c1e8132500440c515150078a601180b0000c41404680201da0240e0450004601311004c50b0804100d40061041c50788141c540750011000a03c01d0101da0b00d00381c0511416030300060443c401f40d803c510480b10b009e04504003141c03141c105070000c1448070030004000c045254550710643c12030300c4207410355054101c4007000712 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 971843839 1250 971842589 971842637
    0x40f1110020124080c0607020303130314120901050304110111010c03141006081506070204020403080c06061009060503272404030527090106020c01030b0d0308010b03041502040b0a 79
    0x344503a40a51703628001e0341090002012000e00050450741401118415a140135200d500308540c01d42500003900403c1c40100503000700c455208a0035410712004000080c083e01000b4009480360b2a660300b08072281c2d0180d8041c0040f00c400400030f00c0040c0c10100043e0180420003568000c0181010010302e213a4011103542c01911659610704000b915980f140400d104d01c00041654810f8041150000580e00d41c40100b00039445000d1254032541c000d5201c42c2000030041c80680204a41c0c11051626980407100c036094410307605001c0d449131185107042014142e115640801c03240e01d01c920b441d044a000405041480201140e0180c0121402c2c01791840750b0141d5006011840502c4990f10400741c10b046850746484001d4100c100300d914100040d000002a408800541c000d000c2010355541c0c580034002c180001603845442091603a03a00502c1408148282000c80001001041c1000781c44001507841c6841118299140c50322500d201c1c029900003010500400d5039050f1489946807010010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 971845089 1250 971843839 971843849
    0x203040f140307350d0204231c050d0f050f130510051315020c0306010609061d030c010809030c0d02152a0d110f0304060c02060f040f1110020124 64
    0x2d204240520241004e41010581c461215002d120101e4014000c00c0219070b002c011500310128042440107000c2d40842c0c209980c00308104408041e00802c07400032f136404000d1201c0c507045520300c000ca03000f22801c2c0100815406856400100c9040741d4041c1c00340d03030701555809c4602c904040080c0700182d5452141c1040d400718440c030080100107284003409400c0509034240191170455031444002824a4002d800c40c101003800640f090180941c081000556859000310f406465082400040e94072000d428101d410400034800181c6012000c2c03041c0d40301e00281d00e04a4071504d0280c20040d4903441103034240075605140740000307000c0c400c02d440300100901741c4c3d00e03490b4200d5501241900203a0700c100b03041469180c4410600d190b16803410000c00009242e09040d40c0c0768285441c1000c140e505191601046604c8842031008414000800540007640001a000900030514107c0214031501e0001b5503c14810190003400c9501900000b40410f80707c42203240c07050a2600100d1498480c0c094 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 971846339 1250 971845089 971845163
    0x61a031005032b05070506040b07020c010509090109150506040b12060a230301021e0d0609090b190912170619031709281a0d0203040f140307 62
    0x1403011401d8440c2c08030b00d41d9003524501383d8a4450a612024981002524115000441401000717490b603414405118050000d10300f6618001521001520051041c00750851003a6540d00d5003403145038062420340107140280200751515030350b01040301103800001c654240300c0a000c00007551442c0491050303090354158038004c41c03510050510300100150014400f83c05640c05c000c44040c003a6400c80242c41c00030f881c1902079441030601c40d49005d0380d1742a88a180380b282084003403800106280800780c0e0103a041c0c1c03c2807000682810020000c1c10300c0802c00780410941c9034040c0100c1d540410740c808000d450b1304440310b031a1900c00500142030907a141500002c1e0303240b0000c2c00010039140b00c0801c005441d050242c10901044006551444141c0d1411340f100000401030210301a41c020716001011244002d4402200c010b5161b0b03000c0c8580b039003501800d81d002002508110b040580060b0b510b0300311101040450150100c25525403003007905540d0580030000041c00404010b2200f2854000291 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 971847589 1250 971846339 971846383
    0x1b011b080901140c040b0a0c0534150516060c030203060f0a030525080601081e0105060307030f020310140603010b1509091e0f10060f0f050d061a03100503 68
    0x1b60300c42c40d0f04040070ba20100409440c440700407600400070b8441c2c2c0f402c9060105580006030001d134210301100f821900714005404400c1182c2c071400d4441e215101d5480c1050b59981c0c07403041d007050313202100b40d000420181c98401c0d139010322035059000d0f5102e09030644076140304014100c2000070711080b5200c000c00990003030101c1d14031901c01c10010070310803104103080b0070003a0b02e4586160070030310f0907080315100d0f52151141800405003030700c4400482c25080000c01c46030615101180c1c9400c002d000103409a08200550340031500c04110010801207000010030002e0304460b075198100b10305440c1203119608003000d20b601c603e0662038240d817929409501d00d01d41b0070b048081c8500d040300200070498402075446070003034400c01e01382c1c0548a219034601402d103e151440200e550810030750041700400008080c03c0440a0704580b0742151035249040a5032526100e801c0d04018118a400440c022222084114031103111100514000c0304032280c41028a40c440050541d40c0881404441c03508207082 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 971848839 1250 971847589 971847599
    0x1050a0e210d1d0a06151203050a050f031524090f03031309050403021e032a1f0c1b1101020c1509150307051b011b080901140c04 57
    0x4002400302820341c0d0300100c1c03035021101c9403c12003059070a032040306802210b0310030300b001030350f200e420f4907440360442c0e101426040c0040c040504440e4079009060100015000f0211b50003482910f02c1d200314003a000d6070328030306010320308181c81c040c0c0a018040c0c12021070b00442e400e0400c5410a034030850450060400314490200a0241c0c600341185815010070051400c983c0d03015000c91010b090070103004030705410103203030081c5001328519180c14011030050742e042d2500d001104503582d1540c809854100c0c80d031000203800503214034081203690f40c807800282c1061142e0030b1809103005007001030b0801c020b120b00c0740c0c01d4580c28040e4403920040180c1c00041d00015070384103900302ea03800061040780c01c260115404100862031015207403410340b00204807140e09191246020f680c121041030b5060031404c19280c050001d0180c81c101201c00b118052088983d03940c25404211001c000444405043c102c0c000d0140140f20195481000d035401c0c201ca518020760b9254109008500040700c03245801e10b00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 971850089 1250 971848839 971848903
    0x1507050a0822050a0b060d020d020d2a050a0e0106050901140c0a0b0a050a06061b0501150f17160603020c0a0b09010203070e120c04050603070b070501050a0e 69
    0x2041440c01e02c2a050800001d6003449160103040b0b84500e0040400032054244007240c02d8009101e24441c1200300030102c0180c81d51003040b09190f030305a40d000002009407800c02c110490700c11240480d040002800c0c030000c1e6000c400d280444030260364808109464150000390008240a42004034100301300e10204c40d482151140d00b8959519856400c102000810906040e1045801e680204040c402e102c0c008130721748212380d00407030080d2007003007030300c0c81c140c40030309000511405405d18240c12808441444070a4114070000c104100f16805416118555683c800545000b5072800d0070003440280042c003400a03100d5100421070001c681c441d0700d420000c4001c0d5104100240d0140928009030340012502400907004907184800586c8070b11380710720002c108401100410388200030042d00316141450105044110301426140407815654150100713151460f2640200040500000c440c2e083c020190702443c01070060010604c6007910026840c2d07a2004000f0a0003e00d120382c2d104207803210350b5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 971851339 1250 971850089 971850091
    0x1050108060d080f03160f2007080109050a030206160203040902181309051c08060f010c05060a0902030607210e07090e0a020907182d090c021507050a08 67
    0x402c0003003034002d240e4480c00a900049001444c032603010051021580303104083c54000e00c200e151070b0701002d403110401820b02041103066100840010742030012107106000420241c22100c009008000c1c052030500d030743d410380d010140c0040c00303500c010401013806600214160419075001f181000d0a00b0300d414002e500c10304081968280c24402d03040075803203508895101901c5c43c1000103202c801c0703040803801e00700c04076144441c0d00d1000381c5000301c65401c40880c1b90040c17020b45040001c24110b5005980034402854054140c1c81070100b0809003080b1500304004041c800e605036001d03900d0b0108156032894506208907502c6e5000d101d00c2503c143c0b981d0241c1c45c042031050840f01d485546202c0042107400c0c030320100b141e5400583c030039420740c10440d034030a0304a54a860008002203640008045018884c02403500504c80b040030814095140c106140094001d1805c400d4400d0742c3c0d404c210018500702c803c1901500580389100c1100b201400150303c180c40b82c1d00c91520317102c51500104d84500e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 971852589 1250 971851339 971851351
    0x10c020d1412070f080f0907030602090303040515041505030c03070e012106080c0f0a0e07090e130303050a0b031e03120103030f080c0a02070522090507141801050108 73
    0x220500601810b40c901d54803480c007800080d150540511009440207000010040840000d05407000621604407000190441180d07009040142c481c4000e9000031304520440c0d006036400301c0e011043c0c40c08480048010011103500c5a01651110345003201070302c403804200c070b0291000c0c0051000400e103501442d002c84810ba07052400b842d140300d201404184681c00d42c1e0f072002400b681c4120a0044820402c0034501402d4112540d160050702d910001d03c58900e030740509840c881851010404160140000380c01504850f803004000b8907110310b181782e5112030710b0004c0d40000d00301400301e03c000d00a44034030720400300d02801410040c40c007440c110312001505c15003141c492204100e20000307a204100d41700d02940c070903602c0500f101d4003010001c2101030045d02c00c841c180ba0401a0300c1b4015000114241180c0307080d180307190409140ca129034901281058519030141c00c0202c50810410081015425683c0220b2902c04240d00d180038007401c900e6041544042d603100c000184210340c00b405805074841703 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 971853839 1250 971852589 971852627
    0x304090b040905062805150d170304050a150213030602180d080901020f060906010e1b0c0c0a120b180111130608180d0c0c1707090509010c020d 63
    0x141d60388451600d20304a404a00034070445c0300c081c42905400c1507415107844600da0500450406084004500c1d9214500740e2292101e80512002c100c28622140c803545000c46a0720b4591401e8140356032617165030602240c00c03403c1602d5140c4c2d01e00c020f2003618120482c0c07491504a60b0b08680d10040254441c0d45022b011080807840c112803969504040920350b40320304144c0c0c3d10740291300f001914281841c0c1010285030448001c000341e002c030000f400703411568006400324640c1c9070450740403124044500ca10052100028500b6481540000c1c424500d08c0c003600c00ca4883caa880b24100360030742c40744000070b20204c611404034400700d481101203158120078200009070404480c3c0c80c3c0c10964001701c402c0d000d5510350002004840d810845c5198014656003007400c80202c9004182d80b11508000c1101c01c1c071400340424028410020024405007868801c454891690b135080243e48000921482d2001070401d000100344c00300c107006a182005041c3c000348820f0369008030944810f2070b8031000f06641 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 971855089 1250 971853839 971853851
    0xb16030309080904151d0402060711040b0a0801090b06010809030d0203150904050a03030c17040204090f0606080f100b032107060c0507140a170a020703080406030204180507020304090b04 82
    0x156961340b02e2105c032025403103510700c1700900e4602a600b188030760302c5044c0d031074410315010007000d41c46640840e200d043d448070400a001e03c840e40024001c0c1b002101c440d4010704460008030343c0600540c000a03005001c0c0c10700401135038590004403041802203401c0b560540003031041d42001a102c2c1c0245400c6901c2000e05c1c140c2048a60101b03c0401c0c0440741038031164410302d00e40b000d0540501c101d60b500000c038a04901c06007102d1343e080130f1111001d040240500c0d510f019440c18007495101118071941d024038240015070790b40c1c59003590b4113520300c01503140c0c0c0661055641e0104080c0b1501031021000380203028020300e610f0000d070707110750005008503c10307004014000000d0304503c00c1c0500c8000c0f90700d58a48503503c03801c0844c2442e0100c502c641e420b81c0044401c5002c56280c04003103000458000a0640d5103200c406c04a0920301103503c001d20f4910041004110140c145d005001070700c0c40ca1040407848140030442d003050700c0c0251034120150308200010701944480d030300102d0041c40003820100744 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 971856339 1250 971855089 971855107
    0x1419032621180a0c1503110c011b0804020f090c0702040e0c030c03060609070f020a1205040905010504180b060d0506041211032502040221011403010c20070815010f0b1603030908 78
    0x629482030508140c140d6490030350403112512b03408000f0b800708207454000f00780c1c0b40075400300703101103c20791403207124005880010740c82c1000e010880d070b5000d5003e8400c0c800c1120840c8500d40d103955541c0b00c035100c4d00440212110078100040c0b07203449440010100d0003d912040c0c0140e0706042c0d00700c004070460103494524000301e03040b2904103820315400d0366602c0c3c2d80c0b440c019400045a0040c0c004d20304c960b00780480b5120f0b040030f00c00540380a54101481400b5921a800000c6050300301d4903004105010f25010082032009440041d0455140780e2100c21601e10507070300b0030b9105c0c030416804100c1c840c00240886010a00d8240b45504030b031000d40010718205055907040c15805800c2d003800c428001c440c0c01401001c2485080f121300040540081c0102d020044020380f91071680d03d000c00c4048920555600b079044100702c0c08008241802c251010000c0c410f059100c0d110003401000000403043c000000c01846440c1140d0f4280f01000381403040e2051a0ba040380078001c98030302500c045d1000d00c001d000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 971857589 1250 971856339 971856371
    0x2011d010e0d050615090720160314060c090d030f170a05060307080c0616020f060a0503250e010f0c0602041419032621180a0c1503 58
    0x240d2809100101030031310b4074030410481d04820031203090250081806100c881500240008440c248a19a40e18405030032303100f0519100580c001a182da0030b902030000300f0312078030500404183c4650f005991443c1d07554140e500d0316205984c81640c01090f20300201c5c020a10410710f65030f04684618003606600f1b0103499070350101c8000e03601003080c207541d4005d00080b481c04000c030000903c0d195000d400b103100300000146860281c94010080441d02e114000c045548402034002700900c01070526845003401e031070050954000f01d031034010100902282c000da204118540302c02c00111503451440040140004480f181d052401d04000d0081c18001c4100141d81070020313101800d80e2401100c0c001c0944d800308000540440355503419088501d6090001c610710400324000c2c02030b14079104918000302c92100d02548a09030001d0b001e003000940f024000c040c0028041e000b407000341c00b100401d0001c10100c030380b5800d00003001000c0851841041000c807480c52060819803040b800c0c0040c81000a0102d0300c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 971858839 1250 971857589 971857609
    0x60b070308010608070e030d140c0a03020a02090c070b0a180606140a060518090910050a090614060a0603050c071403190f020307022101023402011d010e 67
    0x30040340c1400010b000700750f4440c580c0e0394031011324684070b5101054107000c02c1e280d01c0300e11100c00c100843c100c440d1641c003c124003240d4210030303130308100c03511007556043c025112510250200d00c603400305000f0401d0b0303000c20380503106541c1d009503411a04c1c1d1143c0301c40310000d0660414146a1390b10040c085800b2404038880e03540100400d0405904d5408540e080061807240d41d0000814000700f88150b20a5000300c1494400c02c007000d40b01040152944017040d40341c40c0300d49035004410780c10002000740c01c0307050b60030091040f071103460188144131810059140c1000c0031210660443d402031020421982320790009a0000200d0285a11701703806501c0702d00c010b80980719213151503840000c000000c644480c500800b400344925200840f40e9040d50025268424044042d10550341c5001003030454001441c6050b010040e00000c543d1611048500543d007001801406008010b484140a45500700ca5111050aa0594403c001e0361400f0030400000070110034000d042088100000c03107552100c030100c2d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 971860089 1250 971858839 971858843
    0xb220b0a0b03040f11011805040b01020a08031e0a0e0a030804031e0c05120403170c010f0f15080105190e12030f0412020109020604230a090606030b0a0b0913060b07 72
    0x1940d044201070174808070607600303881564108403200220082d42c001d0b80c1608019034800319004103a0742030000040b494410b0f980400b91003044c001040c4511100c1d05904061541c0010511050550b2600340e42400c44580d1101441541c01500707000c0d000901c00d994880e0b00c075100b81003007010ac20342941480c5058195400000100e007041c260710b0280901001400c6480d460004520f162a045646d12810b0032001c41641440a8012400000d040820b401c09a4006000700c3d0400c000062200164058040700c0c02c0c4004a8207451004145510103008507880340035448140401650b08061110043c58440d145400a01940c5400300c401a2008025400717407059142e4150281000d06000c0400c3d83c80c800f617003040d68580020034006880350820380341111a4680d40011413200c0c0c508900746141f5011216502c01d0011030302080c8050250702101c01d6480982d020001505202d040c840300d8500750007980709040090141404038503200d8010441c440c1003c8020901079624002010a0741004d141 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 971861339 1250 971860089 971860103
    0x40e010b0d0e160f0e092808120402090f0c1e0d2f12161e050c0d080c1801090e15130b01140d0921030b220b0a0b0304 52
    0x104010000ea101e081340c01070003240c80307060b40b43c0c2080c06032141d89440c100c14203010070161541d5500e40c801d003080c2503005150007031805903440180240d05100342030226000c034403c617001313000301e50300c0350303006a140740b01d1a0501942c80c070306801105104401d50b019407015145d00f0003042031040046840c0141d0705250a800100500c1c4000c01802500c406108201038203055818002038035100d09000c900364011a00758001e008241d403403001104d59030715402900c0c1c80d4560845c881c00b0440d51183c020042c18a101c802c0c0d80706407221140880d0000d0041e03031110880704090041a0b001076109406185c5030205042095419a40700e00c41c40003160100c4035108019081810b02c03106060200002445030b240340c40801901c5c0e94003001a1080e00c04035000c501180000c40c1d940030400c965402030000b140c0000e20340720303502d26000c81c03c05403509000024000a00b480201c0c5414104500f0800d4260304412000c3c0488000c04458070041c1102d580c43c9500c411280e038001110000d10000318052406640 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 971862589 1250 971861339 971861383
    0x30105031c050d0504080c031201030203060601230d020c07060c0606090c0c03110f07170705190905040c090c020f0606190e0c0712080f060105040e010b0d0e 69
    0x101410041e118200c03152580900e01d01c01d0300558840700f00c9010704000040012541c4440c103003590207029122805140780f00c0010038403c0050001c3d03a0f03034102c1e4400c0b02103400c1542c6400045440409000c0d80b402e01080d00302aa1744182d804401528000ca482880103081c1a907070740b0343c01d25002e555401040445e4002c1501c400741b10b980e0148001034048035009201030b4008550082c082a0b440b84007404000200142071078051041c042142c51024110803207040d2034494001081d040c0f20f03080041c0062245150001e043d0030051030304101c01e07100d402d010080b149000d800b0700140070001c0080f200340000600c0490502c0c118810350051070388582c0280699207081340901d01d02100500740b140300e00c52025070b4004400209042c10180ca8480241032413642385d0148203c004d02649500400076120401c41402e104d51100281c0e10504c4003650311540d54a661005488031b2240e03000700b4030000320807401481034a4841c0c0050200c001c5038400091860101d1100c02e0508003030041014140c20300c11 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 971863839 1250 971862589 971862599
    0x910140708010902030106080601083c0f0402010503130525060810150c0c0b0a03091a0910020901021c031d03090a140a0b0d0f0e06090c0118030204020f0301 69
    0x700c25003d000a5002103143d941843c1c40a00a1800103100303c1c1041900c400007001000e080d582881c152031a6090501c01c5805542c088202001e00d080002c1c00c88050720025001c15407507030626005e180c0603110645161210590700300786000c02c0d10140c03a00c0c0304000c00030201004015502d48900c000169606880c0d04115004004040191603070101d400486030030f10080041c2a07440400b8902810166000c1411b0301c4c05209054403a4030120700311a000c29000c09094140d00b02071100303849001120080c4090b13004143c407421003540c00000c035900015640040c050b4950051101460500448040104004030948040684078450700003d07101c120b0540685030321a1440070303109500d4091810314000b900411a0060284140c0d00c1004a90180c2e802d0354444c0c52810740600000312929660350040950070010f8141c0c1405440003a00e03101c0c0d0f0365524400807540600403070a203000780426201580046401402c8a010000c8503468448004010395030703032000300300000d001c03011251650325007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 971865089 1250 971863839 971863847
    0x308040e040b06010201230a0f020301080d172a040305010c17101a0d1517100605010e10030e0f0a0b060f01050d0c0306050d060902040605240309101407 67
    0x5014141175a040c046c42c2e006803001500b440701e428001c003181c2c030450380d80e031525440540035050310503410510000010420450109659004142e41d80b20013407428000240113048400440c1c1e581501000f400303159946600a154085c840c0301196401c170304107926a01c94a085070340c02c920783c0d07020541d0440f100e041400c03800903a03640500d00c00e019100c3c4034a08038401e99110100003903000003000000c1c4c40714a411659000e000e05115003a8003105440d110440c0058151a20317102a016101d00d020102001c0c40c1070240c042900c2c2c060751816501c014803028001035850303106145017410b031034001c0659030203010402050046983c2c001400e90a6050501c9100d4030301c0941400d00840b140f400d024440d036085421143c400030941000141090200802c800801c0c103500306680c0003100c2d81c844400d100e459001000103a008035803c01200350f4070390400080d000146004800c082025104008001e2800e0165600911070000d84000421b5460740748100c03249041640d01342420401841819584 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 971866339 1250 971865089 971865091
    0x50a080c0111030c030a0c020a0f0303081906050f0409030201110a0e183303061003060506030703030905010c03051b1c0f050d111e031b070b0106180308040e040b 71
    0x40302c0c020314941840040615120301c00c01c8084020b002000d081c0b0421034641144000c0141002031070b4041160712403130000c201e4a0165600c00f640441e402407003a10000510131081254002001185010b000c2d405101c0545034036081a82955130303990000b80c044121100400c0300c0e203030366030302c80e4081038441c410403070300f40162051006910041c0041059490843d507200040041181802140c40e0b500d9205107541d550401c5001d403d405007005000d00004881c07040c4007903d00c40d450502c84c903520f1605066840e91a072001500003040c4580030009035000fa144040418001d1802c18a040b110040c5140a146459100b003041d50003501403505201ca403c428066506d01c0d80781c890040d050010008105010f568544900590385058000510fa041000c5035207840644060846803110cc0d08820003030340003141c4200040d00400500c01c0d01095113801c4444040e40001c01c8940340e4242401140c2000f0408001d0017412400c41022020500c42c00203070009004103c0c0d4019246081e240011031444 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 971867589 1250 971866339 971866367
    0x60203030402061e04030501110a090608071e03020408011503110306240f09091501050a12120207180b010e120c0f01030b04091b06180b070c050a080c01 67
    0x34424000180c2c0e42c0411100c150181c0007540340c0b0301d8503100f039460991203690f03c000e20a40c40e1100700380c1c1c021240300c05851307103280644802c0c0c0035940e90101540c9488007101c1c41000192140c465001b2002c2c0700c00c1d201c400c402e451030014180342d201c040c150b007118800ba08032101d00ca11030b8030810030410350840e0038864040540240000e41421070304250f8020042c3d05403884654048640200c5440e43c0c030485484580040c40c02e0b503182043d842c010b4447d401001d88513051142c510001c59035040540140c422039009149040322020706480d044d070700001d072001590840c02507200008401c1d42d44520f56030184ac3c601c00008080d00f8200000d0108061890658020300c02e00560003500d42011484005035407040c1c80d0800340c0284113004800901c02c2c1d40c4e070ba660003032070102c0301d005008941c0d2041c1c0f950034102d02c410107402c0d1900c1068900d00080d030008661a100900144030380d0210b030303000d044040e00c64501807072441c1d2281c00141080b070381c40d0401a2a50711000078030320a90ba005c1545aa065 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 971868839 1250 971867589 971867593
    0x503091002070f140f04051f06030c02030906090d05070f06020d091d070c0b09030409140c0301030f080d05072c010e1c0f0803040b0a0b240705010507180602 69
    0x91602d0403076240300015201c2d0625850f01c82402c040c16894548102e180450010b0040201d4503205051072540300e00040301701202000001c02007a0b09d4000d10808241c1d448a800071401c281c01802004040e5204c48500d6800a0044207000002002001881c0107055207038540d0503600e0034018001c3c82c25500c1c504010400501312420020744c00b5000021031580e1300d40600021a43d94542e0641e2100c5041e58000c01d03030043e510801c01072200c08005030056900d800428441c41c000d0501000181e80d00740c507019000b1400b00010400100003140000c29140700700000d904000c07003045c0711011140112040700108a158040c1c030030507030f50320643ea00b100e8180d0035101420301024000034101b441520300540916103c0100d81940c15501c03c0120905034082c81c052841a00361070b002059800075602154103c061030003103030740034a40b1300445111644c0501a07161164096010845c02200c1d400b0a0110700810016000441c0e03081c011030344540f100d41c0b15200d90300100c01c01c42102c1c1040f94044030441d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 971870089 1250 971868839 971868853
    0x506280612140105010b1c1404030f17040c0909050a050d090501080f160e0102010b0a0305010b0103050c0301030b04020d06110c010605030c0a181d1507090e010602030304060c09050d0503091002 85
    0x70b4090f54140c8241409208103082e016601047c0000202080c5100090344040755040000f015031280b40c0010361525581e869080e865600e40252468030180c0c0c004041010108050290301e159900000e5030600503001c4901350a0303684c50700c0f402c1074060301201000800002d010302065070080d21203508880c00c8a13592011303262034090410589481c80100c0d0800c40340400051a0ba80b01750881d00c061b640c002c003150f40301c0781d8a160a034003c1c0510b40145000c00d0400340019510444ca074291f034120707608200c0e03003925592950b003003180908500c1d5080325001c2d81c401040d92400014405042000100c000014116080c40100343c50821015402489804298000e00203002e0727003080c0b0f0782c004003103c40100340c0d034148400340442420b002c00c1482c014803c58842c0b0b203101c090300611a0040b81c2903101d14055584880051104120900074071015900c10000304001034103179881040c01d120180343c40c89900f9194000a55014001031080c0c510350300206002460f40380041d81c0b00c80d940f120380020044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 971871339 1250 971870089 971870099
    0xa0b0d0515011b021215010f060206010303050a14042601060806070509042708040e0108010207030f1206082e050402220e120703030c0c050628061214010501 69
    0x1c6103500c00380380d24800020080c280c0442d1608200c002e0b240385d462042d12884000001e5007a12144c00b407040e6040e100e5611000143c450020403190b050305d401d0395507a450007403030807015a212414294000c1d02c00004010019440c1280c48010030780c848101d0f03490f000c1c50284102c09080d00c880347c00c100070940000090002654202c404c40c2e00091058034081501a40b041c03038003007070758080f00c08410b0388000f2511b40d500304040f1308014400d40d0081c0c980c180542e45c1f50b084950803400707990760090115500780c244100c003a004100010403030010000c085441900c902c14603050000c6010651015003c01c4240700c58001c0031402e8005c41044000104810316094001400c2006400b4048820706400b48440c14580c0e59034224a04071040c24044620341c1e0030394005000303241e001e0301e400d8000901c1c11100f803030002d1064005000542d0880010519a21030320884035510114a80c00c1c17032440c03110350440c4124005406828020a516010326404102600309420f2108884d10b83c00500d034036000050107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 971872589 1250 971871339 971871347
    0x110d03031d1204140a03141c09030b0420040f0507020d0c02060403080c1c0c020117100b0d0906140f13051c0c0506100503010c02070f03140c0a0b0d051501 68
    0x46030110788035007400c81284400b25000250321b40000c0c110119030f21070f94144020000d0b401041031140c22040e145448242c0080f20380754601c0c00018801e4034520086008078805070184144098203400503c1c56040f2440042e003217803410950101c0450300c2d2010005000d4040c03024030030b00d129606144a203500a43d000941600c2980070042003440c021402078003210341004218544c500b032010207101c1640101015051001c0c0710307001c9002a4030b041d10061040803001c2e103a8091400c5080c554040b5003095440180ca407c1115101819aa0f6035000d00200b01c1c640918005440000e01040712400c2c00640c40008600040c6112031716041070912400050700066004603e002c0f03030340802654214040110f0b902c0d801c211028026200d44800d1003066101e40440004984046008006450300217005a80340d40c454412110031039024103081001c070b16451808500f414442c0180c40600c030000c0c4c002817501c42c15030441300c925040171580ca8100030191003000e070042526050b0302816258500020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 971873839 1250 971872589 971872597
    0x905071712030c0906030a020408070b16060905030f0d27020108070f050412210305061e0a1a0301030303060e011a22090e150c070f110d03031d12 64
    0x401d5603070000001864000880054880891005001982c2d0b401c0811030a0080e4115005103112030140d140e001401940d02002c50304440d2840840c60500e0000340c98a1008124043d0300b17841c2030108001e4203007560208001840c0d80c034262180011680c0c0c92010454454024010804822000c0724448004d41c0c0c1000d1f0440e40100549842c80f04203101c1c0c5800c0703c2d00d0180e9480203a51004003460482041003038039800072200211440311502e0080d41c0001c900341e440030b44800750840840c10105c001c01000d455004200407010b0400161596251b400c07040c02c5801c44e199480031000400140201503050144034002e00d9103908414040d4106101d20450380d100344036056030508002003103041604103640c4491120f0180880e030604503980c0c0c01e550060119600c605029005a035080300780e9103150000c0c0b1b40200c04105285007803210555903c480720b0310000040e00c01c4170585040d02c0141d034034454542c451034032a5402040c02400d401d0004400c2d03407030031401e02150b000030103807401d0640307080259 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 971875089 1250 971873839 971873863
    0x9020a0e13240e03340203070303030b03150408090f0f060c010603050f0a11060304060f060b040620100b012715030c02122b14010b07110405180d020109050717 70
    0x10f0004181d00144140c45c1385203e51000303415004007031000080c541c06a000400e4008141c05583e1180050500c1a5a00c0011500204402d006102c0c0703ca160501180c0491520409032a900000400c88000340392030b000307914041003030ba4482c4014070030890b06004400c03c03611b176800141b5040d020f1303507240340303040e65900c13045402a04007100043c1402a2034002c1e44425502400421625868880e426100c0e40140642c8010845060243d0100f00c500c20950f120845032101410003076840211880c003501402142604104120f01c1c4d082d12070030f04406002804450003101e031030140c948512220719844c0385240e20140342c07400c07810072015600411403505203000c2580c8950b0301c41d2815904031800003113011301003e000e0301c0d400740380868001d0f41c09204c80c990310b040d40ea600303a030345c0d580300e071080344911a002003d401c10042500a182829000243c000c819041e02c4041d0300400452030746407c050202000c0181c1d103138168401400720510001c00038110000c107854001b0b500041855640d50310680c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 971876339 1250 971875089 971875147
    0xe0604080301051909090b1501020318040506010504030215090102010c050c0a0b04020a090c050c1902060d0509010609020304110a060206060105040512011b050d0b010309020a0e13240e03 82
    0x113040010026140d01c1010700050881042144220b04003021103090459a543d030010f1a4164074003950300000907107001c070002c1070200d4040085a02408082c100140101e814094103000c044010b98510328007643c0c19248080c840d8803400b007040024203580f154a4104184002004003003c11030700410075144c003a8200519200c030b616284046440c00049501850115203411072040c281d41e4000d001b0720850641101700c1303c1080d460070788900715415200b0004e60144080258940007075590b00500c1d1700030030000000688940c0d80140c02c040c1d80c0115001c850080c0e01190088061038450000d10242c00746100800c410700d054000038001d44268020740d44100541c4c15000788a40c001d41241c44054010188a142c8100e070040140064019401c16101642812092070265129119a4044540080650142620340005201e080c0d40160207104911342098612011801e40800c881c440d0a140312104400c2031000a401d0451301c00c0c29051080d0f4000300011004420f0440c201e43c0800d00d280342d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 971877589 1250 971876339 971876359
    0x60909071103030a09020a1703120a02040302030706050403032304170f1603140607050a05180d081305012c011701030f0611031902030c16150e060408030105 69
    0x10305841c406410944090a444000b042103007403681e41d00044407182c826100c400c0b8068a075411103d0b2035411501c010002c1d802401205041e6414140d142e0300075624120044c42c0980f04e4011034141341c42600080b01240c0c000508008241d41300d80901d1081e00c050f03d014411828029105202e1301c914810b0103100e00096030101960201407101e211601d409004a80000954802e542f440441a1006483c060280c00c240d049a4402082c09486024a0b5468600d00b0001c140280c0d00c40e0000107904503810448981a9813940790120140f111a018152881c0c03501c821034007075881d07129103401090400c50301768404515104814103107000b0501041c14412585002d800403100301045405545260103410000810310060200070380c0440d01400082c001d00c080c1c500f203180944000da1381c200d801e40150005003052042030f0701031034102c0c00c0018018034144030100c2c0728541181ca20400d40d0181640501002d1030441403248440c480c030132002418461506440307503040760005200340b0380101480c034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 971878839 1250 971877589 971877601
    0x6060a210617010b12030c2d030c16060302130308090d050601030b0403090906030b062209470618090c0f0609220b0301020a02030a1d060909 62
    0x50800c1c005420a02d203184116015103100c180a8030583c80302c1405400006100c10300c410380802242c0f100042d81f070085c4442e0344401d0311501110b8903001e0440c4c034181e1441da40400034100740024004100c40b9001081091860008907113400c9e10303907006006041c41044441265801000000c003200d41211500380c44844076008544542440203000342a40902400482008a103070240340c0074600995079410403030749a030550704c125403490002410080c411800a0a60b107001d02590380441413440c3c80002c401c9101515005407010b000341264404403c0c81204c10515000340000384100e0f261103121101c0720b80d011400700000008100e101400303007030310000b0032545030201452003c100b4242031004924240c66076585030319031000d64034400c015101345580706280180c20b80e41001c1000301000307003404003544c104c031483c061400704c22606a250308440400b03076000c3c4041c1c929000c15402440d0384180046005101c10443d5400d44149007912400352030503102c42d0140e40c0748460594625105071180 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 971880089 1250 971878839 971878841
    0x80a030f08102919170c0423030f0309031c08070c030c0b15040e0601080309040902190801050702060109020c07030b0c0d06090204080706020a02060a0305101d0f06060a21 75
    0x407036040c507445000040c408101495108090340c104c40d01e5940c020792865403012010014005480c1c04070b074240148030510900c08100441401c140900d42004100d44100c404a4140034082c2c038201481d400108007a181c0d4101806a114130200d044502041d6450710b90010340000005020881000441c9085504050051800c8144a0b800681140c03580c60704402c500031070312503500790030b0289050440c1c041c0b01000000b1880d0503649034601075030a0170004414080108007100d01a640000004803a40d145101a1803940103001d659001007400d00e80520702903e01503069020508840c81080030b4080c885002c100c04007500d50140c1c1c101d44a440f01107000c800f030b008240c0c00d100b031945481000100c040b03013a4010b0045528002c1542c2d016607a943c4243d0b16a04c04035001394008104100b0140302d01c0c400d51003254003014a603007001c0d83c581c940d040300014071300703042e102e0b030b0031042503011b1083c2da24594050560081c0100c9030301f80b51141b80340c8020a6a0f05148a03001c041314041c2814240d1521 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 971881339 1250 971880089 971880149
    0x30b0106141c0501060e040203091b180a050604050915040611040513060e0901110f0a21090b0112050307060506041b2f1b040b0901080a030f0810 64
    0x2900305000b030102c0e500c0040d0014442845000c2c0441d07100d42d200d070518203140c0240c030b00c9554548058299508403071485107800303041300c0034280d1007580c9070807203418500603040705401240000d0b00010140741000c140030071203e02615040050340000030b142c501207001d0030082c2e40075501072000710320039030811040310440c0155040541d20207218071030f4a100c21526880401220081116580c0684680044900304c40c0070041c03e104100e02040184440814100205040300c0d41e45401317039607003010101300d500340d40429401e810004d072640f241e45c0500481d2030030303a4054648216161680c41d22a600c0b01d0786c0c1d200c0c1c520000d00058541002650710344e0740340e210142903c210065902c0300d59441c02d008082c0449041c0c0385e0404400c41506008150b0034500040300403541200501062100000030b41a1580640b00141e201c1e0b10364600b16101e443d0041110300130304a5100a103c050050300d00540404403020400301048166010080318150340b1454030100c0321540d22016401081c1e040004203c41 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 971882589 1250 971881339 971881357
    0x632a0901032705161a0c030904110c1b18090106051315080307020f09040c05060f0901020d080f07030905120403120801080a12030506011214070e0a030b010614 70
    0x150902c0910b84040c6100c54840b2070600c034a00382c80e0f0222244107100d10583c803d00681c00d598600d071051600140c0224000d003164200b442c102d904080b0003e000805a44480b142c1294441021800c603494020402c0b0b1304030850302030342010982a4641021a98001e51003000700d000c80b5015020483e4032100b9480380005c1c1001610222291005600040281942100d02c2c0071007203201034001019a4040240d0301000e900170001d15501c001d501c10404000c8001c0c0080e210f4904014000a0658984004020b918040b0700807503103407240500068107103c00a4564414480c0b00c03820800d40301c00f01c16030507070320400d6403e00160148140c10f00354a000001f60041c8081c0781d0014000c4103200010443c64903001050340c81d1750584c1e072140107050300d890b04040020840040f9841d00c40080303000741c100a91000061501700344110741000910269451701c240309240b4481d20041c400501d5000711203120140040d21640c500314036540c1d65410f003507014072441f1f0401c581851803850000e82e030800c64040740 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 971883839 1250 971882589 971882621
    0x9083c0a02270906061905100f02190c0603110703140f0705010f05090105070c1709011e030c0f0509060403171309060e06632a090103 59
    0x215000f1400390ba00c500503202144aa00203500c403445440d6400c90601c160f800160402c208080f40c034005540c00e08060b98040254001ca09503d420348a00250082c20b40d8000e8441e08012490543d0140495007843c60500105074200400d002080d000300c4041d41c00303400d50469030f03509d200d5203559000354010054020095404d080c000014502250000c03400780010074000c00c00c5480310b680507260761540306070003003000d000300400040c0d40510202403e08440c043c14560601c000c01942902d080d2000f009d0500402c1c1e94902100310954000c5140d41e18044a0400750b1a02c182c9100142c2c070b0380250721000f003000d02c248108900030850748056500d141c005802c0f0000c000d8455400360007801c0580155420b480140300014200d11300356a0300c20803040b105402d5210f060320100d04d607840713900945940c0100508011829802450401c0c090300d150607024403240780f4990854198000e110260409402c0b0004460060720144240305182c0180113020003e40c0c0d0f05401d42c01a03001d02000501ca160f10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 971885089 1250 971883839 971883841
    0x714130f03020f010c030f11070e070203130519120f0803040b0103060c020a020d031b0206041401030e0c090f040606080a0c1d070e1009083c0a0227 65
    0x121018824041e03034030072a80d510180303065500440c2c244030440000350014100c0100c50040e540a99409414481c8000c03d80c0c2e02640c540c402040c0ba80400d91300c010059000040c0080c142401605a2024040c1228040d440041030202c010400d645030044484442040204804000e80d50300090645030788041c0160300ca02c0c0504108000020034442982c0060410811001061011134200d04d0756070300030514103e040858070120307a1101d40f04801000403020030716110160f551040504000c200d415205450078081900040603902503030f80400b840c0d80312400c0620070760f0303461703181d190f02000e586c0405281344c5d624203180028180c2680444082e02074003130641c0a00c130382c610b400401d032401c2280c0a1141e01040007910f00c141c2c000c4565100103084058141d0052030709501c8003000444514000f42c0380c90716034125900f4081d08520b010b01084c181980e214804280d81403c0709000c0394000c4d62000344400c90001511240017490017449180044258a006842c11040141c546000d518411341 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 971886339 1250 971885089 971885099
    0xb0906120316060c020706140f030a021b0c03240c0309070f08030306011d18060d02040e0d0207080607210f0c02010b01090b2a0715020d120b09071413 66
    0x1001c1d0012158010301406c46e0200790701e4003454039205c0040d24042070301d18001c50309100311a9500090100410300c2c0c5c00308144560112a4045021800c1c02c00d005810b0280900301007500e090280b0f0008a00c0c03111620411684260103c080780d400482102c02a07903d036545a100d904006803a003103203403810b11040b00814181300c0003010f1440342d4000e8a809102001c0b052a60b200c1e5030242c1d080c560b1100017051007551420b001e40205400a402031712016144c0b00603070000d070543c0e20b80c1181c400d060b8441c0702c0607940b00fa0b0410842d0b0051a01e000071700b0031400c107040c00402004209411130540c04062905000c03e03000781d804038402c0045181c08000210440c440240a07103421125580083d0440b0004100000700c1811256a48014901c20141c864070380c23842d003440001d0004103080c6000f1141e0004e840b0f10400d140c8070b030b0504141e010b410400b600d00005400e01c0b00c0450703040000c600d0031100c8505529040480c58000c01c841c103108400490040a049051141c00c414400c11f00300c042000030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 971887589 1250 971886339 971886341
    0x6040f21230423040b0a0806270d08061305010905101a040e06120d0203041d040c03030509122e1109010c0f0807030c02130b090612031606 61
    0x10302107600380304400c0c6801d1907540700744580c040c0d400783c140100d4600009a9080c1840341c810542c00d0f00240000c11036080b0200040d0520aa43d4400a1160800300402030b0102010401d014815050342c9030482c0d000c0800c03180c40d80c03246180405400e00c40118086407080c0d4070341d241d0040c0303284408400e000e9582c5074491640a84001d0700c0c0c5400c107402c8bc450118070b03000703c0fa0b40c1035041e4900412130341c1014544101000d13415130190442f5040305c0ca004202400400c1884240500c04140d0021984c5901d00405003c0782842000e074180708090f81000e000010300a21418421030340c1510308a03450301001000524180204400c0e040310f8801c101d441081400d017408961004000800c2d502d221104140281c0d00359448086800e00e1018200072110711580a0f40c1501c00c941d0141850b00c02d80c0b4401da070b503d04039a102070350940204030600005001c41c6041c0d5080c00d003614107000184818a6200d000c20400c10000c0c00312446040404020f83c0803030340c1001980e011415101e1740850351b50b51410090 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 971888839 1250 971887589 971887607
    0x50405040b010f021c0c020a031b09061215020c3c0c09040f0f050304260c100e0a030c05030d08070f0302090d150f05071106040f21 58
    0x2500650614420780300c0703580203640910303804080c3d4000e42281c19580509690050381d006018062040e807900781005a22003c90f032001440c400c0f40e01c12041c3d842185031050300101c80d03128260762400c00b6002d003c500c0411407400d00c69540030510108411490041c10040d0003044d0705c02d45144500da8806401841420000010703034051202074081c0c0154210341c003070b140300d040141101580303d594000c0396405c0ca6802d86520502461030740355803944a0b030300e07030707282c02c10001d41139407541d102080520032100a02c6800c07458891520920314030700d01c00024036131070340d2003c20307120b00c00e50064084140c19801102d0b03c48591100500550449440345009043c608441c06060b0080c4611186d10036034034022402c0902074a030035242e20100382d0300d03080220041d43c01110440c0e002101c4c010700200049010074082c10090345040003040318400700c13403250101e48004011004200c080705e182c0c0640480840c0907900982c00519171501c905ca6801c1a922034100341d080068802c1503500c0f0200c1841c0d200e4101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 971890089 1250 971888839 971888849
    0x70609150b0f0105070210050c070e07020c01110a0201030f060f0807031a09070311220506130605010912050115060c050c04050c090415080f030c0c03010917030c040302040c0504 78
    0x4001e00281d420501010a442c07410b100e020680402806015107800030003012008010700d81540f078005081c400e07a0410825522494031001c1c01d4060100c00c50f018000c1e1807400c0400e00c3d0541c680f101011030355a0700c074000300010b414155a00c40d0012942e1981e0003150180144440d28070340183d48a5003143e070b41d2094401902d210b00e8550450240000d4214114010300308040182030341400e58460b5442094410303221030780a011340589031040162818201c13002c40c100e80c00041c0a1411101740518650005101c2a590f45030040902c04c50f0380240c1204c1c1510000c058040d00d1130030b94907255006254220040c00b114040a41c005007560384401c5202d60342e0700c00d50546402c580000c00380b20a40c0c0060302c070400c18490510076040039050941c40200e020401440c0c156815075680d030b84908040f45000003081c80d8000050800310303e50b0422190951500a4008000c00300490303c4443c2c1310400031058100300c00e000008652960b010b40e003503c4c041e5400800400030380c40c0c401c1d40644194001d12030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 971891339 1250 971890089 971890091
    0x60b060a051b012c070b1303080a0210060608010303080901110a0c080c03070627050a0204020f1902030c0123010303030c1214060a0b0a021209010c0c12030e03031306080c07060915 79
    0x3000c94040c0e401000e407100030f034087c03a4007170340141542d44004058012215000451140300000403000c0b8143c01400e00901d40c45d100e000d00d95042d424001c2100200401d4110705038100f880103100f2007140d80888218001c0341ca003401d003000282c40c124440f0300c9200304680d001e200c08114901880701540c8083c1d008802007411703e40c0302c0c880f4044035403840403c9402810f1a041005420f000d4102034000b054004904009030745041203203003041c2c82c0301107003072500c400580c4040b1f88101d03020002d2007590301e441017503c136401080b5004522294814014040101010346808038884884e0150700c3d112002030707000c03205004c0e10045083e5000050781c2202d0252041030f8110b400142041600c0858024508a0b0301501c06060700410403007060340302003206030400401e0b001d80c20100314298000c101071300020b48142980551401d0090025520220b00d40c8260804c0058440e001d6424030050202d800c941802e90840c0d807000110740d9a8045d05802400c405d06240010080003201d007403107500c010500e00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 971892589 1250 971891339 971891353
    0x4020f0d0b030d0906080a020403051b03061003051222090c0e0f0306070e120312090c01030b060417101a03070e010b0d0e01180f060b060a051b012c 65
    0x4060343e4485890f80400810b4036048240600da101724031499102403a4403000d45003a60360381c0d45a1508040348800f8021140101000032140790601031560007603c0206500380c21804c40c0c031031301d4030303000740d03507032038104a80e0004814070b01012040388480c80e160f0301004c4c08540c0e6034802240000e00702d00054200002c000b5021807105142014001099900280c020502e83e901c8000a4030f400120340c0b4400c4e8007109440c0311140b1420100010010680864800030160a000d280640303404c3c200b04129041c182801c00e1840f0546904059400b141e00d81c0316940700040e8144003490510101e1052070100030300b09041c030402d40c858200c51513260002a400c071a0000e968a144042d069003c1c050700306441002c004440b0541c3c641e40141c1d032005581000050600c4513880d010707482d00f46140c0c00702e40c02003125507800d0900c1035a11a0340c2001905942c0f89103000c8030700100410702c2c454003a00e1081601d40c0c00000c0c030b0080095101c801c10080c00d1108043e403442c0c000403030030210784d02411030b14207201d405 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 971893839 1250 971892589 971892611
    0xe0702100501031a0a0f0509010b01030f0908071218061e0207320307030c051c02100c031709060121050307120215010e252c04020f0d 59
    0x841001d0481e504a484050483e61918130801d8081e00034181314412a100d1103902d14140c140e100ba40e000715090300c000111100e80d2800901900e02ca41103000f5101d00e001c40c0e240c04a29001c041f034503020380c03102e031039920302c90403a4041e10b0701d444800900b02407259940020038281d402c461441890240d02c2440c56240c0c4100000306d03520401e50094070f0403050096651104514444205c1c10340c01d01c00201610011032120100f49000101c1d8000d0319220041d038000c00060a0002043c075440300401500c04a1802d541c02061112140c0c4000c4d03410003944045450626200b12030041000d0490581e8006a0400710003880e0f90380801c0c040d510405d0b24035010881100348400c0a1241564010302840c2070000940b04d42688141410001080d8010403100400c2c41200b80e9205029104c000c2183d0382a040140250b40700300e0b0841c0240b0b54003a14031094034480c54006141c4a154507041200404800340781c0300e160f030200c0c000e919032a082400414502d20110803c00580140500c040d41040b0a083c0b103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 971895089 1250 971893839 971893841
    0x18050105010f3b0603120c0604060b091006050702040e0a0f1103010902030c090a0b1003240315050601050904020c010e0c06130905070e100c05071e050108090a05070e070210 76
    0x14040c00d500c2d803403c5014007500d100c1c0c16110769445080203046d076070801801e6481c2c031260380c48101d2065070b0f038000c0020003041004074890b11070f2002c41518803600600d051a000d020100041c040c4609000c1c020800750115900c64000704003903101100fea91040409182c0b074070382c07203195a00031181844464884256420705104045403160001c00820325044c0038400c0c803501c89030180c080c02c2801e4403442c00904944481404132801001c599002a40c40808165012205002c0b101c0003d0b2480d6804108003003140440220034a61050000041c545c0b03a00005a030584124984280c0060002c1035101c400d0f4019842140100c2e028016580e03214440c108003c440e12840142e55100c0303034910f030240710380f114a42c8400d82c0901c1d242801c62200c1203510000e902c500c031241881e8009091200b440c0308109082c0520002041101484030000c0c004115102c0c0c0500c05008090400c0450710000c0c1d50034408200000a882d00042038801407a102c000145502c0401c450020251080c07490015000700c2c1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 971896339 1250 971895089 971895149
    0x211d010f1a0d02191205071a0315122109130b03030f160203030d051f03050d050708070c080304080607020303100905070e030f0706030b0d0b01060318050105010f 71
    0x100382c10a00c050940c20041942c00d07140030006000400c03000401c84141d060026110b080c0a00d00815002c3d1a2044403c041510004c00345a2201c0a1003802090750520b080e070010100d00b126601c98070f00c1803c4545250040481202c407071004640b100c804000c2e00000181100c58095441749908042d4050f84016075041e507014941550080002ca9203038407006d805030050b005c1001071825801c1c1c0c2da400181c41d41d04611100b03095256540d0502c00d0b90168122428126080e0100100b03d091440c0c4130a43c44012907034101c0c0078400001a28000c200e01441140c1e061903101c00d4080301d0700c0d143d01c0f81395070b01c0d080350180d03403014070580020510060000041c1c074804c0350031081d81e0032a9070900c40000c5c0034000c0985a502480402c0264140c1d40e42c082c00410360450004004058007481e15400905072107000b0b011311701070714907036041d4004a11000402810f447c481d04010401d0b80e40d00304408482050310a000e0810751900c00003041d580b2500d4400821540c401810544109080014035074440c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 971897589 1250 971896339 971896391
    0x12030609061a090d08070b010305031b1603020915060301030c080105070c0f06200309060f070e01120203060a170c030d0305130b06060f131508010303211d010f 70
    0x1803046042c5441c1c6221445502441703801c82c2c5003441c095540f18592030b0000e03042160140c002250030582d141840d40c1e000c1203100c0760030040c140e141012060400785403460001070300a60402000aa1280890841c00440c82d0f0141c80195a50707907a0910f020311194034000c54296500f402c02040b440b912454112900a4100c04001c2940542d9550100102074940160a200008049030310409d030810000d1031046881c2ea0142c00103107840d080d90454400c00611440510180c0c4404600d56640002c00707240c41407050343c0059a07600d80c4400589048a01c0d40440010044010f0440612402080d659070104003070b4202c0d240003200c48415015504202ca0b40030000800150610101d405040440d0304010003400c40ca280034130f0300348452201c0c2d0007084072110423020300c941000003c4510204560700303e440d2601c00529410350750024061804036812001001e9200c00c0700e4803400056101640190b031080a11252410320300560b4040c000004410360344030f01e002082681281444d01d0342036400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 971898839 1250 971897589 971897639
    0x429060310140a0f1107061401050303030c0a0c0c0f03140d020a1101030209042012010801020930011a01110a030f050d0b0301090302420406091203060906 68
    0x150f1002d002c0c100608520598096a9495461440310075800e400202034a50041f08042101c07407a24000c011f00200603400103000c0d40c010000c01042d4000f92050701c80d203118501e014a54060780d41480390010200d90001c00b0450b001d58400410400312121107008004101b0613101200100c05003a030b01d8612410000d40241d04080d0140d19a600c00e034010318441d03500420001b50101201e0600381021018a502001c861000540380c0c072010000341010b0040002000a6185c160440e02103183d503410045c00325032038007580901c02c5101c01b030744441d0301c0d071010888020010100b0300400d48010301014240c3c0ca000c500c0c84000f000040c18086007245100f50551940c198140c0708000c2152694050005016207664030708103440c850364280103c280303042c029402000380c0c0800c1c405104132240180b5a02800000301001c02c03084450703945581503130080144540000765554101900506031038036004140d809a5002c1e1010181c05d90301c410191804032204000003511800460455010850b54030020 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 971900089 1250 971898839 971898841
    0x1b0525020f0904150e10110f07081c050703020301090b3f01090804080d08131e05010e1c0c0308060409060603080a0801030605061503040308042906031014 68
    0x1a081090701160030622901901003103030001c0c41d01004803608140b046040c0d401c00c0200380f4240c00d240c01f0b16180b070709010a4151038100c0070000110b10780304d640300007032000c0c0740880c16149440f0384903c0c031690040c0d992414021443c0a070001002540240039002c100ca142c5080c0c0d03120703410301c01d80328411800001c2072445514800300c2840d9130581c040c000c0710380071f0442d03400211481c1020700520410910507030089442c0c60a041d500e60619100d448151f00704504101000f025907542401e881d0216044012a412000b103d2403800c0410020302c0e001d8415030800b20120701c0c244000800c81e00c039041c18a03d20140b021001d00031242803890384405000129841e01042e11442c055200d83c00c2a4480c1c0c1e400502d5507525a00c0c81134075004114071001180100c0010005d10110f801000e90103c400c4981090418045c403d15045010142005c2d003040540e0001604200c80c19141d154030f04121b228001c52076540b0b020340104000d08442d140d009004510041040c3c04041c040c8440f0f072110b0141ea1011 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 971901339 1250 971900089 971900119
    0xa0515010c23150103120c0f030c08120f06040c030b0f0915120619021918080613022b02011202072f150414041b052502 53
    0x124024501d01081001d418450150300c01d04000f840c2100d040c1d5040b000041d03266051030440c10b0007100390101800000c4203803a0008907560850128143d01d404d102c0305907621030600304601e00556958103495100042407103aa101c1d0301e052079229000803141031000d001c2c2c0d95012425a08001c9801350095101c1c40d0180151900c0a040d0760b1001c0800f160601070922140010003104e0465259111508281d00348124000312050b00d00d40303c0341c190b41c107600d000b03001401141c004000c54400c00410104200010903038410402c0036008014920485a00f800d0082200040006112080f4403a14601c2c0c01280189450325610b07401c0c0103005100c131103850707050300199140e5054864034042c1d030342e00b003192400003024501e44a8007413500c0d45451031002c2681542e0401c402810b54100d204070307078108002504001480444c1c00703455200701c1002a44000700c004c140a00400000800c524103c203030b00c240d5655116001d0700c5d07030201021207254408640380080b00f41c4450000060341044d1403036200b020f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 971902589 1250 971901339 971901353
    0xf23060414010507151409060f04080327010b01231b03132402060f01051201020c060103062a0e0d0c0509040f0203010e0f060a0c1106010e0a0515010c 66
    0x880c03001d040c14603d140452542d034090b280780941c4030304c140441e0380308a09000606030410141e8403c21010007030035a403c0c0303500c1e981000540140001d00500d4000002549101c240305800c01c2e00c44612411040070003801c549501038000c140100e40010100d04a241090301e140c42c0258030041801e42d02c5151002100ca1029840c1e0075100c010001c0c4000c000c0c004442c0304030b46182c40100313142402c811042500809031500c840c084140b1504642c444010b200c0300e41591609076045071001c0b1803038146a8904140c560180c003440403000c605024100000003031040540014041c40703400d5084000808501c00b21045508880244100049480b1400a00b5041040d8900709980c0288410b05025542e0f01c0002c021000440b4211200c0030380700d81240460809010700c0d840b25002201a0254646c039045440d5200b40040c0004c84194844000c41105070084505a00114000d000d45805607183c2d101024001803d44403001c45602d81000600808064800e94400804c142c0d280401c000d8075845200c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 971903839 1250 971902589 971902619
    0x8060c030c2812110a0e09040519050f0d11150601090f08030912071a1303080417010f02030921040306140712090f11030f24010510050702060a0203130f230604 70
    0x440910ae0072000c040d5550300101822a103621900c0103088541046441c4d50514002070301e0401400f50a08150380541c0340400c00800c0040c6a9480c5c2c0100c0d0780341c600413100f81445900c0043c501d42c41d0040400c14010100080c071109905a91690410402d0504030b6501c695030300c2484828003060b03020341704010700d21000744100b5082c419079805031501ca840d04602d80d8000c1d40451000144e0030300164451200f8003500d0400c10070000d045042d45803811400342c46040c5100d0030400e60124803520b504600214007580d002c0c541042c82005448010401281040401e890b00000710740a51300e0052a814103000e80701c3d5890f4402015103c0088640d00c074002a40442103195041c09450025404464100f101c043c001001d41010242c00c0840c03504201c1c100810781005014003a401c000c15012a002400c480c24140d0580340b035507964414040032821802074521103084200c90007000110701d2480241441980d800d00005000c80010901c104d00030861401510b411135030900040205440a440300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 971905089 1250 971903839 971903843
    0x60a0f03080d0902030d050408010b040b212805060a0603030e010e031f022a07030b0613090c1a0a021c0212040f080708060c030c2812110a0e0904 64
    0x46000443e980c0001e0400303403c0110003000810129040000034000d004011022006031070800c83c0c00c54a1021a4000b10358a0140888aa6001c1140544c180401024810304219070784403c40d01c0c0c070a841400402c8080b20142d603240305e0080407a03541c007428400e4004490f8140c5494502c402c102006580e980b8410484640c14021118403c82c03880c1d00140702c0381a11140e030740c0165102043d0f020b101c0c003003e00022008000350030303c1c102900e0000000e080001d6030742142c441c0f4065600d01c8002000b0016030341c1c403440128244841f4a00b04000e03000850141e900820040303034917644070307003d5030904d00a07480c01500603409020448610703039034140c60a441e5111403040c5c89200800301d101c440141e01030b42c480d030540449480100007801062100c0d60207085184054921800d144c40ea0003450301000d0220f10071804d0009130280c0403401501003400b044000c0c00c52000b05041e807580504480c0718008820700c682e0825801e0103511812404803007100384075494000c1d9001c050780911281800003001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 971906339 1250 971905089 971905091
    0x90304091a030102120f0703060605031f1d04121d0111030d0204080a0c0602030307020307030513051e0f0f010507150e0102030c1e04030807060207051c020102070b060a0f03080d 78
    0x1d141441e841c03e0004040180042d6411412810144000d07203a00000a02c050101841d03d0b106001256020040b02e80200c0d0074403840d11010448403000316100981d9100b075a15210383c0008424848081e82c680707104074020910034280c910700800541c1c2d092110440c80b00003855000116245600404099010071800400c503410183c040d803030344040340d2080d080542d09500520380d41c4104070750318646001510b1b1600c069419030074407000181d030303c0c028403900038148440451403078000d1500d0840d00000308001080004440003040f5003595010002203924060900c0c0c0610140500b000305c050b6070700903010f0307492a181101035140c80c02c80c3d040030322150089039110040d5108000090000d180903840080f140c641d00d0803c03070101200b607002c1c6c03107901103000402c3c84200089007500341070b01c012a40101000d66955403900d80703507051401c8442e0001041c0d50080e4240d1405a0540c05422114170a03801140240c40e02000c001e4040d2081c8900c4404401680060001802800103800541c00780c0030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 971907589 1250 971906339 971906381
    0x81b0109060c18150e15210708090a021f0306050a06050a091e030f0305070c0b03010f080f03030c0a090e13110103180b06061e0d0c020609030409 64
    0xa01c14080d41c2e0344500900000320070420340d83d600040c510b41040140240c8490040a494007407018145080701c04d8000d10500c8280e0310145251040421203000707132604107140a100d03009048071400240141c1d00c080c006481d080016108032000224800340e281c0042041170554896080381d08120004180c21042603110900015140c4070400204c004c3c00784c1d030700c4850705d6100c4403100900d001400d07403100c2e951102c000c504403000c4403403a0f188410350340c115640c3d032042c6c8a5400c081c0e606100d0b8400060030b00d00030603000507a03041c400018506882521b030a0f6070001c1da40d81d800a03902c50381000c1030210b6400401c0480d00b080d940000074400002d803800d100780e20715a02c0b480002c4d1303114116610315407550540540c1c020000100103090f020042400e08000d0a034403401c0071801c8820303005004240e40c8100300452074a035240810b4401062994035106100c4000740c0c04030520b904806d0f0204442c5041901c0c2c480740c2c60011a24604c2054201300840c03c041c54801c50310041d1010960071120006070720 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 971908839 1250 971907589 971907593
    0xa0c030c021b100e061303051501030f0209131203050604152304060503030a08090c0d0f1407170a1b12061505100c02010905191e0b0705150105010c081b0109 69
    0x241c09003468003c0e10b02106d11051440c00c00c2c504144080808041d0907851100600014848407814508207406541e00d0340c0c203a880f05480e00803119651030141000e100710401c0a080d41e81508450700c51981990180420280b00c24800e415041c140079810020b0141100028810780324070080006140040003c680c42c4d644801090465000740b00c2140000c2003001000403015023040395141090060b50086003450040e21441400c06c0104402020540e600b040b001e803600382000f8010203044141b12144840d114020056079408800c030041301c0c42c07441503140d800c8209500c41c0c0201280c00d09120b020200740307240e035808000c05400c088883c40b00e0031800041003684848005e20400301032516100007210681c000035082c00055400513110720031100c28180394089540c0e0748012989005802c0320f0b50440d103400070132029038680014280d0340c808030b484405d002c1c00290320024550b03002c00c911210703600d94004441d00402d161001d059001c04000008000d024505110200c4034103100006043d0380e25 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 971910089 1250 971908839 971908849
    0x20d081012050307110a0506070807020f030f0a031206060c02131b12050a09151a030a0f14070501050a050a02160e090708010b030a020904031202030a0c030c021b100e 73
    0x2000381611030ba0701c04901d4104101950345113000e0407034200c40d00e40300b00341f0704000103800b4801d441004280481c00300c0c40c80c045454140318030800c0c007801000d640c25040300b15040f541c1e07034030b0941e400da000800300d1007205071608092181c8000d46005032369015413101180c0900c0380b640c0705e13401e40c90704055917100300d5040e0310b06c1c0b00c0f03502044041d195560004500c1c1c4030654410303540701030511001186094800702c002200d220401c00c080e0300c0594003044000444403000c440c09415a000c9816000f00b200a800300001140071080c101d219048052880d24070700c400c00e42d207411501800d80403400802c541603060380214003800345000300b48102c582d5940c0041070034420328103a620480c0b58003440001d10140510600c6050b02416002c2c00820540b8110030010b80d580c40c502101900403542d10010900f070600c517100f24060460900829035980c10701281d12030007400c2020a04000a06d40040d40381961310104224120704406114032091803c030b4010000b00c110710080182c1404809640400240c1f22 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 971911339 1250 971910089 971910119
    0xa0918230111090306061c05010e0c0a061b03080c1c02030915040b01270207050705040629070203010b120607090506070515070e030d020106081002030c120a1404110a08030a020d0810 80
    0x40c820107409a0bc82d1502403100204241d00315109004c1010201e03030342d0587c3d5194003020290180340140064a07203608101062180c3c80c004d002583c4020441c1541250741d80055000c1c9482000721946185001880d81c0428819600105140020001044044000341c00503501602c502120b003d200c1c014007010f002c99125403422100e81e0080e802c01c00c01c40c5400e20660000b011700c000e90301c001c3d092000c2e1290392104848a10540c41c58041000c000795203095110341015100034060488207400d0941250b40e80e041150507100055403600302058905010f015a490990722038010400d00d203a0040300e0408801c018441020084190b24089169038100f000c100940241d030000145a4101428541405000d00e00404d0391401042403100c074800740011540641d180b09030744256a1030b81210b00d00903000c41d0940925141c441070603c014002d07070103000320f40c04504a5205110b0740d5a40c4040d600d90090024860140c0c122a62007001d00e4021100b441c2e100380380406481203951a200ba82c1404c2007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 971912589 1250 971911339 971911361
    0x3070f0f091d090d020c0609040f0b030316051204060f0c02010c05060a0207060510150c05121801031b050415020a1704060f0306050a0918230111090306061c0501 71
    0x100e8418003c05840900a550320002ca501c05400d00078054070100e030962003984c49960041e550782c243c004511007568804100408014266541e4001e412510240e000d820704050307425026120306c0210b00142c14048404998a41d2110b080d00000554144d9201c0c41042c001e9042c080c0a003068030010b40280442440b0b8500c15000584810740c1c0d003031000c100c1e000181000c141d410982c806201866148640104014140c03600911000706840d0044c201440d06400014203600030440c807504544000340c81c0001e15007a0303420412003140002100c00000420044400f00780100400d0000c441c981e0b140032041c0c40310340120b0b4140d42283da510b9921140b9040180301c0544003040602a1503070005884640c0324591a0a012582c1408005032050403070780f08010445a990080b0300d00c19000b04580f10f00c6a410140c20480980c15030140308880f000d2030650040c40d407900c03000042c041208002d07212044c2c40a0001d203150365403142409500902003445642005d01c1c1c118000014500740100e2020320 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 971913839 1250 971912589 971912639
    0x2310905040b0c0711102703020312030907080601090b0f030c0f1201090b161b05061911070b090601050a0e01090b030c03030a020114010603050c0a0311040b070516090203070f0f09 79
    0xc01d104800c0101d0036919221003000c100048010009640d00158400c540f218090307506330359440354041503141c014907a200e00c989004100002504084960180441e99010f032212100c48038407800b016150841d0100301c6500c514031400e000b21a04020241600d8000c50340000100070025407542c4100030000c4810040302407410b5001c19005034401d42402004416900c2003040100f0b43d500c05464000007003003103404200c445c080d262001c42c01d402a003141001c0855440d0b1f10405420314010040049038640614441d000c00003641d801c0c509190000c0750180302d074051032079081040700406001003e8045a0500c5040c59103803140d0f17001e000401241510b6000002c003000c40a00f076440c0c2650580c8040d040c545407000304525400a4821a1240401450005164603186200490600850b00049001900495032008000300000e03210b400c000d8082002c02200d0351842220103030f100c100c5004002428503241c003003580b401041580da0705035581c2009640b00d900c1348003107003419107200c6010141d5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 971915089 1250 971913839 971913857
    0x100213050415030305030f13230601170a0204111209030d0b1906081f0612050c0a0c0305031905150913051f02310905040b0c071110 58
    0xc0e18151203140844000c2c1540b030414545981c4024240f070000800f0007070301056501c0064000182c1c0c031300d840403d0f40d124140f030180159100c0b804c507084043e000c8412052141c080003241e0181e01c010810f400b10348040040c040708109600b800058000582e2060700e05074188003580414401884640c031601c5004000e40c0c81c1c615040240d42138a500c030a45500501000e80c20241d11000a05180142e0b91141131540040e128140c0c072440ca00da440b103100583c00c04ca07060124070329034000320881c2c00c0c80c2c07500014403071a11140c0100c00d00307104018035000442d50400c41c030000a40143c1c050340d032003100101c594400707107210110700080d01c50484040403802840c2d040014140340182d500c0b90403008604500b01c034100b147e0349060b039840c000b000c0181080e010318107078001c1005540450b895142c60709040707119a08083c0d080704410300303a00c03a0203034900181e407000b01d803660382403042a10940c0c200c0c40340070030f40c0c9031040b4012041d44040d0007070340d4640c0e068984180c2c503202d03402e8032146211103641e40000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 971916339 1250 971915089 971915099
    0x403030e090c03060a0e071e110f06090a0320010f090303270206031504020705060103170f04120305040305190309050409050c0f0d050d020c031b0918100213 69
    0x220754030090200c10303805824401c2c061039458601c107035420380744582d41c1c3c540c050b1101c41040d00c4500c88501c5413960403140316200008958032000314140d14056908503400e0140c90a00d07261108d03030480b51440170b41e0160880b100030a10609005641d62070b2007032500079821100c61414295003400da801381c401d0b80c80c9c1000408143d0f0522980e0902c400e401c5001403414041c5011402610400d1406031203004d0100108040c18039284041410034402001150b8910140c40c0c05611804240310554040040c0114100d81403115022681d076800421100b80c9001d00340100c036072402a5440301a420070400388008400036100700422840e40d0301403040c59080b403225150080052a80780c00c2980114100301c071a0300001c0f000a06103118070303422034642540510400210b40c505080550140c4a88508841050031a4000c1201040c6c900c00380c0a070b459101e00740e41000d1070200d41945258000700070500181d501414400718004d4030605105844c020000c0e4205c420aa13008100c402001221506d02000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 971917589 1250 971916339 971916349
    0x604270311070b0f0d0509010b0402040f090f05090d0c0807080c0c0a1406071e080406050703020c010c0f030e310b180f0414060a0b0f0306090d1808030403030e 70
    0x2c01089580f04080c50800200c00c01c504602400081c40c1e190b58885020401c806400e40144e00b4201014004548540d81c8110494040d003541c46649449458010008200200381c02a1403044568400410890003800c0040301d100714030100540c1e07010024401000000c041a00034444c83c4a8072000303003540301c2d002c1300704083d02002d5404400d07072500f200f00301101a01c504099660f00d5410040a000109200c3d0042440b0742424500070200c0000140114003641c004029000c0c20303000c0d41c22944000c00f00b50054507205a02c0074003508000d00b001c0041700007440381d9502031203900040c250240610003200034400c003500e00c0ba03000307880c81c03400e001ca811024034500c1441001d80c8221000c814800348208414034005c0302902c03070b10480204000080511102c0ca0703559028254850403214a4038101000310010701100d6852441100003214415180c80e00140301c90241000314090402400d10034030580f14003192096400f07d20103803440c001451710007480a0f000450280d15840d081d03402c001d007005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 971918839 1250 971917589 971917603
    0x4030801140904030225120804030c0902132c0708011d0f0703020705070b0c010b09160e060d0b0315070306150e060904060305012d0c02060604270311 66
    0x30b0142c540c0c01c2c20080440d5000606410240c1070a42164500d10195158460003020b5080b0804036900a016101004030308030003001104c1c02122040310842c1c440079520140c0c45032034000c0000c00ea072039501f0300448030303640110044508401c25010702c03c03182302441c0662030360407200d06000c600308500420110014000e004d1043e86090450300c0d661406c0713210a00414005410130041640c0803131b210042000c00c00c00300000c0c089500c2c6580d01c41069070441400b0f803003015100c9001b550808045020703000c0c2e60752100a141010b849001d28071144005004054000c502c0002c04180c0320621301d1929202440611034034043d0484019031490308074001b80507100e0951018154560b20b178200340d032040c1d100300c0324200c204c3d046503001c0c1e03114160b90018014101d5600080c2080d407804251141a944020400160050705003481e41d442402c42a40030884500d064000003503000f031400900d107490950710040e0030b003c003507060b1240507211940e00c2d04800000f030302c101c01040344501548600e20b030400c940d13 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 971920089 1250 971918839 971918879
    0x810030209130b150a0905061c050f01060911090f130f0e0606010804050d0c0c0f14030d020610181506080708012903250504030317040b041403070b04030801 69
    0x4e42c1102c00100124080c40e80c54407034148000d5449000c180c407641c0744010f104048500250700704149d651401d003d07866030048a24110607602c1e2038000258480103005045090507550011428240c0800c24465812194580c40754007850483d00100c840c8032905c604207480c101c100000a2205811081d030303180c11000740c1f0150600940e0020000010000101c0d285401e210b441d20140c841590f21700700103041c130302e900085840d5040c1d94001c00d08806683c46040d1006003201203610031400ba80080c1c1e26000c040d101e140d071642a40a003400400c1c40f65846100081070594002100054911b036520310440326003007800080c1049081c0417400e9880036a03d405481c036011071101491034152517521841210704002031250000c00002c41c180048901500c900084100d1140300030000d40005003242c0c0240411408100390000704a1303010044207581d8442c0e58004c3c6181125191a141d9140300e0880d18248034a51004101d2100001e0403d00c0403409a0322035110881c4c0355050106580b41551102d01c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 971921339 1250 971920089 971920111
    0xc020310140a020c07231c12230a05040308030c03010512010b010c0605040501230106030c02011103070507020a1d04060e06071e02010b0d0b04031b120810030209130b 73
    0x1130070841440104020b400c9513516802404512100c101070b0500b07401800301c0a070b02c0444c100d9412031850740d08035070b100c1407441150000521451407000352441d03004110103150003401c03000034004000c140e80040400a009041c040d08050352681c449805901c120381c58107401c04d001c1300401039405e00068403401542d20b20300a11481c540b10300028038030880e580000d0016902e503008241031110a600560000d802044000009618180340e010400000c0c49101d001078503014800b10b1840c810f00c0b468085070184030000345941c50f038508c1103c40360031205090b43d005100b1300c40042ca00090840b03803010300c0ca0858001c1c034280340070b08103002211440c550040640d00010104405198441c4007070703031182d43c103000720710f44e060b44044102c1c010411201c80c1a04411044505010f1284102010344550702c00da8590b003403945003d0100081c2d821600d002030101840820018000c1d00401c8603961004030311007a40d0b50a9503a80028040041c15a2010b034600ca003510290140000c458102d03500ca404180c07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 971922589 1250 971921339 971921347
    0x30c0501020c06270f030d110f0703030e0f06120f010302030d0309080912390f06040b0d0b06360f040906020904090c06021b0604150c020310140a02 65
    0xa690b071310945040c0c0c5034081c1110082540c1916075625000c03030071040000e0100c0d04058000c15020b0144003003450180c08030f00c01d20f80000203000c00010038005895240d640c0024001058090111004000e241140c2c0310600303006661840c001c000440d17100341e4800e44081c00f07a5140d40103050034004e1400e4142c0c100b6040810503000b10380c00c581161070003c0160350000310036401010b0b01303092603c404214042c044084148690030f8a007140700c5025040810070440c1d0301a011820800e11098100c101030300450306100402101c0c455001401000071002000f00d000d10a0f03200042c00c5a1081c29410038090410381d83c000400c0807200200421803101082c1001ca40000700029101441c1081040c407441e00e0340b0b07001d41000000e4041e0746083c80064000d1012070f0961800d181c40e5041401076000520034000203403d4810b54001c03c0e180c00070041d004501d0541411700c80000e0301000700426042c482030821450050320704002c80524a200900000361030b05800d02d840d6600e1002234904204140144 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 971923839 1250 971922589 971922607
    0xe0a0b100f0f140103110f0706110a210204080706090e07140d0f20090907051e0a030e0d03020d060602030705151e090304030b06060313020f010513030c0501020c06 72
    0x5881000b9501401a443c1803c0044401200581608861588050740204418480d1a2410f000c4d140003881f0742400d2002140d00c0325604850701074126400001408400b000c14040300c1481031410703040300303200c01500d01a201c44403186016183c0d48980d00003400300408000c0da00412800307079008513903480c10b25016922000700c600c26010365200356140d81c1d61102c040c00c00300010b0b44515031080342446c03c6c041c0658040c13580c60954106507829409a8100c0001480040c0310380201c0d4003000c0340c256440d040d03039000e03800e880690b00001000342c240b541e20409290300a00800940400b0314042c2d0b0b0150790b41c44080c0100d81078030126401031096500030721580d0009034001c07540c07802c4006416030190056a0343e00c01036500e40480d00c0c80c038156101c00424011486404030080c420f0306c1c000c0034414071a86038041401540d100440707841e8414012485440010300e010107140c0b00d180340500d0850704000c1000880015003449602c21142c40d0a10b41c42002035503018860304c005200c080710762a041c100300c6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 971925089 1250 971923839 971923859
    0x3090a0b0a020109060e0a02010314040308041104091e02010e0a06020c1e060703020a050c060304021f120f05061f050409111b0303090601050a18050a0e0a0b100f 71
    0x50103001009031000c07440152440c403d42c0a9468107800c00c000380011051042159280c0c110322500b640083d0070f280003c1c811900d0b0709050340c000c6a00d565000080c0d511525500346802840c44880e5005d9264900100401d61002010343e6001a00c42840011f02c1c1501c009010205000c1d01da41c01507004c5502000b030103802049144403a80c01b5541424981ca040c00750002400c442e04007542e001c0b50104481c000c1c0740c1d00050514950b0710503000c03101c040511a003080000d01049600030341c01b400050303115800d032b0041c1001c4101062241884505401c0c0c940b81a41501c00400c0d182000c1942c51081120310f203446c0600b10002110700c0749003207130100074150041042c03095016111526440f11180001f0040d108110b8a80e00c90b88041784042d18110b10f00702e80c50fa841612803600c64400c020010a0714036241710103404950303001084441c2e442d1000050301c040e000007000c0c11340c240d5441d881200c0a0a0500516005074400d41811400d4501003903111301d0340486412a40c492082050184040e80103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 971926339 1250 971925089 971925109
    0x1e070c0201030209121c03061d070c0507082a041b0804050a0b0c0714011a010e03030f0301090b0907030b030c01080606091e150c210708030103030f030e0309 69
    0x20b00e00580d48064003000f1510740c00820b60049818400d40c4602c603106103a51800d8440e0010a9506119044d40c0d60001c01002ca01d40e400c850100e800e10020030041d5000390340e5070305424410019107100070750301c4448038105911860400307114140c4040074000114107052458039007408440400010481c154008100c004040c0f80384140103401010405200041011002166000041405500d0202807003440c0c1d8000c00400c03180c1c600554503503400414103000711545583c00880080801030840b0044414a0000e9506a058001004010302a8039480c0040d0b018101d001070206580c1112700510140c020001c1030f02c01098078011840d003041d60003080b50421074009203400f09081d2100c0000030943c0c4661011154002d60b40400d00321003034500c668240c4941d004880e500f050303520385140c2020911410304101080e030000fa201403004094060030f6918508214085820010a5036910820340d00c2030304158003103000d00343e8114842d03034140540545294400095410030b02e841c0003090300213503 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 971927589 1250 971926339 971926343
    0x30507061107230108090c03150c04180605010801051012051b03041a01050f18130c09020c0601050a050f0f011202040f0503060f09100203040204021309051e070c 71
    0xa14000c06004a40400805019120703281c000207059203846580458041d0340e0f601d140c0450017440028000080c04518107101c0000540507001c06008010420070702c0354010112160300006100120340b0150074010f030790ba01c40b110f4000245031403d01002600c0f0040c16032002e071003000e1504082e148640c0c8032a004501d002c646a000c1916180c0101c0139542403041c0041e1a0030b52008400c0005001c14a054400780191013090b02800da62940140450f001c04201e5094200c50f4011000340d094091400c00d40e40030700c101c030490b00e0a6180d03607661903900813954402c1d0103682c0c0120700b003c84007101f4400135006200407600700a8103498100404c0e8001030b5140c1c01c03407141000041d1264280d0007030303413000c1e82803054800465272551141d483c48030304036441c010079002c2d12841c400145080320f10040c60f4001c80003540100a509041c04082000c2d5000910032a0000e400b07022010b030030b4505403002c2000d45003210020440d403034411101d020040280c1010141002d8010030310640c150010800150b0355 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 971928839 1250 971927589 971927597
    0x50f07050f0f0409050403030f050c040815040204090503040e1005060a1409010c0b090a03020f010506030c190b0a11011b0509100c0f0803070f02062203020f12041e03050706 76
    0xc2c55503810b6921402542d200c0c0541d103040c0010001019810391000e001860071080c02c1202d5241e040b000c0113030340224021845590300c2a2621480d10300141074850740148000d101103800007150751501d0858009502c1242c15407150801c3c0a2203440d40341d200000b030041030711503a0508102c0740004042c424031508811401c000080d8030090b42e407141e4520804140c214441008608251242640e12214003900750010b00903031500c10380c4084103001d20f50140d840100200701150700141040240c008203058000d0000500000194080c994030181c24070000300e403130b40d007401d40710284418251a4448041d40d01800200254100e4541000589640300300035541122003004c0c11405a4900c0385400020b4164403072a1155020000d01c8002580f044015940f0503034014080e0900380d0b5074480598000903040315030790086020701d12039110a285540a84101d44a40d4010940d45041c00301c035400c1e5a90b10440003c050140708040d4a504e100811048651b40d041c5195803036084c0c49003c2030080400b00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 971930089 1250 971928839 971928847
    0x20c010207230c0d323306010c0501180201090b1603050903030c0106181d030405010c06020919050f06040f090f1d03040f0f12150e070803090301050f07050f 69
    0x80200c000c0601303d030a40205d48a001c07452441c0c0d04034a03200f65040b0fa41701c68440d04045484245d0003c4407032910340315020414a4801c030301041d078003103081c00134a403504100d05003140e10080341d000d0162001000600d0b024000203501e03400014a06410b41d00f02c20102d1808128080302068030a00006101d03270140780698a072103420000a0943c86118416140e40d800d207480414018602500c03c060216154401c211000001c10401500e94400b952540a41c00520003088554000c04050010034462072005103000911800101c2c04520510460002d60058405210a081100641c0c3e0416801c554541c203007494841c010b032003821280101d000550300c1c0e9101c5c04801c1200d42002d4204104c8924040c040b0862403043c5580350418412082c0c01c0041c00000038a106050011006507415101d0001c100c45280d00e0300d10312002c42c154420390180d80c0d8000071f080003906000f035802801c0030801a5655200c8601054203480d00034000d00741c0c2142004c1030081040c0c001c422906001c001c0740c6050f8503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 971931339 1250 971930089 971930093
    0x509060102250510090e07081006032f030402010f1407110a05040509150c0906071209080d03090506091501060c08040f270c0207050607020303040504020c010207230c0d 74
    0x34640710b580140e80104c03041080108054101d51220700381c40f4229149039480e580c81d2802c8a40c0e11042c0c0b071090038014004c0d4240a81d504c00c2c2c110095039660313011070254200144504146c4481010707400d14031524040148821580d00040c2d04503601790600c1d1510301302060b108512510f201e942d01c0201881e20a040c050020b4907180c0645d030003490f004104101c945040b5003401d441c5e0300b11840382d402c640d80200004090200d04000c0e540c40380310103000b4901f000c4881d519aa0071403420000711003440758010000801e09810449034014400360303600403c41204078030340f451034240050846145500401107a254040c0d0002e11503045407803a25040310075140500340b03500c080c03107190000b5180ca1024840482d00b62030004003032540b01881c280110b6052101c20802046486616503840181c00c40b4004200620300f401c00390a85030300042c2503d2400b039503078000500b06c1e0700030201c0884694000c1221014800d001524440c20046a0001e02c850340c1c80c000c025450300f05002e0344503c991011061002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 971932589 1250 971931339 971931403
    0x60a14100c0204020d0204030b0106090308071e0212010b150301052b0f060504120807140318060a0501331808010e0c150414040c14040e010f0509060102 67
    0x10740d40e0058001c42d5070f030f006211104065030040c0020307035200c0c400d900002450303481505c00c44222a0404246404c14a65aa0b69490301103044e003238609100b4031440301d10260355621940400200240000200040400107120704504501d02031565200c00b4401045103480340f83c00c0c41203451901e01000010b11124a918503180c2803280007609004505038a40300300030940e03100d5406903016000c02200054065404c070780c481c17403c85084000408000c4940d0003179031503070301031600140c01011b504c000000b60031580e841e1403400c4510400013501c96004200c8004001d810904940f024a050780600103400341418000714520004020801d25054600213040f41100300c00161040130004e0050b0784100c0c1c0455a101164410540310740c00b5080501181c0c0610004c03101110016220000d0105601c002c21005181c0b50700000248000414504540000c01000301301800c51414101070340c0d41407101c9003c0c640c210307800c4030340160768000610045a03000075071141500300403403110a800d103034922846 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 971933839 1250 971932589 971932607
    0x106022b050f1323300d031e02040501050a2109050303070f031b0c050a0c181103060f040207150c0c0203160b0703050f12010902090108060a1410 64
    0x200c0340407004600c11468140310083e050480e81010a8030f0309038020444441d19206406295030340c8042130083e41034a0008548015500c80c9000b8040c10300604e8180c84103050102c401c4601d000280c2d0f840a003000401d03024803004010250440450510741040b00103000b0f440382280c10341c14016429110488000541011107891107820030500c010760043c6089a9284c0081d110040442d5441070704940840c464451459454403030050701800c10800c2c1c50546108002c194195110301402c00c001d00400ca0815a440041030040800300e14071480c850003204031907440302d1144515404100f44000750340c40320350030050014201c60045ea03403502d03490301528407258010141007041c00c08005040b1250000025001503000b901550540303c01116440c01d001c0080c01a148518014000030b004030340303c2c4001c7c2c00e101000021142c45e1070802c1c04001c045071800d07400300d4002d40d000144580c2c1381d44d110704010b8012005840c0d81c00c1880c1000e40c000c0411552000682c0225045024442203d00c0340d082da0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 971935089 1250 971933839 971933857
    0x90f0907051503061c05030d0b0d0b012c040305031602030c0a060522020a060309030c0b1005100302090901090e0703020604091a240904091203050f0106022b05 70
    0x840c18480d200d0000c1403030741003259854811185c0320000d05802900007102041c640d8483c001d140781007440e210110080101c0c89149803c0b02d4104070480004150665490180c41c84179806c40c0d00448801d84c0d01a0300d00d140e02c070000c0d4018080140000a0f81100035079800507034403c040c44451028040c101c2c518080c001d000503203840703846190b4082c4441c541c49240a20000340450030080700000c1100f58451010714000d41040c0700b00400c0056610a50080c50024400d2415001c000e0b101d44528200030001d2b00c1d4070301003500401007045036107010301c241c0c050f08215040a40c1040d0751840000d44040c0140320381d500c216200c0d020198001010322469000c0d541c01003200e510355807149880740040c001508800b124141c844e1104455252100c460405008a1203c0c41d01ca00b0794180310201300c0d08a1000f09401545502c210b00002e1165100c0040f407171020340e0300051500d03148013042040b9106030300c1001036401c03145808482c40004042c40c5000b0803c0e0410494841402004581d00c0c4641010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 971936339 1250 971935089 971935099
    0x3133006050601121503080306061e0c0607091202130f021c0c0206090303070e0f060307030504050c090c0412080d2d061410021e240105090f090705 65
    0xa40100080c0768420340c0200000c0c1d80b101c4c0c0c075501011241044600112003a944030009420410000e02404c0085030701ca00098030050825541c09600341e15100700c0c01710102441000728078980000010040300b60302508626203545801c2c50b0130306c1d6882d40d09501c034000e4010341c104000b20454a549821691401c04602c0301195280c00e0426074000c08601008210b18090034115070250a900c001603860085110070043c5145844071802074030810051001c0a40140a03240d502060760345170000345102e1400d03500c002c503041c80c051502d60305000d0700d103113160b21a400650620100d1444201074400380c030f46542d000040d900003800c118089000e22001100e0040c2031a5054204000b820718820500717001c0441c1c008102d041d0603080c03068484500454100107040041d04813140741582d0700758408905401625625140070300c01320500051801454800e80c00140b031040900340d40384d004441d11241c2050040e065040c007001403040e00c40a4504c00c0c68140e0440441c5d95054140f203080300a00780148 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 971937589 1250 971936339 971936429
    0xc02180a15060903021504081e19030305011d0907091d070303020d090902030f0c07080915030610030501080c0f011b061406011d0114070b180601080313 67
    0x800107003143c1c0d40b400124001c40c1d98111003121100f2060984040d6070080d80a44a40b00407101c1d46881e0b01011001001c50307101c0c0c0400d100d00602c003010340c040c040307019540100321076040c150418501c20080e504400401182010045558000718110307080d44c0000c9004141c10104003074082201004c409415401d00034100300000b010340004086541c0038154a804010702d0f56060aa8102e0004440a1000020000000780c001070503030020070f2030b0b0b48600f900a0411281310042144a1107994001e03c182e900002407022618020070204440c01c2d85144c10f00080d0b04104506448500c1c0448460003089a005103261580c0200300d0354051451203007021185140b10300f4040041d0400148080c41c0082100c081019944201c00200c6041c190780020600031900303100442d065a450401c2400c1c10905215000020302101ca60f240160301202011b0748540e4120505801c0000627401104558000c001203003564030070582e40b100301c07000c0b0300b0f185000546201110051064039070004054681d615 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 971938839 1250 971937589 971937599
    0x603021b06090a02040b0a120210091701050105120a200402070b090a2010110712080903010f02120a0b04090b0a020d0509060c04031b030c240c02180a15 67
    0x41c024100f80c001c0b81c05000004017a4240010040c05001d104e1058413998103840160520035490b440d4180107103014460340c0d9590361803004c40d10341d80301c510b140b50351184c2c0100f020307107050a00440d10050300f0000e0200d01c0e800d40c1c1c41d10880401110030030070540483d0070144050743c4a0303042d00c1c42586c00ca090741d49185044541d064880030689412204e81c40000c6040380042c45480c0018440c69004e000003010101c040d50666010b8901452906503115070040032480d521b50b9120208102d01c00c000e100d40710400682010300b950000d6404c0aa1980305110024084060340401a008070b5038130380000710702c1e0a02c0d020401611316402d001e0810203021040c00306000b642d50003410200071800c003c01958507001a05601d5444c02c1e610640c014405000a1021500042034000d5401d0b02c140c03c00c000c55569900c21a02080d180c2c4400e041800c0c815140110075000003140e90209841d140814410b201e6600069401600b0481004c900c0107071400501c40e145241d210700201d500f010744130360400c0d81d50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 971940089 1250 971938839 971938843
    0xc0601030314090907051c060b070c0e0c160309030f080309010b0a1a0a021606020f0d08040c150c0218070306060201090b0a090206210105040b060a090603021b0609 72
    0xe22044000842403038459920701d2458050b281c1c0403400920303c641d980c441d072004842076000480345182400000780e219880c070742e6922071400100210fa909a8950b8400d043c18665102a603024060404000007001a407500d107004450b000d0710340755401103840b1614101117880b0301e200e8100809000c0500b01250501081c14050751040807404024048081c071001408844060751060244145c00c12042c00c802400c0c4502070840d90060b44101c41840844040c0081d80d042258002000b5821080b10035408c580c0a02100501100341d0800c0742c0a41865501d0079110002ca00c2107074445443e034581000214861314410214030313001444900b10032070011001d08581001e8500b000820b2810100050490041c001c640c0240d410500d0003095a0301c0000c0040a000740b036000701c2c1d101104000444607107c480403590160109000466501d6040c4020b10049445083d21203101c1c5405011199500ea805903030a001e580341842c016849165080400b681c0306130300840c0503000c0c06101e003048111040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 971941339 1250 971940089 971940091
    0xc02340e0417031003140307030c14010207051b09071e0c060b04050a0e0c180a0f0b0909010609050c1603120612060e010c0824010c0b070e131a010e030a06020c06 71
    0xd40c4991b584032101000d1964a1107100b40040c04128074982e80d0b00814405103030400c00f00400d400241c50840d0542d00c3c01d040c002c41465000700107400c1c5110710082d04101c0a4036601120760b0a196489060807050000c0c08500000b3f58001c01040c0703840c001c108400c0e030f00404042c2001410600890405000358000f50040007102e0030a0b100c1c5150181c101d180036908201300701320328011015561541c003150b502038054410100e084075110014164146c46034680240301d98009400010b03940c2c2030080da80184e4501030310082c101001844140c100031b0070b8440d000400c42e898204421048102c0500801820040d07000007140c4c1c400710510350610a0a801000e85525540006c0105610381c0300b055400349001c1c0c920a00c48000c0c90300000140c9141a0101c0b0001030504210078286920340d50789181c064100c1d400c80024a40012810b160300340a50022002038840f4001e1010018a440e07038a680c4070b05040d103e04018501100d4189624144500560700750400c1082d59542070075242c440e580e040c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 971942446 1107 971941339 971941343
    0x503030a0f1b2d17090d200a02060c03071b1505071b150201051302010e01030b0117071106071103040b070212010c02340e0417031003 59
    0x20305074152001c49040f15502c45007140c0820400754901a000380c18200c250f800342c81c12001c05500405c0b8001c640d4038480146a044101421051806410503400b0390080000141c02c3d02480000c03005000d40c90140a44070000728440d100040004010300c20002007040048020207814070510003440300c2c83c050541180e102a80e09035000c1000e0195114092100c0d11100385180c06170280178250340004040200d2148440c140c0001c0e28541030350002504140c0d841c0d081100b241c2c004d5800d50420010900004024600440c000c0c0014103000000045e501c07035400002d030000d202c1e800c020714420643c800f5500b410300d44003070324905401580c01260300901c01c5140c245140424881c0f007401c4007050713008142602030695454040e85a4400403d26801e0401c0c0000c0c0c002d42d045815000c0b41c00e00640c25950303940d50705202c080301c07020000b40445d1b840004140006081c4d259012826a8 = true := by decide +kernel

theorem cover : BRFrame.Cov 971762589 971942446 := by
  have h0 := BRFrame.cov_init 971762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 971762589 ≤ n) (h2 : n < 971942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
